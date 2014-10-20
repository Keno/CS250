(** Encoding semantics in Coq *)
Require Import Arith.
Require Import String.
Require Import List.
Require Import CpdtTactics.
Set Implicit Arguments.
Unset Automatic Introduction.
Local Open Scope string_scope.

Definition var := string.

(** ** Environments *)
Definition env_t(A:Type) := list (var * A).
Fixpoint lookup {A} (env:env_t A) (x:var) : option A := 
  match env with 
    | nil => None
    | (y,v)::env' => if string_dec x y then Some v else lookup env' x
  end.

Fixpoint lookup_def {A} (env:env_t A) (x:var) (v:A) : A := 
  match env with 
    | nil => v 
    | (y,v')::env' => if string_dec x y then v' else lookup_def env' x v
  end.

Inductive type : Type :=
| Nat_t : type
| Bool_t : type
| Arrow_t : type -> type -> type.

Inductive void : Type := .

Fixpoint tDenote (t:type) : Type := 
  match t with 
    | Nat_t => nat
    | Bool_t => bool
    | Arrow_t t1 t2 => (tDenote t1) -> (tDenote t2)
  end.

Inductive binop : type -> type -> type -> Type := 
  | Plus_op : binop Nat_t Nat_t Nat_t
  | Minus_op : binop Nat_t Nat_t Nat_t
  | Times_op : binop Nat_t Nat_t Nat_t
  | Eq_op : binop Nat_t Nat_t Bool_t
  | Lt_op : binop Nat_t Nat_t Bool_t.

Definition binopDenote {t1 t2 t3} (b:binop t1 t2 t3) : 
  tDenote t1 -> tDenote t2 -> tDenote t3 := 
  match b with 
    | Plus_op => plus
    | Minus_op => minus
    | Times_op => mult
    | Eq_op => beq_nat
    | Lt_op => leb
  end.

Inductive exp : env_t type -> type -> Type := 
| Num : forall G (n:nat), exp G Nat_t
| Bool : forall G (b:bool), exp G Bool_t
| If : forall G t, 
         exp G Bool_t -> exp G t -> exp G t -> exp G t
| Binop : forall G t1 t2 t3,
            exp G t1 -> binop t1 t2 t3 -> exp G t2 -> exp G t3
| Var : forall G x, 
          lookup G x <> None -> exp G (lookup_def G x Nat_t)
| Lam : forall G x t1 t2, 
          exp ((x,t1)::G) t2 -> exp G (Arrow_t t1 t2)
| App : forall G t1 t2, 
          exp G (Arrow_t t1 t2) -> exp G t1 -> exp G t2.

Fixpoint envDenote (G:env_t type) : Type := 
  match G with 
    | nil => unit
    | h::G' => let (x,t) := h in (tDenote t)*(envDenote G')
  end%type.

Fixpoint env_lookup (x:var) (G:env_t type) : 
  (envDenote G) -> tDenote (lookup_def G x Nat_t).
  refine (
      fun x G => 
        match G return (envDenote G) -> tDenote (lookup_def G x Nat_t) with
          | nil => fun _ => 0
          | h::t => 
            match h return (envDenote (h::t)) -> 
                           tDenote (lookup_def (h::t) x Nat_t)
            with 
              | (x',ty) => 
                fun env => 
                  let (v,env') := env in 
                  if string_dec x x' then _ else _
            end
        end
    ) ; simpl in * ; destruct (string_dec x x') ; try congruence.
  apply (env_lookup x t (snd env)).
Defined.

Definition coerce {t1 t2} : t1 = t2 -> (tDenote t1) -> (tDenote t2).
  crush.
Defined.

Fixpoint expDenote {G t} (e:exp G t) : envDenote G -> tDenote t := 
  match e in exp G' t' return envDenote G' -> tDenote t' with 
    | Num G' n => fun env => n
    | Bool G' b => fun env => b
    | If G' t' e1 e2 e3 => 
      fun env => if (expDenote e1 env) then (expDenote e2 env) 
                 else (expDenote e3 env)
    | Binop G t1 t2 t3 e1 b e2 => 
      fun env => (binopDenote b) (expDenote e1 env) (expDenote e2 env)
    | Var G x H => env_lookup x G
    | App G t1 t2 e1 e2 => fun env => (expDenote e1 env) (expDenote e2 env)
    | Lam G x t1 t2 e => fun env => (fun v => expDenote e (v,env))
  end.
      
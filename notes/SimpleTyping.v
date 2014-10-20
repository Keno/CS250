(** This file shows that we can build a recursive evaluator for
    lambda-calculus, as long as we use dependent types to capture
    the fact that the terms are well-formed.      
*)
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

(* Same as [lookup], but returns a default value instead of an option. *)
Fixpoint lookup_def {A} (env:env_t A) (x:var) (v:A) : A := 
  match env with 
    | nil => v 
    | (y,v')::env' => if string_dec x y then v' else lookup_def env' x v
  end.

Inductive type : Type :=
| Nat_t : type
| Bool_t : type
| Arrow_t : type -> type -> type.

(* Translate our object language's [type]s into Coq's [Type]s. *)
Fixpoint tDenote (t:type) : Type := 
  match t with 
    | Nat_t => nat
    | Bool_t => bool
    | Arrow_t t1 t2 => (tDenote t1) -> (tDenote t2)
  end.

(* We are going to index binops with their argument and return [type]s. *)
Inductive binop : type -> type -> type -> Type := 
  | Plus_op : binop Nat_t Nat_t Nat_t
  | Minus_op : binop Nat_t Nat_t Nat_t
  | Times_op : binop Nat_t Nat_t Nat_t
  | Eq_op : binop Nat_t Nat_t Bool_t
  | Lt_op : binop Nat_t Nat_t Bool_t.

(* Translate a [binop t1 t2 t3] into a Coq function -- preserving
   the denotation of the types used to index the [binop]. *)
Definition binopDenote {t1 t2 t3} (b:binop t1 t2 t3) : 
  tDenote t1 -> tDenote t2 -> tDenote t3 := 
  match b with 
    | Plus_op => plus
    | Minus_op => minus
    | Times_op => mult
    | Eq_op => beq_nat
    | Lt_op => leb
  end.

(* Here, we index [exp] by a type environment and a type.  In some
   ways, this is quite similar to our typing rules for the untyped
   calculus.  But here, we're simply preventing you from building
   an [exp] unless it's well-typed. 
*)
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

(* Map an environment [(x1,t1);(x2,t2);...;(xn,tn)] to a tuple-type
   of the form [(tDenote t1)*(tDenote t2)*...*(tDenote tn)*unit].
*)
Fixpoint envDenote (G:env_t type) : Type := 
  match G with 
    | nil => unit
    | h::G' => let (x,t) := h in (tDenote t)*(envDenote G')
  end%type.

(* Given a variable [x] and a type environment [G] and a tuple
   of type [envDenote G], lookup the value associated with [x]
   and return it.  *)
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

(* Finally, given an expression [e] of type [t] under type environment [G],
   return a function which when given a tuple of values of type [envDenote G],
   returns a value of type [tDenote t].
*)
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

Definition eval {t} (e: exp nil t) : tDenote t := expDenote e tt.

Implicit Arguments Num [G].
Implicit Arguments Bool [G].
Implicit Arguments If [G t].
Implicit Arguments Binop [G t1 t2 t3].
Implicit Arguments Var [G].
Implicit Arguments Lam [G t2].
Implicit Arguments App [G t1 t2].

Definition seven : exp nil Nat_t := Binop (Num 3) Plus_op (Num 4).
Eval compute in eval seven.

Definition inc : exp nil (Arrow_t Nat_t Nat_t).
  refine (Lam "x" Nat_t (Binop _ Plus_op (Num 1))).
  refine (Var "x" _).
  simpl ; discriminate.
Defined.
Eval compute in eval inc.

Definition inc_seven : exp nil Nat_t := App inc seven.


(* The remarkable thing is that Coq can verify that this function
   terminates, and that we are preserving types as we go.  So this
   definition captures preservation (and progress) as well as
   evaluation in one fell swoop.  

   Of course, if we tried to add "fix" to the language, this
   would fail. 

   On the other hand, you can add a *lot* to this langauge without
   it failing.  For instance, you can add lists and a fold operator
   for lists, or generally speaking, any inductive definition and
   the corresponding "fold".  You can also add (predicative) 
   polymorphism to the language with no major difficulties.  

   You can also add a simple form of state to the language, as
   long as you don't allow closures or refs (basically, anything
   that can cause a cycle).  

*)
   
      
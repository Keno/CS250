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

   Another key distinction -- notice that [exp] lives in [Type],
   whereas the [hasType] lived in [Prop].  
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

   For instance, if our environment is [("x",Nat_t); ("y",Bool_t)] then
   [envDenote] will produce [nat * (bool * unit)].
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
  simpl. discriminate.
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
  

(* It's not very convenient to write the explicitly typed terms.
   So let's write down a surface-level language which doesn't
   require the context and type every where, and then build an
   elaborator (type-checker) which type-checks the code and
   tries to build the explicitly-typed term for us.  *)

(* Syntax for our surface language. *)
Inductive ubinop : Type := 
  | UPlus | UMinus | UTimes | UEq | ULt.

Inductive uexp : Type := 
| UNum : nat -> uexp
| UBool : bool -> uexp
| UIf : uexp -> uexp -> uexp -> uexp
| UBinop : uexp -> ubinop -> uexp -> uexp
| UVar : var -> uexp
| ULam : var -> type -> uexp -> uexp
| UApp : uexp -> uexp -> uexp.


(* Our elaborator might fail because the code might not type-check.
   So we'll use an option monad everywhere.  

   In addition, we need to return a dependent pair of a [type] t and
   an expression of that given type.  The notation:

     { x : A & T[x] }

   is the type of such a dependent pair.  For example, we could have:

     Definition pair_t := { x : bool & if x then nat else string }.

   which would conceptually be pairs of either true and a nat, or
   false and a string.

   These are usually called "sigma" types and notated \sigma x:A.T[x].  

   In Coq, the way you build such a pair is by using the [existT]
   constructor.  For example, to build something of type [pair_t] we
   would write:

     Definition foo : pair_t := 
        existT (fun (b:bool) => if b then nat else string) true 42.

   Notice that the [existT] takes a function that describes the type
   of the second component in terms of the value of the first.  Often,
   Coq can figure out that function from context and we can simply 
   omit it in favor of an underscore:

     Definition foo : pair_t := existT _ true 42.
*)

(* This definition takes care of packaging up [G], [t], and [e] for us. *)
Definition Return {G} {t:type} (e:exp G t) : option { t : type & exp G t} := 
  Some (existT _ t e).

Definition Bind {A B} (c:option A) (f:A -> option B) : option B := 
  match c with 
    | None => None
    | Some v => f v
  end.

Notation "'ret' e" := (Return e) (at level 75).
Notation "x <- c ; f" := (Bind c (fun x => f))
  (right associativity, at level 84, c1 at next level).

(* This notation is much simpler than writing:

       p <- c ; 
       match x with 
       | existT t e => f t e
       end

    which is what we need when we want to work with one of the
    dependent pairs { t : type & exp G t }.
*)
Notation "[ x , y ] <-- c ; f" := 
  (Bind c (fun x => let (x,y) := x in f))
  (right associativity, at level 84, c1 at next level).

Definition error {A} : option A := None.

Definition type_eq_dec : forall (t1 t2:type), {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

Definition coerce_exp {G t1 t2} (H: t1 = t2) (e: exp G t1) : exp G t2.
  intros. subst. apply e.
Defined.

Definition try_coerce {G t1} t2 (e:exp G t1) : option (exp G t2) := 
  match type_eq_dec t1 t2 with 
    | left H => Some (coerce_exp H e)
    | _ => None
  end.

Lemma some_not_none {A} {G : env_t A} {v:A} {x:var} : 
  Some v = lookup G x -> lookup G x <> None.
Proof. 
  intros. rewrite <- H. discriminate.
Defined.

Fixpoint elaborate (G:env_t type) (u:uexp) : option { t : type & exp G t } :=
  match u with 
    | UNum n => ret Num n
    | UBool b => ret Bool b
    | UIf u1 u2 u3 => 
      [t1,e1] <-- elaborate G u1 ;
      [t2,e2] <-- elaborate G u2 ; 
      [t3,e3] <-- elaborate G u3 ; 
      e1' <- try_coerce Bool_t e1 ; 
      e2' <- try_coerce t3 e2 ; 
      ret If e1' e2' e3
    | UBinop u1 b u2 => 
      [t1,e1] <-- elaborate G u1 ; 
      [t2,e2] <-- elaborate G u2 ; 
      e1' <- try_coerce Nat_t e1 ; 
      e2' <- try_coerce Nat_t e2 ; 
      match b with 
        | UPlus => ret Binop e1' Plus_op e2'
        | UMinus => ret Binop e1' Minus_op e2'
        | UTimes => ret Binop e1' Times_op e2'
        | UEq => ret Binop e1' Eq_op e2'
        | ULt => ret Binop e1' Lt_op e2'
      end
    | UVar x => match lookup G x as p return (p = lookup G x) -> _ with 
                  | None => fun _ => error
                  | Some t => fun H => ret Var x (some_not_none H)
                end eq_refl
    | ULam x t1 u => 
      [t2,e] <-- elaborate ((x,t1)::G) u ; 
      ret Lam x t1 e
    | UApp u1 u2 => 
      [t1,e1] <-- elaborate G u1 ; 
      [t2,e2] <-- elaborate G u2 ; 
      match t1 return exp G t1 -> option { t : type & exp G t} with 
        | Arrow_t ta tb => 
          fun e1' => 
            e2' <- try_coerce ta e2 ; 
            ret App e1' e2'
        | _ => fun _ => error
      end e1
  end.

(* Here's an example elaboration for the increment function. *)
Definition uinc : uexp := ULam "x" Nat_t (UBinop (UVar "x") UPlus (UNum 1)).
Eval compute in (elaborate nil uinc).

(* Similarly, applying the increment function to 42. *)
Definition u2 : uexp := UApp uinc (UNum 42).
Eval compute in (elaborate nil u2).

(* Here's something that shouldn't type-check. *)
Definition u3 : uexp := UApp (UVar "notbound") (UBool true).
Eval compute in (elaborate nil u3).

(* A combined elaboration and evaluation function. *)
Definition evaluate (u:uexp) : option { t : type & tDenote t } := 
  match elaborate nil u return option { t : type & tDenote t } with 
    | None => None
    | Some (existT t e) => Some (existT (fun t => tDenote t) t (expDenote e tt))
  end.

Eval compute in evaluate uinc.
Eval compute in evaluate u2.

Lemma u2_is_42 : evaluate u2 = Some (existT _ Nat_t 43).
  auto.
Qed.  

Lemma uinc_is_id : evaluate uinc = 
                   Some (existT (fun t => tDenote t) (Arrow_t Nat_t Nat_t) (fun v => plus v 1)).
  auto.
Qed.
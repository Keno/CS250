(* Exercises at the end of the file. *)

(** Encoding semantics in Coq *)
Require Import Arith.
Require Import String.
Require Import List.
Add LoadPath "/Users/jkcl/cpdtlib".
Require Import CpdtTactics.
Set Implicit Arguments.
Unset Automatic Introduction.
Local Open Scope string_scope.

(** ** Abstract Syntax *)
Definition var := string.

Inductive binop : Type := Plus_op | Minus_op | Eq_op
                          | Mul_op | Lt_op.

Inductive exp : Type := 
| Var_e : var -> exp
| Lam_e : var -> exp -> exp
| App_e : exp -> exp -> exp
| Num_e : nat -> exp
| Binop_e : binop -> exp -> exp -> exp
| Bool_e : bool -> exp
| If_e : exp -> exp -> exp -> exp
| Let_e : var -> exp -> exp -> exp
| Fst_e : exp -> exp
| Snd_e : exp -> exp
| Pair_e : exp -> exp -> exp
| Fix_e : var -> var -> exp -> exp.

Inductive value : Type := 
| Lam_v : list (var * value) -> var -> exp -> value
| Num_v : nat -> value
| Bool_v : bool -> value
| Pair_v : value -> value -> value
| Fix_v : list (var * value) -> var -> var -> exp -> value.

Inductive answer : Type := 
| Value : value -> answer 
| TypeError : answer.

(** ** Environments *)
Definition env_t(A:Type) := list (var * A).
Fixpoint lookup A (env:env_t A) (x:var) : option A := 
  match env with 
    | nil => None
    | (y,v)::env' => if string_dec x y then Some v else lookup env' x
  end.

(** ** Binop Evaluation *)
Definition eval_binop(b:binop)(v1 v2:value) : answer := 
  match b, v1, v2 with 
    | Plus_op, Num_v n1, Num_v n2 => Value (Num_v (n1+n2))
    | Minus_op, Num_v n1, Num_v n2 => Value (Num_v (n1-n2))
    | Eq_op, Num_v n1, Num_v n2 => 
      Value (Bool_v (if eq_nat_dec n1 n2 then true else false))
    | Mul_op, Num_v n1, Num_v n2 => Value (Num_v (n1*n2))
    | Lt_op, Num_v n1, Num_v n2 => Value (Bool_v (NPeano.ltb n1 n2))
    | _, _, _ => TypeError 
  end.

(** We're going to use the Haskell-like approach, but instead of producing
    values, we'll produce "computations."  A computation is simply a way to
    reify the monad, except that we'll add an extra case for "delayed"
    expressions that we haven't bothered to compile yet.  This will allow
    us to break the cycle in our semantics, at the price of needing an
    operational definition of the meaning of a computation. *)

(** Our denotations will be computations.  Notice that we use the Coq
    function space to represent Bind.  That will greatly simplify our
    treatment of substitution in our semantics, and allow us to use
    an arbitrary Coq function to build a continuation. *)
Inductive comp := 
| Ret : answer -> comp
| Bind : comp -> (value -> comp) -> comp
| Delay : exp -> list (var * value) -> comp.

(** You should think of [Delay] as a kind of closure where we have
    some expression [e] to evaluate within an environment [env].  
    You can also think of [Delay] as an intermediate state in a 
    computation.  
*)

Notation "'ret' x" := (Ret (Value x)) (at level 75) : comp_scope.
Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2))
        (right associativity, at level 84, c1 at next level) : comp_scope.
Local Open Scope comp_scope.
Definition Terr := Ret TypeError.

(** Translate expressions to a computation -- this is exactly the same
      as the Haskell approach except that we [Delay] the compilation of
      the appliation of a function -- this is the only place where Coq 
      can't conclude that the compilation will terminate.  *)
Fixpoint compile (e:exp) (env:env_t value) : comp := 
  match e with 
    | Var_e x => 
      match lookup env x with 
        | None => Terr 
        | Some v => ret v
      end
    | Lam_e x e => ret (Lam_v env x e)
    | App_e e1 e2 => 
      v1 <- compile e1 env ; 
      v2 <- compile e2 env ; 
      match v1 with 
        | Lam_v env' x e' => Delay e' ((x,v2)::env')
        | Fix_v env' f x e' => Delay e' ((x,v2)::(f,v1)::env')
        | _ => Terr 
      end
    | Num_e n => ret Num_v n
    | Binop_e b e1 e2 => 
      v1 <- compile e1 env ; 
      v2 <- compile e2 env ; 
      Ret (eval_binop b v1 v2)
    | Bool_e b => ret Bool_v b
    | If_e e1 e2 e3 => 
      v1 <- compile e1 env ; 
      match v1 with 
        | Bool_v b => 
          if b then compile e2 env else compile e3 env
        | _ => Terr 
      end
    | Let_e x e1 e2 =>
      v <- compile e1 env ;
      compile e2 ((x, v)::env)
    | Fst_e e =>
      v <- compile e env ;
      match v with
        | Pair_v v1 v2 => ret v1
        | _ => Terr
      end
    | Snd_e e =>
      v <- compile e env ;
      match v with
        | Pair_v v1 v2 => ret v2
        | _ => Terr
      end
    | Pair_e e1 e2 =>
      v1 <- compile e1 env ;
      v2 <- compile e2 env ;
      ret (Pair_v v1 v2)
    | Fix_e f x e =>
      ret (Fix_v env f x e)
  end. (* XXX *)
  
(** Now we can define a variety of different kinds of operational
      semantics for computations, including big-step, small-step, 
      and even a partial function (since steps are deterministic.)
      The point is that the compilation doesn't preclude our modeling
      "effects" such as non-determinism (i.e., threads) or state or
      exceptions.  We just need to have the right monadic structure
      to support those things.

      The important point is that there are many, many fewer rules
      or cases to deal with in the computation space.  And this 
      will scale a lot better as we grow the source language.
  *)

(** A Big-Step Operational Semantics for Computations *)
Inductive run : comp -> answer -> Prop := 
  (* to run [Ret a], just return a. *)
| run_Ret : forall a, run (Ret a) a
  (* to run [Delay env e], call the compiler on [e] to get a
     computation [c], and then continue by running [c]. *)
| run_Delay : forall env e v, 
                run (compile e env) v -> run (Delay e env) v
  (* to run [Bind c f], run [c] -- if it results in a [Value],
     then apply [f] to the value to get a new computation, and
     continue with that.  If running [c] results in a type error,
     then just return TypeError. *)
| run_Bind_value : forall c f v a, 
                     run c (Value v) -> run (f v) a -> run (Bind c f) a
| run_Bind_typeerror : forall c f, 
                         run c TypeError -> run (Bind c f) TypeError.
Hint Constructors run.

(** A Small-Step Operational Semantics -- this is the same as
    the above, but takes one computation to the next instead of
    running sub-computations recursively. *)
Inductive step : comp -> comp -> Prop := 
| step_Delay : forall env e, step (Delay e env) (compile e env)
| step_Bind_value : forall f v, step (Bind (Ret (Value v)) f) (f v)
| step_Bind_typeerror : forall f, step (Bind (Ret TypeError) f) (Ret TypeError)
| step_Bind : forall c1 c2 f, step c1 c2 -> step (Bind c1 f) (Bind c2 f).
Hint Constructors step.

(** And we can define the steps relations as the reflexive, transitive
      closure of the (one-step) step relation.  Intuitively, [run c a] is
      equivalent to [steps c (Ret a)]
*)
Require Import Relation_Operators.
Definition steps := clos_refl_trans comp step.
Hint Constructors clos_refl_trans.

(** Alternatively, we can define a step function. And intuitively,
    [step c1 c2] holds iff [step_fn c1 = inl c2].  *)
Implicit Arguments inl [A B].
Implicit Arguments inr [A B].
Fixpoint step_fn(c:comp) : comp + answer := 
  match c with 
    | Ret a => inr a
      | Delay e env => inl (compile e env)
      | Bind c1 f => 
        match step_fn c1 with 
          | inl c2 => inl (Bind c2 f)
          | inr (Value v) => inl (f v)
          | inr TypeError => inr TypeError
        end
  end.

Notation "c1 '==>1' c2" := (step c1 c2) (at level 80) : evals_scope.
Notation "c1 '==>*' c2" := (steps c1 c2) (at level 80) : evals_scope.
Local Open Scope evals_scope.

(** Two different notions of evaluation -- [evals1] uses the big-step
      semantics, and [evals2] uses the small-step semantics.  How would
      you define an evals3 using [step_fn]?  *)
Definition evals1 (env:env_t value) (e:exp) (a:answer) := run (compile e env) a.
Definition evals2 (env:env_t value) (e:exp) (a:answer) := 
  (compile e env) ==>* (Ret a).

Notation "env |= e ==> a" := (evals2 env e a) (at level 80) : evals_scope.

(*************************************************************)
(** Typing                                                  **)
(*************************************************************)

(** ** Expression Typing *)
Inductive type : Type :=
| Nat_t : type
| Bool_t : type
| Arrow_t : type -> type -> type
| Pair_t : type -> type -> type.

Reserved Notation "G |-- e ; t" (at level 80).  

(** Typing rules for our expressions *)
Inductive hasType : env_t type -> exp -> type -> Prop := 
| Var_ht : forall G x t, 
    lookup G x = Some t -> 
      G |-- Var_e x ; t
| Lam_ht : forall G x e t1 t2, 
    ((x,t1)::G) |-- e ; t2 -> 
      G |-- Lam_e x e ; Arrow_t t1 t2
| App_ht : forall G e1 e2 t1 t2, 
    G |-- e1 ; (Arrow_t t1 t2) -> 
    G |-- e2 ; t1 -> 
      G |-- App_e e1 e2 ; t2
| Num_ht : forall G n, 
    G |-- Num_e n ; Nat_t
| Binop_ht : forall G b e1 e2, 
    G |-- e1 ; Nat_t -> 
    G |-- e2 ; Nat_t -> 
      G |-- Binop_e b e1 e2 ; match b with | Eq_op | Lt_op => Bool_t | _ => Nat_t end
| Bool_ht : forall G b,
    G |-- Bool_e b ; Bool_t
| If_ht : forall G e1 e2 e3 t, 
    G |-- e1 ; Bool_t -> 
    G |-- e2 ; t -> 
    G |-- e3 ; t -> 
      G |-- If_e e1 e2 e3 ; t
| Let_ht : forall G x e1 e2 t t',
    G |-- e1 ; t' ->
    ((x,t')::G) |-- e2 ; t ->
      G |-- Let_e x e1 e2; t
| Pair_ht : forall G e1 e2 t1 t2,
    G |-- e1 ; t1 ->
    G |-- e2 ; t2 ->
      G |-- Pair_e e1 e2; Pair_t t1 t2
| Fix_ht : forall G f x e t1 t2,
    ((x,t1)::(f,Arrow_t t1 t2)::G) |-- e ; t2 ->
      G |-- Fix_e f x e ; Arrow_t t1 t2
where "G |-- e ; t" := (hasType G e t) : typing_scope.
Hint Constructors hasType.

(** ** Value, Environment, and Answer Typing *)
Section ValueTyping.
  Local Open Scope typing_scope.

  (** Notice that we need value and environments definitions
      to be mutually recursive.  Also notice that by choosing
      inductive definitions, we rule out "circular" lambdas.  If
      we picked CoInductive instead, we could model this sort of
      case... *)
  Inductive valType : value -> type -> Prop := 
  | Num_vt : forall n, valType (Num_v n) Nat_t
  | Bool_vt  : forall b, valType (Bool_v b) Bool_t
  | Lam_vt : forall env x e G t1 t2, 
    envType env G -> 
    (x,t1)::G |-- e ; t2 -> 
      valType (Lam_v env x e) (Arrow_t t1 t2)
  | Pair_vt : forall v1 v2 t1 t2, valType (Pair_v v1 v2) (Pair_t t1 t2)
  | Fix_vt : forall env f x e G t1 t2,
    envType env G ->
    (x,t1)::(f,Arrow_t t1 t2)::G |-- e ; t2 ->
      valType (Fix_v env f x e) (Arrow_t t1 t2)
  with envType : env_t value -> env_t type -> Prop := 
  | Nil_et : envType nil nil 
  | Cons_et : forall x v t env G, 
    valType v t -> 
    envType env G -> 
    envType ((x,v)::env) ((x,t)::G).
End ValueTyping.
Hint Constructors valType envType.

(** We don't really need this induction scheme, but whenever
    I have mutually inductive definitions, I always generate
    this in case I do need it. *)
Scheme valType_ind_2 := Induction for valType Sort Prop
  with envType_ind_2  := Induction for envType Sort Prop.
Combined Scheme valenvType_ind from valType_ind_2, envType_ind_2.

Inductive ansType : answer -> type -> Prop := 
| Val_ans : forall v t, valType v t -> ansType (Value v) t.
Hint Constructors ansType.

(** Now let's prove that our new semantics respects the typing rules. *)
Open Scope typing_scope.

(** Typing for computations:  Notice that the type for bind! *)
Inductive compType : comp -> type -> Prop := 
| Ret_ct : forall a t, ansType a t -> compType (Ret a) t
| Delay_ct : forall e env G t, 
               envType env G -> G |-- e ; t -> 
                                          compType (Delay e env) t
| Bind_ct : 
    forall c f t1 t,
      compType c t1 -> 
      (forall v, valType v t1 -> compType (f v) t) -> compType (Bind c f) t.
Hint Constructors compType.

Ltac mysimp := simpl in * ; intros ; subst ; try congruence ; 
    match goal with 
      | [ |- context[string_dec ?x ?y] ] => destruct (string_dec x y)
      | [ H : Some _ = Some _ |- _ ] => injection H ; clear H
      | [ IH : forall _, envType _ ?G -> compType (compile ?e _) _, 
            H: envType ?env ?G |- _] => 
        generalize (IH env H) ; clear IH ; intro IH
      | [ |- forall _, _ ] => intro
      | _ => eauto
    end.

Ltac pv := 
  match goal with 
    | [ H : lookup _ _ = Some _, H0:envType _ _ |- context[lookup _ _]] => 
      generalize H ; induction H0 
    | [ H : valType _ Nat_t |- _ ] => inversion H ; clear H 
    | [ H : valType _ Bool_t |- _ ] => inversion H ; clear H 
    | [ H : valType _ (Arrow_t _ _) |- _ ] => inversion H ; clear H
    | [ |- context[compType(if ?b then _ else _) _] ] => destruct b
    | [ |- compType (Bind _ _) _ ] => econstructor ; eauto
    | [ |- compType (Delay _ _) _ ] => econstructor ; eauto
    | [ |- compType (Ret (eval_binop ?b (Num_v _) (Num_v _))) _ ] => 
      destruct b ; repeat mysimp
  end ; repeat mysimp.

(** The compiler preserves types. *)
Lemma CompPreserves : 
  forall G e t, G |-- e ; t -> 
     forall env, envType env G -> compType (compile e env) t.
Proof.
  induction 1 ; crush ; repeat pv ; eauto.
Qed. 

(** A small step preserves types *)
Lemma StepPreserves : 
  forall c c', 
    c ==>1 c' -> forall t, compType c t -> compType c' t.
Proof.
  Ltac s := 
    match goal with 
      | [ |- compType (compile _ _) _ ] => eapply CompPreserves ; eauto
      | [ H : compType (ret _) _ |- _ ] => inversion H ; clear H ; subst
      | [ H : ansType (Value _) _ |- _ ] => inversion H ; clear H ; subst
      | [ H : compType (Ret TypeError) _ |- _] => inversion H ; clear H ; subst
      | [ H : ansType TypeError _ |- _ ] => inversion H
      | _ => eauto 
    end.
  
  induction 1 ; crush ;  
  match goal with | [ H : compType _ _ |- _ ] => inversion H ; subst end ; 
  repeat s.
Qed.

  (** The reflexive/transitive closure of the step relation preserves types. *)
Lemma StepsPreserves : 
  forall c c' t, c ==>* c' -> compType c t -> compType c' t.
Proof.
  induction 1 ; auto ; eapply StepPreserves ; auto. 
Qed.

(** Putting the translation and the compuation lemmas together, we get that
      any expression which has type t and that evaluates to an answer, produces 
      an answer of type t. *)
Lemma Preservation : 
  forall env e a, 
    env |= e ==> a -> 
    forall G t, 
      envType env G -> 
      G |-- e ; t -> ansType a t.
Proof.
  intros env e a H G t H1 H2 ; 
  generalize (StepsPreserves H (CompPreserves H2 H1)) ; 
  inversion 1 ; subst ; auto.
Qed.

(** Good exercises: **)

(*
  - Add new binary operations, such as Mul_op and Lt_op, and
    fix all the proofs as they break. 
*)

(* NO PROOF BREAKAGE?! *)

(*
  - Add a "let" construct, and fix the proofs.  
*)

(* NO PROOF BREAKAGE?! *)

(*
  - Add a new type (Pair_t : type -> type -> type), expressions 
    (Pair_e : exp -> exp -> exp) (Fst_e : exp -> exp) and (Snd_e : exp) 
    and a value (Pair_v : value -> value -> value).  Again, where do the 
    definitions and the proofs have to change?
*)

(* NO PROOF BREAKAGE?! *)

(*
  - Add a "fix" construct.  The expression (fix f(x) := e) should
    provide a recursive function for evaluating e.  Typing fix is
    pretty easy:

        f : t1 -> t2, x : t1, G |-- e : t2
        ----------------------------------
        G |-- fix f(x) := e : t1 -> t2

    Building something that actually evaluates properly is not so
    easy.  Inuitively, when I evaluate (fix f(x):=e), I get a closure
    out, similar to the case when I evaluate a lambda-expression.
    When I apply a recursive closure generated by (fix f(x):=e),
    you need to not only provide a binding for x in the environment,
    but also for f.  

    You will need to modify the definition of value to 
    accomplish this.  Note that you may find it easier to encode 
    non-recursive functions as a special case of recursive functions.  
*)

(* NO PROOF BREAKAGE?! *)

(*
  - Prove a progress theorem for well-typed computations:  
    If compType c t then either c is a well-typed answer, 
    or else c ==>1 c'.  
*)

Theorem Progress :
  forall c t, compType c t -> match c with Ret a => ansType a t | _ => exists c', c ==>1 c' end.
  (*forall c t, compType c t -> (exists a, c = Ret a -> ansType a t) \/ (exists c', c ==>1 c').*)
Proof.
  (* CLEAN UP *)

  induction 1; [ crush | exists (compile e env); econstructor | .. ]; destruct c.

  (* Ret *)
  destruct a.
  (* Ret-val *)
  specialize H0 with (v:=v);
  specialize H1 with (v:=v);
  destruct (f v);
  specialize step_Bind_value with (f:=f) (v:=v); intros; eauto.
  (* Ret-err *)
  specialize step_Bind_typeerror with (f:=f); intros; eauto.

  (* Bind *)
  destruct IHcompType as [ x IHcompType ].
  specialize step_Bind with (c1:=c) (c2:=x) (f:=f); intros; eauto.

  (* Delay *)
  destruct IHcompType as [ x IHcompType ].
  specialize step_Delay with (env:=l) (e:=e); intros; eauto.
Qed.

(*
  - Prove a type-soundness theorem:  if e is a well-typed
    program in the empty environment, then it is not the
    case that e ==>* TypeError
*)

(*
  - Prove that (evals1 c a) <-> (evals2 c a).  
*)

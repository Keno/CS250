Require Import Bool Arith String List CpdtTactics.
Open Scope string_scope.

Definition var := string.

Inductive binop := Plus | Times | Minus.

Inductive aexp : Type := 
| Const : nat -> aexp
| Var : var -> aexp
| Binop : aexp -> binop -> aexp -> aexp.

Inductive bexp : Type := 
| Tt : bexp
| Ff : bexp
| Eq : aexp -> aexp -> bexp
| Lt : aexp -> aexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp
| Not : bexp -> bexp.

Inductive com : Type := 
| Skip : com
| Assign : var -> aexp -> com
| Seq : com -> com -> com
| If : bexp -> com -> com -> com
| While : bexp -> com -> com.

Definition state := var -> nat.

Definition get (x:var) (s:state) : nat := s x.

Definition set (x:var) (n:nat) (s:state) : state := 
  fun y => 
    match string_dec x y with 
        | left H => n 
        | right H' => get y s
    end.

Definition eval_binop (b:binop) : nat -> nat -> nat := 
  match b with 
    | Plus => plus
    | Times => mult
    | Minus => minus
  end.

Fixpoint eval_aexp (e:aexp) (s:state) : nat := 
  match e with 
    | Const n => n
    | Var x => get x s
    | Binop e1 b e2 => (eval_binop b) (eval_aexp e1 s) (eval_aexp e2 s)
  end.

Fixpoint eval_bexp (b:bexp) (s:state) : bool := 
  match b with 
    | Tt => true
    | Ff => false
    | Eq e1 e2 => NPeano.Nat.eqb (eval_aexp e1 s) (eval_aexp e2 s)
    | Lt e1 e2 => NPeano.ltb (eval_aexp e1 s) (eval_aexp e2 s)
    | And b1 b2 => eval_bexp b1 s && eval_bexp b2 s
    | Or b1 b2 => eval_bexp b1 s || eval_bexp b2 s
    | Not b => negb (eval_bexp b s)
  end.

Inductive eval_com : com -> state -> state -> Prop := 
| Eval_skip : forall s, eval_com Skip s s
| Eval_assign : forall s x e, eval_com (Assign x e) s (set x (eval_aexp e s) s)
| Eval_seq : forall c1 s0 s1 c2 s2, 
               eval_com c1 s0 s1 -> eval_com c2 s1 s2 -> eval_com (Seq c1 c2) s0 s2
| Eval_if_true : forall b c1 c2 s s',
                   eval_bexp b s = true -> 
                   eval_com c1 s s' -> eval_com (If b c1 c2) s s'
| Eval_if_false : forall b c1 c2 s s',
                   eval_bexp b s = false -> 
                   eval_com c2 s s' -> eval_com (If b c1 c2) s s'
| Eval_while_false : forall b c s, 
                       eval_bexp b s = false -> 
                       eval_com (While b c) s s
| Eval_while_true : forall b c s1 s2 s3, 
                      eval_bexp b s1 = true -> 
                      eval_com c s1 s2 -> 
                      eval_com (While b c) s2 s3 -> 
                      eval_com (While b c) s1 s3.

Definition prog1 := 
  Seq (Assign "y" (Const 1))
  (Seq (Assign "x" (Const 3))
       (While (Lt (Const 0) (Var "x"))
              (Seq (Assign "y" (Binop (Var "y") Times (Const 2)))
                   (Assign "x" (Binop (Var "x") Minus (Const 1)))))).

Definition prog2 := While Tt Skip.

Ltac myinj H := injection H ; intros ; subst ; clear H.

Lemma while_true_imp_false : forall c s1 s2, eval_com c s1 s2 -> 
                                             forall b c', (forall s, eval_bexp b s = true) -> 
                                                          c = While b c' -> 
                                                          False. 
Proof.
  Ltac foo := 
  match goal with 
    | [ H : ?x _ _ = ?x _ _ |- _ ] => myinj H
    | [ H : forall s, eval_bexp _ s = _,
        H' : eval_bexp _ ?s0 = _ |- _] => 
      specialize (H s0) ; congruence
    | [ H : forall b c, _ -> _ |- _ ] => eapply H ; eauto
  end.

  induction 1 ; intros ; try discriminate ; repeat foo.
Qed.
  
Lemma prog2_div : forall s1 s2, eval_com prog2 s1 s2 -> False.

  Lemma prog2_div' : forall c s1 s2, eval_com c s1 s2 -> c = prog2 -> False.
  Proof.
    unfold prog2 ; induction 1; crush.
  Qed.
  Show.
  intros. apply (prog2_div' _ _ _ H eq_refl).
Qed.

(* A simple chained tactic *)
Ltac myinv H := inversion H ; subst ; clear H ; simpl in *.

(* This tactic applies when we have a hypothesis involving
   eval_com of either a Seq or an Assign.  It inverts the
   hypothesis, and performs substitution, simplifying things.
*)
Ltac eval_inv := 
  match goal with 
    | [ H : eval_com (Seq _ _) _ _ |- _ ] => myinv H
    | [ H : eval_com (Assign _ _) _ _ |- _ ] => myinv H
  end.

(* This tactic inverts an eval_com of a While, producing
   two sub-goals.  It tries to eliminate one (or both) of the goals
   through discrimination on the hypotheses.
*)
Ltac eval_while_inv := 
  match goal with
    | [ H : eval_com (While _ _) _ _ |- _ ] => myinv H ; try discriminate
  end.

Theorem prog1_prop : forall s1 s2, eval_com prog1 s1 s2 -> get "x" s2 = 0.
Proof.
  unfold prog1 ; intros.
  repeat ((repeat eval_inv) ; eval_while_inv).
  auto.
Qed.

Theorem seq_assoc : 
  forall c1 c2 c3 s1 s2, 
    eval_com (Seq (Seq c1 c2) c3) s1 s2 -> 
    eval_com (Seq c1 (Seq c2 c3)) s1 s2.
  Lemma seq_assoc' : 
    forall c s1 s2, 
      eval_com c s1 s2 -> 
      forall c1 c2 c3,
        c = Seq (Seq c1 c2) c3 -> 
        eval_com (Seq c1 (Seq c2 c3)) s1 s2.
  Proof.
    (* Adds all of the eval_com constructors as hints for auto/crush *)
    Hint Constructors eval_com.
    induction 1 ; crush.
    inversion H ; clear H ; subst ; 
    econstructor ; eauto.
  Qed.

  intros. eapply seq_assoc' ; eauto.
Qed.

(* Returns true when the variable x occurs as a subexpression of a *)
Fixpoint contains (x:var) (a:aexp) : bool := 
  match a with 
    | Const _ => false
    | Var y => if string_dec x y then true else false
    | Binop a1 _ a2 => contains x a1 || contains x a2
  end.

(* Changing a variable x that doesn't occur in a doesn't effect the 
   value of a. *)
Lemma eval_exp_set : 
  forall s x n a,
    contains x a = false -> 
    eval_aexp a (set x n s) = eval_aexp a s.
Proof.
  induction a ; unfold set, get ; simpl ; unfold get ; crush.
  destruct (string_dec x v) ; crush.
  destruct (contains x a1) ; crush.
Qed.  

(* We can commute assignments x:=ax; y:=ay  as long as the
   variables don't overlap. *)
Lemma assign_comm : 
  forall x ax y ay s1 s2,
    eval_com (Seq (Assign x ax) (Assign y ay)) s1 s2 -> 
    contains x ay = false -> 
    contains y ax = false -> 
    x <> y -> 
    forall s3, eval_com (Seq (Assign y ay) (Assign x ax)) s1 s3 -> s2 = s3.
(*
               forall z, get z s3 = get z s2.
*)
Proof.
  intros.
  repeat eval_inv.
  repeat unfold set, get.
  destruct (string_dec x z) ; destruct (string_dec y z) ; try congruence.
  specialize (eval_exp_set s1 y (eval_aexp ay s1) ax H1).
  unfold set. crush.
  specialize (eval_exp_set s1 x (eval_aexp ax s1) ay H0).
  unfold set. crush.
Qed.


Lemma assign_comm2 : 
  forall x ax y ay s1 s2,
    eval_com (Seq (Assign x ax) (Assign y ay)) s1 s2 -> 
    contains x ay = false -> 
    contains y ax = false -> 
    x <> y -> 
    eval_com (Seq (Assign y ay) (Assign x ax)) s1 s2.
Proof.
  intros.
  remember (set x (eval_aexp ax (set y (eval_aexp ay s1) s1))
                (set y (eval_aexp ay s1) s1)) as s3.
  assert (eval_com (Seq (Assign y ay) (Assign x ax)) s1 s3).
  rewrite Heqs3.
  eauto.
  specialize (assign_comm x ax y ay s1 s2 H H0 H1 H2 _ H3).
  intro.
  assert (s3 = s2).
  Focus 2.
  rewrite <- H5.
  auto.
  Admitted.

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
  fun y => if string_dec x y then n else get y s.

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

Theorem prog1_prop : forall s1 s2, eval_com prog1 s1 s2 -> get "x" s2 = 0.
Proof.
  intros.
  unfold prog1 in H.
  inversion H. clear H ; subst.
  inversion H2. clear H2 ; subst.
  inversion H5 ; clear H5 ; subst.
  inversion H1 ; clear H1 ; subst.
  inversion H4 ; clear H4 ; subst.
  assert False.
  simpl in *. unfold get, set in * ; simpl in *.
  crush.
  contradiction.
  clear H1.
  inversion H2 ; clear H2 ; subst.
  inversion H5 ; clear H5 ; subst.
  inversion H1 ; clear H1 ; subst. simpl in *.
  inversion H6 ; clear H6 ; subst.
  assert False.
  simpl in *. unfold get, set in * ; simpl in *. crush.
  contradiction.
  clear H1.
  inversion H2 ; clear H2 ; subst.
  inversion H6 ; clear H6 ; subst.
  inversion H1 ; clear H1 ; subst.
  simpl in *.
  inversion H5 ; clear H5 ; subst.
  simpl in *. unfold get, set in * ; simpl in *. crush.
  clear H1.
  inversion H2 ; clear H2 ; subst.
  inversion H5 ; clear H5 ; subst.
  inversion H1 ; clear H1 ; subst. simpl in *.
  inversion H6 ; clear H6 ; subst. 
  unfold get, set. simpl. 
  reflexivity.
  clear H2 H5. assert False. simpl in *.
  unfold get, set in H1. simpl in H1. crush.
  contradiction.
Qed.

Definition prog2 := While Tt Skip.

Theorem prog2_div : forall c s1 s2, eval_com c s1 s2 -> c = prog2 -> False.
Proof.
  unfold prog2 ; induction 1 ; crush.
Qed.

Theorem seq_assoc : 
  forall c s1 s2, 
    eval_com c s1 s2 -> 
    forall c1 c2 c3,
      c = Seq (Seq c1 c2) c3 -> 
      eval_com (Seq c1 (Seq c2 c3)) s1 s2.
Proof.
  Hint Constructors eval_com.
  induction 1 ; crush.
  inversion H ; clear H ; subst ; 
  econstructor ; eauto.
Qed.
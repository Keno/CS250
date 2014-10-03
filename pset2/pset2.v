(* Jao-ke Chin-Lee *)
Add LoadPath "/home/jkcl/Dropbox/College/Year4/CS250/jchinlees-cs250-psets/cpdtlib".
Require Import Bool Arith String List CpdtTactics.
Require Import FunctionalExtensionality.
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

Check string_dec.

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
               eval_com c1 s0 s1 -> eval_com c2 s1 s2 -> 
               eval_com (Seq c1 c2) s0 s2
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

(* Write a function ieval_com : nat -> com -> state -> option state
   which takes "fuel" as an argument and tries to run the command
   for fuel-number of steps.  If the command terminates in that time,
   then you should return the resulting state, and if it doesn't
   terminate in that time, you should return None.  
*)
Fixpoint ieval_com (fuel:nat) (c:com) (s:state) {struct fuel} : option state :=
  match fuel with
    | 0 => None
    | S n =>
      match c with
        | Skip => Some s
        | Assign x a => let v := eval_aexp a s in Some (set x v s)
        | Seq c1 c2 =>
          match ieval_com n c1 s with
            | None => None
            | Some s' => ieval_com n c2 s'
          end
        | If b c1 c2 =>
          if eval_bexp b s then ieval_com n c1 s
          else ieval_com n c2 s
        | While b c' => (*ieval_com n (If b (Seq c' c) Skip) s*)
          if eval_bexp b s then ieval_com n (Seq c' c) s
          else Some s
      end
  end.

Lemma seq_intermed : forall fuel c1 c2 s1 s2, ieval_com (S fuel) (Seq c1 c2) s1 = Some s2 ->
                                              exists s', ieval_com fuel c1 s1 = Some s' /\
                                                         ieval_com fuel c2 s' = Some s2.
Proof.
  intros.
  simpl in H.
  remember (ieval_com fuel c1 s1) as x; destruct x; [ exists s | contradict H ]; crush.
Qed.

Ltac unroll :=
  match goal with
    | [ |- ieval_com (S ?X) _ _ = _] =>
      let y := fresh in let Heqy := fresh in
      remember X as y eqn:Heqy; simpl ieval_com; rewrite Heqy
  end.

Lemma ieval_com_plus' : forall fuel c s1 s2, ieval_com (S fuel) c s1 = Some s2 ->
                                             ieval_com (S (S fuel)) c s1 = Some s2.
Proof.
  intro fuel.
  induction fuel.
  (* Base case *)
  intros.
  inversion H.
  destruct c.
  (* Skip *) crush.
  (* Assign *) crush.
  (* Seq *) contradict H1. crush.
  (* If *)
  remember (eval_bexp b s1) as x in H1; destruct x; contradict H1; crush.
  (* While-T *)
  remember (eval_bexp b s1) as x in H1; destruct x.
  contradict H1; crush.
  (* While-F *)
  unfold ieval_com; reflexivity.
  (* Inductive step *)
  destruct c.  intros.
  (* Skip *)
  simpl in *. apply H.
  (* Assign *)
  simpl in *. crush.
  (* Seq *)
  intros.
  remember (S (S fuel)) as m.
  simpl ieval_com.
  remember (ieval_com m c1 s1) as x; destruct x.
  specialize seq_intermed with (fuel:=(S fuel)) (c1:=c1) (c2:=c2) (s1:=s1) (s2:=s2).
  intros.
  rewrite Heqm in H. apply H0 in H. clear H0.
  destruct H.
  destruct H.
  assert (IHfuel1:=IHfuel).
  specialize IHfuel1 with (c:=c1) (s1:=s1) (s2:=x).
  apply IHfuel1 in H. clear IHfuel1.
  assert (IHfuel2:=IHfuel).
  specialize IHfuel2 with (c:=c2) (s1:=x) (s2:=s2).
  apply IHfuel2 in H0. clear IHfuel2.
  rewrite <- Heqx in H.
  injection H.
  intros.
  rewrite H1. apply H0.
  remember (S fuel) as m'. rewrite Heqm in H.
  simpl ieval_com in H.
  remember (ieval_com m' c1 s1) as x; destruct x.
  assert (IHfuel1:=IHfuel).
  specialize IHfuel1 with (c:=c1) (s1:=s1) (s2:=s).
  apply eq_sym in Heqx0. apply IHfuel1 in Heqx0. clear IHfuel1.
  apply eq_sym in Heqx. contradict Heqx. crush. apply H.
  (* If *)
  intros.
  remember (S (S fuel)) as m.
  simpl ieval_com.
  remember (eval_bexp b s1) as x; destruct x;
  remember (S fuel) as m'; rewrite Heqm in H;
  simpl ieval_com in H; rewrite <- Heqx in H; assert (IHfuel1:=IHfuel);
  [ specialize IHfuel1 with (c:=c1) (s1:=s1) (s2:=s2)
  | specialize IHfuel1 with (c:=c2) (s1:=s1) (s2:=s2) ];
  apply IHfuel1 in H; apply H.
  (* While *)
  intros.
  remember (S fuel) as m.
  simpl ieval_com in H.
  remember (eval_bexp b s1) as x; destruct x.
  remember (Seq c (While b c)) as c'; destruct c'.
  crush. crush.
  unroll.
  rewrite <- Heqx.
  rewrite Heqc' in H.
  assert (IHfuel1:=IHfuel).
  specialize IHfuel1 with (c:=(Seq c (While b c))) (s1:=s1) (s2:=s2).
  apply IHfuel1 in H. clear IHfuel1.
  rewrite H1 in H.
  apply H.
  contradict Heqc'. crush.
  contradict Heqc'. crush.
  unroll.
  rewrite <- Heqx.
  apply H.
Qed.

Lemma ieval_com_plus : forall fuel c s1 s2, ieval_com fuel c s1 = Some s2 ->
                                            forall more, ieval_com (fuel+more) c s1 = Some s2.
Proof.
  induction fuel.
  crush.
  intros.
  induction more.
  rewrite plus_comm.
  crush.
  rewrite NPeano.Nat.add_succ_r.
  specialize ieval_com_plus' with (fuel:=(fuel + more)) (c:=c) (s1:=s1) (s2:=s2).
  intros.
  apply H0 in IHmore. assumption.
Qed.

(* Prove that :

   eval_com c s1 s2 -> exists n, ieval_com n c s1 = Some s2.

*)
Theorem if_eval_then_fuel : forall c s1 s2, eval_com c s1 s2 ->
                                            exists n, ieval_com n c s1 = Some s2.
Proof.
  intros.
  induction H.
  (* Skip *)
  exists 1. crush.
  (* Assign *)
  exists 1. crush.
  (* Seq *)
  destruct IHeval_com1. destruct IHeval_com2.
  specialize ieval_com_plus with (fuel:=x) (c:=c1) (s1:=s0) (s2:=s1).
  intros. crush. specialize H4 with (more:=x0).
  specialize ieval_com_plus with (fuel:=x0) (c:=c2) (s1:=s1) (s2:=s2).
  intros. crush. specialize H5 with (more:=x).
  rewrite plus_comm in H4.
  exists (S (x0+x)).
  simpl ieval_com. crush.
  (* If-T *)
  destruct IHeval_com.
  exists (S x).
  simpl ieval_com; crush.
  (* If-F *)
  destruct IHeval_com.
  exists (S x).
  simpl ieval_com. crush.
  (* While-F *)
  exists 1. crush.
  (* While-T *)
  destruct IHeval_com1. destruct IHeval_com2.
  specialize ieval_com_plus with (fuel:=x) (c:=c) (s1:=s1) (s2:=s2).
  intros. crush. specialize H5 with (more:=x0).
  specialize ieval_com_plus with (fuel:=x0) (c:=(While b c)) (s1:=s2) (s2:=s3).
  intros. crush. specialize H6 with (more:=x).
  rewrite plus_comm in H5.
  exists (S (S (x0+x))).
  simpl ieval_com.
  crush.
Qed.

Theorem if_fuel_then_eval : forall n c s1 s2, ieval_com n c s1 = Some s2 ->
                                              eval_com c s1 s2.
Proof.
  Lemma if_fuel_then_eval' : forall n c s1 s2, ieval_com (S n) c s1 = Some s2 ->
                                               eval_com c s1 s2.
    Proof.
      induction n.
      intros.
      destruct c.
      crush. constructor.
      crush. constructor.
      crush.
      crush.
      (* If *)
      remember (eval_bexp b s1) as x; destruct x; contradict H; crush.
      (* While *)
      crush.
      remember (eval_bexp b s1) as x; destruct x.
      contradict H. crush.
      injection H. intros. clear H.
      rewrite H0.
      apply eq_sym in Heqx.
      constructor. crush.
      intros.
      destruct c.
      crush.
      crush.
      (* Seq *)
      remember (S n) as m.
      simpl in H.
      remember (ieval_com m c1 s1) as x; destruct x.
      apply eq_sym in Heqx.
      assert (IHn1:=IHn). assert (IHn2:=IHn).
      specialize IHn1 with (c:=c1) (s1:=s1) (s2:=s).
      specialize IHn2 with (c:=c2) (s1:=s) (s2:=s2).
      apply IHn1 in Heqx. clear IHn1.
      apply IHn2 in H. clear IHn2.
      apply Eval_seq with (c1:=c1) (s0:=s1) (s1:=s) (c2:=c2) (s2:=s2).
      crush. apply H.
      contradict H. crush.
      (* If-T *)
      remember (S n) as m.
      simpl in H.
      remember (eval_bexp b s1) as x; destruct x.
      apply eq_sym in Heqx.
      constructor. apply Heqx. crush.
      (* If-F *)
      apply eq_sym in Heqx.
      apply Eval_if_false with (b:=b) (c1:=c1) (c2:=c2) (s:=s1) (s':=s2).
      apply Heqx. crush.
      (* While-T *)
      remember (S n) as m.
      simpl in H.
      remember (eval_bexp b s1) as x; destruct x.
      apply eq_sym in Heqx.
      specialize seq_intermed with (fuel:=m) (c1:=c) (c2:=(While b c)) (s1:=s1) (s2:=s2).
      intros.
      specialize ieval_com_plus with (fuel:=m) (c:=(Seq c (While b c))) (s1:=s1) (s2:=s2).
      intros.
      apply H1 with (more:=1) in H. clear H1.
      rewrite plus_comm in *.
      apply H0 in H. clear H0.
      destruct H.
      destruct H.
      assert (IHn1:=IHn). assert (IHn2:=IHn).
      specialize IHn1 with (c:=c) (s1:=s1) (s2:=x).
      apply IHn1 in H. clear IHn1.
      specialize IHn2 with (c:=(While b c)) (s1:=x) (s2:=s2).
      apply IHn2 in H0. clear IHn2.
      apply Eval_while_true with (b:=b) (c:=c) (s1:=s1) (s2:=x) (s3:=s2).
      apply Heqx. apply H. apply H0.
      (* While-F *)
      apply eq_sym in Heqx.
      injection H.
      intros. clear H.
      rewrite <- H0.
      constructor. apply Heqx.
    Qed.
    Show.
    destruct n.
    intros. simpl in H. crush.
    apply if_fuel_then_eval'.
Qed.

(* Write a function

     optimize_com : com -> com

   which tries to optimize a command and the sub-expressions 
   within it.  In particular, your optimizer should at least:

   * replace (a + 0) and (0 + a) with a
   * replace (a - 0) with a
   * replace (a * 1) and (1 * a) with a
   * replace (a * 0) and (0 * a) with 0

   * replace (a == a) with Tt
   * replace (a < a) with Ff
   * replace (Tt && Tt) with Tt
   * replace (Tt || b) and (b || Tt) with Tt
   * replace (Ff && b) and (b && Ff) with Ff

   * replace (skip ; c) and (c ; skip) with c
   * replace (if Tt c1 else c2) with c1
   * replace (if Ff c1 else c2) with c2
*)
Fixpoint optimize_aexp (a:aexp) : aexp :=
  match a with
    | Binop a1 op a2 =>
      let (a1', a2') := (optimize_aexp a1, optimize_aexp a2) in
      match op with
        | Minus => match a2' with Const 0 => a1' | _ => Binop a1' Minus a2' end
        | Plus =>
          match (a1', a2') with
            | (Const 0, _) => a2'
            | (_, Const 0) => a1'
            | (_, _) => Binop a1' Plus a2'
          end
        | Times =>
          match (a1', a2') with
            | (Const 0, _) => Const 0
            | (Const 1, _) => a2'
            | (_, Const 0) => Const 0
            | (_, Const 1) => a1'
            | (_, _) => Binop a1' Times a2'
          end
      end
    | _ => a
  end.

Definition eq_aexp_dec (a1 a2:aexp) : {a1=a2} + {a1<>a2}.
  decide equality.
  apply (eq_nat_dec n n0).
  apply (string_dec v v0).
  decide equality.
Defined.

Fixpoint optimize_bexp (b:bexp) : bexp :=
  match b with
    | Eq a1 a2 =>
      let (a1', a2') := (optimize_aexp a1, optimize_aexp a2) in
      match eq_aexp_dec a1' a2' with
        | left _ => Tt
        | right _ => Eq a1' a2'
      end
    | Lt a1 a2 =>
      let (a1', a2') := (optimize_aexp a1, optimize_aexp a2) in
      match eq_aexp_dec a1' a2' with
        | left _ => Ff
        | right _ => Lt a1' a2'
      end
    | And b1 b2 =>
      let (b1', b2') := (optimize_bexp b1, optimize_bexp b2) in
      match (b1', b2') with
        | (Tt, Tt) => Tt
        | (Tt, Ff) | (Ff, Tt) | (Ff, Ff) => Ff
        | _ => And b1' b2'
      end
    | Or b1 b2 =>
      let (b1', b2') := (optimize_bexp b1, optimize_bexp b2) in
      match (b1', b2') with
        | (Tt, _) | (_, Tt) => Tt
        | (Ff, Ff) => Ff
        | _ => Or b1' b2'
      end
    | Not b' =>
      let b'' := optimize_bexp b' in
      match b' with
        | Tt => Ff
        | Ff => Tt
        | _ => Not b''
      end
    | _ => b
  end.

Fixpoint optimize_com (c:com) : com :=
  match c with
    | Skip => Skip
    | Assign x a => Assign x (optimize_aexp a)
    | Seq c1 c2 =>
      let (c1', c2') := (optimize_com c1, optimize_com c2) in
      match c1' with
        | Skip => c2'
        | _ => match c2' with Skip => c1' | _ => Seq c1' c2' end
      end
    | If b c1 c2 =>
      let b' := optimize_bexp b in
      match b' with
        | Tt => optimize_com c1
        | Ff => optimize_com c2
        | _ => If b' (optimize_com c1) (optimize_com c2)
      end
    | While b c' =>
      let b' := optimize_bexp b in
      match b' with
        | Ff => Skip
        | _ => While b' (optimize_com c')
      end
  end.

(* Construct a proof that optimizing a program doesn't change its
   input/output behavior.  That is, show that if we start in state
   s1 and evaluate c to get state s2, then if we evaluate 
   optimize_com(c) in state s1, we get out a state that is
   extensionally equivalent to s2.  
*)

Lemma aopt_ok : forall e s, eval_aexp e s = eval_aexp (optimize_aexp e) s.
Proof.
  induction e; intros; [ crush | crush | .. ]; simpl optimize_aexp; destruct b; simpl.

  remember (optimize_aexp e1) as e1'; destruct e1'; specialize IHe1 with (s:=s); specialize IHe2 with (s:=s).

  destruct n. rewrite IHe1. rewrite <- IHe2. simpl. crush. (* or reflexivity instead of crush *)
  remember (optimize_aexp e2) as e2'; destruct e2'.
  destruct n0. rewrite <- IHe1. rewrite IHe2. simpl. crush.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. omega.
  
  remember (optimize_aexp e2) as e2'; destruct e2'.
  destruct n. rewrite IHe1. rewrite IHe2. simpl. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. omega.

  remember (optimize_aexp e2) as e2'; destruct e2'.
  destruct n. rewrite IHe1. rewrite IHe2. simpl. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. simpl. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. simpl. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. simpl. omega.

  remember (optimize_aexp e1) as e1'; destruct e1'; specialize IHe1 with (s:=s); specialize IHe2 with (s:=s).

  destruct n. rewrite IHe1. simpl. crush. (* or reflexivity instead of crush *)
  remember (optimize_aexp e2) as e2'; destruct e2'.
  destruct n. rewrite IHe1. rewrite IHe2. simpl. omega.
  destruct n0. rewrite IHe1. rewrite IHe2. simpl. omega.
  destruct n0. rewrite IHe1. rewrite IHe2. simpl. omega.

  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. crush.
  destruct n. rewrite IHe1. rewrite IHe2. simpl. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. crush.
  destruct n. rewrite IHe1. rewrite IHe2. simpl. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. simpl. omega.

  remember (optimize_aexp e2) as e2'; destruct e2'.
  destruct n. rewrite IHe1. rewrite IHe2. simpl. omega.
  destruct n. rewrite IHe1. rewrite IHe2. simpl. omega.

  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. omega.
  
  remember (optimize_aexp e2) as e2'; destruct e2'.
  destruct n. rewrite IHe1. rewrite IHe2. simpl. omega.
  destruct n. rewrite IHe1. rewrite IHe2. simpl. omega.

  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. reflexivity.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. reflexivity.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. reflexivity.

  remember (optimize_aexp e2) as e2'; destruct e2'; specialize IHe1 with (s:=s); specialize IHe2 with (s:=s).

  destruct n;
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. simpl. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. simpl. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. simpl. omega.
  simpl eval_aexp in *. rewrite IHe1. rewrite IHe2. simpl. omega.
Qed.

Lemma my_eq_refl : forall n, NPeano.Nat.eqb n n = true.
Proof.
  induction n; crush.
Qed.

Lemma not_lt_refl : forall n, NPeano.Nat.ltb n n = false.
Proof.
  induction n; crush.
Qed.

Lemma bopt_ok : forall e s, eval_bexp e s = eval_bexp (optimize_bexp e) s.
Proof.
  intros; induction e; crush;
  try ( (* embedded aexps *)
      remember (eq_aexp_dec (optimize_aexp a) (optimize_aexp a0)) as comp; destruct comp; simpl;
      specialize aopt_ok with (e:=a) (s:=s); specialize aopt_ok with (e:=a0) (s:=s); intros;
      rewrite H; rewrite H0;
      try rewrite e in *;
        solve
          [ apply my_eq_refl | apply not_lt_refl | reflexivity ]);
  try ( (* embedded bexps *)
      remember (optimize_bexp e1) as e1'; destruct e1'; remember (optimize_bexp e2) as e2'; destruct e2'; simpl; crush).
  destruct e; simpl; crush.
Qed.

Ltac remember_cond name :=
  match goal with
    | [ |- context[ (If ?c _ _)] ] => remember c as name
    | [ |- context[ (While ?c _) ] ] => remember c as name
  end.
Ltac remember_seq c1name c2name:=
  match goal with
    | [ |- context[ (Seq ?c1 ?c2) ] ] => remember c1 as c1name; remember c2 as c2name
  end.

Theorem opt_ok : forall c s1 s2, eval_com c s1 s2 -> eval_com (optimize_com c) s1 s2.
Proof.
  intros.
  induction H.
  (* Skip *)
  simpl. constructor.
  (* Assign *)
  simpl optimize_com.
  specialize aopt_ok with (e:=e) (s:=s). intros.
  rewrite H.
  apply Eval_assign with (s:=s) (x:=x) (e:=(optimize_aexp e)).
  (* Seq *)
  simpl optimize_com.
  remember (optimize_com c1) as x; destruct x;
  [ inversion IHeval_com1; assumption | .. ]; try (
  remember (optimize_com c2) as y; destruct y;
  [ inversion IHeval_com2; rewrite <- H3; apply IHeval_com1 | .. ];
  remember_seq c1' c2'; apply Eval_seq with (c1:=c1') (s0:=s0) (s1:=s1) (c2:=c2') (s2:=s2);
  solve [ apply IHeval_com1 | apply IHeval_com2]).
  (* If-T *)
  simpl optimize_com.
  remember (optimize_bexp b) as b'; destruct b';
  [  assumption
   | apply eq_sym in Heqb';
     specialize bopt_ok with (e:=b) (s:=s); intros;
     rewrite H in H1;
     assert (eval_bexp (optimize_bexp b) s = false);
     crush | .. ];
  remember_cond bnew; apply Eval_if_true with (b:=bnew) (c1:=(optimize_com c1)) (c2:=(optimize_com c2)) (s:=s) (s':=s');
  specialize bopt_ok with (e:=b) (s:=s); intro H1;
  rewrite H in H1; apply eq_sym in Heqb'; crush;
  assumption; assumption.
  (* If-F *)
  simpl optimize_com.
  remember (optimize_bexp b) as b'; destruct b';
  [  apply eq_sym in Heqb';
     specialize bopt_ok with (e:=b) (s:=s); intros;
     rewrite H in H1;
     assert (eval_bexp (optimize_bexp b) s = true);
     crush
   | assumption | .. ];
  remember_cond bnew; apply Eval_if_false with (b:=bnew) (c1:=(optimize_com c1)) (c2:=(optimize_com c2)) (s:=s) (s':=s');
  specialize bopt_ok with (e:=b) (s:=s); intro H1;
  rewrite H in H1; apply eq_sym in Heqb'; crush;
  assumption; assumption.
  (* While-F *)
  Lemma no_inf_ieval : forall n c s, ieval_com n (While Tt c) s = None /\ ieval_com (S n) (While Tt c) s = None.
  Proof.
    induction n.
    crush.
    intros.
    assert (IHn1:=IHn). assert (IHn2:=IHn).
    specialize IHn1 with (c:=c) (s:=s).
    destruct IHn1. split. assumption.
    simpl ieval_com.
    remember (ieval_com n c s) as x; destruct x.
    specialize IHn2 with (c:=c) (s:=s0).
    destruct IHn2. assumption.
    crush.
  Qed.
  Lemma no_inf_eval : forall c s1 s2, eval_com (While Tt c) s1 s2 -> False.
  Proof.
    intros.
    specialize if_eval_then_fuel with (c:=(While Tt c)) (s1:=s1) (s2:=s2).
    specialize no_inf_ieval with (c:=(While Tt c)) (s:=s1).
    intros.
    destruct H1. assumption.
    specialize if_fuel_then_eval with (n:=x) (c:=(While Tt c)) (s1:=s1) (s2:=s2).
    specialize H0 with (n:=x) (c:=c) (s:=s1).
    destruct H0.
    contradict H1. crush.
  Qed.

  simpl optimize_com.
  remember (optimize_bexp b) as b'; destruct b';
  [ apply eq_sym in Heqb';
    specialize bopt_ok with (e:=b) (s:=s); intros;
    rewrite H in H0;
    assert (eval_bexp (optimize_bexp b) s = true);
    crush;
    apply eq_sym in H0; contradict H1; discriminate
  | apply Eval_skip with (s:=s) | .. ];
  remember_cond b'';
  apply Eval_while_false with (b:=b'') (c:=(optimize_com c)) (s:=s);
  specialize bopt_ok with (e:=b) (s:=s); intro Hopt_eq;
  rewrite H in Hopt_eq; rewrite <- Heqb' in Hopt_eq;
  apply eq_sym in Hopt_eq; assumption.
  (* While-T *)
  simpl optimize_com;
  remember (optimize_bexp b) as b'; destruct b';
  [ | specialize bopt_ok with (e:=b) (s:=s1); intros;
      rewrite <- Heqb' in H2; simpl in H2; contradict H; crush | .. ];
  remember_cond bnew;
  apply Eval_while_true with (b:=bnew) (c:=(optimize_com c)) (s1:=s1) (s2:=s2) (s3:=s3);
  specialize bopt_ok with (e:=b) (s:=s1); intro Hopt_eq;
  rewrite H in Hopt_eq; rewrite <- Heqb' in Hopt_eq;
  apply eq_sym in Hopt_eq; try assumption;
  eapply if_eval_then_fuel in IHeval_com2;
  destruct IHeval_com2;
  assert (exists x1, x = S x1);
  repeat solve
         [  induction x; [ contradict H2; crush | exists x; reflexivity ]
          | destruct H3;
            simpl in H2;
            rewrite <- Heqb' in H2;
            rewrite Heqbnew in H2;
            eapply if_fuel_then_eval with (n:=x);
            rewrite Heqbnew; assumption ].
Qed.

(* Hints:

   * You *will* get stuck doing this assignment.  It is hard.
     Don't hesitate to ask questions on Piazza or in class, 
     or collaborate with friends to solve this.  
     
   * When proving ieval_com is equivalent to eval_com, you will
     find the following lemma very useful:

     ieval_plus : forall n c s1 s2, 
       ieval_com n c s1 = Some s2 -> 
         forall m, ieval_com (n + m) c s1 = Some s2

    This says that if it takes n steps to get an answer out,
    then if you run for more than n steps, you still get the
    same answer out.

   * Write a simple optimizer first, and prove that correct.
     Don't try to write a complicated optimizer first.  It's
     easier to "grow" your development incrementally.  

  * You will find the following tactic very useful:

       remember(<exp>) as <id>

    Consider a proof state like this:

        H : P (foo + bar + baz)
        -----------------------------------------
        match foo + bar + baz with 
          | 0 => blah
          | S n => blahblah
        end

    Executing the tactic

        remember (foo + bar + baz) as x

    will leave you in the state:

        x : nat
        Hxeq : x = foo + bar + baz
        H : P x
        -----------------------------------------
        match x with 
          | 0 => blah
          | S n => blahblah
        end

    So "remember" just helps you name a sub-expression in 
    a proof, and replace all occurrences of that sub-expression
    with that name.  You can always undo the substitution by
    rewriting by the Hxeq equation.

  * There are many useful arithmetic facts in the libraries
    (e.g., plus_0_r, NPeano.Nat.sub_0_r, mult_comm, etc.) 
    Don't forget to use "SearchAbout" to find them.

  * If you [Require Import Omega.] then you can use the "omega"
    tactic to solve some arithmetic questions.  

  * You will want to define a comparison operation for arithmetic
    expressions.  The natural thing to write is something like:

       eq_aexp : aexp -> aexp -> bool

    but you will then need to prove that this is actually correct
    i.e., (eq_aexp a1 a2 = true) <-> (a1 = a2).

    An alternative is to define something like:

      eq_aexp_dec : forall (a1 a2:aexp), {a1 = a2} + {a1<>a2}.

    and instead of trying to build it using explicit code, use
    the "decide quality" tactic (two words.)  For instance:

    Definition eq_aexp_dec (a1 a2:aexp) : {a1=a2} + {a1<>a2}.
      decide quality.
      apply (eq_nat_dec n n0).
      apply (string_dec v v0).
      decide equality.
    Defined.

    This tactic will take an inductive definition and try to
    build the decidable equality term for you.  In the example
    above, I had to tell it how to decide quality for some of
    the types used within the definition (nats, strings, and
    binops.)  

  * You may also find the tactic:

       replace (<exp1>) with (<exp2>) 

    useful.  As suggested, it lets you replace occurrences of 
    one expression with another.  It leaves you with two goals:
    The first is the original goal with the substitution performed.
    The second is a requirement to prove <exp1> = <exp2>. 

  * My solution for this whole file (not including these comments)
    is about 400 lines of code.  Yours will be much, much bigger
    unless you use a lot of automation.  

*)
    

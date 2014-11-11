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

Search "ltb".

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

Fixpoint ieval_com n c s1 : option state :=
  match n with
    | 0 => None
    | S n' =>
      match c with
        | Skip => Some s1
        | Assign x e => Some (set x (eval_aexp e s1) s1)
        | Seq c1 c2 =>
          match ieval_com n' c1 s1 with
            | None => None
            | Some s2 => ieval_com n' c2 s2
          end
        | If b ct cf => ieval_com n' (if eval_bexp b s1 then ct else cf) s1
        | While b ct =>
          if eval_bexp b s1
          then match ieval_com n' ct s1 with
                 | None => None
                 | Some s2 => ieval_com n' (While b ct) s2
               end
          else Some s1
      end
  end.

Lemma ieval_seq : forall n c1 c2 s1 s2,
                         ieval_com (S n) (Seq c1 c2) s1 = Some s2 <->
                         exists si, ieval_com n c1 s1 = Some si /\ ieval_com n c2 si = Some s2.
  intros. split.
  + intros. simpl in H. remember (ieval_com n c1 s1) as si. destruct si.
    exists s. split. reflexivity. assumption.
    discriminate.
  + crush.
Qed.

Lemma ieval_while : forall n b ct s1 s2,
  ieval_com (S n) (While b ct) s1 = Some s2 <->
  (eval_bexp b s1 = false /\ s1 = s2) \/
  (eval_bexp b s1 = true /\
   (exists si, ieval_com n ct s1 = Some si /\ ieval_com n (While b ct) si = Some s2)).
Proof.
  intros. split.
  + intros. remember (eval_bexp b s1) as be. destruct be.
    - right. remember (ieval_com n ct s1) as si. destruct si. split. reflexivity. exists s.
      split. reflexivity. rewrite <- H. simpl. rewrite <- Heqbe. rewrite <- Heqsi. reflexivity.
      split. reflexivity. simpl in H. rewrite <- Heqbe in H. rewrite <- Heqsi in H. discriminate.
    - left. split. reflexivity. simpl in H. rewrite <- Heqbe in H. injection H. auto.
  + crush.
Qed.
                      
                      
Lemma ieval_plus : forall n c s1 s2, 
                     ieval_com n c s1 = Some s2 -> 
                     forall m, ieval_com (n + m) c s1 = Some s2.
Proof.
  intros n. destruct n as [| n'].
  intros c s1 s2 ie. simpl in ie. discriminate.
  induction n'.
  + induction m. auto. rewrite <- plus_n_Sm. rewrite <- IHm. simpl.
    destruct c; crush. remember (eval_bexp b s1) as be. destruct be; crush.
  + intros c s1 s2 H m. destruct c; auto; replace (S (S n') + m) with (S (S n' + m)) by auto. 
    - rewrite ieval_seq in *.
      elim H. clear H. intros si. intros H. exists si. crush.
    - crush.
    - rewrite ieval_while in *.
      elim H. clear H. auto. intros H1. elim H1. intros Hbe H2. elim H2. intros si. intros H3.
      right. split. assumption. exists si. split; elim H3; intros H4 H5; apply IHn'; assumption.
Qed.

Print ieval_plus.

(* Prove that :

   eval_com c s1 s2 -> exists n, ieval_com n c s1 = Some s2.

*)
Theorem eval_ieval : forall c s1 s2,
  eval_com c s1 s2 -> exists n, ieval_com n c s1 = Some s2.
Proof.
  intros c s1 s2 ec. induction ec.
  + exists 1. reflexivity.
  + exists 1. reflexivity.
  + destruct IHec1. destruct IHec2. exists (S x + x0). simpl.
    apply ieval_plus with (m := x0) in H. rewrite H.
    apply ieval_plus with (m := x) in H0. rewrite plus_comm. assumption.
  + destruct IHec. exists (S x). simpl. rewrite H. assumption.
  + destruct IHec. exists (S x). simpl. rewrite H. assumption.
  + exists 1. simpl. rewrite H. reflexivity.
  + destruct IHec1. destruct IHec2. exists (S x + x0). simpl. rewrite H. 
    apply ieval_plus with (m := x0) in H0. rewrite H0.
    apply ieval_plus with (m := x) in H1. rewrite plus_comm. assumption.
Qed.

(* Prove that : 

   ieval_com n c s1 = Some s2 -> eval_com c s1 s2

*)
Theorem ieval_eval : forall n c s1 s2,
  ieval_com n c s1 = Some s2 -> eval_com c s1 s2.
Proof.
  intro n. destruct n. discriminate. induction n; intro c. 
  - destruct c; intros s1 s2 H; simpl in H.
    + injection H. intros Heq. rewrite Heq in *. apply Eval_skip.
    + injection H. intros Heq. rewrite <- Heq. apply Eval_assign.
    + discriminate.
    + discriminate.
    + remember (eval_bexp b s1) as be. destruct be.
      discriminate.
      injection H. intros He. rewrite He. apply Eval_while_false. rewrite <- He. auto.
  - destruct c; intros s1 s2 H.
    + injection H. intros Heq. rewrite Heq in *. apply Eval_skip.
    + injection H. intros Heq. rewrite <- Heq. apply Eval_assign.
    + remember (ieval_com (S n) c1 s1) as ms. destruct ms as [| s].
      apply (Eval_seq _ _ s _ _).
      apply IHn. auto.
      remember (S n) as n1.
      simpl in H.
      rewrite <- Heqms in H. apply IHn. assumption.
      remember (S n) as n1.
      simpl in H. rewrite <- Heqms in H. discriminate.
    + remember (S n) as n1.
      simpl in H. remember (eval_bexp b s1) as be. destruct be.
      (* true *)
        apply Eval_if_true. rewrite Heqbe. reflexivity.
        apply IHn. assumption.
      (* false *)
        apply Eval_if_false. rewrite Heqbe. reflexivity.
        apply IHn. assumption.
    + remember (S n) as n1. simpl in H. remember (eval_bexp b s1) as be. destruct be.
      (* true *)
        remember (ieval_com (S n) c s1) as ms. destruct ms. apply Eval_while_true with (s2 := s).
        auto.
        apply IHn. rewrite Heqn1. auto. 
        rewrite <- Heqn1 in Heqms. rewrite <- Heqms in H. apply IHn. assumption.
        rewrite <- Heqn1 in Heqms. rewrite <- Heqms in H. discriminate.
      (* false *)
        injection H. intros Heqs12. rewrite Heqs12. apply Eval_while_false. rewrite <- Heqs12. auto.
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

Fixpoint optimize_aexp ae : aexp :=
  match ae with 
    | Const c => Const c
    | Var v => Var v
    | Binop a op b =>
      match op, optimize_aexp a, optimize_aexp b with
        | Plus, Const 0, a' => a'
        | Plus, a', Const 0 => a'
        | Minus, a', Const 0 => a'
        | Times, a', Const 1 => a'
        | Times, Const 1, a' => a'
        | Times, _, Const 0 => Const 0
        | Times, Const 0, _ => Const 0
        | _, a', b' => Binop a' op b'
      end
  end.

Theorem optimize_aexp_correct :
  forall ae s, eval_aexp ae s = eval_aexp (optimize_aexp ae) s.
Proof.
  intro ae. induction ae; intro s; try auto.
  destruct b;
  simpl; rewrite IHae1; rewrite IHae2;
  remember (optimize_aexp ae1) as e1;
  remember (optimize_aexp ae2) as e2;
  destruct e1 as [c1 | v1 | a1 o1 b1].
  (* Plus *)
  destruct c1. crush.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2; crush.
  crush.
  crush.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2; crush.
  crush.
  crush.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2; crush.
  crush.
  crush.
  (* Times *)
  destruct c1. simpl.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2.
  crush.
  destruct c2; crush.
  crush.
  crush.
  destruct c1.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2.
  crush.
  destruct c2; crush.
  crush.
  crush.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2.
  crush.
  destruct c2.
  crush.
  crush.
  crush.
  crush.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2.
  crush.
  destruct c2; crush.
  crush.
  crush.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2.
  crush.
  destruct c2; crush.
  crush.
  crush.
  (* Minus *)
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2; crush.
  crush.
  crush.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2; crush.
  crush.
  crush.
  destruct e2 as [c2 | v2 | a2 o2 b2].
  destruct c2; crush.
  crush.
  crush.
Qed.

Definition eq_aexp_dec (a1 a2:aexp) : {a1=a2} + {a1<>a2}.
  decide equality.
  apply (eq_nat_dec n n0).
  apply (string_dec v v0).
  decide equality.
Defined.

Fixpoint optimize_bexp be : bexp :=
  match be with 
    | Tt => Tt
    | Ff => Ff
    | Eq a b =>
      let a' := optimize_aexp a in
      let b' := optimize_aexp b in
      if eq_aexp_dec a' b' then Tt else Eq a' b'
    | Lt a b =>
      let a' := optimize_aexp a in
      let b' := optimize_aexp b in
      if eq_aexp_dec a' b' then Ff else Lt a' b'
    | And a b =>
      match optimize_bexp a, optimize_bexp b with
        | Tt, b' => b'
        | a', Tt => a'
        | Ff, _ => Ff             
        | _, Ff => Ff             
        | a', b' => And a' b'
      end
    | Or a b =>
      match optimize_bexp a, optimize_bexp b with
        | Ff, b' => b'
        | a', Ff => a'
        | Tt, _ => Tt             
        | _, Tt => Tt             
        | a', b' => Or a' b'
      end
    | Not a => Not a
end.

Lemma ltb_refl_false : forall a, NPeano.ltb a a = false.
Proof.
  intro a. assert (~(a < a)). omega.
  rewrite <- NPeano.ltb_lt in H. apply not_true_is_false. assumption.
Qed.

Theorem optimize_bexp_correct :
  forall b s, eval_bexp b s = eval_bexp (optimize_bexp b) s.
Proof.
  intro be. induction be; intro s; try auto.
  (* Eq *)
  simpl.
  replace (eval_aexp a s) with (eval_aexp (optimize_aexp a) s).
  replace (eval_aexp a0 s) with (eval_aexp (optimize_aexp a0) s).
  destruct (eq_aexp_dec (optimize_aexp a) (optimize_aexp a0)).
  rewrite e.
  simpl.
  rewrite <- beq_nat_refl. auto.
  crush.
  rewrite <- optimize_aexp_correct. auto.
  rewrite <- optimize_aexp_correct. auto.
  (* Lt *)
  simpl.
  replace (eval_aexp a s) with (eval_aexp (optimize_aexp a) s).
  replace (eval_aexp a0 s) with (eval_aexp (optimize_aexp a0) s).
  destruct (eq_aexp_dec (optimize_aexp a) (optimize_aexp a0)).
  rewrite e.
  apply ltb_refl_false.
  crush.
  rewrite <- optimize_aexp_correct. auto.
  rewrite <- optimize_aexp_correct. auto.
  (* And *)
  simpl.
  rewrite IHbe1. rewrite IHbe2.
  remember (optimize_bexp be1) as b1. remember (optimize_bexp be2) as b2.
  destruct b1; destruct b2; try auto; try apply andb_true_r; try apply andb_false_r.
  (* Or *)
  simpl.
  rewrite IHbe1. rewrite IHbe2.
  remember (optimize_bexp be1) as b1. remember (optimize_bexp be2) as b2.
  destruct b1; destruct b2; try auto; try apply orb_true_r; try apply orb_false_r.
Qed.

Fixpoint optimize_com c : com :=
  match c with
    | Skip => Skip
    | Assign v a => Assign v (optimize_aexp a)
    | Seq Skip b => optimize_com b                  
    | Seq a Skip => optimize_com a
    | Seq a b => Seq (optimize_com a) (optimize_com b)
    | If b ct cf =>
      match optimize_bexp b with
        | Tt => ct
        | Ff => cf
        | b' => If b' (optimize_com ct) (optimize_com cf)
      end
    | While b c => While (optimize_bexp b) (optimize_com c)
  end.

(* Construct a proof that optimizing a program doesn't change its
   input/output behavior.  That is, show that if we start in state
   s1 and evaluate c to get state s2, then if we evaluate 
   optimize_com(c) in state s1, we get out a state that is
   extensionally equivalent to s2.  
*)  

Lemma ieval_seq_plus :
  forall n1 n2 c1 c2 s0 s1 s2,
    ieval_com (S n1) c1 s0 = Some s1 ->
    ieval_com (S n2) c2 s1 = Some s2 ->
    ieval_com (S n1 + S n2) (Seq c1 c2) s0 = Some s2.
Proof.
  intros.
  simpl.
  replace (n1 + S n2) with (S n1 + n2) by omega.
  rewrite ieval_plus with (s2 := s1).
  replace (S n1 + n2) with (S n2 + n1) by omega.
  rewrite ieval_plus with (s2 := s2).
  reflexivity. assumption. assumption.
Qed.

Theorem optimize_com_correct :
  forall c s1 s2, eval_com c s1 s2 -> eval_com (optimize_com c) s1 s2.
Proof.
  intros c s1 s2 H.
  induction H.
  (* skip *)
  - apply Eval_skip.
  (* assign *)
  - simpl. rewrite optimize_aexp_correct. apply Eval_assign.
  (* seq *)
  - simpl.
    apply eval_ieval in IHeval_com1. apply eval_ieval in IHeval_com2.
    destruct IHeval_com1 as [n1 H1]. destruct IHeval_com2 as [n2 H2].
    apply ieval_eval with (n := (n1 + n2)).
    destruct n1; try discriminate.
    destruct n2; try discriminate.
    destruct c1; try (
      destruct c2; try apply ieval_seq_plus with (s1 := s1); try assumption;
      simpl in H2; injection H2; intros He12; rewrite <- He12;
      apply ieval_plus; assumption).
    simpl in H1. injection H1. intros He01. rewrite He01.
    rewrite plus_comm. apply ieval_plus. assumption.
  (* if true *)
  - rewrite optimize_bexp_correct in H. simpl.
    destruct (optimize_bexp b); try (constructor; assumption).
    assumption. discriminate.
  (* if false *)
  - rewrite optimize_bexp_correct in H. simpl.
    destruct (optimize_bexp b); try (apply Eval_if_false; assumption).
    discriminate. assumption.
  (* while false *)
  - simpl. apply Eval_while_false. rewrite <- optimize_bexp_correct. assumption.
  (* while true *)
  - apply eval_ieval in IHeval_com1. apply eval_ieval in IHeval_com2.
    destruct IHeval_com1 as [n1 He1]. destruct IHeval_com2 as [n2 He2].
    apply ieval_eval with (n := (n1 + n2)).
    destruct n1; try discriminate.
    destruct n2; try discriminate.
    simpl.
    rewrite optimize_bexp_correct in H. rewrite H.
    apply ieval_seq_plus with (s1 := s2); auto.
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
    

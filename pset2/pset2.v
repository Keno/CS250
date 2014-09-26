Add LoadPath "/Users/kfischer/Documents/CS250/cpdtlib".

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

Fixpoint ieval_com (n:nat) (c:com) (s:state) : option state :=
match n with 
| O => None
| S m => match c with
    | Skip => Some s
    | Assign x e => Some (set x (eval_aexp e s) s)
    | Seq c1 c2 => match (ieval_com m c1 s) with
      | Some s' => (ieval_com m c2 s')
      | None => None
    end
    | If b c1 c2 => if (eval_bexp b s) then 
      (ieval_com m c1 s) 
      else (ieval_com m c2 s)
    | While b c1 => if (eval_bexp b s) then
      (ieval_com m (Seq c1 c) s)
      else Some s
    end
end.


(* Prove that :

   eval_com c s1 s2 -> exists n, ieval_com n c s1 = Some s2.

*)

Lemma terminates : forall n c s1 s2, ieval_com n c s1 = Some s2 -> n<>0. crush. Qed.
Lemma neq : forall n, n<>0 <-> exists m, n = S m.
crush. destruct n. crush. exists n. reflexivity. Qed.

Ltac aterm H := let id:=fresh in assert (id := H); apply terminates in id.

Lemma ieval_seq : forall n c1 c2 s1 s2 s3,
       ieval_com n c1 s1 = Some s3 -> ieval_com n c2 s3 = Some s2 -> ieval_com (S n) (Seq c1 c2) s1 = Some s2.
  intros. crush.
Qed.

Lemma ieval_iseq : forall n c1 c2 s1 s2 s3,
       ieval_com (S n) (Seq c1 c2) s1 = Some s3 -> ieval_com n c1 s1 = Some s2 -> ieval_com n c2 s2 = Some s3.
  intros. rewrite <- H. crush.
Qed.

Lemma seq_term : forall n c1 c2 s1 s2, ieval_com (S n) (Seq c1 c2) s1 = Some s2 ->
         exists s', ieval_com n c1 s1 = Some s'.
  crush.
  remember (ieval_com n c1 s1) as x.
  destruct x.
  crush.
  exists s.
  rewrite Heqx. reflexivity.
  contradict H. crush.
Qed.

Hint Resolve ieval_seq.

Check NPeano.Nat.add_succ_r.
Lemma ieval_plus : forall n c s1 s2, 
       ieval_com n c s1 = Some s2 -> 
         forall m, ieval_com (n + m) c s1 = Some s2.
intros.
Lemma ieval_plus' : forall n c s1 s2, 
       ieval_com n c s1 = Some s2 -> ieval_com (n + 1) c s1 = Some s2.
intro n.
induction n.
intros. crush.
intros.
rewrite plus_comm. rewrite NPeano.Nat.add_succ_r. simpl plus.
remember (S n) as m.
unfold ieval_com. fold ieval_com.
destruct c.
crush.
crush.
(* Begin SEQ *)
remember (ieval_com m c1 s1) as x.
destruct x.
assert (IHn2 := IHn); specialize IHn2 with (c:=c2) (s1:=s) (s2:=s2); rewrite plus_comm in IHn2.
rewrite Heqm in *.
apply IHn2; clear IHn2.
apply ieval_iseq with (c1:=c1) (s1:=s1).
rewrite H. reflexivity.
apply seq_term in H.
destruct H.
specialize IHn with (c := c1) (s1:=s1) (s2:=x). rewrite plus_comm in IHn.
crush.
rewrite Heqm in *. apply seq_term in H. destruct H.
specialize IHn with (c := c1) (s1:=s1) (s2:=x). rewrite plus_comm in IHn.
apply IHn in H. contradict H. crush.
(* End SEQ *)

 contradict H.
remember (ieval_com m c1 s1) as y. rewrite <- Heqy.

simpl in Heqx.

assert (H2:=H).
apply IHn in H.
apply
assert (x = s).
 
assert (Some s = ieval_com n c1 s1).
assert (IHn2 := IHn); specialize IHn2 with (c:=c1) (s1:=s1) (s2:=s); rewrite plus_comm in IHn2.
rewrite Heqm.
apply IHn2; clear IHn2.

assert (exists s', ieval_com m c1 s1 = Some s'). apply seq_term with (c2:=c2) (s2:=s2).

specialize IHn with (c:=c1) (s1:=s1) (s2:=s2).
rewrite plus_comm in IHn. rewrite Heqm.
rewrite <- IHn. 

assert (n+1 = S n). rewrite plus_comm; simpl; reflexivity. rewrite H1; clear H1.


aterm H.
Show.
assert (n+1 = S n). rewrite plus_comm; simpl; reflexivity. rewrite H1; clear H1.
apply neq in H0.
destruct H0.
rewrite H0.
rewrite H0 in H; clear H0.
induction x.
destruct c.
crush.
crush.
crush.
simpl in H.
remember (eval_bexp b s1) as x in H.
destruct x; contradict H; crush.
simpl in H.
remember (eval_bexp b s1) as x in H.
destruct x.
contradict H. crush.
crush.
rewrite <- Heqx.
reflexivity.
(* End base case *)
Show.
simpl ieval_com in H at 1.


intro m in H0.
assert ( n = S m); 
remember (n+1) as x. unfold H0.


(* Prove that : 

   ieval_com n c s1 = Some s2 -> eval_com c s1 s2

*)

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

(* Construct a proof that optimizing a program doesn't change its
   input/output behavior.  That is, show that if we start in state
   s1 and evaluate c to get state s2, then if we evaluate 
   optimize_com(c) in state s1, we get out a state that is
   extensionally equivalent to s2.  
*)
    


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
    

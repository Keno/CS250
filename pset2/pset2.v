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

Hint Constructors eval_com.

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

Ltac _aterm H id := assert (id := H); apply terminates in id.
Ltac aterm H := let id:=fresh in _aterm H id.
Ltac aterm2 H := let id:=fresh in _aterm H id; apply neq in id; destruct id; rewrite id in *.

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
remember (eval_bexp b s1) as cond.
rewrite Heqm in *.
destruct cond.
specialize IHn with (c := c1) (s1:=s1) (s2:=s2). rewrite plus_comm in IHn. apply IHn. rewrite <- H. simpl. rewrite <- Heqcond. reflexivity.
specialize IHn with (c := c2) (s1:=s1) (s2:=s2). rewrite plus_comm in IHn. apply IHn. rewrite <- H. simpl. rewrite <- Heqcond. reflexivity.
(* END IF *)
remember (eval_bexp b s1) as cond.
rewrite Heqm in *.
destruct cond.
remember ((Seq c (While b c))) as c2.
specialize IHn with (c := c2) (s1:=s1) (s2:=s2). rewrite plus_comm in IHn. apply IHn.
rewrite <- H. simpl. rewrite <- Heqcond. rewrite <- Heqc2. reflexivity.
rewrite <- H. simpl. rewrite <- Heqcond. reflexivity.
Qed.
induction m.
rewrite plus_comm; simpl; rewrite H; reflexivity.
assert ( n + S m = ((n + m) + 1) ). crush.
rewrite H0.
apply ieval_plus'.
assumption.
Qed.

Ltac destruct_inds IHeval_com1 IHeval_com2 :=
  destruct IHeval_com1 as [x IH1]; destruct IHeval_com2 as [x0 IH2];
  aterm IH1; aterm IH2; assert (x+x0 <> 0) as IS; [ omega | ];
  apply neq in IS; destruct IS as [x1 Hyp].

Tactic Notation "raise" constr(x0) := eapply ieval_plus with (n := _) (m := x0).
Tactic Notation "raise" := raise 1; rewrite plus_comm; simpl plus.
Tactic Notation "raise" constr(x0) "in" constr(H) := eapply ieval_plus with (n := _) (m := x0) in H.
Tactic Notation "raise" "in" constr(H) := raise 1 in H; rewrite plus_comm in H; simpl plus in H.

Ltac unroll_ieval_com := 
  match goal with
    | [ |- ieval_com (S ?X) _ _ = _ ] => let y:=fresh in let Heqy:=fresh in remember X as y eqn:Heqy; simpl ieval_com; rewrite Heqy
    | [ H: context[ieval_com (S ?X) _ _] |- _ ] => let y:=fresh in let Heqy:=fresh in remember X as y eqn:Heqy; simpl ieval_com in H; rewrite Heqy in H
  end.

Lemma EvalCom1 : forall c s1 s2, eval_com c s1 s2 -> exists n, ieval_com n c s1 = Some s2.
    intros.
    induction H; try solve [
    (* Skip, Assign, While false *)
        (exists 1; simpl; try rewrite H; reflexivity) |  
    (* Ifs *)
        destruct IHeval_com; exists (S x); simpl; 
        rewrite H; rewrite H1; reflexivity ];
    (* Common Setup *)
        destruct_inds IHeval_com1 IHeval_com2;
    (* Seq *)
       [( exists (S (S x1)); 
          rewrite <- Hyp; unroll_ieval_com )
    (* While True *)
       | (exists (S (S (S x1))); 
         unroll_ieval_com; rewrite <- Hyp; 
         rewrite H; unroll_ieval_com ) ];
    (* Common cleanup *)
       raise x0 in IH1; raise x in IH2; 
       rewrite <- plus_comm in IH2; 
       rewrite IH1; rewrite IH2; reflexivity.
Qed.


(* Prove that : 

   ieval_com n c s1 = Some s2 -> eval_com c s1 s2

*)

Ltac cond_simpl c := let cond:=fresh in remember c as cond; destruct cond; simpl.

Lemma EvalCom2 : forall n c s1 s2, ieval_com n c s1 = Some s2 -> eval_com c s1 s2.
Lemma EvalCom2' : forall n c s1 s2, ieval_com (S n) c s1 = Some s2 -> eval_com c s1 s2.
  intro n. induction n.
  (* Base Case *)
    intros; destruct c; crush; 
    remember (eval_bexp b s1) as x; destruct x; crush.
  (* Induction *)
    intros.
    destruct c. crush. crush.
  (* Seq *)
    unroll_ieval_com.
    remember (S n) as x in H; simpl ieval_com in H.
    remember (ieval_com x c1 s1) as y.
    destruct y. 
    rewrite Heqx in *.
    assert (IHn2:=IHn).
    specialize IHn with (c:=c2) (s1:=s) (s2:=s2).
    specialize IHn2 with (c:=c1) (s1:=s1) (s2:=s).
    rewrite <- H1 in *; apply IHn in H.
    apply eq_sym in Heqy.
    apply IHn2 in Heqy.
    apply (Eval_seq c1 s1 s c2 s2); assumption.
    contradict H. crush.
  (* If *)
    unroll_ieval_com.
    cond_simpl (eval_bexp b s1); crush.
  (* While *) 
    unroll_ieval_com.
    cond_simpl (eval_bexp b s1).
    unroll_ieval_com.
    rewrite H3 in *; rewrite H1 in *; clear H3; clear H1.
    cond_simpl (ieval_com n c s1).
    apply (Eval_while_true b c s1 s s2).
    apply eq_sym; assumption.
    apply eq_sym in HeqH1; raise in HeqH1; 
      eapply IHn in HeqH1; assumption. 
    raise in H; eapply IHn; assumption.
    contradict H; crush.
    crush.
Qed.
intros; aterm2 H; apply EvalCom2' in H; assumption.
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

(*
This is a better optimizer, but it's hard to proof

Fixpoint optimize_com' (c:com) : option com :=
  match c with
      | Skip => None
      | Seq c1 c2 => match (optimize_com' c1, optimize_com' c2) with
        | (Some c1', Some c2') => Some (Seq c1' c2')
        | (Some c1', None) => Some c1'
        | (None, Some c2') => Some c2'
        | (None, None) => None
      end
      | _ => Some c   
end. 

Definition optimize_com (c:com) : com :=
  match (optimize_com' c) with
      | Some c' => c'
      | None => Skip
  end.
*)

Fixpoint optimize_binop (b: binop) (x: aexp) (y: aexp) : aexp :=
  match b with
    | Times => match (x,y) with
      | (Const 1, Const 1) => Const 1
      | (Const 1, Const 0) => Const 0
      | (Const 0, Const 1) => Const 0
      | (Const 0, Const 0) => Const 0
      | (Const 1, b) => b
      | (a, Const 1) => a
      | (Const 0, b) => Const 0
      | (a, Const 0) => Const 0
      | (a,b) => (Binop a Times b)
    end
    | Plus => match (x,y) with
      | (Const 0, Const 0) => Const 0
      | (a, Const 0) => a
      | (Const 0, b) => b
      | (a,b) => (Binop a Plus b)
    end
    | Minus => match (x,y) with
      | (a, Const 0) => a
      | (a,b) => (Binop a Minus b)
    end
  end.                                       

Lemma binop_opt_correct : forall b x y s, eval_aexp (Binop x b y) s = eval_aexp (optimize_binop b x y) s.
intros.
destruct b.
simpl optimize_binop.
destruct x; try destruct n; destruct y; try destruct n; auto; simpl; try omega.
destruct n0; simpl; omega.
destruct n0; simpl; omega.
simpl optimize_binop.
destruct x; try destruct n; destruct y; try destruct n; auto; simpl; try omega.
destruct n; simpl; omega.
destruct n0; simpl. omega.
destruct n0. simpl. omega.
destruct n0; simpl; omega.
destruct n0; simpl. omega.
destruct n0; simpl. omega.
reflexivity.
destruct n. simpl. omega.
destruct n; simpl; omega.
destruct n; simpl; omega.
simpl optimize_binop.
destruct y. destruct n; simpl; omega.
destruct x; simpl; omega.
reflexivity.
Qed.
 
Fixpoint optimize_aexp (a: aexp) : aexp :=
  match a with
    | Binop x b y => optimize_binop b (optimize_aexp x) (optimize_aexp y)
    | _ => a
  end.

Lemma aexpopt_correct : forall a s, eval_aexp a s = eval_aexp (optimize_aexp a) s.
  intros.
  induction a; crush.
  apply binop_opt_correct.
Qed.

Definition eq_aexp_dec (a1 a2:aexp) : {a1=a2} + {a1<>a2}.
      decide equality.
      apply (eq_nat_dec n n0).
      apply (string_dec v v0).
      decide equality.
    Defined.

Fixpoint optimize_bexp (b: bexp) : bexp :=
  match b with
   | Eq aa ab => match eq_aexp_dec (optimize_aexp aa) (optimize_aexp ab) with
      | left P => Tt
      | right p => Eq aa ab
   end
   | Lt aa ab => match eq_aexp_dec aa ab with
      | left P => Ff
      | right p => Lt aa ab 
   end
   | Not x => match (optimize_bexp x) with
      | Tt => Ff
      | Ff => Tt
      | x => Not x
   end
   | Or x y => match (optimize_bexp x, optimize_bexp y) with
      | (Tt, _) | (_, Tt) => Tt
      | (Ff, a) | (a, Ff) => a
      | (a,b) => Or a b
     end
   | And x y => match (optimize_bexp x, optimize_bexp y) with
      | (Tt, a) | (a, Tt) => a
      | (Ff, _) | (_, Ff) => Ff
      | (a,b) => And a b
     end
    | _ => b
  end.

(* These are probably in the library somewhere but I couldn't find them *)
Lemma eqb_true : forall x, NPeano.Nat.eqb x x = true.
induction x; crush.
Qed.

Lemma ltb_false : forall x, NPeano.Nat.ltb x x = false.
induction x; crush.
Qed.

Lemma bexp_opt_correct : forall b s, eval_bexp b s = eval_bexp (optimize_bexp b) s.
intros.
induction b; crush.
remember (eq_aexp_dec (optimize_aexp a) (optimize_aexp a0)) as cond.
destruct cond.
rewrite aexpopt_correct at 1; rewrite e; rewrite <- aexpopt_correct at 1.
remember (eval_aexp a0 s) as x. apply eqb_true.
simpl. reflexivity.
remember (eq_aexp_dec a a0) as cond.
destruct cond.
rewrite aexpopt_correct at 1; rewrite e; rewrite <- aexpopt_correct at 1.
remember (eval_aexp a0 s) as x. apply ltb_false.
simpl. reflexivity.
remember (optimize_bexp b1) as bb1.
remember (optimize_bexp b2) as bb2.
destruct bb1; solve[ simpl; reflexivity | destruct bb2; simpl; solve [ crush | rewrite andb_true_r; reflexivity | rewrite andb_false_r; reflexivity ] ].
remember (optimize_bexp b1) as bb1.
remember (optimize_bexp b2) as bb2.
destruct bb1; solve[ simpl; reflexivity | destruct bb2; simpl; solve [ crush | rewrite andb_true_r; reflexivity | rewrite andb_false_r; reflexivity ] ].
remember (optimize_bexp b) as bb.
destruct bb; crush.
Qed.

Fixpoint optimize_com (c:com) : com :=
  match c with
      | Seq c1 c2 => match (c1, c2) with
        | (Skip, Skip) => Skip
        | (Skip, c2') => optimize_com c2'
        | (c1', Skip) => optimize_com c1'
        | (c1', c2') => (Seq (optimize_com c1') (optimize_com c2'))
      end
      | Assign v a => Assign v (optimize_aexp a)
      | If bb c1 c2 => match (optimize_bexp bb) with
         | Tt => optimize_com c1
         | Ff => optimize_com c2
         | b => If b (optimize_com c1) (optimize_com c2)
      end
      | _ => c
  end.

Lemma Skips : forall x c1 c2 s1 s2, c1 <> Skip -> c2 <> Skip -> ieval_com (S x) (Seq (optimize_com c1) (optimize_com c2)) s1 = Some s2 -> ieval_com (S x) (optimize_com (Seq c1 c2)) s1 = Some s2.
intros.
Lemma Skips' : forall c1 c2, c1 <> Skip -> c2 <> Skip -> Seq (optimize_com c1) (optimize_com c2) = (optimize_com (Seq c1 c2)).
intros.
unfold optimize_com at 3. fold optimize_com. destruct c1; destruct c2; crush.
Qed.
rewrite Skips' in H1; assumption.
Qed.

Lemma Skip1 : forall x c1 c2 s1 s2, c1 = Skip -> c2 <> Skip -> ieval_com (S (S x)) (Seq (optimize_com c1) (optimize_com c2)) s1 = Some s2 -> ieval_com (S (S x)) (optimize_com (Seq c1 c2)) s1 = Some s2.
intros. 
Lemma Skip1': forall c1 c2, c1 = Skip -> c2 <> Skip -> (optimize_com c2) = (optimize_com (Seq c1 c2)).
unfold optimize_com at 2. fold optimize_com. destruct c1; destruct c2; crush.
Qed.
Show.
rewrite H in H1. remember (S x) as y. simpl in H1.
rewrite Heqy in H1. simpl ieval_com at 1 in H1.
rewrite <- Skip1' with (c1 := c1). rewrite <- Heqy in H1.
raise in H1. assumption.
assumption. assumption.
Qed.

Lemma Skip2 : forall x c1 c2 s1 s2, c1 <> Skip -> c2 = Skip -> ieval_com (S (S x)) (Seq (optimize_com c1) (optimize_com c2)) s1 = Some s2 -> ieval_com (S (S x)) (optimize_com (Seq c1 c2)) s1 = Some s2.
intros. 
Lemma Skip2': forall c1 c2, c1 <> Skip -> c2 = Skip -> (optimize_com c1) = (optimize_com (Seq c1 c2)).
unfold optimize_com at 2. fold optimize_com. destruct c1; destruct c2; crush.
Qed.
Show.
rewrite H0 in H1. remember (S x) as y. simpl in H1. simpl ieval_com at 1 in H1.
rewrite <- Skip2' with (c1 := c1). 
rewrite Heqy in H1. simpl ieval_com at 2 in H1. rewrite <- Heqy in H1. simpl in H1.
remember (ieval_com y (optimize_com c1) s1) as cond.
destruct cond.
rewrite <- H1.
apply eq_sym in Heqcond.
raise in Heqcond; rewrite Heqcond; reflexivity.
contradict H1. crush.
assumption. assumption.
Qed.

Lemma NoSkips : forall x c1 c2 s1 s2, ieval_com (S (S x)) (Seq (optimize_com c1) (optimize_com c2)) s1 = Some s2 -> ieval_com (S (S x)) (optimize_com (Seq c1 c2)) s1 = Some s2.
intros.
destruct c1.
destruct c2; [ crush | | | |]; apply Skip1; crush.
destruct c2; [ crush | | | |]; apply Skips; crush.
destruct c2; [ apply Skip2; crush | | | |]; apply Skips; crush.
destruct c2; [ apply Skip2; crush | | | |]; apply Skips; crush.
destruct c2; [ apply Skip2; crush | | | |]; apply Skips; crush.
Qed.

Lemma opt_seq_comp: forall x c1 c2 s1 s s2, ieval_com x (optimize_com c1) s1 = Some s -> ieval_com x (optimize_com c2) s = Some s2 -> ieval_com (S x) (optimize_com (Seq c1 c2)) s1 = Some s2.
intros.
assert ((ieval_com (S x) (Seq (optimize_com c1) (optimize_com c2)) s1) = Some s2). apply ieval_seq with (s3:=s); assumption.
aterm2 H.
apply NoSkips. assumption.
Qed.

Lemma assign_correct: forall x a v s1 s2, ieval_com (S x) (optimize_com (Assign v a)) s1 = Some s2 <-> ieval_com (S x) (Assign v a) s1 = Some s2.
intros.
simpl ieval_com.
intros.
rewrite <- aexpopt_correct. crush.
Qed.

(* Construct a proof that optimizing a program doesn't change its
   input/output behavior.  That is, show that if we start in state
   s1 and evaluate c to get state s2, then if we evaluate 
   optimize_com(c) in state s1, we get out a state that is
   extensionally equivalent to s2.  
*)
    
Lemma optimize_correct : forall c s1 s2, eval_com c s1 s2 -> eval_com (optimize_com c) s1 s2.
Lemma optimize_correct' : forall x c s1 s2, ieval_com (S x) c s1 = Some s2 -> ieval_com (S x) (optimize_com c) s1 = Some s2. 
intro x. induction x. crush. destruct c; crush.
rewrite <- aexpopt_correct. reflexivity.
remember (eval_bexp b s1) as cc; destruct cc; crush.
(* END Base case *)
intros.
destruct c.
crush.
apply assign_correct. assumption.
aterm2 H.
assert (H2:=H).
apply seq_term in H.
destruct H.
apply ieval_iseq with (c2:=c2) (s2:=x1) (s3:=s2) in H2.
injection H0.
intros.
rewrite H1 in IHx.
assert (IHx2 := IHx).
specialize IHx with (c:=c1) (s1:=s1) (s2:=x1).
specialize IHx2 with (c:=c2) (s1:=x1) (s2:=s2).
apply IHx in H. apply IHx2 in H2.
clear IHx; clear IHx2.
apply opt_seq_comp with (s:=x1); assumption. assumption.
(* END Seq *)
simpl optimize_com.
remember (S x) as y.
simpl ieval_com in H.
remember (eval_bexp b s1) as cond.
destruct cond.
specialize IHx with (c:=c1) (s1:=s1) (s2:=s2).
apply IHx in H.
remember (optimize_bexp b) as cond'.
destruct cond'; [ raise in H; assumption |
contradict Heqcond; rewrite bexp_opt_correct; rewrite <- Heqcond'; simpl; crush | | | | | ];
rewrite Heqcond'; simpl ieval_com; rewrite <- bexp_opt_correct; rewrite <- Heqcond; assumption.
remember (optimize_bexp b) as cond'.
destruct cond'; [ contradict Heqcond; rewrite bexp_opt_correct; rewrite <- Heqcond'; simpl; crush  | specialize IHx with (c:=c2) (s1:=s1) (s2:=s2); apply IHx in H; raise in H; assumption | | | | | ]; rewrite Heqcond'; simpl ieval_com; rewrite <- bexp_opt_correct; rewrite <- Heqcond;
specialize IHx with (c:=c2) (s1:=s1) (s2:=s2); apply IHx in H; assumption.
(* END If *)
crush.
Qed.
Show.
intros.
apply EvalCom1 in H.
destruct H.
apply EvalCom2 with (n:=x).
aterm2 H.
apply optimize_correct'.
assumption.
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
    

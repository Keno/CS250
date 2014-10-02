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

Hint Resolve ieval_seq.

Tactic Notation "unroll_ieval_com" "in" constr(H) := 
  match type of H with 
    | ieval_com (S ?X) _ _ = _ => let y:=fresh in let Heqy:=fresh in remember X as y eqn:Heqy; simpl ieval_com in H; rewrite Heqy in *; clear Heqy
  end.

Ltac unroll_ieval_com := 
  match goal with
    | [ |- ieval_com (S ?X) _ _ = _ ] => let y:=fresh in let Heqy:=fresh in remember X as y eqn:Heqy; simpl ieval_com; rewrite Heqy in *; clear Heqy
    | [ H: context[ieval_com (S ?X) _ _] |- _ ] => unroll_ieval_com in H
  end.

Ltac clean :=
  repeat match goal with
    | [ H: ?m = S ?n |- _ ] => rewrite H in *; clear H
    | [ H: S ?m = ?n |- _ ] => rewrite <- H in *; clear H
end.

Ltac cond_simpl c := let cond:=fresh in remember c as cond; destruct cond; simpl.

Lemma seq_term : forall n c1 c2 s1 s2, ieval_com (S n) (Seq c1 c2) s1 = Some s2 ->
         exists s', ieval_com n c1 s1 = Some s'.
  crush. cond_simpl (ieval_com n c1 s1). crush. exists s. crush. crush.
Qed.

Lemma ieval_plus : forall n c s1 s2, 
       ieval_com n c s1 = Some s2 -> 
         forall m, ieval_com (n + m) c s1 = Some s2.
intros.
Lemma ieval_plus' : forall n c s1 s2, 
       ieval_com n c s1 = Some s2 -> ieval_com (n + 1) c s1 = Some s2.
  intro n; induction n.
  (* Base Case *)
    intros. crush.
  (* Induction *)
    intros; rewrite plus_comm in *; rewrite NPeano.Nat.add_succ_r in *; 
      simpl plus in *.
    unroll_ieval_com.
    remember (S n) as m.
    destruct c. crush. crush.
    (* Begin SEQ *)
      cond_simpl (ieval_com m c1 s1). clean.
      assert (H2 := H). assert (IHn2 := IHn).
      apply seq_term in H.
      destruct H. assert (H3 := H).
      specialize IHn with (c:=c1) (s1:=s1) (s2:=x).
      apply IHn in H. rewrite <- HeqH1 in H.
      injection H; intros; rewrite <- H1 in *; clear H1; clear H.
      apply ieval_iseq with (c2:=c2) (s3:=s2) (s2:=s) in H2.
      specialize IHn2 with (c:=c2) (s1:=s) (s2:=s2); apply IHn2 in H2;
         assumption.
      assumption.
      clean; apply seq_term in H; destruct H.
      specialize IHn with (c:=c1) (s1:=s1) (s2:=x); apply IHn in H.
      contradict HeqH1. crush.
    (* End SEQ *)
      cond_simpl (eval_bexp b s1); clean; apply IHn with (s2:=s2); 
        rewrite <- H; simpl; rewrite <- HeqH1; reflexivity.
    (* End IF *)
      cond_simpl (eval_bexp b s1); clean.
      remember ((Seq c (While b c))) as c2. apply IHn. rewrite <- H.
      simpl. rewrite <- HeqH1. rewrite <- Heqc2. reflexivity.
      rewrite <- H. simpl. rewrite <- HeqH1. reflexivity.
  Qed.
  induction m.
  rewrite plus_comm; simpl; rewrite H; reflexivity.
  assert ( n + S m = ((n + m) + 1) ). crush.
  rewrite H0; apply ieval_plus'; assumption.
Qed.

Ltac destruct_inds IHeval_com1 IHeval_com2 :=
  destruct IHeval_com1 as [x IH1]; destruct IHeval_com2 as [x0 IH2];
  aterm IH1; aterm IH2; assert (x+x0 <> 0) as IS; [ omega | ];
  apply neq in IS; destruct IS as [x1 Hyp].

Tactic Notation "raise" constr(x0) := eapply ieval_plus with (n := _) (m := x0).
Tactic Notation "raise" := raise 1; rewrite plus_comm; simpl plus.
Tactic Notation "raise" constr(x0) "in" constr(H) := eapply ieval_plus with (n := _) (m := x0) in H.
Tactic Notation "raise" "in" constr(H) := raise 1 in H; rewrite plus_comm in H; simpl plus in H.

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
    unroll_ieval_com in H.
    remember (S n) as x in H; simpl ieval_com in H.
    remember (ieval_com x c1 s1) as y.
    destruct y. 
    rewrite Heqx in *.
    assert (IHn2:=IHn).
    specialize IHn with (c:=c2) (s1:=s) (s2:=s2).
    specialize IHn2 with (c:=c1) (s1:=s1) (s2:=s).
    apply IHn in H.
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
    cond_simpl (ieval_com n c s1).
    apply (Eval_while_true b c s1 s s2).
    apply eq_sym; assumption.
    apply eq_sym in HeqH2; raise in HeqH2; 
      eapply IHn in HeqH2; assumption. 
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

Fixpoint optimize_binop (b: binop) (x: aexp) (y: aexp) : aexp :=
  match b with
    | Times => match (x,y) with
      | (a, Const 1) | (Const 1, a) => a
      | (Const 0, _) | (_, Const 0) => Const 0
      | (a,b) => (Binop a Times b)
    end
    | Plus => match (x,y) with
      | (a, Const 0) | (Const 0, a) => a
      | (a,b) => (Binop a Plus b)
    end
    | Minus => match (x,y) with
      | (a, Const 0) => a
      | (a,b) => (Binop a Minus b)
    end
  end.                           

Ltac Hammer n := try (destruct n; simpl; try omega).

Lemma binop_opt_correct : forall b x y s, eval_aexp (Binop x b y) s = eval_aexp (optimize_binop b x y) s.
  intros.
  destruct b; simpl optimize_binop; destruct x;
  Hammer n; Hammer n0; destruct y;
  Hammer n; Hammer n; Hammer n0; Hammer n0;
  simpl; try omega.
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
   | Eq aa ab => let (aa', bb') := ((optimize_aexp aa),(optimize_aexp ab)) in
     match eq_aexp_dec aa' bb'  with
        | left P => Tt
        | right p => Eq aa' bb'
     end
   | Lt aa ab => let (aa', bb') := ((optimize_aexp aa),(optimize_aexp ab)) in
     match eq_aexp_dec aa' bb' with
      | left P => Ff
      | right p => Lt aa' bb' 
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
intros. induction b; crush;
try (remember (eq_aexp_dec (optimize_aexp a) (optimize_aexp a0)) as cond;
destruct cond; [ simpl;
rewrite aexpopt_correct at 1; rewrite e; rewrite <- aexpopt_correct at 1; try rewrite eqb_true; try rewrite ltb_false; reflexivity |
simpl; repeat rewrite <- aexpopt_correct; reflexivity ]); [ .. | remember (optimize_bexp b) as bb; destruct bb; crush ];
remember (optimize_bexp b1) as bb1; remember (optimize_bexp b2) as bb2;
destruct bb1; solve[ simpl; reflexivity | destruct bb2; simpl; 
       solve [ crush | rewrite andb_true_r; reflexivity | rewrite andb_false_r; reflexivity ] ].
Qed.

Fixpoint optimize_com (c:com) : com :=
  match c with
      | Seq c1 c2 => match (optimize_com c1, optimize_com c2) with
        | (Skip, Skip) => Skip
        | (Skip, c2') => c2'
        | (c1', Skip) => c1'
        | (c1', c2') => (Seq c1' c2')
      end
      | Assign v a => Assign v (optimize_aexp a)
      | If bb c1 c2 => match (optimize_bexp bb) with
         | Tt => optimize_com c1
         | Ff => optimize_com c2
         | b => If b (optimize_com c1) (optimize_com c2)
      end
      | While bb c1 => match (optimize_bexp bb) with
         | Ff => Skip
         | b => While b (optimize_com c1)
      end
      | Skip => Skip
  end.

(* Construct a proof that optimizing a program doesn't change its
   input/output behavior.  That is, show that if we start in state
   s1 and evaluate c to get state s2, then if we evaluate 
   optimize_com(c) in state s1, we get out a state that is
   extensionally equivalent to s2.  
*)
    
Ltac to_ieval H := apply EvalCom1 in H; destruct H; aterm2 H; simpl in H.
Ltac to_ieval_assign H := simpl ieval_com in H; rewrite <- aexpopt_correct in H.

Lemma eval_assign_correct : forall v a s' s1, eval_com (Assign v (optimize_aexp a)) s1 s' <-> eval_com (Assign v a) s1 s'.
intros.
split; intros; apply EvalCom2 with (n:=1); simpl; apply EvalCom1 in H; destruct H; aterm2 H; simpl in H.
rewrite <- aexpopt_correct in H; assumption.
rewrite aexpopt_correct in H; assumption.
Qed.

Ltac myinj H := let Hx := fresh in injection H as Hx; rewrite Hx in *; clear Hx; clear H.

Ltac magic :=
  repeat match goal with
      | [ H: context[eval_com (optimize_com Skip) _ _] |- _ ] =>  to_ieval H; (try myinj); try assumption
      | [ H: context[eval_com Skip _ _] |- _ ] =>  to_ieval H; (try myinj); try assumption
      | [ H: context[eval_com (Assign _ (optimize_aexp _)) _ _] |- _ ] => apply -> eval_assign_correct in H; try assumption                                         | [ |- eval_com (Assign _ (optimize_aexp _)) _ _ ] => apply eval_assign_correct; try assumption 
      | [ H: context[eval_com (optimize_com (Assign _ _)) _ _ ] |- _] => simpl optimize_com in H; try assumption
      | [ H: eval_com (optimize_com (Seq ?c2 ?c3)) _ _ |- _ ] => remember (optimize_com (Seq c2 c3))
      | [ H: eval_com (optimize_com (If ?b ?c2 ?c3)) _ _ |- _ ] => remember (optimize_com (If b c2 c3))
      | [ H: eval_com (optimize_com (While ?b ?c2)) _ _ |- _ ] => remember (optimize_com (While b c2))                                                       
      | [ H1: eval_com _ ?sx ?s3, H2: eval_com _ ?s3 ?s2 |- eval_com (Seq _ _) ?sx ?s2 ] => apply Eval_seq with (s1:=s3); magic; try assumption
      | [ H: Some ?s1 = Some ?s2 |- _ ] => let Hx := fresh in injection H as Hx; rewrite Hx in *; clear Hx; clear H
      | [ |- eval_com Skip ?s ?s ] => apply Eval_skip; assumption
  end.

Ltac imagic :=
  repeat match goal with
      | [ H: ieval_com ?x ?c ?s1 = ?s2 |- ieval_com (S ?x) ?c ?s1 = ?s2 ] => raise in H; try assumption
      | [ H: ieval_com ?x ?c ?s1 = ?s2, H2: ieval_com (S ?x) ?c ?s1 = ?s3 |- _ ] => 
          let H3:=fresh in assert(H3:=H); raise in H3; rewrite H3 in H2; myinj H2; subst; try assumption; try reflexivity
      | [ H: ?x = ieval_com _ _ _ |- _ ] => apply eq_sym in H
  end.

Lemma seq_correct : forall c1 c2 s1 s' s2, eval_com (optimize_com c1) s1 s' -> eval_com (optimize_com c2) s' s2 -> eval_com (optimize_com (Seq c1 c2)) s1 s2.
intros.
simpl optimize_com.
destruct c1; destruct c2; magic; simpl; magic; destruct c; try destruct c0; magic; simpl; try assumption.
Qed.

Ltac remember_cond name := 
  match goal with
      | [ |- context[ (If ?c _ _ )] ] => remember c as name
      | [ |- context[ (While ?c _ )] ] => remember c as name
  end.

Ltac ifc H Heqcond := contradict H; rewrite bexp_opt_correct; rewrite <- Heqcond; simpl; crush.
Ltac ifb H Heqcond s1 := let cond4:=fresh in  remember_cond cond4; unroll_ieval_com; remember (eval_bexp cond4 s1) as cond5 eqn:Heqcond5; destruct cond5; first [ 
assumption |
contradict H; rewrite bexp_opt_correct; rewrite <- Heqcond; rewrite <- Heqcond5; crush; try assumption ].

Lemma if_correct : forall b c1 c2 s1 s2, 
                     eval_bexp b s1 = false \/ eval_com (optimize_com c1) s1 s2 -> 
                     eval_bexp b s1 = true \/ eval_com (optimize_com c2) s1 s2 -> eval_com (optimize_com (If b c1 c2)) s1 s2.
intros.
destruct H; destruct H0; 
[ contradict H; crush | .. ]; 
try (apply EvalCom1 in H0; destruct H0);
try (apply EvalCom1 in H; destruct H);
try (apply EvalCom2 with (n:= x+x0));
try (apply EvalCom2 with (n:= S x)); simpl optimize_com; remember (optimize_bexp b) as cond.
destruct cond; [ ifc H Heqcond | imagic | .. ]; ifb H Heqcond s1.
destruct cond; [ imagic | ifc H0 Heqcond | .. ] ; ifb H0 Heqcond s1.
destruct cond; [ 
raise x in H; rewrite plus_comm in H; assumption |
raise x0 in H0; assumption | .. ];
(assert (x+x0 <> 0); [ aterm2 H0; crush | ]); apply neq in H1; destruct H1; rewrite H1;
remember_cond cond4; unroll_ieval_com; remember (eval_bexp cond4 s1) as cond5 eqn:Heqcond5; (destruct cond5;
[raise (x-1) in H; assert (x1 = (x0 + (x - 1))) as H3; [ aterm2 H0; crush | ]; rewrite H3; assumption |
raise (x0-1) in H0; assert (x1 = (x + (x0 - 1))) as H3; [ aterm2 H; crush | ]; rewrite H3; assumption ] ).
Qed.

Lemma bexp_true_is_true : forall b, optimize_bexp b = Tt -> (forall s, (eval_bexp b s) = true).
intros. rewrite bexp_opt_correct. rewrite H. simpl. reflexivity.
Qed.

Lemma ieval_minus : forall x c s, ieval_com (S x) c s = None -> ieval_com x c s = None.
intros.
specialize ieval_plus with (n:=x) (m:=1) (c:=c) (s1:=s). intros.
destruct (ieval_com x c s).
assert(Some s0 = Some s0). reflexivity. eapply H0 with (m:=1) in H1.
rewrite plus_comm in H1. simpl plus in H1. congruence. reflexivity.
Qed.

Lemma while_inf : forall x b c s1, (forall s, eval_bexp b s = true) -> ieval_com x (While b c) s1 = None.
induction x; intros; [ crush | ..].
apply ieval_minus. unroll_ieval_com. erewrite H. unroll_ieval_com.
remember (ieval_com x c s1) as cond. destruct cond.
eapply IHx. assumption.
reflexivity.
Qed.

Theorem opt_correct : forall c s1 s2, eval_com c s1 s2 -> eval_com (optimize_com c) s1 s2.
intros.
induction H.
crush.
apply EvalCom2 with (n:=1); simpl. rewrite <- aexpopt_correct. reflexivity.
apply seq_correct with (s':=s1); assumption.
apply if_correct. right. assumption. left. assumption.
apply if_correct. left. assumption. right. assumption.
simpl. apply EvalCom2 with (n:=1). simpl. 
remember (optimize_bexp b) as cond.
destruct cond; try reflexivity; rewrite bexp_opt_correct in H; rewrite <- Heqcond in H; rewrite H; reflexivity.
simpl.
remember (optimize_bexp b) as cond.
destruct cond;
apply EvalCom1 in H1; destruct H1; [
apply eq_sym in Heqcond;
pose proof bexp_true_is_true; specialize H2 with (b:=b); apply while_inf with (x:=x) (c:=c) (s1:=s2) in H2; 
[rewrite H2 in H1; contradict H1; crush | assumption ] |
contradict H; rewrite -> bexp_opt_correct; rewrite <- Heqcond; simpl; crush | .. ];
apply EvalCom1 in IHeval_com2; destruct IHeval_com2;
apply EvalCom1 in IHeval_com1; destruct IHeval_com1;
apply EvalCom2 with (n:=(S (S (x0+x1))));
remember_cond ccc; unroll_ieval_com;
rewrite Heqcond; rewrite <- bexp_opt_correct; rewrite H;
simpl ieval_com; raise x0 in H3; rewrite plus_comm in H3; rewrite H3;
raise x1 in H2; simpl optimize_com in H2; rewrite <- Heqcond in H2; rewrite Heqccc in H2;
rewrite <- Heqcond; rewrite Heqccc; assumption.
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
    

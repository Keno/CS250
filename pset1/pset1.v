(* For the first part of this assignment, I'd like you to construct
   proof terms manually, as we did at the beginning of class, instead
   of using tactics.  

   For each Definition provided, please replace the "." with
   ":= <exp>." for some expression of the appropriate type.
*)

Module PSET1_EX1.

  Definition X1 {A B C D:Prop} : 
    (B /\ (B -> C /\ D)) -> D :=
      fun H1 => match H1 with
        | conj H2 H3 => match (H3 H2) with
          | conj H4 H5 => H5
        end
      end.

  Definition X2 {A B C:Prop} : 
   ~(A \/ B) -> B -> C :=
    fun H1 H2 => match (H1 (or_intror H2)) with
    end.

  Definition X3 {A B C:Prop} : 
    A /\ (B \/ C) -> (A /\ B) \/ (A /\ C) :=
      fun H1 =>
        match H1 with
          | conj H2 H3 => match H3 with
            | or_intror H4 => or_intror (conj H2 H4)
            | or_introl H4 => or_introl (conj H2 H4)
          end
        end.

  Locate "_ <-> _".

  (* To solve the following, you'll need to figure out what
     the definition of "<->" is and how to work with it... *)
  Definition X4 {A:Prop} : 
    A <-> A :=
      (conj (fun H1 => H1) (fun H1 => H1)).

  Definition swap {A B:Prop} (H1: A <-> B) : (B <-> A) :=
    match H1 with
      | conj H2 H3 => conj H3 H2
    end.

  Definition X5 {A B:Prop} : 
    (A <-> B) <-> (B <-> A) :=
      (conj swap swap).

  Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

  Definition X6 {A B C:Prop} : 
    (A <-> B) -> (B <-> C) -> (A <-> C) :=
      fun (H1: A <-> B) (H2: B <-> C) =>
        match H1, H2 with
          | conj H3 H4, conj H5 H6 => (conj (compose H5 H3) (compose H4 H6))
        end.



  (* Thought exercise:  *)

  (* This is not provable in Coq without adding an axiom, even
     though in classical logic, we take this for granted:

     P \/ ~P

     Try to prove it and see what goes wrong...  Interestingly,
     this will almost never bite us.  
  *)
End PSET1_EX1.

(* Now re-do these using only the following tactics:

   intros, apply, destruct, unfold, split, contradiction, left, right

   Hopefully I haven't left off any that you may need.  In general,
   I don't want you using something such as firstorder or tauto
   that trivially solves the goal.  I want you to perform the basic
   steps.  
*)
Module PSET1_EX2.

  Lemma X1 {A B C D:Prop} : 
    (B /\ (B -> C /\ D)) -> D.
  Proof.
    intros.
    destruct H.
    apply H0.
    apply H.
  Qed.

  Lemma X2 {A B C:Prop} : 
    ~(A \/ B) -> B -> C.
  Proof.
    intros.
    destruct H.
    right.
    apply H0.
  Qed.

  Lemma X3 {A B C:Prop} : 
    A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
  Proof.
    intros.
    destruct H.
    destruct H0.
    left.
    split.
    apply H.
    apply H0.
    right.
    split.
    apply H.
    apply H0.
  Qed.

  Lemma X4 {A:Prop} : 
    A <-> A. 
  Proof.
    split.
    intros.
    apply H.
    intros.
    apply H.
  Qed.

  Lemma X5 {A B:Prop} : 
    (A <-> B) <-> (B <-> A).
  Proof.
    split.
    intros.
    split.
    intros.
    apply H.
    apply H0.
    apply H.
    intros.
    split.
    apply H.
    apply H.
  Qed.

  Lemma X6 {A B C:Prop} : 
    (A <-> B) -> (B <-> C) -> (A <-> C).
  Proof.
    intros.
    split.
    intros.
    apply H0.
    apply H.
    apply H1.
    intros.
    apply H.
    apply H0.
    apply H1.
  Qed.

End PSET1_EX2.

(* Here, we're going to exercise the [simpl], [induction] and [rewrite] tactics.
   Replace the [Admitted.]'s with an appropriate proof.
   Don't forget to write "Qed." to terminate your proofs.  It goes
   without saying that you shouldn't just prove these by using a
   library lemma :-)  However, if you get stuck proving one of these, then
   it is sometimes useful to look for one that does solve this, using
   the top-level [SearchAbout] command, and then [Print] the corresponding
   proof.
*)
Module PSET1_EX3.
  Require Import List.
  Require Import Arith.

  Lemma zero_plus_x : forall n, 0 + n = n.
  Proof.
    simpl.
    intros.
    apply eq_refl.
  Qed.

  Lemma x_plus_zero : forall n, n + 0 = n.
  Proof.
    intros.
    auto.
  Qed.

  Lemma map_map : forall {A B C:Type} (f:A->B) (g:B -> C) (xs:list A), 
    map g (map f xs) = map (fun x => g (f x)) xs.
  Proof.
    intros.
    induction xs.
    reflexivity.
    simpl.
    rewrite -> IHxs.
    reflexivity.
  Qed.

  Lemma app_assoc : forall {A:Type} (xs ys zs:list A), 
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
  Proof.
    intros.
    induction xs.
    simpl.
    reflexivity.
    simpl.
    rewrite <- IHxs.
    reflexivity.
  Qed.

  Lemma map_is_fold : forall {A B} (f:A->B) (xs:list A),
    map f xs = fold_right (fun x y => (f x)::y) nil xs.
  Proof.
    intros.
    induction xs.
    simpl.
    reflexivity.
    simpl.
    rewrite <- IHxs.
    reflexivity.
  Qed.

  Definition list_sum (xs:list nat) : nat := fold_right plus 0 xs.

  Print plus.

  Lemma my_plus_assoc : forall (a b c: nat), a + (b + c) = (a + b) + c.
  Proof.
    intros.
    unfold plus.
    induction a.
    simpl.
    reflexivity.
    rewrite IHa.
    reflexivity.
  Qed.


  Lemma list_sum_app : forall (t1 t2: list nat), 
     list_sum (t1 ++ t2) = list_sum t1 + list_sum t2.
  Proof.
    intros.
    induction t1.
    simpl.
    reflexivity.
    simpl.
    rewrite IHt1.
    rewrite my_plus_assoc.
    reflexivity.
  Qed.

  Inductive tree(A:Type) : Type := 
    | Leaf : tree A
    | Node : tree A -> A -> tree A -> tree A.
  Implicit Arguments Leaf [A].
  Implicit Arguments Node [A].

  Fixpoint mirror{A:Type} (t:tree A) : tree A := 
    match t with
      | Leaf => Leaf
      | Node lft v rgt => Node (mirror rgt) v (mirror lft)
    end.

  Lemma mirror_mirror : forall A (t:tree A), mirror (mirror t) = t.
  Proof.
    intros.
    induction t.
    simpl.
    reflexivity. 
    simpl.
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity. 
  Qed.

  Fixpoint flatten {A:Type} (t:tree A) : list A := 
    match t with 
      | Leaf => nil
      | Node lft v rgt => (flatten lft) ++ v::(flatten rgt)
    end.

  Fixpoint tree_sum (t:tree nat) : nat := 
    match t with 
      | Leaf => 0
      | Node lft v rgt => (tree_sum lft) + v + (tree_sum rgt)
    end.

  Lemma tree_flatten_sum : forall t, tree_sum t = list_sum (flatten t).
  Proof.
    intros.
    induction t.
    simpl.
    reflexivity. 
    simpl.
    rewrite list_sum_app.
    rewrite <- IHt1.
    simpl.
    rewrite <- IHt2.
    rewrite my_plus_assoc.
    reflexivity.
  Qed.

End PSET1_EX3.

(* For the first part of this assignment, I'd like you to construct
   proof terms manually, as we did at the beginning of class, instead
   of using tactics.  

   For each Definition provided, please replace the "." with
   ":= <exp>." for some expression of the appropriate type.
*)

Module PSET1_EX1.

  Definition X1 {A B C D:Prop} : 
    (B /\ (B -> C /\ D)) -> D.

  Definition X2 {A B C:Prop} : 
    ~(A \/ B) -> B -> C.

  Definition X3 {A B C:Prop} : 
    A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).

  (* To solve the following, you'll need to figure out what
     the definition of "<->" is and how to work with it... *)
  Definition X4 {A:Prop} : 
    A <-> A. 

  Definition X5 {A B:Prop} : 
    (A <-> B) <-> (B <-> A).

  Definition X6 {A B C:Prop} : 
    (A <-> B) -> (B <-> C) -> (A <-> C).

  (* Thought exercise:  *)

  (* This is not provable in Coq without adding an axiom, even
     though in classical logic, we take this for granted:

     P \/ ~P

     Try to prove it and see what goes wrong...  Interestingly,
     this will almost never bite us.  
  *)

  Abort All.  (* delete this after finishing X1-X6 *)
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
    tauto.
  Qed.

  Lemma X2 {A B C:Prop} : 
    ~(A \/ B) -> B -> C.
  Proof.
    tauto.
  Qed.

  Lemma X3 {A B C:Prop} : 
    A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
  Proof.
    tauto.
  Qed.

  Lemma X4 {A:Prop} : 
    A <-> A. 
  Proof.
    tauto.
  Qed.

  Lemma X5 {A B:Prop} : 
    (A <-> B) <-> (B <-> A).
  Proof.
    tauto.
  Qed.

  Lemma X6 {A B C:Prop} : 
    (A <-> B) -> (B <-> C) -> (A <-> C).
  Proof.
    tauto.
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

  Lemma zero_plus_x : forall n, 0 + n = n.
  Proof.
    Admitted.

  Lemma x_plus_zero : forall n, n + 0 = n.
  Proof.
    Admitted.

  Lemma map_map : forall {A B C:Type} (f:A->B) (g:B -> C) (xs:list A), 
    map g (map f xs) = map (fun x => g (f x)) xs.
  Proof.
    Admitted.

  Lemma app_assoc : forall {A:Type} (xs ys zs:list A), 
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
  Proof.
    Admitted.

  Lemma map_is_fold : forall {A B} (f:A->B) (xs:list A),
    map f xs = fold_right (fun x y => (f x)::y) nil xs.
  Proof.
    Admitted.

  Definition list_sum (xs:list nat) : nat := fold_right plus 0 xs.

  Lemma list_sum_app : forall (t1 t2: list nat), 
     list_sum (t1 ++ t2) = list_sum t1 + list_sum t2.
  Proof.
    Admitted.

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
    Admitted.

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
    Admitted.
  
End PSET1_EX3.
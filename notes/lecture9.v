(* Author: David Darais
   Class: CS 250 Harvard University
   Lecture Date: Oct 16 2014
*)

Require Import List CpdtTactics.
Import ListNotations.

Definition nat_lte := Compare_dec.le_gt_dec.

(* Concepts:
 * 1. Two types of reasoning that I don't have good names for:
 *     - Direct or consequential reasoning:
 *         + Definition: A = B
 *         + Implication: A -> B
 *     VS
 *     - Inverted reasoning, through case analysis or pidgeon-hole:
 *         + S x = O -> False
 *         + length xs = O -> xs = []
 * 2. Predicates as functions vs inductive relations
 *     - length as a function (lengthf : list nat -> nat)
 *     VS
 *     - length as a relation (lengthp : list nat -> nat -> Prop)
 * 3. Intrinsic vs extrinsic verification 
 *     - (merge : list nat -> list nat -> list nat)
 *       and verify it after-the-fact:
 *       (merge_correct : forall xs ys, sorted xs -> sorted ys -> sorted (merge xs ys))
 *     VS
 *     - a sorted_list datatype that is only inhabited by sorted lists:
 *       (slist : nat -> nat -> nat -> Type).
 *       (xs : slist l m n) means xs has length l and is sorted with values between m and n.
 *       merge now has type 
 *       (merge : forall l1 l2 xsm m2 n1 n2, 
 *          slist l1 m1 n1 -> slist l2 m -> slist (l1 + l2) (min m1 m2) (max n1 n2)).
 *       The proof of correctness is built alongside the algorithm.
 *       This approach works well when the property follows the structure of the datatype.
 *
 * 'sorted' from hw3 is a predicate as a function, and the
 * whole pset is about extrinsic verification.
 *)

(* length as a function *)
Fixpoint len (xs : list nat) : nat :=
  match xs with
  | [] => O
  | x :: xs' => S (len xs')
  end. 

(* writing length in proof mode *)
Fixpoint len2 (xs : list nat) : nat.
destruct xs as [|x xs'].
- exact O.
- exact (S (len2 xs')).
Show Proof.
Defined.

Eval compute in len2 [3; 4; 5; 6].


(* A proof which requires direct reasoning. *)
Goal forall x xs, len (x :: xs) = S (len xs).
  intros.
  exact eq_refl.
Defined.

(* A proof which requires inverted reasoning. *)
Goal forall xs, len xs = 0 -> xs = [].
Proof.
  intros.
  destruct xs.
  - exact eq_refl.
  - simpl in H.
    inversion H.
Qed.

(* length as a predicate *)
Inductive lenp : list nat -> nat -> Prop :=
  | Zero : lenp [] O
  | Cons : forall x xs n, lenp xs n -> lenp (x::xs) (S n).

(* this proof is now more work *)
Goal forall x xs n, lenp xs n -> lenp (x :: xs) (S n).
  intros.
  apply Cons.
  exact H.
Qed.

(* this proof is now less work *)
Goal forall xs, lenp xs 0 -> xs = [].
  intros.
  inversion H.
  apply eq_refl.
Qed.

(* An aside about both definitions of length. *)
Section lenp.
  Variable lenp : list nat -> nat -> Prop.
  Variable len : list nat -> nat.
  
  (* the two statements relating lenp and len are only equivalent if
     we know lenp is deterministic *)
  Variable deterministic : forall xs m n, lenp xs m -> lenp xs n -> m = n.

  (* Two statements relating len and lenp.  Are they equivalent? *)
  Definition lenp_correct1 : Type := forall xs n, lenp xs n <-> len xs = n.
  Definition lenp_correct2 : Type := forall xs, lenp xs (len xs).

  Goal lenp_correct1 -> lenp_correct2.
    intros.
    unfold lenp_correct1,lenp_correct2 in *.
    intros xs.
    apply X.
    reflexivity.
  Qed.
  
  Goal lenp_correct2 -> lenp_correct1.
    intros.
    unfold lenp_correct1,lenp_correct2 in *.
    intros xs n.
    split ; intros.
    - specialize (X xs).
      specialize (deterministic xs (len xs) n X H).
      auto.
    - subst.
      apply X.
  Qed.
End lenp.

(* A first try at defining merge that does direct induction on n, and
carries around a proof relating n to the lengths of the lists. *)
Fixpoint merge_dnw (xs ys : list nat) (n : nat) (p : n = length xs + length ys) {struct n} : list nat.
refine(
  match n with
  | O => []
  | S n' =>
    match xs, ys with
    | [], ys => ys
    | xs, [] => xs
    | x :: xs', y :: ys' => 
        match nat_lte x y with
        | left _ => x :: merge_dnw xs' (y :: ys') n' _
        | right _ => y :: merge_dnw (x :: xs') ys' n' _
        end
    end
  end
).
(* We are stuck in proving the first proof hole.  We know nothing about n', only something about n *)
Abort.

(* If we move the proof term to the right and introduce it inside the
bodies of the match statement, we get a refined type for the proof term. *)
Fixpoint merge (xs ys : list nat) (n : nat) {struct n} : n = length xs + length ys -> list nat.
refine(
  match n with
  | O => fun _ => []
  | S n' =>
    match xs, ys with
    | [], ys' => fun (p : S n' = length [] + length ys') => ys'
    | xs', [] => fun (p : S n' = length xs' + length []) => xs'
    | x :: xs', y :: ys' => fun (p : S n' = length (x::xs') + length (y::ys')) =>
        match nat_lte x y with
        | left _ => x :: merge xs' (y :: ys') n' _
        | right _ => y :: merge (x :: xs') ys' n' _
        end
    end
  end
).
(* notice the refined types of p in the bodies of the match. *)
- clear -p.
  simpl in *.
  injection p ; intros.
  auto.
- clear -p.
  simpl in *.
  injection p ; intros.
  rewrite plus_n_Sm.
  auto.
Defined.
Print merge.

(* To prove this correct, we would need to prove (forall xs ys, sorted
xs -> sorted ys -> sorted (merge xs ys).

Let's not try this, but try the intrinsic verification approach
instead and see what it looks like.  First we need to define a sorted
list datatype. *)

Inductive slist : nat -> nat -> nat -> Type :=
  | snil : forall {m n} (pf : m <= n), slist O m n
  | scons : 
      forall m {l xsm xsn} x (pf1 : m <= x) (pf2 : x <= xsm) (xs : slist l xsm xsn), 
      slist (S l) m xsn.

Definition scons' x {l xsm xsn} pf2 xs : slist (S l) x xsn :=
    @scons x l xsm xsn x (le_n x) pf2 xs.

(* Some fancy notation *)
Notation "x :%: xs" := (scons _ x _ _ xs) (at level 60, right associativity).
Notation " [%] " := (snil (le_n _)).
Notation " [% x %] " := (scons' x  _ [%]).
Notation " [% x ; .. ; y %] " := (scons' x _ .. (scons' y _ [%]) ..).

(* slist is a merging of the list datatype and an inductive version of sorted, which might look like this *)
Inductive sortedp : nat -> nat -> nat -> list nat -> Prop :=
  | nil_sorted : forall m n (pf : m <= n), sortedp O m n []
  | cons_sorted : forall l m n x xs (pf : x <= m) (tailpf : sortedp l m n xs), sortedp (S l) x n (x :: xs).

(* questions: 
     1 is x <= xsn in scons?
     2 does (slist m n) -> (m <= n)
   2 implies 1 and 1 is true.  let's prove it.
*)

Lemma slist_order : forall {l m n} (xs:slist l m n), m <= n.
Proof.
  intros l m n xs ; induction xs.
  - auto.
  - transitivity x ; auto.
    transitivity xsm ; auto.
Qed.

(* Looking just at the definition it isn't clear which values are the
"values in the list".  Let's define it.
*)

Fixpoint to_list {l m n} (xs:slist l m n) : list nat :=
  match xs with
  | snil _ _ _ => []
  | scons _ _ _ _ x _ _ xs' => x :: to_list xs'
  end.

(* we will need a weakening lemma which lets us turn (slist l m n) into (slist l m' n')
   for m' <= m and n' >= n *)
Fixpoint slist_weaken' 
  {l} m n m' n' (xs:slist l m n) {struct xs} : m' <= m -> n' >= n -> slist l m' n'.
refine(
  match xs in slist l m n return m' <= m -> n' >= n -> slist l m' n' with
  | snil _ _ _ => fun _ _ => snil _
  | scons _ _ _ _ x _ _ xs' => fun _ _ => x :%: slist_weaken' _ _ _ _ _ xs' _ _
  end) ; auto.
- transitivity m0 ; [|transitivity n0] ;auto.
- transitivity m0 ; auto.
Defined.

Definition slist_weaken {l} m n m' n' p1 p2 xs := slist_weaken' (l := l) m n m' n' xs p1 p2.

(* Now let's implement merge again, but with intrinsic verification *)
Fixpoint smerge 
  {xsl ysl xsm ysm xsn ysn}
  (xs : slist xsl xsm xsn) (ys : slist ysl ysm ysn) 
  (l : nat) {struct l} : l = xsl + ysl -> slist (xsl + ysl) (min xsm ysm) (max xsn ysn).
(* Here is the skeleton of the computation with holes for branches.
We can't directly put terms here because we need to rewrite using
equalities to get a better type for each case *)
(* note the 'as' and 'return' clauses which are necessary to refine the return type *)
refine(
  match l as l return l = xsl + ysl -> slist (xsl + ysl) (min xsm ysm) (max xsn ysn) with
  | O => fun (pf' : O = xsl + ysl) => _
  | S l' =>
    (* again, the 'return' clause is necessary to refine the return type *)
    match xs in slist xsl xsm xsn
    return S l' = xsl + ysl -> slist (xsl + ysl) (min xsm ysm) (max xsn ysn) 
    with
    | snil _ _ _ => fun (pf' : S l' = ysl) => _
    | scons xm xs'l xs'm xs'n x xmltx xltxs'm xs'  =>
      match ys in slist ysl ysm ysn
      return S l' = S xs'l + ysl -> slist (S xs'l + ysl) (min xm ysm) (max xs'n ysn)
      with 
      | snil _ _ _ => fun _ => _
      | scons ym ys'l ys'm ys'n y ymlty yltys'm ys' => fun (pf' : S l' = S xs'l + S ys'l) =>
          match nat_lte x y with
          | left _ => _
          | right _ => _
          end
      end
    end
  end
).
(* We'll write this program using smaller refinement steps *)
- (* This is the l = O case *)
  (* Now we need to do some inverted reasoning. 0 = xsl + ysl -> xs = ys = [] *) 
  symmetry in pf'.
  apply Plus.plus_is_O in pf' ; destruct pf'.
  subst ; simpl.
  inversion xs ; subst.
  inversion ys ; subst.
  refine (snil _).
  apply NPeano.Nat.min_le_iff.
  left.
  apply NPeano.Nat.max_le_iff.
  left ; auto.
- (* This is the xs = snil case *)
  simpl.
  (* we want to use ys, but need to weaken it first *)
  refine (slist_weaken ysm ysn _ _ _ _ ys) ; crush.
- (* This is the ys = snil case *)
  simpl.
  rewrite <- plus_n_O.
  apply (slist_weaken xm xs'n) ; [crush|crush|].
  refine (x :%: xs') ; crush.
- (* Both lists are cons and x <= y *) 
  simpl.
  refine (let zs := smerge _ _ _ _ _ _ xs' (y :%: ys') l' _ in _) ; auto.
  refine (x :%: zs).
  + apply NPeano.Nat.min_le_iff.
    left ; auto.
  + apply Min.min_glb ; auto.
- (* Both lists are cons and x > y *)
  simpl.
  refine (let zs := smerge _ _ _ _ _ _ (x :%: xs') ys' l' _ in _) ; auto.
  { injection pf' ; intros ; subst. rewrite <- plus_n_Sm ; auto. }
  simpl in *.
  rewrite <- plus_n_Sm.
  refine (y :%: zs).
  + apply NPeano.Nat.min_le_iff.
    right ; auto.
  + apply Min.min_glb ; auto.
    apply Lt.lt_le_weak ; auto.
Defined.
Print smerge.

(* let's use it! *)

(* a small sorted list *)
Definition xs0 : slist 3 1 5. refine([% 1 ; 3 ; 5 %]) ; omega. Defined.

Eval compute in to_list (smerge xs0 xs0 _ eq_refl).
(* Yuck! What's going wrong here?  evaluation is stuck on some of our
proofs.  we need to rewrite smerge so that to_list can pull out the
data without needing to evaluate through proofs which have been
defined to be opaque.

Search for plus_n_Sm in the term.  These aren't reducing.  Let's
define our own version that is transpared (meaning it reduces).
Transparent definitions are given with "Defined" while opaque are
given with "Qed".

 *)

Lemma my_plus_n_Sm : forall n m, S (n + m) = n + S m.
  induction n ; intros ; simpl ; try reflexivity.
  rewrite IHn ; reflexivity.
Defined.

(* This version of smerge2 will now reduce nicely (the only change is [plus_n_Sm => my_plus_n_Sm] *)
Fixpoint smerge2
  {xsl ysl xsm ysm xsn ysn}
  (xs : slist xsl xsm xsn) (ys : slist ysl ysm ysn) 
  (l : nat) {struct l} : l = xsl + ysl -> slist (xsl + ysl) (min xsm ysm) (max xsn ysn).
(* note the 'as' and 'return' clauses which are necessary to refine the return type *)
refine(
  match l as l return l = xsl + ysl -> slist (xsl + ysl) (min xsm ysm) (max xsn ysn) with
  | O => fun (pf' : O = xsl + ysl) => _
  | S l' =>
    (* again, the 'return' clause is necessary to refine the return type *)
    match xs in slist xsl xsm xsn
    return S l' = xsl + ysl -> slist (xsl + ysl) (min xsm ysm) (max xsn ysn) 
    with
    | snil _ _ _ => fun (pf' : S l' = ysl) => _
    | scons xm xs'l xs'm xs'n x xmltx xltxs'm xs'  =>
      match ys in slist ysl ysm ysn
      return S l' = S xs'l + ysl -> slist (S xs'l + ysl) (min xm ysm) (max xs'n ysn)
      with 
      | snil _ _ _ => fun _ => _
      | scons ym ys'l ys'm ys'n y ymlty yltys'm ys' => fun (pf' : S l' = S xs'l + S ys'l) =>
          match nat_lte x y with
          | left _ => _
          | right _ => _
          end
      end
    end
  end
).
(* We'll write this program using smaller refinement steps *)
- (* This is the l = O case *)
  (* Now we need to do some inverted reasoning. 0 = xsl + ysl -> xs = ys = [] *) 
  symmetry in pf'.
  apply Plus.plus_is_O in pf' ; destruct pf'.
  subst ; simpl.
  inversion xs ; subst.
  inversion ys ; subst.
  refine (snil _).
  apply NPeano.Nat.min_le_iff.
  left.
  apply NPeano.Nat.max_le_iff.
  left ; auto.
- (* This is the xs = snil case *)
  simpl.
  (* we want to use ys, but need to weaken it first *)
  refine (slist_weaken ysm ysn _ _ _ _ ys) ; crush.
- (* This is the ys = snil case *)
  simpl.
  rewrite <- plus_n_O.
  apply (slist_weaken xm xs'n) ; [crush|crush|].
  refine (x :%: xs') ; crush.
- (* Both lists are cons and x <= y *) 
  simpl.
  refine (let zs := smerge2 _ _ _ _ _ _ xs' (y :%: ys') l' _ in _) ; auto.
  refine (x :%: zs).
  + apply NPeano.Nat.min_le_iff.
    left ; auto.
  + apply Min.min_glb ; auto.
- (* Both lists are cons and x > y *)
  simpl.
  refine (let zs := smerge2 _ _ _ _ _ _ (x :%: xs') ys' l' _ in _) ; auto.
  { injection pf' ; intros ; subst.
    rewrite <- my_plus_n_Sm ; auto. }
  simpl in *.
  rewrite <- my_plus_n_Sm.
  refine (y :%: zs).
  + apply NPeano.Nat.min_le_iff.
    right ; auto.
  + apply Min.min_glb ; auto.
    apply Lt.lt_le_weak ; auto.
Defined.

Eval compute in to_list (smerge2 xs0 xs0 _ eq_refl).
(* Better :) *)
Require Import List CpdtTactics.
Import ListNotations.

(* An abbreviation which given two nats n and m, 
   decides whether {n <= m} or {n > m}. *)
Definition nat_lte := Compare_dec.le_gt_dec.

(* Insert a number into a list.  Assumes the list is
   sorted in in non-decreasing order. *)
Fixpoint insert (n:nat) (xs:list nat) : list nat := 
  match xs with 
    | [] => [n]
    | h::t => if nat_lte n h then n::h::t else h::(insert n t)
  end.

(* Insertion sort. *)
Definition insert_sort (xs:list nat) : list nat := 
  fold_right insert [] xs.

(* Simple test. *)
Eval compute in insert_sort [3;2;5;1;7].

(* A useful predicate on lists.  list_all P xs holds 
   when P holds on each element of xs. *)
Definition list_all {A:Type} (P:A->Prop) (xs:list A) : Prop := 
  fold_right (fun h t => P h /\ t) True xs.

(* We can use list_all to define a notion of a sorted list. *)
Fixpoint sorted (xs:list nat) : Prop := 
  match xs with 
    | [] => True
    | h::t => sorted t /\ list_all (le h) t
  end.

(* Notice that this produces a predicate (which we can't prove!) *)
Eval compute in sorted [3;1;2].

(* We can prove this predicate though. *)
Example sorted_123 : sorted [1;2;3].
Proof.
  simpl. 
  auto 100.
Qed.

(* Here's an alternative definition of sorted using an
   couple of inductive definitions. *)
Inductive list_lte : nat -> list nat -> Prop := 
| nil_list_lte : forall n, list_lte n nil
| cons_list_lte : forall n h t, n <= h -> list_lte n t -> list_lte n (h::t).

Inductive sorted' : list nat -> Prop := 
| nil_is_sorted : sorted' nil
| cons_is_sorted : forall h t, list_lte h t -> sorted' t -> sorted' (h::t).

(* And here's an example proof that the list [1;2;3] is sorted'. *)
Example sorted'_123 : sorted' [1;2;3].
Proof.
  Hint Constructors list_lte sorted'.
  auto 100.
Qed. 

(* The two definitions of sorted'ness are equivalent. *)
Lemma list_lte_iff_list_all_lte : 
  forall n (xs:list nat), 
    list_lte n xs <-> list_all (le n) xs.
Proof.
  induction xs ; crush.
  inversion H1 ; intros ; subst.
  auto.
  inversion H1 ; intros ; subst.
  auto.
Qed.

Lemma sorted_iff_sorted' : 
  forall (xs:list nat), 
    sorted xs <-> sorted' xs.
Proof.
  Hint Constructors sorted'.
  induction xs ; crush.
  constructor. 
  rewrite list_lte_iff_list_all_lte. auto. auto.
  inversion H1 ; intros ; subst. crush.
  rewrite <- list_lte_iff_list_all_lte.
  inversion H1 ; intros ; subst. auto.
Qed.

(* Let's try to prove that insert_sort produces a sorted list. *)
Lemma insert_sort_sorted : forall xs, sorted (insert_sort xs).
Proof.
  induction xs ; crush.
  unfold sorted.
  (* We're stuck since Coq doesn't know if (insert a (insert_sort xs))
     is empty or a cons. Let's try to convince it. *)
  remember (insert a (insert_sort xs)) as sorted_xs.
  destruct sorted_xs.
  (* If (insert a (insert_sort xs)) is empty, we don't have to prove
     anything -- an empty list is already sorted.  (But of course,
     (insert a (insert_sort xs)) is not empty. *)
  auto.
  (* Ugh!  We're no better off than we were before. Let's abort... *)
  Abort.

(* What we need to do first is prove something useful about 
   insert.  For example, if xs is sorted and we insert n into
   it, we should get back a sorted list.  Before juming into
   that, let me define some useful lemmas. *)

(* A useful lemma that lifts implication to list_all.  It says
   that if P x -> Q x for any x, then list_all P xs -> list_all Q xs.
*)
Lemma list_all_imp{A}: 
  forall (P Q : A -> Prop),
    (forall (x:A), P x -> Q x) -> 
  (forall (xs:list A), list_all P xs -> list_all Q xs).
Proof.
  intros P Q H.
  induction xs ; crush.
Qed.

(* If n <= m and m <= each element of xs, then n <= each element of xs. *)
Lemma list_lte_nm (n m:nat) (xs:list nat) : 
  n <= m -> list_all (le m) xs -> list_all (le n) xs.
Proof.
  intros.
  (* Aha!  Now we can use the list_all_imp lemma to avoid
    reasining about the list, and reduce this to a single element. *)
  eapply (list_all_imp (le m) (le n)) ; [ intros ; omega | auto ].
Qed.

(* So let's try to prove this fact now... *)
Lemma insert_sorted : forall n xs, sorted xs -> sorted (insert n xs).
Proof.
  induction xs ; crush.
  destruct (nat_lte n a) ; simpl.
  crush.
  (* Here's where our lemma above comes into play. *)
  eapply list_lte_nm ; eauto.
  crush.
  (* Ugh!  How are we supposed to prove that a <= insert n xs?
     Intuitively it's true, but how can we show this?  We need
     to know that if we insert n into xs, then the elements of
     the resulting list are either equal to n or one of the xs. *)
  Abort.

(* An equivalent way to capture "list_all" *)
Lemma in_list_all {A} (P:A->Prop) (xs:list A) : 
  (forall x, In x xs -> P x) <-> list_all P xs.
Proof.
  induction xs ; crush.
Qed.

(* Now we can prove that if you insert n into xs, then
   any element of the resulting list is either equal to
   n or one of the xs. *)
Lemma in_insert :
  forall (xs:list nat) (n:nat), 
    forall x, In x (insert n xs) -> x = n \/ In x xs.
Proof.
  induction xs ; crush.
  destruct (nat_lte n a) ; crush.
  specialize (IHxs _ _ H0). crush.
Qed.

(* The opposite fact will also be useful. *)
Lemma insert_in : 
  forall (xs:list nat) (n:nat), 
    forall x, x = n \/ In x xs -> In x (insert n xs).
Proof.
  induction xs ; crush.
  destruct (nat_lte n a) ; crush.
  destruct (nat_lte n x) ; crush.
  destruct (nat_lte n a) ; crush.
Qed.

Lemma insert_sorted : forall n xs, sorted xs -> sorted (insert n xs).
Proof.
  induction xs ; crush.
  destruct (nat_lte n a) ; simpl.
  crush.
  eapply list_lte_nm ; eauto.
  crush.
  (* here's where in_list_all comes into play -- we turn the
     list_all into reasoning about a particular element in 
     (insert n xs) which has to be either n or one of the xs. *)
  apply in_list_all.
  intros.
  generalize (in_insert xs n x H2). intro.
  destruct H3.
  crush.
  (* here's where the opposite lemma comes into play. *)
  rewrite <- in_list_all in H1.
  crush.
Qed.

(* Once we've proved that insert produces a sorted list, we
   can easily prove that insert_sort produces a sorted list. *)
Lemma insert_sort_sorted : forall xs, sorted (insert_sort xs).
Proof.
  induction xs ; crush.
  apply insert_sorted ; auto.
Qed.

(* However, note that the following function also produces
   a sorted list:
*)
Definition bogus_sort (xs:list nat) : list nat := nil.

Lemma bogus_sort_sorted (xs:list nat) : sorted (bogus_sort xs).
  apply I.
Qed.

(* Here's an attempt to capture what it means for a sort
   function to actually be correct.   The output should
   be sorted, the length of the input should equal the
   length of the output, and every member of the input 
   should be in the output (and vice versa, though this
   can be shown given that the lengths are the same.)
*)
Definition sublist {A} (xs ys:list A) : Prop := 
  forall (x:A), In x xs -> In x ys.

Definition sort_corr (xs ys:list nat) : Prop := 
  sorted ys /\ sublist xs ys /\ length xs = length ys.

(* There are, of course, alternative definitions.  For
   instance, we might specify that the output is a sorted
   permutation of the input.  

   Often, you can't predict what will be the most useful
   specification.  That depends largely on who'se using
   the code and what they need to know.  For instance,
   we might be using the sort routine as part of a set
   implementation.  In that case, these properties would
   be good enough, though we'd probably want to build
   some derived properties.  For instance, we might 
   like to know that 

     (sort_corr xs ys) -> (sort_corr xs zs) -> ys = zs

   which *cannot* be proven from the spec above (and in 
   fact is not true.)  
*)

(* Let's prove now that our insertion sort is correct,
   according to the definition we gave above.  We have
   already shown insert_sort produces a sorted list. 
   Now we just need to establish the other two properties: *)
Lemma insert_sort_sublist : forall xs, sublist xs (insert_sort xs).
Proof.
  unfold sublist.
  induction xs ; crush ; apply insert_in ; crush.
Qed.

Lemma insert_length : forall xs n, length (insert n xs) = S (length xs).
Proof.
  induction xs ; crush.
  destruct (nat_lte n a) ; crush.
Qed.

Lemma insert_sort_length : forall xs, length xs = length (insert_sort xs).
Proof.
  induction xs ; crush.
  rewrite insert_length. auto.
Qed.

(* And finally, we can show insertion sort is correct. *)
Lemma insert_sort_corr : forall xs, sort_corr xs (insert_sort xs).
Proof.
  unfold sort_corr. intro.
  split.
  apply insert_sort_sorted.
  split.
  apply insert_sort_sublist.
  apply insert_sort_length.
Qed.

(********************************************************)

(* Of course, we don't want to use an O(n^2) sort in practice.
   So here, I develop a merge sort.  This shows off something
   new -- defining a recursive function using something besides
   structural induction to establish termination.
*)


(* First, we need to define a function to merge two (already
   sorted lists).  Now normally, we'd write this as:

   Fixpoint merge (xs ys:list nat) {struct xs} : list nat := 
      match xs, ys with 
      | [], ys => ys
      | xs, [] => xs
      | h1::t1, h2::t2 => if nat_lte h1 h2 then 
                           h1 :: (merge t1 ys)
                         else
                           h2 :: (merge xs t2)
      end.

   But unfortunately, Coq will reject this because it's
   not the case that xs is always getting smaller, nor
   the case that ys is always getting smaller.  Of course,
   *one* of them is always getting smaller, so eventually,
   this will terminate.  

   But in this case, we can hack around the problem by
   simply re-organizing the function as follows:
*)
Fixpoint merge (xs:list nat) : list nat -> list nat := 
  match xs with 
    | nil => fun ys => ys
    | (x::xs') => 
      (fix inner_merge (ys:list nat) : list nat := 
         match ys with 
           | nil => x::xs'
           | y::ys' => if nat_lte x y then 
                         x :: (merge xs' (y::ys'))
                       else 
                         y :: (inner_merge ys')
         end)
  end.
(* Note that for the out loop, we only call it with a
   smaller xs, and for the inner loop, we only call it
   with a smaller ys.  So Coq can see by structural
   induction the loops that the definition terminates.

   Note that if you tried to pull inner_merge out and
   define it as a top-level function, Coq would no 
   longer be able to tell that merge terminates.  
   In this sense, Coq's termination checking isn't
   modular.
*)

(* Test that merge works. *)
Eval compute in merge [1;3;5] [2;4;6].
Eval compute in merge [3] [1;4].

(* This function takes a list of lists of nats, and 
   merges each pair of lists.  See the example below. *)
Fixpoint merge_pairs (xs:list (list nat)) : list (list nat) := 
  match xs with 
    | h1::h2::t => (merge h1 h2) :: (merge_pairs t)
    | xs' => xs'
  end.

Eval compute in merge_pairs [[1;3];[2;4;9];[0];[2;3]].
Eval compute in merge_pairs [[1;3];[2;4;9];[0]].

(* To define our actualy merge sort, we want to take the
   initial list [n1;n2;...;nm] and turn it into a list of 
   singleton lists: [[n1];[n2];...;[nm]] and then successively
   call merge_pairs until we get a single list out. *)

(* This function takes a list and turns it into a list
   of singleton lists of the elements. *)
Definition make_lists (xs:list nat) : list (list nat) := 
  List.map (fun x => x::nil) xs.

Eval compute in make_lists [5; 1; 4; 2; 3].
Eval compute in merge_pairs (merge_pairs (merge_pairs (make_lists [5; 1; 4; 2; 3]))).
(* As with merge, I would like to write the following function
   which is intended to iterate merging the pairs of a list of
   lists until we get a single list out:

  Fixpoint merge_iter (xs:list (list nat)) : list nat := 
    match xs with 
    | [] => []
    | [h] => h
    | h1::h2::xs' => merge_iter (merge_pairs (h1::h2::xs'))
    end.

  But Coq can't tell that this terminates.  The problem is
  that we are calling merge_iter on (merge_pairs (h1::h2::xs'))
  instead of xs'.  Since in principle, merge_pairs could return
  a list no smaller than the input, Coq rejects the definition.

  All is not lost, though.  In Coq, we can define functions
  that use an arbitrary measure (or really, any well-founded
  relation) and show that the measure is always decreasing
  to convince Coq the function terminates.  

  Before doing that, I need to establish a lemma that:

   length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs)

  This is a little tricky to prove since we are peeling off
  2 elements instead of one.  One way to prove it is using
  so-called "strong-induction", but here's another way:
*)
Lemma merge_pairs_length' : 
  forall xs, (forall h1 h2, 
                length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs)) /\
             (forall h, 
                length (merge_pairs (h::xs)) <= length (h::xs)).
Proof.
  induction xs ; crush.
Qed.

(* What I did in merge_pairs_length' is generalize my desired
   property to one that holds regardless of the number of elements
   in the list.  Try doing it without the second case and see what
   goes wrong... *)

(* Anyway, my decreasing measure is now easy to establish from the
   lemma above. *)
Lemma merge_pairs_length : 
  forall h1 h2 xs, length (merge_pairs (h1::h2::xs)) < length (h1::h2::xs).
Proof.
  intros.
  specialize (merge_pairs_length' xs). 
  intros [H _].
  apply H.
Qed.

(* Now I'm going to define my merge_iter function.  Since it's
   not structurally recursive, but rather, defined using a measure,
   I first need to import a couple of libraries. *)
Require Import Program.
Require Import Wf.
Require Import Recdef.

(* The [Program Fixpoint] construct is similar to the [Fixpoint]
   construct.  The big difference is that I'm required to state
   a [{measure ...}] clause to convince Coq as to what's going
   down.  In this case, the length of the argument list is always
   going down when we do a recursive call.
*)
Function merge_iter (xs : list (list nat)) {measure length} : 
  list nat :=
  match xs with 
   | nil => nil
    | h::nil => h
    | h1::h2::xs' => merge_iter (merge_pairs (h1::h2::xs'))
  end.
intros.
apply merge_pairs_length.
Defined.

Print merge_iter.

(* If we print out merge_iter... *)
Print merge_iter.
(* ...we see that the [Program Fixpoint] did a lot of work for us
   to translate our definition into the real core of Coq.  It's
   using a special function Fix_sub, along with some other hidden
   definitions that you can print out if you like. *)
Print Fix_sub.
(* Fix_sub is defined in terms of Fix_F_sub. *)
Print Fix_F_sub.
(* Fix_F_sub is defined to be:

   fun (A : Type) (R : A -> A -> Prop) (P : A -> Type)
     (F_sub : forall x : A, (forall y : {y : A | R y x}, P (` y)) -> P x) =>
       fix Fix_F_sub (x : A) (r : Acc R x) {struct r} : P x :=
       F_sub x

  If you look carefully, this is proceeding by (structural) induction
  on r and is just a seemingly infinite loop.  But since r must be
  getting smaller each time around the loop, the loop actually
  terminates.

  What is r?  It's a proof that the value x is "accessible" (Acc) with
  respect to the relation R.  In our case, R is essentially the 
  relation between the length of the original input
  the length of the list we are recursing on (a < relation on the
  lengths of the lists.)  The "accessible" notion is capturing the
  idea that our relation has no infinite descending chains.  In the
  case of <, there is a least element, namely 0.  So if we are always
  going down in the relation, we will eventually get to 0.  

  TL;DR:  You don't need to understand all of this.  You just need
  to be able to use the [Program Fixpoint ... {measure ...}] construct
  to write functions and argue that the generated obligations are
  met (i.e., that your measure really is decreasing.)
*)

(* Once we've defined our merge_iter, we can finally define
   our merge_sort: *)
Definition merge_sort (xs:list nat) := 
  merge_iter (make_lists xs).

(* Let's test that it's working... *)
Eval compute in merge_sort [7;8;3;5;1;2;6;4].
Eval compute in merge_sort [3;2;7;8].

(* Exercises:

1. Show that

   a. sorted xs -> sorted ys -> sorted (merge xs ys)

*)

Lemma merge_list_all : forall P xs ys, list_all P xs -> list_all P ys -> list_all P (merge xs ys).
intros P xs.
induction xs; intros.
simpl. assumption.
simpl merge.
induction ys.
assumption.
remember (nat_lte a a0) as cond. destruct cond.
simpl. destruct H. split. assumption. eapply IHxs; assumption.
destruct H0. apply IHys in H1.
simpl. split; assumption.
Qed.

Lemma list_all_le : forall a n ys, a <= n -> list_all (le n) ys -> list_all (le a) ys.
intros.
induction ys.
simpl. reflexivity.
destruct H0.
apply IHys in H1.
simpl. split. rewrite H0 in H. assumption.
assumption.
Qed.

Theorem merged_sorted : forall xs ys, sorted xs -> sorted ys -> sorted (merge xs ys).
  intro xs.
  induction xs; intros.
  simpl. assumption.
  induction ys. assumption.
  simpl merge.
  destruct (nat_lte a a0); simpl; split.
  (* a <= a0 *)
      eapply IHxs.
      crush. crush.
      eapply merge_list_all.
      crush.
      simpl.
      split. assumption. apply list_all_le with (n:=a0); crush.
  (* a > a0 *)
    simpl in H0.
    destruct H0.
    apply IHys in H0.
    simpl in H0.
    assumption.
    simpl in H0.
    eapply merge_list_all with (P:=(le a0)) (xs:=(a :: xs)) (ys:= ys); intros.
    simpl.
    split.
    crush.
    simpl in H. destruct H. apply list_all_le with (n:=a); crush.
    crush.
Qed.

(*
   b. (length xs + length ys) = length (merge xs ys)
*)

Require Import Arith.

Theorem merge_adds : forall xs ys, (length xs + length ys) = length (merge xs ys).
  induction xs. crush.
  induction ys. crush.
  simpl. destruct (nat_lte a a0).
  simpl. rewrite <- IHxs with (ys:=(a0 :: ys)).
  crush. simpl in *. rewrite <- IHys. crush.
Qed.

(*
   c. In x xs \/ In x ys <-> In (merge xs ys)
*)

Theorem merged_in : forall x xs ys, In x xs \/ In x ys <-> In x (merge xs ys).
  induction xs. crush.
  induction ys. crush.
  simpl. destruct (nat_lte a a0).
  simpl. rewrite <- IHxs with (ys:=(a0 :: ys)). crush. 
  simpl in *. rewrite <- IHys. crush.
Qed.

(*

2. Show that 

   a. list_all sorted xs -> list_all sorted (merge_pairs xs)

*)

Require Import Arith.Even.

Lemma length0 : forall A (xs : list A), length xs = 0 <-> xs = [].
induction xs. crush. simpl. split; crush.
Qed.

Lemma length0' : forall A (xs : list A), 0 = length xs <-> xs = [].
induction xs. crush. simpl. split; crush.
Qed.

Lemma not_odd_and_even : forall n, odd n -> even n -> False.
crush. apply not_even_and_odd with (n:=n); assumption.
Qed.

Lemma oddS : forall m, odd (S m) -> even m.
intros. destruct m.
crush. specialize even_odd_dec with (n:=(S m)).
intros. destruct H0. assumption. contradict H.
intro. apply not_even_and_odd with (n:=(S (S m))).
constructor. assumption. assumption.
Qed.

Lemma evenS : forall m, even (S m) -> odd m.
intros. induction m.
contradict H. crush. assert (odd 1). crush.
apply not_even_and_odd with (n:=1); assumption.
specialize even_odd_dec with (n:=(S m)).
intros. destruct H0. apply IHm in e.
contradict H. intro. apply not_even_and_odd with (n:=(S (S m))).
assumption. constructor. constructor. assumption. assumption.
Qed.
 
Lemma evenSn: forall m, (even m -> (exists n, m = 2*n)) /\ (odd m -> exists n, m = S(2*n)).
induction m.
split. intros. exists 0. simpl. reflexivity.
intro. contradict H. crush. assert (even 0). crush. 
apply not_even_and_odd with (n:=0); assumption.
split. destruct IHm.
intro. apply evenS in H1. apply H0 in H1.
destruct H1. rewrite H1. exists (S x). crush.
destruct IHm. intro. apply oddS in H1. apply H in H1.
destruct H1. rewrite H1. exists x. crush.
Qed.

Lemma evenSn2: forall m, (exists n, m = 2*n) -> even m.
intros. destruct H. simpl in H. assert( x + (x + 0) = x+x). crush. rewrite H0 in H. clear H0.
specialize even_odd_dec with (n:=x).
intros. rewrite H. destruct H0.
apply even_even_plus; assumption.
apply odd_even_plus; assumption.
Qed.

Lemma test: forall A (xs: list A), even (length xs) -> (length xs <> 0) -> (exists a b t, (xs = a :: b :: t) /\ (even (length t))).
intros.
destruct xs. contradict H0.
simpl. reflexivity.
destruct xs.
contradict H.
simpl. intro.
assert (odd 1). crush.
apply not_even_and_odd with (n:=1); assumption.
exists a. exists a0. exists xs. split. reflexivity.
simpl in H. apply evenS in H. apply oddS in H. assumption.
Qed.

Lemma neq : forall n, n<>0 <-> exists m, n = S m.
crush. destruct n. crush. exists n. reflexivity. Qed.

Lemma list_all_tail : forall A P (l:A) (r: list A), list_all P r /\ P l <-> list_all P (r ++ [l]).
intros. induction r; simpl; crush.
Qed.

Lemma app_cons : forall A (x:A) xs, x :: xs = [x] ++ xs.
crush.
Qed.

Lemma merge_pairs_app: forall xs l, even (length xs) -> merge_pairs (xs ++ [l]) = (merge_pairs xs) ++ [l].
  Lemma merge_pairs_app': forall n xs l, (n*2) = length xs -> merge_pairs (xs ++ [l]) = (merge_pairs xs) ++ [l].
    induction n.
    intros. simpl in H. apply eq_sym in H. rewrite length0 in H. rewrite H.
    simpl. reflexivity.
    intros.
    pose proof test.
    assert (even (length xs)). apply evenSn2. exists (S n).
    rewrite mult_comm. apply eq_sym. assumption.
    specialize H0 with (xs:=xs).
    apply H0 in H1. destruct H1. destruct H1. destruct H1.
    destruct H1. rewrite H1. simpl.
    assert (merge_pairs x1 ++ [l] = merge_pairs (x1 ++ [l])).
    apply eq_sym. apply IHn.
    rewrite H1 in H. simpl in H. injection H. intros. assumption.
    rewrite H3. reflexivity.
    apply neq. rewrite <- H. simpl. exists (S (n * 2)). reflexivity.
  Qed.
  intros. apply evenSn in H. destruct H.
  apply merge_pairs_app' with (n:=x). crush.
Qed.


Lemma odd0 : odd 0 -> False. intro. assert (even 0). crush. apply not_even_and_odd with (n:=0); assumption. Qed.

Ltac mymagic := match goal with
  | [ H: odd 0 |- _ ] => apply odd0 in H; crush
  | [ H: odd (length []) |- _ ] => simpl in H; apply odd0 in H; crush
  | [ H: context[ _ + length [_]] |- _ ] => simpl length in H; rewrite plus_comm in H; simpl plus in H
  | [ H: context[(length (_ ++ [_]))] |- _ ] => rewrite app_length in H; mymagic
  | [ H: 0 = length ?xs |- _ ] => apply eq_sym in H; apply length0 in H
end.

Lemma evenSn' : forall A (Q: list A -> Prop), (forall n (xs : list A), 2*n = length xs -> Q xs) <-> (forall (xs : list A), (even (length xs)) -> Q xs).
  intros. split.
  intros. apply evenSn in H0.  destruct H0. apply eq_sym in H0. apply H in H0. assumption.
  intros. eapply H. apply evenSn2. exists n. crush.
Qed.

Lemma list_odd : forall A (xs:list A), (odd (length xs)) -> (exists (ys:list A) (t:A), xs = ys ++ [t] /\ even (length ys)).
  intros.
  assert (xs <> []). crush. mymagic.
  exists (removelast xs). apply exists_last in H0.
  destruct H0. destruct s. exists x0. rewrite e. rewrite removelast_app. simpl.
  rewrite app_nil_r. split. reflexivity.
  rewrite e in H. mymagic. apply oddS in H. assumption. crush.
Qed.

Ltac third := let HH:=fresh in let H2:=fresh "X" in intro n; induction n; [
        (* Base Case *)
        simpl mult; try (split; intros x HH); try rewrite length0' in HH; subst; simpl in *; [ crush; try mymagic; crush | .. ]; try assumption |
        (* Start of Recursive Case *)
        intros xs Hy;
        remember (2 * S n) as m;
        assert (even m /\ m <> 0) as Hx; [ split; [ apply evenSn2; exists (S n); assumption | crush ] | ];
        specialize test with (xs:=xs); intros Hm; rewrite <- Hy in Hm;
        destruct Hx; destruct Hm as [x H2]; [ assumption | assumption | .. ] ];
        destruct H2 as [y H2]; destruct H2 as [z H2]; destruct H2; subst.

Theorem merge_pairs_sorted : forall xs, list_all sorted xs -> list_all sorted (merge_pairs xs).
  Lemma merge_pairs_sorted_even : forall xs, (even (length xs)) -> list_all sorted xs -> list_all sorted (merge_pairs xs).
    erewrite <- evenSn'. third. crush. apply merged_sorted; assumption.

  Qed.
  intros.
  remember (length xs) as n.
  specialize even_odd_dec with (n:=n). intros Hx. destruct Hx. 
   + apply merge_pairs_sorted_even; [ crush | .. ]; try assumption.
   + specialize list_odd with (xs:=xs). intros Hy. subst. apply Hy in o.
     destruct o eqn:Hz. destruct Hz eqn:Ha. destruct e eqn:Hb. crush.
     rewrite merge_pairs_app; [ | assumption ].
     (* apply eq_sym. rewrite fold_right_app. *)
     rewrite H1 in H. apply list_all_tail in H. destruct H.
     apply list_all_tail; (try split); try assumption.
     apply merge_pairs_sorted_even. assumption. assumption.
Qed.

(*
   b. (sum of lengths of lists in xs) = 
        (sum of lengths of lists in merge_pairs xs)
*)

Definition sum_length (a:list nat) (b:nat) := (plus (length a) b).

Hint Unfold sum_length.

Theorem sum_merge_pairs : forall (xs: list (list nat)), (fold_right sum_length 0 xs) = (fold_right sum_length 0 (merge_pairs xs)).
  Lemma sum_merge_pairs_even : forall d xs, (even (length xs)) -> (fold_right sum_length d xs) = (fold_right sum_length d (merge_pairs xs)).
    intro d. erewrite <- evenSn'.
    third. crush. unfold sum_length. fold sum_length. rewrite <- merge_adds. erewrite <- IHn; [ | crush]. crush.
  Qed.
  intros.
  remember (length xs) as n.
  specialize even_odd_dec with (n:=n). intros Hx. destruct Hx. 
   + apply sum_merge_pairs_even; [ crush | .. ]; try assumption.
   + specialize list_odd with (xs:=xs). intros Hy. subst. apply Hy in o.
     destruct o eqn:Hz. destruct Hz eqn:Ha. destruct e eqn:Hb. 
     destruct a as [aa ab]. rewrite aa.
     rewrite merge_pairs_app; [ | assumption ].
     (* End Generic Skeleton *)
     rewrite fold_right_app. apply eq_sym. rewrite fold_right_app.
     rewrite <- sum_merge_pairs_even; [ | assumption ].
     subst. reflexivity.
Qed.

(*
   c. (x is in one of the lists in xs) <->
        (x is in one of the lists in merge_pairs xs)

*)
Definition InOneOf (x:nat) (xs: list (list nat)) : Prop :=
 exists subl, (In x subl) /\ (In subl xs).

Hint Unfold InOneOf.

Lemma In_app : forall A (x: A) xs ys, In x (xs ++ ys) <-> In x xs \/ In x ys.
  intros. induction xs; crush.
Qed.

Lemma InOneOf_app : forall x xs ys, InOneOf x (xs ++ ys) <-> InOneOf x xs \/ InOneOf x ys.
  intros. unfold InOneOf.
  split; intros.
  do 2 destruct H; rewrite In_app in H0. 
  { destruct H0.
    + left. exists x0. split; assumption.
    + right. exists x0. split; assumption. 
  }
  do 2 destruct H; exists x0; rewrite In_app; crush.
Qed.

Lemma InOneOf_one : forall x y, InOneOf x [y] <-> In x y.
  crush. unfold InOneOf in H. crush. unfold InOneOf. exists y. crush.
Qed.

Lemma InOneOf_cons : forall x xs y, InOneOf x (y :: xs) <-> In x y \/ InOneOf x xs.
  intros. rewrite app_cons. rewrite <- InOneOf_one. eapply InOneOf_app.
Qed. 

Theorem InPairs : forall (x:nat) (xs: list (list nat)), InOneOf x xs <-> InOneOf x (merge_pairs xs).
  Lemma InPairs_even : forall x xs, (even (length xs)) -> (InOneOf x xs <-> InOneOf x (merge_pairs xs)).
     intro d. erewrite <- evenSn'. third.
     simpl merge_pairs. repeat rewrite InOneOf_cons.
     rewrite <- merged_in. rewrite IHn; [ | crush ].
     crush.
  Qed.
  intros.
  remember (length xs) as n.
  specialize even_odd_dec with (n:=n). intros Hx. destruct Hx. 
   + apply InPairs_even; [ crush | .. ]; try assumption.
   + specialize list_odd with (xs:=xs). intros Hy. subst. apply Hy in o.
     destruct o eqn:Hz. destruct Hz eqn:Ha. destruct e eqn:Hb.
     destruct a as [aa ab]. rewrite aa.
     rewrite merge_pairs_app; [ | assumption ].
     (* End Generic Skeleton *)
     rewrite InOneOf_app. apply iff_sym. rewrite InOneOf_app. 
     rewrite InPairs_even with (xs:=x0); [ | assumption ].
     reflexivity.
Qed.

(*

3. Show that

   a. list_all sorted xs -> sorted (merge_iter xs)

*)

Theorem merge_iter_sorted : forall xs, list_all sorted xs -> sorted (merge_iter xs).
intros.
functional induction (merge_iter xs).
crush. crush. apply merge_pairs_sorted in H. apply IHl in H. assumption.
Qed.

(*
   b. (sum of lengths of lists in xs) = length of (merge_iter xs)
*)

Theorem merge_iter_length : forall xs, (fold_right sum_length 0 xs) = length (merge_iter xs).
intros.
functional induction (merge_iter xs).
crush. crush. unfold sum_length. crush.
rewrite sum_merge_pairs. assumption.
Qed.

(*
   c. (x is in one of the lists in xs) <-> In x (merge_iter xs)
*)

Theorem merge_iter_in : forall x xs, InOneOf x xs <-> In x (merge_iter xs).
intros.
functional induction (merge_iter xs).
crush. unfold InOneOf in H. destruct H. crush.
crush. unfold InOneOf in H. crush.
unfold InOneOf. exists h. crush.
rewrite InPairs. assumption.
Qed.

(*
4.  Show that
    a. make_lists xs is sorted
    b. In x xs <-> (x is in one of the lists in make_lists xs)
    c. length xs = (sum of the lengths of the lists in make_lists xs)
*)

Theorem make_lists_sorted : forall xs, list_all sorted (make_lists xs).
induction xs. crush. simpl. crush.
Qed.

Theorem make_lists_in : forall x xs, In x xs <-> InOneOf x (make_lists xs).
intros. induction xs.
crush. unfold InOneOf in H. destruct H. crush.
simpl. rewrite app_cons. rewrite InOneOf_app.
split. intros.
destruct H. left. rewrite H. unfold InOneOf. exists [x]. crush.
apply IHxs in H. right. assumption.
intros. destruct H. left. unfold InOneOf in H. destruct H. crush. crush.
Qed.

Theorem make_lists_length : forall xs, length xs = (fold_right sum_length 0 (make_lists xs)).
intros. induction xs. crush.
simpl. unfold sum_length. fold sum_length. crush.
Qed.

 (*

5.  Show that sort_corr xs (merge_sort xs)

*)

Theorem merge_corr: forall xs, sort_corr xs (merge_sort xs).
crush. unfold sort_corr. unfold merge_sort.
split. apply merge_iter_sorted. apply make_lists_sorted.
split. unfold sublist. intros.
apply merge_iter_in. apply make_lists_in. assumption.
rewrite <- merge_iter_length. apply make_lists_length.
Qed.

(*

6.  Define a better definition of correctness for sorts (sort_corr').

*)

Require Import Permutation.

Definition sort_corr' (xs ys:list nat) : Prop :=
  sorted ys /\ Permutation xs ys.

(* This is better because *)
Goal sort_corr ([1;1;2;2;3;3]) ([1;1;2;2;2;3]).
  unfold sort_corr.
  unfold sorted.
  unfold sublist.
  simpl.
  crush.
Qed.

Goal ~ sort_corr' ([1;1;2;2;3;3]) ([1;1;2;2;2;3]). 
  unfold sort_corr'. crush. clear -H1.
  repeat apply Permutation_cons_inv in H1.
  apply Permutation_length_2_inv in H1.
  destruct H1; crush.
Qed.

(* Let's show that this is a stronger condition *)
Theorem sort_corr'_strong : forall xs ys, sort_corr' xs ys -> sort_corr xs ys.
  intros. unfold sort_corr. unfold sort_corr' in H. crush.
  - unfold sublist. intros. apply Permutation_in with (l:=xs); assumption.
  - apply Permutation_length; assumption.
Qed.

(* And let's show that merge still satisfies this *)
Fixpoint flatten {A: Type} (xs: list (list A)) : list A :=
  match xs with
   | [] => []
   | A::B => (app A (flatten B))
  end.

Lemma flatten_app : forall x (xs: list (list nat)), flatten (xs ++ [x]) = (flatten xs) ++ x.
  intros. induction xs; crush.
Qed.

Lemma make_lists_inv : forall xs, xs = (flatten (make_lists xs)).
  induction xs. crush. crush.
Qed.

Theorem merge_pairs_permutation : forall xs, Permutation (flatten xs) (flatten (merge_pairs xs)).
Lemma merge_pairs_permutation_even : forall xs, even (length xs) -> Permutation (flatten xs) (flatten (merge_pairs xs)).
  Lemma merge_pairs_permutation_even' : forall n xs, 2*n=length xs -> Permutation (flatten xs) (flatten (merge_pairs xs)).
    Lemma merge_permutation : forall xs ys, Permutation (xs++ys) (merge xs ys).
      induction xs. crush.
      induction ys. 
      - crush. apply perm_skip. specialize IHxs with (ys:=[]). 
        rewrite app_nil_r in IHxs. apply Permutation_sym. assumption.
      - simpl. destruct (nat_lte a a0).
        apply perm_skip. eapply IHxs.
        apply Permutation_trans with (l' := (a0 :: a :: xs ++ ys)).
        + admit.
        + unfold merge in IHxs. fold merge in IHxs. apply perm_skip. apply IHys.
    Qed.
    third.
    specialize IHn with (xs:=z).
    assert (2*n = length z). crush.
    apply IHn in H1. clear IHn.
    crush.
    rewrite app_assoc.
    apply Permutation_app.
    apply merge_permutation.
    assumption.
  Qed.
  erewrite <- evenSn'. apply merge_pairs_permutation_even'.
  Qed.
  Show.
  intros.
  remember (length xs) as n.
  specialize even_odd_dec with (n:=n). intros Hx.
  destruct Hx. apply merge_pairs_permutation_even. crush.
  specialize list_odd with (xs:=xs). intros Hy. subst. apply Hy in o.
  destruct o eqn:Hz. destruct Hz eqn:Ha. destruct e eqn:Hb. crush.
  rewrite merge_pairs_app.
  remember (fold_right sum_length 0 (x1 ++ [x2])).
  do 2 rewrite flatten_app.
  apply Permutation_app_tail.
  apply merge_pairs_permutation_even. assumption.
  assumption.
Qed.

Theorem merge_iter_perm : forall xs, Permutation (merge_iter xs) (flatten xs).
  crush. functional induction (merge_iter xs).
  crush. crush. rewrite app_nil_r. apply Permutation_refl.
  apply Permutation_trans with (l' := flatten (merge_pairs (h1 :: h2 :: xs'))).
  assumption.
  apply Permutation_sym. apply merge_pairs_permutation.
Qed.

Theorem sort_corr'_merge : forall xs, sort_corr' xs (merge_sort xs).
  intros. unfold sort_corr'.
  specialize merge_corr with (xs:=xs). 
  split. unfold sort_corr in H. crush.
  unfold merge_sort.
  unfold sort_corr in H.
  unfold merge_sort.
  destruct (merge_sort xs).
  crush. apply length0 in H2. crush.
  rewrite make_lists_inv with (xs:=xs) at 1. 
  apply Permutation_sym.
  apply merge_iter_perm.
Qed.

(* From the chapter entitled Inductive Predicates in CPDT *)
Require Import Bool Arith List CpdtTactics.

Print ex.

Lemma exist1 : exists x : nat, x + 1 = 2.
Proof.
  exists 1.
  reflexivity.
Qed.

Lemma exist2 : forall (n m:nat), (exists x, n + x = m) -> n <= m.
Proof.
  destruct 1.
  crush.
Qed.

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
  constructor.
Qed.

Lemma isZero_plus : forall n m : nat, isZero m -> n + m = n.
Proof.
  destruct 1.
  crush.
Qed.

Lemma isZero_contra : isZero 1 -> False.
Proof.
  inversion 1.
Qed.

Inductive even : nat -> Prop := 
| Even0 : even 0
| EvenSS : forall n, even n -> even (S (S n)).

Theorem even_0 : even 0.
  constructor.
Qed.

Definition even_4 : even 4.
  repeat constructor.
Qed.
Print even_4.

(*Hint Constructors even.

Theorem even_4' : even 4.
  auto.
Qed.

*)
Theorem even_1_contra : even 1 -> False.
  intro H.
  inversion H.
Qed.
Print even_1_contra.

Theorem even_3_contr : even 3 -> False.
  intro H.
  inversion H.
  inversion H1.
Qed.

Hint Constructors even.
Theorem even_plus : forall n m, even n -> even m -> even (n + m).
Proof.
  induction 1 ; crush.
Qed.

(*
Theorem even_contra : forall n, even (S (n + n)) -> False.
  induction 1.
*)

Theorem even_contra : forall n, even (S (n + n)) -> False.
Proof.
  assert (forall n', even n' -> forall n, n' = S (n + n) -> False).
  Focus 2.
  intros.
  apply (H _ H0 _ eq_refl).
  induction 1 ; crush.
  destruct n ; destruct n0 ; crush.
  rewrite <- plus_n_Sm in H0.
  apply (IHeven _ H0).
Qed.

Print even_contra.

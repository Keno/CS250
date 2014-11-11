(* More about dependent types.
 *)
Require Import Coq.Lists.List.

(* Recall the type of lists in Coq's standard library.
 *)
Print list.
(* Inductive list (A : Type) : Type := *)
(*     nil : list A | cons : A -> list A -> list A *)

(* In this defintion, we call [A] a *parameter* of the inductive data
 * type.
 *)

(* From this definition it is pretty easy to write a function that
 * returns an element from the list.
 * We have to return an option because we could ask for an element off
 * the end of the list.
 *)

Fixpoint nth_error {T} (ls : list T) (n : nat) {struct ls} : option T :=
  match ls with
    | nil => None
    | l :: ls' => match n with
                    | 0 => Some l
                    | S n' => nth_error ls' n'
                  end
  end.

(* QUESTION: Can we implement the function if it is total, i.e. has
 * the following type?
 *   forall (T : Type) (ls : list T) (n : nat), T.
 * If so, construct it, otherwise, prove that it is impossible to construct
 * in Coq.
 *)

(* ADVANCED QUESTION:
 *   What is the difference between the above definition and the
 *   following alternative definition?
 *)
Fixpoint nth_error' {T} (ls : list T) (n : nat) {struct n} : option T :=
  match ls with
    | nil => None
    | l :: ls' => match n with
                    | 0 => Some l
                    | S n' => nth_error' ls' n'
                  end
  end.
(* It is subtle since we can prove that they are "equal".
 * Hint: Take a look at the proof in little more detail.
 * Why does Coq need to distinguish the two definitions?
 *)
Theorem nth_error_is_nth_error'
: forall T ls n, @nth_error T ls n = @nth_error' T ls n.
Proof.
  induction ls; destruct n; simpl; auto.
Qed.

Local Notation "[ ]" := (nil).
Local Notation "[ x ]" := (cons x nil).
Local Notation "[ x ; .. ; y ]" := (cons x (.. (cons y nil) ..)).

(* Theorem force_unfold_nth_error' {T} ls n : *)
(*   @nth_error' T ls n = *)
(*   match ls with *)
(*     | nil => None *)
(*     | l :: ls' => match n with *)
(*                     | 0 => Some l *)
(*                     | S n' => nth_error' ls' n' *)
(*                   end *)
(*   end. *)
(* destruct n; simpl. reflexivity. *)
(* Qed. *)

(* Goal forall ls x, @nth_error' nat ls x = None. *)
(*   intros. *)
(*   rewrite force_unfold_nth_error'. *)
(*   Show Proof. *)
(*   rewrite (force_unfold_nth_error' ls' n'). *)
(*   unfold nth_error'. *)


(* It is pretty easy to use [nth_error]:
 *)
Eval compute in nth_error [1;2;3] 2.

Eval compute in nth_error [1;2;3] 5.

(** Using Proofs **)
(******************)

(* A lot of times we know that [nth_error] is going to return success
 * or failure. In that case we might want to just get the result instead
 * of being forced to [match] on the option and do something in the case
 * that we get [None].
 *
 * Let's take a look at another defintion.
 *)
Theorem n_lt_0_any : forall (T : Type) n, n < 0 -> T.
intros. exfalso. inversion H.
Defined.

Theorem lt_inj : forall n m, S n < S m -> n < m.
  apply Lt.lt_S_n.
Defined.

Fixpoint nth_and_i_know {T : Type} (ls : list T) (n : nat)
: n < length ls -> T :=
  match ls as ls' return n < length ls' -> T with
    | nil => fun pf : n < 0 => n_lt_0_any _ _ pf
    | l :: ls' => match n as n return n < S (length ls') -> T with
                    | 0 => fun _ => l
                    | S n' => fun pf : S n' < S (length ls') =>
                                @nth_and_i_know _ ls' n' (lt_inj _ _ pf)
                  end
  end.

(* Now, this function is total but we do not get an
 * answer back until we provide a proof.
 *)
Eval compute in @nth_and_i_know _ [1;2;3] 2.

Definition two_lt_three : 2 < 3. repeat constructor. Defined.

Eval compute in @nth_and_i_know _ [1;2;3] 2 two_lt_three.

Eval compute in @nth_and_i_know _ [1;2;3] 5.
(* Here, we can not construct a proof so we'll never be able
 * to "get an answer out".
 *)

(* NOTE: The plumbing of proofs here actually makes the implementation
 *       quadratic since we have to construct a new proof every
 *       time we make the recursive call.
 *)

(** Encoding Facts in Dependent Types **)
(***************************************)

(* Passing the explicit proof is a little bit cumbersome.
 * An alternative approach is to combine the proof and
 * the index argument using dependent types.
 *
 * To do this, we'll make a type for "numbers up to some max"
 *)
Inductive fin : nat -> Type :=
| FO : forall {n}, fin (S n)
| FS : forall {n}, fin n -> fin (S n).
(* Because 'nat' occurs to the right hand side of the ':' it
 * is called a type *index* and it is allowed to vary between
 * different constructors of the inductive type
 *)
Definition four_of_six : fin 6 := FS (FS (FS (FS (FO)))).

(* This number is similar to the less-than proof that we passed
 * to [nth_and_i_know].
 *)
Unset Printing Notations.
Print le.
(* Inductive le (n : nat) : nat -> Prop := *)
(*     le_n : le n n | le_S : forall m : nat, le n m -> le n (S m) *)
Set Printing Notations.
(* Both types capture the difference between two natural numbers.
 *)

(* Now let's try to use this type to implement [nth_and_i_know] without
 * the extra proof argument.
 *
 * Doing this is going to require some 'dependent typing'-fu.
 * Let's review the 6 pieces to depenent pattern matching
 *
 *   match (1) in (2) as (3) return (4) with
 *     | (5) => (6)
 *   end
 *
 * (1) Is the discriminee, it is the object that we are inspecting
 * (2) The 'in' clause allows us to remember aspects about its *type*.
 *     The 'in' clause only matches *indicies*, *parameters* are not necessary
 *     since they are the same in all constructors
 * (3) The 'as' clause allows us to remember aspects of its *value*
 * (4) The 'return' clause allows us to use the information from (2) and
 *     (3) to describe the result type
 * (5) The pattern tells us what the different cases are
 * (6) The branch tells us what to do in each case
 *
 * The power of dependent pattern matching is based on a simple idea of
 * the 'inside' type versus the 'outside' type.
 * > The entire expression has the 'outside' type which is computed by
 *   determining the type of the discriminee and patterning it in the
 *   'in' clause and the value and substituting it in the 'return' clause
 * > Each branch is typed using the 'inside' type which is computed from
 *   the pattern.
 *)

(* First, let's prove that if you have a [fin 0] then you can prove anything.
 *)
Definition fin_0_any : forall T : Type, fin 0 -> T.
(* [inversion 1] would solve this but let's see if we
 * can write it using a dependent pattern match.
 *   inversion 1.
 *)
refine
  (fun T pf =>
     match pf : fin 0 in fin n return match n with
                                        | 0 => T
                                        | S _ => unit
                                      end
     with
       | FO n => tt : match (S n) with | 0 => T | S _ => unit end
       | FS n f => tt : match (S n) with | 0 => T | S _ => unit end
     end).
Defined.

(* Now we can continue with the implementation of [nth_fin].
 *)
Fixpoint nth_fin {T : Type} (ls : list T)
: fin (length ls) -> T :=
  match ls as ls return fin (length ls) -> T with
    | nil => fun pf : fin 0 => fin_0_any _ pf
    | l :: ls' => fun fn : fin (S (length ls')) =>
                    match fn in fin n return match n with
                                               | 0 => T
                                               | S x => (fin x -> T) -> T
                                             end
                    with
                      | FO _ => fun _ => l
                      | FS _ f => fun z => z f
                    end (@nth_fin _ ls')
  end.

Fixpoint lt_c (a b : nat) : Prop :=
  match a , b with
    | 0 , 0 => False
    | 0 , _ => True
    | S n , S m => lt_c n m
    | _ , _ => False
  end.

Fixpoint into_fin (n m : nat) : (lt_c n m) -> fin m.
Admitted.

Definition x : fin 3 := into_fin 2 3 I.
Print x.
Notation "!! x" := (into_fin x _ I) (at level 30).

(* We can still run our program like we expect.
 *)
Eval compute in nth_fin [ 1 ; 2 ; 3 ] (FS (FS FO)).

Eval compute in nth_fin [ 1 ; 2 ; 3 ] (FS FO).

(* Note that there is no way to get something that is not in the list.
 *)

(** Enriching Types with Properties **)
(*************************************)


(* In the above implementation, we still needed to talk about
 * the length of the list by explicitly calling the [length] function.
 *
 * An alternative way is to use dependent types to express the type
 * 'lists with a given length'. Traditionally, length-indexed lists are
 * called vectors.
 *)
Inductive vector (T : Type) : nat -> Type :=
| Vnil : vector T 0
| Vcons : forall n, T -> vector T n -> vector T (S n).

(** Let's define some more notation *)
Local Notation "[| |]" := (@Vnil _).
Local Notation "[| x |]" := (@Vcons _ 1 x Vnil).
Local Notation "[| x ; .. ; y |]" := (@Vcons _ _ x (.. (@Vcons _ _ y (@Vnil _)) ..)).

Check [| |].
Check [| 1 |].
Check [| 1 ; 2 ; 3 |].

(* Now we can get the element by a relatively simple modification
 * of [nth_fin].
 *)
Fixpoint vnth_fin {T : Type} {l : nat} (vs : vector T l)
: fin l -> T :=
  match vs in vector _ l return fin l -> T with
    | Vnil => @fin_0_any _
    | Vcons n' v vs' => fun n : fin (S n') =>
      match n in fin l return match l with
                                | 0 => unit
                                | S n' => (fin n' -> T) -> T
                              end
      with
        | FO _ => fun _ => v
        | FS _ n' => fun f => f n'
      end (vnth_fin vs')
  end.

(* ... and it works. *)
Eval compute in vnth_fin [| 1 ; 2 ; 3 |] (FS (FS FO)).

Eval compute in vnth_fin [| 1 ; 2 ; 3 |] (FS FO).

(* ASIDE:
 * In the above code we started with a simple data type, e.g. [nat] and [list],
 * and enriched it to express a particular property, e.g. boundedness in [fin]
 * and length in [vector].
 * This is the general idea of 'ornamentation' and is described by Connor
 * McBride in another proof assistant called Epigram (now integrated with Agda).
 * You can read more about it here:
 *     https://personal.cis.strath.ac.uk/conor.mcbride/pub/OAAO/Ornament.pdf
 * But fair warning, it is a pretty dense read.
 *)

(** Heterogeneous Lists **)
(*************************)

(* Sometimes you want to have a list that includes elements with different
 * data types. For example, if you have a programming language that includes
 * variables with both numbers and booleans, you will need your variable
 * environment to contain both numbers and boolean values.
 *
 * We can not do this with simple lists, but we can build a data type that
 * stores elements of different types.
 *
 * QUESTION: What can we index our data type by to solve this problem?
 *)
Inductive hlist : list Type -> Type :=
| Hnil : hlist nil
| Hcons : forall {T} {TS}, T -> hlist TS -> hlist (T :: TS).

(* An alternative implementation of this data type is as a function
 *)
Fixpoint hlist' (TS : list Type) : Type :=
  match TS with
    | nil => unit
    | T :: TS' => prod T (hlist' TS')
  end.

Eval compute in fun T : Type => hlist [ T ; T ; T ].
Eval compute in fun T : Type => hlist' [ T ; T ; T ].

(* QUESTIONs:
 * - What is the practical difference between these two types?
 * - Why might we prefer one or the other?
 *)

(* The implementation of head and tail are pretty easy for hlist' *)
Definition head' (T : Type) (TS : list Type) (h : hlist' (T :: TS)) : T :=
  fst h.

Definition tail' (T : Type) (TS : list Type) (h : hlist' (T :: TS)) : hlist' TS :=
  snd h.

(* Implementing these functions for [hlist], however, requires a
 * little bit of dependent pattern-matching-fu.
 *)
Definition head (T : Type) (TS : list Type) (h : hlist (T :: TS)) : T :=
  match h in hlist ts return match ts with
                               | nil => unit
                               | T :: _ => T
                             end
  with
    | Hnil => tt
    | Hcons _ _ v _ => v
  end.

Definition tail (T : Type) (TS : list Type) (h : hlist (T :: TS)) : hlist TS :=
  match h in hlist ts return match ts with
                               | nil => unit
                               | _ :: TS => hlist TS
                             end
  with
    | Hnil => tt
    | Hcons _ _ _ hs => hs
  end.

(* It takes a little bit more work to describe the type of projecting an
 * arbitrary element from a heterogeneous list.
 * QUESTION: How can we do this?
 *)

(* One option is to use [fin] and [nth_fin]
 *)
Fixpoint hlist_nth' {TS : list Type} (hs : hlist TS)
: forall n : fin (length TS), nth_fin TS n :=
  match hs in hlist TS return forall n : fin (length TS), nth_fin TS n with
    | Hnil => fun f => fin_0_any _ f
    | Hcons T' TS' x hs => fun f : fin (length (T' :: TS')) =>
                             match f as f' in fin X
                                   return match X as X return fin X -> Type with
                                            | 0 => fun _ => unit
                                            | S n' => fun f' : fin (S n') =>
                                                        forall T : fin n' -> Type,
                                                          (forall n0 : fin n', T n0) ->
                                                          match
                                                            f' in (fin n0)
                                                            return match n0 with
                                                                     | 0 => Type
                                                                     | S x0 => (fin x0 -> Type) -> Type
                                                                   end
                                                          with
                                                            | FO n0 => fun _ : fin n0 -> Type => T'
                                                            | FS n0 f0 => fun z : fin n0 -> Type => z f0
                                                          end T
                                          end f'
                             with
                               | FO _ => fun _ _ => x
                               | FS _ f => fun _ x => x f
                             end _ (hlist_nth' hs)
  end.

(* That one turns out to be a little bit more complicated than
 * is reasonable to do, though kudos to you if you come up with
 * an axiom-free solution.
 *
 * The key difficulty in the previous proof is that we have to reason
 * about [length], which has great computational properties, but
 * bad matching properties. It turns out that we can dramatically
 * simplify the function by enriching [fin] with a little bit of extra
 * information.
 *)
Inductive mem {T} (t : T) : list T -> Type :=
| MO : forall ts, mem t (t :: ts)
| MS : forall t' ts, mem t ts -> mem t (t' :: ts).

(* Conveniently (but actually by design), this type is indexed by the
 * same thing as [hlist]. Which drastically simplifies our lives.
 *
 * This type not only states that the 'index' is within bounds, but
 * also states what the precise value at that index is. What is the
 * benefit of that? We do not have to reason about the [nth_fin]
 * function anymore!
 *
 * With this in mind, let's take another crack at hlist_nth.
 *)
Fixpoint hlist_nth {TS : list Type} {T} (hs : hlist TS)
: mem T TS -> T :=
  match hs in hlist TS return mem T TS -> T with
    | Hnil =>
      fun x => match x in mem _ Z return match Z with
                                           | nil => T
                                           | _ :: _ => unit
                                         end
               with
                 | MO _ => tt
                 | MS _ _ _ => tt
               end
    | Hcons T' TS' x hs =>
      fun m => match m in mem _ Z
                     return match Z with
                              | nil => T
                              | x :: y => x -> (mem T y -> T) -> T
                            end
               with
                 | MO _ => fun x _ => x
                 | MS _ _ m' => fun _ f => f m'
               end x (@hlist_nth TS' T hs)
  end.

(* Here, the pattern is apparent, make the recursive call
 * outside of the match and pass the values in so they are
 * refined outside-in in the dependent match.
 *)

(** A Multi-sorted Language **)
(*****************************)

(* Using heterogeneous lists we can construct the type of
 * environments for programs with multiple types.
 *
 * Let's take a look at a simplely typed language that
 * uses dependent types to track a multi-sorted environment.
 *)
Inductive expr : list Type -> Type -> Type :=
  (* Constants of any type *)
| Const : forall T ts, T -> expr ts T
  (* Conditional expressions *)
| If : forall T ts, expr ts bool -> expr ts T -> expr ts T -> expr ts T
  (* Variables are references into the environment *)
| Var : forall T ts, mem T ts -> expr ts T
  (* LetIn extends the type environment used for the [in] clause
   * using the the type of [let]
   *)
| LetIn : forall T U ts, expr ts T -> expr (T :: ts) U -> expr ts U
  (* Function application *)
| App : forall T U ts, expr ts (T -> U) -> expr ts T -> expr ts U
  (* Function construction *)
| Lam : forall T U ts, expr (T :: ts) U -> expr ts (T -> U).

(* With our knowledge about dependent types, we can fairly easily
 * write an interpreter for the above language.
 *
 * Note that since the syntax is guaranteed to be well-typed, our
 * denotation function can be total.
 *)
Fixpoint exprD {ts : list Type} {t : Type} (e : expr ts t) : hlist ts -> t :=
  match e in expr ts t return hlist ts -> t with
    | Const _ _ x => fun _ => x
    | If _ _ test tr fa => fun g => if exprD test g then exprD tr g else exprD fa g
    | Var _ _ v => fun g => hlist_nth g v
    | LetIn _ _ _ e i => fun g => let x := exprD e g in
                                  exprD i (Hcons x g)
    | App _ _ _ f x => fun g => (exprD f g) (exprD x g)
    | Lam _ _ _ f => fun g => fun x => exprD f (Hcons x g)
  end.

(* Unfortunately, there are not a lot of other functions that we
 * can write to manipulate our syntax. For example, we can't even
 * write a function to decide equality of [expr]s.
 *
 * The problem is that our functions can not inspect the [Type]s
 * that are embedded inside of expressions.
 *)

(** Computational Reflection **)
(******************************)

(* There are techniques to solving this problem, some of which I
 * use in my thesis. With a representation that is completely
 * computational we can do a lot of interesting things, for
 * example extensible computational reflection, see:
 *    https://github.com/gmalecha/mirror-core
 * or
 *    http://www.people.fas.harvard.edu/~gmalecha/pub/ccr-itp14.pdf
 *
 * The basic idea is the following, let's say that we want to
 * reason about the [Even]ness of natural numbers.
 *)
Inductive Even : nat -> Prop :=
| E0 : Even 0
| ES : forall n, Odd n -> Even (S n)
with Odd : nat -> Prop :=
| OS : forall n, Even n -> Odd (S n).

(* Now if we have a constant that we want to prove is [Even] (or [Odd])
 * we can simply use the constructors.
 *)
Lemma Even_4 : Even 4.
Proof. repeat constructor. Qed.

Lemma Odd_5 : Odd 5.
Proof. repeat constructor. Qed.

(* But if we get a big number then we end up with a big proof.
 *)
Lemma Even_big : Even 1024.
Proof. Time repeat constructor. Time Qed.

(* But this is a pretty easy problem to solve by computation.
 * Let's see if we can do something a little bit more efficient.
 *)
Fixpoint even_or_odd (n : nat) : {Even n} + {Odd n}.
destruct n.
left. constructor.
destruct (even_or_odd n). right. constructor. auto.
left. constructor. auto.
Defined.

Print even_or_odd.
(* Now we can use computation to find the proof for us.
 *)

Lemma Even_big' : Even 1024.
Proof.
match even_or_odd n with
  | left _ => Even n
  | right _ => True
end : Prop
  Time refine (let n := 1024 in
               match even_or_odd n (*as X in { _ } + { _ }
                     return match X with
                              | left _ => Even n
                              | right _ => True
                            end *)
               with
                 | left pf => pf
                 | right _ => I
               end : match even_or_odd n with
                       | left _ => Even n
                       | right _ => True
                     end).
Time Qed.

(* But things are still pretty slow. Note that the [refine] is the
 * slow part, checking the proof is very fast.
 *
 * But, with the appropriate abstraction, we can make things pretty fast.
 *)
Theorem Even_by_refl : forall n,
                             true = match even_or_odd n with
                                      | left _ => true
                                      | right _ => false
                                    end ->
                             Even n.
Proof.
  intro n.
  refine (match even_or_odd n as X
                return true = match X with
                                | left _ => true
                                | right _ => false
                              end -> Even n
          with
            | left pf => fun X => pf
            | right _ => fun X => _
          end).
  discriminate.
Show Proof.
Defined.

Lemma Even_big'' : Even 1024.
Proof.
  Time (apply (Even_by_refl 1024); vm_compute; reflexivity).
Time Defined.
(* Here, [vm_compute] is running our Coq-code more efficiently
 * using some compilation techniques.
 *)

(* What does the proof look like?
 *)
Print Even_big''.
(* hmmm... that doesn't look like it is made up of [EO], [ES], and [OS].
 * But it turns out that it is.
 *)
Eval vm_compute in Even_big''.


(* It turns out, however, that we can do even better. Can you
 * spot where the inefficiency of [even_or_odd] comes from?
 * Hint: Do we ever construct something that we don't need?
 *)

(* If we avoid constructing the proof object, then we can
 * make things go even faster. Let's take a look.
 *
 * The computational part of the type [sumbool] (represented
 * with the [{ _ } + { _ }] notation) is just a bool. So,
 * we'll just compute that.
 *)
Fixpoint even_or_odd_nd (n : nat) : bool :=
  match n with
    | 0 => true
    | S n' => negb (even_or_odd_nd n')
  end.

(* Now, we have to separately prove the procedure sound.
 * The proof requires a stronger inductive hypothesis.
 *)
Lemma even_or_odd_nd_sound
: forall n,
    match even_or_odd_nd n with
      | true => Even n
      | false => Odd n
    end.
Proof.
  induction n; simpl; intros; try constructor; auto.
  destruct (even_or_odd_nd n); simpl; constructor; auto.
Defined.

Theorem Even_by_refl_nd : forall n, even_or_odd_nd n = true -> Even n.
Proof.
  intros. specialize (even_or_odd_nd_sound n).
  rewrite H. exact (fun x => x).
Defined.

(* Now how do we do?
 *)
Lemma Even_big''' : Even 1024.
Proof.
  Time (apply (Even_by_refl 1024); vm_compute; reflexivity).
Time Defined.
(* Just a little bit better.
 * The more computation we have, the better an improvement we get.
 *)

Lemma Even_bigger : Even 4092.
Proof.
(*  Time (apply (Even_by_refl 4092); vm_compute; reflexivity). *)
(* vs *)
  Time (apply (Even_by_refl_nd 4092); vm_compute; reflexivity).
Time Defined.

(* If you're interested in computational reflection, email me.
 * gmalecha@cs.harvard.edu
 *)
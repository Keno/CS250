(* Comments in Coq are as in Ocaml and SML:  they start with a left-paren 
   and asterisk, and are closed with an asterisk and right-paren. *)

Require Import Arith.

(* [Require Import Arith.] is a top-level command that tells Coq to import
   the definitions from the [Arith] library (arithmetic) and to make the
   definitions available at the top-level.  All top-level commands end
   with a period.
*)


Definition four : nat := 4.
(* A top-level definition begins with the keyword "Definition", followed
   by an identifier (in this case "four") that we want to use, a colon,
   a type, ":=", and then an expression followed by a period.  
   Here the type of the number 4 is [nat] which stands for natural number.  *)

Definition four' := 2 + 2.
(* You can leave off the type information and Coq can often infer it.  
   But it can't always infer types, and it's good documentation to put
   the types on complicated definitions. *)

Eval compute in four'.
(* [Eval compute in <exp>.] lets you evaluate an expression to the 
   resulting value and type. *)

Check four'.
(* [Check <exp>] lets you check the type of an expression. *)

Definition four'' := (6 - 4) * 2.

Check four''.
Eval compute in four''.

Definition inc(x:nat) : nat := x + 1.
(* To define a function, we just make a parameterized definition.  The
   parameters. *)

Check inc.
Eval compute in inc.
Eval compute in inc four.

Definition inc' x := x + 1.
(* As in Ocaml, we can leave off the types and Coq can usually infer them. *)

Check inc'.
Eval compute in inc' four.

Definition inc'' := fun (x:nat) => x + 1.
(* Parameterized definitions are just short-hand for a regular definition
   using a lambda expression. *)

Check inc''.
Eval compute in inc'' four.


Definition add x y := x + y.
Definition add' := fun x => fun y => x + y.

Check add.
Check add'.
Eval compute in add 5 4.
Eval compute in add' 5 4.

Inductive bool : Type := 
| true : bool 
| false : bool.
(* An inductive definition is just like an Ocaml datatype definition,
   though the syntax is a little different.  Here, we are defining
   a new [Type] called [bool] with constructors [true] and [false].

   Notice that when we evaluate this definition, Coq says that not
   only is [bool] defined, but also [bool_rect], [bool_ind], and 
   [bool_rec].  We'll discuss those later on when we start talking
   about proving things.
*)
Check true.
Check false.

Definition negb (b:bool) : bool := 
  match b with 
    | true => false
    | false => true
  end.
(* The definition above shows how we use pattern-matching to tear apart
   an inductive type, in this case a [bool].  The syntax is similar to 
   Ocaml except that we use "=>" for the guard instead of "->" and we
   have to put an "end" to terminate the "match". *)

Check negb.
Eval compute in negb true.
Eval compute in negb false.

Definition andb (b1 b2:bool) : bool := 
  match b1 with 
    | true => b2
    | false => false
  end.

Eval compute in andb true false.
Eval compute in andb true true.

Definition orb b1 b2 := 
  match b1 with
    | true => true
    | _ => b2
  end.

Eval compute in orb true false.
Eval compute in orb true true.

(* The [Arith] module defines this [nat] type already.  It is a way to
   represent the natural numbers, with a base case of zero, "0" and 
   successor constructor [S]. *)

Inductive nat : Type := 
  | O : nat
  | S : nat -> nat.
*)

Print nat.

Check O.
Check 0.   (* the numeral 0 is just notation for the constructor O *)
Check S.
Check S 0. (* numerals such as 1 are short-hand for S 0. *)
Check S (S (S 0)).

Definition is_zero (n:nat) : bool := 
  match n with 
    | 0 => true
    | S _ => false
  end.

Fixpoint add'' (n m:nat) : nat := 
  match n with 
    | 0 => m
    | S n' => S (add'' n' m)
  end.
(* We construct recursive functions by using the keyword "Fixpoint". *)

Eval compute in add'' 4 3.

Definition add3 :=
  fix local_add (n m:nat) : nat := 
  match n with 
    | 0 => m
    | S n' => S (local_add n' m)
  end.
(* Alternatively, we can use a "fix" expression which builds a recursive
   functions, similar to the way "fun" builds a non-recursive function.
*)

Eval compute in add3 4 3.

(* Pairs *)
Definition p1 : nat * nat := (3,4).  (* pair of nats *)
Definition p2 : nat * bool := (3, true).  (* nat and bool *)
Definition p3 : nat * bool * nat := (3,true,2).

Eval compute in add3 (fst p1) (snd p1).  
(* [fst] extracts the first component of a pair, and [snd]
   extracts the second component. *)

Eval compute in fst p3.
Eval compute in snd p3.
(* Notice that [(3,true,2)] is really short-hand for [((3,true),2)]. 
   and [nat * bool * nat] is short for [(nat * bool) * nat]. *)

(* Options *)
Definition opt1 : option nat := None.
Definition opt2 : option nat := Some 4.
(* An [option t] is either [None] or [Some] applied to a value of type [t]. 
   Notice that unlike Ocaml, we write [option nat] instead of [nat option].
*)

Fixpoint subtract (m n:nat) : option nat := 
  match m, n with 
    | _, 0 => Some m
    | 0, S _ => None
    | S m', S n' => subtract m' n'
  end.
Eval compute in subtract 5 2.
Eval compute in subtract 2 5.

Definition subt (m n:nat) : nat := 
  match subtract m n with 
    | None => 0
    | Some i => i
  end.
Eval compute in subt 5 2.
Eval compute in subt 2 5.

(* Sums *)
Definition s1 : nat + bool := inl 3.
Definition s2 : nat + bool := inr true.
(* We build something of type [t1 + t2] by using either [inl] or 
   [inr].  It's important to provide Coq enough type information
   that it can figure out what the other type is. *)

Definition add_nat_or_bool (s1 s2: nat + bool) : nat + bool := 
  match s1, s2 with 
    | inl n1, inl n2 => inl (n1 + n2)
    | inr b1, inr b2 => inr (orb b1 b2)
    | _, _ => inr false
  end.

(* Lists *)
Require Import List.
Definition l1 : list nat := nil.
Definition l2 : list nat := 3::2::1::nil.
Definition l3 : list bool := true::false::nil.
Definition l4 : list (nat + bool) := (inl 3)::(inr true)::nil.

Fixpoint append (l1 l2:list nat) : list nat := 
  match l1 with 
    | nil => l2
    | h::t => h::(append t l2)
  end.

Eval compute in append l2 l2.

Fixpoint add_list (l1 l2:list nat) : option (list nat) := 
  match l1, l2 with 
    | nil, nil => Some nil
    | n1::l1, n2::l2 => 
      match add_list l1 l2 with
        | None => None
        | Some l => Some ((n1+n2)::l)
      end
    | _, _ => None
  end.

Eval compute in add_list l2 l2.

(* Polymorphism *)

Fixpoint generic_append (A:Type) (l1 l2: list A) : list A := 
  match l1 with 
    | nil => l2
    | h::t => h::(generic_append A t l2)
  end.
(* Unlike Ocaml, we make type parameters explicit in Coq.  Here, 
   we've defined a generic append function, which abstracts over
   a type [A].  Notice that the types of the arguments [l1] and
   [l2] depend upon [A], as does the result type.  Notice also
  that when we call this function, we must provide an actual
  type for the instantiation of [A].
*)

Eval compute in generic_append bool l3 l3.
Eval compute in generic_append nat l1 l2.
Eval compute in generic_append _ l3 l3.  
(* Coq can usually figure out what the types are, and we can
   leave out the type by just putting an underscore there 
   instead.  But there are cases where it can't figure it
   out (e.g., generic_append _ nil nil).
*)

Fixpoint generic_append' {A:Type} (l1 l2:list A) : list A := 
  match l1 with 
    | nil => l2
    | h::t => h::(generic_append' t l2)
  end.
(* The curly braces tell Coq to make an argument implicit.  That
   means it's up to Coq to fill in the argument for you.  Notice
   that in the recursive call, we didn't have to specify the type. *)

Eval compute in generic_append' l1 l1.
Eval compute in generic_append' l2 l2.
Eval compute in generic_append' nil nil.

(* This won't work though:
Definition foo := generic_append' nil nil.
   We can fix it by either giving enough information in the context
   or by using "@" to override the implicit arguments:
*)
Definition foo : list nat := generic_append' nil nil.
Definition foo1 := @generic_append' nat nil nil.



(* KENO FISCHER *)

(* CS250 Problem Set 0:  Basic Functional Programming in Coq 

Due:  Tuesday 9/9 at Midnight

The goal of this problem set is to just get you comfortable
with the basic syntax of Coq, using ProofGeneral or the CoqIDE
in an interactive fashion, and to remember some basic functional
programming.  

Feel free to collaborate with each other, but make sure to do
the exercises yourself so you start to become familiar with the
syntax and the environment.  If you get stuck, as questions
on Piazza, or come see me (MD151) or one of the students in MD309
to get un-stuck. 

Complete each of the definitions below, and add some test cases
(using [Eval compute in <exp>.] to make sure they are working
properly.

Make sure to push your solution back to your cloned repository,
but only after you've added your name!  
*)
Require Import Arith.
Require Import List.
Import ListNotations.


(* 0. Write a function [length] to compute the length of list.
      [length : forall {A:Type}, list A -> nat]
*)
Fixpoint length {A:Type} (l:list A) : nat :=
  match l with
    | [] => 0
    | (_::tl) => S (length tl)
  end.

(* 1. Write a function [rev] that reverses a list.
      [rev : forall {A:Type}, list A -> list A]
*)

Fixpoint rev {A:Type} (l:list A) : list A :=
  match l with
    | [] => []
    | (hd::tl) => (rev tl) ++ [hd]
  end.

(* 2. Write a function [ith] that returns the ith element of a list,
      if the list has enough elements, and otherwise returns None.
      We are working zero-based, so for instance, 
      [ith 2 (1::2::3::4::nil)] should return [Some 3], whereas
      [ith 4 (1::2::3::4::nil)] should return None.

      [ith : forall {A:type}, nat -> list A -> option A]
*)

Fixpoint ith {A:Type} (n:nat) (l:list A) : option A :=
  match n with
    | 0 => find (fun (x:A) => true) l
    | S k => (ith k (tail l))
  end.

(* 3. Write a generic function [comp] to compose two functions.
      [comp : forall {A B C:Type}, (A -> B) -> (B -> C) -> (A -> C)]
*)
Definition comp {A B C: Type} (f:A->B) (g:B->C) : (A->C) :=
  (fun (x:A) => (g (f x))).

(* 4. Write a function [sum] that adds up all of the [nat]s in a list.
      [sum : list nat -> nat]
*)
Fixpoint sum (l: list nat) : nat :=
  match l with
    | [] => 0
    | hd::tl => hd + (sum tl)
  end.

(* 5. Write a function that [map] that maps a function over the 
      elements in a list, producing a new list.
      [map : forall {A B:Type}, (A -> B) -> list A -> list B]
*)
Fixpoint map {A B:Type} (f:A->B) (l:list A) : list B :=
  match l with
    | [] => []
    | hd::tl => [(f hd)] ++ (map f tl)
  end.


(* 6. Write a generic "fold-right" for a list such that, for instance.
      [fold (fun x y => x + y) 0 (1::2::3::nil)] evaluates to [6].  
      [fold : forall {A B:Type}, (A -> B -> B) -> B -> list A -> B] 
*)
Fixpoint fold {A B:Type} (f:(A->B->B)) (acc:B) (l:list A) : B :=
  match l with
    (* Not part of the recursion but for the empty case *)
    | [] => acc
    | (hd::tl) => (f hd (fold f acc tl))
  end.


(* 7. Write a function add_pairs that takes a list of pairs of nats and 
      returns the list of the corresponding sums.  For instance,
      [add_pairs ((1,2)::(3,4)::nil)] should return [3::7::nil].
      [add_pairs : list (nat * nat) -> list nat] 
*)
Definition add_pair (l:list (nat * nat)) : list nat :=
  (map (fun (p:(nat*nat)) => (fst p)+(snd p)) l).

(* 8. Given the following definition for trees: *)
Inductive tree (A:Type) : Type := 
| Leaf : tree A
| Node : tree A -> A -> tree A -> tree A.

Implicit Arguments Leaf [A].  (* Ask Coq to synthesis the type argument to Leaf *)
Implicit Arguments Node [A].  (* Ditto for Node *)

(* 9. Write a function which flattens the tree into a list.
      For instance, flatten on the tree:

                   3
                 /   \
                1     7
              /  \   /  \
             o    o o    o

   should yield [1::3::7::nil].
   [flatten : forall {A:Type}, tree A -> list A]
*)
Fixpoint flatten {A:Type} (t:tree A) : list A :=
  match t with
    | Leaf => []
    | (Node t1 x t2) => (flatten t1) ++ [x] ++ (flatten t2)
  end.

Inductive order : Type := 
| Less 
| Equal
| Greater.

(* 11. Write a function which when given two numbers n and m,
       returns [Less] if n < m, [Equal] if n = m, and otherwise
       returns [Greater].  
       [nat_cmp : nat -> nat -> order] *)

Fixpoint nat_cmp (a:nat) (b:nat) : order :=
  match a,b with
    | 0, S k => Less
    | 0, 0 => Equal
    | S k, 0 => Greater
    | S x, S y => (nat_cmp x y)
  end.

(* 12. Write a function that determines whether a [tree nat] is
       a valid search tree in the sense that for a given node
       with value [n], all elements in the left sub-tree should 
       be less than [n] and all elements in the right sub-tree
       should be greater than [n].  
       [search_tree : tree nat -> bool]
*)

Fixpoint search_tree (t: tree nat) : bool :=
  match t with
    | Leaf => true
    | (Node t1 x t2) => (andb
        (andb match (nat_cmp x (fold max 0 (flatten t1 ))) with
        | Less => true
        | _ => false
      end (search_tree t1)) 
        (andb match (nat_cmp x (fold min (S x) (flatten t2))) with
        | Greater => true
        | _ => false
      end (search_tree t2)))
  end.

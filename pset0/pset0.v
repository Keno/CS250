(* Jao-ke Chin-Lee with Keno Fischer *)

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


(* 0. Write a function [length] to compute the length of list.
      [length : forall {A:Type}, list A -> nat]
*)
Fixpoint length {A:Type} (l:list A) : nat :=
  match l with
    | nil => 0
    | _::rest => 1 + length rest
  end.

Definition l1 : list nat := nil.
Definition l2 : list nat := 1::nil.
Definition l3 : list nat := 1::2::3::nil.
Eval compute in length l1.
Eval compute in length l2.
Eval compute in length l3.

(* 1. Write a function [rev] that reverses a list.
      [rev : forall {A:Type}, list A -> list A]
*)
Fixpoint rev {A:Type} (l:list A) : list A :=
  match l with
    | nil => nil
    | h::t => (rev t) ++ (h::nil)
  end.

Eval compute in rev l1.
Eval compute in rev l2.
Eval compute in rev l3.

(* 2. Write a function [ith] that returns the ith element of a list,
      if the list has enough elements, and otherwise returns None.
      We are working zero-based, so for instance, 
      [ith 2 (1::2::3::4::nil)] should return [Some 3], whereas
      [ith 4 (1::2::3::4::nil)] should return None.

      [ith : forall {A:type}, nat -> list A -> option A]
*)
Fixpoint ith {A:Type} (i:nat) (l:list A) : option A :=
  match i, l with
    | _, nil => None
    | 0, h::_ => Some h
    | S j, _::t => ith j t
  end.

Eval compute in ith 0 l1.
Eval compute in ith 1 l1.
Eval compute in ith 3 l1.
Eval compute in ith 0 l2.
Eval compute in ith 1 l2.
Eval compute in ith 0 l3.
Eval compute in ith 1 l3.
Eval compute in ith 3 l3.

(* 3. Write a generic function [comp] to compose two functions.
      [comp : forall {A B C:Type}, (A -> B) -> (B -> C) -> (A -> C)]
*)
Definition comp {A B C:Type} (f1:A->B) (f2:B->C) : A->C :=
  fun (x:A) => f2 (f1 x).

Eval compute in (comp rev (ith 0)) l1.
Eval compute in (comp rev (ith 0)) l2.
Eval compute in (comp rev (ith 0)) l3.
Eval compute in (comp rev (ith 2)) l3.
Eval compute in (comp rev (ith 3)) l3.

(* 4. Write a function [sum] that adds up all of the [nat]s in a list.
      [sum : list nat -> nat]
*)
Fixpoint sum (l:list nat) : nat :=
  match l with
    | nil => 0
    | h::t => h + sum t
  end.

Eval compute in sum l1.
Eval compute in sum l2.
Eval compute in sum l3.

(* 5. Write a function that [map] that maps a function over the 
      elements in a list, producing a new list.
      [map : forall {A B:Type}, (A -> B) -> list A -> list B]
*)
Fixpoint map {A B:Type} (f:A->B) (l:list A) : list B :=
  match l with
    | nil => nil
    | h::t => (f h)::(map f t)
  end.

Definition nested : list (list nat) := (1::2::nil)::(0::3::4::nil)::(5::nil)::nil.
Eval compute in map sum nested.

(* 6. Write a generic "fold-right" for a list such that, for instance.
      [fold (fun x y => x + y) 0 (1::2::3::nil)] evaluates to [6].  
      [fold : forall {A B:Type}, (A -> B -> B) -> B -> list A -> B] 
*)
Fixpoint fold {A B:Type} (f:A->B->B) (base:B) (l:list A) : B :=
  match l with
    | nil => base
    | h::t => f h (fold f base t)
  end.

Definition sum' (x y:nat) : nat := x + y.
Eval compute in fold sum' 1 l1.
Eval compute in fold sum' 1 l2.
Eval compute in fold sum' 1 l3.
Eval compute in fold (fun x y => x - y) 3 (10::5::nil). (* expect 10 - (5 - 3) = 8 *)

(* 7. Write a function add_pairs that takes a list of pairs of nats and 
      returns the list of the corresponding sums.  For instance,
      [add_pairs ((1,2)::(3,4)::nil)] should return [3::7::nil].
      [add_pairs : list (nat * nat) -> list nat] 
*)
Definition add_pairs (l:list (nat * nat)) : list nat :=
  map (fun (x:(nat * nat)) => fst x + snd x) l.

Eval compute in add_pairs nil.
Eval compute in add_pairs ((1,2)::nil).
Eval compute in add_pairs ((1,2)::(3,4)::(5,6)::nil).

(* 8. Given the following definition for trees: *)
Inductive tree {A:Type} : Type := 
| Leaf : tree
| Node : tree -> A -> tree -> tree.

Definition leaf : tree := @Leaf nat.
Definition tree1 : tree := Node (Node Leaf 1 Leaf) 3 (Node Leaf 7 Leaf).
Definition tree2 : tree := Node Leaf 3 (Node (Node Leaf 5 Leaf) 7 (Node Leaf 9 Leaf)).
Definition tree3 : tree := Node (Node (Node Leaf 1 Leaf) 3 (Node Leaf 4 Leaf)) 5 Leaf.
Definition tree1' : tree := Node (Node Leaf 5 Leaf) 3 (Node Leaf 7 Leaf).
Definition tree2' : tree := Node Leaf 5 (Node (Node Leaf 5 Leaf) 7 (Node Leaf 9 Leaf)).
Definition tree3' : tree := Node (Node (Node Leaf 5 Leaf) 3 (Node Leaf 4 Leaf)) 5 Leaf.

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
Fixpoint flatten {A:Type} (t:tree) : list A :=
  match t with
    | Leaf => nil
    | Node l v r => (flatten l) ++ (v::nil) ++ (flatten r)
  end.

Eval compute in flatten leaf.
Eval compute in flatten tree1.
Eval compute in flatten tree2.
Eval compute in flatten tree3.
Eval compute in flatten tree1'.
Eval compute in flatten tree2'.
Eval compute in flatten tree3'.

Inductive order : Type := 
| Less 
| Equal
| Greater.

(* 11. Write a function which when given two numbers n and m,
       returns [Less] if n < m, [Equal] if n = m, and otherwise
       returns [Greater].  
       [nat_cmp : nat -> nat -> order]
*)
Fixpoint nat_cmp (n m:nat) : order :=
  match n,m with
    | 0,0 => Equal
    | _,0 => Greater
    | 0,_ => Less
    | S n', S m' => nat_cmp n' m'
  end.

Eval compute in nat_cmp 0 0.
Eval compute in nat_cmp 0 1.
Eval compute in nat_cmp 1 0.
Eval compute in nat_cmp 1 1.
Eval compute in nat_cmp 1 2.
Eval compute in nat_cmp 2 1.
Eval compute in nat_cmp 10 10.
Eval compute in nat_cmp 10 5.
Eval compute in nat_cmp 5 10.

(* 12. Write a function that determines whether a [tree nat] is
       a valid search tree in the sense that for a given node
       with value [n], all elements in the left sub-tree should 
       be less than [n] and all elements in the right sub-tree
       should be greater than [n].  
       [search_tree : tree nat -> bool]
*)
Definition search_tree (t:tree) : bool :=
  (fix is_monotone (l:list nat) : bool :=
    match l with
      | nil => true
      | h::t => (* incidentally why does coq believe the structure decreases here but not below? *)
        match t with
          | nil => true
          | h'::_ =>
            match nat_cmp h h' with
              | Equal | Greater => false
              | Less => is_monotone t
            end
         end
    end) (flatten t).

(* expect true *)
Eval compute in search_tree leaf.
Eval compute in search_tree tree1.
Eval compute in search_tree tree2.
Eval compute in search_tree tree3.
(* expect false *)
Eval compute in search_tree tree1'.
Eval compute in search_tree tree2'.
Eval compute in search_tree tree3'.

(* alternatively, we can just fold, keeping track of the last value we looked at (unless
   it was the first call) and comparing it to the present value, foldr'ing, which is cute
   although it does go through the whole list whether it needs to or not
*)
Notation "n < m" := match nat_cmp n m with Less => true | _ => false end.
Definition track_increasing (prev:nat) (info:bool*nat*bool) : bool*nat*bool :=
  let '(init, cur, is_inc) := info in
  (false, prev, orb (andb is_inc (prev < cur)) init).
Definition search_tree' (t:tree) : bool :=
  snd (fold track_increasing (true, 0, true) (flatten t)).

(* expect true *)
Eval compute in search_tree' leaf.
Eval compute in search_tree' tree1.
Eval compute in search_tree' tree2.
Eval compute in search_tree' tree3.
(* expect false *)
Eval compute in search_tree' tree1'.
Eval compute in search_tree' tree2'.
Eval compute in search_tree' tree3'.


(*
(* Why does this not work? *)
Definition search_tree (t:tree nat) : bool :=
  (fix ord_list (l:list nat) : bool :=
    match l with
      | nil | _::nil => true
      | x1::x2::t => (
        match nat_cmp x1 x2 with
          | Equal | Greater => false
          | Less => ord_list (x2::t) (* this seems to be the problem; how can we specify that indeed it decreases? *)
        end)
    end
  ) (flatten t).*)

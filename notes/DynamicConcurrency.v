Require Import PArith Bool List String CpdtTactics.

(* Inductive positive : Set := 
   | xH : positive             (* [xH] = 1             *)
   | xO : positive -> positive (* [xO p] = [p] * 2     *)
   | xI : positive -> positive (* [xI p] = [p] * 2 + 1 *)


              __________ xH _________
             /                       \
       (xO xH)                      (xI xH)
       /      \                   /       \
 xO (xO xH)   xI (xO xH)    xO (xI xH)   xI (xI xH)

*)

Definition namespace := positive.
Definition left_tree (p:positive) := xO p.
Definition right_tree (p:positive) := xI p.
Definition tid := positive.

Definition msg := string.

Inductive com : Type -> Type := 
| Ret : forall {A}, A -> com A
| Bind : forall {A B}, com A -> (A -> com B) -> com B
| Send : tid -> msg -> com unit
| Rcv : com string
| Fork : com unit -> com tid.

Inductive system := 
| Empty : system
| Thread : tid -> namespace -> com unit -> system
| Par : system -> system -> system.

Infix "|+|" := Par (right associativity, at level 80).

Reserved Notation "s1 == s2" (at level 84).

Inductive equiv : system -> system -> Prop := 
| system_refl : forall s, s == s
| system_trans : forall s1 s2 s3, s1 == s2 -> s2 == s3 -> s1 == s3
| system_comm : forall s1 s2, s1 |+| s2 == s2 |+| s1
| system_assoc : forall s1 s2 s3,
                   s1 |+| (s2 |+| s3) == (s1 |+| s2) |+| s3
| system_plus_empty : forall s, equiv (s |+| Empty) s
| system_cong : forall s1 s2 s3 s4, 
                  s1 == s3 -> s2 == s4 -> s1 |+| s2 == s3 |+| s4
where "s1 == s2" := (equiv s1 s2).

Inductive action : Type := 
| Eps_a : action
| Send_a : tid -> msg -> action
| Rcv_a : msg -> action
| Fork_a : tid -> com unit -> action.

Reserved Notation "c1 -: a :-> c2" (at level 84).

Inductive step_thread : forall {A}, com A -> action -> com A -> Prop := 
| step_Ret_Bind : 
    forall {A B} (x:A) (f:A -> com B), 
      (Bind (Ret x) f) -:Eps_a:-> (f x)
| step_Cong : 
    forall {A B} (c:com A) (a: action) (c':com A) (f: A -> com B),
      c -:a:-> c' -> Bind c f -:a:-> Bind c' f
| step_Send : 
    forall (t:tid) (m:msg), 
      Send t m -:Send_a t m:-> Ret tt
| step_Rcv : 
    forall (m:msg), 
      Rcv -:Rcv_a m:-> Ret m
| step_Fork : 
    forall (t:tid) (c:com unit), 
      Fork c -:Fork_a t c:-> Ret t
where "c1 -: a :-> c2" := (step_thread c1 a c2).

Reserved Notation "s1 ==> s2" (at level 84).

Inductive step_system : system -> system -> Prop := 
| system_Eps : 
    forall t n c1 c1', 
      c1 -:Eps_a:-> c1' -> 
      Thread t n c1 ==> Thread t n c1'
| system_SndRcv : 
    forall t1 n1 c1 c1' 
           t2 n2 c2 c2' m,
      c1 -: (Send_a t2 m) :-> c1' -> 
      c2 -: (Rcv_a m) :-> c2' -> 
      Thread t1 n1 c1 |+| Thread t2 n2 c2 ==>
      Thread t1 n1 c1' |+| Thread t2 n2 c2'
| system_Fork : 
    forall t n c child c', 
      c -: Fork_a (right_tree n) child :-> c' -> 
      Thread t n c ==> 
             Thread t (left_tree n) c' |+| 
             Thread (right_tree n) (right_tree n) child
| system_GC : 
    forall t n, 
      Thread t n (Ret tt) ==> Empty
| system_Cong : 
    forall s1 s1' s2,
      s1 ==> s1' -> s1 |+| s2 ==> s1' |+| s2
| system_Equiv : 
    forall s1 s2 s3 s4,
      s1 ==> s2 -> s1 == s3 -> s2 == s4 -> s3 ==> s4
where "s1 ==> s2" := (step_system s1 s2).




Class Monad(M:Type -> Type) := 
{
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.


(* As usual, we will use the more convenient notation for bind. *)
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
  (right associativity, at level 84, c1 at next level).
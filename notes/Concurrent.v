Require Import Arith Bool List String CpdtTactics.

Definition tid := nat.
Definition msg := string.

Inductive com : Type -> Type := 
| Ret : forall {A}, A -> com A
| Bind : forall {A B}, com A -> (A -> com B) -> com B
| Send : tid -> msg -> com unit
| Rcv : com string.

Inductive system := 
| Empty : system
| Thread : tid -> com unit -> system
| Par : system -> system -> system.

Infix "|+|" := Par (right associativity, at level 80).

Reserved Notation "s1 ~~ s2" (at level 84).

Inductive equiv : system -> system -> Prop := 
| system_refl : forall s, s ~~ s
| system_trans : forall s1 s2 s3, s1 ~~ s2 -> s2 ~~ s3 -> s1 ~~ s3
| system_comm : forall s1 s2, s1 |+| s2 ~~ s2 |+| s1
| system_assoc : forall s1 s2 s3,
                   s1 |+| (s2 |+| s3) ~~ (s1 |+| s2) |+| s3
| system_plus_empty : forall s, equiv (s |+| Empty) s
| system_cong : forall s1 s2 s3 s4, 
                  s1 ~~ s3 -> s2 ~~ s4 -> s1 |+| s2 ~~ s3 |+| s4
where "s1 ~~ s2" := (equiv s1 s2).

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
where "c1 -: a :-> c2" := (step_thread c1 a c2).

Reserved Notation "s1 ==> s2" (at level 84).

Inductive step_system : system -> system -> Prop := 
| system_Eps : 
    forall t c1 c1', 
      c1 -:Eps_a:-> c1' -> 
      Thread t c1 ==> Thread t c1'
| system_SndRcv : 
    forall t1 c1 c1' 
           t2 c2 c2' m,
      c1 -: (Send_a t2 m) :-> c1' -> 
      c2 -: (Rcv_a m) :-> c2' -> 
      Thread t1 c1 |+| Thread t2 c2 ==>
      Thread t1 c1' |+| Thread t2 c2'
| system_GC : 
    forall t, 
      Thread t (Ret tt) ==> Empty
| system_Cong : 
    forall s1 s1' s2,
      s1 ==> s1' -> s1 |+| s2 ==> s1' |+| s2
| system_Equiv : 
    forall s1 s2 s3 s4,
      s1 ==> s2 -> s1 ~~ s3 -> s2 ~~ s4 -> s3 ==> s4
where "s1 ==> s2" := (step_system s1 s2).

Class Monad(M:Type -> Type) := 
{
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.

Definition ready_queue := list (tid * (com unit))%type.

Definition M (A:Type) := tid -> (A -> com unit) -> ready_queue -> list (ready_queue).

Definition MReturn {A:Type} (x:A) : M A := 
  fun (t:tid) (k: A -> com unit) (q:ready_queue) => 
    ((t, k x)::q)::nil.

Definition MBind {A B:Type} (c:M A) (f:A -> M B) : M B := 
  fun (t:tid) (k: B -> com unit) (q:ready_queue) => 
    c t (fun (v:A) => Bind (Ret v) c)
  
Definition flatMap {A B:Type} (xs:list A) (f:A->list B) : list B := 
  fold_right (fun x a => (f x) ++ a) nil xs.

Instance mMonad : Monad M := 
{
  ret := fun {A:Type} (x:A) (t:tid) (k:A-> com unit)(r:ready_queue) => (x::nil) ; 
  bind := @flatMap
}.

Fixpoint step_thread_fn {A} (c:com A) : list (com A) := 
  match c with 
    | Ret v => 
    | Bind c f => 
  

(* As usual, we will use the more convenient notation for bind. *)
Notation "x <- c1 ; c2" := (bind c1 (fun x => c2)) 
  (right associativity, at level 84, c1 at next level).
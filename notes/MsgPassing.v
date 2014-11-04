Require Import Arith Bool List String CpdtTactics.

(* Thread IDs *)
Definition tid := nat.
(* Some notion of message *)
Definition msg := string.

(* Thread commands -- monadic style -- with support
   for sending a message to a thread, or for receiving
   a message.  So the only inter-thread communication
   is through this kind of message passing. 
*)
Inductive com : Type -> Type := 
| Ret : forall {A}, A -> com A
| Bind : forall {A B}, com A -> (A -> com B) -> com B
| Send : tid -> msg -> com unit
| Rcv : com string.

(* A system is a tree of threads, where a thread is a
   thread id and a command.   Conceptually, all of the
   threads are running in parallel.  
*)
Inductive system := 
| Empty : system
| Thread : tid -> com unit -> system
| Par : system -> system -> system.

Infix "|+|" := Par (right associativity, at level 80).

(* We really want to view the system as one where the
   structure of the "tree" doesn't matter (i.e., it's
   like a finite set.)  So we introduce a notion of 
   equivalence for systems where we say two systems
   are equivalent if we ignore the order of the threads.

   To ensure that this is an equivalence relation, we 
   also have rules for reflexivity, transitivity, etc. *)
Reserved Notation "s1 ~~ s2" (at level 84).

Inductive equiv : system -> system -> Prop := 
| system_refl : forall s, s ~~ s
| system_symm : forall s1 s2, s1 ~~ s2 -> s2 ~~ s1
| system_trans : forall s1 s2 s3, s1 ~~ s2 -> s2 ~~ s3 -> s1 ~~ s3
| system_comm : forall s1 s2, s1 |+| s2 ~~ s2 |+| s1
| system_assoc : forall s1 s2 s3,
                   s1 |+| (s2 |+| s3) ~~ (s1 |+| s2) |+| s3
| system_plus_empty : forall s, equiv (s |+| Empty) s
| system_cong : forall s1 s2 s3 s4, 
                  s1 ~~ s3 -> s2 ~~ s4 -> s1 |+| s2 ~~ s3 |+| s4
where "s1 ~~ s2" := (equiv s1 s2).

(* We're going to model the behavior of an individual thread
   as a series of actions that lead from one thread state to
   another thread state.  This definition of actions will be
   important for gluing together our individual threads into
   systems.  
*)
Inductive action : Type := 
| Eps_a : action (* an internal action with no communication *)
| Send_a : tid -> msg -> action
| Rcv_a : msg -> action.

(* A relation specifying how a thread can step and what action that
   step results in.  The action enacpsulates how the thread is 
   interacting with the rest of the environment.  Note that this is
   *not* a deterministic relation since we can step a Rcv to 
   Ret m for any message m!  The issue is that the environment can
   in some sense, non-deterministically choose to send us any message. *)
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

(* A relation specifying how a whole system steps. *)
Reserved Notation "s1 ==> s2" (at level 84).
Inductive step_system : system -> system -> Prop := 
| system_Eps : 
    (* A thread that does no communication can step *)
    forall t c1 c1', 
      c1 -:Eps_a:-> c1' -> 
      Thread t c1 ==> Thread t c1'
| system_SndRcv : 
    (* Two threads matching in their communication needs
       can step together.  Notice this is where we are
       cutting down what a Rcv and do.  *)
    forall t1 c1 c1' 
           t2 c2 c2' m,
      c1 -: (Send_a t2 m) :-> c1' -> 
      c2 -: (Rcv_a m) :-> c2' -> 
      Thread t1 c1 |+| Thread t2 c2 ==>
      Thread t1 c1' |+| Thread t2 c2'
| system_Cong : 
    (* A sub-system can step. *)
    forall s1 s1' s2,
      s1 ==> s1' -> 
      s1 |+| s2 ==> s1' |+| s2
| system_GC : 
    (* A thread that's done running can be turned into
       an empty system. *)
    forall t, 
      Thread t (Ret tt) ==> Empty
| system_Equiv : 
    (* If system s1 steps to system s2, and s1 is 
       equivalent to s3 and s2 is equivalent to s4,
       then s2 also steps to s4. *)
    forall s1 s2 s3 s4,
      s1 ==> s2 -> s1 ~~ s3 -> s2 ~~ s4 -> s3 ==> s4
where "s1 ==> s2" := (step_system s1 s2).

Class Monad(M:Type -> Type) := 
{
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.

(* As usual, we will use the more convenient notation for bind. *)
Notation "x <- c1 ; c2" := (bind c1 (fun x => c2)) 
  (right associativity, at level 84, c1 at next level).

Notation "[ x , y ] <-- c1 ; c2" := (bind c1 (fun x => match x with (x,y) => c2 end))
  (right associativity, at level 84, c1 at next level).

Definition set (A:Type) := list A.

Definition flatMap {A B:Type} (xs:set A) (f:A->set B) : set B := 
  fold_right (fun x a => (f x) ++ a) nil xs.

Instance setMonad : Monad set := { 
  ret := fun {A} (x:A) => x::nil ; 
  bind := @flatMap
}.

Definition Fail {A:Type} : set A := nil.

Inductive thread_state := 
| Terminated
| Sending : tid -> msg -> thread_state -> thread_state
| Receiving : (msg -> thread_state) -> thread_state.

Definition ready_queue := list (tid * thread_state)%type.

Fixpoint com_to_thread_state' {A} (c: com A) : (A -> thread_state) -> thread_state := 
  match c in com A return (A -> thread_state) -> thread_state with 
    | Ret A v => fun k => k v
    | Bind A B c f => fun k => com_to_thread_state' c (fun v => com_to_thread_state' (f v) k)
    | Send t m => fun k => Sending t m (k tt)
    | Rcv => fun k => Receiving k
  end.

Definition com_to_thread_state (c:com unit) := com_to_thread_state' c (fun _ => Terminated).

Fixpoint find_rcv_thread t (q:ready_queue) : set ((msg -> thread_state) * ready_queue) := 
  match q with 
    | nil => Fail
    | (t',ts)::rest => 
      if eq_nat_dec t t' then 
        match ts with 
          | Receiving k => ret (k, rest)
          | _ => Fail
        end
      else
        [k', q'] <-- find_rcv_thread t rest ; 
        ret (k', ((t',ts)::q'))
  end.

Definition step_thread_fn (q1:ready_queue) (t:tid) (ts:thread_state) (q2:ready_queue) : set ready_queue := 
  match ts with 
    | Terminated => ret (q1 ++ q1)
    | Receiving k => Fail
    | Sending t' m k => 
      [k', q'] <-- find_rcv_thread t' (q1 ++ q2) ; 
      ret ((t, k)::(t', k' m)::q')
  end.

Fixpoint step_system_fn' (q1:ready_queue) (q2:ready_queue) : set ready_queue := 
  match q2 with 
    | nil => Fail
    | (t,ts)::q2' => (step_thread_fn q1 t ts q2') ++ (step_system_fn' ((t,ts)::q1) q2')
  end.

Fixpoint system_to_queue (s:system) : ready_queue := 
  match s with 
    | Empty => nil
    | Thread t c => (t, com_to_thread_state c)::nil
    | Par s1 s2 => (system_to_queue s1) ++ (system_to_queue s2)
  end.


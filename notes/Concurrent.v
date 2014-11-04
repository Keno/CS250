Require Import Arith Bool List String CpdtTactics.
Local Open Scope string_scope.
Infix "++" := List.app.
Import ListNotations.
Class Monad(M:Type -> Type) := 
{
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.
Notation "x <- c1 ; c2" := (bind c1 (fun x => c2))
  (right associativity, at level 84, c1 at next level).

Definition flatMap {A B:Type} (xs:list A) (f:A->list B) : list B := 
  fold_right (fun x a => (f x) ++ a) nil xs.

Definition var := string.
Definition lock := string.
Definition value := nat.
Definition store := list (var * value).
Inductive lock_state := Locked | Unlocked.
Definition locks := list (var * lock_state).
Definition memory := (locks * store)%type.

Fixpoint update {A} (v:string) (val:A) (m:list (string * A)) : list (string * A) := 
  match m with 
    | nil => (v,val)::nil
    | (v',val')::m' => if string_dec v v' then (v',val)::m'
                       else (v',val')::(update v val m')
  end.

Fixpoint lookup_def {A} (v:var) (m:list (string * A)) (def:A) : A := 
  match m with 
    | nil => def
    | (v',val)::m' => if string_dec v v' then val else lookup_def v m' def
  end.

Definition lookup_lock (l:lock) (m:memory) : lock_state := 
  lookup_def l (fst m) Unlocked.

Definition lookup_store (v:var) (m:memory) : value := 
  lookup_def v (snd m) 0.

Definition update_store (v:var) (val:value) (m:memory) : memory := 
  (fst m, update v val (snd m)).

Definition update_lock (l:lock) (ls:lock_state) (m:memory) : memory := 
  (update l ls (fst m), snd m).

Inductive com : Type := 
| Ret : value -> com
| Bind : com -> (value -> com) -> com
| Write : var -> value -> com
| Read : var -> com
| Lock : lock -> com
| Unlock : lock -> com.

Definition program := list com.

Notation "'def' x ':=' c1 'in' c2" := (Bind c1 (fun x => c2))
  (right associativity, at level 84, c1 at next level).
Definition c1 : com := def v := Read "x" in Write "x" (1 + v).
Definition c2 : com := def v := Read "x" in Write "x" (v - 1).
Definition c3 : com := def v := Read "x" in if eq_nat_dec v 0 then Write "y" 42 else  Write "y" 1.

Definition p0 : program := [c1;c2;c3].
Definition s0 : store := [("x",0) ; ("y",0)].
Definition l0 : locks := [].
Definition m0 : memory := (l0, s0).

Inductive step_com : com -> memory -> com -> memory -> Prop := 
| step_bind_ret : forall v f m, step_com (Bind (Ret v) f) m (f v) m
| step_bind_cong : forall c c' m m' f, 
                     step_com c m c' m' -> 
                     step_com (Bind c f) m (Bind c' f) m'
| step_write : forall x v m m', m' = update_store x v m -> step_com (Write "x" v) m (Ret v) m'
| step_read : forall x m v, v = lookup_store x m -> step_com (Read "x") m (Ret v) m
| step_lock : forall l m m', lookup_lock l m = Unlocked -> m' = update_lock l Locked m -> 
                             step_com (Lock l) m (Ret 1) m'
| step_unlock : forall l m m', lookup_lock l m = Locked -> m' = update_lock l Unlocked m -> 
                               step_com (Unlock l) m (Ret 1)  m'.
Hint Constructors step_com.

Inductive step_program : program -> memory -> program -> memory -> Prop := 
| step_prog_com : forall cs1 c cs2 m c' m' p1 p2,
                    step_com c m c' m' -> 
                    p1 = cs1 ++ c :: cs2 -> 
                    p2 = cs1 ++ c' :: cs2 -> 
                    step_program p1 m p2 m'
| step_prog_gc : forall cs1 cs2 v m, 
                   step_program (cs1 ++ (Ret v) :: cs2) m (cs1 ++ cs2) m.
Hint Constructors step_program.

Inductive rt_step_program : program -> memory -> program -> memory -> Prop := 
| rt_step : forall p1 m1 p2 m2 p3 m3, 
              step_program p1 m1 p2 m2 -> 
              rt_step_program p2 m2 p3 m3 -> 
              rt_step_program p1 m1 p3 m3
| rt_refl : forall p m, rt_step_program p m p m.
Hint Constructors rt_step_program.

Definition evals : program -> memory -> memory -> Prop := 
  fun p1 m1 m2 => rt_step_program p1 m1 nil m2.

Fixpoint step_com_fn' (c:com) (m:memory) : option (com * memory) := 
  match c with 
    | Ret _ => None
    | Bind (Ret v) f => Some (f v, m)
    | Bind c1 f => match step_com_fn' c1 m with
                     | None => None
                     | Some (c2, m') => Some (Bind c2 f, m')
                   end
    | Write x v => Some (Ret v, update_store x v m)
    | Read x => Some (Ret (lookup_store x m), m)
    | Lock l => match lookup_lock l m with 
                  | Unlocked => Some (Ret 1, update_lock l Locked m)
                  | Locked => None
                end
    | Unlock l => match lookup_lock l m with 
                  | Locked => Some (Ret 1, update_lock l Unlocked m)
                  | Unlocked => None
                  end
  end.


Lemma p0_trace1 : evals p0 m0 (nil,[("x",0) ; ("y",42)]).
Proof.
  Admitted.






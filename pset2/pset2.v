Require Import Bool Arith String List CpdtTactics.
Require Import FunctionalExtensionality.
Open Scope string_scope.

Definition var := string.

Inductive binop := Plus | Times | Minus.

Inductive aexp : Type := 
| Const : nat -> aexp
| Var : var -> aexp
| Binop : aexp -> binop -> aexp -> aexp.

Inductive bexp : Type := 
| Tt : bexp
| Ff : bexp
| Eq : aexp -> aexp -> bexp
| Lt : aexp -> aexp -> bexp
| And : bexp -> bexp -> bexp
| Or : bexp -> bexp -> bexp
| Not : bexp -> bexp.

Inductive com : Type := 
| Skip : com
| Assign : var -> aexp -> com
| Seq : com -> com -> com
| If : bexp -> com -> com -> com
| While : bexp -> com -> com.

Definition state := var -> nat.

Definition get (x:var) (s:state) : nat := s x.

Definition set (x:var) (n:nat) (s:state) : state := 
  fun y => if string_dec x y then n else get y s.

Check string_dec.

Definition eval_binop (b:binop) : nat -> nat -> nat := 
  match b with 
    | Plus => plus
    | Times => mult
    | Minus => minus
  end.

Fixpoint eval_aexp (e:aexp) (s:state) : nat := 
  match e with 
    | Const n => n
    | Var x => get x s
    | Binop e1 b e2 => (eval_binop b) (eval_aexp e1 s) (eval_aexp e2 s)
  end.

Fixpoint eval_bexp (b:bexp) (s:state) : bool := 
  match b with 
    | Tt => true
    | Ff => false
    | Eq e1 e2 => NPeano.Nat.eqb (eval_aexp e1 s) (eval_aexp e2 s)
    | Lt e1 e2 => NPeano.ltb (eval_aexp e1 s) (eval_aexp e2 s)
    | And b1 b2 => eval_bexp b1 s && eval_bexp b2 s
    | Or b1 b2 => eval_bexp b1 s || eval_bexp b2 s
    | Not b => negb (eval_bexp b s)
  end.

Inductive eval_com : com -> state -> state -> Prop := 
| Eval_skip : forall s, eval_com Skip s s
| Eval_assign : forall s x e, eval_com (Assign x e) s (set x (eval_aexp e s) s)
| Eval_seq : forall c1 s0 s1 c2 s2, 
               eval_com c1 s0 s1 -> eval_com c2 s1 s2 -> 
               eval_com (Seq c1 c2) s0 s2
| Eval_if_true : forall b c1 c2 s s',
                   eval_bexp b s = true -> 
                   eval_com c1 s s' -> eval_com (If b c1 c2) s s'
| Eval_if_false : forall b c1 c2 s s',
                   eval_bexp b s = false -> 
                   eval_com c2 s s' -> eval_com (If b c1 c2) s s'
| Eval_while_false : forall b c s, 
                       eval_bexp b s = false -> 
                       eval_com (While b c) s s
| Eval_while_true : forall b c s1 s2 s3, 
                      eval_bexp b s1 = true -> 
                      eval_com c s1 s2 -> 
                      eval_com (While b c) s2 s3 -> 
                      eval_com (While b c) s1 s3.

(* Write a function ieval_com : nat -> com -> state -> option state
   which takes "fuel" as an argument and tries to run the command
   for fuel-number of steps.  If the command terminates in that time,
   then you should return the resulting state, and if it doesn't
   terminate in that time, you should return None.  
*)

(* Prove that :

   eval_com c s1 s2 -> exists n, ieval_com n c s1 = Some s2.

*)

(* Prove that : 

   ieval_com n c s1 = Some s2 -> eval_com c s1 s2

*)

(* Write a function

     optimize_com : com -> com

   which tries to optimize a command and the sub-expressions 
   within it.  In particular, your optimizer should at least:

   * replace (a + 0) and (0 + a) with a
   * replace (a - 0) with a
   * replace (a * 1) and (1 * a) with a
   * replace (a * 0) and (0 * a) with 0

   * replace (a == a) with Tt
   * replace (a < a) with Ff
   * replace (Tt && Tt) with Tt
   * replace (Tt || b) and (b || Tt) with Tt
   * replace (Ff && b) and (b && Ff) with Ff

   * replace (skip ; c) and (c ; skip) with c
   * replace (if Tt c1 else c2) with c1
   * replace (if Ff c1 else c2) with c2
*)

(* Construct a proof that optimizing a program doesn't change its
   input/output behavior.  That is, show that if we start in state
   s1 and evaluate c to get state s2, then if we evaluate 
   optimize_com(c) in state s1, we get out a state that is
   extensionally equivalent to s2.  
*)
    
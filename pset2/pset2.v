(* Jao-ke Chin-Lee *)
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

Fixpoint ieval_comm_help (fuel used:nat) (c:com) (s:state) {struct fuel} : option state * nat :=
  match fuel with
    | 0 => (None, used)
    | S n =>
      match c with
        | Skip => (Some s, S used)
        | Assign x a =>
          let v := eval_aexp a s in
          (Some (set x v s), S used)
        | Seq c1 c2 =>
          let '(s', used') := ieval_comm_help n used c1 s in
          match s' with
            | None => (None, used')
            | Some s1 => ieval_comm_help (n-used') used' c2 s1
          end
        | If b c1 c2 =>
          if eval_bexp b s then
            ieval_comm_help n (S used) c1 s
          else
            ieval_comm_help n (S used) c2 s
        | While b c =>
          if eval_bexp b s then
            ieval_comm_help n (S used) (While b c) s
          else
            (Some s, S used)
      end
  end.
Fixpoint ieval_comm (fuel:nat) (c:com) (s:state) : option state :=
  let '(res, _) := ieval_comm_help fuel 0 c s in
  res.

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
Definition op_id (op:binop) : aexp :=
  match op with
    | Plus | Minus => Const 0
    | Times => Const 1
  end.
Fixpoint optimize_aexp (a:aexp) : aexp :=
  match a with
    | Binop a1 op a2 =>
      let (a1', a2') := (optimize_aexp a1, optimize_aexp a2) in
      match op with
        | Minus => match a2' with Const 0 => a1' | _ => Binop a1' Minus a2' end
        | Plus =>
          match (a1', a2') with
            | (Const 0, _) => a2'
            | (_, Const 0) => a1'
            | (_, _) => Binop a1' Plus a2'
          end
        | Times =>
          match (a1', a2') with
            | (Const 0, _) => Const 0
            | (Const 1, _) => a2'
            | (_, Const 0) => Const 0
            | (_, Const 1) => a1'
            | (_, _) => Binop a1' Times a2'
          end
      end
    | _ => a
  end.
Fixpoint optimize_bexp (b:bexp) : bexp :=
  match b with
    | Eq a1 a2 =>
      let (a1', a2') := (optimize_aexp a1, optimize_aexp a2) in
      match (a1', a2') with
        | (Const x, Const y) => if beq_nat x y then Tt else Ff
        | (Var x, Var y) => if prefix x y && prefix y x then Tt else Ff
        | (_,_) => Eq a1' a2'
      end
    | Lt a1 a2 =>
      let (a1', a2') := (optimize_aexp a1, optimize_aexp a2) in
      match (a1', a2') with
        | (Const x, Const y) => if beq_nat x y then Ff else Tt
        | (Var x, Var y) => if prefix x y && prefix y x then Ff else Tt
        | (_,_) => Lt a1' a2'
      end
    | And b1 b2 =>
      let (b1', b2') := (optimize_bexp b1, optimize_bexp b2) in
      match (b1', b2') with
        | (Tt, Tt) => Tt
        | (Tt, Ff) | (Ff, Tt) | (Ff, Ff) => Ff
        | _ => And b1' b2'
      end
    | Or b1 b2 =>
      let (b1', b2') := (optimize_bexp b1, optimize_bexp b2) in
      match (b1', b2') with
        | (Tt, _) | (_, Tt) => Tt
        | (Ff, Ff) => Ff
        | _ => Or b1' b2'
      end
    | Not b' =>
      let b'' := optimize_bexp b' in
      match b' with
        | Tt => Ff
        | Ff => Tt
        | _ => Not b''
      end
    | _ => b
   end.
Fixpoint optimize_com (c:com) : com :=
  match c with
    | Skip => Skip
    | Assign x a => Assign x (optimize_aexp a)
    | Seq c1 c2 =>
      let (c1', c2') := (optimize_com c1, optimize_com c2) in
      match c1' with
        | Skip => c2'
        | _ => match c2' with Skip => c1' | _ => Seq c1' c2' end
      end
    | If b c1 c2 =>
      let b' := optimize_bexp b in
      match b' with
        | Tt => optimize_com c1
        | Ff => optimize_com c2
        | _ => If b (optimize_com c1) (optimize_com c2)
      end
    | While b c =>
      let b' := optimize_bexp b in
      match b' with
        | Ff => Skip
        | _ => While b' (optimize_com c)
      end
  end.

(* Construct a proof that optimizing a program doesn't change its
   input/output behavior.  That is, show that if we start in state
   s1 and evaluate c to get state s2, then if we evaluate 
   optimize_com(c) in state s1, we get out a state that is
   extensionally equivalent to s2.  
*)
    


(* Hints:

   * You *will* get stuck doing this assignment.  It is hard.
     Don't hesitate to ask questions on Piazza or in class, 
     or collaborate with friends to solve this.  
     
   * When proving ieval_com is equivalent to eval_com, you will
     find the following lemma very useful:

     ieval_plus : forall n c s1 s2, 
       ieval_com n c s1 = Some s2 -> 
         forall m, ieval_com (n + m) c s1 = Some s2

    This says that if it takes n steps to get an answer out,
    then if you run for more than n steps, you still get the
    same answer out.

   * Write a simple optimizer first, and prove that correct.
     Don't try to write a complicated optimizer first.  It's
     easier to "grow" your development incrementally.  

  * You will find the following tactic very useful:

       remember(<exp>) as <id>

    Consider a proof state like this:

        H : P (foo + bar + baz)
        -----------------------------------------
        match foo + bar + baz with 
          | 0 => blah
          | S n => blahblah
        end

    Executing the tactic

        remember (foo + bar + baz) as x

    will leave you in the state:

        x : nat
        Hxeq : x = foo + bar + baz
        H : P x
        -----------------------------------------
        match x with 
          | 0 => blah
          | S n => blahblah
        end

    So "remember" just helps you name a sub-expression in 
    a proof, and replace all occurrences of that sub-expression
    with that name.  You can always undo the substitution by
    rewriting by the Hxeq equation.

  * There are many useful arithmetic facts in the libraries
    (e.g., plus_0_r, NPeano.Nat.sub_0_r, mult_comm, etc.) 
    Don't forget to use "SearchAbout" to find them.

  * If you [Require Import Omega.] then you can use the "omega"
    tactic to solve some arithmetic questions.  

  * You will want to define a comparison operation for arithmetic
    expressions.  The natural thing to write is something like:

       eq_aexp : aexp -> aexp -> bool

    but you will then need to prove that this is actually correct
    i.e., (eq_aexp a1 a2 = true) <-> (a1 = a2).

    An alternative is to define something like:

      eq_aexp_dec : forall (a1 a2:aexp), {a1 = a2} + {a1<>a2}.

    and instead of trying to build it using explicit code, use
    the "decide quality" tactic (two words.)  For instance:

    Definition eq_aexp_dec (a1 a2:aexp) : {a1=a2} + {a1<>a2}.
      decide quality.
      apply (eq_nat_dec n n0).
      apply (string_dec v v0).
      decide equality.
    Defined.

    This tactic will take an inductive definition and try to
    build the decidable equality term for you.  In the example
    above, I had to tell it how to decide quality for some of
    the types used within the definition (nats, strings, and
    binops.)  

  * You may also find the tactic:

       replace (<exp1>) with (<exp2>) 

    useful.  As suggested, it lets you replace occurrences of 
    one expression with another.  It leaves you with two goals:
    The first is the original goal with the substitution performed.
    The second is a requirement to prove <exp1> = <exp2>. 

  * My solution for this whole file (not including these comments)
    is about 400 lines of code.  Yours will be much, much bigger
    unless you use a lot of automation.  

*)
    
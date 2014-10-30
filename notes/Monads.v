Require Import NPeano Arith Bool String List CpdtTactics.
Set Implicit Arguments.

(* A class definition defines an interface for some type.  In this
   case, we say that types A that implement the Show interface have
   a method named show that will convert them to a string. 

   So we can use the generic method "show" on any type A that is
   an instance of the Show class. 

   In general, you can have multiple things in the interface that
   depend upon the type A.
*)
Class Show(A:Type) := {
  show : A -> string
}.

(* Here we define booleans as an instance of the Show class and
   give a definition of the method.  *)
Instance boolShow : Show bool := {
  show := fun (b:bool) => (if b then "true" else "false") % string
}.

Eval compute in show true.
Eval compute in show false.

(* Now let's define nat as an instance of Show.  We first need
   some helper functions to convert nats to strings. *)

Definition digit2string(d:nat) : string := 
  match d with 
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3"
    | 4 => "4" | 5 => "5" | 6 => "6" | 7 => "7"
    | 8 => "8" | _ => "9"
  end %string.

(* Alas, it can be difficult to convince Coq that
   this terminates.  So we give it fuel.  But, we
   know how much fuel we should use in this case... *)
Fixpoint digits'(fuel n:nat) (accum : string) : string := 
  match fuel with 
    | 0 => accum
    | S fuel' => 
      match n with 
        | 0 => accum
        | _ => let d := digit2string(n mod 10) in 
               digits' fuel' (n / 10) (d ++ accum)
      end
  end.

(* It's sufficient to use n as the fuel here since
   we know we won't need to divide n by 10 more than
   n times.  We could of course use log_10 n, but there's
   no need to bother here. *)
Definition digits (n:nat) : string := 
  match digits' n n "" with 
    | "" => "0"
    | ds => ds
  end %string.

(* Now we can define our nat instance for the Show class. *)
Instance natShow : Show nat := { 
  show := digits
}.

Eval compute in show 42.
Eval compute in show (10+2).

(* Importantly, we still have the ability to show booleans. *)
Eval compute in show true.


(* This is a generic instance in that if we can have two types
    A and B that are instances of the Show class, then we can
   build a generic Show for the product type (A*B).
*)
Instance pairShow(A B:Type)(showA : Show A)(showB : Show B) : Show (A*B) := {
  show := (fun p => "(" ++ (show (fst p)) ++ "," ++ (show (snd p)) ++ ")")
            %string
}.

Eval compute in show (3,4).                 
Eval compute in show (true,42).

(* Similarly, we can define a generic show for lists, as long
   as the elements of the lists are show'able. *)
Definition show_list{A:Type}{showA:Show A}(xs:list A) : string := 
  ("[" ++ ((fix loop (xs:list A) : string := 
             match xs with 
               | nil => "]"
               | h::nil => show h ++ "]"
               | h::t => show h ++ "," ++ loop t
             end) xs))%string.

Instance listShow(A:Type)(showA:Show A) : Show (list A) := {
  show := @show_list A showA
}.

Eval compute in show (1::2::3::nil).
Eval compute in show (true::false::nil).
Eval compute in show ((1,true)::(42,false)::nil).
Eval compute in show ((1::2::3::nil)::(4::5::nil)::(6::nil)::nil).

(***********************************************************)

(* Now we define a generic class for Monads.  Here, it's not a type
   that's a monad, but rather a type constructor (i.e., a function
   from types to types, aka a functor.  Monads have two operations:
   ret and bind.  

   If we think of monads as a pattern for encoding effects, such
   as exceptions or state or non-determinism, then we can think 
   of "M A" as describing side-effecting computations that produce
   a value of type A.  

   The "ret" operation takes a pure (effect-free) value of type A
   and injects it into the space of side-effecting computations.

   The "bind" operation sequences two side-effecting computations,
   allowing the latter to depend upon the value of the first one.
*)
Class Monad(M:Type -> Type) := 
{
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.

(* As usual, we will use the more convenient notation for bind. *)
Notation "x <- c1 ; c2" := (bind c1 (fun x => c2)) 
  (right associativity, at level 84, c1 at next level).

(* One instance of the generic Monad class is the option monad
   defined as follows. *)
Instance OptionMonad : Monad option := 
{
  ret := fun {A:Type} (x:A) => Some x ; 
  bind := fun {A B:Type} (x:option A) (f:A -> option B) =>
            match x with 
              | None => None
              | Some y => f y
            end
}.

Fixpoint subtract (x y:nat) : option nat := 
  match x, y with 
    | 0, 0 => ret 0
    | 0, S _ => None
    | S x', S y' => subtract x' y'
    | _, 0 => ret x
  end.

Inductive exp := 
| Num : nat -> exp
| Plus : exp -> exp -> exp
| Minus : exp -> exp -> exp.

Instance expShow : Show exp := {
  show := fix show_exp (e:exp) : string := 
              match e with 
                | Num n => show n
                | Plus e1 e2 => 
                  "(" ++ (show_exp e1) ++ "+" ++ (show_exp e2) ++ ")"
                | Minus e1 e2 => 
                  "(" ++ (show_exp e1) ++ "-" ++ (show_exp e2) ++ ")"
              end %string
}.

Fixpoint eval (e:exp) : option nat := 
  match e with 
    | Num n => ret n
    | Plus e1 e2 => n1 <- eval e1 ; 
                    n2 <- eval e2 ; 
                    ret (n1 + n2)
    | Minus e1 e2 => n1 <- eval e1 ; 
                     n2 <- eval e2 ; 
                     subtract n1 n2
  end.

Require Import String.
Inductive Exn(A:Type) : Type := 
| Result : A -> Exn A
| Fail : string -> Exn A.
Implicit Arguments Result [A].
Implicit Arguments Fail [A].

Instance ExnMonad : Monad Exn := 
{
  ret := fun {A:Type} (x:A) => Result x ; 
  bind := fun {A B:Type} (x:Exn A) (f:A -> Exn B) =>
            match x with 
              | Result y => f y
              | Fail s => Fail s
            end
}. 

Fixpoint eval' (e:exp) : Exn nat := 
  match e with 
    | Num n => ret n
    | Plus e1 e2 => n1 <- eval' e1 ; 
                    n2 <- eval' e2 ; 
                    ret (n1 + n2)
    | Minus e1 e2 => n1 <- eval' e1 ; 
                     n2 <- eval' e2 ; 
                     match subtract n1 n2 with 
                       | None => Fail "underflow"
                       | Some v => ret v
                     end
  end.

Definition tryCatch {A} (e:Exn A) (s:string) (handler:Exn A) : Exn A := 
  match e with 
    | Fail s' => if string_dec s s' then handler else e
    | _ => e
  end.

Definition eval_to_zero (e:exp) := 
  tryCatch (eval' e) "underflow" (ret 0).

Eval compute in eval' (Minus (Num 2) (Num 5)).
Eval compute in eval_to_zero (Minus (Num 2) (Num 5)).

Require Import List.
Definition var := string.

Inductive exp_s : Type := 
| Var_s : var -> exp_s
| Plus_s : exp_s -> exp_s -> exp_s
| Times_s : exp_s -> exp_s -> exp_s
| Set_s : var -> exp_s -> exp_s
| Seq_s : exp_s -> exp_s -> exp_s
| If0_s : exp_s -> exp_s -> exp_s -> exp_s.

Definition state := var -> nat.
Definition upd(x:var)(n:nat)(s:state) : state := 
  fun v => if string_dec x v then n else s x.

Fixpoint eval_s (e:exp_s)(s:state) : (state * nat) := 
  match e with 
    | Var_s x => (s, s x)
    | Plus_s e1 e2 => 
      let (s1, n1) := eval_s e1 s in
      let (s2, n2) := eval_s e2 s1 in 
      (s2, n1+n2)
    | Times_s e1 e2 =>
      let (s1, n1) := eval_s e1 s in
      let (s2, n2) := eval_s e2 s1 in 
      (s2, n1*n2)
    | Set_s x e => 
      let (s1, n1) := eval_s e s in 
      (upd x n1 s1, n1)
    | Seq_s e1 e2 => 
      let (s1, n1) := eval_s e1 s in
      eval_s e2 s1
    | If0_s e1 e2 e3 => 
      let (s1, n1) := eval_s e1 s in 
      match n1 with 
        | 0 => eval_s e2 s1
        | _ => eval_s e3 s1
      end
  end.

Definition state_comp(A:Type) := state -> (state*A).

Instance StateMonad : Monad state_comp := {
  ret := fun {A:Type} (x:A) => (fun (s:state) => (s,x)) ; 
  bind := fun {A B:Type} (c : state_comp A) (f: A -> state_comp B) => 
            fun (s:state) => 
              let (s',v) := c s in 
              f v s'
}.

Definition read (x:var) : state_comp nat := 
  fun s => (s, s x).

Definition write (x:var) (n:nat) : state_comp nat := 
  fun s => (upd x n s, n).

Fixpoint eval_sm (e:exp_s) : state_comp nat := 
  match e with 
    | Var_s x => read x
    | Plus_s e1 e2 => 
      n1 <- eval_sm e1 ; 
      n2 <- eval_sm e2 ; 
      ret (n1 + n2)
    | Times_s e1 e2 =>
      n1 <- eval_sm e1 ; 
      n2 <- eval_sm e2 ; 
      ret (n1 * n2)
    | Set_s x e => 
      n <- eval_sm e ; 
      write x n 
    | Seq_s e1 e2 => 
      _ <- eval_sm e1 ; 
      eval_sm e2
    | If0_s e1 e2 e3 => 
      n <- eval_sm e1 ;
      match n with 
        | 0 => eval_sm e2
        | _ => eval_sm e3 
      end
  end.

Inductive exp_nd : Type := 
| Choose_nd : list nat -> exp_nd
| Plus_nd : exp_nd -> exp_nd -> exp_nd
| Times_nd : exp_nd -> exp_nd -> exp_nd.

Definition flatten {A:Type} (xs:list (list A)) := 
  fold_right (fun x a => x ++ a) nil xs.

Instance listMonad : Monad list := {
  ret := fun {A:Type} (x:A) => (x::nil) ;
  bind := fun {A B:Type} (c:list A) (f: A -> list B) => 
            flatten (map f c)
}.

Fixpoint eval_nd (e:exp_nd) : list nat := 
  match e with 
    | Choose_nd ns => ns
    | Plus_nd e1 e2 => 
      n1 <- eval_nd e1 ; 
      n2 <- eval_nd e2 ; 
      ret (n1 + n2)
    | Times_nd e1 e2 => 
      n1 <- eval_nd e1 ; 
      n2 <- eval_nd e2 ;
      ret (n1 * n2)
  end.


Class Monad_with_Laws (M: Type -> Type){MonadM : Monad M} :=
{
  m_left_id : forall {A B:Type} (x:A) (f:A -> M B), bind (ret x) f = f x ;
  m_right_id : forall {A B:Type} (c:M A), bind c ret = c ;
  m_assoc : forall {A B C} (c:M A) (f:A->M B) (g:B -> M C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g)
}.

Instance OptionMonadLaws : @Monad_with_Laws option _ := {}.
  auto.
  intros ; destruct c ; auto.
  intros ; destruct c ; auto.
Defined.



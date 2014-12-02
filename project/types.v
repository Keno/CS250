Require Import Arith.
Require Import String.
Require Import List.
Require Import CpdtTactics.
Set Implicit Arguments.
Unset Automatic Introduction.
Local Open Scope string_scope.

(* TODO: Split into TagT when adding parameters *)

Inductive TypeName : Type :=
| TypName : string -> AbstractType -> TypeName
with AbstractType : Type :=
| Any : AbstractType
| Top : AbstractType
(* TODO: Add parameters here *)
| AbstractTyp : TypeName -> AbstractType.

Inductive ConcreteType : Type := 
| ConcreteTyp : TypeName -> ConcreteType.

Inductive JLType : Type :=
| AT : AbstractType -> JLType
| CT : ConcreteType -> JLType.

Definition super (T: JLType) := 
  AT match T with
    | AT T' => 
      match T' with
       | Any => Any
       | Top => Top
       | AbstractTyp (TypName _ T'') => T''
      end
    | CT (ConcreteTyp (TypName _ T'')) => T''
  end.

Definition typname (T: JLType) :=
  match T with
    | AT Any | AT Top => None
    | AT (AbstractTyp tn) | CT (ConcreteTyp tn) => Some tn
  end.

Inductive issub : JLType -> JLType -> Prop :=
| issub_Top : issub (AT Any) (AT Top)
| issub_refl : forall S, issub S S
| issub_name : forall S T, typname S = typname T -> (* Parameters here *) issub S T
| issub_lattice : forall S T, issub (super S) T -> issub S T.

(* TODO: Tuples, Unions *)
(* No sideeffects *)

Definition label := nat.
Definition var := string.

(* We are avoiding interprocedural type inference for now by 
   defining every method to have a well defined return type *)
Definition Method := (prod (list JLType) ConcreteType).
Definition MethodTable := list Method.

Inductive ExprTree :=
| Call : MethodTable -> list ExprTree -> JLType -> ExprTree (* allowed annots, params, rettype *)
| Const : ConcreteType -> ExprTree (* consttype *)
| VarLookup : var -> JLType -> ExprTree. (* var, vartype *)

Inductive LoweredASTNode :=
| Assign : var -> ExprTree -> LoweredASTNode
| GotoNode : label -> LoweredASTNode
| GotoIfNot : ExprTree -> label -> LoweredASTNode
| Return : ExprTree -> LoweredASTNode.

Definition LoweredAST := list LoweredASTNode.

Definition TypedList T := (list (var * T)).

Definition LambdaInfo := (pair (TypedList ConcreteType) LoweredAST).

Fixpoint twolist_all {A:Type} (P:A->A->Prop) (xs ys:list A) : Prop :=
  match xs, ys with
      | nil, nil => True
      | (hdx::xs'), (hdy::ys') => (P hdx hdy) /\ twolist_all P xs' ys'
      | _, _ => False
  end.

Fixpoint method_lookup (M: MethodTable) (args: list ExprTree) : option Method := None.

Definition rettype (x : option Method) : option JLType := 
  match x with
    | None => None
    | Some y => Some (CT (snd y))
  end. 

Definition issub' (x : option JLType) (y : JLType) : Prop :=
  match x with
    | None => True
    | Some x' => issub x' y
  end.

Fixpoint var_lookup (typs : TypedList JLType) (v : var) : option JLType :=
  match typs with
    | nil => None
    | (u,t)::rest => if string_dec u v then Some t else var_lookup rest v
  end.

Definition var_istype (typs : TypedList JLType) (v : var) (t : JLType) : Prop :=
  match var_lookup typs v with
    | None => False
    | Some t' => t' = t
  end.

Definition var_isdef (typs : TypedList JLType) (v : var) : Prop :=
  match var_lookup typs v with
    | None => False
    | _ => True
  end.

Inductive PreExprTreeValid : (TypedList JLType) -> ExprTree -> ExprTree -> Prop :=
| PreCall_valid : forall typs f args1 args2 ret1 ret2,
                    issub' (rettype (method_lookup f args2)) ret2 ->
                    issub ret1 ret2 -> (* rettype *)
                    (* argtype *)
                      PreExprTreeValid typs (Call f args1 ret1) (Call f args2 ret2)
| PreConst_valid : forall typs C, PreExprTreeValid typs (Const C) (Const C)
| PreVarLookup_valid : forall typs v T1 T2,
                         (*(*var_isdef typs v ->*)
                         var_istype typs v T1 ->*)
                         issub T1 T2 ->
                           PreExprTreeValid typs (VarLookup v T1) (VarLookup v T2).

Lemma PreExprTreeValid_refl : forall typs tree, PreExprTreeValid typs tree tree.
Proof.  
  induction tree; intros; econstructor.
  induction m; simpl in *; crush.
  econstructor.
  econstructor.
Qed.

Inductive ExprTreeValid : (TypedList JLType) -> ExprTree -> ExprTree -> Prop :=
| Call_valid : forall typs f args1 args2 ret1 ret2,
                 PreExprTreeValid typs (Call f args1 ret1) (Call f args2 ret2) ->
                 twolist_all (fun A B => PreExprTreeValid typs A B) args1 args2 ->
                   ExprTreeValid typs (Call f args1 ret1) (Call f args2 ret2)
| Const_valid : forall typs C,
                  PreExprTreeValid typs (Const C) (Const C) ->
                    ExprTreeValid typs (Const C) (Const C)
| VarLookup_valid : forall typs v T1 T2,
                      PreExprTreeValid typs (VarLookup v T1) (VarLookup v T2) ->
                        ExprTreeValid typs (VarLookup v T1) (VarLookup v T2).

Lemma ExprTreeValid_refl : forall typs tree, ExprTreeValid typs tree tree.
Proof.
  induction tree; intros; econstructor.
  eapply PreExprTreeValid_refl.
  induction l; crush.
  eapply PreExprTreeValid_refl.
  eapply PreExprTreeValid_refl.
  eapply PreExprTreeValid_refl.
Qed.

Inductive NodeInferenceValid : (TypedList JLType) -> LoweredASTNode -> LoweredASTNode -> Prop :=
| Assign_valid : forall typs tree1 tree2 v,
                   ExprTreeValid typs tree1 tree2 -> 
                     NodeInferenceValid typs (Assign v tree1) (Assign v tree2)
| GotoNode_valid : forall typs l,
                     NodeInferenceValid typs (GotoNode l) (GotoNode l)
| GotoIfNot_valid : forall typs tree1 tree2 l,
                      ExprTreeValid typs tree1 tree2 ->
                        NodeInferenceValid typs (GotoIfNot tree1 l) (GotoIfNot tree2 l)
| Return_valid : forall typs tree1 tree2,
                   ExprTreeValid typs tree1 tree2 ->
                     NodeInferenceValid typs (Return tree1) (Return tree2).

Lemma NodeInferenceValid_refl : forall typs node, NodeInferenceValid typs node node.
Proof.
  induction node; intros; econstructor; apply ExprTreeValid_refl.
Qed.

Definition InferenceValid (typs: TypedList JLType) (AST1: LoweredAST) (AST2: LoweredAST) : Prop :=
  twolist_all (fun A B => NodeInferenceValid typs A B) AST1 AST2.

Hint Unfold InferenceValid.

Lemma InferenceValid_refl : forall typs AST, InferenceValid typs AST AST.
Proof.
  induction AST. crush. unfold InferenceValid. simpl. crush.
  apply NodeInferenceValid_refl.
Qed.

(* PAUSE *)

Inductive PreExprTreeValid : (TypedList JLType) -> ExprTree -> ExprTree -> Prop :=
| PreCall_valid : forall typs M args1 args2 ret1 ret2, 
    issub' (rettype (method_lookup M args2)) ret2 -> 
    issub ret2 ret1 -> 
    (*twolist_all (fun A B => ExprTreeValid typs A B) args1 args2 ->*)
      PreExprTreeValid typs (Call M args1 ret1) (Call M args2 ret2)
| PreConst_valid : forall typs C, PreExprTreeValid typs (Const C) (Const C)
| PreVarLookup_valid : forall typs v T1 T2, issub (var_lookup typs v) T2 -> 
     issub T2 T1 -> PreExprTreeValid typs (VarLookup v T1) (VarLookup v T2).

Lemma PreExprTreeValid_refl : forall typs tree, PreExprTreeValid typs tree tree.
Proof.
  induction tree; intros; econstructor.
  induction m; simpl in *; crush.
  econstructor.
  



Inductive ExprTreeValid : (TypedList JLType) -> ExprTree -> ExprTree -> Prop :=
| Call_valid : forall typs M args1 args2 ret1 ret2,
                 PreExprTreeValid typs (Call M args1 ret1) (Call M args2 ret2)
                 -> twolist_all (fun A B => PreExprTreeValid typs A B) args1 args2 ->
                 ExprTreeValid typs (Call M args1 ret1) (Call M args2 ret2)
| Const_valid : forall typs C,
                  PreExprTreeValid typs (Const C) (Const C) ->
                  ExprTreeValid typs (Const C) (Const C)
| VarLookup_valid : forall typs v T1 T2,
                      PreExprTreeValid typs (VarLookup v T1) (VarLookup v T2) ->
                      ExprTreeValid typs (VarLookup v T1) (VarLookup v T2).

Lemma ExprTreeValid_refl : forall typs tree, ExprTreeValid typs tree tree.
Proof.
  induction tree; intros; econstructor.
  

Inductive NodeInferenceValid : (TypedList JLType) -> LoweredASTNode -> LoweredASTNode -> Prop :=
| Assign_valid : forall typs tree1 tree2 v,
                   ExprTreeValid typs tree1 tree2 -> 
                     NodeInferenceValid typs (Assign v tree1) (Assign v tree2)
| GotoNode_valid : forall typs l,
                     NodeInferenceValid typs (GotoNode l) (GotoNode l)
| GotoIfNot_valid : forall typs tree1 tree2 l,
                      ExprTreeValid typs tree1 tree2 ->
                        NodeInferenceValid typs (GotoIfNot tree1 l) (GotoIfNot tree2 l)
| Return_valid : forall typs tree1 tree2,
                   ExprTreeValid typs tree1 tree2 ->
                     NodeInferenceValid typs (Return tree1) (Return tree2).

Lemma NodeInferenceValid_refl : forall typs node, NodeInferenceValid typs node node.
Proof.
  induction node; intros; econstructor; apply ExprTreeValid_refl.
Qed.

Definition InferenceValid (typs: TypedList JLType) (AST1: LoweredAST) (AST2: LoweredAST) : Prop :=
  twolist_all (fun A B => NodeInferenceValid typs A B) AST1 AST2.

Hint Unfold InferenceValid.

Lemma InferenceValid_refl : forall typs AST, InferenceValid typs AST AST.
Proof.
  induction AST. crush. unfold InferenceValid. simpl. crush.
  apply NodeInferenceValid_refl.
Qed.

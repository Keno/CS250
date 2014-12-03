Require Import Arith.
Require Import String.
Require Import List.
Require Import CpdtTactics.
Import ListNotations.
Set Implicit Arguments.
Unset Automatic Introduction.
Local Open Scope string_scope.
Require Import Program.Wf Init.Wf.
Require Import FunctionalExtensionality.
Include WfExtensionality.

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

Inductive PreExprTreeValid : (TypedList JLType) -> ExprTree -> Prop :=
| PreCall_valid : forall env mt args rettyp,
                    issub' (rettype (method_lookup mt args)) rettyp ->
                      PreExprTreeValid env (Call mt args rettyp)
| PreConst_valid : forall env consttyp,
                     PreExprTreeValid env (Const consttyp)
| PreVarLookup_valid : forall env v vartyp,
                         var_istype env v vartyp ->
                           PreExprTreeValid env (VarLookup v vartyp).

Inductive ExprTreeValid : (TypedList JLType) -> ExprTree -> Prop :=
| Call_valid : forall env mt args rettyp,
                 fold_right (fun h t => PreExprTreeValid env h /\ t) True args ->
                 ExprTreeValid env (Call mt args rettyp)
| Const_valid : forall env consttyp,
                  PreExprTreeValid env (Const consttyp) ->
                    ExprTreeValid env (Const consttyp)
| VarLookup_valid : forall env v vartyp,
                      PreExprTreeValid env (VarLookup v vartyp) ->
                        ExprTreeValid env (VarLookup v vartyp).

(*Inductive ExprTreeValid_d : (TypedList JLType) -> ExprTree -> nat -> Prop :=
| Call_valid : forall n env mt args rettyp,
                 (forall a, In a args /\ PreExprTreeValid env a) ->
                 (forall a, n >= depth a) ->
                   ExprTreeValid env (Call mt args*)

Require Import Coq.Program.Wf.

Definition max_all l := fold_right (fun h t => max h t) 0 l.
(*Fixpoint depth (e : ExprTree) :=
  match e with
    | Call _ args _ => S (max_all (map depth args))
    | _ => 0
  end.*)
Fixpoint depth (e : ExprTree) :=
  match e with
    | Call _ args _ => max_all (map (fun a => S (depth a)) args)
    | _ => 0
  end.

Theorem exprtree_eq_dec : forall (E1 E2:ExprTree), {E1 = E2} + {E1 <> E2}.
Proof.
  Lemma exprtree_eq_dec_depth' : forall (E1 E2:ExprTree) (n:nat), n = depth E1 -> ({E1 = E2} + {E1 <> E2}).
  Proof.
    induction n.
    Admitted. (* use decidability of equality of nats *)
  intros.
  specialize exprtree_eq_dec_depth' with (E1:=E1) (E2:=E2) (n:=(depth E1)).
  crush.
Qed.

Check In.

Definition foobar : forall {A:Type} (xs xs':list A) (hdx:A),
                      xs = (hdx::xs') -> In hdx (hdx::xs') -> In hdx xs.
Proof.
  induction xs; crush.
Qed.

Fixpoint twolist_all_wf {A:Type} (xs ys: list A) (Q: A->Prop) (P: forall x:A, A->(Q x)->Prop) (O: forall x, (In x xs)->(Q x)) {struct xs} : Prop.
  intros.
  destruct xs eqn:XE; destruct ys eqn:YE. 
  refine (True).
  refine (False).
  refine (False).
  refine ( (P a a0 _) /\ twolist_all_wf A l l0 Q P _ ). 
(* WE WANTED TO DO THIS BUT IT DOESN"T GIVE THE xs=hdx::xs' HYPOTHESIS. PLEASE FIX IN COQ
 refine (match (xs, ys) with
      | (nil, nil) => True
      | ((hdx::xs'), (hdy::ys')) => (P hdx hdy _) /\ twolist_all_wf A xs' ys' Q P _
      | (_, _) => False
  end). *)
  apply O.
  apply in_eq.
  intros.
  apply O.
  apply in_cons.
  assumption.
Defined.

Definition args (E : ExprTree) : list ExprTree :=
match E with
| (Call _ args _) => args
| _ => nil
end.

Lemma maxes : forall x l, In x l -> x <= (max_all l).
induction l; crush. 
Qed.

(* BELOW IS BAR WITH DEPTH WITH CALL ALWAYS DEPTH >= 1 *)
(*Definition bar (xs:list ExprTree) (E1 : ExprTree) : (xs = args E1)  -> (forall x, (In x xs)->(depth x < depth E1)).
  intros.
  destruct E1 eqn:EC.
  + simpl args in *.
    subst.
    crush.
    apply le_lt_n_Sm.
    apply maxes.
    apply in_map.
    assumption.
  + crush.
  + crush.
Qed.*)

Definition bar (xs:list ExprTree) (E1 : ExprTree) : (xs = args E1)  -> (forall x, (In x xs)->(depth x < depth E1)).
  intros.
  destruct E1 eqn:EC.
  + simpl args in *.
    subst.
    induction l.
    contradict H0.
    assert ({x=a} + {x<>a}). admit.
    destruct H.
    subst.
    simpl.
    Ltac r := match goal with
      | [ |- context[ max_all ?x ] ] => remember (max_all x) as cond; destruct cond
    end.
    r.
    crush.
    crush.
    apply in_inv in H0.
    destruct H0; [ congruence | ].
    apply IHl in H.
    assert (depth (Call m l j) <= depth (Call m (a::l) j)).
    simpl depth.
    r; crush.
    crush.
 + crush.
 + crush.
Qed.

(* Definition wft (arg E1 : ExprTree) : forall mt1 arg1 rt1, E1 = (Call mt1 arg1 rt1) -> In arg arg1 -> depth arg < depth E1 -> Prop.
Admitted.
*)

Program Fixpoint exprtree_subtype (E1 E2 : ExprTree) {measure (depth E1)} : Prop :=
  match (E1, E2) with
    | (Call mt1 arg1 rettyp1, Call mt2 arg2 rettyp2) =>
      mt1 = mt2 /\
      twolist_all_wf arg1 arg2 (fun E => depth E < depth E1) exprtree_subtype ((bar E1) (eq_refl (args E1))) /\
      issub rettyp2 rettyp1
    | (Const c1, Const c2) => c1 = c2
    | (VarLookup v1 vartyp1, VarLookup v2 vartyp2) => v1 = v2 /\ issub vartyp1 vartyp2
    | (_,_) => False
  end.
Solve Obligations using crush.

Check exprtree_subtype_func.

(*Lemma exprtree_subtype_trans: forall tree1 tree2 tree', exprtree_subtype tree1 tree' ->
                                                        exprtree_subtype tree' tree2 ->
                                                          exprtree_subtype tree1 tree2.
Proof.
  Check depth_induct.
  intros tree1 tree2.
  specialize depth_induct with (P:=(fun tree' => exprtree_subtype tree1 tree')); intro.
  specialize depth_induct with (P:=(fun tree' => exprtree_subtype tree' tree2)); intro.
  induction tree'.*)
  
Lemma Call0 : forall m args r, 0 = depth (Call m args r) <-> args = [].
Proof.
  induction args0.
  crush.
  split. simpl depth. r; crush. crush.
Qed.

Fixpoint list_all_wf {A:Type} (xs : list A) (Q: A->Prop) (P: forall x:A, A->(Q x)->Prop) (O: forall x, (In x xs)->(Q x)) {struct xs} : Prop.
intros.
destruct xs eqn:XE.
refine (True).
refine ( (P a a _) /\ list_all_wf A l Q P _ ).
apply O.
apply in_eq.
intros.
apply O.
apply in_cons.
assumption.
Defined.

Lemma twolist_all_ind : forall A xs ys Q P O, xs = ys -> @list_all_wf A xs Q P O -> @twolist_all_wf A xs ys Q P O.
intros. subst.
induction ys; crush.
Qed.

Lemma exprtree_subtype_hammer : forall m1 m2 args1 args2 r1 r2,
                                  m1=m2 -> 
                                  issub r2 r1 ->
                                  twolist_all exprtree_subtype args1 args2 ->
                                    exprtree_subtype (Call m1 args1 r1) (Call m2 args2 r2).
Proof.
  intros.
  set (call:= (exprtree_subtype (Call m1 args1 r1) (Call m2 args2 r2))).
  unfold exprtree_subtype in call.
  unfold call.
  unfold exprtree_subtype_func.
  rewrite fix_sub_eq_ext.
  repeat fold_sub exprtree_sub.
  simpl proj1_sig.
  simpl.
  split.
  assumption.
  split; [ | assumption ].
  induction args1.
  crush.
  destruct args2; assumption.
  Admitted.

(*rewrite fix_sub_eq_ext.
simpl.
split.
Check fix_sub_eq_ext.
unfold_sub exprtree_subtype (exprtree_subtype (Call m1 args1 r1) (Call m2 args2 r2)).
econstructor. assumption.
induction args1.
fold_sub.
split.*)

Lemma exprtree_subtype_refl : forall n tree, n >= depth tree -> exprtree_subtype tree tree.
Proof.
  induction n.
  intros. destruct tree.
  apply le_lt_or_eq in H. destruct H. contradict H. crush.
  erewrite Call0 in H. subst.
  econstructor; crush.
  econstructor.
  crush. 
  econstructor.
  reflexivity.
  econstructor.
  intros.
  destruct tree.

  apply exprtree_subtype_hammer.
  reflexivity.
  econstructor.
  induction l.
  crush.
  unfold twolist_all.
  split.
  apply IHn.

  econstructor.
  reflexivity.
  fold exprtree_subtype.
  fold exprtree_subtype.
  unfold exprtree_subtype in *.
  fold exprtree_subtype_func in *.
  match goal with 
      | [ |- context[ twolist_all_wf ?x ?y ?Q ?P ?O ] ] => remember P as P1; remember O as O1
  end.
  split; [ | econstructor ].
  eapply twolist_all_ind. reflexivity.

  unfold list_all_wf. simpl.
  crush. crush.

  assert (list_all_wf l (fun E => depth E < depth (Call m l j)) exprtree_subtype ((bar (Call m l j)) (eq_refl (args (Call m l j))))). 
  eapply twolist_all_ind.
  induction l.
  crush.
  econstructor.
  ref
  crush.
  erewrite twolist_all_ind.

crush.
 crush.
  econstructor.
  crush.
  crush.
  econstructor. reflexivity. econstructor.
  intros. destruct tree.
  induction l.
  crush.
  eapply IHn.
  

intro.
econstructor.
reflexivity.

crush.
Check exprtree_subtype.

Lemma Call_raise_params : forall args1 args2 env mt rettyp,
                             ->
                            ExprTreeValid env (Call mt args1 rettyp) ->
                              ExprTreeValid env (Call mt args2 rettyp).

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

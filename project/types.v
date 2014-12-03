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
(**
Here we have types. 
*)
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

Fixpoint list_all {A:Type} (P:A->Prop) (xs:list A) : Prop :=
  match xs with
      | nil => True
      | (hdx::xs') => (P hdx) /\ list_all P xs'
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

Inductive ExprTreeValid : (TypedList JLType) -> ExprTree -> Prop :=
| Call_valid : forall env mt args rettyp,
                 issub' (rettype (method_lookup mt args)) rettyp ->
                 (forall a, (In a args -> ExprTreeValid env a)) ->
                   ExprTreeValid env (Call mt args rettyp)
| Const_valid : forall env consttyp,
                  ExprTreeValid env (Const consttyp)
| VarLookup_valid : forall env v vartyp,
                      var_istype env v vartyp ->
                        ExprTreeValid env (VarLookup v vartyp).

Require Import Coq.Program.Wf.

Definition max_all l := fold_right (fun h t => max h t) 0 l.
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
Proof.
  induction l; crush. 
Qed.

Definition depth_decreases (xs:list ExprTree) (E1 : ExprTree) : (xs = args E1) -> (forall x, (In x xs)->(depth x < depth E1)).
Proof.
  intros.
  destruct E1 eqn:EC.
  + simpl args in *.
    subst.
    induction l.
    contradict H0.
    assert ({x=a} + {x<>a}). apply exprtree_eq_dec.
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

Program Fixpoint exprtree_subtype (E1 E2 : ExprTree) {measure (depth E1)} : Prop :=
  match (E1, E2) with
    | (Call mt1 arg1 rettyp1, Call mt2 arg2 rettyp2) =>
      mt1 = mt2
      /\ twolist_all_wf arg1 arg2 (fun E => depth E < depth E1)
                        exprtree_subtype ((depth_decreases E1) (eq_refl (args E1)))
      /\ issub rettyp2 rettyp1
    | (Const c1, Const c2) => c1 = c2
    | (VarLookup v1 vartyp1, VarLookup v2 vartyp2) => v1 = v2 /\ issub vartyp1 vartyp2
    | (_,_) => False
  end.
Solve Obligations using crush.
  
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

Lemma twolist_all_ind : forall A xs ys Q P O, xs = ys ->
                                              @list_all_wf A xs Q P O ->
                                                @twolist_all_wf A xs ys Q P O.
Proof.
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

Lemma max_ge : forall n m z, z >= max n m -> z >= n /\ z >= m.
Proof.
  intros.
  specialize le_ge_dec with (n:=n) (m:=m); intros.
  destruct H0. assert (l2:=l). apply max_r in l. crush.
  assert (g2:=g). apply max_l in g. crush.
Qed.

Lemma max_cons : forall a l n, n >= max_all (a::l) -> n >= max_all l.
Proof.
  induction l.
  crush.
  intros.
  simpl max_all in *.
  apply max_ge in H. destruct H. assumption.
Qed.

Lemma cons_is_app_one : forall A (a: A) (l: list A), a::l = (app [a] l).
Proof.
  crush.
Qed.

Lemma argdepth : forall m n a l j, n >= depth (Call m (a :: l) j) ->
                                     n > (depth a) /\ n >= depth (Call m l j).
Proof.
  intros.
  unfold depth in *.
  do 2 match goal with
    | [ M : context[ (max_all ?l) ] |- _ ] => remember l as x
    | [ M : context[ (map ?l _) ] |- _ ] => remember l as y
  end.
  assert (depth a < max_all x).
  apply maxes.
  rewrite Heqx.
  assert (S (depth a) = (y a)). crush. rewrite H0.
  apply in_map. crush.
  split. fold depth. crush.
  rewrite Heqx in *. clear Heqx. 
  rewrite cons_is_app_one in H.
  rewrite map_app in H.
  simpl map in H.
  rewrite <- cons_is_app_one in H.
  apply max_cons in H.
  assumption.
Qed.

Lemma exprtree_subtype_refl : forall tree, exprtree_subtype tree tree.
  Lemma exprtree_subtype_refl' : forall n tree, n >= depth tree -> exprtree_subtype tree tree.
  Proof.
    induction n.
    intros. destruct tree.
    apply le_lt_or_eq in H. destruct H. contradict H. crush.
    apply eq_sym in H.
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
    apply argdepth in H. destruct H.

    split. apply IHn. apply lt_n_Sm_le. assumption.
    apply IHl. assumption.

    crush.
    crush.
  Qed.
  intros.
  destruct (depth tree) eqn:d.
  apply exprtree_subtype_refl' with (n:=0). crush.
  apply exprtree_subtype_refl' with (n:=(S (S n))). crush.
Qed.

Definition ExprTreeInferenceValid (typs: TypedList JLType) (E1 E2: ExprTree) :=
  ExprTreeValid typs E1 /\ ExprTreeValid typs E2 /\ exprtree_subtype E2 E1.

Inductive NodeValid : (TypedList JLType) -> LoweredASTNode -> Prop :=
| Assign_valid : forall typs tree v, ExprTreeValid typs tree -> NodeValid typs (Assign v tree)
| GotoNode_valid: forall typs l, NodeValid typs (GotoNode l)
| GotoIfNot_valid: forall typs tree l, ExprTreeValid typs tree -> NodeValid typs (GotoIfNot tree l)
| Return_valid: forall typs tree, ExprTreeValid typs tree -> NodeValid typs (Return tree).

Inductive NodeInferenceValid : (TypedList JLType) -> LoweredASTNode -> LoweredASTNode -> Prop :=
| AssignInference_valid : forall typs tree1 tree2 v,
                   NodeValid typs (Assign v tree1) -> NodeValid typs (Assign v tree2) ->
                     ExprTreeInferenceValid typs tree1 tree2 ->
                     NodeInferenceValid typs (Assign v tree1) (Assign v tree2)
| GotoNodeInference_valid : forall typs l,
                   NodeValid typs (GotoNode l) ->
                     NodeInferenceValid typs (GotoNode l) (GotoNode l)
| GotoIfNotInference_valid : forall typs tree1 tree2 l,
                      ExprTreeInferenceValid typs tree1 tree2 ->
                        NodeInferenceValid typs (GotoIfNot tree1 l) (GotoIfNot tree2 l)
| ReturnInference_valid : forall typs tree1 tree2,
                   ExprTreeInferenceValid typs tree1 tree2 ->
                     NodeInferenceValid typs (Return tree1) (Return tree2).

Lemma NodeInferenceValid_refl : forall typs node, NodeValid typs node ->
                                                    NodeInferenceValid typs node node.
Proof.
  induction node; intros; econstructor; econstructor; inversion H; try assumption; 
  ( split; [ assumption | ] ); apply exprtree_subtype_refl.
Qed.

Definition InferenceValid (typs: TypedList JLType) (AST1: LoweredAST) (AST2: LoweredAST) : Prop :=
  twolist_all (fun A B => NodeInferenceValid typs A B) AST1 AST2.

Hint Unfold InferenceValid.

Definition ASTValid typs AST := list_all (fun A => NodeValid typs A) AST.

Lemma InferenceValid_refl : forall typs AST, ASTValid typs AST -> InferenceValid typs AST AST.
Proof.
  intros.
  unfold InferenceValid. 
  induction AST. crush. simpl. split. apply NodeInferenceValid_refl. 
  unfold ASTValid in H. simpl in H. destruct H. assumption.
  apply IHAST. unfold ASTValid in H. simpl in H. destruct H. assumption.
Qed.

(* A simple inference algorithm that just takes the function parameters and annotates them throughout the tree. Also useful as a first pass for other algorithms. *)



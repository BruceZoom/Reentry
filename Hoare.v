Require Import Coq.Lists.List.
Require Import Omega.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Require Import AST.
Require Import ASTLc.
Require Import Label.

(** Basic Assertions *)
Definition Assertion := state -> Prop.

Definition derives (P Q: Assertion): Prop :=
  forall st, P st -> Q st.

Definition equiv_assert (P Q: Assertion): Prop :=
  derives P Q /\ derives Q P.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Definition andp (P Q : Assertion) : Assertion :=
  fun st => P st /\ Q st.

Definition orp (P Q : Assertion) : Assertion :=
  fun st => P st \/ Q st.

Definition notp (P : Assertion) : Assertion :=
  fun st => ~ (P st).

Notation "P 'AND' Q" := (andp P Q) (at level 50, left associativity).
Notation "P 'OR' Q" := (orp P Q) (at level 51, left associativity).
Notation "'NOT' P" := (notp P) (at level 40).
Notation "P '|--' Q" := (derives P Q) (at level 90, no associativity).
Notation "P '--||--' Q" := (equiv_assert P Q) (at level 90, no associativity).
Notation "{[ b ]}" := (bassn b) (at level 30, no associativity).

Definition globalp (P : Assertion) : Prop :=
  forall loc1 loc2 glb,
    P (loc1, glb) -> P (loc2, glb).

Definition localp (P : Assertion) : Prop :=
  forall loc glb1 glb2,
    P (loc, glb1) -> P (loc, glb2).
(** [] *)


(** Conventional Hoare with call *)
Module HoareWithCall.
Import ASTWithCall.

Definition hoare_triple (fc : func_context) (lf : public_funcs) (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st1 st2, 
    ceval fc lf c st1 st2 ->
    P st1 ->
    Q st2.

Definition func_triple (fc : func_context) (lf : public_funcs) (P : Assertion) (f : func) (Q : Assertion) : Prop :=
  forall st1 st2,
    ceval fc lf (func_bdy f) st1 st2 ->
    P st1 ->
    Q st2.

Notation "'|' fc ',' lf '|' '{{' P '}}' c '{{' Q '}}'" := (hoare_triple fc lf P c Q) (at level 90, c at next level).

Definition pv_to_assertion (fc : func_context) (f : func) (pv : list aexp) (P : Assertion) : Assertion :=
  fun st => P (param_to_local_state st (func_arg f) pv, snd st).

Theorem func_hoare_triple_equiv : forall fc lf f pv P Q,
  func_triple fc lf (pv_to_assertion fc f pv P) f Q <->
  |fc, lf| {{P}} (CCall f pv) {{Q}}.
Proof.
  unfold func_triple, hoare_triple.
  intros.
  split.
  {
    intros.
    inversion H0; subst.
    destruct H8 as [loc2 ?].
    pose proof H _ _ H2.
    unfold pv_to_assertion in *.
    simpl in *.
Admitted.

Theorem hoare_consequence : forall fc lf P P' Q Q' c,
  P |-- P' ->
  |fc, lf| {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  |fc, lf| {{P}} c {{Q}}.
Proof.
  intros.
  unfold hoare_triple. intros.
  apply H1. apply H in H3.
  pose proof H0 st1 st2 H2 H3.
  exact H4.
Qed.

Theorem hoare_reentry : forall fc lf P I,
  localp P ->
  globalp I ->
  (forall f, In f lf ->
      func_triple fc lf I f I) ->
  |fc, lf| {{ P AND I }} CReentry {{ P AND I }}.
Proof.
  unfold localp, globalp, hoare_triple, func_triple.
  intros.
(** Attempt arbitrary reentry *)
  inversion H2; subst.
  unfold andp in *.
  destruct H3.
  split; [eapply H; apply H3 | ].
  induction H4.
  - exact H5.
  - pose proof H0 _ loc1 _ H5.
    pose proof H1 f H4 _ _ H6 H8.
    apply (H0 _ loc _) in H9.
    apply E_Reentry in H7.
    pose proof IHarbitrary_eval H1 (H _ _ _ H3) H9 H7.
    exact H10.
Qed.

End HoareWithCall.
(** [] *)


(** Conventional Hoare without call *)
Module HoareWithoutCall.
Import ASTWithoutCall.

Definition hoare_triple (fc : func_context) (lf : public_funcs) (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st1 st2,
    ceval fc lf c st1 st2 ->
    P st1 ->
    Q st2.

Definition func_triple (fc : func_context) (lf : public_funcs) (P : Assertion) (f : func) (Q : Assertion) : Prop :=
  forall st1 st2,
    ceval fc lf (func_bdy f) st1 st2 ->
    P st1 ->
    Q st2.

Notation "'|' fc ',' lf '|' '{{' P '}}' c '{{' Q '}}'" := (hoare_triple fc lf P c Q) (at level 90, c at next level).

Definition pv_to_assertion (fc : func_context) (f : func) (pv : list aexp) (P : Assertion) : Assertion :=
  fun st => P (param_to_local_state st (func_arg f) pv, snd st).

Theorem hoare_consequence : forall fc lf P P' Q Q' c,
  P |-- P' ->
  |fc, lf| {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  |fc, lf| {{P}} c {{Q}}.
Proof.
  intros.
  unfold hoare_triple. intros.
  apply H1. apply H in H3.
  pose proof H0 st1 st2 H2 H3.
  exact H4.
Qed.

Theorem hoare_reentry : forall fc lf P I,
  localp P ->
  globalp I ->
  (forall f, In f lf ->
      func_triple fc lf I f I) ->
  |fc, lf| {{ P AND I }} CReentry {{ P AND I }}.
Proof.
  unfold localp, globalp, hoare_triple, func_triple.
  intros.
(** Attempt arbitrary reentry *)
  inversion H2; subst.
  unfold andp in *.
  destruct H3.
  split; [eapply H; apply H3 | ].
  induction H4.
  - exact H5.
  - pose proof H0 _ loc1 _ H5.
    pose proof H1 f H4 _ _ H6 H8.
    apply (H0 _ loc _) in H9.
    apply E_Reentry in H7.
    pose proof IHarbitrary_eval H1 (H _ _ _ H3) H9 H7.
    exact H10.
Qed.

End HoareWithoutCall.
(** [] *)


(** Labelled Hoare with call *)
Module HoareLcWithCall.
Import ASTWithCall.
Import ASTLcWithCall.
Import LWithCall.

End HoareLcWithCall.
(** [] *)


(** Labelled Hoare without call *)
Module HoareLcWithoutCall.
Import ASTWithoutCall.
Import ASTLcWithoutCall.
Import LWithoutCall.

Definition valid_index_label (fc : func_context) (c : com) (lb : label) : Prop :=
  single_point lb /\ matched_label lb c.

Module COM.
Definition index_label_set (fc : func_context) (c : com) : Type :=
  sig (valid_index_label fc c).

Definition rAssertion (fc : func_context) (c : com) : Type :=
  forall i: index_label_set fc c, Assertion.
End COM.

Module FUN.
Definition index_label_set (fc : func_context) (f : func) : Type :=
  COM.index_label_set fc (func_bdy f).

Definition rAssertion (fc : func_context) (f : func) : Type :=
  COM.rAssertion fc (func_bdy f).
End FUN.

Record index_set (fc : func_context) (lf : list func) : Type := {
  fname : func;
  fvalid : In fname lf;
  index_label : FUN.index_label_set fc fname;
}.

Definition param_type (fc : func_context) (lf : list func) : Type :=
  index_set fc lf -> Type.

Definition invariants (fc : func_context) (lf : list func) (pt : param_type fc lf) : Type :=
  forall i: index_set fc lf, (pt i) -> Assertion.

Definition index_relation (fc : func_context) (lf : list func) (pt : param_type fc lf) : Type := forall i j : index_set fc lf, (pt i) -> (pt j) -> Prop.

Definition triple_PQ (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2,
      ceval' fc (func_bdy f) (top fc f) (bottom fc f) st1 st2 ->
      P st1 ->
      Q st2.

Definition triple_PR (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2 (i: FUN.index_label_set fc f),
      ceval' fc (func_bdy f) (top fc f) (proj1_sig i) st1 st2 ->
      P st1 ->
      R2 i st2.

Definition triple_RQ (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2 (i: FUN.index_label_set fc f),
      ceval' fc (func_bdy f) (proj1_sig i) (bottom fc f) st1 st2 ->
      R1 i st1 ->
      Q st2.

Definition triple_RR (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2 (i1 i2: FUN.index_label_set fc f),
      ceval' fc (func_bdy f) (proj1_sig i1) (proj1_sig i2) st1 st2 ->
      R1 i1 st1 ->
      R2 i2 st2.

Definition func_triple' (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    triple_PQ fc f P Q R1 R2
 /\ triple_PR fc f P Q R1 R2
 /\ triple_RQ fc f P Q R1 R2
 /\ triple_RR fc f P Q R1 R2.

End HoareLcWithoutCall.
(** [] *)

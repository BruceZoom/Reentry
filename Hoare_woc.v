Require Import Coq.Lists.List.
Require Import AST_woc.

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

(* dummy version of the Reentry Rule *)
(* The final version is in HoareFunc.v *)
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
(** [] *)

Require Import Coq.Lists.List.
Require Import AST_wc.
Require Import Hoare_wc.

Definition func_predicate : Type := func -> list (Assertion * Assertion).

Module Simple.

Definition triple_valid (fc : func_context) (lf : public_funcs) (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st1 st2,
    P st1 ->
    ceval fc lf c st1 st2 ->
    Q st2.

Definition fp_valid (fc : func_context) (lf : public_funcs) (fp : func_predicate) : Prop :=
  forall f P Q,
    In (P, Q) (fp f) ->
    triple_valid fc lf P (func_bdy f) Q.

Definition hoare_triple (fc : func_context) (lf : public_funcs) (fp : func_predicate) (P : Assertion) (c : com) (Q : Assertion) : Type :=
  fp_valid fc lf fp ->
  triple_valid fc lf P c Q.

Theorem hoare_call : forall fc lf fp f pv P Q,
  In (P, Q) (fp f) ->
  hoare_triple fc lf fp P (CCall f pv) Q.
Proof.
  unfold hoare_triple, fp_valid.
  intros.
Admitted.

Theorem hoare_reentry :
  forall P I,
    localp P ->
    globalp I ->
  forall fc lf fp,
    (forall f, In f lf ->
      In (I, I) (fp f)) ->
  hoare_triple fc lf fp (P AND I) CReentry (P AND I).
Proof.
  unfold hoare_triple, fp_valid, triple_valid.
  unfold andp.
  intros P I Hloc Hglb.
  intros.
  destruct H1.
  inversion H2; subst.
  split.
  - eapply Hloc.
    apply H1.
  - clear H1 H2.
    induction H4; [exact H3 |].
    specialize (IHarbitrary_eval H H0).
    pose proof H0 f I I (H _ H1) _ _ (Hglb _ _ _ H3) H2.
    apply IHarbitrary_eval.
    eapply Hglb.
    exact H5.
Qed.

End Simple.

Module Axiomatic.

Inductive hoare_triple : Type :=
  | Build_hoare_triple (P : Assertion) (c : com) (Q : Assertion).

Notation "{{ P }}  c  {{ Q }}" :=
  (Build_hoare_triple P c Q) (at level 90, c at next level).

Inductive provable (fc : func_context) (lf : public_funcs) (fp : func_predicate) : hoare_triple -> Prop :=
  | hoare_reentry : forall P I,
        localp P ->
        globalp I ->
        (forall f, In f lf ->
          In (I, I) (fp f)) ->
        provable fc lf fp ({{P AND I}} CReentry {{P AND I}}).

Notation "fc lf fp |--  tr" := (provable fc lf fp tr) (at level 91, no associativity).

Definition triple_valid (fc : func_context) (lf : public_funcs) (tr : hoare_triple) : Prop :=
  match tr with
  | {{P}} c {{Q}} =>
    forall st1 st2, P st1 -> ceval fc lf c st1 st2 -> Q st2
  end.

Notation "fc lf |== tr" := (triple_valid fc lf tr) (at level 91, no associativity).

Definition fp_valid (fc : func_context) (lf : public_funcs) (fp : func_predicate) : Prop :=
  forall f P Q,
    In (P, Q) (fp f) ->
    triple_valid fc lf ({{P}} (func_bdy f) {{Q}}).

Notation "fc lf ||== fp" := (fp_valid fc lf fp) (at level 91, no associativity).

Definition valid (fc : func_context) (lf : public_funcs) (fp : func_predicate) (tr : hoare_triple) : Prop :=
  fp_valid fc lf fp ->
  triple_valid fc lf tr.

Notation "fc lf fp |== tr" := (valid fc lf fp tr) (at level 91, no associativity).


Lemma reentry_sound fc lf fp :
  forall P I,
  localp P ->
  globalp I ->
  (forall f, In f lf ->
    In (I, I) (fp f)) ->
  valid fc lf fp ({{P AND I}} CReentry {{P AND I}}).
Proof.
  unfold valid, fp_valid, triple_valid.
  unfold andp.
  intros P I Hloc Hglb.
  intros.
  destruct H1.
  inversion H2; subst.
  split.
  - eapply Hloc.
    apply H1.
  - clear H1 H2.
    induction H4; [exact H3 |].
    specialize (IHarbitrary_eval H H0).
    pose proof H0 f I I (H _ H1) _ _ (Hglb _ _ _ H3) H2.
    apply IHarbitrary_eval.
    eapply Hglb.
    exact H5.
Qed.

Theorem hoare_sound: forall fc lf fp tr,
  provable fc lf fp tr ->
  valid fc lf fp tr.
Proof.
  intros.
  induction H.
  - apply reentry_sound; assumption.
Qed.



End Axiomatic.






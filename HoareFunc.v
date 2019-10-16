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

(* ceval' sigma c st1 st2

sg n
0 => _ _ _ => False
S n => ceval' (sg n)

sigma
exists n, sg n

ceval' sigma <-> ceval

Delta P f Q -> Delta |-- P f Q -> Delta |-- P c Q -> |== P c Q *)

Definition assn_sub (P : Assertion) (X : var) (a : aexp) : Assertion :=
  fun st => P (update_state st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub P X a) (at level 10, X at next level).

Inductive hoare_triple : Type :=
  | Build_hoare_triple (P : Assertion) (c : com) (Q : Assertion).

Notation "{{ P }}  c  {{ Q }}" :=
  (Build_hoare_triple P c Q) (at level 90, c at next level).

Inductive provable (fc : func_context) (lf : public_funcs) (fp : func_predicate) : hoare_triple -> Prop :=
  (* fixed reentry *)
  | hoare_reentry : forall P I,
      localp P ->
      globalp I ->
      (forall f, In f lf ->
        In (I, I) (fp f)) ->
      provable fc lf fp ({{P AND I}} CReentry {{P AND I}})
  (* function predicate call *)
  | hoare_call : forall f pv P Q R,
      globalp Q ->
      localp R ->
      In (P, Q) (fp f) ->
      provable fc lf fp ({{(pv_to_assertion fc f pv P) AND R}} CCall f pv {{Q AND R}})
  (* traditional ones *)
  | hoare_skip : forall (P : Assertion),
      provable fc lf fp ({{P}} CSkip {{P}})
  | hoare_asgn_bwd : forall (P : Assertion) (X : var) (E : aexp),
      provable fc lf fp ({{ P [ X |-> E] }} CAss X E {{ P }})
  | hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
      provable fc lf fp ({{P}} c1 {{Q}}) ->
      provable fc lf fp ({{Q}} c2 {{R}}) ->
      provable fc lf fp ({{P}} c1;;c2 {{R}})
  | hoare_if : forall (P Q : Assertion) (b : bexp) (c1 c2 : com),
      provable fc lf fp ({{ P AND {[b]} }} c1 {{ Q }}) ->
      provable fc lf fp ({{ P AND NOT {[b]} }} c2 {{ Q }}) ->
      provable fc lf fp ({{ P }} If b Then c1 Else c2 EndIf {{ Q }})
  | hoare_while_linear : forall P (b : bexp) c,
    provable fc lf fp ({{P AND {[b]}}} c {{P}}) ->
    provable fc lf fp ({{P}} While b Do c EndWhile {{P AND NOT {[b]}}})
  | hoare_consequence : forall (P P' Q Q' : Assertion) c,
      P |-- P' ->
      provable fc lf fp ({{P'}} c {{Q'}}) ->
      Q' |-- Q ->
      provable fc lf fp ({{P}} c {{Q}}).

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

(** Soundness *)
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

Lemma call_sound fc lf fp :
  forall f pv P Q R,
  globalp Q ->
  localp R ->
  In (P, Q) (fp f) ->
  valid fc lf fp ({{(pv_to_assertion fc f pv P) AND R}} CCall f pv {{Q AND R}}).
Proof.
  unfold valid, fp_valid, triple_valid.
  unfold andp.
  intros.
  inversion H4; subst.
  destruct H11 as [loc2 ?].
  destruct H3.
  split.
  - specialize (H2 _ _ _ H1).
    unfold pv_to_assertion in H1.
    specialize (H2 _ _ H3 H5).
    eapply H.
    exact H2.
  - eapply H0.
    exact H6.
Qed.

Theorem hoare_sound: forall fc lf fp tr,
  provable fc lf fp tr ->
  valid fc lf fp tr.
Proof.
  intros.
  induction H.
  - apply reentry_sound; assumption.
  - apply call_sound; assumption.
Admitted.
(** [] *)


Definition reentry_semantic fc lf (st1 st2 : state) : Prop :=
  match st1, st2 with
  | (loc1, glb1), (loc2, glb2) =>
      arbitrary_eval fc lf loc1 glb1 glb2 /\ loc1 = loc2
  end.

Theorem hoare_complete : forall fc lf fp tr,
  fp_valid fc lf fp ->
  valid fc lf fp tr ->
  provable fc lf fp tr.
Proof.
  intros.
  destruct tr.
  specialize (H0 H).
  unfold triple_valid in H0.
  induction c.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - remember ((fun st => exists st0, P st0 /\ reentry_semantic fc lf st0 st):Assertion) as I.
    epose proof hoare_consequence _ _ _ _ I _ I _ _ _ _.
    Unshelve.
    + exact H1.
    + unfold derives.
      intros.
      subst.
      exists st.
      split; [exact H1 |].
      destruct st as (loc, glb).
      simpl.
      split; [constructor | auto].
    + replace I with ((fun st => True) AND I).
      eapply hoare_reentry.
      * unfold localp.
        intros. exact H1.
      * unfold globalp.
        subst. unfold reentry_semantic.
        intros.
        destruct H1 as [[loc0 glb0] [? [? ?]]].
        subst.
        exists (loc2, glb0). admit.
      * admit.
      * unfold andp.
        admit.
    + admit.
Admitted.


End Axiomatic.






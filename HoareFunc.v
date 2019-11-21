Require Import Coq.Lists.List.
Require Import AST_wc.
Require Import Hoare_wc.

Require Import Omega.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Require Import FunctionalExtensionality.

Fixpoint iter_loop_body (b : bexp) (loop_body : state -> state -> Prop) (n : nat): state -> state -> Prop :=
  match n with
  | O => fun st1 st2 => st1 = st2 /\ beval st1 b = false
  | S n' => fun st1 st3 => (exists st2, loop_body st1 st2 /\ iter_loop_body b loop_body n' st2 st3 /\ beval st1 b = true)
  end.

Definition while_body_sem (b : bexp) (loop_body : state -> state -> Prop) st1 st2 : Prop :=
  loop_body st1 st2 /\ beval st1 b = true.

Definition while_sem b loop_body : state -> state -> Prop :=
  clos_refl_trans (while_body_sem b loop_body).

Definition while_sem_1n b loop_body : state -> state -> Prop :=
  clos_refl_trans_1n (while_body_sem b loop_body).

Definition while_sem_n1 b loop_body : state -> state -> Prop :=
  clos_refl_trans_n1 (while_body_sem b loop_body).

Definition semantic : Type := func_context -> public_funcs -> com -> state -> state -> Prop.

Inductive ceval' (sigma : semantic) (fc : func_context) (lf : public_funcs) : com -> state -> state -> Prop :=
  | E'_Skip : forall st,
      ceval' sigma fc lf CSkip st st
  | E'_Ass : forall st X a n,
      aeval st a = n ->
      ceval' sigma fc lf (CAss X a) st (update_state st X n)
  | E'_Seq : forall c1 c2 st1 st2 st3,
      ceval' sigma fc lf c1 st1 st2 ->
      ceval' sigma fc lf c2 st2 st3 ->
      ceval' sigma fc lf (CSeq c1 c2) st1 st3
  | E'_IfTrue : forall b c1 c2 st1 st2,
      beval st1 b = true ->
      ceval' sigma fc lf c1 st1 st2 ->
      ceval' sigma fc lf (CIf b c1 c2) st1 st2
  | E'_IfFalse : forall b c1 c2 st1 st2,
      beval st1 b = false ->
      ceval' sigma fc lf c2 st1 st2 ->
      ceval' sigma fc lf (CIf b c1 c2) st1 st2
  | E'_WhileFalse : forall b c st,
      beval st b = false ->
      ceval' sigma fc lf (CWhile b c) st st
  | E'_WhileTrue : forall b c st1 st2 st3,
      beval st1 b = true ->
      ceval' sigma fc lf c st1 st2 ->
      ceval' sigma fc lf (CWhile b c) st2 st3 ->
      ceval' sigma fc lf (CWhile b c) st1 st3
  | E'_Call : forall f pv loc1 loc2 glb1 glb2,
      sigma fc lf (func_bdy f) ((param_to_local_state (loc1, glb1) (func_arg f) pv), glb1) (loc2, glb2) ->
      ceval' sigma fc lf (CCall f pv) (loc1, glb1) (loc1, glb2)
  | E'_Reentry : forall loc glb1 glb2,
      arbitrary_eval' sigma fc lf glb1 glb2 ->
      ceval' sigma fc lf CReentry (loc, glb1) (loc, glb2)
with arbitrary_eval' (sigma: semantic) (fc: func_context) (lf: public_funcs): unit_state -> unit_state -> Prop :=
  | ArE'_nil: forall gl, arbitrary_eval' sigma fc lf gl gl
(*   | ArE'_cons: forall loc loc1 loc2 gl1 gl2 gl3 f, *)
  | ArE'_cons: forall loc pv gl1 gl2 gl3 f,
      In f lf ->
(*       sigma fc lf (func_bdy f) (loc1, gl1) (loc2, gl2) -> *)
      ceval' sigma fc lf (CCall f pv) (loc, gl1) (loc, gl2) ->
      arbitrary_eval' sigma fc lf gl2 gl3 ->
      arbitrary_eval' sigma fc lf gl1 gl3.


Module FixpointSigma.
Fixpoint sg (n : nat) : semantic :=
  match n with
  | 0 => fun _ _ _ _ _ => False
  | S n => ceval' (sg n)
  end.

Lemma sg_mono_inc : forall fc lf c st1 st2 n m,
  sg n fc lf c st1 st2 -> sg (n + m) fc lf c st1 st2.
Proof.
  intros.
  revert H.
  revert c st1 st2 m.
  induction n; intros; [inversion H |].
  simpl in *.
  induction H.
  - constructor.
  - constructor.
    auto.
  - eapply E'_Seq.
    + apply IHceval'1.
    + apply IHceval'2.
  - apply E'_IfTrue; auto.
  - apply E'_IfFalse; auto.
  - apply E'_WhileFalse; auto.
  - eapply E'_WhileTrue; auto.
    + apply IHceval'1.
    + apply IHceval'2.
  - eapply E'_Call.
    apply IHn.
    apply H.
  - apply E'_Reentry.
    induction H.
    + apply ArE'_nil.
    + eapply ArE'_cons.
      * apply H.
      * inversion H0; subst.
        eapply E'_Call.
        apply IHn.
        apply H3.
      * apply IHarbitrary_eval'.
Qed.

Lemma arbitrary_eval'_mono_inc : forall fc lf gl1 gl2 n1 n2,
  arbitrary_eval' (sg n1) fc lf gl1 gl2 ->
  arbitrary_eval' (sg (n1 + n2)) fc lf gl1 gl2.
Proof.
  intros.
  revert H.
  revert gl1 gl2 n2.
  induction n1; intros.
  - inversion H; subst.
    + apply ArE'_nil.
    + inversion H1.
      inversion H4.
  - induction H.
   + apply ArE'_nil.
   + eapply ArE'_cons.
    * apply H.
    * inversion H0; subst.
      eapply E'_Call.
      apply sg_mono_inc.
      apply H3.
    * apply IHarbitrary_eval'.
Qed.

Definition sigma (fc: func_context) (lf: public_funcs) (c: com) (st1 st2: state) : Prop :=
  exists n, sg n fc lf c st1 st2.

Lemma sigma_ceval'_equiv fc lf c st1 st2:
  sigma fc lf c st1 st2 <-> ceval' sigma fc lf c st1 st2.
Proof.
  split; intros.
  {
    destruct H as [n ?].
    destruct n; [inversion H |].
    simpl in H.
    induction H; subst.
    - apply E'_Skip.
    - apply E'_Ass.
      auto.
    - eapply E'_Seq.
      + apply IHceval'1.
      + apply IHceval'2.
    - apply E'_IfTrue; auto.
    - apply E'_IfFalse; auto.
    - apply E'_WhileFalse; auto.
    - eapply E'_WhileTrue.
      + apply H.
      + apply IHceval'1.
      + apply IHceval'2.
    - eapply E'_Call.
      exists n.
      apply H.
    - apply E'_Reentry.
      induction H.
      + apply ArE'_nil.
      + eapply ArE'_cons.
        * apply H.
        * inversion H0; subst.
          eapply E'_Call.
          exists n.
          apply H3.
        * auto.
  }
  {
    induction H.
    - exists 1; simpl.
      apply E'_Skip.
    - exists 1; simpl.
      apply E'_Ass.
      auto.
    - destruct IHceval'1 as [n1 ?].
      destruct IHceval'2 as [n2 ?].
      exists (S n1 + n2).
      simpl.
      eapply E'_Seq.
      + pose proof sg_mono_inc _ _ _ _ _ _ (S n2) H1.
        replace (n1 + S n2) with (S n1 + n2) in H3; [| omega].
        apply H3.
      + pose proof sg_mono_inc _ _ _ _ _ _ (S n1) H2.
        replace (n2 + S n1) with (S n1 + n2) in H3; [| omega].
        apply H3.
    - destruct IHceval' as [n ?].
      exists (S n).
      simpl.
      apply E'_IfTrue; auto.
      replace (ceval' (sg n)) with (sg (S n)); auto.
      replace (S n) with (n + 1); try omega.
      eapply sg_mono_inc in H1.
      apply H1.
    - destruct IHceval' as [n ?].
      exists (S n).
      simpl.
      apply E'_IfFalse; auto.
      replace (ceval' (sg n)) with (sg (S n)); auto.
      replace (S n) with (n + 1); try omega.
      eapply sg_mono_inc in H1.
      apply H1.
    - exists 1; simpl.
      apply E'_WhileFalse; auto.
    - destruct IHceval'1 as [n1 ?].
      destruct IHceval'2 as [n2 ?].
      exists (S n1 + n2).
      simpl.
      eapply E'_WhileTrue; auto.
      + pose proof sg_mono_inc _ _ _ _ _ _ (S n2) H2.
        replace (n1 + S n2) with (S n1 + n2) in H4; [| omega].
        apply H4.
      + pose proof sg_mono_inc _ _ _ _ _ _ (S n1) H3.
        replace (n2 + S n1) with (S n1 + n2) in H4; [| omega].
        apply H4.
    - destruct H as [n ?].
      exists (S n).
      simpl.
      eapply E'_Call.
      apply H.
    - induction H.
      + exists 1; simpl.
        apply E'_Reentry.
        apply ArE'_nil.
      + inversion H0; subst.
        destruct H3 as [n1 ?].
        destruct IHarbitrary_eval' as [n2 ?].
        apply (sg_mono_inc _ _ _ _ _ _ 1) in H3.
        replace (n2 + 1) with (S n2) in H3; [| omega].
        simpl in H3.
        inversion H3; subst.
        exists (S n1 + n2); simpl.
        apply E'_Reentry.
        eapply ArE'_cons.
        * apply H.
        * eapply E'_Call.
          apply sg_mono_inc.
          apply H2.
        * rewrite Nat.add_comm.
          apply arbitrary_eval'_mono_inc.
          apply H7.
  }
Qed.

Lemma sg_n_ceval n fc lf: forall c st1 st2,
  sg n fc lf c st1 st2 -> ceval fc lf c st1 st2.
Proof.
  induction n; intros.
  + simpl in H.
    inversion H.
  + simpl in H.
    induction H; subst.
    * apply E_Skip.
    * apply E_Ass; auto.
    * apply E_Seq with st2; auto.
    * apply E_IfTrue; auto.
    * apply E_IfFalse; auto.
    * apply E_WhileFalse; auto.
    * apply E_WhileTrue with st2; auto.
    * eapply E_Call.
      apply IHn.
      apply H.
    * apply E_Reentry.
      induction H.
      - apply ArE_nil.
      - inversion H0; subst.
        eapply ArE_cons.
        ++ apply H.
        ++ apply IHn in H3.
           eapply E_Call.
           apply H3.
        ++ apply IHarbitrary_eval'.
Qed.

Lemma ceval'_ceval (fc: func_context) (lf: public_funcs) (c: com) (st1 st2: state) :
  ceval' sigma fc lf c st1 st2 -> ceval fc lf c st1 st2.
Proof.
  intros.
  induction H.
  - apply E_Skip.
  - apply E_Ass; auto.
  - apply E_Seq with st2; auto.
  - apply E_IfTrue; auto.
  - apply E_IfFalse; auto.
  - apply E_WhileFalse; auto.
  - apply E_WhileTrue with st2; auto.
  - destruct H as [n ?].
    eapply E_Call.
    apply sg_n_ceval in H.
    apply H.
  - apply E_Reentry.
    induction H.
    + apply ArE_nil.
    + inversion H0; subst.
      destruct H3.
      apply sg_n_ceval in H2.
      eapply ArE_cons.
      * apply H.
      * eapply E_Call.
        apply H2.
      * apply IHarbitrary_eval'.
Qed.

Lemma abeval'_abeval (fc: func_context) (lf: public_funcs) (glb1 glb2: unit_state) :
  arbitrary_eval' sigma fc lf glb1 glb2 -> arbitrary_eval fc lf glb1 glb2.
Proof.
  intros.
  induction H.
  + apply ArE_nil.
  + (* Possibly the follwing line causes the trouble *)
    inversion H0; subst.
    apply sigma_ceval'_equiv in H3.
    apply ceval'_ceval in H3.
    apply E_Call in H3.
    pose proof ArE_cons _ _ _ _ _ _ _ _ H H3 IHarbitrary_eval'.
    apply H2.
Qed.

Lemma ceval_ceval' (fc: func_context) (lf: public_funcs) (c: com) (st1 st2: state) :
  ceval fc lf c st1 st2 -> ceval' sigma fc lf c st1 st2
with abeval_abeval' (fc: func_context) (lf: public_funcs) (glb1 glb2: unit_state) :
  arbitrary_eval fc lf glb1 glb2 -> arbitrary_eval' sigma fc lf glb1 glb2.
Proof.
{
  clear ceval_ceval'.
  intros.
  induction H.
  - apply E'_Skip.
  - apply E'_Ass; auto.
  - apply E'_Seq with st2; auto.
  - apply E'_IfTrue; auto.
  - apply E'_IfFalse; auto.
  - apply E'_WhileFalse; auto.
  - apply E'_WhileTrue with st2; auto.
  - eapply E'_Call.
    rewrite sigma_ceval'_equiv.
    apply IHceval.
  - apply E'_Reentry.
    apply abeval_abeval'.
    exact H.
}
{
  clear abeval_abeval'.
  intros.
  induction H.
  - apply ArE'_nil.
  - apply ceval_ceval' in H0.
    eapply ArE'_cons.
    + apply H.
    + apply H0.
    + apply IHarbitrary_eval.
}
Qed.

Lemma ceval'_ceval_equiv (fc: func_context) (lf: public_funcs) (c: com) (st1 st2: state) :
  ceval' sigma fc lf c st1 st2 <-> ceval fc lf c st1 st2
with abeval'_abeval_equiv (fc: func_context) (lf: public_funcs) (glb1 glb2: unit_state) :
  arbitrary_eval' sigma fc lf glb1 glb2 <-> arbitrary_eval fc lf glb1 glb2.
Proof.
  - clear ceval'_ceval_equiv.
    pose proof ceval_ceval' fc lf c st1 st2.
    pose proof ceval'_ceval fc lf c st1 st2.
    tauto.
  - clear abeval'_abeval_equiv.
    pose proof abeval_abeval' fc lf glb1 glb2.
    pose proof abeval'_abeval fc lf glb1 glb2.
    tauto.
Qed.
End FixpointSigma.


Module HoareLogic.
Definition func_predicate : Type := func -> Assertion -> Assertion -> Prop.

Definition assn_sub (P : Assertion) (X : var) (a : aexp) : Assertion :=
  fun st => P (update_state st X (aeval st a)).
Notation "P [ X |-> a ]" := (assn_sub P X a) (at level 10, X at next level).

Inductive hoare_triple : Type :=
  | Build_hoare_triple (P : Assertion) (c : com) (Q : Assertion).
Notation "{{ P }}  c  {{ Q }}" :=
  (Build_hoare_triple P c Q) (at level 90, c at next level).

Inductive provable (fc : func_context) (lf : public_funcs) (fp : func_predicate) : hoare_triple -> Prop :=
  (* fixed reentry *)
  | hoare_reentry : forall A (P I: A -> Assertion),
    (forall x, localp (P x)) ->
    (forall x,  globalp (I x))->
      (forall f x, In f lf -> fp f (I x) (I x)) ->
      provable fc lf fp ({{fun st => exists x, P x st /\ I x st}} CReentry {{fun st => exists x, P x st /\ I x st}})
  (* function predicate call *)
  | hoare_call : forall A f pv (Q P R: A -> Assertion),
      (forall x, fp f (P x) (Q x)) ->
      (forall x, globalp (Q x)) ->
      (forall x, localp (R x)) ->
      provable fc lf fp ({{fun st => exists x, (pv_to_assertion fc f pv (P x)) st /\ R x st}} CCall f pv {{fun st => exists x, Q x st /\ R x st}})
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
  | hoare_while : forall P (b : bexp) c,
    provable fc lf fp ({{P AND {[b]}}} c {{P}}) ->
    provable fc lf fp ({{P}} While b Do c EndWhile {{P AND NOT {[b]}}})
  | hoare_consequence : forall (P P' Q Q' : Assertion) c,
      P |-- P' ->
      provable fc lf fp ({{P'}} c {{Q'}}) ->
      Q' |-- Q ->
      provable fc lf fp ({{P}} c {{Q}}).
Notation "fc lf fp |--  tr" := (provable fc lf fp tr) (at level 91, no associativity).

Definition triple_valid (sigma: semantic) (fc : func_context) (lf : public_funcs) (tr : hoare_triple) : Prop :=
  match tr with
  | {{P}} c {{Q}} =>
    forall st1 st2, P st1 -> sigma fc lf c st1 st2 -> Q st2
  end.
Notation "sigma fc lf |== tr" := (triple_valid sigma fc lf tr) (at level 91, no associativity).

Definition valid (fc: func_context) (lf: public_funcs) (tr: hoare_triple) : Prop := triple_valid ceval fc lf tr.
Notation "fc lf |== tr" := (valid fc lf tr) (at level 91, no associativity).

Definition fp_valid (sigma: semantic) (fc : func_context) (lf : public_funcs) (fp : func_predicate) : Prop :=
  forall f P Q,
(*     fp f P Q -> P st1 -> ceval fc lf (func_bdy f) st1 st2 -> Q st2. *)
    fp f P Q -> triple_valid sigma fc lf ({{P}} (func_bdy f) {{Q}}).
Notation "sigma fc lf ||== fp" := (fp_valid sigma fc lf fp) (at level 91, no associativity).

(** Weak Valid *)
Definition weak_valid (sigma: semantic) (fc : func_context) (lf : public_funcs) (fp : func_predicate) (tr : hoare_triple) : Prop :=
  fp_valid sigma fc lf fp ->
  triple_valid (ceval' sigma) fc lf tr.
Notation "sigma fc lf fp |== tr" := (weak_valid sigma fc lf fp tr) (at level 91, no associativity).
End HoareLogic.

(** Soundness *)
Module Soundness.
Import HoareLogic.

Lemma reentry_sound_weak sigma fc lf (fp: func_predicate) :
  forall A (P I: A -> Assertion),
  (forall x, localp (P x)) ->
  (forall x, globalp (I x)) ->
  (forall f x, In f lf -> fp f (I x) (I x)) ->
  weak_valid sigma fc lf fp ({{fun st => exists x, P x st /\ I x st}} CReentry {{fun st => exists x, P x st /\ I x st}}).
Proof.
  unfold weak_valid, fp_valid, triple_valid.
  unfold andp.
  intros A P I Hloc Hglb.
  intros.
  destruct H1 as [? [? ?]].
  exists x.
  inversion H2; subst.
  split; [eapply Hloc; apply H1 |].
  clear H1 H2.
  induction H4; [exact H3 |].
  apply IHarbitrary_eval'; clear IHarbitrary_eval'.
  inversion H2; subst.
  remember (param_to_local_state (loc0, gl1) (func_arg f) pv) as loc1.
  pose proof H0 _ _ _ (H _ _ H1) _ (loc2, gl2) (Hglb _ _ loc1 _ H3) H6.
  eapply Hglb.
  apply H5.
Qed.

Lemma call_sound_weak sigma fc lf (fp: func_predicate) :
  forall A f pv (Q P R : A -> Assertion),
  (forall x, fp f (P x) (Q x)) ->
  (forall x, globalp (Q x)) ->
  (forall x, localp (R x)) ->
  weak_valid sigma fc lf fp ({{fun st => exists x, (pv_to_assertion fc f pv (P x)) st /\ R x st}} CCall f pv {{fun st => exists x, Q x st /\ R x st}}).
Proof.
  unfold weak_valid, fp_valid, triple_valid.
  unfold andp.
  intros.
  inversion H4; subst.
  destruct H3 as [? [? ?]].
  exists x.
  split.
  - unfold pv_to_assertion in H3.
    pose proof H2 _ _ _ (H x) _ _ H3 H9.
    eapply H0.
    apply H6.
  - eapply H1.
    apply H5.
Qed.

Lemma skip_sound_weak sigma fc lf (fp: func_predicate) :
  forall P,
  weak_valid sigma fc lf fp ({{P}} CSkip {{P}}).
Proof.
  unfold weak_valid, fp_valid, triple_valid.
  intros.
  inversion H1; subst; auto.
Qed.

Lemma assgn_sound_weak sigma fc lf (fp: func_predicate) :
  forall P X E,
  weak_valid sigma fc lf fp ({{P [X |-> E] }} CAss X E {{P}}).
Proof.
  unfold weak_valid, fp_valid, triple_valid.
  intros.
  inversion H1; subst; auto.
Qed.

Lemma seq_sound_weak sigma fc lf (fp: func_predicate) :
  forall P Q R c1 c2,
  weak_valid sigma fc lf fp ({{P}} c1 {{Q}}) ->
  weak_valid sigma fc lf fp ({{Q}} c2 {{R}}) ->
  weak_valid sigma fc lf fp ({{P}} c1;; c2 {{R}}).
Proof.
  unfold weak_valid, triple_valid.
  intros.
  inversion H3; subst.
  pose proof H H1 _ _ H2 H6.
  pose proof H0 H1 _ _ H4 H9.
  auto.
Qed.

Lemma if_sound_weak sigma fc lf (fp: func_predicate) :
  forall P b Q c1 c2,
  weak_valid sigma fc lf fp ({{P AND {[b]}}} c1 {{Q}}) ->
  weak_valid sigma fc lf fp ({{P AND NOT {[b]}}} c2 {{Q}}) ->
  weak_valid sigma fc lf fp ({{P}} If b Then c1 Else c2 EndIf {{Q}}).
Proof.
  unfold weak_valid, triple_valid.
  intros.
  inversion H3; subst.
  - eapply H; auto.
    + unfold andp.
      split; [apply H2 | apply H9].
    + auto.
  - eapply H0; auto.
    + unfold andp, notp, not.
      split; [apply H2 | congruence].
    + auto.
Qed.

Lemma while_sem_equiv fc lf sigma:
  forall b c st1 st2,
  (exists n, iter_loop_body b (ceval' sigma fc lf c) n st1 st2) <->
  ceval' sigma fc lf (CWhile b c) st1 st2.
Proof.
  split; intros.
  - destruct H as [n ?].
    revert H.
    revert c st1 st2.
    induction n; intros.
    + simpl in H.
      destruct H; subst.
      apply E'_WhileFalse; auto.
    + simpl in H.
      destruct H as [st3 [? [? ?]]].
      apply E'_WhileTrue with st3; auto.
  - remember (While b Do c EndWhile) as c'.
    induction H; subst; inversion Heqc'; subst.
    + exists 0.
      simpl.
      tauto.
    + specialize (IHceval'2 eq_refl).
      destruct IHceval'2 as [n ?].
      exists (S n).
      simpl.
      exists st2; split; auto.
Qed.

Lemma while_sound_weak sigma fc lf (fp: func_predicate) :
  forall P c b,
  weak_valid sigma fc lf fp ({{P AND {[b]}}} c {{P}}) ->
  weak_valid sigma fc lf fp ({{P}} While b Do c EndWhile {{P AND NOT {[b]}}}).
Proof.
  unfold weak_valid, triple_valid.
  intros.
  rewrite <- while_sem_equiv in H2.
  destruct H2 as [n ?].
  revert H1 H2.
  revert st1 st2.
  induction n; intros.
  - destruct H2 as [? ?]; subst.
    unfold andp, notp; split; auto.
    unfold bassn, not.
    congruence.
  - simpl in H2.
    destruct H2 as [st3 [? [? ?]]].
    apply IHn with st3; auto.
    apply H with st1; auto.
    unfold andp, bassn.
    tauto.
Qed.

Lemma consequence_sound_weak sigma fc lf (fp: func_predicate) :
  forall P Q P' Q' c,
  P |-- P' ->
  Q' |-- Q ->
  weak_valid sigma fc lf fp ({{P'}} c {{Q'}}) ->
  weak_valid sigma fc lf fp ({{P}} c {{Q}}).
Proof.
  unfold weak_valid, triple_valid.
  intros.
  apply H in H3.
  apply H0.
  eapply H1; auto.
  + apply H3.
  + auto.
Qed.

Theorem hoare_sound_weak : forall sigma fc lf fp tr,
  provable fc lf fp tr ->
  weak_valid sigma fc lf fp tr.
Proof.
  intros.
  induction H.
  - apply reentry_sound_weak; auto.
  - apply call_sound_weak; auto.
  - apply skip_sound_weak; auto.
  - apply assgn_sound_weak; auto.
  - apply seq_sound_weak with Q; auto.
  - apply if_sound_weak; auto.
  - apply while_sound_weak; auto.
  - apply consequence_sound_weak with P' Q'; auto.
Qed.

Import FixpointSigma.

Lemma sg_n_fp_valid : forall n fc lf (fp: func_predicate),
  (forall f P Q, fp f P Q ->
    provable fc lf fp ({{P}} (func_bdy f) {{Q}})) ->
  fp_valid (sg n) fc lf fp.
Proof.
  intros.
  induction n; intros.
  - unfold fp_valid, triple_valid.
    simpl.
    intros.
    inversion H2.
  - unfold fp_valid, triple_valid.
    intros.
    pose proof H f P Q H0.
    apply (hoare_sound_weak (sg n)) in H3.
    unfold weak_valid in H3.
    specialize (H3 IHn).
    simpl in H2, H3.
    eapply H3.
    + apply H1.
    + apply H2.
Qed.

Lemma sigma_fp_valid : forall fc lf (fp: func_predicate),
  (forall f P Q, fp f P Q ->
    provable fc lf fp ({{P}} (func_bdy f) {{Q}})) ->
  fp_valid sigma fc lf fp.
Proof.
  intros.
  unfold fp_valid, triple_valid.
  intros.
  destruct H2 as [n ?].
  pose proof sg_n_fp_valid n fc lf fp H.
  unfold fp_valid, triple_valid in H3.
  eapply H3.
  - apply H0.
  - apply H1.
  - apply H2.
Qed.

(* (Delta P f Q -> Delta |-- P f Q) -> Delta |-- P c Q -> |== P c Q *)
Theorem hoare_sound: forall fc lf (fp : func_predicate),
  (forall f P Q, fp f P Q ->
      provable fc lf fp ({{P}} (func_bdy f) {{Q}})) ->
  forall tr, provable fc lf fp tr ->
      valid fc lf tr.
Proof.
  intros.
  pose proof sigma_fp_valid _ _ _ H.
  pose proof hoare_sound_weak sigma _ _ _ _ H0 H1.
  destruct tr.
  simpl in *.
  intros.
  eapply H2.
  - apply H3.
  - rewrite ceval'_ceval_equiv.
    apply H4.
Qed.

End Soundness.
(** [] *)

Module abevals.

Definition reCall_semantic fc lf : unit_state -> unit_state -> Prop :=
  fun glb1 glb2 => exists f pv loc,
    In f lf /\
    ceval fc lf (CCall f pv) (loc, glb1) (loc, glb2).

Definition abeval_n1 fc lf := clos_refl_trans_n1 (reCall_semantic fc lf).

Definition abeval_1n fc lf := clos_refl_trans_1n (reCall_semantic fc lf).

Definition abeval fc lf := clos_refl_trans (reCall_semantic fc lf).

Lemma arbitrary_eval_abeval_1n fc lf : forall glb1 glb2,
  arbitrary_eval fc lf glb1 glb2 <-> abeval_1n fc lf glb1 glb2.
Proof.
  split; intros.
  {
    induction H.
    - apply rt1n_refl.
    - eapply rt1n_trans; [| apply IHarbitrary_eval].
      unfold reCall_semantic.
      exists f, pv, loc.
      auto.
  }
  {
    induction H.
    - apply ArE_nil.
    - destruct H as [f [pv [loc [? ?]]]].
      eapply ArE_cons.
      + apply H.
      + apply H1.
      + apply IHclos_refl_trans_1n. 
  }
Qed.

Lemma abeval_1n_n1_iff fc lf : forall glb1 glb2,
  abeval_1n fc lf glb1 glb2 <-> abeval_n1 fc lf glb1 glb2.
Proof.
  intros.
  unfold abeval_1n, abeval_n1.
  rewrite <- Operators_Properties.clos_rt_rt1n_iff.
  rewrite <- Operators_Properties.clos_rt_rtn1_iff.
  tauto.
Qed.
End abevals.

(** Completeness *)
Module Completeness.

Definition reentry_semantic fc lf (st1 st2 : state) : Prop :=
  match st1, st2 with
  | (loc1, glb1), (loc2, glb2) =>
      arbitrary_eval fc lf glb1 glb2 /\ loc1 = loc2
  end.

Import HoareLogic.
Import abevals.

Lemma hoare_reentry_complete: forall fc lf fp P Q,
  valid fc lf ({{P}} Re {{Q}}) ->
  fp = (fun (f : func) (P Q : Assertion) => valid fc lf ({{P}} func_bdy f {{Q}})) ->
  provable fc lf fp ({{P}} Re {{Q}}).
Proof.
  intros.
  remember ((fun loc (st:state) => fst st = loc):unit_state -> Assertion) as P'.
  remember ((fun loc (st:state) => exists glb0, P (loc, glb0) /\ arbitrary_eval fc lf glb0 (snd st)):unit_state -> Assertion) as I.
  remember (fun st => exists loc, P' loc st /\ I loc st) as R.
  apply (hoare_consequence _ _ _ _ R _ R _).
  + unfold derives.
    intros.
    destruct st as [loc glb].
    subst.
    exists loc; split; auto.
    exists glb; repeat split; auto.
(*     exists (loc, glb); repeat split; auto. *)
    apply ArE_nil.
  + subst R.
    eapply hoare_reentry.
    * unfold localp.
      intros.
      subst P'.
      auto.
    * intros loc.
      unfold globalp.
      intros.
      subst.
      destruct H1 as [glb0 [? ?]].
      subst.
      exists glb0.
      repeat split; auto.
    * intros f loc.
      subst.
      simpl.
      intros.
      destruct H1 as [glb0 [? ?]].
      destruct st1 as [loc1 glb1].
      destruct st2 as [loc2 glb2].
      exists glb0.
      split; auto.
      simpl in *.
      pose proof undo_param_existence loc1 glb1 (func_arg f) as [loc' [pv ?]].
      pose proof E_Call fc lf f pv loc' loc2 glb1 glb2.
      rewrite H4 in H5.
      specialize (H5 H2).
      assert (reCall_semantic fc lf glb1 glb2).
      {
        unfold reCall_semantic.
        exists f, pv, loc'.
        auto.
      }
(*       destruct H3. *)
(*       split; auto. *)
      rewrite arbitrary_eval_abeval_1n in *.
      rewrite abeval_1n_n1_iff in *.
      eapply rtn1_trans.
      -- apply H6.
      -- apply H3.
  + unfold derives.
    intros. subst.
    destruct H1 as [loc [? [glb0 [? ?]]]].
    destruct st as [loc' glb].
    simpl in H0. subst.
    simpl in *.
    eapply H.
    - apply H1.
    - apply E_Reentry.
      apply H2.
Qed.

Lemma hoare_call_complete: forall fc lf fp f prms P Q,
  valid fc lf ({{P}} f [(prms)] {{Q}}) ->
  fp = (fun (f : func) (P Q : Assertion) => valid fc lf ({{P}} func_bdy f {{Q}})) ->
  provable fc lf fp ({{P}} f [(prms)] {{Q}}).
Proof.
  intros.
  pose proof hoare_call.
  remember (fun loc (st:state) => fst st = loc) as R.
  assert (forall x, localp (R x)).
  {
    unfold localp.
    intros.
    subst.
    simpl in *.
    auto.
  }
  (* construct the inverse (st |== P') ~ (st' |== P) *)
  remember (fun st' (st:state) => P st' /\ st = (param_to_local_state st' (func_arg f) prms, snd st')) as P'.
  assert (P |-- (fun st => exists x, (pv_to_assertion fc f prms (P' x)) st /\ R (fst x) st)).
  {
    unfold derives, pv_to_assertion.
    subst.
    intros.
    simpl.
    exists st.
    destruct st.
    split; auto.
  }
  remember (fun x (st:state) => exists st0 loc, P' x st0 /\ ceval fc lf (func_bdy f) st0 (loc, snd st)) as Q'.
  eapply (hoare_consequence _ _ _ _ _ _ (fun st => exists x, Q' x st /\ R (fst x) st)).
  - apply H3.
  - eapply hoare_call.
    + subst.
      unfold valid, triple_valid.
      intros.
      destruct st2.
      exists st1, u.
      simpl.
      auto.
    + subst.
      unfold globalp.
      intros.
      destruct H0 as [? [? ?]].
      exists x0, x1.
      auto.
    + subst.
      unfold localp.
      intros.
      simpl in *.
      auto.
  - subst.
    unfold derives.
    intros.
    destruct H0 as [? [[? [? [[? ?] ?]]] ?]].
    destruct x, x0.
    inversion H4; subst.
    simpl in *.
    eapply E_Call in H5.
    eapply H in H5; auto.
    subst.
    destruct st.
    auto.
Qed.

Lemma derives_refl: forall P, P |-- P.
Proof.
  unfold derives; auto.
Qed.

Lemma hoare_skip_complete:
  forall fc lf fp P Q,
  valid fc lf ({{P}} Skip {{Q}}) ->
  provable fc lf fp ({{P}} Skip {{Q}}).
Proof.
  unfold valid, triple_valid.
  intros.
  eapply hoare_consequence.
  + apply derives_refl.
  + apply hoare_skip.
  + unfold derives.
    intros.
    eapply H.
    - apply H0.
    - apply E_Skip.
Qed.

Lemma hoare_assn_complete:
  forall fc lf fp P Q X E,
  valid fc lf ({{P}} CAss X E {{Q}}) ->
  provable fc lf fp ({{P}} CAss X E {{Q}}).
Proof.
  unfold valid, triple_valid.
  intros.
  eapply hoare_consequence; [| | apply derives_refl].
  2:{
    apply hoare_asgn_bwd.
  }
  unfold derives.
  intros.
  eapply H; [apply H0 |].
  apply E_Ass; auto.
Qed.

Lemma hoare_seq_complete:
  forall fc lf fp P Q c1 c2,
  (forall P Q : Assertion, valid fc lf ({{P}} c1 {{Q}}) -> provable fc lf fp ({{P}} c1 {{Q}})) ->
  (forall P Q : Assertion, valid fc lf ({{P}} c2 {{Q}}) -> provable fc lf fp ({{P}} c2 {{Q}})) ->
  valid fc lf ({{P}} c1;; c2 {{Q}}) ->
  provable fc lf fp ({{P}} c1;; c2 {{Q}}).
Proof.
  unfold valid, triple_valid.
  intros.
  remember (fun st:state => exists st1, P st1 /\ ceval fc lf c1 st1 st) as R.
  eapply hoare_seq with R.
  - eapply H.
    intros; subst.
    exists st1; auto.
  - eapply H0.
    intros; subst.
    destruct H2 as [st3 [? ?]].
    eapply H1.
    + apply H2.
    + eapply E_Seq with st1; auto.
Qed.

Lemma hoare_if_complete:
  forall fc lf fp P Q c1 c2 b,
  (forall P Q : Assertion, valid fc lf ({{P}} c1 {{Q}}) -> provable fc lf fp ({{P}} c1 {{Q}})) ->
  (forall P Q : Assertion, valid fc lf ({{P}} c2 {{Q}}) -> provable fc lf fp ({{P}} c2 {{Q}})) ->
  valid fc lf ({{P}} If b Then c1 Else c2 EndIf {{Q}}) ->
  provable fc lf fp ({{P}} If b Then c1 Else c2 EndIf {{Q}}).
Proof.
  unfold valid, triple_valid.
  intros.
  apply hoare_if.
  - apply H; intros.
    unfold andp in H2.
    destruct H2.
    eapply H1.
    + apply H2.
    + apply E_IfTrue; auto.
  - apply H0; intros.
    unfold andp, notp in H2.
    destruct H2.
    eapply H1.
    + apply H2.
    + apply E_IfFalse; auto.
      unfold bassn in H4.
      destruct (beval st1 b); auto.
      congruence.
Qed.

Lemma hoare_while_complete:
  forall fc lf fp P Q c b,
  (forall P Q : Assertion, valid fc lf ({{P}} c {{Q}}) -> provable fc lf fp ({{P}} c {{Q}})) ->
  valid fc lf ({{P}} While b Do c EndWhile {{Q}}) ->
  provable fc lf fp ({{P}} While b Do c EndWhile {{Q}}).
Proof.
  unfold valid, triple_valid.
  intros.
  remember (fun (st:state) => exists st0, P st0 /\ while_sem b (ceval fc lf c) st0 st) as I.
  apply hoare_consequence with I (fun st => I st /\ not (bassn b st)).
  - subst.
    unfold derives.
    intros.
    exists st.
    split; auto.
    apply rt_refl.
  - eapply hoare_while.
    subst.
    apply H.
    intros.
    destruct H1 as [[st0 [? ?]] ?].
    exists st0.
    split; auto.
    apply Operators_Properties.clos_rt_rtn1_iff in H3.
    apply Operators_Properties.clos_rt_rtn1_iff.
    apply rtn1_trans with st1; auto.
    split; auto.
  - subst.
    unfold derives.
    intros.
    destruct H1 as [[st0 [? ?]] ?].
    eapply H0; [apply H1 |].
    clear H1.
    apply Operators_Properties.clos_rt_rt1n_iff in H2.
    induction H2.
    + apply E_WhileFalse; auto.
      unfold bassn in H3.
      destruct (beval x b); auto.
      congruence.
    + specialize (IHclos_refl_trans_1n H3).
      destruct H1.
      apply E_WhileTrue with y; auto.
Qed.

Lemma hoare_triple_complete: forall fc lf fp tr,
  valid fc lf tr ->
  fp = (fun (f : func) (P Q : Assertion) => valid fc lf ({{P}} func_bdy f {{Q}})) ->
  provable fc lf fp tr.
Proof.
  intros.
  destruct tr.
  revert dependent Q.
  revert P.
  induction c; intros.
  - apply hoare_skip_complete; auto.
  - apply hoare_assn_complete; auto.
  - apply hoare_seq_complete; auto.
  - apply hoare_if_complete; auto.
  - apply hoare_while_complete; auto.
  - apply hoare_call_complete; auto.
  - apply hoare_reentry_complete; auto.
Qed.

Theorem hoare_complete: forall fc lf tr,
  valid fc lf tr ->
  exists (fp: func_predicate),
    (forall f P Q,fp f P Q ->
      provable fc lf fp ({{P}} (func_bdy f) {{Q}})) /\
    provable fc lf fp tr.
Proof.
  intros.
  remember (fun f P Q => valid fc lf ({{P}} (func_bdy f) {{Q}})) as fp.
  exists fp.
  split.
  {
    intros.
    rewrite Heqfp in H0.
    apply hoare_triple_complete; auto.
  }
  {
    apply hoare_triple_complete; auto.
  }
Qed.
End Completeness.
(** [] *)

Import Soundness.
Import Completeness.
Print Assumptions hoare_sound.
Print Assumptions hoare_complete.

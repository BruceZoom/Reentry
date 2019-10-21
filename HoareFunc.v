Require Import Coq.Lists.List.
Require Import AST_wc.
Require Import Hoare_wc.

Require Import Omega.

(* ceval' sigma c st1 st2

sg n
0 => _ _ _ => False
S n => ceval' (sg n)

sigma
exists n, sg n

ceval' sigma <-> ceval *)

(* Inductive arbitrary_eval' (sigma: func_context -> public_funcs -> com -> state -> state -> Prop) (fc: func_context) (lf: public_funcs): unit_state -> unit_state -> unit_state -> Prop :=
  | ArE'_nil: forall loc gl, arbitrary_eval' sigma fc lf loc gl gl
  | ArE'_cons: forall loc loc1 loc2 gl1 gl2 gl3 f,
      In f lf ->
      sigma fc lf (func_bdy f) (loc1, gl1) (loc2, gl2) ->
      arbitrary_eval' sigma fc lf loc gl2 gl3 ->
      arbitrary_eval' sigma fc lf loc gl1 gl3. *)

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
      arbitrary_eval' sigma fc lf loc glb1 glb2 ->
      ceval' sigma fc lf CReentry (loc, glb1) (loc, glb2)
with arbitrary_eval' (sigma: semantic) (fc: func_context) (lf: public_funcs): unit_state -> unit_state -> unit_state -> Prop :=
  | ArE'_nil: forall loc gl, arbitrary_eval' sigma fc lf loc gl gl
  | ArE'_cons: forall loc loc1 loc2 gl1 gl2 gl3 f,
      In f lf ->
      sigma fc lf (func_bdy f) (loc1, gl1) (loc2, gl2) ->
      arbitrary_eval' sigma fc lf loc gl2 gl3 ->
      arbitrary_eval' sigma fc lf loc gl1 gl3.

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
      * apply IHn. apply H0.
      * apply IHarbitrary_eval'.
Qed.

Lemma arbitrary_eval'_mono_inc : forall fc lf loc gl1 gl2 n1 n2,
  arbitrary_eval' (sg n1) fc lf loc gl1 gl2 ->
  arbitrary_eval' (sg (n1 + n2)) fc lf loc gl1 gl2.
Proof.
  intros.
  revert H.
  revert loc gl1 gl2 n2.
  induction n1; intros.
  - inversion H.
    + apply ArE'_nil.
    + simpl.
      induction H2.
      * inversion H1.
      * apply IHarbitrary_eval'; auto.
  - induction H.
   + apply ArE'_nil.
   + eapply ArE'_cons.
    * apply H.
    * apply sg_mono_inc.
      apply H0.
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
        * exists n.
          apply H0.
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
      + destruct H0 as [n1 ?].
        destruct IHarbitrary_eval' as [n2 ?].
        apply (sg_mono_inc _ _ _ _ _ _ 1) in H2.
        replace (n2 + 1) with (S n2) in H2; [| omega].
        simpl in H2.
        inversion H2; subst.
        exists (S n1 + n2); simpl.
        apply E'_Reentry.
        eapply ArE'_cons.
        * apply H.
        * apply sg_mono_inc.
          apply H0.
        * rewrite Nat.add_comm.
          apply arbitrary_eval'_mono_inc.
          apply H6.
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
      - eapply ArE_cons.
        ++ apply H.
        ++ apply IHn. apply H0.
        ++ apply IHarbitrary_eval'.
Qed.

Lemma ceval_sg_n fc lf: forall c st1 st2,
  ceval fc lf c st1 st2 ->
  exists n, sg n fc lf c st1 st2.
Proof.
  intros.
  induction H.
  - exists 1; simpl.
    apply E'_Skip.
  - exists 1; simpl.
    apply E'_Ass; auto.
  - destruct IHceval1 as [n1 ?].
    destruct IHceval2 as [n2 ?].
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - induction H.
    + exists 1; simpl.
      apply E'_Reentry.
      apply ArE'_nil.
    + destruct IHarbitrary_eval as [n ?].
      admit.
Admitted.

Fact pass' : False. Admitted.
Ltac pass := pose proof pass' as Htest; inversion Htest.

(* One way does not work *)
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
    + destruct H0.
      apply sg_n_ceval in H0.
      eapply ArE_cons.
      apply H.
      apply H0.
      apply IHarbitrary_eval'.
Qed.

Lemma abeval'_abeval (fc: func_context) (lf: public_funcs) (loc glb1 glb2: unit_state) :
  arbitrary_eval' sigma fc lf loc glb1 glb2 -> arbitrary_eval fc lf loc glb1 glb2.
Proof.
  intros.
  induction H.
  + apply ArE_nil.
  + (* Possibly the follwing line causes the trouble *)
    apply sigma_ceval'_equiv in H0.
    apply ceval'_ceval in H0.
    pose proof ArE_cons _ _ _ _ _ _ _ _ _ H H0 IHarbitrary_eval'.
    apply H2.
Qed.

Lemma ceval_ceval' (fc: func_context) (lf: public_funcs) (c: com) (st1 st2: state) :
  ceval fc lf c st1 st2 -> ceval' sigma fc lf c st1 st2
with abeval_abeval' (fc: func_context) (lf: public_funcs) (loc glb1 glb2: unit_state) :
  arbitrary_eval fc lf loc glb1 glb2 -> arbitrary_eval' sigma fc lf loc glb1 glb2.
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
  pass.
}
Admitted.

Lemma ceval'_ceval_equiv (fc: func_context) (lf: public_funcs) (c: com) (st1 st2: state) :
  ceval' sigma fc lf c st1 st2 <-> ceval fc lf c st1 st2
with abeval'_abeval_equiv (fc: func_context) (lf: public_funcs) (loc glb1 glb2: unit_state) :
  arbitrary_eval' sigma fc lf loc glb1 glb2 <-> arbitrary_eval fc lf loc glb1 glb2.
Proof.
  - clear ceval'_ceval_equiv.
    pose proof ceval_ceval' fc lf c st1 st2.
    pose proof ceval'_ceval fc lf c st1 st2.
    tauto.
  - clear abeval'_abeval_equiv.
    pose proof abeval_abeval' fc lf loc glb1 glb2.
    pose proof abeval'_abeval fc lf loc glb1 glb2.
    tauto.
Qed.

End FixpointSigma.

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
  | hoare_call : forall f pv P Q R,
      globalp Q ->
      localp R ->
      fp f P Q ->
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
(* delta f P Q -> delta |== P f Q *)

(*
  sg n |= delta -> P st1 -> ceval' (sg n) c st1 st2 -> Q st2
*)

(** Weak Valid *)
Definition weak_valid (sigma: semantic) (fc : func_context) (lf : public_funcs) (fp : func_predicate) (tr : hoare_triple) : Prop :=
  fp_valid sigma fc lf fp ->
  triple_valid (ceval' sigma) fc lf tr.
Notation "sigma fc lf fp |== tr" := (weak_valid sigma fc lf fp tr) (at level 91, no associativity).

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
  pose proof H0 _ _ _ (H _ _ H1) _ (loc2, gl2) (Hglb _ _ loc1 _ H3) H2.
  eapply Hglb.
  apply H5.
Qed.

Theorem hoare_sound_weak : forall sigma fc lf fp tr,
  provable fc lf fp tr ->
  weak_valid sigma fc lf fp tr.
Proof.
  intros.
  induction H.
  - apply reentry_sound_weak; auto.
  - admit.
Admitted.
(** [] *)

(** Soundness *)
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
(** [] *)

(** Completeness *)
Definition reentry_semantic fc lf (st1 st2 : state) : Prop :=
  match st1, st2 with
  | (loc1, glb1), (loc2, glb2) =>
      arbitrary_eval fc lf loc1 glb1 glb2 /\ loc1 = loc2
  end.

Theorem hoare_complete: forall fc lf tr,
  triple_valid fc lf tr ->
  exists fp, provable fc lf fp tr. (* /\ fp |- forall tr in fp *)
Proof.
  intros.
  destruct tr.
  induction c.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - (* TODO: global I? split into two *)
(*     remember ((fun st => exists st0, P st0 /\ reentry_semantic fc lf st0 st):Assertion) as I. *)
    (* assert (globalp I).
    {
      unfold globalp.
      intros.
      subst.
      destruct H0 as [st0 [? ?]].
      destruct st0 as [loc0 glb0].
      admit.
    } *)
    (* TODO: how to construct fp *)
    Print func_predicate.
    remember (fun (f: func) P Q => In f lf -> P = I /\ Q = I) as fp.
    exists fp.
    eapply hoare_consequence.
    
Admitted.
(** [] *)

(*
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

*)




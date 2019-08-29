Require Import Coq.Lists.List.
Require Import AST_woc.
Require Import ASTLc_woc.
Require Import Hoare_woc.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Omega.

Definition top (fc : func_context) (f : func) : label :=
  com_to_label_pure (snd (fc f)).

Definition bottom (fc : func_context) (f : func) : label :=
  com_to_label_pure (snd (fc f)).

Inductive matched_label : label -> com -> Prop :=
  | ML_Skip : matched_label LPure CSkip
  | ML_Ass : forall X a, matched_label LPure (CAss X a)
  | ML_Seq : forall l1 l2 c1 c2,
        matched_label l1 c1 ->
        matched_label l2 c2 ->
        matched_label (LSeq l1 l2) (CSeq c1 c2)
  | ML_If : forall l1 l2 c1 c2 b,
        matched_label l1 c1 ->
        matched_label l2 c2 ->
        matched_label (LIf b l1 l2) (CIf b c1 c2)
  | ML_While : forall lb c b,
        matched_label lb c ->
        matched_label (LWhile b lb) (CWhile b c)
  | ML_Reentry_here : matched_label LHere CReentry
  | ML_Reentry_pure : matched_label LPure CReentry.

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
  COM.index_label_set fc (snd (fc f)).

Definition rAssertion (fc : func_context) (f : func) : Type :=
  COM.rAssertion fc (snd (fc f)).
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
      ceval' fc (snd (fc f)) (top fc f) (bottom fc f) st1 st2 ->
      P st1 ->
      Q st2.

Definition triple_PR (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2 (i: FUN.index_label_set fc f),
      ceval' fc (snd (fc f)) (top fc f) (proj1_sig i) st1 st2 ->
      P st1 ->
      R2 i st2.

Definition triple_RQ (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2 (i: FUN.index_label_set fc f),
      ceval' fc (snd (fc f)) (proj1_sig i) (bottom fc f) st1 st2 ->
      R1 i st1 ->
      Q st2.

Definition triple_RR (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2 (i1 i2: FUN.index_label_set fc f),
      ceval' fc (snd (fc f)) (proj1_sig i1) (proj1_sig i2) st1 st2 ->
      R1 i1 st1 ->
      R2 i2 st2.

Definition func_triple' (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    triple_PQ fc f P Q R1 R2
 /\ triple_PR fc f P Q R1 R2
 /\ triple_RQ fc f P Q R1 R2
 /\ triple_RR fc f P Q R1 R2.

Inductive reachable_param (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (R : index_relation fc (f :: lf) pt) : restk -> forall (i : index_set fc (f :: lf)), (pt i) -> Prop :=
  | RP_single : forall st i x,
      fname _ _ i = f ->
      reachable_param fc lf f pt R ((snd (fc f), Some (proj1_sig (index_label _ _ i)), st) :: nil) i x
  | RP_multi : forall st1 st2 i j x y stk,
      In (fname _ _ j) lf ->
      R i j x y ->
      reachable_param fc lf f pt R ((snd (fc (fname _ _ i)), Some (proj1_sig (index_label _ _ i)), st1) :: stk) i x ->
      reachable_param fc lf f pt R ((snd (fc (fname _ _ j)), Some (proj1_sig (index_label _ _ j)), st2) :: (snd (fc (fname _ _ i)), Some (proj1_sig (index_label _ _ i)), st1) :: stk) j y.

Lemma reachable_param_head : 
  forall fc lf f pt R p stk i x,
  reachable_param fc lf f pt R (p :: stk) i x ->
  exists st, p = (snd (fc (fname _ _ i)), Some (proj1_sig (index_label _ _ i)), st).
Proof.
  intros.
  inversion H; subst.
  - exists st.
    destruct i.
    simpl in *.
    subst. auto.
  - exists st2.
    auto.
Qed.

Lemma reachable_param_state :
  forall fc lf f pt R c l st1 stk i x st2,
  reachable_param fc lf f pt R ((c, l, st1) :: stk) i x ->
  reachable_param fc lf f pt R ((c, l, st2) :: stk) i x.
Proof.
  intros.
  remember ((c, l, st1) :: stk) as stk'.
  induction H; subst.
  - inversion Heqstk'; subst.
    apply RP_single.
    exact H.
  - inversion Heqstk'; subst.
    eapply RP_multi.
    exact H.
    exact H0.
    exact H1.
Qed.

Definition stk_to_pre (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (stk : restk) (P Q : Assertion) : Prop :=
  match stk with
  | nil => False                          (* empty stack *)
  | (c1, l1, st1) :: stk' =>
    match stk' with
    | nil =>                              (* only with bottom level *)
      match l1 with
      | Some l1 =>
        (is_pure l1 /\ P st1) \/          (* bottom level head *)
        (single_point l1 /\ exists i x,   (* bottom level reentry *)
          c1 = snd (fc (fname _ _ i)) /\
          l1 = proj1_sig (index_label _ _ i) /\
          reachable_param fc lf f pt R ((c1, Some l1, st1) :: stk') i x /\
          invs i x st1)
      | None => Q st1                     (* bottom level tail *)
      end
    | _ =>                                (* during reentry *)
      match l1 with
      | Some l1 =>
        (is_pure l1 /\ exists i x,        (* current level head *)
          reachable_param fc lf f pt R stk' i x /\ invs i x st1) \/
        (single_point l1 /\ exists i x,   (* current level reentry *)
          c1 = snd (fc (fname _ _ i)) /\
          l1 = proj1_sig (index_label _ _ i) /\
          reachable_param fc lf f pt R ((c1, Some l1, st1) :: stk') i x /\
          invs i x st1)
      | None => exists i x,               (* current level tail *)
        reachable_param fc lf f pt R stk' i x /\ invs i x st1
      end
    end
  end.

(* Inductive stk_to_pre (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion): forall (stk : restk), Prop :=
| stk_to_pre_bottom_level_head: forall st,
    P st ->
    stk_to_pre fc lf f pt invs R P Q ((snd (fc f), Some (com_to_label_pure (snd (fc f))), st) :: nil)
| stk_to_pre_bottom_level_tail: forall st,
    Q st ->
    stk_to_pre fc lf f pt invs R P Q ((snd (fc f), None, st) :: nil)
| stk_to_pre_upper_level_head: forall c st stk i x,
    invs i x st ->
    reachable_param fc lf f pt R stk i x ->
    stk_to_pre fc lf f pt invs R P Q ((c, Some (com_to_label_pure c), st) :: stk)
| stk_to_pre_upper_level_tail: forall c st stk i x,
    invs i x st ->
    reachable_param fc lf f pt R stk i x ->
    stk_to_pre fc lf f pt invs R P Q ((c, None, st) :: stk)
| stk_to_pre_reentry: forall c l st stk i x,
    single_point (proj1_sig (index_label _ _ i)) ->
    invs i x st ->
    reachable_param fc lf f pt R ((c, l, st) :: stk) i x ->
    stk_to_pre fc lf f pt invs R P Q ((c, l, st) :: stk). *)

Fixpoint get_bottom_com (stk : restk) : com :=
  match stk with
  | nil => CSkip
  | (c, _, _) :: stk' =>
    match stk' with
    | nil => c
    | _ => get_bottom_com stk'
    end
  end.

Lemma ceval'_pure_head :
  forall fc c l1 l2 st1 st2,
  is_pure l1 ->
  ceval' fc c l1 l2 st1 st2 ->
  l1 = com_to_label_pure c.
Proof.
  intros.
  induction H0; auto;
  try (inversion H; subst;
    pose proof IHceval'1 H6;
    pose proof IHceval'2 H7;
    subst; auto);
  try (inversion H; subst;
    try pose proof IHceval'1 H3;
    try pose proof IHceval' H4;
    try pose proof IHceval' H5;
    try pose proof IHceval' H6;
    try pose proof IHceval' H7;
    try pose proof IHceval' H8;
    subst; auto).
Qed.

Lemma ceval'_pure_tail :
  forall fc c l1 l2 st1 st2,
  is_pure l2 ->
  ceval' fc c l1 l2 st1 st2 ->
  l2 = com_to_label_pure c.
Proof.
  intros.
  induction H0; auto;
  try (inversion H; subst;
    pose proof IHceval'1 H6;
    pose proof IHceval'2 H7;
    subst; auto);
  try (inversion H; subst;
    try pose proof IHceval'1 H3;
    try pose proof IHceval' H4;
    try pose proof IHceval' H5;
    try pose proof IHceval' H6;
    try pose proof IHceval' H7;
    try pose proof IHceval' H8;
    subst; auto).
Qed.

Lemma com_to_label_pure_matched :
  forall c, matched_label (com_to_label_pure c) c.
Proof.
  intros.
  induction c.
  - apply ML_Skip.
  - apply ML_Ass.
  - apply ML_Seq; assumption.
  - apply ML_If; assumption.
  - apply ML_While; assumption.
  - apply ML_Reentry_pure.
Qed.

Lemma ceval'_matched_head :
  forall fc c l1 l2 st1 st2,
  ceval' fc c l1 l2 st1 st2 ->
  matched_label l1 c.
Proof.
  intros.
  induction H;
  try (pose proof (com_to_label_pure_matched c1));
  try (pose proof (com_to_label_pure_matched c2));
  try (pose proof (com_to_label_pure_matched c));
  try (apply ML_Skip);
  try (apply ML_Ass);
  try (apply ML_Seq; assumption);
  try (apply ML_If; assumption);
  try (apply ML_While; assumption);
  try constructor.
  pose proof ceval'_pure_head _ _ _ _ _ _ H H3; subst.
  exact IHceval'2.
Qed.

Lemma ceval'_matched_tail :
  forall fc c l1 l2 st1 st2,
  ceval' fc c l1 l2 st1 st2 ->
  matched_label l2 c.
Proof.
  intros.
  induction H;
  try (pose proof (com_to_label_pure_matched c1));
  try (pose proof (com_to_label_pure_matched c2));
  try (pose proof (com_to_label_pure_matched c));
  try (apply ML_Skip);
  try (apply ML_Ass);
  try (apply ML_Seq; assumption);
  try (apply ML_If; assumption);
  try (apply ML_While; assumption);
  try constructor.
  exact IHceval'2.
  exact IHceval'2.
Qed.

Theorem reentry_invariant :
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion),

  (forall i x, globalp (invs i x)) ->

  (forall f' (Hin: In f' lf) (i: index_set fc (f :: lf)) (x: pt i) invs',
    (invs' = fun j st =>
        exists y, R i {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} x y 
        /\ invs {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st) ->
  func_triple' fc f' (invs i x) (invs i x) invs' invs') ->

  (forall (invs' : FUN.rAssertion fc f),
    (invs' = fun j st =>
        exists z, invs {| fname := f; fvalid := in_eq f lf ; index_label := j|} z st) ->
  func_triple' fc f P Q invs' invs') ->

  func_triple fc lf P f Q.
Proof.
  intros.
  rename H into Ginv.
  rename H0 into H.
  rename H1 into H0.
  unfold func_triple.
  intros.
  apply ceval_multi_ceval' in H1.

  remember ((snd (fc f), Some (com_to_label_pure (snd (fc f))), st1) :: nil) as stk1.
  (* Generalized precondition *)
  assert (stk_to_pre fc lf f pt invs R stk1 P Q).
  {
    subst. simpl.
    left.
    split.
    apply com_to_label_pure_is_pure.
    exact H2.
  }
  (* Some properties of the stack *)
  assert (get_bottom_com stk1 = snd (fc f)) as Hbt.
  {
    subst.
    auto.
  }
  assert (forall c l st p stk' stk'',
            stk1 = stk' ++ p :: stk'' ->
            In (c, l, st) stk' ->
            exists f', In f' lf /\ c = (snd (fc f'))) as Hctop.
  {
    intros.
    rewrite H4 in Heqstk1.
    apply app_eq_unit in Heqstk1.
    destruct Heqstk1.
    destruct H6. subst. inversion H5.
    destruct H6. inversion H7.
  }
  clear dependent st1.

  apply Operators_Properties.clos_rt_rt1n in H1.
  remember ((snd (fc f), None, st2) :: nil) as stk2.
(*   revert dependent f. *)
  induction H1; intros; subst.
  - simpl in H3. exact H3.
  - inversion H1; subst.
    {
      apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
      auto.
      destruct stk.
      - simpl in Hbt. subst c.
        pose proof H0 (fun j st =>
        exists z, invs {| fname := f; fvalid := in_eq _ _ ; index_label := j|} z st) (eq_refl _).
        simpl in H3.
        destruct H3; unfold func_triple' in H5.
        + destruct H5 as [? _].
          destruct H3.
          eapply H5.
          pose proof ceval'_pure_head _ _ _ _ _ _ H3 H4. subst.
          exact H4. exact H6.
        + destruct H3 as [? [? [? [? [? [? ?]]]]]]. subst.
          simpl in *.
          destruct H5 as [_ [_ [? _]]].
          destruct x.
          simpl in H6.
          assert (fname0 = f). inversion H8. auto.
          subst fname0.
          simpl in *.
          eapply H5.
          apply H4.
          assert (fvalid0 = in_eq f lf). apply proof_irrelevance.
          subst.
          exists x0.
          apply H9.
      - simpl.
        simpl in H3.
        destruct H3.
        + destruct H3 as [? [? [? [? ?]]]].
          pose proof Hctop c (Some l1) st1 p ((c, Some l1, st1)::nil) stk (eq_refl _) (in_eq _ _) as [f' [? ?]].
          subst.
          pose proof H f' H7 x x0
            (fun (j : FUN.index_label_set fc f') (st : state) =>
              exists y : pt {| fname := f'; fvalid := in_cons f f' lf H7; index_label := j |}, R x {| fname := f'; fvalid := in_cons f f' lf H7; index_label := j |} x0 y /\ invs {| fname := f'; fvalid := in_cons f f' lf H7; index_label := j |} y st) (eq_refl _) as [? _].
          unfold triple_PQ in H8.
          pose proof ceval'_pure_head _ _ _ _ _ _ H3 H4.
          subst.
          pose proof H8 _ _ H4 H6.
          exists x, x0.
          tauto.
        + destruct H3 as [? [? [? [? [? [? ?]]]]]].
          subst c.
          remember ((snd (fc (fname fc (f :: lf) x)), Some l1, st1) :: p :: stk) as stk'.
          induction H7; subst.
          * inversion Heqstk'.
          * clear IHreachable_param.
            inversion Heqstk'; subst.
            pose proof H (fname fc (f :: lf) j) H5 i x (fun (j0 : FUN.index_label_set fc (fname fc (f :: lf) j)) (st : state) =>
      exists y : pt {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H5; index_label := j0 |},
        R i {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H5; index_label := j0 |} x y /\
        invs {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H5; index_label := j0 |} y st) (eq_refl _) as [_ [_ [? _]]].
          unfold triple_RQ in H6.
          exists i, x.
          split. assumption.
          eapply H6;
          clear H6.
          apply H4.
          replace {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H5; index_label := index_label fc (f :: lf) j |} with j.
          2:{
            destruct j.
            f_equal.
            apply proof_irrelevance.
          }
          exists y. tauto.
      - rewrite <- Hbt.
        auto.
      - intros.
        destruct stk'.
        inversion H6.
        destruct H6.
        + inversion H5; subst.
          inversion H8; subst.
          pose proof Hctop c0 (Some l1) st1 p ((c0, Some l1, st1) :: stk') stk'' (eq_refl _) (in_eq _ _). exact H6.
        + inversion H5; subst.
          pose proof Hctop c0 l st p ((c, Some l1, st1) :: stk') stk'' (eq_refl _) (in_cons _ _ _ H6). exact H7.
    }
    {
      apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
      auto.
      destruct stk.
      - simpl in Hbt. subst.
        pose proof H0 (fun j st =>
        exists z, invs {| fname := f; fvalid := in_eq _ _ ; index_label := j|} z st) (eq_refl _).
        destruct H3.
        + destruct H3.
          right.
          split. assumption.
          destruct H6 as [_ [? _]].
          unfold triple_PR in H6.
          rewrite (ceval'_pure_head _ _ _ _ _ _ H3 H5) in H5.
          assert (valid_index_label fc (snd (fc f)) l2).
          {
            split.
            exact H4.
            eapply ceval'_matched_tail.
            exact H5.
          }
          specialize (H6 _ _ (exist _ l2 H8) H5 H7).
          destruct H6.
          exists {|
            fname := f;
            fvalid := in_eq f lf;
            index_label := exist (valid_index_label fc (snd (fc f))) l2 H8 |}, x.
          simpl.
          repeat split.
          * replace (Some l2) with (Some (proj1_sig (index_label _ _ {|
            fname := f; fvalid := in_eq f lf; index_label := exist (valid_index_label fc (snd (fc f))) l2 H8 |}))).
            apply RP_single. auto. auto.
          * exact H6.
        + destruct H3 as [? [? [? [? [? [? ?]]]]]].
          right. split. assumption.
          destruct H6 as [_ [_ [_ ?]]].
          unfold triple_RR in H6.
          subst.
          assert (valid_index_label fc (snd (fc f)) l2).
          {
            split.
            exact H4.
            eapply ceval'_matched_tail.
            exact H5.
          }
          replace l2 with (proj1_sig (exist _ l2 H8)) in H5.
          2:{ auto. }
          inversion H9; subst.
          destruct x.
          simpl in *.
          subst f.
          clear H11 H15.
          assert (exists z : pt {| fname := fname0; fvalid := in_eq fname0 lf; index_label := index_label0 |},
          invs {| fname := fname0; fvalid := in_eq fname0 lf; index_label := index_label0 |} z st1).
          {
            replace (in_eq fname0 lf) with fvalid0.
            2:{ apply proof_irrelevance. }
            exists x0. auto.
          }
          specialize (H6 _ _ _ (exist _ l2 H8) H5 H11); clear H11.
          destruct H6.
          exists {| fname := fname0; fvalid := in_eq fname0 lf; index_label := exist (valid_index_label fc (snd (fc fname0))) l2 H8 |}, x.
          repeat split.
          replace (Some l2) with (Some (proj1_sig (index_label _ _ {| fname := fname0; fvalid := in_eq fname0 lf; index_label := exist (valid_index_label fc (snd (fc fname0))) l2 H8 |}))). 2:{ auto. }
          apply RP_single. auto. assumption.
      - simpl.
        destruct H3.
        + right.
          split. assumption.
          destruct H3 as [? [? [? [? ?]]]].
          rewrite (ceval'_pure_head _ _ _ _ _ _ H3 H5) in H5.
          pose proof Hctop c (Some l1) st1 p ((c, Some l1, st1)::nil) stk (eq_refl _) (in_eq _ _) as [f' [? ?]].
          subst.
          pose proof H f' H8 x x0 (fun (j : FUN.index_label_set fc f') (st : state) =>
            exists y : pt {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j |},
              R x {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j |} x0 y /\
              invs {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j |} y st) (eq_refl _) as [_ [? _]].
          unfold triple_PR in H9.
          assert (valid_index_label fc (snd (fc f')) l2).
          split. assumption. eapply ceval'_matched_tail. apply H5.
          specialize (H9 _ _ (exist _ l2 H10) H5 H7).
          destruct H9 as [y [? ?]].
          exists {| fname := f'; fvalid := in_cons f f' lf H8; index_label := exist (valid_index_label fc (snd (fc f'))) l2 H10 |}, y.
          repeat split.
          replace ((snd (fc f')), Some l2, st0) with ((snd (fc (fname _ _ {| fname := f'; fvalid := in_cons f f' lf H8; index_label := exist (valid_index_label fc (snd (fc f'))) l2 H10 |}))), Some l2, st0). 2:{ auto. }
          replace (Some l2) with (Some (proj1_sig (index_label _ _ {| fname := f'; fvalid := in_cons f f' lf H8; index_label := exist (valid_index_label fc (snd (fc f'))) l2 H10 |}))). 2:{ auto. }
          pose proof reachable_param_head _ _ _ _ _ _ _ _ _ H6 as [st ?].
          subst.
          eapply RP_multi.
          auto.
          apply H9.
          apply H6.
          apply H11.
        + right.
          split. assumption.
          destruct H3 as [? [? [? [? [? [? ?]]]]]].
          subst.
          remember ((snd (fc (fname fc (f :: lf) x)), Some (proj1_sig (index_label fc (f :: lf) x)), st1) :: p :: stk) as stk'.
          induction H8; subst.
          * inversion Heqstk'.
          * clear IHreachable_param.
            inversion Heqstk'; subst.
            pose proof H (fname fc (f :: lf) j) H6 i x (fun (j0 : FUN.index_label_set fc (fname fc (f :: lf) j)) (st : state) =>
       exists y : pt {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H6; index_label := j0 |},
         R i {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H6; index_label := j0 |} x y /\
         invs {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H6; index_label := j0 |} y st) (eq_refl _) as [_ [_ [_ ?]]].
            unfold triple_RR in H10.
            assert (valid_index_label fc (snd (fc (fname fc (f :: lf) j))) l2).
            { split. assumption. eapply ceval'_matched_tail. apply H5. }
            assert (exists y : pt {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H6; index_label := index_label fc (f :: lf) j |},
         R i {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H6; index_label := index_label fc (f :: lf) j |} x y /\
         invs {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H6; index_label := index_label fc (f :: lf) j |} y st1).
            {
              replace {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H6; index_label := index_label fc (f :: lf) j |} with j.
              exists y. tauto.
              destruct j. simpl.
              replace (in_cons f fname0 lf H6) with fvalid0.
              auto. apply proof_irrelevance.
            }
            specialize (H10 _ _ _ (exist _ l2 H11) H5 H12); clear H12.
            destruct H10 as [? [? ?]].
            exists {|
             fname := fname fc (f :: lf) j;
             fvalid := in_cons f (fname fc (f :: lf) j) lf H6;
             index_label := exist (valid_index_label fc (snd (fc (fname fc (f :: lf) j)))) l2 H11 |}, x0.
            repeat split.
            2:{ apply H12. }
            remember {|
             fname := fname fc (f :: lf) j;
             fvalid := in_cons f (fname fc (f :: lf) j) lf H6;
             index_label := exist (valid_index_label fc (snd (fc (fname fc (f :: lf) j)))) l2 H11 |} as k.
            replace (snd (fc (fname fc (f :: lf) j))) with (snd (fc (fname fc (f :: lf) k))).
            2:{ subst. auto. }
            replace (Some l2) with (Some (proj1_sig (index_label _ _ k))).
            2:{ subst. auto. }
            eapply RP_multi.
            subst. simpl. exact H6.
            exact H10.
            exact H8.
     - auto.
     - intros.
      destruct stk'.
      inversion H6.
      inversion H7.
      destruct H7.
      + inversion H6; subst.
        inversion H9; subst.
        pose proof Hctop c0 (Some l1) st1 p ((c0, Some l1, st1) :: stk') stk'' (eq_refl _) (in_eq _ _). exact H7.
      + inversion H6; subst.
        pose proof Hctop c0 l st p ((c, Some l1, st1) :: stk') stk'' (eq_refl _) (in_cons _ _ _ H7). exact H8.
    }
    {
      apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
      auto.
      destruct stk.
      - simpl.
        destruct H3.
        + destruct H3.
          pose proof pure_no_point l1 H3.
          congruence.
        + left.
          split. apply com_to_label_pure_is_pure.
          destruct H3 as [_ [? [? [? [? [? ?]]]]]].
          subst.
          exists x, x0.
          split. assumption.
          eapply Ginv. exact H8.
      - simpl.
        destruct H3.
        + destruct H3.
          pose proof pure_no_point l1 H3.
          congruence.
        + left.
          split. apply com_to_label_pure_is_pure.
          destruct H3 as [_ [? [? [? [? [? ?]]]]]].
          subst.
          exists x, x0.
          split. assumption.
          eapply Ginv. exact H8.
      - auto.
      - intros.
        remember ((c1, Some l1, (loc1, glb)) :: stk) as stk'''.
        clear dependent stk.
        rename stk''' into stk.
        destruct stk'.
        inversion H7.
        destruct H7.
        + inversion H5; subst.
          inversion H9; subst.
          exists f0. tauto.
        + inversion H5; subst.
          pose proof Hctop c l st p stk' stk'' (eq_refl _) H7. exact H8.
    }
    {
      apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
      auto.
      destruct stk.
      - simpl.
        destruct H3.
        destruct H3 as [? [? ?]].
        right.
        split. assumption.
        remember ((c2, Some l2, (loc2, glb2)) :: nil) as stk.
        induction H3; subst;
        inversion Heqstk; subst.
        exists i, x.
        repeat split.
        rewrite H3. auto.
        apply RP_single. exact H3.
        eapply Ginv. exact H5.
      - simpl.
        destruct H3.
        destruct H3 as [? [? ?]].
        right.
        split. assumption.
        exists x, x0.
        pose proof reachable_param_head _ _ _ _ _ _ _ _ _ H3.
        destruct H6. inversion H6; subst.
        repeat split.
        eapply reachable_param_state.
        apply H3.
        eapply Ginv. exact H5.
      - auto.
      - intros.
        destruct stk'.
        inversion H6.
        destruct H6.
        + inversion H5; subst.
          inversion H8; subst.
          pose proof Hctop c (Some l2) (loc2, glb2) p ((c1, None, (loc1, glb1)) :: (c, Some l2, (loc2, glb2)) :: stk') stk'' (eq_refl _) (in_cons _ _ _ (in_eq _ _)).
          exact H6.
        + inversion H5; subst.
          pose proof Hctop c l st p ((c1, None, (loc1, glb1)) :: (c2, Some l2, (loc2, glb2)) :: stk') stk'' (eq_refl _) (in_cons _ _ _ (in_cons _ _ _ H6)). exact H7.
    }
Qed.

Require Import Coq.Lists.List.
Require Import AST_wc.
Require Import ASTLc_wc.
Require Import Hoare_wc.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Omega.

Definition top (fc : func_context) (f : func) : lbstk :=
  (com_to_label_pure (func_bdy f)) :: nil.

Definition bottom (fc : func_context) (f : func) : lbstk :=
  (com_to_label_pure (func_bdy f)) :: nil.

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
  | ML_Reentry_pure : matched_label LPure CReentry
  | ML_Call_here : forall f pv, matched_label LHere (CCall f pv)
  | ML_Call_pure : forall f pv, matched_label LPure (CCall f pv).

Definition combine (f1 f2: option func) : option func :=
  match f1, f2 with
  | Some f1, None => Some f1
  | None, Some f2 => Some f2
  | _, _ => None
  end.

Lemma combine_left:
  forall f, combine f None = f.
Proof.
  intros.
  destruct f; auto.
Qed.

Lemma combine_right:
  forall f, combine None f = f.
Proof.
  intros.
  destruct f; auto.
Qed.

Fixpoint retrieve_func (lb: label) (c: com) : option func :=
  match lb, c with
  | LHere, CCall f _ => Some f
  | LHere, _ => None
  | LSeq l1 l2, CSeq c1 c2 => combine (retrieve_func l1 c1) (retrieve_func l2 c2)
  | LIf _ l1 l2, CIf _ c1 c2 => combine (retrieve_func l1 c1) (retrieve_func l2 c2)
  | LWhile _ l1, CWhile _ c1 => retrieve_func l1 c1
  | _, _ => None
  end.

Lemma retrieve_func_pure :
  forall lb c, is_pure lb -> retrieve_func lb c = None.
Proof.
  intros.
  revert c.
  induction H; intros; auto;
  try (simpl;
      destruct c; auto;
      rewrite (IHis_pure1 c1), (IHis_pure2 c2);
      auto).
Qed.

Fixpoint matched_lbstk (fc: func_context) (bstk: lbstk) (c: com) : Prop :=
  match bstk with
  | nil => True
  | lb :: bstk => single_point lb /\ matched_label lb c /\
      match bstk, (retrieve_func lb c) with
      | nil, None => True
      | _, Some f => matched_lbstk fc bstk (func_bdy f)
      | _, None => False
      end
  end.

(* Fixpoint matched_lbstk (fc: func_context) (bstk: lbstk) (c: com) : Prop :=
  match bstk with
  | nil => True
  | lb :: bstk => single_point lb /\ matched_label lb c /\
      match bstk, (retrieve_func lb c) with
      | nil, None => True
      | _, Some f => matched_lbstk fc bstk (func_bdy f)
      | _, None => False
      end
  end. *)

Definition valid_index_label (fc : func_context) (c : com) (bstk : lbstk) : Prop :=
  length bstk > 0 /\ matched_lbstk fc bstk c.

Definition Assertion' := state' -> Prop.

Definition A'2A (P: Assertion') : Assertion :=
  fun (st: state) => match st with
                     | (loc, glb) => P (loc :: nil, glb)
                     end.

Definition globalp' (P: Assertion') : Prop :=
  forall sstk1 sstk2 glb, P (sstk1, glb) -> P (sstk2, glb).

Definition localp' (P: Assertion') : Prop :=
  forall sstk glb1 glb2, P (sstk, glb1) -> P (sstk, glb2).

Module COM.
Definition index_label_set (fc : func_context) (c : com) : Type :=
  sig (valid_index_label fc c).

Definition rAssertion (fc : func_context) (c : com) : Type :=
  forall i: index_label_set fc c, Assertion'.
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
  forall i: index_set fc lf, (pt i) -> Assertion'.

Definition index_relation (fc : func_context) (lf : list func) (pt : param_type fc lf) : Type := forall i j : index_set fc lf, (pt i) -> (pt j) -> Prop.

Definition triple_PQ (fc : func_context) (f : func) (P Q : Assertion') (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2,
      ceval' fc (func_bdy f) (top fc f) (bottom fc f) st1 st2 ->
      P st1 ->
      Q st2.

Definition triple_PR (fc : func_context) (f : func) (P Q : Assertion') (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2 (i: FUN.index_label_set fc f),
      ceval' fc (func_bdy f) (top fc f) (proj1_sig i) st1 st2 ->
      P st1 ->
      R2 i st2.

Definition triple_RQ (fc : func_context) (f : func) (P Q : Assertion') (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2 (i: FUN.index_label_set fc f),
      ceval' fc (func_bdy f) (proj1_sig i) (bottom fc f) st1 st2 ->
      R1 i st1 ->
      Q st2.

Definition triple_RR (fc : func_context) (f : func) (P Q : Assertion') (R1 R2 : FUN.rAssertion fc f): Prop :=
    forall st1 st2 (i1 i2: FUN.index_label_set fc f),
      ceval' fc (func_bdy f) (proj1_sig i1) (proj1_sig i2) st1 st2 ->
      R1 i1 st1 ->
      R2 i2 st2.

Definition func_triple' (fc : func_context) (f : func) (P Q : Assertion') (R1 R2 : FUN.rAssertion fc f): Prop :=
    triple_PQ fc f P Q R1 R2
 /\ triple_PR fc f P Q R1 R2
 /\ triple_RQ fc f P Q R1 R2
 /\ triple_RR fc f P Q R1 R2.

(* Inductive reachable_param (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (R : index_relation fc (f :: lf) pt) : restk -> forall (i : index_set fc (f :: lf)), (pt i) -> Prop :=
  | RP_single : forall st i x,
      fname _ _ i = f ->
      reachable_param fc lf f pt R ((func_bdy f, Some (proj1_sig (index_label _ _ i)), st) :: nil) i x
  | RP_multi : forall st1 st2 i j x y stk,
      In (fname _ _ j) lf ->
      R i j x y ->
      reachable_param fc lf f pt R ((func_bdy (fname _ _ i), Some (proj1_sig (index_label _ _ i)), st1) :: stk) i x ->
      reachable_param fc lf f pt R ((func_bdy (fname _ _ j), Some (proj1_sig (index_label _ _ j)), st2) :: (func_bdy (fname _ _ i), Some (proj1_sig (index_label _ _ i)), st1) :: stk) j y.

Lemma reachable_param_head : 
  forall fc lf f pt R p stk i x,
  reachable_param fc lf f pt R (p :: stk) i x ->
  exists st, p = (func_bdy (fname _ _ i), Some (proj1_sig (index_label _ _ i)), st).
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
Qed. *)

Fixpoint stk_loc_R (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (loc_R : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (stk : restk) i x : Prop :=
  match stk with
  | nil => f = fname _ _ i
  | (c1, l1, st1) :: stk' =>
      In (fname _ _ i) lf /\
      match l1 with
      | Some l1 =>
        exists j y,
          c1 = func_bdy (fname _ _ j) /\
          l1 = proj1_sig (index_label _ _ j) /\
          R j i y x /\ loc_R j y st1 /\
          stk_loc_R fc lf f pt loc_R R stk' j y
      | None => False
      end
  end.

Definition stk_to_pre (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs loc_R : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (stk : restk) (P Q : Assertion') : Prop :=
  match stk with
  | nil => False                          (* empty stack *)
  | (c1, l1, st1) :: stk' =>
    match stk' with
    | nil =>                              (* only with bottom level *)
      match l1 with
      | Some (l1 :: bstk) =>
        (is_pure l1 /\ P st1) \/          (* bottom level head *)
        (single_point l1 /\ exists i x,   (* bottom level reentry *)
          c1 = func_bdy (fname _ _ i) /\
          (l1 :: bstk) = proj1_sig (index_label _ _ i) /\
          f = fname _ _ i /\ invs i x st1 /\ loc_R i x st1)
      | None => Q st1                     (* bottom level tail *)
      | _ => False
      end
    | (c2, Some (l2 :: bstk2), st2) :: stk'' =>   (* during reentry *)
      exists j y,
        stk_loc_R fc lf f pt loc_R R stk'' j y /\
        c2 = func_bdy (fname _ _ j) /\
        (l2 :: bstk2) = proj1_sig (index_label _ _ j) /\
        loc_R j y st2 /\
        match l1 with
        | Some (l1 :: bstk) =>
          (is_pure l1 /\ invs j y st1) \/   (* current level head *)
          (single_point l1 /\ exists i x,   (* current level reentry *)
            c1 = func_bdy (fname _ _ i) /\
            (l1 :: bstk) = proj1_sig (index_label _ _ i) /\
            In (fname _ _ i) lf /\ R j i y x /\
            invs i x st1 /\ loc_R i x st1)
        | None => invs j y st1              (* current level tail *)
        | _ => False
        end
    | _ => False
    end
  end.

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
  forall fc c l1 l2 st1 st2 bstk,
  is_pure l1 ->
  ceval' fc c (l1 :: bstk) l2 st1 st2 ->
  l1 = com_to_label_pure c.
Proof.
  intros.
  remember (l1 :: bstk) as bstk'.
  revert H Heqbstk'.
  revert l1 bstk.
  induction H0; intros; inversion Heqbstk'; subst; auto;
  try (inversion H; tauto).
  - inversion H2.
  - inversion H4.
  - inversion H3; subst.
    pose proof IHceval'1 l1 bstk H6 eq_refl.
    pose proof IHceval'2 l3 nil H7 eq_refl.
    subst. auto.
  - inversion H2; subst.
    pose proof IHceval' l1 bstk H5 eq_refl.
    subst. auto.
  - inversion H2; subst.
    pose proof IHceval' l1 bstk H6 eq_refl.
    subst; auto.
  - inversion H3; subst.
    pose proof IHceval' l1 nil H6 eq_refl.
    subst; auto.
  - inversion H3; subst.
    pose proof IHceval' l1 nil H8 eq_refl.
    subst; auto.
  - inversion H2; subst.
    pose proof IHceval' l1 bstk H5 eq_refl.
    subst; auto.
  - inversion H2; subst.
    pose proof IHceval' l1 bstk H7 eq_refl.
    subst; auto.
  - inversion H3; subst.
    pose proof IHceval' l1 nil H5 eq_refl.
    subst; auto.
  - eapply IHceval'2; auto.
  - simpl.
    inversion H2; subst.
    pose proof IHceval' l1 bstk H4 eq_refl.
    subst; auto.
  - simpl.
    inversion H1; subst.
    pose proof IHceval'1 l1 bstk H3 eq_refl.
    subst; auto.
Qed.

Lemma ceval'_pure_tail :
  forall fc c l1 l2 st1 st2 bstk,
  is_pure l2 ->
  ceval' fc c l1 (l2 :: bstk) st1 st2 ->
  l2 = com_to_label_pure c.
Proof.
Admitted.

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
  - apply ML_Call_pure.
  - apply ML_Reentry_pure.
Qed.

Lemma ceval'_matched_head :
  forall fc c l1 l2 st1 st2 bstk,
  ceval' fc c (l1 :: bstk) l2 st1 st2 ->
  matched_label l1 c.
Proof.
  intros.
  remember (l1 :: bstk) as bstk'.
  revert Heqbstk'.
  revert l1 bstk.
  induction H; intros; inversion Heqbstk'; subst.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - pose proof IHceval'1 l1 bstk eq_refl.
    pose proof IHceval'2 l3 nil eq_refl.
    apply ML_Seq; auto.
  - pose proof IHceval' l1 bstk eq_refl.
    apply ML_Seq; auto.
    apply com_to_label_pure_matched.
Admitted.

Lemma ceval'_matched_tail :
  forall fc c l1 l2 st1 st2 bstk,
  ceval' fc c l1 (l2 :: bstk) st1 st2 ->
  matched_label l2 c.
Proof.
  intros.
  remember (l2 :: bstk) as bstk'.
  revert Heqbstk'.
  revert l2 bstk.
  induction H; intros; subst; auto;
  inversion Heqbstk'; subst; try (constructor; tauto).
  - pose proof IHceval'1 l2 nil eq_refl.
    pose proof IHceval'2 l4 bstk eq_refl.
    apply ML_Seq; auto.
  - pose proof IHceval' l2 bstk eq_refl.
    apply ML_Seq; auto.
    apply com_to_label_pure_matched.
  - pose proof IHceval' l2 bstk eq_refl.
    apply ML_Seq; auto.
    apply com_to_label_pure_matched.
  - pose proof IHceval' l2 bstk0 eq_refl.
    apply ML_If; auto.
    apply com_to_label_pure_matched.
  - pose proof IHceval' l2 bstk0 eq_refl.
    apply ML_If; auto.
    apply com_to_label_pure_matched.
  - pose proof IHceval' l2 bstk eq_refl.
    apply ML_If; auto.
    apply com_to_label_pure_matched.
  - pose proof IHceval' l2 bstk eq_refl.
    apply ML_If; auto.
    apply com_to_label_pure_matched.
  - apply ML_While.
    apply com_to_label_pure_matched.
  - pose proof IHceval' l2 bstk0 eq_refl.
    apply ML_While; auto.
  - pose proof IHceval'2 l0 bstk0 eq_refl; auto.
  - pose proof IHceval' l2 bstk eq_refl.
    apply ML_While; auto.
  - pose proof IHceval'2 l0 bstk eq_refl; auto.
Qed.

Lemma ceval'_matched_lbstk_left :
  forall fc c st1 st2 bstk1 bstk2 l1,
  ceval' fc c (l1 :: bstk1) bstk2 st1 st2 ->
  single_point l1 ->
  matched_lbstk fc (l1 :: bstk1) c.
Proof.
  intros.
  remember (l1 :: bstk1) as bstk'.
  revert H0 Heqbstk'.
  revert l1 bstk1.
  assert (~ single_point LPure).
  { unfold not. intros. inversion H0. }
  induction H; intros; subst; inversion Heqbstk'; subst;
  try congruence; simpl; auto; split; auto.
  - split; auto.
    apply ML_Reentry_here.
  - split; [apply ML_Call_here |].
    destruct bstk.
    + pose proof IHceval' l1 nil H eq_refl.
      auto.
    + apply ceval'_single_point_stack_left_t2b in H2; auto.
      pose proof IHceval' l (bstk ++ l1 :: nil) H2 eq_refl.
      auto.
  - split; [apply ML_Call_here |].
    destruct bstk1.
    + pose proof IHceval' l1 nil H eq_refl.
      auto.
    + apply ceval'_single_point_stack_left_t2b in H4; auto.
      pose proof IHceval' l (bstk1 ++ l1 :: nil) H4 eq_refl.
      auto.
  - split.
    + apply ceval'_matched_head in H4.
      apply ceval'_matched_head in H5.
      apply ML_Seq; auto.
    + inversion H6; subst; [| apply pure_no_point in H2; congruence].
      pose proof IHceval'1 l1 bstk0 H9 eq_refl.
      simpl in H7.
      pose proof retrieve_func_pure l3 c2 H2.
      rewrite H8.
      rewrite combine_left.
      tauto.
  - split.
    + apply ceval'_matched_head in H2.
      apply ML_Seq; auto.
      apply com_to_label_pure_matched.
    + inversion H3; subst; [| pose proof com_to_label_pure_no_point c2; congruence].
      pose proof IHceval' l1 bstk0 H6 eq_refl.
      simpl in H4.
      pose proof retrieve_func_pure (com_to_label_pure c2) c2 (com_to_label_pure_is_pure _).
      rewrite H5.
      rewrite combine_left.
      tauto.
  - split.
    + apply ceval'_matched_head in H2.
      apply ML_Seq; auto.
      apply com_to_label_pure_matched.
    + inversion H3; subst; [pose proof com_to_label_pure_no_point c1; congruence |].
      pose proof IHceval' l1 bstk0 H7 eq_refl.
      simpl in H4.
      pose proof retrieve_func_pure (com_to_label_pure c1) c1 (com_to_label_pure_is_pure _).
      rewrite H5.
      rewrite combine_right.
      tauto.
  - split.
    + apply ceval'_matched_head in H3.
      apply ML_If; auto.
      apply com_to_label_pure_matched.
    + destruct (combine (retrieve_func l1 c1) (retrieve_func (com_to_label_pure c2) c2)); auto.
  - split.
    + apply ceval'_matched_head in H3.
      apply ML_If; auto.
      apply com_to_label_pure_matched.
    + destruct (combine (retrieve_func (com_to_label_pure c1) c1) (retrieve_func l1 c2)); auto.
  - split; auto.
    + apply ceval'_matched_head in H2.
      apply ML_If; auto.
      apply com_to_label_pure_matched.
    + inversion H3; subst; [| pose proof com_to_label_pure_no_point c2; congruence].
      pose proof IHceval' l1 bstk0 H6 eq_refl.
      simpl in H4.
      pose proof retrieve_func_pure (com_to_label_pure c2) c2 (com_to_label_pure_is_pure _).
      rewrite H5.
      rewrite combine_left.
      tauto.
  - split.
    + apply ceval'_matched_head in H2.
      apply ML_If; auto.
      apply com_to_label_pure_matched.
    + inversion H3; subst; [pose proof com_to_label_pure_no_point c1; congruence |].
      pose proof IHceval' l1 bstk0 H8 eq_refl.
      simpl in H4.
      pose proof retrieve_func_pure (com_to_label_pure c1) c1 (com_to_label_pure_is_pure _).
      rewrite H5.
      rewrite combine_right.
      tauto.
  - split.
    + apply ML_While.
      apply com_to_label_pure_matched.
    + destruct (retrieve_func (com_to_label_pure c) c); auto.
  - split.
    + apply ML_While.
      apply ceval'_matched_head in H3; auto.
    + destruct (retrieve_func l1 c); auto.
  - split.
    + apply ceval'_matched_head in H4; auto.
    + destruct (retrieve_func l0 (While b Do c EndWhile)); auto.
  - split.
    + apply ML_While.
      apply ceval'_matched_head in H2; auto.
    + inversion H3; subst.
      pose proof IHceval' l1 bstk0 H5 eq_refl.
      simpl in H4.
      tauto.
  - split.
    + apply ML_While.
      apply ceval'_matched_head in H2; auto.
    + inversion H4; subst.
      pose proof IHceval'1 l1 bstk0 H6 eq_refl.
      simpl in H5.
      tauto.
Qed.

Lemma ceval'_matched_lbstk_right :
  forall fc c st1 st2 bstk1 bstk2 l1,
  ceval' fc c bstk2 (l1 :: bstk1) st1 st2 ->
  single_point l1 ->
  matched_lbstk fc (l1 :: bstk1) c.
Proof.
  intros.
  remember (l1 :: bstk1) as bstk'.
  revert H0 Heqbstk'.
  revert l1 bstk1.
  assert (~ single_point LPure).
  { unfold not. intros. inversion H0. }
  induction H; intros; subst; inversion Heqbstk'; subst;
  try congruence; simpl; auto; split; auto.
  - split; auto.
    apply ML_Reentry_here.
  - split; [apply ML_Call_here |].
    destruct bstk.
    + pose proof IHceval' l2 nil H eq_refl.
      auto.
    + apply ceval'_single_point_stack_right_t2b in H2; auto.
      pose proof IHceval' l (bstk ++ l2 :: nil) H2 eq_refl.
      auto.
  - split; [apply ML_Call_here |].
    destruct bstk2.
    + pose proof IHceval' l2 nil H1 eq_refl.
      auto.
    + apply ceval'_single_point_stack_right_t2b in H4; auto.
      pose proof IHceval' l (bstk2 ++ l2 :: nil) H4 eq_refl.
      auto.
  - split.
    + apply ceval'_matched_tail in H4.
      apply ceval'_matched_tail in H5.
      apply ML_Seq; auto.
    + inversion H6; subst; [apply pure_no_point in H1; congruence |].
      pose proof IHceval'2 l4 bstk0 H10 eq_refl.
      simpl in H7.
      pose proof retrieve_func_pure l2 c1 H1.
      rewrite H8.
      rewrite combine_right.
      tauto.
  - split.
    + apply ceval'_matched_tail in H2.
      apply ML_Seq; auto.
      apply com_to_label_pure_matched.
    + inversion H3; subst; [| pose proof com_to_label_pure_no_point c2; congruence].
      pose proof IHceval' l2 bstk0 H6 eq_refl.
      simpl in H4.
      pose proof retrieve_func_pure (com_to_label_pure c2) c2 (com_to_label_pure_is_pure _).
      rewrite H5.
      rewrite combine_left.
      tauto.
  - split.
    + apply ceval'_matched_tail in H2.
      apply ML_Seq; auto.
      apply com_to_label_pure_matched.
    + inversion H3; subst; [pose proof com_to_label_pure_no_point c1; congruence |].
      pose proof IHceval' l2 bstk0 H7 eq_refl.
      simpl in H4.
      pose proof retrieve_func_pure (com_to_label_pure c1) c1 (com_to_label_pure_is_pure _).
      rewrite H5.
      rewrite combine_right.
      tauto.
  - split.
    + apply ceval'_matched_tail in H3.
      apply ML_If; auto.
      apply com_to_label_pure_matched.
    + inversion H4; subst; [| pose proof com_to_label_pure_no_point c2; congruence].
      pose proof IHceval' l2 bstk1 H7 eq_refl.
      pose proof retrieve_func_pure (com_to_label_pure c2) c2 (com_to_label_pure_is_pure _).
      rewrite H6.
      rewrite combine_left.
      simpl in H5.
      tauto.
  - split.
    + apply ceval'_matched_tail in H3.
      apply ML_If; auto.
      apply com_to_label_pure_matched.
    + inversion H4; subst; [pose proof com_to_label_pure_no_point c1; congruence |].
      pose proof IHceval' l2 bstk1 H9 eq_refl.
      pose proof retrieve_func_pure (com_to_label_pure c1) c1 (com_to_label_pure_is_pure _).
      rewrite H6.
      rewrite combine_right.
      simpl in H5.
      tauto.
  - split; auto.
    + apply ceval'_matched_tail in H2.
      apply ML_If; auto.
      apply com_to_label_pure_matched.
    + inversion H3; subst; [| pose proof com_to_label_pure_no_point c2; congruence].
      pose proof IHceval' l2 bstk0 H6 eq_refl.
      simpl in H4.
      pose proof retrieve_func_pure (com_to_label_pure c2) c2 (com_to_label_pure_is_pure _).
      rewrite H5.
      rewrite combine_left.
      tauto.
  - split.
    + apply ceval'_matched_tail in H2.
      apply ML_If; auto.
      apply com_to_label_pure_matched.
    + inversion H3; subst; [pose proof com_to_label_pure_no_point c1; congruence |].
      pose proof IHceval' l2 bstk0 H8 eq_refl.
      simpl in H4.
      pose proof retrieve_func_pure (com_to_label_pure c1) c1 (com_to_label_pure_is_pure _).
      rewrite H5.
      rewrite combine_right.
      tauto.
  - split.
    + apply ML_While.
      apply com_to_label_pure_matched.
    + destruct (retrieve_func (com_to_label_pure c) c); auto.
  - split.
    + apply ML_While.
      apply ceval'_matched_tail in H3; auto.
    + inversion H4; subst.
      pose proof IHceval' l2 bstk1 H6 eq_refl.
      simpl in H5; tauto.
  - split.
    + apply ceval'_matched_tail in H4; auto.
    + pose proof IHceval'2 l0 bstk1 H5 eq_refl.
      simpl in H6; tauto.
  - split.
    + apply ML_While.
      apply ceval'_matched_tail in H2; auto.
    + inversion H3; subst.
      pose proof IHceval' l2 bstk0 H5 eq_refl.
      simpl in H4.
      tauto.
  - split.
    + apply ceval'_matched_tail in H3; auto.
    + pose proof IHceval'2 l0 bstk0 H4 eq_refl.
      simpl in H5.
      tauto.
Qed.

Lemma ceval'_single_point_stack_left_bottom :
  forall fc c l1 l2 bstk1 bstk2 st1 st2,
  ceval' fc c (l1 :: bstk1 ++ l2 :: nil) bstk2 st1 st2 ->
  single_point l1.
Proof.
  intros.
  remember (l1 :: bstk1 ++ l2 :: nil) as bstk'.
  revert Heqbstk'.
  revert l1 bstk1 l2.
  induction H; intros; inversion Heqbstk'; subst;
  try apply SP_Here;
  app_cons_nil H6; app_cons_nil H5; app_cons_nil H4;
  app_cons_nil H3; app_cons_nil H2; app_cons_nil H1.
  - pose proof IHceval'1 l1 bstk0 l5 eq_refl.
    apply SP_Seq1; auto.
  - pose proof IHceval' l1 bstk0 l3 eq_refl.
    apply SP_Seq1; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l1 bstk0 l3 eq_refl.
    apply SP_Seq2; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l1 bstk0 l3 eq_refl.
    apply SP_If1; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l1 bstk0 l3 eq_refl.
    apply SP_If2; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l1 bstk0 l3 eq_refl.
    apply SP_While; auto.
  - pose proof IHceval'1 l1 bstk0 l3 eq_refl.
    apply SP_While; auto.
Qed.

Lemma ceval'_single_point_stack_right_bottom :
  forall fc c l1 l2 bstk1 bstk2 st1 st2,
  ceval' fc c bstk1 (l1 :: bstk2 ++ l2 :: nil) st1 st2 ->
  single_point l1.
Proof.
  intros.
  remember (l1 :: bstk2 ++ l2 :: nil) as bstk'.
  revert Heqbstk'.
  revert l1 bstk2 l2.
  induction H; intros; inversion Heqbstk'; subst;
  try apply SP_Here;
  app_cons_nil H6; app_cons_nil H5; app_cons_nil H4;
  app_cons_nil H3; app_cons_nil H2; app_cons_nil H1.
  - pose proof IHceval'2 l4 bstk0 l5 eq_refl.
    apply SP_Seq2; auto.
  - pose proof IHceval' l2 bstk0 l3 eq_refl.
    apply SP_Seq1; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l2 bstk0 l3 eq_refl.
    apply SP_Seq2; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l2 bstk2 l3 eq_refl.
    apply SP_If1; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l2 bstk2 l3 eq_refl.
    apply SP_If2; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l2 bstk0 l3 eq_refl.
    apply SP_If1; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l2 bstk0 l3 eq_refl.
    apply SP_If2; auto.
    apply com_to_label_pure_is_pure.
  - pose proof IHceval' l2 bstk2 l3 eq_refl.
    apply SP_While; auto.
  - pose proof IHceval'2 l0 bstk2 l3 eq_refl; auto.
  - pose proof IHceval' l2 bstk0 l3 eq_refl.
    apply SP_While; auto.
  - pose proof IHceval'2 l0 bstk0 l3 eq_refl; auto.
Qed.

Lemma multi_ceval'_stack_bottom:
  forall fc lf stk1 f st,
    multi_ceval' fc lf stk1 ((func_bdy f, None, st) :: nil) ->
    get_bottom_com stk1 = func_bdy f.
Proof.
  intros.
  apply Operators_Properties.clos_rt_rt1n in H.
  remember ((func_bdy f, None, st) :: nil) as stk2.
  induction H; subst.
  - auto.
  - specialize (IHclos_refl_trans_1n (eq_refl _)).
    inversion H; subst; destruct stk; exact IHclos_refl_trans_1n.
Qed.

Lemma reentry_bottom_level:
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs loc_R : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion') (c : com) (l1 : lbstk) (l2 : option lbstk) (st1 st0 : state'),

  (* Rule 2 *)
  (forall (invs' : FUN.rAssertion fc f),
    (invs' = fun j st =>
        exists z, invs {| fname := f; fvalid := in_eq f lf ; index_label := j|} z st /\ loc_R {| fname := f; fvalid := in_eq f lf ; index_label := j|} z st) ->
  func_triple' fc f P Q invs' invs') ->

  get_bottom_com ((c, Some l1, st1) :: nil) = func_bdy f ->
  stk_to_pre fc lf f pt invs loc_R R ((c, Some l1, st1) :: nil) P Q ->
  middle_ceval' fc lf ((c, Some l1, st1) :: nil) ((c, l2, st0) :: nil) ->

  stk_to_pre fc lf f pt invs loc_R R ((c, l2, st0) :: nil) P Q.
Proof.
  intros.
(*   rename H0 into Hctop. *)
  rename H0 into Hbt.
  rename H1 into Hstk.
  inversion H2; subst.
  - simpl in Hbt. subst c.
    pose proof H (fun (j : COM.index_label_set fc (func_bdy f)) (st : state') =>
      exists z : pt {| fname := f; fvalid := in_eq f lf; index_label := j |},
        invs {| fname := f; fvalid := in_eq f lf; index_label := j |} z st /\
        loc_R {| fname := f; fvalid := in_eq f lf; index_label := j |} z st) eq_refl.
    destruct l1; simpl in Hstk; destruct Hstk.
    + destruct H1.
      destruct H0 as [? _].
      eapply H0; [| exact H3].
      remember (rev l1) as l1'.
      destruct l1';
      pose proof rev_involutive l1 as Hrev;
      rewrite <- Heql1' in Hrev;
      simpl in *;
      subst.
      {
        rewrite (ceval'_pure_head _ _ _ _ _ _ _ H1 H4) in H4.
        apply H4.
      }
      {
        apply ceval'_single_point_stack_left_bottom in H4.
        apply pure_no_point in H1.
        congruence.
      }
    + destruct H1 as [? [i [x [? [? [? ?]]]]]]. subst.
      destruct i. simpl in *. subst.
      destruct H0 as [_ [_ [? _]]].
      eapply H0.
      * rewrite H5 in H4.
        apply H4.
      * replace (in_eq fname0 lf) with fvalid0; [| apply proof_irrelevance].
        exists x. exact H7.
  - simpl in Hbt. subst.
    pose proof H (fun (j : COM.index_label_set fc (func_bdy f)) (st : state') =>
      exists z : pt {| fname := f; fvalid := in_eq f lf; index_label := j |},
        invs {| fname := f; fvalid := in_eq f lf; index_label := j |} z st /\
        loc_R {| fname := f; fvalid := in_eq f lf; index_label := j |} z st) eq_refl.
    destruct l1; simpl in Hstk; destruct Hstk.
    + destruct H1.
      destruct bstk2; simpl.
      {
        right; split; auto.
        destruct H0 as [_ [? _]].
        rewrite (ceval'_pure_head _ _ _ _ _ _ _ H1 H10) in H10.
        unfold triple_PR in H0.
        assert (valid_index_label fc (func_bdy f) (l0 :: nil)).
        {
          split.
          + simpl; omega.
          + apply ceval'_matched_lbstk_right in H10; auto.
        }
        remember (rev l1) as l1'.
        destruct l1';
        pose proof rev_involutive l1 as Hrev;
        rewrite <- Heql1' in Hrev;
        simpl in *;
        subst.
        + specialize (H0 _ _ (exist _ (l0 :: nil) H4) H10 H3).
          destruct H0 as [? [? ?]].
          exists {|
          fname := f;
          fvalid := in_eq f lf;
          index_label := exist (valid_index_label fc (func_bdy f)) (l0 :: nil) H4 |}, x.
          simpl.
          repeat split; auto.
        + apply ceval'_single_point_stack_left_bottom in H10.
          pose proof com_to_label_pure_no_point (func_bdy f).
          congruence.
      }
      {
        pose proof H10.
        apply ceval'_single_point_stack_right_bottom in H4.
        right; split; auto.
        destruct H0 as [_ [? _]].
        rewrite (ceval'_pure_head _ _ _ _ _ _ _ H1 H10) in H10.
        unfold triple_PR in H0.
        assert (valid_index_label fc (func_bdy f) ((l2 :: bstk2) ++ l0 :: nil)).
        {
          split.
          + simpl; omega.
          + apply ceval'_matched_lbstk_right in H10; auto.
        }
        remember (rev l1) as l1'.
        destruct l1';
        pose proof rev_involutive l1 as Hrev;
        rewrite <- Heql1' in Hrev;
        simpl in *;
        subst.
        + specialize (H0 _ _ (exist _ ((l2 :: bstk2) ++ l0 :: nil) H6) H10 H3).
          destruct H0 as [? [? ?]].
          exists {|
          fname := f;
          fvalid := in_eq f lf;
          index_label := exist (valid_index_label fc (func_bdy f)) ((l2 :: bstk2) ++ l0 :: nil) H6 |}, x.
          simpl.
          repeat split; auto.
        + apply ceval'_single_point_stack_left_bottom in H10.
          pose proof com_to_label_pure_no_point (func_bdy f).
          congruence.
      }
    + destruct H1 as [? [i [x [? [? [? ?]]]]]]. subst.
      destruct bstk2.
      {
        right; split; auto.
        destruct i. simpl in *. subst fname0.
        rewrite H4 in *.
        assert (valid_index_label fc (func_bdy f) (l0 :: nil)).
        {
          split.
          + simpl. omega.
          + apply ceval'_matched_lbstk_right in H10; auto.
        }
        replace (l0 :: nil) with (proj1_sig (exist _ (l0 :: nil) H6)) in H10; auto.
        assert (exists z : pt {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |},
    invs {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |} z st1 /\ loc_R {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |} z st1).
        {
          replace (in_eq f lf) with fvalid0.
          exists x. auto.
          apply proof_irrelevance.
        }
        destruct H0 as [_ [_ [_ ?]]].
        specialize (H0 _ _ _ (exist _ (l0 :: nil) H6) H10 H8); clear H8.
        destruct H0 as [? [? ?]].
        exists {| fname := f; fvalid := in_eq f lf; index_label := exist (valid_index_label fc (func_bdy f)) (l0 :: nil) H6 |}, x0.
        (* Clear goals *)
        repeat split; auto.
      }
      {
        pose proof H10 as Hl2.
        apply ceval'_single_point_stack_right_t2b in Hl2; auto.
        right; split; auto.
        destruct i. simpl in *. subst fname0.
        rewrite H4 in *.
        assert (valid_index_label fc (func_bdy f) (l2 :: bstk2 ++ l0 :: nil)).
        {
          split.
          + simpl. omega.
          + apply ceval'_matched_lbstk_right in H10; auto.
        }
        replace (l2 :: bstk2 ++ l0 :: nil) with (proj1_sig (exist _ (l2 :: bstk2 ++ l0 :: nil) H6)) in H10; auto.
        assert (exists z : pt {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |},
    invs {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |} z st1 /\ loc_R {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |} z st1).
        {
          replace (in_eq f lf) with fvalid0.
          exists x. auto.
          apply proof_irrelevance.
        }
        destruct H0 as [_ [_ [_ ?]]].
        specialize (H0 _ _ _ (exist _ (l2 :: bstk2 ++ l0 :: nil) H6) H10 H8); clear H8.
        destruct H0 as [? [? ?]].
        exists {| fname := f; fvalid := in_eq f lf; index_label := exist (valid_index_label fc (func_bdy f)) (l2 :: bstk2 ++ l0 :: nil) H6 |}, x0.
        (* Clear goals *)
        repeat split; auto.
      }
Qed.

Lemma reentry_higher_level:
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs loc_R : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion') (c : com) (l1 : lbstk) (l2 : option lbstk) (st1 st0 : state') p stk,

  (* Rule 1 *)
  (forall f' (Hin: In f' lf) (i: index_set fc (f :: lf)) (x: pt i) invs',
    (invs' = fun j st =>
        exists y, R i {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} x y 
        /\ invs {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st /\ loc_R {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st) ->
  func_triple' fc f' (invs i x) (invs i x) invs' invs') ->

  (forall (c0 : com) (l : option lbstk) (st : state') (p0 : com * option lbstk * state') (stk' stk'' : restk),
    (c, Some l1, st1) :: p :: stk = stk' ++ p0 :: stk'' ->
    In (c0, l, st) stk' -> exists f' : func, In f' lf /\ c0 = func_bdy f') ->
  stk_to_pre fc lf f pt invs loc_R R ((c, Some l1, st1) :: p :: stk) P Q ->
  middle_ceval' fc lf ((c, Some l1, st1) :: p :: stk) ((c, l2, st0) :: p :: stk) ->

  stk_to_pre fc lf f pt invs loc_R R ((c, l2, st0) :: p :: stk) P Q.
Proof.
  intros.
  rename H0 into Hctop.
  rename H1 into Hstk.
  destruct p as [[cp lp] stp].
  destruct lp; [| inversion Hstk].
  destruct l as [| lp plstk]; [inversion Hstk |].
  inversion H2; subst.
  (* Transition in higher level, from some point to the end *)
  - simpl in Hstk.
    destruct Hstk as [j [y [? [? [? [? ?]]]]]].
    destruct l1; destruct H6.
    (* From head to tail *)
    + destruct H6.
      pose proof Hctop c (Some (l :: l1)) st1 (cp, Some (lp :: plstk), stp) ((c, Some (l :: l1), st1)::nil) stk (eq_refl _) (in_eq _ _) as [f' [? ?]].
      subst.
      (* Construct index and parameter *)
      exists j, y.
      repeat split; auto.
      (* Apply hoare rule, select PQ to use *)
      pose proof H f' H8 j y
        (fun (j0 : FUN.index_label_set fc f') (st : state') =>
      exists y0 : pt {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |},
        R j {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |} y y0 /\
        invs {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |} y0 st /\
        loc_R {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |} y0 st) (eq_refl _) as [? _].
      eapply H1.
      * rewrite (ceval'_pure_head _ _ _ _ _ _ _ H6 H4) in H4.
        remember (rev l1) as l';
        pose proof rev_involutive l1 as Hrev;
        rewrite <- Heql' in Hrev;
        destruct l';
        subst.
        {
          apply H4.
        }
        {
          simpl in H4.
          apply ceval'_single_point_stack_left_bottom in H4.
          pose proof com_to_label_pure_no_point (func_bdy f').
          congruence.
        }
      * auto.
    (* From middle to tail *)
    + destruct H6 as [? [i [x [? [? [? [? [? ?]]]]]]]]. subst c.
      (* Utilize information in reachable_param *)
      (* remember ((func_bdy (fname fc (f :: lf) i), Some (l :: l1), st1) :: (cp, Some (lp :: plstk), stp) :: stk) as stk'.
      induction H5; subst; inversion Heqstk'; subst.
      clear IHreachable_param. *)
      (* Construct index and parameter *)
      simpl.
      exists j, y.
      repeat split; auto.
      (* Apply hoare rule, select RQ to use *)
      pose proof H (fname fc (f :: lf) i) H9 j y (fun (j0 : FUN.index_label_set fc (fname fc (f :: lf) i)) (st : state') =>
      exists
        y0 : pt
               {|
               fname := fname fc (f :: lf) i;
               fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
               index_label := j0 |},
        R j
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := j0 |} y y0 /\
        invs
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := j0 |} y0 st /\
        loc_R
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := j0 |} y0 st) (eq_refl _) as [_ [_ [? _]]].
      eapply H7; clear H7.
      * rewrite <- H8.
        apply H4.
      * replace{|
        fname := fname fc (f :: lf) i;
        fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
        index_label := index_label fc (f :: lf) i |} with i.
        -- exists x.
           tauto.
        -- destruct i.
           simpl. f_equal.
           apply proof_irrelevance.
  (* Transition within higher level, from some point to one reentry point *)
  - simpl in Hstk.
    destruct Hstk as [j [y [? [? [? [? ?]]]]]].
    destruct l1; destruct H6.
    (* From head to middle *)
    + destruct H6.
      destruct bstk2.
      {
        exists j, y.
        repeat split; auto.
        simpl.
        right; split; auto.
        pose proof Hctop c (Some (l :: l1)) st1 (cp, Some (lp :: plstk), stp) ((c, Some (l :: l1), st1)::nil) stk (eq_refl _) (in_eq _ _) as [f' [? ?]]. subst.
        remember (rev l1) as l';
        pose proof rev_involutive l1 as Hrev;
        rewrite <- Heql' in Hrev;
        destruct l';
        subst; [|
          apply ceval'_single_point_stack_left_bottom in H10;
          apply pure_no_point in H6;
          congruence].
        (* Prepare conditions *)
        rewrite (ceval'_pure_head _ _ _ _ _ _ _ H6 H10) in H10.
        assert (valid_index_label fc (func_bdy f') (l0 :: nil)).
        {
          split.
          - simpl. omega.
          - apply ceval'_matched_lbstk_right in H10; auto.
        }
        pose proof H f' H8 j y (fun (j0 : FUN.index_label_set fc f') (st : state') =>
       exists y0 : pt {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |},
         R j {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |} y y0 /\
         invs {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |} y0 st /\
         loc_R {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |} y0 st) (eq_refl _) as [_ [? _]].
        specialize (H9 _ _ (exist _ (l0::nil) H1) H10 H7).
        destruct H9 as [x [? [? ?]]].
        exists {|
          fname := f';
          fvalid := in_cons f f' lf H8;
          index_label := exist (valid_index_label fc (func_bdy f')) (l0 :: nil) H1 |}, x.
        repeat split; auto.
      }
      {
        simpl.
        exists j, y.
        repeat split; auto.
        pose proof ceval'_single_point_stack_right_t2b _ _ _ _ _ _ _ _ H5 H10.
        right; split; auto.
        remember (rev l1) as l';
        pose proof rev_involutive l1 as Hrev;
        rewrite <- Heql' in Hrev;
        destruct l';
        subst; [|
          apply ceval'_single_point_stack_left_bottom in H10;
          apply pure_no_point in H6;
          congruence].
        pose proof Hctop c (Some (l :: nil)) st1 (func_bdy (fname fc (f :: lf) j), Some (lp :: plstk), stp) ((c, Some (l :: nil), st1)::nil) stk (eq_refl _) (in_eq _ _) as [f' [? ?]]. subst.
        (* Prepare conditions *)
        rewrite (ceval'_pure_head _ _ _ _ _ _ _ H6 H10) in H10.
        assert (valid_index_label fc (func_bdy f') ((l2 :: bstk2) ++ l0 :: nil)).
        {
          split.
          - simpl. omega.
          - apply ceval'_matched_lbstk_right in H10; auto.
        }
        pose proof H f' H1 j y (fun (j0 : FUN.index_label_set fc f') (st : state') =>
       exists y0 : pt {| fname := f'; fvalid := in_cons f f' lf H1; index_label := j0 |},
         R j {| fname := f'; fvalid := in_cons f f' lf H1; index_label := j0 |} y y0 /\
         invs {| fname := f'; fvalid := in_cons f f' lf H1; index_label := j0 |} y0 st /\
         loc_R {| fname := f'; fvalid := in_cons f f' lf H1; index_label := j0 |} y0 st) (eq_refl _) as [_ [? _]].
        specialize (H11 _ _ (exist _ ((l2 :: bstk2) ++ l0 :: nil) H9) H10 H7).
        destruct H11 as [x [? [? ?]]].
        exists {|
        fname := f';
        fvalid := in_cons f f' lf H1;
        index_label := exist (valid_index_label fc (func_bdy f'))
                         ((l2 :: bstk2) ++ l0 :: nil) H9 |}, x.
        (* Clear goals *)
        repeat split; auto.
      }
    (* From middle to middle *)
    + destruct H6.
      destruct bstk2.
      {
        simpl.
        exists j, y.
        repeat split; auto.
        right. split; auto.
        destruct H7 as [i [x [? [? [? [? [? ?]]]]]]]; subst.
        (* Utilize information in reachable_param *)
(*         remember ((@func_bdy fc (fname fc (f :: lf) i), @Some (list label) (l :: l1), st1) :: (func_bdy (fname fc (f :: lf) j), Some (lp :: plstk), stp) :: stk) as stk'.
        induction H4; inversion Heqstk'; subst.
        clear IHreachable_param. *)
        (* Prepare conditions *)
        assert (valid_index_label fc (func_bdy (fname fc (f :: lf) i)) (l0 :: nil)).
        {
          split.
          + simpl. omega.
          + apply ceval'_matched_lbstk_right in H10; auto.
        }
        pose proof H (fname fc (f :: lf) i) H9 j y (fun (j0 : FUN.index_label_set fc (fname fc (f :: lf) i)) (st : state') =>
      exists
        y0 : pt
               {|
               fname := fname fc (f :: lf) i;
               fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
               index_label := j0 |},
        R j
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := j0 |} y y0 /\
        invs
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := j0 |} y0 st /\
        loc_R
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := j0 |} y0 st) (eq_refl _) as [_ [_ [_ ?]]].
        assert (exists
        y0 : pt
               {|
               fname := fname fc (f :: lf) i;
               fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
               index_label := index_label fc (f :: lf) i |},
        R j
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := index_label fc (f :: lf) i |} y y0 /\
        invs
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := index_label fc (f :: lf) i |} y0 st1 /\
        loc_R
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := index_label fc (f :: lf) i |} y0 st1).
        {
          replace {|
           fname := fname fc (f :: lf) i;
           fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
           index_label := index_label fc (f :: lf) i |} with i.
           2:{
            destruct i.
            f_equal. apply proof_irrelevance.
           }
           exists x.
           tauto.
        }
        rewrite H8 in *.
        specialize (H7 _ _ _ (exist _ (l0 :: nil) H1) H10 H14); clear H14.
        destruct H7 as [x0 [? [? ?]]].
        exists {|
        fname := fname fc (f :: lf) i;
        fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
        index_label := exist (valid_index_label fc (func_bdy (fname fc (f :: lf) i))) (l0 :: nil) H1 |}, x0.
        simpl.
        repeat split; auto.
      }
      {
        pose proof H10 as Hl2.
        apply ceval'_single_point_stack_right_t2b in Hl2; auto.
        
        exists j, y.
        repeat split; auto.
        simpl.
        right. split; auto.
        destruct H7 as [i [x [? [? [? [? [? ?]]]]]]]; subst.
        (* Prepare conditions *)
        assert (valid_index_label fc (func_bdy (fname fc (f :: lf) i)) ((l2 :: bstk2) ++ l0 :: nil)).
        {
          split.
          + simpl. omega.
          + apply ceval'_matched_lbstk_right in H10; auto.
        }
        pose proof H (fname fc (f :: lf) i) H9 j y (fun (j0 : FUN.index_label_set fc (fname fc (f :: lf) i)) (st : state') =>
      exists
        y0 : pt
               {|
               fname := fname fc (f :: lf) i;
               fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
               index_label := j0 |},
        R j
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := j0 |} y y0 /\
        invs
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := j0 |} y0 st /\
        loc_R
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := j0 |} y0 st) (eq_refl _) as [_ [_ [_ ?]]].
        assert (exists
        y0 : pt
               {|
               fname := fname fc (f :: lf) i;
               fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
               index_label := index_label fc (f :: lf) i |},
        R j
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := index_label fc (f :: lf) i |} y y0 /\
        invs
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := index_label fc (f :: lf) i |} y0 st1 /\
        loc_R
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := index_label fc (f :: lf) i |} y0 st1).
        {
          replace {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
          index_label := index_label fc (f :: lf) i |} with i.
          2:{
            destruct i.
            f_equal. apply proof_irrelevance.
          }
          exists x.
          repeat split; auto.
        }
        rewrite H8 in *.
        specialize (H7 _ _ _ (exist _ ((l2 :: bstk2) ++ l0 :: nil) H1) H10 H14); clear H14.
        destruct H7 as [x0 [? [? ?]]].
        exists {|
        fname := fname fc (f :: lf) i;
        fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
        index_label := exist (valid_index_label fc (func_bdy (fname fc (f :: lf) i))) ((l2 :: bstk2) ++ l0 :: nil) H1 |}, x0.
        repeat split; auto.
      }
  - pose proof eq_refl (length stk).
    rewrite <- H14 in H0 at 1.
    simpl in H0. omega.
Qed.

Lemma multi_ceval'_ctop :
  forall fc lf stk1 c l st p0 p (stk' stk'' : restk),
    multi_ceval' fc lf (p0 :: nil) stk1 ->
    stk1 = stk' ++ p :: stk'' ->
    In (c, l, st) stk' ->
    exists f', In f' lf /\ c = (func_bdy f').
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ?.
  remember (p0 :: nil) as stk2.
  apply Operators_Properties.clos_rt_rtn1 in H.
  revert c l st p stk' stk''.
  induction H; intros; subst.
  - destruct stk'.
    + inversion H0.
    + pose proof eq_refl (length (p0 :: nil)).
      rewrite H in H1 at 1.
      rewrite app_length in H1.
      simpl in H1. omega.
  - inversion H; subst.
    + destruct stk'; [inversion H2 |].
      destruct H2.
      * inversion H2; subst.
        inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c (Some bstk) st1 p ((c, Some bstk, st1) :: stk') stk'' eq_refl (in_eq _ _).
        exact H2.
      * inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c l st p ((c0, Some bstk, st1) :: stk') stk'' eq_refl (in_cons _ _ _ H2).
        exact H3.
    + destruct stk'; [inversion H2 |].
      destruct H2.
      * inversion H2; subst.
        inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c (Some bstk1) st1 p ((c, Some bstk1, st1) :: stk') stk'' eq_refl (in_eq _ _).
        exact H2.
      * inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c l st p ((c0, Some bstk1, st1) :: stk') stk'' eq_refl (in_cons _ _ _ H2).
        exact H4.
    + remember ((c1, Some (bstk ++ l1 :: nil), (sstk, glb)) :: stk) as stk'''.
      clear dependent stk.
      rename stk''' into stk.
      destruct stk'; [inversion H2 |].
      destruct H2.
      * inversion H2; subst.
        inversion H1; subst.
        exists f. tauto.
      * inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c l st p stk' stk'' eq_refl H2.
        exact H4.
    + destruct stk'; [inversion H2 |].
      destruct H2.
      * inversion H2; subst.
        inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c (Some (bstk ++ l2 :: nil)) (sstk, glb2) p ((c1, None, (loc :: nil, glb1)) :: (c, Some (bstk ++ l2 :: nil), (sstk, glb2)) :: stk') stk'' (eq_refl _) (in_cons _ _ _ (in_eq _ _)).
        exact H2.
      * inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c l st p ((c1, None, (loc :: nil, glb1)) :: (c2, Some (bstk ++ l2 :: nil), (sstk, glb2)) :: stk') stk'' (eq_refl _) (in_cons _ _ _ (in_cons _ _ _ H2)).
        exact H4.
Qed.

Lemma multi_ceval'_left_bottom_single_point :
  forall fc lf stk c1 c2 l l1 bstk l2 st1 st2,
  single_point l2 ->
  multi_ceval' fc lf ((c1, Some (l :: nil), st1) :: nil) (stk ++ (c2, Some (l1 :: bstk ++ l2 :: nil), st2) :: nil) ->
  single_point l1.
Proof.
  intros.
  remember ((c1, Some (l :: nil), st1) :: nil) as stk1.
  remember (stk ++ (c2, Some (l1 :: bstk ++ l2 :: nil), st2) :: nil) as stk2.
  revert H Heqstk2.
  revert stk c2 l1 bstk l2 st2.
  apply Operators_Properties.clos_rt_rtn1 in H0.
  induction H0; intros; subst.
  - destruct stk; inversion Heqstk2; subst.
    + app_cons_nil H3.
    + app_cons_nil H2.
  - inversion H; subst.
    + destruct stk; inversion H2; subst.
      pose proof IHclos_refl_trans_n1 ((c, Some bstk0, st0) :: stk) c2 l1 bstk l2 st2 H1 eq_refl.
      auto.
    + destruct stk; inversion H2; subst.
      * destruct bstk2; inversion H6; subst; [app_cons_nil H8 |].
        apply app_inj_tail in H8 as [? ?]; subst.
        eapply ceval'_single_point_stack_right_t2b.
        exact H3. exact H7.
      * pose proof IHclos_refl_trans_n1 ((c, Some bstk1, st0) :: stk) c2 l1 bstk l2 st2 H1 eq_refl.
        auto.
    + destruct stk; inversion H2; subst.
      destruct stk; inversion H7; subst.
      * destruct bstk0; inversion H8; subst; [app_cons_nil H10 |].
        apply app_inj_tail in H10 as [? ?]; subst.
        pose proof IHclos_refl_trans_n1 nil c2 l1 bstk l2 (sstk, glb) H1 eq_refl.
        auto.
      * pose proof IHclos_refl_trans_n1 ((c0, Some (bstk0 ++ l0 :: nil), (sstk, glb)) :: stk) c2 l1 bstk l2 st2 H1 eq_refl.
        auto.
    + destruct stk; inversion H2; subst.
      * destruct bstk0; inversion H6; subst; [app_cons_nil H8 |].
        apply app_inj_tail in H8 as [? ?]; subst.
        pose proof IHclos_refl_trans_n1 ((c0, None, (loc :: nil, glb1)) :: nil) c2 l1 bstk l2 (sstk, glb2) H1 eq_refl.
        auto.
      * pose proof IHclos_refl_trans_n1 ((c0, None, (loc :: nil, glb1)) :: (c3, Some (bstk0 ++ l0 :: nil), (sstk, glb2)) :: stk) c2 l1 bstk l2 st2 H1 eq_refl.
        auto.
Qed.

Lemma multi_ceval'_left_bottom_bottom_single_point :
  forall fc lf stk' stk'' c1 c2 l l1 bstk l2 st1 st2,
  single_point l2 ->
  multi_ceval' fc lf ((c1, Some (l :: nil), st1) :: nil) (stk' ++ (c2, Some (l1 :: bstk ++ l2 :: nil), st2) :: stk'') ->
  single_point l1.
Proof.
  intros.
  remember ((c1, Some (l :: nil), st1) :: nil) as stk1.
  remember (stk' ++ (c2, Some (l1 :: bstk ++ l2 :: nil), st2) :: stk'') as stk2.
  revert H Heqstk2.
  revert stk' c2 l1 bstk l2 st2 stk''.
  apply Operators_Properties.clos_rt_rtn1 in H0.
  induction H0; intros; subst.
  - destruct stk'; inversion Heqstk2; subst.
    + app_cons_nil H3.
    + pose proof eq_refl (length (stk' ++ (c2, Some (l1 :: bstk ++ l2 :: nil), st2) :: stk'')).
      rewrite <- H2 in H0 at 1.
      rewrite app_length in H0.
      simpl in H0.
      omega.
  - inversion H; subst.
    + destruct stk'; inversion H2; subst.
      pose proof IHclos_refl_trans_n1 ((c, Some bstk0, st0) :: stk') c2 l1 bstk l2 st2 stk'' H1 eq_refl.
      auto.
    + destruct stk'; inversion H2; subst.
      * destruct bstk2; inversion H6; subst; [app_cons_nil H8 |].
        apply app_inj_tail in H8 as [? ?]; subst.
        eapply ceval'_single_point_stack_right_t2b.
        exact H3. exact H7.
      * pose proof IHclos_refl_trans_n1 ((c, Some bstk1, st0) :: stk') c2 l1 bstk l2 st2 stk'' H1 eq_refl.
        auto.
    + destruct stk'; inversion H2; subst; [app_cons_nil H8 |].
      destruct stk'; inversion H7; subst.
      * destruct bstk0; inversion H8; subst; [app_cons_nil H10 |].
        apply app_inj_tail in H10 as [? ?]; subst.
        pose proof IHclos_refl_trans_n1 nil c2 l1 bstk l2 (sstk, glb) stk'' H1 eq_refl.
        auto.
      * pose proof IHclos_refl_trans_n1 ((c0, Some (bstk0 ++ l0 :: nil), (sstk, glb)) :: stk') c2 l1 bstk l2 st2 stk'' H1 eq_refl.
        auto.
    + destruct stk'; inversion H2; subst.
      * destruct bstk0; inversion H6; subst; [app_cons_nil H8 |].
        apply app_inj_tail in H8 as [? ?]; subst.
        pose proof IHclos_refl_trans_n1 ((c0, None, (loc :: nil, glb1)) :: nil) c2 l1 bstk l2 (sstk, glb2) stk'' H1 eq_refl.
        auto.
      * pose proof IHclos_refl_trans_n1 ((c0, None, (loc :: nil, glb1)) :: (c3, Some (bstk0 ++ l0 :: nil), (sstk, glb2)) :: stk') c2 l1 bstk l2 st2 stk'' H1 eq_refl.
        auto.
Qed.

Theorem reentry_invariant :
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs loc_R : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion'),

  (forall i x, globalp' (invs i x) /\ localp' (loc_R i x)) ->

  (* Rule 1 *)
  (forall f' (Hin: In f' lf) (i: index_set fc (f :: lf)) (x: pt i) invs',
    (invs' = fun j st =>
        exists y, R i {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} x y 
        /\ invs {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st /\ loc_R {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st) ->
  func_triple' fc f' (invs i x) (invs i x) invs' invs') ->

  (* Rule 2 *)
  (forall (invs' : FUN.rAssertion fc f),
    (invs' = fun j st =>
        exists z, invs {| fname := f; fvalid := in_eq f lf ; index_label := j|} z st /\ loc_R {| fname := f; fvalid := in_eq f lf ; index_label := j|} z st) ->
  func_triple' fc f P Q invs' invs') ->

  func_triple fc lf (A'2A P) f (A'2A Q).
Proof.
  unfold A'2A in *.
  intros.
  rename H into Ginv.
  rename H0 into H.
  rename H1 into H0.
  unfold func_triple.
  intros.
  destruct st1 as [loc1 glb1].
  destruct st2 as [loc2 glb2].
  apply ceval_multi_ceval' in H1.
  remember ((func_bdy f, Some ((com_to_label_pure (func_bdy f)) :: nil), (loc1 :: nil, glb1)) :: nil) as stk1.
  (* Generalized precondition *)
  assert (stk_to_pre fc lf f pt invs loc_R R stk1 P Q).
  {
    subst. simpl.
    left.
    split.
    apply com_to_label_pure_is_pure.
    exact H2.
  }
  remember (func_bdy f, Some (com_to_label_pure (func_bdy f) :: nil), (loc1 :: nil, glb1)) as p'.
  assert (multi_ceval' fc lf (p' :: nil) stk1) as Hfront.
  {
    subst.
    apply rt_refl.
  }
  assert (snd (fst p') = Some (com_to_label_pure (func_bdy f) :: nil)) as Hp'lbstk.
  {
    subst.
    auto.
  }
  clear dependent loc1.
  clear glb1.
  clear Heqstk1.
  apply Operators_Properties.clos_rt_rt1n in H1.
  remember ((func_bdy f, None, (loc2 :: nil, glb2)) :: nil) as stk2.
  induction H1; intros; subst.
  - simpl in H3. exact H3.
  - apply Operators_Properties.clos_rt1n_rt in H2.
    pose proof multi_ceval'_stack_bottom _ _ _ _ _ H2 as Hbt.
    specialize (IHclos_refl_trans_1n eq_refl).
    inversion H1; subst.
    {
      apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
      - destruct stk.
        (* Transition within the main f, from some point to the end *)
        * eapply reentry_bottom_level; try assumption.
          exact H3. assumption.
        (* Transition in higher level, from some point to the end *)
        * eapply reentry_higher_level; try assumption.
          + intros.
            eapply multi_ceval'_ctop.
            exact Hfront.
            exact H5.
            exact H6.
          + assumption.
          + assumption.
      - apply Operators_Properties.clos_rtn1_rt.
        eapply rtn1_trans.
        exact H1.
        apply Operators_Properties.clos_rt_rtn1.
        exact Hfront.
    }
    {
      apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
      - destruct stk.
        (* Transition with in bottom level, from some point to one reentry point *)
        * eapply reentry_bottom_level; try assumption.
          exact H3. assumption.
        (* Transition within higher level, from some point to one reentry point *)
        * eapply reentry_higher_level; try assumption.
          + intros.
            eapply multi_ceval'_ctop.
            exact Hfront.
            exact H6.
            exact H7.
          + assumption.
          + assumption.
      - apply Operators_Properties.clos_rtn1_rt.
        eapply rtn1_trans.
        exact H1.
        apply Operators_Properties.clos_rt_rtn1.
        exact Hfront.
    }
    {
      apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
      (* Transition from lower level to upper level *)
      - destruct stk.
        + destruct bstk.
          {
            simpl in *.
            destruct H3.
            - destruct H3.
              pose proof pure_no_point l1 H3.
              congruence.
            - destruct H3 as [_ [i [x [? [? [? [? ?]]]]]]].
              exists i, x.
              repeat split; auto.
              left; split.
              * apply com_to_label_pure_is_pure.
              * eapply Ginv.
                exact H9.
          }
          {
            assert (single_point l).
            {
              destruct p'.
              destruct p.
              destruct o; inversion Hp'lbstk; subst.
              eapply multi_ceval'_left_bottom_single_point.
              exact H6.
              change ((c1, Some ((l :: bstk) ++ l1 :: nil), (sstk, glb)) :: nil) with (nil ++ (c1, Some ((l :: bstk) ++ l1 :: nil), (sstk, glb)) :: nil) in Hfront.
              exact Hfront.
            }
            simpl in *.
            destruct H3.
            - destruct H3.
              pose proof pure_no_point l H3.
              congruence.
            - destruct H3 as [_ [i [x [? [? [? [? ?]]]]]]].
              exists i, x.
              repeat split; auto.
              left; split.
              * apply com_to_label_pure_is_pure.
              * eapply Ginv.
                exact H10.
          }
        + destruct p as [[cp lp] stp].
          destruct lp; [| inversion H3].
          destruct l as [| lp plstk]; [inversion H3 |].
          destruct bstk.
          {
            simpl in *.
            destruct H3 as [j [y [? [? [? [? ?]]]]]].
            destruct H10.
            - destruct H10.
              pose proof pure_no_point l1 H10.
              congruence.
            - destruct H10 as [_ [i [x [? [? [? [? [? ?]]]]]]]].
              exists i, x.
              repeat split; auto.
              * exists j, y.
                repeat split; auto.
              * left; split; [apply com_to_label_pure_is_pure |].
                eapply Ginv. apply H14.
          }
          {
            assert (single_point l).
            {
              destruct p' as [[cp' lp'] stp'].
              destruct lp'; inversion Hp'lbstk; subst.
              eapply multi_ceval'_left_bottom_bottom_single_point.
              exact H6.
              change ((c1, Some ((l :: bstk) ++ l1 :: nil), (sstk, glb)) :: (cp, Some (lp :: plstk), stp) :: stk) with (nil ++ (c1, Some ((l :: bstk) ++ l1 :: nil), (sstk, glb)) :: (cp, Some (lp :: plstk), stp) :: stk) in Hfront.
              exact Hfront.
            }
            simpl in *.
            destruct H3 as [j [y [? [? [? [? ?]]]]]].
            destruct H11.
            - destruct H11.
              pose proof pure_no_point l H11.
              congruence.
            - destruct H11 as [_ [i [x [? [? [? [? [? ?]]]]]]]].
              exists i, x.
              repeat split; auto.
              * exists j, y.
                repeat split; auto.
              * left; split; [apply com_to_label_pure_is_pure |].
                eapply Ginv. apply H15.
          }
      - apply Operators_Properties.clos_rtn1_rt.
        eapply rtn1_trans.
        exact H1.
        apply Operators_Properties.clos_rt_rtn1.
        exact Hfront.
    }
    {
      apply IHclos_refl_trans_1n; clear IHclos_refl_trans_1n.
      (* Transition from upper level to lower level *)
      - simpl in H3.
        destruct bstk.
        {
          simpl in *.
          destruct H3 as [j [y [? [? [? [? ?]]]]]].
          destruct stk.
          + right; split; auto.
            exists j, y.
            repeat split; auto.
            * eapply Ginv.
              apply H9.
            * eapply Ginv.
              apply H8.
          + destruct p as [[cp lp] stp].
            destruct lp; [| inversion H3].
            destruct l as [| lp plstk].
            {
              simpl in H3.
              destruct H3 as [? [i [x [? [? [? [? ?]]]]]]].
              destruct i.
              simpl in H11.
              destruct index_label0.
              simpl in H11. subst.
              unfold valid_index_label in v.
              simpl in v. omega.
            }
            simpl in H3.
            destruct H3 as [? [i [x [? [? [? [? ?]]]]]]].
            exists i, x.
            repeat split; auto.
            right; split; auto.
            exists j, y.
            repeat split; auto.
            * eapply Ginv.
              apply H9.
            * eapply Ginv.
              apply H8.
            * auto.
        }
        {
          simpl in *.
          destruct H3 as [j [y [? [? [? [? ?]]]]]].
          assert (single_point l).
          {
            destruct j.
            simpl in H7.
            destruct index_label0.
            simpl in H7. subst.
            unfold valid_index_label in v.
            destruct v as [? ?].
            inversion m; subst.
            auto.
          }
          destruct stk.
          + right; split; auto.
            exists j, y.
            repeat split; auto.
            * eapply Ginv. apply H9.
            * eapply Ginv. apply H8.
          + destruct p as [[cp lp] stp].
            destruct lp; [| inversion H3].
            destruct l0 as [| lp plstk].
            {
              simpl in H3.
              destruct H3 as [? [i [x [? [? [? [? ?]]]]]]].
              destruct i.
              simpl in H12.
              destruct index_label0.
              simpl in H12; subst.
              unfold valid_index_label in v.
              simpl in v. omega.
            }
            simpl in H3.
            destruct H3 as [? [i [x [? [? [? [? ?]]]]]]].
            exists i, x.
            repeat split; auto.
            right; split; auto.
            exists j, y.
            repeat split; auto.
            * eapply Ginv; apply H9.
            * eapply Ginv; apply H8.
            * auto.
        }
      - apply Operators_Properties.clos_rtn1_rt.
        eapply rtn1_trans.
        exact H1.
        apply Operators_Properties.clos_rt_rtn1.
        exact Hfront.
    }
Qed.

Print Assumptions reentry_invariant.

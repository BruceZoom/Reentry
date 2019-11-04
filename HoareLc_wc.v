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
  | ML_Reentry_pure : matched_label LPure CReentry.

Definition combine (f1 f2: option func) : option func :=
  match f1, f2 with
  | Some f1, None => Some f1
  | None, Some f2 => Some f2
  | _, _ => None
  end.

Fixpoint retrive_func (lb: label) (c: com) : option func :=
  match lb, c with
  | LHere, CCall f _ => Some f
  | LHere, _ => None
  | LSeq l1 l2, CSeq c1 c2 => combine (retrive_func l1 c1) (retrive_func l2 c2)
  | LIf _ l1 l2, CIf _ c1 c2 => combine (retrive_func l1 c1) (retrive_func l2 c2)
  | LWhile _ l1, CWhile _ c1 => retrive_func l1 c1
  | _, _ => None
  end.

Fixpoint matched_lbstk (fc: func_context) (bstk: lbstk) (c: com) : Prop :=
  match bstk with
  | nil => True
  | lb :: bstk => single_point lb /\ matched_label lb c /\
      match bstk, (retrive_func lb c) with
      | nil, None => True
      | _, Some f => matched_lbstk fc bstk (func_bdy f)
      | _, None => False
      end
  end.

Definition valid_index_label (fc : func_context) (c : com) (bstk : lbstk) : Prop :=
  length bstk > 0 /\ matched_lbstk fc bstk c.

Definition Assertion' := state' -> Prop.

Definition A'2A (P: Assertion') : Assertion :=
  fun (st: state) => match st with
                     | (loc, glb) => P (loc :: nil, glb)
                     end.

Definition globalp' (P: Assertion') : Prop :=
  forall sstk1 sstk2 glb, P (sstk1, glb) -> P (sstk2, glb).

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

Inductive reachable_param (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (R : index_relation fc (f :: lf) pt) : restk -> forall (i : index_set fc (f :: lf)), (pt i) -> Prop :=
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
Qed.

Definition stk_to_pre (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (stk : restk) (P Q : Assertion') : Prop :=
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
          reachable_param fc lf f pt R ((c1, Some (l1 :: bstk), st1) :: stk') i x /\
          invs i x st1)
      | None => Q st1                     (* bottom level tail *)
      | _ => False
      end
    | _ =>                                (* during reentry *)
      match l1 with
      | Some (l1 :: bstk) =>
        (is_pure l1 /\ exists i x,        (* current level head *)
          reachable_param fc lf f pt R stk' i x /\ invs i x st1) \/
        (single_point l1 /\ exists i x,   (* current level reentry *)
          c1 = func_bdy (fname _ _ i) /\
          (l1 :: bstk) = proj1_sig (index_label _ _ i) /\
          reachable_param fc lf f pt R ((c1, Some (l1 :: bstk), st1) :: stk') i x /\
          invs i x st1)
      | None => exists i x,               (* current level tail *)
        reachable_param fc lf f pt R stk' i x /\ invs i x st1
      | _ => False
      end
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
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion') (c : com) (l1 : lbstk) (l2 : option lbstk) (st1 st0 : state'),

  (* Rule 2 *)
  (forall (invs' : FUN.rAssertion fc f),
    (invs' = fun j st =>
        exists z, invs {| fname := f; fvalid := in_eq f lf ; index_label := j|} z st) ->
  func_triple' fc f P Q invs' invs') ->

  get_bottom_com ((c, Some l1, st1) :: nil) = func_bdy f ->
  stk_to_pre fc lf f pt invs R ((c, Some l1, st1) :: nil) P Q ->
  middle_ceval' fc lf ((c, Some l1, st1) :: nil) ((c, l2, st0) :: nil) ->

  stk_to_pre fc lf f pt invs R ((c, l2, st0) :: nil) P Q.
Proof.
Admitted.

Lemma reentry_higher_level:
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion') (c : com) (l1 : lbstk) (l2 : option lbstk) (st1 st0 : state') p stk,

  (* Rule 1 *)
  (forall f' (Hin: In f' lf) (i: index_set fc (f :: lf)) (x: pt i) invs',
    (invs' = fun j st =>
        exists y, R i {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} x y 
        /\ invs {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st) ->
  func_triple' fc f' (invs i x) (invs i x) invs' invs') ->

  (forall (c0 : com) (l : option lbstk) (st : state') (p0 : com * option lbstk * state') (stk' stk'' : restk),
    (c, Some l1, st1) :: p :: stk = stk' ++ p0 :: stk'' ->
    In (c0, l, st) stk' -> exists f' : func, In f' lf /\ c0 = func_bdy f') ->
  stk_to_pre fc lf f pt invs R ((c, Some l1, st1) :: p :: stk) P Q ->
  middle_ceval' fc lf ((c, Some l1, st1) :: p :: stk) ((c, l2, st0) :: p :: stk) ->

  stk_to_pre fc lf f pt invs R ((c, l2, st0) :: p :: stk) P Q.
Proof.
Admitted.

Lemma multi_ceval'_ctop :
  forall fc lf stk1 c l st p0 p (stk' stk'' : restk),
    multi_ceval' fc lf (p0 :: nil) stk1 ->
    stk1 = stk' ++ p :: stk'' ->
    In (c, l, st) stk' ->
    exists f', In f' lf /\ c = (func_bdy f').
Proof.
Admitted.

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
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion'),

  (forall i x, globalp' (invs i x)) ->

  (* Rule 1 *)
  (forall f' (Hin: In f' lf) (i: index_set fc (f :: lf)) (x: pt i) invs',
    (invs' = fun j st =>
        exists y, R i {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} x y 
        /\ invs {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st) ->
  func_triple' fc f' (invs i x) (invs i x) invs' invs') ->

  (* Rule 2 *)
  (forall (invs' : FUN.rAssertion fc f),
    (invs' = fun j st =>
        exists z, invs {| fname := f; fvalid := in_eq f lf ; index_label := j|} z st) ->
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
  assert (stk_to_pre fc lf f pt invs R stk1 P Q).
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
          (* (destruct bstk;[
            simpl in *;
            destruct H3;[
              destruct H3;
              pose proof pure_no_point l1 H3;
              congruence |
              left; split;[
                apply com_to_label_pure_is_pure |
                destruct H3 as [_ [? [? [? [? [? ?]]]]]];
                subst; exists x, x0;
                split; [auto |
                eapply Ginv;
                exact H9]]] |
            assert (single_point l);[
              destruct p';
              destruct p;
              destruct o; inversion Hp'lbstk; subst;
              eapply multi_ceval'_left_bottom_single_point; [
              exact H6 |
              change ((c1, Some ((l :: bstk) ++ l1 :: nil), (sstk, glb)) :: nil) with (nil ++ (c1, Some ((l :: bstk) ++ l1 :: nil), (sstk, glb)) :: nil) in Hfront;
              exact Hfront]
            |
            simpl in *;
            destruct H3;[
              destruct H3;
              pose proof pure_no_point l H3;
              congruence |
              left; split;[
                apply com_to_label_pure_is_pure |
                destruct H3 as [_ [? [? [? [? [? ?]]]]]];
                subst; exists x, x0;
                split; [auto |
                eapply Ginv;
                exact H10]]]]]). *)
        + destruct bstk.
          {
            simpl in *.
            destruct H3.
            - destruct H3.
              pose proof pure_no_point l1 H3.
              congruence.
            - left; split.
              * apply com_to_label_pure_is_pure.
              * destruct H3 as [_ [? [? [? [? [? ?]]]]]].
                subst; exists x, x0.
                split; auto.
                eapply Ginv.
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
            - left; split.
              * apply com_to_label_pure_is_pure.
              * destruct H3 as [_ [? [? [? [? [? ?]]]]]].
                subst; exists x, x0.
                split; auto.
                eapply Ginv.
                exact H10.
          }
        + destruct bstk.
          {
            simpl in *.
            destruct H3.
            - destruct H3.
              pose proof pure_no_point l1 H3.
              congruence.
            - left; split.
              * apply com_to_label_pure_is_pure.
              * destruct H3 as [_ [? [? [? [? [? ?]]]]]].
                subst; exists x, x0.
                split; auto.
                eapply Ginv.
                exact H9.
          }
          {
            assert (single_point l).
            {
              destruct p'.
              destruct p0.
              destruct o; inversion Hp'lbstk; subst.
              eapply multi_ceval'_left_bottom_bottom_single_point.
              exact H6.
              change ((c1, Some ((l :: bstk) ++ l1 :: nil), (sstk, glb)) :: p :: stk) with (nil ++ (c1, Some ((l :: bstk) ++ l1 :: nil), (sstk, glb)) :: p :: stk) in Hfront.
              exact Hfront.
            }
            simpl in *.
            destruct H3.
            - destruct H3.
              pose proof pure_no_point l H3.
              congruence.
            - left; split.
              * apply com_to_label_pure_is_pure.
              * destruct H3 as [_ [? [? [? [? [? ?]]]]]].
                subst; exists x, x0.
                split; auto.
                eapply Ginv.
                exact H10.
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
      - destruct stk; (simpl;
        destruct H3 as [? [? [? ?]]];
        right; split; [assumption |
        exists x, x0;
        pose proof reachable_param_head _ _ _ _ _ _ _ _ _ H3;
        destruct H6; inversion H6; subst;
        repeat split;
        [eapply reachable_param_state; apply H3|
         eapply Ginv; exact H5]]).
      - apply Operators_Properties.clos_rtn1_rt.
        eapply rtn1_trans.
        exact H1.
        apply Operators_Properties.clos_rt_rtn1.
        exact Hfront.
    }

Admitted.



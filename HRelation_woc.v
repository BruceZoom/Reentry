Require Import Coq.Lists.List.
Require Import Omega.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Require Import DSRelation_woc.
Require Import Hoare.
Import HoareWithoutCall.
Import HoareLcWithoutCall.

(** Reachable Parameter *)
Inductive reachable_param (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (R : index_relation fc (f :: lf) pt) : restk -> forall (i : index_set fc (f :: lf)), (pt i) -> Prop :=
  | RP_single : forall st i x,
      fname _ _ i = f ->
      reachable_param fc lf f pt R ((func_bdy f, Some (proj1_sig (index_label _ _ i)), st) :: nil) i x
  | RP_multi : forall st1 st2 i j x y stk,
      In (fname _ _ j) lf ->
      R i j x y ->
      reachable_param fc lf f pt R ((func_bdy (fname _ _ i), Some (proj1_sig (index_label _ _ i)), st1) :: stk) i x ->
      reachable_param fc lf f pt R ((func_bdy (fname _ _ j), Some (proj1_sig (index_label _ _ j)), st2) :: (func_bdy (fname _ _ i), Some (proj1_sig (index_label _ _ i)), st1) :: stk) j y.
(** [] *)

(** Stack to Precondition *)
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
          c1 = func_bdy (fname _ _ i) /\
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
          c1 = func_bdy (fname _ _ i) /\
          l1 = proj1_sig (index_label _ _ i) /\
          reachable_param fc lf f pt R ((c1, Some l1, st1) :: stk') i x /\
          invs i x st1)
      | None => exists i x,               (* current level tail *)
        reachable_param fc lf f pt R stk' i x /\ invs i x st1
      end
    end
  end.
(** [] *)

(** Auxiliary Definitions and Lemmas *)
Fixpoint get_bottom_com (stk : restk) : com :=
  match stk with
  | nil => CSkip
  | (c, _, _) :: stk' =>
    match stk' with
    | nil => c
    | _ => get_bottom_com stk'
    end
  end.

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
(** [] *)

(** Part I: bottom reentry *)
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
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion) (c : com) (l1 : label) (l2 : option label) (st1 st0 : state),

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
  intros.
(*   rename H0 into Hctop. *)
  rename H0 into Hbt.
  rename H1 into Hstk.
  inversion H2; subst.
  - simpl in Hbt. subst c.
    (* Specialize rule 2 to use *)
    pose proof H (fun j st =>
    exists z, invs {| fname := f; fvalid := in_eq _ _ ; index_label := j|} z st) (eq_refl _).
    simpl in Hstk.
    destruct Hstk.
    (* From head to tail *)
    + destruct H1.
      (* Apply hoare rule, select PQ to use *)
      destruct H0 as [? _].
      eapply H0.
      (* Adjust ceval form *)
      rewrite (ceval'_pure_head _ _ _ _ _ _ H1 H4) in H4.
      (* Clear goals *)
      exact H4. exact H3.
    (* From middle to tail *)
    + destruct H1 as [? [? [? [? [? [? ?]]]]]]. subst.
      (* Utilize information in reachable_param *)
      remember ((func_bdy f, Some (proj1_sig (index_label fc (f :: lf) x)), st1) :: nil) as stk'.
      induction H6; subst; inversion Heqstk'.
      destruct i. simpl in *. subst.
      (* Apply hoare rule, select RQ to use *)
      destruct H0 as [_ [_ [? _]]].
      eapply H0.
      apply H4.
      replace (in_eq f lf) with fvalid0.
      exists x. exact H7.
      apply proof_irrelevance.
  - simpl in Hbt. subst.
    (* Specialize rule 2 to use *)
    pose proof H (fun j st =>
    exists z, invs {| fname := f; fvalid := in_eq _ _ ; index_label := j|} z st) (eq_refl _).
    destruct Hstk.
    (* From head to middle *)
    + destruct H1.
      right. split. assumption.
      (* Apply hoare rule to construct index and parameter, select PR to use *)
      destruct H0 as [_ [? _]].
      rewrite (ceval'_pure_head _ _ _ _ _ _ H1 H10) in H10.
      assert (valid_index_label fc (func_bdy f) l3).
      {
        split.
        exact H5.
        eapply ceval'_matched_tail.
        exact H10.
      }
      specialize (H0 _ _ (exist _ l3 H4) H10 H3).
      destruct H0.
      exists {|
        fname := f;
        fvalid := in_eq f lf;
        index_label := exist (valid_index_label fc (func_bdy f)) l3 H4 |}, x.
      simpl.
      (* Clear goals *)
      repeat split.
      * replace (Some l3) with (Some (proj1_sig (index_label _ _ {|
        fname := f; fvalid := in_eq f lf; index_label := exist (valid_index_label fc (func_bdy f)) l3 H4 |}))).
        apply RP_single. auto. auto.
      * exact H0.
    (* From middle to middle *)
    + destruct H1 as [? [? [? [? [? [? ?]]]]]]. subst.
      right. split. assumption.
      (* Utilize information in reachable_param *)
      remember ((func_bdy f, Some (proj1_sig (index_label fc (f :: lf) x)), st1) :: nil) as stk'.
      induction H6; subst; inversion Heqstk'.
      destruct i. simpl in *. subst.
      (* Prepare conditions *)
      assert (valid_index_label fc (func_bdy f) l3).
      {
        split.
        exact H5.
        eapply ceval'_matched_tail.
        exact H10.
      }
      replace l3 with (proj1_sig (exist _ l3 H4)) in H10; auto.
      assert (exists z : pt {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |},
    invs {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |} z st1).
      {
        replace (in_eq f lf) with fvalid0.
        exists x. auto.
        apply proof_irrelevance.
      }
      (* Apply hoare rule to construct index and parameter, select RR to use *)
      destruct H0 as [_ [_ [_ ?]]].
      specialize (H0 _ _ _ (exist _ l3 H4) H10 H6); clear H6.
      destruct H0.
      exists {| fname := f; fvalid := in_eq f lf; index_label := exist (valid_index_label fc (func_bdy f)) l3 H4 |}, x0.
      (* Clear goals *)
      repeat split.
      replace (Some l3) with (Some (proj1_sig (index_label _ _ {| fname := f; fvalid := in_eq f lf; index_label := exist (valid_index_label fc (func_bdy f)) l3 H4 |}))).
      apply RP_single. auto. auto. assumption.
Qed.
(** [] *)

(** Part II: nested reentry *)
Lemma reentry_higher_level:
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion) (c : com) (l1 : label) (l2 : option label) (st1 st0 : state) p stk,

  (* Rule 1 *)
  (forall f' (Hin: In f' lf) (i: index_set fc (f :: lf)) (x: pt i) invs',
    (invs' = fun j st =>
        exists y, R i {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} x y 
        /\ invs {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st) ->
  func_triple' fc f' (invs i x) (invs i x) invs' invs') ->

  (forall (c0 : com) (l : option label) (st : state) (p0 : com * option label * state) (stk' stk'' : list (com * option label * state)),
    (c, Some l1, st1) :: p :: stk = stk' ++ p0 :: stk'' ->
    In (c0, l, st) stk' -> exists f' : func, In f' lf /\ c0 = func_bdy f') ->
  stk_to_pre fc lf f pt invs R ((c, Some l1, st1) :: p :: stk) P Q ->
  middle_ceval' fc lf ((c, Some l1, st1) :: p :: stk) ((c, l2, st0) :: p :: stk) ->

  stk_to_pre fc lf f pt invs R ((c, l2, st0) :: p :: stk) P Q.
Proof.
  intros.
  rename H0 into Hctop.
  rename H1 into Hstk.
  inversion H2; subst.
  (* Transition in higher level, from some point to the end *)
  - simpl in Hstk.
    destruct Hstk.
    (* From head to tail *)
    + destruct H0 as [? [? [? [? ?]]]].
      pose proof Hctop c (Some l1) st1 p ((c, Some l1, st1)::nil) stk (eq_refl _) (in_eq _ _) as [f' [? ?]]. subst.
      (* Construct index and parameter *)
      exists x, x0.
      split. auto.
      (* Apply hoare rule, select PQ to use *)
      pose proof H f' H5 x x0
        (fun (j : FUN.index_label_set fc f') (st : state) =>
          exists y : pt {| fname := f'; fvalid := in_cons f f' lf H5; index_label := j |}, R x {| fname := f'; fvalid := in_cons f f' lf H5; index_label := j |} x0 y /\ invs {| fname := f'; fvalid := in_cons f f' lf H5; index_label := j |} y st) (eq_refl _) as [? _].
      eapply H6.
      rewrite (ceval'_pure_head _ _ _ _ _ _ H0 H4) in H4.
      exact H4. exact H3.
    (* From middle to tail *)
    + destruct H0 as [? [? [? [? [? [? ?]]]]]]. subst c.
      (* Utilize information in reachable_param *)
      remember ((func_bdy (fname fc (f :: lf) x), Some l1, st1) :: p :: stk) as stk'.
      induction H5; subst; inversion Heqstk'; subst.
      clear IHreachable_param.
      (* Construct index and parameter *)
      exists i, x.
      split. assumption.
      (* Apply hoare rule, select RQ to use *)
      pose proof H (fname fc (f :: lf) j) H1 i x (fun (j0 : FUN.index_label_set fc (fname fc (f :: lf) j)) (st : state) =>
exists y : pt {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := j0 |},
  R i {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := j0 |} x y /\
  invs {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := j0 |} y st) (eq_refl _) as [_ [_ [? _]]].
      eapply H3; clear H3.
      apply H4.
      replace {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := index_label fc (f :: lf) j |} with j.
      exists y. tauto.
      destruct j. f_equal.
      apply proof_irrelevance.
  (* Transition within higher level, from some point to one reentry point *)
  - destruct Hstk.
    (* From head to middle *)
    + right. split. assumption.
      destruct H0 as [? [? [? [? ?]]]].
      pose proof Hctop c (Some l1) st1 p ((c, Some l1, st1)::nil) stk (eq_refl _) (in_eq _ _) as [f' [? ?]]. subst.
      (* Prepare conditions *)
      rewrite (ceval'_pure_head _ _ _ _ _ _ H0 H10) in H10.
      assert (valid_index_label fc (func_bdy f') l3).
      {
        split. assumption. eapply ceval'_matched_tail.
        apply H10.
      }
      (* Apply hoare rule to construct index and parameter, select PR to use *)
      pose proof H f' H4 x x0 (fun (j : FUN.index_label_set fc f') (st : state) =>
        exists y : pt {| fname := f'; fvalid := in_cons f f' lf H4; index_label := j |},
          R x {| fname := f'; fvalid := in_cons f f' lf H4; index_label := j |} x0 y /\
          invs {| fname := f'; fvalid := in_cons f f' lf H4; index_label := j |} y st) (eq_refl _) as [_ [? _]].
      specialize (H7 _ _ (exist _ l3 H6) H10 H3).
      destruct H7 as [y [? ?]].
      exists {| fname := f'; fvalid := in_cons f f' lf H4; index_label := exist (valid_index_label fc (func_bdy f')) l3 H6 |}, y.
      (* Clear goals *)
      repeat split.
      replace ((func_bdy f'), Some l3, st0) with ((func_bdy (fname _ _ {| fname := f'; fvalid := in_cons f f' lf H4; index_label := exist (valid_index_label fc (func_bdy f')) l3 H6 |})),Some (proj1_sig (index_label _ _ {| fname := f'; fvalid := in_cons f f' lf H4; index_label := exist (valid_index_label fc (func_bdy f')) l3 H6 |})), st0); auto.
      pose proof reachable_param_head _ _ _ _ _ _ _ _ _ H1 as [st ?]; subst.
      eapply RP_multi; auto.
      exact H7. assumption. assumption.
    (* From middle to middle *)
    + right. split. assumption.
      destruct H0 as [? [? [? [? [? [? ?]]]]]]; subst.
      (* Utilize information in reachable_param *)
      remember ((func_bdy (fname fc (f :: lf) x), Some (proj1_sig (index_label fc (f :: lf) x)), st1) :: p :: stk) as stk'.
      induction H4; inversion Heqstk'; subst.
      clear IHreachable_param.
      (* Prepare conditions *)
      assert (valid_index_label fc (func_bdy (fname fc (f :: lf) j)) l3).
      { split. assumption. eapply ceval'_matched_tail. apply H10. }
      assert (exists y : pt {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := index_label fc (f :: lf) j |},
   R i {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := index_label fc (f :: lf) j |} x y /\
   invs {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := index_label fc (f :: lf) j |} y st1).
      {
        replace {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := index_label fc (f :: lf) j |} with j.
        exists y. tauto.
        destruct j. simpl.
        replace (in_cons f fname0 lf H1) with fvalid0.
        auto. apply proof_irrelevance.
      }
      (* Apply hoare rule to construct index and parameter, select RR to use *)
      pose proof H (fname fc (f :: lf) j) H1 i x (fun (j0 : FUN.index_label_set fc (fname fc (f :: lf) j)) (st : state) =>
 exists y : pt {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := j0 |},
   R i {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := j0 |} x y /\
   invs {| fname := fname fc (f :: lf) j; fvalid := in_cons f (fname fc (f :: lf) j) lf H1; index_label := j0 |} y st) (eq_refl _) as [_ [_ [_ ?]]].
      specialize (H9 _ _ _ (exist _ l3 H7) H10 H8); clear H8.
      destruct H9 as [? [? ?]].
      exists {|
       fname := fname fc (f :: lf) j;
       fvalid := in_cons f (fname fc (f :: lf) j) lf H1;
       index_label := exist (valid_index_label fc (func_bdy (fname fc (f :: lf) j))) l3 H7 |}, x0.
      (* Clear goals *)
      repeat split.
      remember {|
       fname := fname fc (f :: lf) j;
       fvalid := in_cons f (fname fc (f :: lf) j) lf H1;
       index_label := exist (valid_index_label fc (func_bdy (fname fc (f :: lf) j))) l3 H7 |} as k.
      replace (func_bdy (fname fc (f :: lf) j), Some l3, st0) with (func_bdy (fname fc (f :: lf) k), Some (proj1_sig (index_label _ _ k)), st0); [|subst; auto].
      eapply RP_multi.
      subst. simpl. assumption.
      exact H8. assumption. assumption.
  - pose proof eq_refl (length stk).
    rewrite <- H12 in H0 at 1.
    simpl in H0. omega.
Qed.
(** [] *)

(** Main Theorem: derivation rule *)
Theorem reentry_invariant :
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion),

  (forall i x, globalp (invs i x)) ->

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

  func_triple fc lf P f Q.
Proof.
  intros.
  rename H into Ginv.
  rename H0 into H.
  rename H1 into H0.
  unfold func_triple.
  intros.
  apply ceval_multi_ceval' in H1.

  remember ((func_bdy f, Some (com_to_label_pure (func_bdy f)), st1) :: nil) as stk1.
  (* Generalized precondition *)
  assert (stk_to_pre fc lf f pt invs R stk1 P Q).
  {
    subst. simpl.
    left.
    split.
    apply com_to_label_pure_is_pure.
    exact H2.
  }
  (* All non-bottom com have a corresponding f' in lf *)
  (* This condition CANNOT be removed! It is used in 2 cases where stk_to_pre condition describe the transition from a lower level to the head of upper level, where reachable_param does not provide any information about the upper level. *)
  assert (forall c l st p stk' stk'',
            stk1 = stk' ++ p :: stk'' ->
            In (c, l, st) stk' ->
            exists f', In f' lf /\ c = (func_bdy f')) as Hctop.
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
  remember ((func_bdy f, None, st2) :: nil) as stk2.
(*   revert dependent f. *)
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
          exact Hctop. assumption. assumption.
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
      - destruct stk.
        (* Transition with in bottom level, from some point to one reentry point *)
        * eapply reentry_bottom_level; try assumption.
          exact H3. assumption.
        (* Transition within higher level, from some point to one reentry point *)
        * eapply reentry_higher_level; try assumption.
          exact Hctop. assumption. assumption.
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
      (* Transition from lower level to upper level *)
      - destruct stk; (simpl; destruct H3;
        [destruct H3; pose proof pure_no_point l1 H3; congruence |
         left; split;
         [apply com_to_label_pure_is_pure |
         destruct H3 as [_ [? [? [? [? [? ?]]]]]];
         subst; exists x, x0;
         split; [assumption | eapply Ginv; exact H8]]]).
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
(** [] *)

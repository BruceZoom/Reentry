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
  com_to_label_pure (func_bdy f).

Definition bottom (fc : func_context) (f : func) : label :=
  com_to_label_pure (func_bdy f).

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

Definition stk_to_pre (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs loc_R : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (stk : restk) (P Q : Assertion) : Prop :=
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
          f = fname _ _ i /\ invs i x st1 /\ loc_R i x st1)
      | None => Q st1                     (* bottom level tail *)
      end
    | (c2, Some l2, st2) :: stk'' =>      (* during reentry *)
      exists j y,
        stk_loc_R fc lf f pt loc_R R stk'' j y /\
        c2 = func_bdy (fname _ _ j) /\
        l2 = proj1_sig (index_label _ _ j) /\
        loc_R j y st2 /\
        match l1 with
        | Some l1 =>
          (is_pure l1 /\ invs j y st1) \/   (* current level head *)
          (single_point l1 /\ exists i x,   (* current level reentry *)
            c1 = func_bdy (fname _ _ i) /\
            l1 = proj1_sig (index_label _ _ i) /\
            In (fname _ _ i) lf /\ R j i y x /\
            invs i x st1 /\ loc_R i x st1)
        | None => invs j y st1              (* current level tail *)
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
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs loc_R : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion) (c : com) (l1 : label) (l2 : option label) (st1 st0 : state),

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
    (* Specialize rule 2 to use *)
    pose proof H (fun (j : COM.index_label_set fc (func_bdy f)) (st : state) =>
      exists z : pt {| fname := f; fvalid := in_eq f lf; index_label := j |},
        invs {| fname := f; fvalid := in_eq f lf; index_label := j |} z st /\
        loc_R {| fname := f; fvalid := in_eq f lf; index_label := j |} z st) (eq_refl _).
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
    + destruct H1 as [? [i [x [? [? [? [? ?]]]]]]]. subst.
      destruct i. simpl in *. subst.
      eapply H0.
      apply H4.
      replace (in_eq fname0 lf) with fvalid0.
      exists x. tauto.
      apply proof_irrelevance.
  - simpl in Hbt. subst.
    (* Specialize rule 2 to use *)
    pose proof H (fun j st =>
    exists z, invs {| fname := f; fvalid := in_eq _ _ ; index_label := j|} z st /\ loc_R {| fname := f; fvalid := in_eq f lf; index_label := j |} z st) (eq_refl _).
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
      destruct H0 as [? [? ?]].
      exists {|
        fname := f;
        fvalid := in_eq f lf;
        index_label := exist (valid_index_label fc (func_bdy f)) l3 H4 |}, x.
      simpl.
      (* Clear goals *)
      repeat split; auto.
    (* From middle to middle *)
    + destruct H1 as [? [i [x [? [? [? [? ?]]]]]]]. subst.
      right; split; auto.
      destruct i. simpl in *. subst fname0.
      (* Prepare conditions *)
      assert (valid_index_label fc (func_bdy f) l3).
      {
        split.
        exact H5.
        eapply ceval'_matched_tail.
        exact H10.
      }
      replace l3 with (proj1_sig (exist _ l3 H4)) in H10; auto.
      assert (exists z : pt {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |}, invs {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |} z st1 /\ loc_R {| fname := f; fvalid := in_eq f lf; index_label := index_label0 |} z st1).
      {
        replace (in_eq f lf) with fvalid0.
        exists x. auto.
        apply proof_irrelevance.
      }
      (* Apply hoare rule to construct index and parameter, select RR to use *)
      destruct H0 as [_ [_ [_ ?]]].
      specialize (H0 _ _ _ (exist _ l3 H4) H10 H6); clear H6.
      destruct H0 as [? [? ?]].
      exists {| fname := f; fvalid := in_eq f lf; index_label := exist (valid_index_label fc (func_bdy f)) l3 H4 |}, x0.
      (* Clear goals *)
      repeat split; auto.
Qed.

Lemma reentry_higher_level:
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs loc_R : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion) (c : com) (l1 : label) (l2 : option label) (st1 st0 : state) p stk,

  (* Rule 1 *)
  (forall f' (Hin: In f' lf) (i: index_set fc (f :: lf)) (x: pt i) invs',
    (invs' = fun j st =>
        exists y, R i {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} x y 
        /\ invs {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st /\ loc_R {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st) ->
  func_triple' fc f' (invs i x) (invs i x) invs' invs') ->

  (forall (c0 : com) (l : option label) (st : state) (p0 : com * option label * state) (stk' stk'' : list (com * option label * state)),
    (c, Some l1, st1) :: p :: stk = stk' ++ p0 :: stk'' ->
    In (c0, l, st) stk' -> exists f' : func, In f' lf /\ c0 = func_bdy f') ->
  stk_to_pre fc lf f pt invs loc_R R ((c, Some l1, st1) :: p :: stk) P Q ->
  middle_ceval' fc lf ((c, Some l1, st1) :: p :: stk) ((c, l2, st0) :: p :: stk) ->

  stk_to_pre fc lf f pt invs loc_R R ((c, l2, st0) :: p :: stk) P Q.
Proof.
  intros.
  rename H0 into Hctop.
  rename H1 into Hstk.
  inversion H2; subst.
  (* Transition in higher level, from some point to the end *)
  - destruct p as [[cp lp] stp].
    simpl in Hstk.
    destruct lp; [| inversion Hstk].
    rename l into lp.
    destruct Hstk as [j [y [? [? [? [? ?]]]]]].
    destruct H6.
    (* From head to tail *)
    + destruct H6.
      simpl.
      exists j, y.
      repeat split; auto.
      pose proof Hctop c (Some l1) st1 (cp, Some lp, stp) ((c, Some l1, st1)::nil) stk (eq_refl _) (in_eq _ _) as [f' [? ?]]. subst.
      pose proof H f' H8 j y
          (fun (j0 : FUN.index_label_set fc f') (st : state) =>
      exists y0 : pt {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |},
        R j {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |} y y0 /\
        invs {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |} y0 st /\
        loc_R {| fname := f'; fvalid := in_cons f f' lf H8; index_label := j0 |} y0 st) (eq_refl _) as [? _].
      eapply H1.
      rewrite (ceval'_pure_head _ _ _ _ _ _ H6 H4) in H4.
      exact H4. tauto.
    (* From middle to tail *)
    + destruct H6 as [? [i [x [? [? [? [? [? ?]]]]]]]].
      simpl.
      exists j, y.
      repeat split; auto.
      pose proof H (fname fc (f :: lf) i) H9 j y (fun (j0 : FUN.index_label_set fc (fname fc (f :: lf) i)) (st : state) =>
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
      eapply H13; clear H13.
      * subst.
        apply H4.
      * replace ({|
         fname := fname fc (f :: lf) i;
         fvalid := in_cons f (fname fc (f :: lf) i) lf H9;
         index_label := index_label fc (f :: lf) i |}) with i.
        2:{
          destruct i. simpl.
          assert (fvalid0 = in_cons f fname0 lf H9).
          apply proof_irrelevance.
          rewrite H13. auto.
        }
        exists x.
        tauto.
  (* Transition within higher level, from some point to one reentry point *)
  - destruct p as [[cp lp] stp].
    destruct lp; [| inversion Hstk].
    rename l into lp.
    simpl in Hstk.
    destruct Hstk as [j [y [? [? [? [H_loc' ?]]]]]].
    destruct H4.
    (* From head to middle *)
    + destruct H4.
      exists j, y.
      repeat split; auto.
      right; split; auto.
      pose proof Hctop c (Some l1) st1 (cp, Some lp, stp) ((c, Some l1, st1)::nil) stk (eq_refl _) (in_eq _ _) as [f' [? ?]]. subst.
      rewrite (ceval'_pure_head _ _ _ _ _ _ H4 H10) in H10.
      assert (valid_index_label fc (func_bdy f') l3).
      {
        split. assumption. eapply ceval'_matched_tail.
        apply H10.
      }
      pose proof H f' H7 j y (fun (j0 : FUN.index_label_set fc f') (st : state) =>
      exists y0 : pt {| fname := f'; fvalid := in_cons f f' lf H7; index_label := j0 |},
        R j {| fname := f'; fvalid := in_cons f f' lf H7; index_label := j0 |} y y0 /\
        invs {| fname := f'; fvalid := in_cons f f' lf H7; index_label := j0 |} y0 st /\
        loc_R {| fname := f'; fvalid := in_cons f f' lf H7; index_label := j0 |} y0 st) (eq_refl _) as [_ [? _]].
      specialize (H3 _ _ (exist _ l3 H1) H10 H6) as [x [? [? ?]]].
      exists {|
      fname := f';
      fvalid := in_cons f f' lf H7;
      index_label := exist (valid_index_label fc (func_bdy f')) l3 H1 |}, x.
      simpl.
      repeat split; auto.
    (* From middle to middle *)
    + destruct H4 as [? [i [x [? [? [? [? [? ?]]]]]]]].
      subst.
      exists j, y.
      repeat split; auto.
      right; split; auto.
      remember ((func_bdy (fname fc (f :: lf) j),
           Some (proj1_sig (index_label fc (f :: lf) j)), stp) :: stk) as stk'.
      pose proof H (fname fc (f :: lf) i) H8 j y (fun (j0 : FUN.index_label_set fc (fname fc (f :: lf) i)) (st : state) =>
      exists
        y0 : pt
               {|
               fname := fname fc (f :: lf) i;
               fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
               index_label := j0 |},
        R j
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
          index_label := j0 |} y y0 /\
        invs
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
          index_label := j0 |} y0 st /\
        loc_R
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
          index_label := j0 |} y0 st) (eq_refl _) as [_ [_ [_ ?]]].
      unfold triple_RR in H1.
      assert (valid_index_label fc (func_bdy (fname fc (f :: lf) i)) l3).
      { split. assumption. eapply ceval'_matched_tail. apply H10. }
      assert (exists
        y0 : pt
               {|
               fname := fname fc (f :: lf) i;
               fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
               index_label := index_label fc (f :: lf) i |},
        R j
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
          index_label := index_label fc (f :: lf) i |} y y0 /\
        invs
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
          index_label := index_label fc (f :: lf) i |} y0 st1 /\
        loc_R
          {|
          fname := fname fc (f :: lf) i;
          fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
          index_label := index_label fc (f :: lf) i |} y0 st1).
      {
        replace {|
         fname := fname fc (f :: lf) i;
         fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
         index_label := index_label fc (f :: lf) i |} with i.
         2:{ destruct i. simpl. assert (fvalid0 = in_cons f fname0 lf H8).
         apply proof_irrelevance. rewrite H6; auto. }
         exists x. tauto.
      }
      specialize (H1 _ _ _ (exist _ l3 H3) H10 H6) as [y0 [? [? ?]]]; clear H6.
      exists {|
       fname := fname fc (f :: lf) i;
       fvalid := in_cons f (fname fc (f :: lf) i) lf H8;
       index_label := exist (valid_index_label fc (func_bdy (fname fc (f :: lf) i))) l3 H3 |}, y0.
       repeat split; auto.
  - pose proof eq_refl (length stk).
    rewrite <- H12 in H0 at 1.
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
        pose proof IHclos_refl_trans_n1 c (Some l1) st1 p ((c, Some l1, st1) :: stk') stk'' eq_refl (in_eq _ _).
        exact H2.
      * inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c l st p ((c0, Some l1, st1) :: stk') stk'' eq_refl (in_cons _ _ _ H2).
        exact H3.
    + destruct stk'; [inversion H2 |].
      destruct H2.
      * inversion H2; subst.
        inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c (Some l1) st1 p ((c, Some l1, st1) :: stk') stk'' eq_refl (in_eq _ _).
        exact H2.
      * inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c l st p ((c0, Some l1, st1) :: stk') stk'' eq_refl (in_cons _ _ _ H2).
        exact H4.
    + remember ((c1, Some l1, (loc1, glb)) :: stk) as stk'''.
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
        pose proof IHclos_refl_trans_n1 c (Some l2) (loc2, glb2) p ((c1, None, (loc1, glb1)) :: (c, Some l2, (loc2, glb2)) :: stk') stk'' (eq_refl _) (in_cons _ _ _ (in_eq _ _)).
        exact H2.
      * inversion H1; subst.
        pose proof IHclos_refl_trans_n1 c l st p ((c1, None, (loc1, glb1)) :: (c2, Some l2, (loc2, glb2)) :: stk') stk'' (eq_refl _) (in_cons _ _ _ (in_cons _ _ _ H2)).
        exact H3.
Qed.

Theorem reentry_invariant :
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs loc_R : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion),

  (forall i x, globalp (invs i x) /\ localp (loc_R i x)) ->

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
  assert (stk_to_pre fc lf f pt invs loc_R R stk1 P Q).
  {
    subst. simpl.
    left.
    split.
    apply com_to_label_pure_is_pure.
    exact H2.
  }
  remember (func_bdy f, Some (com_to_label_pure (func_bdy f)), st1) as p'.
  assert (multi_ceval' fc lf (p' :: nil) stk1) as Hfront.
  {
    subst.
    apply rt_refl.
  }
  clear dependent st1.
  clear Heqstk1.

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
      - destruct stk; simpl.
        + destruct H3.
          * destruct H3; pose proof pure_no_point l1 H3; congruence.
          * destruct H3 as [_ [i [x [? [? [? [? ?]]]]]]].
            exists i, x.
            repeat split; auto.
            left; split; [apply com_to_label_pure_is_pure |].
            eapply Ginv; apply H8.
        + destruct p as [[cp lp] stp].
          destruct lp; [| inversion H3].
          destruct H3 as [i [x [? [? [? [? ?]]]]]].
          destruct H9; [destruct H9; pose proof pure_no_point l1 H9; congruence |].
          destruct H9 as [_ [j [y [? [? [? [? [? ?]]]]]]]].
          exists j, y.
          repeat split; auto.
          * exists i, x.
            repeat split; auto.
          * left; split; [apply com_to_label_pure_is_pure |].
            eapply Ginv.
            apply H13.
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
        destruct H3 as [j [y [? [? [? [? ?]]]]]].
        destruct stk; simpl.
        + right; split; auto.
          exists j, y.
          repeat split; auto.
          * eapply Ginv. apply H8.
          * eapply Ginv. apply H7.
        + destruct p as [[cp lp] stp].
          destruct lp; [| inversion H3].
          simpl in H3.
          destruct H3 as [? [j0 [y0 [? [? [? [? ?]]]]]]].
          exists j0, y0.
          repeat split; auto.
          right; split; auto.
          exists j, y.
          repeat split; auto.
          * eapply Ginv; apply H8.
          * eapply Ginv; apply H7.
          * congruence.
      - apply Operators_Properties.clos_rtn1_rt.
        eapply rtn1_trans.
        exact H1.
        apply Operators_Properties.clos_rt_rtn1.
        exact Hfront.
    }
Qed.

Print Assumptions reentry_invariant.

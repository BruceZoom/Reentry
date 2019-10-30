Require Import Coq.Lists.List.
Require Import AST_wc.
Require Import Omega.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.


(** Definitions about label *)
Inductive label : Type :=
  | LHere
  | LPure
  | LSeq (l1 : label) (l2 : label)
  | LIf (b : bexp) (l1 : label) (l2 : label)
  | LWhile (b : bexp) (l : label)
.

Inductive is_pure : label -> Prop :=
  | IP_Pure : is_pure LPure
  | IP_Seq : forall l1 l2,
      is_pure l1 ->
      is_pure l2 ->
      is_pure (LSeq l1 l2)
  | IP_If : forall l1 l2 b,
      is_pure l1 ->
      is_pure l2 ->
      is_pure (LIf b l1 l2)
  | IP_While : forall l b,
      is_pure l ->
      is_pure (LWhile b l)
.

Inductive single_point : label -> Prop :=
  | SP_Here : single_point LHere
  | SP_Seq1 : forall l1 l2,
      single_point l1 ->
      is_pure l2 ->
      single_point (LSeq l1 l2)
  | SP_Seq2 : forall l1 l2,
      is_pure l1 ->
      single_point l2 ->
      single_point (LSeq l1 l2)
  | SP_If1 : forall l1 l2 b,
      single_point l1 ->
      is_pure l2 ->
      single_point (LIf b l1 l2)
  | SP_If2 : forall l1 l2 b,
      is_pure l1 ->
      single_point l2 ->
      single_point (LIf b l1 l2)
  | SP_While : forall l b,
      single_point l ->
      single_point (LWhile b l)
.

Definition valid_label (l : label) : Prop := is_pure l \/ single_point l.

Fixpoint com_to_label_pure (c : com) : label :=
  match c with
  | CSeq c1 c2 => LSeq (com_to_label_pure c1) (com_to_label_pure c2)
  | CIf b c1 c2 => LIf b (com_to_label_pure c1) (com_to_label_pure c2)
  | CWhile b c => LWhile b (com_to_label_pure c)
  | _ => LPure
  end.

Lemma com_to_label_pure_is_pure : forall c,
  is_pure (com_to_label_pure c).
Proof.
  intros.
  induction c.
  - simpl. apply IP_Pure.
  - simpl. apply IP_Pure.
  - simpl. apply IP_Seq; assumption.
  - simpl. apply IP_If; assumption.
  - simpl. apply IP_While; assumption.
  - simpl. apply IP_Pure.
  - simpl. apply IP_Pure.
Qed.

Lemma com_to_label_pure_valid : forall c,
  valid_label (com_to_label_pure c).
Proof.
  intros.
  unfold valid_label.
  left.
  apply com_to_label_pure_is_pure.
Qed.

Lemma pure_no_point : forall c,
  is_pure c ->
  ~single_point c.
Proof.
  unfold not.
  intros.
  induction H.
  - inversion H0.
  - inversion H0.
    apply (IHis_pure1 H4).
    apply (IHis_pure2 H5).
  - inversion H0.
    apply (IHis_pure1 H4).
    apply (IHis_pure2 H6).
  - inversion H0.
    apply (IHis_pure H2).
Qed.

Lemma com_to_label_pure_no_point : forall c,
  ~single_point (com_to_label_pure c).
Proof.
  intros.
  apply pure_no_point.
  apply com_to_label_pure_is_pure.
Qed.
(** [] *)

(** Length Support? *)
Lemma length_nil_app_cons {A : Type} : forall l a,
  @nil A = l ++ a :: nil -> False.
Proof.
  intros.
  pose proof eq_refl (length (@nil A)).
  rewrite H in H0 at 1.
  rewrite app_length in H0.
  simpl in H0. omega.
Qed.
Ltac auto_len :=
  auto; try (rewrite app_length; auto).
Ltac app_len_inv H :=
  rewrite app_length in H; simpl in H; omega.
Ltac app_cons_nil H :=
  try (apply eq_sym in H;
  pose proof length_nil_app_cons _ _ H as Happ_cons_nil;
  inversion Happ_cons_nil; tauto);
  try (pose proof length_nil_app_cons _ _ H as Happ_cons_nil;
  inversion Happ_cons_nil; tauto).
Ltac destruct_rev stk :=
  remember (rev stk) as dr_stk' eqn: Heqdr_stk';
  destruct dr_stk';
  pose proof rev_involutive stk as dr_H;
  rewrite <- Heqdr_stk' in dr_H; subst;
  try (remember (rev dr_stk') as stk;
  clear dependent dr_stk').
(** [] *)


(** Definition of basic ceval' *)
(* Calling stacks are ordered top-down, i.e. inner call state at stack top *)
(* label calling stack *)
Definition lbstk : Type := list label.
(* local calling stack *)
Definition lcstk : Type := list unit_state.
Definition state' : Type := lcstk (* local *) * unit_state (* global *).

Definition pure_stk (bstk : lbstk) : Prop :=
  forall lb, In lb bstk -> is_pure lb.

Inductive ceval' : func_context -> com -> lbstk -> lbstk -> state' -> state' -> Prop :=
  | E'_Skip : forall fc loc glb,
      ceval' fc CSkip (LPure :: nil) (LPure :: nil) (loc :: nil, glb) (loc :: nil, glb)
  | E'_Ass : forall fc X a n loc1 loc2 glb1 glb2,
      aeval (loc1, glb1) a = n ->
      update_state (loc1, glb1) X n = (loc2, glb2) ->
      ceval' fc (CAss X a) (LPure :: nil) (LPure :: nil) (loc1 :: nil, glb1) (loc2 :: nil, glb2)

  | E'_Reentry1c : forall fc loc glb,
      ceval' fc CReentry (LPure :: nil) (LHere :: nil) (loc :: nil, glb) (loc :: nil, glb)
  | E'_Reentryr2 : forall fc loc glb,
      ceval' fc CReentry (LHere :: nil) (LPure :: nil) (loc :: nil, glb) (loc :: nil, glb)

  | E'_CallOut : forall fc f pv l2 loc1 loc2 glb1 glb2 bstk sstk,
      single_point l2 ->
      length bstk = length sstk ->
      ceval' fc (func_bdy f)
        (com_to_label_pure (func_bdy f) :: nil) (bstk ++ l2 :: nil)
        (param_to_local_state (loc1, glb1) (func_arg f) pv :: nil, glb1)
        (sstk ++ loc2 :: nil, glb2) ->
(** Might be equivalent to
        ((l2, loc2) :: stk) glb1 glb2 -> *)
      ceval' fc (CCall f pv)
        (LPure :: nil) (LHere :: bstk ++ l2 :: nil)
        (loc1 :: nil, glb1) (loc1 :: sstk ++ loc2 :: nil, glb2)
(** Might be equivalent to
        ((LPure, loc) :: nil) ((LHere, loc) :: (l2, loc2) :: stk) glb1 glb2 *)
  | E'_CallRet : forall fc f pv l1 loc loc1 loc2 glb1 glb2 bstk sstk,
      single_point l1 ->
      length bstk = length sstk ->
      ceval' fc (func_bdy f)
        (bstk ++ l1 :: nil) ((com_to_label_pure (func_bdy f)) :: nil)
        (sstk ++ loc1 :: nil, glb1) (loc2 :: nil, glb2) ->
      ceval' fc (CCall f pv)
        (LHere :: bstk ++ l1 :: nil) (LPure :: nil)
        (loc :: sstk ++ loc1 :: nil, glb1) (loc :: nil, glb2)
  | E'_CallSeg : forall fc f pv l1 l2 loc glb1 glb2 bstk1 bstk2 sstk1 sstk2,
      single_point l1 ->
      single_point l2 ->
      1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 ->
      ceval' fc (func_bdy f)
        (bstk1 ++ l1 :: nil) (bstk2 ++ l2 :: nil)
        (sstk1, glb1) (sstk2, glb2) ->
      ceval' fc (CCall f pv)
        (LHere :: bstk1 ++ l1 :: nil) (LHere :: bstk2 ++ l2 :: nil)
        (loc :: sstk1, glb1) (loc :: sstk2, glb2)
  | E'_CallPure : forall fc f pv loc loc2 glb1 glb2,
      ceval' fc (func_bdy f)
        ((com_to_label_pure (func_bdy f)) :: nil) ((com_to_label_pure (func_bdy f)) :: nil)
        ((param_to_local_state (loc, glb1) (func_arg f) pv) :: nil, glb1) (loc2 :: nil, glb2) ->
      ceval' fc (CCall f pv)
        (LPure :: nil) (LPure :: nil)
        (loc :: nil, glb1) (loc :: nil, glb2)

  | E'_Seq : forall fc c1 c2 l1 l2 l3 l4 st bstk1 bstk2 st1 st2,
      valid_label l1 ->
      is_pure l2 ->
      is_pure l3 ->
      valid_label l4 ->
(*       1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 -> *)
      ceval' fc c1
        (l1 :: bstk1) (l2 :: nil)
        st1 st ->
      ceval' fc c2
        (l3 :: nil) (l4 :: bstk2)
        st st2 ->
      ceval' fc (CSeq c1 c2)
        ((LSeq l1 l3) :: bstk1) ((LSeq l2 l4) :: bstk2) st1 st2
  | E'_Seq1 : forall fc c1 c2 l1 l2 bstk1 bstk2 st1 st2,
      valid_label l1 ->
      single_point l2 ->
(*       1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 -> *)
      ceval' fc c1
        (l1 :: bstk1) (l2 :: bstk2)
        st1 st2 ->
      ceval' fc (CSeq c1 c2)
        ((LSeq l1 (com_to_label_pure c2)) :: bstk1)
        ((LSeq l2 (com_to_label_pure c2)) :: bstk2) st1 st2
  | E'_Seq2 : forall fc c1 c2 l1 l2 bstk1 bstk2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
(*       1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 -> *)
      ceval' fc c2
        (l1 :: bstk1) (l2 :: bstk2)
        st1 st2 ->
      ceval' fc (CSeq c1 c2)
        ((LSeq (com_to_label_pure c1) l1) :: bstk1)
        ((LSeq (com_to_label_pure c1) l2) :: bstk2) st1 st2

  | E'_IfTrue : forall fc b c1 c2 l1 l2 loc1 glb1 st2 bstk,
      is_pure l1 ->
      valid_label l2 ->
(*       1 + length bstk = length sstk -> *)
      beval (loc1, glb1) b = true ->
      ceval' fc c1
        (l1 :: nil) (l2 :: bstk)
        (loc1 :: nil, glb1) st2 ->
      ceval' fc (CIf b c1 c2)
        ((LIf b l1 (com_to_label_pure c2)) :: nil)
        ((LIf b l2 (com_to_label_pure c2)) :: bstk)
        (loc1 :: nil, glb1) st2
  | E'_IfFalse : forall fc b c1 c2 l1 l2 loc1 glb1 st2 bstk,
      is_pure l1 ->
      valid_label l2 ->
(*       1 + length bstk = length sstk -> *)
      beval (loc1, glb1) b = false ->
      ceval' fc c2
        (l1 :: nil) (l2 :: bstk)
        (loc1 :: nil, glb1) st2 ->
      ceval' fc (CIf b c1 c2)
        ((LIf b (com_to_label_pure c1) l1) :: nil)
        ((LIf b (com_to_label_pure c1) l2) :: bstk)
        (loc1 :: nil, glb1) st2
  | E'_If1 : forall fc b c1 c2 l1 l2 bstk1 bstk2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
(*       1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 -> *)
      ceval' fc c1
        (l1 :: bstk1) (l2 :: bstk2) st1 st2 ->
      ceval' fc (CIf b c1 c2)
        ((LIf b l1 (com_to_label_pure c2)) :: bstk1)
        ((LIf b l2 (com_to_label_pure c2)) :: bstk2) st1 st2
  | E'_If2 : forall fc b c1 c2 l1 l2 bstk1 bstk2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
(*       1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 -> *)
      ceval' fc c2
        (l1 :: bstk1) (l2 :: bstk2) st1 st2 ->
      ceval' fc (CIf b c1 c2)
        ((LIf b (com_to_label_pure c1) l1) :: bstk1)
        ((LIf b (com_to_label_pure c1) l2) :: bstk2) st1 st2

  | E'_WhileFalse : forall fc b c loc glb,
      beval (loc, glb) b = false ->
      ceval' fc (CWhile b c)
        ((LWhile b (com_to_label_pure c)) :: nil)
        ((LWhile b (com_to_label_pure c)) :: nil)
        (loc :: nil, glb) (loc :: nil, glb)
  | E'_WhileTrue1 : forall fc b c l1 l2 loc1 glb1 st2 bstk,
      is_pure l1 ->
      single_point l2 ->
(*       1 + length bstk = length sstk -> *)
      beval (loc1, glb1) b = true ->
      ceval' fc c
        (l1 :: nil) (l2 :: bstk)
        (loc1 :: nil, glb1) st2 ->
      ceval' fc (CWhile b c)
        ((LWhile b l1) :: nil) ((LWhile b l2) :: bstk)
        (loc1 :: nil, glb1) st2
  | E'_WhileTrue2 : forall fc b c l1 l2 loc1 glb1 bstk st1 st2,
      is_pure l1 ->
      valid_label l2 ->
(*       1 + length bstk = length sstk -> *)
      beval (loc1, glb1) b = true ->
      ceval' fc c
        ((com_to_label_pure c) :: nil)
        ((com_to_label_pure c) :: nil)
        (loc1 :: nil, glb1) st1 ->
      ceval' fc (CWhile b c)
        (l1 :: nil) (l2 :: bstk)
        st1 st2 ->
      ceval' fc (CWhile b c)
        (l1 :: nil) (l2 :: bstk)
        (loc1 :: nil, glb1) st2
  | E'_WhileSeg1 : forall fc b c l1 l2 bstk1 bstk2 st1 st2,
      single_point l1 ->
      single_point l2 ->
(*       1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 -> *)
      ceval' fc c
        (l1 :: bstk1) (l2 :: bstk2) st1 st2 ->
      ceval' fc (CWhile b c)
        ((LWhile b l1) :: bstk1) ((LWhile b l2) :: bstk2) st1 st2
  | E'_WhileSeg2 : forall fc b c l1 l2 bstk1 bstk2 st1 st2 st3,
      single_point l1 ->
      valid_label l2 ->
(*       1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 -> *)
      ceval' fc c
        (l1 :: bstk1) ((com_to_label_pure c) :: nil) st1 st3 ->
      ceval' fc (CWhile b c)
        ((LWhile b (com_to_label_pure c)) :: nil) (l2 :: bstk2) st3 st2 ->
      ceval' fc (CWhile b c)
        ((LWhile b l1) :: bstk1) (l2 :: bstk2) st1 st2
.

Lemma ceval'_valid_label :
  forall fc c l1 l2 bstk1 bstk2 st1 st2,
  ceval' fc c (l1 :: bstk1) (l2 :: bstk2) st1 st2 ->
  valid_label l1 /\ valid_label l2.
Proof.
  intros.
  assert (valid_label LPure); [left; apply IP_Pure |].
  assert (valid_label LHere); [right; apply SP_Here |].
  inversion H; subst;
  try (split; left; apply IP_Pure);
  try pose proof com_to_label_pure_is_pure c1 as Hpc1;
  try pose proof com_to_label_pure_is_pure c2 as Hpc2;
  try pose proof com_to_label_pure_is_pure c0 as Hpc0;
  try tauto.
  - destruct H6, H11.
    + split; left; apply IP_Seq; auto.
    + split; [left; apply IP_Seq | right; apply SP_Seq2]; auto.
    + split; [right; apply SP_Seq1 | left; apply IP_Seq]; auto.
    + split; right; [apply SP_Seq1 | apply SP_Seq2]; auto.
Admitted.

Corollary ceval'_valid_label_left :
  forall fc c l1 bstk1 bstk2 st1 st2,
  ceval' fc c (l1 :: bstk1) bstk2 st1 st2 ->
  valid_label l1.
Proof.
  intros.
  destruct bstk2; [inversion H |].
  apply ceval'_valid_label in H.
  tauto.
Qed.

Corollary ceval'_valid_label_right :
  forall fc c l2 bstk1 bstk2 st1 st2,
  ceval' fc c bstk1 (l2 :: bstk2) st1 st2 ->
  valid_label l2.
Proof.
  intros.
  destruct bstk1; [inversion H |].
  apply ceval'_valid_label in H.
  tauto.
Qed.

Lemma ceval'_depth_valid : forall fc c bstk1 bstk2 sstk1 sstk2 glb1 glb2,
  ceval' fc c bstk1 bstk2 (sstk1, glb1) (sstk2, glb2) ->
  length bstk1 = length sstk1 /\ length bstk2 = length sstk2.
Proof.
  intros.
  remember c as c'.
  inversion H; subst; auto.
  - simpl. repeat rewrite app_length.
    rewrite H9. auto.
  - simpl. repeat rewrite app_length.
    rewrite H9. auto.
  - simpl. repeat rewrite app_length.
    rewrite <- H10, <- H11.
    simpl. omega.
Admitted.

Corollary ceval'_depth_valid_left : forall fc c bstk1 bstk2 sstk1 glb1 st2,
  ceval' fc c bstk1 bstk2 (sstk1, glb1) st2 ->
  length bstk1 = length sstk1.
Proof.
  intros.
  destruct st2.
  apply ceval'_depth_valid in H.
  tauto.
Qed.

Corollary ceval'_depth_valid_right : forall fc c bstk1 bstk2 st1 sstk2 glb2,
  ceval' fc c bstk1 bstk2 st1 (sstk2, glb2) ->
  length bstk2 = length sstk2.
Proof.
  intros.
  destruct st1.
  apply ceval'_depth_valid in H.
  tauto.
Qed.

Definition single_point_stack bstk : Prop :=
  forall lb, In lb bstk -> single_point lb.

Lemma ceval'_single_point_stack_left_b2t :
  forall fc c l1 l2 bstk bstk2 st1 st2,
  single_point l1 ->
  ceval' fc c (l1 :: bstk ++ l2 :: nil) bstk2 st1 st2 ->
  single_point l2.
Proof.
  intros.
  remember (l1 :: bstk ++ l2 :: nil) as bstk1.
  revert dependent bstk.
  revert dependent l1.
  induction H0; intros; subst;
  try (pose proof eq_refl (length (l1 :: bstk ++ l2 :: nil)) as Htmp;
      rewrite <- Heqbstk1 in Htmp at 1;
      simpl in Htmp;
      rewrite app_length in Htmp;
      simpl in Htmp;
      omega);
  try (pose proof eq_refl (length (l1 :: bstk0 ++ l2 :: nil)) as Htmp;
      rewrite <- Heqbstk1 in Htmp at 1;
      simpl in Htmp;
      rewrite app_length in Htmp;
      simpl in Htmp;
      omega).
  - inversion Heqbstk1; subst;
    apply app_inj_tail in H5 as [? ?]; subst; auto.
  - repeat rewrite app_comm_cons in Heqbstk1.
    apply app_inj_tail in Heqbstk1 as [? ?]; subst; auto.
  - inversion Heqbstk1; subst.
    inversion H3; subst.
    + eapply IHceval'1; [exact H6 | auto].
    + apply pure_no_point in H1. congruence.
  - inversion Heqbstk1; subst.
    inversion H2; subst.
    + eapply IHceval'; [apply H5 | auto].
    + pose proof com_to_label_pure_no_point c2.
      congruence.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma ceval'_single_point_stack_right_b2t :
  forall fc c l1 l2 bstk bstk1 st1 st2,
  single_point l1 ->
  ceval' fc c bstk1 (l1 :: bstk ++ l2 :: nil) st1 st2 ->
  single_point l2.
Proof.
  intros.
  remember (l1 :: bstk ++ l2 :: nil) as bstk2.
  revert dependent bstk.
  revert dependent l1.
  induction H0; intros; subst;
  try (inversion Heqbstk2; subst;
      try app_cons_nil H2; try app_cons_nil H3).
  - apply app_inj_tail in H5 as [? ?]; subst; auto.
  - app_cons_nil H5.
  - apply app_inj_tail in H7 as [? ?]; subst; auto.
  - inversion H3; subst.
    + apply pure_no_point in H0. congruence.
    + eapply IHceval'2; [apply H7 | auto].
  - inversion H2; subst.
    + eapply IHceval'; [apply H5 | auto].
    + pose proof com_to_label_pure_no_point c2.
      congruence.
  - inversion H2; subst.
    + pose proof com_to_label_pure_no_point c1.
      congruence.
    + eapply IHceval'; [apply H6 | auto].
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - eapply IHceval'2; [apply H1 | auto].
Admitted.

Lemma ceval'_single_point_stack_right_t2b :
  forall fc c l1 l2 bstk bstk1 st1 st2,
  single_point l2 ->
  ceval' fc c bstk1 (l1 :: bstk ++ l2 :: nil) st1 st2 ->
  single_point l1.
Proof.
  intros.
  remember (l1 :: bstk ++ l2 :: nil) as bstk2.
  revert dependent bstk.
  revert dependent l1.
  induction H0; intros; subst;
  try (pose proof eq_refl (length (l1 :: bstk ++ l2 :: nil)) as Htmp;
      rewrite <- Heqbstk2 in Htmp at 1;
      simpl in Htmp;
      rewrite app_length in Htmp;
      simpl in Htmp;
      omega);
  try (pose proof eq_refl (length (l0 :: bstk0 ++ l2 :: nil)) as Htmp;
      rewrite <- Heqbstk2 in Htmp at 1;
      simpl in Htmp;
      rewrite app_length in Htmp;
      simpl in Htmp;
      omega);
  try (inversion Heqbstk2; subst;
    apply SP_Here).
  - inversion Heqbstk2; subst.
    pose proof IHceval'2 l4 bstk eq_refl.
    apply SP_Seq2; auto.
  - inversion Heqbstk2; subst.
    pose proof IHceval' l0 bstk eq_refl.
    apply SP_Seq1; auto. apply com_to_label_pure_is_pure.
  - inversion Heqbstk2; subst.
    pose proof IHceval' l0 bstk eq_refl.
    apply SP_Seq2; auto. apply com_to_label_pure_is_pure.
  - inversion Heqbstk2; subst.
    pose proof IHceval' l0 bstk0 eq_refl.
    apply SP_If1; auto. apply com_to_label_pure_is_pure.
  - inversion Heqbstk2; subst.
    pose proof IHceval' l0 bstk0 eq_refl.
    apply SP_If2; auto. apply com_to_label_pure_is_pure.
  - inversion Heqbstk2; subst.
    pose proof IHceval' l0 bstk eq_refl.
    apply SP_If1; auto. apply com_to_label_pure_is_pure.
  - inversion Heqbstk2; subst.
    pose proof IHceval' l0 bstk eq_refl.
    apply SP_If2; auto. apply com_to_label_pure_is_pure.
  - inversion Heqbstk2; subst.
    pose proof IHceval' l0 bstk0 eq_refl.
    apply SP_While; auto.
  - inversion Heqbstk2; subst.
    pose proof IHceval'2 l3 bstk0 eq_refl.
    auto.
  - inversion Heqbstk2; subst.
    pose proof IHceval' l0 bstk eq_refl.
    apply SP_While; auto.
  - inversion Heqbstk2; subst.
    pose proof IHceval'2 l3 bstk eq_refl.
    auto.
Qed.

Lemma ceval'_single_point_stack_left_t2b :
  forall fc c l1 l2 bstk bstk2 st1 st2,
  single_point l2 ->
  ceval' fc c (l1 :: bstk ++ l2 :: nil) bstk2 st1 st2 ->
  single_point l1.
Proof.
  intros.
  remember (l1 :: bstk ++ l2 :: nil) as bstk1.
  revert dependent bstk.
  revert dependent l1.
  induction H0; intros; subst;
  try (inversion Heqbstk1; subst;
      try app_cons_nil H2; try app_cons_nil H3;
      try app_cons_nil H5; try app_cons_nil H6).
  - apply app_inj_tail in H5 as [? ?]; subst.
    apply SP_Here.
  - apply SP_Here.
  - apply SP_Seq1; auto.
    eapply IHceval'1; auto.
  - apply SP_Seq1; [| apply com_to_label_pure_is_pure].
    eapply IHceval'; auto.
  - apply SP_Seq2; [apply com_to_label_pure_is_pure | auto].
  - apply SP_If1; [auto | apply com_to_label_pure_is_pure].
  - apply SP_If2; [apply com_to_label_pure_is_pure | auto].
  - apply SP_While; auto.
  - apply SP_While; auto.
Qed.
(** [] *)

(** Bridging basic ceval' to multi_ceval' *)
Definition restk : Type := list (com * option lbstk * state').

Inductive middle_ceval' : func_context -> list func -> restk -> restk -> Prop :=
  | ME_r_pure : forall fc lf c bstk st1 st2 stk,
      ceval' fc c bstk ((com_to_label_pure c) :: nil) st1 st2 ->
      middle_ceval' fc lf ((c, Some bstk, st1) :: stk) ((c, None, st2) :: stk)
  | ME_r_single : forall fc c l2 bstk1 bstk2 st1 st2 stk lf,
      single_point l2 ->
      ceval' fc c bstk1 (bstk2 ++ l2 :: nil) st1 st2 ->
      middle_ceval' fc lf ((c, Some bstk1, st1) :: stk) ((c, Some (bstk2 ++ l2 :: nil), st2) :: stk)
  | ME_re : forall fc c1 c2 l1 loc glb stk lf f bstk sstk,
      In f lf ->
      c2 = func_bdy f ->
      single_point l1 ->
      (* two calling stacks should match *)
      1 + length bstk = length sstk ->
      middle_ceval' fc lf
        ((c1, Some (bstk ++ l1 :: nil), (sstk, glb)) :: stk)
        (* Each reentry call clears the calling stack *)
        ((c2, Some ((com_to_label_pure c2) :: nil), (loc :: nil, glb))
          :: (c1, Some (bstk ++ l1 :: nil), (sstk, glb)) :: stk)
  | ME_ex : forall fc c1 c2 l2 glb1 glb2 stk lf bstk loc sstk,
      single_point l2 ->
      (* two calling stacks should match *)
      1 + length bstk = length sstk ->
      middle_ceval' fc lf
        ((c1, None, (loc :: nil, glb1))
          :: (c2, Some (bstk ++ l2 :: nil), (sstk, glb2)) :: stk)
        ((c2, Some (bstk ++ l2 :: nil), (sstk, glb1)) :: stk).

Definition multi_ceval' (fc : func_context) (lf : public_funcs) : restk -> restk -> Prop := clos_refl_trans (middle_ceval' fc lf).

Lemma middle_ceval'_right_single_point_top :
  forall fc lf stk1 c bstk l2 st2,
  middle_ceval' fc lf stk1 ((c, Some (bstk ++ l2 :: nil), st2) :: nil) ->
  single_point l2.
Proof.
  intros.
  inversion H; subst;
  apply app_inj_tail in H1 as [? ?]; subst;
  auto.
Qed.

Lemma middle_ceval'_right_single_point_bottom :
  forall fc lf y c1 l1 bstk bstk1 st1 st2 st3,
  ceval' fc c1 (l1 :: bstk) bstk1 st2 st3 ->
  middle_ceval' fc lf y ((c1, Some (l1 :: bstk), st1) :: nil) ->
  single_point l1.
Proof.
  intros.
  inversion H0; subst.
  - destruct bstk2, bstk.
    + inversion H2; subst; auto.
    + pose proof eq_refl (length (nil ++ l2 :: nil)).
      rewrite H2 in H1 at 1.
      rewrite app_length in H1.
      simpl in H1. omega.
    + pose proof eq_refl (length (l1 :: nil)).
      rewrite <- H2 in H1 at 1.
      simpl in H1. rewrite app_length in H1.
      simpl in H1. omega.
    + inversion H2; subst.
      apply ceval'_single_point_stack_right_t2b in H9; auto.
  - remember (rev bstk) as bstk'.
    destruct bstk', bstk0.
    + pose proof rev_involutive bstk.
      rewrite <- Heqbstk' in H1; subst.
      inversion H2; subst. auto.
    + pose proof rev_involutive bstk.
      rewrite <- Heqbstk' in H1; subst.
      inversion H2; subst.
      pose proof eq_refl (length (bstk0 ++ l2 :: nil)).
      rewrite H4 in H1 at 1.
      rewrite app_length in H1. simpl in H1.
      omega.
    + inversion H2; subst.
      pose proof eq_refl (length (l :: bstk')).
      rewrite Heqbstk' in H1 at 1.
      simpl in H1. omega.
    + inversion H2; subst.
      apply ceval'_single_point_stack_left_t2b in H; auto.
Qed.

Lemma middle_ceval'_right_nil_label :
  forall fc lf stk1 c st stk2,
  middle_ceval' fc lf stk1 ((c, Some nil, st) :: stk2) -> False.
Proof.
  intros.
  inversion H; subst.
  - pose proof eq_refl (length (bstk2 ++ l2 :: nil)).
    rewrite H1 in H0 at 1.
    rewrite app_length in H0.
    simpl in H0. omega.
  - pose proof eq_refl (length (bstk ++ l2 :: nil)).
    rewrite H1 in H0 at 1.
    rewrite app_length in H0.
    simpl in H0. omega.
Qed.
(** [] *)

Lemma middle_ceval'_seq_head_some:
  forall fc lf c1 c2 l1 l2 st1 st2 stk1 stk2 bstk,
  single_point l1 ->
  middle_ceval' fc lf
    (stk1 ++ (c2, Some (l1 :: bstk), st1) :: nil)
    (stk2 ++ (c2, Some (l2 :: bstk), st2) :: nil) ->
  middle_ceval' fc lf
    (stk1 ++ (CSeq c1 c2, Some ((LSeq (com_to_label_pure c1) l1) :: bstk), st1) :: nil)
    (stk2 ++ (CSeq c1 c2, Some ((LSeq (com_to_label_pure c1) l2) :: bstk), st2) :: nil).
Proof.
  intros.
  destruct stk1, stk2; simpl in *.
  - inversion H0; subst.
    destruct st1, st2.
    pose proof ceval'_depth_valid _ _ _ _ _ _ _ _ H10 as [? ?].
    remember (rev bstk) as bstk'.
    destruct bstk'; pose proof rev_involutive bstk;
    rewrite <- Heqbstk' in H3; subst; simpl in *.
    {
      destruct bstk2.
      - inversion H8; subst.
        replace (LSeq (com_to_label_pure c1) l1 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l1 :: nil); auto.
        replace (LSeq (com_to_label_pure c1) l2 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l2 :: nil); auto.
        apply ME_r_single.
        + apply SP_Seq2; auto.
          apply com_to_label_pure_is_pure.
        + eapply E'_Seq2; auto.
          right. auto.
      - inversion H8; subst.
        pose proof eq_refl (length (bstk2 ++ l0 :: nil)).
        rewrite H6 in H3 at 1.
        rewrite app_length in H3.
        simpl in H3. omega.
    }
    {
      rewrite app_comm_cons in H8.
      apply app_inj_tail in H8 as [? ?]; subst.
      repeat rewrite app_comm_cons.
      apply ME_r_single; auto.
      eapply E'_Seq2; auto.
      apply ceval'_valid_label_right in H10.
      auto.
    }
  - inversion H0; subst.
    + pose proof length_nil_app_cons _ _ H9. inversion H1.
    + pose proof length_nil_app_cons _ _ H9. inversion H1.
    + destruct stk2; simpl in *; inversion H9; subst.
      * remember (rev bstk) as bstk';
        destruct bstk'; pose proof rev_involutive bstk as Hrev;
        rewrite <- Heqbstk' in Hrev; subst; simpl in *;
        destruct bstk0; inversion H3; subst;
        inversion H2; subst.
        {
          replace (LSeq (com_to_label_pure c1) l1 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l1 :: nil); auto.
          eapply ME_re; [exact H8 | | |]; auto.
          apply SP_Seq2; auto.
          apply com_to_label_pure_is_pure.
        }
        {
          pose proof eq_refl (length (bstk0 ++ l0 :: nil)).
          rewrite H5 in H1 at 1.
          app_len_inv H1.
        }
        {
          pose proof eq_refl (length (rev bstk' ++ l :: nil)).
          rewrite <- H5 in H1 at 1.
          app_len_inv H1.
        }
        {
          apply app_inj_tail in H5 as [? ?]; subst.
          repeat rewrite app_comm_cons.
          eapply ME_re; [exact H8 | | |]; auto.
        }
      * pose proof length_nil_app_cons _ _ H4. inversion H1.
  - inversion H0; subst.
    + apply eq_sym in H9.
      pose proof length_nil_app_cons _ _ H9. inversion H1.
    + destruct stk1; simpl in *; inversion H2; subst.
      remember (rev bstk) as bstk';
      destruct bstk'; pose proof rev_involutive bstk as Hrev;
      rewrite <- Heqbstk' in Hrev; subst; simpl in *;
      destruct bstk0; inversion H3; subst;
      inversion H7; subst; try app_cons_nil H5.
      {
        replace (LSeq (com_to_label_pure c1) l2 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l2 :: nil); auto.
        eapply ME_ex; auto.
        apply SP_Seq2; auto.
        apply com_to_label_pure_is_pure.
      }
      {
        apply app_inj_tail in H5 as [? ?]; subst.
        rewrite app_comm_cons.
        eapply ME_ex; auto.
      }
      * pose proof length_nil_app_cons _ _ H4. inversion H1.
  - inversion H0; subst.
    + apply app_inj_tail in H7 as [? ?].
      inversion H2; subst.
      apply ME_r_pure; assumption.
    + apply app_inj_tail in H7 as [? ?].
      inversion H2; subst.
      apply ME_r_single; assumption.
    + rewrite app_comm_cons in H4.
      apply app_inj_tail in H4 as [? ?].
      inversion H2; subst.
      eapply ME_re; try assumption.
      exact H7. auto.
    + rewrite app_comm_cons in H2.
      apply app_inj_tail in H2 as [? ?].
      inversion H2; subst.
      apply ME_ex; try assumption.
Qed.

Lemma multi_ceval'_seq_head:
  forall l1 fc lf c2 st4 st3 c1 bstk,
  single_point l1 ->
  clos_refl_trans (middle_ceval' fc lf)
      ((c2, Some (l1 :: bstk), st4) :: nil)
      ((c2, None, st3) :: nil) ->
  clos_refl_trans (middle_ceval' fc lf)
      ((CSeq c1 c2, Some ((LSeq (com_to_label_pure c1) l1) :: bstk), st4) :: nil)
      ((CSeq c1 c2, None, st3) :: nil).
Proof.
  intros.
  set (stk := @nil (com * option lbstk * state')).
  unfold stk.
  change ((c2, Some (l1 :: bstk), st4) :: nil) with (stk ++ (c2, Some (l1 :: bstk), st4) :: nil) in H0.
  change ((CSeq c1 c2, Some ((LSeq (com_to_label_pure c1) l1) :: bstk), st4) :: nil) with (stk ++ (CSeq c1 c2, Some ((LSeq (com_to_label_pure c1) l1) :: bstk), st4) :: nil).
  clearbody stk.
  remember (stk ++ (c2, Some (l1 :: bstk), st4) :: nil) as l.
  remember ((c2, None, st3) :: nil) as l'.
  apply Operators_Properties.clos_rt_rt1n in H0.
  revert Heql.
  revert stk bstk st4.
  revert c1.
  generalize dependent l1.
  induction H0; intros; subst.
  - destruct stk; inversion Heql; subst.
    pose proof length_nil_app_cons _ _ H2. inversion H0.
  - specialize (IHclos_refl_trans_1n eq_refl).
    inversion H; subst.
    + destruct stk.
      * inversion H2; subst.
        inversion H0; subst.
        {
          apply rt_step, ME_r_pure. simpl.
          destruct st3, st4.
          pose proof ceval'_depth_valid _ _ _ _ _ _ _ _ H5 as [? ?].
          eapply E'_Seq2; try assumption.
          apply com_to_label_pure_valid.
        }
        {
          inversion H3.
        }
      * simpl in H2.
        inversion H2; subst; clear H2.
        simpl.
        pose proof IHclos_refl_trans_1n l1 H1 c1 ((c, None, st2) :: stk) bstk st4 eq_refl.
        eapply rt_trans; [| apply H2].
        apply rt_step, ME_r_pure.
        apply H5.
    + destruct stk.
      * inversion H2; subst.
        destruct bstk2 as [| l0 bstk2].
        {
          pose proof IHclos_refl_trans_1n l2 H3 c1 nil nil st2 eq_refl.
          eapply rt_trans; [| apply H4].
          change (LSeq (com_to_label_pure c1) l2 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l2 :: nil).
          apply rt_step, ME_r_single; auto.
          + apply SP_Seq2; auto.
            apply com_to_label_pure_is_pure.
          + eapply E'_Seq2; auto.
            right; auto.
       }
       {
          pose proof H6.
          apply ceval'_single_point_stack_right_t2b in H4; auto.
          pose proof IHclos_refl_trans_1n l0 H4 c1 nil (bstk2 ++ l2 :: nil) st2 eq_refl.
          eapply rt_trans; [| apply H5].
          rewrite app_comm_cons.
          apply rt_step, ME_r_single; auto.
          apply E'_Seq2; auto.
          right; auto.
       }
    * inversion H2; subst.
      pose proof IHclos_refl_trans_1n l1 H1 c1 ((c, Some (bstk2 ++ l2 :: nil), st2) :: stk) bstk st4 eq_refl.
      eapply rt_trans; [| apply H4].
      apply rt_step, ME_r_single; auto.
  + destruct stk.
    * inversion H2; subst.
      destruct bstk0.
      {
        inversion H7; subst.
        pose proof IHclos_refl_trans_1n l1 H1 c1 ((func_bdy f, Some (com_to_label_pure (func_bdy f) :: nil), (loc :: nil, glb)) :: nil) nil (sstk, glb) eq_refl.
        eapply rt_trans; [| apply H4].
        change (LSeq (com_to_label_pure c1) l1 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l1 :: nil).
        eapply rt_step, ME_re; auto.
        + apply H3.
        + apply SP_Seq2; auto.
          apply com_to_label_pure_is_pure.
      }
      {
        inversion H7; subst.
        pose proof IHclos_refl_trans_1n l1 H1 c1 ((func_bdy f, Some (com_to_label_pure (func_bdy f) :: nil), (loc :: nil, glb)) :: nil) (bstk0 ++ l0 :: nil) (sstk, glb) eq_refl.
        eapply rt_trans; [| apply H4].
        rewrite app_comm_cons.
        eapply rt_step, ME_re; auto.
        exact H3.
      }
    * inversion H2; subst.
      pose proof IHclos_refl_trans_1n l1 H1 c1 ((func_bdy f, Some (com_to_label_pure (func_bdy f) :: nil), (loc :: nil, glb)) :: (c0, Some (bstk0 ++ l0 :: nil), (sstk, glb)) :: stk) bstk st4 eq_refl.
      eapply rt_trans; [| apply H4].
      eapply rt_step, ME_re; auto.
      exact H3.
  + destruct stk.
    * inversion H2; subst.
    * inversion H2; subst.
      destruct stk.
      {
        inversion H7; subst.
        destruct bstk0.
        + inversion H8; subst.
          pose proof IHclos_refl_trans_1n l1 H1 c1 nil nil (sstk, glb1) eq_refl.
          eapply rt_trans; [| apply H4].
          change (LSeq (com_to_label_pure c1) l1 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l1 :: nil).
          eapply rt_step, ME_ex; auto.
          apply SP_Seq2; auto.
          apply com_to_label_pure_is_pure.
        + inversion H8; subst.
          pose proof IHclos_refl_trans_1n l1 H1 c1 nil (bstk0 ++ l2 :: nil) (sstk, glb1) eq_refl.
          eapply rt_trans; [| apply H4].
          rewrite app_comm_cons.
          eapply rt_step, ME_ex; auto.
      }
      {
        inversion H7; subst.
        pose proof IHclos_refl_trans_1n l1 H1 c1 ((c3, Some (bstk0 ++ l2 :: nil), (sstk, glb1)) :: stk) bstk st4 eq_refl.
        eapply rt_trans; [| apply H4].
        eapply rt_step, ME_ex; auto.
      }
Qed.

Lemma multi_ceval'_seq_tail:
  forall l1 fc lf c1 c2 st1 st0 bstk,
  single_point l1 ->
  clos_refl_trans (middle_ceval' fc lf)
      ((c1, Some ((com_to_label_pure c1) :: nil), st1) :: nil)
      ((c1, Some (l1 :: bstk), st0) :: nil) ->
  clos_refl_trans (middle_ceval' fc lf)
      ((CSeq c1 c2, Some ((LSeq (com_to_label_pure c1) (com_to_label_pure c2)) :: nil), st1) :: nil)
      ((CSeq c1 c2, Some ((LSeq l1 (com_to_label_pure c2)) :: bstk), st0) :: nil).
Proof.
  intros.
Admitted.

Lemma multi_ceval'_if_branch:
  forall fc lf b c1 c2 l1 st3 st2 bstk,
  single_point l1 ->
  clos_refl_trans (middle_ceval' fc lf)
    ((c1, Some (l1 :: bstk), st3) :: nil)
    ((c1, None, st2) :: nil) ->
  clos_refl_trans (middle_ceval' fc lf)
    ((CIf b c1 c2, Some ((LIf b l1 (com_to_label_pure c2)) :: bstk), st3) :: nil)
    ((CIf b c1 c2, None, st2) :: nil).
Proof.
  intros.
Admitted.

Lemma multi_ceval'_else_branch:
  forall fc lf b c1 c2 l1 st3 st2 bstk,
  single_point l1 ->
  clos_refl_trans (middle_ceval' fc lf)
    ((c2, Some (l1 :: bstk), st3) :: nil)
    ((c2, None, st2) :: nil) ->
  clos_refl_trans (middle_ceval' fc lf)
    ((CIf b c1 c2, Some ((LIf b (com_to_label_pure c1) l1) :: bstk), st3) :: nil)
    ((CIf b c1 c2, None, st2) :: nil).
Proof.
  intros.
Admitted.

Lemma multi_ceval'_while_loop:
  forall fc lf b c l1 loc1 glb1 st2 bstk,
  beval (loc1, glb1) b = true ->
  clos_refl_trans (middle_ceval' fc lf)
    ((c, Some (com_to_label_pure c :: nil), (loc1 :: nil, glb1)) :: nil)
    ((c, Some (l1 :: bstk), st2) :: nil) ->
  clos_refl_trans (middle_ceval' fc lf)
    ((CWhile b c, Some ((LWhile b (com_to_label_pure c)) :: nil), (loc1 :: nil, glb1)) :: nil)
    ((CWhile b c, Some ((LWhile b l1) :: bstk), st2) :: nil).
Proof.
  intros.
Admitted.

Lemma multi_ceval'_call_bottom :
  forall fc lf f bstk1 bstk2 l1 l2 sstk1 sstk2 glb1 glb2 pv loc,
  single_point l1 ->
  single_point l2 ->
  clos_refl_trans (middle_ceval' fc lf)
    ((func_bdy f, Some (bstk1 ++ l1 :: nil), (sstk1, glb1)) :: nil)
    ((func_bdy f, Some (bstk2 ++ l2 :: nil), (sstk2, glb2)) :: nil) ->
  clos_refl_trans (middle_ceval' fc lf)
    ((f [(pv)], Some (LHere :: bstk1 ++ l1 :: nil),
      (loc :: sstk1, glb1)) :: nil)
    ((f [(pv)], Some (LHere :: bstk2 ++ l2 :: nil),
      (loc :: sstk2, glb2)) :: nil).
Proof.
  intros.
  set (stk := @nil (com * option lbstk * state')).
  replace ((func_bdy f, Some (bstk1 ++ l1 :: nil), (sstk1, glb1)) :: nil) with (stk ++ (func_bdy f, Some (bstk1 ++ l1 :: nil), (sstk1, glb1)) :: nil) in H1; auto.
  replace ((f [(pv)], Some (LHere :: bstk1 ++ l1 :: nil), (loc :: sstk1, glb1)) :: nil) with (stk ++ (f [(pv)], Some (LHere :: bstk1 ++ l1 :: nil), (loc :: sstk1, glb1)) :: nil); auto.
  clearbody stk.
  remember (stk ++ (func_bdy f, Some (bstk1 ++ l1 :: nil), (sstk1, glb1)) :: nil) as l.
  remember ((func_bdy f, Some (bstk2 ++ l2 :: nil), (sstk2, glb2)) :: nil) as l'.
  revert Heql.
  revert stk bstk1 sstk1 glb1.
  generalize dependent l1.
  apply Operators_Properties.clos_rt_rt1n in H1.
  induction H1; intros; subst.
  - destruct stk; [| inversion Heql; app_cons_nil H3].
    inversion Heql; subst.
    apply rt_refl.
  - specialize (IHclos_refl_trans_1n eq_refl).
    inversion H; subst.
    + destruct stk.
      * inversion H3; subst.
        inversion H1.
        inversion H4.
      * inversion H3; subst.
        pose proof IHclos_refl_trans_1n l1 H2 ((c, None, st2) :: stk) bstk1 sstk1 glb1 eq_refl.
        eapply rt_trans; [| apply H4].
        apply rt_step, ME_r_pure; auto.
    + destruct stk.
      * inversion H3; subst.
        destruct st2 as [sstk' glb'].
        pose proof IHclos_refl_trans_1n l0 H4 nil bstk3 sstk' glb' eq_refl.
        eapply rt_trans; [| apply H5].
        repeat rewrite app_comm_cons.
        apply rt_step, ME_r_single; auto.
        pose proof H7.
        apply ceval'_depth_valid in H6.
        repeat rewrite app_length in H6. simpl in H6.
        apply E'_CallSeg; auto; try omega.
      * inversion H3; subst.
        pose proof IHclos_refl_trans_1n l1 H2 ((c, Some (bstk3 ++ l0 :: nil), st2) :: stk) bstk1 sstk1 glb1 eq_refl.
        eapply rt_trans; [| apply H5].
        apply rt_step, ME_r_single; auto.
    + destruct stk.
      * inversion H3; subst.
        apply app_inj_tail in H8 as [? ?]; subst.
        pose proof IHclos_refl_trans_1n l1 H2 ((func_bdy f0, Some (com_to_label_pure (func_bdy f0) :: nil), (loc0 :: nil, glb1)) :: nil) bstk1 sstk1 glb1 eq_refl.
        eapply rt_trans; [| apply H5].
        simpl.
        apply rt_step.
        rewrite app_comm_cons.
        eapply ME_re; [exact H4 | | |]; auto.
        simpl. rewrite <- H9.
        omega.
      * inversion H3; subst.
        pose proof IHclos_refl_trans_1n l1 H2 ((func_bdy f0, Some (com_to_label_pure (func_bdy f0) :: nil), (loc0 :: nil, glb)) :: (c1, Some (bstk ++ l0 :: nil), (sstk, glb)) :: stk) bstk1 sstk1 glb1 eq_refl.
        eapply rt_trans; [| apply H5].
        apply rt_step.
        rewrite app_comm_cons.
        eapply ME_re; [exact H4 | | |]; auto.
    + destruct stk.
      * inversion H3; subst.
      * inversion H3; subst.
        destruct stk.
        {
          inversion H8; subst.
          apply app_inj_tail in H9 as [? ?]; subst.
          pose proof IHclos_refl_trans_1n l1 H2 nil bstk1 sstk1 glb0 eq_refl.
          eapply rt_trans; [| apply H5].
          apply rt_step.
          rewrite app_comm_cons.
          apply ME_ex; auto.
          simpl. rewrite <- H7.
          omega.
        }
        {
          inversion H8; subst.
          pose proof IHclos_refl_trans_1n l1 H2 ((c2, Some (bstk ++ l0 :: nil), (sstk, glb0)) :: stk) bstk1 sstk1 glb1 eq_refl.
          eapply rt_trans; [| apply H5].
          apply rt_step.
          rewrite app_comm_cons.
          apply ME_ex; auto.
        }
Qed.

Lemma multi_ceval'_elevate:
  forall fc lf c bstk1 bstk2 st1 st2 stk,
  multi_ceval' fc lf ((c, bstk1, st1) :: nil) ((c, bstk2, st2) :: nil) ->
  multi_ceval' fc lf ((c, bstk1, st1) :: stk) ((c, bstk2, st2) :: stk).
Proof.
  intros.
Admitted.

(** Denotational Sematics Relation *)
Theorem ceval_multi_ceval' : forall fc lf c loc1 loc2 glb1 glb2,
    ceval fc lf c (loc1, glb1) (loc2, glb2) ->
    multi_ceval' fc lf
      ((c, Some ((com_to_label_pure c) :: nil), ((loc1 :: nil), glb1)) :: nil)
      ((c, None, ((loc2 :: nil), glb2)) :: nil)
  with arbitrary_eval_multi_ceval' : forall fc lf glb1 glb2 bstk sstk,
    arbitrary_eval fc lf glb1 glb2 ->
    forall lb c,
    single_point lb ->
    1 + length bstk = length sstk ->
    multi_ceval' fc lf
      ((c, Some (bstk ++ lb :: nil), (sstk, glb1)) :: nil)
      ((c, Some (bstk ++ lb :: nil), (sstk, glb2)) :: nil).
Proof.
{
  intros.
  clear ceval_multi_ceval'.
  remember (loc1, glb1) as st1.
  remember (loc2, glb2) as st2.
  revert dependent loc1.
  revert dependent loc2.
  revert dependent glb1.
  revert dependent glb2.
  induction H; intros.
  - subst. inversion Heqst1; subst.
    simpl.
    apply rt_step, ME_r_pure.
    simpl. apply E'_Skip.
  - subst st. simpl.
    apply rt_step, ME_r_pure.
    simpl. eapply E'_Ass.
    apply H.
    apply Heqst2.
  - destruct st2 as (loc3, glb3); subst.
    specialize (IHceval1 glb3 glb1 loc3 eq_refl loc1 eq_refl).
    specialize (IHceval2 glb2 glb3 loc2 eq_refl loc3 eq_refl).
    simpl.
    apply Operators_Properties.clos_rt_rtn1 in IHceval1.
    apply Operators_Properties.clos_rt_rt1n in IHceval2.
    inversion IHceval1; subst; inversion IHceval2; subst.
    + inversion H1; subst; inversion H3; subst.
      * inversion H4; subst.
        2:{ inversion H5. } clear H4.
        inversion H2; subst.
        {
          apply rt_step, ME_r_pure.
          eapply E'_Seq; auto.
          apply com_to_label_pure_valid.
          apply com_to_label_pure_is_pure.
          apply com_to_label_pure_is_pure.
          apply com_to_label_pure_valid.
          exact H9. exact H13.
        }
        {
          (* construct label *)
          destruct bstk as [| l1];
          [apply middle_ceval'_right_nil_label in H4; inversion H4 |].
          assert (single_point l1).
          {
            eapply middle_ceval'_right_single_point_bottom.
            - apply H9.
            - apply H4.
          }
          (* label constructed *)
          apply Operators_Properties.clos_rtn1_rt in H2.
          eapply multi_ceval'_seq_tail in H2.
          eapply rt_trans.
          apply H2.
          apply rt_step, ME_r_pure.
          destruct st1 as [sstk' glb'].
          eapply E'_Seq.
          + right; exact H6.
          + apply com_to_label_pure_is_pure.
          + apply com_to_label_pure_is_pure.
          + apply com_to_label_pure_valid.
          + exact H9.
          + exact H13.
          + exact H6.
        }
      * (* construct l1 *)
        destruct bstk as [| l1 bstk1]; [inversion H9 |].
        pose proof H9 as Htmp1.
        apply ceval'_valid_label_left in Htmp1.
        (* l1 constructed *)
        (* construct l2' *)
        
        (* remember (bstk2 ++ l2 :: nil) as bstk2'.
        destruct bstk2' as [| l2' ?]; [inversion Htmp4 |].
        assert (valid_label l2') as Htmp2.
        {
          destruct bstk2; inversion Heqbstk2'; subst.
          - right. auto.
          - apply ceval'_valid_label_right in H14.
            auto.
        }
        pose proof E'_Seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ Htmp1 (com_to_label_pure_is_pure _) (com_to_label_pure_is_pure _) Htmp2 Htmp3 Htmp4 H9 H14. (* clear Htmp1 Htmp2 Htmp3 Htmp4. *)
        apply Operators_Properties.clos_rt1n_rt in H4.
          inversion H2; subst.
          {
            eapply multi_ceval'_seq_head in H4; auto.
            eapply rt_trans; [| exact H4].
            replace (LSeq (com_to_label_pure c1) l2 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l2 :: nil); auto.
            apply rt_step, ME_r_single; auto. *)
        
        destruct bstk2 as [| l2' bstk2].
        {
          assert (valid_label l2) as Htmp2; [right; auto |].
          pose proof E'_Seq _ _ _ _ _ _ _ _ _ _ _ _ Htmp1 (com_to_label_pure_is_pure _) (com_to_label_pure_is_pure _) Htmp2 H9 H14; clear Htmp1 Htmp2.
          apply Operators_Properties.clos_rt1n_rt in H4.
          inversion H2; subst.
          {
            eapply multi_ceval'_seq_head in H4; auto.
            eapply rt_trans; [| exact H4].
            replace (LSeq (com_to_label_pure c1) l2 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l2 :: nil); auto.
            apply rt_step, ME_r_single; auto.
            apply SP_Seq2, H13. apply com_to_label_pure_is_pure.
          }
          {
            assert (single_point l1).
            {
              eapply middle_ceval'_right_single_point_bottom.
              - apply H9.
              - apply H6.
            }
            apply Operators_Properties.clos_rtn1_rt in H2.
            eapply multi_ceval'_seq_tail in H2; try assumption.
            eapply multi_ceval'_seq_head in H4; try assumption.
            eapply rt_trans; [apply H2 |].
            eapply rt_trans; [| apply H4].
            clear H2 H4.
            change (LSeq (com_to_label_pure c1) l2 :: nil) with (nil ++ LSeq (com_to_label_pure c1) l2 :: nil).
            apply rt_step, ME_r_single; auto.
            apply SP_Seq2; auto.
            apply com_to_label_pure_is_pure.
        }
      }
      {
        pose proof H14 as Htmp2.
        apply ceval'_valid_label_right in Htmp2.
        pose proof E'_Seq _ _ _ _ _ _ _ _ _ _ _ _ Htmp1 (com_to_label_pure_is_pure _) (com_to_label_pure_is_pure _) Htmp2 H9 H14; clear Htmp1 Htmp2.
        apply Operators_Properties.clos_rt1n_rt in H4.
        inversion H2; subst.
        {
          pose proof H14.
          apply ceval'_single_point_stack_right_t2b in H6; auto.
          eapply multi_ceval'_seq_head in H4; auto.
          eapply rt_trans; [| exact H4].
          replace (LSeq (com_to_label_pure c1) l2'
      :: (fix app (l m : list label) {struct l} : list label :=
            match l with
            | nil => m
            | a :: l1 => a :: app l1 m
            end) bstk2 (l2 :: nil)) with ((LSeq (com_to_label_pure c1) l2'
      ::  bstk2) ++ l2 :: nil); auto.
          apply rt_step, ME_r_single; auto.
        }
        {
          assert (single_point l1).
          {
            eapply middle_ceval'_right_single_point_bottom.
            - apply H9.
            - apply H6.
          }
          apply Operators_Properties.clos_rtn1_rt in H2.
          eapply multi_ceval'_seq_tail in H2; try assumption.
          eapply multi_ceval'_seq_head in H4; try assumption.
          replace (LSeq (com_to_label_pure c1) l2'
      :: (fix app (l m : list label) {struct l} : list label :=
            match l with
            | nil => m
            | a :: l1 => a :: app l1 m
            end) bstk2 (l2 :: nil)) with ((LSeq (com_to_label_pure c1) l2'
      ::  bstk2) ++ l2 :: nil) in H5; auto.
          eapply ME_r_single, rt_step in H5; auto.
          {
            eapply rt_trans.
            apply H2.
            eapply rt_trans.
            apply H5.
            apply H4.
          }
          {
            eapply ceval'_single_point_stack_right_t2b.
            + apply H13.
            + apply H14.
          }
        }
      }
      * destruct bstk0; [| simpl in H17; omega].
        inversion H6; subst.
        pose proof com_to_label_pure_no_point c2.
        tauto.
  - (* subst.
    specialize (IHceval glb2 glb1 loc2 eq_refl loc1 eq_refl).
    apply Operators_Properties.clos_rt_rt1n in IHceval.
    inversion IHceval; subst.
    inversion H1; subst.
    + inversion H2; subst; [| inversion H3].
      eapply E'_IfTrue, ME_r_pure, rt_step in H10; auto.
      * exact H10.
      * apply com_to_label_pure_is_pure.
      * apply com_to_label_pure_valid.
      * auto.
    + apply Operators_Properties.clos_rt1n_rt in H2.
      eapply multi_ceval'_if_branch in H2.
      eapply rt_trans.
      2:{ exact H2. }
      apply rt_step, ME_r_single; auto.
      * apply SP_If1; [exact H10 | apply com_to_label_pure_is_pure].
      * pose proof H11 as Htmp.
        destruct st2 as [[| loc' sstk'] glb'];
        apply ceval'_depth_valid_right in Htmp; [inversion Htmp |].
        apply E'_IfTrue; auto.
        ++ apply com_to_label_pure_is_pure.
        ++ right. exact H10.
      * exact H10.
    + pose proof com_to_label_pure_no_point c1.
      congruence. *)
    admit.
  - (* subst.
    specialize (IHceval glb2 glb1 loc2 eq_refl loc1 eq_refl).
    apply Operators_Properties.clos_rt_rt1n in IHceval.
    inversion IHceval; subst.
    inversion H1; subst.
    + inversion H2; subst; [| inversion H3].
      eapply E'_IfFalse, ME_r_pure, rt_step in H10; auto.
      * exact H10.
      * apply com_to_label_pure_is_pure.
      * apply com_to_label_pure_valid.
      * auto.
    + apply Operators_Properties.clos_rt1n_rt in H2.
      eapply multi_ceval'_else_branch in H2.
      eapply rt_trans.
      2:{ exact H2. }
      apply rt_step, ME_r_single; auto.
      * apply SP_If2; [apply com_to_label_pure_is_pure | exact H10].
      * pose proof H11 as Htmp.
        destruct st2 as [[| loc' sstk'] glb'];
        apply ceval'_depth_valid_right in Htmp; [inversion Htmp |].
        apply E'_IfFalse; auto.
        ++ apply com_to_label_pure_is_pure.
        ++ right. exact H10.
      * exact H10.
    + pose proof com_to_label_pure_no_point c2.
      congruence. *)
    admit.
  - subst.
    inversion Heqst1; subst.
    apply rt_step, ME_r_pure, E'_WhileFalse.
    exact H.
  - (* subst.
    destruct st2 as [loc3 glb3].
    specialize (IHceval1 glb3 glb1 loc3 eq_refl loc1 eq_refl).
    specialize (IHceval2 glb2 glb3 loc2 eq_refl loc3 eq_refl).
    simpl in *.
    apply Operators_Properties.clos_rt_rtn1 in IHceval1.
    apply Operators_Properties.clos_rt_rt1n in IHceval2.
    inversion IHceval1; inversion IHceval2; subst.
    inversion H2; inversion H5; subst.
    + inversion H6; subst.
      2:{ inversion H4. }
      inversion H3; subst.
      {
        assert (1 + @length label nil = length (loc2 :: nil)) as Htmp; auto.
        pose proof E'_WhileTrue2 _ _ _ _ _ _ _ _ _ _ _ ltac: (apply IP_While, com_to_label_pure_is_pure) (com_to_label_pure_valid _) Htmp H H10 H20.
        eapply rt_step, ME_r_pure, H4.
      }
      {
        destruct bstk as [| l1 bstk]; [inversion H4 |].
        assert (single_point l1); [inversion H4; assumption |].
        eapply Operators_Properties.clos_rtn1_rt, multi_ceval'_while_loop in H3; try assumption; [| exact H].
        eapply rt_trans; [apply H3 |].
        apply rt_step, ME_r_pure.
        destruct st1 as [sstk' glb'].
        eapply E'_WhileSeg2; auto.
        * apply com_to_label_pure_valid.
        * apply ceval'_depth_valid_left in H10.
          auto.
        * exact H10.
        * exact H20.
      }
    + apply Operators_Properties.clos_rt1n_rt in H6.
      inversion H3; subst.
      {
        eapply rt_trans.
        2:{ exact H6. }
        apply rt_step, ME_r_single; auto.
        destruct st3 as [sstk' glb'].
        eapply E'_WhileTrue2; auto.
        * apply IP_While, com_to_label_pure_is_pure.
        * right; auto.
        * apply ceval'_depth_valid_right in H21.
          auto.
        * exact H10.
        * exact H21.
      }
      {
        apply Operators_Properties.clos_rtn1_rt in H3.
        destruct bstk as [| l1 bstk]; [inversion H10 |].
        eapply multi_ceval'_while_loop in H3; [| exact H].
        eapply rt_trans; [exact H3 |].
        eapply rt_trans; [| exact H6].
        inversion H5; subst.
        apply rt_step, ME_r_single; auto.
        destruct st1 as [sstk' glb'].
        destruct st3 as [sstk'' glb''].
        eapply E'_WhileSeg2.
        + inversion H4; assumption.
        + right; assumption.
        + apply ceval'_depth_valid_left in H10. auto.
        + apply ceval'_depth_valid_right in H19. auto.
        + exact H10.
        + exact H21.
      }
    + inversion H24.
      pose proof com_to_label_pure_no_point c.
      congruence. *)
    admit.
  - inversion Heqst1; inversion Heqst2; subst; clear Heqst2 Heqst1.
    specialize (IHceval glb0 glb3 loc2 eq_refl (param_to_local_state (loc0, glb3) (func_arg f) pv) eq_refl).
    
    apply Operators_Properties.clos_rt_rt1n in IHceval.
    inversion IHceval; subst.
    inversion H0; subst.
    + destruct st2 as [[|loc' [| sstk']] glb'].
      * apply ceval'_depth_valid_right in H9.
        simpl in H9. omega.
      * eapply E'_CallPure in H9.
        apply rt_step, ME_r_pure.
        inversion H1; subst; [| inversion H2].
        apply H9.
      * apply ceval'_depth_valid_right in H9.
        simpl in H9. omega.
    + (* adjust call head *)
      destruct st2 as [sstk' glb'].
      remember (rev sstk') as sstk1.
      destruct sstk1 as [| loc' sstk1];
      pose proof rev_involutive sstk';
      rewrite <- Heqsstk1 in H2; subst;
      [apply ceval'_depth_valid_right in H10;
      app_len_inv H10 |].
      pose proof H10.
      apply ceval'_depth_valid_right in H2.
      simpl in H2.
      repeat rewrite app_length in H2.
      simpl in H2.
      apply E'_CallOut in H10; auto.
      2:{ 
        replace ((fix rev (l : list unit_state) : list unit_state :=
                 match l with
                 | nil => nil
                 | x :: l' => rev l' ++ x :: nil
                 end) sstk1) with (rev sstk1); auto.
        omega.
      }
      clear H2.
      replace ((fix rev (l : list unit_state) : list unit_state :=
                 match l with
                 | nil => nil
                 | x :: l' => rev l' ++ x :: nil
                 end) sstk1) with (rev sstk1) in H10; auto.
      repeat rewrite app_comm_cons in H10.
      eapply ME_r_single, rt_step in H10; auto.
      eapply rt_trans; [apply H10 |].
      (* call head adjusted *)
      
      (* call tail *)
      apply Operators_Properties.clos_rt1n_rt in H1.
      apply Operators_Properties.clos_rt_rtn1 in H1.
      inversion H1; subst.
      inversion H2; subst.
      (* label adjustment *)
      remember (rev bstk) as bstk'.
      destruct bstk' as [| l1 bstk'];
      pose proof rev_involutive bstk;
      rewrite <- Heqbstk' in H4; subst;
      [inversion H8 |].
      simpl in *.
      remember (rev bstk') as bstk1.
      clear dependent bstk'.
      (* state adjustment *)
      destruct st1 as [sstk' glb''].
      remember (rev sstk') as sstk''.
      destruct sstk'' as [| loc'' sstk''];
      pose proof rev_involutive sstk';
      rewrite <- Heqsstk'' in H4; subst;
      [apply ceval'_depth_valid_left in H8;
      app_len_inv H8 |].
      simpl in *.
      remember (rev sstk'') as sstk2.
      clear dependent sstk''.
      (* adjustments complete *)
      assert (single_point l1).
      {
        inversion H3; subst.
        - apply app_inj_tail in H5 as [? ?]; subst.
          auto.
        - eapply middle_ceval'_right_single_point_top.
          apply H4.
      }
      pose proof H8.
      apply ceval'_depth_valid_left in H5.
      repeat rewrite app_length in H5.
      simpl in H5.
      eapply E'_CallRet in H8; [| auto | omega].
      eapply ME_r_pure, rt_step in H8.
      eapply rt_trans; [| apply H8].
      apply Operators_Properties.clos_rtn1_rt in H3.
      apply multi_ceval'_call_bottom; auto.
    + destruct bstk.
      * inversion H3; subst.
        pose proof com_to_label_pure_no_point (func_bdy f).
        congruence.
      * pose proof eq_refl (length ((l :: bstk) ++ l1 :: nil)).
        rewrite H3 in H2 at 1.
        app_len_inv H2.
  - inversion Heqst1; inversion Heqst2; subst.
    clear Heqst1 Heqst2.
    simpl in *.
    apply Operators_Properties.clos_rtn1_rt.
    eapply rtn1_trans.
    eapply ME_r_pure.
    apply E'_Reentryr2.
    apply Operators_Properties.clos_rt_rtn1.
    apply Operators_Properties.clos_rt1n_rt.
    eapply rt1n_trans.
    apply ME_r_single.
    2:{
      pose proof E'_Reentry1c fc loc2 glb3.
      change (LHere :: nil) with (nil ++ LHere :: nil) in H0.
      apply H0.
    }
    + apply SP_Here.
    + apply Operators_Properties.clos_rt_rt1n.
      apply arbitrary_eval_multi_ceval'.
      exact H. apply SP_Here.
      auto.
}
{
  intros.
  clear arbitrary_eval_multi_ceval'.
  induction H; subst.
  - apply rt_refl.
  - inversion H2; subst.
    apply ceval_multi_ceval' in H7.
    simpl in *.
    eapply rt_trans.
    {
      apply rt_step.
      eapply ME_re; auto.
      - exact H.
    }
    eapply rt_trans.
    {
      apply multi_ceval'_elevate.
      exact H7.
    }
    eapply rt_trans.
    {
      apply rt_step.
      apply ME_ex.
      + exact H0.
      + simpl. omega.
    }
    exact IHarbitrary_eval.
}
Admitted.


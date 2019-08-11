Require Import Coq.Lists.List.
Require Import AST_woc.
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
  | LSeq (c1 : label) (c2 : label)
  | LIf (b : bexp) (c1 : label) (c2 : label)
  | LWhile (b : bexp) (c : label)
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


(** Definition of basic ceval' *)
Inductive ceval' : func_context -> com -> label -> label -> state -> state -> Prop :=
  | E'_Skip : forall fc st,
      ceval' fc CSkip LPure LPure st st
  | E'_Ass : forall fc st X a n,
      aeval st a = n ->
      ceval' fc (CAss X a) LPure LPure st (update_state st X n)

  | E'_Seq : forall fc c1 c2 l1 l2 l3 l4 st1 st2 st3,
      valid_label l1 ->
      is_pure l2 ->
      is_pure l3 ->
      valid_label l4 ->
      ceval' fc c1 l1 l2 st1 st3 ->
      ceval' fc c2 l3 l4 st3 st2 ->
      ceval' fc (CSeq c1 c2) (LSeq l1 l3) (LSeq l2 l4) st1 st2
  | E'_Seq1 : forall fc c1 c2 l1 l2 st1 st2,
      valid_label l1 ->
      single_point l2 ->
      ceval' fc c1 l1 l2 st1 st2 ->
      ceval' fc (CSeq c1 c2)
        (LSeq l1 (com_to_label_pure c2)) (LSeq l2 (com_to_label_pure c2)) st1 st2
  | E'_Seq2 : forall fc c1 c2 l1 l2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c2 l1 l2 st1 st2 ->
      ceval' fc (CSeq c1 c2)
        (LSeq (com_to_label_pure c1) l1) (LSeq (com_to_label_pure c1) l2) st1 st2

  | E'_IfTrue : forall fc b c1 c2 l1 l2 st1 st2,
      is_pure l1 ->
      valid_label l2 ->
      beval st1 b = true ->
      ceval' fc c1 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b l1 (com_to_label_pure c2)) (LIf b l2 (com_to_label_pure c2)) st1 st2
  | E'_IfFalse : forall fc b c1 c2 l1 l2 st1 st2,
      is_pure l1 ->
      valid_label l2 ->
      beval st1 b = false ->
      ceval' fc c2 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b (com_to_label_pure c1) l1) (LIf b (com_to_label_pure c1) l2) st1 st2
  | E'_If1 : forall fc b c1 c2 l1 l2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c1 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b l1 (com_to_label_pure c2)) (LIf b l2 (com_to_label_pure c2)) st1 st2
  | E'_If2 : forall fc b c1 c2 l1 l2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c2 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b (com_to_label_pure c1) l1) (LIf b (com_to_label_pure c1) l2) st1 st2

  | E'_WhileFalse : forall fc b c st,
      beval st b = false ->
      ceval' fc (CWhile b c)
        (LWhile b (com_to_label_pure c)) (LWhile b (com_to_label_pure c)) st st
  | E'_WhileTrue1 : forall fc b c l1 l2 st1 st2,
      is_pure l1 ->
      single_point l2 ->
      beval st1 b = true ->
      ceval' fc c l1 l2 st1 st2 ->
      ceval' fc (CWhile b c) (LWhile b l1) (LWhile b l2) st1 st2
  | E'_WhileTrue2 : forall fc b c l1 l2 st1 st2 st3,
      is_pure l1 ->
      valid_label l2 ->
      beval st1 b = true ->
      ceval' fc c (com_to_label_pure c) (com_to_label_pure c) st1 st3 ->
      ceval' fc (CWhile b c) l1 l2 st3 st2 ->
      ceval' fc (CWhile b c) l1 l2 st1 st2
  | E'_WhileSeg1 : forall fc b c l1 l2 st1 st2,
      single_point l1 ->
      single_point l2 ->
      ceval' fc c l1 l2 st1 st2 ->
      ceval' fc (CWhile b c) (LWhile b l1) (LWhile b l2) st1 st2
  | E'_WhileSeg2 : forall fc b c l1 l2 st1 st2 st3,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c l1 (com_to_label_pure c) st1 st3 ->
      ceval' fc (CWhile b c) (LWhile b (com_to_label_pure c)) l2 st3 st2 ->
      ceval' fc (CWhile b c) l1 l2 st1 st2

  | E'_Reentry1c : forall fc st,
      ceval' fc CReentry LPure LHere st st
  | E'_Reentryr2 : forall fc st,
      ceval' fc CReentry LHere LPure st st
.

Lemma ceval'_valid_label : 
  forall fc c l1 l2 st1 st2,
  ceval' fc c l1 l2 st1 st2 ->
  valid_label l1 /\ valid_label l2.
Proof.
  intros.
  inversion H; subst;
  try (split; left; apply IP_Pure);
  try pose proof com_to_label_pure_is_pure c1 as Hpc1;
  try pose proof com_to_label_pure_is_pure c2 as Hpc2;
  try pose proof com_to_label_pure_is_pure c0 as Hpc0.
  - destruct H0, H3.
    split; left; apply IP_Seq; assumption.
    split. left; apply IP_Seq; assumption.
           right; apply SP_Seq2; assumption.
    split. right; apply SP_Seq1; assumption.
           left; apply IP_Seq; assumption.
    split. right; apply SP_Seq1; assumption.
           right; apply SP_Seq2; assumption.
  - split.
    destruct H0.
    left; apply IP_Seq; assumption.
    right; apply SP_Seq1; assumption.
    right; apply SP_Seq1; assumption.
  - split.
    right; apply SP_Seq2; assumption.
    destruct H1.
    left; apply IP_Seq; assumption.
    right; apply SP_Seq2; assumption.
  - split.
    left; apply IP_If; assumption.
    destruct H1.
    left; apply IP_If; assumption.
    right; apply SP_If1; assumption.
  - split.
    left; apply IP_If; assumption.
    destruct H1.
    left; apply IP_If; assumption.
    right; apply SP_If2; assumption.
  - split.
    right; apply SP_If1; assumption.
    destruct H1.
    left; apply IP_If; assumption.
    right; apply SP_If1; assumption.
  - split.
    right; apply SP_If2; assumption.
    destruct H1.
    left; apply IP_If; assumption.
    right; apply SP_If2; assumption.
  - split;
    left; apply IP_While; assumption.
  - split.
    left; apply IP_While; assumption.
    right; apply SP_While; assumption.
  - split.
    left; assumption.
    assumption.
  - split; right; apply SP_While; assumption.
  - split.
    right; assumption.
    assumption.
  - split.
    left; apply IP_Pure.
    right; apply SP_Here.
  - split.
    right; apply SP_Here.
    left; apply IP_Pure.
Qed.
(** [] *)


(** Bridging basic ceval' to multi_ceval' *)
Definition restk : Type := list (com * (option label) * state).

Inductive middle_ceval' : func_context -> public_funcs -> restk -> restk -> Prop :=
  | ME_r_pure : forall fc c l1 st1 st2 stk lf,
      ceval' fc c l1 (com_to_label_pure c) st1 st2 ->
      middle_ceval' fc lf ((c, Some l1, st1) :: stk) ((c, None, st2) :: stk)
  | ME_r_single : forall fc c l1 l2 st1 st2 stk lf,
      single_point l2 ->
      ceval' fc c l1 l2 st1 st2 ->
      middle_ceval' fc lf ((c, Some l1, st1) :: stk) ((c, Some l2, st2) :: stk)
  | ME_re : forall fc c1 c2 l1 loc1 loc2 glb stk lf f,
      In f lf ->
      c2 = snd (fc f) ->
      single_point l1 ->
      middle_ceval' fc lf ((c1, Some l1, (loc1, glb)) :: stk)
        ((c2, Some (com_to_label_pure c2), (loc2, glb)) :: (c1, Some l1, (loc1, glb)) :: stk)
  | ME_ex : forall fc c1 c2 l2 loc1 loc2 glb1 glb2 stk lf,
      single_point l2 ->
      middle_ceval' fc lf
        ((c1, None, (loc1, glb1)) :: (c2, Some l2, (loc2, glb2)) :: stk)
        ((c2, Some l2, (loc2, glb1)) :: stk).

Print clos_trans.
Search clos_trans_1n.
(*
Inductive clos_trans (A : Type) (R : relation A) (x : A) : A -> Prop :=
    t_step : forall y : A, R x y -> clos_trans A R x y
  | t_trans : forall y z : A, clos_trans A R x y -> clos_trans A R y z -> clos_trans A R x z
*)
Definition multi_ceval' (fc : func_context) (lf : public_funcs) : restk -> restk -> Prop :=
  clos_trans restk (middle_ceval' fc lf).

Lemma middle_ceval'_some : forall fc c l1 l2 st1 st2 lf,
  middle_ceval' fc lf ((c, Some l1, st1) :: nil) ((c, Some l2, st2) :: nil) ->
  ceval' fc c l1 l2 st1 st2.
Proof.
  intros.
  inversion H; subst.
  exact H9.
Qed.

Lemma middle_ceval'_none : forall fc c l1 st1 st2 lf,
  middle_ceval' fc lf ((c, Some l1, st1) :: nil) ((c, None, st2) :: nil) ->
  ceval' fc c l1 (com_to_label_pure c) st1 st2.
Proof.
  intros.
  inversion H; subst.
  exact H3.
Qed.
(** [] *)


(** Equivalence between ceval & multi_ceval' *)
Check ceval.
Check multi_ceval'.
Print ceval.

Definition ceval'_derive_multi_ceval : Prop :=
  forall fc lf c st1 st2,
  ceval fc lf c st1 st2 ->
  multi_ceval' fc lf
    ((c, Some (com_to_label_pure c), st1) :: nil)
    ((c, None, st2) :: nil).

Definition arbitrary_eval_derive_multi_ceval : Prop :=
  forall fc lf loc glb1 glb2 lb c stk,
  single_point lb ->
  arbitrary_eval fc lf loc glb1 glb2 ->
  multi_ceval' fc lf
    ((c, Some lb, (loc, glb1)) :: stk)
    ((c, Some lb, (loc, glb2)) :: stk).

(** Seq Head *)
Lemma middle_ceval'_seq_head1:
  forall l1 fc lf c2 st1 st2 stk c1,
  single_point l1 ->
  middle_ceval' fc lf
    ((c2, Some l1, st1) :: stk)
    ((c2, None, st2) :: stk) ->
  middle_ceval' fc lf
    ((CSeq c1 c2, Some (LSeq (com_to_label_pure c1) l1), st1) :: stk)
    ((CSeq c1 c2, None, st2) :: stk).
Proof.
  intros.
  inversion H0; subst.
  eapply E'_Seq2 in H4.
  - apply ME_r_pure.
    exact H4.
  - exact H.
  - apply com_to_label_pure_valid.
Qed.

Lemma increase_one_side {A : Type}:
  forall (a : A) l l',
  ~(l' ++ a :: l = l).
Proof.
  unfold not.
  intros.
  assert (length (l' ++ a :: l) = length l).
  rewrite H. auto.
  rewrite app_length in H0.
  simpl in H0.
  omega.
Qed.

Lemma increase_one_side1 {A : Type}:
  forall (a b : A) l l',
  a <> b ->
  ~(l' ++ a :: l = b :: l).
Proof.
  unfold not.
  intros.
  destruct l'.
  - inversion H0.
    auto.
  - assert (length ((a0 :: l') ++ a :: l) = length (b :: l)).
    rewrite H0. auto.
    rewrite app_length in H1.
    simpl in H1.
    omega.
Qed.

Lemma middle_ceval'_seq_head2:
  forall l1 l2 fc lf c2 st1 st2 stk c1,
  single_point l1 ->
  middle_ceval' fc lf
    ((c2, Some l1, st1) :: stk)
    ((c2, Some l2, st2) :: stk) ->
  middle_ceval' fc lf
    ((CSeq c1 c2, Some (LSeq (com_to_label_pure c1) l1), st1) :: stk)
    ((CSeq c1 c2, Some (LSeq (com_to_label_pure c1) l2), st2) :: stk).
Proof.
  intros.
  inversion H0; subst.
  eapply E'_Seq2 in H10.
  - apply ME_r_single.
    apply SP_Seq2.
    apply com_to_label_pure_is_pure.
    exact H5.
    exact H10.
  - exact H.
  - right.
    exact H5.
  - pose proof increase_one_side (snd (fc f), Some l1, (loc1, glb)) stk nil.
    simpl in H1.
    congruence.
Qed.

Lemma middle_ceval'_seq_head_some:
  forall fc lf c1 c2 l1 l2 st1 st2 stk1 stk2,
  single_point l1 ->
  middle_ceval' fc lf
    (stk1 ++ (c2, Some l1, st1) :: nil)
    (stk2 ++ (c2, Some l2, st2) :: nil) ->
  middle_ceval' fc lf
    (stk1 ++ (CSeq c1 c2, Some (LSeq (com_to_label_pure c1) l1), st1) :: nil)
    (stk2 ++ (CSeq c1 c2, Some (LSeq (com_to_label_pure c1) l2), st2) :: nil).
Proof.
  intros.
  destruct stk1, stk2; simpl in *.
  - inversion H0; subst.
    apply middle_ceval'_seq_head2; assumption.
  - inversion H0; subst.
    + assert (@length (com * option label * state) nil = length (stk2 ++ (c2, Some l2, st2) :: nil)).
      rewrite H9 at 1. auto.
      rewrite app_length in H1.
      simpl in H1. omega.
    + assert (@length (com * option label * state) nil = length (stk2 ++ (c2, Some l2, st2) :: nil)).
      rewrite H9 at 1. auto.
      rewrite app_length in H1.
      simpl in H1. omega.
    + destruct stk2; simpl in *.
      2:{
        assert (length ((c2, Some l1, (loc1, glb)) :: nil) = length (p :: stk2 ++ (c2, Some l2, st2) :: nil)).
        rewrite <- H9. auto.
        simpl in H1.
        rewrite app_length in H1.
        simpl in H1.
        omega.
      }
      rewrite <- app_nil_l in H9 at 1.
      rewrite <- app_nil_l in H9.
      apply app_inj_tail in H9.
      destruct H9 as [_ ?].
      inversion H1; subst. clear H1.
      eapply ME_re.
      * exact H6.
      * auto.
      * apply SP_Seq2.
        apply com_to_label_pure_is_pure.
        exact H11.
  - inversion H0; subst.
    + assert (length (stk1 ++ (c2, Some l1, st1) :: nil) = @length (com * option label * state) nil).
      rewrite H9. auto.
      rewrite app_length in H1.
      simpl in H1.
      omega.
    + destruct stk1; simpl in *.
      2:{
        assert (length ((c2, Some l2, (loc2, glb2)) :: nil) = length (p :: stk1 ++ (c2, Some l1, st1) :: nil)).
        rewrite <- H5. auto.
        simpl in H1.
        rewrite app_length in H1.
        simpl in H1.
        omega.
      }
      rewrite <- app_nil_l in H5 at 1.
      rewrite <- app_nil_l in H5.
      apply app_inj_tail in H5.
      destruct H5 as [_ ?].
      inversion H1; subst; clear H1.
      eapply ME_ex.
      apply SP_Seq2.
      apply com_to_label_pure_is_pure.
      exact H4.
  - inversion H0; subst.
    + apply app_inj_tail in H7.
      destruct H7.
      inversion H2; subst.
      apply ME_r_pure.
      exact H4.
    + apply app_inj_tail in H7.
      destruct H7.
      inversion H2; subst.
      apply ME_r_single.
      exact H6.
      exact H8.
    + rewrite app_comm_cons in H6.
      apply app_inj_tail in H6.
      destruct H6.
      inversion H2; subst; clear H2.
      eapply ME_re.
      * exact H7.
      * auto.
      * exact H9.
    + rewrite app_comm_cons in H5.
      apply app_inj_tail in H5.
      destruct H5.
      inversion H2; subst; clear H2.
      apply ME_ex.
      exact H4.
Qed.

Lemma middle_ceval'_seq_head_none:
  forall fc lf c1 c2 l1 st1 st2 stk1 stk2,
  single_point l1 ->
  middle_ceval' fc lf
    (stk1 ++ (c2, Some l1, st1) :: nil)
    (stk2 ++ (c2, None, st2) :: nil) ->
  middle_ceval' fc lf
    (stk1 ++ (CSeq c1 c2, Some (LSeq (com_to_label_pure c1) l1), st1) :: nil)
    (stk2 ++ (CSeq c1 c2, None, st2) :: nil).
Proof.
  intros.
  destruct stk1, stk2; simpl in *.
  - inversion H0; subst.
    apply middle_ceval'_seq_head1; assumption.
  - inversion H0; subst.
    + assert (@length (com * option label * state) nil = length (stk2 ++ (c2, None, st2) :: nil)).
      rewrite H9 at 1. auto.
      rewrite app_length in H1.
      simpl in H1. omega.
    + assert (@length (com * option label * state) nil = length (stk2 ++ (c2, None, st2) :: nil)).
      rewrite H9 at 1. auto.
      rewrite app_length in H1.
      simpl in H1. omega.
    + destruct stk2; simpl in *.
      2:{
        assert (length ((c2, Some l1, (loc1, glb)) :: nil) = length (p :: stk2 ++ (c2, None, st2) :: nil)).
        rewrite <- H9. auto.
        simpl in H1.
        rewrite app_length in H1.
        simpl in H1.
        omega.
      }
      rewrite <- app_nil_l in H9 at 1.
      rewrite <- app_nil_l in H9.
      apply app_inj_tail in H9.
      destruct H9 as [_ ?].
      inversion H1.
  - inversion H0; subst.
    + assert (length (stk1 ++ (c2, Some l1, st1) :: nil) = @length (com * option label * state) nil).
      rewrite H8. auto.
      rewrite app_length in H1.
      simpl in H1.
      omega.
  - inversion H0; subst.
    + apply app_inj_tail in H7.
      destruct H7.
      inversion H2.
    + apply app_inj_tail in H7.
      destruct H7.
      inversion H2.
    + rewrite app_comm_cons in H6.
      apply app_inj_tail in H6.
      destruct H6.
      inversion H2.
    + rewrite app_comm_cons in H5.
      apply app_inj_tail in H5.
      destruct H5.
      inversion H2.
Qed.

Lemma cons_insert_nil {A : Type} :
  forall (a : A) l,
  a :: l = a :: nil ++ l.
Proof.
  intros.
  auto.
Qed.

Lemma multi_ceval'_seq_head:
  forall l2 fc lf c2 st4 st3 c1,
  single_point l2 ->
  clos_trans restk (middle_ceval' fc lf)
      ((c2, Some l2, st4) :: nil)
      ((c2, None, st3) :: nil) ->
  clos_trans restk (middle_ceval' fc lf)
      ((CSeq c1 c2, Some (LSeq (com_to_label_pure c1) l2), st4) :: nil)
      ((CSeq c1 c2, None, st3) :: nil).
Proof.
  intros.
  set (stk := @nil (com * option label * state)).
  unfold stk.
  change ((c2, Some l2, st4) :: nil) with (stk ++ ((c2, Some l2, st4) :: nil)) in H0.
  change ((CSeq c1 c2, Some (LSeq (com_to_label_pure c1) l2), st4) :: nil) with (stk ++ ((CSeq c1 c2, Some (LSeq (com_to_label_pure c1) l2), st4) :: nil)).
  clearbody stk.
  remember (stk ++ ((c2, Some l2, st4) :: nil)) as l.
  remember ((c2, None, st3) :: nil) as l'.
  apply Operators_Properties.clos_trans_t1n in H0.
  revert Heql.
  revert stk st4.
  revert c1.
  generalize dependent l2.
  induction H0; intros; subst.
  - rewrite <- app_nil_l in H.
    eapply middle_ceval'_seq_head_none, t_step in H.
    simpl in H. exact H. exact H0.
  - inversion H; subst.
    + specialize (IHclos_trans_1n (eq_refl _) l2 H1).
      destruct stk.
      * destruct stk0.
        inversion H0; inversion H3.
        assert (length ((c, Some l1, st1) :: p :: stk0) = length (nil ++ (c2, Some l2, st4) :: nil)).
        rewrite H2. auto.
        simpl in H3. omega.
      * simpl in H2.
        inversion H2; subst; clear H2.
        simpl in *.
        pose proof IHclos_trans_1n c1 ((c, None, st2) :: stk) st4.
        specialize (H2 (eq_refl _)).
        repeat rewrite app_comm_cons in H.
        eapply middle_ceval'_seq_head_some, t_step in H.
        simpl in *.
        eapply t_trans.
        exact H. exact H2. exact H1.
    + destruct stk.
      * destruct stk0.
        2:{
          pose proof (eq_refl (length ((c, Some l1, st1) :: p :: stk0))).
          rewrite H2 in H4 at 1.
          simpl in H4. omega.
        }
        simpl in *.
        inversion H2; subst; clear H2.
        pose proof (IHclos_trans_1n (eq_refl _) l0 H3 c1 nil st2 (eq_refl _)).
        simpl in *.
        eapply middle_ceval'_seq_head2, t_step in H.
        eapply t_trans.
        exact H. exact H2. exact H1.
      * simpl in H2.
        inversion H2; subst; clear H2.
        pose proof (IHclos_trans_1n (eq_refl _) l2 H1 c1 ((c, Some l0, st2) :: stk) st4 (eq_refl _)).
        rewrite app_comm_cons in H.
        eapply middle_ceval'_seq_head_some, t_step in H.
        eapply t_trans.
        exact H. exact H2. exact H1.
    + destruct stk.
      * destruct stk0.
        2:{
          pose proof (eq_refl (length ((c0, Some l1, (loc1, glb)) :: p :: stk0))).
          rewrite H2 in H4 at 1.
          simpl in H4. omega.
        }
        simpl in *.
        inversion H2; subst; clear H2.
        pose proof IHclos_trans_1n (eq_refl _) l2 H1 c1 ((snd (fc f), Some (com_to_label_pure (snd (fc f))), (loc2, glb)) :: nil) (loc1, glb) (eq_refl _).
        assert ((c2, Some l2, (loc1, glb)) :: nil = nil ++ (c2, Some l2, (loc1, glb)) :: nil). auto.
        pose proof middle_ceval'_seq_head_some fc lf c1 c2 l2 l2 (loc1, glb) (loc1, glb) nil. simpl in H5.
        assert ((snd (fc f), Some (com_to_label_pure (snd (fc f))), (loc2, glb)) :: (c2, Some l2, (loc1, glb)) :: nil = ((snd (fc f), Some (com_to_label_pure (snd (fc f))), (loc2, glb)) :: nil) ++ (c2, Some l2, (loc1, glb)) :: nil). auto.
        rewrite H6 in H; clear H6.
        eapply H5, t_step in H.
        eapply t_trans.
        exact H. exact H2. exact H1.
      * simpl in H2; inversion H2; subst; clear H2.
        pose proof IHclos_trans_1n (eq_refl _) l2 H1 c1 ((snd (fc f), Some (com_to_label_pure (snd (fc f))), (loc2, glb)) :: (c0, Some l1, (loc1, glb)) :: stk) st4 (eq_refl _).
        rewrite app_comm_cons in H. rewrite app_comm_cons in H.
        eapply middle_ceval'_seq_head_some, t_step in H.
        eapply t_trans.
        exact H. exact H2. exact H1.
  + destruct stk.
    simpl in H2.
    pose proof eq_refl (length ((c2, Some l2, st4) :: nil)).
    rewrite <- H2 in H3 at 1.
    simpl in H3. omega.
    simpl in H2.
    destruct stk.
    * simpl in H2.
      inversion H2; subst; clear H2.
      pose proof IHclos_trans_1n (eq_refl _) l2 H1 c1 nil (loc2, glb1) (eq_refl _).
      simpl in H2.
      rewrite <- app_nil_l in H.
      eapply middle_ceval'_seq_head_some, t_step in H.
      eapply t_trans.
      exact H. exact H2. exact H1.
    * simpl in *.
      inversion H2; subst; clear H2.
      pose proof IHclos_trans_1n (eq_refl _) l2 H1 c1 ((c3, Some l0, (loc2, glb1)) :: stk) st4 (eq_refl _).
      repeat rewrite app_comm_cons in H.
      eapply middle_ceval'_seq_head_some, t_step in H.
      eapply t_trans.
      exact H. exact H2. exact H1.
Qed.
(** Seq Head *)

(** Seq Tail *)
Lemma middle_ceval'_seq_tail:
  forall fc lf c1 st1 stk1 stk2 l0 l1 st0 c2,
  single_point l1 ->
  middle_ceval' fc lf
    (stk1 ++ (c1, Some l0, st1) :: nil)
    (stk2 ++ (c1, Some l1, st0) :: nil) ->
  middle_ceval' fc lf
    (stk1 ++ (CSeq c1 c2, Some (LSeq l0 (com_to_label_pure c2)), st1) :: nil)
    (stk2 ++ (CSeq c1 c2, Some (LSeq l1 (com_to_label_pure c2)), st0) :: nil).
Proof.
  intros.
  destruct stk1, stk2; simpl in *.
  - inversion H0; subst.
    eapply E'_Seq1 in H10.
    apply ME_r_single.
    apply SP_Seq1.
    exact H.
    apply com_to_label_pure_is_pure.
    exact H10.
    apply ceval'_valid_label in H10.
    tauto.
    exact H.
  - inversion H0; subst.
    + pose proof eq_refl (@length (com * option label * state) nil).
      rewrite H9 in H1 at 1.
      rewrite app_length in H1.
      simpl in H1. omega.
    + pose proof eq_refl (@length (com * option label * state) nil).
      rewrite H9 in H1 at 1.
      rewrite app_length in H1.
      simpl in H1. omega.
    + destruct stk2; simpl in *.
      * inversion H9; subst; clear H9.
        eapply ME_re.
        exact H6.
        apply eq_refl.
        apply SP_Seq1.
        exact H11.
        apply com_to_label_pure_is_pure.
      * pose proof eq_refl (length (p :: stk2 ++ (c1, Some l1, st0) :: nil)).
        rewrite <- H9 in H1 at 1.
        simpl in H1.
        rewrite app_length in H1.
        simpl in H1. omega.
  - inversion H0; subst.
    + pose proof eq_refl (@length (com * option label * state) nil).
      rewrite <- H9 in H1 at 1.
      rewrite app_length in H1.
      simpl in H1. omega.
    + destruct stk1; simpl in *.
      * inversion H5; subst.
        apply ME_ex.
        apply SP_Seq1.
        exact H4.
        apply com_to_label_pure_is_pure.
      * pose proof eq_refl (length ((c1, Some l1, (loc2, glb2)) :: nil)).
        rewrite H5 in H1 at 1.
        simpl in H1.
        rewrite app_length in H1.
        simpl in H1. omega.
  - inversion H0; subst.
    + apply app_inj_tail in H7;
      destruct H7; inversion H2; subst; clear H2.
      eapply ME_r_pure in H4.
      apply H4.
    + apply app_inj_tail in H7;
      destruct H7; inversion H2; subst; clear H2.
      eapply ME_r_single in H8.
      apply H8.
      exact H6.
    + destruct stk2; simpl in *.
      * pose proof eq_refl (length ((c1, Some l1, st0) :: nil)).
        rewrite <- H6 in H1 at 1.
        simpl in H1.
        rewrite app_length in H1.
        simpl in H1. omega.
      * inversion H6; subst; clear H6.
        apply app_inj_tail in H3 as [? ?].
        inversion H2; subst; clear H2.
        eapply ME_re.
        exact H7.
        auto.
        exact H9.
    + destruct stk1; simpl in *.
      * pose proof eq_refl (length ((c1, Some l0, st1) :: nil)).
        rewrite <- H5 in H1 at 1.
        simpl in H1.
        rewrite app_length in H1.
        simpl in H1. omega.
      * inversion H5; subst; clear H5.
        apply app_inj_tail in H3 as [? ?].
        inversion H2; subst; clear H2.
        eapply ME_ex.
        exact H4.
Qed.

Lemma multi_ceval'_seq_tail:
  forall fc lf c1 c2 l1 st1 st0,
  single_point l1 ->
  clos_trans restk (middle_ceval' fc lf)
    ((c1, Some (com_to_label_pure c1), st1) :: nil)
    ((c1, Some l1, st0) :: nil) ->
  clos_trans restk (middle_ceval' fc lf)
    ((CSeq c1 c2, Some (LSeq (com_to_label_pure c1) (com_to_label_pure c2)), st1) :: nil)
    ((CSeq c1 c2, Some (LSeq l1 (com_to_label_pure c2)), st0) :: nil).
Proof.
  intros.
  set (stk := @nil (com * option label * state)).
  unfold stk.
  change ((c1, Some l1, st0) :: nil) with (stk ++ ((c1, Some l1, st0) :: nil)) in H0.
  change ((CSeq c1 c2, Some (LSeq l1 (com_to_label_pure c2)), st0) :: nil) with (stk ++ ((CSeq c1 c2, Some (LSeq l1 (com_to_label_pure c2)), st0) :: nil)).
  clearbody stk.
  remember (stk ++ ((c1, Some l1, st0) :: nil)) as l.
  remember ((c1, Some (com_to_label_pure c1), st1) :: nil) as l'.
  apply Operators_Properties.clos_trans_tn1 in H0.
  revert Heql.
  revert stk st0.
  revert c2.
  generalize dependent l1.
  induction H0; intros; subst.
  - change ((c1, Some (com_to_label_pure c1), st1) :: nil) with (nil ++ (c1, Some (com_to_label_pure c1), st1) :: nil) in H.
    eapply middle_ceval'_seq_tail, t_step in H.
    simpl in H. exact H. exact H0.
  - inversion H; subst.
    + destruct stk; simpl in *; inversion H2; subst; clear H2.
      pose proof IHclos_trans_n1 l1 H1 c2 ((c, Some l0, st2) :: stk) st0 (eq_refl _).
      repeat rewrite app_comm_cons in H.
      eapply middle_ceval'_seq_tail, t_step in H.
      eapply t_trans.
      exact H2. exact H. exact H1.
    + destruct stk; simpl in *.
      * inversion H2; subst; clear H2.
        change ((c1, Some l0, st2) :: nil) with (nil ++ (c1, Some l0, st2) :: nil) in H.
        change ((c1, Some l1, st0) :: nil) with (nil ++ (c1, Some l1, st0) :: nil) in H.
        eapply middle_ceval'_seq_tail, t_step in H.
        epose proof IHclos_trans_n1 l0 _ c2 nil st2 (eq_refl _).
        simpl in *.
        eapply t_trans.
        exact H2. exact H. exact H3.
      * inversion H2; subst; clear H2.
        pose proof IHclos_trans_n1 l1 H1 c2 ((c, Some l0, st2) :: stk) st0 (eq_refl _).
        repeat rewrite app_comm_cons in H.
        eapply middle_ceval'_seq_tail, t_step in H.
        simpl in *.
        eapply t_trans.
        exact H2. exact H. exact H1.
    + destruct stk; simpl in *.
      * pose proof eq_refl (length ((c1, Some l1, st0) :: nil)).
        rewrite <- H2 in H4 at 1.
        simpl in H4. omega.
      * inversion H2; subst.
        destruct stk; simpl in *.
        {
          inversion H6; subst.
          clear H2 H6.
          pose proof IHclos_trans_n1 l1 H1 c2 nil (loc1, glb) (eq_refl _).
          rewrite <- (@app_nil_l (_ * _ * _)) in H at 1.
          pose proof cons_insert_nil (snd (fc f), Some (com_to_label_pure (snd (fc f))), (loc2, glb)).
          rewrite H4, app_comm_cons in H; clear H4.
          eapply middle_ceval'_seq_tail, t_step in H.
          eapply t_trans.
          exact H2. exact H. exact H1.
        }
        {
          inversion H6; subst; clear H2 H6.
          pose proof IHclos_trans_n1 l1 H1 c2 ((c0, Some l0, (loc1, glb)) :: stk) st0 (eq_refl _).
          repeat rewrite app_comm_cons in H.
          eapply middle_ceval'_seq_tail, t_step in H.
          eapply t_trans.
          exact H2. exact H. exact H1.
        }
    + destruct stk; simpl in *.
      * inversion H2; subst; clear H2.
        pose proof IHclos_trans_n1 l1 H1 c2 ((c0, None, (loc1, glb1)) :: nil) (loc2, glb2) (eq_refl _).
        rewrite <- app_nil_l in H.
        rewrite cons_insert_nil, app_comm_cons in H.
        eapply middle_ceval'_seq_tail, t_step in H.
        eapply t_trans.
        exact H2. exact H. exact H1.
      * inversion H2; subst; clear H2.
        pose proof IHclos_trans_n1 l1 H1 c2 ((c0, None, (loc1, glb1)) :: (c3, Some l2, (loc2, glb2)) :: stk) st0 (eq_refl _).
        repeat rewrite app_comm_cons in H.
        eapply middle_ceval'_seq_tail, t_step in H.
        eapply t_trans.
        exact H2. exact H. exact H1.
Unshelve.
  inversion H0; inversion H2; assumption.
Qed.
(** Seq Tail *)

Theorem ceval'_derive_multi_ceval_correct : ceval'_derive_multi_ceval.
Proof.
  unfold ceval'_derive_multi_ceval.
  intros.
  induction H.
  - simpl.
    apply t_step, ME_r_pure.
    simpl. apply E'_Skip.
  - simpl.
    apply t_step, ME_r_pure.
    simpl. apply E'_Ass, H.
  - simpl.
    apply Operators_Properties.clos_trans_tn1 in IHceval1.
    apply Operators_Properties.clos_trans_t1n in IHceval2.
    inversion IHceval1; subst; inversion IHceval2; subst.
    + apply middle_ceval'_none in H1.
      apply middle_ceval'_none in H2.
      epose proof E'_Seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2.
      apply t_step, ME_r_pure.
      exact H3.
    + apply middle_ceval'_none in H1.
      inversion H2; subst.
      * inversion H3; inversion H4.
      * assert (valid_label l2) as Htmp. right. assumption.
      pose proof E'_Seq fc c1 c2 (com_to_label_pure c1) (com_to_label_pure c1) (com_to_label_pure c2) l2 _ _ _ (com_to_label_pure_valid _) (com_to_label_pure_is_pure _) (com_to_label_pure_is_pure _) Htmp H1 H12.
        clear Htmp.
        apply Operators_Properties.clos_t1n_trans in H3.
        eapply ME_r_single in H4.
        2:{
          apply SP_Seq2, H11.
          apply com_to_label_pure_is_pure.
        }
        apply Operators_Properties.clos_t1n_trans.
        eapply t1n_trans.
        apply H4.
        clear H4.
        eapply multi_ceval'_seq_head in H3.
        apply Operators_Properties.clos_trans_t1n.
        exact H3.
        exact H11.
      * pose proof com_to_label_pure_no_point c2.
        tauto.
    + apply middle_ceval'_none in H3.
      inversion H1; subst.
      * pose proof ceval'_valid_label _ _ _ _ _ _ H8 as [Htmp _].
        pose proof E'_Seq _ _ _ _ _ _ _ _ _ _ Htmp (com_to_label_pure_is_pure _) (com_to_label_pure_is_pure _) (com_to_label_pure_valid _) H8 H3.
        clear Htmp.
        apply Operators_Properties.clos_tn1_trans in H2.
        eapply ME_r_pure, t_step in H4.
        eapply multi_ceval'_seq_tail in H2.
        eapply t_trans.
        apply H2. apply H4.
        apply Operators_Properties.clos_trans_tn1 in H2.
        inversion H2; inversion H5; assumption.
    + inversion H1; subst; inversion H3; subst.
      * inversion H4; inversion H5.
      * pose proof ceval'_valid_label _ _ _ _ _ _ H9 as [Htmp1 _].
        pose proof ceval'_valid_label _ _ _ _ _ _ H14 as [_ Htmp2].
        pose proof E'_Seq _ _ _ _ _ _ _ _ _ _ Htmp1 (com_to_label_pure_is_pure _) (com_to_label_pure_is_pure _) Htmp2 H9 H14.
        apply Operators_Properties.clos_tn1_trans in H2.
        apply Operators_Properties.clos_t1n_trans in H4.
        eapply multi_ceval'_seq_tail in H2.
        eapply multi_ceval'_seq_head in H4.
        eapply ME_r_single, t_step in H5.
        {
          eapply t_trans.
          apply H2.
          eapply t_trans.
          apply H5.
          apply H4.
        }
        {
          apply SP_Seq2.
          apply com_to_label_pure_is_pure.
          assumption.
        }
        assumption.
        inversion H2.
        {
          inversion H6; subst.
          assumption.
        }
        apply Operators_Properties.clos_trans_tn1 in H2.
        inversion H2; inversion H10; assumption.
      * pose proof com_to_label_pure_no_point c2.
        tauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Unshelve.
  left. apply com_to_label_pure_is_pure.
  apply com_to_label_pure_is_pure.
  apply com_to_label_pure_is_pure.
  left. apply com_to_label_pure_is_pure.
Admitted.
(*   remember (snd (fc f)) as c.
  revert f Heqc.
  induction H; intros.
  - simpl.
    apply t_step, ME_r.
    rewrite <- Heqc.
    apply E'_Skip.
  - simpl.
    apply t_step, ME_r.
    rewrite <- Heqc.
    apply E'_Ass, H.
  - simpl.
Admitted. *)
(** [] *)




















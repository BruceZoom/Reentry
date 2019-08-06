Require Import Coq.Lists.List.
Require Import AST_woc.

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

Fixpoint com_to_lable_pure (c : com) : label :=
  match c with
  | CSeq c1 c2 => LSeq (com_to_lable_pure c1) (com_to_lable_pure c2)
  | CIf b c1 c2 => LIf b (com_to_lable_pure c1) (com_to_lable_pure c2)
  | CWhile b c => LWhile b (com_to_lable_pure c)
  | _ => LPure
  end.

Lemma com_to_lable_pure_is_pure : forall c,
  is_pure (com_to_lable_pure c).
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

Lemma com_to_lable_pure_valid : forall c,
  valid_label (com_to_lable_pure c).
Proof.
  intros.
  unfold valid_label.
  left.
  apply com_to_lable_pure_is_pure.
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

Lemma com_to_lable_pure_no_point : forall c,
  ~single_point (com_to_lable_pure c).
Proof.
  intros.
  apply pure_no_point.
  apply com_to_lable_pure_is_pure.
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
        (LSeq l1 (com_to_lable_pure c2)) (LSeq l2 (com_to_lable_pure c2)) st1 st2
  | E'_Seq2 : forall fc c1 c2 l1 l2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c2 l1 l2 st1 st2 ->
      ceval' fc (CSeq c1 c2)
        (LSeq (com_to_lable_pure c1) l1) (LSeq (com_to_lable_pure c1) l2) st1 st2

  | E'_IfTrue : forall fc b c1 c2 l1 l2 st1 st2,
      is_pure l1 ->
      valid_label l2 ->
      beval st1 b = true ->
      ceval' fc c1 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b l1 (com_to_lable_pure c2)) (LIf b l2 (com_to_lable_pure c2)) st1 st2
  | E'_IfFalse : forall fc b c1 c2 l1 l2 st1 st2,
      is_pure l1 ->
      valid_label l2 ->
      beval st1 b = false ->
      ceval' fc c2 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b (com_to_lable_pure c1) l1) (LIf b (com_to_lable_pure c1) l2) st1 st2
  | E'_If1 : forall fc b c1 c2 l1 l2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c1 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b l1 (com_to_lable_pure c2)) (LIf b l2 (com_to_lable_pure c2)) st1 st2
  | E'_If2 : forall fc b c1 c2 l1 l2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c2 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b (com_to_lable_pure c1) l1) (LIf b (com_to_lable_pure c1) l2) st1 st2

  | E'_WhileFalse : forall fc b c st,
      beval st b = false ->
      ceval' fc (CWhile b c)
        (LWhile b (com_to_lable_pure c)) (LWhile b (com_to_lable_pure c)) st st
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
      ceval' fc c (com_to_lable_pure c) (com_to_lable_pure c) st1 st3 ->
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
      ceval' fc c l1 (com_to_lable_pure c) st1 st3 ->
      ceval' fc (CWhile b c) (LWhile b (com_to_lable_pure c)) l2 st3 st2 ->
      ceval' fc (CWhile b c) l1 l2 st1 st2

  | E'_Reentry1c : forall fc lf st,
      ceval' fc (CReentry lf) LPure LHere st st
  | E'_Reentryr2 : forall fc lf st,
      ceval' fc (CReentry lf) LHere LPure st st
.
(** [] *)


(** Bridging basic ceval' to multi_ceval' *)
Definition restk : Type := list (com * label * state).

Inductive middle_ceval' : func_context -> restk -> restk -> Prop :=
  | ME_r : forall fc c l1 l2 st1 st2 stk,
      ceval' fc c l1 l2 st1 st2 ->
      middle_ceval' fc ((c, l1, st1) :: stk) ((c, l2, st2) :: stk)
  | ME_re : forall fc c1 c2 l1 loc1 loc2 glb stk,
      single_point l1 ->
      middle_ceval' fc ((c1, l1, (loc1, glb)) :: stk)
        ((c2, com_to_lable_pure c2, (loc2, glb)) :: (c1, l1, (loc1, glb)) :: stk)
  | ME_ex : forall fc c1 c2 l2 loc1 loc2 glb1 glb2 stk,
      middle_ceval' fc
        ((c1, (com_to_lable_pure c1), (loc1, glb1)) :: (c2, l2, (loc2, glb2)) :: stk)
        ((c2, l2, (loc2, glb1)) :: stk).

Print clos_trans.
(*
Inductive clos_trans (A : Type) (R : relation A) (x : A) : A -> Prop :=
    t_step : forall y : A, R x y -> clos_trans A R x y
  | t_trans : forall y z : A, clos_trans A R x y -> clos_trans A R y z -> clos_trans A R x z
*)
Definition multi_ceval' (fc : func_context) : restk -> restk -> Prop :=
  clos_trans restk (middle_ceval' fc).

Lemma middle_ceval'_pure : forall fc c l1 l2 st1 st2,
  middle_ceval' fc ((c, l1, st1) :: nil) ((c, l2, st2) :: nil) ->
  ceval' fc c l1 l2 st1 st2.
Proof.
  intros.
  inversion H; subst.
  exact H2.
Qed.
(** [] *)


(** Equivalence between ceval & multi_ceval' *)
Check ceval.
Check multi_ceval'.
Print ceval.

Definition ceval'_derive_multi_ceval (fc : func_context) (c : com) (st1 st2 : state) : Prop :=
  ceval fc c st1 st2 ->
  multi_ceval' fc
    ((c, com_to_lable_pure c, st1) :: nil)
    ((c, com_to_lable_pure c, st2) :: nil).

(* Definition arbitrary_eval
  arbitrary_eval fc lf loc glb1 glb2 ->
  single_point lb ->
  multi_ceval' fc
    ((c, lb, (loc, glb1)) :: stk)
    ((c, lb, (loc, glb2)) :: stk) *)

(* 
Definition ceval_multi_derive_ceval' (fc : func_context) (f : func) (st1 st2 : state) : Prop :=
  multi_ceval' fc
    ((f, com_to_lable_pure (snd (fc f)), st1) :: nil)
    ((f, com_to_lable_pure (snd (fc f)), st2) :: nil) ->
  ceval fc (snd (fc f)) st1 st2.
 *)
(* Scheme eval_abeval := Minimality for ceval Sort Prop
  with abeval_eval := Minimality for arbitrary_eval Sort Prop. *)

Theorem ceval'_derive_multi_ceval_correct : forall fc c st1 st2,
  ceval'_derive_multi_ceval fc c st1 st2.
Proof.
  unfold ceval'_derive_multi_ceval.
  intros.
  induction H.
  - simpl.
    apply t_step, ME_r.
    apply E'_Skip.
  - simpl.
    apply t_step, ME_r.
    apply E'_Ass, H.
  - simpl.
    
    apply t_step, ME_r.
    eapply E'_Seq.
    apply com_to_lable_pure_valid.
    apply com_to_lable_pure_is_pure.
    apply com_to_lable_pure_is_pure.
    apply com_to_lable_pure_valid.
    
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

Theorem ceval_multi_derive_ceval'_correct : forall fc f st1 st2,
  ceval_multi_derive_ceval' fc f st1 st2.
Proof.
  unfold ceval_multi_derive_ceval', multi_ceval'.
  intros.

   inversion H; subst.
  {
    apply middle_ceval'_pure in H0.
    remember (snd (fc f)) as c.
    clear Heqc H.
    generalize dependent st2. revert st1.
    induction c; intros;
     inversion H0; subst;
    try (pose proof com_to_lable_pure_no_point c1;
         congruence);
    try (pose proof com_to_lable_pure_no_point c2;
         congruence);
    try (pose proof com_to_lable_pure_no_point c;
         congruence).
    - apply E_Skip.
    - apply E_Ass. reflexivity.
    - apply IHc1 in H13.
      apply IHc2 in H14.
      eapply E_Seq;
      [apply H13 | apply H14].
    - apply IHc1 in H11.
      apply (E_IfTrue _ _ _ _ _ _ H10).
      apply H11.
    - apply IHc2 in H11.
      apply (E_IfFalse _ _ _ _ _ _ H10).
      apply H11.
    - apply E_WhileFalse.
      apply H2.
    - apply IHc in H6.
      eapply E_WhileTrue.
      apply H4. apply H6.
      admit.
    - pose proof com_to_lable_pure_no_point (CWhile b c);
      congruence.
  }
  {
    remember (snd (fc f)) as c.
    clear H.
    generalize dependent y.
    revert st1 st2.
    induction c; intros; simpl in *.
    - inversion H0; inversion H1; subst.
      + inversion H; inversion H3; subst;
        try (rewrite <- Heqc in * ).
        * inversion H9; inversion H13; inversion H12; subst.
          apply E_Skip.
        * inversion H11.
        * inversion H12.
        * inversion H9.
      + inversion H; subst.
        rewrite <- Heqc in *.
        Abort.

(*   remember ((f, com_to_lable_pure (snd (fc f)), st1) :: nil) as stk1.
  remember ((f, com_to_lable_pure (snd (fc f)), st2) :: nil) as stk2.
  generalize dependent st1.
  generalize dependent st2.
  induction H; intros; subst.
  {
    apply middle_ceval'_pure in H.
    remember (snd (fc f)) as c.
    clear Heqc.
    generalize dependent st2. revert st1.
    induction c; intros;
     inversion H; subst;
    try (pose proof com_to_lable_pure_no_point c1;
         congruence);
    try (pose proof com_to_lable_pure_no_point c2;
         congruence);
    try (pose proof com_to_lable_pure_no_point c;
         congruence).
    - apply E_Skip.
    - apply E_Ass. reflexivity.
    - apply IHc1 in H13.
      apply IHc2 in H14.
      eapply E_Seq;
      [apply H13 | apply H14].
    - apply IHc1 in H11.
      apply (E_IfTrue _ _ _ _ _ _ H10).
      apply H11.
    - apply IHc2 in H11.
      apply (E_IfFalse _ _ _ _ _ _ H10).
      apply H11.
    - apply E_WhileFalse.
      apply H2.
    - apply IHc in H6.
      eapply E_WhileTrue.
      apply H4. apply H6.
      admit.
    - pose proof com_to_lable_pure_no_point (CWhile b c);
      congruence.
  }
  {
    
  }
  induction c.
  - simpl in H.
    inversion H.
    +
Admitted. *)
(** [] *)




















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
(** [] *)


(** Bridging basic ceval' to multi_ceval' *)
Definition restk : Type := list (com * label * state).

Inductive middle_ceval' : func_context -> public_funcs -> restk -> restk -> Prop :=
  | ME_r : forall fc c l1 l2 st1 st2 stk lf,
      ceval' fc c l1 l2 st1 st2 ->
      middle_ceval' fc lf ((c, l1, st1) :: stk) ((c, l2, st2) :: stk)
  | ME_re : forall fc c1 c2 l1 loc1 loc2 glb stk lf f,
      In f lf ->
      c2 = snd (fc f) ->
      single_point l1 ->
      middle_ceval' fc lf ((c1, l1, (loc1, glb)) :: stk)
        ((c2, com_to_label_pure c2, (loc2, glb)) :: (c1, l1, (loc1, glb)) :: stk)
  | ME_ex : forall fc c1 c2 l2 loc1 loc2 glb1 glb2 stk lf,
      single_point l2 ->
      middle_ceval' fc lf
        ((c1, (com_to_label_pure c1), (loc1, glb1)) :: (c2, l2, (loc2, glb2)) :: stk)
        ((c2, l2, (loc2, glb1)) :: stk).

Print clos_trans.
Search clos_trans_1n.
(*
Inductive clos_trans (A : Type) (R : relation A) (x : A) : A -> Prop :=
    t_step : forall y : A, R x y -> clos_trans A R x y
  | t_trans : forall y z : A, clos_trans A R x y -> clos_trans A R y z -> clos_trans A R x z
*)
Definition multi_ceval' (fc : func_context) (lf : public_funcs) : restk -> restk -> Prop :=
  clos_trans restk (middle_ceval' fc lf).

Lemma middle_ceval'_pure : forall fc c l1 l2 st1 st2 lf,
  middle_ceval' fc lf ((c, l1, st1) :: nil) ((c, l2, st2) :: nil) ->
  ceval' fc c l1 l2 st1 st2.
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
    ((c, com_to_label_pure c, st1) :: nil)
    ((c, com_to_label_pure c, st2) :: nil).

Definition arbitrary_eval_derive_multi_ceval : Prop :=
  forall fc lf loc glb1 glb2 lb c stk,
  single_point lb ->
  arbitrary_eval fc lf loc glb1 glb2 ->
  multi_ceval' fc lf
    ((c, lb, (loc, glb1)) :: stk)
    ((c, lb, (loc, glb2)) :: stk).


Lemma com_extension_head :
  forall fc lf c2 l2 st4 st3 c1,
  clos_trans restk (middle_ceval' fc lf)
      ((c2, l2, st4) :: nil)
      ((c2, com_to_label_pure c2, st3) :: nil) ->
  clos_trans restk (middle_ceval' fc lf)
      ((CSeq c1 c2, LSeq (com_to_label_pure c1) l2, st4) :: nil)
      ((CSeq c1 c2, LSeq (com_to_label_pure c1) (com_to_label_pure c2), st3) :: nil).
Proof.
  intros.
Admitted.

Theorem ceval'_derive_multi_ceval_correct : ceval'_derive_multi_ceval.
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
    apply Operators_Properties.clos_trans_tn1 in IHceval1.
    apply Operators_Properties.clos_trans_t1n in IHceval2.
    inversion IHceval1; subst; inversion IHceval2; subst.
    + apply middle_ceval'_pure in H1.
      apply middle_ceval'_pure in H2.
      epose proof E'_Seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2.
      apply t_step, ME_r.
      exact H3.
    + apply middle_ceval'_pure in H1.
      inversion H2; subst.
      * epose proof E'_Seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H11.
        Search clos_trans_1n clos_trans.
        apply Operators_Properties.clos_t1n_trans in H3.
        eapply com_extension_head in H3.
        apply Operators_Properties.clos_t1n_trans.
        eapply t1n_trans.
        {
          apply ME_r.
          apply H4.
        }
        {
          apply Operators_Properties.clos_trans_t1n.
          exact H3.
        }
      * pose proof com_to_label_pure_no_point c2.
        tauto.
    + apply middle_ceval'_pure in H3.
      inversion H1; subst.
      * epose proof E'_Seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H8 H3.
        admit.
      * pose proof com_to_label_pure_no_point c1.
        tauto.
    + inversion H1; subst; inversion H3; subst.
      * epose proof E'_Seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H9 H13.
        admit.
      * pose proof com_to_label_pure_no_point c2.
        tauto.
      * pose proof com_to_label_pure_no_point c1.
        tauto.
      * pose proof com_to_label_pure_no_point c1.
        tauto.
    apply t_step, ME_r.
    eapply E'_Seq.
    apply com_to_label_pure_valid.
    apply com_to_label_pure_is_pure.
    apply com_to_label_pure_is_pure.
    apply com_to_label_pure_valid.
    
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




















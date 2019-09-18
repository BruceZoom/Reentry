Require Import Coq.Lists.List.
Require Import Omega.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Require Import AST.
Require Import Label.


(** ASTLc with call *)
Module ASTLcWithCall.
Import ASTWithCall.
Import LWithCall.

(** TODO: ceval' with call *)

End ASTLcWithCall.
(** [] *)


(** ASTLc with out call *)
Module ASTLcWithoutCall.
Import ASTWithoutCall.
Import LWithoutCall.

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
      ceval' fc (CWhile b c) (LWhile b l1) l2 st1 st2

  | E'_Reentry1c : forall fc st,
      ceval' fc CReentry LPure LHere st st
  | E'_Reentryr2 : forall fc st,
      ceval' fc CReentry LHere LPure st st
.
(** [] *)

(** Middle & Multi ceval' *)
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
      c2 = func_bdy f ->
      single_point l1 ->
      middle_ceval' fc lf ((c1, Some l1, (loc1, glb)) :: stk)
        ((c2, Some (com_to_label_pure c2), (loc2, glb)) :: (c1, Some l1, (loc1, glb)) :: stk)
  | ME_ex : forall fc c1 c2 l2 loc1 loc2 glb1 glb2 stk lf,
      single_point l2 ->
      middle_ceval' fc lf
        ((c1, None, (loc1, glb1)) :: (c2, Some l2, (loc2, glb2)) :: stk)
        ((c2, Some l2, (loc2, glb1)) :: stk).

Definition multi_ceval' (fc : func_context) (lf : public_funcs) : restk -> restk -> Prop :=
  clos_refl_trans (middle_ceval' fc lf).
(** [] *)

(** Basic Properties *)
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
    right; apply SP_While; assumption.
    assumption.
  - split.
    left; apply IP_Pure.
    right; apply SP_Here.
  - split.
    right; apply SP_Here.
    left; apply IP_Pure.
Qed.

Lemma middle_ceval'_some : forall fc c l1 l2 st1 st2 lf,
  middle_ceval' fc lf ((c, Some l1, st1) :: nil) ((c, Some l2, st2) :: nil) ->
  ceval' fc c l1 l2 st1 st2.
Proof.
  intros.
  inversion H; subst.
  exact H9.
Qed.

Lemma middle_ceval'_none : forall fc c l1 st1 st2 lf stk,
  middle_ceval' fc lf ((c, Some l1, st1) :: stk) ((c, None, st2) :: stk) ->
  ceval' fc c l1 (com_to_label_pure c) st1 st2.
Proof.
  intros.
  inversion H; subst.
  exact H3.
Qed.
(** [] *)
End ASTLcWithoutCall.


(** Utilities *)
Module Utils.
(** Properties of List *)
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

Lemma cons_insert_nil {A : Type} :
  forall (a : A) l,
  a :: l = a :: nil ++ l.
Proof.
  intros.
  auto.
Qed.
(** [] *)
End Utils.
(** [] *)

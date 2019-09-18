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
  | LCall
  | LSeq (l1 : label) (l2 : label)
  | LIf (b : bexp) (l1 : label) (l2 : label)
  | LWhile (b : bexp) (l : label)
.

Inductive is_pure : label -> Prop :=
  | IP_Pure : is_pure LPure
  | IP_Call : is_pure LCall
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
  - simpl. apply IP_Pure.
Qed.
(** [] *)


(** Definition of basic ceval' *)
Definition lsstack : Type := list (label * unit_state).

Inductive ceval' : func_context -> com -> lsstack -> lsstack -> unit_state -> unit_state -> Prop :=
  | E'_Skip : forall fc loc glb,
      ceval' fc CSkip ((LPure, loc) :: nil) ((LPure, loc) :: nil) glb glb
  | E'_Ass : forall fc X a n loc1 loc2 glb1 glb2,
      aeval (loc1, glb1) a = n ->
      update_state (loc1, glb1) X n = (loc2, glb2) ->
      ceval' fc (CAss X a) ((LPure, loc1) :: nil) ((LPure, loc2) :: nil) glb1 glb2

  | E'_Reentry1c : forall fc loc glb,
      ceval' fc CReentry ((LPure, loc) :: nil) ((LHere, loc) :: nil) glb glb
  | E'_Reentryr2 : forall fc loc glb,
      ceval' fc CReentry ((LHere, loc) :: nil) ((LPure, loc) :: nil) glb glb

  | E'_CallOut : forall fc f pv stk l2 loc loc2 glb1 glb2,
      single_point l2 ->
      ceval' fc (func_bdy f)
        ((com_to_lable_pure (func_bdy f),
          (param_to_local_state (loc, glb1) (func_arg f) pv)) :: nil)
        (stk ++ (l2, loc2) :: nil) glb1 glb2 ->
(** Might be equivalent to
        ((l2, loc2) :: stk) glb1 glb2 -> *)
      ceval' fc (CCall f pv)
        ((LPure, loc) :: nil) ((LHere, loc) :: stk ++ (l2, loc2) :: nil) glb1 glb2
(** Might be equivalent to
        ((LPure, loc) :: nil) ((LHere, loc) :: (l2, loc2) :: stk) glb1 glb2 *)
  | E'_CallRet : forall fc f pv stk l1 loc loc1 loc2 glb1 glb2,
      single_point l1 ->
      ceval' fc (func_bdy f)
        (stk ++ (l1, loc1) :: nil) ((com_to_lable_pure (func_bdy f), loc2) :: nil)
        glb1 glb2 ->
      ceval' fc (CCall f pv)
        ((LHere, loc) :: stk ++ (l1, loc1) :: nil) ((LPure, loc) :: nil) glb1 glb2
  | E'_CallSeg : forall fc f pv l1 l2 stk1 stk2 loc loc1 loc2 glb1 glb2,
      single_point l1 ->
      single_point l2 ->
      ceval' fc (func_bdy f)
        (stk1 ++ (l1, loc1) :: nil) (stk2 ++ (l2, loc2) :: nil) glb1 glb2 ->
      ceval' fc (CCall f pv)
        ((LHere, loc) :: stk1 ++ (l1, loc1) :: nil)
        ((LHere, loc) :: stk2 ++ (l2, loc2) :: nil) glb1 glb2
  | E'_CallPure : forall fc f pv loc loc2 glb1 glb2,
      ceval' fc (func_bdy f)
        ((com_to_lable_pure (func_bdy f),
          (param_to_local_state (loc, glb1) (func_arg f) pv)) :: nil)
        ((com_to_lable_pure (func_bdy f), loc2) :: nil) glb1 glb2 ->
      ceval' fc (CCall f pv) ((LPure, loc) :: nil) ((LPure, loc) :: nil) glb1 glb2

  | E'_Seq : forall fc c1 c2 l1 l2 l3 l4 stk1 stk2 stk3 loc1 loc2 loc3 glb1 glb2 glb3,
      valid_label l1 ->
      is_pure l2 ->
      is_pure l3 ->
      valid_label l4 ->
      ceval' fc c1 ((l1, loc1) :: stk1) ((l2, loc3) :: stk3) glb1 glb3 ->
      ceval' fc c2 ((l3, loc3) :: stk3) ((l4, loc2) :: stk2) glb3 glb2 ->
(**   Should be equivalent to the following property
      ceval' fc c1 ((l1, loc1) :: stk1) ((l2, loc3) :: nil) glb1 glb3 ->
      ceval' fc c2 ((l3, loc3) :: nil) ((l4, loc2) :: stk2) glb3 glb2 -> *)
      ceval' fc (CSeq c1 c2)
        ((LSeq l1 l3, loc1) :: stk1) ((LSeq l2 l4, loc2) :: stk2) glb1 glb2
  | E'_Seq1 : forall fc c1 c2 l1 l2 stk1 stk2 loc1 loc2 glb1 glb2,
      valid_label l1 ->
      single_point l2 ->
      ceval' fc c1 ((l1, loc1) :: stk1) ((l2, loc2) :: stk2) glb1 glb2 ->
      ceval' fc (CSeq c1 c2)
        ((LSeq l1 (com_to_lable_pure c2), loc1) :: stk1)
        ((LSeq l2 (com_to_lable_pure c2), loc2) :: stk2) glb1 glb2
  | E'_Seq2 : forall fc c1 c2 l1 l2 stk1 stk2 loc1 loc2 glb1 glb2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c2 ((l1, loc1) :: stk1) ((l2, loc2) :: stk2) glb1 glb2 ->
      ceval' fc (CSeq c1 c2)
        ((LSeq (com_to_lable_pure c1) l1, loc1) :: stk1)
        ((LSeq (com_to_lable_pure c1) l2, loc2) :: stk2) glb1 glb2

  | E'_IfTrue : forall fc b c1 c2 l1 l2 stk loc1 loc2 glb1 glb2,
      is_pure l1 ->
      valid_label l2 ->
      beval (loc1, glb1) b = true ->
      ceval' fc c1 ((l1, loc1) :: nil) ((l2, loc2) :: stk) glb1 glb2 ->
      ceval' fc (CIf b c1 c2)
        ((LIf b l1 (com_to_lable_pure c2), loc1) :: nil)
        ((LIf b l2 (com_to_lable_pure c2), loc2) :: stk) glb1 glb2
  | E'_IfFalse : forall fc b c1 c2 l1 l2 stk loc1 loc2 glb1 glb2,
      is_pure l1 ->
      valid_label l2 ->
      beval (loc1, glb1) b = false ->
      ceval' fc c2 ((l1, loc1) :: nil) ((l2, loc2) :: stk) glb1 glb2 ->
      ceval' fc (CIf b c1 c2)
        ((LIf b (com_to_lable_pure c1) l1, loc1) :: nil)
        ((LIf b (com_to_lable_pure c1) l2, loc2) :: stk) glb1 glb2
  | E'_If1 : forall fc b c1 c2 l1 l2 stk1 stk2 loc1 loc2 glb1 glb2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c1 ((l1, loc1) :: stk1) ((l2, loc2) :: stk2) glb1 glb2 ->
      ceval' fc (CIf b c1 c2)
        ((LIf b l1 (com_to_lable_pure c2), loc1) :: stk1)
        ((LIf b l2 (com_to_lable_pure c2), loc2) :: stk2) glb1 glb2
  | E'_If2 : forall fc b c1 c2 l1 l2 stk1 stk2 loc1 loc2 glb1 glb2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c2 ((l1, loc1) :: stk1) ((l2, loc2) :: stk2) glb1 glb2 ->
      ceval' fc (CIf b c1 c2)
        ((LIf b (com_to_lable_pure c1) l1, loc1) :: stk1)
        ((LIf b (com_to_lable_pure c1) l2, loc2) :: stk2) glb1 glb2

  | E'_WhileFalse : forall fc b c loc glb,
      beval (loc, glb) b = false ->
      ceval' fc (CWhile b c)
        ((LWhile b (com_to_lable_pure c), loc) :: nil)
        ((LWhile b (com_to_lable_pure c), loc) :: nil) glb glb
  | E'_WhileTrue1 : forall fc b c l1 l2 stk loc1 loc2 glb1 glb2,
      is_pure l1 ->
      single_point l2 ->
      beval (loc1, glb1) b = true ->
      ceval' fc c ((l1, loc1) :: nil) ((l2, loc2) :: stk) glb1 glb2 ->
      ceval' fc (CWhile b c)
        ((LWhile b l1, loc1) :: nil) ((LWhile b l2, loc2) :: stk) glb1 glb2
  | E'_WhileTrue2 : forall fc b c l1 l2 stk loc1 loc2 loc3 glb1 glb2 glb3,
      is_pure l1 ->
      valid_label l2 ->
      beval (loc1, glb1) b = true ->
      ceval' fc c
        ((com_to_lable_pure c, loc1) :: nil)
        ((com_to_lable_pure c, loc3) :: nil) glb1 glb3 ->
      ceval' fc (CWhile b c)
        ((l1, loc3) :: nil) ((l2, loc2) :: stk) glb3 glb2 ->
      ceval' fc (CWhile b c)
        ((l1, loc1) :: nil) ((l2, loc2) :: stk) glb1 glb2
  | E'_WhileSeg1 : forall fc b c l1 l2 stk1 stk2 loc1 loc2 glb1 glb2,
      single_point l1 ->
      single_point l2 ->
      ceval' fc c ((l1, loc1) :: stk1) ((l2, loc2) :: stk2) glb1 glb2 ->
      ceval' fc (CWhile b c)
        ((LWhile b l1, loc1) :: stk1) ((LWhile b l2, loc2) :: stk2) glb1 glb2
  | E'_WhileSeg2 : forall fc b c l1 l2 stk1 stk2 loc1 loc2 loc3 glb1 glb2 glb3,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c
        ((l1, loc1) :: stk1) ((com_to_lable_pure c, loc3) :: nil) glb1 glb3 ->
      ceval' fc (CWhile b c)
        ((LWhile b (com_to_lable_pure c), loc3) :: nil)
        ((l2, loc2) :: stk2) glb3 glb2 ->
      ceval' fc (CWhile b c) ((l1, loc1) :: stk1) ((l2, loc2) :: stk2) glb1 glb2
.
(** [] *)


(** Bridging basic ceval' to multi_ceval' *)
Inductive middle_ceval' : func_context -> list (func * lsstack * unit_state) -> list (func * lsstack * unit_state) -> Prop :=
  | ME_r : forall fc f lsstk1 lsstk2 glb1 glb2 stk,
      ceval' fc (snd (fc f)) lsstk1 lsstk2 glb1 glb2 ->
      middle_ceval' fc ((f, lsstk1, glb1) :: stk) ((f, lsstk2, glb2) :: stk)
  | ME_re : forall fc f1 f2 l1 loc1 loc2 glb stk lsstk,
      single_point l1 ->
      middle_ceval' fc
        ((f1, (l1, loc1) :: lsstk, glb)
          :: stk)
        ((f2, (com_to_lable_pure (snd (fc f2)), loc2) :: (l1, loc1) :: lsstk, glb)
          :: (f1, (l1, loc1) :: lsstk, glb)
          :: stk)
  | ME_ex : forall fc f1 f2 l2 loc1 loc2 glb1 glb2 stk lsstk,
      middle_ceval' fc
        ((f1, (com_to_lable_pure (snd (fc f1)), loc1) :: (l2, loc2) :: lsstk, glb1)
          :: (f2, (l2, loc2) :: lsstk, glb2)
          :: stk)
        ((f2, (l2, loc2) :: lsstk, glb1)
          :: stk).

Definition multi_ceval' (fc : func_context) : list (func * lsstack * unit_state) -> list (func * lsstack * unit_state) -> Prop := clos_refl_trans (middle_ceval' fc).
(** [] *)

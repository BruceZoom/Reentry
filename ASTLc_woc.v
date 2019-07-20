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
Inductive middle_ceval' : func_context -> list (func * label * state) -> list (func * label * state) -> Prop :=
  | ME_r : forall fc f l1 l2 st1 st2 stk,
      ceval' fc (snd (fc f)) l1 l2 st1 st2 ->
      middle_ceval' fc ((f, l1, st1) :: stk) ((f, l2, st2) :: stk)
  | ME_re : forall fc f1 f2 l1 loc1 loc2 glb stk,
      single_point l1 ->
      middle_ceval' fc ((f1, l1, (loc1, glb)) :: stk)
        ((f2, (com_to_lable_pure (snd (fc f2))), (loc2, glb)) :: (f1, l1, (loc1, glb)) :: stk)
  | ME_ex : forall fc f1 f2 l2 loc1 loc2 glb1 glb2 stk,
      middle_ceval' fc
        ((f1, (com_to_lable_pure (snd (fc f1))), (loc1, glb1)) :: (f2, l2, (loc2, glb2)) :: stk)
        ((f2, l2, (loc2, glb1)) :: stk).

Definition multi_ceval' (fc : func_context) : list (func * label * state) -> list (func * label * state) -> Prop := clos_refl_trans (middle_ceval' fc).
(** [] *)

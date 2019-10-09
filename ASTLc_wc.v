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
        (com_to_lable_pure (func_bdy f) :: nil) (bstk ++ l2 :: nil)
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
        (bstk ++ l1 :: nil) ((com_to_lable_pure (func_bdy f)) :: nil)
        (sstk ++ loc1 :: nil, glb1) (loc2 :: nil, glb2) ->
      ceval' fc (CCall f pv)
        (LHere :: bstk ++ l1 :: nil) (LPure :: nil)
        (loc :: sstk ++ loc1 :: nil, glb1) (loc :: nil, glb2)
  | E'_CallSeg : forall fc f pv l1 l2 loc loc1 loc2 glb1 glb2 bstk1 bstk2 sstk1 sstk2,
      single_point l1 ->
      single_point l2 ->
      length bstk1 = length sstk1 ->
      length bstk2 = length sstk2 ->
      ceval' fc (func_bdy f)
        (bstk1 ++ l1 :: nil) (bstk2 ++ l2 :: nil)
        (sstk1 ++ loc1 :: nil, glb1) (sstk2 ++ loc2 :: nil, glb2) ->
      ceval' fc (CCall f pv)
        (LHere :: bstk1 ++ l1 :: nil) (LHere :: bstk2 ++ l2 :: nil)
        (loc :: sstk1 ++ loc1 :: nil, glb1) (loc :: sstk2 ++ loc2 :: nil, glb2)
  | E'_CallPure : forall fc f pv loc loc2 glb1 glb2,
      ceval' fc (func_bdy f)
        ((com_to_lable_pure (func_bdy f)) :: nil) ((com_to_lable_pure (func_bdy f)) :: nil)
        ((param_to_local_state (loc, glb1) (func_arg f) pv) :: nil, glb1) (loc2 :: nil, glb2) ->
      ceval' fc (CCall f pv)
        (LPure :: nil) (LPure :: nil)
        (loc :: nil, glb1) (loc :: nil, glb2)

  | E'_Seq : forall fc c1 c2 l1 l2 l3 l4 glb1 glb2 st bstk1 bstk2 sstk1 sstk2,
      valid_label l1 ->
      is_pure l2 ->
      is_pure l3 ->
      valid_label l4 ->
      1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 ->
      ceval' fc c1
        (l1 :: bstk1) (l2 :: nil)
        (sstk1, glb1) st ->
      ceval' fc c2
        (l3 :: nil) (l4 :: bstk2)
        st (sstk2, glb2) ->
      ceval' fc (CSeq c1 c2)
        ((LSeq l1 l3) :: bstk1) ((LSeq l2 l4) :: bstk2)
        (sstk1, glb1) (sstk2, glb2)
  | E'_Seq1 : forall fc c1 c2 l1 l2 glb1 glb2 bstk1 bstk2 sstk1 sstk2,
      valid_label l1 ->
      single_point l2 ->
      1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 ->
      ceval' fc c1
        (l1 :: bstk1) (l2 :: bstk2)
        (sstk1, glb1) (sstk2, glb2) ->
      ceval' fc (CSeq c1 c2)
        ((LSeq l1 (com_to_lable_pure c2)) :: bstk1)
        ((LSeq l2 (com_to_lable_pure c2)) :: bstk2)
        (sstk1, glb1) (sstk2, glb2)
  | E'_Seq2 : forall fc c1 c2 l1 l2 glb1 glb2 bstk1 bstk2 sstk1 sstk2,
      single_point l1 ->
      valid_label l2 ->
      1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 ->
      ceval' fc c2
        (l1 :: bstk1) (l2 :: bstk2)
        (sstk1, glb1) (sstk2, glb2) ->
      ceval' fc (CSeq c1 c2)
        ((LSeq (com_to_lable_pure c1) l1) :: bstk1)
        ((LSeq (com_to_lable_pure c1) l2) :: bstk2)
        (sstk1, glb1) (sstk2, glb2)

  | E'_IfTrue : forall fc b c1 c2 l1 l2 loc1 glb1 glb2 bstk sstk,
      is_pure l1 ->
      valid_label l2 ->
      1 + length bstk = length sstk ->
      beval (loc1, glb1) b = true ->
      ceval' fc c1
        (l1 :: nil) (l2 :: bstk)
        (loc1 :: nil, glb1) (sstk, glb2) ->
      ceval' fc (CIf b c1 c2)
        ((LIf b l1 (com_to_lable_pure c2)) :: nil)
        ((LIf b l2 (com_to_lable_pure c2)) :: bstk)
        (loc1 :: nil, glb1) (sstk, glb2)
  | E'_IfFalse : forall fc b c1 c2 l1 l2 loc1 glb1 glb2 bstk sstk,
      is_pure l1 ->
      valid_label l2 ->
      1 + length bstk = length sstk ->
      beval (loc1, glb1) b = false ->
      ceval' fc c2
        (l1 :: nil) (l2 :: bstk)
        (loc1 :: nil, glb1) (sstk, glb2) ->
      ceval' fc (CIf b c1 c2)
        ((LIf b (com_to_lable_pure c1) l1) :: nil)
        ((LIf b (com_to_lable_pure c1) l2) :: bstk)
        (loc1 :: nil, glb1) (sstk, glb2)
  | E'_If1 : forall fc b c1 c2 l1 l2 glb1 glb2 bstk1 bstk2 sstk1 sstk2,
      single_point l1 ->
      valid_label l2 ->
      1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 ->
      ceval' fc c1
        (l1 :: bstk1) (l2 :: bstk2)
        (sstk1, glb1) (sstk2, glb2) ->
      ceval' fc (CIf b c1 c2)
        ((LIf b l1 (com_to_lable_pure c2)) :: bstk1)
        ((LIf b l2 (com_to_lable_pure c2)) :: bstk2)
        (sstk1, glb1) (sstk2, glb2)
  | E'_If2 : forall fc b c1 c2 l1 l2 glb1 glb2 bstk1 bstk2 sstk1 sstk2,
      single_point l1 ->
      valid_label l2 ->
      1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 ->
      ceval' fc c2
        (l1 :: bstk1) (l2 :: bstk2)
        (sstk1, glb1) (sstk2, glb2) ->
      ceval' fc (CIf b c1 c2)
        ((LIf b (com_to_lable_pure c1) l1) :: bstk1)
        ((LIf b (com_to_lable_pure c1) l2) :: bstk2)
        (sstk1, glb1) (sstk2, glb2)

  | E'_WhileFalse : forall fc b c loc glb,
      beval (loc, glb) b = false ->
      ceval' fc (CWhile b c)
        ((LWhile b (com_to_lable_pure c)) :: nil)
        ((LWhile b (com_to_lable_pure c)) :: nil)
        (loc :: nil, glb) (loc :: nil, glb)
  | E'_WhileTrue1 : forall fc b c l1 l2 loc1 glb1 glb2 bstk sstk,
      is_pure l1 ->
      single_point l2 ->
      1 + length bstk = length sstk ->
      beval (loc1, glb1) b = true ->
      ceval' fc c
        (l1 :: nil) (l2 :: bstk)
        (loc1 :: nil, glb1) (sstk, glb2) ->
      ceval' fc (CWhile b c)
        ((LWhile b l1) :: nil) ((LWhile b l2) :: bstk)
        (loc1 :: nil, glb1) (sstk, glb2)
  | E'_WhileTrue2 : forall fc b c l1 l2 loc1 glb1 glb2 bstk sstk st,
      is_pure l1 ->
      valid_label l2 ->
      1 + length bstk = length sstk ->
      beval (loc1, glb1) b = true ->
      ceval' fc c
        ((com_to_lable_pure c) :: nil)
        ((com_to_lable_pure c) :: nil)
        (loc1 :: nil, glb1) st ->
      ceval' fc (CWhile b c)
        (l1 :: nil) (l2 :: bstk)
        st (sstk, glb2) ->
      ceval' fc (CWhile b c)
        (l1 :: nil) (l2 :: bstk)
        (loc1 :: nil, glb1) (sstk, glb2)
  | E'_WhileSeg1 : forall fc b c l1 l2 glb1 glb2 bstk1 bstk2 sstk1 sstk2,
      single_point l1 ->
      single_point l2 ->
      1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 ->
      ceval' fc c
        (l1 :: bstk1) (l2 :: bstk2)
        (sstk1, glb1) (sstk2, glb2) ->
      ceval' fc (CWhile b c)
        ((LWhile b l1) :: bstk1) ((LWhile b l2) :: bstk2)
        (sstk1, glb1) (sstk2, glb2)
  | E'_WhileSeg2 : forall fc b c l1 l2 glb1 glb2 bstk1 bstk2 sstk1 sstk2 st,
      single_point l1 ->
      valid_label l2 ->
      1 + length bstk1 = length sstk1 ->
      1 + length bstk2 = length sstk2 ->
      ceval' fc c
        (l1 :: bstk1) ((com_to_lable_pure c) :: nil)
        (sstk1, glb1) st ->
      ceval' fc (CWhile b c)
        ((LWhile b (com_to_lable_pure c)) :: nil) (l2 :: bstk2)
        st (sstk2, glb2) ->
      ceval' fc (CWhile b c)
        (l1 :: bstk1) (l2 :: bstk2)
        (sstk1, glb1) (sstk2, glb2)
.

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
    rewrite H10, H11. auto.
Qed.
(** [] *)


(** Bridging basic ceval' to multi_ceval' *)
Definition restk : Type := list (com * option lbstk * state').

Inductive middle_ceval' : func_context -> list func -> restk -> restk -> Prop :=
  | ME_r : forall fc lf c bstk st1 st2 stk,
      ceval' fc c bstk ((com_to_lable_pure c) :: nil) st1 st2 ->
      middle_ceval' fc lf ((c, Some bstk, st1) :: stk) ((c, None, st2) :: stk)
  | ME_r_single : forall fc c l2 bstk1 bstk2 st1 st2 stk lf,
      single_point l2 ->
      ceval' fc c bstk1 (l2 :: bstk2) st1 st2 ->
      middle_ceval' fc lf ((c, Some bstk1, st1) :: stk) ((c, Some (l2 :: bstk2), st2) :: stk)
  | ME_re : forall fc c1 c2 l1 loc glb stk lf f bstk sstk,
      In f lf ->
      c2 = func_bdy f ->
      single_point l1 ->
      (* two calling stacks should match *)
      1 + length bstk = length sstk ->
      middle_ceval' fc lf
        ((c1, Some (l1 :: bstk), (sstk, glb)) :: stk)
        (* Each reentry call clears the calling stack *)
        ((c2, Some ((com_to_lable_pure c2) :: nil), (loc :: nil, glb))
          :: (c1, Some (l1 :: bstk), (sstk, glb)) :: stk)
  | ME_ex : forall fc c1 c2 l2 glb1 glb2 stk lf bstk loc sstk,
      single_point l2 ->
      (* two calling stacks should match *)
      1 + length bstk = length sstk ->
      middle_ceval' fc lf
        ((c1, None, (loc :: nil, glb1))
          :: (c2, Some (l2 :: bstk), (sstk, glb2)) :: stk)
        ((c2, Some (l2 :: bstk), (sstk, glb1)) :: stk).

Definition multi_ceval' (fc : func_context) (lf : public_funcs) : restk -> restk -> Prop := clos_refl_trans (middle_ceval' fc lf).
(** [] *)

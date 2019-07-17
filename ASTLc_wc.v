Require Import Coq.Lists.List.
Require Import AST_wc.

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

Definition pop {A : Type} (stk : list A) : list A :=
  match stk with
  | nil => nil
  | _ :: stk' => stk'
  end.

Definition lsstack : Type := list (label * unit_state).

(* TODO: adapt semantics for structural commands to the usage of stack *)
Inductive ceval' : func_context -> com -> lsstack -> lsstack -> unit_state -> unit_state -> Prop :=
  | E'_Skip : forall fc loc glb,
      ceval' fc CSkip ((LPure, loc) :: nil) ((LPure, loc) :: nil) glb glb
  | E'_Ass : forall fc X a n loc1 loc2 glb1 glb2,
      aeval (loc1, glb1) a = n ->
      update_state (loc1, glb1) X n = (loc2, glb2) ->
      ceval' fc (CAss X a) ((LPure, loc1) :: nil) ((LPure, loc2) :: nil) glb1 glb2

  | E'_Reentry1c : forall fc lf loc glb,
      ceval' fc (CReentry lf) ((LPure, loc) :: nil) ((LHere, loc) :: nil) glb glb
  | E'_Reentryr2 : forall fc lf loc glb,
      ceval' fc (CReentry lf) ((LHere, loc) :: nil) ((LPure, loc) :: nil) glb glb

  | E'_CallOut : forall fc f pv stk l2 loc loc2 glb1 glb2,
      single_point l2 ->
      ceval' fc (snd (fc f))
        ((com_to_lable_pure (snd (fc f)),
          (param_to_local_state (loc, glb1) (fst (fc f)) pv)) :: nil)
        (stk ++ (l2, loc2) :: nil) glb1 glb2 ->
(** Might be equivalent to
        ((l2, loc2) :: stk) glb1 glb2 -> *)
      ceval' fc (CCall f pv)
        ((LPure, loc) :: nil) ((LHere, loc) :: stk ++ (l2, loc2) :: nil) glb1 glb2
(** Might be equivalent to
        ((LPure, loc) :: nil) ((LHere, loc) :: (l2, loc2) :: stk) glb1 glb2 *)
  | E'_CallRet : forall fc f pv stk l1 loc loc1 loc2 glb1 glb2,
      single_point l1 ->
      ceval' fc (snd (fc f))
        (stk ++ (l1, loc1) :: nil) ((com_to_lable_pure (snd (fc f)), loc2) :: nil)
        glb1 glb2 ->
      ceval' fc (CCall f pv)
        ((LHere, loc) :: stk ++ (l1, loc1) :: nil) ((LPure, loc) :: nil) glb1 glb2
  | E'_CallSeg : forall fc f pv l1 l2 stk1 stk2 loc loc1 loc2 glb1 glb2,
      single_point l1 ->
      single_point l2 ->
      ceval' fc (snd (fc f))
        (stk1 ++ (l1, loc1) :: nil) (stk2 ++ (l2, loc2) :: nil) glb1 glb2 ->
      ceval' fc (CCall f pv)
        ((LHere, loc) :: stk1 ++ (l1, loc1) :: nil)
        ((LHere, loc) :: stk2 ++ (l2, loc2) :: nil) glb1 glb2
  | E'_CallPure : forall fc f pv loc loc2 glb1 glb2,
      ceval' fc (snd (fc f))
        ((com_to_lable_pure (snd (fc f)),
          (param_to_local_state (loc, glb1) (fst (fc f)) pv)) :: nil)
        ((com_to_lable_pure (snd (fc f)), loc2) :: nil) glb1 glb2 ->
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

Inductive mult_ceval' : func_context -> func -> label -> label -> state -> state -> list (func * unit_state) -> Prop :=
  | ceval'_r : forall fc f l1 l2 st1 st2,
      ceval' fc (snd (fc f)) l1 l2 st1 st2 ->
      mult_ceval' fc f l1 l2 st1 st2 nil
  | ceval'_tr_re : forall fc f f' pv l1 l2 l3 l4 st1 loc1 loc2 glb1 glb2 stk,
      single_point l2 ->
      is_pure l3 ->
      mult_ceval' fc f l1 l2 st1 (loc1, glb1) stk ->
      ceval' fc (snd (fc f')) l3 l4
        (param_to_local_state (loc1, glb1) (fst (fc f')) (map (fun n => ANum n) pv), glb1) (loc2, glb2) ->
      mult_ceval' fc f' l1 l4 st1 (loc2, glb2) ((f', loc2)::stk).
  | ceval'_tr_ex : forall fc f l1 l2 l3 l4 st1 st2 st3,
      single_point l2 ->
      single_point l3 ->
      mult_ceval' fc f l1 l2 st1 st2 ->
      ceval' fc (snd (fc f)) l3 l4 st2 st3 ->
      mult_ceval' fc f l1 l4 st1 st3
.






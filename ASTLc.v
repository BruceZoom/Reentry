Require Import Coq.Lists.List.
Require Import AST.

Open Scope list_scope.
Import ListNotations.

Definition label : Type := nat.

Inductive com' : Type :=
  | CSkip' (l1 l2 : label)
  | CAss' (l1 l2 : label) (X : var) (a : aexp)
  | CSeq' (c1' c2' : com')
  | CIf' (l1 l2 : label) (b : bexp) (c1' c2' : com')
  | CWhile' (l1 l2 : label) (b : bexp) (c' : com')
  | CCall' (l1 l2 : label) (f : func) (pv : list aexp)
  | CReentry' (l1 l2 : label) (lf : list func)
  | CReentryCall (l1 l2 : label) (f : func)
.

Fixpoint com'_to_com (c' : com') : com :=
  match c' with
  | CSkip' _ _ => CSkip
  | CAss' _ _ X a => CAss X a
  | CSeq' c1' c2' => CSeq (com'_to_com c1') (com'_to_com c2')
  | CIf' _ _ b c1' c2' => CIf b (com'_to_com c1') (com'_to_com c2')
  | CWhile' _ _ b c' => CWhile b (com'_to_com c')
  | CCall' _ _ f pv => CCall f pv
  | CReentry' _ _ lf => CReentry lf
  | _ => CSkip
  end.

Fixpoint get_entry_label (c' : com') : label :=
  match c' with
  | CSkip' l1 _ => l1
  | CAss' l1 _ _ _ => l1
  | CSeq' c1' _ => get_entry_label c1'
  | CIf' l1 _ _ _ _ => l1
  | CWhile' l1 _ _ _ => l1
  | CCall' l1 _ _ _ => l1
  | CReentry' l1 _ _ => l1
  | CReentryCall l1 _ _ => l1
  end.

Fixpoint get_exit_label (c' : com') : label :=
  match c' with
  | CSkip' _ l2 => l2
  | CAss' _ l2 _ _ => l2
  | CSeq' _ c2' => get_exit_label c2'
  | CIf' _ l2 _ _ _ => l2
  | CWhile' _ l2 _ _ => l2
  | CCall' _ l2 _ _ => l2
  | CReentry' _ l2 _ => l2
  | CReentryCall _ l2 _ => l2
  end.

Inductive valid_com_label : com' -> Prop :=
  | V_Skip' : forall l1 l2,
      valid_com_label (CSkip' l1 l2)
  | V_Ass' : forall l1 l2 X a,
      valid_com_label (CAss' l1 l2 X a)
  | V_Seq' : forall c1' c2',
      valid_com_label c1' ->
      valid_com_label c2' ->
      get_exit_label c1' = get_entry_label c2' ->
      valid_com_label (CSeq' c1' c2')
  | V_If' : forall l1 l2 b c1' c2',
      valid_com_label c1' ->
      valid_com_label c2' ->
      valid_com_label (CIf' l1 l2 b c1' c2')
  | V_While' : forall l1 l2 b c',
      valid_com_label c' ->
      valid_com_label (CWhile' l1 l2 b c')
  | V_Call' : forall l1 l2 f pv,
      valid_com_label (CCall' l1 l2 f pv)
  | V_Reentry' : forall l1 l2 lf,
      valid_com_label (CReentry' l1 l2 lf)
  | V_ReentryCall : forall l1 l2 f,
      valid_com_label (CReentryCall l1 l2 f)
.

Definition func_context' : Type := func -> (list ident) * com' * label.

Definition label_context : Type := label -> com'.

Definition label_func'_context_match (lbc : label_context) (fc' : func_context') : Prop :=
  forall f, exists l1 l2, lbc (snd (fc' f)) = CReentryCall l1 l2 f.

Inductive ceval' : label_context -> func_context' -> com' -> label -> label -> state -> state -> Prop :=
(** Elementary Operations *)
  | E_Skip' : forall lbc fc' l1 l2 st,
      ceval' lbc fc' (CSkip' l1 l2) l1 l2 st st
  | E_Ass' : forall lbc fc' l1 l2 st X a n,
      ceval' lbc fc' (CAss' l1 l2 X a) l1 l2 st (update_state st X n)
(** [] *)

(** Sequencing *)
  | E_Ignore : forall lbc fc' c st lb,
      ceval' lbc fc' c lb lb st st
  | E_Seq' : forall lbc fc' c1' c2' l1 l2 l3 st1 st2 st3,
      valid_com_label (CSeq' c1' c2') ->
      ceval' lbc fc' c1' l1 l2 st1 st2 ->
      ceval' lbc fc' c2' l2 l3 st2 st3 ->
      ceval' lbc fc' (CSeq' c1' c2') l1 l3 st1 st3
(** [] *)

(** If' *)
  | E_If'True1 : forall lbc fc' b c1' c2' l1 l2 l3 st1 st2,
      beval st1 b = true ->
      ceval' lbc fc' c1' (get_entry_label c1') l3 st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l1 l3 st1 st2
  | E_If'True2 : forall lbc fc' b c1' c2' l1 l2 st1 st2,
      beval st1 b = true ->
      ceval' lbc fc' c1' (get_entry_label c1') (get_exit_label c1') st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l1 l2 st1 st2

  | E_If'False1 : forall lbc fc' b c1' c2' l1 l2 l3 st1 st2,
      beval st1 b = false ->
      ceval' lbc fc' c2' (get_entry_label c2') l3 st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l1 l3 st1 st2
  | E_If'False2 : forall lbc fc' b c1' c2' l1 l2 st1 st2,
      beval st1 b = false ->
      ceval' lbc fc' c2' (get_entry_label c2') (get_exit_label c2') st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l1 l2 st1 st2

  | E_If'Exit : forall lbc fc' b c1' c2' l1 l2 l3 st1 st2,
      ceval' lbc fc' c1' l3 (get_exit_label c1') st1 st2
      \/ ceval' lbc fc' c1' l3 (get_exit_label c2') st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l3 l2 st1 st2
  | E_If'Seg : forall lbc fc' b c1' c2' l1 l2 l3 l4 st1 st2,
      ceval' lbc fc' c1' l3 l4 st1 st2
      \/ ceval' lbc fc' c2' l3 l4 st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l3 l4 st1 st2
(** [] *)

(** While' *)
  | E_While'False : forall lbc fc' b c' l1 l2 st,
      beval st b = false ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l2 st st

  | E_While'True1 : forall lbc fc' b c' l1 l2 l3 st1 st2,
      beval st1 b = true ->
      ceval' lbc fc' c' (get_entry_label c') l3 st1 st2 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l3 st1 st2
  | E_While'True2 : forall lbc fc' b c' l1 l2 st1 st2 st3,
      beval st1 b = true ->
      ceval' lbc fc' c' (get_entry_label c') (get_exit_label c') st1 st2 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l2 st2 st3 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l2 st1 st3

  | E_While'Unroll : forall lbc fc' b c' l1 l2 l3 st1 st2 st3,
      ceval' lbc fc' c' l3 (get_exit_label c') st1 st2 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l2 st2 st3 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l3 l2 st1 st3
  | E_While'Seg : forall lbc fc' b c' l1 l2 l3 l4 st1 st2,
      ceval' lbc fc' c' l3 l4 st1 st2 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l3 l4 st1 st2
(** [] *)

(** Function Call *)
  | E_Call' : forall lbc fc' f pv l1 l2 loc1 glb1 glb2,
      (exists loc2,
        ceval' lbc fc' (snd (fst (fc' f))) (get_entry_label (snd (fst (fc' f)))) (get_exit_label (snd (fst (fc' f)))) ((param_to_local_state (loc1, glb1) (fst (fst (fc' f))) pv), glb1) (loc2, glb2)) ->
      ceval' lbc fc' (CCall' l1 l2 f pv) l1 l2 (loc1, glb1) (loc1, glb2)
(** [] *)

(** Reentry *)
  (* Transitions between entries and exits *)
  | E_Reentry'12 : forall lbc fc' lf l1 l2 st,
      ceval' lbc fc' (CReentry' l1 l2 lf) l1 l2 st st
  | E_Reentry'1c : forall lbc fc' lf l1 l2 f st,
      In f lf ->
      ceval' lbc fc' (CReentry' l1 l2 lf) l1 (snd (fc' f)) st st
  | E_Reentry'r2 : forall lbc fc' lf l1 l2 f st,
      In f lf ->
      ceval' lbc fc' (CReentry' l1 l2 lf) (get_exit_label (lbc (snd (fc' f)))) l2 st st
  | E_Reentry'rc : forall lbc fc' lf l1 l2 f1 f2 st,
      In f1 lf ->
      In f2 lf ->
      ceval' lbc fc' (CReentry' l1 l2 lf) (get_exit_label (lbc (snd (fc' f1)))) (snd (fc' f2)) st st

  (* Concrete function calls *)
  | E_ReentryCall : forall lbc fc' f pv l1 l2 loc1 glb1 glb2,
      (exists loc2,
        ceval' lbc fc' (snd (fst (fc' f))) (get_entry_label (snd (fst (fc' f)))) (get_exit_label (snd (fst (fc' f)))) ((param_to_local_state (loc1, glb1) (fst (fst (fc' f))) pv), glb1) (loc2, glb2)) ->
      ceval' lbc fc' (CReentryCall l1 l2 f) l1 l2 (loc1, glb1) (loc1, glb2)

  (* Label continuation *)
  | E_LC : forall lbc fc' c' l1 l2 l3 st1 st2 st3,
      ceval' lbc fc' c' l1 l3 st1 st3 ->
      ceval' lbc fc' (lbc l3) l3 l2 st3 st2 ->
      ceval' lbc fc' c' l1 l2 st1 st2
(** [] *)
.













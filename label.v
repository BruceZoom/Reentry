Require Import Coq.Lists.List.
Require Import AST.

(**
  DESIGN CHOICE:
  WE PREFER "PURE-SINGLE LABEL" OVER "OPTION LABEL" WHEN IMPLEMENTING CEVAL' BECAUSE IN THIS WAY WE CAN EASILY OBTAIN "HEAD LABEL" AND "TAIL LABEL" OF ANY "COMPOSITIONAL COMMAND", OTHERWISE WE NEED TO DEVISE "TWO FUNCTIONS" TO FIND THOSE LABELS FOR "EVERY COMMAND COMPOSITION" WE ADD TO THE ABSTRACT SYNTAX TREE.
*)

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

Lemma pure_no_point : forall lb,
  is_pure lb ->
  ~single_point lb.
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


(** Label with call *)
Module LWithCall.
Import ASTWithCall.

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

Lemma com_to_label_pure_no_point : forall c,
  ~single_point (com_to_label_pure c).
Proof.
  intros.
  apply pure_no_point.
  apply com_to_label_pure_is_pure.
Qed.

(** Label stack *)
Definition lbstk : Type := list label.
Definition lcstk : Type := list unit_state.

Definition pure_stk (bstk : lbstk) : Prop :=
  forall lb, In lb bstk -> is_pure lb.
(** [] *)

(** Reentry stack *)
Definition restk : Type := list (com * option lbstk * (lcstk * unit_state)).
(** [] *)
End LWithCall.
(** [] *)


(** Label with out call *)
Module LWithoutCall.
Import ASTWithoutCall.

Fixpoint com_to_label_pure (c : com) : label :=
  match c with
  | CSeq c1 c2 => LSeq (com_to_label_pure c1) (com_to_label_pure c2)
  | CIf b c1 c2 => LIf b (com_to_label_pure c1) (com_to_label_pure c2)
  | CWhile b c => LWhile b (com_to_label_pure c)
  | _ => LPure
  end.

Definition top (fc : func_context) (f : func) : label :=
  com_to_label_pure (func_bdy f).

Definition bottom (fc : func_context) (f : func) : label :=
  com_to_label_pure (func_bdy f).

Inductive matched_label : label -> com -> Prop :=
  | ML_Skip : matched_label LPure CSkip
  | ML_Ass : forall X a, matched_label LPure (CAss X a)
  | ML_Seq : forall l1 l2 c1 c2,
        matched_label l1 c1 ->
        matched_label l2 c2 ->
        matched_label (LSeq l1 l2) (CSeq c1 c2)
  | ML_If : forall l1 l2 c1 c2 b,
        matched_label l1 c1 ->
        matched_label l2 c2 ->
        matched_label (LIf b l1 l2) (CIf b c1 c2)
  | ML_While : forall lb c b,
        matched_label lb c ->
        matched_label (LWhile b lb) (CWhile b c)
  | ML_Reentry_here : matched_label LHere CReentry
  | ML_Reentry_pure : matched_label LPure CReentry.

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

Lemma com_to_label_pure_no_point : forall c,
  ~single_point (com_to_label_pure c).
Proof.
  intros.
  apply pure_no_point.
  apply com_to_label_pure_is_pure.
Qed.

(** Reentry Stack *)
Definition restk := list (com * option label * state).
(** [] *)
End LWithoutCall.
(** [] *)

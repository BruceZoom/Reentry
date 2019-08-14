Require Import Coq.Lists.List.
Require Import AST_woc.
Require Import ASTLc_woc.
Require Import Hoare_woc.


Definition LContSet := list (label * Assertion).

Definition hoare_triple' (fc : func_context) (P : LContSet) (c : com) (Q : LContSet) : Prop :=
  forall st1 st2 l1 l2 p q,
    In (l1, p) P ->
    In (l2, q) Q ->
    ceval' fc c l1 l2 st1 st2 ->
    p st1 ->
    q st2.

Definition func_triple' (fc : func_context) (P : LContSet) (f : func) (Q : LContSet) : Prop :=
  forall st1 st2 l1 l2 p q,
    In (l1, p) P ->
    In (l2, q) Q ->
    ceval' fc (snd (fc f)) l1 l2 st1 st2 ->
    p st1 ->
    q st2.

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

Definition top (fc : func_context) (f : func) : label :=
  com_to_label_pure (snd (fc f)).

Definition bottom (fc : func_context) (f : func) : label :=
  com_to_label_pure (snd (fc f)).

Definition index : Type := (func * label).
Print sig.
Print sigT.
Search sig.
Definition valid_index (fc : func_context) (lf : list func) (idx : index) : Prop :=
  In (fst idx) lf /\ matched_label (snd idx) (snd (fc (fst idx))).

Definition index_set (fc : func_context) (lf : list func) : Type :=
  sig (valid_index fc lf).

Definition param_type (fc : func_context) (lf : list func) : Type :=
  index_set fc lf -> Type.

Definition invariant (fc : func_context) (lf : list func) (pt : param_type fc lf) : Type := forall i : index_set fc lf, (pt i) -> Assertion.

Definition index_relation (fc : func_context) (lf : list func) (pt : param_type fc lf) : Type := forall i j : index_set fc lf, (pt i) -> (pt j) -> Prop.

Theorem reentry_invariant :
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariant fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt),
  (forall f',
  In f' lf ->
  forall (x : pt (f', top fc f')) (linv : list Assertion),
    (forall I (j : index_set fc (f' :: nil)),
      I = (fun st => exists (y : pt j), R (f', top f') j x y /\ (invs j y) st) <-> In I linv) ->
  func_triple fc lf
    (((f', top fc f'), (invs (f', top fc f')) x) :: linv) f' (((f', top fc f'), (invs (f', top fc f')) x) :: linv)) ->
  forall P Q linv,
  func_triple fc lf
    (((f, top fc f), P) :: linv) f (((f, top fc f), Q) :: linv).

Theorem bridge_between_hoares_re :
  forall fc lf f' l1 l2 I,
  In f' lf ->
  hoare_triple' fc ((l1, I) :: nil) (snd (fc f')) ((l2, I) :: nil) ->
  hoare_triple fc lf I CReentry I.
Proof.
  unfold hoare_triple', hoare_triple.
  intros.
  apply ceval_multi_ceval' in H1.
Admitted.

Theorem bridge_between_hoares_func :
  forall fc lf f f' lp lq P Q,
    In f' lf ->
    (forall l1 l2 p q,
      matched_label l1 (snd (fc f')) ->
      matched_label l2 (snd (fc f')) ->
      func_triple' fc ((l1, p) :: nil) f' ((l2, q) :: nil)
        /\ In p lp /\ In q lq) ->
    (forall p q,
      In p lp ->
      In q lq ->
      q |-- p) ->
    (exists l1 p,
    func_triple' fc
      ((com_to_label_pure (snd (fc f)), P) :: nil)
      f ((l1, p) :: nil) /\ matched_label l1 (snd (fc f)) /\ In p lp) ->
    (exists l2 q,
    func_triple' fc
      ((l2, q) :: nil) f
      ((com_to_label_pure (snd (fc f)), Q) :: nil)
       /\ matched_label l2 (snd (fc f)) /\ In q lq) ->
    func_triple fc lf P f Q.
Proof.
  unfold func_triple', func_triple.
  intros.













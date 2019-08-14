Require Import Coq.Lists.List.
Require Import AST_woc.
Require Import ASTLc_woc.
Require Import Hoare_woc.

Definition top (fc : func_context) (f : func) : label :=
  com_to_label_pure (snd (fc f)).

Definition bottom (fc : func_context) (f : func) : label :=
  com_to_label_pure (snd (fc f)).

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

Definition valid_index_label (fc : func_context) (lf : list func) (f : func) (lb : label) : Prop :=
  In f lf /\ single_point lb /\ matched_label lb (snd (fc f)).

Definition index_label_set (fc : func_context) (lf : list func) (f : func) : Type :=
  sig (valid_index_label fc lf f).

Definition index_set (fc : func_context) (lf : list func) : Type :=
  sigT (index_label_set fc lf).

Definition param_type (fc : func_context) (lf : list func) : Type :=
  index_set fc lf -> Type.

Definition rAssertion (fc : func_context) (lf : list func) (pt : param_type fc lf) : Type :=
  forall i: index_set fc lf, (pt i) -> Assertion.

Definition index_relation (fc : func_context) (lf : list func) (pt : param_type fc lf) : Type := forall i j : index_set fc lf, (pt i) -> (pt j) -> Prop.

Definition func_triple' (fc : func_context) (lf : list func) (P : Assertion) (f : func) (Q : Assertion) (pt : param_type fc (f :: lf)) (R1 R2 : rAssertion fc (f :: lf) pt): Prop := forall (params : forall i : index_set fc (f :: lf), (pt i)),
    forall st1 st2,
      ceval' fc (snd (fc f)) (top fc f) (bottom fc f) st1 st2 ->
      P st1 ->
      Q st2
 /\ forall st1 st2 (i: index_set fc (f :: lf)),
      ceval' fc (snd (fc f)) (top fc f) (proj1_sig (projT2 i)) st1 st2 ->
      P st1 ->
      R2 i (params i) st2
 /\ forall st1 st2 (i: index_set fc (f :: lf)),
      ceval' fc (snd (fc f)) (proj1_sig (projT2 i)) (bottom fc f) st1 st2 ->
      R1 i (params i) st1 ->
      Q st2
 /\ forall st1 st2 (i1 i2: index_set fc (f :: lf)),
      ceval' fc (snd (fc f)) (proj1_sig (projT2 i1)) (proj1_sig (projT2 i2)) st1 st2 ->
      R1 i1 (params i1) st1 ->
      R2 i2 (params i2) st2.

Search sig.

(* Definition param_type_subset (fc : func_context) (lf1 lf2 : list func) (pt1 : param_type fc lf1) (pt2 : param_type fc lf2) : Prop :=
  forall f,
    (In f lf1 -> In f lf2)
 /\ forall (lb : label) (lb2: index_label_set fc lf2 f),
      pt1 (existT (index_label_set fc lf1) f (exist (index_label_set fc lf1) lb)) = pt2 (existT (index_label_set fc lf2) f lb2). *)

Theorem reentry_invariant :
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt),
  forall f',
  In f' lf ->
  forall (i: index_set fc (f :: lf)) (x: pt i) (j: index_set fc (f' :: nil)),
  func_triple
  
  forall (i: index_set fc (f :: lf)) (x: pt i) pt' invs',
  
  func_triple' fc (invs i x) f' (invs i x) pt' invs'.



Definition label_param_type (fc : func_context) (lf : list func) (f : func) : Type :=
  index_label_set fc lf f -> Type.

Definition label_invariants (fc : func_context) (lf : list func) (f : func) (pt : label_param_type fc lf f) : Type := forall i : index_label_set fc lf f, (pt i) -> Assertion.


Definition func_triple' (fc : func_context) (P : Assertion) (f : func) (Q : Assertion) (pt : label_param_type fc (f :: nil) f) (invs : label_invariants fc (f :: nil) f pt) (params : forall ilb: index_label_set fc (f :: nil) f, pt ilb) : Prop :=
    forall st1 st2 (ilb: index_label_set fc (f :: nil) f),
      ceval' fc (snd (fc f)) (top fc f) (proj1_sig ilb) st1 st2 ->
      P st1 ->
      invs ilb (params ilb) st2
 /\ forall st1 st2 (ilb: index_label_set fc (f :: nil) f),
      ceval' fc (snd (fc f)) (proj1_sig ilb) (bottom fc f) st1 st2 ->
      invs ilb (params ilb) st1 ->
      Q st2
 /\ forall st1 st2 (ilb1 ilb2: index_label_set fc (f :: nil) f),
      ceval' fc (snd (fc f)) (proj1_sig ilb1) (proj1_sig ilb2) st1 st2 ->
      invs ilb1 (params ilb1) st1 ->
      invs ilb2 (params ilb2) st2.




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













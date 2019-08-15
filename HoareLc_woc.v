Require Import Coq.Lists.List.
Require Import AST_woc.
Require Import ASTLc_woc.
Require Import Hoare_woc.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

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

Definition valid_index_label (fc : func_context) (c : com) (lb : label) : Prop :=
  single_point lb /\ matched_label lb c.

Module COM.
Definition index_label_set (fc : func_context) (c : com) : Type :=
  sig (valid_index_label fc c).

Definition rAssertion (fc : func_context) (c : com) : Type :=
  forall i: index_label_set fc c, Assertion.
End COM.

Module FUN.
Definition index_label_set (fc : func_context) (f : func) : Type :=
  COM.index_label_set fc (snd (fc f)).

Definition rAssertion (fc : func_context) (f : func) : Type :=
  COM.rAssertion fc (snd (fc f)).
End FUN.

Record index_set (fc : func_context) (lf : list func) : Type := {
  fname : func;
  fvalid : In fname lf;
  index_label : FUN.index_label_set fc fname;
}.

Definition param_type (fc : func_context) (lf : list func) : Type :=
  index_set fc lf -> Type.

(*
Definition valid_index_label (fc : func_context) (lf : list func) (f : func) (lb : label) : Prop :=
  In f lf /\ single_point lb /\ matched_label lb (snd (fc f)).

Definition index_label_set (fc : func_context) (lf : list func) (f : func) : Type :=
  sig (valid_index_label fc lf f).

Definition index_set (fc : func_context) (lf : list func) : Type :=
  sigT (index_label_set fc lf).

Definition param_type (fc : func_context) (lf : list func) : Type :=
  index_set fc lf -> Type.
*)

Definition invariants (fc : func_context) (lf : list func) (pt : param_type fc lf) : Type :=
  forall i: index_set fc lf, (pt i) -> Assertion.

Definition index_relation (fc : func_context) (lf : list func) (pt : param_type fc lf) : Type := forall i j : index_set fc lf, (pt i) -> (pt j) -> Prop.

Definition func_triple' (fc : func_context) (f : func) (P Q : Assertion) (R1 R2 : FUN.rAssertion fc f): Prop :=
    (forall st1 st2,
      ceval' fc (snd (fc f)) (top fc f) (bottom fc f) st1 st2 ->
      P st1 ->
      Q st2)
 /\ (forall st1 st2 (i: FUN.index_label_set fc f),
      ceval' fc (snd (fc f)) (top fc f) (proj1_sig i) st1 st2 ->
      P st1 ->
      R2 i st2)
 /\ (forall st1 st2 (i: FUN.index_label_set fc f),
      ceval' fc (snd (fc f)) (proj1_sig i) (bottom fc f) st1 st2 ->
      R1 i st1 ->
      Q st2)
 /\ (forall st1 st2 (i1 i2: FUN.index_label_set fc f),
      ceval' fc (snd (fc f)) (proj1_sig i1) (proj1_sig i2) st1 st2 ->
      R1 i1 st1 ->
      R2 i2 st2).

(* Section exp.
(* Definition param_type_subset (fc : func_context) (lf1 lf2 : list func) (pt1 : param_type fc lf1) (pt2 : param_type fc lf2) : Prop :=
  forall f,
    (In f lf1 -> In f lf2)
 /\ forall (lb : label) (lb2: index_label_set fc lf2 f),
      pt1 (existT (index_label_set fc lf1) f (exist (index_label_set fc lf1) lb)) = pt2 (existT (index_label_set fc lf2) f lb2). *)

Parameter fc : func_context.
Parameter lf : list func.
Parameter f f' : func.
Parameter pt : param_type fc (f :: lf).
Parameter invs : invariants fc (f :: lf) pt.
Parameter R : index_relation fc (f :: lf) pt.
Parameter i: index_set fc (f :: lf).
(* Parameter j: index_label_set fc f'. *)
Parameter H: In f' lf.
Parameter x: pt i.
(* Check invs {| fname := f' ; fname_valid := H ; index_label := j |}. *)

Definition invs' : rAssertion fc f' :=
  fun j st => exists y, R i {| fname := f' ; fname_valid := in_cons _ _ _ H ; index_label := j |} x y /\ invs {| fname := f' ; fname_valid := in_cons _ _ _ H ; index_label := j |} y st.
End exp. *)

(* Definition empty_rassert (fc : func_context) (f : func) : rAssertion fc f :=
  fun _ _ => False. *)
Print restk.
Inductive reachable_param (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (R : index_relation fc (f :: lf) pt) : forall (i j : index_set fc (f :: lf)), restk -> (pt i) -> (pt j) -> Prop :=
  | single : forall (st1 st2 : state) i j x y,
      R i j x y ->
      reachable_param fc lf f pt R i j ((snd (fc (fname _ _ j)), Some (proj1_sig (index_label _ _ j)), st2) :: (snd (fc (fname _ _ i)), Some (proj1_sig (index_label _ _ i)), st1) :: nil) x y
  | multi : forall i j x y k (z : (pt k)) st stk,
      R i j x y ->
      reachable_param fc lf f pt R j k stk y z ->
      reachable_param fc lf f pt R i k ((snd (fc (fname _ _ i)), Some (proj1_sig (index_label _ _ i)), st) :: stk) x z.

Definition stk_to_pre (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (stk : restk) : Prop :=
  match stk with
  | nil => False
  | (c1, l1, st1) :: stk' =>
    match stk' with
    | nil =>
      match l1 with
      | Some l1 => False (* FIXME *)
      | None => False (* FIXME *)
    | (c2, l2, st2) :: _ =>
      match l1, l2 with
      | Some l1, Some l2 =>
        exists f' (H: In f' (f :: lf)) (x : FUN.index_label_set fc f'), c1 = snd (fc f') /\ l1 = proj1_sig x /\ invs {| fname := f'; fvalid := H; index_label := x |}  st1 (* FIXME *)
      | None, Some l2 => False (* FIXME *)
      | _, _ => False
      end
    end
  end.

Theorem reentry_invariant :
  forall (fc : func_context) (lf : list func) (f : func) (pt : param_type fc (f :: lf)) (invs : invariants fc (f :: lf) pt) (R : index_relation fc (f :: lf) pt) (P Q : Assertion),

  (forall f' (Hin: In f' lf) (i: index_set fc (f :: lf)) (x: pt i) invs',
    (invs' = fun j st =>
        exists y, R i {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} x y 
        /\ invs {| fname := f'; fvalid := in_cons _ _ _ Hin; index_label := j |} y st) ->
  func_triple' fc f' (invs i x) (invs i x) invs' invs') ->

  (forall (invs' : FUN.rAssertion fc f),
    (invs' = fun j st =>
        exists z, invs {| fname := f; fvalid := in_eq _ _ ; index_label := j|} z st) ->
  func_triple' fc f P Q invs' invs') ->

  func_triple fc lf P f Q.
Proof.
  intros.
  unfold func_triple.
  intros.
  apply ceval_multi_ceval' in H1.
  apply Operators_Properties.clos_rt_rt1n in H1.
  remember ((snd (fc f), Some (com_to_label_pure (snd (fc f))), st1) :: nil) as stk1.
  remember ((snd (fc f), None, st2) :: nil) as stk2.
(*   clear Heqstk1. *)
  generalize dependent st1.
(*   generalize dependent st2. *)
  induction H1; intros; subst.


  inversion Heqstk1.
  inversion H1; subst.
  - inversion H2; subst.
    2:{ inversion H4. }
    pose proof H0 (empty_rassert fc f).
    assert (empty_rassert fc f =
     (fun (j : index_label_set fc f) (st : state) =>
      exists z : pt {| fname := f; fname_valid := in_eq f lf; index_label := j |},
        invs {| fname := f; fname_valid := in_eq f lf; index_label := j |} z st)).
    {
      extensionality x.
      extensionality y.
      unfold empty_rassert.
      admit.
    }
    pose proof H4 H5; clear H4 H5.
    unfold func_triple' in H6.
    destruct H6 as [? _ _ _].
    apply (H4 st1 st2 H11 H3).
  -

(*
Proof Irrelavence
*)

(*     (fun j st => exists y, R i {| fname := f' ; fname_valid := in_cons _ _ _ H ; index_label := j |} x y /\ invs {| fname := f' ; fname_valid := in_cons _ _ _ H ; index_label := j |} y st)
    (fun j st => exists y, R i {| fname := f' ; fname_valid := in_cons _ _ _ H ; index_label := j |} x y /\ invs {| fname := f' ; fname_valid := in_cons _ _ _ H ; index_label := j |} y st).
  
  forall (i: index_set fc (f :: lf)) (x: pt i) (j: index_label_set fc f'),
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
  intros. *)













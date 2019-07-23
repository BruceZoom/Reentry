Require Import Coq.Lists.List.
Require Import AST_woc.
Require Import ASTLc_woc.
Require Import Hoare_woc.


Definition LContSet := list (label * Assertion).
Print ceval'.
Definition hoare_triple' (fc : func_context) (P : LContSet) (c : com) (Q : LContSet) : Prop :=
  forall st1 st2 l1 l2 p q,
    In (l1, p) P ->
    In (l2, q) Q ->
    ceval' fc c l1 l2 st1 st2 ->
    p st1 ->
    q st2.

Definition bridge_between_hoares_re : Prop :=
  forall fc lf f' l1 l2 I,
  In f' lf ->
  hoare_triple' fc ((l1, I) :: nil) (snd (fc f')) ((l2, I) :: nil) ->
  hoare_triple fc I (CReentry lf) I.

Theorem bridge_between_hoares_re_correct : bridge_between_hoares_re.
Proof.
  unfold bridge_between_hoares_re, hoare_triple', hoare_triple.
  intros.
Admitted.

Definition bridge_between_hoares_func : Prop

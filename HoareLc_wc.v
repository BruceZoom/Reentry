Require Import Coq.Lists.List.
Require Import AST_wc.
Require Import ASTLc_wc.
Require Import Hoare_wc.


Definition LContSet := list (label * Assertion).

Definition hoare_triple' (lbc : label_context) (fc' : func_context') (P : LContSet) (c' : com') (Q : LContSet) : Prop :=
  forall st1 st2 l1 l2 p q,
    In (l1, p) P ->
    In (l2, q) Q ->
    ceval' lbc fc' c' l1 l2 st1 st2 ->
    p st1 ->
    q st2.




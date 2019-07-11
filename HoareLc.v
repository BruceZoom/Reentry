Require Import Coq.Lists.List.
Require Import AST.

Definition label := nat.

Definition SContSet := list (label * state).

(** Denotational Semantics for Lc *)
Inductive ceval' : func_context -> com

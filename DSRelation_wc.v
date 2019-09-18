Require Import Coq.Lists.List.
Require Import Omega.

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Require Import AST.
Require Import Label.
Require Import ASTLc.

Export ASTWithCall.
Export LWithCall.
Export ASTLcWithCall.
Export Utils.

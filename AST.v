Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Definition ident : Type := nat.
Definition ident' : Type := bool (* is global *) * ident.

Definition var := ident'.
Definition func := ident.

(** Definition of AST *)
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive com : Type :=
  | CSkip
  | CAss (X : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CCall (f : func) (prms : list aexp)
  | CReentry (lf : list func).
(** [] *)

(** State Model *)
Definition unit_state : Type := ident -> nat.
Definition state : Type := unit_state (* local state *) * unit_state (* global state *).

Definition empty_state : unit_state := fun x => 0.

Definition get_state (st : state) (X : var) : nat :=
  match X with
  | (false, x) => (fst st) x
  | (true,  x) => (snd st) x
  end.

Definition update_unit_state (st : unit_state) (x : ident) (v : nat) : unit_state :=
  fun x' => if Nat.eq_dec x x' then v else st x'.

Definition update_state (st : state) (X : var) (v : nat) : state :=
  match X with
  | (false, x) => (update_unit_state (fst st) x v, snd st)
  | (true,  x) => (fst st, update_unit_state (snd st) x v)
  end.
(** [] *)

(** Expression Evaluation *)
Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => get_state st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.
(** [] *)

(** Function Context *)
Definition func_context : Type := func -> (list ident) * com.

Definition empty_func : (list ident) * com := (nil, CSkip).
(** [] *)

(** Function Support *)
Fixpoint param_to_local_state (st : state) (prm_name : list ident) (prm_value : list aexp) : unit_state :=
  match prm_name with
  | nil => empty_state
  | x :: tx =>
    match prm_value with
    | nil => empty_state
    | v :: tv => update_unit_state (param_to_local_state st tx tv) x (aeval st v)
    end
  end.
(** [] *)






































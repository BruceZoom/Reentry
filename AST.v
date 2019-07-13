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

Module Origin.
Inductive com : Type :=
  | CSkip
  | CAss (X : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CCall (f : func) (prms : list aexp)
  | CReentry (lf : list func).
End Origin.
Module Test.
Inductive com : Type :=
  | CSeq1 (c1: com) (c2 : Origin.com)
  | CSeq2 (c1 : Origin.com) (c2: com)
(*  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
*)
  | Here (lf : list func). (* a reentry in origin *)
End Test.
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

(** Denotational Semantics *)
Inductive ceval : func_context -> com -> state -> state -> Prop :=
  | E_Skip : forall fc st,
      ceval fc CSkip st st
  | E_Ass : forall fc st X a n,
      aeval st a = n ->
      ceval fc (CAss X a) st (update_state st X n)
  | E_Seq : forall fc c1 c2 st1 st2 st3,
      ceval fc c1 st1 st2 ->
      ceval fc c2 st2 st3 ->
      ceval fc (CSeq c1 c2) st1 st3
  | E_IfTrue : forall fc b c1 c2 st1 st2,
      beval st1 b = true ->
      ceval fc c1 st1 st2 ->
      ceval fc (CIf b c1 c2) st1 st2
  | E_IfFalse : forall fc b c1 c2 st1 st2,
      beval st1 b = false ->
      ceval fc c2 st1 st2 ->
      ceval fc (CIf b c1 c2) st1 st2
  | E_WhileFalse : forall fc b c st,
      beval st b = false ->
      ceval fc (CWhile b c) st st
  | E_WhileTrue : forall fc b c st1 st2 st3,
      beval st1 b = true ->
      ceval fc c st1 st2 ->
      ceval fc (CWhile b c) st2 st3 ->
      ceval fc (CWhile b c) st1 st3
  | E_Call : forall fc f pv loc1 glb1 glb2,
      (exists loc2,
        ceval fc (snd (fc f)) ((param_to_local_state (loc1, glb1) (fst (fc f)) pv), glb1) (loc2, glb2)) ->
      ceval fc (CCall f pv) (loc1, glb1) (loc1, glb2)
  | E_Reentry : forall fc lf loc glb1 glb2,
      arbitrary_eval fc lf loc glb1 glb2 ->
      ceval fc (CReentry lf) (loc, glb1) (loc, glb2)
with arbitrary_eval: forall (fc: func_context) (lf: list func) (loc : unit_state), unit_state -> unit_state -> Prop :=
  | ArE_nil: forall fc lf loc gl, arbitrary_eval fc lf loc gl gl
  | ArE_cons: forall fc lf loc gl1 gl2 gl3 f pv,
                In f lf ->
                ceval fc (CCall f (map (fun v => ANum v) pv)) (loc, gl1) (loc, gl2) ->
                arbitrary_eval fc lf loc gl2 gl3 ->
                arbitrary_eval fc lf loc gl1 gl3.
(** [] *)




































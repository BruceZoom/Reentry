Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

Definition beq_string x y :=
  if string_dec x y then true else false.

Theorem beq_string_true_iff : forall x y : string,
  beq_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold beq_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. inversion contra.
     + intros H. inversion H. subst. destruct Hs. reflexivity.
Qed.

Theorem beq_string_false_iff : forall x y : string,
  beq_string x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Definition total_map (A:Type) := string -> A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.

Notation "{ --> d }" := (t_empty d) (at level 0).

Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (t_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (t_update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 20).

Lemma t_apply_empty:  forall (A:Type) (x: string) (v: A), { --> v } x = v.
Proof.
  intros. unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (m & {x --> v}) x = v.
Proof.
  intros. simpl. unfold t_update.
  assert (beq_string x x = true).
  {rewrite beq_string_true_iff. reflexivity. }
  rewrite H. reflexivity.
Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (m & {x1 --> v}) x2 = m x2.
Proof.
  intros. simpl. unfold t_update.
  assert (beq_string x1 x2 = false).
  {rewrite beq_string_false_iff. exact H. }
  rewrite H0. reflexivity.
Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    m & {x --> v1 ; x --> v2} = m & {x --> v2}.
Proof.
  intros.
  assert (forall x':string, m & {x --> v1 ; x --> v2} x' = m & {x --> v2} x').
  { intros. unfold t_update. destruct (beq_string x x'); reflexivity. }
  apply functional_extensionality. exact H.
Qed.

Theorem t_update_same : forall X x (m : total_map X),
    m & { x --> m x } = m.
Proof.
  intros.
  apply functional_extensionality.
  unfold t_update. intros.
  destruct (beq_string x x0) eqn:H.
  - apply beq_string_true_iff in H. rewrite H. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
  m & { x2 --> v2 ; x1 --> v1 }
  =  m & { x1 --> v1 ; x2 --> v2 }.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold t_update.
  destruct (beq_string x1 x) eqn:H'; destruct (beq_string x2 x) eqn:H''; simpl; try reflexivity.
  apply beq_string_true_iff in H'. apply beq_string_true_iff in H''. subst.
  apply False_ind, H. reflexivity.
Qed.

Definition state := total_map nat.

Fixpoint list_to_state (ls:list string) (ln:list nat) : state :=
match ls with
| nil => { --> 0 }
| hs :: ts =>
  match ln with
  | nil => { --> 0 }
  | hn :: tn => (list_to_state ts tn) & {hs --> hn}
  end
end.

(*End of the definition of map*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.



Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope aexp_scope with aexp.
Infix "+" := APlus : aexp_scope.
Infix "-" := AMinus : aexp_scope.
Infix "*" := AMult : aexp_scope.
Bind Scope bexp_scope with bexp.
Infix "<=" := BLe : bexp_scope.
Infix "=" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
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

Fixpoint list_to_st (ls:list string) (la:list aexp) (st:state) : state :=
match ls with
| nil => { --> 0 }
| hs :: ts =>
  match la with
  | nil => { --> 0 }
  | ha :: ta => (list_to_st ts ta st) & {hs --> aeval st ha}
  end
end.

(*End of the definition of aexp and bexp*)

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRet : aexp -> com
  | CFuncDef : string -> list string -> com -> com
  | CFuncCall : string -> string -> list aexp -> com.


Bind Scope com_scope with com.
Notation "'SKIP'" :=
   CSkip : com_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : com_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.
Notation "'RET' a" :=
  (CRet a) (at level 60) : com_scope.
Open Scope com_scope.
Definition exit_kind : Type := bool.
Definition ek_normal : exit_kind := true.
Definition ek_return : exit_kind := false.
(*Inductive ceval : com -> state -> exit_kind -> state -> Prop :=
  | E_Skip : forall st,
      ceval SKIP st st
  | E_Ass  : forall st a n x,
      aeval st a = n ->
      ceval (x ::= a) st (st & { x --> n })
  | E_Seq : forall c1 c2 st st' st'',
      ceval c1 st st' ->
      ceval c2 st' st'' ->
      ceval (c1 ;; c2) st st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      ceval c1 st st' ->
      ceval (IFB b THEN c1 ELSE c2 FI) st st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      ceval c2 st st' ->
      ceval (IFB b THEN c1 ELSE c2 FI) st st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      ceval (WHILE b DO c END) st st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      ceval c st st' ->
      ceval (WHILE b DO c END) st' st'' ->
      ceval (WHILE b DO c END) st st''
  | E_Ret : forall st a n,
      aeval st a = n ->
      ceval (CRet a) st (st & {"R" --> n}).
*)
Definition func : Type := (list string) * com.

Definition func_context := total_map func.

Definition empty_func : func := ([],SKIP).

Example example_func : func := ([X] , RET 2*X).
Example example_fc : func_context := { --> empty_func } & { "DOUBLE" --> example_func }.
Definition FACT : com :=
IFB X=0 THEN RET 1 ELSE CFuncCall Y "FACT"%string [AMinus (AId X) 1];;RET X*Y FI.
Example example_func' : func := ([X] , FACT).
Example example_fc' : func_context := { --> empty_func } & { "FACT" --> example_func' }.
Definition MAX : com :=
IFB Y<=X THEN RET X ELSE RET Y FI.
Example example_m : func := (X::[Y], MAX).
Example example_fullfc : func_context := { --> empty_func } & { "DOUBLE" --> example_func } & { "FACT" --> example_func' } & { "MAX" --> example_m }.

Inductive ceval : func_context -> com -> state -> exit_kind -> state -> func_context -> Prop :=
  | E_Skip : forall fc st,
      ceval fc SKIP st ek_normal st fc
  | E_Ass  : forall fc st a n x,
      aeval st a = n ->
      ceval fc (x ::= a) st ek_normal (st & { x --> n }) fc
  | E_Seq_n : forall fc fc' fc'' c1 c2 st st' st'' ek,
      ceval fc c1 st ek_normal st' fc' ->
      ceval fc' c2 st' ek st'' fc'' ->
      ceval fc (c1 ;; c2) st ek st'' fc''
  | E_Seq_r : forall fc fc' c1 c2 st st',
      ceval fc c1 st ek_return st' fc' ->
      ceval fc (c1 ;; c2) st ek_return st' fc'
  | E_IfTrue : forall fc fc' st st' b c1 c2 ek,
      beval st b = true ->
      ceval fc c1 st ek st' fc' ->
      ceval fc (IFB b THEN c1 ELSE c2 FI) st ek st' fc'
  | E_IfFalse : forall fc fc' st st' b c1 c2 ek,
      beval st b = false ->
      ceval fc c2 st ek st' fc' ->
      ceval fc (IFB b THEN c1 ELSE c2 FI) st ek st' fc'
  | E_WhileFalse : forall fc b st c,
      beval st b = false ->
      ceval fc (WHILE b DO c END) st ek_normal st fc
  | E_WhileTrue_n : forall fc fc' fc'' st st' st'' b c ek,
      beval st b = true ->
      ceval fc c st ek_normal st' fc' ->
      ceval fc' (WHILE b DO c END) st' ek st'' fc'' ->
      ceval fc (WHILE b DO c END) st ek st'' fc''
  | E_WhileTrue_r : forall fc fc' st st' b c,
      beval st b = true ->
      ceval fc c st ek_return st' fc' ->
      ceval fc (WHILE b DO c END) st ek_return st' fc'
  | E_Ret : forall fc st a n,
      aeval st a = n ->
      ceval fc (RET a) st ek_return ({--> 0} & {"RV" --> n}) fc
  | E_FuncDef : forall fc st x l c,
      ceval fc (CFuncDef x l c) st ek_normal st (fc & {x --> (l,c)})
  | E_FuncCall : forall fc fc' st n x y l,
      ceval fc (snd (fc y)) (list_to_st (fst (fc y)) l st) ek_return ({--> 0} & {"RV" --> n}) fc' ->
      ceval fc (CFuncCall x y l) st ek_normal (st & { x --> n }) fc.


Example FuncDef_correct : forall st,
ceval {--> empty_func}
(
  CFuncDef "DOUBLE"%string [X] (RET 2*X);;
  CFuncDef "FACT"%string [X] FACT;;
  CFuncDef "MAX"%string (X::[Y]) MAX
)
st ek_normal st example_fullfc.
Proof.
  intros.
  eapply E_Seq_n.
  apply E_FuncDef.
  eapply E_Seq_n.
  apply E_FuncDef.
  apply E_FuncDef.
Qed.

Example DOUBLE_correct : forall (n:nat), ceval example_fc (X::=n;;CFuncCall X "DOUBLE"%string [AId X]) ({ --> 0}) ek_normal ({ --> 0}&{X --> 2*n}) example_fc.
Proof.
  intros.
  eapply E_Seq_n.
  apply E_Ass. simpl. reflexivity.
  pose proof E_FuncCall example_fc example_fc ({--> 0}&{X --> n}) (2*n) X "DOUBLE"%string [AId X] .
  assert ({ --> 0} & {X --> n; X --> 2 * n}={ --> 0} & {X --> 2 * n}).
  apply t_update_shadow.
  rewrite H0 in H.
  apply H.
  simpl.
  apply E_Ret.
  reflexivity.
Qed.

Example FACT_correct : forall (n:nat), ceval example_fc' (X::=n;;CFuncCall X "FACT"%string [AId X]) ({ --> 0}) ek_normal ({ --> 0}&{X --> fact n}) example_fc'.
Proof.
  intros.
  eapply E_Seq_n.
  apply E_Ass. simpl. reflexivity.
  pose proof E_FuncCall example_fc' example_fc' ({--> 0}&{X --> n}) (fact n) X "FACT"%string [AId X].
  assert ({ --> 0} & {X --> n; X --> fact n}={ --> 0} & {X --> fact n}).
  apply t_update_shadow.
  rewrite H0 in H.
  apply H.
  simpl.
  rewrite t_update_eq.
  induction n.
  - unfold FACT. simpl.
    apply E_IfTrue. reflexivity.
    apply E_Ret. reflexivity.
  - unfold FACT. simpl.
    apply E_IfFalse. reflexivity.
    apply (E_Seq_n _ example_fc' _ _ _ _ ({--> 0}&{X --> S n}&{Y --> fact n})).
    + apply E_FuncCall with example_fc'. simpl. replace (n-0) with n. apply IHn.
      intros. assert ({ --> 0} & {X --> n; X --> fact n} = { --> 0} & {X --> fact n}).
      apply t_update_shadow. rewrite <- H2. apply E_FuncCall with example_fc'. exact H1.
      apply t_update_shadow.
      symmetry.
      apply Nat.sub_0_r.
    + assert ((S n)*(fact n)=fact n + n*(fact n)). simpl. reflexivity.
      rewrite <- H1. apply E_Ret. reflexivity.
Qed.

Example MAX_correct : forall (n m:nat), ceval {--> empty_func} (
  CFuncDef "DOUBLE"%string [X] (RET 2*X);;
  CFuncDef "FACT"%string [X] FACT;;
  CFuncDef "MAX"%string (X::[Y]) MAX;;
  X::=n;;Y::=m;;
  CFuncCall X "MAX"%string (AId Y::[AId X])
) ({ --> 0}) ek_normal ({--> 0}&{X --> n}&{Y --> m}&{X --> Nat.max n m}) example_fullfc.
Proof.
  intros.
  eapply E_Seq_n. apply E_FuncDef.
  eapply E_Seq_n. apply E_FuncDef.
  eapply E_Seq_n. apply E_FuncDef.
  apply E_Seq_n with (fc':=example_fullfc) (st':={--> 0}&{X --> n}). apply E_Ass. reflexivity.
  apply E_Seq_n with (fc':=example_fullfc) (st':={--> 0}&{X --> n}&{Y --> m}). apply E_Ass. reflexivity.
  apply E_FuncCall with example_fullfc. simpl. unfold MAX.
  assert (X<>Y). intro. inversion H.
  assert (Y<>X). intro. inversion H0.
  destruct (beval ({ --> 0} & {Y --> ({ --> 0} & {X --> n; Y --> m}) X; X --> ({ --> 0} & {X --> n; Y --> m}) Y}) (Y<=X)) eqn:h.
  - apply E_IfTrue. exact h.
    simpl in h. apply leb_complete in h.
    rewrite t_update_neq in h; [|exact H]. rewrite t_update_eq in h. rewrite t_update_permute in h; [| exact H]. rewrite t_update_eq in h.
    rewrite t_update_eq in h. rewrite t_update_permute in h; [| exact H0]. rewrite t_update_eq in h.
    apply Nat.max_r in h. rewrite h.
    rewrite t_update_neq; [| exact H0]. rewrite t_update_eq. rewrite t_update_eq.
    apply E_Ret. reflexivity.
  - apply E_IfFalse. exact h.
    simpl in h. apply leb_iff_conv in h.
    rewrite t_update_eq in h. rewrite t_update_permute in h; [| exact H]. rewrite t_update_eq in h.
    rewrite t_update_neq in h; [|exact H]. rewrite t_update_eq in h. rewrite t_update_permute in h; [| exact H0]. rewrite t_update_eq in h.
    apply Nat.lt_le_incl in h. apply Nat.max_l in h. rewrite h.
    rewrite t_update_neq; [| exact H0]. rewrite t_update_eq. rewrite t_update_eq.
    apply E_Ret. reflexivity.
Qed.
Require Import Coq.Lists.List.
Require Import AST.

Inductive label : Type :=
  | LHere
  | LPure
  | LSeq (c1 : label) (c2 : label)
  | LIf (b : bexp) (c1 : label) (c2 : label)
  | LWhile (b : bexp) (c : label)
.

Inductive is_pure : label -> Prop :=
  | IP_Pure : is_pure LPure
  | IP_Seq : forall l1 l2,
      is_pure l1 ->
      is_pure l2 ->
      is_pure (LSeq l1 l2)
  | IP_If : forall l1 l2 b,
      is_pure l1 ->
      is_pure l2 ->
      is_pure (LIf b l1 l2)
  | IP_While : forall l b,
      is_pure l ->
      is_pure (LWhile b l)
.

Inductive single_point : label -> Prop :=
  | SP_Here : single_point LHere
  | SP_Seq1 : forall l1 l2,
      single_point l1 ->
      is_pure l2 ->
      single_point (LSeq l1 l2)
  | SP_Seq2 : forall l1 l2,
      is_pure l1 ->
      single_point l2 ->
      single_point (LSeq l1 l2)
  | SP_If1 : forall l1 l2 b,
      single_point l1 ->
      is_pure l2 ->
      single_point (LIf b l1 l2)
  | SP_If2 : forall l1 l2 b,
      is_pure l1 ->
      single_point l2 ->
      single_point (LIf b l1 l2)
  | SP_While : forall l b,
      single_point l ->
      single_point (LWhile b l)
.

Definition valid_label (l : label) : Prop := is_pure l \/ single_point l.

Fixpoint com_to_lable_pure (c : com) : label :=
  match c with
  | CSeq c1 c2 => LSeq (com_to_lable_pure c1) (com_to_lable_pure c2)
  | CIf b c1 c2 => LIf b (com_to_lable_pure c1) (com_to_lable_pure c2)
  | CWhile b c => LWhile b (com_to_lable_pure c)
  | _ => LPure
  end.

Inductive ceval' : func_context -> com -> label -> label -> state -> state -> Prop :=
  | E'_Skip : forall fc st,
      ceval' fc CSkip LPure LPure st st
  | E'_Ass : forall fc st X a n,
      aeval st a = n ->
      ceval' fc (CAss X a) LPure LPure st (update_state st X n)

  | E'_Seq : forall fc c1 c2 l1 l2 l3 l4 st1 st2 st3,
      valid_label l1 ->
      is_pure l2 ->
      is_pure l3 ->
      valid_label l4 ->
      ceval' fc c1 l1 l2 st1 st3 ->
      ceval' fc c2 l3 l4 st3 st2 ->
      ceval' fc (CSeq c1 c2) (LSeq l1 l3) (LSeq l2 l4) st1 st2
  | E'_Seq1 : forall fc c1 c2 l1 l2 st1 st2,
      valid_label l1 ->
      single_point l2 ->
      ceval' fc c1 l1 l2 st1 st2 ->
      ceval' fc (CSeq c1 c2)
        (LSeq l1 (com_to_lable_pure c2)) (LSeq l2 (com_to_lable_pure c2)) st1 st2
  | E'_Seq2 : forall fc c1 c2 l1 l2 st1 st2,
      valid_label l1 ->
      single_point l2 ->
      ceval' fc c2 l1 l2 st1 st2 ->
      ceval' fc (CSeq c1 c2)
        (LSeq (com_to_lable_pure c1) l1) (LSeq (com_to_lable_pure c1) l2) st1 st2

  | E'_IfTrue : forall fc b c1 c2 l1 l2 st1 st2,
      is_pure l1 ->
      valid_label l2 ->
      beval st1 b = true ->
      ceval' fc c1 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b l1 (com_to_lable_pure c2)) (LIf b l2 (com_to_lable_pure c2)) st1 st2
  | E'_IfFalse : forall fc b c1 c2 l1 l2 st1 st2,
      is_pure l1 ->
      valid_label l2 ->
      beval st1 b = false ->
      ceval' fc c2 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b (com_to_lable_pure c1) l1) (LIf b (com_to_lable_pure c1) l2) st1 st2
  | E'_If1 : forall fc b c1 c2 l1 l2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c1 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b l1 (com_to_lable_pure c2)) (LIf b l2 (com_to_lable_pure c2)) st1 st2
  | E'_If2 : forall fc b c1 c2 l1 l2 st1 st2,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c2 l1 l2 st1 st2 ->
      ceval' fc (CIf b c1 c2)
        (LIf b (com_to_lable_pure c1) l1) (LIf b (com_to_lable_pure c1) l2) st1 st2

  | E'_WhileFalse : forall fc b c st,
      beval st b = false ->
      ceval' fc (CWhile b c)
        (LWhile b (com_to_lable_pure c)) (LWhile b (com_to_lable_pure c)) st st
  | E'_WhileTrue1 : forall fc b c l1 l2 st1 st2,
      is_pure l1 ->
      single_point l2 ->
      beval st1 b = true ->
      ceval' fc c l1 l2 st1 st2 ->
      ceval' fc (CWhile b c) (LWhile b l1) (LWhile b l2) st1 st2
  | E'_WhileTrue2 : forall fc b c l1 l2 st1 st2 st3,
      is_pure l1 ->
      valid_label l2 ->
      beval st1 b = true ->
      ceval' fc c (com_to_lable_pure c) (com_to_lable_pure c) st1 st3 ->
      ceval' fc (CWhile b c) l1 l2 st3 st2 ->
      ceval' fc (CWhile b c) l1 l2 st1 st2
  | E'_WhileSeg1 : forall fc b c l1 l2 st1 st2,
      single_point l1 ->
      single_point l2 ->
      ceval' fc c l1 l2 st1 st2 ->
      ceval' fc (CWhile b c) (LWhile b l1) (LWhile b l2) st1 st2
  | E'_WhileSeg2 : forall fc b c l1 l2 st1 st2 st3,
      single_point l1 ->
      valid_label l2 ->
      ceval' fc c l1 (com_to_lable_pure c) st1 st3 ->
      ceval' fc (CWhile b c) (LWhile b (com_to_lable_pure c)) l2 st3 st2 ->
      ceval' fc (CWhile b c) l1 l2 st1 st2

  | E'_Call : forall fc f pv loc1 glb1 glb2,
      (exists loc2,
(*         mult_ceval' fc (snd (fc f)) *)
          ceval' fc (snd (fc f))
          (com_to_lable_pure (snd (fc f))) (com_to_lable_pure (snd (fc f)))
          ((param_to_local_state (loc1, glb1) (fst (fc f)) pv), glb1) (loc2, glb2)) ->
      ceval' fc (CCall f pv) LPure LPure (loc1, glb1) (loc1, glb2)

  | E'_Reentry1c : forall fc lf st,
      ceval' fc (CReentry lf) LPure LHere st st
  | E'_Reentryr2 : forall fc lf st,
      ceval' fc (CReentry lf) LHere LPure st st
.

Definition pop {A : Type} (stk : list A) : list A :=
  match stk with
  | nil => nil
  | _ :: stk' => stk'
  end.

Inductive mult_ceval' : func_context -> func -> label -> label -> state -> state -> list (func * unit_state) -> Prop :=
  | ceval'_r : forall fc f l1 l2 st1 st2,
      ceval' fc (snd (fc f)) l1 l2 st1 st2 ->
      mult_ceval' fc f l1 l2 st1 st2 nil
  | ceval'_tr_re : forall fc f f' pv l1 l2 l3 l4 st1 loc1 loc2 glb1 glb2 stk,
      single_point l2 ->
      is_pure l3 ->
      mult_ceval' fc f l1 l2 st1 (loc1, glb1) stk ->
      ceval' fc (snd (fc f')) l3 l4
        (param_to_local_state (loc1, glb1) (fst (fc f')) (map (fun n => ANum n) pv), glb1) (loc2, glb2) ->
      mult_ceval' fc f' l1 l4 st1 (loc2, glb2) ((f', loc2)::stk).
  | ceval'_tr_ex : forall fc f l1 l2 l3 l4 st1 st2 st3,
      single_point l2 ->
      single_point l3 ->
      mult_ceval' fc f l1 l2 st1 st2 ->
      ceval' fc (snd (fc f)) l3 l4 st2 st3 ->
      mult_ceval' fc f l1 l4 st1 st3
.

(*
Definition label : Type := nat.

Inductive com' : Type :=
  | CSkip' (l1 l2 : label)
  | CAss' (l1 l2 : label) (X : var) (a : aexp)
  | CSeq' (c1' c2' : com')
  | CIf' (l1 l2 : label) (b : bexp) (c1' c2' : com')
  | CWhile' (l1 l2 : label) (b : bexp) (c' : com')
  | CCall' (l1 l2 : label) (f : func) (pv : list aexp)
  | CReentry' (l1 l2 : label) (lf : list func)
  | CReentryCall (l1 l2 : label) (f : func)
.

Fixpoint get_entry_label (c' : com') : label :=
  match c' with
  | CSkip' l1 _ => l1
  | CAss' l1 _ _ _ => l1
  | CSeq' c1' _ => get_entry_label c1'
  | CIf' l1 _ _ _ _ => l1
  | CWhile' l1 _ _ _ => l1
  | CCall' l1 _ _ _ => l1
  | CReentry' l1 _ _ => l1
  | CReentryCall l1 _ _ => l1
  end.

Fixpoint get_exit_label (c' : com') : label :=
  match c' with
  | CSkip' _ l2 => l2
  | CAss' _ l2 _ _ => l2
  | CSeq' _ c2' => get_exit_label c2'
  | CIf' _ l2 _ _ _ => l2
  | CWhile' _ l2 _ _ => l2
  | CCall' _ l2 _ _ => l2
  | CReentry' _ l2 _ => l2
  | CReentryCall _ l2 _ => l2
  end.

(** TODO: label inequality reconsider *)
Inductive valid_com_label : com' -> Prop :=
  | V_Skip' : forall l1 l2,
      l1 <> l2 ->
      valid_com_label (CSkip' l1 l2)
  | V_Ass' : forall l1 l2 X a,
      l1 <> l2 ->
      valid_com_label (CAss' l1 l2 X a)
  | V_Seq' : forall c1' c2',
      valid_com_label c1' ->
      valid_com_label c2' ->
      get_exit_label c1' = get_entry_label c2' ->
      valid_com_label (CSeq' c1' c2')
  | V_If' : forall l1 l2 b c1' c2',
      l1 <> l2 ->
      valid_com_label c1' ->
      valid_com_label c2' ->
      valid_com_label (CIf' l1 l2 b c1' c2')
  | V_While' : forall l1 l2 b c',
      l1 <> l2 ->
      valid_com_label c' ->
      valid_com_label (CWhile' l1 l2 b c')
  | V_Call' : forall l1 l2 f pv,
      l1 <> l2 ->
      valid_com_label (CCall' l1 l2 f pv)
  | V_Reentry' : forall l1 l2 lf,
      l1 <> l2 ->
      valid_com_label (CReentry' l1 l2 lf)
  | V_ReentryCall : forall l1 l2 f,
      l1 <> l2 ->
      valid_com_label (CReentryCall l1 l2 f)
.

Lemma valid_label_no_loop : forall c',
  valid_com_label c' -> (get_entry_label c') <> (get_exit_label c').
Proof.
Admitted.

Definition func_context' : Type := func -> (list ident) * com' * label.

Definition label_context : Type := label -> com'.

Definition label_func'_context_match (lbc : label_context) (fc' : func_context') : Prop :=
  forall f, exists l1 l2, lbc (snd (fc' f)) = CReentryCall l1 l2 f.


(** Denotational Semantics for Lc *)
Inductive ceval' : label_context -> func_context' -> com' -> label -> label -> state -> state -> Prop :=
(** Elementary Operations *)
  | E_Skip' : forall lbc fc' l1 l2 st,
      ceval' lbc fc' (CSkip' l1 l2) l1 l2 st st
  | E_Ass' : forall lbc fc' l1 l2 st X a n,
      aeval st a = n ->
      ceval' lbc fc' (CAss' l1 l2 X a) l1 l2 st (update_state st X n)
(** [] *)

(** Sequencing *)
  | E_Ignore : forall lbc fc' c st lb,
      ceval' lbc fc' c lb lb st st
  | E_Seq' : forall lbc fc' c1' c2' l1 l2 l3 st1 st2 st3,
      valid_com_label (CSeq' c1' c2') ->
      ceval' lbc fc' c1' l1 l2 st1 st2 ->
      ceval' lbc fc' c2' l2 l3 st2 st3 ->
      ceval' lbc fc' (CSeq' c1' c2') l1 l3 st1 st3
(** [] *)

(** If' *)
  | E_If'True1 : forall lbc fc' b c1' c2' l1 l2 l3 st1 st2,
      beval st1 b = true ->
      ceval' lbc fc' c1' (get_entry_label c1') l3 st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l1 l3 st1 st2
  | E_If'True2 : forall lbc fc' b c1' c2' l1 l2 st1 st2,
      beval st1 b = true ->
      ceval' lbc fc' c1' (get_entry_label c1') (get_exit_label c1') st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l1 l2 st1 st2

  | E_If'False1 : forall lbc fc' b c1' c2' l1 l2 l3 st1 st2,
      beval st1 b = false ->
      ceval' lbc fc' c2' (get_entry_label c2') l3 st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l1 l3 st1 st2
  | E_If'False2 : forall lbc fc' b c1' c2' l1 l2 st1 st2,
      beval st1 b = false ->
      ceval' lbc fc' c2' (get_entry_label c2') (get_exit_label c2') st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l1 l2 st1 st2

  | E_If'Exit : forall lbc fc' b c1' c2' l1 l2 l3 st1 st2,
      ceval' lbc fc' c1' l3 (get_exit_label c1') st1 st2
      \/ ceval' lbc fc' c1' l3 (get_exit_label c2') st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l3 l2 st1 st2
  | E_If'Seg : forall lbc fc' b c1' c2' l1 l2 l3 l4 st1 st2,
      ceval' lbc fc' c1' l3 l4 st1 st2
      \/ ceval' lbc fc' c2' l3 l4 st1 st2 ->
      ceval' lbc fc' (CIf' l1 l2 b c1' c2') l3 l4 st1 st2
(** [] *)

(** While' *)
  | E_While'False : forall lbc fc' b c' l1 l2 st,
      beval st b = false ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l2 st st

  | E_While'True1 : forall lbc fc' b c' l1 l2 l3 st1 st2,
      beval st1 b = true ->
      ceval' lbc fc' c' (get_entry_label c') l3 st1 st2 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l3 st1 st2
  | E_While'True2 : forall lbc fc' b c' l1 l2 st1 st2 st3,
      beval st1 b = true ->
      ceval' lbc fc' c' (get_entry_label c') (get_exit_label c') st1 st2 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l2 st2 st3 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l2 st1 st3

  | E_While'Unroll : forall lbc fc' b c' l1 l2 l3 st1 st2 st3,
      ceval' lbc fc' c' l3 (get_exit_label c') st1 st2 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l1 l2 st2 st3 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l3 l2 st1 st3
  | E_While'Seg : forall lbc fc' b c' l1 l2 l3 l4 st1 st2,
      ceval' lbc fc' c' l3 l4 st1 st2 ->
      ceval' lbc fc' (CWhile' l1 l2 b c') l3 l4 st1 st2
(** [] *)

(** Function Call *)
  | E_Call' : forall lbc fc' f pv l1 l2 loc1 glb1 glb2,
      (exists loc2,
        ceval' lbc fc' (snd (fst (fc' f))) (get_entry_label (snd (fst (fc' f)))) (get_exit_label (snd (fst (fc' f)))) ((param_to_local_state (loc1, glb1) (fst (fst (fc' f))) pv), glb1) (loc2, glb2)) ->
      ceval' lbc fc' (CCall' l1 l2 f pv) l1 l2 (loc1, glb1) (loc1, glb2)
(** [] *)

(** Reentry *)
  (* Transitions between entries and exits *)
  | E_Reentry'12 : forall lbc fc' lf l1 l2 st,
      ceval' lbc fc' (CReentry' l1 l2 lf) l1 l2 st st
  | E_Reentry'1c : forall lbc fc' lf l1 l2 f st,
      In f lf ->
      ceval' lbc fc' (CReentry' l1 l2 lf) l1 (snd (fc' f)) st st
  | E_Reentry'r2 : forall lbc fc' lf l1 l2 f st,
      In f lf ->
      ceval' lbc fc' (CReentry' l1 l2 lf) (get_exit_label (lbc (snd (fc' f)))) l2 st st
  | E_Reentry'rc : forall lbc fc' lf l1 l2 f1 f2 st,
      In f1 lf ->
      In f2 lf ->
      ceval' lbc fc' (CReentry' l1 l2 lf) (get_exit_label (lbc (snd (fc' f1)))) (snd (fc' f2)) st st

  (* Concrete function calls *)
  | E_ReentryCall : forall lbc fc' f pv l1 l2 loc1 glb1 glb2,
      (exists loc2,
        ceval' lbc fc' (snd (fst (fc' f))) (get_entry_label (snd (fst (fc' f)))) (get_exit_label (snd (fst (fc' f)))) ((param_to_local_state (loc1, glb1) (fst (fst (fc' f))) pv), glb1) (loc2, glb2)) ->
      ceval' lbc fc' (CReentryCall l1 l2 f) l1 l2 (loc1, glb1) (loc1, glb2)

  (* Label continuation *)
  | E_LC : forall lbc fc' c' l1 l2 l3 st1 st2 st3,
      ceval' lbc fc' c' l1 l3 st1 st3 ->
      ceval' lbc fc' (lbc l3) l3 l2 st3 st2 ->
      ceval' lbc fc' c' l1 l2 st1 st2
(** [] *)
.
(** [] *)

(** Equivalence between two Semantics *)
Inductive com_equiv : com -> com' -> Prop :=
  | CE_Skip : forall l1 l2,
      com_equiv CSkip (CSkip' l1 l2)
  | CE_Ass : forall l1 l2 X a,
      com_equiv (CAss X a) (CAss' l1 l2 X a)
  | CE_Seq : forall c1 c2 c1' c2',
      com_equiv c1 c1' ->
      com_equiv c2 c2' ->
      com_equiv (CSeq c1 c2) (CSeq' c1' c2')
  | CE_If : forall l1 l2 b c1 c2 c1' c2',
      com_equiv c1 c1' ->
      com_equiv c2 c2' ->
      com_equiv (CIf b c1 c2) (CIf' l1 l2 b c1' c2')
  | CE_While : forall l1 l2 b c c',
      com_equiv c c' ->
      com_equiv (CWhile b c) (CWhile' l1 l2 b c')
  | CE_Call : forall l1 l2 f pv,
      com_equiv (CCall f pv) (CCall' l1 l2 f pv)
  | CE_Reentry : forall l1 l2 lf,
      com_equiv (CReentry lf) (CReentry' l1 l2 lf)
.

Definition func_context_equiv (fc : func_context) (fc' : func_context') : Prop :=
  forall f, fst (fc f) = fst (fst (fc' f)) /\ com_equiv (snd (fc f)) (snd (fst (fc' f))).

Theorem ceval_equiv : forall c c' st1 st2 lbc fc fc',
  label_func'_context_match lbc fc' ->
  func_context_equiv fc fc' ->
  valid_com_label c' ->
  com_equiv c c' ->
  ceval fc c st1 st2 <-> ceval' lbc fc' c' (get_entry_label c') (get_exit_label c') st1 st2.
Proof.
  intros.
  rename H into Hlfe.
  rename H0 into Hfe.
  rename H1 into Hvl.
  rename H2 into Hce.
  revert st1 st2.
  induction Hce; split; intros; simpl in *.
  - inversion H; subst.
    apply E_Skip'.
  - inversion H; subst.
    + apply E_Skip.
    + inversion Hvl.
      congruence.
    + admit.
  - inversion H; subst.
    apply E_Ass'. reflexivity.
  - inversion H; subst; simpl in *.
    + apply E_Ass. reflexivity.
    + inversion Hvl.
      congruence.
    + admit.
  - inversion H; subst.
    inversion Hvl; subst.
    rewrite (IHHce1 H2) in H3.
    rewrite (IHHce2 H4) in H6.
    eapply E_Seq'.
    + apply V_Seq'; assumption.
    + apply H3.
    + rewrite H5. apply H6.
  - inversion H; subst.
    + pose proof valid_label_no_loop (CSeq' c1' c2') Hvl.
      simpl in H0. congruence.
    + 
Admitted.
(** [] *)
*)






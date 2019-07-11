## Expressions
- No Complex Type System
- Whether value type is required?
- Whether it is necessary to distinguish between left value and right value?
```
Definition var: Type := nat.

Inductive aexp : Type :=
  | ANum (n : Z)
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
```
## Command
- The `CCall` only has one `ident` parameter to specify which function is called. __Passing parameters to and receiving return values from the function call is accomplished by assignments to global variables.__
- The `CReentry` has a list of `ident` as the parameter to specify which functions might be called at the reentry point.
```
Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CCall (f : com)             <-- (* new *) (* recursive *)
  | CReentry (lf : list com).   <-- (* new *)
```
## Denotational
### State Model
```
local_state := ident -> aexp.
global_state := ident -> aexp.
state := local_state * global_state.
```
### New Semantics
```
Definition call_sem (fbody : state -> state -> Prop) : state -> state -> Prop :=
  fun st1 st2 => forall (loc1 : local_state), exists (loc2 : local_state), fbody (loc1, snd st1) (loc2, snd st2).
```
```
Fixpoint to_seq (lf : list com) : com :=
  match lf with
  | nil => CSkip
  | c :: t => CSeq c (to_seq t)
  end.
```
```
Inductive ceval : com -> state -> state -> Prop :=
  match c with
  ...
  | E_Call : forall (loc1 : local_state) (glb1 glb2 : global_state),
    exists (loc : local_state), ceval c (loc1, glb1) (loc2, glb2) ->
    ceval (CCall c) (loc1, glb1) (loc1, glb2)
  | E_Reentry : forall (lf : list com) (st1 st2 : state),
    (forall (lf' : list com), 
      (forall c, In c lf' -> In c lf) ->
      ceval (to_seq lf') st1 st2) ->
    ceval (CReentry lf) st1 st2     (* This seems problematic *)
  end.
```
The usage of local state and global state is troubling in the definition of reentry semantics. Need to go through all possible parameter configurations, but not all global states (global attributes).
### Alternative State Model
```
unit_state := ident -> Z.
Definition empty : unit_state :=
  fun id => 0.

Inductive var_level : Type :=
  | LOC
  | GLB
  | PRM.

ident' := var_level * ident.

state := ident' -> Z.
Definition build_state (loc_st glb_st prm_st : unit_state) : state :=
  fun (id : ident') => match (fst id) with
                       | LOC => loc_st (snd id)
                       | GLB => glb_st (snd id)
                       | PRM => prm_st (snd id)
```
### Alternative New Semantics
- Passing parameters to the function is accomplished by updating parameter state, which is not used any where except at the entry of a function call.
- Receiving return value is accomplished by updating specific variable in global state.
```
Inductive ceval (c : com) : state -> state -> Prop :=
  match c with
  ...
  | E_Call : forall loc1 loc2 glb1 glb2 prm1 prm2,
      ceval c (build_state prm1 glb1 empty) (build_state loc2 glb2 empty) ->
      ceval (CCall c) (build_state loc1 glb1 prm1) (build_state loc1 glb2 empty)
  ...
```
```
Fixpoint reentry_body (lf : list c) (eval : c -> state -> state -> Prop) (glb1 glb2 : unit_state) : Prop :=
  match lf with
  | nil => glb1 = glb2
  | f :: t => forall prm1, exists loc3 glb3,
              (eval f) (build_state prm1 glb1 empty) (build_state loc3 glb3 empty) /\ reentry_body t glb3 glb2
```
```
Inductive ceval (c : com) : state -> state -> Prop :=
  match c with
  ...
  | E_Reentry : forall (lf : list com) (loc glb1 glb2 prm : unit_state),
    (forall (lf' : list com), 
      (forall c, In c lf' -> In c lf) ->
      reentry_body lf' ceval glb1 glb2) ->
    ceval (CReentry lf) (build_state loc glb1 prm) (build_state loc glb2 prm)
  end.
```

## Hoare Logic
```
Inductive hoare_triple: Type :=
| Build_hoare_triple (P_loc P_glb P_prm : Assertion) (c: com) (Q_loc Q_glb Q_prm : Assertion)
```
- May consider something similar to separation logical to describe properties of local, global, parameter variables separately.
```
forall c P1 P2 P3 Q,
{{P3 # P2 # True}} c {{True # Q # True}} ->
{{P1 # P2 # P3}} CCall c {{P1 # Q # True}}
```
```
forall lf P1 P2 I,
(forall c, In c lf ->
          {{True # I # True}} c {{True # I # True}}) ->
{{P1 # I # P2}} CReentry lf {{P1 # I # P2}}
```

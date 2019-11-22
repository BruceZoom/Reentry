# __Coq Formalization for "Reentrancy? Yes. Reentrancy bug? No."__
## __Files__
We provide following files organized in directories as our formalizations.
```
ReentryCode
│   Makefile
│   README.md
│   _CoqProject
│
├───WithCall
│       CoarseGrainedLogic.v
│       DenotationalSemantics.v
│       DerivationTheorem.v
│       FineGrainedSemantics.v
│
└───WithoutCall
        DenotationalSemantics.v
        DerivationTheorem.v
        FineGrainedSemantics.v
```

We only provide the WithCall version of `CoarseGrainedLogic.v`, because the coarse-grained logic requires properties of regular function invocations to be complete.

## __Makefile__
We provide a Makefile to compile two versions of our formalizations: with function call, and without function call.
- WithCall: Run `make WithCall` (or simply `make`) will compile `.v` files in `WithCall` folder into `.vo` files.
- WithoutCall: Run `make WithoutCall` will compile `.v` files in `WithCall` folder into `.vo` files.

_Running any of the above command will remove all existing compiled files in the current directory to avoid name conflicts._
For the same reason, we do not allow `make all`.

You may need to set up your own CONFIGURE file to the bin directory of Coq to compile files.

## __Catalogue__
### __WithCall__
#### The toy language and its denotational semantics
- Syntax Tree of the Toy Language
  - line 14 to line 47 in `WithCall/DenotationalSemantics.v`
- Program State Model and Function Model
  - line 51 to line 114 in `WithCall/DenotationalSemantics.v`
- __Definition of Denotational Semantics__ ( the $\Downarrow$ in the paper ) ( `ceval` )
  - line 139 to line 178 in `WithCall/DenotationalSemantics.v`

#### The fine-grained semantics
- __Definition of Label__
  - line 18 to line 24 in `WithCall/FineGrainedSemantics.v`
- Definition of Stacked State for Regular Function Calls
  - line 164 to line 168 in `WithCall/FineGrainedSemantics.v`
- __Definition of Fine-Grained Semantics__ ( the $\downarrow$ in the paper ) ( `ceval'` )
  - line 170 to line 339 in `WithCall/FineGrainedSemantics.v`

#### The relationship between two semantics
- __Definition of Reentry Stack__ ( the $\Sigma$ in the paper ) ( `restk` )
  - line 689 in `WithCall/FineGrainedSemantics.v`
- __Definition of Single-Step Reentry Semantics__ ( the $\downdownarrows_1$ in the paper ) ( `middle_ceval'` )
  - line 691 to line 717 in `WithCall/FineGrainedSemantics.v`
- __Definition of Multi-Step Reentry Semantics__  ( the $\downdownarrows_*$ in the paper ) ( `multi_ceval'` )
  - line 719 in `WithCall/FineGrainedSemantics.v`
- Congruence Lemmas for Reentry Semantics
  - line 790 to line 1690 in `WithCall/FineGrainedSemantics.v`
  - Congruence Lemma for Seq1 ( the example lemma 5.1 in the paper )
    - line 1032 to line 1161
- __Equivalence between Semantics__ ( theorem 5.2 `ceval_multi_ceval'` and theorem 5.3 `arbitrary_eval_multi_ceval'` in the paper )
  - line 1694 to line 2190 in `WithCall/FineGrainedSemantics.v`

#### The judgment in coarse-grained logic
- Assertion Language
  - line 17 to line 73 in `WithCall/DerivationTheorem.v`
  - Special Assertion for Stacked States
    - line 60 to line 70
- Validity of Coarse-Grained Judgment
  - line 80 to line 84 in `WithCall/DerivationTheorem.v`
- Validity of Coarse-Grained Specification
  - line 86 to line 90 in `WithCall/DerivationTheorem.v`

#### The judgment in fine-grained logic
- __Definition of Index__ ( `index_set` )
  - line 194 to line 198 in `WithCall/DerivationTheorem.v` 
- __Definition of Parameter Type__ ( the $\Lambda$ in the paper ) ( `param_type` )
  - line 200 to line 201 in `WithCall/DerivationTheorem.v`
- __Validity of Fine-Grained Specification__
  - line 208 to line 236 in `WithCall/DerivationTheorem.v`

#### The derivation theorem between judgments in two logics
- __Definition of Contract Invariant Type__ ( the type for $\mathcal{I}$ and $\mathcal{R}$ in the paper ) ( `invariants` )
  - line 203 to line 204 in `WithCall/DerivationTheorem.v`
- __Definition of Parameter Transition Relation__ ( `index_relation` )
  - line 206 to line 207 in `WithCall/DerivationTheorem.v`
- __Definition of Generalized Precondition__ ( the $\mathcal{P}(\Sigma, P, Q, \mathcal{I}, \mathcal{R})$ in the paper ) ( `stk_loc_R` and `stk_to_pre` )
  - line 678 to line 729 in `WithCall/DerivationTheorem.v`
- __Lemma 5.5__ ( `reentry_invariant_precondition` )
  - line 1320 to line 1582 in `WithCall/DerivationTheorem.v`
  - Main lemmas used in the proof:
    - `multi_ceval'_ctop` from line 733 to line 790 in `WithCall/DerivationTheorem.v`
    - `reentry_bottom_level` from line 794 to line 968 in `WithCall/DerivationTheorem.v`
    - `reentry_higher_level` from line 971 to line 1316 in `WithCall/DerivationTheorem.v`
- __The Derivation Theorem__ ( the theorem 5.4 in the paper ) ( `derivation_theorem` )
  - line 1586 to line 1638 in `WithCall/DerivationTheorem.v`

#### The coarse-grained logic (proof system, soundness and completeness)
- Function Assumption ( the $\Delta$ in the paper ) ( `func_assumption` )
  - line 387 in `WithCall/CoarseGrainedLogic.v`
- Hoare Triple
  - line 393 to line 396 in `WithCall/CoarseGrainedLogic.v`
- The Proof System ( the $\vdash$ in the paper ) ( `provable` )
  - line 398 to line 432 in `WithCall/CoarseGrainedLogic.v`
- Triple Valid ( the $\vDash$ in the paper ) ( `valid` )
  - line 434 to line 442 in `WithCall/CoarseGrainedLogic.v`
- Validity from Assumptions ( the $\VDash$ in the paper ) ( `weak_valid` )
  - line 444 to line 453 in `WithCall/CoarseGrainedLogic.v`
- __Lemma 3.2__ ( `weak_soundness` )
  - line 626 to line 640 in `WithCall/CoarseGrainedLogic.v`
  - Proofs for different branches
    - line 460 to line 624 in `WithCall/CoarseGrainedLogic.v`
    - The one for the reentry rule
      - line 460 to 483
- __Lemma 3.3__ ( `sigma_fp_valid` )
  - line 667 to line 682 in `WithCall/CoarseGrainedLogic.v`
- __Soundness__ ( theorem 3.1 in the paper ) ( `hoare_sound` )
  - line 685 to line 701 in `WithCall/CoarseGrainedLogic.v`
- __Completeness__ ( theorem 6.1 in the paper ) ( `hoare_complete` )
  - line 1052 to line 1071 in `WithCall/CoarseGrainedLogic.v`
  - The `hoare_triple_complete` from line 1033 to line 1050 is used here
  - Proofs for different branches
    - line 766 to line 1031 in `WithCall/CoarseGrainedLogic.v`
    - __The one for the reentry__ ( lemma 6.2 in the paper ) ( `hoare_reentry_complete` )
      - line 766 to line 835 in `WithCall/CoarseGrainedLogic.v`

### __WithoutCall__
#### The toy language and its denotational semantics
- Syntax Tree of the Toy Language
  - line 12 to line 33 in `WithoutCall/DenotationalSemantics.v`
- Program State Model and Function Model
  - line 37 to line 99 in `WithoutCall/DenotationalSemantics.v`
- __Definition of Denotational Semantics__ ( the $\Downarrow$ in the paper ) ( `ceval` )
  - line 103 to line 138 in `WithoutCall/DenotationalSemantics.v`

#### The fine-grained semantics
- __Definition of Label__
  - line 18 to line 24 in `WithoutCall/FineGrainedSemantics.v`
- __Definition of Fine-Grained Semantics__ ( the $\downarrow$ in the paper ) ( `ceval'` )
  - line 124 to line 212 in `WithoutCall/FineGrainedSemantics.v`

#### The relationship between two semantics
- __Definition of Reentry Stack__ ( the $\Sigma$ in the paper ) ( `restk` )
  - line 285 in `WithoutCall/FineGrainedSemantics.v`
- __Definition of Single-Step Reentry Semantics__ ( the $\downdownarrows_1$ in the paper ) ( `middle_ceval'` )
  - line 287 to line 305 in `WithoutCall/FineGrainedSemantics.v`
- __Definition of Multi-Step Reentry Semantics__  ( the $\downdownarrows_*$ in the paper ) ( `multi_ceval'` )
  - line 307 in `WithoutCall/FineGrainedSemantics.v`
- Congruence Lemmas for Reentry Semantics
  - line 373 to line 1473 in `WithoutCall/FineGrainedSemantics.v`
  - Congruence Lemma for Seq1 ( the example lemma 5.1 in the paper )
    - line 698 to line 792
- __Equivalence between Semantics__ ( theorem 5.2 `ceval_multi_ceval'` and theorem 5.3 `arbitrary_eval_multi_ceval'` in the paper )
  - line 1477 to line 1696 in `WithoutCall/FineGrainedSemantics.v`

#### The judgment in coarse-grained logic
- Assertion Language
  - line 17 to line 55 in `WithoutCall/DerivationTheorem.v`
- Validity of Coarse-Grained Judgment
  - line 62 to line 66 in `WithoutCall/DerivationTheorem.v`
- Validity of Coarse-Grained Specification
  - line 68 to line 72 in `WithoutCall/DerivationTheorem.v`

#### The judgment in fine-grained logic
- __Definition of Index__ ( `index_set` )
  - line 120 to line 124 in `WithoutCall/DerivationTheorem.v` 
- __Definition of Parameter Type__ ( the $\Lambda$ in the paper ) ( `param_type` )
  - line 126 to line 127 in `WithoutCall/DerivationTheorem.v`
- __Validity of Fine-Grained Specification__
  - line 134 to line 162 in `WithoutCall/DerivationTheorem.v`

#### The derivation theorem between judgments in two logics
- __Definition of Contract Invariant Type__ ( the type for $\mathcal{I}$ and $\mathcal{R}$ in the paper ) ( `invariants` )
  - line 129 to line 130 in `WithoutCall/DerivationTheorem.v`
- __Definition of Parameter Transition Relation__ ( `index_relation` )
  - line 132 `WithoutCall/DerivationTheorem.v`
- __Definition of Generalized Precondition__ ( the $\mathcal{P}(\Sigma, P, Q, \mathcal{I}, \mathcal{R})$ in the paper ) ( `stk_loc_R` and `stk_to_pre` )
  - line 294 to line 343 in `WithoutCall/DerivationTheorem.v`
- __Lemma 5.5__ ( `reentry_invariant_precondition` )
  - line 703 to line 838 in `WithoutCall/DerivationTheorem.v`
  - Main lemmas used in the proof:
    - `multi_ceval'_ctop` from line 347 to line 404 in `WithoutCall/DerivationTheorem.v`
    - `reentry_bottom_level` from line 408 to line 506 in `WithoutCall/DerivationTheorem.v`
    - `reentry_higher_level` from line 510 to line 699 in `WithoutCall/DerivationTheorem.v`
- __The Derivation Theorem__ ( the theorem 5.4 in the paper ) ( `derivation_theorem` )
  - line 841 to line 886 in `WithoutCall/DerivationTheorem.v`

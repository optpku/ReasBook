/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {Problem : Type u} {Query : Type v} {Answer : Type w}

/- Definition 1.2.13 lies in the informational-state/locality domain of black-box optimization.

Layer targeted by this refinement:
* source-facing informational-state and locality declarations built from the core/canonical owner
  expressions already used in Chapter 1

Primary domain:
* information-set-based black-box methods and local optimization oracles

Relevant owner-style declarations sampled before refining:
* `#check (Problem → Query → Answer)` in `Definition_1_2_8.lean`, the class-level oracle owner;
* `GeneralIterativeScheme.query`, `GeneralIterativeScheme.shouldStop`, and
  `GeneralIterativeScheme.output` in `Algorithm_1_2_10.lean`, which use the informational state
  `Set (Query × Answer)`;
* `Set.insert` in mathlib, the canonical update operation for adjoining one new oracle sample to
  an informational set;
* `DeterministicValueOracleMethod.oracleTranscript` in `Theorem_1_3_9.lean`, a downstream ordered
  sample-history view kept separate from the owner informational set.

Owner abstractions:
* the informational state is the oracle-sample set `Set (Query × Answer)`;
* locality for a class of optimization problems is `OptimizationOracle.IsLocal oracle
  sameDataNear`.

Primitive data:
* query/answer pairs `(x, oracle x)` recorded as members of an accumulated informational set;
* an oracle `Problem → Query → Answer` together with the local-data relation `sameDataNear`.

Derived API:
* information-set-based query, stopping, and output rules in `Algorithm_1_2_10.lean`;
* direct use of the locality hypothesis by application, without an extra wrapper lemma.

This file therefore exposes the informational-state type expression directly and defines the owner
locality predicate where the chapter first uses that notion, instead of keeping a parallel public
wrapper for "informational state" or "local method". -/

#check (Set (Query × Answer))

namespace OptimizationOracle

/-- A local optimization oracle has the same answer at `x` for any two problem instances whose
data agree near `x`; the relation `sameDataNear` abstracts the condition that their difference is
supported sufficiently far from the query point. -/
def IsLocal
    (oracle : Problem → Query → Answer)
    (sameDataNear : Problem → Problem → Query → Prop) : Prop :=
  ∀ ⦃problem₁ problem₂ x⦄,
    sameDataNear problem₁ problem₂ x → oracle problem₁ x = oracle problem₂ x

end OptimizationOracle

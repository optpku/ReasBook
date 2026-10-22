/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

/- Definition 1.2.4 lies in the Chapter 1 black-box optimization problem-class domain.

Sampled owner declarations:
* `#check (Type u)` in `Definition_1_2_1.lean` for the model `Σ`;
* `#check (Query → Answer)` in `Definition_1_2_2.lean` for each fixed-problem oracle;
* `#check (Set State)` in `Definition_1_2_3.lean` for the stopping criterion `𝒯_ε`;
* `GeneralIterativeScheme.shouldStop` in `Algorithm_1_2_10.lean` for a downstream consumer of the
  same stopping-criterion owner.

Source/core/bridge triage:
* source-facing: the textbook triple `𝒫 ≡ (Σ, 𝒪, 𝒯_ε)`;
* core/canonical: the owner expressions `Type`, `Query → Answer`, and `Set State`;
* bridge/view: for fixed `σ : 𝒫.model`, the evaluation `𝒫.oracle σ : Query → Answer`.

The owner abstraction stays source-facing: the primitive data are exactly the model, class oracle,
and stopping criterion, each stored in its canonical owner type. -/

/-- Definition 1.2.4: a black-box optimization problem class is the triple
`𝒫 ≡ (Σ, 𝒪, 𝒯_ε)`, where `Σ` is a model of problems, `𝒪` is the class oracle, and `𝒯_ε` is the
chosen stopping criterion. The accuracy threshold is already part of the source-facing stopping
criterion `𝒯_ε`, so it is not stored as separate primitive data in the owner. -/
structure BlackBoxOptimizationProblemClass
    (Query : Type v) (Answer : Type w) (State : Type x) where
  /-- The model `Σ` of optimization problems. -/
  model : Type u
  /-- The class oracle `𝒪`, as a model-indexed family of fixed-problem oracles. -/
  oracle : model → Query → Answer
  /-- The fixed `ε`-stopping criterion `𝒯_ε`, in the canonical owner form `Set State`. -/
  stoppingCriterion : Set State

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_38

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.91 is a recall-only item in the chapter's mixed-accuracy / iteration-bound domain.

Mandatory domain-style sampling before refinement:
- `mixedAccuracyIterationCountBound` in `Chap07/Proposition_7_38`, the Chapter 7 owner of the
  logarithmic mixed-accuracy iteration budget;
- `mixedAccuracyIterationCountBound_def` in `Chap07/Proposition_7_38`, the defining formula bridge
  for that owner;
- `mixedAccuracyUniformIterationCountBound` in `Chap07/Proposition_7_38`, the companion
  dimension-free comparison bound in the same domain;
- `quasiNewton_bestPoint_relative_accuracy_of_iterationBound` in `Chap07/Proposition_7_39`, the
  downstream theorem that uses the same logarithmic budget shape as a sufficient iteration lower
  bound.

Best owner abstraction:
- source-facing: Definition 7.91's textbook quantity `N_n(ε, δ)` for the quasi-Newton mixed
  accuracy budget;
- core/canonical: the existing Chapter 7 owner `mixedAccuracyIterationCountBound`;
- bridge/view: `mixedAccuracyIterationCountBound_def`.

Primitive data:
- the dimension `n : ℕ+`;
- the subgradient bound `L : ℝ`;
- the distance bound `R : ℝ`;
- the accuracy parameters `ε δ : ℝ`.

Derived API:
- the logarithmic expansion theorem `mixedAccuracyIterationCountBound_def`;
- the dimension-free comparison bound `mixedAccuracyUniformIterationCountBound`;
- the strict comparison theorem
  `mixedAccuracyIterationCountBound_lt_uniformUpperBound`.

Source/core/bridge triage:
- source-facing: the named textbook iteration budget `N_n(ε, δ)`;
- core/canonical: `mixedAccuracyIterationCountBound`;
- bridge/view: the expansion theorem recalled below.

The previous file duplicated the same logarithmic owner already introduced in
`Chap07/Proposition_7_38` under a second Chapter 7 name
`quasiNewtonMixedAccuracyIterationBound`. That wrapper carried no additional mathematics, so this
refinement removes it and reuses the existing owner directly.
-/

/- Definition 7.91 recalls the Chapter 7 mixed-accuracy iteration-count owner `N_n(ε, δ)`. -/
recall mixedAccuracyIterationCountBound
    (n : ℕ+) (L R ε δ : ℝ) :
    ℝ

/- The textbook logarithmic formula is recalled through the canonical expansion theorem. -/
recall mixedAccuracyIterationCountBound_def
    (n : ℕ+) (L R ε δ : ℝ) :
    mixedAccuracyIterationCountBound n L R ε δ =
      (n : ℝ) / δ * Real.log (1 + (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * ε))

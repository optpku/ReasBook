/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_14

noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n : ℕ} {m : ℕ+}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- This item lies in the chapter's finite max-absolute-inner / symmetric log-sum-exp
smoothing domain.

Sampled owner-style declarations:
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the project owner and
  its evaluation bridge for finite maxima of nonempty families;
- `absLinearLogSumExp` in `Chap07/Proposition_7_14`, the chapter owner for the symmetric
  log-sum-exp smoothing;
- `absLinearLogSumExp_apply` in `Chap07/Proposition_7_14`, the defining evaluation theorem for
  that smoothing owner.

Best owner abstraction:
- source-facing: the max-absolute-inner objective and its smooth log-sum-exp approximation;
- core/canonical: `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)` and `absLinearLogSumExp μ a`;
- bridge/view: direct recall of the positive-parameter owner surface.

Primitive data:
- a finite family `a : Fin (m : ℕ) → E`;
- a positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the canonical max-objective owner `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`;
- the canonical smoothing owner `absLinearLogSumExp μ a`.

Source/core/bridge triage:
- source-facing: the textbook formula for the max-absolute-inner objective and its smoothing;
- core/canonical: the project finite-max owner `maxTypeObjective` and the earlier Chapter 7
  smoothing owner `absLinearLogSumExp`;
- bridge/view: direct recall of the positive-parameter smoothing owner.

The previous file duplicated these owners as `maxAbsoluteInnerFunction` and
`maxAbsoluteInnerLogSumExpSmoothing`. Those wrappers carried no extra mathematics. This refined
file reuses the earlier owners directly; after fixing `Proposition_7_14` to make positivity part
of the owner itself, no extra subtype-specialization theorem is needed here.
-/

section

variable (a : Fin (m : ℕ) → E) (μ : {μ : ℝ // 0 < μ})

/- The unsmoothed objective uses the canonical finite-max owner
`maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`. -/
set_option linter.hashCommand false in
#check maxTypeObjective (fun i x ↦ |inner ℝ (a i) x|)

/- Definition 7.38: for a finite family `a : Fin (m : ℕ) → E` and a positive parameter
`μ : {μ : ℝ // 0 < μ}`, the textbook log-sum-exp smoothing
`x ↦ μ log (∑ i, [exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)])`
is the Chapter 7 owner `absLinearLogSumExp μ a`. -/
#check (absLinearLogSumExp μ a : E → ℝ)

end

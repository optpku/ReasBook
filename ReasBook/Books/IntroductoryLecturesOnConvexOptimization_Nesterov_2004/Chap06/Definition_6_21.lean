/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 6.21 lies in the finite max-type constrained-minimization domain.

Sampled owner-style declarations:
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the project owner for
  pointwise maxima of nonempty finite families;
- `SetConstrainedMinimizationProblem` and `argmin[Q]` in `Chap01/Definition_1_3_3`, the project
  owner for a feasible-set objective and its minimizer set;
- `AffineVariationalInequalityProblem.gapProblem` in `Chap06/Definition_6_18`, the chapter
  pattern of keeping the source-facing objective and packaging the associated problem through the
  Chapter 1 owner;
- `piecewiseLinearObjective` in `Chap06/Example_6_1_1`, which already expresses a finite affine
  maximum through `maxTypeObjective`.

Best owner abstraction:
- source-facing: `maxAbsoluteValueOptimizationObjective`;
- core/canonical: `maxTypeObjective` for the finite maximum and
  `SetConstrainedMinimizationProblem E` for the ambient constrained problem;
- bridge/view: `maxAbsoluteValueOptimizationProblem`, whose minimizer set is
  `argmin[Q₁] (maxAbsoluteValueOptimizationObjective a b)`.

Primitive data:
- the nonempty finite index type `ι`;
- the affine data `a : ι → Module.Dual ℝ E` and `b : ι → ℝ`.

Derived API:
- the ambient objective on `E`, expressed through `maxTypeObjective`;
- the associated constrained minimization problem with feasible set `Q₁`;
- the canonical minimizer set `argmin[Q₁] (maxAbsoluteValueOptimizationObjective a b)`.

Source/core/bridge triage:
- source-facing: the finite max-of-absolute-values objective;
- core/canonical: `maxTypeObjective`, `SetConstrainedMinimizationProblem`, and `argmin[Q]`;
- bridge/view: `maxAbsoluteValueOptimizationProblem`.

The previous version packaged the objective on the subtype `Q₁` and then rebuilt the problem as an
unconstrained problem on that subtype. This file keeps the source-facing objective as an ambient
function on `E` and uses the Chapter 1 owner `SetConstrainedMinimizationProblem E` directly, so
the feasible set remains part of the constraint layer rather than the primitive objective data.
-/

/-- For a feasible set `Q₁ ⊆ E` and linear functionals `a_i ∈ E*` with offsets `bⁱ` indexed by
a nonempty finite family, the maximum-of-absolute-values objective is the ambient function
`f(x) = max_i (|a_i(x)| - bⁱ)`. -/
def maxAbsoluteValueOptimizationObjective
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) : E → ℝ :=
  maxTypeObjective fun i x ↦ |a i x| - b i

/-- Evaluating the objective recovers the finite maximum of the shifted absolute dual pairings. -/
@[simp] theorem maxAbsoluteValueOptimizationObjective_apply
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (x : E) :
    maxAbsoluteValueOptimizationObjective a b x =
      Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ |a i x| - b i) := by
  simpa [maxAbsoluteValueOptimizationObjective] using
    (maxTypeObjective_apply (fun i x ↦ |a i x| - b i) x)

-- Proof sketch: rewrite the objective through `maxAbsoluteValueOptimizationObjective_apply` and
-- apply the canonical finite-maximum bound criterion `maxTypeObjective_le_iff` to the family
-- `i ↦ |a i x| - b i`.
/-- Definition 6.21: the max-absolute-value objective is bounded by `t` at `x` exactly when every
shifted absolute dual pairing `|aᵢ(x)| - bᵢ` is bounded by `t`. -/
theorem maxAbsoluteValueOptimizationObjective_le_iff
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (x : E) (t : ℝ) :
    maxAbsoluteValueOptimizationObjective a b x ≤ t ↔
      ∀ i : ι, |a i x| - b i ≤ t := by
  -- Rewrite to the Chapter 2 owner `maxTypeObjective` and reuse its pointwise bound criterion.
  simpa [maxAbsoluteValueOptimizationObjective] using
    (maxTypeObjective_le_iff (fun i x ↦ |a i x| - b i) x t)

/-- The associated optimization problem `min_{x ∈ Q₁} max_i (|a_i(x)| - bⁱ)`, expressed through
the Chapter 1 ambient owner. Its minimizer set is
`argmin[Q₁] (maxAbsoluteValueOptimizationObjective a b)`. -/
def maxAbsoluteValueOptimizationProblem
    (Q₁ : Set E) (a : ι → Module.Dual ℝ E) (b : ι → ℝ) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := Q₁
  objective := maxAbsoluteValueOptimizationObjective a b

/-- The feasible set of the associated optimization problem is exactly `Q₁`. -/
@[simp] theorem maxAbsoluteValueOptimizationProblem_feasibleSet
    (Q₁ : Set E) (a : ι → Module.Dual ℝ E) (b : ι → ℝ) :
    (maxAbsoluteValueOptimizationProblem Q₁ a b).feasibleSet = Q₁ :=
  rfl

/-- Evaluating the associated problem recovers the source-facing objective. -/
@[simp] theorem maxAbsoluteValueOptimizationProblem_apply
    (Q₁ : Set E) (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (x : E) :
    maxAbsoluteValueOptimizationProblem Q₁ a b x =
      maxAbsoluteValueOptimizationObjective a b x :=
  rfl

end

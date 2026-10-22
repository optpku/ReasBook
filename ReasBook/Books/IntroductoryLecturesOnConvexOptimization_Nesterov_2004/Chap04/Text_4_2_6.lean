/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Text 4.2.6 lies in real inner-product-space norm-power calculus.

Layer targeted by this refinement:
- source-facing: the centered power-distance `x ↦ (1 / p) * ‖x - x₀‖^p`;
- core/canonical: mathlib's `hasFDerivAt_norm_rpow` and the chapter/mathlib owner
  `HasGradientAt`;
- bridge/view: the differentiability consequences below.

Sampled owner-style declarations:
- `HasGradientAt` in `Mathlib.Analysis.Calculus.Gradient.Basic`;
- `HasGradientAt.differentiableAt`;
- `hasFDerivAt_norm_rpow` in `Mathlib.Analysis.InnerProductSpace.NormPow`;
- `HasFDerivAt.hasGradientAt`.

Primitive data:
- the exponent `p : ℝ`;
- the center `x₀ : E`.

Derived API:
- the pointwise expansion of `powerDistance`;
- the gradient formula;
- differentiability at a point and on the whole space.

There is no earlier chapter owner for this centered Euclidean power function itself, so the
source-facing owner `powerDistance` stays public. The gradient theorem is refined to reuse the
canonical norm-power derivative owner instead of a parallel local wheel. -/

section Basic

variable {E : Type u} [NormedAddCommGroup E]

/-- The power-distance from a center `x₀`, namely `x ↦ (1 / p) * ‖x - x₀‖^p`. -/
def powerDistance (p : ℝ) (x0 : E) : E → ℝ :=
  fun x ↦ (1 / p) * ‖x - x0‖ ^ p

/-- Expanding `powerDistance p x₀` at `x` yields `(1 / p) * ‖x - x₀‖^p`. -/
theorem powerDistance_apply (p : ℝ) (x0 x : E) :
    powerDistance p x0 x = (1 / p) * ‖x - x0‖ ^ p :=
  rfl

end Basic

section Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- For `p > 1`, the centered power-distance has gradient
`‖x - x₀‖^(p - 2) • (x - x₀)` at `x`. -/
theorem hasGradientAt_powerDistance_of_one_lt
    {p : ℝ} (hp : 1 < p) (x0 x : E) :
    HasGradientAt (powerDistance p x0)
      (‖x - x0‖ ^ (p - 2) • (x - x0)) x := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp.le).ne'
  have htoDual_innerSL (z : E) : (InnerProductSpace.toDual ℝ E).symm ((innerSL ℝ) z) = z := by
    apply ext_inner_right ℝ
    intro y
    simp [InnerProductSpace.toDual_symm_apply]
  have hsub : HasFDerivAt (fun y : E ↦ y - x0) (1 : E →L[ℝ] E) x := by
    simpa using (hasFDerivAt_id x).sub_const x0
  have hnorm :
      HasFDerivAt (fun y : E ↦ ‖y - x0‖ ^ p)
        ((p * ‖x - x0‖ ^ (p - 2)) • innerSL ℝ (x - x0)) x := by
    simpa using (hasFDerivAt_norm_rpow (x - x0) hp).comp x hsub
  have hscaled :
      HasFDerivAt (fun y : E ↦ (1 / p) * ‖y - x0‖ ^ p)
        (((1 / p) * (p * ‖x - x0‖ ^ (p - 2))) • innerSL ℝ (x - x0)) x := by
    simpa [one_div, smul_smul, mul_assoc, mul_comm, mul_left_comm] using
      hnorm.const_smul (1 / p)
  have hgrad :
      HasGradientAt (fun y : E ↦ (1 / p) * ‖y - x0‖ ^ p)
        (‖x - x0‖ ^ (p - 2) • (x - x0)) x := by
    simpa [one_div, smul_smul, mul_assoc, mul_comm, mul_left_comm, hp0, sub_eq_add_neg,
      htoDual_innerSL] using hscaled.hasGradientAt
  change HasGradientAt (fun y : E ↦ (1 / p) * ‖y - x0‖ ^ p)
    (‖x - x0‖ ^ (p - 2) • (x - x0)) x
  exact hgrad

/-- Text 4.2.6: for `p ≥ 2`, the power-distance `x ↦ (1 / p) * ‖x - x₀‖^p` on a real
inner-product space has gradient `‖x - x₀‖^(p - 2) • (x - x₀)` at every point. In particular,
this applies to the finite-dimensional setting of the text. -/
theorem hasGradientAt_powerDistance
    {p : ℝ} (hp : 2 ≤ p) (x0 x : E) :
    HasGradientAt (powerDistance p x0)
      (‖x - x0‖ ^ (p - 2) • (x - x0)) x :=
  hasGradientAt_powerDistance_of_one_lt (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hp) x0 x

/-- The power-distance is differentiable at every point when `p ≥ 2`. -/
theorem differentiableAt_powerDistance
    {p : ℝ} (hp : 2 ≤ p) (x0 x : E) :
    DifferentiableAt ℝ (powerDistance p x0) x :=
  (hasGradientAt_powerDistance hp x0 x).differentiableAt

/-- The power-distance is differentiable on the whole space when `p ≥ 2`. -/
theorem differentiable_powerDistance
    {p : ℝ} (hp : 2 ≤ p) (x0 : E) :
    Differentiable ℝ (powerDistance p x0) :=
  fun x ↦ differentiableAt_powerDistance hp x0 x

end Gradient

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {Q : Set E} {d : E → ℝ} {p σp : ℝ}

local notation "gradQ" => gradientWithin d Q

/- Lemma 4.2.2 lies in the chapter's uniformly convex differentiable-analysis domain on real
Hilbert spaces.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* `uniformConvexPowerModulus` in `Definition_4_2_8`
* `UniformConvexOn.lower_tangent_power_of_hasGradientWithinAt` in `Definition_4_2_8`
* `UniformConvexOn.lower_tangent_power` in `Definition_4_2_8`
* mathlib `Real.HolderConjugate.conjExponent` and `Real.young_inequality_of_nonneg`

Best owner abstraction:
* source-facing: the Bregman-gap upper bound from Lemma 4.2.2, with the within-gradients at
  `x` and `y`
* core/canonical: `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* bridge/view: the stronger comparison-vector form, where the tangent model at `x` is replaced by
  an arbitrary comparison vector and only the tangent model at `y` is required to come from an
  actual within-set gradient

Primitive data:
* the feasible set `Q`
* the objective `d`
* the power parameter `p` and modulus parameter `σp`
* the canonical owner predicate `UniformConvexOn Q (uniformConvexPowerModulus σp p) d`
* feasible points `x` and `y`
* the canonical within-gradients `gradientWithin d Q x` and `gradientWithin d Q y`, under
  differentiability at those points

Derived API:
* the pointwise lower-tangent inequality from
  `UniformConvexOn.lower_tangent_power_of_hasGradientWithinAt`
* the dual-exponent scalar estimate from Young's inequality, factored into a private helper
* an internal comparison-vector reduction, obtained by allowing an arbitrary `gx` at `x`

This file keeps only the source-facing two-gradient inequality as public API and treats the
arbitrary-comparison-vector estimate as private bridge/view scaffolding built on the same
owner-level uniform-convexity predicate.
-/

namespace UniformConvexOn

private theorem young_gap_le_gradient_sub_rpow
    (hp : 1 < p)
    (hσp : 0 < σp)
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    a * b - ((1 / p) * σp * b ^ p) ≤
      ((p - 1) / p) * (1 / σp) ^ (1 / (p - 1)) * a ^ (p / (p - 1)) := by
  have hp_ne : p ≠ 0 := by positivity
  let q : ℝ := Real.conjExponent p
  have hpq : Real.HolderConjugate p q := Real.HolderConjugate.conjExponent hp
  let σroot : ℝ := σp ^ (1 / p)
  have hσroot_nonneg : 0 ≤ σroot := by
    dsimp [σroot]
    exact Real.rpow_nonneg hσp.le _
  have hσroot_ne : σroot ≠ 0 := by
    dsimp [σroot]
    positivity
  have hyoung := Real.young_inequality_of_nonneg
    (show 0 ≤ σroot * b by positivity)
    (show 0 ≤ a / σroot by positivity) hpq
  have hσroot_pow : σroot ^ p = σp := by
    dsimp [σroot]
    simpa [one_div] using Real.rpow_inv_rpow hσp.le hp_ne
  have hfirst : (σroot * b) ^ p / p = ((1 / p) * σp * b ^ p) := by
    rw [div_eq_mul_inv, Real.mul_rpow hσroot_nonneg hb, hσroot_pow]
    ring
  have hq_inv : q⁻¹ = (p - 1) / p := by
    dsimp [q, Real.conjExponent]
    field_simp [hp_ne, sub_ne_zero.mpr hp.ne']
  have hexp : (1 / p) * (p / (p - 1)) = 1 / (p - 1) := by
    field_simp [hp_ne, sub_ne_zero.mpr hp.ne']
  have hσroot_rpow_q : σroot ^ q = σp ^ (1 / (p - 1)) := by
    calc
      σroot ^ q = σp ^ ((1 / p) * (p / (p - 1))) := by
        dsimp [σroot, q, Real.conjExponent]
        rw [Real.rpow_mul hσp.le]
      _ = σp ^ (1 / (p - 1)) := by
        rw [hexp]
  have hinv : (σp ^ (1 / (p - 1)))⁻¹ = (1 / σp) ^ (1 / (p - 1)) := by
    simpa [one_div] using (Real.inv_rpow hσp.le (1 / (p - 1))).symm
  have hsecond : (a / σroot) ^ q / q =
      ((p - 1) / p) * (1 / σp) ^ (1 / (p - 1)) * a ^ (p / (p - 1)) := by
    rw [Real.div_rpow ha hσroot_nonneg, div_eq_mul_inv, div_eq_mul_inv,
      hq_inv, hσroot_rpow_q, hinv]
    dsimp [q, Real.conjExponent]
    ring
  have hleft : σroot * b * (a / σroot) = a * b := by
    field_simp [σroot, hσroot_ne]
  rw [hleft, hfirst, hsecond] at hyoung
  linarith

-- Internal bridge/view reduction: the tangent model at `x` is replaced by an arbitrary
-- comparison vector `gx`, while `gy` remains an actual within-set gradient at `y`.
private theorem comparison_gap_le_gradient_sub_rpow_of_hasGradientWithinAt
    (huc : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (hp : 1 < p)
    (hσp : 0 < σp)
    {x y gx gy : E}
    (hx : x ∈ Q)
    (hy : y ∈ Q)
    (hdy : HasGradientWithinAt d gy Q y) :
    d y - d x - inner ℝ gx (y - x) ≤
      ((p - 1) / p) * Real.rpow (1 / σp) (1 / (p - 1)) *
        Real.rpow ‖gy - gx‖ (p / (p - 1)) := by
  have hlower :=
    huc.lower_tangent_power_of_hasGradientWithinAt y hy gy hdy x hx
  have hsub : x - y = -(y - x) := by
    simp [sub_eq_add_neg]
  rw [hsub, inner_neg_right, norm_neg] at hlower
  have hdyx :
      d y - d x ≤ inner ℝ gy (y - x) - uniformConvexPowerModulus σp p ‖y - x‖ := by
    linarith
  have hgap :
      d y - d x - inner ℝ gx (y - x) ≤
        inner ℝ (gy - gx) (y - x) -
          uniformConvexPowerModulus σp p ‖y - x‖ := by
    calc
      d y - d x - inner ℝ gx (y - x)
          ≤ (inner ℝ gy (y - x) - uniformConvexPowerModulus σp p ‖y - x‖) -
              inner ℝ gx (y - x) := by
            linarith
      _ = inner ℝ (gy - gx) (y - x) - uniformConvexPowerModulus σp p ‖y - x‖ := by
        rw [inner_sub_left]
        ring
  have hinner :
      inner ℝ (gy - gx) (y - x) - uniformConvexPowerModulus σp p ‖y - x‖ ≤
        ((p - 1) / p) * Real.rpow (1 / σp) (1 / (p - 1)) *
          Real.rpow ‖gy - gx‖ (p / (p - 1)) := by
    have hnorm :
        inner ℝ (gy - gx) (y - x) ≤ ‖gy - gx‖ * ‖y - x‖ :=
      real_inner_le_norm _ _
    calc
      inner ℝ (gy - gx) (y - x) - uniformConvexPowerModulus σp p ‖y - x‖
          ≤ ‖gy - gx‖ * ‖y - x‖ - uniformConvexPowerModulus σp p ‖y - x‖ := by
            linarith
      _ ≤ ((p - 1) / p) * Real.rpow (1 / σp) (1 / (p - 1)) *
            Real.rpow ‖gy - gx‖ (p / (p - 1)) := by
          simpa [uniformConvexPowerModulus] using
            young_gap_le_gradient_sub_rpow hp hσp (norm_nonneg _) (norm_nonneg _)
  exact hgap.trans hinner

/-- Lemma 4.2.2 in source-facing form: for a degree-`p` uniformly convex function, the Bregman
gap between two feasible points is controlled by the dual power of the difference of their
canonical within-gradients. -/
theorem tangent_gap_le_gradient_sub_rpow
    (huc : UniformConvexOn Q (uniformConvexPowerModulus σp p) d)
    (hp : 1 < p)
    (hσp : 0 < σp)
    {x y : E}
    (hx : x ∈ Q)
    (hy : y ∈ Q)
    (hdx : DifferentiableWithinAt ℝ d Q x)
    (hdy : DifferentiableWithinAt ℝ d Q y) :
    d y - d x - inner ℝ (gradQ x) (y - x) ≤
      ((p - 1) / p) * Real.rpow (1 / σp) (1 / (p - 1)) *
        Real.rpow ‖gradQ y - gradQ x‖ (p / (p - 1)) := by
  let gx := gradQ x
  let gy := gradQ y
  have hgx : HasGradientWithinAt d gx Q x := by
    simpa [gx] using hdx.hasGradientWithinAt
  have hgy : HasGradientWithinAt d gy Q y := by
    simpa [gy] using hdy.hasGradientWithinAt
  simpa [gx, gy] using
    comparison_gap_le_gradient_sub_rpow_of_hasGradientWithinAt
      huc hp hσp hx hy hgy

end UniformConvexOn

end

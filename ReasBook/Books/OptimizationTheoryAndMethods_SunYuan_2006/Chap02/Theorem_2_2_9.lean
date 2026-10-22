/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.OrderClosed
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1

noncomputable section

open MeasureTheory
open scoped Gradient RealInnerProductSpace

-- Semantic recall: the canonical owner for the companion theorem is
-- `StrongConvexOn Set.univ η f`, while the source theorem itself is phrased through a
-- strong-monotonicity inequality for `∇ f`. This file keeps the source-facing Chapter 2
-- exact-line-search owner `IsExactLineSearchStepOnNonnegativeRay`, whose objective profile is
-- `lineSearchObjective`.

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace StrongConvexOn

/-- A differentiable globally `η`-strongly convex function has an `η`-strongly monotone
gradient. -/
theorem gradientStrongMonotone_univ {f : E → ℝ} {η : ℝ}
    (hStrong : StrongConvexOn Set.univ η f)
    (h_hasGradient : ∀ x : E, HasGradientAt f (∇ f x) x) :
    ∀ x z : E,
      inner ℝ (x - z) (∇ f x - ∇ f z) ≥ η * ‖x - z‖ ^ 2 := by
  let g : E → ℝ := fun x ↦ f x - (η / 2) * ‖x‖ ^ 2
  -- Repackage strong convexity as ordinary convexity after subtracting the quadratic term.
  have hg_convex : ConvexOn ℝ Set.univ g := by
    simpa [g] using
      (strongConvexOn_iff_convex (s := Set.univ) (m := η) (f := f)).mp hStrong
  -- The shifted function has the expected gradient `∇ f x - η • x`.
  have hg_hasGradient : ∀ x : E, HasGradientAt g (∇ f x - η • x) x := by
    intro x
    have hf' : HasFDerivAt f (InnerProductSpace.toDual ℝ E (∇ f x)) x := by
      simpa [hasGradientAt_iff_hasFDerivAt] using h_hasGradient x
    have hquad' : HasFDerivAt (fun y : E ↦ ‖y‖ ^ 2 * (η / 2))
        ((η / 2) • (2 • innerSL ℝ x)) x := by
      simpa [mul_comm] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (η / 2)
    have hsub :
        HasFDerivAt (fun y : E ↦ f y - ‖y‖ ^ 2 * (η / 2))
          ((InnerProductSpace.toDual ℝ E) (∇ f x) - ((η / 2) • (2 • innerSL ℝ x))) x :=
      hf'.sub hquad'
    have hmap :
        (InnerProductSpace.toDual ℝ E) (∇ f x) - ((η / 2) • (2 • innerSL ℝ x)) =
          (InnerProductSpace.toDual ℝ E) (∇ f x - η • x) := by
      apply ContinuousLinearMap.ext
      intro y
      simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, real_inner_smul_left,
        sub_eq_add_neg, smul_smul, mul_assoc, mul_left_comm, mul_comm]
      ring
    have hsub' :
        HasFDerivAt (fun y : E ↦ f y - ‖y‖ ^ 2 * (η / 2))
          ((InnerProductSpace.toDual ℝ E) (∇ f x - η • x)) x := by
      simpa [hmap] using hsub
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa [g, mul_comm] using hsub'
  intro x z
  let φ : ℝ → ℝ := lineSearchObjective g z (x - z)
  have hφ_eq : φ = g ∘ AffineMap.lineMap z x := by
    funext t
    change g (z + t • (x - z)) = g (AffineMap.lineMap z x t)
    congr 1
    rw [AffineMap.lineMap_apply_module, smul_sub]
    calc
      z + (t • x - t • z) = t • x + (z - t • z) := by abel
      _ = t • x + ((1 - t) • z) := by
        congr 1
        simpa [one_smul] using (sub_smul 1 t z).symm
      _ = (1 - t) • z + t • x := by ac_rfl
  have hφ_convex : ConvexOn ℝ Set.univ φ := by
    rw [hφ_eq]
    simpa using (hg_convex.comp_affineMap (AffineMap.lineMap z x))
  have hφ_diff : ∀ t : ℝ, DifferentiableAt ℝ φ t := by
    intro t
    have hray :
        DifferentiableAt ℝ (fun s : ℝ ↦ z + s • (x - z)) t := by
      simpa using ((differentiableAt_id' t).smul_const (x - z)).const_add z
    change DifferentiableAt ℝ (fun s : ℝ ↦ g (z + s • (x - z))) t
    exact (hg_hasGradient (z + t • (x - z))).differentiableAt.comp t hray
  have hleft :
      deriv φ 0 ≤ slope φ 0 1 :=
    hφ_convex.deriv_le_slope (by simp) (by simp) zero_lt_one (hφ_diff 0)
  have hright :
      slope φ 0 1 ≤ deriv φ 1 :=
    hφ_convex.slope_le_deriv (by simp) (by simp) zero_lt_one (hφ_diff 1)
  have hmono_line :
      inner ℝ (∇ f z - η • z) (x - z) ≤
        inner ℝ (∇ f x - η • x) (x - z) := by
    have hzGrad : HasGradientAt g (∇ f z - η • z) (z + (0 : ℝ) • (x - z)) := by
      simpa using hg_hasGradient z
    have hxGrad : HasGradientAt g (∇ f x - η • x) (z + (1 : ℝ) • (x - z)) := by
      simpa using hg_hasGradient x
    calc
      inner ℝ (∇ f z - η • z) (x - z) = deriv φ 0 := by
        symm
        simpa [φ] using
          hzGrad.deriv_lineSearchObjective_apply (x := z) (d := x - z) (t := 0)
      _ ≤ slope φ 0 1 := hleft
      _ ≤ deriv φ 1 := hright
      _ = inner ℝ (∇ f x - η • x) (x - z) := by
        simpa [eq_comm, φ] using
          hxGrad.deriv_lineSearchObjective_apply (x := z) (d := x - z) (t := 1)
  have hmono_g :
      0 ≤ inner ℝ (x - z) ((∇ f x - η • x) - (∇ f z - η • z)) := by
    have hrewrite_line :
        inner ℝ (x - z) ((∇ f x - η • x) - (∇ f z - η • z)) =
          inner ℝ (x - z) (∇ f x - η • x) -
            inner ℝ (x - z) (∇ f z - η • z) := by
      rw [inner_sub_right]
    rw [hrewrite_line]
    simpa [sub_eq_add_neg, real_inner_comm] using sub_nonneg.mpr hmono_line
  have hshift :
      (∇ f x - η • x) - (∇ f z - η • z) = (∇ f x - ∇ f z) - η • (x - z) := by
    simp [sub_eq_add_neg, smul_sub, add_comm, add_left_comm, add_assoc]
  have hrewrite :
      inner ℝ (x - z) ((∇ f x - η • x) - (∇ f z - η • z)) =
        inner ℝ (x - z) (∇ f x - ∇ f z) - η * ‖x - z‖ ^ 2 := by
    rw [hshift, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hrewrite] at hmono_g
  linarith

end StrongConvexOn

end

section Theorem229

variable {Point : Type*} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [CompleteSpace Point]

/-- Helper for Chapter02 Theorem 2.2.9: a positive exact line-search step is stationary on the
interior of the nonnegative ray. -/
lemma exactLineSearch_stationary_inner_eq_zero_of_pos
    (f : Point → ℝ) (xk dk : Point) (αk : ℝ)
    (hαk : 0 < αk)
    (h_exactLineSearch : IsExactLineSearchStepOnNonnegativeRay f xk dk αk)
    (h_hasGradient : ∀ x : Point, HasGradientAt f (∇ f x) x) :
    inner ℝ (∇ f (xk + αk • dk)) dk = 0 := by
  -- Positive exact steps lie in the interior of `Set.Ici 0`, so exact optimality gives a
  -- genuine local minimum for the ray profile.
  have hnhds : Set.Ici 0 ∈ nhds αk := Ici_mem_nhds hαk
  have hlocal : IsLocalMin (lineSearchObjective f xk dk) αk :=
    h_exactLineSearch.isMinOn.isLocalMin hnhds
  have hderivzero : deriv (lineSearchObjective f xk dk) αk = 0 := hlocal.deriv_eq_zero
  -- The derivative of the line-search objective is the gradient paired with the search direction.
  have hderiv :
      deriv (lineSearchObjective f xk dk) αk =
        inner ℝ (∇ f (xk + αk • dk)) dk :=
    (h_hasGradient (xk + αk • dk)).deriv_lineSearchObjective_apply (x := xk) (d := dk) (t := αk)
  rw [hderivzero] at hderiv
  simpa [eq_comm] using hderiv

/-- Helper for Chapter02 Theorem 2.2.9: strong gradient monotonicity along the search ray makes
the shifted directional derivative monotone. -/
lemma ray_gradient_inner_shifted_monotone
    (f : Point → ℝ) (xk dk : Point) (η : ℝ)
    (h_gradientStrongMonotone :
      ∀ x z : Point,
        inner ℝ (x - z) (∇ f x - ∇ f z) ≥ η * ‖x - z‖ ^ 2) :
    Monotone (fun t : ℝ ↦
      inner ℝ (∇ f (xk + t • dk)) dk - η * t * ‖dk‖ ^ 2) := by
  intro s t hst
  by_cases hEq : s = t
  · simp [hEq]
  have hlt : s < t := lt_of_le_of_ne hst hEq
  have hmono := h_gradientStrongMonotone (xk + t • dk) (xk + s • dk)
  have hts_nonneg : 0 ≤ t - s := sub_nonneg.mpr hst
  have hsub_ray : (xk + t • dk) - (xk + s • dk) = (t - s) • dk := by
    calc
      (xk + t • dk) - (xk + s • dk) = xk + t • dk + -(xk + s • dk) := by
        simp [sub_eq_add_neg]
      _ = t • dk - s • dk := by abel
      _ = (t - s) • dk := by rw [sub_smul]
  have hrewrite_left :
      inner ℝ ((xk + t • dk) - (xk + s • dk))
        (∇ f (xk + t • dk) - ∇ f (xk + s • dk)) =
          (t - s) *
            (inner ℝ (∇ f (xk + t • dk)) dk -
              inner ℝ (∇ f (xk + s • dk)) dk) := by
    rw [hsub_ray, real_inner_smul_left, inner_sub_right, real_inner_comm dk (∇ f (xk + t • dk)),
      real_inner_comm dk (∇ f (xk + s • dk))]
  have hnorm_ray :
      ‖(xk + t • dk) - (xk + s • dk)‖ ^ 2 =
        (t - s) * ((t - s) * ‖dk‖ ^ 2) := by
    rw [hsub_ray, norm_smul, Real.norm_eq_abs, abs_of_nonneg hts_nonneg, pow_two]
    ring
  have hrewrite_right :
      η * ‖(xk + t • dk) - (xk + s • dk)‖ ^ 2 =
        (t - s) * (η * (t - s) * ‖dk‖ ^ 2) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun r : ℝ ↦ η * r) hnorm_ray
  rw [hrewrite_left, hrewrite_right] at hmono
  have hscaled :
      (t - s) * (η * (t - s) * ‖dk‖ ^ 2) ≤
        (t - s) *
          (inner ℝ (∇ f (xk + t • dk)) dk -
            inner ℝ (∇ f (xk + s • dk)) dk) := by
    linarith
  have hstep :
      η * (t - s) * ‖dk‖ ^ 2 ≤
        inner ℝ (∇ f (xk + t • dk)) dk -
          inner ℝ (∇ f (xk + s • dk)) dk :=
    le_of_mul_le_mul_left hscaled (sub_pos.mpr hlt)
  linarith

/-- Helper for Chapter02 Theorem 2.2.9: the ray derivative is interval-integrable because it is
the sum of a monotone shifted term and an affine term. -/
lemma ray_gradient_inner_intervalIntegrable
    (f : Point → ℝ) (xk dk : Point) (αk η : ℝ)
    (h_gradientStrongMonotone :
      ∀ x z : Point,
        inner ℝ (x - z) (∇ f x - ∇ f z) ≥ η * ‖x - z‖ ^ 2) :
    IntervalIntegrable (fun t : ℝ ↦ inner ℝ (∇ f (xk + t • dk)) dk) MeasureTheory.volume 0 αk := by
  have hshift :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ (∇ f (xk + t • dk)) dk - η * t * ‖dk‖ ^ 2)
        MeasureTheory.volume 0 αk :=
    (ray_gradient_inner_shifted_monotone f xk dk η h_gradientStrongMonotone).intervalIntegrable
  have hlinear :
      IntervalIntegrable (fun t : ℝ ↦ η * t * ‖dk‖ ^ 2) MeasureTheory.volume 0 αk := by
    exact (by continuity : Continuous fun t : ℝ ↦ η * t * ‖dk‖ ^ 2).intervalIntegrable 0 αk
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hshift.add hlinear

/-- Helper for Chapter02 Theorem 2.2.9: integrating the affine lower bound on the search ray
produces the half-square coefficient. -/
lemma integral_affine_lineSearch_lowerBound
    (dk : Point) (αk η : ℝ) :
    ∫ t in 0..αk, η * (αk - t) * ‖dk‖ ^ 2 = (η / 2) * ‖αk • dk‖ ^ 2 := by
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ αk) MeasureTheory.volume 0 αk :=
    intervalIntegrable_const
  have hid : IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 αk :=
    continuous_id.intervalIntegrable 0 αk
  have hsub : ∫ t in 0..αk, (αk - t) = αk ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub hconst hid, intervalIntegral.integral_const]
    have hid' : ∫ t in 0..αk, t = αk ^ 2 / 2 := by
      have hderiv :
          ∀ t ∈ Set.uIcc (0 : ℝ) αk, HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
        intro t ht
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
          ((hasDerivAt_pow 2 t).const_mul (1 / (2 : ℝ)))
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s : ℝ ↦ s ^ 2 / 2) hderiv hid
      simpa [pow_two] using hftc
    rw [hid']
    ring
  calc
    ∫ t in 0..αk, η * (αk - t) * ‖dk‖ ^ 2 =
        (η * ‖dk‖ ^ 2) * ∫ t in 0..αk, (αk - t) := by
          rw [show (fun t : ℝ ↦ η * (αk - t) * ‖dk‖ ^ 2) =
            fun t : ℝ ↦ (η * ‖dk‖ ^ 2) * (αk - t) by
              funext t
              ring, intervalIntegral.integral_const_mul]
    _ = (η * ‖dk‖ ^ 2) * (αk ^ 2 / 2) := by rw [hsub]
    _ = (η / 2) * ‖αk • dk‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : (|αk| * ‖dk‖) ^ 2 = αk ^ 2 * ‖dk‖ ^ 2 := by
        calc
          (|αk| * ‖dk‖) ^ 2 = |αk| ^ 2 * ‖dk‖ ^ 2 := by ring
          _ = αk ^ 2 * ‖dk‖ ^ 2 := by rw [sq_abs]
      rw [habs]
      ring

/-- Chapter02 Theorem 2.2.9: if `αk` is an exact line-search step from `xk` along `dk` on
the nonnegative ray in the Chapter 2 sense
`IsExactLineSearchStepOnNonnegativeRay f xk dk αk`, equivalently when
`lineSearchObjective f xk dk` attains its minimum on `Set.Ici 0` at `αk`, and
`f` has a globally `η`-strongly monotone gradient in the sense that
`inner ℝ (x - z) (∇ f x - ∇ f z) ≥ η * ‖x - z‖^2` for all `x, z`, then the
exact line-search decrease is bounded below by `(η / 2) * ‖αk • dk‖^2`. -/
theorem exactLineSearch_decrease_ge_half_mul_eta_mul_stepNormSq_of_gradient_strongMonotone
    (f : Point → ℝ) (xk dk : Point) (αk η : ℝ)
    (h_exactLineSearch : IsExactLineSearchStepOnNonnegativeRay f xk dk αk)
    (h_hasGradient : ∀ x : Point, HasGradientAt f (∇ f x) x)
    (h_gradientStrongMonotone :
      ∀ x z : Point,
        inner ℝ (x - z) (∇ f x - ∇ f z) ≥ η * ‖x - z‖ ^ 2) :
    f xk - f (xk + αk • dk) ≥ (η / 2) * ‖αk • dk‖ ^ 2 := by
  by_cases hαk_zero : αk = 0
  · -- The zero-step branch is exactly the trivial equality case.
    simp [hαk_zero]
  have hαk_nonneg : 0 ≤ αk := h_exactLineSearch.nonneg
  have hαk_pos : 0 < αk := lt_of_le_of_ne hαk_nonneg (by simpa [eq_comm] using hαk_zero)
  have hstationary :
      inner ℝ (∇ f (xk + αk • dk)) dk = 0 :=
    exactLineSearch_stationary_inner_eq_zero_of_pos f xk dk αk hαk_pos h_exactLineSearch
      h_hasGradient
  have hψ_int :
      IntervalIntegrable (fun t : ℝ ↦ inner ℝ (∇ f (xk + t • dk)) dk) MeasureTheory.volume 0 αk :=
    ray_gradient_inner_intervalIntegrable f xk dk αk η h_gradientStrongMonotone
  have hnegψ_int :
      IntervalIntegrable (fun t : ℝ ↦ -inner ℝ (∇ f (xk + t • dk)) dk) MeasureTheory.volume 0 αk :=
    hψ_int.neg
  have hlower_int :
      IntervalIntegrable (fun t : ℝ ↦ η * (αk - t) * ‖dk‖ ^ 2) MeasureTheory.volume 0 αk := by
    exact (by continuity : Continuous fun t : ℝ ↦ η * (αk - t) * ‖dk‖ ^ 2).intervalIntegrable 0 αk
  -- Rewrite the decrease as the integral of the negative directional derivative.
  have hdecrease_eq :
      f xk - f (xk + αk • dk) =
        ∫ t in 0..αk, -inner ℝ (∇ f (xk + t • dk)) dk := by
    have hftc :
        ∫ t in 0..αk, inner ℝ (∇ f (xk + t • dk)) dk =
          f (xk + αk • dk) - f xk := by
      have hftc' :
          ∫ t in 0..αk, inner ℝ (∇ f (xk + t • dk)) dk =
            lineSearchObjective f xk dk αk - lineSearchObjective f xk dk 0 := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := lineSearchObjective f xk dk) ?_ hψ_int
        intro t ht
        have hDiff :
            DifferentiableAt ℝ (lineSearchObjective f xk dk) t := by
          have hray :
              DifferentiableAt ℝ (fun s : ℝ ↦ xk + s • dk) t := by
            simpa using ((differentiableAt_id' t).smul_const dk).const_add xk
          change DifferentiableAt ℝ (fun s : ℝ ↦ f (xk + s • dk)) t
          exact (h_hasGradient (xk + t • dk)).differentiableAt.comp t hray
        have hDerivEq :
            deriv (lineSearchObjective f xk dk) t =
              inner ℝ (∇ f (xk + t • dk)) dk :=
          (h_hasGradient (xk + t • dk)).deriv_lineSearchObjective_apply (x := xk) (d := dk) (t := t)
        exact hDerivEq ▸ hDiff.hasDerivAt
      simpa [lineSearchObjective_apply, lineSearchObjective_zero] using hftc'
    calc
      f xk - f (xk + αk • dk) = -(f (xk + αk • dk) - f xk) := by ring
      _ = -(∫ t in 0..αk, inner ℝ (∇ f (xk + t • dk)) dk) := by rw [hftc]
      _ = ∫ t in 0..αk, -inner ℝ (∇ f (xk + t • dk)) dk := by
        rw [intervalIntegral.integral_neg]
  -- Strong monotonicity along the ray bounds the negative directional derivative from below.
  have hpointwise :
      ∀ t ∈ Set.Icc 0 αk,
        η * (αk - t) * ‖dk‖ ^ 2 ≤ -inner ℝ (∇ f (xk + t • dk)) dk := by
    intro t ht
    by_cases hEq : αk = t
    · subst hEq
      simp [hstationary]
    have hfac_nonneg : 0 ≤ αk - t := sub_nonneg.mpr ht.2
    have hfac_pos : 0 < αk - t := lt_of_le_of_ne hfac_nonneg (by simpa [sub_eq_zero, eq_comm] using hEq)
    have hmono := h_gradientStrongMonotone (xk + αk • dk) (xk + t • dk)
    have hsub_ray : (xk + αk • dk) - (xk + t • dk) = (αk - t) • dk := by
      calc
        (xk + αk • dk) - (xk + t • dk) = xk + αk • dk + -(xk + t • dk) := by
          simp [sub_eq_add_neg]
        _ = αk • dk - t • dk := by abel
        _ = (αk - t) • dk := by rw [sub_smul]
    have hrewrite_left :
        inner ℝ ((xk + αk • dk) - (xk + t • dk))
          (∇ f (xk + αk • dk) - ∇ f (xk + t • dk)) =
            (αk - t) *
              (inner ℝ (∇ f (xk + αk • dk)) dk -
                inner ℝ (∇ f (xk + t • dk)) dk) := by
      rw [hsub_ray, real_inner_smul_left, inner_sub_right,
        real_inner_comm dk (∇ f (xk + αk • dk)), real_inner_comm dk (∇ f (xk + t • dk))]
    have hnorm_ray :
        ‖(xk + αk • dk) - (xk + t • dk)‖ ^ 2 =
          (αk - t) * ((αk - t) * ‖dk‖ ^ 2) := by
      rw [hsub_ray, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac_nonneg, pow_two]
      ring
    have hrewrite_right :
        η * ‖(xk + αk • dk) - (xk + t • dk)‖ ^ 2 =
          (αk - t) * (η * (αk - t) * ‖dk‖ ^ 2) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun r : ℝ ↦ η * r) hnorm_ray
    rw [hrewrite_left, hrewrite_right] at hmono
    have hscaled :
        (αk - t) * (η * (αk - t) * ‖dk‖ ^ 2) ≤
          (αk - t) *
            (inner ℝ (∇ f (xk + αk • dk)) dk -
              inner ℝ (∇ f (xk + t • dk)) dk) := by
      linarith
    have hstep :
        η * (αk - t) * ‖dk‖ ^ 2 ≤
          inner ℝ (∇ f (xk + αk • dk)) dk -
            inner ℝ (∇ f (xk + t • dk)) dk :=
      le_of_mul_le_mul_left hscaled hfac_pos
    linarith [hstep, hstationary]
  have hintegral_lower :
      ∫ t in 0..αk, η * (αk - t) * ‖dk‖ ^ 2 ≤
        ∫ t in 0..αk, -inner ℝ (∇ f (xk + t • dk)) dk :=
    intervalIntegral.integral_mono_on hαk_nonneg hlower_int hnegψ_int hpointwise
  calc
    f xk - f (xk + αk • dk) =
        ∫ t in 0..αk, -inner ℝ (∇ f (xk + t • dk)) dk := hdecrease_eq
    _ ≥ ∫ t in 0..αk, η * (αk - t) * ‖dk‖ ^ 2 := hintegral_lower
    _ = (η / 2) * ‖αk • dk‖ ^ 2 :=
      integral_affine_lineSearch_lowerBound dk αk η

/-- Canonical strong-convexity form of Chapter02 Theorem 2.2.9. -/
theorem exactLineSearch_decrease_ge_half_mul_eta_mul_stepNormSq_of_strongConvex
    (f : Point → ℝ) (xk dk : Point) (αk η : ℝ)
    (h_exactLineSearch : IsExactLineSearchStepOnNonnegativeRay f xk dk αk)
    (h_hasGradient : ∀ x : Point, HasGradientAt f (∇ f x) x)
    (hStrong : StrongConvexOn Set.univ η f) :
    f xk - f (xk + αk • dk) ≥ (η / 2) * ‖αk • dk‖ ^ 2 :=
  exactLineSearch_decrease_ge_half_mul_eta_mul_stepNormSq_of_gradient_strongMonotone
    f xk dk αk η h_exactLineSearch h_hasGradient
    (hStrong.gradientStrongMonotone_univ h_hasGradient)

end Theorem229

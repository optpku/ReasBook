/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_57
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_21
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_25
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace
open ERealFunction

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

private noncomputable def gammaHalf : PosReal := ⟨(1 / 2 : ℝ), by positivity⟩

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

omit [CompleteSpace H] in
/-- The indicator of a nonempty closed convex set belongs to `Γ₀(H)`. -/
theorem indicator_mem_gammaZero_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] ∈ Γ₀(H) := by
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

-- Proof sketch: apply Proposition 12.30 to the indicator of `C` with `γ = 1 / 2`, then use
-- Example 12.21 to identify the Moreau envelope with `x ↦ Metric.infDist x C ^ 2` and
-- Example 12.25 to identify the proximity operator with the metric projection `P_C`.
/-- Corollary 12.31: if `C` is a nonempty closed convex subset of a real Hilbert space, then the
squared distance function `x ↦ Metric.infDist x C ^ 2` is Fréchet differentiable at every point,
with gradient `2 • (x - P_C x)`. -/
theorem sq_infDist_hasGradientAt_of_nonempty_isClosed_convex
    (x : H) :
    HasGradientAt (fun y : H ↦ Metric.infDist y C ^ 2) ((2 : ℝ) • (x - P x)) x := by
  have hindicator : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  have hgradient :
      HasGradientAt (fun y ↦ (({}^[gammaHalf] ι[C]) y).toReal)
        ((gammaHalf : ℝ)⁻¹ • (x - Prox[gammaHalf, ι[C], hindicator] x)) x :=
    moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero (ι[C]) gammaHalf hindicator x
  have hmoreau :
      (fun y ↦ (({}^[gammaHalf] ι[C]) y).toReal) = fun y ↦ Metric.infDist y C ^ 2 := by
    funext y
    have henv := congrArg (fun f : H → EReal ↦ f y) <|
      indicator_moreauEnvelope_eq_scaled_sq_infEDist C gammaHalf
    have henv' :
        (({}^[gammaHalf] ι[C]) y).toReal =
          (((Metric.infEDist y C : EReal) ^ 2 / (2 * (gammaHalf : ℝ) : EReal))).toReal := by
      simpa using congrArg EReal.toReal henv
    have hgamma : (2 * (gammaHalf : ℝ) : EReal) = 1 := by
      change (((2 : ℝ) * (gammaHalf : ℝ) : ℝ) : EReal) = 1
      norm_num [gammaHalf]
    rw [hgamma] at henv'
    have hsq : ((((Metric.infEDist y C : EReal) ^ 2) / 1).toReal) = Metric.infDist y C ^ 2 := by
      simpa [Metric.infDist, pow_two] using
        (show
          (((Metric.infEDist y C : EReal) * (Metric.infEDist y C : EReal)).toReal =
            (Metric.infEDist y C : EReal).toReal * (Metric.infEDist y C : EReal).toReal) from
          EReal.toReal_mul)
    exact henv'.trans hsq
  have hprox : Prox[gammaHalf, ι[C], hindicator] = P := by
    have hsmul_indicator : gammaHalf • ι[C] = ι[C] := by
      funext y
      apply Subtype.ext
      by_cases hy : y ∈ C
      · simp [gammaHalf, ERealFunction.indicator, hy]
      · simpa [gammaHalf, ERealFunction.indicator, hy] using
          (EReal.coe_mul_top_of_pos gammaHalf.2 : ((gammaHalf : ℝ) : EReal) * ⊤ = ⊤)
    ext y
    simpa [scaledProximityOperator, hsmul_indicator] using
      congrArg (fun f : H → H ↦ f y) <|
      proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex
  rw [hmoreau, hprox] at hgradient
  simpa [gammaHalf] using hgradient

-- Proof sketch: apply `gradient_eq` to the pointwise gradient formula from
-- `sq_infDist_hasGradientAt_of_nonempty_isClosed_convex`.
/-- The gradient of the squared distance to a nonempty closed convex set is `2 • (Id - P_C)`. -/
theorem gradient_sq_infDist_eq_two_smul_sub_projectionPoint_of_nonempty_isClosed_convex
    :
    ∇ (fun y : H ↦ Metric.infDist y C ^ 2) = fun x : H ↦ (2 : ℝ) • (x - P x) :=
  gradient_eq <|
    sq_infDist_hasGradientAt_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

end

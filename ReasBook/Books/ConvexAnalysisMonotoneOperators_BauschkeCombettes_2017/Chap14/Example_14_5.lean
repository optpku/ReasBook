/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Example_4_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_16
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section ProximityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use Moreau's decomposition with `(ρ ‖·‖)^* = ι_{B(0;ρ)}`, identify the proximity
-- operator of that indicator with the metric projection onto `B(0;ρ)`, and then invoke the
-- Chapter 4 owner `softThresholder`.
/-- Example 14.5: for the scaled-norm kernel `f = ρ ‖·‖` with `ρ ∈ ℝ_{++}`, the proximal
operator `Prox_f` is the soft thresholder with threshold `ρ`. -/
theorem proximityOperator_scaledNorm_eq_softThresholder
    (ρ : Set.Ioi (0 : ℝ)) :
    Prox[scaledNormKernelOfPos ρ, scaledNormKernelOfPos_mem_gammaZero ρ] =
      (softThresholder (ρ : ℝ) : H → H) := sorry

/-- Evaluating the proximal operator of the scaled-norm kernel yields the standard soft-threshold
formula. -/
theorem proximityOperator_scaledNorm_apply
    (ρ : Set.Ioi (0 : ℝ)) (x : H) :
    Prox[scaledNormKernelOfPos ρ, scaledNormKernelOfPos_mem_gammaZero ρ] x =
      if (ρ : ℝ) < ‖x‖ then (1 - (ρ : ℝ) / ‖x‖) • x else 0 := by
  simpa [softThresholder_apply] using
    congrFun (proximityOperator_scaledNorm_eq_softThresholder ρ) x

end ProximityOperator

section MoreauEnvelope

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: rewrite the unit Moreau envelope as the Fenchel conjugate of
-- `ι_{B(0;ρ)} + ‖·‖² / 2`, then apply the Chapter 13 owner
-- `fenchelConjugate_indicator_add_halfSquaredNorm_closedBall_eq_huberFunction_comp_norm`.
/-- The unit Moreau envelope of the scaled-norm kernel is the radial Huber profile
`u ↦ huberFunction ρ ‖u‖`, viewed in `EReal`. -/
theorem moreauEnvelope_scaledNorm_eq_huberFunction_comp_norm
    (ρ : Set.Ioi (0 : ℝ)) :
    {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (scaledNormKernelOfPos ρ) =
      (huberFunction ρ ∘ (norm : H → ℝ)).toEReal.asEReal := sorry

end MoreauEnvelope

-- Proof sketch: specialize the Hilbert-space radial formula to `H = ℝ`, where the radial Huber
-- profile becomes the scalar owner `huberFunction ρ`.
/-- In one dimension, the unit Moreau envelope of the scaled-norm kernel is the canonical
extended-real Huber function with threshold `ρ`. -/
theorem moreauEnvelope_scaledNorm_real_eq_huberFunction
    (ρ : Set.Ioi (0 : ℝ)) :
    {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (scaledNormKernelOfPos ρ) =
      (huberFunction ρ).toEReal.asEReal := by
  calc
    {}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (scaledNormKernelOfPos ρ) =
        (huberFunction ρ ∘ (norm : ℝ → ℝ)).toEReal.asEReal :=
          moreauEnvelope_scaledNorm_eq_huberFunction_comp_norm ρ
    _ = (huberFunction ρ).toEReal.asEReal := by
      funext x
      by_cases hx : (ρ : ℝ) < |x|
      · simp [Function.comp_def, huberFunction, Real.norm_eq_abs, hx]
      · simp [Function.comp_def, huberFunction, Real.norm_eq_abs, hx]

end

end ERealFunction

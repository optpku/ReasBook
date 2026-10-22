/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Definition_14_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

noncomputable section

universe u

namespace ERealFunction

section StrongerDifferentiabilityNotions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: specialize the Chapter 18 generator `h = (Σ i, α i (fᵢ* □ q))^* - q` to the two
-- weights `α₁ = α₂ = 1 / 2`, rewrite the sum as the average of the two unit Moreau envelopes of
-- `f₁*` and `f₂*`, and then apply the identification of that equal-weight case with the proximal
-- average from Corollary 14.8(4).
/-- Remark 18.21: for two functions `f₁, f₂ ∈ Γ₀(H)`, the function `h` from `(18.40)` specialized
to the equal weights `α₁ = α₂ = 1 / 2` is exactly the proximal average `pav(f₁, f₂)`. -/
theorem equalWeight_conjugateSubInvHalfSquaredNorm_eq_proximalAverage
    (f₁ f₂ : H → Set.Ioi (⊥ : EReal)) (hf₁ : f₁ ∈ Γ₀(H)) (hf₂ : f₂ ∈ Γ₀(H)) :
    (fun x : H ↦
      (conjugateSubInvHalfSquaredNorm
        (fun y : H ↦
          (1 / 2 : ℝ) *
              (({}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (gammaZeroConjugate f₁ hf₁)) y).toReal +
            (1 / 2 : ℝ) *
              (({}^[⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩] (gammaZeroConjugate f₂ hf₂)) y).toReal)
        ⟨(1 : ℝ), Set.mem_Ioi.2 zero_lt_one⟩ x : EReal)) =
      pav(f₁, f₂) := sorry

end StrongerDifferentiabilityNotions

end ERealFunction

/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: apply Proposition 16.33 to the indicator `ι_C`, whose Fenchel conjugate is the
-- support function `σ[C]`. The minimizers of `ι_C` are exactly the points of `C`, and the
-- nonempty closed convex hypotheses place `ι_C` in `Γ₀(H)`.
/-- Example 16.34: if `C` is a nonempty closed convex subset of a real Hilbert space, then the
subdifferential of its support function at `0` is exactly `C`. -/
theorem subdifferential_supportFunction_eq_self_at_zero_of_nonempty_isClosed_convex
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    (∂ σ[C]) 0 = C := by
  have hC_gamma : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  have hargmin : Argmin ((ι[C]).asEReal) = C := by
    ext x
    constructor
    · intro hx
      rw [mem_argmin_iff, isMinOn_univ_iff] at hx
      by_contra hxC
      rcases hC_nonempty with ⟨y, hy⟩
      simpa [indicator_apply, hxC, hy] using hx y
    · intro hx
      rw [mem_argmin_iff, isMinOn_univ_iff]
      intro y
      by_cases hy : y ∈ C <;> simp [indicator_apply, hx, hy]
  calc
    (∂ σ[C]) 0 = (∂ (((ι[C]).asEReal)∗)) 0 := by
      exact congrArg (fun h : H → EReal ↦ (∂ h) 0)
        (conjugate_indicator_eq_supportFunction C).symm
    _ = Argmin ((ι[C]).asEReal) := by
      simpa [gammaZeroConjugate_apply] using
        (argmin_eq_subdifferential_gammaZeroConjugate_zero (ι[C]) hC_gamma).symm
    _ = C := hargmin

end

end ERealFunction

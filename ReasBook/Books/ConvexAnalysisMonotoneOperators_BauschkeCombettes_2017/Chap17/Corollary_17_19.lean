/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section ToERealHelpers

variable {H : Type u} [NormedAddCommGroup H]

variable [InnerProductSpace ℝ H]

/-- A lower semicontinuous convex real-valued function becomes a member of `Γ₀(H)` after the
canonical coercion `toEReal`. -/
theorem toEReal_mem_gammaZero_of_lowerSemicontinuous_convexOn_univ
    (f : H → ℝ) (hlsc : LowerSemicontinuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    f.toEReal ∈ Γ₀(H) := by
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    have h1ma : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    have hsum : a + (1 - a) = 1 := by ring
    have hreal : f (a • x + (1 - a) • y) ≤ a • f x + (1 - a) • f y :=
      hconv.2 (by simp) (by simp) ha0 h1ma hsum
    change ((f (a • x + (1 - a) • y) : ℝ) : EReal) ≤
      ((a • f x + (1 - a) • f y : ℝ) : EReal)
    exact_mod_cast hreal
  · simpa [Function.comp] using
      continuous_coe_real_ereal.comp_lowerSemicontinuous hlsc
        (show Monotone ((↑) : ℝ → EReal) from by
          intro a b hab
          exact_mod_cast hab)

end ToERealHelpers

section DirectionalDerivativesAndSubgradients

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: first use the canonical Chapter 9 owner theorem
-- `toEReal_mem_gammaZero_of_lowerSemicontinuous_convexOn_univ` to package `f.toEReal` as a
-- member of `Γ₀(H)`, then work with the canonical conjugate owner `(f.toEReal)∗[hf]` and the
-- recession owner `recessionFunction f.toEReal hf.2.nonempty`. Apply Corollary 16.57 for
-- `(ii) → (i)`, combine Corollaries 16.39 and 16.30 with the closedness of the ball for
-- `(ii) ↔ (iii)`, and use Proposition 13.49 together with the support function of the closed ball
-- for `(iii) ↔ (iv)`.
/-- Corollary 17.19: for a lower semicontinuous convex real-valued function on a real Hilbert
space, the following are equivalent: `β`-Lipschitz continuity, containment of the range of the
subdifferential in `B(0;β)`, containment of the effective domain of the Fenchel conjugate in
`B(0;β)`, and the recession bound `rec f ≤ β ‖·‖`. -/
theorem lipschitzWith_tfae_subdifferential_range_conjugateDomain_recession_bound
    (f : H → ℝ) (β : NNReal) (hlsc : LowerSemicontinuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f) :
    let hf := toEReal_mem_gammaZero_of_lowerSemicontinuous_convexOn_univ f hlsc hconv
    List.TFAE
      [LipschitzWith β f,
        SetValuedOperator.range (∂ f.toEReal) ⊆ Metric.closedBall (0 : H) β,
        effectiveDomain ((f.toEReal)∗[hf]) ⊆ Metric.closedBall (0 : H) β,
        ∀ y : H, (recessionFunction f.toEReal hf.2.nonempty y : EReal) ≤
          ((β : ℝ) * ‖y‖ : ℝ)] := sorry

end DirectionalDerivativesAndSubgradients

end ERealFunction

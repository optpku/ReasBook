/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Example_12_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: rewrite `x ↦ φ (d(x, C))` as the infimal convolution of `ι[C]` with the radial
-- kernel `x ↦ φ ‖x‖`, the monotone-radial companion of
-- `distanceToSet_eq_indicator_infimalConvolution_norm` from Example 12.2. Then apply Proposition
-- 13.24(i), Example 13.3(i), and Example 13.8 to identify the three conjugates.
/-- Example 13.26: if `C` is a nonempty closed convex subset of `H` and `φ` is increasing on
`[0, ∞)` and even, then the Fenchel conjugate of `x ↦ φ (d(x, C))` is
`σ[C] + (u ↦ φ^*(‖u‖))`. -/
theorem fenchelConjugate_comp_infDist_eq_supportFunction_add_comp_norm
    (C : Set H) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (φ : ℝ → Set.Ioi (⊥ : EReal))
    (hφ_mono : MonotoneOn φ (Set.Ici (0 : ℝ))) (hφ_even : Function.Even φ) :
    (φ ∘ fun x : H ↦ Metric.infDist x C).asEReal∗ =
      σ[C] + φ.asEReal∗ ∘ norm := sorry

end Conjugation

end ERealFunction

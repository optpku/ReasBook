/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use Theorem 9.20 to minorize `f` by a continuous affine functional
-- `x ↦ ⟪x, u⟫ + η`, divide by `‖x‖`, bound the affine term below by `-‖u‖ + η / ‖x‖`, and then
-- combine this lower bound with the supercoercive growth of `g`. The `Γ₀(H)`-valued wrapper
-- `pointwiseAdd f g` is only a bridge; the supercoercive owner lives on the underlying
-- `EReal`-valued sum.
/-- Proposition 11.14: if `f ∈ Γ₀(H)` and `g` is supercoercive, then the canonical underlying
extended-real-valued pointwise sum `(f + g).asEReal` is supercoercive. -/
theorem pointwiseAdd_supercoercive_of_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hg_super : Supercoercive g.asEReal) :
    Supercoercive (f + g).asEReal := sorry

end ERealFunction

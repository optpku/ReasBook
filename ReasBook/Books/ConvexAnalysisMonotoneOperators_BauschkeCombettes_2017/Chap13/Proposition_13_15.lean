/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Fenchel conjugate of a proper extended-real-valued function never takes the value `-∞`. -/
theorem conjugate_ne_bot_of_isProper
    {f : H → EReal} (hproper : IsProper f) (u : H) :
    f∗ u ≠ ⊥ := by
  rcases hproper.2 with ⟨x, hx⟩
  have hxtop : f x ≠ ⊤ := (mem_dom_iff_ne_top _ _).1 hx
  have hterm : (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ≠ ⊥ := by
    cases hfx : f x with
    | bot => simp
    | top => exact (hxtop hfx).elim
    | coe r => simpa using (EReal.coe_ne_bot (⟪x, u⟫_ℝ - r))
  intro hconj
  apply hterm
  exact le_bot_iff.mp <| hconj ▸ by
    rw [conjugate_apply]
    exact le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) x

-- Proof sketch: if `f x = +∞`, the inequality is immediate. Otherwise, unfold the definition of
-- `f∗ u` and evaluate the defining supremum at the chosen point `x` to get
-- `⟪x,u⟫ - f x ≤ f∗ u`; then rearrange in `EReal`. Properness rules out the `-∞`
-- pathology for `f x`.
/-- Proposition 13.15: for a proper extended-real-valued function on a real inner-product space,
the Fenchel--Young inequality states that `f x + f*(u)` dominates the pairing `⟪x, u⟫`. -/
theorem fenchel_young_inequality
    {f : H → EReal} (hproper : IsProper f) (x u : H) :
    ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ f x + f∗ u := by
  by_cases htop : f x = ⊤
  · have hsum : f x + f∗ u = ⊤ := by
      rw [htop]
      exact EReal.top_add_of_ne_bot (conjugate_ne_bot_of_isProper hproper u)
    rw [hsum]
    exact le_top
  · rw [conjugate_apply]
    simpa [add_comm] using
      (EReal.sub_le_iff_le_add (.inl (hproper.1 x)) (.inl htop)).1 <|
        le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) x

end Conjugation

end ERealFunction

/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_45

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section FenchelMoreau

variable {I : Type v}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use the chapter owner `f.asEReal` for the `EReal` coercion of each `Γ₀(H)`
-- function and its canonical conjugate `(f i).asEReal∗`. Corollary 13.38 identifies every
-- `f i.asEReal` with its biconjugate, Proposition 13.28(i) gives
-- `conjugate (⨅ i, (f i).asEReal∗) = ⨆ i, f i.asEReal`, and
-- Proposition 13.45 turns the resulting biconjugate into the lower semicontinuous convex envelope
-- under the hypothesis that the supremum is not identically `+∞`.
/-- Proposition 13.47: for a family of functions in `Γ₀(H)` whose pointwise supremum is
not identically `+∞`, the Fenchel conjugate of that supremum is the lower semicontinuous convex
envelope of the pointwise infimum of the Fenchel conjugates. -/
theorem conjugate_iSup_eq_lowerSemicontinuousConvexEnvelope_iInf_conjugate_of_mem_gammaZero
    (f : I → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i, f i ∈ Γ₀(H))
    (hfinite : (⨆ i : I, (f i).asEReal) ≠ (⊤ : H → EReal)) :
    (⨆ i : I, (f i).asEReal)∗ =
      lowerSemicontinuousConvexEnvelope
        (⨅ i : I, (f i).asEReal∗) := by
  let g : H → EReal := ⨅ i : I, (f i).asEReal∗
  have hg_conjugate : g∗ = ⨆ i : I, (f i).asEReal := by
    calc
      g∗ = ⨆ i : I, (f i).asEReal∗∗ := by
        simpa [g] using conjugate_iInf_eq_iSup_conjugate (fun i ↦ (f i).asEReal∗)
      _ = ⨆ i : I, (f i).asEReal := by
        exact iSup_congr fun i ↦ biconjugate_eq_of_mem_gammaZero (hf i)
  have hg_dom : (dom g∗).Nonempty := by
    by_contra hdom
    have hg_top : g∗ = (⊤ : H → EReal) := by
      ext x
      by_contra hx
      exact hdom ⟨x, (mem_dom_iff_ne_top _ _).2 hx⟩
    exact hfinite (by simpa [hg_conjugate] using hg_top)
  calc
    (⨆ i : I, (f i).asEReal)∗ = g∗∗ := by
      rw [← hg_conjugate]
    _ = lowerSemicontinuousConvexEnvelope g := by
      exact biconjugate_eq_lowerSemicontinuousConvexEnvelope_of_dom_conjugate_nonempty g hg_dom
    _ = lowerSemicontinuousConvexEnvelope (⨅ i : I, (f i).asEReal∗) := by
      rfl

end FenchelMoreau

end ERealFunction

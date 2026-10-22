/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Proposition_14_19

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply the preceding conjugation identity for the piecewise function equal to
-- `g - h` on `effectiveDomain g` and `+∞` outside it at `u = 0`, then use the canonical origin
-- formula for Fenchel conjugates to rewrite both sides as negative infima. Finally unfold that
-- piecewise expression on the primal side and `dom` on the dual side to recover the displayed
-- source-facing infima.
/-- Corollary 14.20: if `g, h ∈ Γ₀(H)`, then the infimum of `g - h` over `dom g` equals the
infimum of `h* - g*` over `dom h*`. -/
theorem toland_singer_inf_sub_eq_inf_conjugate_sub
    (g h : H → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(H)) (hh : h ∈ Γ₀(H)) :
    sInf ((fun x ↦ g.asEReal x - h.asEReal x) '' effectiveDomain g) =
      sInf
        ((fun v ↦ h.asEReal∗ v - g.asEReal∗ v) '' dom (h.asEReal∗)) := sorry

end Conjugation

end ERealFunction

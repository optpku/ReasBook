/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: the forward implication is Proposition 13.16(ii) applied to the canonical
-- `EReal`-valued owner `f.asEReal`. For the reverse implication, apply Proposition 13.16(ii) to
-- the conjugate inequality to get `f.asEReal∗∗ ≤ g∗∗`, rewrite the left-hand side using
-- Corollary 13.38, and finish with Proposition 13.16(i), which gives `g∗∗ ≤ g`.
/-- Corollary 13.39: for `f ∈ Γ₀(H)` and `g : H → [-∞,+∞]`, one has `f ≤ g` if and only if the
Fenchel conjugates satisfy `f* ≥ g*`. -/
theorem le_iff_conjugate_ge_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {g : H → EReal} :
    f.asEReal ≤ g ↔ f.asEReal∗ ≥ g∗ := by
  constructor
  · intro hfg
    simpa using (conjugate_antitone hfg : g∗ ≤ f.asEReal∗)
  · intro hconj
    calc
      f.asEReal = f.asEReal∗∗ := (biconjugate_eq_of_mem_gammaZero hf).symm
      _ ≤ g∗∗ := conjugate_antitone hconj
      _ ≤ g := biconjugate_le g

end FenchelMoreau

end ERealFunction

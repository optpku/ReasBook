/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: `gammaZeroConjugate` packages Fenchel conjugation inside `Γ₀(H)`, so applying it
-- twice yields the biconjugate. Corollary 13.38 identifies that biconjugate with the original
-- function for every member of `Γ₀(H)`.
@[simp] theorem gammaZeroConjugate_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    gammaZeroConjugate (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf) = f := by
  ext x
  simpa [Function.asEReal] using congrFun (biconjugate_eq_of_mem_gammaZero hf) x

-- Proof sketch: if `f = gammaZeroConjugate g hg`, apply the involution theorem for
-- `gammaZeroConjugate` to `g` and rewrite the inner conjugate as `f`; the reverse implication is
-- symmetric.
/-- Corollary 13.40: for functions `f` and `g` in `Γ₀(H)`, one has `f = g*` if and only if
`g = f*`, stated using the canonical `Γ₀(H)`-valued conjugate owner `gammaZeroConjugate`. -/
theorem eq_conjugate_iff_eq_conjugate_of_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H)) :
    f = gammaZeroConjugate g hg ↔
      g = gammaZeroConjugate f hf := by
  constructor
  · intro hfg
    calc
      g = gammaZeroConjugate (gammaZeroConjugate g hg) (gammaZeroConjugate_mem_gammaZero hg) := by
        exact (gammaZeroConjugate_gammaZeroConjugate g hg).symm
      _ = gammaZeroConjugate f hf := by
        ext x
        simp [Function.asEReal, hfg]
  · intro hgf
    calc
      f = gammaZeroConjugate (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf) := by
        exact (gammaZeroConjugate_gammaZeroConjugate f hf).symm
      _ = gammaZeroConjugate g hg := by
        ext x
        simp [Function.asEReal, hgf]

end FenchelMoreau

end ERealFunction

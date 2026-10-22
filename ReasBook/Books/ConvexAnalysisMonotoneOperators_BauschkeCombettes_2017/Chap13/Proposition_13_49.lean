/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_40

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: apply Proposition 13.11 to the support function of the epigraph of the
-- `EReal`-valued coercion of `f`, identify the zero-height slice with the recession function of
-- `f*`, and rewrite the remaining support term as the support function of `effectiveDomain f`.
/-- Proposition 13.49 (1): for `f ∈ Γ₀(ℋ)`, the recession function of the Fenchel conjugate `f*`
coincides with the support function of the effective domain of `f`. -/
theorem recessionFunction_gammaZeroConjugate_eq_supportFunction_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (recessionFunction (gammaZeroConjugate f hf)
      (gammaZeroConjugate_mem_gammaZero hf).2.nonempty).asEReal =
      σ[effectiveDomain f] := sorry

end Conjugation

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply clause (1) to `g := gammaZeroConjugate f hf`, use Corollary 13.40 to
-- identify `g*` with `f`, and then rewrite the `EReal`-valued recession function through
-- `recessionFunction_apply`.
/-- Proposition 13.49 (2): for `f ∈ Γ₀(ℋ)`, the recession function of `f` coincides with the
support function of the effective domain of its Fenchel conjugate `f*`. -/
theorem recessionFunction_eq_supportFunction_effectiveDomain_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    (recessionFunction f hf.2.nonempty).asEReal =
      σ[effectiveDomain (gammaZeroConjugate f hf)] := by
  have hdouble :
      gammaZeroConjugate (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf) = f :=
    gammaZeroConjugate_gammaZeroConjugate f hf
  ext u
  simpa [Function.asEReal, recessionFunction_apply, hdouble] using
    congrFun
      (recessionFunction_gammaZeroConjugate_eq_supportFunction_effectiveDomain
        (gammaZeroConjugate f hf) (gammaZeroConjugate_mem_gammaZero hf))
      u

end FenchelMoreau

end ERealFunction

/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20_Core
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace ERealFunction

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply the chapter sum rule for the full-domain quadratic perturbation
-- `γ • halfSquaredNorm`, then identify its subdifferential via Proposition 16.6 and
-- Example 16.12 as the singleton-valued map `x ↦ {γ • x}`.
/-- Example 16.43: if `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, then the subdifferential of
`f + (γ / 2) ‖·‖²` is `∂ f + γ Id`, encoded here as the set-valued map
`x ↦ (∂ f) x + {γ • x}`. -/
theorem subdifferential_add_scaledHalfSquaredNorm_eq_add_singleton_smul
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) :
    ∂ (f + γ • halfSquaredNorm) = (∂ f) + fun x ↦ ({(γ : ℝ) • x} : Set H) := sorry

end

end ERealFunction

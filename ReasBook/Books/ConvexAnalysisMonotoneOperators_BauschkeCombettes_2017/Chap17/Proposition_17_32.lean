/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Corollary_16_72
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply Corollary 16.72 to the scalar composition `φ ∘ f`, viewed through
-- `.toEReal`, to rewrite its subdifferential as the union of the scaled sets
-- `α • (∂ f.toEReal) x` for `α ∈ (∂ φ.toEReal) (f x)`. Then use
-- Proposition 17.31 (1) in the scalar space `H = ℝ` together with the ordinary differentiability
-- of `φ` at `f x` to identify `(∂ φ.toEReal) (f x)` with the singleton
-- `{deriv φ (f x)}`, so the union collapses to the claimed scalar multiple.
/-- Proposition 17.32: if `f : H → ℝ` is continuous and convex, and `φ : ℝ → ℝ` is convex,
increasing on `range f`, and differentiable at `f x`, then the subdifferential of `φ ∘ f` at `x`
is the scalar multiple `φ'(f(x)) ∂ f(x)`, represented here via `deriv φ (f x)` and `.toEReal`.
-/
theorem subdifferential_comp_eq_deriv_smul_of_differentiableAt
    (f : H → ℝ) (φ : ℝ → ℝ) (x : H) (hcont : Continuous f)
    (hconv : _root_.ConvexOn ℝ Set.univ f) (hφconv : _root_.ConvexOn ℝ Set.univ φ)
    (hφdiff : DifferentiableAt ℝ φ (f x)) (hmono : MonotoneOn φ (Set.range f)) :
    (∂ (φ ∘ f).toEReal) x = (deriv φ (f x)) • ((∂ f.toEReal) x) := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction

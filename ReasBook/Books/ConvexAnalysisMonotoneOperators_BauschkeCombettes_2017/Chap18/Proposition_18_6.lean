/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_61
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfInfimalConvolutions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Proposition 16.61 rewrites the subdifferential of the exact infimal convolution at
-- `x` as `(∂ f) y ∩ (∂ g) (x - y)`. The Gâteaux derivative hypothesis identifies `(∂ f) y` with
-- the singleton `{gradf}` via Proposition 17.31 once exactness and domain membership of the
-- left-hand side place `y` in `effectiveDomain f`. Rewriting that domain membership as pointwise
-- nonemptiness makes the intersection nonempty, hence it must equal `{gradf}`.
/-- Proposition 18.6: if `x` belongs to the domain of the subdifferential of the infimal
convolution `f □ g`, the infimal convolution is exact at `x` with minimizer `y`, and `f` has
Gâteaux gradient `gradf` at `y`, then the subdifferential of `f □ g` at `x` is the singleton
`{gradf}`. -/
theorem subdifferential_infimalConvolution_eq_singleton_of_mem_dom_of_value_eq_of_gateauxDerivative
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (x y gradf : H)
    (hx : x ∈ SetValuedOperator.dom (∂ (f □ g)))
    (hEq : (f □ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDual ℝ H gradf) y) :
    (∂ (f □ g)) x = ({gradf} : Set H) := sorry

end DifferentiabilityOfInfimalConvolutions

end ERealFunction

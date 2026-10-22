/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_26
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.44 identifies the textbook proximal-point equation
  `p = Prox_f x` with a subdifferential inclusion.
- `core/canonical`: the owner declarations are `IsProxPoint`, `Prox[f, hf]`, and `∂ f`.
- `bridge/view`: this file translates the Chapter 12 proximal-point owner into the Chapter 16
  subdifferential owner, and then packages the result as an inverse-operator identity.

The refinement should therefore stay at the bridge/view layer and reuse the existing owners rather
than introduce a new local wrapper for `Id + ∂ f`. -/

-- Proof sketch: rewrite `p = Prox_f x` as `IsProxPoint f x p` via the Chapter 12 owner theorem
-- `eq_proximityOperator_of_isProxPoint`, then apply Proposition 12.26 and unfold Definition 16.1
-- to identify the same variational inequality with `x - p ∈ ∂ f p`.
/-- Proposition 16.44: for `f ∈ Γ₀(H)` and `x, p ∈ H`, the point `p` equals `Prox_f x` exactly
when the residual `x - p` belongs to the subdifferential of `f` at `p`. -/
theorem eq_proximityOperator_iff_sub_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (x p : H) :
    p = Prox[f, hf] x ↔
      x - p ∈ (∂ f) p := sorry

-- Proof sketch: extensionality on `x` and set extensionality on `p` reduce the operator identity
-- to the pointwise equivalence above; then use `SetValuedOperator.mem_inverse_iff` and membership
-- in the value of the operator sum `id.toSetValuedOperator + ∂ f` at `p`.
/-- The proximity operator of a `Γ₀(H)` function is the inverse of the set-valued operator
`id.toSetValuedOperator + ∂ f`, which is the textbook formula `Prox_f = (Id + ∂ f)⁻¹`
written through the canonical singleton-valued operator owner. -/
theorem singleton_proximityOperator_eq_inverse_add_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Prox[f, hf].toSetValuedOperator = ((id : H → H).toSetValuedOperator + ∂ f).inverse := sorry

end SubdifferentialCalculus

end ERealFunction

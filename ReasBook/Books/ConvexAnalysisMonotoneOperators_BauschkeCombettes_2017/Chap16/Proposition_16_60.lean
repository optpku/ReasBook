/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.60 states the subdifferential and exactness formulas for the
  source-level infimal postcomposition `L ▷ f`.
- `core/canonical`: `infimalPostcomposition.ExactAt` from Definition 12.34 is the owner notion
  of fiberwise attainment.
- `bridge/view`: Proposition 13.24(4) and Proposition 16.10 convert that owner notion into the
  adjoint-preimage description of the subdifferential.
-/

-- Proof sketch: use Proposition 13.24(4) to rewrite the conjugate of `L ▷ f` as `f* ∘ L.adjoint`,
-- then combine Proposition 13.15 and Proposition 16.10 at the active point `x` with
-- `L x = y` and `(L ▷ f) y = f x`.
/-- Proposition 16.60 (1): if `y = L x` and the infimal postcomposition is exact there through the
point `x`, then formula (16.50) identifies the subdifferential of `L ▷ f` at `y` with the adjoint
preimage `(L^*)⁻¹ (∂ f(x))`. -/
theorem subdifferential_infimalPostcomposition_eq_preimage_adjoint_of_value_eq
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) {x : H} {y : K}
    (hxy : L x = y) (hEq : (L ▷ f) y = (f x : EReal)) :
    (∂ (L ▷ f)) y = (L.adjoint) ⁻¹' ((∂ f) x) := sorry

-- Proof sketch: apply the companion equality theorem below to the chosen witness
-- `v` with `L.adjoint v ∈ ∂ f x`, then package the resulting minimizing point `x`
-- with `infimalPostcomposition.ExactAt`. The extra hypothesis `x ∈ effectiveDomain f`
-- is exactly the primitive finiteness datum required by that owner notion.
/-- Proposition 16.60 (2): if some vector `v` satisfies `L.adjoint v ∈ ∂ f x`, then the infimal
postcomposition is exact at `y = L x`, attained by `x`. -/
theorem infimalPostcomposition_exactAt_of_mem_effectiveDomain_of_adjoint_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) {x : H} {y : K}
    (v : K) (hx : x ∈ effectiveDomain f) (hxy : L x = y)
    (hv : L.adjoint v ∈ (∂ f) x) :
    infimalPostcomposition.ExactAt L f y := sorry

/-- Companion to Proposition 16.60 (2): the exactness conclusion gives the displayed value
equality `(L ▷ f) y = f x`. Unlike exactness, this value identity does not need the extra
effective-domain hypothesis on `x`. -/
theorem infimalPostcomposition_eq_of_adjoint_mem_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) {x : H} {y : K}
    (v : K) (hxy : L x = y)
    (hv : L.adjoint v ∈ (∂ f) x) :
    (L ▷ f) y = (f x : EReal) := sorry

end SubdifferentialCalculus

end ERealFunction

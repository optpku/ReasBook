/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_60

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.61 is the infimal-convolution specialization with a displayed
  minimizing point `y`.
- `core/canonical`: the owner exactness notion is `infimalPostcomposition.ExactAt` applied to the
  canonical product-sum map `Prod.fst + Prod.snd`.
- `bridge/view`: Proposition 12.37 identifies `f □ g` with that infimal postcomposition of the
  separable sum `f ⊕ g`, and Proposition 16.60 transports exactness/subdifferentials back to the
  infimal-convolution surface.
-/

section WithCompleteSpace

variable [CompleteSpace H]
variable (f g : H → Set.Ioi (⊥ : EReal)) (x y : H)

-- Proof sketch: rewrite `f □ g` as the infimal postcomposition of the separable sum by the
-- addition map, apply Proposition 16.60(i) at the exact point `(y, x - y)`, and identify the
-- resulting adjoint preimage with the intersection of the two component subdifferentials via the
-- product-space subdifferential formula.
/-- Proposition 16.61 (1): if the infimal convolution `f □ g` is exact at `x`, attained by `y`,
then, under `f, g ∈ Γ₀(H)`, the subdifferential of `f □ g` at `x` is the intersection of the
subdifferentials of `f` at `y` and of `g` at `x - y`. -/
theorem subdifferential_infimalConvolution_eq_inter_of_value_eq
    (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hEq : (f □ g) x = (f y : EReal) + (g (x - y) : EReal)) :
    (∂ (f □ g)) x = (∂ f) y ∩ (∂ g) (x - y) := sorry

end WithCompleteSpace

variable (f g : H → Set.Ioi (⊥ : EReal)) (x y : H)

-- Proof sketch: choose `u ∈ (∂ f) y ∩ (∂ g) (x - y)`. Applying the two subgradient inequalities
-- at `z` and `x - z` makes the linear terms cancel, so `f y + g (x - y) ≤ f z + g (x - z)` for
-- every `z`. Since the defining infimum of `(f □ g) x` is always bounded above by the value at
-- `z = y`, this yields the displayed equality and hence exactness at `x`.
/-- Proposition 16.61 (2): if the subdifferentials of `f` at `y` and of `g` at `x - y` intersect,
then the infimal convolution `f □ g` is exact at `x`. -/
theorem infimalConvolution_exactAt_of_subdifferential_inter_nonempty
    (hinter : ((∂ f) y ∩ (∂ g) (x - y)).Nonempty) :
    infimalConvolution.ExactAt f g x := sorry

/-- Companion to Proposition 16.61 (2): under the same intersection hypothesis, the displayed
point `y` attains the defining infimum of `f □ g` at `x`. -/
theorem infimalConvolution_eq_add_of_subdifferential_inter_nonempty
    (hinter : ((∂ f) y ∩ (∂ g) (x - y)).Nonempty) :
    (f □ g) x = (f y : EReal) + (g (x - y) : EReal) := sorry

end SubdifferentialCalculus

end

end ERealFunction

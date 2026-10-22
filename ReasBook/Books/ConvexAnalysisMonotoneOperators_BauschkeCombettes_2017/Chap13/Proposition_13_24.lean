/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: expand the conjugate of `f □ g`, rewrite the defining infimum as a translated
-- supremum over decompositions `x = y + z`, and separate the two resulting suprema.
/-- Proposition 13.24 (1): the Fenchel conjugate of the infimal convolution `f □ g` is the
pointwise sum `f* + g*`. -/
theorem conjugate_infimalConvolution_eq
    (f g : H → Set.Ioi (⊥ : EReal)) :
    (f □ g)∗ = f.asEReal∗ + g.asEReal∗ := sorry

-- Proof sketch: apply Proposition 13.16 to `f + g ≥ f** + g**`, then use clause (1) together
-- with the general inequality `h** ≤ h` for the EReal-valued infimal convolution of the
-- conjugates.
/-- Proposition 13.24 (2): the conjugate of the pointwise sum is bounded above by the infimal
convolution `f* □ g*` of the conjugates. -/
theorem conjugate_add_le_infimalConvolution_conjugate
    (f g : H → Set.Ioi (⊥ : EReal)) :
    (f.asEReal + g.asEReal)∗ ≤ f.asEReal∗ □ g.asEReal∗ := sorry

-- Proof sketch: specialize clause (1) to the decomposition of the Moreau envelope as `f □ qγ`,
-- then identify the conjugate of the quadratic kernel `qγ` with the scaled canonical quadratic
-- owner `γ • halfSquaredNorm.asEReal`.
/-- Proposition 13.24 (3): for every `γ ∈ ℝ_{++}`, the conjugate of the `γ`-Moreau envelope
`{}^[γ] f` is `f* + (γ / 2) ‖·‖²`. -/
theorem conjugate_moreauEnvelope_eq
    (f : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ)) :
    ({}^[γ] f)∗ = f.asEReal∗ + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal) := sorry

section LinearMaps

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
variable [CompleteSpace H] [CompleteSpace K]

-- Proof sketch: expand the fiberwise infimum defining `L ▷ f`, rewrite the dual pairing
-- `⟪L x, v⟫` as `⟪x, L.adjoint v⟫`, and identify the remaining supremum with `f* (L* v)`.
/-- Proposition 13.24 (4): for a bounded linear operator `L : H → K`, the conjugate of the
infimal postcomposition `L ▷ f` is the composition `f* ∘ L*`. -/
theorem conjugate_infimalPostcomposition_eq_comp_adjoint
    (f : H → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    (L ▷ f)∗ = f.asEReal∗ ∘ L.adjoint := sorry

-- Proof sketch: apply clause (4) to `L.adjoint` and Proposition 13.16 to the inequality
-- `(L.adjoint ▷ f*)* ≤ f ∘ L`, then dualize once more to obtain the stated upper bound by the
-- infimal postcomposition along the adjoint.
/-- Proposition 13.24 (5): for a bounded linear operator `L : K → H`, the conjugate of the
precomposition `f ∘ L` is bounded above by the infimal postcomposition of `f*` along `L*`
(equivalently, the fiberwise infimum over `{v | L* v = u}`). -/
theorem conjugate_comp_le_fiberInf_conjugate
    (f : H → Set.Ioi (⊥ : EReal)) (L : K →L[ℝ] H) :
    (f.asEReal ∘ L)∗ ≤ L.adjoint ▷ f.asEReal∗ := sorry

end LinearMaps

end Conjugation

end ERealFunction

/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Proposition 14.1 identifies the Fenchel conjugate of `f + γ q` with the
  `γ`-Moreau envelope of `f*` and records exactness of the defining infimal convolution.
- `core/canonical`: the owner abstractions are `halfSquaredNorm.asEReal`, `{}^[γ] f`, and
  `infimalConvolution.Exact`.
- `bridge/view`: `gammaZeroConjugate f hf` is only the canonical `Γ₀(H)`-valued packaging of
  `f∗`, so it should be used through those owner abstractions rather than through a parallel local
  wrapper API. -/

section MoreauDecomposition

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply Corollary 13.38 to identify the biconjugate of `f` with `f`, combine
-- Proposition 13.24(2) with the quadratic-kernel conjugacy from Proposition 13.24(3), and then
-- use that `gammaZeroConjugate f hf` belongs to `Γ₀(H)` so its Moreau envelope is the exact
-- infimal convolution with `γ⁻¹ q`.
/-- Proposition 14.1: for `f ∈ Γ₀(H)` and `γ ∈ ℝ_{++}`, if `q(x) = (1 / 2) ‖x‖^2`, then the
Fenchel conjugate of `f + γ q` is the `γ`-Moreau envelope of `f*`; equivalently,
`(f + γ q)^* = f* □ (γ⁻¹ q) = {}^γ(f^*)`, and this infimal convolution is exact. -/
theorem conjugate_add_scaledQuadratic_eq_moreauEnvelope_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : Set.Ioi (0 : ℝ)) :
    (f.asEReal + (((γ : ℝ) : EReal) • halfSquaredNorm.asEReal))∗ =
      {}^[γ] (gammaZeroConjugate f hf) := sorry

-- Proof sketch: Corollary 13.38 puts `gammaZeroConjugate f hf` in `Γ₀(H)`, and the quadratic
-- kernel is the canonical Moreau regularizer. Proposition 12.14 then gives attainment for the
-- translated sums defining the infimal convolution.
/-- Proposition 14.1 companion: the infimal convolution `f* □ (γ⁻¹ q)` occurring in the Moreau
envelope representation is exact. -/
theorem infimalConvolution_exact_gammaZeroConjugate_moreauQuadraticKernel
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : Set.Ioi (0 : ℝ)) :
    infimalConvolution.Exact (gammaZeroConjugate f hf) (moreauQuadraticKernel γ) := sorry

end MoreauDecomposition

end ERealFunction

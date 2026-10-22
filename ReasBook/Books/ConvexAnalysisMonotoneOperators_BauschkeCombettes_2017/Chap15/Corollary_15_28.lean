/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_48
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_24_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Theorem_15_27

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 15.28 contributes the Chapter 15 attainment/exactness consequence
  for the adjoint infimal postcomposition attached to `g ∘ L`.
- `core/canonical`: the conjugation identity itself is already owned by
  `conjugate_comp_eq_adjointInfimalPostcomposition` from Proposition 13.48.
- `bridge/view`: the fiberwise `sInf` formula is the pointwise view of that owner identity,
  while `infimalPostcomposition.Exact L.adjoint (g∗[hg])` is the genuinely new
  Chapter 15 regularity conclusion.
-/

variable
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)

/- Corollary 15.28 reuses the Chapter 13 owner identity
`conjugate_comp_eq_adjointInfimalPostcomposition`; the Chapter 15 regularity package is only
needed for the attainment/exactness conclusion below. -/
#check conjugate_comp_eq_adjointInfimalPostcomposition

-- Proof sketch: evaluate the Chapter 13 owner identity
-- `conjugate_comp_eq_adjointInfimalPostcomposition` at `u` and unfold `infimalPostcomposition`.
/-- Evaluating the canonical composition-conjugation identity gives the fiberwise infimum formula
from `(15.45)`. -/
theorem conjugate_comp_apply_eq_sInf_fiber_conjugate_of_range_inter_effectiveDomain_nonempty
    (hdom : (range L ∩ effectiveDomain g).Nonempty)
    (u : H) :
    (g ∘ L).asEReal∗ u =
      sInf (g.asEReal∗ '' {v : K | L.adjoint v = u}) :=
  sorry

-- Proof sketch: the same specialization of Theorem 15.27 that gives the function identity also
-- gives exactness of the dual infimal postcomposition on its domain, i.e. whenever the fiberwise
-- infimum is finite it is attained by some `v` with `L.adjoint v = u`.
/-- Under the Corollary 15.28 regularity hypotheses, the infimal postcomposition `L^* ▷ g^*` is
exact on its domain, so the fiberwise infimum in `(15.45)` is attained whenever finite. -/
theorem infimalPostcomposition_adjoint_conjugate_exact_of_regular
    (hregular :
      (0 : K) ∈ sri (effectiveDomain g - Set.range L) ∨
        (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
          (effectiveDomain g ∩ Set.range L).Nonempty))
    :
    infimalPostcomposition.Exact L.adjoint (g∗[hg]) := sorry

end FenchelRockafellarDuality

end ERealFunction

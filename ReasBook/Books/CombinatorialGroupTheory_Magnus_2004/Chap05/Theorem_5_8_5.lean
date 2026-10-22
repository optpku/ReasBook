/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Theorem_4_4_8
import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_8_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_8_3
import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_8_4

universe u v

set_option autoImplicit false

section

namespace Group

open Knot

/-!
Primary domain: solvable conjugacy problem for groups of alternating knots.

Layer triage:
- `source-facing`: an alternating knot `K : Knot`, its standard alternating projections, and the
  presentation data extracted from such a projection.
- `core/canonical`: `K.knotGroup` is the canonical group attached to `K`,
  `Group.HasSolvableConjugacyProblem` is the abstract group-level owner for the conclusion, and
  `K.presentationRelators P` and `K.presentationEquiv P` reuse the project's canonical
  presentation owner for the relator set attached to a projection, while
  `GroupPresentation.HasSolvableConjugacyProblem R` together with the Chapter `5` predicates
  `C(4)[basis, R]` and `T(4)[basis, R]` are the owner abstractions for the presentation-level
  input.
- `bridge/view`: Lemma `5-8-3` supplies a standard alternating projection of an alternating knot,
  and Lemma `5-8-1` converts such a projection, via the source-facing `Knot` owner abstraction,
  into finiteness and `(C(4), T(4))` for the canonical presentation already attached to that
  projection.

Domain sampling:
1. `Knot` from Lemma `5-8-1` is the source-facing owner abstraction for knots, projections, and
   the canonical presentation attached to each projection.
2. `exists_alternating_standard_projection` from Lemma `5-8-3` is the source-facing theorem for
   obtaining a standard alternating projection from an alternating knot.
3. `presentation_of_standard_alternating_projection` from Lemma `5-8-1` is the chapter bridge from
   explicit standard and alternating projection hypotheses to the canonical finite `(C(4), T(4))`
   properties of the projection-attached presentation data.
4. `GroupPresentation.hasSolvableConjugacyProblem_of_finite_C4_T4` from Lemma `5-8-4` and
   `Group.hasSolvableConjugacyProblem_of_presentation` from Theorem `4-4-8` are the canonical
   presentation-level and abstract group-level owner theorems used in the final upgrade step.

Primitive vs. derived:
- primitive public data: the knot `K` together with its canonically attached group `K.knotGroup`
  and the canonical presentation attached to each projection;
- derived API: the abstract group-level conclusion
  `Group.HasSolvableConjugacyProblem K.knotGroup`.
-/

-- Proof sketch: choose a standard alternating projection of `K` using Lemma `5-8-3`. The bridge
-- theorem `presentation_of_standard_alternating_projection` shows that the canonical presentation
-- attached to that projection is finite and satisfies `C(4)` and `T(4)`.
-- Lemma `5-8-4` gives solvability of the conjugacy problem for that presentation, and the
-- canonical group-level presentation bridge upgrades the conclusion to the knot group itself.
/-- Theorem 5-8-5: if `K` is an alternating knot, then the group of `K` has solvable conjugacy
problem. -/
theorem hasSolvableConjugacyProblem_of_alternatingKnot
    {K : Knot.{u, v}} (hK : K.IsAlternating) :
    HasSolvableConjugacyProblem K.knotGroup := by
  obtain ⟨P, hP_standard, hP_alternating⟩ := K.exists_alternating_standard_projection hK
  obtain ⟨hR, hC4, hT4⟩ :=
    K.presentation_of_standard_alternating_projection hP_standard hP_alternating
  have hPresentation :
      GroupPresentation.HasSolvableConjugacyProblem (K.presentationRelators P) := by
    simpa using
      GroupPresentation.hasSolvableConjugacyProblem_of_finite_C4_T4 (K.presentationRelators P)
        hR hC4 hT4
  exact hasSolvableConjugacyProblem_of_presentation
    (K.presentationRank P) (K.presentationRelators P) (K.presentationEquiv P) hPresentation

end Group

end

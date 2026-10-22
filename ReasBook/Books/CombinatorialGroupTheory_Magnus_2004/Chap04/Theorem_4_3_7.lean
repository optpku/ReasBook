/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_3
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

namespace GroupPresentation

section

variable {X : Type u} [Primcodable X]

/-!
Primary domain: algorithmic group theory for recursively presented groups.

Layer triage:
- `source-facing`: a recursive presentation `(X; R)` together with the simplicity of the presented
  group determined by that presentation.
- `core/canonical`: `PresentedGroup R` is the owner object for the group defined by the relators,
  while `GroupPresentation.IsRecursive`, `GroupPresentation.HasSolvableWordProblem`, and
  `IsSimpleGroup` are the owner predicates for the hypotheses and conclusion.
- `bridge/view`: if `(X; R)` is given as a presentation of an ambient group `G` via
  `P : PresentedGroup R ≃* G`, then simplicity of `G` transports back to `PresentedGroup R`
  through `P`.

Domain sampling:
1. Definition `2-1-1` uses `PresentedGroup R` and `PresentedGroup R ≃* G` as the canonical owner
   object and presentation bridge.
2. `GroupPresentation.IsRecursive R` is the chapter owner for recursive enumerability of relators.
3. `GroupPresentation.HasSolvableWordProblem R` is the owner predicate for the conclusion.
4. `MulEquiv.isSimpleGroup_congr` is mathlib's canonical explicit transport of simplicity across
   a presentation equivalence.

Primitive vs. derived:
the primitive public data are the generator type `X` and relator set `R`; the ambient group `G`
and a presentation equivalence `PresentedGroup R ≃* G` are derived bridge data used only to
transport simplicity, so they do not remain in the main theorem.
-/

/-- Theorem 4-3-7: if a recursive presentation `(X; R)` presents a simple group, equivalently if
its canonical presented group `PresentedGroup R` is simple, then `(X; R)` has solvable word
problem. -/
-- Proof sketch: for an input word `w`, enumerate in parallel the words trivial in the original
-- presentation and the words trivial in the quotient obtained by adjoining `w` as an extra
-- relator. Simplicity implies that the second quotient is trivial exactly when `w` is nontrivial
-- in the original group, so one of the two enumerations eventually certifies the answer.
theorem hasSolvableWordProblem_of_isRecursive_of_simple_presentedGroup
    (R : Set (FreeGroup X)) (hR : IsRecursive R) (hsimple : IsSimpleGroup (PresentedGroup R)) :
    HasSolvableWordProblem R := sorry

/-- Bridge form of Theorem 4-3-7 for a chosen presentation equivalence with an ambient simple
group. -/
theorem hasSolvableWordProblem_of_isRecursive_of_presentation_of_isSimpleGroup
    {G : Type u} [Group G] (R : Set (FreeGroup X)) (hR : IsRecursive R)
    (P : PresentedGroup R ≃* G) (hsimple : IsSimpleGroup G) :
    HasSolvableWordProblem R := by
  exact hasSolvableWordProblem_of_isRecursive_of_simple_presentedGroup R hR
    ((MulEquiv.isSimpleGroup_congr P).2 hsimple)

end

end GroupPresentation

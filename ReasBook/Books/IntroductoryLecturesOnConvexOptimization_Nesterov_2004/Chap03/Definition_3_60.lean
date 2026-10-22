/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_62

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.60 lies in the chapter's bounded-polyhedron / polyhedral-localization domain on
real inner-product spaces.

Sampled owner-style declarations:
- `innerLePolyhedron` in `Definition_3_62`, the chapter owner for a finite system of half-space
  inequalities in a real inner-product space;
- `mem_innerLePolyhedron_iff` in `Definition_3_62`, the canonical membership expansion of that
  owner set;
- `IsPolyhedron` in `Chap01/Definition_1_1_4_5`, the chapter's canonical finite affine-presentation
  predicate;
- `isPolyhedron_of_eq_innerLePolyhedron` in `Definition_3_62`, the owner-side bridge from the
  half-space presentation to the chapter polyhedron predicate;
- `Bornology.IsBounded` in mathlib, the ambient owner predicate for bounded subsets.

Best owner abstraction:
- source-facing: a set `Q` together with boundedness and a presentation
  `Q = innerLePolyhedron a b`;
- core/canonical: the owner set constructor `innerLePolyhedron` and the chapter predicate
  `IsPolyhedron`;
- bridge/view: `isPolyhedron_of_eq_innerLePolyhedron`.

Primitive data:
- a bounded ambient set `Q`;
- a finite index size `m`;
- half-space normals `a : Fin m → E`;
- scalar bounds `b : Fin m → ℝ`.

Derived API:
- the owner set `innerLePolyhedron a b`;
- its polyhedral consequence `IsPolyhedron (innerLePolyhedron a b)`.

There is no separate project-level owner predicate for bounded polyhedra, so the numbered item is
kept as a source-facing predicate on sets. The word `polytope` contributes genuine boundedness,
while the displayed formula is captured by the chapter owner presentation
`Q = innerLePolyhedron a b`.
-/

namespace Set

section

/-- Definition 3.60: a polyhedral localization set is a bounded set that admits a finite
inner-product half-space presentation `Q = {x | ∀ j, ⟪a j, x⟫ ≤ b j}`. -/
def IsPolyhedralLocalizationSet (Q : Set E) : Prop :=
  Bornology.IsBounded Q ∧
    ∃ (m : ℕ) (a : Fin m → E) (b : Fin m → ℝ), Q = innerLePolyhedron a b

/-- A polyhedral localization set is bounded. -/
theorem IsPolyhedralLocalizationSet.isBounded
    {Q : Set E} (hQ : Q.IsPolyhedralLocalizationSet) :
    Bornology.IsBounded Q :=
  hQ.1

/-- A polyhedral localization set is a polyhedron in the chapter's canonical sense. -/
-- Proof sketch: unpack the defining half-space presentation from
-- `hQ : IsPolyhedralLocalizationSet Q` and apply
-- `isPolyhedron_of_eq_innerLePolyhedron`; boundedness is additional source data and is not needed
-- for the polyhedral bridge.
theorem IsPolyhedralLocalizationSet.isPolyhedron
    {Q : Set E} (hQ : Q.IsPolyhedralLocalizationSet) :
    Q.IsPolyhedron := by
  rcases hQ with ⟨_, m, a, b, rfl⟩
  exact innerLePolyhedron_isPolyhedron a b

end

end Set

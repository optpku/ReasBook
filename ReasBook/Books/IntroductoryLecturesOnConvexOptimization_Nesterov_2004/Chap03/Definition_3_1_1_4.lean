/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

noncomputable section

open scoped BigOperators
open ConvexSpace

universe u v w

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.1.1.4 lives in the finite convex-combination domain.

Sampled owner-style declarations:
- `StdSimplex`
- `StdSimplex.map`
- `ConvexSpace.convexCombination`
- `convexCombination_eq_sum`

Best owner abstraction:
- `convexCombination (w.map points)` for `w : StdSimplex R ι`

Primitive data:
- a simplex weight vector `w : StdSimplex R ι`
- a family `points : ι → E`, with finiteness carried intrinsically by the simplex witness

Derived API:
- `is_convex_combination_of R`, the source-facing owner-shaped predicate
- `StdSimplex.map`, transporting coefficient data to a simplex of points
- `StdSimplex.convexCombination_map_eq_sum`, rewriting the owner-shaped convex combination on a
  family indexed by a finite type into the textbook weighted-sum formula
- `convexCombination_eq_sum`, identifying the canonical convex combination with the textbook
  weighted sum
- `is_convex_combination_of_iff_exists_coefficients`, the coefficient bridge

Source/core/bridge triage:
- source-facing: `is_convex_combination_of R points x`, centered on the owner-shaped simplex
  presentation
- core/canonical: `convexCombination (w.map points)`
- bridge/view: `is_convex_combination_of_iff_exists_coefficients`

There is no earlier chapter declaration with this exact source-facing interface, so this file
introduces the source-facing predicate directly in terms of the mathlib owner abstraction over an
arbitrary scalar `R`, index type `ι`, and convex space. The finiteness of the combination is
encoded intrinsically by the simplex witness rather than by a separate public `Fintype`
assumption. The textbook real / `Fin m` coefficient formula is kept only as a companion bridge in
the module layer. -/

section Owner

variable (R : Type u) [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
variable {ι : Type v}
variable {E : Type w} [ConvexSpace R E]

/-- Definition 3.1.1.4: a point is a convex combination of a finite family of points when it is
the canonical convex combination associated to some simplex weight vector on that family. -/
def is_convex_combination_of (points : ι → E) (x : E) : Prop :=
  ∃ w : StdSimplex R ι, x = convexCombination (w.map points)

end Owner

section Module

variable (R : Type u) [PartialOrder R] [Ring R] [IsStrictOrderedRing R]
variable {ι : Type v} [Fintype ι]
variable {E : Type w} [AddCommGroup E] [Module R E]

local notation "convexCombination" =>
  @ConvexSpace.convexCombination R E inferInstance inferInstance inferInstance inferInstance

namespace StdSimplex

/-- Rewriting the canonical convex combination of a finite family gives the usual weighted-sum
formula with the simplex coefficients. -/
theorem convexCombination_map_eq_sum (w : StdSimplex R ι) (points : ι → E) :
    convexCombination (w.map points) = ∑ i, w.weights i • points i := by
  rw [convexCombination_eq_sum, StdSimplex.map]
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ add_smul _ _ _)]
  simpa using
    (Finsupp.sum_fintype w.weights (fun i r ↦ r • points i) (fun _ ↦ by simp))

end StdSimplex

/-- Unpacking the canonical simplex-based convex combination into coefficient data gives exactly
the textbook finite convex-combination formula, and conversely. -/
-- Proof sketch: read the coefficients directly from the simplex weights, using the `StdSimplex`
-- axioms for nonnegativity and normalization; conversely, package a coefficient family on the
-- finite index type `ι` into a finitely supported weight vector via
-- `Finsupp.equivFunOnFinite.symm`, then rewrite the owner-shaped convex combination by
-- `StdSimplex.convexCombination_map_eq_sum`.
theorem is_convex_combination_of_iff_exists_coefficients
    (points : ι → E) (x : E) :
    is_convex_combination_of R points x ↔
      ∃ α : ι → R, (∀ i, 0 ≤ α i) ∧ (∑ i, α i) = 1 ∧ x = ∑ i, α i • points i := by
  unfold is_convex_combination_of
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.weights, fun i ↦ w.nonneg i, ?_, ?_⟩
    · simpa [Finsupp.sum_fintype] using w.total
    · simpa [StdSimplex.convexCombination_map_eq_sum R w points] using hw
  · rintro ⟨α, hαnonneg, hαsum, rfl⟩
    let w : StdSimplex R ι :=
      ⟨Finsupp.equivFunOnFinite.symm α,
        by simpa using hαnonneg,
        by simpa using (Finsupp.equivFunOnFinite_symm_sum α).trans hαsum⟩
    refine ⟨w, ?_⟩
    simpa [w] using (StdSimplex.convexCombination_map_eq_sum R w points).symm

end Module

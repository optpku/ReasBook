/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM

/-- A set is polyhedral when finitely many continuous linear inequalities cut it out. -/
def IsPolyhedralSet {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) : Prop :=
  ∃ n : ℕ, ∃ a : Fin n → E, ∃ b : Fin n → ℝ,
    C = {z | ∀ i, inner ℝ (a i) z ≤ b i}

/-- The finite-halfspace presentation of a polyhedral set. -/
theorem polyhedralSet_iff {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} :
    IsPolyhedralSet C ↔
      ∃ n : ℕ, ∃ a : Fin n → E, ∃ b : Fin n → ℝ,
        C = {z | ∀ i, inner ℝ (a i) z ≤ b i} := by
  -- Unfolding the predicate exposes exactly the stated halfspace presentation.
  rfl

/-- A compact convex polytope presented as the convex hull of finitely many vertices. -/
def IsCompactConvexPolytope {E : Type u} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] (X : Set E) : Prop :=
  IsCompact X ∧ Convex ℝ X ∧
    ∃ vertices : Finset E, X = convexHull ℝ (vertices : Set E)

/-- Compact convex polytopes are exactly compact convex finite convex hulls. -/
theorem compactConvexPolytope_iff {E : Type u} [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace E] {X : Set E} :
    IsCompactConvexPolytope X ↔
      IsCompact X ∧ Convex ℝ X ∧
        ∃ vertices : Finset E, X = convexHull ℝ (vertices : Set E) := by
  -- Unfolding the predicate exposes the same compact convex finite-hull data.
  rfl

end ConsensusADMM

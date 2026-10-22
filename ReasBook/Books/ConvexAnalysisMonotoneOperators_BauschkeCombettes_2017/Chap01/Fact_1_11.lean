/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u v w

variable {X : Type u} [TopologicalSpace X]

/-- The closed-set finite-intersection property relative to a subset `C` of a topological space. -/
def ClosedSetFiniteIntersectionPropertyIn (C : Set X) : Prop :=
  ∀ ⦃J : Type u⦄ (Z : J → Set X),
    (∀ j, IsClosed (Z j)) →
      (∀ I : Finset J, (C ∩ ⋂ i ∈ I, Z i).Nonempty) →
        (C ∩ ⋂ j, Z j).Nonempty

/-- Every net with values in `C` has a cluster point in `C`. -/
def EveryNetHasClusterPointIn (C : Set X) : Prop :=
  ∀ ⦃A : Type*⦄ [Nonempty A] [Preorder A] [IsDirectedOrder A] (u : A → X),
    (∀ a, u a ∈ C) → ∃ x ∈ C, MapClusterPt x atTop u

/-- Every net with values in `C` has a subnet converging to a point of `C`. -/
def EveryNetHasConvergentSubnetIn (C : Set X) : Prop :=
  ∀ ⦃A : Type*⦄ [Nonempty A] [Preorder A] [IsDirectedOrder A] (u : A → X),
    (∀ a, u a ∈ C) →
      ∃ x ∈ C, ∃ (B : Type*) (_ : Nonempty B) (_ : Preorder B) (_ : IsDirectedOrder B)
        (φ : B → A),
        Monotone φ ∧ Tendsto φ atTop atTop ∧ Tendsto (u ∘ φ) atTop (𝓝 x)

/-- A subset is compact iff every family of closed sets with the finite-intersection property
meets it. -/
theorem isCompact_iff_closedSetFiniteIntersectionPropertyIn (C : Set X) :
    IsCompact C ↔ ClosedSetFiniteIntersectionPropertyIn C := by
  constructor
  · intro hC J Z hZ hfinite
    by_contra hCZ
    rcases (isCompact_iff_finite_subfamily_closed.mp hC) Z hZ
        (Set.not_nonempty_iff_eq_empty.mp hCZ) with ⟨I, hI⟩
    exact (Set.not_nonempty_iff_eq_empty.mpr hI) (hfinite I)
  · intro hC
    refine (isCompact_iff_finite_subfamily_closed.mpr ?_)
    intro J Z hZ hCZ
    by_contra hfinite
    have hfinite' : ∀ I : Finset J, (C ∩ ⋂ i ∈ I, Z i).Nonempty := by
      intro I
      by_contra hI
      exact hfinite ⟨I, Set.not_nonempty_iff_eq_empty.mp hI⟩
    exact (Set.not_nonempty_iff_eq_empty.mpr hCZ) (hC Z hZ hfinite')

/-- The cluster-point criterion and the convergent-subnet criterion are equivalent. -/
theorem everyNetHasClusterPointIn_iff_everyNetHasConvergentSubnetIn (C : Set X) :
    EveryNetHasClusterPointIn C ↔ EveryNetHasConvergentSubnetIn C := sorry

/-- Every net in `C` has a cluster point in `C` iff `C` is compact. -/
-- Proof sketch: compactness gives cluster points for maps into a compact set by
-- `IsCompact.exists_mapClusterPt_of_frequently`; conversely, apply the net criterion for
-- compactness.
theorem isCompact_iff_everyNetHasClusterPointIn [T2Space X] (C : Set X) :
    IsCompact C ↔ EveryNetHasClusterPointIn C := sorry

/-- Every net in `C` has a convergent subnet with limit in `C` iff `C` is compact. -/
theorem isCompact_iff_everyNetHasConvergentSubnetIn [T2Space X] (C : Set X) :
    IsCompact C ↔ EveryNetHasConvergentSubnetIn.{u, v, w} C := by
  constructor
  · intro hC
    exact
      (everyNetHasClusterPointIn_iff_everyNetHasConvergentSubnetIn.{u, v, v, w} C).1
        ((isCompact_iff_everyNetHasClusterPointIn.{u, v} C).1 hC)
  · intro hC
    exact
      (isCompact_iff_everyNetHasClusterPointIn.{u, v} C).2
        ((everyNetHasClusterPointIn_iff_everyNetHasConvergentSubnetIn.{u, v, v, w} C).2 hC)

/-- Fact 1.11: for a subset `C` of a Hausdorff topological space, compactness, the closed-set
finite-intersection property relative to `C`, the existence of cluster points for all nets in `C`,
and the existence of convergent subnets for all nets in `C` are equivalent. -/
theorem isCompact_tfae [T2Space X] (C : Set X) :
    List.TFAE [
      IsCompact C,
      ClosedSetFiniteIntersectionPropertyIn C,
      EveryNetHasClusterPointIn C,
      EveryNetHasConvergentSubnetIn C
    ] := by
  tfae_have 1 ↔ 2 := isCompact_iff_closedSetFiniteIntersectionPropertyIn C
  tfae_have 1 ↔ 3 := isCompact_iff_everyNetHasClusterPointIn C
  tfae_have 3 ↔ 4 := everyNetHasClusterPointIn_iff_everyNetHasConvergentSubnetIn C
  tfae_finish

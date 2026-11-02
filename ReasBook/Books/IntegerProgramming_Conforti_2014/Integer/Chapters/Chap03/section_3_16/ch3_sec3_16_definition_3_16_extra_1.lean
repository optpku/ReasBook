import Mathlib

open scoped Matrix

namespace Set

section Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 3.16-extra-1. The polar of a set `S` in a real inner-product space is the set of
vectors `y` such that `⟪y, x⟫ ≤ 1` for every `x ∈ S`. -/
def polar (S : Set E) : Set E :=
  {y : E | ∀ x ∈ S, inner ℝ y x ≤ 1}

scoped[Polar] postfix:max "*" => Set.polar

open scoped Polar

/-- Membership in `S*` means satisfying `⟪y, x⟫ ≤ 1` for every `x ∈ S`. -/
theorem mem_polar_iff (S : Set E) (y : E) :
    y ∈ S* ↔ ∀ x ∈ S, inner ℝ y x ≤ 1 :=
  Iff.rfl

/-- The zero vector belongs to the polar of any set in a real inner-product space. -/
theorem zero_mem_polar (S : Set E) :
    (0 : E) ∈ S* := by
  simp [Set.polar]

/-- The polar of any set in a real inner-product space is convex. -/
theorem convex_polar (S : Set E) :
    Convex ℝ (S*) := by
  rw [show S* = ⋂ x ∈ S, {y : E | inner ℝ y x ≤ 1} by
    ext y
    simp [Set.polar]]
  refine convex_iInter₂ fun x _ ↦ ?_
  let f : E → ℝ := fun y ↦ inner ℝ y x
  have hf : IsLinearMap ℝ f := by
    refine ⟨?_, ?_⟩
    · intro y z
      simp [f, inner_add_left]
    · intro a y
      simp [f, real_inner_smul_left]
  simpa [f] using convex_halfSpace_le hf (1 : ℝ)

end Polar

section Euclidean

variable {ι : Type*} [Fintype ι]

open scoped Polar

/-- The canonical Euclidean realization of a subset of `ℝ^ι`. -/
noncomputable abbrev toEuclidean (S : Set (ι → ℝ)) : Set (EuclideanSpace ℝ ι) :=
  (EuclideanSpace.equiv ι ℝ).symm '' S

/-- In `ℝ^n`, membership in `S*` is exactly the textbook dot-product inequality
`y ⬝ᵥ x ≤ 1` for all `x ∈ S`. -/
theorem mem_polar_iff_dotProduct {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ S* ↔ ∀ x ∈ S, y ⬝ᵥ x ≤ 1 := by
  simp [Set.polar, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

end Euclidean

end Set

namespace Submodule

section Euclidean

variable {ι : Type*} [Fintype ι]

/-- The canonical Euclidean realization of a subspace of `ℝ^ι`. -/
noncomputable abbrev toEuclidean (L : Submodule ℝ (ι → ℝ)) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  L.map (EuclideanSpace.equiv ι ℝ).symm.toLinearMap

end Euclidean

end Submodule

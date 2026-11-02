import Mathlib

open AffineMap

section

variable {𝕜 V : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]

section OrderedRing

variable [PartialOrder 𝕜] [IsOrderedRing 𝕜]

/-- Helper for Exercise 3.18: one tight point forces the valid inequality to be tight on the
whole affine subspace. -/
lemma eq_everywhere_of_exists_tight_point
    (P : AffineSubspace 𝕜 V) (c : V →ₗ[𝕜] 𝕜) (δ : 𝕜)
    {x₀ : V}
    (hx₀ : x₀ ∈ P)
    (htight : c x₀ = δ)
    (hvalid : ∀ x ∈ P, c x ≤ δ) :
    ∀ y ∈ P, c y = δ := by
  intro y hy
  -- Apply validity at `y` and at the reflection of `y` through the tight point `x0`.
  have hy_le : c y ≤ δ := hvalid y hy
  have hreflect_mem : lineMap y x₀ (2 : 𝕜) ∈ P := lineMap_mem (2 : 𝕜) hy hx₀
  have hreflect_le : lineMap (c y) δ (2 : 𝕜) ≤ δ := by
    simpa [htight] using
      (show c.toAffineMap (lineMap y x₀ (2 : 𝕜)) ≤ δ from hvalid _ hreflect_mem)
  -- The reflected inequality becomes `(1 - 2) * c y + 2 * δ ≤ δ`, which forces equality.
  rw [lineMap_apply_ring] at hreflect_le
  norm_num at hreflect_le
  have hδ_le : δ ≤ c y := by
    exact (add_le_add_iff_right δ).mp <|
      by simpa [two_mul, add_comm, add_left_comm, add_assoc] using hreflect_le
  exact le_antisymm hy_le hδ_le

end OrderedRing

section PartialOrder

/-- Helper for Exercise 3.18: if no point of the affine subspace is tight, then the valid
inequality is strict everywhere on the affine subspace. -/
lemma strict_everywhere_of_no_tight_point
    [PartialOrder 𝕜]
    (P : AffineSubspace 𝕜 V) (c : V →ₗ[𝕜] 𝕜) (δ : 𝕜)
    (hnotight : ¬ ∃ x ∈ P, c x = δ)
    (hvalid : ∀ x ∈ P, c x ≤ δ) :
    ∀ x ∈ P, c x < δ := by
  intro x hx
  -- Excluding tight points turns the valid weak inequality into a strict one.
  have hx_ne : c x ≠ δ := by
    intro hx_eq
    exact hnotight ⟨x, hx, hx_eq⟩
  exact lt_of_le_of_ne (hvalid x hx) hx_ne

end PartialOrder

section OrderedRing

variable [PartialOrder 𝕜] [IsOrderedRing 𝕜]

/-- Exercise 3.18: if `c x ≤ δ` is a valid inequality for an affine space `P`, then
either it is tight at every point of `P` or it is strict at every point of `P`. -/
theorem valid_inequality_on_affine_subspace_eq_or_lt_everywhere
    (P : AffineSubspace 𝕜 V) (c : V →ₗ[𝕜] 𝕜) (δ : 𝕜)
    (hvalid : ∀ x ∈ P, c x ≤ δ) :
    (∀ x ∈ P, c x = δ) ∨
      (∀ x ∈ P, c x < δ) := by
  classical
  -- Split on whether the valid inequality is tight at some point of the affine subspace.
  by_cases hEq : ∃ x ∈ P, c x = δ
  · obtain ⟨x0, hx0, hx0_tight⟩ := hEq
    -- A single tight point propagates equality across the whole affine space by reflection.
    exact Or.inl (eq_everywhere_of_exists_tight_point P c δ hx0 hx0_tight hvalid)
  · -- Without a tight point, every valid inequality is automatically strict.
    exact Or.inr (strict_everywhere_of_no_tight_point P c δ hEq hvalid)

end OrderedRing

end

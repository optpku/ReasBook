import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Corollary 3.41 lives in finite-dimensional convex geometry.

Domain-style sampling for this refine pass:
* core/canonical owner: `Caratheodory.minCardFinsetOfMemConvexHull`
* canonical companion API:
  `Caratheodory.minCardFinsetOfMemConvexHull_subseteq`,
  `Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull`,
  `Caratheodory.mem_minCardFinsetOfMemConvexHull`
* dimension bound API: `AffineIndependent.card_le_finrank_succ`

The previous file duplicated this owner with a bespoke witness structure. The source-facing
corollary is better expressed by returning a finite subset witness directly, while the convex
combination itself remains encoded canonically as membership in `convexHull`.
-/

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Corollary 3.41. If `v ∈ convexHull 𝕜 X`, then `v` lies in the convex hull of at most
`dim(X) + 1` affinely independent points of `X`, where the dimension is that of the direction of
`affineSpan 𝕜 X`. -/
theorem exists_affineIndependent_convexCombination_of_mem_convexHull
    {X : Set E} {v : E} (hv : v ∈ convexHull 𝕜 X) :
    ∃ t : Finset E,
      (t : Set E) ⊆ X ∧
      AffineIndependent 𝕜 ((↑) : t → E) ∧
      v ∈ convexHull 𝕜 (t : Set E) ∧
      t.card ≤ Module.finrank 𝕜 (affineSpan 𝕜 X).direction + 1 := by
  let t := Caratheodory.minCardFinsetOfMemConvexHull hv
  refine ⟨t, Caratheodory.minCardFinsetOfMemConvexHull_subseteq hv,
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hv,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hv, ?_⟩
  have ht_card :
      Fintype.card t ≤ Module.finrank 𝕜 (vectorSpan 𝕜 (Set.range ((↑) : t → E))) + 1 := by
    simpa using
      (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hv).card_le_finrank_succ
  have ht_range_subset : Set.range ((↑) : t → E) ⊆ X := by
    rw [Subtype.range_coe_subtype]
    exact Caratheodory.minCardFinsetOfMemConvexHull_subseteq hv
  have ht_finrank :
      Module.finrank 𝕜 (vectorSpan 𝕜 (Set.range ((↑) : t → E))) ≤
        Module.finrank 𝕜 (affineSpan 𝕜 X).direction := by
    rw [direction_affineSpan]
    exact Submodule.finrank_mono (vectorSpan_mono 𝕜 ht_range_subset)
  have ht_bound :
      Fintype.card t ≤ Module.finrank 𝕜 (affineSpan 𝕜 X).direction + 1 :=
    ht_card.trans <| by simpa [add_comm] using add_le_add_right ht_finrank 1
  simpa using ht_bound

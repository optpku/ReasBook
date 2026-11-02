import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Module
open Set

-- `lean_leansearch` was unavailable in this environment; verified candidate API:
-- `Convex.radon_partition` in `Mathlib.Analysis.Convex.Radon`.

section Radon

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Helper for Theorem 3.43: a subset of a finite-dimensional vector space with exactly
`finrank 𝕜 E + 2` points is affinely dependent. -/
private lemma not_affineIndependent_subtype_val_of_encard_eq [FiniteDimensional 𝕜 E]
    (T : Set E) (hT : T.encard = finrank 𝕜 E + 2) :
    ¬ AffineIndependent 𝕜 (Subtype.val : T → E) := by
  classical
  letI : Fintype T := Set.Finite.fintype <| Set.finite_of_encard_eq_coe hT
  have hcard_enat : (Fintype.card T : ℕ∞) = finrank 𝕜 E + 2 := by
    rw [Set.coe_fintypeCard]
    exact hT
  have hcard : Fintype.card T = finrank 𝕜 E + 2 := ENat.coe_inj.mp hcard_enat
  rw [← finrank_vectorSpan_le_iff_not_affineIndependent 𝕜 (Subtype.val : T → E) hcard]
  exact Submodule.finrank_le _

section Ordered

variable [LinearOrder 𝕜]

/-- Helper for Theorem 3.43: the images of a subtype subset and its complement cover the ambient
subset. -/
private lemma subtype_val_image_union_compl_eq {α : Type*} (T : Set α) (I : Set T) :
    (Subtype.val '' I) ∪ (Subtype.val '' Iᶜ) = T := by
  -- The subtype coercion maps `I` and its complement onto a partition of the full subtype.
  rw [Set.image_union_image_compl_eq_range (Subtype.val : T → α),
    Subtype.range_coe_subtype, Set.setOf_mem_eq]

/-- Helper for Theorem 3.43: a Radon partition on a chosen subset extends to a Radon partition of
the ambient set by adjoining the unused points to the right side. -/
private lemma exists_partition_of_subset_image_partition
    {S T : Set E} (hTS : T ⊆ S) (I : Set T)
    (hI : (convexHull 𝕜 (Subtype.val '' I) ∩ convexHull 𝕜 (Subtype.val '' Iᶜ)).Nonempty) :
    ∃ left right : Set E,
      Disjoint left right ∧
        left ∪ right = S ∧
          (convexHull 𝕜 left ∩ convexHull 𝕜 right).Nonempty := by
  classical
  have h_left_subset : (Subtype.val '' I) ⊆ T := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  have h_image_disjoint : Disjoint (Subtype.val '' I) (Subtype.val '' Iᶜ) := by
    -- A point cannot come from both a subtype subset and its complement.
    refine Set.disjoint_left.2 ?_
    intro x hxI hxIc
    rcases hxI with ⟨y, hy, rfl⟩
    rcases hxIc with ⟨z, hz, hzval⟩
    have hyz : z = y := Subtype.ext hzval
    exact hz <| hyz ▸ hy
  have h_left_disjoint_diff : Disjoint (Subtype.val '' I) (S \ T) := by
    -- The left side stays inside `T`, while `S \ T` is disjoint from `T`.
    refine Set.disjoint_left.2 ?_
    intro x hx hxST
    exact hxST.2 <| h_left_subset hx
  refine ⟨Subtype.val '' I, (Subtype.val '' Iᶜ) ∪ (S \ T), ?_, ?_, ?_⟩
  · exact Set.disjoint_union_right.2 ⟨h_image_disjoint, h_left_disjoint_diff⟩
  · -- First recover the chosen subset `T`, then adjoin the unused points of `S`.
    calc
      (Subtype.val '' I) ∪ ((Subtype.val '' Iᶜ) ∪ (S \ T))
          = ((Subtype.val '' I) ∪ (Subtype.val '' Iᶜ)) ∪ (S \ T) := by
              rw [union_assoc]
      _ = T ∪ (S \ T) := by rw [subtype_val_image_union_compl_eq]
      _ = S := by simpa [union_comm] using union_diff_cancel hTS
  · -- The original Radon witness still lies in the larger right convex hull.
    refine hI.mono ?_
    intro x hx
    exact ⟨hx.1, convexHull_mono (subset_union_left : (Subtype.val '' Iᶜ) ⊆
      (Subtype.val '' Iᶜ) ∪ (S \ T)) hx.2⟩

section StrictOrdered

variable [IsStrictOrderedRing 𝕜]

/-- Theorem 3.43 (Radon), in coordinate-free form. Let `S` be a subset of a finite-dimensional
vector space over an ordered field with at least `finrank 𝕜 E + 2` points. Then `S` can be
partitioned into two sets `S₁` and `S₂` so that
`convexHull 𝕜 S₁ ∩ convexHull 𝕜 S₂` is nonempty. The textbook `ℝ^d` statement is the
specialization to `E = EuclideanSpace ℝ (Fin d)`. -/
theorem radon_theorem [FiniteDimensional 𝕜 E] (S : Set E)
    (h_card : (finrank 𝕜 E + 2 : ℕ∞) ≤ S.encard) :
    ∃ S₁ S₂ : Set E,
      Disjoint S₁ S₂ ∧
        S₁ ∪ S₂ = S ∧
          (convexHull 𝕜 S₁ ∩ convexHull 𝕜 S₂).Nonempty := by
  classical
  -- Follow the source proof: first freeze a `finrank 𝕜 E + 2` point subset of `S`.
  obtain ⟨T, hTS, hT⟩ := exists_subset_encard_eq h_card
  have h_dep : ¬ AffineIndependent 𝕜 (Subtype.val : T → E) :=
    not_affineIndependent_subtype_val_of_encard_eq T hT
  -- Mathlib's Radon theorem partitions the chosen subtype into two parts with intersecting hulls.
  obtain ⟨I, hI⟩ := Convex.radon_partition h_dep
  -- Extend that subtype partition back to all of `S`.
  exact exists_partition_of_subset_image_partition hTS I hI

end StrictOrdered
end Ordered
end Radon

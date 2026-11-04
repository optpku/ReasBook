/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Polyhedron
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_16.ch3_sec3_16_theorem_3_49

open scoped Matrix

section Proposition22

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_2/ch2_sec2_2_proposition_2_2.lean

Proposition 2.2. If `real_mixed_polyhedron A₁ G₁ b₁` is nonempty, then its inclusion in
`real_mixed_polyhedron A₂ G₂ b₂` is equivalent to a nonnegative row-multiplier certificate for
every row of the outer mixed system. -/
theorem real_mixed_polyhedron_subset_iff_row_certificate
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (hP₁_nonempty : (real_mixed_polyhedron A₁ G₁ b₁).Nonempty) :
    real_mixed_polyhedron A₁ G₁ b₁ ⊆ real_mixed_polyhedron A₂ G₂ b₂ ↔
      ∀ i : Fin m₂,
        ∃ u : Fin m₁ → ℝ,
          ∃ hu_nonneg : 0 ≤ u,
            u ᵥ* A₁ = A₂ i ∧
              u ᵥ* G₁ = G₂ i ∧
              u ⬝ᵥ b₁ ≤ b₂ i := by
  constructor
  · intro hsubset
    -- Flatten one feasible mixed point to supply the nonemptiness premise for Farkas' lemma.
    obtain ⟨xy₀, hxy₀⟩ := hP₁_nonempty
    have hflat_nonempty :
        (polyhedron_le_set (mixedConstraintMatrix A₁ G₁) b₁).Nonempty := by
      refine ⟨Fin.append xy₀.1 xy₀.2, ?_⟩
      rw [mem_polyhedron_le_set_iff, mixedConstraintMatrix_mulVec_append]
      exact mem_real_mixed_polyhedron_iff.mp hxy₀
    intro i
    have hvalid :
        is_valid_inequality (polyhedron_le_set (mixedConstraintMatrix A₁ G₁) b₁)
          (mixedConstraintMatrix A₂ G₂ i) (b₂ i) := by
      -- Pull a flattened point back to mixed coordinates and apply the assumed inclusion.
      intro z hz
      have hz_image :
          z ∈ (Fin.appendEquiv n p) '' real_mixed_polyhedron A₁ G₁ b₁ := by
        rw [image_real_mixed_polyhedron_eq_polyhedron_le_set]
        exact hz
      obtain ⟨xy, hxy, rfl⟩ := hz_image
      have hi := (mem_real_mixed_polyhedron_iff.mp (hsubset hxy)) i
      calc
        mixedConstraintMatrix A₂ G₂ i ⬝ᵥ Fin.append xy.1 xy.2 =
            (mixedConstraintMatrix A₂ G₂ *ᵥ Fin.append xy.1 xy.2) i := by rfl
        _ = (A₂ *ᵥ xy.1 + G₂ *ᵥ xy.2) i :=
          congrFun (mixedConstraintMatrix_mulVec_append A₂ G₂ xy.1 xy.2) i
        _ ≤ b₂ i := hi
    obtain ⟨u, hu_nonneg, hu_row, hu_rhs⟩ :=
      (valid_inequality_iff_exists_nonneg_row_multiplier
        (mixedConstraintMatrix A₁ G₁) b₁ (mixedConstraintMatrix A₂ G₂ i) (b₂ i)
        hflat_nonempty).mp hvalid
    -- Restrict the flattened row identity to each of the two coordinate blocks.
    have hu_A : u ᵥ* A₁ = A₂ i := by
      ext j
      have hj := congrFun hu_row (Fin.castAdd p j)
      simpa [mixedConstraintMatrix, Matrix.vecMul, dotProduct] using hj
    have hu_G : u ᵥ* G₁ = G₂ i := by
      ext j
      have hj := congrFun hu_row (Fin.natAdd n j)
      simpa [mixedConstraintMatrix, Matrix.vecMul, dotProduct] using hj
    exact ⟨u, hu_nonneg, hu_A, hu_G, hu_rhs⟩
  · intro hcertificate xy hxy
    rw [mem_real_mixed_polyhedron_iff]
    have hinner := mem_real_mixed_polyhedron_iff.mp hxy
    intro i
    obtain ⟨u, hu_nonneg, hu_A, hu_G, hu_rhs⟩ := hcertificate i
    -- Weight the inner system by the nonnegative certificate and identify its two blocks.
    have hweighted :
        u ⬝ᵥ (A₁ *ᵥ xy.1 + G₁ *ᵥ xy.2) ≤ u ⬝ᵥ b₁ :=
      dotProduct_le_dotProduct_of_nonneg_left hinner hu_nonneg
    calc
      (A₂ *ᵥ xy.1 + G₂ *ᵥ xy.2) i =
          (A₂ i) ⬝ᵥ xy.1 + (G₂ i) ⬝ᵥ xy.2 := by rfl
      _ = (u ᵥ* A₁) ⬝ᵥ xy.1 + (u ᵥ* G₁) ⬝ᵥ xy.2 := by rw [hu_A, hu_G]
      _ = u ⬝ᵥ (A₁ *ᵥ xy.1) + u ⬝ᵥ (G₁ *ᵥ xy.2) := by
        rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
      _ = u ⬝ᵥ (A₁ *ᵥ xy.1 + G₁ *ᵥ xy.2) := by rw [dotProduct_add]
      _ ≤ u ⬝ᵥ b₁ := hweighted
      _ ≤ b₂ i := hu_rhs

end Proposition22

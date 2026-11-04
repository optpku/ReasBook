/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1

open scoped Matrix

section MixedPolyhedron

/-- The flattened block matrix `[A G]` whose rows encode the mixed system
`A *ᵥ x + G *ᵥ y ≤ b`. -/
def mixedConstraintMatrix
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ) :
    Matrix (Fin m) (Fin (n + p)) ℝ :=
  fun i ↦ Fin.addCases (A i) (G i)

/-- Multiplying `mixedConstraintMatrix A G` against `Fin.append x y` recovers the mixed left-hand
side `A *ᵥ x + G *ᵥ y`. -/
theorem mixedConstraintMatrix_mulVec_append
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (x : Fin n → ℝ)
    (y : Fin p → ℝ) :
    mixedConstraintMatrix A G *ᵥ Fin.append x y = A *ᵥ x + G *ᵥ y := by
  -- Split the block matrix-vector product along the appended coordinates.
  ext i
  simp [mixedConstraintMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

/-- The mixed polyhedron cut out by the real block system `A *ᵥ x + G *ᵥ y ≤ b`, pulled back from
the flat owner on `Fin (n + p) → ℝ` along `Fin.appendEquiv`. -/
def real_mixed_polyhedron
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    Set (MixedRealPoint n p) :=
  (Fin.appendEquiv n p).symm '' polyhedron_le_set (mixedConstraintMatrix A G) b

/-- Membership in `real_mixed_polyhedron A G b` is exactly the inequality system
`A *ᵥ x + G *ᵥ y ≤ b`. -/
theorem mem_real_mixed_polyhedron_iff
    {m n p : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin p) ℝ}
    {b : Fin m → ℝ}
    {xy : MixedRealPoint n p} :
    xy ∈ real_mixed_polyhedron A G b ↔ A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    -- Rewrite the flattened witness back into the original block coordinates.
    rw [mem_polyhedron_le_set_iff] at hw
    have hw' :
        mixedConstraintMatrix A G *ᵥ
            Fin.append (fun i ↦ w (Fin.castAdd p i)) (fun i ↦ w (Fin.natAdd n i)) ≤ b := by
      simpa [Fin.append_castAdd_natAdd] using hw
    simpa [mixedConstraintMatrix_mulVec_append] using hw'
  · intro hxy
    -- Package the mixed point as a single flat vector in the ambient polyhedron.
    refine ⟨Fin.append xy.1 xy.2, ?_, ?_⟩
    · simpa [mem_polyhedron_le_set_iff, mixedConstraintMatrix_mulVec_append] using hxy
    · ext i <;> simp [Fin.appendEquiv]

/-- A subset of the mixed space is a mixed polyhedron when its flattening along `Fin.appendEquiv`
is a polyhedron in the canonical Chapter 3 sense. -/
def is_mixed_polyhedron
    {n p : ℕ}
    (P : Set (MixedRealPoint n p)) : Prop :=
  is_polyhedron ((Fin.appendEquiv n p) '' P)

/-- Unfolding equation for `is_mixed_polyhedron`. -/
theorem is_mixed_polyhedron_iff
    {n p : ℕ}
    {P : Set (MixedRealPoint n p)} :
    is_mixed_polyhedron P ↔ is_polyhedron ((Fin.appendEquiv n p) '' P) := by
  rfl

/-- Flattening `real_mixed_polyhedron A G b` along `Fin.appendEquiv` recovers the flat polyhedron
cut out by `mixedConstraintMatrix A G`. -/
theorem image_real_mixed_polyhedron_eq_polyhedron_le_set
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    (Fin.appendEquiv n p) '' real_mixed_polyhedron A G b =
      polyhedron_le_set (mixedConstraintMatrix A G) b := by
  ext z
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    rcases hxy with ⟨w, hw, rfl⟩
    simpa [Fin.appendEquiv, Fin.append_castAdd_natAdd] using hw
  · intro hz
    refine ⟨(Fin.appendEquiv n p).symm z, ?_, ?_⟩
    · exact ⟨z, hz, rfl⟩
    · simpa using (Fin.appendEquiv n p).apply_symm_apply z

/-- Every explicit mixed-system presentation `real_mixed_polyhedron A G b` defines a mixed
polyhedron in the canonical flattened owner. -/
theorem is_mixed_polyhedron_real_mixed_polyhedron
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    is_mixed_polyhedron (real_mixed_polyhedron A G b) := by
  refine ⟨m, mixedConstraintMatrix A G, b, ?_⟩
  exact image_real_mixed_polyhedron_eq_polyhedron_le_set A G b

end MixedPolyhedron

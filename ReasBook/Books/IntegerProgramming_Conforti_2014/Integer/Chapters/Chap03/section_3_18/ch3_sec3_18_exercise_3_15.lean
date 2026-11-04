/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_corollary_3_23
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2

open scoped Matrix

section Exercise315

variable {m n : ℕ}

/-- The coordinate section of `{x | A *ᵥ x ≥ b}` cut out by `x j = 0` is the canonical equality
face of the Chapter 3 polyhedron owner `polyhedron_le_set (-A) (-b)` defined by the coordinate
functional `Pi.single j 1`. -/
theorem mem_coordinate_face_iff
    {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {j : Fin n} {x : Fin n → ℝ} :
    x ∈ face_set (polyhedron_le_set (-A) (-b)) (Pi.single j (1 : ℝ)) 0 ↔
      b ≤ A *ᵥ x ∧ x j = 0 := by
  rw [mem_face_set_iff]
  constructor
  · rintro ⟨hx, hxj⟩
    refine ⟨?_, ?_⟩
    · intro i
      have hx' : -((A *ᵥ x) i) ≤ -(b i) := by
        simpa [polyhedron_le_set, Matrix.neg_mulVec] using hx i
      simpa using neg_le_neg hx'
    · simpa [dotProduct, Pi.single_apply] using hxj
  · rintro ⟨hx, hxj⟩
    refine ⟨?_, ?_⟩
    · intro i
      have hx' : -((A *ᵥ x) i) ≤ -(b i) := neg_le_neg (hx i)
      simpa [polyhedron_le_set, Matrix.neg_mulVec] using hx'
    · simpa [dotProduct, Pi.single_apply] using hxj

/-- The source-facing inequality `β ≤ α ⬝ᵥ x` is exactly the Chapter 3 valid inequality
`(-α) ⬝ᵥ x ≤ -β`. -/
theorem valid_ge_inequality_iff_is_valid_inequality_neg
    {P : Set (Fin n → ℝ)} {α : Fin n → ℝ} {β : ℝ} :
    (∀ ⦃x : Fin n → ℝ⦄, x ∈ P → β ≤ α ⬝ᵥ x) ↔ is_valid_inequality P (-α) (-β) := by
  constructor
  · intro h x hx
    have hx' : β ≤ α ⬝ᵥ x := h hx
    simpa [dotProduct_neg] using neg_le_neg hx'
  · intro h x hx
    have hx' : (-α) ⬝ᵥ x ≤ -β := h hx
    simpa [dotProduct_neg] using neg_le_neg hx'

/-- Helper for Exercise 3.15: the coordinate section `x j = 0` of the ambient polyhedron is the
same set as the mixed system obtained by adding the single equality row `Pi.single j 1`. -/
lemma mem_coordinate_section_iff_mem_mixed_constraint_polyhedron
    {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {j : Fin n} {x : Fin n → ℝ} :
    x ∈ face_set (polyhedron_le_set (-A) (-b)) (Pi.single j (1 : ℝ)) 0 ↔
      x ∈ mixed_constraint_polyhedron (-A) (-b) (fun _ ↦ Pi.single j (1 : ℝ))
        (0 : Fin 1 → ℝ) := by
  -- Reinterpret the face equation `x j = 0` as a one-row equality subsystem.
  rw [mem_coordinate_face_iff, mem_mixed_constraint_polyhedron]
  constructor
  · rintro ⟨hx, hxj⟩
    refine ⟨?_, ?_⟩
    · intro i
      have hx' : -((A *ᵥ x) i) ≤ -(b i) := neg_le_neg (hx i)
      simpa [Matrix.neg_mulVec] using hx'
    ext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hxj]
  · rintro ⟨hx, hxeq⟩
    refine ⟨?_, ?_⟩
    · intro i
      have hx' : -((A *ᵥ x) i) ≤ -(b i) := by
        simpa [Matrix.neg_mulVec] using hx i
      simpa using neg_le_neg hx'
    have hrow : ((fun _ : Fin 1 ↦ Pi.single j (1 : ℝ)) *ᵥ x) 0 = 0 := by
      exact congrFun hxeq 0
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hrow

/-- Helper for Exercise 3.15: multiplying the one-row coordinate matrix on the left picks out a
scalar multiple of the coordinate vector `Pi.single j 1`. -/
lemma vecMul_coordinate_row_eq_smul_single
    {j : Fin n} (v : Fin 1 → ℝ) :
    v ᵥ* (fun _ : Fin 1 ↦ Pi.single j (1 : ℝ)) = (v 0) • Pi.single j (1 : ℝ) := by
  -- The only row index is `0`, so the row combination collapses to one scalar multiple.
  ext k
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

/-- Helper for Exercise 3.15: the mixed multiplier row equation is equivalent to the lifted
coefficient vector `-(α + (v 0) • Pi.single j 1)` needed for the ambient polyhedron certificate. -/
lemma mixed_row_certificate_eq_neg_lifted_coefficient
    {A : Matrix (Fin m) (Fin n) ℝ} {j : Fin n} {α : Fin n → ℝ}
    {u : Fin m → ℝ} {v : Fin 1 → ℝ}
    (hrow :
      u ᵥ* (-A) + v ᵥ* (fun _ : Fin 1 ↦ Pi.single j (1 : ℝ)) = -α) :
    u ᵥ* (-A) = -(α + (v 0) • Pi.single j (1 : ℝ)) := by
  -- Rewrite the `Fin 1` row contribution as a single-coordinate vector and isolate `u ᵥ* (-A)`.
  rw [vecMul_coordinate_row_eq_smul_single] at hrow
  ext k
  change (u ᵥ* (-A)) k = -(α k + ((v 0) • Pi.single j (1 : ℝ)) k)
  have hk : (u ᵥ* (-A)) k + ((v 0) • Pi.single j (1 : ℝ)) k = -α k := by
    simpa using congrFun hrow k
  linarith

/-- Exercise 3.15. If the inequality `β ≤ α ⬝ᵥ x` is valid on the coordinate face of
`{x | A *ᵥ x ≥ b}` cut out by `x j = 0`, then one can add a suitable multiple of `x j` to obtain a
valid inequality on the whole polyhedron. The companion lemma
`valid_ge_inequality_iff_is_valid_inequality_neg` converts this source-facing formulation to the
Chapter 3 owner `is_valid_inequality` when needed. -/
theorem valid_inequality_lift_from_coordinate_section
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin n)
    (α : Fin n → ℝ)
    (β : ℝ)
    (h_section_nonempty :
      Set.Nonempty (face_set (polyhedron_le_set (-A) (-b)) (Pi.single j (1 : ℝ)) 0))
    (hvalid :
      ∀ ⦃x : Fin n → ℝ⦄,
        x ∈ face_set (polyhedron_le_set (-A) (-b)) (Pi.single j (1 : ℝ)) 0 →
          β ≤ α ⬝ᵥ x) :
    ∃ c : ℝ,
      ∀ ⦃x : Fin n → ℝ⦄,
        x ∈ polyhedron_le_set (-A) (-b) →
          β ≤ (α + c • Pi.single j (1 : ℝ)) ⬝ᵥ x := by
  let Cj : Matrix (Fin 1) (Fin n) ℝ := fun _ ↦ Pi.single j (1 : ℝ)
  let d0 : Fin 1 → ℝ := 0
  rcases h_section_nonempty with ⟨x₀, hx₀_face⟩
  have hmixed_nonempty : Set.Nonempty (mixed_constraint_polyhedron (-A) (-b) Cj d0) := by
    -- Transport the given nonempty section across the face/mixed-system equivalence.
    refine ⟨x₀, ?_⟩
    simpa [Cj, d0] using
      (mem_coordinate_section_iff_mem_mixed_constraint_polyhedron.mp hx₀_face)
  have hvalid_mixed_ge :
      ∀ ⦃x : Fin n → ℝ⦄,
        x ∈ mixed_constraint_polyhedron (-A) (-b) Cj d0 →
          β ≤ α ⬝ᵥ x := by
    -- The original valid inequality is exactly the same statement on the mixed-system owner.
    intro x hx
    have hx_face :
        x ∈ face_set (polyhedron_le_set (-A) (-b)) (Pi.single j (1 : ℝ)) 0 := by
      simpa [Cj, d0] using
        (mem_coordinate_section_iff_mem_mixed_constraint_polyhedron.mpr hx)
    exact hvalid hx_face
  have hvalid_mixed :
      is_valid_inequality (mixed_constraint_polyhedron (-A) (-b) Cj d0) (-α) (-β) := by
    -- Convert the source-facing `β ≤ α ⬝ᵥ x` form to the chapter-validity owner.
    exact valid_ge_inequality_iff_is_valid_inequality_neg.mp hvalid_mixed_ge
  rcases
      (valid_inequality_iff_exists_mixed_row_multiplier (-A) (-b) Cj d0 (-α) (-β)
        hmixed_nonempty).mp hvalid_mixed with
    ⟨u, v, hu_nonneg, hrow, hδ⟩
  have hrow_lifted :
      u ᵥ* (-A) = -(α + (v 0) • Pi.single j (1 : ℝ)) := by
    -- Rewrite the mixed equality certificate into the ambient polyhedron coefficient.
    simpa [Cj] using
      mixed_row_certificate_eq_neg_lifted_coefficient (A := A) (j := j) (α := α) hrow
  have hδ' : u ⬝ᵥ (-b) ≤ -β := by
    -- The equality right-hand side is zero, so its multiplier term vanishes.
    simpa [Cj, d0] using hδ
  have hvalid_ambient_neg :
      is_valid_inequality
        (polyhedron_le_set (-A) (-b))
        (-(α + (v 0) • Pi.single j (1 : ℝ)))
        (-β) := by
    -- Evaluate the row certificate on every feasible point of the ambient polyhedron.
    intro x hx
    calc
      (-(α + (v 0) • Pi.single j (1 : ℝ))) ⬝ᵥ x = (u ᵥ* (-A)) ⬝ᵥ x := by
        rw [hrow_lifted]
      _ = u ⬝ᵥ ((-A) *ᵥ x) := by
        rw [Matrix.dotProduct_mulVec]
      _ ≤ u ⬝ᵥ (-b) := dotProduct_le_dotProduct_of_nonneg_left hx hu_nonneg
      _ ≤ -β := hδ'
  refine ⟨v 0, ?_⟩
  -- Convert the ambient valid inequality back to the textbook `β ≤ ...` formulation.
  exact valid_ge_inequality_iff_is_valid_inequality_neg.mpr hvalid_ambient_neg

end Exercise315

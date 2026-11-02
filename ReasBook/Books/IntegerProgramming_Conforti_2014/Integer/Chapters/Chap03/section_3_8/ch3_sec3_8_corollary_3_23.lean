import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1

open scoped Matrix

-- Domain sampling for this corollary:
-- * primary domain: valid inequalities of mixed equality/inequality polyhedra in `ℝ^n`
-- * source-facing owner: `mixed_constraint_polyhedron`
-- * core/canonical owner: `is_valid_inequality`
-- * supporting chapter theorem: `valid_inequality_iff_exists_nonneg_row_multiplier`
-- * primitive data: the mixed system `A *ᵥ x ≤ b`, `C *ᵥ x = d`
-- * derived API: membership in the mixed polyhedron and the multiplier feasibility conclusion

section Corollary_3_23

variable {m p n : ℕ}

/-- The mixed polyhedron cut out by `A *ᵥ x ≤ b` and `C *ᵥ x = d`. -/
def mixed_constraint_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ) :
    Set (Fin n → ℝ) :=
  {x | A *ᵥ x ≤ b ∧ C *ᵥ x = d}

/-- Membership in `mixed_constraint_polyhedron` means satisfying the inequality subsystem
`A *ᵥ x ≤ b` and the equality subsystem `C *ᵥ x = d`. -/
theorem mem_mixed_constraint_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ)
    (x : Fin n → ℝ) :
    x ∈ mixed_constraint_polyhedron A b C d ↔ A *ᵥ x ≤ b ∧ C *ᵥ x = d :=
  Iff.rfl

/-- Helper for Corollary 3.23: the mixed system `A *ᵥ x ≤ b`, `C *ᵥ x = d` is equivalent to the
stacked inequality system obtained by adjoining the opposite inequalities `-C *ᵥ x ≤ -d`. -/
private lemma stackedMixedConstraintSystem_feasible_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ)
    (x : Fin n → ℝ) :
    Matrix.fromRows (Matrix.fromRows A C) (-C) *ᵥ x ≤ Sum.elim (Sum.elim b d) (-d) ↔
      x ∈ mixed_constraint_polyhedron A b C d := by
  constructor
  · intro hx
    rw [mem_mixed_constraint_polyhedron]
    constructor
    · intro i
      -- The top block of the stacked system is exactly the original inequality subsystem.
      have hi :
          (Matrix.fromRows (Matrix.fromRows A C) (-C) *ᵥ x) (Sum.inl (Sum.inl i)) ≤
            Sum.elim (Sum.elim b d) (-d) (Sum.inl (Sum.inl i)) :=
        hx (Sum.inl (Sum.inl i))
      simpa [Matrix.fromRows_mulVec] using hi
    · apply le_antisymm
      · intro i
        -- The middle block recovers the forward inequality `C *ᵥ x ≤ d`.
        have hi :
            (Matrix.fromRows (Matrix.fromRows A C) (-C) *ᵥ x) (Sum.inl (Sum.inr i)) ≤
              Sum.elim (Sum.elim b d) (-d) (Sum.inl (Sum.inr i)) :=
          hx (Sum.inl (Sum.inr i))
        simpa [Matrix.fromRows_mulVec] using hi
      · intro i
        -- The bottom block yields the reverse inequality after removing the minus signs.
        have hi :
            (Matrix.fromRows (Matrix.fromRows A C) (-C) *ᵥ x) (Sum.inr i) ≤
              Sum.elim (Sum.elim b d) (-d) (Sum.inr i) :=
          hx (Sum.inr i)
        have hi' : -((C *ᵥ x) i) ≤ (-d) i := by
          simpa [Matrix.fromRows_mulVec, Matrix.neg_mulVec] using hi
        simpa using (neg_le_neg_iff.mp hi')
  · intro hx
    rw [mem_mixed_constraint_polyhedron] at hx
    intro s
    rcases s with (i | i) | i
    · -- The first block is supplied directly by the inequality membership certificate.
      simpa [Matrix.fromRows_mulVec] using hx.1 i
    · -- Equality constraints contribute the forward inequality on the second block.
      have hi : (C *ᵥ x) i ≤ d i := le_of_eq (congrFun hx.2 i)
      simpa [Matrix.fromRows_mulVec] using hi
    · -- Equality constraints also give the negated inequality on the third block.
      have hi : -((C *ᵥ x) i) ≤ (-d) i := by
        simp [congrFun hx.2 i]
      simpa [Matrix.fromRows_mulVec, Matrix.neg_mulVec] using hi

/-- Helper for Corollary 3.23: a nonnegative multiplier on the stacked inequality system
compresses to the mixed certificate `(u, v)` with unrestricted equality multiplier `v`. -/
private lemma exists_mixedRowMultiplier_of_stackedMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ)
    (w : ((Fin m ⊕ Fin p) ⊕ Fin p) → ℝ)
    (hw_nonneg : 0 ≤ w)
    (hrow : w ᵥ* Matrix.fromRows (Matrix.fromRows A C) (-C) = c)
    (hδ : w ⬝ᵥ Sum.elim (Sum.elim b d) (-d) ≤ δ) :
    ∃ u : Fin m → ℝ, ∃ v : Fin p → ℝ,
      0 ≤ u ∧ u ᵥ* A + v ᵥ* C = c ∧ u ⬝ᵥ b + v ⬝ᵥ d ≤ δ := by
  let u : Fin m → ℝ := (w ∘ Sum.inl) ∘ Sum.inl
  let v₁ : Fin p → ℝ := (w ∘ Sum.inl) ∘ Sum.inr
  let v₂ : Fin p → ℝ := w ∘ Sum.inr
  let v : Fin p → ℝ := v₁ - v₂
  refine ⟨u, v, ?_, ?_, ?_⟩
  · -- Only the original inequality block needs nonnegative multipliers.
    intro i
    exact hw_nonneg (Sum.inl (Sum.inl i))
  · -- Split the stacked row equation into the inequality and equality blocks.
    ext j
    have hj :
        (u ᵥ* A) j + (v₁ ᵥ* C) j - (v₂ ᵥ* C) j = c j := by
      simpa [Function.comp, u, v₁, v₂, Matrix.vecMul_fromRows, Matrix.vecMul_neg,
        Pi.add_apply, sub_eq_add_neg, add_assoc] using congrFun hrow j
    have hvCj : (v ᵥ* C) j = (v₁ ᵥ* C) j - (v₂ ᵥ* C) j := by
      simpa [v] using congrFun (Matrix.sub_vecMul C v₁ v₂) j
    have hEq : (u ᵥ* A) j + ((v₁ ᵥ* C) j - (v₂ ᵥ* C) j) = c j := by
      simpa [sub_eq_add_neg, add_assoc] using hj
    simpa [Pi.add_apply, hvCj] using hEq
  · -- The scalar certificate splits in the same way across the three row blocks.
    have hw_split :
        w = Sum.elim (Sum.elim u v₁) v₂ := by
      funext s
      rcases s with (i | i) | i <;> rfl
    have h_rhs :
        w ⬝ᵥ Sum.elim (Sum.elim b d) (-d) = u ⬝ᵥ b + v ⬝ᵥ d := by
      calc
        w ⬝ᵥ Sum.elim (Sum.elim b d) (-d)
            = Sum.elim (Sum.elim u v₁) v₂ ⬝ᵥ Sum.elim (Sum.elim b d) (-d) := by
                rw [hw_split]
        _ = (Sum.elim u v₁) ⬝ᵥ Sum.elim b d + v₂ ⬝ᵥ (-d) := by
              rw [sumElim_dotProduct_sumElim]
        _ = (u ⬝ᵥ b + v₁ ⬝ᵥ d) + v₂ ⬝ᵥ (-d) := by
              rw [sumElim_dotProduct_sumElim]
        _ = u ⬝ᵥ b + v ⬝ᵥ d := by
              simp [v, sub_eq_add_neg, add_assoc]
    rw [h_rhs] at hδ
    exact hδ

/-- Helper for Corollary 3.23: any feasible mixed multiplier certificate yields a valid
inequality on the mixed polyhedron. -/
private lemma isValidInequality_of_mixedRowMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ)
    (u : Fin m → ℝ)
    (v : Fin p → ℝ)
    (hu_nonneg : 0 ≤ u)
    (hrow : u ᵥ* A + v ᵥ* C = c)
    (hδ : u ⬝ᵥ b + v ⬝ᵥ d ≤ δ) :
    is_valid_inequality (mixed_constraint_polyhedron A b C d) c δ := by
  rw [is_valid_inequality_iff]
  intro x hx
  rw [mem_mixed_constraint_polyhedron] at hx
  -- Evaluate the row identity at `x`, then bound the inequality block by feasibility.
  calc
    c ⬝ᵥ x = (u ᵥ* A + v ᵥ* C) ⬝ᵥ x := by rw [← hrow]
    _ = (u ᵥ* A) ⬝ᵥ x + (v ᵥ* C) ⬝ᵥ x := by rw [add_dotProduct]
    _ = u ⬝ᵥ (A *ᵥ x) + v ⬝ᵥ (C *ᵥ x) := by
          rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
    _ = u ⬝ᵥ (A *ᵥ x) + v ⬝ᵥ d := by rw [hx.2]
    _ ≤ u ⬝ᵥ b + v ⬝ᵥ d := by
          gcongr
          exact dotProduct_le_dotProduct_of_nonneg_left hx.1 hu_nonneg
    _ ≤ δ := hδ

/-- Corollary 3.23. Let `P := {x | A *ᵥ x ≤ b, C *ᵥ x = d}` be a nonempty polyhedron. An
inequality `c ⬝ᵥ x ≤ δ` is valid for `P` if and only if the system
`u ᵥ* A + v ᵥ* C = c`, `u ⬝ᵥ b + v ⬝ᵥ d ≤ δ`, `0 ≤ u` is feasible. -/
theorem valid_inequality_iff_exists_mixed_row_multiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin p → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ)
    (hP_nonempty : (mixed_constraint_polyhedron A b C d).Nonempty) :
    is_valid_inequality (mixed_constraint_polyhedron A b C d) c δ ↔
      ∃ u : Fin m → ℝ, ∃ v : Fin p → ℝ,
        0 ≤ u ∧ u ᵥ* A + v ᵥ* C = c ∧ u ⬝ᵥ b + v ⬝ᵥ d ≤ δ := by
  constructor
  · intro hvalid
    let M : Matrix ((Fin m ⊕ Fin p) ⊕ Fin p) (Fin n) ℝ :=
      Matrix.fromRows (Matrix.fromRows A C) (-C)
    let r : ((Fin m ⊕ Fin p) ⊕ Fin p) → ℝ := Sum.elim (Sum.elim b d) (-d)
    have hM_nonempty : Set.Nonempty {x : Fin n → ℝ | M *ᵥ x ≤ r} := by
      rcases hP_nonempty with ⟨x₀, hx₀⟩
      refine ⟨x₀, ?_⟩
      -- Rewrite the mixed feasibility witness into the stacked inequality owner.
      simpa [M, r] using
        (stackedMixedConstraintSystem_feasible_iff A b C d x₀).mpr hx₀
    have hvalid_stacked :
        ∀ ⦃x : Fin n → ℝ⦄, x ∈ {x : Fin n → ℝ | M *ᵥ x ≤ r} → c ⬝ᵥ x ≤ δ := by
      intro x hx
      -- Every feasible point of the stacked system is feasible for the mixed owner.
      have hx_mixed : x ∈ mixed_constraint_polyhedron A b C d := by
        simpa [M, r] using (stackedMixedConstraintSystem_feasible_iff A b C d x).mp hx
      exact hvalid hx_mixed
    obtain ⟨w, hw_nonneg, hw_row, hw_δ⟩ :=
      exists_nonneg_row_multiplier_of_valid_inequality M r c δ hM_nonempty hvalid_stacked
    -- Compress the stacked nonnegative certificate to the textbook `(u, v)` certificate.
    exact exists_mixedRowMultiplier_of_stackedMultiplier A b C d c δ w hw_nonneg hw_row hw_δ
  · rintro ⟨u, v, hu_nonneg, hrow, hδ⟩
    -- Route correction: the reverse implication closes directly on each feasible `x`; no
    -- stacked re-encoding is needed once the mixed row certificate is available.
    exact isValidInequality_of_mixedRowMultiplier A b C d c δ u v hu_nonneg hrow hδ

end Corollary_3_23

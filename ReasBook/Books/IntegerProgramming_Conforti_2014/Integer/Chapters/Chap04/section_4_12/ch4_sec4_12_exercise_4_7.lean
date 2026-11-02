import Mathlib

open scoped Matrix

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file uses
-- direct local inspection of Mathlib's `Matrix.IsTotallyUnimodular` API together with the
-- source-facing signed-matrix owner and a Boolean sign-pattern bridge.

namespace Matrix

section Signing

variable {m n α : Type*} [Neg α]

/-- `ε.signed A` is the matrix obtained by negating exactly the entries of `A` marked by the
Boolean sign pattern `ε`. -/
def signed (ε : Matrix m n Bool) (A : Matrix m n α) : Matrix m n α :=
  fun i j ↦ if ε i j then -(A i j) else A i j

/-- Entrywise description of `Matrix.signed`. -/
theorem signed_apply (ε : Matrix m n Bool) (A : Matrix m n α) (i : m) (j : n) :
    ε.signed A i j = if ε i j then -(A i j) else A i j :=
  rfl

/-- A matrix `S` is a signing of `A` if it is obtained from `A` by an entrywise choice of signs. -/
def IsSigningOf (S A : Matrix m n α) : Prop :=
  ∀ i j, S i j = A i j ∨ S i j = -(A i j)

/-- Source-facing characterization of `Matrix.IsSigningOf`. -/
theorem isSigningOf_iff {S A : Matrix m n α} :
    S.IsSigningOf A ↔ ∀ i j, S i j = A i j ∨ S i j = -(A i j) :=
  Iff.rfl

/-- The Boolean sign-pattern presentation is equivalent to the source-facing signing property. -/
theorem isSigningOf_iff_exists_signed {S A : Matrix m n α} :
    S.IsSigningOf A ↔ ∃ ε : Matrix m n Bool, ε.signed A = S := by
  classical
  constructor
  · intro h
    refine ⟨fun i j ↦ S i j ≠ A i j, ?_⟩
    ext i j
    by_cases hij : S i j = A i j
    · simp [signed, hij]
    · rcases h i j with hij' | hij'
      · exact (hij hij').elim
      · simpa [signed, hij] using hij'.symm
  · rintro ⟨ε, rfl⟩ i j
    by_cases hij : ε i j
    · simp [signed, hij]
    · simp [signed, hij]

end Signing

section TotallyUnimodularSigning

variable {m n R : Type*} [CommRing R]

/-- A matrix has a totally unimodular signing if some signing of it is totally unimodular. -/
def HasTotallyUnimodularSigning (A : Matrix m n R) : Prop :=
  ∃ S : Matrix m n R, S.IsSigningOf A ∧ S.IsTotallyUnimodular

/-- The Boolean sign-pattern presentation is a bridge to the source-facing signed-matrix owner. -/
theorem hasTotallyUnimodularSigning_iff (A : Matrix m n R) :
    A.HasTotallyUnimodularSigning ↔
      ∃ ε : Matrix m n Bool, (ε.signed A).IsTotallyUnimodular := by
  constructor
  · rintro ⟨S, hS, hTU⟩
    rcases (isSigningOf_iff_exists_signed).1 hS with ⟨ε, rfl⟩
    exact ⟨ε, hTU⟩
  · rintro ⟨ε, hTU⟩
    exact ⟨ε.signed A, (isSigningOf_iff_exists_signed).2 ⟨ε, rfl⟩, hTU⟩

end TotallyUnimodularSigning

end Matrix

/-- The `3 × 4` `0,1` matrix on the left in Exercise 4.7. -/
def exercise_4_7_left_matrix : Matrix (Fin 3) (Fin 4) ℤ :=
  !![(1 : ℤ), 1, 1, 0;
    1, 0, 1, 1;
    1, 1, 0, 1]

/-- The `5 × 5` `0,1` matrix on the right in Exercise 4.7. -/
def exercise_4_7_right_matrix : Matrix (Fin 5) (Fin 5) ℤ :=
  !![(1 : ℤ), 1, 0, 0, 1;
    1, 1, 1, 0, 0;
    0, 1, 1, 1, 0;
    0, 0, 1, 1, 1;
    1, 0, 0, 1, 1]

/-- An explicit signing of the right-hand matrix from Exercise 4.7. -/
def exercise_4_7_right_signed_matrix : Matrix (Fin 5) (Fin 5) ℤ :=
  !![(1 : ℤ), -1, 0, 0, 1;
    -1, 1, 1, 0, 0;
    0, 1, 1, 1, 0;
    0, 0, 1, 1, 1;
    1, 0, 0, 1, 1]

/-- The explicit signed matrix for Exercise 4.7 is indeed a signing of the right-hand `0,1`
matrix. -/
theorem exercise_4_7_right_signed_matrix_is_signing :
    exercise_4_7_right_signed_matrix.IsSigningOf exercise_4_7_right_matrix := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- Helper for Exercise 4.7: the integer sign attached to a Boolean choice. -/
def boolean_sign (b : Bool) : ℤ :=
  if b then -1 else 1

/-- Helper for Exercise 4.7: a Boolean sign choice is always `1` or `-1`. -/
lemma boolean_sign_eq_one_or_neg_one (b : Bool) :
    boolean_sign b = 1 ∨ boolean_sign b = -1 := by
  cases b <;> simp [boolean_sign]

/-- Helper for Exercise 4.7: squaring a Boolean sign choice gives `1`. -/
lemma boolean_sign_sq (b : Bool) : boolean_sign b * boolean_sign b = 1 := by
  cases b <;> simp [boolean_sign]

/-- Helper for Exercise 4.7: the product of two sign values is again a sign value. -/
lemma mul_eq_one_or_neg_one_of_sign_values {a b : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl
  · simpa using hb
  · rcases hb with rfl | rfl
    · right
      norm_num
    · left
      norm_num

/-- Helper for Exercise 4.7: the product of three sign values is again a sign value. -/
lemma mul_three_eq_one_or_neg_one_of_sign_values {a b c : ℤ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) :
    a * b * c = 1 ∨ a * b * c = -1 := by
  have hab : a * b = 1 ∨ a * b = -1 :=
    mul_eq_one_or_neg_one_of_sign_values ha hb
  exact mul_eq_one_or_neg_one_of_sign_values hab hc

/-- Helper for Exercise 4.7: a dense `2 × 2` sign matrix with negative entry-product has
determinant `±2`. -/
lemma exercise_4_7_two_by_two_det_of_negative_entry_product
    {a b c d : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (hprod : a * b * c * d = -1) :
    Matrix.det !![a, b; c, d] = 2 ∨ Matrix.det !![a, b; c, d] = -2 := by
  -- Rewrite the determinant through the two diagonal products.
  have had : a * d = 1 ∨ a * d = -1 :=
    mul_eq_one_or_neg_one_of_sign_values ha hd
  have hbc : b * c = 1 ∨ b * c = -1 :=
    mul_eq_one_or_neg_one_of_sign_values hb hc
  have hfactor : (a * d) * (b * c) = -1 := by
    calc
      (a * d) * (b * c) = a * b * c * d := by ring
      _ = -1 := hprod
  rcases had with had | had
  · have hbc' : b * c = -1 := by
      rcases hbc with hbc | hbc
      · exfalso
        nlinarith [hfactor, had, hbc]
      · exact hbc
    left
    rw [Matrix.det_fin_two_of]
    nlinarith [had, hbc']
  · have hbc' : b * c = 1 := by
      rcases hbc with hbc | hbc
      · exact hbc
      · exfalso
        nlinarith [hfactor, had, hbc]
    right
    rw [Matrix.det_fin_two_of]
    nlinarith [had, hbc']

/-- Helper for Exercise 4.7: the cycle-shaped `3 × 3` sign matrix with positive nonzero-entry
product has determinant `±2`. -/
lemma exercise_4_7_cycle_three_by_three_det_of_positive_entry_product
    {a b c d e f : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (hprod : a * b * c * d * e * f = 1) :
    Matrix.det !![a, b, 0; 0, c, d; e, 0, f] = 2 ∨
      Matrix.det !![a, b, 0; 0, c, d; e, 0, f] = -2 := by
  -- The determinant is the sum of the two nonzero cycle monomials.
  have hacf : a * c * f = 1 ∨ a * c * f = -1 :=
    mul_three_eq_one_or_neg_one_of_sign_values ha hc hf
  have hbde : b * d * e = 1 ∨ b * d * e = -1 :=
    mul_three_eq_one_or_neg_one_of_sign_values hb hd he
  have hfactor : (a * c * f) * (b * d * e) = 1 := by
    calc
      (a * c * f) * (b * d * e) = a * b * c * d * e * f := by ring
      _ = 1 := hprod
  rcases hacf with hacf | hacf
  · have hbde' : b * d * e = 1 := by
      rcases hbde with hbde | hbde
      · exact hbde
      · exfalso
        nlinarith [hfactor, hacf, hbde]
    left
    rw [Matrix.det_fin_three]
    simp
    nlinarith [hacf, hbde']
  · have hbde' : b * d * e = -1 := by
      rcases hbde with hbde | hbde
      · exfalso
        nlinarith [hfactor, hacf, hbde]
      · exact hbde
    right
    rw [Matrix.det_fin_three]
    simp
    nlinarith [hacf, hbde']

/-- Helper for Exercise 4.7: the first dense `2 × 2` left minor is the expected sign matrix. -/
lemma exercise_4_7_left_dense_minor_rows01_cols02
    (ε : Matrix (Fin 3) (Fin 4) Bool) :
    (ε.signed exercise_4_7_left_matrix).submatrix ![0, 1] ![0, 2] =
      !![boolean_sign (ε 0 0), boolean_sign (ε 0 2);
        boolean_sign (ε 1 0), boolean_sign (ε 1 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.signed_apply, exercise_4_7_left_matrix, boolean_sign]

/-- Helper for Exercise 4.7: the second dense `2 × 2` left minor is the expected sign matrix. -/
lemma exercise_4_7_left_dense_minor_rows02_cols01
    (ε : Matrix (Fin 3) (Fin 4) Bool) :
    (ε.signed exercise_4_7_left_matrix).submatrix ![0, 2] ![0, 1] =
      !![boolean_sign (ε 0 0), boolean_sign (ε 0 1);
        boolean_sign (ε 2 0), boolean_sign (ε 2 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.signed_apply, exercise_4_7_left_matrix, boolean_sign]

/-- Helper for Exercise 4.7: the third dense `2 × 2` left minor is the expected sign matrix. -/
lemma exercise_4_7_left_dense_minor_rows12_cols03
    (ε : Matrix (Fin 3) (Fin 4) Bool) :
    (ε.signed exercise_4_7_left_matrix).submatrix ![1, 2] ![0, 3] =
      !![boolean_sign (ε 1 0), boolean_sign (ε 1 3);
        boolean_sign (ε 2 0), boolean_sign (ε 2 3)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.signed_apply, exercise_4_7_left_matrix, boolean_sign]

/-- Helper for Exercise 4.7: the cycle `3 × 3` left minor has the expected sparse sign pattern. -/
lemma exercise_4_7_left_cycle_minor_cols123
    (ε : Matrix (Fin 3) (Fin 4) Bool) :
    (ε.signed exercise_4_7_left_matrix).submatrix id ![1, 2, 3] =
      !![boolean_sign (ε 0 1), boolean_sign (ε 0 2), 0;
        0, boolean_sign (ε 1 2), boolean_sign (ε 1 3);
        boolean_sign (ε 2 1), 0, boolean_sign (ε 2 3)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.signed_apply, exercise_4_7_left_matrix, boolean_sign]

/-- Helper for Exercise 4.7: every signing of the left-hand matrix has a square minor with
determinant `2` or `-2`. -/
lemma exercise_4_7_left_signed_matrix_has_bad_minor (ε : Matrix (Fin 3) (Fin 4) Bool) :
    ∃ k : ℕ, ∃ row : Fin k → Fin 3, ∃ col : Fin k → Fin 4,
      Function.Injective row ∧ Function.Injective col ∧
        (((ε.signed exercise_4_7_left_matrix).submatrix row col).det = 2 ∨
          ((ε.signed exercise_4_7_left_matrix).submatrix row col).det = -2) := by
  let a := boolean_sign (ε 0 0)
  let b := boolean_sign (ε 0 1)
  let c := boolean_sign (ε 0 2)
  let d := boolean_sign (ε 1 0)
  let e := boolean_sign (ε 1 2)
  let f := boolean_sign (ε 1 3)
  let g := boolean_sign (ε 2 0)
  let h := boolean_sign (ε 2 1)
  let i := boolean_sign (ε 2 3)
  have ha : a = 1 ∨ a = -1 := by
    simpa [a] using boolean_sign_eq_one_or_neg_one (ε 0 0)
  have hb : b = 1 ∨ b = -1 := by
    simpa [b] using boolean_sign_eq_one_or_neg_one (ε 0 1)
  have hc : c = 1 ∨ c = -1 := by
    simpa [c] using boolean_sign_eq_one_or_neg_one (ε 0 2)
  have hd : d = 1 ∨ d = -1 := by
    simpa [d] using boolean_sign_eq_one_or_neg_one (ε 1 0)
  have he : e = 1 ∨ e = -1 := by
    simpa [e] using boolean_sign_eq_one_or_neg_one (ε 1 2)
  have hf : f = 1 ∨ f = -1 := by
    simpa [f] using boolean_sign_eq_one_or_neg_one (ε 1 3)
  have hg : g = 1 ∨ g = -1 := by
    simpa [g] using boolean_sign_eq_one_or_neg_one (ε 2 0)
  have hh : h = 1 ∨ h = -1 := by
    simpa [h] using boolean_sign_eq_one_or_neg_one (ε 2 1)
  have hi : i = 1 ∨ i = -1 := by
    simpa [i] using boolean_sign_eq_one_or_neg_one (ε 2 3)
  have ha_sq : a * a = 1 := by
    simpa [a] using boolean_sign_sq (ε 0 0)
  have hd_sq : d * d = 1 := by
    simpa [d] using boolean_sign_sq (ε 1 0)
  have hg_sq : g * g = 1 := by
    simpa [g] using boolean_sign_sq (ε 2 0)
  have hp₁ : a * c * d * e = 1 ∨ a * c * d * e = -1 := by
    exact mul_eq_one_or_neg_one_of_sign_values
      (mul_three_eq_one_or_neg_one_of_sign_values ha hc hd) he
  have hp₂ : a * b * g * h = 1 ∨ a * b * g * h = -1 := by
    exact mul_eq_one_or_neg_one_of_sign_values
      (mul_three_eq_one_or_neg_one_of_sign_values ha hb hg) hh
  have hp₃ : d * f * g * i = 1 ∨ d * f * g * i = -1 := by
    exact mul_eq_one_or_neg_one_of_sign_values
      (mul_three_eq_one_or_neg_one_of_sign_values hd hf hg) hi
  -- Check the three dense `2 × 2` minors first.
  rcases hp₁ with hp₁ | hp₁
  · rcases hp₂ with hp₂ | hp₂
    · rcases hp₃ with hp₃ | hp₃
      · -- If all three dense minors have positive entry-product, the cycle minor does.
        have hpair_product :
            (a * c * d * e) * (a * b * g * h) * (d * f * g * i) = 1 := by
          rw [hp₁, hp₂, hp₃]
          norm_num
        have hcycle_factor :
            (a * c * d * e) * (a * b * g * h) * (d * f * g * i) = b * c * e * f * h * i := by
          calc
            (a * c * d * e) * (a * b * g * h) * (d * f * g * i)
                = (a * a) * (d * d) * (g * g) * (b * c * e * f * h * i) := by ring
            _ = b * c * e * f * h * i := by simp [ha_sq, hd_sq, hg_sq]
        have hcycle_product : b * c * e * f * h * i = 1 := by
          rw [← hcycle_factor]
          exact hpair_product
        have hdet :=
          exercise_4_7_cycle_three_by_three_det_of_positive_entry_product
            hb hc he hf hh hi hcycle_product
        refine ⟨3, id, ![1, 2, 3], Function.injective_id, by decide, ?_⟩
        rw [exercise_4_7_left_cycle_minor_cols123 ε]
        simpa [b, c, e, f, h, i] using hdet
      · have hdet :=
          exercise_4_7_two_by_two_det_of_negative_entry_product hd hf hg hi hp₃
        refine ⟨2, ![1, 2], ![0, 3], by decide, by decide, ?_⟩
        rw [exercise_4_7_left_dense_minor_rows12_cols03 ε]
        simpa [d, f, g, i] using hdet
    · have hdet :=
        exercise_4_7_two_by_two_det_of_negative_entry_product ha hb hg hh hp₂
      refine ⟨2, ![0, 2], ![0, 1], by decide, by decide, ?_⟩
      rw [exercise_4_7_left_dense_minor_rows02_cols01 ε]
      simpa [a, b, g, h] using hdet
  · have hdet :=
      exercise_4_7_two_by_two_det_of_negative_entry_product ha hc hd he hp₁
    refine ⟨2, ![0, 1], ![0, 2], by decide, by decide, ?_⟩
    rw [exercise_4_7_left_dense_minor_rows01_cols02 ε]
    simpa [a, c, d, e] using hdet

/-- Helper for Exercise 4.7: `2` is not a sign value. -/
lemma two_not_mem_signType_range : (2 : ℤ) ∉ Set.range SignType.cast := by
  simp [SignType.range_eq, Set.mem_insert_iff]

/-- Helper for Exercise 4.7: `-2` is not a sign value. -/
lemma neg_two_not_mem_signType_range : (-2 : ℤ) ∉ Set.range SignType.cast := by
  simp [SignType.range_eq, Set.mem_insert_iff]

/-- Helper for Exercise 4.7: the determinant of the displayed signed `5 × 5` matrix is `-1`. -/
lemma exercise_4_7_right_signed_matrix_det :
    exercise_4_7_right_signed_matrix.det = (-1 : ℤ) := by
  native_decide

/-- Helper for Exercise 4.7: multiplying `-1` by a permutation sign still gives a sign value. -/
lemma permutation_sign_mul_neg_one_mem_sign_range (σ : Equiv.Perm (Fin 5)) :
    ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ)) ∈ Set.range SignType.cast := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · use SignType.neg
    simp [hσ]
  · use SignType.pos
    simp [hσ]

/-- Helper for Exercise 4.7: minors of sizes at most `3` in the signed right matrix have
determinant in `{0, 1, -1}`. -/
lemma exercise_4_7_right_signed_matrix_minor_sign_range_small_sizes
    (k : ℕ) (hk : k ≤ 3) (f : Fin k → Fin 5) (g : Fin k → Fin 5)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (exercise_4_7_right_signed_matrix.submatrix f g).det ∈ Set.range SignType.cast := by
  interval_cases k
  · -- The empty minor has determinant `1`.
    use 1
    simp
  · -- The remaining small sizes are finite enough for direct certification.
    have h₁ :
        ∀ f : Fin 1 → Fin 5, ∀ g : Fin 1 → Fin 5,
          Function.Injective f → Function.Injective g →
            (exercise_4_7_right_signed_matrix.submatrix f g).det ∈ Set.range SignType.cast := by
      native_decide
    exact h₁ f g hf hg
  · have h₂ :
        ∀ f : Fin 2 → Fin 5, ∀ g : Fin 2 → Fin 5,
          Function.Injective f → Function.Injective g →
            (exercise_4_7_right_signed_matrix.submatrix f g).det ∈ Set.range SignType.cast := by
      native_decide
    exact h₂ f g hf hg
  · have h₃ :
        ∀ f : Fin 3 → Fin 5, ∀ g : Fin 3 → Fin 5,
          Function.Injective f → Function.Injective g →
            (exercise_4_7_right_signed_matrix.submatrix f g).det ∈ Set.range SignType.cast := by
      native_decide
    exact h₃ f g hf hg

/-- Helper for Exercise 4.7: the `4 × 4` and `5 × 5` minors of the signed right matrix also have
determinant in `{0, 1, -1}`. -/
lemma exercise_4_7_right_signed_matrix_minor_sign_range_large_sizes
    (k : ℕ) (hk : k = 4 ∨ k = 5) (f : Fin k → Fin 5) (g : Fin k → Fin 5)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (exercise_4_7_right_signed_matrix.submatrix f g).det ∈ Set.range SignType.cast := by
  rcases hk with rfl | rfl
  · -- The `4 × 4` minors are still small enough for finite certification.
    have h₄ :
        ∀ f : Fin 4 → Fin 5, ∀ g : Fin 4 → Fin 5,
          Function.Injective f → Function.Injective g →
            (exercise_4_7_right_signed_matrix.submatrix f g).det ∈ Set.range SignType.cast := by
      native_decide
    exact h₄ f g hf hg
  · -- Reindex a full-size minor by the permutations induced by the injective row and column maps.
    let ef : Fin 5 ≃ Fin 5 := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
    let eg : Fin 5 ≃ Fin 5 := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg)
    let σ : Equiv.Perm (Fin 5) := eg.symm.trans ef
    have hdet :
        (exercise_4_7_right_signed_matrix.submatrix f g).det =
          (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) := by
      calc
        (exercise_4_7_right_signed_matrix.submatrix f g).det
            = (Equiv.Perm.sign σ : ℤ) * exercise_4_7_right_signed_matrix.det := by
              simpa [ef, eg, σ] using
                (Matrix.det_reindex ef.symm eg.symm exercise_4_7_right_signed_matrix)
        _ = (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) := by
              rw [exercise_4_7_right_signed_matrix_det]
    simpa [hdet] using permutation_sign_mul_neg_one_mem_sign_range σ

/-- The explicit signed matrix for Exercise 4.7 is totally unimodular. -/
theorem exercise_4_7_right_signed_matrix_is_totally_unimodular :
    exercise_4_7_right_signed_matrix.IsTotallyUnimodular := by
  intro k f g hf hg
  -- Injectivity bounds the size of a square minor by the ambient `5 × 5` matrix.
  have hk : k ≤ 5 := by
    simpa using Fintype.card_le_of_injective f hf
  -- Split by minor size and dispatch each finite case.
  interval_cases k
  · exact exercise_4_7_right_signed_matrix_minor_sign_range_small_sizes 0 (by decide) f g hf hg
  · exact exercise_4_7_right_signed_matrix_minor_sign_range_small_sizes 1 (by decide) f g hf hg
  · exact exercise_4_7_right_signed_matrix_minor_sign_range_small_sizes 2 (by decide) f g hf hg
  · exact exercise_4_7_right_signed_matrix_minor_sign_range_small_sizes 3 (by decide) f g hf hg
  · exact exercise_4_7_right_signed_matrix_minor_sign_range_large_sizes 4 (by simp) f g hf hg
  · exact exercise_4_7_right_signed_matrix_minor_sign_range_large_sizes 5 (by simp) f g hf hg

/-- Exercise 4.7 (1). The left-hand `3 × 4` matrix cannot be signed to be totally unimodular. -/
theorem exercise_4_7_left_matrix_has_no_totally_unimodular_signing :
    ¬ exercise_4_7_left_matrix.HasTotallyUnimodularSigning := by
  rw [Matrix.hasTotallyUnimodularSigning_iff]
  rintro ⟨ε, hε⟩
  -- Every signing of the left matrix has a square minor whose determinant is `±2`.
  rcases exercise_4_7_left_signed_matrix_has_bad_minor ε with
    ⟨k, row, col, hrow, hcol, hbad⟩
  have hminor :
      (((ε.signed exercise_4_7_left_matrix).submatrix row col).det ∈ Set.range SignType.cast) :=
    hε k row col hrow hcol
  rcases hbad with hbad | hbad
  · have htwo : (2 : ℤ) ∈ Set.range SignType.cast := by
      simpa [hbad] using hminor
    exact two_not_mem_signType_range htwo
  · have hneg_two : (-2 : ℤ) ∈ Set.range SignType.cast := by
      simpa [hbad] using hminor
    exact neg_two_not_mem_signType_range hneg_two

/-- Exercise 4.7 (2). The right-hand `5 × 5` matrix can be signed to be totally unimodular. -/
theorem exercise_4_7_right_matrix_has_totally_unimodular_signing :
    exercise_4_7_right_matrix.HasTotallyUnimodularSigning := by
  exact ⟨exercise_4_7_right_signed_matrix, exercise_4_7_right_signed_matrix_is_signing,
    exercise_4_7_right_signed_matrix_is_totally_unimodular⟩

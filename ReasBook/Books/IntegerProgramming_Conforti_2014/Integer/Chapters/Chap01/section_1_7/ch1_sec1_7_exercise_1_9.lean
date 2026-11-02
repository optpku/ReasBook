module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.Data.Rat.Lemmas
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9.Encoding

@[expose] public section

open scoped BigOperators Matrix

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
evaluating a polynomial
with natural coefficients is monotone. -/
private lemma polynomialNatEval_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  -- Addition preserves monotonicity, while each monomial is a nonnegative multiple of a power.
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      intro a b hab
      simpa only [Polynomial.eval_add] using Nat.add_le_add (hp hab) (hq hab)
  | monomial k c =>
      intro a b hab
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab k)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
the encoding of a square
rational matrix dominates its dimension. -/
private lemma rationalMatrixDimension_le_encodingSize {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    n ≤ rational_matrix_encoding_size A := by
  -- Keep one diagonal entry from each row; every rational entry costs at least one bit.
  rw [rational_matrix_encoding_size]
  calc
    n = ∑ _i : Fin n, 1 := by simp
    _ ≤ ∑ i : Fin n, EncodingSize.rational (A i i) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      simp only [EncodingSize.rational_eq]
      omega
    _ ≤ ∑ i : Fin n, EncodingSize.rationalVector (A i) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [EncodingSize.rationalVector_eq_sum]
      exact Finset.single_le_sum
        (f := fun k : Fin n ↦ EncodingSize.rational (A i k))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
adjoining a standard basis
right-hand side increases a square system's encoding by at most a factor of four. -/
private lemma standardBasisSystemEncodingSize_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (j : Fin n) :
    rational_linear_system_encoding_size A (Pi.single j (1 : ℚ)) ≤
      4 * rational_matrix_encoding_size A := by
  -- A standard basis vector has at most three encoding bits per coordinate.
  have hentry (i : Fin n) :
      EncodingSize.rational (((Pi.single j (1 : ℚ)) : Fin n → ℚ) i) ≤ 3 := by
    by_cases h : j = i
    · subst i
      norm_num [EncodingSize.rational_eq]
    · simp [h, EncodingSize.rational_eq]
  have hvector : EncodingSize.rationalVector (Pi.single j (1 : ℚ)) ≤ 3 * n := by
    rw [EncodingSize.rationalVector_eq_sum]
    calc
      ∑ i : Fin n,
          EncodingSize.rational (((Pi.single j (1 : ℚ)) : Fin n → ℚ) i) ≤
          ∑ _i : Fin n, 3 := by
        exact Finset.sum_le_sum fun i _ ↦ hentry i
      _ = 3 * n := by simp [Nat.mul_comm]
  -- The matrix encoding absorbs the dimension, so it also absorbs this vector cost.
  rw [rational_linear_system_encoding_size]
  have hdimension := rationalMatrixDimension_le_encodingSize A
  omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
matrix encoding can be summed
column by column. -/
private lemma rationalMatrixEncodingSize_eq_sum_cols {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) :
    rational_matrix_encoding_size A = ∑ j, EncodingSize.rationalVector (A.col j) := by
  -- Expand both encodings and commute the two finite sums.
  rw [rational_matrix_encoding_size]
  simp only [EncodingSize.rationalVector_eq_sum, Matrix.col_apply]
  exact Finset.sum_comm

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
each inverse column obeys the
uniform solution-size bound at four times the matrix encoding. -/
private lemma inverseColumnEncodingSize_le_scaledInput
    (p : Polynomial ℕ)
    (hp : ∀ n (A : Matrix (Fin n) (Fin n) ℚ) (b x : Fin n → ℚ),
      IsUnit A.det → A *ᵥ x = b →
        EncodingSize.rationalVector x ≤ p.eval (rational_linear_system_encoding_size A b))
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsUnit A.det) (j : Fin n) :
    EncodingSize.rationalVector ((A⁻¹).col j) ≤
      p.eval (4 * rational_matrix_encoding_size A) := by
  -- The `j`th inverse column is the solution with the `j`th standard basis vector as data.
  have hsolution : A *ᵥ (A⁻¹).col j = Pi.single j 1 := by
    calc
      A *ᵥ (A⁻¹).col j = A *ᵥ (A⁻¹ *ᵥ Pi.single j 1) := by
        rw [Matrix.mulVec_single_one]
      _ = (A * A⁻¹) *ᵥ Pi.single j 1 := by
        rw [Matrix.mulVec_mulVec]
      _ = Pi.single j 1 := by
        rw [A.mul_nonsing_inv hA, Matrix.one_mulVec]
  have hcolumn := hp n A (Pi.single j 1) ((A⁻¹).col j) hA hsolution
  -- Monotonicity transports Proposition 1.9 along the uniform input-size estimate.
  exact hcolumn.trans
    (polynomialNatEval_monotone p (standardBasisSystemEncodingSize_le A j))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
the binary size of a product is at most the sum of the sizes of its factors. -/
private lemma natSizeMul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  -- Compare the product with the product of the defining power-of-two bounds.
  refine Nat.size_le.2 ?_
  calc
    a * b < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ = 2 ^ (Nat.size a + Nat.size b) := by rw [pow_add]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
the size of a finite product is bounded by the sum of factor sizes, with one empty-product bit. -/
private lemma natSizeFinsetProd_le_sum_add_one
    {α : Type*} (s : Finset α) (f : α → ℕ) :
    Nat.size (∏ i ∈ s, f i) ≤ (∑ i ∈ s, Nat.size (f i)) + 1 := by
  -- The extra bit handles the empty product; nonempty products use the multiplicative estimate.
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      have hmul := natSizeMul_le (f a) (∏ i ∈ s, f i)
      omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
the common denominator of a rational matrix has size controlled by its entry encoding. -/
private lemma rationalMatrixDenominatorSize_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    Nat.size A.den ≤ rational_matrix_encoding_size A + 1 := by
  -- The matrix denominator divides the product of all positive entry denominators.
  classical
  have hDvd : A.den ∣ ∏ p : Fin n × Fin n, (A p.1 p.2).den := by
    unfold Matrix.den
    exact Finset.lcm_dvd fun p hp ↦
      Finset.dvd_prod_of_mem (fun q ↦ (A q.1 q.2).den) hp
  have hProdPos : 0 < ∏ p : Fin n × Fin n, (A p.1 p.2).den :=
    Finset.prod_pos fun p _ ↦ (A p.1 p.2).den_pos
  have hDenLe : A.den ≤ ∏ p : Fin n × Fin n, (A p.1 p.2).den :=
    Nat.le_of_dvd hProdPos hDvd
  have hDenTerms :
      (∑ p : Fin n × Fin n, Nat.size (A p.1 p.2).den) ≤
        rational_matrix_encoding_size A := by
    rw [rational_matrix_encoding_size]
    simp only [EncodingSize.rationalVector_eq_sum, EncodingSize.rational_eq]
    calc
      (∑ p : Fin n × Fin n, Nat.size (A p.1 p.2).den) =
          ∑ i : Fin n, ∑ j : Fin n, Nat.size (A i j).den := by
        rw [← Finset.sum_product' Finset.univ Finset.univ]
        simp
      _ ≤ ∑ i : Fin n, ∑ j : Fin n,
          (Nat.size (A i j).num.natAbs + Nat.size (A i j).den + 1) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        refine Finset.sum_le_sum ?_
        intro j hj
        omega
  calc
    Nat.size A.den ≤ Nat.size (∏ p : Fin n × Fin n, (A p.1 p.2).den) :=
      Nat.size_le_size hDenLe
    _ ≤ (∑ p : Fin n × Fin n, Nat.size (A p.1 p.2).den) + 1 :=
      natSizeFinsetProd_le_sum_add_one Finset.univ
        (fun p : Fin n × Fin n ↦ (A p.1 p.2).den)
    _ ≤ rational_matrix_encoding_size A + 1 := Nat.add_le_add_right hDenTerms 1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
each entry of the integral numerator matrix has size controlled by the rational matrix. -/
private lemma rationalMatrixNumeratorEntrySize_le
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    EncodingSize.integer (A.num i j) ≤ 2 * (rational_matrix_encoding_size A + 1) := by
  -- Express the entry as the reduced numerator times the denominator quotient.
  obtain ⟨c, hc⟩ := (A.den_dvd_iff.mp (dvd_refl A.den) i j)
  have hcoordinate : A.num i j = (c : ℤ) * (A i j).num := by
    apply Rat.intCast_injective
    have hdenCast : (A.den : ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
    calc
      ((A.num i j : ℤ) : ℚ) = (A.den : ℚ) * A i j := by
        simpa [mul_comm] using (div_eq_iff hdenCast).mp (A.num_div_den i j)
      _ = ((c : ℤ) * (A i j).num : ℤ) := by
        rw [hc, Nat.cast_mul, mul_comm ((A i j).den : ℚ) (c : ℚ), mul_assoc,
          Rat.den_mul_eq_num]
        norm_cast
  have hcLe : c ≤ A.den := by
    rw [hc]
    exact Nat.le_mul_of_pos_left c (A i j).den_pos
  have hcSize : Nat.size c ≤ rational_matrix_encoding_size A + 1 :=
    (Nat.size_le_size hcLe).trans (rationalMatrixDenominatorSize_le A)
  have hentry : EncodingSize.rational (A i j) ≤ rational_matrix_encoding_size A := by
    simp only [rational_matrix_encoding_size, EncodingSize.rationalVector_eq_sum]
    exact le_trans
      (Finset.single_le_sum (f := fun t : Fin n ↦ EncodingSize.rational (A i t))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))
      (Finset.single_le_sum
        (f := fun s : Fin n ↦ ∑ t : Fin n, EncodingSize.rational (A s t))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))
  have hproduct : Nat.size (c * (A i j).num.natAbs) ≤
      Nat.size c + Nat.size (A i j).num.natAbs := natSizeMul_le _ _
  -- Combine the quotient, numerator, and sign-bit contributions.
  simp only [EncodingSize.integer_eq, hcoordinate, Int.natAbs_mul, Int.natAbs_natCast]
  simp only [EncodingSize.rational_eq] at hentry
  omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
an entry-size bound gives a polynomial binary-size bound for an integer determinant. -/
private lemma integerMatrixDeterminantSize_le
    {n B : ℕ} (Z : Matrix (Fin n) (Fin n) ℤ)
    (hentry : ∀ i j, EncodingSize.integer (Z i j) ≤ B) :
    Nat.size Z.det.natAbs ≤ n * n + B * n + 1 := by
  -- Bound the determinant by the number of Leibniz terms times their common entry bound.
  have htwoPos : 0 < (2 : ℕ) := by omega
  have honeLtTwo : 1 < (2 : ℕ) := by omega
  have hentryAbs : ∀ i j, (Z i j).natAbs ≤ 2 ^ B := by
    intro i j
    have hsize : Nat.size (Z i j).natAbs ≤ B := by
      have hij := hentry i j
      simp only [EncodingSize.integer_eq] at hij
      omega
    exact (Nat.lt_size_self (Z i j).natAbs).le.trans
      (Nat.pow_le_pow_right htwoPos hsize)
  have hentryAbsInt : ∀ i j,
      (AbsoluteValue.abs (Z i j) : ℤ) ≤ ((2 ^ B : ℕ) : ℤ) := by
    intro i j
    change |Z i j| ≤ ((2 ^ B : ℕ) : ℤ)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hentryAbs i j
  have hdetInt := Matrix.det_le (A := Z)
    (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := ((2 ^ B : ℕ) : ℤ)) hentryAbsInt
  have hdet : Z.det.natAbs ≤ Nat.factorial n * (2 ^ B) ^ n := by
    have hdetCast : ((Z.det.natAbs : ℕ) : ℤ) ≤
        ((Nat.factorial n * (2 ^ B) ^ n : ℕ) : ℤ) := by
      simpa [Fintype.card_fin, nsmul_eq_mul, Int.natCast_natAbs] using hdetInt
    exact_mod_cast hdetCast
  have hdetBound : Z.det.natAbs ≤ 2 ^ (n * n + B * n) := by
    calc
      Z.det.natAbs ≤ Nat.factorial n * (2 ^ B) ^ n := hdet
      _ ≤ n ^ n * (2 ^ B) ^ n := Nat.mul_le_mul_right _ (Nat.factorial_le_pow n)
      _ ≤ (2 ^ n) ^ n * (2 ^ B) ^ n := by
        exact Nat.mul_le_mul_right _
          (Nat.pow_le_pow_left (show n ≤ 2 ^ n from Nat.lt_two_pow_self.le) n)
      _ = 2 ^ (n * n + B * n) := by rw [← pow_mul, ← pow_mul, ← pow_add]
  refine Nat.size_le.2 (hdetBound.trans_lt ?_)
  exact Nat.pow_lt_pow_right honeLtTwo (Nat.lt_succ_self _)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
a displayed quotient of integers bounds the encoding of the reduced rational it represents. -/
private lemma rationalEncodingSize_le_divInt
    (q : ℚ) (a b : ℤ) (hb : b ≠ 0) (hq : q = Rat.divInt a b) :
    EncodingSize.rational q ≤ Nat.size a.natAbs + Nat.size b.natAbs + 1 := by
  -- Reduction can only decrease the absolute numerator and positive denominator.
  by_cases ha : a = 0
  · subst a
    have hq0 : q = 0 := hq.trans ((Rat.divInt_eq_zero hb).mpr rfl)
    have hbAbsPos : 0 < b.natAbs := Int.natAbs_pos.mpr hb
    have hbSize : 1 ≤ Nat.size b.natAbs := Nat.size_pos.mpr hbAbsPos
    rw [hq0]
    norm_num [EncodingSize.rational_eq]
    omega
  · have hnumDvd : q.num ∣ a := by
      rw [hq]
      exact Rat.num_dvd a hb
    have hdenDvd : (q.den : ℤ) ∣ b := by
      rw [hq]
      exact Rat.den_dvd a b
    have hnum : Nat.size q.num.natAbs ≤ Nat.size a.natAbs :=
      Nat.size_le_size (Int.natAbs_le_of_dvd_ne_zero hnumDvd ha)
    have hdenAbs : q.den ≤ b.natAbs := by
      simpa using Int.natAbs_le_of_dvd_ne_zero hdenDvd hb
    have hden : Nat.size q.den ≤ Nat.size b.natAbs := Nat.size_le_size hdenAbs
    simp only [EncodingSize.rational_eq]
    omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
clearing a matrix's common denominator gives an integral Cramer representation of every inverse
entry. -/
private lemma rationalMatrixNumerator_inverseEntry
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsUnit A.det) (i j : Fin n) :
    A.num.det ≠ 0 ∧
      (A⁻¹) i j = Rat.divInt
        (A.num.updateCol i (Pi.single j (A.den : ℤ))).det A.num.det := by
  classical
  let C : Matrix (Fin n) (Fin n) ℚ := A.num.map (Int.castRingHom ℚ)
  let b : Fin n → ℚ := Pi.single j (A.den : ℚ)
  have hdenCast : (A.den : ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
  -- The integral numerator matrix is obtained by scaling every entry by `A.den`.
  have hscale : C = (A.den : ℚ) • A := by
    ext r c
    simp only [C, Matrix.map_apply]
    simpa [mul_comm] using (div_eq_iff hdenCast).mp (A.num_div_den r c)
  have hCunit : IsUnit C.det := by
    rw [hscale, Matrix.det_smul, Fintype.card_fin]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero n hdenCast) hA.ne_zero)
  have hdetCast : (A.num.det : ℚ) = C.det := by
    simpa only [C] using (Int.castRingHom ℚ).map_det A.num
  have hnumDet : A.num.det ≠ 0 := by
    intro hzero
    apply hCunit.ne_zero
    rw [← hdetCast, hzero]
    norm_num
  -- The inverse column solves the denominator-cleared system with scaled basis right-hand side.
  have hAcolumn : A *ᵥ (A⁻¹).col j = Pi.single j 1 := by
    calc
      A *ᵥ (A⁻¹).col j = A *ᵥ (A⁻¹ *ᵥ Pi.single j 1) := by
        rw [Matrix.mulVec_single_one]
      _ = (A * A⁻¹) *ᵥ Pi.single j 1 := by rw [Matrix.mulVec_mulVec]
      _ = Pi.single j 1 := by rw [A.mul_nonsing_inv hA, Matrix.one_mulVec]
  have hsolution : C *ᵥ (A⁻¹).col j = b := by
    calc
      C *ᵥ (A⁻¹).col j = (A.den : ℚ) • (A *ᵥ (A⁻¹).col j) := by
        rw [hscale, Matrix.smul_mulVec]
      _ = (A.den : ℚ) • Pi.single j 1 := congrArg _ hAcolumn
      _ = b := by
        ext r
        simp [b, Pi.single_apply]
  have hinverseSolution : C⁻¹ *ᵥ b = (A⁻¹).col j := by
    calc
      C⁻¹ *ᵥ b = C⁻¹ *ᵥ (C *ᵥ (A⁻¹).col j) :=
        congrArg (fun x ↦ C⁻¹ *ᵥ x) hsolution.symm
      _ = (C⁻¹ * C) *ᵥ (A⁻¹).col j := by rw [Matrix.mulVec_mulVec]
      _ = (A⁻¹).col j := by rw [C.nonsing_inv_mul hCunit, Matrix.one_mulVec]
  have hcramer := congrFun (C.det_smul_inv_mulVec_eq_cramer b hCunit) i
  rw [hinverseSolution] at hcramer
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply, Matrix.cramer_apply] at hcramer
  let Z : Matrix (Fin n) (Fin n) ℤ :=
    A.num.updateCol i (Pi.single j (A.den : ℤ))
  -- Cast the updated integer matrix once, keeping the determinant transport out of the final step.
  have hupdateCast : Z.map (Int.castRingHom ℚ) = C.updateCol i b := by
    ext r c
    simp [Z, C, b, Matrix.updateCol_apply, Pi.single_apply]
  have hupdatedDetCast : (Z.det : ℚ) = (C.updateCol i b).det := by
    calc
      (Z.det : ℚ) = (Z.map (Int.castRingHom ℚ)).det :=
        (Int.castRingHom ℚ).map_det Z
      _ = (C.updateCol i b).det := congrArg Matrix.det hupdateCast
  have hnumDetCast : (A.num.det : ℚ) ≠ 0 := by
    exact_mod_cast hnumDet
  have hquotient : (A⁻¹) i j = (Z.det : ℚ) / (A.num.det : ℚ) := by
    apply (eq_div_iff hnumDetCast).2
    calc
      (A⁻¹) i j * (A.num.det : ℚ) = C.det * (A⁻¹) i j := by
        rw [hdetCast, mul_comm]
      _ = (C.updateCol i b).det := hcramer
      _ = (Z.det : ℚ) := hupdatedDetCast.symm
  refine ⟨hnumDet, ?_⟩
  simpa only [Z, Rat.intCast_div_eq_divInt] using hquotient

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
replacing one numerator-matrix column by a scaled basis vector preserves the uniform entry-size
bound. -/
private lemma updatedNumeratorEntrySize_le
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j r c : Fin n) :
    EncodingSize.integer
        ((A.num.updateCol i (Pi.single j (A.den : ℤ))) r c) ≤
      2 * (rational_matrix_encoding_size A + 1) := by
  -- Off the selected column use the numerator bound; on it, only `0` or `A.den` occurs.
  rw [Matrix.updateCol_apply]
  split_ifs with hci
  · subst c
    simp only [Pi.single_apply]
    split_ifs with hrj
    · subst r
      have hden := rationalMatrixDenominatorSize_le A
      simp only [EncodingSize.integer_eq, Int.natAbs_natCast]
      omega
    · simp only [EncodingSize.integer_eq, Int.natAbs_zero, Nat.size_zero, zero_add]
      omega
  · exact rationalMatrixNumeratorEntrySize_le A r c

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
every entry of a nonsingular rational inverse has a uniform polynomial encoding bound. -/
private lemma inverseEntryEncodingSize_le
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsUnit A.det) (i j : Fin n) :
    EncodingSize.rational ((A⁻¹) i j) ≤
      2 * (n * n + 2 * (rational_matrix_encoding_size A + 1) * n + 1) + 1 := by
  let Z : Matrix (Fin n) (Fin n) ℤ :=
    A.num.updateCol i (Pi.single j (A.den : ℤ))
  obtain ⟨hden, hrepr⟩ := rationalMatrixNumerator_inverseEntry A hA i j
  have hnumSize : Nat.size Z.det.natAbs ≤
      n * n + 2 * (rational_matrix_encoding_size A + 1) * n + 1 := by
    apply integerMatrixDeterminantSize_le Z
    intro r c
    exact updatedNumeratorEntrySize_le A i j r c
  have hdenSize : Nat.size A.num.det.natAbs ≤
      n * n + 2 * (rational_matrix_encoding_size A + 1) * n + 1 := by
    apply integerMatrixDeterminantSize_le A.num
    intro r c
    exact rationalMatrixNumeratorEntrySize_le A r c
  -- Reduction of the Cramer quotient cannot increase either determinant's bit size.
  have hrepresentation : (A⁻¹) i j = Rat.divInt Z.det A.num.det := by
    simpa only [Z] using hrepr
  have hquotient := rationalEncodingSize_le_divInt ((A⁻¹) i j) Z.det A.num.det hden
    hrepresentation
  omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean:
a uniform entry bound controls the encoding size of an entire rational matrix. -/
private lemma rationalMatrixEncodingSize_le_of_entry
    {m n B : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (hentry : ∀ i j, EncodingSize.rational (A i j) ≤ B) :
    rational_matrix_encoding_size A ≤ m * (n * B) := by
  -- Sum the entrywise estimate first across each row and then across all rows.
  simp only [rational_matrix_encoding_size, EncodingSize.rationalVector_eq_sum]
  calc
    ∑ i : Fin m, ∑ j : Fin n, EncodingSize.rational (A i j) ≤
        ∑ _i : Fin m, ∑ _j : Fin n, B := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hentry i j
    _ = m * (n * B) := by simp

/-- remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9.lean
Exercise 1.9 (1): the encoding size of the inverse of a nonsingular rational square matrix is
bounded above by a polynomial in the encoding size of the original matrix. -/
theorem rational_matrix_inverse_encoding_size_is_polynomially_bounded :
    ∃ p : Polynomial ℕ, ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℚ,
      IsUnit A.det →
        rational_matrix_encoding_size A⁻¹ ≤ p.eval (rational_matrix_encoding_size A) := by
  -- Route correction: avoid the placeholder-dependent system theorem via integral Cramer bounds.
  -- Use a polynomial large enough for two determinant encodings at each of the `n²` entries.
  refine ⟨Polynomial.X *
    (Polynomial.X *
      (2 * (Polynomial.X * Polynomial.X +
        2 * (Polynomial.X + 1) * Polynomial.X + 1) + 1)), ?_⟩
  intro n A hA
  let L := rational_matrix_encoding_size A
  let entryBound := 2 * (n * n + 2 * (L + 1) * n + 1) + 1
  let uniformBound := 2 * (L * L + 2 * (L + 1) * L + 1) + 1
  have hdimension : n ≤ L := rationalMatrixDimension_le_encodingSize A
  have hentryMonotone : entryBound ≤ uniformBound := by
    dsimp only [entryBound, uniformBound]
    have hinside : n * n + 2 * (L + 1) * n + 1 ≤
        L * L + 2 * (L + 1) * L + 1 := by
      gcongr
    omega
  -- Sum the uniform Cramer bound first over columns and then over rows.
  have hsum : rational_matrix_encoding_size A⁻¹ ≤ n * (n * entryBound) :=
    rationalMatrixEncodingSize_le_of_entry A⁻¹ fun i j ↦
      inverseEntryEncodingSize_le A hA i j
  have htotal : n * (n * entryBound) ≤ L * (L * uniformBound) :=
    Nat.mul_le_mul hdimension (Nat.mul_le_mul hdimension hentryMonotone)
  -- Evaluate the displayed polynomial after replacing both occurrences of `n` by `L`.
  simpa only [L, uniformBound, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_one] using hsum.trans htotal

#print axioms rational_matrix_inverse_encoding_size_is_polynomially_bounded

end

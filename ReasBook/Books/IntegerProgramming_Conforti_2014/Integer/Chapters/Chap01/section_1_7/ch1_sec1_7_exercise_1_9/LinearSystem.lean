/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9.Encoding

@[expose] public section

open scoped BigOperators Matrix

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
every linear functional on a finite coordinate space is a dot product. -/
private lemma existsDotProductRepresentation
    {ι R : Type*} [Fintype ι] [CommSemiring R]
    (f : (ι → R) →ₗ[R] R) :
    ∃ u : ι → R, ∀ x : ι → R, u ⬝ᵥ x = f x := by
  classical
  -- Read off the functional on the standard coordinate vectors.
  refine ⟨fun i ↦ f (fun j ↦ if i = j then 1 else 0), ?_⟩
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [dotProduct, smul_eq_mul, mul_comm]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
membership in the range of `A.mulVecLin` is solvability of the matrix equation. -/
private lemma memRangeMulVecLin_iff
    {m n R : Type*} [Fintype n] [CommSemiring R]
    (A : Matrix m n R) (b : m → R) :
    b ∈ LinearMap.range A.mulVecLin ↔ ∃ x : n → R, A *ᵥ x = b := by
  constructor
  · rintro ⟨x, hx⟩
    have hmul : A *ᵥ x = b := by
      simpa only [Matrix.mulVecLin_apply] using hx
    exact ⟨x, hmul⟩
  · rintro ⟨x, hx⟩
    have hmul : A.mulVecLin x = b := by
      simpa only [Matrix.mulVecLin_apply] using hx
    exact ⟨x, hmul⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
real feasibility of a rational matrix equation already implies rational feasibility. -/
private lemma existsRationalSolutionOfRealSolution
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hreal : ∃ xbar : Fin n → ℝ,
      (A.map (Rat.castHom ℝ)).mulVec xbar = fun i ↦ (b i : ℝ)) :
    ∃ x : Fin n → ℚ, A.mulVec x = b := by
  classical
  -- A separating rational functional would cast to a separating real functional.
  by_contra hrat
  have hbNotMem : b ∉ LinearMap.range A.mulVecLin := by
    intro hb
    exact hrat ((memRangeMulVecLin_iff A b).mp hb)
  obtain ⟨f, hfb, hRangeKer⟩ := Submodule.exists_le_ker_of_notMem hbNotMem
  obtain ⟨u, hu⟩ := existsDotProductRepresentation f
  have huA : u ᵥ* A = 0 := by
    apply dotProduct_eq_zero
    intro x
    rw [← Matrix.dotProduct_mulVec, hu]
    apply LinearMap.mem_ker.mp
    apply hRangeKer
    exact ⟨x, rfl⟩
  obtain ⟨xbar, hxbar⟩ := hreal
  apply hfb
  rw [← hu b]
  have hcast : ((u ⬝ᵥ b : ℚ) : ℝ) = 0 := by
    calc
    ((u ⬝ᵥ b : ℚ) : ℝ) =
        (fun i ↦ (u i : ℝ)) ⬝ᵥ (fun i ↦ (b i : ℝ)) := by
          simpa only [Function.comp_apply] using
            RingHom.map_dotProduct (Rat.castHom ℝ) u b
    _ = (fun i ↦ (u i : ℝ)) ⬝ᵥ ((A.map (Rat.castHom ℝ)).mulVec xbar) :=
      congrArg (fun y ↦ (fun i ↦ (u i : ℝ)) ⬝ᵥ y) hxbar.symm
    _ = ((fun i ↦ (u i : ℝ)) ᵥ* (A.map (Rat.castHom ℝ))) ⬝ᵥ xbar :=
      Matrix.dotProduct_mulVec _ _ _
    _ = 0 := by
      have huACast :
          (fun i ↦ (u i : ℝ)) ᵥ* (A.map (Rat.castHom ℝ)) = 0 := by
        ext j
        calc
          ((fun i ↦ (u i : ℝ)) ᵥ* (A.map (Rat.castHom ℝ))) j =
              (((u ᵥ* A) j : ℚ) : ℝ) := by
            simpa only [Function.comp_apply] using
              (RingHom.map_vecMul (Rat.castHom ℝ) A u j).symm
          _ = 0 := by
            rw [congrFun huA j]
            norm_num
      rw [huACast, zero_dotProduct]
  have hcastZero : ((u ⬝ᵥ b : ℚ) : ℝ) = ((0 : ℚ) : ℝ) := by
    simpa using hcast
  exact Rat.cast_injective hcastZero

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
zero-extending selected coordinates turns ambient multiplication into multiplication by the
selected-column submatrix. -/
private lemma mulVec_extend_eq_submatrix_mulVec
    {μ ν κ R : Type*} [Fintype ν] [Fintype κ] [CommSemiring R]
    (M : Matrix μ ν R) (cols : κ ↪ ν) (y : κ → R) :
    M *ᵥ Function.extend cols y 0 = (M.submatrix id cols) *ᵥ y := by
  classical
  -- Terms outside the selected image vanish, after which the embedding reindexes the sum.
  ext i
  simp only [Matrix.mulVec, Matrix.submatrix_apply, id_eq]
  calc
    (∑ j : ν, M i j * Function.extend cols y 0 j) =
        ∑ j ∈ Finset.univ.image cols, M i j * Function.extend cols y 0 j := by
      symm
      apply Finset.sum_subset
      · simp
      · intro j _ hjOutside
        rw [Function.extend_def, dif_neg]
        · simp
        · simpa only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] using hjOutside
    _ = ∑ j : κ, M i (cols j) * Function.extend cols y 0 (cols j) := by
      rw [Finset.sum_image]
      exact Set.injOn_of_injective cols.injective
    _ = ∑ j : κ, M i (cols j) * y j := by
      simp only [cols.injective.extend_apply]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
a full-row-rank finite matrix contains an invertible square column submatrix. -/
private lemma existsInvertibleColumnSubmatrix
    {r : ℕ} {c K : Type*} [Finite c] [Field K]
    (N : Matrix (Fin r) c K) (hrows : LinearIndependent K N.row) :
    ∃ cols : Fin r ↪ c, IsUnit (N.submatrix id cols).det := by
  classical
  -- Local instance justification (finite coordinates): matrix rank needs an enumeration of `c`.
  letI : Fintype c := Fintype.ofFinite c
  -- Select a basis from the column span, whose dimension is the full row rank `r`.
  let colSpace : Submodule K (Fin r → K) := Submodule.span K (Set.range N.col)
  have hrank : N.rank = r := by simpa using hrows.rank_matrix
  have hcolFinrank : Module.finrank K colSpace = r := by
    calc
      Module.finrank K colSpace = N.rank := by
        simpa [colSpace] using (Matrix.rank_eq_finrank_span_cols (A := N)).symm
      _ = r := hrank
  have hcard : Fintype.card (Fin (Module.finrank K colSpace)) = Fintype.card (Fin r) := by
    simp [hcolFinrank]
  obtain ⟨basisCols, hbasisMem, -, hbasisLinear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range N.col)
  let reindex : Fin (Module.finrank K colSpace) ≃ Fin r :=
    Fintype.equivOfCardEq hcard
  let picked : Fin r → c := fun i ↦ Classical.choose (hbasisMem (reindex.symm i))
  have hpicked : ∀ i : Fin r, N.col (picked i) = basisCols (reindex.symm i) := by
    intro i
    exact Classical.choose_spec (hbasisMem (reindex.symm i))
  have hpickedLinear : LinearIndependent K (fun i : Fin r ↦ N.col (picked i)) := by
    have hreindexed : LinearIndependent K (fun i : Fin r ↦ basisCols (reindex.symm i)) :=
      (linearIndependent_equiv reindex.symm).2 hbasisLinear
    convert hreindexed using 1
    exact funext hpicked
  have hpickedInjective : Function.Injective picked := by
    intro i j hij
    apply hpickedLinear.injective
    simp [hij]
  let cols : Fin r ↪ c := ⟨picked, hpickedInjective⟩
  have hunit : IsUnit (N.submatrix id cols) := by
    apply Matrix.linearIndependent_cols_iff_isUnit.mp
    simpa [cols, Matrix.col, Matrix.submatrix_apply] using hpickedLinear
  exact ⟨cols, (N.submatrix id cols).isUnit_iff_isUnit_det.mp hunit⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
a finite matrix with independent columns contains an invertible square row submatrix. -/
private lemma existsInvertibleRowSubmatrix
    {m r : ℕ} {K : Type*} [Field K]
    (C : Matrix (Fin m) (Fin r) K) (hcols : LinearIndependent K C.col) :
    ∃ rows : Fin r ↪ Fin m, IsUnit (C.submatrix rows id).det := by
  classical
  -- Apply the preceding column-minor result to the transpose.
  have hrowsTranspose : LinearIndependent K C.transpose.row := by
    simpa [Matrix.row, Matrix.col] using hcols
  obtain ⟨rows, hrows⟩ := existsInvertibleColumnSubmatrix C.transpose hrowsTranspose
  refine ⟨rows, ?_⟩
  have htranspose : (C.transpose.submatrix id rows)ᵀ = C.submatrix rows id := by
    ext i j
    rfl
  rw [← htranspose, Matrix.det_transpose]
  exact hrows

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
a real-feasible rational system has a basic rational solution supported on independent columns. -/
private lemma existsRationalBasicSolution
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hreal : ∃ xbar : Fin n → ℝ,
      (A.map (Rat.castHom ℝ)).mulVec xbar = fun i ↦ (b i : ℝ)) :
    ∃ r : ℕ, ∃ rows : Fin r ↪ Fin m, ∃ cols : Fin r ↪ Fin n,
      IsUnit (A.submatrix rows cols).det ∧
        A.mulVec (Function.extend cols
          ((A.submatrix rows cols)⁻¹.mulVec (b ∘ rows)) 0) = b := by
  classical
  -- Work entirely over `ℚ` after descending the given real feasibility certificate.
  obtain ⟨x₀, hx₀⟩ := existsRationalSolutionOfRealSolution A b hreal
  let colSpace : Submodule ℚ (Fin m → ℚ) := Submodule.span ℚ (Set.range A.col)
  let r := Module.finrank ℚ colSpace
  obtain ⟨basisCols, hbasisMem, hbasisSpan, hbasisLinear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range A.col)
  let picked : Fin r → Fin n := fun i ↦ Classical.choose (hbasisMem i)
  have hpicked : ∀ i : Fin r, A.col (picked i) = basisCols i := by
    intro i
    exact Classical.choose_spec (hbasisMem i)
  have hpickedLinear : LinearIndependent ℚ (fun i : Fin r ↦ A.col (picked i)) := by
    convert hbasisLinear using 1
    exact funext hpicked
  have hpickedInjective : Function.Injective picked := by
    intro i j hij
    apply hpickedLinear.injective
    simp [hij]
  let cols : Fin r ↪ Fin n := ⟨picked, hpickedInjective⟩
  let C : Matrix (Fin m) (Fin r) ℚ := A.submatrix id cols
  have hCcols : LinearIndependent ℚ C.col := by
    simpa [C, cols, Matrix.col, Matrix.submatrix_apply] using hpickedLinear
  have hCcolEq : C.col = basisCols := by
    funext i
    simpa [C, cols, Matrix.col, Matrix.submatrix_apply] using hpicked i
  have hbSpan : b ∈ Submodule.span ℚ (Set.range C.col) := by
    have hx₀Lin : A.mulVecLin x₀ = b := by
      simpa only [Matrix.mulVecLin_apply] using hx₀
    have hbRange : b ∈ LinearMap.range A.mulVecLin := ⟨x₀, hx₀Lin⟩
    have hbAspan : b ∈ Submodule.span ℚ (Set.range A.col) := by
      rwa [← Matrix.range_mulVecLin]
    have hspan : Submodule.span ℚ (Set.range C.col) =
        Submodule.span ℚ (Set.range A.col) := by
      rw [hCcolEq]
      exact hbasisSpan
    rwa [hspan]
  obtain ⟨y, hySum⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hbSpan
  have hCy : C.mulVec y = b := by
    -- The span representation is the usual column expansion of a matrix-vector product.
    rw [← hySum]
    ext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  obtain ⟨rows, hrows⟩ := existsInvertibleRowSubmatrix C hCcols
  let D : Matrix (Fin r) (Fin r) ℚ := A.submatrix rows cols
  have hD : IsUnit D.det := by simpa [D, C, Matrix.submatrix_submatrix] using hrows
  let z : Fin r → ℚ := D⁻¹.mulVec (b ∘ rows)
  have hDz : D.mulVec z = b ∘ rows := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, D.mul_nonsing_inv hD, Matrix.one_mulVec]
  have hDy : D.mulVec y = b ∘ rows := by
    funext i
    simpa [D, C, Matrix.mulVec, Matrix.submatrix_apply] using congrFun hCy (rows i)
  have hyz : y = z := by
    exact (Matrix.mulVec_injective_iff_isUnit.mpr
      (D.isUnit_iff_isUnit_det.mpr hD)) (hDy.trans hDz.symm)
  have hCz : C.mulVec z = b := by
    rw [← hyz]
    exact hCy
  refine ⟨r, rows, cols, hD, ?_⟩
  -- The zero-extension interface now lifts the selected solution to the ambient columns.
  rw [mulVec_extend_eq_submatrix_mulVec]
  simpa [C, D, z] using hCz

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
the binary size of a product is at most the sum of the sizes of its factors. -/
private lemma natSizeMul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  -- Compare the product with the product of the defining power-of-two bounds.
  refine Nat.size_le.2 ?_
  calc
    a * b < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ = 2 ^ (Nat.size a + Nat.size b) := by rw [pow_add]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
the size of a natural power grows at most linearly in its exponent. -/
private lemma natSizePow_le (a k : ℕ) : Nat.size (a ^ k) ≤ k * Nat.size a + 1 := by
  -- Induct on the exponent and use the product-size estimate at each successor.
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      calc
        Nat.size (a ^ k * a) ≤ Nat.size (a ^ k) + Nat.size a := natSizeMul_le _ _
        _ ≤ (k * Nat.size a + 1) + Nat.size a := Nat.add_le_add_right ih _
        _ = (k + 1) * Nat.size a + 1 := by
          simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
a displayed integral fraction bounds the encoding of the reduced rational it represents. -/
private lemma rationalEncodingSize_le_of_eq_divInt
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
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
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
      have hsum : Nat.size (f a) + Nat.size (∏ i ∈ s, f i) ≤
          Nat.size (f a) + ∑ i ∈ s, Nat.size (f i) + 1 := by
        omega
      exact (natSizeMul_le (f a) (∏ i ∈ s, f i)).trans hsum

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
the common denominator of a rational matrix has size at most its entry encoding plus one. -/
private lemma matrixDenSize_le {k : ℕ} (M : Matrix (Fin k) (Fin k) ℚ) :
    Nat.size M.den ≤ rational_matrix_encoding_size M + 1 := by
  -- The matrix lcm divides the product of all entry denominators.
  classical
  have hDvd : M.den ∣ ∏ p : Fin k × Fin k, (M p.1 p.2).den := by
    unfold Matrix.den
    exact Finset.lcm_dvd fun p hp ↦ Finset.dvd_prod_of_mem (fun q ↦ (M q.1 q.2).den) hp
  have hProdPos : 0 < ∏ p : Fin k × Fin k, (M p.1 p.2).den :=
    Finset.prod_pos fun p _ ↦ (M p.1 p.2).den_pos
  have hDenLe : M.den ≤ ∏ p : Fin k × Fin k, (M p.1 p.2).den :=
    Nat.le_of_dvd hProdPos hDvd
  have hDenTerms :
      (∑ p : Fin k × Fin k, Nat.size (M p.1 p.2).den) ≤
        rational_matrix_encoding_size M := by
    rw [rational_matrix_encoding_size]
    simp only [EncodingSize.rationalVector_eq_sum, EncodingSize.rational_eq]
    calc
      (∑ p : Fin k × Fin k, Nat.size (M p.1 p.2).den) =
          ∑ i : Fin k, ∑ j : Fin k, Nat.size (M i j).den := by
        rw [Fintype.sum_prod_type]
      _ ≤ ∑ i : Fin k, ∑ j : Fin k,
          (Nat.size (M i j).num.natAbs + Nat.size (M i j).den + 1) := by
        have hterm : ∀ i j, Nat.size (M i j).den ≤
            Nat.size (M i j).num.natAbs + Nat.size (M i j).den + 1 := by
          intro i j
          omega
        exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hterm i j
  calc
    Nat.size M.den ≤ Nat.size (∏ p : Fin k × Fin k, (M p.1 p.2).den) :=
      Nat.size_le_size hDenLe
    _ ≤ (∑ p : Fin k × Fin k, Nat.size (M p.1 p.2).den) + 1 :=
      natSizeFinsetProd_le_sum_add_one Finset.univ
        (fun p : Fin k × Fin k ↦ (M p.1 p.2).den)
    _ ≤ rational_matrix_encoding_size M + 1 := Nat.add_le_add_right hDenTerms 1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
each entry of the integral numerator matrix has encoding controlled by the whole rational matrix. -/
private lemma matrixNumEntryEncodingSize_le
    {k : ℕ} (M : Matrix (Fin k) (Fin k) ℚ) (i j : Fin k) :
    EncodingSize.integer (M.num i j) ≤ 2 * (rational_matrix_encoding_size M + 1) := by
  -- Express this numerator as the reduced numerator times the denominator quotient.
  obtain ⟨c, hc⟩ := (M.den_dvd_iff.mp (dvd_refl M.den) i j)
  have hcoordinate : M.num i j = (c : ℤ) * (M i j).num := by
    apply Rat.intCast_injective
    have hdenCast : (M.den : ℚ) ≠ 0 := by exact_mod_cast M.den_ne_zero
    calc
      ((M.num i j : ℤ) : ℚ) = (M.den : ℚ) * M i j := by
        simpa [mul_comm] using (div_eq_iff hdenCast).mp (M.num_div_den i j)
      _ = ((c : ℤ) * (M i j).num : ℤ) := by
        rw [hc, Nat.cast_mul, mul_comm ((M i j).den : ℚ) (c : ℚ), mul_assoc,
          Rat.den_mul_eq_num]
        norm_cast
  have hcLe : c ≤ M.den := by
    rw [hc]
    exact Nat.le_mul_of_pos_left c (M i j).den_pos
  have hcSize : Nat.size c ≤ rational_matrix_encoding_size M + 1 :=
    (Nat.size_le_size hcLe).trans (matrixDenSize_le M)
  have hentry : EncodingSize.rational (M i j) ≤ rational_matrix_encoding_size M := by
    simp only [rational_matrix_encoding_size, EncodingSize.rationalVector_eq_sum]
    exact le_trans
      (Finset.single_le_sum (f := fun t : Fin k ↦ EncodingSize.rational (M i t))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))
      (Finset.single_le_sum
        (f := fun s : Fin k ↦ ∑ t : Fin k, EncodingSize.rational (M s t))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))
  have hproduct : Nat.size (c * (M i j).num.natAbs) ≤
      Nat.size c + Nat.size (M i j).num.natAbs := natSizeMul_le _ _
  -- Expand the integer encoding and combine the common-denominator and local-numerator budgets.
  simp only [EncodingSize.integer_eq, hcoordinate, Int.natAbs_mul, Int.natAbs_natCast]
  simp only [EncodingSize.rational_eq] at hentry
  omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
the determinant of an integer matrix has polynomial binary size in an entry-size bound. -/
private lemma integerDetSize_le
    {k B : ℕ} (Z : Matrix (Fin k) (Fin k) ℤ)
    (hentry : ∀ i j, EncodingSize.integer (Z i j) ≤ B) :
    Nat.size Z.det.natAbs ≤ k * k + B * k + 1 := by
  -- Bound all entries by `2^B`, apply the Leibniz determinant estimate, then take binary size.
  have hentryAbs : ∀ i j, (Z i j).natAbs ≤ 2 ^ B := by
    intro i j
    have hsize : Nat.size (Z i j).natAbs ≤ B := by
      have hij := hentry i j
      simp only [EncodingSize.integer_eq] at hij
      omega
    have htwoPositive : 0 < 2 := by omega
    exact (Nat.lt_size_self (Z i j).natAbs).le.trans
      (Nat.pow_le_pow_right htwoPositive hsize)
  have hentryAbsInt : ∀ i j,
      (AbsoluteValue.abs (Z i j) : ℤ) ≤ ((2 ^ B : ℕ) : ℤ) := by
    intro i j
    change |Z i j| ≤ ((2 ^ B : ℕ) : ℤ)
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hentryAbs i j
  have hdetInt := Matrix.det_le (A := Z)
    (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ))
    (x := ((2 ^ B : ℕ) : ℤ)) hentryAbsInt
  have hdet : Z.det.natAbs ≤ Nat.factorial k * (2 ^ B) ^ k := by
    have hdetCast : ((Z.det.natAbs : ℕ) : ℤ) ≤
        ((Nat.factorial k * (2 ^ B) ^ k : ℕ) : ℤ) := by
      simpa [Fintype.card_fin, nsmul_eq_mul, Int.natCast_natAbs] using hdetInt
    exact_mod_cast hdetCast
  have hdetBound : Z.det.natAbs ≤ 2 ^ (k * k + B * k) := by
    calc
      Z.det.natAbs ≤ Nat.factorial k * (2 ^ B) ^ k := hdet
      _ ≤ k ^ k * (2 ^ B) ^ k := Nat.mul_le_mul_right _ (Nat.factorial_le_pow k)
      _ ≤ (2 ^ k) ^ k * (2 ^ B) ^ k := by
        exact Nat.mul_le_mul_right _
          (Nat.pow_le_pow_left (show k ≤ 2 ^ k from Nat.lt_two_pow_self.le) k)
      _ = 2 ^ (k * k + B * k) := by rw [← pow_mul, ← pow_mul, ← pow_add]
  refine Nat.size_le.2 (hdetBound.trans_lt ?_)
  have htwoAtLeastTwo : 1 < 2 := by omega
  exact Nat.pow_lt_pow_right htwoAtLeastTwo (Nat.lt_succ_self _)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
the determinant of a rational matrix is represented by its integral numerator determinant over a
power of the common denominator. -/
private lemma rationalDet_eq_divInt {k : ℕ} (M : Matrix (Fin k) (Fin k) ℚ) :
    M.det = Rat.divInt M.num.det ((M.den ^ k : ℕ) : ℤ) := by
  -- Take determinants in the canonical `M = M.den⁻¹ • M.num` identity.
  calc
    M.det = ((M.den⁻¹ : ℚ) • M.num.map (Int.castRingHom ℚ)).det :=
      congrArg Matrix.det M.inv_denom_smul_num.symm
    _ = (M.den⁻¹ : ℚ) ^ k * (M.num.map (Int.castRingHom ℚ)).det := by
      rw [Matrix.det_smul, Fintype.card_fin]
    _ = (M.den⁻¹ : ℚ) ^ k * (M.num.det : ℚ) := by
      congr 1
      exact ((Int.castRingHom ℚ).map_det M.num).symm
    _ = (M.num.det : ℚ) / (M.den ^ k : ℕ) := by
      rw [Nat.cast_pow]
      simp only [div_eq_mul_inv, inv_pow]
      rw [mul_comm]
    _ = Rat.divInt M.num.det ((M.den ^ k : ℕ) : ℤ) := by
      rw [Rat.divInt_eq_div]
      norm_cast

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
the encoding size of a rational determinant is polynomial in its dimension and matrix encoding. -/
private lemma rationalDetEncodingSize_le {k : ℕ} (M : Matrix (Fin k) (Fin k) ℚ) :
    EncodingSize.rational M.det ≤
      k * k + 3 * (rational_matrix_encoding_size M + 1) * k + 3 := by
  -- Bound the displayed integral numerator and denominator in the preceding representation.
  let L := rational_matrix_encoding_size M
  have hnum : Nat.size M.num.det.natAbs ≤ k * k + 2 * (L + 1) * k + 1 := by
    apply integerDetSize_le M.num
    intro i j
    exact matrixNumEntryEncodingSize_le M i j
  have hden : Nat.size (M.den ^ k) ≤ k * (L + 1) + 1 := by
    exact (natSizePow_le M.den k).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left k (matrixDenSize_le M)) 1)
  have hdenNonzero : ((M.den ^ k : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast pow_ne_zero k M.den_ne_zero
  have hrepr := rationalEncodingSize_le_of_eq_divInt M.det M.num.det
    ((M.den ^ k : ℕ) : ℤ) hdenNonzero (rationalDet_eq_divInt M)
  simp only [Int.natAbs_natCast] at hrepr
  calc
    EncodingSize.rational M.det ≤
        Nat.size M.num.det.natAbs + Nat.size (M.den ^ k) + 1 := hrepr
    _ ≤ (k * k + 2 * (L + 1) * k + 1) + (k * (L + 1) + 1) + 1 := by omega
    _ = k * k + 3 * (L + 1) * k + 3 := by ring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
division of nonzero rationals increases encoding size by at most a fixed linear factor. -/
private lemma rationalDivEncodingSize_le (a b : ℚ) (hb : b ≠ 0) :
    EncodingSize.rational (a / b) ≤
      2 * (EncodingSize.rational a + EncodingSize.rational b) := by
  -- Display the quotient using the reduced numerators and denominators of its two operands.
  have hbNum : b.num ≠ 0 := Rat.num_ne_zero.mpr hb
  have haDen : (a.den : ℤ) ≠ 0 := by
    exact_mod_cast a.den_ne_zero
  have hdenNonzero : (a.den : ℤ) * b.num ≠ 0 := mul_ne_zero haDen hbNum
  have hquotient :
      a / b = Rat.divInt (a.num * (b.den : ℤ)) ((a.den : ℤ) * b.num) := by
    calc
      a / b = Rat.divInt a.num a.den / Rat.divInt b.num b.den := by
        rw [Rat.num_divInt_den, Rat.num_divInt_den]
      _ = Rat.divInt (a.num * (b.den : ℤ)) ((a.den : ℤ) * b.num) :=
        Rat.divInt_div_divInt _ _ _ _
  have hrepr := rationalEncodingSize_le_of_eq_divInt (a / b)
    (a.num * (b.den : ℤ)) ((a.den : ℤ) * b.num) hdenNonzero hquotient
  have hnumProduct : Nat.size (a.num.natAbs * b.den) ≤
      Nat.size a.num.natAbs + Nat.size b.den := natSizeMul_le _ _
  have hdenProduct : Nat.size (a.den * b.num.natAbs) ≤
      Nat.size a.den + Nat.size b.num.natAbs := natSizeMul_le _ _
  calc
    EncodingSize.rational (a / b) ≤
        Nat.size (a.num.natAbs * b.den) +
          Nat.size (a.den * b.num.natAbs) + 1 := by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hrepr
    _ ≤ (Nat.size a.num.natAbs + Nat.size b.den) +
          (Nat.size a.den + Nat.size b.num.natAbs) + 1 := by omega
    _ ≤ 2 * (EncodingSize.rational a + EncodingSize.rational b) := by
      simp only [EncodingSize.rational_eq]
      omega

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
an individual matrix entry costs no more than the encoding of its whole linear system. -/
private lemma matrixEntryEncodingSize_le_system
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (i : Fin m) (j : Fin n) :
    EncodingSize.rational (A i j) ≤ rational_linear_system_encoding_size A b := by
  -- Keep the selected entry, then its row, then the matrix summand of the system encoding.
  simp only [rational_linear_system_encoding_size, rational_matrix_encoding_size,
    EncodingSize.rationalVector_eq_sum]
  exact (Finset.single_le_sum (f := fun t : Fin n ↦ EncodingSize.rational (A i t))
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)).trans
      ((Finset.single_le_sum
        (f := fun s : Fin m ↦ ∑ t : Fin n, EncodingSize.rational (A s t))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_add_right _ _))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
an individual right-hand-side entry costs no more than the encoding of its whole linear system. -/
private lemma vectorEntryEncodingSize_le_system
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (i : Fin m) :
    EncodingSize.rational (b i) ≤ rational_linear_system_encoding_size A b := by
  -- Keep the selected term in the right-hand-side sum.
  rw [rational_linear_system_encoding_size, EncodingSize.rationalVector_eq_sum]
  exact (Finset.single_le_sum (f := fun s : Fin m ↦ EncodingSize.rational (b s))
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_add_left _ _)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
a square matrix whose entries have a common encoding bound has the corresponding quadratic total
encoding bound. -/
private lemma rationalMatrixEncodingSize_le_of_entry_le
    {k L : ℕ} (M : Matrix (Fin k) (Fin k) ℚ)
    (hentry : ∀ i j, EncodingSize.rational (M i j) ≤ L) :
    rational_matrix_encoding_size M ≤ k * k * L := by
  -- Sum the common entry bound over the `k²` matrix positions.
  rw [rational_matrix_encoding_size]
  simp only [EncodingSize.rationalVector_eq_sum]
  calc
    (∑ i : Fin k, ∑ j : Fin k, EncodingSize.rational (M i j)) ≤
        ∑ _i : Fin k, ∑ _j : Fin k, L := by
      exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hentry i j
    _ = k * k * L := by
      simp
      ring

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
the width of a nonempty-row rational system is bounded by its encoding size. -/
private lemma systemWidth_le_encodingSize
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (i : Fin m) :
    n ≤ rational_linear_system_encoding_size A b := by
  -- One row contains `n` entries, and every rational entry costs at least one bit.
  have hrow : n ≤ EncodingSize.rationalVector (A i) := by
    rw [EncodingSize.rationalVector_eq_sum]
    calc
      n = ∑ _j : Fin n, 1 := by simp
      _ ≤ ∑ j : Fin n, EncodingSize.rational (A i j) := by
        have hentry : ∀ j, 1 ≤ EncodingSize.rational (A i j) := by
          intro j
          simp only [EncodingSize.rational_eq]
          omega
        exact Finset.sum_le_sum fun j _ ↦ hentry j
  rw [rational_linear_system_encoding_size, rational_matrix_encoding_size]
  exact hrow.trans
    ((Finset.single_le_sum (f := fun s : Fin m ↦ EncodingSize.rationalVector (A s))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_add_right _ _))

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
the zero-extended solution obtained from an invertible selected minor has polynomial encoding
size. -/
private lemma rationalBasicSolutionEncodingSize_le
    {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (rows : Fin r ↪ Fin m) (cols : Fin r ↪ Fin n)
    (hunit : IsUnit (A.submatrix rows cols).det)
    (hn : n ≤ rational_linear_system_encoding_size A b) :
    EncodingSize.rationalVector
      (Function.extend cols
        ((A.submatrix rows cols)⁻¹.mulVec (b ∘ rows)) 0) ≤
      40 * (rational_linear_system_encoding_size A b + 1) ^ 5 := by
  classical
  -- Name the selected square system and the global input-size invariant.
  let L := rational_linear_system_encoding_size A b
  let D : Matrix (Fin r) (Fin r) ℚ := A.submatrix rows cols
  let c : Fin r → ℚ := b ∘ rows
  let z : Fin r → ℚ := D⁻¹.mulVec c
  have hrn : r ≤ n := by
    simpa using Fintype.card_le_of_injective cols cols.injective
  have hrL : r ≤ L := hrn.trans hn
  have hDentry : ∀ i j, EncodingSize.rational (D i j) ≤ L := by
    intro i j
    exact matrixEntryEncodingSize_le_system A b (rows i) (cols j)
  have hDencoding : rational_matrix_encoding_size D ≤ r * r * L :=
    rationalMatrixEncodingSize_le_of_entry_le D hDentry
  have hUpdateEntry (j i t : Fin r) :
      EncodingSize.rational ((D.updateCol j c) i t) ≤ L := by
    by_cases ht : t = j
    · subst t
      simpa [c] using vectorEntryEncodingSize_le_system A b (rows i)
    · rw [Matrix.updateCol_ne ht]
      exact hDentry i t
  have hUpdateEncoding (j : Fin r) :
      rational_matrix_encoding_size (D.updateCol j c) ≤ r * r * L :=
    rationalMatrixEncodingSize_le_of_entry_le (D.updateCol j c) (hUpdateEntry j)
  have hdetBound (M : Matrix (Fin r) (Fin r) ℚ)
      (hM : rational_matrix_encoding_size M ≤ r * r * L) :
      EncodingSize.rational M.det ≤ 10 * (L + 1) ^ 4 := by
    calc
      EncodingSize.rational M.det ≤
          r * r + 3 * (rational_matrix_encoding_size M + 1) * r + 3 :=
        rationalDetEncodingSize_le M
      _ ≤ r * r + 3 * (r * r * L + 1) * r + 3 := by gcongr
      _ ≤ L * L + 3 * (L * L * L + 1) * L + 3 := by gcongr
      _ ≤ 10 * (L + 1) ^ 4 := by nlinarith
  have hdetD : EncodingSize.rational D.det ≤ 10 * (L + 1) ^ 4 :=
    hdetBound D hDencoding
  have hcoordinate (j : Fin r) :
      EncodingSize.rational (z j) ≤ 40 * (L + 1) ^ 4 := by
    have hdetNe : D.det ≠ 0 := hunit.ne_zero
    have hcramer := congrFun (D.det_smul_inv_mulVec_eq_cramer c hunit) j
    have hz : z j = (D.updateCol j c).det / D.det := by
      apply (eq_div_iff hdetNe).2
      simpa [z, Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hcramer
    rw [hz]
    calc
      EncodingSize.rational ((D.updateCol j c).det / D.det) ≤
          2 * (EncodingSize.rational (D.updateCol j c).det +
            EncodingSize.rational D.det) := rationalDivEncodingSize_le _ _ hdetNe
      _ ≤ 2 * (10 * (L + 1) ^ 4 + 10 * (L + 1) ^ 4) := by
        gcongr
        exact hdetBound (D.updateCol j c) (hUpdateEncoding j)
      _ = 40 * (L + 1) ^ 4 := by ring
  have hextended (t : Fin n) :
      EncodingSize.rational (Function.extend cols z 0 t) ≤ 40 * (L + 1) ^ 4 := by
    by_cases ht : t ∈ Set.range cols
    · obtain ⟨j, rfl⟩ := ht
      simpa only [cols.injective.extend_apply] using hcoordinate j
    · rw [Function.extend_def, dif_neg]
      · norm_num [EncodingSize.rational_eq]
        calc
          2 ≤ 40 := by omega
          _ = 40 * 1 := by omega
          _ ≤ 40 * (L + 1) ^ 4 :=
            Nat.mul_le_mul_left 40 (Nat.one_le_pow 4 (L + 1) (Nat.succ_pos L))
      · simpa only [Set.mem_range, not_exists] using ht
  -- Sum the coordinate bounds and absorb the ambient width using `n ≤ L`.
  rw [EncodingSize.rationalVector_eq_sum]
  calc
    (∑ t : Fin n, EncodingSize.rational
        (Function.extend cols ((A.submatrix rows cols)⁻¹.mulVec (b ∘ rows)) 0 t)) ≤
        ∑ _t : Fin n, 40 * (L + 1) ^ 4 := by
      refine Finset.sum_le_sum ?_
      intro t ht
      simpa [D, c, z] using hextended t
    _ = n * (40 * (L + 1) ^ 4) := by simp
    _ ≤ L * (40 * (L + 1) ^ 4) := Nat.mul_le_mul_right _ hn
    _ ≤ (L + 1) * (40 * (L + 1) ^ 4) :=
      Nat.mul_le_mul_right _ (Nat.le_succ L)
    _ = 40 * (L + 1) ^ 5 := by ring

-- The earlier statement-defect diagnosis concerned a split owner label.
-- Exercise 1.9 (2): if a rational linear system has a real solution, then it has a rational
-- solution whose encoding size is bounded above by a polynomial in the encoding size of the input
-- pair `(A, b)`, provided the zero-row case is also zero-dimensional.
/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean.
Exercise 1.9 (2): if a rational linear system has a real solution, then it has a rational solution
whose encoding size is bounded above by a polynomial in the encoding size of the input pair
`(A, b)`, provided the zero-row case is also zero-dimensional. -/
theorem rational_linear_system_has_small_rational_solution :
    ∃ p : Polynomial ℕ, ∀ m n : ℕ, ∀ A : Matrix (Fin m) (Fin n) ℚ,
      ∀ b : Fin m → ℚ,
      (n = 0 ∨ 0 < m) →
      (∃ xbar : Fin n → ℝ, (A.map (Rat.castHom ℝ)).mulVec xbar = fun i ↦ (b i : ℝ)) →
        ∃ x : Fin n → ℚ,
          A.mulVec x = b ∧
            EncodingSize.rationalVector x ≤
              p.eval (rational_linear_system_encoding_size A b) := by
    -- The explicit polynomial absorbs the selected minor, both Cramer determinants, and extension.
    refine ⟨Polynomial.C 40 * (Polynomial.X + 1) ^ 5, ?_⟩
    intro m n A b hdimension hreal
    have hnEncoding : n ≤ rational_linear_system_encoding_size A b := by
      rcases hdimension with hn | hm
      · subst n
        exact Nat.zero_le _
      · exact systemWidth_le_encodingSize A b ⟨0, hm⟩
    obtain ⟨r, rows, cols, hunit, hsolution⟩ :=
      existsRationalBasicSolution A b hreal
    let x : Fin n → ℚ := Function.extend cols
      ((A.submatrix rows cols)⁻¹.mulVec (b ∘ rows)) 0
    refine ⟨x, ?_, ?_⟩
    · exact hsolution
    · have hbound := rationalBasicSolutionEncodingSize_le A b rows cols hunit hnEncoding
      simpa only [x, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using hbound

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_9/LinearSystem.lean:
the square specialization needs no separate dimension hypothesis. -/
theorem square_rational_linear_system_has_small_rational_solution :
    ∃ p : Polynomial ℕ, ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℚ, ∀ b : Fin n → ℚ,
      (∃ xbar : Fin n → ℝ, (A.map (Rat.castHom ℝ)).mulVec xbar = fun i ↦ (b i : ℝ)) →
        ∃ x : Fin n → ℚ,
          A.mulVec x = b ∧
            EncodingSize.rationalVector x ≤
              p.eval (rational_linear_system_encoding_size A b) := by
  obtain ⟨p, hp⟩ := rational_linear_system_has_small_rational_solution
  refine ⟨p, ?_⟩
  intro n A b hA
  exact hp n n A b (Nat.eq_zero_or_pos n) hA

#print axioms rational_linear_system_has_small_rational_solution

end

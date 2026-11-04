/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_theorem_1_6
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_lemma_1_3.RowOperations

@[expose] public section

open scoped Matrix
open scoped IntegerVectorNotation

namespace Matrix

section Lemma13

variable {n : ℕ}

/-- Lemma 1.3 (1). For an integer square matrix, unimodularity is equivalent to the existence of
an integral two-sided inverse. -/
theorem isUnit_det_iff_exists_int_inverse (U : Matrix (Fin n) (Fin n) ℤ) :
    IsUnit U.det ↔ ∃ V : Matrix (Fin n) (Fin n) ℤ, U * V = 1 ∧ V * U = 1 := by
  constructor
  · intro hU
    -- The nonsingular inverse is integral because it is formed in the original coefficient ring.
    exact ⟨U⁻¹, U.mul_nonsing_inv hU, U.nonsing_inv_mul hU⟩
  · rintro ⟨V, hUV, _⟩
    -- A right inverse already forces the determinant to be a unit.
    exact Matrix.isUnit_det_of_right_inverse hUV

/-- Lemma 1.3 (2). If `V` is an integral two-sided inverse of `U`, then `U` is unimodular if and
only if `V` is unimodular. -/
theorem isUnit_det_iff_inverse_isUnit_det
    {U V : Matrix (Fin n) (Fin n) ℤ}
    (hUV : U * V = 1)
    (hVU : V * U = 1) :
    IsUnit U.det ↔ IsUnit V.det := by
  -- Each multiplication identity independently exhibits the other matrix as an inverse.
  constructor
  · intro _
    exact Matrix.isUnit_det_of_right_inverse hVU
  · intro _
    exact Matrix.isUnit_det_of_right_inverse hUV

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: an integer matrix sends
embedded integer vectors to embedded integer vectors. -/
private lemma integerMatrix_mulVec_mem_integerVectors
    (A : Matrix (Fin n) (Fin n) ℤ)
    {x : Fin n → ℝ}
    (hx : x ∈ ℤ^n) :
    A.map (Int.castRingHom ℝ) *ᵥ x ∈ ℤ^n := by
  rcases mem_integerVectors_iff.mp hx with ⟨z, rfl⟩
  -- Mapping commutes with matrix-vector multiplication, so the integral product is a witness.
  refine mem_integerVectors_iff.mpr ⟨A *ᵥ z, ?_⟩
  funext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) A z i).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: a real number whose every
real multiple is integral must vanish. -/
private lemma eq_zero_of_all_smul_mem_integerVectors
    (x : Fin n → ℝ)
    (hx : ∀ c : ℝ, c • x ∈ ℤ^n) :
    x = 0 := by
  ext i
  by_contra hxi
  have hhalf := (mem_integerVectors_iff_forall.mp (hx ((2 * x i)⁻¹))) i
  rcases hhalf with ⟨z, hz⟩
  have hcoordinate : ((2 * x i)⁻¹ • x) i = (1 / 2 : ℝ) := by
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hxi]
    exact div_self hxi
  rw [hcoordinate] at hz
  have htwice : (2 : ℝ) * (z : ℝ) = 1 := by
    linarith
  have htwiceInt : (2 : ℤ) * z = 1 := by
    exact_mod_cast htwice
  omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: reflection of the embedded
integer lattice by an integer matrix forces its determinant to be a unit. -/
private lemma isUnit_det_of_reflects_integerVectors
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hreflect : ∀ x : Fin n → ℝ,
      A.map (Int.castRingHom ℝ) *ᵥ x ∈ ℤ^n → x ∈ ℤ^n) :
    IsUnit A.det := by
  classical
  let AReal : Matrix (Fin n) (Fin n) ℝ := A.map (Int.castRingHom ℝ)
  have hinjective : Function.Injective AReal.mulVec := by
    -- Every scalar multiple of a kernel vector is integral; the preceding scalar lemma kills it.
    intro x y hxy
    have hker : AReal *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hzero : x - y = 0 := by
      apply eq_zero_of_all_smul_mem_integerVectors (x - y)
      intro c
      apply hreflect
      rw [Matrix.mulVec_smul, hker, smul_zero]
      refine mem_integerVectors_iff.mpr ⟨0, ?_⟩
      funext i
      simp
    exact sub_eq_zero.mp hzero
  have hAReal : IsUnit AReal := Matrix.mulVec_injective_iff_isUnit.mp hinjective
  have hsurjective : Function.Surjective AReal.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hAReal
  choose preimage hpreimage using fun j : Fin n ↦ hsurjective (Pi.single j 1)
  have hpreimageIntegral (j : Fin n) : preimage j ∈ ℤ^n := by
    apply hreflect
    rw [hpreimage]
    refine mem_integerVectors_iff.mpr ⟨(Pi.single j 1 : Fin n → ℤ), ?_⟩
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij]
  choose integralPreimage hintegralPreimage using fun j : Fin n ↦
    mem_integerVectors_iff.mp (hpreimageIntegral j)
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j ↦ integralPreimage j i
  have hright : A * B = 1 := by
    -- The chosen integral columns map to the standard basis columns over `ℝ`.
    ext i j
    have hcol := congrFun (hpreimage j) i
    rw [hintegralPreimage j] at hcol
    simp only [AReal, Matrix.mulVec, dotProduct, Matrix.map_apply, Function.comp_apply,
      Pi.single_apply] at hcol
    simp only [Matrix.mul_apply, B, one_apply]
    apply (Int.cast_injective (α := ℝ))
    simpa only [Int.coe_castRingHom, Int.cast_sum, Int.cast_mul, Int.cast_ite,
      Int.cast_one, Int.cast_zero] using hcol
  -- The integral right inverse gives the required determinant unit.
  exact Matrix.isUnit_det_of_right_inverse hright

/-- Lemma 1.3 (3). An integer square matrix is unimodular if and only if its real linear action
preserves membership in `ℤ^n`. -/
theorem isUnit_det_iff_mulVec_mem_integerVectors (U : Matrix (Fin n) (Fin n) ℤ) :
    IsUnit U.det ↔
      ∀ x : Fin n → ℝ, (U.map (Int.castRingHom ℝ)) *ᵥ x ∈ ℤ^n ↔ x ∈ ℤ^n := by
  constructor
  · intro hU x
    rcases (isUnit_det_iff_exists_int_inverse U).mp hU with ⟨V, hUV, hVU⟩
    constructor
    · intro hUx
      -- Apply the integral inverse action and cancel the mapped product.
      have hVx := integerMatrix_mulVec_mem_integerVectors V hUx
      have hmapVU :
          V.map (Int.castRingHom ℝ) * U.map (Int.castRingHom ℝ) = 1 := by
        rw [← Matrix.map_mul, hVU]
        simp
      simpa only [Matrix.mulVec_mulVec, hmapVU, Matrix.one_mulVec] using hVx
    · exact integerMatrix_mulVec_mem_integerVectors U
  · intro hreflect
    -- Only the reverse implication is needed to recover unimodularity.
    exact isUnit_det_of_reflects_integerVectors U (fun x hx ↦ (hreflect x).mp hx)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: one elementary row matrix is
reachable in a single step. -/
private lemma reachableByUnimodularRowOps_of_elementary
    {E : Matrix (Fin n) (Fin n) ℤ}
    (hE : IsElementaryUnimodularRowMatrix E) :
    reachableByUnimodularRowOps E := by
  -- A singleton operation list folds to the given elementary matrix.
  refine ⟨[E], ?_, ?_⟩
  · intro M hM
    simp only [List.mem_singleton] at hM
    subst M
    exact hE
  · simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: the custom row-addition matrix
is the standard transvection whenever its two row indices differ. -/
private lemma rowAddMatrix_eq_transvection
    (i j : Fin n) (c : ℤ) (hij : i ≠ j) :
    rowAddMatrix i j c = Matrix.transvection i j c := by
  -- Both matrices are the identity with the same off-diagonal entry.
  ext r k
  by_cases hri : r = i
  · subst r
    by_cases hki : k = i
    · subst k
      simp [rowAddMatrix, Matrix.transvection, hij.symm]
    · by_cases hkj : k = j
      · subst k
        simp [rowAddMatrix, Matrix.transvection, hij, hki]
      · simp [rowAddMatrix, Matrix.transvection, hki, hkj,
          Ne.symm hki, Ne.symm hkj]
  · by_cases hrk : r = k
    · subst k
      simp [rowAddMatrix, Matrix.transvection, hri, Ne.symm hri]
    · simp [rowAddMatrix, Matrix.transvection, hri, hrk, Ne.symm hri]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: a row sign change is its own
inverse. -/
private lemma rowNegMatrix_mul_self (i : Fin n) :
    rowNegMatrix i * rowNegMatrix i = 1 := by
  -- Only the common diagonal coordinate contributes to each matrix entry.
  ext r k
  by_cases hrk : r = k
  · subst k
    by_cases hri : r = i
    · subst r
      simp [rowNegMatrix, Matrix.mul_apply]
    · simp [rowNegMatrix, Matrix.mul_apply, hri]
  · simp [rowNegMatrix, Matrix.mul_apply, hrk]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: every elementary row matrix
has an elementary two-sided inverse. -/
private lemma elementaryUnimodularRowMatrix_hasInverse
    {E : Matrix (Fin n) (Fin n) ℤ}
    (hE : IsElementaryUnimodularRowMatrix E) :
    ∃ F : Matrix (Fin n) (Fin n) ℤ,
      IsElementaryUnimodularRowMatrix F ∧ E * F = 1 ∧ F * E = 1 := by
  rcases hE with ⟨i, j, hij, rfl⟩ | ⟨i, rfl⟩ | ⟨i, j, c, hij, rfl⟩
  · -- A row swap is an involution.
    refine ⟨rowSwapMatrix i j, Or.inl ⟨i, j, hij, rfl⟩, ?_, ?_⟩
    · exact Matrix.swap_mul_self i j
    · exact Matrix.swap_mul_self i j
  · -- A row sign change is also an involution.
    refine ⟨rowNegMatrix i, Or.inr (Or.inl ⟨i, rfl⟩), ?_, ?_⟩
    · exact rowNegMatrix_mul_self i
    · exact rowNegMatrix_mul_self i
  · -- Negating the transvection coefficient gives the inverse row addition.
    refine ⟨rowAddMatrix i j (-c), Or.inr (Or.inr ⟨i, j, -c, hij, rfl⟩), ?_, ?_⟩
    · rw [rowAddMatrix_eq_transvection i j c hij,
        rowAddMatrix_eq_transvection i j (-c) hij,
        Matrix.transvection_mul_transvection_same (i := i) (j := j) hij c (-c)]
      simp
    · rw [rowAddMatrix_eq_transvection i j (-c) hij,
        rowAddMatrix_eq_transvection i j c hij,
        Matrix.transvection_mul_transvection_same (i := i) (j := j) hij (-c) c]
      simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: folding left
multiplications from an arbitrary initial matrix appends that matrix on the right. -/
private lemma foldl_leftMul_eq_foldl_one_mul
    (ops : List (Matrix (Fin n) (Fin n) ℤ))
    (A : Matrix (Fin n) (Fin n) ℤ) :
    ops.foldl (fun X E ↦ E * X) A =
      ops.foldl (fun X E ↦ E * X) 1 * A := by
  induction ops generalizing A with
  | nil => simp
  | cons E ops ih =>
      simp only [List.foldl_cons]
      calc
        ops.foldl (fun X F ↦ F * X) (E * A) =
            ops.foldl (fun X F ↦ F * X) 1 * (E * A) := ih (E * A)
        _ = (ops.foldl (fun X F ↦ F * X) 1 * E) * A := by rw [mul_assoc]
        _ = ops.foldl (fun X F ↦ F * X) E * A := by
          exact congrArg (fun X ↦ X * A) (ih E).symm
        _ = ops.foldl (fun X F ↦ F * X) (E * 1) * A := by rw [mul_one]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: every reachable row-operation
product has a reachable two-sided inverse. -/
private lemma reachableByUnimodularRowOps_hasInverse
    {U : Matrix (Fin n) (Fin n) ℤ}
    (hU : reachableByUnimodularRowOps U) :
    ∃ V : Matrix (Fin n) (Fin n) ℤ,
      reachableByUnimodularRowOps V ∧ U * V = 1 ∧ V * U = 1 := by
  rcases hU with ⟨ops, hOps, rfl⟩
  induction ops with
  | nil =>
      -- The empty product is its own inverse.
      refine ⟨1, reachableByUnimodularRowOps_one, ?_, ?_⟩
      · simp
      · simp
  | cons E ops ih =>
      have hmemE : E ∈ E :: ops := List.mem_cons_self
      have hE : IsElementaryUnimodularRowMatrix E := hOps E hmemE
      have hTail : ∀ M ∈ ops, IsElementaryUnimodularRowMatrix M := by
        intro M hM
        exact hOps M (List.mem_cons_of_mem E hM)
      rcases ih hTail with ⟨V, hV, hTV, hVT⟩
      rcases elementaryUnimodularRowMatrix_hasInverse hE with ⟨F, hF, hEF, hFE⟩
      have hReachF := reachableByUnimodularRowOps_of_elementary hF
      refine ⟨F * V, reachableByUnimodularRowOps_mul hV hReachF, ?_, ?_⟩
      · -- The fold is the tail product followed by the first operation.
        rw [List.foldl_cons, mul_one, foldl_leftMul_eq_foldl_one_mul]
        calc
          (ops.foldl (fun X G ↦ G * X) 1 * E) * (F * V) =
              ops.foldl (fun X G ↦ G * X) 1 * (E * F) * V := by
                simp only [mul_assoc]
          _ = 1 := by rw [hEF, mul_one, hTV]
      · rw [List.foldl_cons, mul_one, foldl_leftMul_eq_foldl_one_mul]
        calc
          (F * V) * (ops.foldl (fun X G ↦ G * X) 1 * E) =
              F * (V * ops.foldl (fun X G ↦ G * X) 1) * E := by
                simp only [mul_assoc]
          _ = 1 := by rw [hVT, mul_one, hFE]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: reachability implies that the
determinant is a unit. -/
private lemma isUnit_det_of_reachableByUnimodularRowOps
    {U : Matrix (Fin n) (Fin n) ℤ}
    (hU : reachableByUnimodularRowOps U) :
    IsUnit U.det := by
  -- A reachable inverse supplies a right inverse, so no determinant calculation is needed.
  rcases reachableByUnimodularRowOps_hasInverse hU with ⟨V, _, hUV, _⟩
  exact Matrix.isUnit_det_of_right_inverse hUV

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: the transpose of one Euclidean
step is a swap followed by an integral row addition. -/
private lemma reachableByUnimodularRowOps_euclideanStepMatrix_transpose
    (a b : ℤ) :
    reachableByUnimodularRowOps (Int.euclideanStepMatrix a b)ᵀ := by
  have hzeroOne : (0 : Fin 2) ≠ 1 := by decide
  have honeZero : (1 : Fin 2) ≠ 0 := by decide
  have hswap : reachableByUnimodularRowOps
      (rowSwapMatrix (0 : Fin 2) (1 : Fin 2)) :=
    reachableByUnimodularRowOps_of_elementary
      (Or.inl ⟨0, 1, hzeroOne, rfl⟩)
  have hadd : reachableByUnimodularRowOps
      (rowAddMatrix (1 : Fin 2) (0 : Fin 2) (-Int.fdiv a b)) :=
    reachableByUnimodularRowOps_of_elementary
      (Or.inr (Or.inr ⟨1, 0, -Int.fdiv a b, honeZero, rfl⟩))
  have hfactor :
      (Int.euclideanStepMatrix a b)ᵀ =
        rowAddMatrix (1 : Fin 2) (0 : Fin 2) (-Int.fdiv a b) *
          rowSwapMatrix (0 : Fin 2) (1 : Fin 2) := by
    -- The explicit `2 × 2` product is exactly the symmetric Euclidean-step matrix.
    ext i j
    fin_cases i
    · fin_cases j
      · simp [Int.euclideanStepMatrix, rowAddMatrix, Matrix.swap, Matrix.mul_apply]
      · simp [Int.euclideanStepMatrix, rowAddMatrix, Matrix.swap, Matrix.mul_apply]
    · fin_cases j
      · simp [Int.euclideanStepMatrix, rowAddMatrix, Matrix.swap, Matrix.mul_apply]
      · simp [Int.euclideanStepMatrix, rowAddMatrix, Matrix.swap, Matrix.mul_apply]
  rw [hfactor]
  exact reachableByUnimodularRowOps_mul hswap hadd

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: a product has reachable
transpose when the transpose of each factor is reachable. -/
private lemma reachableByUnimodularRowOps_listProd_transpose
    (L : List (Matrix (Fin n) (Fin n) ℤ))
    (hL : ∀ M ∈ L, reachableByUnimodularRowOps Mᵀ) :
    reachableByUnimodularRowOps L.prodᵀ := by
  induction L with
  | nil =>
      simpa using (reachableByUnimodularRowOps_one (n := n))
  | cons E L ih =>
      have hmemE : E ∈ E :: L := List.mem_cons_self
      have hE : reachableByUnimodularRowOps Eᵀ := hL E hmemE
      have hTail : ∀ M ∈ L, reachableByUnimodularRowOps Mᵀ := by
        intro M hM
        exact hL M (List.mem_cons_of_mem E hM)
      rw [List.prod_cons, Matrix.transpose_mul]
      exact reachableByUnimodularRowOps_mul hE (ih hTail)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: a finite Euclidean product,
transposed to act on columns, is reachable by row operations. -/
private lemma reachableByUnimodularRowOps_euclideanStepProduct_transpose
    (k : ℕ)
    (ab : Fin (k + 1) → ℤ × ℤ) :
    reachableByUnimodularRowOps (Int.euclideanStepProduct k ab)ᵀ := by
  rw [Int.euclideanStepProduct_def]
  apply reachableByUnimodularRowOps_listProd_transpose
  intro M hM
  simp only [List.mem_ofFn] at hM
  rcases hM with ⟨i, rfl⟩
  exact reachableByUnimodularRowOps_euclideanStepMatrix_transpose
    (ab i.castSucc).1 (ab i.castSucc).2

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: two integer coordinates can be
reduced by reachable row operations to their nonnegative gcd and zero. -/
private lemma exists_reachable_pairReduction_to_gcd (a b : ℤ) :
    ∃ R : Matrix (Fin 2) (Fin 2) ℤ,
      reachableByUnimodularRowOps R ∧
        R *ᵥ (![a, b] : Fin 2 → ℤ) = ![(Int.gcd a b : ℤ), 0] := by
  by_cases hnot : a ≠ 0 ∨ b ≠ 0
  · rcases Int.exists_euclideanStepSequence_vecMul_eq_terminal_zero a b hnot with
      ⟨k, ab, hseq, haction⟩
    let P := Int.euclideanStepProduct k ab
    let t := (ab (Fin.last k)).1
    have hP : reachableByUnimodularRowOps Pᵀ :=
      reachableByUnimodularRowOps_euclideanStepProduct_transpose k ab
    have hcolumn : Pᵀ *ᵥ (![a, b] : Fin 2 → ℤ) = ![t, 0] := by
      -- Transposing converts the source row action into the required column action.
      simpa only [Matrix.mulVec_transpose, P, t] using haction
    have habs : Int.natAbs t = Int.gcd a b :=
      Int.euclideanStepSequence_terminal_natAbs_eq_gcd a b k ab hseq
    by_cases ht : 0 ≤ t
    · refine ⟨Pᵀ, hP, ?_⟩
      have htGcd : t = (Int.gcd a b : ℤ) := by
        calc
          t = (Int.natAbs t : ℤ) := (Int.natAbs_of_nonneg ht).symm
          _ = (Int.gcd a b : ℤ) := by exact_mod_cast habs
      simpa only [htGcd] using hcolumn
    · have htNeg : t < 0 := lt_of_not_ge ht
      let D : Matrix (Fin 2) (Fin 2) ℤ := rowNegMatrix 0
      have hD : reachableByUnimodularRowOps D :=
        reachableByUnimodularRowOps_of_elementary
          (Or.inr (Or.inl ⟨0, rfl⟩))
      refine ⟨D * Pᵀ, reachableByUnimodularRowOps_mul hP hD, ?_⟩
      have hnegAction : D *ᵥ (![t, 0] : Fin 2 → ℤ) = ![-t, 0] := by
        -- The sign operation changes only the first coordinate.
        ext i
        fin_cases i
        · simp [D, rowNegMatrix, Matrix.mulVec, dotProduct]
        · simp [D, rowNegMatrix, Matrix.mulVec, dotProduct]
      have hnegGcd : -t = (Int.gcd a b : ℤ) := by
        calc
          -t = (Int.natAbs t : ℤ) :=
            (Int.ofNat_natAbs_of_nonpos (le_of_lt htNeg)).symm
          _ = (Int.gcd a b : ℤ) := by exact_mod_cast habs
      rw [← Matrix.mulVec_mulVec, hcolumn, hnegAction, hnegGcd]
  · have ha : a = 0 := by
      by_contra ha
      exact hnot (Or.inl ha)
    have hb : b = 0 := by
      by_contra hb
      exact hnot (Or.inr hb)
    subst a
    subst b
    refine ⟨1, reachableByUnimodularRowOps_one, ?_⟩
    simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: extend a square matrix by an
identity coordinate at the head. -/
private def rowOpsLiftTailMatrix
    (S : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons
    (Fin.cons 1 (fun _ : Fin n ↦ 0))
    (fun i ↦ Fin.cons 0 (fun j ↦ S i j))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: tail lifting preserves matrix
multiplication. -/
private lemma rowOpsLiftTailMatrix_mul
    (S V : Matrix (Fin n) (Fin n) ℤ) :
    rowOpsLiftTailMatrix (S * V) = rowOpsLiftTailMatrix S * rowOpsLiftTailMatrix V := by
  -- The head coordinate multiplies as the identity and the tail block multiplies as `S * V`.
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp [rowOpsLiftTailMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
      | succ j => simp [rowOpsLiftTailMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  | succ i =>
      cases j using Fin.cases with
      | zero => simp [rowOpsLiftTailMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
      | succ j => simp [rowOpsLiftTailMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: tail lifting preserves the
identity matrix. -/
private lemma rowOpsLiftTailMatrix_one :
    rowOpsLiftTailMatrix (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := by
  -- Each of the four head/tail blocks is the corresponding identity block.
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp [rowOpsLiftTailMatrix]
      | succ j => simp [rowOpsLiftTailMatrix, Fin.ext_iff]
  | succ i =>
      cases j using Fin.cases with
      | zero => simp [rowOpsLiftTailMatrix, Fin.ext_iff]
      | succ j => simp [rowOpsLiftTailMatrix, Matrix.one_apply, Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: tail lifting sends a row swap
to the same swap on successor indices. -/
private lemma rowOpsLiftTailMatrix_rowSwap (i j : Fin n) :
    rowOpsLiftTailMatrix (rowSwapMatrix i j) = rowSwapMatrix i.succ j.succ := by
  -- Both sides fix the head coordinate and exchange precisely the same two tail coordinates.
  ext r k
  cases r using Fin.cases with
  | zero =>
      cases k using Fin.cases with
      | zero =>
          simp [rowOpsLiftTailMatrix, Matrix.swap,
            Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
              (Fin.succ_ne_zero j).symm]
      | succ k =>
          simp [rowOpsLiftTailMatrix, Matrix.swap,
            Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
              (Fin.succ_ne_zero j).symm, (Fin.succ_ne_zero k).symm]
  | succ r =>
      cases k using Fin.cases with
      | zero =>
          by_cases hri : r = i
          · subst r
            simp [rowOpsLiftTailMatrix, Matrix.swap]
          · by_cases hrj : r = j
            · subst r
              simp [rowOpsLiftTailMatrix, Matrix.swap]
            · simp [rowOpsLiftTailMatrix, Matrix.swap,
                Equiv.swap_apply_of_ne_of_ne hri hrj,
                Equiv.swap_apply_of_ne_of_ne ((Fin.succ_injective _).ne hri)
                  ((Fin.succ_injective _).ne hrj)]
      | succ k =>
          by_cases hri : r = i
          · subst r
            simp [rowOpsLiftTailMatrix, Matrix.swap]
          · by_cases hrj : r = j
            · subst r
              simp [rowOpsLiftTailMatrix, Matrix.swap]
            · simp [rowOpsLiftTailMatrix, Matrix.swap,
                Equiv.swap_apply_of_ne_of_ne hri hrj,
                Equiv.swap_apply_of_ne_of_ne ((Fin.succ_injective _).ne hri)
                  ((Fin.succ_injective _).ne hrj), Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: tail lifting sends a row sign
change to the same sign change on the successor index. -/
private lemma rowOpsLiftTailMatrix_rowNeg (i : Fin n) :
    rowOpsLiftTailMatrix (rowNegMatrix i) = rowNegMatrix i.succ := by
  -- The head remains positive and the same tail diagonal entry changes sign.
  ext r k
  cases r using Fin.cases with
  | zero =>
      cases k using Fin.cases with
      | zero => simp [rowOpsLiftTailMatrix, rowNegMatrix, Fin.ext_iff]
      | succ k => simp [rowOpsLiftTailMatrix, rowNegMatrix, Fin.ext_iff]
  | succ r =>
      cases k using Fin.cases with
      | zero => simp [rowOpsLiftTailMatrix, rowNegMatrix, Fin.ext_iff]
      | succ k => simp [rowOpsLiftTailMatrix, rowNegMatrix, Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: tail lifting sends a row
addition to the same addition on successor indices. -/
private lemma rowOpsLiftTailMatrix_rowAdd (i j : Fin n) (c : ℤ) :
    rowOpsLiftTailMatrix (rowAddMatrix i j c) = rowAddMatrix i.succ j.succ c := by
  -- The head remains fixed and the same off-diagonal coefficient appears in the tail block.
  ext r k
  cases r using Fin.cases with
  | zero =>
      cases k using Fin.cases with
      | zero => simp [rowOpsLiftTailMatrix, rowAddMatrix, Fin.ext_iff]
      | succ k => simp [rowOpsLiftTailMatrix, rowAddMatrix, Fin.ext_iff]
  | succ r =>
      cases k using Fin.cases with
      | zero => simp [rowOpsLiftTailMatrix, rowAddMatrix, Fin.ext_iff]
      | succ k => simp [rowOpsLiftTailMatrix, rowAddMatrix, Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: tail lifting preserves
reachability. -/
private lemma reachableByUnimodularRowOps_liftTail
    {S : Matrix (Fin n) (Fin n) ℤ}
    (hS : reachableByUnimodularRowOps S) :
    reachableByUnimodularRowOps (rowOpsLiftTailMatrix S) := by
  rcases hS with ⟨ops, hOps, hFold⟩
  subst S
  induction ops with
  | nil =>
      simpa only [List.foldl_nil, rowOpsLiftTailMatrix_one] using
        (reachableByUnimodularRowOps_one (n := n + 1))
  | cons E ops ih =>
      have hmemE : E ∈ E :: ops := List.mem_cons_self
      have hE : IsElementaryUnimodularRowMatrix E := hOps E hmemE
      have hTail : ∀ M ∈ ops, IsElementaryUnimodularRowMatrix M := by
        intro M hM
        exact hOps M (List.mem_cons_of_mem E hM)
      have hLiftE : IsElementaryUnimodularRowMatrix (rowOpsLiftTailMatrix E) := by
        rcases hE with ⟨i, j, hij, rfl⟩ | ⟨i, rfl⟩ | ⟨i, j, c, hij, rfl⟩
        · rw [rowOpsLiftTailMatrix_rowSwap]
          exact Or.inl ⟨i.succ, j.succ, (Fin.succ_injective _).ne hij, rfl⟩
        · rw [rowOpsLiftTailMatrix_rowNeg]
          exact Or.inr (Or.inl ⟨i.succ, rfl⟩)
        · rw [rowOpsLiftTailMatrix_rowAdd]
          exact Or.inr (Or.inr ⟨i.succ, j.succ, c, (Fin.succ_injective _).ne hij, rfl⟩)
      rw [List.foldl_cons, mul_one, foldl_leftMul_eq_foldl_one_mul,
        rowOpsLiftTailMatrix_mul]
      exact reachableByUnimodularRowOps_mul
        (reachableByUnimodularRowOps_of_elementary hLiftE) (ih hTail)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: extend a `2 × 2` matrix by
the identity on all coordinates after the first two. -/
private def rowOpsLiftHeadMatrix
    (U : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
  Fin.cons
    (Fin.cons (U 0 0) (Fin.cons (U 0 1) (fun _ : Fin n ↦ 0)))
    (Fin.cons
      (Fin.cons (U 1 0) (Fin.cons (U 1 1) (fun _ : Fin n ↦ 0)))
      (fun i ↦ Fin.cons 0 (Fin.cons 0 (fun j ↦ if i = j then 1 else 0))))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: head lifting preserves matrix
multiplication. -/
private lemma rowOpsLiftHeadMatrix_mul
    (U W : Matrix (Fin 2) (Fin 2) ℤ) :
    rowOpsLiftHeadMatrix (n := n) (U * W) =
      rowOpsLiftHeadMatrix (n := n) U * rowOpsLiftHeadMatrix (n := n) W := by
  -- The first two coordinates multiply as `U * W`; the remaining block is the identity.
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
      | succ j =>
          cases j using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
          | succ j => simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
          | succ j =>
              cases j using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
              | succ j => simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
      | succ i =>
          cases j using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
          | succ j =>
              cases j using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
              | succ j =>
                  by_cases hij : i = j
                  · subst j
                    simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
                  · simp [rowOpsLiftHeadMatrix, Matrix.mul_apply, Fin.sum_univ_succ, hij]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: head lifting preserves the
identity matrix. -/
private lemma rowOpsLiftHeadMatrix_one :
    rowOpsLiftHeadMatrix (n := n) (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  -- The explicit head block and the tail block are both identities.
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp [rowOpsLiftHeadMatrix, Fin.ext_iff]
      | succ j =>
          cases j using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, Fin.ext_iff]
          | succ j => simp [rowOpsLiftHeadMatrix, Fin.ext_iff]
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, Fin.ext_iff]
          | succ j =>
              cases j using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, Fin.ext_iff]
              | succ j => simp [rowOpsLiftHeadMatrix, Fin.ext_iff]
      | succ i =>
          cases j using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, Fin.ext_iff]
          | succ j =>
              cases j using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, Fin.ext_iff]
              | succ j => simp [rowOpsLiftHeadMatrix, Matrix.one_apply, Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: head lifting carries the
nontrivial swap on `Fin 2` to the corresponding swap in the larger dimension. -/
private lemma rowOpsLiftHeadMatrix_rowSwap_zero_one :
    rowOpsLiftHeadMatrix (n := n) (rowSwapMatrix (0 : Fin 2) 1) =
      rowSwapMatrix (0 : Fin (n + 2)) 1 := by
  -- Inspect the two head coordinates and the untouched tail separately.
  ext r k
  cases r using Fin.cases with
  | zero =>
      cases k using Fin.cases with
      | zero => simp [rowOpsLiftHeadMatrix, Matrix.swap, Fin.ext_iff]
      | succ k =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, Matrix.swap, Fin.ext_iff]
          | succ k => simp [rowOpsLiftHeadMatrix, Matrix.swap, Fin.ext_iff]
  | succ r =>
      cases r using Fin.cases with
      | zero =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, Matrix.swap, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, Matrix.swap, Fin.ext_iff]
              | succ k => simp [rowOpsLiftHeadMatrix, Matrix.swap, Fin.ext_iff]
      | succ r =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, Matrix.swap, Equiv.swap_apply_def, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, Matrix.swap, Equiv.swap_apply_def, Fin.ext_iff]
              | succ k =>
                  simp [rowOpsLiftHeadMatrix, Matrix.swap, Equiv.swap_apply_def,
                    Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: the reverse ordering of the
nontrivial head swap has the same lift. -/
private lemma rowOpsLiftHeadMatrix_rowSwap_one_zero :
    rowOpsLiftHeadMatrix (n := n) (rowSwapMatrix (1 : Fin 2) 0) =
      rowSwapMatrix (1 : Fin (n + 2)) 0 := by
  -- Swap matrices are symmetric in their two indices.
  simpa only [Matrix.swap_comm] using
    (rowOpsLiftHeadMatrix_rowSwap_zero_one (n := n))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: head lifting carries the
first row sign change to the larger dimension. -/
private lemma rowOpsLiftHeadMatrix_rowNeg_zero :
    rowOpsLiftHeadMatrix (n := n) (rowNegMatrix (0 : Fin 2)) =
      rowNegMatrix (0 : Fin (n + 2)) := by
  -- The first diagonal entry is negated and every other diagonal entry remains one.
  ext r k
  cases r using Fin.cases with
  | zero =>
      cases k using Fin.cases with
      | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
      | succ k =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix]
          | succ k =>
              simp [rowOpsLiftHeadMatrix, rowNegMatrix,
                (Fin.succ_ne_zero k.succ).symm]
  | succ r =>
      cases r using Fin.cases with
      | zero =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
              | succ k => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
      | succ r =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
              | succ k => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: head lifting carries the
second row sign change to the larger dimension. -/
private lemma rowOpsLiftHeadMatrix_rowNeg_one :
    rowOpsLiftHeadMatrix (n := n) (rowNegMatrix (1 : Fin 2)) =
      rowNegMatrix (1 : Fin (n + 2)) := by
  -- The second diagonal entry is negated and every other diagonal entry remains one.
  ext r k
  cases r using Fin.cases with
  | zero =>
      cases k using Fin.cases with
      | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
      | succ k =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
          | succ k => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
  | succ r =>
      cases r using Fin.cases with
      | zero =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
              | succ k => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
      | succ r =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]
              | succ k => simp [rowOpsLiftHeadMatrix, rowNegMatrix, Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: head lifting carries an
addition from the second row to the first to the larger dimension. -/
private lemma rowOpsLiftHeadMatrix_rowAdd_zero_one (c : ℤ) :
    rowOpsLiftHeadMatrix (n := n) (rowAddMatrix (0 : Fin 2) 1 c) =
      rowAddMatrix (0 : Fin (n + 2)) 1 c := by
  -- The sole off-diagonal coefficient remains in position `(0, 1)`.
  ext r k
  cases r using Fin.cases with
  | zero =>
      cases k using Fin.cases with
      | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
      | succ k =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
          | succ k => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
  | succ r =>
      cases r using Fin.cases with
      | zero =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
              | succ k => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
      | succ r =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
              | succ k => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: head lifting carries an
addition from the first row to the second to the larger dimension. -/
private lemma rowOpsLiftHeadMatrix_rowAdd_one_zero (c : ℤ) :
    rowOpsLiftHeadMatrix (n := n) (rowAddMatrix (1 : Fin 2) 0 c) =
      rowAddMatrix (1 : Fin (n + 2)) 0 c := by
  -- The sole off-diagonal coefficient remains in position `(1, 0)`.
  ext r k
  cases r using Fin.cases with
  | zero =>
      cases k using Fin.cases with
      | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
      | succ k =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
          | succ k => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
  | succ r =>
      cases r using Fin.cases with
      | zero =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
              | succ k => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
      | succ r =>
          cases k using Fin.cases with
          | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
          | succ k =>
              cases k using Fin.cases with
              | zero => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]
              | succ k => simp [rowOpsLiftHeadMatrix, rowAddMatrix, Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: head lifting preserves
reachability of `2 × 2` row-operation products. -/
private lemma reachableByUnimodularRowOps_liftHead
    {U : Matrix (Fin 2) (Fin 2) ℤ}
    (hU : reachableByUnimodularRowOps U) :
    reachableByUnimodularRowOps (rowOpsLiftHeadMatrix (n := n) U) := by
  rcases hU with ⟨ops, hOps, hFold⟩
  subst U
  induction ops with
  | nil =>
      simpa only [List.foldl_nil, rowOpsLiftHeadMatrix_one] using
        (reachableByUnimodularRowOps_one (n := n + 2))
  | cons E ops ih =>
      have hmemE : E ∈ E :: ops := List.mem_cons_self
      have hE : IsElementaryUnimodularRowMatrix E := hOps E hmemE
      have hTail : ∀ M ∈ ops, IsElementaryUnimodularRowMatrix M := by
        intro M hM
        exact hOps M (List.mem_cons_of_mem E hM)
      have hLiftE : IsElementaryUnimodularRowMatrix
          (rowOpsLiftHeadMatrix (n := n) E) := by
        rcases hE with ⟨i, j, hij, rfl⟩ | ⟨i, rfl⟩ | ⟨i, j, c, hij, rfl⟩
        · by_cases hi : i = 0
          · have hj : j = 1 := by omega
            subst i
            subst j
            rw [rowOpsLiftHeadMatrix_rowSwap_zero_one]
            have hne : (0 : Fin (n + 2)) ≠ 1 := Fin.zero_ne_one
            exact Or.inl ⟨0, 1, hne, rfl⟩
          · have hi' : i = 1 := by omega
            have hj : j = 0 := by omega
            subst i
            subst j
            rw [rowOpsLiftHeadMatrix_rowSwap_one_zero]
            have hne : (1 : Fin (n + 2)) ≠ 0 := Fin.zero_ne_one.symm
            exact Or.inl ⟨1, 0, hne, rfl⟩
        · by_cases hi : i = 0
          · subst i
            rw [rowOpsLiftHeadMatrix_rowNeg_zero]
            exact Or.inr (Or.inl ⟨0, rfl⟩)
          · have hi' : i = 1 := by omega
            subst i
            rw [rowOpsLiftHeadMatrix_rowNeg_one]
            exact Or.inr (Or.inl ⟨1, rfl⟩)
        · by_cases hi : i = 0
          · have hj : j = 1 := by omega
            subst i
            subst j
            rw [rowOpsLiftHeadMatrix_rowAdd_zero_one]
            have hne : (0 : Fin (n + 2)) ≠ 1 := Fin.zero_ne_one
            exact Or.inr (Or.inr ⟨0, 1, c, hne, rfl⟩)
          · have hi' : i = 1 := by omega
            have hj : j = 0 := by omega
            subst i
            subst j
            rw [rowOpsLiftHeadMatrix_rowAdd_one_zero]
            have hne : (1 : Fin (n + 2)) ≠ 0 := Fin.zero_ne_one.symm
            exact Or.inr (Or.inr ⟨1, 0, c, hne, rfl⟩)
      rw [List.foldl_cons, mul_one, foldl_leftMul_eq_foldl_one_mul,
        rowOpsLiftHeadMatrix_mul]
      exact reachableByUnimodularRowOps_mul
        (reachableByUnimodularRowOps_of_elementary hLiftE) (ih hTail)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: tail lifting fixes the head of
a column and applies the original matrix to its tail. -/
private lemma rowOpsLiftTailMatrix_mulVec
    (S : Matrix (Fin n) (Fin n) ℤ)
    (x : ℤ)
    (xs : Fin n → ℤ) :
    rowOpsLiftTailMatrix S *ᵥ Fin.cons x xs = Fin.cons x (S *ᵥ xs) := by
  -- Split the output coordinate into its head and tail cases.
  ext i
  cases i using Fin.cases with
  | zero => simp [rowOpsLiftTailMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  | succ i => simp [rowOpsLiftTailMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: head lifting applies a
`2 × 2` matrix to the first two column coordinates and fixes the tail. -/
private lemma rowOpsLiftHeadMatrix_mulVec
    (U : Matrix (Fin 2) (Fin 2) ℤ)
    (x y : ℤ)
    (zs : Fin n → ℤ) :
    rowOpsLiftHeadMatrix (n := n) U *ᵥ Fin.cons x (Fin.cons y zs) =
      Fin.cons ((U *ᵥ (![x, y] : Fin 2 → ℤ)) 0)
        (Fin.cons ((U *ᵥ (![x, y] : Fin 2 → ℤ)) 1) zs) := by
  -- The explicit block matrix separates the first two dot products from every tail coordinate.
  ext i
  cases i using Fin.cases with
  | zero =>
      simp [rowOpsLiftHeadMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          simp [rowOpsLiftHeadMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      | succ i =>
          simp [rowOpsLiftHeadMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: the coefficient gcd of an
integer column. -/
private def integerVectorGcd (a : Fin n → ℤ) : ℤ :=
  Finset.univ.gcd a

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: adjoining a head coordinate
turns the coefficient gcd into the binary gcd of the head and tail gcd. -/
private lemma integerVectorGcd_cons (x : ℤ) (xs : Fin n → ℤ) :
    integerVectorGcd (Fin.cons x xs) = Int.gcd x (integerVectorGcd xs) := by
  -- Decompose `Fin (n + 1)` into its head and successor image inside the finite gcd.
  have huniv :
      (Finset.univ : Finset (Fin (n + 1))) = insert 0 (Finset.univ.image Fin.succ) := by
    ext i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp
  rw [integerVectorGcd, huniv, Finset.gcd_insert, Finset.gcd_image, integerVectorGcd]
  simpa using (Int.coe_gcd x (integerVectorGcd xs)).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: reachable row operations send
any nonempty integer column to its coefficient gcd in the first coordinate. -/
private lemma exists_reachable_rowReduction_to_gcd
    (a : Fin (n + 1) → ℤ) :
    ∃ R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
      reachableByUnimodularRowOps R ∧
        R *ᵥ a = Fin.cons (integerVectorGcd a) (fun _ : Fin n ↦ 0) := by
  induction n with
  | zero =>
      by_cases ha : 0 ≤ a 0
      · refine ⟨1, reachableByUnimodularRowOps_one, ?_⟩
        -- In dimension one, the gcd is the nonnegative value of the sole coordinate.
        ext i
        fin_cases i
        simpa [integerVectorGcd] using (Int.normalize_of_nonneg ha).symm
      · have haNeg : a 0 < 0 := lt_of_not_ge ha
        let D : Matrix (Fin 1) (Fin 1) ℤ := rowNegMatrix 0
        have hD : reachableByUnimodularRowOps D :=
          reachableByUnimodularRowOps_of_elementary
            (Or.inr (Or.inl ⟨0, rfl⟩))
        refine ⟨D, hD, ?_⟩
        -- The sole sign change turns a negative coefficient into its nonnegative gcd.
        ext i
        fin_cases i
        simpa [D, rowNegMatrix, Matrix.mulVec, dotProduct, integerVectorGcd] using
          (Int.normalize_of_nonpos (le_of_lt haNeg)).symm
  | succ n ih =>
      let x : ℤ := a 0
      let xs : Fin (n + 1) → ℤ := Fin.tail a
      rcases ih xs with ⟨S, hS, hSaction⟩
      rcases exists_reachable_pairReduction_to_gcd x (integerVectorGcd xs) with
        ⟨P, hP, hPaction⟩
      let S' := rowOpsLiftTailMatrix S
      let P' := rowOpsLiftHeadMatrix (n := n) P
      have hS' : reachableByUnimodularRowOps S' :=
        reachableByUnimodularRowOps_liftTail hS
      have hP' : reachableByUnimodularRowOps P' :=
        reachableByUnimodularRowOps_liftHead hP
      have haCons : a = Fin.cons x xs := by
        dsimp only [x, xs]
        exact (Fin.cons_self_tail a).symm
      refine ⟨P' * S', reachableByUnimodularRowOps_mul hS' hP', ?_⟩
      -- First normalize the tail; then the lifted pair operation combines its gcd with the head.
      calc
        (P' * S') *ᵥ a = P' *ᵥ (S' *ᵥ a) := by rw [Matrix.mulVec_mulVec]
        _ = P' *ᵥ Fin.cons x (S *ᵥ xs) := by
          rw [haCons]
          dsimp only [S']
          rw [rowOpsLiftTailMatrix_mulVec]
        _ = P' *ᵥ Fin.cons x
            (Fin.cons (integerVectorGcd xs) (fun _ : Fin n ↦ 0)) := by rw [hSaction]
        _ = Fin.cons ((P *ᵥ (![x, integerVectorGcd xs] : Fin 2 → ℤ)) 0)
            (Fin.cons ((P *ᵥ (![x, integerVectorGcd xs] : Fin 2 → ℤ)) 1)
              (fun _ : Fin n ↦ 0)) := by
                exact rowOpsLiftHeadMatrix_mulVec P x (integerVectorGcd xs)
                  (fun _ : Fin n ↦ 0)
        _ = Fin.cons (integerVectorGcd a) (fun _ : Fin (n + 1) ↦ 0) := by
          rw [hPaction, haCons, integerVectorGcd_cons]
          ext i
          cases i using Fin.cases with
          | zero => simp
          | succ i =>
              cases i using Fin.cases with
              | zero => simp
              | succ i => simp

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: left multiplication by a row
addition updates its target row. -/
private lemma rowAddMatrix_mul_apply_same
    (i j : Fin n) (c : ℤ) (hij : i ≠ j)
    (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) :
    (rowAddMatrix i j c * A) i k = A i k + c * A j k := by
  -- Rewrite to the canonical transvection computation rule.
  rw [rowAddMatrix_eq_transvection i j c hij]
  exact Matrix.transvection_mul_apply_same i j k c A

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: left multiplication by a row
addition leaves every nontarget row unchanged. -/
private lemma rowAddMatrix_mul_apply_of_ne
    (i j r : Fin n) (c : ℤ) (hij : i ≠ j) (hri : r ≠ i)
    (A : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) :
    (rowAddMatrix i j c * A) r k = A r k := by
  -- Rewrite to the canonical transvection computation rule.
  rw [rowAddMatrix_eq_transvection i j c hij]
  exact Matrix.transvection_mul_apply_of_ne i j r k hri c A

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: folding additions into the
first row accumulates their coefficients while leaving all other rows fixed. -/
private lemma foldl_topRowAdds_apply
    (L : List (Fin n × ℤ))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (r k : Fin (n + 1)) :
    (L.foldl
        (fun X p ↦ rowAddMatrix (0 : Fin (n + 1)) p.1.succ p.2 * X) A) r k =
      if r = 0 then
        A 0 k + (L.map (fun p ↦ p.2 * A p.1.succ k)).sum
      else A r k := by
  induction L generalizing A with
  | nil =>
      by_cases hr : r = 0
      · subst r
        simp
      · simp [hr]
  | cons p L ih =>
      rw [List.foldl_cons, ih]
      by_cases hr : r = 0
      · subst r
        rw [if_pos rfl, rowAddMatrix_mul_apply_same]
        · simp only [List.map_cons, List.sum_cons]
          have hsource (q : Fin n × ℤ) :
              (rowAddMatrix (0 : Fin (n + 1)) p.1.succ p.2 * A) q.1.succ k =
                A q.1.succ k := by
            exact rowAddMatrix_mul_apply_of_ne 0 p.1.succ q.1.succ p.2
              (Fin.succ_ne_zero p.1).symm (Fin.succ_ne_zero q.1) A k
          simp only [hsource]
          rw [if_true]
          ring
        · exact (Fin.succ_ne_zero p.1).symm
      · simp only [if_neg hr]
        exact rowAddMatrix_mul_apply_of_ne 0 p.1.succ r p.2
          (Fin.succ_ne_zero p.1).symm hr A k

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: the matrix adding a prescribed
linear combination of all tail rows to the first row. -/
private def topRowAddMatrix (c : Fin n → ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons
    (Fin.cons 1 c)
    (fun i ↦ Fin.cons 0 (fun j ↦ if i = j then 1 else 0))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: every simultaneous first-row
addition matrix is reachable by its individual row additions. -/
private lemma reachableByUnimodularRowOps_topRowAddMatrix (c : Fin n → ℤ) :
    reachableByUnimodularRowOps (topRowAddMatrix c) := by
  let ops : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :=
    List.ofFn (fun i : Fin n ↦ rowAddMatrix 0 i.succ (c i))
  refine ⟨ops, ?_, ?_⟩
  · intro M hM
    simp only [ops, List.mem_ofFn] at hM
    rcases hM with ⟨i, rfl⟩
    exact Or.inr (Or.inr ⟨0, i.succ, c i, (Fin.succ_ne_zero i).symm, rfl⟩)
  · -- The fold formula evaluates to the explicit first-row matrix on the identity.
    ext r k
    have hfold := foldl_topRowAdds_apply
      (L := List.ofFn fun i : Fin n ↦ (i, c i))
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) r k
    have hops : ops = (List.ofFn fun i : Fin n ↦ (i, c i)).map
        (fun p ↦ rowAddMatrix (0 : Fin (n + 1)) p.1.succ p.2) := by
      simpa only [ops] using
        (List.ofFn_comp' (fun i : Fin n ↦ (i, c i))
          (fun p ↦ rowAddMatrix (0 : Fin (n + 1)) p.1.succ p.2))
    rw [hops, List.foldl_map, hfold]
    cases r using Fin.cases with
    | zero =>
        cases k using Fin.cases with
        | zero => simp [topRowAddMatrix, List.sum_ofFn]
        | succ k =>
            simp [topRowAddMatrix, Matrix.one_apply, List.sum_ofFn,
              (Fin.succ_ne_zero k).symm]
    | succ r =>
        cases k using Fin.cases with
        | zero => simp [topRowAddMatrix]
        | succ k => simp [topRowAddMatrix, Matrix.one_apply, Fin.ext_iff]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: the upper block matrix with
first column equal to the first standard basis vector. -/
private def upperBlockMatrix
    (b : Fin n → ℤ)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons
    (Fin.cons 1 b)
    (fun i ↦ Fin.cons 0 (fun j ↦ A i j))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: multiplying a lifted tail
matrix by simultaneous first-row additions forms the expected upper block matrix. -/
private lemma topRowAddMatrix_mul_liftTail
    (c : Fin n → ℤ)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    topRowAddMatrix c * rowOpsLiftTailMatrix A = upperBlockMatrix (c ᵥ* A) A := by
  -- Compare the head row, head column, and trailing block entrywise.
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simp [topRowAddMatrix, rowOpsLiftTailMatrix, upperBlockMatrix, Matrix.mul_apply,
            Fin.sum_univ_succ]
      | succ j =>
          simp [topRowAddMatrix, rowOpsLiftTailMatrix, upperBlockMatrix, Matrix.mul_apply,
            Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          simp [topRowAddMatrix, rowOpsLiftTailMatrix, upperBlockMatrix, Matrix.mul_apply,
            Fin.sum_univ_succ]
      | succ j =>
          simp [topRowAddMatrix, rowOpsLiftTailMatrix, upperBlockMatrix, Matrix.mul_apply,
            Fin.sum_univ_succ]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: an upper block matrix with
unimodular reachable tail block is reachable. -/
private lemma reachableByUnimodularRowOps_upperBlockMatrix
    (b : Fin n → ℤ)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : IsUnit A.det)
    (hReachA : reachableByUnimodularRowOps A) :
    reachableByUnimodularRowOps (upperBlockMatrix b A) := by
  let c : Fin n → ℤ := b ᵥ* A⁻¹
  have hc : c ᵥ* A = b := by
    -- The nonsingular inverse solves the row equation defining the desired first row.
    calc
      c ᵥ* A = b ᵥ* (A⁻¹ * A) := by rw [Matrix.vecMul_vecMul]
      _ = b := by rw [A.nonsing_inv_mul hA, Matrix.vecMul_one]
  have hTop := reachableByUnimodularRowOps_topRowAddMatrix c
  have hTail := reachableByUnimodularRowOps_liftTail hReachA
  rw [← hc, ← topRowAddMatrix_mul_liftTail]
  exact reachableByUnimodularRowOps_mul hTail hTop

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: the coefficient gcd divides
every coordinate of an integer column. -/
private lemma integerVectorGcd_dvd (a : Fin n → ℤ) (i : Fin n) :
    integerVectorGcd a ∣ a i := by
  -- This is the defining divisibility property of a finite gcd.
  rw [integerVectorGcd]
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  exact Finset.gcd_dvd hi

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: the first column of a
unimodular integer matrix has coefficient gcd one. -/
private lemma integerVectorGcd_firstColumn_eq_one
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hU : IsUnit U.det) :
    integerVectorGcd (fun i ↦ U i 0) = 1 := by
  rcases (isUnit_det_iff_exists_int_inverse U).mp hU with ⟨V, _, hVU⟩
  let g := integerVectorGcd (fun i ↦ U i 0)
  have hgDvdSum : g ∣ ∑ i, V 0 i * U i 0 := by
    -- Each summand is divisible by the column gcd.
    apply Finset.dvd_sum
    intro i hi
    exact dvd_mul_of_dvd_right (integerVectorGcd_dvd (fun k ↦ U k 0) i) (V 0 i)
  have hsum : (∑ i, V 0 i * U i 0) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.one_apply, if_pos] using
      congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ ↦ M 0 0) hVU
  have hgDvdOne : g ∣ 1 := by simpa only [hsum] using hgDvdSum
  rcases hgDvdOne with ⟨q, hq⟩
  have hgUnit : IsUnit g := IsUnit.of_mul_eq_one q hq.symm
  have hgNonneg : 0 ≤ g := by
    dsimp only [g, integerVectorGcd]
    exact Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  -- The only nonnegative unit of `ℤ` is `1`.
  rcases Int.isUnit_eq_one_or hgUnit with hg | hg
  · exact hg
  · omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: the determinant of an upper
block matrix with leading entry one is the determinant of its tail block. -/
private lemma det_upperBlockMatrix
    (b : Fin n → ℤ)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    (upperBlockMatrix b A).det = A.det := by
  -- Expand along the first column, whose only nonzero entry is its leading one.
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [upperBlockMatrix]
  congr 1

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean`: every integer matrix with unit
determinant is generated by the three elementary row operations. -/
private lemma reachableByUnimodularRowOps_of_isUnit_det :
    ∀ (m : ℕ) (U : Matrix (Fin m) (Fin m) ℤ),
      IsUnit U.det → reachableByUnimodularRowOps U := by
  intro m
  induction m with
  | zero =>
      intro U hU
      have hUOne : U = 1 := by
        ext i
        exact Fin.elim0 i
      rw [hUOne]
      exact reachableByUnimodularRowOps_one
  | succ n ih =>
      intro U hU
      let a : Fin (n + 1) → ℤ := fun i ↦ U i 0
      have hgcd : integerVectorGcd a = 1 :=
        integerVectorGcd_firstColumn_eq_one U hU
      rcases exists_reachable_rowReduction_to_gcd a with ⟨R, hR, hRaction⟩
      rcases reachableByUnimodularRowOps_hasInverse hR with
        ⟨Rinv, hRinv, hRRinv, hRinvR⟩
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := R * U
      let A : Matrix (Fin n) (Fin n) ℤ := M.submatrix Fin.succ Fin.succ
      let b : Fin n → ℤ := fun j ↦ M 0 j.succ
      have hMcol (i : Fin (n + 1)) :
          M i 0 = ((Fin.cons (1 : ℤ) (fun _ : Fin n ↦ 0)) : Fin (n + 1) → ℤ) i := by
        have hi := congrFun hRaction i
        simpa only [M, a, Matrix.mul_apply, Matrix.mulVec, dotProduct, hgcd] using hi
      have hMUpper : M = upperBlockMatrix b A := by
        -- The reduced first column and the trailing submatrix determine this upper block form.
        ext i j
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => simpa [upperBlockMatrix] using hMcol 0
            | succ j => rfl
        | succ i =>
            cases j using Fin.cases with
            | zero => simpa [upperBlockMatrix] using hMcol i.succ
            | succ j => rfl
      have hMdet : IsUnit M.det := by
        have hRdet := isUnit_det_of_reachableByUnimodularRowOps hR
        simpa only [M, Matrix.det_mul] using hRdet.mul hU
      have hAdet : IsUnit A.det := by
        rw [hMUpper, det_upperBlockMatrix] at hMdet
        exact hMdet
      have hA : reachableByUnimodularRowOps A := ih A hAdet
      have hM : reachableByUnimodularRowOps M := by
        rw [hMUpper]
        exact reachableByUnimodularRowOps_upperBlockMatrix b A hAdet hA
      have hRinvM : reachableByUnimodularRowOps (Rinv * M) :=
        reachableByUnimodularRowOps_mul hM hRinv
      have hrecover : Rinv * M = U := by
        -- Undo the initial column reduction to recover the original matrix.
        calc
          Rinv * M = (Rinv * R) * U := by simp only [M, Matrix.mul_assoc]
          _ = U := by rw [hRinvR, Matrix.one_mul]
      rwa [hrecover] at hRinvM

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_lemma_1_3.lean.
Lemma 1.3 (4). An integer square matrix is unimodular if and only if it can be obtained from
the identity by finitely many unimodular row operations. -/
theorem isUnit_det_iff_reachableByUnimodularRowOps (U : Matrix (Fin n) (Fin n) ℤ) :
    IsUnit U.det ↔ reachableByUnimodularRowOps U := by
  -- The forward direction is integer row reduction; the reverse uses a reachable inverse.
  constructor
  · exact reachableByUnimodularRowOps_of_isUnit_det n U
  · exact isUnit_det_of_reachableByUnimodularRowOps

end Lemma13

end Matrix

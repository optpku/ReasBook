/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_1
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef

open Matrix
open Matrix.IsHermitian

noncomputable section

-- Semantic recall hits verified for this item: `IsVectorNorm`, `‖·‖₁`, `‖·‖₂`,
-- `‖·‖∞`, `ellipsoidNorm`, `Matrix.frobenius_norm_def`,
-- `Matrix.l2_opNorm_mulVec`, `Matrix.IsHermitian.eigenvalues`, and
-- `Matrix.PosDef.eigenvalues_pos`.

/-- For Chapter01 Definition 1.2.3 (1): two norms on `ℝ^n` are equivalent when each bounds the other
up to positive multiplicative constants. -/
def EquivalentVectorNorms {n : ℕ} (normα normβ : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ 0 < μ₂ ∧ ∀ x : Fin n → ℝ,
    μ₁ * normα x ≤ normβ x ∧ normβ x ≤ μ₂ * normα x

/-- Unfolding formula for `EquivalentVectorNorms`. -/
@[simp] theorem equivalentVectorNorms_iff {n : ℕ} (normα normβ : (Fin n → ℝ) → ℝ) :
    EquivalentVectorNorms normα normβ ↔
      ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ 0 < μ₂ ∧ ∀ x : Fin n → ℝ,
        μ₁ * normα x ≤ normβ x ∧ normβ x ≤ μ₂ * normα x :=
  Iff.rfl

section L2OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- The matrix `ℓ₂` operator norm induced by the Euclidean norms on `ℝ^n` and `ℝ^m`. -/
abbrev matrixL2OperatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖A‖

notation3:max "‖" A "‖₂" => matrixL2OperatorNorm A

end L2OperatorNorm

section FrobeniusNorm

open scoped Matrix.Norms.Frobenius

/-- The Frobenius norm on real matrices. -/
abbrev matrixFrobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖A‖

notation3:max "‖" A "‖_F" => matrixFrobeniusNorm A

end FrobeniusNorm

section ElementwiseNorm

open scoped Matrix.Norms.Elementwise

/-- The largest absolute value of an entry of a real matrix, recorded using mathlib's elementwise
matrix norm. -/
abbrev matrixMaxEntryNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖A‖

end ElementwiseNorm

section OperatorNorm

open scoped Matrix.Norms.Operator

/-- The matrix `ℓ∞` norm, given by the largest absolute row sum. -/
abbrev matrixInfinityNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖A‖

/-- The matrix `ℓ₁` norm, obtained from the `ℓ∞` operator norm of the transpose. -/
abbrev matrixOneNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖Aᵀ‖

notation3:max "‖" A "‖∞" => matrixInfinityNorm A
notation3:max "‖" A "‖₁" => matrixOneNorm A

/-- Unfolding `‖A‖₁` through the transpose bridge to the `Matrix.Norms.Operator` owner. -/
@[simp] theorem matrixOneNorm_eq_matrixInfinityNorm_transpose {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖₁ = ‖Aᵀ‖∞ :=
  rfl

end OperatorNorm

/-- The eigenvalue family of a positive-definite real matrix, viewed through its Hermitian
structure. -/
def posDefEigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    Fin n → ℝ :=
  eigenvalues hA.isHermitian

/-- Expands `posDefEigenvalues` into the Hermitian eigenvalue family attached to `A`. -/
@[simp] theorem posDefEigenvalues_def {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    posDefEigenvalues A hA = eigenvalues hA.isHermitian :=
  rfl

/-- Unfolding formula for `IsLeast (Set.range (posDefEigenvalues A hA)) lambdaMin`. -/
theorem isLeast_posDefEigenvalues_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (lambdaMin : ℝ) :
    IsLeast (Set.range (posDefEigenvalues A hA)) lambdaMin ↔
      (∃ i, posDefEigenvalues A hA i = lambdaMin) ∧
        ∀ i, lambdaMin ≤ posDefEigenvalues A hA i := by
  constructor
  · intro hLeast
    -- Unpack the extremal witness from the range presentation.
    refine ⟨?_, ?_⟩
    · rcases hLeast.1 with ⟨i, hi⟩
      exact ⟨i, hi⟩
    · intro i
      exact hLeast.2 ⟨i, rfl⟩
  · rintro ⟨⟨i, hi⟩, hLower⟩
    -- Repackage the witness and the pointwise lower bound into `IsLeast`.
    refine ⟨?_, ?_⟩
    · exact ⟨i, hi⟩
    · rintro _ ⟨j, rfl⟩
      exact hLower j

/-- Unfolding formula for `IsGreatest (Set.range (posDefEigenvalues A hA)) lambdaMax`. -/
theorem isGreatest_posDefEigenvalues_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (lambdaMax : ℝ) :
    IsGreatest (Set.range (posDefEigenvalues A hA)) lambdaMax ↔
      (∃ i, posDefEigenvalues A hA i = lambdaMax) ∧
        ∀ i, posDefEigenvalues A hA i ≤ lambdaMax := by
  constructor
  · intro hGreatest
    -- Unpack the extremal witness from the range presentation.
    refine ⟨?_, ?_⟩
    · rcases hGreatest.1 with ⟨i, hi⟩
      exact ⟨i, hi⟩
    · intro i
      exact hGreatest.2 ⟨i, rfl⟩
  · rintro ⟨⟨i, hi⟩, hUpper⟩
    -- Repackage the witness and the pointwise upper bound into `IsGreatest`.
    refine ⟨?_, ?_⟩
    · exact ⟨i, hi⟩
    · rintro _ ⟨j, rfl⟩
      exact hUpper j

-- The source restatement `(1.2.25)` is already covered by the next two atomic vector inequalities.

/-- For Chapter01 Definition 1.2.3 (2): the source inequality `‖x‖₂ ≤ ‖x‖₁` on `ℝ^n`. -/
theorem vectorTwoNorm_le_vectorOneNorm {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖₂ ≤ ‖x‖₁ := by
  -- Compare the squared `ℓ₂` and `ℓ₁` formulas and then take square roots.
  rw [l2Norm_eq_sqrt_sum_sq, l1Norm_eq_sum_abs]
  refine Real.sqrt_le_iff.mpr ?_
  constructor
  · exact Finset.sum_nonneg fun i _ ↦ abs_nonneg (x i)
  · have hsq : (∑ i : Fin n, |x i| ^ 2) ≤ (∑ i : Fin n, |x i|) ^ 2 := by
      -- The square of a nonnegative sum dominates the sum of squares.
      simpa [pow_two] using
        (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i : Fin n ↦ |x i|)
          (fun i _ ↦ abs_nonneg (x i)) : _)
    simpa [pow_two] using hsq

/-- For Chapter01 Definition 1.2.3 (3): the source inequality `‖x‖₁ ≤ sqrt n * ‖x‖₂` on `ℝ^n`. -/
theorem vectorOneNorm_le_sqrt_mul_vectorTwoNorm {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖₁ ≤ Real.sqrt (n : ℝ) * ‖x‖₂ := by
  -- Apply Cauchy-Schwarz to the absolute-value vector against the all-ones vector.
  rw [l1Norm_eq_sum_abs, l2Norm_eq_sqrt_sum_sq]
  calc
    ∑ i : Fin n, |x i| = ∑ i : Fin n, |x i| * 1 := by simp
    _ ≤ Real.sqrt (∑ i : Fin n, |x i| ^ 2) * Real.sqrt (∑ i : Fin n, (1 : ℝ) ^ 2) := by
      simpa using
        Real.sum_mul_le_sqrt_mul_sqrt (s := Finset.univ) (f := fun i : Fin n ↦ |x i|)
          (g := fun _ : Fin n ↦ (1 : ℝ))
    _ = Real.sqrt (∑ i : Fin n, |x i| ^ 2) * Real.sqrt (n : ℝ) := by simp
    _ = Real.sqrt (n : ℝ) * Real.sqrt (∑ i : Fin n, |x i| ^ 2) := by ring

/-- For Chapter01 Definition 1.2.3 (4): the source inequality `‖x‖∞ ≤ ‖x‖₂` on `ℝ^n`. -/
theorem vectorInfNorm_le_vectorTwoNorm {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖∞ ≤ ‖x‖₂ := by
  -- Each coordinate is bounded by the `ℓ₂` norm; take the supremum over coordinates.
  rw [linftyNorm_eq_iSup_abs]
  refine Real.iSup_le ?_ (l2Norm_isVectorNorm.nonneg x)
  intro i
  simpa [l2Norm, lpNorm, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (x := WithLp.toLp (2 : ENNReal) x) i)

/-- For Chapter01 Definition 1.2.3 (5): the source inequality `‖x‖₂ ≤ sqrt n * ‖x‖∞` on `ℝ^n`. -/
theorem vectorTwoNorm_le_sqrt_mul_vectorInfNorm {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖₂ ≤ Real.sqrt (n : ℝ) * ‖x‖∞ := by
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hy :
      ‖y‖ ≤
        Real.sqrt (Fintype.card (Fin n)) *
          ⨆ i : Fin n, ‖inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i) y‖ :=
    (EuclideanSpace.basisFun (Fin n) ℝ).norm_le_card_mul_iSup_norm_inner y
  -- The standard orthonormal basis identifies the coordinate sup with `‖x‖∞`.
  simpa [y, l2Norm, lpNorm, linftyNorm_eq_iSup_abs, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_left] using hy

/-- For Chapter01 Definition 1.2.3 (6): the source inequality `‖x‖∞ ≤ ‖x‖₁` on `ℝ^n`. -/
theorem vectorInfNorm_le_vectorOneNorm {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖∞ ≤ ‖x‖₁ := by
  -- Route through the already-proved `ℓ∞ ≤ ℓ₂ ≤ ℓ₁` chain.
  exact (vectorInfNorm_le_vectorTwoNorm x).trans (vectorTwoNorm_le_vectorOneNorm x)

/-- For Chapter01 Definition 1.2.3 (7): the source inequality `‖x‖₁ ≤ n * ‖x‖∞` on `ℝ^n`. -/
theorem vectorOneNorm_le_nat_mul_vectorInfNorm {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖₁ ≤ (n : ℝ) * ‖x‖∞ := by
  -- The `ℓ₁` norm is the sum of coordinate norms, each bounded by `‖x‖∞`.
  rw [l1Norm_eq_sum_abs]
  simpa [linftyNorm, lpNorm] using (Pi.sum_norm_apply_le_norm x)

section

open scoped Matrix.Norms.Frobenius

/-- Helper for Chapter01 Definition 1.2.3: multiplication by a real matrix is bounded by its
Frobenius norm on vector `ℓ₂` norms. -/
lemma matrixMulVecTwoNorm_le_matrixFrobeniusNorm_mul_vectorTwoNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    ‖A.mulVec x‖₂ ≤ ‖A‖_F * ‖x‖₂ := by
  unfold matrixFrobeniusNorm
  have hMul := Matrix.frobenius_norm_mul A (Matrix.replicateCol (Fin 1) x)
  -- Convert matrix multiplication against a single-column matrix back to `mulVec`.
  rw [← Matrix.replicateCol_mulVec] at hMul
  have hVector : ‖WithLp.toLp 2 (A.mulVec x)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 x‖ := by
    -- The Frobenius norm of a single-column matrix is the vector `ℓ₂` norm.
    rw [← Matrix.frobenius_norm_replicateCol (ι := Fin 1) (A.mulVec x)]
    rw [← Matrix.frobenius_norm_replicateCol (ι := Fin 1) x]
    exact hMul
  simpa [l2Norm, lpNorm] using hVector

/-- Helper for Chapter01 Definition 1.2.3: each column has Euclidean norm at most the matrix `ℓ₂`
operator norm. -/
lemma columnVectorTwoNorm_le_matrixL2OperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    ‖A.col j‖₂ ≤ ‖A‖₂ := by
  let e : Fin n → ℝ := Pi.single j (1 : ℝ)
  have hMul := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 e)
  have hVector :
      ‖WithLp.toLp 2 (A.mulVec e)‖ ≤ matrixL2OperatorNorm A * ‖WithLp.toLp 2 e‖ := by
    -- Evaluate the operator norm on the `j`th basis vector.
    simpa [matrixL2OperatorNorm, Matrix.toLpLin_apply, e] using hMul
  have hBasis : ‖WithLp.toLp 2 e‖ = 1 := by
    -- The Euclidean norm of a standard basis vector is `1`.
    simp [e]
  simpa [matrixL2OperatorNorm, l2Norm, lpNorm, e, hBasis] using hVector

/-- Helper for Chapter01 Definition 1.2.3: any least positive-definite eigenvalue is a lower bound
for the Euclidean Rayleigh quotient of `A`. -/
lemma leastPosDefEigenvalue_le_euclideanRayleighQuotient {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (lambdaMin : ℝ)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues A hA)) lambdaMin) :
    ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 →
      lambdaMin ≤ inner ℝ (A.toEuclideanLin u) u / ‖u‖ ^ 2 := by
  intro u hu
  let Tlin := A.toEuclideanLin
  let T := Tlin.toContinuousLinearMap
  have hSymm : Tlin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  -- The minimizing Rayleigh quotient of the symmetric Euclidean operator is an eigenvalue.
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := ⟨⟨u, 0, hu⟩⟩
  let s : ℝ := ⨅ x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 },
    inner ℝ (Tlin x) x / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2
  have hs_eigen : Module.End.HasEigenvalue Tlin s := by
    simpa [s, Tlin] using LinearMap.IsSymmetric.hasEigenvalue_iInf_of_finiteDimensional hSymm
  have hs_spec : s ∈ spectrum ℝ A := by
    rw [← Matrix.spectrum_toLpLin (p := 2)]
    exact hs_eigen.mem_spectrum
  have hs_mem_range : s ∈ Set.range (posDefEigenvalues A hA) := by
    rw [hA.isHermitian.spectrum_eq_image_range] at hs_spec
    simpa [posDefEigenvalues_def] using hs_spec
  have hs_ge : lambdaMin ≤ s := hLambdaMin.2 hs_mem_range
  have hs_bdd :
      BddBelow (Set.range fun x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 } ↦
        inner ℝ (Tlin x) x / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    -- A Rayleigh quotient is bounded below by the negative operator norm.
    refine ⟨-‖T‖, ?_⟩
    rintro y ⟨x, rfl⟩
    have hnorm : |T.rayleighQuotient x| ≤ ‖T‖ := T.rayleighQuotient_le_norm x
    have hneg : -‖T‖ ≤ -|T.rayleighQuotient x| := by
      exact neg_le_neg hnorm
    have habs : -|T.rayleighQuotient x| ≤ T.rayleighQuotient x := neg_abs_le _
    simpa [T, Tlin, ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using le_trans hneg habs
  -- The infimum Rayleigh value bounds every nonzero vector from below.
  calc
    lambdaMin ≤ s := hs_ge
    _ ≤ inner ℝ (Tlin u) u / ‖u‖ ^ 2 := by
      exact ciInf_le hs_bdd ⟨u, hu⟩

/-- Helper for Chapter01 Definition 1.2.3: any greatest positive-definite eigenvalue is an upper
bound for the Euclidean Rayleigh quotient of `A`. -/
lemma euclideanRayleighQuotient_le_greatestPosDefEigenvalue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (lambdaMax : ℝ)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues A hA)) lambdaMax) :
    ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 →
      inner ℝ (A.toEuclideanLin u) u / ‖u‖ ^ 2 ≤ lambdaMax := by
  intro u hu
  let Tlin := A.toEuclideanLin
  let T := Tlin.toContinuousLinearMap
  have hSymm : Tlin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  -- The maximizing Rayleigh quotient of the symmetric Euclidean operator is an eigenvalue.
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := ⟨⟨u, 0, hu⟩⟩
  let s : ℝ := ⨆ x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 },
    inner ℝ (Tlin x) x / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2
  have hs_eigen : Module.End.HasEigenvalue Tlin s := by
    simpa [s, Tlin] using LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional hSymm
  have hs_spec : s ∈ spectrum ℝ A := by
    rw [← Matrix.spectrum_toLpLin (p := 2)]
    exact hs_eigen.mem_spectrum
  have hs_mem_range : s ∈ Set.range (posDefEigenvalues A hA) := by
    rw [hA.isHermitian.spectrum_eq_image_range] at hs_spec
    simpa [posDefEigenvalues_def] using hs_spec
  have hs_le : s ≤ lambdaMax := hLambdaMax.2 hs_mem_range
  have hs_bdd :
      BddAbove (Set.range fun x : { x : EuclideanSpace ℝ (Fin n) // x ≠ 0 } ↦
        inner ℝ (Tlin x) x / ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    -- A Rayleigh quotient is bounded above by the operator norm.
    refine ⟨‖T‖, ?_⟩
    rintro y ⟨x, rfl⟩
    simpa [T, Tlin, ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply] using
      le_trans (le_abs_self (T.rayleighQuotient x)) (T.rayleighQuotient_le_norm x)
  -- The supremum Rayleigh value bounds every nonzero vector from above.
  calc
    inner ℝ (Tlin u) u / ‖u‖ ^ 2 ≤ s := by
      exact le_ciSup hs_bdd ⟨u, hu⟩
    _ ≤ lambdaMax := hs_le

/-- Helper for Chapter01 Definition 1.2.3: the Euclidean matrix action computes the quadratic form
`xᵀ A x` on coordinate vectors. -/
lemma toEuclideanLin_inner_eq_dotProduct_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    inner ℝ (A.toEuclideanLin (WithLp.toLp 2 x)) (WithLp.toLp 2 x) = x ⬝ᵥ (A *ᵥ x) := by
  -- Rewrite `toEuclideanLin` through the owner-level continuous linear map and evaluate its inner
  -- product formula on the same Euclidean vector twice.
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  simpa [real_inner_comm] using Matrix.inner_toEuclideanCLM A (WithLp.toLp 2 x) (WithLp.toLp 2 x)

/-- Helper for Chapter01 Definition 1.2.3: the Euclidean inner product on `WithLp 2` coordinate
vectors is the usual dot product. -/
lemma toLpInner_eq_dotProduct {n : ℕ} (u v : Fin n → ℝ) :
    inner ℝ (WithLp.toLp (2 : ENNReal) u) (WithLp.toLp (2 : ENNReal) v) = u ⬝ᵥ v := by
  -- Rewrite the Euclidean `WithLp` inner product to the coordinate dot product once.
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct_comm]

/-- Helper for Chapter01 Definition 1.2.3: the matrix `ℓ₂` operator norm is the operator norm of
the associated Euclidean continuous linear map. -/
lemma matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖₂ =
      ‖((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) (n := Fin n)).trans
          LinearMap.toContinuousLinearMap) A‖ := by
  -- Keep the public theorem bodies in the bundled continuous-linear-map spelling.
  simpa [matrixL2OperatorNorm] using (Matrix.l2_opNorm_def A)

/-- Helper for Chapter01 Definition 1.2.3: the Frobenius norm is the square root of the sum of
the squared Euclidean column norms. -/
lemma matrixFrobeniusNorm_eq_sqrt_sum_columnVectorTwoNorm_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖_F = Real.sqrt (∑ j : Fin n, ‖A.col j‖₂ ^ 2) := by
  have hcols :
      ∑ j : Fin n, ‖A.col j‖₂ ^ 2 = ∑ j : Fin n, ∑ i : Fin m, ‖A i j‖ ^ (2 : ℝ) := by
    -- Square each column `ℓ₂` norm once, then rewrite it to the coordinate square sum.
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [l2Norm_eq_sqrt_sum_sq]
    calc
      (Real.sqrt (∑ i : Fin m, |A.col j i| ^ 2)) ^ 2 = ∑ i : Fin m, |A.col j i| ^ 2 := by
        exact Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ by positivity)
      _ = ∑ i : Fin m, ‖A i j‖ ^ (2 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [Matrix.col_apply, Real.norm_eq_abs]
  have hFrob :
      ‖A‖_F = (∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    -- Expand the owner-level Frobenius formula before commuting the finite sums.
    simpa [matrixFrobeniusNorm] using (Matrix.frobenius_norm_def A)
  rw [hFrob, ← Real.sqrt_eq_rpow, Finset.sum_comm]
  exact congrArg Real.sqrt hcols.symm

/-- Helper for Chapter01 Definition 1.2.3: the Frobenius norm square is the sum of the column
`ℓ₂` norm squares. -/
lemma matrixFrobeniusNorm_sq_eq_sum_columnVectorTwoNorm_sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖_F ^ 2 = ∑ j : Fin n, ‖A.col j‖₂ ^ 2 := by
  -- First move to the stable square-root normal form, then square both sides once.
  rw [matrixFrobeniusNorm_eq_sqrt_sum_columnVectorTwoNorm_sq]
  simpa [pow_two] using
    (Real.sq_sqrt (Finset.sum_nonneg fun j _ ↦ sq_nonneg ‖A.col j‖₂))

/-- Helper for Chapter01 Definition 1.2.3: each row has `ℓ₁` norm at most `sqrt n * ‖A‖₂`. -/
lemma rowVectorOneNorm_le_sqrt_cols_mul_matrixL2OperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    ‖fun j : Fin n => A i j‖₁ ≤ Real.sqrt (n : ℝ) * ‖A‖₂ := by
  have hRowTwo : ‖A.row i‖₂ ≤ ‖A‖₂ := by
    -- Rewrite the row as a transpose column so the existing column estimate applies directly.
    simpa [Matrix.col_transpose] using
      (columnVectorTwoNorm_le_matrixL2OperatorNorm (A := Aᵀ) i).trans_eq
        (Matrix.l2_opNorm_conjTranspose A)
  -- Compare the row `ℓ₁` norm to its `ℓ₂` norm, then transport the `ℓ₂` bound from the
  -- transpose column estimate.
  calc
    ‖fun j : Fin n => A i j‖₁ = ‖A.row i‖₁ := by rfl
    _ ≤ Real.sqrt (n : ℝ) * ‖A.row i‖₂ := vectorOneNorm_le_sqrt_mul_vectorTwoNorm (A.row i)
    _ ≤ Real.sqrt (n : ℝ) * ‖A‖₂ := by gcongr

/-- Helper for Chapter01 Definition 1.2.3: a rowwise `ℓ₁` bound controls the matrix `ℓ∞` norm on
the public surface. -/
lemma matrixInfinityNorm_le_of_rowVectorOneNorm_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i, ‖A.row i‖₁ ≤ C) :
    ‖A‖∞ ≤ C := by
  -- Package the owner-level row-sup formula once so later theorem bodies stay on the public norm
  -- surface.
  unfold matrixInfinityNorm
  rw [Matrix.linfty_opNorm_def]
  have hnn : (Finset.univ.sup fun i : Fin m => ∑ j : Fin n, ‖A i j‖₊) ≤ ⟨C, hC⟩ := by
    refine Finset.sup_le ?_
    intro i _
    -- Convert the row `ℓ₁` hypothesis to the `ℝ≥0` row-sum presentation used by the owner API.
    have hi : (((∑ j : Fin n, ‖A i j‖₊) : NNReal) : ℝ) ≤ C := by
      simpa [l1Norm_eq_sum_abs, Matrix.row_apply] using hrow i
    exact_mod_cast hi
  exact_mod_cast hnn

/-- Helper for Chapter01 Definition 1.2.3: each column is bounded by `sqrt m` times the maximum
entry norm. -/
lemma columnVectorTwoNorm_le_sqrt_rows_mul_matrixMaxEntryNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    ‖A.col j‖₂ ≤ Real.sqrt (m : ℝ) * matrixMaxEntryNorm A := by
  have hmaxnonneg : 0 ≤ matrixMaxEntryNorm A := by
    -- The elementwise matrix norm is a supremum norm, so it is manifestly nonnegative.
    unfold matrixMaxEntryNorm
    rw [Matrix.norm_def]
    exact norm_nonneg _
  calc
    ‖A.col j‖₂ ≤ Real.sqrt (m : ℝ) * ‖A.col j‖∞ := by
      -- First move from the Euclidean column norm to the column sup norm.
      exact vectorTwoNorm_le_sqrt_mul_vectorInfNorm (A.col j)
    _ ≤ Real.sqrt (m : ℝ) * matrixMaxEntryNorm A := by
      -- Then each column entry is bounded by the elementwise matrix supremum norm.
      gcongr
      rw [linftyNorm_eq_iSup_abs]
      refine Real.iSup_le ?_ hmaxnonneg
      intro i
      simpa [matrixMaxEntryNorm, Matrix.col_apply, Real.norm_eq_abs] using
        (Matrix.norm_entry_le_entrywise_sup_norm (A := A) (i := i) (j := j))

/-- Helper for Chapter01 Definition 1.2.3: the Frobenius norm is bounded by `sqrt (m n)` times the
maximum entry norm. -/
lemma matrixFrobeniusNorm_le_sqrt_mul_matrixMaxEntryNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖_F ≤ Real.sqrt ((m * n : ℕ) : ℝ) * matrixMaxEntryNorm A := by
  have hFnonneg : 0 ≤ ‖A‖_F := by
    -- Keep the Frobenius side on the stable square-root column formula.
    rw [matrixFrobeniusNorm_eq_sqrt_sum_columnVectorTwoNorm_sq]
    exact Real.sqrt_nonneg _
  have hmaxnonneg : 0 ≤ matrixMaxEntryNorm A := by
    -- The public max-entry norm is the elementwise supremum norm.
    unfold matrixMaxEntryNorm
    rw [Matrix.norm_def]
    exact norm_nonneg _
  refine (sq_le_sq₀ hFnonneg (mul_nonneg (Real.sqrt_nonneg _) hmaxnonneg)).1 ?_
  rw [matrixFrobeniusNorm_sq_eq_sum_columnVectorTwoNorm_sq, pow_two]
  have hsqrtm : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := by
    rw [Real.sq_sqrt (show 0 ≤ (m : ℝ) by positivity)]
  have hsqrtmn : Real.sqrt ((m * n : ℕ) : ℝ) ^ 2 = ((m * n : ℕ) : ℝ) := by
    rw [Real.sq_sqrt (show 0 ≤ ((m * n : ℕ) : ℝ) by positivity)]
  have hmn : (((m * n : ℕ) : ℝ)) = (m : ℝ) * (n : ℝ) := by
    exact_mod_cast Nat.cast_mul m n
  calc
    ∑ j : Fin n, ‖A.col j‖₂ ^ 2 ≤
        ∑ j : Fin n, (Real.sqrt (m : ℝ) * matrixMaxEntryNorm A) ^ 2 := by
      -- Bound each column square by the column-level max-entry estimate.
      refine Finset.sum_le_sum ?_
      intro j _
      exact
        (sq_le_sq₀ (l2Norm_isVectorNorm.nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hmaxnonneg)).2
          (columnVectorTwoNorm_le_sqrt_rows_mul_matrixMaxEntryNorm A j)
    _ = (n : ℝ) * (Real.sqrt (m : ℝ) * matrixMaxEntryNorm A) ^ 2 := by
      simp [Finset.card_univ]
    _ = Real.sqrt ((m * n : ℕ) : ℝ) * matrixMaxEntryNorm A *
          (Real.sqrt ((m * n : ℕ) : ℝ) * matrixMaxEntryNorm A) := by
      -- Expand both sides to the common scalar `m * n * matrixMaxEntryNorm A ^ 2`.
      calc
        (n : ℝ) * (Real.sqrt (m : ℝ) * matrixMaxEntryNorm A) ^ 2
            = (n : ℝ) * (Real.sqrt (m : ℝ) ^ 2) * matrixMaxEntryNorm A ^ 2 := by
                ring
        _ = (n : ℝ) * (m : ℝ) * matrixMaxEntryNorm A ^ 2 := by rw [hsqrtm]
        _ = ((m * n : ℕ) : ℝ) * matrixMaxEntryNorm A ^ 2 := by rw [hmn]; ring
        _ = Real.sqrt ((m * n : ℕ) : ℝ) ^ 2 * matrixMaxEntryNorm A ^ 2 := by rw [hsqrtmn]
        _ = Real.sqrt ((m * n : ℕ) : ℝ) * matrixMaxEntryNorm A *
              (Real.sqrt ((m * n : ℕ) : ℝ) * matrixMaxEntryNorm A) := by
                ring

end

/-- Chapter01 Definition 1.2.3: clause (8), the lower spectral-eigenvalue bound
for the positive-definite `A`-norm. -/
theorem sqrt_lambdaMin_mul_vectorTwoNorm_le_matrixInducedVectorNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (lambdaMin : ℝ)
    (hLambdaMin : IsLeast (Set.range (posDefEigenvalues A hA)) lambdaMin)
    (x : Fin n → ℝ) :
    Real.sqrt lambdaMin * ‖x‖₂ ≤
      ellipsoidNorm A x := by
  by_cases hx : x = 0
  · -- The zero vector makes both norm sides vanish.
    subst hx
    simp [ellipsoidNorm, l2Norm, lpNorm]
  · have hux : WithLp.toLp (2 : ENNReal) x ≠ 0 := by
      -- The nonzero coordinate vector stays nonzero in the Euclidean `WithLp 2` model.
      exact fun h => hx ((WithLp.toLp_eq_zero (p := (2 : ENNReal)) (x := x)).1 h)
    have hRay :=
      leastPosDefEigenvalue_le_euclideanRayleighQuotient A hA lambdaMin hLambdaMin
        (WithLp.toLp (2 : ENNReal) x) hux
    change lambdaMin ≤ inner ℝ (WithLp.toLp 2 (A *ᵥ x)) (WithLp.toLp 2 x) /
        ‖WithLp.toLp 2 x‖ ^ 2 at hRay
    rw [toLpInner_eq_dotProduct] at hRay
    have hRay' : lambdaMin ≤ (x ⬝ᵥ (A *ᵥ x)) / ‖x‖₂ ^ 2 := by
      -- Transport the Rayleigh quotient back to the public quadratic-form surface.
      simpa [l2Norm, lpNorm, dotProduct_comm] using hRay
    rcases hLambdaMin.1 with ⟨i, hi⟩
    have hlambda_pos : 0 < lambdaMin := by
      -- The least positive-definite eigenvalue is still positive.
      rw [← hi]
      exact hA.eigenvalues_pos i
    have hxnorm_pos : 0 < ‖x‖₂ := by
      have hxnorm_ne : ‖x‖₂ ≠ 0 := by
        exact fun h => hx ((l2Norm_isVectorNorm.eq_zero_iff x).1 h)
      exact lt_of_le_of_ne (l2Norm_isVectorNorm.nonneg x) (Ne.symm hxnorm_ne)
    have hquad : lambdaMin * ‖x‖₂ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) := by
      -- Clear the positive denominator of the Rayleigh quotient inequality.
      exact (le_div_iff₀ (pow_pos hxnorm_pos 2)).mp hRay'
    have hq_nonneg : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
      exact le_trans (mul_nonneg hlambda_pos.le (sq_nonneg ‖x‖₂)) hquad
    rw [ellipsoidNorm_eq_sqrt_dotProduct_mulVec]
    refine
      (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (l2Norm_isVectorNorm.nonneg x))
        (Real.sqrt_nonneg _)).1 ?_
    calc
      (Real.sqrt lambdaMin * ‖x‖₂) ^ 2 = lambdaMin * ‖x‖₂ ^ 2 := by
        -- Square the left side once and rewrite `sqrt lambdaMin`.
        rw [pow_two]
        nlinarith [Real.sq_sqrt hlambda_pos.le]
      _ ≤ x ⬝ᵥ (A *ᵥ x) := hquad
      _ = (Real.sqrt (x ⬝ᵥ (A *ᵥ x))) ^ 2 := by
        symm
        exact Real.sq_sqrt hq_nonneg

/-- For Chapter01 Definition 1.2.3 (9): the upper spectral-eigenvalue bound
for the positive-definite `A`-norm. -/
theorem matrixInducedVectorNorm_le_sqrt_lambdaMax_mul_vectorTwoNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (lambdaMax : ℝ)
    (hLambdaMax : IsGreatest (Set.range (posDefEigenvalues A hA)) lambdaMax)
    (x : Fin n → ℝ) :
    ellipsoidNorm A x ≤
      Real.sqrt lambdaMax * ‖x‖₂ := by
  by_cases hx : x = 0
  · -- The zero vector makes both norm sides vanish.
    subst hx
    simp [ellipsoidNorm, l2Norm, lpNorm]
  · have hux : WithLp.toLp (2 : ENNReal) x ≠ 0 := by
      -- The nonzero coordinate vector stays nonzero in the Euclidean `WithLp 2` model.
      exact fun h => hx ((WithLp.toLp_eq_zero (p := (2 : ENNReal)) (x := x)).1 h)
    have hRay :=
      euclideanRayleighQuotient_le_greatestPosDefEigenvalue A hA lambdaMax hLambdaMax
        (WithLp.toLp (2 : ENNReal) x) hux
    change inner ℝ (WithLp.toLp 2 (A *ᵥ x)) (WithLp.toLp 2 x) /
        ‖WithLp.toLp 2 x‖ ^ 2 ≤ lambdaMax at hRay
    rw [toLpInner_eq_dotProduct] at hRay
    have hRay' : (x ⬝ᵥ (A *ᵥ x)) / ‖x‖₂ ^ 2 ≤ lambdaMax := by
      -- Transport the Rayleigh quotient back to the public quadratic-form surface.
      simpa [l2Norm, lpNorm, dotProduct_comm] using hRay
    rcases hLambdaMax.1 with ⟨i, hi⟩
    have hlambda_pos : 0 < lambdaMax := by
      -- The greatest positive-definite eigenvalue is still positive.
      rw [← hi]
      exact hA.eigenvalues_pos i
    have hxnorm_pos : 0 < ‖x‖₂ := by
      have hxnorm_ne : ‖x‖₂ ≠ 0 := by
        exact fun h => hx ((l2Norm_isVectorNorm.eq_zero_iff x).1 h)
      exact lt_of_le_of_ne (l2Norm_isVectorNorm.nonneg x) (Ne.symm hxnorm_ne)
    have hquad : x ⬝ᵥ (A *ᵥ x) ≤ lambdaMax * ‖x‖₂ ^ 2 := by
      -- Clear the positive denominator of the Rayleigh quotient inequality.
      exact (div_le_iff₀ (pow_pos hxnorm_pos 2)).mp hRay'
    have hq_nonneg : 0 ≤ x ⬝ᵥ (A *ᵥ x) := (hA.dotProduct_mulVec_pos hx).le
    rw [ellipsoidNorm_eq_sqrt_dotProduct_mulVec]
    refine
      (sq_le_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (l2Norm_isVectorNorm.nonneg x))).1 ?_
    calc
      (Real.sqrt (x ⬝ᵥ (A *ᵥ x))) ^ 2 = x ⬝ᵥ (A *ᵥ x) := by
        -- Square the ellipsoid-norm side once.
        exact Real.sq_sqrt hq_nonneg
      _ ≤ lambdaMax * ‖x‖₂ ^ 2 := hquad
      _ = (Real.sqrt lambdaMax * ‖x‖₂) ^ 2 := by
        -- Square the right side once and rewrite `sqrt lambdaMax`.
        rw [pow_two]
        nlinarith [Real.sq_sqrt hlambda_pos.le]

/-- For Chapter01 Definition 1.2.3 (10): the source inequality `‖A‖₂ ≤ ‖A‖_F` for real matrices. -/
theorem matrixL2OperatorNorm_le_matrixFrobeniusNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖₂ ≤ ‖A‖_F := by
  have hFnonneg : 0 ≤ ‖A‖_F := by
    rw [matrixFrobeniusNorm_eq_sqrt_sum_columnVectorTwoNorm_sq]
    exact Real.sqrt_nonneg _
  rw [matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ hFnonneg ?_
  intro x
  -- Evaluate the operator norm bound on an arbitrary Euclidean vector and transport to `mulVec`.
  change ‖WithLp.toLp 2 (A *ᵥ x.ofLp)‖ ≤ ‖A‖_F * ‖x‖
  simpa [l2Norm, lpNorm] using
    (matrixMulVecTwoNorm_le_matrixFrobeniusNorm_mul_vectorTwoNorm A x.ofLp)

/-- For Chapter01 Definition 1.2.3 (11): the source inequality `‖A‖_F ≤ sqrt n * ‖A‖₂` for real
`m × n` matrices. -/
theorem matrixFrobeniusNorm_le_sqrt_cols_mul_matrixL2OperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖_F ≤ Real.sqrt (n : ℝ) * ‖A‖₂ := by
  have hFnonneg : 0 ≤ ‖A‖_F := by
    rw [matrixFrobeniusNorm_eq_sqrt_sum_columnVectorTwoNorm_sq]
    exact Real.sqrt_nonneg _
  have hOpnonneg : 0 ≤ ‖A‖₂ := by
    rw [matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm]
    exact norm_nonneg _
  refine (sq_le_sq₀ hFnonneg (mul_nonneg (Real.sqrt_nonneg _) hOpnonneg)).1 ?_
  rw [matrixFrobeniusNorm_sq_eq_sum_columnVectorTwoNorm_sq, pow_two]
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := by
    rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  calc
    ∑ j : Fin n, ‖A.col j‖₂ ^ 2 ≤ ∑ j : Fin n, ‖A‖₂ ^ 2 := by
      -- Bound each column square by the operator norm square.
      refine Finset.sum_le_sum ?_
      intro j _
      exact (sq_le_sq₀ (l2Norm_isVectorNorm.nonneg _) hOpnonneg).2
        (columnVectorTwoNorm_le_matrixL2OperatorNorm A j)
    _ = (n : ℝ) * ‖A‖₂ ^ 2 := by simp [pow_two, Finset.card_univ]
    _ = Real.sqrt (n : ℝ) * ‖A‖₂ * (Real.sqrt (n : ℝ) * ‖A‖₂) := by
      nlinarith [hsqrt]

/-- For Chapter01 Definition 1.2.3 (12): the maximum entry norm is bounded above by the matrix `ℓ₂`
operator norm. -/
theorem matrixMaxEntryNorm_le_matrixL2OperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixMaxEntryNorm A ≤ ‖A‖₂ := by
  have hOpnonneg : 0 ≤ ‖A‖₂ := by
    rw [matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm]
    exact norm_nonneg _
  unfold matrixMaxEntryNorm
  refine (Matrix.norm_le_iff hOpnonneg).2 ?_
  intro i j
  have hEntry : ‖A i j‖ ≤ ‖A.col j‖₂ := by
    -- Each entry is bounded by the Euclidean norm of its column.
    simpa [l2Norm, lpNorm, Matrix.col_apply] using
      (PiLp.norm_apply_le (x := WithLp.toLp (2 : ENNReal) (A.col j)) i)
  exact hEntry.trans (columnVectorTwoNorm_le_matrixL2OperatorNorm A j)

/-- For Chapter01 Definition 1.2.3 (13): the matrix `ℓ₂` operator norm is bounded by `sqrt (m n)`
times the maximum entry norm. -/
theorem matrixL2OperatorNorm_le_sqrt_mul_matrixMaxEntryNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖₂ ≤
      Real.sqrt ((m * n : ℕ) : ℝ) * matrixMaxEntryNorm A := by
  -- Route through the Frobenius norm, which is already controlled by the maximal entry norm.
  exact (matrixL2OperatorNorm_le_matrixFrobeniusNorm A).trans
    (matrixFrobeniusNorm_le_sqrt_mul_matrixMaxEntryNorm A)

/-- For Chapter01 Definition 1.2.3 (14): the source lower bound `(1 / sqrt n) * ‖A‖∞ ≤ ‖A‖₂`. -/
theorem one_div_sqrt_cols_mul_matrixInfinityNorm_le_matrixL2OperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (1 / Real.sqrt (n : ℝ)) * ‖A‖∞ ≤ ‖A‖₂ := by
  have hOpnonneg : 0 ≤ ‖A‖₂ := by
    rw [matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm]
    exact norm_nonneg _
  have hrows : ∀ i : Fin m, ‖A.row i‖₁ ≤ Real.sqrt (n : ℝ) * ‖A‖₂ := by
    intro i
    exact rowVectorOneNorm_le_sqrt_cols_mul_matrixL2OperatorNorm A i
  have hinf : ‖A‖∞ ≤ Real.sqrt (n : ℝ) * ‖A‖₂ := by
    -- First prove the stronger undivided row-sum bound on `‖A‖∞`.
    exact matrixInfinityNorm_le_of_rowVectorOneNorm_le A _
      (mul_nonneg (Real.sqrt_nonneg _) hOpnonneg) hrows
  by_cases hn : n = 0
  · -- In the zero-column case the left side vanishes.
    subst hn
    simpa only [CharP.cast_eq_zero, Real.sqrt_zero, div_zero, zero_mul, ge_iff_le] using hOpnonneg
  · have hs : Real.sqrt (n : ℝ) ≠ 0 := by
      exact Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (Nat.pos_iff_ne_zero.mpr hn))
    calc
      (1 / Real.sqrt (n : ℝ)) * ‖A‖∞ ≤
          (1 / Real.sqrt (n : ℝ)) * (Real.sqrt (n : ℝ) * ‖A‖₂) := by
            gcongr
      _ = ‖A‖₂ := by
        field_simp [hs]

/-- For Chapter01 Definition 1.2.3 (15): the source upper bound `‖A‖₂ ≤ sqrt m * ‖A‖∞`. -/
theorem matrixL2OperatorNorm_le_sqrt_rows_mul_matrixInfinityNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖₂ ≤ Real.sqrt (m : ℝ) * ‖A‖∞ := by
  have hInftyNonneg : 0 ≤ ‖A‖∞ := by
    -- Unfold the owner formula once to record nonnegativity on the public surface.
    unfold matrixInfinityNorm
    rw [Matrix.linfty_opNorm_def]
    exact_mod_cast
      (show (0 : NNReal) ≤ Finset.univ.sup fun i : Fin m => ∑ j : Fin n, ‖A i j‖₊ by
        exact bot_le)
  rw [matrixL2OperatorNorm_eq_rectangularEuclideanOpNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hInftyNonneg) ?_
  intro x
  change ‖A.toEuclideanLin x‖ ≤ Real.sqrt (m : ℝ) * ‖A‖∞ * ‖x‖
  change ‖WithLp.toLp 2 (A *ᵥ x.ofLp)‖ ≤ Real.sqrt (m : ℝ) * ‖A‖∞ * ‖x‖
  calc
    ‖A *ᵥ x.ofLp‖₂ ≤ Real.sqrt (m : ℝ) * ‖A *ᵥ x.ofLp‖∞ := by
      -- Compare the image vector's Euclidean norm to its sup norm.
      exact vectorTwoNorm_le_sqrt_mul_vectorInfNorm (A *ᵥ x.ofLp)
    _ ≤ Real.sqrt (m : ℝ) * (‖A‖∞ * ‖x.ofLp‖∞) := by
      -- Then bound the image sup norm by the matrix `ℓ∞` norm times the input sup norm.
      gcongr
      simpa [matrixInfinityNorm, linftyNorm, lpNorm] using (Matrix.linfty_opNorm_mulVec A x.ofLp)
    _ ≤ Real.sqrt (m : ℝ) * (‖A‖∞ * ‖x.ofLp‖₂) := by
      -- Finally compare the input sup norm to its Euclidean norm.
      gcongr
      exact vectorInfNorm_le_vectorTwoNorm x.ofLp
    _ = Real.sqrt (m : ℝ) * ‖A‖∞ * ‖x‖ := by
      simp [l2Norm, lpNorm, mul_assoc, mul_left_comm, mul_comm]

/-- For Chapter01 Definition 1.2.3 (16): the source lower bound `(1 / sqrt m) * ‖A‖₁ ≤ ‖A‖₂`. -/
theorem one_div_sqrt_rows_mul_matrixOneNorm_le_matrixL2OperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (1 / Real.sqrt (m : ℝ)) * ‖A‖₁ ≤ ‖A‖₂ := by
  have hTranspose :
      (1 / Real.sqrt (m : ℝ)) * ‖Aᵀ‖∞ ≤ ‖Aᵀ‖₂ :=
    one_div_sqrt_cols_mul_matrixInfinityNorm_le_matrixL2OperatorNorm Aᵀ
  have hOpTranspose : ‖Aᵀ‖₂ = ‖A‖₂ := by
    simpa using Matrix.l2_opNorm_conjTranspose A
  -- Reduce the `ℓ₁` statement to the transpose `ℓ∞` statement.
  simpa [matrixOneNorm_eq_matrixInfinityNorm_transpose, hOpTranspose] using hTranspose

/-- For Chapter01 Definition 1.2.3 (17): the source upper bound `‖A‖₂ ≤ sqrt n * ‖A‖₁`. -/
theorem matrixL2OperatorNorm_le_sqrt_cols_mul_matrixOneNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖₂ ≤ Real.sqrt (n : ℝ) * ‖A‖₁ := by
  have hTranspose : ‖Aᵀ‖₂ ≤ Real.sqrt (n : ℝ) * ‖Aᵀ‖∞ :=
    matrixL2OperatorNorm_le_sqrt_rows_mul_matrixInfinityNorm Aᵀ
  have hOpTranspose : ‖Aᵀ‖₂ = ‖A‖₂ := by
    simpa using Matrix.l2_opNorm_conjTranspose A
  -- Reduce the `ℓ₁` statement to the transpose `ℓ∞` statement.
  simpa [matrixOneNorm_eq_matrixInfinityNorm_transpose, hOpTranspose] using hTranspose

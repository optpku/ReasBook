/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Definition_1_3.Tikhonov
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_12.Operator
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_2.Discrepancy
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Order.IntermediateValue

public section

noncomputable section

open Filter
open scoped BigOperators Matrix Topology

universe u v

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]

/-- Helper for Remark 1.2-extra-3: applying `Matrix.toEuclideanLin` twice is the
same as applying the product matrix once. -/
theorem toEuclideanLin_mul_apply
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) (x : EuclideanSpace ℝ m) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) =
      Matrix.toEuclideanLin (A * B) x := by
  -- Move both sides to coordinate functions so the statement is just `mulVec_mulVec`.
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

/-- Helper for Remark 1.2-extra-3: `Kᵀ * K + α I` is positive definite for
every positive Tikhonov parameter `α`. -/
theorem gramianShift_posDef
    (K : Matrix m n ℝ) (α : ℝ) (hα_pos : 0 < α) :
    (Kᵀ * K + α • (1 : Matrix n n ℝ)).PosDef := by
  -- Combine the positive semidefinite Gramian with the positive definite scalar shift.
  have hgram : (Kᵀ * K).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self K
  have hshift : (α • (1 : Matrix n n ℝ)).PosDef := Matrix.PosDef.smul Matrix.PosDef.one hα_pos
  simpa [add_comm] using hshift.add_posSemidef hgram

/-- Helper for Remark 1.2-extra-3: the singular Gramian branch forces the
zero-parameter reconstruction to vanish because `nonsing_inv` collapses to `0`. -/
theorem reconstruction_zero_of_not_isUnit_gramian
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (hgram_not_unit : ¬ IsUnit ((Kᵀ * K).det)) :
    Tikhonov.reconstruction K 0 d = 0 := by
  -- At `α = 0`, the reconstruction matrix is `(Kᵀ K)⁻¹ Kᵀ`, so a singular
  -- Gramian makes the inverse matrix vanish.
  rw [Tikhonov.reconstruction_eq]
  have hzeroInv : (Kᵀ * K)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hgram_not_unit
  simp [hzeroInv]

/-- Helper for Remark 1.2-extra-3: an invertible square matrix acts injectively on
`EuclideanSpace` through `Matrix.toEuclideanLin`. -/
theorem eq_zero_of_toEuclideanLin_eq_zero
    (A : Matrix n n ℝ) (hA_det : IsUnit A.det) {x : EuclideanSpace ℝ n}
    (hx : A.toEuclideanLin x = 0) :
    x = 0 := by
  -- Apply the inverse matrix on the left to transport the zero equation back to the vector.
  calc
    x = Matrix.toEuclideanLin (1 : Matrix n n ℝ) x := by simp
    _ = Matrix.toEuclideanLin (A⁻¹ * A) x := by
      rw [← Matrix.nonsing_inv_mul A hA_det]
    _ = Matrix.toEuclideanLin A⁻¹ (A.toEuclideanLin x) := by
      rw [toEuclideanLin_mul_apply]
    _ = 0 := by simp [hx]

/-- Helper for Remark 1.2-extra-3: the Tikhonov reconstruction solves the shifted
normal equation `(Kᵀ * K + α I) f_α = Kᵀ d`. -/
theorem tikhonovNormalEquation
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ)
    (hA_det : IsUnit ((Kᵀ * K + α • (1 : Matrix n n ℝ)).det)) :
    (Kᵀ * K + α • (1 : Matrix n n ℝ)).toEuclideanLin
      (Tikhonov.reconstruction K α d) =
        (Kᵀ).toEuclideanLin d := by
  -- Apply the shifted Gramian to the explicit reconstruction formula and cancel the inverse.
  rw [Tikhonov.reconstruction_eq]
  calc
    (Kᵀ * K + α • (1 : Matrix n n ℝ)).toEuclideanLin
        (((Kᵀ * K + α • (1 : Matrix n n ℝ))⁻¹ * Kᵀ).toEuclideanLin d)
        = ((Kᵀ * K + α • (1 : Matrix n n ℝ)) *
            ((Kᵀ * K + α • (1 : Matrix n n ℝ))⁻¹ * Kᵀ)).toEuclideanLin d := by
              simpa using
                toEuclideanLin_mul_apply
                  (Kᵀ * K + α • (1 : Matrix n n ℝ))
                  (((Kᵀ * K + α • (1 : Matrix n n ℝ))⁻¹ * Kᵀ)) d
    _ = (Kᵀ).toEuclideanLin d := by
          rw [Matrix.mul_nonsing_inv_cancel_left
            (Kᵀ * K + α • (1 : Matrix n n ℝ)) Kᵀ hA_det]

/-- Helper for Remark 1.2-extra-3: applying `K` to the Tikhonov normal
equation gives the corresponding shifted equation for the predicted data
`K f_α`. -/
theorem tikhonovDataNormalEquation
    (K : Matrix n n ℝ) (d : EuclideanSpace ℝ n) (α : ℝ)
    (hA_det : IsUnit ((Kᵀ * K + α • (1 : Matrix n n ℝ)).det)) :
    (K * Kᵀ + α • (1 : Matrix n n ℝ)).toEuclideanLin
      (K.toEuclideanLin (Tikhonov.reconstruction K α d)) =
        (K * Kᵀ).toEuclideanLin d := by
  have hComm :
      (K * Kᵀ + α • (1 : Matrix n n ℝ)) * K =
        K * (Kᵀ * K + α • (1 : Matrix n n ℝ)) := by
    -- Reassociate the two matrix products so `K` sits on the outside.
    calc
      (K * Kᵀ + α • (1 : Matrix n n ℝ)) * K
          = (K * Kᵀ) * K + (α • (1 : Matrix n n ℝ)) * K := by
              rw [Matrix.add_mul]
      _ = K * (Kᵀ * K) + α • K := by
            simp [Matrix.mul_assoc]
      _ = K * (Kᵀ * K) + K * (α • (1 : Matrix n n ℝ)) := by
            simp
      _ = K * (Kᵀ * K + α • (1 : Matrix n n ℝ)) := by
            rw [Matrix.mul_add]
  -- Push `K` across the domain normal equation to move from solution space to data space.
  calc
    (K * Kᵀ + α • (1 : Matrix n n ℝ)).toEuclideanLin
        (K.toEuclideanLin (Tikhonov.reconstruction K α d))
        = Matrix.toEuclideanLin
            (((K * Kᵀ + α • (1 : Matrix n n ℝ)) * K))
            (Tikhonov.reconstruction K α d) := by
              simpa using
                (toEuclideanLin_mul_apply
                  (K * Kᵀ + α • (1 : Matrix n n ℝ))
                  K
                  (Tikhonov.reconstruction K α d))
    _ = Matrix.toEuclideanLin
          (K * (Kᵀ * K + α • (1 : Matrix n n ℝ)))
          (Tikhonov.reconstruction K α d) := by
            rw [hComm]
    _ = K.toEuclideanLin
          ((Kᵀ * K + α • (1 : Matrix n n ℝ)).toEuclideanLin
            (Tikhonov.reconstruction K α d)) := by
            rw [toEuclideanLin_mul_apply]
    _ = K.toEuclideanLin ((Kᵀ).toEuclideanLin d) := by
          rw [tikhonovNormalEquation K d α hA_det]
    _ = (K * Kᵀ).toEuclideanLin d := by
          rw [toEuclideanLin_mul_apply]

/-- Helper for Remark 1.2-extra-3: in SVD coordinates, the data-space Gramian
`K Kᵀ` diagonalizes with eigenvalues `s i ^ 2`. -/
theorem dataGramian_eq_orthogonalDiagonal
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    K * Kᵀ = U * Matrix.diagonal (fun i => s i ^ 2) * Uᵀ := by
  have hVtV : Vᵀ * V = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := V)).1 hV
  have hDiagSq :
      Matrix.diagonal s * Matrix.diagonal s = Matrix.diagonal (fun i => s i ^ 2) := by
    -- Two diagonal matrices multiply by multiplying their diagonal entries.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [pow_two]
    · simp [hij]
  -- Expand the SVD of `K` and cancel the right singular basis.
  calc
    K * Kᵀ = (U * Matrix.diagonal s * Vᵀ) * (U * Matrix.diagonal s * Vᵀ)ᵀ := by
      rw [hK]
    _ = (U * Matrix.diagonal s * Vᵀ) * (V * Matrix.diagonal s * Uᵀ) := by
      simpa [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.transpose_transpose,
        Matrix.mul_assoc]
    _ = ((U * Matrix.diagonal s) * (Vᵀ * V) * Matrix.diagonal s) * Uᵀ := by
      simp [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal s * (Vᵀ * V) * Matrix.diagonal s) * Uᵀ := by
      simp [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal s * Matrix.diagonal s) * Uᵀ := by
      rw [hVtV]
      simp [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i => s i ^ 2) * Uᵀ := by
      rw [hDiagSq]

/-- Helper for Remark 1.2-extra-3: the shifted data-space Gramian keeps the
same singular basis, and only the diagonal entries change to `s i ^ 2 + α`. -/
theorem shiftedDataGramian_eq_orthogonalDiagonal
    (K U V : Matrix n n ℝ) (s : n → ℝ) (α : ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    K * Kᵀ + α • (1 : Matrix n n ℝ) =
      U * Matrix.diagonal (fun i => s i ^ 2 + α) * Uᵀ := by
  have hUUt : U * Uᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := U)).1 hU
  have hDiagConst : Matrix.diagonal (fun _ : n => α) = α • (1 : Matrix n n ℝ) := by
    -- A constant diagonal matrix is exactly a scalar multiple of the identity.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hDiagAdd :
      Matrix.diagonal (fun i => s i ^ 2) + Matrix.diagonal (fun _ : n => α) =
        Matrix.diagonal (fun i => s i ^ 2 + α) := by
    -- Adding diagonal matrices adds the diagonal entries pointwise.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hScalar :
      α • (1 : Matrix n n ℝ) = U * Matrix.diagonal (fun _ : n => α) * Uᵀ := by
    -- Reinsert the identity as `U * Uᵀ` so the scalar shift shares the same basis.
    calc
      α • (1 : Matrix n n ℝ) = α • (U * Uᵀ) := by rw [hUUt]
      _ = U * (α • (1 : Matrix n n ℝ)) * Uᵀ := by
            simp [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun _ : n => α) * Uᵀ := by
            rw [← hDiagConst]
  -- Combine the diagonalized Gramian with the diagonalized scalar shift.
  calc
    K * Kᵀ + α • (1 : Matrix n n ℝ)
        = U * Matrix.diagonal (fun i => s i ^ 2) * Uᵀ +
            U * Matrix.diagonal (fun _ : n => α) * Uᵀ := by
              rw [dataGramian_eq_orthogonalDiagonal K U V s hU hV hK, hScalar]
    _ = U * (Matrix.diagonal (fun i => s i ^ 2) + Matrix.diagonal (fun _ : n => α)) * Uᵀ := by
          calc
            U * Matrix.diagonal (fun i => s i ^ 2) * Uᵀ +
                U * Matrix.diagonal (fun _ : n => α) * Uᵀ
                = (U * Matrix.diagonal (fun i => s i ^ 2)) * Uᵀ +
                    (U * Matrix.diagonal (fun _ : n => α)) * Uᵀ := by
                      simp [Matrix.mul_assoc]
            _ = (U * (Matrix.diagonal (fun i => s i ^ 2) +
                    Matrix.diagonal (fun _ : n => α))) * Uᵀ := by
                  rw [← Matrix.add_mul, ← Matrix.mul_add]
            _ = U * (Matrix.diagonal (fun i => s i ^ 2) +
                    Matrix.diagonal (fun _ : n => α)) * Uᵀ := by
                  simp [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i => s i ^ 2 + α) * Uᵀ := by
          rw [hDiagAdd]

/-- Helper for Remark 1.2-extra-3: positive singular values force the square
SVD matrix `K` to be invertible. -/
theorem svd_det_isUnit_of_posSingularValues
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i) :
    IsUnit K.det := by
  have hU_det_sq : U.det * U.det = 1 := by
    have hUUt : U * Uᵀ = 1 :=
      (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := U)).1 hU
    simpa [Matrix.det_mul, Matrix.det_transpose] using congrArg Matrix.det hUUt
  have hV_det_sq : V.det * V.det = 1 := by
    have hVVt : V * Vᵀ = 1 :=
      (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := V)).1 hV
    simpa [Matrix.det_mul, Matrix.det_transpose] using congrArg Matrix.det hVVt
  have hU_det_ne : U.det ≠ 0 := by
    intro hzero
    have : (0 : ℝ) = 1 := by simpa [hzero] using hU_det_sq
    exact zero_ne_one this
  have hV_det_ne : V.det ≠ 0 := by
    intro hzero
    have : (0 : ℝ) = 1 := by simpa [hzero] using hV_det_sq
    exact zero_ne_one this
  have hDiag_ne : (∏ i, s i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact (hs_pos i).ne'
  have hK_det_ne : K.det ≠ 0 := by
    rw [hK, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero (mul_ne_zero hU_det_ne hDiag_ne) hV_det_ne
  exact isUnit_iff_ne_zero.mpr hK_det_ne

/-- Helper for Remark 1.2-extra-3: with positive singular values, the
zero-parameter Tikhonov discrepancy is exactly zero because the data are fit
without residual. -/
theorem tikhonov_discrepancy_zero_eq_zero_of_posSingularValues
    (K U V : Matrix n n ℝ) (s : n → ℝ) (d : EuclideanSpace ℝ n)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i) :
    Tikhonov.discrepancy K d 0 = 0 := by
  have hK_det : IsUnit K.det := svd_det_isUnit_of_posSingularValues K U V s hU hV hK hs_pos
  have hGram_det : IsUnit ((Kᵀ * K).det) := by
    simpa [Matrix.det_mul, Matrix.det_transpose] using
      (Matrix.isUnit_det_transpose K hK_det).mul hK_det
  have hData_det : IsUnit ((K * Kᵀ).det) := by
    simpa [Matrix.det_mul, Matrix.det_transpose] using
      hK_det.mul (Matrix.isUnit_det_transpose K hK_det)
  let y := K.toEuclideanLin (Tikhonov.reconstruction K 0 d)
  have hActual :
      (K * Kᵀ).toEuclideanLin y = (K * Kᵀ).toEuclideanLin d := by
    -- At `α = 0`, the data-space normal equation reduces to `K Kᵀ y = K Kᵀ d`.
    have hGram_det' : IsUnit ((Kᵀ * K + (0 : ℝ) • (1 : Matrix n n ℝ)).det) := by
      simpa using hGram_det
    simpa [y] using tikhonovDataNormalEquation K d 0 hGram_det'
  have hDiff :
      (K * Kᵀ).toEuclideanLin (y - d) = 0 := by
    -- Subtract the two data-space equations to isolate the residual.
    rw [LinearMap.map_sub, hActual, sub_self]
  have hy_eq : y = d := by
    have hy_zero : y - d = 0 := eq_zero_of_toEuclideanLin_eq_zero (K * Kᵀ) hData_det hDiff
    exact sub_eq_zero.mp hy_zero
  -- The discrepancy is the norm of the fitted data residual, which vanishes here.
  rw [Tikhonov.discrepancy_eq]
  simpa [y, hy_eq]

/-- Helper for Remark 1.2-extra-3: whenever `Kᵀ * K + α I` is invertible, the
Tikhonov objective splits into the value at the reconstruction plus a
nonnegative gap in `f - f_α`. -/
theorem tikhonovObjective_gap_eq_reconstruction
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ)
    (hA_det : IsUnit ((Kᵀ * K + α • (1 : Matrix n n ℝ)).det))
    (f : EuclideanSpace ℝ n) :
    VariationalRegularization.tikhonovObjective K d α f =
      VariationalRegularization.tikhonovObjective K d α
        (Tikhonov.reconstruction K α d) +
      ‖K.toEuclideanLin (f - Tikhonov.reconstruction K α d)‖ ^ 2 +
      α * ‖f - Tikhonov.reconstruction K α d‖ ^ 2 := by
  let r := Tikhonov.reconstruction K α d
  let h := f - r
  -- Route correction: expand the objective at `r + h` rather than at arbitrary `f`.
  have hf : f = r + h := by
    simp [h, r, sub_eq_add_neg, add_left_comm]
  -- Rewrite the residual into a translated coordinate centered at the reconstruction.
  have hres :
      K.toEuclideanLin f - d = (K.toEuclideanLin r - d) + K.toEuclideanLin h := by
    rw [hf, LinearMap.map_add]
    abel
  -- The normal equation kills the translated mixed term.
  have hcross :
      inner ℝ (K.toEuclideanLin r - d) (K.toEuclideanLin h) + α * inner ℝ r h = 0 := by
    have hEq : ((Kᵀ * K).toEuclideanLin r) + α • r = (Kᵀ).toEuclideanLin d := by
      have hNormal := tikhonovNormalEquation K d α hA_det
      simpa [r, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using hNormal
    have hnormal : (Kᵀ).toEuclideanLin (K.toEuclideanLin r - d) + α • r = 0 := by
      have hEq' := congrArg (fun x => x - (Kᵀ).toEuclideanLin d) hEq
      rw [LinearMap.map_sub]
      rw [show (Kᵀ).toEuclideanLin (K.toEuclideanLin r) = ((Kᵀ * K).toEuclideanLin r) by
        simpa [r] using (toEuclideanLin_mul_apply (Kᵀ) K r)]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEq'
    have hinner := congrArg (fun x => inner ℝ h x) hnormal
    have hAdj : LinearMap.adjoint K.toEuclideanLin = (Kᵀ).toEuclideanLin := by
      simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint K).symm
    rw [inner_add_right, inner_smul_right, inner_zero_right] at hinner
    rw [← hAdj, LinearMap.adjoint_inner_right] at hinner
    simpa [r, real_inner_comm, mul_comm] using hinner
  -- Expand both quadratic norms and then eliminate the mixed term with `hcross`.
  calc
    VariationalRegularization.tikhonovObjective K d α f
        = ‖K.toEuclideanLin f - d‖ ^ 2 + α * ‖f‖ ^ 2 := by
            rw [VariationalRegularization.tikhonovObjective_def]
    _ = ‖(K.toEuclideanLin r - d) + K.toEuclideanLin h‖ ^ 2 + α * ‖r + h‖ ^ 2 := by
          rw [hres, hf]
    _ = (‖K.toEuclideanLin r - d‖ ^ 2 +
          2 * inner ℝ (K.toEuclideanLin r - d) (K.toEuclideanLin h) +
          ‖K.toEuclideanLin h‖ ^ 2) +
          α * (‖r‖ ^ 2 + 2 * inner ℝ r h + ‖h‖ ^ 2) := by
          rw [norm_add_sq_real, norm_add_sq_real]
    _ = (‖K.toEuclideanLin r - d‖ ^ 2 + α * ‖r‖ ^ 2) +
          ‖K.toEuclideanLin h‖ ^ 2 + α * ‖h‖ ^ 2 := by
          nlinarith [hcross]
    _ = VariationalRegularization.tikhonovObjective K d α r +
          ‖K.toEuclideanLin h‖ ^ 2 + α * ‖h‖ ^ 2 := by
          rw [VariationalRegularization.tikhonovObjective_def]
    _ = VariationalRegularization.tikhonovObjective K d α
          (Tikhonov.reconstruction K α d) +
          ‖K.toEuclideanLin (f - Tikhonov.reconstruction K α d)‖ ^ 2 +
          α * ‖f - Tikhonov.reconstruction K α d‖ ^ 2 := by
          simp [r, h]

/-- Helper for Remark 1.2-extra-3: the predicted data `K f_α` already has the
textbook diagonal form in the left singular basis. -/
theorem predictedData_eq_filterRepresentation
    (K U V : Matrix n n ℝ) (s : n → ℝ) (d : EuclideanSpace ℝ n) (α : ℝ)
    (hα_pos : 0 < α)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    K.toEuclideanLin (Tikhonov.reconstruction K α d) =
      Matrix.toEuclideanLin
        (U * Matrix.diagonal (fun i ↦ s i ^ 2 / (s i ^ 2 + α)) * Uᵀ) d := by
  let coeff : n → ℝ := fun i ↦ s i / (s i ^ 2 + α)
  have hVtV : Vᵀ * V = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := V)).1 hV
  have hRecon :
      Tikhonov.reconstruction K α d =
        Matrix.toEuclideanLin (V * Matrix.diagonal coeff * Uᵀ) d := by
    have hCoeffDiag :
        Matrix.diagonal (fun i ↦ SpectralFilter.tikhonov α (s i ^ 2) / s i) =
          Matrix.diagonal coeff := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [coeff, Tikhonov.filterScalar_eq_ratio]
      · simp [Matrix.diagonal_apply_ne _ hij]
    -- Route correction: reuse the stable Exercise 1.12 filter formula instead
    -- of reopening the shifted normal equation in data space.
    calc
      Tikhonov.reconstruction K α d
          = Matrix.toEuclideanLin (Tikhonov.operator K α) d := by
              simp [Tikhonov.reconstruction_eq, Tikhonov.operator_def]
      _ = Matrix.toEuclideanLin
            (V * Matrix.diagonal (fun i ↦ SpectralFilter.tikhonov α (s i ^ 2) / s i) * Uᵀ) d := by
              simpa using Tikhonov.operator_apply_eq_svdFilter K U V s α d hα_pos hU hV hK
      _ = Matrix.toEuclideanLin (V * Matrix.diagonal coeff * Uᵀ) d := by
            rw [hCoeffDiag]
  have hPredMatrix :
      K * (V * Matrix.diagonal coeff * Uᵀ) =
        U * Matrix.diagonal (fun i ↦ s i ^ 2 / (s i ^ 2 + α)) * Uᵀ := by
    have hDiagCoeff :
        Matrix.diagonal (fun i ↦ s i * coeff i) =
          Matrix.diagonal (fun i ↦ s i ^ 2 / (s i ^ 2 + α)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [coeff]
        ring
      · simp [Matrix.diagonal_apply_ne _ hij]
    -- Push the SVD of `K` through the filter matrix and collapse the diagonal core.
    calc
      K * (V * Matrix.diagonal coeff * Uᵀ)
          = (U * Matrix.diagonal s * Vᵀ) * (V * Matrix.diagonal coeff * Uᵀ) := by
              rw [hK]
      _ = U * (Matrix.diagonal s * (Vᵀ * V) * Matrix.diagonal coeff) * Uᵀ := by
            simp [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal s * Matrix.diagonal coeff) * Uᵀ := by
            rw [hVtV]
            simp [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun i ↦ s i * coeff i) * Uᵀ := by
            rw [Matrix.diagonal_mul_diagonal]
      _ = U * Matrix.diagonal (fun i ↦ s i ^ 2 / (s i ^ 2 + α)) * Uᵀ := by
            rw [hDiagCoeff]
  -- Convert the matrix identity back into the Euclidean-space action on `d`.
  calc
    K.toEuclideanLin (Tikhonov.reconstruction K α d)
        = K.toEuclideanLin (Matrix.toEuclideanLin (V * Matrix.diagonal coeff * Uᵀ) d) := by
            rw [hRecon]
    _ = Matrix.toEuclideanLin (K * (V * Matrix.diagonal coeff * Uᵀ)) d := by
          symm
          simpa using
            (toEuclideanLin_mul_apply K (V * Matrix.diagonal coeff * Uᵀ) d)
    _ = Matrix.toEuclideanLin
          (U * Matrix.diagonal (fun i ↦ s i ^ 2 / (s i ^ 2 + α)) * Uᵀ) d := by
            rw [hPredMatrix]

/-- Helper for Remark 1.2-extra-3: subtracting the data vector from the
predicted data exposes the discrepancy in diagonal left-singular coordinates. -/
theorem predictedDataResidual_eq_orthogonalDiagonal
    (K U V : Matrix n n ℝ) (s : n → ℝ) (d : EuclideanSpace ℝ n) (α : ℝ)
    (hα_pos : 0 < α)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    K.toEuclideanLin (Tikhonov.reconstruction K α d) - d =
      Matrix.toEuclideanLin U
        (Matrix.toEuclideanLin
          (Matrix.diagonal (fun i ↦ s i ^ 2 / (s i ^ 2 + α) - 1))
          ((Uᵀ).toEuclideanLin d)) := by
  let coeff : n → ℝ := fun i ↦ s i ^ 2 / (s i ^ 2 + α)
  let u : EuclideanSpace ℝ n := (Uᵀ).toEuclideanLin d
  have hPred :
      K.toEuclideanLin (Tikhonov.reconstruction K α d) =
        Matrix.toEuclideanLin U (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) := by
    -- Rewrite the predicted data once into the outer-orthogonal plus diagonal core.
    calc
      K.toEuclideanLin (Tikhonov.reconstruction K α d)
          = Matrix.toEuclideanLin (U * Matrix.diagonal coeff * Uᵀ) d := by
              simpa [coeff] using
                predictedData_eq_filterRepresentation K U V s d α hα_pos hU hV hK
      _ = Matrix.toEuclideanLin U
            (Matrix.toEuclideanLin (Matrix.diagonal coeff * Uᵀ) d) := by
            simpa [Matrix.mul_assoc] using
              (toEuclideanLin_mul_apply U (Matrix.diagonal coeff * Uᵀ) d).symm
      _ = Matrix.toEuclideanLin U
            (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) := by
            congr 1
            simpa [u, Matrix.mul_assoc] using
              (toEuclideanLin_mul_apply (Matrix.diagonal coeff) Uᵀ d).symm
  have hData :
      d = Matrix.toEuclideanLin U u := by
    -- Recover `d` from its left-singular coordinates using orthogonality of `U`.
    simpa [u] using (FilterRegularization.orthogonal_toEuclideanLin_apply_transpose U hU d).symm
  -- Keep the subtraction under the outer orthogonal map and rewrite only the diagonal bias.
  calc
    K.toEuclideanLin (Tikhonov.reconstruction K α d) - d
        = Matrix.toEuclideanLin U (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) -
            Matrix.toEuclideanLin U u := by
              rw [hPred, hData]
    _ = Matrix.toEuclideanLin U
          (Matrix.toEuclideanLin (Matrix.diagonal coeff) u - u) := by
            simpa using
              (Matrix.toEuclideanLin U).map_sub
                (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) u
    _ = Matrix.toEuclideanLin U
          (Matrix.toEuclideanLin
            (Matrix.diagonal (fun i ↦ coeff i - 1))
            u) := by
              congr 1
              ext i
              simp [coeff, Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal]
              ring
    _ = Matrix.toEuclideanLin U
          (Matrix.toEuclideanLin
            (Matrix.diagonal (fun i ↦ s i ^ 2 / (s i ^ 2 + α) - 1))
            ((Uᵀ).toEuclideanLin d)) := by
              simp [coeff, u]

/-- Equation `(1.31)` for Remark 1.2-extra-3 (1) in the square finite-dimensional
SVD specialization used by the local matrix/operator API: for an orthogonal
SVD `K = U * Matrix.diagonal s * Vᵀ` with `K : Matrix n n ℝ` and a positive
regularization parameter `α`, the squared discrepancy functional is the
displayed singular-value expansion. -/
theorem tikhonov_discrepancy_sq_eq
    (K U V : Matrix n n ℝ) (s : n → ℝ) (d : EuclideanSpace ℝ n) (α : ℝ)
    (hα_pos : 0 < α)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    Tikhonov.discrepancy K d α ^ 2 =
      ∑ i, (1 - s i ^ 2 / (s i ^ 2 + α)) ^ 2 * (((Uᵀ).toEuclideanLin d) i) ^ 2 := by
  let bias : n → ℝ := fun i ↦ s i ^ 2 / (s i ^ 2 + α) - 1
  let u : EuclideanSpace ℝ n := (Uᵀ).toEuclideanLin d
  have hResidual :
      K.toEuclideanLin (Tikhonov.reconstruction K α d) - d =
        Matrix.toEuclideanLin U
          (Matrix.toEuclideanLin (Matrix.diagonal bias) u) := by
    -- Route correction: consume the dedicated residual bridge instead of
    -- rebuilding the predicted-data comparison inline.
    simpa [bias, u] using
      predictedDataResidual_eq_orthogonalDiagonal K U V s d α hα_pos hU hV hK
  -- After the residual is diagonalized in the left singular basis, only the norm-square calculation remains.
  calc
    Tikhonov.discrepancy K d α ^ 2
        = ‖K.toEuclideanLin (Tikhonov.reconstruction K α d) - d‖ ^ 2 := by
            rw [Tikhonov.discrepancy_eq]
    _ = ‖Matrix.toEuclideanLin U
          (Matrix.toEuclideanLin (Matrix.diagonal bias) u)‖ ^ 2 := by
            rw [hResidual]
    _ = ‖Matrix.toEuclideanLin (Matrix.diagonal bias) u‖ ^ 2 := by
          simpa using
            FilterRegularization.orthogonal_toEuclideanLin_norm_sq_eq U hU
              (Matrix.toEuclideanLin (Matrix.diagonal bias) u)
    _ = ∑ i, (bias i) ^ 2 * (u i) ^ 2 := by
          simpa using FilterRegularization.diagonal_toEuclideanLin_normSq bias u
    _ = ∑ i, (1 - s i ^ 2 / (s i ^ 2 + α)) ^ 2 * (((Uᵀ).toEuclideanLin d) i) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          change (bias i) ^ 2 * (u i) ^ 2 =
            (1 - s i ^ 2 / (s i ^ 2 + α)) ^ 2 * (((Uᵀ).toEuclideanLin d) i) ^ 2
          rw [show u i = ((Uᵀ).toEuclideanLin d) i by rfl]
          dsimp [bias]
          ring

/-- Helper for Remark 1.2-extra-3: the squared discrepancy formula extends from
positive `α` to all `α ∈ Set.Ici 0` by separating the zero endpoint. -/
theorem discrepancySq_eq_svdSum_nonneg
    (K U V : Matrix n n ℝ) (s : n → ℝ) (d : EuclideanSpace ℝ n) (α : ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hα_nonneg : 0 ≤ α) :
    Tikhonov.discrepancy K d α ^ 2 =
      ∑ i, (1 - s i ^ 2 / (s i ^ 2 + α)) ^ 2 * (((Uᵀ).toEuclideanLin d) i) ^ 2 := by
  rcases eq_or_lt_of_le hα_nonneg with rfl | hα_pos
  · -- At `α = 0`, both sides vanish because positive singular values force exact data fit.
    rw [tikhonov_discrepancy_zero_eq_zero_of_posSingularValues K U V s d hU hV hK hs_pos]
    have hsum :
        ∑ i, (1 - s i ^ 2 / (s i ^ 2 + 0)) ^ 2 * (((Uᵀ).toEuclideanLin d) i) ^ 2 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hs_mul_ne : s i * s i ≠ 0 := mul_ne_zero (hs_pos i).ne' (hs_pos i).ne'
      field_simp [pow_two, hs_mul_ne]
      ring
    simpa using hsum.symm
  · -- On the positive branch, reuse the explicit formula already proved above.
    exact tikhonov_discrepancy_sq_eq K U V s d α hα_pos hU hV hK

/-- Helper for Remark 1.2-extra-3: on `Set.Ici 0`, the squared discrepancy
coefficient rewrites to the monotonicity-friendly normalized form
`α / (s i ^ 2 + α)`. -/
theorem discrepancySq_eq_normalizedSvdSum_nonneg
    (K U V : Matrix n n ℝ) (s : n → ℝ) (d : EuclideanSpace ℝ n) (α : ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hα_nonneg : 0 ≤ α) :
    Tikhonov.discrepancy K d α ^ 2 =
      ∑ i, (α / (s i ^ 2 + α)) ^ 2 * (((Uᵀ).toEuclideanLin d) i) ^ 2 := by
  -- Rewrite the closed-form discrepancy once into the normalized scalar coefficient.
  rw [discrepancySq_eq_svdSum_nonneg K U V s d α hU hV hK hs_pos hα_nonneg]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hden_pos : 0 < s i ^ 2 + α := by
    have hs_sq_pos : 0 < s i ^ 2 := by
      nlinarith [hs_pos i]
    nlinarith
  have hcoeff :
      1 - s i ^ 2 / (s i ^ 2 + α) = α / (s i ^ 2 + α) := by
    field_simp [hden_pos.ne']
    ring
  rw [hcoeff]

/-- Helper for Remark 1.2-extra-3: a nonzero Euclidean vector has a nonzero
coordinate. -/
theorem exists_ne_zero_coord_of_ne_zero
    [Nonempty n] {u : EuclideanSpace ℝ n} (hu_ne : u ≠ 0) :
    ∃ i, u i ≠ 0 := by
  -- Contraposing turns the goal into extensional equality with the zero vector.
  by_contra hcoord
  apply hu_ne
  ext i
  by_contra hi
  exact hcoord ⟨i, hi⟩

/-- Helper for Remark 1.2-extra-3: for a positive scalar shift `c`, the
normalized coefficient `α / (c + α)` has strictly increasing square on
`Set.Ici 0`. -/
theorem scalarResidualCoeff_sq_strictMonoOn
    {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun α : ℝ ↦ (α / (c + α)) ^ 2) (Set.Ici 0) := by
  intro x hx y hy hxy
  -- First compare the unsquared normalized coefficients by cross-multiplication.
  have hx_nonneg : 0 ≤ x := hx
  have hy_nonneg : 0 ≤ y := hy
  have hcx : 0 < c + x := by nlinarith
  have hcy : 0 < c + y := by nlinarith
  have hratio : x / (c + x) < y / (c + y) := by
    refine (div_lt_div_iff₀ hcx hcy).2 ?_
    nlinarith [hc, hxy]
  -- Both coefficients are nonnegative on `Set.Ici 0`, so squaring preserves strict order.
  have hx_ratio_nonneg : 0 ≤ x / (c + x) := div_nonneg hx_nonneg hcx.le
  have hy_ratio_nonneg : 0 ≤ y / (c + y) := div_nonneg hy_nonneg hcy.le
  nlinarith

/-- Helper for Remark 1.2-extra-3: a single nonzero coordinate forces the full
normalized squared discrepancy sum to be strictly increasing on `Set.Ici 0`. -/
theorem normalizedDiscrepancySq_strictMonoOn_of_nonzeroCoord
    [Nonempty n] (s : n → ℝ) (u : EuclideanSpace ℝ n) (i0 : n)
    (hs_pos : ∀ i, 0 < s i) (hu : u i0 ≠ 0) :
    StrictMonoOn
      (fun α : ℝ ↦ ∑ i, (α / (s i ^ 2 + α)) ^ 2 * (u i) ^ 2)
      (Set.Ici 0) := by
  intro x hx y hy hxy
  -- Sum the coordinatewise monotone estimates, then use the witness coordinate for strictness.
  have hle :
      ∀ i ∈ (Finset.univ : Finset n),
        (x / (s i ^ 2 + x)) ^ 2 * (u i) ^ 2 ≤
          (y / (s i ^ 2 + y)) ^ 2 * (u i) ^ 2 := by
    intro i hi
    have hs_sq_pos : 0 < s i ^ 2 := by
      nlinarith [hs_pos i]
    have hcoeff :
        (x / (s i ^ 2 + x)) ^ 2 < (y / (s i ^ 2 + y)) ^ 2 :=
      scalarResidualCoeff_sq_strictMonoOn (c := s i ^ 2) hs_sq_pos hx hy hxy
    exact mul_le_mul_of_nonneg_right (le_of_lt hcoeff) (sq_nonneg (u i))
  have hlt :
      ∃ i ∈ (Finset.univ : Finset n),
        (x / (s i ^ 2 + x)) ^ 2 * (u i) ^ 2 <
          (y / (s i ^ 2 + y)) ^ 2 * (u i) ^ 2 := by
    refine ⟨i0, Finset.mem_univ _, ?_⟩
    have hs_sq_pos : 0 < s i0 ^ 2 := by
      nlinarith [hs_pos i0]
    have hcoeff :
        (x / (s i0 ^ 2 + x)) ^ 2 < (y / (s i0 ^ 2 + y)) ^ 2 :=
      scalarResidualCoeff_sq_strictMonoOn (c := s i0 ^ 2) hs_sq_pos hx hy hxy
    have hweight : 0 < (u i0) ^ 2 := sq_pos_of_ne_zero hu
    exact mul_lt_mul_of_pos_right hcoeff hweight
  exact Finset.sum_lt_sum hle hlt

/-- Helper for Remark 1.2-extra-3: along nat-casts, the normalized squared
discrepancy model converges to the coordinate norm square. -/
theorem normalizedDiscrepancySq_natCast_tendsto_coordNormSq
    (s : n → ℝ) (u : EuclideanSpace ℝ n) (hs_pos : ∀ i, 0 < s i) :
    Tendsto
      (fun k : ℕ ↦ ∑ i, (((k : ℝ) / (s i ^ 2 + k)) ^ 2) * (u i) ^ 2)
      atTop
      (𝓝 (∑ i, (u i) ^ 2)) := by
  -- Prove convergence coordinatewise, then sum the finitely many coordinates.
  refine tendsto_finsetSum Finset.univ ?_
  intro i hi
  have hs_sq_pos : 0 < s i ^ 2 := by
    nlinarith [hs_pos i]
  have hden :
      Tendsto (fun k : ℕ ↦ s i ^ 2 + (k : ℝ)) atTop atTop := by
    simpa [add_comm] using
      tendsto_atTop_add_const_right atTop (s i ^ 2) tendsto_natCast_atTop_atTop
  have hsmall :
      Tendsto (fun k : ℕ ↦ s i ^ 2 / (s i ^ 2 + (k : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    exact hden.const_div_atTop (s i ^ 2)
  have hratio :
      Tendsto (fun k : ℕ ↦ ((k : ℝ) / (s i ^ 2 + k))) atTop (𝓝 (1 : ℝ)) := by
    -- Rewrite the ratio as `1 - c / (c + k)` so the limit reduces to the vanishing tail term.
    have hratio_aux :
        Tendsto
          (fun k : ℕ ↦ (1 : ℝ) - s i ^ 2 / (s i ^ 2 + (k : ℝ)))
          atTop
          (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub hsmall)
    refine Tendsto.congr' ?_ hratio_aux
    filter_upwards with k
    have hden_ne : s i ^ 2 + (k : ℝ) ≠ 0 := by
      have hk_nonneg : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
      have : 0 < s i ^ 2 + (k : ℝ) := by nlinarith
      exact this.ne'
    field_simp [hden_ne]
    ring
  -- Squaring and multiplying by the fixed coordinate weight preserves the limit.
  simpa using (hratio.pow 2).mul tendsto_const_nhds

/-- Remark 1.2-extra-3 (2). In the same square full-rank finite-dimensional
Tikhonov/SVD setup as `(1.31)`, with all displayed singular values positive,
the equation `D(α) = δ` has a unique nonnegative solution for a noise level
`δ` satisfying `0 ≤ δ` and `δ < ‖d‖`. -/
theorem tikhonov_discrepancy_eq_noiseLevel_existsUnique
    (K U V : Matrix n n ℝ) (s : n → ℝ) (d : EuclideanSpace ℝ n) {δ : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hδ_nonneg : 0 ≤ δ)
    (hδ_lt : δ < ‖d‖) :
    ∃! α : ℝ, α ∈ Set.Ici 0 ∧ Tikhonov.discrepancy K d α = δ := by
  classical
  rcases isEmpty_or_nonempty n with hEmpty | hNonempty
  · letI := hEmpty
    -- If the index type is empty, then `d = 0`, contradicting `0 ≤ δ < ‖d‖`.
    have hd_zero : d = 0 := Subsingleton.elim _ _
    have hδ_neg : δ < 0 := by simpa [hd_zero] using hδ_lt
    exact (not_lt_of_ge hδ_nonneg hδ_neg).elim
  · letI := hNonempty
    let u : EuclideanSpace ℝ n := (Uᵀ).toEuclideanLin d
    let F : ℝ → ℝ := fun α ↦
      ∑ i, (α / (s i ^ 2 + α)) ^ 2 * (u i) ^ 2
    -- Route correction: stay in the normalized scalar model and avoid reopening matrix transport.
    have hF_eq :
        ∀ {α : ℝ}, 0 ≤ α → Tikhonov.discrepancy K d α ^ 2 = F α := by
      intro α hα_nonneg
      simpa [F, u] using
        discrepancySq_eq_normalizedSvdSum_nonneg K U V s d α hU hV hK hs_pos hα_nonneg
    have hd_ne : d ≠ 0 := by
      -- The noise-level hypothesis excludes the zero-data case.
      intro hd_zero
      have hδ_neg : δ < 0 := by simpa [hd_zero] using hδ_lt
      exact (not_lt_of_ge hδ_nonneg hδ_neg).elim
    have hu_ne : u ≠ 0 := by
      -- Orthogonality transports nonzeroness between `d` and its left-singular coordinates.
      intro hu_zero
      apply hd_ne
      calc
        d = Matrix.toEuclideanLin U u := by
          simpa [u] using
            (FilterRegularization.orthogonal_toEuclideanLin_apply_transpose U hU d).symm
        _ = 0 := by simp [hu_zero]
    obtain ⟨i0, hu0⟩ := exists_ne_zero_coord_of_ne_zero (u := u) hu_ne
    have hF_strict : StrictMonoOn F (Set.Ici 0) := by
      -- One nonzero coordinate gives a strict witness for the finite sum.
      simpa [F] using
        normalizedDiscrepancySq_strictMonoOn_of_nonzeroCoord s u i0 hs_pos hu0
    have hcoord_norm :
        ∑ i, (u i) ^ 2 = ‖d‖ ^ 2 := by
      -- Orthogonality preserves the Euclidean norm square in the singular basis.
      have hUt : Uᵀ ∈ Matrix.orthogonalGroup n ℝ :=
        FilterRegularization.transpose_mem_orthogonalGroup U hU
      calc
        ∑ i, (u i) ^ 2 = ‖u‖ ^ 2 := by
          rw [← EuclideanSpace.real_norm_sq_eq u]
        _ = ‖d‖ ^ 2 := by
          simpa [u] using
            FilterRegularization.orthogonal_toEuclideanLin_norm_sq_eq Uᵀ hUt d
    have hF_limit_coord :
        Tendsto (fun k : ℕ ↦ F k) atTop (𝓝 (∑ i, (u i) ^ 2)) := by
      simpa [F] using normalizedDiscrepancySq_natCast_tendsto_coordNormSq s u hs_pos
    have hF_limit :
        Tendsto (fun k : ℕ ↦ F k) atTop (𝓝 (‖d‖ ^ 2)) := by
      simpa [hcoord_norm] using hF_limit_coord
    have hδ_sq_lt : δ ^ 2 < ‖d‖ ^ 2 := by
      nlinarith [hδ_nonneg, hδ_lt, norm_nonneg d]
    have hEventually : ∀ᶠ k : ℕ in atTop, δ ^ 2 < F k := by
      simpa [Set.mem_Ioi] using hF_limit.eventually (Ioi_mem_nhds hδ_sq_lt)
    rcases eventually_atTop.1 hEventually with ⟨N, hN⟩
    have hFN : δ ^ 2 < F N := hN N le_rfl
    have hcontTerm :
        ∀ i : n,
          ContinuousOn
            (fun α : ℝ ↦ (α / (s i ^ 2 + α)) ^ 2 * (u i) ^ 2)
            (Set.Icc (0 : ℝ) (N : ℝ)) := by
      intro i
      -- Each scalar summand is continuous because its denominator stays positive on the interval.
      have hden :
          ∀ α ∈ Set.Icc (0 : ℝ) (N : ℝ), s i ^ 2 + α ≠ 0 := by
        intro α hα
        have hα_nonneg : 0 ≤ α := hα.1
        have hs_sq_pos : 0 < s i ^ 2 := by
          nlinarith [hs_pos i]
        have : 0 < s i ^ 2 + α := by
          nlinarith
        exact this.ne'
      have hratio :
          ContinuousOn (fun α : ℝ ↦ α / (s i ^ 2 + α)) (Set.Icc (0 : ℝ) (N : ℝ)) := by
        exact continuousOn_id.div (continuousOn_const.add continuousOn_id) hden
      exact (hratio.pow 2).mul continuousOn_const
    have hF_cont : ContinuousOn F (Set.Icc (0 : ℝ) (N : ℝ)) := by
      -- The full scalar model is a finite sum of continuous summands.
      refine continuousOn_finsetSum Finset.univ ?_
      intro i hi
      simpa [F] using hcontTerm i
    have h0N : (0 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.zero_le N
    have hF_zero : F 0 = 0 := by
      simp [F]
    have hδ_mem : δ ^ 2 ∈ Set.Icc (F 0) (F N) := by
      rw [hF_zero]
      constructor
      · nlinarith [hδ_nonneg]
      · exact le_of_lt hFN
    have hImage : δ ^ 2 ∈ F '' Set.Icc (0 : ℝ) (N : ℝ) := by
      exact (intermediate_value_Icc (a := (0 : ℝ)) (b := (N : ℝ)) h0N hF_cont) hδ_mem
    rcases hImage with ⟨α, hαIcc, hFα⟩
    have hα_mem : α ∈ Set.Ici 0 := hαIcc.1
    refine ⟨α, ?_, ?_⟩
    · constructor
      · exact hα_mem
      · -- Unsquare only once, after the scalar-model existence step is finished.
        have hdisc_sq : Tikhonov.discrepancy K d α ^ 2 = δ ^ 2 := by
          rw [hF_eq hα_mem, hFα]
        have hdisc_nonneg : 0 ≤ Tikhonov.discrepancy K d α := by
          rw [Tikhonov.discrepancy_eq]
          exact norm_nonneg _
        nlinarith
    · intro β hβ
      rcases hβ with ⟨hβ_mem, hβ_disc⟩
      -- Uniqueness stays in the squared scalar model, so no second unsquaring step is needed.
      have hβF : F β = δ ^ 2 := by
        calc
          F β = Tikhonov.discrepancy K d β ^ 2 := by
            symm
            exact hF_eq hβ_mem
          _ = δ ^ 2 := by rw [hβ_disc]
      exact hF_strict.injOn hβ_mem hα_mem (by rw [hβF, hFα])

/-- `Tikhonov.reconstruction K α d` is the variational Tikhonov minimizer at
positive parameter `α`. -/
theorem tikhonov_reconstruction_isTikhonovMinimizer
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (α : ℝ)
    (hα_pos : 0 < α) :
    VariationalRegularization.IsTikhonovMinimizer K d α
      (Tikhonov.reconstruction K α d) := by
  rw [VariationalRegularization.IsTikhonovMinimizer_iff, isMinOn_univ_iff]
  intro f
  -- Positive definiteness supplies the invertibility needed by the gap identity.
  have hA_posDef : (Kᵀ * K + α • (1 : Matrix n n ℝ)).PosDef := gramianShift_posDef K α hα_pos
  have hA_det : IsUnit ((Kᵀ * K + α • (1 : Matrix n n ℝ)).det) := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp hA_posDef.isUnit
  -- The two gap terms are nonnegative, so the reconstruction minimizes the objective.
  rw [tikhonovObjective_gap_eq_reconstruction K d α hA_det f]
  have hResidual : 0 ≤ ‖K.toEuclideanLin (f - Tikhonov.reconstruction K α d)‖ ^ 2 := sq_nonneg _
  have hPenalty : 0 ≤ α * ‖f - Tikhonov.reconstruction K α d‖ ^ 2 := by
    nlinarith [sq_nonneg ‖f - Tikhonov.reconstruction K α d‖, hα_pos]
  linarith

/-- Equation `(1.33)` for Remark 1.2-extra-3 (3): if `α(δ)` is the discrepancy-principle
parameter, then
`‖f_{α(δ)}‖ ≤ ‖f_true‖`. -/
theorem tikhonov_norm_le_true_of_discrepancyParam
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m) (fTrue : EuclideanSpace ℝ n)
    {δ : ℝ}
    (h_existsUnique : ∃! α : ℝ, α ∈ Set.Ici 0 ∧ Tikhonov.discrepancy K d α = δ)
    (h_data : ‖K.toEuclideanLin fTrue - d‖ = δ) :
    ‖Tikhonov.reconstruction K (Tikhonov.discrepancyParam K d δ h_existsUnique) d‖ ≤
      ‖fTrue‖ := by
  let αStar := Tikhonov.discrepancyParam K d δ h_existsUnique
  have hspec := Tikhonov.discrepancyParam_spec K d δ h_existsUnique
  have hα_nonneg : 0 ≤ αStar := hspec.1
  rcases eq_or_lt_of_le hα_nonneg with hα_zero | hα_pos
  · have hα_zero' : αStar = 0 := hα_zero.symm
    let r0 := Tikhonov.reconstruction K 0 d
    -- In the zero-parameter branch, either the Gramian is singular and the reconstruction is zero,
    -- or it is invertible and equal residuals force `r0 = fTrue`.
    have hr0_data : ‖K.toEuclideanLin r0 - d‖ = δ := by
      simpa [αStar, hα_zero', r0, Tikhonov.discrepancy_eq] using hspec.2
    by_cases hGram : IsUnit ((Kᵀ * K).det)
    · have hA_det : IsUnit ((Kᵀ * K + (0 : ℝ) • (1 : Matrix n n ℝ)).det) := by
        simpa using hGram
      have hgap0 := tikhonovObjective_gap_eq_reconstruction K d 0 hA_det fTrue
      have hobjSq : VariationalRegularization.tikhonovObjective K d 0 fTrue =
          VariationalRegularization.tikhonovObjective K d 0 r0 := by
        simp [VariationalRegularization.tikhonovObjective_def, hr0_data, h_data, r0]
      have hresSq : ‖K.toEuclideanLin (fTrue - r0)‖ ^ 2 = 0 := by
        nlinarith [hgap0, hobjSq]
      have hKerNorm : ‖K.toEuclideanLin (fTrue - r0)‖ = 0 := sq_eq_zero_iff.mp hresSq
      have hKer : K.toEuclideanLin (fTrue - r0) = 0 := norm_eq_zero.mp hKerNorm
      have hGramKer : (Kᵀ * K).toEuclideanLin (fTrue - r0) = 0 := by
        rw [show (Kᵀ * K).toEuclideanLin (fTrue - r0) =
            (Kᵀ).toEuclideanLin (K.toEuclideanLin (fTrue - r0)) by
          simpa using (toEuclideanLin_mul_apply (Kᵀ) K (fTrue - r0))]
        simp [hKer]
      have hEq : fTrue - r0 = 0 := eq_zero_of_toEuclideanLin_eq_zero (Kᵀ * K) hGram hGramKer
      have hrEq : r0 = fTrue := (sub_eq_zero.mp hEq).symm
      simpa [αStar, hα_zero', r0, hrEq]
    · simpa [αStar, hα_zero', reconstruction_zero_of_not_isUnit_gramian K d hGram]
  · let r := Tikhonov.reconstruction K αStar d
    -- For positive parameter, compare objective values at the minimizer and at `fTrue`.
    have hr_data : ‖K.toEuclideanLin r - d‖ = δ := by
      simpa [αStar, r, Tikhonov.discrepancy_eq] using hspec.2
    have hmin : VariationalRegularization.IsTikhonovMinimizer K d αStar r := by
      simpa [αStar, r] using tikhonov_reconstruction_isTikhonovMinimizer K d αStar hα_pos
    rw [VariationalRegularization.IsTikhonovMinimizer_iff, isMinOn_univ_iff] at hmin
    have hobj := hmin fTrue
    have hobj' : δ ^ 2 + αStar * ‖r‖ ^ 2 ≤ δ ^ 2 + αStar * ‖fTrue‖ ^ 2 := by
      simpa [VariationalRegularization.tikhonovObjective_def, hr_data, h_data, αStar, r] using hobj
    have hsquare : ‖r‖ ^ 2 ≤ ‖fTrue‖ ^ 2 := by
      nlinarith
    have hnorm : ‖r‖ ≤ ‖fTrue‖ := by
      nlinarith [hsquare, norm_nonneg r, norm_nonneg fTrue]
    simpa [αStar, r] using hnorm

/-- Under the source condition `f_true = Kᵀ z`, Remark 1.2-extra-3 (4) gives the
discrepancy-principle Tikhonov reconstruction satisfies the order-optimal
estimate `‖f_{α(δ)} - f_true‖^2 ≤ 4 * δ * ‖z‖`. -/
theorem tikhonov_orderOptimality_of_sourceCondition
    (K : Matrix m n ℝ) (d : EuclideanSpace ℝ m)
    (fTrue : EuclideanSpace ℝ n) (z : EuclideanSpace ℝ m) {δ : ℝ}
    (h_existsUnique : ∃! α : ℝ, α ∈ Set.Ici 0 ∧ Tikhonov.discrepancy K d α = δ)
    (h_data : ‖K.toEuclideanLin fTrue - d‖ = δ)
    (h_source : fTrue = (Kᵀ).toEuclideanLin z) :
    ‖Tikhonov.reconstruction K (Tikhonov.discrepancyParam K d δ h_existsUnique) d - fTrue‖ ^ 2 ≤
      4 * δ * ‖z‖ := by
  let αStar := Tikhonov.discrepancyParam K d δ h_existsUnique
  let r := Tikhonov.reconstruction K αStar d
  have hspec := Tikhonov.discrepancyParam_spec K d δ h_existsUnique
  have hr_data : ‖K.toEuclideanLin r - d‖ = δ := by
    simpa [αStar, r, Tikhonov.discrepancy_eq] using hspec.2
  have hδ_nonneg : 0 ≤ δ := by
    rw [← h_data]
    exact norm_nonneg _
  -- First convert the norm bound `(1.33)` into a square bound.
  have hnorm_le : ‖r‖ ≤ ‖fTrue‖ := by
    simpa [αStar, r] using
      tikhonov_norm_le_true_of_discrepancyParam K d fTrue h_existsUnique h_data
  have hnorm_sq : ‖r‖ ^ 2 ≤ ‖fTrue‖ ^ 2 := by
    nlinarith [hnorm_le, norm_nonneg r, norm_nonneg fTrue]
  -- Rewrite the source condition through the adjoint so the residual lives in data space.
  have hAdj : LinearMap.adjoint K.toEuclideanLin = (Kᵀ).toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint K).symm
  have hsource_inner :
      inner ℝ (fTrue - r) fTrue = inner ℝ (K.toEuclideanLin (fTrue - r)) z := by
    rw [h_source, ← hAdj, LinearMap.adjoint_inner_right]
  have hsplit :
      K.toEuclideanLin (fTrue - r) = (K.toEuclideanLin fTrue - d) + (d - K.toEuclideanLin r) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Bound the two residual pairings separately by Cauchy--Schwarz.
  have hinner_bound : inner ℝ (K.toEuclideanLin (fTrue - r)) z ≤ 2 * δ * ‖z‖ := by
    rw [hsplit, inner_add_left]
    have h₁ := real_inner_le_norm (K.toEuclideanLin fTrue - d) z
    have h₂ := real_inner_le_norm (d - K.toEuclideanLin r) z
    have hr_rev : ‖d - K.toEuclideanLin r‖ = δ := by
      simpa [norm_sub_rev] using hr_data
    calc
      inner ℝ (K.toEuclideanLin fTrue - d) z + inner ℝ (d - K.toEuclideanLin r) z
          ≤ ‖K.toEuclideanLin fTrue - d‖ * ‖z‖ + ‖d - K.toEuclideanLin r‖ * ‖z‖ := by
            nlinarith [h₁, h₂]
      _ = 2 * δ * ‖z‖ := by
            rw [h_data, hr_rev]
            ring
  calc
    ‖r - fTrue‖ ^ 2 = ‖r‖ ^ 2 - 2 * inner ℝ r fTrue + ‖fTrue‖ ^ 2 := by
      rw [norm_sub_sq_real]
    _ ≤ 2 * ‖fTrue‖ ^ 2 - 2 * inner ℝ r fTrue := by
      nlinarith
    _ = 2 * inner ℝ (fTrue - r) fTrue := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]
      ring
    _ = 2 * inner ℝ (K.toEuclideanLin (fTrue - r)) z := by
      rw [hsource_inner]
    _ ≤ 4 * δ * ‖z‖ := by
      nlinarith [hinner_bound, hδ_nonneg, norm_nonneg z]

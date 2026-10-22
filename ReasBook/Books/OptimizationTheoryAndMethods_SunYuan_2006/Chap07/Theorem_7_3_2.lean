/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_3_extra_1
import Mathlib.Algebra.Group.Pi.Units
import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Order.Monotone.Basic

open Matrix

noncomputable section

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ

-- Semantic recall: `lean_leansearch` surfaced `InnerProductGeometry.angle` and `AntitoneOn`,
-- while Chapter 7 already owns the source regularized-normal-equation predicate
-- `solvesLevenbergMarquardtNormalEquation`. This item keeps the direct-gradient theorem surface
-- and reuses that owner.

/-- Helper for Chapter07 Theorem 7.3.2: the regularized normal matrix `Jᵀ * J + μI` is positive
definite for every positive damping parameter `μ`. -/
lemma regularized_normal_matrix_posDef
    (J : JacobianMatrix) {μ : ℝ} (hμ : 0 < μ) :
    (Jᵀ * J + μ • (1 : MatrixN)).PosDef := by
  -- The source proof needs invertibility of the regularized normal matrix. Positive definiteness
  -- gives that invertibility canonically.
  have hJTJ : (Jᵀ * J).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self J
  have hμI : (μ • (1 : MatrixN)).PosDef := by
    simpa using (Matrix.PosDef.one : (1 : MatrixN).PosDef).smul hμ
  exact Matrix.PosDef.posSemidef_add hJTJ hμI

/-- Helper for Chapter07 Theorem 7.3.2: any step solving the regularized normal equation is the
canonical inverse-based Levenberg-Marquardt step. -/
lemma step_eq_neg_inv_mulVec_of_solves
    (J : JacobianMatrix) (g step : Point) {μ : ℝ} (hμ : 0 < μ)
    (hstep : solvesLevenbergMarquardtNormalEquation J g μ step) :
    step = -((Jᵀ * J + μ • (1 : MatrixN))⁻¹).mulVec g := by
  let A : MatrixN := Jᵀ * J + μ • (1 : MatrixN)
  have hA : A.PosDef := by
    -- This reduces the linear-system solution to the invertible matrix owner from the previous
    -- helper.
    simpa [A] using regularized_normal_matrix_posDef J hμ
  letI : Invertible A := hA.isUnit.invertible
  have hsolve : A.mulVec step = -g := by
    simpa [A, solvesLevenbergMarquardtNormalEquation] using hstep
  have hinv : A⁻¹.mulVec (-g) = step :=
    Matrix.inv_mulVec_eq_vec (A := A) hsolve.symm
  -- Rewriting `A⁻¹ *ᵥ (-g)` as the negated inverse action yields the textbook explicit step.
  simpa [A, Matrix.mulVec_neg] using hinv.symm

/-- Helper for Chapter07 Theorem 7.3.2: when the gradient vanishes, every positive-damping
Levenberg-Marquardt step is zero. -/
lemma step_eq_zero_of_zero_gradient
    (J : JacobianMatrix) (step : Point) {μ : ℝ} (hμ : 0 < μ)
    (hstep : solvesLevenbergMarquardtNormalEquation J 0 μ step) :
    step = 0 := by
  -- The inverse formula collapses immediately when the right-hand side is the zero gradient.
  simpa using step_eq_neg_inv_mulVec_of_solves J 0 step hμ hstep

/-- Helper for Chapter07 Theorem 7.3.2: for diagonal spectral data, the inverse of
`diag λ + μI` acts coordinatewise by division by `λ i + μ`. -/
lemma diagonal_regularized_inverse_mulVec
    (diag : Fin n → ℝ) (v : Point) (μ : ℝ) (hμ : ∀ i, 0 < diag i + μ) :
    ((Matrix.diagonal diag + μ • (1 : MatrixN))⁻¹).mulVec v =
      fun i ↦ v i / (diag i + μ) := by
  -- This is the transport-free coordinate formula needed by the spectral decomposition route.
  have hdiag :
      Matrix.diagonal diag + μ • (1 : MatrixN) = Matrix.diagonal (fun i ↦ diag i + μ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal, add_comm]
    · simp [Matrix.diagonal, hij]
  rw [hdiag, Matrix.inv_diagonal]
  ext i
  -- Once the matrix is diagonalized, the inverse and matrix-vector product are coordinatewise.
  simp [Matrix.mulVec_diagonal, div_eq_mul_inv]
  have hfun_unit : IsUnit (fun j : Fin n ↦ diag j + μ) := by
    refine Pi.isUnit_iff.mpr ?_
    intro j
    exact isUnit_iff_ne_zero.mpr (by linarith [hμ j])
  have hpoint :
      Ring.inverse (fun j : Fin n ↦ diag j + μ) i = (diag i + μ)⁻¹ := by
    simpa [Pi.inv_apply] using congrFun (Ring.inverse_unit hfun_unit.unit) i
  rw [hpoint]
  rw [mul_comm]

/-- Helper for Chapter07 Theorem 7.3.2: in the nonzero-gradient regime, a positive-damping
Levenberg-Marquardt step cannot vanish. -/
lemma lm_step_ne_zero_of_nonzero_gradient
    (J : JacobianMatrix) (g step : Point) {μ : ℝ} (_hμ : 0 < μ)
    (hstep : solvesLevenbergMarquardtNormalEquation J g μ step) (hg : g ≠ 0) :
    step ≠ 0 := by
  -- A zero step would force the regularized normal equation right-hand side `-g` to be zero.
  intro hzero
  have hsolve : (Jᵀ * J + μ • (1 : MatrixN)).mulVec step = -g := by
    simpa [solvesLevenbergMarquardtNormalEquation] using hstep
  have hneg : -g = 0 := by
    simpa [hzero] using hsolve.symm
  have hg_zero : g = 0 := by
    simpa using congrArg Neg.neg hneg
  exact hg hg_zero

/-- Helper for Chapter07 Theorem 7.3.2: monotonicity of the cosine family on `Set.Ioi 0`
implies antitonicity of the corresponding angle family because `cos` is strictly decreasing on
`[0, π]`. -/
lemma angle_antitoneOn_of_cosine_monotoneOn
    (g : Point) (s : ℝ → Point)
    (hcos :
      MonotoneOn (fun μ : ℝ ↦ Real.cos (InnerProductGeometry.angle (s μ) (-g))) (Set.Ioi 0)) :
    AntitoneOn (fun μ : ℝ ↦ InnerProductGeometry.angle (s μ) (-g)) (Set.Ioi 0) := by
  intro μ hμ ν hν hμν
  -- The angle always lives in `[0, π]`, so the order can be recovered from the cosine order.
  have hμI :
      InnerProductGeometry.angle (s μ) (-g) ∈ Set.Icc (0 : ℝ) Real.pi := by
    exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  have hνI :
      InnerProductGeometry.angle (s ν) (-g) ∈ Set.Icc (0 : ℝ) Real.pi := by
    exact ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
  have hcos_le :
      Real.cos (InnerProductGeometry.angle (s μ) (-g)) ≤
        Real.cos (InnerProductGeometry.angle (s ν) (-g)) :=
    hcos hμ hν hμν
  exact (Real.strictAntiOn_cos.le_iff_ge hμI hνI).1 hcos_le

/-- Helper for Chapter07 Theorem 7.3.2: a Hermitian matrix acts diagonally in its orthonormal
eigenbasis after transporting the matrix action to Euclidean space. -/
lemma hermitian_repr_toEuclideanLin_eq_eigenvalue_mul
    (A : MatrixN) (hA : A.IsHermitian) (x : Point) (i : Fin n) :
    ((hA.eigenvectorBasis.repr (Matrix.toEuclideanLin A x)).ofLp i) =
      hA.eigenvalues i * ((hA.eigenvectorBasis.repr x).ofLp i) := by
  -- This is exactly mathlib's self-adjoint diagonalization formula, reindexed to the matrix API.
  simpa [Matrix.IsHermitian.eigenvectorBasis, Matrix.IsHermitian.eigenvalues,
    Matrix.IsHermitian.eigenvalues₀] using
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis_apply_self_apply
      finrank_euclideanSpace x ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)

/-- Helper for Chapter07 Theorem 7.3.2: adding the damping term `μI` shifts the spectral
coordinate action by `μ`. -/
lemma hermitian_repr_regularized_toEuclideanLin_eq_shifted_eigenvalue_mul
    (A : MatrixN) (hA : A.IsHermitian) (x : Point) (μ : ℝ) (i : Fin n) :
    ((hA.eigenvectorBasis.repr (Matrix.toEuclideanLin (A + μ • (1 : MatrixN)) x)).ofLp i) =
      (hA.eigenvalues i + μ) * ((hA.eigenvectorBasis.repr x).ofLp i) := by
  let b := hA.eigenvectorBasis
  show ((b.repr (Matrix.toEuclideanLin (A + μ • (1 : MatrixN)) x)).ofLp i) =
    (hA.eigenvalues i + μ) * ((b.repr x).ofLp i)
  -- Split the regularized action into the Hermitian part and the scalar identity part.
  calc
    ((b.repr (Matrix.toEuclideanLin (A + μ • (1 : MatrixN)) x)).ofLp i)
      = ((b.repr (Matrix.toEuclideanLin A x)).ofLp i) +
          ((b.repr (Matrix.toEuclideanLin (μ • (1 : MatrixN)) x)).ofLp i) := by
          simp
    _ = hA.eigenvalues i * ((b.repr x).ofLp i) + μ * ((b.repr x).ofLp i) := by
          have hdiag :
              ((b.repr (Matrix.toEuclideanLin A x)).ofLp i) =
                hA.eigenvalues i * ((b.repr x).ofLp i) := by
            simpa [b] using hermitian_repr_toEuclideanLin_eq_eigenvalue_mul A hA x i
          rw [hdiag]
          simp
    _ = (hA.eigenvalues i + μ) * ((b.repr x).ofLp i) := by
          ring

/-- Helper for Chapter07 Theorem 7.3.2: projecting the regularized normal equation onto the
eigenbasis of `Jᵀ * J` yields the source coordinate formula for the Levenberg-Marquardt step. -/
lemma lm_step_coordinate_eq_neg_repr_div_shifted_eigenvalue
    (J : JacobianMatrix) (g step : Point) {μ : ℝ} (hμ : 0 < μ)
    (hstep : solvesLevenbergMarquardtNormalEquation J g μ step) (i : Fin n) :
    let A : MatrixN := Jᵀ * J
    let hA : A.IsHermitian := by
      simpa [A] using Matrix.isHermitian_conjTranspose_mul_self J
    (((hA.eigenvectorBasis.repr step).ofLp i)) =
      -(((hA.eigenvectorBasis.repr g).ofLp i)) / (hA.eigenvalues i + μ) := by
  let A : MatrixN := Jᵀ * J
  have hA : A.IsHermitian := by
    simpa [A] using Matrix.isHermitian_conjTranspose_mul_self J
  let b := hA.eigenvectorBasis
  show ((b.repr step).ofLp i) = -((b.repr g).ofLp i) / (hA.eigenvalues i + μ)
  have hsolve :
      Matrix.toEuclideanLin (A + μ • (1 : MatrixN)) step = -g := by
    -- Rewrite the normal equation as an equality in Euclidean space before taking coordinates.
    ext k
    change (((A + μ • (1 : MatrixN)).mulVec step.ofLp) k) = (-g.ofLp) k
    simpa [A, solvesLevenbergMarquardtNormalEquation] using congrFun hstep k
  have hcoord :
      (hA.eigenvalues i + μ) * ((b.repr step).ofLp i) = -((b.repr g).ofLp i) := by
    -- The regularized action is diagonal in the eigenbasis, so one scalar equation remains.
    have hcoord_raw := congrArg (fun y : Point ↦ (b.repr y).ofLp i) hsolve
    have hdiag :
        ((b.repr (Matrix.toEuclideanLin A step)).ofLp i) =
          hA.eigenvalues i * ((b.repr step).ofLp i) := by
      simpa [A, b] using hermitian_repr_toEuclideanLin_eq_eigenvalue_mul A hA step i
    calc
      (hA.eigenvalues i + μ) * ((b.repr step).ofLp i)
        = ((b.repr (Matrix.toEuclideanLin A step)).ofLp i) + μ * ((b.repr step).ofLp i) := by
            rw [hdiag]
            ring
      _ = -((b.repr g).ofLp i) := by
            simpa [A, b, map_neg] using hcoord_raw
  have hdenom_pos : 0 < hA.eigenvalues i + μ := by
    have hnonneg : 0 ≤ hA.eigenvalues i := by
      simpa [A] using Matrix.eigenvalues_conjTranspose_mul_self_nonneg J i
    linarith
  have hdenom_ne : hA.eigenvalues i + μ ≠ 0 := ne_of_gt hdenom_pos
  -- Dividing the scalar coordinate equation by the positive shifted eigenvalue gives the formula.
  apply (eq_div_iff hdenom_ne).2
  simpa [mul_comm] using hcoord

/-- Helper for Chapter07 Theorem 7.3.2: an orthonormal-basis coordinate formula for `step`
turns `⟪step,-g⟫` into the scalar numerator from the source proof. -/
lemma parseval_inner_from_coordinate_formula
    (b : OrthonormalBasis (Fin n) ℝ Point) (g step : Point) (eigs : Fin n → ℝ) {μ : ℝ}
    (hcoord : ∀ i, ((b.repr step).ofLp i) = -(((b.repr g).ofLp i) / (eigs i + μ))) :
    inner ℝ step (-g) = ∑ i, (((b.repr g).ofLp i) ^ 2) / (eigs i + μ) := by
  -- Parseval rewrites the numerator as a sum of eigenbasis coordinates.
  calc
    inner ℝ step (-g) = ∑ i, inner ℝ step (b i) * inner ℝ (b i) (-g) := by
      simpa using (OrthonormalBasis.sum_inner_mul_inner b step (-g)).symm
    _ = ∑ i, ((b.repr step).ofLp i) * (-((b.repr g).ofLp i)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      calc
        inner ℝ step (b i) * inner ℝ (b i) (-g)
            = inner ℝ step (b i) * (-(inner ℝ (b i) g)) := by
                rw [inner_neg_right]
        _ = inner ℝ step (b i) * (-((b.repr g).ofLp i)) := by
                rw [b.repr_apply_apply]
        _ = inner ℝ (b i) step * (-((b.repr g).ofLp i)) := by
                rw [real_inner_comm]
        _ = ((b.repr step).ofLp i) * (-((b.repr g).ofLp i)) := by
                rw [← b.repr_apply_apply]
    _ = ∑ i, (-(((b.repr g).ofLp i) / (eigs i + μ))) * (-((b.repr g).ofLp i)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hcoord i]
    _ = ∑ i, (((b.repr g).ofLp i) ^ 2) / (eigs i + μ) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      ring

/-- Helper for Chapter07 Theorem 7.3.2: Parseval rewrites the squared step norm in the eigenbasis
of `Jᵀ * J`. -/
lemma parseval_norm_sq_from_coordinate_formula
    (b : OrthonormalBasis (Fin n) ℝ Point) (g step : Point) (eigs : Fin n → ℝ) {μ : ℝ}
    (hcoord : ∀ i, ((b.repr step).ofLp i) = -(((b.repr g).ofLp i) / (eigs i + μ))) :
    ‖step‖ ^ 2 = ∑ i, (((b.repr g).ofLp i) ^ 2) / (eigs i + μ) ^ 2 := by
  -- The squared norm is the Parseval sum of squared eigenbasis coordinates.
  calc
    ‖step‖ ^ 2 = ∑ i, (((b.repr step).ofLp i) ^ 2) := by
      simpa [b.repr_apply_apply] using (OrthonormalBasis.sum_sq_inner_right b step).symm
    _ = ∑ i, (((b.repr g).ofLp i) ^ 2) / (eigs i + μ) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hcoord i]
      by_cases hzero : eigs i + μ = 0
      · simp [hzero]
      · field_simp [hzero]

/-- Helper for Chapter07 Theorem 7.3.2: after diagonalizing `Jᵀ * J`, the cosine of the angle
between the Levenberg-Marquardt step and `-g` is exactly the scalar quotient from the source
proof. -/
lemma lm_diagonalized_cosine_formula
    (J : JacobianMatrix) (g step : Point) {μ : ℝ} (hμ : 0 < μ)
    (hstep : solvesLevenbergMarquardtNormalEquation J g μ step) :
    let A : MatrixN := Jᵀ * J
    let hA : A.IsHermitian := by
      simpa [A] using Matrix.isHermitian_conjTranspose_mul_self J
    let b := hA.eigenvectorBasis
    let v : Fin n → ℝ := (b.repr g).ofLp
    Real.cos (InnerProductGeometry.angle step (-g)) =
      (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ)) /
        (‖g‖ * Real.sqrt (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) ^ 2)) := by
  let A : MatrixN := Jᵀ * J
  have hA : A.IsHermitian := by
    simpa [A] using Matrix.isHermitian_conjTranspose_mul_self J
  let b := hA.eigenvectorBasis
  let v : Fin n → ℝ := (b.repr g).ofLp
  have hcoord :
      ∀ i, ((b.repr step).ofLp i) = -(((b.repr g).ofLp i) / (hA.eigenvalues i + μ)) := by
    intro i
    simpa [A, b, neg_div] using
      lm_step_coordinate_eq_neg_repr_div_shifted_eigenvalue J g step hμ hstep i
  have hinner_raw :=
    parseval_inner_from_coordinate_formula b g step hA.eigenvalues hcoord
  have hnorm_sq_raw :=
    parseval_norm_sq_from_coordinate_formula b g step hA.eigenvalues hcoord
  have hinner_eq : inner ℝ step (-g) = ∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) := by
    simpa [v] using hinner_raw
  have hnorm_sq_eq : ‖step‖ ^ 2 = ∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) ^ 2 := by
    simpa [v] using hnorm_sq_raw
  have hsum_nonneg : 0 ≤ ∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) ^ 2 := by
    simpa [hnorm_sq_eq] using (show 0 ≤ ‖step‖ ^ 2 by positivity)
  have hstep_norm :
      Real.sqrt (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) ^ 2) = ‖step‖ := by
    -- The second Parseval identity identifies the step norm with the square root of the
    -- scalar denominator from the source quotient.
    apply (Real.sqrt_eq_iff_mul_self_eq hsum_nonneg (norm_nonneg _)).2
    simpa [pow_two] using hnorm_sq_eq.symm
  show
    Real.cos (InnerProductGeometry.angle step (-g)) =
      (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ)) /
        (‖g‖ * Real.sqrt (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) ^ 2))
  -- Substituting the Parseval formulas into `cos_angle` yields the spectral quotient directly.
  calc
    Real.cos (InnerProductGeometry.angle step (-g))
        = inner ℝ step (-g) / (‖step‖ * ‖-g‖) := by
            rw [InnerProductGeometry.cos_angle]
    _ = (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ)) / (‖step‖ * ‖g‖) := by
          rw [hinner_eq]
          simp
    _ = (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ)) /
          (‖g‖ * Real.sqrt (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) ^ 2)) := by
          rw [mul_comm, ← hstep_norm]

/-- Helper for Chapter07 Theorem 7.3.2: positive damping shifts every nonnegative spectral value
into the open positive ray. -/
lemma spectral_shifted_pos
    {eigs : Fin n → ℝ} (heigs : ∀ i, 0 ≤ eigs i) {μ : ℝ} (hμ : 0 < μ) (i : Fin n) :
    0 < eigs i + μ := by
  -- The source proof uses `λᵢ + μ > 0` repeatedly when normalizing the scalar quotient.
  linarith [heigs i, hμ]

/-- Helper for Chapter07 Theorem 7.3.2: the shifted square-sum denominator in the source quotient
is strictly positive whenever the spectral coordinates are nonzero. -/
lemma spectral_shifted_sq_sum_pos_of_nonzero
    {eigs : Fin n → ℝ} (heigs : ∀ i, 0 ≤ eigs i) {v : Fin n → ℝ} (hv : v ≠ 0)
    {μ : ℝ} (hμ : 0 < μ) :
    0 < ∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    ext j
    by_contra hj
    exact h ⟨j, hj⟩
  have hshift : 0 < eigs i + μ := spectral_shifted_pos heigs hμ i
  have hterm_pos : 0 < (v i) ^ 2 / (eigs i + μ) ^ 2 := by
    have hnum : 0 < (v i) ^ 2 := by
      nlinarith [sq_pos_of_ne_zero hi]
    exact div_pos hnum (pow_pos hshift 2)
  have hle :
      (v i) ^ 2 / (eigs i + μ) ^ 2 ≤ ∑ j, (v j) ^ 2 / (eigs j + μ) ^ 2 := by
    simpa using
      (Finset.single_le_sum (f := fun j : Fin n ↦ (v j) ^ 2 / (eigs j + μ) ^ 2)
        (fun j _ ↦ by
          exact div_nonneg (sq_nonneg _) (pow_two_nonneg _))
        (by simp : i ∈ (Finset.univ : Finset (Fin n))))
  -- A single strictly positive summand already forces the full finite sum to be positive.
  exact lt_of_lt_of_le hterm_pos hle

/-- Helper for Chapter07 Theorem 7.3.2: one shifted reciprocal spectral term has derivative
`-c / (λ + μ)^2` on the positive damping ray. -/
lemma shiftedInverseTerm_hasDerivWithinAt
    (coeff eig : ℝ) {μ : ℝ} (hshift : 0 < eig + μ) :
    HasDerivWithinAt
      (fun t : ℝ ↦ coeff / (eig + t))
      (-(coeff / (eig + μ) ^ 2))
      (Set.Ioi 0) μ := by
  have hden : HasDerivWithinAt (fun t : ℝ ↦ eig + t) 1 (Set.Ioi 0) μ := by
    -- The denominator is affine in `t`, so its derivative is the constant `1`.
    simpa using (hasDerivWithinAt_id μ (Set.Ioi 0)).const_add eig
  have hinv := hden.inv hshift.ne'
  have hderiv_eq : coeff * (-1 / (eig + μ) ^ 2) = -(coeff / (eig + μ) ^ 2) := by
    ring
  -- Rescale the reciprocal derivative by the constant numerator `coeff`.
  simpa [Pi.inv_apply, Pi.mul_apply, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hderiv_eq ▸ hinv.const_mul coeff

/-- Helper for Chapter07 Theorem 7.3.2: one shifted squared reciprocal spectral term has
derivative `-2c / (λ + μ)^3` on the positive damping ray. -/
lemma shiftedInverseSqTerm_hasDerivWithinAt
    (coeff eig : ℝ) {μ : ℝ} (hshift : 0 < eig + μ) :
    HasDerivWithinAt
      (fun t : ℝ ↦ coeff / (eig + t) ^ 2)
      (-(2 * coeff / (eig + μ) ^ 3))
      (Set.Ioi 0) μ := by
  have hden : HasDerivWithinAt (fun t : ℝ ↦ eig + t) 1 (Set.Ioi 0) μ := by
    -- As above, the shifted denominator is affine in the damping parameter.
    simpa using (hasDerivWithinAt_id μ (Set.Ioi 0)).const_add eig
  have hinv := hden.inv hshift.ne'
  have hinvSq := hinv.mul hinv
  have hmul := hinvSq.const_mul coeff
  have hmul' :
      HasDerivWithinAt
        (fun t : ℝ ↦ coeff * ((fun t : ℝ ↦ eig + t)⁻¹ t * (fun t : ℝ ↦ eig + t)⁻¹ t))
        (-(2 * coeff / (eig + μ) ^ 3))
        (Set.Ioi 0) μ := by
    -- Normalize the derivative value of the inverse-square product.
    refine hmul.congr_deriv ?_
    simp [Pi.inv_apply, div_eq_mul_inv, pow_two, pow_three, mul_assoc, mul_left_comm, mul_comm]
    field_simp [hshift.ne']
    ring
  -- Replace the inverse-square product with the equivalent reciprocal-square quotient.
  refine hmul'.congr ?_ ?_
  · intro t ht
    simp [Pi.inv_apply, div_eq_mul_inv, pow_two]
  · simp [Pi.inv_apply, div_eq_mul_inv, pow_two]

/-- Helper for Chapter07 Theorem 7.3.2: the Cauchy-Schwarz defect from (7.3.16) is nonnegative. -/
lemma spectral_cauchy_schwarz_defect_nonneg
    {eigs : Fin n → ℝ} (heigs : ∀ i, 0 ≤ eigs i) (v : Fin n → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    0 ≤
      (∑ i, (v i) ^ 2 / (eigs i + μ)) * (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 3) -
        (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2) ^ 2 := by
  have hcs :
      (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2) ^ 2 ≤
        (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 3) * (∑ i, (v i) ^ 2 / (eigs i + μ)) := by
    -- Apply the finitary squared Cauchy-Schwarz inequality directly to the three spectral sums.
    exact
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := (Finset.univ : Finset (Fin n)))
        (r := fun i ↦ (v i) ^ 2 / (eigs i + μ) ^ 2)
        (f := fun i ↦ (v i) ^ 2 / (eigs i + μ) ^ 3)
        (g := fun i ↦ (v i) ^ 2 / (eigs i + μ))
        (fun i _ ↦ by
          exact div_nonneg (sq_nonneg _) (pow_nonneg (spectral_shifted_pos heigs hμ i).le 3))
        (fun i _ ↦ by
          exact div_nonneg (sq_nonneg _) (spectral_shifted_pos heigs hμ i).le)
        (fun i _ ↦ by
          have hshift : 0 < eigs i + μ := spectral_shifted_pos heigs hμ i
          field_simp [hshift.ne']
          nlinarith)
  -- Rewriting the inequality into the target defect form finishes the sign computation.
  nlinarith [hcs]

/-- Helper for Chapter07 Theorem 7.3.2: the first shifted spectral sum differentiates to the
negative second shifted sum. -/
lemma spectral_inverse_sum_hasDerivWithinAt
    {eigs : Fin n → ℝ} (heigs : ∀ i, 0 ≤ eigs i) (v : Fin n → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    HasDerivWithinAt
      (fun t : ℝ ↦ ∑ i, (v i) ^ 2 / (eigs i + t))
      (-(∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2))
      (Set.Ioi 0) μ := by
  -- Sum the one-dimensional reciprocal derivative over the finite spectral index set.
  simpa using
    (HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset (Fin n))) fun i _ ↦
      shiftedInverseTerm_hasDerivWithinAt ((v i) ^ 2) (eigs i) (spectral_shifted_pos heigs hμ i))

/-- Helper for Chapter07 Theorem 7.3.2: the second shifted spectral sum differentiates to the
negative doubled third shifted sum. -/
lemma spectral_inverse_sq_sum_hasDerivWithinAt
    {eigs : Fin n → ℝ} (heigs : ∀ i, 0 ≤ eigs i) (v : Fin n → ℝ) {μ : ℝ} (hμ : 0 < μ) :
    HasDerivWithinAt
      (fun t : ℝ ↦ ∑ i, (v i) ^ 2 / (eigs i + t) ^ 2)
      (-(2 * ∑ i, (v i) ^ 2 / (eigs i + μ) ^ 3))
      (Set.Ioi 0) μ := by
  -- Sum the coordinatewise cubic-reciprocal derivative formulas over the spectral index set.
  have hsum :
      HasDerivWithinAt
        (fun t : ℝ ↦ ∑ i, (v i) ^ 2 / (eigs i + t) ^ 2)
        (∑ i, -(2 * (v i) ^ 2 / (eigs i + μ) ^ 3))
        (Set.Ioi 0) μ := by
    exact
      HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset (Fin n))) fun i _ ↦
        shiftedInverseSqTerm_hasDerivWithinAt ((v i) ^ 2) (eigs i)
          (spectral_shifted_pos heigs hμ i)
  -- Reassociate the constant factor `2` outside the finite sum.
  refine hsum.congr_deriv ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- Helper for Chapter07 Theorem 7.3.2: the source scalar quotient has the derivative formula
from (7.3.15). -/
lemma lm_scalar_quotient_hasDerivWithinAt
    {eigs : Fin n → ℝ} (heigs : ∀ i, 0 ≤ eigs i) (v : Fin n → ℝ) (hv : v ≠ 0)
    {μ : ℝ} (hμ : 0 < μ) :
    HasDerivWithinAt
      (fun t : ℝ ↦
        (∑ i, (v i) ^ 2 / (eigs i + t)) /
          Real.sqrt (∑ i, (v i) ^ 2 / (eigs i + t) ^ 2))
      (((∑ i, (v i) ^ 2 / (eigs i + μ)) * (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 3) -
            (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2) ^ 2) /
          ((∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2) *
            Real.sqrt (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2)))
      (Set.Ioi 0) μ := by
  let s1 : ℝ → ℝ := fun t ↦ ∑ i, (v i) ^ 2 / (eigs i + t)
  let s2 : ℝ → ℝ := fun t ↦ ∑ i, (v i) ^ 2 / (eigs i + t) ^ 2
  let s3 : ℝ := ∑ i, (v i) ^ 2 / (eigs i + μ) ^ 3
  have hs2_pos : 0 < s2 μ := by
    -- The square-sum denominator is strictly positive on the nonzero-gradient branch.
    simpa [s2] using spectral_shifted_sq_sum_pos_of_nonzero heigs hv hμ
  have hs2_ne : s2 μ ≠ 0 := ne_of_gt hs2_pos
  have hsqrt_ne : Real.sqrt (s2 μ) ≠ 0 := (Real.sqrt_pos.2 hs2_pos).ne'
  have hs1_deriv : HasDerivWithinAt s1 (-(s2 μ)) (Set.Ioi 0) μ := by
    -- The numerator derivative is the first reciprocal-sum identity.
    simpa [s1, s2] using spectral_inverse_sum_hasDerivWithinAt heigs v hμ
  have hs2_deriv : HasDerivWithinAt s2 (-(2 * s3)) (Set.Ioi 0) μ := by
    -- The denominator-square derivative is the second reciprocal-sum identity.
    simpa [s2, s3] using spectral_inverse_sq_sum_hasDerivWithinAt heigs v hμ
  have hsqrt_deriv :
      HasDerivWithinAt (fun t : ℝ ↦ Real.sqrt (s2 t))
        (-(2 * s3) / (2 * Real.sqrt (s2 μ)))
        (Set.Ioi 0) μ := by
    -- Differentiate the square root of the positive denominator sum.
    simpa using hs2_deriv.sqrt hs2_ne
  have hquot :
      HasDerivWithinAt
        (fun t : ℝ ↦ s1 t / Real.sqrt (s2 t))
        (((-(s2 μ)) * Real.sqrt (s2 μ) -
              s1 μ * (-(2 * s3) / (2 * Real.sqrt (s2 μ)))) /
            (Real.sqrt (s2 μ)) ^ 2)
        (Set.Ioi 0) μ := by
    -- The quotient rule assembles the source derivative before algebraic normalization.
    exact hs1_deriv.div hsqrt_deriv hsqrt_ne
  have hsqrt_sq : (Real.sqrt (s2 μ)) ^ 2 = s2 μ := by
    rw [Real.sq_sqrt hs2_pos.le]
  have hsimp :
      (((-(s2 μ)) * Real.sqrt (s2 μ) -
            s1 μ * (-(2 * s3) / (2 * Real.sqrt (s2 μ)))) /
          (Real.sqrt (s2 μ)) ^ 2) =
        ((s1 μ * s3 - (s2 μ) ^ 2) / (s2 μ * Real.sqrt (s2 μ))) := by
    -- Clearing the positive square-root denominator recovers the exact scalar formula (7.3.15).
    rw [hsqrt_sq]
    field_simp [hs2_ne, hsqrt_ne]
    nlinarith [hsqrt_sq]
  simpa [s1, s2, s3] using hsimp ▸ hquot

/-- Helper for Chapter07 Theorem 7.3.2: the scalar quotient from the source proof is monotone on
`Set.Ioi 0`. -/
lemma lm_scalar_quotient_monotone
    {eigs : Fin n → ℝ} (heigs : ∀ i, 0 ≤ eigs i) (v : Fin n → ℝ) (hv : v ≠ 0) :
    MonotoneOn
      (fun μ : ℝ ↦
        (∑ i, (v i) ^ 2 / (eigs i + μ)) /
          Real.sqrt (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2))
      (Set.Ioi 0) := by
  let f' : ℝ → ℝ := fun μ ↦
    (((∑ i, (v i) ^ 2 / (eigs i + μ)) * (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 3) -
          (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2) ^ 2) /
        ((∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2) *
          Real.sqrt (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2)))
  refine monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Set.Ioi 0)
      (f := fun μ : ℝ ↦
        (∑ i, (v i) ^ 2 / (eigs i + μ)) /
          Real.sqrt (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2))
      (f' := f')
      (convex_Ioi (0 : ℝ)) ?_ ?_ ?_
  · intro μ hμ
    -- The derivative formula immediately provides continuity on the positive damping ray.
    exact (lm_scalar_quotient_hasDerivWithinAt heigs v hv hμ).continuousWithinAt
  · intro μ hμ
    have hμ' : 0 < μ := by
      simpa using hμ
    -- On the interior of `Set.Ioi 0`, the derivative is exactly the source scalar formula.
    simpa [f'] using lm_scalar_quotient_hasDerivWithinAt heigs v hv hμ'
  · intro μ hμ
    have hμ' : 0 < μ := by
      simpa using hμ
    have hnum :
        0 ≤
          (∑ i, (v i) ^ 2 / (eigs i + μ)) * (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 3) -
            (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2) ^ 2 := by
      exact spectral_cauchy_schwarz_defect_nonneg heigs v hμ'
    have hsq_pos :
        0 < ∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2 := by
      exact spectral_shifted_sq_sum_pos_of_nonzero heigs hv hμ'
    have hdenom_pos :
        0 <
          (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2) *
            Real.sqrt (∑ i, (v i) ^ 2 / (eigs i + μ) ^ 2) := by
      -- Both factors in the derivative denominator are strictly positive on `μ > 0`.
      exact mul_pos hsq_pos (Real.sqrt_pos.2 hsq_pos)
    simpa [f'] using div_nonneg hnum hdenom_pos.le

/-- Helper for Chapter07 Theorem 7.3.2: the nonzero-gradient branch reduces to the textbook
spectral-coordinate monotonicity argument for the cosine of the angle. -/
lemma lm_angle_antitone_of_nonzero_gradient
    (J : JacobianMatrix) (g : Point) (s : ℝ → Point)
    (h_step : ∀ ⦃μ : ℝ⦄, 0 < μ → solvesLevenbergMarquardtNormalEquation J g μ (s μ))
    (hg : g ≠ 0) :
    AntitoneOn (fun μ : ℝ ↦ InnerProductGeometry.angle (s μ) (-g)) (Set.Ioi 0) := by
  -- Route correction: the remaining branch must follow the source proof by diagonalizing
  -- `Jᵀ * J`, rewriting the cosine in spectral coordinates, and applying Cauchy-Schwarz to the
  -- derivative formula. The structural inverse and diagonal helpers above stabilize that route.
  refine angle_antitoneOn_of_cosine_monotoneOn g s ?_
  have hs_ne : ∀ ⦃μ : ℝ⦄, 0 < μ → s μ ≠ 0 := by
    intro μ hμ
    -- The spectral rewrite only makes sense on the nontrivial branch, so record that the LM
    -- step stays nonzero whenever the gradient is nonzero.
    exact lm_step_ne_zero_of_nonzero_gradient J g (s μ) hμ (h_step hμ) hg
  let A : MatrixN := Jᵀ * J
  have hA : A.IsHermitian := by
    simpa [A] using Matrix.isHermitian_conjTranspose_mul_self J
  let b := hA.eigenvectorBasis
  let v : Fin n → ℝ := (b.repr g).ofLp
  have hcos_formula :
      ∀ ⦃μ : ℝ⦄, 0 < μ →
        Real.cos (InnerProductGeometry.angle (s μ) (-g)) =
          (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ)) /
            (‖g‖ * Real.sqrt (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) ^ 2)) := by
    intro μ hμ
    -- Route correction: the source proof first rewrites the cosine into a scalar quotient.
    simpa [A, b, v] using lm_diagonalized_cosine_formula J g (s μ) hμ (h_step hμ)
  have heigs_nonneg : ∀ i, 0 ≤ hA.eigenvalues i := by
    intro i
    simpa [A] using Matrix.eigenvalues_conjTranspose_mul_self_nonneg J i
  have hv : v ≠ 0 := by
    -- The spectral coordinates vanish exactly when `g` vanishes, which is excluded here.
    intro hv0
    apply hg
    apply b.repr.injective
    ext i
    simpa [v] using congrFun hv0 i
  have hquot_monotone :
      MonotoneOn
        (fun μ : ℝ ↦
          (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ)) /
            Real.sqrt (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) ^ 2))
        (Set.Ioi 0) :=
    lm_scalar_quotient_monotone heigs_nonneg v hv
  intro μ hμ ν hν hμν
  -- The source quotient is monotone, and dividing by the fixed positive constant `‖g‖`
  -- preserves that order.
  change
    Real.cos (InnerProductGeometry.angle (s μ) (-g)) ≤
      Real.cos (InnerProductGeometry.angle (s ν) (-g))
  rw [hcos_formula hμ, hcos_formula hν]
  have hscaled :
      ((∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ)) /
          Real.sqrt (∑ i, (v i) ^ 2 / (hA.eigenvalues i + μ) ^ 2)) /
        ‖g‖ ≤
        ((∑ i, (v i) ^ 2 / (hA.eigenvalues i + ν)) /
            Real.sqrt (∑ i, (v i) ^ 2 / (hA.eigenvalues i + ν) ^ 2)) /
          ‖g‖ := by
    exact div_le_div_of_nonneg_right (hquot_monotone hμ hν hμν) (norm_nonneg g)
  simpa [div_div, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Chapter07 Theorem 7.3.2: fix a Jacobian matrix `J` and a vector `g`, and for each
damping parameter `μ > 0` let `s μ` solve the regularized normal equation
`(Jᵀ * J + μ • 1).mulVec (s μ) = -g`. Then the angle between `s μ` and `-g` is antitone on
`Set.Ioi 0`, so it does not increase as `μ` increases. -/
theorem levenbergMarquardtAngle_antitoneOn
    (J : JacobianMatrix) (g : Point) (s : ℝ → Point)
    (h_step : ∀ ⦃μ : ℝ⦄, 0 < μ → solvesLevenbergMarquardtNormalEquation J g μ (s μ)) :
    AntitoneOn (fun μ : ℝ ↦ InnerProductGeometry.angle (s μ) (-g)) (Set.Ioi 0) := by
  by_cases hg : g = 0
  · intro μ hμ ν hν hμν
    -- In the zero-gradient branch, both steps vanish, so the angle is constantly `π / 2`.
    have hsμ : s μ = 0 := step_eq_zero_of_zero_gradient J (s μ) hμ <| by
      simpa [hg] using h_step hμ
    have hsν : s ν = 0 := step_eq_zero_of_zero_gradient J (s ν) hν <| by
      simpa [hg] using h_step hν
    simp [hg, hsμ, hsν]
  · -- The nonzero-gradient branch is exactly the source spectral-coordinate argument.
    exact lm_angle_antitone_of_nonzero_gradient J g s h_step hg

end

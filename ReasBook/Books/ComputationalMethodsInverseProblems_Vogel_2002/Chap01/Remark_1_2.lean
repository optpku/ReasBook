/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_4
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_4.ErrorTerms
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_5
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2.Operator
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open Filter
open scoped Matrix Topology

namespace FilterRegularization

noncomputable section

universe u

variable {n : Type u}
variable [Fintype n] [DecidableEq n]

/-- Helper for Remark 1.2-extra-1: transposing an orthogonal matrix keeps it in
`Matrix.orthogonalGroup n ℝ`. -/
lemma transpose_mem_orthogonalGroup
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ) :
    Aᵀ ∈ Matrix.orthogonalGroup n ℝ := by
  -- Rewrite orthogonality through the defining transpose identity.
  rw [Matrix.mem_orthogonalGroup_iff']
  simpa [Matrix.transpose_mul] using
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := A)).1 hA

/-- Helper for Remark 1.2-extra-1: an orthogonal matrix followed by its
transpose acts as the identity on `EuclideanSpace ℝ n`. -/
lemma orthogonal_toEuclideanLin_transpose_apply
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x) = x := by
  have hA' : Aᵀ * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := A)).1 hA
  -- Convert matrix multiplication into composition of the associated linear maps.
  calc
    Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x)
        = Matrix.toEuclideanLin (Aᵀ * A) x := by
            simp [Matrix.toEuclideanLin]
    _ = x := by
      rw [hA']
      simp [Matrix.toEuclideanLin]

/-- Helper for Remark 1.2-extra-1: an orthogonal matrix and its transpose also
cancel in the opposite order on `EuclideanSpace ℝ n`. -/
lemma orthogonal_toEuclideanLin_apply_transpose
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin Aᵀ x) = x := by
  have hA' : A * Aᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := A)).1 hA
  -- Use the forward orthogonality identity for the reversed composition.
  calc
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin Aᵀ x)
        = Matrix.toEuclideanLin (A * Aᵀ) x := by
            simp [Matrix.toEuclideanLin]
    _ = x := by
      rw [hA']
      simp [Matrix.toEuclideanLin]

/-- Helper for Remark 1.2-extra-1: an orthogonal matrix preserves Euclidean
norm squares through `Matrix.toEuclideanLin`. -/
lemma orthogonal_toEuclideanLin_norm_sq_eq
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin A x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hAtA : Aᵀ * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := A)).1 hA
  -- Expand both norms into coordinate sums and move `A` across the dot product.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  calc
    ∑ i, (A *ᵥ x.ofLp) i ^ 2 = (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) := by
          simp [dotProduct, pow_two]
    _ = x.ofLp ⬝ᵥ (Aᵀ *ᵥ (A *ᵥ x.ofLp)) := by
          rw [Matrix.dotProduct_transpose_mulVec]
    _ = x.ofLp ⬝ᵥ x.ofLp := by
          simp [Matrix.mulVec_mulVec, hAtA]
    _ = ∑ i, x.ofLp i ^ 2 := by
          simp [dotProduct, pow_two]

/-- Helper for Remark 1.2-extra-1: an orthogonal matrix preserves Euclidean
norms through `Matrix.toEuclideanLin`. -/
lemma orthogonal_toEuclideanLin_norm_map
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
  -- Extract the norm identity from the squared norm identity and nonnegativity.
  have hsq := orthogonal_toEuclideanLin_norm_sq_eq A hA x
  nlinarith [hsq, norm_nonneg (Matrix.toEuclideanLin A x), norm_nonneg x]

/-- Helper for Remark 1.2-extra-1: the scalar filter bias
`w α (σ ^ 2) - 1` tends to `0` as `α → 0+` for the TSVD and Tikhonov
filters. -/
lemma filterValueSubOne_tendstoZero_of_eq_tsvd_or_tikhonov
    {w : ℝ → ℝ → ℝ} {σ : ℝ}
    (hσ : 0 < σ)
    (h_filter : w = SpectralFilter.tsvd ∨ w = SpectralFilter.tikhonov) :
    Tendsto
      (fun α : ℝ ↦ w α (σ ^ 2) - 1)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 0) := by
  rcases h_filter with rfl | rfl
  · have hσsq : 0 < σ ^ 2 := by positivity
    -- Near `0+`, the TSVD coefficient is identically `1`, so the bias vanishes.
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards
      [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hσsq)] with α hα hlt
    rw [Set.mem_Iio] at hlt
    simp [SpectralFilter.tsvd, hlt.le]
  · have hcont :
        ContinuousAt (fun α : ℝ ↦ SpectralFilter.tikhonov α (σ ^ 2) - 1) 0 := by
      -- The Tikhonov bias is a rational function with nonzero denominator at `0`.
      refine
        (continuousAt_const.div (continuousAt_id.add continuousAt_const) ?_).sub
          continuousAt_const
      have hσsq_ne : (σ ^ 2 : ℝ) ≠ 0 := by positivity
      simpa using hσsq_ne
    simpa [SpectralFilter.tikhonov, hσ.ne', pow_two] using hcont.continuousWithinAt.tendsto

/-- Helper for Remark 1.2-extra-1: the truncation error takes the stable
diagonal-bias form in SVD coordinates. -/
lemma truncationError_eq_orthogonalDiagonalBias
    (K U V : Matrix n n ℝ) (s : n → ℝ) (fTrue : EuclideanSpace ℝ n)
    (w : ℝ → ℝ → ℝ) (α : ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i) :
    truncationError
        (operator U V s w α)
        (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
        fTrue =
      Matrix.toEuclideanLin V
        (Matrix.toEuclideanLin
          (Matrix.diagonal (fun i ↦ w α (s i ^ 2) - 1))
          (Matrix.toEuclideanLin Vᵀ fTrue)) := by
  let dFilter : n → ℝ := fun i ↦ w α (s i ^ 2) / s i
  let dWeight : n → ℝ := fun i ↦ w α (s i ^ 2)
  let y : EuclideanSpace ℝ n := Matrix.toEuclideanLin Vᵀ fTrue
  have hUtU : Uᵀ * U = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := U)).1 hU
  have hDiagMul :
      Matrix.diagonal dFilter * Matrix.diagonal s = Matrix.diagonal dWeight := by
    -- Collapse the reciprocal in the filter matrix against the singular values.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [dFilter, dWeight, (hs_pos i).ne']
    · simp [hij, dFilter, dWeight]
  have hOperatorMatrixMul :
      operatorMatrix U V s w α * K = V * Matrix.diagonal dWeight * Vᵀ := by
    -- Expand the SVD factors and collapse the orthogonal middle factor.
    calc
      operatorMatrix U V s w α * K
          = (V * Matrix.diagonal dFilter * Uᵀ) * (U * Matrix.diagonal s * Vᵀ) := by
              rw [FilterRegularization.operatorMatrix_def, hK]
      _ = V * (Matrix.diagonal dFilter * (Uᵀ * U) * Matrix.diagonal s) * Vᵀ := by
            simp [Matrix.mul_assoc]
      _ = V * (Matrix.diagonal dFilter * Matrix.diagonal s) * Vᵀ := by
            rw [hUtU]
            simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal dWeight * Vᵀ := by
            rw [hDiagMul]
  have hOperatorOnData :
      operator U V s w α (Matrix.toEuclideanLin K fTrue) =
        Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin (Matrix.diagonal dWeight) y) := by
    -- Push the forward model through the reconstruction operator to isolate the diagonal core.
    rw [operator_apply]
    calc
      Matrix.toEuclideanLin (operatorMatrix U V s w α) (Matrix.toEuclideanLin K fTrue)
          = Matrix.toEuclideanLin (operatorMatrix U V s w α * K) fTrue := by
              simp [Matrix.toEuclideanLin]
      _ = Matrix.toEuclideanLin (V * Matrix.diagonal dWeight * Vᵀ) fTrue := by
            rw [hOperatorMatrixMul]
      _ = Matrix.toEuclideanLin V
            (Matrix.toEuclideanLin (Matrix.diagonal dWeight) y) := by
            simp [y, Matrix.toEuclideanLin]
  have hTrue : fTrue = Matrix.toEuclideanLin V y := by
    -- Recover `fTrue` by canceling the `Vᵀ` coordinate change.
    simp [y, orthogonal_toEuclideanLin_apply_transpose, hV]
  -- Rewrite the truncation error as a diagonal bias inside the outer orthogonal factor.
  rw [FilterRegularization.truncationError, sub_apply,
    ContinuousLinearMap.comp_apply, one_apply_eq_self]
  calc
    operator U V s w α (Matrix.toEuclideanLin K fTrue) - fTrue
        = Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal dWeight) y) -
            Matrix.toEuclideanLin V y := by
              rw [hOperatorOnData, hTrue]
    _ = Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin (Matrix.diagonal dWeight) y - y) := by
          simp
    _ =
      Matrix.toEuclideanLin V
        (Matrix.toEuclideanLin
          (Matrix.diagonal (fun i ↦ w α (s i ^ 2) - 1)) y) := by
            congr 1
            ext i
            simp [dWeight, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
            ring
    _ =
      Matrix.toEuclideanLin V
        (Matrix.toEuclideanLin
          (Matrix.diagonal (fun i ↦ w α (s i ^ 2) - 1))
          (Matrix.toEuclideanLin Vᵀ fTrue)) := by
            simp [y]

/-- Helper for Remark 1.2-extra-1: a diagonal matrix acts coordinatewise on the
Euclidean norm square. -/
lemma diagonal_toEuclideanLin_normSq
    (a : n → ℝ) (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin (Matrix.diagonal a) x‖ ^ 2 =
      ∑ i, (a i) ^ 2 * (x i) ^ 2 := by
  -- `EuclideanSpace.real_norm_sq_eq` turns the claim into a coordinatewise identity.
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal, pow_two,
    mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Remark 1.2-extra-1: a diagonal operator on `EuclideanSpace ℝ n`
is bounded by the coordinatewise supremum of its diagonal entries. -/
lemma diagonal_toEuclideanLin_norm_le_of_forall
    (a : n → ℝ) (C : ℝ) (x : EuclideanSpace ℝ n)
    (hC_nonneg : 0 ≤ C)
    (hC : ∀ i, |a i| ≤ C) :
    ‖Matrix.toEuclideanLin (Matrix.diagonal a) x‖ ≤ C * ‖x‖ := by
  have hsq :
      ‖Matrix.toEuclideanLin (Matrix.diagonal a) x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    -- Square the norm estimate and compare the diagonal action coordinatewise.
    rw [diagonal_toEuclideanLin_normSq]
    calc
      ∑ i, (a i) ^ 2 * (x i) ^ 2 ≤ ∑ i, C ^ 2 * (x i) ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have ha_sq : (a i) ^ 2 ≤ C ^ 2 := by
              have habs := abs_le.mp (hC i)
              nlinarith [habs.1, habs.2]
            exact mul_le_mul_of_nonneg_right ha_sq (sq_nonneg (x i))
      _ = C ^ 2 * ∑ i, (x i) ^ 2 := by
            rw [Finset.mul_sum]
      _ = C ^ 2 * ‖x‖ ^ 2 := by
            rw [← EuclideanSpace.real_norm_sq_eq x]
      _ = (C * ‖x‖) ^ 2 := by
            ring
  have hRight_nonneg : 0 ≤ C * ‖x‖ := mul_nonneg hC_nonneg (norm_nonneg x)
  exact (sq_le_sq₀ (norm_nonneg _) hRight_nonneg).1 hsq

/-- Helper for Remark 1.2-extra-1: for `0 < p < 2`, the scalar noise factor
`δ / Real.sqrt (δ ^ p)` tends to `0` as `δ → 0+`. -/
lemma deltaDivSqrtRpow_tendstoZero
    {p : ℝ} (_hp_pos : 0 < p) (hp_lt : p < 2) :
    Tendsto
      (fun δ : ℝ ↦ δ / Real.sqrt (Real.rpow δ p))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 0) := by
  have hExpPos : 0 < 1 - p / 2 := by
    nlinarith
  have hId : Tendsto (fun δ : ℝ ↦ δ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ℝ)) := by
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hRpow :
      Tendsto
        (fun δ : ℝ ↦ δ ^ (1 - p / 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : ℝ)) :=
    Filter.Tendsto.rpow_const_nhds_zero hId hExpPos
  have hEq :
      (fun δ : ℝ ↦ δ ^ (1 - p / 2)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun δ : ℝ ↦ δ / Real.sqrt (Real.rpow δ p) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    calc
      δ ^ (1 - p / 2) = δ ^ ((1 : ℝ) - p / 2) := by
            rfl
      _ = δ ^ (1 : ℝ) / δ ^ (p / 2) := by
            rw [Real.rpow_sub hδ (1 : ℝ) (p / 2)]
      _ = δ / δ ^ (p / 2) := by
            rw [Real.rpow_one]
      _ = δ / Real.sqrt (Real.rpow δ p) := by
            have hmul : (δ ^ p) ^ (1 / 2 : ℝ) = δ ^ (p / 2) := by
              calc
                (δ ^ p) ^ (1 / 2 : ℝ) = δ ^ (p * (1 / 2 : ℝ)) := by
                      symm
                      exact Real.rpow_mul hδ.le p (1 / 2 : ℝ)
                _ = δ ^ (p / 2) := by
                      congr 1
                      ring
            rw [Real.sqrt_eq_rpow]
            change δ / δ ^ (p / 2) = δ / ((δ ^ p) ^ (1 / 2 : ℝ))
            rw [hmul]
  -- Rewrite the scalar factor to a single positive real power on `0+`.
  exact hRpow.congr' hEq

/-- For Remark 1.2-extra-1 (1), in the square finite-dimensional SVD specialization
used by the local Chapter 1 matrix/operator API, if `w` is either the TSVD
filter or the Tikhonov filter, then the truncation error for the reconstruction
operator `FilterRegularization.operator U V s w α` tends to `0` as `α → 0+`. -/
theorem truncationErrorTendstoZero
    (K U V : Matrix n n ℝ) (s : n → ℝ) (fTrue : EuclideanSpace ℝ n)
    (w : ℝ → ℝ → ℝ)
    (h_filter : w = SpectralFilter.tsvd ∨ w = SpectralFilter.tikhonov)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i) :
    Tendsto
      (fun α : ℝ ↦
        truncationError
          (operator U V s w α)
          (LinearMap.toContinuousLinearMap <|
            Matrix.toEuclideanLin K)
          fTrue)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (0 : EuclideanSpace ℝ n)) := by
  let y : EuclideanSpace ℝ n := Matrix.toEuclideanLin Vᵀ fTrue
  have hInnerCoord :
      Tendsto
        (fun α : ℝ ↦ fun i : n ↦ (w α (s i ^ 2) - 1) * y i)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : n → ℝ)) := by
    -- Each coordinate of the diagonal bias tends to zero by the scalar filter limit.
    refine tendsto_pi_nhds.2 ?_
    intro i
    have hCoeff :
        Tendsto
          (fun α : ℝ ↦ w α (s i ^ 2) - 1)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (𝓝 (0 : ℝ)) :=
      filterValueSubOne_tendstoZero_of_eq_tsvd_or_tikhonov (hs_pos i) h_filter
    simpa using hCoeff.mul tendsto_const_nhds
  have hToLp :
      Tendsto
        (WithLp.toLp 2 : (n → ℝ) → EuclideanSpace ℝ n)
        (𝓝 (0 : n → ℝ))
        (𝓝 (WithLp.toLp 2 (0 : n → ℝ))) := by
    have hToLpCont : Continuous (WithLp.toLp 2 : (n → ℝ) → EuclideanSpace ℝ n) := by
      fun_prop
    exact hToLpCont.continuousAt.tendsto
  have hInner :
      Tendsto
        (fun α : ℝ ↦
          Matrix.toEuclideanLin
            (Matrix.diagonal (fun i ↦ w α (s i ^ 2) - 1))
            y)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : EuclideanSpace ℝ n)) := by
    have hInnerToLp :
        Tendsto
          (fun α : ℝ ↦ WithLp.toLp 2 (fun i : n ↦ (w α (s i ^ 2) - 1) * y i))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (𝓝 (0 : EuclideanSpace ℝ n)) := by
      change
        Tendsto
          (((WithLp.toLp 2 : (n → ℝ) → EuclideanSpace ℝ n) ∘
            fun α : ℝ ↦ fun i : n ↦ (w α (s i ^ 2) - 1) * y i))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (𝓝 (0 : EuclideanSpace ℝ n))
      simpa [WithLp.toLp_zero] using hToLp.comp hInnerCoord
    refine hInnerToLp.congr' ?_
    exact Eventually.of_forall fun α ↦ by
      ext i
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  have hOuter :
      Tendsto
        (fun z : EuclideanSpace ℝ n ↦ Matrix.toEuclideanLin V z)
        (𝓝 (0 : EuclideanSpace ℝ n))
        (𝓝 (0 : EuclideanSpace ℝ n)) := by
    -- The outer orthogonal change of basis is continuous.
    simpa using
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin V)).continuous.tendsto
        (0 : EuclideanSpace ℝ n)
  -- Route correction: use the diagonal-bias normal form and coordinatewise convergence,
  -- not the earlier adjoint/unitary normalization attempt.
  refine Tendsto.congr' ?_ (hOuter.comp hInner)
  exact Eventually.of_forall fun α ↦ by
    simpa [y] using
      (truncationError_eq_orthogonalDiagonalBias K U V s fTrue w α hU hV hK hs_pos).symm

/-- For Remark 1.2-extra-1 (2), in the same square finite-dimensional SVD
specialization, if `w` is either the TSVD filter or the Tikhonov filter, then
the noise amplification error satisfies `‖e_α^noise‖ ≤ δ / Real.sqrt α` for
positive `α` whenever `‖η‖ ≤ δ`. -/
theorem noiseError_norm_le
    (U V : Matrix n n ℝ) (s : n → ℝ) (η : EuclideanSpace ℝ n)
    (w : ℝ → ℝ → ℝ) {α δ : ℝ}
    (h_filter : w = SpectralFilter.tsvd ∨ w = SpectralFilter.tikhonov)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hs_pos : ∀ i, 0 < s i)
    (hα_pos : 0 < α)
    (h_noise : ‖η‖ ≤ δ) :
    ‖noiseError (operator U V s w α) η‖ ≤
      δ / Real.sqrt α := by
  let coeff : n → ℝ := fun i ↦ w α (s i ^ 2) / s i
  let u : EuclideanSpace ℝ n := Matrix.toEuclideanLin Uᵀ η
  have hU_t : Uᵀ ∈ Matrix.orthogonalGroup n ℝ :=
    transpose_mem_orthogonalGroup U hU
  have hCoeff_nonneg : ∀ i, 0 ≤ coeff i := by
    intro i
    rcases h_filter with rfl | rfl
    · -- The TSVD coefficients are either `1 / s i` or `0`.
      by_cases hcut : α ≤ s i ^ 2
      · simp [coeff, SpectralFilter.tsvd, hcut, (hs_pos i).le]
      · simp [coeff, SpectralFilter.tsvd, hcut]
    · -- The Tikhonov coefficients are positive because all factors are positive.
      change 0 ≤ SpectralFilter.tikhonov α (s i ^ 2) / s i
      rw [SpectralFilter.tikhonovAtSquare_div_eq_ratio (hs_pos i).ne']
      exact div_nonneg (hs_pos i).le (by positivity)
  have hCore :
      noiseError (operator U V s w α) η =
        Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) := by
    -- Rewrite the propagated noise into orthogonal-diagonal coordinates.
    rw [FilterRegularization.noiseError_eq, FilterRegularization.operator_apply,
      FilterRegularization.operatorMatrix_def]
    calc
      Matrix.toEuclideanLin (V * Matrix.diagonal coeff * Uᵀ) η
        = Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff * Uᵀ) η) := by
            simp [Matrix.toEuclideanLin]
      _ = Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) := by
            congr 1
            simp [u, Matrix.toEuclideanLin]
  have hDiag :
      ‖Matrix.toEuclideanLin (Matrix.diagonal coeff) u‖ ≤ (1 / Real.sqrt α) * ‖u‖ := by
    -- Exercise 1.5 bounds each diagonal coefficient by `1 / sqrt α`.
    refine diagonal_toEuclideanLin_norm_le_of_forall coeff (1 / Real.sqrt α) u (by positivity) ?_
    intro i
    simpa [abs_of_nonneg (hCoeff_nonneg i), coeff] using
      SpectralFilter.inverseBound_of_eq_tsvd_or_tikhonov h_filter hα_pos (hs_pos i)
  -- Remove the orthogonal factors and apply the diagonal coefficient bound.
  calc
    ‖noiseError (operator U V s w α) η‖
      = ‖Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u)‖ := by
          rw [hCore]
    _ = ‖Matrix.toEuclideanLin (Matrix.diagonal coeff) u‖ := by
          rw [orthogonal_toEuclideanLin_norm_map V hV]
    _ ≤ (1 / Real.sqrt α) * ‖u‖ := hDiag
    _ = (1 / Real.sqrt α) * ‖η‖ := by
          congr 1
          simp [u, orthogonal_toEuclideanLin_norm_map Uᵀ hU_t]
    _ ≤ (1 / Real.sqrt α) * δ := by
          gcongr
    _ = δ / Real.sqrt α := by ring

/-- Remark 1.2-extra-1 (3). In the same square finite-dimensional SVD
specialization, let the reconstruction operator be
`FilterRegularization.operator U V s w α`, given by the right-hand side of
`(1.10)` for either the TSVD filter or the Tikhonov filter. If the noisy data
satisfy `d δ = Matrix.toEuclideanLin K fTrue + η δ` with `‖η δ‖ ≤ δ` for
positive `δ`, then the parameter rule `α = δ ^ p` with `0 < p` and `p < 2`
guarantees convergence of the actual reconstruction error
`operator U V s w (δ ^ p) (d δ) - fTrue` as `δ → 0+`. -/
theorem totalErrorTendstoZero
    (K U V : Matrix n n ℝ) (s : n → ℝ) (fTrue : EuclideanSpace ℝ n)
    (d η : ℝ → EuclideanSpace ℝ n) (w : ℝ → ℝ → ℝ) {p : ℝ}
    (h_filter : w = SpectralFilter.tsvd ∨ w = SpectralFilter.tikhonov)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hp_pos : 0 < p)
    (hp_lt : p < 2)
    (h_data : ∀ {δ : ℝ}, 0 < δ → d δ = Matrix.toEuclideanLin K fTrue + η δ)
    (h_noise : ∀ {δ : ℝ}, 0 < δ → ‖η δ‖ ≤ δ) :
    Tendsto
      (fun δ : ℝ ↦ operator U V s w (Real.rpow δ p) (d δ) - fTrue)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (0 : EuclideanSpace ℝ n)) := by
  have hId : Tendsto (fun δ : ℝ ↦ δ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ℝ)) := by
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hPowToZero :
      Tendsto
        (fun δ : ℝ ↦ Real.rpow δ p)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : ℝ)) :=
    Filter.Tendsto.rpow_const_nhds_zero hId hp_pos
  have hPowWithin :
      Tendsto
        (fun δ : ℝ ↦ Real.rpow δ p)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hPowToZero ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Real.rpow_pos_of_pos hδ p
  have hTrunc :
      Tendsto
        (fun δ : ℝ ↦
          truncationError
            (operator U V s w (Real.rpow δ p))
            (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
            fTrue)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : EuclideanSpace ℝ n)) :=
    (truncationErrorTendstoZero K U V s fTrue w h_filter hU hV hK hs_pos).comp hPowWithin
  have hNoiseScalar :
      Tendsto
        (fun δ : ℝ ↦ δ / Real.sqrt (Real.rpow δ p))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : ℝ)) :=
    deltaDivSqrtRpow_tendstoZero hp_pos hp_lt
  have hNoiseBound :
      ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖noiseError (operator U V s w (Real.rpow δ p)) (η δ)‖ ≤
          δ / Real.sqrt (Real.rpow δ p) := by
    -- The pointwise noise estimate specializes with `α = δ^p` on `0+`.
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hα_pos : 0 < Real.rpow δ p := Real.rpow_pos_of_pos hδ p
    exact noiseError_norm_le U V s (η δ) w h_filter hU hV hs_pos hα_pos (h_noise hδ)
  have hNoise :
      Tendsto
        (fun δ : ℝ ↦ noiseError (operator U V s w (Real.rpow δ p)) (η δ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : EuclideanSpace ℝ n)) :=
    squeeze_zero_norm' hNoiseBound hNoiseScalar
  have hSum :
      Tendsto
        (fun δ : ℝ ↦
          truncationError
            (operator U V s w (Real.rpow δ p))
            (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
            fTrue +
          noiseError (operator U V s w (Real.rpow δ p)) (η δ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : EuclideanSpace ℝ n)) := by
    simpa using hTrunc.add hNoise
  -- Rewrite the actual reconstruction error into truncation plus propagated noise.
  refine Tendsto.congr' ?_ hSum
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  simpa using
    (FilterRegularization.error_eq_truncationError_add_noiseError
      (K := LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
      (R := operator U V s w (Real.rpow δ p))
      (fTrue := fTrue)
      (d := d δ)
      (η := η δ)
      (h_data := h_data hδ)).symm

end

end FilterRegularization

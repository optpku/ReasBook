/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_4.ErrorTerms
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_5
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2.Operator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped Matrix
open FilterRegularization
open SpectralFilter

universe u

variable {n : Type u}

/-- The stronger Exercise 1.10 source condition is a special case of the
Chapter 1 `Kᵀ z` source condition from `Remark_1_2_1`, with canonical witness
`z = K.toEuclideanLin w`. -/
theorem tsvdGramianSourceCondition_toSourceCondition
    [Fintype n] [DecidableEq n]
    (K : Matrix n n ℝ) (fTrue w : EuclideanSpace ℝ n)
    (h_source : fTrue = (Kᵀ * K).toEuclideanLin w) :
    fTrue = (Kᵀ).toEuclideanLin (K.toEuclideanLin w) := by
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using h_source

/-- Helper for Exercise 1.10: the scalar TSVD residual coefficient for the
squared source condition is bounded by `α` on every singular component. -/
theorem tsvdResidualSq_mul_sq_le_alphaSq
    {α s : ℝ} (hα_pos : 0 < α) (_hs_pos : 0 < s) :
    (((1 - SpectralFilter.tsvd α (s ^ 2)) * s ^ 2) ^ 2) ≤ α ^ 2 := by
  by_cases hcut : α ≤ s ^ 2
  · -- In the retained branch the TSVD residual coefficient vanishes.
    have hα_sq_nonneg : 0 ≤ α ^ 2 := by positivity
    simpa [SpectralFilter.tsvd, hcut] using hα_sq_nonneg
  · -- In the truncated branch the residual is exactly `s ^ 2`, which is `< α`.
    have hsq_lt : s ^ 2 < α := lt_of_not_ge hcut
    have hsq_nonneg : 0 ≤ s ^ 2 := sq_nonneg s
    simp [SpectralFilter.tsvd, hcut]
    nlinarith

/-- Helper for Exercise 1.10: an orthogonal matrix preserves the Euclidean norm
of the vector obtained from `Matrix.toEuclideanLin`. -/
theorem orthogonal_toEuclideanLin_norm_sq_eq
    [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin V x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hVtV : Vᵀ * V = 1 := (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hV
  -- Expand both norms into coordinate sums and move one copy of `V` across the dot product.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.toEuclideanLin_apply]
  calc
    ∑ i, (V *ᵥ x.ofLp) i ^ 2 = (V *ᵥ x.ofLp) ⬝ᵥ (V *ᵥ x.ofLp) := by
          simp [dotProduct, pow_two]
    _ =
        x.ofLp ⬝ᵥ (Vᵀ *ᵥ (V *ᵥ x.ofLp)) := by
          rw [Matrix.dotProduct_transpose_mulVec]
    _ = x.ofLp ⬝ᵥ x.ofLp := by
      simpa [Matrix.mulVec_mulVec, hVtV]
    _ = ∑ i, x.ofLp i ^ 2 := by
      simp [dotProduct, pow_two]

/-- Helper for Exercise 1.10: a diagonal map whose squared coefficients are
bounded by `α ^ 2` has squared operator action bounded by `α ^ 2`. -/
theorem diagonal_toEuclideanLin_norm_sq_le
    [Fintype n] [DecidableEq n]
    (c : n → ℝ) (x : EuclideanSpace ℝ n) {α : ℝ}
    (hbound : ∀ i, (c i) ^ 2 ≤ α ^ 2) :
    ‖Matrix.toEuclideanLin (Matrix.diagonal c) x‖ ^ 2 ≤ α ^ 2 * ‖x‖ ^ 2 := by
  -- Reduce the diagonal operator norm estimate to a coordinatewise sum inequality.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal]
  calc
    ∑ i, (c i * x.ofLp i) ^ 2 ≤ ∑ i, (α ^ 2 * (x.ofLp i) ^ 2) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hx_sq_nonneg : 0 ≤ (x.ofLp i) ^ 2 := sq_nonneg (x.ofLp i)
      nlinarith [hbound i]
    _ = α ^ 2 * ∑ i, (x.ofLp i) ^ 2 := by
      rw [← Finset.mul_sum]

/-- Helper for Exercise 1.10: under the orthogonal SVD
`K = U * Matrix.diagonal s * Vᵀ`, the Gramian `Kᵀ * K` is
`V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ`. -/
theorem gramianMatrix_eq_svdSquares
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ) :
    Kᵀ * K = V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ := by
  have hUtU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hU
  -- Expand the Gramian once and collapse the orthogonal middle factor.
  calc
    Kᵀ * K = ((U * Matrix.diagonal s * Vᵀ)ᵀ) * (U * Matrix.diagonal s * Vᵀ) := by
      rw [hK]
    _ = (V * Matrix.diagonal s * Uᵀ) * (U * Matrix.diagonal s * Vᵀ) := by
      simp [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    _ = V * (Matrix.diagonal s * (Uᵀ * U) * Matrix.diagonal s) * Vᵀ := by
      simp [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal s * Matrix.diagonal s) * Vᵀ := by
      rw [hUtU]
      simp [Matrix.mul_assoc]
    _ = V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 2
      ext i
      ring

/-- Helper for Exercise 1.10: multiplying the TSVD reconstruction matrix by
`K` leaves the right-singular basis `V` and replaces the diagonal entries by
`SpectralFilter.tsvd α (s i ^ 2)`. -/
theorem tsvdOperatorMatrix_mul_eq
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ) {α : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i) :
    operatorMatrix U V s tsvd α * K =
      V * Matrix.diagonal (fun i ↦ SpectralFilter.tsvd α (s i ^ 2)) * Vᵀ := by
  have hUtU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hU
  have hs_ne : ∀ i, s i ≠ 0 := fun i ↦ (hs_pos i).ne'
  -- The factor `s i` from `K` cancels the reciprocal built into `operatorMatrix`.
  calc
    operatorMatrix U V s tsvd α * K =
        (V * Matrix.diagonal (fun i ↦ SpectralFilter.tsvd α (s i ^ 2) / s i) * Uᵀ) *
          (U * Matrix.diagonal s * Vᵀ) := by
            rw [FilterRegularization.operatorMatrix_def, hK]
    _ = V *
          (Matrix.diagonal (fun i ↦ SpectralFilter.tsvd α (s i ^ 2) / s i) *
            (Uᵀ * U) * Matrix.diagonal s) *
          Vᵀ := by
            simp [Matrix.mul_assoc]
    _ = V *
          (Matrix.diagonal (fun i ↦ SpectralFilter.tsvd α (s i ^ 2) / s i) *
            Matrix.diagonal s) *
          Vᵀ := by
            rw [hUtU]
            simp [Matrix.mul_assoc]
    _ = V * Matrix.diagonal
          (fun i ↦ (SpectralFilter.tsvd α (s i ^ 2) / s i) * s i) * Vᵀ := by
            rw [Matrix.diagonal_mul_diagonal]
    _ = V * Matrix.diagonal (fun i ↦ SpectralFilter.tsvd α (s i ^ 2)) * Vᵀ := by
          congr 2
          ext i j
          by_cases hij : i = j
          · subst hij
            simp [Matrix.diagonal_apply, hs_ne i, div_eq_mul_inv, mul_assoc]
          · simp [Matrix.diagonal_apply, hij]

/-- Helper for Exercise 1.10: applying `Matrix.toEuclideanLin` twice is the
same as applying the product matrix once. -/
theorem toEuclideanLin_mul_apply
    [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) =
      Matrix.toEuclideanLin (A * B) x := by
  -- Move to coordinate functions so the statement becomes `mulVec_mulVec`.
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

/-- Helper for Exercise 1.10: an orthogonal matrix followed by its transpose
acts as the identity on `EuclideanSpace ℝ n`. -/
theorem orthogonal_toEuclideanLin_apply_transpose
    [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin V (Matrix.toEuclideanLin Vᵀ x) = x := by
  have hVVt : V * Vᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := V)).1 hV
  -- Collapse the orthogonal pair into the identity matrix before simplifying the action.
  calc
    Matrix.toEuclideanLin V (Matrix.toEuclideanLin Vᵀ x) =
        Matrix.toEuclideanLin (V * Vᵀ) x := by
          simpa using (toEuclideanLin_mul_apply V Vᵀ x)
    _ = x := by
      rw [hVVt]
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Exercise 1.10: the transpose of an orthogonal matrix cancels
the original matrix on `EuclideanSpace ℝ n`. -/
theorem orthogonal_toEuclideanLin_transpose_apply
    [Fintype n] [DecidableEq n]
    (V : Matrix n n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin Vᵀ (Matrix.toEuclideanLin V x) = x := by
  have hVtV : Vᵀ * V = 1 := (Matrix.mem_orthogonalGroup_iff' n ℝ).mp hV
  -- Collapse the transposed orthogonal pair into the identity matrix before simplifying.
  calc
    Matrix.toEuclideanLin Vᵀ (Matrix.toEuclideanLin V x) =
        Matrix.toEuclideanLin (Vᵀ * V) x := by
          simpa using (toEuclideanLin_mul_apply Vᵀ V x)
    _ = x := by
      rw [hVtV]
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Exercise 1.10: the TSVD noise term satisfies the standard
`δ / Real.sqrt α` bound from the earlier Chapter 1 TSVD analysis. -/
theorem tsvdNoiseError_norm_le
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (η : EuclideanSpace ℝ n) {α δ : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hα_pos : 0 < α)
    (h_noise : ‖η‖ ≤ δ) :
    ‖noiseError (operator U V s tsvd α) η‖ ≤
      δ / Real.sqrt α := by
  let coeff : n → ℝ := fun i ↦ SpectralFilter.tsvd α (s i ^ 2) / s i
  let u : EuclideanSpace ℝ n := Matrix.toEuclideanLin Uᵀ η
  have hU_t : Uᵀ ∈ Matrix.orthogonalGroup n ℝ := by
    -- Orthogonality is stable under transpose, so the `Uᵀ` coordinates stay orthogonal.
    rw [Matrix.mem_orthogonalGroup_iff']
    simpa [Matrix.transpose_mul] using
      (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := U)).1 hU
  have hδ_nonneg : 0 ≤ δ := le_trans (norm_nonneg _) h_noise
  have hcore :
      noiseError (operator U V s tsvd α) η =
        Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) := by
    -- Rewrite the propagated noise into orthogonal-diagonal coordinates.
    rw [FilterRegularization.noiseError_eq, FilterRegularization.operator_apply,
      FilterRegularization.operatorMatrix_def, Matrix.mul_assoc]
    calc
      Matrix.toEuclideanLin (V * (Matrix.diagonal coeff * Uᵀ)) η =
          Matrix.toEuclideanLin V
            (Matrix.toEuclideanLin (Matrix.diagonal coeff * Uᵀ) η) := by
            simpa using
              (toEuclideanLin_mul_apply V (Matrix.diagonal coeff * Uᵀ) η).symm
      _ = Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) := by
            congr 1
            simpa [u] using
              (toEuclideanLin_mul_apply (Matrix.diagonal coeff) Uᵀ η).symm
  have hdiag_sq :
      ‖Matrix.toEuclideanLin (Matrix.diagonal coeff) u‖ ^ 2 ≤
        (1 / Real.sqrt α) ^ 2 * ‖u‖ ^ 2 := by
    -- Exercise 1.5 gives the coefficient bound on each diagonal entry.
    refine diagonal_toEuclideanLin_norm_sq_le coeff u ?_
    intro i
    have hcoeff_nonneg : 0 ≤ coeff i := by
      by_cases hcut : α ≤ s i ^ 2
      · simp [coeff, SpectralFilter.tsvd, hcut, (hs_pos i).le]
      · simp [coeff, SpectralFilter.tsvd, hcut]
    have hcoeff_le : coeff i ≤ 1 / Real.sqrt α := by
      simpa [coeff] using SpectralFilter.tsvdInverseBound hα_pos (hs_pos i)
    nlinarith
  have hu_sq : ‖u‖ ^ 2 = ‖η‖ ^ 2 := by
    -- The intermediate `Uᵀ` basis change preserves the Euclidean norm.
    simpa [u] using orthogonal_toEuclideanLin_norm_sq_eq Uᵀ hU_t η
  have hnoise_sq : ‖η‖ ^ 2 ≤ δ ^ 2 := by
    -- Squaring the noise bound is safe because both sides are nonnegative.
    nlinarith [h_noise, norm_nonneg η]
  have hbound_sq :
      ‖noiseError (operator U V s tsvd α) η‖ ^ 2 ≤
        (δ / Real.sqrt α) ^ 2 := by
    -- Remove the orthogonal factors and compare the remaining diagonal action.
    rw [hcore]
    rw [orthogonal_toEuclideanLin_norm_sq_eq V hV
      (Matrix.toEuclideanLin (Matrix.diagonal coeff) u)]
    have hsq : ‖Matrix.toEuclideanLin (Matrix.diagonal coeff) u‖ ^ 2 ≤
        (1 / Real.sqrt α) ^ 2 * δ ^ 2 := by
      nlinarith [hdiag_sq, hu_sq, hnoise_sq]
    have hrewrite :
        (1 / Real.sqrt α) ^ 2 * δ ^ 2 = (δ / Real.sqrt α) ^ 2 := by
      ring_nf
    rwa [← hrewrite]
  have hrhs_nonneg : 0 ≤ δ / Real.sqrt α := by
    exact div_nonneg hδ_nonneg (le_of_lt (Real.sqrt_pos_of_pos hα_pos))
  -- The squared estimate upgrades to the desired norm estimate.
  nlinarith [hbound_sq, norm_nonneg (noiseError (operator U V s tsvd α) η)]

/-- Helper for Exercise 1.10: the Gramian source condition becomes a single
diagonal action after passing to `Vᵀ` coordinates. -/
theorem gramianSource_toVCoordinates
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (fTrue w : EuclideanSpace ℝ n)
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (h_source : fTrue = (Kᵀ * K).toEuclideanLin w) :
    Matrix.toEuclideanLin Vᵀ fTrue =
      Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ s i ^ 2))
        (Matrix.toEuclideanLin Vᵀ w) := by
  -- Rewrite the Gramian through the right-singular basis before canceling the outer `V`.
  rw [h_source, gramianMatrix_eq_svdSquares K U V s hU hK]
  calc
    Matrix.toEuclideanLin Vᵀ
        (Matrix.toEuclideanLin (V * Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ) w) =
      Matrix.toEuclideanLin Vᵀ
        (Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ) w)) := by
            congr 1
            symm
            simpa [Matrix.mul_assoc] using
              (toEuclideanLin_mul_apply V
                (Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ) w)
    _ = Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ s i ^ 2) * Vᵀ) w := by
          exact orthogonal_toEuclideanLin_transpose_apply V hV _
    _ = Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ s i ^ 2))
          (Matrix.toEuclideanLin Vᵀ w) := by
            symm
            simpa [Matrix.mul_assoc] using
              (toEuclideanLin_mul_apply (Matrix.diagonal (fun i ↦ s i ^ 2)) Vᵀ w)

/-- Helper for Exercise 1.10: the stronger source condition puts the TSVD
truncation bias into one diagonal form in the right-singular basis. -/
theorem tsvdGramianTruncationError_eq_diagonalForm
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (fTrue w : EuclideanSpace ℝ n) {α : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (h_source : fTrue = (Kᵀ * K).toEuclideanLin w) :
    truncationError
        (operator U V s tsvd α)
        (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
        fTrue =
      Matrix.toEuclideanLin V
        (Matrix.toEuclideanLin
          (Matrix.diagonal
            (fun i ↦ (SpectralFilter.tsvd α (s i ^ 2) - 1) * s i ^ 2))
          (Matrix.toEuclideanLin Vᵀ w)) := by
  let dWeight : n → ℝ := fun i ↦ SpectralFilter.tsvd α (s i ^ 2)
  let dBias : n → ℝ := fun i ↦ SpectralFilter.tsvd α (s i ^ 2) - 1
  let y : EuclideanSpace ℝ n := Matrix.toEuclideanLin Vᵀ fTrue
  let u : EuclideanSpace ℝ n := Matrix.toEuclideanLin Vᵀ w
  have hOperatorOnData :
      operator U V s tsvd α (Matrix.toEuclideanLin K fTrue) =
        Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin
            (Matrix.diagonal dWeight)
            y) := by
    -- Rewrite the reconstructed forward data into orthogonal-diagonal coordinates.
    rw [FilterRegularization.operator_apply]
    calc
      Matrix.toEuclideanLin (operatorMatrix U V s tsvd α) (Matrix.toEuclideanLin K fTrue) =
          Matrix.toEuclideanLin (operatorMatrix U V s tsvd α * K) fTrue := by
            symm
            simpa [Matrix.toEuclideanLin] using
              congrArg
                (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f fTrue)
                (Matrix.toLpLin_mul_same (p := 2) (operatorMatrix U V s tsvd α) K)
      _ = Matrix.toEuclideanLin (V * Matrix.diagonal dWeight * Vᵀ) fTrue := by
            rw [tsvdOperatorMatrix_mul_eq K U V s hU hK hs_pos]
      _ = Matrix.toEuclideanLin V
            (Matrix.toEuclideanLin
              (Matrix.diagonal dWeight)
              y) := by
            calc
              Matrix.toEuclideanLin (V * Matrix.diagonal dWeight * Vᵀ) fTrue =
                  Matrix.toEuclideanLin (V * Matrix.diagonal dWeight) y := by
                      simpa [y, Matrix.mul_assoc] using
                        (toEuclideanLin_mul_apply (V * Matrix.diagonal dWeight) Vᵀ fTrue).symm
              _ = Matrix.toEuclideanLin V
                    (Matrix.toEuclideanLin
                      (Matrix.diagonal dWeight)
                      y) := by
                        simpa [y, Matrix.mul_assoc] using
                          (toEuclideanLin_mul_apply V
                            (Matrix.diagonal dWeight)
                            y).symm
  have hTrue :
      fTrue = Matrix.toEuclideanLin V y := by
    -- Recover `fTrue` from its `Vᵀ` coordinates using orthogonality.
    simpa [y] using (orthogonal_toEuclideanLin_apply_transpose V hV fTrue).symm
  have hy_source :
      y = Matrix.toEuclideanLin (Matrix.diagonal (fun i ↦ s i ^ 2)) u := by
    -- Transport the Gramian source condition into the `Vᵀ` basis once and for all.
    simpa [y, u] using
      gramianSource_toVCoordinates K U V s fTrue w hU hV hK h_source
  -- Route correction: keep the subtraction under the outer orthogonal map and
  -- rewrite only the diagonal core of the TSVD bias.
  rw [FilterRegularization.truncationError, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
  calc
    operator U V s tsvd α (Matrix.toEuclideanLin K fTrue) - fTrue =
        Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin
            (Matrix.diagonal dWeight)
            y) -
          Matrix.toEuclideanLin V y := by
            rw [hOperatorOnData]
            simpa [hTrue]
    _ = Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin
            (Matrix.diagonal dWeight)
            y - y) := by
          simpa using
            (Matrix.toEuclideanLin V).map_sub
              (Matrix.toEuclideanLin
                (Matrix.diagonal dWeight)
                y)
              y
    _ = Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin
            (Matrix.diagonal dBias)
            y) := by
              congr 1
              ext i
              dsimp [y]
              change
                ((Matrix.diagonal dWeight *ᵥ (Vᵀ *ᵥ fTrue.ofLp)) i - (Vᵀ *ᵥ fTrue.ofLp) i =
                  (Matrix.diagonal dBias *ᵥ (Vᵀ *ᵥ fTrue.ofLp)) i)
              rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
              simp [dBias, dWeight]
              ring
    _ = Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin
            (Matrix.diagonal (fun i ↦ dBias i * s i ^ 2))
            u) := by
              rw [hy_source]
              congr 1
              rw [toEuclideanLin_mul_apply, Matrix.diagonal_mul_diagonal]
    _ = Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin
            (Matrix.diagonal
              (fun i ↦ (SpectralFilter.tsvd α (s i ^ 2) - 1) * s i ^ 2))
            (Matrix.toEuclideanLin Vᵀ w)) := by
              simp [dBias, u]

/-- Helper for Exercise 1.10: under the squared source condition
`fTrue = (Kᵀ * K).toEuclideanLin w`, the TSVD truncation bias is bounded by
`α * ‖w‖`. -/
theorem tsvdGramianTruncationError_le
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (fTrue w : EuclideanSpace ℝ n) {α : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hα_pos : 0 < α)
    (h_source : fTrue = (Kᵀ * K).toEuclideanLin w) :
    ‖truncationError
        (operator U V s tsvd α)
        (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
        fTrue‖ ≤
      α * ‖w‖ := by
  let coeff : n → ℝ := fun i ↦ (SpectralFilter.tsvd α (s i ^ 2) - 1) * s i ^ 2
  let u : EuclideanSpace ℝ n := Matrix.toEuclideanLin Vᵀ w
  have hV_t : Vᵀ ∈ Matrix.orthogonalGroup n ℝ := by
    -- The right-singular basis remains orthogonal after transpose.
    rw [Matrix.mem_orthogonalGroup_iff']
    simpa [Matrix.transpose_mul] using
      (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := V)).1 hV
  have hu_sq : ‖u‖ ^ 2 = ‖w‖ ^ 2 := by
    -- Passing to `Vᵀ` coordinates preserves the Euclidean norm of the source witness.
    simpa [u] using orthogonal_toEuclideanLin_norm_sq_eq Vᵀ hV_t w
  have hdiag_sq :
      ‖Matrix.toEuclideanLin (Matrix.diagonal coeff) u‖ ^ 2 ≤
        α ^ 2 * ‖u‖ ^ 2 := by
    -- The scalar TSVD residual bound applies coordinatewise after diagonalization.
    refine diagonal_toEuclideanLin_norm_sq_le coeff u ?_
    intro i
    have hscalar := tsvdResidualSq_mul_sq_le_alphaSq hα_pos (hs_pos i)
    dsimp [coeff]
    nlinarith
  have hbound_sq :
      ‖truncationError
          (operator U V s tsvd α)
          (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
          fTrue‖ ^ 2 ≤
        (α * ‖w‖) ^ 2 := by
    -- Keep the full truncation term behind the diagonal-form helper.
    rw [tsvdGramianTruncationError_eq_diagonalForm K U V s fTrue w hU hV hK hs_pos h_source]
    rw [orthogonal_toEuclideanLin_norm_sq_eq V hV
      (Matrix.toEuclideanLin (Matrix.diagonal coeff) u)]
    have hsq := hdiag_sq
    rw [hu_sq] at hsq
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hrhs_nonneg : 0 ≤ α * ‖w‖ := by positivity
  -- The squared bound converts back to the claimed norm estimate.
  nlinarith [hbound_sq, norm_nonneg
    (truncationError
      (operator U V s tsvd α)
      (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
      fTrue)]

/-- In the square finite-dimensional TSVD/SVD setup used locally in Chapter 1,
the stronger source condition `fTrue = (Kᵀ * K).toEuclideanLin w` yields the
pre-optimization total-error bound with source exponent `1`. -/
theorem tsvdGramianSourceCondition_error_le
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (fTrue w d η : EuclideanSpace ℝ n) {α δ : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hα_pos : 0 < α)
    (h_data : d = K.toEuclideanLin fTrue + η)
    (h_noise : ‖η‖ ≤ δ)
    (h_source : fTrue = (Kᵀ * K).toEuclideanLin w) :
    ‖operator U V s tsvd α d - fTrue‖ ≤
      α * ‖w‖ + δ / Real.sqrt α := by
  have h_decomp :
      operator U V s tsvd α d - fTrue =
        truncationError
            (operator U V s tsvd α)
            (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
            fTrue +
          noiseError (operator U V s tsvd α) η := by
    -- Split the total error into the deterministic truncation term and the propagated noise term.
    simp [h_data, truncationError, noiseError, sub_eq_add_neg, add_comm, add_left_comm]
  have h_trunc :
      ‖truncationError
          (operator U V s tsvd α)
          (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
          fTrue‖ ≤
        α * ‖w‖ :=
    tsvdGramianTruncationError_le K U V s fTrue w hU hV hK hs_pos hα_pos h_source
  have h_noise_term :
      ‖noiseError (operator U V s tsvd α) η‖ ≤ δ / Real.sqrt α :=
    tsvdNoiseError_norm_le K U V s η hU hV hK hs_pos hα_pos h_noise
  calc
    ‖operator U V s tsvd α d - fTrue‖ =
        ‖truncationError
            (operator U V s tsvd α)
            (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
            fTrue +
          noiseError (operator U V s tsvd α) η‖ := by
            rw [h_decomp]
    _ ≤ ‖truncationError
            (operator U V s tsvd α)
            (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
            fTrue‖ +
          ‖noiseError (operator U V s tsvd α) η‖ := by
            exact norm_add_le _ _
    _ ≤ α * ‖w‖ + δ / Real.sqrt α := by
          gcongr

/-- For positive `δ` and positive source norm `sourceNorm`, evaluating the
TSVD objective `α * sourceNorm + δ / Real.sqrt α` at the a priori choice
`α = Real.rpow (δ / sourceNorm) (2 / 3 : ℝ)` gives the order-`δ^(2 / 3)`
bound used in the final Exercise 1.10 estimate. In the source-condition
application, one specializes to `sourceNorm = ‖w‖`. -/
theorem tsvdGramianSourceCondition_aPrioriAlpha
    (sourceNorm : ℝ) {δ : ℝ}
    (hδ_pos : 0 < δ)
    (hSourceNorm_pos : 0 < sourceNorm) :
    Real.rpow (δ / sourceNorm) (2 / 3 : ℝ) * sourceNorm +
        δ / Real.sqrt (Real.rpow (δ / sourceNorm) (2 / 3 : ℝ)) ≤
      2 * Real.rpow sourceNorm (1 / 3 : ℝ) * Real.rpow δ (2 / 3 : ℝ) := by
  let x : ℝ := δ / sourceNorm
  have hx_pos : 0 < x := by
    -- The a priori parameter is built from the positive ratio `δ / sourceNorm`.
    exact div_pos hδ_pos hSourceNorm_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hδ_eq : sourceNorm * x = δ := by
    -- This rewrites the source/noise ratio back to the original noise level.
    dsimp [x]
    field_simp [hSourceNorm_pos.ne']
  have hsqrt :
      Real.sqrt (Real.rpow x (2 / 3 : ℝ)) = Real.rpow x (1 / 3 : ℝ) := by
    -- `sqrt (x^(2/3)) = x^(1/3)` for the positive ratio `x`.
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow (Real.rpow x (2 / 3 : ℝ)) (1 / 2 : ℝ) =
          Real.rpow x ((2 / 3 : ℝ) * (1 / 2 : ℝ)) := by
            symm
            exact Real.rpow_mul hx_nonneg (2 / 3 : ℝ) (1 / 2 : ℝ)
      _ = Real.rpow x (1 / 3 : ℝ) := by
        congr 1
        norm_num
  have hx_sub :
      x / Real.rpow x (1 / 3 : ℝ) = Real.rpow x (2 / 3 : ℝ) := by
    -- Normalize the quotient to the exponent difference `1 - 1/3 = 2/3`.
    calc
      x / Real.rpow x (1 / 3 : ℝ) = x ^ (1 : ℝ) / x ^ (1 / 3 : ℝ) := by
            simp
      _ = x ^ ((1 : ℝ) - 1 / 3) := by
            rw [← Real.rpow_sub hx_pos (1 : ℝ) (1 / 3 : ℝ)]
      _ = Real.rpow x (2 / 3 : ℝ) := by
            congr 1
            norm_num
  have hsource_split :
      sourceNorm = Real.rpow sourceNorm (1 / 3 : ℝ) * Real.rpow sourceNorm (2 / 3 : ℝ) := by
    -- Split `sourceNorm` into the exponents needed to match the right-hand side.
    calc
      sourceNorm = sourceNorm ^ (1 : ℝ) := by
        simpa using (Real.rpow_one sourceNorm).symm
      _ = Real.rpow sourceNorm ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by
        congr 1
        norm_num
      _ = Real.rpow sourceNorm (1 / 3 : ℝ) * Real.rpow sourceNorm (2 / 3 : ℝ) := by
        simpa using (Real.rpow_add hSourceNorm_pos (1 / 3 : ℝ) (2 / 3 : ℝ))
  have hmul :
      Real.rpow (sourceNorm * x) (2 / 3 : ℝ) =
        Real.rpow sourceNorm (2 / 3 : ℝ) * Real.rpow x (2 / 3 : ℝ) := by
    -- The positive factors let us distribute the `2/3` power across the product.
    simpa using
      (Real.mul_rpow (le_of_lt hSourceNorm_pos) hx_nonneg (z := (2 / 3 : ℝ)))
  have hterm :
      sourceNorm * Real.rpow x (2 / 3 : ℝ) =
        Real.rpow sourceNorm (1 / 3 : ℝ) * Real.rpow δ (2 / 3 : ℝ) := by
    -- Both summands of the objective reduce to the same monomial.
    calc
      sourceNorm * Real.rpow x (2 / 3 : ℝ) =
          (Real.rpow sourceNorm (1 / 3 : ℝ) * Real.rpow sourceNorm (2 / 3 : ℝ)) *
            Real.rpow x (2 / 3 : ℝ) := by
              conv_lhs => rw [hsource_split]
      _ = Real.rpow sourceNorm (1 / 3 : ℝ) *
            (Real.rpow sourceNorm (2 / 3 : ℝ) * Real.rpow x (2 / 3 : ℝ)) := by
              ring
      _ = Real.rpow sourceNorm (1 / 3 : ℝ) *
            Real.rpow (sourceNorm * x) (2 / 3 : ℝ) := by
              rw [hmul]
      _ = Real.rpow sourceNorm (1 / 3 : ℝ) * Real.rpow δ (2 / 3 : ℝ) := by
              rw [hδ_eq]
  have hobjective :
      Real.rpow (δ / sourceNorm) (2 / 3 : ℝ) * sourceNorm +
          δ / Real.sqrt (Real.rpow (δ / sourceNorm) (2 / 3 : ℝ)) =
        2 * Real.rpow sourceNorm (1 / 3 : ℝ) * Real.rpow δ (2 / 3 : ℝ) := by
    -- Rewrite both pieces through the common monomial from `hterm`.
    calc
      Real.rpow (δ / sourceNorm) (2 / 3 : ℝ) * sourceNorm +
          δ / Real.sqrt (Real.rpow (δ / sourceNorm) (2 / 3 : ℝ))
          = sourceNorm * Real.rpow x (2 / 3 : ℝ) +
              δ / Real.rpow x (1 / 3 : ℝ) := by
                rw [hsqrt]
                ring
      _ = sourceNorm * Real.rpow x (2 / 3 : ℝ) +
            sourceNorm * Real.rpow x (2 / 3 : ℝ) := by
              rw [← hδ_eq, mul_div_assoc, hx_sub]
      _ = 2 * (sourceNorm * Real.rpow x (2 / 3 : ℝ)) := by ring
      _ = 2 * Real.rpow sourceNorm (1 / 3 : ℝ) * Real.rpow δ (2 / 3 : ℝ) := by
            rw [hterm]
            ring
  exact le_of_eq hobjective

/-- Exercise 1.10. In the same square finite-dimensional TSVD/SVD setup,
if `fTrue` lies in `Range(Kᵀ * K)` through the explicit source witness
`fTrue = (Kᵀ * K).toEuclideanLin w`, then the a priori parameter choice
`α = Real.rpow (δ / ‖w‖) (2 / 3 : ℝ)` yields an order-`δ^(2 / 3)` TSVD
error bound. -/
theorem tsvdGramianSourceCondition_error_le_of_aPrioriAlpha
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (fTrue w d η : EuclideanSpace ℝ n) {δ : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hδ_pos : 0 < δ)
    (hw_pos : 0 < ‖w‖)
    (h_data : d = K.toEuclideanLin fTrue + η)
    (h_noise : ‖η‖ ≤ δ)
    (h_source : fTrue = (Kᵀ * K).toEuclideanLin w) :
    ‖operator U V s tsvd (Real.rpow (δ / ‖w‖) (2 / 3 : ℝ)) d - fTrue‖ ≤
      2 * Real.rpow ‖w‖ (1 / 3 : ℝ) * Real.rpow δ (2 / 3 : ℝ) := by
  have hα_pos : 0 < Real.rpow (δ / ‖w‖) (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (div_pos hδ_pos hw_pos) _
  calc
    ‖operator U V s tsvd (Real.rpow (δ / ‖w‖) (2 / 3 : ℝ)) d - fTrue‖ ≤
      Real.rpow (δ / ‖w‖) (2 / 3 : ℝ) * ‖w‖ +
        δ / Real.sqrt (Real.rpow (δ / ‖w‖) (2 / 3 : ℝ)) :=
      tsvdGramianSourceCondition_error_le K U V s fTrue w d η
        hU hV hK hs_pos hα_pos h_data h_noise h_source
    _ ≤ 2 * Real.rpow ‖w‖ (1 / 3 : ℝ) * Real.rpow δ (2 / 3 : ℝ) :=
      tsvdGramianSourceCondition_aPrioriAlpha ‖w‖ hδ_pos hw_pos

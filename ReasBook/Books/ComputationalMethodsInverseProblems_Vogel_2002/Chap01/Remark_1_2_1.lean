/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_4
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_5
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2.Operator
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped Matrix
open FilterRegularization
open SpectralFilter

universe u

variable {n : Type u}

/-- Helper for Remark 1.2-extra-2: transposing an orthogonal matrix keeps it in
`Matrix.orthogonalGroup n ℝ`. -/
lemma transpose_mem_orthogonalGroup
    [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ) :
    Aᵀ ∈ Matrix.orthogonalGroup n ℝ := by
  -- Rewrite orthogonality through the transpose identities.
  rw [Matrix.mem_orthogonalGroup_iff']
  simpa [Matrix.transpose_mul] using
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := A)).1 hA

/-- Helper for Remark 1.2-extra-2: an orthogonal matrix and its transpose also
cancel in the order `Aᵀ ∘ A` on `EuclideanSpace ℝ n`. -/
lemma orthogonal_toEuclideanLin_transpose_apply
    [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x) = x := by
  have hA' : Aᵀ * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := A)).1 hA
  -- Convert the matrix product into composition of the associated linear maps.
  calc
    Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin A x)
        = Matrix.toEuclideanLin (Aᵀ * A) x := by
            symm
            simpa [Matrix.toEuclideanLin] using
              congrArg
                (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f x)
                (Matrix.toLpLin_mul_same (p := 2) Aᵀ A)
    _ = x := by
      rw [hA']
      simpa [Matrix.toEuclideanLin] using
        congrArg
          (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f x)
          (Matrix.toLpLin_one (p := 2) (n := n) (R := ℝ))

/-- Helper for Remark 1.2-extra-2: an orthogonal matrix composed with its
transpose acts as the identity on `EuclideanSpace ℝ n`. -/
lemma orthogonal_toEuclideanLin_apply_transpose
    [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin Aᵀ x) = x := by
  have hA' : A * Aᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := A)).1 hA
  -- Convert the matrix product into composition of the associated linear maps.
  calc
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin Aᵀ x)
        = Matrix.toEuclideanLin (A * Aᵀ) x := by
            symm
            simpa [Matrix.toEuclideanLin] using
              congrArg
                (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f x)
                (Matrix.toLpLin_mul_same (p := 2) A Aᵀ)
    _ = x := by
      rw [hA']
      simpa [Matrix.toEuclideanLin] using
        congrArg
          (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f x)
          (Matrix.toLpLin_one (p := 2) (n := n) (R := ℝ))

/-- Helper for Remark 1.2-extra-2: an orthogonal matrix preserves Euclidean
norm squares through `Matrix.toEuclideanLin`. -/
lemma orthogonal_toEuclideanLin_norm_sq_eq
    [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin A x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hAtA : Aᵀ * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := A)).1 hA
  -- Expand both norms into coordinate sums and move `A` across the dot product.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.toEuclideanLin_apply]
  calc
    ∑ i, (A *ᵥ x.ofLp) i ^ 2 = (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) := by
          simp [dotProduct, pow_two]
    _ = x.ofLp ⬝ᵥ (Aᵀ *ᵥ (A *ᵥ x.ofLp)) := by
          rw [Matrix.dotProduct_transpose_mulVec]
    _ = x.ofLp ⬝ᵥ x.ofLp := by
          simpa [Matrix.mulVec_mulVec, hAtA]
    _ = ∑ i, x.ofLp i ^ 2 := by
          simp [dotProduct, pow_two]

/-- Helper for Remark 1.2-extra-2: an orthogonal matrix preserves the Euclidean
norm through `Matrix.toEuclideanLin`. -/
lemma orthogonal_toEuclideanLin_norm_map
    [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
  -- Extract the norm equality from equality of squared norms and nonnegativity.
  have hsq := orthogonal_toEuclideanLin_norm_sq_eq A hA x
  nlinarith [hsq, norm_nonneg (Matrix.toEuclideanLin A x), norm_nonneg x]

/-- Helper for Remark 1.2-extra-2: the TSVD truncation coefficient satisfies
the scalar source-condition bound from equation `(1.26)`. -/
lemma tsvdBiasCoeff_sq_mul_le_alpha
    {α σ : ℝ} (hα : 0 < α) (hσ : 0 < σ) :
    (SpectralFilter.tsvd α (σ ^ 2) - 1) ^ 2 * σ ^ 2 ≤ α := by
  -- Split into the retained and truncated TSVD branches.
  by_cases hcut : α ≤ σ ^ 2
  · simp [SpectralFilter.tsvd, hcut, hα.le]
  · have hsq_lt : σ ^ 2 < α := lt_of_not_ge hcut
    have hσsq_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
    simp [SpectralFilter.tsvd, hcut]
    linarith

/-- Helper for Remark 1.2-extra-2: the TSVD amplification coefficient satisfies
the reciprocal square-root bound from equation `(1.21)`. -/
lemma tsvdInverseCoeff_sq_le_inv_alpha
    {α σ : ℝ} (hα : 0 < α) (hσ : 0 < σ) :
    (SpectralFilter.tsvd α (σ ^ 2) / σ) ^ 2 ≤ 1 / α := by
  have hbound : SpectralFilter.tsvd α (σ ^ 2) / σ ≤ 1 / Real.sqrt α :=
    SpectralFilter.tsvdInverseBound hα hσ
  have hnonneg : 0 ≤ SpectralFilter.tsvd α (σ ^ 2) / σ := by
    by_cases hcut : α ≤ σ ^ 2
    · simp [SpectralFilter.tsvd, hcut, hσ.le]
    · simp [SpectralFilter.tsvd, hcut]
  have hright_nonneg : 0 ≤ 1 / Real.sqrt α := by
    positivity
  have hsq : (SpectralFilter.tsvd α (σ ^ 2) / σ) ^ 2 ≤ (1 / Real.sqrt α) ^ 2 := by
    exact sq_le_sq₀ hnonneg hright_nonneg |>.2 hbound
  calc
    (SpectralFilter.tsvd α (σ ^ 2) / σ) ^ 2 ≤ (1 / Real.sqrt α) ^ 2 := hsq
    _ = 1 / α := by
          field_simp [hα.ne']
          rw [Real.sq_sqrt hα.le]

/-- Helper for Remark 1.2-extra-2: if `Qᵀ * Q = 1`, then `Matrix.toEuclideanLin Q`
preserves the Euclidean norm. -/
lemma toEuclideanLin_norm_eq_of_transpose_mul_self
    [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : Qᵀ * Q = 1) (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin Q x‖ = ‖x‖ := by
  -- Repackage the transpose identity as orthogonality and reuse the chapter helper.
  have hQ_mem : Q ∈ Matrix.orthogonalGroup n ℝ :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).2 hQ
  exact orthogonal_toEuclideanLin_norm_map Q hQ_mem x

/-- Helper for Remark 1.2-extra-2: a diagonal matrix acts coordinatewise on the
Euclidean norm square. -/
lemma diagonal_toEuclideanLin_normSq
    [Fintype n] [DecidableEq n]
    (a : n → ℝ) (x : EuclideanSpace ℝ n) :
    ‖Matrix.toEuclideanLin (Matrix.diagonal a) x‖ ^ 2 =
      ∑ i, (a i) ^ 2 * (x i) ^ 2 := by
  -- `EuclideanSpace.real_norm_sq_eq` turns the claim into a coordinatewise identity.
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hcoord : (Matrix.toEuclideanLin (Matrix.diagonal a) x) i = a i * x i := by
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal]
  rw [hcoord]
  ring

/-- Helper for Remark 1.2-extra-2: a diagonal operator is bounded by a uniform
bound on its diagonal coefficients. -/
lemma diagonal_toEuclideanLin_norm_le_of_forall
    [Fintype n] [DecidableEq n]
    (a : n → ℝ) (C : ℝ) (x : EuclideanSpace ℝ n)
    (hC_nonneg : 0 ≤ C)
    (hC : ∀ i, |a i| ≤ C) :
    ‖Matrix.toEuclideanLin (Matrix.diagonal a) x‖ ≤ C * ‖x‖ := by
  have hsq :
      ‖Matrix.toEuclideanLin (Matrix.diagonal a) x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
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

/-- Helper for Remark 1.2-extra-2: the truncation error of a spectral-filter
reconstruction takes the stable diagonal-bias form in SVD coordinates. -/
lemma truncationError_eq_orthogonalDiagonalBias
    [Fintype n] [DecidableEq n]
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
              symm
              simpa [Matrix.toEuclideanLin] using
                congrArg
                  (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f fTrue)
                  (Matrix.toLpLin_mul_same (p := 2) (operatorMatrix U V s w α) K)
      _ = Matrix.toEuclideanLin (V * Matrix.diagonal dWeight * Vᵀ) fTrue := by
            rw [hOperatorMatrixMul]
      _ = Matrix.toEuclideanLin V
            (Matrix.toEuclideanLin (Matrix.diagonal dWeight) y) := by
            symm
            simpa [y, Matrix.toEuclideanLin] using
              congrArg
                (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f fTrue)
                (Matrix.toLpLin_mul_same (p := 2) (V * Matrix.diagonal dWeight) Vᵀ)
  have hTrue : fTrue = Matrix.toEuclideanLin V y := by
    -- Recover `fTrue` by canceling the `Vᵀ` coordinate change.
    simp [y, orthogonal_toEuclideanLin_apply_transpose, hV]
  -- Rewrite the truncation error as a diagonal bias inside the outer orthogonal factor.
  rw [FilterRegularization.truncationError, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
  calc
    operator U V s w α (Matrix.toEuclideanLin K fTrue) - fTrue
        = Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal dWeight) y) -
            Matrix.toEuclideanLin V y := by
              rw [hOperatorOnData, hTrue]
    _ = Matrix.toEuclideanLin V
          (Matrix.toEuclideanLin (Matrix.diagonal dWeight) y - y) := by
          simpa using
            (Matrix.toEuclideanLin V).map_sub
              (Matrix.toEuclideanLin (Matrix.diagonal dWeight) y) y
    _ =
      Matrix.toEuclideanLin V
        (Matrix.toEuclideanLin
          (Matrix.diagonal (fun i ↦ w α (s i ^ 2) - 1)) y) := by
            congr 1
            ext i
            simp [dWeight, Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal]
            ring
    _ =
      Matrix.toEuclideanLin V
        (Matrix.toEuclideanLin
          (Matrix.diagonal (fun i ↦ w α (s i ^ 2) - 1))
          (Matrix.toEuclideanLin Vᵀ fTrue)) := by
            simp [y]

/-- Helper for Remark 1.2-extra-2: evaluating the a priori parameter
`α = δ / sourceNorm` turns the objective from `(1.27)` into the symmetric value
`2 * √sourceNorm * √δ`. -/
lemma aPrioriObjective_at_sourceChoice
    (sourceNorm : ℝ) {δ : ℝ}
    (hδ_pos : 0 < δ)
    (hSourceNorm_pos : 0 < sourceNorm) :
    Real.sqrt (δ / sourceNorm) * sourceNorm + δ / Real.sqrt (δ / sourceNorm) =
      2 * Real.sqrt sourceNorm * Real.sqrt δ := by
  have hsqrtSource_ne : Real.sqrt sourceNorm ≠ 0 := by
    exact (Real.sqrt_ne_zero hSourceNorm_pos.le).2 hSourceNorm_pos.ne'
  have hsqrtDelta_ne : Real.sqrt δ ≠ 0 := by
    exact (Real.sqrt_ne_zero hδ_pos.le).2 hδ_pos.ne'
  have hterm1 : Real.sqrt (δ / sourceNorm) * sourceNorm = Real.sqrt δ * Real.sqrt sourceNorm := by
    rw [Real.sqrt_div hδ_pos.le]
    field_simp [hsqrtSource_ne]
    ring_nf
    rw [Real.sq_sqrt hSourceNorm_pos.le]
  have hterm2 : δ / Real.sqrt (δ / sourceNorm) = Real.sqrt δ * Real.sqrt sourceNorm := by
    rw [Real.sqrt_div hδ_pos.le]
    field_simp [hsqrtSource_ne, hsqrtDelta_ne]
    ring_nf
    rw [Real.sq_sqrt hδ_pos.le]
  -- Normalize both summands through `sqrt (δ / sourceNorm) = √δ / √sourceNorm`.
  calc
    Real.sqrt (δ / sourceNorm) * sourceNorm + δ / Real.sqrt (δ / sourceNorm)
      = (Real.sqrt δ * Real.sqrt sourceNorm) + (Real.sqrt δ * Real.sqrt sourceNorm) := by
          rw [hterm1, hterm2]
    _ = 2 * Real.sqrt sourceNorm * Real.sqrt δ := by ring

/-- Helper for Remark 1.2-extra-2: the TSVD noise term satisfies the square-root
noise-amplification estimate from equation `(1.22)`. -/
lemma tsvdNoiseError_norm_le
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
  have hU_t : Uᵀ ∈ Matrix.orthogonalGroup n ℝ :=
    transpose_mem_orthogonalGroup U hU
  have hδ_nonneg : 0 ≤ δ := le_trans (norm_nonneg _) h_noise
  have hcore :
      noiseError (operator U V s tsvd α) η =
        Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) := by
    -- Rewrite the TSVD noise term into orthogonal SVD coordinates.
    rw [FilterRegularization.noiseError_eq, FilterRegularization.operator_apply,
      FilterRegularization.operatorMatrix_def]
    calc
      Matrix.toEuclideanLin (V * Matrix.diagonal coeff * Uᵀ) η
        = Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff * Uᵀ) η) := by
            symm
            simpa [Matrix.toEuclideanLin] using
              congrArg
                (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f η)
                (Matrix.toLpLin_mul_same (p := 2) (V * Matrix.diagonal coeff) Uᵀ)
      _ = Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) := by
            congr 1
            symm
            simpa [u, Matrix.toEuclideanLin] using
              congrArg
                (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f η)
                (Matrix.toLpLin_mul_same (p := 2) (Matrix.diagonal coeff) Uᵀ)
  have hdiag :
      ‖Matrix.toEuclideanLin (Matrix.diagonal coeff) u‖ ≤ (1 / Real.sqrt α) * ‖u‖ := by
    refine diagonal_toEuclideanLin_norm_le_of_forall coeff (1 / Real.sqrt α) u (by positivity) ?_
    intro i
    have hcoeff_nonneg : 0 ≤ coeff i := by
      by_cases hcut : α ≤ s i ^ 2
      · simp [coeff, SpectralFilter.tsvd, hcut, (hs_pos i).le]
      · simp [coeff, SpectralFilter.tsvd, hcut]
    simpa [abs_of_nonneg hcoeff_nonneg, coeff] using SpectralFilter.tsvdInverseBound hα_pos (hs_pos i)
  -- Remove the orthogonal factors and apply the diagonal coefficient bound.
  calc
    ‖noiseError (operator U V s tsvd α) η‖
      = ‖Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u)‖ := by
          rw [hcore]
    _ = ‖Matrix.toEuclideanLin (Matrix.diagonal coeff) u‖ := by
          rw [orthogonal_toEuclideanLin_norm_map V hV]
    _ ≤ (1 / Real.sqrt α) * ‖u‖ := hdiag
    _ = (1 / Real.sqrt α) * ‖η‖ := by
          congr 1
          simp [u, orthogonal_toEuclideanLin_norm_map Uᵀ hU_t]
    _ ≤ (1 / Real.sqrt α) * δ := by
          gcongr
    _ = δ / Real.sqrt α := by ring

/-- Truncation bound for Remark 1.2-extra-2 (1). In the square finite-dimensional SVD specialization
used by the local Chapter 1 matrix/operator API, the source condition
`fTrue = (Kᵀ).toEuclideanLin z` implies the TSVD truncation estimate `(1.26)`
for the reconstruction operator `operator U V s tsvd α`. -/
theorem tsvdSourceCondition_truncationErrorSq_le
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (fTrue z : EuclideanSpace ℝ n) {α : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hα_pos : 0 < α)
    (h_source : fTrue = (Kᵀ).toEuclideanLin z) :
    ‖truncationError
        (operator U V s tsvd α)
        (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
        fTrue‖ ^ 2 ≤
      α * ‖z‖ ^ 2 := by
  let u : EuclideanSpace ℝ n := Matrix.toEuclideanLin Uᵀ z
  let coeff : n → ℝ := fun i ↦ (SpectralFilter.tsvd α (s i ^ 2) - 1) * s i
  have hU_t : Uᵀ ∈ Matrix.orthogonalGroup n ℝ :=
    transpose_mem_orthogonalGroup U hU
  have hV_right : Vᵀ * V = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).1 hV
  have hK_transpose : Kᵀ = V * Matrix.diagonal s * Uᵀ := by
    rw [hK]
    simp [Matrix.mul_assoc, Matrix.diagonal_transpose]
  have hVt_fTrue :
      Matrix.toEuclideanLin Vᵀ fTrue =
        Matrix.toEuclideanLin (Matrix.diagonal s) u := by
    -- Push the source condition through `Vᵀ` to expose the diagonal singular values.
    rw [h_source, hK_transpose]
    calc
      Matrix.toEuclideanLin Vᵀ (Matrix.toEuclideanLin (V * Matrix.diagonal s * Uᵀ) z)
        = Matrix.toEuclideanLin Vᵀ
            (Matrix.toEuclideanLin V
              (Matrix.toEuclideanLin (Matrix.diagonal s * Uᵀ) z)) := by
                congr 1
                symm
                simpa [Matrix.toEuclideanLin, Matrix.mul_assoc] using
                  congrArg
                    (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f z)
                    (Matrix.toLpLin_mul_same (p := 2) V (Matrix.diagonal s * Uᵀ))
      _ = Matrix.toEuclideanLin (Matrix.diagonal s * Uᵀ) z := by
            exact orthogonal_toEuclideanLin_transpose_apply V hV _
      _ = Matrix.toEuclideanLin (Matrix.diagonal s) u := by
            symm
            simpa [u, Matrix.toEuclideanLin] using
              congrArg
                (fun f : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n => f z)
                (Matrix.toLpLin_mul_same (p := 2) (Matrix.diagonal s) Uᵀ)
  have hcore :
      truncationError
          (operator U V s tsvd α)
          (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
          fTrue =
        Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u) := by
    -- Rewrite the truncation error through the stable diagonal-bias normal form.
    rw [truncationError_eq_orthogonalDiagonalBias K U V s fTrue tsvd α hU hV hK hs_pos]
    rw [hVt_fTrue]
    congr 1
    ext i
    simp [coeff, Matrix.toEuclideanLin_apply]
  calc
    ‖truncationError
        (operator U V s tsvd α)
        (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
        fTrue‖ ^ 2
      = ‖Matrix.toEuclideanLin V (Matrix.toEuclideanLin (Matrix.diagonal coeff) u)‖ ^ 2 := by
          rw [hcore]
    _ = ‖Matrix.toEuclideanLin (Matrix.diagonal coeff) u‖ ^ 2 := by
          rw [orthogonal_toEuclideanLin_norm_map V hV]
    _ = ∑ i, (coeff i) ^ 2 * (u i) ^ 2 := diagonal_toEuclideanLin_normSq coeff u
    _ ≤ ∑ i, α * (u i) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hcoeff : (coeff i) ^ 2 ≤ α := by
            convert tsvdBiasCoeff_sq_mul_le_alpha hα_pos (hs_pos i) using 1
            ring
          exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (u i))
    _ = α * ∑ i, (u i) ^ 2 := by
          symm
          rw [Finset.mul_sum]
    _ = α * ‖u‖ ^ 2 := by
          congr 1
          simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : n => ℝ) u).symm
    _ = α * ‖z‖ ^ 2 := by
          change α * ‖Matrix.toEuclideanLin Uᵀ z‖ ^ 2 = α * ‖z‖ ^ 2
          congr 1
          rw [orthogonal_toEuclideanLin_norm_map Uᵀ hU_t]

/-- Total-error bound for Remark 1.2-extra-2 (2). In the same square finite-dimensional TSVD/SVD
setup, combining the source condition `fTrue = (Kᵀ).toEuclideanLin z` with the
noisy data model `d = K.toEuclideanLin fTrue + η` gives the total-error bound
`(1.27)` for the reconstruction operator `operator U V s tsvd α`. -/
theorem tsvdSourceCondition_error_le
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (fTrue z d η : EuclideanSpace ℝ n) {α δ : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hα_pos : 0 < α)
    (h_data : d = K.toEuclideanLin fTrue + η)
    (h_noise : ‖η‖ ≤ δ)
    (h_source : fTrue = (Kᵀ).toEuclideanLin z) :
    ‖operator U V s tsvd α d - fTrue‖ ≤
      Real.sqrt α * ‖z‖ + δ / Real.sqrt α := by
  have hdecomp :
      operator U V s tsvd α d - fTrue =
        truncationError
          (operator U V s tsvd α)
          (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
          fTrue +
        noiseError (operator U V s tsvd α) η :=
    FilterRegularization.error_eq_truncationError_add_noiseError h_data
  have htruncSq :
      ‖truncationError
          (operator U V s tsvd α)
          (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
          fTrue‖ ^ 2 ≤
        (Real.sqrt α * ‖z‖) ^ 2 := by
    -- Convert the squared truncation estimate into the square of the target bound.
    calc
      ‖truncationError
          (operator U V s tsvd α)
          (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
          fTrue‖ ^ 2
        ≤ α * ‖z‖ ^ 2 :=
          tsvdSourceCondition_truncationErrorSq_le K U V s fTrue z
            hU hV hK hs_pos hα_pos h_source
      _ = (Real.sqrt α * ‖z‖) ^ 2 := by
            have hsqrt : (Real.sqrt α) ^ 2 = α := by
              simpa using (Real.sq_sqrt hα_pos.le)
            calc
              α * ‖z‖ ^ 2 = (Real.sqrt α) ^ 2 * ‖z‖ ^ 2 := by rw [hsqrt]
              _ = (Real.sqrt α * ‖z‖) ^ 2 := by ring
  have htrunc :
      ‖truncationError
          (operator U V s tsvd α)
          (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
          fTrue‖ ≤
        Real.sqrt α * ‖z‖ := by
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 htruncSq
  have hnoiseBound :
      ‖noiseError (operator U V s tsvd α) η‖ ≤ δ / Real.sqrt α :=
    tsvdNoiseError_norm_le K U V s η hU hV hK hs_pos hα_pos h_noise
  -- Combine the truncation and noise pieces through the standard error decomposition.
  calc
    ‖operator U V s tsvd α d - fTrue‖
      = ‖truncationError
            (operator U V s tsvd α)
            (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
            fTrue +
          noiseError (operator U V s tsvd α) η‖ := by
            rw [hdecomp]
    _ ≤ ‖truncationError
            (operator U V s tsvd α)
            (LinearMap.toContinuousLinearMap <| Matrix.toEuclideanLin K)
            fTrue‖ +
          ‖noiseError (operator U V s tsvd α) η‖ := norm_add_le _ _
    _ ≤ Real.sqrt α * ‖z‖ + δ / Real.sqrt α := by
          exact add_le_add htrunc hnoiseBound

/-- A priori parameter minimization for Remark 1.2-extra-2 (3). For positive `δ` and positive source norm
`sourceNorm`, the TSVD objective from `(1.27)` is minimized by the a priori
parameter choice `α = δ / sourceNorm` from `(1.28)`. In the source-condition
application, one specializes to `sourceNorm = ‖z‖`. -/
theorem tsvdSourceCondition_aPrioriAlpha
    (sourceNorm : ℝ) {α δ : ℝ}
    (hδ_pos : 0 < δ)
    (hSourceNorm_pos : 0 < sourceNorm)
    (hα_pos : 0 < α) :
    Real.sqrt (δ / sourceNorm) * sourceNorm + δ / Real.sqrt (δ / sourceNorm) ≤
      Real.sqrt α * sourceNorm + δ / Real.sqrt α := by
  have ha_nonneg : 0 ≤ Real.sqrt α * sourceNorm := by
    positivity
  have hb_nonneg : 0 ≤ δ / Real.sqrt α := by
    positivity
  have hsymmetric :
      2 * Real.sqrt sourceNorm * Real.sqrt δ =
        2 * Real.sqrt (Real.sqrt α * sourceNorm) * Real.sqrt (δ / Real.sqrt α) := by
    have hsqrtAlpha_ne : Real.sqrt α ≠ 0 := by
      exact (Real.sqrt_ne_zero hα_pos.le).2 hα_pos.ne'
    -- Rewrite the geometric mean of the two objective terms into the source/noise form.
    calc
      2 * Real.sqrt sourceNorm * Real.sqrt δ
        = 2 * Real.sqrt (sourceNorm * δ) := by
            rw [Real.sqrt_mul hSourceNorm_pos.le]
            ring
      _ = 2 * Real.sqrt ((Real.sqrt α * sourceNorm) * (δ / Real.sqrt α)) := by
            congr 1
            field_simp [hsqrtAlpha_ne]
      _ = 2 * Real.sqrt (Real.sqrt α * sourceNorm) * Real.sqrt (δ / Real.sqrt α) := by
            rw [Real.sqrt_mul ha_nonneg]
            ring
  have hAMGM :
      2 * Real.sqrt (Real.sqrt α * sourceNorm) * Real.sqrt (δ / Real.sqrt α) ≤
        Real.sqrt α * sourceNorm + δ / Real.sqrt α := by
    calc
      2 * Real.sqrt (Real.sqrt α * sourceNorm) * Real.sqrt (δ / Real.sqrt α)
        ≤ (Real.sqrt (Real.sqrt α * sourceNorm)) ^ 2 +
            (Real.sqrt (δ / Real.sqrt α)) ^ 2 := by
              simpa [pow_two, two_mul, mul_assoc, mul_left_comm, mul_comm] using
                two_mul_le_add_sq (Real.sqrt (Real.sqrt α * sourceNorm))
                  (Real.sqrt (δ / Real.sqrt α))
      _ = Real.sqrt α * sourceNorm + δ / Real.sqrt α := by
            rw [Real.sq_sqrt ha_nonneg, Real.sq_sqrt hb_nonneg]
  -- Evaluate the objective at the a priori choice and apply AM-GM to the general parameter.
  calc
    Real.sqrt (δ / sourceNorm) * sourceNorm + δ / Real.sqrt (δ / sourceNorm)
      = 2 * Real.sqrt sourceNorm * Real.sqrt δ :=
          aPrioriObjective_at_sourceChoice sourceNorm hδ_pos hSourceNorm_pos
    _ = 2 * Real.sqrt (Real.sqrt α * sourceNorm) * Real.sqrt (δ / Real.sqrt α) :=
          hsymmetric
    _ ≤ Real.sqrt α * sourceNorm + δ / Real.sqrt α := hAMGM

/-- Remark 1.2-extra-2 (4). In the same square finite-dimensional TSVD/SVD
setup, substituting the a priori choice `α = δ / ‖z‖` into `(1.27)` yields the
order-`√δ` estimate `(1.29)` for the reconstruction operator
`operator U V s tsvd (δ / ‖z‖)`. -/
theorem tsvdSourceCondition_error_le_of_aPrioriAlpha
    [Fintype n] [DecidableEq n]
    (K U V : Matrix n n ℝ) (s : n → ℝ)
    (fTrue z d η : EuclideanSpace ℝ n) {δ : ℝ}
    (hU : U ∈ Matrix.orthogonalGroup n ℝ)
    (hV : V ∈ Matrix.orthogonalGroup n ℝ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hs_pos : ∀ i, 0 < s i)
    (hδ_pos : 0 < δ)
    (hz_pos : 0 < ‖z‖)
    (h_data : d = K.toEuclideanLin fTrue + η)
    (h_noise : ‖η‖ ≤ δ)
    (h_source : fTrue = (Kᵀ).toEuclideanLin z) :
    ‖operator U V s tsvd (δ / ‖z‖) d - fTrue‖ ≤
      2 * Real.sqrt ‖z‖ * Real.sqrt δ := by
  have hα_pos : 0 < δ / ‖z‖ := div_pos hδ_pos hz_pos
  -- Apply the pre-optimization estimate at the a priori parameter and then minimize the scalar objective.
  calc
    ‖operator U V s tsvd (δ / ‖z‖) d - fTrue‖ ≤
      Real.sqrt (δ / ‖z‖) * ‖z‖ + δ / Real.sqrt (δ / ‖z‖) :=
        tsvdSourceCondition_error_le K U V s fTrue z d η
          hU hV hK hs_pos hα_pos h_data h_noise h_source
    _ = 2 * Real.sqrt ‖z‖ * Real.sqrt δ :=
          aPrioriObjective_at_sourceChoice ‖z‖ hδ_pos hz_pos

/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_35
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Exercise_7_1
import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_5.SpectralRepresentation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.EstimationError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.WhiteNoise
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

noncomputable section

open scoped BigOperators Matrix

namespace FilterRegularization

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
variable {K U V Rα : Matrix n n ℝ} {wα : ℝ → ℝ} {s : n → ℝ}
variable {fTrue : EuclideanSpace ℝ n} {η : Ω → EuclideanSpace ℝ n} {σ : ℝ}

/-- Helper for Proposition 7.6: the trace owner `noiseAmplificationTrace`
specialized to a matrix reconstruction operator is exactly the matrix trace of
`Rᵀ * R`. -/
lemma noiseAmplificationTrace_toEuclideanLin_eq_matrixTrace_transpose_mul
    (R : Matrix n n ℝ) :
    noiseAmplificationTrace R.toEuclideanLin.toContinuousLinearMap =
      Matrix.trace (Rᵀ * R) := by
  -- Rewrite the adjoint through transpose and compare the resulting endomorphism pointwise.
  rw [noiseAmplificationTrace_eq_trace_adjoint_comp]
  let T : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n :=
    R.toEuclideanLin.adjoint.comp R.toEuclideanLin
  have hT :
      (R.toEuclideanLin.toContinuousLinearMap.adjoint.comp
          R.toEuclideanLin.toContinuousLinearMap).toLinearMap = T := by
    rfl
  rw [hT]
  have hAdj : LinearMap.adjoint (Matrix.toEuclideanLin R) = Matrix.toEuclideanLin Rᵀ := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint R).symm
  have hMatrix : T = (Rᵀ * R).toEuclideanLin := by
    ext x i
    simp [T, hAdj, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  rw [hMatrix]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq (A := Rᵀ * R) ((EuclideanSpace.basisFun n ℝ).toBasis)

/-- Helper for Proposition 7.6: orthogonal coordinate changes preserve Euclidean
norm squares. -/
lemma orthogonalGroup_toEuclideanLin_norm_sq_eq
    (A : Matrix n n ℝ) (hA : A ∈ Matrix.orthogonalGroup n ℝ)
    (x : EuclideanSpace ℝ n) :
    ‖A.toEuclideanLin x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hAtA : Aᵀ * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := A)).mp hA
  -- Expand both norms to coordinate sums and cancel the middle orthogonal factor.
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

omit [DecidableEq n] in
/-- Helper for Proposition 7.6: the `null(K)` component really lies in
`ker K`. -/
lemma nullspaceComponent_mem_ker
    (Kclm : (EuclideanSpace ℝ n) →L[ℝ] EuclideanSpace ℝ n)
    (x : EuclideanSpace ℝ n) :
    nullspaceComponent Kclm x ∈ Kclm.ker := by
  -- Unfold the owner to the star projection onto the kernel.
  rw [nullspaceComponent_eq_starProjection]
  exact Kclm.ker.starProjection_apply_mem x

omit [DecidableEq n] in
/-- Helper for Proposition 7.6: subtracting the `null(K)` component leaves the
orthogonal projection onto `ker Kᗮ`. -/
lemma sub_nullspaceComponent_mem_kerOrthogonal
    (Kclm : (EuclideanSpace ℝ n) →L[ℝ] EuclideanSpace ℝ n)
    (x : EuclideanSpace ℝ n) :
    x - nullspaceComponent Kclm x ∈ Kclm.kerᗮ := by
  -- Unfold the owner and use the standard orthogonality of `x - starProjection x`.
  rw [nullspaceComponent_eq_starProjection]
  exact Kclm.ker.sub_starProjection_mem_orthogonal x

omit [Fintype n] [DecidableEq n] in
/-- Helper for Proposition 7.6: multiplying a singular value by the auxiliary
quotient used to factor `Rα` through `Kᵀ` recovers the filter quotient
`wα (s i ^ 2) / s i`, with `wα 0 = 0` handling the zero singular-value case. -/
lemma singularValueMul_filterSquareQuotient_eq_filterQuotient
    (wα : ℝ → ℝ) (s : n → ℝ) (hw0 : wα 0 = 0) :
    ∀ i, s i * (if s i = 0 then 0 else wα (s i ^ 2) / (s i ^ 2)) = wα (s i ^ 2) / s i := by
  intro i
  by_cases hs : s i = 0
  · simp [hs, hw0]
  · have hs2 : s i ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 hs
    rw [if_neg hs, pow_two]
    field_simp [hs]

/-- Helper for Proposition 7.6: every reconstruction output lies in
`ker(K)ᗮ`. -/
lemma reconstruction_toEuclideanLin_mem_kerOrthogonal
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s)
    (x : EuclideanSpace ℝ n) :
    Rα.toEuclideanLin x ∈ K.toEuclideanLin.kerᗮ := by
  let c : n → ℝ := fun i ↦ if s i = 0 then 0 else wα (s i ^ 2) / (s i ^ 2)
  let C : Matrix n n ℝ := U * Matrix.diagonal c * Uᵀ
  have hUtU : Uᵀ * U = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := U)).mp hRα.orthogonalU
  have hFactor : Kᵀ * C = Rα := by
    -- Normalize both products into the same orthogonal-diagonal form.
    calc
      Kᵀ * C
          = (V * Matrix.diagonal s * Uᵀ) * (U * Matrix.diagonal c * Uᵀ) := by
              rw [hK]
              simp [C, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = V * Matrix.diagonal s * (Uᵀ * U) * Matrix.diagonal c * Uᵀ := by
            simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal s * Matrix.diagonal c * Uᵀ := by
            rw [hUtU]
            simp [Matrix.mul_assoc]
      _ = V * (Matrix.diagonal s * Matrix.diagonal c) * Uᵀ := by
            simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal (fun i ↦ wα (s i ^ 2) / s i) * Uᵀ := by
            refine congrArg (fun M ↦ V * M * Uᵀ) ?_
            ext i j
            by_cases hij : i = j
            · subst hij
              simp [c,
                singularValueMul_filterSquareQuotient_eq_filterQuotient
                  (wα := wα) (s := s) hRα.filter_zero]
            · simp [hij]
      _ = Rα := by
            rw [hRα.eq_spectralRep]
  have hAdj :
      K.toEuclideanLin.adjoint = Kᵀ.toEuclideanLin := by
    simpa using
      congrArg LinearMap.toContinuousLinearMap
        (Matrix.toEuclideanLin_conjTranspose_eq_adjoint K).symm
  -- Put the reconstruction output explicitly in the adjoint range.
  have hRange :
      Rα.toEuclideanLin x ∈ K.toEuclideanLin.adjoint.range := by
    refine ⟨C.toEuclideanLin x, ?_⟩
    rw [hAdj]
    ext i
    simpa [C, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc] using
      congrArg (fun M : Matrix n n ℝ => (M *ᵥ x.ofLp) i) hFactor
  simpa [LinearMap.orthogonal_ker] using hRange

/-- Helper for Proposition 7.6: pairing propagated white noise with a fixed
vector has zero expectation. -/
lemma integral_inner_const_reconstruction_eq_zero
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (b : EuclideanSpace ℝ n) (B : Matrix n n ℝ) :
    ∫ ω, inner ℝ b (B.toEuclideanLin (η ω)) ∂μ = 0 := by
  have h_two_le : (1 : ENNReal) ≤ (2 : ENNReal) := by
    norm_num
  have hNoiseLp : MeasureTheory.MemLp (fun ω ↦ B.toEuclideanLin (η ω)) 2 μ := by
    simpa using hη.memLp.continuousLinearMap_comp B.toEuclideanLin.toContinuousLinearMap
  have hNoiseInt : MeasureTheory.Integrable (fun ω ↦ B.toEuclideanLin (η ω)) μ :=
    hNoiseLp.integrable h_two_le
  have hEtaInt : MeasureTheory.Integrable η μ := hη.memLp.integrable h_two_le
  have hMeanZero :
      ∫ ω, B.toEuclideanLin (η ω) ∂μ = 0 := by
    -- Commute the fixed linear map through the integral and use the mean-zero hypothesis.
    rw [show ∫ ω, B.toEuclideanLin (η ω) ∂μ = B.toEuclideanLin (∫ ω, η ω ∂μ) by
      simpa using
        ContinuousLinearMap.integral_comp_comm B.toEuclideanLin.toContinuousLinearMap hEtaInt]
    rw [hη.mean_zero]
    simp
  -- Rewrite the scalar pairing integral through the vector-valued mean.
  rw [integral_inner hNoiseInt, hMeanZero]
  simp

/-- Helper for Proposition 7.6: the propagated white-noise variance is
`σ ^ 2 * noiseAmplificationTrace` for the reconstruction map. -/
lemma integral_sqNorm_reconstruction_eq_sigma_sq_noiseAmplificationTrace
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (B : Matrix n n ℝ) :
    ∫ ω, ‖B.toEuclideanLin (η ω)‖ ^ 2 ∂μ =
      σ ^ 2 * noiseAmplificationTrace B.toEuclideanLin.toContinuousLinearMap := by
  have hLinearEq :
      (fun ω ↦ B.toEuclideanLin (η ω)) = ProbabilityTheory.linearEstimator B η := by
    funext ω
    rw [ProbabilityTheory.linearEstimator_apply]
  have hNoiseLp : MeasureTheory.MemLp (fun ω ↦ B.toEuclideanLin (η ω)) 2 μ := by
    simpa using hη.memLp.continuousLinearMap_comp B.toEuclideanLin.toContinuousLinearMap
  have hCycle : Matrix.trace (B * Bᵀ) = Matrix.trace (Bᵀ * B) := by
    -- Cycle the trace once to match the `noiseAmplificationTrace` convention.
    simpa using (Matrix.trace_mul_cycle (1 : Matrix n n ℝ) B Bᵀ)
  -- Convert the expected squared norm to a second-moment trace and then insert isotropy.
  calc
    ∫ ω, ‖B.toEuclideanLin (η ω)‖ ^ 2 ∂μ
        =
          Matrix.trace
            (ProbabilityTheory.secondMomentMatrix μ (fun ω ↦ B.toEuclideanLin (η ω))) := by
            rw [ProbabilityTheory.expected_sqNorm_eq_trace_secondMomentMatrix hNoiseLp]
    _ = Matrix.trace (B * ProbabilityTheory.secondMomentMatrix μ η * Bᵀ) := by
          rw [hLinearEq, ProbabilityTheory.MinimumVarianceLinear.secondMomentMatrix_linearEstimator
            hη.memLp B]
    _ = Matrix.trace (B * (σ ^ 2 • (1 : Matrix n n ℝ)) * Bᵀ) := by
          rw [hη.secondMoment_eq]
    _ = Matrix.trace (σ ^ 2 • (B * 1 * Bᵀ)) := by
          simp
    _ = (σ ^ 2 : ℝ) • Matrix.trace (B * 1 * Bᵀ) := by
          rw [Matrix.trace_smul]
    _ = σ ^ 2 * Matrix.trace (B * 1 * Bᵀ) := by
          simp
    _ = σ ^ 2 * Matrix.trace (B * Bᵀ) := by
          simp
    _ = σ ^ 2 * Matrix.trace (Bᵀ * B) := by
          rw [hCycle]
    _ = σ ^ 2 * noiseAmplificationTrace B.toEuclideanLin.toContinuousLinearMap := by
          rw [noiseAmplificationTrace_toEuclideanLin_eq_matrixTrace_transpose_mul]

/-- Helper for Proposition 7.6: composing the Chapter 7 reconstruction matrix
with the forward matrix recovers the spectral weight diagonal on the solution
side. -/
lemma reconstruction_comp_forward_eq_spectralRep
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    Rα * K = V * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * Vᵀ := by
  have hUtU : Uᵀ * U = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := U)).mp hRα.orthogonalU
  -- Expand both factors and collapse the middle orthogonal term before simplifying diagonals.
  calc
    Rα * K
        = (V * Matrix.diagonal (fun i ↦ wα (s i ^ 2) / s i) * Uᵀ) *
            (U * Matrix.diagonal s * Vᵀ) := by
              rw [hRα.eq_spectralRep, hK]
    _ = V * Matrix.diagonal (fun i ↦ wα (s i ^ 2) / s i) * (Uᵀ * U) *
          Matrix.diagonal s * Vᵀ := by
            simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal (fun i ↦ wα (s i ^ 2) / s i) *
          Matrix.diagonal s * Vᵀ := by
            rw [hUtU]
            simp [Matrix.mul_assoc]
      _ = V * (Matrix.diagonal (fun i ↦ wα (s i ^ 2) / s i) * Matrix.diagonal s) * Vᵀ := by
          simp [Matrix.mul_assoc]
      _ = V * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * Vᵀ := by
            refine congrArg (fun M ↦ V * M * Vᵀ) ?_
            ext i j
            by_cases hij : i = j
            · subst hij
              rw [Matrix.diagonal_mul_diagonal]
              simp only [Matrix.diagonal_apply_eq]
              rw [mul_comm]
              exact singularValueMul_filterQuotient_eq_weight wα s hRα.filter_zero i
            · simp [hij]

omit [DecidableEq n] in
/-- Helper for Proposition 7.6: removing the nullspace component does not change
the forward data because the discarded part already lies in `ker K`. -/
lemma forward_sub_nullspaceComponent_eq_forward
    (Kclm : (EuclideanSpace ℝ n) →L[ℝ] EuclideanSpace ℝ n)
    (x : EuclideanSpace ℝ n) :
    Kclm (x - nullspaceComponent Kclm x) = Kclm x := by
  -- Apply `K` to the projected component and kill the nullspace term in `ker K`.
  have hNull : Kclm (nullspaceComponent Kclm x) = 0 := by
    exact LinearMap.mem_ker.mp (nullspaceComponent_mem_ker Kclm x)
  rw [map_sub, hNull, sub_zero]

omit [MeasurableSpace Ω] in
/-- Helper for Proposition 7.6: pointwise, the estimation error splits into a
`ker(K)ᗮ` component and the orthogonal nullspace floor, so the squared norm
separates by Pythagoras. -/
lemma estimationError_normSq_eq_projectedBiasNoise_add_nullspaceNormSq
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s)
    (ω : Ω) :
    ‖estimationError Rα.toEuclideanLin.toContinuousLinearMap
        K.toEuclideanLin.toContinuousLinearMap fTrue (η ω)‖ ^ 2 =
      ‖(Rα.toEuclideanLin (K.toEuclideanLin fTrue) -
          (fTrue -
            nullspaceComponent K.toEuclideanLin.toContinuousLinearMap
              fTrue)) +
        Rα.toEuclideanLin (η ω)‖ ^ 2 +
        ‖nullspaceComponent K.toEuclideanLin.toContinuousLinearMap fTrue‖ ^ 2 := by
  let Kclm : (EuclideanSpace ℝ n) →L[ℝ] EuclideanSpace ℝ n :=
    K.toEuclideanLin.toContinuousLinearMap
  let floor : EuclideanSpace ℝ n := nullspaceComponent Kclm fTrue
  let proj : EuclideanSpace ℝ n := fTrue - floor
  let bias : EuclideanSpace ℝ n := Rα.toEuclideanLin (K.toEuclideanLin fTrue) - proj
  let propagatedNoise : EuclideanSpace ℝ n := Rα.toEuclideanLin (η ω)
  have hError :
      estimationError Rα.toEuclideanLin.toContinuousLinearMap
          K.toEuclideanLin.toContinuousLinearMap fTrue (η ω) =
        (bias + propagatedNoise) - floor := by
    -- Expand the error and regroup the deterministic projected component and the nullspace floor.
    rw [estimationError_def]
    dsimp [bias, propagatedNoise, proj, floor]
    rw [Rα.toEuclideanLin.map_add]
    abel
  have hFloorMem : floor ∈ Kclm.ker := by
    -- The nullspace floor is exactly the `ker K` projection.
    simpa [floor] using nullspaceComponent_mem_ker Kclm fTrue
  have hProjMem : proj ∈ Kclm.kerᗮ := by
    -- The complementary projected component lies in `ker Kᗮ`.
    simpa [proj, floor] using sub_nullspaceComponent_mem_kerOrthogonal Kclm fTrue
  have hReconMem :
      Rα.toEuclideanLin (K.toEuclideanLin fTrue) ∈ Kclm.kerᗮ := by
    -- Every reconstruction output belongs to the orthogonal complement of `ker K`.
    simpa [Kclm] using
      reconstruction_toEuclideanLin_mem_kerOrthogonal
        (K := K) (U := U) (V := V) (Rα := Rα) (wα := wα) (s := s)
        hK hRα (K.toEuclideanLin fTrue)
  have hNoiseMem : propagatedNoise ∈ Kclm.kerᗮ := by
    -- The propagated noise is another reconstruction output, so it has the same orthogonality.
    simpa [propagatedNoise, Kclm] using
      reconstruction_toEuclideanLin_mem_kerOrthogonal
        (K := K) (U := U) (V := V) (Rα := Rα) (wα := wα) (s := s)
        hK hRα (η ω)
  have hBiasMem : bias ∈ Kclm.kerᗮ := by
    -- Subtract the projected component inside the same orthogonal complement.
    exact Kclm.kerᗮ.sub_mem hReconMem hProjMem
  have hSumMem : bias + propagatedNoise ∈ Kclm.kerᗮ := by
    -- The full non-nullspace component stays inside `ker Kᗮ`.
    exact Kclm.kerᗮ.add_mem hBiasMem hNoiseMem
  have hInner :
      inner ℝ (bias + propagatedNoise) (-floor) = 0 := by
    -- Vectors in `ker Kᗮ` are orthogonal to every vector in `ker K`, including the nullspace floor.
    simpa using
      Submodule.inner_left_of_mem_orthogonal hFloorMem hSumMem
  -- Rewrite the error into an orthogonal sum and apply the Pythagorean identity.
  rw [hError, sub_eq_add_neg]
  simpa [pow_two, floor] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (bias + propagatedNoise) (-floor) hInner

/-- Helper for Proposition 7.6: on the projected component, `Rα K - I`
becomes the diagonal filter-deviation operator in `V`-coordinates. -/
lemma reconstructionOnProjectedComponent_eq_orthogonalDiagonalDeviation
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s)
    (x : EuclideanSpace ℝ n) :
    Rα.toEuclideanLin
        (K.toEuclideanLin
          (x -
            nullspaceComponent K.toEuclideanLin.toContinuousLinearMap
              x)) -
      (x -
        nullspaceComponent K.toEuclideanLin.toContinuousLinearMap
          x) =
      V.toEuclideanLin
        ((Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1)).toEuclideanLin
          ((Vᵀ).toEuclideanLin
            (x -
              nullspaceComponent K.toEuclideanLin.toContinuousLinearMap
                x))) := by
  let proj : EuclideanSpace ℝ n :=
    x - nullspaceComponent K.toEuclideanLin.toContinuousLinearMap x
  let ξ : EuclideanSpace ℝ n := (Vᵀ).toEuclideanLin proj
  let d : n → ℝ := fun i ↦ wα (s i ^ 2) - 1
  have hVtV : Vᵀ * V = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ) (A := V)).mp hRα.orthogonalV
  have hVVt : V * Vᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ) (A := V)).mp hRα.orthogonalV
  have hSub :
      Rα * K - 1 = V * Matrix.diagonal d * Vᵀ := by
    -- Rewrite `Rα * K` and `1` in the same orthogonal basis before subtracting diagonals.
    calc
      Rα * K - 1
          = V * Matrix.diagonal (fun i ↦ wα (s i ^ 2)) * Vᵀ -
              V * Matrix.diagonal (fun _ : n ↦ (1 : ℝ)) * Vᵀ := by
                rw [reconstruction_comp_forward_eq_spectralRep
                  (K := K) (U := U) (V := V) (Rα := Rα) (wα := wα) (s := s) hK hRα, ← hVVt]
                simp
      _ = V *
            ((Matrix.diagonal (fun i ↦ wα (s i ^ 2)) -
              Matrix.diagonal (fun _ : n ↦ (1 : ℝ))) *
              Vᵀ) := by
            simp [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
      _ = V * (Matrix.diagonal d * Vᵀ) := by
            rw [Matrix.diagonal_sub]
      _ = V * Matrix.diagonal d * Vᵀ := by
            simp [Matrix.mul_assoc]
  have hDiff :
      Rα.toEuclideanLin (K.toEuclideanLin proj) - proj =
        (Rα * K - 1).toEuclideanLin proj := by
    -- Collapse the vector difference to the single matrix `(Rα * K - 1)` acting on `proj`.
    apply WithLp.ofLp_injective
    simp [proj, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hCompose :
      (V * Matrix.diagonal d * Vᵀ).toEuclideanLin proj =
        V.toEuclideanLin ((Matrix.diagonal d).toEuclideanLin ξ) := by
    -- Reassociate the orthogonal-diagonal action instead of unfolding coordinates in the theorem.
    apply WithLp.ofLp_injective
    simp [ξ, proj, d, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  -- Put the projected reconstruction bias into the stable orthogonal-diagonal normal form.
  calc
    Rα.toEuclideanLin (K.toEuclideanLin
        (x - nullspaceComponent K.toEuclideanLin.toContinuousLinearMap x)) -
        (x - nullspaceComponent K.toEuclideanLin.toContinuousLinearMap x)
        = Rα.toEuclideanLin (K.toEuclideanLin proj) - proj := by
            simp [proj]
    _ = (Rα * K - 1).toEuclideanLin proj := hDiff
    _ = (V * Matrix.diagonal d * Vᵀ).toEuclideanLin proj := by
          rw [hSub]
    _ = V.toEuclideanLin ((Matrix.diagonal d).toEuclideanLin ξ) := hCompose
    _ = V.toEuclideanLin
          ((Matrix.diagonal (fun i ↦ wα (s i ^ 2) - 1)).toEuclideanLin
            ((Vᵀ).toEuclideanLin
              (x - nullspaceComponent K.toEuclideanLin.toContinuousLinearMap x))) := by
          simp [ξ, proj, d]

/-- Helper for Proposition 7.6: the squared norm of a diagonal operator is the
sum of the squared coordinate weights. -/
lemma diagonal_toEuclideanLin_normSq_eq_coordinateSum
    (c : n → ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖(Matrix.diagonal c).toEuclideanLin ξ‖ ^ 2 =
      ∑ i : n, (c i) ^ 2 * (ξ i) ^ 2 := by
  -- Move to coordinate functions so the diagonal action becomes pointwise multiplication.
  rw [EuclideanSpace.real_norm_sq_eq]
  have htoLp :
      ((Matrix.diagonal c).toEuclideanLin ξ).ofLp = Matrix.diagonal c *ᵥ ξ.ofLp := by
    simpa only [Matrix.toEuclideanLin, Matrix.toLin'_apply] using
      (Matrix.ofLp_toLpLin (p := 2) (q := 2) (Matrix.diagonal c) ξ)
  have hcoords :
      ∑ i : n, (((Matrix.diagonal c).toEuclideanLin ξ) i) ^ 2 =
        ∑ i : n, ((Matrix.diagonal c *ᵥ ξ.ofLp) i) ^ 2 := by
    exact
      congrArg (fun y : n → ℝ ↦ ∑ i : n, (y i) ^ 2)
        htoLp
  rw [hcoords]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Matrix.mulVec_diagonal]
  ring

/-- The first displayed identity in Proposition 7.6: under the Chapter 7
semidiscrete white-noise owner and the shared SVD/filter representation setup
for `K` and `Rα` from `(7.36)`, the expected squared estimation error splits
into the projected deterministic bias, the nullspace floor, and the stochastic
variance term
`σ ^ 2 * noiseAmplificationTrace Rα.toEuclideanLin.toContinuousLinearMap`. -/
theorem expectedSqEstimationError_eq_projectedBias_add_noiseAmplification
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    expectedSqEstimationError μ Rα.toEuclideanLin.toContinuousLinearMap
        K.toEuclideanLin.toContinuousLinearMap fTrue η =
      ‖Rα.toEuclideanLin (K.toEuclideanLin fTrue) -
          (fTrue -
            nullspaceComponent K.toEuclideanLin.toContinuousLinearMap
              fTrue)‖ ^ 2 +
        ‖nullspaceComponent K.toEuclideanLin.toContinuousLinearMap fTrue‖ ^ 2 +
        σ ^ 2 * noiseAmplificationTrace Rα.toEuclideanLin.toContinuousLinearMap := by
  let floor : EuclideanSpace ℝ n :=
    nullspaceComponent K.toEuclideanLin.toContinuousLinearMap fTrue
  let bias : EuclideanSpace ℝ n :=
    Rα.toEuclideanLin (K.toEuclideanLin fTrue) - (fTrue - floor)
  let noise : Ω → EuclideanSpace ℝ n := fun ω ↦ Rα.toEuclideanLin (η ω)
  let cross : Ω → ℝ := fun ω ↦ 2 * inner ℝ bias (noise ω)
  let variance : Ω → ℝ := fun ω ↦ ‖noise ω‖ ^ 2
  let constBias : Ω → ℝ := fun _ ↦ ‖bias‖ ^ 2 + ‖floor‖ ^ 2
  have h_two_le : (1 : ENNReal) ≤ (2 : ENNReal) := by
    norm_num
  have hNoiseLp : MeasureTheory.MemLp noise 2 μ := by
    -- The propagated noise is a fixed continuous linear image of the white-noise field.
    simpa [noise] using
      hη.memLp.continuousLinearMap_comp Rα.toEuclideanLin.toContinuousLinearMap
  have hNoiseInt : MeasureTheory.Integrable noise μ := hNoiseLp.integrable h_two_le
  have hNoiseSqInt : MeasureTheory.Integrable (fun ω ↦ ‖noise ω‖ ^ 2) μ := by
    exact MeasureTheory.MemLp.integrable_norm_pow (p := 2) hNoiseLp (by decide)
  have hCrossInt : MeasureTheory.Integrable cross μ := by
    -- The mixed term is a constant multiple of the integrable scalar pairing with the noise.
    simpa [cross] using (hNoiseInt.const_inner bias).const_mul (2 : ℝ)
  have hVarianceInt : MeasureTheory.Integrable variance μ := by
    -- The variance term is exactly the squared-norm integrand of the propagated noise.
    simpa [variance] using hNoiseSqInt
  have hConstBiasInt : MeasureTheory.Integrable constBias μ :=
    MeasureTheory.integrable_const _
  have hPointwise :
      (fun ω ↦ ‖estimationError Rα.toEuclideanLin.toContinuousLinearMap
          K.toEuclideanLin.toContinuousLinearMap fTrue (η ω)‖ ^ 2) =
        fun ω ↦ constBias ω + cross ω + variance ω := by
    -- Route correction: use the standalone orthogonal decomposition first, then expand
    -- `‖bias + noise‖^2` once into bias, cross, and variance.
    funext ω
    rw [estimationError_normSq_eq_projectedBiasNoise_add_nullspaceNormSq
      (K := K) (U := U) (V := V) (Rα := Rα) (wα := wα) (s := s)
      (fTrue := fTrue) (η := η) hK hRα ω]
    rw [norm_add_sq_real]
    dsimp [constBias, cross, variance, noise]
    ring
  have hAssoc :
      (fun ω ↦ constBias ω + cross ω + variance ω) =
        fun ω ↦ constBias ω + (cross ω + variance ω) := by
    funext ω
    ring
  have hSplit :
      ∫ ω, constBias ω + (cross ω + variance ω) ∂μ =
        ∫ ω, constBias ω ∂μ + ∫ ω, cross ω + variance ω ∂μ := by
    simpa using
      (MeasureTheory.integral_add (μ := μ) (f := constBias) (g := cross + variance)
        hConstBiasInt (hCrossInt.add hVarianceInt))
  have hCrossVarianceSplit :
      ∫ ω, cross ω + variance ω ∂μ = ∫ ω, cross ω ∂μ + ∫ ω, variance ω ∂μ := by
    simpa using
      (MeasureTheory.integral_add (μ := μ) (f := cross) (g := variance) hCrossInt hVarianceInt)
  have hCrossZero : ∫ ω, cross ω ∂μ = 0 := by
    -- The white-noise mean-zero hypothesis removes the mixed term.
    rw [show cross = fun ω ↦ 2 * inner ℝ bias (noise ω) by
      funext ω
      simp [cross]]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_inner_const_reconstruction_eq_zero
      (μ := μ) (η := η) (σ := σ) hη bias Rα]
    simp
  have hVariance :
      ∫ ω, variance ω ∂μ =
        σ ^ 2 * noiseAmplificationTrace Rα.toEuclideanLin.toContinuousLinearMap := by
    -- The remaining quadratic noise term is exactly the noise-amplification trace term.
    rw [show variance = fun ω ↦ ‖noise ω‖ ^ 2 by
      funext ω
      simp [variance]]
    rw [integral_sqNorm_reconstruction_eq_sigma_sq_noiseAmplificationTrace
      (μ := μ) (η := η) (σ := σ) hη Rα]
  -- Route correction: after the pointwise orthogonal split, the theorem is a flat integral split.
  rw [expectedSqEstimationError_def, hPointwise, hAssoc, hSplit, hCrossVarianceSplit, hCrossZero,
    hVariance, MeasureTheory.integral_const]
  simp [bias, floor]

/-- The deterministic bias term from Proposition 7.6 rewrites, under the
Chapter 7 SVD/filter setup, as the spectral sum over the
`Null(K_n)^⊥`-component of `fTrue`. -/
theorem projectedBias_sq_eq_spectralSum_of_spectralRep
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    ‖Rα.toEuclideanLin (K.toEuclideanLin fTrue) -
        (fTrue -
          nullspaceComponent K.toEuclideanLin.toContinuousLinearMap
            fTrue)‖ ^ 2 =
      ∑ i : n,
          (1 - wα (s i ^ 2)) ^ 2 *
            (((Vᵀ).toEuclideanLin
                (fTrue -
                  nullspaceComponent K.toEuclideanLin.toContinuousLinearMap
                    fTrue)) i) ^ 2 := by
  let floor : EuclideanSpace ℝ n :=
    nullspaceComponent K.toEuclideanLin.toContinuousLinearMap fTrue
  let proj : EuclideanSpace ℝ n := fTrue - floor
  let ξ : EuclideanSpace ℝ n := (Vᵀ).toEuclideanLin proj
  let d : n → ℝ := fun i ↦ wα (s i ^ 2) - 1
  have hForward :
      K.toEuclideanLin proj = K.toEuclideanLin fTrue := by
    -- Replace `fTrue` by its projected component before moving to spectral coordinates.
    simpa [proj, floor] using
      forward_sub_nullspaceComponent_eq_forward
        (Kclm := K.toEuclideanLin.toContinuousLinearMap) (x := fTrue)
  have hBias :
      Rα.toEuclideanLin (K.toEuclideanLin fTrue) - proj =
        V.toEuclideanLin ((Matrix.diagonal d).toEuclideanLin ξ) := by
    -- Route correction: first rewrite the deterministic bias through the projected component,
    -- then move directly to the stable `V`-coordinate diagonal normal form.
    rw [← hForward]
    simpa [floor, proj, ξ, d] using
      reconstructionOnProjectedComponent_eq_orthogonalDiagonalDeviation
        (K := K) (U := U) (V := V) (Rα := Rα) (wα := wα) (s := s)
        hK hRα fTrue
  have hDiagNorm :
      ‖V.toEuclideanLin ((Matrix.diagonal d).toEuclideanLin ξ)‖ ^ 2 =
        ‖(Matrix.diagonal d).toEuclideanLin ξ‖ ^ 2 := by
    -- Orthogonal changes of basis preserve Euclidean norm.
    rw [orthogonalGroup_toEuclideanLin_norm_sq_eq V hRα.orthogonalV
      ((Matrix.diagonal d).toEuclideanLin ξ)]
  have hSign :
      ∑ i : n, (d i) ^ 2 * (ξ i) ^ 2 =
        ∑ i : n, (1 - wα (s i ^ 2)) ^ 2 * (ξ i) ^ 2 := by
    -- Squaring removes the sign change between `wα - 1` and `1 - wα`.
    refine Finset.sum_congr rfl ?_
    intro i _
    dsimp [d]
    ring
  -- Normalize the bias to the orthogonal-diagonal form, drop the orthogonal factor, and read
  -- the remaining diagonal operator coordinatewise.
  rw [hBias, hDiagNorm, diagonal_toEuclideanLin_normSq_eq_coordinateSum, hSign]

/-- Under the Chapter 7 reconstruction spectral-representation owner for `Rα`,
the variance owner
`noiseAmplificationTrace Rα.toEuclideanLin.toContinuousLinearMap` rewrites as
the spectral sum from Lemma 7.5(5), with the zero singular-value case handled
by the Chapter 7 convention `wα 0 = 0`. -/
theorem noiseAmplificationTrace_eq_spectralSum_of_spectralRep
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    noiseAmplificationTrace Rα.toEuclideanLin.toContinuousLinearMap =
      ∑ i : n, (wα (s i ^ 2)) ^ 2 / (s i ^ 2) := by
  -- Rewrite the abstract trace owner through the concrete matrix trace from Lemma 7.5(5).
  rw [noiseAmplificationTrace_toEuclideanLin_eq_matrixTrace_transpose_mul]
  exact reconstruction_trace_transpose_mul_of_spectralRep hRα

/-- Proposition 7.6. Combining the operator-level expected-error decomposition with
the deterministic spectral-bias rewrite and the Lemma 7.5 variance rewrite
yields the full spectral expected-error formula `(7.45)` without a full-rank
assumption, using `wα 0 = 0` to cover zero singular values and using only the
`Null(K_n)^⊥` component of `f_true` in the spectral bias sum. -/
theorem expectedSqEstimationError_eq_spectralBias_add_spectralVariance
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ)
    (hK : K = U * Matrix.diagonal s * Vᵀ)
    (hRα : HasReconstructionSpectralRep Rα U V wα s) :
    expectedSqEstimationError μ Rα.toEuclideanLin.toContinuousLinearMap
        K.toEuclideanLin.toContinuousLinearMap fTrue η =
      ∑ i : n,
          (1 - wα (s i ^ 2)) ^ 2 *
            (((Vᵀ).toEuclideanLin
                (fTrue -
                  nullspaceComponent K.toEuclideanLin.toContinuousLinearMap
                    fTrue)) i) ^ 2 +
        ‖nullspaceComponent K.toEuclideanLin.toContinuousLinearMap fTrue‖ ^ 2 +
        σ ^ 2 * ∑ i : n, (wα (s i ^ 2)) ^ 2 / (s i ^ 2) := by
  -- Assemble the full spectral formula by rewriting the bias and variance terms separately.
  rw [expectedSqEstimationError_eq_projectedBias_add_noiseAmplification
    (μ := μ) (K := K) (U := U) (V := V) (Rα := Rα) (wα := wα) (s := s)
    (fTrue := fTrue) (η := η) (σ := σ) hη hK hRα]
  rw [projectedBias_sq_eq_spectralSum_of_spectralRep
    (K := K) (U := U) (V := V) (Rα := Rα) (wα := wα) (s := s)
    (fTrue := fTrue) hK hRα]
  rw [noiseAmplificationTrace_eq_spectralSum_of_spectralRep
    (Rα := Rα) (U := U) (V := V) (wα := wα) (s := s) hRα]

end

end FilterRegularization

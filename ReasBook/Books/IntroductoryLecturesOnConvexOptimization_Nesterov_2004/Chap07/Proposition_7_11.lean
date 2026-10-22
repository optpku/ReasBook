/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace Topology

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/-- Helper for Proposition 7.11: endow ambient real matrices with the Frobenius normed-group
structure so matrix-valued derivatives use the intended Chapter 5 topology. -/
local instance ambientMatrixNormedAddCommGroup : NormedAddCommGroup Mat :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Proposition 7.11: scalar multiplication on ambient real matrices is measured with
the Frobenius norm. -/
local instance ambientMatrixNormedSpace : NormedSpace ℝ Mat :=
  Matrix.frobeniusNormedSpace

/-- Helper for Proposition 7.11: the Frobenius norm supplies the ambient matrix pseudometric. -/
local instance ambientMatrixPseudoMetricSpace : PseudoMetricSpace Mat := by
  infer_instance

/-- Helper for Proposition 7.11: the Frobenius matrix pseudometric induces the uniform structure
used by the derivative APIs below. -/
local instance ambientMatrixUniformSpace : UniformSpace Mat :=
  ambientMatrixPseudoMetricSpace.toUniformSpace

/-- Helper for Proposition 7.11: the matrix derivative lemmas below use the Frobenius topological
space rather than the default product topology on entries. -/
local instance ambientMatrixTopologicalSpace : TopologicalSpace Mat :=
  ambientMatrixUniformSpace.toTopologicalSpace

/- Proposition 7.11 lies in Chapter 7's positive-definite matrix-path / log-determinant potential
domain.

Sampled owner-style declarations:
- `logDetBarrierAmbient` and `logDetBarrier` in `Chap05/Definition_5_4_4_5`, the chapter owners
  for the ambient `-log det` formula and its intrinsic positive-definite barrier;
- `logDetBarrier_lineDeriv_eq_frobeniusInner` and its second-directional companion in
  `Chap05/Lemma_5_4_4_1`, the canonical derivative owners for the same matrix potential;
- `Matrix.PosDef`, the canonical matrix-level positivity owner used to justify the logarithmic
  domain.

Best owner abstraction:
- source-facing: the scalar path potential `V(α) = log (det G(0) / det G(α))`;
- core/canonical: the Chapter 5 ambient owner `logDetBarrierAmbient n`;
- bridge/view: the determinant-ratio formula and the trace identities obtained by differentiating
  along the scalar path.

Primitive data:
- the matrix path `G : ℝ → Mat`;
- the parameter family `τ : Fin n → ℝ`;
- positivity of `G α` near `α = 0`;
- differentiability of `G` and of its scalar derivative at `0`.

Derived API:
- the source-facing ratio potential;
- the Chapter 5 bridge expressing that potential as a difference of ambient `-log det` terms on
  the positive-definite locus;
- the first- and second-derivative identities at `α = 0`.

This refinement keeps the source-facing scalar potential, but removes the duplicate derivative
witness data `G₁`, `G₂` from the public theorem surface: the canonical derivatives are
`deriv G 0` and `deriv (deriv G) 0`, while the Chapter 5 barrier owner remains the core
matrix-level abstraction behind the formulas.
-/

/-- The logarithmic determinant-ratio potential
`V(α) = log (det G(0) / det G(α))` attached to a matrix path `G`. -/
def logDetRatioPotential
    (G : ℝ → Mat) (α : ℝ) : ℝ :=
  Real.log (Matrix.det (G 0) / Matrix.det (G α))

/-- Expanding `logDetRatioPotential G α` gives the determinant-ratio formula
`log (det G(0) / det G(α))`. -/
theorem logDetRatioPotential_def
    (G : ℝ → Mat) (α : ℝ) :
    logDetRatioPotential G α =
      Real.log (Matrix.det (G 0) / Matrix.det (G α)) := rfl

/- On the positive-definite locus, the source-facing determinant-ratio potential is the difference
of the Chapter 5 ambient barrier values at `G α` and `G 0`. -/
theorem logDetRatioPotential_eq_sub_logDetBarrierAmbient
    (G : ℝ → Mat) {α : ℝ} (hG0 : (G 0).PosDef) (hGα : (G α).PosDef) :
    logDetRatioPotential G α =
      logDetBarrierAmbient n
          (⟨G α, by
            rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
            simpa [Matrix.IsHermitian, Matrix.IsSymm] using hGα.isHermitian⟩ : SymmMat) -
        logDetBarrierAmbient n
          (⟨G 0, by
            rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
            simpa [Matrix.IsHermitian, Matrix.IsSymm] using hG0.isHermitian⟩ : SymmMat) := by
  rw [logDetRatioPotential, logDetBarrierAmbient_apply, logDetBarrierAmbient_apply,
    Real.log_div hG0.det_pos.ne' hGα.det_pos.ne']
  ring_nf

/-- Helper for Proposition 7.11: a positive-definite real matrix determines a point of the
ambient symmetric-matrix space. -/
private theorem mem_symmMat_of_posDef
    {X : Mat} (hX : X.PosDef) :
    X ∈ SymmMat := by
  -- Positive definiteness gives symmetry, so the matrix lies in the real symmetric carrier.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using hX.isHermitian

/-- Helper for Proposition 7.11: positivity in a punctured neighborhood already gives the
positive-definite base point at `α = 0`. -/
private theorem posDef_at_zero_of_posDef_near_zero
    (G : ℝ → Mat)
    (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef) :
    (G 0).PosDef := by
  rcases hpos with ⟨ε, hεpos, hε⟩
  -- Evaluate the neighborhood hypothesis at `α = 0`.
  exact hε (by simpa using hεpos)

/-- Helper for Proposition 7.11: positivity near `0` yields a totalized symmetric wrapper whose
ambient barrier difference agrees locally with the determinant-ratio potential. -/
private theorem exists_symmetric_wrapper_eventually_eq_logDetRatioPotential
    (G : ℝ → Mat)
    (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef) :
    ∃ Γ : ℝ → SymmMat,
      logDetRatioPotential G =ᶠ[𝓝 0]
        fun α ↦ logDetBarrierAmbient n (Γ α) - logDetBarrierAmbient n (Γ 0) := by
  rcases hpos with ⟨ε, hεpos, hε⟩
  have hG0 : (G 0).PosDef :=
    posDef_at_zero_of_posDef_near_zero G ⟨ε, hεpos, hε⟩
  let Γ : ℝ → SymmMat := fun α ↦
    if hα : |α| < ε then
      ⟨G α, mem_symmMat_of_posDef (hε hα)⟩
    else
      ⟨G 0, mem_symmMat_of_posDef hG0⟩
  refine ⟨Γ, ?_⟩
  have hsmall : ∀ᶠ α in 𝓝 0, |α| < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hεpos] with α hα
    simpa [Metric.mem_ball, Real.dist_eq] using hα
  filter_upwards [hsmall] with α hα
  have hαpos : (G α).PosDef := hε hα
  have hΓα :
      Γ α = (⟨G α, mem_symmMat_of_posDef hαpos⟩ : SymmMat) := by
    simp [Γ, hα]
  have hΓ0 :
      Γ 0 = (⟨G 0, mem_symmMat_of_posDef hG0⟩ : SymmMat) := by
    have h0 : |(0 : ℝ)| < ε := by
      simpa using hεpos
    simp [Γ]
  -- On the small positive-definite neighborhood, rewrite the source potential through the
  -- Chapter 5 ambient barrier bridge.
  calc
    logDetRatioPotential G α
        =
          logDetBarrierAmbient n
              (⟨G α, mem_symmMat_of_posDef hαpos⟩ : SymmMat) -
            logDetBarrierAmbient n
              (⟨G 0, mem_symmMat_of_posDef hG0⟩ : SymmMat) := by
            simpa using
              logDetRatioPotential_eq_sub_logDetBarrierAmbient G hG0 hαpos
    _ = logDetBarrierAmbient n (Γ α) - logDetBarrierAmbient n (Γ 0) := by
          rw [hΓα, hΓ0]

/-- Helper for Proposition 7.11: neighborhood equality at `0` transfers both the first
derivative and the second iterated derivative. -/
private theorem deriv_iteratedDeriv_two_eq_of_eventuallyEq
    {f g : ℝ → ℝ}
    (hEq : f =ᶠ[𝓝 0] g) :
    deriv f 0 = deriv g 0 ∧
      iteratedDeriv 2 f 0 = iteratedDeriv 2 g 0 := by
  constructor
  · -- The first derivative is local, so the neighborhood equality identifies `deriv` at `0`.
    exact Filter.EventuallyEq.deriv_eq hEq
  · -- The same locality principle applies to the second iterated derivative.
    exact Filter.EventuallyEq.iteratedDeriv_eq 2 hEq

/-- Helper for Proposition 7.11: negating the source first trace identity gives the target
formula `n - ∑ τᵢ`. -/
private theorem neg_sum_tau_sub_one_eq_dim_sub_sum
    (τ : Fin n → ℝ) :
    -(∑ i : Fin n, (τ i - 1)) = (n : ℝ) - ∑ i : Fin n, τ i := by
  -- Expand the finite sum of `(τ i - 1)` and collect the constant contribution `n`.
  calc
    -(∑ i : Fin n, (τ i - 1))
        = -((∑ i : Fin n, τ i) - ∑ i : Fin n, (1 : ℝ)) := by
            rw [Finset.sum_sub_distrib]
    _ = -((∑ i : Fin n, τ i) - n) := by
          simp
    _ = (n : ℝ) - ∑ i : Fin n, τ i := by
          ring

/-- Helper for Proposition 7.11: the assumed first trace identity already has the target
right-hand side after negation. -/
private theorem neg_trace_first_identity_eq_dimension_sub_sum
    (G : ℝ → Mat) (τ : Fin n → ℝ)
    (htrace₁ : Matrix.trace ((G 0)⁻¹ * deriv G 0) = ∑ i : Fin n, (τ i - 1)) :
    -Matrix.trace ((G 0)⁻¹ * deriv G 0) = (n : ℝ) - ∑ i : Fin n, τ i := by
  -- Substitute the trace identity and collapse the scalar sum.
  rw [htrace₁]
  exact neg_sum_tau_sub_one_eq_dim_sub_sum τ

/-- Helper for Proposition 7.11: the assumed second trace identity already has the target
right-hand side after negation. -/
private theorem neg_trace_second_identity_eq_sum_sq
    (G : ℝ → Mat) (τ : Fin n → ℝ)
    (htrace₂ :
      Matrix.trace
          ((G 0)⁻¹ * deriv (deriv G) 0 - (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) =
        -∑ i : Fin n, (τ i - 1) ^ (2 : ℕ)) :
    -Matrix.trace
        ((G 0)⁻¹ * deriv (deriv G) 0 - (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) =
      ∑ i : Fin n, (τ i - 1) ^ (2 : ℕ) := by
  -- Negating the assumed identity matches the target second-derivative sign convention.
  rw [htrace₂]
  ring

/-- Helper for Proposition 7.11: replacing one row of the identity by a row vector has
determinant equal to the diagonal entry of that row. -/
private theorem det_updateRow_one
    (i : Fin n) (u : Fin n → ℝ) :
    Matrix.det ((1 : Mat).updateRow i u) = u i := by
  -- Expand the new row in the standard basis of rows of the identity matrix.
  have hrow :
      (∑ k, (u k) • ((1 : Mat) k)) = u := by
    funext j
    simp [Pi.smul_apply, Matrix.one_apply]
  calc
    Matrix.det ((1 : Mat).updateRow i u)
        = Matrix.det ((1 : Mat).updateRow i (∑ k, (u k) • ((1 : Mat) k))) := by
            rw [hrow]
    _ = u i • Matrix.det (1 : Mat) := Matrix.det_updateRow_sum (1 : Mat) i u
    _ = u i := by simp

/-- Helper for Proposition 7.11: `trace` as a continuous linear functional on square matrices. -/
private def traceContinuousLinearMap : Mat →L[ℝ] ℝ :=
  let traceLinear : Mat →ₗ[ℝ] ℝ :=
    { toFun := Matrix.trace
      map_add' := by
        intro A B
        exact Matrix.trace_add A B
      map_smul' := by
        intro c A
        exact Matrix.trace_smul c A }
  { toLinearMap := traceLinear
    cont := traceLinear.continuous_of_finiteDimensional }

/-- Evaluating the continuous trace functional recovers the ordinary matrix trace. -/
@[simp] private theorem traceContinuousLinearMap_apply
    (M : Mat) :
    traceContinuousLinearMap M = Matrix.trace M :=
  by simp [traceContinuousLinearMap]

/-- Helper for Proposition 7.11: left multiplication by a fixed matrix, bundled as a continuous
linear map on square matrices. -/
private def leftMulContinuousLinearMap (X : Mat) : Mat →L[ℝ] Mat :=
  ⟨LinearMap.mulLeft ℝ X, (LinearMap.mulLeft ℝ X).continuous_of_finiteDimensional⟩

/-- Evaluating the bundled left-multiplication map recovers ordinary matrix multiplication. -/
@[simp] private theorem leftMulContinuousLinearMap_apply
    (X Y : Mat) :
    leftMulContinuousLinearMap X Y = X * Y :=
  rfl

/-- Helper for Proposition 7.11: Jacobi's normalization reconstructs the original path from the
increment `(G 0)⁻¹ * (G α - G 0)`. -/
private theorem normalized_path_reconstruct
    (G : ℝ → Mat) (hG0 : (G 0).PosDef) (α : ℝ) :
    G 0 * ((1 : Mat) + (G 0)⁻¹ * (G α - G 0)) = G α := by
  have hunit : IsUnit (Matrix.det (G 0)) := isUnit_iff_ne_zero.mpr hG0.det_pos.ne'
  -- Expand the normalized increment and cancel `G 0 * (G 0)⁻¹` using nonsingularity.
  calc
    G 0 * ((1 : Mat) + (G 0)⁻¹ * (G α - G 0))
        = G 0 * (1 : Mat) + G 0 * ((G 0)⁻¹ * (G α - G 0)) := by
            rw [Matrix.mul_add]
    _ = G 0 + (G 0 * (G 0)⁻¹) * (G α - G 0) := by
          rw [Matrix.mul_one, Matrix.mul_assoc]
    _ = G 0 + (1 : Mat) * (G α - G 0) := by
          rw [Matrix.mul_nonsing_inv _ hunit]
    _ = G 0 + (G α - G 0) := by simp
    _ = G α := by
          simp [sub_eq_add_neg, add_left_comm]

/-- Helper for Proposition 7.11: the determinant alternating map is continuous on row tuples. -/
private theorem detRowAlternating_continuous :
    Continuous (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^(Fin n)]→ₗ[ℝ] ℝ) := by
  -- The determinant is continuous as a polynomial in the matrix entries.
  simpa [Matrix.det] using
    continuous_id.matrix_det

/-- Helper for Proposition 7.11: continuity gives the determinant alternating map a global norm
bound. -/
private theorem detRowAlternating_exists_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ m : Fin n → Fin n → ℝ, ‖Matrix.detRowAlternating m‖ ≤ C * ∏ i : Fin n, ‖m i‖ := by
  -- Apply the general boundedness theorem for continuous alternating maps.
  let detLinear : (Fin n → ℝ) [⋀^(Fin n)]→ₗ[ℝ] ℝ := Matrix.detRowAlternating
  exact AlternatingMap.exists_bound_of_continuous detLinear detRowAlternating_continuous

/-- Helper for Proposition 7.11: the determinant, bundled as a continuous alternating map in the
rows. -/
private def detContinuousAlternating : (Fin n → ℝ) [⋀^(Fin n)]→L[ℝ] ℝ :=
  let detLinear : (Fin n → ℝ) [⋀^(Fin n)]→ₗ[ℝ] ℝ := Matrix.detRowAlternating
  let C : ℝ := Classical.choose detRowAlternating_exists_bound
  AlternatingMap.mkContinuous
    detLinear
    C
    (Classical.choose_spec detRowAlternating_exists_bound).2

/-- Helper for Proposition 7.11: the linear derivative of the continuous determinant owner at the
identity is the trace functional. -/
private theorem detContinuousAlternating_linearDeriv_one_eq_trace :
    detContinuousAlternating.linearDeriv (1 : Mat) =
      traceContinuousLinearMap := by
  ext M
  -- Expand the alternating-map derivative into the sum of single-row replacements.
  calc
    (detContinuousAlternating.linearDeriv (1 : Mat)) M
        =
          ∑ i : Fin n,
            detContinuousAlternating (Function.update (1 : Mat) i (M i)) := by
              exact
                detContinuousAlternating.toContinuousMultilinearMap.linearDeriv_apply
                  (1 : Mat) M
    _ = ∑ i : Fin n, M i i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          -- Replacing one row of the identity keeps only the corresponding diagonal entry.
          simpa [detContinuousAlternating] using det_updateRow_one i (M i)
    _ = Matrix.trace M := by
          simp [Matrix.trace]
    _ = traceContinuousLinearMap M := by
          rw [traceContinuousLinearMap_apply]

/-- Helper for Proposition 7.11: the determinant itself has Fréchet derivative `trace` at the
identity matrix. -/
private theorem hasFDerivAt_det_at_one :
    HasFDerivAt
      Matrix.det
      traceContinuousLinearMap
      (1 : Mat) := by
  -- Differentiate the determinant directly on the raw row tuple space at the identity.
  have hraw :
      HasFDerivAt
        (detContinuousAlternating : Mat → ℝ)
        (detContinuousAlternating.linearDeriv (1 : Mat))
        (1 : Mat) :=
    detContinuousAlternating.hasFDerivAt (1 : Mat)
  change HasFDerivAt
    Matrix.det
    (detContinuousAlternating.linearDeriv (1 : Mat))
    (1 : Mat) at hraw
  simpa [detContinuousAlternating_linearDeriv_one_eq_trace] using hraw

/-- Helper for Proposition 7.11: the Fréchet derivative of `M ↦ det (1 + M)` at `0` is the trace
functional. -/
private theorem hasFDerivAt_det_one_add_zero :
    HasFDerivAt
      (fun M : Mat ↦ Matrix.det ((1 : Mat) + M))
      traceContinuousLinearMap
      0 := by
  have hshift :
      HasFDerivAt
        (fun M : Mat ↦ (1 : Mat) + M)
        (1 : Mat →L[ℝ] Mat)
        0 := by
    -- The translation `M ↦ 1 + M` is affine with derivative the identity.
    simpa [add_comm] using (hasFDerivAt_id (0 : Mat)).const_add (1 : Mat)
  have hdet :
      HasFDerivAt
        Matrix.det
        traceContinuousLinearMap
        ((fun M : Mat ↦ (1 : Mat) + M) 0) := by
    -- Re-express the determinant owner at the shifted base point `1 + 0 = 1`.
    simpa using hasFDerivAt_det_at_one
  -- Compose the determinant derivative at the identity with the affine shift `M ↦ 1 + M`.
  simpa using hdet.comp (0 : Mat) hshift

/-- Helper for Proposition 7.11: if `A(0) = 0`, then the determinant slice
`α ↦ det (1 + A(α))` has first derivative `trace (A'(0))`. -/
private theorem hasDerivAt_det_one_add_path_at_zero
    (A : ℝ → Mat) (hA0 : A 0 = 0) (hA : DifferentiableAt ℝ A 0) :
    HasDerivAt
      (fun α ↦ Matrix.det ((1 : Mat) + A α))
      (Matrix.trace (deriv A 0))
      0 := by
  have hA' : HasDerivAt A (deriv A 0) 0 := by
    -- Under the Frobenius matrix topology, the derivative of the path is the canonical `deriv`.
    simpa using hA.hasDerivAt
  have hcomp :
      HasDerivAt
        (fun α ↦ Matrix.det ((1 : Mat) + A α))
        (traceContinuousLinearMap (deriv A 0))
        0 := by
    -- Differentiate the determinant slice by composing the shifted determinant owner with `A`.
    simpa [Function.comp, hA0] using
      hasFDerivAt_det_one_add_zero.comp_hasDerivAt_of_eq 0 hA' hA0.symm
  -- Evaluating the continuous trace functional gives the textbook scalar derivative.
  simpa [traceContinuousLinearMap_apply] using hcomp

/-- Helper for Proposition 7.11: the determinant of a differentiable matrix path has the Jacobi
first derivative `det(G(0)) * trace(G(0)⁻¹ G'(0))` at `0`. -/
private theorem hasDerivAt_det_path_at_zero
    (G : ℝ → Mat) (hG0 : (G 0).PosDef) (hG₁ : DifferentiableAt ℝ G 0) :
    HasDerivAt
      (fun α ↦ Matrix.det (G α))
      (Matrix.det (G 0) * Matrix.trace ((G 0)⁻¹ * deriv G 0))
      0 := by
  letI : NormedRing Mat := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
  let A : ℝ → Mat := fun α ↦ (G 0)⁻¹ * (G α - G 0)
  have hG' : HasDerivAt G (deriv G 0) 0 := by
    -- The Frobenius matrix topology turns the path differentiability hypothesis into `HasDerivAt`.
    simpa using hG₁.hasDerivAt
  have hA0 : A 0 = 0 := by
    -- The normalized increment vanishes at the base point.
    simp [A]
  have hA' :
      HasDerivAt A ((G 0)⁻¹ * deriv G 0) 0 := by
    have hsub : HasDerivAt (fun α ↦ G α - G 0) (deriv G 0) 0 := by
      -- Subtracting the constant base matrix does not change the derivative.
      simpa using hG'.sub_const (G 0)
    -- Left multiplication by the fixed inverse matrix transports the derivative of the increment.
    simpa [A] using hsub.const_mul ((G 0)⁻¹)
  have hdetNormalized :
      HasDerivAt
        (fun α ↦ Matrix.det ((1 : Mat) + A α))
        (Matrix.trace ((G 0)⁻¹ * deriv G 0))
        0 := by
    -- Differentiate the normalized determinant slice and then substitute the derivative of `A`.
    simpa [hA'.deriv] using
      hasDerivAt_det_one_add_path_at_zero A hA0 hA'.differentiableAt
  have hscaled :
      HasDerivAt
        (fun α ↦ Matrix.det (G 0) * Matrix.det ((1 : Mat) + A α))
        (Matrix.det (G 0) * Matrix.trace ((G 0)⁻¹ * deriv G 0))
        0 := by
    -- Multiplying the normalized determinant path by the constant factor `det(G 0)` restores the
    -- Jacobi scalar prefactor.
    simpa using hdetNormalized.const_mul (Matrix.det (G 0))
  have hrewrite :
      (fun α ↦ Matrix.det (G α)) =
        fun α ↦ Matrix.det (G 0) * Matrix.det ((1 : Mat) + A α) := by
    funext α
    -- Reconstruct `G α` from its normalized increment and then split the determinant.
    calc
      Matrix.det (G α)
          = Matrix.det (G 0 * ((1 : Mat) + A α)) := by
              rw [normalized_path_reconstruct G hG0 α]
      _ = Matrix.det (G 0) * Matrix.det ((1 : Mat) + A α) := by
            rw [Matrix.det_mul]
  -- Rewrite the determinant path through the normalized factorization and use the differentiated
  -- scalar product formula.
  simpa [hrewrite] using hscaled

/-- Helper for Proposition 7.11: positivity near `0` lets us rewrite the ratio potential locally
as the difference of two scalar logarithms. -/
private theorem logDetRatioPotential_eventually_eq_sub_logs
    (G : ℝ → Mat)
    (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef) :
    logDetRatioPotential G =ᶠ[𝓝 0]
      fun α ↦ Real.log (Matrix.det (G 0)) - Real.log (Matrix.det (G α)) := by
  rcases hpos with ⟨ε, hεpos, hε⟩
  have hG0 : (G 0).PosDef :=
    posDef_at_zero_of_posDef_near_zero G ⟨ε, hεpos, hε⟩
  have hsmall : ∀ᶠ α in 𝓝 0, |α| < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hεpos] with α hα
    simpa [Metric.mem_ball, Real.dist_eq] using hα
  filter_upwards [hsmall] with α hα
  have hGα : (G α).PosDef := hε hα
  -- On the positive-definite neighborhood, `log (a / b) = log a - log b`.
  rw [logDetRatioPotential, Real.log_div hG0.det_pos.ne' hGα.det_pos.ne']

/-- Helper for Proposition 7.11: the first derivative of the source ratio potential is the raw
`-trace(G(0)⁻¹ G'(0))` formula. -/
private theorem hasDerivAt_logDetRatioPotential_raw_at_zero
    (G : ℝ → Mat)
    (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef)
    (hG₁ : DifferentiableAt ℝ G 0) :
    HasDerivAt
      (logDetRatioPotential G)
      (-Matrix.trace ((G 0)⁻¹ * deriv G 0))
      0 := by
  have hG0 : (G 0).PosDef :=
    posDef_at_zero_of_posDef_near_zero G hpos
  have hdet :
      HasDerivAt
        (fun α ↦ Matrix.det (G α))
        (Matrix.det (G 0) * Matrix.trace ((G 0)⁻¹ * deriv G 0))
        0 :=
    hasDerivAt_det_path_at_zero G hG0 hG₁
  have hlog :
      HasDerivAt
        (fun α ↦ Real.log (Matrix.det (G α)))
        ((Matrix.det (G 0) * Matrix.trace ((G 0)⁻¹ * deriv G 0)) / Matrix.det (G 0))
        0 := by
    -- Differentiate the logarithm of the determinant path using the Jacobi owner for `det`.
    exact hdet.log hG0.det_pos.ne'
  have hsub :
      HasDerivAt
        (fun α ↦ Real.log (Matrix.det (G 0)) - Real.log (Matrix.det (G α)))
        (-Matrix.trace ((G 0)⁻¹ * deriv G 0))
        0 := by
    -- The constant `log det(G 0)` contributes no derivative; only the logarithmic path remains.
    have hconstSub := hlog.const_sub (Real.log (Matrix.det (G 0)))
    have hcancel :
        -((Matrix.det (G 0) * Matrix.trace ((G 0)⁻¹ * deriv G 0)) / Matrix.det (G 0)) =
          -Matrix.trace ((G 0)⁻¹ * deriv G 0) := by
      field_simp [hG0.det_pos.ne']
    exact hconstSub.congr_deriv hcancel
  -- Transfer the derivative through the local source rewrite `log(a / b) = log a - log b`.
  exact hsub.congr_of_eventuallyEq
    (logDetRatioPotential_eventually_eq_sub_logs G hpos)

/-- Helper for Proposition 7.11: the inverse path `α ↦ G(α)⁻¹` has derivative
`-G(0)⁻¹ G'(0) G(0)⁻¹` at `0`. -/
private theorem hasDerivAt_matrix_inverse_path_at_zero
    (G : ℝ → Mat)
    (hG0 : (G 0).PosDef)
    (hG₁ : DifferentiableAt ℝ G 0) :
    HasDerivAt
      (fun α ↦ (G α)⁻¹)
      (-(G 0)⁻¹ * deriv G 0 * (G 0)⁻¹)
      0 := by
  letI : NormedRing Mat := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
  letI : Invertible (G 0) := hG0.isUnit.invertible
  have hG' : HasDerivAt G (deriv G 0) 0 := by
    -- The Frobenius matrix topology turns the path differentiability hypothesis into `HasDerivAt`.
    simpa using hG₁.hasDerivAt
  have hInv :
      HasFDerivAt
        Ring.inverse
        (-ContinuousLinearMap.mulLeftRight ℝ Mat (⅟ (G 0)) (⅟ (G 0)))
        (G 0) := by
    -- Specialize the normed-ring inverse derivative owner at the positive-definite base point.
    simpa using
      (hasFDerivAt_ringInverse (unitOfInvertible (G 0)))
  have hComp :
      HasDerivAt
        (Ring.inverse ∘ G)
        (-(⅟ (G 0)) * deriv G 0 * ⅟ (G 0))
        0 := by
    -- Compose the abstract inverse derivative with the scalar path `G`.
    simpa [ContinuousLinearMap.mulLeftRight_apply, Function.comp, Matrix.mul_assoc] using
      hInv.comp_hasDerivAt 0 hG'
  have hEq :
      (fun α ↦ (G α)⁻¹) =ᶠ[𝓝 0] (Ring.inverse ∘ G) := by
    -- Matrix inversion agrees pointwise with `Ring.inverse`.
    filter_upwards with α
    simp [Function.comp, Matrix.nonsing_inv_eq_ringInverse]
  -- Compose the matrix inverse derivative with the scalar path `G`.
  refine (hComp.congr_of_eventuallyEq hEq).congr_deriv ?_
  simp [Matrix.invOf_eq_nonsing_inv, Matrix.mul_assoc]

/-- Helper for Proposition 7.11: the matrix-valued Jacobi integrand
`α ↦ G(α)⁻¹ * G'(α)` has derivative
`G(0)⁻¹ G''(0) - G(0)⁻¹ G'(0) G(0)⁻¹ G'(0)` at `0`. -/
private theorem hasDerivAt_inverse_mul_deriv_path_at_zero
    (G : ℝ → Mat)
    (hG0 : (G 0).PosDef)
    (hG₁ : DifferentiableAt ℝ G 0)
    (hG₂ : DifferentiableAt ℝ (deriv G) 0) :
    HasDerivAt
      (fun α ↦ (G α)⁻¹ * deriv G α)
      ((G 0)⁻¹ * deriv (deriv G) 0 -
        (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0)
      0 := by
  letI : NormedRing Mat := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
  have hInv :
      HasDerivAt
        (fun α ↦ (G α)⁻¹)
        (-(G 0)⁻¹ * deriv G 0 * (G 0)⁻¹)
        0 :=
    hasDerivAt_matrix_inverse_path_at_zero G hG0 hG₁
  have hDerivG : HasDerivAt (deriv G) (deriv (deriv G) 0) 0 := by
    -- The second differentiability hypothesis is exactly the derivative owner for `deriv G`.
    simpa using hG₂.hasDerivAt
  have hMul :
      HasDerivAt
        (fun α ↦ (G α)⁻¹ * deriv G α)
        ((-(G 0)⁻¹ * deriv G 0 * (G 0)⁻¹) * deriv G 0 +
          (G 0)⁻¹ * deriv (deriv G) 0)
        0 := by
    -- Differentiate the noncommutative product before applying `trace`.
    simpa using hInv.mul hDerivG
  -- Reassociate the product-rule output into the textbook matrix expression.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Matrix.mul_assoc] using hMul

/-- Helper for Proposition 7.11: differentiating the raw trace integrand
`α ↦ trace(G(α)⁻¹ G'(α))` at `0` produces the textbook second-order matrix expression. -/
private theorem hasDerivAt_trace_inverse_mul_deriv_at_zero
    (G : ℝ → Mat)
    (hG0 : (G 0).PosDef)
    (hG₁ : DifferentiableAt ℝ G 0)
    (hG₂ : DifferentiableAt ℝ (deriv G) 0) :
    HasDerivAt
      (fun α ↦ Matrix.trace ((G α)⁻¹ * deriv G α))
      (Matrix.trace
        ((G 0)⁻¹ * deriv (deriv G) 0 -
          (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0))
      0 := by
  have hMatrix :
      HasDerivAt
        (fun α ↦ (G α)⁻¹ * deriv G α)
        ((G 0)⁻¹ * deriv (deriv G) 0 -
          (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0)
        0 :=
    hasDerivAt_inverse_mul_deriv_path_at_zero G hG0 hG₁ hG₂
  have hTraceComp :
      HasDerivAt
        (fun α ↦ traceContinuousLinearMap ((G α)⁻¹ * deriv G α))
        (traceContinuousLinearMap
          ((G 0)⁻¹ * deriv (deriv G) 0 -
            (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0))
        0 :=
    traceContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hMatrix
  -- Postcompose the matrix-valued product derivative with the continuous trace functional.
  simpa [traceContinuousLinearMap_apply, Matrix.trace_sub] using hTraceComp

/-- Helper for Proposition 7.11: neighborhood `C²` control on `G` yields the local Jacobi
identity for the derivative of the determinant-ratio potential. -/
private theorem hasDerivAt_logDetRatioPotential_raw_at
    (G : ℝ → Mat) {α : ℝ}
    (hG0 : (G 0).PosDef)
    (hposα : ∃ ε > 0, ∀ ⦃β : ℝ⦄, |β| < ε → (G (β + α)).PosDef)
    (hGdiff : DifferentiableAt ℝ G α) :
    HasDerivAt
      (logDetRatioPotential G)
      (-Matrix.trace ((G α)⁻¹ * deriv G α))
      α := by
  let H : ℝ → Mat := fun β ↦ G (β + α)
  have hHpos : ∃ ε > 0, ∀ ⦃β : ℝ⦄, |β| < ε → (H β).PosDef := by
    rcases hposα with ⟨ε, hεpos, hε⟩
    refine ⟨ε, hεpos, ?_⟩
    intro β hβ
    simpa [H] using hε hβ
  have hHdiff : DifferentiableAt ℝ H 0 := by
    -- Compose the original path with the translation `β ↦ β + α`.
    have hGdiffShift : DifferentiableAt ℝ G (((fun β : ℝ ↦ β + α) 0)) := by
      simpa using hGdiff
    simpa [H] using
      hGdiffShift.comp 0 (((hasDerivAt_id 0).add_const α).differentiableAt)
  have hbase :
      HasDerivAt
        (logDetRatioPotential H)
        (-Matrix.trace ((G α)⁻¹ * deriv G α))
        0 := by
    -- Apply the zero-based Jacobi formula to the translated path.
    simpa [H, deriv_comp_add_const] using
      hasDerivAt_logDetRatioPotential_raw_at_zero H hHpos hHdiff
  have hshifted :
      HasDerivAt
        (fun u ↦ logDetRatioPotential H (u + -α) + logDetRatioPotential G α)
        (-Matrix.trace ((G α)⁻¹ * deriv G α))
        α := by
    have htranslate :
        HasDerivAt
          (fun u ↦ logDetRatioPotential H (u + -α))
          (-Matrix.trace ((G α)⁻¹ * deriv G α))
          α := by
      -- Recenter the translated derivative from `0` back to the base point `α`.
      have hbaseAt :
          HasDerivAt
            (logDetRatioPotential H)
            (-Matrix.trace ((G α)⁻¹ * deriv G α))
            (((fun u : ℝ ↦ u + -α) α)) := by
        simpa using hbase
      simpa [Function.comp] using
        hbaseAt.comp α ((hasDerivAt_id α).add_const (-α))
    -- Adding the constant value `V(α)` preserves the derivative.
    simpa using htranslate.add_const (logDetRatioPotential G α)
  have hEq :
      logDetRatioPotential G =ᶠ[𝓝 α]
        fun u ↦ logDetRatioPotential H (u + -α) + logDetRatioPotential G α := by
    rcases hposα with ⟨ε, hεpos, hε⟩
    have hGα : (G α).PosDef := by
      have h0 : |(0 : ℝ)| < ε := by
        simpa using hεpos
      simpa using hε h0
    have hsmall : ∀ᶠ u in 𝓝 α, |u + -α| < ε := by
      filter_upwards [Metric.ball_mem_nhds α hεpos] with u hu
      simpa [Metric.mem_ball, Real.dist_eq, sub_eq_add_neg, abs_sub_comm] using hu
    filter_upwards [hsmall] with u hu
    have huPos : (G u).PosDef := by
      have hshiftPos : (G ((u + -α) + α)).PosDef := hε hu
      simpa [sub_eq_add_neg, add_assoc] using hshiftPos
    -- Route correction: the shifted ratio potential has a different numerator, so we compare it
    -- to the original potential only after isolating the constant `logDetRatioPotential G α`.
    calc
      logDetRatioPotential G u
          = Real.log (Matrix.det (G 0)) - Real.log (Matrix.det (G u)) := by
              rw [logDetRatioPotential, Real.log_div hG0.det_pos.ne' huPos.det_pos.ne']
      _ = (Real.log (Matrix.det (G α)) - Real.log (Matrix.det (G u))) +
            (Real.log (Matrix.det (G 0)) - Real.log (Matrix.det (G α))) := by
            ring
      _ = logDetRatioPotential H (u + -α) + logDetRatioPotential G α := by
            rw [logDetRatioPotential, logDetRatioPotential]
            have hHu : H (u + -α) = G u := by
              simp [H, add_assoc]
            rw [show H 0 = G α by simp [H], hHu]
            rw [Real.log_div hGα.det_pos.ne' huPos.det_pos.ne',
              Real.log_div hG0.det_pos.ne' hGα.det_pos.ne']
  -- Transfer the translated local identity back to the original source potential.
  exact hshifted.congr_of_eventuallyEq hEq

/-- Helper for Proposition 7.11: neighborhood `C²` control on `G` yields the local Jacobi
identity for the derivative of the determinant-ratio potential. -/
private theorem deriv_logDetRatioPotential_eventually_eq_neg_trace
    (G : ℝ → Mat)
    (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef)
    (hGtwice :
      ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε →
        DifferentiableAt ℝ G α ∧ DifferentiableAt ℝ (deriv G) α) :
    deriv (logDetRatioPotential G) =ᶠ[𝓝 0]
      fun α ↦ -Matrix.trace ((G α)⁻¹ * deriv G α) := by
  rcases hpos with ⟨εpos, hεpos_pos, hεpos⟩
  rcases hGtwice with ⟨εtwice, hεtwice_pos, hεtwice⟩
  let δ : ℝ := min (εpos / 2) εtwice
  have hδpos : 0 < δ := by
    refine lt_min ?_ hεtwice_pos
    linarith
  have hG0 : (G 0).PosDef :=
    posDef_at_zero_of_posDef_near_zero G ⟨εpos, hεpos_pos, hεpos⟩
  have hsmall : ∀ᶠ α in 𝓝 0, |α| < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with α hα
    simpa [δ, Metric.mem_ball, Real.dist_eq] using hα
  filter_upwards [hsmall] with α hα
  have hαposHalf : |α| < εpos / 2 := by
    exact lt_of_lt_of_le hα (min_le_left _ _)
  have hαtwice : |α| < εtwice := by
    exact lt_of_lt_of_le hα (min_le_right _ _)
  have hαdiff : DifferentiableAt ℝ G α :=
    (hεtwice hαtwice).1
  have hlocalPos :
      ∃ η > 0, ∀ ⦃β : ℝ⦄, |β| < η → (G (β + α)).PosDef := by
    refine ⟨εpos / 2, by linarith, ?_⟩
    intro β hβ
    have habs : |β + α| ≤ |β| + |α| := abs_add_le β α
    have hsum : |β + α| < εpos := by
      linarith
    exact hεpos hsum
  -- Apply the translated Jacobi formula pointwise on a common small neighborhood of `0`.
  exact (hasDerivAt_logDetRatioPotential_raw_at G hG0 hlocalPos hαdiff).deriv

/-- Helper for Proposition 7.11: once the first derivative of the determinant-ratio potential
agrees locally with the traced Jacobi integrand, the second derivative at `0` is the negative
Jacobi trace term. -/
private theorem iteratedDerivTwoLogDetRatioPotential_of_eventuallyEqDeriv
    (G : ℝ → Mat)
    (hEq :
      deriv (logDetRatioPotential G) =ᶠ[𝓝 0]
        fun α ↦ -Matrix.trace ((G α)⁻¹ * deriv G α))
    (htrace :
      HasDerivAt
        (fun α ↦ Matrix.trace ((G α)⁻¹ * deriv G α))
        (Matrix.trace
          ((G 0)⁻¹ * deriv (deriv G) 0 -
            (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0))
        0) :
    iteratedDeriv 2 (logDetRatioPotential G) 0 =
      -Matrix.trace
        ((G 0)⁻¹ * deriv (deriv G) 0 -
          (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) := by
  -- Rewrite the second iterated derivative as the derivative of the first one.
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  calc
    deriv (deriv (logDetRatioPotential G)) 0
        = deriv (fun α ↦ -Matrix.trace ((G α)⁻¹ * deriv G α)) 0 :=
          Filter.EventuallyEq.deriv_eq hEq
    _ = -Matrix.trace
          ((G 0)⁻¹ * deriv (deriv G) 0 -
            (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) := by
          -- The traced Jacobi integrand already has the required derivative at the base point.
          simpa using htrace.neg.deriv

/-- Helper for Proposition 7.11: the second derivative of the determinant-ratio potential is the
negative derivative of the traced Jacobi integrand. -/
private theorem iteratedDeriv_two_logDetRatioPotential_raw_at_zero
    (G : ℝ → Mat)
    (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef)
    (hGtwice :
      ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε →
        DifferentiableAt ℝ G α ∧ DifferentiableAt ℝ (deriv G) α) :
    iteratedDeriv 2 (logDetRatioPotential G) 0 =
      -Matrix.trace
        ((G 0)⁻¹ * deriv (deriv G) 0 -
          (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) := by
  have hEq :
      deriv (logDetRatioPotential G) =ᶠ[𝓝 0]
        fun α ↦ -Matrix.trace ((G α)⁻¹ * deriv G α) :=
    deriv_logDetRatioPotential_eventually_eq_neg_trace G hpos hGtwice
  have hG0 : (G 0).PosDef :=
    posDef_at_zero_of_posDef_near_zero G hpos
  rcases hGtwice with ⟨ε, hεpos, hε⟩
  have h0 : |(0 : ℝ)| < ε := by
    simpa using hεpos
  have hG₁ : DifferentiableAt ℝ G 0 :=
    (hε h0).1
  have hG₂ : DifferentiableAt ℝ (deriv G) 0 :=
    (hε h0).2
  -- Differentiate the local first-derivative identity once more at the base point.
  exact iteratedDerivTwoLogDetRatioPotential_of_eventuallyEqDeriv G hEq
    (hasDerivAt_trace_inverse_mul_deriv_at_zero G hG0 hG₁ hG₂)

section

variable (G : ℝ → Mat) (τ : Fin n → ℝ)
variable (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef)
variable
  (hGtwice :
    ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε →
      DifferentiableAt ℝ G α ∧ DifferentiableAt ℝ (deriv G) α)
variable (htrace₁ : Matrix.trace ((G 0)⁻¹ * deriv G 0) = ∑ i : Fin n, (τ i - 1))
variable
  (htrace₂ :
    Matrix.trace
        ((G 0)⁻¹ * deriv (deriv G) 0 - (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) =
      -∑ i : Fin n, (τ i - 1) ^ (2 : ℕ))

-- Proof sketch: differentiate `V(α) = log (det G(0) / det G(α))` using Jacobi's formula for
-- `det`, the derivative of matrix inversion, and the cyclicity of the trace; then substitute the
-- two assumed trace identities at `α = 0`.
/-- Proposition 7.11 (1): if a matrix path `G` is twice differentiable on a neighborhood of `0`,
stays positive definite near `0`, and its first and second trace identities are encoded by the
parameters `τ₁, …, τₙ`, then the determinant-ratio potential
`V(α) = log (det G(0) / det G(α))` satisfies the stated formula for `V'(0)`. -/
theorem logDetRatioPotential_deriv_at_zero
    (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef)
    (hGtwice :
      ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε →
        DifferentiableAt ℝ G α ∧ DifferentiableAt ℝ (deriv G) α)
    (htrace₁ : Matrix.trace ((G 0)⁻¹ * deriv G 0) = ∑ i : Fin n, (τ i - 1))
    (htrace₂ :
      Matrix.trace
          ((G 0)⁻¹ * deriv (deriv G) 0 - (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) =
        -∑ i : Fin n, (τ i - 1) ^ (2 : ℕ))
    :
    deriv (logDetRatioPotential G) 0 = (n : ℝ) - ∑ i : Fin n, τ i := by
  rcases hGtwice with ⟨ε, hεpos, hε⟩
  have h0 : |(0 : ℝ)| < ε := by
    simpa using hεpos
  have hG₁ : DifferentiableAt ℝ G 0 :=
    (hε h0).1
  have hraw :
      deriv (logDetRatioPotential G) 0 =
        -Matrix.trace ((G 0)⁻¹ * deriv G 0) := by
    -- Extract the first derivative from the raw Jacobi formula at the base point.
    exact (hasDerivAt_logDetRatioPotential_raw_at_zero G hpos hG₁).deriv
  -- Substitute the given trace identity into the raw derivative formula.
  calc
    deriv (logDetRatioPotential G) 0
        = -Matrix.trace ((G 0)⁻¹ * deriv G 0) := hraw
    _ = (n : ℝ) - ∑ i : Fin n, τ i :=
          neg_trace_first_identity_eq_dimension_sub_sum G τ htrace₁

/-- Proposition 7.11 (2): under the same neighborhood positivity, `C²`, and trace hypotheses,
the determinant-ratio potential
`V(α) = log (det G(0) / det G(α))` satisfies the stated formula for `V''(0)`. -/
theorem logDetRatioPotential_iteratedDeriv_two_at_zero
    (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef)
    (hGtwice :
      ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε →
        DifferentiableAt ℝ G α ∧ DifferentiableAt ℝ (deriv G) α)
    (htrace₁ : Matrix.trace ((G 0)⁻¹ * deriv G 0) = ∑ i : Fin n, (τ i - 1))
    (htrace₂ :
      Matrix.trace
          ((G 0)⁻¹ * deriv (deriv G) 0 - (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) =
        -∑ i : Fin n, (τ i - 1) ^ (2 : ℕ))
    :
    iteratedDeriv 2 (logDetRatioPotential G) 0 =
      ∑ i : Fin n, (τ i - 1) ^ (2 : ℕ) := by
  have hraw :
      iteratedDeriv 2 (logDetRatioPotential G) 0 =
        -Matrix.trace
          ((G 0)⁻¹ * deriv (deriv G) 0 -
            (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) :=
    iteratedDeriv_two_logDetRatioPotential_raw_at_zero G hpos hGtwice
  -- Substitute the second trace identity into the raw second-derivative formula.
  calc
    iteratedDeriv 2 (logDetRatioPotential G) 0
        = -Matrix.trace
            ((G 0)⁻¹ * deriv (deriv G) 0 -
              (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) := hraw
    _ = ∑ i : Fin n, (τ i - 1) ^ (2 : ℕ) :=
          neg_trace_second_identity_eq_sum_sq G τ htrace₂

-- Proof sketch: apply `logDetRatioPotential_deriv_at_zero` to obtain the first derivative
-- identity, then rewrite the sum `∑ i, τ i` using the given identification with
-- `(\|g\|_D^*)^2`.
/-- If the sum of the parameters `τ₁, …, τₙ` is identified with `(\|g\|_D^*)^2`, then the first
derivative of the determinant-ratio potential is `n - (\|g\|_D^*)^2`. -/
theorem logDetRatioPotential_deriv_at_zero_of_dualNormSq
    (hpos : ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε → (G α).PosDef)
    (hGtwice :
      ∃ ε > 0, ∀ ⦃α : ℝ⦄, |α| < ε →
        DifferentiableAt ℝ G α ∧ DifferentiableAt ℝ (deriv G) α)
    (htrace₁ : Matrix.trace ((G 0)⁻¹ * deriv G 0) = ∑ i : Fin n, (τ i - 1))
    (htrace₂ :
      Matrix.trace
          ((G 0)⁻¹ * deriv (deriv G) 0 - (G 0)⁻¹ * deriv G 0 * (G 0)⁻¹ * deriv G 0) =
        -∑ i : Fin n, (τ i - 1) ^ (2 : ℕ))
    (dualNormSq : ℝ) (hdualNormSq : dualNormSq = ∑ i : Fin n, τ i) :
    deriv (logDetRatioPotential G) 0 = (n : ℝ) - dualNormSq := by
  -- The dual-norm rewrite only depends on the first component of Proposition 7.11.
  simpa [hdualNormSq] using
    logDetRatioPotential_deriv_at_zero G τ hpos hGtwice htrace₁ htrace₂

end

end

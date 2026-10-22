/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.MeanValue
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_48
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_36
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open RealSymmetricMatrixSpace
open scoped Gradient Matrix.Norms.L2Operator RealSymmetricMatrixSpace StandardSimplex

universe u

section

variable {E : Type u} [NormedAddCommGroup E]
variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Proposition 6.38: use the operator norm on ambient matrices when building the
canonical normed-group structure on `𝕊^n`. -/
local instance proposition638AmbientMatrixNormedAddCommGroup : NormedAddCommGroup Mat :=
  Matrix.instL2OpNormedAddCommGroup

/-- Helper for Proposition 6.38: scalar multiplication on ambient matrices is measured with the
same operator norm used in Proposition 6.35. -/
local instance proposition638AmbientMatrixNormedSpace : NormedSpace ℝ Mat :=
  Matrix.instL2OpNormedSpace

/-- Helper for Proposition 6.38: use the canonical submodule normed-group structure on `𝕊^n`
so the operator-norm Fréchet-calculus API stays on one carrier spelling. -/
local instance canonicalSymmetricMatrixNormedAddCommGroup : NormedAddCommGroup (𝕊^n) := by
  letI : NormedAddCommGroup Mat := proposition638AmbientMatrixNormedAddCommGroup
  exact Submodule.normedAddCommGroup (𝕊^n)

/-- Helper for Proposition 6.38: use the canonical submodule normed-space structure on `𝕊^n`
for the operator-norm calculus imported from Proposition 6.35. -/
local instance canonicalSymmetricMatrixNormedSpace : NormedSpace ℝ (𝕊^n) := by
  letI : NormedAddCommGroup Mat := proposition638AmbientMatrixNormedAddCommGroup
  letI : NormedSpace ℝ Mat := proposition638AmbientMatrixNormedSpace
  exact Submodule.normedSpace (𝕊^n)

/-- The affine pullback `φ_μ(y) = f_μ(C + A y)` from Proposition 6.38. -/
abbrev affinePullbackObjective
    [NormedSpace ℝ E]
    (fμ : 𝕊^n → ℝ) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) : E → ℝ :=
  fun y ↦ fμ (C + A y)

@[simp] theorem affinePullbackObjective_apply
    [NormedSpace ℝ E]
    (fμ : 𝕊^n → ℝ) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) (y : E) :
    affinePullbackObjective fμ C A y = fμ (C + A y) :=
  rfl

-- LeanSearch/local recall: the canonical operator-norm owner for `A : E →L[ℝ] 𝕊^n` is `‖A‖`,
-- with the source-facing unit-sphere bridge already recorded in Definition 6.49.

/-- Helper for Proposition 6.38: affine lines in normed spaces differentiate to their direction
vector. -/
private theorem affineLineHasDerivAt_generic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x h : F} (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • h) h t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const h).const_add x

/-- Helper for Proposition 6.38: affine lines have vanishing second iterated derivative in every
normed space. -/
private theorem affineLineIteratedDerivTwo_generic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x h : F} :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ (0 : F) := by
  -- Differentiate the affine line once to a constant, then differentiate that constant again.
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s • h) = fun _ : ℝ ↦ h := by
    funext s
    have hs : HasDerivAt (fun t : ℝ ↦ x + t • h) h s := affineLineHasDerivAt_generic s
    exact hs.deriv
  rw [hderiv, deriv_const]

/-- Helper for Proposition 6.38: the repeated second Fréchet derivative on a repeated direction
agrees with the Chapter 5 second directional derivative. -/
private theorem iteratedFDerivTwo_apply_eq_secondDirectionalDerivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {x h : F} (hcont : ContDiffAt ℝ 2 f x) :
    iteratedFDeriv ℝ 2 f x ![h, h] = secondDirectionalDerivative f x h := by
  let line : ℝ → F := fun t ↦ x + t • h
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  have hcomp :
      iteratedDeriv 2 (f ∘ line) 0 =
        (iteratedFDeriv ℝ 2 f (line 0)) (fun _ ↦ deriv line 0) +
          (fderiv ℝ f (line 0)) (iteratedDeriv 2 line 0) := by
    simpa [line] using (iteratedDeriv_vcomp_two (by simpa [line] using hcont) hline₂)
  have hline_deriv : deriv line 0 = h := by
    have hzero : HasDerivAt (fun t : ℝ ↦ x + t • h) h 0 := affineLineHasDerivAt_generic 0
    simpa [line] using hzero.deriv
  -- The quadratic chain rule collapses because the affine line has zero second derivative.
  rw [secondDirectionalDerivative]
  symm
  calc
    iteratedDeriv 2 (directionalSlice f x h) 0 = iteratedDeriv 2 (f ∘ line) 0 := by
      rfl
    _ =
        (iteratedFDeriv ℝ 2 f (line 0)) (fun _ ↦ deriv line 0) +
          (fderiv ℝ f (line 0)) (iteratedDeriv 2 line 0) := hcomp
    _ = iteratedFDeriv ℝ 2 f x ![h, h] := by
      rw [affineLineIteratedDerivTwo_generic]
      simp [line, hline_deriv, iteratedFDeriv_two_apply]

/-- Helper for Proposition 6.38: at a `C²` point, the repeated second Fréchet derivative on a
repeated direction agrees with the Hessian quadratic form. -/
private theorem iteratedFDerivTwo_apply_eq_hessianQuadraticForm
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} {x h : F} (hcont : ContDiffAt ℝ 2 f x) :
    iteratedFDeriv ℝ 2 f x ![h, h] = inner ℝ h (hessian f x h) := by
  -- Collapse the repeated Fréchet derivative to the directional owner, then invoke the Chapter 5
  -- Hessian bridge on the same `C²` point.
  calc
    iteratedFDeriv ℝ 2 f x ![h, h] = secondDirectionalDerivative f x h := by
      exact iteratedFDerivTwo_apply_eq_secondDirectionalDerivative hcont
    _ = inner ℝ h (hessian f x h) := by
      exact secondDirectionalDerivative_eq_hessian_quadratic_form hcont

/-- Helper for Proposition 6.38: the affine pullback `y ↦ f(C + A y)` has the same second
directional derivative as the owner `f` evaluated at the transported base point and direction. -/
private theorem directionalSlice_affinePullback
    [NormedSpace ℝ E]
    (f : 𝕊^n → ℝ) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) (y h : E) :
    directionalSlice (affinePullbackObjective f C A) y h =
      directionalSlice f (C + A y) (A h) := by
  funext t
  -- Expand the scalar slice and distribute the affine map once so both sides become syntactically
  -- identical before differentiating.
  simp [directionalSlice, affinePullbackObjective, map_add, map_smul, add_assoc]

/-- Helper for Proposition 6.38: the affine pullback `y ↦ f(C + A y)` has the same second
directional derivative as the owner `f` evaluated at the transported base point and direction. -/
private theorem secondDirectionalDerivative_affinePullback
    [NormedSpace ℝ E]
    (f : 𝕊^n → ℝ) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) (y h : E) :
    secondDirectionalDerivative (affinePullbackObjective f C A) y h =
      secondDirectionalDerivative f (C + A y) (A h) := by
  -- After freezing the scalar directional slice in raw affine coordinates, the derivative owner
  -- sees exactly the same one-variable function on both sides.
  simp [secondDirectionalDerivative, directionalSlice_affinePullback]

/-- Helper for Proposition 6.38: a self-adjoint operator whose quadratic form is bounded above in
absolute value by `s ‖u‖²` has operator norm at most `s`. -/
private theorem selfAdjoint_norm_le_of_quadratic_bound
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    {T : E →L[ℝ] E} {s : ℝ}
    (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hs : 0 ≤ s)
    (hquad : ∀ u : E, |inner ℝ (T u) u| ≤ s * ‖u‖ ^ (2 : ℕ)) :
    ‖T‖ ≤ s := by
  have hbound : ∀ u : E, |T.rayleighQuotient u| ≤ s := by
    intro u
    by_cases hu : u = 0
    · simpa [hu] using hs
    · have hu_pos : 0 < ‖u‖ ^ (2 : ℕ) := by
        positivity
      rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, abs_div,
        abs_of_nonneg (by positivity : 0 ≤ ‖u‖ ^ (2 : ℕ))]
      exact (div_le_iff₀ hu_pos).2 (by simpa using hquad u)
  -- The Rayleigh-quotient characterization turns the diagonal bound into an operator bound.
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT]
  exact ciSup_le hbound

/-- Helper for Proposition 6.38: the exact continuous affine owner of the raw shift
`y ↦ C + A y`. -/
private def affineShiftMap
    [NormedSpace ℝ E]
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) : E →ᴬ[ℝ] 𝕊^n :=
  A.toContinuousAffineMap +ᵥ ContinuousAffineMap.const ℝ E C

/-- Helper for Proposition 6.38: coercing the bundled affine shift back to a function recovers
the raw affine lambda `y ↦ C + A y`. -/
private theorem affineShiftMap_coe_eq_raw
    [NormedSpace ℝ E]
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    ((affineShiftMap C A : E →ᴬ[ℝ] 𝕊^n) : E → 𝕊^n) = fun y : E ↦ C + A y := by
  funext y
  simp [affineShiftMap, add_comm]

/-- Helper for Proposition 6.38: the identity continuous linear map on `𝕊^n`, bundled using the
local symmetric-matrix normed-space structure. -/
private def symmetricIdentityMap : 𝕊^n →L[ℝ] 𝕊^n :=
  { toLinearMap := LinearMap.id
    cont := (LinearMap.id : 𝕊^n →ₗ[ℝ] 𝕊^n).continuous_of_finiteDimensional }

/-- Helper for Proposition 6.38: `symmetricIdentityMap` acts as the identity on `𝕊^n`. -/
@[simp] private theorem symmetricIdentityMap_apply
    (X : 𝕊^n) :
    symmetricIdentityMap X = X :=
  rfl

/-- Helper for Proposition 6.38: the fixed affine shift `y ↦ C + A y` is `C²` at every point on
the exact raw lambda surface used by the pullback objective. -/
private theorem affineShift_contDiffAt_two
    [NormedSpace ℝ E]
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) (y : E) :
    ContDiffAt ℝ 2 (fun z : E ↦ C + A z) y := by
  -- Route correction: the affine shift already lives on the exact raw surface
  -- `fun z ↦ C + A z`, so it is just a constant translate of the continuous linear owner `A`.
  simpa [add_comm] using
    (contDiffAt_const.add A.contDiff.contDiffAt : ContDiffAt ℝ 2 (fun z : E ↦ C + A z) y)

/-- Helper for Proposition 6.38: the fixed affine shift `y ↦ C + A y` is globally `C²` on the
exact raw lambda surface used by the pullback objective. -/
private theorem affineShift_contDiff_two
    [NormedSpace ℝ E]
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    ContDiff ℝ 2 (fun z : E ↦ C + A z) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact affineShift_contDiffAt_two C A y

/-- Helper for Proposition 6.38: the assumed owner-side Hessian bound implies the pointwise
Hessian quadratic-form bound for the affine pullback. -/
private theorem affinePullbackObjective_hessianQuadraticForm_le
    [NormedSpace ℝ E]
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n)
    (y h : E)
    (hyC2 : ContDiffAt ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^n → ℝ) (C + A y))
    (hyHess :
      iteratedFDeriv ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^n → ℝ) (C + A y) ![A h, A h] ≤
        (1 / (μ : ℝ)) * ‖(((A h : 𝕊^n) : Mat))‖ ^ (2 : ℕ)) :
      iteratedFDeriv ℝ 2 (smoothedSemidefiniteObjective n μ C A) y ![h, h] ≤
      ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
  have hyPullbackC2 : ContDiffAt ℝ 2 (smoothedSemidefiniteObjective n μ C A) y := by
    -- Compose the owner-side `C²` hypothesis with the raw affine shift used by the pullback, so
    -- the directional-derivative transport stays on a single surface.
    simpa [smoothedSemidefiniteObjective, affinePullbackObjective] using
      (hyC2.comp y (affineShift_contDiffAt_two C A y))
  have hpullEq :
      iteratedFDeriv ℝ 2 (smoothedSemidefiniteObjective n μ C A) y ![h, h] =
        secondDirectionalDerivative (smoothedSemidefiniteObjective n μ C A) y h :=
    iteratedFDerivTwo_apply_eq_secondDirectionalDerivative hyPullbackC2
  have hownerEq :
      iteratedFDeriv ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^n → ℝ) (C + A y) ![A h, A h] =
        secondDirectionalDerivative (logSumExpMaxEigenvalueSmoothing μ : 𝕊^n → ℝ) (C + A y) (A h) :=
    iteratedFDerivTwo_apply_eq_secondDirectionalDerivative hyC2
  have htransport :
      secondDirectionalDerivative (smoothedSemidefiniteObjective n μ C A) y h =
        secondDirectionalDerivative
            (logSumExpMaxEigenvalueSmoothing μ : 𝕊^n → ℝ) (C + A y) (A h) := by
    simpa [smoothedSemidefiniteObjective, affinePullbackObjective] using
      secondDirectionalDerivative_affinePullback
        (logSumExpMaxEigenvalueSmoothing μ : 𝕊^n → ℝ) C A y h
  have hAh_le : ‖(((A h : 𝕊^n) : Mat))‖ ≤ ‖A‖ * ‖h‖ := by
    simpa using A.le_opNorm h
  have hAh_sq :
      ‖(((A h : 𝕊^n) : Mat))‖ ^ (2 : ℕ) ≤ (‖A‖ * ‖h‖) ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ (norm_nonneg _) hAh_le 2
  have hμ_nonneg : 0 ≤ 1 / (μ : ℝ) := one_div_nonneg.mpr μ.property.le
  calc
    iteratedFDeriv ℝ 2 (smoothedSemidefiniteObjective n μ C A) y ![h, h]
        = secondDirectionalDerivative (smoothedSemidefiniteObjective n μ C A) y h := hpullEq
    _ = secondDirectionalDerivative (logSumExpMaxEigenvalueSmoothing μ : 𝕊^n → ℝ) (C + A y) (A h) :=
          htransport
    _ = iteratedFDeriv ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^n → ℝ) (C + A y) ![A h, A h] := by
          symm
          exact hownerEq
    _ ≤ (1 / (μ : ℝ)) * ‖(((A h : 𝕊^n) : Mat))‖ ^ (2 : ℕ) := hyHess
    _ ≤ (1 / (μ : ℝ)) * (‖A‖ * ‖h‖) ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hAh_sq hμ_nonneg
    _ = ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
          rw [mul_pow]
          ring

/-- Helper for Proposition 6.38: the positive-parameter spectral smoothing is the `μ`-scaled
entropy smoothing evaluated at the rescaled matrix. -/
private theorem logSumExpMaxEigenvalueSmoothing_eq_scaledEntropySmoothing
    (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    logSumExpMaxEigenvalueSmoothing μ X =
      (μ : ℝ) * entropySmoothing (((μ : ℝ)⁻¹) • X) := by
  -- Compare both sides through the same trace-exponential normal form from Propositions 6.35
  -- and 6.36, so the scaling transport is discharged once at the owner level.
  rw [logSumExpMaxEigenvalueSmoothing_eq_matrixExponentialTrace,
    entropySmoothing_eq_log_trace_exp]
  simp

/-- Helper for Proposition 6.38: rewrite the positive-parameter smoothing owner as the scalar
multiple of entropy smoothing composed with the fixed rescaling `X ↦ μ⁻¹ • X`. -/
private theorem logSumExpMaxEigenvalueSmoothing_eq_scaledEntropySmoothing_fun
    (m : ℕ) (μ : {μ : ℝ // 0 < μ}) :
    (logSumExpMaxEigenvalueSmoothing μ : 𝕊^m → ℝ) =
      (μ : ℝ) • (fun X : 𝕊^m ↦ entropySmoothing (((μ : ℝ)⁻¹) • X)) := by
  funext X
  -- Package the pointwise scaled-entropy rewrite as a function equality for the calculus steps
  -- below.
  simpa [Pi.smul_apply, smul_eq_mul] using
    (logSumExpMaxEigenvalueSmoothing_eq_scaledEntropySmoothing (n := m) μ X)

/-- Helper for Proposition 6.38: the bundled linear owner of the fixed rescaling
`X ↦ ((μ : ℝ)⁻¹) • X` on `𝕊^m`. -/
private def symmetricScaleMap
    (m : ℕ) (μ : {μ : ℝ // 0 < μ}) : 𝕊^m →L[ℝ] 𝕊^m :=
  ((μ : ℝ)⁻¹) • ContinuousLinearMap.id ℝ (𝕊^m)

/-- Helper for Proposition 6.38: coercing `symmetricScaleMap` back to a function recovers the raw
rescaling `X ↦ ((μ : ℝ)⁻¹) • X`. -/
@[simp] private theorem symmetricScaleMap_apply
    (m : ℕ) (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^m) :
    symmetricScaleMap m μ X = ((μ : ℝ)⁻¹) • X := by
  -- Evaluate the bundled scaling owner once and reduce to the identity map on `𝕊^m`.
  simp [symmetricScaleMap]

/-- Helper for Proposition 6.38: Proposition 6.35 restated on the local `𝕊^m` instance spelling
used in this file. -/
private theorem carrierNormalizedEntropySmoothing_contDiff_and_hessianQuadraticForm_le
    (m : ℕ) :
    ContDiff ℝ 2 (entropySmoothing : 𝕊^m → ℝ) ∧
      ∀ X H : 𝕊^m,
        iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^m → ℝ) X ![H, H] ≤
          ‖((H : Matrix (Fin m) (Fin m) ℝ))‖ ^ (2 : ℕ) := by
  -- Route correction: Proposition 6.35 already has the exact local `𝕊^m` carrier spelling used
  -- in this file, so this bridge is just a direct restatement.
  simpa using entropySmoothing_contDiff_and_hessianQuadraticForm_le m

/-- Helper for Proposition 6.38: composing entropy smoothing with the fixed rescaling
`X ↦ μ⁻¹ • X` preserves `C²` regularity. -/
private theorem entropySmoothing_invScale_contDiff_two
    (m : ℕ) (μ : {μ : ℝ // 0 < μ}) :
    ContDiff ℝ 2 (fun X : 𝕊^m ↦ entropySmoothing (((μ : ℝ)⁻¹) • X)) := by
  have hEntropy :
      ContDiff ℝ 2 (entropySmoothing : 𝕊^m → ℝ) :=
    (carrierNormalizedEntropySmoothing_contDiff_and_hessianQuadraticForm_le m).1
  have hScale : ContDiff ℝ 2 (fun X : 𝕊^m ↦ ((μ : ℝ)⁻¹) • X) := by
    let scaleMap : 𝕊^m →L[ℝ] 𝕊^m :=
      ((μ : ℝ)⁻¹) • ContinuousLinearMap.id ℝ (𝕊^m)
    -- The rescaling owner is linear, hence smooth.
    simpa [scaleMap] using scaleMap.contDiff
  -- Compose the owner-side `C²` regularity with the fixed linear rescaling map
  -- `X ↦ ((μ : ℝ)⁻¹) • X`.
  simpa using hEntropy.comp hScale

/-- Helper for Proposition 6.38: a `C²` scalar field on a real Hilbert space has differentiable
gradient at the same point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} {x : F} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  let D : StrongDual ℝ F →L[ℝ] F :=
    (InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    -- The Fréchet derivative is `C¹` at a `C²` point.
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the inverse Riesz map and differentiate that composition.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Proposition 6.38: the positive-parameter smoothing owner is globally `C²`. -/
private theorem logSumExpMaxEigenvalueSmoothing_contDiff_two
    (m : ℕ) (μ : {μ : ℝ // 0 < μ}) :
    ContDiff ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^m → ℝ) := by
  have hScaledCont := entropySmoothing_invScale_contDiff_two m μ
  -- Restore the source-facing owner after proving regularity on the rescaled entropy surface.
  rw [logSumExpMaxEigenvalueSmoothing_eq_scaledEntropySmoothing_fun m μ]
  simpa [smul_eq_mul] using hScaledCont.const_smul (μ : ℝ)

/-- Helper for Proposition 6.38: Proposition 6.35 transfers the Hessian quadratic-form bound to
the positive-parameter smoothing owner. -/
private theorem logSumExpMaxEigenvalueSmoothing_hessianQuadraticForm_le
    (m : ℕ) (μ : {μ : ℝ // 0 < μ}) (X H : 𝕊^m) :
    iteratedFDeriv ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^m → ℝ) X ![H, H] ≤
      (1 / (μ : ℝ)) * ‖((H : Matrix (Fin m) (Fin m) ℝ))‖ ^ (2 : ℕ) := by
  let a : ℝ := (μ : ℝ)⁻¹
  have hEntropy := carrierNormalizedEntropySmoothing_contDiff_and_hessianQuadraticForm_le m
  have hScaledCont :
      ContDiffAt ℝ 2 (fun Y : 𝕊^m ↦ entropySmoothing (a • Y)) X := by
    simpa [a] using (entropySmoothing_invScale_contDiff_two m μ).contDiffAt (x := X)
  have hrewrite :
      iteratedFDeriv ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^m → ℝ) X ![H, H] =
        (μ : ℝ) * iteratedFDeriv ℝ 2 (fun Y : 𝕊^m ↦ entropySmoothing (a • Y)) X ![H, H] := by
    rw [logSumExpMaxEigenvalueSmoothing_eq_scaledEntropySmoothing_fun m μ]
    -- Pull the outer scalar through the second Fréchet derivative before estimating the rescaled
    -- entropy smoothing term.
    have hsmul :
        iteratedFDeriv ℝ 2 ((μ : ℝ) • (fun Y : 𝕊^m ↦ entropySmoothing (a • Y))) X =
          (μ : ℝ) • iteratedFDeriv ℝ 2 (fun Y : 𝕊^m ↦ entropySmoothing (a • Y)) X :=
      iteratedFDeriv_const_smul_apply' (a := (μ : ℝ)) (i := 2)
        (f := fun Y : 𝕊^m ↦ entropySmoothing (a • Y)) hScaledCont
    simpa [Pi.smul_apply, smul_eq_mul] using congrArg (fun T ↦ T ![H, H]) hsmul
  have hcomp :
      iteratedFDeriv ℝ 2 (fun Y : 𝕊^m ↦ entropySmoothing (a • Y)) X ![H, H] =
        a ^ (2 : ℕ) *
          iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^m → ℝ) (a • X) ![H, H] := by
    -- The fixed rescaling contributes the expected factor `a²` to the second derivative.
    have hcompFun :=
      iteratedFDeriv_comp_const_smul a (i := 2) (f := (entropySmoothing : 𝕊^m → ℝ)) hEntropy.1
    simpa [Pi.smul_apply, smul_eq_mul] using
      congrArg (fun g ↦ g X ![H, H]) hcompFun
  have ha_nonneg : 0 ≤ a ^ (2 : ℕ) := by
    positivity
  have hscaledBound :
      iteratedFDeriv ℝ 2 (fun Y : 𝕊^m ↦ entropySmoothing (a • Y)) X ![H, H] ≤
        a ^ (2 : ℕ) * ‖((H : Matrix (Fin m) (Fin m) ℝ))‖ ^ (2 : ℕ) := by
    -- Apply Proposition 6.35 at the rescaled base point, then multiply by the nonnegative factor
    -- coming from the fixed linear change of variables.
    calc
      iteratedFDeriv ℝ 2 (fun Y : 𝕊^m ↦ entropySmoothing (a • Y)) X ![H, H]
          = a ^ (2 : ℕ) *
              iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^m → ℝ) (a • X) ![H, H] := hcomp
      _ ≤ a ^ (2 : ℕ) * ‖((H : Matrix (Fin m) (Fin m) ℝ))‖ ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left (hEntropy.2 (a • X) H) ha_nonneg
  have hμ_nonneg : 0 ≤ (μ : ℝ) := μ.property.le
  have hμ_ne : (μ : ℝ) ≠ 0 := μ.property.ne'
  have hscalar :
      (μ : ℝ) * (a ^ (2 : ℕ) * ‖((H : Matrix (Fin m) (Fin m) ℝ))‖ ^ (2 : ℕ)) =
        (1 / (μ : ℝ)) * ‖((H : Matrix (Fin m) (Fin m) ℝ))‖ ^ (2 : ℕ) := by
    -- Simplify the scalar transport `μ * (μ⁻¹)^2` to `1 / μ` once, outside the main inequality.
    dsimp [a]
    rw [pow_two]
    field_simp [hμ_ne]
  calc
    iteratedFDeriv ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^m → ℝ) X ![H, H]
        = (μ : ℝ) * iteratedFDeriv ℝ 2 (fun Y : 𝕊^m ↦ entropySmoothing (a • Y)) X ![H, H] :=
          hrewrite
    _ ≤ (μ : ℝ) * (a ^ (2 : ℕ) * ‖((H : Matrix (Fin m) (Fin m) ℝ))‖ ^ (2 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hscaledBound hμ_nonneg
    _ = (1 / (μ : ℝ)) * ‖((H : Matrix (Fin m) (Fin m) ℝ))‖ ^ (2 : ℕ) := hscalar

/-- Helper for Proposition 6.38: Proposition 6.35 transfers to the scaled smoothing owner,
yielding global `C²` regularity and the source upper Hessian quadratic-form bound. -/
private theorem logSumExpMaxEigenvalueSmoothing_contDiff_and_hessianQuadraticForm_le
    (m : ℕ)
    (μ : {μ : ℝ // 0 < μ}) :
    ContDiff ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^m → ℝ) ∧
      ∀ X H : 𝕊^m,
        iteratedFDeriv ℝ 2 (logSumExpMaxEigenvalueSmoothing μ : 𝕊^m → ℝ) X ![H, H] ≤
          (1 / (μ : ℝ)) * ‖((H : Matrix (Fin m) (Fin m) ℝ))‖ ^ (2 : ℕ) := by
  constructor
  · exact logSumExpMaxEigenvalueSmoothing_contDiff_two m μ
  · intro X H
    exact logSumExpMaxEigenvalueSmoothing_hessianQuadraticForm_le m μ X H

/-- Helper for Proposition 6.38: the vector log-sum-exp owner `η` is convex on the whole
Euclidean space. -/
private theorem eta_convexOn
    {n : ℕ} [NeZero n] (μ : {μ : ℝ // 0 < μ}) :
    ConvexOn ℝ Set.univ (η μ : EuclideanSpace ℝ (Fin n) → ℝ) := by
  let f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i u ↦ u i / (μ : ℝ)
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin n)), ConvexOn ℝ Set.univ (f i) := by
    intro i hi
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    -- Each coordinate map divided by `μ` is affine, hence convex.
    have hEq : f i (a • x + b • y) = a * f i x + b * f i y := by
      simp [f, div_eq_mul_inv, add_mul]
      ring
    simpa [mul_comm, mul_left_comm, mul_assoc] using le_of_eq hEq
  have hlog :
      ConvexOn ℝ Set.univ (fun u : EuclideanSpace ℝ (Fin n) ↦
        Real.log (∑ i : Fin n, Real.exp (f i u))) := by
    simpa using convexOn_log_sum_exp_of_convexOn Set.univ Finset.univ_nonempty hf
  -- `η μ` is the positive scalar multiple `μ • logSumExp`.
  simpa [η, f, smul_eq_mul] using hlog.smul μ.property.le

/-- Helper for Proposition 6.38: permuting the coordinates does not change the vector log-sum-exp
owner `η`. -/
private theorem eta_permInvariant
    {n : ℕ} [NeZero n] (μ : {μ : ℝ // 0 < μ})
    (u : EuclideanSpace ℝ (Fin n)) (σ : Equiv.Perm (Fin n)) :
    η μ (WithLp.toLp 2 (fun i : Fin n ↦ u (σ i))) = η μ u := by
  -- Reindex the finite exponential sum along the permutation `σ`.
  rw [eta_apply, eta_apply]
  congr 2
  simpa using
    (Equiv.sum_comp σ (fun i : Fin n ↦ Real.exp (u i / (μ : ℝ))))

/-- Helper for Proposition 6.38: applying a doubly stochastic matrix to the score vector can only
decrease the vector log-sum-exp owner `η`. -/
private theorem eta_mulVec_le_of_doublyStochastic
    {n : ℕ} [NeZero n] (μ : {μ : ℝ // 0 < μ})
    {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W ∈ doublyStochastic ℝ (Fin n))
    (s : Fin n → ℝ) :
    η μ (WithLp.toLp 2 (W.mulVec s)) ≤ η μ (WithLp.toLp 2 s) := by
  obtain ⟨w, hw_nonneg, hw_sum, hwWsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hW
  let permVec : Equiv.Perm (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun σ ↦ WithLp.toLp 2 (fun i : Fin n ↦ s (σ i))
  have hmulVec :
      W.mulVec s = ∑ σ : Equiv.Perm (Fin n), w σ • (s ∘ σ) := by
    -- Expand the Birkhoff decomposition of `W` and simplify the permutation-matrix action.
    calc
      W.mulVec s = (∑ σ : Equiv.Perm (Fin n), w σ • (σ.permMatrix ℝ)).mulVec s := by
        rw [hwWsum]
      _ = ∑ σ : Equiv.Perm (Fin n), (w σ • (σ.permMatrix ℝ)).mulVec s := by
            simpa using
              (Matrix.sum_mulVec
                Finset.univ
                (fun σ : Equiv.Perm (Fin n) ↦ w σ • (σ.permMatrix ℝ)) s)
      _ = ∑ σ : Equiv.Perm (Fin n), w σ • ((σ.permMatrix ℝ).mulVec s) := by
            refine Finset.sum_congr rfl ?_
            intro σ hσ
            rw [Matrix.smul_mulVec]
      _ = ∑ σ : Equiv.Perm (Fin n), w σ • (s ∘ σ) := by
            refine Finset.sum_congr rfl ?_
            intro σ hσ
            rw [Matrix.permMatrix_mulVec]
  have havg :
      WithLp.toLp 2 (W.mulVec s) = ∑ σ : Equiv.Perm (Fin n), w σ • permVec σ := by
    -- Read the Birkhoff average on the exact `EuclideanSpace` surface used by `η`.
    ext i
    simp [permVec, hmulVec, Pi.smul_apply]
  have hconv_le :
      η μ (∑ σ : Equiv.Perm (Fin n), w σ • permVec σ) ≤
        ∑ σ : Equiv.Perm (Fin n), w σ • η μ (permVec σ) := by
    -- Jensen's inequality applies because `η μ` is convex on the whole space.
    exact
      (eta_convexOn μ).map_sum_le
        (fun σ hσ ↦ hw_nonneg σ) hw_sum (fun σ hσ ↦ by simp)
  calc
    η μ (WithLp.toLp 2 (W.mulVec s)) = η μ (∑ σ : Equiv.Perm (Fin n), w σ • permVec σ) := by
      rw [havg]
    _ ≤ ∑ σ : Equiv.Perm (Fin n), w σ • η μ (permVec σ) := hconv_le
    _ = ∑ σ : Equiv.Perm (Fin n), w σ * η μ (WithLp.toLp 2 s) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          simpa [smul_eq_mul, permVec] using
            congrArg (fun r : ℝ ↦ w σ * r)
              (eta_permInvariant μ (WithLp.toLp 2 s) σ)
    _ = (∑ σ : Equiv.Perm (Fin n), w σ) * η μ (WithLp.toLp 2 s) := by
          rw [Finset.sum_mul]
    _ = η μ (WithLp.toLp 2 s) := by
          rw [hw_sum, one_mul]

/-- Helper for Proposition 6.38: transposing a doubly stochastic matrix preserves the doubly
stochastic constraints. -/
private theorem transpose_mem_doublyStochastic
    {n : ℕ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W ∈ doublyStochastic ℝ (Fin n)) :
    Matrix.transpose W ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum] at hW ⊢
  rcases hW with ⟨hW_nonneg, hW_row, hW_col⟩
  constructor
  · intro i j
    simpa [Matrix.transpose_apply] using hW_nonneg j i
  · constructor
    · intro i
      simpa [Matrix.transpose_apply] using hW_col i
    · intro j
      simpa [Matrix.transpose_apply] using hW_row j

/-- Helper for Proposition 6.38: rewriting a fixed unitary/simplex affine model through the
mixed overlap scores identifies it with the Chapter 6 entropy-regularized simplex owner. -/
private theorem unitarySimplexObjective_eq_entropyRegularizedSimplexObjective_mixedScore
    (hn : 0 < n) (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (u : Δ[n]) :
    let UB : Matrix.unitaryGroup (Fin n) ℝ :=
      (RealSymmetricMatrixSpace.isHermitian X).eigenvectorUnitary
    let W : Mat := fun i j ↦ (((star (UB : Mat) * (U : Mat)) i j) ^ (2 : ℕ))
    Matrix.trace
        ((X : Mat) * ((U : Mat) * Matrix.diagonal (fun i : Fin n ↦ (u i : ℝ)) * star (U : Mat)))
      - (μ : ℝ) * normalizedEntropyProxFunction ⟨n, hn⟩ u + (μ : ℝ) * Real.log (n : ℝ)
      =
        entropyRegularizedSimplexObjective ⟨n, hn⟩ μ
          (WithLp.toLp 2 ((Matrix.transpose W).mulVec (eigenvalues X))) u := by
  let UB : Matrix.unitaryGroup (Fin n) ℝ :=
    (RealSymmetricMatrixSpace.isHermitian X).eigenvectorUnitary
  let W : Mat := fun i j ↦ (((star (UB : Mat) * (U : Mat)) i j) ^ (2 : ℕ))
  have hspec :
      (X : Mat) = (UB : Mat) * Matrix.diagonal (eigenvalues X) * star (UB : Mat) := by
    simpa [UB, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using
      (RealSymmetricMatrixSpace.isHermitian X).spectral_theorem
  have hpairing :
      Matrix.trace
          ((X : Mat) * ((U : Mat) * Matrix.diagonal (fun i : Fin n ↦ (u i : ℝ)) * star (U : Mat)))
        = ∑ i : Fin n, ∑ j : Fin n, eigenvalues X i * W i j * (u j : ℝ) := by
    rw [hspec]
    simpa [UB, W] using
      unitary_diagonal_pairing_eq_sum_overlapSquares
        UB U (eigenvalues X) (fun i : Fin n ↦ (u i : ℝ))
  have hscore :
      ∑ i : Fin n, ∑ j : Fin n, eigenvalues X i * W i j * (u j : ℝ) =
        ∑ j : Fin n, (u j : ℝ) *
          (WithLp.toLp 2 ((Matrix.transpose W).mulVec (eigenvalues X))) j := by
    calc
      ∑ i : Fin n, ∑ j : Fin n, eigenvalues X i * W i j * (u j : ℝ)
          = ∑ j : Fin n, ∑ i : Fin n,
              (u j : ℝ) * (Matrix.transpose W) j i * eigenvalues X i := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl ?_
                intro j hj
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [Matrix.transpose_apply]
                ring
      _ = ∑ j : Fin n, (u j : ℝ) * ∑ i : Fin n,
            (Matrix.transpose W) j i * eigenvalues X i := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = ∑ j : Fin n, (u j : ℝ) *
            (WithLp.toLp 2 ((Matrix.transpose W).mulVec (eigenvalues X))) j := by
            simp [Matrix.mulVec, dotProduct]
  dsimp [UB, W]
  rw [entropyRegularizedSimplexObjective, hpairing]
  simpa using
    congrArg
      (fun t : ℝ ↦
        t - (μ : ℝ) * normalizedEntropyProxFunction ⟨n, hn⟩ u + (μ : ℝ) * Real.log (n : ℝ))
      hscore

/-- Helper for Proposition 6.38: every affine unitary/simplex model lies below the Chapter 6
smoothing owner. -/
private theorem unitarySimplexObjective_le_logSumExpMaxEigenvalueSmoothing
    (hn : 0 < n) (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (u : Δ[n]) :
    Matrix.trace
        ((X : Mat) * ((U : Mat) * Matrix.diagonal (fun i : Fin n ↦ (u i : ℝ)) * star (U : Mat)))
      - (μ : ℝ) * normalizedEntropyProxFunction ⟨n, hn⟩ u + (μ : ℝ) * Real.log (n : ℝ)
      ≤ logSumExpMaxEigenvalueSmoothing μ X := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let UB : Matrix.unitaryGroup (Fin n) ℝ :=
    (RealSymmetricMatrixSpace.isHermitian X).eigenvectorUnitary
  let W : Mat := fun i j ↦ (((star (UB : Mat) * (U : Mat)) i j) ^ (2 : ℕ))
  let s : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 ((Matrix.transpose W).mulVec (eigenvalues X))
  have hW :
      W ∈ doublyStochastic ℝ (Fin n) :=
    squared_overlap_matrix_mem_doubly_stochastic UB U
  have hW_transpose :
      Matrix.transpose W ∈ doublyStochastic ℝ (Fin n) :=
    transpose_mem_doublyStochastic hW
  have hsoftmax_max :
      IsMaxOn (entropyRegularizedSimplexObjective ⟨n, hn⟩ μ s) Set.univ
        (entropySimplexSoftmax ⟨n, hn⟩ μ s) := by
    exact (entropyRegularizedSimplexObjective_isMaxOn_iff ⟨n, hn⟩ μ s
      (entropySimplexSoftmax ⟨n, hn⟩ μ s)).2 rfl
  calc
    Matrix.trace
        ((X : Mat) * ((U : Mat) * Matrix.diagonal (fun i : Fin n ↦ (u i : ℝ)) * star (U : Mat)))
      - (μ : ℝ) * normalizedEntropyProxFunction ⟨n, hn⟩ u + (μ : ℝ) * Real.log (n : ℝ)
        = entropyRegularizedSimplexObjective ⟨n, hn⟩ μ s u := by
            simpa [UB, W, s] using
              unitarySimplexObjective_eq_entropyRegularizedSimplexObjective_mixedScore
                hn μ X U u
    _ ≤ entropyRegularizedSimplexObjective ⟨n, hn⟩ μ s (entropySimplexSoftmax ⟨n, hn⟩ μ s) := by
          exact (isMaxOn_iff.mp hsoftmax_max) u (Set.mem_univ _)
    _ = η μ s := entropyRegularizedSimplexObjective_softmax_eq_value ⟨n, hn⟩ μ s
    _ ≤ η μ (WithLp.toLp 2 (eigenvalues X)) := by
          simpa [s] using eta_mulVec_le_of_doublyStochastic μ hW_transpose (eigenvalues X)
    _ = logSumExpMaxEigenvalueSmoothing μ X := by
          simpa using (logSumExpMaxEigenvalueSmoothing_eq_eta μ X).symm

/-- Helper for Proposition 6.38: the Chapter 6 smoothing owner attains its value at the affine
unitary/simplex model built from the eigenbasis of `X` and the corresponding softmax weights. -/
private theorem logSumExpMaxEigenvalueSmoothing_eq_unitarySimplexObjective
    (hn : 0 < n) (μ : {μ : ℝ // 0 < μ}) (X : 𝕊^n) :
    let U : Matrix.unitaryGroup (Fin n) ℝ :=
      (RealSymmetricMatrixSpace.isHermitian X).eigenvectorUnitary
    let u : Δ[n] := entropySimplexSoftmax ⟨n, hn⟩ μ (WithLp.toLp 2 (eigenvalues X))
    Matrix.trace
        ((X : Mat) * ((U : Mat) * Matrix.diagonal (fun i : Fin n ↦ (u i : ℝ)) * star (U : Mat)))
      - (μ : ℝ) * normalizedEntropyProxFunction ⟨n, hn⟩ u + (μ : ℝ) * Real.log (n : ℝ)
      = logSumExpMaxEigenvalueSmoothing μ X := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let U : Matrix.unitaryGroup (Fin n) ℝ :=
    (RealSymmetricMatrixSpace.isHermitian X).eigenvectorUnitary
  let u : Δ[n] := entropySimplexSoftmax ⟨n, hn⟩ μ (WithLp.toLp 2 (eigenvalues X))
  let W : Mat := fun i j ↦ (((star (U : Mat) * (U : Mat)) i j) ^ (2 : ℕ))
  have hW :
      Matrix.transpose W = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [W]
    · simp [W, hij, ne_comm.mp hij]
  have hmulVec :
      (Matrix.transpose W).mulVec (eigenvalues X) = eigenvalues X := by
    rw [hW]
    simp
  calc
    Matrix.trace
        ((X : Mat) * ((U : Mat) * Matrix.diagonal (fun i : Fin n ↦ (u i : ℝ)) * star (U : Mat)))
      - (μ : ℝ) * normalizedEntropyProxFunction ⟨n, hn⟩ u + (μ : ℝ) * Real.log (n : ℝ)
        = entropyRegularizedSimplexObjective ⟨n, hn⟩ μ
            (WithLp.toLp 2 ((Matrix.transpose W).mulVec (eigenvalues X))) u := by
              simpa [U, u, W] using
                unitarySimplexObjective_eq_entropyRegularizedSimplexObjective_mixedScore
                  hn μ X U u
    _ = entropyRegularizedSimplexObjective ⟨n, hn⟩ μ
          (WithLp.toLp 2 (eigenvalues X)) u := by
            simp [hmulVec]
    _ = η μ (WithLp.toLp 2 (eigenvalues X)) := by
      simpa [u] using
        entropyRegularizedSimplexObjective_softmax_eq_value
          ⟨n, hn⟩ μ (WithLp.toLp 2 (eigenvalues X))
    _ = logSumExpMaxEigenvalueSmoothing μ X := by
          exact (logSumExpMaxEigenvalueSmoothing_eq_eta μ X).symm

/-- Helper for Proposition 6.38: the affine pullback of the Chapter 6 smoothing owner is globally
`C²`. -/
private theorem smoothedSemidefiniteObjective_contDiff_two
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    ContDiff ℝ 2 (smoothedSemidefiniteObjective n μ C A) := by
  have hOwner := logSumExpMaxEigenvalueSmoothing_contDiff_and_hessianQuadraticForm_le n μ
  -- Compose the global owner `C²` result with the fixed affine shift on its exact raw spelling.
  simpa [smoothedSemidefiniteObjective, add_comm, add_left_comm, add_assoc] using
    hOwner.1.comp (affineShift_contDiff_two C A)

/-- Helper for Proposition 6.38: the Chapter 6 smoothing owner is convex on the whole symmetric
matrix space. -/
private theorem logSumExpMaxEigenvalueSmoothing_convexCombination_le
    (hn : 0 < n) (μ : {μ : ℝ // 0 < μ}) (X Y : 𝕊^n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    logSumExpMaxEigenvalueSmoothing μ (a • X + b • Y) ≤
      a * logSumExpMaxEigenvalueSmoothing μ X + b * logSumExpMaxEigenvalueSmoothing μ Y := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let Z : 𝕊^n := a • X + b • Y
  let U : Matrix.unitaryGroup (Fin n) ℝ :=
    (RealSymmetricMatrixSpace.isHermitian Z).eigenvectorUnitary
  let u : Δ[n] := entropySimplexSoftmax ⟨n, hn⟩ μ (WithLp.toLp 2 (eigenvalues Z))
  let M : Mat := (U : Mat) * Matrix.diagonal (fun i : Fin n ↦ (u i : ℝ)) * star (U : Mat)
  let offset : ℝ :=
    - (μ : ℝ) * normalizedEntropyProxFunction ⟨n, hn⟩ u + (μ : ℝ) * Real.log (n : ℝ)
  have hZeq :
      Matrix.trace ((Z : Mat) * M) + offset = logSumExpMaxEigenvalueSmoothing μ Z := by
    simpa [M, offset, sub_eq_add_neg, add_assoc] using
      logSumExpMaxEigenvalueSmoothing_eq_unitarySimplexObjective hn μ Z
  have hXle :
      Matrix.trace ((X : Mat) * M) + offset ≤ logSumExpMaxEigenvalueSmoothing μ X := by
    simpa [M, offset, sub_eq_add_neg, add_assoc] using
      unitarySimplexObjective_le_logSumExpMaxEigenvalueSmoothing hn μ X U u
  have hYle :
      Matrix.trace ((Y : Mat) * M) + offset ≤ logSumExpMaxEigenvalueSmoothing μ Y := by
    simpa [M, offset, sub_eq_add_neg, add_assoc] using
      unitarySimplexObjective_le_logSumExpMaxEigenvalueSmoothing hn μ Y U u
  have hAffine :
      Matrix.trace ((Z : Mat) * M) + offset =
        a * (Matrix.trace ((X : Mat) * M) + offset) +
          b * (Matrix.trace ((Y : Mat) * M) + offset) := by
    have htrace :
        Matrix.trace ((Z : Mat) * M) =
          a * Matrix.trace ((X : Mat) * M) + b * Matrix.trace ((Y : Mat) * M) := by
      change
        Matrix.trace (((a • (X : Mat) + b • (Y : Mat)) * M)) =
          a * Matrix.trace ((X : Mat) * M) + b * Matrix.trace ((Y : Mat) * M)
      calc
        Matrix.trace (((a • (X : Mat) + b • (Y : Mat)) * M))
            = Matrix.trace ((a • (X : Mat)) * M + (b • (Y : Mat)) * M) := by
                rw [add_mul]
        _ = Matrix.trace (a • ((X : Mat) * M) + b • ((Y : Mat) * M)) := by
              simp
        _ = a * Matrix.trace ((X : Mat) * M) + b * Matrix.trace ((Y : Mat) * M) := by
              simp [smul_eq_mul, Matrix.trace_add, Matrix.trace_smul]
    have hoffset : offset = (a + b) * offset := by
      rw [hab]
      ring
    calc
      Matrix.trace ((Z : Mat) * M) + offset
          = (a * Matrix.trace ((X : Mat) * M) + b * Matrix.trace ((Y : Mat) * M)) +
              ((a + b) * offset) := by
                nlinarith [htrace, hoffset]
      _ = a * (Matrix.trace ((X : Mat) * M) + offset) +
            b * (Matrix.trace ((Y : Mat) * M) + offset) := by
              nlinarith [hab]
  calc
    logSumExpMaxEigenvalueSmoothing μ (a • X + b • Y)
        = Matrix.trace ((Z : Mat) * M) + offset := by
            simpa [Z] using hZeq.symm
    _ = a * (Matrix.trace ((X : Mat) * M) + offset) +
          b * (Matrix.trace ((Y : Mat) * M) + offset) := hAffine
    _ ≤ a * logSumExpMaxEigenvalueSmoothing μ X + b * logSumExpMaxEigenvalueSmoothing μ Y := by
          gcongr

/-- Helper for Proposition 6.38: the Chapter 6 smoothing owner is convex on the whole symmetric
matrix space. -/
private theorem logSumExpMaxEigenvalueSmoothing_convexOn
    (μ : {μ : ℝ // 0 < μ}) :
    ConvexOn ℝ Set.univ (logSumExpMaxEigenvalueSmoothing μ : 𝕊^n → ℝ) := by
  by_cases hzero : n = 0
  · subst hzero
    refine ⟨convex_univ, ?_⟩
    intro X hX Y hY a b ha hb hab
    simp [logSumExpMaxEigenvalueSmoothing]
  · have hn : 0 < n := Nat.pos_iff_ne_zero.mpr hzero
    letI : NeZero n := ⟨hzero⟩
    refine ⟨convex_univ, ?_⟩
    intro X hX Y hY a b ha hb hab
    exact logSumExpMaxEigenvalueSmoothing_convexCombination_le hn μ X Y ha hb hab

/-- Helper for Proposition 6.38: convexity of the Chapter 6 smoothing owner transports through the
affine pullback `y ↦ C + A y`. -/
private theorem smoothedSemidefiniteObjective_convexOn
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    ConvexOn ℝ Set.univ (smoothedSemidefiniteObjective n μ C A) := by
  let g : E →ᵃ[ℝ] 𝕊^n :=
    A.toLinearMap.toAffineMap + AffineMap.const ℝ E C
  -- Affine precomposition keeps the owner convex once the source surface is normalized to
  -- `y ↦ C + A y`.
  simpa [smoothedSemidefiniteObjective, g, add_comm, add_left_comm, add_assoc] using
    (logSumExpMaxEigenvalueSmoothing_convexOn μ).comp_affineMap g

/-- Helper for Proposition 6.38: owner-side Hessian nonnegativity transports through the affine
pullback `y ↦ C + A y`. -/
private theorem smoothedSemidefiniteObjective_hessianQuadraticForm_nonneg
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n)
    (y h : E) :
    0 ≤ inner ℝ h (hessian (smoothedSemidefiniteObjective n μ C A) y h) := by
  have hiff :
      ConvexOn ℝ Set.univ (smoothedSemidefiniteObjective n μ C A) ↔
        ∀ x ∈ Set.univ, ∀ v : E,
          0 ≤ inner ℝ ((hessian (smoothedSemidefiniteObjective n μ C A) x) v) v := by
    exact convexOn_iff_hessian_quadratic_form_nonneg
      isOpen_univ convex_univ (smoothedSemidefiniteObjective_contDiff_two μ C A).contDiffOn
  simpa [real_inner_comm] using
    (hiff.mp (smoothedSemidefiniteObjective_convexOn μ C A)) y (by simp) h

/-- Helper for Proposition 6.38: package the pullback Hessian sign and upper bound into the
absolute-value estimate needed by the operator-norm step. -/
private theorem smoothedSemidefiniteObjective_hessianQuadraticForm_abs_le
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n)
    (y h : E) :
    |inner ℝ (hessian (smoothedSemidefiniteObjective n μ C A) y h) h| ≤
      ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
  have howner := logSumExpMaxEigenvalueSmoothing_contDiff_and_hessianQuadraticForm_le n μ
  have hbound :=
    affinePullbackObjective_hessianQuadraticForm_le μ C A y h
      (howner.1.contDiffAt) (howner.2 (C + A y) (A h))
  have hyC2 : ContDiffAt ℝ 2 (smoothedSemidefiniteObjective n μ C A) y :=
    (smoothedSemidefiniteObjective_contDiff_two μ C A).contDiffAt
  have hupper :
      inner ℝ h (hessian (smoothedSemidefiniteObjective n μ C A) y h) ≤
        ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
    rwa [iteratedFDerivTwo_apply_eq_hessianQuadraticForm hyC2] at hbound
  have hnonneg :
      0 ≤ inner ℝ h (hessian (smoothedSemidefiniteObjective n μ C A) y h) :=
    smoothedSemidefiniteObjective_hessianQuadraticForm_nonneg μ C A y h
  have hnonneg' :
      0 ≤ inner ℝ (hessian (smoothedSemidefiniteObjective n μ C A) y h) h := by
    simpa [real_inner_comm] using hnonneg
  -- Cache the sign-plus-upper-bound endgame once so the norm proof can consume a single absolute
  -- quadratic-form estimate instead of rebuilding it inline.
  calc
    |inner ℝ (hessian (smoothedSemidefiniteObjective n μ C A) y h) h|
        = inner ℝ (hessian (smoothedSemidefiniteObjective n μ C A) y h) h := by
            exact abs_of_nonneg hnonneg'
    _ = inner ℝ h (hessian (smoothedSemidefiniteObjective n μ C A) y h) := by
          rw [real_inner_comm]
    _ ≤ ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := hupper

/-- Helper for Proposition 6.38: the pullback gradient is globally Lipschitz with the textbook
constant `(1 / μ) ‖A‖²`. -/
private theorem affinePullbackObjective_gradient_lipschitz_global
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (μ : {μ : ℝ // 0 < μ}) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    LipschitzWith
      (Real.toNNReal ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)))
      (fun y ↦ gradient (smoothedSemidefiniteObjective n μ C A) y) := by
  let L : NNReal := Real.toNNReal ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ))
  have hL_nonneg : 0 ≤ ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) := by
    rw [one_div]
    exact mul_nonneg (inv_nonneg.mpr μ.property.le) (pow_nonneg (norm_nonneg A) _)
  have hdiff :
      Differentiable ℝ (∇ (smoothedSemidefiniteObjective n μ C A)) :=
    differentiable_gradient_of_contDiff_two (smoothedSemidefiniteObjective_contDiff_two μ C A)
  have hbound :
      ∀ y : E, ‖hessian (smoothedSemidefiniteObjective n μ C A) y‖ ≤ (L : ℝ) := by
    intro y
    have hyC2 : ContDiffAt ℝ 2 (smoothedSemidefiniteObjective n μ C A) y :=
      (smoothedSemidefiniteObjective_contDiff_two μ C A).contDiffAt
    have hsymm :
        (hessian (smoothedSemidefiniteObjective n μ C A) y).IsSymmetric :=
      fderiv_gradient_isSymmetric_of_contDiffAt hyC2
    have hL_real_nonneg : 0 ≤ (L : ℝ) := by
      simpa [L, Real.toNNReal_of_nonneg hL_nonneg] using hL_nonneg
    have hquadL :
        ∀ u : E,
          |inner ℝ ((hessian (smoothedSemidefiniteObjective n μ C A) y) u) u| ≤
            (L : ℝ) * ‖u‖ ^ (2 : ℕ) := by
      simpa [L, Real.toNNReal_of_nonneg hL_nonneg] using
        (smoothedSemidefiniteObjective_hessianQuadraticForm_abs_le μ C A y)
    -- Turn the absolute quadratic-form estimate into the operator-norm bound needed by the
    -- Chapter 1 gradient-Lipschitz theorem.
    have hnorm : ‖hessian (smoothedSemidefiniteObjective n μ C A) y‖ ≤ (L : ℝ) :=
      selfAdjoint_norm_le_of_quadratic_bound
        hsymm hL_real_nonneg hquadL
    simpa [L, Real.toNNReal_of_nonneg hL_nonneg] using hnorm
  -- The global gradient-Lipschitz conclusion is exactly the Chapter 1 Hessian-norm criterion.
  change LipschitzWith L (∇ (smoothedSemidefiniteObjective n μ C A))
  have hLip : LipschitzWith L (∇ (smoothedSemidefiniteObjective n μ C A)) :=
    lipschitzGradient_of_norm_hessian_le hdiff hbound
  exact hLip

-- LeanSearch recall: `Convex.lipschitzOnWith_of_nnnorm_fderiv_le` packages the convex-set
-- mean-value step on the canonical `LipschitzOnWith` owner, so the Euclidean `gradient`
-- companion below keeps the extra convexity and Hessian-sign hypotheses needed by that surface.

/-- Generic affine-pullback Hessian companion: if `φ(y) = f(C + A y)` on `Q`, where `f` is twice
continuously differentiable on `((fun y ↦ C + A y) '' Q)` and satisfies the owner-side Hessian
quadratic-form bound there, then the pullback satisfies the quadratic-form estimate
`μ⁻¹ ‖A‖² ‖h‖²` on `Q`. -/
theorem affinePullbackObjective_hessianQuadraticForm_le_on
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : {μ : ℝ // 0 < μ}) (Q : Set E)
    (fμ : 𝕊^n → ℝ) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n)
    (hC2 : ∀ X ∈ ((fun y : E ↦ C + A y) '' Q), ContDiffAt ℝ 2 fμ X)
    (hHess :
      ∀ X ∈ ((fun y : E ↦ C + A y) '' Q), ∀ H : 𝕊^n,
        secondDirectionalDerivative fμ X H ≤
          (1 / (μ : ℝ)) * ‖((H : Mat))‖ ^ (2 : ℕ)) :
    ∀ y ∈ Q, ∀ h : E,
      secondDirectionalDerivative
          (affinePullbackObjective fμ C A) y h ≤
        ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
  let _ := hC2
  intro y hy h
  have hyIm : C + A y ∈ ((fun y : E ↦ C + A y) '' Q) := ⟨y, hy, rfl⟩
  have hμ_nonneg : 0 ≤ (1 / (μ : ℝ)) := by
    exact one_div_nonneg.mpr μ.property.le
  have hSecond :
      secondDirectionalDerivative (affinePullbackObjective fμ C A) y h =
        secondDirectionalDerivative fμ (C + A y) (A h) := by
    -- The affine pullback slice is literally the owner slice at the transported base point.
    exact secondDirectionalDerivative_affinePullback fμ C A y h
  have hAh_le : ‖(((A h : 𝕊^n) : Mat))‖ ≤ ‖A‖ * ‖h‖ := by
    simpa using A.le_opNorm h
  have hAh_sq :
      ‖(((A h : 𝕊^n) : Mat))‖ ^ (2 : ℕ) ≤ (‖A‖ * ‖h‖) ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ (norm_nonneg _) hAh_le 2
  calc
    secondDirectionalDerivative (affinePullbackObjective fμ C A) y h
        = secondDirectionalDerivative fμ (C + A y) (A h) := hSecond
    _ ≤ (1 / (μ : ℝ)) * ‖(((A h : 𝕊^n) : Mat))‖ ^ (2 : ℕ) := hHess _ hyIm (A h)
    _ ≤ (1 / (μ : ℝ)) * (‖A‖ * ‖h‖) ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hAh_sq hμ_nonneg
    _ = ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
          rw [mul_pow]
          ring

/-- Affine-pullback companion: on a convex set `Q`, the pullback gradient is Lipschitz with
constant `μ⁻¹ ‖A‖²` once the extra Hessian nonnegativity hypothesis needed by the mean-value
`LipschitzOnWith` surface is stated explicitly. -/
theorem affinePullbackObjective_gradient_lipschitzOn
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (μ : {μ : ℝ // 0 < μ}) (Q : Set E)
    (hQ_convex : Convex ℝ Q)
    (fμ : 𝕊^n → ℝ) (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n)
    (hC2 : ∀ X ∈ ((fun y : E ↦ C + A y) '' Q), ContDiffAt ℝ 2 fμ X)
    (hHess_nonneg :
      ∀ X ∈ ((fun y : E ↦ C + A y) '' Q), ∀ H : 𝕊^n,
        0 ≤ secondDirectionalDerivative fμ X H)
    (hHess :
      ∀ X ∈ ((fun y : E ↦ C + A y) '' Q), ∀ H : 𝕊^n,
        secondDirectionalDerivative fμ X H ≤
          (1 / (μ : ℝ)) * ‖((H : Mat))‖ ^ (2 : ℕ)) :
    LipschitzOnWith
      (Real.toNNReal
        ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)))
      (fun y ↦
        gradient
          (affinePullbackObjective fμ C A) y) Q := by
  let g : E → ℝ := affinePullbackObjective fμ C A
  let L : NNReal := Real.toNNReal ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ))
  have hL_nonneg : 0 ≤ ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) := by
    exact mul_nonneg (one_div_nonneg.mpr μ.property.le) (pow_nonneg (norm_nonneg A) _)
  change LipschitzOnWith L (∇ g) Q
  refine hQ_convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (f := ∇ g) (f' := fun y : E ↦ hessian g y) ?_ ?_
  · intro y hy
    have hyIm : C + A y ∈ ((fun y : E ↦ C + A y) '' Q) := ⟨y, hy, rfl⟩
    have hyC2 : ContDiffAt ℝ 2 g y := by
      -- Compose the owner-side `C²` hypothesis with the raw affine shift surface used by `g`.
      simpa [g, affinePullbackObjective] using
        (hC2 _ hyIm).comp y (affineShift_contDiffAt_two C A y)
    -- A `C²` scalar field has a differentiable gradient at the same point.
    exact (differentiableAt_gradient_of_contDiffAt_two hyC2).hasFDerivAt.hasFDerivWithinAt
  · intro y hy
    have hyIm : C + A y ∈ ((fun y : E ↦ C + A y) '' Q) := ⟨y, hy, rfl⟩
    have hyC2 : ContDiffAt ℝ 2 g y := by
      -- Reuse the same local `C²` bridge because both the symmetry and Hessian formulas are read
      -- from the pullback at this point.
      simpa [g, affinePullbackObjective] using
        (hC2 _ hyIm).comp y (affineShift_contDiffAt_two C A y)
    have hsymm :
        (hessian g y).IsSymmetric :=
      fderiv_gradient_isSymmetric_of_contDiffAt hyC2
    have hupper :
        ∀ u : E,
          inner ℝ u (hessian g y u) ≤
            ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖u‖ ^ (2 : ℕ) := by
      intro u
      have hu :=
        affinePullbackObjective_hessianQuadraticForm_le_on
          (n := n) μ Q fμ C A hC2 hHess y hy u
      -- Rewrite the second directional derivative bound as the Hessian quadratic-form bound.
      rwa [secondDirectionalDerivative_eq_hessian_quadratic_form hyC2] at hu
    have hnonneg :
        ∀ u : E, 0 ≤ inner ℝ u (hessian g y u) := by
      intro u
      have hu :
          0 ≤ secondDirectionalDerivative g y u := by
        calc
          0 ≤ secondDirectionalDerivative fμ (C + A y) (A u) := hHess_nonneg _ hyIm (A u)
          _ = secondDirectionalDerivative g y u := by
              symm
              simpa [g, affinePullbackObjective] using
                secondDirectionalDerivative_affinePullback fμ C A y u
      -- The owner-side sign condition becomes the pullback Hessian nonnegativity after the usual
      -- second-derivative/Hessian identification.
      rwa [secondDirectionalDerivative_eq_hessian_quadratic_form hyC2] at hu
    have hquad :
        ∀ u : E,
          |inner ℝ ((hessian g y) u) u| ≤
            ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖u‖ ^ (2 : ℕ) := by
      intro u
      have hnonneg' : 0 ≤ inner ℝ ((hessian g y) u) u := by
        simpa [real_inner_comm] using hnonneg u
      calc
        |inner ℝ ((hessian g y) u) u|
            = inner ℝ ((hessian g y) u) u := abs_of_nonneg hnonneg'
        _ = inner ℝ u (hessian g y u) := by rw [real_inner_comm]
        _ ≤ ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖u‖ ^ (2 : ℕ) := hupper u
    have hnorm :
        ‖hessian g y‖ ≤ ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) :=
      selfAdjoint_norm_le_of_quadratic_bound hsymm hL_nonneg hquad
    -- Convert the operator-norm Hessian estimate into the `‖fderiv‖₊` bound required by the
    -- convex-set mean value theorem for `∇ g`.
    simpa [L, g, hessian, Real.toNNReal_of_nonneg hL_nonneg] using hnorm

/-- Hessian companion for the Chapter 6 smoothing pullback
`φ_μ(y) = f_μ (C + A y) = smoothedSemidefiniteObjective n μ C A y`: the Euclidean Hessian
quadratic form is bounded above by `μ⁻¹ ‖A‖² ‖h‖²` on `Q`. -/
theorem smoothedSemidefiniteObjective_hessianQuadraticForm_le_on
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : {μ : ℝ // 0 < μ}) (Q : Set E)
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    ∀ y ∈ Q, ∀ h : E,
      inner ℝ h (hessian (smoothedSemidefiniteObjective n μ C A) y h) ≤
        ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
  intro y hy h
  have habs :
      |inner ℝ h (hessian (smoothedSemidefiniteObjective n μ C A) y h)| ≤
        ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)) * ‖h‖ ^ (2 : ℕ) := by
    simpa [real_inner_comm] using
      smoothedSemidefiniteObjective_hessianQuadraticForm_abs_le μ C A y h
  exact le_trans (le_abs_self _) habs

/-- Proposition 6.38 [Lipschitz constant for `∇φ_μ`]: for the Chapter 6 smoothing pullback
`φ_μ(y) = f_μ (C + A y) = smoothedSemidefiniteObjective n μ C A y`, the gradient is
Lipschitz on `Q` with constant `μ⁻¹ ‖A‖²`.

The Hessian quadratic-form estimate is recorded in
`smoothedSemidefiniteObjective_hessianQuadraticForm_le_on`, and the specialization
`μ = ε / (2 * log n)` is recorded just below. -/
theorem smoothedSemidefiniteObjective_gradient_lipschitzOn
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : {μ : ℝ // 0 < μ}) (Q : Set E)
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n) :
    LipschitzOnWith
      (Real.toNNReal ((1 / (μ : ℝ)) * ‖A‖ ^ (2 : ℕ)))
      (fun y ↦ gradient (smoothedSemidefiniteObjective n μ C A) y) Q := by
  -- Restrict the already-proved global Lipschitz estimate to the requested set `Q`.
  exact (affinePullbackObjective_gradient_lipschitz_global (n := n) μ C A).lipschitzOnWith

private def epsDivTwoLogSmoothingParameter
    (n : ℕ) (ε : ℝ) (hn : 1 < n) (hε : 0 < ε) : {μ : ℝ // 0 < μ} := by
  refine ⟨ε / (2 * Real.log (n : ℝ)), ?_⟩
  have hn_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn_real
  have hdenom : 0 < 2 * Real.log (n : ℝ) := by
    nlinarith
  exact div_pos hε hdenom

/-- Helper for Proposition 6.38: the textbook choice `μ = ε / (2 log n)` has reciprocal
`(2 log n) / ε`. -/
private theorem epsDivTwoLogSmoothingParameter_inv
    (n : ℕ) (ε : ℝ) (hn : 1 < n) (hε : 0 < ε) :
    1 / ((epsDivTwoLogSmoothingParameter n ε hn hε : ℝ)) =
      (2 * Real.log (n : ℝ)) / ε := by
  have hden_ne : 2 * Real.log (n : ℝ) ≠ 0 := by
    have hn_real : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_real
    positivity
  -- Specialize the textbook smoothing parameter and clear the reciprocal once.
  change 1 / (ε / (2 * Real.log (n : ℝ))) = (2 * Real.log (n : ℝ)) / ε
  field_simp [hε.ne', hden_ne]

/-- Concrete smoothing corollary: with `μ = ε / (2 * log n)`, the Chapter 6 smoothed
semidefinite objective has gradient Lipschitz constant
`((2 * log n) / ε) * ‖A‖²` on `Q`. -/
theorem smoothedSemidefiniteObjective_gradient_lipschitzOn_of_eps_div_twoLog
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ε : ℝ) (Q : Set E)
    (C : 𝕊^n) (A : E →L[ℝ] 𝕊^n)
    (hn : 1 < n) (hε : 0 < ε) :
    LipschitzOnWith
      (Real.toNNReal (((2 * Real.log (n : ℝ)) / ε) * ‖A‖ ^ (2 : ℕ)))
      (fun y ↦
        gradient
          (smoothedSemidefiniteObjective
            n (epsDivTwoLogSmoothingParameter n ε hn hε) C A) y) Q := by
  -- Reuse the dedicated reciprocal simplification for the textbook smoothing choice.
  simpa [epsDivTwoLogSmoothingParameter_inv n ε hn hε] using
    (smoothedSemidefiniteObjective_gradient_lipschitzOn
      (n := n) (epsDivTwoLogSmoothingParameter n ε hn hε) Q C A)

end

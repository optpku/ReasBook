/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Notation_2_4
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_32
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus

public section

noncomputable section

universe u v

variable {H1 : Type u} [NormedAddCommGroup H1] [InnerProductSpace ℝ H1] [CompleteSpace H1]
variable {H2 : Type v} [NormedAddCommGroup H2] [InnerProductSpace ℝ H2] [CompleteSpace H2]

omit [CompleteSpace H1] in
/-- Helper for Example 2.36: the half-scaled identity penalty is half of the
squared norm. -/
lemma halfScaledId_inner_eq_half_normSq (x : H1) :
    inner ℝ ((((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) x)) x = ‖x‖ ^ 2 / 2 := by
  -- Rewrite the penalty term into the norm-squared normal form used throughout the example.
  rw [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- Helper for Example 2.36: expanding `‖x + τ • y‖ ^ 2` isolates its constant,
linear, and quadratic parts. -/
lemma normSq_add_smul_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (τ : ℝ) :
    ‖x + τ • y‖ ^ 2 = ‖x‖ ^ 2 + τ * (inner ℝ x y + inner ℝ y x) + τ ^ 2 * ‖y‖ ^ 2 := by
  -- Expand the square through the inner product and collect the scalar factors.
  calc
    ‖x + τ • y‖ ^ 2 = inner ℝ (x + τ • y) (x + τ • y) := by
      rw [real_inner_self_eq_norm_sq]
    _ = inner ℝ x x + inner ℝ x (τ • y) + (inner ℝ (τ • y) x + inner ℝ (τ • y) (τ • y)) := by
      rw [inner_add_left, inner_add_right, inner_add_right]
    _ = ‖x‖ ^ 2 + τ * (inner ℝ x y + inner ℝ y x) + τ ^ 2 * ‖y‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq, real_inner_smul_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring

/-- Helper for Example 2.36: the scaled Tikhonov functional has the expected
Fréchet derivative as the sum of the residual and penalty functionals. -/
lemma tikhonovFunctional_hasFDerivAt (K : H1 →L[ℝ] H2) (g : H2) (α : ℝ) (f : H1) :
    HasFDerivAt
      (K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α)
      (((innerSL ℝ (K f - g)).comp K) + α • innerSL ℝ f) f := by
  let Jres : H1 → ℝ := fun x ↦ ‖K x - g‖ ^ 2 / 2
  let Jpen : H1 → ℝ := fun x ↦ α * inner ℝ ((((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) x)) x
  have hresSq :
      HasFDerivAt (fun x : H1 ↦ ‖K x - g‖ ^ 2)
        (2 • (innerSL ℝ (K f - g)).comp K) f := by
    -- Differentiate the residual term by chaining `x ↦ K x - g` with `‖·‖ ^ 2`.
    simpa using (K.hasFDerivAt.sub_const g).norm_sq
  have hres : HasFDerivAt Jres (((innerSL ℝ (K f - g)).comp K)) f := by
    -- Divide the squared residual by `2` after differentiating.
    have hresHalf :
        HasFDerivAt (fun x : H1 ↦ ‖K x - g‖ ^ 2 * (1 / 2 : ℝ))
          (((1 / 2 : ℝ)) • (2 • (innerSL ℝ (K f - g)).comp K)) f :=
      hresSq.mul_const (1 / 2 : ℝ)
    have hresHalf' :
        HasFDerivAt (fun x : H1 ↦ ‖K x - g‖ ^ 2 * (1 / 2 : ℝ))
          (((innerSL ℝ (K f - g)).comp K)) f :=
      hresHalf.congr_fderiv <| by
        ext h
        simp [innerSL_apply_apply]
    refine hresHalf'.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun x => by
      simp [Jres, div_eq_mul_inv]
  have hpenNorm :
      HasFDerivAt (fun x : H1 ↦ ‖x‖ ^ 2) (2 • innerSL ℝ f) f := by
    -- The penalty term is reduced to the derivative of `‖x‖ ^ 2`.
    simpa using (hasStrictFDerivAt_norm_sq f).hasFDerivAt
  have hpenAlpha :
      HasFDerivAt (fun x : H1 ↦ α * ‖x‖ ^ 2) (α • (2 • innerSL ℝ f)) f := by
    simpa using hpenNorm.const_mul α
  have hpen : HasFDerivAt Jpen (α • innerSL ℝ f) f := by
    -- Normalize the penalty before differentiating, then simplify the resulting scalar factor.
    have hpenHalf :
        HasFDerivAt (fun x : H1 ↦ α * ‖x‖ ^ 2 * (1 / 2 : ℝ))
          (((1 / 2 : ℝ)) • (α • (2 • innerSL ℝ f))) f :=
      hpenAlpha.mul_const (1 / 2 : ℝ)
    have hpenHalf' :
        HasFDerivAt (fun x : H1 ↦ α * ‖x‖ ^ 2 * (1 / 2 : ℝ))
          (α • innerSL ℝ f) f :=
      hpenHalf.congr_fderiv <| by
        ext h
        simp [innerSL_apply_apply]
        ring_nf
    refine hpenHalf'.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun x => by
      change α * inner ℝ ((((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) x)) x =
        α * ‖x‖ ^ 2 * (1 / 2 : ℝ)
      rw [halfScaledId_inner_eq_half_normSq]
      ring
  -- Combine the differentiated residual and penalty pieces.
  have hsum :
      HasFDerivAt
        ((fun x : H1 ↦ ‖K x - g‖ ^ 2 / 2) +
          fun x ↦ α * inner ℝ ((((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) x)) x)
        (((innerSL ℝ (K f - g)).comp K) + α • innerSL ℝ f) f :=
    hres.add hpen
  have hsum' : HasFDerivAt
      (fun x : H1 ↦
        ‖K x - g‖ ^ 2 / 2 +
          α * inner ℝ ((((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) x)) x)
      (((innerSL ℝ (K f - g)).comp K) + α • innerSL ℝ f) f := by
    refine hsum.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun x => by
      rfl
  refine hsum'.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [ContinuousLinearMap.tikhonovFunctional_def]

/-- Helper for Example 2.36: the operator-form vector reproduces the textbook
directional derivative via the inner product. -/
lemma operatorForm_inner_eq_directional (K : H1 →L[ℝ] H2) (g : H2) (α : ℝ) (f h : H1) :
    inner ℝ (((K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1) f - K.adjoint g)) h =
      inner ℝ (K f - g) (K h) + α * inner ℝ f h := by
  -- Move the adjoint across the inner product to recover the directional formula.
  calc
    inner ℝ (((K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1) f - K.adjoint g)) h
        = inner ℝ (((K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1) f)) h -
            inner ℝ (K.adjoint g) h := by
          rw [inner_sub_left]
    _ = inner ℝ ((K.adjoint.comp K) f) h +
          inner ℝ ((α • ContinuousLinearMap.id ℝ H1) f) h -
            inner ℝ (K.adjoint g) h := by
          rw [add_apply, inner_add_left]
    _ = inner ℝ (K f) (K h) + α * inner ℝ f h - inner ℝ g (K h) := by
          rw [ContinuousLinearMap.comp_apply, smul_apply,
            ContinuousLinearMap.id_apply, ContinuousLinearMap.adjoint_inner_left,
            ContinuousLinearMap.adjoint_inner_left, real_inner_smul_left]
    _ = inner ℝ (K f - g) (K h) + α * inner ℝ f h := by
          rw [inner_sub_left]
          ring

/-- Helper for Example 2.36: the analytic derivative functional is the Riesz
functional represented by the operator-form vector. -/
lemma operatorFunctional_eq_toDual_operatorForm (K : H1 →L[ℝ] H2) (g : H2) (α : ℝ) (f : H1) :
    ((innerSL ℝ (K f - g)).comp K + α • innerSL ℝ f) =
      (InnerProductSpace.toDual ℝ H1)
        (((K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1) f) - K.adjoint g) := by
  -- Compare both linear functionals on an arbitrary direction.
  ext h
  rw [add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    innerSL_apply_apply, InnerProductSpace.toDual_apply_apply]
  exact (operatorForm_inner_eq_directional K g α f h).symm

/-- First clause of Example 2.36. The Hilbert-space Tikhonov functional expands
along the line `τ ↦ f + τ • h` into constant, linear, and quadratic terms. -/
theorem tikhonovFunctional_lineExpansion (K : H1 →L[ℝ] H2) (g : H2) (α : ℝ)
    (f h : H1) (τ : ℝ) :
    K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α (f + τ • h) =
      (‖K f - g‖ ^ 2 + α * ‖f‖ ^ 2) / 2 +
        (τ / 2) *
          (inner ℝ (K f - g) (K h) + inner ℝ (K h) (K f - g) +
            α * inner ℝ f h + α * inner ℝ h f) +
        (τ ^ 2 / 2) * (‖K h‖ ^ 2 + α * ‖h‖ ^ 2) := by
  have hResidual :
      ‖K (f + τ • h) - g‖ ^ 2 =
        ‖K f - g‖ ^ 2 +
          τ * (inner ℝ (K f - g) (K h) + inner ℝ (K h) (K f - g)) +
          τ ^ 2 * ‖K h‖ ^ 2 := by
    have hMap : K (f + τ • h) - g = (K f - g) + τ • K h := by
      simp [sub_eq_add_neg, add_assoc, add_comm]
    rw [hMap, normSq_add_smul_eq]
  -- Expand the residual and penalty squares separately, then collect coefficients.
  rw [ContinuousLinearMap.tikhonovFunctional_def, halfScaledId_inner_eq_half_normSq]
  rw [hResidual, normSq_add_smul_eq (x := f) (y := h) τ]
  ring

/-- Second clause of Example 2.36. The derivative at `τ = 0` of the Tikhonov
functional along the line `τ ↦ f + τ • h` is
`inner ℝ (K f - g) (K h) + α * inner ℝ f h`. -/
theorem tikhonovFunctional_hasDerivAtLineAtZero (K : H1 →L[ℝ] H2) (g : H2) (α : ℝ)
    (f h : H1) :
    HasDerivAt
      (fun τ : ℝ ↦ K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α
        (f + τ • h))
      (inner ℝ (K f - g) (K h) + α * inner ℝ f h) 0 := by
  let J := K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α
  let lineCLM : ℝ →L[ℝ] H1 := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h
  have hsmulCLM :
      HasFDerivAt (⇑lineCLM) lineCLM 0 := by
    -- The line direction is a continuous linear map in the scalar variable.
    exact lineCLM.hasFDerivAt
  have hsmul : HasDerivAt (fun τ : ℝ ↦ τ • h) h 0 := by
    -- Specialize the one-dimensional Fréchet derivative to the scalar derivative.
    have hsmulBase : HasDerivAt (⇑lineCLM) (lineCLM 1) 0 := hsmulCLM.hasDerivAt
    have hsmulBase' : HasDerivAt (⇑lineCLM) h 0 := by
      refine hsmulBase.congr_deriv ?_
      simp [lineCLM, ContinuousLinearMap.smulRight_apply]
    refine hsmulBase'.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun τ => by
      simp [lineCLM, ContinuousLinearMap.smulRight_apply]
  have hline : HasDerivAt (fun τ : ℝ ↦ f + τ • h) h 0 := by
    -- Differentiate the affine line `τ ↦ f + τ • h`.
    have hlineF :
        HasFDerivAt (fun τ : ℝ ↦ lineCLM τ + f) lineCLM 0 := by
      exact hsmulCLM.add_const f
    have hlineBase : HasDerivAt (fun τ : ℝ ↦ lineCLM τ + f) (lineCLM 1) 0 := hlineF.hasDerivAt
    have hlineBase' : HasDerivAt (fun τ : ℝ ↦ lineCLM τ + f) h 0 := by
      refine hlineBase.congr_deriv ?_
      simp [lineCLM, ContinuousLinearMap.smulRight_apply]
    refine hlineBase'.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun τ => by
      simp [lineCLM, ContinuousLinearMap.smulRight_apply, add_comm]
  have hJ0 :
      HasFDerivAt J (((innerSL ℝ (K f - g)).comp K) + α • innerSL ℝ f)
        ((fun τ : ℝ ↦ f + τ • h) 0) := by
    simpa [J] using tikhonovFunctional_hasFDerivAt K g α f
  -- Chain rule turns the Fréchet derivative of `J` into the directional derivative at `τ = 0`.
  have hcomp :
      HasDerivAt (J ∘ fun τ : ℝ ↦ f + τ • h)
        (inner ℝ (K f) (K h) - inner ℝ g (K h) + α * inner ℝ f h) 0 := by
    simpa [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hJ0.comp_hasDerivAt 0 hline
  convert hcomp using 1
  · funext τ
    rfl
  · rw [inner_sub_left]

/-- Gradient clause of Example 2.36. The gradient of the Hilbert-space Tikhonov
functional has the operator form
`((K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1) f - K.adjoint g)`. -/
theorem tikhonovFunctional_gradient_eq_operatorForm (K : H1 →L[ℝ] H2) (g : H2) (α : ℝ)
    (f : H1) :
    gradient (K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α) f =
      ((K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1) f - K.adjoint g) := by
  -- Identify the gradient by comparing its Riesz functional with the computed Fréchet derivative.
  apply (InnerProductSpace.toDual ℝ H1).injective
  rw [toDual_gradient]
  calc
    fderiv ℝ (K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α) f
      = ((innerSL ℝ (K f - g)).comp K + α • innerSL ℝ f) :=
        (tikhonovFunctional_hasFDerivAt K g α f).fderiv
    _ = (InnerProductSpace.toDual ℝ H1)
          (((K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1) f) - K.adjoint g) :=
        operatorFunctional_eq_toDual_operatorForm K g α f

/-- Example 2.36. The Fréchet derivative of the Hilbert-space Tikhonov
functional is the Riesz functional represented by the operator-form gradient. -/
theorem tikhonovFunctional_fderiv_eq_toDual_operatorForm
    (K : H1 →L[ℝ] H2) (g : H2) (α : ℝ) (f : H1) :
    fderiv ℝ (K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α) f =
      (InnerProductSpace.toDual ℝ H1)
        (((K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1) f) - K.adjoint g) := by
  -- Rewrite the computed derivative into the operator-form Riesz functional.
  calc
    fderiv ℝ (K.tikhonovFunctional ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ H1) g α) f
      = ((innerSL ℝ (K f - g)).comp K + α • innerSL ℝ f) :=
        (tikhonovFunctional_hasFDerivAt K g α f).fderiv
    _ = (InnerProductSpace.toDual ℝ H1)
          (((K.adjoint.comp K + α • ContinuousLinearMap.id ℝ H1) f) - K.adjoint g) :=
        operatorFunctional_eq_toDual_operatorForm K g α f

/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Algorithm_2_1.Iteration

public section

open scoped NNReal

namespace LALM

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- The model-descent constant determined by the regularity bounds and candidate
parameters. -/
@[expose] noncomputable def modelConstant (h : EqualityConstrained.Regularity f c)
    (delta rho multiplierBound : ℝ) : ℝ :=
  h.gradientLipschitz / 2 + linearizationConstant h *
    (3 * multiplierBound + rho * h.constraintGradientBound * delta) +
    (rho / 2) * linearizationConstant h ^ 2 * delta ^ 2

/-- The model constant has its defining explicit formula. -/
theorem modelConstant_def (h : EqualityConstrained.Regularity f c)
    (delta rho multiplierBound : ℝ) :
    modelConstant h delta rho multiplierBound =
      h.gradientLipschitz / 2 + linearizationConstant h *
        (3 * multiplierBound + rho * h.constraintGradientBound * delta) +
        (rho / 2) * linearizationConstant h ^ 2 * delta ^ 2 := rfl

/-- The primal-step constant determined by the proximal and penalty parameters. -/
@[expose] noncomputable def primalConstant (h : EqualityConstrained.Regularity f c)
    (delta beta rho : ℝ) : ℝ :=
  beta + rho * h.constraintGradientBound * linearizationConstant h * delta

/-- The primal-step constant has its defining explicit formula. -/
theorem primalConstant_def (h : EqualityConstrained.Regularity f c)
    (delta beta rho : ℝ) :
    primalConstant h delta beta rho =
      beta + rho * h.constraintGradientBound * linearizationConstant h * delta := rfl

/-- The comparison constant augments the primal-step constant by the objective and
constraint regularity terms. -/
@[expose] noncomputable def primalComparisonConstant (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) : ℝ :=
  primalConstant h delta beta rho + h.gradientLipschitz +
    h.constraintGradientLipschitz * multiplierBound

/-- The primal comparison constant has its defining explicit formula. -/
theorem primalComparisonConstant_def (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) :
    primalComparisonConstant h delta beta rho multiplierBound =
      primalConstant h delta beta rho + h.gradientLipschitz +
        h.constraintGradientLipschitz * multiplierBound := rfl

/-- The multiplier-primal comparison constant determined by the LICQ modulus. -/
@[expose] noncomputable def multiplierPrimalConstant (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) : ℝ :=
  (4 / h.licqModulus ^ 2) *
    max ((primalConstant h delta beta rho) ^ 2)
      ((primalComparisonConstant h delta beta rho multiplierBound) ^ 2)

/-- The multiplier-primal constant has its defining explicit formula. -/
theorem multiplierPrimalConstant_def (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : ℝ) :
    multiplierPrimalConstant h delta beta rho multiplierBound =
      (4 / h.licqModulus ^ 2) *
        max ((primalConstant h delta beta rho) ^ 2)
          ((primalComparisonConstant h delta beta rho multiplierBound) ^ 2) := rfl

/-- Positive scalar NR-LALM parameters satisfying the initialization-independent
admissibility bounds. -/
structure AdmissibleParameters (h : EqualityConstrained.Regularity f c) where
  /-- The candidate step-radius parameter. -/
  delta : NNRealˣ
  /-- The candidate proximal parameter. -/
  beta : NNRealˣ
  /-- The candidate penalty parameter. -/
  rho : NNRealˣ
  /-- The candidate uniform multiplier bound. -/
  multiplierBound : NNRealˣ
  /-- The multiplier bound dominates the regularity and parameter expression. -/
  parameterBound_le :
    ((h.gradientBound + beta * delta +
      rho * h.constraintGradientBound * linearizationConstant h * delta ^ 2) /
        h.licqModulus : ℝ) ≤ multiplierBound
  /-- The step-radius parameter dominates its required comparison expression. -/
  comparisonBound_le :
    (h.gradientBound / beta +
      3 * h.constraintGradientBound * multiplierBound /
        (beta + rho * h.licqModulus ^ 2) : ℝ) ≤ delta
  /-- The model constant is at most three eighths of the proximal parameter. -/
  modelConstant_le : modelConstant h delta rho multiplierBound ≤ 3 * beta / 8
  /-- The penalty parameter dominates the multiplier-primal constant. -/
  multiplierPrimalConstant_le :
    8 * multiplierPrimalConstant h delta beta rho multiplierBound / beta ≤ rho

namespace AdmissibleParameters

/-- Construct an admissible scalar-parameter certificate from structured positive
values and proofs of the four source inequalities. -/
def ofValues (h : EqualityConstrained.Regularity f c)
    (delta beta rho multiplierBound : NNRealˣ)
    (parameterBound_le :
      ((h.gradientBound + beta * delta +
        rho * h.constraintGradientBound * linearizationConstant h * delta ^ 2) /
          h.licqModulus : ℝ) ≤ multiplierBound)
    (comparisonBound_le :
      (h.gradientBound / beta +
        3 * h.constraintGradientBound * multiplierBound /
          (beta + rho * h.licqModulus ^ 2) : ℝ) ≤ delta)
    (modelConstant_le : modelConstant h delta rho multiplierBound ≤ 3 * beta / 8)
    (multiplierPrimalConstant_le :
      8 * multiplierPrimalConstant h delta beta rho multiplierBound / beta ≤ rho) :
    AdmissibleParameters h :=
  { delta
    beta
    rho
    multiplierBound
    parameterBound_le
    comparisonBound_le
    modelConstant_le
    multiplierPrimalConstant_le }

/-- The four positive parameters viewed in the real scalar domain used by the
algorithm and its asymptotic statements. -/
@[expose] def values (params : AdmissibleParameters h) : ℝ × ℝ × ℝ × ℝ :=
  (params.delta, params.beta, params.rho, params.multiplierBound)

/-- The real-coordinate view lists the step radius, proximal parameter, penalty,
and multiplier bound in that order. -/
theorem values_def (params : AdmissibleParameters h) :
    params.values =
      ((params.delta : ℝ), (params.beta : ℝ), (params.rho : ℝ),
        (params.multiplierBound : ℝ)) := rfl

/-- Assumption 2.3: an admissible scalar-parameter certificate exposes positivity
and the four initialization-independent inequalities. -/
theorem spec (params : AdmissibleParameters h) :
    ((0 : ℝ) < params.delta ∧ (0 : ℝ) < params.beta ∧
      (0 : ℝ) < params.rho ∧ (0 : ℝ) < params.multiplierBound) ∧
    (((h.gradientBound + params.beta * params.delta +
      params.rho * h.constraintGradientBound * linearizationConstant h *
        params.delta ^ 2) / h.licqModulus : ℝ) ≤ params.multiplierBound ∧
      (h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * h.licqModulus ^ 2) : ℝ) ≤ params.delta ∧
      modelConstant h params.delta params.rho params.multiplierBound ≤
        3 * params.beta / 8 ∧
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound / params.beta ≤ params.rho) := by
  -- Each unit-valued parameter is nonzero, hence strictly positive as an NNReal and as a real.
  constructor
  · constructor
    · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 params.delta.ne_zero)
    · constructor
      · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 params.beta.ne_zero)
      · constructor
        · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 params.rho.ne_zero)
        · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 params.multiplierBound.ne_zero)
  -- The remaining conjuncts are precisely the four inequalities stored in the certificate.
  · constructor
    · exact params.parameterBound_le
    · constructor
      · exact params.comparisonBound_le
      · constructor
        · exact params.modelConstant_le
        · exact params.multiplierPrimalConstant_le

end AdmissibleParameters

/-- A chosen set of admissible NR-LALM parameters together with the two bounds imposed
by the initialization data. -/
structure Parameters (h : EqualityConstrained.Regularity f c)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (multiplier₀ : EuclideanSpace ℝ (Fin m)) extends AdmissibleParameters h where
  /-- The initial multiplier obeys the chosen multiplier bound. -/
  norm_multiplier₀_le : ‖multiplier₀‖ ≤ multiplierBound
  /-- The scaled initial constraint residual obeys the chosen multiplier bound. -/
  initialResidual_le : rho * ‖c x₀‖ ≤ multiplierBound

namespace Parameters

/-- Add the two initialization inequalities to an admissible scalar-parameter
certificate. -/
def ofAdmissible (h : EqualityConstrained.Regularity f c)
    (x₀ : EuclideanSpace ℝ (Fin n)) (multiplier₀ : EuclideanSpace ℝ (Fin m))
    (params : AdmissibleParameters h)
    (norm_multiplier₀_le : ‖multiplier₀‖ ≤ params.multiplierBound)
    (initialResidual_le : params.rho * ‖c x₀‖ ≤ params.multiplierBound) :
    Parameters h x₀ multiplier₀ :=
  { toAdmissibleParameters := params
    norm_multiplier₀_le
    initialResidual_le }

/-- An admissible parameter certificate exposes exactly the positivity, parameter,
and initialization conditions of the source assumption. -/
theorem spec {h : EqualityConstrained.Regularity f c}
    {x₀ : EuclideanSpace ℝ (Fin n)} {multiplier₀ : EuclideanSpace ℝ (Fin m)}
    (params : Parameters h x₀ multiplier₀) :
    ((0 : ℝ) < params.delta ∧ (0 : ℝ) < params.beta ∧
      (0 : ℝ) < params.rho ∧ (0 : ℝ) < params.multiplierBound) ∧
    (((h.gradientBound + params.beta * params.delta +
      params.rho * h.constraintGradientBound * linearizationConstant h *
        params.delta ^ 2) / h.licqModulus : ℝ) ≤ params.multiplierBound ∧
      (h.gradientBound / params.beta +
        3 * h.constraintGradientBound * params.multiplierBound /
          (params.beta + params.rho * h.licqModulus ^ 2) : ℝ) ≤ params.delta ∧
      modelConstant h params.delta params.rho params.multiplierBound ≤
        3 * params.beta / 8 ∧
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound / params.beta ≤ params.rho) ∧
    (‖multiplier₀‖ ≤ params.multiplierBound ∧
      params.rho * ‖c x₀‖ ≤ params.multiplierBound) :=
  ⟨params.toAdmissibleParameters.spec.1,
    ⟨params.toAdmissibleParameters.spec.2,
      ⟨params.norm_multiplier₀_le, params.initialResidual_le⟩⟩⟩

end Parameters

end LALM

end

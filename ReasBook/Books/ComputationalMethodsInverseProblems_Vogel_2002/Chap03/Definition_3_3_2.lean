/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_7
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3_1.QuadraticModel
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace Newton

universe u

variable {H : Type u} [NormedAddCommGroup H]

/-- Helper for Definition 3.3-extra-2: the multiplier activity clause from the
trust-region update formula `(3.22)`. -/
def IsTrustRegionMultiplierActive (s_v : H) (Δ_v γ_v : ℝ) : Prop :=
  (‖s_v‖ < Δ_v → γ_v = 0) ∧ (Δ_v ≤ ‖s_v‖ → 0 < γ_v)

/-- Helper for Definition 3.3-extra-2: `Newton.IsTrustRegionMultiplierActive`
is already presented in its exposed normal form. -/
theorem isTrustRegionMultiplierActive_iff (s_v : H) (Δ_v γ_v : ℝ) :
    IsTrustRegionMultiplierActive s_v Δ_v γ_v ↔
      (‖s_v‖ < Δ_v → γ_v = 0) ∧ (Δ_v ≤ ‖s_v‖ → 0 < γ_v) :=
  Iff.rfl

namespace IsTrustRegionMultiplierActive

/-- Helper for Definition 3.3-extra-2: if the trust-region step stays strictly
inside the ball, the multiplier vanishes. -/
theorem eq_zero_of_norm_lt {s_v : H} {Δ_v γ_v : ℝ}
    (hActive : IsTrustRegionMultiplierActive s_v Δ_v γ_v) (hs : ‖s_v‖ < Δ_v) :
    γ_v = 0 :=
  hActive.1 hs

/-- Helper for Definition 3.3-extra-2: if the trust-region step reaches the
radius, the multiplier is positive. -/
theorem pos_of_le_norm {s_v : H} {Δ_v γ_v : ℝ}
    (hActive : IsTrustRegionMultiplierActive s_v Δ_v γ_v) (hs : Δ_v ≤ ‖s_v‖) :
    0 < γ_v :=
  hActive.2 hs

end IsTrustRegionMultiplierActive

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Definition 3.3-extra-2: `IsTrustRegionStep J f_v s_v Δ_v` means
that `Δ_v` is positive and `s_v` minimizes the Newton quadratic model on the
closed trust-region ball of radius `Δ_v` centered at `0`. -/
def IsTrustRegionStep (J : H → ℝ) (f_v s_v : H) (Δ_v : ℝ) : Prop :=
  0 < Δ_v ∧ IsMinOn (Newton.quadraticModel J f_v) (Metric.closedBall (0 : H) Δ_v) s_v

/-- Helper for Definition 3.3-extra-2: `Newton.IsTrustRegionStep` is exactly
its source-facing defining conjunction. -/
theorem isTrustRegionStep_iff (J : H → ℝ) (f_v s_v : H) (Δ_v : ℝ) :
    IsTrustRegionStep J f_v s_v Δ_v ↔
      0 < Δ_v ∧ IsMinOn (Newton.quadraticModel J f_v) (Metric.closedBall (0 : H) Δ_v) s_v := by
  -- This theorem is exactly the exposed normal form of the predicate definition.
  rfl

/-- Helper for Definition 3.3-extra-2: the regularized trust-region operator
`hessian J f_v + γ_v • id`. -/
def regularizedOperator (J : H → ℝ) (f_v : H) (γ_v : ℝ) : H →L[ℝ] H :=
  hessian J f_v + γ_v • ContinuousLinearMap.id ℝ H

/-- Helper for Definition 3.3-extra-2: applying the regularized operator adds
the shifted identity term `γ_v • s`. -/
theorem regularizedOperator_apply (J : H → ℝ) (f_v s : H) (γ_v : ℝ) :
    regularizedOperator J f_v γ_v s = hessian J f_v s + γ_v • s := by
  simp [regularizedOperator]

/-- Helper for Definition 3.3-extra-2: the regularized trust-region step
obtained by applying the inverse of the regularized operator to the gradient. -/
def regularizedStep (J : H → ℝ) (f_v : H) (γ_v : ℝ)
    (hReg : OperatorEquation.WellPosed (regularizedOperator J f_v γ_v)) : H :=
  hReg.inverse (gradient J f_v)

/-- Helper for Definition 3.3-extra-2: defining equation for
`Newton.regularizedStep`. -/
theorem regularizedStep_def (J : H → ℝ) (f_v : H) (γ_v : ℝ)
    (hReg : OperatorEquation.WellPosed (regularizedOperator J f_v γ_v)) :
    regularizedStep J f_v γ_v hReg = hReg.inverse (gradient J f_v) := by
  -- This proof just unfolds the wrapper around the well-posed inverse.
  rfl

/-- Helper for Definition 3.3-extra-2: the regularized Newton step satisfies
the shifted Hessian equation. -/
theorem regularizedOperator_regularizedStep (J : H → ℝ) (f_v : H) (γ_v : ℝ)
    (hReg : OperatorEquation.WellPosed (regularizedOperator J f_v γ_v)) :
    regularizedOperator J f_v γ_v (regularizedStep J f_v γ_v hReg) = gradient J f_v := by
  rw [regularizedStep_def]
  exact hReg.apply_inverse (gradient J f_v)

/-- Helper for Definition 3.3-extra-2: the trust-region Newton update obtained
by subtracting the regularized step from the current iterate `f_v`. -/
def trustRegionNextIterate (J : H → ℝ) (f_v : H) (γ_v : ℝ)
    (hReg : OperatorEquation.WellPosed (regularizedOperator J f_v γ_v)) : H :=
  f_v - regularizedStep J f_v γ_v hReg

/-- Helper for Definition 3.3-extra-2: defining equation for
`Newton.trustRegionNextIterate`. -/
theorem trustRegionNextIterate_def (J : H → ℝ) (f_v : H) (γ_v : ℝ)
    (hReg : OperatorEquation.WellPosed (regularizedOperator J f_v γ_v)) :
    trustRegionNextIterate J f_v γ_v hReg = f_v - regularizedStep J f_v γ_v hReg := by
  -- This theorem exposes the iterate constructor in its source-facing form.
  rfl

/-- Helper for Definition 3.3-extra-2: `IsTrustRegionNextIterate J f_v f_next
s_v Δ_v γ_v` packages the source update statement `(3.22)`. -/
def IsTrustRegionNextIterate
    (J : H → ℝ) (f_v f_next s_v : H) (Δ_v γ_v : ℝ) : Prop :=
  f_next = f_v - s_v ∧
    regularizedOperator J f_v γ_v s_v = gradient J f_v ∧
    IsTrustRegionMultiplierActive s_v Δ_v γ_v

/-- Helper for Definition 3.3-extra-2: `Newton.IsTrustRegionNextIterate` is
already given in its exposed source-facing normal form. -/
theorem isTrustRegionNextIterate_iff
    (J : H → ℝ) (f_v f_next s_v : H) (Δ_v γ_v : ℝ) :
    IsTrustRegionNextIterate J f_v f_next s_v Δ_v γ_v ↔
      f_next = f_v - s_v ∧
        regularizedOperator J f_v γ_v s_v = gradient J f_v ∧
        IsTrustRegionMultiplierActive s_v Δ_v γ_v :=
  Iff.rfl

namespace IsTrustRegionNextIterate

/-- Helper for Definition 3.3-extra-2: a trust-region next iterate is obtained
by subtracting the step. -/
theorem eq_sub {J : H → ℝ} {f_v f_next s_v : H} {Δ_v γ_v : ℝ}
    (hNext : IsTrustRegionNextIterate J f_v f_next s_v Δ_v γ_v) :
    f_next = f_v - s_v :=
  hNext.1

/-- Helper for Definition 3.3-extra-2: a trust-region next iterate satisfies
the regularized Newton equation. -/
theorem regularizedEquation {J : H → ℝ} {f_v f_next s_v : H} {Δ_v γ_v : ℝ}
    (hNext : IsTrustRegionNextIterate J f_v f_next s_v Δ_v γ_v) :
    regularizedOperator J f_v γ_v s_v = gradient J f_v :=
  hNext.2.1

/-- Helper for Definition 3.3-extra-2: a trust-region next iterate satisfies
the multiplier activity clause. -/
theorem activity {J : H → ℝ} {f_v f_next s_v : H} {Δ_v γ_v : ℝ}
    (hNext : IsTrustRegionNextIterate J f_v f_next s_v Δ_v γ_v) :
    IsTrustRegionMultiplierActive s_v Δ_v γ_v :=
  hNext.2.2

end IsTrustRegionNextIterate

/-- Helper for Definition 3.3-extra-2: the step from `f_v` to
`Newton.trustRegionNextIterate J f_v γ_v hReg` is the regularized Newton step. -/
theorem sub_trustRegionNextIterate (J : H → ℝ) (f_v : H) (γ_v : ℝ)
    (hReg : OperatorEquation.WellPosed (regularizedOperator J f_v γ_v)) :
    f_v - trustRegionNextIterate J f_v γ_v hReg = regularizedStep J f_v γ_v hReg := by
  rw [trustRegionNextIterate_def]
  simp

/-- Helper for Definition 3.3-extra-2: the canonical iterate satisfies the
regularized Newton equation from the source formulation `(3.22)`. -/
theorem regularizedEquation_trustRegionNextIterate (J : H → ℝ) (f_v : H) (γ_v : ℝ)
    (hReg : OperatorEquation.WellPosed (regularizedOperator J f_v γ_v)) :
    regularizedOperator J f_v γ_v (f_v - trustRegionNextIterate J f_v γ_v hReg) =
      gradient J f_v := by
  simpa [sub_trustRegionNextIterate] using
    regularizedOperator_regularizedStep J f_v γ_v hReg

/-- Definition 3.3-extra-2: the canonical trust-region iterate
`Newton.trustRegionNextIterate J f_v γ_v hReg` satisfies the source update
formula `(3.22)` exactly when the multiplier activity clause holds for the
regularized step. -/
theorem trustRegionNextIterate_spec (J : H → ℝ) (f_v : H) (Δ_v γ_v : ℝ)
    (hReg : OperatorEquation.WellPosed (regularizedOperator J f_v γ_v)) :
    IsTrustRegionNextIterate J f_v (trustRegionNextIterate J f_v γ_v hReg)
        (regularizedStep J f_v γ_v hReg) Δ_v γ_v ↔
      IsTrustRegionMultiplierActive (regularizedStep J f_v γ_v hReg) Δ_v γ_v := by
  constructor
  · intro hNext
    exact hNext.activity
  · intro hActivity
    refine ⟨?_, ?_, hActivity⟩
    · rw [trustRegionNextIterate_def]
    · exact regularizedOperator_regularizedStep J f_v γ_v hReg

end Newton

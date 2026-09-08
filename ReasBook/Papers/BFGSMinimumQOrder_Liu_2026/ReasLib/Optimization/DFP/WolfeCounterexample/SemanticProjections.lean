module

public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedIdentityInitialization
public import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Semantic projections for the DFP counterexample certificates

These lemmas expose the formulations used in the paper.  In particular,
convergence to a positive limit gives a positive `liminf`, while an eventual
positive lower bound alone is paired with an eventual upper bound before using
the conditionally-complete real-valued `liminf`.
-/

public section

noncomputable section

open Filter
open scoped Topology InnerProduct

namespace DFP

/-- Helper for TASK-15: a sequence with an eventual positive lower bound and an
eventual finite upper bound has strictly positive real `liminf`. -/
theorem positive_liminf_of_eventually_lower_upper
    {u : ℕ → ℝ} {δ B : ℝ} (hδ : 0 < δ)
    (hLower : ∀ᶠ k in atTop, δ ≤ u k)
    (hUpper : ∀ᶠ k in atTop, u k ≤ B) :
    0 < liminf u atTop := by
  have hCobounded : IsCoboundedUnder (· ≥ ·) atTop u :=
    isCoboundedUnder_ge_of_eventually_le atTop hUpper
  have hδLiminf : δ ≤ liminf u atTop :=
    le_liminf_of_le hCobounded hLower
  exact lt_of_lt_of_le hδ hδLiminf

/-- Helper for TASK-15: convergence of a real sequence to a positive value identifies its
`liminf` with that value and hence makes the `liminf` positive. -/
theorem positive_liminf_of_tendsto
    {u : ℕ → ℝ} {L : ℝ} (hL : 0 < L)
    (hTendsto : Tendsto u atTop (𝓝 L)) :
    0 < liminf u atTop := by
  rw [hTendsto.liminf_eq]
  exact hL

/-- Helper for TASK-15: uniform lower and upper Loewner bounds on a Hessian force the lower scalar
bound to be no larger than the upper scalar bound on a nontrivial space. -/
theorem hessianBounds_lower_le_upper
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Nontrivial E] {m M : ℝ} {f : E → ℝ}
    (hBounds : HasHessianBounds m M f) : m ≤ M := by
  obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := exists_ne (0 : E)
  have hOrder : m • (1 : E →L[ℝ] E) ≤ M • (1 : E →L[ℝ] E) := by
    exact hBounds.at 0 |>.lower.trans (hBounds.at 0).upper
  have hQuadratic := (ContinuousLinearMap.le_def _ _).mp hOrder |>.inner_nonneg_left v
  have hScalar : m * ‖v‖ ^ 2 ≤ M * ‖v‖ ^ 2 := by
    have hNonnegative : 0 ≤ M * ‖v‖ ^ 2 - m * ‖v‖ ^ 2 := by
      simpa only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq] using hQuadratic
    linarith
  have hNorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  nlinarith

/-- Helper for TASK-15: a weak-Wolfe counterexample's positive gradient limit is the paper-facing
strictly positive `liminf` statement. -/
theorem WolfeCounterexample.gradientNorm_liminf_pos
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : WolfeCounterexample (Fin n) m M c₁ c₂) :
    0 < liminf
      (fun k ↦ ‖gradients c.iteration.objective c.iteration.point k‖) atTop := by
  exact positive_liminf_of_tendsto c.gradientLimitPos c.gradientNormTendsto

/-- Helper for TASK-15: a strong-Wolfe counterexample inherits the positive gradient `liminf` of
its weak-Wolfe projection. -/
theorem StrongWolfeCounterexample.gradientNorm_liminf_pos
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : StrongWolfeCounterexample (Fin n) m M c₁ c₂) :
    0 < liminf
      (fun k ↦ ‖gradients c.iteration.objective c.iteration.point k‖) atTop := by
  exact c.toWolfeCounterexample.gradientNorm_liminf_pos

/-- Helper for TASK-15: the nonzero secant denominator in a classical inverse iteration rules out a
zero gradient at every iteration index. -/
theorem WolfeCounterexample.gradient_ne_zero
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : WolfeCounterexample (Fin n) m M c₁ c₂) (k : ℕ) :
    gradients c.iteration.objective c.iteration.point k ≠ 0 := by
  intro hzero
  apply c.iteration.secantDenominatorNe k
  rw [DFP.steps_apply, DFP.directions_apply, hzero]
  simp

/-- Helper for TASK-15: a strong-Wolfe counterexample inherits the nonzero-gradient projection of
its underlying classical inverse iteration. -/
theorem StrongWolfeCounterexample.gradient_ne_zero
    {n : ℕ} {m M c₁ c₂ : ℝ}
    (c : StrongWolfeCounterexample (Fin n) m M c₁ c₂) (k : ℕ) :
    gradients c.iteration.objective c.iteration.point k ≠ 0 := by
  exact c.toWolfeCounterexample.gradient_ne_zero k

end DFP

namespace DFP.WolfeCounterexample

/-- Helper for TASK-15: an identity-initialized operator certificate has a positive gradient
`liminf` once its recorded eventual lower bound is supplemented by an
eventual finite upper bound.  The extra hypothesis is explicit because a
conditionally complete real `liminf` is not determined by a lower bound alone.
-/
theorem IdentityInitializedOperatorCertificate.gradientNorm_liminf_pos_of_eventually_upper
    {ι : Type u} [Fintype ι] {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedOperatorCertificate ι m M c₁ c₂)
    (hUpper : ∃ B : ℝ, ∀ᶠ k in atTop, ‖c.gradient k‖ ≤ B) :
    0 < liminf (fun k ↦ ‖c.gradient k‖) atTop := by
  obtain ⟨δ, hδ, hLower⟩ := c.gradientNormEventuallyPositive
  obtain ⟨B, hUpperB⟩ := hUpper
  exact DFP.positive_liminf_of_eventually_lower_upper hδ hLower hUpperB

/-- Helper for TASK-15: an identity-initialized operator certificate whose transformed gradient norm
is known to converge has the paper-facing positive `liminf` conclusion. -/
theorem IdentityInitializedOperatorCertificate.gradientNorm_liminf_pos_of_tendsto
    {ι : Type u} [Fintype ι] {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedOperatorCertificate ι m M c₁ c₂)
    {L : ℝ}
    (hL : 0 < L)
    (hTendsto : Tendsto (fun k ↦ ‖c.gradient k‖) atTop (𝓝 L)) :
    0 < liminf (fun k ↦ ‖c.gradient k‖) atTop :=
  DFP.positive_liminf_of_tendsto hL hTendsto

/-- Helper for TASK-15: a strong identity-initialized operator certificate has the same semantic
`liminf` projection, under the explicit eventual upper bound required by the
real-valued liminf construction. -/
theorem IdentityInitializedStrongWolfeOperatorCertificate.gradientNorm_liminf_pos_of_eventually_upper
    {ι : Type u} [Fintype ι] {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate ι m M c₁ c₂)
    (hUpper : ∃ B : ℝ, ∀ᶠ k in atTop, ‖c.gradient k‖ ≤ B) :
    0 < liminf (fun k ↦ ‖c.gradient k‖) atTop := by
  exact IdentityInitializedOperatorCertificate.gradientNorm_liminf_pos_of_eventually_upper
    c.toIdentityInitializedOperatorCertificate hUpper

/-- Helper for TASK-15: the strong identity-initialized operator certificate has the same `liminf`
projection when its transformed gradient norm is supplied with a positive
limit. -/
theorem IdentityInitializedStrongWolfeOperatorCertificate.gradientNorm_liminf_pos_of_tendsto
    {ι : Type u} [Fintype ι] {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate ι m M c₁ c₂)
    {L : ℝ}
    (hL : 0 < L)
    (hTendsto : Tendsto (fun k ↦ ‖c.gradient k‖) atTop (𝓝 L)) :
    0 < liminf (fun k ↦ ‖c.gradient k‖) atTop :=
  IdentityInitializedOperatorCertificate.gradientNorm_liminf_pos_of_tendsto
    c.toIdentityInitializedOperatorCertificate hL hTendsto

/-- Helper for TASK-15: the identity-initialized operator certificate exposes its exact initial
inverse-Hessian identity as a direct semantic projection. -/
theorem IdentityInitializedOperatorCertificate.initialInverseHessian_is_identity
    {ι : Type u} [Fintype ι] {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedOperatorCertificate ι m M c₁ c₂) :
    c.inverseHessian 0 = 1 :=
  c.initialInverseHessian_eq_one

/-- Helper for TASK-15: the strong identity-initialized certificate preserves the exact initial
inverse-Hessian identity from its underlying operator certificate. -/
theorem IdentityInitializedStrongWolfeOperatorCertificate.initialInverseHessian_is_identity
    {ι : Type u} [Fintype ι] {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedStrongWolfeOperatorCertificate ι m M c₁ c₂) :
    c.inverseHessian 0 = 1 :=
  c.toIdentityInitializedOperatorCertificate.initialInverseHessian_eq_one

/-- Helper for TASK-15: positive Hessian bounds and the nontrivial Euclidean state space give the
paper's ordered parameter statement `0 < m ≤ M`. -/
theorem hessianBounds_pos_le
    {ι : Type u} [Fintype ι] [Nontrivial (EuclideanSpace ℝ ι)]
    {m M c₁ c₂ : ℝ}
    (c : IdentityInitializedOperatorCertificate ι m M c₁ c₂)
    (hm : 0 < m) : 0 < m ∧ m ≤ M := by
  exact ⟨hm, DFP.hessianBounds_lower_le_upper c.hessianBounds⟩

end DFP.WolfeCounterexample

end

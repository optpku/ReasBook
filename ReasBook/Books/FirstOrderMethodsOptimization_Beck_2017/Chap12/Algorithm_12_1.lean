/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open scoped Gradient

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Algorithm 12.1 is `source-facing` in the chapter's dual proximal-gradient API.

Domain sampling against the nearby project owners identifies:
- `proximal_gradient_step` and `is_proximal_gradient_trajectory` from Chapter 10 as the
  `core/canonical` owners for the generic proximal-gradient step and trajectory;
- `prox[...]` from Chapter 6 as the canonical owner for the underlying proximal step;
- `PosReal` from Chapter 6 as the positive stepsize owner;
- the operator norm on `ContinuousLinearMap` as the canonical source of the bound
  `L_F = ‖A‖² / σ`.

Since the source algorithm specifies an initialization `y^0`, a constant admissible parameter
`L ≥ L_F`, and the usual proximal-gradient recursion for the dual objective `F + G`, the clean
public API is a thin source-facing specialization of the Chapter 10 trajectory owner together with
the small subtype of admissible constant stepsizes. The one-step owner below keeps an explicit map
parameter only as a helper layer for Chapter 12 bridge statements; the main labeled trajectory
owner reuses the canonical Chapter 10 proximal-gradient surface directly. -/

-- Semantic search note: `lean_leansearch` confirmed `gradient` as the canonical owner for the
-- explicit dual smooth term, and the surrounding owner/API choice was then verified against the
-- local Chapter 6 and Chapter 10 declarations.

/-- The dual smoothness bound `L_F = ‖A‖² / σ` attached to the dual representation. -/
def dual_based_proximal_gradient_dual_lipschitz_constant
    (A : E →L[ℝ] V) (σ : PosReal) : ℝ :=
  ‖A‖ ^ (2 : ℕ) / (σ : ℝ)

-- Proof sketch: unfold `dual_based_proximal_gradient_dual_lipschitz_constant`; the displayed
-- scalar is exactly the textbook bound `‖A‖² / σ`.
/-- Expanding the dual smoothness bound gives the textbook value `‖A‖² / σ`. -/
theorem dual_based_proximal_gradient_dual_lipschitz_constant_eq
    (A : E →L[ℝ] V) (σ : PosReal) :
    dual_based_proximal_gradient_dual_lipschitz_constant A σ =
      ‖A‖ ^ (2 : ℕ) / (σ : ℝ) :=
  rfl

/-- An admissible constant parameter for the dual proximal-gradient method is a positive real
`L` satisfying the textbook lower bound `L_F = ‖A‖² / σ ≤ L`. -/
abbrev DualBasedProximalGradientDualStepsizeParameter
    (A : E →L[ℝ] V) (σ : PosReal) :=
  { L : PosReal // dual_based_proximal_gradient_dual_lipschitz_constant A σ ≤ (L : ℝ) }

namespace DualBasedProximalGradientDualStepsizeParameter

-- Proof sketch: the subtype condition in
-- `DualBasedProximalGradientDualStepsizeParameter A σ` is exactly the required lower bound.
/-- Every admissible dual proximal-gradient parameter satisfies `‖A‖² / σ ≤ L`. -/
theorem lower_bound
    {A : E →L[ℝ] V} {σ : PosReal}
    (L : DualBasedProximalGradientDualStepsizeParameter A σ) :
    dual_based_proximal_gradient_dual_lipschitz_constant A σ ≤ (L : ℝ) :=
  L.2

end DualBasedProximalGradientDualStepsizeParameter

/-- The admissible next dual iterates from `y^k` are the proximal points of `(1 / L) G` at the
forward-gradient point `y^k - (1 / L) gradF(y^k)`, where `gradF` represents the gradient of the
smooth term `F`. -/
def dual_based_proximal_gradient_dual_step
    (G : V → EReal) (gradF : V → V) (L : PosReal) (yk : V) : Set V :=
  prox[((((1 / L : PosReal) : EReal) • G))] (yk - (1 / L : ℝ) • gradF yk)

-- Proof sketch: unfold `dual_based_proximal_gradient_dual_step`; membership is definitionally
-- proximal-set membership for the scaled nonsmooth term at the forward-gradient point.
/-- A point belongs to the dual proximal-gradient step set exactly when it is a proximal point of
`(1 / L) G` at `y^k - (1 / L) gradF(y^k)`. -/
@[simp] theorem mem_dual_based_proximal_gradient_dual_step_iff
    {G : V → EReal} {gradF : V → V} {L : PosReal} {yk yNext : V} :
    yNext ∈ dual_based_proximal_gradient_dual_step G gradF L yk ↔
      yNext ∈ prox[((((1 / L : PosReal) : EReal) • G))]
        (yk - (1 / L : ℝ) • gradF yk) :=
  Iff.rfl

/-- Algorithm 12.1: given an initial point `y^0 = y0` and a constant admissible parameter
`L ≥ ‖A‖² / σ`, a sequence `y` is a dual proximal-gradient trajectory for the dual representation
for the dual objective `F + G` when it starts at `y0` and follows the canonical proximal-gradient
trajectory for `F + G` with the constant parameter `L`. -/
class is_dual_based_proximal_gradient_dual_trajectory
    (F G : V → EReal) [InnerProductSpace ℝ V] [CompleteSpace V]
    {A : E →L[ℝ] V} {σ : PosReal}
    (L : DualBasedProximalGradientDualStepsizeParameter A σ)
    (y : ℕ → V) (y0 : V) : Prop where
  zero_eq : y 0 = y0
  trajectory : is_proximal_gradient_trajectory F G y (fun _ ↦ (L : PosReal))

-- Proof sketch: extract the initialization equation from the first conjunct of
-- `is_dual_based_proximal_gradient_dual_trajectory`.
/-- A dual proximal-gradient trajectory starts from the prescribed initial point `y^0 = y0`. -/
theorem is_dual_based_proximal_gradient_dual_trajectory_zero
    {F G : V → EReal} [InnerProductSpace ℝ V] [CompleteSpace V]
    {A : E →L[ℝ] V} {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A σ}
    {y : ℕ → V} {y0 : V}
    (h : is_dual_based_proximal_gradient_dual_trajectory F G L y y0) :
    y 0 = y0 :=
  h.zero_eq

-- Proof sketch: apply the Chapter 10 trajectory-step theorem to the stored canonical trajectory
-- field `h.trajectory`.
/-- At every iteration `k`, a dual proximal-gradient trajectory satisfies the Chapter 10
interior-domain condition and the constant-stepsize proximal-gradient update for `F + G`. -/
theorem is_dual_based_proximal_gradient_dual_trajectory_step
    {F G : V → EReal} [InnerProductSpace ℝ V] [CompleteSpace V]
    {A : E →L[ℝ] V} {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A σ}
    {y : ℕ → V} {y0 : V}
    (h : is_dual_based_proximal_gradient_dual_trajectory F G L y y0)
    (k : ℕ) :
    y k ∈ interior (effective_domain F) ∧
      y (k + 1) ∈ proximal_gradient_step F G (y k) (L : PosReal) :=
  h.trajectory k

end

section

variable {V : Type v}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

-- Proof sketch: unfold both step owners at the canonical gradient of `F`; the proximal-point
-- sets coincide definitionally.
/-- The Chapter 12 dual-step formula with the canonical gradient of `F` is exactly the Chapter 10
proximal-gradient step for the composite objective `F + G`. -/
theorem dual_based_proximal_gradient_dual_step_eq_proximal_gradient_step
    (F G : V → EReal) (L : PosReal)
    (yk : V) :
    dual_based_proximal_gradient_dual_step
        G
        (fun y : V ↦ ∇ (fun z : V ↦ (F z).toReal) y)
        L
        yk =
      proximal_gradient_step F G yk L :=
  rfl

-- Proof sketch: this is the canonical trajectory field stored in
-- `is_dual_based_proximal_gradient_dual_trajectory`.
/-- A Chapter 12 dual proximal-gradient trajectory is, by construction, the corresponding Chapter
10 proximal-gradient trajectory with constant parameter `L`. -/
theorem is_dual_based_proximal_gradient_dual_trajectory.toIsProximalGradientTrajectory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : V → EReal} {A : E →L[ℝ] V} {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A σ}
    {y : ℕ → V} {y0 : V}
    (h : is_dual_based_proximal_gradient_dual_trajectory F G L y y0) :
    is_proximal_gradient_trajectory F G y (fun _ ↦ (L : PosReal)) :=
  h.trajectory

end

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The reciprocal parameter `σ⁻¹` is an admissible dual proximal-gradient stepsize for the
identity map. -/
theorem dual_based_proximal_gradient_identity_stepsize_parameter_lower_bound
    (σ : PosReal) :
    dual_based_proximal_gradient_dual_lipschitz_constant
        (ContinuousLinearMap.id ℝ E) σ ≤ ((σ⁻¹ : PosReal) : ℝ) := by
  rw [dual_based_proximal_gradient_dual_lipschitz_constant_eq]
  have hid_norm_le : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have hid_sq_le : ‖ContinuousLinearMap.id ℝ E‖ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [norm_nonneg (ContinuousLinearMap.id ℝ E), hid_norm_le]
  have hσ : 0 < (σ : ℝ) := σ.2
  have hdiv : ‖ContinuousLinearMap.id ℝ E‖ ^ (2 : ℕ) / (σ : ℝ) ≤ 1 / (σ : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hid_sq_le (inv_nonneg.mpr hσ.le)
  simpa [one_div] using hdiv

/-- The canonical admissible dual proximal-gradient stepsize parameter for the identity map is
the reciprocal value `σ⁻¹`. -/
abbrev dual_based_proximal_gradient_identity_stepsize_parameter
    (σ : PosReal) :
    DualBasedProximalGradientDualStepsizeParameter
      (ContinuousLinearMap.id ℝ E) σ :=
  ⟨σ⁻¹, dual_based_proximal_gradient_identity_stepsize_parameter_lower_bound σ⟩

end

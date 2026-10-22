/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Algorithm_2_5_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_1_extra_1

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Layer triage:
-- * source-facing: `IsFeasiblePointArmijoStep`
-- * core/canonical reused from earlier project owners:
--   `IsFeasibleDescentDirection`, `armijoBacktrackingAccepts`
-- * bridge/view: `feasiblePointArmijoAccepts`, `isFeasiblePointArmijoStep_iff`

-- Domain sampling:
-- * primitive feasible-direction owner: `IsFeasibleDirectionAt`
-- * primitive descent-direction owner: `IsDescentDirectionAt`
-- * combined Chapter 11 owner: `IsFeasibleDescentDirection`
-- * canonical Chapter 2 Armijo owner: `armijoBacktrackingAccepts`

-- Semantic recall: Chapter 11 already owns the feasible-descent notion in
-- `Definition_11_1_extra_1`, while Chapter 2 already owns the Armijo sufficient-decrease
-- predicate `armijoBacktrackingAccepts`. This file keeps the Chapter 11 feasible-step predicate
-- only as the constrained bridge: feasibility of the trial point plus the canonical Chapter 2
-- Armijo test with gradient witness `gradient f xk`.

/-- The accepted-step condition in Definition 11.1-extra-2: the trial point is feasible and
satisfies the canonical Chapter 2 Armijo sufficient-decrease test along `d` at `xk`. -/
def feasiblePointArmijoAccepts
    (f : E → ℝ) (X : Set E)
    (c1 : ℝ) (xk d : E) (α : ℝ) : Prop :=
  xk + α • d ∈ X ∧
    armijoBacktrackingAccepts f c1 xk (gradient f xk : E) d α

/-- Unfolding `feasiblePointArmijoAccepts` recovers the Chapter 11 feasibility condition together
with the canonical Chapter 2 Armijo predicate. -/
theorem feasiblePointArmijoAccepts_iff
    (f : E → ℝ) (X : Set E)
    (c1 : ℝ) (xk d : E) (α : ℝ) :
    feasiblePointArmijoAccepts f X c1 xk d α ↔
      xk + α • d ∈ X ∧
        armijoBacktrackingAccepts f c1 xk (gradient f xk : E) d α :=
  Iff.rfl

/-- Expanding the canonical Chapter 2 Armijo owner recovers the explicit sufficient-decrease
inequality at the trial point. -/
theorem feasiblePointArmijoAccepts_iff_step_mem_and_armijo
    (f : E → ℝ) (X : Set E)
    (c1 : ℝ) (xk d : E) (α : ℝ) :
    feasiblePointArmijoAccepts f X c1 xk d α ↔
      xk + α • d ∈ X ∧
        f (xk + α • d) ≤ f xk + c1 * α * inner ℝ d (gradient f xk) := by
  rw [feasiblePointArmijoAccepts_iff]
  simp [armijoBacktrackingAccepts_iff, mul_assoc]

/-- Chapter11 Definition 11.1-extra-2: `α` is a feasible point Armijo step along `d` at `xk`
when `c1 ∈ (0, 1)`, `d` satisfies the feasible-descent conditions `(11.1.1)`-`(11.1.2)` at `xk`,
`α > 0`, the trial `α` is accepted by `feasiblePointArmijoAccepts`, and the doubled step
`2 * α` is not accepted. -/
class IsFeasiblePointArmijoStep
    (f : E → ℝ) (X : Set E)
    (xk d : E) (c1 α : ℝ) : Prop
    extends IsFeasibleDescentDirection f xk X d where
  c1_mem : c1 ∈ Set.Ioo (0 : ℝ) 1
  alpha_pos : 0 < α
  accepted : feasiblePointArmijoAccepts f X c1 xk d α
  double_not_accepted : ¬ feasiblePointArmijoAccepts f X c1 xk d (2 * α)

/-- `IsFeasiblePointArmijoStep f X xk d c1 α` is proposition-valued. -/
instance isFeasiblePointArmijoStepSubsingleton
    (f : E → ℝ) (X : Set E) (xk d : E) (c1 α : ℝ) :
    Subsingleton (IsFeasiblePointArmijoStep f X xk d c1 α) := inferInstance

/-- A feasible point Armijo step lands in `X`. -/
theorem IsFeasiblePointArmijoStep.step_mem
    {f : E → ℝ} {X : Set E} {xk d : E} {c1 α : ℝ}
    (h : IsFeasiblePointArmijoStep f X xk d c1 α) :
    xk + α • d ∈ X :=
  h.accepted.1

/-- A feasible point Armijo step satisfies the Armijo inequality at `α`. -/
theorem IsFeasiblePointArmijoStep.armijo
    {f : E → ℝ} {X : Set E} {xk d : E} {c1 α : ℝ}
    (h : IsFeasiblePointArmijoStep f X xk d c1 α) :
    f (xk + α • d) ≤ f xk + c1 * α * inner ℝ d (gradient f xk) := by
  simpa [armijoBacktrackingAccepts_iff, mul_assoc] using h.accepted.2

/-- If the doubled step is feasible, then its Armijo inequality fails strictly. -/
theorem IsFeasiblePointArmijoStep.maximal
    {f : E → ℝ} {X : Set E} {xk d : E} {c1 α : ℝ}
    (h : IsFeasiblePointArmijoStep f X xk d c1 α) :
    xk + (2 * α) • d ∈ X →
      f (xk + (2 * α) • d) > f xk + c1 * (2 * α) * inner ℝ d (gradient f xk) := by
  intro hdouble
  have hnot :
      ¬ f (xk + (2 * α) • d) ≤ f xk + c1 * (2 * α) * inner ℝ d (gradient f xk) := by
    intro harmijo
    have haccept :
        feasiblePointArmijoAccepts f X c1 xk d (2 * α) :=
      (feasiblePointArmijoAccepts_iff_step_mem_and_armijo f X c1 xk d (2 * α)).2
        ⟨hdouble, harmijo⟩
    exact h.double_not_accepted haccept
  exact lt_of_not_ge hnot

/-- Unfolding `IsFeasiblePointArmijoStep` recovers the Chapter 11 feasible-point Armijo
conditions. -/
theorem isFeasiblePointArmijoStep_iff
    {f : E → ℝ} {X : Set E} {xk d : E} {c1 α : ℝ} :
    IsFeasiblePointArmijoStep f X xk d c1 α ↔
      c1 ∈ Set.Ioo (0 : ℝ) 1 ∧
        IsFeasibleDescentDirection f xk X d ∧
          0 < α ∧
            feasiblePointArmijoAccepts f X c1 xk d α ∧
              ¬ feasiblePointArmijoAccepts f X c1 xk d (2 * α) := by
  constructor
  · intro h
    exact
      ⟨h.c1_mem, h.toIsFeasibleDescentDirection, h.alpha_pos, h.accepted,
        h.double_not_accepted⟩
  · rintro ⟨hc1, hd, hα, haccepted, hdouble⟩
    exact
      { toIsFeasibleDescentDirection := hd
        c1_mem := hc1
        alpha_pos := hα
        accepted := haccepted
        double_not_accepted := hdouble }

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Layer targeted by this refinement:
* source-facing: `SatisfiesArmijoRule`
* core/canonical owner: `gradientMethod stepSize f x0`
* bridge/view: the projection lemmas `alpha_pos`, `stepSize_pos`, `bounds`, `lowerBound`,
  and `upperBound`

Primary domain:
* Armijo step-size rules for real-Hilbert-space gradient-method trajectories

Sampled owner-style declarations:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `gradientMethod_succ` in `Algorithm_1_6_1.lean`
* `SatisfiesExactLineSearch` and `SatisfiesExactLineSearchAlong` in `Definition_1_6_3.lean`

Owner abstraction:
* the canonical recursive trajectory `gradientMethod stepSize f x0`

Primitive data:
* the objective `f`
* the step-size schedule `stepSize`
* the initial point `x0`
* the Armijo parameters `α`, `β`
* differentiability of `f` at each iterate of the owner trajectory

Derived API:
* genuine gradient existence of the displayed `∇ f (xₖ)` at each iterate
* positivity of `α`
* the inequalities `α < β < 1`
* positivity of each step size
* the iterate-wise lower and upper Armijo bounds

Unlike exact line search, a bare predicate along an arbitrary trajectory does not record that
`stepSize k` actually produces the next iterate. Definition 1.6.4 is therefore kept directly as
the gradient-method specialization, with the update rule owned by `gradientMethod` itself.

The source text is written on `ℝⁿ`, but the defining conditions use only the ambient inner
product, the genuine gradient, and the owner trajectory. As in `Algorithm_1_6_1` and
`Definition_1_6_3`, the public owner is therefore refined to the real-Hilbert-space level rather
than kept on a concrete Euclidean model.
-/

section

variable (f : E → ℝ) (stepSize : ℕ → ℝ) (x0 : E) (α β : ℝ)

/-- Definition 1.6.4: a step-size schedule `hₖ` satisfies the Armijo rule for the gradient-method
trajectory started at `x₀` when the objective is differentiable at every iterate, so the
displayed `∇ f(xₖ)` is genuine, `0 < α < β < 1`, every step size is positive, and the
consecutive iterates satisfy the two-sided Armijo decrease bounds. -/
def SatisfiesArmijoRule (f : E → ℝ) (stepSize : ℕ → ℝ) (x0 : E) (α β : ℝ) : Prop :=
  let traj := gradientMethod stepSize f x0
  (∀ k : ℕ, DifferentiableAt ℝ f (traj k)) ∧
    0 < α ∧
    α < β ∧
    β < 1 ∧
    (∀ k : ℕ, 0 < stepSize k) ∧
    ∀ k : ℕ,
      α * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) ≤
          f (traj k) - f (traj (k + 1)) ∧
        f (traj k) - f (traj (k + 1)) ≤
          β * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1))

end

namespace SatisfiesArmijoRule

variable {f : E → ℝ} {stepSize : ℕ → ℝ} {x0 : E} {α β : ℝ}

local notation "traj" => gradientMethod stepSize f x0

/-- Along an Armijo trajectory, the objective is differentiable at every iterate. -/
theorem differentiableAt
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    DifferentiableAt ℝ f (traj k) := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  simpa using hArmijo.1 k

/-- Along an Armijo trajectory, the displayed antigradient is the genuine gradient at every
iterate. -/
theorem hasGradientAt
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    HasGradientAt f (∇ f (traj k)) (traj k) :=
  (hArmijo.differentiableAt k).hasGradientAt

/-- The Armijo rule forces the lower parameter to be positive. -/
theorem alpha_pos
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) :
    0 < α := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, hα0, _, _, _, _⟩
  exact hα0

/-- The Armijo parameters satisfy `α < β`. -/
theorem alpha_lt_beta
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) :
    α < β := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, _, hαβ, _, _, _⟩
  exact hαβ

/-- The upper Armijo parameter lies below `1`. -/
theorem beta_lt_one
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) :
    β < 1 := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, _, _, hβ1, _, _⟩
  exact hβ1

/-- Every Armijo step size is positive. -/
theorem stepSize_pos
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    0 < stepSize k := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, _, _, _, hstep, _⟩
  exact hstep k

/-- The Armijo rule provides both comparison inequalities at each iterate. -/
theorem bounds
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    α * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) ≤
        f (traj k) - f (traj (k + 1)) ∧
      f (traj k) - f (traj (k + 1)) ≤
        β * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) := by
  dsimp [SatisfiesArmijoRule] at hArmijo
  rcases hArmijo with ⟨_, _, _, _, _, hbounds⟩
  simpa using hbounds k

/-- The lower Armijo comparison inequality. -/
theorem lowerBound
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    α * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) ≤
      f (traj k) - f (traj (k + 1)) := by
  rcases hArmijo.bounds k with ⟨hlow, _⟩
  exact hlow

/-- The upper Armijo comparison inequality. -/
theorem upperBound
    (hArmijo : SatisfiesArmijoRule f stepSize x0 α β) (k : ℕ) :
    f (traj k) - f (traj (k + 1)) ≤
      β * inner ℝ (∇ f (traj k)) (traj k - traj (k + 1)) := by
  rcases hArmijo.bounds k with ⟨_, hupp⟩
  exact hupp

end SatisfiesArmijoRule

/-- The constant zero objective with initial point `0` and unit step sizes satisfies the Armijo
rule for the canonical parameters `α = 1 / 4` and `β = 1 / 2`. -/
theorem zero_zero_constOne_satisfiesArmijoRule :
    SatisfiesArmijoRule (fun _ : E ↦ 0) (fun _ : ℕ ↦ 1) (0 : E)
      (1 / 4 : ℝ) (1 / 2 : ℝ) := by
  dsimp [SatisfiesArmijoRule]
  refine ⟨?_, by positivity, by norm_num, by norm_num, ?_, ?_⟩
  · intro k
    exact
      (show DifferentiableAt ℝ (fun _ : E ↦ (0 : ℝ))
          ((gradientMethod (fun _ : ℕ ↦ (1 : ℝ)) (fun _ : E ↦ 0) (0 : E)) k) from
        differentiableAt_const (0 : ℝ))
  · intro k
    norm_num
  · intro k
    constructor <;> simp

end

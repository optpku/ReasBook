/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_6_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient MinGradientNormAlongIterates SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "p" => normSeminorm ℝ E
local notation "State" => E × E × ℝ

/- Primary domain: smooth-convex accelerated optimal-method recurrences on real Hilbert spaces,
and the monotone type-I variant of method `(2.2.32)`.

Owner-style declarations sampled before refining this file:
* `OptimalMethodRecurrence` in `Algorithm_2_2`, the owner recurrence data
  `(xₖ, yₖ, vₖ, αₖ, γₖ)`;
* `GeneralOptimalMethodScheme` in `Algorithm_2_2`, the owner extension adding the step-`(c)`
  descent inequality;
* `constantStepSchemeIAlphaNext` in `Algorithm_2_3`, the owner scalar update for the
  `μ = 0` optimal-method recurrence used here at `γ₀ = 3L`;
* `minGradientNormAlongIterates` in `Definition_2_23`, the owner finite-window realization of the
  textbook quantity `g_{0,T}`.

Best owner abstraction:
* source-facing: the recursive monotone type-I trajectory `monotoneConstantStepSchemeIA`,
  together with its source-named points `x̂ₖ`, `ŷₖ`;
* core/canonical: `OptimalMethodRecurrence f (L : ℝ) 0 x0 (3 * (L : ℝ))`,
  `GeneralOptimalMethodScheme f (L : ℝ) 0 x0 (3 * (L : ℝ))`, and
  `minGradientNormAlongIterates`;
* bridge/view: `monotoneConstantStepSchemeIAToOptimalMethodRecurrence` and
  `monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme`.

Primitive data:
* the recursive state `(xₖ, vₖ, γₖ)`.

Derived API:
* the source-named sequences `αₖ`, `yₖ`, `x̂ₖ`, `ŷₖ`;
* the comparison lemmas showing `ŷₖ` is chosen between `xₖ` and `x̂ₖ₊₁`;
* the owner bridges recovering the canonical recurrence and descent inequality.

This file therefore keeps the method itself as a recursive source-facing object, not as a public
wrapper structure with primitive comparison fields. The monotonicity data `x̂ₖ`, `ŷₖ` remain
visible as exact recursive declarations, while the owner optimal-method structures are derived
bridge API. -/

private def monotoneConstantStepSchemeIAAlphaState
    (L : NNReal) (state : State) : ℝ :=
  constantStepSchemeIAlphaNext (L : ℝ) 0 state.2.2

private def monotoneConstantStepSchemeIAGammaNextState
    (L : NNReal) (state : State) : ℝ :=
  (L : ℝ) * monotoneConstantStepSchemeIAAlphaState L state ^ (2 : ℕ)

private def monotoneConstantStepSchemeIAYState
    (L : NNReal) (state : State) : E :=
  let xk := state.1
  let vk := state.2.1
  let gammak := state.2.2
  let alphak := monotoneConstantStepSchemeIAAlphaState L state
  let gammaNext := monotoneConstantStepSchemeIAGammaNextState L state
  (1 / gammak) • ((alphak * gammak) • vk + gammaNext • xk)

private def monotoneConstantStepSchemeIAXHatState
    (f : E → ℝ) (L : NNReal) (state : State) : E :=
  let yk := monotoneConstantStepSchemeIAYState L state
  yk - (1 / (L : ℝ)) • ∇ f yk

private def monotoneConstantStepSchemeIAYHatState
    (f : E → ℝ) (L : NNReal) (state : State) : E :=
  let xk := state.1
  let xHatNext := monotoneConstantStepSchemeIAXHatState f L state
  if f xk ≤ f xHatNext then xk else xHatNext

private def monotoneConstantStepSchemeIAXNextState
    (f : E → ℝ) (L : NNReal) (state : State) : E :=
  let yHatk := monotoneConstantStepSchemeIAYHatState f L state
  yHatk - (1 / (L : ℝ)) • ∇ f yHatk

private def monotoneConstantStepSchemeIAVNextState
    (f : E → ℝ) (L : NNReal) (state : State) : E :=
  let vk := state.2.1
  let gammak := state.2.2
  let alphak := monotoneConstantStepSchemeIAAlphaState L state
  let gammaNext := monotoneConstantStepSchemeIAGammaNextState L state
  let yk := monotoneConstantStepSchemeIAYState L state
  (1 / gammaNext) • (((1 - alphak) * gammak) • vk - alphak • ∇ f yk)

/-- Method `(2.2.32)`: the recursive monotone type-I trajectory with state `(xₖ, vₖ, γₖ)`,
started from `(x₀, x₀, 3L)`. The source-named points `yₖ`, `x̂ₖ₊₁`, and `ŷₖ` are derived from the
current state, and the next iterate is the reciprocal-`L` gradient step from `ŷₖ`. -/
noncomputable def monotoneConstantStepSchemeIA
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E × E × ℝ
  | 0 => (x0, x0, 3 * (L : ℝ))
  | k + 1 =>
      let state := monotoneConstantStepSchemeIA f L x0 k
      let xNext := monotoneConstantStepSchemeIAXNextState f L state
      let vNext := monotoneConstantStepSchemeIAVNextState f L state
      let gammaNext := monotoneConstantStepSchemeIAGammaNextState L state
      (xNext, vNext, gammaNext)

/-- The main iterate sequence `xₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAX
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ (monotoneConstantStepSchemeIA f L x0 k).1

/-- The estimating-sequence centers `vₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAV
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ (monotoneConstantStepSchemeIA f L x0 k).2.1

/-- The curvature sequence `γₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAGamma
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → ℝ :=
  fun k ↦ (monotoneConstantStepSchemeIA f L x0 k).2.2

/-- The coefficient sequence `αₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAAlpha
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → ℝ :=
  fun k ↦ monotoneConstantStepSchemeIAAlphaState L (monotoneConstantStepSchemeIA f L x0 k)

/-- The interpolation sequence `yₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAY
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ monotoneConstantStepSchemeIAYState L (monotoneConstantStepSchemeIA f L x0 k)

/-- The trial gradient-step points `x̂ₖ`. We set `x̂₀ = x₀`, while the source recursion uses the
successor values `x̂ₖ₊₁`. -/
noncomputable def monotoneConstantStepSchemeIAXHat
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E
  | 0 => x0
  | k + 1 => monotoneConstantStepSchemeIAXHatState f L (monotoneConstantStepSchemeIA f L x0 k)

/-- The selected comparison points `ŷₖ` of the monotone type-I trajectory. -/
noncomputable def monotoneConstantStepSchemeIAYHat
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ monotoneConstantStepSchemeIAYHatState f L (monotoneConstantStepSchemeIA f L x0 k)

@[simp] theorem monotoneConstantStepSchemeIA_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIA f L x0 0 = (x0, x0, 3 * (L : ℝ)) :=
  rfl

@[simp] theorem monotoneConstantStepSchemeIA_succ
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIA f L x0 (k + 1) =
      let state := monotoneConstantStepSchemeIA f L x0 k
      let xNext := monotoneConstantStepSchemeIAXNextState f L state
      let vNext := monotoneConstantStepSchemeIAVNextState f L state
      let gammaNext := monotoneConstantStepSchemeIAGammaNextState L state
      (xNext, vNext, gammaNext) :=
  rfl

@[simp] theorem monotoneConstantStepSchemeIAX_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIAX f L x0 0 = x0 :=
  rfl

@[simp] theorem monotoneConstantStepSchemeIAV_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIAV f L x0 0 = x0 :=
  rfl

@[simp] theorem monotoneConstantStepSchemeIAGamma_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIAGamma f L x0 0 = 3 * (L : ℝ) :=
  rfl

@[simp] private theorem monotoneConstantStepSchemeIAAlpha_eq
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAAlpha f L x0 k =
      constantStepSchemeIAlphaNext
        (L : ℝ) 0 (monotoneConstantStepSchemeIAGamma f L x0 k) :=
  rfl

@[simp] private theorem monotoneConstantStepSchemeIAGamma_succ_eq_L_mul_sq
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAGamma f L x0 (k + 1) =
      (L : ℝ) * monotoneConstantStepSchemeIAAlpha f L x0 k ^ (2 : ℕ) :=
  rfl

/-- The interpolation points satisfy the owner optimal-method formula specialized to `μ = 0`. -/
private theorem monotoneConstantStepSchemeIAY_eq
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAY f L x0 k =
      (1 / monotoneConstantStepSchemeIAGamma f L x0 k) •
        ((monotoneConstantStepSchemeIAAlpha f L x0 k *
              monotoneConstantStepSchemeIAGamma f L x0 k) •
            monotoneConstantStepSchemeIAV f L x0 k +
          monotoneConstantStepSchemeIAGamma f L x0 (k + 1) •
            monotoneConstantStepSchemeIAX f L x0 k) := by
  rfl

@[simp] theorem monotoneConstantStepSchemeIAXHat_zero
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    monotoneConstantStepSchemeIAXHat f L x0 0 = x0 :=
  rfl

/-- The trial points `x̂ₖ₊₁` are the reciprocal-`L` gradient steps from `yₖ`. -/
@[simp] theorem monotoneConstantStepSchemeIAXHat_succ
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAXHat f L x0 (k + 1) =
      monotoneConstantStepSchemeIAY f L x0 k -
        (1 / (L : ℝ)) • ∇ f (monotoneConstantStepSchemeIAY f L x0 k) := by
  rfl

/-- Each comparison point `ŷₖ` is chosen between the current iterate `xₖ` and the trial point
`x̂ₖ₊₁`. -/
@[simp] theorem monotoneConstantStepSchemeIAYHat_eq_if
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAYHat f L x0 k =
      if f (monotoneConstantStepSchemeIAX f L x0 k) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1))
      then monotoneConstantStepSchemeIAX f L x0 k
      else monotoneConstantStepSchemeIAXHat f L x0 (k + 1) := by
  rfl

/-- The selected comparison point has objective value no larger than `x̂ₖ₊₁`. -/
private theorem monotoneConstantStepSchemeIAYHat_objective_le_xHat
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    f (monotoneConstantStepSchemeIAYHat f L x0 k) ≤
      f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1)) := by
  by_cases h :
      f (monotoneConstantStepSchemeIAX f L x0 k) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1))
  · rw [monotoneConstantStepSchemeIAYHat_eq_if, if_pos h]
    exact h
  · rw [monotoneConstantStepSchemeIAYHat_eq_if, if_neg h]

/-- Helper for Theorem 2.26: the selected comparison point has objective value no larger than the
current iterate `xₖ`. -/
private theorem monotoneConstantStepSchemeIAYHat_objective_le_x
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    f (monotoneConstantStepSchemeIAYHat f L x0 k) ≤
      f (monotoneConstantStepSchemeIAX f L x0 k) := by
  -- The `if` defining `ŷₖ` chooses the lower-objective point between `xₖ` and `x̂ₖ₊₁`.
  by_cases h :
      f (monotoneConstantStepSchemeIAX f L x0 k) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1))
  · rw [monotoneConstantStepSchemeIAYHat_eq_if, if_pos h]
  · rw [monotoneConstantStepSchemeIAYHat_eq_if, if_neg h]
    exact le_of_not_ge h

/-- The actual iterates are the reciprocal-`L` gradient steps from the selected comparison
points `ŷₖ`. -/
@[simp] theorem monotoneConstantStepSchemeIAX_succ
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAX f L x0 (k + 1) =
      monotoneConstantStepSchemeIAYHat f L x0 k -
        (1 / (L : ℝ)) • ∇ f (monotoneConstantStepSchemeIAYHat f L x0 k) := by
  rfl

/-- The center update matches the owner optimal-method recurrence specialized to `μ = 0`. -/
private theorem monotoneConstantStepSchemeIAV_succ
    (f : E → ℝ) (L : NNReal) (x0 : E) (k : ℕ) :
    monotoneConstantStepSchemeIAV f L x0 (k + 1) =
      (1 / monotoneConstantStepSchemeIAGamma f L x0 (k + 1)) •
        (((1 - monotoneConstantStepSchemeIAAlpha f L x0 k) *
              monotoneConstantStepSchemeIAGamma f L x0 k) •
            monotoneConstantStepSchemeIAV f L x0 k -
          monotoneConstantStepSchemeIAAlpha f L x0 k •
            ∇ f (monotoneConstantStepSchemeIAY f L x0 k)) := by
  rfl

/-- The curvature sequence stays positive once `L > 0`. -/
private theorem monotoneConstantStepSchemeIAGamma_pos
    (f : E → ℝ) (L : NNReal) (x0 : E) (hL : 0 < (L : ℝ)) :
    ∀ k : ℕ, 0 < monotoneConstantStepSchemeIAGamma f L x0 k
  | 0 => by
      simpa using show 0 < 3 * (L : ℝ) from by nlinarith
  | k + 1 => by
      have hk : 0 < monotoneConstantStepSchemeIAGamma f L x0 k :=
        monotoneConstantStepSchemeIAGamma_pos f L x0 hL k
      have hα :
          0 <
            constantStepSchemeIAlphaNext
              (L : ℝ) 0 (monotoneConstantStepSchemeIAGamma f L x0 k) :=
        constantStepSchemeIAlphaNext_pos hL hk
      have hsucc :
          0 <
            (L : ℝ) * monotoneConstantStepSchemeIAAlpha f L x0 k ^ (2 : ℕ) := by
        positivity
      simpa [monotoneConstantStepSchemeIAGamma_succ_eq_L_mul_sq] using hsucc

private theorem monotoneConstantStepSchemeIAAlpha_mem_Ioo
    (f : E → ℝ) (L : NNReal) (x0 : E) (hL : 0 < (L : ℝ)) (k : ℕ) :
    monotoneConstantStepSchemeIAAlpha f L x0 k ∈ Set.Ioo (0 : ℝ) 1 := by
  simpa [monotoneConstantStepSchemeIAAlpha_eq] using
    constantStepSchemeIAlphaNext_mem_Ioo hL hL
      (monotoneConstantStepSchemeIAGamma_pos f L x0 hL k)

private theorem monotoneConstantStepSchemeIAAlpha_equation
    (f : E → ℝ) (L : NNReal) (x0 : E) (hL : 0 < (L : ℝ)) (k : ℕ) :
    (L : ℝ) * monotoneConstantStepSchemeIAAlpha f L x0 k ^ (2 : ℕ) =
      (1 - monotoneConstantStepSchemeIAAlpha f L x0 k) *
          monotoneConstantStepSchemeIAGamma f L x0 k +
        monotoneConstantStepSchemeIAAlpha f L x0 k * 0 := by
  have hEq :
      (L : ℝ) * constantStepSchemeIAlphaNext (L : ℝ) 0
          (monotoneConstantStepSchemeIAGamma f L x0 k) ^ (2 : ℕ) =
        (1 - constantStepSchemeIAlphaNext (L : ℝ) 0
            (monotoneConstantStepSchemeIAGamma f L x0 k)) *
            monotoneConstantStepSchemeIAGamma f L x0 k +
          constantStepSchemeIAlphaNext (L : ℝ) 0
            (monotoneConstantStepSchemeIAGamma f L x0 k) * 0 := by
    exact constantStepSchemeIAlphaNext_satisfies_equation hL
      (monotoneConstantStepSchemeIAGamma_pos f L x0 hL k)
  simpa [monotoneConstantStepSchemeIAAlpha_eq] using hEq

/-- The recursive monotone type-I trajectory, viewed through the owner optimal-method recurrence
API. -/
def monotoneConstantStepSchemeIAToOptimalMethodRecurrence
    (f : E → ℝ) (L : NNReal) (x0 : E) (hL : 0 < (L : ℝ)) :
    OptimalMethodRecurrence f (L : ℝ) 0 x0 (3 * (L : ℝ)) where
  L_pos := hL
  mu_nonneg := by positivity
  gamma0_pos := by
    linarith
  x := monotoneConstantStepSchemeIAX f L x0
  y := monotoneConstantStepSchemeIAY f L x0
  v := monotoneConstantStepSchemeIAV f L x0
  alpha := monotoneConstantStepSchemeIAAlpha f L x0
  gamma := monotoneConstantStepSchemeIAGamma f L x0
  x_zero := monotoneConstantStepSchemeIAX_zero f L x0
  v_zero := monotoneConstantStepSchemeIAV_zero f L x0
  gamma_zero := monotoneConstantStepSchemeIAGamma_zero f L x0
  alpha_mem_Ioo := monotoneConstantStepSchemeIAAlpha_mem_Ioo f L x0 hL
  alpha_equation := monotoneConstantStepSchemeIAAlpha_equation f L x0 hL
  gamma_succ := by
    intro k
    calc
      monotoneConstantStepSchemeIAGamma f L x0 (k + 1) =
          (L : ℝ) * monotoneConstantStepSchemeIAAlpha f L x0 k ^ (2 : ℕ) := by
            exact monotoneConstantStepSchemeIAGamma_succ_eq_L_mul_sq f L x0 k
      _ =
          (1 - monotoneConstantStepSchemeIAAlpha f L x0 k) *
              monotoneConstantStepSchemeIAGamma f L x0 k +
            monotoneConstantStepSchemeIAAlpha f L x0 k * 0 := by
              exact monotoneConstantStepSchemeIAAlpha_equation f L x0 hL k
  y_eq := by
    intro k
    simpa using monotoneConstantStepSchemeIAY_eq f L x0 k
  v_succ := by
    intro k
    simpa using monotoneConstantStepSchemeIAV_succ f L x0 k

/-- Under the intrinsic reciprocal-`L` gradient-step hypotheses, the monotone type-I trajectory
inherits the descent inequality of the general optimal-method scheme. -/
def monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
    (f : E → ℝ) (L : NNReal) (x0 : E)
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    GeneralOptimalMethodScheme f (L : ℝ) 0 x0 (3 * (L : ℝ)) where
  toOptimalMethodRecurrence :=
    monotoneConstantStepSchemeIAToOptimalMethodRecurrence f L x0 hL
  x_succ_le := by
    intro k
    have hx_le_yHat :
        f (monotoneConstantStepSchemeIAX f L x0 (k + 1)) ≤
          f (monotoneConstantStepSchemeIAYHat f L x0 k) := by
      have hx_desc :
          f (monotoneConstantStepSchemeIAX f L x0 (k + 1)) ≤
            f (monotoneConstantStepSchemeIAYHat f L x0 k) -
              (1 / (2 * (L : ℝ))) *
                ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 k)‖ ^ (2 : ℕ) := by
        simpa [monotoneConstantStepSchemeIAX_succ] using
          gradient_step_value_descent_of_lipschitzGradient
            f hL (fun x ↦ (hgrad x).differentiableAt)
            (by simpa using hgrad_lipschitz)
            (monotoneConstantStepSchemeIAYHat f L x0 k)
      calc
        f (monotoneConstantStepSchemeIAX f L x0 (k + 1)) ≤
            f (monotoneConstantStepSchemeIAYHat f L x0 k) -
              (1 / (2 * (L : ℝ))) *
                ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 k)‖ ^ (2 : ℕ) := hx_desc
        _ ≤ f (monotoneConstantStepSchemeIAYHat f L x0 k) := by
          exact sub_le_self _ (by positivity)
    have hxHat_desc :
        f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1)) ≤
          f (monotoneConstantStepSchemeIAY f L x0 k) -
            (1 / (2 * (L : ℝ))) *
              ‖∇ f (monotoneConstantStepSchemeIAY f L x0 k)‖ ^ (2 : ℕ) := by
      simpa [monotoneConstantStepSchemeIAXHat_succ] using
        gradient_step_value_descent_of_lipschitzGradient
          f hL (fun x ↦ (hgrad x).differentiableAt)
          (by simpa using hgrad_lipschitz)
          (monotoneConstantStepSchemeIAY f L x0 k)
    calc
      f (monotoneConstantStepSchemeIAX f L x0 (k + 1)) ≤
          f (monotoneConstantStepSchemeIAYHat f L x0 k) := hx_le_yHat
      _ ≤ f (monotoneConstantStepSchemeIAXHat f L x0 (k + 1)) :=
          monotoneConstantStepSchemeIAYHat_objective_le_xHat f L x0 k
      _ ≤
          f (monotoneConstantStepSchemeIAY f L x0 k) -
            (1 / (2 * (L : ℝ))) *
              ‖∇ f (monotoneConstantStepSchemeIAY f L x0 k)‖ ^ (2 : ℕ) := hxHat_desc

/-
Theorem 2.26 on the intrinsic real-Hilbert-space owner layer: if `f` is convex on the whole
space, admits the ambient gradient `∇ f` everywhere, that gradient is `L`-Lipschitz in the
ambient norm, and `xStar` is a global minimizer, then the recursive monotone type-I trajectory of
method `(2.2.32)` satisfies the explicit `O(T^{-3/2})` bound on the minimum gradient norm
`g_{0,T}` over the first `T + 1` iterates. The textbook `ℝⁿ` statement is the finite-dimensional
specialization below.
-/

/-- Helper for Theorem 2.26: when `L = 0`, the Lipschitz-gradient hypothesis forces the ambient
gradient to vanish everywhere, so the finite-window minimum gradient norm is exactly zero. -/
private lemma monotoneConstantStepSchemeIA_minGradientNorm_eq_zero_of_L_eq_zero
    {L : NNReal} {f : E → ℝ}
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ}
    (hL0 : (L : ℝ) = 0) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] = 0 := by
  -- A global minimizer is stationary, so the `0`-Lipschitz gradient field is identically zero.
  have hgrad_zero_at_minimizer : ∇ f xStar = 0 :=
    isMinOn_gradient_eq_zero hxStar
  have hgrad_zero : ∀ x : E, ∇ f x = 0 := by
    intro x
    have hdist := hgrad_lipschitz.dist_le_mul x xStar
    have hdist0 : dist (∇ f x) (∇ f xStar) = 0 := by
      apply le_antisymm
      · simpa [hL0] using hdist
      · exact dist_nonneg
    simpa [hgrad_zero_at_minimizer] using eq_of_dist_eq_zero hdist0
  -- The window minimum is attained at some iterate, and that iterate has zero gradient norm.
  rcases minGradientNormAlongIterates.exists_eq
      f (monotoneConstantStepSchemeIAX f L x0) (Nat.zero_le T) with
    ⟨i, -, -, hi⟩
  rw [hi, hgrad_zero, norm_zero]

/-- Helper for Theorem 2.26: the finite-window minimum gradient norm is nonnegative because it is
attained by a gradient norm in the window. -/
private lemma monotoneConstantStepSchemeIA_minGradientNorm_nonneg
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    (T : ℕ) :
    0 ≤ g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] := by
  -- The owner minimum is realized by one iterate in the window.
  rcases minGradientNormAlongIterates.exists_eq
      f (monotoneConstantStepSchemeIAX f L x0) (Nat.zero_le T) with
    ⟨i, -, -, hi⟩
  rw [hi]
  exact norm_nonneg _

/-- Helper for Theorem 2.26: the explicit cubic denominator in the displayed rate is positive for
every admissible horizon `T ≥ 1`. -/
private lemma monotoneConstantStepSchemeIA_explicit_denominator_pos
    {T : ℕ} (hT : 1 ≤ T) :
    0 <
      ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
        (9 / 4 : ℝ) * (T + 2 : ℝ) -
        (9 / 8 : ℝ)) := by
  -- Factor the cubic denominator as `((2x - 3) (4x + 3)^2) / 24` at `x = T + 2`.
  have hT' : (1 : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hT
  have hx : (3 : ℝ) ≤ (T : ℝ) + 2 := by
    nlinarith
  have hfactor_pos : 0 < 2 * ((T : ℝ) + 2) - 3 := by
    nlinarith
  have hsquare_pos : 0 < (4 * ((T : ℝ) + 2) + 3) ^ (2 : ℕ) := by
    positivity
  have hprod_pos :
      0 < (2 * ((T : ℝ) + 2) - 3) * (4 * ((T : ℝ) + 2) + 3) ^ (2 : ℕ) := by
    positivity
  have hrewrite :
      ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
          (9 / 4 : ℝ) * (T + 2 : ℝ) -
          (9 / 8 : ℝ)) =
        ((2 * ((T : ℝ) + 2) - 3) * (4 * ((T : ℝ) + 2) + 3) ^ (2 : ℕ)) / 24 := by
    ring
  rw [hrewrite]
  positivity

/-- Helper for Theorem 2.26: every owner weight stays at most `1`. -/
private theorem optimalMethodRecurrence_weight_le_one
    {f : E → ℝ} {L μ gamma0 : ℝ} {x0 : E}
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    (k : ℕ) :
    method.weight k ≤ 1 := by
  -- The owner weight starts at `1` and every update multiplies by a factor from `(0, 1)`.
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [method.weight_succ]
      have hfactor_nonneg : 0 ≤ 1 - method.alpha k := by
        linarith [(method.alpha_mem_Ioo k).2]
      have hfactor_le_one : 1 - method.alpha k ≤ 1 := by
        linarith [(method.alpha_mem_Ioo k).1]
      have hweight_nonneg : 0 ≤ method.weight k := (method.weight_pos k).le
      have hmul_le :
          (1 - method.alpha k) * method.weight k ≤ 1 * method.weight k := by
        exact mul_le_mul_of_nonneg_right hfactor_le_one hweight_nonneg
      have ih' : 1 * method.weight k ≤ 1 := by
        simpa using ih
      exact hmul_le.trans ih'

/-- Helper for Theorem 2.26: every positive-stage owner weight is strictly below `1`. -/
private theorem optimalMethodRecurrence_weight_lt_one_of_one_le
    {f : E → ℝ} {L μ gamma0 : ℝ} {x0 : E}
    (method : OptimalMethodRecurrence f L μ x0 gamma0)
    {k : ℕ} (hk : 1 ≤ k) :
    method.weight k < 1 := by
  -- Once `k ≥ 1`, the last recurrence factor is strictly smaller than `1`.
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨j, rfl⟩
  rw [method.weight_succ]
  have hfactor_nonneg : 0 ≤ 1 - method.alpha j := by
    linarith [(method.alpha_mem_Ioo j).2]
  have hfactor_lt_one : 1 - method.alpha j < 1 := by
    linarith [(method.alpha_mem_Ioo j).1]
  have hweight_nonneg : 0 ≤ method.weight j := (method.weight_pos j).le
  have hweight_le_one : method.weight j ≤ 1 :=
    optimalMethodRecurrence_weight_le_one method j
  nlinarith

/-- Helper for Theorem 2.26: the initialization `γ₀ = 3L` forces the owner coefficient to satisfy
`α_k^2 + 3 α_k ≤ 3` at every stage. -/
private lemma monotoneConstantStepSchemeIA_alpha_sq_add_three_mul_alpha_le_three
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {k : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    method.alpha k ^ (2 : ℕ) + 3 * method.alpha k ≤ 3 := by
  -- Bound `γ_k` by the initial curvature `3L`, then substitute the owner quadratic relation
  -- `L α_k^2 = (1 - α_k) γ_k`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hweight_le_one : method.weight k ≤ 1 :=
    optimalMethodRecurrence_weight_le_one method.toOptimalMethodRecurrence k
  have hgamma_eq :
      method.gamma k = method.weight k * (3 * (L : ℝ)) := by
    simpa [method] using method.gamma_sub_mu_eq_weight_mul_initial_gap k
  have hgamma_le :
      method.gamma k ≤ 3 * (L : ℝ) := by
    calc
      method.gamma k = method.weight k * (3 * (L : ℝ)) := hgamma_eq
      _ ≤ 1 * (3 * (L : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hweight_le_one (by positivity)
      _ = 3 * (L : ℝ) := by ring
  have halpha_eq :
      (L : ℝ) * method.alpha k ^ (2 : ℕ) =
        (1 - method.alpha k) * method.gamma k := by
    simpa using method.alpha_equation k
  have halpha_nonneg : 0 ≤ method.alpha k := (method.alpha_mem_Ioo k).1.le
  have halpha_lt_one : method.alpha k < 1 := (method.alpha_mem_Ioo k).2
  nlinarith

/-- Helper for Theorem 2.26: two copies of the window mass weighted only by `α_k` still sit below
the target coefficient `3 - α_k^2`. -/
private lemma monotoneConstantStepSchemeIA_two_mul_alpha_le_targetCoefficient
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {k : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * method.alpha k ≤ 3 - method.alpha k ^ (2 : ℕ) := by
  -- The quadratic upper bound on `α_k` leaves at least one extra unit of mass beyond
  -- the duplicated `α_k`-weighted window contribution.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have halpha_bound :
      method.alpha k ^ (2 : ℕ) + 3 * method.alpha k ≤ 3 := by
    simpa [method] using
      monotoneConstantStepSchemeIA_alpha_sq_add_three_mul_alpha_le_three
        (f := f) (L := L) x0 (k := k) hL hgrad hgrad_lipschitz
  have halpha_nonneg : 0 ≤ method.alpha k := (method.alpha_mem_Ioo k).1.le
  nlinarith

/-- Helper for Theorem 2.26: even a `3 α_k`-weighted iterate window is still no larger than the
target coefficient `3 - α_k^2`, so any branch closure that only produces `3 α_k` copies of `g₀²`
is strictly one-sided for the final theorem. -/
private lemma monotoneConstantStepSchemeIA_three_mul_alpha_le_targetCoefficient
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {k : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    3 * method.alpha k ≤ 3 - method.alpha k ^ (2 : ℕ) := by
  -- Repackage the already-proved owner quadratic bound on `α_k`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have halpha_bound :
      method.alpha k ^ (2 : ℕ) + 3 * method.alpha k ≤ 3 := by
    simpa [method] using
      monotoneConstantStepSchemeIA_alpha_sq_add_three_mul_alpha_le_three
        (f := f) (L := L) x0 (k := k) hL hgrad hgrad_lipschitz
  nlinarith

/-- Helper for Theorem 2.26: the quadratic weight polynomial on `Icc 1 T` has the displayed
closed form. -/
private lemma monotoneConstantStepSchemeIA_quadratic_weight_sum_closed_form
    (T : ℕ) :
    Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) =
      ((T : ℝ) * (2 * (T : ℝ) ^ (2 : ℕ) + 9 * (T : ℝ) + 5)) / 2 := by
  -- Extend the interval sum by one top index and simplify the resulting polynomial recursion.
  induction T with
  | zero =>
      norm_num
  | succ T ih =>
      rw [Finset.sum_Icc_succ_top (show 1 ≤ T + 1 by omega), ih]
      norm_num [pow_two]
      ring_nf

/-- Helper for Theorem 2.26: the owner weight-ratio bound from Theorem 2.22 forces the summed
weight denominator to dominate the displayed cubic polynomial. -/
private lemma monotoneConstantStepSchemeIA_weight_sum_ge_explicit_denominator
    {L : NNReal} {f : E → ℝ} {x0 : E}
    (method : GeneralOptimalMethodScheme f (L : ℝ) 0 x0 (3 * (L : ℝ)))
    {T : ℕ} (hT : 1 ≤ T) :
    ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
        (9 / 4 : ℝ) * (T + 2 : ℝ) -
        (9 / 8 : ℝ)) ≤
      16 * Finset.sum (Finset.Icc 1 T) (fun k ↦
        (1 - method.toOptimalMethodRecurrence.weight k) /
          method.toOptimalMethodRecurrence.weight k) := by
  set weight : ℕ → ℝ := method.toOptimalMethodRecurrence.weight
  have hterm :
      ∀ k ∈ Finset.Icc 1 T,
        (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) ≤ 4 * ((1 - weight k) / weight k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hratio :
        weight k / (1 - weight k) ≤ 4 / (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) :=
      method.toOptimalMethodRecurrence.weight_ratio_le_of_gamma0_eq_three_mul hk1
    have hweight_pos : 0 < weight k := method.toOptimalMethodRecurrence.weight_pos k
    have hweight_lt_one : weight k < 1 :=
      optimalMethodRecurrence_weight_lt_one_of_one_le
        method.toOptimalMethodRecurrence hk1
    have hratio_pos : 0 < weight k / (1 - weight k) := by
      have hden_pos : 0 < 1 - weight k := by
        linarith
      positivity
    have hinv :
        (3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) / 4 ≤ (1 - weight k) / weight k := by
      simpa [one_div_div] using one_div_le_one_div_of_le hratio_pos hratio
    nlinarith
  have hsum :
      Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) ≤
        4 * Finset.sum (Finset.Icc 1 T) (fun k ↦ (1 - weight k) / weight k) := by
    calc
      Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4)
          ≤ Finset.sum (Finset.Icc 1 T) (fun k ↦ 4 * ((1 - weight k) / weight k)) := by
            exact Finset.sum_le_sum fun k hk ↦ hterm k hk
      _ = 4 * Finset.sum (Finset.Icc 1 T) (fun k ↦ (1 - weight k) / weight k) := by
            rw [Finset.mul_sum]
  have hT' : (1 : ℝ) ≤ T := by
    exact_mod_cast hT
  have hpoly :
      ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
          (9 / 4 : ℝ) * (T + 2 : ℝ) -
          (9 / 8 : ℝ)) ≤
        4 * Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) := by
    rw [monotoneConstantStepSchemeIA_quadratic_weight_sum_closed_form]
    nlinarith
  have hfour :
      4 * Finset.sum (Finset.Icc 1 T) (fun k ↦ 3 * (k + 1 : ℝ) ^ (2 : ℕ) - 4) ≤
        16 * Finset.sum (Finset.Icc 1 T) (fun k ↦ (1 - weight k) / weight k) := by
    nlinarith
  exact hpoly.trans hfour

/-- Helper for Theorem 2.26: a global minimizer bounds every objective value below by the local
smooth quadratic gap `‖∇ f x‖² / (2L)`. -/
private lemma monotoneConstantStepSchemeIA_objective_gap_ge_gradient_sq_half_div_L
    {L : NNReal} {f : E → ℝ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x : E) :
    f xStar + (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) ≤ f x := by
  -- A reciprocal-`L` gradient step from `x` decreases the objective by the smooth quadratic
  -- term, and the minimizer sits below that descended value.
  have hdesc :
      f (x - (1 / (L : ℝ)) • ∇ f x) ≤
        f x - (1 / (2 * (L : ℝ))) * ‖∇ f x‖ ^ (2 : ℕ) := by
    simpa using
      gradient_step_value_descent_of_lipschitzGradient
        f hL (fun z ↦ (hgrad z).differentiableAt) (by simpa using hgrad_lipschitz) x
  have hmin :
      f xStar ≤ f (x - (1 / (L : ℝ)) • ∇ f x) := by
    exact isMinOn_univ_iff.mp hxStar _
  linarith

/-- Helper for Theorem 2.26: every current iterate already satisfies the one-square minimizer-gap
bound `2L (f (x_m) - f (x_★)) ≥ ‖∇ f (x_m)‖²`. -/
private lemma monotoneConstantStepSchemeIA_currentGap_lower_bound
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hxStar : IsMinOn f Set.univ xStar) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (f (method m) - f xStar) ≥
      ‖∇ f (method m)‖ ^ (2 : ℕ) := by
  -- Specialize the generic minimizer-gap estimate at the current iterate and clear the factor
  -- `1 / (2L)` once so later branch proofs can reuse the one-square form directly.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hgap :=
    monotoneConstantStepSchemeIA_objective_gap_ge_gradient_sq_half_div_L
      (f := f) (L := L) hL hgrad hgrad_lipschitz xStar hxStar (method m)
  have hgap' :
      (1 / (2 * (L : ℝ))) * ‖∇ f (method m)‖ ^ (2 : ℕ) ≤
        f (method m) - f xStar := by
    linarith
  have hscaled :=
    mul_le_mul_of_nonneg_left hgap' (show 0 ≤ 2 * (L : ℝ) by positivity)
  calc
    ‖∇ f (method m)‖ ^ (2 : ℕ)
        = 2 * (L : ℝ) *
            ((1 / (2 * (L : ℝ))) * ‖∇ f (method m)‖ ^ (2 : ℕ)) := by
            field_simp [hL.ne']
    _ ≤ 2 * (L : ℝ) * (f (method m) - f xStar) := hscaled

/-- Helper for Theorem 2.26: the owner interpolation point has the exact smooth-convex source
form `y_k = α_k v_k + (1 - α_k) x_k`. -/
private lemma monotoneConstantStepSchemeIA_y_eq_alpha_smul_v_add_one_sub_smul_x
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {k : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    method.y k = method.alpha k • method.v k + (1 - method.alpha k) • method k := by
  -- Route correction: rewrite the owner `y_k` formula once so the later Lyapunov step can use
  -- the source interpolation identity directly rather than raw `γ` algebra.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hgamma_eq :
      method.gamma k = method.weight k * (3 * (L : ℝ)) := by
    simpa [method] using method.gamma_sub_mu_eq_weight_mul_initial_gap k
  have hgamma_ne : method.gamma k ≠ 0 := by
    rw [hgamma_eq]
    exact mul_ne_zero (method.weight_pos k).ne' (by positivity)
  calc
    method.y k
        = (1 / method.gamma k) •
            ((method.alpha k * method.gamma k) • method.v k +
              method.gamma (k + 1) • method k) := by
            simpa [method] using method.y_eq k
    _ = (1 / method.gamma k) •
          ((method.alpha k * method.gamma k) • method.v k +
            ((1 - method.alpha k) * method.gamma k) • method k) := by
          rw [method.gamma_succ k]
          ring_nf
    _ = method.alpha k • method.v k + (1 - method.alpha k) • method k := by
          have hcoef_v :
              (1 / method.gamma k) * (method.alpha k * method.gamma k) = method.alpha k := by
            field_simp [hgamma_ne]
          have hcoef_x :
              (1 / method.gamma k) * ((1 - method.alpha k) * method.gamma k) =
                1 - method.alpha k := by
            field_simp [hgamma_ne]
          rw [smul_add, smul_smul, smul_smul, hcoef_v, hcoef_x]

/-- Helper for Theorem 2.26: the monotone comparison chain from `y_m` down to the actual iterate
`x_{m+1}` yields three explicit gradient-square terms above the minimizer. -/
private lemma monotoneConstantStepSchemeIA_stage_objective_drop_to_minimizer
    {L : NNReal} {f : E → ℝ}
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    f (method.y m) - f xStar ≥
      (1 / (2 * (L : ℝ))) *
        (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
          ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
          ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
  -- Package the exact source chain
  -- `x_{m+1} ≤ ŷ_m ≤ x̂_{m+1} ≤ y_m`
  -- into one inequality that already ends at the minimizer `xStar`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hx_succ_desc :
      f (method.x (m + 1)) ≤
        f (monotoneConstantStepSchemeIAYHat f L x0 m) -
          (1 / (2 * (L : ℝ))) *
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) := by
    -- Rewrite the owner iterate back to the source successor formula before applying descent.
    change f (monotoneConstantStepSchemeIAX f L x0 (m + 1)) ≤
      f (monotoneConstantStepSchemeIAYHat f L x0 m) -
        (1 / (2 * (L : ℝ))) *
          ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ)
    simpa [monotoneConstantStepSchemeIAX_succ] using
      gradient_step_value_descent_of_lipschitzGradient
        f hL (fun x ↦ (hgrad x).differentiableAt) (by simpa using hgrad_lipschitz)
        (monotoneConstantStepSchemeIAYHat f L x0 m)
  have hyHat_le_xHat :
      f (monotoneConstantStepSchemeIAYHat f L x0 m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) :=
    monotoneConstantStepSchemeIAYHat_objective_le_xHat f L x0 m
  have hxHat_desc :
      f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) ≤
        f (method.y m) -
          (1 / (2 * (L : ℝ))) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    simpa [method, monotoneConstantStepSchemeIAXHat_succ] using
      gradient_step_value_descent_of_lipschitzGradient
        f hL (fun x ↦ (hgrad x).differentiableAt) (by simpa using hgrad_lipschitz)
        (method.y m)
  have hx_gap :
      f xStar +
          (1 / (2 * (L : ℝ))) * ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) ≤
        f (method.x (m + 1)) := by
    -- Insert the actual iterate into the local smooth minimizer gap.
    exact monotoneConstantStepSchemeIA_objective_gap_ge_gradient_sq_half_div_L
      hL hgrad hgrad_lipschitz xStar hxStar (method.x (m + 1))
  linarith

/-- Helper for Theorem 2.26: the bridged owner center update has the smooth-convex source form
`v_{k+1} = v_k - (α_k / γ_{k+1}) ∇ f(y_k)`. -/
private lemma monotoneConstantStepSchemeIA_center_step_eq_sub_weighted_gradient
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {k : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    method.v (k + 1) =
      method.v k - (method.alpha k / method.gamma (k + 1)) • ∇ f (method.y k) := by
  -- Rewrite the owner successor once so the remaining Lyapunov algebra sees a single gradient step.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hgamma_next :
      method.gamma (k + 1) = method.weight (k + 1) * (3 * (L : ℝ)) := by
    simpa [method] using method.gamma_sub_mu_eq_weight_mul_initial_gap (k + 1)
  have hgamma_next_ne : method.gamma (k + 1) ≠ 0 := by
    rw [hgamma_next]
    exact mul_ne_zero (method.weight_pos (k + 1)).ne' (by positivity)
  calc
    method.v (k + 1)
        = (1 / method.gamma (k + 1)) •
            (((1 - method.alpha k) * method.gamma k) • method.v k -
              method.alpha k • ∇ f (method.y k)) := by
            simpa [method] using method.v_succ k
    _ = (1 / method.gamma (k + 1)) •
          (method.gamma (k + 1) • method.v k -
            method.alpha k • ∇ f (method.y k)) := by
          rw [method.gamma_succ k]
          ring_nf
    _ = (1 / method.gamma (k + 1)) • (method.gamma (k + 1) • method.v k) -
          (1 / method.gamma (k + 1)) • (method.alpha k • ∇ f (method.y k)) := by
          rw [smul_sub]
    _ = method.v k - (method.alpha k / method.gamma (k + 1)) • ∇ f (method.y k) := by
          rw [smul_smul, one_div, inv_mul_cancel₀ hgamma_next_ne, one_smul]
          rw [smul_smul]
          congr 1
          field_simp [hgamma_next_ne]

/-- Helper for Theorem 2.26: the `v_m - y_m` part of the mixed inner product is exactly the
source tangent-plane term against the current iterate `x_m`. -/
private lemma monotoneConstantStepSchemeIA_v_minus_y_inner_ge_scaled_objective_drop
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - method.y m) ≥
      (1 - method.alpha m) * (f (method.y m) - f (method m)) := by
  -- Rewrite `y_m = α_m v_m + (1 - α_m) x_m`, then apply the tangent-plane lower bound at `y_m`
  -- to the current iterate `x_m`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hfactor_nonneg : 0 ≤ 1 - method.alpha m := by
    linarith [(method.alpha_mem_Ioo m).2]
  have htangent :
      f (method.y m) + inner ℝ (∇ f (method.y m)) (method m - method.y m) ≤
        f (method m) := by
    have hlower :=
      ConvexOn.lower_tangent_plane_of_hasGradientWithinAt hconvex
        (method.y m) (by simp) (∇ f (method.y m))
        ((hasGradientWithinAt_univ).2 (hgrad (method.y m)))
        (method m) (by simp)
    linarith
  have htangent_scaled :
      (1 - method.alpha m) *
          (f (method.y m) + inner ℝ (∇ f (method.y m)) (method m - method.y m)) ≤
        (1 - method.alpha m) * f (method m) := by
    exact mul_le_mul_of_nonneg_left htangent hfactor_nonneg
  have hcancel_vec :
      (1 - method.alpha m) • (method m - method.y m) +
        method.alpha m • (method.v m - method.y m) = 0 := by
    rw [monotoneConstantStepSchemeIA_y_eq_alpha_smul_v_add_one_sub_smul_x
      (f := f) (L := L) x0 (k := m) hL hgrad hgrad_lipschitz]
    module
  have hcancel_inner :
      (1 - method.alpha m) * inner ℝ (∇ f (method.y m)) (method m - method.y m) +
        method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - method.y m) = 0 := by
    have hinner :=
      congrArg (fun z ↦ inner ℝ (∇ f (method.y m)) z) hcancel_vec
    simpa [inner_add_right, inner_smul_right] using hinner
  have hdom :
      (1 - method.alpha m) * f (method.y m) +
          (1 - method.alpha m) * inner ℝ (∇ f (method.y m)) (method m - method.y m) ≤
        (1 - method.alpha m) * f (method m) := by
    simpa [mul_add] using htangent_scaled
  linarith

/-- Helper for Theorem 2.26: the iterate-window minimum controls the squared gradient at the
current iterate `x_m`. -/
private lemma monotoneConstantStepSchemeIA_minGradientNorm_sq_le_current
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m T : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hmT : m < T) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) ≤
      ‖∇ f (method m)‖ ^ (2 : ℕ) := by
  -- Square the window bound at the current iterate `x_m`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
  have hbound' : g0 ≤ ‖∇ f (monotoneConstantStepSchemeIAX f L x0 m)‖ := by
    simpa [g0] using
      minGradientNormAlongIterates.le
        f (monotoneConstantStepSchemeIAX f L x0) (Nat.zero_le T)
        (Nat.zero_le m) (Nat.le_of_lt hmT)
  have hbound : g0 ≤ ‖∇ f (method m)‖ := by
    simpa [method] using hbound'
  have hg0_nonneg : 0 ≤ g0 := by
    simpa [g0] using monotoneConstantStepSchemeIA_minGradientNorm_nonneg (f := f) x0 T
  -- Monotonicity of squaring on nonnegative reals upgrades the window bound to squared norms.
  gcongr
  exact hbound

/-- Helper for Theorem 2.26: the iterate-window minimum controls the squared gradient at the
successor iterate `x_{m+1}`. -/
private lemma monotoneConstantStepSchemeIA_minGradientNorm_sq_le_next
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m T : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hmT : m < T) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) ≤
      ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) := by
  -- Square the window bound at the successor iterate `x_{m+1}`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
  have hbound' : g0 ≤ ‖∇ f (monotoneConstantStepSchemeIAX f L x0 (m + 1))‖ := by
    simpa [g0] using
      minGradientNormAlongIterates.le
        f (monotoneConstantStepSchemeIAX f L x0) (Nat.zero_le T)
        (Nat.zero_le (m + 1)) hmT
  have hbound : g0 ≤ ‖∇ f (method.x (m + 1))‖ := by
    -- Match the owner successor spelling with the source iterate spelling before squaring.
    change g0 ≤ ‖∇ f (monotoneConstantStepSchemeIAX f L x0 (m + 1))‖
    exact hbound'
  have hg0_nonneg : 0 ≤ g0 := by
    simpa [g0] using monotoneConstantStepSchemeIA_minGradientNorm_nonneg (f := f) x0 T
  -- Monotonicity of squaring on nonnegative reals upgrades the window bound to squared norms.
  gcongr
  exact hbound

/-- Helper for Theorem 2.26: the stage objective gap splits exactly along the source chain
`y_m → x̂_{m+1} → ŷ_m → x_{m+1}` together with the current-iterate correction term. -/
private lemma monotoneConstantStepSchemeIA_stage_objective_gap_split
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    f (method.y m) -
        ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar) =
      (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
          f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
        method.alpha m *
          (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
        method.alpha m * (f (method.x (m + 1)) - f xStar) +
        (1 - method.alpha m) *
          (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m)) := by
  -- Expand around the selected comparison point `ŷ_m` so the unresolved compensation term is
  -- isolated explicitly.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  ring

/-- Helper for Theorem 2.26: regroup the exact stage split into the lead descent
`f (y_m) - f (x̂_{m+1})` plus the remaining selected-point block. -/
private lemma monotoneConstantStepSchemeIA_stage_gap_eq_leadDescent_add_selectedPointBlock
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    f (method.y m) -
        ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar) =
      (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        ((f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
            f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
          method.alpha m *
            (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
          method.alpha m * (f (method.x (m + 1)) - f xStar) +
          (1 - method.alpha m) *
            (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m))) := by
  -- Keep the exact source-chain split, but package the last four terms as one selected-point
  -- block so the later proof can bound it branchwise.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  ring

/-- Helper for Theorem 2.26: the lead term `f (y_m) - f (x̂_{m+1})` already contributes the
current `‖∇ f (y_m)‖²` piece of the textbook coefficient. -/
private lemma monotoneConstantStepSchemeIA_leadDescent_lower_bound
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) *
        (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) ≥
      ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Rewrite `x̂_{m+1}` as the reciprocal-`L` gradient step from `y_m`, then apply the standard
  -- descent estimate at `y_m`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hdesc :
      f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) ≤
        f (method.y m) -
          (1 / (2 * (L : ℝ))) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    simpa [method, monotoneConstantStepSchemeIAXHat_succ] using
      gradient_step_value_descent_of_lipschitzGradient
        f hL (fun x ↦ (hgrad x).differentiableAt) (by simpa using hgrad_lipschitz)
        (method.y m)
  have hgap :
      (1 / (2 * (L : ℝ))) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) ≤
        f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
    linarith
  have hscaled :=
    mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * (L : ℝ) by positivity)
  have hcoeff :
      2 * (L : ℝ) * ((1 / (2 * (L : ℝ))) * ‖∇ f (method.y m)‖ ^ (2 : ℕ)) =
        ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    field_simp [hL.ne']
  calc
    ‖∇ f (method.y m)‖ ^ (2 : ℕ)
        = 2 * (L : ℝ) * ((1 / (2 * (L : ℝ))) * ‖∇ f (method.y m)‖ ^ (2 : ℕ)) := by
            rw [hcoeff]
    _ ≤ 2 * (L : ℝ) *
          (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) := by
            simpa [mul_assoc] using hscaled

/-- Helper for Theorem 2.26: in the `ŷ_m = x_m` branch, the selected-point block collapses to
the comparison term `f (x̂_{m+1}) - f (x_m)` plus the weighted current minimizer gap. -/
private lemma monotoneConstantStepSchemeIA_selectedPointBlock_eq_choose_x
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hsel :
      f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
          f L x0 hL hgrad hgrad_lipschitz) m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
        f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
      method.alpha m *
        (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
      method.alpha m * (f (method.x (m + 1)) - f xStar) +
      (1 - method.alpha m) *
        (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m)) =
      (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        method.alpha m * (f (method m) - f xStar) := by
  -- Once the selected point is `x_m`, the middle two terms telescope across `x_{m+1}` and the
  -- correction term vanishes.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  simp [method, monotoneConstantStepSchemeIAYHat_eq_if, hsel]
  ring

/-- Helper for Theorem 2.26: in the `ŷ_m = x̂_{m+1}` branch, the selected-point block collapses
to the weighted `x̂_{m+1}` minimizer gap plus the branch comparison term against `x_m`. -/
private lemma monotoneConstantStepSchemeIA_selectedPointBlock_eq_choose_xHat
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hsel :
      ¬ f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
            f L x0 hL hgrad hgrad_lipschitz) m) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
        f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
      method.alpha m *
        (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
      method.alpha m * (f (method.x (m + 1)) - f xStar) +
      (1 - method.alpha m) *
        (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m)) =
      method.alpha m *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar) +
        (1 - method.alpha m) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) := by
  -- Once the selected point is `x̂_{m+1}`, the first term vanishes and the remaining three terms
  -- telescope against `x_{m+1}`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  simp [method, monotoneConstantStepSchemeIAYHat_eq_if, hsel]
  ring

/-- Helper for Theorem 2.26: regardless of the comparison branch, the selected-point block can be
rewritten as the explicit comparison term `f (x̂_{m+1}) - f (x_m)` plus the weighted current
minimizer gap. -/
private lemma monotoneConstantStepSchemeIA_selectedPointBlock_eq_comparison_add_currentGap
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
        f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
      method.alpha m *
        (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
      method.alpha m * (f (method.x (m + 1)) - f xStar) +
      (1 - method.alpha m) *
        (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m)) =
      (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        method.alpha m * (f (method m) - f xStar) := by
  -- Route correction: keep the current-gap term explicit before any branch-specific scalar
  -- closure, instead of collapsing immediately to the reopened bonus surface.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  by_cases hsel :
      f (method m) ≤ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))
  · -- In the `choose_x` branch this is exactly the existing branch-local simplification.
    simpa [method] using
      monotoneConstantStepSchemeIA_selectedPointBlock_eq_choose_x
        (f := f) (L := L) xStar x0 (m := m) hL hgrad hgrad_lipschitz hsel
  · have hbranch :
        (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
            f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
          method.alpha m *
            (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
          method.alpha m * (f (method.x (m + 1)) - f xStar) +
          (1 - method.alpha m) *
            (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m)) =
        method.alpha m *
            (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar) +
          (1 - method.alpha m) *
            (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) := by
      -- The `choose_xHat` branch gives the weighted selected-gap form, which is algebraically
      -- equivalent to the comparison-plus-current-gap surface used below.
      simpa [method] using
        monotoneConstantStepSchemeIA_selectedPointBlock_eq_choose_xHat
          (f := f) (L := L) xStar x0 (m := m) hL hgrad hgrad_lipschitz hsel
    rw [hbranch]
    ring

/-- Helper for Theorem 2.26: the comparison term plus the weighted current minimizer gap can be
repacked as the weighted selected-gap term together with a residual weighted comparison term. -/
private lemma
    monotoneConstantStepSchemeIA_comparison_add_currentGap_eq_selectedGap_add_weightedComparison
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        method.alpha m * (f (method m) - f xStar) =
      method.alpha m *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar) +
        (1 - method.alpha m) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) := by
  -- Keep the `choose_xHat` residual on the selected-gap surface instead of normalizing away the
  -- signed comparison term too early.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  ring

/-- Helper for Theorem 2.26: the lead descent term and the explicit comparison term telescope
back to the direct gap from `y_m` to the current iterate `x_m`. -/
private lemma monotoneConstantStepSchemeIA_leadDescent_add_comparison_eq_leadToCurrent
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) =
      2 * (L : ℝ) * (f (method.y m) - f (method m)) := by
  -- This algebraic telescope is the stable owner-level normal form behind both branch closures.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  ring

/-- Helper for Theorem 2.26: the exact stage objective gap can be rewritten directly as the lead
descent term, the explicit comparison term, and the weighted current minimizer gap. -/
private lemma monotoneConstantStepSchemeIA_stage_gap_eq_leadDescent_add_comparison_add_currentGap
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    f (method.y m) -
        ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar) =
      (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        method.alpha m * (f (method m) - f xStar) := by
  -- Rewrite the stage gap through the selected-point block once, then replace that block by the
  -- stable comparison-plus-current-gap normal form.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  calc
    f (method.y m) - ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar)
        =
      (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        ((f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
            f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
          method.alpha m *
            (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
          method.alpha m * (f (method.x (m + 1)) - f xStar) +
          (1 - method.alpha m) *
            (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m))) := by
            simpa [method] using
              monotoneConstantStepSchemeIA_stage_gap_eq_leadDescent_add_selectedPointBlock
                (f := f) (L := L) xStar x0 (m := m) hL hgrad hgrad_lipschitz
    _ =
      (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        ((f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
          method.alpha m * (f (method m) - f xStar)) := by
            rw [monotoneConstantStepSchemeIA_selectedPointBlock_eq_comparison_add_currentGap
              (f := f) (L := L) xStar x0 (m := m) hL hgrad hgrad_lipschitz]
    _ =
      (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        method.alpha m * (f (method m) - f xStar) := by
            ring

/-- Helper for Theorem 2.26: convexity and an `L`-Lipschitz gradient give the standard quadratic
lower bound at the base point `y`. -/
private lemma monotoneConstantStepSchemeIA_gradientQuadraticLowerBound
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (x y : E)
    (hL : 0 < (L : ℝ)) :
    f y + inner ℝ (∇ f y) (x - y) +
        (1 / (2 * (L : ℝ))) * ‖∇ f x - ∇ f y‖ ^ (2 : ℕ) ≤
      f x := by
  -- Compare the lower tangent inequality at `y` with the smooth upper model at
  -- `x - (1 / L) (∇ f x - ∇ f y)`.
  let d : E := ∇ f x - ∇ f y
  let z : E := x - (1 / (L : ℝ)) • d
  have hfC1 : ContDiff ℝ 1 f := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun u ↦ (hgrad u).differentiableAt, ?_⟩
    have hEq : fderiv ℝ f = fun u ↦ InnerProductSpace.toDual ℝ E (∇ f u) := by
      funext u
      simpa using (hgrad u).hasFDerivAt.fderiv
    have hcont : Continuous (fun u ↦ InnerProductSpace.toDual ℝ E (∇ f u)) :=
      (InnerProductSpace.toDual ℝ E).continuous.comp hgrad_lipschitz.continuous
    simpa [hEq] using hcont
  have hupper :
      f z ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    have h :=
      taylor_upper_bound_of_contDiffOne_withLipschitzGradient hfC1 hgrad_lipschitz x z
    have hz : z - x = -((1 / (L : ℝ)) • d) := by
      simp [z]
    calc
      f z ≤ f x + inner ℝ (∇ f x) (z - x) + ((L : ℝ) / 2) * ‖z - x‖ ^ (2 : ℕ) := by
        simpa [firstOrderTaylorModelAt_apply] using h
      _ = f x + inner ℝ (∇ f x) (-((1 / (L : ℝ)) • d)) +
            ((L : ℝ) / 2) * ‖-((1 / (L : ℝ)) • d)‖ ^ (2 : ℕ) := by rw [hz]
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            ((L : ℝ) / 2) * ((1 / (L : ℝ)) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ)) := by
            simp [inner_smul_right, norm_smul, sq]
            ring
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
            field_simp [hL.ne']
  have hlower :
      f z ≥
        f y + inner ℝ (∇ f y) (x - y) -
          (1 / (L : ℝ)) * inner ℝ (∇ f y) d := by
    have h :=
      hconvex.lower_tangent_plane_of_hasGradientWithinAt
        y (by simp) (∇ f y) ((hasGradientWithinAt_univ).2 (hgrad y)) z (by simp)
    have hz : z - y = (x - y) - (1 / (L : ℝ)) • d := by
      simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    calc
      f z ≥ f y + inner ℝ (∇ f y) (z - y) := h
      _ = f y + inner ℝ (∇ f y) ((x - y) - (1 / (L : ℝ)) • d) := by rw [hz]
      _ = f y + inner ℝ (∇ f y) (x - y) -
            (1 / (L : ℝ)) * inner ℝ (∇ f y) d := by
            rw [inner_sub_right, inner_smul_right]
            ring
  have hinner :
      inner ℝ (∇ f x) d = inner ℝ (∇ f y) d + ‖d‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (∇ f x) d = inner ℝ (d + ∇ f y) d := by
        congr 1
        dsimp [d]
        abel_nf
      _ = inner ℝ d d + inner ℝ (∇ f y) d := by
        rw [inner_add_left]
      _ = inner ℝ (∇ f y) d + ‖d‖ ^ (2 : ℕ) := by
        simp [inner_self_eq_norm_sq_to_K, add_comm]
  have hupper' :
      f z ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
    calc
      f z ≤
          f x - (1 / (L : ℝ)) * inner ℝ (∇ f x) d +
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := hupper
      _ = f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
            (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) := by
            rw [hinner]
            ring
  have hmid :
      f y + inner ℝ (∇ f y) (x - y) -
          (1 / (L : ℝ)) * inner ℝ (∇ f y) d ≤
        f x - (1 / (L : ℝ)) * inner ℝ (∇ f y) d -
          (1 / (2 * (L : ℝ))) * ‖d‖ ^ (2 : ℕ) :=
    le_trans hlower hupper'
  linarith

/-- Helper for Theorem 2.26: the `v_m - y_m` part of the mixed inner product gains the
quadratic gradient-difference bonus missing from the false selected-point route. -/
private lemma monotoneConstantStepSchemeIA_vMinusYInnerWithBonus
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * method.alpha m *
        inner ℝ (∇ f (method.y m)) (method.v m - method.y m) ≥
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Rewrite `α_m (v_m - y_m)` as `(1 - α_m) (y_m - x_m)` and then apply the quadratic lower
  -- bound at `y_m` against the current iterate `x_m`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hfactor_nonneg : 0 ≤ 1 - method.alpha m := by
    linarith [(method.alpha_mem_Ioo m).2]
  have hquad :
      f (method.y m) + inner ℝ (∇ f (method.y m)) (method m - method.y m) +
          (1 / (2 * (L : ℝ))) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) ≤
        f (method m) := by
    simpa [method] using
      monotoneConstantStepSchemeIA_gradientQuadraticLowerBound
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz (method m) (method.y m) hL
  have hinner :
      inner ℝ (∇ f (method.y m)) (method.y m - method m) ≥
        f (method.y m) - f (method m) +
          (1 / (2 * (L : ℝ))) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) := by
    have hquad' := hquad
    have hneg :
        inner ℝ (∇ f (method.y m)) (method m - method.y m) =
          -inner ℝ (∇ f (method.y m)) (method.y m - method m) := by
      rw [show method m - method.y m = -(method.y m - method m) by abel, inner_neg_right]
    rw [hneg] at hquad'
    linarith
  have hinterp_vec :
      method.alpha m • (method.v m - method.y m) =
        (1 - method.alpha m) • (method.y m - method m) := by
    rw [monotoneConstantStepSchemeIA_y_eq_alpha_smul_v_add_one_sub_smul_x
      (f := f) (L := L) x0 (k := m) hL hgrad hgrad_lipschitz]
    module
  have hinterp :
      method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - method.y m) =
        (1 - method.alpha m) * inner ℝ (∇ f (method.y m)) (method.y m - method m) := by
    have hinner_eq := congrArg (fun z ↦ inner ℝ (∇ f (method.y m)) z) hinterp_vec
    simpa [inner_smul_right] using hinner_eq
  have hmul :
      (1 - method.alpha m) *
          (f (method.y m) - f (method m) +
            (1 / (2 * (L : ℝ))) *
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) ≤
        method.alpha m * inner ℝ (∇ f (method.y m)) (method.v m - method.y m) := by
    have hmul' := mul_le_mul_of_nonneg_left hinner hfactor_nonneg
    simpa [hinterp] using hmul'
  have hscaled := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 2 * (L : ℝ) by positivity)
  have hright :
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) =
        2 * (L : ℝ) *
          ((1 - method.alpha m) *
            (f (method.y m) - f (method m) +
              (1 / (2 * (L : ℝ))) *
                ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ))) := by
    field_simp [hL.ne']
  rw [hright]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Helper for Theorem 2.26: the `y_m - xStar` part of the mixed inner product already carries
the minimizer objective gap together with the `‖∇ f (y_m)‖²` bonus. -/
private lemma monotoneConstantStepSchemeIA_yMinusXStarInnerWithBonus
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * method.alpha m *
        inner ℝ (∇ f (method.y m)) (method.y m - xStar) ≥
      2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Specialize the same quadratic lower bound at the minimizer, where the gradient vanishes.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hgrad0 : ∇ f xStar = 0 := isMinOn_gradient_eq_zero hxStar
  have hquad :
      f (method.y m) + inner ℝ (∇ f (method.y m)) (xStar - method.y m) +
          (1 / (2 * (L : ℝ))) * ‖∇ f xStar - ∇ f (method.y m)‖ ^ (2 : ℕ) ≤
        f xStar := by
    simpa [method] using
      monotoneConstantStepSchemeIA_gradientQuadraticLowerBound
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar (method.y m) hL
  have hinner :
      inner ℝ (∇ f (method.y m)) (method.y m - xStar) ≥
        f (method.y m) - f xStar +
          (1 / (2 * (L : ℝ))) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    have hquad' := hquad
    have hneg :
        inner ℝ (∇ f (method.y m)) (xStar - method.y m) =
          -inner ℝ (∇ f (method.y m)) (method.y m - xStar) := by
      rw [show xStar - method.y m = -(method.y m - xStar) by abel, inner_neg_right]
    rw [hneg, hgrad0, zero_sub, norm_neg] at hquad'
    linarith
  have hscaled :=
    mul_le_mul_of_nonneg_left hinner
      (mul_nonneg (show 0 ≤ 2 * (L : ℝ) by positivity) (method.alpha_pos m).le)
  have hright :
      2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) =
        2 * (L : ℝ) * method.alpha m *
          (f (method.y m) - f xStar +
            (1 / (2 * (L : ℝ))) * ‖∇ f (method.y m)‖ ^ (2 : ℕ)) := by
    field_simp [hL.ne']
  rw [hright]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Helper for Theorem 2.26: combine the `y_m - xStar` bonus with the monotone selected-point
descent chain so the `ŷ_m` and `x_{m+1}` gradient squares remain explicit. -/
private lemma monotoneConstantStepSchemeIA_yMinusXStarInnerWithStageSquares
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * method.alpha m *
        inner ℝ (∇ f (method.y m)) (method.y m - xStar) ≥
      method.alpha m *
        (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
          ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
          ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
  -- Keep the selected-point chain in the owner spelling before any branch rewrite of `ŷ_m`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hyxStar :
      2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.y m - xStar) ≥
        2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Start from the basic minimizer-gap bonus at `y_m`.
    simpa [method] using
      monotoneConstantStepSchemeIA_yMinusXStarInnerWithBonus
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar hxStar x0 (m := m) hL
  have hdrop :
      f (method.y m) - f xStar ≥
        (1 / (2 * (L : ℝ))) *
          (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
    -- The monotone chain `y_m → ŷ_m → x_{m+1} → xStar` already contributes three squares.
    simpa [method] using
      monotoneConstantStepSchemeIA_stage_objective_drop_to_minimizer
        (f := f) (L := L) hgrad hgrad_lipschitz xStar hxStar x0 (m := m) hL
  have hdrop_scaled :
      2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) ≥
        method.alpha m *
          (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
    -- Scale the chain inequality by `2L α_m` and cancel the reciprocal `2L`.
    have hscaled :=
      mul_le_mul_of_nonneg_left hdrop
        (mul_nonneg (show 0 ≤ 2 * (L : ℝ) by positivity) (method.alpha_pos m).le)
    have hcoeff :
        (2 * (L : ℝ) * method.alpha m) *
            ((1 / (2 * (L : ℝ))) *
              (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
                ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
                ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))) =
          method.alpha m *
              (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
                ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
                ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
      field_simp [hL.ne']
    rw [hcoeff] at hscaled
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  -- Add the explicit `‖∇ f (y_m)‖²` bonus to the selected-point square package.
  nlinarith

/-- Helper for Theorem 2.26: in the `ŷ_m = x_m` branch, the lead descent term can be compared
directly with the current iterate because the selected point does not improve on `x_m`. -/
private lemma monotoneConstantStepSchemeIA_chooseXBranchLeadToCurrent_lower_bound
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hsel :
      f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
          f L x0 hL hgrad hgrad_lipschitz) m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (f (method.y m) - f (method m)) ≥
      ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Compare `x_m` with `x̂_{m+1}` using the branch condition, then reuse the standard lead
  -- descent bound against `x̂_{m+1}`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hlead :
      2 * (L : ℝ) *
          (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) ≥
        ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    simpa [method] using
      monotoneConstantStepSchemeIA_leadDescent_lower_bound
        (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz
  have hcompare :
      f (method.y m) - f (method m) ≥
        f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
    linarith
  have hscaled :=
    mul_le_mul_of_nonneg_left hcompare (show 0 ≤ 2 * (L : ℝ) by positivity)
  exact le_trans hlead hscaled

/-- Helper for Theorem 2.26: in the `ŷ_m = x_m` branch, the current minimizer gap already
contains the descent from `x_m` to `x_{m+1}` and the successor minimizer gap. -/
private lemma monotoneConstantStepSchemeIA_chooseXBranchCurrentGap_lower_bound
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hxStar : IsMinOn f Set.univ xStar)
    (hsel :
      f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
          f L x0 hL hgrad hgrad_lipschitz) m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (f (method m) - f xStar) ≥
      ‖∇ f (method m)‖ ^ (2 : ℕ) + ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) := by
  -- Rewrite `x_{m+1}` as the gradient step from `x_m` that is active in the `choose_x` branch.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hsel' :
      f (monotoneConstantStepSchemeIAX f L x0 m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
    simpa [method] using hsel
  have hxsucc :
      method.x (m + 1) = method.x m - (1 / (L : ℝ)) • ∇ f (method.x m) := by
    change monotoneConstantStepSchemeIAX f L x0 (m + 1) =
      monotoneConstantStepSchemeIAX f L x0 m -
        (1 / (L : ℝ)) • ∇ f (monotoneConstantStepSchemeIAX f L x0 m)
    rw [monotoneConstantStepSchemeIAX_succ, monotoneConstantStepSchemeIAYHat_eq_if, if_pos hsel']
  have hdesc0 :
      f (method.x m - (1 / (L : ℝ)) • ∇ f (method.x m)) ≤
        f (method.x m) - (1 / (2 * (L : ℝ))) * ‖∇ f (method.x m)‖ ^ (2 : ℕ) := by
    simpa using
      gradient_step_value_descent_of_lipschitzGradient
        f hL (fun x ↦ (hgrad x).differentiableAt) (by simpa using hgrad_lipschitz)
        (method.x m)
  have hdesc :
      f (method.x (m + 1)) ≤
        f (method.x m) - (1 / (2 * (L : ℝ))) * ‖∇ f (method.x m)‖ ^ (2 : ℕ) := by
    simpa [hxsucc] using hdesc0
  have hgap :
      f xStar + (1 / (2 * (L : ℝ))) * ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) ≤
        f (method.x (m + 1)) := by
    exact monotoneConstantStepSchemeIA_objective_gap_ge_gradient_sq_half_div_L
      (f := f) (L := L) hL hgrad hgrad_lipschitz xStar hxStar (method.x (m + 1))
  have hdesc_gap :
      (1 / (2 * (L : ℝ))) * ‖∇ f (method.x m)‖ ^ (2 : ℕ) ≤
        f (method.x m) - f (method.x (m + 1)) := by
    linarith
  have hgap_gap :
      (1 / (2 * (L : ℝ))) * ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) ≤
        f (method.x (m + 1)) - f xStar := by
    linarith
  have hsum := add_le_add hdesc_gap hgap_gap
  have hsum' :
      (1 / (2 * (L : ℝ))) *
          (‖∇ f (method.x m)‖ ^ (2 : ℕ) + ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) ≤
        f (method.x m) - f xStar := by
    nlinarith [hsum]
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum' (show 0 ≤ 2 * (L : ℝ) by positivity)
  have hcoeff :
      2 * (L : ℝ) *
          ((1 / (2 * (L : ℝ))) *
            (‖∇ f (method.x m)‖ ^ (2 : ℕ) + ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))) =
        ‖∇ f (method.x m)‖ ^ (2 : ℕ) + ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) := by
    field_simp [hL.ne']
  rw [hcoeff] at hscaled
  simpa using hscaled

/-- Helper for Theorem 2.26: in the `ŷ_m = x̂_{m+1}` branch, the selected-point minimizer gap
already contains the descent from `x̂_{m+1}` to the actual next iterate. -/
private lemma monotoneConstantStepSchemeIA_chooseXHatBranchSelectedGap_lower_bound
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hxStar : IsMinOn f Set.univ xStar)
    (hsel :
      ¬ f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
            f L x0 hL hgrad hgrad_lipschitz) m) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar) ≥
      ‖∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))‖ ^ (2 : ℕ) +
        ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) := by
  -- Rewrite `x_{m+1}` as the gradient step from `x̂_{m+1}` that is active in the `choose_xHat`
  -- branch.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hsel' :
      ¬ f (monotoneConstantStepSchemeIAX f L x0 m) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
    simpa [method] using hsel
  have hxsucc :
      method.x (m + 1) =
        monotoneConstantStepSchemeIAXHat f L x0 (m + 1) -
          (1 / (L : ℝ)) • ∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
    change monotoneConstantStepSchemeIAX f L x0 (m + 1) =
      monotoneConstantStepSchemeIAXHat f L x0 (m + 1) -
        (1 / (L : ℝ)) • ∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))
    rw [monotoneConstantStepSchemeIAX_succ, monotoneConstantStepSchemeIAYHat_eq_if, if_neg hsel']
  have hdesc0 :
      f
          (monotoneConstantStepSchemeIAXHat f L x0 (m + 1) -
            (1 / (L : ℝ)) • ∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
          (1 / (2 * (L : ℝ))) *
            ‖∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))‖ ^ (2 : ℕ) := by
    simpa using
      gradient_step_value_descent_of_lipschitzGradient
        f hL (fun x ↦ (hgrad x).differentiableAt) (by simpa using hgrad_lipschitz)
        (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))
  have hdesc :
      f (method.x (m + 1)) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
          (1 / (2 * (L : ℝ))) *
            ‖∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))‖ ^ (2 : ℕ) := by
    simpa [hxsucc] using hdesc0
  have hgap :
      f xStar + (1 / (2 * (L : ℝ))) * ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) ≤
        f (method.x (m + 1)) := by
    exact monotoneConstantStepSchemeIA_objective_gap_ge_gradient_sq_half_div_L
      (f := f) (L := L) hL hgrad hgrad_lipschitz xStar hxStar (method.x (m + 1))
  have hdesc_gap :
      (1 / (2 * (L : ℝ))) * ‖∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))‖ ^ (2 : ℕ) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method.x (m + 1)) := by
    linarith
  have hgap_gap :
      (1 / (2 * (L : ℝ))) * ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) ≤
        f (method.x (m + 1)) - f xStar := by
    linarith
  have hsum := add_le_add hdesc_gap hgap_gap
  have hsum' :
      (1 / (2 * (L : ℝ))) *
          (‖∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar := by
    nlinarith [hsum]
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum' (show 0 ≤ 2 * (L : ℝ) by positivity)
  have hcoeff :
      2 * (L : ℝ) *
          ((1 / (2 * (L : ℝ))) *
            (‖∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))) =
        ‖∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))‖ ^ (2 : ℕ) +
          ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ) := by
    field_simp [hL.ne']
  rw [hcoeff] at hscaled
  simpa using hscaled

/-- Helper for Theorem 2.26: in the `ŷ_m = x_m` branch, the stalled bonus surface rewrites so
the comparison term `f (x̂_{m+1}) - f (x_m)` remains explicit. -/
private lemma monotoneConstantStepSchemeIA_stageBonusSurface_eq_choose_x
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hsel :
      f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
          f L x0 hL hgrad hgrad_lipschitz) m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) =
      (1 - method.alpha m) *
          (2 * (L : ℝ) *
              (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
            2 * (L : ℝ) *
              (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (method m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
  -- Rewrite `ŷ_m = x_m` and telescope the two objective differences before the scalar cleanup.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hsel' :
      f (monotoneConstantStepSchemeIAX f L x0 m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
    simpa [method] using hsel
  have hyhat :
      monotoneConstantStepSchemeIAYHat f L x0 m = monotoneConstantStepSchemeIAX f L x0 m := by
    rw [monotoneConstantStepSchemeIAYHat_eq_if, if_pos hsel']
  have hlead :
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) * (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) =
      2 * (L : ℝ) * (f (method.y m) - f (method m)) := by
    simpa [method] using
      monotoneConstantStepSchemeIA_leadDescent_add_comparison_eq_leadToCurrent
        (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz
  calc
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) * ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
          method.alpha m *
            (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))
        =
      (1 - method.alpha m) *
          (2 * (L : ℝ) * (f (method.y m) - f (method m)) +
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (method m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
          have hxcur : monotoneConstantStepSchemeIAX f L x0 m = method.x m := rfl
          rw [hyhat]
          rw [hxcur]
          ring
    _ =
      (1 - method.alpha m) *
          (2 * (L : ℝ) *
              (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
            2 * (L : ℝ) *
              (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (method m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
          rw [hlead]

/-- Helper for Theorem 2.26: in the `ŷ_m = x̂_{m+1}` branch, the stalled bonus surface rewrites
so the signed comparison term `f (x̂_{m+1}) - f (x_m)` remains explicit. -/
private lemma monotoneConstantStepSchemeIA_stageBonusSurface_eq_choose_xHat
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hsel :
      ¬ f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
            f L x0 hL hgrad hgrad_lipschitz) m) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) =
      (1 - method.alpha m) *
          (2 * (L : ℝ) *
              (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
            2 * (L : ℝ) *
              (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
  -- Rewrite `ŷ_m = x̂_{m+1}` and telescope the same objective split with the opposite branch.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hsel' :
      ¬ f (monotoneConstantStepSchemeIAX f L x0 m) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
    simpa [method] using hsel
  have hyhat :
      monotoneConstantStepSchemeIAYHat f L x0 m =
        monotoneConstantStepSchemeIAXHat f L x0 (m + 1) := by
    rw [monotoneConstantStepSchemeIAYHat_eq_if, if_neg hsel']
  rw [hyhat]
  ring_nf

/-- Helper for Theorem 2.26: the `choose_x` branch keeps the comparison term
`f (x̂_{m+1}) - f (x_m)` nonnegative. -/
private lemma monotoneConstantStepSchemeIA_chooseXBranchComparison_nonneg
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hsel :
      f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
          f L x0 hL hgrad hgrad_lipschitz) m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    0 ≤ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m) := by
  -- Keep the branch sign as a standalone fact so the final closure can use it directly.
  dsimp
  linarith

/-- Helper for Theorem 2.26: the `choose_xHat` branch keeps the comparison term
`f (x̂_{m+1}) - f (x_m)` nonpositive. -/
private lemma monotoneConstantStepSchemeIA_chooseXHatBranchComparison_nonpos
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hsel :
      ¬ f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
            f L x0 hL hgrad hgrad_lipschitz) m) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m) ≤ 0 := by
  -- Keep the opposite branch sign as a standalone fact so the final closure can use it directly.
  dsimp
  linarith

/-- Helper for Theorem 2.26: after reopening the `choose_x` bonus surface, the available branch
facts already recover the lead `‖∇ f (y_m)‖²` term and the weighted current/next gradient window.
-/
private lemma monotoneConstantStepSchemeIA_chooseXBranchSurface_lower_bound
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hsel :
      f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
          f L x0 hL hgrad hgrad_lipschitz) m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    (1 - method.alpha m) *
        (2 * (L : ℝ) *
            (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
          2 * (L : ℝ) *
            (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
      method.alpha m *
        (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
          ‖∇ f (method m)‖ ^ (2 : ℕ) +
          ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) ≥
      (1 + method.alpha m) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m *
          (‖∇ f (method m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
  -- Keep the `choose_x` branch closure at the full reopened surface: the lead descent handles
  -- `‖∇ f (y_m)‖²`, the comparison term is nonnegative, and the remaining weighted window stays
  -- explicit for the final theorem-specific scalar argument.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hlead_current :
      2 * (L : ℝ) * (f (method.y m) - f (method m)) ≥
        ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- In the `choose_x` branch the lead descent can stop at `x_m`.
    simpa [method] using
      monotoneConstantStepSchemeIA_chooseXBranchLeadToCurrent_lower_bound
        (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz hsel
  have hcompare_nonneg :
      0 ≤ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m) := by
    -- The reopened comparison term has the favorable sign in the `choose_x` branch.
    simpa [method] using
      monotoneConstantStepSchemeIA_chooseXBranchComparison_nonneg
        (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz hsel
  have hdefect_nonneg :
      0 ≤ ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) := by
    positivity
  have halpha_nonneg : 0 ≤ 1 - method.alpha m := by
    linarith [(method.alpha_mem_Ioo m).2]
  have hsurface_core :
      2 * (L : ℝ) *
          (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) ≥
      ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Collapse the two objective differences back to `f (y_m) - f (x_m)` only after inserting
    -- the branch sign and the nonnegative quadratic remainder.
    nlinarith
  have hsurface_scaled :
      (1 - method.alpha m) *
          (2 * (L : ℝ) *
              (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
            2 * (L : ℝ) *
              (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) ≥
        (1 - method.alpha m) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_left hsurface_core halpha_nonneg
  nlinarith

/-- Helper for Theorem 2.26: in the `choose_x` branch, the collapsed stage surface is just the
reopened `choose_x` surface, so the previously proved reopened lower bound applies verbatim. -/
private lemma monotoneConstantStepSchemeIA_chooseXStageSurface_lower_bound
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hsel :
      f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
          f L x0 hL hgrad hgrad_lipschitz) m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    (1 - method.alpha m) *
          (2 * (L : ℝ) * (f (method.y m) - f (method m)) +
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (method m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) ≥
      (1 + method.alpha m) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m *
          (‖∇ f (method m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
  -- Freeze the branch rewrite `ŷ_m = x_m`, then reuse the already proved reopened-surface bound.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hsurface_eq :
      (1 - method.alpha m) *
            (2 * (L : ℝ) * (f (method.y m) - f (method m)) +
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
          method.alpha m *
            (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              ‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) =
        (1 - method.alpha m) *
            (2 * (L : ℝ) *
                (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
              2 * (L : ℝ) *
                (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
          method.alpha m *
            (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              ‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
    have hsel' :
        f (monotoneConstantStepSchemeIAX f L x0 m) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
      simpa [method] using hsel
    have hyhat :
        monotoneConstantStepSchemeIAYHat f L x0 m = method.x m := by
      change monotoneConstantStepSchemeIAYHat f L x0 m =
        monotoneConstantStepSchemeIAX f L x0 m
      rw [monotoneConstantStepSchemeIAYHat_eq_if, if_pos hsel']
    -- Rewrite the stage surface to the explicit `ŷ_m = x_m` branch before applying the owner
    -- branch normalization.
    calc
      (1 - method.alpha m) *
            (2 * (L : ℝ) * (f (method.y m) - f (method m)) +
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
          method.alpha m *
            (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              ‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))
          =
        2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
            (1 - method.alpha m) *
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
            method.alpha m *
              (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
                ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
                ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
              rw [hyhat]
              ring
      _ =
        (1 - method.alpha m) *
            (2 * (L : ℝ) *
                (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
              2 * (L : ℝ) *
                (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
          method.alpha m *
            (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              ‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
              simpa [method] using
                monotoneConstantStepSchemeIA_stageBonusSurface_eq_choose_x
                  (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz hsel
  have hraw :
      (1 - method.alpha m) *
            (2 * (L : ℝ) *
                (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
              2 * (L : ℝ) *
                (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
          method.alpha m *
            (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              ‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) ≥
        (1 + method.alpha m) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
          method.alpha m *
            (‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
    -- Reuse the branch-local lower bound at the reopened surface spelling.
    simpa [method] using
      monotoneConstantStepSchemeIA_chooseXBranchSurface_lower_bound
        (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz hsel
  -- The collapsed stage surface now matches the reopened branch surface exactly.
  calc
    (1 - method.alpha m) *
          (2 * (L : ℝ) * (f (method.y m) - f (method m)) +
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (method m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))
        =
      (1 - method.alpha m) *
            (2 * (L : ℝ) *
                (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
              2 * (L : ℝ) *
                (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
          method.alpha m *
            (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              ‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := hsurface_eq
    _ ≥
      (1 + method.alpha m) * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m *
          (‖∇ f (method m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := hraw

/-- Helper for Theorem 2.26: in the `ŷ_m = x_m` branch, the reopened stage bonus surface still
contains enough objective-gap mass to reach the final coefficient `(3 - α_m^2)`. -/
private lemma
    monotoneConstantStepSchemeIA_fullBonusSurface_eq_leadDescent_add_comparison_add_currentGap
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) =
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        2 * (L : ℝ) * method.alpha m * (f (method m) - f xStar) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Repackage the two objective terms as the exact stage gap before reopening that gap through the
  -- stable lead/comparison/current-gap normal form.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  calc
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
          2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ)
        =
      2 * (L : ℝ) *
          (f (method.y m) -
            ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            ring
    _ =
      2 * (L : ℝ) *
          ((f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
            (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
            method.alpha m * (f (method m) - f xStar)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            rw [monotoneConstantStepSchemeIA_stage_gap_eq_leadDescent_add_comparison_add_currentGap
              (f := f) (L := L) xStar x0 (m := m) hL hgrad hgrad_lipschitz]
    _ =
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        2 * (L : ℝ) * method.alpha m * (f (method m) - f xStar) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            ring

/-- Helper for Theorem 2.26: in the `choose_x` branch, the reopened full surface is exactly the
stage-square surface plus the explicit lead slack and current-gap slack that remain after
rewriting `ŷ_m = x_m`. -/
private lemma monotoneConstantStepSchemeIA_chooseXBranchFullSurface_eq_stageSurface_add_slacks
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) =
      ((1 - method.alpha m) *
            (2 * (L : ℝ) * (f (method.y m) - f (method m)) +
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
          method.alpha m *
            (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              ‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))) +
        method.alpha m *
          (2 * (L : ℝ) * (f (method.y m) - f (method m)) -
            ‖∇ f (method.y m)‖ ^ (2 : ℕ)) +
        method.alpha m *
          (2 * (L : ℝ) * (f (method m) - f xStar) -
            (‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))) := by
  -- Rewrite once to the `choose_x` stage surface, then isolate the two branch slacks by pure
  -- scalar algebra.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hsurface_eq :
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
          2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) =
        2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
          2 * (L : ℝ) *
            (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
          2 * (L : ℝ) * method.alpha m * (f (method m) - f xStar) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Reopen the stage gap exactly once, so the current-gap block remains explicit.
    simpa [method] using
      monotoneConstantStepSchemeIA_fullBonusSurface_eq_leadDescent_add_comparison_add_currentGap
        (f := f) (L := L) xStar x0 (m := m) hL hgrad hgrad_lipschitz
  have hlead :
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
          2 * (L : ℝ) *
            (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) =
        2 * (L : ℝ) * (f (method.y m) - f (method m)) := by
    -- Collapse the lead/comparison pair only after the branch rewrite has been frozen.
    simpa [method] using
      monotoneConstantStepSchemeIA_leadDescent_add_comparison_eq_leadToCurrent
        (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz
  calc
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
          2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ)
        =
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        2 * (L : ℝ) * method.alpha m * (f (method m) - f xStar) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := hsurface_eq
    _ =
      2 * (L : ℝ) * (f (method.y m) - f (method m)) +
        2 * (L : ℝ) * method.alpha m * (f (method m) - f xStar) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            rw [hlead]
    _ =
      ((1 - method.alpha m) *
            (2 * (L : ℝ) * (f (method.y m) - f (method m)) +
              ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
          method.alpha m *
            (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              ‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))) +
        method.alpha m *
          (2 * (L : ℝ) * (f (method.y m) - f (method m)) -
            ‖∇ f (method.y m)‖ ^ (2 : ℕ)) +
        method.alpha m *
          (2 * (L : ℝ) * (f (method m) - f xStar) -
            (‖∇ f (method m)‖ ^ (2 : ℕ) +
              ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ))) := by
            ring

/-- Helper for Theorem 2.26: before any sign estimate in the `choose_xHat` branch, the reopened
full bonus surface can be repacked so the weighted selected-gap term is explicit. -/
private lemma monotoneConstantStepSchemeIA_chooseXHatFullSurface_eq_repackedSurface
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) =
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) * method.alpha m *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar) +
        2 * (L : ℝ) * (1 - method.alpha m) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Route correction: repack the comparison term with the weighted current minimizer gap before
  -- trying to use the `choose_xHat` sign, so the selected-gap mass is exposed once and for all.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  calc
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
          2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ)
        =
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        2 * (L : ℝ) * method.alpha m * (f (method m) - f xStar) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            simpa [method] using
              monotoneConstantStepSchemeIA_fullBonusSurface_eq_leadDescent_add_comparison_add_currentGap
                (f := f) (L := L) xStar x0 (m := m) hL hgrad hgrad_lipschitz
    _ =
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) *
          ((f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
            method.alpha m * (f (method m) - f xStar)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            ring
    _ =
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) *
          (method.alpha m *
              (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar) +
            (1 - method.alpha m) *
              (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m))) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            rw [monotoneConstantStepSchemeIA_comparison_add_currentGap_eq_selectedGap_add_weightedComparison
              (f := f) (L := L) xStar x0 (m := m) hL hgrad hgrad_lipschitz]
    _ =
      2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) * method.alpha m *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar) +
        2 * (L : ℝ) * (1 - method.alpha m) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            ring

/-- Helper for Theorem 2.26: after expanding the center-step norm and rewriting the weight ratio,
the one-step Lyapunov difference is exactly the raw scalar branch expression. -/
private lemma monotoneConstantStepSchemeIA_weightedDescentRawGoal_eq_branchDifference
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m T : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
    ((4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v (m + 1) - xStar‖ ^ (2 : ℕ) +
        16 * g0 ^ (2 : ℕ) *
          ((1 - method.toOptimalMethodRecurrence.weight (m + 1)) /
            method.toOptimalMethodRecurrence.weight (m + 1))) -
      (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v m - xStar‖ ^ (2 : ℕ) =
    (16 / method.alpha m ^ (2 : ℕ)) *
      (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
        (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
        2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - xStar)) := by
  -- Normalize the one-step Lyapunov difference before any branch split, so the only remaining
  -- work is the sign of the exact raw scalar expression.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
  have hratio :
      ((1 - method.toOptimalMethodRecurrence.weight (m + 1)) /
          method.toOptimalMethodRecurrence.weight (m + 1)) =
        (3 - method.alpha m ^ (2 : ℕ)) / (method.alpha m ^ (2 : ℕ)) := by
    -- Derive the ratio directly here so the raw-goal normal form does not depend on a later
    -- helper declaration.
    have hgamma_weight :
        method.gamma (m + 1) = method.toOptimalMethodRecurrence.weight (m + 1) * (3 * (L : ℝ)) := by
      simpa [method] using method.gamma_sub_mu_eq_weight_mul_initial_gap (m + 1)
    have hgamma_alpha :
        method.gamma (m + 1) = (L : ℝ) * method.alpha m ^ (2 : ℕ) := by
      simpa [method] using method.gamma_succ_eq_L_mul_sq m
    have hweight_eq :
        method.toOptimalMethodRecurrence.weight (m + 1) = method.alpha m ^ (2 : ℕ) / 3 := by
      have hthreeL_ne : (3 * (L : ℝ)) ≠ 0 := by
        exact mul_ne_zero (by norm_num) hL.ne'
      calc
        method.toOptimalMethodRecurrence.weight (m + 1)
            =
          (method.toOptimalMethodRecurrence.weight (m + 1) * (3 * (L : ℝ))) / (3 * (L : ℝ)) := by
                field_simp [hthreeL_ne]
        _ = ((L : ℝ) * method.alpha m ^ (2 : ℕ)) / (3 * (L : ℝ)) := by
              rw [← hgamma_weight, hgamma_alpha]
        _ = method.alpha m ^ (2 : ℕ) / 3 := by
              field_simp [hL.ne']
    have halpha_sq_ne : method.alpha m ^ (2 : ℕ) ≠ 0 := by
      exact pow_ne_zero 2 (method.alpha_pos m).ne'
    change
      (1 - ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m)) /
          ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m) =
        (3 - method.alpha m ^ (2 : ℕ)) / (method.alpha m ^ (2 : ℕ))
    rw [← method.toOptimalMethodRecurrence.weight_succ m, hweight_eq]
    field_simp [halpha_sq_ne]
  have hcenter :
      method.v (m + 1) =
        method.v m - (method.alpha m / method.gamma (m + 1)) • ∇ f (method.y m) := by
    simpa [method] using
      monotoneConstantStepSchemeIA_center_step_eq_sub_weighted_gradient
        (f := f) (L := L) x0 (k := m) hL hgrad hgrad_lipschitz
  have hgamma_alpha :
      method.gamma (m + 1) = (L : ℝ) * method.alpha m ^ (2 : ℕ) := by
    simpa [method] using method.gamma_succ_eq_L_mul_sq m
  have halpha_ne : method.alpha m ≠ 0 := (method.alpha_pos m).ne'
  have hstep_eq :
      method.v (m + 1) - xStar =
        (method.v m - xStar) -
          ((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m)) := by
    -- Rewrite the center step to one reciprocal-`L α_m` multiple of the current gradient.
    have hcoeff :
        method.alpha m / method.gamma (m + 1) = 1 / ((L : ℝ) * method.alpha m) := by
      rw [hgamma_alpha]
      field_simp [hL.ne', halpha_ne]
    calc
      method.v (m + 1) - xStar
          = (method.v m - (method.alpha m / method.gamma (m + 1)) • ∇ f (method.y m)) - xStar := by
              rw [hcenter]
      _ = (method.v m - xStar) - (method.alpha m / method.gamma (m + 1)) • ∇ f (method.y m) := by
            abel
      _ = (method.v m - xStar) - ((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m)) := by
            rw [hcoeff]
  have hnorm_smul :
      ‖((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m))‖ ^ (2 : ℕ) =
        (1 / ((L : ℝ) * method.alpha m)) ^ (2 : ℕ) *
          ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Compute the norm-square of the scaled gradient in the scalar normal form used below.
    calc
      ‖((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m))‖ ^ (2 : ℕ)
          = inner ℝ
              (((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m)))
              (((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m))) := by
                rw [real_inner_self_eq_norm_sq]
      _ =
        (1 / ((L : ℝ) * method.alpha m)) ^ (2 : ℕ) *
          ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
            ring
  have hnorm_expand :
      ‖method.v (m + 1) - xStar‖ ^ (2 : ℕ) =
        ‖method.v m - xStar‖ ^ (2 : ℕ) -
          2 * (1 / ((L : ℝ) * method.alpha m)) *
            inner ℝ (∇ f (method.y m)) (method.v m - xStar) +
          (1 / ((L : ℝ) * method.alpha m)) ^ (2 : ℕ) *
            ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Expand the next center norm after the normalized center-step rewrite.
    rw [hstep_eq]
    show
      ‖(method.v m - xStar) -
          ((1 / ((L : ℝ) * method.alpha m)) • ∇ f (method.y m))‖ ^ (2 : ℕ) =
        ‖method.v m - xStar‖ ^ (2 : ℕ) -
          2 * (1 / ((L : ℝ) * method.alpha m)) *
            inner ℝ (∇ f (method.y m)) (method.v m - xStar) +
          (1 / ((L : ℝ) * method.alpha m)) ^ (2 : ℕ) *
            ‖∇ f (method.y m)‖ ^ (2 : ℕ)
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm, hnorm_smul]
    ring
  have hratio' :
      ((1 - ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m)) /
          ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m)) =
        (3 - method.alpha m ^ (2 : ℕ)) / (method.alpha m ^ (2 : ℕ)) := by
    simpa [method.toOptimalMethodRecurrence.weight_succ] using hratio
  rw [hratio']
  rw [hnorm_expand]
  set a : ℝ := ‖method.v m - xStar‖ ^ (2 : ℕ)
  set b : ℝ := inner ℝ (∇ f (method.y m)) (method.v m - xStar)
  set c : ℝ := ‖∇ f (method.y m)‖ ^ (2 : ℕ)
  set α : ℝ := method.alpha m
  have hdiff :
      (4 * (L : ℝ)) ^ (2 : ℕ) *
          (a - 2 * (1 / ((L : ℝ) * α)) * b + (1 / ((L : ℝ) * α)) ^ (2 : ℕ) * c) +
        16 * g0 ^ (2 : ℕ) * ((3 - α ^ (2 : ℕ)) / α ^ (2 : ℕ)) -
        (4 * (L : ℝ)) ^ (2 : ℕ) * a =
      (16 / α ^ (2 : ℕ)) *
        (c + (3 - α ^ (2 : ℕ)) * g0 ^ (2 : ℕ) - 2 * (L : ℝ) * α * b) := by
    field_simp [halpha_ne, hL.ne']
    ring
  simpa [a, b, c, α] using hdiff

/-- Helper for Theorem 2.26: the live one-step frontier is the sign of the exact raw Lyapunov
difference, after the center-step normalization but before any branch-local scalar compression. -/
private lemma monotoneConstantStepSchemeIA_mixedInner_ge_stageBonusSurface
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * method.alpha m *
        inner ℝ (∇ f (method.y m)) (method.v m - xStar) ≥
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
  -- Split the center displacement as `(v_m - y_m) + (y_m - x_★)` so the already packaged
  -- bonus lower bounds can be added without reopening the stage algebra here.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hvMinusY :
      2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - method.y m) ≥
        2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Keep the `v_m - y_m` contribution in the exact owner spelling used by the earlier bridge.
    simpa [method] using
      monotoneConstantStepSchemeIA_vMinusYInnerWithBonus
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz x0 (m := m) hL
  have hyMinusXStar :
      2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.y m - xStar) ≥
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
    -- The minimizer-side bridge already carries the full stage-square package used later in the
    -- branch-local closure.
    simpa [method] using
      monotoneConstantStepSchemeIA_yMinusXStarInnerWithStageSquares
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar hxStar x0 (m := m) hL
  have hsplit :
      method.v m - xStar = (method.v m - method.y m) + (method.y m - xStar) := by
    abel
  calc
    2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - xStar)
        =
      2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - method.y m) +
        2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.y m - xStar) := by
            rw [hsplit, inner_add_right]
            ring
    _ ≥
      (2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
            nlinarith [hvMinusY, hyMinusXStar]
    _ =
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m *
          (2 * ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) +
            ‖∇ f (method.x (m + 1))‖ ^ (2 : ℕ)) := by
            ring

/-- Helper for Theorem 2.26: keep the mixed-inner estimate at the fuller objective-gap surface,
before rewriting `ŷ_m` to either branch and before compressing away the current-gap mass. -/
private lemma monotoneConstantStepSchemeIA_mixedInner_ge_fullBonusSurface
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * method.alpha m *
        inner ℝ (∇ f (method.y m)) (method.v m - xStar) ≥
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Route correction: branch before the stage-square compression, so the source objective-gap
  -- mass from `y_m` to `xStar` stays explicit through the branch split.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hvMinusY :
      2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - method.y m) ≥
        2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Keep the `v_m - y_m` contribution in the exact owner spelling used by the earlier bridge.
    simpa [method] using
      monotoneConstantStepSchemeIA_vMinusYInnerWithBonus
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz x0 (m := m) hL
  have hyMinusXStar :
      2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.y m - xStar) ≥
        2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
    -- Keep only the minimizer objective gap at this stage; the branch rewrite will recover the
    -- iterate-window squares later.
    simpa [method] using
      monotoneConstantStepSchemeIA_yMinusXStarInnerWithBonus
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar hxStar x0 (m := m) hL
  have hsplit :
      method.v m - xStar = (method.v m - method.y m) + (method.y m - xStar) := by
    abel
  calc
    2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - xStar)
        =
      2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - method.y m) +
        2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.y m - xStar) := by
            rw [hsplit, inner_add_right]
            ring
    _ ≥
      (2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
        (2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ)) := by
            nlinarith [hvMinusY, hyMinusXStar]
    _ =
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            ring

/-- Helper for Theorem 2.26: reopen the full bonus surface through the exact source stage split,
so the branch-local proof still sees the chain `y_m → x̂_{m+1} → ŷ_m → x_{m+1} → xStar`
before any scalar compression. -/
private lemma monotoneConstantStepSchemeIA_fullBonusSurface_eq_stageSplitSurface
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) =
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m *
          (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) * method.alpha m *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
            f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
        2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
          (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
        2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
          (f (method.x (m + 1)) - f xStar) +
        2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
          (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m)) +
        2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
          (f (method m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Route correction: rewrite the minimizer objective gap one layer earlier through the exact
  -- source chain, so the branch proof can keep the current-gap and successor-gap pieces separate.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  calc
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
          2 * (L : ℝ) * method.alpha m * (f (method.y m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ)
        =
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m *
          (f (method.y m) -
            ((1 - method.alpha m) * f (method m) + method.alpha m * f xStar)) +
        2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
          (f (method m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
          ring
    _ =
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m *
          ((f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
            (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
              f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
            method.alpha m *
              (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
            method.alpha m * (f (method.x (m + 1)) - f xStar) +
            (1 - method.alpha m) *
              (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m))) +
        2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
          (f (method m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
          rw [monotoneConstantStepSchemeIA_stage_objective_gap_split
            (f := f) (L := L) xStar x0 (m := m) hL hgrad hgrad_lipschitz]
    _ =
      2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m *
          (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) * method.alpha m *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
            f (monotoneConstantStepSchemeIAYHat f L x0 m)) +
        2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
          (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method.x (m + 1))) +
        2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
          (f (method.x (m + 1)) - f xStar) +
        2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
          (f (monotoneConstantStepSchemeIAYHat f L x0 m) - f (method m)) +
        2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
          (f (method m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
          ring

/-- Helper for Theorem 2.26: after the exact source split is specialized to the `choose_x`
branch, the branch-local surface collapses to the current lead gap, the quadratic defect, and one
weighted current minimizer gap. -/
private lemma monotoneConstantStepSchemeIA_chooseX_stageSplit_eq_currentGapSurface
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m *
          (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) * method.alpha m *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
          (f (method m) - f (method.x (m + 1))) +
        2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
          (f (method.x (m + 1)) - f xStar) +
        2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
          (f (method m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) =
      2 * (L : ℝ) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m * (f (method m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Collapse the exact `choose_x` source split before any inequality is applied, so the live
  -- blocker is a compact scalar residual rather than the long stage chain.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  calc
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
          (1 - method.alpha m) *
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
          2 * (L : ℝ) * method.alpha m *
            (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
          2 * (L : ℝ) * method.alpha m *
            (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
          2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
            (f (method m) - f (method.x (m + 1))) +
          2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
            (f (method.x (m + 1)) - f xStar) +
          2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
            (f (method m) - f xStar) +
          method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ)
        =
      2 * (L : ℝ) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) *
          (method.alpha m ^ (2 : ℕ) * (f (method m) - f (method.x (m + 1))) +
            method.alpha m ^ (2 : ℕ) * (f (method.x (m + 1)) - f xStar) +
            method.alpha m * (1 - method.alpha m) * (f (method m) - f xStar)) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            ring
    _ =
      2 * (L : ℝ) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m * (f (method m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
            ring

/-- Helper for Theorem 2.26: after the exact source split is specialized to the `choose_xHat`
branch, the branch-local surface becomes the weighted current lead/defect block together with the
lead gap to `x̂_{m+1}` and the weighted selected-point minimizer gap. -/
private lemma monotoneConstantStepSchemeIA_chooseXHat_stageSplit_eq_selectedGapSurface
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    2 * (L : ℝ) * (1 - method.alpha m) * (f (method.y m) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        2 * (L : ℝ) * method.alpha m *
          (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) -
            f (method.x (m + 1))) +
        2 * (L : ℝ) * method.alpha m ^ (2 : ℕ) *
          (f (method.x (m + 1)) - f xStar) +
        2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        2 * (L : ℝ) * method.alpha m * (1 - method.alpha m) *
          (f (method m) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) =
      (1 - method.alpha m) *
          (2 * (L : ℝ) * (f (method.y m) - f (method m)) +
            ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ)) +
        2 * (L : ℝ) * method.alpha m *
          (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) * method.alpha m *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) := by
  -- Collapse the exact `choose_xHat` source split before any sign estimate is applied, so the
  -- remaining blocker is the selected-gap residual itself.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  ring


/-- Helper for Theorem 2.26: the successor weight coefficient is exactly
`(3 - α_m^2) / α_m^2` when `γ₀ = 3L`. -/
private lemma monotoneConstantStepSchemeIA_weight_ratio_eq_alpha_sq
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    ((1 - method.toOptimalMethodRecurrence.weight (m + 1)) /
        method.toOptimalMethodRecurrence.weight (m + 1)) =
      (3 - method.alpha m ^ (2 : ℕ)) / (method.alpha m ^ (2 : ℕ)) := by
  -- Rewrite `λ_{m+1}` from `γ_{m+1} = λ_{m+1} (3L)` and `γ_{m+1} = L α_m^2`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hgamma_weight :
      method.gamma (m + 1) = method.toOptimalMethodRecurrence.weight (m + 1) * (3 * (L : ℝ)) := by
    simpa [method] using method.gamma_sub_mu_eq_weight_mul_initial_gap (m + 1)
  have hgamma_alpha :
      method.gamma (m + 1) = (L : ℝ) * method.alpha m ^ (2 : ℕ) := by
    simpa [method] using method.gamma_succ_eq_L_mul_sq m
  have hweight_eq :
      method.toOptimalMethodRecurrence.weight (m + 1) = method.alpha m ^ (2 : ℕ) / 3 := by
    have hthreeL_ne : (3 * (L : ℝ)) ≠ 0 := by
      exact mul_ne_zero (by norm_num) hL.ne'
    calc
      method.toOptimalMethodRecurrence.weight (m + 1)
          = (method.toOptimalMethodRecurrence.weight (m + 1) * (3 * (L : ℝ))) / (3 * (L : ℝ)) := by
              field_simp [hthreeL_ne]
      _ = ((L : ℝ) * method.alpha m ^ (2 : ℕ)) / (3 * (L : ℝ)) := by
            rw [← hgamma_weight, hgamma_alpha]
      _ = method.alpha m ^ (2 : ℕ) / 3 := by
            field_simp [hL.ne']
  have halpha_sq_ne : method.alpha m ^ (2 : ℕ) ≠ 0 := by
    exact pow_ne_zero 2 (method.alpha_pos m).ne'
  change (1 - ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m)) /
      ((1 - method.alpha m) * method.toOptimalMethodRecurrence.weight m) =
    (3 - method.alpha m ^ (2 : ℕ)) / (method.alpha m ^ (2 : ℕ))
  rw [← method.toOptimalMethodRecurrence.weight_succ m, hweight_eq]
  field_simp [halpha_sq_ne]

/-- Helper for Theorem 2.26: the monotone type-I objective values decrease along the actual
iterate sequence `x_m`. -/
private lemma monotoneConstantStepSchemeIA_objective_succ_le_current
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    f (method.x (m + 1)) ≤ f (method m) := by
  -- First compare the next iterate with the selected monotone point `ŷ_m`, then use the
  -- branch-independent fact `f (ŷ_m) ≤ f (x_m)`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hx_le_yHat :
      f (method.x (m + 1)) ≤ f (monotoneConstantStepSchemeIAYHat f L x0 m) := by
    -- The actual successor is a reciprocal-`L` gradient step from `ŷ_m`, so the descent lemma
    -- gives a quantitative decrease and hence the coarse comparison used here.
    change f (monotoneConstantStepSchemeIAX f L x0 (m + 1)) ≤
      f (monotoneConstantStepSchemeIAYHat f L x0 m)
    have hx_desc :
        f (monotoneConstantStepSchemeIAX f L x0 (m + 1)) ≤
          f (monotoneConstantStepSchemeIAYHat f L x0 m) -
            (1 / (2 * (L : ℝ))) *
              ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) := by
      simpa [monotoneConstantStepSchemeIAX_succ] using
        gradient_step_value_descent_of_lipschitzGradient
          f hL (fun x ↦ (hgrad x).differentiableAt) (by simpa using hgrad_lipschitz)
          (monotoneConstantStepSchemeIAYHat f L x0 m)
    exact le_trans hx_desc (sub_le_self _ (by positivity))
  have hyHat_le_x :
      f (monotoneConstantStepSchemeIAYHat f L x0 m) ≤ f (method m) := by
    -- The source monotone selector chooses the better of `x_m` and `x̂_{m+1}`.
    simpa [method] using monotoneConstantStepSchemeIAYHat_objective_le_x f L x0 m
  exact hx_le_yHat.trans hyHat_le_x

/-- Helper for Theorem 2.26: the actual successor objective value also stays below the tentative
gradient step `x̂_{m+1}` because `x_{m+1}` descends from the selected point `ŷ_m`, which never
has larger objective than `x̂_{m+1}`. -/
private lemma monotoneConstantStepSchemeIA_objective_succ_le_xHat
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    f (method.x (m + 1)) ≤
      f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
  -- Compare `x_{m+1}` first with the selected point `ŷ_m`, then use the branch-independent
  -- monotone selector inequality `f (ŷ_m) ≤ f (x̂_{m+1})`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hx_le_yHat :
      f (method.x (m + 1)) ≤ f (monotoneConstantStepSchemeIAYHat f L x0 m) := by
    -- The actual successor is always a reciprocal-`L` gradient step from `ŷ_m`.
    change f (monotoneConstantStepSchemeIAX f L x0 (m + 1)) ≤
      f (monotoneConstantStepSchemeIAYHat f L x0 m)
    have hx_desc :
        f (monotoneConstantStepSchemeIAX f L x0 (m + 1)) ≤
          f (monotoneConstantStepSchemeIAYHat f L x0 m) -
            (1 / (2 * (L : ℝ))) *
              ‖∇ f (monotoneConstantStepSchemeIAYHat f L x0 m)‖ ^ (2 : ℕ) := by
      simpa [monotoneConstantStepSchemeIAX_succ] using
        gradient_step_value_descent_of_lipschitzGradient
          f hL (fun x ↦ (hgrad x).differentiableAt) (by simpa using hgrad_lipschitz)
          (monotoneConstantStepSchemeIAYHat f L x0 m)
    exact le_trans hx_desc (sub_le_self _ (by positivity))
  have hyHat_le_xHat :
      f (monotoneConstantStepSchemeIAYHat f L x0 m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
    -- The selected point is defined as the better of `x_m` and `x̂_{m+1}`.
    exact monotoneConstantStepSchemeIAYHat_objective_le_xHat f L x0 m
  exact hx_le_yHat.trans hyHat_le_xHat

/-- Helper for Theorem 2.26: the tentative-step comparison term is always bounded below by the
actual iterate drop because `x_{m+1}` never has larger objective than `x̂_{m+1}`. -/
private lemma monotoneConstantStepSchemeIA_xHatComparison_ge_iterateDrop
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m) ≥
      f (method.x (m + 1)) - f (method m) := by
  -- Subtract the same current objective from the monotone comparison
  -- `f (x_{m+1}) ≤ f (x̂_{m+1})`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hx_le_xHat :
      f (method.x (m + 1)) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) := by
    -- Reuse the branch-independent successor-versus-`x̂_{m+1}` comparison.
    simpa [method] using
      monotoneConstantStepSchemeIA_objective_succ_le_xHat
        (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz
  linarith

/-- Helper for Theorem 2.26: multiplying the tentative-step comparison by the nonnegative branch
coefficient preserves the `x̂_{m+1}`-to-`x_{m+1}` transport used in the `choose_xHat` closure. -/
private lemma monotoneConstantStepSchemeIA_chooseXHatWeightedComparison_ge_iterateDrop
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {m : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    ((2 * (L : ℝ)) * (1 - method.alpha m)) *
        (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) ≥
      ((2 * (L : ℝ)) * (1 - method.alpha m)) *
        (f (method.x (m + 1)) - f (method m)) := by
  -- Transport the weighted comparison before the final raw-summand inequality, so the branch
  -- proof can stay on the actual iterate-drop surface afterwards.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hcompare :
      f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m) ≥
        f (method.x (m + 1)) - f (method m) := by
    simpa [method] using
      monotoneConstantStepSchemeIA_xHatComparison_ge_iterateDrop
        (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz
  have hcoeff_nonneg : 0 ≤ (2 * (L : ℝ)) * (1 - method.alpha m) := by
    -- The branch coefficient is nonnegative because `α_m ∈ (0, 1)`.
    have hfactor_nonneg : 0 ≤ 1 - method.alpha m := by
      linarith [(method.alpha_mem_Ioo m).2]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hcompare hcoeff_nonneg
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Helper for Theorem 2.26: the weighted actual iterate-drop residual is nonpositive on every
prefix because each term is a nonnegative coefficient times the monotone objective decrease
`f (x_{m+1}) - f (x_m) ≤ 0`. -/
private lemma monotoneConstantStepSchemeIA_weightedIterateDrop_prefix_nonpos
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {s : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    Finset.sum (Finset.range s) (fun m ↦
        ((16 / method.alpha m ^ (2 : ℕ)) * (2 * (L : ℝ)) * (1 - method.alpha m)) *
          (f (method.x (m + 1)) - f (method m))) ≤
      0 := by
  -- Sum the pointwise nonpositive weighted iterate drops over the requested prefix.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  refine Finset.sum_nonpos ?_
  intro m hm
  have hcoeff_nonneg :
      0 ≤ (16 / method.alpha m ^ (2 : ℕ)) * (2 * (L : ℝ)) * (1 - method.alpha m) := by
    -- Every scalar coefficient is nonnegative on the positive-`L` branch.
    have halpha_sq_pos : 0 < method.alpha m ^ (2 : ℕ) := by
      exact pow_pos (method.alpha_pos m) 2
    have hfactor_nonneg : 0 ≤ 1 - method.alpha m := by
      linarith [(method.alpha_mem_Ioo m).2]
    positivity
  have hdrop :
      f (method.x (m + 1)) - f (method m) ≤ 0 := by
    -- The actual iterate objectives form a monotone decreasing sequence.
    have hmono :
        f (method.x (m + 1)) ≤ f (method m) := by
      simpa [method] using
        monotoneConstantStepSchemeIA_objective_succ_le_current
          (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos hcoeff_nonneg hdrop

/-- Helper for Theorem 2.26: after freezing the branch selector, the piecewise residual that is
`0` in the `choose_x` branch and the weighted actual iterate drop in the `choose_xHat` branch is
still nonpositive on every prefix. -/
private lemma monotoneConstantStepSchemeIA_branchResidual_prefix_nonpos
    {L : NNReal} {f : E → ℝ}
    (x0 : E)
    {s : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    Finset.sum (Finset.range s) (fun m ↦
        if f (method m) ≤ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) then
          0
        else
          ((16 / method.alpha m ^ (2 : ℕ)) * (2 * (L : ℝ)) * (1 - method.alpha m)) *
            (f (method.x (m + 1)) - f (method m))) ≤
      0 := by
  -- Sum the branchwise residual termwise: the `choose_x` case contributes `0`, while the
  -- `choose_xHat` case is the same nonpositive weighted iterate drop as before.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  refine Finset.sum_nonpos ?_
  intro m hm
  by_cases hsel :
      f (method m) ≤ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))
  · -- The `choose_x` branch contributes exactly `0`.
    rw [if_pos hsel]
  · -- The `choose_xHat` branch keeps the same weighted actual iterate-drop term.
    rw [if_neg hsel]
    have hcoeff_nonneg :
        0 ≤ (16 / method.alpha m ^ (2 : ℕ)) * (2 * (L : ℝ)) * (1 - method.alpha m) := by
      -- The branch coefficient is nonnegative because `α_m ∈ (0, 1)`.
      have halpha_sq_pos : 0 < method.alpha m ^ (2 : ℕ) := by
        exact pow_pos (method.alpha_pos m) 2
      have hfactor_nonneg : 0 ≤ 1 - method.alpha m := by
        linarith [(method.alpha_mem_Ioo m).2]
      positivity
    have hdrop :
        f (method.x (m + 1)) - f (method m) ≤ 0 := by
      -- Reuse the branch-independent monotonicity of the actual iterate sequence.
      have hmono :
          f (method.x (m + 1)) ≤ f (method m) := by
        simpa [method] using
          monotoneConstantStepSchemeIA_objective_succ_le_current
            (f := f) (L := L) x0 (m := m) hL hgrad hgrad_lipschitz
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hcoeff_nonneg hdrop

/-- Helper for Theorem 2.26: the weighted Lyapunov potential equals its initial value plus the
prefix sum of the exact raw branch differences. -/
private lemma monotoneConstantStepSchemeIA_weightedDescentPotential_eq_initial_add_prefix
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {s T : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
    let Ψ : ℕ → ℝ := fun k ↦
      (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v k - xStar‖ ^ (2 : ℕ) +
        16 * g0 ^ (2 : ℕ) *
          Finset.sum (Finset.Icc 1 k) (fun j ↦
            (1 - method.toOptimalMethodRecurrence.weight j) /
              method.toOptimalMethodRecurrence.weight j)
    Ψ s =
      Ψ 0 +
        Finset.sum (Finset.range s) (fun m ↦
          (16 / method.alpha m ^ (2 : ℕ)) *
            (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
              2 * (L : ℝ) * method.alpha m *
                inner ℝ (∇ f (method.y m)) (method.v m - xStar))) := by
  -- Freeze the potential once, then telescope the exact one-step Lyapunov identity over the
  -- prefix `0, ..., s - 1`.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
  let Ψ : ℕ → ℝ := fun k ↦
    (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v k - xStar‖ ^ (2 : ℕ) +
      16 * g0 ^ (2 : ℕ) *
        Finset.sum (Finset.Icc 1 k) (fun j ↦
          (1 - method.toOptimalMethodRecurrence.weight j) /
            method.toOptimalMethodRecurrence.weight j)
  let raw : ℕ → ℝ := fun m ↦
    (16 / method.alpha m ^ (2 : ℕ)) *
      (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
        (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
        2 * (L : ℝ) * method.alpha m *
          inner ℝ (∇ f (method.y m)) (method.v m - xStar))
  have htel :
      ∀ n, Ψ n = Ψ 0 + Finset.sum (Finset.range n) raw := by
    intro n
    induction n with
    | zero =>
        -- The empty prefix contributes no raw terms.
        simp [Ψ, raw]
    | succ n ih =>
        have hsum_succ :
            Finset.sum (Finset.Icc 1 (n + 1)) (fun j ↦
                (1 - method.toOptimalMethodRecurrence.weight j) /
                  method.toOptimalMethodRecurrence.weight j) =
              Finset.sum (Finset.Icc 1 n) (fun j ↦
                  (1 - method.toOptimalMethodRecurrence.weight j) /
                    method.toOptimalMethodRecurrence.weight j) +
                ((1 - method.toOptimalMethodRecurrence.weight (n + 1)) /
                  method.toOptimalMethodRecurrence.weight (n + 1)) := by
          -- Peel the final weight coefficient off the interval sum once.
          rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
        have hstep_raw :
            ((4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v (n + 1) - xStar‖ ^ (2 : ℕ) +
                16 * g0 ^ (2 : ℕ) *
                  ((1 - method.toOptimalMethodRecurrence.weight (n + 1)) /
                    method.toOptimalMethodRecurrence.weight (n + 1))) -
              (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v n - xStar‖ ^ (2 : ℕ) =
            raw n := by
          -- This is exactly the normalized one-step Lyapunov identity already proved above.
          simpa [method, g0, raw] using
            monotoneConstantStepSchemeIA_weightedDescentRawGoal_eq_branchDifference
              (f := f) (L := L) xStar x0 (m := n) (T := T) hL hgrad hgrad_lipschitz
        have hstep : Ψ (n + 1) = Ψ n + raw n := by
          -- Rewrite the weight sum by `hsum_succ`, then solve the scalar rearrangement using the
          -- exact one-step raw identity.
          have hsum_expanded :
              Ψ (n + 1) =
                ((4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v (n + 1) - xStar‖ ^ (2 : ℕ) +
                    16 * g0 ^ (2 : ℕ) *
                      ((1 - method.toOptimalMethodRecurrence.weight (n + 1)) /
                        method.toOptimalMethodRecurrence.weight (n + 1))) +
                  16 * g0 ^ (2 : ℕ) *
                    Finset.sum (Finset.Icc 1 n) (fun j ↦
                      (1 - method.toOptimalMethodRecurrence.weight j) /
                        method.toOptimalMethodRecurrence.weight j) := by
            simp [Ψ, hsum_succ]
            ring
          have hsum_prev :
              Ψ n =
                (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v n - xStar‖ ^ (2 : ℕ) +
                  16 * g0 ^ (2 : ℕ) *
                    Finset.sum (Finset.Icc 1 n) (fun j ↦
                      (1 - method.toOptimalMethodRecurrence.weight j) /
                        method.toOptimalMethodRecurrence.weight j) := by
            simp [Ψ]
          rw [hsum_expanded, hsum_prev]
          nlinarith
        calc
          Ψ (n + 1) = Ψ n + raw n := hstep
          _ = Ψ 0 + Finset.sum (Finset.range n) raw + raw n := by
                rw [ih]
          _ = Ψ 0 + Finset.sum (Finset.range (n + 1)) raw := by
                rw [Finset.sum_range_succ]
                ring
  simpa [raw, Ψ] using htel s

/-- Helper for Theorem 2.26: after summing the exact raw branch differences over a prefix, the
remaining signed residual is nonpositive. -/
private lemma monotoneConstantStepSchemeIA_chooseXWeightedRawSummand_nonpos
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m T : ℕ}
    (hL : 0 < (L : ℝ))
    (hmT : m < T)
    (hsel :
      f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
          f L x0 hL hgrad hgrad_lipschitz) m) ≤
        f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
    (16 / method.alpha m ^ (2 : ℕ)) *
        (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
          (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
          2 * (L : ℝ) * method.alpha m *
            inner ℝ (∇ f (method.y m)) (method.v m - xStar)) ≤
      0 := by
  -- TODO: restore the stabilized `choose_x` branch proof by rewriting the mixed-inner lower bound
  -- to the exact current-gap surface and closing the remaining scalar inequality against the
  -- iterate-window bounds without reopening the prefix summation.
  sorry

/-- Helper for Theorem 2.26: in the `choose_xHat` branch, the repacked full surface already
contains the target coefficient together with the weighted actual iterate-drop residual. -/
private lemma monotoneConstantStepSchemeIA_chooseXHatRepackedSurface_lower_bound
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {m T : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hxStar : IsMinOn f Set.univ xStar)
    (hmT : m < T)
    (hsel :
      ¬ f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
            f L x0 hL hgrad hgrad_lipschitz) m) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
    2 * (L : ℝ) * (f (method.y m) - f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) +
        2 * (L : ℝ) * method.alpha m *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f xStar) +
        2 * (L : ℝ) * (1 - method.alpha m) *
          (f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) - f (method m)) +
        (1 - method.alpha m) *
          ‖∇ f (method m) - ∇ f (method.y m)‖ ^ (2 : ℕ) +
        method.alpha m * ‖∇ f (method.y m)‖ ^ (2 : ℕ) ≥
      ‖∇ f (method.y m)‖ ^ (2 : ℕ) +
        (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
          ((2 * (L : ℝ)) * (1 - method.alpha m)) *
            (f (method.x (m + 1)) - f (method m)) := by
  -- TODO: prove the exact `choose_xHat` repacked surface lower bound by combining the lead
  -- descent, the selected-gap lower bound, and a new branch-local scalar bridge that upgrades
  -- the available window controls to the target coefficient `(3 - α_m^2)`.
  sorry

/-- Helper for Theorem 2.26: in the `choose_xHat` branch, the exact raw summand is controlled by
the weighted actual iterate drop residual. -/
private lemma monotoneConstantStepSchemeIA_chooseXHatWeightedRawSummand_le_iterateDrop
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {m T : ℕ}
    (hL : 0 < (L : ℝ))
    (hmT : m < T)
    (hsel :
      ¬ f ((monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
            f L x0 hL hgrad hgrad_lipschitz) m) ≤
          f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
    (16 / method.alpha m ^ (2 : ℕ)) *
        (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
          (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
          2 * (L : ℝ) * method.alpha m *
            inner ℝ (∇ f (method.y m)) (method.v m - xStar)) ≤
      ((16 / method.alpha m ^ (2 : ℕ)) * (2 * (L : ℝ)) * (1 - method.alpha m)) *
        (f (method.x (m + 1)) - f (method m)) := by
  -- TODO: normalize the exact raw summand through the repacked `choose_xHat` surface, use the
  -- dedicated repacked lower bound above, and only then scale the resulting core inequality by
  -- `16 / α_m^2`.
  sorry

/-- Helper for Theorem 2.26: after summing the exact raw branch differences over a prefix, the
remaining signed residual is nonpositive. -/
private lemma monotoneConstantStepSchemeIA_weightedDescentRawDifference_prefix_nonpos
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {s T : ℕ}
    (hL : 0 < (L : ℝ))
    (hsT : s ≤ T) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
    Finset.sum (Finset.range s) (fun m ↦
        (16 / method.alpha m ^ (2 : ℕ)) *
          (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
            (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
            2 * (L : ℝ) * method.alpha m *
              inner ℝ (∇ f (method.y m)) (method.v m - xStar))) ≤
      0 := by
  -- Freeze the branchwise residual once: the remaining work is only the pointwise comparison from
  -- the exact raw summand to this residual, while its summed sign is already closed below.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
  let residual : ℕ → ℝ := fun m ↦
    if f (method m) ≤ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1)) then
      0
    else
      ((16 / method.alpha m ^ (2 : ℕ)) * (2 * (L : ℝ)) * (1 - method.alpha m)) *
        (f (method.x (m + 1)) - f (method m))
  have hsum_le :
      Finset.sum (Finset.range s) (fun m ↦
          (16 / method.alpha m ^ (2 : ℕ)) *
            (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
              2 * (L : ℝ) * method.alpha m *
                inner ℝ (∇ f (method.y m)) (method.v m - xStar))) ≤
        Finset.sum (Finset.range s) residual := by
    -- Compare each exact raw summand to the frozen branch residual after splitting the selector.
    refine Finset.sum_le_sum ?_
    intro m hm
    have hmT : m < T := lt_of_lt_of_le (Finset.mem_range.mp hm) hsT
    by_cases hsel :
        f (method m) ≤ f (monotoneConstantStepSchemeIAXHat f L x0 (m + 1))
    · -- The positive branch reduces to the proved `raw ≤ 0` lemma.
      change
        (16 / method.alpha m ^ (2 : ℕ)) *
            (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
              2 * (L : ℝ) * method.alpha m *
                inner ℝ (∇ f (method.y m)) (method.v m - xStar)) ≤
          residual m
      have hresidual_eq : residual m = 0 := by
        unfold residual
        rw [if_pos hsel]
      rw [hresidual_eq]
      exact
        monotoneConstantStepSchemeIA_chooseXWeightedRawSummand_nonpos
          (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar hxStar x0
          (m := m) (T := T) hL hmT hsel
    · -- The negative branch is reduced to a single exact helper statement.
      change
        (16 / method.alpha m ^ (2 : ℕ)) *
            (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
              2 * (L : ℝ) * method.alpha m *
                inner ℝ (∇ f (method.y m)) (method.v m - xStar)) ≤
          residual m
      have hresidual_eq :
          residual m =
            ((16 / method.alpha m ^ (2 : ℕ)) * (2 * (L : ℝ)) * (1 - method.alpha m)) *
              (f (method.x (m + 1)) - f (method m)) := by
        unfold residual
        rw [if_neg hsel]
      rw [hresidual_eq]
      exact
        monotoneConstantStepSchemeIA_chooseXHatWeightedRawSummand_le_iterateDrop
          (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar hxStar x0
          (m := m) (T := T) hL hmT hsel
  have hresidual_nonpos :
      Finset.sum (Finset.range s) residual ≤ 0 := by
    -- The residual sum is already closed because each branch contributes either `0` or a
    -- nonpositive weighted actual iterate drop.
    simpa [method, residual] using
      monotoneConstantStepSchemeIA_branchResidual_prefix_nonpos
        (f := f) (L := L) x0 (s := s) hL hgrad hgrad_lipschitz
  exact le_trans hsum_le hresidual_nonpos

/-- Helper for Theorem 2.26: the weighted Lyapunov potential is bounded above by its initial
value on every prefix `s ≤ T`, without assuming a false pointwise drop. -/
private lemma monotoneConstantStepSchemeIA_weightedDescentPotential_le_initial_prefix
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {s T : ℕ}
    (hL : 0 < (L : ℝ))
    (hsT : s ≤ T) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
    let Ψ : ℕ → ℝ := fun k ↦
      (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v k - xStar‖ ^ (2 : ℕ) +
        16 * g0 ^ (2 : ℕ) *
          Finset.sum (Finset.Icc 1 k) (fun j ↦
            (1 - method.toOptimalMethodRecurrence.weight j) /
              method.toOptimalMethodRecurrence.weight j)
    Ψ s ≤ (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
  -- Combine the exact prefix telescoping identity with the summed nonpositivity of the raw
  -- branch expression, then evaluate the initial potential explicitly.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
  let Ψ : ℕ → ℝ := fun k ↦
    (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v k - xStar‖ ^ (2 : ℕ) +
      16 * g0 ^ (2 : ℕ) *
        Finset.sum (Finset.Icc 1 k) (fun j ↦
          (1 - method.toOptimalMethodRecurrence.weight j) /
            method.toOptimalMethodRecurrence.weight j)
  have hprefix :
      Ψ s =
        Ψ 0 +
          Finset.sum (Finset.range s) (fun m ↦
            (16 / method.alpha m ^ (2 : ℕ)) *
              (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
                (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
                2 * (L : ℝ) * method.alpha m *
                  inner ℝ (∇ f (method.y m)) (method.v m - xStar))) := by
    -- Expand the prefix potential by telescoping the exact one-step Lyapunov identity.
    simpa [method, g0, Ψ] using
      monotoneConstantStepSchemeIA_weightedDescentPotential_eq_initial_add_prefix
        (f := f) (L := L) xStar x0 (s := s) (T := T) hL hgrad hgrad_lipschitz
  have hsum_nonpos :
      Finset.sum (Finset.range s) (fun m ↦
          (16 / method.alpha m ^ (2 : ℕ)) *
            (‖∇ f (method.y m)‖ ^ (2 : ℕ) +
              (3 - method.alpha m ^ (2 : ℕ)) * g0 ^ (2 : ℕ) -
              2 * (L : ℝ) * method.alpha m *
                inner ℝ (∇ f (method.y m)) (method.v m - xStar))) ≤
        0 := by
    -- The only substantive remaining input is the sign of the summed raw branch residual.
    simpa [method, g0] using
      monotoneConstantStepSchemeIA_weightedDescentRawDifference_prefix_nonpos
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar hxStar x0 hL hsT
  have hΨ0 :
      Ψ 0 = (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
    -- At stage `0`, the center is exactly `x₀` and the interval sum is empty.
    have hv0 : method.v 0 = x0 := by
      simpa [method] using method.v_zero
    simp [Ψ, hv0]
    ring_nf
  have hbound : Ψ s ≤ (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
    nlinarith [hprefix, hsum_nonpos, hΨ0]
  simpa [Ψ] using hbound

/-- Helper for Theorem 2.26: once the one-step weighted Lyapunov drop is available up to stage
`T - 1`, the weighted potential is bounded by its initial value at every stage `k ≤ T`. -/
private lemma monotoneConstantStepSchemeIA_weightedDescentPotential_le_initial_of_step
    {L : NNReal} {f : E → ℝ}
    (xStar : E)
    (x0 : E)
    {T : ℕ}
    (hL : 0 < (L : ℝ))
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (g0 : ℝ)
    (hstep :
      ∀ m, m < T →
        let method :=
          monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
        ((4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v (m + 1) - xStar‖ ^ (2 : ℕ) +
            16 * g0 ^ (2 : ℕ) *
              Finset.sum (Finset.Icc 1 (m + 1)) (fun k ↦
                (1 - method.toOptimalMethodRecurrence.weight k) /
                  method.toOptimalMethodRecurrence.weight k)) ≤
          ((4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v m - xStar‖ ^ (2 : ℕ) +
            16 * g0 ^ (2 : ℕ) *
              Finset.sum (Finset.Icc 1 m) (fun k ↦
                (1 - method.toOptimalMethodRecurrence.weight k) /
                  method.toOptimalMethodRecurrence.weight k))) :
    let method :=
      monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
    ∀ k, k ≤ T →
      ((4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v k - xStar‖ ^ (2 : ℕ) +
          16 * g0 ^ (2 : ℕ) *
            Finset.sum (Finset.Icc 1 k) (fun j ↦
              (1 - method.toOptimalMethodRecurrence.weight j) /
                method.toOptimalMethodRecurrence.weight j)) ≤
        (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
  -- Freeze the Lyapunov potential once, then iterate the one-step drop until the initial stage.
  dsimp
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let Ψ : ℕ → ℝ := fun k ↦
    (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v k - xStar‖ ^ (2 : ℕ) +
      16 * g0 ^ (2 : ℕ) *
        Finset.sum (Finset.Icc 1 k) (fun j ↦
          (1 - method.toOptimalMethodRecurrence.weight j) /
            method.toOptimalMethodRecurrence.weight j)
  have hΨ0 :
      Ψ 0 = (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
    -- At stage `0`, the center is `x₀` and the interval sum is empty.
    have hv0 : method.v 0 = x0 := by
      simpa [method] using method.v_zero
    simp [Ψ, hv0]
    ring_nf
  intro k hk
  induction k with
  | zero =>
      -- The initial potential is exactly the initial radius term.
      simpa [Ψ] using hΨ0.le
  | succ k ih =>
      -- Apply the one-step drop at stage `k`, then invoke the induction hypothesis.
      have hkT : k < T := Nat.lt_of_succ_le hk
      exact (hstep k hkT).trans (ih (Nat.le_of_lt hkT))

/-- Helper for Theorem 2.26: the remaining positive-`L` step is the source-faithful weighted
descent sum for the monotone type-I trajectory. -/
private lemma monotoneConstantStepSchemeIA_weighted_descent_sum_le_initial_radius_sq
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ} (hL : 0 < (L : ℝ)) (_hT : 1 ≤ T) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) *
        (16 * Finset.sum (Finset.Icc 1 T) (fun k ↦
          (1 -
              (monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
                f L x0 hL hgrad hgrad_lipschitz).toOptimalMethodRecurrence.weight k) /
            (monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme
              f L x0 hL hgrad hgrad_lipschitz).toOptimalMethodRecurrence.weight k)) ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
  -- Route correction: the earlier pointwise potential-drop frontier is false for this monotone
  -- scheme, so the remaining task is a direct summed Lyapunov estimate rather than a per-step
  -- coefficient bound.
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  let g0 : ℝ := g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T]
  have hpotential :
      ∀ k, k ≤ T →
        ((4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v k - xStar‖ ^ (2 : ℕ) +
            16 * g0 ^ (2 : ℕ) *
            Finset.sum (Finset.Icc 1 k) (fun j ↦
              (1 - method.toOptimalMethodRecurrence.weight j) /
                method.toOptimalMethodRecurrence.weight j)) ≤
          (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
    -- Route correction: use the direct prefix Lyapunov estimate instead of the false pointwise
    -- one-step drop route.
    intro k hk
    simpa [method, g0] using
      monotoneConstantStepSchemeIA_weightedDescentPotential_le_initial_prefix
        (f := f) (L := L) hconvex hgrad hgrad_lipschitz xStar hxStar x0
        (s := k) (T := T) hL hk
  have hfinal :=
    hpotential T le_rfl
  have hnonneg :
      0 ≤ (4 * (L : ℝ)) ^ (2 : ℕ) * ‖method.v T - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hsum_le :
      16 * g0 ^ (2 : ℕ) *
          Finset.sum (Finset.Icc 1 T) (fun k ↦
            (1 - method.toOptimalMethodRecurrence.weight k) /
              method.toOptimalMethodRecurrence.weight k) ≤
        (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
    nlinarith
  simpa [method, g0, mul_assoc, mul_left_comm, mul_comm] using hsum_le

/-- Helper for Theorem 2.26: on the positive-`L` branch, the source squared estimate `(2.u398)`
controls the minimum gradient norm over the first `T + 1` iterates. -/
private lemma monotoneConstantStepSchemeIA_sq_minGradientNorm_mul_explicit_denominator_le_of_pos
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ} (hL : 0 < (L : ℝ)) (hT : 1 ≤ T) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) *
        (((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ)) -
          ((9 / 4 : ℝ) * (T + 2 : ℝ)) -
          (9 / 8 : ℝ)) ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) := by
  -- Route correction: separate the positive-`L` proof into the structural weighted-descent sum
  -- and the scalar weight-denominator comparison from Theorem 2.22.
  let method :=
    monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz
  have hweighted :=
    monotoneConstantStepSchemeIA_weighted_descent_sum_le_initial_radius_sq
      hconvex hgrad hgrad_lipschitz xStar hxStar x0 hL hT
  have hscalar :=
    monotoneConstantStepSchemeIA_weight_sum_ge_explicit_denominator (method := method) hT
  have hmul :
      g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) *
          (((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ)) -
            ((9 / 4 : ℝ) * (T + 2 : ℝ)) -
            (9 / 8 : ℝ)) ≤
        g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) *
          (16 * Finset.sum (Finset.Icc 1 T) (fun k ↦
            (1 - method.toOptimalMethodRecurrence.weight k) /
              method.toOptimalMethodRecurrence.weight k)) := by
    exact mul_le_mul_of_nonneg_left hscalar (sq_nonneg _)
  exact hmul.trans (by simpa [method] using hweighted)

-- Proof sketch: on the positive-`L` branch, use
-- `monotoneConstantStepSchemeIAToGeneralOptimalMethodScheme f L x0 hL hgrad hgrad_lipschitz`
-- only as the bridge supplying the owner step-`(c)` descent inequality, then combine that bridge
-- with the source monotone comparison data `x̂ₖ`, `ŷₖ` and the exact update
-- `x_{k+1} = ŷ_k - (1 / L) ∇ f(ŷ_k)` to transfer the resulting function-gap control to the actual
-- iterate gradients `‖∇ f (x_k)‖`. When `L = 0`, the intrinsic gradient hypotheses together with
-- a minimizer forces the gradients to vanish, so the same bound is immediate. After telescoping
-- the tail inequality, identify the textbook `g_{0,T}` with `minGradientNormAlongIterates` and
-- simplify the coefficient sum to the displayed cubic polynomial in `T + 2`.
/-- Theorem 2.26 on the intrinsic real-Hilbert-space owner layer: if `f` is convex on the whole
space, admits the ambient gradient `∇ f` everywhere, that gradient is `L`-Lipschitz in the
ambient norm, and `xStar` is a global minimizer, then the recursive monotone type-I trajectory of
method `(2.2.32)` satisfies the explicit `O(T^{-3/2})` bound on the minimum gradient norm
`g_{0,T}` over the first `T + 1` iterates. The textbook `ℝⁿ` statement is the finite-dimensional
specialization below. -/
theorem monotoneConstantStepSchemeIA_minGradientNormAlongIterates_le_explicit_bound
    {L : NNReal} {f : E → ℝ}
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ} (hT : 1 ≤ T) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) /
        Real.sqrt
          ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
            (9 / 4 : ℝ) * (T + 2 : ℝ) -
            (9 / 8 : ℝ)) := by
  by_cases hL0 : (L : ℝ) = 0
  · -- In the degenerate case `L = 0`, every gradient vanishes and the right-hand side is zero.
    rw [monotoneConstantStepSchemeIA_minGradientNorm_eq_zero_of_L_eq_zero
      hgrad_lipschitz xStar hxStar x0 hL0]
    simp [hL0]
  · have hL : 0 < (L : ℝ) := by
      exact lt_of_le_of_ne (by exact_mod_cast L.2) (by simpa [eq_comm] using hL0)
    have hmin_nonneg :
        0 ≤ g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] :=
      monotoneConstantStepSchemeIA_minGradientNorm_nonneg x0 T
    have hden_pos :
        0 <
          ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
            (9 / 4 : ℝ) * (T + 2 : ℝ) -
            (9 / 8 : ℝ)) :=
      monotoneConstantStepSchemeIA_explicit_denominator_pos hT
    have hsq :=
      monotoneConstantStepSchemeIA_sq_minGradientNorm_mul_explicit_denominator_le_of_pos
        hconvex hgrad hgrad_lipschitz xStar hxStar x0 hL hT
    let denom : ℝ :=
      ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
        (9 / 4 : ℝ) * (T + 2 : ℝ) -
        (9 / 8 : ℝ))
    let rhs : ℝ := (4 * (L : ℝ) * ‖x0 - xStar‖) / Real.sqrt denom
    have hsq_div :
        g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) ≤
          (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) / denom := by
      exact (le_div_iff₀ (by simpa [denom] using hden_pos)).2 (by simpa [denom] using hsq)
    have hrhs_nonneg : 0 ≤ rhs := by
      -- The displayed right-hand side is a nonnegative quotient by a positive square root.
      dsimp [rhs]
      positivity
    have hrhs_sq :
        rhs ^ (2 : ℕ) =
          (4 * (L : ℝ) * ‖x0 - xStar‖) ^ (2 : ℕ) / denom := by
      -- Squaring removes the square root in the denominator.
      dsimp [rhs]
      rw [div_pow]
      rw [Real.sq_sqrt (by simpa [denom] using hden_pos.le)]
    have hsq_rhs :
        g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ^ (2 : ℕ) ≤
          rhs ^ (2 : ℕ) := by
      simpa [hrhs_sq] using hsq_div
    simpa [rhs, denom] using (sq_le_sq₀ hmin_nonneg hrhs_nonneg).1 hsq_rhs

/-- Finite-dimensional Chapter 2 bridge form of Theorem 2.26 using the source-facing notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`. -/
theorem monotoneConstantStepSchemeIA_minGradientNormAlongIterates_le_explicit_bound_of_mem_F11
    [FiniteDimensional ℝ E]
    {L : NNReal} {f : E → ℝ}
    (hf : f ∈ 𝓕[L, p]¹¹)
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (x0 : E)
    {T : ℕ} (hT : 1 ≤ T) :
    g[f; monotoneConstantStepSchemeIAX f L x0; 0, T | Nat.zero_le T] ≤
      (4 * (L : ℝ) * ‖x0 - xStar‖) /
        Real.sqrt
          ((4 / 3 : ℝ) * (T + 2 : ℝ) ^ (3 : ℕ) -
            (9 / 4 : ℝ) * (T + 2 : ℝ) -
            (9 / 8 : ℝ)) :=
  monotoneConstantStepSchemeIA_minGradientNormAlongIterates_le_explicit_bound
    hf.convexOn hf.hasGradientAt hf.gradient_lipschitz xStar hxStar x0 hT

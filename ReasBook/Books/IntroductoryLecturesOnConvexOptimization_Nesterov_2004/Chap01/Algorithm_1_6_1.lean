/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_57

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 1.6.1 is the source-facing owner of the gradient-method trajectory.

Primary domain:
- recursive first-order optimization trajectories on real Hilbert spaces

Sampled owner-style declarations:
- `Function.iterate` for autonomous discrete trajectories
- the downstream owner uses of `gradientMethod` in `Definition_1_6_4.lean`,
  `Proposition_1_6_7.lean`, and `Theorem_1_6_8.lean`

Source/core/bridge triage:
- source-facing: `gradientMethod`
- core/canonical owner: the recursive map `gradientMethod stepSize f x0 : ℕ → E`
- bridge/view: `gradientMethod_const_eq_iterate` for constant step size

Primitive data:
- the step-size schedule `stepSize`,
- the objective `f`,
- the initial point `x0`.

Derived API:
- `gradientMethod_zero`
- `gradientMethod_succ`
- `gradientMethod_const_eq_iterate`

The recursive trajectory is the primitive mathematical object. The constant-step iterate
description is only a derived bridge to the autonomous-map viewpoint, so it stays secondary.

The source text is written on `ℝⁿ`, but the owner abstraction is refined to the real-Hilbert
space level because mathlib's canonical gradient API already lives there and the recursion uses no
coordinate, finite-dimensional, or Euclidean-model-specific data. -/
/-- Algorithm 1.6.1: the gradient method associated to an initial point `x₀`, a step-size
schedule `hₖ`, and an objective `f` is the trajectory defined recursively by
`xₖ₊₁ = xₖ - hₖ • ∇ f (xₖ)`. -/
def gradientMethod
    (stepSize : ℕ → ℝ)
    (f : E → ℝ)
    (x0 : E) :
    ℕ → E
  | 0 => x0
  | k + 1 =>
      gradientMethod stepSize f x0 k -
        stepSize k • ∇ f (gradientMethod stepSize f x0 k)

section

variable (stepSize : ℕ → ℝ) (f : E → ℝ) (x0 : E)

/-- The gradient method starts at the prescribed initial point. -/
@[simp] theorem gradientMethod_zero :
    gradientMethod stepSize f x0 0 = x0 :=
  rfl

/-- The iterates of `gradientMethod` satisfy the textbook update rule at each step. -/
@[simp] theorem gradientMethod_succ (k : ℕ) :
    gradientMethod stepSize f x0 (k + 1) =
      gradientMethod stepSize f x0 k -
        stepSize k • ∇ f (gradientMethod stepSize f x0 k) :=
  rfl

end

/-- For a constant stepsize, `gradientMethod` agrees with iterating the single gradient-step map. -/
theorem gradientMethod_const_eq_iterate
    (f : E → ℝ) (α : ℝ) (x0 : E) (k : ℕ) :
    gradientMethod (fun _ ↦ α) f x0 k =
      (fun x ↦ x - α • ∇ f x)^[k] x0 := by
  induction k with
  | zero =>
      simp
  | succ k hk =>
      simp [gradientMethod_succ, hk, Function.iterate_succ_apply']

end

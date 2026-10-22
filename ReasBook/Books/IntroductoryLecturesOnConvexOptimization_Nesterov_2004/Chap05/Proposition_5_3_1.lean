/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/-
Proposition 5.3.1 lies in the chapter's central-path / first-order stationarity domain.

Sampled owner-style declarations:
- `centralPathPenaltyObjective` in `Definition_5_3_6_1`, the Chapter 5 owner for the tilted
  objective `x ↦ t ⟪c, x⟫ + f x`;
- `IsCentralPath` in `Definition_5_3_6_1`, the owner predicate asserting pointwise minimizers of
  that objective;
- `IsMinOn.isLocalMin`, the canonical bridge from a feasible-set minimizer to an ambient local
  minimizer once the feasible set is a neighborhood of the minimizer;
- `isLocalMin_gradient_eq_zero` in `Chap01/Theorem_1_4_13`, the source-facing stationarity theorem
  for local minimizers on complete real inner-product spaces.

Best owner abstraction:
- source-facing: the central-path stationarity equation in the penalty objective;
- core/canonical: `centralPathPenaltyObjective`, `IsCentralPath`, and `HasGradientAt`;
- bridge/view: the pointwise gradient computation for the penalty objective and the deduction of
  the displayed zero-gradient equation from the owner local-minimum theorem.

Primitive data:
- a domain `dom : Set E`;
- an objective vector `c : E`;
- a differentiable function `f : E → ℝ`;
- a trajectory `xStar : Set.Ici (0 : ℝ) → dom`.

Derived API:
- the gradient identity for `centralPathPenaltyObjective c f t`;
- the stationarity equation satisfied by a central-path point.

This file is therefore a `bridge/view` layer over the existing Chapter 5 central-path owner and
the Chapter 1 stationary-point owner. No parallel local central-path wrapper is introduced. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: differentiate the linear term `x ↦ (t : ℝ) * ⟪c, x⟫`, whose gradient is
-- `t • c`, then add the canonical gradient of `f`.
/-- The tilted objective `x ↦ t ⟪c, x⟫ + f(x)` has gradient `(t : ℝ) • c + ∇ f x` at every
point where `f` is differentiable. -/
theorem hasGradientAt_centralPathPenaltyObjective
    (c : E) (f : E → ℝ) (t : ℝ) {x : E}
    (hf : DifferentiableAt ℝ f x) :
    HasGradientAt (centralPathPenaltyObjective c f t) (t • c + ∇ f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlinear : HasFDerivAt (fun z : E ↦ t * inner ℝ c z) ((t : ℝ) • innerSL ℝ c) x := by
    simpa using (((t : ℝ) • innerSL ℝ c).hasFDerivAt :
      HasFDerivAt (fun z : E ↦ ((t : ℝ) • innerSL ℝ c) z) ((t : ℝ) • innerSL ℝ c) x)
  simpa [centralPathPenaltyObjective] using hlinear.add hf.hasGradientAt.hasFDerivAt

-- Proof sketch: for a fixed `t`, the central-path point `x*(t)` is a global minimizer of the
-- tilted objective on `dom`. If `dom` is a neighborhood of `x*(t)`, then this is an ambient
-- local minimizer. Apply Fermat's theorem to `x ↦ (t : ℝ) * ⟪c, x⟫ + f(x)` and then rewrite the
-- gradient using `hasGradientAt_centralPathPenaltyObjective`.
/-- Proposition 5.3.1: if `x*(t)` minimizes the tilted objective
`x ↦ t ⟪c, x⟫ + f(x)` for every `t ≥ 0`, then at each parameter `t` where `dom` is a
neighborhood of `x*(t)` and `f` is differentiable at `x*(t)`, it satisfies the central-path
stationarity equation `(t : ℝ) • c + ∇ f(x*(t)) = 0`. -/
theorem centralPath_stationarity_eq_zero
    (dom : Set E) (c : E) (f : E → ℝ) (xStar : Set.Ici (0 : ℝ) → dom)
    (hpath : IsCentralPath dom c f xStar)
    (t : Set.Ici (0 : ℝ))
    (hdom : dom ∈ nhds (xStar t : E))
    (hf : DifferentiableAt ℝ f (xStar t : E)) :
    (t : ℝ) • c + ∇ f (xStar t : E) = 0 := by
  have hmin : IsMinOn (centralPathPenaltyObjective c f t) dom (xStar t : E) := hpath t
  have hlocal : IsLocalMin (centralPathPenaltyObjective c f t) (xStar t : E) :=
    hmin.isLocalMin hdom
  have hgrad :
      ∇ (centralPathPenaltyObjective c f (t : ℝ)) (xStar t : E) =
        (t : ℝ) • c + ∇ f (xStar t : E) :=
    (hasGradientAt_centralPathPenaltyObjective c f (t : ℝ) hf).gradient
  have hgradzero : ∇ (centralPathPenaltyObjective c f t) (xStar t : E) = 0 :=
    isLocalMin_gradient_eq_zero hlocal
  rw [hgrad] at hgradzero
  exact hgradzero

end

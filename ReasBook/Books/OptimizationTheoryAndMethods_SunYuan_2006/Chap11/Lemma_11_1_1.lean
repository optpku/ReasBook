/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Segment
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_1_extra_2

noncomputable section

section Chapter11Lemma111

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling for this item:
-- * primary domain: feasible-point Armijo decrease estimates in real-Hilbert-space smooth
--   constrained optimization
-- * owner abstractions inspected: `Metric.infDist`, `IsFeasiblePointArmijoStep`,
--   `HasHessianUpperBoundOn`, `lineTaylorFormula_withIntegralHessianRemainder`, and the
--   Chapter 3 Hessian owner `hessianAt`
-- * layer triage:
--   - `Metric.infDist x Xᶜ`: canonical distance owner for the source quantity `Γ(x)`
--   - `feasiblePointArmijoHessianBound`: source-facing scalar quantity for Lemma 11.1.1,
--     built from the canonical Hessian owner `hessianAt`
--   - `feasiblePointArmijoHessianBound_hasHessianUpperBoundOn`: bridge/view from the source
--     maximum to the canonical Chapter 1 setwise Hessian-bound owner
--   - the two decrease theorems: source-facing statements built on the Chapter 11 Armijo owner
-- * primitive data vs. derived API:
--   - primitive/source data: the Armijo step, the doubled-step feasibility branch, an open
--     set containing the traced segment from `xk` to `xk + (2 * α) • d`, and `ContDiffOn ℝ 2 f`
--     there
--   - derived API: the scalar source maximum `feasiblePointArmijoHessianBound f xk d α`,
--     expressed through the canonical owner `hessianAt`, together with the induced Chapter 1
--     setwise Hessian upper bound on the traced segment

/-- The source scalar bound obtained by taking the supremum of
`‖hessianAt f (xk + (t * α) • d)‖` for `t ∈ [0, 2]`, equivalently of
`‖hessianAt f (xk + s • d)‖` for `s ∈ [0, 2 * α]`. Under the regularity hypotheses in the
theorems below, this agrees with the textbook Hessian maximum along the traced segment from `xk`
to `xk + (2 * α) • d`. -/
def feasiblePointArmijoHessianBound
    (f : E → ℝ) (xk d : E) (α : ℝ) : ℝ :=
  sSup ((fun t : ℝ ↦ ‖hessianAt f (xk + (t * α) • d)‖) '' Set.Icc (0 : ℝ) 2)

/-- `feasiblePointArmijoHessianBound f xk d α` is the source maximum
`max_(0 ≤ t ≤ 2) ‖∇² f(xk + t α d)‖₂`, expressed through the canonical owner `hessianAt`. -/
theorem feasiblePointArmijoHessianBound_isGreatest
    (f : E → ℝ) (xk d : E) (α : ℝ) {D : Set E}
    (hD : IsOpen D)
    (h_segment : segment ℝ xk (xk + (2 * α) • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D) :
    IsGreatest ((fun t : ℝ ↦ ‖hessianAt f (xk + (t * α) • d)‖) '' Set.Icc (0 : ℝ) 2)
      (feasiblePointArmijoHessianBound f xk d α) := sorry

/-- If the doubled-step segment from `xk` to `xk + (2 * α) • d` lies in an open `C²` domain for
`f`, then the source maximum `feasiblePointArmijoHessianBound f xk d α` induces the canonical
Chapter 1 setwise Hessian upper bound on the traced set `xk + (t * α) • d`, `t ∈ [0, 2]`. -/
theorem feasiblePointArmijoHessianBound_hasHessianUpperBoundOn
    (f : E → ℝ) (xk d : E) (α : ℝ) {D : Set E}
    (hD : IsOpen D)
    (h_segment : segment ℝ xk (xk + (2 * α) • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D) :
    HasHessianUpperBoundOn ((fun t : ℝ ↦ xk + (t * α) • d) '' Set.Icc (0 : ℝ) 2) f
      (feasiblePointArmijoHessianBound f xk d α) := sorry

/-- Chapter11 Lemma 11.1.1 (1): if `xk ∈ X`, `d` satisfies `(11.1.1)` and `(11.1.2)`, `α` is a
feasible point Armijo step along `d` at `xk`, the doubled-step segment
`xk + (t * α) • d`, `t ∈ [0, 2]`, lies in an open set `D` on which `f` is `C²`, the source
maximum `feasiblePointArmijoHessianBound f xk d α` then induces the canonical Chapter 1 Hessian
upper bound on that trace, and `xk + (2 * α) • d ∈ X`, then `f (xk + α • d)` satisfies the
decrease estimate `(11.1.5)` with that source maximum. -/
theorem feasiblePointArmijoStep_decrease_of_double_mem
    (f : E → ℝ) (X : Set E) (c1 : ℝ) (xk d : E) (α : ℝ) {D : Set E}
    (hD : IsOpen D)
    (h_segment : segment ℝ xk (xk + (2 * α) • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hα : IsFeasiblePointArmijoStep f X xk d c1 α)
    (h_double_mem : xk + (2 * α) • d ∈ X) :
    f (xk + α • d) ≤
      f xk -
        (c1 * (1 - c1) / feasiblePointArmijoHessianBound f xk d α) *
          (inner ℝ d (gradient f xk) / ‖d‖) ^ (2 : ℕ) := sorry

/-- Chapter11 Lemma 11.1.1 (2): if `xk ∈ X`, `d` satisfies `(11.1.1)` and `(11.1.2)`, `α` is a
feasible point Armijo step along `d` at `xk`, the doubled-step segment
`xk + (t * α) • d`, `t ∈ [0, 2]`, lies in an open set `D` on which `f` is `C²`, the source
maximum `feasiblePointArmijoHessianBound f xk d α` then induces the canonical Chapter 1 Hessian
upper bound on that trace, and `xk + (2 * α) • d ∉ X`, then `f (xk + α • d)` satisfies the
boundary estimate `(11.1.6)` with `Γ(xk) = Metric.infDist xk Xᶜ`. -/
theorem feasiblePointArmijoStep_decrease_of_double_not_mem
    (f : E → ℝ) (X : Set E) (c1 : ℝ) (xk d : E) (α : ℝ) {D : Set E}
    (hD : IsOpen D)
    (h_segment : segment ℝ xk (xk + (2 * α) • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hα : IsFeasiblePointArmijoStep f X xk d c1 α)
    (h_double_not_mem : xk + (2 * α) • d ∉ X) :
    f (xk + α • d) ≤
      f xk +
        c1 * (Metric.infDist xk Xᶜ / (2 * ‖d‖)) *
          inner ℝ d (gradient f xk) := sorry

#print axioms feasiblePointArmijoHessianBound

end Chapter11Lemma111

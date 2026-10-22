/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_6_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_6_6

noncomputable section

open Filter

section InexactNewtonMethod

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Source/core/bridge triage:
-- * source-facing: the three textbook local-convergence consequences for the inexact Newton
--   method applied to `gradient f`
-- * core/canonical: `IsRegularZero`, `IsInexactNewtonSequence`, and the Chapter 3.6 convergence
--   theorems
-- * bridge/view: local minimizer plus Hessian positivity at `xStar` upgrades the gradient map to
--   a regular zero of the canonical Chapter 3.6 owner
--
-- Domain sampling:
-- * `Chapter03/Definition_3_5_1.lean`: `hessianAt`, `hessianQuadraticAt`
-- * `Chapter03/Algorithm_3_6_extra_2.lean`: `IsInexactNewtonSequence`
-- * `Chapter03/Theorem_3_6_2.lean`: `IsRegularZero`
-- * `Chapter03/Theorem_3_6_6.lean`: canonical local convergence theorems for inexact Newton
--
-- Primitive data: the source assumptions are a local minimizer `xStar`, an open neighborhood
-- `U` with `C¹` gradient regularity, and positive definiteness of the Hessian quadratic form at
-- `xStar`. The regular-zero package for `gradient f` is derived from those data, so it should not
-- stay as a parallel primitive surface in this file.

/-- The source assumptions of Theorem 3.6.7 canonically upgrade `gradient f` at `xStar` to the
Chapter 3.6 regular-zero owner. -/
theorem isRegularZero_gradient_of_isLocalMin_contDiffGradient_posDef
    (f : Point → ℝ) (xStar : Point) (U : Set Point)
    (hMin : IsLocalMin f xStar)
    (hxStar_mem : xStar ∈ U)
    (hU_open : IsOpen U)
    (hC1Grad : ContDiffOn ℝ 1 (gradient f) U)
    (hPosDef : ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y) :
    IsRegularZero (gradient f) xStar := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gradient, IsLocalMin.fderiv_eq_zero hMin, map_zero]
  · exact ⟨U, IsOpen.mem_nhds hU_open hxStar_mem, hC1Grad⟩
  · let hessianLin : Point →ₗ[ℝ] Point := (hessianAt f xStar).toLinearMap
    have hker : LinearMap.ker hessianLin = ⊥ := by
        refine LinearMap.ker_eq_bot'.2 ?_
        intro y hy
        by_contra hy_ne
        have hpositive : 0 < hessianQuadraticAt f xStar y := hPosDef y hy_ne
        have hzero : hessianQuadraticAt f xStar y = 0 := by
          simpa [hessianQuadraticAt, hessianLin] using congrArg (fun v ↦ inner ℝ y v) hy
        linarith
    have hsurj : LinearMap.range hessianLin = ⊤ :=
      LinearMap.ker_eq_bot_iff_range_eq_top.1 hker
    exact ⟨ContinuousLinearEquiv.ofBijective (hessianAt f xStar) hker hsurj, rfl⟩

/-- Chapter03 Theorem 3.6.7 (1): if `∇ f` is continuously differentiable on an open neighborhood
`U` of a local minimizer `xStar`, `hessianQuadraticAt f xStar` is positive definite, and
`x`, `s`, `r`, and `ηSeq` form an inexact Newton sequence with `0 ≤ ηSeq k ≤ η < 1`, then every
sufficiently close initial iterate generates a sequence converging `Q`-linearly to `xStar`. -/
theorem inexactNewton_qLinearlyConvergesTo_of_contDiffGradient_posDef
    (f : Point → ℝ) (xStar : Point) (U : Set Point)
    (hMin : IsLocalMin f xStar)
    (hxStar_mem : xStar ∈ U)
    (hU_open : IsOpen U)
    (hC1Grad : ContDiffOn ℝ 1 (gradient f) U)
    (hPosDef : ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y)
    (η : ℝ)
    (hη_lt_one : η < 1) :
    ∃ ε > 0, ∀ x s r : ℕ → Point, ∀ ηSeq : ℕ → ℝ, ‖x 0 - xStar‖ < ε →
      IsInexactNewtonSequence (gradient f) x s r ηSeq →
      HasInexactNewtonForcingBound ηSeq η →
      HasEventuallyLinearConvergenceTo x xStar := sorry

/-- Chapter03 Theorem 3.6.7 (2): under the same local minimizer, regularity, and positive
definiteness hypotheses on an open neighborhood `U`, if `x`, `s`, `r`, and `ηSeq` form an
inexact Newton sequence and `‖r k‖ = o(‖gradient f (x k)‖)`, then every sufficiently close
initial iterate generates a sequence converging `Q`-superlinearly to `xStar`. -/
theorem inexactNewton_qSuperlinearlyConvergesTo_of_contDiffGradient_posDef
    (f : Point → ℝ) (xStar : Point) (U : Set Point)
    (hMin : IsLocalMin f xStar)
    (hxStar_mem : xStar ∈ U)
    (hU_open : IsOpen U)
    (hC1Grad : ContDiffOn ℝ 1 (gradient f) U)
    (hPosDef : ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y)
    (η : ℝ)
    (hη_lt_one : η < 1) :
    ∃ ε > 0, ∀ x s r : ℕ → Point, ∀ ηSeq : ℕ → ℝ, ‖x 0 - xStar‖ < ε →
      IsInexactNewtonSequence (gradient f) x s r ηSeq →
      HasInexactNewtonForcingBound ηSeq η →
      ((fun k ↦ ‖r k‖) =o[atTop] fun k ↦ ‖gradient f (x k)‖) →
      HasSuperlinearConvergenceTo x xStar := sorry

/-- Chapter03 Theorem 3.6.7 (3): under the same local minimizer, regularity, and positive
definiteness hypotheses on an open neighborhood `U`, if `x`, `s`, `r`, and `ηSeq` form an
inexact Newton sequence and `‖r k‖ = O(‖gradient f (x k)‖²)`, then every sufficiently close
initial iterate generates a sequence converging `Q`-quadratically to `xStar`. -/
theorem inexactNewton_qQuadraticallyConvergesTo_of_contDiffGradient_posDef
    (f : Point → ℝ) (xStar : Point) (U : Set Point)
    (hMin : IsLocalMin f xStar)
    (hxStar_mem : xStar ∈ U)
    (hU_open : IsOpen U)
    (hC1Grad : ContDiffOn ℝ 1 (gradient f) U)
    (hPosDef : ∀ y : Point, y ≠ 0 → 0 < hessianQuadraticAt f xStar y)
    (η : ℝ)
    (hη_lt_one : η < 1) :
    ∃ ε > 0, ∀ x s r : ℕ → Point, ∀ ηSeq : ℕ → ℝ, ‖x 0 - xStar‖ < ε →
      IsInexactNewtonSequence (gradient f) x s r ηSeq →
      HasInexactNewtonForcingBound ηSeq η →
      ((fun k ↦ ‖r k‖) =O[atTop] fun k ↦ ‖gradient f (x k)‖ ^ (2 : ℕ)) →
      HasQuadraticConvergenceTo x xStar := by
  sorry

end InexactNewtonMethod

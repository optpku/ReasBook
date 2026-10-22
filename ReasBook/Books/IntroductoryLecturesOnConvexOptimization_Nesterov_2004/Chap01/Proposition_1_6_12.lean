/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Example_1_6_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open EuclideanSpace
open scoped Gradient

noncomputable section

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "leftPoint" => single 1 (-1 : ℝ)
local notation "rightPoint" => single 1 (1 : ℝ)
local notation "initialPoint" => single 0 (1 : ℝ)

/- Primary domain:
* gradient-method dynamics and second-order stationary-point analysis for a concrete polynomial
  objective on `ℝ²`

Sampled owner-style declarations:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `∇²` / `hessianMatrix` in `Definition_1_4_16.lean`
* `strict_local_minimizer_of_gradient_zero_of_hessian_posDef` in `Theorem_1_4_21.lean`
* `unitStepGradientMethod_converges_to_nonminimizing_stationary_point` in
  `Example_1_6_11.lean`

Source/core/bridge triage:
* source-facing: the explicit quartic formulas, stationary-point classification, the universal
  axis-invariance claim, and the corrected unit-step convergence to a nonminimizing stationary
  point
* core/canonical: `gradientMethod stepSize f x0`, `∇² f x`, `HasGradientAt f 0 xStar`,
  and `IsLocalMin f xStar`
* bridge/view: the coordinate formulas on `EuclideanSpace ℝ (Fin 2)` and the specializations of
  the second-order sufficient condition to `leftPoint` and `rightPoint`

Owner abstraction:
* the quartic objective `saddlePointConvergenceObjective` from `Example_1_6_11`, together with the
  canonical gradient-method and second-order owner API

Primitive data:
* the quartic objective `saddlePointConvergenceObjective`
* the canonical comparison points `0`, `single 1 (-1)`, and `single 1 1`

Derived API:
* the explicit gradient and Hessian matrix formulas
* the stationary-point description
* the left/right isolated-minimum statements, as source-facing specializations of
  `strict_local_minimizer_of_gradient_zero_of_hessian_posDef`
* the universal axis-invariance statement for trajectories started at `(1, 0)`
* the proposition-level unit-step convergence/nonminimality conclusion, reused directly from the
  owner theorem

This file therefore keeps the source-facing quartic companions and the universal trajectory
invariance claim, while the corrected constant-step convergence conclusion is reused from the
existing owner theorem rather than duplicated as a parallel local theorem. -/

/-- Helper for Proposition 1.6.12: the quartic objective has the explicit gradient witness
`(x₁, x₂^3 - x₂)`. -/
private lemma saddlePointConvergenceObjective_hasGradientAt (x : E) :
    HasGradientAt saddlePointConvergenceObjective
      (single 0 (x 0) + single 1 (x 1 ^ 3 - x 1)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  change
    HasFDerivAt
      (fun y : E ↦
        (1 / 2 : ℝ) * y 0 ^ 2 + (1 / 4 : ℝ) * y 1 ^ 4 - (1 / 2 : ℝ) * y 1 ^ 2)
      ((InnerProductSpace.toDual ℝ E)
        (single 0 (x 0) + single 1 (x 1 ^ 3 - x 1)))
      x
  let proj0 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : E →L[ℝ] ℝ)
  let proj1 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : E →L[ℝ] ℝ)
  have h0 : HasFDerivAt (fun y : E ↦ y 0) proj0 x := by
    simpa [proj0] using (PiLp.hasFDerivAt_apply 2 x 0)
  have h1 : HasFDerivAt (fun y : E ↦ y 1) proj1 x := by
    simpa [proj1] using (PiLp.hasFDerivAt_apply 2 x 1)
  -- Differentiate the three scalar polynomial pieces coordinatewise.
  have hsq0 :
      HasFDerivAt (fun y : E ↦ y 0 ^ 2) (((2 : ℝ) * x 0) • proj0) x := by
    simpa [two_nsmul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using (h0.pow 2)
  have hpow4 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 4) (((4 : ℝ) * x 1 ^ 3) • proj1) x := by
    simpa [pow_succ, pow_succ', mul_comm, mul_left_comm, mul_assoc] using (h1.pow 4)
  have hsq1 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 2) (((2 : ℝ) * x 1) • proj1) x := by
    simpa [two_nsmul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using (h1.pow 2)
  have hmain :
      HasFDerivAt
        (fun y : E ↦
          (1 / 2 : ℝ) * y 0 ^ 2 + (1 / 4 : ℝ) * y 1 ^ 4 - (1 / 2 : ℝ) * y 1 ^ 2)
        ((x 0) • proj0 + (x 1 ^ 3 - x 1) • proj1) x := by
    -- Assemble the derivative from the quadratic and quartic coordinate terms.
    simpa [sub_eq_add_neg, proj0, proj1, smul_add, add_smul, mul_smul, mul_assoc, mul_comm,
      mul_left_comm, add_comm, add_left_comm, add_assoc] using
      (hsq0.const_smul (1 / 2 : ℝ)).add
        ((hpow4.const_smul (1 / 4 : ℝ)).sub (hsq1.const_smul (1 / 2 : ℝ)))
  have hdual :
      (x 0) • proj0 + (x 1 ^ 3 - x 1) • proj1 =
        (InnerProductSpace.toDual ℝ E)
          (single 0 (x 0) + single 1 (x 1 ^ 3 - x 1)) := by
    -- The coordinate linear form is the inner-product dual of the explicit gradient vector.
    ext y
    have hinner0 : inner ℝ (single 0 (x 0)) y = (x 0) * y 0 := by
      simpa using (EuclideanSpace.inner_single_left 0 (x 0) y)
    have hinner1 :
        inner ℝ (single 1 (x 1 ^ 3 - x 1)) y = (x 1 ^ 3 - x 1) * y 1 := by
      simpa using (EuclideanSpace.inner_single_left 1 (x 1 ^ 3 - x 1) y)
    rw [InnerProductSpace.toDual_apply_apply, inner_add_left, hinner0, hinner1]
    simp [proj0, proj1]
  exact hmain.congr_fderiv hdual

/-- Helper for Proposition 1.6.12: the explicit quartic gradient map has derivative given by the
diagonal matrix `diag(1, 3 x₂² - 1)`. -/
private lemma explicitQuarticGradient_hasFDerivAt (x : E) :
    HasFDerivAt
      (fun y : E ↦ single 0 (y 0) + single 1 (y 1 ^ 3 - y 1))
      (LinearMap.toContinuousLinearMap
        ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin))
      x := by
  let proj0 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : E →L[ℝ] ℝ)
  let proj1 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : E →L[ℝ] ℝ)
  have h0 : HasFDerivAt (fun y : E ↦ y 0) proj0 x := by
    simpa [proj0] using (PiLp.hasFDerivAt_apply 2 x 0)
  have h1 : HasFDerivAt (fun y : E ↦ y 1) proj1 x := by
    simpa [proj1] using (PiLp.hasFDerivAt_apply 2 x 1)
  -- The second coordinate differentiates to `3 x₂² - 1`.
  have hcube :
      HasFDerivAt (fun y : E ↦ y 1 ^ 3) (((3 : ℝ) * x 1 ^ 2) • proj1) x := by
    simpa [pow_succ, pow_succ', mul_comm, mul_left_comm, mul_assoc] using (h1.pow 3)
  have hcoord1 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 3 - y 1) (((3 : ℝ) * x 1 ^ 2 - 1) • proj1) x := by
    simpa [sub_eq_add_neg, proj1, smul_add, add_smul, mul_smul, mul_assoc, mul_comm,
      mul_left_comm, add_comm, add_left_comm, add_assoc] using hcube.sub h1
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  fin_cases i
  · change HasFDerivWithinAt
        (fun y : E ↦ (single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)).ofLp 0)
        ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0).comp
          (LinearMap.toContinuousLinearMap
            ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin)))
        Set.univ x
    have hfun0 :
        (fun y : E ↦ (single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)).ofLp 0) =
          fun y : E ↦ y 0 := by
      funext y
      simp
    rw [hfun0]
    have hcomp0 :
        proj0.comp
          (LinearMap.toContinuousLinearMap
            ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin)) =
          proj0 := by
      ext y
      simp [proj0, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_two]
    exact (h0.hasFDerivWithinAt).congr_fderiv hcomp0.symm
  · change HasFDerivWithinAt
        (fun y : E ↦ (single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)).ofLp 1)
        ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1).comp
          (LinearMap.toContinuousLinearMap
            ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin)))
        Set.univ x
    have hfun1 :
        (fun y : E ↦ (single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)).ofLp 1) =
          fun y : E ↦ y 1 ^ 3 - y 1 := by
      funext y
      simp
    rw [hfun1]
    have hcomp1 :
        proj1.comp
          (LinearMap.toContinuousLinearMap
            ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin)) =
          ((3 : ℝ) * x 1 ^ 2 - 1) • proj1 := by
      ext y
      simp [proj1, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_two]
    exact (hcoord1.hasFDerivWithinAt).congr_fderiv hcomp1.symm

/-- Helper for Proposition 1.6.12: the gradient map has derivative given by the explicit Hessian
matrix. -/
private lemma saddlePointConvergenceObjective_gradient_hasFDerivAt (x : E) :
    HasFDerivAt (∇ saddlePointConvergenceObjective)
      (LinearMap.toContinuousLinearMap
        ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin))
      x := by
  have hfun :
      (∇ saddlePointConvergenceObjective) =
        (fun y : E ↦ single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)) := by
    funext y
    exact (saddlePointConvergenceObjective_hasGradientAt y).gradient
  -- Rewrite to the explicit gradient map and differentiate that polynomial map directly.
  rw [hfun]
  exact explicitQuarticGradient_hasFDerivAt x

/-- Helper for Proposition 1.6.12: stationarity forces the scalar equations
`x₁ = 0` and `x₂^3 - x₂ = 0`. -/
private lemma quartic_stationary_coordinate_eq_zero {x : E}
    (h : HasGradientAt saddlePointConvergenceObjective 0 x) :
    x 0 = 0 ∧ x 1 ^ 3 - x 1 = 0 := by
  have hgrad : ∇ saddlePointConvergenceObjective x = 0 := h.gradient
  -- Read off the two scalar equations from the explicit gradient formula.
  have hcoord0 : x 0 = 0 := by
    have hexp0 : (∇ saddlePointConvergenceObjective x) 0 = x 0 := by
      simpa using congrArg (fun v : E ↦ v 0)
        ((saddlePointConvergenceObjective_hasGradientAt x).gradient)
    have hzero0 : (∇ saddlePointConvergenceObjective x) 0 = 0 := by
      simpa using congrArg (fun v : E ↦ v 0) hgrad
    exact hexp0.symm.trans hzero0
  have hcoord1 : x 1 ^ 3 - x 1 = 0 := by
    have hexp1 : (∇ saddlePointConvergenceObjective x) 1 = x 1 ^ 3 - x 1 := by
      simpa using congrArg (fun v : E ↦ v 1)
        ((saddlePointConvergenceObjective_hasGradientAt x).gradient)
    have hzero1 : (∇ saddlePointConvergenceObjective x) 1 = 0 := by
      simpa using congrArg (fun v : E ↦ v 1) hgrad
    exact hexp1.symm.trans hzero1
  exact ⟨hcoord0, hcoord1⟩

/-- Helper for Proposition 1.6.12: the side-point Hessian matrix `diag(1, 2)` is positive
definite. -/
private lemma quartic_side_hessian_posDef :
    ((!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) := by
  -- The matrix is diagonal with strictly positive diagonal entries.
  have hdiag :
      (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [hdiag]
  exact Matrix.PosDef.diagonal (n := Fin 2) (R := ℝ) (d := ![1, 2]) (by
    intro i
    fin_cases i <;> norm_num)

-- Proof sketch: differentiate the explicit polynomial formula for
-- `saddlePointConvergenceObjective` coordinatewise; the first coordinate contributes `x₁`, and
-- the second contributes `x₂^3 - x₂`.
/-- The quartic example objective has gradient `(x₁, x₂^3 - x₂)`. -/
theorem saddlePointConvergenceObjective_gradient_eq (x : E) :
    ∇ saddlePointConvergenceObjective x =
      single 0 (x 0) + single 1 (x 1 ^ 3 - x 1) := by
  -- The explicit gradient witness from the helper is the canonical gradient.
  exact (saddlePointConvergenceObjective_hasGradientAt x).gradient

-- Proof sketch: differentiate the explicit gradient formula
-- `x ↦ (x 0, x 1 ^ 3 - x 1)` once more; this yields the diagonal matrix with entries
-- `1` and `3 x₂² - 1`.
/-- The Hessian of the quartic example objective is the diagonal matrix
`diag(1, 3 x₂² - 1)`. -/
theorem saddlePointConvergenceObjective_hessian_eq (x : E) :
    ∇² saddlePointConvergenceObjective x =
      !![1, 0; 0, 3 * x 1 ^ 2 - 1] := by
  apply Matrix.toEuclideanLin.injective
  have hgrad :
      fderiv ℝ (∇ saddlePointConvergenceObjective) x =
        LinearMap.toContinuousLinearMap
          ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin) := by
    exact (saddlePointConvergenceObjective_gradient_hasFDerivAt x).fderiv
  -- Compare the Hessian operator with the derivative of the explicit gradient map.
  calc
    (∇² saddlePointConvergenceObjective x).toEuclideanLin =
        hessian saddlePointConvergenceObjective x := by
      simpa using hessianMatrix_toEuclideanLin saddlePointConvergenceObjective x
    _ = ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin) := by
      simpa [hessian] using congrArg ContinuousLinearMap.toLinearMap hgrad

-- Proof sketch: the quartic polynomial is differentiable everywhere, so the owner stationary
-- condition `HasGradientAt saddlePointConvergenceObjective 0 x` is equivalent to
-- `∇ saddlePointConvergenceObjective x = 0`. Combine this with
-- `saddlePointConvergenceObjective_gradient_eq`, solve
-- `x₁ = 0` and `x₂^3 - x₂ = x₂ (x₂^2 - 1) = 0`, and identify the resulting three points with the
-- canonical points `0`, `single 1 (-1)`, and `single 1 1`.
/-- The stationary points of the quartic example objective are exactly `(0, 0)`, `(0, -1)`, and
`(0, 1)`. -/
theorem saddlePointConvergenceObjective_stationary_iff (x : E) :
    HasGradientAt saddlePointConvergenceObjective 0 x ↔
      x = 0 ∨ x = leftPoint ∨ x = rightPoint := by
  constructor
  · intro h
    obtain ⟨hx0, hx1⟩ := quartic_stationary_coordinate_eq_zero h
    have hfactor : x 1 * (x 1 ^ 2 - 1) = 0 := by
      nlinarith [hx1]
    rcases mul_eq_zero.mp hfactor with hx1zero | hsq
    · -- The vanishing second coordinate identifies the origin.
      left
      ext i
      fin_cases i <;> simp [hx0, hx1zero]
    · have hsquare : x 1 ^ 2 = 1 := by
        linarith
      have hsign : x 1 = 1 ∨ x 1 = -1 := by
        have hsquare' : x 1 ^ 2 = (1 : ℝ) ^ 2 := by
          simpa using hsquare
        simpa using (sq_eq_sq_iff_eq_or_eq_neg.mp hsquare')
      rcases hsign with hx1one | hx1neg
      · right
        right
        ext i
        fin_cases i <;> simp [hx0, hx1one]
      · right
        left
        ext i
        fin_cases i <;> simp [hx0, hx1neg]
  · intro hx
    rcases hx with rfl | rfl | rfl
    · -- The explicit gradient formula vanishes at the origin.
      convert saddlePointConvergenceObjective_hasGradientAt (0 : E) using 1
      ext i
      fin_cases i <;> simp
    · -- The explicit gradient formula vanishes at `(0, -1)`.
      convert saddlePointConvergenceObjective_hasGradientAt leftPoint using 1
      ext i
      fin_cases i <;> norm_num
    · -- The explicit gradient formula vanishes at `(0, 1)`.
      convert saddlePointConvergenceObjective_hasGradientAt rightPoint using 1
      ext i
      fin_cases i <;> norm_num

-- Proof sketch: evaluate the Hessian matrix at `(0, -1)` to obtain `diag(1, 2)`, verify positive
-- definiteness, and apply
-- `strict_local_minimizer_of_gradient_zero_of_hessian_posDef`, whose conclusion already has the
-- metric-radius shape below.
/-- The point `(0, -1)` is an isolated local minimum of the quartic example objective. -/
theorem leftPoint_isolatedLocalMin :
    ∃ ε > 0, ∀ ⦃y : E⦄,
      y ≠ leftPoint →
        dist y leftPoint < ε →
          saddlePointConvergenceObjective leftPoint <
            saddlePointConvergenceObjective y := by
  have hstationary : HasGradientAt saddlePointConvergenceObjective 0 leftPoint := by
    exact (saddlePointConvergenceObjective_stationary_iff leftPoint).mpr (Or.inr (Or.inl rfl))
  have hgradDiff : DifferentiableAt ℝ (∇ saddlePointConvergenceObjective) leftPoint := by
    exact (saddlePointConvergenceObjective_gradient_hasFDerivAt leftPoint).differentiableAt
  have hH : (∇² saddlePointConvergenceObjective leftPoint).PosDef := by
    -- The Hessian at the left side point is exactly `diag(1, 2)`.
    have hhess : ∇² saddlePointConvergenceObjective leftPoint = !![1, 0; 0, 2] := by
      rw [saddlePointConvergenceObjective_hessian_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    rw [hhess]
    exact quartic_side_hessian_posDef
  simpa using
    strict_local_minimizer_of_gradient_zero_of_hessian_posDef hstationary hgradDiff hH

-- Proof sketch: evaluate the Hessian matrix at `(0, 1)` to obtain `diag(1, 2)`, verify positive
-- definiteness, and apply
-- `strict_local_minimizer_of_gradient_zero_of_hessian_posDef`, whose conclusion already has the
-- metric-radius shape below.
/-- The point `(0, 1)` is an isolated local minimum of the quartic example objective. -/
theorem rightPoint_isolatedLocalMin :
    ∃ ε > 0, ∀ ⦃y : E⦄,
      y ≠ rightPoint →
        dist y rightPoint < ε →
          saddlePointConvergenceObjective rightPoint <
            saddlePointConvergenceObjective y := by
  have hstationary : HasGradientAt saddlePointConvergenceObjective 0 rightPoint := by
    exact (saddlePointConvergenceObjective_stationary_iff rightPoint).mpr (Or.inr (Or.inr rfl))
  have hgradDiff : DifferentiableAt ℝ (∇ saddlePointConvergenceObjective) rightPoint := by
    exact (saddlePointConvergenceObjective_gradient_hasFDerivAt rightPoint).differentiableAt
  have hH : (∇² saddlePointConvergenceObjective rightPoint).PosDef := by
    -- The Hessian at the right side point is again `diag(1, 2)`.
    have hhess : ∇² saddlePointConvergenceObjective rightPoint = !![1, 0; 0, 2] := by
      rw [saddlePointConvergenceObjective_hessian_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    rw [hhess]
    exact quartic_side_hessian_posDef
  simpa using
    strict_local_minimizer_of_gradient_zero_of_hessian_posDef hstationary hgradDiff hH

-- Proof sketch: use the recurrence together with
-- `saddlePointConvergenceObjective_gradient_eq`. If the second coordinate of `x k` is `0`, then
-- the second coordinate of the gradient also vanishes, so the update preserves the value `0`.
-- Apply this to the owner trajectory `gradientMethod stepSize saddlePointConvergenceObjective
-- initialPoint`, whose start point and update are canonical.
/-- Proposition 1.6.12 (1): every quartic-example gradient trajectory started at `(1, 0)` stays
on the horizontal axis `x₂ = 0`. -/
theorem quarticGradientMethod_axisInvariant
    (stepSize : ℕ → ℝ) (k : ℕ) :
    (gradientMethod stepSize saddlePointConvergenceObjective
      initialPoint k) 1 = 0 := by
  induction k with
  | zero =>
      -- The prescribed initial point is `(1, 0)`.
      norm_num
  | succ k hk =>
      let xk := gradientMethod stepSize saddlePointConvergenceObjective initialPoint k
      have hgradcoord : (∇ saddlePointConvergenceObjective xk) 1 = 0 := by
        -- On the axis `x₂ = 0`, the second gradient component vanishes as well.
        have := congrArg (fun v : E ↦ v 1) (saddlePointConvergenceObjective_gradient_eq xk)
        have hexp1 : (∇ saddlePointConvergenceObjective xk) 1 = xk 1 ^ 3 - xk 1 := by
          simpa using this
        have hxk1 : xk 1 = 0 := by
          simpa [xk] using hk
        have hcoord_rhs : xk 1 ^ 3 - xk 1 = 0 := by
          simp [hxk1]
        exact hexp1.trans hcoord_rhs
      rw [gradientMethod_succ]
      -- The update subtracts a multiple of the zero second gradient component.
      change xk 1 - stepSize k * (∇ saddlePointConvergenceObjective xk) 1 = 0
      rw [hk, hgradcoord]
      ring

/- Proposition 1.6.12 has two source-facing layers in this formalization:
the universal horizontal-axis invariance of trajectories started at `(1, 0)`, and the corrected
unit-step convergence-to-a-nonminimizing-stationary-point conclusion from
`Example_1_6_11`. The latter is reused through the owner theorem
`unitStepGradientMethod_converges_to_nonminimizing_stationary_point`, so the proposition keeps
that second clause as a direct owner recall rather than a duplicate local theorem. -/
/- Proposition 1.6.12 (2): for the constant unit-step schedule, the quartic-example trajectory
started at `(1, 0)` converges to `(0, 0)`, and this limit point is stationary but not a local
minimum for `saddlePointConvergenceObjective`. -/
recall unitStepGradientMethod_converges_to_nonminimizing_stationary_point :
    Tendsto
      (gradientMethod (fun _ : ℕ ↦ (1 : ℝ))
        saddlePointConvergenceObjective initialPoint)
      atTop (nhds (0 : E)) ∧
      HasGradientAt saddlePointConvergenceObjective 0 (0 : E) ∧
      ¬ IsLocalMin saddlePointConvergenceObjective (0 : E)

end

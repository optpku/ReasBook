/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

/-
Domain sampling for this item:
- primary domain: quasi-Newton secant equations and curvature pairings;
- sampled canonical declarations in this domain:
  `LinearMap.congr_fun`,
  endomorphism composition on `E →ₗ[𝕜] E`,
  `Matrix.toEuclideanLin`,
  `Matrix.toLpLin_apply`,
  `PiLp.inner_apply`;
- best owner abstraction: the secant equation lives on a module endomorphism `E →ₗ[𝕜] E`,
  while the curvature pairing and Euclidean matrix bridges live on the real inner-product
  specialization;
- primitive data here: the inverse-form secant equation, the Hessian-form secant equation, and
  the curvature pairing itself;
- derived API here: inverse-conversion lemmas and Euclidean matrix-model bridge lemmas.

This file therefore makes the public Chapter 5 secant/curvature owners operator-valued and keeps
the Euclidean matrix model only as a thin bridge.
-/

section

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

/-- Chapter05 Definition 5.1-extra-1 (1): the inverse-Hessian form of the quasi-Newton equation
for an endomorphism `H` and secant data `y s` is `H y = s`. -/
def satisfiesQuasiNewtonEquation (H : E →ₗ[𝕜] E) (y s : E) : Prop :=
  H y = s

/-- Chapter05 Definition 5.1-extra-1 (2): the Hessian-approximation form of the quasi-Newton
equation for an endomorphism `B` and secant data `s y` is `B s = y`. -/
def satisfiesQuasiNewtonEquationHessianForm
    (B : E →ₗ[𝕜] E) (s y : E) : Prop :=
  B s = y

/-- A left inverse for `H` converts the inverse-Hessian form of the quasi-Newton equation into
its Hessian-form expression. -/
theorem satisfiesQuasiNewtonEquationHessianForm_of_mul_eq_one
    {H B : E →ₗ[𝕜] E} (hBH : B * H = 1) {y s : E}
    (hQN : satisfiesQuasiNewtonEquation H y s) :
    satisfiesQuasiNewtonEquationHessianForm B s y := by
  rw [satisfiesQuasiNewtonEquationHessianForm, ← hQN]
  simpa using LinearMap.congr_fun hBH y

/-- A right inverse for `B` converts the Hessian-form quasi-Newton equation back to the
inverse-Hessian form. -/
theorem satisfiesQuasiNewtonEquation_of_mul_eq_one
    {H B : E →ₗ[𝕜] E} (hHB : H * B = 1) {s y : E}
    (hQN : satisfiesQuasiNewtonEquationHessianForm B s y) :
    satisfiesQuasiNewtonEquation H y s := by
  rw [satisfiesQuasiNewtonEquation, ← hQN]
  simpa using LinearMap.congr_fun hHB s

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Chapter05 Definition 5.1-extra-1 (3): the curvature condition attached to secant data
`s y` is the positivity relation `0 < ⟪s, y⟫_ℝ`. -/
def satisfiesCurvatureCondition (s y : E) : Prop :=
  0 < ⟪s, y⟫_ℝ

/-- Under the Hessian-form quasi-Newton equation, the curvature pairing `⟪s, y⟫_ℝ` is the
quadratic form value `⟪s, B s⟫_ℝ`. -/
theorem satisfiesCurvatureCondition_iff_inner_apply_pos
    {B : E →ₗ[ℝ] E} {s y : E}
    (hQN : satisfiesQuasiNewtonEquationHessianForm B s y) :
    satisfiesCurvatureCondition s y ↔ 0 < ⟪s, B s⟫_ℝ := by
  rw [satisfiesQuasiNewtonEquationHessianForm] at hQN
  rw [satisfiesCurvatureCondition, ← hQN]

end

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- On the Chapter 5 Euclidean matrix model, the inverse-form secant equation is exactly the
matrix-vector equation `H.mulVec y = s` after passing through `Matrix.toEuclideanLin`. -/
theorem satisfiesQuasiNewtonEquation_toEuclideanLin_iff
    {H : MatrixN} {y s : Point} :
    satisfiesQuasiNewtonEquation H.toEuclideanLin y s ↔ H.mulVec y.ofLp = s.ofLp := by
  rw [satisfiesQuasiNewtonEquation, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  constructor
  · intro h
    simpa using congrArg WithLp.ofLp h
  · intro h
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using congrArg (WithLp.toLp 2) h

/-- On the Chapter 5 Euclidean matrix model, the Hessian-form secant equation is exactly the
matrix-vector equation `B.mulVec s = y` after passing through `Matrix.toEuclideanLin`. -/
theorem satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff
    {B : MatrixN} {s y : Point} :
    satisfiesQuasiNewtonEquationHessianForm B.toEuclideanLin s y ↔ B.mulVec s.ofLp = y.ofLp := by
  rw [satisfiesQuasiNewtonEquationHessianForm, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  constructor
  · intro h
    simpa using congrArg WithLp.ofLp h
  · intro h
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using congrArg (WithLp.toLp 2) h

/-- On the Chapter 5 Euclidean matrix model, the curvature condition is exactly the usual
Euclidean inner-product positivity `0 < dotProduct s y`. -/
theorem satisfiesCurvatureCondition_iff_dotProduct_pos
    {s y : Point} :
    satisfiesCurvatureCondition s y ↔ 0 < dotProduct s y := by
  rw [satisfiesCurvatureCondition]
  simp [PiLp.inner_apply, dotProduct, mul_comm]

/-- Under the Hessian-form quasi-Newton equation on the Chapter 5 Euclidean matrix model, the
curvature pairing `dotProduct s y` is the quadratic form value `dotProduct s (B.mulVec s)`. -/
theorem satisfiesCurvatureCondition_iff_dotProduct_mulVec_pos
    {B : MatrixN} {s y : Point}
    (hQN : satisfiesQuasiNewtonEquationHessianForm B.toEuclideanLin s y) :
    satisfiesCurvatureCondition s y ↔ 0 < dotProduct s (B.mulVec s) := by
  rw [satisfiesCurvatureCondition_iff_dotProduct_pos]
  have hmul : B.mulVec s = y :=
    satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mp hQN
  simp [hmul]


end

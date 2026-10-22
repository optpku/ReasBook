/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Algorithm_12_2_2

noncomputable section

/-
Chapter12 Exercise 12.2 compares two source-facing damped-BFGS candidates for the modified
secant vector `ȳ_k`. The Chapter 12 Wilson-Han-Powell owner already names the stagewise
displacement `s_k` as `method.stepVectorAt k` and the gradient difference `y_k` as
`method.gradientDifferenceAt k`. This file therefore keeps one source-facing modified-secant
owner and records the two Exercise 12.2 comparison choices as thin bridge/view companions,
without introducing a fake preference theorem.
-/

/-- The damped-BFGS modified secant vector `ȳ` is the affine combination `α • y + β • c`
of the secant vector `y` and a comparison vector `c`. -/
def dampedBfgsModifiedSecantVector {n : ℕ}
    (α β : ℝ) (y comparison : WilsonHanPowellPoint n) :
    WilsonHanPowellPoint n :=
  α • y + β • comparison

/-- Unfolding `dampedBfgsModifiedSecantVector α β y c` gives the source affine combination
`α • y + β • c`. -/
@[simp] theorem dampedBfgsModifiedSecantVector_eq {n : ℕ}
    (α β : ℝ) (y comparison : WilsonHanPowellPoint n) :
    dampedBfgsModifiedSecantVector α β y comparison =
      α • y + β • comparison :=
  rfl

/-- The stagewise Hessian-side comparison vector `B_k s_k`, expressed in the Wilson-Han-Powell
primal space through the canonical matrix action `Matrix.toEuclideanLin`. -/
def WilsonHanPowellMethod.hessianStepImageAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    WilsonHanPowellPoint n :=
  (method.hessianApproximation k).toEuclideanLin (method.stepVectorAt k)

/-- Unfolding `method.hessianStepImageAt k` gives the stagewise vector `B_k s_k`. -/
@[simp] theorem WilsonHanPowellMethod.hessianStepImageAt_eq {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (k : ℕ) :
    method.hessianStepImageAt k =
      (method.hessianApproximation k).toEuclideanLin (method.stepVectorAt k) :=
  rfl

/-- The stagewise modified secant vector at stage `k` formed from the recorded `y_k` and an
explicit comparison vector. Exercise 12.2 compares two choices of this comparison vector. -/
def WilsonHanPowellMethod.dampedBfgsModifiedSecantVectorAt {n m : ℕ}
    (method : WilsonHanPowellMethod n m)
    (α β : ℝ) (k : ℕ) (comparison : WilsonHanPowellPoint n) :
    WilsonHanPowellPoint n :=
  dampedBfgsModifiedSecantVector α β (method.gradientDifferenceAt k) comparison

/-- Unfolding `method.dampedBfgsModifiedSecantVectorAt α β k c` gives the stagewise affine
combination `α • y_k + β • c`. -/
@[simp] theorem WilsonHanPowellMethod.dampedBfgsModifiedSecantVectorAt_eq {n m : ℕ}
    (method : WilsonHanPowellMethod n m)
    (α β : ℝ) (k : ℕ) (comparison : WilsonHanPowellPoint n) :
    method.dampedBfgsModifiedSecantVectorAt α β k comparison =
      dampedBfgsModifiedSecantVector α β (method.gradientDifferenceAt k) comparison :=
  rfl

/-- Chapter12 Exercise 12.2, first candidate: at stage `k`, choose the comparison vector
`B_k s_k`, so `ȳ_k = α • y_k + β • (B_k s_k)`. -/
theorem WilsonHanPowellMethod.dampedBfgsModifiedSecantVectorAt_eq_hessianStepImage {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (α β : ℝ) (k : ℕ) :
    method.dampedBfgsModifiedSecantVectorAt α β k (method.hessianStepImageAt k) =
      α • method.gradientDifferenceAt k + β • method.hessianStepImageAt k :=
  rfl

/-- Chapter12 Exercise 12.2, second candidate: at stage `k`, choose the comparison vector
`s_k`, so `ȳ_k = α • y_k + β • s_k`. -/
theorem WilsonHanPowellMethod.dampedBfgsModifiedSecantVectorAt_eq_stepVector {n m : ℕ}
    (method : WilsonHanPowellMethod n m) (α β : ℝ) (k : ℕ) :
    method.dampedBfgsModifiedSecantVectorAt α β k (method.stepVectorAt k) =
      α • method.gradientDifferenceAt k + β • method.stepVectorAt k :=
  rfl

end

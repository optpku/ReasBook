/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_4

section Chapter01Theorem145

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Semantic recall: `lean_leansearch` surfaced `IsLocalMin.hasFDerivAt_eq_zero` and
-- `IsLocalMin.fderiv_eq_zero`, while the local Chapter 1 precedent records Hessian positivity
-- through `(iteratedFDeriv ℝ 2 f xStar) ![y, y]`.

/-- Helper for Chapter01 Theorem 1.4.5: restricting a local minimizer to an affine line through
`xStar` preserves local minimality at the base point. -/
lemma isLocalMin_comp_affineLine
    (f : E → ℝ) (xStar y : E) (hmin : IsLocalMin f xStar) :
    IsLocalMin (fun t : ℝ => f (xStar + t • y)) 0 := by
  let γ : ℝ → E := fun t => xStar + t • y
  have hminAt : IsLocalMin f (γ 0) := by
    simpa [γ] using hmin
  have hγ : ContinuousAt γ 0 := by
    -- The affine line map is smooth, hence continuous at the base point.
    have hγC2 : ContDiffAt ℝ 2 γ 0 := by
      simpa [γ] using contDiffAt_const.add (contDiffAt_id.smul_const y)
    simpa using hγC2.continuousAt
  -- Compose the local minimum with the continuous affine line restriction.
  have hcomp : IsLocalMin (f ∘ γ) 0 := hminAt.comp_continuous hγ
  change IsLocalMin (f ∘ γ) 0
  exact hcomp

/-- Helper for Chapter01 Theorem 1.4.5: a twice continuously differentiable real-valued function
has nonnegative second derivative at a local minimizer. -/
lemma iteratedDeriv_two_nonneg_of_isLocalMin
    (g : ℝ → ℝ) (x : ℝ) (hC2 : ContDiffAt ℝ 2 g x) (hmin : IsLocalMin g x) :
    0 ≤ iteratedDeriv 2 g x := by
  by_contra hnonneg
  have hneg : iteratedDeriv 2 g x < 0 := lt_of_not_ge hnonneg
  -- Convert the negative second derivative into the derivative-test hypothesis.
  have hderivZero : deriv g x = 0 := hmin.deriv_eq_zero
  have hsecondNeg : deriv (deriv g) x < 0 := by
    simpa [iteratedDeriv_succ', iteratedDeriv_one] using hneg
  have hmax : IsLocalMax g x := by
    -- The scalar second-derivative test turns the negative curvature into a local maximum.
    exact isLocalMax_of_deriv_deriv_neg hsecondNeg hderivZero hC2.continuousAt
  have heq : g =ᶠ[nhds x] fun _ ↦ g x := by
    -- Having both a local minimum and a local maximum forces local constancy.
    simpa [IsLocalMin, IsLocalMax] using
      eventuallyEq_of_isMinFilter_of_isMaxFilter hmin hmax
  have hzero : iteratedDeriv 2 g x = 0 := by
    -- Eventual equality lets us replace `g` by the constant germ near `x`.
    have hiter : iteratedDeriv 2 g x = iteratedDeriv 2 (fun _ ↦ g x) x :=
      Filter.EventuallyEq.iteratedDeriv_eq 2 heq
    calc
      iteratedDeriv 2 g x = iteratedDeriv 2 (fun _ ↦ g x) x := hiter
      _ = 0 := by
        simpa using (iteratedDeriv_const (n := 2) (c := g x) (x := x))
  exact (lt_irrefl (0 : ℝ)) (by simp [hzero] at hneg)

/-- Helper for Chapter01 Theorem 1.4.5: the second derivative of the affine-line restriction of
`f` agrees with the Hessian quadratic form in the chosen direction. -/
lemma iteratedDeriv_two_comp_affineLine_eq
    (f : E → ℝ) (xStar y : E) (hC2 : ContDiffAt ℝ 2 f xStar) :
    iteratedDeriv 2 (fun t : ℝ => f (xStar + t • y)) 0 =
      (iteratedFDeriv ℝ 2 f xStar) ![y, y] := by
  let γ : ℝ → E := fun t => xStar + t • y
  have hC2At : ContDiffAt ℝ 2 f (γ 0) := by
    simpa [γ] using hC2
  have hγC2 : ContDiffAt ℝ 2 γ 0 := by
    -- The affine line is `C²`, so the one-variable chain rule applies.
    simpa [γ] using contDiffAt_const.add (contDiffAt_id.smul_const y)
  have hγDeriv : deriv γ 0 = y := by
    -- The velocity of the affine line at the base point is exactly the direction `y`.
    simpa [γ, one_smul] using (((hasDerivAt_id' (0 : ℝ)).smul_const y).const_add xStar).deriv
  have hγSecond : iteratedDeriv 2 γ 0 = 0 := by
    -- Affine functions have vanishing second derivative.
    have hsmulSecond : iteratedDeriv 2 (fun z : ℝ => z • y) 0 = 0 := by
      simpa [iteratedDeriv_fun_id_zero] using
        (iteratedDeriv_smul_const (n := 2) (x := 0) (f := fun z : ℝ => z)
          (hf := contDiffAt_id) y)
    simpa [γ, iteratedDeriv_const_add] using hsmulSecond
  have hconstVec : (fun _ : Fin 2 => y) = ![y, y] := by
    ext i
    fin_cases i <;> rfl
  -- Apply the second-order chain rule and simplify the affine-line derivatives.
  calc
    iteratedDeriv 2 (fun t : ℝ => f (xStar + t • y)) 0
        = iteratedFDeriv ℝ 2 f (γ 0) (fun _ ↦ deriv γ 0) +
            fderiv ℝ f (γ 0) (iteratedDeriv 2 γ 0) := by
            have hvcomp :
                iteratedDeriv 2 (f ∘ γ) 0 =
                  iteratedFDeriv ℝ 2 f (γ 0) (fun _ ↦ deriv γ 0) +
                    fderiv ℝ f (γ 0) (iteratedDeriv 2 γ 0) :=
              iteratedDeriv_vcomp_two hC2At hγC2
            change iteratedDeriv 2 (f ∘ γ) 0 =
              iteratedFDeriv ℝ 2 f (γ 0) (fun _ ↦ deriv γ 0) +
                fderiv ℝ f (γ 0) (iteratedDeriv 2 γ 0)
            exact hvcomp
    _ = iteratedFDeriv ℝ 2 f xStar (fun _ ↦ y) := by
      rw [hγDeriv, hγSecond]
      simp [γ]
    _ = (iteratedFDeriv ℝ 2 f xStar) ![y, y] := by
      rw [hconstVec]

/-- Chapter01 Theorem 1.4.5 (Second-Order Necessary Condition): on a real normed space, if `f` is
`C²` at a local minimizer `xStar`, then the Hessian quadratic form at `xStar`, expressed as
`(iteratedFDeriv ℝ 2 f xStar) ![y, y]`, is nonnegative in every direction. This is the Fréchet
calculus core behind the textbook open-set statement on `ℝⁿ`. -/
theorem iteratedFDeriv_nonneg_of_isLocalMin
    (f : E → ℝ) (xStar : E) (hC2 : ContDiffAt ℝ 2 f xStar) (hmin : IsLocalMin f xStar)
    (y : E) : 0 ≤ (iteratedFDeriv ℝ 2 f xStar) ![y, y] := by
  have hLineC2 : ContDiffAt ℝ 2 (fun t : ℝ => f (xStar + t • y)) 0 := by
    -- Restricting `f` to a smooth affine line keeps the `C²` regularity at the base point.
    let γ : ℝ → E := fun t => xStar + t • y
    have hC2At : ContDiffAt ℝ 2 f (γ 0) := by
      simpa [γ] using hC2
    have hγC2 : ContDiffAt ℝ 2 γ 0 := by
      simpa [γ] using contDiffAt_const.add (contDiffAt_id.smul_const y)
    have hcomp : ContDiffAt ℝ 2 (f ∘ γ) 0 := hC2At.comp 0 hγC2
    change ContDiffAt ℝ 2 (f ∘ γ) 0
    exact hcomp
  have hLineMin : IsLocalMin (fun t : ℝ => f (xStar + t • y)) 0 :=
    isLocalMin_comp_affineLine f xStar y hmin
  -- Reduce the multivariate statement to the scalar second-order necessary condition.
  have hScalar : 0 ≤ iteratedDeriv 2 (fun t : ℝ => f (xStar + t • y)) 0 :=
    iteratedDeriv_two_nonneg_of_isLocalMin (fun t : ℝ => f (xStar + t • y)) 0 hLineC2 hLineMin
  -- Rewrite the scalar second derivative as the Hessian quadratic form.
  rw [iteratedDeriv_two_comp_affineLine_eq f xStar y hC2] at hScalar
  exact hScalar

/- Chapter01 Theorem 1.4.5 (1) reuses the first-order necessary condition already recorded as
`gradient_eq_zero_of_isLocalMinOn` in Theorem 1.4.4. The extra `ContDiffOn ℝ 2 f D` hypothesis
belongs to the second-order context and is mathematically redundant for this clause, so no new
wrapper theorem is kept here. -/
#check gradient_eq_zero_of_isLocalMinOn

/-- Bridge for Chapter01 Theorem 1.4.5: if `f : D ⊆ ℝⁿ → ℝ` is
twice continuously differentiable on an open set `D` and `xStar` is a local minimizer of `f` on
`D`, then the Hessian at `xStar`, expressed via the quadratic form
`(iteratedFDeriv ℝ 2 f xStar) ![y, y]`, is positive semidefinite. This source-facing open-set
statement is a bridge to `iteratedFDeriv_nonneg_of_isLocalMin`. -/
theorem iteratedFDeriv_nonneg_of_isLocalMinOn_secondOrderNecessary
    (D : Set E) (f : E → ℝ) (xStar : E)
    (hD_open : IsOpen D) (hxStar : xStar ∈ D) (hC2 : ContDiffOn ℝ 2 f D)
    (hmin : IsLocalMinOn f D xStar) (y : E) :
    0 ≤ (iteratedFDeriv ℝ 2 f xStar) ![y, y] := by
  have hD_nhds : D ∈ nhds xStar := hD_open.mem_nhds hxStar
  have hC2At : ContDiffAt ℝ 2 f xStar := hC2.contDiffAt hD_nhds
  have hlocal : IsLocalMin f xStar := hmin.isLocalMin hD_nhds
  exact iteratedFDeriv_nonneg_of_isLocalMin f xStar hC2At hlocal y

end Chapter01Theorem145

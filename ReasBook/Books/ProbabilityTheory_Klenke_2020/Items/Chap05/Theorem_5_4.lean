/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Theorem 5.4: if `X` and `Y` are independent integrable real random variables on a probability
space, then the product `XY` is integrable. This is the canonical theorem
`IndepFun.integrable_mul`. -/
recall IndepFun.integrable_mul

variable {μ : Measure Ω} {X Y : Ω → ℝ}

-- Proof sketch: apply the canonical factorization theorem
-- `IndepFun.integral_mul_eq_mul_integral`; the required strong measurability follows from the
-- integrability hypotheses.
/-- Theorem 5.4: if `X` and `Y` are independent integrable real random variables on a probability
space, then their expectation factors as `𝔼[XY] = 𝔼[X] 𝔼[Y]`. -/
theorem expectation_mul_eq_mul_expectation_of_indepFun
    (hXY : X ⟂ᵢ[μ] Y) (hX : Integrable X μ) (hY : Integrable Y μ) :
    μ[X * Y] = μ[X] * μ[Y] :=
  hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable

-- Proof sketch: `IndepFun.covariance_eq_zero` is the canonical covariance formulation, and
-- `Definition_5_1` packages uncorrelatedness as square-integrability together with vanishing
-- covariance.
/-- Theorem 5.4: in particular, independent square-integrable real random variables are
uncorrelated. -/
theorem isUncorrelated_of_indepFun
    (hXY : X ⟂ᵢ[μ] Y) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    IsUncorrelated X Y μ :=
  ⟨hX, hY, hXY.covariance_eq_zero hX hY⟩

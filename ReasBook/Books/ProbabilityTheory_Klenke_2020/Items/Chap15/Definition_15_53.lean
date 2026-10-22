/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

noncomputable section

/-- Definition 15.53: a random vector `X` with values in `ℝ^ι` is multivariate normally
distributed with expectation `μ` and covariance matrix `C` if `C` is positive definite and `X`
has the canonical multivariate Gaussian law `multivariateGaussian μ C` under `P`. -/
def HasMultivariateNormalLaw {Ω : Type u} [MeasurableSpace Ω] {ι : Type v}
    [Fintype ι] [DecidableEq ι] (X : Ω → EuclideanSpace ℝ ι) (P : Measure Ω)
    (μ : EuclideanSpace ℝ ι) (C : Matrix ι ι ℝ) : Prop :=
  C.PosDef ∧ HasLaw X (multivariateGaussian μ C) P

/-- The canonical multivariate Gaussian measure realizes its own multivariate normal law. -/
theorem hasMultivariateNormalLaw_id {ι : Type v} [Fintype ι] [DecidableEq ι]
    (μ : EuclideanSpace ℝ ι)
    (C : Matrix ι ι ℝ) (hC : C.PosDef) :
    HasMultivariateNormalLaw (fun x : EuclideanSpace ℝ ι ↦ x) (multivariateGaussian μ C) μ C :=
  ⟨hC, HasLaw.id⟩

namespace HasMultivariateNormalLaw

variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v}
variable [Fintype ι] [DecidableEq ι]
variable {X : Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
variable {μ : EuclideanSpace ℝ ι} {C : Matrix ι ι ℝ}

/-- The source-facing positivity requirement in `HasMultivariateNormalLaw`. -/
theorem posDef (hX : HasMultivariateNormalLaw X P μ C) : C.PosDef :=
  hX.1

/-- The canonical owner law stored in `HasMultivariateNormalLaw`. -/
theorem hasLaw (hX : HasMultivariateNormalLaw X P μ C) :
    HasLaw X (multivariateGaussian μ C) P :=
  hX.2

-- Proof sketch: apply `HasLaw.integral_eq` to `hX.hasLaw` and rewrite the resulting expectation
-- of the canonical law by `integral_id_multivariateGaussian`.
/-- A multivariate normal random vector has expectation `μ`. -/
theorem integral_eq_mean (hX : HasMultivariateNormalLaw X P μ C) :
    P[X] = μ := by
  rw [hX.hasLaw.integral_eq, integral_id_multivariateGaussian]

-- Proof sketch: transport covariance along `hX.hasLaw` with `HasLaw.covariance_fun_comp`, then
-- identify the covariance of the canonical law with `covariance_eval_multivariateGaussian
-- hX.posDef.posSemidef`.
/-- The covariance between the `i`-th and `j`-th coordinates of a multivariate normal random
vector is the `(i,j)` entry of its covariance matrix. -/
theorem covariance_eval_eq (hX : HasMultivariateNormalLaw X P μ C) (i j : ι) :
    cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P] = C i j := by
  have hi : AEMeasurable (fun x : EuclideanSpace ℝ ι ↦ x i) (multivariateGaussian μ C) := by
    fun_prop
  have hj : AEMeasurable (fun x : EuclideanSpace ℝ ι ↦ x j) (multivariateGaussian μ C) := by
    fun_prop
  have hcov :
      cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P] =
        cov[fun x : EuclideanSpace ℝ ι ↦ x i, fun x : EuclideanSpace ℝ ι ↦ x j;
          multivariateGaussian μ C] :=
    hX.hasLaw.covariance_fun_comp hi hj
  rw [hcov]
  exact covariance_eval_multivariateGaussian hX.posDef.posSemidef i j

end HasMultivariateNormalLaw

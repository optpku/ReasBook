/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

variable {n : ℕ}

-- Semantic recall: `lean_leansearch` surfaced `Matrix.PosDef` as the canonical owner for the
-- positive-definite matrix condition, and nearby Chapter 4/5/6 precedent records optimization
-- algorithms as explicit sequence data on the concrete `EuclideanSpace ℝ (Fin n)` matrix layer.

/-- The upper bound `ᾱ` for the line-search parameter in the collinear scaling BFGS algorithm. -/
def collinearScalingAlphaUpperBound (δ αMax : ℝ) : ℝ :=
  if δ < 0 then min αMax (-(1 / δ)) else αMax

/-- The step `s_k = -(α_k / (1 + α_k δ_k)) C_k g_k` used by the collinear scaling BFGS
algorithm. -/
def collinearScalingStep
    (α δ : ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  -((α / (1 + α * δ)) • Matrix.toEuclideanLin C g)

/-- The line-search objective `φ(α) = f(x_k - (α / (1 + α δ_k)) C_k g_k)` from the collinear
scaling BFGS algorithm. -/
def collinearScalingLineSearchFunction
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (xk : EuclideanSpace ℝ (Fin n)) (δk : ℝ)
    (Ck : Matrix (Fin n) (Fin n) ℝ) (gk : EuclideanSpace ℝ (Fin n)) : ℝ → ℝ :=
  fun α ↦ f (xk + collinearScalingStep α δk Ck gk)

/-- Evaluating the collinear-scaling line-search objective gives the textbook formula
`f(x_k - (α / (1 + α δ_k)) C_k g_k)`. -/
theorem collinearScalingLineSearchFunction_apply
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (xk : EuclideanSpace ℝ (Fin n)) (δk : ℝ)
    (Ck : Matrix (Fin n) (Fin n) ℝ) (gk : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    collinearScalingLineSearchFunction f xk δk Ck gk α =
      f (xk - (α / (1 + α * δk)) • Matrix.toEuclideanLin Ck gk) := by
  simp [collinearScalingLineSearchFunction, collinearScalingStep, sub_eq_add_neg]

/-- The scalar `ρ_k² = (f_k - f_{k+1})² - (g_{k+1}ᵀ s_k) (g_kᵀ s_k)` appearing in the
collinear scaling BFGS algorithm. -/
def collinearScalingRhoSq
    (fk fkNext : ℝ) (gkNext gk sk : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (fk - fkNext) ^ 2 - dotProduct gkNext sk * dotProduct gk sk

/-- The scalar `γ_k = -(g_kᵀ s_k) / (f_k - f_{k+1} + ρ_k)` from the collinear scaling BFGS
update. -/
def collinearScalingGamma (gk sk : EuclideanSpace ℝ (Fin n)) (fk fkNext ρk : ℝ) : ℝ :=
  -dotProduct gk sk / (fk - fkNext + ρk)

/-- The vector `y_k = γ_k g_{k+1} - g_k / γ_k` used in the collinear scaling BFGS update. -/
def collinearScalingYVector
    (γk : ℝ) (gk gkNext : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  γk • gkNext - γk⁻¹ • gk

/-- The matrix update
`C_{k+1} = γ_k² [((I - s_k y_kᵀ / (s_kᵀ y_k)) C_k (I - y_k s_kᵀ / (s_kᵀ y_k))) +
  s_k s_kᵀ / (s_kᵀ y_k)]`
from the collinear scaling BFGS algorithm. -/
def collinearScalingBFGSMatrixUpdate
    (γk : ℝ) (Ck : Matrix (Fin n) (Fin n) ℝ)
    (sk yk : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  let curvature := dotProduct sk yk
  γk ^ 2 •
    (((1 : Matrix (Fin n) (Fin n) ℝ) - curvature⁻¹ • Matrix.vecMulVec sk yk) * Ck *
        ((1 : Matrix (Fin n) (Fin n) ℝ) - curvature⁻¹ • Matrix.vecMulVec yk sk) +
      curvature⁻¹ • Matrix.vecMulVec sk sk)

/-- The update
`δ_{k+1} = -((1 - γ_k) g_kᵀ C_{k+1} g_{k+1}) / (γ_k g_kᵀ s_k)`
from the collinear scaling BFGS algorithm. -/
def collinearScalingDeltaUpdate
    (γk : ℝ) (gk sk : EuclideanSpace ℝ (Fin n)) (CkNext : Matrix (Fin n) (Fin n) ℝ)
    (gkNext : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -((1 - γk) * dotProduct gk (Matrix.toEuclideanLin CkNext gkNext)) /
    (γk * dotProduct gk sk)

/-- Chapter06 Algorithm 6.2.2: a collinear scaling BFGS algorithm on `ℝ^n` consists of an
objective `f`, an initial positive-definite matrix `C₀`, an initial point `x₀`, an initial
scalar `δ₀ > 0`, a maximum line-search bound `αMax > 0`, and explicit sequences of matrices
`C k`, iterates `x k`, objective values `fVal k`, gradients `g k`, line-search parameters
`α k`, steps `s k`, auxiliary scalars `ρ k` and `γ k`, vectors `y k`, and scaling parameters
`δ k`. The source Step 2 bound `ᾱ` is recorded by
`collinearScalingAlphaUpperBound (δ k) αMax`; the line-search step, iterate update, value and
gradient evaluation, and the formula for `ρ_k²` with `ρ_k > 0` are recorded explicitly; and
Step 4 is recorded by the formulas for `γ_k`, `y_k`, `C_{k+1}`, and `δ_{k+1}` together with the
source inequalities and nonvanishing hypotheses from which the displayed divisions are
well-defined. -/
structure CollinearScalingBFGSAlgorithm
    (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) where
  C0 : Matrix (Fin n) (Fin n) ℝ
  x0 : EuclideanSpace ℝ (Fin n)
  δ0 : ℝ
  αMax : ℝ
  C : ℕ → Matrix (Fin n) (Fin n) ℝ
  x : ℕ → EuclideanSpace ℝ (Fin n)
  fVal : ℕ → ℝ
  g : ℕ → EuclideanSpace ℝ (Fin n)
  α : ℕ → ℝ
  s : ℕ → EuclideanSpace ℝ (Fin n)
  ρ : ℕ → ℝ
  γ : ℕ → ℝ
  y : ℕ → EuclideanSpace ℝ (Fin n)
  δ : ℕ → ℝ
  C0_posDef : C0.PosDef
  δ0_pos : 0 < δ0
  αMax_pos : 0 < αMax
  C_zero : C 0 = C0
  x_zero : x 0 = x0
  δ_zero : δ 0 = δ0
  value_eq : ∀ k : ℕ, fVal k = f (x k)
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  alpha_mem :
    ∀ k : ℕ, α k ∈ Set.Ioo (0 : ℝ) (collinearScalingAlphaUpperBound (δ k) αMax)
  step_eq : ∀ k : ℕ, s k = collinearScalingStep (α k) (δ k) (C k) (g k)
  iterate_eq : ∀ k : ℕ, x (k + 1) = x k + s k
  rho_sq_eq :
    ∀ k : ℕ, ρ k ^ 2 = collinearScalingRhoSq (fVal k) (fVal (k + 1)) (g (k + 1)) (g k) (s k)
  rho_pos : ∀ k : ℕ, 0 < ρ k
  value_strict_decrease : ∀ k : ℕ, fVal (k + 1) < fVal k
  gamma_eq :
    ∀ k : ℕ, γ k = collinearScalingGamma (g k) (s k) (fVal k) (fVal (k + 1)) (ρ k)
  directionalDerivative_ne_zero : ∀ k : ℕ, dotProduct (g k) (s k) ≠ 0
  y_eq : ∀ k : ℕ, y k = collinearScalingYVector (γ k) (g k) (g (k + 1))
  secant_pairing_ne_zero : ∀ k : ℕ, dotProduct (s k) (y k) ≠ 0
  matrix_update_eq :
    ∀ k : ℕ, C (k + 1) = collinearScalingBFGSMatrixUpdate (γ k) (C k) (s k) (y k)
  delta_update_eq :
    ∀ k : ℕ, δ (k + 1) = collinearScalingDeltaUpdate (γ k) (g k) (s k) (C (k + 1)) (g (k + 1))

/-- A collinear scaling BFGS algorithm can be used as its sequence of iterates. -/
instance {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    CoeFun (CollinearScalingBFGSAlgorithm n f) (fun _ ↦ ℕ → EuclideanSpace ℝ (Fin n)) where
  coe A := A.x

namespace CollinearScalingBFGSAlgorithm

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- The Step 2 upper bound `ᾱ_k` attached to the current scaling parameter `δ_k`. -/
def alphaUpperBound (A : CollinearScalingBFGSAlgorithm n f) (k : ℕ) : ℝ :=
  collinearScalingAlphaUpperBound (A.δ k) A.αMax

/-- The Step 2 line-search objective `φ_k(α)` attached to the `k`-th iterate. -/
def lineSearchFunction (A : CollinearScalingBFGSAlgorithm n f) (k : ℕ) : ℝ → ℝ :=
  collinearScalingLineSearchFunction f (A.x k) (A.δ k) (A.C k) (A.g k)

/-- The recorded line-search parameter `α_k` lies in the source interval `(0, ᾱ_k)`. -/
theorem alpha_mem_alphaUpperBound
    (A : CollinearScalingBFGSAlgorithm n f) (k : ℕ) :
    A.α k ∈ Set.Ioo (0 : ℝ) (A.alphaUpperBound k) := by
  simpa [alphaUpperBound] using A.alpha_mem k

/-- The Step 2 interval condition implies that the denominator `1 + α_k δ_k` is positive. -/
theorem lineSearchDenom_pos
    (A : CollinearScalingBFGSAlgorithm n f) (k : ℕ) :
    0 < 1 + A.α k * A.δ k := by
  rcases A.alpha_mem_alphaUpperBound k with ⟨hα_pos, hα_lt⟩
  by_cases hδ : A.δ k < 0
  · have hα_lt_bound : A.α k < -(1 / A.δ k) := by
      exact
        (by
          simpa [alphaUpperBound, collinearScalingAlphaUpperBound, hδ] using hα_lt :
            A.α k < A.αMax ∧ A.α k < -(1 / A.δ k)).2
    have hδ_ne : A.δ k ≠ 0 := by
      linarith
    have hmul : -1 < A.α k * A.δ k := by
      simpa [neg_mul, hδ_ne] using mul_lt_mul_of_neg_right hα_lt_bound hδ
    linarith
  · have hδ_nonneg : 0 ≤ A.δ k := by
      exact le_of_not_gt hδ
    nlinarith

/-- Evaluating the `k`-th line-search objective gives the textbook formula
`f(x_k - (α / (1 + α δ_k)) C_k g_k)`. -/
theorem lineSearchFunction_apply
    (A : CollinearScalingBFGSAlgorithm n f) (k : ℕ) (α : ℝ) :
    A.lineSearchFunction k α =
      f (A.x k - (α / (1 + α * A.δ k)) • Matrix.toEuclideanLin (A.C k) (A.g k)) := by
  simpa [lineSearchFunction] using
    collinearScalingLineSearchFunction_apply f (A.x k) (A.δ k) (A.C k) (A.g k) α

/-- Evaluating `φ_k` at the selected parameter `α_k` gives the next objective value formula. -/
theorem lineSearchFunction_at_alpha
    (A : CollinearScalingBFGSAlgorithm n f) (k : ℕ) :
    A.lineSearchFunction k (A.α k) = f (A.x (k + 1)) := by
  calc
    A.lineSearchFunction k (A.α k)
      = f (A.x k + collinearScalingStep (A.α k) (A.δ k) (A.C k) (A.g k)) := by
          rfl
    _ = f (A.x k + A.s k) := by
          simpa using
            congrArg (fun t : EuclideanSpace ℝ (Fin n) ↦ f (A.x k + t)) (A.step_eq k).symm
    _ = f (A.x (k + 1)) := by
          simpa using congrArg f (A.iterate_eq k).symm

/-- The recorded next objective value is the line-search objective evaluated at `α_k`. -/
theorem fVal_succ_eq_lineSearchFunction
    (A : CollinearScalingBFGSAlgorithm n f) (k : ℕ) :
    A.fVal (k + 1) = A.lineSearchFunction k (A.α k) := by
  calc
    A.fVal (k + 1) = f (A.x (k + 1)) := A.value_eq (k + 1)
    _ = A.lineSearchFunction k (A.α k) := (A.lineSearchFunction_at_alpha k).symm

/-- The Step 4 formula for `γ_k` is nonzero because its numerator and denominator are both
nonzero under the recorded descent assumptions. -/
theorem gamma_ne_zero
    (A : CollinearScalingBFGSAlgorithm n f) (k : ℕ) :
    A.γ k ≠ 0 := by
  have hdenom_pos : 0 < A.fVal k - A.fVal (k + 1) + A.ρ k := by
    linarith [A.value_strict_decrease k, A.rho_pos k]
  rw [A.gamma_eq k, collinearScalingGamma]
  exact div_ne_zero (neg_ne_zero.mpr (A.directionalDerivative_ne_zero k)) (ne_of_gt hdenom_pos)

end CollinearScalingBFGSAlgorithm

end

/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_5_extra_1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul

open Matrix

noncomputable section

variable {n m p q : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "GradientPoint" => EuclideanSpace ℝ (Fin p)
local notation "ResidualPoint" => EuclideanSpace ℝ (Fin q)

-- Sampled owner declarations in the Chapter 10 smooth-penalty domain:
-- * `simpleSmoothExactPenaltyFunction` in `Definition_10_5_extra_1` is the chapter's
--   core/canonical equal-parameter smooth exact penalty owner.
-- * `equalitySmoothExactPenaltyFunction` in `Definition_10_5_extra_1` is the diagonal-penalty
--   generalization upstream.
-- * the present `(10.5.17)` formula is the source-facing extension that adds the extra
--   residual-square term involving `g`, `A`, `M`, `ρ`, and the free multiplier variable `λ`.

/-- Chapter10 Definition 10.5-extra-3: for an equality-constrained problem with objective `f`,
constraint map `c`, gradient-like term `g`, matrix fields `A` and `M`, penalty parameters `σ`
and `ρ`, the smooth exact penalty function is
`(x, λ) ↦ f x - dotProduct (c x) λ + (1 / 2) * σ * ‖c x‖ ^ 2 +
  (1 / 2) * ρ * ‖(M x).mulVec (g x - (A x).mulVec λ)‖ ^ 2`.
The source allows `M x` to be chosen, for example, as `(A x)ᵀ`, a generalized inverse of
`A x`, or the identity matrix. -/
def smoothExactPenaltyFunction
    (f : Point → ℝ)
    (c : Point → ConstraintPoint)
    (g : Point → GradientPoint)
    (A : Point → Matrix (Fin p) (Fin m) ℝ)
    (M : Point → Matrix (Fin q) (Fin p) ℝ)
    (σ ρ : ℝ) (x : Point) (lam : ConstraintPoint) : ℝ :=
  simpleSmoothExactPenaltyFunction f (fun _ ↦ lam) c σ x +
    (1 / 2 : ℝ) * ρ * ‖(M x).mulVec (g x - (A x).mulVec lam)‖ ^ (2 : ℕ)

/-- Evaluating `smoothExactPenaltyFunction` unfolds to the source formula `(10.5.17)`. -/
theorem smoothExactPenaltyFunction_apply
    (f : Point → ℝ)
    (c : Point → ConstraintPoint)
    (g : Point → GradientPoint)
    (A : Point → Matrix (Fin p) (Fin m) ℝ)
    (M : Point → Matrix (Fin q) (Fin p) ℝ)
    (σ ρ : ℝ) (x : Point) (lam : ConstraintPoint) :
    smoothExactPenaltyFunction f c g A M σ ρ x lam =
      f x - dotProduct (c x) lam +
        (1 / 2 : ℝ) * σ * ‖c x‖ ^ (2 : ℕ) +
        (1 / 2 : ℝ) * ρ * ‖(M x).mulVec (g x - (A x).mulVec lam)‖ ^ (2 : ℕ) := by
  simp [smoothExactPenaltyFunction, simpleSmoothExactPenaltyFunction, dotProduct_comm]

#print axioms smoothExactPenaltyFunction

end

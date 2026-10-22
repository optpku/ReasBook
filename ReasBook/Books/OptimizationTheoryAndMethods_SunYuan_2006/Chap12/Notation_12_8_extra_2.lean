/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_1_4

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => LagrangeNewtonPoint n
local notation "Multiplier" => LagrangeNewtonMultiplier m
local notation "ReducedHessian" => Point →L[ℝ] Point

-- Domain-style sampling pass for this item:
-- * primary domain: Chapter 12 SQP / reduced-Hessian stage notation on the operator-valued
--   Jacobian surface.
-- * sampled owner declarations in the minimal semantic closure:
--   - `LagrangeNewtonPoint`
--   - `LagrangeNewtonMultiplier`
--   - `constraintJacobian`
--   - `lagrangeNewtonTrialMultiplier`
-- * best owner abstraction: this file lives at the bridge/view layer. The primitive owners are
--   the ambient Chapter 12 point and multiplier owners `LagrangeNewtonPoint` and
--   `LagrangeNewtonMultiplier`, the reduced-Hessian field `W`, the Chapter 10 Jacobian owner
--   `constraintJacobian`, the Euclidean matrix-action bridge `Matrix.toEuclideanLin`, the
--   gradient owner `gradient`, the constraint map `c`, and the Chapter 12 trial-multiplier
--   owner `lagrangeNewtonTrialMultiplier`.
-- * primitive data vs derived API:
--   - primitive data: `W`, `constraintJacobian c`, `f`, `c`, `xSeq`, `lamSeq`, and
--     `deltaLamSeq`;
--   - derived/source-facing API: the stagewise symbols `W_k`, `A_k`, `g_k`, `c_k`, and `λ̂_k`,
--     obtained by evaluating those owners along the recorded sequences.
-- This file therefore deletes the duplicate local wheel definitions and records the textbook
-- formulas directly on the canonical owners.

-- Source/core/bridge triage:
-- * source-facing items: the displayed stage formulas `W_k`, `A_k`, `g_k`, `c_k`, and `λ̂_k`
-- * core/canonical owners: `gradient`, `constraintJacobian`, `lagrangeNewtonTrialMultiplier`
-- * bridge/view: `Matrix.toEuclideanLin`, sequence evaluation/composition, plus the
--   specialization of `lagrangeNewtonTrialMultiplier` at step size `1`

/- Chapter12 Notation 12.8-extra-2 (1): `W_k = W(x_k, λ_k)` is direct stagewise evaluation of
the reduced-Hessian field `W`. -/
example
    (W : Point → Multiplier → ReducedHessian)
    (xSeq : ℕ → Point) (lamSeq : ℕ → Multiplier) (k : ℕ) :
    (fun j ↦ W (xSeq j) (lamSeq j)) k = W (xSeq k) (lamSeq k) :=
  rfl

/- Chapter12 Notation 12.8-extra-2 (2): `A_k = A(x_k) = ∇ c(x_k)ᵀ` is the direct stagewise
evaluation of the canonical Jacobian owner, viewed as a Euclidean linear map. -/
#check constraintJacobian

example
    (c : Point → Multiplier) (xSeq : ℕ → Point) (k : ℕ) :
    ((fun x ↦ Matrix.toEuclideanLin (constraintJacobian c x)) ∘ xSeq) k =
      Matrix.toEuclideanLin (constraintJacobian c (xSeq k)) :=
  rfl

/- Chapter12 Notation 12.8-extra-2 (3): `g_k = ∇ f(x_k)` is the sequence evaluation of the
canonical gradient owner. -/
#check gradient

example
    (f : Point → ℝ) (xSeq : ℕ → Point) (k : ℕ) :
    ((gradient f) ∘ xSeq) k = gradient f (xSeq k) :=
  rfl

/- Chapter12 Notation 12.8-extra-2 (4): `c_k = c(x_k)` is direct stagewise evaluation of the
constraint map. -/
example
    (c : Point → Multiplier) (xSeq : ℕ → Point) (k : ℕ) :
    (c ∘ xSeq) k = c (xSeq k) :=
  rfl

/- Chapter12 Notation 12.8-extra-2 (5): `λ̂_k = λ_k + (δλ)_k` is the Chapter 12
trial-multiplier owner specialized to the full step `α = 1`. -/
#check lagrangeNewtonTrialMultiplier

example
    (lamSeq deltaLamSeq : ℕ → Multiplier) (k : ℕ) :
    lagrangeNewtonTrialMultiplier (lamSeq k) (deltaLamSeq k) 1 =
      lamSeq k + deltaLamSeq k := by
  simpa using
    (lagrangeNewtonTrialMultiplier_eq (lamSeq k) (deltaLamSeq k) (1 : ℝ))

end

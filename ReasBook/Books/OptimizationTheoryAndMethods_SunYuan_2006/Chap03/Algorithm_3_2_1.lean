/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic

noncomputable section

open scoped Gradient

variable {n : ℕ}

-- Chapter 3 Newton-family owners keep the objective and canonical derivative data explicit.
-- This file keeps the source-facing matrix realization of the Hessian while tying it to `f`
-- through `HasGradientAt` and `HasFDerivAt (∇ f)`.

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Hessian" => Matrix (Fin n) (Fin n) ℝ

/-- Chapter03 Algorithm 3.2.1: Newton's method for minimizing `f : ℝⁿ → ℝ` consists of a
tolerance `ε > 0`, an initial point `x₀`, iterates `x k`, Newton directions `s k`,
explicit gradient data `g k`, and Hessian matrices `G k` satisfying `x 0 = x₀`. At every
index `k`, `g k` is the gradient of `f` at `x k`; at every nonterminal index with
`ε < ‖g k‖`, `G k` is a Hessian matrix of `f` at `x k`, the Newton linear system
`(G k).mulVec (s k) = -g k` is solved, and the next iterate is updated by
`x (k + 1) = x k + s k`. -/
structure NewtonMethod (n : ℕ) (f : Point → ℝ) where
  ε : ℝ
  x0 : Point
  x : ℕ → Point
  s : ℕ → Point
  g : ℕ → Point
  G : ℕ → Hessian
  eps_pos : 0 < ε
  x_zero : x 0 = x0
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  hessian :
    ∀ k : ℕ, ε < ‖g k‖ →
      HasFDerivAt (∇ f)
        (((Matrix.toEuclideanCLM : Hessian ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (G k)))
        (x k)
  linearSystem : ∀ k : ℕ, ε < ‖g k‖ → (G k).mulVec (s k) = -g k
  update : ∀ k : ℕ, ε < ‖g k‖ → x (k + 1) = x k + s k

/-- A Newton method can be used as its sequence of iterates. -/
instance {f : Point → ℝ} : CoeFun (NewtonMethod n f) (fun _ ↦ ℕ → Point) where
  coe A := A.x

/-- Evaluating a Newton method as a function returns its iterate sequence. -/
theorem NewtonMethod.coe_apply {f : Point → ℝ} (A : NewtonMethod n f) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- The explicit gradient data in a Newton method agrees with the canonical gradient of `f`
at every iterate. -/
theorem NewtonMethod.gradient_eq {f : Point → ℝ}
    (A : NewtonMethod n f) (k : ℕ) :
    ∇ f (A.x k) = A.g k :=
  (A.hasGradientAt k).gradient

/-- The stopping condition for a Newton method iterate is `‖g k‖ ≤ ε`. -/
def NewtonMethod.terminatedAt {f : Point → ℝ} (A : NewtonMethod n f) (k : ℕ) : Prop :=
  ‖A.g k‖ ≤ A.ε

/-- `terminatedAt` unfolds to the gradient-norm stopping test from Algorithm 3.2.1. -/
theorem NewtonMethod.terminatedAt_iff {f : Point → ℝ} (A : NewtonMethod n f) (k : ℕ) :
    A.terminatedAt k ↔ ‖A.g k‖ ≤ A.ε :=
  Iff.rfl

/-- At every nonterminal stage, Algorithm 3.2.1 records the Hessian of `f`, solves the
Newton linear system, and updates the iterate by the Newton direction. -/
theorem NewtonMethod.step {f : Point → ℝ}
    (A : NewtonMethod n f) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    HasFDerivAt (∇ f)
      (((Matrix.toEuclideanCLM : Hessian ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (A.G k)))
      (A.x k) ∧
      (A.G k).mulVec (A.s k) = -A.g k ∧
      A.x (k + 1) = A.x k + A.s k :=
  ⟨A.hessian k hNotStopped, A.linearSystem k hNotStopped, A.update k hNotStopped⟩

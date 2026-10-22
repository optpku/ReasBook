/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

variable {n : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall: `lean_leansearch` surfaced the canonical minimizer owner `IsMinOn`,
-- and nearby repository precedent for optimization algorithms records one concrete run
-- through explicit iterate, gradient, direction, and step-size sequences.

/-- Chapter02 Algorithm 2.2.1: a general exact-line-search method for unconstrained
optimization in `ℝ^n` starts from `x0`, uses a tolerance `ε ≥ 0`, computes a descent
direction `d k` from the current gradient data `g k`, chooses `α k` so that
`a ↦ f (x k + a • d k)` attains its minimum on `Set.Ici 0` at `α k`, and updates by
`x (k + 1) = x k + α k • d k`. The textbook stopping test after the `k`-th update is
`‖g (k + 1)‖ ≤ ε`, where `g k` is a gradient of `f` at `x k`. -/
structure GeneralUnconstrainedOptimizationMethod (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) where
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin n)
  x : ℕ → EuclideanSpace ℝ (Fin n)
  g : ℕ → EuclideanSpace ℝ (Fin n)
  d : ℕ → EuclideanSpace ℝ (Fin n)
  α : ℕ → ℝ
  epsilon_nonneg : 0 ≤ ε
  x_zero : x 0 = x0
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  descentDirection : ∀ k : ℕ, inner ℝ (g k) (d k) < 0
  exactLineSearch :
    ∀ k : ℕ, IsMinOn (fun a : ℝ ↦ f (x k + a • d k)) (Set.Ici 0) (α k)
  update : ∀ k : ℕ, x (k + 1) = x k + α k • d k

/-- A general unconstrained optimization method can be used as its iterate sequence `x`. -/
instance : CoeFun (GeneralUnconstrainedOptimizationMethod n f) (fun _ ↦ ℕ → Point) where
  coe A := A.x

namespace GeneralUnconstrainedOptimizationMethod

/-- Evaluating a general exact-line-search method as a function returns its iterate sequence. -/
theorem coe_apply (A : GeneralUnconstrainedOptimizationMethod n f) (k : ℕ) :
    A k = A.x k := by
  -- The `CoeFun` instance is defined by the iterate sequence `x`.
  rfl

/-- The explicit gradient data in a general exact-line-search method agrees with the canonical
gradient of `f` at every iterate. -/
theorem gradient_eq (A : GeneralUnconstrainedOptimizationMethod n f) (k : ℕ) :
    gradient f (A k) = A.g k := by
  -- Route correction: use the stored `HasGradientAt` witness instead of unfolding `gradient`.
  simpa using (A.hasGradientAt k).gradient

/-- The stopping condition of Chapter02 Algorithm 2.2.1 checked after the `k`-th update. -/
def terminatedAfter (A : GeneralUnconstrainedOptimizationMethod n f) (k : ℕ) : Prop :=
  ‖A.g (k + 1)‖ ≤ A.ε

/-- Unfolding `terminatedAfter` gives the gradient-norm stopping test at the fresh iterate
`x (k + 1)`. -/
theorem terminatedAfter_iff (A : GeneralUnconstrainedOptimizationMethod n f) (k : ℕ) :
    A.terminatedAfter k ↔ ‖gradient f (A (k + 1))‖ ≤ A.ε := by
  -- Unfold the stopping predicate and rewrite the recorded next gradient canonically.
  simp [terminatedAfter, A.gradient_eq (k + 1)]

/-- A step of `GeneralUnconstrainedOptimizationMethod` consists of a descent direction,
an exact line-search minimizer on `Set.Ici 0`, and the standard iterate update. -/
theorem stepSpec (A : GeneralUnconstrainedOptimizationMethod n f) (k : ℕ) :
    inner ℝ (A.g k) (A.d k) < 0 ∧
      IsMinOn (fun a : ℝ ↦ f (A k + a • A.d k)) (Set.Ici 0) (A.α k) ∧
      A (k + 1) = A k + A.α k • A.d k := by
  -- Package the three stagewise algorithm clauses from the structure fields.
  refine ⟨A.descentDirection k, ?_, ?_⟩
  · -- Normalize the public function view `A k` back to the stored iterate sequence.
    simpa [A.coe_apply] using A.exactLineSearch k
  · -- The update field already states the iterate recurrence in the public notation.
    simpa [A.coe_apply] using A.update k

end GeneralUnconstrainedOptimizationMethod

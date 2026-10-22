/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3

-- Domain sampling:
-- * source-facing owner: `IsDescentDirectionAt` from Chapter 1 Definition 1.4.3;
-- * derived API there: `IsDescentDirectionAt.inner_gradient_neg`,
--   `IsDescentDirectionAt.differentiableAt`;
-- * mathlib gradient bridge: `DifferentiableAt.hasGradientAt`.
-- This algorithm remains source-facing, but its Step-2 descent-direction clause should
-- reuse that Chapter 1 owner instead of restating the raw inequality.

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Chapter01 Algorithm 1.5.1: a basic descent method for `f : E → ℝ` consists of a positive
tolerance `ε`, an initial point `x₀`, iterates `x k`, descent directions `d k`, and step sizes
`α k` such that `x 0 = x₀`. The source text is written on `ℝ^n`, but the data only use the real
complete inner-product-space layer already underlying `IsDescentDirectionAt`. At every
nonterminal index with `ε < ‖gradient f (x k)‖`, the method uses a descent direction, chooses a
positive step size, strictly decreases the objective value, and updates by
`x (k + 1) = x k + α k • d k`. -/
structure BasicDescentMethod (f : E → ℝ) where
  ε : ℝ
  x0 : E
  x : ℕ → E
  d : ℕ → E
  α : ℕ → ℝ
  epsilon_pos : 0 < ε
  x_zero : x 0 = x0
  differentiableAt : ∀ k : ℕ, DifferentiableAt ℝ f (x k)
  descentDirection :
    ∀ k : ℕ, ε < ‖gradient f (x k)‖ → IsDescentDirectionAt f (x k) (d k)
  stepSize_pos :
    ∀ k : ℕ, ε < ‖gradient f (x k)‖ → 0 < α k
  objectiveDecrease :
    ∀ k : ℕ, ε < ‖gradient f (x k)‖ → f (x k + α k • d k) < f (x k)
  update :
    ∀ k : ℕ, ε < ‖gradient f (x k)‖ → x (k + 1) = x k + α k • d k

/-- A basic descent method can be used as its iterate sequence `x`. -/
instance {f : E → ℝ} : CoeFun (BasicDescentMethod f) (fun _ ↦ ℕ → E) where
  coe A := A.x

/-- Evaluating a basic descent method as a function returns its iterate sequence. -/
theorem BasicDescentMethod.coe_apply {f : E → ℝ} (A : BasicDescentMethod f) (k : ℕ) :
    A k = A.x k := rfl

/-- The method hypothesis that `f` is differentiable at each iterate yields the canonical
gradient statement used by the textbook descent inequalities. -/
theorem BasicDescentMethod.hasGradientAt {f : E → ℝ} (A : BasicDescentMethod f) (k : ℕ) :
    HasGradientAt f (gradient f (A k)) (A k) :=
  (A.differentiableAt k).hasGradientAt

/-- The stopping test in Chapter01 Algorithm 1.5.1 checks whether
`‖gradient f (x k)‖ ≤ ε`. -/
def BasicDescentMethod.terminatedAt {f : E → ℝ} (A : BasicDescentMethod f) (k : ℕ) : Prop :=
  ‖gradient f (A k)‖ ≤ A.ε

/-- The predicate `terminatedAt` is exactly the gradient-norm stopping criterion from the
basic scheme. -/
theorem BasicDescentMethod.terminatedAt_iff {f : E → ℝ} (A : BasicDescentMethod f) (k : ℕ) :
    A.terminatedAt k ↔ ‖gradient f (A k)‖ ≤ A.ε := Iff.rfl

/-- At every nonterminal index, the basic descent scheme uses a descent direction, chooses a
positive step size, strictly decreases the objective function, and updates by
`x (k + 1) = x k + α k • d k`. -/
theorem BasicDescentMethod.step {f : E → ℝ}
    (A : BasicDescentMethod f) {k : ℕ} (hNotStopped : A.ε < ‖gradient f (A k)‖) :
    IsDescentDirectionAt f (A k) (A.d k) ∧
      0 < A.α k ∧
      f (A k + A.α k • A.d k) < f (A k) ∧
      A (k + 1) = A k + A.α k • A.d k :=
  ⟨A.descentDirection k hNotStopped, A.stepSize_pos k hNotStopped,
    A.objectiveDecrease k hNotStopped, A.update k hNotStopped⟩

/-- The Step-2 descent-direction clause implies the textbook strict negativity inequality. -/
theorem BasicDescentMethod.step_inner_gradient_neg {f : E → ℝ}
    (A : BasicDescentMethod f) {k : ℕ} (hNotStopped : A.ε < ‖gradient f (A k)‖) :
    inner ℝ (gradient f (A k)) (A.d k) < 0 :=
  (A.step hNotStopped).1.inner_gradient_neg

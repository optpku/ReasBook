/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_1_extra_1

universe u

-- Domain sampling for this file:
-- * Chapter 2 already owns the genuine line-search notion `IsLineSearchStep`
-- * Chapter 3 already owns the canonical steepest-descent direction and update through
--   `steepestDescentDirection` and `steepestDescentStep`
-- * `Algorithm_3_1_1.lean` already places the Chapter 3 steepest-descent method on the
--   canonical real-Hilbert-space owner layer, so this file should reuse that ambient level
-- * the source-facing primitive data here are the iterate, gradient, and step-size sequences;
--   the search direction is derived from the chapter owner `steepestDescentDirection`, while the
--   later Barzilai-Borwein steplength rule is recorded by the two textbook quotient predicates
--   with their admissible denominator conditions

section StepSize

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Formula `(3.1.29)` with its source-faithful nonzero-denominator side condition. -/
def IsBarzilaiBorweinStepSize29 (xk xkm1 gk gkm1 : E) (αk : ℝ) : Prop :=
  inner ℝ (xk - xkm1) (gk - gkm1) ≠ 0 ∧
    αk =
      inner ℝ (xk - xkm1) (xk - xkm1) /
        inner ℝ (xk - xkm1) (gk - gkm1)

/-- Formula `(3.1.30)` with its source-faithful nonzero-denominator side condition. -/
def IsBarzilaiBorweinStepSize30 (xk xkm1 gk gkm1 : E) (αk : ℝ) : Prop :=
  inner ℝ (gk - gkm1) (gk - gkm1) ≠ 0 ∧
    αk =
      inner ℝ (xk - xkm1) (gk - gkm1) /
        inner ℝ (gk - gkm1) (gk - gkm1)

/-- A later Barzilai-Borwein step size is given by formula `(3.1.29)` or formula `(3.1.30)`,
with the corresponding denominator condition recorded explicitly. -/
def IsBarzilaiBorweinStepSize (xk xkm1 gk gkm1 : E) (αk : ℝ) : Prop :=
  IsBarzilaiBorweinStepSize29 xk xkm1 gk gkm1 αk ∨
    IsBarzilaiBorweinStepSize30 xk xkm1 gk gkm1 αk

end StepSize

section Method

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Chapter03 Algorithm 3.1.8: a Barzilai-Borwein gradient-method run for `f` on a real
Hilbert space starts from `x0`, stops when `‖g k‖ ≤ ε`, uses a genuine line-search step at the first
nonterminal stage along the steepest-descent direction, and thereafter uses formula `(3.1.29)`
or `(3.1.30)` for the step size while updating by the canonical steepest-descent step. -/
structure BarzilaiBorweinGradientMethod (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  f : E → ℝ
  x0 : E
  ε : ℝ
  x : ℕ → E
  g : ℕ → E
  α : ℕ → ℝ
  x_zero : x 0 = x0
  epsilon_pos : 0 < ε
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  initialLineSearch :
    ε < ‖g 0‖ →
      IsLineSearchStep f (x 0) (steepestDescentDirection f (x 0)) (α 0)
  initialUpdate :
    ε < ‖g 0‖ →
      x 1 = steepestDescentStep f (x 0) (α 0)
  laterStepSize :
    ∀ k : ℕ, ε < ‖g (k + 1)‖ →
      IsBarzilaiBorweinStepSize (x (k + 1)) (x k) (g (k + 1)) (g k) (α (k + 1))
  laterUpdate :
    ∀ k : ℕ, ε < ‖g (k + 1)‖ →
      x (k + 2) = steepestDescentStep f (x (k + 1)) (α (k + 1))

namespace BarzilaiBorweinGradientMethod

/-- A Barzilai-Borwein gradient-method run coerces to its iterate sequence `k ↦ x_k`. -/
instance : CoeFun (BarzilaiBorweinGradientMethod E) (fun _ ↦ ℕ → E) where
  coe run := run.x

/-- Evaluating a Barzilai-Borwein gradient-method run as a function returns its iterate
sequence. -/
theorem coe_apply (run : BarzilaiBorweinGradientMethod E) (k : ℕ) :
    run k = run.x k := rfl

/-- The explicit gradient data in a Barzilai-Borwein run agree with the canonical gradient. -/
theorem gradient_eq (run : BarzilaiBorweinGradientMethod E) (k : ℕ) :
    gradient run.f (run.x k) = run.g k :=
  (run.hasGradientAt k).gradient

/-- The first nonterminal step uses the canonical steepest-descent direction together with a
genuine line-search step. -/
theorem initialStep
    (run : BarzilaiBorweinGradientMethod E) (hNotStopped : run.ε < ‖run.g 0‖) :
    IsLineSearchStep run.f (run.x 0) (steepestDescentDirection run.f (run.x 0)) (run.α 0) ∧
      run.x 1 = steepestDescentStep run.f (run.x 0) (run.α 0) :=
  ⟨run.initialLineSearch hNotStopped, run.initialUpdate hNotStopped⟩

/-- Every later nonterminal step uses the Barzilai-Borwein step-size rule and the canonical
steepest-descent update formula. -/
theorem laterStep
    (run : BarzilaiBorweinGradientMethod E) (k : ℕ) (hNotStopped : run.ε < ‖run.g (k + 1)‖) :
    IsBarzilaiBorweinStepSize (run.x (k + 1)) (run.x k) (run.g (k + 1)) (run.g k)
        (run.α (k + 1)) ∧
      run.x (k + 2) = steepestDescentStep run.f (run.x (k + 1)) (run.α (k + 1)) :=
  ⟨run.laterStepSize k hNotStopped, run.laterUpdate k hNotStopped⟩

end BarzilaiBorweinGradientMethod

end Method

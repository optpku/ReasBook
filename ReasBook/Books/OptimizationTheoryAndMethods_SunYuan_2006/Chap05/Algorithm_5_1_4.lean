/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

-- Source/core/bridge triage for this file:
-- * source-facing owner kept here: `DfpMethod`, the DFP specialization of Algorithm 5.1.1.
-- * core/canonical owner reused here: `GeneralQuasiNewtonMethod`.
-- * bridge/view API kept here: the concrete Euclidean matrix representative `A.matrix`.
--
-- Primitive data for the DFP specialization is only the initial matrix positivity, the two
-- denominator side conditions, and the DFP matrix update. The iterate, gradient, search
-- direction, step-size, stopping rule, and secant equation are already owned upstream by
-- `GeneralQuasiNewtonMethod`.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

variable {f : Point → ℝ}

/-- The DFP inverse-Hessian update attached to a current matrix `H` and secant data `s y`. -/
def dfpInverseUpdate (H : MatrixN) (s y : Point) : MatrixN :=
  H + (dotProduct s y)⁻¹ • Matrix.vecMulVec s s -
    (dotProduct y (H.mulVec y))⁻¹ • Matrix.vecMulVec (H.mulVec y) (H.mulVec y)

/-- Chapter05 Algorithm 5.1.4: a DFP method on `ℝ^n` is a general quasi-Newton run whose
initial Euclidean matrix representative is positive definite and whose nonterminal stages satisfy
the two denominator conditions required by the DFP inverse update together with the textbook DFP
matrix recursion on `A.matrix`. The iterate, search-direction, step-size, stopping, and secant
equation data are inherited from `GeneralQuasiNewtonMethod`. -/
structure DfpMethod (f : Point → ℝ) extends GeneralQuasiNewtonMethod f where
  matrix0_posDef : (Matrix.toEuclideanLin.symm (H 0)).PosDef
  secant_denom_ne_zero (k : ℕ) (_ : ε < ‖g k‖) :
    dotProduct (x (k + 1) - x k) (g (k + 1) - g k) ≠ 0
  metric_denom_ne_zero (k : ℕ) (_ : ε < ‖g k‖) :
    dotProduct (g (k + 1) - g k)
      ((Matrix.toEuclideanLin.symm (H k)).mulVec (g (k + 1) - g k)) ≠ 0
  update_eq (k : ℕ) (_ : ε < ‖g k‖) :
    Matrix.toEuclideanLin.symm (H (k + 1)) =
      dfpInverseUpdate
        (Matrix.toEuclideanLin.symm (H k)) (x (k + 1) - x k) (g (k + 1) - g k)

namespace DfpMethod

/-- A DFP method can be used as its iterate sequence `x`. -/
instance instCoeFunForallNat
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    CoeFun (DfpMethod f) (fun _ ↦ ℕ → EuclideanSpace ℝ (Fin n)) where
  coe A := A.toGeneralQuasiNewtonMethod

/-- Evaluating a DFP method as a function returns its iterate sequence. -/
theorem coe_apply
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : DfpMethod f) (k : ℕ) :
    A k = A.x k := rfl

/-- The initial DFP inverse-Hessian approximation is symmetric because it is positive definite. -/
theorem matrix0_isSymm
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : DfpMethod f) :
    A.matrix0.IsSymm :=
  A.matrix0_posDef.isHermitian

/-- The DFP update formula on `A.matrix` is available directly from the source-facing owner. -/
theorem matrix_update_eq
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : DfpMethod f) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    A.matrix (k + 1) =
      dfpInverseUpdate (A.matrix k) (A (k + 1) - A k) (A.g (k + 1) - A.g k) :=
  A.update_eq k hNotStopped

/-- A DFP method is generated through stage `k` when the underlying quasi-Newton run is
generated through stage `k` and each earlier secant pair satisfies the Chapter 5 curvature
condition. This is the source-facing stage predicate for Algorithm 5.1.4. -/
structure GeneratedThrough
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : DfpMethod f) (k : ℕ) : Prop where
  run : A.toGeneralQuasiNewtonMethod.GeneratedThrough k
  curvatureCondition :
    ∀ i : ℕ, i < k →
      satisfiesCurvatureCondition (A (i + 1) - A i) (A.g (i + 1) - A.g i)

namespace GeneratedThrough

/-- Unfolding `A.GeneratedThrough k` gives the underlying generated-stage predicate together
with the stagewise DFP curvature condition through stage `k - 1`. -/
theorem iff
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : DfpMethod f} {k : ℕ} :
    A.GeneratedThrough k ↔
      A.toGeneralQuasiNewtonMethod.GeneratedThrough k ∧
        (∀ i : ℕ, i < k →
          satisfiesCurvatureCondition (A (i + 1) - A i) (A.g (i + 1) - A.g i)) := by
  constructor
  · intro h
    exact ⟨h.run, h.curvatureCondition⟩
  · rintro ⟨hRun, hCurvature⟩
    exact ⟨hRun, hCurvature⟩

/-- A DFP run generated through stage `k` is also generated through every earlier stage `m ≤ k`. -/
theorem of_le
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : DfpMethod f} {m k : ℕ}
    (h : A.GeneratedThrough k) (hmk : m ≤ k) :
    A.GeneratedThrough m := by
  refine ⟨?_, ?_⟩
  · intro i hi
    exact h.run i (Nat.lt_of_lt_of_le hi hmk)
  · intro i hi
    exact h.curvatureCondition i (Nat.lt_of_lt_of_le hi hmk)

/-- Every generated DFP stage `i < k` is nonterminal. -/
theorem notStopped
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : DfpMethod f} {k i : ℕ}
    (h : A.GeneratedThrough k) (hi : i < k) :
    A.ε < ‖A.g i‖ :=
  h.run i hi

/-- Every generated DFP stage `i < k` satisfies the secant-curvature condition. -/
theorem curvature
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : DfpMethod f} {k i : ℕ}
    (h : A.GeneratedThrough k) (hi : i < k) :
    satisfiesCurvatureCondition (A (i + 1) - A i) (A.g (i + 1) - A.g i) :=
  h.curvatureCondition i hi

/-- The current stage of a DFP run generated through `k + 1` is nonterminal and satisfies the
curvature condition. -/
theorem stepSpec
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : DfpMethod f} {k : ℕ}
    (h : A.GeneratedThrough (k + 1)) :
    A.ε < ‖A.g k‖ ∧
      satisfiesCurvatureCondition (A (k + 1) - A k) (A.g (k + 1) - A.g k) :=
  ⟨h.notStopped (Nat.lt_succ_self k), h.curvature (Nat.lt_succ_self k)⟩

end GeneratedThrough

/-- At every nonterminal stage, a DFP method uses the source secant data `s k = α k • d k`,
updates the iterate by `x (k + 1) = x k + α k • d k`, records the gradient difference
`g (k + 1) - g k`, and applies the DFP inverse-Hessian formula to `A.matrix` under the two
nonzero denominator conditions required by that update. -/
theorem stepSpec
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (A : DfpMethod f) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    A.d k = -(A.H k (A.g k)) ∧
      0 < A.α k ∧
      A (k + 1) = A k + A.α k • A.d k ∧
      satisfiesQuasiNewtonEquation (A.H (k + 1)) (A.g (k + 1) - A.g k) (A (k + 1) - A k) ∧
      dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k) ≠ 0 ∧
      dotProduct (A.g (k + 1) - A.g k)
        ((A.matrix k).mulVec (A.g (k + 1) - A.g k)) ≠ 0 ∧
      A.matrix (k + 1) =
        dfpInverseUpdate (A.matrix k) (A (k + 1) - A k) (A.g (k + 1) - A.g k) :=
  let ⟨hd, hα, hx, hQN⟩ := A.toGeneralQuasiNewtonMethod.stepSpec hNotStopped
  ⟨hd, hα, hx, hQN, A.secant_denom_ne_zero k hNotStopped,
    A.metric_denom_ne_zero k hNotStopped, A.matrix_update_eq hNotStopped⟩

end DfpMethod

end

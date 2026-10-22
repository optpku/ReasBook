/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.SR1Update
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

-- Domain sampling for this file:
-- * primary domain: SR1 quasi-Newton runs on Euclidean quadratic objectives;
-- * sampled owner declarations in the minimal closure:
--   `GeneralQuasiNewtonMethod`,
--   `GeneralQuasiNewtonMethod.GeneratedThrough`,
--   `quadraticObjective`,
--   `sr1Update`;
-- * best owner abstraction: the primitive SR1 recursion belongs to the run owner
--   `GeneralQuasiNewtonMethod`, while positive definiteness of the quadratic Hessian `G`
--   belongs to the source theorem hypotheses rather than to the SR1 recursion data itself;
-- * primitive data kept here: zero tolerance, nonvanishing SR1 denominator, and SR1 update law;
-- * derived API kept here: `IsSR1Run.stepSpec` and the quadratic terminal-matrix theorem.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

namespace GeneralQuasiNewtonMethod

section SR1Run

variable {f : Point → ℝ}

/-- An SR1 run is a general quasi-Newton run with zero stopping tolerance and, at each
nonterminal stage, the SR1 inverse-Hessian update applied to the generated step/secant data
`x (k + 1) - x k` and `g (k + 1) - g k` on the Euclidean matrix model `A.matrix`. -/
structure IsSR1Run (A : GeneralQuasiNewtonMethod f) : Prop where
  epsilon_eq_zero : A.ε = 0
  denominator_ne_zero (k : ℕ) (_ : A.ε < ‖A.g k‖) :
    dotProduct
        (sr1Residual (A.matrix k) (broydenSecant A.g k) (broydenStep A k))
        (broydenSecant A.g k) ≠ 0
  sr1_update (k : ℕ) (_ : A.ε < ‖A.g k‖) :
    A.matrix (k + 1) = sr1Update (A.matrix k) (broydenStep A k) (broydenSecant A.g k)

namespace IsSR1Run

/-- Every nonterminal SR1 stage has the generated secant data, a nonvanishing SR1 denominator,
and the explicit SR1 inverse-Hessian update formula. -/
theorem stepSpec
    {A : GeneralQuasiNewtonMethod f}
    (hSR1 : A.IsSR1Run) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    dotProduct
        (sr1Residual (A.matrix k) (broydenSecant A.g k) (broydenStep A k))
        (broydenSecant A.g k) ≠ 0 ∧
      A.matrix (k + 1) = sr1Update (A.matrix k) (broydenStep A k) (broydenSecant A.g k) := by
  exact ⟨hSR1.denominator_ne_zero k hNotStopped, hSR1.sr1_update k hNotStopped⟩

end IsSR1Run

attribute [simp] GeneralQuasiNewtonMethod.IsSR1Run.epsilon_eq_zero

/-- The predicate `IsSR1Run` is proof-irrelevant. -/
instance isSR1Run_subsingleton
    {A : GeneralQuasiNewtonMethod f} :
    Subsingleton A.IsSR1Run := inferInstance

end SR1Run

end GeneralQuasiNewtonMethod

variable {G : MatrixN} {b : Point} {c : ℝ}

local notation "f" => quadraticObjective G b c

/-- Chapter05 Theorem 5.1.2: if `G` is the positive-definite Hessian of a quadratic objective,
`A` is an SR1 run for `quadraticObjective G b c`, the run is generated through stage `n`, and
the generated step vectors `broydenStep A k` for `k = 0, ..., n - 1` are linearly independent,
then the SR1 method terminates after `n + 1` steps, formalized here as `A.matrix n = G⁻¹`. -/
theorem sr1TerminalMatrix_eq_inv_of_linearIndependent_steps
    (A : GeneralQuasiNewtonMethod f)
    (hSR1 : A.IsSR1Run)
    (hPosDef : G.PosDef)
    (hGenerated : A.GeneratedThrough n)
    (hstep : LinearIndependent ℝ (fun k : Fin n ↦ broydenStep A k)) :
    A.matrix n = G⁻¹ := sorry
end

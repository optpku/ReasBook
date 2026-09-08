module

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Matrix.Order
import ReasLib.Analysis.StandardQuadratic

open scoped Distributions Matrix.Norms.L2Operator MatrixOrder

section

variable (n : ℕ)
variable (x : EuclideanSpace ℝ (Fin n)) (r : ℝ)
variable (f : EuclideanSpace ℝ (Fin n) → ℝ)
variable (A B : Matrix (Fin n) (Fin n) ℝ)

/- Notation 1.1 (1): the standard quadratic on `ℝⁿ`. -/
#check (standardQuadratic : EuclideanSpace ℝ (Fin n) → ℝ)

/- Notation 1.1 (2): the Euclidean norm and induced matrix operator norm. -/
#check (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖)
#check Matrix.l2_opNorm_def

/- Notation 1.1 (3): the `n × n` identity matrix. -/
#check (1 : Matrix (Fin n) (Fin n) ℝ)

/- Notation 1.1 (4): open Euclidean balls and their closures. -/
#check Metric.ball x r
#check closure (Metric.ball x r)
#check (closure_ball x : r ≠ 0 → closure (Metric.ball x r) = Metric.closedBall x r)

/- Notation 1.1 (5): the topological support of a function. -/
#check tsupport f

/- Notation 1.1 (6): smooth compactly supported functions. -/
#check (𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))), ℝ))
#check (ContDiff ℝ ⊤ f)
#check HasCompactSupport f

/- Notation 1.1 (7): the Loewner order on matrices. -/
#check (Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef)

end

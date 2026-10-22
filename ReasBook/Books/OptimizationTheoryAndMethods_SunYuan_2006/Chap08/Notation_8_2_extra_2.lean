/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_1

-- Domain sampling:
-- * primary domain: constrained optimization with Lagrange multipliers
-- * primitive owner data: `ConstrainedOptimizationProblem` from
--   `Chapter01.Definition_1_1_extra_1`, reused through the Chapter 8 owner file
--   `Definition_8_1_1`
-- * inspected owner declarations in this domain:
--   `ConstrainedOptimizationProblem.lagrangian` from `Definition_8_1_1`
--   `ConstrainedOptimizationProblem.lagrangian_eq` from `Definition_8_1_1`
--   `ConstrainedOptimizationProblem.feasibleSet` from `Chapter01.Definition_1_1_extra_1`
--   `ConstrainedOptimizationProblem.eqIndices` from `Definition_8_1_1`
--   `ConstrainedOptimizationProblem.activeConstraintIndexSet` from `Definition_8_1_1`
-- * core/canonical owner reused directly:
--   `ConstrainedOptimizationProblem.lagrangian` from `Definition_8_1_1`
-- * layer targeted here: `bridge/view`, namely the textbook notation
--   `𝓛[problem](x, lam)` for the canonical owner call `problem.lagrangian x lam`
-- * primitive data vs. derived API:
--   the constrained problem data and the Chapter 8 Lagrangian owner remain primitive upstream;
--   this file contributes only the derived notation bridge

/-- Textbook notation for the Chapter 8 Lagrangian of `problem` at `(x, lam)`. -/
notation:max "𝓛[" problem "](" x ", " lam ")" =>
  ConstrainedOptimizationProblem.lagrangian problem x lam

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

/-- Chapter08 Notation 8.2-extra-2: the textbook notation `𝓛[problem](x, lam)` unfolds to the
canonical Chapter 8 Lagrangian owner call `problem.lagrangian x lam`. -/
theorem lagrangian_notation_eq
    (problem : _root_.ConstrainedOptimizationProblem n m E I)
    (x : Point) (lam : Fin m → ℝ) :
    𝓛[problem](x, lam) = problem.lagrangian x lam := by
  -- The notation is defined as the canonical owner application, so it unfolds directly.
  rfl

end ConstrainedOptimizationProblem

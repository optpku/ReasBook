/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_2_1

-- Domain sampling pass:
-- * primary domain: finite-dimensional quasi-Newton / inverse-Hessian Broyden-class methods on
--   quadratic objectives
-- * relevant chapter owners inspected:
--   `GeneralQuasiNewtonMethod`
--   `GeneralQuasiNewtonMethod.IsBroydenClassMethod`
--   `GeneralQuasiNewtonMethod.broydenClassMethod_hereditary`
--   `GeneralQuasiNewtonMethod.broydenClassMethod_conjugateDirections`
--   `GeneralQuasiNewtonMethod.broydenClassMethod_finalInverse`
-- * owner abstraction: `GeneralQuasiNewtonMethod.IsBroydenClassMethod` over the run data
--   owner `GeneralQuasiNewtonMethod`
-- * source/core/bridge triage:
--   source-facing: this exercise is a recall-only reference to the Chapter 5 Broyden-class
--     termination theorem package
--   core/canonical: `Theorem_5_2_1` and its owner chain
--   bridge/view: none
-- * primitive data: the explicit quasi-Newton run data in `GeneralQuasiNewtonMethod`
-- * derived API: the Broyden-class predicate and the five finite-termination conclusions already
--   owned by `Theorem_5_2_1`
--
-- This exercise asks for a proof of Theorem 5.2.1, so the canonical Chapter 5 file already owns
-- the mathematical content. This file therefore reuses the source-facing owner
-- `GeneralQuasiNewtonMethod.IsBroydenClassMethod` and the five canonical theorem owners
-- directly, instead of reconstructing their proposition types locally.

/-
Chapter05 Exercise 5.6

Recall-only entry: the requested exercise content is already formalized canonically in
`Theorem_5_2_1.lean`.
-/
section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

variable {G : MatrixN} {b : Point} {c : ℝ}

local notation "f" => quadraticObjective G b c

variable (A : GeneralQuasiNewtonMethod f) (φ : ℕ → ℝ)

#check A.IsBroydenClassMethod φ
#check A.broydenClassMethod_hereditary
#check A.broydenClassMethod_conjugateDirections
#check A.broydenClassMethod_quadraticTermination
#check A.broydenClassMethod_terminationBound
#check A.broydenClassMethod_finalInverse

end

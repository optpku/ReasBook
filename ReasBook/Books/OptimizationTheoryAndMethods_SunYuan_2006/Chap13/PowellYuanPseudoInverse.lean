/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

section

variable {m n : ℕ}

local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ
local notation "PseudoInverseMatrix" => Matrix (Fin m) (Fin n) ℝ

/-- `PowellYuanIsPseudoInverseOf AkPlus Ak` records that `AkPlus` is the source Moore-Penrose
pseudoinverse `A_k⁺` of the Powell-Yuan stage Jacobian `A_k`. -/
def PowellYuanIsPseudoInverseOf
    (AkPlus : PseudoInverseMatrix)
    (Ak : Jacobian) : Prop :=
  Ak * AkPlus * Ak = Ak ∧
    AkPlus * Ak * AkPlus = AkPlus ∧
    (Ak * AkPlus).transpose = Ak * AkPlus ∧
    (AkPlus * Ak).transpose = AkPlus * Ak

/-- Unfolding `PowellYuanIsPseudoInverseOf AkPlus Ak` gives the four Penrose identities used to
record the source role of `A_k⁺`. -/
theorem powellYuanIsPseudoInverseOf_iff
    (AkPlus : PseudoInverseMatrix)
    (Ak : Jacobian) :
    PowellYuanIsPseudoInverseOf AkPlus Ak ↔
      Ak * AkPlus * Ak = Ak ∧
        AkPlus * Ak * AkPlus = AkPlus ∧
        (Ak * AkPlus).transpose = Ak * AkPlus ∧
        (AkPlus * Ak).transpose = AkPlus * Ak :=
  Iff.rfl

end

/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.Block

namespace Matrix

variable {n R : Type*} [Preorder n] [Zero R] [One R]

/-- A square matrix is unit lower triangular when it is lower triangular and all of its diagonal
entries are `1`. The lower-triangular part reuses the canonical `BlockTriangular toDual` owner. -/
def IsUnitLowerTriangular (M : Matrix n n R) : Prop :=
  M.BlockTriangular OrderDual.toDual ∧ M.diag = 1

theorem IsUnitLowerTriangular.blockTriangular_toDual {M : Matrix n n R}
    (hM : M.IsUnitLowerTriangular) :
    M.BlockTriangular OrderDual.toDual :=
  hM.1

theorem IsUnitLowerTriangular.diag_eq_one {M : Matrix n n R}
    (hM : M.IsUnitLowerTriangular) :
    M.diag = 1 :=
  hM.2

theorem IsUnitLowerTriangular.apply_eq_zero {M : Matrix n n R}
    (hM : M.IsUnitLowerTriangular) {i j : n} (hij : i < j) :
    M i j = 0 :=
  hM.blockTriangular_toDual <| by
    simpa using (OrderDual.toDual_lt_toDual.mpr hij)

theorem IsUnitLowerTriangular.apply_diag {M : Matrix n n R}
    (hM : M.IsUnitLowerTriangular) (i : n) :
    M i i = 1 := by
  simpa using congrFun hM.diag_eq_one i

end Matrix

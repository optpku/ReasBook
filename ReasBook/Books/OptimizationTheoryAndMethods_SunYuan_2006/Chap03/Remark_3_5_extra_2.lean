/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.UnitaryGroup
import OptimizationTheoryAndMethods_SunYuan_2006.Matrix.UnitLowerTriangular

noncomputable section

open scoped BigOperators

section

variable {n : ℕ}

local notation "Vec" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

-- Semantic recall: `lean_leansearch` surfaced spectral-decomposition and eigenvector-basis
-- APIs for symmetric operators. This remark stays at a source-facing matrix recipe layer,
-- because the textbook item records one concrete construction of `(s_k, d_k)` rather than
-- a canonical mathlib owner.

/-- A source-facing encoding of the Bunch-Parlett requirement that `D_k` be block diagonal
with contiguous diagonal blocks of size `1` or `2`. The monotone block map records which
indices belong to the same diagonal block after the omitted permutations have been fixed. -/
structure IsBunchParlettBlockDiagonal (D : Mat) where
  blockCount : ℕ
  blockOf : Fin n → Fin blockCount
  blockOf_monotone : Monotone blockOf
  block_card_eq_one_or_two :
    ∀ b : Fin blockCount,
      (Finset.univ.filter fun i ↦ blockOf i = b).card = 1 ∨
        (Finset.univ.filter fun i ↦ blockOf i = b).card = 2
  zero_of_ne_block : ∀ ⦃i j : Fin n⦄, blockOf i ≠ blockOf j → D i j = 0

/-- The regularized eigenvalue `bar λ_j` from the Bunch-Parlett spectral modification in the
remark. The parameter `ε` is the source machine-precision constant, and the distinguished
index `maxAbsIndex` records an eigenvalue with maximal absolute value among the listed
`eigenvalues`. -/
def bunchParlettRegularizedEigenvalue
    (ε : ℝ) (eigenvalues : Fin n → ℝ) (maxAbsIndex : Fin n) (j : Fin n) : ℝ :=
  max (|eigenvalues j|) (max (ε * (n : ℝ) * |eigenvalues maxAbsIndex|) ε)

/-- The diagonal matrix `bar Λ_k = diag(bar λ_1^(k), ..., bar λ_n^(k))` from the source
regularization with machine precision `ε`. -/
def bunchParlettRegularizedSpectrum
    (ε : ℝ) (eigenvalues : Fin n → ℝ) (maxAbsIndex : Fin n) : Mat :=
  Matrix.diagonal (bunchParlettRegularizedEigenvalue ε eigenvalues maxAbsIndex)

/-- The regularized matrix `bar D_k = U_k bar Λ_k U_kᵀ` used to solve for `s_k`, again with
the source machine precision `ε`. -/
def bunchParlettRegularizedMatrix
    (U : Mat) (ε : ℝ) (eigenvalues : Fin n → ℝ) (maxAbsIndex : Fin n) : Mat :=
  U * bunchParlettRegularizedSpectrum ε eigenvalues maxAbsIndex * U.transpose

/-- The index set of the nonpositive eigenvalues appearing in the alternative source formula
for `d_k`. -/
def nonpositiveEigenvalueIndices (eigenvalues : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ eigenvalues j ≤ 0

/-- The shared Bunch-Parlett factorization and spectral data used in the remark to construct
the descent pair `(s_k, d_k)`. -/
structure BunchParlettSpectralSetup where
  G : Mat
  g : Vec
  ε : ℝ
  L : Mat
  D : Mat
  U : Mat
  eigenvalues : Fin n → ℝ
  maxAbsIndex : Fin n
  ε_pos : 0 < ε
  L_unitLowerTriangular : L.IsUnitLowerTriangular
  D_symmetric : Matrix.IsSymm D
  D_blockDiagonal : IsBunchParlettBlockDiagonal D
  U_orthogonal : U ∈ Matrix.orthogonalGroup (Fin n) ℝ
  factorization : G = L * D * L.transpose
  spectral : D = U * Matrix.diagonal eigenvalues * U.transpose
  maxAbs_spec : ∀ j, |eigenvalues j| ≤ |eigenvalues maxAbsIndex|

local notation "Setup" => @BunchParlettSpectralSetup n

namespace BunchParlettSpectralSetup

variable (setup : Setup)

/-- The orthogonal matrix stored in a `BunchParlettSpectralSetup` satisfies `U Uᵀ = 1`. -/
theorem mul_transpose_eq_one :
    setup.U * setup.U.transpose = 1 :=
  by simpa [Matrix.mem_orthogonalGroup_iff] using setup.U_orthogonal

/-- The orthogonal matrix stored in a `BunchParlettSpectralSetup` satisfies `Uᵀ U = 1`. -/
theorem transpose_mul_eq_one :
    setup.U.transpose * setup.U = 1 :=
  by simpa [Matrix.mem_orthogonalGroup_iff'] using setup.U_orthogonal

end BunchParlettSpectralSetup

/-- Chapter03 Remark 3.5-extra-2 (1): under the Bunch-Parlett factorization and spectral
setup, `s_k` is obtained as a solution of
`L_k bar D_k L_kᵀ s = -g_k`, where `bar D_k = U_k bar Λ_k U_kᵀ`. -/
structure HasBunchParlettStep (setup : BunchParlettSpectralSetup) where
  step : Vec
  equation :
    (setup.L * bunchParlettRegularizedMatrix
        setup.U setup.ε setup.eigenvalues setup.maxAbsIndex * setup.L.transpose).mulVec step =
      -setup.g

instance (setup : Setup) : CoeOut (HasBunchParlettStep setup) Vec where
  coe h := h.step

/-- Chapter03 Remark 3.5-extra-2 (2): under the same Bunch-Parlett setup, one source
construction of a negative curvature direction `d_k` uses a unit eigenvector corresponding
to the smallest eigenvalue of `D_k` and solves
`L_kᵀ d_k = ± |min {λ(D_k), 0}|^(1 / 2) z_k`. -/
structure HasSmallestEigenvalueDirection (setup : BunchParlettSpectralSetup) where
  direction : Vec
  minIndex : Fin n
  sign : ℝ
  sign_spec : sign = 1 ∨ sign = -1
  smallest_spec : ∀ j, setup.eigenvalues minIndex ≤ setup.eigenvalues j
  column_eigenvector_eq :
    setup.D.mulVec (Matrix.col setup.U minIndex) =
      setup.eigenvalues minIndex • Matrix.col setup.U minIndex
  column_unit : ‖Matrix.col setup.U minIndex‖ = 1
  direction_eq :
    Matrix.mulVec (Matrix.transpose setup.L) direction =
      (sign * Real.sqrt (|min (setup.eigenvalues minIndex) 0|)) • Matrix.col setup.U minIndex

instance (setup : Setup) :
    CoeOut (HasSmallestEigenvalueDirection setup) Vec where
  coe h := h.direction

/-- Chapter03 Remark 3.5-extra-2 (3): under the same Bunch-Parlett setup, another source
construction of a negative curvature direction `d_k` solves
`L_kᵀ d_k = ± ∑_{λ_j(D_k) ≤ 0} z_j`. -/
structure HasNonpositiveEigenvectorSumDirection (setup : BunchParlettSpectralSetup) where
  direction : Vec
  sign : ℝ
  sign_spec : sign = 1 ∨ sign = -1
  column_eigenvector_eq :
    ∀ j, setup.D.mulVec (Matrix.col setup.U j) = setup.eigenvalues j • Matrix.col setup.U j
  column_unit : ∀ j, ‖Matrix.col setup.U j‖ = 1
  direction_eq :
    Matrix.mulVec (Matrix.transpose setup.L) direction =
      sign • Finset.sum (nonpositiveEigenvalueIndices setup.eigenvalues) (Matrix.col setup.U)

instance (setup : Setup) :
    CoeOut (HasNonpositiveEigenvectorSumDirection setup) Vec where
  coe h := h.direction

end

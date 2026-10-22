/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_30

-- Declarations for this item will be appended below by the statement pipeline.

section

/-- Definition 1.31 (1): `positiveSemidefiniteMatrices n` is the set `𝕊_+^n` of real `n × n`
positive semidefinite matrices. -/
def positiveSemidefiniteMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.PosSemidef

/-- Definition 1.31 (2): `positiveDefiniteMatrices n` is the set `𝕊_{++}^n` of real `n × n`
positive definite matrices. -/
def positiveDefiniteMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.PosDef

/-- Definition 1.31 (3): `negativeSemidefiniteMatrices n` is the set `𝕊_-^n` of real `n × n`
negative semidefinite matrices. -/
def negativeSemidefiniteMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  fun A ↦ (-A).PosSemidef

/-- Definition 1.31 (4): `negativeDefiniteMatrices n` is the set `𝕊_{--}^n` of real `n × n`
negative definite matrices. -/
def negativeDefiniteMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  fun A ↦ (-A).PosDef

/-- A real matrix belongs to `𝕊_+^n` exactly when it is positive semidefinite. -/
theorem mem_positiveSemidefiniteMatrices_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ positiveSemidefiniteMatrices n ↔ A.PosSemidef :=
  Iff.rfl

/-- A real matrix belongs to `𝕊_{++}^n` exactly when it is positive definite. -/
theorem mem_positiveDefiniteMatrices_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ positiveDefiniteMatrices n ↔ A.PosDef :=
  Iff.rfl

/-- A real matrix belongs to `𝕊_-^n` exactly when its negation is positive semidefinite. -/
theorem mem_negativeSemidefiniteMatrices_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ negativeSemidefiniteMatrices n ↔ (-A).PosSemidef :=
  Iff.rfl

/-- A real matrix belongs to `𝕊_{--}^n` exactly when its negation is positive definite. -/
theorem mem_negativeDefiniteMatrices_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ negativeDefiniteMatrices n ↔ (-A).PosDef :=
  Iff.rfl

/-- Every positive definite real matrix is positive semidefinite. -/
theorem positiveDefiniteMatrices_subset_positiveSemidefiniteMatrices (n : ℕ) :
    positiveDefiniteMatrices n ⊆ positiveSemidefiniteMatrices n :=
  fun _ hA ↦ hA.posSemidef

/-- Every positive semidefinite real matrix belongs to the symmetric matrix space `𝕊^n`. -/
theorem positiveSemidefiniteMatrices_subset_symmetricMatrices (n : ℕ) :
    positiveSemidefiniteMatrices n ⊆
      (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :
        Set (Matrix (Fin n) (Fin n) ℝ)) := by
  intro A hA
  change IsSelfAdjoint A
  exact hA.isHermitian.isSelfAdjoint

end

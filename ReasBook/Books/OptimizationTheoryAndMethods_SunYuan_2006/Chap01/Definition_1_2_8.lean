/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.PosDef

-- Semantic recall: `lean_leansearch` identified `Matrix.PosDef` and `Matrix.PosSemidef`
-- in `Mathlib.LinearAlgebra.Matrix.PosDef` as the canonical mathlib notions.

/- Canonical recall: for a symmetric real square matrix `A`, positive definiteness is expressed by
`A.PosDef`. -/
#check Matrix.PosDef

/- Canonical recall: for a symmetric real square matrix `A`, positive semidefiniteness is
expressed by `A.PosSemidef`. -/
#check Matrix.PosSemidef

namespace Matrix

variable {n : ℕ}

/-- Chapter01 Definition 1.2.8 (1): for a symmetric real square matrix `A`, negative definiteness
means that `-A` is positive definite. -/
abbrev NegDef (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (-A).PosDef

/-- Characterization of `Matrix.NegDef`. -/
@[simp] theorem negDef_iff {A : Matrix (Fin n) (Fin n) ℝ} :
    A.NegDef ↔ (-A).PosDef :=
  Iff.rfl

/-- Chapter01 Definition 1.2.8 (2): for a symmetric real square matrix `A`, negative
semidefiniteness means that `-A` is positive semidefinite. -/
abbrev NegSemidef (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (-A).PosSemidef

/-- Characterization of `Matrix.NegSemidef`. -/
@[simp] theorem negSemidef_iff {A : Matrix (Fin n) (Fin n) ℝ} :
    A.NegSemidef ↔ (-A).PosSemidef :=
  Iff.rfl

namespace NegDef

/-- A negative definite real matrix is symmetric. -/
theorem isSymm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.NegDef) : A.IsSymm := by
  rw [← Matrix.isSymm_neg_iff]
  simpa using hA.isHermitian

/-- A negative definite real matrix is negative semidefinite. -/
theorem negSemidef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.NegDef) : A.NegSemidef :=
  hA.posSemidef

end NegDef

namespace NegSemidef

/-- A negative semidefinite real matrix is symmetric. -/
theorem isSymm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.NegSemidef) : A.IsSymm := by
  rw [← Matrix.isSymm_neg_iff]
  simpa using hA.isHermitian

end NegSemidef

/-- Chapter01 Definition 1.2.8 (3): a symmetric real square matrix is indefinite if it is neither
positive semidefinite nor negative semidefinite. -/
class Indefinite (A : Matrix (Fin n) (Fin n) ℝ) : Prop where
  isSymm : A.IsSymm
  not_posSemidef : ¬ A.PosSemidef
  not_negSemidef : ¬ A.NegSemidef

/-- Indefiniteness of a real square matrix is classically decidable. -/
noncomputable instance instDecidableIndefinite (A : Matrix (Fin n) (Fin n) ℝ) :
    Decidable A.Indefinite :=
  Classical.propDecidable _

/-- Characterization of `Matrix.Indefinite`. -/
@[simp] theorem indefinite_iff {A : Matrix (Fin n) (Fin n) ℝ} :
    A.Indefinite ↔ A.IsSymm ∧ ¬ A.PosSemidef ∧ ¬ A.NegSemidef := by
  constructor
  · intro hA
    exact ⟨hA.isSymm, hA.not_posSemidef, hA.not_negSemidef⟩
  · rintro ⟨hSymm, hNotPosSemidef, hNotNegSemidef⟩
    exact ⟨hSymm, hNotPosSemidef, hNotNegSemidef⟩

namespace Indefinite

/-- An indefinite real matrix cannot be positive definite. -/
theorem not_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.Indefinite) : ¬ A.PosDef := by
  intro hPosDef
  exact hA.not_posSemidef hPosDef.posSemidef

/-- An indefinite real matrix cannot be negative definite. -/
theorem not_negDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.Indefinite) : ¬ A.NegDef := by
  intro hNegDef
  exact hA.not_negSemidef hNegDef.posSemidef

end Indefinite

end Matrix

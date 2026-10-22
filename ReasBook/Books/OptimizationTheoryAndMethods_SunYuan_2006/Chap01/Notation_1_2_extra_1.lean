/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Matrix

/-
Chapter01 Notation 1.2-extra-1

Domain sampling for this recall item:
- primary domain: Euclidean-coordinate linear algebra over `ℝ` and `ℂ`
- core/canonical owners:
  * `EuclideanSpace 𝕜 (Fin n)` for `𝕜^n`
  * `Matrix.transpose` / postfix `ᵀ`
  * `Matrix.conjTranspose` / postfix `ᴴ`
  * `Matrix.toEuclideanLin` for matrix action on Euclidean spaces
- layer targeted here: `core/canonical`
- primitive data: only the dimensions `m`, `n`
- derived API: column-vector realizations and the induced transpose / conjugate-transpose /
  Euclidean linear-action views

Canonical recall for the book's vector and matrix notation:

- `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℂ (Fin n)` formalize `ℝ^n` and `ℂ^n`.
- A column vector is represented by `Matrix (Fin n) (Fin 1) 𝕜`, so `xᵀ` and `xᴴ` are
  `Matrix.transpose x` and `Matrix.conjTranspose x`.
- An `m × n` matrix `A : Matrix (Fin m) (Fin n) 𝕜` acts on coordinate vectors through the
  canonical linear map `Matrix.toEuclideanLin A :
    EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin m)`.

Mathlib recall hits verified for this item: `Matrix.transpose`, `Matrix.conjTranspose`,
`Matrix.toEuclideanLin`.
-/

section

variable {m n : ℕ}

#check EuclideanSpace ℝ (Fin n)
#check EuclideanSpace ℂ (Fin n)
#check Matrix (Fin n) (Fin 1) ℝ
#check Matrix (Fin n) (Fin 1) ℂ
#check (show Matrix (Fin n) (Fin 1) ℝ → Matrix (Fin 1) (Fin n) ℝ from (·ᵀ))
#check (show Matrix (Fin n) (Fin 1) ℂ → Matrix (Fin 1) (Fin n) ℂ from (·ᴴ))
#check (show Matrix (Fin m) (Fin n) ℝ ≃ₗ[ℝ]
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) from Matrix.toEuclideanLin)
#check (show Matrix (Fin m) (Fin n) ℂ ≃ₗ[ℂ]
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) from Matrix.toEuclideanLin)

/-- Helper for Chapter01 Notation 1.2-extra-1: the book's `xᵀ` notation is the canonical
matrix transpose on real column vectors. -/
theorem realColumnTranspose_eq_matrixTranspose (x : Matrix (Fin n) (Fin 1) ℝ) :
    xᵀ = Matrix.transpose x := by
  -- The postfix transpose notation is definitionally the matrix transpose.
  rfl

/-- Helper for Chapter01 Notation 1.2-extra-1: the book's `xᴴ` notation is the canonical
conjugate transpose on complex column vectors. -/
theorem complexColumnConjTranspose_eq_matrixConjTranspose (x : Matrix (Fin n) (Fin 1) ℂ) :
    xᴴ = Matrix.conjTranspose x := by
  -- The postfix conjugate-transpose notation is definitionally `Matrix.conjTranspose`.
  rfl

/-- Helper for Chapter01 Notation 1.2-extra-1: transporting a real matrix action back to
coordinate functions recovers ordinary matrix-vector multiplication. -/
theorem realMatrixAction_ofLp_eq_mulVec (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (Matrix.toEuclideanLin A x).ofLp = A *ᵥ x.ofLp := by
  -- Expand the Euclidean-space action into the canonical `toLp` model, then read off the
  -- underlying coordinate vector.
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Helper for Chapter01 Notation 1.2-extra-1: the complex Euclidean matrix action is likewise
ordinary matrix-vector multiplication after `ofLp`. -/
theorem complexMatrixAction_ofLp_eq_mulVec (A : Matrix (Fin m) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    (Matrix.toEuclideanLin A x).ofLp = A *ᵥ x.ofLp := by
  -- The complex case uses the same canonical `toLp` bridge and underlying coordinate readout.
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Chapter01 Notation 1.2-extra-1: the textbook notation for `ℝ^n`, `ℂ^n`, transpose,
conjugate transpose, and matrix-induced linear maps is realized canonically by Euclidean spaces,
matrix transpose operations, and `Matrix.toEuclideanLin`. -/
theorem notationRecallChecks
    (x : Matrix (Fin n) (Fin 1) ℝ) (z : Matrix (Fin n) (Fin 1) ℂ)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) (Fin n) ℂ)
    (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℂ (Fin n)) :
    xᵀ = Matrix.transpose x ∧
      zᴴ = Matrix.conjTranspose z ∧
      (Matrix.toEuclideanLin A u).ofLp = A *ᵥ u.ofLp ∧
      (Matrix.toEuclideanLin B v).ofLp = B *ᵥ v.ofLp := by
  -- Combine the canonical transpose and action identifications used throughout the file.
  constructor
  · exact realColumnTranspose_eq_matrixTranspose x
  constructor
  · exact complexColumnConjTranspose_eq_matrixConjTranspose z
  constructor
  · exact realMatrixAction_ofLp_eq_mulVec A u
  · exact complexMatrixAction_ofLp_eq_mulVec B v

end

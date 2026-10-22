/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace

noncomputable section

variable {m n : ℕ}

local notation "SymmMat" => 𝕊^n

/- Algorithm 5.4.4.1 lies in the semidefinite Newton-system domain.

Sampled owner-style declarations:
* Chapter 5 `𝕊^n` in `Definition_5_4_4_1`, the owner for real symmetric matrices;
* Chapter 5 `RealSymmetricMatrixSpace.frobeniusInner` in `Definition_5_4_4_2`, the owner for the
  Frobenius pairing on `𝕊^n`;
* Chapter 5 `𝕊^n₊₊` and `strictPositiveSemidefiniteCone_isSymm` in `Definition_5_4_4_5`, the
  owner and bridge for strict positive-definite symmetric matrices;
* mathlib `Matrix.mulVec`, the ambient coordinate-free linear-system owner for the normal
  equations once the entries are scalar-valued.

Best owner abstraction:
* source-facing: the semidefinite Newton normal system, its multiplier solutions, and the
  recovered Newton direction;
* core/canonical: the chapter carriers `𝕊^n`, `𝕊^n₊₊`, and the Frobenius pairing `⟪·, ·⟫_F`;
* bridge/view: ambient matrix multiplication and `Matrix.mulVec`.

Primitive data:
* `X : 𝕊^n₊₊`;
* `U : 𝕊^n`;
* `A : Fin m → 𝕊^n`.

Derived API:
* the conjugated sandwiches `sandwich X Aⱼ`;
* the normal matrix and right-hand side built from `⟪·, ·⟫_F`;
* a multiplier solving the normal equations `S λ = d`;
* the recovered Newton direction from a multiplier vector;
* the output relation pairing a displayed multiplier with its reconstructed Newton direction.

Source/core/bridge triage:
* source-facing: the algorithmic normal system, its multiplier solutions, and the output relation;
* core/canonical: the chapter symmetric-matrix and strict-cone owners;
* bridge/view: the ambient matrix formulas implementing conjugation and the normal equations.

This refinement keeps the algorithm source-facing, but removes the parallel raw-matrix Frobenius
owner and the explicit symmetry/positive-definiteness fields, since those are already carried by
the canonical Chapter 5 owners. -/

/-- The normal-equation matrix `S` with entries `S_(i,j) = ⟪A_i, X A_j X⟫_F`. -/
def semidefiniteNewtonNormalMatrix
    (X : 𝕊^n₊₊) (A : Fin m → SymmMat) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j ↦ ⟪A i, sandwich (X : SymmMat) (A j)⟫_F

/-- The right-hand side `d` with entries `d_i = ⟪A_i, X U X⟫_F`. -/
def semidefiniteNewtonNormalRhs
    (X : 𝕊^n₊₊) (U : SymmMat) (A : Fin m → SymmMat) :
    Fin m → ℝ :=
  fun i ↦ ⟪A i, sandwich (X : SymmMat) U⟫_F

/-- The matrix `Δ = X (-U + ∑_j λ_j A_j) X` recovered from a multiplier vector. -/
def semidefiniteNewtonDirectionFromMultiplier
    (X : 𝕊^n₊₊) (U : SymmMat) (A : Fin m → SymmMat) (multiplier : Fin m → ℝ) :
    SymmMat :=
  let correction : SymmMat := -U + ∑ j : Fin m, multiplier j • A j
  sandwich (X : SymmMat) correction

/-- A multiplier vector solves the semidefinite Newton normal equations `S λ = d`. -/
def IsSemidefiniteNewtonMultiplier
    (X : 𝕊^n₊₊) (U : SymmMat) (A : Fin m → SymmMat) (multiplier : Fin m → ℝ) : Prop :=
  Matrix.mulVec (semidefiniteNewtonNormalMatrix X A) multiplier =
    semidefiniteNewtonNormalRhs X U A

/-- Alg 5.4.4.1: with the symmetry and positive-definiteness assumptions carried by the Chapter 5
owners `𝕊^n` and `𝕊^n₊₊`, the pair `(λ, Δ)` is an output of the semidefinite Newton-direction
algorithm when `λ` solves the normal equations `S λ = d` and
`Δ = X (-U + ∑_j λ_j A_j) X`. -/
def IsSemidefiniteNewtonDirectionOutput
    (X : 𝕊^n₊₊) (U : SymmMat) (A : Fin m → SymmMat)
    (multiplier : Fin m → ℝ) (Δ : SymmMat) : Prop :=
  IsSemidefiniteNewtonMultiplier X U A multiplier ∧
    Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier

-- Proof sketch: unfold `IsSemidefiniteNewtonMultiplier`; after the owner-typed refinement, the
-- right-hand side is exactly the displayed matrix normal system `S λ = d`.
/-- Expanding `IsSemidefiniteNewtonMultiplier X U A multiplier` recovers the matrix-level normal
equations `S λ = d`. -/
theorem isSemidefiniteNewtonMultiplier_iff
    (X : 𝕊^n₊₊) (U : SymmMat) (A : Fin m → SymmMat) (multiplier : Fin m → ℝ) :
    IsSemidefiniteNewtonMultiplier X U A multiplier ↔
      Matrix.mulVec (semidefiniteNewtonNormalMatrix X A) multiplier =
        semidefiniteNewtonNormalRhs X U A :=
  Iff.rfl

@[simp] theorem IsSemidefiniteNewtonDirectionOutput.isMultiplier
    {X : 𝕊^n₊₊} {U : SymmMat} {A : Fin m → SymmMat}
    {multiplier : Fin m → ℝ} {Δ : SymmMat}
    (hOutput : IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ) :
    IsSemidefiniteNewtonMultiplier X U A multiplier :=
  hOutput.1

@[simp] theorem IsSemidefiniteNewtonDirectionOutput.direction_eq
    {X : 𝕊^n₊₊} {U : SymmMat} {A : Fin m → SymmMat}
    {multiplier : Fin m → ℝ} {Δ : SymmMat}
    (hOutput : IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ) :
    Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier :=
  hOutput.2

-- Proof sketch: unfold `IsSemidefiniteNewtonDirectionOutput`; after the owner-typed refinement,
-- the right-hand side is exactly the normal equations together with the explicit reconstruction
-- formula for the Newton direction attached to the displayed multiplier.
/-- Expanding `IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ` recovers the normal
equations and the explicit output formula, with symmetry and positive-definiteness already
absorbed into the Chapter 5 owners. -/
theorem isSemidefiniteNewtonDirectionOutput_iff
    (X : 𝕊^n₊₊) (U : SymmMat) (A : Fin m → SymmMat)
    (multiplier : Fin m → ℝ) (Δ : SymmMat) :
    IsSemidefiniteNewtonDirectionOutput X U A multiplier Δ ↔
      IsSemidefiniteNewtonMultiplier X U A multiplier ∧
        Δ = semidefiniteNewtonDirectionFromMultiplier X U A multiplier :=
  Iff.rfl

end

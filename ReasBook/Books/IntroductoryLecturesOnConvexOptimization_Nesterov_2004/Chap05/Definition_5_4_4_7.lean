/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open RealSymmetricMatrixSpace
open scoped ConstrainedArgmin RealSymmetricMatrixSpace

noncomputable section

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/-
Definition 5.4.4.7 lies in the semidefinite Newton-direction domain.

Sampled owner-style declarations:
* `𝕊^n₊₊` and `strictPositiveSemidefiniteCone_posDef` in Definition 5.4.4.5, the chapter owner
  for the strict positive-definite cone and its canonical matrix-level bridge;
* `StrictPositiveSemidefiniteCone.inv` and `RealSymmetricMatrixSpace.sandwich`, the intrinsic
  Chapter 5 owners for the symmetric-matrix conjugation `X⁻¹ Δ X⁻¹`;
* `realSymmetricMatrixConstraintMap` and `realSymmetricMatrixAssociatedAffineSubspace` in
  Definition 5.4.4.6, the chapter owners for the tangent constraint kernel and the feasible affine
  slice `𝓛`;
* `constrainedArgmin` / notation `argmin[Q] f` in Chapter 1, the canonical minimizer-set owner on
  a feasible set;
* `mem_constrainedArgmin_iff`, the canonical bridge from `argmin` membership to set membership
  plus `IsMinOn`.

Best owner abstraction:
* source-facing: the Newton-direction set at a feasible strict-cone point `X : 𝕊^n₊₊`;
* core/canonical: tangent directions through `(realSymmetricMatrixConstraintMap A).ker` and
  minimizers through `argmin`;
* bridge/view: feasibility of the base point through
  `realSymmetricMatrixAssociatedAffineSubspace A b`.

Primitive data:
* the constraint matrices `A : Fin m → 𝕊^n`;
* the strict-cone base point `X : 𝕊^n₊₊`;
* the linear term `U : 𝕊^n`.

Derived API:
* the quadratic Newton objective `semidefiniteNewtonDirectionObjective X U`, built from the
  Chapter 5 owners `⟪·, ·⟫_F` and `sandwich (StrictPositiveSemidefiniteCone.inv X)`;
* the Newton-direction set `semidefiniteNewtonDirectionSet A X U`;
* the affine-slice bridge theorem that reintroduces `b` only when one wants the textbook
  feasibility statement.

Source/core/bridge triage:
* source-facing: the Newton directions of the barrier at a strict-cone feasible point;
* core/canonical: the constraint-map kernel and the minimizer owner `argmin`;
* bridge/view: the Frobenius-equation theorems for the base-point feasibility and tangent
  constraints.
-/

/-- The equality-constrained quadratic objective whose minimizers are the Newton directions for
the restriction of the semidefinite log-determinant barrier at the strict-cone point `X`. -/
def semidefiniteNewtonDirectionObjective (X : 𝕊^n₊₊) (U : SymmMat) : SymmMat → ℝ :=
  fun Δ ↦
    ⟪U, Δ⟫_F +
      (1 / 2 : ℝ) *
        ⟪sandwich (StrictPositiveSemidefiniteCone.inv X) Δ, Δ⟫_F

-- Proof sketch: unfold `semidefiniteNewtonDirectionObjective`, then rewrite the intrinsic
-- symmetric-matrix sandwich `sandwich (StrictPositiveSemidefiniteCone.inv X) Δ` and the
-- Frobenius pairing by their ambient matrix formulas.
/-- Evaluating `semidefiniteNewtonDirectionObjective X U` at `Δ` gives the quadratic Newton-model
expression `⟨U, Δ⟩_F + (1 / 2) ⟨X⁻¹ Δ X⁻¹, Δ⟩_F`. -/
theorem semidefiniteNewtonDirectionObjective_apply
    (X : 𝕊^n₊₊) (U Δ : SymmMat) :
    semidefiniteNewtonDirectionObjective X U Δ =
      ⟪U, Δ⟫_F +
        (1 / 2 : ℝ) *
          Matrix.trace
            ((((X : SymmMat) : Mat)⁻¹ * (Δ : Mat) * ((X : SymmMat) : Mat)⁻¹)ᵀ *
              (Δ : Mat)) := by
  calc
    semidefiniteNewtonDirectionObjective X U Δ =
        ⟪U, Δ⟫_F +
          (1 / 2 : ℝ) *
            ⟪sandwich (StrictPositiveSemidefiniteCone.inv X) Δ, Δ⟫_F :=
      rfl
    _ =
        ⟪U, Δ⟫_F +
          (1 / 2 : ℝ) *
            Matrix.trace
              ((((X : SymmMat) : Mat)⁻¹ * (Δ : Mat) * ((X : SymmMat) : Mat)⁻¹)ᵀ *
                (Δ : Mat)) := by
      congr 1
      rw [frobeniusInner_def]
      simp [StrictPositiveSemidefiniteCone.coe_inv]

/-- Definition 5.4.4.7: for a strict-cone base point `X`, the Newton directions are the
minimizers of the quadratic model `⟨U, Δ⟩_F + (1 / 2) ⟨X⁻¹ Δ X⁻¹, Δ⟩_F` on the tangent kernel
`⟨Aᵢ, Δ⟩_F = 0`. When `X` also lies in the affine slice
`realSymmetricMatrixAssociatedAffineSubspace A b`, this is exactly the textbook Newton-direction
set for the barrier restricted to `𝓛`. -/
def semidefiniteNewtonDirectionSet
    (A : Fin m → SymmMat) (X : 𝕊^n₊₊) (U : SymmMat) : Set SymmMat :=
  argmin[(realSymmetricMatrixConstraintMap A).ker]
    (semidefiniteNewtonDirectionObjective X U)

/-- Expanding Newton-direction membership through the `argmin` owner recovers the tangent
Frobenius equations and the minimizing property on the constraint kernel. -/
theorem mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn
    {A : Fin m → SymmMat} {X : 𝕊^n₊₊} {U Δ : SymmMat} :
    Δ ∈ semidefiniteNewtonDirectionSet A X U ↔
      (∀ i : Fin m, ⟪A i, Δ⟫_F = 0) ∧
        IsMinOn (semidefiniteNewtonDirectionObjective X U)
          (realSymmetricMatrixConstraintMap A).ker Δ := by
  rw [semidefiniteNewtonDirectionSet, mem_constrainedArgmin_iff]
  constructor
  · rintro ⟨hΔ, hmin⟩
    change realSymmetricMatrixConstraintMap A Δ = 0 at hΔ
    refine ⟨?_, hmin⟩
    intro i
    simpa [realSymmetricMatrixConstraintMap_apply] using
      congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v i) hΔ
  · rintro ⟨hΔ, hmin⟩
    refine ⟨?_, hmin⟩
    change realSymmetricMatrixConstraintMap A Δ = 0
    apply PiLp.ext
    intro i
    simpa [realSymmetricMatrixConstraintMap_apply] using hΔ i

/-- For a strict-cone point `X` already known to lie in the affine slice `𝓛`, expanding
`semidefiniteNewtonDirectionSet A X U` recovers the textbook Frobenius feasibility equations for
`X` together with the minimizing property on tangent directions. -/
theorem mem_semidefiniteNewtonDirectionSet_iff_feasible_frobenius_isMinOn
    {A : Fin m → SymmMat} {b : EuclideanSpace ℝ (Fin m)} {X : 𝕊^n₊₊} {U Δ : SymmMat}
    (hX : (X : SymmMat) ∈ realSymmetricMatrixAssociatedAffineSubspace A b) :
    Δ ∈ semidefiniteNewtonDirectionSet A X U ↔
      (∀ i : Fin m, ⟪A i, (X : SymmMat)⟫_F = b i) ∧
        (∀ i : Fin m, ⟪A i, Δ⟫_F = 0) ∧
          IsMinOn (semidefiniteNewtonDirectionObjective X U)
            (realSymmetricMatrixConstraintMap A).ker Δ := by
  rw [mem_semidefiniteNewtonDirectionSet_iff_frobenius_isMinOn]
  constructor
  · intro hΔ
    exact ⟨mem_realSymmetricMatrixAssociatedAffineSubspace_iff.mp hX, hΔ.1, hΔ.2⟩
  · rintro ⟨_, hΔ, hmin⟩
    exact ⟨hΔ, hmin⟩

end

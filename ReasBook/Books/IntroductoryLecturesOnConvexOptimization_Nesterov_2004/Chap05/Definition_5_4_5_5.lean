/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped BigOperators RealInnerProductSpace RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

private abbrev quadraticSlack
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : SymmMat) (i : Fin m) : ℝ :=
  (b i - ⟪a i, v⟫) ^ (2 : ℕ) - ⟪(H : Mat).toEuclideanLin (a i), a i⟫

/- Definition 5.4.5.5 lies in the circumscribed-ellipsoid / logarithmic-barrier domain.

Sampled owner-style declarations in this domain:
* `logDetBarrier` and `logDetBarrier_apply` in `Chap05/Definition_5_4_4_5`, the chapter owner of
  the `-log det` contribution on `𝕊^n₊₊`;
* `circumscribedEllipsoidShapeSet` and
  `mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff` in
  `Chap05/Definition_5_4_5_4`, the adjacent primitive shape constraints and their nonstrict
  epigraph reformulation;
* `minimumVolumeEnclosingEllipsoidBarrier` and
  `MinimumVolumeEnclosingEllipsoidBarrierPoint` in `Chap05/Definition_5_4_5_2`, the chapter
  barrier-owner pattern on a strict-domain subtype;
* `semidefiniteAffineLogDetBarrier` and `SemidefiniteAffineBarrierPoint` in
  `Chap05/Definition_5_4_4_8`, the same log-determinant barrier pattern on a pullback strict
  domain;
* `Matrix.toEuclideanLin` in `Chap05/Definition_5_0_6`, the canonical linear-operator owner for a
  matrix acting on `EuclideanSpace ℝ (Fin n)`;
* `inner ℝ` and `EuclideanSpace.inner_eq_star_dotProduct` in `Chap01/Definition_1_4_4`, the
  owner/bridge pair showing that the quadratic term should live in the intrinsic inner-product
  language, with `dotProduct` only as its coordinate realization.

Source/core/bridge triage:
* source-facing: the strict circumscribed-ellipsoid barrier domain and barrier;
* core/canonical: `logDetBarrier n` on `𝕊^n₊₊`;
* bridge/view: the ambient pair domain
  `circumscribedEllipsoidBarrierAmbientDomain` and formula
  `circumscribedEllipsoidBarrierAmbient` on `𝕊^n × ℝ`.

Primitive data:
* the half-space data `a`, `b`, and the fixed center `v`.

Derived API:
* the strict domain `circumscribedEllipsoidBarrierDomain a b v`;
* the strict-domain carrier `CircumscribedEllipsoidBarrierPoint a b v`;
* the ambient bridge domain `circumscribedEllipsoidBarrierAmbientDomain a b v`;
* the ambient bridge formula `circumscribedEllipsoidBarrierAmbient a b v`;
* the source-facing barrier `circumscribedEllipsoidBarrier a b v`.

This file therefore reuses the chapter owner `logDetBarrier` for the determinant contribution and
keeps the raw formula only as a bridge, instead of maintaining a parallel ambient barrier owner on
all pairs `(H, τ)`.
-/

/-- The strict domain on which the circumscribed-ellipsoid logarithmic barrier is defined. -/
def circumscribedEllipsoidBarrierDomain
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) : Set (𝕊^n₊₊ × ℝ) :=
  {Hτ | 0 < Hτ.2 - logDetBarrier n Hτ.1 ∧
    ∀ i : Fin m, 0 < quadraticSlack a b v Hτ.1 i}

/-- The ambient pullback domain of the circumscribed-ellipsoid logarithmic barrier on
`𝕊ⁿ × ℝ`. It is a bridge/view that records strict positivity of the shape variable together with
the same strict slack inequalities used by the source-facing strict-domain owner
`circumscribedEllipsoidBarrierDomain a b v`. -/
def circumscribedEllipsoidBarrierAmbientDomain
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) : Set (SymmMat × ℝ) :=
  {Hτ | Hτ.1 ∈ (𝕊^n₊₊ : Set SymmMat) ∧
    0 < Hτ.2 - logDetBarrierAmbient n Hτ.1 ∧
      ∀ i : Fin m, 0 < quadraticSlack a b v Hτ.1 i}

/-- Membership in the barrier domain means that the shifted logarithmic argument
`τ - logDetBarrier n H = τ + log det H` is positive and every quadratic slack
`(bᵢ - ⟪aᵢ, v⟫)^2 - ⟪H aᵢ, aᵢ⟫` is positive. -/
theorem mem_circumscribedEllipsoidBarrierDomain_iff
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v ↔
      0 < τ - logDetBarrier n H ∧
        ∀ i : Fin m,
          0 < (b i - ⟪a i, v⟫) ^ (2 : ℕ) -
            ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ := by
  simp [circumscribedEllipsoidBarrierDomain, quadraticSlack, toMatrix_def]

/-- Membership in the ambient bridge domain means that the shape variable lies in the strict
cone, the shifted logarithmic argument `τ + log det H` is positive, and every quadratic slack
`(bᵢ - ⟪aᵢ, v⟫)^2 - ⟪H aᵢ, aᵢ⟫` is positive. -/
theorem mem_circumscribedEllipsoidBarrierAmbientDomain_iff
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : SymmMat) (τ : ℝ) :
    (H, τ) ∈ circumscribedEllipsoidBarrierAmbientDomain a b v ↔
      H ∈ (𝕊^n₊₊ : Set SymmMat) ∧
        0 < τ - logDetBarrierAmbient n H ∧
          ∀ i : Fin m,
            0 < (b i - ⟪a i, v⟫) ^ (2 : ℕ) -
              ⟪(H : Mat).toEuclideanLin (a i), a i⟫ := by
  rfl

/-- Restricting the ambient bridge domain to a strict-cone shape recovers the source-facing
strict-domain owner. -/
@[simp] theorem mem_circumscribedEllipsoidBarrierAmbientDomain_iff_strict
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    ((H : SymmMat), τ) ∈ circumscribedEllipsoidBarrierAmbientDomain a b v ↔
      (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v := by
  simp [circumscribedEllipsoidBarrierAmbientDomain, circumscribedEllipsoidBarrierDomain,
    logDetBarrier, logDetBarrierAmbient]

/-- Expanding `logDetBarrier n` rewrites barrier-domain membership back to the textbook
`τ + log det H` formula. -/
theorem mem_circumscribedEllipsoidBarrierDomain_iff_formula
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v ↔
      0 < τ + Real.log (toMatrix H).det ∧
        ∀ i : Fin m,
          0 < (b i - ⟪a i, v⟫) ^ (2 : ℕ) -
            ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ := by
  simp [mem_circumscribedEllipsoidBarrierDomain_iff, toMatrix_def]

/-- The subtype of points in the strict circumscribed-ellipsoid barrier domain. This is the
natural owner carrier for the circumscribed-ellipsoid logarithmic barrier. -/
abbrev CircumscribedEllipsoidBarrierPoint
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) :=
  {Hτ : 𝕊^n₊₊ × ℝ // Hτ ∈ circumscribedEllipsoidBarrierDomain a b v}

/-- The ambient formula underlying the circumscribed-ellipsoid logarithmic barrier. It is only a
bridge view; the owner barrier is `circumscribedEllipsoidBarrier a b v` on
`CircumscribedEllipsoidBarrierPoint a b v`. -/
def circumscribedEllipsoidBarrierAmbient
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) : SymmMat × ℝ → ℝ :=
  fun Hτ ↦
    logDetBarrierAmbient n Hτ.1
      - Real.log (Hτ.2 - logDetBarrierAmbient n Hτ.1)
      - ∑ i : Fin m, Real.log (quadraticSlack a b v Hτ.1 i)

/-- Definition 5.4.5.5: the logarithmic barrier for the circumscribed-ellipsoid reformulation,
kept on its strict domain. -/
def circumscribedEllipsoidBarrier
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) :
    CircumscribedEllipsoidBarrierPoint a b v → ℝ :=
  fun Hτ ↦ circumscribedEllipsoidBarrierAmbient a b v ((Hτ.1.1 : SymmMat), Hτ.1.2)

/-- Evaluating the ambient circumscribed-ellipsoid barrier recovers the owner formula equivalent
to the textbook expression
`-log det H - log (τ + log det H) - \sum_i log ((bᵢ - ⟪aᵢ, v⟫)^2 - aᵢᵀ H aᵢ)`. -/
theorem circumscribedEllipsoidBarrierAmbient_apply
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : SymmMat) (τ : ℝ) :
    circumscribedEllipsoidBarrierAmbient a b v (H, τ) =
      logDetBarrierAmbient n H
        - Real.log (τ - logDetBarrierAmbient n H)
        - ∑ i : Fin m,
            Real.log
              ((b i - ⟪a i, v⟫) ^ (2 : ℕ) -
                ⟪(H : Mat).toEuclideanLin (a i), a i⟫) := by
  simp [circumscribedEllipsoidBarrierAmbient, quadraticSlack]

/-- On a strict-cone slice, the ambient circumscribed-ellipsoid barrier agrees with the owner
formula built from `logDetBarrier n`. -/
theorem circumscribedEllipsoidBarrierAmbient_apply_strict
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    circumscribedEllipsoidBarrierAmbient a b v ((H : SymmMat), τ) =
      logDetBarrier n H
        - Real.log (τ - logDetBarrier n H)
        - ∑ i : Fin m,
            Real.log
              ((b i - ⟪a i, v⟫) ^ (2 : ℕ) -
                ⟪(toMatrix H).toEuclideanLin (a i), a i⟫) := by
  simp [circumscribedEllipsoidBarrierAmbient_apply, toMatrix_def]

/-- Evaluating the circumscribed-ellipsoid barrier on a strict-domain point recovers its ambient
bridge formula. -/
@[simp] theorem circumscribedEllipsoidBarrier_apply
    (a : Fin m → E) (b : Fin m → ℝ) (v : E)
    (Hτ : CircumscribedEllipsoidBarrierPoint a b v) :
    circumscribedEllipsoidBarrier a b v Hτ =
      circumscribedEllipsoidBarrierAmbient a b v ((Hτ.1.1 : SymmMat), Hτ.1.2) :=
  rfl

/-- At a strict-domain pair `(H, τ)`, the circumscribed-ellipsoid logarithmic barrier is the
owner formula built from the chapter determinant barrier `logDetBarrier n`. -/
theorem circumscribedEllipsoidBarrier_apply_pair
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ)
    (h : (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v) :
    circumscribedEllipsoidBarrier a b v ⟨(H, τ), h⟩ =
      logDetBarrier n H
        - Real.log (τ - logDetBarrier n H)
        - ∑ i : Fin m,
            Real.log
              ((b i - ⟪a i, v⟫) ^ (2 : ℕ) -
                ⟪(toMatrix H).toEuclideanLin (a i), a i⟫) := by
  simpa [toMatrix_def] using circumscribedEllipsoidBarrierAmbient_apply_strict a b v H τ

/-- Expanding `logDetBarrier n` rewrites the circumscribed-ellipsoid barrier back to the textbook
formula `-log det H - log (τ + log det H) - \sum_i log ((bᵢ - ⟪aᵢ, v⟫)^2 - aᵢᵀ H aᵢ)`. -/
theorem circumscribedEllipsoidBarrier_apply_pair_formula
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ)
    (h : (H, τ) ∈ circumscribedEllipsoidBarrierDomain a b v) :
    circumscribedEllipsoidBarrier a b v ⟨(H, τ), h⟩ =
      -Real.log (toMatrix H).det
        - Real.log (τ + Real.log (toMatrix H).det)
        - ∑ i : Fin m,
            Real.log
              ((b i - ⟪a i, v⟫) ^ (2 : ℕ) -
                ⟪(toMatrix H).toEuclideanLin (a i), a i⟫) := by
  rw [circumscribedEllipsoidBarrier_apply_pair]
  simp [toMatrix_def]

end

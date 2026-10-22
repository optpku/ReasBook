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
open scoped MatrixOrder RealSymmetricMatrixSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 5.4.4.8 lies in the semidefinite affine-epigraph / log-determinant barrier domain.

Sampled owner-style declarations:
* Chapter 5 `𝕊^n`, `𝕊^n₊`, and `𝕊^n₊₊`, the intrinsic symmetric-matrix and cone owners;
* Chapter 5 `logDetBarrier n`, the owner barrier on the strict cone subtype;
* `AffineMap.fst`, `LinearMap.snd`, and `Set.preimage`, the canonical affine and pullback owners.

Source/core/bridge triage:
* source-facing: the affine slack map into `𝕊^n`, the semidefinite epigraph, and the strict-domain
  semidefinite affine log-determinant barrier;
* core/canonical: `AffineMap`, `𝕊^n₊`, `𝕊^n₊₊`, and `logDetBarrier n`;
* bridge/view: the ambient matrix formula `t I - 𝓐(x)` and the ambient barrier formula
  `-log det (t I - 𝓐(x))`.

Primitive data:
* an affine map `𝓐 : E →ᵃ[ℝ] SymmMat`.

Derived API:
* the affine slack map `(x, t) ↦ t I - 𝓐(x)` valued in `𝕊^n`;
* the semidefinite epigraph and strict barrier domain as pullbacks of `𝕊^n₊` and `𝕊^n₊₊`;
* the strict-domain barrier on the barrier-point subtype;
* the ambient bridge formula on `E × ℝ`.

This refinement removes the raw matrix-valued duplicate owner and reuses the chapter's intrinsic
symmetric-matrix and cone owners directly. The textbook ambient matrix formula is retained only as
a bridge.
-/

/-- The affine slack map `(x, t) ↦ t I - 𝓐(x)` valued in the symmetric-matrix carrier `𝕊^n`. -/
abbrev semidefiniteAffineSlack
    (𝓐 : E →ᵃ[ℝ] SymmMat) : E × ℝ →ᵃ[ℝ] SymmMat :=
  ((LinearMap.snd ℝ E ℝ).smulRight (1 : SymmMat)).toAffineMap -
    𝓐.comp (AffineMap.fst : E × ℝ →ᵃ[ℝ] E)

/-- Evaluating `semidefiniteAffineSlack` at `(x, t)` gives the source-facing formula
`t I - 𝓐(x)` in `𝕊^n`. -/
@[simp] theorem semidefiniteAffineSlack_apply
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ) :
    semidefiniteAffineSlack 𝓐 (x, t) = t • (1 : SymmMat) - 𝓐 x :=
  rfl

/-- Coercing the affine slack matrix to ambient matrices recovers the textbook formula
`t I - 𝓐(x)`. -/
@[simp] theorem semidefiniteAffineSlack_apply_matrix
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ) :
    ((semidefiniteAffineSlack 𝓐 (x, t) : SymmMat) : Mat) =
      t • (1 : Mat) - (𝓐 x : Mat) :=
  rfl

/-- The semidefinite epigraph `K = {(x, t) | t I - 𝓐(x) ∈ 𝕊ⁿ₊}` attached to the affine
symmetric-matrix map `𝓐`. -/
def semidefiniteAffineEpigraph
    (𝓐 : E →ᵃ[ℝ] SymmMat) : Set (E × ℝ) :=
  semidefiniteAffineSlack 𝓐 ⁻¹' (𝕊^n₊ : Set SymmMat)

/-- Membership in the semidefinite epigraph means that the intrinsic slack matrix lies in
`𝕊ⁿ₊`. -/
@[simp] theorem mem_semidefiniteAffineEpigraph_iff
    (𝓐 : E →ᵃ[ℝ] SymmMat) (xt : E × ℝ) :
    xt ∈ semidefiniteAffineEpigraph 𝓐 ↔
      semidefiniteAffineSlack 𝓐 xt ∈ 𝕊^n₊ :=
  Iff.rfl

/-- In pair coordinates, membership in the semidefinite epigraph means that the textbook slack
matrix `t I - 𝓐(x)` is positive semidefinite. -/
theorem mem_semidefiniteAffineEpigraph_pair_iff
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ) :
    (x, t) ∈ semidefiniteAffineEpigraph 𝓐 ↔
      (t • (1 : Mat) - (𝓐 x : Mat)).PosSemidef := by
  rw [mem_semidefiniteAffineEpigraph_iff, mem_positiveSemidefiniteCone_iff,
    semidefiniteAffineSlack_apply_matrix]

/-- The strict domain on which the semidefinite affine log-determinant barrier is defined. -/
def semidefiniteAffineLogDetBarrierDomain
    (𝓐 : E →ᵃ[ℝ] SymmMat) : Set (E × ℝ) :=
  semidefiniteAffineSlack 𝓐 ⁻¹' (𝕊^n₊₊ : Set SymmMat)

/-- Membership in the strict barrier domain means that the intrinsic slack matrix lies in
`𝕊ⁿ₊₊`. -/
@[simp] theorem mem_semidefiniteAffineLogDetBarrierDomain_iff
    (𝓐 : E →ᵃ[ℝ] SymmMat) (xt : E × ℝ) :
    xt ∈ semidefiniteAffineLogDetBarrierDomain 𝓐 ↔
      semidefiniteAffineSlack 𝓐 xt ∈ 𝕊^n₊₊ :=
  Iff.rfl

/-- In pair coordinates, membership in the strict barrier domain means that the textbook slack
matrix `t I - 𝓐(x)` is positive definite. -/
theorem mem_semidefiniteAffineLogDetBarrierDomain_pair_iff
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ) :
    (x, t) ∈ semidefiniteAffineLogDetBarrierDomain 𝓐 ↔
      (t • (1 : Mat) - (𝓐 x : Mat)).PosDef := by
  rw [mem_semidefiniteAffineLogDetBarrierDomain_iff]
  constructor
  · intro h
    simpa [semidefiniteAffineSlack_apply_matrix] using
      strictPositiveSemidefiniteCone_posDef
        ⟨semidefiniteAffineSlack 𝓐 (x, t), h⟩
  · intro h
    exact mem_strictPositiveSemidefiniteCone_of_posDef <|
      by simpa [semidefiniteAffineSlack_apply_matrix] using h

/-- The subtype of points in the strict semidefinite affine barrier domain. -/
abbrev SemidefiniteAffineBarrierPoint
    (𝓐 : E →ᵃ[ℝ] SymmMat) :=
  {xt : E × ℝ // xt ∈ semidefiniteAffineLogDetBarrierDomain 𝓐}

/-- The ambient formula underlying the semidefinite affine log-determinant barrier. It is only a
bridge view; the owner barrier is `semidefiniteAffineLogDetBarrier 𝓐` on
`SemidefiniteAffineBarrierPoint 𝓐`. -/
def semidefiniteAffineLogDetBarrierAmbient
    (𝓐 : E →ᵃ[ℝ] SymmMat) : E × ℝ → ℝ :=
  fun xt ↦ logDetBarrierAmbient n (semidefiniteAffineSlack 𝓐 xt)

/-- Definition 5.4.4.8: the logarithmic-determinant barrier on the strict domain
`{(x, t) | t I - 𝓐(x) ∈ 𝕊ⁿ₊₊}`. -/
def semidefiniteAffineLogDetBarrier
    (𝓐 : E →ᵃ[ℝ] SymmMat) : SemidefiniteAffineBarrierPoint 𝓐 → ℝ :=
  fun xt ↦ logDetBarrier n ⟨semidefiniteAffineSlack 𝓐 xt.1, xt.2⟩

/-- Evaluating the semidefinite affine log-determinant barrier recovers its ambient bridge
formula. -/
@[simp] theorem semidefiniteAffineLogDetBarrier_apply
    (𝓐 : E →ᵃ[ℝ] SymmMat) (xt : SemidefiniteAffineBarrierPoint 𝓐) :
    semidefiniteAffineLogDetBarrier 𝓐 xt =
      semidefiniteAffineLogDetBarrierAmbient 𝓐 xt :=
  rfl

/-- At a strict-domain pair `(x, t)`, the semidefinite affine log-determinant barrier is the
textbook formula `-log det (t I - 𝓐(x))`. -/
theorem semidefiniteAffineLogDetBarrier_apply_pair
    (𝓐 : E →ᵃ[ℝ] SymmMat) (x : E) (t : ℝ)
    (h : (x, t) ∈ semidefiniteAffineLogDetBarrierDomain 𝓐) :
    semidefiniteAffineLogDetBarrier 𝓐 ⟨(x, t), h⟩ =
      -Real.log (t • (1 : Mat) - (𝓐 x : Mat)).det := by
  rw [semidefiniteAffineLogDetBarrier]
  rw [logDetBarrier_apply]
  rw [semidefiniteAffineSlack_apply_matrix]

end

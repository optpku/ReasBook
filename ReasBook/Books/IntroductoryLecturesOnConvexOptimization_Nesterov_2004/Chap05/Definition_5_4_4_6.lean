/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped RealSymmetricMatrixSpace

noncomputable section

variable {m n : ℕ}

/- Definition 5.4.4.6 lies in the affine linear-constraint domain on the symmetric-matrix
Frobenius space.

Sampled owner-style declarations:
* `AffineSubspace` in mathlib, the canonical owner for affine subsets, including the empty case;
* `AffineSubspace.comap`, the canonical preimage owner under an affine map;
* `AffineSubspace.mk'` and `AffineSubspace.mem_mk'`, the canonical singleton affine-subspace owner
  and its membership bridge;
* `LinearMap.toAffineMap`, the canonical bridge from a linear constraint map to an affine map.

Best owner abstraction:
* source-facing: the associated affine subspace cut out by the Frobenius equations;
* core/canonical: `AffineSubspace ℝ (𝕊^n)`;
* bridge/view: the constraint linear map and the set-style membership theorem.

Primitive data:
* the constraint matrices `A : Fin m → 𝕊^n`;
* the right-hand side `b : EuclideanSpace ℝ (Fin m)`.

Derived API:
* the linear constraint map `realSymmetricMatrixConstraintMap A`;
* the affine subspace `realSymmetricMatrixAssociatedAffineSubspace A b`;
* the membership characterization
  `mem_realSymmetricMatrixAssociatedAffineSubspace_iff`.

Source/core/bridge triage:
* source-facing: `realSymmetricMatrixAssociatedAffineSubspace A b`;
* core/canonical: `AffineSubspace.comap` of the singleton `{b}` under the constraint map;
* bridge/view: the coordinate-free linear map and the pointwise membership lemma.

The refinement therefore keeps the source-facing affine-constraint locus, but upgrades its public
owner from a duplicate bare `Set` to the canonical mathlib affine-subspace owner. -/

/-- The linear map sending `X ∈ 𝕊^n` to the vector of Frobenius constraint values
`(⟪Aᵢ, X⟫_F)_i`. -/
def realSymmetricMatrixConstraintMap
    (A : Fin m → 𝕊^n) : 𝕊^n →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi fun i ↦ innerₛₗ ℝ (A i))

/-- The `i`-th coordinate of the constraint map is the Frobenius pairing with `Aᵢ`. -/
@[simp] theorem realSymmetricMatrixConstraintMap_apply
    (A : Fin m → 𝕊^n) (X : 𝕊^n) (i : Fin m) :
    realSymmetricMatrixConstraintMap A X i = ⟪A i, X⟫_F := by
  simp [realSymmetricMatrixConstraintMap, RealSymmetricMatrixSpace.frobeniusInner]

/-- Definition 5.4.4.6: for symmetric matrices `A₁, …, Aₘ ∈ 𝕊ⁿ` and `b ∈ ℝᵐ`, the associated
affine subspace is the affine subset of `𝕊ⁿ` cut out by the Frobenius inner-product equations
`⟨Aᵢ, X⟩_F = bᵢ` for all `i`. -/
def realSymmetricMatrixAssociatedAffineSubspace
    (A : Fin m → 𝕊^n) (b : EuclideanSpace ℝ (Fin m)) : AffineSubspace ℝ (𝕊^n) :=
  (AffineSubspace.mk' b (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin m)))).comap
    (realSymmetricMatrixConstraintMap A).toAffineMap

/-- Membership in the associated affine subspace means satisfying all Frobenius constraints
`⟨Aᵢ, X⟩_F = bᵢ`. -/
theorem mem_realSymmetricMatrixAssociatedAffineSubspace_iff
    {A : Fin m → 𝕊^n} {b : EuclideanSpace ℝ (Fin m)} {X : 𝕊^n} :
    X ∈ realSymmetricMatrixAssociatedAffineSubspace A b ↔
      ∀ i : Fin m, ⟪A i, X⟫_F = b i := by
  rw [realSymmetricMatrixAssociatedAffineSubspace, AffineSubspace.mem_comap, AffineSubspace.mem_mk',
    Submodule.mem_bot, vsub_eq_sub, sub_eq_zero]
  constructor
  · intro h i
    simpa using congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v i) h
  · intro h
    apply PiLp.ext
    intro i
    simpa using h i

end

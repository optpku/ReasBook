/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_81
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_82
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u v

/- Lemma 7.16 lies in the Chapter 7 whole-space subdifferential / affine-pullback domain.

Mandatory domain-style sampling before refinement:
- `StrictlyPositiveOn` and `StrictlyPositiveOn.inequality` in `Definition_7_81`, the source-facing
  owner and its atomic projection lemma;
- `subdifferential_comp_affineMap_image_adjoint_subset` in `Chap03/Lemma_3_11`, the Euclidean
  affine-pullback bridge on subgradients;
- `IsSubgradientAt.comp_affineMap` in `Chap03/Definition_3_1_5`, the owner-level affine pullback
  theorem on subgradients;
- `matrix_transpose_adjointness` in `Chap01/Proposition_1_4_5`, the Euclidean bridge rewriting
  `⟪g, A (y - x)⟫` as `⟪Aᵀ g, y - x⟫`;
- `mem_preimage_linearMap_add_iff` in `Definition_7_82`, the chapter's canonical bridge for the
  affine preimage set `Q_y = {y | A y + b ∈ Q_x}`.

Best owner abstraction:
- source-facing: the affine-pullback inequality for explicit pulled-back subgradients;
- core/canonical: `StrictlyPositiveOn` together with the Chapter 3 affine-pullback owner
  `IsSubgradientAt.comp_affineMap`;
- bridge/view: the matrix specialization `y ↦ A y + b` from `Definition_7_82`, together with the
  transpose/adjoint identification from `Chap01/Proposition_1_4_5`.

Primitive data:
- the source-facing set `Q`;
- the real-valued objective `f`;
- the affine map `g`, or in coordinates the matrix `A` and translation `b`.

Derived API:
- the affine-pullback inequality for explicit pulled-back subgradients;
- the source-facing matrix-and-translation specialization.

Source/core/bridge triage:
- source-facing: Lemma 7.16's inequality for the affine pullback against pulled-back
  subgradients;
- core/canonical: `StrictlyPositiveOn` and `IsSubgradientAt.comp_affineMap`;
- bridge/view: the matrix specialization of the affine map, the affine preimage `Q_y`, and the
  transpose-adjoint identity.
-/

section AffinePullback

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

namespace StrictlyPositiveOn

/-- Lemma 7.16, affine form: for an explicit whole-space subgradient
`h ∈ ∂[Set.univ] f(g x)`, the
strict-positivity inequality for the affine pullback holds with the pulled-back vector
`g.linear.adjoint h`. -/
theorem inequality_comp_affineMap_image_adjoint
    {Qx : Set F} {f : F → ℝ}
    (hf : StrictlyPositiveOn Qx f) (g : E →ᵃ[ℝ] F)
    {x y : E}
    (hx : x ∈ g ⁻¹' Qx) (hy : y ∈ g ⁻¹' Qx)
    {h : F} (hh : h ∈ ∂[Set.univ] f((g x))) :
    0 ≤ f (g y) + f (g x) + inner ℝ (g.linear.adjoint h) (y - x) := by
  have hineq := hf.inequality hx hy hh
  have hgsub : g y - g x = g.linear (y - x) := by
    simpa using (g.linearMap_vsub y x).symm
  have hinner : inner ℝ h (g y - g x) = inner ℝ (g.linear.adjoint h) (y - x) := by
    rw [hgsub, ← g.linear.adjoint_inner_left]
  simpa [Function.comp, hinner] using hineq

end StrictlyPositiveOn

end AffinePullback

section MatrixSpecialization

variable {n m : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Em" => EuclideanSpace ℝ (Fin m)

open Matrix

namespace StrictlyPositiveOn

/-- Lemma 7.16, matrix specialization: for an explicit whole-space subgradient
`g ∈ ∂[Set.univ] f(A x + b)`, the
strict-positivity inequality for the affine pullback holds with the pulled-back vector `Aᵀ g`. -/
theorem inequality_comp_linearMap_add_image_adjoint
    {Qx : Set En} {f : En → ℝ}
    (hf : StrictlyPositiveOn Qx f)
    (A : Matrix (Fin n) (Fin m) ℝ) (b : En)
    {x y : Em}
    (hx : A.toEuclideanLin x + b ∈ Qx)
    (hy : A.toEuclideanLin y + b ∈ Qx)
    {g : En} (hg : g ∈ ∂[Set.univ] f((A.toEuclideanLin x + b))) :
    0 ≤
      f (A.toEuclideanLin y + b) + f (A.toEuclideanLin x + b) +
        inner ℝ (Aᵀ.toEuclideanLin g) (y - x) := by
  have hx' : x ∈ ((A.toEuclideanLin.toAffineMap +ᵥ AffineMap.const ℝ Em b) ⁻¹' Qx) := by
    rwa [mem_preimage_linearMap_add_iff]
  have hy' : y ∈ ((A.toEuclideanLin.toAffineMap +ᵥ AffineMap.const ℝ Em b) ⁻¹' Qx) := by
    rwa [mem_preimage_linearMap_add_iff]
  have hadjoint : A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  simpa [hadjoint] using
    hf.inequality_comp_affineMap_image_adjoint
      (A.toEuclideanLin.toAffineMap +ᵥ AffineMap.const ℝ Em b) hx' hy' hg

end StrictlyPositiveOn

end MatrixSpecialization

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_62
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_4_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped EllipsoidNotation RealInnerProductSpace RealSymmetricMatrixSpace

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 5.4.5.4 lies in the symmetric-positive-definite ellipsoid / constrained-minimization
domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.coe_apply` in
  `Chap01/Definition_1_3_3`, the project owner and evaluation view for constrained minimization
  problems;
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` in `Chap03/Definition_3_3`, the
  chapter owner/view for epigraph feasible sets built from primitive base constraints and an
  objective;
* `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Chap03/Definition_3_62`, the project
  owner/view for the half-space intersection cut out by `⟪aᵢ, x⟫ ≤ bᵢ`;
* `affineEllipsoid`, the notation `E(H, v)`, and `center_mem_affineEllipsoid` in
  `Chap03/Lemma_3_2_7`, the chapter owner/view for the ellipsoid centered at `v`;
* `𝕊^n₊₊` in `Definition_5_4_4_5`, the intrinsic strict-cone owner for positive-definite shape
  matrices;
* `affine_le_on_affineEllipsoid_iff` in `Lemma_5_4_5_1`, the chapter bridge from ellipsoid
  containment in one half-space to the quadratic inequality plus the center-slack sign condition.

Best owner abstraction:
* source-facing: the circumscribed-ellipsoid shape set on `H : 𝕊^n₊₊`, expressed by the textbook
  quadratic inequalities `⟪H aᵢ, aᵢ⟫ ≤ (bᵢ - ⟪aᵢ, v⟫)^2`, together with its epigraph
  reformulation in the variables `(H, τ)`;
* core/canonical: `constrainedEpigraph` over the primitive shape set and the owner
  `SetConstrainedMinimizationProblem (𝕊^n₊₊ × ℝ)`;
* bridge/view: the objective-evaluation lemma together with the containment bridge theorems below,
  which compare the source-facing quadratic owner to the geometric condition
  `E(H, v) ⊆ innerLePolyhedron a b` under the explicit center-slack hypotheses needed by
  `affine_le_on_affineEllipsoid_iff`.

Primitive data:
* the half-space data `a`, `b`, the center `v`, and the quadratic inequalities on `𝕊^n₊₊`.

Derived API:
* the epigraph feasible set built by `constrainedEpigraph`;
* the packaged optimization problem with objective `Prod.snd`;
* the bridge lemmas identifying its objective and relating the quadratic constraints to geometric
  containment when the center satisfies the half-space inequalities.

This file therefore keeps the source-facing quadratic feasible set on the intrinsic strict-cone
owner `𝕊^n₊₊`, and treats geometric containment only as a companion bridge under the explicit
center-slack assumptions from Lemma `5.4.5.1`.
-/

/-- The primitive shape set of the circumscribed-ellipsoid reformulation consists of
positive-definite shapes `H : 𝕊ⁿ₊₊` satisfying the textbook quadratic constraints
`⟪H aᵢ, aᵢ⟫ ≤ (bᵢ - ⟪aᵢ, v⟫)^2`. -/
def circumscribedEllipsoidShapeSet
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) : Set 𝕊^n₊₊ :=
  {H | ∀ i : Fin m,
    ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
      (b i - ⟪a i, v⟫) ^ (2 : ℕ)}

/-- Membership in the primitive circumscribed-ellipsoid shape set is exactly the textbook
quadratic constraint family. -/
@[simp] theorem mem_circumscribedEllipsoidShapeSet_iff
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) :
    H ∈ circumscribedEllipsoidShapeSet a b v ↔
      ∀ i : Fin m,
        ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
          (b i - ⟪a i, v⟫) ^ (2 : ℕ) :=
  Iff.rfl

/-- Geometric containment of the ellipsoid `E(H, v)` in the half-space intersection
`innerLePolyhedron a b` implies the source-facing quadratic constraints. -/
theorem mem_circumscribedEllipsoidShapeSet_of_subset_innerLePolyhedron
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) :
    E(toMatrix H, v) ⊆ innerLePolyhedron a b →
      H ∈ circumscribedEllipsoidShapeSet a b v := by
  intro hsubset
  rw [mem_circumscribedEllipsoidShapeSet_iff]
  intro i
  have hhalfspace : ∀ x ∈ E(toMatrix H, v), ⟪a i, x⟫ ≤ b i := by
    intro x hx
    exact (mem_innerLePolyhedron_iff a b).1 (hsubset hx) i
  have hcenter : ⟪a i, v⟫ ≤ b i := by
    exact hhalfspace v (center_mem_affineEllipsoid (toMatrix H) v)
  have hslack : 0 ≤ b i - ⟪a i, v⟫ := sub_nonneg.mpr hcenter
  have hPosDef : (toMatrix H).PosDef := by
    simpa [toMatrix_def] using strictPositiveSemidefiniteCone_posDef H
  have hquad :
      ⟪a i, (toMatrix H).toEuclideanLin (a i)⟫ ≤
        (b i - ⟪a i, v⟫) ^ (2 : ℕ) :=
    (affine_le_on_affineEllipsoid_iff (a i) v (b i) (toMatrix H) hslack hPosDef).1 hhalfspace
  simpa [real_inner_comm] using hquad

/-- Under the explicit center-slack hypotheses `⟪aᵢ, v⟫ ≤ bᵢ`, the source-facing quadratic
constraints imply the geometric containment `E(H, v) ⊆ innerLePolyhedron a b`. -/
theorem subset_innerLePolyhedron_of_mem_circumscribedEllipsoidShapeSet
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊)
    (hcenter : ∀ i : Fin m, ⟪a i, v⟫ ≤ b i)
    (hH : H ∈ circumscribedEllipsoidShapeSet a b v) :
    E(toMatrix H, v) ⊆ innerLePolyhedron a b := by
  intro x hx
  rw [mem_innerLePolyhedron_iff]
  intro i
  have hslack : 0 ≤ b i - ⟪a i, v⟫ := sub_nonneg.mpr (hcenter i)
  have hPosDef : (toMatrix H).PosDef := by
    simpa [toMatrix_def] using strictPositiveSemidefiniteCone_posDef H
  have hquad :
      ⟪a i, (toMatrix H).toEuclideanLin (a i)⟫ ≤
        (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
    have hi := (mem_circumscribedEllipsoidShapeSet_iff a b v H).1 hH i
    simpa [real_inner_comm] using hi
  exact
    (affine_le_on_affineEllipsoid_iff (a i) v (b i) (toMatrix H) hslack hPosDef).2 hquad x hx

/-- Under the explicit center-slack hypotheses `⟪aᵢ, v⟫ ≤ bᵢ`, the source-facing quadratic
constraints are equivalent to geometric containment of the ellipsoid in the half-space
intersection. -/
theorem mem_circumscribedEllipsoidShapeSet_iff_subset_innerLePolyhedron
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊)
    (hcenter : ∀ i : Fin m, ⟪a i, v⟫ ≤ b i) :
    H ∈ circumscribedEllipsoidShapeSet a b v ↔
      E(toMatrix H, v) ⊆ innerLePolyhedron a b := by
  constructor
  · exact subset_innerLePolyhedron_of_mem_circumscribedEllipsoidShapeSet a b v H hcenter
  · exact mem_circumscribedEllipsoidShapeSet_of_subset_innerLePolyhedron a b v H

/-- Definition 5.4.5.4: the circumscribed-ellipsoid optimization problem minimizes the auxiliary
variable `τ` over pairs `(H, τ)` satisfying `H ∈ 𝕊ⁿ₊₊`, `logDetBarrier n H ≤ τ`, and the
textbook quadratic constraints
`⟪H aᵢ, aᵢ⟫ ≤ (bᵢ - ⟪aᵢ, v⟫)^2`. The geometric containment formulation is kept only as a bridge
under the explicit center-slack hypotheses. -/
def circumscribedEllipsoidOptimizationProblem
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) :
    SetConstrainedMinimizationProblem (𝕊^n₊₊ × ℝ) where
  feasibleSet := constrainedEpigraph
    (circumscribedEllipsoidShapeSet a b v)
    fun H ↦ (logDetBarrier n H : WithTop ℝ)
  objective := Prod.snd

/-- Evaluating the objective of the circumscribed-ellipsoid optimization problem returns the
auxiliary scalar variable `τ`. -/
@[simp] theorem circumscribedEllipsoidOptimizationProblem_objective_apply
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    circumscribedEllipsoidOptimizationProblem a b v (H, τ) = τ :=
  rfl

/-- Membership in the feasible set of the circumscribed-ellipsoid optimization problem is exactly
the conjunction of the chapter-owner determinant barrier and the textbook quadratic constraints,
with the strict cone condition absorbed into the ambient owner `𝕊ⁿ₊₊ × ℝ`. -/
@[simp] theorem mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    (H, τ) ∈ (circumscribedEllipsoidOptimizationProblem a b v).feasibleSet ↔
      logDetBarrier n H ≤ τ ∧
        ∀ i : Fin m,
          ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
            (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
  change (H, τ) ∈ constrainedEpigraph
      (circumscribedEllipsoidShapeSet a b v)
      (fun H ↦ (logDetBarrier n H : WithTop ℝ)) ↔
    logDetBarrier n H ≤ τ ∧
      ∀ i : Fin m,
        ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
          (b i - ⟪a i, v⟫) ^ (2 : ℕ)
  rw [mem_constrainedEpigraph_iff, mem_circumscribedEllipsoidShapeSet_iff]
  constructor
  · rintro ⟨hshape, hτ⟩
    exact ⟨by exact_mod_cast hτ, hshape⟩
  · rintro ⟨hτ, hshape⟩
    exact ⟨hshape, by exact_mod_cast hτ⟩

/-- Under the explicit center-slack hypotheses `⟪aᵢ, v⟫ ≤ bᵢ`, feasible points for the
circumscribed-ellipsoid optimization problem are exactly those satisfying the determinant bound
and the geometric containment `E(H, v) ⊆ innerLePolyhedron a b`. -/
theorem mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff_subset_innerLePolyhedron
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ)
    (hcenter : ∀ i : Fin m, ⟪a i, v⟫ ≤ b i) :
    (H, τ) ∈ (circumscribedEllipsoidOptimizationProblem a b v).feasibleSet ↔
      logDetBarrier n H ≤ τ ∧
        E(toMatrix H, v) ⊆ innerLePolyhedron a b := by
  rw [mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff]
  constructor
  · rintro ⟨hτ, hshape⟩
    exact
      ⟨hτ, subset_innerLePolyhedron_of_mem_circumscribedEllipsoidShapeSet a b v H hcenter hshape⟩
  · rintro ⟨hτ, hshape⟩
    exact ⟨hτ, mem_circumscribedEllipsoidShapeSet_of_subset_innerLePolyhedron a b v H hshape⟩

/-- Expanding the owner determinant barrier rewrites circumscribed-ellipsoid feasibility back to
the textbook `-log det` inequality together with the quadratic constraints. -/
theorem mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff_formula
    (a : Fin m → E) (b : Fin m → ℝ) (v : E) (H : 𝕊^n₊₊) (τ : ℝ) :
    (H, τ) ∈ (circumscribedEllipsoidOptimizationProblem a b v).feasibleSet ↔
      -Real.log (toMatrix H).det ≤ τ ∧
        ∀ i : Fin m,
          ⟪(toMatrix H).toEuclideanLin (a i), a i⟫ ≤
            (b i - ⟪a i, v⟫) ^ (2 : ℕ) := by
  rw [mem_circumscribedEllipsoidOptimizationProblem_feasibleSet_iff, logDetBarrier_apply]
  simp [toMatrix_def]

end

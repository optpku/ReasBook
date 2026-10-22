/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped ConstrainedArgmin
open scoped NormalCone
open scoped WithTopConvexAnalysis

/-
Proposition 3.23 lies in the chapter's equality-constrained convex-optimality / normal-cone
domain.

Relevant owner declarations sampled before refinement:
* `mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone` in `Theorem_3_1_24`, the chapter
  owner theorem for constrained convex optimality in normal-cone form
* `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical owner
  for feasible minimizers on a set
* `normalCone_linearLevelSet` in `Proposition_3_22`, the affine-level-set normal-cone formula
  `(N[{x | L x = b}] xStar : Set E) = L.adjoint.range`
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the matrix/linear-map bridge identifying
  `Aᵀ` with the adjoint of `A.toEuclideanLin`

Best owner abstraction:
* the affine level set `{x | L x = b}` together with the constrained-optimality owner theorem
  `mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone`

Primitive data:
* a convex objective `f : E → ℝ`
* a linear equality constraint `L x = b`
* a feasible base point `xStar`

Derived API:
* the affine-level-set specialization of the normal-cone optimality criterion
* the adjoint-range reformulation on finite-dimensional inner-product spaces
* the Euclidean matrix/transpose specialization `Aᵀ yStar ∈ ∂ f(xStar)`

Source/core/bridge triage:
* source-facing: Proposition 3.23's equality-constrained optimality criteria in normal-cone and
  transpose form
* core/canonical: `argmin[Q] f`, `mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone`,
  `N[Q] xStar`, and `normalCone_linearLevelSet`
* bridge/view: `mem_constrainedArgmin_iff`, `L.adjoint.range`, and the transpose/adjoint
  identification for matrices

The previous file exposed a conditional decomposition hypothesis for the constrained
subdifferential. That weakened the source-facing proposition into a bridge lemma. This refinement
instead specializes the existing chapter owner theorem for constrained convex optimality directly
to the affine set `{x | L x = b}`, and only then rewrites the resulting normal-cone certificate
through the canonical affine normal-cone formula and the matrix transpose/adjoint bridge.
-/

section

variable {E Λ : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]

/-- Proposition 3.23, affine normal-cone form: for a convex objective on a real inner-product
space, a feasible point minimizes `f` on the affine level set `{x | L x = b}` exactly when some
subgradient at that point lies in the normal cone of the level set. -/
theorem isMinOn_linearLevelSet_iff_exists_subgradient_mem_normalCone
    [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    (L : E →ₗ[ℝ] Λ) (b : Λ) {xStar : E}
    (hxStar : L xStar = b) :
    IsMinOn f {x | L x = b} xStar ↔
      ∃ gStar : E,
        gStar ∈ ∂ (fun x : E ↦ (f x : WithTop ℝ))(xStar) ∧
          gStar ∈ N[{x | L x = b}] xStar := by
  let Q : Set E := {x | L x = b}
  have hxQ : xStar ∈ Q := by
    simpa [Q] using hxStar
  have hQ_convex : Convex ℝ Q := by
    simpa [Q] using (convex_singleton b).linear_preimage L
  have howner :
      xStar ∈ argmin[Q] f ↔
        ∃ gStar : E,
          gStar ∈ ∂ (fun x : E ↦ (f x : WithTop ℝ))(xStar) ∧
            gStar ∈ N[Q] xStar :=
    mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone
      hQ_convex hf_conv hxQ
  rw [mem_constrainedArgmin_iff] at howner
  constructor
  · intro hxMin
    exact howner.mp ⟨hxQ, hxMin⟩
  · intro hcert
    exact (howner.mpr hcert).2

end

section

variable {E Λ : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]

/-- Proposition 3.23, affine adjoint-range form: on a finite-dimensional affine level set
`{x | L x = b}`, optimality is equivalent to the existence of a subgradient in the adjoint range
`range Lᵀ`. -/
theorem isMinOn_linearLevelSet_iff_exists_adjoint_subgradient
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ Λ]
    {f : E → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    (L : E →ₗ[ℝ] Λ) (b : Λ) {xStar : E}
    (hxStar : L xStar = b) :
    IsMinOn f {x | L x = b} xStar ↔
      ∃ yStar : Λ, L.adjoint yStar ∈ ∂ (fun x : E ↦ (f x : WithTop ℝ))(xStar) := by
  have hnormal :
      (N[{x : E | L x = b}] xStar : Set E) = L.adjoint.range :=
    normalCone_linearLevelSet L b hxStar
  rw [isMinOn_linearLevelSet_iff_exists_subgradient_mem_normalCone
      hf_conv L b hxStar]
  constructor
  · rintro ⟨gStar, hgStar, hgNormal⟩
    have hgRange : gStar ∈ L.adjoint.range := by
      change gStar ∈ ((N[{x : E | L x = b}] xStar : Set E)) at hgNormal
      rw [hnormal] at hgNormal
      exact hgNormal
    rcases Set.mem_range.mp hgRange with ⟨yStar, hyStar⟩
    exact ⟨yStar, hyStar.symm ▸ hgStar⟩
  · rintro ⟨yStar, hyStar⟩
    have hyNormal : L.adjoint yStar ∈ N[{x : E | L x = b}] xStar := by
      have hyRange : L.adjoint yStar ∈ L.adjoint.range := ⟨yStar, rfl⟩
      change L.adjoint yStar ∈ (N[{x : E | L x = b}] xStar : Set E)
      rw [hnormal]
      exact hyRange
    exact ⟨L.adjoint yStar, hyStar, hyNormal⟩

end

section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/-- Proposition 3.23, textbook matrix form: on the affine level set `{x | A x = b}`, a feasible
point minimizes `f` exactly when some transpose image `Aᵀ yStar` belongs to `∂ f(xStar)`. -/
theorem isMinOn_matrix_linearLevelSet_iff_exists_transpose_subgradient
    {f : Eₙ → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Eₘ) {xStar : Eₙ}
    (hxStar : A.toEuclideanLin xStar = b) :
    IsMinOn f {x | A.toEuclideanLin x = b} xStar ↔
      ∃ yStar : Eₘ,
        Aᵀ.toEuclideanLin yStar ∈ ∂ (fun x : Eₙ ↦ (f x : WithTop ℝ))(xStar) := by
  have hAdj : A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin := by
    simpa using (toEuclideanLin_conjTranspose_eq_adjoint A).symm
  simpa [hAdj] using
    isMinOn_linearLevelSet_iff_exists_adjoint_subgradient
      hf_conv A.toEuclideanLin b hxStar

end

end

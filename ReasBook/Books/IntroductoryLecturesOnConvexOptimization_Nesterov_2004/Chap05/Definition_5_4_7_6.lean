/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped EuclideanSpaceLp

variable (n : ℕ)

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Definition 5.4.7.6 lies in the Chapter 5 finite-dimensional `ℓ_p` epigraph / lifted-cone
domain.

Sampled owner declarations:
* `EuclideanSpace.LpExponent` from `Chap03/Definition_3_7`, the project owner for admissible
  finite-dimensional `ℓ_p` exponents `1 ≤ p < ∞`;
* `EuclideanSpace.lpSeminorm` and its notation surface `‖z‖_[p]` from `Chap03/Definition_3_7`,
  the intrinsic `ℓ_p` owner on `EuclideanSpace ℝ (Fin n)`;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for epigraphs over a
  specified feasible set;
* `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the atomic membership bridge for
  that owner.

Best owner abstraction:
* the intrinsic epigraph
  `lpNormEpigraphCone n p : Set (ℝ × EuclideanSpace ℝ (Fin n))`
  built from `EuclideanSpace.lpSeminorm n p`.

Source/core/bridge triage:
* source-facing: `lpNormEpigraphCone n p`, the textbook epigraph cone written in the source order
  `(τ, z)`;
* core/canonical: `constrainedEpigraph Set.univ (fun z : Eₙ ↦ (‖z‖_[p] : WithTop ℝ))`, the
  chapter epigraph owner for the intrinsic `ℓ_p` seminorm;
* bridge/view: the permutation `Prod.swap`, plus the coordinate realization through
  `EuclideanSpace.equiv (Fin n) ℝ`.

Primitive data:
* the admissible exponent `p : EuclideanSpace.LpExponent`;
* the vector `z : EuclideanSpace ℝ (Fin n)`;
* the epigraph height `τ : ℝ`.

Derived API:
* the source-facing owner `lpNormEpigraphCone n p`;
* the intrinsic membership theorem `mem_lpNormEpigraphCone_iff`;
* the coordinate bridge `mem_lpNormEpigraphCone_coord_iff`.

This refinement removes the old coordinate-level owner on `Fin n → ℝ` and makes the intrinsic
Chapter 3 `ℓ_p` seminorm the public core. The raw coordinate presentation survives only as a
bridge theorem, not as a second owner. -/

/-- Definition 5.4.7.6: the epigraph cone of the finite-dimensional `ℓ_p` norm is the set of
pairs `(τ, z)` with `τ ≥ ‖z‖_[p]`, implemented as the chapter constrained epigraph of the
canonical Chapter 3 owner `EuclideanSpace.lpSeminorm n p`, read in the source order `(τ, z)`. -/
def lpNormEpigraphCone (p : EuclideanSpace.LpExponent) : Set (ℝ × Eₙ) :=
  Prod.swap ⁻¹' constrainedEpigraph Set.univ (fun z : Eₙ ↦ (‖z‖_[p] : WithTop ℝ))

/-- Membership in `lpNormEpigraphCone n p` is exactly the intrinsic epigraph inequality
`‖z‖_[p] ≤ τ`. -/
@[simp] theorem mem_lpNormEpigraphCone_iff
    {p : EuclideanSpace.LpExponent} {τ : ℝ} {z : Eₙ} :
    (τ, z) ∈ lpNormEpigraphCone n p ↔ ‖z‖_[p] ≤ τ := by
  change
    ((z, τ) : Eₙ × ℝ) ∈
        constrainedEpigraph Set.univ (fun w : Eₙ ↦ (‖w‖_[p] : WithTop ℝ)) ↔
      ‖z‖_[p] ≤ τ
  rw [mem_constrainedEpigraph_iff]
  simp

/-- Reading the intrinsic epigraph owner through the canonical coordinate identification
`EuclideanSpace.equiv (Fin n) ℝ` recovers the original coordinate inequality
`‖WithLp.toLp p z‖ ≤ τ`. -/
theorem mem_lpNormEpigraphCone_coord_iff
    (p : EuclideanSpace.LpExponent) {τ : ℝ} {z : Fin n → ℝ} :
    (τ, (EuclideanSpace.equiv (Fin n) ℝ).symm z) ∈ lpNormEpigraphCone n p ↔
      ‖WithLp.toLp (p : ENNReal) z‖ ≤ τ := by
  rw [mem_lpNormEpigraphCone_iff, EuclideanSpace.lpNorm_eq_sum]
  rw [PiLp.norm_eq_sum p.toReal_pos (WithLp.toLp (p : ENNReal) z)]
  simp [EuclideanSpace.equiv, Real.norm_eq_abs]

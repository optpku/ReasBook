/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 4.4.15 lies in the nonlinear-equation / distance-to-solution-set domain.

Sampled owner-style declarations:
* `SmoothNonlinearEquationProblem.solutionSet` in `Definition_4_4_8`, the chapter owner for
  exact solutions of a nonlinear system;
* `𝓛[f](τ)` and `mem_levelSet_iff` in `Definition_4_4_14`, the recalled owner for sublevel sets;
* `IsLeast` in mathlib, the canonical order-theoretic owner for an attained minimum;
* `Metric.isGLB_infDist` and `IsClosed.exists_infDist_eq_dist`, the metric bridge lemmas relating
  an attained minimum to the canonical infimum distance.

Best owner abstraction:
* source-facing: the exact-solution sublevel set through `x₀` and the attained-distance set
  attached to an arbitrary residual map;
* core/canonical: `solutionSet`, `𝓛[f](f x₀)`, and `IsLeast`;
* bridge/view: the comparison with `Metric.infDist x₀ (...)`, and the later specialization to
  bundled smooth maps used by the modified Gauss--Newton development.

Primitive data:
* a residual map `problem`;
* a real-valued function `f`;
* a base point `x₀`.

Derived API:
* the set of exact solutions lying in `𝓛[f](f x₀)`;
* the distance image set realized on that solution set;
* the source-facing minimum statement `IsLeast (solutionSublevelDistanceSet problem f x₀) D`;
* companion bridges to `Metric.infDist`.
-/

open SmoothNonlinearEquationProblem
open scoped LevelSetNotation

variable {E₁ : Type u} {E₂ : Type v} [Zero E₂]

/-- The exact solutions of `problem` that lie in the sublevel set `𝓛[f](f x₀)`. -/
def solutionSublevelSet
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) (x0 : E₁) : Set E₁ :=
  𝓛[f]((f x0)) ∩ solutionSet problem

/-- Membership in `solutionSublevelSet problem f x₀` means belonging to `𝓛[f](f x₀)` and solving
the equation `problem x = 0`. -/
@[simp] theorem mem_solutionSublevelSet_iff
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) (x0 x : E₁) :
    x ∈ solutionSublevelSet problem f x0 ↔ x ∈ 𝓛[f]((f x0)) ∧ problem x = 0 := by
  simp [solutionSublevelSet]

/-- For a merit reformulation `x ↦ φ (problem x)`, every exact solution already lies in the
sublevel set through `x₀`, so `solutionSublevelSet` reduces to `solutionSet`. -/
theorem solutionSublevelSet_eq_solutionSet_of_meritFunctionReformulation
    (problem : E₁ → E₂)
    (φ : E₂ → ℝ) [IsMeritFunction φ]
    (x0 : E₁) :
    solutionSublevelSet problem (meritFunctionReformulation problem φ) x0 =
      solutionSet problem := by
  ext x
  constructor
  · intro hx
    have hmem :=
      (mem_solutionSublevelSet_iff problem (meritFunctionReformulation problem φ) x0 x).1 hx
    exact hmem.2
  · intro hx
    refine
      (mem_solutionSublevelSet_iff problem (meritFunctionReformulation problem φ) x0 x).2 ?_
    refine ⟨?_, hx⟩
    rw [mem_levelSet_iff]
    have hxzero : meritFunctionReformulation problem φ x = 0 := by
      simpa [meritFunctionReformulation] using
        (IsMeritFunction.eq_zero_iff (problem x)).2 hx
    exact hxzero.le.trans (IsMeritFunction.nonneg (problem x0))

section

variable [NormedAddCommGroup E₁]

/-- The set of distances from `x₀` attained by exact solutions in the sublevel set
`𝓛[f](f x₀)`. -/
def solutionSublevelDistanceSet
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) (x0 : E₁) : Set ℝ :=
  (fun x : E₁ ↦ ‖x - x0‖) '' solutionSublevelSet problem f x0

/-- Membership in `solutionSublevelDistanceSet problem f x₀` means that the radius is realized by
an exact solution lying in `𝓛[f](f x₀)`. -/
@[simp] theorem mem_solutionSublevelDistanceSet_iff
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) {x0 : E₁} {r : ℝ} :
    r ∈ solutionSublevelDistanceSet problem f x0 ↔
      ∃ x : E₁, x ∈ 𝓛[f]((f x0)) ∧ problem x = 0 ∧ ‖x - x0‖ = r := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (mem_solutionSublevelSet_iff problem f x0 x).1 hx with ⟨hxlevel, hxsol⟩
    exact ⟨x, hxlevel, hxsol, rfl⟩
  · rintro ⟨x, hxlevel, hxsol, hdist⟩
    exact ⟨x, (mem_solutionSublevelSet_iff problem f x0 x).2 ⟨hxlevel, hxsol⟩, hdist⟩

/-- For a merit reformulation, the source-facing attained-distance owner from Definition 4.4.15
agrees with the direct distance image of the exact solution set. -/
theorem solutionSublevelDistanceSet_eq_image_solutionSet_of_meritFunctionReformulation
    (problem : E₁ → E₂)
    (φ : E₂ → ℝ) [IsMeritFunction φ]
    (x0 : E₁) :
    solutionSublevelDistanceSet problem (meritFunctionReformulation problem φ) x0 =
      (fun y : E₁ ↦ ‖y - x0‖) '' solutionSet problem := by
  simp [solutionSublevelDistanceSet,
    solutionSublevelSet_eq_solutionSet_of_meritFunctionReformulation]

/-- An attained minimum distance on `solutionSublevelDistanceSet problem f x₀` agrees with the
canonical infimum distance to `solutionSublevelSet problem f x₀`. -/
theorem infDist_eq_of_isLeast_solutionSublevelDistanceSet
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) {x0 : E₁} {D : ℝ}
    (hD : IsLeast (solutionSublevelDistanceSet problem f x0) D) :
    Metric.infDist x0 (solutionSublevelSet problem f x0) = D := by
  rcases hD.1 with ⟨y, hy, hyD⟩
  have hs : (solutionSublevelSet problem f x0).Nonempty := ⟨y, hy⟩
  have hglb :
      IsGLB ((fun z : E₁ ↦ dist x0 z) '' solutionSublevelSet problem f x0) D := by
    simpa [solutionSublevelDistanceSet, dist_eq_norm, norm_sub_rev] using hD.isGLB
  exact (Metric.isGLB_infDist hs).unique hglb

/-- If the exact-solution sublevel set is closed and nonempty in a proper space, then the metric
infimum distance is attained there, hence it is the least element of
`solutionSublevelDistanceSet problem f x₀`. -/
theorem isLeast_solutionSublevelDistanceSet_infDist
    [ProperSpace E₁]
    (problem : E₁ → E₂)
    (f : E₁ → ℝ) {x0 : E₁}
    (hclosed : IsClosed (solutionSublevelSet problem f x0))
    (hsol : (solutionSublevelSet problem f x0).Nonempty) :
    IsLeast (solutionSublevelDistanceSet problem f x0)
      (Metric.infDist x0 (solutionSublevelSet problem f x0)) := by
  obtain ⟨y, hy, hyD⟩ := hclosed.exists_infDist_eq_dist hsol x0
  refine ⟨?_, ?_⟩
  · refine ⟨y, hy, ?_⟩
    simpa [solutionSublevelDistanceSet, dist_eq_norm, norm_sub_rev] using hyD.symm
  · intro r hr
    rcases hr with ⟨z, hz, rfl⟩
    have hdist : Metric.infDist x0 (solutionSublevelSet problem f x0) ≤ dist x0 z :=
      Metric.infDist_le_dist_of_mem hz
    simpa [solutionSublevelDistanceSet, dist_eq_norm, norm_sub_rev] using
      hdist

section

variable (problem : E₁ → E₂) (f : E₁ → ℝ) (x0 : E₁) (D : ℝ)

/- Definition 4.4.15: the textbook quantity
`min {‖x - x₀‖ : x ∈ 𝓛[f](f x₀), problem x = 0}`
is the attained-minimum statement
`IsLeast (solutionSublevelDistanceSet problem f x₀) D`.
The always-defined metric infimum `Metric.infDist x₀ (solutionSublevelSet problem f x₀)` appears
only as a companion bridge under additional hypotheses. -/
set_option linter.hashCommand false in
#check IsLeast (solutionSublevelDistanceSet problem f x0) D

end

end

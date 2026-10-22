/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u

variable {X : Type u}

/- Definition 4.1.8 lies in the constrained global-minimization / quadratic error-bound domain on
feasible subsets of a pseudo-metric ambient space. The textbook statement on `ℝⁿ` is the
specialization to `X = EuclideanSpace ℝ (Fin n)`.

Sampled owner-style declarations:
* `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project
  owner for minimizer sets of an ambient objective on an explicit feasible set;
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the Chapter 1 owner for the
  primitive constrained-optimization data `(F, f)`;
* `StarConvexFunction` in `Chap04/Definition_4_1_7`, which keeps source-facing optimization data
  while exposing minimizers through `argmin[Set.univ] f`;
* `GradientDominatedOn` in `Chap04/Definition_4_1_9`, which is likewise organized around an
  ambient objective `f : X → ℝ` on an explicit feasible set `F`.

Best owner abstraction:
* the ambient constrained data `F : Set X` and `f : X → ℝ`;
* the canonical optimal set `argmin[F] f`;
* the canonical distance-to-optimal-set term `Metric.infDist x (argmin[F] f)`;
* the source-facing error-bound property `HasGloballyNondegenerateOptimalSet F f`.

Primitive data:
* a pseudo-metric ambient type `X`;
* a feasible set `F : Set X`;
* a real-valued ambient objective `f : X → ℝ`;
* nonemptiness of `argmin[F] f`;
* the quadratic error bound relative to `argmin[F] f`.

Derived API:
* pointwise membership in `argmin[F] f` via `mem_constrainedArgmin_iff`;
* distance-to-optimal-set expressions via `Metric.infDist`.
* the witness package `HasGloballyNondegenerateOptimalSet.UsesConstant F f xStar μ`;
* transport of an owner-level error-bound constant to any canonical minimizer in `argmin[F] f`.

Source/core/bridge triage:
* source-facing: `HasGloballyNondegenerateOptimalSet`;
* core/canonical: `argmin[F] f`, `IsMinOn f F x`, and `Metric.infDist`;
* bridge/view: `HasGloballyNondegenerateOptimalSet.UsesConstant`,
  `HasGloballyNondegenerateOptimalSet.exists_usesConstant_of_mem_argmin`, and the standard
  simplification route `mem_constrainedArgmin_iff`.

This refinement keeps the source-facing nondegeneracy property, but moves it onto the ambient
constrained owner layer used elsewhere in the project instead of packaging the objective on the
feasible subtype.
-/

namespace HasGloballyNondegenerateOptimalSet

/-- `UsesConstant F f xStar μ` packages the canonical `argmin` membership of `xStar` together with
the positive error-bound constant `μ` used in the source-facing quadratic growth inequality. -/
def UsesConstant [PseudoMetricSpace X] (F : Set X) (f : X → ℝ) (xStar : X) (μ : ℝ) : Prop :=
  xStar ∈ argmin[F] f ∧ 0 < μ ∧
    ∀ ⦃x : X⦄, x ∈ F →
      f x - f xStar ≥
        (μ / 2) * (Metric.infDist x (argmin[F] f)) ^ (2 : ℕ)

end HasGloballyNondegenerateOptimalSet

/-- Definition 4.1.8: a real-valued function `f` on a feasible set `F ⊆ X` has a globally
non-degenerate optimal set if `argmin[F] f` is nonempty and there exists a constant `μ > 0` such
that, for every feasible point `x ∈ F`, the objective gap above the constrained optimal value
`sInf (f '' F)` is bounded below by `(μ / 2)` times the squared distance from `x` to
`argmin[F] f`. The textbook `ℝⁿ` version is the specialization to
`X = EuclideanSpace ℝ (Fin n)`. -/
class HasGloballyNondegenerateOptimalSet [PseudoMetricSpace X] (F : Set X) (f : X → ℝ) : Prop where
  /-- The optimal set `argmin[F] f` is nonempty. -/
  optimalSet_nonempty : (argmin[F] f).Nonempty
  /-- The objective gap dominates the squared distance to the optimal set with a positive
  error-bound constant. -/
  exists_error_bound :
    ∃ μ : ℝ, 0 < μ ∧ ∀ ⦃x : X⦄, x ∈ F →
      f x - sInf (f '' F) ≥
        (μ / 2) * (Metric.infDist x (argmin[F] f)) ^ (2 : ℕ)

namespace HasGloballyNondegenerateOptimalSet

variable [PseudoMetricSpace X] {F : Set X} {f : X → ℝ}

theorem UsesConstant.mem_argmin
    {xStar : X} {μ : ℝ}
    (hμ : UsesConstant F f xStar μ) :
    xStar ∈ argmin[F] f :=
  hμ.1

theorem UsesConstant.pos
    {xStar : X} {μ : ℝ}
    (hμ : UsesConstant F f xStar μ) :
    0 < μ :=
  hμ.2.1

theorem UsesConstant.bound
    {xStar : X} {μ : ℝ}
    (hμ : UsesConstant F f xStar μ) {x : X} (hx : x ∈ F) :
    f x - f xStar ≥
      (μ / 2) * (Metric.infDist x (argmin[F] f)) ^ (2 : ℕ) :=
  hμ.2.2 hx

/-- Any point of the canonical minimizer set can be paired with some positive quadratic
error-bound constant. -/
theorem exists_usesConstant_of_mem_argmin
    (hf : HasGloballyNondegenerateOptimalSet F f) {xStar : X} (hxStar : xStar ∈ argmin[F] f) :
    ∃ μ, UsesConstant F f xStar μ := by
  rcases hf.exists_error_bound with ⟨μ, hμ, hbound⟩
  have hxStar_mem : xStar ∈ argmin[F] f := hxStar
  rw [mem_constrainedArgmin_iff] at hxStar
  have hxStar_glb : IsGLB (f '' F) (f xStar) := by
    simpa using hxStar.2.isGLB hxStar.1
  have hxStar_val : sInf (f '' F) = f xStar := by
    exact hxStar_glb.csInf_eq ⟨f xStar, ⟨xStar, hxStar.1, rfl⟩⟩
  refine ⟨μ, hxStar_mem, hμ, ?_⟩
  intro x hx
  simpa [hxStar_val] using hbound hx

end HasGloballyNondegenerateOptimalSet

/-- A constant objective on a nonempty feasible set has a globally non-degenerate optimal set. -/
theorem hasGloballyNondegenerateOptimalSet_const [PseudoMetricSpace X]
    {F : Set X} (hF : F.Nonempty) (c : ℝ) :
    HasGloballyNondegenerateOptimalSet F (fun _ : X ↦ c) := by
  have hargmin : argmin[F] (fun _ : X ↦ c) = F := by
    ext x
    rw [mem_constrainedArgmin_iff]
    simp [isMinOn_iff]
  have himage : (fun _ : X ↦ c) '' F = ({c} : Set ℝ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp
    · intro hy
      rcases hF with ⟨x, hx⟩
      refine ⟨x, hx, ?_⟩
      simpa [Set.mem_singleton_iff] using hy.symm
  have hsInf : sInf ((fun _ : X ↦ c) '' F) = c := by
    rw [himage]
    simp
  refine ⟨?_, ?_⟩
  · rcases hF with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hargmin]
    exact hx
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    rw [hsInf, sub_self, hargmin, Metric.infDist_zero_of_mem hx]
    norm_num

end

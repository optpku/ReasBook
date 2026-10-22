/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise TangentCone Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 3.19 is a source-facing specialization in the chapter's first-order optimality /
tangent-cone domain.

Primary domain:
- directional derivatives and tangent-cone optimality conditions for convex feasible sets in
  real normed spaces.

Relevant owner-style declarations sampled before refinement:
- `posTangentConeAt`
- `𝒯[Q] xStar` from `Definition_3_23`, the chapter's source-facing tangent-cone surface
- `lineDerivWithin`
- `LineDifferentiableWithinAt`
- `IsMinOn.localize`
- `IsPositivelyHomogeneousOn`
- `directionalDerivative_nonneg_on_posTangentCone_of_isLocalMinOn`

Best owner abstraction:
- the chapter theorem `directionalDerivative_nonneg_on_posTangentCone_of_isLocalMinOn`, whose
  ambient owner objects are `IsLocalMinOn`, `posTangentConeAt`, and `lineDerivWithin`

Primitive data:
- the feasible set `Q`
- the objective `f`
- the minimizer `xStar`
- continuity of `lineDerivWithin ℝ f Q xStar`
- the positive-homogeneity owner witness
  `IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar)`
- the directionwise existence owner witnesses `LineDifferentiableWithinAt ℝ f Q xStar d`

Derived API:
- nonnegativity of `lineDerivWithin ℝ f Q xStar` on `𝒯[Q] xStar`

Source/core/bridge triage:
- source-facing: the global constrained-optimum first-order consequence with hypothesis
  `IsMinOn f Q xStar`
- core/canonical: `IsLocalMinOn`, `posTangentConeAt`, and the owner theorem
  `directionalDerivative_nonneg_on_posTangentCone_of_isLocalMinOn`
- bridge/view: the standard global-to-local owner implication `IsMinOn.localize`, which yields the
  source-facing global specialization

The owner theorem file is not available as a compiled dependency in this item-per-file context, so
this file proves the same source-facing statement directly from the feasible-ray, cone-hull, and
closure steps used in the textbook argument. On this source-facing theorem surface, the tangent
cone is written in the chapter's established notation `𝒯[Q] xStar`. -/

/-- Helper for Lemma 3.19: any direction whose positive ray stays feasible near `xStar` has
nonnegative intrinsic line derivative at a global minimizer. -/
lemma line_deriv_within_nonneg_of_eventually_feasible
    {Q : Set E} {f : E → ℝ} {xStar d : E}
    (hmin : IsMinOn f Q xStar)
    (hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q)
    (hline : LineDifferentiableWithinAt ℝ f Q xStar d) :
    0 ≤ lineDerivWithin ℝ f Q xStar d := by
  let T : Set ℝ := ((fun t : ℝ ↦ xStar + t • d) ⁻¹' Q)
  let g : ℝ → ℝ := fun t ↦ f (xStar + t • d)
  have hminT : IsMinOn g T 0 := by
    -- Restrict the global minimum to the scalar slice through `xStar` in direction `d`.
    intro t ht
    simpa [T, g] using hmin ht
  have hone : (1 : ℝ) ∈ posTangentConeAt T (0 : ℝ) := by
    -- Eventual positive feasibility says that the right half-line direction belongs to the slice
    -- tangent cone at the origin.
    apply mem_posTangentConeAt_of_frequently_mem
    simpa [T] using hd.frequently
  have hderiv : HasDerivWithinAt g (lineDerivWithin ℝ f Q xStar d) T 0 := by
    -- The within-set line derivative is exactly the one-dimensional derivative of the slice.
    simpa [T, g, one_smul] using hline.hasLineDerivWithinAt
  -- Apply the one-sided Fermat rule on the scalar slice.
  simpa [hasDerivWithinAt_iff_hasFDerivWithinAt] using
    hminT.localize.hasFDerivWithinAt_nonneg hderiv.hasFDerivWithinAt hone

/-- Helper for Lemma 3.19: every feasible displacement from `xStar` has nonnegative intrinsic line
derivative. -/
lemma line_deriv_within_nonneg_on_feasible_displacements
    {Q : Set E} {f : E → ℝ} {xStar x : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsMinOn f Q xStar)
    (hline :
      ∀ d : E,
        (∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q) →
          LineDifferentiableWithinAt ℝ f Q xStar d)
    (hx : x ∈ Q) :
    0 ≤ lineDerivWithin ℝ f Q xStar (x - xStar) := by
  have h01 : (0 : ℝ) < 1 := by
    norm_num
  have hlt : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds h01)
  have hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • (x - xStar) ∈ Q := by
    -- Convexity keeps the whole segment from `xStar` to `x` feasible for `0 < β < 1`.
    filter_upwards [self_mem_nhdsWithin, hlt] with β hβpos hβlt
    have hseg : xStar + β • (x - xStar) ∈ segment ℝ xStar x := by
      rw [segment_eq_image']
      exact ⟨β, ⟨le_of_lt hβpos, le_of_lt hβlt⟩, rfl⟩
    exact hQ_convex.segment_subset hxStar hx hseg
  exact line_deriv_within_nonneg_of_eventually_feasible hmin hd (hline (x - xStar) hd)

/-- Helper for Lemma 3.19: nonnegativity on feasible displacements extends to the pointed cone hull
generated by `Q - xStar`. -/
lemma line_deriv_within_nonneg_on_pointed_cone_hull_vsub_singleton
    {Q : Set E} {f : E → ℝ} {xStar p : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsMinOn f Q xStar)
    (hline_hom : IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar))
    (hline :
      ∀ d : E,
        (∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q) →
          LineDifferentiableWithinAt ℝ f Q xStar d)
    (hp : p ∈ PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E))) :
    0 ≤ lineDerivWithin ℝ f Q xStar p := by
  let S : Set E := Q -ᵥ ({xStar} : Set E)
  have hS_convex : Convex ℝ S := by
    simpa [S, Set.vsub_singleton, vsub_eq_sub] using hQ_convex.sub (convex_singleton xStar)
  have hxSingleton : xStar ∈ ({xStar} : Set E) := by
    simp
  have hz : xStar -ᵥ xStar = (0 : E) := by
    simp [vsub_eq_sub]
  have hS_zero : (0 : E) ∈ S := by
    -- The zero displacement belongs to the displacement set because `xStar ∈ Q`.
    exact ⟨xStar, hxStar, xStar, hxSingleton, hz⟩
  have hconvexHull_pointed : (ConvexCone.hull ℝ S).Pointed :=
    ConvexCone.subset_hull hS_zero
  have hpointedHull_eq_convexHull : (PointedCone.hull ℝ S : Set E) = ConvexCone.hull ℝ S := by
    -- For a convex set containing `0`, the pointed hull agrees with the convex cone hull.
    ext v
    constructor
    · intro hv
      let C : PointedCone ℝ E := (ConvexCone.hull ℝ S).toPointedCone hconvexHull_pointed
      have hspan : PointedCone.hull ℝ S ≤ C := by
        refine Submodule.span_le.2 ?_
        intro y hy
        exact ConvexCone.subset_hull hy
      exact hspan hv
    · intro hv
      have hconvexHull_le : ConvexCone.hull ℝ S ≤ (PointedCone.hull ℝ S : ConvexCone ℝ E) := by
        exact ConvexCone.hull_min (fun y hy ↦ PointedCone.subset_hull hy)
      exact hconvexHull_le hv
  have hpS : p ∈ (PointedCone.hull ℝ S : Set E) := by
    simpa [S] using hp
  have hp' : p ∈ ConvexCone.hull ℝ S := by
    simpa [hpointedHull_eq_convexHull] using hpS
  rcases (ConvexCone.mem_hull_of_convex hS_convex).mp hp' with ⟨r, hr, y, hy, rfl⟩
  have hy' : y ∈ (fun z ↦ z - xStar) '' Q := by
    simpa [S, Set.vsub_singleton] using hy
  rcases hy' with ⟨x, hx, rfl⟩
  have hdisp :
      0 ≤ lineDerivWithin ℝ f Q xStar (x - xStar) :=
    line_deriv_within_nonneg_on_feasible_displacements hxStar hQ_convex hmin hline hx
  have hmap :
      lineDerivWithin ℝ f Q xStar (r • (x - xStar)) =
        r * lineDerivWithin ℝ f Q xStar (x - xStar) := by
    -- Positive homogeneity converts the displacement estimate into a conical estimate.
    simpa [Real.rpow_one, smul_eq_mul] using
      hline_hom.map_smul (by simp : x - xStar ∈ Set.univ) ⟨r, hr.le⟩
  rw [hmap]
  exact mul_nonneg hr.le hdisp

/-- Lemma 3.19: if `xStar` minimizes `f` on the convex feasible set `Q`, then the intrinsic
within-set directional-derivative map `lineDerivWithin ℝ f Q xStar` is nonnegative on the tangent
cone `𝒯[Q] xStar`. -/
theorem directionalDerivative_nonneg_on_posTangentCone_of_isMinOn
    {Q : Set E} {f : E → ℝ} {xStar : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsMinOn f Q xStar)
    (hline_cont : Continuous (lineDerivWithin ℝ f Q xStar))
    (hline_hom : IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar))
    (hline :
      ∀ d : E,
        (∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q) →
          LineDifferentiableWithinAt ℝ f Q xStar d)
    (p : E) (hp : p ∈ 𝒯[Q] xStar) :
    0 ≤ lineDerivWithin ℝ f Q xStar p := by
  -- Route correction: the unavailable compiled owner wrapper is replaced by the textbook proof
  -- route: feasible rays, then the pointed cone hull of feasible displacements, then closure.
  let C : Set E := {q : E | 0 ≤ lineDerivWithin ℝ f Q xStar q}
  have hclosed : IsClosed C := by
    -- Continuity of the derivative map makes the nonnegative half-space preimage closed.
    simpa [C] using isClosed_Ici.preimage hline_cont
  have hsubset :
      (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E) ⊆ C := by
    -- The cone-hull helper covers the dense generating cone of the tangent cone.
    intro q hq
    exact line_deriv_within_nonneg_on_pointed_cone_hull_vsub_singleton
      hxStar hQ_convex hmin hline_hom hline hq
  have hp' : p ∈ closure ((PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E)) := by
    -- Lemma 3.1.18 identifies the tangent cone with the closure of that pointed hull.
    rw [posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton Q hQ_convex xStar hxStar] at hp
    simpa using hp
  have hclosure : closure ((PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E)) ⊆ C := by
    exact hclosed.closure_subset_iff.2 hsubset
  exact hclosure hp'

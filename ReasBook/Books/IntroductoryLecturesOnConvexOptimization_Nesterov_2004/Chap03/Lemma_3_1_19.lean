/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 3.1.19 is the chapter owner theorem in the constrained directional-derivative /
tangent-cone optimality domain.

Primary domain:
- first-order necessary optimality conditions on convex feasible sets in real normed spaces,
  expressed through positive tangent cones and intrinsic within-set directional derivatives.

Relevant owner-style declarations sampled before refinement:
- mathlib `posTangentConeAt`, the ambient owner for feasible infinitesimal directions;
- mathlib `lineDerivWithin`, the intrinsic directional-derivative map on a constraint set;
- mathlib `LineDifferentiableWithinAt`, the owner predicate asserting existence of that
  directional derivative in a fixed direction;
- mathlib `HasLineDerivWithinAt`, the witness-level bridge recovered from
  `LineDifferentiableWithinAt`;
- chapter `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the owner predicate for the
  nonnegative scaling law satisfied by the intrinsic directional-derivative map.

Best owner abstraction:
- `posTangentConeAt Q xStar` for feasible directions;
- `lineDerivWithin ℝ f Q xStar : E → ℝ` for the directional-derivative object `p ↦ f'(xStar; p)`.

Primitive data:
- the feasible set `Q`, objective `f`, and local minimizer `xStar`;
- continuity of the intrinsic directional-derivative map `lineDerivWithin ℝ f Q xStar`;
- positive homogeneity of that intrinsic map;
- directionwise existence of the within-set directional derivative, expressed by
  `LineDifferentiableWithinAt`.

Derived API:
- nonnegativity of `lineDerivWithin ℝ f Q xStar` on `posTangentConeAt Q xStar`.

Source/core/bridge triage:
- source-facing: the textbook first-order necessary condition on the tangent cone;
- core/canonical: `posTangentConeAt` and `lineDerivWithin`;
- bridge/view: `LineDifferentiableWithinAt` together with the recovered witness
  `HasLineDerivWithinAt`.

This refinement removes the non-canonical auxiliary parameter `f' : E → ℝ` from the public API.
The theorem is now stated directly on the intrinsic owner `lineDerivWithin ℝ f Q xStar`, while
existence data remains in the bridge layer `LineDifferentiableWithinAt`.
-/

/-- Helper for Lemma 3.1.19: any direction whose positive ray stays feasible near `xStar` has
nonnegative intrinsic line derivative at a local minimizer. -/
lemma line_deriv_within_nonneg_of_eventually_feasible
    {Q : Set E} {f : E → ℝ} {xStar d : E}
    (hxStar : xStar ∈ Q)
    (hmin : IsLocalMinOn f Q xStar)
    (hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q)
    (hline : LineDifferentiableWithinAt ℝ f Q xStar d) :
    0 ≤ lineDerivWithin ℝ f Q xStar d := by
  let T : Set ℝ := ((fun t : ℝ ↦ xStar + t • d) ⁻¹' Q)
  let φ : ℝ → E := fun t ↦ xStar + t • d
  let g : ℝ → ℝ := fun t ↦ f (φ t)
  have hφ_cont : ContinuousOn φ T := by
    -- The line map is continuous on the scalar slice.
    simpa [φ] using (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  have hminT : IsLocalMinOn g T 0 := by
    -- Restrict the local minimum of `f` to the feasible scalar slice through `xStar`.
    have hminφ : IsLocalMinOn f Q (φ 0) := by
      simpa [φ] using hmin
    have hpre : T ⊆ φ ⁻¹' Q := by
      intro t ht
      simpa [T, φ] using ht
    have hzero : (0 : ℝ) ∈ T := by
      simpa [T, φ] using hxStar
    simpa [g] using hminφ.comp_continuousOn hpre hφ_cont hzero
  have hone : (1 : ℝ) ∈ posTangentConeAt T (0 : ℝ) := by
    -- Eventual positive feasibility places the rightward scalar direction in the slice tangent cone.
    apply mem_posTangentConeAt_of_frequently_mem
    simpa [T] using hd.frequently
  have hderiv : HasDerivWithinAt g (lineDerivWithin ℝ f Q xStar d) T 0 := by
    -- The intrinsic line derivative is the derivative of the one-dimensional slice.
    simpa [T, φ, g, one_smul] using hline.hasLineDerivWithinAt
  -- Apply the local Fermat rule on the scalar slice.
  simpa [hasDerivWithinAt_iff_hasFDerivWithinAt] using
    hminT.hasFDerivWithinAt_nonneg hderiv.hasFDerivWithinAt hone

/-- Helper for Lemma 3.1.19: every feasible displacement from `xStar` has nonnegative intrinsic
line derivative. -/
lemma line_deriv_within_nonneg_on_feasible_displacements
    {Q : Set E} {f : E → ℝ} {xStar x : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsLocalMinOn f Q xStar)
    (hline :
      ∀ (d : E) (_hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q),
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
  exact
    line_deriv_within_nonneg_of_eventually_feasible
      hxStar hmin hd (hline (x - xStar) hd)

/-- Helper for Lemma 3.1.19: nonnegativity on feasible displacements extends to the pointed cone
hull generated by `Q - xStar`. -/
lemma line_deriv_within_nonneg_on_pointed_cone_hull_vsub_singleton
    {Q : Set E} {f : E → ℝ} {xStar p : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsLocalMinOn f Q xStar)
    (hline_hom : IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar))
    (hline :
      ∀ (d : E) (_hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q),
        LineDifferentiableWithinAt ℝ f Q xStar d)
    (hp : p ∈ PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E))) :
    0 ≤ lineDerivWithin ℝ f Q xStar p := by
  let S : Set E := Q -ᵥ ({xStar} : Set E)
  have hS_convex : Convex ℝ S := by
    -- Translating a convex feasible set by `-xStar` preserves convexity.
    simpa [S, Set.vsub_singleton, vsub_eq_sub] using hQ_convex.sub (convex_singleton xStar)
  have hxSingleton : xStar ∈ ({xStar} : Set E) := by
    simp
  have hz : xStar -ᵥ xStar = (0 : E) := by
    simp [vsub_eq_sub]
  have hS_zero : (0 : E) ∈ S := by
    -- The zero displacement is feasible because `xStar` itself is feasible.
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

-- Proof sketch: for each feasible direction `d`, local optimality of `xStar` forces every
-- sufficiently small forward difference quotient of `f` along `d` to be nonnegative, so the
-- corresponding within-set directional derivative is nonnegative. Any tangent direction is a
-- limit of positive rescalings of such feasible displacements; positive homogeneity and
-- continuity of `lineDerivWithin ℝ f Q xStar` then pass the inequality to the limit.
/-- Lemma 3.1.19: if `xStar` is a local minimizer of `f` on `Q`, then the intrinsic constrained
directional-derivative map `lineDerivWithin ℝ f Q xStar` is nonnegative on the tangent cone
`posTangentConeAt Q xStar`. The textbook `ℝⁿ` statement is the specialization to
`E = EuclideanSpace ℝ (Fin n)`. -/
theorem directionalDerivative_nonneg_on_posTangentCone_of_isLocalMinOn
    {Q : Set E} {f : E → ℝ} {xStar : E}
    (hxStar : xStar ∈ Q) (hQ_convex : Convex ℝ Q) (hmin : IsLocalMinOn f Q xStar)
    (hline_cont : Continuous (lineDerivWithin ℝ f Q xStar))
    (hline_hom : IsPositivelyHomogeneousOn 1 Set.univ (lineDerivWithin ℝ f Q xStar))
    (hline :
      ∀ (d : E) (_hd : ∀ᶠ β : ℝ in 𝓝[>] (0 : ℝ), xStar + β • d ∈ Q),
        LineDifferentiableWithinAt ℝ f Q xStar d)
    (p : E) (hp : p ∈ posTangentConeAt Q xStar) :
    0 ≤ lineDerivWithin ℝ f Q xStar p := by
  let C : Set E := {q : E | 0 ≤ lineDerivWithin ℝ f Q xStar q}
  have hclosed : IsClosed C := by
    -- Continuity of the derivative map makes the nonnegative half-space preimage closed.
    simpa [C] using isClosed_Ici.preimage hline_cont
  have hsubset :
      (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E) ⊆ C := by
    -- The cone-hull helper covers the dense generating cone of the tangent cone.
    intro q hq
    exact
      line_deriv_within_nonneg_on_pointed_cone_hull_vsub_singleton
        hxStar hQ_convex hmin hline_hom hline hq
  have hp' : p ∈ closure ((PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E)) := by
    -- Lemma 3.1.18 identifies the tangent cone with the closure of that pointed hull.
    rw [posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton Q hQ_convex xStar hxStar] at hp
    simpa using hp
  have hclosure : closure ((PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E)) ⊆ C := by
    -- Closedness upgrades the cone-hull estimate to its closure.
    exact hclosed.closure_subset_iff.2 hsubset
  exact hclosure hp'

end

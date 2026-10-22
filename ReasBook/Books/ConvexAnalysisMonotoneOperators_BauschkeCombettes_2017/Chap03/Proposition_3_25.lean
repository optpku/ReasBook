/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

private abbrev spanClosure (C : Set 𝓗) : Submodule ℝ 𝓗 :=
  (Submodule.span ℝ C).topologicalClosure

private abbrev spanClosureSubset (C : Set 𝓗) : Set (spanClosure C) :=
  (Subtype.val : spanClosure C → 𝓗) ⁻¹' C

/-- Helper for Proposition 3.25: every point of `C` lies in the closed linear span of `C`. -/
private lemma mem_spanClosure_of_mem {C : Set 𝓗} {z : 𝓗} (hz : z ∈ C) :
    z ∈ spanClosure C := by
  -- Points of `C` lie in `closure C`, and that closure sits inside the closed span.
  exact Submodule.closure_subset_topologicalClosure_span C (subset_closure hz)

section MetricHelpers

variable {X : Type u} [MetricSpace X]

/-- Helper for Proposition 3.25: a point realizes `Metric.infDist` exactly when it is no farther
than every other point of the set. -/
private lemma dist_eq_infDist_iff_forall_dist_le {S : Set X} {x p : X} (hp : p ∈ S) :
    dist x p = Metric.infDist x S ↔ ∀ z ∈ S, dist x p ≤ dist x z := by
  refine ⟨?_, ?_⟩
  · intro h z hz
    -- Rewriting by the realized infimum turns the claim into the standard lower bound.
    rw [h]
    exact Metric.infDist_le_dist_of_mem hz
  · intro h
    -- The minimizing inequalities give both bounds on `Metric.infDist`.
    refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem hp)
    exact (Metric.le_infDist ⟨p, hp⟩).2 fun z hz ↦ h z hz

end MetricHelpers

section Complete

variable [CompleteSpace 𝓗]

/-- Helper for Proposition 3.25: for points in the closed span, the distance to `x` splits into
the distance to the orthogonal projection plus the fixed orthogonal residual. -/
private lemma dist_sq_eq_dist_sq_projection_add_residual_sq
    (C : Set 𝓗) {x z : 𝓗} (hz : z ∈ spanClosure C) :
    dist x z ^ 2 =
      dist ((spanClosure C).starProjection x) z ^ 2 +
        ‖x - (spanClosure C).starProjection x‖ ^ 2 := by
  have hpyth :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection (x - z) (spanClosure C)
  have hz' : (spanClosure C).starProjection z = z := by
    -- Projecting a vector already in the subspace does nothing.
    exact Submodule.starProjection_mem_subspace_eq_self ⟨z, hz⟩
  have horth : (spanClosure C)ᗮ.starProjection z = 0 := by
    -- The orthogonal-complement projection vanishes on the subspace itself.
    exact Submodule.starProjection_orthogonal_apply_eq_zero hz
  have hres :
      (spanClosure C)ᗮ.starProjection x = x - (spanClosure C).starProjection x := by
    -- The orthogonal component is the residual after subtracting the projection.
    simpa using
      (show (spanClosure C)ᗮ.starProjection x = x - (spanClosure C).starProjection x from
        Submodule.starProjection_orthogonal_val x)
  calc
    dist x z ^ 2 = ‖x - z‖ ^ 2 := by
      rw [dist_eq_norm]
    _ = ‖(spanClosure C).starProjection (x - z)‖ ^ 2 +
          ‖(spanClosure C)ᗮ.starProjection (x - z)‖ ^ 2 := hpyth
    _ = ‖(spanClosure C).starProjection x - z‖ ^ 2 +
          ‖(spanClosure C)ᗮ.starProjection x -
            (spanClosure C)ᗮ.starProjection z‖ ^ 2 := by
      rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub, hz']
    _ = ‖(spanClosure C)ᗮ.starProjection x - (spanClosure C)ᗮ.starProjection z‖ ^ 2 +
          ‖(spanClosure C).starProjection x - z‖ ^ 2 := by
      ring
    _ = ‖(spanClosure C)ᗮ.starProjection x‖ ^ 2 +
          ‖(spanClosure C).starProjection x - z‖ ^ 2 := by
      rw [horth, sub_zero]
    _ = ‖x - (spanClosure C).starProjection x‖ ^ 2 +
          dist ((spanClosure C).starProjection x) z ^ 2 := by
      rw [hres, dist_eq_norm]
    _ = dist ((spanClosure C).starProjection x) z ^ 2 +
          ‖x - (spanClosure C).starProjection x‖ ^ 2 := by
      ring

/-- Helper for Proposition 3.25: for points in the closed span, comparing their distances to `x`
is equivalent to comparing their distances to the projection of `x` onto the closed span. -/
private lemma projection_dist_le_iff
    (C : Set 𝓗) {x p z : 𝓗} (hp : p ∈ spanClosure C) (hz : z ∈ spanClosure C) :
    dist x p ≤ dist x z ↔
      dist ((spanClosure C).starProjection x) p ≤ dist ((spanClosure C).starProjection x) z := by
  have hpdecomp :
      dist x p ^ 2 =
        dist ((spanClosure C).starProjection x) p ^ 2 +
          ‖x - (spanClosure C).starProjection x‖ ^ 2 :=
    dist_sq_eq_dist_sq_projection_add_residual_sq C hp
  have hzdecomp :
      dist x z ^ 2 =
        dist ((spanClosure C).starProjection x) z ^ 2 +
          ‖x - (spanClosure C).starProjection x‖ ^ 2 :=
    dist_sq_eq_dist_sq_projection_add_residual_sq C hz
  have hxp_nonneg : 0 ≤ dist x p := dist_nonneg
  have hxz_nonneg : 0 ≤ dist x z := dist_nonneg
  have hpp_nonneg : 0 ≤ dist ((spanClosure C).starProjection x) p := dist_nonneg
  have hpz_nonneg : 0 ≤ dist ((spanClosure C).starProjection x) z := dist_nonneg
  constructor
  · intro h
    -- Squaring preserves the inequality because all distances are nonnegative.
    have hsquare : dist x p ^ 2 ≤ dist x z ^ 2 := by
      nlinarith
    have hprojSquare :
        dist ((spanClosure C).starProjection x) p ^ 2 ≤
          dist ((spanClosure C).starProjection x) z ^ 2 := by
      nlinarith [hpdecomp, hzdecomp, hsquare]
    nlinarith
  · intro h
    -- The same cancellation works in reverse because the residual term is identical.
    have hsquare :
        dist ((spanClosure C).starProjection x) p ^ 2 ≤
          dist ((spanClosure C).starProjection x) z ^ 2 := by
      nlinarith
    have hxSquare : dist x p ^ 2 ≤ dist x z ^ 2 := by
      nlinarith [hpdecomp, hzdecomp, hsquare]
    nlinarith

-- Helper for Proposition 3.25: realizing the distance to `C` in the ambient Hilbert space is
-- equivalent to realizing the distance to `C`, viewed inside its closed span.
omit [CompleteSpace 𝓗] in
private lemma dist_eq_infDist_spanClosureSubset_iff_ambient
    (C : Set 𝓗) {v p : spanClosure C} (hp : p ∈ spanClosureSubset C) :
    dist v p = Metric.infDist v (spanClosureSubset C) ↔
      dist (v : 𝓗) (p : 𝓗) = Metric.infDist (v : 𝓗) C := by
  constructor
  · intro h
    have hiff :
        dist v p = Metric.infDist v (spanClosureSubset C) ↔
          ∀ z ∈ spanClosureSubset C, dist v p ≤ dist v z :=
      dist_eq_infDist_iff_forall_dist_le hp
    have hmin : ∀ z ∈ spanClosureSubset C, dist v p ≤ dist v z :=
      hiff.mp h
    have hmin' : ∀ z ∈ C, dist (v : 𝓗) (p : 𝓗) ≤ dist (v : 𝓗) z := by
      -- Any ambient competitor in `C` becomes a subtype competitor in the closed span.
      intro z hz
      simpa [spanClosureSubset, Subtype.dist_eq] using hmin ⟨z, mem_spanClosure_of_mem hz⟩ hz
    have hiff' :
        dist (v : 𝓗) (p : 𝓗) = Metric.infDist (v : 𝓗) C ↔
          ∀ z ∈ C, dist (v : 𝓗) (p : 𝓗) ≤ dist (v : 𝓗) z :=
      dist_eq_infDist_iff_forall_dist_le hp
    exact hiff'.mpr hmin'
  · intro h
    have hiff :
        dist (v : 𝓗) (p : 𝓗) = Metric.infDist (v : 𝓗) C ↔
          ∀ z ∈ C, dist (v : 𝓗) (p : 𝓗) ≤ dist (v : 𝓗) z :=
      dist_eq_infDist_iff_forall_dist_le hp
    have hmin : ∀ z ∈ C, dist (v : 𝓗) (p : 𝓗) ≤ dist (v : 𝓗) z :=
      hiff.mp h
    have hmin' : ∀ z ∈ spanClosureSubset C, dist v p ≤ dist v z := by
      -- A subtype competitor is already an ambient competitor lying in `C`.
      intro z hz
      simpa [spanClosureSubset, Subtype.dist_eq] using hmin (z : 𝓗) hz
    have hiff' :
        dist v p = Metric.infDist v (spanClosureSubset C) ↔
          ∀ z ∈ spanClosureSubset C, dist v p ≤ dist v z :=
      dist_eq_infDist_iff_forall_dist_le hp
    exact hiff'.mpr hmin'

-- Proof sketch: let `V := (Submodule.span ℝ C).topologicalClosure`. Since `C ⊆ V`, every
-- `z ∈ C` lies in `V`, while
-- `x - V.starProjection x ∈ Vᗮ` and `V.starProjection x - z ∈ V`. The Pythagorean identity then
-- gives `‖x - z‖ ^ 2 = ‖V.starProjection x - z‖ ^ 2 + ‖x - V.starProjection x‖ ^ 2`, so the
-- minimizing points in `C` for `x` and for `V.starProjection x` coincide. For the consequent,
-- use this equality of projector values together with `V.starProjection x ∈ V` and the fact that
-- `C`, viewed inside `V`, has the same distance-realizing points as in the ambient space.

/-- Proposition 3.25: the set-valued projector onto `C` is unchanged after orthogonal projection
onto the closed span of `C`, and consequently `C` is proximinal in the ambient Hilbert space if
and only if it is proximinal in its closed span. -/
theorem setValuedProjector_eq_comp_closedSpanProjection_and_isProximinalIn_iff
    (C : Set 𝓗) (hC : C.Nonempty) :
    setValuedProjector C =
        setValuedProjector C ∘ ((Submodule.span ℝ C).topologicalClosure).starProjection ∧
      (IsProximinalIn C ↔
        IsProximinalIn (Subtype.val ⁻¹' C : Set ((Submodule.span ℝ C).topologicalClosure))) := by
  let _ : C.Nonempty := hC
  let V : Submodule ℝ 𝓗 := (Submodule.span ℝ C).topologicalClosure
  let C' : Set V := Subtype.val ⁻¹' C
  have hprojector :
      setValuedProjector C = setValuedProjector C ∘ V.starProjection := by
    funext x
    ext p
    rw [Function.comp_apply, mem_setValuedProjector_iff, mem_setValuedProjector_iff]
    constructor
    · intro hp
      have hpmin : ∀ z ∈ C, dist x (p : 𝓗) ≤ dist x z :=
        (dist_eq_infDist_iff_forall_dist_le hp.1).mp hp.2
      have hpV : p ∈ V := by
        simpa [V] using mem_spanClosure_of_mem hp.1
      have hprojmin :
          ∀ z ∈ C, dist (V.starProjection x) p ≤ dist (V.starProjection x) z := by
        -- Each comparison point in `C` lies in the closed span, so the residual term cancels.
        intro z hz
        have hzV : z ∈ V := by
          simpa [V] using mem_spanClosure_of_mem hz
        simpa [V] using (projection_dist_le_iff C hpV hzV).mp (hpmin z hz)
      exact ⟨hp.1, (dist_eq_infDist_iff_forall_dist_le hp.1).mpr hprojmin⟩
    · intro hp
      have hpmin : ∀ z ∈ C, dist (V.starProjection x) p ≤ dist (V.starProjection x) z :=
        (dist_eq_infDist_iff_forall_dist_le hp.1).mp hp.2
      have hpV : p ∈ V := by
        simpa [V] using mem_spanClosure_of_mem hp.1
      have hxmin : ∀ z ∈ C, dist x p ≤ dist x z := by
        -- The same comparison equivalence transports minimality back to the ambient space.
        intro z hz
        have hzV : z ∈ V := by
          simpa [V] using mem_spanClosure_of_mem hz
        simpa [V] using (projection_dist_le_iff C hpV hzV).mpr (hpmin z hz)
      exact ⟨hp.1, (dist_eq_infDist_iff_forall_dist_le hp.1).mpr hxmin⟩
  refine ⟨by simpa [V] using hprojector, ?_⟩
  constructor
  · intro hprox v
    obtain ⟨p, hpC, hpdist⟩ := hprox v
    let q : V := ⟨p, by simpa [V] using mem_spanClosure_of_mem hpC⟩
    -- An ambient minimizer already lives in the closed span and remains minimizing there.
    refine ⟨q, hpC, ?_⟩
    simpa [C', V] using (dist_eq_infDist_spanClosureSubset_iff_ambient C hpC).2 hpdist
  · intro hprox x
    let v : V := V.orthogonalProjection x
    obtain ⟨q, hqC, hqdist⟩ := hprox v
    have hqProj : (q : 𝓗) ∈ setValuedProjector C (V.starProjection x) := by
      -- The closed-span witness yields an ambient best approximation at the projected point.
      rw [mem_setValuedProjector_iff]
      exact ⟨hqC, by
        simpa [C', V, v] using (dist_eq_infDist_spanClosureSubset_iff_ambient C hqC).1 hqdist⟩
    have hqX : (q : 𝓗) ∈ setValuedProjector C x := by
      -- The projector identity lifts that witness back from `P_V x` to `x`.
      rw [(congrFun hprojector x)]
      exact hqProj
    exact ⟨q, (mem_setValuedProjector_iff).mp hqX⟩
end Complete

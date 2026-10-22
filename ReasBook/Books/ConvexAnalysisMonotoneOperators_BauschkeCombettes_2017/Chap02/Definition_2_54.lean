/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u v

open scoped Topology

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- A set `C` admits short positive line segments from `x` in every direction. -/
def HasRadialSegmentsAt (C : Set H) (x : H) : Prop :=
  ∀ y : H, ∃ α : ℝ, 0 < α ∧ ∀ t ∈ Set.Icc (0 : ℝ) α, x + t • y ∈ C

/-- Definition 2.54: `A` is the Gâteaux derivative of `T` at `x` within `C` if every direction
from `x` stays in `C` along some short positive segment and the restriction of `T` to each affine
line through `x` has the one-sided derivative `A y` at `0`. -/
def HasGateauxDerivativeWithinAt (T : H → K) (A : H →L[ℝ] K) (C : Set H) (x : H) : Prop :=
  HasRadialSegmentsAt C x ∧
    ∀ y : H,
      HasDerivWithinAt (fun α : ℝ ↦ T (x + α • y)) (A y) (Set.Ioi 0) 0

/-- `T` has Gâteaux derivative `A` at `x` if it has this derivative within the whole space. -/
abbrev HasGateauxDerivativeAt (T : H → K) (A : H →L[ℝ] K) (x : H) : Prop :=
  HasGateauxDerivativeWithinAt T A Set.univ x

/-- `T` is Gâteaux differentiable within `C` at `x` if it admits some Gâteaux derivative there. -/
abbrev GateauxDifferentiableWithinAt (T : H → K) (C : Set H) (x : H) : Prop :=
  ∃ A : H →L[ℝ] K, HasGateauxDerivativeWithinAt T A C x

/-- `T` is Gâteaux differentiable at `x` if it is Gâteaux differentiable within the whole space. -/
abbrev GateauxDifferentiableAt (T : H → K) (x : H) : Prop :=
  ∃ A : H →L[ℝ] K, HasGateauxDerivativeAt T A x

/-- `T` is Gâteaux differentiable on `C` if it is Gâteaux differentiable at every point of `C`. -/
def GateauxDifferentiableOn (T : H → K) (C : Set H) : Prop :=
  ∀ x ∈ C, GateauxDifferentiableWithinAt T C x

/-- A derivative field `DT` on `C` assigns to each point of `C` a Gâteaux derivative of `T`. -/
def HasGateauxDerivativeOn (T : H → K) (DT : H → H →L[ℝ] K) (C : Set H) : Prop :=
  ∀ x ∈ C, HasGateauxDerivativeWithinAt T (DT x) C x

/-- Definition 2.54: relative to a first-derivative field `DT`, `A₂` is a second Gâteaux
derivative of `T` at `x` within `C` if `DT x` is a Gâteaux derivative of `T` at `x` within `C`
and the operator field `DT` has Gâteaux derivative `A₂` there. -/
def HasGateauxSecondDerivativeWithinAt
    (T : H → K) (DT : H → H →L[ℝ] K) (C : Set H)
    (x : H) (A₂ : H →L[ℝ] (H →L[ℝ] K)) : Prop :=
  HasGateauxDerivativeWithinAt T (DT x) C x ∧ HasGateauxDerivativeWithinAt DT A₂ C x

/-- A neighborhood of `x` contains a short positive line segment from `x` in every direction. -/
theorem HasRadialSegmentsAt.of_mem_nhds
    {C : Set H} {x : H} (hC : C ∈ 𝓝 x) :
    HasRadialSegmentsAt C x := by
  intro y
  rcases Metric.mem_nhds_iff.1 hC with ⟨r, hrpos, hrC⟩
  refine ⟨r / (‖y‖ + 1), by positivity, ?_⟩
  intro t ht
  apply hrC
  have ht_nonneg : 0 ≤ t := ht.1
  have hy_pos : 0 < ‖y‖ + 1 := by positivity
  calc
    dist (x + t • y) x = ‖t • y‖ := by
      simp [dist_eq_norm, sub_eq_add_neg, add_assoc]
    _ = ‖t‖ * ‖y‖ := norm_smul t y
    _ = t * ‖y‖ := by rw [Real.norm_of_nonneg ht_nonneg]
    _ ≤ (r / (‖y‖ + 1)) * ‖y‖ := by nlinarith [ht.2, norm_nonneg y]
    _ < (r / (‖y‖ + 1)) * (‖y‖ + 1) := by
      gcongr
      linarith [norm_nonneg y]
    _ = r := by field_simp [hy_pos.ne']

/-- Helper for Definition 2.54: the whole space admits radial segments at every point. -/
theorem hasRadialSegmentsAt_univ (x : H) : HasRadialSegmentsAt (Set.univ : Set H) x :=
  HasRadialSegmentsAt.of_mem_nhds Filter.univ_mem

/-- A Fréchet derivative within a neighborhood gives the corresponding Gâteaux derivative. -/
theorem HasFDerivWithinAt.hasGateauxDerivativeWithinAt
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasFDerivWithinAt T A C x) (hC : C ∈ 𝓝 x) :
    HasGateauxDerivativeWithinAt T A C x := by
  refine ⟨HasRadialSegmentsAt.of_mem_nhds hC, ?_⟩
  intro y
  simpa [HasLineDerivAt] using
    (((hT.hasLineDerivWithinAt y).hasLineDerivAt hC).hasDerivWithinAt :
      HasDerivWithinAt (fun α : ℝ ↦ T (x + α • y)) (A y) (Set.Ioi 0) 0)

/-- A Fréchet derivative gives the corresponding Gâteaux derivative in the whole space. -/
theorem HasFDerivAt.hasGateauxDerivativeAt
    {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasFDerivAt T A x) :
    HasGateauxDerivativeAt T A x := by
  simpa [HasGateauxDerivativeAt] using
    hT.hasFDerivWithinAt.hasGateauxDerivativeWithinAt Filter.univ_mem

/-- In the whole space, a Gâteaux derivative yields the corresponding line derivative in every
direction. -/
theorem hasLineDerivAt_of_hasGateauxDerivativeAt
    {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasGateauxDerivativeAt T A x) (y : H) :
    HasLineDerivAt ℝ T (A y) x y := by
  let path : ℝ → K := fun t ↦ T (x + t • y)
  have hright : HasDerivWithinAt path (A y) (Set.Ioi 0) 0 := by
    simpa [HasGateauxDerivativeAt, path] using hT.2 y
  have hleftAux : HasDerivWithinAt path (A y) (Set.Iio 0) 0 := by
    let negPath : ℝ → K := fun s ↦ T (x + s • (-y))
    have hneg : HasDerivWithinAt negPath (A (-y)) (Set.Ioi 0) 0 := by
      simpa [HasGateauxDerivativeAt, negPath] using hT.2 (-y)
    have hnegTendsto :
        Filter.Tendsto (slope negPath 0) (𝓝[Set.Ioi 0] 0) (𝓝 (A (-y))) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hneg
    have hnegMap :
        Filter.Tendsto (fun t : ℝ ↦ -t) (𝓝[Set.Iio 0] 0) (𝓝[Set.Ioi 0] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa [ContinuousWithinAt] using
          (continuous_neg.continuousAt.continuousWithinAt :
            ContinuousWithinAt (fun t : ℝ ↦ -t) (Set.Iio 0) 0)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [Set.mem_Iio, Set.mem_Ioi] using neg_pos.mpr (show t < 0 by simpa using ht)
    have hcomp :
        Filter.Tendsto (fun t : ℝ ↦ slope negPath 0 (-t)) (𝓝[Set.Iio 0] 0) (𝓝 (A (-y))) :=
      hnegTendsto.comp hnegMap
    have hleftTendsto :
        Filter.Tendsto (fun t : ℝ ↦ slope path 0 t) (𝓝[Set.Iio 0] 0) (𝓝 (A y)) := by
      convert hcomp.neg using 1
      · ext t
        by_cases ht : t = 0
        · simp [ht, path, negPath]
        · rw [slope_def_module, slope_def_module]
          simp [path, negPath]
      · simp
    exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Iio 0 by simp)).2 hleftTendsto
  rw [HasLineDerivAt, hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Iio 0 by simp)).1 hleftAux
  · exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).1 hright

/-- A Gâteaux derivative within `C` yields the corresponding two-sided line derivative. -/
theorem HasGateauxDerivativeWithinAt.hasLineDerivAt
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasGateauxDerivativeWithinAt T A C x) (y : H) :
    HasLineDerivAt ℝ T (A y) x y := by
  let path : ℝ → K := fun t ↦ T (x + t • y)
  have hright : HasDerivWithinAt path (A y) (Set.Ioi 0) 0 := by
    simpa [path] using hT.2 y
  have hleftAux : HasDerivWithinAt path (A y) (Set.Iio 0) 0 := by
    let negPath : ℝ → K := fun s ↦ T (x + s • (-y))
    have hneg : HasDerivWithinAt negPath (A (-y)) (Set.Ioi 0) 0 := by
      simpa [negPath] using hT.2 (-y)
    have hnegTendsto :
        Filter.Tendsto (slope negPath 0) (𝓝[Set.Ioi 0] 0) (𝓝 (A (-y))) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hneg
    have hnegMap :
        Filter.Tendsto (fun t : ℝ ↦ -t) (𝓝[Set.Iio 0] 0) (𝓝[Set.Ioi 0] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa [ContinuousWithinAt] using
          (continuous_neg.continuousAt.continuousWithinAt :
            ContinuousWithinAt (fun t : ℝ ↦ -t) (Set.Iio 0) 0)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [Set.mem_Iio, Set.mem_Ioi] using neg_pos.mpr (show t < 0 by simpa using ht)
    have hcomp :
        Filter.Tendsto (fun t : ℝ ↦ slope negPath 0 (-t)) (𝓝[Set.Iio 0] 0) (𝓝 (A (-y))) :=
      hnegTendsto.comp hnegMap
    have hleftTendsto :
        Filter.Tendsto (fun t : ℝ ↦ slope path 0 t) (𝓝[Set.Iio 0] 0) (𝓝 (A y)) := by
      convert hcomp.neg using 1
      · ext t
        by_cases ht : t = 0
        · simp [ht, path, negPath]
        · rw [slope_def_module, slope_def_module]
          simp [path, negPath]
      · simp
    exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Iio 0 by simp)).2 hleftTendsto
  rw [HasLineDerivAt, hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Iio 0 by simp)).1 hleftAux
  · exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).1 hright

/-- Whole-space Gâteaux differentiability is exactly the existence of the corresponding line
derivative in every direction. -/
theorem hasGateauxDerivativeAt_iff_forall_hasLineDerivAt
    {T : H → K} {x : H} {A : H →L[ℝ] K} :
    HasGateauxDerivativeAt T A x ↔ ∀ y : H, HasLineDerivAt ℝ T (A y) x y := by
  constructor
  · intro hT y
    exact hasLineDerivAt_of_hasGateauxDerivativeAt hT y
  · intro hT
    refine ⟨hasRadialSegmentsAt_univ x, ?_⟩
    intro y
    simpa [HasLineDerivAt] using (hT y).hasDerivWithinAt

/-- Definition 2.54 in textbook form: the one-sided line-derivative formulation is equivalent to
the convergence of directional difference quotients to `A y` as the scalar tends to `0` from the
right. -/
theorem hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K} :
    HasGateauxDerivativeWithinAt T A C x ↔
      HasRadialSegmentsAt C x ∧
        ∀ y : H,
          Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
  constructor
  · rintro ⟨hSegments, hDeriv⟩
    refine ⟨hSegments, ?_⟩
    intro y
    let path : ℝ → K := fun α ↦ T (x + α • y)
    have hpath : HasDerivWithinAt path (A y) (Set.Ioi 0) 0 := hDeriv y
    have htendsto :
        Filter.Tendsto (slope path 0) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hpath
    have hslope :
        slope path 0 = fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x) := by
      ext α
      simp [path, slope_def_module, one_div]
    simpa [hslope] using htendsto
  · rintro ⟨hSegments, hTendsto⟩
    refine ⟨hSegments, ?_⟩
    intro y
    let path : ℝ → K := fun α ↦ T (x + α • y)
    have hslope :
        slope path 0 = fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x) := by
      ext α
      simp [path, slope_def_module, one_div]
    have htendsto :
        Filter.Tendsto (slope path 0) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
      rw [hslope]
      exact hTendsto y
    exact (hasDerivWithinAt_iff_tendsto_slope' (by simp)).2 htendsto

/-- A Gâteaux derivative provides the textbook directional-difference-quotient limit. -/
theorem HasGateauxDerivativeWithinAt.tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (h : HasGateauxDerivativeWithinAt T A C x) :
    ∀ y : H,
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
  (hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient.1 h).2

/-- Definition 2.54 in second-order form: the operator-valued line-derivative formulation for
`DT` is equivalent to the convergence of operator directional difference quotients to `A₂ y` as
the scalar tends to `0` from the right, together with the local first-derivative condition
`DT x = T'(x)`. -/
theorem hasGateauxSecondDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {DT : H → H →L[ℝ] K} {x : H}
    {A₂ : H →L[ℝ] (H →L[ℝ] K)} :
    HasGateauxSecondDerivativeWithinAt T DT C x A₂ ↔
      HasGateauxDerivativeWithinAt T (DT x) C x ∧
        HasRadialSegmentsAt C x ∧
          ∀ y : H,
            Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (DT (x + α • y) - DT x))
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A₂ y)) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient.1 h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient.2 h₂⟩

/-- A second Gâteaux derivative at `x` provides the corresponding first Gâteaux derivative there. -/
theorem HasGateauxSecondDerivativeWithinAt.hasGateauxDerivativeWithinAt
    {C : Set H} {T : H → K} {DT : H → H →L[ℝ] K} {x : H}
    {A₂ : H →L[ℝ] (H →L[ℝ] K)}
    (h : HasGateauxSecondDerivativeWithinAt T DT C x A₂) :
    HasGateauxDerivativeWithinAt T (DT x) C x :=
  h.1

/-- A second Gâteaux derivative at `x` differentiates the derivative field `DT` at `x`. -/
theorem HasGateauxSecondDerivativeWithinAt.hasGateauxDerivativeFieldWithinAt
    {C : Set H} {T : H → K} {DT : H → H →L[ℝ] K} {x : H}
    {A₂ : H →L[ℝ] (H →L[ℝ] K)}
    (h : HasGateauxSecondDerivativeWithinAt T DT C x A₂) :
    HasGateauxDerivativeWithinAt DT A₂ C x :=
  h.2

/-- A second Gâteaux derivative gives the textbook operator directional-difference-quotient limit
for the derivative field `DT`. -/
theorem HasGateauxSecondDerivativeWithinAt.tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {DT : H → H →L[ℝ] K} {x : H}
    {A₂ : H →L[ℝ] (H →L[ℝ] K)}
    (h : HasGateauxSecondDerivativeWithinAt T DT C x A₂) :
    ∀ y : H,
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (DT (x + α • y) - DT x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A₂ y)) :=
  (hasGateauxSecondDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient.1 h).2.2

/-- In the whole space, Definition 2.54 reduces to the directional-difference-quotient limit. -/
theorem hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient
    {T : H → K} {x : H} {A : H →L[ℝ] K} :
    HasGateauxDerivativeAt T A x ↔
      ∀ y : H,
        Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
  have hiff :
      HasGateauxDerivativeWithinAt T A Set.univ x ↔
        HasRadialSegmentsAt (Set.univ : Set H) x ∧
          ∀ y : H,
            Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
    hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient
  simpa [HasGateauxDerivativeAt, hasRadialSegmentsAt_univ] using hiff

/-- A Gâteaux derivative in the whole space provides the textbook directional-difference-quotient
limit. -/
theorem HasGateauxDerivativeAt.tendsto_directionalDifferenceQuotient
    {T : H → K} {x : H} {A : H →L[ℝ] K}
    (h : HasGateauxDerivativeAt T A x) :
    ∀ y : H,
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
  hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient.1 h

/-- A Gâteaux derivative at `x` forces the directional segment condition at `x`. -/
theorem HasGateauxDerivativeWithinAt.hasRadialSegmentsAt
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (h : HasGateauxDerivativeWithinAt T A C x) :
    HasRadialSegmentsAt C x :=
  h.1

/-- `T` is Gâteaux differentiable within `C` at `x` exactly when it admits some Gâteaux derivative
there. -/
theorem gateauxDifferentiableWithinAt_iff_exists_hasGateauxDerivativeWithinAt
    {C : Set H} {T : H → K} {x : H} :
    GateauxDifferentiableWithinAt T C x ↔
      ∃ A : H →L[ℝ] K, HasGateauxDerivativeWithinAt T A C x :=
  Iff.rfl

/-- `T` is Gâteaux differentiable at `x` exactly when it admits some Gâteaux derivative there. -/
theorem gateauxDifferentiableAt_iff_exists_hasGateauxDerivativeAt
    {T : H → K} {x : H} :
    GateauxDifferentiableAt T x ↔ ∃ A : H →L[ℝ] K, HasGateauxDerivativeAt T A x :=
  Iff.rfl

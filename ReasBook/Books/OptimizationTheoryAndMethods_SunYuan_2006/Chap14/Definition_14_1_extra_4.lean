/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Instances.EReal.Lemmas
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.OneSidedDirectionalDeriv

noncomputable section

open Filter
open scoped ClarkeDirectionalDerivative ClarkeDifferential

universe u

section

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

-- Domain sampling:
-- * primary domain: nonsmooth stationarity on real normed spaces
-- * sampled project owners: `HasOneSidedDirectionalDerivAt`, `oneSidedDirectionalDeriv`,
--   `clarkeDirectionalDeriv`, `clarkeDifferential`
-- * source-facing layer here: the three stationary-point predicates and their optimality bridges
-- * core/canonical owners reused here: the upstream one-sided directional derivative and Clarke
--   differential APIs
-- * bridge/view retained here: the lower Dini directional derivative, which is not already owned
--   upstream in this whole-space form
-- * primitive data vs derived API: stationarity uses the upstream derivative owners directly;
--   only `diniDirectionalDeriv` is introduced as new primitive data in this file

local notation "DualSpace" => StrongDual ℝ X

/-- The lower Dini directional derivative is the liminf of the positive difference quotient
`(f (x + t • d) - f x) / t` as `t → 0`, viewed in `EReal` so no finiteness hypothesis is
silently imposed. -/
def diniDirectionalDeriv (f : X → ℝ) (x d : X) : EReal :=
  Filter.liminf
    (fun t : ℝ ↦ (((f (x + t • d) - f x) / t : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- Unfolding formula for `diniDirectionalDeriv`. -/
theorem diniDirectionalDeriv_eq_liminf (f : X → ℝ) (x d : X) :
    diniDirectionalDeriv f x d =
      Filter.liminf
        (fun t : ℝ ↦ (((f (x + t • d) - f x) / t : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := rfl

/-- Chapter14 Definition 14.1-extra-4 (1): `x` is a stationary point of `f` when the
chapter's one-sided directional derivative exists in every direction at `x` and every such
directional derivative there is nonnegative. The earlier `Set.univ` directional-differentiability
surface is retained below only as a bridge reformulation. -/
def IsDirectionalStationaryPoint (f : X → ℝ) (x : X) : Prop :=
  (∀ d : X, HasOneSidedDirectionalDerivAt f (oneSidedDirectionalDeriv f x d) x d) ∧
    ∀ d : X, 0 ≤ oneSidedDirectionalDeriv f x d

/-- Unfolding formula for `IsDirectionalStationaryPoint`. -/
theorem isDirectionalStationaryPoint_iff {f : X → ℝ} {x : X} :
    IsDirectionalStationaryPoint f x ↔
      (∀ d : X, HasOneSidedDirectionalDerivAt f (oneSidedDirectionalDeriv f x d) x d) ∧
        ∀ d : X, 0 ≤ oneSidedDirectionalDeriv f x d := Iff.rfl

/-- Bridge reformulation of `IsDirectionalStationaryPoint` through the older whole-space
directional-differentiability owner `DirectionallyDifferentiableWithinAt Set.univ`. -/
theorem isDirectionalStationaryPoint_iff_directionallyDifferentiableWithinAt_univ
    {f : X → ℝ} {x : X} :
    IsDirectionalStationaryPoint f x ↔
      DirectionallyDifferentiableWithinAt Set.univ f ⟨x, by simp⟩ ∧
        ∀ d : X, 0 ≤ directionalDerivWithin Set.univ f ⟨x, by simp⟩ d := by
  rw [isDirectionalStationaryPoint_iff]
  constructor
  · intro h
    constructor
    · rw [directionallyDifferentiableWithinAt_univ_iff]
      intro d
      exact ⟨oneSidedDirectionalDeriv f x d, h.1 d⟩
    · intro d
      simpa [directionalDerivWithin_univ_eq_oneSidedDirectionalDeriv] using h.2 d
  · intro h
    constructor
    · intro d
      rcases (directionallyDifferentiableWithinAt_univ_iff.mp h.1) d with ⟨f', hf'⟩
      have hf'' : oneSidedDirectionalDeriv f x d = f' := hf'.oneSidedDirectionalDeriv_eq
      simpa [hf''] using hf'
    · intro d
      simpa [directionalDerivWithin_univ_eq_oneSidedDirectionalDeriv] using h.2 d

/-- A directional stationary point admits the chapter's one-sided directional derivative in each
direction. -/
theorem IsDirectionalStationaryPoint.hasOneSidedDirectionalDerivAt
    {f : X → ℝ} {x d : X} (h : IsDirectionalStationaryPoint f x) :
    HasOneSidedDirectionalDerivAt f (oneSidedDirectionalDeriv f x d) x d := h.1 d

/-- Bridge lemma: a directional stationary point is directionally differentiable in the
whole-space sense of `DirectionallyDifferentiableWithinAt Set.univ`. -/
theorem IsDirectionalStationaryPoint.directionallyDifferentiableWithinAt_univ
    {f : X → ℝ} {x : X} (h : IsDirectionalStationaryPoint f x) :
    DirectionallyDifferentiableWithinAt Set.univ f ⟨x, by simp⟩ :=
  (isDirectionalStationaryPoint_iff_directionallyDifferentiableWithinAt_univ.mp h).1

/-- Every one-sided directional derivative at a directional stationary point is nonnegative. -/
theorem IsDirectionalStationaryPoint.nonneg_oneSidedDirectionalDeriv
    {f : X → ℝ} {x d : X} (h : IsDirectionalStationaryPoint f x) :
    0 ≤ oneSidedDirectionalDeriv f x d := h.2 d

/-- Bridge lemma: every whole-space directional derivative at a directional stationary point is
nonnegative. -/
theorem IsDirectionalStationaryPoint.nonneg_directionalDerivWithin_univ
    {f : X → ℝ} {x d : X} (h : IsDirectionalStationaryPoint f x) :
    0 ≤ directionalDerivWithin Set.univ f ⟨x, by simp⟩ d := by
  simpa [directionalDerivWithin_univ_eq_oneSidedDirectionalDeriv] using
    h.nonneg_oneSidedDirectionalDeriv

/-- Chapter14 Definition 14.1-extra-4 (2): `x` is a Dini stationary point of `f` when every
lower Dini directional derivative `diniDirectionalDeriv f x d` is nonnegative. -/
def IsDiniStationaryPoint (f : X → ℝ) (x : X) : Prop :=
  ∀ d : X, 0 ≤ diniDirectionalDeriv f x d

/-- Unfolding formula for `IsDiniStationaryPoint`. -/
theorem isDiniStationaryPoint_iff {f : X → ℝ} {x : X} :
    IsDiniStationaryPoint f x ↔ ∀ d : X, 0 ≤ diniDirectionalDeriv f x d := Iff.rfl

/-- Every lower Dini directional derivative at a Dini stationary point is nonnegative. -/
theorem IsDiniStationaryPoint.nonneg_diniDirectionalDeriv
    {f : X → ℝ} {x d : X} (h : IsDiniStationaryPoint f x) :
    0 ≤ diniDirectionalDeriv f x d := h d

/-- Chapter14 Definition 14.1-extra-4 (3): `x` is a Clarke stationary point of `f` when every
Clarke generalized directional derivative `fᵒ(x; d)` is nonnegative. -/
def IsClarkeStationaryPoint (f : X → ℝ) (x : X) : Prop :=
  ∀ d : X, 0 ≤ fᵒ(x; d)

/-- Unfolding formula for `IsClarkeStationaryPoint`. -/
theorem isClarkeStationaryPoint_iff {f : X → ℝ} {x : X} :
    IsClarkeStationaryPoint f x ↔
      ∀ d : X, 0 ≤ fᵒ(x; d) := Iff.rfl

/-- Every Clarke directional derivative at a Clarke stationary point is
nonnegative. -/
theorem IsClarkeStationaryPoint.nonneg_clarkeDirectionalDeriv
    {f : X → ℝ} {x d : X} (h : IsClarkeStationaryPoint f x) :
    0 ≤ fᵒ(x; d) := h d

/-- Chapter14 Definition 14.1-extra-4 (4): under the local Lipschitz hypothesis required by
the Clarke differential owner, `0 ∈ ∂ᶜ f(x)` is equivalent to Clarke stationarity at `x`. -/
theorem isClarkeStationaryPoint_iff_zero_mem_clarkeDifferential
    {f : X → ℝ} {x : X} :
    IsClarkeStationaryPoint f x ↔
      (0 : DualSpace) ∈ (∂ᶜ f) x := by
  rw [isClarkeStationaryPoint_iff, mem_clarkeDifferential_iff]
  simp

/-- Helper for Chapter14 Definition 14.1-extra-4: positive times still approach `0`, so the
forward-time filter used in the Dini derivative is nontrivial. -/
lemma nhdsWithin_zero_Ioi_neBot :
    NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  -- The closure identity `closure (Ioi 0) = Ici 0` keeps `0` in the forward-time closure.
  rw [← mem_closure_iff_nhdsWithin_neBot]
  simp [closure_Ioi]

/-- Helper for Chapter14 Definition 14.1-extra-4: along any forward ray from a local minimizer,
the positive difference quotient is eventually nonnegative. -/
lemma eventually_nonneg_positive_differenceQuotient_of_isLocalMin
    {f : X → ℝ} {x d : X} (h_min : IsLocalMin f x) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (0 : EReal) ≤ (((f (x + t • d) - f x) / t : ℝ) : EReal) := by
  have h_ray_tendsto :
      Tendsto (fun t : ℝ ↦ x + t • d) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds x) := by
    -- The ray map is continuous at `0`, so pulling back the local-minimum neighborhood is valid.
    have h_smul_tendsto :
        Tendsto (fun t : ℝ ↦ t • d) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 • d)) := by
      simpa using
        (((continuous_id.smul continuous_const).continuousAt.continuousWithinAt
          : ContinuousWithinAt (fun t : ℝ ↦ t • d) (Set.Ioi 0) 0).tendsto)
    simpa using tendsto_const_nhds.add h_smul_tendsto
  have h_values :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), f x ≤ f (x + t • d) :=
    h_ray_tendsto h_min
  -- On positive times, nonnegative numerator and denominator force a nonnegative quotient.
  filter_upwards [h_values, self_mem_nhdsWithin] with t ht_value ht_pos
  have hquot_nonneg : 0 ≤ (f (x + t • d) - f x) / t := by
    exact div_nonneg (sub_nonneg.mpr ht_value) ht_pos.le
  exact_mod_cast hquot_nonneg

/-- Helper for Chapter14 Definition 14.1-extra-4: restricting a local minimizer to the forward
ray `t ↦ x + t • d` yields a local minimum on `Ici 0` at `0`. -/
lemma isLocalMinOn_ray_Ici_of_isLocalMin
    {f : X → ℝ} {x d : X} (h_min : IsLocalMin f x) :
    IsLocalMinOn (fun t : ℝ ↦ f (x + t • d)) (Set.Ici 0) 0 := by
  let ray : ℝ → X := fun t ↦ x + t • d
  have h_ray_cont : ContinuousOn ray (Set.Ici 0) := by
    -- The ray map is affine, hence continuous on every set.
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  have h_min_ray : IsLocalMin f (ray 0) := by
    -- The ray starts at `x`, so the ambient local minimum is still based at the ray origin.
    simpa [ray] using h_min
  -- Compose the ambient local minimum with the continuous ray, then restrict to forward times.
  convert
    h_min_ray.comp_continuousOn (s := Set.Ici 0) h_ray_cont (show 0 ≤ (0 : ℝ) from le_rfl) using 1
  funext t
  simp [ray, Function.comp]

/-- Helper for Chapter14 Definition 14.1-extra-4: a whole-space local Lipschitz bound at `x`
induces the within-`Set.univ` Lipschitz hypothesis needed by the Chapter 14 Clarke API. -/
lemma locallyLipschitzWithinAt_univ_of_locallyLipschitzAt
    {f : X → ℝ} {x : X} (h_local : LocallyLipschitzAt f x) :
    LocallyLipschitzWithinAt Set.univ f ⟨x, Set.mem_univ x⟩ := by
  rcases locallyLipschitzAt_iff.mp h_local with ⟨ε, hε, K, hK⟩
  -- The same closed-ball witness works verbatim inside the whole-space within filter.
  refine ⟨K, Metric.closedBall x ε, ?_, hK⟩
  simpa using (Metric.closedBall_mem_nhds x hε)

/-- Helper for Chapter14 Definition 14.1-extra-4: under local Lipschitz control, the lower Dini
directional derivative is bounded above by the Clarke directional derivative. -/
lemma diniDirectionalDeriv_le_clarkeDirectionalDeriv_of_locallyLipschitzAt
    {f : X → ℝ} {x d : X} (h_local : LocallyLipschitzAt f x) :
    diniDirectionalDeriv f x d ≤ fᵒ(x; d) := by
  let q : ℝ → EReal := fun t ↦ (((f (x + t • d) - f x) / t : ℝ) : EReal)
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let xuniv : Set.univ := ⟨x, Set.mem_univ x⟩
  have hlocalWithin : LocallyLipschitzWithinAt Set.univ f xuniv :=
    locallyLipschitzWithinAt_univ_of_locallyLipschitzAt h_local
  have hupper_le :
      upperDiniDirectionalDerivWithin Set.univ f xuniv d ≤
        clarkeDirectionalDerivWithin Set.univ f xuniv d :=
    upperDiniDirectionalDerivWithin_le_clarkeDirectionalDerivWithin hlocalWithin
  haveI : NeBot l := nhdsWithin_zero_Ioi_neBot
  have hliminf_le : Filter.liminf q l ≤ Filter.limsup q l := by
    -- The same forward-time quotient admits the standard `liminf ≤ limsup` comparison.
    exact liminf_le_limsup
  have hcompare :
      Filter.limsup q l ≤ fᵒ(x; d) := by
    -- In the whole-space case, the upper-Dini owner is exactly the same limsup quotient.
    simpa [clarkeDirectionalDeriv, upperDiniDirectionalDerivWithin_eq_limsup, q, l] using hupper_le
  calc
    diniDirectionalDeriv f x d = Filter.liminf q l := by
      rfl
    _ ≤ Filter.limsup q l := hliminf_le
    _ ≤ fᵒ(x; d) := hcompare

/-- Helper for Chapter14 Definition 14.1-extra-4: the function `x ↦ min x 0` has lower Dini
directional derivative `-1` at `0` in direction `-1`. -/
lemma diniDirectionalDeriv_min_zero_at_zero_neg_one :
    diniDirectionalDeriv (fun x : ℝ ↦ min x 0) 0 (-1) = ((-1 : ℝ) : EReal) := by
  let q : ℝ → EReal :=
    fun t ↦ ((((min (0 + t • (-1 : ℝ)) 0) - min (0 : ℝ) 0) / t : ℝ) : EReal)
  haveI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := nhdsWithin_zero_Ioi_neBot
  have hq :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), q t = (((-1 : ℝ) : ℝ) : EReal) := by
    -- For positive `t`, the ray stays on the negative half-line, so the quotient is literally `-1`.
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_ne : t ≠ 0 := ne_of_gt ht
    have hneg : -t ≤ 0 := neg_nonpos.mpr ht.le
    have hmin : min (-t) 0 = -t := min_eq_left hneg
    have hmin0 : min (0 : ℝ) 0 = 0 := by
      simp
    have hsmul : t • (-1 : ℝ) = -t := by
      ring
    have hquot :
        ((min (0 + t • (-1 : ℝ)) 0 - min (0 : ℝ) 0) / t : ℝ) = -1 := by
      calc
        ((min (0 + t • (-1 : ℝ)) 0 - min (0 : ℝ) 0) / t : ℝ)
            = ((min (-t) 0 - 0) / t : ℝ) := by
                rw [hsmul, hmin0]
                ring_nf
        _ = ((-t) / t : ℝ) := by
              rw [hmin]
              ring
        _ = (-1 : ℝ) := by
              field_simp [ht_ne]
    change ((((min (0 + t • (-1 : ℝ)) 0) - min (0 : ℝ) 0) / t : ℝ) : EReal) = ((-1 : ℝ) : EReal)
    exact_mod_cast hquot
  -- Replace the quotient by the eventual constant value and evaluate the liminf of a constant.
  calc
    diniDirectionalDeriv (fun x : ℝ ↦ min x 0) 0 (-1)
        = Filter.liminf q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
            rfl
    _ = Filter.liminf (fun _ : ℝ ↦ (((-1 : ℝ) : ℝ) : EReal))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
            exact liminf_congr hq
    _ = (((-1 : ℝ) : ℝ) : EReal) := by
          simpa using (liminf_const (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (((( -1 : ℝ) : ℝ) : EReal)))

/-- Chapter14 Definition 14.1-extra-4 (5): a local minimizer is Dini stationary at `x`. -/
theorem IsLocalMin.isDiniStationaryPoint
    {f : X → ℝ} {x : X}
    (h_min : IsLocalMin f x) :
    IsDiniStationaryPoint f x := by
  intro d
  haveI : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := nhdsWithin_zero_Ioi_neBot
  -- The source route is to show the forward difference quotient is eventually nonnegative and
  -- then pass to the liminf that defines the lower Dini derivative.
  rw [diniDirectionalDeriv_eq_liminf]
  exact
    le_liminf_of_le
      (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (u := fun t : ℝ ↦ (((f (x + t • d) - f x) / t : ℝ) : EReal))
      (a := (0 : EReal))
      (by isBoundedDefault)
      (eventually_nonneg_positive_differenceQuotient_of_isLocalMin (d := d) h_min)

/-- Chapter14 Definition 14.1-extra-4 (6): a local minimizer is directionally stationary once
the canonical one-sided directional derivative exists in every direction at the minimizer. -/
theorem IsLocalMin.isDirectionalStationaryPoint
    {f : X → ℝ} {x : X}
    (h_min : IsLocalMin f x)
    (h_dir : ∀ d : X, HasOneSidedDirectionalDerivAt f (oneSidedDirectionalDeriv f x d) x d) :
    IsDirectionalStationaryPoint f x := by
  constructor
  · -- The derivative-existence half is part of the hypothesis.
    exact h_dir
  · intro d
    let ray : ℝ → ℝ := fun t ↦ f (x + t • d)
    have h_ray_min : IsLocalMinOn ray (Set.Ici 0) 0 :=
      isLocalMinOn_ray_Ici_of_isLocalMin h_min
    have hone :
        (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) (0 : ℝ) := by
      -- The forward direction belongs to the tangent cone because `0` is in the closure of `Ioi 0`.
      rw [one_mem_posTangentConeAt_iff_mem_closure]
      simp [Set.inter_eq_left.mpr Set.Ioi_subset_Ici_self, closure_Ioi]
    have hnonneg :
        0 ≤
          (ContinuousLinearMap.toSpanSingleton ℝ (oneSidedDirectionalDeriv f x d)) (1 : ℝ) := by
      -- Apply the local-minimum derivative test to the ray restricted to `Ici 0`.
      exact h_ray_min.hasFDerivWithinAt_nonneg (h_dir d).hasFDerivWithinAt hone
    -- Evaluating the one-dimensional derivative functional at `1` recovers the directional
    -- derivative.
    simpa [HasOneSidedDirectionalDerivAt, oneSidedDirectionalDeriv, ray] using hnonneg

/-- Chapter14 Definition 14.1-extra-4 (7): under the local Lipschitz hypothesis that keeps the
textbook Clarke generalized directional derivative in scope, every Dini stationary point is
Clarke stationary. -/
theorem IsDiniStationaryPoint.isClarkeStationaryPoint
    {f : X → ℝ} {x : X} (h : IsDiniStationaryPoint f x)
    (h_local : LocallyLipschitzAt f x) :
    IsClarkeStationaryPoint f x := by
  intro d
  -- The Dini derivative is nonnegative, and the Clarke derivative dominates it under local
  -- Lipschitz control.
  exact (h d).trans (diniDirectionalDeriv_le_clarkeDirectionalDeriv_of_locallyLipschitzAt h_local)

/-- A local minimizer is Clarke stationary under the local Lipschitz hypothesis used by the
Chapter 14 Clarke owner. -/
theorem IsLocalMin.isClarkeStationaryPoint
    {f : X → ℝ} {x : X}
    (h_min : IsLocalMin f x)
    (h_local : LocallyLipschitzAt f x) :
    IsClarkeStationaryPoint f x :=
  (h_min.isDiniStationaryPoint).isClarkeStationaryPoint h_local

/-- A local maximizer is Clarke stationary under the same local Lipschitz hypothesis. -/
theorem IsLocalMax.isClarkeStationaryPoint
    {f : X → ℝ} {x : X}
    (h_max : IsLocalMax f x)
    (h_local : LocallyLipschitzAt f x) :
    IsClarkeStationaryPoint f x := by
  have h_neg : IsClarkeStationaryPoint (-f) x :=
    h_max.neg.isClarkeStationaryPoint h_local.neg
  intro d
  have hnegd : 0 ≤ (-f)ᵒ(x; -d) := h_neg (-d)
  rw [← clarkeDirectionalDerivative_neg_direction f x h_local (-d), neg_neg] at hnegd
  exact hnegd

/-- A local extremum is Clarke stationary under the local Lipschitz hypothesis. -/
theorem IsLocalExtr.isClarkeStationaryPoint
    {f : X → ℝ} {x : X}
    (h_ext : IsLocalExtr f x)
    (h_local : LocallyLipschitzAt f x) :
    IsClarkeStationaryPoint f x :=
  h_ext.elim
    (fun h_min ↦ h_min.isClarkeStationaryPoint h_local)
    (fun h_max ↦ h_max.isClarkeStationaryPoint h_local)

/-- Chapter14 Definition 14.1-extra-4 (8): the converse to Dini implies Clarke stationary fails
in general; there exists a Clarke stationary point that is not Dini stationary. -/
theorem exists_clarkeStationaryPoint_not_diniStationaryPoint :
    ∃ (f : ℝ → ℝ) (x : ℝ), IsClarkeStationaryPoint f x ∧ ¬ IsDiniStationaryPoint f x := by
  refine ⟨fun x : ℝ ↦ min x 0, 0, ?_, ?_⟩
  · have hmax : IsLocalMax (fun x : ℝ ↦ min x 0) 0 := by
      -- The function `min x 0` never exceeds its value at `0`, so `0` is a local maximum.
      change ∀ᶠ y in nhds (0 : ℝ), min y 0 ≤ min (0 : ℝ) 0
      exact Eventually.of_forall (fun y : ℝ ↦ by simp)
    have hlocal : LocallyLipschitzAt (fun x : ℝ ↦ min x 0) 0 := by
      -- A global Lipschitz bound for `min x 0` gives the required local Lipschitz witness.
      refine locallyLipschitzAt_of_closedBall (K := 1) ?_
      refine ⟨1, by norm_num, ?_⟩
      exact (LipschitzWith.min_const LipschitzWith.id 0).lipschitzOnWith
    exact hmax.isClarkeStationaryPoint hlocal
  · intro h_dini
    have hnonneg : (0 : EReal) ≤ ((-1 : ℝ) : EReal) := by
      simpa [diniDirectionalDeriv_min_zero_at_zero_neg_one] using h_dini (-1 : ℝ)
    have hlt : (((-1 : ℝ) : EReal) < 0) := by
      exact_mod_cast (show (-1 : ℝ) < 0 by norm_num)
    exact (not_le_of_gt hlt) hnonneg

end

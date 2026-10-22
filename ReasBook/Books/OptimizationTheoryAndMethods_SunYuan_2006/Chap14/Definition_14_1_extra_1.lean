/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.EReal.Lemmas
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.OneSidedDirectionalDeriv

noncomputable section

open Filter

universe u v

section

variable {X : Type u} {Z : Type v}
variable [PseudoEMetricSpace X] [PseudoEMetricSpace Z]

-- Domain sampling for the local-Lipschitz bridge:
-- - mathlib core owners: `LipschitzOnWith`, `LocallyLipschitzOn`
-- - project comparison owner: `LocallyLipschitzAt`
-- - owner abstraction here: `LocallyLipschitzOn Y f`
-- - primitive pointwise clause: `∃ K t, t ∈ nhdsWithin x Y ∧ LipschitzOnWith K f t`
-- - derived API here: the source-facing pointwise bridge name
--   `LocallyLipschitzWithinAt Y f x`
-- The later directional/Clarke layer is genuinely real-valued and starts in the next section.

/-
Chapter14 Definition 14.1-extra-1: the global Lipschitz condition `(14.1.1)` on a set
and the canonical local-on-a-set owner are the mathlib notions
`LipschitzOnWith K f Y` and `LocallyLipschitzOn Y f`. -/
#check LipschitzOnWith
#check LocallyLipschitzOn

/-- Source notion for Chapter14 Definition 14.1-extra-1 (1): `f` is Lipschitz near `x`
within `Y` when it is Lipschitz on some neighborhood of `x` relative to `Y`. This is the
pointwise bridge to the canonical owner `LocallyLipschitzOn Y f`. -/
def LocallyLipschitzWithinAt (Y : Set X) (f : X → Z) (x : Y) : Prop :=
  ∃ K : NNReal, ∃ t ∈ nhdsWithin (x : X) Y, LipschitzOnWith K f t

/-- Unfolding formula for `LocallyLipschitzWithinAt`. -/
theorem locallyLipschitzWithinAt_iff {Y : Set X} {f : X → Z} {x : Y} :
    LocallyLipschitzWithinAt Y f x ↔
      ∃ K : NNReal, ∃ t ∈ nhdsWithin (x : X) Y, LipschitzOnWith K f t :=
  Iff.rfl

/-- The canonical setwise owner gives the pointwise within-domain owner at each point of `Y`. -/
theorem LocallyLipschitzOn.locallyLipschitzWithinAt
    {Y : Set X} {f : X → Z} (h : LocallyLipschitzOn Y f) (x : Y) :
    LocallyLipschitzWithinAt Y f x :=
  h x.2

/-- The source-facing pointwise owner is exactly the pointwise form of the canonical setwise owner
`LocallyLipschitzOn Y f`. -/
theorem locallyLipschitzOn_iff_forall_locallyLipschitzWithinAt
    {Y : Set X} {f : X → Z} :
    LocallyLipschitzOn Y f ↔ ∀ x : Y, LocallyLipschitzWithinAt Y f x := by
  constructor
  · intro h x
    exact h.locallyLipschitzWithinAt x
  · intro h x hx
    exact h ⟨x, hx⟩

end

section

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `HasDirectionalTraceWithinDomain Y x d` means that the forward ray `x + t • d` stays in `Y`
for all sufficiently small positive `t`. -/
def HasDirectionalTraceWithinDomain (Y : Set X) (x : Y) (d : X) : Prop :=
  ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (x : X) + t • d ∈ Y

/-- Unfolding formula for `HasDirectionalTraceWithinDomain`. -/
theorem hasDirectionalTraceWithinDomain_iff {Y : Set X} {x : Y} {d : X} :
    HasDirectionalTraceWithinDomain Y x d ↔
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (x : X) + t • d ∈ Y :=
  Iff.rfl

/-- The one-sided time domain used for directional derivatives along `d` inside `Y`. -/
def directionalDerivWithinDomain (Y : Set X) (x : Y) (d : X) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ (x : X) + t • d ∈ Y}

/-- Membership in `directionalDerivWithinDomain Y x d` means nonnegative time and domain
membership along the ray starting at `x` in direction `d`. -/
theorem mem_directionalDerivWithinDomain {Y : Set X} {x : Y} {d : X} {t : ℝ} :
    t ∈ directionalDerivWithinDomain Y x d ↔ 0 ≤ t ∧ (x : X) + t • d ∈ Y :=
  Iff.rfl

/-- Source notion for Chapter14 Definition 14.1-extra-1 (2):
`HasDirectionalDerivWithinAt Y f f' x d` is the source directional derivative existence
statement, formalized as the right derivative of `t ↦ f (x + t • d)` at `0` along the
admissible nonnegative times staying in `Y`, together with the explicit trace condition
that the forward ray remains in `Y` for small positive `t`. -/
class HasDirectionalDerivWithinAt
    (Y : Set X) (f : X → ℝ) (f' : ℝ) (x : Y) (d : X) : Prop where
  /-- The forward ray `x + t • d` stays in the source domain `Y` for small positive `t`. -/
  hasDirectionalTraceWithinDomain : HasDirectionalTraceWithinDomain Y x d
  /-- The curve `t ↦ f (x + t • d)` has right derivative `f'` at `0` along the admissible
  nonnegative times staying in `Y`. -/
  hasDerivWithinAt :
    HasDerivWithinAt
      (fun t : ℝ ↦ f ((x : X) + t • d))
      f'
      (directionalDerivWithinDomain Y x d)
      0

/-- `HasDirectionalDerivWithinAt Y f f' x d` is proposition-valued. -/
instance hasDirectionalDerivWithinAt_subsingleton
    (Y : Set X) (f : X → ℝ) (f' : ℝ) (x : Y) (d : X) :
    Subsingleton (HasDirectionalDerivWithinAt Y f f' x d) := inferInstance

/-- Unfolding formula for `HasDirectionalDerivWithinAt`. -/
theorem hasDirectionalDerivWithinAt_iff
    {Y : Set X} {f : X → ℝ} {f' : ℝ} {x : Y} {d : X} :
    HasDirectionalDerivWithinAt Y f f' x d ↔
      HasDirectionalTraceWithinDomain Y x d ∧
        HasDerivWithinAt
          (fun t : ℝ ↦ f ((x : X) + t • d))
          f'
          (directionalDerivWithinDomain Y x d)
          0 := by
  constructor
  · intro h
    exact ⟨h.hasDirectionalTraceWithinDomain, h.hasDerivWithinAt⟩
  · rintro ⟨htrace, hderiv⟩
    exact ⟨htrace, hderiv⟩

/-- The directional derivative value at `x` in direction `d`, used as a companion to
`HasDirectionalDerivWithinAt Y f f' x d`. -/
def directionalDerivWithin (Y : Set X) (f : X → ℝ) (x : Y) (d : X) : ℝ :=
  derivWithin
    (fun t : ℝ ↦ f ((x : X) + t • d))
    (directionalDerivWithinDomain Y x d)
    0

/-- Unfolding formula for `directionalDerivWithin`. -/
theorem directionalDerivWithin_eq_derivWithin (Y : Set X) (f : X → ℝ) (x : Y) (d : X) :
    directionalDerivWithin Y f x d =
      derivWithin
        (fun t : ℝ ↦ f ((x : X) + t • d))
        (directionalDerivWithinDomain Y x d)
        0 :=
  rfl

/-- Helper for Chapter14 Definition 14.1-extra-1: near `0`, the admissible directional time
domain agrees with the standard right half-line `Set.Ici 0`. -/
theorem directionalDerivWithinDomain_eventuallyEq_Ici
    {Y : Set X} {x : Y} {d : X} (htrace : HasDirectionalTraceWithinDomain Y x d) :
    directionalDerivWithinDomain Y x d =ᶠ[nhds (0 : ℝ)] Set.Ici 0 := by
  -- Restrict to a neighborhood where every positive time already stays inside `Y`.
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp htrace with ⟨u, hu_nhds, hu_subset⟩
  refine Filter.mem_of_superset hu_nhds ?_
  intro t htu
  apply propext
  constructor
  · intro ht
    exact ht.1
  · intro ht0
    refine ⟨ht0, ?_⟩
    by_cases hzero : t = 0
    · simp [hzero, x.2]
    · exact hu_subset ⟨htu, lt_of_le_of_ne ht0 (Ne.symm hzero)⟩

/-- If the directional derivative exists with value `f'`, then `directionalDerivWithin Y f x d`
recovers that value. -/
theorem HasDirectionalDerivWithinAt.directionalDerivWithin_eq
    {Y : Set X} {f : X → ℝ} {f' : ℝ} {x : Y} {d : X}
    (h : HasDirectionalDerivWithinAt Y f f' x d) :
    directionalDerivWithin Y f x d = f' := by
  -- Normalize the source time domain to `Set.Ici 0` so the standard one-sided derivative API
  -- can recover the derivative value.
  have hdomain :
      directionalDerivWithinDomain Y x d =ᶠ[nhds (0 : ℝ)] Set.Ici 0 :=
    directionalDerivWithinDomain_eventuallyEq_Ici h.hasDirectionalTraceWithinDomain
  have hderivIci :
      HasDerivWithinAt
        (fun t : ℝ ↦ f ((x : X) + t • d))
        f'
        (Set.Ici 0)
        0 := by
    exact h.hasDerivWithinAt.congr_set hdomain
  -- With the normalized domain in place, `derivWithin` equals the prescribed derivative.
  unfold directionalDerivWithin
  rw [derivWithin_congr_set hdomain]
  exact hderivIci.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))

/-- Source notion for Chapter14 Definition 14.1-extra-1 (3): the upper Dini directional
derivative is the limsup of the difference quotient as `t → 0` through positive scalars
for which `x + t • d ∈ Y`, viewed in `EReal` so no finiteness hypothesis is silently
imposed. -/
def upperDiniDirectionalDerivWithin (Y : Set X) (f : X → ℝ) (x : Y) (d : X) : EReal :=
  Filter.limsup
    (fun t : ℝ ↦ (((f ((x : X) + t • d) - f x) / t : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0 ∩ {t : ℝ | (x : X) + t • d ∈ Y}))

/-- Unfolding formula for `upperDiniDirectionalDerivWithin`. -/
theorem upperDiniDirectionalDerivWithin_eq_limsup
    (Y : Set X) (f : X → ℝ) (x : Y) (d : X) :
    upperDiniDirectionalDerivWithin Y f x d =
      Filter.limsup
        (fun t : ℝ ↦ (((f ((x : X) + t • d) - f x) / t : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0 ∩ {t : ℝ | (x : X) + t • d ∈ Y})) :=
  rfl

/-- Helper for Chapter14 Definition 14.1-extra-1: removing the time `0` from the directional
time domain leaves exactly the positive times for which the forward ray stays inside `Y`. -/
theorem directionalDerivWithinDomain_sdiff_zero_eq
    {Y : Set X} {x : Y} {d : X} :
    directionalDerivWithinDomain Y x d \ ({0} : Set ℝ) =
      Set.Ioi 0 ∩ {t : ℝ | (x : X) + t • d ∈ Y} := by
  ext t
  constructor
  · intro ht
    rcases ht with ⟨ht, ht0⟩
    have htne : t ≠ 0 := by simpa using ht0
    exact ⟨lt_of_le_of_ne ht.1 htne.symm, ht.2⟩
  · rintro ⟨ht0, htY⟩
    refine ⟨⟨le_of_lt ht0, htY⟩, ?_⟩
    simpa using ht0.ne'

/-- The admissible pair domain for the Clarke directional derivative consists of points
`y ∈ Y` and positive times `t` such that `y + t • d ∈ Y`. -/
def clarkeDirectionalDerivWithinDomain (Y : Set X) (d : X) : Set (X × ℝ) :=
  {p : X × ℝ | p.1 ∈ Y ∧ 0 < p.2 ∧ p.1 + p.2 • d ∈ Y}

/-- Membership in `clarkeDirectionalDerivWithinDomain Y d` means that both the base point and the
forward step used in the Clarke difference quotient stay in `Y`, with positive time. -/
theorem mem_clarkeDirectionalDerivWithinDomain {Y : Set X} {d : X} {p : X × ℝ} :
    p ∈ clarkeDirectionalDerivWithinDomain Y d ↔ p.1 ∈ Y ∧ 0 < p.2 ∧ p.1 + p.2 • d ∈ Y :=
  Iff.rfl

/-- Source notion for Chapter14 Definition 14.1-extra-1 (4): the Clarke generalized
directional derivative is the joint limsup of the difference quotient as `y → x` and
`t → 0` through positive scalars, restricted to admissible pairs `y ∈ Y` and
`y + t • d ∈ Y`. Local Lipschitz hypotheses belong to the later theorem layer, not to
this source-facing owner itself, so the codomain is `EReal` rather than `ℝ`. -/
def clarkeDirectionalDerivWithin (Y : Set X) (f : X → ℝ) (x : Y) (d : X) : EReal :=
  Filter.limsup
    (fun p : X × ℝ ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))
    (nhdsWithin ((x : X), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Y d))

/-- Unfolding formula for `clarkeDirectionalDerivWithin`. -/
theorem clarkeDirectionalDerivWithin_eq_limsup (Y : Set X) (f : X → ℝ) (x : Y) (d : X) :
    clarkeDirectionalDerivWithin Y f x d =
      Filter.limsup
        (fun p : X × ℝ ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))
        (nhdsWithin ((x : X), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Y d)) := rfl

/-- Helper for Chapter14 Definition 14.1-extra-1: the constant-base embedding
`t ↦ ((x : X), t)` sends the upper-Dini time filter into the admissible Clarke-pair filter. -/
theorem constantBasePair_tendsto_clarkeDirectionalDerivWithinDomain
    {Y : Set X} {x : Y} {d : X} :
    Tendsto
      (fun t : ℝ ↦ ((x : X), t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0 ∩ {t : ℝ | (x : X) + t • d ∈ Y}))
      (nhdsWithin ((x : X), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Y d)) := by
  -- The map `t ↦ ((x : X), t)` tends to `(x, 0)` and preserves Clarke admissibility by
  -- construction of the source filter.
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · simpa using
      Filter.Tendsto.prodMk_nhds
        (tendsto_const_nhds :
          Tendsto
            (fun _ : ℝ ↦ (x : X))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0 ∩ {t : ℝ | (x : X) + t • d ∈ Y}))
            (nhds (x : X)))
        (tendsto_nhds_of_tendsto_nhdsWithin tendsto_id)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨x.2, ht.1, ht.2⟩

/-- Consequence from Chapter14 Definition 14.1-extra-1 (5): if `f` is Lipschitz near `x`
within `Y`, then its upper Dini directional derivative is bounded above by its Clarke
directional derivative in every direction. -/
theorem upperDiniDirectionalDerivWithin_le_clarkeDirectionalDerivWithin
    {Y : Set X} {f : X → ℝ} {x : Y} {d : X} (h_local : LocallyLipschitzWithinAt Y f x) :
    upperDiniDirectionalDerivWithin Y f x d ≤ clarkeDirectionalDerivWithin Y f x d := by
  -- The local Lipschitz hypothesis is part of the source statement, even though this inequality
  -- itself follows from the filter comparison alone.
  let _ := h_local
  -- The upper-Dini quotient is the Clarke quotient specialized along the constant-base path
  -- `t ↦ ((x : X), t)`.
  rw [upperDiniDirectionalDerivWithin_eq_limsup, clarkeDirectionalDerivWithin_eq_limsup]
  -- Route correction: compare limsups through an explicit composed quotient instead of an `ext`
  -- step on `EReal`.
  let u : X × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
  let v : ℝ → X × ℝ := fun t ↦ ((x : X), t)
  have hcomp :
      u ∘ v = fun t : ℝ ↦ (((f ((x : X) + t • d) - f x) / t : ℝ) : EReal) := by
    -- Evaluating the Clarke quotient along the constant-base path gives the upper-Dini quotient.
    funext t
    simp [u, v, Function.comp]
  rw [← hcomp]
  simpa [u, v] using
    (Tendsto.limsup_comp_le_limsup
      (β := EReal)
      (hv := constantBasePair_tendsto_clarkeDirectionalDerivWithinDomain
        (Y := Y) (x := x) (d := d))
      (u := u))

/-- Chapter14 Definition 14.1-extra-1 (6): if the directional derivative exists at `x` in the
direction `d`, then it agrees with the upper Dini directional derivative. -/
theorem upperDiniDirectionalDerivWithin_eq_of_hasDirectionalDerivWithinAt
    {Y : Set X} {f : X → ℝ} {f' : ℝ} {x : Y} {d : X}
    (h : HasDirectionalDerivWithinAt Y f f' x d) :
    upperDiniDirectionalDerivWithin Y f x d = (f' : EReal) := by
  let g : ℝ → ℝ := fun t ↦ f ((x : X) + t • d)
  let A : Set ℝ := {t : ℝ | (x : X) + t • d ∈ Y}
  -- The trace hypothesis keeps the upper-Dini filter nontrivial by identifying it with the
  -- usual right-neighborhood filter after restricting to admissible times.
  have hsource_ne : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0 ∩ A)) := by
    have hrestrict :
        nhdsWithin (0 : ℝ) (Set.Ioi 0) = nhdsWithin (0 : ℝ) (Set.Ioi 0 ∩ A) := by
      simpa [A] using
        (nhdsWithin_restrict'' (Set.Ioi (0 : ℝ)) h.hasDirectionalTraceWithinDomain)
    rw [← hrestrict]
    rw [← mem_closure_iff_nhdsWithin_neBot]
    simp [closure_Ioi]
  letI := hsource_ne
  have hslope :
      Tendsto
        (slope g 0)
        (nhdsWithin (0 : ℝ) (directionalDerivWithinDomain Y x d \ ({0} : Set ℝ)))
        (nhds f') := by
    simpa [g] using (hasDerivWithinAt_iff_tendsto_slope.mp h.hasDerivWithinAt)
  have hslopeEReal :
      Tendsto
        (fun t : ℝ ↦ ((slope g 0 t : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (directionalDerivWithinDomain Y x d \ ({0} : Set ℝ)))
        (nhds (f' : EReal)) := by
    exact (EReal.tendsto_coe).2 hslope
  have hquot :
      Tendsto
        (fun t : ℝ ↦ (((f ((x : X) + t • d) - f x) / t : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0 ∩ A))
        (nhds (f' : EReal)) := by
    rw [← directionalDerivWithinDomain_sdiff_zero_eq (Y := Y) (x := x) (d := d)]
    refine Filter.Tendsto.congr' ?_ hslopeEReal
    refine Filter.Eventually.of_forall ?_
    intro t
    simp [g, slope_def_field]
  -- Once the quotient has an honest limit, its limsup is exactly that limit.
  rw [upperDiniDirectionalDerivWithin_eq_limsup]
  simpa [A] using hquot.limsup_eq

/-- Source notion for Chapter14 Definition 14.1-extra-1 (7): `f` is directionally
differentiable at `x` within `Y` when every direction `d` admits a directional derivative
value `f'(x; d)`. -/
class DirectionallyDifferentiableWithinAt (Y : Set X) (f : X → ℝ) (x : Y) : Prop where
  /-- Every direction has a right directional derivative at `x` within the domain `Y`. -/
  exists_hasDirectionalDerivWithinAt (d : X) :
    ∃ f' : ℝ, HasDirectionalDerivWithinAt Y f f' x d

/-- `DirectionallyDifferentiableWithinAt Y f x` is proposition-valued. -/
instance directionallyDifferentiableWithinAt_subsingleton
    (Y : Set X) (f : X → ℝ) (x : Y) :
    Subsingleton (DirectionallyDifferentiableWithinAt Y f x) := inferInstance

/-- Unfolding formula for `DirectionallyDifferentiableWithinAt`. -/
theorem directionallyDifferentiableWithinAt_iff {Y : Set X} {f : X → ℝ} {x : Y} :
    DirectionallyDifferentiableWithinAt Y f x ↔
      ∀ d : X, ∃ f' : ℝ, HasDirectionalDerivWithinAt Y f f' x d := by
  constructor
  · intro h
    exact h.exists_hasDirectionalDerivWithinAt
  · intro h
    exact ⟨h⟩

private theorem directionalDerivWithinDomain_univ (x d : X) :
    directionalDerivWithinDomain Set.univ ⟨x, by simp⟩ d = Set.Ici 0 := by
  ext t
  simp [directionalDerivWithinDomain]

/-- On the whole space, the source directional-derivative owner specializes to the chapter's
one-sided directional derivative owner. -/
theorem hasDirectionalDerivWithinAt_univ_iff_hasOneSidedDirectionalDerivAt
    {f : X → ℝ} {f' : ℝ} {x d : X} :
    HasDirectionalDerivWithinAt Set.univ f f' ⟨x, by simp⟩ d ↔
      HasOneSidedDirectionalDerivAt f f' x d := by
  rw [hasDirectionalDerivWithinAt_iff]
  constructor
  · rintro ⟨_, hderiv⟩
    rw [HasOneSidedDirectionalDerivAt]
    simpa [directionalDerivWithinDomain_univ x d] using hderiv
  · intro h
    refine ⟨?_, ?_⟩
    · rw [hasDirectionalTraceWithinDomain_iff]
      exact Filter.Eventually.of_forall (fun t ↦ by simp)
    · rw [HasOneSidedDirectionalDerivAt] at h
      simpa [directionalDerivWithinDomain_univ x d] using h

/-- On the whole space, `directionalDerivWithin` recovers the chapter's one-sided directional
derivative owner. -/
theorem directionalDerivWithin_univ_eq_oneSidedDirectionalDeriv
    (f : X → ℝ) (x d : X) :
    directionalDerivWithin Set.univ f ⟨x, by simp⟩ d = oneSidedDirectionalDeriv f x d := by
  unfold directionalDerivWithin oneSidedDirectionalDeriv
  rw [directionalDerivWithinDomain_univ x d]

/-- On the whole space, directional differentiability is exactly per-direction existence of the
chapter's one-sided directional derivative. -/
theorem directionallyDifferentiableWithinAt_univ_iff
    {f : X → ℝ} {x : X} :
    DirectionallyDifferentiableWithinAt Set.univ f ⟨x, by simp⟩ ↔
      ∀ d : X, ∃ f' : ℝ, HasOneSidedDirectionalDerivAt f f' x d := by
  rw [directionallyDifferentiableWithinAt_iff]
  constructor
  · intro h d
    rcases h d with ⟨f', hf'⟩
    exact ⟨f', hasDirectionalDerivWithinAt_univ_iff_hasOneSidedDirectionalDerivAt.mp hf'⟩
  · intro h d
    rcases h d with ⟨f', hf'⟩
    exact ⟨f', hasDirectionalDerivWithinAt_univ_iff_hasOneSidedDirectionalDerivAt.mpr hf'⟩

/-- Source notion for Chapter14 Definition 14.1-extra-1 (8): `f` is regular at `x` within
`Y` when it is directionally differentiable there, is Lipschitz near `x` within `Y`, and
its directional derivative agrees with the Clarke derivative in every direction. -/
class ClarkeRegularWithinAt (Y : Set X) (f : X → ℝ) (x : Y) : Prop where
  /-- A regular point is locally Lipschitz relative to the domain. -/
  locallyLipschitzWithinAt : LocallyLipschitzWithinAt Y f x
  /-- A regular point is directionally differentiable in every direction. -/
  directionallyDifferentiableWithinAt : DirectionallyDifferentiableWithinAt Y f x
  /-- At a regular point, the directional and Clarke derivatives coincide in every direction. -/
  clarke_eq_directional (d : X) :
    (directionalDerivWithin Y f x d : EReal) = clarkeDirectionalDerivWithin Y f x d

/-- `ClarkeRegularWithinAt Y f x` is proposition-valued. -/
instance clarkeRegularWithinAt_subsingleton (Y : Set X) (f : X → ℝ) (x : Y) :
    Subsingleton (ClarkeRegularWithinAt Y f x) := inferInstance

/-- Unfolding formula for `ClarkeRegularWithinAt`. -/
theorem clarkeRegularWithinAt_iff {Y : Set X} {f : X → ℝ} {x : Y} :
    ClarkeRegularWithinAt Y f x ↔
      LocallyLipschitzWithinAt Y f x ∧
        DirectionallyDifferentiableWithinAt Y f x ∧
          ∀ d : X, (directionalDerivWithin Y f x d : EReal) =
            clarkeDirectionalDerivWithin Y f x d := by
  constructor
  · intro h
    exact ⟨h.locallyLipschitzWithinAt, h.directionallyDifferentiableWithinAt,
      h.clarke_eq_directional⟩
  · rintro ⟨h_local, h_dir, h_eq⟩
    exact ⟨h_local, h_dir, h_eq⟩

/-- Source notion for Chapter14 Definition 14.1-extra-1 (9): `f` is regular on `Y` when it
is regular at every point of the domain `Y`, hence locally Lipschitz and directionally
differentiable there. -/
class ClarkeRegularOn (Y : Set X) (f : X → ℝ) : Prop where
  /-- Every point of `Y` is a Clarke-regular point of `f`. -/
  regular_at (x : Y) : ClarkeRegularWithinAt Y f x

/-- `ClarkeRegularOn Y f` is proposition-valued. -/
instance clarkeRegularOn_subsingleton (Y : Set X) (f : X → ℝ) :
    Subsingleton (ClarkeRegularOn Y f) := inferInstance

/-- Unfolding formula for `ClarkeRegularOn`. -/
theorem clarkeRegularOn_iff {Y : Set X} {f : X → ℝ} :
    ClarkeRegularOn Y f ↔ ∀ x : Y, ClarkeRegularWithinAt Y f x := by
  constructor
  · intro h
    exact h.regular_at
  · intro h
    exact ⟨h⟩

end

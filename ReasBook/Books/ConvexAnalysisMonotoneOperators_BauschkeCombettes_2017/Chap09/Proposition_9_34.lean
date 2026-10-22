/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Corollary_9_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_33

-- Declarations for this item will be appended below by the statement pipeline.

open Set Filter
open scoped Topology

namespace ERealFunction

attribute [local instance] Classical.propDecidable

/-- The open real interval cut out by the extended-real endpoints `α` and `β`. -/
def erealOpenInterval (α β : EReal) : Set ℝ :=
  ((↑) : ℝ → EReal) ⁻¹' Set.Ioo α β

/-- A real number lies in `erealOpenInterval α β` exactly when its `EReal` coercion lies strictly
between `α` and `β`. -/
@[simp] theorem mem_erealOpenInterval_iff {α β : EReal} {x : ℝ} :
    x ∈ erealOpenInterval α β ↔ α < (x : EReal) ∧ (x : EReal) < β :=
  Iff.rfl

/-- The one-sided-limit extension of a function with domain `]α,β[`:
it agrees with `g` on the open interval, takes the right and left `Filter.liminf` values at finite
endpoints, and is `+∞` elsewhere. -/
noncomputable def oneSidedLimitExtensionEReal
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal) : ℝ → EReal :=
  fun x ↦
    if x ∈ erealOpenInterval α β then
      g x
    else if α = (x : EReal) then
      Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x))
    else if β = (x : EReal) then
      Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x))
    else
      ⊤

/-- On `]α,β[`, the one-sided-limit extension agrees with `g`. -/
-- Proof sketch: unfold `oneSidedLimitExtensionEReal` and evaluate the first branch of the defining
-- piecewise formula.
@[simp] theorem oneSidedLimitExtensionEReal_apply_of_mem_erealOpenInterval
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal) {x : ℝ}
    (hx : x ∈ erealOpenInterval α β) :
    oneSidedLimitExtensionEReal g α β x = g x := by
  -- On interior points, the first branch of the piecewise definition is active.
  simp [oneSidedLimitExtensionEReal, hx]

/-- If the one-sided boundary liminf values stay above `-∞`, then the one-sided-limit extension is
everywhere `]-∞,+∞]`-valued. -/
-- Proof sketch: split according to the four branches in the definition; on the interior use the
-- subtype codomain of `g`, on the two boundary branches use the corresponding hypotheses, and
-- outside the interval use the fact that `⊤ > ⊥`.
theorem oneSidedLimitExtensionEReal_ne_bot
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)))
    (x : ℝ) :
    ⊥ < oneSidedLimitExtensionEReal g α β x := by
  -- Evaluate the active branch and use the corresponding lower-bound witness.
  unfold oneSidedLimitExtensionEReal
  split_ifs with hx hxα hxβ
  · exact (g x).2
  · exact hαlim hxα
  · exact hβlim hxβ
  · simp

/-- The subtype-valued one-sided-limit extension associated with `oneSidedLimitExtensionEReal`. -/
noncomputable def oneSidedLimitExtension
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x))) :
    ℝ → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨oneSidedLimitExtensionEReal g α β x,
      oneSidedLimitExtensionEReal_ne_bot g α β hαlim hβlim x⟩

/-- Coercing the subtype-valued one-sided-limit extension to `EReal` recovers the explicit
piecewise extension formula. -/
-- Proof sketch: unfold `oneSidedLimitExtension`.
@[simp] theorem oneSidedLimitExtension_coe
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)))
    (x : ℝ) :
    (oneSidedLimitExtension g α β hαlim hβlim x : EReal) =
      oneSidedLimitExtensionEReal g α β x := by
  -- Coercing out of the subtype simply forgets the proof component.
  rfl

/-- Helper for Proposition 9.34: outside the effective domain of an `]-∞,+∞]`-valued function,
the value is forced to be `+∞`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {g : ℝ → Set.Ioi (⊥ : EReal)} {x : ℝ} (hx : x ∉ effectiveDomain g) :
    (g x : EReal) = ⊤ := by
  -- A finite value would place `x` back in the effective domain.
  by_contra htop
  exact hx (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

/-- Helper for Proposition 9.34: if a function is already `+∞` outside a set, then its ordinary
`liminf` agrees with the bounded `bliminf` restricted to that set. -/
private theorem liminf_eq_bliminf_of_eq_top_outside
    {X : Type*} {f : Filter X} (u : X → EReal) (p : X → Prop)
    (hout : ∀ x, ¬ p x → u x = ⊤) :
    Filter.liminf u f = Filter.bliminf u f p := by
  -- The implication-form eventually bound is equivalent to the ordinary one because the
  -- off-domain values are all `⊤`.
  rw [Filter.liminf_eq, Filter.bliminf_eq]
  apply le_antisymm
  · refine sSup_le ?_
    intro a ha
    exact le_sSup (ha.mono fun x hx _ ↦ hx)
  · refine sSup_le ?_
    intro a ha
    have hall : ∀ᶠ x in f, a ≤ u x := by
      filter_upwards [ha] with x hx
      by_cases hp : p x
      · exact hx hp
      · simpa [hout x hp] using (le_top : a ≤ (⊤ : EReal))
    exact le_sSup hall

/-- Helper for Proposition 9.34: the real preimage of an `EReal` open interval is convex. -/
private theorem convex_erealOpenInterval (α β : EReal) :
    Convex ℝ (erealOpenInterval α β) := by
  -- The real coercion into `EReal` is monotone, so order-connected interval preimages stay
  -- order-connected, hence convex on `ℝ`.
  rw [convex_iff_ordConnected]
  simpa [erealOpenInterval] using
    (ordConnected_Ioo.preimage_mono
      (show Monotone ((↑) : ℝ → EReal) from EReal.coe_strictMono.monotone))

/-- Helper for Proposition 9.34: strict convexity on a nonempty interval domain yields the weak
convexity inequality on the effective domain. -/
private theorem convexOn_effectiveDomain_of_strictlyConvex
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal) (hαβ : α < β)
    (hdom : effectiveDomain g = erealOpenInterval α β) (hstrict : StrictlyConvex g) :
    ConvexOn g (effectiveDomain g) := by
  refine ⟨?_, subset_rfl, ?_⟩
  · -- The strict inequality `α < β` provides one interior point of the effective domain.
    rcases EReal.lt_iff_exists_real_btwn.mp hαβ with ⟨x, hxα, hxβ⟩
    refine ⟨x, ?_⟩
    rw [hdom, mem_erealOpenInterval_iff]
    exact ⟨hxα, hxβ⟩
  · intro x hx y hy a ha0 ha1
    by_cases hxy : x = y
    · -- For equal endpoints, the Jensen bound is an equality by collapsing the weights.
      subst y
      have hcombo : a • x + (1 - a) • x = x := by
        calc
          a • x + (1 - a) • x = (a + (1 - a)) • x := by rw [add_smul]
          _ = x := by simp
      have ha_nonneg : 0 ≤ (a : EReal) := by
        exact_mod_cast ha0.le
      have hb_nonneg : 0 ≤ ((1 - a : ℝ) : EReal) := by
        exact_mod_cast (sub_nonneg.mpr ha1.le)
      have hsum : (a : EReal) + (1 - a : EReal) = 1 := by
        exact_mod_cast (show a + (1 - a : ℝ) = 1 by ring)
      have hweight :
          (a : EReal) * (g x : EReal) + (1 - a : EReal) * (g x : EReal) = (g x : EReal) := by
        calc
          (a : EReal) * (g x : EReal) + (1 - a : EReal) * (g x : EReal)
              = ((a : EReal) + (1 - a : EReal)) * (g x : EReal) := by
                  symm
                  exact EReal.right_distrib_of_nonneg ha_nonneg hb_nonneg
          _ = (g x : EReal) := by rw [hsum, one_mul]
      calc
        (g (a • x + (1 - a) • x) : EReal) = g x := by
          simpa using congrArg (fun t : ℝ ↦ (g t : EReal)) hcombo
        _ ≤ (a : EReal) * (g x : EReal) + (1 - a : EReal) * (g x : EReal) := by
          rw [hweight]
    · -- For distinct points, the defining strict Jensen inequality is stronger than convexity.
      exact le_of_lt (hstrict hx hy hxy ha0 ha1)

/-- Helper for Proposition 9.34: the open interval domain is open, so Corollary 8.39 upgrades
convexity to continuity of the finite real representative on that whole domain. -/
private theorem continuousOn_toReal_of_open_interval_domain
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)
    (hdom : effectiveDomain g = erealOpenInterval α β)
    (hconv : ConvexOn g (effectiveDomain g)) :
    ContinuousOn (fun x : ℝ ↦ (g x : EReal).toReal) (effectiveDomain g) := by
  have hopen : IsOpen (effectiveDomain g) := by
    rw [hdom, erealOpenInterval]
    exact continuous_coe_real_ereal.isOpen_preimage _ isOpen_Ioo
  intro x hx
  have hEq :=
    continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
      (f := g) hconv (Or.inr (Or.inr (inferInstance : FiniteDimensional ℝ ℝ)))
  have hxint : x ∈ interior (effectiveDomain g) := by
    simpa [hopen.interior_eq] using hx
  have hxcontset :
      x ∈ {x : ℝ | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain g ∧
        ContinuousAt (fun y : ℝ ↦ (g y : EReal).toReal) x} := by
    rw [hEq]
    exact hxint
  rcases hxcontset with ⟨ρ, hρ, hball, hcont⟩
  -- The local continuity witness from Corollary 8.39 yields continuity on the open domain.
  exact hcont.continuousWithinAt

/-- Helper for Proposition 9.34: the frontier of the real preimage of the `EReal` open interval is
exactly the set of real points whose coercion equals one of the endpoints. -/
private theorem frontier_erealOpenInterval (α β : EReal) (hαβ : α < β) :
    frontier (erealOpenInterval α β) =
      {x : ℝ | (x : EReal) = α ∨ (x : EReal) = β} := by
  -- The real coercion is an open embedding, so it preserves interval frontiers by preimage.
  rw [erealOpenInterval]
  rw [(EReal.isOpenEmbedding_coe.isOpenMap.preimage_frontier_eq_frontier_preimage
      continuous_coe_real_ereal (Set.Ioo α β)).symm]
  ext x
  simp [frontier_Ioo hαβ]

/-- Helper for Proposition 9.34: the closure of the real preimage of the `EReal` open interval is
the corresponding closed interval cut out by `α` and `β`. -/
private theorem closure_erealOpenInterval (α β : EReal) (hαβ : α < β) :
    closure (erealOpenInterval α β) =
      {x : ℝ | α ≤ (x : EReal) ∧ (x : EReal) ≤ β} := by
  -- The same open-embedding argument transports the standard closure formula.
  rw [erealOpenInterval]
  rw [(EReal.isOpenEmbedding_coe.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_coe_real_ereal (Set.Ioo α β)).symm]
  ext x
  simp [closure_Ioo hαβ.ne]

/-- Helper for Proposition 9.34: at the left endpoint, the neighborhood liminf reduces to the
right-sided liminf because the function is already `+∞` on the forbidden side. -/
private theorem liminfAt_eq_right_liminf_of_open_interval_domain
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)
    (hαβ : α < β) (hdom : effectiveDomain g = erealOpenInterval α β)
    {x : ℝ} (hxa : α = (x : EReal)) :
    liminfAt (fun y : ℝ ↦ (g y : EReal)) x =
      Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)) := by
  have hs_convex : Convex ℝ (effectiveDomain g) := by
    -- The interval-domain hypothesis puts the effective domain in the 1D convex-order setting.
    rw [hdom]
    exact convex_erealOpenInterval α β
  have hx_not_mem : x ∉ effectiveDomain g := by
    -- The left endpoint itself is excluded from the open interval domain.
    intro hx
    rw [hdom, mem_erealOpenInterval_iff] at hx
    have hxlt : ¬ α < (x : EReal) := by
      simpa [hxa]
    exact hxlt hx.1
  have hx_closure : x ∈ closure (effectiveDomain g) := by
    -- The closure description shows that the endpoint lies in the closed interval.
    rw [hdom, closure_erealOpenInterval α β hαβ]
    constructor
    · simpa [hxa]
    · simpa [hxa] using hαβ.le
  have hs_left_empty : effectiveDomain g ∩ Set.Iio x = ∅ := by
    -- No effective-domain point can lie strictly to the left of the left endpoint.
    ext y
    constructor
    · intro hy
      exfalso
      rcases hy with ⟨hy, hylt⟩
      rw [hdom, mem_erealOpenInterval_iff] at hy
      have hylt' : (y : EReal) < α := by
        simpa [hxa] using hylt
      exact not_le_of_gt hylt' hy.1.le
    · intro hy
      simp at hy
  have hs_right_nonempty : (effectiveDomain g ∩ Set.Ioi x).Nonempty := by
    -- The strict inequality `α < β` provides one domain point to the right of the endpoint.
    rcases EReal.lt_iff_exists_real_btwn.mp (hxa ▸ hαβ) with ⟨y, hyα, hyβ⟩
    refine ⟨y, ?_⟩
    constructor
    · rw [hdom, mem_erealOpenInterval_iff]
      exact ⟨by simpa [hxa] using hyα, hyβ⟩
    · simpa [hxa] using hyα
  have hnhds : nhdsWithin x (effectiveDomain g) = nhdsWithin x (Set.Ioi x) := by
    -- Convex one-dimensional neighborhood geometry collapses the domain filter to the right-hand
    -- neighborhood because only the interior side is available.
    calc
      nhdsWithin x (effectiveDomain g) = 𝓝[effectiveDomain g \ {x}] x := by
        simp [hx_not_mem]
      _ = 𝓝[>] x := by
        simpa using
          hs_convex.nhdsWithin_diff_eq_nhdsGT hx_closure hs_left_empty hs_right_nonempty
      _ = nhdsWithin x (Set.Ioi x) := rfl
  have hout : ∀ y, y ∉ effectiveDomain g → (g y : EReal) = ⊤ := by
    -- Outside the effective domain, `g` is already on the `+∞` branch.
    intro y hy
    exact value_eq_top_of_not_mem_effectiveDomain hy
  -- Replace the ordinary liminf by the bounded liminf over the effective domain, then identify
  -- that restricted filter with the right-sided neighborhood filter.
  calc
    liminfAt (fun y : ℝ ↦ (g y : EReal)) x =
        Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhds x) := rfl
    _ = Filter.bliminf (fun y : ℝ ↦ (g y : EReal)) (nhds x)
          (fun y ↦ y ∈ effectiveDomain g) := by
        exact
          liminf_eq_bliminf_of_eq_top_outside (f := nhds x)
            (fun y : ℝ ↦ (g y : EReal)) (fun y ↦ y ∈ effectiveDomain g) hout
    _ = Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (effectiveDomain g)) := by
        rw [Filter.bliminf_eq_liminf]
        rfl
    _ = Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)) := by
        rw [hnhds]

/-- Helper for Proposition 9.34: at the right endpoint, the neighborhood liminf reduces to the
left-sided liminf because the function is already `+∞` on the forbidden side. -/
private theorem liminfAt_eq_left_liminf_of_open_interval_domain
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)
    (hαβ : α < β) (hdom : effectiveDomain g = erealOpenInterval α β)
    {x : ℝ} (hxb : β = (x : EReal)) :
    liminfAt (fun y : ℝ ↦ (g y : EReal)) x =
      Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)) := by
  have hs_convex : Convex ℝ (effectiveDomain g) := by
    -- The interval-domain hypothesis again gives a convex one-dimensional effective domain.
    rw [hdom]
    exact convex_erealOpenInterval α β
  have hx_not_mem : x ∉ effectiveDomain g := by
    -- The right endpoint itself is excluded from the open interval domain.
    intro hx
    rw [hdom, mem_erealOpenInterval_iff] at hx
    have hxlt : ¬ (x : EReal) < β := by
      simpa [hxb]
    exact hxlt hx.2
  have hx_closure : x ∈ closure (effectiveDomain g) := by
    -- The closure formula again places the endpoint in the closed interval.
    rw [hdom, closure_erealOpenInterval α β hαβ]
    constructor
    · have hαx : α ≤ β := hαβ.le
      simpa [hxb] using hαx
    · simpa [hxb]
  have hs_right_empty : effectiveDomain g ∩ Set.Ioi x = ∅ := by
    -- No effective-domain point can lie strictly to the right of the right endpoint.
    ext y
    constructor
    · intro hy
      exfalso
      rcases hy with ⟨hy, hygt⟩
      rw [hdom, mem_erealOpenInterval_iff] at hy
      have hygt' : β < (y : EReal) := by
        simpa [hxb] using hygt
      exact not_le_of_gt hygt' hy.2.le
    · intro hy
      simp at hy
  have hs_left_nonempty : (effectiveDomain g ∩ Set.Iio x).Nonempty := by
    -- The same strict inequality `α < β` gives one domain point to the left of the endpoint.
    rcases EReal.lt_iff_exists_real_btwn.mp (hαβ.trans_eq hxb) with ⟨y, hyα, hyβ⟩
    refine ⟨y, ?_⟩
    constructor
    · rw [hdom, mem_erealOpenInterval_iff]
      exact ⟨hyα, by simpa [hxb] using hyβ⟩
    · simpa [hxb] using hyβ
  have hnhds : nhdsWithin x (effectiveDomain g) = nhdsWithin x (Set.Iio x) := by
    -- Only the interior left-hand side contributes to the neighborhood filter at the endpoint.
    calc
      nhdsWithin x (effectiveDomain g) = 𝓝[effectiveDomain g \ {x}] x := by
        simp [hx_not_mem]
      _ = 𝓝[<] x := by
        simpa using
          hs_convex.nhdsWithin_diff_eq_nhdsLT hx_closure hs_left_nonempty hs_right_empty
      _ = nhdsWithin x (Set.Iio x) := rfl
  have hout : ∀ y, y ∉ effectiveDomain g → (g y : EReal) = ⊤ := by
    -- Outside the effective domain, the function is again identically `+∞`.
    intro y hy
    exact value_eq_top_of_not_mem_effectiveDomain hy
  -- As on the left endpoint, move from the full-neighborhood liminf to the effective-domain
  -- bounded liminf, then identify the restricted filter with the one-sided neighborhood filter.
  calc
    liminfAt (fun y : ℝ ↦ (g y : EReal)) x =
        Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhds x) := rfl
    _ = Filter.bliminf (fun y : ℝ ↦ (g y : EReal)) (nhds x)
          (fun y ↦ y ∈ effectiveDomain g) := by
        exact
          liminf_eq_bliminf_of_eq_top_outside (f := nhds x)
            (fun y : ℝ ↦ (g y : EReal)) (fun y ↦ y ∈ effectiveDomain g) hout
    _ = Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (effectiveDomain g)) := by
        rw [Filter.bliminf_eq_liminf]
        rfl
    _ = Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)) := by
        rw [hnhds]

/-- Helper for Proposition 9.34: convexity on the effective domain is equivalent to convexity of
the `EReal` epigraph of the coerced function. -/
private theorem convex_epigraph_coe_of_convexOn_effectiveDomain
    (g : ℝ → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn g (effectiveDomain g)) :
    Convex ℝ (epigraph (fun x : ℝ ↦ (g x : EReal))) := by
  -- Rewrite the stored Jensen inequality into the standard epigraph criterion.
  refine (convex_epigraph_iff_jensen_on_dom (fun x : ℝ ↦ (g x : EReal))).2 ?_
  intro x y hx hy a ha0 ha1
  have hx' : x ∈ effectiveDomain g := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain g := by
    simpa [effectiveDomain, dom] using hy
  simpa using hconv.ineq hx' hy' ha0 ha1

/-- Helper for Proposition 9.34: the Chapter 9 boundary extension agrees pointwise with the
explicit one-sided extension on the open interval `]α,β[`. -/
private theorem boundaryLiminfExtensionEReal_eq_oneSidedLimitExtensionEReal
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal) (hαβ : α < β)
    (hdom : effectiveDomain g = erealOpenInterval α β) :
    boundaryLiminfExtensionEReal g = oneSidedLimitExtensionEReal g α β := by
  funext x
  by_cases hxdom : x ∈ effectiveDomain g
  · -- On interior points, both constructions use the original value of `g`.
    have hxint : x ∈ erealOpenInterval α β := by
      simpa [hdom] using hxdom
    simp [boundaryLiminfExtensionEReal, oneSidedLimitExtensionEReal, hxdom, hxint]
  · by_cases hxa : α = (x : EReal)
    · -- On the left endpoint, the frontier branch of the boundary extension matches the explicit
      -- one-sided right liminf.
      have hxf : x ∈ frontier (effectiveDomain g) := by
        rw [hdom, frontier_erealOpenInterval α β hαβ]
        exact Or.inl (by simpa [hxa])
      have hxb : ¬ β = (x : EReal) := by
        intro hxb
        have hbad : α < α := by
          simpa [hxa, hxb] using hαβ
        exact lt_irrefl _ hbad
      have hxint : x ∉ erealOpenInterval α β := by
        simpa [hdom] using hxdom
      calc
        boundaryLiminfExtensionEReal g x = liminfAt (fun y : ℝ ↦ (g y : EReal)) x := by
          simp [boundaryLiminfExtensionEReal, hxdom, hxf]
        _ = Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)) :=
          liminfAt_eq_right_liminf_of_open_interval_domain g α β hαβ hdom hxa
        _ = oneSidedLimitExtensionEReal g α β x := by
          simp [oneSidedLimitExtensionEReal, hxint, hxa, hxb]
    · by_cases hxb : β = (x : EReal)
      · -- The right endpoint is the symmetric frontier case.
        have hxf : x ∈ frontier (effectiveDomain g) := by
          rw [hdom, frontier_erealOpenInterval α β hαβ]
          exact Or.inr (by simpa [hxb])
        have hxint : x ∉ erealOpenInterval α β := by
          simpa [hdom] using hxdom
        calc
          boundaryLiminfExtensionEReal g x = liminfAt (fun y : ℝ ↦ (g y : EReal)) x := by
            simp [boundaryLiminfExtensionEReal, hxdom, hxf]
          _ = Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)) :=
            liminfAt_eq_left_liminf_of_open_interval_domain g α β hαβ hdom hxb
          _ = oneSidedLimitExtensionEReal g α β x := by
            simp [oneSidedLimitExtensionEReal, hxint, hxa, hxb]
      · -- Away from the closed interval, both extensions are on the `+∞` branch.
        have hxf : x ∉ frontier (effectiveDomain g) := by
          intro hxfront
          rw [hdom, frontier_erealOpenInterval α β hαβ] at hxfront
          rcases hxfront with hxα | hxβ
          · exact hxa hxα.symm
          · exact hxb hxβ.symm
        have hxint : x ∉ erealOpenInterval α β := by
          simpa [hdom] using hxdom
        simp [boundaryLiminfExtensionEReal, oneSidedLimitExtensionEReal, hxdom, hxf, hxint, hxa,
          hxb]

-- Proof sketch: first identify the one-sided-limit extension with the lower semicontinuous hull of
-- `g`; the hull is lower semicontinuous, and because `g` is already convex on the open interval
-- `]α,β[`, the extension stays convex on its effective domain. Packaging these properties yields
-- membership in `Γ₀(ℝ)`.
/-- The one-sided-limit extension from Proposition 9.34 belongs to `Γ₀(ℝ)`. -/
theorem oneSidedLimitExtension_mem_gammaZero
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal) (hαβ : α < β)
    (hdom : effectiveDomain g = erealOpenInterval α β)
    (hstrict : StrictlyConvex g)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x))) :
    oneSidedLimitExtension g α β hαlim hβlim ∈ Γ₀(ℝ) := by
  let hconv :=
    convexOn_effectiveDomain_of_strictlyConvex g α β hαβ hdom hstrict
  have hopen : IsOpen (effectiveDomain g) := by
    -- The effective domain is the real preimage of an open `EReal` interval.
    rw [hdom, erealOpenInterval]
    exact continuous_coe_real_ereal.isOpen_preimage _ isOpen_Ioo
  have hcont :=
    continuousOn_toReal_of_open_interval_domain g α β hdom hconv
  have hEReal_eq :
      boundaryLiminfExtensionEReal g = oneSidedLimitExtensionEReal g α β :=
    boundaryLiminfExtensionEReal_eq_oneSidedLimitExtensionEReal g α β hαβ hdom
  have hfun_eq :
      boundaryLiminfExtension g hconv hopen hcont =
        oneSidedLimitExtension g α β hαlim hβlim := by
    -- The subtype-valued extensions agree because their `EReal` coercions agree pointwise.
    funext x
    apply Subtype.ext
    calc
      (boundaryLiminfExtension g hconv hopen hcont x : EReal) =
          boundaryLiminfExtensionEReal g x :=
        boundaryLiminfExtension_coe g hconv hopen hcont x
      _ = oneSidedLimitExtensionEReal g α β x :=
        congrFun hEReal_eq x
      _ = (oneSidedLimitExtension g α β hαlim hβlim x : EReal) :=
        (oneSidedLimitExtension_coe g α β hαlim hβlim x).symm
  -- Rewrite the Chapter 9 boundary-extension result along the pointwise identification.
  simpa [hfun_eq] using boundaryLiminfExtension_mem_gammaZero g hconv hopen hcont

-- Proof sketch: on the open interval `]α,β[` the extension agrees with `g`, at finite endpoints
-- it is defined by the corresponding one-sided limit, and away from the closed interval it is
-- `+∞`; this is exactly the lower semicontinuous-hull construction for a convex function with
-- interval domain.
/-- The one-sided-limit extension coincides with the lower semicontinuous hull of `g`. -/
theorem oneSidedLimitExtensionEReal_eq_lowerSemicontinuousEnvelope
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal) (hαβ : α < β)
    (hdom : effectiveDomain g = erealOpenInterval α β)
    (hstrict : StrictlyConvex g)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x))) :
    oneSidedLimitExtensionEReal g α β =
      lowerSemicontinuousEnvelope (fun x : ℝ ↦ (g x : EReal)) := by
  let hconv :=
    convexOn_effectiveDomain_of_strictlyConvex g α β hαβ hdom hstrict
  have hopen : IsOpen (effectiveDomain g) := by
    -- The interval-domain description makes openness immediate.
    rw [hdom, erealOpenInterval]
    exact continuous_coe_real_ereal.isOpen_preimage _ isOpen_Ioo
  have hcont :=
    continuousOn_toReal_of_open_interval_domain g α β hdom hconv
  have hboundary :
      boundaryLiminfExtensionEReal g = oneSidedLimitExtensionEReal g α β :=
    boundaryLiminfExtensionEReal_eq_oneSidedLimitExtensionEReal g α β hαβ hdom
  have hconv_epi : Convex ℝ (epigraph (fun x : ℝ ↦ (g x : EReal))) :=
    convex_epigraph_coe_of_convexOn_effectiveDomain g hconv
  -- First identify the explicit formula with the Chapter 9 boundary extension, then drop the
  -- convex-envelope wrapper using Corollary 9.10.
  calc
    oneSidedLimitExtensionEReal g α β = boundaryLiminfExtensionEReal g := hboundary.symm
    _ = lowerSemicontinuousConvexEnvelope (fun x : ℝ ↦ (g x : EReal)) :=
      boundaryLiminfExtensionEReal_eq_lowerSemicontinuousConvexEnvelope g hconv hopen hcont
    _ = lowerSemicontinuousEnvelope (fun x : ℝ ↦ (g x : EReal)) :=
      lowerSemicontinuousConvexEnvelope_eq_lowerSemicontinuousEnvelope_of_convex_epigraph
        (fun x : ℝ ↦ (g x : EReal)) hconv_epi

/-- Helper for Proposition 9.34: convexity on the effective domain forces the effective domain
itself to be convex. -/
private theorem convex_effectiveDomain_of_convexOn_local
    (f : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) :
    Convex ℝ (effectiveDomain f) := by
  -- A convex combination of two finite values stays finite, so the segment remains in the domain.
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  have ha_lt_one : a < 1 := by
    linarith
  have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hb_eq : (1 - a : ℝ) = b := by
    linarith
  have hineq0 := hconv.ineq hx hy ha ha_lt_one
  have hineq1 :
      (f (a • x + (1 - a) • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
    simpa [hsub_cast] using hineq0
  have hineq :
      (f (a • x + b • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
    simpa [hb_eq] using hineq1
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsum :
      (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
        ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (hineq.trans_eq hsum) (EReal.coe_lt_top _)

/-- Helper for Proposition 9.34: the finite real representative of a convex `]-∞,+∞]`-valued
function is convex on its effective domain. -/
private theorem toReal_convexOn_effectiveDomain_local
    (f : ℝ → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) :
    _root_.ConvexOn ℝ (effectiveDomain f) (fun x ↦ (f x : EReal).toReal) := by
  -- Rewrite the stored `EReal` Jensen inequality through `toReal` on finite-domain points.
  rw [convexOn_iff_forall_pos]
  constructor
  · exact convex_effectiveDomain_of_convexOn_local f hconv
  · intro x hx y hy a b ha hb hab
    have ha_lt_one : a < 1 := by
      linarith
    have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hb_eq : (1 - a : ℝ) = b := by
      linarith
    have hineq0 := hconv.ineq hx hy ha ha_lt_one
    have hineq1 :
        (f (a • x + (1 - a) • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
      simpa [hsub_cast] using hineq0
    have hineq :
        (f (a • x + b • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
      simpa [hb_eq] using hineq1
    have hxy : a • x + b • y ∈ effectiveDomain f :=
      (convex_effectiveDomain_of_convexOn_local f hconv) hx hy ha.le hb.le hab
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hxy_bot : (f (a • x + b • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (a • x + b • y) : EReal) from (f _).2)
    have hsum :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
          ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      simp
    have hright_top :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) ≠ ⊤ := by
      rw [hsum]
      exact ne_of_lt (EReal.coe_lt_top _)
    simpa [hsum] using EReal.toReal_le_toReal hineq hxy_bot hright_top

/-- Helper for Proposition 9.34: tracing the one-sided-limit extension along a segment inside the
effective domain yields an ordinary convex real-valued function on `Icc 0 1`. -/
private theorem oneSidedLimitExtension_segmentTrace_convexOn
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)))
    (hconv :
      ConvexOn (oneSidedLimitExtension g α β hαlim hβlim)
        (effectiveDomain (oneSidedLimitExtension g α β hαlim hβlim)))
    {x y : ℝ}
    (hx : x ∈ effectiveDomain (oneSidedLimitExtension g α β hαlim hβlim))
    (hy : y ∈ effectiveDomain (oneSidedLimitExtension g α β hαlim hβlim)) :
    _root_.ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ ↦
        ((oneSidedLimitExtension g α β hαlim hβlim (AffineMap.lineMap x y t)) : EReal).toReal) := by
  let f := oneSidedLimitExtension g α β hαlim hβlim
  have htoRealConvex :
      _root_.ConvexOn ℝ (effectiveDomain f) (fun z ↦ (f z : EReal).toReal) :=
    toReal_convexOn_effectiveDomain_local f hconv
  have hcomp :
      _root_.ConvexOn ℝ ((AffineMap.lineMap x y) ⁻¹' effectiveDomain f)
        (fun t : ℝ ↦ (f (AffineMap.lineMap x y t) : EReal).toReal) :=
    htoRealConvex.comp_affineMap (AffineMap.lineMap x y)
  have hdomain_convex : Convex ℝ (effectiveDomain f) :=
    convex_effectiveDomain_of_convexOn_local f hconv
  refine hcomp.subset ?_ (convex_Icc (0 : ℝ) 1)
  intro t ht
  -- The whole parameter interval maps into the effective domain because that domain is convex.
  show AffineMap.lineMap x y t ∈ effectiveDomain f
  simpa [AffineMap.lineMap_apply_module] using
    hdomain_convex hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-- Helper for Proposition 9.34: equality with the endpoint chord at one interior point forces a
convex real-valued trace on `Icc 0 1` to agree with that chord everywhere. -/
private theorem eq_lineMap_on_Icc_of_convex_eq_at_interior
    {φ : ℝ → ℝ}
    (hφ : _root_.ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (hEq : φ γ = AffineMap.lineMap (φ 0) (φ 1) γ) :
    ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
      φ t = AffineMap.lineMap (φ 0) (φ 1) t := by
  let ℓ : ℝ → ℝ := fun t ↦ AffineMap.lineMap (φ 0) (φ 1) t
  let ψ : ℝ → ℝ := fun t ↦ ℓ t - φ t
  have hline_convex : _root_.ConvexOn ℝ (Set.Icc (0 : ℝ) 1) ℓ := by
    -- The chord itself is affine, hence Jensen's inequality holds with equality.
    rw [convexOn_iff_forall_pos]
    constructor
    · exact convex_Icc (0 : ℝ) 1
    · intro x hx y hy a b ha hb hab
      have hab' : b = 1 - a := by
        linarith
      have hEqLine : ℓ (a * x + b * y) = a * ℓ x + b * ℓ y := by
        simp [ℓ, AffineMap.lineMap_apply_module, hab', sub_eq_add_neg, mul_add, add_mul]
        ring
      simpa [smul_eq_mul] using le_of_eq hEqLine
  have hline_concave : _root_.ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) ℓ := by
    -- The same affine identity also gives the reverse Jensen inequality.
    rw [concaveOn_iff_forall_pos]
    constructor
    · exact convex_Icc (0 : ℝ) 1
    · intro x hx y hy a b ha hb hab
      have hab' : b = 1 - a := by
        linarith
      have hEqLine : ℓ (a * x + b * y) = a * ℓ x + b * ℓ y := by
        simp [ℓ, AffineMap.lineMap_apply_module, hab', sub_eq_add_neg, mul_add, add_mul]
        ring
      simpa [smul_eq_mul] using ge_of_eq hEqLine
  have hdefect : _root_.ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) ψ := by
    -- The chord defect is concave because it is affine minus a convex function.
    exact hline_concave.sub hφ
  have hzero_nonneg :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ ψ t := by
    intro t ht
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      simp
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      simp
    have hle :
        φ ((1 - t) • (0 : ℝ) + t • (1 : ℝ)) ≤
          (1 - t) • φ 0 + t • φ 1 := by
      exact hφ.2 h0 h1 (sub_nonneg.mpr ht.2) ht.1 (by ring)
    -- The convexity bound against the endpoint chord is exactly nonnegativity of the defect.
    simpa [ψ, ℓ, AffineMap.lineMap_apply_module, smul_eq_mul, sub_eq_add_neg] using hle
  have hψ_zero : ψ 0 = 0 := by
    simp [ψ, ℓ]
  have hψ_one : ψ 1 = 0 := by
    simp [ψ, ℓ]
  have hψ_gamma : ψ γ = 0 := by
    -- The assumed interior equality says the defect vanishes at `γ`.
    simp [ψ, ℓ, hEq]
  intro t ht
  by_cases htγ : t ≤ γ
  · have ht_le : ψ t ≤ ψ γ := by
      exact hdefect.left_le_of_le_right'' (y := γ) ht (by simp) htγ hγ.2
        (by simpa [hψ_one, hψ_gamma])
    have ht_nonneg : 0 ≤ ψ t := hzero_nonneg ht
    have ht_zero : ψ t = 0 := by
      linarith [ht_nonneg, ht_le]
    have ht_eq : φ t = ℓ t := by
      linarith [ht_zero]
    simpa [ℓ] using ht_eq
  · have hγt : γ ≤ t := by
      linarith
    have ht_le : ψ t ≤ ψ γ := by
      exact hdefect.right_le_of_le_left'' (y := γ) (by simp) ht hγ.1 hγt
        (by simpa [hψ_zero, hψ_gamma])
    have ht_nonneg : 0 ≤ ψ t := hzero_nonneg ht
    have ht_zero : ψ t = 0 := by
      linarith [ht_nonneg, ht_le]
    have ht_eq : φ t = ℓ t := by
      linarith [ht_zero]
    simpa [ℓ] using ht_eq

/-- Helper for Proposition 9.34: every effective-domain point of the one-sided extension lies in
the closed interval cut out by the boundary parameters. -/
private theorem mem_closedInterval_of_mem_effectiveDomain_extension
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)
    (hαβ : α < β)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)))
    {x : ℝ}
    (hx : x ∈ effectiveDomain (oneSidedLimitExtension g α β hαlim hβlim)) :
    α ≤ (x : EReal) ∧ (x : EReal) ≤ β := by
  constructor
  · by_contra hαx
    have hx_not_mem : x ∉ erealOpenInterval α β := by
      intro hx_mem
      exact hαx hx_mem.1.le
    have hxa : α ≠ (x : EReal) := by
      intro hxa
      exact hαx hxa.le
    have hxb : β ≠ (x : EReal) := by
      intro hxb
      exact hαx (hxb.symm ▸ hαβ.le)
    have htop :
        (oneSidedLimitExtension g α β hαlim hβlim x : EReal) = ⊤ := by
      rw [oneSidedLimitExtension_coe]
      simp [oneSidedLimitExtensionEReal, hx_not_mem, hxa, hxb]
    have hx_top : (oneSidedLimitExtension g α β hαlim hβlim x : EReal) < ⊤ :=
      mem_effectiveDomain_iff.mp hx
    have hx_top' : (⊤ : EReal) < ⊤ := by
      simpa [oneSidedLimitExtension_coe, oneSidedLimitExtensionEReal, hx_not_mem, hxa, hxb] using
        hx_top
    exact lt_irrefl _ hx_top'
  · by_contra hβx
    have hx_not_mem : x ∉ erealOpenInterval α β := by
      intro hx_mem
      exact hβx hx_mem.2.le
    have hxb : β ≠ (x : EReal) := by
      intro hxb
      exact hβx hxb.ge
    have hxa : α ≠ (x : EReal) := by
      intro hxa
      exact hβx (hxa.symm ▸ hαβ.le)
    have htop :
        (oneSidedLimitExtension g α β hαlim hβlim x : EReal) = ⊤ := by
      rw [oneSidedLimitExtension_coe]
      simp [oneSidedLimitExtensionEReal, hx_not_mem, hxa, hxb]
    have hx_top : (oneSidedLimitExtension g α β hαlim hβlim x : EReal) < ⊤ :=
      mem_effectiveDomain_iff.mp hx
    have hx_top' : (⊤ : EReal) < ⊤ := by
      simpa [oneSidedLimitExtension_coe, oneSidedLimitExtensionEReal, hx_not_mem, hxa, hxb] using
        hx_top
    exact lt_irrefl _ hx_top'

/-- Helper for Proposition 9.34: interior points of a segment joining two effective-domain points
of the one-sided extension lie in the original open interval `]\alpha,\beta[`. -/
private theorem lineMap_mem_erealOpenInterval_of_mem_effectiveDomain_extension
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal)
    (hαβ : α < β)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)))
    {x y t : ℝ}
    (hx : x ∈ effectiveDomain (oneSidedLimitExtension g α β hαlim hβlim))
    (hy : y ∈ effectiveDomain (oneSidedLimitExtension g α β hαlim hβlim))
    (hxy : x ≠ y)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    AffineMap.lineMap x y t ∈ erealOpenInterval α β := by
  have hx_closed :=
    mem_closedInterval_of_mem_effectiveDomain_extension g α β hαβ hαlim hβlim hx
  have hy_closed :=
    mem_closedInterval_of_mem_effectiveDomain_extension g α β hαβ hαlim hβlim hy
  rw [mem_erealOpenInterval_iff]
  rcases lt_or_gt_of_ne hxy with hxy_lt | hyx_lt
  · constructor
    · have hleft : x < AffineMap.lineMap x y t :=
        (left_lt_lineMap_iff_pos hxy_lt).2 ht.1
      have hleft' : (x : EReal) < (AffineMap.lineMap x y t : ℝ) := by
        exact_mod_cast hleft
      exact lt_of_le_of_lt hx_closed.1 hleft'
    · have hright : AffineMap.lineMap x y t < y :=
        (lineMap_lt_right_iff_lt_one hxy_lt).2 ht.2
      have hright' : ((AffineMap.lineMap x y t : ℝ) : EReal) < (y : EReal) := by
        exact_mod_cast hright
      exact lt_of_lt_of_le hright' hy_closed.2
  · constructor
    · have hleft : y < AffineMap.lineMap x y t :=
        (right_lt_lineMap_iff_lt (a := x) (b := y) ht.2).2 hyx_lt
      have hleft' : (y : EReal) < (AffineMap.lineMap x y t : ℝ) := by
        exact_mod_cast hleft
      exact lt_of_le_of_lt hy_closed.1 hleft'
    · have hright : AffineMap.lineMap x y t < x :=
        (lineMap_lt_left_iff_lt ht.1).2 hyx_lt
      have hright' : ((AffineMap.lineMap x y t : ℝ) : EReal) < (x : EReal) := by
        exact_mod_cast hright
      exact lt_of_lt_of_le hright' hx_closed.2

-- Proof sketch: assume equality in Jensen's inequality for two distinct points of the effective
-- domain of the extension. Exercise 8.1 upgrades that equality to every point of the segment, and
-- because the open segment lies in `]α,β[`, the extension agrees there with `g`, contradicting the
-- strict convexity of `g`.
/-- Proposition 9.34: the one-sided-limit extension of a proper strictly convex function on
`]\alpha,\beta[` is strictly convex. -/
theorem oneSidedLimitExtension_strictlyConvex
    (g : ℝ → Set.Ioi (⊥ : EReal)) (α β : EReal) (hαβ : α < β)
    (hdom : effectiveDomain g = erealOpenInterval α β)
    (hstrict : StrictlyConvex g)
    (hαlim : ∀ ⦃x : ℝ⦄, α = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Ioi x)))
    (hβlim : ∀ ⦃x : ℝ⦄, β = (x : EReal) →
      ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x))) :
    StrictlyConvex (oneSidedLimitExtension g α β hαlim hβlim) := by
  let f := oneSidedLimitExtension g α β hαlim hβlim
  have hfΓ : f ∈ Γ₀(ℝ) :=
    oneSidedLimitExtension_mem_gammaZero g α β hαβ hdom hstrict hαlim hβlim
  have hconvf : ConvexOn f (effectiveDomain f) := by
    exact (mem_gammaZero_iff.mp hfΓ).2
  intro x hx y hy hxy γ hγ0 hγ1
  have hle :
      (f (γ • x + (1 - γ) • y) : EReal) <
        (γ : EReal) * (f x : EReal) + (1 - γ : EReal) * (f y : EReal) ∨
      (f (γ • x + (1 - γ) • y) : EReal) =
        (γ : EReal) * (f x : EReal) + (1 - γ : EReal) * (f y : EReal) := by
    exact lt_or_eq_of_le (hconvf.ineq hx hy hγ0 hγ1)
  rcases hle with hlt | hEq
  · exact hlt
  · -- Route correction: after the assumed Jensen equality at `γ`, propagate affine equality to the
    -- whole segment trace and contradict strict convexity of `g` at the quarter and three-quarter
    -- points.
    let φ : ℝ → ℝ := fun t ↦ (f (AffineMap.lineMap y x t) : EReal).toReal
    have htrace_convex :
        _root_.ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ :=
      oneSidedLimitExtension_segmentTrace_convexOn g α β hαlim hβlim hconvf hy hx
    have hdomain_convex : Convex ℝ (effectiveDomain f) :=
      convex_effectiveDomain_of_convexOn_local f hconvf
    have hγmem : AffineMap.lineMap y x γ ∈ effectiveDomain f := by
      show AffineMap.lineMap y x γ ∈ effectiveDomain f
      simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
        hdomain_convex hy hx (sub_nonneg.mpr hγ1.le) hγ0.le (by ring)
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hγ_top : (f (AffineMap.lineMap y x γ) : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hγmem)
    have hγ_bot : (f (AffineMap.lineMap y x γ) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (AffineMap.lineMap y x γ) : EReal) from
        (f (AffineMap.lineMap y x γ)).2)
    have hEq_line :
        (f (AffineMap.lineMap y x γ) : EReal) =
          (γ : EReal) * (f x : EReal) + (1 - γ : EReal) * (f y : EReal) := by
      simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using hEq
    have hsub_cast : (((1 - γ : ℝ) : EReal)) = 1 - (γ : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hsum :
        (γ : EReal) * (f x : EReal) + (1 - γ : EReal) * (f y : EReal) =
          (((1 - γ) * (f y : EReal).toReal + γ * (f x : EReal).toReal : ℝ) : EReal) := by
      rw [← hsub_cast]
      rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      simp
      rw [add_comm]
    have hEq_real :
        φ γ = AffineMap.lineMap (φ 0) (φ 1) γ := by
      -- Apply `toReal` to the equality and rewrite the weighted sum as the real endpoint chord.
      have hEq_toReal :
          (f (AffineMap.lineMap y x γ) : EReal).toReal =
            (1 - γ) * (f y : EReal).toReal + γ * (f x : EReal).toReal := by
        simpa using congrArg EReal.toReal (hEq_line.trans hsum)
      simpa [φ, AffineMap.lineMap_apply_module] using hEq_toReal
    have htrace_affine :
        ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 →
          φ t = AffineMap.lineMap (φ 0) (φ 1) t := by
      exact eq_lineMap_on_Icc_of_convex_eq_at_interior htrace_convex ⟨hγ0, hγ1⟩ hEq_real
    let quarter : ℝ := AffineMap.lineMap y x (1 / 4 : ℝ)
    let midpoint : ℝ := AffineMap.lineMap y x (1 / 2 : ℝ)
    let threeQuarter : ℝ := AffineMap.lineMap y x (3 / 4 : ℝ)
    have hquarter_mem :
        quarter ∈ erealOpenInterval α β := by
      exact lineMap_mem_erealOpenInterval_of_mem_effectiveDomain_extension
        g α β hαβ hαlim hβlim hy hx hxy.symm (by norm_num [quarter])
    have hmid_mem :
        midpoint ∈ erealOpenInterval α β := by
      exact lineMap_mem_erealOpenInterval_of_mem_effectiveDomain_extension
        g α β hαβ hαlim hβlim hy hx hxy.symm (by norm_num [midpoint])
    have hthreeQuarter_mem :
        threeQuarter ∈ erealOpenInterval α β := by
      exact lineMap_mem_erealOpenInterval_of_mem_effectiveDomain_extension
        g α β hαβ hαlim hβlim hy hx hxy.symm (by norm_num [threeQuarter])
    have hquarter_dom : quarter ∈ effectiveDomain g := by
      simpa [hdom] using hquarter_mem
    have hthreeQuarter_dom : threeQuarter ∈ effectiveDomain g := by
      simpa [hdom] using hthreeQuarter_mem
    have hmid_dom : midpoint ∈ effectiveDomain g := by
      simpa [hdom] using hmid_mem
    have hquarter_ne_threeQuarter : quarter ≠ threeQuarter := by
      intro hq
      have hxy_eq : x = y := by
        simp [quarter, threeQuarter, AffineMap.lineMap_apply_module] at hq
        linarith
      exact hxy hxy_eq
    have hquarter_eval :
        φ (1 / 4 : ℝ) = (g quarter : EReal).toReal := by
      -- Interior segment points are exactly the region where the extension and `g` coincide.
      have hEqQuarter :
          (f quarter : EReal) = g quarter := by
        simpa [f, quarter] using
          oneSidedLimitExtensionEReal_apply_of_mem_erealOpenInterval g α β hquarter_mem
      simpa [φ, quarter] using congrArg EReal.toReal hEqQuarter
    have hmid_eval :
        φ (1 / 2 : ℝ) = (g midpoint : EReal).toReal := by
      have hEqMid :
          (f midpoint : EReal) = g midpoint := by
        simpa [f, midpoint] using
          oneSidedLimitExtensionEReal_apply_of_mem_erealOpenInterval g α β hmid_mem
      simpa [φ, midpoint] using congrArg EReal.toReal hEqMid
    have hthreeQuarter_eval :
        φ (3 / 4 : ℝ) = (g threeQuarter : EReal).toReal := by
      have hEqThreeQuarter :
          (f threeQuarter : EReal) = g threeQuarter := by
        simpa [f, threeQuarter] using
          oneSidedLimitExtensionEReal_apply_of_mem_erealOpenInterval g α β hthreeQuarter_mem
      simpa [φ, threeQuarter] using congrArg EReal.toReal hEqThreeQuarter
    have hquarter_affine :
        φ (1 / 4 : ℝ) = AffineMap.lineMap (φ 0) (φ 1) (1 / 4 : ℝ) := by
      exact htrace_affine (by norm_num)
    have hmid_affine :
        φ (1 / 2 : ℝ) = AffineMap.lineMap (φ 0) (φ 1) (1 / 2 : ℝ) := by
      exact htrace_affine (by norm_num)
    have hthreeQuarter_affine :
        φ (3 / 4 : ℝ) = AffineMap.lineMap (φ 0) (φ 1) (3 / 4 : ℝ) := by
      exact htrace_affine (by norm_num)
    have hmid_real :
        (g midpoint : EReal).toReal =
          AffineMap.lineMap ((g quarter : EReal).toReal) ((g threeQuarter : EReal).toReal)
            (1 / 2 : ℝ) := by
      -- Once the trace is affine on the whole interval, the midpoint value is the midpoint of the
      -- quarter and three-quarter values.
      calc
        (g midpoint : EReal).toReal = φ (1 / 2 : ℝ) := by
          symm
          exact hmid_eval
        _ = AffineMap.lineMap (φ 0) (φ 1) (1 / 2 : ℝ) := hmid_affine
        _ = AffineMap.lineMap (φ (1 / 4 : ℝ)) (φ (3 / 4 : ℝ)) (1 / 2 : ℝ) := by
          rw [hquarter_affine, hthreeQuarter_affine]
          simp [AffineMap.lineMap_apply_module]
          ring
        _ = AffineMap.lineMap ((g quarter : EReal).toReal) ((g threeQuarter : EReal).toReal)
              (1 / 2 : ℝ) := by
          rw [hquarter_eval, hthreeQuarter_eval]
    have hmid_between :
        (1 / 2 : ℝ) • quarter + (1 - (1 / 2 : ℝ)) • threeQuarter = midpoint := by
      simp [quarter, midpoint, threeQuarter, AffineMap.lineMap_apply_module]
      ring
    have hquarter_top : (g quarter : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hquarter_dom)
    have hquarter_bot : (g quarter : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (g quarter : EReal) from (g quarter).2)
    have hthreeQuarter_top : (g threeQuarter : EReal) ≠ ⊤ :=
      ne_of_lt (mem_effectiveDomain_iff.mp hthreeQuarter_dom)
    have hthreeQuarter_bot : (g threeQuarter : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (g threeQuarter : EReal) from (g threeQuarter).2)
    have hhalf_real : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    have hhalf_cast : (1 - (1 / 2 : ℝ) : EReal) = (1 / 2 : EReal) := by
      simpa using congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hhalf_real
    have hstrict_mid :=
      hstrict.ineq hquarter_dom hthreeQuarter_dom hquarter_ne_threeQuarter
        (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
    rw [hmid_between] at hstrict_mid
    have hsum_mid :
        (1 / 2 : EReal) * (g quarter : EReal) +
          (1 - (1 / 2 : ℝ) : EReal) * (g threeQuarter : EReal) =
            ((AffineMap.lineMap ((g quarter : EReal).toReal) ((g threeQuarter : EReal).toReal)
              (1 / 2 : ℝ) : ℝ) : EReal) := by
      have hsum_mid_cast :
          (1 / 2 : EReal) * (g quarter : EReal) +
            (1 - (1 / 2 : ℝ) : EReal) * (g threeQuarter : EReal) =
              (((1 / 2 : ℝ) * (g quarter : EReal).toReal +
                (1 - (1 / 2 : ℝ)) * (g threeQuarter : EReal).toReal : ℝ) : EReal) := by
        have hquarter_term :
            (1 / 2 : EReal) * (g quarter : EReal) =
              (((1 / 2 : ℝ) * (g quarter : EReal).toReal : ℝ) : EReal) := by
          calc
            (1 / 2 : EReal) * (g quarter : EReal)
                = (1 / 2 : EReal) * (((g quarter : EReal).toReal : ℝ) : EReal) := by
                    rw [EReal.coe_toReal hquarter_top hquarter_bot]
            _ = (((1 / 2 : ℝ) : EReal) * (((g quarter : EReal).toReal : ℝ) : EReal)) := by
                    rfl
            _ = (((1 / 2 : ℝ) * (g quarter : EReal).toReal : ℝ) : EReal) := by
                    rw [← EReal.coe_mul]
        have hthreeQuarter_term :
            (1 / 2 : EReal) * (g threeQuarter : EReal) =
              (((1 / 2 : ℝ) * (g threeQuarter : EReal).toReal : ℝ) : EReal) := by
          calc
            (1 / 2 : EReal) * (g threeQuarter : EReal)
                = (1 / 2 : EReal) * (((g threeQuarter : EReal).toReal : ℝ) : EReal) := by
                    rw [EReal.coe_toReal hthreeQuarter_top hthreeQuarter_bot]
            _ = (((1 / 2 : ℝ) : EReal) *
                  (((g threeQuarter : EReal).toReal : ℝ) : EReal)) := by
                    rfl
            _ = (((1 / 2 : ℝ) * (g threeQuarter : EReal).toReal : ℝ) : EReal) := by
                    rw [← EReal.coe_mul]
        calc
          (1 / 2 : EReal) * (g quarter : EReal) +
              (1 - (1 / 2 : ℝ) : EReal) * (g threeQuarter : EReal)
              = (1 / 2 : EReal) * (g quarter : EReal) +
                  (1 / 2 : EReal) * (g threeQuarter : EReal) := by
                    rw [hhalf_cast]
          _ = (((1 / 2 : ℝ) * (g quarter : EReal).toReal : ℝ) : EReal) +
                (((1 / 2 : ℝ) * (g threeQuarter : EReal).toReal : ℝ) : EReal) := by
                  rw [hquarter_term, hthreeQuarter_term]
          _ = (((1 / 2 : ℝ) * (g quarter : EReal).toReal +
                (1 / 2 : ℝ) * (g threeQuarter : EReal).toReal : ℝ) : EReal) := by
                  rw [← EReal.coe_add]
          _ = (((1 / 2 : ℝ) * (g quarter : EReal).toReal +
                (1 - (1 / 2 : ℝ)) * (g threeQuarter : EReal).toReal : ℝ) : EReal) := by
                  rw [hhalf_real]
      have hsum_mid_real :
          (1 / 2 : ℝ) * (g quarter : EReal).toReal +
            (1 - (1 / 2 : ℝ)) * (g threeQuarter : EReal).toReal =
              AffineMap.lineMap ((g quarter : EReal).toReal) ((g threeQuarter : EReal).toReal)
                (1 / 2 : ℝ) := by
        rw [AffineMap.lineMap_apply_module, hhalf_real]
        simpa [smul_eq_mul]
      rw [hsum_mid_cast, hsum_mid_real]
    have hmid_top : (g midpoint : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hmid_dom)
    have hmid_bot : (g midpoint : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (g midpoint : EReal) from (g midpoint).2)
    have hstrict_mid_real :
        (g midpoint : EReal).toReal <
          AffineMap.lineMap ((g quarter : EReal).toReal) ((g threeQuarter : EReal).toReal)
            (1 / 2 : ℝ) := by
      have hltE :
          (((g midpoint : EReal).toReal : ℝ) : EReal) <
            ((AffineMap.lineMap ((g quarter : EReal).toReal) ((g threeQuarter : EReal).toReal)
              (1 / 2 : ℝ) : ℝ) : EReal) := by
        calc
          (((g midpoint : EReal).toReal : ℝ) : EReal) = (g midpoint : EReal) := by
            exact EReal.coe_toReal hmid_top hmid_bot
          _ < (1 / 2 : EReal) * (g quarter : EReal) +
                (1 - (1 / 2 : ℝ) : EReal) * (g threeQuarter : EReal) := hstrict_mid
          _ = ((AffineMap.lineMap ((g quarter : EReal).toReal) ((g threeQuarter : EReal).toReal)
                (1 / 2 : ℝ) : ℝ) : EReal) := hsum_mid
      exact EReal.coe_lt_coe_iff.mp hltE
    exact (lt_irrefl _ (hstrict_mid_real.trans_eq hmid_real.symm)).elim

end ERealFunction

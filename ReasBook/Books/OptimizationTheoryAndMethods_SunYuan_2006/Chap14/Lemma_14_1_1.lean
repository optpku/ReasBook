/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_2
import Mathlib.Order.Filter.IsBounded
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section

open scoped Topology ClarkeDirectionalDerivative

section ClarkeDirectionalDerivative

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Chapter14 Lemma 14.1.1: in the whole-space specialization, the admissible Clarke
pairs are exactly those with positive time component. -/
lemma wholeSpaceClarkePairDomain_eq_positiveTimes (d : E) :
    clarkeDirectionalDerivWithinDomain Set.univ d = {p : E × ℝ | 0 < p.2} := by
  -- The whole-space constraints remove both endpoint membership conditions.
  ext p
  simp [clarkeDirectionalDerivWithinDomain]

/-- Helper for Chapter14 Lemma 14.1.1: shifting the base point by `t • e` preserves the normalized
whole-space Clarke pair filter. -/
lemma wholeSpaceClarkePair_tendsto_shift (x e : E) :
    Filter.Tendsto
      (fun p : E × ℝ ↦ (p.1 + p.2 • e, p.2))
      (nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2})
      (nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}) := by
  -- The ambient map is continuous at `(x, 0)`, so only positivity of the time coordinate remains.
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (fun p : E × ℝ ↦ (p.1 + p.2 • e, p.2)) ?_ ?_
  · simpa using
      (by
        let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
        let g : E × ℝ → E := fun p ↦ p.1 + p.2 • e
        have hbase : Filter.Tendsto (fun p : E × ℝ ↦ p) l (nhds ((x : E), (0 : ℝ))) :=
          tendsto_nhds_of_tendsto_nhdsWithin Filter.tendsto_id
        have hg : ContinuousAt g ((x : E), (0 : ℝ)) := by
          dsimp [g]
          exact (continuous_fst.add (continuous_snd.smul continuous_const)).continuousAt
        have hfst : Filter.Tendsto g l (nhds (x : E)) := by
          have hfst' : Filter.Tendsto (fun p : E × ℝ ↦ g p) l (nhds (g ((x : E), (0 : ℝ)))) :=
            hg.tendsto.comp hbase
          simpa [g] using hfst'
        have hsnd : Filter.Tendsto (fun p : E × ℝ ↦ p.2) l (nhds (0 : ℝ)) :=
          continuous_snd.continuousAt.tendsto.comp hbase
        simpa [l] using Filter.Tendsto.prodMk_nhds hfst hsnd)
  · filter_upwards [self_mem_nhdsWithin] with p hp
    simpa using hp

/-- Helper for Chapter14 Lemma 14.1.1: rescaling the positive time variable by a positive scalar
preserves the normalized whole-space Clarke pair filter. -/
lemma wholeSpaceClarkePair_tendsto_rescale (x : E) {lam : ℝ} (h_lam : 0 < lam) :
    Filter.Tendsto
      (fun p : E × ℝ ↦ (p.1, lam * p.2))
      (nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2})
      (nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}) := by
  -- The rescaling map is continuous, and positivity is preserved by multiplication with `lam > 0`.
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    (fun p : E × ℝ ↦ (p.1, lam * p.2)) ?_ ?_
  · simpa using
      (by
        let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
        let g : E × ℝ → ℝ := fun p ↦ lam * p.2
        have hbase : Filter.Tendsto (fun p : E × ℝ ↦ p) l (nhds ((x : E), (0 : ℝ))) :=
          tendsto_nhds_of_tendsto_nhdsWithin Filter.tendsto_id
        have hfst : Filter.Tendsto (fun p : E × ℝ ↦ p.1) l (nhds (x : E)) :=
          continuous_fst.continuousAt.tendsto.comp hbase
        have hg : ContinuousAt g ((x : E), (0 : ℝ)) := by
          dsimp [g]
          exact (continuous_const.mul continuous_snd).continuousAt
        have hsnd : Filter.Tendsto g l (nhds (lam * 0)) := by
          have hsnd' : Filter.Tendsto (fun p : E × ℝ ↦ g p) l (nhds (g ((x : E), (0 : ℝ)))) :=
            hg.tendsto.comp hbase
          simpa [g] using hsnd'
        simpa [l] using Filter.Tendsto.prodMk_nhds hfst hsnd)
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact mul_pos h_lam hp

/-- Helper for Chapter14 Lemma 14.1.1: the Clarke quotient in direction `d₁ + d₂` splits into the
shifted `d₁` quotient plus the `d₂` quotient, matching the source decomposition for (14.1.9). -/
lemma clarkeQuotient_add_eq_shifted_sum
    (f : E → ℝ) (d₁ d₂ : E) (p : E × ℝ) (hp : 0 < p.2) :
    (((f (p.1 + p.2 • (d₁ + d₂)) - f p.1) / p.2 : ℝ) : EReal) =
      (((f ((p.1 + p.2 • d₂) + p.2 • d₁) - f (p.1 + p.2 • d₂)) / p.2 : ℝ) : EReal) +
        (((f (p.1 + p.2 • d₂) - f p.1) / p.2 : ℝ) : EReal) := by
  have hp_ne : p.2 ≠ 0 := ne_of_gt hp
  have hdir : p.1 + p.2 • (d₁ + d₂) = (p.1 + p.2 • d₂) + p.2 • d₁ := by
    rw [smul_add, add_assoc, add_comm (p.2 • d₁), ← add_assoc]
  set a : ℝ := f ((p.1 + p.2 • d₂) + p.2 • d₁)
  set b : ℝ := f (p.1 + p.2 • d₂)
  set c : ℝ := f p.1
  -- Rewrite the numerator by adding and subtracting the shifted base value.
  have hsplit :
      (a - c) / p.2 = (a - b) / p.2 + (b - c) / p.2 := by
    -- Route correction: isolate the scalar denominator algebra before reintroducing the quotient.
    field_simp [hp_ne]
    ring
  exact_mod_cast
    (by
      simpa [a, b, c, hdir, smul_add, add_assoc, add_left_comm, add_comm] using hsplit : _)

/-- Helper for Chapter14 Lemma 14.1.1: on the positive-time Clarke-pair filter, the quotient in
direction `lam • d` is the positive scalar `lam` times the quotient with rescaled time
`(y, t) ↦ (y, lam * t)`. This is the source pointwise algebra behind positive homogeneity. -/
lemma clarkeQuotient_smul_eq_const_mul_rescaled
    (f : E → ℝ) (d : E) {lam : ℝ} (h_lam : 0 < lam) (p : E × ℝ) (hp : 0 < p.2) :
    (((f (p.1 + p.2 • (lam • d)) - f p.1) / p.2 : ℝ) : EReal) =
      (((lam : ℝ) : EReal) *
        ((((f (p.1 + (lam * p.2) • d) - f p.1) / (lam * p.2) : ℝ) : EReal))) := by
  have hp_ne : p.2 ≠ 0 := ne_of_gt hp
  have hlam_ne : lam ≠ 0 := ne_of_gt h_lam
  have hlamt_ne : lam * p.2 ≠ 0 := mul_ne_zero hlam_ne hp_ne
  have hsmul : p.2 • (lam • d) = (lam * p.2) • d := by
    simpa [mul_comm] using (smul_smul p.2 lam d)
  have hreal :
      ((f (p.1 + p.2 • (lam • d)) - f p.1) / p.2 : ℝ) =
        lam * (((f (p.1 + (lam * p.2) • d) - f p.1) / (lam * p.2) : ℝ)) := by
    -- The source route factors the positive scalar out before transporting the limsup.
    rw [hsmul]
    field_simp [hp_ne, hlamt_ne]
  exact_mod_cast hreal

/-- Helper for Chapter14 Lemma 14.1.1: a local Lipschitz witness gives one finite upper bound and
one finite lower bound for the normalized whole-space Clarke quotient on the positive-time filter.
This packages the boundedness side conditions that otherwise recur in every `limsup` transport. -/
lemma eventually_bounded_clarkeQuotient_of_locallyLipschitzAt
    (f : E → ℝ) (x d : E) (h_local : LocallyLipschitzAt f x) :
    ∃ K : NNReal,
      let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
      let q : E × ℝ → EReal :=
        fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
      (∀ᶠ p in l, q p ≤ (((K : ℝ) * ‖d‖ : ℝ) : EReal)) ∧
        ∀ᶠ p in l, (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ q p) := by
  rcases locallyLipschitzAt_iff.mp h_local with ⟨ε, hε, K, hK⟩
  refine ⟨K, ?_⟩
  let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
  let q : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
  have habs :
      ∀ᶠ p in l, |(f (p.1 + p.2 • d) - f p.1) / p.2| ≤ (K : ℝ) * ‖d‖ := by
    -- The fixed closed-ball witness supplies the common two-sided real bound for the quotient.
    simpa [l, wholeSpaceClarkePairDomain_eq_positiveTimes] using
      eventuallyAbsClarkeQuotient_le_of_closedBallLipschitz f x d K hε hK
  have hupper :
      ∀ᶠ p in l, q p ≤ (((K : ℝ) * ‖d‖ : ℝ) : EReal) := by
    -- Convert the absolute-value estimate to the eventual upper `EReal` bound.
    filter_upwards [habs] with p hp
    change (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal) ≤
      (((K : ℝ) * ‖d‖ : ℝ) : EReal)
    exact_mod_cast (abs_le.mp hp).2
  have hlower :
      ∀ᶠ p in l, (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ q p) := by
    -- The same estimate also yields the eventual lower `EReal` bound.
    filter_upwards [habs] with p hp
    change (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤
      (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))
    exact_mod_cast (abs_le.mp hp).1
  exact ⟨hupper, hlower⟩

/-- Helper for Chapter14 Lemma 14.1.1: positive rescaling of the time variable preserves the
whole-space Clarke quotient limsup. This is the filter-transport bridge used in the `0 < lam`
branch of positive homogeneity. -/
lemma clarkeQuotient_limsup_rescale_eq
    (f : E → ℝ) (x d : E) (h_local : LocallyLipschitzAt f x) {lam : ℝ} (h_lam : 0 < lam) :
    let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
    let qr : E × ℝ → EReal :=
      fun p ↦ (((f (p.1 + (lam * p.2) • d) - f p.1) / (lam * p.2) : ℝ) : EReal)
    Filter.limsup qr l = fᵒ(x; d) := by
  let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
  let q : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
  let qr : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + (lam * p.2) • d) - f p.1) / (lam * p.2) : ℝ) : EReal)
  let s : E × ℝ → E × ℝ := fun p ↦ (p.1, lam * p.2)
  let rinv : E × ℝ → E × ℝ := fun p ↦ (p.1, (1 / lam) * p.2)
  have hl_ne : l.NeBot := by
    rw [show l =
        nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d) by
          simp [l, wholeSpaceClarkePairDomain_eq_positiveTimes]]
    exact wholeSpaceClarkePairFilter_neBot x d
  letI := hl_ne
  obtain ⟨K, hupper, hlower⟩ :=
    by
      simpa [l, q] using
        eventually_bounded_clarkeQuotient_of_locallyLipschitzAt f x d h_local
  have hs : Filter.Tendsto s l l := by
    -- The source substitution `t ↦ lam * t` keeps us on the same positive-time filter.
    simpa [l, s] using wholeSpaceClarkePair_tendsto_rescale x h_lam
  have hq_bdd : l.IsBoundedUnder (· ≤ ·) q := ⟨(((K : ℝ) * ‖d‖ : ℝ) : EReal), hupper⟩
  have hs_lower :
      ∀ᶠ p in l, (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ q (s p)) := by
    -- Pull the lower finite bound across the rescaling map once for the transport theorem.
    simpa [q, s] using hs.eventually hlower
  have hs_cobdd : (Filter.map s l).IsCoboundedUnder (· ≤ ·) q := by
    have hs_comp : l.IsCoboundedUnder (· ≤ ·) (q ∘ s) :=
      Filter.isCoboundedUnder_le_of_eventually_le l
        (by simpa [Function.comp] using hs_lower)
    simpa [Filter.IsCoboundedUnder, Function.comp, Filter.map_map, s] using hs_comp
  have hle : Filter.limsup qr l ≤ Filter.limsup q l := by
    have hqr_eq : qr = q ∘ s := by
      funext p
      rfl
    have htransport : Filter.limsup (q ∘ s) l ≤ Filter.limsup q l :=
      hs.limsup_comp_le_limsup (β := EReal) (u := q) (hvf := hs_cobdd) (hg := hq_bdd)
    rw [hqr_eq]
    exact htransport
  have hqr_upper :
      ∀ᶠ p in l, qr p ≤ (((K : ℝ) * ‖d‖ : ℝ) : EReal) := by
    -- The same rescaling also transfers the eventual upper finite bound to the rescaled quotient.
    simpa [qr, q, s] using hs.eventually hupper
  have hqr_lower :
      ∀ᶠ p in l, (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ qr p) := by
    -- And it transfers the matching lower finite bound.
    simpa [qr, q, s] using hs.eventually hlower
  have hqr_bdd : l.IsBoundedUnder (· ≤ ·) qr := ⟨(((K : ℝ) * ‖d‖ : ℝ) : EReal), hqr_upper⟩
  have h_inv : 0 < 1 / lam := by positivity
  have hs_inv : Filter.Tendsto rinv l l := by
    -- Reapplying the same positive rescaling with `1 / lam` gives the reverse comparison.
    simpa [l, rinv] using wholeSpaceClarkePair_tendsto_rescale x h_inv
  have hs_inv_lower :
      ∀ᶠ p in l, (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ qr (rinv p)) := by
    simpa [rinv] using hs_inv.eventually hqr_lower
  have hs_inv_cobdd : (Filter.map rinv l).IsCoboundedUnder (· ≤ ·) qr := by
    have hs_inv_comp : l.IsCoboundedUnder (· ≤ ·) (qr ∘ rinv) :=
      Filter.isCoboundedUnder_le_of_eventually_le l
        (by simpa [Function.comp] using hs_inv_lower)
    simpa [Filter.IsCoboundedUnder, Function.comp, Filter.map_map, rinv] using hs_inv_comp
  have hge : Filter.limsup q l ≤ Filter.limsup qr l := by
    have htransport : Filter.limsup (qr ∘ rinv) l ≤ Filter.limsup qr l :=
      hs_inv.limsup_comp_le_limsup (β := EReal) (u := qr)
        (hvf := hs_inv_cobdd) (hg := hqr_bdd)
    have hq_eq : q = qr ∘ rinv := by
      funext p
      dsimp [q, qr, rinv]
      have hlam_ne : lam ≠ 0 := ne_of_gt h_lam
      have hrescale : lam * ((1 / lam) * p.2) = p.2 := by
        field_simp [hlam_ne]
      rw [hrescale]
    rw [← hq_eq] at htransport
    exact htransport
  have hq_limsup : Filter.limsup q l = fᵒ(x; d) := by
    rw [clarkeDirectionalDeriv_eq_limsup]
    simp [l, q, wholeSpaceClarkePairDomain_eq_positiveTimes]
  calc
    Filter.limsup qr l = Filter.limsup q l := le_antisymm hle hge
    _ = fᵒ(x; d) := hq_limsup

/-- Helper for Chapter14 Lemma 14.1.1: the source substitution `y ↦ y + t • e` transports the
whole-space Clarke quotient in direction `d` back into the same positive-time filter, so the
resulting limsup is bounded above by `fᵒ(x; d)`. -/
lemma clarkeQuotient_limsup_shift_le
    (f : E → ℝ) (x d e : E) (h_local : LocallyLipschitzAt f x) :
    let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
    let q : E × ℝ → EReal :=
      fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
    Filter.limsup (fun p ↦ q (p.1 + p.2 • e, p.2)) l ≤ fᵒ(x; d) := by
  let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
  let q : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
  let s : E × ℝ → E × ℝ := fun p ↦ (p.1 + p.2 • e, p.2)
  obtain ⟨K, hupper, hlower⟩ :=
    by
      simpa [l, q] using
        eventually_bounded_clarkeQuotient_of_locallyLipschitzAt f x d h_local
  have hs : Filter.Tendsto s l l := by
    -- The shift map preserves positivity of the time coordinate and tends to the identity base.
    simpa [l, s] using wholeSpaceClarkePair_tendsto_shift x e
  have hq_bdd : l.IsBoundedUnder (· ≤ ·) q := ⟨(((K : ℝ) * ‖d‖ : ℝ) : EReal), hupper⟩
  have hs_cobdd : (Filter.map s l).IsCoboundedUnder (· ≤ ·) q := by
    -- Pull the eventual lower bound back across the shift map once, rather than in every consumer.
    have hshift_lower :
        ∀ᶠ p in l, (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ q (s p)) := by
      simpa [s] using hs.eventually hlower
    have hl_ne : l.NeBot := by
      rw [show l =
          nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d) by
            simp [l, wholeSpaceClarkePairDomain_eq_positiveTimes]]
      exact wholeSpaceClarkePairFilter_neBot x d
    letI := hl_ne
    have hs_comp : l.IsCoboundedUnder (· ≤ ·) (q ∘ s) :=
      Filter.isCoboundedUnder_le_of_eventually_le l
        (by simpa [Function.comp] using hshift_lower)
    simpa [Filter.IsCoboundedUnder, Function.comp, Filter.map_map, s] using hs_comp
  -- Route correction: package the `limsup` transport at the actual Clarke quotient family,
  -- instead of rebuilding boundedness side conditions inside the main theorem.
  have htransport : Filter.limsup (q ∘ s) l ≤ Filter.limsup q l :=
    hs.limsup_comp_le_limsup (β := EReal) (u := q) (hvf := hs_cobdd) (hg := hq_bdd)
  rw [clarkeDirectionalDeriv_eq_limsup]
  change Filter.limsup (q ∘ s) l ≤
    Filter.limsup q (nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d))
  simpa [l, wholeSpaceClarkePairDomain_eq_positiveTimes] using htransport

/-- Helper for Chapter14 Lemma 14.1.1: after the source substitution `u = y - t • d`, the
quotient in direction `-d` becomes the Clarke quotient of `-f` in direction `d` at the shifted
base point. -/
lemma clarkeQuotient_neg_eq_negf_after_shift
    (f : E → ℝ) (d : E) (p : E × ℝ) (_hp : 0 < p.2) :
    (((f (p.1 + p.2 • (-d)) - f p.1) / p.2 : ℝ) : EReal) =
      ((((fun y ↦ -f y) ((p.1 + p.2 • (-d)) + p.2 • d) -
          (fun y ↦ -f y) (p.1 + p.2 • (-d))) / p.2 : ℝ) : EReal) := by
  have hcancel : (p.1 + p.2 • (-d)) + p.2 • d = p.1 := by
    -- The shift by `-d` followed by the shift by `d` returns to the original base point.
    rw [smul_neg, add_assoc, neg_add_cancel, add_zero]
  have hreal :
      (f (p.1 + p.2 • (-d)) - f p.1) / p.2 =
        ((fun y ↦ -f y) ((p.1 + p.2 • (-d)) + p.2 • d) -
          (fun y ↦ -f y) (p.1 + p.2 • (-d))) / p.2 := by
    -- Once the numerator is rewritten, both sides are the same real quotient.
    rw [hcancel]
    ring
  exact_mod_cast hreal

/-
Domain sampling:
* primary domain: nonsmooth analysis via the Clarke generalized directional derivative
* inspected project owners:
  `clarkeDirectionalDeriv`, `LocallyLipschitzAt`, `clarkeDifferential`
* inspected ambient mathlib owners:
  `Filter.limsup`, `LipschitzOnWith`, `UpperSemicontinuousAt`
* core/canonical owner in this chapter: `clarkeDirectionalDeriv f x d` from
  `Definition_14_1_2`
* primitive owner data: a function `f`, a base point `x`, and a direction `d`
* derived API here: whole-space properties of the canonical owner, with no `Set.univ`
  specialization wrappers
-/

/-- Negating the target preserves local Lipschitz continuity at the same point. -/
theorem LocallyLipschitzAt.neg {f : E → ℝ} {x : E}
    (h_local : LocallyLipschitzAt f x) :
    LocallyLipschitzAt (fun y ↦ -f y) x := by
  -- Reuse the same closed-ball witness and negate the Lipschitz map on that ball.
  rcases locallyLipschitzAt_iff.mp h_local with ⟨ε, hε, K, hK⟩
  exact locallyLipschitzAt_of_closedBall ⟨ε, hε, hK.neg⟩

variable (f : E → ℝ) (x : E)

/-- Chapter14 Lemma 14.1.1 (1): if `f` is Lipschitz near `x`, then its Clarke generalized
directional derivative `fᵒ(x; d)` is positively homogeneous in the direction variable. -/
theorem clarkeDirectionalDerivative_posHomogeneous
    (h_lipschitz : LocallyLipschitzAt f x)
    (d : E)
    (lam : ℝ)
    (h_lam : 0 ≤ lam) :
    fᵒ(x; lam • d) = lam * fᵒ(x; d) := by
  by_cases h_zero : lam = 0
  · subst h_zero
    let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
    let q0 : E × ℝ → EReal :=
      fun p ↦ (((f (p.1 + p.2 • ((0 : ℝ) • d)) - f p.1) / p.2 : ℝ) : EReal)
    have hl_ne : l.NeBot := by
      rw [show l =
          nhdsWithin ((x : E), (0 : ℝ))
            (clarkeDirectionalDerivWithinDomain Set.univ ((0 : ℝ) • d)) by
            simp [l, wholeSpaceClarkePairDomain_eq_positiveTimes]]
      exact wholeSpaceClarkePairFilter_neBot x ((0 : ℝ) • d)
    letI := hl_ne
    have hq0 :
        q0 =ᶠ[l] fun _ ↦ (0 : EReal) := by
      -- In the zero-direction branch, every admissible quotient is identically zero.
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hreal :
          ((f (p.1 + p.2 • ((0 : ℝ) • d)) - f p.1) / p.2 : ℝ) = 0 := by
        simp
      change (((f (p.1 + p.2 • ((0 : ℝ) • d)) - f p.1) / p.2 : ℝ) : EReal) = 0
      exact_mod_cast hreal
    have hzero : fᵒ(x; (0 : ℝ) • d) = 0 := by
      have hzero_limsup : Filter.limsup q0 l = 0 := by
        calc
          Filter.limsup q0 l = Filter.limsup (fun _ ↦ (0 : EReal)) l := by
            exact Filter.limsup_congr hq0
          _ = 0 := Filter.limsup_const (f := l) 0
      rw [clarkeDirectionalDeriv_eq_limsup]
      simpa [l, wholeSpaceClarkePairDomain_eq_positiveTimes] using hzero_limsup
    simpa using hzero
  · have h_lam_pos : 0 < lam := lt_of_le_of_ne h_lam (by simpa [eq_comm] using h_zero)
    let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
    let qlam : E × ℝ → EReal :=
      fun p ↦ (((f (p.1 + p.2 • (lam • d)) - f p.1) / p.2 : ℝ) : EReal)
    let qr : E × ℝ → EReal :=
      fun p ↦ (((f (p.1 + (lam * p.2) • d) - f p.1) / (lam * p.2) : ℝ) : EReal)
    have hl_ne : l.NeBot := by
      rw [show l =
          nhdsWithin ((x : E), (0 : ℝ))
            (clarkeDirectionalDerivWithinDomain Set.univ (lam • d)) by
            simp [l, wholeSpaceClarkePairDomain_eq_positiveTimes]]
      exact wholeSpaceClarkePairFilter_neBot x (lam • d)
    letI := hl_ne
    have hqlam :
        qlam =ᶠ[l] fun p ↦ (((lam : ℝ) : EReal) * qr p) := by
      -- Route correction: factor out `lam` pointwise before applying the rescaled-time
      -- limsup bridge.
      filter_upwards [self_mem_nhdsWithin] with p hp
      simpa [qlam, qr] using clarkeQuotient_smul_eq_const_mul_rescaled f d h_lam_pos p hp
    have hqlam_limsup : fᵒ(x; lam • d) = Filter.limsup qlam l := by
      rw [clarkeDirectionalDeriv_eq_limsup]
      simp [l, qlam, wholeSpaceClarkePairDomain_eq_positiveTimes]
    have hqr_limsup : Filter.limsup qr l = fᵒ(x; d) := by
      simpa [l, qr] using
        clarkeQuotient_limsup_rescale_eq (f := f) (x := x) (d := d)
          (h_local := h_lipschitz) h_lam_pos
    calc
      fᵒ(x; lam • d) = Filter.limsup qlam l := hqlam_limsup
      _ = Filter.limsup (fun p ↦ (((lam : ℝ) : EReal) * qr p)) l := by
        exact Filter.limsup_congr hqlam
      _ = (((lam : ℝ) : EReal) * Filter.limsup qr l) := by
        simpa using
          EReal.limsup_const_mul_of_nonneg_of_ne_top (f := l) (u := qr)
            (c := (((lam : ℝ) : EReal))) (by exact_mod_cast h_lam_pos.le) (by simp)
      _ = lam * fᵒ(x; d) := by
        simp [hqr_limsup]

/-- Chapter14 Lemma 14.1.1 (2): if `f` is Lipschitz near `x`, then its Clarke generalized
directional derivative `fᵒ(x; d)` is subadditive in the direction variable. -/
theorem clarkeDirectionalDerivative_subadditive
    (h_lipschitz : LocallyLipschitzAt f x)
    (d₁ d₂ : E) :
    fᵒ(x; d₁ + d₂) ≤ fᵒ(x; d₁) + fᵒ(x; d₂) := by
  let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
  let qsum : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • (d₁ + d₂)) - f p.1) / p.2 : ℝ) : EReal)
  let qshift : E × ℝ → EReal :=
    fun p ↦ (((f ((p.1 + p.2 • d₂) + p.2 • d₁) - f (p.1 + p.2 • d₂)) / p.2 : ℝ) : EReal)
  let q₂ : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d₂) - f p.1) / p.2 : ℝ) : EReal)
  let q₁ : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d₁) - f p.1) / p.2 : ℝ) : EReal)
  let s : E × ℝ → E × ℝ := fun p ↦ (p.1 + p.2 • d₂, p.2)
  have hsum_eq : qsum =ᶠ[l] fun p ↦ qshift p + q₂ p := by
    -- This is exactly the source numerator split from equation (14.1.9).
    filter_upwards [self_mem_nhdsWithin] with p hp
    simpa [qsum, qshift, q₂] using clarkeQuotient_add_eq_shifted_sum f d₁ d₂ p hp
  have hsum_limsup : fᵒ(x; d₁ + d₂) = Filter.limsup qsum l := by
    rw [clarkeDirectionalDeriv_eq_limsup]
    simp [l, qsum, wholeSpaceClarkePairDomain_eq_positiveTimes]
  have hq₂_limsup : fᵒ(x; d₂) = Filter.limsup q₂ l := by
    rw [clarkeDirectionalDeriv_eq_limsup]
    simp [l, q₂, wholeSpaceClarkePairDomain_eq_positiveTimes]
  obtain ⟨K₁, hupper₁, hlower₁⟩ :=
    by
      simpa [l, q₁] using
        eventually_bounded_clarkeQuotient_of_locallyLipschitzAt f x d₁ h_lipschitz
  have hs : Filter.Tendsto s l l := by
    -- The `d₂` shift is the source substitution used in the first quotient term.
    simpa [l, s] using wholeSpaceClarkePair_tendsto_shift x d₂
  have hshift_upper :
      ∀ᶠ p in l, qshift p ≤ (((K₁ : ℝ) * ‖d₁‖ : ℝ) : EReal) := by
    -- Pull back the upper bound for the `d₁` quotient across the shift map.
    simpa [qshift, s, q₁] using hs.eventually hupper₁
  have hshift_lower :
      ∀ᶠ p in l, (((-((K₁ : ℝ) * ‖d₁‖) : ℝ) : EReal) ≤ qshift p) := by
    -- The same pullback also gives the finite lower bound needed for `EReal.limsup_add_le`.
    simpa [qshift, s, q₁] using hs.eventually hlower₁
  have hl_ne : l.NeBot := by
    rw [show l =
        nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d₁) by
          simp [l, wholeSpaceClarkePairDomain_eq_positiveTimes]]
    exact wholeSpaceClarkePairFilter_neBot x d₁
  letI := hl_ne
  have hshift_bdd : l.IsBoundedUnder (· ≤ ·) qshift :=
    ⟨(((K₁ : ℝ) * ‖d₁‖ : ℝ) : EReal), hshift_upper⟩
  have hshift_limsup_ge :
      (((-((K₁ : ℝ) * ‖d₁‖) : ℝ) : EReal) ≤ Filter.limsup qshift l) := by
    refine Filter.le_limsup_of_le (f := l) (u := qshift)
      (a := (((-((K₁ : ℝ) * ‖d₁‖) : ℝ) : EReal))) (hf := hshift_bdd) ?_
    intro b hb
    rcases hl_ne.nonempty_of_mem (Filter.inter_mem hshift_lower hb) with ⟨p, hp⟩
    exact le_trans hp.1 hp.2
  have hshift_ne_bot : Filter.limsup qshift l ≠ ⊥ := by
    exact (lt_of_lt_of_le (EReal.bot_lt_coe (-((K₁ : ℝ) * ‖d₁‖))) hshift_limsup_ge).ne'
  have hshift_ne_top : Filter.limsup qshift l ≠ ⊤ := by
    have hshift_limsup_le :
        Filter.limsup qshift l ≤ (((K₁ : ℝ) * ‖d₁‖ : ℝ) : EReal) :=
      Filter.limsup_le_of_le (f := l) (u := qshift)
        (a := (((K₁ : ℝ) * ‖d₁‖ : ℝ) : EReal)) (h := hshift_upper)
    exact (lt_of_le_of_lt hshift_limsup_le (EReal.coe_lt_top ((K₁ : ℝ) * ‖d₁‖))).ne
  have hshift_le : Filter.limsup qshift l ≤ fᵒ(x; d₁) := by
    -- The shift transport package closes the first term exactly as in the source proof.
    simpa [l, qshift, s, wholeSpaceClarkePairDomain_eq_positiveTimes] using
      clarkeQuotient_limsup_shift_le (f := f) (x := x) (d := d₁) (e := d₂)
        (h_local := h_lipschitz)
  calc
    fᵒ(x; d₁ + d₂) = Filter.limsup qsum l := hsum_limsup
    _ = Filter.limsup (fun p ↦ qshift p + q₂ p) l := by
      exact Filter.limsup_congr hsum_eq
    _ ≤ Filter.limsup qshift l + Filter.limsup q₂ l := by
      exact EReal.limsup_add_le (Or.inl hshift_ne_bot) (Or.inl hshift_ne_top)
    _ ≤ fᵒ(x; d₁) + fᵒ(x; d₂) := by
      simpa [hq₂_limsup] using
        add_le_add hshift_le (le_rfl : Filter.limsup q₂ l ≤ Filter.limsup q₂ l)

/-- Helper for Chapter14 Lemma 14.1.1: on a fixed closed-ball Lipschitz neighborhood, the Clarke
quotient in direction `d'` is bounded by the quotient in direction `d` plus
`K * ‖d' - d‖`. This is the source inequality (14.1.10) before taking upper limits. -/
lemma clarkeQuotient_le_add_norm_sub_of_closedBallLipschitz
    (f : E → ℝ) (x y d d' : E) {t eps : ℝ} (ht : 0 < t) (K : NNReal)
    (hK : LipschitzOnWith K f (Metric.closedBall x eps))
    (_hy : y ∈ Metric.closedBall x eps)
    (hyd : y + t • d ∈ Metric.closedBall x eps)
    (hyd' : y + t • d' ∈ Metric.closedBall x eps) :
    (((f (y + t • d') - f y) / t : ℝ) : EReal) ≤
      (((f (y + t • d) - f y) / t : ℝ) : EReal) + (((K : ℝ) * ‖d' - d‖ : ℝ) : EReal) := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hsub :
      (y + t • d') - (y + t • d) = t • (d' - d) := by
    calc
      (y + t • d') - (y + t • d) = (t • d') - t • d := by
        abel_nf
      _ = t • (d' - d) := by
        rw [smul_sub]
  have hdist :
      dist (y + t • d') (y + t • d) = t * ‖d' - d‖ := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg ht.le]
  have hstep :
      f (y + t • d') ≤ f (y + t • d) + (K : ℝ) * (t * ‖d' - d‖) := by
    -- The fixed closed-ball Lipschitz witness compares the two endpoint evaluations directly.
    simpa [hdist] using hK.le_add_mul hyd' hyd
  have hdiff :
      f (y + t • d') - f y ≤
        (f (y + t • d) - f y) + (K : ℝ) * (t * ‖d' - d‖) := by
    linarith
  have hquot :
      (f (y + t • d') - f y) / t ≤
        (f (y + t • d) - f y) / t + (K : ℝ) * ‖d' - d‖ := by
    -- Divide the source inequality by the common positive time and simplify the scalar factor.
    calc
      (f (y + t • d') - f y) / t ≤
          ((f (y + t • d) - f y) + (K : ℝ) * (t * ‖d' - d‖)) / t := by
        exact div_le_div_of_nonneg_right hdiff ht.le
      _ = (f (y + t • d) - f y) / t + ((K : ℝ) * (t * ‖d' - d‖)) / t := by
        rw [add_div]
      _ = (f (y + t • d) - f y) / t + (K : ℝ) * ‖d' - d‖ := by
        congr 1
        field_simp [ht_ne]
  exact_mod_cast hquot

/-- Chapter14 Lemma 14.1.1 (3): if `f` is `K`-Lipschitz on some closed ball centered at `x`, then
the absolute value of the finite real-valued Clarke directional derivative is bounded by
`K * ‖d‖`. -/
theorem clarkeDirectionalDerivative_abs_le
    (d : E)
    (K : NNReal)
    (h_lipschitz : ∃ ε : ℝ, 0 < ε ∧ LipschitzOnWith K f (Metric.closedBall x ε)) :
    abs (clarkeDirectionalDerivReal f x d) ≤ (K : ℝ) * ‖d‖ := by
  -- Turn the concrete closed-ball witness into the project-local local Lipschitz owner.
  have h_local : LocallyLipschitzAt f x :=
    locallyLipschitzAt_of_closedBall h_lipschitz
  obtain ⟨h_lower, h_upper⟩ :=
    clarkeDirectionalDeriv_bounds_of_closedBallLipschitz f x d K h_lipschitz
  obtain ⟨h_ne_top, h_ne_bot⟩ :=
    clarkeDirectionalDeriv_ne_top_ne_bot_of_locallyLipschitzAt f x d h_local
  have hcoe :
      ((clarkeDirectionalDerivReal f x d : ℝ) : EReal) = fᵒ(x; d) :=
    coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local
  have h_lower_real : -((K : ℝ) * ‖d‖) ≤ clarkeDirectionalDerivReal f x d := by
    -- Transport the lower bound through the real-to-`EReal` order embedding.
    have hlower' : (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤
        ((clarkeDirectionalDerivReal f x d : ℝ) : EReal)) := by
      simpa [hcoe] using h_lower
    exact_mod_cast hlower'
  have h_upper_real : clarkeDirectionalDerivReal f x d ≤ (K : ℝ) * ‖d‖ := by
    -- Transport the upper bound through the same bridge.
    have hupper' : (((clarkeDirectionalDerivReal f x d : ℝ) : EReal) ≤
        (((K : ℝ) * ‖d‖ : ℝ) : EReal)) := by
      simpa [hcoe] using h_upper
    exact_mod_cast hupper'
  exact abs_le.mpr ⟨h_lower_real, h_upper_real⟩

/-- Chapter14 Lemma 14.1.1 (4): if `f` is Lipschitz near `x`, then the map sending `d` to the
finite real-valued Clarke directional derivative is Lipschitz. -/
theorem clarkeDirectionalDerivative_lipschitz
    (h_lipschitz : LocallyLipschitzAt f x) :
    ∃ K : NNReal, LipschitzWith K (fun d ↦ clarkeDirectionalDerivReal f x d) := by
  rcases locallyLipschitzAt_iff.mp h_lipschitz with ⟨ε, hε, K, hK⟩
  refine ⟨K, LipschitzWith.of_le_add_mul K ?_⟩
  intro d₁ d₂
  have hsubadd :
      fᵒ(x; d₁) ≤ fᵒ(x; d₂) + fᵒ(x; d₁ - d₂) := by
    -- This is the source inequality (14.1.11), obtained from subadditivity with
    -- `d₁ = d₂ + (d₁ - d₂)`.
    have h :=
      clarkeDirectionalDerivative_subadditive (f := f) (x := x) h_lipschitz d₂ (d₁ - d₂)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hsubadd_real :
      clarkeDirectionalDerivReal f x d₁ ≤
        clarkeDirectionalDerivReal f x d₂ + clarkeDirectionalDerivReal f x (d₁ - d₂) := by
    -- Transport the finite `EReal` inequality back to the textbook real-valued derivative.
    have hsubaddE :
        (((clarkeDirectionalDerivReal f x d₁ : ℝ) : EReal) ≤
          ((clarkeDirectionalDerivReal f x d₂ : ℝ) : EReal) +
            ((clarkeDirectionalDerivReal f x (d₁ - d₂) : ℝ) : EReal)) := by
      simpa
        [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d₁ h_lipschitz,
          coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d₂ h_lipschitz,
          coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x (d₁ - d₂) h_lipschitz]
        using hsubadd
    exact_mod_cast hsubaddE
  have habs :
      abs (clarkeDirectionalDerivReal f x (d₁ - d₂)) ≤ (K : ℝ) * ‖d₁ - d₂‖ :=
    clarkeDirectionalDerivative_abs_le (f := f) (x := x) (d := d₁ - d₂) K ⟨ε, hε, hK⟩
  have hdiff :
      clarkeDirectionalDerivReal f x (d₁ - d₂) ≤ (K : ℝ) * ‖d₁ - d₂‖ := (abs_le.mp habs).2
  calc
    clarkeDirectionalDerivReal f x d₁ ≤
        clarkeDirectionalDerivReal f x d₂ + clarkeDirectionalDerivReal f x (d₁ - d₂) :=
      hsubadd_real
    _ ≤ clarkeDirectionalDerivReal f x d₂ + (K : ℝ) * ‖d₁ - d₂‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hdiff (clarkeDirectionalDerivReal f x d₂)
    _ = clarkeDirectionalDerivReal f x d₂ + (K : ℝ) * dist d₁ d₂ := by
      simp [dist_eq_norm]

/-- Helper for Chapter14 Lemma 14.1.1: a strict upper bound on `fᵒ(x; d)` yields one closed-ball
radius around `((x : E), 0)` on which every positive-time quotient in direction `d` stays below
the same cutoff. This packages the fixed-direction `limsup` bound into a witness-friendly metric
statement. -/
lemma clarkeQuotient_eventually_le_of_lt_bound
    (f : E → ℝ) (x d : E) {b : EReal}
    (hb : fᵒ(x; d) < b) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {p : E × ℝ},
      p ∈ Metric.closedBall ((x : E), (0 : ℝ)) ρ →
      0 < p.2 →
      (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal) ≤ b := by
  let a : E × ℝ := ((x : E), (0 : ℝ))
  let s : Set (E × ℝ) := {p : E × ℝ | 0 < p.2}
  let l : Filter (E × ℝ) := nhdsWithin a s
  let q : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
  have hlim : Filter.limsup q l < b := by
    -- Rewrite the Clarke derivative as the limsup of the whole-space quotient family.
    rw [clarkeDirectionalDeriv_eq_limsup] at hb
    simpa [a, l, q, s, wholeSpaceClarkePairDomain_eq_positiveTimes] using hb
  have hlt : ∀ᶠ p in l, q p < b :=
    Filter.eventually_lt_of_limsup_lt hlim
  have himpl : ∀ᶠ p in 𝓝 a, p ∈ s → q p ≤ b := by
    -- Unpack the within-filter event into an ordinary neighborhood where positivity implies
    -- the quotient bound.
    have hlt' : {p : E × ℝ | q p < b} ∈ l := hlt
    have hlt'' : {p : E × ℝ | q p < b} ∈ nhds a ⊓ Filter.principal s := by
      simpa [l, nhdsWithin] using hlt'
    rw [Filter.mem_inf_iff] at hlt''
    rcases hlt'' with ⟨t₁, ht₁, t₂, ht₂, hEq⟩
    have hs_subset : s ⊆ t₂ := by
      simpa [Filter.mem_principal] using ht₂
    refine Filter.mem_of_superset ht₁ ?_
    intro p hp₁ hp_pos
    have hp_mem : p ∈ t₁ ∩ t₂ := ⟨hp₁, hs_subset hp_pos⟩
    have hq_lt : q p < b := by
      have : p ∈ ({p : E × ℝ | q p < b} : Set (E × ℝ)) := by
        rwa [hEq]
      exact this
    exact le_of_lt hq_lt
  rcases Metric.eventually_nhds_iff.mp himpl with ⟨ε, hε, hε_prop⟩
  refine ⟨ε / 2, by linarith, ?_⟩
  intro p hp ht
  have hpdist : dist p a < ε := by
    have hp_le : dist p a ≤ ε / 2 := by
      simpa [Metric.mem_closedBall] using hp
    linarith
  exact hε_prop hpdist ht

/-- Helper for Chapter14 Lemma 14.1.1: one small product closed ball around `(x, d)` forces any
positive-time Clarke witness based at a nearby `(x', 0)` to keep its base point and both
directional endpoints inside the same closed ball around `x`. This is the geometric packaging
needed before applying the fixed local Lipschitz witness. -/
lemma clarkeWitness_points_mem_closedBall_of_nearby_pair
    (x d : E) {eps : ℝ} (hε : 0 < eps) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ {x' d' : E} {p : E × ℝ},
      (x', d') ∈ Metric.closedBall (x, d) ρ →
      p ∈ Metric.closedBall ((x' : E), (0 : ℝ)) ρ →
      0 < p.2 →
      p.1 ∈ Metric.closedBall x eps ∧
        p.1 + p.2 • d ∈ Metric.closedBall x eps ∧
        p.1 + p.2 • d' ∈ Metric.closedBall x eps := by
  let ρ : ℝ := min 1 (eps / (‖d‖ + 3))
  have hρ_pos : 0 < ρ := by
    -- Shrink by both the unit radius and the source geometric denominator.
    have hden : 0 < ‖d‖ + 3 := by positivity
    have hdiv : 0 < eps / (‖d‖ + 3) := by positivity
    exact lt_min (by norm_num) hdiv
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ_pos
  have hρ_le_one : ρ ≤ 1 := min_le_left _ _
  have hρ_le_div : ρ ≤ eps / (‖d‖ + 3) := min_le_right _ _
  have hρ_mul : ρ * (‖d‖ + 3) ≤ eps := by
    -- Record the common scalar bound that closes all three distance estimates.
    have hden : 0 < ‖d‖ + 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hρ_le_div hden.le
    simpa [div_eq_mul_inv, hden.ne'] using hmul
  refine ⟨ρ, hρ_pos, ?_⟩
  intro x' d' p hx'd' hp ht
  have hx_pair : dist x' x ≤ ρ ∧ dist d' d ≤ ρ := by
    simpa [Metric.mem_closedBall, Prod.dist_eq, max_le_iff] using hx'd'
  have hp_pair : dist p.1 x' ≤ ρ ∧ dist p.2 0 ≤ ρ := by
    simpa [Metric.mem_closedBall, Prod.dist_eq, max_le_iff] using hp
  have hxx : dist x' x ≤ ρ := hx_pair.1
  have hdd : dist d' d ≤ ρ := hx_pair.2
  have hpx : dist p.1 x' ≤ ρ := hp_pair.1
  have hpt_abs : |p.2| ≤ ρ := by
    simpa [Real.dist_eq, abs_sub_comm] using hp_pair.2
  have hpt_le : p.2 ≤ ρ := (abs_le.mp hpt_abs).2
  have hd'_norm : ‖d'‖ ≤ ‖d‖ + 1 := by
    -- Nearby directions have uniformly bounded norm once `ρ ≤ 1`.
    calc
      ‖d'‖ = ‖(d' - d) + d‖ := by simp
      _ ≤ ‖d' - d‖ + ‖d‖ := norm_add_le _ _
      _ = dist d' d + ‖d‖ := by rw [dist_eq_norm]
      _ ≤ ρ + ‖d‖ := by linarith
      _ ≤ ‖d‖ + 1 := by linarith
  have hp1_dist : dist p.1 x ≤ 2 * ρ := by
    -- First control the witness base point itself.
    calc
      dist p.1 x ≤ dist p.1 x' + dist x' x := dist_triangle _ _ _
      _ ≤ ρ + ρ := add_le_add hpx hxx
      _ = 2 * ρ := by ring
  have hp1_mem : p.1 ∈ Metric.closedBall x eps := by
    have htwo : 2 * ρ ≤ eps := by
      calc
        2 * ρ ≤ (‖d‖ + 3) * ρ := by
          have hsmall : 2 ≤ ‖d‖ + 3 := by linarith [norm_nonneg d]
          simpa [mul_comm] using mul_le_mul_of_nonneg_right hsmall hρ_nonneg
        _ = ρ * (‖d‖ + 3) := by ring
        _ ≤ eps := hρ_mul
    simpa [Metric.mem_closedBall] using le_trans hp1_dist htwo
  have hmove_d : dist (p.1 + p.2 • d) p.1 = p.2 * ‖d‖ := by
    -- Moving from `p.1` to the fixed-direction endpoint has exactly the expected size.
    calc
      dist (p.1 + p.2 • d) p.1 = ‖(p.1 + p.2 • d) - p.1‖ := by rw [dist_eq_norm]
      _ = ‖p.2 • d‖ := by simp
      _ = p.2 * ‖d‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have hpd_mem : p.1 + p.2 • d ∈ Metric.closedBall x eps := by
    have hmul_d : p.2 * ‖d‖ ≤ ρ * ‖d‖ :=
      mul_le_mul_of_nonneg_right hpt_le (norm_nonneg d)
    have hsum_d :
        dist (p.1 + p.2 • d) p.1 + dist p.1 x ≤ dist (p.1 + p.2 • d) p.1 + 2 * ρ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hp1_dist (dist (p.1 + p.2 • d) p.1)
    have hdist_d : dist (p.1 + p.2 • d) x ≤ p.2 * ‖d‖ + 2 * ρ := by
      calc
        dist (p.1 + p.2 • d) x ≤ dist (p.1 + p.2 • d) p.1 + dist p.1 x := dist_triangle _ _ _
        _ ≤ dist (p.1 + p.2 • d) p.1 + 2 * ρ := hsum_d
        _ = p.2 * ‖d‖ + 2 * ρ := by rw [hmove_d]
    have hbound_d : p.2 * ‖d‖ + 2 * ρ ≤ eps := by
      calc
        p.2 * ‖d‖ + 2 * ρ ≤ ρ * ‖d‖ + 2 * ρ := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul_d (2 * ρ)
        _ = ρ * (‖d‖ + 2) := by ring
        _ ≤ ρ * (‖d‖ + 3) := by
          have hsmall : ‖d‖ + 2 ≤ ‖d‖ + 3 := by linarith
          exact mul_le_mul_of_nonneg_left hsmall hρ_nonneg
        _ ≤ eps := hρ_mul
    simpa [Metric.mem_closedBall] using le_trans hdist_d hbound_d
  have hmove_d' : dist (p.1 + p.2 • d') p.1 = p.2 * ‖d'‖ := by
    -- The perturbed-direction endpoint has the same scalar displacement formula.
    calc
      dist (p.1 + p.2 • d') p.1 = ‖(p.1 + p.2 • d') - p.1‖ := by rw [dist_eq_norm]
      _ = ‖p.2 • d'‖ := by simp
      _ = p.2 * ‖d'‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have hpd'_mem : p.1 + p.2 • d' ∈ Metric.closedBall x eps := by
    have hmul_d' : p.2 * ‖d'‖ ≤ ρ * (‖d‖ + 1) := by
      calc
        p.2 * ‖d'‖ ≤ p.2 * (‖d‖ + 1) := mul_le_mul_of_nonneg_left hd'_norm ht.le
        _ ≤ ρ * (‖d‖ + 1) := mul_le_mul_of_nonneg_right hpt_le (by positivity)
    have hsum_d' :
        dist (p.1 + p.2 • d') p.1 + dist p.1 x ≤ dist (p.1 + p.2 • d') p.1 + 2 * ρ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hp1_dist (dist (p.1 + p.2 • d') p.1)
    have hdist_d' : dist (p.1 + p.2 • d') x ≤ p.2 * ‖d'‖ + 2 * ρ := by
      calc
        dist (p.1 + p.2 • d') x ≤ dist (p.1 + p.2 • d') p.1 + dist p.1 x := dist_triangle _ _ _
        _ ≤ dist (p.1 + p.2 • d') p.1 + 2 * ρ := hsum_d'
        _ = p.2 * ‖d'‖ + 2 * ρ := by rw [hmove_d']
    have hbound_d' : p.2 * ‖d'‖ + 2 * ρ ≤ eps := by
      calc
        p.2 * ‖d'‖ + 2 * ρ ≤ ρ * (‖d‖ + 1) + 2 * ρ := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul_d' (2 * ρ)
        _ = ρ * (‖d‖ + 3) := by ring
        _ ≤ eps := hρ_mul
    simpa [Metric.mem_closedBall] using le_trans hdist_d' hbound_d'
  exact ⟨hp1_mem, hpd_mem, hpd'_mem⟩

/-- Helper for Chapter14 Lemma 14.1.1: a fixed closed-ball Lipschitz witness around `x` turns any
strict real cutoff for `fᵒ(x; d)` into an eventual strict real cutoff for nearby
`fᵒ(x'; d')`. The proof keeps the source structure: freeze the `d`-quotient below an
intermediate level `c`, then compare nearby quotients on the same positive-time witness. -/
lemma clarkeDirectionalDerivative_eventually_lt_coe_of_closedBallLipschitz
    (f : E → ℝ) (x d : E) {eps b : ℝ} (hε : 0 < eps) (K : NNReal)
    (hK : LipschitzOnWith K f (Metric.closedBall x eps))
    (hb : fᵒ(x; d) < ((b : ℝ) : EReal)) :
    ∀ᶠ p' in 𝓝 (x, d), fᵒ(p'.1; p'.2) < ((b : ℝ) : EReal) := by
  obtain ⟨c, hc_left, hc_right⟩ := EReal.lt_iff_exists_real_btwn.mp hb
  obtain ⟨ρq, hρq, hρq_bound⟩ :=
    clarkeQuotient_eventually_le_of_lt_bound (f := f) (x := x) (d := d) hc_left
  obtain ⟨ρg, hρg, hgeom⟩ :=
    clarkeWitness_points_mem_closedBall_of_nearby_pair (x := x) (d := d) hε
  have hcb : c < b := by
    simpa using hc_right
  let ρe : ℝ := (b - c) / ((K : ℝ) + 1)
  have hρe_pos : 0 < ρe := by
    -- Keep one explicit margin for the perturbation term `K * ‖d' - d‖`.
    dsimp [ρe]
    exact div_pos (sub_pos.mpr hcb) (by positivity)
  let ρ : ℝ := min ρg (min (ρq / 2) ρe)
  have hρ_pos : 0 < ρ := by
    -- The final neighborhood must fit both the geometric ball and the fixed quotient cutoff ball.
    dsimp [ρ]
    exact lt_min hρg (lt_min (by linarith) hρe_pos)
  have hρ_le_g : ρ ≤ ρg := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_half : ρ ≤ ρq / 2 := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_e : ρ ≤ ρe := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hnear :
      ∀ {x' d' : E}, (x', d') ∈ Metric.closedBall (x, d) ρ →
        fᵒ(x'; d') < ((b : ℝ) : EReal) := by
    intro x' d' hx'd'
    have hx_pair : dist x' x ≤ ρ ∧ dist d' d ≤ ρ := by
      simpa [Metric.mem_closedBall, Prod.dist_eq, max_le_iff] using hx'd'
    have herror_real :
        (K : ℝ) * ‖d' - d‖ < b - c := by
      -- Route correction: bound the perturbation term by a fixed radius, rather than searching
      -- for a witness after the limsup step.
      have hρe_eq : ((K : ℝ) + 1) * ρe = b - c := by
        have hden_ne : (K : ℝ) + 1 ≠ 0 := by positivity
        dsimp [ρe]
        field_simp [hden_ne]
      have hρe_lt : (K : ℝ) * ρe < b - c := by
        calc
          (K : ℝ) * ρe < ((K : ℝ) + 1) * ρe := by
            exact mul_lt_mul_of_pos_right (by linarith) hρe_pos
          _ = b - c := hρe_eq
      calc
        (K : ℝ) * ‖d' - d‖ = (K : ℝ) * dist d' d := by rw [dist_eq_norm]
        _ ≤ (K : ℝ) * ρ := mul_le_mul_of_nonneg_left hx_pair.2 K.2
        _ ≤ (K : ℝ) * ρe := mul_le_mul_of_nonneg_left hρ_le_e K.2
        _ < b - c := hρe_lt
    have hbound_lt :
        (((c + (K : ℝ) * ‖d' - d‖ : ℝ)) : EReal) < ((b : ℝ) : EReal) := by
      have hsum_lt : c + (K : ℝ) * ‖d' - d‖ < b := by
        linarith
      exact_mod_cast hsum_lt
    let a : E × ℝ := ((x' : E), (0 : ℝ))
    let l' : Filter (E × ℝ) := nhdsWithin a {p : E × ℝ | 0 < p.2}
    let q' : E × ℝ → EReal :=
      fun p ↦ (((f (p.1 + p.2 • d') - f p.1) / p.2 : ℝ) : EReal)
    have hq'_event :
        ∀ᶠ p in l', q' p ≤ (((c + (K : ℝ) * ‖d' - d‖ : ℝ)) : EReal) := by
      -- On one common small witness ball, compare the nearby `d'`-quotient to the frozen
      -- `d`-quotient on the same positive-time pair.
      filter_upwards
          [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds a hρ_pos), self_mem_nhdsWithin] with
          p hp_ball hp_pos
      have hx'd'_g : (x', d') ∈ Metric.closedBall (x, d) ρg := by
        have hx'd'_dist : dist (x', d') (x, d) ≤ ρ := by
          simpa [Metric.mem_closedBall] using hx'd'
        simpa [Metric.mem_closedBall] using le_trans hx'd'_dist hρ_le_g
      have hp_ball_g : p ∈ Metric.closedBall ((x' : E), (0 : ℝ)) ρg := by
        have hp_ball_dist : dist p ((x' : E), (0 : ℝ)) ≤ ρ := by
          simpa [Metric.mem_closedBall, a] using hp_ball
        simpa [Metric.mem_closedBall] using le_trans hp_ball_dist hρ_le_g
      obtain ⟨hy, hyd, hyd'⟩ := hgeom hx'd'_g hp_ball_g hp_pos
      have hp_pair : dist p.1 x' ≤ ρ ∧ dist p.2 0 ≤ ρ := by
        simpa [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, a] using hp_ball
      have hp_fixed : p ∈ Metric.closedBall ((x : E), (0 : ℝ)) ρq := by
        -- The same witness ball around `(x', 0)` sits inside the frozen quotient ball around
        -- `(x, 0)` once `(x', d')` is close enough to `(x, d)`.
        rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff]
        constructor
        · calc
            dist p.1 x ≤ dist p.1 x' + dist x' x := dist_triangle _ _ _
            _ ≤ ρ + ρ := add_le_add hp_pair.1 hx_pair.1
            _ = 2 * ρ := by ring
            _ ≤ ρq := by linarith
        · calc
            dist p.2 0 ≤ ρ := hp_pair.2
            _ ≤ ρq / 2 := hρ_le_half
            _ ≤ ρq := by linarith
      have hcompare :=
        clarkeQuotient_le_add_norm_sub_of_closedBallLipschitz
          (f := f) (x := x) (y := p.1) (d := d) (d' := d') (t := p.2) (eps := eps)
          hp_pos K hK hy hyd hyd'
      have hqd_le :
          (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal) ≤ (c : EReal) :=
        hρq_bound hp_fixed hp_pos
      calc
        q' p ≤ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal) +
            ((((K : ℝ) * ‖d' - d‖ : ℝ)) : EReal) := by
          simpa [q'] using hcompare
        _ ≤ (c : EReal) + ((((K : ℝ) * ‖d' - d‖ : ℝ)) : EReal) := by
          exact add_le_add hqd_le le_rfl
        _ = (((c + (K : ℝ) * ‖d' - d‖ : ℝ)) : EReal) := by
          simp
    have hq'_limsup : fᵒ(x'; d') = Filter.limsup q' l' := by
      rw [clarkeDirectionalDeriv_eq_limsup]
      simp [a, l', q', wholeSpaceClarkePairDomain_eq_positiveTimes]
    have hl'_ne : l'.NeBot := by
      simpa [a, l', wholeSpaceClarkePairDomain_eq_positiveTimes] using
        wholeSpaceClarkePairFilter_neBot x' d'
    letI := hl'_ne
    have hq'_cobdd : l'.IsCoboundedUnder (· ≤ ·) q' := by
      exact Filter.isCoboundedUnder_le_of_le l' (f := q') (x := (⊥ : EReal)) fun _ ↦ by simp
    calc
      fᵒ(x'; d') = Filter.limsup q' l' := hq'_limsup
      _ ≤ (((c + (K : ℝ) * ‖d' - d‖ : ℝ)) : EReal) := by
        exact Filter.limsup_le_of_le
          (f := l') (u := q') (a := (((c + (K : ℝ) * ‖d' - d‖ : ℝ)) : EReal))
          (hf := hq'_cobdd) hq'_event
      _ < ((b : ℝ) : EReal) := hbound_lt
  filter_upwards [Metric.closedBall_mem_nhds (x, d) hρ_pos] with p' hp'
  exact hnear hp'

/-- Chapter14 Lemma 14.1.1 (5): if `f` is Lipschitz near `x`, then `(y, e) ↦ fᵒ(y; e)` is upper
semicontinuous at `(x, d)` on `E × E`. -/
theorem clarkeDirectionalDerivative_upperSemicontinuousAt
    (h_lipschitz : LocallyLipschitzAt f x)
    (d : E) :
    UpperSemicontinuousAt (fun p : E × E ↦ fᵒ(p.1; p.2)) (x, d) := by
  rcases locallyLipschitzAt_iff.mp h_lipschitz with ⟨eps, hε, K, hK⟩
  rw [upperSemicontinuousAt_iff]
  intro y hy
  by_cases hy_top : y = ⊤
  · let b : ℝ := clarkeDirectionalDerivReal f x d + 1
    have hb : fᵒ(x; d) < ((b : ℝ) : EReal) := by
      -- In the `y = ⊤` branch, any finite real bound above the base Clarke value is enough.
      rw [← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_lipschitz]
      dsimp [b]
      exact_mod_cast (lt_add_of_pos_right (clarkeDirectionalDerivReal f x d) zero_lt_one)
    have h_event :
        ∀ᶠ p' in 𝓝 (x, d), fᵒ(p'.1; p'.2) < ((b : ℝ) : EReal) :=
      clarkeDirectionalDerivative_eventually_lt_coe_of_closedBallLipschitz
        (f := f) (x := x) (d := d) (eps := eps) hε K hK hb
    filter_upwards [h_event] with p' hp'
    simpa [hy_top] using hp'.trans (EReal.coe_lt_top b)
  · have hy_ne_bot : y ≠ ⊥ := by
      intro hy_bot
      simp [hy_bot] at hy
    have hy_coe : (((y.toReal : ℝ)) : EReal) = y :=
      EReal.coe_toReal hy_top hy_ne_bot
    have hb : fᵒ(x; d) < (((y.toReal : ℝ)) : EReal) := by
      simpa [hy_coe] using hy
    -- The finite branch reduces directly to the closed-ball cutoff lemma with `b = y.toReal`.
    simpa [hy_coe] using
      clarkeDirectionalDerivative_eventually_lt_coe_of_closedBallLipschitz
        (f := f) (x := x) (d := d) (eps := eps) hε K hK hb

/-- Chapter14 Lemma 14.1.1 (6): if `f` is Lipschitz near `x`, then the Clarke generalized
directional derivative satisfies the sign-change identity
`fᵒ(x; -d) = (-f)ᵒ(x; d)`. -/
theorem clarkeDirectionalDerivative_neg_direction
    (h_lipschitz : LocallyLipschitzAt f x)
    (d : E) :
    fᵒ(x; -d) = (-f)ᵒ(x; d) := by
  let l : Filter (E × ℝ) := nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2}
  let qneg : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • (-d)) - f p.1) / p.2 : ℝ) : EReal)
  let qminus : E × ℝ → EReal :=
    fun p ↦ ((((fun y ↦ -f y) (p.1 + p.2 • d) - (fun y ↦ -f y) p.1) / p.2 : ℝ) : EReal)
  let sneg : E × ℝ → E × ℝ := fun p ↦ (p.1 + p.2 • (-d), p.2)
  let spos : E × ℝ → E × ℝ := fun p ↦ (p.1 + p.2 • d, p.2)
  have hneg_eq : qneg =ᶠ[l] fun p ↦ qminus (sneg p) := by
    -- The source substitution `u = y - t • d` matches the `-d` quotient with the shifted `-f`
    -- quotient on the common positive-time filter.
    filter_upwards [self_mem_nhdsWithin] with p hp
    simpa [qneg, qminus, sneg] using clarkeQuotient_neg_eq_negf_after_shift f d p hp
  have hminus_eq : qminus =ᶠ[l] fun p ↦ qneg (spos p) := by
    -- Reversing the substitution `y = u + t • d` gives the opposite comparison.
    filter_upwards [self_mem_nhdsWithin] with p hp
    simpa [qneg, qminus, sneg, spos, add_assoc, add_left_comm, add_comm] using
      (clarkeQuotient_neg_eq_negf_after_shift f d (spos p) hp).symm
  have hneg_limsup : fᵒ(x; -d) = Filter.limsup qneg l := by
    rw [clarkeDirectionalDeriv_eq_limsup]
    simp [l, qneg, wholeSpaceClarkePairDomain_eq_positiveTimes]
  have hminus_limsup : (-f)ᵒ(x; d) = Filter.limsup qminus l := by
    rw [clarkeDirectionalDeriv_eq_limsup]
    simp [l, qminus, wholeSpaceClarkePairDomain_eq_positiveTimes]
  have hle : fᵒ(x; -d) ≤ (-f)ᵒ(x; d) := by
    -- Compare the two limsups through the shifted `-f` quotient.
    calc
      fᵒ(x; -d) = Filter.limsup qneg l := hneg_limsup
      _ = Filter.limsup (fun p ↦ qminus (sneg p)) l := by
        exact Filter.limsup_congr hneg_eq
      _ ≤ (-f)ᵒ(x; d) := by
        calc
          Filter.limsup (fun p ↦ qminus (sneg p)) l ≤ (fun y ↦ -f y)ᵒ(x; d) := by
            simpa [l, qminus, sneg, wholeSpaceClarkePairDomain_eq_positiveTimes] using
              clarkeQuotient_limsup_shift_le (f := fun y ↦ -f y) (x := x) (d := d) (e := -d)
                (h_local := h_lipschitz.neg)
          _ = (-f)ᵒ(x; d) := by rfl
  have hge : (-f)ᵒ(x; d) ≤ fᵒ(x; -d) := by
    -- Apply the same shift comparison in the reverse direction.
    calc
      (-f)ᵒ(x; d) = Filter.limsup qminus l := hminus_limsup
      _ = Filter.limsup (fun p ↦ qneg (spos p)) l := by
        exact Filter.limsup_congr hminus_eq
      _ ≤ fᵒ(x; -d) := by
        simpa [l, qneg, spos, wholeSpaceClarkePairDomain_eq_positiveTimes] using
          clarkeQuotient_limsup_shift_le (f := f) (x := x) (d := -d) (e := d)
            (h_local := h_lipschitz)
  exact le_antisymm hle hge

end ClarkeDirectionalDerivative

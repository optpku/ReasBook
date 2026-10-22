/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Topology.Instances.EReal.Lemmas
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

-- Semantic recall note: the source-facing statement is continuity of `f` on `effective_domain f`,
-- and the chapter owner `IsProperExtendedRealFunction` packages the source properness assumptions:
-- global exclusion of `⊥` together with nonempty `effective_domain f`. The finite-valued `toReal`
-- bridge only needs the local no-`⊥` hypothesis on `effective_domain f`.

-- Proof sketch: the convexity hypothesis makes the effective domain an interval in `ℝ`, hence its
-- interior is again an interval where the finite-valued restriction of `f` is a real-valued convex
-- function and therefore continuous. At an endpoint of the effective domain, use the one-sided
-- monotonicity of secant slopes for convex functions to show that the one-sided limit exists, then
-- combine this with lower semicontinuity to identify that limit with the endpoint value.
/-- Helper for Theorem 2.10: a point of a convex subset of `ℝ` that is not interior must be an
order endpoint of that set. -/
private lemma endpointOrder_of_mem_convex_not_mem_interior
    {s : Set ℝ} (hs : Convex ℝ s) {x : ℝ} (_hx : x ∈ s) (hx_int : x ∉ interior s) :
    (∀ y ∈ s, x ≤ y) ∨ (∀ y ∈ s, y ≤ x) := by
  by_contra hendpoint
  have hy_exists : ∃ y ∈ s, y < x := by
    by_contra hy_exists
    apply hendpoint
    left
    intro y hy
    by_contra hxy
    exact hy_exists ⟨y, hy, lt_of_not_ge hxy⟩
  have hz_exists : ∃ z ∈ s, x < z := by
    by_contra hz_exists
    apply hendpoint
    right
    intro z hz
    by_contra hxz
    exact hz_exists ⟨z, hz, lt_of_not_ge hxz⟩
  rcases hy_exists with ⟨y, hy, hyx⟩
  rcases hz_exists with ⟨z, hz, hxz⟩
  have hs_ord : Set.OrdConnected s := hs.ordConnected
  have hIoo_subset : Set.Ioo y z ⊆ s := by
    intro w hw
    exact hs_ord.out hy hz ⟨hw.1.le, hw.2.le⟩
  have hxIoo : x ∈ Set.Ioo y z := ⟨hyx, hxz⟩
  -- A point with domain points strictly on both sides lies in an open interval contained in `s`.
  exact hx_int <| mem_interior_iff_mem_nhds.mpr <|
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxIoo) hIoo_subset

/-- Helper for Theorem 2.10: lower semicontinuity of `f` transfers to lower semicontinuity of the
finite-valued restriction `x ↦ (f x).toReal` on `effective_domain f`. -/
private lemma lowerSemicontinuousWithinAt_toReal_effectiveDomain
    {f : ℝ → EReal} (h_closed : LowerSemicontinuous f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) {a : ℝ}
    (ha : a ∈ effective_domain f) :
    LowerSemicontinuousWithinAt (fun x ↦ (f x).toReal) (effective_domain f) a := by
  intro y hy
  have ha_top : f a ≠ ⊤ := (mem_effective_domain.mp ha).ne
  have hya_ereal : (y : EReal) < f a := by
    -- Rewrite `f a` as the real coercion of its finite value at a domain point.
    simpa [EReal.coe_toReal ha_top (h_ne_bot a ha)] using (EReal.coe_lt_coe_iff.mpr hy)
  have hbase :
      ∀ᶠ x in 𝓝[effective_domain f] a, (y : EReal) < f x :=
    h_closed.lowerSemicontinuousWithinAt (effective_domain f) a y hya_ereal
  filter_upwards [self_mem_nhdsWithin, hbase] with x hx hxE
  have hx_top : f x ≠ ⊤ := (mem_effective_domain.mp hx).ne
  -- On the effective domain, `toReal` sits above the original extended-real value.
  have hy_toReal : (y : EReal) < ((f x).toReal : EReal) :=
    lt_of_lt_of_le hxE (EReal.le_coe_toReal hx_top)
  exact EReal.coe_lt_coe_iff.mp hy_toReal

/-- Helper for Theorem 2.10: at a left endpoint of the effective domain, convexity gives an affine
upper bound that forces right continuity of `x ↦ (f x).toReal`. -/
private lemma continuousWithinAt_toReal_of_leftEndpoint
    {f : ℝ → EReal} (h_closed : LowerSemicontinuous f) (h_convex : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) {a : ℝ} (ha : a ∈ effective_domain f)
    (hleft : ∀ y ∈ effective_domain f, a ≤ y) :
    ContinuousWithinAt (fun x ↦ (f x).toReal) (effective_domain f) a := by
  let s : Set ℝ := effective_domain f
  let g : ℝ → ℝ := fun x ↦ (f x).toReal
  have hg_lsc : LowerSemicontinuousWithinAt g s a :=
    lowerSemicontinuousWithinAt_toReal_effectiveDomain h_closed h_ne_bot ha
  refine (continuousWithinAt_iff_lower_upperSemicontinuousWithinAt).2 ⟨hg_lsc, ?_⟩
  by_cases hsingle : ∀ y ∈ s, y = a
  · have hs_eq : s = ({a} : Set ℝ) := by
      ext y
      constructor
      · intro hy
        exact Set.mem_singleton_iff.mpr (hsingle y hy)
      · intro hy
        simpa [Set.mem_singleton_iff.mp hy] using ha
    -- Route correction: when the effective domain is a singleton, continuity is immediate.
    simpa [s, g, hs_eq] using
      (continuousWithinAt_singleton :
        ContinuousWithinAt g ({a} : Set ℝ) a).upperSemicontinuousWithinAt
  · have hnontrivial : ∃ c ∈ s, c ≠ a := by
      by_contra hnontrivial
      apply hsingle
      intro y hy
      by_contra hya
      exact hnontrivial ⟨y, hy, hya⟩
    rcases hnontrivial with ⟨c, hc, hca⟩
    have hac : a < c := lt_of_le_of_ne (hleft c hc) (Ne.symm hca)
    have hca_pos : 0 < c - a := sub_pos.mpr hac
    have hconv : ConvexOn ℝ s g := convexOn_toReal_of_is_convex_function h_convex h_ne_bot
    let φ : ℝ → ℝ := fun x ↦
      (1 - (x - a) / (c - a)) * g a + ((x - a) / (c - a)) * g c
    have hφ_cont : ContinuousWithinAt φ s a := by
      -- The affine comparison function is continuous everywhere.
      exact (by fun_prop : ContinuousAt φ a).continuousWithinAt
    have hφ_upper : UpperSemicontinuousWithinAt φ s a :=
      hφ_cont.upperSemicontinuousWithinAt
    rw [upperSemicontinuousWithinAt_iff]
    intro y hy
    have hφa : φ a < y := by
      simpa [φ, g, hca_pos.ne'] using hy
    have hφ_event :
        ∀ᶠ x in 𝓝[s] a, φ x < y :=
      (upperSemicontinuousWithinAt_iff.mp hφ_upper) y hφa
    have hltc : ∀ᶠ x in 𝓝[s] a, x ∈ s ∧ x < c := by
      simpa [s] using (inter_mem_nhdsWithin s (Iio_mem_nhds hac))
    filter_upwards [hltc, hφ_event] with x hx hφx
    have hx_left : a ≤ x := hleft x hx.1
    have hxIcc : x ∈ Set.Icc a c := ⟨hx_left, hx.2.le⟩
    let t : ℝ := (x - a) / (c - a)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hx_left) hca_pos.le
      · have hnum_le : x - a ≤ c - a := by linarith
        have ht_le : (x - a) / (c - a) ≤ (c - a) / (c - a) :=
          div_le_div_of_nonneg_right hnum_le hca_pos.le
        simpa [hca_pos.ne'] using ht_le
    have hsum : (1 - t) + t = 1 := by ring
    have hxeq : (1 - t) * a + t * c = x := by
      dsimp [t]
      field_simp [hca_pos.ne']
      ring
    have hconv_bound :
        g x ≤ (1 - t) * g a + t * g c := by
      -- Convexity bounds the function by the chord through `(a, g a)` and `(c, g c)`.
      simpa [g, hxeq, t, smul_eq_mul] using
        hconv.2 ha hc (sub_nonneg.mpr ht.2) ht.1 hsum
    exact lt_of_le_of_lt (by simpa [φ, g, t] using hconv_bound) hφx

/-- Helper for Theorem 2.10: the right-endpoint case is the symmetric affine-chord estimate for
`x ↦ (f x).toReal`. -/
private lemma continuousWithinAt_toReal_of_rightEndpoint
    {f : ℝ → EReal} (h_closed : LowerSemicontinuous f) (h_convex : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) {a : ℝ} (ha : a ∈ effective_domain f)
    (hright : ∀ y ∈ effective_domain f, y ≤ a) :
    ContinuousWithinAt (fun x ↦ (f x).toReal) (effective_domain f) a := by
  let s : Set ℝ := effective_domain f
  let g : ℝ → ℝ := fun x ↦ (f x).toReal
  have hg_lsc : LowerSemicontinuousWithinAt g s a :=
    lowerSemicontinuousWithinAt_toReal_effectiveDomain h_closed h_ne_bot ha
  refine (continuousWithinAt_iff_lower_upperSemicontinuousWithinAt).2 ⟨hg_lsc, ?_⟩
  by_cases hsingle : ∀ y ∈ s, y = a
  · have hs_eq : s = ({a} : Set ℝ) := by
      ext y
      constructor
      · intro hy
        exact Set.mem_singleton_iff.mpr (hsingle y hy)
      · intro hy
        simpa [Set.mem_singleton_iff.mp hy] using ha
    -- Route correction: the singleton-domain case is closed directly here as well.
    simpa [s, g, hs_eq] using
      (continuousWithinAt_singleton :
        ContinuousWithinAt g ({a} : Set ℝ) a).upperSemicontinuousWithinAt
  · have hnontrivial : ∃ c ∈ s, c ≠ a := by
      by_contra hnontrivial
      apply hsingle
      intro y hy
      by_contra hya
      exact hnontrivial ⟨y, hy, hya⟩
    rcases hnontrivial with ⟨c, hc, hca⟩
    have hca : c < a := lt_of_le_of_ne (hright c hc) hca
    have hac_pos : 0 < a - c := sub_pos.mpr hca
    have hconv : ConvexOn ℝ s g := convexOn_toReal_of_is_convex_function h_convex h_ne_bot
    let φ : ℝ → ℝ := fun x ↦
      (1 - (a - x) / (a - c)) * g a + ((a - x) / (a - c)) * g c
    have hφ_cont : ContinuousWithinAt φ s a := by
      -- The affine comparison function is continuous everywhere.
      exact (by fun_prop : ContinuousAt φ a).continuousWithinAt
    have hφ_upper : UpperSemicontinuousWithinAt φ s a :=
      hφ_cont.upperSemicontinuousWithinAt
    rw [upperSemicontinuousWithinAt_iff]
    intro y hy
    have hφa : φ a < y := by
      simpa [φ, g, hac_pos.ne'] using hy
    have hφ_event :
        ∀ᶠ x in 𝓝[s] a, φ x < y :=
      (upperSemicontinuousWithinAt_iff.mp hφ_upper) y hφa
    have hgtc : ∀ᶠ x in 𝓝[s] a, x ∈ s ∧ c < x := by
      simpa [s] using (inter_mem_nhdsWithin s (Ioi_mem_nhds hca))
    filter_upwards [hgtc, hφ_event] with x hx hφx
    have hx_right : x ≤ a := hright x hx.1
    have hxIcc : x ∈ Set.Icc c a := ⟨hx.2.le, hx_right⟩
    let t : ℝ := (a - x) / (a - c)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hx_right) hac_pos.le
      · have hnum_le : a - x ≤ a - c := by linarith
        have ht_le : (a - x) / (a - c) ≤ (a - c) / (a - c) :=
          div_le_div_of_nonneg_right hnum_le hac_pos.le
        simpa [hac_pos.ne'] using ht_le
    have hsum : (1 - t) + t = 1 := by ring
    have hxeq : (1 - t) * a + t * c = x := by
      dsimp [t]
      field_simp [hac_pos.ne']
      ring
    have hconv_bound :
        g x ≤ (1 - t) * g a + t * g c := by
      -- Convexity again bounds the function by the chord
      -- through the endpoint and an interior point.
      simpa [g, hxeq, t, smul_eq_mul] using
        hconv.2 ha hc (sub_nonneg.mpr ht.2) ht.1 hsum
    exact lt_of_le_of_lt (by simpa [φ, g, t] using hconv_bound) hφx

/-- Helper for Theorem 2.10: the finite-valued restriction `x ↦ (f x).toReal` is continuous on
`effective_domain f` once lower semicontinuity handles the lower bound and convexity handles the
endpoint upper bound. -/
private theorem continuousOnToRealEffectiveDomainCore
    {f : ℝ → EReal} (h_closed : LowerSemicontinuous f) (h_convex : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    ContinuousOn (fun x ↦ (f x).toReal) (effective_domain f) := by
  let s : Set ℝ := effective_domain f
  let g : ℝ → ℝ := fun x ↦ (f x).toReal
  have hs_convex : Convex ℝ s := effective_domain_convex_of_is_convex_function h_convex
  have hg_convex : ConvexOn ℝ s g := convexOn_toReal_of_is_convex_function h_convex h_ne_bot
  intro x hx
  by_cases hx_int : x ∈ interior s
  · -- Interior points are handled by mathlib's continuity theorem for real-valued convex functions.
    have hcont_int : ContinuousWithinAt g (interior s) x := hg_convex.continuousOn_interior x hx_int
    have hcont_at : ContinuousAt g x :=
      (continuousWithinAt_iff_continuousAt (isOpen_interior.mem_nhds hx_int)).1 hcont_int
    exact hcont_at.continuousWithinAt
  · -- A non-interior point of a convex subset of `ℝ` is a left or right endpoint.
    rcases endpointOrder_of_mem_convex_not_mem_interior hs_convex hx hx_int with hleft | hright
    · exact continuousWithinAt_toReal_of_leftEndpoint h_closed h_convex h_ne_bot hx hleft
    · exact continuousWithinAt_toReal_of_rightEndpoint h_closed h_convex h_ne_bot hx hright

/-- Theorem 2.10: a proper closed convex extended-real-valued function on `ℝ` is continuous on its
effective domain. Here properness is expressed by `IsProperExtendedRealFunction`, closedness by
`LowerSemicontinuous`, and convexity by the chapter owner predicate `is_convex_function`. -/
theorem continuousOn_effective_domain_of_lowerSemicontinuous_convex_univariate
    {f : ℝ → EReal} (hproper : IsProperExtendedRealFunction f) (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) :
    ContinuousOn f (effective_domain f) := by
  have hcore : ContinuousOn (fun x ↦ (f x).toReal) (effective_domain f) :=
    continuousOnToRealEffectiveDomainCore h_closed h_convex (fun x _ ↦ hproper.ne_bot x)
  intro x hx
  have hcoe :
      ContinuousWithinAt (fun z ↦ (((f z).toReal : ℝ) : EReal)) (effective_domain f) x :=
    continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt (hcore x hx)
  -- On the effective domain, `f` agrees with its finite-valued coercion back to `EReal`.
  refine hcoe.congr ?_ ?_
  · intro z hz
    exact (EReal.coe_toReal (mem_effective_domain.mp hz).ne (hproper.ne_bot z)).symm
  · exact (EReal.coe_toReal (mem_effective_domain.mp hx).ne (hproper.ne_bot x)).symm

/-- Companion bridge: if `f` never takes the value `⊥` on `effective_domain f`, then the
finite-valued restriction `x ↦ (f x).toReal` is continuous on `effective_domain f`. -/
theorem continuousOn_toReal_effective_domain_of_lowerSemicontinuous_convex_univariate
    {f : ℝ → EReal} (h_closed : LowerSemicontinuous f) (h_convex : is_convex_function f)
    (h_ne_bot : ∀ x ∈ effective_domain f, f x ≠ ⊥) :
    ContinuousOn (fun x ↦ (f x).toReal) (effective_domain f) := by
  -- The private core theorem carries the actual continuity proof.
  exact continuousOnToRealEffectiveDomainCore h_closed h_convex h_ne_bot

/-- Proper specialization of the `toReal` bridge in Theorem 2.10: properness supplies the exact
`⊥`-exclusion hypothesis needed for `EReal.toReal`. -/
theorem continuousOn_toReal_effective_domain_of_lowerSemicontinuous_convex_univariate_of_proper
    {f : ℝ → EReal} [IsProperExtendedRealFunction f] (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) :
    ContinuousOn (fun x ↦ (f x).toReal) (effective_domain f) := by
  -- Properness globally rules out `⊥`, so the generic `toReal` bridge applies directly.
  exact continuousOn_toReal_effective_domain_of_lowerSemicontinuous_convex_univariate
    h_closed h_convex (fun x _ ↦ IsProperExtendedRealFunction.ne_bot (f := f) x)

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Remark_3_1_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_8
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.SeparationQuotient.Section

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise PolarSet
open scoped MinkowskiFunctional
open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.18 lies in the chapter's Minkowski-functional / polar-subdifferential domain.

Sampled owner-style declarations:
- `dom`, `IsSubgradientAt`, and `subdifferential` from `Definition_3_1_5`, the chapter owners
  for extended-valued convex analysis;
- `polarSet` and `mem_polarSet_iff` from `Definition_3_18`, the chapter owner for the polar set;
- `pointwiseSupremumOn` from `Theorem_3_1_8` and `activePointwiseSupremumOnIndices` from
  `Lemma_3_1_14`, the chapter owners for active parameter sets of pointwise suprema;
- `minkowskiFunctional` and `minkowskiFunctional_eq_gauge` from `Remark_3_1_2_1`, the chapter
  owner for the source-facing `WithTop ℝ`-valued Minkowski functional and its bridge to mathlib
  `gauge`.

Best owner abstraction:
- source-facing owner reused from the chapter Minkowski/gauge file: `minkowskiFunctional`;
- core/canonical owners: `dom`, `subdifferential`, `polarSet`, `pointwiseSupremumOn`,
  `activePointwiseSupremumOnIndices`, and `gauge`.

Primitive data:
- a set `Q : Set E`;
- for the active-pointwise-supremum owner, a point `x : E`.

Derived API:
- the active polar set
  `activePointwiseSupremumOnIndices Qᵒ (fun x g ↦ ((inner ℝ g x : ℝ) : WithTop ℝ)) x`;
- the three proposition statements on `∂ ψ[Q](x)` and `Qᵒ`.

Source/core/bridge triage:
- source-facing: the Proposition 3.18 statements phrased using the chapter owner
  `minkowskiFunctional`;
- core/canonical: `dom`, `subdifferential`, `polarSet`, `pointwiseSupremumOn`,
  `activePointwiseSupremumOnIndices`, and `gauge`;
- bridge/view: the specialization of `activePointwiseSupremumOnIndices` to the polar-pairing
  slices `fun x g ↦ ((inner ℝ g x : ℝ) : WithTop ℝ)`, together with the upstream bridge
  `minkowskiFunctional_eq_gauge`.

This refinement removes the proposition-local argmax-set wrapper. The file now routes the active
polar-vector statements through the chapter owner `activePointwiseSupremumOnIndices` instead of
keeping a parallel local set definition.
-/

section Subdifferential

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (Q : Set E)

local notation "polarPairingFamily" =>
  (fun y : E ↦ fun g ↦ ((inner ℝ g y : ℝ) : WithTop ℝ))

/-- Helper for Proposition 3.18: if the extended gauge is finite, then the source-facing
Minkowski functional is also finite. -/
-- Proof sketch: unfold the source wrapper to the explicit `if` on the extended gauge and
-- simplify using the hypothesis that the gauge is not `⊤`.
lemma minkowskiFunctional_lt_top_of_egauge_ne_top
    {x : E} (hx : egauge NNReal Q x ≠ ⊤) :
    ψ[Q] x < ⊤ := by
  change
    (if egauge NNReal Q x = ⊤ then ⊤ else (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ)) < ⊤
  simp [hx]

/-- Helper for Proposition 3.18: on finite extended-gauge values, the source-facing Minkowski
wrapper is exactly the coerced real part of the extended gauge. -/
-- Proof sketch: unfold the wrapper and simplify the defining `if` using the non-`⊤` hypothesis.
lemma minkowskiFunctional_eq_coe_toReal_of_egauge_ne_top
    {x : E} (hx : egauge NNReal Q x ≠ ⊤) :
    ψ[Q] x = (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ) := by
  change
    (if egauge NNReal Q x = ⊤ then ⊤ else (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ)) =
      (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ)
  simp [hx]

/-- Helper for Proposition 3.18: every point of `Q` has Minkowski functional at most `1`. -/
-- Proof sketch: membership in `Q` gives an immediate `egauge ≤ 1` witness, hence `ψ[Q] z` is
-- finite and agrees with the real-valued gauge. The standard gauge bound on points of `Q` then
-- gives the stated `WithTop` inequality.
lemma minkowskiFunctional_le_one_of_mem
    {z : E} (hz : z ∈ Q) :
    ψ[Q] z ≤ (1 : WithTop ℝ) := by
  -- First show that `z` is a finite point of the source-facing Minkowski functional.
  have hz_mem_one_smul : z ∈ (1 : NNReal) • Q := by
    simpa using hz
  have hz_dom : z ∈ dom (ψ[Q]) := by
    rw [mem_withTopEffectiveDomain_iff]
    have hEgauge : egauge NNReal Q z ≤ (1 : ENNReal) :=
      egauge_le_of_mem_smul hz_mem_one_smul
    have hNotTop : egauge NNReal Q z ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hEgauge
    exact minkowskiFunctional_lt_top_of_egauge_ne_top Q hNotTop
  -- On finite points the chapter wrapper agrees with the canonical real-valued gauge.
  rw [minkowskiFunctional_eq_gauge hz_dom]
  exact_mod_cast gauge_le_one_of_mem hz

/-- Helper for Proposition 3.18: every polar vector is bounded above by the Minkowski functional
on the effective domain. -/
-- Proof sketch: after rewriting `ψ[Q] y` as the real-valued gauge, choose a nonzero scaling
-- witness `y ∈ c • Q` coming from finiteness of `ψ[Q] y`. The polar inequalities on `Q` then
-- show `⟪g, y⟫ ≤ c` for every admissible scale `c`, so `⟪g, y⟫` is bounded by the infimum that
-- defines the gauge.
lemma polarPairing_le_minkowskiFunctional_of_mem_polarSet
    {g y : E} (hg : g ∈ Qᵒ) (hy : y ∈ dom (ψ[Q])) :
    polarPairingFamily y g ≤ ψ[Q] y := by
  -- Rewrite the source-facing value through the canonical real-valued gauge.
  rw [minkowskiFunctional_eq_gauge hy]
  -- Rewrite the polar condition as the pointwise pairing bound on `Q`.
  rw [mem_polarSet_iff] at hg
  have hreal : inner ℝ g y ≤ gauge Q y := by
    -- Approximate the infimum defining the gauge by an actual scaling witness.
    let e : ENNReal := egauge NNReal Q y
    have he_ne_top : e ≠ ⊤ := by
      intro he_top
      have hpsi_lt_top : ψ[Q] y < ⊤ := by
        simpa [mem_withTopEffectiveDomain_iff] using hy
      have hpsi_top : ψ[Q] y = ⊤ := by
        change
          (if egauge NNReal Q y = ⊤ then ⊤ else (((egauge NNReal Q y).toReal : ℝ) : WithTop ℝ)) =
            ⊤
        simp [e, he_top]
      simp [hpsi_top] at hpsi_lt_top
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    let r : NNReal := ⟨e.toReal + ε, add_nonneg ENNReal.toReal_nonneg hε.le⟩
    have htoReal_lt : e.toReal < (r : ℝ) := by
      change e.toReal < e.toReal + ε
      linarith
    have hr_ne_top : (r : ENNReal) ≠ ⊤ := by
      simp
    have he_lt : e < (r : ENNReal) := by
      exact (ENNReal.toReal_lt_toReal he_ne_top hr_ne_top).1 (by simpa [r] using htoReal_lt)
    rcases (egauge_lt_iff.1 he_lt) with ⟨c, hyc, hc_lt⟩
    rcases hyc with ⟨z, hz, hyz⟩
    have hz_pair : inner ℝ g z ≤ 1 := hg z hz
    have hinner_le_c : inner ℝ g ((c : NNReal) • z) ≤ c := by
      calc
        inner ℝ g ((c : NNReal) • z) = (c : ℝ) * inner ℝ g z := by
          simpa [NNReal.smul_def, mul_comm] using (real_inner_smul_right g z (c : ℝ))
        _ ≤ (c : ℝ) * 1 := by gcongr
        _ = c := by simp
    have he_toReal_eq_gauge : e.toReal = gauge Q y := by
      have hy_eq_toReal :
          ψ[Q] y = ((e.toReal : ℝ) : WithTop ℝ) := by
        simpa [e] using minkowskiFunctional_eq_coe_toReal_of_egauge_ne_top Q he_ne_top
      have hy_eq_gauge :
          ψ[Q] y = ((gauge Q y : ℝ) : WithTop ℝ) := by
        rw [minkowskiFunctional_eq_gauge hy]
      have hcoe : ((e.toReal : ℝ) : WithTop ℝ) = ((gauge Q y : ℝ) : WithTop ℝ) := by
        exact hy_eq_toReal.symm.trans hy_eq_gauge
      exact WithTop.coe_injective hcoe
    have hy_lt : inner ℝ g y < e.toReal + ε := by
      calc
        inner ℝ g y = inner ℝ g ((c : NNReal) • z) := by
          simp [hyz]
        _ < e.toReal + ε := hinner_le_c.trans_lt (by simpa [r] using hc_lt)
    simpa [he_toReal_eq_gauge] using hy_lt
  change (((inner ℝ g y : ℝ) : WithTop ℝ)) ≤ ((gauge Q y : ℝ) : WithTop ℝ)
  exact_mod_cast hreal

/-- Helper for Proposition 3.18: at every finite point, the subdifferential of the Minkowski
functional is the set of polar vectors that touch the function value. -/
-- Proof sketch: for `g ∈ ∂ ψ[Q](x)`, first test the subgradient inequality at `0` to obtain
-- `ψ[Q] x ≤ ⟪g, x⟫`, then test it on points of `Q` to prove `g ∈ Qᵒ`. The reverse direction uses
-- the polar upper bound from `polarPairing_le_minkowskiFunctional_of_mem_polarSet` and rewrites
-- the touching equality into the affine support inequality at `x`.
lemma subdifferential_minkowskiFunctional_eq_polar_touching
    {x : E} (hx : x ∈ dom (ψ[Q])) :
    ∂ ψ[Q](x) = Qᵒ ∩ {g | polarPairingFamily x g = ψ[Q] x} := by
  ext g
  constructor
  · intro hg
    have hsub : IsSubgradientAt (ψ[Q]) x g := mem_subdifferential_iff.mp hg
    -- Extract one scaling witness from finiteness of `ψ[Q] x`; this gives the nonemptiness of `Q`.
    have hx_witness : ∃ c : NNReal, x ∈ c • Q := by
      by_contra hfalse
      have he_top : egauge NNReal Q x = ⊤ := by
        rw [egauge_eq_top]
        intro c
        exact fun hxc ↦ hfalse ⟨c, hxc⟩
      have hpsi_lt_top : ψ[Q] x < ⊤ := by
        simpa [mem_withTopEffectiveDomain_iff] using hx
      have hxtop : ψ[Q] x = ⊤ := by
        change
          (if egauge NNReal Q x = ⊤ then ⊤ else (((egauge NNReal Q x).toReal : ℝ) : WithTop ℝ)) =
            ⊤
        simp [he_top]
      simp [hxtop] at hpsi_lt_top
    have hQ_nonempty : Q.Nonempty := by
      rcases hx_witness with ⟨c, z, hz, _⟩
      exact ⟨z, hz⟩
    -- The origin is finite because a nonempty set always contains `0` in its zero scaling.
    have hzero_dom : (0 : E) ∈ dom (ψ[Q]) := by
      rw [mem_withTopEffectiveDomain_iff]
      rcases hQ_nonempty with ⟨z, hz⟩
      have hzero_mem : (0 : E) ∈ (0 : NNReal) • Q := by
        refine ⟨z, hz, ?_⟩
        simp
      have hEgauge : egauge NNReal Q (0 : E) ≤ (0 : ENNReal) :=
        egauge_le_of_mem_smul hzero_mem
      have hNotTop : egauge NNReal Q (0 : E) ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp) hEgauge
      exact minkowskiFunctional_lt_top_of_egauge_ne_top Q hNotTop
    have hx_scaled_dom : ∀ {t : ℝ}, 0 ≤ t → t • x ∈ dom (ψ[Q]) := by
      intro t ht
      rw [mem_withTopEffectiveDomain_iff]
      rcases hx_witness with ⟨c, z, hz, hxc⟩
      let tc : NNReal := ⟨t, ht⟩ * c
      have hscaled_mem : t • ((c : NNReal) • z) ∈ tc • Q := by
        refine ⟨z, hz, ?_⟩
        change (((tc : NNReal) : ℝ) • z) = t • ((c : NNReal) • z)
        rw [NNReal.smul_def, smul_smul]
        have htc : ((tc : NNReal) : ℝ) = t * (c : ℝ) := by
          rw [show ((tc : NNReal) : ℝ) = ((⟨t, ht⟩ : NNReal) : ℝ) * (c : ℝ) by rfl]
        rw [htc]
      have hEgauge : egauge NNReal Q (t • ((c : NNReal) • z)) ≤ (tc : ENNReal) :=
        egauge_le_of_mem_smul hscaled_mem
      have hx_eq : x = (c : ℝ) • z := by
        simpa [NNReal.smul_def] using hxc.symm
      have hEgauge_tx : egauge NNReal Q (t • x) ≤ (tc : ENNReal) := by
        calc
          egauge NNReal Q (t • x) = egauge NNReal Q (t • ((c : ℝ) • z)) := by rw [hx_eq]
          _ = egauge NNReal Q (t • ((c : NNReal) • z)) := by simp [NNReal.smul_def]
          _ ≤ (tc : ENNReal) := hEgauge
      have hNotTop : egauge NNReal Q (t • x) ≠ ⊤ := by
        exact ne_top_of_le_ne_top (by simp) hEgauge_tx
      exact minkowskiFunctional_lt_top_of_egauge_ne_top Q hNotTop
    have hpsi_zero : ψ[Q] (0 : E) = 0 := by
      rw [minkowskiFunctional_eq_gauge hzero_dom]
      simp [gauge_zero]
    -- Test the subgradient inequality at `0` and at `2x` to pin down the touching equality.
    have hineq_zero := hsub.2 hzero_dom
    have hpair_ge_real : gauge Q x ≤ inner ℝ g x := by
      have hineq_zero' :
          (((0 : ℝ) : WithTop ℝ) ≥ ((gauge Q x + inner ℝ g (-x) : ℝ) : WithTop ℝ)) := by
        simpa [hpsi_zero, minkowskiFunctional_eq_gauge hx] using hineq_zero
      have hineq_zero_real : 0 ≥ gauge Q x + inner ℝ g (-x) := by
        exact_mod_cast hineq_zero'
      have haux : gauge Q x - inner ℝ g x ≤ 0 := by
        simpa using hineq_zero_real
      linarith
    have htwo_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have htwo_dom : (2 : ℝ) • x ∈ dom (ψ[Q]) := hx_scaled_dom htwo_nonneg
    have hineq_two := hsub.2 htwo_dom
    have htwo_sub : (2 : ℝ) • x - x = x := by
      simp [two_smul]
    rw [htwo_sub] at hineq_two
    have hpair_le_real : inner ℝ g x ≤ gauge Q x := by
      have hineq_two' :
          (((2 * gauge Q x : ℝ) : WithTop ℝ) ≥ ((gauge Q x + inner ℝ g x : ℝ) : WithTop ℝ)) := by
        simpa [minkowskiFunctional_eq_gauge hx, minkowskiFunctional_eq_gauge htwo_dom,
          gauge_smul_of_nonneg htwo_nonneg, smul_eq_mul] using hineq_two
      have hineq_two_real : 2 * gauge Q x ≥ gauge Q x + inner ℝ g x := by
        exact_mod_cast hineq_two'
      linarith
    have hpair_eq_real : inner ℝ g x = gauge Q x := by
      linarith
    -- Once the touching value is known, the `y ∈ Q` test yields the polar inequalities.
    have hg_polar : g ∈ Qᵒ := by
      rw [mem_polarSet_iff]
      intro z hz
      have hz_dom : z ∈ dom (ψ[Q]) := by
        rw [mem_withTopEffectiveDomain_iff]
        have hz_lt_top : ψ[Q] z < ⊤ := by
          exact lt_of_le_of_lt (minkowskiFunctional_le_one_of_mem Q hz) (by norm_num)
        exact hz_lt_top
      have hineq_z := hsub.2 hz_dom
      have hineq_z' :
          (((gauge Q z : ℝ) : WithTop ℝ) ≥ ((gauge Q x + inner ℝ g (z - x) : ℝ) : WithTop ℝ)) := by
        simpa [minkowskiFunctional_eq_gauge hz_dom, minkowskiFunctional_eq_gauge hx] using hineq_z
      have hineq_z_real : gauge Q z ≥ gauge Q x + inner ℝ g (z - x) := by
        exact_mod_cast hineq_z'
      have hz_le_one : gauge Q z ≤ 1 := by
        exact gauge_le_one_of_mem hz
      have hz_pair : inner ℝ g z ≤ gauge Q z := by
        calc
          inner ℝ g z = inner ℝ g x + inner ℝ g (z - x) := by
            simp [inner_sub_right]
          _ = gauge Q x + inner ℝ g (z - x) := by
            rw [hpair_eq_real]
          _ ≤ gauge Q z := hineq_z_real
      exact hz_pair.trans hz_le_one
    have hpair_eq : polarPairingFamily x g = ψ[Q] x := by
      rw [minkowskiFunctional_eq_gauge hx]
      change (((inner ℝ g x : ℝ) : WithTop ℝ)) = ((gauge Q x : ℝ) : WithTop ℝ)
      exact_mod_cast hpair_eq_real
    exact ⟨hg_polar, hpair_eq⟩
  · rintro ⟨hg_polar, hpair_eq⟩
    refine mem_subdifferential_iff.mpr ?_
    refine ⟨hx, ?_⟩
    intro y hy
    -- Replace the target affine support inequality by the polar upper bound at `y`.
    have hineq :=
      polarPairing_le_minkowskiFunctional_of_mem_polarSet Q hg_polar hy
    have hsum_real : inner ℝ g x + inner ℝ g (y - x) = inner ℝ g y := by
      simp [inner_sub_right]
    have hsum :
        polarPairingFamily x g + (inner ℝ g (y - x) : WithTop ℝ) = polarPairingFamily y g := by
      change
        (((inner ℝ g x : ℝ) : WithTop ℝ) + ((inner ℝ g (y - x) : ℝ) : WithTop ℝ)) =
          (((inner ℝ g y : ℝ) : WithTop ℝ))
      exact_mod_cast hsum_real
    calc
      ψ[Q] y ≥ polarPairingFamily y g := hineq
      _ = polarPairingFamily x g + (inner ℝ g (y - x) : WithTop ℝ) := by
        rw [hsum.symm]
      _ = ψ[Q] x + (inner ℝ g (y - x) : WithTop ℝ) := by
        rw [hpair_eq]

/-- Helper for Proposition 3.18: every positive level strictly below `gauge Q x` is exceeded by
some polar pairing. -/
-- Proof sketch: separate `x` from the closed convex set `c • Q`, then identify the separating
-- functional with an inner-product vector and normalize it so that its values on `Q` are at most
-- `1`.
lemma exists_polarVector_gt_of_lt_gauge
    [FiniteDimensional ℝ E]
    (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q)
    (h0Q : (0 : E) ∈ Q)
    {x : E} {c : ℝ}
    (hc_pos : 0 < c)
    (hc_lt : c < gauge Q x) :
    ∃ g ∈ Qᵒ, c < inner ℝ g x := by
  -- Route correction: the remaining gap is transport, not a missing dependency.
  -- We separate `x` from `c • Q`, then rewrite the separator through `InnerProductSpace.toDual`.
  let s : Set E := c • Q
  have hs_convex : Convex ℝ s := by
    simpa [s] using hQ_convex.smul c
  have hs_closed : IsClosed s := by
    simpa [s] using hQ_closed.smul_of_ne_zero (c := c) hc_pos.ne'
  have hzero_mem : (0 : E) ∈ s := by
    change (0 : E) ∈ c • Q
    refine ⟨0, h0Q, ?_⟩
    simp
  have hx_not_mem : x ∉ s := by
    intro hx_mem
    have hx_le : gauge Q x ≤ c := by
      simpa [s] using gauge_le_of_mem hc_pos.le hx_mem
    linarith
  -- Strictly separate the point from the closed convex scaled set.
  obtain ⟨f, u, hsep, hfx⟩ :=
    geometric_hahn_banach_closed_point hs_convex hs_closed hx_not_mem
  let fbar : StrongDual ℝ (SeparationQuotient E) :=
    SeparationQuotient.liftCLM f fun x y hxy ↦ (hxy.map f.continuous).eq
  let vbar : SeparationQuotient E := (InnerProductSpace.toDual ℝ (SeparationQuotient E)).symm fbar
  let v : E := SeparationQuotient.outCLM ℝ E vbar
  have hmk_v : SeparationQuotient.mk v = vbar := by
    simp [v]
  have happly : ∀ z : E, f z = inner ℝ v z := by
    intro z
    have hrepr :
        fbar (SeparationQuotient.mk z) =
          inner ℝ vbar (SeparationQuotient.mk z) := by
      simp [vbar]
    have hleft : fbar (SeparationQuotient.mk z) = f z := by
      simp [fbar]
    have hright : inner ℝ vbar (SeparationQuotient.mk z) = inner ℝ v z := by
      rw [← hmk_v]
      simp
    exact hleft.symm.trans (hrepr.trans hright)
  have hu_pos : 0 < u := by
    have hzero_lt : f 0 < u := hsep 0 hzero_mem
    simpa using hzero_lt
  let g : E := (c / u) • v
  have hg_polar : g ∈ Qᵒ := by
    rw [mem_polarSet_iff]
    intro y hy
    have hcy_mem : c • y ∈ s := by
      change c • y ∈ c • Q
      exact Set.smul_mem_smul_set hy
    have hcy_lt : f (c • y) < u := hsep (c • y) hcy_mem
    have hvy_lt_u : c * inner ℝ v y < u := by
      simpa [happly (c • y), real_inner_smul_right, mul_comm] using hcy_lt
    have hratio_lt : (c / u) * inner ℝ v y < 1 := by
      have hratio_lt' : (c * inner ℝ v y) / u < 1 := by
        exact (div_lt_one hu_pos).2 hvy_lt_u
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hratio_lt'
    exact le_of_lt <| by
      simpa [g, real_inner_smul_left] using hratio_lt
  have hvx_gt : u < inner ℝ v x := by
    simpa [happly x] using hfx
  have hcg : c < inner ℝ g x := by
    have hcu_pos : 0 < c / u := div_pos hc_pos hu_pos
    have hmul_lt : (c / u) * u < (c / u) * inner ℝ v x :=
      mul_lt_mul_of_pos_left hvx_gt hcu_pos
    have hc_eq : c = (c / u) * u := by
      field_simp [hu_pos.ne']
    calc
      c = (c / u) * u := hc_eq
      _ < (c / u) * inner ℝ v x := hmul_lt
      _ = inner ℝ g x := by
        simp [g, real_inner_smul_left]
  exact ⟨g, hg_polar, hcg⟩

/-- Helper for Proposition 3.18: if `0 ∈ Q`, then at finite points the supremum of the polar
pairings equals the Minkowski functional. -/
-- Route correction: the earlier easy inequalities and touching characterization are now proved.
-- The remaining gap is the source-faithful support-value identity, which needs the structural
-- lower-bound/separation argument converting the polar support supremum back to `ψ[Q] x`.
lemma minkowskiFunctional_eq_pointwiseSupremumOn_polarSet
    [FiniteDimensional ℝ E]
    (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q)
    (h0Q : (0 : E) ∈ Q)
    {x : E} (hx : x ∈ dom (ψ[Q])) :
    pointwiseSupremumOn Qᵒ polarPairingFamily x = ψ[Q] x := by
  have hzero_polar : (0 : E) ∈ Qᵒ := by
    rw [mem_polarSet_iff]
    intro z hz
    simp
  have hupper :
      pointwiseSupremumOn Qᵒ polarPairingFamily x ≤ ((gauge Q x : ℝ) : WithTop ℝ) := by
    -- Bound each polar slice by the canonical gauge value and take the supremum.
    exact ClosedConvexOn.pointwiseSupremumOn_le_of_forall_le
      (Δ := Qᵒ) (φ := polarPairingFamily) (x := x) (t := gauge Q x)
      ⟨0, hzero_polar⟩ fun g hg ↦ by
        simpa [minkowskiFunctional_eq_gauge hx] using
          polarPairing_le_minkowskiFunctional_of_mem_polarSet (Q := Q) hg hx
  have hsup_dom : x ∈ dom (pointwiseSupremumOn Qᵒ polarPairingFamily) := by
    rw [mem_withTopEffectiveDomain_iff]
    exact lt_of_le_of_lt hupper (by simp)
  have hlower_real : gauge Q x ≤ withTopRealPart (pointwiseSupremumOn Qᵒ polarPairingFamily) x := by
    -- If the supremum were smaller than the gauge, a midpoint level would be exceeded by some
    -- polar slice, contradicting the definition of the supremum.
    by_contra hlt
    have hsup_lt : withTopRealPart (pointwiseSupremumOn Qᵒ polarPairingFamily) x < gauge Q x :=
      lt_of_not_ge hlt
    have hsup_nonneg : 0 ≤ withTopRealPart (pointwiseSupremumOn Qᵒ polarPairingFamily) x := by
      exact (le_withTopRealPart_iff hsup_dom).2 (by simpa using
        (slice_le_pointwiseSupremumOn (Δ := Qᵒ) (φ := polarPairingFamily) (x := x)
          (y := (0 : E)) hzero_polar))
    have hgauge_pos : 0 < gauge Q x := by
      exact lt_of_le_of_lt hsup_nonneg hsup_lt
    let c : ℝ := (withTopRealPart (pointwiseSupremumOn Qᵒ polarPairingFamily) x + gauge Q x) / 2
    have hc_def :
        c = (withTopRealPart (pointwiseSupremumOn Qᵒ polarPairingFamily) x + gauge Q x) / 2 := rfl
    have hc_pos : 0 < c := by
      rw [hc_def]
      linarith
    have hc_lt : c < gauge Q x := by
      rw [hc_def]
      linarith
    have hsup_lt_c : withTopRealPart (pointwiseSupremumOn Qᵒ polarPairingFamily) x < c := by
      rw [hc_def]
      linarith
    obtain ⟨g, hg_polar, hcg⟩ :=
      exists_polarVector_gt_of_lt_gauge (Q := Q) hQ_closed hQ_convex h0Q hc_pos hc_lt
    have hslice_le :
        polarPairingFamily x g ≤ pointwiseSupremumOn Qᵒ polarPairingFamily x :=
      slice_le_pointwiseSupremumOn (Δ := Qᵒ) (φ := polarPairingFamily) (x := x) hg_polar
    have hslice_real_le : inner ℝ g x ≤
        withTopRealPart (pointwiseSupremumOn Qᵒ polarPairingFamily) x := by
      exact (le_withTopRealPart_iff hsup_dom).2 hslice_le
    exact (not_lt_of_ge (le_trans hcg.le hslice_real_le)) hsup_lt_c
  -- Convert the real lower bound back to the source-facing `WithTop` equality.
  apply le_antisymm
  · simpa [minkowskiFunctional_eq_gauge hx] using hupper
  · rw [minkowskiFunctional_eq_gauge hx]
    rw [← coe_withTopRealPart hsup_dom]
    exact_mod_cast hlower_real

/-- Zero-point case of Proposition 3.18: for a closed convex set `Q` containing `0` in a
finite-dimensional real
inner-product space, the subdifferential of the Minkowski functional at `0` is the polar set
`Qᵒ`. -/
-- Proof sketch: use `0 ∈ Q` to show `ψ[Q] 0 < ⊤`, so the base point is admissible for
-- `∂ ψ[Q](0)`. A vector belongs to `∂ ψ[Q](0)` exactly when its pairing with every point of `Q`
-- is bounded by `1`, which is the defining membership condition for `Qᵒ`.
theorem subdifferential_minkowskiFunctional_zero_eq_polarSet
    [FiniteDimensional ℝ E]
    (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q)
    (h0Q : (0 : E) ∈ Q) :
    ∂ ψ[Q](0) = Qᵒ := by
  have _ : IsClosed Q := hQ_closed
  have _ : Convex ℝ Q := hQ_convex
  have hQ_dom_zero : (0 : E) ∈ dom (ψ[Q]) := by
    rw [mem_withTopEffectiveDomain_iff]
    exact lt_of_le_of_lt (minkowskiFunctional_le_one_of_mem Q h0Q) (by norm_num)
  ext g
  constructor
  · intro hg
    have hsub : IsSubgradientAt (ψ[Q]) 0 g := mem_subdifferential_iff.mp hg
    have hpsi_zero : ψ[Q] (0 : E) = 0 := by
      rw [minkowskiFunctional_eq_gauge hQ_dom_zero]
      simp [gauge_zero]
    rw [mem_polarSet_iff]
    intro z hz
    have hz_dom : z ∈ dom (ψ[Q]) := by
      rw [mem_withTopEffectiveDomain_iff]
      exact lt_of_le_of_lt (minkowskiFunctional_le_one_of_mem Q hz) (by norm_num)
    have hineq := hsub.2 hz_dom
    rw [hpsi_zero, zero_add, sub_zero] at hineq
    have hpsi_le : ψ[Q] z ≤ (1 : WithTop ℝ) :=
      minkowskiFunctional_le_one_of_mem Q hz
    exact_mod_cast (hineq.trans hpsi_le)
  · intro hg
    refine mem_subdifferential_iff.mpr ?_
    refine ⟨hQ_dom_zero, ?_⟩
    intro y hy
    have hpsi_zero : ψ[Q] (0 : E) = 0 := by
      rw [minkowskiFunctional_eq_gauge hQ_dom_zero]
      simp [gauge_zero]
    have hineq :=
      polarPairing_le_minkowskiFunctional_of_mem_polarSet Q hg hy
    simpa [hpsi_zero, sub_zero] using hineq

section PolarSupport

variable {x : E}

/-- Proposition 3.18 (2): for a closed convex set `Q` containing `0` in a finite-dimensional real
inner-product space, the subdifferential of the Minkowski functional at a finite point `x` is the
active parameter set for the polar-pairing pointwise supremum over `Qᵒ`. -/
-- Proof sketch: write the gauge as the supremum of the linear functionals `g ↦ ⟪g, x⟫` over
-- `Qᵒ`. On `dom (ψ[Q])`, the general subdifferential rule for such suprema identifies `∂ ψ[Q](x)`
-- with the active maximizers.
theorem subdifferential_minkowskiFunctional_eq_activePolarIndices
    [FiniteDimensional ℝ E]
    (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q)
    (h0Q : (0 : E) ∈ Q)
    (hx : x ∈ dom (ψ[Q])) :
    ∂ ψ[Q](x) =
      activePointwiseSupremumOnIndices Qᵒ polarPairingFamily x := by
  -- Rewrite both sides through the existing touching description and the support-value identity.
  rw [subdifferential_minkowskiFunctional_eq_polar_touching (Q := Q) (x := x) hx]
  ext g
  rw [mem_activePointwiseSupremumOnIndices_iff]
  constructor
  · rintro ⟨hg_polar, hg_touch⟩
    refine ⟨hg_polar, ?_⟩
    calc
      polarPairingFamily x g = ψ[Q] x := hg_touch
      _ = pointwiseSupremumOn Qᵒ polarPairingFamily x := by
        symm
        exact minkowskiFunctional_eq_pointwiseSupremumOn_polarSet
          (Q := Q) hQ_closed hQ_convex h0Q hx
  · rintro ⟨hg_polar, hg_active⟩
    refine ⟨hg_polar, ?_⟩
    calc
      polarPairingFamily x g = pointwiseSupremumOn Qᵒ polarPairingFamily x := hg_active
      _ = ψ[Q] x :=
        minkowskiFunctional_eq_pointwiseSupremumOn_polarSet
          (Q := Q) hQ_closed hQ_convex h0Q hx

/-- Active-vector reformulation in Proposition 3.18: for a closed convex set `Q` containing `0`
in a finite-dimensional real
inner-product space, the active polar indices at a finite point `x` are exactly the polar vectors
satisfying `⟪g, x⟫ = ψ_Q(x)`. -/
-- Proof sketch: combine the max formula for the gauge with the defining equality in
-- `activePointwiseSupremumOnIndices`. On `dom (ψ[Q])`, activity means the pairing reaches the
-- value `ψ[Q] x`.
theorem activePolarIndices_eq_activePolarVectors_of_minkowskiFunctional
    [FiniteDimensional ℝ E]
    (hQ_closed : IsClosed Q)
    (hQ_convex : Convex ℝ Q)
    (h0Q : (0 : E) ∈ Q)
    (hx : x ∈ dom (ψ[Q])) :
    activePointwiseSupremumOnIndices Qᵒ polarPairingFamily x =
      Qᵒ ∩ {g | polarPairingFamily x g = ψ[Q] x} := by
  -- Compare the active-index description with the previously proved touching characterization.
  calc
    activePointwiseSupremumOnIndices Qᵒ polarPairingFamily x = ∂ ψ[Q](x) := by
      symm
      exact subdifferential_minkowskiFunctional_eq_activePolarIndices
        (Q := Q) hQ_closed hQ_convex h0Q hx
    _ = Qᵒ ∩ {g | polarPairingFamily x g = ψ[Q] x} :=
      subdifferential_minkowskiFunctional_eq_polar_touching (Q := Q) (x := x) hx

end PolarSupport

end Subdifferential

end

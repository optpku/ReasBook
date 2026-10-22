/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Data.Real.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_2

noncomputable section

open ContinuousLinearMap
open scoped ClarkeDirectionalDerivative ClarkeDifferential

/- Domain sampling:
- primary domain: Clarke generalized gradients on real normed spaces, specialized to `x ↦ |x|`
- sampled chapter owners: `LocallyLipschitzAt`, `clarkeDirectionalDeriv`, `clarkeDifferential`,
  `mem_clarkeDifferential_iff`
- sampled mathlib owner for the one-dimensional dual embedding:
  `ContinuousLinearMap.toSpanSingleton`
- core/canonical owner reused here: `clarkeDifferential`
- source-facing layer here: the absolute-value example from Chapter 14
- primitive data: the canonical Clarke owner and the one-dimensional slope functional
- derived API here: the positive/negative/origin formulas for the Clarke differential of `|x|`
-/

section

local notation "DualSpace" => StrongDual ℝ ℝ

/-- Helper for Chapter14 Example 14.1-extra-2: the real absolute-value map is `1`-Lipschitz on
every closed ball. -/
lemma abs_lipschitzOn_closedBall (x r : ℝ) :
    LipschitzOnWith 1 abs (Metric.closedBall x r) := by
  -- The reverse triangle inequality gives the global `1`-Lipschitz estimate for `abs`.
  refine LipschitzOnWith.mk_one ?_
  intro y hy z hz
  simpa [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub y z

/-- Helper for Chapter14 Example 14.1-extra-2: every continuous linear functional on `ℝ` is
determined by its value at `1`. -/
lemma real_dual_eq_toSpanSingleton (ξ : DualSpace) :
    ξ = toSpanSingleton ℝ (ξ 1) := by
  -- In one dimension, linearity reduces every evaluation to the value at the basis vector `1`.
  symm
  apply ContinuousLinearMap.ext
  intro d
  simpa [ContinuousLinearMap.toSpanSingleton_apply, mul_comm] using
    (ξ.map_smul d (1 : ℝ)).symm

/-- The absolute-value function is locally Lipschitz at every real point. -/
instance absLocallyLipschitzAt (x : ℝ) : LocallyLipschitzAt abs x := by
  -- A global `1`-Lipschitz bound certainly holds on the unit closed ball around `x`.
  refine locallyLipschitzAt_of_closedBall (K := 1) ?_
  exact ⟨1, by norm_num, abs_lipschitzOn_closedBall x 1⟩

/-- For `x > 0`, the Clarke directional derivative of `x ↦ |x|` in direction `d` is `d`. -/
theorem clarkeDirectionalDeriv_abs_pos (x d : ℝ) (hx : 0 < x) :
    absᵒ(x; d) = d := by
  let s : Set (ℝ × ℝ) := clarkeDirectionalDerivWithinDomain Set.univ d
  let l : Filter (ℝ × ℝ) := nhdsWithin ((x : ℝ), (0 : ℝ)) s
  have hs : s = {p : ℝ × ℝ | 0 < p.2} := by
    ext p
    simp [s, clarkeDirectionalDerivWithinDomain]
  have hl_ne : l.NeBot := by
    simpa [l, s] using wholeSpaceClarkePairFilter_neBot x d
  letI := hl_ne
  have hy_pos : ∀ᶠ p in l, 0 < p.1 := by
    have hmem : Prod.fst ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds ((x : ℝ), (0 : ℝ)) := by
      simpa using
        (continuous_fst.continuousAt.preimage_mem_nhds
          (show Set.Ioi (0 : ℝ) ∈ nhds x from Ioi_mem_nhds hx))
    exact nhdsWithin_le_nhds hmem
  have hstep_pos : ∀ᶠ p in l, 0 < p.1 + p.2 * d := by
    have hcont : Continuous fun p : ℝ × ℝ ↦ p.1 + p.2 * d := by
      exact continuous_fst.add (continuous_snd.mul continuous_const)
    have hmem : (fun p : ℝ × ℝ ↦ p.1 + p.2 * d) ⁻¹' Set.Ioi (0 : ℝ) ∈
        nhds ((x : ℝ), (0 : ℝ)) := by
      simpa using
        (hcont.continuousAt.preimage_mem_nhds
          (show Set.Ioi (0 : ℝ) ∈ nhds (x + 0 * d) by
            simpa using (Ioi_mem_nhds hx)))
    exact nhdsWithin_le_nhds hmem
  have hquot_eq :
      (fun p : ℝ × ℝ ↦ (((abs (p.1 + p.2 * d) - abs p.1) / p.2 : ℝ) : EReal)) =ᶠ[l]
        fun _ ↦ ((d : ℝ) : EReal) := by
    -- Once both endpoints stay positive, the quotient collapses to the constant slope `d`.
    filter_upwards [hy_pos, hstep_pos, self_mem_nhdsWithin] with p hp1 hp2 hs_mem
    have hp2_pos : 0 < p.2 := (mem_clarkeDirectionalDerivWithinDomain.mp hs_mem).2.1
    have hp2_ne : p.2 ≠ 0 := ne_of_gt hp2_pos
    have hreal : (abs (p.1 + p.2 * d) - abs p.1) / p.2 = d := by
      rw [abs_of_pos hp2, abs_of_pos hp1]
      have hnum : p.1 + p.2 * d - p.1 = p.2 * d := by ring
      rw [hnum]
      field_simp [hp2_ne]
    exact_mod_cast hreal
  have hquot_tendsto :
      Filter.Tendsto
        (fun p : ℝ × ℝ ↦ (((abs (p.1 + p.2 * d) - abs p.1) / p.2 : ℝ) : EReal))
        l
        (nhds ((d : ℝ) : EReal)) := by
    refine Filter.Tendsto.congr' hquot_eq.symm ?_
    simpa using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ × ℝ ↦ ((d : ℝ) : EReal)) l
        (nhds ((d : ℝ) : EReal)))
  -- The whole Clarke limsup is the limsup of a function eventually equal to a constant.
  rw [clarkeDirectionalDeriv_eq_limsup]
  simpa [l, s] using hquot_tendsto.limsup_eq

/-- For `x < 0`, the Clarke directional derivative of `x ↦ |x|` in direction `d` is `-d`. -/
theorem clarkeDirectionalDeriv_abs_neg (x d : ℝ) (hx : x < 0) :
    absᵒ(x; d) = -d := by
  let s : Set (ℝ × ℝ) := clarkeDirectionalDerivWithinDomain Set.univ d
  let l : Filter (ℝ × ℝ) := nhdsWithin ((x : ℝ), (0 : ℝ)) s
  have hs : s = {p : ℝ × ℝ | 0 < p.2} := by
    ext p
    simp [s, clarkeDirectionalDerivWithinDomain]
  have hl_ne : l.NeBot := by
    simpa [l, s] using wholeSpaceClarkePairFilter_neBot x d
  letI := hl_ne
  have hy_neg : ∀ᶠ p in l, p.1 < 0 := by
    have hmem : Prod.fst ⁻¹' Set.Iio (0 : ℝ) ∈ nhds ((x : ℝ), (0 : ℝ)) := by
      simpa using
        (continuous_fst.continuousAt.preimage_mem_nhds
          (show Set.Iio (0 : ℝ) ∈ nhds x from Iio_mem_nhds hx))
    exact nhdsWithin_le_nhds hmem
  have hstep_neg : ∀ᶠ p in l, p.1 + p.2 * d < 0 := by
    have hcont : Continuous fun p : ℝ × ℝ ↦ p.1 + p.2 * d := by
      exact continuous_fst.add (continuous_snd.mul continuous_const)
    have hmem : (fun p : ℝ × ℝ ↦ p.1 + p.2 * d) ⁻¹' Set.Iio (0 : ℝ) ∈
        nhds ((x : ℝ), (0 : ℝ)) := by
      simpa using
        (hcont.continuousAt.preimage_mem_nhds
          (show Set.Iio (0 : ℝ) ∈ nhds (x + 0 * d) by
            simpa using (Iio_mem_nhds hx)))
    exact nhdsWithin_le_nhds hmem
  have hquot_eq :
      (fun p : ℝ × ℝ ↦ (((abs (p.1 + p.2 * d) - abs p.1) / p.2 : ℝ) : EReal)) =ᶠ[l]
        fun _ ↦ (((-d : ℝ)) : EReal) := by
    -- On the negative branch, both absolute values linearize with slope `-1`.
    filter_upwards [hy_neg, hstep_neg, self_mem_nhdsWithin] with p hp1 hp2 hs_mem
    have hp2_pos : 0 < p.2 := (mem_clarkeDirectionalDerivWithinDomain.mp hs_mem).2.1
    have hp2_ne : p.2 ≠ 0 := ne_of_gt hp2_pos
    have hreal : (abs (p.1 + p.2 * d) - abs p.1) / p.2 = -d := by
      rw [abs_of_neg hp2, abs_of_neg hp1]
      have hnum : -(p.1 + p.2 * d) - -p.1 = -(p.2 * d) := by ring
      rw [hnum]
      field_simp [hp2_ne]
    exact_mod_cast hreal
  have hquot_tendsto :
      Filter.Tendsto
        (fun p : ℝ × ℝ ↦ (((abs (p.1 + p.2 * d) - abs p.1) / p.2 : ℝ) : EReal))
        l
        (nhds (((-d : ℝ)) : EReal)) := by
    refine Filter.Tendsto.congr' hquot_eq.symm ?_
    simpa using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ × ℝ ↦ (((-d : ℝ)) : EReal)) l
        (nhds (((-d : ℝ)) : EReal)))
  -- The limsup is the constant slope from the negative branch.
  rw [clarkeDirectionalDeriv_eq_limsup]
  simpa [l, s] using hquot_tendsto.limsup_eq

/-- At `x = 0`, the Clarke directional derivative of `x ↦ |x|` in direction `d` is `|d|`. -/
theorem clarkeDirectionalDeriv_abs_zero (d : ℝ) :
    absᵒ(0; d) = |d| := by
  have hupper :
      absᵒ(0; d) ≤ ((|d| : ℝ) : EReal) := by
    -- The global `1`-Lipschitz bound gives the standard Clarke upper estimate.
    obtain ⟨_, hupper⟩ :=
      clarkeDirectionalDeriv_bounds_of_closedBallLipschitz abs 0 d 1
        ⟨1, by norm_num, abs_lipschitzOn_closedBall 0 1⟩
    simpa [Real.norm_eq_abs] using hupper
  have hupperDini :
      upperDiniDirectionalDerivWithin Set.univ abs ⟨(0 : ℝ), by simp⟩ d = ((|d| : ℝ) : EReal) := by
    -- Along the constant base path `y = 0`, the one-sided quotient is already the constant `|d|`.
    rw [upperDiniDirectionalDerivWithin_eq_limsup]
    have hdomain :
        Set.Ioi (0 : ℝ) ∩ {t : ℝ | (0 : ℝ) + t • d ∈ Set.univ} = Set.Ioi (0 : ℝ) := by
      ext t
      simp
    rw [hdomain]
    have hIoi_ne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := by
      refine (mem_closure_iff_nhdsWithin_neBot.1 ?_)
      simpa [closure_Ioi]
    letI := hIoi_ne
    have hquot_tendsto :
        Filter.Tendsto
          (fun t : ℝ ↦ (((abs ((0 : ℝ) + t * d) - abs (0 : ℝ)) / t : ℝ) : EReal))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((|d| : ℝ) : EReal)) := by
      have hquot_eq :
          (fun t : ℝ ↦ (((abs ((0 : ℝ) + t * d) - abs (0 : ℝ)) / t : ℝ) : EReal)) =ᶠ[
            nhdsWithin (0 : ℝ) (Set.Ioi 0)]
            fun _ ↦ ((|d| : ℝ) : EReal) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht_pos : 0 < t := ht
        have ht_ne : t ≠ 0 := ne_of_gt ht_pos
        have hreal : (abs ((0 : ℝ) + t * d) - abs (0 : ℝ)) / t = |d| := by
          rw [abs_zero, zero_add, abs_mul, abs_of_pos ht_pos]
          have hnum : t * |d| - 0 = t * |d| := by ring
          rw [hnum]
          field_simp [ht_ne]
        exact_mod_cast hreal
      refine Filter.Tendsto.congr' hquot_eq.symm ?_
      exact
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ ↦ ((|d| : ℝ) : EReal))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds ((|d| : ℝ) : EReal)))
    simpa using hquot_tendsto.limsup_eq
  have hlower :
      ((|d| : ℝ) : EReal) ≤ absᵒ(0; d) := by
    -- Compare the upper-Dini derivative with the Clarke derivative under local Lipschitz control.
    have hlocal : LocallyLipschitzWithinAt Set.univ abs ⟨(0 : ℝ), by simp⟩ := by
      refine ⟨1, Metric.closedBall (0 : ℝ) 1, ?_, abs_lipschitzOn_closedBall 0 1⟩
      simpa using (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
    have hcompare :
        upperDiniDirectionalDerivWithin Set.univ abs ⟨(0 : ℝ), by simp⟩ d ≤
          clarkeDirectionalDerivWithin Set.univ abs ⟨(0 : ℝ), by simp⟩ d :=
      upperDiniDirectionalDerivWithin_le_clarkeDirectionalDerivWithin hlocal
    simpa [clarkeDirectionalDeriv] using
      (show ((|d| : ℝ) : EReal) ≤ clarkeDirectionalDerivWithin Set.univ abs ⟨(0 : ℝ), by simp⟩ d by
        rw [← hupperDini]
        exact hcompare)
  -- The lower and upper estimates meet at the common value `|d|`.
  exact le_antisymm hupper (by simpa using hlower)

/-- Membership of the slope functional `toSpanSingleton ℝ ξ` in the Clarke differential of
`x ↦ |x|` is exactly the source inequality `fᵒ(x; d) ≥ ξ * d` for every direction `d`. -/
theorem mem_absClarkeDifferential_iff (x ξ : ℝ) :
    toSpanSingleton ℝ ξ ∈ (∂ᶜ abs) x ↔
      ∀ d : ℝ, absᵒ(x; d) ≥ ξ * d := by
  -- Unfold Clarke membership and evaluate the one-dimensional functional explicitly.
  rw [mem_clarkeDifferential_iff]
  constructor
  · intro h d
    simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using h d
  · intro h d
    simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm] using h d

/-- Helper for Chapter14 Example 14.1-extra-2: the universal inequality `|d| ≥ ξ d` for all
directions is equivalent to the scalar slope lying in the interval `[-1, 1]`. -/
lemma abs_zero_slope_iff_mem_Icc (ξ : ℝ) :
    (∀ d : ℝ, |d| ≥ ξ * d) ↔ ξ ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · intro h
    -- Testing the inequality on the directions `1` and `-1` pins down the interval bounds.
    have hpos : ξ ≤ 1 := by
      simpa using h 1
    have hneg : -1 ≤ ξ := by
      have hneg' : 1 ≥ ξ * (-1 : ℝ) := by simpa using h (-1)
      linarith
    exact ⟨hneg, hpos⟩
  · intro h d
    -- Inside `[-1,1]`, the product `ξ * d` is controlled by `|ξ| * |d| ≤ |d|`.
    have hξabs : |ξ| ≤ 1 := by
      exact abs_le.mpr h
    calc
      ξ * d ≤ |ξ * d| := le_abs_self _
      _ = |ξ| * |d| := by rw [abs_mul]
      _ ≤ 1 * |d| := by
        exact mul_le_mul_of_nonneg_right hξabs (abs_nonneg d)
      _ = |d| := by ring

/-- Chapter14 Example 14.1-extra-2 (1): for `x > 0`, the Clarke differential of `x ↦ |x|`
reduces to the singleton generated by the slope `1`. -/
theorem absClarkeDifferential_pos (x : ℝ) (hx : 0 < x) :
    (∂ᶜ abs) x = ({toSpanSingleton ℝ 1} : Set DualSpace) := by
  ext ξ
  constructor
  · intro hξ
    -- Reduce to the scalar slope `ξ 1` and test the source inequality at `d = ±1`.
    have hξ' := hξ
    rw [real_dual_eq_toSpanSingleton ξ] at hξ'
    have hslope' := (mem_absClarkeDifferential_iff x (ξ 1)).mp hξ'
    have hle : ξ 1 ≤ 1 := by
      have hleE : (((ξ 1 : ℝ)) : EReal) ≤ (((1 : ℝ)) : EReal) := by
        simpa [clarkeDirectionalDeriv_abs_pos x 1 hx] using hslope' 1
      exact_mod_cast hleE
    have hge : 1 ≤ ξ 1 := by
      have hnegE : (((ξ 1 * (-1 : ℝ) : ℝ)) : EReal) ≤ (((-1 : ℝ)) : EReal) := by
        simpa [clarkeDirectionalDeriv_abs_pos x (-1) hx, mul_comm] using hslope' (-1)
      have hneg : ξ 1 * (-1 : ℝ) ≤ -1 := by
        exact_mod_cast hnegE
      linarith
    have hξ1 : ξ 1 = 1 := le_antisymm hle hge
    rw [Set.mem_singleton_iff]
    calc
      ξ = toSpanSingleton ℝ (ξ 1) := real_dual_eq_toSpanSingleton ξ
      _ = toSpanSingleton ℝ 1 := by rw [hξ1]
  · intro hξ
    rcases Set.mem_singleton_iff.mp hξ with rfl
    -- The slope functional with coefficient `1` satisfies the Clarke inequality exactly.
    rw [mem_absClarkeDifferential_iff]
    intro d
    have hE : (((d : ℝ)) : EReal) ≤ (((d : ℝ)) : EReal) := le_rfl
    simpa [clarkeDirectionalDeriv_abs_pos x d hx] using hE

/-- Chapter14 Example 14.1-extra-2 (2): for `x < 0`, the Clarke differential of `x ↦ |x|`
reduces to the singleton generated by the slope `-1`. -/
theorem absClarkeDifferential_neg (x : ℝ) (hx : x < 0) :
    (∂ᶜ abs) x = ({toSpanSingleton ℝ (-1)} : Set DualSpace) := by
  ext ξ
  constructor
  · intro hξ
    -- Reduce to the scalar slope `ξ 1` and test the negative-branch inequality at `d = ±1`.
    have hξ' := hξ
    rw [real_dual_eq_toSpanSingleton ξ] at hξ'
    have hslope' := (mem_absClarkeDifferential_iff x (ξ 1)).mp hξ'
    have hle : ξ 1 ≤ -1 := by
      have hleE : (((ξ 1 : ℝ)) : EReal) ≤ (((-1 : ℝ)) : EReal) := by
        simpa [clarkeDirectionalDeriv_abs_neg x 1 hx] using hslope' 1
      exact_mod_cast hleE
    have hge : -1 ≤ ξ 1 := by
      have hnegE : (((ξ 1 * (-1 : ℝ) : ℝ)) : EReal) ≤ (((1 : ℝ)) : EReal) := by
        simpa [clarkeDirectionalDeriv_abs_neg x (-1) hx, mul_comm] using hslope' (-1)
      have hneg : ξ 1 * (-1 : ℝ) ≤ 1 := by
        exact_mod_cast hnegE
      linarith
    have hξ1 : ξ 1 = -1 := le_antisymm hle hge
    rw [Set.mem_singleton_iff]
    calc
      ξ = toSpanSingleton ℝ (ξ 1) := real_dual_eq_toSpanSingleton ξ
      _ = toSpanSingleton ℝ (-1) := by rw [hξ1]
  · intro hξ
    rcases Set.mem_singleton_iff.mp hξ with rfl
    -- The slope functional with coefficient `-1` matches the negative branch derivative.
    rw [mem_absClarkeDifferential_iff]
    intro d
    have hE : (((-d : ℝ)) : EReal) ≤ (((-d : ℝ)) : EReal) := le_rfl
    simpa [clarkeDirectionalDeriv_abs_neg x d hx] using hE

/-- Chapter14 Example 14.1-extra-2 (3): at `x = 0`, the Clarke differential of `x ↦ |x|`
is the image of the interval `[-1, 1]` under the canonical scalar-to-dual embedding. -/
theorem absClarkeDifferential_zero :
    (∂ᶜ abs) 0 = toSpanSingleton ℝ '' Set.Icc (-1 : ℝ) 1 := by
  ext ξ
  constructor
  · intro hξ
    -- Evaluate `ξ` at `1` and recover interval membership from the scalar inequality.
    have hξ' := hξ
    rw [real_dual_eq_toSpanSingleton ξ] at hξ'
    have hslope : ∀ d : ℝ, |d| ≥ ξ 1 * d := by
      intro d
      have hslope' : (((ξ 1 * d : ℝ)) : EReal) ≤ (((|d| : ℝ)) : EReal) := by
        simpa [clarkeDirectionalDeriv_abs_zero, mul_comm] using
          (mem_absClarkeDifferential_iff 0 (ξ 1)).mp hξ' d
      exact_mod_cast hslope'
    refine ⟨ξ 1, (abs_zero_slope_iff_mem_Icc (ξ 1)).mp hslope, (real_dual_eq_toSpanSingleton ξ).symm⟩
  · rintro ⟨ξ, hξ, rfl⟩
    -- Any slope in `[-1,1]` gives a supporting affine functional at the origin.
    rw [mem_absClarkeDifferential_iff]
    intro d
    have hd : ξ * d ≤ |d| := (abs_zero_slope_iff_mem_Icc ξ).mpr hξ d
    have hdE : (((ξ * d : ℝ)) : EReal) ≤ (((|d| : ℝ)) : EReal) := by
      exact_mod_cast hd
    simpa [clarkeDirectionalDeriv_abs_zero, mul_comm] using hdE

/-- The scalar slopes whose associated functionals lie in the Clarke differential at a positive
point are exactly `{1}`. -/
theorem absClarkeDifferential_pos_slopes (x : ℝ) (hx : 0 < x) :
    {ξ : ℝ | toSpanSingleton ℝ ξ ∈ (∂ᶜ abs) x} = ({1} : Set ℝ) := by
  ext ξ
  constructor
  · intro hξ
    have hfun : toSpanSingleton ℝ ξ = toSpanSingleton ℝ 1 := by
      rw [absClarkeDifferential_pos x hx] at hξ
      simpa using hξ
    have hone := congrArg (fun η : DualSpace ↦ η 1) hfun
    simpa [Set.mem_singleton_iff] using hone
  · intro hξ
    rcases Set.mem_singleton_iff.mp hξ with rfl
    rw [absClarkeDifferential_pos x hx]
    simp

/-- The scalar slopes whose associated functionals lie in the Clarke differential at a negative
point are exactly `{-1}`. -/
theorem absClarkeDifferential_neg_slopes (x : ℝ) (hx : x < 0) :
    {ξ : ℝ | toSpanSingleton ℝ ξ ∈ (∂ᶜ abs) x} = ({-1} : Set ℝ) := by
  ext ξ
  constructor
  · intro hξ
    have hfun : toSpanSingleton ℝ ξ = toSpanSingleton ℝ (-1) := by
      rw [absClarkeDifferential_neg x hx] at hξ
      simpa using hξ
    have hone := congrArg (fun η : DualSpace ↦ η 1) hfun
    simpa [Set.mem_singleton_iff] using hone
  · intro hξ
    rcases Set.mem_singleton_iff.mp hξ with rfl
    rw [absClarkeDifferential_neg x hx]
    simp

/-- At the origin, the scalar slopes whose associated functionals lie in the Clarke differential
form the interval `[-1, 1]`. -/
theorem absClarkeDifferential_zero_slopes :
    {ξ : ℝ | toSpanSingleton ℝ ξ ∈ (∂ᶜ abs) 0} = Set.Icc (-1 : ℝ) 1 := by
  ext ξ
  constructor
  · intro hξ
    rw [absClarkeDifferential_zero] at hξ
    rcases hξ with ⟨η, hη, hEq⟩
    have hval := congrArg (fun f : DualSpace ↦ f 1) hEq
    have hξη : ξ = η := by simpa using hval.symm
    simpa [Set.mem_setOf_eq, hξη] using hη
  · intro hξ
    rw [absClarkeDifferential_zero]
    exact ⟨ξ, hξ, rfl⟩

#print axioms absLocallyLipschitzAt
#print axioms absClarkeDifferential_zero

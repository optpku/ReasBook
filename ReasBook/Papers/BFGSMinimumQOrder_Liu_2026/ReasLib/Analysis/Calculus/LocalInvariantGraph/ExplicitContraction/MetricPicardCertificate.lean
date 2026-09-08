module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.MetricCutoff
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph.FixedPoint

public section

noncomputable section

open Filter
open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-!
# Metric Picard certificates for local invariant graphs

This module constructs the graph transform using only a small global Lipschitz remainder and
the metric inverse-center estimates.  In particular, it does not require the center projection
to be smooth for every element of the Lipschitz graph cone.  Finite smoothness of the resulting
fixed graph remains a separate regularity problem.
-/

/-- Helper for Infrastructure I.16a: the contraction rate of the metric graph transform when
the whole nonlinear remainder has Lipschitz constant `epsilon`. -/
def metricGraphTransformRate
    (lower linearRate epsilon slope : ℝ≥0) : ℝ≥0 :=
  linearRate + epsilon + (linearRate * slope + epsilon) * lower⁻¹ * epsilon

/-- Helper for Infrastructure I.16a: coercing `metricGraphTransformRate` to `ℝ` gives its
three-term scalar expansion. -/
theorem metricGraphTransformRate_coe
    (lower linearRate epsilon slope : ℝ≥0) :
    (metricGraphTransformRate lower linearRate epsilon slope : ℝ) =
      (linearRate : ℝ) + (epsilon : ℝ) +
        ((linearRate : ℝ) * (slope : ℝ) + (epsilon : ℝ)) *
          (lower : ℝ)⁻¹ * (epsilon : ℝ) := by
  simp only [metricGraphTransformRate, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_inv]

/-- Helper for Infrastructure I.16a: the linear-plus-fiber coefficient `linearRate + epsilon` is
bounded by the full metric transform rate.  This is `le_self_add` on the opaque rate (the trailing
`(linearRate * slope + epsilon) * lower⁻¹ * epsilon` summand is nonnegative), exposed here as a named
lemma so downstream leaves can bridge the combined operator norm `‖L + derivFiber‖ ≤ linearRate +
epsilon` to the certified `< 1` contraction factor without unfolding the (unexposed) rate. -/
theorem linearRate_add_epsilon_le_metricGraphTransformRate
    (lower linearRate epsilon slope : ℝ≥0) :
    linearRate + epsilon ≤ metricGraphTransformRate lower linearRate epsilon slope := by
  unfold metricGraphTransformRate
  exact le_self_add

/-- The real-cast form of `linearRate_add_epsilon_le_metricGraphTransformRate`, ready for the
leaf-level operator-norm bridge: `(linearRate : ℝ) + epsilon ≤ (metricGraphTransformRate …)`. -/
theorem linearRate_add_epsilon_le_metricGraphTransformRate_real
    (lower linearRate epsilon slope : ℝ≥0) :
    (linearRate : ℝ) + (epsilon : ℝ) ≤
      (metricGraphTransformRate lower linearRate epsilon slope : ℝ) := by
  have h := linearRate_add_epsilon_le_metricGraphTransformRate lower linearRate epsilon slope
  exact_mod_cast h

/-- Helper for Infrastructure I.16a: quantitative data for the metric graph transform of a
globally smooth, compactly supported, small Lipschitz remainder. -/
structure MetricGraphTransformData (X : Type u) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where
  nu : ℕ
  R : ℝ × X → ℝ × X
  L : X →L[ℝ] X
  radius : ℝ≥0
  slope : ℝ≥0
  epsilon : ℝ≥0
  lower : ℝ≥0
  linearRate : ℝ≥0
  stableBound : ℝ≥0
  hnu : 2 ≤ nu
  hR_smooth : ContDiff ℝ nu R
  hR_support : HasCompactSupport R
  hR_zero : R 0 = 0
  hR_lipschitz : LipschitzWith epsilon R
  hslope_one : slope ≤ 1
  hlower_pos : 0 < lower
  hlower_add : lower + epsilon = 1
  h_center_bijective : ∀ zeta : SmallLipschitzGraph X radius slope,
    Function.Bijective (fun u ↦ u + (R (u, zeta u)).1)
  h_inverse_lipschitz : ∀ zeta : SmallLipschitzGraph X radius slope,
    LipschitzWith lower⁻¹ (Function.invFun (fun u ↦ u + (R (u, zeta u)).1))
  h_inverse_dist : ∀ (zeta eta : SmallLipschitzGraph X radius slope) (ubar : ℝ),
    dist (Function.invFun (fun u ↦ u + (R (u, zeta u)).1) ubar)
      (Function.invFun (fun u ↦ u + (R (u, eta u)).1) ubar) ≤
      (lower⁻¹ : ℝ) * (epsilon : ℝ) * dist zeta eta
  hL : ‖L‖ ≤ (linearRate : ℝ)
  hlinearRate : linearRate < 1
  hstable_bound : ∀ p, ‖(R p).2‖ ≤ (stableBound : ℝ)
  hradius : linearRate * radius + stableBound ≤ radius
  hslope : (linearRate * slope + epsilon) * lower⁻¹ ≤ slope
  hrate : metricGraphTransformRate lower linearRate epsilon slope < 1

namespace MetricGraphTransformData

/-- Helper for Infrastructure I.16a: Bernoulli's lower bound for powers of a number in
the unit interval. -/
theorem one_sub_mul_pow_lower_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hfactor : 0 ≤ 1 - x := sub_nonneg.mpr hx1
      have hmul := mul_le_mul_of_nonneg_right ih hfactor
      rw [pow_succ]
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      rw [hcast]
      nlinarith [hmul, mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hx0) hx0]

/-- A stable contraction rate admits metric graph-transform parameters satisfying all finite-order
bunching inequalities. -/
theorem exists_metricTransformParameters
    (ν : ℕ) (a stableBound : NNReal) (hν : 2 ≤ ν) (ha : (a : ℝ) < 1) :
    ∃ epsilon lower linearRate radius : NNReal,
      0 < epsilon ∧
        0 < lower ∧
          lower + epsilon = 1 ∧
            a ≤ linearRate ∧
              linearRate < 1 ∧
                linearRate * radius + stableBound ≤ radius ∧
                  (linearRate + epsilon) * lower⁻¹ ≤ 1 ∧
                    metricGraphTransformRate lower linearRate epsilon 1 < 1 ∧
                    (∀ r : ℕ, 1 ≤ r → r ≤ ν →
                        (metricGraphTransformRate lower linearRate epsilon 1 : ℝ) *
                          (lower : ℝ)⁻¹ ^ r < 1) := by
  have haNN : a < 1 := by exact_mod_cast ha
  have hgapNN : 0 < 1 - a := tsub_pos_iff_lt.mpr haNN
  let epsilon : NNReal := (1 - a) / (2 * ((ν + 2 : ℕ) : NNReal))
  let lower : NNReal := 1 - epsilon
  let linearRate : NNReal := a
  let radius : NNReal := stableBound / (1 - a)
  have hden_pos : 0 < (2 * ((ν + 2 : ℕ) : NNReal)) := by positivity
  have htwo_nonneg_nn : (0 : NNReal) ≤ 2 := by norm_num
  have hepsilon_pos : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos hgapNN hden_pos
  have hepsilon_le_one : epsilon ≤ 1 := by
    have hνnat : 2 ≤ ν + 2 := by omega
    have hνcast : (2 : NNReal) ≤ ((ν + 2 : ℕ) : NNReal) := by exact_mod_cast hνnat
    have hden_ge_one : (1 : NNReal) ≤ 2 * ((ν + 2 : ℕ) : NNReal) := by
      calc
        (1 : NNReal) ≤ 2 := by norm_num
        _ ≤ 2 * ((ν + 2 : ℕ) : NNReal) := by
          calc
            (2 : NNReal) ≤ 2 * 2 := by norm_num
            _ ≤ 2 * ((ν + 2 : ℕ) : NNReal) :=
              mul_le_mul_of_nonneg_left hνcast htwo_nonneg_nn
    have hgap_le : 1 - a ≤ 1 := by
      exact tsub_le_self
    dsimp [epsilon]
    apply (div_le_iff₀ hden_pos).2
    simpa only [one_mul] using le_trans hgap_le hden_ge_one
  have hepsilon_lt_one : epsilon < 1 := by
    have hνnat : 2 ≤ ν + 2 := by omega
    have hνcast : (2 : NNReal) ≤ ((ν + 2 : ℕ) : NNReal) := by exact_mod_cast hνnat
    have hden_gt_one : (1 : NNReal) < 2 * ((ν + 2 : ℕ) : NNReal) := by
      calc
        (1 : NNReal) < 2 := by norm_num
        _ ≤ 2 * ((ν + 2 : ℕ) : NNReal) := by
          calc
            (2 : NNReal) ≤ 2 * 2 := by norm_num
            _ ≤ 2 * ((ν + 2 : ℕ) : NNReal) :=
              mul_le_mul_of_nonneg_left hνcast htwo_nonneg_nn
    dsimp [epsilon]
    apply (div_lt_iff₀ hden_pos).2
    have hden_gt_one_mul : (1 : NNReal) < 1 * (2 * ((ν + 2 : ℕ) : NNReal)) := by
      simpa only [one_mul] using hden_gt_one
    exact lt_of_le_of_lt tsub_le_self hden_gt_one_mul
  have hlower_pos : 0 < lower := by
    dsimp [lower]
    exact tsub_pos_iff_lt.mpr hepsilon_lt_one
  have hlower_coe_pos : 0 < (lower : ℝ) := by exact_mod_cast hlower_pos
  have hlower_coe_ne : (lower : ℝ) ≠ 0 := ne_of_gt hlower_coe_pos
  have hgap_coe : ((1 - a : NNReal) : ℝ) = 1 - (a : ℝ) := by
    rw [NNReal.coe_sub haNN.le]
    norm_num
  have hepsilon_coe : (epsilon : ℝ) =
      (1 - (a : ℝ)) / (2 * (ν + 2 : ℝ)) := by
    dsimp [epsilon]
    simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
    rw [hgap_coe]
    norm_num [Nat.cast_add]
  have hlower_coe : (lower : ℝ) = 1 - (epsilon : ℝ) := by
    dsimp [lower]
    rw [NNReal.coe_sub (le_of_lt hepsilon_lt_one)]
    norm_num
  have hlinearRate_lt : (linearRate : ℝ) < 1 := by
    dsimp [linearRate]
    exact ha
  have hlower_add : lower + epsilon = (1 : NNReal) := by
    dsimp [lower]
    exact tsub_add_cancel_of_le hepsilon_le_one
  have hradius : linearRate * radius + stableBound ≤ radius := by
    dsimp [linearRate, radius]
    field_simp [hgapNN.ne']
    rw [add_tsub_cancel_of_le haNN.le]
    simpa only [mul_one] using le_refl stableBound
  have hsum_strict : (linearRate : ℝ) + (epsilon : ℝ) < (lower : ℝ) := by
    have hstrict : (a : ℝ) + 2 * (epsilon : ℝ) < 1 := by
      rw [hepsilon_coe]
      have hνreal : 0 < (ν + 2 : ℝ) := by positivity
      have hgap_real : 0 < 1 - (a : ℝ) := sub_pos.mpr ha
      field_simp [hνreal.ne']
      nlinarith
    rw [hlower_coe]
    dsimp [linearRate]
    nlinarith [hepsilon_pos]
  have hsum_le : (linearRate + epsilon) * lower⁻¹ ≤ 1 := by
    have hsum_mul_le : (linearRate : ℝ) + (epsilon : ℝ) ≤ 1 * (lower : ℝ) := by
      simpa only [one_mul] using hsum_strict.le
    have hsum_real :
        ((linearRate : ℝ) + (epsilon : ℝ)) / (lower : ℝ) ≤ 1 :=
      (div_le_iff₀ hlower_coe_pos).2 hsum_mul_le
    apply (NNReal.coe_le_coe).mp
    simpa only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_one,
      div_eq_mul_inv] using hsum_real
  have hrate_real :
      (metricGraphTransformRate lower linearRate epsilon 1 : ℝ) =
        ((linearRate : ℝ) + (epsilon : ℝ)) / (lower : ℝ) := by
    have hlower_add_real : (lower : ℝ) + (epsilon : ℝ) = 1 := by
      exact_mod_cast hlower_add
    simp only [metricGraphTransformRate, NNReal.coe_add, NNReal.coe_mul,
      NNReal.coe_inv, NNReal.coe_one]
    field_simp [hlower_coe_ne]
    nlinarith [hlower_add_real]
  have hrate_lt : metricGraphTransformRate lower linearRate epsilon 1 < 1 := by
    have hreal : (metricGraphTransformRate lower linearRate epsilon 1 : ℝ) < 1 := by
      rw [hrate_real]
      have hsum_mul_lt : (linearRate : ℝ) + (epsilon : ℝ) < 1 * (lower : ℝ) := by
        simpa only [one_mul] using hsum_strict
      exact (div_lt_iff₀ hlower_coe_pos).2 hsum_mul_lt
    exact_mod_cast hreal
  have hfinite : ∀ r : ℕ, 1 ≤ r → r ≤ ν →
      (metricGraphTransformRate lower linearRate epsilon 1 : ℝ) *
        (lower : ℝ)⁻¹ ^ r < 1 := by
    intro r hr1 rle
    have hε0 : 0 ≤ (epsilon : ℝ) := by positivity
    have hε1 : (epsilon : ℝ) ≤ 1 := by exact_mod_cast hepsilon_le_one
    have hbern := one_sub_mul_pow_lower_bound hε0 hε1 (r + 1)
    have hsmall : (linearRate : ℝ) + (epsilon : ℝ) <
        1 - ((r + 1 : ℕ) : ℝ) * (epsilon : ℝ) := by
      rw [show (linearRate : ℝ) = (a : ℝ) by rfl]
      have hrle : (r : ℝ) ≤ (ν : ℝ) := by exact_mod_cast rle
      have hνreal : 0 < (ν + 2 : ℝ) := by positivity
      have hcoef : (r + 2 : ℝ) < 2 * (ν + 2 : ℝ) := by
        have hnat : r + 2 ≤ ν + 2 := by omega
        have hcast : (r + 2 : ℝ) ≤ (ν + 2 : ℝ) := by exact_mod_cast hnat
        nlinarith
      have hratio : (r + 2 : ℝ) / (2 * (ν + 2 : ℝ)) < 1 := by
        have hden_real_pos : 0 < (2 : ℝ) * (ν + 2 : ℝ) := by positivity
        have hcoef_mul : (r + 2 : ℝ) < 1 * (2 * (ν + 2 : ℝ)) := by
          simpa only [one_mul] using hcoef
        apply (div_lt_iff₀ hden_real_pos).2
        exact hcoef_mul
      have hgap_real : 0 < 1 - (a : ℝ) := sub_pos.mpr ha
      have hprod :
          (1 - (a : ℝ)) * ((r + 2 : ℝ) / (2 * (ν + 2 : ℝ))) <
            1 - (a : ℝ) :=
        by
          have htmp := mul_lt_mul_of_pos_left hratio hgap_real
          simpa only [mul_one] using htmp
      have hmul :
          (r + 2 : ℝ) * (epsilon : ℝ) =
            (1 - (a : ℝ)) * ((r + 2 : ℝ) / (2 * (ν + 2 : ℝ))) := by
        rw [hepsilon_coe]
        field_simp [hνreal.ne']
      have hcast_succ : ((r + 1 : ℕ) : ℝ) + 1 = (r + 2 : ℝ) := by
        norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
      nlinarith [hprod, hmul, hcast_succ]
    have hpow_pos : 0 < (lower : ℝ) ^ (r + 1) := pow_pos hlower_coe_pos _
    have hpow_lower : (linearRate : ℝ) + (epsilon : ℝ) <
        (lower : ℝ) ^ (r + 1) := by
      rw [← hlower_coe] at hbern
      exact lt_of_lt_of_le hsmall hbern
    rw [hrate_real]
    rw [inv_pow]
    field_simp [hlower_coe_ne]
    simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hpow_lower
  refine ⟨epsilon, lower, linearRate, radius, hepsilon_pos, hlower_pos, hlower_add,
    ?_, ?_, ?_, ?_, ?_, hfinite⟩
  · rfl
  · exact hlinearRate_lt
  · exact hradius
  · exact hsum_le
  · exact hrate_lt

/-- Helper for Infrastructure I.16a: the small remainder rate is strictly below one whenever
it leaves a positive center lower bound. -/
theorem epsilon_lt_one (d : MetricGraphTransformData X) : d.epsilon < 1 := by
  rw [← d.hlower_add]
  exact lt_add_of_pos_left d.epsilon d.hlower_pos

/-- Helper for Infrastructure I.16a: the center coordinate along a small graph. -/
def centerMap (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) : ℝ → ℝ :=
  fun u ↦ u + (d.R (u, zeta u)).1

/-- Helper for Infrastructure I.16a: the inverse center coordinate used by the metric graph
transform. -/
def inverseCenter (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) : ℝ → ℝ :=
  Function.invFun (d.centerMap zeta)

/-- The center map is the identity coordinate plus the first remainder component. -/
theorem centerMap_eq (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    d.centerMap zeta = fun u ↦ u + (d.R (u, zeta u)).1 := by
  rfl

/-- The inverse center map is the inverse function selected by `Function.invFun`. -/
theorem inverseCenter_eq (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    d.inverseCenter zeta = Function.invFun (d.centerMap zeta) := by
  rfl

/-- Helper for Infrastructure I.16a: the center coordinate fixes zero. -/
theorem centerMap_zero (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) : d.centerMap zeta 0 = 0 := by
  rw [centerMap, SmallLipschitzGraph.zero_apply]
  simpa only [Prod.mk_zero_zero, d.hR_zero, Prod.fst_zero, add_zero]

/-- Helper for Infrastructure I.16a: every metric center coordinate is globally bijective. -/
theorem centerMap_bijective (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    Function.Bijective (d.centerMap zeta) := by
  exact d.h_center_bijective zeta

/-- Helper for Infrastructure I.16a: the inverse center coordinate fixes zero. -/
theorem inverseCenter_zero (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) : d.inverseCenter zeta 0 = 0 := by
  have hleft := Function.leftInverse_invFun (d.centerMap_bijective zeta).1 0
  simpa only [inverseCenter, d.centerMap_zero zeta] using hleft

/-- Helper for Infrastructure I.16a: inverse center coordinates obey the reciprocal lower
Lipschitz bound. -/
theorem inverseCenter_lipschitzWith (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    LipschitzWith d.lower⁻¹ (d.inverseCenter zeta) := by
  exact d.h_inverse_lipschitz zeta

/-- Helper for Infrastructure I.16a: inverse centers of two graphs satisfy the uniform
cross-graph estimate required for contraction. -/
theorem inverseCenter_dist_le (d : MetricGraphTransformData X)
    (zeta eta : SmallLipschitzGraph X d.radius d.slope) (ubar : ℝ) :
    dist (d.inverseCenter zeta ubar) (d.inverseCenter eta ubar) ≤
      (d.lower⁻¹ : ℝ) * (d.epsilon : ℝ) * dist zeta eta := by
  exact d.h_inverse_dist zeta eta ubar

/-- Helper for Infrastructure I.16a: the pointwise stable output before it is bundled as a
small Lipschitz graph. -/
def rawTransform (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) : ℝ → X :=
  fun ubar ↦
    let u := d.inverseCenter zeta ubar
    d.L (zeta u) + (d.R (u, zeta u)).2

/-- The raw metric transform has its defining inverse-center formula. -/
theorem rawTransform_eq (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    d.rawTransform zeta = fun ubar ↦
      d.L (zeta (d.inverseCenter zeta ubar)) +
        (d.R (d.inverseCenter zeta ubar, zeta (d.inverseCenter zeta ubar))).2 := by
  rfl

/-- Helper for Infrastructure I.16a: the raw metric graph transform fixes zero. -/
theorem rawTransform_zero (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) : d.rawTransform zeta 0 = 0 := by
  rw [rawTransform, d.inverseCenter_zero zeta, SmallLipschitzGraph.zero_apply]
  simpa only [map_zero, Prod.mk_zero_zero, d.hR_zero, Prod.snd_zero, add_zero]

/-- Helper for Infrastructure I.16a: the raw metric graph transform is continuous. -/
theorem rawTransform_continuous (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    Continuous (d.rawTransform zeta) := by
  have hinverse : Continuous (d.inverseCenter zeta) :=
    (d.inverseCenter_lipschitzWith zeta).continuous
  have hzeta : Continuous (fun ubar ↦ zeta (d.inverseCenter zeta ubar)) :=
    (SmallLipschitzGraph.lipschitzWith zeta).continuous.comp hinverse
  have hgraph : Continuous
      (fun ubar ↦ (d.inverseCenter zeta ubar, zeta (d.inverseCenter zeta ubar))) :=
    hinverse.prodMk hzeta
  have hlinear : Continuous (fun ubar ↦ d.L (zeta (d.inverseCenter zeta ubar))) :=
    d.L.continuous.comp hzeta
  have hremainder : Continuous
      (fun ubar ↦ (d.R (d.inverseCenter zeta ubar,
        zeta (d.inverseCenter zeta ubar))).2) :=
    continuous_snd.comp (d.hR_lipschitz.continuous.comp hgraph)
  exact hlinear.add hremainder

/-- Helper for Infrastructure I.16a: every raw transform value stays inside the prescribed
uniform graph radius. -/
theorem norm_rawTransform_le (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (ubar : ℝ) :
    ‖d.rawTransform zeta ubar‖ ≤ (d.radius : ℝ) := by
  let u := d.inverseCenter zeta ubar
  have hzeta : ‖zeta u‖ ≤ (d.radius : ℝ) :=
    (BoundedContinuousFunction.norm_coe_le_norm
      (zeta : BoundedContinuousFunction ℝ X) u).trans (SmallLipschitzGraph.norm_le zeta)
  have hlinear : ‖d.L (zeta u)‖ ≤ (d.linearRate : ℝ) * (d.radius : ℝ) := by
    calc
      ‖d.L (zeta u)‖ ≤ ‖d.L‖ * ‖zeta u‖ := d.L.le_opNorm _
      _ ≤ (d.linearRate : ℝ) * (d.radius : ℝ) :=
        mul_le_mul d.hL hzeta (norm_nonneg _) d.linearRate.coe_nonneg
  have hradius_real :
      (d.linearRate : ℝ) * (d.radius : ℝ) + (d.stableBound : ℝ) ≤
        (d.radius : ℝ) := by
    exact_mod_cast d.hradius
  calc
    ‖d.rawTransform zeta ubar‖ =
        ‖d.L (zeta u) + (d.R (u, zeta u)).2‖ := by rfl
    _ ≤ ‖d.L (zeta u)‖ + ‖(d.R (u, zeta u)).2‖ := norm_add_le _ _
    _ ≤ (d.linearRate : ℝ) * (d.radius : ℝ) + (d.stableBound : ℝ) :=
      add_le_add hlinear (d.hstable_bound (u, zeta u))
    _ ≤ (d.radius : ℝ) := hradius_real

/-- Helper for Infrastructure I.16a: the raw metric graph transform has the sharp Lipschitz
constant obtained from the stable linear rate, graph slope, remainder size, and inverse-center
bound. -/
theorem rawTransform_lipschitzWith_sharp (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    LipschitzWith ((d.linearRate * d.slope + d.epsilon) * d.lower⁻¹)
      (d.rawTransform zeta) := by
  apply LipschitzWith.of_dist_le_mul
  intro ubar vbar
  let u := d.inverseCenter zeta ubar
  let v := d.inverseCenter zeta vbar
  have hinverse := (d.inverseCenter_lipschitzWith zeta).dist_le_mul ubar vbar
  have hinverse_real :
      |u - v| ≤ (d.lower⁻¹ : ℝ) * |ubar - vbar| := by
    simpa only [u, v, Real.dist_eq, NNReal.coe_inv] using hinverse
  have hzeta := (SmallLipschitzGraph.lipschitzWith zeta).dist_le_mul u v
  have hzeta_real : ‖zeta u - zeta v‖ ≤ (d.slope : ℝ) * |u - v| := by
    simpa only [dist_eq_norm, Real.dist_eq, Real.norm_eq_abs] using hzeta
  have hslope_one_real : (d.slope : ℝ) ≤ 1 := by
    exact_mod_cast d.hslope_one
  have hzeta_one : ‖zeta u - zeta v‖ ≤ |u - v| := by
    calc
      ‖zeta u - zeta v‖ ≤ (d.slope : ℝ) * |u - v| := hzeta_real
      _ ≤ 1 * |u - v| :=
        mul_le_mul_of_nonneg_right hslope_one_real (abs_nonneg _)
      _ = |u - v| := one_mul _
  have hgraph : dist (u, zeta u) (v, zeta v) ≤ |u - v| := by
    rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_le le_rfl hzeta_one
  have hlinear :
      ‖d.L (zeta u) - d.L (zeta v)‖ ≤
        (d.linearRate : ℝ) * (d.slope : ℝ) * |u - v| := by
    calc
      ‖d.L (zeta u) - d.L (zeta v)‖ = ‖d.L (zeta u - zeta v)‖ := by
        rw [map_sub]
      _ ≤ ‖d.L‖ * ‖zeta u - zeta v‖ := d.L.le_opNorm _
      _ ≤ (d.linearRate : ℝ) * ((d.slope : ℝ) * |u - v|) :=
        mul_le_mul d.hL hzeta_real (norm_nonneg _) d.linearRate.coe_nonneg
      _ = (d.linearRate : ℝ) * (d.slope : ℝ) * |u - v| := by ring
  have hremainder :
      ‖(d.R (u, zeta u)).2 - (d.R (v, zeta v)).2‖ ≤
        (d.epsilon : ℝ) * |u - v| := by
    calc
      ‖(d.R (u, zeta u)).2 - (d.R (v, zeta v)).2‖ =
          dist (d.R (u, zeta u)).2 (d.R (v, zeta v)).2 := by
        rw [dist_eq_norm]
      _ ≤ dist (d.R (u, zeta u)) (d.R (v, zeta v)) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      _ ≤ (d.epsilon : ℝ) * dist (u, zeta u) (v, zeta v) :=
        d.hR_lipschitz.dist_le_mul _ _
      _ ≤ (d.epsilon : ℝ) * |u - v| :=
        mul_le_mul_of_nonneg_left hgraph d.epsilon.coe_nonneg
  have hlinear_slope_epsilon_nonneg : 0 ≤
      (d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ) := by
    positivity
  rw [dist_eq_norm]
  calc
    ‖d.rawTransform zeta ubar - d.rawTransform zeta vbar‖ =
        ‖(d.L (zeta u) - d.L (zeta v)) +
          ((d.R (u, zeta u)).2 - (d.R (v, zeta v)).2)‖ := by
      simp only [rawTransform, u, v]
      congr 1
      abel
    _ ≤ ‖d.L (zeta u) - d.L (zeta v)‖ +
        ‖(d.R (u, zeta u)).2 - (d.R (v, zeta v)).2‖ := norm_add_le _ _
    _ ≤ ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) * |u - v| := by
      calc
        ‖d.L (zeta u) - d.L (zeta v)‖ +
            ‖(d.R (u, zeta u)).2 - (d.R (v, zeta v)).2‖ ≤
            (d.linearRate : ℝ) * (d.slope : ℝ) * |u - v| +
              (d.epsilon : ℝ) * |u - v| := add_le_add hlinear hremainder
        _ = ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            |u - v| := by ring
    _ ≤ ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
        ((d.lower⁻¹ : ℝ) * |ubar - vbar|) :=
      mul_le_mul_of_nonneg_left hinverse_real hlinear_slope_epsilon_nonneg
    _ = (((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
        (d.lower⁻¹ : ℝ)) * |ubar - vbar| := by ring

/-- Helper for Infrastructure I.16a: the sharp raw-transform estimate and the cone inequality
show that the metric graph transform preserves the prescribed Lipschitz cone. -/
theorem rawTransform_lipschitzWith (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    LipschitzWith d.slope (d.rawTransform zeta) := by
  exact (d.rawTransform_lipschitzWith_sharp zeta).weaken d.hslope

/-- Helper for Infrastructure I.16a: bundle the raw transform as a bounded continuous
function. -/
def boundedTransform (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) : BoundedContinuousFunction ℝ X :=
  BoundedContinuousFunction.ofNormedAddCommGroup (d.rawTransform zeta)
    (d.rawTransform_continuous zeta) d.radius (d.norm_rawTransform_le zeta)

/-- Helper for Infrastructure I.16a: the bounded transform evaluates by the raw metric
formula. -/
theorem boundedTransform_apply (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (ubar : ℝ) :
    d.boundedTransform zeta ubar = d.rawTransform zeta ubar := by
  rfl

/-- Helper for Infrastructure I.16a: the bounded transform obeys the prescribed uniform
radius. -/
theorem norm_boundedTransform_le (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) :
    ‖d.boundedTransform zeta‖ ≤ (d.radius : ℝ) := by
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
    (d.rawTransform_continuous zeta) d.radius.coe_nonneg (d.norm_rawTransform_le zeta)

/-- Helper for Infrastructure I.16a: the metric graph transform is a self-map of the cone of
small Lipschitz graphs. -/
def transform (d : MetricGraphTransformData X) :
    SmallLipschitzGraph X d.radius d.slope → SmallLipschitzGraph X d.radius d.slope :=
  fun zeta ↦ SmallLipschitzGraph.of (d.boundedTransform zeta)
    (d.rawTransform_zero zeta) (d.norm_boundedTransform_le zeta)
    (d.rawTransform_lipschitzWith zeta)

/-- Helper for Infrastructure I.16a: the bundled metric transform evaluates by its raw
inverse-center formula. -/
theorem transform_apply (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope) (ubar : ℝ) :
    d.transform zeta ubar = d.rawTransform zeta ubar := by
  rw [transform, SmallLipschitzGraph.coe_of]
  exact d.boundedTransform_apply zeta ubar

/-- Helper for Infrastructure I.16a: two raw metric transforms satisfy the explicit
graph-distance estimate encoded by `metricGraphTransformRate`. -/
theorem rawTransform_dist_apply_le (d : MetricGraphTransformData X)
    (zeta eta : SmallLipschitzGraph X d.radius d.slope) (ubar : ℝ) :
    dist (d.rawTransform zeta ubar) (d.rawTransform eta ubar) ≤
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
        dist zeta eta := by
  let u := d.inverseCenter zeta ubar
  let v := d.inverseCenter eta ubar
  have hinverse := d.inverseCenter_dist_le zeta eta ubar
  have hinverse_real : |u - v| ≤
      (d.lower⁻¹ : ℝ) * (d.epsilon : ℝ) * dist zeta eta := by
    simpa only [u, v, Real.dist_eq, NNReal.coe_inv, mul_assoc] using hinverse
  have hgraph_cross : ‖zeta u - eta v‖ ≤
      (d.slope : ℝ) * |u - v| + dist zeta eta := by
    calc
      ‖zeta u - eta v‖ ≤ ‖zeta u - zeta v‖ + ‖zeta v - eta v‖ := by
        have hdecomp : zeta u - eta v = (zeta u - zeta v) + (zeta v - eta v) := by
          abel
        rw [hdecomp]
        exact norm_add_le _ _
      _ ≤ (d.slope : ℝ) * |u - v| + dist zeta eta := by
        have hζ := (SmallLipschitzGraph.lipschitzWith zeta).dist_le_mul u v
        have hη := SmallLipschitzGraph.dist_apply_le zeta eta v
        simpa only [dist_eq_norm, Real.dist_eq, Real.norm_eq_abs] using add_le_add hζ hη
  have hpoint_dist : dist (u, zeta u) (v, eta v) ≤
      |u - v| + dist zeta eta := by
    have hslope_one_real : (d.slope : ℝ) ≤ 1 := by
      exact_mod_cast d.hslope_one
    have hslope_abs : (d.slope : ℝ) * |u - v| ≤ |u - v| := by
      calc
        (d.slope : ℝ) * |u - v| ≤ 1 * |u - v| :=
          mul_le_mul_of_nonneg_right hslope_one_real
            (abs_nonneg _)
        _ = |u - v| := one_mul _
    have hgraph_cross_one : ‖zeta u - eta v‖ ≤
        |u - v| + dist zeta eta := by
      exact hgraph_cross.trans (add_le_add_left hslope_abs _)
    rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_le (le_add_of_nonneg_right dist_nonneg) hgraph_cross_one
  have hlinear : ‖d.L (zeta u) - d.L (eta v)‖ ≤
      (d.linearRate : ℝ) *
        ((d.slope : ℝ) * |u - v| + dist zeta eta) := by
    calc
      ‖d.L (zeta u) - d.L (eta v)‖ = ‖d.L (zeta u - eta v)‖ := by
        rw [map_sub]
      _ ≤ ‖d.L‖ * ‖zeta u - eta v‖ := d.L.le_opNorm _
      _ ≤ (d.linearRate : ℝ) *
          ((d.slope : ℝ) * |u - v| + dist zeta eta) := by
        exact mul_le_mul d.hL hgraph_cross (norm_nonneg _)
          d.linearRate.coe_nonneg
  have hstable : ‖(d.R (u, zeta u)).2 - (d.R (v, eta v)).2‖ ≤
      (d.epsilon : ℝ) * (|u - v| + dist zeta eta) := by
    calc
      ‖(d.R (u, zeta u)).2 - (d.R (v, eta v)).2‖ =
          dist (d.R (u, zeta u)).2 (d.R (v, eta v)).2 := by
        rw [dist_eq_norm]
      _ ≤ dist (d.R (u, zeta u)) (d.R (v, eta v)) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      _ ≤ (d.epsilon : ℝ) * dist (u, zeta u) (v, eta v) :=
        d.hR_lipschitz.dist_le_mul _ _
      _ ≤ (d.epsilon : ℝ) * (|u - v| + dist zeta eta) :=
        mul_le_mul_of_nonneg_left hpoint_dist d.epsilon.coe_nonneg
  have hraw : dist (d.rawTransform zeta ubar) (d.rawTransform eta ubar) ≤
      (d.linearRate : ℝ) *
          ((d.slope : ℝ) * |u - v| + dist zeta eta) +
        (d.epsilon : ℝ) * (|u - v| + dist zeta eta) := by
    rw [dist_eq_norm, rawTransform, rawTransform]
    calc
      ‖d.L (zeta (d.inverseCenter zeta ubar)) +
          (d.R (d.inverseCenter zeta ubar,
            zeta (d.inverseCenter zeta ubar))).2 -
          (d.L (eta (d.inverseCenter eta ubar)) +
            (d.R (d.inverseCenter eta ubar,
              eta (d.inverseCenter eta ubar))).2)‖ =
          ‖(d.L (zeta u) - d.L (eta v)) +
            ((d.R (u, zeta u)).2 - (d.R (v, eta v)).2)‖ := by
        congr 1
        simp only [u, v]
        abel
      _ ≤ ‖d.L (zeta u) - d.L (eta v)‖ +
          ‖(d.R (u, zeta u)).2 - (d.R (v, eta v)).2‖ := norm_add_le _ _
      _ ≤ (d.linearRate : ℝ) *
          ((d.slope : ℝ) * |u - v| + dist zeta eta) +
          (d.epsilon : ℝ) * (|u - v| + dist zeta eta) :=
        add_le_add hlinear hstable
  have hcoeff_nonneg : 0 ≤
      (d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ) := by positivity
  have hrate_real :
      (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) =
        (d.linearRate : ℝ) + (d.epsilon : ℝ) +
          ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
            (d.lower⁻¹ : ℝ) * (d.epsilon : ℝ) := by
    simp only [metricGraphTransformRate, NNReal.coe_add, NNReal.coe_mul,
      NNReal.coe_inv]
  calc
    dist (d.rawTransform zeta ubar) (d.rawTransform eta ubar) ≤
        (d.linearRate : ℝ) *
            ((d.slope : ℝ) * |u - v| + dist zeta eta) +
          (d.epsilon : ℝ) * (|u - v| + dist zeta eta) := hraw
    _ = ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          |u - v| + ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * dist zeta eta := by
      ring
    _ ≤ ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
          ((d.lower⁻¹ : ℝ) * (d.epsilon : ℝ) * dist zeta eta) +
        ((d.linearRate : ℝ) + (d.epsilon : ℝ)) * dist zeta eta := by
      gcongr
    _ = (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope : ℝ) *
          dist zeta eta := by
      rw [hrate_real]
      ring

/-- Helper for Infrastructure I.16a: the bundled metric graph transform is a strict
contraction in the uniform graph metric. -/
theorem transform_contracting (d : MetricGraphTransformData X) :
    ContractingWith (metricGraphTransformRate d.lower d.linearRate d.epsilon d.slope)
      d.transform := by
  apply SmallLipschitzGraph.contractingWith_of_dist_apply_le_mul d.hrate
  intro zeta eta ubar
  rw [d.transform_apply, d.transform_apply]
  exact d.rawTransform_dist_apply_le zeta eta ubar

/-- Infrastructure I.16a: a complete metric graph-transform certificate produces a canonical
fixed graph.  This theorem is intentionally metric, and finite `C^ν` regularity is supplied by the
separate finite-smooth bootstrap. -/
theorem exists_metricFixedGraph [CompleteSpace X]
    (d : MetricGraphTransformData X) :
    ∃ zeta : SmallLipschitzGraph X d.radius d.slope,
      d.transform zeta = zeta := by
  let hcontract := d.transform_contracting
  refine ⟨ContractingWith.fixedPoint d.transform hcontract, ?_⟩
  exact hcontract.fixedPoint_isFixedPt

/-- Helper for Infrastructure I.16a: every fixed graph inherits the sharp raw-transform
Lipschitz constant. -/
theorem fixedGraph_lipschitzWith_sharp [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta) :
    LipschitzWith ((d.linearRate * d.slope + d.epsilon) * d.lower⁻¹)
      (zeta : ℝ → X) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [← hfixed, d.transform_apply, d.transform_apply]
  exact (d.rawTransform_lipschitzWith_sharp zeta).dist_le_mul u v

/-- Helper for Infrastructure I.16a: the derivative of a metric fixed graph is bounded by
the sharp Lipschitz constant at every center coordinate. -/
theorem norm_deriv_fixedGraph_le_sharp [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta) (u : ℝ) :
    ‖deriv (zeta : ℝ → X) u‖ ≤
      ((d.linearRate : ℝ) * (d.slope : ℝ) + (d.epsilon : ℝ)) *
        (d.lower : ℝ)⁻¹ := by
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_inv] using
    norm_deriv_le_of_lipschitz (d.fixedGraph_lipschitzWith_sharp zeta hfixed)

/-- Infrastructure I.16a: the metric fixed graph satisfies the forward invariance equation
in the original center parameter, before any smoothness or tangent argument is applied. -/
theorem fixedGraph_equation [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (zeta : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform zeta = zeta) :
    ∀ u : ℝ, zeta (d.centerMap zeta u) =
      d.L (zeta u) + (d.R (u, zeta u)).2 := by
  intro u
  have hleft := congrArg
    (fun eta : SmallLipschitzGraph X d.radius d.slope ↦ eta (d.centerMap zeta u)) hfixed
  rw [d.transform_apply] at hleft
  have hinverse : d.inverseCenter zeta (d.centerMap zeta u) = u := by
    exact Function.leftInverse_invFun (d.centerMap_bijective zeta).1 u
  rw [rawTransform, hinverse] at hleft
  exact hleft.symm

end MetricGraphTransformData

end LocalInvariantGraph

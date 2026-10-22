/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

open MeasureTheory
open scoped NNReal Topology

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

/-- Helper for Theorem 21.17: the `i`th shifted mesh block event asks that `k` consecutive
increments of mesh `1 / (n + 1)` starting at the grid point
`m + i / (n + 1)` all have size at most `N * (1 / (n + 1))^γ`. -/
def smallIncrementBlockSlice
    (B : NNReal → Ω → ℝ) (γ : Set.Ioc (0 : ℝ≥0) 1) (k N m n i : ℕ) : Set Ω :=
  ⋂ l ∈ Finset.range k,
    {ω | |B ((m : NNReal) + ((i + l + 1 : ℕ) : NNReal) / (n + 1)) ω -
        B ((m : NNReal) + ((i + l : ℕ) : NNReal) / (n + 1)) ω|
      ≤ (N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)}

/-- Helper for Theorem 21.17: on the `m`th unit window, at mesh `1 / (n + 1)`, there is some
start index among the first `n + 1` mesh points from which `k` consecutive increments are all
small. -/
def smallIncrementBlockEvent
    (B : NNReal → Ω → ℝ) (γ : Set.Ioc (0 : ℝ≥0) 1) (k N m n : ℕ) : Set Ω :=
  ⋃ i ∈ Finset.range (n + 1), smallIncrementBlockSlice B γ k N m n i

/-- Helper for Theorem 21.17: for a centered Gaussian law with nonzero variance, the mass of the
interval `{x : ℝ | |x| ≤ R}` is bounded by the interval length times the maximal density height.
-/
lemma gaussianReal_abs_le_densityHeight {v : ℝ≥0} {R : ℝ}
    (_hR : 0 ≤ R) (hv : v ≠ 0) :
    gaussianReal 0 v {x : ℝ | |x| ≤ R} ≤
      ENNReal.ofReal (2 * R * (Real.sqrt (2 * Real.pi * v))⁻¹) := by
  let c : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹
  have hpoint : ∀ x : ℝ, gaussianPDF 0 v x ≤ ENNReal.ofReal c := by
    intro x
    rw [gaussianPDF_def, gaussianPDFReal_def]
    refine ENNReal.ofReal_le_ofReal ?_
    have hvpos : 0 < (v : ℝ) := by
      exact_mod_cast (show 0 < v from pos_iff_ne_zero.mpr hv)
    have hneg : -(x - 0) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
      have hnum : -(x - 0) ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (x - 0)]
      have hden : 0 ≤ 2 * (v : ℝ) := by
        positivity
      exact div_nonpos_of_nonpos_of_nonneg hnum hden
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * v)) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr hneg
    have hmul : c * Real.exp (-(x - 0) ^ 2 / (2 * v)) ≤ c * 1 := by
      exact mul_le_mul_of_nonneg_left hexp hc_nonneg
    simpa [c] using hmul
  have hset : {x : ℝ | |x| ≤ R} = Set.Icc (-R) R := by
    ext x
    simp [abs_le]
  -- Proof comment: bound the Gaussian density on the whole interval by its height at the origin,
  -- then integrate that constant over the interval of length `2 * R`.
  rw [hset, gaussianReal_apply _ hv]
  calc
    ∫⁻ x in Set.Icc (-R) R, gaussianPDF 0 v x ≤
        ∫⁻ _ in Set.Icc (-R) R, ENNReal.ofReal c := by
          refine lintegral_mono fun x ↦ hpoint x
    _ = ENNReal.ofReal c * volume (Set.Icc (-R) R) := setLIntegral_const _ _
    _ = ENNReal.ofReal c * ENNReal.ofReal (R - -R) := by
          rw [Real.volume_Icc]
    _ = ENNReal.ofReal c * ENNReal.ofReal (2 * R) := by
          congr 1
          ring_nf
    _ = ENNReal.ofReal (c * (2 * R)) := by
          rw [← ENNReal.ofReal_mul]
          positivity
    _ = ENNReal.ofReal (2 * R * (Real.sqrt (2 * Real.pi * v))⁻¹) := by
          congr 1
          ring

/-- Helper for Theorem 21.17: a Brownian increment over an ordered time interval has the centered
Gaussian law with variance equal to the time lag. -/
lemma brownianIncrement_hasLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun ω ↦ B t ω - B s ω) (gaussianReal 0 (t - s)) μ := by
  by_cases hEq : s = t
  · letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    -- Proof comment: a zero-length increment is the constant-zero random variable.
    subst hEq
    have hConst : HasLaw (fun _ : Ω ↦ (0 : ℝ)) (gaussianReal 0 0) μ := by
      constructor
      · exact measurable_const.aemeasurable
      · rw [Measure.map_const]
        simp [gaussianReal_zero_var]
    simpa using hConst
  · let u : NNReal := t - s
    have hu_pos : 0 < u := by
      exact tsub_pos_of_lt (lt_of_le_of_ne hst hEq)
    have hLawU : HasLaw (B u) (gaussianReal 0 u) μ := hB.gaussian_marginal hu_pos
    have hLawZero : HasLaw (fun ω ↦ B (u + 0) ω - B 0 ω) (gaussianReal 0 u) μ := by
      have hLawBase : HasLaw (fun ω ↦ B u ω - B 0 ω) (gaussianReal 0 u) μ := by
        refine hLawU.congr ?_
        simp [hB.zero]
      simpa using hLawBase
    have hStationary := hB.stationaryIncrements 0 u s
    have hu_add : u + s = t := by
      simp [u, tsub_add_cancel_of_le hst]
    -- Proof comment: stationary increments transport the Brownian law on `[0, u]` to `[s, t]`.
    simpa [u, hu_add, add_comm, add_left_comm, add_assoc] using hStationary.symm.hasLaw hLawZero

/-- Helper for Theorem 21.17: every consecutive increment on the uniform mesh
`m + (i + l) / (n + 1)` has the centered Gaussian law with variance `(n + 1)⁻¹`. -/
lemma meshIncrement_hasLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (m n i l : ℕ) :
    HasLaw
      (fun ω ↦
        B ((m : NNReal) + ((i + l + 1 : ℕ) : NNReal) / (n + 1)) ω -
          B ((m : NNReal) + ((i + l : ℕ) : NNReal) / (n + 1)) ω)
      (gaussianReal 0 (((n + 1 : ℕ) : ℝ≥0)⁻¹)) μ := by
  let s : NNReal := (m : NNReal) + ((i + l : ℕ) : NNReal) / (n + 1)
  let t : NNReal := (m : NNReal) + ((i + l + 1 : ℕ) : NNReal) / (n + 1)
  have hst :
      s ≤ t := by
    have hnum : ((i + l : ℕ) : NNReal) ≤ ((i + l + 1 : ℕ) : NNReal) := by
      exact_mod_cast Nat.le_succ (i + l)
    have hdiv :
        ((i + l : ℕ) : NNReal) / (n + 1) ≤
          ((i + l + 1 : ℕ) : NNReal) / (n + 1) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      gcongr
    simpa [s, t, add_assoc] using add_le_add_left hdiv (m : NNReal)
  have hstep :
      t - s =
        (((n + 1 : ℕ) : ℝ≥0)⁻¹) := by
    -- Proof comment: the consecutive mesh points differ by exactly one mesh step.
    ext
    rw [NNReal.coe_sub hst]
    simp [s, t, div_eq_mul_inv, add_assoc]
    ring
  -- Proof comment: apply the Brownian increment-law owner lemma to the ordered mesh pair, then
  -- rewrite the time lag to the fixed mesh variance.
  have hLaw :
      HasLaw
        (fun ω ↦ B t ω - B s ω)
        (gaussianReal 0 (t - s)) μ :=
    brownianIncrement_hasLaw hB hst
  have hLaw' :
      HasLaw
        (fun ω ↦ B t ω - B s ω)
        (gaussianReal 0 (((n + 1 : ℕ) : ℝ≥0)⁻¹)) μ := by
    simpa [hstep] using hLaw
  simpa [s, t] using hLaw'

/-- Helper for Theorem 21.17: a fixed mesh block has probability bounded by the `k`th power of
the one-step Gaussian small-ball estimate at mesh size `(n + 1)⁻¹`. -/
lemma measure_smallIncrementBlockSlice_le
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (γ : Set.Ioc (0 : ℝ≥0) 1) (k N m n i : ℕ) :
    μ (smallIncrementBlockSlice B γ k N m n i) ≤
      (ENNReal.ofReal
        (2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
          (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹)) ^ k := by
  let τ : ℕ → NNReal := fun j ↦ (m : NNReal) + ((i + j : ℕ) : NNReal) / (n + 1)
  let Y : ℕ → Ω → ℝ := fun l ω ↦ B (τ (l + 1)) ω - B (τ l) ω
  let A : Set ℝ := {x : ℝ | |x| ≤ (N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)}
  have hτmono : Monotone τ := by
    intro a b hab
    have hnum : ((i + a : ℕ) : NNReal) ≤ ((i + b : ℕ) : NNReal) := by
      exact_mod_cast Nat.add_le_add_left hab i
    have hdiv :
        ((i + a : ℕ) : NNReal) / (n + 1) ≤
          ((i + b : ℕ) : NNReal) / (n + 1) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      gcongr
    simpa [τ, add_assoc] using add_le_add_left hdiv (m : NNReal)
  have hY_indep : iIndepFun Y μ := by
    -- Proof comment: consecutive increments along the monotone mesh inherit independence from the
    -- Brownian independent-increments axiom.
    simpa [Y, τ, add_assoc, add_left_comm, add_comm] using hB.indepIncrements.nat (t := τ) hτmono
  have hA_meas : MeasurableSet A := by
    -- Proof comment: the threshold set is the preimage of the closed interval `(-∞, c]` under
    -- the measurable absolute-value map.
    change MeasurableSet {x : ℝ | |x| ≤ (N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)}
    exact measurableSet_le measurable_abs measurable_const
  have hfactor :
      μ (smallIncrementBlockSlice B γ k N m n i) =
        ∏ l ∈ Finset.range k, μ (Y l ⁻¹' A) := by
    -- Proof comment: rewrite the block event as the standard finite intersection of measurable
    -- increment-threshold preimages, then use the finite-product formula for `iIndepFun`.
    simpa [smallIncrementBlockSlice, Y, τ, A, Set.mem_setOf_eq, add_assoc, add_left_comm,
      add_comm] using
      hY_indep.measure_inter_preimage_eq_mul (Finset.range k) (fun _ _ ↦ hA_meas)
  have hstep :
      ∀ l ∈ Finset.range k,
        μ (Y l ⁻¹' A) ≤
          ENNReal.ofReal
            (2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
              (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹) := by
    intro l hl
    have hLaw := meshIncrement_hasLaw (hB := hB) m n i l
    have hRadius_nonneg : 0 ≤ (N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ) := by
      positivity
    have hv_ne :
        (((n + 1 : ℕ) : ℝ≥0)⁻¹) ≠ 0 := by
      exact inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
    -- Proof comment: every factor has the same one-step Gaussian law, so the interval-mass bound
    -- from `gaussianReal_abs_le_densityHeight` applies uniformly across the block.
    calc
      μ (Y l ⁻¹' A)
        = gaussianReal 0 (((n + 1 : ℕ) : ℝ≥0)⁻¹) A := by
            simpa [Y, τ, add_assoc, add_left_comm, add_comm] using
              (show μ
                  ((fun ω ↦
                      B ((m : NNReal) + ((i + l + 1 : ℕ) : NNReal) / (n + 1)) ω -
                        B ((m : NNReal) + ((i + l : ℕ) : NNReal) / (n + 1)) ω) ⁻¹' A) =
                    gaussianReal 0 (((n + 1 : ℕ) : ℝ≥0)⁻¹) A by
                  rw [← Measure.map_apply_of_aemeasurable hLaw.aemeasurable hA_meas, hLaw.map_eq])
      _ ≤ ENNReal.ofReal
            (2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
              (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹) := by
            simpa [A] using gaussianReal_abs_le_densityHeight hRadius_nonneg hv_ne
  calc
    μ (smallIncrementBlockSlice B γ k N m n i)
      = ∏ l ∈ Finset.range k, μ (Y l ⁻¹' A) := hfactor
    _ ≤ ∏ l ∈ Finset.range k,
          ENNReal.ofReal
            (2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
              (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹) := by
          exact Finset.prod_le_prod (fun l hl ↦ by positivity) (fun l hl ↦ hstep l hl)
    _ = (ENNReal.ofReal
          (2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
            (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹)) ^ k := by
          simp

/-- Helper for Theorem 21.17: on one unit window there are only `n + 1` possible block starts, so
the full bad event is bounded by the union bound over the slice estimate above. -/
lemma measure_smallIncrementBlockEvent_le
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (γ : Set.Ioc (0 : ℝ≥0) 1) (k N m n : ℕ) :
    μ (smallIncrementBlockEvent B γ k N m n) ≤
      (n + 1 : ENNReal) *
        (ENNReal.ofReal
          (2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
            (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹)) ^ k := by
  classical
  -- Proof comment: first bound the finite union of possible start indices by the sum of the slice
  -- probabilities, then insert the slice estimate term-by-term.
  calc
      μ (smallIncrementBlockEvent B γ k N m n)
      = μ (⋃ i ∈ Finset.range (n + 1), smallIncrementBlockSlice B γ k N m n i) := rfl
    _ ≤ ∑ i ∈ Finset.range (n + 1), μ (smallIncrementBlockSlice B γ k N m n i) := by
          exact
            measure_biUnion_finset_le (μ := μ) (Finset.range (n + 1))
              (fun i ↦ smallIncrementBlockSlice B γ k N m n i)
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          (ENNReal.ofReal
            (2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
              (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹)) ^ k := by
          gcongr with i hi
          exact measure_smallIncrementBlockSlice_le hB γ k N m n i
    _ = (n + 1 : ENNReal) *
          (ENNReal.ofReal
            (2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
              (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹)) ^ k := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          simp

/-- Helper for Theorem 21.17: the one-step Gaussian small-ball kernel on mesh `(n + 1)⁻¹`
has the power-decay normal form `(2 * N) * (n + 1)^(1 / 2 - γ)`. -/
lemma smallIncrementKernel_le_powerDecay
    (γ : Set.Ioc (0 : ℝ≥0) 1) (N n : ℕ) :
    2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
        (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹ ≤
      (2 * N : ℝ) * (n + 1 : ℝ) ^ ((1 / 2 : ℝ) - (γ : ℝ)) := by
  have hn : 0 < (n + 1 : ℝ) := by
    positivity
  have hsqrt_inv :
      (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹ ≤
        (n + 1 : ℝ) ^ (1 / 2 : ℝ) := by
    have htwoPi : (1 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hsqrt_le' :
        Real.sqrt ((n + 1 : ℝ)⁻¹) ≤ Real.sqrt (2 * Real.pi * (n + 1 : ℝ)⁻¹) := by
      have hbase_nonneg : 0 ≤ (n + 1 : ℝ)⁻¹ := by
        positivity
      refine Real.sqrt_le_sqrt ?_
      nlinarith [htwoPi, hbase_nonneg]
    have hsqrt_le :
        Real.sqrt ((n + 1 : ℝ)⁻¹) ≤
          Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)) := by
      simpa using hsqrt_le'
    have hsqrt_pos : 0 < Real.sqrt ((n + 1 : ℝ)⁻¹) := by
      apply Real.sqrt_pos.2
      positivity
    have hkernel_pos' : 0 < Real.sqrt (2 * Real.pi * (n + 1 : ℝ)⁻¹) := by
      apply Real.sqrt_pos.2
      positivity
    -- Proof comment: `2 * π ≥ 1` makes the Gaussian denominator at least `√((n + 1)⁻¹)`, so
    -- its inverse is at most `√(n + 1)`.
    have hinv' :
        (Real.sqrt (2 * Real.pi * (n + 1 : ℝ)⁻¹))⁻¹ ≤
          (Real.sqrt ((n + 1 : ℝ)⁻¹))⁻¹ := by
      exact (inv_le_inv₀ hkernel_pos' hsqrt_pos).2 hsqrt_le'
    have hinv :
        (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹ ≤
          (Real.sqrt ((n + 1 : ℝ)⁻¹))⁻¹ := by
      simpa using hinv'
    have hsqrt_inv_eq :
        (Real.sqrt ((n + 1 : ℝ)⁻¹))⁻¹ = (n + 1 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.inv_rpow hn.le, inv_inv]
    exact le_trans hinv hsqrt_inv_eq.le
  have hpow :
      ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ) * (n + 1 : ℝ) ^ (1 / 2 : ℝ) =
        (n + 1 : ℝ) ^ ((1 / 2 : ℝ) - (γ : ℝ)) := by
    rw [Real.inv_rpow hn.le]
    rw [← Real.rpow_neg hn.le]
    rw [← Real.rpow_add hn]
    congr 1
    ring
  -- Proof comment: after separating the square-root factor, the remaining exponents collect
  -- exactly to `1 / 2 - γ`.
  calc
    2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
        (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹ ≤
      2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) * ((n + 1 : ℝ) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = (2 * N : ℝ) * (n + 1 : ℝ) ^ ((1 / 2 : ℝ) - (γ : ℝ)) := by
        rw [mul_assoc, mul_assoc, hpow]
        ring

/-- Helper for Theorem 21.17: the block-event probability is bounded by a real-valued p-series
majorant with exponent `1 + k * (1 / 2 - γ)`. -/
lemma measure_smallIncrementBlockEvent_toReal_le_powerDecay
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (γ : Set.Ioc (0 : ℝ≥0) 1) (k N m n : ℕ) :
    (μ (smallIncrementBlockEvent B γ k N m n)).toReal ≤
      (2 * N : ℝ) ^ k * (n + 1 : ℝ) ^ (1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ))) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let kernel : ℝ :=
    2 * ((N : ℝ) * ((n + 1 : ℝ)⁻¹) ^ (γ : ℝ)) *
      (Real.sqrt (2 * Real.pi * (((n + 1 : ℕ) : ℝ≥0)⁻¹)))⁻¹
  have hkernel_nonneg : 0 ≤ kernel := by
    dsimp [kernel]
    positivity
  have hkernel_le :
      kernel ≤ (2 * N : ℝ) * (n + 1 : ℝ) ^ ((1 / 2 : ℝ) - (γ : ℝ)) := by
    simpa [kernel] using smallIncrementKernel_le_powerDecay γ N n
  have hkernel_pow :
      kernel ^ k ≤ ((2 * N : ℝ) * (n + 1 : ℝ) ^ ((1 / 2 : ℝ) - (γ : ℝ))) ^ k := by
    gcongr
  have hbound :
      μ (smallIncrementBlockEvent B γ k N m n) ≤
        (n + 1 : ENNReal) * (ENNReal.ofReal kernel) ^ k := by
    simpa [kernel] using measure_smallIncrementBlockEvent_le hB γ k N m n
  have hcollect :
      (n + 1 : ℝ) * (((2 * N : ℝ) * (n + 1 : ℝ) ^ ((1 / 2 : ℝ) - (γ : ℝ))) ^ k) =
        (2 * N : ℝ) ^ k * (n + 1 : ℝ) ^ (1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ))) := by
    let a : ℝ := (1 / 2 : ℝ) - (γ : ℝ)
    have hn : 0 < (n + 1 : ℝ) := by
      positivity
    have hpow_rpow :
        ((n + 1 : ℝ) ^ a) ^ k = (n + 1 : ℝ) ^ (a * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    have hfirst_factor :
        (n + 1 : ℝ) * (n + 1 : ℝ) ^ (a * k) =
          (n + 1 : ℝ) ^ (1 : ℝ) * (n + 1 : ℝ) ^ (a * k) := by
      rw [Real.rpow_one]
    have hpow_add :
        (n + 1 : ℝ) ^ (1 : ℝ) * (n + 1 : ℝ) ^ (a * k) =
          (n + 1 : ℝ) ^ (1 + a * k) := by
      rw [← Real.rpow_add hn]
    have hexp :
        1 + a * k = 1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ)) := by
      dsimp [a]
      ring
    calc
      (n + 1 : ℝ) * (((2 * N : ℝ) * (n + 1 : ℝ) ^ a) ^ k)
          = (n + 1 : ℝ) * ((2 * N : ℝ) ^ k * ((n + 1 : ℝ) ^ a) ^ k) := by
              rw [mul_pow]
      _ = (2 * N : ℝ) ^ k * ((n + 1 : ℝ) * ((n + 1 : ℝ) ^ a) ^ k) := by ring
      _ = (2 * N : ℝ) ^ k * ((n + 1 : ℝ) * (n + 1 : ℝ) ^ (a * k)) := by
            rw [hpow_rpow]
      _ = (2 * N : ℝ) ^ k * ((n + 1 : ℝ) ^ (1 : ℝ) * (n + 1 : ℝ) ^ (a * k)) := by
            exact congrArg (fun x : ℝ ↦ (2 * N : ℝ) ^ k * x) hfirst_factor
      _ = (2 * N : ℝ) ^ k * ((n + 1 : ℝ) ^ (1 + a * k)) := by
            exact congrArg (fun x : ℝ ↦ (2 * N : ℝ) ^ k * x) hpow_add
      _ = (2 * N : ℝ) ^ k * (n + 1 : ℝ) ^
            (1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ))) := by
            simp [hexp]
  -- Proof comment: after the finite `toReal` conversion, the only remaining work is to collect
  -- the power of `(n + 1)` into the p-series exponent `1 + k * (1 / 2 - γ)`.
  have htoReal :
      (μ (smallIncrementBlockEvent B γ k N m n)).toReal ≤
        (n + 1 : ℝ) * kernel ^ k := by
    have hbound_ne_top :
        (n + 1 : ENNReal) * (ENNReal.ofReal kernel) ^ k ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by simp) (by simp)
    have htmp :=
      ENNReal.toReal_mono hbound_ne_top hbound
    simpa [hkernel_nonneg] using htmp
  calc
    (μ (smallIncrementBlockEvent B γ k N m n)).toReal ≤
        (n + 1 : ℝ) * kernel ^ k := htoReal
    _ ≤ (n + 1 : ℝ) * (((2 * N : ℝ) * (n + 1 : ℝ) ^ ((1 / 2 : ℝ) - (γ : ℝ))) ^ k) := by
        exact mul_le_mul_of_nonneg_left hkernel_pow (by positivity)
    _ = (2 * N : ℝ) ^ k * (n + 1 : ℝ) ^ (1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ))) := hcollect

/-- Helper for Theorem 21.17: for every fixed window index `m` and threshold `N`, the block-event
probabilities form a summable series when `1 + k * (1 / 2 - γ) < -1`. -/
lemma tsum_smallIncrementBlockEvent_ne_top
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (γ : Set.Ioc (0 : ℝ≥0) 1) {k : ℕ}
    (hk : 1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ)) < -1) (N m : ℕ) :
    (∑' n : ℕ, μ (smallIncrementBlockEvent B γ k N m n)) ≠ ⊤ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hmajorant :
      Summable
        (fun n : ℕ ↦
          (2 * N : ℝ) ^ k * (n + 1 : ℝ) ^ (1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ)))) := by
    have hrpow :
        Summable (fun n : ℕ ↦ (n : ℝ) ^ (1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ)))) := by
      exact Real.summable_nat_rpow.mpr hk
    have hshift :
        Summable
          (fun n : ℕ ↦ (n + 1 : ℝ) ^ (1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ)))) := by
      simpa using (_root_.summable_nat_add_iff 1).2 hrpow
    exact hshift.mul_left ((2 * N : ℝ) ^ k)
  have hreal :
      Summable (fun n : ℕ ↦ (μ (smallIncrementBlockEvent B γ k N m n)).toReal) := by
    -- Proof comment: compare the event probabilities term-by-term with the p-series majorant in
    -- the previous lemma, then apply the nonnegative comparison test.
    refine Summable.of_nonneg_of_le
      (fun n ↦ ENNReal.toReal_nonneg)
      (fun n ↦ measure_smallIncrementBlockEvent_toReal_le_powerDecay hB γ k N m n)
      hmajorant
  -- Proof comment: a summable real-valued series of event probabilities lifts back to a finite
  -- ENNReal total mass because every measurable set has finite measure under a probability law.
  have hfinite :
      (∑' n : ℕ, ENNReal.ofReal (μ (smallIncrementBlockEvent B γ k N m n)).toReal) ≠ ⊤ := by
    exact hreal.tsum_ofReal_ne_top
  have htsum :
      (∑' n : ℕ, ENNReal.ofReal (μ (smallIncrementBlockEvent B γ k N m n)).toReal) =
        ∑' n : ℕ, μ (smallIncrementBlockEvent B γ k N m n) := by
    congr with n
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simpa [htsum] using hfinite

/-- Helper for Theorem 21.17: Borel--Cantelli gives almost sure eventual avoidance of every fixed
small-increment block-event family indexed by `(m, N)`. -/
lemma ae_eventually_notMem_smallIncrementBlockEvent
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (γ : Set.Ioc (0 : ℝ≥0) 1) {k : ℕ}
    (hk : 1 + (k : ℝ) * ((1 / 2 : ℝ) - (γ : ℝ)) < -1) :
    ∀ᵐ ω ∂μ, ∀ m N : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ω ∉ smallIncrementBlockEvent B γ k N m n := by
  rw [ae_all_iff]
  intro m
  rw [ae_all_iff]
  intro N
  -- Proof comment: for each fixed `(m, N)`, the summable series of event measures feeds directly
  -- into the Borel--Cantelli eventual non-membership theorem.
  simpa using
    (MeasureTheory.ae_eventually_notMem
      (μ := μ) (s := fun n : ℕ ↦ smallIncrementBlockEvent B γ k N m n)
      (tsum_smallIncrementBlockEvent_ne_top hB γ hk N m))

end IsBrownianMotion

end ProbabilityTheory

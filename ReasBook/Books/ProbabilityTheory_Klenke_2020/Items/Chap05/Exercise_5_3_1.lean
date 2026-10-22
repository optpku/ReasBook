/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_30

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable section

omit [IsProbabilityMeasure P] in
private lemma centered_average_eq_partialSum_centered
    (X : ℕ → Ω → ℝ) :
    centered_average P (fun n ↦ X (n + 1)) =
      fun n ω ↦
        partialSum (fun k ω ↦ X (k + 1) ω - P[X (k + 1)]) n ω / n := by
  funext n ω
  rw [centered_average, centered_partial_sum, partialSum]

/-- Helper for Exercise 5.3.1: the scalar series
`∑ (Real.log (n + 1))^2 / (n + 1)^2` is summable. -/
private lemma summable_logSq_inv_sq_natSucc :
    Summable (fun n : ℕ ↦ ((Real.log (n + 1)) ^ 2) * (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹)) := by
  let f : ℕ → ℝ := fun n ↦ ((Real.log (n + 1)) ^ 2) * (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹)
  let g : ℕ → ℝ := fun n ↦ (((n + 1 : ℝ) ^ (3 / 2 : ℝ))⁻¹)
  have hLittleReal :
      (fun x : ℝ ↦ (Real.log x) ^ (2 : ℝ)) =o[atTop] fun x ↦ x ^ ((2 : ℝ)⁻¹) := by
    -- Proof comment: logarithmic powers are dominated by any positive power at infinity.
    simpa using
      (isLittleO_log_rpow_rpow_atTop (r := (2 : ℝ)) (s := (2 : ℝ)⁻¹) (by positivity))
  have hShiftTendsto : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    -- Proof comment: the shifted natural cast still tends to `∞`.
    simpa using ((tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop)
  have hLittleNat :
      (fun n : ℕ ↦ (Real.log (n + 1 : ℝ)) ^ (2 : ℝ)) =o[atTop] fun n ↦
        (n + 1 : ℝ) ^ ((2 : ℝ)⁻¹) := by
    -- Proof comment: compose the real asymptotic directly with the shifted natural cast.
    simpa using hLittleReal.comp_tendsto hShiftTendsto
  have hEventually :
      ∀ᶠ n : ℕ in atTop, (Real.log (n + 1 : ℝ)) ^ (2 : ℝ) ≤ (n + 1 : ℝ) ^ ((2 : ℝ)⁻¹) := by
    filter_upwards [hLittleNat.eventuallyLE] with n hn
    have hlogBaseNonneg : 0 ≤ Real.log (n + 1 : ℝ) := by
      refine Real.log_nonneg ?_
      norm_num
    have hlogNonneg : 0 ≤ (Real.log (n + 1 : ℝ)) ^ (2 : ℝ) := by
      exact Real.rpow_nonneg hlogBaseNonneg _
    have hpowNonneg : 0 ≤ (n + 1 : ℝ) ^ ((2 : ℝ)⁻¹) := by
      exact Real.rpow_nonneg (by positivity) _
    simpa [Real.norm_eq_abs,
      abs_of_nonneg hlogNonneg, abs_of_nonneg hpowNonneg] using hn
  have hg : Summable g := by
    -- Proof comment: the comparison target is a shifted `p`-series with exponent `3 / 2`.
    simpa [g] using
      ((summable_nat_add_iff 1).2
        ((Real.summable_nat_rpow_inv).2 (by norm_num : 1 < (3 / 2 : ℝ))))
  refine Summable.of_norm_bounded_eventually_nat (g := g) hg ?_
  filter_upwards [hEventually] with n hn
  have hlog :
      (Real.log (n + 1 : ℝ)) ^ 2 ≤ (n + 1 : ℝ) ^ ((2 : ℝ)⁻¹) := by
    simpa [Real.rpow_natCast] using hn
  have hsqInvNonneg : 0 ≤ (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
    positivity
  have hf_nonneg : 0 ≤ f n := by
    dsimp [f]
    exact mul_nonneg (sq_nonneg _) hsqInvNonneg
  calc
    ‖f n‖ = f n := by
      exact abs_of_nonneg hf_nonneg
    _ ≤ (n + 1 : ℝ) ^ ((2 : ℝ)⁻¹) * (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
      dsimp [f]
      exact mul_le_mul_of_nonneg_right hlog hsqInvNonneg
    _ = g n := by
      dsimp [g]
      have hpos : 0 < (n + 1 : ℝ) := by
        positivity
      have hnonneg : 0 ≤ (n + 1 : ℝ) := hpos.le
      have hpowInv : (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) = (n + 1 : ℝ) ^ (-(2 : ℝ)) := by
        calc
          (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) = (((n + 1 : ℝ) ^ (2 : ℝ))⁻¹) := by
            simp
          _ = (n + 1 : ℝ) ^ (-(2 : ℝ)) := by
            rw [← Real.rpow_neg hnonneg]
      rw [hpowInv, ← Real.rpow_neg hnonneg, ← Real.rpow_add hpos]
      norm_num

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 5.3.1: a limsup-zero statement for `ENNReal.ofReal |Z n|` forces the real
sequence `Z n` to converge to `0`. -/
private lemma tendsto_zero_of_limsup_ennrealAbs_eq_zero
    (Z : ℕ → ℝ)
    (hZ : limsup (fun n : ℕ ↦ ENNReal.ofReal |Z n|) atTop = 0) :
    Tendsto Z atTop (𝓝 0) := by
  let u : ℕ → ENNReal := fun n ↦ ENNReal.ofReal |Z n|
  have hu_tendsto : Tendsto u atTop (𝓝 0) := by
    -- Proof comment: a nonnegative `ENNReal` sequence with limsup `0` must converge to `0`.
    refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
    · exact bot_le
    · simpa [u] using hZ.le
  have hu_toReal : Tendsto (fun n ↦ (u n).toReal) atTop (𝓝 0) := by
    -- Proof comment: the sequence never hits `∞`, so `toReal` preserves the convergence.
    refine (ENNReal.tendsto_toReal_zero_iff ?_).2 hu_tendsto
    intro n
    simp [u]
  have habs_tendsto : Tendsto (fun n ↦ |Z n|) atTop (𝓝 0) := by
    simpa [u] using hu_toReal
  exact (tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs_tendsto))

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 5.3.1: the weighted absolute partial sum from the Rademacher-Menshov
criterion is exactly the shifted centered average in the chapter notation. -/
private lemma weightedPartialSum_eq_centeredAverageShift
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (ENNReal.ofReal
        (abs (partialSum (fun k ω ↦ X (k + 1) ω - P[X (k + 1)]) (n + 1) ω))) *
      ((n + 1 : ℝ≥0∞)⁻¹) =
      ENNReal.ofReal (abs (centered_average P (fun k ↦ X (k + 1)) (n + 1) ω)) := by
  have hnPos : 0 < ((n + 1 : ℕ) : ℝ) := by
    positivity
  have havg :
      centered_average P (fun k ↦ X (k + 1)) (n + 1) ω =
        partialSum (fun k ω ↦ X (k + 1) ω - P[X (k + 1)]) (n + 1) ω /
          ((n + 1 : ℕ) : ℝ) := by
    -- Proof comment: this is the chapter's centered-average identity at the shifted index `n + 1`.
    simpa using
      congrFun (congrFun (centered_average_eq_partialSum_centered (P := P) X) (n + 1)) ω
  -- Proof comment: rewrite the ENNReal weight as the real reciprocal of `n + 1` and fold the
  -- quotient back into the centered-average normalization.
  have hInv :
      ((n + 1 : ℝ≥0∞)⁻¹) = ENNReal.ofReal ((((n + 1 : ℕ) : ℝ)⁻¹)) := by
    calc
      ((n + 1 : ℝ≥0∞)⁻¹) = (ENNReal.ofReal (((n + 1 : ℕ) : ℝ)))⁻¹ := by
        simpa using (congrArg Inv.inv (ENNReal.ofReal_natCast (n + 1))).symm
      _ = ENNReal.ofReal ((((n + 1 : ℕ) : ℝ)⁻¹)) := by
        simpa using (ENNReal.ofReal_inv_of_pos hnPos).symm
  rw [hInv, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  calc
    abs (partialSum (fun k ω ↦ X (k + 1) ω - P[X (k + 1)]) (n + 1) ω) * (((n + 1 : ℕ) : ℝ)⁻¹)
        =
          abs (partialSum (fun k ω ↦ X (k + 1) ω - P[X (k + 1)]) (n + 1) ω) *
            |(((n + 1 : ℕ) : ℝ)⁻¹)| := by
            rw [abs_of_pos (inv_pos.mpr hnPos)]
    _ = abs
          (partialSum (fun k ω ↦ X (k + 1) ω - P[X (k + 1)]) (n + 1) ω *
            (((n + 1 : ℕ) : ℝ)⁻¹)) := by
          rw [← abs_mul]
    _ = abs
          (partialSum (fun k ω ↦ X (k + 1) ω - P[X (k + 1)]) (n + 1) ω /
            ((n + 1 : ℕ) : ℝ)) := by
          rw [div_eq_mul_inv]
    _ = abs (centered_average P (fun k ↦ X (k + 1)) (n + 1) ω) := by
          rw [havg]

-- Proof sketch: combine the pairwise-independent variance estimate for centered partial sums with
-- the bounded-variance hypothesis to obtain summable tail bounds along a dyadic subsequence, apply
-- Borel--Cantelli, and then upgrade the dyadic almost sure convergence of centered averages to the
-- full strong law.
/-- Exercise 5.3.1: the textbook sequence `X₁, X₂, …`, represented by `X 1, X 2, …`, satisfies
the strong law of large numbers as soon as its terms are pairwise independent, square integrable,
and have uniformly bounded variances. -/
theorem satisfies_strong_law_of_large_numbers_of_pairwise_indep_memLp_two_bounded_variance
    (X : ℕ → Ω → ℝ) (hX_memLp : ∀ n, MemLp (X (n + 1)) 2 P)
    (hX_pairwise_indep : Pairwise fun i j ↦ X (i + 1) ⟂ᵢ[P] X (j + 1))
    (hX_var_bdd : BddAbove (Set.range fun n : ℕ ↦ Var[X (n + 1); P])) :
    satisfies_strong_law_of_large_numbers P (fun n ↦ X (n + 1)) := by
  let Y : ℕ → Ω → ℝ := fun n ω ↦ X (n + 1) ω - P[X (n + 1)]
  have hY_memLp : ∀ n, MemLp (Y n) 2 P := by
    intro n
    exact (hX_memLp n).sub (memLp_const _)
  have hY_centered : ∀ n, P[Y n] = 0 := by
    intro n
    rw [show Y n = fun ω ↦ X (n + 1) ω - P[X (n + 1)] by rfl]
    rw [integral_sub ((hX_memLp n).integrable (by simp)) (integrable_const _)]
    simp
  have hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0 := by
    intro i j hij
    have hXi_int : Integrable (X (i + 1)) P := (hX_memLp i).integrable (by simp)
    have hXj_int : Integrable (X (j + 1)) P := (hX_memLp j).integrable (by simp)
    have hcov :
        cov[X (i + 1), X (j + 1); P] = 0 :=
      (hX_pairwise_indep hij).covariance_eq_zero (hX_memLp i) (hX_memLp j)
    simpa [Y, hXi_int, hXj_int] using hcov
  have hY_var :
      ∀ n, Var[Y n; P] = Var[X (n + 1); P] := by
    intro n
    simp [Y, variance_sub_const (hX_memLp n).aestronglyMeasurable]
  let a : ℕ → NNReal := fun n ↦ n + 1
  -- Canonical route: apply `rademacher_menshov_ae_limsup_weighted_partial_sums_eq_zero` to the
  -- centered sequence `Y` with the owner normalization `a n = n + 1`, using `hY_var` together
  -- with `hX_var_bdd` to bound the logarithmically weighted variance series, then rewrite the
  -- resulting normalized partial sums back to `centered_average` via
  -- `centered_average_eq_partialSum_centered`.
  refine ⟨fun n ↦ (hX_memLp n).integrable (by simp), ?_⟩
  have ha_mono : Monotone a := by
    -- Proof comment: the normalization `a n = n + 1` is the canonical increasing choice.
    intro m n hmn
    simpa [a] using Nat.succ_le_succ hmn
  have ha_tendsto : Tendsto a atTop atTop := by
    -- Proof comment: the shifted natural sequence still tends to `∞`, and coercion to `NNReal`
    -- preserves that fact.
    rw [← NNReal.tendsto_coe_atTop]
    simpa [a] using ((tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop)
  have hseriesScalar :
      Summable (fun n : ℕ ↦ ((Real.log (n + 1)) ^ 2) * (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹)) :=
    summable_logSq_inv_sq_natSucc
  let V : ℝ := sSup (Set.range fun n : ℕ ↦ Var[X (n + 1); P])
  have hseriesBound :
      Summable (fun n : ℕ ↦ V * (((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹))) := by
    -- Proof comment: multiply the scalar summable series by the uniform variance bound `V`.
    simpa [a, mul_assoc, mul_left_comm, mul_comm] using hseriesScalar.mul_left V
  have hseries :
      Summable (fun n : ℕ ↦
        ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) * Var[Y n; P]) := by
    -- Proof comment: compare the theorem's weighted variance series with the scalar series scaled
    -- by the supremum bound on `Var[X (n + 1); P]`.
    refine Summable.of_nonneg_of_le ?_ ?_ hseriesBound
    · intro n
      have hbaseNonneg : 0 ≤ ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) := by
        positivity
      exact mul_nonneg hbaseNonneg (variance_nonneg _ _)
    · intro n
      have hvarLe : Var[X (n + 1); P] ≤ V := by
        dsimp [V]
        exact le_csSup hX_var_bdd (Set.mem_range_self n)
      have hbaseNonneg : 0 ≤ ((Real.log (n + 1)) ^ 2) * (((a n : ℝ) ^ (2 : ℕ))⁻¹) := by
        positivity
      rw [hY_var n]
      simpa [a, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hvarLe hbaseNonneg)
  have hlimsup :
      ∀ᵐ ω ∂P,
        limsup
          (fun n : ℕ ↦ (ENNReal.ofReal (abs (partialSum Y (n + 1) ω))) *
            ((a n : ℝ≥0∞)⁻¹))
          atTop = 0 := by
    have hrealTendstoAE :
        ∀ᵐ ω ∂P,
          Tendsto
            (fun n : ℕ ↦ abs (partialSum Y (n + 1) ω) / (a n : ℝ))
            atTop (𝓝 0) :=
      ae_tendsto_abs_weighted_partial_sums_zero P Y a ha_mono ha_tendsto
        hY_memLp hY_centered hY_uncorrelated hseries
    filter_upwards [hrealTendstoAE] with ω hrealTendsto
    have hennTendsto :
        Tendsto
          (fun n : ℕ ↦ ENNReal.ofReal
            (abs (partialSum Y (n + 1) ω) / (a n : ℝ)))
          atTop (𝓝 0) :=
      by simpa using ENNReal.tendsto_ofReal hrealTendsto
    calc
      limsup
          (fun n : ℕ ↦ (ENNReal.ofReal (abs (partialSum Y (n + 1) ω))) *
            ((a n : ℝ≥0∞)⁻¹))
          atTop =
          limsup
            (fun n : ℕ ↦ ENNReal.ofReal
              (abs (partialSum Y (n + 1) ω) / (a n : ℝ)))
            atTop := by
              apply limsup_congr
              filter_upwards [] with n
              rw [ENNReal.ofReal_div_of_pos]
              · have hden : ENNReal.ofReal ((n : ℝ) + 1) = (n : ℝ≥0∞) + 1 := by
                  rw [ENNReal.ofReal_add (Nat.cast_nonneg n) (by positivity)]
                  simp
                simpa [a, div_eq_mul_inv, hden]
              · positivity
      _ = 0 := hennTendsto.limsup_eq
  have hshiftTendsto :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ centered_average P (fun k ↦ X (k + 1)) (n + 1) ω) atTop (𝓝 0) := by
    filter_upwards [hlimsup] with ω hω
    have hrewrite :
        (fun n : ℕ ↦ (ENNReal.ofReal (abs (partialSum Y (n + 1) ω))) *
          ((a n : ℝ≥0∞)⁻¹)) =
          fun n ↦ ENNReal.ofReal (abs (centered_average P (fun k ↦ X (k + 1)) (n + 1) ω)) := by
      -- Proof comment: rewrite the theorem's normalized absolute partial sums into the chapter's
      -- centered-average language at the shifted index `n + 1`.
      funext n
      simpa [a, Y] using weightedPartialSum_eq_centeredAverageShift (P := P) X n ω
    have hcentered :
        limsup
          (fun n : ℕ ↦ ENNReal.ofReal (abs (centered_average P (fun k ↦ X (k + 1)) (n + 1) ω)))
          atTop = 0 := by
      simpa [hrewrite] using hω
    exact tendsto_zero_of_limsup_ennrealAbs_eq_zero
      (fun n ↦ centered_average P (fun k ↦ X (k + 1)) (n + 1) ω) hcentered
  -- Proof comment: the strong-law definition uses the unshifted sequence, so remove the fixed
  -- shift by one in the index.
  filter_upwards [hshiftTendsto] with ω hω
  exact (tendsto_add_atTop_iff_nat 1).1 hω

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_34
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_35
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Beta

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

/-- The exact block-size mass of the first occupied table in a zero-discount Chinese restaurant
process with concentration parameter `θ` and total size `n`. Equivalently, this is the
Beta-binomial law of the next occupied table after conditioning on the previous ones. -/
def zeroDiscountTableSizeMass (θ : ℝ) (n k : ℕ) : ℝ :=
  (((n - 1).choose (k - 1) : ℝ) *
      ProbabilityTheory.beta k (((n - k : ℕ) : ℝ) + θ)) /
    ProbabilityTheory.beta 1 θ

/-- A source-facing realization of the zero-discount Chinese restaurant process with concentration
parameter `θ`, exposing the table-size coordinates `N_l^n` on a probability space. The Lean table
index `l = 0` corresponds to the textbook index `1`. Besides measurability and mass constraints,
the structure stores the exact ordered block-size law of the `(0, θ)` Chinese restaurant process.
-/
structure ChineseRestaurantProcessZeroDiscount (θ : ℝ) where
  /-- The underlying sample space of the process. -/
  Ω : Type u
  /-- The measurable-space structure on the sample space. -/
  mΩ : MeasurableSpace Ω
  /-- The probability law of the Chinese restaurant process. -/
  law : ProbabilityMeasure Ω
  /-- The table-size coordinate `N_l^n`, with zero-based Lean table index `l`. -/
  tableSize : ℕ → Ω → ℕ → ℕ
  /-- The concentration parameter is positive. -/
  theta_pos : 0 < θ
  /-- Every table-size coordinate is measurable. -/
  measurable_tableSize : ∀ n l, Measurable (fun ω ↦ tableSize n ω l)
  /-- At time `n`, the table sizes sum to `n`. -/
  total_customers : ∀ n ω, (Finset.range (n + 1)).sum (fun l ↦ tableSize n ω l) = n
  /-- At time `n`, all coordinates after index `n` vanish. -/
  tail_zero : ∀ n ω l, n < l → tableSize n ω l = 0
  /-- After conditioning on a positive initial block-size profile, the next occupied table has the
  exact zero-discount Chinese-restaurant block-size law on the remaining restaurant. -/
  next_table_conditional_law :
    ∀ {n l k : ℕ} (ks : Fin l → ℕ), 0 < k → (∀ i, 0 < ks i) →
      Finset.univ.sum ks + k ≤ n →
      (law : Measure Ω)[({ω | tableSize n ω l = k} : Set Ω) |
        ({ω | ∀ i : Fin l, tableSize n ω i = ks i} : Set Ω)] =
          ENNReal.ofReal
            (zeroDiscountTableSizeMass θ (n - Finset.univ.sum ks) k)

namespace ChineseRestaurantProcessZeroDiscount

variable {θ : ℝ}

/-- The measurable-space structure on the sample space of a Chinese restaurant process. -/
instance instMeasurableSpace (crp : ChineseRestaurantProcessZeroDiscount θ) :
    MeasurableSpace crp.Ω :=
  crp.mΩ

/-- The rescaled block-size sequence `l ↦ N_l^n / n` of the Chinese restaurant process. -/
def blockProportions (crp : ChineseRestaurantProcessZeroDiscount θ) (n : ℕ) :
    crp.Ω → ℕ → ℝ :=
  fun ω l ↦ (crp.tableSize n ω l : ℝ) / n

-- Proof sketch: measurability into the countable product `ℝ^ℕ` is coordinatewise; each coordinate
-- `ω ↦ (crp.tableSize n ω l : ℝ) / n` is measurable because `crp.measurable_tableSize n l` is and
-- scalar division preserves measurability.
/-- The rescaled block-size sequence is measurable as an `ℝ^ℕ`-valued random variable. -/
theorem measurable_blockProportions (crp : ChineseRestaurantProcessZeroDiscount θ) (n : ℕ) :
    Measurable (crp.blockProportions n) := by
  -- Proof comment: measurability into the product space is checked coordinatewise.
  refine measurable_pi_lambda _ fun l ↦ ?_
  exact
    (((measurable_of_countable fun m : ℕ ↦ (m : ℝ)).comp (crp.measurable_tableSize n l)).div_const
      (n : ℝ))

end ChineseRestaurantProcessZeroDiscount

/-- The remaining mass after prescribing a finite initial block-size profile. -/
def chineseRestaurantRemainingMass {l : ℕ} (xs : Fin l → ℝ) : ℝ :=
  1 - Finset.univ.sum xs

/-- Helper for Exercise 24.3.3: the zero-discount parameter pair satisfies the standing
assumption `α < 1` for `α = 0`. -/
private theorem zeroDiscountAlphaLtOne : (0 : ℝ) < 1 := by
  norm_num

/-- Helper for Exercise 24.3.3: the zero-discount parameter pair satisfies the standing
assumption `-α < θ` for `(α, θ) = (0, 1)`. -/
private theorem zeroDiscountThetaPos : -(0 : ℝ) < (1 : ℝ) := by
  norm_num

/-- Helper for Exercise 24.3.3: the `l = 0` specialization of the stored conditional law gives
the unconditional law of the first occupied table. -/
private theorem firstTableLaw_eq_tableSizeMass {θ : ℝ}
    (crp : ChineseRestaurantProcessZeroDiscount θ) {n k : ℕ}
    (hk : 0 < k) (hk_le : k ≤ n) :
    ((crp.law : Measure crp.Ω) ({ω | crp.tableSize n ω 0 = k} : Set crp.Ω)) =
      ENNReal.ofReal (zeroDiscountTableSizeMass θ n k) := by
  -- Proof comment: for `l = 0`, the prefix event is `Set.univ`, so conditional mass reduces to
  -- ordinary mass via `ProbabilityTheory.cond_univ`.
  simpa using
    (crp.next_table_conditional_law (n := n) (l := 0) (k := k)
      (ks := fun i : Fin 0 ↦ Fin.elim0 i) hk (by intro i; exact Fin.elim0 i)
      (by simpa using hk_le))

/-- Helper for Exercise 24.3.3: at `θ = 1`, the zero-discount block-size mass is uniform over the
admissible values. -/
private theorem chineseRestaurantTableSizeMass_thetaOne {m k : ℕ}
    (hk : 0 < k) (hk_le : k ≤ m) :
    zeroDiscountTableSizeMass 1 m k = 1 / (m : ℝ) := by
  -- Proof comment: expand the beta factors into Gamma values, evaluate those Gamma values at
  -- integers, and then collapse the remaining factorial expression with the binomial identity.
  have hbeta_one_one : ProbabilityTheory.beta 1 (1 : ℝ) = 1 := by
    have hgamma_two : Real.Gamma (1 + 1 : ℝ) = 1 := by
      simpa using (Real.Gamma_nat_eq_factorial 1)
    simp [ProbabilityTheory.beta, hgamma_two]
  have hk_sub : ((k - 1 : ℕ) : ℝ) + 1 = k := by
    exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_of_lt hk))
  have hsum : (k : ℝ) + (((m - k : ℕ) : ℝ) + 1) = m + 1 := by
    have hsum_nat : k + (m - k) + 1 = m + 1 := by
      omega
    exact_mod_cast hsum_nat
  have hsub : (m - 1) - (k - 1) = m - k := by
    omega
  have hchoose_nat :
      (m - 1).choose (k - 1) * Nat.factorial (k - 1) * Nat.factorial (m - k) =
        Nat.factorial (m - 1) := by
    have hpred : k - 1 ≤ m - 1 := Nat.sub_le_sub_right hk_le 1
    simpa [hsub, Nat.mul_assoc] using Nat.choose_mul_factorial_mul_factorial hpred
  have hchoose :
      (((m - 1).choose (k - 1) : ℝ) * (Nat.factorial (k - 1) : ℝ) *
          (Nat.factorial (m - k) : ℝ)) =
        (Nat.factorial (m - 1) : ℝ) := by
    exact_mod_cast hchoose_nat
  have hm_pos : 0 < m := lt_of_lt_of_le hk hk_le
  have hgamma_k : Real.Gamma (k : ℝ) = Nat.factorial (k - 1) := by
    simpa [hk_sub] using (Real.Gamma_nat_eq_factorial (k - 1))
  have hgamma_mk : Real.Gamma (((m - k : ℕ) : ℝ) + 1) = Nat.factorial (m - k) := by
    simpa using (Real.Gamma_nat_eq_factorial (m - k))
  have hgamma_m : Real.Gamma ((m : ℝ) + 1) = Nat.factorial m := by
    simpa using (Real.Gamma_nat_eq_factorial m)
  rw [zeroDiscountTableSizeMass, hbeta_one_one, div_one, ProbabilityTheory.beta, hgamma_k,
    hgamma_mk, hsum, hgamma_m]
  rw [← mul_div_assoc, ← mul_assoc, hchoose]
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos) with ⟨r, rfl⟩
  have hfac : (Nat.factorial r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero r
  have hsucc_cast : (((r + 1 : ℕ) : ℝ)) = (r : ℝ) + 1 := by
    simp [Nat.cast_add]
  calc
    (Nat.factorial r : ℝ) / (Nat.factorial (r + 1) : ℝ) =
        (Nat.factorial r : ℝ) / (((r + 1 : ℕ) : ℝ) * (Nat.factorial r : ℝ)) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    _ = 1 / ((r : ℝ) + 1) := by
      rw [hsucc_cast]
      field_simp [hfac]
    _ = 1 / (r.succ : ℝ) := by
      simp [Nat.succ_eq_add_one, Nat.cast_add]

/-- Helper for Exercise 24.3.3: the positivity of `θ` in the process data is exactly the
admissibility condition `-0 < θ` needed for `PD_{0,θ}`. -/
private theorem zeroDiscountThetaAdmissible {θ : ℝ}
    (crp : ChineseRestaurantProcessZeroDiscount θ) : -(0 : ℝ) < θ := by
  simpa using crp.theta_pos

/-- Helper for Exercise 24.3.3: the zero-discount table-size mass is the `α = 0`
specialization of `chineseRestaurantTableSizeMass`. -/
private theorem zeroDiscountTableSizeMass_eq_chineseRestaurantTableSizeMass_zero
    {θ : ℝ} (l n k : ℕ) :
    zeroDiscountTableSizeMass θ n k = chineseRestaurantTableSizeMass 0 θ l n k := by
  -- Proof comment: setting `α = 0` removes every `l`-dependent correction term in the general
  -- Chinese-restaurant mass formula.
  simp [zeroDiscountTableSizeMass, chineseRestaurantTableSizeMass]

/-- Helper for Exercise 24.3.3: a zero-discount Chinese restaurant process already satisfies the
general Chapter 24 Chinese-restaurant process law with parameter `α = 0`. -/
private theorem zeroDiscountIsChineseRestaurantProcessLaw {θ : ℝ}
    (crp : ChineseRestaurantProcessZeroDiscount θ) :
    IsChineseRestaurantProcessLaw 0 θ crp.law crp.tableSize := by
  refine
    ⟨crp.measurable_tableSize, crp.total_customers, crp.tail_zero, ?_⟩
  intro n l k ks hk hks_pos hsum_le
  -- Proof comment: the stored zero-discount transition law already has the right shape; only the
  -- mass formula must be rewritten to the `α = 0` owner API.
  rw [← zeroDiscountTableSizeMass_eq_chineseRestaurantTableSizeMass_zero (θ := θ) (l := l)]
  exact crp.next_table_conditional_law ks hk hks_pos hsum_le

/-- Helper for Exercise 24.3.3: package a zero-discount Chinese restaurant process as a general
Chinese restaurant process with `α = 0`. -/
private def zeroDiscountToChineseRestaurantProcess {θ : ℝ}
    (crp : ChineseRestaurantProcessZeroDiscount θ) :
    ChineseRestaurantProcess 0 θ le_rfl zeroDiscountAlphaLtOne
      (zeroDiscountThetaAdmissible crp) :=
  { Ω := crp.Ω
    mΩ := crp.mΩ
    law := crp.law
    tableSize := crp.tableSize
    isChineseRestaurantProcess := zeroDiscountIsChineseRestaurantProcessLaw crp }

/-- Helper for Exercise 24.3.3: the normalized ranked law of the packaged `α = 0` process at time
`n` is exactly the local ranked block-proportion law at time `n + 1`. -/
private theorem normalizedChineseRestaurantProcessLaw_eq_zeroDiscountRankedLaw_succ {θ : ℝ}
    (crp : ChineseRestaurantProcessZeroDiscount θ) (n : ℕ) :
    normalizedChineseRestaurantProcessLaw (zeroDiscountToChineseRestaurantProcess crp) n =
      crp.law.map
        ((measurable_rankedRearrangement.comp
          (crp.measurable_blockProportions (n + 1))).aemeasurable) := by
  -- Proof comment: after unpacking the adapter, both sides are the same pushforward of `crp.law`
  -- along the ranked normalized block-proportion map at restaurant size `n + 1`.
  have hBlockProportions :
      ProbabilityTheory.blockProportions (zeroDiscountToChineseRestaurantProcess crp) n =
        crp.blockProportions (n + 1) := by
    -- Proof comment: both `blockProportions` APIs evaluate the same normalized table-size
    -- coordinates once the packaged process is unfolded.
    ext ω l
    simp [ProbabilityTheory.blockProportions, ChineseRestaurantProcessZeroDiscount.blockProportions,
      zeroDiscountToChineseRestaurantProcess]
  apply ProbabilityMeasure.toMeasure_injective
  rw [normalizedChineseRestaurantProcessLaw]
  simp only [ProbabilityMeasure.toMeasure_map]
  congr 1
  funext ω
  simp [Function.comp, hBlockProportions]

/-- Helper for Exercise 24.3.3: the zero-discount block-size mass rewrites into a Gamma-ratio
normal form that isolates the remaining customer count `m - k`. -/
private theorem zeroDiscountTableSizeMass_eq_theta_mul_gammaRatio
    {θ : ℝ} {m k : ℕ} (hθ : 0 < θ) (hk : 0 < k) (hk_le : k ≤ m) :
    zeroDiscountTableSizeMass θ m k =
      θ * Real.Gamma (m : ℝ) * Real.Gamma (((m - k : ℕ) : ℝ) + θ) /
        (Real.Gamma (((m - k : ℕ) : ℝ) + 1) * Real.Gamma ((m : ℝ) + θ)) := by
  -- Proof comment: expand the Beta factors into Gamma factors, evaluate the integer Gamma terms,
  -- and then collapse the remaining binomial coefficient against the factorials.
  have hbeta_one : ProbabilityTheory.beta 1 θ = 1 / θ := by
    have hGammaθ_ne : Real.Gamma θ ≠ 0 := (Real.Gamma_pos_of_pos hθ).ne'
    have hGamma_one : Real.Gamma (1 : ℝ) = 1 := by
      norm_num [Real.Gamma_nat_eq_factorial]
    have hGamma_theta_succ : Real.Gamma (1 + θ) = θ * Real.Gamma θ := by
      simpa [add_comm] using (Real.Gamma_add_one (ne_of_gt hθ) : Real.Gamma (θ + 1) = _)
    rw [ProbabilityTheory.beta, hGamma_one, hGamma_theta_succ]
    field_simp [hGammaθ_ne]
  have hk_sub : (((k - 1 : ℕ) : ℝ) + 1) = k := by
    exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_of_lt hk))
  have hm_pos : 0 < m := lt_of_lt_of_le hk hk_le
  have hm_sub : (((m - 1 : ℕ) : ℝ) + 1) = m := by
    exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos))
  have hsum : (k : ℝ) + (((m - k : ℕ) : ℝ) + θ) = (m : ℝ) + θ := by
    calc
      (k : ℝ) + (((m - k : ℕ) : ℝ) + θ)
          = ((k + (m - k) : ℕ) : ℝ) + θ := by
              norm_num [Nat.cast_add, add_assoc]
      _ = (m : ℝ) + θ := by
            rw [Nat.add_sub_of_le hk_le]
  have hsub : (m - 1) - (k - 1) = m - k := by
    omega
  have hchoose_nat :
      (m - 1).choose (k - 1) * Nat.factorial (k - 1) * Nat.factorial (m - k) =
        Nat.factorial (m - 1) := by
    have hpred : k - 1 ≤ m - 1 := Nat.sub_le_sub_right hk_le 1
    simpa [hsub, Nat.mul_assoc] using Nat.choose_mul_factorial_mul_factorial hpred
  have hfactorial_ne : (Nat.factorial (m - k) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (m - k))
  have hchoose :
      (((m - 1).choose (k - 1) : ℝ) * (Nat.factorial (k - 1) : ℝ)) =
        (Nat.factorial (m - 1) : ℝ) / (Nat.factorial (m - k) : ℝ) := by
    apply (eq_div_iff hfactorial_ne).2
    exact_mod_cast hchoose_nat
  have hGamma_k : Real.Gamma (k : ℝ) = Nat.factorial (k - 1) := by
    simpa [hk_sub] using (Real.Gamma_nat_eq_factorial (k - 1))
  have hGamma_m : Real.Gamma (m : ℝ) = Nat.factorial (m - 1) := by
    simpa [hm_sub] using (Real.Gamma_nat_eq_factorial (m - 1))
  have hGamma_res :
      Real.Gamma (((m - k : ℕ) : ℝ) + 1) = Nat.factorial (m - k) := by
    simpa using (Real.Gamma_nat_eq_factorial (m - k))
  have hGamma_mθ_ne : Real.Gamma ((m : ℝ) + θ) ≠ 0 := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.zero_le m)
    exact (Real.Gamma_pos_of_pos (lt_of_lt_of_le hθ (by nlinarith))).ne'
  have hGamma_res_ne : Real.Gamma (((m - k : ℕ) : ℝ) + 1) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity)).ne'
  calc
    zeroDiscountTableSizeMass θ m k
        = (((m - 1).choose (k - 1) : ℝ) *
            (Real.Gamma (k : ℝ) * Real.Gamma (((m - k : ℕ) : ℝ) + θ) /
              Real.Gamma ((m : ℝ) + θ))) /
            (1 / θ) := by
              rw [zeroDiscountTableSizeMass, ProbabilityTheory.beta, hsum, hbeta_one]
    _ = θ * ((((m - 1).choose (k - 1) : ℝ) * Real.Gamma (k : ℝ)) *
          Real.Gamma (((m - k : ℕ) : ℝ) + θ) / Real.Gamma ((m : ℝ) + θ)) := by
            field_simp [hθ.ne', mul_assoc, mul_left_comm, mul_comm]
    _ = θ * (((Nat.factorial (m - 1) : ℝ) / (Nat.factorial (m - k) : ℝ)) *
          Real.Gamma (((m - k : ℕ) : ℝ) + θ) / Real.Gamma ((m : ℝ) + θ)) := by
            rw [hGamma_k, hchoose]
    _ = θ * Real.Gamma (m : ℝ) * Real.Gamma (((m - k : ℕ) : ℝ) + θ) /
          (Real.Gamma (((m - k : ℕ) : ℝ) + 1) * Real.Gamma ((m : ℝ) + θ)) := by
            rw [hGamma_m, hGamma_res]
            field_simp [hGamma_res_ne, hGamma_mθ_ne]

/-- Helper for Exercise 24.3.3: after multiplying by `m`, the zero-discount block-size mass splits
into one Gamma ratio for the total restaurant size and one for the remaining size `m - k`. -/
private theorem scaledZeroDiscountTableSizeMass_eq_gammaRatio
    {θ : ℝ} {m k : ℕ} (hθ : 0 < θ) (hk : 0 < k) (hk_le : k ≤ m) :
    (m : ℝ) * zeroDiscountTableSizeMass θ m k =
      θ * (Real.Gamma ((m : ℝ) + 1) / Real.Gamma ((m : ℝ) + θ)) *
        (Real.Gamma (((m - k : ℕ) : ℝ) + θ) / Real.Gamma (((m - k : ℕ) : ℝ) + 1)) := by
  -- Proof comment: multiply the previous exact mass formula by `m` and absorb that factor into
  -- `Gamma (m + 1)` using the Gamma recurrence.
  have hm_pos : 0 < m := lt_of_lt_of_le hk hk_le
  have hm_ne : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm_pos)
  have hGamma_mθ_ne : Real.Gamma ((m : ℝ) + θ) ≠ 0 := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by
      exact_mod_cast (Nat.zero_le m)
    exact (Real.Gamma_pos_of_pos (lt_of_lt_of_le hθ (by nlinarith))).ne'
  have hGamma_res_ne : Real.Gamma (((m - k : ℕ) : ℝ) + 1) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [zeroDiscountTableSizeMass_eq_theta_mul_gammaRatio hθ hk hk_le]
  rw [Real.Gamma_add_one hm_ne]
  field_simp [hGamma_mθ_ne, hGamma_res_ne]

/-- Helper for Exercise 24.3.3: once the remaining customer count `m - k` is positive, the
scaled zero-discount mass factors into the two convergent Gamma terms and the residual proportion
power `((m - k) / m)^(θ - 1)`. -/
private theorem scaledZeroDiscountTableSizeMass_eq_gammaLimitFactors
    {θ : ℝ} {m k : ℕ} (hθ : 0 < θ) (hk : 0 < k) (hk_lt : k < m) :
    (m : ℝ) * zeroDiscountTableSizeMass θ m k =
      θ *
        (((m : ℝ) ^ (θ - 1)) * (Real.Gamma ((m : ℝ) + 1) / Real.Gamma ((m : ℝ) + θ))) *
        ((((m - k : ℕ) : ℝ) ^ (1 - θ)) *
          (Real.Gamma (((m - k : ℕ) : ℝ) + θ) / Real.Gamma (((m - k : ℕ) : ℝ) + 1))) *
        ((((m - k : ℕ) : ℝ) / m) ^ (θ - 1)) := by
  -- Proof comment: insert the compensating powers of `m` and `m - k`, and then collapse those
  -- powers back to `1` using `rpow_add` on the positive residual size.
  let a : ℝ := Real.Gamma ((m : ℝ) + 1) / Real.Gamma ((m : ℝ) + θ)
  let b : ℝ := Real.Gamma (((m - k : ℕ) : ℝ) + θ) / Real.Gamma (((m - k : ℕ) : ℝ) + 1)
  let u : ℝ := (m : ℝ) ^ (θ - 1)
  let v : ℝ := (((m - k : ℕ) : ℝ) ^ (1 - θ))
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (lt_trans hk hk_lt)
  have hr_pos : 0 < (((m - k : ℕ) : ℝ)) := by
    exact_mod_cast (tsub_pos_of_lt hk_lt)
  have hu_ne : u ≠ 0 := by
    exact (Real.rpow_pos_of_pos hm_pos _).ne'
  have hRatioPow :
      ((((m - k : ℕ) : ℝ) / m) ^ (θ - 1)) =
        (((m - k : ℕ) : ℝ) ^ (θ - 1)) / u := by
    simp [u, Real.div_rpow (show 0 ≤ (((m - k : ℕ) : ℝ)) by positivity)
      (show 0 ≤ (m : ℝ) by positivity)]
  have hResidualPow :
      v * (((m - k : ℕ) : ℝ) ^ (-1 + θ)) = 1 := by
    dsimp [v]
    rw [show (-1 + θ : ℝ) = θ - 1 by ring]
    rw [show (1 - θ : ℝ) = -(θ - 1) by ring, Real.rpow_neg hr_pos.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hr_pos _)]
  calc
    (m : ℝ) * zeroDiscountTableSizeMass θ m k = θ * a * b := by
      simp [a, b, scaledZeroDiscountTableSizeMass_eq_gammaRatio hθ hk hk_lt.le]
    _ = θ * (u * a) * (v * b) * ((((m - k : ℕ) : ℝ) / m) ^ (θ - 1)) := by
      rw [hRatioPow]
      field_simp [hu_ne]
      calc
        a * b = a * b * 1 := by ring
        _ = a * b * (v * (((m - k : ℕ) : ℝ) ^ (-1 + θ))) := by rw [hResidualPow]
        _ = a * b * v * (((m - k : ℕ) : ℝ) ^ (-1 + θ)) := by ring
        _ = a * b * v * (((m - k : ℕ) : ℝ) ^ (θ - 1)) := by
              rw [show (-1 + θ : ℝ) = θ - 1 by ring]

/-- Helper for Exercise 24.3.3: the rounded-down number of customers prescribed by a finite
initial block-proportion profile at time `n`. -/
private def roundedPrefixCustomerCount {l : ℕ} (xs : Fin l → ℝ) (n : ℕ) : ℕ :=
  Finset.univ.sum (fun i ↦ ⌊(n : ℝ) * xs i⌋₊)

/-- Helper for Exercise 24.3.3: the number of customers remaining after removing the rounded-down
initial block counts from a restaurant of size `n`. -/
private def roundedRemainingCustomerCount {l : ℕ} (xs : Fin l → ℝ) (n : ℕ) : ℕ :=
  n - roundedPrefixCustomerCount xs n

/-- Helper for Exercise 24.3.3: the normalized rounded prefix count converges to the prescribed
prefix mass `∑ xs`. -/
private theorem roundedPrefixCustomerCountRatio_tendsto {l : ℕ} (xs : Fin l → ℝ)
    (hxs_nonneg : ∀ i, 0 ≤ xs i) :
    Tendsto
      (fun n : ℕ ↦ (((roundedPrefixCustomerCount xs n : ℕ) : ℝ) / n))
      atTop
      (𝓝 (Finset.univ.sum xs)) := by
  -- Proof comment: sum the coordinatewise floor-ratio limits over the finite index set.
  have hsum :
      Tendsto
        (fun n : ℕ ↦ Finset.univ.sum (fun i ↦ (⌊(n : ℝ) * xs i⌋₊ : ℝ) / n))
        atTop
        (𝓝 (Finset.univ.sum xs)) := by
    refine tendsto_finset_sum Finset.univ fun i _ ↦ ?_
    have hi :
        Tendsto
          (((fun x : ℝ ↦ (⌊xs i * x⌋₊ : ℝ) / x)) ∘ Nat.cast)
          atTop
          (𝓝 (xs i)) :=
      ((tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := xs i) (hxs_nonneg i)).comp
        tendsto_natCast_atTop_atTop)
    convert hi using 1
    ext n
    simp [Function.comp, mul_comm]
  simpa [roundedPrefixCustomerCount, Nat.cast_sum, Finset.sum_div] using hsum

/-- Helper for Exercise 24.3.3: if the prescribed initial proportions sum to at most `1`, then the
rounded prefix counts never exceed the total restaurant size. -/
private theorem roundedPrefixCustomerCount_le {l : ℕ} (xs : Fin l → ℝ)
    (hxs_nonneg : ∀ i, 0 ≤ xs i) (hxs_sum_le : Finset.univ.sum xs ≤ 1) (n : ℕ) :
    roundedPrefixCustomerCount xs n ≤ n := by
  -- Proof comment: each floor is bounded above by the corresponding real mass, and the total
  -- prescribed mass is at most `1`.
  have hprefix_le_real : ((roundedPrefixCustomerCount xs n : ℕ) : ℝ) ≤ n := by
    calc
      ((roundedPrefixCustomerCount xs n : ℕ) : ℝ)
          = Finset.univ.sum (fun i ↦ ((⌊(n : ℝ) * xs i⌋₊ : ℕ) : ℝ)) := by
              simp [roundedPrefixCustomerCount, Nat.cast_sum]
      _ ≤ Finset.univ.sum (fun i ↦ (n : ℝ) * xs i) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact_mod_cast
              (Nat.floor_le (mul_nonneg (show 0 ≤ (n : ℝ) by positivity) (hxs_nonneg i)))
      _ = (n : ℝ) * Finset.univ.sum xs := by rw [Finset.mul_sum]
      _ ≤ (n : ℝ) * 1 := by
            gcongr
      _ = n := by ring
  exact_mod_cast hprefix_le_real

/-- Helper for Exercise 24.3.3: if the prescribed initial block proportions sum to at most `1`,
then the remaining restaurant size normalized by `n` converges to the remaining mass
`1 - ∑ xs`. -/
private theorem remainingFloorRatio_tendsto {l : ℕ} (xs : Fin l → ℝ)
    (hxs_nonneg : ∀ i, 0 ≤ xs i) (hxs_sum_le : Finset.univ.sum xs ≤ 1) :
    Tendsto
      (fun n : ℕ ↦
        (((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n))
      atTop
      (𝓝 (chineseRestaurantRemainingMass xs)) := by
  -- Proof comment: the floor ratios converge coordinatewise to `xs i`, so the residual ratio is
  -- the complement of their finite sum once we note that the summed floors never exceed `n`.
  have hfloorSum := roundedPrefixCustomerCountRatio_tendsto xs hxs_nonneg
  have hEventually :
      (fun n : ℕ ↦ (((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n)) =ᶠ[atTop]
        fun n : ℕ ↦ 1 - (((roundedPrefixCustomerCount xs n : ℕ) : ℝ) / n) := by
    refine Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    have hprefix_le : roundedPrefixCustomerCount xs n ≤ n :=
      roundedPrefixCustomerCount_le xs hxs_nonneg hxs_sum_le n
    calc
      (((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n)
          = (((n - roundedPrefixCustomerCount xs n : ℕ) : ℝ) / n) := by
              rfl
      _ = 1 - (((roundedPrefixCustomerCount xs n : ℕ) : ℝ) / n) := by
            rw [Nat.cast_sub hprefix_le, sub_div, div_self hn_ne]
  have hComplement :
      Tendsto (fun n : ℕ ↦ 1 - (((roundedPrefixCustomerCount xs n : ℕ) : ℝ) / n)) atTop
        (𝓝 (1 - Finset.univ.sum xs)) := by
    exact tendsto_const_nhds.sub hfloorSum
  have hResidual :
      Tendsto (fun n : ℕ ↦ (((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n)) atTop
        (𝓝 (chineseRestaurantRemainingMass xs)) := by
    have hTendsto :
        Tendsto (fun n : ℕ ↦ (((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n)) atTop
          (𝓝 (1 - Finset.univ.sum xs)) := by
      exact hComplement.congr' hEventually.symm
    simpa [chineseRestaurantRemainingMass] using hTendsto
  exact hResidual

/-- Helper for Exercise 24.3.3: multiplying `Γ(θ)` by the first `n + 1` shifted factors recovers
the Gamma value at `θ + n + 1`. -/
private theorem gammaMulProdRange_eq_gammaAdd {θ : ℝ} (hθ : 0 < θ) :
    ∀ n : ℕ,
      Real.Gamma θ * ∏ j ∈ Finset.range (n + 1), (θ + j) =
        Real.Gamma (θ + n + 1)
  | 0 => by
      -- Proof comment: the first product contains only the factor `θ`, so this is exactly the
      -- Gamma recurrence at `θ`.
      simpa [mul_comm] using (Real.Gamma_add_one (ne_of_gt hθ)).symm
  | n + 1 => by
      -- Proof comment: append the next shifted factor to the range product and then apply the
      -- Gamma recurrence at `θ + n + 1`.
      have hPrev := gammaMulProdRange_eq_gammaAdd hθ n
      have harg_ne : θ + n + 1 ≠ 0 := by positivity
      have hStep :
          Real.Gamma (θ + ↑(n + 1) + 1) =
            (θ + ↑(n + 1)) * Real.Gamma (θ + ↑(n + 1)) := by
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
          (Real.Gamma_add_one harg_ne)
      rw [Finset.prod_range_succ, ← mul_assoc, hPrev]
      simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        using hStep.symm

/-- Helper for Exercise 24.3.3: `Real.GammaSeq` matches the Gamma-ratio normal form naturally
adapted to the zero-discount block-size mass. -/
private theorem gammaSeq_eq_gammaRatio {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    Real.GammaSeq θ n =
      ((n : ℝ) ^ θ) * Real.Gamma θ * Real.Gamma ((n : ℝ) + 1) /
        Real.Gamma (θ + n + 1) := by
  -- Proof comment: rewrite the finite product in `GammaSeq` as `Γ(θ + n + 1) / Γ(θ)` and then
  -- clear the common `Γ(θ)` factor.
  have hProd := gammaMulProdRange_eq_gammaAdd hθ n
  have hGammaθ_ne : Real.Gamma θ ≠ 0 := (Real.Gamma_pos_of_pos hθ).ne'
  have hGammaNat : (n.factorial : ℝ) = Real.Gamma ((n : ℝ) + 1) := by
    simpa using (Real.Gamma_nat_eq_factorial n).symm
  rw [Real.GammaSeq]
  rw [hGammaNat]
  calc
    (n : ℝ) ^ θ * Real.Gamma ((n : ℝ) + 1) / ∏ j ∈ Finset.range (n + 1), (θ + j)
        = ((n : ℝ) ^ θ * Real.Gamma ((n : ℝ) + 1) * Real.Gamma θ) /
            (Real.Gamma θ * ∏ j ∈ Finset.range (n + 1), (θ + j)) := by
              field_simp [hGammaθ_ne]
    _ = ((n : ℝ) ^ θ) * Real.Gamma θ * Real.Gamma ((n : ℝ) + 1) /
          Real.Gamma (θ + n + 1) := by
            rw [hProd]
            ring

/-- Helper for Exercise 24.3.3: the total-size Gamma factor in the exact zero-discount mass
formula converges to `1`. -/
private theorem gammaSuccDivGammaAdd_mulPow_tendsto_one {θ : ℝ} (hθ : 0 < θ) :
    Tendsto
      (fun n : ℕ ↦
        ((n : ℝ) ^ (θ - 1)) * (Real.Gamma ((n : ℝ) + 1) / Real.Gamma ((n : ℝ) + θ)))
      atTop
      (𝓝 1) := by
  -- Proof comment: rewrite the Gamma ratio through `Real.GammaSeq θ n`, whose limit is exactly
  -- `Γ(θ)`, and separate the harmless prefactor `1 + θ / n`.
  have hGammaθ_ne : Real.Gamma θ ≠ 0 := (Real.Gamma_pos_of_pos hθ).ne'
  have hGammaSeq :
      Tendsto (fun n : ℕ ↦ Real.GammaSeq θ n / Real.Gamma θ) atTop (𝓝 1) := by
    simpa [hGammaθ_ne] using (Real.GammaSeq_tendsto_Gamma θ).div_const (Real.Gamma θ)
  have hInv :
      Tendsto (fun n : ℕ ↦ ((n : ℝ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hPrefactor : Tendsto (fun n : ℕ ↦ 1 + θ / n) atTop (𝓝 1) := by
    -- Proof comment: `θ / n` vanishes because `n⁻¹ → 0`.
    simpa [div_eq_mul_inv, one_mul] using
      (tendsto_const_nhds.add
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ θ) atTop (𝓝 θ)).mul hInv))
  have hEventually :
      (fun n : ℕ ↦
        ((n : ℝ) ^ (θ - 1)) * (Real.Gamma ((n : ℝ) + 1) / Real.Gamma ((n : ℝ) + θ))) =ᶠ[atTop]
        fun n : ℕ ↦ (Real.GammaSeq θ n / Real.Gamma θ) * (1 + θ / n) := by
    refine Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hGammaSeqRatio := gammaSeq_eq_gammaRatio hθ n
    have harg_ne : θ + n ≠ 0 := by positivity
    have hPow :
        (n : ℝ) ^ θ = (n : ℝ) ^ (θ - 1) * (n : ℝ) := by
      rw [show θ = (θ - 1) + 1 by ring, Real.rpow_add (show 0 < (n : ℝ) by exact_mod_cast hn)]
      simp
    change ((n : ℝ) ^ (θ - 1)) * (Real.Gamma ((n : ℝ) + 1) / Real.Gamma ((n : ℝ) + θ)) =
      (Real.GammaSeq θ n / Real.Gamma θ) * (1 + θ / n)
    rw [hGammaSeqRatio, Real.Gamma_add_one harg_ne]
    rw [hPow]
    field_simp [hGammaθ_ne, hn_ne]
    ring_nf
  have hProduct :
      Tendsto (fun n : ℕ ↦ (Real.GammaSeq θ n / Real.Gamma θ) * (1 + θ / n)) atTop (𝓝 1) := by
    simpa using hGammaSeq.mul hPrefactor
  exact hProduct.congr' hEventually.symm

/-- Helper for Exercise 24.3.3: the residual-size Gamma factor in the exact zero-discount mass
formula also converges to `1`. -/
private theorem powOneSubThetaMulGammaAddDivGammaSucc_tendsto_one {θ : ℝ} (hθ : 0 < θ) :
    Tendsto
      (fun r : ℕ ↦
        ((r : ℝ) ^ (1 - θ)) * (Real.Gamma ((r : ℝ) + θ) / Real.Gamma ((r : ℝ) + 1)))
      atTop
      (𝓝 1) := by
  -- Proof comment: for positive `r`, this factor is the reciprocal of the previous Gamma ratio,
  -- so the limit follows by inversion at the nonzero target `1`.
  have hMain := gammaSuccDivGammaAdd_mulPow_tendsto_one hθ
  have hEventually :
      (fun r : ℕ ↦
        ((r : ℝ) ^ (1 - θ)) * (Real.Gamma ((r : ℝ) + θ) / Real.Gamma ((r : ℝ) + 1))) =ᶠ[atTop]
        fun r : ℕ ↦
          (((r : ℝ) ^ (θ - 1)) *
            (Real.Gamma ((r : ℝ) + 1) / Real.Gamma ((r : ℝ) + θ)))⁻¹ := by
    refine Filter.eventually_atTop.2 ⟨1, fun r hr ↦ ?_⟩
    have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
    have hrpow_ne : (r : ℝ) ^ (θ - 1) ≠ 0 :=
      (Real.rpow_pos_of_pos hr_pos _).ne'
    have hGamma_rθ_ne : Real.Gamma ((r : ℝ) + θ) ≠ 0 := by
      exact (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hGamma_r1_ne : Real.Gamma ((r : ℝ) + 1) ≠ 0 := by
      exact (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hrpow :
        (r : ℝ) ^ (1 - θ) = (((r : ℝ) ^ (θ - 1))⁻¹) := by
      rw [show 1 - θ = -(θ - 1) by ring, Real.rpow_neg hr_pos.le]
    change ((r : ℝ) ^ (1 - θ)) * (Real.Gamma ((r : ℝ) + θ) / Real.Gamma ((r : ℝ) + 1)) =
      (((r : ℝ) ^ (θ - 1)) * (Real.Gamma ((r : ℝ) + 1) / Real.Gamma ((r : ℝ) + θ)))⁻¹
    rw [hrpow]
    symm
    refine inv_eq_of_mul_eq_one_left ?_
    field_simp [hrpow_ne, hGamma_rθ_ne, hGamma_r1_ne]
  have hInv :
      Tendsto
        (fun r : ℕ ↦
          (((r : ℝ) ^ (θ - 1)) * (Real.Gamma ((r : ℝ) + 1) / Real.Gamma ((r : ℝ) + θ)))⁻¹)
        atTop
        (𝓝 1) := by
    simpa using (Tendsto.inv₀ hMain one_ne_zero)
  exact hInv.congr' hEventually.symm

/-- Helper for Exercise 24.3.3: after removing one further rounded block of mass `x`, the
residual customer count normalized by `n` converges to the residual mass
`chineseRestaurantRemainingMass xs - x`. -/
private theorem remainingAfterNextFloorRatio_tendsto {l : ℕ} (xs : Fin l → ℝ) {x : ℝ}
    (hxs_nonneg : ∀ i, 0 ≤ xs i) (hxs_sum_x_le : Finset.univ.sum xs + x ≤ 1) (hx_nonneg : 0 ≤ x) :
    Tendsto
      (fun n : ℕ ↦
        ((((roundedRemainingCustomerCount xs n - ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n)))
      atTop
      (𝓝 (chineseRestaurantRemainingMass xs - x)) := by
  have hxs_sum_le : Finset.univ.sum xs ≤ 1 := by nlinarith
  have hRemaining := remainingFloorRatio_tendsto xs hxs_nonneg hxs_sum_le
  have hFloor :
      Tendsto
        (fun n : ℕ ↦ (((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n))
        atTop
        (𝓝 x) := by
    have hFloor' :
        Tendsto
          (((fun t : ℝ ↦ (⌊x * t⌋₊ : ℝ) / t)) ∘ Nat.cast)
          atTop
          (𝓝 x) :=
      ((tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := x) hx_nonneg)).comp
        tendsto_natCast_atTop_atTop
    convert hFloor' using 1
    ext n
    simp [Function.comp, mul_comm]
  have hEventually :
      (fun n : ℕ ↦
        ((((roundedRemainingCustomerCount xs n - ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n))) =ᶠ[atTop]
        fun n : ℕ ↦
          (((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n) -
            (((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n) := by
    refine Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hPrefixLe :
        ((roundedPrefixCustomerCount xs n : ℕ) : ℝ) ≤ (n : ℝ) * Finset.univ.sum xs := by
      -- Proof comment: every rounded block count is bounded by its corresponding prescribed mass.
      calc
        ((roundedPrefixCustomerCount xs n : ℕ) : ℝ)
            = Finset.univ.sum (fun i ↦ ((⌊(n : ℝ) * xs i⌋₊ : ℕ) : ℝ)) := by
                simp [roundedPrefixCustomerCount, Nat.cast_sum]
        _ ≤ Finset.univ.sum (fun i ↦ (n : ℝ) * xs i) := by
              refine Finset.sum_le_sum fun i _ ↦ ?_
              exact_mod_cast
                (Nat.floor_le (mul_nonneg (show 0 ≤ (n : ℝ) by positivity) (hxs_nonneg i)))
        _ = (n : ℝ) * Finset.univ.sum xs := by rw [Finset.mul_sum]
    have hFloorAddPrefix :
        ⌊(n : ℝ) * x⌋₊ + roundedPrefixCustomerCount xs n ≤ n := by
      have hFloorLe :
          ((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * x := by
        exact_mod_cast
          (Nat.floor_le (mul_nonneg (show 0 ≤ (n : ℝ) by positivity) hx_nonneg))
      have hReal :
          (((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) + ((roundedPrefixCustomerCount xs n : ℕ) : ℝ)) ≤ n := by
        have : (n : ℝ) * x + (n : ℝ) * Finset.univ.sum xs ≤ n := by
          nlinarith
        linarith
      exact_mod_cast hReal
    have hFloorLeRemaining :
        ⌊(n : ℝ) * x⌋₊ ≤ roundedRemainingCustomerCount xs n := by
      have hPrefixLeNat :
          roundedPrefixCustomerCount xs n ≤ n :=
        roundedPrefixCustomerCount_le xs hxs_nonneg hxs_sum_le n
      rw [roundedRemainingCustomerCount]
      exact (Nat.le_sub_iff_add_le hPrefixLeNat).2 hFloorAddPrefix
    simp [Nat.cast_sub hFloorLeRemaining, sub_div]
  have hDiff :
      Tendsto
        (fun n : ℕ ↦
          (((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n) -
            (((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n))
        atTop
        (𝓝 (chineseRestaurantRemainingMass xs - x)) := by
    exact hRemaining.sub hFloor
  exact hDiff.congr' hEventually.symm

/-- Helper for Exercise 24.3.3: a natural-valued sequence whose normalization by `n` converges to
a strictly positive limit must itself diverge to `+∞`. -/
private theorem natSequence_tendsto_atTop_of_div_tendsto_positive
    {f : ℕ → ℕ} {c : ℝ}
    (hfc : Tendsto (fun n : ℕ ↦ ((f n : ℕ) : ℝ) / n) atTop (𝓝 c)) (hc : 0 < c) :
    Tendsto f atTop atTop := by
  -- Proof comment: an eventually positive fraction of `n` is bounded below by a fixed multiple of
  -- `n`, and that lower bound already tends to `+∞`.
  have hc_half : 0 < c / 2 := by linarith
  have hc_half_lt : c / 2 < c := by linarith
  have hEventuallyRatio :
      ∀ᶠ n : ℕ in atTop, c / 2 < ((f n : ℕ) : ℝ) / n := by
    exact hfc (Ioi_mem_nhds hc_half_lt)
  have hRealAtTop : Tendsto (fun n : ℕ ↦ ((f n : ℕ) : ℝ)) atTop atTop := by
    have hLower :
        (fun n : ℕ ↦ (c / 2) * n) ≤ᶠ[atTop] fun n ↦ ((f n : ℕ) : ℝ) := by
      filter_upwards [hEventuallyRatio, eventually_ge_atTop 1] with n hn hn₁
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn₁
      have : (c / 2) * n < ((f n : ℕ) : ℝ) := by
        exact (lt_div_iff₀ hn_pos).1 hn
      exact le_of_lt this
    have hLowerAtTop :
        Tendsto (fun n : ℕ ↦ (c / 2) * n) atTop atTop := by
      exact Tendsto.const_mul_atTop hc_half tendsto_natCast_atTop_atTop
    exact tendsto_atTop_mono' atTop hLower hLowerAtTop
  refine tendsto_atTop.2 fun b ↦ ?_
  exact (tendsto_atTop.1 hRealAtTop b).mono fun n hn ↦ by
    exact_mod_cast hn

/-- Helper for Exercise 24.3.3: the remaining proportion after removing the next rounded block is
the quotient of the two residual-size normalizations, so its limit is the corresponding quotient of
their deterministic masses. -/
private theorem remainingAfterNextFloorOverRemaining_tendsto {l : ℕ} (xs : Fin l → ℝ) {x : ℝ}
    (hxs_nonneg : ∀ i, 0 ≤ xs i) (hx_nonneg : 0 ≤ x) (hxs_sum_x_lt : Finset.univ.sum xs + x < 1) :
    Tendsto
      (fun n : ℕ ↦
        (((roundedRemainingCustomerCount xs n - ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) /
          (roundedRemainingCustomerCount xs n : ℝ)))
      atTop
      (𝓝 (1 - x / chineseRestaurantRemainingMass xs)) := by
  -- Proof comment: divide the post-next-block residual ratio by the current residual ratio and
  -- then rewrite the deterministic quotient into the advertised `1 - x / y` form.
  have hRemainingPos : 0 < chineseRestaurantRemainingMass xs := by
    unfold chineseRestaurantRemainingMass
    have hsum_nonneg : 0 ≤ Finset.univ.sum xs := by
      exact Finset.sum_nonneg fun i _ ↦ hxs_nonneg i
    nlinarith [hsum_nonneg, hxs_sum_x_lt, hx_nonneg]
  have hRemainingNe : chineseRestaurantRemainingMass xs ≠ 0 := ne_of_gt hRemainingPos
  have hRemaining :
      Tendsto
        (fun n : ℕ ↦ (((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n))
        atTop
        (𝓝 (chineseRestaurantRemainingMass xs)) := by
    have hxs_sum_le : Finset.univ.sum xs ≤ 1 := by nlinarith [hxs_sum_x_lt, hx_nonneg]
    exact remainingFloorRatio_tendsto xs hxs_nonneg hxs_sum_le
  have hAfter :
      Tendsto
        (fun n : ℕ ↦
          ((((roundedRemainingCustomerCount xs n - ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n)))
        atTop
        (𝓝 (chineseRestaurantRemainingMass xs - x)) := by
    exact remainingAfterNextFloorRatio_tendsto xs hxs_nonneg (by linarith) hx_nonneg
  have hQuot :
      Tendsto
        (fun n : ℕ ↦
          ((((roundedRemainingCustomerCount xs n - ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n) /
            ((((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n)))
        )
        atTop
        (𝓝 ((chineseRestaurantRemainingMass xs - x) / chineseRestaurantRemainingMass xs)) := by
    exact hAfter.div hRemaining hRemainingNe
  have hEventually :
      (fun n : ℕ ↦
        (((roundedRemainingCustomerCount xs n - ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) /
          (roundedRemainingCustomerCount xs n : ℝ))) =ᶠ[atTop]
        fun n : ℕ ↦
          ((((roundedRemainingCustomerCount xs n - ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) / n) /
            ((((roundedRemainingCustomerCount xs n : ℕ) : ℝ) / n))) := by
    refine Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    by_cases hm : (((roundedRemainingCustomerCount xs n : ℕ) : ℝ)) = 0
    · simp [hm]
    · field_simp [hn_ne, hm]
  have hLimit :
      Tendsto
        (fun n : ℕ ↦
          (((roundedRemainingCustomerCount xs n - ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) /
            (roundedRemainingCustomerCount xs n : ℝ)))
        atTop
        (𝓝 ((chineseRestaurantRemainingMass xs - x) / chineseRestaurantRemainingMass xs)) := by
    exact hQuot.congr' hEventually.symm
  have hTarget :
      ((chineseRestaurantRemainingMass xs - x) / chineseRestaurantRemainingMass xs) =
        1 - x / chineseRestaurantRemainingMass xs := by
    field_simp [hRemainingNe]
  simpa [hTarget] using hLimit

/-- Helper for Exercise 24.3.3: the rounded prefix counts together with one extra rounded block
still fit inside the restaurant whenever the prescribed masses sum to at most `1`. -/
private theorem roundedPrefixAndNextFloor_le {l : ℕ} (xs : Fin l → ℝ) {x : ℝ}
    (hxs_nonneg : ∀ i, 0 ≤ xs i) (hx_nonneg : 0 ≤ x) (hxs_sum_x_le : Finset.univ.sum xs + x ≤ 1)
    (n : ℕ) :
    roundedPrefixCustomerCount xs n + ⌊(n : ℝ) * x⌋₊ ≤ n := by
  -- Proof comment: bound each floor by its defining real mass and then use the total mass
  -- constraint `∑ xs + x ≤ 1`.
  have hPrefixLe :
      ((roundedPrefixCustomerCount xs n : ℕ) : ℝ) ≤ (n : ℝ) * Finset.univ.sum xs := by
    calc
      ((roundedPrefixCustomerCount xs n : ℕ) : ℝ)
          = Finset.univ.sum (fun i ↦ ((⌊(n : ℝ) * xs i⌋₊ : ℕ) : ℝ)) := by
              simp [roundedPrefixCustomerCount, Nat.cast_sum]
      _ ≤ Finset.univ.sum (fun i ↦ (n : ℝ) * xs i) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact_mod_cast
              (Nat.floor_le (mul_nonneg (show 0 ≤ (n : ℝ) by positivity) (hxs_nonneg i)))
      _ = (n : ℝ) * Finset.univ.sum xs := by rw [Finset.mul_sum]
  have hFloorLe : ((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * x := by
    exact_mod_cast
      (Nat.floor_le (mul_nonneg (show 0 ≤ (n : ℝ) by positivity) hx_nonneg))
  have hReal :
      (((roundedPrefixCustomerCount xs n + ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ)) ≤ n := by
    have : (n : ℝ) * Finset.univ.sum xs + (n : ℝ) * x ≤ n := by
      nlinarith
    have hCast :
        (((roundedPrefixCustomerCount xs n + ⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ)) =
          ((roundedPrefixCustomerCount xs n : ℕ) : ℝ) +
            ((⌊(n : ℝ) * x⌋₊ : ℕ) : ℝ) := by
      norm_num [Nat.cast_add]
    rw [hCast]
    linarith
  exact_mod_cast hReal

/-- Helper for Exercise 24.3.3: if every prescribed initial block proportion is strictly positive,
then every rounded block count is eventually positive as well. -/
private theorem eventually_positive_roundedFloors {l : ℕ} (xs : Fin l → ℝ)
    (hxs_pos : ∀ i, 0 < xs i) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin l, 0 < ⌊(n : ℝ) * xs i⌋₊ := by
  induction l with
  | zero =>
      exact Filter.Eventually.of_forall (by intro n i; exact Fin.elim0 i)
  | succ l ih =>
      let x0 : ℝ := xs 0
      let xsTail : Fin l → ℝ := fun i ↦ xs i.succ
      have hHead : ∀ᶠ n : ℕ in atTop, 0 < ⌊(n : ℝ) * x0⌋₊ := by
        have hnx : Tendsto (fun n : ℕ ↦ (n : ℝ) * x0) atTop atTop := by
          simpa [x0, mul_comm] using
            (tendsto_natCast_atTop_atTop.atTop_mul_const (hxs_pos 0))
        exact (tendsto_atTop.1 hnx 1).mono fun n hn ↦ Nat.floor_pos.2 hn
      have hTail : ∀ᶠ n : ℕ in atTop, ∀ i : Fin l, 0 < ⌊(n : ℝ) * xsTail i⌋₊ := by
        exact ih xsTail (fun i ↦ hxs_pos i.succ)
      -- Proof comment: `Fin (l + 1)` splits into its head coordinate and the tail coordinates.
      filter_upwards [hHead, hTail] with n hnHead hnTail
      simpa [Fin.forall_fin_succ, x0, xsTail] using And.intro hnHead hnTail

-- Proof sketch: for the zero-discount process with `θ = 1`, the first occupied table has the
-- same law as the length of the first cycle of a uniform random permutation of `{1, …, n}`; the
-- cycle-length law is uniform on `{1, …, n}`.
/-- For Exercise 24.3.3 (1): in the case `θ = 1`, the first table size `N_1^n` (Lean index `0`) is
uniform on `{1, …, n}`. -/
theorem chineseRestaurant_first_table_uniform
    (crp : ChineseRestaurantProcessZeroDiscount 1) {n k : ℕ}
    (_hk_pos : 0 < k) (_hk_le : k ≤ n) :
    ((crp.law : Measure crp.Ω) ({ω | crp.tableSize n ω 0 = k} : Set crp.Ω)) =
      ENNReal.ofReal (1 / (n : ℝ)) := by
  -- Proof comment: rewrite the first-table law through the exact zero-discount mass, then use the
  -- closed-form evaluation of that mass at `θ = 1`.
  simpa [chineseRestaurantTableSizeMass_thetaOne _hk_pos _hk_le] using
    firstTableLaw_eq_tableSizeMass crp _hk_pos _hk_le

-- Proof sketch: condition on the first `l` table sizes and use the Ewens-permutation description
-- for `θ = 1`; after removing the already specified customers, the next table length is uniform on
-- the remaining set of admissible sizes.
/-- For Exercise 24.3.3 (2): in the case `θ = 1`, after conditioning on the first `l` table sizes,
the next table size (Lean index `l`) is uniform on the remaining sizes. -/
theorem chineseRestaurant_next_table_conditional_uniform
    (crp : ChineseRestaurantProcessZeroDiscount 1) {n l k : ℕ} (ks : Fin l → ℕ)
    (_hk_pos : 0 < k) (_hks_pos : ∀ i, 0 < ks i)
    (_hks_sum_le : Finset.univ.sum ks + k ≤ n) :
    (crp.law : Measure crp.Ω)[({ω | crp.tableSize n ω l = k} : Set crp.Ω) |
      ({ω | ∀ i : Fin l, crp.tableSize n ω i = ks i} : Set crp.Ω)] =
      ENNReal.ofReal (1 / ((n - Finset.univ.sum ks : ℕ) : ℝ)) := by
  have hremaining_le : k ≤ n - Finset.univ.sum ks := by
    apply Nat.le_sub_of_add_le
    simpa [add_comm] using _hks_sum_le
  -- Proof comment: the stored conditional law already gives the exact mass on the remaining
  -- restaurant, and at `θ = 1` that mass is uniform over the admissible sizes.
  simpa [chineseRestaurantTableSizeMass_thetaOne _hk_pos hremaining_le] using
    (crp.next_table_conditional_law ks _hk_pos _hks_pos _hks_sum_le)

-- Semantic recall note: the ranked limit layer in the local Chapter 24 API is expressed via
-- `rankedRearrangement` and `poissonDirichletDistribution`, matching Theorem 24.35.
-- Proof sketch: combine clauses (1) and (2) with the argument of Theorem 24.35 in the special
-- case `(α, θ) = (0, 1)`, then sort the appearance-ordered normalized block sizes into decreasing
-- order to obtain the Poisson--Dirichlet limit law `PD_{0,1}`.
/-- Helper for Exercise 24.3.3: ranking the appearance-order block-proportion law is the same as
pushing it forward along `rankedRearrangement`. -/
private theorem rankedBlockProportionsLaw_eq_rankedAppearanceLaw {θ : ℝ}
    (crp : ChineseRestaurantProcessZeroDiscount θ) (n : ℕ) :
    crp.law.map
        ((measurable_rankedRearrangement.comp (crp.measurable_blockProportions n)).aemeasurable) =
      (crp.law.map (crp.measurable_blockProportions n).aemeasurable).map
        measurable_rankedRearrangement.aemeasurable := by
  -- Proof comment: rank the appearance-order block proportions by one further pushforward; this
  -- is the only exact finite-law identity available for the ranked clauses in this file.
  apply ProbabilityMeasure.toMeasure_injective
  simpa [Function.comp] using
    (AEMeasurable.map_map_of_aemeasurable
      (μ := (crp.law : Measure crp.Ω))
      measurable_rankedRearrangement.aemeasurable
      (crp.measurable_blockProportions n).aemeasurable).symm

/-- Exercise 24.3.3 (3): for `θ = 1`, the ranked normalized Chinese-restaurant block sizes
converge weakly to the Poisson--Dirichlet law `PD_{0,1}`. -/
theorem chineseRestaurant_theta_one_rankedBlockProportions_tendsto_poissonDirichlet
    (crp : ChineseRestaurantProcessZeroDiscount 1) :
    Tendsto
      (fun n ↦
        crp.law.map
          ((measurable_rankedRearrangement.comp
            (crp.measurable_blockProportions n)).aemeasurable))
      atTop
      (𝓝 (poissonDirichletDistribution
        0 1 le_rfl zeroDiscountAlphaLtOne zeroDiscountThetaPos)) := by
  -- Route correction: the intended proof is the `α = 0` specialization of Theorem 24.35.
  let process := zeroDiscountToChineseRestaurantProcess crp
  have hgeneral :
      Tendsto (normalizedChineseRestaurantProcessLaw process) atTop
        (𝓝 (poissonDirichletDistribution
          0 1 le_rfl zeroDiscountAlphaLtOne (zeroDiscountThetaAdmissible crp))) := by
    -- Proof comment: Theorem 24.35 applies directly once the zero-discount owner is repackaged as
    -- a general Chinese restaurant process with `α = 0`.
    simpa [process] using
      normalizedChineseRestaurantPartitionLaw_tendsto_poissonDirichlet
        0 1 le_rfl zeroDiscountAlphaLtOne (zeroDiscountThetaAdmissible crp) process
  have hshift :
      Tendsto
        (fun n ↦
          crp.law.map
            ((measurable_rankedRearrangement.comp
              (crp.measurable_blockProportions (n + 1))).aemeasurable))
        atTop
        (𝓝 (poissonDirichletDistribution
          0 1 le_rfl zeroDiscountAlphaLtOne zeroDiscountThetaPos)) := by
    -- Proof comment: the packaged normalized law is exactly the local ranked law with the expected
    -- one-step time shift.
    have hseq :
        normalizedChineseRestaurantProcessLaw process =
          (fun n ↦
            crp.law.map
              ((measurable_rankedRearrangement.comp
                (crp.measurable_blockProportions (n + 1))).aemeasurable)) := by
      funext n
      exact normalizedChineseRestaurantProcessLaw_eq_zeroDiscountRankedLaw_succ crp n
    have hshifted :
        Tendsto
          (fun n ↦
            crp.law.map
              ((measurable_rankedRearrangement.comp
                (crp.measurable_blockProportions (n + 1))).aemeasurable))
          atTop
          (𝓝 (poissonDirichletDistribution
            0 1 le_rfl zeroDiscountAlphaLtOne (zeroDiscountThetaAdmissible crp))) := by
      simpa [hseq] using hgeneral
    simpa using hshifted
  -- Proof comment: convergence of the shifted sequence is equivalent to convergence of the
  -- original sequence along `atTop`.
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hshift

-- Proof sketch: write the exact Ewens sampling formula for `N_1^n`, evaluate it at
-- `k = ⌊n x⌋`, and use the asymptotics of Gamma-function ratios or rising factorials to identify
-- the limit density `θ (1 - x)^{θ - 1}`.
/-- For Exercise 24.3.3 (4): for `θ > 0`, the first table size satisfies the local limit
`n P[N_1^n = ⌊n x⌋] → θ (1 - x)^{θ - 1}` for every `x ∈ (0, 1)`. -/
theorem chineseRestaurant_first_table_localLimit
    {θ x : ℝ} (crp : ChineseRestaurantProcessZeroDiscount θ)
    (_hx0 : 0 < x) (_hx1 : x < 1) :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) *
          ((crp.law : Measure crp.Ω) {ω | crp.tableSize n ω 0 = ⌊(n : ℝ) * x⌋₊}).toReal)
      atTop
      (𝓝 (θ * (1 - x) ^ (θ - 1))) := by
  -- Route correction: the finite-dimensional law is now isolated in
  -- `firstTableLaw_eq_tableSizeMass`; the remaining work is the Gamma-ratio local-limit argument.
  let k : ℕ → ℕ := fun n ↦ ⌊(n : ℝ) * x⌋₊
  let r : ℕ → ℕ := fun n ↦ n - k n
  have hkPos :
      ∀ᶠ n : ℕ in atTop, 0 < k n := by
    have hnx : Tendsto (fun n : ℕ ↦ (n : ℝ) * x) atTop atTop := by
      simpa [mul_comm] using (tendsto_natCast_atTop_atTop.atTop_mul_const _hx0)
    filter_upwards [(tendsto_atTop.1 hnx 1)] with n hn
    exact (Nat.floor_pos.2 hn)
  have hkLt :
      ∀ᶠ n : ℕ in atTop, k n < n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hmul_lt : (n : ℝ) * x < n := by
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
      nlinarith
    exact (Nat.floor_lt (show 0 ≤ (n : ℝ) * x by positivity)).2 hmul_lt
  have hResidualRatio :
      Tendsto (fun n : ℕ ↦ ((r n : ℕ) : ℝ) / n) atTop (𝓝 (1 - x)) := by
    simpa [k, r, chineseRestaurantRemainingMass] using
      (remainingAfterNextFloorRatio_tendsto (xs := fun i : Fin 0 ↦ Fin.elim0 i)
        (hxs_nonneg := fun i ↦ Fin.elim0 i) (hxs_sum_x_le := by simpa using _hx1.le)
        (hx_nonneg := _hx0.le))
  have hResidualAtTop : Tendsto r atTop atTop := by
    exact natSequence_tendsto_atTop_of_div_tendsto_positive hResidualRatio (by linarith)
  have hEventually :
      (fun n : ℕ ↦
        (n : ℝ) *
          ((crp.law : Measure crp.Ω) {ω | crp.tableSize n ω 0 = k n}).toReal) =ᶠ[atTop]
        fun n : ℕ ↦
          θ *
            (((n : ℝ) ^ (θ - 1)) * (Real.Gamma ((n : ℝ) + 1) / Real.Gamma ((n : ℝ) + θ))) *
            ((((r n : ℕ) : ℝ) ^ (1 - θ)) *
              (Real.Gamma (((r n : ℕ) : ℝ) + θ) / Real.Gamma (((r n : ℕ) : ℝ) + 1))) *
            ((((r n : ℕ) : ℝ) / n) ^ (θ - 1)) := by
    filter_upwards [hkPos, hkLt] with n hkn_pos hkn_lt
    have hmass :
        ((crp.law : Measure crp.Ω) {ω | crp.tableSize n ω 0 = k n}).toReal =
          zeroDiscountTableSizeMass θ n (k n) := by
      have hmass_nonneg : 0 ≤ zeroDiscountTableSizeMass θ n (k n) := by
        rw [zeroDiscountTableSizeMass]
        have hchoose_nonneg : 0 ≤ (((n - 1).choose (k n - 1) : ℝ)) := by positivity
        have hbeta_num_pos :
            0 < ProbabilityTheory.beta (k n) (((n - k n : ℕ) : ℝ) + θ) := by
          refine ProbabilityTheory.beta_pos ?_ ?_
          · exact_mod_cast hkn_pos
          · have hres_nonneg : 0 ≤ (((n - k n : ℕ) : ℝ)) := by positivity
            nlinarith [crp.theta_pos, hres_nonneg]
        have hnum_nonneg :
            0 ≤
              (((n - 1).choose (k n - 1) : ℝ) *
                ProbabilityTheory.beta (k n) (((n - k n : ℕ) : ℝ) + θ)) := by
          exact mul_nonneg hchoose_nonneg hbeta_num_pos.le
        have hden_nonneg : 0 ≤ ProbabilityTheory.beta 1 θ := by
          exact (ProbabilityTheory.beta_pos zero_lt_one crp.theta_pos).le
        exact div_nonneg hnum_nonneg hden_nonneg
      calc
        ((crp.law : Measure crp.Ω) {ω | crp.tableSize n ω 0 = k n}).toReal
            = (ENNReal.ofReal (zeroDiscountTableSizeMass θ n (k n))).toReal := by
                exact congrArg ENNReal.toReal (firstTableLaw_eq_tableSizeMass crp hkn_pos hkn_lt.le)
        _ = zeroDiscountTableSizeMass θ n (k n) := ENNReal.toReal_ofReal hmass_nonneg
    rw [hmass]
    simpa [k, r] using
      (scaledZeroDiscountTableSizeMass_eq_gammaLimitFactors crp.theta_pos hkn_pos hkn_lt)
  have hTotalGamma :
      Tendsto
        (fun n : ℕ ↦
          ((n : ℝ) ^ (θ - 1)) * (Real.Gamma ((n : ℝ) + 1) / Real.Gamma ((n : ℝ) + θ)))
        atTop
        (𝓝 1) :=
    gammaSuccDivGammaAdd_mulPow_tendsto_one crp.theta_pos
  have hResidualGamma :
      Tendsto
        (fun n : ℕ ↦
          (((r n : ℕ) : ℝ) ^ (1 - θ)) *
            (Real.Gamma (((r n : ℕ) : ℝ) + θ) / Real.Gamma (((r n : ℕ) : ℝ) + 1)))
        atTop
        (𝓝 1) := by
    exact (powOneSubThetaMulGammaAddDivGammaSucc_tendsto_one crp.theta_pos).comp hResidualAtTop
  have hResidualPow :
      Tendsto (fun n : ℕ ↦ ((((r n : ℕ) : ℝ) / n) ^ (θ - 1))) atTop
        (𝓝 ((1 - x) ^ (θ - 1))) := by
    exact
      (Real.continuousAt_rpow_const (1 - x) (θ - 1)
        (Or.inl (sub_ne_zero.mpr _hx1.ne.symm))).tendsto.comp
        hResidualRatio
  have hLimit :
      Tendsto
        (fun n : ℕ ↦
          θ *
            (((n : ℝ) ^ (θ - 1)) * (Real.Gamma ((n : ℝ) + 1) / Real.Gamma ((n : ℝ) + θ))) *
            ((((r n : ℕ) : ℝ) ^ (1 - θ)) *
              (Real.Gamma (((r n : ℕ) : ℝ) + θ) / Real.Gamma (((r n : ℕ) : ℝ) + 1))) *
            ((((r n : ℕ) : ℝ) / n) ^ (θ - 1)))
        atTop
        (𝓝 (θ * (1 - x) ^ (θ - 1))) := by
    simpa [mul_assoc] using
      (tendsto_const_nhds.mul ((hTotalGamma.mul hResidualGamma).mul hResidualPow))
  exact hLimit.congr' hEventually.symm

-- Proof sketch: condition on the first `l` rescaled table sizes, apply the Ewens sampling formula
-- to the remaining restaurant with residual mass `y = 1 - ∑_{i < l} x_i`, and pass to the limit
-- exactly as in the one-dimensional case after rescaling by the residual mass.
/-- For Exercise 24.3.3 (5): for `θ > 0`, after conditioning on the first `l` block sizes, the
next block size has local limit density `(θ / y) (1 - x / y)^{θ - 1}` with
`y = 1 - (x_1 + ··· + x_{l-1})`. -/
theorem chineseRestaurant_next_table_conditional_localLimit
    {θ x : ℝ} (crp : ChineseRestaurantProcessZeroDiscount θ) {l : ℕ}
    (xs : Fin l → ℝ) (_hxs_pos : ∀ i, 0 < xs i)
    (_hx_pos : 0 < x) (_hx_lt_remaining : x < chineseRestaurantRemainingMass xs) :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) *
          ((crp.law : Measure crp.Ω)[{ω | crp.tableSize n ω l = ⌊(n : ℝ) * x⌋₊} |
            {ω | ∀ i : Fin l, crp.tableSize n ω i = ⌊(n : ℝ) * xs i⌋₊}]).toReal)
      atTop
      (𝓝
        ((θ / chineseRestaurantRemainingMass xs) *
          (1 - x / chineseRestaurantRemainingMass xs) ^ (θ - 1))) := by
  -- Route correction: the contradiction-based route has been removed in favor of the exact
  -- conditional-mass formula already stored in `crp.next_table_conditional_law`.
  -- Proof comment: the reusable ingredients are now in place:
  -- `scaledZeroDiscountTableSizeMass_eq_gammaLimitFactors`,
  -- `natSequence_tendsto_atTop_of_div_tendsto_positive`, and
  -- `remainingAfterNextFloorOverRemaining_tendsto`.
  let k : ℕ → ℕ := fun n ↦ ⌊(n : ℝ) * x⌋₊
  let m : ℕ → ℕ := roundedRemainingCustomerCount xs
  let r : ℕ → ℕ := fun n ↦ m n - k n
  let y : ℝ := chineseRestaurantRemainingMass xs
  have hxs_nonneg : ∀ i, 0 ≤ xs i := fun i ↦ (_hxs_pos i).le
  have hxs_sum_x_lt : Finset.univ.sum xs + x < 1 := by
    unfold chineseRestaurantRemainingMass at _hx_lt_remaining
    linarith
  have hy_pos : 0 < y := by
    have hsum_nonneg : 0 ≤ Finset.univ.sum xs := by
      exact Finset.sum_nonneg fun i _ ↦ hxs_nonneg i
    unfold y chineseRestaurantRemainingMass
    nlinarith
  have hy_ne : y ≠ 0 := ne_of_gt hy_pos
  have hkPos : ∀ᶠ n : ℕ in atTop, 0 < k n := by
    have hnx : Tendsto (fun n : ℕ ↦ (n : ℝ) * x) atTop atTop := by
      simpa [mul_comm] using (tendsto_natCast_atTop_atTop.atTop_mul_const _hx_pos)
    filter_upwards [(tendsto_atTop.1 hnx 1)] with n hn
    exact Nat.floor_pos.2 hn
  have hksPos : ∀ᶠ n : ℕ in atTop, ∀ i : Fin l, 0 < ⌊(n : ℝ) * xs i⌋₊ :=
    eventually_positive_roundedFloors xs _hxs_pos
  have hRemainingRatio :
      Tendsto (fun n : ℕ ↦ (((m n : ℕ) : ℝ) / n)) atTop (𝓝 y) := by
    have hxs_sum_le : Finset.univ.sum xs ≤ 1 := by
      nlinarith [hxs_sum_x_lt, _hx_pos]
    simpa [m, y] using remainingFloorRatio_tendsto xs hxs_nonneg hxs_sum_le
  have hRemainingAtTop : Tendsto m atTop atTop := by
    exact natSequence_tendsto_atTop_of_div_tendsto_positive hRemainingRatio hy_pos
  have hmPos : ∀ᶠ n : ℕ in atTop, 0 < m n := by
    exact (tendsto_atTop.1 hRemainingAtTop 1).mono fun n hn ↦ lt_of_lt_of_le Nat.zero_lt_one hn
  have hResidualRatio :
      Tendsto (fun n : ℕ ↦ (((r n : ℕ) : ℝ) / n)) atTop (𝓝 (y - x)) := by
    simpa [r, m, y] using
      remainingAfterNextFloorRatio_tendsto xs hxs_nonneg (by linarith : Finset.univ.sum xs + x ≤ 1)
        _hx_pos.le
  have hResidualMassPos : 0 < y - x := by
    nlinarith [hy_pos, _hx_lt_remaining]
  have hResidualAtTop : Tendsto r atTop atTop := by
    exact natSequence_tendsto_atTop_of_div_tendsto_positive hResidualRatio hResidualMassPos
  have hkLt : ∀ᶠ n : ℕ in atTop, k n < m n := by
    have hrPos : ∀ᶠ n : ℕ in atTop, 0 < r n := by
      exact (tendsto_atTop.1 hResidualAtTop 1).mono fun n hn ↦ lt_of_lt_of_le Nat.zero_lt_one hn
    filter_upwards [hrPos] with n hn
    exact Nat.sub_pos_iff_lt.mp (by simpa [r] using hn)
  have hResidualOverRemaining :
      Tendsto
        (fun n : ℕ ↦ (((r n : ℕ) : ℝ) / (m n : ℝ)))
        atTop
        (𝓝 (1 - x / y)) := by
    simpa [r, m, y] using
      remainingAfterNextFloorOverRemaining_tendsto xs hxs_nonneg _hx_pos.le hxs_sum_x_lt
  have hResidualOverRemainingPos : 0 < 1 - x / y := by
    have hxy : x < y := by
      simpa [y] using _hx_lt_remaining
    exact sub_pos.mpr ((div_lt_one hy_pos).2 hxy)
  have hRatioInv :
      Tendsto (fun n : ℕ ↦ ((((m n : ℕ) : ℝ) / n))⁻¹) atTop (𝓝 (1 / y)) := by
    simpa [one_div] using (Tendsto.inv₀ hRemainingRatio hy_ne)
  have hRatioEventually :
      (fun n : ℕ ↦ (n : ℝ) / (m n : ℝ)) =ᶠ[atTop]
        fun n : ℕ ↦ ((((m n : ℕ) : ℝ) / n))⁻¹ := by
    filter_upwards [hmPos, eventually_ge_atTop 1] with n hm hn
    have hm_ne : (m n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hm)
    have hn_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hm_ne, hn_ne]
  have hRatio :
      Tendsto (fun n : ℕ ↦ (n : ℝ) / (m n : ℝ)) atTop (𝓝 (1 / y)) := by
    exact hRatioInv.congr' hRatioEventually.symm
  have hEventually :
      (fun n : ℕ ↦
        (n : ℝ) *
          ((crp.law : Measure crp.Ω)[{ω | crp.tableSize n ω l = k n} |
            {ω | ∀ i : Fin l, crp.tableSize n ω i = ⌊(n : ℝ) * xs i⌋₊}]).toReal) =ᶠ[atTop]
        fun n : ℕ ↦
          ((n : ℝ) / (m n : ℝ)) *
            (θ *
              (((m n : ℝ) ^ (θ - 1)) *
                (Real.Gamma ((m n : ℝ) + 1) / Real.Gamma ((m n : ℝ) + θ))) *
              ((((r n : ℕ) : ℝ) ^ (1 - θ)) *
                (Real.Gamma (((r n : ℕ) : ℝ) + θ) / Real.Gamma (((r n : ℕ) : ℝ) + 1))) *
              ((((r n : ℕ) : ℝ) / (m n : ℝ)) ^ (θ - 1))) := by
    filter_upwards [hkPos, hkLt, hksPos] with n hkn_pos hklt hks_pos
    have hm_pos : 0 < m n := lt_trans hkn_pos hklt
    have hm_ne : (m n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hm_pos)
    have hsum_le :
        Finset.univ.sum (fun i : Fin l ↦ ⌊(n : ℝ) * xs i⌋₊) + k n ≤ n := by
      simpa [roundedPrefixCustomerCount, k] using
        (roundedPrefixAndNextFloor_le xs hxs_nonneg _hx_pos.le hxs_sum_x_lt.le n)
    have hmass_nonneg : 0 ≤ zeroDiscountTableSizeMass θ (m n) (k n) := by
      rw [zeroDiscountTableSizeMass]
      have hchoose_nonneg : 0 ≤ (((m n - 1).choose (k n - 1) : ℝ)) := by positivity
      have hbeta_num_pos :
          0 < ProbabilityTheory.beta (k n) (((m n - k n : ℕ) : ℝ) + θ) := by
        refine ProbabilityTheory.beta_pos ?_ ?_
        · exact_mod_cast hkn_pos
        · have hres_nonneg : 0 ≤ (((m n - k n : ℕ) : ℝ)) := by positivity
          nlinarith [crp.theta_pos, hres_nonneg]
      have hnum_nonneg :
          0 ≤
            (((m n - 1).choose (k n - 1) : ℝ) *
              ProbabilityTheory.beta (k n) (((m n - k n : ℕ) : ℝ) + θ)) := by
        exact mul_nonneg hchoose_nonneg hbeta_num_pos.le
      have hden_nonneg : 0 ≤ ProbabilityTheory.beta 1 θ := by
        exact (ProbabilityTheory.beta_pos zero_lt_one crp.theta_pos).le
      exact div_nonneg hnum_nonneg hden_nonneg
    have hmass :
        ((crp.law : Measure crp.Ω)[{ω | crp.tableSize n ω l = k n} |
          {ω | ∀ i : Fin l, crp.tableSize n ω i = ⌊(n : ℝ) * xs i⌋₊}]).toReal =
          zeroDiscountTableSizeMass θ (m n) (k n) := by
      calc
        ((crp.law : Measure crp.Ω)[{ω | crp.tableSize n ω l = k n} |
          {ω | ∀ i : Fin l, crp.tableSize n ω i = ⌊(n : ℝ) * xs i⌋₊}]).toReal
            =
              (ENNReal.ofReal (zeroDiscountTableSizeMass θ (m n) (k n))).toReal := by
                exact congrArg ENNReal.toReal
                  (by
                    simpa [m, k, roundedRemainingCustomerCount, roundedPrefixCustomerCount] using
                      (crp.next_table_conditional_law
                        (n := n) (l := l) (k := k n)
                        (ks := fun i : Fin l ↦ ⌊(n : ℝ) * xs i⌋₊)
                        hkn_pos hks_pos hsum_le))
        _ = zeroDiscountTableSizeMass θ (m n) (k n) := ENNReal.toReal_ofReal hmass_nonneg
    -- Proof comment: rewrite the conditional law on the remaining restaurant, then split off the
    -- prefactor `n / m_n` from the scaled zero-discount mass.
    calc
      (n : ℝ) *
          ((crp.law : Measure crp.Ω)[{ω | crp.tableSize n ω l = k n} |
            {ω | ∀ i : Fin l, crp.tableSize n ω i = ⌊(n : ℝ) * xs i⌋₊}]).toReal
          = (n : ℝ) * zeroDiscountTableSizeMass θ (m n) (k n) := by rw [hmass]
      _ = ((n : ℝ) / (m n : ℝ)) * ((m n : ℝ) * zeroDiscountTableSizeMass θ (m n) (k n)) := by
            field_simp [hm_ne]
      _ = ((n : ℝ) / (m n : ℝ)) *
            (θ *
              (((m n : ℝ) ^ (θ - 1)) *
                (Real.Gamma ((m n : ℝ) + 1) / Real.Gamma ((m n : ℝ) + θ))) *
              ((((r n : ℕ) : ℝ) ^ (1 - θ)) *
                (Real.Gamma (((r n : ℕ) : ℝ) + θ) / Real.Gamma (((r n : ℕ) : ℝ) + 1))) *
              ((((r n : ℕ) : ℝ) / (m n : ℝ)) ^ (θ - 1))) := by
            rw [scaledZeroDiscountTableSizeMass_eq_gammaLimitFactors crp.theta_pos hkn_pos hklt]
  have hTotalGamma :
      Tendsto
        (fun n : ℕ ↦
          ((m n : ℝ) ^ (θ - 1)) * (Real.Gamma ((m n : ℝ) + 1) / Real.Gamma ((m n : ℝ) + θ)))
        atTop
        (𝓝 1) := by
    exact (gammaSuccDivGammaAdd_mulPow_tendsto_one crp.theta_pos).comp hRemainingAtTop
  have hResidualGamma :
      Tendsto
        (fun n : ℕ ↦
          (((r n : ℕ) : ℝ) ^ (1 - θ)) *
            (Real.Gamma (((r n : ℕ) : ℝ) + θ) / Real.Gamma (((r n : ℕ) : ℝ) + 1)))
        atTop
        (𝓝 1) := by
    exact
      (powOneSubThetaMulGammaAddDivGammaSucc_tendsto_one crp.theta_pos).comp hResidualAtTop
  have hResidualPow :
      Tendsto
        (fun n : ℕ ↦ ((((r n : ℕ) : ℝ) / (m n : ℝ)) ^ (θ - 1)))
        atTop
        (𝓝 ((1 - x / y) ^ (θ - 1))) := by
    exact
      (Real.continuousAt_rpow_const (1 - x / y) (θ - 1)
        (Or.inl (ne_of_gt hResidualOverRemainingPos))).tendsto.comp
        hResidualOverRemaining
  have hScaled :
      Tendsto
        (fun n : ℕ ↦
          θ *
            (((m n : ℝ) ^ (θ - 1)) * (Real.Gamma ((m n : ℝ) + 1) / Real.Gamma ((m n : ℝ) + θ))) *
            ((((r n : ℕ) : ℝ) ^ (1 - θ)) *
              (Real.Gamma (((r n : ℕ) : ℝ) + θ) / Real.Gamma (((r n : ℕ) : ℝ) + 1))) *
            ((((r n : ℕ) : ℝ) / (m n : ℝ)) ^ (θ - 1)))
        atTop
        (𝓝 (θ * (1 - x / y) ^ (θ - 1))) := by
    simpa [mul_assoc] using
      (tendsto_const_nhds.mul ((hTotalGamma.mul hResidualGamma).mul hResidualPow))
  have hLimit :
      Tendsto
        (fun n : ℕ ↦
          ((n : ℝ) / (m n : ℝ)) *
            (θ *
              (((m n : ℝ) ^ (θ - 1)) *
                (Real.Gamma ((m n : ℝ) + 1) / Real.Gamma ((m n : ℝ) + θ))) *
              ((((r n : ℕ) : ℝ) ^ (1 - θ)) *
                (Real.Gamma (((r n : ℕ) : ℝ) + θ) / Real.Gamma (((r n : ℕ) : ℝ) + 1))) *
              ((((r n : ℕ) : ℝ) / (m n : ℝ)) ^ (θ - 1))))
        atTop
        (𝓝 ((θ / y) * (1 - x / y) ^ (θ - 1))) := by
    have hMul := hRatio.mul hScaled
    have hTarget :
        y⁻¹ * (θ * (1 - x / y) ^ (θ - 1)) =
          (θ / y) * (1 - x / y) ^ (θ - 1) := by
      rw [div_eq_mul_inv]
      ring
    simpa [one_div, hTarget]
      using hMul
  simpa [k, m, r, y] using hLimit.congr' hEventually.symm

-- Proof sketch: use clauses (4) and (5) to identify the asymptotic ranked normalized block-size
-- law, then invoke the `α = 0` specialization of Theorem 24.35 to conclude weak convergence to
-- `PD_{0,θ}`.
/-- Exercise 24.3.3 (6): for `θ > 0`, the ranked normalized block sizes of the zero-discount
Chinese restaurant process converge weakly to the Poisson--Dirichlet law `PD_{0,θ}`. -/
theorem chineseRestaurant_rankedBlockProportions_tendsto_poissonDirichlet
    {θ : ℝ} (crp : ChineseRestaurantProcessZeroDiscount θ) :
    Tendsto
      (fun n ↦
        crp.law.map
          ((measurable_rankedRearrangement.comp
            (crp.measurable_blockProportions n)).aemeasurable))
      atTop
      (𝓝
        (poissonDirichletDistribution 0 θ le_rfl zeroDiscountAlphaLtOne
          (zeroDiscountThetaAdmissible crp))) := by
  -- Route correction: the intended proof is again the `α = 0` specialization of Theorem 24.35.
  let process := zeroDiscountToChineseRestaurantProcess crp
  have hgeneral :
      Tendsto (normalizedChineseRestaurantProcessLaw process) atTop
        (𝓝
          (poissonDirichletDistribution 0 θ le_rfl zeroDiscountAlphaLtOne
            (zeroDiscountThetaAdmissible crp))) := by
    -- Proof comment: after packaging the zero-discount owner into the general one, the dependency
    -- theorem provides the ranked Poisson--Dirichlet limit immediately.
    simpa [process] using
      normalizedChineseRestaurantPartitionLaw_tendsto_poissonDirichlet
        0 θ le_rfl zeroDiscountAlphaLtOne (zeroDiscountThetaAdmissible crp) process
  have hshift :
      Tendsto
        (fun n ↦
          crp.law.map
            ((measurable_rankedRearrangement.comp
              (crp.measurable_blockProportions (n + 1))).aemeasurable))
        atTop
        (𝓝
          (poissonDirichletDistribution 0 θ le_rfl zeroDiscountAlphaLtOne
            (zeroDiscountThetaAdmissible crp))) := by
    -- Proof comment: the packaged normalized process law is just the local ranked law viewed one
    -- time step later.
    have hseq :
        normalizedChineseRestaurantProcessLaw process =
          (fun n ↦
            crp.law.map
              ((measurable_rankedRearrangement.comp
                (crp.measurable_blockProportions (n + 1))).aemeasurable)) := by
      funext n
      exact normalizedChineseRestaurantProcessLaw_eq_zeroDiscountRankedLaw_succ crp n
    simpa [hseq] using hgeneral
  -- Proof comment: remove the harmless successor shift in the index.
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hshift

end ProbabilityTheory

/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.PowerSums
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_25.Benchmark
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public section
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace TsvdDiscrepancy

/-- Infinite signal tail past the retained TSVD index. -/
@[expose] def powerTail (r : ℝ) (m : ℕ) : ℝ :=
  ∑' k : ℕ, ((k + m + 1 : ℕ) : ℝ) ^ (-r)

lemma powerTail_summable {r : ℝ} (hr : 1 < r) (m : ℕ) :
    Summable (fun k : ℕ ↦ ((k + m + 1 : ℕ) : ℝ) ^ (-r)) := by
  exact (Real.summable_nat_rpow.2 (by linarith : -r < -1)).comp_injective
    (fun _ _ h ↦ by omega)

lemma powerTail_succ (r : ℝ) (hr : 1 < r) (m : ℕ) :
    powerTail r m = ((m : ℝ) + 1) ^ (-r) + powerTail r (m + 1) := by
  have h := (powerTail_summable hr m).tsum_eq_zero_add
  simpa only [powerTail, Nat.zero_add, Nat.cast_add, Nat.cast_one,
    Nat.add_right_comm _ 1 m, add_assoc] using h

lemma powerTail_lower {r : ℝ} (hr : 1 < r) (m : ℕ) :
    ((m : ℝ) + 1) ^ (1 - r) / (r - 1) ≤ powerTail r m := by
  have h := (TsvdEstimation.powerTail_bounds hr (Nat.succ_pos m)).1
  rw [powerTail_succ r hr m]
  change (↑(m + 1) : ℝ) ^ (1 - r) / (r - 1) - (↑(m + 1) : ℝ) ^ (-r) ≤
    powerTail r (m + 1) at h
  simpa only [Nat.cast_add, Nat.cast_one] using (sub_le_iff_le_add.1 h).trans_eq (add_comm _ _)

lemma powerTail_pos {r : ℝ} (hr : 1 < r) (m : ℕ) : 0 < powerTail r m :=
  lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos (by positivity) _) (by linarith))
    (powerTail_lower hr m)

lemma crossing_bounds {A δ r : ℝ} {m : ℕ} (hA : 0 < A) (hδ : 0 < δ) (hr : 1 < r)
    (hlo : A * powerTail r m ≤ δ * (m : ℝ))
    (hhi : 0 < m → δ * ((m - 1 : ℕ) : ℝ) ≤ A * powerTail r (m - 1)) :
    let β : ℝ := (A / ((r - 1) * δ)) ^ (1 / r)
    β ≤ (m : ℝ) + 1 ∧ (m : ℝ) ≤ β + 1 := by
  intro β
  have hbase : 0 < A / ((r - 1) * δ) := div_pos hA (mul_pos (by linarith) hδ)
  have hβ : 0 < β := Real.rpow_pos_of_pos hbase _
  have hβpow : β ^ r = A / ((r - 1) * δ) := by
    dsimp [β]
    rw [← Real.rpow_mul hbase.le, one_div_mul_cancel (by linarith : r ≠ 0), Real.rpow_one]
  constructor
  · apply (Real.rpow_le_rpow_iff hβ.le (by positivity) (by linarith : 0 < r)).1
    rw [hβpow]
    have hl := (mul_le_mul_of_nonneg_left (powerTail_lower hr m) hA.le).trans hlo
    have hmpos : 0 < (m : ℝ) + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hl
      (Real.rpow_nonneg hmpos.le (r - 1))
    have hcancel : ((m : ℝ) + 1) ^ (1 - r) * ((m : ℝ) + 1) ^ (r - 1) = 1 := by
      rw [← Real.rpow_add hmpos, show 1 - r + (r - 1) = 0 by ring, Real.rpow_zero]
    have htarget : A / (r - 1) ≤ δ * ((m : ℝ) + 1) ^ r := by
      calc
        A / (r - 1) = A * (((m : ℝ) + 1) ^ (1 - r) / (r - 1)) *
            ((m : ℝ) + 1) ^ (r - 1) := by
              calc
                _ = A / (r - 1) * (((m : ℝ) + 1) ^ (1 - r) *
                    ((m : ℝ) + 1) ^ (r - 1)) := by rw [hcancel, mul_one]
                _ = _ := by ring
        _ ≤ δ * (m : ℝ) * ((m : ℝ) + 1) ^ (r - 1) := hmul
        _ ≤ δ * ((m : ℝ) + 1) * ((m : ℝ) + 1) ^ (r - 1) := by gcongr; linarith
        _ = δ * ((m : ℝ) + 1) ^ r := by
          rw [mul_assoc, mul_comm ((m : ℝ) + 1) (((m : ℝ) + 1) ^ (r - 1)), ← Real.rpow_add_one hmpos.ne' (r - 1), sub_add_cancel]
    apply (div_le_iff₀ (mul_pos (by linarith) hδ)).2
    have ht := (div_le_iff₀ (by linarith : 0 < r - 1)).1 htarget
    nlinarith
  · by_cases hm : 1 < m
    · have hm1 : 0 < (m - 1 : ℕ) := by omega
      have hm1r : 0 < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hm1
      have hu := (hhi (by omega)).trans
        (mul_le_mul_of_nonneg_left (TsvdEstimation.powerTail_bounds hr hm1).2 hA.le)
      have hpw : (((m - 1 : ℕ) : ℝ)) ^ (r - 1) * (((m - 1 : ℕ) : ℝ)) ^ (1 - r) = 1 := by
        rw [← Real.rpow_add hm1r, show r - 1 + (1 - r) = 0 by ring, Real.rpow_zero]
      have hmul := mul_le_mul_of_nonneg_right hu (Real.rpow_nonneg hm1r.le (r - 1))
      have hpowbound : ((m - 1 : ℕ) : ℝ) ^ r ≤ β ^ r := by
        rw [hβpow]
        apply (le_div_iff₀ (mul_pos (by linarith) hδ)).2
        have heq : δ * ((m - 1 : ℕ) : ℝ) * ((m - 1 : ℕ) : ℝ) ^ (r - 1) =
            δ * ((m - 1 : ℕ) : ℝ) ^ r := by
          rw [mul_assoc, mul_comm ((m - 1 : ℕ) : ℝ) (((m - 1 : ℕ) : ℝ) ^ (r - 1)), ← Real.rpow_add_one hm1r.ne' (r - 1), sub_add_cancel]
        rw [heq] at hmul
        have hright : A * (((m - 1 : ℕ) : ℝ) ^ (1 - r) / (r - 1)) *
            ((m - 1 : ℕ) : ℝ) ^ (r - 1) = A / (r - 1) := by
          calc
            _ = A / (r - 1) * ((((m - 1 : ℕ) : ℝ) ^ (r - 1)) *
                (((m - 1 : ℕ) : ℝ) ^ (1 - r))) := by ring
            _ = _ := by rw [hpw, mul_one]
        rw [hright] at hmul
        have ht := (le_div_iff₀ (by linarith : 0 < r - 1)).1 hmul
        nlinarith
      have hle := (Real.rpow_le_rpow_iff hm1r.le hβ.le (by linarith : 0 < r)).1 hpowbound
      have hcast : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show m = m - 1 + 1 by omega)
      linarith
    · have hmle : (m : ℝ) ≤ 1 := by exact_mod_cast (show m ≤ 1 by omega)
      linarith

lemma indexBenchmark_eq_root {b c p q σ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hpq : 1 < p + q) (hσ : 0 < σ)
    {n : ℕ} (hn : 0 < n) :
    indexBenchmark b c p q σ n =
      (b * c / ((p + q - 1) * (σ ^ 2 / (n : ℝ)))) ^ (1 / (p + q)) := by
  rw [indexBenchmark_def, indexConstant_def, Real.rpow_neg (by positivity)]
  rw [← div_eq_mul_inv, ← Real.div_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

lemma indexBenchmark_tendstoAtTop {b c p q σ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hpq : 1 < p + q) (hσ : 0 < σ) :
    Tendsto (indexBenchmark b c p q σ) atTop atTop := by
  have hδ : Tendsto (fun n : ℕ ↦ σ ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_nhds_zero_nat.const_mul (σ ^ 2))
  have hδpos : ∀ᶠ n : ℕ in atTop, σ ^ 2 / (n : ℝ) ∈ Set.Ioi 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    change 0 < σ ^ 2 / (n : ℝ)
    positivity
  have hδgt := tendsto_nhdsWithin_iff.mpr ⟨hδ, hδpos⟩
  have hpow := (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos (one_div_pos.mpr (by linarith : 0 < p + q)))).comp hδgt
  have hconst : 0 < indexConstant b c p q := by
    rw [indexConstant_def]
    exact Real.rpow_pos_of_pos (by positivity) _
  change Tendsto (fun n ↦ indexBenchmark b c p q σ n) atTop atTop
  simp_rw [indexBenchmark_def]
  exact hpow.const_mul_atTop hconst

lemma crossing_isEquivalent {b c p q σ : ℝ} {m : ℕ → ℕ}
    (hb : 0 < b) (hc : 0 < c) (hpq : 1 < p + q) (hσ : 0 < σ)
    (hcross : ∀ᶠ n in atTop,
      b * c * powerTail (p + q) (m n) ≤ (σ ^ 2 / (n : ℝ)) * (m n : ℝ) ∧
      (0 < m n → (σ ^ 2 / (n : ℝ)) * ((m n - 1 : ℕ) : ℝ) ≤
        b * c * powerTail (p + q) (m n - 1))) :
    IsEquivalent atTop (fun n ↦ (m n : ℝ)) (indexBenchmark b c p q σ) := by
  let β := indexBenchmark b c p q σ
  have hβtop : Tendsto β atTop atTop := indexBenchmark_tendstoAtTop hb hc hpq hσ
  have hβpos : ∀ᶠ n in atTop, 0 < β n := hβtop.eventually (eventually_gt_atTop 0)
  have hInv : Tendsto (fun n ↦ 1 / β n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using! tendsto_inv_atTop_zero.comp hβtop
  have hbounds : ∀ᶠ n in atTop, β n - 1 ≤ (m n : ℝ) ∧ (m n : ℝ) ≤ β n + 1 := by
    filter_upwards [hcross, eventually_gt_atTop 0] with n hcr hn
    have h := crossing_bounds (mul_pos hb hc) (by positivity : 0 < σ ^ 2 / (n : ℝ))
      hpq hcr.1 hcr.2
    rw [← indexBenchmark_eq_root hb hc hpq hσ hn] at h
    change β n ≤ (m n : ℝ) + 1 ∧ (m n : ℝ) ≤ β n + 1 at h
    constructor <;> linarith [h.1, h.2]
  apply isEquivalent_of_tendsto_one
  change Tendsto (fun n ↦ (m n : ℝ) / β n) atTop (𝓝 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n ↦ 1 - 1 / β n) (h := fun n ↦ 1 + 1 / β n)
    (by simpa using tendsto_const_nhds.sub hInv)
    (by simpa using tendsto_const_nhds.add hInv)
  · filter_upwards [hbounds, hβpos] with n h hn
    simpa only [sub_div, div_self hn.ne'] using
      div_le_div_of_nonneg_right h.1 hn.le
  · filter_upwards [hbounds, hβpos] with n h hn
    simpa only [add_div, div_self hn.ne'] using
      div_le_div_of_nonneg_right h.2 hn.le


/-- Spectrally averaged residual: signal tail plus the `n-m` unretained
noise modes, each of variance `σ²/n`. This is an infinite signal tail with
noise in the first `n` modes. A strictly `n`-dimensional datum whose residual
vanishes at `m=n` instead has a signal tail truncated at `n`. -/
@[expose] def powerResidual (b c p q σ : ℝ) (n m : ℕ) : ℝ :=
  b * c * powerTail (p + q) m + (σ ^ 2 / (n : ℝ)) * ((n : ℝ) - (m : ℝ))

/-- Exact residual spectral model, required only eventually and on admissible
indices. It applies directly to expected squared residuals. -/
@[expose] def HasPowerResidualModel (residual : ℕ → ℕ → ℝ) (b c p q σ : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ m ≤ n, residual n m = powerResidual b c p q σ n m

/-- Integer discrepancy rule: cross the noise threshold between adjacent
indices. Exact equality is neither needed nor generally possible. -/
@[expose] def IsResidualDiscrepancyChoiceAt (residual : ℕ → ℕ → ℝ)
    (σ : ℝ) (n m : ℕ) : Prop :=
  m ≤ n ∧ residual n m ≤ σ ^ 2 ∧ (0 < m → σ ^ 2 ≤ residual n (m - 1))

lemma isEquivalent_of_powerResidualModel {residual : ℕ → ℕ → ℝ}
    {b c p q σ : ℝ} {m : ℕ → ℕ}
    (hb : 0 < b) (hc : 0 < c) (hpq : 1 < p + q) (hσ : 0 < σ)
    (hmodel : HasPowerResidualModel residual b c p q σ)
    (hchoice : ∀ᶠ n in atTop, IsResidualDiscrepancyChoiceAt residual σ n (m n)) :
    IsEquivalent atTop (fun n ↦ (m n : ℝ)) (indexBenchmark b c p q σ) := by
  apply crossing_isEquivalent hb hc hpq hσ
  filter_upwards [hmodel, hchoice, eventually_gt_atTop 0] with n hmod hch hn
  have hδn : σ ^ 2 / (n : ℝ) * (n : ℝ) = σ ^ 2 := by
    exact div_mul_cancel₀ _ (by positivity : (n : ℝ) ≠ 0)
  have hlow := hch.2.1
  rw [hmod _ hch.1, powerResidual] at hlow
  constructor
  · nlinarith
  · intro hm
    have hhigh := hch.2.2 hm
    rw [hmod _ ((Nat.sub_le _ _).trans hch.1), powerResidual] at hhigh
    nlinarith

lemma powerTail_tendsto_zero {r : ℝ} (hr : 1 < r) :
    Tendsto (powerTail r) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 - r) / (r - 1)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(r - 1))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < r - 1)).comp hnat
    simpa only [neg_sub, zero_div] using ht.div_const (r - 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpow
  · exact Eventually.of_forall fun n ↦ (powerTail_pos hr n).le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact (TsvdEstimation.powerTail_bounds hr hn).2

lemma exists_discrepancyChoice_eventually {b c p q σ : ℝ}
    (hpq : 1 < p + q) (hσ : 0 < σ) :
    ∀ᶠ n in atTop, ∃ m, IsResidualDiscrepancyChoiceAt
      (powerResidual b c p q σ) σ n m := by
  have htail : Tendsto (fun n ↦ b * c * powerTail (p + q) n) atTop (𝓝 0) := by
    simpa using (powerTail_tendsto_zero hpq).const_mul (b * c)
  filter_upwards [htail.eventually (gt_mem_nhds (sq_pos_of_pos hσ))] with n hn
  have hex : ∃ m : ℕ, powerResidual b c p q σ n m ≤ σ ^ 2 := by
    exact ⟨n, by simpa [powerResidual] using hn.le⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · apply Nat.find_min'
    simpa [powerResidual] using hn.le
  · intro hm
    have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    exact (lt_of_not_ge hprev).le

end TsvdDiscrepancy

/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.PSeries
/-!
# Power-sum estimates for Theorem 7.16

Integral comparison gives the leading constants in the TSVD error:
`∑_{i ≤ m} i^p ~ m^(p+1)/(p+1)` and
`∑_{i > m} i^(-q) ~ m^(1-q)/(q-1)`. After normalization, both errors
are bounded by `1/m`, which gives the required limits directly.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology BigOperators
namespace TsvdEstimation

lemma powerSum_bounds {p : ℝ} (hp : 0 < p) (m : ℕ) :
    (m : ℝ) ^ (p + 1) / (p + 1) ≤ ∑ k ∈ Finset.range m, ((k : ℝ) + 1) ^ p ∧
    (∑ k ∈ Finset.range m, ((k : ℝ) + 1) ^ p) ≤
      (m : ℝ) ^ (p + 1) / (p + 1) + (m : ℝ) ^ p := by
  have hmono : MonotoneOn (fun x : ℝ ↦ x ^ p) (Set.Icc 0 (0 + (m : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow hx.1 hxy hp.le
  have hInt : ∫ x in (0 : ℝ)..m, x ^ p = (m : ℝ) ^ (p + 1) / (p + 1) := by
    rw [integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]
  have hlo := hmono.integral_le_sum
  have hhi := hmono.sum_le_integral
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at hlo hhi
  rw [hInt] at hlo hhi
  refine ⟨hlo, ?_⟩
  have hshift : (∑ k ∈ Finset.range m, ((k : ℝ) + 1) ^ p) =
      (∑ k ∈ Finset.range m, (k : ℝ) ^ p) + (m : ℝ) ^ p := by
    simpa [Real.zero_rpow hp.ne', Nat.cast_add, Nat.cast_one] using
      (Finset.sum_range_succ' (f := fun k : ℕ ↦ (k : ℝ) ^ p) m).symm.trans
        (Finset.sum_range_succ (fun k : ℕ ↦ (k : ℝ) ^ p) m)
  rw [hshift]
  linarith

lemma powerSum_normalized_tendsto {p : ℝ} (hp : 0 < p) :
    Tendsto (fun m : ℕ ↦ (∑ k ∈ Finset.range m, ((k : ℝ) + 1) ^ p) /
      (m : ℝ) ^ (p + 1)) atTop (𝓝 (1 / (p + 1))) := by
  have hInv : Tendsto (fun m : ℕ ↦ 1 / (m : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℕ ↦ 1 / (p + 1))
    (h := fun m : ℕ ↦ 1 / (p + 1) + 1 / (m : ℝ)) tendsto_const_nhds
    (by simpa using tendsto_const_nhds.add hInv)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have h := div_le_div_of_nonneg_right (powerSum_bounds hp m).1
      (Real.rpow_nonneg hmreal.le (p + 1))
    have heq : ((m : ℝ) ^ (p + 1) / (p + 1)) / (m : ℝ) ^ (p + 1) = 1 / (p + 1) := by
      field_simp
    rwa [heq] at h
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have h := div_le_div_of_nonneg_right (powerSum_bounds hp m).2
      (Real.rpow_nonneg hmreal.le (p + 1))
    have heq : (m : ℝ) ^ p / (m : ℝ) ^ (p + 1) = 1 / (m : ℝ) := by
      rw [Real.rpow_add_one hmreal.ne' p]
      field_simp
    have heq' : ((m : ℝ) ^ (p + 1) / (p + 1)) / (m : ℝ) ^ (p + 1) = 1 / (p + 1) := by
      field_simp
    rwa [add_div, heq', heq] at h

lemma powerTail_bounds {q : ℝ} (hq : 1 < q) {m : ℕ} (hm : 0 < m) :
    (m : ℝ) ^ (1 - q) / (q - 1) - (m : ℝ) ^ (-q) ≤
      ∑' k : ℕ, ((k + m + 1 : ℕ) : ℝ) ^ (-q) ∧
    (∑' k : ℕ, ((k + m + 1 : ℕ) : ℝ) ^ (-q)) ≤
      (m : ℝ) ^ (1 - q) / (q - 1) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-q)) (Set.Ici (m : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hmreal.trans_le hx) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -q < -1) hmreal
  have hn : ∀ t ∈ Set.Ioi (m : ℝ), 0 ≤ t ^ (-q) :=
    fun t ht ↦ Real.rpow_nonneg (hmreal.trans ht).le _
  have hInt : ∫ x in Set.Ioi (m : ℝ), x ^ (-q) = (m : ℝ) ^ (1 - q) / (q - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -q < -1) hmreal]
    rw [show -q + 1 = 1 - q by ring, show q - 1 = -(1 - q) by ring, div_neg]
    ring
  have hs : Summable (fun k : ℕ ↦ (k : ℝ) ^ (-q)) :=
    Real.summable_nat_rpow.2 (by linarith)
  have hlo := hanti.integral_le_tsum_comp_add m hs hn
  have hhi := hanti.tsum_comp_add_le_integral m hi hn
  rw [hInt] at hlo hhi
  have hsplit : (∑' k : ℕ, ((k + m : ℕ) : ℝ) ^ (-q)) =
      (m : ℝ) ^ (-q) + ∑' k : ℕ, ((k + m + 1 : ℕ) : ℝ) ^ (-q) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ((summable_nat_add_iff m).2 hs).tsum_eq_zero_add
  rw [hsplit] at hlo
  exact ⟨by linarith, hhi⟩

lemma powerTail_normalized_tendsto {q : ℝ} (hq : 1 < q) :
    Tendsto (fun m : ℕ ↦ (∑' k : ℕ, ((k + m + 1 : ℕ) : ℝ) ^ (-q)) /
      (m : ℝ) ^ (1 - q)) atTop (𝓝 (1 / (q - 1))) := by
  have hInv : Tendsto (fun m : ℕ ↦ 1 / (m : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun m : ℕ ↦ 1 / (q - 1) - 1 / (m : ℝ))
    (h := fun _ : ℕ ↦ 1 / (q - 1))
    (by simpa using tendsto_const_nhds.sub hInv) tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have h := div_le_div_of_nonneg_right (powerTail_bounds hq hm).1
      (Real.rpow_nonneg hmreal.le (1 - q))
    have heq : (m : ℝ) ^ (-q) / (m : ℝ) ^ (1 - q) = 1 / (m : ℝ) := by
      rw [show 1 - q = -q + 1 by ring, Real.rpow_add_one hmreal.ne']
      field_simp
    have heq' : ((m : ℝ) ^ (1 - q) / (q - 1)) / (m : ℝ) ^ (1 - q) = 1 / (q - 1) := by
      field_simp
    rwa [sub_div, heq', heq] at h
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have h := div_le_div_of_nonneg_right (powerTail_bounds hq hm).2
      (Real.rpow_nonneg hmreal.le (1 - q))
    have heq : ((m : ℝ) ^ (1 - q) / (q - 1)) / (m : ℝ) ^ (1 - q) = 1 / (q - 1) := by
      field_simp
    rwa [heq] at h

end TsvdEstimation

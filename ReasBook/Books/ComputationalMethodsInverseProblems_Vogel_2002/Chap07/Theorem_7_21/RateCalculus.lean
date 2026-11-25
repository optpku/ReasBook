/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.MomentLimits
public section
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace TikhonovEstimation
namespace PowerRisk

lemma equivalent_const_mul_of_div_tendsto {f g : ℕ → ℝ} {C : ℝ}
    (hC : C ≠ 0) (h : Tendsto (fun n ↦ f n / g n) atTop (𝓝 C)) :
    f ~[atTop] (fun n ↦ C * g n) := by
  apply isEquivalent_of_tendsto_one
  have ht := h.div_const C
  simpa only [div_self hC] using! ht.congr (fun n ↦ by dsimp; ring)

lemma power_equivalence {α δ : ℕ → ℝ} {a C : ℝ}
    (ha : a ≠ 0) (hC : 0 < C) (hδ : ∀ n, 0 ≤ δ n)
    (hα : ∀ᶠ n in atTop, 0 < α n)
    (h : (fun n ↦ (α n) ^ a) ~[atTop] (fun n ↦ C * δ n)) :
    α ~[atTop] (fun n ↦ C ^ (1 / a) * (δ n) ^ (1 / a)) := by
  have hr := h.rpow (r := 1 / a) (fun n ↦ mul_nonneg hC.le (hδ n))
  have hl : (fun n ↦ ((α n) ^ a) ^ (1 / a)) =ᶠ[atTop] α := by
    filter_upwards [hα] with n hn
    rw [← Real.rpow_mul hn.le, mul_one_div_cancel ha, Real.rpow_one]
  have hright : (fun n ↦ (C * δ n) ^ (1 / a)) =ᶠ[atTop]
      (fun n ↦ C ^ (1 / a) * (δ n) ^ (1 / a)) :=
    Eventually.of_forall fun n ↦ Real.mul_rpow hC.le (hδ n)
  exact (hr.congr_left hl).congr_right hright

lemma rate_of_balance {α δ B V : ℕ → ℝ} {u v C D : ℝ}
    (ha : 1 + v - u ≠ 0) (hC : 0 < C) (hD : 0 < D)
    (hδ : ∀ n, 0 ≤ δ n) (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hα : ∀ᶠ n in atTop, 0 < α n)
    (hB : Tendsto (fun n ↦ (α n) ^ u * B n) atTop (𝓝 D))
    (hV : Tendsto (fun n ↦ (α n) ^ v * V n) atTop (𝓝 C))
    (hbalance : ∀ᶠ n in atTop, α n * B n = δ n * V n) :
    α ~[atTop] (fun n ↦ (C / D) ^ (1 / (1 + v - u)) *
      (δ n) ^ (1 / (1 + v - u))) := by
  apply power_equivalence ha (div_pos hC hD) hδ hα
  apply equivalent_const_mul_of_div_tendsto (div_pos hC hD).ne'
  have ht := hV.div hB hD.ne'
  apply ht.congr'
  filter_upwards [hα, hδpos, hbalance,
    hB.eventually (lt_mem_nhds hD)] with n hn hdn hbn hBpos
  have hBp : B n ≠ 0 := by
    intro hz
    simp [hz] at hBpos
  have hpw : α n ^ (1 + v - u) * α n ^ u = α n ^ v * α n := by
    rw [← Real.rpow_add hn, show 1 + v - u + u = v + 1 by ring,
      Real.rpow_add hn, Real.rpow_one]
  apply (div_eq_div_iff (mul_ne_zero (Real.rpow_pos_of_pos hn u).ne' hBp) hdn.ne').2
  calc
    _ = α n ^ v * (δ n * V n) := by ring
    _ = α n ^ v * (α n * B n) := by rw [hbn]
    _ = _ := by rw [← mul_assoc, ← hpw]; ring

@[expose] def logPower (a x : ℝ) : ℝ := x ^ a * (-Real.log x)

lemma logPower_tendsto_zero {α : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ logPower a (α n)) atTop (𝓝 0) := by
  have ht := (tendsto_log_mul_rpow_nhdsGT_zero ha).comp
    (tendsto_nhdsWithin_iff.2 ⟨hα, hαpos⟩)
  simpa [logPower, mul_comm] using! ht.neg

lemma log_inv_logPower_equivalent {α : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    (fun n ↦ Real.log ((logPower a (α n))⁻¹)) ~[atTop]
      (fun n ↦ a * (-Real.log (α n))) := by
  have hu := negLog_tendsto hα hαpos
  have hl : Tendsto (fun n ↦ Real.log (-Real.log (α n)) / (-Real.log (α n))) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hu
  apply equivalent_const_mul_of_div_tendsto ha.ne'
  have ht := (tendsto_const_nhds (x := a) (f := atTop)).sub hl
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [hαpos, hu.eventually (eventually_gt_atTop 0)] with n hn hun
  rw [Real.log_inv, logPower, Real.log_mul (Real.rpow_pos_of_pos hn a).ne' hun.ne',
    Real.log_rpow hn]
  field_simp [ne_of_lt (neg_pos.1 hun)]
  ring

lemma logPower_inverse_equivalent {α β : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n)
    (hβ : Tendsto β atTop (𝓝 0)) (hβpos : ∀ᶠ n in atTop, 0 < β n)
    (heq : (fun n ↦ logPower a (α n)) ~[atTop] (fun n ↦ logPower a (β n))) :
    α ~[atTop] β := by
  have hu := negLog_tendsto hα hαpos
  have hv := negLog_tendsto hβ hβpos
  have hfβ : Tendsto (fun n ↦ (logPower a (β n))⁻¹) atTop atTop := by
    apply tendsto_inv_nhdsGT_zero.comp
    apply tendsto_nhdsWithin_iff.2
    refine ⟨logPower_tendsto_zero ha hβ hβpos, ?_⟩
    filter_upwards [hβpos, hv.eventually (eventually_gt_atTop 0)] with n hn hvn
    exact mul_pos (Real.rpow_pos_of_pos hn _) hvn
  have hlogs := heq.inv.log hfβ
  have hauv := (log_inv_logPower_equivalent ha hα hαpos).symm.trans
    (hlogs.trans (log_inv_logPower_equivalent ha hβ hβpos))
  have hlogratio : Tendsto (fun n ↦ (-Real.log (β n)) / (-Real.log (α n))) atTop (𝓝 1) := by
    have hnz : ∀ᶠ n in atTop, a * (-Real.log (α n)) ≠ 0 :=
      (hu.eventually (eventually_gt_atTop 0)).mono fun n hn ↦ (mul_pos ha hn).ne'
    have ht := (isEquivalent_iff_tendsto_one hnz).1 hauv.symm
    change Tendsto (fun n ↦ (a * (-Real.log (β n))) / (a * (-Real.log (α n))))
      atTop (𝓝 1) at ht
    simpa only [mul_div_mul_left _ _ ha.ne'] using ht
  have hfratio := (isEquivalent_iff_tendsto_one
    (show ∀ᶠ n in atTop, logPower a (β n) ≠ 0 from by
      filter_upwards [hβpos, hv.eventually (eventually_gt_atTop 0)] with n hn hvn
      exact (mul_pos (Real.rpow_pos_of_pos hn _) hvn).ne')).1 heq
  have hpow : (fun n ↦ α n ^ a) ~[atTop] (fun n ↦ β n ^ a) := by
    apply isEquivalent_of_tendsto_one
    have ht := hfratio.mul hlogratio
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [hu.eventually (eventually_gt_atTop 0),
      hv.eventually (eventually_gt_atTop 0)] with n hun hvn
    dsimp [logPower]
    field_simp [ne_of_lt (neg_pos.1 hun), ne_of_lt (neg_pos.1 hvn)]
  have hratio := (isEquivalent_iff_tendsto_one
    (hβpos.mono fun n hn ↦ (Real.rpow_pos_of_pos hn a).ne')).1 hpow
  have ht := hratio.rpow_const (p := 1 / a) (Or.inl one_ne_zero)
  simp only [Real.one_rpow] at ht
  apply isEquivalent_of_tendsto_one
  apply ht.congr'
  filter_upwards [hαpos, hβpos] with n hn hmn
  change (α n ^ a / β n ^ a) ^ (1 / a) = α n / β n
  rw [← Real.div_rpow hn.le hmn.le, ← Real.rpow_mul (div_pos hn hmn).le,
    mul_one_div_cancel ha.ne', Real.rpow_one]
lemma critical_rate_of_balance {α β δ B V : ℕ → ℝ} {v C D : ℝ}
    (ha : 0 < 1 + v) (hC : 0 < C) (hD : 0 < D)
    (hδpos : ∀ᶠ n in atTop, 0 < δ n)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n)
    (hβ : Tendsto β atTop (𝓝 0)) (hβpos : ∀ᶠ n in atTop, 0 < β n)
    (hB : Tendsto (fun n ↦ B n / (-Real.log (α n))) atTop (𝓝 D))
    (hV : Tendsto (fun n ↦ (α n) ^ v * V n) atTop (𝓝 C))
    (hbalance : ∀ᶠ n in atTop, α n * B n = δ n * V n)
    (hroot : ∀ᶠ n in atTop, logPower (1 + v) (β n) = (C / D) * δ n) :
    α ~[atTop] β := by
  apply logPower_inverse_equivalent ha hα hαpos hβ hβpos
  have ht := hV.div hB hD.ne'
  have hlog := negLog_tendsto hα hαpos
  have hlim : Tendsto (fun n ↦ logPower (1 + v) (α n) / δ n) atTop (𝓝 (C / D)) := by
    apply ht.congr'
    filter_upwards [hαpos, hδpos, hbalance, hB.eventually (lt_mem_nhds hD),
      hlog.eventually (eventually_gt_atTop 0)] with n hn hdn hbn hBpos hln
    have hBn : B n ≠ 0 := by intro hz; simp [hz] at hBpos
    have hpw : α n ^ (1 + v) = α n ^ v * α n := by
      rw [show 1 + v = v + 1 by ring, Real.rpow_add hn, Real.rpow_one]
    change (α n ^ v * V n) / (B n / (-Real.log (α n))) = logPower (1 + v) (α n) / δ n
    rw [logPower, hpw]
    field_simp [hBn, hdn.ne', ne_of_lt (neg_pos.1 hln)]
    nlinarith [congrArg (fun t : ℝ ↦ (α n ^ v * Real.log (α n)) * t) hbn]
  have heq := equivalent_const_mul_of_div_tendsto (div_pos hC hD).ne' hlim
  exact heq.congr_right (hroot.mono fun n hn ↦ hn.symm)

lemma risk_normalized_tendsto {α δ B₂ B₃ V₂ V₃ : ℕ → ℝ} {r C₂ C₃ T : ℝ}
    (hα : ∀ᶠ n in atTop, 0 < α n) (hδ : ∀ᶠ n in atTop, 0 < δ n)
    (hB₃ : ∀ᶠ n in atTop, B₃ n ≠ 0)
    (hbalance : ∀ᶠ n in atTop, α n * B₃ n = δ n * V₃ n)
    (hB : Tendsto (fun n ↦ B₂ n / B₃ n) atTop (𝓝 T))
    (hV₂ : Tendsto (fun n ↦ (α n) ^ r * V₂ n) atTop (𝓝 C₂))
    (hV₃ : Tendsto (fun n ↦ (α n) ^ (r + 1) * V₃ n) atTop (𝓝 C₃)) :
    Tendsto (fun n ↦ ((α n) ^ 2 * B₂ n + δ n * V₂ n) /
      (δ n * (α n) ^ (-r))) atTop (𝓝 (C₂ + C₃ * T)) := by
  have ht := hV₂.add (hV₃.mul hB)
  apply ht.congr'
  filter_upwards [hα, hδ, hB₃, hbalance] with n hn hdn hBn hbn
  have hpw : α n ^ (r + 1) = α n ^ r * α n := by
    rw [Real.rpow_add hn, Real.rpow_one]
  rw [Real.rpow_neg hn.le r, hpw]
  field_simp [hBn, hdn.ne', (Real.rpow_pos_of_pos hn r).ne']
  nlinarith [congrArg (fun t : ℝ ↦ (α n * B₂ n) * t) hbn]

lemma bias_ratio_of_scaled_limits {α B₂ B₃ : ℕ → ℝ} {u D₂ D₃ : ℝ}
    (hα : ∀ᶠ n in atTop, 0 < α n) (hD₃ : D₃ ≠ 0)
    (h₂ : Tendsto (fun n ↦ (α n) ^ u * B₂ n) atTop (𝓝 D₂))
    (h₃ : Tendsto (fun n ↦ (α n) ^ u * B₃ n) atTop (𝓝 D₃)) :
    Tendsto (fun n ↦ B₂ n / B₃ n) atTop (𝓝 (D₂ / D₃)) := by
  have ht := h₂.div h₃ hD₃
  apply ht.congr'
  filter_upwards [hα] with n hn
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos hn u).ne'
end PowerRisk
end TikhonovEstimation

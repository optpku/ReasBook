/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.LpDual.BoundedRepresentation

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace VariationalRegularization.LpDual

/-- The signed power used to test the conjugate integrability of a density. -/
@[expose] def dualPower (q t : ℝ) : ℝ :=
  if t < 0 then -(‖t‖ ^ (q - 1)) else ‖t‖ ^ (q - 1)

lemma norm_dualPower (q t : ℝ) : ‖dualPower q t‖ = ‖t‖ ^ (q - 1) := by
  unfold dualPower
  split <;> simp only [norm_neg, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg t) _)]

lemma dualPower_mul {q : ℝ} (hq : 1 < q) (t : ℝ) :
    dualPower q t * t = ‖t‖ ^ q := by
  have h : dualPower q t * t = ‖t‖ ^ (q - 1) * ‖t‖ := by
    by_cases ht : t < 0
    · simp only [dualPower, if_pos ht, Real.norm_of_nonpos ht.le]
      ring
    · simp only [dualPower, if_neg ht, Real.norm_of_nonneg (le_of_not_gt ht)]
  rw [h]
  by_cases ht : t = 0
  · subst t
    simp [Real.zero_rpow (by linarith : q ≠ 0)]
  · have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
    calc
      _ = ‖t‖ ^ (q - 1) * ‖t‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖t‖ ^ ((q - 1) + 1) := (Real.rpow_add htpos _ _).symm
      _ = _ := by rw [sub_add_cancel]

lemma rpow_bound_of_le_mul_rpow {I C p q : ℝ} (hI : 0 ≤ I) (hC : 0 ≤ C)
    (hpq : p.HolderConjugate q) (h : I ≤ C * I ^ p⁻¹) : I ≤ C ^ q := by
  rcases eq_or_lt_of_le hI with hzero | hpos
  · rw [← hzero]
    exact Real.rpow_nonneg hC _
  have hsplit : I ^ p⁻¹ * I ^ q⁻¹ = I := by
    rw [← Real.rpow_add hpos, hpq.inv_add_inv_eq_one, Real.rpow_one]
  have hroot : I ^ q⁻¹ ≤ C := by
    nlinarith [Real.rpow_pos_of_pos hpos p⁻¹]
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hroot hpq.symm.pos.le
  rwa [← Real.rpow_mul hI, inv_mul_cancel₀ hpq.symm.ne_zero, Real.rpow_one] at hp

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (p q : ENNReal) [Fact (1 ≤ p)]

/-- The RN density of a bounded `Lp` functional lies in the conjugate space.
Only bounded measurable tests are used before this membership is established. -/
theorem density_memLp_conjugate (hp : p ≠ ∞) (hq : q ≠ ∞)
    (hpq : p.toReal.HolderConjugate q.toReal)
    (ℓ : StrongDual ℝ (Lp ℝ p μ)) {g : α → ℝ} (hgm : Measurable g) (hg : Integrable g μ)
    (hrep : ∀ s, MeasurableSet s → ℓ (indicator μ p s) = ∫ x in s, g x ∂μ) :
    MemLp g q μ := by
  classical
  have hp0 : p ≠ 0 := by intro h; simpa [h] using hpq.pos
  have hq0 : q ≠ 0 := by intro h; simpa [h] using hpq.symm.pos
  let S : ℕ → Set α := fun n ↦ {x | ‖g x‖ ≤ (n : ℝ) + 1}
  have hS : ∀ n, MeasurableSet (S n) := fun n ↦ measurableSet_le hgm.norm measurable_const
  let F : ℕ → α → ℝ := fun n ↦ (S n).indicator (fun x ↦ dualPower q.toReal (g x))
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    apply Measurable.indicator _ (hS n)
    unfold dualPower
    exact Measurable.ite (measurableSet_lt hgm measurable_const)
      (hgm.norm.pow_const _).neg (hgm.norm.pow_const _)
  have hFnorm : ∀ n x, ‖F n x‖ ≤ ((n : ℝ) + 1) ^ (q.toReal - 1) := by
    intro n x
    by_cases hx : x ∈ S n
    · change ‖(S n).indicator (fun x ↦ dualPower q.toReal (g x)) x‖ ≤ _
      rw [indicator_of_mem hx, norm_dualPower]
      exact Real.rpow_le_rpow (norm_nonneg _) hx hpq.symm.sub_one_pos.le
    · change ‖(S n).indicator (fun x ↦ dualPower q.toReal (g x)) x‖ ≤ _
      rw [indicator_of_notMem hx, norm_zero]
      exact Real.rpow_nonneg (by positivity) _
  let hFLp : ∀ n, MemLp (F n) p μ := fun n ↦
    MemLp.of_bound (hFm n).aestronglyMeasurable _ (Filter.Eventually.of_forall (hFnorm n))
  let I : ℕ → ℝ := fun n ↦ ∫ x in S n, ‖g x‖ ^ q.toReal ∂μ
  have hI0 : ∀ n, 0 ≤ I n := fun n ↦ integral_nonneg (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)
  have hprod : ∀ n, (fun x ↦ F n x * g x) = (S n).indicator (fun x ↦ ‖g x‖ ^ q.toReal) := by
    intro n
    funext x
    by_cases hx : x ∈ S n
    · simp only [F, indicator_of_mem hx, dualPower_mul hpq.symm.lt]
    · simp only [F, indicator_of_notMem hx, zero_mul]
  have hpower : ∀ n, (fun x ↦ ‖F n x‖ ^ p.toReal) =
      (S n).indicator (fun x ↦ ‖g x‖ ^ q.toReal) := by
    intro n
    funext x
    by_cases hx : x ∈ S n
    · simp only [F, indicator_of_mem hx, norm_dualPower]
      rw [← Real.rpow_mul (norm_nonneg _), hpq.symm.sub_one_mul_conj]
    · simp only [F, indicator_of_notMem hx, norm_zero, Real.zero_rpow hpq.pos.ne']
  have hnorm : ∀ n, ‖(hFLp n).toLp (F n)‖ = I n ^ p.toReal⁻¹ := by
    intro n
    rw [Lp.norm_toLp, (hFLp n).eLpNorm_eq_integral_rpow_norm hp0 hp, hpower n,
      integral_indicator (hS n), ENNReal.toReal_ofReal (Real.rpow_nonneg (hI0 n) _)]
  have hI : ∀ n, I n ≤ ‖ℓ‖ ^ q.toReal := by
    intro n
    have htest := functional_eq_integral_bounded μ p hp ℓ hg hrep (hFm n) (hFnorm n)
    rw [hprod n, integral_indicator (hS n)] at htest
    have hle : I n ≤ ‖ℓ‖ * I n ^ p.toReal⁻¹ := by
      calc
        I n = ℓ ((hFLp n).toLp (F n)) := htest.symm
        _ ≤ ‖ℓ ((hFLp n).toLp (F n))‖ := le_abs_self _
        _ ≤ ‖ℓ‖ * ‖(hFLp n).toLp (F n)‖ := ℓ.le_opNorm _
        _ = _ := by rw [hnorm n]
    exact rpow_bound_of_le_mul_rpow (hI0 n) (norm_nonneg _) hpq hle
  have hpowerInt : ∀ n, Integrable ((S n).indicator (fun x ↦ ‖g x‖ ^ q.toReal)) μ := by
    intro n
    apply (MemLp.of_bound ((hgm.norm.pow_const _).indicator (hS n)).aestronglyMeasurable
      (((n : ℝ) + 1) ^ q.toReal) _ : MemLp _ 1 μ).integrable (by rfl)
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ S n
    · rw [indicator_of_mem hx, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact Real.rpow_le_rpow (norm_nonneg _) hx hpq.symm.pos.le
    · rw [indicator_of_notMem hx, norm_zero]
      exact Real.rpow_nonneg (by positivity) _
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (‖g x‖ ^ q.toReal))
  have hν : ∀ n, ν (S n) ≤ ENNReal.ofReal (‖ℓ‖ ^ q.toReal) := by
    intro n
    change μ.withDensity _ (S n) ≤ _
    rw [withDensity_apply _ (hS n)]
    have he : (∫⁻ x in S n, ENNReal.ofReal (‖g x‖ ^ q.toReal) ∂μ) = ENNReal.ofReal (I n) := by
      exact (ofReal_integral_eq_lintegral_ofReal
        ((integrable_indicator_iff (hS n)).mp (hpowerInt n))
        (Filter.Eventually.of_forall (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _))).symm
    rw [he]
    exact ENNReal.ofReal_le_ofReal (hI n)
  have hmono : Monotone S := by
    intro n m hnm x hx
    change ‖g x‖ ≤ (n : ℝ) + 1 at hx
    change ‖g x‖ ≤ (m : ℝ) + 1
    exact hx.trans (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hcover : ⋃ n, S n = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt ‖g x‖
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change ‖g x‖ ≤ (n : ℝ) + 1
    linarith only [hn]
  have hfull : ν univ ≤ ENNReal.ofReal (‖ℓ‖ ^ q.toReal) := by
    rw [← hcover, hmono.measure_iUnion]
    exact iSup_le hν
  have hfinite : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q.toReal) ∂μ) < ∞ := by
    have h := hfull.trans_lt ENNReal.ofReal_lt_top
    simpa only [ν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h
  apply (integrable_norm_rpow_iff hgm.aestronglyMeasurable hq0 hq).mp
  refine ⟨(hgm.norm.pow_const _).aestronglyMeasurable, ?_⟩
  change (∫⁻ x, ‖‖g x‖ ^ q.toReal‖ₑ ∂μ) < ∞
  simpa only [← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hfinite

end VariationalRegularization.LpDual

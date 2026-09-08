module

public import ReasLib.Analysis.Convergence.QOrder
public import ReasLib.Optimization.BFGS.PlanarGradient.AlternatingScale.Construction

public section

namespace PlanarGradient

/-- A positive sequence whose successive logarithmic scales have ratio one cannot
satisfy an eventual power estimate of exponent strictly larger than one. -/
private theorem logRatioOneExcludesPowerBound
    (r s : ℕ → ℝ) (hrPos : ∀ j, 0 < r j) (hsPos : ∀ j, 0 < s j)
    (hrZero : Filter.Tendsto r Filter.atTop (nhds 0))
    (hlog : Filter.Tendsto
      (fun j ↦ (-Real.log (s j)) / (-Real.log (r j))) Filter.atTop (nhds 1))
    {p C : ℝ} (hp : 1 < p) (hC : 0 < C) :
    ¬ ∀ᶠ j in Filter.atTop, s j ≤ C * r j ^ p := by
  intro hbound
  let q := (1 + p) / 2
  have honeQ : 1 < q := by
    dsimp [q]
    linarith
  have hqP : q < p := by
    dsimp [q]
    linarith
  have hpq : 0 < p - q := sub_pos.mpr hqP
  -- Positivity upgrades convergence to zero to convergence from the right.
  have hrWithin : Filter.Tendsto r Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hrZero, ?_⟩
    exact Filter.Eventually.of_forall hrPos
  have hnegLog : Filter.Tendsto (fun j ↦ -Real.log (r j))
      Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def] using
      Filter.tendsto_neg_atBot_atTop.comp
        (Real.tendsto_log_nhdsGT_zero.comp hrWithin)
  have hlarge : ∀ᶠ j in Filter.atTop,
      (|Real.log C| + 1) / (p - q) ≤ -Real.log (r j) :=
    hnegLog.eventually_ge_atTop ((|Real.log C| + 1) / (p - q))
  have hratioSmall : ∀ᶠ j in Filter.atTop,
      (-Real.log (s j)) / (-Real.log (r j)) < q :=
    hlog.eventually_lt_const honeQ
  -- Taking logarithms of the power bound forces the same ratio above `q`.
  obtain ⟨j, ⟨hj, hjLarge⟩, hjSmall⟩ :=
    ((hbound.and hlarge).and hratioSmall).exists
  have hrPowPos : 0 < r j ^ p := Real.rpow_pos_of_pos (hrPos j) p
  have hlogBound : Real.log (s j) ≤ Real.log C + p * Real.log (r j) := by
    have h := Real.log_le_log (hsPos j) hj
    simpa only [Real.log_mul hC.ne' hrPowPos.ne', Real.log_rpow (hrPos j)] using h
  have hdenomPos : 0 < -Real.log (r j) := by
    have hthreshold : 0 < (|Real.log C| + 1) / (p - q) := by positivity
    exact hthreshold.trans_le hjLarge
  have habsorb : Real.log C < (p - q) * (-Real.log (r j)) := by
    have hscaled : |Real.log C| + 1 ≤ (-Real.log (r j)) * (p - q) :=
      (div_le_iff₀ hpq).mp hjLarge
    have hlogC : Real.log C < |Real.log C| + 1 := by
      linarith [le_abs_self (Real.log C)]
    nlinarith
  have hratioLarge : q < (-Real.log (s j)) / (-Real.log (r j)) := by
    rw [lt_div_iff₀ hdenomPos]
    nlinarith
  exact (not_lt_of_ge hjSmall.le hratioLarge).elim

/-- Adjacent-radius decay in an alternating-scale construction yields Q-superlinear
convergence of its gradient sequence to zero. -/
theorem IsAlternatingScale.isSuperlinear
    {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (h : IsAlternatingScale σ g δ a b) : QConvergence.IsSuperlinear g 0 := by
  -- Normalize vector convergence and adjacent errors to the stored radius laws.
  rw [QConvergence.isSuperlinear_iff_ratio]
  refine ⟨?tendsto, Filter.Eventually.of_forall h.nonzero, ?ratio⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero] using h.radiusTendsto
  · simpa only [QConvergence.error_apply, sub_zero] using h.ratioTendsto

/-- The retained odd transitions of an alternating-scale construction force its
gradient sequence to have exact Q-order one. -/
theorem IsAlternatingScale.order_eq_one
    {σ : ℝ} {g : ℕ → EuclideanSpace ℝ (Fin 2)} {δ : ℕ → ℝ} {a b : ℝ}
    (h : IsAlternatingScale σ g δ a b) : QConvergence.order g 0 = 1 := by
  rw [QConvergence.order_eq_one_iff]
  constructor
  · -- Superlinear decay supplies the admissible exponent one.
    rw [QConvergence.hasOrderAtLeast_iff]
    have hsuper := h.isSuperlinear
    rw [QConvergence.isSuperlinear_iff] at hsuper
    rcases hsuper with ⟨htendsto, hnonstationary, hlittle⟩
    obtain ⟨C, hC, hbound⟩ := (Asymptotics.isBigO_iff').mp hlittle.isBigO
    refine ⟨htendsto, hnonstationary, le_rfl, C, hC, ?_⟩
    filter_upwards [hbound] with k hk
    simpa only [Real.norm_eq_abs, abs_of_nonneg, QConvergence.error_apply,
      norm_nonneg, Real.rpow_one] using hk
  · intro p hp hpOrder
    rw [QConvergence.hasOrderAtLeast_iff] at hpOrder
    rcases hpOrder with ⟨_, _, _, C, hC, hbound⟩
    -- Restrict the hypothetical power bound to the cofinal odd indices.
    have hoddStrict : StrictMono (fun j : ℕ ↦ 2 * j + 1) := by
      refine strictMono_nat_of_lt_succ ?_
      intro j
      omega
    have hoddTop : Filter.Tendsto (fun j : ℕ ↦ 2 * j + 1)
        Filter.atTop Filter.atTop := hoddStrict.tendsto_atTop
    have hrOddZero : Filter.Tendsto (fun j ↦ ‖g (2 * j + 1)‖)
        Filter.atTop (nhds 0) := h.radiusTendsto.comp hoddTop
    have hboundOdd : ∀ᶠ j in Filter.atTop,
        ‖g (2 * j + 2)‖ ≤ C * ‖g (2 * j + 1)‖ ^ p := by
      filter_upwards [hoddTop.eventually hbound] with j hj
      have hindex : (2 * j + 1) + 1 = 2 * j + 2 := by
        omega
      simpa only [QConvergence.error_apply, sub_zero, hindex] using hj
    have hrOddPos : ∀ j, 0 < ‖g (2 * j + 1)‖ := by
      intro j
      exact norm_pos_iff.mpr (h.nonzero (2 * j + 1))
    have hsEvenPos : ∀ j, 0 < ‖g (2 * j + 2)‖ := by
      intro j
      exact norm_pos_iff.mpr (h.nonzero (2 * j + 2))
    exact logRatioOneExcludesPowerBound
      (fun j ↦ ‖g (2 * j + 1)‖) (fun j ↦ ‖g (2 * j + 2)‖)
      hrOddPos hsEvenPos hrOddZero h.oddLogRatioTendsto hp hC hboundOdd

end PlanarGradient

module

public import ReasLib.Analysis.Asymptotics.PartialSumDivergence

public section

open Filter

/-! Divergence criteria from eventual lower bounds on successive decrements. -/

/-- A real sequence that eventually decreases by nonnegative increments with a
nonsummable series tends to `atBot`. -/
theorem tendsto_atBot_of_eventually_succ_add_le_of_not_summable {u v : ℕ → ℝ}
    (hv : ∀ n, 0 ≤ v n)
    (hstep : ∀ᶠ n in atTop, u (n + 1) + v n ≤ u n)
    (hdiv : ¬ Summable v) :
    Tendsto u atTop atBot := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
  have htail_nonneg (n : ℕ) : 0 ≤ v (n + N) := hv (n + N)
  have htail_step (n : ℕ) :
      u ((n + 1) + N) + v (n + N) ≤ u (n + N) := by
    have hbound := hN (n + N) (Nat.le_add_left N n)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
  have htail_not_summable : ¬ Summable (fun n ↦ v (n + N)) := by
    intro hsummable
    exact hdiv ((summable_nat_add_iff N).mp hsummable)
  have htail_tendsto : Tendsto (fun n ↦ u (n + N)) atTop atBot :=
    tendsto_atBot_of_succ_add_le_of_not_summable
      htail_nonneg htail_step htail_not_summable
  exact (tendsto_add_atTop_iff_nat N).mp htail_tendsto

/-- If the eventual decrement of a real sequence dominates a positive multiple of a
nonnegative nonsummable sequence, then the original sequence tends to `atBot`. -/
theorem tendsto_atBot_of_eventually_le_decrement_of_not_summable {u v : ℕ → ℝ}
    {c : ℝ} (hc : 0 < c) (hv : ∀ n, 0 ≤ v n)
    (hstep : ∀ᶠ n in atTop, c * v n ≤ u n - u (n + 1))
    (hdiv : ¬ Summable v) :
    Tendsto u atTop atBot := by
  have hscaled_nonneg (n : ℕ) : 0 ≤ c * v n :=
    mul_nonneg hc.le (hv n)
  have hscaled_not_summable : ¬ Summable (fun n ↦ c * v n) := by
    intro hsummable
    exact hdiv ((summable_mul_left_iff hc.ne').mp hsummable)
  have hscaled_step : ∀ᶠ n in atTop, u (n + 1) + c * v n ≤ u n := by
    filter_upwards [hstep] with n hn
    linarith
  exact tendsto_atBot_of_eventually_succ_add_le_of_not_summable
    hscaled_nonneg hscaled_step hscaled_not_summable

/-- An eventual absolute error bound around a negative leading forward difference forces
divergence to `atBot` when the retained positive part is nonsummable. -/
theorem tendsto_atBot_of_eventually_abs_forwardDiff_add_le_of_not_summable
    {u v error : ℕ → ℝ} {a c : ℝ} (hc : 0 < c) (hv : ∀ n, 0 ≤ v n)
    (hforward : ∀ᶠ n in atTop,
      |u (n + 1) - u n + a * v n| ≤ error n)
    (herror : ∀ᶠ n in atTop, error n ≤ (a - c) * v n)
    (hdiv : ¬ Summable v) :
    Tendsto u atTop atBot := by
  apply tendsto_atBot_of_eventually_le_decrement_of_not_summable hc hv
  · filter_upwards [hforward, herror] with n hn herrorn
    have hupper : u (n + 1) - u n + a * v n ≤ error n :=
      (abs_le.mp hn).2
    linarith
  · exact hdiv

module

public import ReasLib.Analysis.Asymptotics.PartialSumDivergence.Eventual

public section

open Filter
open scoped Topology

/-! A vanishing multiplicative error can be fed into the eventual divergence criterion. -/

/-- If the error in a forward-difference estimate is bounded by `C * v n * w n`, where
`w` tends to zero, then a nonsummable nonnegative `v` still forces
the sequence to tend to `atBot`. -/
theorem tendsto_atBot_of_eventually_abs_forwardDiff_add_le_of_vanishing_factor
    {u v w : ℕ → ℝ} {a c C : ℝ} (hc : 0 < c) (hca : c < a) (hC : 0 < C)
    (hv : ∀ n, 0 ≤ v n)
    (hw_zero : Tendsto w atTop (𝓝 0))
    (hforward : ∀ᶠ n in atTop,
      |u (n + 1) - u n + a * v n| ≤ C * v n * w n)
    (hdiv : ¬ Summable v) :
    Tendsto u atTop atBot := by
  have hgap : 0 < (a - c) / C := div_pos (sub_pos.mpr hca) hC
  have hsmall : ∀ᶠ n in atTop, w n < (a - c) / C :=
    Filter.Tendsto.eventually_lt_const hgap hw_zero
  apply tendsto_atBot_of_eventually_abs_forwardDiff_add_le_of_not_summable
    hc hv hforward ?_ hdiv
  filter_upwards [hsmall] with n hn
  have hcancel : C * ((a - c) / C) = a - c := by
    field_simp [hC.ne']
  have hscaled : C * w n ≤ a - c := by
    calc
      C * w n ≤ C * ((a - c) / C) := mul_le_mul_of_nonneg_left hn.le hC.le
      _ = a - c := hcancel
  have hfactor : C * v n * w n = v n * (C * w n) := by
    ring
  have hswap : v n * (a - c) = (a - c) * v n := by
    ring
  calc
    C * v n * w n = v n * (C * w n) := hfactor
    _ ≤ v n * (a - c) := mul_le_mul_of_nonneg_left hscaled (hv n)
    _ = (a - c) * v n := hswap

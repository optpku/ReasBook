module

public import ReasLib.Analysis.Asymptotics.PartialSumDivergence.VanishingError

public section

open Filter
open scoped Topology

/-! A quadratic scale specializes the vanishing-error divergence criterion. -/

/-- A fourth-order absolute remainder around the decrement `3 * ε n ^ 2` forces a real
sequence to tend to `atBot` when `ε n` tends to zero and its square is nonsummable. -/
theorem tendsto_atBot_of_eventually_abs_forwardDiff_add_le_of_square_vanishing
    {u ε : ℕ → ℝ} {C : ℝ}
    (hC : 0 < C)
    (hε_zero : Tendsto ε atTop (𝓝 0))
    (hforward : ∀ᶠ n in atTop,
      |u (n + 1) - u n + 3 * ε n ^ 2| ≤ C * ε n ^ 4)
    (hdiv : ¬ Summable (fun n ↦ ε n ^ 2)) :
    Tendsto u atTop atBot := by
  have hεsq_zero : Tendsto (fun n ↦ ε n ^ 2) atTop (𝓝 0) := by
    simpa using hε_zero.pow 2
  have hforward' : ∀ᶠ n in atTop,
      |u (n + 1) - u n + (3 : ℝ) * (ε n ^ 2)| ≤
        C * (ε n ^ 2) * (ε n ^ 2) := by
    filter_upwards [hforward] with n hn
    simpa [pow_succ, pow_two, mul_assoc] using hn
  exact tendsto_atBot_of_eventually_abs_forwardDiff_add_le_of_vanishing_factor
    (u := u) (v := fun n ↦ ε n ^ 2) (w := fun n ↦ ε n ^ 2)
    (a := 3) (c := 1) (C := C)
    (by norm_num) (by norm_num) hC
    (fun n ↦ sq_nonneg (ε n)) hεsq_zero hforward' hdiv

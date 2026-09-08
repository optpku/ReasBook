module

public import ReasLib.Analysis.Asymptotics.ParabolicRecurrence.DecrementBounds
public import ReasLib.Analysis.Asymptotics.ParabolicRecurrence.UniformTailError

public section

open Filter
open scoped BigOperators Topology

namespace ParabolicRecurrence

/-- A family with a uniform parabolic recurrence residual has uniformly summable
shifted higher-power tails, with the bound obtained from its leading decrement. -/
theorem summable_tail_pow_and_tsum_le_of_residual
    {ι : Type*} {ε : ι → ℕ → ℝ} {p q : ℕ} {a b C η δ : ℝ}
    (hδa : δ < a) (hpq : p + 1 ≤ q) (hC : 0 ≤ C)
    (hδbound : |b| * η + C * η ^ 2 ≤ δ)
    (hpositive : ∀ i n, 0 < ε i n) (hscale : ∀ i n, ε i n ≤ η)
    (hresidual : ∀ i n,
      |ε i (n + 1) - ε i n + a * ε i n ^ (p + 1) + b * ε i n ^ (p + 2)| ≤
        C * ε i n ^ (p + 3))
    (i : ι) (j : ℕ) :
    Summable (fun k : ℕ ↦ ε i (j + k) ^ q) ∧
      (∑' k : ℕ, ε i (j + k) ^ q) ≤ (a - δ)⁻¹ * ε i j ^ (q - p) := by
  have hdecrement (i : ι) (n : ℕ) :
      (a - δ) * ε i n ^ (p + 1) ≤ ε i n - ε i (n + 1) :=
    (decrementBounds_of_residual (hpositive i n) (hscale i n) hC hδbound
      (hresidual i n)).1
  exact summable_tail_pow_and_tsum_le_of_decrement
    (sub_pos.mpr hδa) hpq hpositive hdecrement i j

/-- A uniform two-term parabolic recurrence residual gives the sharp interval for
the critical power tail when every member of the family tends to zero. -/
theorem tsum_tail_pow_interval_of_residual
    {ι : Type*} {ε : ι → ℕ → ℝ} {p : ℕ} {a b C η δ : ℝ}
    (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : δ < a) (hC : 0 ≤ C)
    (hδbound : |b| * η + C * η ^ 2 ≤ δ)
    (hpositive : ∀ i n, 0 < ε i n) (hscale : ∀ i n, ε i n ≤ η)
    (hzero : ∀ i, Tendsto (ε i) atTop (𝓝 0))
    (hresidual : ∀ i n,
      |ε i (n + 1) - ε i n + a * ε i n ^ (p + 1) + b * ε i n ^ (p + 2)| ≤
        C * ε i n ^ (p + 3))
    (i : ι) (j : ℕ) :
    ε i j / (a + δ) ≤ ∑' k : ℕ, ε i (j + k) ^ (p + 1) ∧
      (∑' k : ℕ, ε i (j + k) ^ (p + 1)) ≤ ε i j / (a - δ) := by
  have hdecrement (i : ι) (n : ℕ) :
      (a - δ) * ε i n ^ (p + 1) ≤ ε i n - ε i (n + 1) ∧
        ε i n - ε i (n + 1) ≤ (a + δ) * ε i n ^ (p + 1) :=
    decrementBounds_of_residual (hpositive i n) (hscale i n) hC hδbound
      (hresidual i n)
  exact tsum_tail_pow_interval_of_two_sided_decrement ha hδ hδa hpositive hzero
    (fun i n ↦ (hdecrement i n).1) (fun i n ↦ (hdecrement i n).2) i j

/-- A uniform two-term parabolic recurrence residual controls the critical power
tail's absolute error from its leading value `ε i j / a`. -/
theorem recurrence_tail_pow_error_of_residual
    {ι : Type*} {ε : ι → ℕ → ℝ} {p : ℕ} {a b C η δ : ℝ}
    (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : δ < a) (hC : 0 ≤ C)
    (hδbound : |b| * η + C * η ^ 2 ≤ δ)
    (hpositive : ∀ i n, 0 < ε i n) (hscale : ∀ i n, ε i n ≤ η)
    (hzero : ∀ i, Tendsto (ε i) atTop (𝓝 0))
    (hresidual : ∀ i n,
      |ε i (n + 1) - ε i n + a * ε i n ^ (p + 1) + b * ε i n ^ (p + 2)| ≤
        C * ε i n ^ (p + 3))
    (i : ι) (j : ℕ) :
    |(∑' k : ℕ, ε i (j + k) ^ (p + 1)) - ε i j / a| ≤
      (δ / (a * (a - δ))) * ε i j := by
  have hdecrement (i : ι) (n : ℕ) :
      (a - δ) * ε i n ^ (p + 1) ≤ ε i n - ε i (n + 1) ∧
        ε i n - ε i (n + 1) ≤ (a + δ) * ε i n ^ (p + 1) :=
    decrementBounds_of_residual (hpositive i n) (hscale i n) hC hδbound
      (hresidual i n)
  exact recurrence_tail_pow_error_of_two_sided_decrement ha hδ hδa hpositive hzero
    (fun i n ↦ (hdecrement i n).1) (fun i n ↦ (hdecrement i n).2) i j

end ParabolicRecurrence

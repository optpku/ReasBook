module

public import ReasLib.Analysis.Asymptotics.ParabolicRecurrence.UniformTail

public section

open Filter
open scoped BigOperators Topology

namespace ParabolicRecurrence

/-- An interval around `x / a` with positive denominators controls the absolute
error by the wider endpoint displacement. -/
theorem abs_sub_inv_mul_le_of_interval {x s a δ : ℝ} (hx : 0 ≤ x) (ha : 0 < a)
    (hδ : 0 ≤ δ) (hδa : δ < a)
    (hinterval : x / (a + δ) ≤ s ∧ s ≤ x / (a - δ)) :
    |s - x / a| ≤ (δ / (a * (a - δ))) * x := by
  have hminus : 0 < a - δ := sub_pos.mpr hδa
  have hplus : 0 < a + δ := add_pos_of_pos_of_nonneg ha hδ
  have hupperIdentity :
      x / (a - δ) - x / a = (δ / (a * (a - δ))) * x := by
    field_simp [ha.ne', hminus.ne']
    ring
  have hlowerIdentity :
      x / a - x / (a + δ) = (δ / (a * (a + δ))) * x := by
    field_simp [ha.ne', hplus.ne']
    ring
  have hdenOrder : a * (a - δ) ≤ a * (a + δ) := by
    nlinarith [ha, hδ]
  have hcoef : δ / (a * (a + δ)) ≤ δ / (a * (a - δ)) := by
    exact div_le_div_of_nonneg_left hδ (mul_pos ha hminus) hdenOrder
  have hupper : s - x / a ≤ (δ / (a * (a - δ))) * x := by
    calc
      s - x / a ≤ x / (a - δ) - x / a := sub_le_sub_right hinterval.2 _
      _ = (δ / (a * (a - δ))) * x := hupperIdentity
  have hlower : -(δ / (a * (a - δ)) * x) ≤ s - x / a := by
    have hleft : x / a - s ≤ (δ / (a * (a - δ))) * x := by
      calc
        x / a - s ≤ x / a - x / (a + δ) := sub_le_sub_left hinterval.1 _
        _ = (δ / (a * (a + δ))) * x := hlowerIdentity
        _ ≤ (δ / (a * (a - δ))) * x :=
          mul_le_mul_of_nonneg_right hcoef hx
    calc
      -(δ / (a * (a - δ)) * x) ≤ -(x / a - s) := neg_le_neg hleft
      _ = s - x / a := by ring
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Two-sided decrement bounds yield an explicit error bound for the power-tail
sum around its leading coefficient `1 / a`. -/
theorem recurrence_tail_pow_error_of_two_sided_decrement
    {ι : Type*} {ε : ι → ℕ → ℝ} {p : ℕ} {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 ≤ δ) (hδa : δ < a)
    (hpositive : ∀ i j, 0 < ε i j)
    (hzero : ∀ i, Tendsto (ε i) atTop (𝓝 0))
    (hlower : ∀ i j,
      (a - δ) * ε i j ^ (p + 1) ≤ ε i j - ε i (j + 1))
    (hupper : ∀ i j,
      ε i j - ε i (j + 1) ≤ (a + δ) * ε i j ^ (p + 1))
    (i : ι) (j : ℕ) :
    |(∑' k : ℕ, ε i (j + k) ^ (p + 1)) - ε i j / a| ≤
      (δ / (a * (a - δ))) * ε i j := by
  have hinterval := tsum_tail_pow_interval_of_two_sided_decrement
    ha hδ hδa hpositive hzero hlower hupper i j
  exact abs_sub_inv_mul_le_of_interval (x := ε i j)
    (s := ∑' k : ℕ, ε i (j + k) ^ (p + 1))
    (hpositive i j).le ha hδ hδa hinterval

end ParabolicRecurrence

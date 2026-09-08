module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

namespace ParabolicRecurrence

/-- A controlled higher-order recurrence residual bounds the error in its leading
decrement term. -/
theorem abs_decrementError_le_of_residual {p : ℕ} {x y a b C η δ : ℝ}
    (hx : 0 < x) (hxη : x ≤ η) (hC : 0 ≤ C)
    (hδ : |b| * η + C * η ^ 2 ≤ δ)
    (hres : |y - x + a * x ^ (p + 1) + b * x ^ (p + 2)| ≤ C * x ^ (p + 3)) :
    |x - y - a * x ^ (p + 1)| ≤ δ * x ^ (p + 1) := by
  have hx_nonneg : 0 ≤ x := hx.le
  have hx_sq_le : x ^ 2 ≤ η ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hx_nonneg hxη
  have hcoefficient : |b| * x + C * x ^ 2 ≤ |b| * η + C * η ^ 2 := by
    exact add_le_add (mul_le_mul_of_nonneg_left hxη (abs_nonneg b))
      (mul_le_mul_of_nonneg_left hx_sq_le hC)
  have hx_pow_two : x ^ (p + 2) = x ^ (p + 1) * x := by
    simpa only [pow_one] using pow_add x (p + 1) 1
  have hx_pow_three : x ^ (p + 3) = x ^ (p + 1) * x ^ 2 := by
    simpa only using pow_add x (p + 1) 2
  have herror_identity :
      x - y - a * x ^ (p + 1) =
        b * x ^ (p + 2) - (y - x + a * x ^ (p + 1) + b * x ^ (p + 2)) := by
    ring
  calc
    |x - y - a * x ^ (p + 1)| =
        |b * x ^ (p + 2) - (y - x + a * x ^ (p + 1) + b * x ^ (p + 2))| := by
          rw [herror_identity]
    _ ≤ |b * x ^ (p + 2)| + |y - x + a * x ^ (p + 1) + b * x ^ (p + 2)| :=
      abs_sub _ _
    _ = |b| * x ^ (p + 2) + |y - x + a * x ^ (p + 1) + b * x ^ (p + 2)| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hx_nonneg _)]
    _ ≤ |b| * x ^ (p + 2) + C * x ^ (p + 3) := add_le_add (le_refl _) hres
    _ = x ^ (p + 1) * (|b| * x + C * x ^ 2) := by
      rw [hx_pow_two, hx_pow_three]
      ring
    _ ≤ x ^ (p + 1) * (|b| * η + C * η ^ 2) :=
      mul_le_mul_of_nonneg_left hcoefficient (pow_nonneg hx_nonneg _)
    _ ≤ x ^ (p + 1) * δ :=
      mul_le_mul_of_nonneg_left hδ (pow_nonneg hx_nonneg _)
    _ = δ * x ^ (p + 1) := mul_comm _ _

/-- A controlled residual for a parabolic recurrence traps its one-step decrement
between the corresponding perturbed leading terms. -/
theorem decrementBounds_of_residual {p : ℕ} {x y a b C η δ : ℝ}
    (hx : 0 < x) (hxη : x ≤ η) (hC : 0 ≤ C)
    (hδ : |b| * η + C * η ^ 2 ≤ δ)
    (hres : |y - x + a * x ^ (p + 1) + b * x ^ (p + 2)| ≤ C * x ^ (p + 3)) :
    (a - δ) * x ^ (p + 1) ≤ x - y ∧ x - y ≤ (a + δ) * x ^ (p + 1) := by
  have herror := abs_decrementError_le_of_residual hx hxη hC hδ hres
  have hbounds := abs_le.mp herror
  constructor
  · nlinarith [hbounds.1]
  · nlinarith [hbounds.2]

end ParabolicRecurrence

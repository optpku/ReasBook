module

public import ReasLib.Analysis.PSeries

public section

open Filter
open scoped Asymptotics

namespace Asymptotics.IsEquivalent

/-- The power-scale tail asymptotic can be rewritten in terms of the original sequence rather
than its model power, so the coefficient becomes `C ^ p * (p / (q - p))`. -/
theorem tail_rpow_isEquivalent_self_via_power_scale {ε : ℕ → ℝ} {C p q : ℝ}
    (hε : ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p))) (hC : 0 < C)
    (hp : 0 < p) (hq : p < q) :
    (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ q) ~[atTop]
      (fun j : ℕ ↦ C ^ p * (p / (q - p)) * ε j ^ (q - p)) := by
  have htail := tail_rpow_isEquivalent hε hC hp hq
  have hpow := Asymptotics.IsEquivalent.rpow (r := q - p)
    (fun j ↦ mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hε
  have hcomparison :
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-1 / p)) ^ (q - p) =
        (fun j : ℕ ↦ C ^ (q - p) * (j : ℝ) ^ (1 - q / p)) := by
    funext j
    rw [Pi.pow_apply, Real.mul_rpow hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _),
      ← Real.rpow_mul (Nat.cast_nonneg j)]
    congr 2
    field_simp [hp.ne']
    ring_nf
  rw [hcomparison] at hpow
  have hscaled :=
    (IsEquivalent.refl :
      (fun _ : ℕ ↦ C ^ p * (p / (q - p))) ~[atTop]
        (fun _ : ℕ ↦ C ^ p * (p / (q - p)))).mul hpow
  have hscaled' :
      (fun j : ℕ ↦ C ^ p * (p / (q - p)) * ε j ^ (q - p)) ~[atTop]
        (fun j : ℕ ↦ C ^ q * (p / (q - p)) * (j : ℝ) ^ (1 - q / p)) := by
    refine hscaled.congr_left (Eventually.of_forall fun j ↦ ?_) |>.congr_right
      (Eventually.of_forall fun j ↦ ?_)
    · rfl
    · simp only [Pi.mul_apply]
      calc
        C ^ p * (p / (q - p)) *
              (C ^ (q - p) * (j : ℝ) ^ (1 - q / p)) =
            (C ^ p * C ^ (q - p)) * (p / (q - p)) *
              (j : ℝ) ^ (1 - q / p) := by ring_nf
        _ = C ^ q * (p / (q - p)) * (j : ℝ) ^ (1 - q / p) := by
          rw [← Real.rpow_add hC]
          ring_nf
  exact htail.trans hscaled'.symm

end Asymptotics.IsEquivalent

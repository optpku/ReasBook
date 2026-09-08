module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import Mathlib.Analysis.Real.Sqrt

public section

namespace Asymptotics.IsUniformRemainderOn

universe u

/-- Perturbing a positive real number changes its square root by at most the
absolute perturbation divided by the original square root. -/
private lemma sqrtPerturbation_le {a r : ℝ} (ha : 0 < a) :
    |√(a + r) - √a| ≤ |r| / √a := by
  have hsqrt : 0 < √a := Real.sqrt_pos.2 ha
  by_cases har : 0 ≤ a + r
  · -- Rationalize the difference when the perturbed argument is nonnegative.
    have hsum : 0 < √(a + r) + √a :=
      add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hsqrt
    have hproduct : (√(a + r) - √a) * (√(a + r) + √a) = r := by
      calc
        (√(a + r) - √a) * (√(a + r) + √a) =
            √(a + r) ^ 2 - √a ^ 2 := by ring
        _ = r := by
          rw [Real.sq_sqrt har, Real.sq_sqrt ha.le]
          ring
    have hrationalized : |√(a + r) - √a| = |r| / (√(a + r) + √a) := by
      apply (eq_div_iff hsum.ne').2
      calc
        |√(a + r) - √a| * (√(a + r) + √a) =
            |(√(a + r) - √a) * (√(a + r) + √a)| := by
              rw [abs_mul, abs_of_pos hsum]
        _ = |r| := by rw [hproduct]
    rw [hrationalized]
    exact div_le_div_of_nonneg_left (abs_nonneg r) hsqrt
      (le_add_of_nonneg_left (Real.sqrt_nonneg _))
  · -- If the perturbed argument is nonpositive, its square root vanishes and
    -- the same estimate follows from `a ≤ |r|`.
    have har' : a + r ≤ 0 := le_of_not_ge har
    have ha_abs : a ≤ |r| := by linarith [neg_le_abs r]
    rw [Real.sqrt_eq_zero_of_nonpos har', zero_sub, abs_neg, abs_of_pos hsqrt]
    apply (le_div_iff₀ hsqrt).2
    rw [← pow_two, Real.sq_sqrt ha.le]
    exact ha_abs

/-- Taking a square root around a positive real base preserves a positive-order uniform
remainder estimate. -/
theorem sqrt {Θ : Type u} {R : Θ → ℝ → ℝ} {s : Set Θ} {a C q : ℝ}
    (hR : IsUniformRemainderOn R s C q) (ha : 0 < a) (_hC : 0 ≤ C) (_hq : 0 < q) :
    IsUniformRemainderOn (fun θ ε ↦ √(a + R θ ε) - √a) s (C / √a) q := by
  -- Transport to the product filter so the original eventual estimate can be reused directly.
  refine (isBigOWith_iff (fun θ ε ↦ √(a + R θ ε) - √a) s (C / √a) q).mp ?_
  have hR' := (isBigOWith_iff R s C q).mpr hR
  refine IsBigOWith.of_bound ?_
  filter_upwards [hR'.bound] with z hz
  have hRbound : ‖R z.1 z.2‖ ≤ C * |z.2| ^ q := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg z.2) q)] using hz
  -- Apply the pointwise square-root estimate and divide the original bound by `√a`.
  calc
    ‖√(a + R z.1 z.2) - √a‖ = |√(a + R z.1 z.2) - √a| := Real.norm_eq_abs _
    _ ≤ |R z.1 z.2| / √a := sqrtPerturbation_le ha
    _ = ‖R z.1 z.2‖ / √a := by rw [Real.norm_eq_abs]
    _ ≤ (C * |z.2| ^ q) / √a :=
      div_le_div_of_nonneg_right hRbound (Real.sqrt_nonneg _)
    _ = (C / √a) * |z.2| ^ q := by ring
    _ = (C / √a) * ‖|z.2| ^ q‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg z.2) q)]

end Asymptotics.IsUniformRemainderOn

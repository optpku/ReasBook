module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

public section

open Filter
open Asymptotics
open scoped Asymptotics Topology

namespace PositiveProduct

/-- A positive real sequence with summable successive ratio perturbations converges to a
strictly positive limit. -/
private lemma existsPositiveLimitOfSummableRatioSubOne {a : ℕ → ℝ}
    (ha_pos : ∀ j, 0 < a j) (h_ratio_summable : Summable fun j ↦ a (j + 1) / a j - 1) :
    ∃ aLim : ℝ, 0 < aLim ∧ Tendsto a atTop (𝓝 aLim) := by
  -- The summable perturbations define a convergent, nonzero infinite product.
  have h_multipliable : Multipliable (fun j ↦ 1 + (a (j + 1) / a j - 1)) :=
    Real.multipliable_one_add_of_summable h_ratio_summable
  have h_tprod_ne : ∏' j, (1 + (a (j + 1) / a j - 1)) ≠ 0 := by
    apply tprod_one_add_ne_zero_of_summable
    · intro j
      have h_ratio_pos : 0 < a (j + 1) / a j := div_pos (ha_pos (j + 1)) (ha_pos j)
      nlinarith
    · exact h_ratio_summable.norm
  have h_partial_tendsto := h_multipliable.tendsto_prod_tprod_nat
  -- Finite products of successive ratios telescope to `a n / a 0`.
  have h_telescope (n : ℕ) :
      ∏ j ∈ Finset.range n, (1 + (a (j + 1) / a j - 1)) = a n / a 0 := by
    induction n with
    | zero =>
        simp only [Finset.range_zero, Finset.prod_empty]
        exact (div_self (ne_of_gt (ha_pos 0))).symm
    | succ n ih =>
        rw [Finset.prod_range_succ, ih]
        have h_factor : 1 + (a (n + 1) / a n - 1) = a (n + 1) / a n := by
          ring
        rw [h_factor]
        exact div_mul_div_cancel₀' (ne_of_gt (ha_pos n)) (a 0) (a (n + 1))
  have h_quotient_tendsto :
      Tendsto (fun n ↦ a n / a 0) atTop
        (𝓝 (∏' j, (1 + (a (j + 1) / a j - 1)))) :=
    h_partial_tendsto.congr' (Eventually.of_forall h_telescope)
  have h_tprod_nonneg : 0 ≤ ∏' j, (1 + (a (j + 1) / a j - 1)) := by
    apply ge_of_tendsto' h_partial_tendsto
    intro n
    apply Finset.prod_nonneg
    intro j _
    have h_ratio_pos : 0 < a (j + 1) / a j := div_pos (ha_pos (j + 1)) (ha_pos j)
    nlinarith
  have h_tprod_pos : 0 < ∏' j, (1 + (a (j + 1) / a j - 1)) :=
    lt_of_le_of_ne h_tprod_nonneg (Ne.symm h_tprod_ne)
  -- Multiplying the quotient limit by `a 0` recovers the original sequence.
  refine ⟨a 0 * ∏' j, (1 + (a (j + 1) / a j - 1)), mul_pos (ha_pos 0) h_tprod_pos, ?_⟩
  have h_scaled_tendsto :
      Tendsto (fun n ↦ a 0 * (a n / a 0)) atTop
        (𝓝 (a 0 * ∏' j, (1 + (a (j + 1) / a j - 1)))) :=
    tendsto_const_nhds.mul h_quotient_tendsto
  refine h_scaled_tendsto.congr' (Eventually.of_forall fun n ↦ ?_)
  field_simp [ne_of_gt (ha_pos 0)]

/-- Little-o control is preserved when one sums the tails of a summable sequence against
a nonnegative summable comparison sequence. -/
private lemma tailTsumIsLittleO {r u : ℕ → ℝ} (hu_nonneg : ∀ j, 0 ≤ u j)
    (hu : Summable u) (hr : r =o[atTop] u) :
    (fun j ↦ ∑' k : ℕ, r (j + k)) =o[atTop] (fun j ↦ ∑' k : ℕ, u (j + k)) := by
  have hr_summable : Summable r := summable_of_isBigO_nat hu hr.isBigO
  -- Apply the pointwise little-o bound uniformly beyond its eventual threshold.
  rw [isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hr.bound hε)
  refine eventually_atTop.mpr ⟨N, ?_⟩
  intro j hj
  have hu_shift : Summable (fun k ↦ u (j + k)) := by
    have hu_nat_add : Summable (fun k ↦ u (k + j)) := (summable_nat_add_iff j).mpr hu
    refine hu_nat_add.congr fun k ↦ ?_
    rw [Nat.add_comm]
  have hr_norm_shift : Summable (fun k ↦ ‖r (j + k)‖) := by
    have hr_nat_add : Summable (fun k ↦ ‖r (k + j)‖) :=
      (summable_nat_add_iff j).mpr hr_summable.norm
    refine hr_nat_add.congr fun k ↦ ?_
    rw [Nat.add_comm]
  have h_term_bound (k : ℕ) : ‖r (j + k)‖ ≤ ε * u (j + k) := by
    have h_index : N ≤ j + k := by
      omega
    have h_bound := hN (j + k) h_index
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hu_nonneg (j + k))] using h_bound
  -- Compare the norm of the tail sum termwise, then remove the norm of the nonnegative tail.
  calc
    ‖∑' k : ℕ, r (j + k)‖ ≤ ∑' k : ℕ, ‖r (j + k)‖ :=
      norm_tsum_le_tsum_norm hr_norm_shift
    _ ≤ ∑' k : ℕ, ε * u (j + k) :=
      Summable.tsum_le_tsum h_term_bound hr_norm_shift (hu_shift.mul_left ε)
    _ = ε * ∑' k : ℕ, u (j + k) := hu_shift.tsum_mul_left ε
    _ = ε * ‖∑' k : ℕ, u (j + k)‖ := by
      rw [Real.norm_of_nonneg (tsum_nonneg fun k ↦ hu_nonneg (j + k))]

/-- Multiplicative little-o control of successive ratios becomes additive little-o control
of the forward difference at the limiting value. -/
private lemma forwardDiffErrorIsLittleO {u a : ℕ → ℝ} {c aLim : ℝ}
    (ha_ne : ∀ j, a j ≠ 0) (ha_tendsto : Tendsto a atTop (𝓝 aLim))
    (h_ratio : (fun j ↦ a (j + 1) / a j - (1 - c * u j)) =o[atTop] u) :
    (fun j ↦ a (j + 1) - a j + c * aLim * u j) =o[atTop] u := by
  -- Multiplication by the convergent sequence `a` preserves the ratio remainder's order.
  have h_scaled_ratio :
      (fun j ↦ a j * (a (j + 1) / a j - (1 - c * u j))) =o[atTop] u := by
    have h_product := (ha_tendsto.isBigO_one ℝ).mul_isLittleO h_ratio
    simpa only [one_mul] using h_product
  have h_limit_difference : (fun j ↦ aLim - a j) =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa only [sub_self] using (tendsto_const_nhds (x := aLim)).sub ha_tendsto
  have h_limit_correction : (fun j ↦ c * (aLim - a j) * u j) =o[atTop] u := by
    have h_product := h_limit_difference.mul_isBigO (isBigO_refl u atTop)
    have h_unscaled : (fun j ↦ (aLim - a j) * u j) =o[atTop] u := by
      simpa only [one_mul] using h_product
    simpa only [mul_assoc] using h_unscaled.const_mul_left c
  have h_error_identity (j : ℕ) :
      a j * (a (j + 1) / a j - (1 - c * u j)) + c * (aLim - a j) * u j =
        a (j + 1) - a j + c * aLim * u j := by
    field_simp [ha_ne j]
    ring
  -- The two additive errors combine to the desired forward-difference normal form.
  exact (h_scaled_ratio.add h_limit_correction).congr'
    (Eventually.of_forall h_error_identity) EventuallyEq.rfl

/-- The tail sum of the forward differences of a convergent sequence equals its remaining
distance to the limit. -/
private lemma tailTsumForwardDiff {a : ℕ → ℝ} {aLim : ℝ}
    (h_diff : Summable fun j ↦ a (j + 1) - a j)
    (ha_tendsto : Tendsto a atTop (𝓝 aLim)) (j : ℕ) :
    ∑' k : ℕ, (a (j + k + 1) - a (j + k)) = aLim - a j := by
  -- Partial sums telescope, so convergence of `a` identifies the sum of all differences.
  have h_partial_tendsto :
      Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (a (i + 1) - a i)) atTop (𝓝 (aLim - a 0)) := by
    simpa only [Finset.sum_range_sub] using ha_tendsto.sub tendsto_const_nhds
  have h_full_sum : HasSum (fun i ↦ a (i + 1) - a i) (aLim - a 0) :=
    (h_diff.hasSum_iff_tendsto_nat).mpr h_partial_tendsto
  have h_tail_sum := (hasSum_nat_add_iff' j).mpr h_full_sum
  have h_tail_value :
      (aLim - a 0) - ∑ i ∈ Finset.range j, (a (i + 1) - a i) = aLim - a j := by
    rw [Finset.sum_range_sub]
    ring
  rw [h_tail_value] at h_tail_sum
  have h_reindex (k : ℕ) :
      a (j + k + 1) - a (j + k) = a (k + j + 1) - a (k + j) := by
    rw [Nat.add_comm k j]
  exact (h_tail_sum.congr_fun h_reindex).tsum_eq

/-- A positive sequence whose successive ratios have a summable nonnegative first-order
perturbation converges to a positive limit. -/
theorem existsLimit {u a : ℕ → ℝ} {c : ℝ}
    (_hu_nonneg : ∀ j, 0 ≤ u j) (hu : Summable u) (ha_pos : ∀ j, 0 < a j)
    (h_ratio : (fun j ↦ a (j + 1) / a j - (1 - c * u j)) =o[atTop] u) :
    ∃ aLim : ℝ, 0 < aLim ∧ Tendsto a atTop (𝓝 aLim) := by
  -- The little-o remainder is summable because the comparison series is summable.
  have h_remainder_summable :
      Summable (fun j ↦ a (j + 1) / a j - (1 - c * u j)) :=
    summable_of_isBigO_nat hu h_ratio.isBigO
  have h_ratio_summable : Summable (fun j ↦ a (j + 1) / a j - 1) := by
    refine (h_remainder_summable.sub (hu.mul_left c)).congr fun j ↦ ?_
    ring
  -- Apply the product criterion to the now-summable ratio perturbation.
  exact existsPositiveLimitOfSummableRatioSubOne ha_pos h_ratio_summable

/-- If the shifted tail of `u` is asymptotic to `v`, then the error from the positive
limit has first-order term `c * aLim * v`. -/
theorem subLimitIsLittleO {u a v : ℕ → ℝ} {c aLim : ℝ}
    (hu_nonneg : ∀ j, 0 ≤ u j) (hu : Summable u) (ha_pos : ∀ j, 0 < a j)
    (h_ratio : (fun j ↦ a (j + 1) / a j - (1 - c * u j)) =o[atTop] u)
    (ha_tendsto : Tendsto a atTop (𝓝 aLim))
    (h_tail : (fun j ↦ ∑' k : ℕ, u (j + k)) ~[atTop] v) :
    (fun j ↦ a j - aLim - c * aLim * v j) =o[atTop] v := by
  have ha_ne (j : ℕ) : a j ≠ 0 := ne_of_gt (ha_pos j)
  have h_error : (fun j ↦ a (j + 1) - a j + c * aLim * u j) =o[atTop] u :=
    forwardDiffErrorIsLittleO ha_ne ha_tendsto h_ratio
  -- Summability of the normalized error yields summability of the forward differences.
  have h_error_summable : Summable (fun j ↦ a (j + 1) - a j + c * aLim * u j) :=
    summable_of_isBigO_nat hu h_error.isBigO
  have h_diff_summable : Summable (fun j ↦ a (j + 1) - a j) := by
    refine (h_error_summable.sub (hu.mul_left (c * aLim))).congr fun j ↦ ?_
    ring
  have h_error_tail :
      (fun j ↦ ∑' k : ℕ, (a (j + k + 1) - a (j + k) + c * aLim * u (j + k)))
        =o[atTop] (fun j ↦ ∑' k : ℕ, u (j + k)) :=
    tailTsumIsLittleO hu_nonneg hu h_error
  have h_error_tail_v :
      (fun j ↦ ∑' k : ℕ, (a (j + k + 1) - a (j + k) + c * aLim * u (j + k)))
        =o[atTop] v :=
    h_error_tail.trans_isEquivalent h_tail
  have h_tail_approximation :
      (fun j ↦ c * aLim * ((∑' k : ℕ, u (j + k)) - v j)) =o[atTop] v := by
    simpa only [Pi.sub_apply, mul_assoc] using h_tail.isLittleO.const_mul_left (c * aLim)
  have h_combined :
      (fun j ↦
        -(∑' k : ℕ, (a (j + k + 1) - a (j + k) + c * aLim * u (j + k))) +
          c * aLim * ((∑' k : ℕ, u (j + k)) - v j)) =o[atTop] v :=
    h_error_tail_v.neg_left.add h_tail_approximation
  have h_tail_identity (j : ℕ) :
      a j - aLim - c * aLim * v j =
        -(∑' k : ℕ, (a (j + k + 1) - a (j + k) + c * aLim * u (j + k))) +
          c * aLim * ((∑' k : ℕ, u (j + k)) - v j) := by
    have h_diff_shift : Summable (fun k ↦ a (j + k + 1) - a (j + k)) := by
      have h_nat_add : Summable (fun k ↦ a (k + j + 1) - a (k + j)) :=
        (summable_nat_add_iff j).mpr h_diff_summable
      refine h_nat_add.congr fun k ↦ ?_
      rw [Nat.add_comm k j]
    have hu_shift : Summable (fun k ↦ u (j + k)) := by
      have hu_nat_add : Summable (fun k ↦ u (k + j)) := (summable_nat_add_iff j).mpr hu
      refine hu_nat_add.congr fun k ↦ ?_
      rw [Nat.add_comm k j]
    have h_error_term (k : ℕ) :
        a (j + k + 1) - a (j + k) + c * aLim * u (j + k) =
          (a (j + k + 1) - a (j + k)) + (c * aLim) * u (j + k) := by
      ring
    have h_error_tsum :
        ∑' k : ℕ, (a (j + k + 1) - a (j + k) + c * aLim * u (j + k)) =
          (∑' k : ℕ, (a (j + k + 1) - a (j + k))) +
            c * aLim * ∑' k : ℕ, u (j + k) := by
      calc
        ∑' k : ℕ, (a (j + k + 1) - a (j + k) + c * aLim * u (j + k)) =
            ∑' k : ℕ, ((a (j + k + 1) - a (j + k)) + (c * aLim) * u (j + k)) :=
          tsum_congr h_error_term
        _ = (∑' k : ℕ, (a (j + k + 1) - a (j + k))) +
            ∑' k : ℕ, (c * aLim) * u (j + k) :=
          Summable.tsum_add h_diff_shift (hu_shift.mul_left (c * aLim))
        _ = (∑' k : ℕ, (a (j + k + 1) - a (j + k))) +
            c * aLim * ∑' k : ℕ, u (j + k) := by
          rw [hu_shift.tsum_mul_left]
    rw [h_error_tsum, tailTsumForwardDiff h_diff_summable ha_tendsto j]
    ring
  have h_tail_identity_symm (j : ℕ) :
      -(∑' k : ℕ, (a (j + k + 1) - a (j + k) + c * aLim * u (j + k))) +
          c * aLim * ((∑' k : ℕ, u (j + k)) - v j) =
        a j - aLim - c * aLim * v j :=
    (h_tail_identity j).symm
  -- The algebraic tail identity transports the combined little-o estimate to the target.
  exact h_combined.congr' (Eventually.of_forall h_tail_identity_symm) EventuallyEq.rfl

/-- The first-order tail expansion as an asymptotic equivalence when its coefficient
`c` is nonzero. -/
theorem subLimitIsEquivalent {u a v : ℕ → ℝ} {c aLim : ℝ}
    (hu_nonneg : ∀ j, 0 ≤ u j) (hu : Summable u) (ha_pos : ∀ j, 0 < a j)
    (h_ratio : (fun j ↦ a (j + 1) / a j - (1 - c * u j)) =o[atTop] u)
    (ha_tendsto : Tendsto a atTop (𝓝 aLim))
    (h_tail : (fun j ↦ ∑' k : ℕ, u (j + k)) ~[atTop] v) (hc : c ≠ 0) :
    (fun j ↦ a j - aLim) ~[atTop] (fun j ↦ c * aLim * v j) := by
  -- Uniqueness identifies the supplied limit with the positive limit obtained above.
  obtain ⟨positiveLimit, hpositiveLimit, hpositiveLimit_tendsto⟩ :=
    existsLimit hu_nonneg hu ha_pos h_ratio
  have h_limit_eq : positiveLimit = aLim :=
    tendsto_nhds_unique hpositiveLimit_tendsto ha_tendsto
  have haLim_pos : 0 < aLim := h_limit_eq ▸ hpositiveLimit
  have h_coefficient_ne : c * aLim ≠ 0 := mul_ne_zero hc (ne_of_gt haLim_pos)
  have h_remainder :=
    subLimitIsLittleO hu_nonneg hu ha_pos h_ratio ha_tendsto h_tail
  -- Rescaling the comparison function by the nonzero leading coefficient gives equivalence.
  have h_scaled_remainder :
      (fun j ↦ a j - aLim - c * aLim * v j) =o[atTop] (fun j ↦ c * aLim * v j) := by
    simpa only [mul_assoc] using h_remainder.const_mul_right h_coefficient_ne
  have h_numerator (j : ℕ) :
      a j - aLim - c * aLim * v j =
        ((fun k ↦ a k - aLim) - fun k ↦ c * aLim * v k) j := by
    simp only [Pi.sub_apply]
  rw [IsEquivalent]
  exact h_scaled_remainder.congr' (Eventually.of_forall h_numerator) EventuallyEq.rfl

end PositiveProduct

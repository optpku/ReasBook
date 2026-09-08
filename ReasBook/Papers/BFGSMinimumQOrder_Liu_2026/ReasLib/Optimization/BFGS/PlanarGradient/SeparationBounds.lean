module

public import ReasLib.Optimization.BFGS.PlanarGradient.Recurrence
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

public section

noncomputable section

open scoped BigOperators

universe u

namespace PlanarGradient

section OrientedPlane

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Positive initial angular separation remains positive along a nonzero planar gradient
recurrence. -/
theorem angularSeparation_pos_of_recurrence (o : Orientation ℝ E (Fin 2))
    (g : ℕ → E) (δ : ℕ → ℝ) (hNonzero : ∀ k, g k ≠ 0)
    (hDistinct : ∀ k, 0 < k → g k ≠ g (k - 1))
    (hPre : ∀ k, 0 < k →
      inner ℝ (g k - g (k - 1)) (g k) =
        inner ℝ (g k) (perturbation o (g (k - 1)) (δ (k - 1))))
    (hScale : ∀ k, 0 < k → scale o (g (k - 1)) (g k) (δ k) ≠ 0)
    (hNext : ∀ k, 0 < k →
      g (k + 1) = next o (g (k - 1)) (g k) (δ k))
    (hInitial : 0 < angularSeparation o (g 0) (g 1)) :
    ∀ k, 0 < k → 0 < angularSeparation o (g (k - 1)) (g k) := by
  -- Induct on the positive recurrence index, separating the initial pair from later steps.
  intro k hk
  induction k with
  | zero =>
      simp only [lt_self_iff_false] at hk
  | succ k ih =>
      by_cases hkZero : k = 0
      · subst k
        simpa only [Nat.succ_eq_add_one, Nat.zero_add, Nat.add_sub_cancel] using hInitial
      · have hkPos : 0 < k := Nat.pos_of_ne_zero hkZero
        have hPrevious := ih hkPos
        -- The one-step identity expresses the new separation as a quotient of positive terms.
        rw [Nat.add_sub_cancel, hNext k hkPos,
          angularSeparation_next o (g (k - 1)) (g k) (δ (k - 1)) (δ k)
            (hNonzero (k - 1)) (hNonzero k) (hDistinct k hkPos) (hPre k hkPos)
            (hScale k hkPos)]
        exact div_pos
          (mul_pos (norm_pos_iff.mpr (hNonzero (k - 1))) hPrevious)
          (norm_pos_iff.mpr (sub_ne_zero_of_ne (hDistinct k hkPos)))

omit [Fact (Module.finrank ℝ E = 2)] in
/-- Scaling the difference of two normalized vectors by the first norm recovers the
corresponding difference of the original vectors. -/
private lemma normNormalizeSubNormRatioSMul (x y : E) (hx : x ≠ 0) :
    ‖NormedSpace.normalize x - (‖y‖ / ‖x‖) • NormedSpace.normalize y‖ =
      ‖y - x‖ / ‖x‖ := by
  -- The zero second vector is the unit-norm normalization identity.
  by_cases hy : y = 0
  · subst y
    simp only [norm_zero, zero_div, zero_smul, sub_zero, zero_sub, norm_neg,
      NormedSpace.norm_normalize hx]
    exact (div_self (norm_ne_zero_iff.mpr hx)).symm
  · have hxNorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hyNorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have hCoefficient : (‖y‖ / ‖x‖) * ‖y‖⁻¹ = ‖x‖⁻¹ := by
      field_simp
    -- After unfolding normalization, both vectors have the same scalar coefficient.
    rw [NormedSpace.normalize, NormedSpace.normalize, smul_smul, hCoefficient,
      ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg x), norm_sub_rev]
    rw [div_eq_mul_inv, mul_comm]

/-- Angular separation after one recurrence step is the previous separation divided by
the norm of the difference of the normalized adjacent gradients at their norm ratio. -/
theorem angularSeparation_next_eq_div_norm (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev δ : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hScale : scale o gPrev g δ ≠ 0) :
    angularSeparation o g (next o gPrev g δ) =
      angularSeparation o gPrev g /
        ‖NormedSpace.normalize gPrev -
          (‖g‖ / ‖gPrev‖) • NormedSpace.normalize g‖ := by
  have hPrevNorm : ‖gPrev‖ ≠ 0 := norm_ne_zero_iff.mpr hPrev
  have hDifferenceNorm : ‖g - gPrev‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hDistinct)
  -- Rewrite both denominators to the same secant-norm ratio, then cancel nonzero norms.
  rw [angularSeparation_next o gPrev g δPrev δ hPrev hg hDistinct hPre hScale,
    normNormalizeSubNormRatioSMul gPrev g hPrev]
  field_simp

/-- One recurrence step decreases angular separation by at most the factor
`1 + ‖g‖ / ‖gPrev‖`. -/
theorem angularSeparation_next_lower_bound (o : Orientation ℝ E (Fin 2))
    (gPrev g : E) (δPrev δ : ℝ) (hPrev : gPrev ≠ 0) (hg : g ≠ 0)
    (hDistinct : g ≠ gPrev)
    (hPre : inner ℝ (g - gPrev) g = inner ℝ g (perturbation o gPrev δPrev))
    (hScale : scale o gPrev g δ ≠ 0) :
    angularSeparation o gPrev g / (1 + ‖g‖ / ‖gPrev‖) ≤
      angularSeparation o g (next o gPrev g δ) := by
  have hRatioNonneg : 0 ≤ ‖g‖ / ‖gPrev‖ :=
    div_nonneg (norm_nonneg g) (norm_nonneg gPrev)
  have hSeparationNonneg : 0 ≤ angularSeparation o gPrev g :=
    (angularSeparation_mem_Icc o hPrev hg).1
  have hDenominatorPos :
      0 < ‖NormedSpace.normalize gPrev -
        (‖g‖ / ‖gPrev‖) • NormedSpace.normalize g‖ := by
    rw [normNormalizeSubNormRatioSMul gPrev g hPrev]
    exact div_pos
      (norm_pos_iff.mpr (sub_ne_zero_of_ne hDistinct))
      (norm_pos_iff.mpr hPrev)
  have hDenominatorBound :
      ‖NormedSpace.normalize gPrev -
          (‖g‖ / ‖gPrev‖) • NormedSpace.normalize g‖ ≤
        1 + ‖g‖ / ‖gPrev‖ := by
    calc
      ‖NormedSpace.normalize gPrev -
          (‖g‖ / ‖gPrev‖) • NormedSpace.normalize g‖ ≤
          ‖NormedSpace.normalize gPrev‖ +
            ‖(‖g‖ / ‖gPrev‖) • NormedSpace.normalize g‖ := norm_sub_le _ _
      _ = 1 + ‖g‖ / ‖gPrev‖ := by
        rw [NormedSpace.norm_normalize hPrev, norm_smul,
          NormedSpace.norm_normalize hg, mul_one, Real.norm_eq_abs,
          abs_of_nonneg hRatioNonneg]
  -- Division by the smaller positive normalized secant gives the stronger lower bound.
  rw [angularSeparation_next_eq_div_norm o gPrev g δPrev δ hPrev hg hDistinct hPre
    hScale]
  exact div_le_div_of_nonneg_left hSeparationNonneg hDenominatorPos hDenominatorBound

/-- Iteration of the one-step estimate gives a finite-product lower bound for angular
separation. -/
theorem angularSeparation_prod_lower_bound (o : Orientation ℝ E (Fin 2))
    (g : ℕ → E) (δ : ℕ → ℝ) (hNonzero : ∀ k, g k ≠ 0)
    (hDistinct : ∀ k, 0 < k → g k ≠ g (k - 1))
    (hPre : ∀ k, 0 < k →
      inner ℝ (g k - g (k - 1)) (g k) =
        inner ℝ (g k) (perturbation o (g (k - 1)) (δ (k - 1))))
    (hScale : ∀ k, 0 < k → scale o (g (k - 1)) (g k) (δ k) ≠ 0)
    (hNext : ∀ k, 0 < k →
      g (k + 1) = next o (g (k - 1)) (g k) (δ k))
    (hInitial : 0 < angularSeparation o (g 0) (g 1)) (k : ℕ) :
    angularSeparation o (g 0) (g 1) *
        ∏ i ∈ Finset.range k, (1 + ‖g (i + 1)‖ / ‖g i‖)⁻¹ ≤
      angularSeparation o (g k) (g (k + 1)) := by
  -- Accumulate the one-step estimate by induction over the finite product.
  induction k with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, mul_one, zero_add, le_refl]
  | succ k ih =>
      have hkPos : 0 < k + 1 := Nat.zero_lt_succ k
      have hFactorNonneg : 0 ≤ (1 + ‖g (k + 1)‖ / ‖g k‖)⁻¹ := by
        positivity
      have hMultiplied := mul_le_mul_of_nonneg_right ih hFactorNonneg
      have hStep :
          g (k + 2) = next o (g k) (g (k + 1)) (δ (k + 1)) := by
        simpa only [Nat.add_sub_cancel] using hNext (k + 1) hkPos
      have hPreStep :
          inner ℝ (g (k + 1) - g k) (g (k + 1)) =
            inner ℝ (g (k + 1)) (perturbation o (g k) (δ k)) := by
        simpa only [Nat.add_sub_cancel] using hPre (k + 1) hkPos
      have hDistinctStep : g (k + 1) ≠ g k := by
        simpa only [Nat.add_sub_cancel] using hDistinct (k + 1) hkPos
      have hScaleStep : scale o (g k) (g (k + 1)) (δ (k + 1)) ≠ 0 := by
        simpa only [Nat.add_sub_cancel] using hScale (k + 1) hkPos
      -- Append the new inverse factor and finish with the next recurrence inequality.
      rw [Finset.prod_range_succ]
      calc
        angularSeparation o (g 0) (g 1) *
              ((∏ i ∈ Finset.range k, (1 + ‖g (i + 1)‖ / ‖g i‖)⁻¹) *
                (1 + ‖g (k + 1)‖ / ‖g k‖)⁻¹) =
            (angularSeparation o (g 0) (g 1) *
                ∏ i ∈ Finset.range k, (1 + ‖g (i + 1)‖ / ‖g i‖)⁻¹) *
              (1 + ‖g (k + 1)‖ / ‖g k‖)⁻¹ := by ring
        _ ≤ angularSeparation o (g k) (g (k + 1)) *
              (1 + ‖g (k + 1)‖ / ‖g k‖)⁻¹ := hMultiplied
        _ = angularSeparation o (g k) (g (k + 1)) /
              (1 + ‖g (k + 1)‖ / ‖g k‖) := by
            simp only [div_eq_mul_inv]
        _ ≤ angularSeparation o (g (k + 1)) (g (k + 2)) := by
          rw [hStep]
          exact angularSeparation_next_lower_bound o (g k) (g (k + 1)) (δ k)
            (δ (k + 1)) (hNonzero k) (hNonzero (k + 1))
            hDistinctStep hPreStep hScaleStep

/-- The explicit uniform lower bound obtained from the summable norm ratios. -/
def angleLowerBound (o : Orientation ℝ E (Fin 2)) (g : ℕ → E) : ℝ :=
  angularSeparation o (g 0) (g 1) *
    Real.exp (-(∑' i : ℕ, ‖g (i + 1)‖ / ‖g i‖))

/-- The defining formula for the uniform angular lower bound. -/
theorem angleLowerBound_apply (o : Orientation ℝ E (Fin 2)) (g : ℕ → E) :
    angleLowerBound o g = angularSeparation o (g 0) (g 1) *
      Real.exp (-(∑' i : ℕ, ‖g (i + 1)‖ / ‖g i‖)) := by
  -- Expose the defining product of the initial separation and exponential tail.
  rfl

/-- The explicit angular lower bound is positive when the norm-ratio series is summable
and the initial separation is positive. -/
theorem angleLowerBound_pos (o : Orientation ℝ E (Fin 2)) (g : ℕ → E)
    (hNonzero : ∀ k, g k ≠ 0)
    (hSummable : Summable (fun i : ℕ ↦ ‖g (i + 1)‖ / ‖g i‖))
    (hInitial : 0 < angularSeparation o (g 0) (g 1)) :
    0 < angleLowerBound o g := by
  -- The exponential factor is strictly positive, independently of convergence details.
  rw [angleLowerBound_apply]
  exact mul_pos hInitial (Real.exp_pos _)

/-- The exponential of the negative sum of a nonnegative summable sequence is bounded
by every finite product of the inverse factors `1 + f i`. -/
private lemma expNegTsumLeProdInvOneAdd (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hSummable : Summable f) (n : ℕ) :
    Real.exp (-(∑' i, f i)) ≤ ∏ i ∈ Finset.range n, (1 + f i)⁻¹ := by
  have hFiniteSum : (∑ i ∈ Finset.range n, f i) ≤ ∑' i, f i :=
    hSummable.sum_le_tsum (Finset.range n) (fun i _ ↦ hf i)
  have hProductBound :
      (∏ i ∈ Finset.range n, (1 + f i)) ≤ Real.exp (∑' i, f i) := by
    calc
      (∏ i ∈ Finset.range n, (1 + f i)) ≤
          Real.exp (∑ i ∈ Finset.range n, f i) :=
        Real.prod_one_add_le_exp_sum (Finset.range n) hf
      _ ≤ Real.exp (∑' i, f i) := Real.exp_le_exp.mpr hFiniteSum
  have hFactorPos : ∀ i ∈ Finset.range n, 0 < 1 + f i := by
    intro i hi
    linarith [hf i]
  have hProductPos : 0 < ∏ i ∈ Finset.range n, (1 + f i) := by
    exact Finset.prod_pos hFactorPos
  -- Invert the positive direct-product bound and rewrite both inverses canonically.
  rw [Real.exp_neg, Finset.prod_inv_distrib]
  exact (inv_le_inv₀ (Real.exp_pos _) hProductPos).2 hProductBound

/-- The explicit positive constant uniformly bounds every angular separation in the
recurrence from below. -/
theorem angleLowerBound_le_angularSeparation (o : Orientation ℝ E (Fin 2))
    (g : ℕ → E) (δ : ℕ → ℝ) (hNonzero : ∀ k, g k ≠ 0)
    (hDistinct : ∀ k, 0 < k → g k ≠ g (k - 1))
    (hPre : ∀ k, 0 < k →
      inner ℝ (g k - g (k - 1)) (g k) =
        inner ℝ (g k) (perturbation o (g (k - 1)) (δ (k - 1))))
    (hScale : ∀ k, 0 < k → scale o (g (k - 1)) (g k) (δ k) ≠ 0)
    (hNext : ∀ k, 0 < k →
      g (k + 1) = next o (g (k - 1)) (g k) (δ k))
    (hInitial : 0 < angularSeparation o (g 0) (g 1))
    (hSummable : Summable (fun i : ℕ ↦ ‖g (i + 1)‖ / ‖g i‖)) :
    ∀ k, 0 < k →
      angleLowerBound o g ≤ angularSeparation o (g (k - 1)) (g k) := by
  intro k hk
  cases k with
  | zero =>
      simp only [lt_self_iff_false] at hk
  | succ n =>
      have hRatioNonneg : ∀ i : ℕ, 0 ≤ ‖g (i + 1)‖ / ‖g i‖ :=
        fun i ↦ div_nonneg (norm_nonneg _) (norm_nonneg _)
      have hExponential := expNegTsumLeProdInvOneAdd
        (fun i : ℕ ↦ ‖g (i + 1)‖ / ‖g i‖) hRatioNonneg hSummable n
      have hScaled := mul_le_mul_of_nonneg_left hExponential hInitial.le
      have hProduct := angularSeparation_prod_lower_bound o g δ hNonzero hDistinct hPre
        hScale hNext hInitial n
      -- Combine the analytic product bound with the accumulated recurrence estimate.
      rw [angleLowerBound_apply]
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hScaled.trans hProduct

/-- The explicit positive constant uniformly bounds the absolute tangent coefficients
in the recurrence from below. -/
theorem angleLowerBound_le_abs_tangentCoefficient (o : Orientation ℝ E (Fin 2))
    (g : ℕ → E) (δ : ℕ → ℝ) (hNonzero : ∀ k, g k ≠ 0)
    (hDistinct : ∀ k, 0 < k → g k ≠ g (k - 1))
    (hPre : ∀ k, 0 < k →
      inner ℝ (g k - g (k - 1)) (g k) =
        inner ℝ (g k) (perturbation o (g (k - 1)) (δ (k - 1))))
    (hScale : ∀ k, 0 < k → scale o (g (k - 1)) (g k) (δ k) ≠ 0)
    (hNext : ∀ k, 0 < k →
      g (k + 1) = next o (g (k - 1)) (g k) (δ k))
    (hInitial : 0 < angularSeparation o (g 0) (g 1))
    (hSummable : Summable (fun i : ℕ ↦ ‖g (i + 1)‖ / ‖g i‖)) :
    ∀ k, 0 < k → angleLowerBound o g ≤
      |tangentCoefficient o (g (k - 1)) (g k)| := by
  intro k hk
  have hSeparation := angleLowerBound_le_angularSeparation o g δ hNonzero hDistinct hPre
    hScale hNext hInitial hSummable (k + 1) (Nat.zero_lt_succ k)
  have hStep := hNext k hk
  have hCoefficient := abs_tangentCoefficient_eq_next o (g (k - 1)) (g k)
    (δ (k - 1)) (δ k) (hNonzero (k - 1)) (hNonzero k) (hDistinct k hk)
    (hPre k hk) (hScale k hk)
  -- Shift the uniform separation bound forward once and identify it with the coefficient.
  calc
    angleLowerBound o g ≤ angularSeparation o (g k) (g (k + 1)) := by
      simpa only [Nat.add_sub_cancel] using hSeparation
    _ = angularSeparation o (g k) (next o (g (k - 1)) (g k) (δ k)) := by
      rw [hStep]
    _ = |tangentCoefficient o (g (k - 1)) (g k)| := hCoefficient.symm

end OrientedPlane

end PlanarGradient

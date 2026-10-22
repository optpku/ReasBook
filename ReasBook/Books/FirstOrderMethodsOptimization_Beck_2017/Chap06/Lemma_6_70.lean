/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_11
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_69
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp)
open scoped BigOperators SoftThreshold

noncomputable section

section

variable {ι : Type*}

local notation "E" => EuclideanSpace ℝ ι

/- Lemma 6.70 is `source-facing` in the Chapter 6 proximal-operator domain. Domain sampling uses
the Chapter 6 owners `prox[...]` from Definition 6.1, the Euclidean `ℓ¹` norm `‖x‖₁` and its
soft-thresholding proximal formula from Example 6.8, and the residual/root-function pattern from
Theorem 6.36 and Example 6.38. The primitive source-facing object is the penalty
`x ↦ ρ ‖x‖₁²`, which stays on that canonical surface directly rather than through a one-off local
owner; the coordinate weights and scalar root function are derived `bridge/view` auxiliaries for
the explicit proximal formula, not competing owner abstractions. -/

/-- The coordinate weights `λ_i = [√ρ |x_i| / √μ - 2ρ]_+` appearing in the explicit proximal
formula for `x ↦ ρ ‖x‖₁²`. -/
def l1SquareProxWeight (ρ μ : ℝ) (x : E) : ι → ℝ :=
  fun i ↦ (Real.sqrt ρ * |x i| / Real.sqrt μ - 2 * ρ)⁺

-- Proof sketch: unfold `l1SquareProxWeight`; evaluation at coordinate `i` returns exactly the
-- textbook formula for `λ_i`.
/-- Evaluating `l1SquareProxWeight ρ μ x` at `i` gives the textbook coordinate formula for
`λ_i`. -/
@[simp] theorem l1SquareProxWeight_apply
    (ρ μ : ℝ) (x : E) (i : ι) :
    l1SquareProxWeight ρ μ x i = (Real.sqrt ρ * |x i| / Real.sqrt μ - 2 * ρ)⁺ :=
  rfl

/-- Helper for Lemma 6.70: the explicit proximal candidate attached to the textbook weights
`λ_i`. -/
def l1SquareProxCandidate (ρ μ : ℝ) (x : E) : E :=
  toLp 2 (fun i ↦
    (l1SquareProxWeight ρ μ x i * x i) /
      (l1SquareProxWeight ρ μ x i + 2 * ρ))

-- Proof sketch: unfold `l1SquareProxCandidate`; the `i`-th coordinate is definitionally the
-- displayed weighted ratio.
/-- Helper for Lemma 6.70: evaluating the candidate at coordinate `i` gives the textbook quotient
`λ_i x_i / (λ_i + 2 ρ)`. -/
@[simp] theorem l1SquareProxCandidate_apply
    (ρ μ : ℝ) (x : E) (i : ι) :
    l1SquareProxCandidate ρ μ x i =
      (l1SquareProxWeight ρ μ x i * x i) /
        (l1SquareProxWeight ρ μ x i + 2 * ρ) :=
  rfl

/-- Helper for Lemma 6.70: the magnitude of scalar soft-thresholding is the positive part of the
excess absolute value when the threshold is nonnegative. -/
theorem abs_soft_thresholding_eq_posPart_sub_real
    {τ t : ℝ} (hτ : 0 ≤ τ) :
    |𝒯[τ] t| = max (|t| - τ) 0 := by
  let τNN : NNReal := ⟨τ, hτ⟩
  change |𝒯[(τNN : ℝ)] t| = max (|t| - (τNN : ℝ)) 0
  by_cases ht : t = 0
  · simp [ht, soft_thresholding_apply]
  · have hsign :
      (((SignType.sign t : SignType) : ℝ)) = Real.sign t := by
      obtain hneg | hpos := lt_or_gt_of_ne ht
      · simp [Real.sign_of_neg hneg, SignType.sign, hneg, not_lt.mpr hneg.le]
      · simp [Real.sign_of_pos hpos, SignType.sign, hpos]
    have habs_sign : |Real.sign t| = 1 := by
      obtain hneg | hpos := lt_or_gt_of_ne ht
      · simp [Real.sign_of_neg hneg]
      · simp [Real.sign_of_pos hpos]
    calc
      |𝒯[(τNN : ℝ)] t| = |(|t| - (τNN : ℝ))⁺ * (((SignType.sign t : SignType) : ℝ))| := by
        simp [soft_thresholding_apply]
      _ = |(|t| - (τNN : ℝ))⁺| * |(((SignType.sign t : SignType) : ℝ))| := by
        rw [abs_mul]
      _ = (|t| - (τNN : ℝ))⁺ := by
        rw [hsign, habs_sign, mul_one, abs_of_nonneg (posPart_nonneg _)]
      _ = max (|t| - (τNN : ℝ)) 0 := rfl

/-- Helper for Lemma 6.70: scalar soft-thresholding supports the absolute-value penalty with
slope `τ`. -/
theorem soft_thresholding_support_bound_real
    {τ : ℝ} (hτ : 0 ≤ τ) (x t : ℝ) :
    (x - 𝒯[τ] x) * (t - 𝒯[τ] x) ≤ τ * (|t| - |𝒯[τ] x|) := by
  by_cases hτx : τ ≤ x
  · rw [soft_thresholding_eq_piecewise hτ x, if_pos hτx]
    have hsoft_nonneg : 0 ≤ x - τ := sub_nonneg.mpr hτx
    have hsoft_abs : |x - τ| = x - τ := abs_of_nonneg hsoft_nonneg
    have hbound : t - (x - τ) ≤ |t| - |x - τ| := by
      rw [hsoft_abs]
      linarith [le_abs_self t]
    nlinarith
  · by_cases habs : |x| < τ
    · rw [soft_thresholding_eq_piecewise hτ x, if_neg hτx, if_pos habs]
      have hbound : x * t ≤ τ * |t| := by
        calc
          x * t ≤ |x * t| := le_abs_self _
          _ = |x| * |t| := by rw [abs_mul]
          _ ≤ τ * |t| := by
            gcongr
      simpa using hbound
    · rw [soft_thresholding_eq_piecewise hτ x, if_neg hτx, if_neg habs]
      have hxneg : x < 0 := by
        by_contra hxnonneg
        exact hτx (by simpa [abs_of_nonneg (le_of_not_gt hxnonneg)] using le_of_not_gt habs)
      have hsoft_nonpos : x + τ ≤ 0 := by
        have hτabs : τ ≤ |x| := le_of_not_gt habs
        rw [abs_of_neg hxneg] at hτabs
        linarith
      have hsoft_abs : |x + τ| = -(x + τ) := abs_of_nonpos hsoft_nonpos
      have hbound : -(t - (x + τ)) ≤ |t| - |x + τ| := by
        rw [hsoft_abs]
        linarith [neg_le_abs t]
      nlinarith

/-- Helper for Lemma 6.70: each textbook weight is the positive part of the excess absolute value
scaled by `√ρ / √μ`. -/
theorem l1SquareProxWeight_eq_scaled_posPart
    {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (x : E) (i : ι) :
    l1SquareProxWeight ρ μ x i =
      (Real.sqrt ρ / Real.sqrt μ) *
        (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ)⁺ := by
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hfactor_nonneg : 0 ≤ Real.sqrt ρ / Real.sqrt μ := div_nonneg hsρ.le hsμ.le
  have hrewrite :
      Real.sqrt ρ * |x i| / Real.sqrt μ - 2 * ρ =
        (Real.sqrt ρ / Real.sqrt μ) *
          (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ) := by
    have hmul_eq :
        (Real.sqrt ρ / Real.sqrt μ) * (2 * Real.sqrt ρ * Real.sqrt μ) = 2 * ρ := by
      field_simp [hsρ.ne', hsμ.ne']
      nlinarith [Real.sq_sqrt hρ.le]
    calc
      Real.sqrt ρ * |x i| / Real.sqrt μ - 2 * ρ
          = (Real.sqrt ρ / Real.sqrt μ) * |x i| - 2 * ρ := by
              field_simp [hsμ.ne']
      _ = (Real.sqrt ρ / Real.sqrt μ) * |x i| -
            (Real.sqrt ρ / Real.sqrt μ) * (2 * Real.sqrt ρ * Real.sqrt μ) := by
              rw [hmul_eq]
      _ = (Real.sqrt ρ / Real.sqrt μ) *
            (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ) := by
              ring
  rw [l1SquareProxWeight_apply, hrewrite]
  by_cases hnonpos : |x i| - 2 * Real.sqrt ρ * Real.sqrt μ ≤ 0
  · have hmul_nonpos :
        (Real.sqrt ρ / Real.sqrt μ) *
            (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hfactor_nonneg hnonpos
    simp [posPart_of_nonpos hnonpos, posPart_of_nonpos hmul_nonpos]
  · have hpos : 0 < |x i| - 2 * Real.sqrt ρ * Real.sqrt μ := lt_of_not_ge hnonpos
    have hmul_nonneg :
        0 ≤ (Real.sqrt ρ / Real.sqrt μ) *
            (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ) := by
      exact mul_nonneg hfactor_nonneg hpos.le
    simp [posPart_of_nonneg hpos.le, posPart_of_nonneg hmul_nonneg]

/-- Helper for Lemma 6.70: the explicit quotient candidate is exactly the soft-thresholded point
with threshold `2 √ρ √μ`. -/
theorem l1SquareProxCandidate_eq_softThreshold
    {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (x : E) :
    l1SquareProxCandidate ρ μ x = T_[2 * Real.sqrt ρ * Real.sqrt μ] x := by
  ext i
  let τ : ℝ := 2 * Real.sqrt ρ * Real.sqrt μ
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hsμ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hτ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    positivity
  have hweight :
      l1SquareProxWeight ρ μ x i =
        (Real.sqrt ρ / Real.sqrt μ) * (|x i| - τ)⁺ := by
    simpa [τ] using l1SquareProxWeight_eq_scaled_posPart hρ hμ x i
  rw [l1SquareProxCandidate_apply, softThreshold_apply]
  by_cases hsub : |x i| - τ ≤ 0
  · have hweight_zero : l1SquareProxWeight ρ μ x i = 0 := by
      rw [hweight]
      simp [hsub]
    rw [hweight_zero, soft_thresholding_apply]
    simp [τ, hsub]
  · have hsub_pos : 0 < |x i| - τ := lt_of_not_ge hsub
    have hweight_eq :
        l1SquareProxWeight ρ μ x i =
          (Real.sqrt ρ / Real.sqrt μ) * (|x i| - τ) := by
      rw [hweight, posPart_of_nonneg hsub_pos.le]
    by_cases hxnonneg : 0 ≤ x i
    · have hτx : τ ≤ x i := by
        simpa [abs_of_nonneg hxnonneg] using hsub_pos.le
      have hxpos : 0 < x i := lt_of_lt_of_le (by
        dsimp [τ]
        positivity) hτx
      have hc_ne : Real.sqrt ρ / Real.sqrt μ ≠ 0 := div_ne_zero hsρ.ne' hsμ.ne'
      have hweight_eq' :
          l1SquareProxWeight ρ μ x i =
            (Real.sqrt ρ / Real.sqrt μ) * (x i - τ) := by
        simpa [abs_of_nonneg hxnonneg] using hweight_eq
      have hden_eq' :
          l1SquareProxWeight ρ μ x i + 2 * ρ =
            (Real.sqrt ρ / Real.sqrt μ) * x i := by
        rw [hweight_eq']
        dsimp [τ]
        field_simp [hsρ.ne', hsμ.ne']
        nlinarith [Real.sq_sqrt hρ.le]
      have hden_calc :
          (Real.sqrt ρ / Real.sqrt μ) * (x i - τ) + 2 * ρ =
            (Real.sqrt ρ / Real.sqrt μ) * x i := by
        nlinarith [hweight_eq', hden_eq']
      have hsoft : 𝒯[τ] (x i) = x i - τ := by
        simpa [hτx] using (soft_thresholding_eq_piecewise hτ_nonneg (x i))
      rw [hsoft]
      calc
        l1SquareProxWeight ρ μ x i * x i / (l1SquareProxWeight ρ μ x i + 2 * ρ)
            = ((Real.sqrt ρ / Real.sqrt μ) * (x i - τ) * x i) /
                ((Real.sqrt ρ / Real.sqrt μ) * x i) := by
                  rw [hweight_eq', hden_calc]
        _ = x i - τ := by
              field_simp [hc_ne, hxpos.ne']
    · have hxneg : x i < 0 := lt_of_not_ge hxnonneg
      have hτabs : τ ≤ |x i| := by linarith
      have hnotabs : ¬ |x i| < τ := not_lt.mpr hτabs
      have hc_ne : Real.sqrt ρ / Real.sqrt μ ≠ 0 := div_ne_zero hsρ.ne' hsμ.ne'
      have hweight_eq' :
          l1SquareProxWeight ρ μ x i =
            (Real.sqrt ρ / Real.sqrt μ) * (-x i - τ) := by
        simpa [abs_of_neg hxneg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using hweight_eq
      have hden_eq' :
          l1SquareProxWeight ρ μ x i + 2 * ρ =
            (Real.sqrt ρ / Real.sqrt μ) * (-x i) := by
        rw [hweight_eq']
        dsimp [τ]
        field_simp [hsρ.ne', hsμ.ne']
        nlinarith [Real.sq_sqrt hρ.le]
      have hden_calc :
          (Real.sqrt ρ / Real.sqrt μ) * (-x i - τ) + 2 * ρ =
            (Real.sqrt ρ / Real.sqrt μ) * (-x i) := by
        nlinarith [hweight_eq', hden_eq']
      have hsoft : 𝒯[τ] (x i) = x i + τ := by
        have hτ_not_le : ¬ τ ≤ x i := by
          intro hle
          linarith
        have hsoft_piece := soft_thresholding_eq_piecewise hτ_nonneg (x i)
        simpa [soft_thresholding_apply, hτ_not_le, hnotabs] using hsoft_piece
      rw [hsoft]
      have hxne : x i ≠ 0 := ne_of_lt hxneg
      calc
        l1SquareProxWeight ρ μ x i * x i / (l1SquareProxWeight ρ μ x i + 2 * ρ)
            = ((Real.sqrt ρ / Real.sqrt μ) * (-x i - τ) * x i) /
                ((Real.sqrt ρ / Real.sqrt μ) * (-x i)) := by
                  rw [hweight_eq', hden_calc]
        _ = x i + τ := by
              field_simp [hc_ne, hxne]
              ring

section

variable [Fintype ι]

/-- The scalar root function
`ψ(μ) = ∑ i [√ρ |x_i| / √μ - 2ρ]_+ - 1` governing the prox of `x ↦ ρ ‖x‖₁²`. -/
def l1SquareProxRootFunction (ρ : ℝ) (x : E) : ℝ → ℝ :=
  fun μ ↦ ∑ i, l1SquareProxWeight ρ μ x i - 1

-- Proof sketch: unfold `l1SquareProxRootFunction`; the right-hand side is exactly the defining
-- sum formula for `ψ`.
/-- Evaluating `l1SquareProxRootFunction ρ x` at `μ` gives the sum formula
`ψ(μ) = ∑ i λ_i - 1`. -/
@[simp] theorem l1SquareProxRootFunction_apply
    (ρ : ℝ) (x : E) (μ : ℝ) :
    l1SquareProxRootFunction ρ x μ = ∑ i, l1SquareProxWeight ρ μ x i - 1 :=
  rfl

section

omit [Fintype ι]

/-- Helper for Lemma 6.70: each textbook weight is nonnegative because it is a positive part. -/
theorem l1SquareProxWeight_nonneg
    (ρ μ : ℝ) (x : E) (i : ι) :
    0 ≤ l1SquareProxWeight ρ μ x i := by
  -- The coordinate weight is literally a positive-part value.
  simpa [l1SquareProxWeight] using
    (posPart_nonneg (Real.sqrt ρ * |x i| / Real.sqrt μ - 2 * ρ))

-- Proof sketch: the inner affine term is antitone in `μ` on `(0,∞)` because `μ ↦ 1 / √μ`
-- decreases there. Applying monotonicity of the positive-part operation preserves the
-- coordinatewise order.
/-- Helper for Lemma 6.70: on `(0, ∞)`, each coordinate weight
`μ ↦ [√ρ |x_i| / √μ - 2ρ]_+` is nonincreasing. -/
theorem l1SquareProxWeight_coordinate_antitoneOn_pos
    (ρ : ℝ) (x : E) (i : ι) :
    AntitoneOn (fun μ ↦ l1SquareProxWeight ρ μ x i) (Set.Ioi 0) := by
  intro μ₁ hμ₁ μ₂ hμ₂ hle
  have hsqrt : Real.sqrt μ₁ ≤ Real.sqrt μ₂ :=
    Real.sqrt_monotone hle
  have hcoeff_nonneg : 0 ≤ Real.sqrt ρ * |x i| := by
    exact mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hdiv :
      Real.sqrt ρ * |x i| / Real.sqrt μ₂ ≤
        Real.sqrt ρ * |x i| / Real.sqrt μ₁ := by
    exact div_le_div_of_nonneg_left hcoeff_nonneg (Real.sqrt_pos.mpr hμ₁) hsqrt
  have hinside :
      Real.sqrt ρ * |x i| / Real.sqrt μ₂ - 2 * ρ ≤
        Real.sqrt ρ * |x i| / Real.sqrt μ₁ - 2 * ρ := by
    linarith
  -- The positive-part map is monotone, so the coordinate weights inherit this order.
  exact posPart_mono hinside

end

-- Proof sketch: for each coordinate `i`, the map
-- `μ ↦ (Real.sqrt ρ * |x i| / Real.sqrt μ - 2 * ρ)⁺` is nonincreasing on `(0, ∞)` because
-- `μ ↦ 1 / Real.sqrt μ` is nonincreasing there. Finite sums of nonincreasing functions remain
-- nonincreasing, and subtracting `1` does not change monotonicity.
/-- On `(0, ∞)`, the root function
`μ ↦ ∑ i [√ρ |x_i| / √μ - 2ρ]_+ - 1` is nonincreasing. -/
theorem l1SquareProxRootFunction_antitoneOn_pos
    (ρ : ℝ) (x : E) :
    AntitoneOn (l1SquareProxRootFunction ρ x) (Set.Ioi 0) := by
  intro μ₁ hμ₁ μ₂ hμ₂ hle
  have hsum :
      ∑ i, l1SquareProxWeight ρ μ₂ x i ≤
        ∑ i, l1SquareProxWeight ρ μ₁ x i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact l1SquareProxWeight_coordinate_antitoneOn_pos ρ x i hμ₁ hμ₂ hle
  -- Subtracting the same constant from both sums preserves the order.
  rw [l1SquareProxRootFunction_apply, l1SquareProxRootFunction_apply]
  linarith

/-- Helper for Lemma 6.70: a vanishing root value is exactly the simplex normalization
`∑ i λ_i = 1`. -/
theorem l1SquareProxWeight_sum_eq_one_of_root
    (ρ μ : ℝ) (x : E)
    (hroot : l1SquareProxRootFunction ρ x μ = 0) :
    ∑ i, l1SquareProxWeight ρ μ x i = 1 := by
  -- The root equation is the displayed sum formula with the trailing `- 1` set to zero.
  rw [l1SquareProxRootFunction_apply] at hroot
  linarith

section

omit [Fintype ι]

/-- Helper for Lemma 6.70: when the textbook weight on coordinate `i` vanishes, the corresponding
coordinate lies below the active threshold `2 √ρ √μ`. -/
theorem l1SquareProxWeight_eq_zero_implies_abs_le_threshold
    {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (x : E) (i : ι)
    (hzero : l1SquareProxWeight ρ μ x i = 0) :
    |x i| ≤ 2 * Real.sqrt ρ * Real.sqrt μ := by
  have hscale_ne : Real.sqrt ρ / Real.sqrt μ ≠ 0 := by
    exact div_ne_zero (Real.sqrt_ne_zero'.2 hρ) (Real.sqrt_ne_zero'.2 hμ)
  have hpp :
      (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ)⁺ = 0 := by
    rw [l1SquareProxWeight_eq_scaled_posPart hρ hμ x i] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hscale_ne
  have hle : |x i| - 2 * Real.sqrt ρ * Real.sqrt μ ≤ 0 := (posPart_eq_zero.mp hpp)
  linarith

/-- Helper for Lemma 6.70: on an active coordinate, the candidate magnitude is the weight scaled
by `√μ / √ρ`. -/
theorem l1SquareProxCandidate_abs_eq_weight_scale
    {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (x : E) :
    ∀ i, |l1SquareProxCandidate ρ μ x i| =
      (Real.sqrt μ / Real.sqrt ρ) * l1SquareProxWeight ρ μ x i := by
  intro i
  have hτ_nonneg : 0 ≤ 2 * Real.sqrt ρ * Real.sqrt μ := by
    positivity
  calc
    |l1SquareProxCandidate ρ μ x i|
        = |𝒯[2 * Real.sqrt ρ * Real.sqrt μ] (x i)| := by
            rw [l1SquareProxCandidate_eq_softThreshold hρ hμ x, softThreshold_apply]
    _ = max (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ) 0 := by
          exact abs_soft_thresholding_eq_posPart_sub_real hτ_nonneg
    _ = (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ)⁺ := rfl
    _ = ((Real.sqrt μ / Real.sqrt ρ) * (Real.sqrt ρ / Real.sqrt μ)) *
          (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ)⁺ := by
            field_simp [Real.sqrt_ne_zero'.2 hρ, Real.sqrt_ne_zero'.2 hμ]
    _ = (Real.sqrt μ / Real.sqrt ρ) *
          ((Real.sqrt ρ / Real.sqrt μ) *
            (|x i| - 2 * Real.sqrt ρ * Real.sqrt μ)⁺) := by
              ring
    _ = (Real.sqrt μ / Real.sqrt ρ) * l1SquareProxWeight ρ μ x i := by
          rw [l1SquareProxWeight_eq_scaled_posPart hρ hμ x i]

end

/-- Helper for Lemma 6.70: the root equation normalizes the candidate so that its `ℓ¹` norm is
`√μ / √ρ`. -/
theorem l1SquareProxCandidate_l1Norm_eq_root_scale
    {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (x : E)
    (hroot : l1SquareProxRootFunction ρ x μ = 0) :
    ‖l1SquareProxCandidate ρ μ x‖₁ = Real.sqrt μ / Real.sqrt ρ := by
  rw [EuclideanSpace.l1Norm_eq_sum_abs]
  calc
    ∑ i, |l1SquareProxCandidate ρ μ x i|
        = ∑ i, (Real.sqrt μ / Real.sqrt ρ) * l1SquareProxWeight ρ μ x i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact l1SquareProxCandidate_abs_eq_weight_scale hρ hμ x i
    _ = (Real.sqrt μ / Real.sqrt ρ) * ∑ i, l1SquareProxWeight ρ μ x i := by
          rw [← Finset.mul_sum]
    _ = (Real.sqrt μ / Real.sqrt ρ) * 1 := by
          rw [l1SquareProxWeight_sum_eq_one_of_root ρ μ x hroot]
    _ = Real.sqrt μ / Real.sqrt ρ := by ring

section

omit [Fintype ι]

/-- Helper for Lemma 6.70: on an active coordinate, the residual `x_i - u_i` is exactly the
threshold `2 √ρ √μ` times the coordinate sign. -/
theorem l1SquareProxCandidate_sub_eq_threshold_mul_sign_of_weight_pos
    {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (x : E) (i : ι)
    (hpos : 0 < l1SquareProxWeight ρ μ x i) :
    x i - l1SquareProxCandidate ρ μ x i =
      (2 * Real.sqrt ρ * Real.sqrt μ) * Real.sign (x i) := by
  let τ : ℝ := 2 * Real.sqrt ρ * Real.sqrt μ
  have hτ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    positivity
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    positivity
  have hsoft : l1SquareProxCandidate ρ μ x i = 𝒯[τ] (x i) := by
    simpa [τ] using congrArg (fun z : E ↦ z i) (l1SquareProxCandidate_eq_softThreshold hρ hμ x)
  have hpp_ne :
      (|x i| - τ)⁺ ≠ 0 := by
    intro hpp
    rw [l1SquareProxWeight_eq_scaled_posPart hρ hμ x i, hpp, mul_zero] at hpos
    exact hpos.ne' rfl
  have hsub_pos : 0 < |x i| - τ := by
    by_contra hnot
    exact hpp_ne (posPart_of_nonpos (not_lt.mp hnot))
  by_cases hxnonneg : 0 ≤ x i
  · have hτx : τ ≤ x i := by
      simpa [abs_of_nonneg hxnonneg] using hsub_pos.le
    have hxpos : 0 < x i := lt_of_lt_of_le hτ_pos hτx
    have hsoft_eq : 𝒯[τ] (x i) = x i - τ := by
      simpa [hτx] using (soft_thresholding_eq_piecewise hτ_nonneg (x i))
    rw [hsoft, hsoft_eq]
    simp [Real.sign_of_pos hxpos, τ]
  · have hxneg : x i < 0 := lt_of_not_ge hxnonneg
    have hτ_not_le : ¬ τ ≤ x i := by
      intro hle
      linarith
    have hnotabs : ¬ |x i| < τ := not_lt.mpr (by linarith)
    have hsoft_eq : 𝒯[τ] (x i) = x i + τ := by
      simpa [soft_thresholding_apply, hτ_not_le, hnotabs] using
        (soft_thresholding_eq_piecewise hτ_nonneg (x i))
    rw [hsoft, hsoft_eq]
    simp [Real.sign_of_neg hxneg, τ]

/-- Helper for Lemma 6.70: the candidate satisfies the coordinatewise support inequality needed
for the proximal objective gap estimate. -/
theorem l1SquareProxCandidate_coordinate_support_bound
    {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (x : E) (i : ι) (t : ℝ) :
    (x i - l1SquareProxCandidate ρ μ x i) * (t - l1SquareProxCandidate ρ μ x i) ≤
      (2 * Real.sqrt ρ * Real.sqrt μ) *
        (|t| - |l1SquareProxCandidate ρ μ x i|) := by
  have hτ_nonneg : 0 ≤ 2 * Real.sqrt ρ * Real.sqrt μ := by
    positivity
  rw [l1SquareProxCandidate_eq_softThreshold hρ hμ x, softThreshold_apply]
  simpa using
    soft_thresholding_support_bound_real hτ_nonneg (x i) t

end

/-- Helper for Lemma 6.70: the active-branch candidate satisfies the real support inequality for
the squared `ℓ¹` penalty. -/
theorem l1SquareProxCandidate_support_bound
    {ρ μ : ℝ} (hρ : 0 < ρ) (hμ : 0 < μ) (x y : E)
    (hroot : l1SquareProxRootFunction ρ x μ = 0) :
    inner ℝ (x - l1SquareProxCandidate ρ μ x) (y - l1SquareProxCandidate ρ μ x) ≤
      ρ * ‖y‖₁ ^ (2 : ℕ) -
        ρ * ‖l1SquareProxCandidate ρ μ x‖₁ ^ (2 : ℕ) := by
  let u : E := l1SquareProxCandidate ρ μ x
  have hcoord :
      ∑ i, (x i - u i) * (y i - u i) ≤
        ∑ i, (2 * Real.sqrt ρ * Real.sqrt μ) * (|y i| - |u i|) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa [u] using l1SquareProxCandidate_coordinate_support_bound hρ hμ x i (y i)
  have hinner :
      inner ℝ (x - u) (y - u) = ∑ i, (x i - u i) * (y i - u i) := by
    simpa [u, dotProduct, mul_comm] using
      EuclideanSpace.inner_toLp_toLp ((x - u).ofLp) ((y - u).ofLp)
  have hsum_eq :
      ∑ i, (2 * Real.sqrt ρ * Real.sqrt μ) * (|y i| - |u i|) =
        (2 * Real.sqrt ρ * Real.sqrt μ) * (‖y‖₁ - ‖u‖₁) := by
    calc
      ∑ i, (2 * Real.sqrt ρ * Real.sqrt μ) * (|y i| - |u i|)
          = (2 * Real.sqrt ρ * Real.sqrt μ) * ∑ i, (|y i| - |u i|) := by
              simpa using
                (Finset.mul_sum Finset.univ
                  (fun i : ι ↦ |y i| - |u i|)
                  (2 * Real.sqrt ρ * Real.sqrt μ)).symm
      _ = (2 * Real.sqrt ρ * Real.sqrt μ) * (‖y‖₁ - ‖u‖₁) := by
            rw [Finset.sum_sub_distrib,
              ← EuclideanSpace.l1Norm_eq_sum_abs, ← EuclideanSpace.l1Norm_eq_sum_abs]
  have hu_norm : ‖u‖₁ = Real.sqrt μ / Real.sqrt ρ := by
    simpa [u] using l1SquareProxCandidate_l1Norm_eq_root_scale hρ hμ x hroot
  have hscale :
      2 * Real.sqrt ρ * Real.sqrt μ = 2 * ρ * ‖u‖₁ := by
    rw [hu_norm]
    field_simp [Real.sqrt_ne_zero'.2 hρ, Real.sqrt_ne_zero'.2 hμ]
    rw [Real.sq_sqrt hρ.le]
  calc
    inner ℝ (x - l1SquareProxCandidate ρ μ x) (y - l1SquareProxCandidate ρ μ x)
        = ∑ i, (x i - u i) * (y i - u i) := by simpa [u] using hinner
    _ ≤ ∑ i, (2 * Real.sqrt ρ * Real.sqrt μ) * (|y i| - |u i|) := hcoord
    _ = (2 * Real.sqrt ρ * Real.sqrt μ) * (‖y‖₁ - ‖u‖₁) := hsum_eq
    _ = 2 * ρ * ‖u‖₁ * (‖y‖₁ - ‖u‖₁) := by rw [hscale]
    _ ≤ ρ * ‖y‖₁ ^ (2 : ℕ) - ρ * ‖u‖₁ ^ (2 : ℕ) := by
          nlinarith [sq_nonneg (‖y‖₁ - ‖u‖₁)]

-- Proof sketch: if `x = 0`, the proximal objective
-- `u ↦ ρ ‖u‖₁² + (1 / 2) ‖u - x‖₂²` is minimized at `u = 0`. If `x ≠ 0`, use the variational
-- simplex representation of `‖x‖₁²`, minimize first in `u`, and solve the simplex dual problem.
-- The hypothesis supplies a positive root `μ` of the nonincreasing function
-- `l1SquareProxRootFunction ρ x`, so the KKT system gives
-- `λ_i = l1SquareProxWeight ρ μ x i`; substituting these weights yields the displayed minimizer.
/-- Lemma 6.70: let `f(x) = ‖x‖₁²` and `ρ > 0`. If `μ` is a positive root of
`ψ(μ) = ∑ i [√ρ |x_i| / √μ - 2ρ]_+ - 1` whenever `x ≠ 0`, then the proximal mapping of `ρ f` at
`x` is `{0}` for `x = 0`, and otherwise it is the singleton whose `i`-th coordinate is
`λ_i x_i / (λ_i + 2ρ)` with `λ_i = [√ρ |x_i| / √μ - 2ρ]_+`. -/
theorem prox_squared_l1_norm_penalty_eq_singleton_piecewise
    (ρ μ : ℝ) (hρ : 0 < ρ) (x : E)
    (hμ : x ≠ 0 → 0 < μ ∧ l1SquareProxRootFunction ρ x μ = 0) :
    prox[fun y : E ↦ ((ρ * ‖y‖₁ ^ (2 : ℕ) : ℝ) : EReal)] x =
      if _hx : x = 0 then
        {(0 : E)}
      else
        {toLp 2 (fun i ↦
          (l1SquareProxWeight ρ μ x i * x i) /
            (l1SquareProxWeight ρ μ x i + 2 * ρ))} := by
  let f : E → EReal := fun y : E ↦ ((ρ * ‖y‖₁ ^ (2 : ℕ) : ℝ) : EReal)
  have hf_proper : IsProperExtendedRealFunction f := by
    refine ⟨?_, ?_⟩
    · intro y
      simpa [f] using (EReal.coe_ne_bot (ρ * ‖y‖₁ ^ (2 : ℕ)))
    · refine ⟨0, ?_⟩
      simp [f]
  by_cases hx : x = 0
  · -- TODO: close the zero branch by showing the proximal objective is a sum of nonnegative
    -- real terms, with equality only at the origin.
    subst x
    have hsupport :
        ∀ y ∈ effective_domain f,
          ((inner ℝ ((0 : E) - 0) (y - 0) : ℝ) : EReal) ≤ f y - f 0 := by
      intro y hy
      have hnonneg : 0 ≤ ρ * ‖y‖₁ ^ (2 : ℕ) := by
        positivity
      have hnonnegE : (((0 : ℝ) : EReal)) ≤ (((ρ * ‖y‖₁ ^ (2 : ℕ) : ℝ) : EReal)) := by
        exact_mod_cast hnonneg
      simpa [f, EReal.coe_sub] using hnonnegE
    have hprox0 : prox[f] (0 : E) = {(0 : E)} := by
      refine
        prox_eq_singleton_of_effective_domain_and_inner_support
          f hf_proper (0 : E) (0 : E) ?_ hsupport
      simp [f, mem_effective_domain]
    simpa [f] using hprox0
  · -- TODO: active branch. The remaining blocker is the support-gap route:
    -- prove the threshold lemmas above, derive the global support inequality for
    -- `u = l1SquareProxCandidate ρ μ x`, and conclude that the objective gap is at least
    -- `(1 / 2) * ‖y - u‖^2`.
    rcases hμ hx with ⟨hμpos, hroot⟩
    let u : E := l1SquareProxCandidate ρ μ x
    have hsupport :
        ∀ y ∈ effective_domain f,
          ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤ f y - f u := by
      intro y hy
      have hreal :
          inner ℝ (x - u) (y - u) ≤
            ρ * ‖y‖₁ ^ (2 : ℕ) - ρ * ‖u‖₁ ^ (2 : ℕ) := by
        simpa [u] using l1SquareProxCandidate_support_bound hρ hμpos x y hroot
      have hrealE :
          ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤
            (((ρ * ‖y‖₁ ^ (2 : ℕ) - ρ * ‖u‖₁ ^ (2 : ℕ) : ℝ)) : EReal) :=
        EReal.coe_le_coe hreal
      simpa [f, u, EReal.coe_sub] using hrealE
    have hprox : prox[f] x = {u} := by
      refine prox_eq_singleton_of_effective_domain_and_inner_support f hf_proper x u ?_ hsupport
      simpa [f, u] using (EReal.coe_lt_top (ρ * ‖u‖₁ ^ (2 : ℕ)))
    simpa [f, u, hx] using hprox

end

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_22
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_14
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Remark_6_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TwoSidedSoftThreshold

/-- Rewriting the indicator of the nonnegative interval through `abs` gives the symmetric box
indicator used by the scalar coordinate penalty in Example 6.23. -/
private theorem extendedIndicator_nonnegative_interval_abs_eq_absolute_value_box_indicator
    (α : ENNReal) (t : ℝ) :
    extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} |t| =
      extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
  -- Both indicators are controlled by the same scalar box-membership condition.
  by_cases ht : ENNReal.ofReal |t| ≤ α
  · have hmem :
        |t| ∈ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} := by
      refine ⟨abs_nonneg t, ?_⟩
      have hmemE : (((ENNReal.ofReal |t| : ENNReal) : EReal)) ≤ (α : EReal) := by
        exact_mod_cast ht
      simpa using hmemE
    calc
      extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} |t| = 0 :=
        extendedIndicator_of_mem hmem
      _ = extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
        simp [extendedIndicator, ht]
  · have hnot_mem :
        |t| ∉ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} := by
      intro hmem
      have hmemE : (((ENNReal.ofReal |t| : ENNReal) : EReal)) ≤ (α : EReal) := by
        simpa using hmem.2
      exact ht (by exact_mod_cast hmemE)
    calc
      extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} |t| = ⊤ :=
        extendedIndicator_of_not_mem hnot_mem
      _ = extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
        simp [extendedIndicator, ht]

/-- The scalar coordinate penalty `truncated_linear_penalty μ α ∘ abs` is exactly the absolute
value box penalty `t ↦ μ |t| + δ_{[-α, α]}(t)`. This is the one-dimensional bridge used by the
vector separable formula in Example 6.23 and by its `Fin 1` specialization in Example 6.22. -/
private theorem truncated_linear_penalty_comp_abs_eq_absolute_value_box_penalty
    (μ : NNReal) (α : ENNReal) :
    truncated_linear_penalty (μ : ℝ) α ∘ abs =
      absoluteValueBoxPenalty μ α := by
  funext t
  -- Unfold both scalar owners and rewrite the interval indicator through `abs`.
  simp [absoluteValueBoxPenalty, truncated_linear_penalty, Function.comp_apply,
    extendedIndicator_nonnegative_interval_abs_eq_absolute_value_box_indicator, add_comm]

/-- Helper for Example 6.23: the `SignType.sign` coercion agrees with `Real.sign` on `ℝ`. -/
private theorem signTypeSignCoe_eq_realSign (x : ℝ) :
    (((SignType.sign x : SignType) : ℝ)) = Real.sign x := by
  -- Compare the three scalar sign regimes directly.
  obtain hxneg | hzero | hxpos := lt_trichotomy x 0
  · simp [Real.sign_of_neg hxneg, SignType.sign, hxneg, not_lt.mpr hxneg.le]
  · simp [hzero, Real.sign_zero]
  · simp [Real.sign_of_pos hxpos, SignType.sign, hxpos]

/-- Helper for Example 6.23: the magnitude of scalar soft-thresholding is the positive-part
radius `max (|x| - λ) 0`. -/
private theorem absSoftThresholding_eq_posPart_sub
    (lam : NNReal) (x : ℝ) :
    |𝒯[(lam : ℝ)] x| = max (|x| - (lam : ℝ)) 0 := by
  by_cases hx : x = 0
  · -- At the origin, soft-thresholding vanishes.
    simp [hx, soft_thresholding_apply]
  · -- Away from the origin, the sign factor has absolute value one.
    have hsign : |(((SignType.sign x : SignType) : ℝ))| = 1 := by
      obtain hxneg | hxpos := lt_or_gt_of_ne hx
      · rw [signTypeSignCoe_eq_realSign]
        simp [Real.sign_of_neg hxneg]
      · rw [signTypeSignCoe_eq_realSign]
        simp [Real.sign_of_pos hxpos]
    calc
      |𝒯[(lam : ℝ)] x| = |(|x| - (lam : ℝ))⁺ * (((SignType.sign x : SignType) : ℝ))| := by
        simp [soft_thresholding_apply]
      _ = |(|x| - (lam : ℝ))⁺| * |(((SignType.sign x : SignType) : ℝ))| := by
        rw [abs_mul]
      _ = (|x| - (lam : ℝ))⁺ := by
        rw [hsign, mul_one, abs_of_nonneg (by positivity)]
      _ = max (|x| - (lam : ℝ)) 0 := by
        simp [posPart]

/-- Helper for Example 6.23: scalar soft-thresholding is its magnitude multiplied by
`Real.sign`. -/
private theorem softThresholding_eq_abs_mul_realSign
    (lam : NNReal) (x : ℝ) :
    𝒯[(lam : ℝ)] x = |𝒯[(lam : ℝ)] x| * Real.sign x := by
  -- Rewrite both sides to the same positive-part/sign normal form.
  calc
    𝒯[(lam : ℝ)] x = (|x| - (lam : ℝ))⁺ * (((SignType.sign x : SignType) : ℝ)) := by
      simp [soft_thresholding_apply]
    _ = max (|x| - (lam : ℝ)) 0 * Real.sign x := by
      rw [signTypeSignCoe_eq_realSign]
      simp [posPart]
    _ = |𝒯[(lam : ℝ)] x| * Real.sign x := by
      rw [← absSoftThresholding_eq_posPart_sub]

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Example 6.23 is `source-facing` in the finite-product proximal domain.
Domain sampling against the surrounding chapter API fixes the owner split as follows:

- primitive/source data: the weighted box penalty `weighted_l1_box_penalty ω α`,
- core/canonical owners already upstream: `prox[...]`, `separableSum`, and the finite-product
  singleton bridge for separable proximal operators,
- private scalar bridge: `truncated_linear_penalty` from Example 6.14, used only to connect the
  box penalty with the scalar proximal theorem,
- bridge/view surface: the decomposition of `weighted_l1_box_penalty` into a separable sum of the
  scalar absolute-value box penalties.

The public statement therefore stays on the source-facing owner `weighted_l1_box_penalty`, while
the supporting API should reuse the chapter's separable-product proximal machinery rather than
introducing a parallel single-valued proximal map or a packaged coordinatewise wrapper; the
thresholded point itself should be expressed directly through the vector owner `𝓢[ω, α]`.
-/

/-- Helper for Example 6.23: the weighted `ℓ¹` penalty on the symmetric box `[-α, α]` is the
separable sum of the scalar absolute-value box penalties. -/
theorem weighted_l1_box_penalty_eq_separableSum_absoluteValueBoxPenalty
    (ω : ι → NNReal) (α : ι → ENNReal) :
    weighted_l1_box_penalty ω α =
      PiLp.separableSum
        (fun i ↦ absoluteValueBoxPenalty (ω i) (α i)) := by
  classical
  funext x
  -- Split according to whether `x` lies in the symmetric box.
  by_cases hx : ∀ i, ENNReal.ofReal |x i| ≤ α i
  · have hsum :
        (((∑ i, (ω i : ℝ) * |x i| : ℝ) : EReal)) =
          ∑ i, (((ω i : ℝ) * |x i| : ℝ) : EReal) := by
      simpa using ereal_coe_sum (s := Finset.univ) (φ := fun i : ι ↦ (ω i : ℝ) * |x i|)
    have hbox :
        extendedIndicator {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} x = 0 :=
      extendedIndicator_of_mem hx
    have hcoord :
        ∀ i, extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α i} (x i) = 0 := by
      intro i
      exact extendedIndicator_of_mem (hx i)
    calc
      weighted_l1_box_penalty ω α x
          = (((∑ i, (ω i : ℝ) * |x i| : ℝ) : EReal)) := by
              rw [weighted_l1_box_penalty_apply, hbox, add_zero]
      _ = ∑ i, (((ω i : ℝ) * |x i| : ℝ) : EReal) := hsum
      _ = ∑ i, absoluteValueBoxPenalty (ω i) (α i) (x i) := by
            simp [absoluteValueBoxPenalty_apply, hcoord]
      _ = PiLp.separableSum (fun i ↦ absoluteValueBoxPenalty (ω i) (α i)) x := by
            rw [PiLp.separableSum_apply]
  · have hx' : ∃ i, ¬ ENNReal.ofReal |x i| ≤ α i := by
      simpa using hx
    rcases hx' with ⟨i, hi⟩
    have hbox :
        extendedIndicator {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i} x = ⊤ :=
      extendedIndicator_of_not_mem hx
    have hterm_top :
        absoluteValueBoxPenalty (ω i) (α i) (x i) = ⊤ := by
      have hind_top :
          extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α i} (x i) = ⊤ :=
        extendedIndicator_of_not_mem hi
      calc
        absoluteValueBoxPenalty (ω i) (α i) (x i)
            = ((((ω i : ℝ) * |x i| : ℝ) : EReal) + ⊤) := by
                rw [absoluteValueBoxPenalty_apply, hind_top]
        _ = ⊤ := by
              rw [EReal.add_top_of_ne_bot (EReal.coe_ne_bot ((ω i : ℝ) * |x i|))]
    have hterm_ne_bot :
        ∀ j, absoluteValueBoxPenalty (ω j) (α j) (x j) ≠ ⊥ := by
      intro j
      by_cases hj : ENNReal.ofReal |x j| ≤ α j
      · have hind_zero :
            extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α j} (x j) = 0 :=
          extendedIndicator_of_mem hj
        calc
          absoluteValueBoxPenalty (ω j) (α j) (x j)
              = ((((ω j : ℝ) * |x j| : ℝ) : EReal) + 0) := by
                  rw [absoluteValueBoxPenalty_apply, hind_zero]
          _ ≠ ⊥ := by
                simpa using (EReal.coe_ne_bot ((ω j : ℝ) * |x j|))
      · have hind_top :
            extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α j} (x j) = ⊤ :=
          extendedIndicator_of_not_mem hj
        calc
          absoluteValueBoxPenalty (ω j) (α j) (x j)
              = ((((ω j : ℝ) * |x j| : ℝ) : EReal) + ⊤) := by
                  rw [absoluteValueBoxPenalty_apply, hind_top]
          _ ≠ ⊥ := by
                rw [EReal.add_top_of_ne_bot (EReal.coe_ne_bot ((ω j : ℝ) * |x j|))]
                simp
    have hrest_ne_bot :
        ((Finset.univ.erase i).sum
          (fun j ↦ absoluteValueBoxPenalty (ω j) (α j) (x j))) ≠ ⊥ := by
      exact ereal_sum_ne_bot (s := Finset.univ.erase i)
        (φ := fun j ↦ absoluteValueBoxPenalty (ω j) (α j) (x j))
        (fun j hj ↦ hterm_ne_bot j)
    calc
      weighted_l1_box_penalty ω α x = ⊤ := by
        rw [weighted_l1_box_penalty_apply, hbox, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      _ = ∑ j, absoluteValueBoxPenalty (ω j) (α j) (x j) := by
        symm
        rw [show
            (∑ j, absoluteValueBoxPenalty (ω j) (α j) (x j)) =
              absoluteValueBoxPenalty (ω i) (α i) (x i) +
                (Finset.univ.erase i).sum
                  (fun j ↦ absoluteValueBoxPenalty (ω j) (α j) (x j)) by
          symm
          exact Finset.add_sum_erase (s := Finset.univ) (a := i)
            (f := fun j ↦ absoluteValueBoxPenalty (ω j) (α j) (x j)) (Finset.mem_univ i)]
        rw [hterm_top, EReal.top_add_of_ne_bot hrest_ne_bot]
      _ = PiLp.separableSum (fun j ↦ absoluteValueBoxPenalty (ω j) (α j)) x := by
        rw [PiLp.separableSum_apply]

section

omit [Fintype ι]

/-- Helper for Example 6.23: the `i`-th coordinate of `𝓢[ω, α] x` matches the scalar closed form
used in Example 6.22. -/
private theorem twoSidedSoftThreshold_apply_eq_scalar_box_display
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) (i : ι) :
    𝓢[ω, α] x i =
      if α i = ⊤ then
        𝒯[(ω i : ℝ)] (x i)
      else
        min |𝒯[(ω i : ℝ)] (x i)| (α i).toReal * Real.sign (x i) := by
  -- Normalize the coordinate formula by separating the unbounded and clipped branches.
  by_cases hα : α i = ⊤
  · calc
      𝓢[ω, α] x i = |𝒯[(ω i : ℝ)] (x i)| * Real.sign (x i) := by
        simp [twoSidedSoftThreshold_apply, hα]
      _ = 𝒯[(ω i : ℝ)] (x i) := by
        rw [(softThresholding_eq_abs_mul_realSign (ω i) (x i)).symm]
      _ = if α i = ⊤ then
            𝒯[(ω i : ℝ)] (x i)
          else
            min |𝒯[(ω i : ℝ)] (x i)| (α i).toReal * Real.sign (x i) := by
        simp [hα]
  · calc
      𝓢[ω, α] x i =
          (((Set.projIcc 0 (α i).toReal (by positivity) |𝒯[(ω i : ℝ)] (x i)| :
              Set.Icc 0 (α i).toReal) : ℝ) * Real.sign (x i)) := by
        simp [twoSidedSoftThreshold_apply, hα]
      _ = min |𝒯[(ω i : ℝ)] (x i)| (α i).toReal * Real.sign (x i) := by
        congr 1
        rw [Set.coe_projIcc]
        have hclip_nonneg : 0 ≤ min |𝒯[(ω i : ℝ)] (x i)| (α i).toReal := by
          exact le_min (abs_nonneg _) ENNReal.toReal_nonneg
        rw [min_comm]
        rw [max_eq_right hclip_nonneg]
      _ = if α i = ⊤ then
            𝒯[(ω i : ℝ)] (x i)
          else
            min |𝒯[(ω i : ℝ)] (x i)| (α i).toReal * Real.sign (x i) := by
        simp [hα]

/-- Helper for Example 6.23: each coordinate proximal problem is exactly the scalar absolute-value
box problem, so its proximal set is the singleton at the corresponding
two-sided soft-threshold value. -/
private theorem prox_coordinate_truncated_linear_penalty_comp_abs_eq_singleton
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) (i : ι) :
    prox[truncated_linear_penalty (ω i) (α i) ∘ abs] (x i) =
      {𝓢[ω, α] x i} := by
  calc
    prox[truncated_linear_penalty (ω i) (α i) ∘ abs] (x i)
        = prox[absoluteValueBoxPenalty (ω i) (α i)] (x i) := by
            simp [truncated_linear_penalty_comp_abs_eq_absolute_value_box_penalty]
    _ = {if α i = ⊤ then
           𝒯[(ω i : ℝ)] (x i)
         else
           min |𝒯[(ω i : ℝ)] (x i)| (α i).toReal * Real.sign (x i)} := by
            simpa using prox_absolute_value_box_penalty_eq_singleton (ω i) (α i) (x i)
    _ = {𝓢[ω, α] x i} := by
            rw [← twoSidedSoftThreshold_apply_eq_scalar_box_display ω α x i]

end

-- Proof sketch: rewrite `weighted_l1_box_penalty` using
-- `weighted_l1_box_penalty_eq_separableSum_absoluteValueBoxPenalty`, apply
-- `prox_separableSum_eq_singleton_iff_coordinatewise`, and then use the scalar absolute-value
-- box formula from Example 6.22 coordinatewise to identify the minimizer as the corresponding
-- two-sided soft-threshold value.
/-- Example 6.23 (prox of weighted `ℓ¹` over a box): the proximal mapping of the weighted `ℓ¹`
penalty on the symmetric box `[-α, α]` is the singleton containing the coordinatewise two-sided
soft-thresholding point, i.e.
the vector with `i`-th coordinate
`min (max (|x i| - ω i) 0) α i * Real.sign (x i)`, with `α i = ∞` allowed. -/
theorem prox_weighted_l1_box_penalty_eq_singleton_twoSidedSoftThreshold
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) :
    prox[weighted_l1_box_penalty ω α] x =
      {𝓢[ω, α] x} := by
  have hf_proper :
      ∀ i, IsProperExtendedRealFunction (absoluteValueBoxPenalty (ω i) (α i)) := by
    intro i
    refine ⟨?_, ?_⟩
    · intro t
      by_cases ht : ENNReal.ofReal |t| ≤ α i
      · have hind_zero :
            extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α i} t = 0 :=
          extendedIndicator_of_mem ht
        calc
          absoluteValueBoxPenalty (ω i) (α i) t
              = ((((ω i : ℝ) * |t| : ℝ) : EReal) + 0) := by
                  rw [absoluteValueBoxPenalty_apply, hind_zero]
          _ ≠ ⊥ := by
                simpa using (EReal.coe_ne_bot ((ω i : ℝ) * |t|))
      · have hind_top :
            extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α i} t = ⊤ :=
          extendedIndicator_of_not_mem ht
        calc
          absoluteValueBoxPenalty (ω i) (α i) t
              = ((((ω i : ℝ) * |t| : ℝ) : EReal) + ⊤) := by
                  rw [absoluteValueBoxPenalty_apply, hind_top]
          _ ≠ ⊥ := by
                rw [EReal.add_top_of_ne_bot (EReal.coe_ne_bot ((ω i : ℝ) * |t|))]
                simp
    · refine ⟨0, ?_⟩
      rw [mem_effective_domain]
      simp [absoluteValueBoxPenalty_apply]
  -- Rewrite the source-facing penalty into the canonical separable owner and solve
  -- coordinatewise with the scalar proximal formula from Example 6.22.
  rw [weighted_l1_box_penalty_eq_separableSum_absoluteValueBoxPenalty]
  exact
    (prox_separableSum_eq_singleton_iff_coordinatewise
      (fun i ↦ absoluteValueBoxPenalty (ω i) (α i))
      hf_proper
      x
      (𝓢[ω, α] x)).2
      (fun i ↦ by
        simpa [truncated_linear_penalty_comp_abs_eq_absolute_value_box_penalty] using
          prox_coordinate_truncated_linear_penalty_comp_abs_eq_singleton ω α x i)

end

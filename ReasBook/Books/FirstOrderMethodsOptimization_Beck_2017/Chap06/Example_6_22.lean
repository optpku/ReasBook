/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_3
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_14
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_18
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

/- Example 6.22 is `source-facing` in the scalar box-constrained proximal domain.
The primitive owner is the scalar penalty `x ↦ λ |x| + δ_{[-α, α]}(x)`, while the surrounding
chapter already owns the supporting canonical API:

- `prox[...]` from Definition 6.1 for the set-valued proximal mapping,
- `𝒯[λ]` from Definition 6.2 for scalar soft-thresholding,
- the symmetric-box indicator `extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α}` from
  Chapter 2.

Accordingly, this file should own the scalar box penalty itself rather than leaving it as an
anonymous function in the proximal theorem. -/

/-- The scalar absolute-value box penalty `x ↦ λ |x| + δ_{[-α, α]}(x)`. -/
def absoluteValueBoxPenalty (lam : NNReal) (α : ENNReal) : ℝ → EReal :=
  fun t ↦ ((lam : ℝ) * |t| : ℝ) + extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t

/-- Evaluating `absoluteValueBoxPenalty lam α` gives the scalar value `λ |x|` plus the symmetric
box indicator. -/
@[simp] theorem absoluteValueBoxPenalty_apply (lam : NNReal) (α : ENNReal) (x : ℝ) :
    absoluteValueBoxPenalty lam α x =
      ((lam : ℝ) * |x| : ℝ) + extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} x :=
  rfl

/-- Helper for Example 6.22: the `SignType.sign` coercion agrees with `Real.sign` on `ℝ`. -/
private theorem signTypeSignCoe_eq_realSign (x : ℝ) :
    (((SignType.sign x : SignType) : ℝ)) = Real.sign x := by
  -- Compare the three scalar sign regimes directly.
  obtain hxneg | rfl | hxpos := lt_trichotomy x 0
  · simp [Real.sign_of_neg hxneg, SignType.sign, hxneg, not_lt.mpr hxneg.le]
  · simp [Real.sign_zero]
  · simp [Real.sign_of_pos hxpos, SignType.sign, hxpos]

/-- Helper for Example 6.22: evaluating the interval indicator at `|t|` matches the symmetric-box
indicator at `t`. -/
private theorem extendedIndicator_nonnegativeIntervalAbs_eq_absoluteValueBoxIndicator
    (α : ENNReal) (t : ℝ) :
    extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} |t| =
      extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
  -- Both indicators are controlled by the same membership condition `ENNReal.ofReal |t| ≤ α`.
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
      _ =
          extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
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
      _ =
          extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
            simp [extendedIndicator, ht]

/-- Helper for Example 6.22: the magnitude of scalar soft-thresholding is the positive-part
radius `max (|x| - λ) 0`. -/
private theorem absSoftThresholding_eq_posPart_sub
    (lam : NNReal) (x : ℝ) :
    |𝒯[(lam : ℝ)] x| = max (|x| - (lam : ℝ)) 0 := by
  by_cases hx : x = 0
  · -- At the origin, soft-thresholding vanishes.
    simp [hx, soft_thresholding_apply]
  · -- Away from the origin, the sign factor contributes absolute value one.
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

/-- Helper for Example 6.22: scalar soft-thresholding is its magnitude multiplied by
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

/-- Helper for Example 6.22: the box-constrained absolute-value penalty is the radial lift of the
scalar truncated linear penalty from Example 6.14. -/
private theorem absoluteValueBoxPenalty_eq_truncatedLinearPenalty_comp_abs
    (lam : NNReal) (α : ENNReal) :
    absoluteValueBoxPenalty lam α = truncated_linear_penalty (lam : ℝ) α ∘ abs := by
  funext t
  -- Unfold both owners and rewrite the indicator through the absolute value.
  simp [absoluteValueBoxPenalty, truncated_linear_penalty, Function.comp_apply,
    extendedIndicator_nonnegativeIntervalAbs_eq_absoluteValueBoxIndicator, add_comm]

/-- Helper for Example 6.22: the scalar truncated linear profile is proper, closed, and convex,
so it can be fed into Theorem 6.18. -/
private theorem truncatedLinearPenalty_proper_closed_convex
    (lam : NNReal) (α : ENNReal) :
    IsProperExtendedRealFunction (truncated_linear_penalty (lam : ℝ) α) ∧
      LowerSemicontinuous (truncated_linear_penalty (lam : ℝ) α) ∧
      is_convex_function (truncated_linear_penalty (lam : ℝ) α) := by
  let C : Set ℝ := {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)}
  have hC_closed : IsClosed C := by
    -- The scalar feasible set is either `[0, ∞)` or `[0, α.toReal]`.
    by_cases hα : α = ⊤
    · simpa [C, hα] using isClosed_Ici (a := (0 : ℝ))
    · have hC_eq : C = Set.Icc (0 : ℝ) α.toReal := by
        ext y
        constructor
        · intro hy
          refine ⟨hy.1, ?_⟩
          have hy' : (((ENNReal.ofReal y : ENNReal) : EReal)) ≤ (α : EReal) := by
            simpa [hy.1] using hy.2
          have hy'' : ENNReal.ofReal y ≤ α := by
            exact_mod_cast hy'
          exact (ENNReal.ofReal_le_iff_le_toReal hα).1 hy''
        · intro hy
          refine ⟨hy.1, ?_⟩
          have hy' : ENNReal.ofReal y ≤ α :=
            ENNReal.ofReal_le_of_le_toReal hy.2
          have hy'' : (((ENNReal.ofReal y : ENNReal) : EReal)) ≤ (α : EReal) := by
            exact_mod_cast hy'
          simpa [hy.1] using hy''
      rw [hC_eq]
      exact isClosed_Icc
  have hC_convex : Convex ℝ C := by
    -- The same geometric description gives convexity of the feasible interval.
    by_cases hα : α = ⊤
    · simpa [C, hα] using convex_Ici (0 : ℝ)
    · have hC_eq : C = Set.Icc (0 : ℝ) α.toReal := by
        ext y
        constructor
        · intro hy
          refine ⟨hy.1, ?_⟩
          have hy' : (((ENNReal.ofReal y : ENNReal) : EReal)) ≤ (α : EReal) := by
            simpa [hy.1] using hy.2
          have hy'' : ENNReal.ofReal y ≤ α := by
            exact_mod_cast hy'
          exact (ENNReal.ofReal_le_iff_le_toReal hα).1 hy''
        · intro hy
          refine ⟨hy.1, ?_⟩
          have hy' : ENNReal.ofReal y ≤ α :=
            ENNReal.ofReal_le_of_le_toReal hy.2
          have hy'' : (((ENNReal.ofReal y : ENNReal) : EReal)) ≤ (α : EReal) := by
            exact_mod_cast hy'
          simpa [hy.1] using hy''
      rw [hC_eq]
      exact convex_Icc (0 : ℝ) α.toReal
  have heff :
      effective_domain (truncated_linear_penalty (lam : ℝ) α) = C := by
    ext y
    rw [mem_effective_domain]
    by_cases hy : y ∈ C
    · rw [truncated_linear_penalty, Pi.add_apply, extendedIndicator_of_mem hy]
      simpa [hy] using (EReal.coe_lt_top ((lam : ℝ) * y))
    · rw [truncated_linear_penalty, Pi.add_apply, extendedIndicator_of_not_mem hy]
      rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      simp [hy]
  have hproper : IsProperExtendedRealFunction (truncated_linear_penalty (lam : ℝ) α) := by
    refine ⟨?_, ?_⟩
    · intro y
      by_cases hy : y ∈ C
      · rw [truncated_linear_penalty, Pi.add_apply, extendedIndicator_of_mem hy]
        simpa using (EReal.coe_ne_bot ((lam : ℝ) * y))
      · rw [truncated_linear_penalty, Pi.add_apply, extendedIndicator_of_not_mem hy]
        rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
        simp
    · -- The feasible interval always contains `0`, so the effective domain is nonempty.
      refine ⟨0, ?_⟩
      rw [mem_effective_domain, truncated_linear_penalty, Pi.add_apply]
      have hzero_mem : (0 : ℝ) ∈ C := by
        refine ⟨le_rfl, ?_⟩
        simpa using
          (show (((0 : ENNReal) : EReal)) ≤ (α : EReal) by
            exact_mod_cast (show (0 : ENNReal) ≤ α from bot_le))
      rw [extendedIndicator_of_mem hzero_mem]
      simp
  have hcont :
      ContinuousOn (truncated_linear_penalty (lam : ℝ) α)
        (effective_domain (truncated_linear_penalty (lam : ℝ) α)) := by
    -- On the effective domain, the indicator vanishes and only the affine term remains.
    rw [heff]
    have hlin :
        Continuous fun y : ℝ ↦ (((lam : ℝ) * y : ℝ) : EReal) :=
      continuous_coe_real_ereal.comp (continuous_const.mul continuous_id)
    refine hlin.continuousOn.congr ?_
    intro y hy
    simp [truncated_linear_penalty, C, hy]
  have hclosed : LowerSemicontinuous (truncated_linear_penalty (lam : ℝ) α) := by
    -- Closedness follows from continuity on the closed effective domain.
    exact lowerSemicontinuous_of_continuousOn_effective_domain
      (truncated_linear_penalty (lam : ℝ) α) hcont (by simpa [heff] using hC_closed)
  have hconvex : is_convex_function (truncated_linear_penalty (lam : ℝ) α) := by
    -- The profile is the sum of the convex interval indicator and the affine term.
    have hind : is_convex_function (δ_ C) :=
      extendedIndicator_isConvexFunction_of_convex C hC_convex
    have hlin :
        is_convex_function (fun y : ℝ ↦ (((lam : ℝ) * y : ℝ) : EReal)) := by
      refine Function.toEReal_isConvexFunction ?_
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b ha hb hab
      change (lam : ℝ) * (a * x + b * y) ≤ a * ((lam : ℝ) * x) + b * ((lam : ℝ) * y)
      nlinarith
    simpa [truncated_linear_penalty, C, Function.toEReal, Pi.add_apply] using
      is_convex_function_pointwise_add hind hlin
        (fun y ↦ by
          by_cases hy : y ∈ C <;> simp [extendedIndicator, hy])
        (fun y ↦ by exact EReal.coe_ne_bot _)
  exact ⟨hproper, hclosed, hconvex⟩

/-- Helper for Example 6.22: the scalar truncated linear profile is `⊤` on the negative ray. -/
private theorem truncatedLinearPenalty_eq_top_of_neg
    (lam : NNReal) (α : ENNReal) {t : ℝ} (ht : t < 0) :
    truncated_linear_penalty (lam : ℝ) α t = ⊤ := by
  -- Negative radii lie outside the feasible interval, so the indicator forces `⊤`.
  have ht_mem :
      t ∉ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} := by
    intro h
    exact ht.not_ge h.1
  rw [truncated_linear_penalty, Pi.add_apply, extendedIndicator_of_not_mem ht_mem]
  exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)

/-- Helper for Example 6.22: radial lifts on `ℝ` reduce to multiplication by `Real.sign`. -/
private theorem div_abs_mul_eq_mul_realSign
    {x a : ℝ} (hx : x ≠ 0) :
    (a / |x|) * x = a * Real.sign x := by
  -- Normalize the ray factor through the identity `x / |x| = sign x`.
  have hsign : x / |x| = Real.sign x := by
    obtain hxneg | hxpos := lt_or_gt_of_ne hx
    · rw [abs_of_neg hxneg, Real.sign_of_neg hxneg]
      field_simp [hxneg.ne]
    · rw [abs_of_pos hxpos, Real.sign_of_pos hxpos]
      field_simp [hxpos.ne']
  calc
    (a / |x|) * x = a * (x / |x|) := by
      rw [div_eq_mul_inv, mul_assoc, mul_comm (|x|⁻¹) x, ← div_eq_mul_inv]
    _ = a * Real.sign x := by rw [hsign]

/-- Example 6.22: for the scalar penalty `x ↦ λ |x| + δ_{[-α, α]}(x)`, the proximal mapping at
`x` is the singleton containing the clipped soft-threshold value. -/
theorem prox_absolute_value_box_penalty_eq_singleton
    (lam : NNReal) (α : ENNReal) (x : ℝ) :
    prox[absoluteValueBoxPenalty lam α] x =
      {if α = ⊤ then
         𝒯[(lam : ℝ)] x
       else
         min |𝒯[(lam : ℝ)] x| α.toReal * Real.sign x} := by
  -- Route correction: rewrite the box penalty as the radial lift of Example 6.14's scalar owner,
  -- then use Theorem 6.18 to transport the scalar proximal singleton to `ℝ`.
  let g : ℝ → EReal := truncated_linear_penalty (lam : ℝ) α
  have hcomp : absoluteValueBoxPenalty lam α = g ∘ abs := by
    simpa [g] using absoluteValueBoxPenalty_eq_truncatedLinearPenalty_comp_abs lam α
  rcases truncatedLinearPenalty_proper_closed_convex lam α with ⟨hproper, hclosed, hconvex⟩
  have hdom : ∀ t : ℝ, t < 0 → g t = ⊤ := by
    intro t ht
    simpa [g] using truncatedLinearPenalty_eq_top_of_neg lam α ht
  by_cases hx : x = 0
  · subst x
    have hscalar0 : prox[g] 0 = {0} := by
      simpa [g] using prox_truncated_linear_penalty_eq_singleton (lam : ℝ) α 0
    have hzero :
        prox[absoluteValueBoxPenalty lam α] 0 = {u : ℝ | |u| ∈ prox[g] 0} := by
      calc
        prox[absoluteValueBoxPenalty lam α] 0 = prox[g ∘ abs] 0 := by
          exact congrArg (fun h : ℝ → EReal ↦ prox[h] 0) hcomp
        _ = {u : ℝ | |u| ∈ prox[g] 0} := by
          simpa [Real.norm_eq_abs] using
            prox_norm_composition_at_zero (g := g) (hproper := hproper) (hclosed := hclosed)
              (hconvex := hconvex) (hdom := hdom)
    calc
      prox[absoluteValueBoxPenalty lam α] 0 = {u : ℝ | |u| ∈ prox[g] 0} := hzero
      _ = {0} := by
        rw [hscalar0]
        ext u
        simp
      _ = {if α = ⊤ then
             𝒯[(lam : ℝ)] (0 : ℝ)
           else
             min |𝒯[(lam : ℝ)] (0 : ℝ)| α.toReal * Real.sign (0 : ℝ)} := by
        rw [Set.singleton_eq_singleton_iff]
        by_cases hα : α = ⊤ <;> simp [hα, soft_thresholding_apply]
  · have hnonzero :
        prox[absoluteValueBoxPenalty lam α] x =
          (fun t : ℝ ↦ (t / |x|) * x) '' prox[g] |x| := by
      calc
        prox[absoluteValueBoxPenalty lam α] x = prox[g ∘ abs] x := by
          exact congrArg (fun h : ℝ → EReal ↦ prox[h] x) hcomp
        _ = (fun t : ℝ ↦ (t / ‖x‖) • x) '' prox[g] ‖x‖ := by
          simpa [Real.norm_eq_abs] using
            prox_norm_composition_of_ne_zero (g := g) (hproper := hproper) (hclosed := hclosed)
              (hconvex := hconvex) (hdom := hdom) hx
        _ = (fun t : ℝ ↦ (t / |x|) * x) '' prox[g] |x| := by
          simp [Real.norm_eq_abs, smul_eq_mul]
    by_cases hα : α = ⊤
    · have hscalar :
          prox[g] |x| = {max (|x| - (lam : ℝ)) 0} := by
        simpa [g, hα] using prox_truncated_linear_penalty_eq_singleton (lam : ℝ) α |x|
      have hvalue :
          ((max (|x| - (lam : ℝ)) 0) / |x|) * x = 𝒯[(lam : ℝ)] x := by
        calc
          ((max (|x| - (lam : ℝ)) 0) / |x|) * x =
              max (|x| - (lam : ℝ)) 0 * Real.sign x := by
                simpa using
                  (div_abs_mul_eq_mul_realSign (x := x)
                    (a := max (|x| - (lam : ℝ)) 0) hx)
          _ = |𝒯[(lam : ℝ)] x| * Real.sign x := by
                rw [absSoftThresholding_eq_posPart_sub]
          _ = 𝒯[(lam : ℝ)] x := (softThresholding_eq_abs_mul_realSign lam x).symm
      rw [hnonzero, hscalar, Set.image_singleton, hvalue]
      simp [hα]
    · have hscalar :
          prox[g] |x| = {min (max (|x| - (lam : ℝ)) 0) α.toReal} := by
        simpa [g, hα] using prox_truncated_linear_penalty_eq_singleton (lam : ℝ) α |x|
      have hvalue :
          ((min (max (|x| - (lam : ℝ)) 0) α.toReal) / |x|) * x =
            min |𝒯[(lam : ℝ)] x| α.toReal * Real.sign x := by
        calc
          ((min (max (|x| - (lam : ℝ)) 0) α.toReal) / |x|) * x =
              min (max (|x| - (lam : ℝ)) 0) α.toReal * Real.sign x := by
                simpa using
                  (div_abs_mul_eq_mul_realSign (x := x)
                    (a := min (max (|x| - (lam : ℝ)) 0) α.toReal) hx)
          _ = min |𝒯[(lam : ℝ)] x| α.toReal * Real.sign x := by
                rw [absSoftThresholding_eq_posPart_sub]
      rw [hnonzero, hscalar, Set.image_singleton, hvalue]
      simp [hα]

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_23
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators TwoSidedSoftThreshold

noncomputable section

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/-
Example 6.34 is `source-facing` in the weighted `ℓ¹`-plus-box projection domain. Domain sampling
against Definition 6.5, Definition 6.6, Example 6.23, and Theorem 6.30 shows that the owner
layers are:

- `source-facing`: the weighted-box projection formula itself,
- `core/canonical`: the coordinatewise two-sided soft-thresholding operator `𝓢[ω, α]`, the
  weighted box constraint set `weighted_l1_box_constraint_set ω α β`, the weighted penalty owner
  `weighted_l1_box_penalty ω α`, the generic level-set residual `level_set_projection_residual`,
  and the set-valued projection map `P[C]`,
- `bridge/view`: the explicit scalar root function coming from the proximal singleton formula in
  Example 6.23, its positive-multiplier identification with the generic residual from Theorem
  6.30, and the feasible `λ = 0` reduction to projection onto `effective_domain
  (weighted_l1_box_penalty ω α)`, i.e. the symmetric box.

The local file should therefore not re-own the clipped point `S_{0, α}(x)` or the active point
`S_{λω, α}(x)` as parallel public definitions. The only genuine local bridge owner is the explicit
root function governing the active-constraint branch, together with its positive-multiplier bridge
to Theorem 6.30.
-/

variable (ω : ι → NNReal) (α : ι → ENNReal) (β : ℝ)

/-- The explicit root function `φ(λ) = ωᵀ |S_{λω, α}(x)| - β` governing the active branch of the
weighted-box projection formula. Its domain is `NNReal`, so the nonnegativity of the multiplier
is built into the owner rather than carried as a separate hypothesis. At `λ = 0`, this owner is
the weighted `ℓ¹` value of the box-clipped point `S_{0, α}(x)`, not the generic residual from
Theorem 6.30 evaluated at `0`. -/
def weightedL1BoxProjectionRootFunction
    (x : E) : NNReal → ℝ :=
  fun lam ↦ (∑ i, (ω i : ℝ) * |𝓢[(fun i ↦ lam * ω i), α] x i|) - β

section

variable (x : E)

/-- In the source-facing projection statements below, the textbook root function is written as
`φ(λ) = ωᵀ |S_{λω, α}(x)| - β`. -/
local notation "φ" => weightedL1BoxProjectionRootFunction ω α β x
local notation "C" => weighted_l1_box_constraint_set ω α β

/-- Helper for Example 6.34: the magnitude of scalar soft-thresholding is the positive-part
radius. -/
lemma abs_soft_thresholding_eq_posPart_sub
    (μ : NNReal) (t : ℝ) :
    |𝒯[(μ : ℝ)] t| = max (|t| - (μ : ℝ)) 0 := by
  -- Rewrite the scalar thresholding rule into its positive-part/sign form.
  by_cases ht : t = 0
  · simp [ht, soft_thresholding_apply]
  · have hsign : |(((SignType.sign t : SignType) : ℝ))| = 1 := by
      obtain hneg | hpos := lt_or_gt_of_ne ht
      · simp [SignType.sign, hneg, not_lt.mpr hneg.le]
      · simp [SignType.sign, hpos]
    calc
      |𝒯[(μ : ℝ)] t| = |(|t| - (μ : ℝ))⁺ * (((SignType.sign t : SignType) : ℝ))| := by
        simp [soft_thresholding_apply]
      _ = |(|t| - (μ : ℝ))⁺| * |(((SignType.sign t : SignType) : ℝ))| := by
        rw [abs_mul]
      _ = (|t| - (μ : ℝ))⁺ := by
        rw [hsign, mul_one, abs_of_nonneg (by positivity)]
      _ = max (|t| - (μ : ℝ)) 0 := rfl

/-- Helper for Example 6.34: the magnitude of each coordinate of the two-sided thresholded point
is exactly the clipped positive-part radius. -/
lemma abs_twoSidedSoftThreshold_apply_eq_clipped_radius
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) (i : ι) :
    |𝓢[ω, α] x i| =
      if hα : α i = ⊤ then
        max (|x i| - (ω i : ℝ)) 0
      else
        ((Set.projIcc 0 (α i).toReal (by positivity)
            (max (|x i| - (ω i : ℝ)) 0) : Set.Icc 0 (α i).toReal) : ℝ) := by
  -- Route correction: prove the coordinate magnitude formula first, then use it for both the box
  -- membership bridge and the monotonicity of the source-facing root function.
  by_cases hα : α i = ⊤
  · by_cases hxi : x i = 0
    · simp [twoSidedSoftThreshold_apply, hα, hxi]
    · have hsign : |Real.sign (x i)| = 1 := by
        obtain hneg | hpos := lt_or_gt_of_ne hxi
        · simp [Real.sign_of_neg hneg]
        · simp [Real.sign_of_pos hpos]
      calc
        |𝓢[ω, α] x i| = |(|𝒯[(ω i : ℝ)] (x i)| * Real.sign (x i))| := by
          simp [twoSidedSoftThreshold_apply, hα]
        _ = |𝒯[(ω i : ℝ)] (x i)| * |Real.sign (x i)| := by
          rw [abs_mul, abs_of_nonneg (abs_nonneg _)]
        _ = max (|x i| - (ω i : ℝ)) 0 * 1 := by
          rw [abs_soft_thresholding_eq_posPart_sub (ω i) (x i), hsign]
        _ = max (|x i| - (ω i : ℝ)) 0 := by ring
        _ = if hα' : α i = ⊤ then max (|x i| - (ω i : ℝ)) 0 else
              ((Set.projIcc 0 (α i).toReal (by positivity)
                  (max (|x i| - (ω i : ℝ)) 0) : Set.Icc 0 (α i).toReal) : ℝ) := by
              simp [hα]
  · by_cases hxi : x i = 0
    · simp [twoSidedSoftThreshold_apply, hα, hxi]
    · have hsign : |Real.sign (x i)| = 1 := by
        obtain hneg | hpos := lt_or_gt_of_ne hxi
        · simp [Real.sign_of_neg hneg]
        · simp [Real.sign_of_pos hpos]
      calc
        |𝓢[ω, α] x i| =
            |(((Set.projIcc 0 (α i).toReal (by positivity) |𝒯[(ω i : ℝ)] (x i)| :
                Set.Icc 0 (α i).toReal) : ℝ) * Real.sign (x i))| := by
              simp [twoSidedSoftThreshold_apply, hα]
        _ =
            ((Set.projIcc 0 (α i).toReal (by positivity) |𝒯[(ω i : ℝ)] (x i)| :
                Set.Icc 0 (α i).toReal) : ℝ) * |Real.sign (x i)| := by
              rw [abs_mul, abs_of_nonneg]
              exact (Set.projIcc 0 (α i).toReal (by positivity)
                |𝒯[(ω i : ℝ)] (x i)|).property.1
        _ =
            ((Set.projIcc 0 (α i).toReal (by positivity)
                (max (|x i| - (ω i : ℝ)) 0) : Set.Icc 0 (α i).toReal) : ℝ) * 1 := by
              rw [abs_soft_thresholding_eq_posPart_sub (ω i) (x i), hsign]
        _ =
            ((Set.projIcc 0 (α i).toReal (by positivity)
                (max (|x i| - (ω i : ℝ)) 0) : Set.Icc 0 (α i).toReal) : ℝ) := by
              ring
        _ = if hα' : α i = ⊤ then max (|x i| - (ω i : ℝ)) 0 else
              ((Set.projIcc 0 (α i).toReal (by positivity)
                  (max (|x i| - (ω i : ℝ)) 0) : Set.Icc 0 (α i).toReal) : ℝ) := by
              simp [hα]

/-- Helper for Example 6.34: every two-sided thresholded point lies in the symmetric box
supporting the weighted box penalty. -/
lemma twoSidedSoftThreshold_mem_effective_box
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) :
    ∀ i, ENNReal.ofReal |𝓢[ω, α] x i| ≤ α i := by
  intro i
  -- Keep the finite branch in `ℝ` until the clipped radius bound is complete, then transport once
  -- to `ENNReal`.
  rw [abs_twoSidedSoftThreshold_apply_eq_clipped_radius (ω := ω) (α := α) (x := x) (i := i)]
  by_cases hα : α i = ⊤
  · simp [hα]
  · let c : Set.Icc (0 : ℝ) (α i).toReal :=
      Set.projIcc 0 (α i).toReal (by positivity) (max (|x i| - (ω i : ℝ)) 0)
    have hc_le : (c : ℝ) ≤ (α i).toReal := c.property.2
    simpa [hα, c] using ENNReal.ofReal_le_of_le_toReal hc_le

/-- Helper for Example 6.34: for each coordinate, the magnitude of the clipped thresholded point
is antitone in the multiplier. -/
lemma abs_twoSidedSoftThreshold_apply_antitone
    (ω : ι → NNReal) (α : ι → ENNReal) (x : E) (i : ι) :
    Antitone (fun lam : NNReal ↦ |𝓢[(fun j ↦ lam * ω j), α] x i|) := by
  intro lam₁ lam₂ hle
  -- Compare the unclipped radii first, then use the monotonicity of interval projection.
  have hradius :
      max (|x i| - ((lam₂ * ω i : NNReal) : ℝ)) 0 ≤
        max (|x i| - ((lam₁ * ω i : NNReal) : ℝ)) 0 := by
    have hmul :
        (((lam₁ * ω i : NNReal) : ℝ)) ≤ (((lam₂ * ω i : NNReal) : ℝ)) := by
      exact_mod_cast (show lam₁ * ω i ≤ lam₂ * ω i by
        exact mul_le_mul_right' hle (ω i))
    have hsub :
        |x i| - ((lam₂ * ω i : NNReal) : ℝ) ≤
          |x i| - ((lam₁ * ω i : NNReal) : ℝ) := by
      linarith
    exact max_le_max_right 0 hsub
  change |𝓢[(fun j ↦ lam₂ * ω j), α] x i| ≤ |𝓢[(fun j ↦ lam₁ * ω j), α] x i|
  rw [abs_twoSidedSoftThreshold_apply_eq_clipped_radius
      (ω := fun j ↦ lam₂ * ω j) (α := α) (x := x) (i := i)]
  rw [abs_twoSidedSoftThreshold_apply_eq_clipped_radius
      (ω := fun j ↦ lam₁ * ω j) (α := α) (x := x) (i := i)]
  by_cases hα : α i = ⊤
  · simpa [hα] using hradius
  · -- In the finite branch, `Set.projIcc` preserves order on the clipped radii.
    simpa [hα] using
      (Set.monotone_projIcc (a := (0 : ℝ)) (b := (α i).toReal) (h := by positivity) hradius)

/-- Helper for Example 6.34: the effective domain of the weighted box penalty is exactly the
symmetric box `{-α ≤ x ≤ α}`. -/
lemma mem_effective_domain_weighted_l1_box_penalty_iff
    (ω : ι → NNReal) (α : ι → ENNReal) (y : E) :
    y ∈ effective_domain (weighted_l1_box_penalty ω α) ↔
      ∀ i, ENNReal.ofReal |y i| ≤ α i := by
  -- The weighted absolute-value sum is always finite; only the indicator term governs finiteness.
  rw [mem_effective_domain, weighted_l1_box_penalty_apply]
  by_cases hy : ∀ i, ENNReal.ofReal |y i| ≤ α i
  · simp [extendedIndicator, hy]
  · simp [extendedIndicator, hy, EReal.add_top_of_ne_bot, EReal.coe_ne_bot]

/-- Helper for Example 6.34: on its effective domain, the weighted box penalty reduces to the
finite weighted absolute-value sum. -/
lemma weighted_l1_box_penalty_eq_weighted_sum_of_mem_effective_domain
    (ω : ι → NNReal) (α : ι → ENNReal) {y : E}
    (hy : y ∈ effective_domain (weighted_l1_box_penalty ω α)) :
    weighted_l1_box_penalty ω α y =
      ((∑ i, (ω i : ℝ) * |y i| : ℝ) : EReal) := by
  -- Once `y` is known to stay in the box, the indicator term vanishes.
  have hy_box : ∀ i, ENNReal.ofReal |y i| ≤ α i :=
    (mem_effective_domain_weighted_l1_box_penalty_iff ω α y).1 hy
  rw [weighted_l1_box_penalty_apply]
  simp [extendedIndicator, hy_box]

/-- Helper for Example 6.34: at zero weights, the weighted box penalty is just the indicator of
the effective domain of `weighted_l1_box_penalty ω α`, i.e. of the symmetric box. -/
lemma weighted_l1_box_penalty_zero_weights_eq_extendedIndicator_effective_domain
    (ω : ι → NNReal) (α : ι → ENNReal) :
    weighted_l1_box_penalty (fun _ ↦ (0 : NNReal)) α =
      extendedIndicator (effective_domain (weighted_l1_box_penalty ω α)) := by
  funext y
  -- The zero-weight penalty keeps only the box indicator, and the effective domain does not
  -- depend on the weights.
  by_cases hy : ∀ i, ENNReal.ofReal |y i| ≤ α i
  · rw [weighted_l1_box_penalty_apply]
    have hy_eff : y ∈ effective_domain (weighted_l1_box_penalty ω α) := by
      exact (mem_effective_domain_weighted_l1_box_penalty_iff ω α y).2 hy
    simp [extendedIndicator, hy, hy_eff]
  · rw [weighted_l1_box_penalty_apply]
    have hy_not_eff : y ∉ effective_domain (weighted_l1_box_penalty ω α) := by
      simpa [mem_effective_domain_weighted_l1_box_penalty_iff (ω := ω) (α := α) (y := y)] using hy
    simp [extendedIndicator, hy, hy_not_eff, EReal.add_top_of_ne_bot, EReal.coe_ne_bot]

/-- Helper for Example 6.34: the weighted box penalty is proper, lower semicontinuous, and
convex, so it fits the generic level-set projection framework from Theorem 6.30. -/
lemma weighted_l1_box_penalty_proper_closed_convex :
    IsProperExtendedRealFunction (weighted_l1_box_penalty ω α) ∧
      LowerSemicontinuous (weighted_l1_box_penalty ω α) ∧
      is_convex_function (weighted_l1_box_penalty ω α) := by
  let g : E → ℝ := fun y ↦ ∑ i, (ω i : ℝ) * |y i|
  let B : Set E := {y : E | ∀ i, ENNReal.ofReal |y i| ≤ α i}
  have hbox_closed : IsClosed B := by
    have hset :
        weighted_l1_box_constraint_set (fun _ ↦ (0 : NNReal)) α 0 = B := by
      ext y
      simp [B, mem_weighted_l1_box_constraint_set_iff]
    simpa [hset] using
      weighted_l1_box_constraint_set_isClosed (fun _ ↦ (0 : NNReal)) α 0
  have hbox_convex : Convex ℝ B := by
    have hset :
        weighted_l1_box_constraint_set (fun _ ↦ (0 : NNReal)) α 0 = B := by
      ext y
      simp [B, mem_weighted_l1_box_constraint_set_iff]
    simpa [hset] using
      weighted_l1_box_constraint_set_convex (fun _ ↦ (0 : NNReal)) α 0
  have hcont_g : Continuous g := by
    -- The weighted absolute-value sum is continuous coordinatewise.
    unfold g
    refine continuous_finset_sum Finset.univ ?_
    intro i hi
    simpa [Real.norm_eq_abs] using
      ((PiLp.continuous_apply (2 : ENNReal) (fun _ ↦ ℝ) i).norm.const_mul (ω i : ℝ))
  have hg_closed : LowerSemicontinuous (fun y ↦ (g y : EReal)) :=
    (continuous_coe_real_ereal.comp hcont_g).lowerSemicontinuous
  have hind_closed : LowerSemicontinuous (extendedIndicator B) := by
    rw [extendedIndicator_lowerSemicontinuous_iff_isClosed]
    exact hbox_closed
  have hproper : IsProperExtendedRealFunction (weighted_l1_box_penalty ω α) := by
    refine ⟨?_, ?_⟩
    · intro y
      by_cases hy : ∀ i, ENNReal.ofReal |y i| ≤ α i
      · rw [weighted_l1_box_penalty_apply]
        simp [extendedIndicator, hy]
      · rw [weighted_l1_box_penalty_apply]
        simp [extendedIndicator, hy, EReal.add_top_of_ne_bot, EReal.coe_ne_bot]
    · refine ⟨0, ?_⟩
      have hzero : ∀ i, ENNReal.ofReal |(0 : E) i| ≤ α i := by
        intro i
        simp
      rw [mem_effective_domain_weighted_l1_box_penalty_iff (ω := ω) (α := α) (y := (0 : E))]
      exact hzero
  have heff :
      effective_domain (weighted_l1_box_penalty ω α) = B := by
    ext y
    simp [B, mem_effective_domain_weighted_l1_box_penalty_iff (ω := ω) (α := α) (y := y)]
  have hsum_convex : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, ?_⟩
    intro y hy z hz a b ha hb hab
    -- Convexity follows from the triangle inequality coordinatewise and nonnegative weights.
    change (∑ i, (ω i : ℝ) * |(a • y + b • z) i|) ≤
      a * (∑ i, (ω i : ℝ) * |y i|) + b * (∑ i, (ω i : ℝ) * |z i|)
    have hterm :
        ∀ i,
          (ω i : ℝ) * |(a • y + b • z) i| ≤
            (ω i : ℝ) * (a * |y i| + b * |z i|) := by
      intro i
      have habs :
          |(a • y + b • z) i| ≤ a * |y i| + b * |z i| := by
        calc
          |(a • y + b • z) i| = |a * y i + b * z i| := by
            simp [smul_eq_mul]
          _ ≤ |a * y i| + |b * z i| := by
            simpa [Real.norm_eq_abs] using norm_add_le (a * y i) (b * z i)
          _ = a * |y i| + b * |z i| := by
            rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hb]
      have hω : 0 ≤ (ω i : ℝ) := by
        exact_mod_cast (ω i).2
      exact mul_le_mul_of_nonneg_left habs hω
    have hsum :
        (∑ i, (ω i : ℝ) * |(a • y + b • z) i|) ≤
          ∑ i, (ω i : ℝ) * (a * |y i| + b * |z i|) := by
      exact Finset.sum_le_sum fun i hi ↦ hterm i
    calc
      (∑ i, (ω i : ℝ) * |(a • y + b • z) i|) ≤
          ∑ i, (ω i : ℝ) * (a * |y i| + b * |z i|) := hsum
      _ = a * ∑ i, (ω i : ℝ) * |y i| + b * ∑ i, (ω i : ℝ) * |z i| := by
        calc
          (∑ i, (ω i : ℝ) * (a * |y i| + b * |z i|)) =
              ∑ i, (a * ((ω i : ℝ) * |y i|) + b * ((ω i : ℝ) * |z i|)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
          _ = a * ∑ i, (ω i : ℝ) * |y i| + b * ∑ i, (ω i : ℝ) * |z i| := by
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_add_distrib]
  have hconv_box :
      ConvexOn ℝ B (fun y ↦ (weighted_l1_box_penalty ω α y).toReal) := by
    refine ⟨hbox_convex, ?_⟩
    intro y hy z hz a b ha hb hab
    have hy_eff : y ∈ effective_domain (weighted_l1_box_penalty ω α) := by
      simpa [heff] using hy
    have hz_eff : z ∈ effective_domain (weighted_l1_box_penalty ω α) := by
      simpa [heff] using hz
    have hcombo : a • y + b • z ∈ B := hbox_convex hy hz ha hb hab
    have hcombo_eff : a • y + b • z ∈ effective_domain (weighted_l1_box_penalty ω α) := by
      simpa [heff] using hcombo
    -- After restricting to the effective domain, only the finite weighted sum remains.
    simpa [g,
        weighted_l1_box_penalty_eq_weighted_sum_of_mem_effective_domain (ω := ω) (α := α)
          hy_eff,
        weighted_l1_box_penalty_eq_weighted_sum_of_mem_effective_domain (ω := ω) (α := α)
          hz_eff,
        weighted_l1_box_penalty_eq_weighted_sum_of_mem_effective_domain (ω := ω) (α := α)
          hcombo_eff] using
      hsum_convex.2 (by simp) (by simp) ha hb hab
  have hconv : is_convex_function (weighted_l1_box_penalty ω α) := by
    have hne_bot :
        ∀ y ∈ effective_domain (weighted_l1_box_penalty ω α),
          weighted_l1_box_penalty ω α y ≠ ⊥ := by
      intro y hy
      rw [weighted_l1_box_penalty_eq_weighted_sum_of_mem_effective_domain (ω := ω) (α := α) hy]
      exact EReal.coe_ne_bot _
    refine (is_convex_function_iff_convexOn_toReal hne_bot).2 ?_
    simpa [heff] using hconv_box
  have hclosed : LowerSemicontinuous (weighted_l1_box_penalty ω α) := by
    -- Lower semicontinuity comes from adding the continuous weighted sum and the closed-box
    -- indicator.
    have hrepr :
        weighted_l1_box_penalty ω α = fun y ↦ (g y : EReal) + extendedIndicator B y := by
      funext y
      rw [weighted_l1_box_penalty_apply]
    rw [hrepr]
    refine hg_closed.add' hind_closed ?_
    intro y
    exact EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  exact ⟨hproper, hclosed, hconv⟩

/-- Helper for Example 6.34: positive scaling of the weighted box penalty only rescales the
weights; the box indicator is unchanged because the multiplier is strictly positive. -/
lemma smul_weighted_l1_box_penalty_eq_scaled_weights_of_pos
    (lam : NNReal) (hlam : 0 < lam) :
    ((lam : EReal) • weighted_l1_box_penalty ω α) =
      weighted_l1_box_penalty (fun i ↦ lam * ω i) α := by
  funext y
  -- Separate the finite-box and outside-box cases so the indicator term can be simplified
  -- deterministically.
  rw [Pi.smul_apply, smul_eq_mul, weighted_l1_box_penalty_apply, weighted_l1_box_penalty_apply]
  by_cases hy : ∀ i, ENNReal.ofReal |y i| ≤ α i
  · have hsum_real :
        (lam : ℝ) * (∑ i, (ω i : ℝ) * |y i|) =
          ∑ i, (((lam * ω i : NNReal) : ℝ) * |y i|) := by
        simp [Finset.mul_sum, mul_assoc]
    simp [extendedIndicator, hy]
    simpa [EReal.coe_mul] using
      congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hsum_real
  · simp [extendedIndicator, hy]
    simpa using EReal.coe_mul_top_of_pos (show 0 < (lam : ℝ) by exact_mod_cast hlam)

-- Proof sketch: rewrite the weighted-box constraint set as the `β`-sublevel set of
-- `weighted_l1_box_penalty ω α` using
-- `weighted_l1_box_constraint_set_eq_sublevel_weighted_l1_box_penalty`. For `λ > 0`, specialize
-- the generic level-set residual from Theorem 6.30 and identify its scaled proximal singleton
-- using Example 6.23 applied to the scaled weight family `fun i ↦ lam * ω i`. The excluded
-- endpoint `λ = 0` is handled separately by projection onto `effective_domain
-- (weighted_l1_box_penalty ω α)`.
/-- On the positive-multiplier branch, the explicit root function agrees with the generic
level-set residual for the weighted box penalty owner. -/
theorem weightedL1BoxProjectionRootFunction_eq_level_set_projection_residual_of_pos
    (x : E) (lam : NNReal) (hlam : 0 < lam) :
    level_set_projection_residual (weighted_l1_box_penalty ω α) β x lam =
      (weightedL1BoxProjectionRootFunction ω α β x lam : EReal) := by
  let y : E := 𝓢[(fun i ↦ lam * ω i), α] x
  have hscaled :
      ((lam : EReal) • weighted_l1_box_penalty ω α) =
        weighted_l1_box_penalty (fun i ↦ lam * ω i) α :=
    smul_weighted_l1_box_penalty_eq_scaled_weights_of_pos (ω := ω) (α := α) lam hlam
  have hprox :
      prox[((lam : EReal) • weighted_l1_box_penalty ω α)] x = {y} := by
    -- The positive scaling turns the prox problem into Example 6.23 with scaled weights.
    simpa [hscaled, y] using
      prox_weighted_l1_box_penalty_eq_singleton_twoSidedSoftThreshold
        (ω := fun i ↦ lam * ω i) (α := α) (x := x)
  have hy_eff : y ∈ effective_domain (weighted_l1_box_penalty ω α) := by
    -- The thresholded point remains in the box, so the indicator part vanishes there.
    rw [mem_effective_domain_weighted_l1_box_penalty_iff]
    exact twoSidedSoftThreshold_mem_effective_box
      (ω := fun i ↦ lam * ω i) (α := α) (x := x)
  calc
    level_set_projection_residual (weighted_l1_box_penalty ω α) β x lam =
        weighted_l1_box_penalty ω α y - β := by
          simpa [y] using
            level_set_projection_residual_eq_of_scaled_prox_eq_singleton
              (weighted_l1_box_penalty ω α) β x (lam : ℝ) y hprox
    _ = (((∑ i, (ω i : ℝ) * |y i| : ℝ) - β : ℝ) : EReal) := by
      rw [weighted_l1_box_penalty_eq_weighted_sum_of_mem_effective_domain
        (ω := ω) (α := α) hy_eff]
      simp [EReal.coe_sub]
    _ = (weightedL1BoxProjectionRootFunction ω α β x lam : EReal) := by
      simp [weightedL1BoxProjectionRootFunction, y]

-- Proof sketch: use the coordinatewise clipped-radius formula to see that each
-- `|S_{λω, α}(x)_i|` is antitone in `λ`, then sum with nonnegative weights.
/-- The root function `λ ↦ ωᵀ |S_{λω, α}(x)| - β` is nonincreasing on the positive multipliers. -/
theorem weightedL1BoxProjectionRootFunction_antitoneOn_pos
    (x : E)
    : AntitoneOn (weightedL1BoxProjectionRootFunction ω α β x) (Set.Ioi 0) := by
  intro lam₁ hlam₁ lam₂ hlam₂ hle
  -- Sum the coordinatewise antitone inequalities with the nonnegative weights.
  have hsum :
      ∑ i, (ω i : ℝ) * |𝓢[(fun j ↦ lam₂ * ω j), α] x i| ≤
        ∑ i, (ω i : ℝ) * |𝓢[(fun j ↦ lam₁ * ω j), α] x i| := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hcoord :=
      abs_twoSidedSoftThreshold_apply_antitone (ω := ω) (α := α) (x := x) (i := i) hle
    have hω : 0 ≤ (ω i : ℝ) := by
      exact_mod_cast (ω i).2
    exact mul_le_mul_of_nonneg_left hcoord hω
  simpa [weightedL1BoxProjectionRootFunction] using sub_le_sub_right hsum β

-- Proof sketch: the same coordinatewise monotonicity argument used on `(0, ∞)` also handles
-- the endpoint `0`, since the magnitudes `|S_{λω, α}(x)_i|` remain antitone for all
-- `λ ≥ 0`.
/-- The root function `λ ↦ ωᵀ |S_{λω, α}(x)| - β` is nonincreasing. -/
theorem weightedL1BoxProjectionRootFunction_antitone
    (x : E)
    : Antitone (weightedL1BoxProjectionRootFunction ω α β x) := by
  intro lam₁ lam₂ hle
  -- The coordinatewise clipped-radius comparison works on all `NNReal`, including `λ = 0`.
  have hsum :
      ∑ i, (ω i : ℝ) * |𝓢[(fun j ↦ lam₂ * ω j), α] x i| ≤
        ∑ i, (ω i : ℝ) * |𝓢[(fun j ↦ lam₁ * ω j), α] x i| := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hcoord :=
      abs_twoSidedSoftThreshold_apply_antitone (ω := ω) (α := α) (x := x) (i := i) hle
    have hω : 0 ≤ (ω i : ℝ) := by
      exact_mod_cast (ω i).2
    exact mul_le_mul_of_nonneg_left hcoord hω
  simpa [weightedL1BoxProjectionRootFunction] using sub_le_sub_right hsum β

-- Proof sketch: let `y = 𝓢[(fun _ ↦ 0), α] x`. Then `y` is the projection of `x` onto
-- `effective_domain (weighted_l1_box_penalty ω α)`, i.e. onto the symmetric box. The hypothesis
-- `φ 0 ≤ 0` says exactly that this box projection already lies in `C`, so Theorem 6.30(1)
-- identifies the projection onto `C` with the projection onto
-- `effective_domain (weighted_l1_box_penalty ω α)`.
/-- Example 6.34, feasible branch: if the residual at `λ = 0` is nonpositive, then the clipped
box projection already satisfies the weighted `ℓ¹` constraint and is the unique projected point. -/
theorem projection_mapping_weighted_l1_box_constraint_set_eq_singleton_of_residual_nonpos
    (x : E) (hres : weightedL1BoxProjectionRootFunction ω α β x 0 ≤ 0) :
    P[C] x =
      {𝓢[(fun _ ↦ 0), α] x} := by
  let y : E := 𝓢[(fun _ ↦ 0), α] x
  have hproper :
      IsProperExtendedRealFunction (weighted_l1_box_penalty ω α) :=
    (weighted_l1_box_penalty_proper_closed_convex (ω := ω) (α := α)).1
  have hdom_nonempty :
      (effective_domain (weighted_l1_box_penalty ω α)).Nonempty :=
    hproper.effective_domain_nonempty
  have hproj_eff :
      P[effective_domain (weighted_l1_box_penalty ω α)] x = {y} := by
    -- At zero weights, Example 6.23 reduces the box prox to the ordinary box projection.
    calc
      P[effective_domain (weighted_l1_box_penalty ω α)] x =
          prox[extendedIndicator (effective_domain (weighted_l1_box_penalty ω α))] x := by
            symm
            exact prox_extendedIndicator_eq_projection_mapping
              (effective_domain (weighted_l1_box_penalty ω α)) hdom_nonempty x
      _ = prox[weighted_l1_box_penalty (fun _ ↦ (0 : NNReal)) α] x := by
            rw [weighted_l1_box_penalty_zero_weights_eq_extendedIndicator_effective_domain
              (ω := ω) (α := α)]
      _ = {y} := by
            simpa [y] using
              prox_weighted_l1_box_penalty_eq_singleton_twoSidedSoftThreshold
                (ω := fun _ ↦ (0 : NNReal)) (α := α) (x := x)
  have hproj_nonempty : (P[effective_domain (weighted_l1_box_penalty ω α)] x).Nonempty := by
    rw [hproj_eff]
    exact Set.singleton_nonempty y
  have hy_eff : y ∈ effective_domain (weighted_l1_box_penalty ω α) := by
    -- The zero-threshold point is still in the box, so it belongs to the effective domain.
    rw [mem_effective_domain_weighted_l1_box_penalty_iff]
    exact twoSidedSoftThreshold_mem_effective_box
      (ω := fun _ ↦ (0 : NNReal)) (α := α) (x := x)
  have hy_sum_le :
      ∑ i, (ω i : ℝ) * |y i| ≤ β := by
    simpa [weightedL1BoxProjectionRootFunction, y] using hres
  have hy_sublevel :
      y ∈ (weighted_l1_box_penalty ω α) ⁻¹' Set.Iic (β : EReal) := by
    -- The residual hypothesis says that the box projection already satisfies the weighted `ℓ¹`
    -- bound.
    change weighted_l1_box_penalty ω α y ≤ (β : EReal)
    rw [weighted_l1_box_penalty_eq_weighted_sum_of_mem_effective_domain
      (ω := ω) (α := α) hy_eff]
    exact_mod_cast hy_sum_le
  have hproj_sublevel :
      P[effective_domain (weighted_l1_box_penalty ω α)] x ⊆
        (weighted_l1_box_penalty ω α) ⁻¹' Set.Iic (β : EReal) := by
    intro z hz
    rw [hproj_eff] at hz
    have hz' : z = y := by simpa using hz
    simpa [hz'] using hy_sublevel
  calc
    P[C] x = P[(weighted_l1_box_penalty ω α) ⁻¹' Set.Iic (β : EReal)] x := by
      rw [weighted_l1_box_constraint_set_eq_sublevel_weighted_l1_box_penalty]
    _ = P[effective_domain (weighted_l1_box_penalty ω α)] x := by
      exact projection_mapping_sublevel_eq_projection_effective_domain_of_projection_mem_sublevel
        (weighted_l1_box_penalty ω α) β x hproj_nonempty hproj_sublevel
    _ = {y} := hproj_eff

-- Proof sketch: if `φ 0 > 0`, then the clipped box projection violates the active weighted `ℓ¹`
-- constraint. If `φ lam = 0`, then `lam ≠ 0`, hence `0 < lam` in `NNReal`. The positive-branch
-- bridge `weightedL1BoxProjectionRootFunction_eq_level_set_projection_residual_of_pos` converts
-- the source-facing root equation to the generic residual equation from Theorem 6.30, and the
-- projected point is the thresholded point `S_{λω, α}(x)`.
/-- Example 6.34, active branch: if the residual at `λ = 0` is positive and `λ` is a root of
`φ(λ) = ωᵀ |S_{λω, α}(x)| - β`, then `λ` is automatically positive and the set-valued projection
onto the weighted box-constrained set is the singleton `{S_{λω, α}(x)}`. Together with
`projection_mapping_weighted_l1_box_constraint_set_eq_singleton_of_residual_nonpos`, this gives
the textbook piecewise formula for `P_C(x)`. -/
theorem projection_mapping_weighted_l1_box_constraint_set_eq_singleton_of_root
    (x : E) (lam : NNReal)
    (hactive : 0 < weightedL1BoxProjectionRootFunction ω α β x 0)
    (hroot : weightedL1BoxProjectionRootFunction ω α β x lam = 0) :
    P[C] x =
      {𝓢[(fun i ↦ lam * ω i), α] x} := by
  have hlam_ne : lam ≠ 0 := by
    intro hlam
    have hzero_root : weightedL1BoxProjectionRootFunction ω α β x 0 = 0 := by
      simpa [hlam] using hroot
    exact ne_of_gt hactive hzero_root
  have hlam : 0 < lam := lt_of_le_of_ne lam.2 (by simpa [eq_comm] using hlam_ne)
  let lamPos : PosReal := ⟨(lam : ℝ), by exact_mod_cast hlam⟩
  have hresidual :
      level_set_projection_residual (weighted_l1_box_penalty ω α) β x (lam : ℝ) = 0 := by
    calc
      level_set_projection_residual (weighted_l1_box_penalty ω α) β x lam =
          (weightedL1BoxProjectionRootFunction ω α β x lam : EReal) :=
            weightedL1BoxProjectionRootFunction_eq_level_set_projection_residual_of_pos
              (ω := ω) (α := α) (β := β) x lam hlam
      _ = 0 := by
        exact_mod_cast hroot
  rcases weighted_l1_box_penalty_proper_closed_convex (ω := ω) (α := α) with
    ⟨hf_proper, hf_closed, hf_convex⟩
  calc
    P[C] x = P[(weighted_l1_box_penalty ω α) ⁻¹' Set.Iic (β : EReal)] x := by
      rw [weighted_l1_box_constraint_set_eq_sublevel_weighted_l1_box_penalty]
    _ = prox[((lamPos : EReal) • weighted_l1_box_penalty ω α)] x := by
      exact projection_mapping_sublevel_eq_scaled_prox_of_level_set_projection_residual_eq_zero
        (weighted_l1_box_penalty ω α) β hf_proper hf_closed hf_convex x lamPos hresidual
    _ = prox[weighted_l1_box_penalty (fun i ↦ lam * ω i) α] x := by
      simpa [lamPos] using congrArg (fun f : E → EReal ↦ prox[f] x)
        (smul_weighted_l1_box_penalty_eq_scaled_weights_of_pos
          (ω := ω) (α := α) lam hlam)
    _ = {𝓢[(fun i ↦ lam * ω i), α] x} := by
      simpa using
        prox_weighted_l1_box_penalty_eq_singleton_twoSidedSoftThreshold
          (ω := fun i ↦ lam * ω i) (α := α) (x := x)

-- Proof sketch: split on whether the clipped box projection already satisfies the weighted `ℓ¹`
-- constraint, detected by the sign of `φ 0`. In the feasible branch use
-- `projection_mapping_weighted_l1_box_constraint_set_eq_singleton_of_residual_nonpos`; otherwise
-- use `projection_mapping_weighted_l1_box_constraint_set_eq_singleton_of_root` with the supplied
-- root of `φ`.
/-- Example 6.34: the projection onto the weighted `ℓ¹`-plus-box set is given by the textbook
piecewise rule determined by the root function `φ(λ) = ωᵀ |S_{λω, α}(x)| - β`. If `φ(0) ≤ 0`,
the clipped point `S_{0, α}(x)` is already feasible and is the projection. Otherwise, any
multiplier `λ` with `φ(λ) = 0` yields the active-constraint projection `S_{λω, α}(x)`. -/
theorem projection_mapping_weighted_l1_box_constraint_set_eq_singleton_piecewise
    (x : E) (lam : NNReal)
    (hroot : 0 < weightedL1BoxProjectionRootFunction ω α β x 0 →
      weightedL1BoxProjectionRootFunction ω α β x lam = 0) :
    P[C] x =
      {if weightedL1BoxProjectionRootFunction ω α β x 0 ≤ 0 then
        𝓢[(fun _ ↦ 0), α] x
      else
        𝓢[(fun i ↦ lam * ω i), α] x} := by
  by_cases hres : weightedL1BoxProjectionRootFunction ω α β x 0 ≤ 0
  · -- In the feasible branch, the box projection already lies in the weighted `ℓ¹` sublevel.
    simpa [hres] using
      projection_mapping_weighted_l1_box_constraint_set_eq_singleton_of_residual_nonpos
        (ω := ω) (α := α) (β := β) x hres
  · -- Otherwise the supplied root triggers the active branch of Theorem 6.30.
    have hactive : 0 < weightedL1BoxProjectionRootFunction ω α β x 0 := lt_of_not_ge hres
    simpa [hres] using
      projection_mapping_weighted_l1_box_constraint_set_eq_singleton_of_root
        (ω := ω) (α := α) (β := β) x lam hactive (hroot hactive)

end

end

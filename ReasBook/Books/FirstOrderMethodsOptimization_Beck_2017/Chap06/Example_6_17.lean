/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 6.17 is `source-facing`: the public content is the proximal formula for the rank-one
penalty `u ↦ |⟪a, u⟫|`, stated directly on the chapter owner `prox[...]`. Domain sampling against
Lemma 6.5, Proposition 6.2.2, and Theorem 6.15 shows that the primitive source data are the
vector `a`, its nonzeroness needed for the displayed denominator `‖a‖²`, and the evaluation point
`x`. The `core/canonical` owners are the rank-one functional `innerSL ℝ a`, the scalar penalty
`absolute_value_penalty 1`, and the affine-composition transport theorem
`proximal_mapping_precompose_continuousAffineMap`; properness of `absolute_value_penalty 1` is
derived proof data rather than primitive public data. The displayed correction term remains the
source-facing textbook singleton formula, obtained by specializing those owners rather than by
introducing a parallel local wrapper. -/

/-- Evaluating the canonical rank-one absolute-value penalty owner gives the textbook scalar
formula `u ↦ |⟪a, u⟫|`. -/
@[simp] theorem absolute_value_penalty_one_comp_innerSL_apply (a u : E) :
    (absolute_value_penalty 1 ∘ innerSL ℝ a) u = ((|⟪a, u⟫| : ℝ) : EReal) := by
  simp [absolute_value_penalty_apply]

/-- Helper for Example 6.17: the canonical affine section of the rank-one map `u ↦ ⟪a, u⟫`
through the base point `x`. -/
def rank_one_section (a x : E) (α z : ℝ) : E :=
  x + (((z - ⟪a, x⟫) / α) • a)

/-- Helper for Example 6.17: the canonical rank-one section sends the scalar coordinate `z`
back to a point whose inner product with `a` is exactly `z`. -/
lemma inner_rank_one_section_eq (a x : E) (ha : a ≠ 0) (z : ℝ) :
    ⟪a, rank_one_section a x (‖a‖ ^ 2) z⟫ = z := by
  have hα : ‖a‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  -- Expand the section and collapse the rank-one correction with `⟪a, a⟫ = ‖a‖²`.
  calc
    ⟪a, rank_one_section a x (‖a‖ ^ 2) z⟫
        = ⟪a, x⟫ + ((z - ⟪a, x⟫) / (‖a‖ ^ 2)) * ⟪a, a⟫ := by
            simp [rank_one_section, inner_add_right, real_inner_smul_right]
    _ = ⟪a, x⟫ + ((z - ⟪a, x⟫) / (‖a‖ ^ 2)) * (‖a‖ ^ 2) := by
            rw [real_inner_self_eq_norm_sq]
    _ = z := by
            field_simp [hα]
            ring

/-- Helper for Example 6.17: every displacement `u - x` splits orthogonally into the section
correction and a residual orthogonal to `a`. -/
lemma rank_one_section_norm_sq_split (a x u : E) (ha : a ≠ 0) :
    ‖u - x‖ ^ (2 : ℕ) =
      ‖rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫ - x‖ ^ (2 : ℕ) +
        ‖u - rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫‖ ^ (2 : ℕ) := by
  let c : E := (((⟪a, u⟫ - ⟪a, x⟫) / (‖a‖ ^ 2)) • a)
  let r : E := u - rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫
  have horth : inner ℝ c r = 0 := by
    have hr : inner ℝ a r = 0 := by
      -- The residual stays in the kernel of the rank-one functional.
      calc
        inner ℝ a r = ⟪a, u⟫ - ⟪a, rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫⟫ := by
            simp [r, inner_sub_right]
        _ = 0 := by
            simp [inner_rank_one_section_eq a x ha ⟪a, u⟫]
    -- Orthogonality follows because `c` is a scalar multiple of `a`.
    calc
      inner ℝ c r = ((⟪a, u⟫ - ⟪a, x⟫) / (‖a‖ ^ 2)) * inner ℝ a r := by
          rw [show c = (((⟪a, u⟫ - ⟪a, x⟫) / (‖a‖ ^ 2)) • a) by rfl, real_inner_smul_left]
      _ = 0 := by simp [hr]
  have hdecomp : u - x = c + r := by
    -- This is the explicit affine-fiber decomposition around the section point.
    simp [c, r, rank_one_section, sub_eq_add_neg, add_left_comm, add_comm]
  have hsplit :
      ‖u - x‖ ^ (2 : ℕ) = ‖c‖ ^ (2 : ℕ) + ‖r‖ ^ (2 : ℕ) := by
    -- Apply the real Pythagorean identity to the orthogonal decomposition.
    calc
      ‖u - x‖ ^ (2 : ℕ) = ‖c + r‖ ^ (2 : ℕ) := by rw [hdecomp]
      _ = ‖c‖ ^ (2 : ℕ) + 2 * inner ℝ c r + ‖r‖ ^ (2 : ℕ) := norm_add_sq_real _ _
      _ = ‖c‖ ^ (2 : ℕ) + ‖r‖ ^ (2 : ℕ) := by simp [horth]
  have hc_eq : rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫ - x = c := by
    simp [rank_one_section, c]
  simpa [r, hc_eq] using hsplit

/-- Helper for Example 6.17: on the canonical section, the scalar proximal objective for
`absolute_value_penalty (‖a‖²)` is the vector proximal objective scaled by `‖a‖²`. -/
lemma proximal_objective_abs_inner_on_section (a x : E) (ha : a ≠ 0) (z : ℝ) :
    proximal_objective (absolute_value_penalty (‖a‖ ^ 2)) ⟪a, x⟫ z =
      (((‖a‖ ^ 2 : ℝ) : EReal) *
        proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
          (rank_one_section a x (‖a‖ ^ 2) z)) := by
  have hα : ‖a‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  have hs_nonneg : 0 ≤ ((‖a‖ ^ 2 : ℝ) : EReal) := by
    exact_mod_cast sq_nonneg ‖a‖
  have hs_top : ((‖a‖ ^ 2 : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hquad :
      ((((1 / 2 : ℝ) * ‖z - ⟪a, x⟫‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        (((‖a‖ ^ 2 : ℝ) : EReal) *
          (((((1 / 2 : ℝ) * ‖rank_one_section a x (‖a‖ ^ 2) z - x‖ ^ (2 : ℕ)) : ℝ)) :
            EReal)) := by
    -- The section displacement is exactly the scaled rank-one correction along `a`.
    exact_mod_cast (show ((1 / 2 : ℝ) * ‖z - ⟪a, x⟫‖ ^ (2 : ℕ)) =
      (‖a‖ ^ 2) * ((1 / 2 : ℝ) * ‖rank_one_section a x (‖a‖ ^ 2) z - x‖ ^ (2 : ℕ)) by
      rw [show rank_one_section a x (‖a‖ ^ 2) z - x = (((z - ⟪a, x⟫) / (‖a‖ ^ 2)) • a) by
            simp [rank_one_section]]
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs]
      rw [pow_two, mul_pow, sq_abs, pow_two]
      field_simp [hα])
  have hsection :
      absolute_value_penalty 1 z +
          (((((1 / 2 : ℝ) * ‖rank_one_section a x (‖a‖ ^ 2) z - x‖ ^ (2 : ℕ)) : ℝ)) : EReal) =
        proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
          (rank_one_section a x (‖a‖ ^ 2) z) := by
    -- On the section, the penalty term becomes `|z|`.
    rw [proximal_objective_apply, absolute_value_penalty_one_comp_innerSL_apply,
      inner_rank_one_section_eq a x ha z]
    simp [absolute_value_penalty_apply]
  calc
    proximal_objective (absolute_value_penalty (‖a‖ ^ 2)) ⟪a, x⟫ z
        = (((‖a‖ ^ 2 : ℝ) : EReal) * absolute_value_penalty 1 z) +
            ((((1 / 2 : ℝ) * ‖z - ⟪a, x⟫‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
              simp [proximal_objective_apply, absolute_value_penalty_apply]
    _ = (((‖a‖ ^ 2 : ℝ) : EReal) * absolute_value_penalty 1 z) +
          (((‖a‖ ^ 2 : ℝ) : EReal) *
            (((((1 / 2 : ℝ) * ‖rank_one_section a x (‖a‖ ^ 2) z - x‖ ^ (2 : ℕ)) : ℝ)) :
              EReal)) := by
            rw [hquad]
    _ = (((‖a‖ ^ 2 : ℝ) : EReal) *
          (absolute_value_penalty 1 z +
            (((((1 / 2 : ℝ) * ‖rank_one_section a x (‖a‖ ^ 2) z - x‖ ^ (2 : ℕ)) : ℝ)) :
              EReal))) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top hs_nonneg hs_top]
    _ = (((‖a‖ ^ 2 : ℝ) : EReal) *
          proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
            (rank_one_section a x (‖a‖ ^ 2) z)) := by
            rw [hsection]

/-- Helper for Example 6.17: the vector proximal objective splits into its value on the canonical
section plus a nonnegative residual quadratic term. -/
lemma proximal_objective_abs_inner_split (a x u : E) (ha : a ≠ 0) :
    proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x u =
      proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
        (rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫) +
      (((((1 / 2 : ℝ) * ‖u - rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫‖ ^ (2 : ℕ)) : ℝ)) :
        EReal) := by
  -- Rewrite the penalty term through the section identity and then split the norm square.
  rw [proximal_objective_apply, proximal_objective_apply,
    absolute_value_penalty_one_comp_innerSL_apply, absolute_value_penalty_one_comp_innerSL_apply,
    inner_rank_one_section_eq a x ha ⟪a, u⟫]
  have hquad :
      ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        (((((1 / 2 : ℝ) * ‖rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫ - x‖ ^ (2 : ℕ)) : ℝ)) :
          EReal) +
          (((((1 / 2 : ℝ) * ‖u - rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫‖ ^ (2 : ℕ)) : ℝ)) :
            EReal) := by
    have hquad_real :
        ((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) =
          (1 / 2 : ℝ) * ‖rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫ - x‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) * ‖u - rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫‖ ^ (2 : ℕ) := by
      nlinarith [rank_one_section_norm_sq_split a x u ha]
    exact_mod_cast hquad_real
  rw [hquad]
  simp [add_left_comm, add_comm]

/-- Helper for Example 6.17: projecting to the canonical section cannot increase the pullback
proximal objective. -/
lemma rank_one_section_objective_le (a x u : E) (ha : a ≠ 0) :
    proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
        (rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫) ≤
      proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x u := by
  have hnonneg_real :
      0 ≤ (1 / 2 : ℝ) * ‖u - rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫‖ ^ (2 : ℕ) := by
    positivity
  have hnonneg :
      (0 : EReal) ≤
        (((((1 / 2 : ℝ) * ‖u - rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫‖ ^ (2 : ℕ)) : ℝ)) :
          EReal) := by
    exact_mod_cast hnonneg_real
  -- The split lemma isolates the residual as an explicitly nonnegative term.
  rw [proximal_objective_abs_inner_split a x u ha]
  exact le_add_of_nonneg_right hnonneg

/-- Helper for Example 6.17: a proximal minimizer of the pullback objective maps to a proximal
minimizer of the scalar objective under `u ↦ ⟪a, u⟫`. -/
lemma pullback_minimizer_maps_to_scalar_minimizer (a x u : E) (ha : a ≠ 0)
    (hu : u ∈ prox[absolute_value_penalty 1 ∘ innerSL ℝ a] x) :
    ⟪a, u⟫ ∈ prox[absolute_value_penalty (‖a‖ ^ 2)] ⟪a, x⟫ := by
  have hs_nonneg : 0 ≤ ((‖a‖ ^ 2 : ℝ) : EReal) := by
    exact_mod_cast sq_nonneg ‖a‖
  rw [mem_proximal_mapping_iff] at hu ⊢
  rw [isMinOn_univ_iff] at hu ⊢
  intro z
  have huz :
      proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x u ≤
        proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
          (rank_one_section a x (‖a‖ ^ 2) z) := hu _
  -- Compare the scalar objectives through the section formula and the section contraction.
  calc
    proximal_objective (absolute_value_penalty (‖a‖ ^ 2)) ⟪a, x⟫ ⟪a, u⟫
        = (((‖a‖ ^ 2 : ℝ) : EReal) *
            proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
              (rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫)) :=
            proximal_objective_abs_inner_on_section a x ha ⟪a, u⟫
    _ ≤ (((‖a‖ ^ 2 : ℝ) : EReal) *
          proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x u) :=
            mul_le_mul_of_nonneg_left (rank_one_section_objective_le a x u ha) hs_nonneg
    _ ≤ (((‖a‖ ^ 2 : ℝ) : EReal) *
          proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
            (rank_one_section a x (‖a‖ ^ 2) z)) :=
          mul_le_mul_of_nonneg_left huz hs_nonneg
    _ = proximal_objective (absolute_value_penalty (‖a‖ ^ 2)) ⟪a, x⟫ z := by
          symm
          exact proximal_objective_abs_inner_on_section a x ha z

/-- Helper for Example 6.17: any pullback proximal minimizer must already lie on the canonical
rank-one section above its scalar coordinate. -/
lemma pullback_minimizer_eq_rank_one_section (a x u : E) (ha : a ≠ 0)
    (hu : u ∈ prox[absolute_value_penalty 1 ∘ innerSL ℝ a] x) :
    u = rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫ := by
  let Tu : E := rank_one_section a x (‖a‖ ^ 2) ⟪a, u⟫
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
  have hu_le :
      proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x u ≤
        proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x Tu := hu Tu
  have hreal :
      |⟪a, u⟫| + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤
        |⟪a, u⟫| + (1 / 2 : ℝ) * ‖Tu - x‖ ^ (2 : ℕ) := by
    -- The penalty terms agree at `u` and its section point, so only the norm terms remain.
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [Tu, proximal_objective_apply, absolute_value_penalty_one_comp_innerSL_apply,
        inner_rank_one_section_eq a x ha ⟪a, u⟫] using hu_le
  have hsq_le : ‖u - x‖ ^ (2 : ℕ) ≤ ‖Tu - x‖ ^ (2 : ℕ) := by
    nlinarith
  have hres_zero : ‖u - Tu‖ ^ (2 : ℕ) = 0 := by
    -- Combined with the orthogonal norm split, the residual square must vanish.
    nlinarith [rank_one_section_norm_sq_split a x u ha]
  have hnorm_zero : ‖u - Tu‖ = 0 := eq_zero_of_pow_eq_zero hres_zero
  have hu_eq_Tu : u - Tu = 0 := norm_eq_zero.mp hnorm_zero
  exact sub_eq_zero.mp hu_eq_Tu

/-- Helper for Example 6.17: a scalar proximal minimizer lifts through the canonical section to a
pullback proximal minimizer. -/
lemma scalar_minimizer_lifts_to_pullback_minimizer (a x : E) (ha : a ≠ 0) (z : ℝ)
    (hz : z ∈ prox[absolute_value_penalty (‖a‖ ^ 2)] ⟪a, x⟫) :
    rank_one_section a x (‖a‖ ^ 2) z ∈ prox[absolute_value_penalty 1 ∘ innerSL ℝ a] x := by
  have hs_nonneg : 0 ≤ ((‖a‖ ^ 2 : ℝ) : EReal) := by
    exact_mod_cast sq_nonneg ‖a‖
  have hs_top : ((‖a‖ ^ 2 : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hs_bot : ((‖a‖ ^ 2 : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hs_zero : ((‖a‖ ^ 2 : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  rw [mem_proximal_mapping_iff] at hz ⊢
  rw [isMinOn_univ_iff] at hz ⊢
  intro v
  have hscaled :
      (((‖a‖ ^ 2 : ℝ) : EReal) *
        proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
          (rank_one_section a x (‖a‖ ^ 2) z)) ≤
        (((‖a‖ ^ 2 : ℝ) : EReal) *
          proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x v) := by
    -- Compare scalar minimizers first, then return to the pullback objective and divide by `‖a‖²`.
    calc
      (((‖a‖ ^ 2 : ℝ) : EReal) *
          proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
            (rank_one_section a x (‖a‖ ^ 2) z)) =
          proximal_objective (absolute_value_penalty (‖a‖ ^ 2)) ⟪a, x⟫ z :=
            (proximal_objective_abs_inner_on_section a x ha z).symm
      _ ≤ proximal_objective (absolute_value_penalty (‖a‖ ^ 2)) ⟪a, x⟫ ⟪a, v⟫ := hz ⟪a, v⟫
      _ = (((‖a‖ ^ 2 : ℝ) : EReal) *
            proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
              (rank_one_section a x (‖a‖ ^ 2) ⟪a, v⟫)) :=
            proximal_objective_abs_inner_on_section a x ha ⟪a, v⟫
      _ ≤ (((‖a‖ ^ 2 : ℝ) : EReal) *
            proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x v) :=
          mul_le_mul_of_nonneg_left (rank_one_section_objective_le a x v ha) hs_nonneg
  have hdiv :
      ((((‖a‖ ^ 2 : ℝ) : EReal) *
          proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
            (rank_one_section a x (‖a‖ ^ 2) z)) / ((‖a‖ ^ 2 : ℝ) : EReal)) ≤
        ((((‖a‖ ^ 2 : ℝ) : EReal) *
            proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x v) /
            ((‖a‖ ^ 2 : ℝ) : EReal)) :=
    EReal.monotone_div_right_of_nonneg hs_nonneg hscaled
  rw [mul_comm (((‖a‖ ^ 2 : ℝ) : EReal))
        (proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x
          (rank_one_section a x (‖a‖ ^ 2) z)),
    mul_comm (((‖a‖ ^ 2 : ℝ) : EReal))
      (proximal_objective (absolute_value_penalty 1 ∘ innerSL ℝ a) x v),
    ← EReal.mul_div_right,
    ← EReal.mul_div_right,
    EReal.div_mul_cancel hs_bot hs_top hs_zero,
    EReal.div_mul_cancel hs_bot hs_top hs_zero] at hdiv
  exact hdiv

/-- Helper for Example 6.17: the pullback proximal set is exactly the image of the scalar proximal
set under the canonical rank-one section. -/
theorem prox_abs_inner_eq_image_scalar_prox (a x : E) (ha : a ≠ 0) :
    prox[absolute_value_penalty 1 ∘ innerSL ℝ a] x =
      (fun z : ℝ ↦ rank_one_section a x (‖a‖ ^ 2) z) ''
        prox[absolute_value_penalty (‖a‖ ^ 2)] ⟪a, x⟫ := by
  ext u
  constructor
  · intro hu
    rw [Set.mem_image]
    refine ⟨⟪a, u⟫, pullback_minimizer_maps_to_scalar_minimizer a x u ha hu, ?_⟩
    simpa using (pullback_minimizer_eq_rank_one_section a x u ha hu).symm
  · rintro ⟨z, hz, rfl⟩
    exact scalar_minimizer_lifts_to_pullback_minimizer a x ha z hz

-- Conceptual route: work on the rank-one scalar coordinate `z = ⟪a, u⟫`, lift scalar minimizers
-- through the canonical section, and then apply Lemma 6.5(2) to identify the scalar proximal set
-- with the soft-thresholding singleton.
/-- Example 6.17: on a real inner product space, for
`f = absolute_value_penalty 1 ∘ innerSL ℝ a`, equivalently `f(u) = |⟪a, u⟫|`,
if `a ≠ 0`, then the proximal mapping at `x` is the singleton containing the soft-thresholding
correction `x + ((𝒯[‖a‖^2] ⟪a, x⟫ - ⟪a, x⟫) / ‖a‖^2) a`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook formula for `|aᵀ x|` on `ℝ^n`. The
nonzeroness hypothesis is mathematically active here because the displayed coefficient divides by
`‖a‖^2`; without it, the written source formula would rely on Lean's totalized division by zero
rather than on the textbook expression itself. -/
theorem prox_abs_inner_eq_singleton_soft_thresholding_correction
    (a x : E) (ha : a ≠ 0) :
    prox[absolute_value_penalty 1 ∘ innerSL ℝ a] x =
      {x + (((𝒯[‖a‖ ^ 2] ⟪a, x⟫ - ⟪a, x⟫) / ‖a‖ ^ 2) • a)} := by
  -- Route correction: Theorem 6.15 packages this pattern with adjoints, but this source-facing
  -- item has no `[CompleteSpace E]` hypothesis, so we execute the rank-one scalar-section proof
  -- directly in this file.
  calc
    prox[absolute_value_penalty 1 ∘ innerSL ℝ a] x
        = (fun z : ℝ ↦ rank_one_section a x (‖a‖ ^ 2) z) ''
            prox[absolute_value_penalty (‖a‖ ^ 2)] ⟪a, x⟫ :=
          prox_abs_inner_eq_image_scalar_prox a x ha
    _ = (fun z : ℝ ↦ rank_one_section a x (‖a‖ ^ 2) z) ''
          ({𝒯[‖a‖ ^ 2] ⟪a, x⟫} : Set ℝ) := by
            -- Lemma 6.5 identifies the scalar proximal set with soft thresholding.
            congr 1
            simpa using prox_absolute_value_penalty_eq_singleton_soft_thresholding
              (‖a‖ ^ 2) (sq_nonneg ‖a‖) ⟪a, x⟫
    _ = {rank_one_section a x (‖a‖ ^ 2) (𝒯[‖a‖ ^ 2] ⟪a, x⟫)} := by
          simp
    _ = {x + (((𝒯[‖a‖ ^ 2] ⟪a, x⟫ - ⟪a, x⟫) / ‖a‖ ^ 2) • a)} := by
          simp [rank_one_section]

end

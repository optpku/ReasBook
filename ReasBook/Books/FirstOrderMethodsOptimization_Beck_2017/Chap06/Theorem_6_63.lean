/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_4
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Pointwise
open AffineMap

/- Theorem 6.63 is `source-facing`: the chapter already owns the proximal mapping `prox[...]`, the
Moreau envelope `M[μ, f]`, and the proper/closed/convex singleton theorem
`prox_eq_singleton_of_proper_closed_convex`. Domain sampling therefore identifies the owner stack
for this item as:

- Definition 6.1's `prox[...]`,
- Definition 6.7's `M[μ, f]`,
- Theorem 6.3's `prox_eq_singleton_of_proper_closed_convex`, and
- mathlib's canonical affine owner `AffineMap.lineMap`.

This separates primitive data from derived API correctly. The primitive source-facing data are the
function `f`, the smoothing parameter `μ`, the base point `x`, and the proper/closed/convex
hypotheses that ensure the relevant proximal minimizers are attained and unique. The weaker bridge
statement below then takes as derived input a singleton computation for
`prox[((μ + 1 : ℝ) : EReal) • f] x`, together with the non-`⊥` hypothesis needed to rule out the
`⊥` pathology in Moreau-envelope calculus. What cannot remain as a public owner statement is the
bare affine-image identity for `prox[M[μ, f]]` under only `∀ y, f y ≠ ⊥`, because the scaled
proximal set can be empty while the Moreau-envelope proximal set is nonempty. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable (f : E → EReal) (μ : PosReal)

/-- Helper for Theorem 6.63: the outer penalized objective whose unique minimizer is the scaled
proximal point of `f` at `x`. -/
def outer_moreau_penalty (x : E) : E → EReal :=
  fun y ↦ f y +
    (((1 / (2 * ((μ + 1 : PosReal) : ℝ)) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal))

/-- Evaluating the outer penalty from Theorem 6.63 gives the expected sum of `f` and the
`(μ + 1)⁻¹` quadratic term. -/
@[simp] lemma outer_moreau_penalty_apply (x y : E) :
    outer_moreau_penalty (f := f) (μ := μ) x y =
      f y + (((1 / (2 * ((μ + 1 : PosReal) : ℝ)) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  rfl

/-- Helper for Theorem 6.63: adding a finite real constant commutes with the infimum defining a
Moreau envelope. -/
lemma iInf_add_real_eq (g : E → EReal) (c : ℝ) :
    (⨅ y, g y) + (c : EReal) = ⨅ y, g y + c := by
  let F : EReal → EReal × EReal := fun z ↦ (z, c)
  have hF : ContinuousAt F (⨅ y, g y) := by
    exact continuousAt_id.prodMk continuousAt_const
  have hAdd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (F (⨅ y, g y)) := by
    simpa [F] using
      EReal.continuousAt_add (p := (⨅ y, g y, (c : EReal)))
        (Or.inr (EReal.coe_ne_bot _))
        (Or.inr (EReal.coe_ne_top _))
  have hmono : Monotone (fun z : EReal ↦ z + c) := by
    intro a b hab
    simpa [add_comm] using add_le_add_left hab ((c : ℝ) : EReal)
  -- Pull the finite additive term through the infimum by monotone continuity of `z ↦ z + c`.
  simpa [F] using
    Monotone.map_ciInf_of_continuousAt (ContinuousAt.comp hAdd hF) hmono

/-- Helper for Theorem 6.63: the affine point minimizing the inner quadratic subproblem lies on the
segment from `x` to `y`, and its displacement from `y` is the expected scaled copy of `x - y`. -/
lemma lineMap_sub_right_for_moreau (x y : E) :
    lineMap x y (1 / (((μ + 1 : PosReal) : ℝ))) - y =
      ((μ : ℝ) / (((μ + 1 : PosReal) : ℝ))) • (x - y) := by
  -- Rewrite the affine interpolation point as `x + t • (y - x)` and collect coefficients.
  have hcoeff : 1 - (1 / (((μ + 1 : PosReal) : ℝ))) =
      ((μ : ℝ) / (((μ + 1 : PosReal) : ℝ))) := by
    have hpos : (0 : ℝ) < (((μ + 1 : PosReal) : ℝ)) := by
      simpa using add_pos μ.2 zero_lt_one
    have hden : (((μ + 1 : PosReal) : ℝ)) ≠ 0 := hpos.ne'
    field_simp [hden]
    simp
  rw [AffineMap.lineMap_apply_module']
  calc
    (1 / (((μ + 1 : PosReal) : ℝ))) • (y - x) + x - y
        = (1 - (1 / (((μ + 1 : PosReal) : ℝ)))) • (x - y) := by
            module
    _ = ((μ : ℝ) / (((μ + 1 : PosReal) : ℝ))) • (x - y) := by
        rw [hcoeff]

/-- Helper for Theorem 6.63: the same affine interpolation point has displacement from `x`
equal to the textbook weight `1 / (μ + 1)` times `y - x`. -/
lemma lineMap_sub_left_for_moreau (x y : E) :
    lineMap x y (1 / (((μ + 1 : PosReal) : ℝ))) - x =
      (1 / (((μ + 1 : PosReal) : ℝ))) • (y - x) := by
  -- This is the direct affine-line formula specialized to the module setting.
  rw [AffineMap.lineMap_apply_module']
  module

/-- Helper for Theorem 6.63: after evaluating the inner quadratic minimizer, the two endpoint
quadratic terms collapse to the single outer penalty `‖x - y‖² / (2 (μ + 1))`. -/
lemma scaled_square_factor_for_moreau (n : ℝ) :
    (1 / (2 * (μ : ℝ))) * (((μ : ℝ) / (((μ + 1 : PosReal) : ℝ)) * n) ^ (2 : ℕ)) +
      (1 / 2 : ℝ) * ((1 / (((μ + 1 : PosReal) : ℝ)) * n) ^ (2 : ℕ)) =
      (1 / (2 * (((μ + 1 : PosReal) : ℝ))) : ℝ) * n ^ (2 : ℕ) := by
  -- The coefficient identity is scalar algebra once the common factor `n²` is exposed.
  have hμ : (0 : ℝ) < (μ : ℝ) := μ.2
  have hmu1 : (0 : ℝ) < (((μ + 1 : PosReal) : ℝ)) := by
    simpa using add_pos μ.2 zero_lt_one
  field_simp [hμ.ne', hmu1.ne']
  simp
  ring

/-- Helper for Theorem 6.63: the cross term in the completed-square expansion vanishes because the
inner quadratic minimizer satisfies the first-order balance equation. -/
lemma cross_factor_for_moreau (r : ℝ) :
    (1 / (μ : ℝ)) * (((μ : ℝ) / (((μ + 1 : PosReal) : ℝ))) * r) -
      (1 / (((μ + 1 : PosReal) : ℝ))) * r = 0 := by
  -- The two coefficients cancel after clearing the positive denominator `μ`.
  have hμ : (0 : ℝ) < (μ : ℝ) := μ.2
  field_simp [hμ.ne']
  ring

/-- Helper for Theorem 6.63: the remaining quadratic term after completing the square has
coefficient `(μ + 1) / (2 μ)`. -/
lemma residual_factor_for_moreau (n : ℝ) :
    (1 / (2 * (μ : ℝ))) * n + (1 / 2 : ℝ) * n =
      ((((μ + 1 : PosReal) : ℝ) / (2 * (μ : ℝ))) : ℝ) * n := by
  -- This is the scalar coefficient identity for the residual square.
  have hμ : (0 : ℝ) < (μ : ℝ) := μ.2
  field_simp [hμ.ne']
  simp [add_comm]

/-- Helper for Theorem 6.63: the affine transport sends the textbook candidate
`lineMap x y (1 / (μ + 1))` back to `y`. -/
lemma transport_lineMap_eq_of_moreau (x y : E) :
    x + (((μ + 1 : PosReal) : ℝ)) •
        (lineMap x y (1 / (((μ + 1 : PosReal) : ℝ))) - x) = y := by
  -- Rewrite the transported displacement using the explicit `lineMap` difference formula.
  rw [lineMap_sub_left_for_moreau (μ := μ) x y]
  have hmu1_pos : 0 < (((μ + 1 : PosReal) : ℝ)) := by
    simpa using add_pos μ.2 zero_lt_one
  have hmu1_ne : ((((μ + 1 : PosReal) : ℝ)) ≠ 0) := hmu1_pos.ne'
  have hmu1 :
      (((μ + 1 : PosReal) : ℝ)) * (1 / (((μ + 1 : PosReal) : ℝ))) = 1 := by
    field_simp [hmu1_ne]
  rw [smul_smul, hmu1, one_smul]
  abel

/-- Helper for Theorem 6.63: the affine transport `T v = x + (μ + 1) • (v - x)` converts the
residual displacement from `lineMap x y (1 / (μ + 1))` into the direct displacement from `y`. -/
lemma transport_sub_eq_smul_of_moreau (x v y : E) :
    (x + (((μ + 1 : PosReal) : ℝ)) • (v - x)) - y =
      (((μ + 1 : PosReal) : ℝ)) •
        (v - lineMap x y (1 / (((μ + 1 : PosReal) : ℝ)))) := by
  -- Expand the affine interpolation point and pull out the common scale `(μ + 1)`.
  rw [AffineMap.lineMap_apply_module']
  have hmu1_pos : 0 < (((μ + 1 : PosReal) : ℝ)) := by
    simpa using add_pos μ.2 zero_lt_one
  have hscale :
      (((μ + 1 : PosReal) : ℝ)) * (1 / (((μ + 1 : PosReal) : ℝ))) = 1 := by
    field_simp [hmu1_pos.ne']
  calc
    (x + (((μ + 1 : PosReal) : ℝ)) • (v - x)) - y
        = (((μ + 1 : PosReal) : ℝ)) • (v - x) - (y - x) := by
            module
    _ = (((μ + 1 : PosReal) : ℝ)) • (v - x) -
          ((((μ + 1 : PosReal) : ℝ)) * (1 / (((μ + 1 : PosReal) : ℝ)))) • (y - x) := by
            rw [hscale, one_smul]
    _ = (((μ + 1 : PosReal) : ℝ)) •
          ((v - x) - (1 / (((μ + 1 : PosReal) : ℝ))) • (y - x)) := by
            module
    _ = (((μ + 1 : PosReal) : ℝ)) •
          (v - ((1 / (((μ + 1 : PosReal) : ℝ))) • (y - x) + x)) := by
            module
    _ = (((μ + 1 : PosReal) : ℝ)) •
          (v - lineMap x y (1 / (((μ + 1 : PosReal) : ℝ)))) := by
            rw [AffineMap.lineMap_apply_module']

/-- Helper for Theorem 6.63: after the affine transport `T`, the residual Moreau-envelope
coefficient is exactly the completed-square coefficient `(μ + 1) / (2 μ)`. -/
lemma transported_square_factor_for_moreau (n : ℝ) :
    (1 / (2 * ((μ : ℝ) * (((μ + 1 : PosReal) : ℝ))))) *
        ((((μ + 1 : PosReal) : ℝ) * n) ^ (2 : ℕ)) =
      ((((μ + 1 : PosReal) : ℝ) / (2 * (μ : ℝ))) : ℝ) * n ^ (2 : ℕ) := by
  -- This is the scalar coefficient identity after substituting `T v - y = (μ + 1) (v - z)`.
  have hμ : (0 : ℝ) < (μ : ℝ) := μ.2
  have hmu1 : (0 : ℝ) < (((μ + 1 : PosReal) : ℝ)) := by
    simpa using add_pos μ.2 zero_lt_one
  field_simp [hμ.ne', hmu1.ne']

/-- Helper for Theorem 6.63: the two-stage quadratic objective in the Moreau-envelope proof is a
completed square centered at `lineMap x y (1 / (μ + 1))`. -/
lemma moreau_two_stage_quadratic_eq_completed_square (x v y : E) :
    (1 / (2 * (μ : ℝ))) * ‖v - y‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ) =
      (1 / (2 * (((μ + 1 : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ) +
        ((((μ + 1 : PosReal) : ℝ) / (2 * (μ : ℝ))) *
          ‖v - lineMap x y (1 / (((μ + 1 : PosReal) : ℝ)))‖ ^ (2 : ℕ)) := by
  let z : E := lineMap x y (1 / (((μ + 1 : PosReal) : ℝ)))
  -- Expand both quadratic terms around the inner minimizer `z`.
  have hvy := quadratic_translate_identity y z v
  have hvx := quadratic_translate_identity x z v
  have hvy' :
      (1 / (2 * (μ : ℝ))) * ‖v - y‖ ^ (2 : ℕ) =
        (1 / (2 * (μ : ℝ))) * ‖z - y‖ ^ (2 : ℕ) +
          (1 / (μ : ℝ)) * inner ℝ (z - y) (v - z) +
          (1 / (2 * (μ : ℝ))) * ‖v - z‖ ^ (2 : ℕ) := by
    have hvy0 := congrArg (fun t : ℝ ↦ (1 / (μ : ℝ)) * t) hvy
    simpa [mul_add, mul_assoc, mul_left_comm, mul_comm] using hvy0
  have hzy : z - y = ((μ : ℝ) / (((μ + 1 : PosReal) : ℝ))) • (x - y) := by
    simpa [z] using lineMap_sub_right_for_moreau (μ := μ) x y
  have hzx : z - x = (1 / (((μ + 1 : PosReal) : ℝ))) • (y - x) := by
    simpa [z] using lineMap_sub_left_for_moreau (μ := μ) x y
  have hcross :
      (1 / (μ : ℝ)) * inner ℝ (z - y) (v - z) + inner ℝ (z - x) (v - z) = 0 := by
    -- The first-order condition for the inner variable cancels the mixed term.
    rw [hzy, hzx, inner_smul_left, inner_smul_left]
    have hyx : y - x = -(x - y) := by
      abel
    rw [hyx, inner_neg_left]
    simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
      cross_factor_for_moreau (μ := μ) (inner ℝ (x - y) (v - z))
  have hconst :
      (1 / (2 * (μ : ℝ))) * ‖z - y‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
        (1 / (2 * (((μ + 1 : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ) := by
    -- The endpoint terms collapse to the outer penalty on `y`.
    rw [hzy, hzx, norm_smul, norm_smul, norm_sub_rev]
    have hμ : (0 : ℝ) < (μ : ℝ) := μ.2
    have hmu1 : (0 : ℝ) < (((μ + 1 : PosReal) : ℝ)) := by
      simpa using add_pos μ.2 zero_lt_one
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (div_pos hμ hmu1),
      abs_of_pos (one_div_pos.mpr hmu1)]
    simpa [norm_sub_rev] using scaled_square_factor_for_moreau (μ := μ) ‖x - y‖
  have hcoeff_v :
      (1 / (2 * (μ : ℝ))) * ‖v - z‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖v - z‖ ^ (2 : ℕ) =
        ((((μ + 1 : PosReal) : ℝ) / (2 * (μ : ℝ))) : ℝ) * ‖v - z‖ ^ (2 : ℕ) := by
    -- The remaining square collects the residual coefficient.
    simpa using residual_factor_for_moreau (μ := μ) (‖v - z‖ ^ (2 : ℕ))
  linarith [hvy', hvx, hcross, hconst, hcoeff_v]

/-- Helper for Theorem 6.63: minimizing the scaled proximal objective is equivalent to minimizing
the outer penalty `y ↦ f y + ‖x - y‖² / (2 μ)`. -/
lemma mem_scaled_prox_iff_isMinOn_moreau_penalty {x u : E} :
    u ∈ prox[((μ : EReal) • f)] x ↔
      IsMinOn (fun v : E ↦ f v + ((((1 / (2 * μ) : ℝ) * ‖x - v‖ ^ (2 : ℕ)) : ℝ) : EReal))
        Set.univ u := by
  constructor
  · intro hu
    -- The forward direction is the owner-level bridge from Definition 6.7.
    exact isMinOn_moreau_penalty_of_mem_scaled_prox hu
  · intro hu
    -- The reverse direction rebuilds the scaled proximal inequality from the divided objective.
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    rw [isMinOn_univ_iff] at hu
    intro v
    have huv_div :
        proximal_objective (((μ : EReal) • f)) x u / ((μ : ℝ) : EReal) ≤
          proximal_objective (((μ : EReal) • f)) x v / ((μ : ℝ) : EReal) := by
      rw [scaled_proximal_objective_div_eq_moreau_penalty,
        scaled_proximal_objective_div_eq_moreau_penalty]
      exact hu v
    have hμ_nonneg : 0 ≤ ((μ : ℝ) : EReal) := by
      exact_mod_cast μ.2.le
    have hμ_top : ((μ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    have hμ_bot : ((μ : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
    have hμ_zero : ((μ : ℝ) : EReal) ≠ 0 := by
      exact_mod_cast μ.2.ne'
    have huv := mul_le_mul_of_nonneg_right huv_div hμ_nonneg
    rw [EReal.div_mul_cancel hμ_bot hμ_top hμ_zero,
      EReal.div_mul_cancel hμ_bot hμ_top hμ_zero] at huv
    exact huv

/-- Helper for Theorem 6.63: scaling the outer penalty by `μ + 1` turns it into the proximal
objective of the scaled function `((μ + 1) • f)` at `x`. -/
lemma scaled_outer_moreau_penalty_eq_scaled_proximal_objective (x y : E) :
    (((μ + 1 : PosReal) : EReal) • outer_moreau_penalty (f := f) (μ := μ) x) y =
      proximal_objective (((((μ + 1 : PosReal) : ℝ) : EReal) • f)) x y := by
  -- Expand both owners and isolate the quadratic coefficient under the positive scalar `μ + 1`.
  rw [Pi.smul_apply, outer_moreau_penalty_apply, proximal_objective_apply, smul_eq_mul]
  have hμ1_nonneg : (0 : EReal) ≤ (((μ + 1 : PosReal) : ℝ) : EReal) := by
    exact_mod_cast (show 0 ≤ ((μ + 1 : PosReal) : ℝ) by exact le_of_lt (μ + 1).2)
  have hμ1_ne_top : ((((μ + 1 : PosReal) : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top _
  rw [EReal.left_distrib_of_nonneg_of_ne_top hμ1_nonneg hμ1_ne_top]
  congr 1
  rw [norm_sub_rev]
  have hcoeff :
      (((μ + 1 : PosReal) : ℝ) *
          ((1 / (2 * (((μ + 1 : PosReal) : ℝ))) * ‖y - x‖ ^ (2 : ℕ)))) =
        ((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)) := by
    have hmu1_ne : (((μ + 1 : PosReal) : ℝ)) ≠ 0 := by
      have hmu1_pos : 0 < (((μ + 1 : PosReal) : ℝ)) := by
        simpa using add_pos μ.2 zero_lt_one
      exact ne_of_gt hmu1_pos
    field_simp [hmu1_ne]
  exact_mod_cast hcoeff

/-- Helper for Theorem 6.63: on the effective domain of `g`, the proximal objective has the
expected real-valued form `g.toReal + (1 / 2) ‖z - x‖²`. -/
lemma proximal_objective_toReal_eq_on_effective_domain
    (g : E → EReal) (x z : E) (hbot : g z ≠ ⊥) (hz : z ∈ effective_domain g) :
    (proximal_objective g x z).toReal = (g z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
  -- On the effective domain, both summands are finite, so `toReal` distributes over the sum.
  rw [proximal_objective_apply, EReal.toReal_add]
  · simpa using EReal.toReal_coe ((1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ))
  · exact (mem_effective_domain.mp hz).ne
  · exact hbot
  · exact EReal.coe_ne_top _
  · exact EReal.coe_ne_bot _

/-- Helper for Theorem 6.63: every translated quadratic penalty with a nonnegative coefficient is
convex as an extended-real-valued function. -/
lemma translated_quadratic_penalty_is_convex_function
    (x : E) (a : ℝ) (ha : 0 ≤ a) :
    is_convex_function (fun z : E ↦ (((a * ‖z - x‖ ^ (2 : ℕ) : ℝ) : EReal))) := by
  -- First package the centered quadratic `z ↦ a ‖z‖²`, then translate it by `x`.
  have hnorm_sq : ConvexOn ℝ Set.univ (fun z : E ↦ ‖z‖ ^ (2 : ℕ)) :=
    convexOn_univ_norm.pow (fun z _ ↦ norm_nonneg z) 2
  let q0 : E → EReal := fun z ↦ (((a * ‖z‖ ^ (2 : ℕ) : ℝ) : EReal))
  have hdom : effective_domain q0 = Set.univ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      change q0 z < ⊤
      exact EReal.coe_lt_top (a * ‖z‖ ^ (2 : ℕ))
  have hbase : is_convex_function q0 := by
    -- The centered quadratic is everywhere finite, so the Chapter 2 `toReal` bridge applies on
    -- the whole space.
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro z hz
      simpa [q0] using (EReal.coe_ne_bot (a * ‖z‖ ^ (2 : ℕ)))
    · rw [hdom]
      simpa [q0] using hnorm_sq.smul ha
  simpa [q0, sub_eq_add_neg] using
    is_convex_function_precompose_linearMap_add hbase (LinearMap.id : E →ₗ[ℝ] E) (-x)

/-- Helper for Theorem 6.63: adding the quadratic penalty keeps a proper closed convex function
proper, closed, and convex. -/
lemma proximal_objective_proper_closed_convex_of_proper_closed_convex
    (g : E → EReal) (x : E) (hg_proper : IsProperExtendedRealFunction g)
    (hg_closed : LowerSemicontinuous g) (hg_convex : is_convex_function g) :
    IsProperExtendedRealFunction (proximal_objective g x) ∧
      LowerSemicontinuous (proximal_objective g x) ∧
      is_convex_function (proximal_objective g x) := by
  -- Properness and lower semicontinuity are owner-level consequences of the same properties for
  -- `g`; convexity comes from adding the translated quadratic penalty to `g`.
  have hproper : IsProperExtendedRealFunction (proximal_objective g x) := by
    refine ⟨?_, ?_⟩
    · intro z
      rw [proximal_objective_apply, EReal.add_ne_bot_iff]
      exact ⟨hg_proper.ne_bot z, EReal.coe_ne_bot _⟩
    · rcases hg_proper.effective_domain_nonempty with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      rw [mem_effective_domain, proximal_objective_apply]
      exact EReal.add_lt_top (mem_effective_domain.mp hz).ne (EReal.coe_ne_top _)
  have hclosed : LowerSemicontinuous (proximal_objective g x) :=
    lowerSemicontinuous_proximal_objective hg_closed x
  have hquad :
      is_convex_function
        (fun z : E ↦ ((((1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) : ℝ) : EReal))) :=
    translated_quadratic_penalty_is_convex_function (x := x) (a := 1 / 2) (by norm_num)
  let F : Fin 2 → E → EReal := fun i ↦
    if i = 0 then g else fun z ↦ ((((1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) : ℝ) : EReal))
  have hF : ∀ i : Fin 2, is_convex_function (F i) := by
    intro i
    fin_cases i
    · dsimp [F]
      simpa using hg_convex
    · dsimp [F]
      simpa using hquad
  have hF_ne_bot : ∀ i ∈ Finset.univ, ∀ z, F i z ≠ ⊥ := by
    intro i _ z
    fin_cases i
    · simpa [F] using hg_proper.ne_bot z
    · dsimp [F]
      simpa only [← EReal.coe_pow, ← EReal.coe_mul] using
        EReal.coe_ne_bot ((1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ))
  have hconvex : is_convex_function (proximal_objective g x) := by
    -- The proximal objective is the sum of `g` and the canonical quadratic penalty.
    have hsum :=
      is_convex_function_finset_nonneg_weighted_sum (s := Finset.univ) (f := F)
        (fun i _ ↦ hF i) hF_ne_bot (fun _ ↦ (1 : NNReal))
    simpa [proximal_objective_apply, F, Fin.sum_univ_two] using hsum
  exact ⟨hproper, hclosed, hconvex⟩

/-- Helper for Theorem 6.63: for fixed `y`, the two-stage Moreau integrand equals the outer
penalty plus the transported residual kernel. -/
lemma two_stage_moreau_integrand_eq_outer_kernel (x v y : E) :
    f y + (((1 / (2 * μ) : ℝ) * ‖v - y‖ ^ (2 : ℕ) : ℝ) : EReal) +
        (((1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ) : ℝ) : EReal) =
      outer_moreau_penalty (f := f) (μ := μ) x y +
        (((1 / (2 * ((μ : ℝ) * (((μ + 1 : PosReal) : ℝ)))) : ℝ) *
            ‖(x + (((μ + 1 : PosReal) : ℝ)) • (v - x)) - y‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let z : E := lineMap x y (1 / (((μ + 1 : PosReal) : ℝ)))
  let a : ℝ := (1 / (2 * (μ : ℝ))) * ‖v - y‖ ^ (2 : ℕ)
  let b : ℝ := (1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ)
  let c : ℝ := (1 / (2 * (((μ + 1 : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ)
  let d : ℝ :=
    (1 / (2 * ((μ : ℝ) * (((μ + 1 : PosReal) : ℝ)))) : ℝ) *
      ‖(x + (((μ + 1 : PosReal) : ℝ)) • (v - x)) - y‖ ^ (2 : ℕ)
  have htransport :
      ((((μ + 1 : PosReal) : ℝ) / (2 * (μ : ℝ))) : ℝ) * ‖v - z‖ ^ (2 : ℕ) = d := by
    -- Rewrite the transported residual square using the affine transport identity.
    rw [show d =
        (1 / (2 * ((μ : ℝ) * (((μ + 1 : PosReal) : ℝ)))) : ℝ) *
          ‖(x + (((μ + 1 : PosReal) : ℝ)) • (v - x)) - y‖ ^ (2 : ℕ) by rfl]
    rw [transport_sub_eq_smul_of_moreau (μ := μ) x v y]
    rw [norm_smul]
    have hmu1_pos : 0 < (((μ + 1 : PosReal) : ℝ)) := by
      simpa using add_pos μ.2 zero_lt_one
    rw [Real.norm_eq_abs, abs_of_pos hmu1_pos]
    simpa [z] using (transported_square_factor_for_moreau (μ := μ) (‖v - z‖)).symm
  have hreal : a + b = c + d := by
    -- Complete the square in `v` and then rewrite the residual by affine transport.
    calc
      a + b
          = (1 / (2 * (((μ + 1 : PosReal) : ℝ)))) * ‖x - y‖ ^ (2 : ℕ) +
              ((((μ + 1 : PosReal) : ℝ) / (2 * (μ : ℝ))) : ℝ) *
                ‖v - z‖ ^ (2 : ℕ) := by
              simpa [a, b, c, z] using
                moreau_two_stage_quadratic_eq_completed_square (μ := μ) x v y
      _ = c + d := by
            simpa [c] using congrArg (fun t : ℝ ↦ c + t) htransport
  have hreal_ereal :
      (((a + b : ℝ)) : EReal) = (((c + d : ℝ)) : EReal) := by
    exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hreal
  -- Package the real completed-square identity back into the `EReal` integrand.
  calc
    (f y + ((a : ℝ) : EReal)) + ((b : ℝ) : EReal)
        = f y + (((a + b : ℝ)) : EReal) := by
            simp [add_assoc, EReal.coe_add]
    _ = f y + (((c + d : ℝ)) : EReal) := by
          rw [hreal_ereal]
    _ = (f y + ((c : ℝ) : EReal)) + ((d : ℝ) : EReal) := by
          simp [add_assoc, EReal.coe_add]
    _ = outer_moreau_penalty (f := f) (μ := μ) x y + ((d : ℝ) : EReal) := by
          rw [outer_moreau_penalty_apply]

/-- Helper for Theorem 6.63: the proximal objective of the Moreau envelope is the Moreau envelope
of the outer penalty after the affine transport `v ↦ x + (μ + 1) • (v - x)`. -/
lemma proximal_objective_moreau_envelope_eq_outer_moreau_envelope
    (x v : E) :
    let ν : PosReal :=
      ⟨(μ : ℝ) * (((μ + 1 : PosReal) : ℝ)),
        by
          have hμ : (0 : ℝ) < (μ : ℝ) := μ.2
          have hmu1 : (0 : ℝ) < (((μ + 1 : PosReal) : ℝ)) := by
            simpa using add_pos hμ zero_lt_one
          exact mul_pos hμ hmu1⟩
    let T : E → E := fun z ↦ x + (((μ + 1 : PosReal) : ℝ)) • (z - x)
    proximal_objective (M[μ, f]) x v = M[ν, outer_moreau_penalty (f := f) (μ := μ) x] (T v) := by
  -- Route correction: rewrite the transport pointwise under the infimum instead of searching for
  -- a coarser global Moreau-envelope identity.
  dsimp
  rw [moreau_envelope_apply, moreau_envelope_apply]
  let c : ℝ := (1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ)
  change
    (⨅ u : E, f u + ((((1 / (2 * μ) : ℝ) * ‖v - u‖ ^ (2 : ℕ) : ℝ) : EReal))) + (c : EReal) =
      ⨅ u : E,
        outer_moreau_penalty (f := f) (μ := μ) x u +
          (((1 / (2 * ((μ : ℝ) * (((μ + 1 : PosReal) : ℝ)))) : ℝ) *
              ‖(x + (((μ + 1 : PosReal) : ℝ)) • (v - x)) - u‖ ^ (2 : ℕ) : ℝ) : EReal)
  rw [iInf_add_real_eq]
  -- The completed-square identity now closes the pointwise integrand comparison.
  refine iInf_congr fun y ↦ ?_
  simpa [c] using two_stage_moreau_integrand_eq_outer_kernel (f := f) (μ := μ) x v y

/-- Helper for Theorem 6.63: the outer penalty is the positive inverse scaling of the proximal
objective of `((μ + 1) • f)` at `x`. -/
lemma outer_moreau_penalty_eq_inv_scaled_proximal_objective (x : E) :
    outer_moreau_penalty (f := f) (μ := μ) x =
      ((((μ + 1 : PosReal)⁻¹ : PosReal) : EReal) •
        (fun z : E ↦ proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z)) := by
  -- Rewrite the outer penalty as the inverse scaling of the already identified proximal
  -- objective for `((μ + 1) • f)`.
  ext z
  have hμ1_pos : (0 : ℝ) < ((μ + 1 : PosReal) : ℝ) := by
    simpa using add_pos μ.2 zero_lt_one
  let a : EReal := ((μ + 1 : PosReal) : EReal)
  have ha_bot : a ≠ ⊥ := by
    dsimp [a]
    exact EReal.coe_ne_bot _
  have ha_top : a ≠ ⊤ := by
    dsimp [a]
    exact EReal.coe_ne_top _
  have ha_zero : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast hμ1_pos.ne'
  rw [Pi.smul_apply]
  have hs := scaled_outer_moreau_penalty_eq_scaled_proximal_objective
    (f := f) (μ := μ) x z
  rw [Pi.smul_apply, smul_eq_mul] at hs
  rw [smul_eq_mul]
  rw [eq_comm]
  have hdiv :
      (((μ + 1 : PosReal) : EReal))⁻¹ *
          proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z =
        proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z / a := by
    simpa [a] using
      (EReal.div_eq_inv_mul
        (proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z) a).symm
  calc
    (((μ + 1 : PosReal) : EReal))⁻¹ *
        proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z
        = proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z / a := hdiv
    _ = outer_moreau_penalty (f := f) (μ := μ) x z := by
          exact (EReal.div_eq_iff ha_bot ha_top ha_zero).2 (by simpa [a, mul_comm] using hs.symm)

/-- Helper for Theorem 6.63: the outer penalty remains proper, closed, and convex under the same
owner hypotheses as `f`. -/
lemma outer_moreau_penalty_proper_closed_convex {x : E}
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f) :
    IsProperExtendedRealFunction (outer_moreau_penalty (f := f) (μ := μ) x) ∧
      LowerSemicontinuous (outer_moreau_penalty (f := f) (μ := μ) x) ∧
      is_convex_function (outer_moreau_penalty (f := f) (μ := μ) x) := by
  -- Package the scaled source function first, then package its proximal objective, and finally
  -- scale back by the positive inverse factor from the preceding identity.
  rcases
      scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex (μ + 1) with
    ⟨hscaled_proper, hscaled_closed, hscaled_convex⟩
  rcases
      proximal_objective_proper_closed_convex_of_proper_closed_convex
        ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x
        hscaled_proper hscaled_closed hscaled_convex with
    ⟨hprox_proper, hprox_closed, hprox_convex⟩
  simpa [outer_moreau_penalty_eq_inv_scaled_proximal_objective (f := f) (μ := μ) (x := x)] using
    (scaled_function_proper_closed_convex_of_pos
      (fun z : E ↦ proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z)
      hprox_proper hprox_closed hprox_convex ((μ + 1 : PosReal)⁻¹))

/-- Helper for Theorem 6.63: a minimizer of the outer penalty remains a minimizer after Moreau
smoothing, because the smoothing infimum is attained at the same point. -/
lemma moreau_envelope_isMinOn_of_isMinOn {G : E → EReal} {ν : PosReal} {u : E}
    (hu : IsMinOn G Set.univ u) :
    IsMinOn (M[ν, G]) Set.univ u := by
  -- Compare the smoothed value at `u` with the outer minimum value `G u`.
  rw [isMinOn_univ_iff] at hu ⊢
  intro y
  have hu_upper : M[ν, G] u ≤ G u := by
    -- Evaluating the infimum at `z = u` gives the upper bound.
    rw [moreau_envelope_apply]
    have hi :
        (⨅ z : E, G z + ((((1 / (2 * ν) : ℝ) * ‖u - z‖ ^ (2 : ℕ)) : ℝ) : EReal)) ≤
          G u + ((((1 / (2 * ν) : ℝ) * ‖u - u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
      exact iInf_le (fun z : E ↦
        G z + ((((1 / (2 * ν) : ℝ) * ‖u - z‖ ^ (2 : ℕ)) : ℝ) : EReal)) u
    exact le_trans hi (by simp)
  have hu_lower : G u ≤ M[ν, G] y := by
    -- Every integrand is bounded below by the minimal outer value `G u`.
    rw [moreau_envelope_apply]
    refine le_iInf ?_
    intro z
    calc
      G u ≤ G z := hu z
      _ ≤ G z + ((((1 / (2 * ν) : ℝ) * ‖y - z‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
          have hnonneg_real :
              0 ≤ (1 / (2 * (ν : ℝ)) : ℝ) * ‖y - z‖ ^ (2 : ℕ) := by
            have hν : 0 < (ν : ℝ) := ν.2
            positivity
          have hnonneg :
              (0 : EReal) ≤ ((((1 / (2 * ν) : ℝ) * ‖y - z‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
            exact_mod_cast hnonneg_real
          simpa using le_add_of_nonneg_right hnonneg
  exact le_trans hu_upper hu_lower

/-- Helper for Theorem 6.63: if a Moreau-envelope minimizer already attains the unique minimum
value of the outer function, then the envelope minimizer is the unique outer minimizer. -/
lemma moreau_minimizer_eq_unique_outer_minimizer_of_value_match
    {G : E → EReal} (hG_proper : IsProperExtendedRealFunction G)
    (hG_closed : LowerSemicontinuous G) (hG_convex : is_convex_function G)
    {ν : PosReal} {u y : E} (hu : IsMinOn G Set.univ u)
    (huniq : ∀ z, IsMinOn G Set.univ z → z = u)
    (hy : IsMinOn (M[ν, G]) Set.univ y) (hvalue : M[ν, G] y = G u) :
    y = u := by
  rcases scaled_function_proper_closed_convex_of_pos G hG_proper hG_closed hG_convex ν with
    ⟨hscaled_proper, hscaled_closed, hscaled_convex⟩
  rcases prox_eq_singleton_of_proper_closed_convex (((ν : ℝ) : EReal) • G)
      hscaled_proper hscaled_closed hscaled_convex y with ⟨w, hwprox⟩
  have hu_univ : ∀ z, G u ≤ G z := by
    simpa [isMinOn_univ_iff] using hu
  let r : ℝ := (1 / (2 * ν) : ℝ) * ‖y - w‖ ^ (2 : ℕ)
  have hmoreau :
      M[ν, G] y = G w + ((r : ℝ) : EReal) := by
    simpa [r] using
      moreau_envelope_eq_of_scaled_prox_eq_singleton (f := G) (μ := ν) (x := y) (u := w) hwprox
  have hr_nonneg_real : 0 ≤ r := by
    have hν : 0 < (ν : ℝ) := ν.2
    positivity
  have hr_nonneg : (0 : EReal) ≤ ((r : ℝ) : EReal) := by
    exact_mod_cast hr_nonneg_real
  have hGw_le_Gu : G w ≤ G u := by
    calc
      G w ≤ G w + ((r : ℝ) : EReal) := by
        simpa using le_add_of_nonneg_right hr_nonneg
      _ = M[ν, G] y := by simpa [r] using hmoreau.symm
      _ = G u := hvalue
  have hGu_le_Gw : G u ≤ G w := hu_univ w
  have hGw_eq_Gu : G w = G u := le_antisymm hGw_le_Gu hGu_le_Gw
  have hw_min : IsMinOn G Set.univ w := by
    rw [isMinOn_univ_iff]
    intro z
    calc
      G w = G u := hGw_eq_Gu
      _ ≤ G z := hu_univ z
  have hw_eq_u : w = u := huniq w hw_min
  have hGu_ne_bot : G u ≠ ⊥ := hG_proper.ne_bot u
  have hGu_ne_top : G u ≠ ⊤ := by
    rcases hG_proper.effective_domain_nonempty with ⟨z, hz⟩
    exact ne_of_lt (lt_of_le_of_lt (hu_univ z) (mem_effective_domain.mp hz))
  have hadd : G u + ((r : ℝ) : EReal) = G u := by
    calc
      G u + ((r : ℝ) : EReal) = G w + ((r : ℝ) : EReal) := by rw [hGw_eq_Gu]
      _ = M[ν, G] y := by simpa [r] using hmoreau.symm
      _ = G u := hvalue
  have htoReal := congrArg EReal.toReal hadd
  rw [EReal.toReal_add hGu_ne_top hGu_ne_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
    EReal.toReal_coe] at htoReal
  have hr_eq_zero : r = 0 := by
    linarith
  have hnorm_sq_eq : ‖y - w‖ ^ (2 : ℕ) = 0 := by
    have hν : 0 < (ν : ℝ) := ν.2
    have hcoeff_pos : 0 < (1 / (2 * (ν : ℝ)) : ℝ) := by
      positivity
    have hmul_zero :
        (1 / (2 * (ν : ℝ)) : ℝ) * ‖y - w‖ ^ (2 : ℕ) = 0 := by
      simpa [r] using hr_eq_zero
    exact (mul_eq_zero.mp hmul_zero).resolve_left hcoeff_pos.ne'
  have hy_eq_w : y = w := by
    have hnorm_eq_zero : ‖y - w‖ = 0 := eq_zero_of_pow_eq_zero hnorm_sq_eq
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_eq_zero)
  exact hy_eq_w.trans hw_eq_u

/-- Helper for Theorem 6.63: if the outer penalty has the unique minimizer `u`, then every
minimizer of its Moreau envelope is also `u`. -/
lemma eq_of_isMinOn_moreau_envelope_of_unique_outer_penalty_minimizer
    {x : E} (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f) {ν : PosReal} {u y : E}
    (hu :
      IsMinOn (outer_moreau_penalty (f := f) (μ := μ) x) Set.univ u)
    (huniq :
      ∀ z,
        IsMinOn (outer_moreau_penalty (f := f) (μ := μ) x) Set.univ z → z = u)
    (hy :
      IsMinOn (M[ν, outer_moreau_penalty (f := f) (μ := μ) x]) Set.univ y) :
    y = u := by
  let G : E → EReal := outer_moreau_penalty (f := f) (μ := μ) x
  rcases outer_moreau_penalty_proper_closed_convex (f := f) (μ := μ)
      (x := x) hf_proper hf_closed hf_convex with
    ⟨hG_proper, hG_closed, hG_convex⟩
  have huG : IsMinOn G Set.univ u := by
    simpa [G] using hu
  have huniqG : ∀ z, IsMinOn G Set.univ z → z = u := by
    intro z hz
    exact huniq z (by simpa [G] using hz)
  have hyG : IsMinOn (M[ν, G]) Set.univ y := by
    simpa [G] using hy
  have huG_univ : ∀ z, G u ≤ G z := by
    simpa [isMinOn_univ_iff] using huG
  have hu_moreau : IsMinOn (M[ν, G]) Set.univ u :=
    moreau_envelope_isMinOn_of_isMinOn (ν := ν) huG
  have hu_moreau_univ : ∀ z, M[ν, G] u ≤ M[ν, G] z := by
    simpa [isMinOn_univ_iff] using hu_moreau
  have hy_moreau_univ : ∀ z, M[ν, G] y ≤ M[ν, G] z := by
    simpa [isMinOn_univ_iff] using hyG
  have hu_value : M[ν, G] u = G u := by
    apply le_antisymm
    · -- Evaluating the Moreau infimum at the minimizer itself gives the upper bound.
      rw [moreau_envelope_apply]
      exact le_trans (iInf_le _ u) (by simp)
    · -- Every Moreau integrand is bounded below by the minimum value `G u`.
      rw [moreau_envelope_apply]
      refine le_iInf ?_
      intro z
      calc
        G u ≤ G z := huG_univ z
        _ ≤ G z + ((((1 / (2 * ν) : ℝ) * ‖u - z‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
            have hnonneg_real :
                0 ≤ (1 / (2 * (ν : ℝ)) : ℝ) * ‖u - z‖ ^ (2 : ℕ) := by
              have hν : 0 < (ν : ℝ) := ν.2
              positivity
            have hnonneg :
                (0 : EReal) ≤ ((((1 / (2 * ν) : ℝ) * ‖u - z‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
              exact_mod_cast hnonneg_real
            simpa using le_add_of_nonneg_right hnonneg
  have hvalue : M[ν, G] y = G u := by
    calc
      M[ν, G] y = M[ν, G] u := le_antisymm (hy_moreau_univ u) (hu_moreau_univ y)
      _ = G u := hu_value
  -- The value match forces the Moreau minimizer to collapse to the unique outer minimizer.
  exact
    moreau_minimizer_eq_unique_outer_minimizer_of_value_match
      (G := G) hG_proper hG_closed hG_convex huG huniqG hyG hvalue

/-- Helper for Theorem 6.63: applying `lineMap` to the transported point
`x + (μ + 1) • (v - x)` recovers `v`. -/
lemma lineMap_transport_self (x v : E) :
    lineMap x (x + (((μ + 1 : PosReal) : ℝ)) • (v - x))
      (1 / (((μ + 1 : PosReal) : ℝ))) = v := by
  rw [AffineMap.lineMap_apply_module']
  have hmu1_pos : 0 < (((μ + 1 : PosReal) : ℝ)) := by
    simpa using add_pos μ.2 zero_lt_one
  have hmu1 :
      (1 / (((μ + 1 : PosReal) : ℝ))) * (((μ + 1 : PosReal) : ℝ)) = 1 := by
    field_simp [hmu1_pos.ne']
  -- Expanding `lineMap` turns the claim into a scalar cancellation.
  calc
    (1 / (((μ + 1 : PosReal) : ℝ))) • ((x + (((μ + 1 : PosReal) : ℝ)) • (v - x)) - x) + x
        = (1 / (((μ + 1 : PosReal) : ℝ))) • ((((μ + 1 : PosReal) : ℝ)) • (v - x)) + x := by
            module
    _ = (((1 / (((μ + 1 : PosReal) : ℝ))) * (((μ + 1 : PosReal) : ℝ))) • (v - x)) + x := by
          rw [smul_smul]
    _ = v := by
          rw [hmu1, one_smul]
          module

/-- Helper for Theorem 6.63: once the scaled proximal point of `f` at `x` is the singleton `{u}`,
the proximal set of the Moreau envelope is the singleton at the transported point
`lineMap x u (1 / (μ + 1))`. -/
theorem prox_moreau_envelope_eq_singleton_of_scaled_prox_eq_singleton_strong
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f) {x u : E}
    (hprox : prox[((μ + 1 : ℝ) : EReal) • f] x = {u}) :
    prox[M[μ, f]] x = {lineMap x u (1 / (μ + 1) : ℝ)} := by
  let ν : PosReal :=
    ⟨(μ : ℝ) * (((μ + 1 : PosReal) : ℝ)),
      by
        have hμ : (0 : ℝ) < (μ : ℝ) := μ.2
        have hmu1 : (0 : ℝ) < (((μ + 1 : PosReal) : ℝ)) := by
          simpa using add_pos hμ zero_lt_one
        exact mul_pos hμ hmu1⟩
  let T : E → E := fun z ↦ x + (((μ + 1 : PosReal) : ℝ)) • (z - x)
  let G : E → EReal := outer_moreau_penalty (f := f) (μ := μ) x
  let a : EReal := (((μ + 1 : PosReal) : ℝ) : EReal)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact_mod_cast (show 0 ≤ ((μ + 1 : PosReal) : ℝ) by exact le_of_lt (μ + 1).2)
  have ha_bot : a ≠ ⊥ := by
    dsimp [a]
    exact EReal.coe_ne_bot _
  have ha_top : a ≠ ⊤ := by
    dsimp [a]
    exact EReal.coe_ne_top _
  have ha_zero : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (show (((μ + 1 : PosReal) : ℝ)) ≠ 0 by exact (show 0 < (((μ + 1 : PosReal) : ℝ)) by simpa using add_pos μ.2 zero_lt_one).ne')
  have hu_mem : u ∈ prox[((μ + 1 : ℝ) : EReal) • f] x := by
    rw [hprox]
    simp
  have hu_scaled_univ :
      ∀ z,
        proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x u ≤
          proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu_mem
    exact hu_mem
  have hu : IsMinOn G Set.univ u := by
    -- The scaled proximal singleton is exactly the unique minimizer of the outer penalty.
    rw [isMinOn_univ_iff]
    intro z
    have hscaled :
        a * G u ≤ a * G z := by
      calc
        a * G u = proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x u := by
          simpa [a, G, Pi.smul_apply, smul_eq_mul] using
            scaled_outer_moreau_penalty_eq_scaled_proximal_objective (f := f) (μ := μ) x u
        _ ≤ proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z := hu_scaled_univ z
        _ = a * G z := by
          simpa [a, G, Pi.smul_apply, smul_eq_mul] using
            (scaled_outer_moreau_penalty_eq_scaled_proximal_objective (f := f) (μ := μ) x z).symm
    have hdiv := EReal.monotone_div_right_of_nonneg ha_nonneg hscaled
    have hleft : (a * G u) / a = G u := by
      calc
        (a * G u) / a = G u * a / (1 * a) := by rw [mul_comm, one_mul]
        _ = G u / 1 := by rw [EReal.mul_div_mul_cancel ha_bot ha_top ha_zero]
        _ = G u := by simp
    have hright : (a * G z) / a = G z := by
      calc
        (a * G z) / a = G z * a / (1 * a) := by rw [mul_comm, one_mul]
        _ = G z / 1 := by rw [EReal.mul_div_mul_cancel ha_bot ha_top ha_zero]
        _ = G z := by simp
    calc
      G u = (a * G u) / a := hleft.symm
      _ ≤ (a * G z) / a := hdiv
      _ = G z := hright
  have huniq : ∀ z, IsMinOn G Set.univ z → z = u := by
    intro z hz
    have hz_mem : z ∈ prox[((μ + 1 : ℝ) : EReal) • f] x := by
      rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
      intro y
      have hz_univ : ∀ y, G z ≤ G y := by
        simpa [isMinOn_univ_iff] using hz
      calc
        proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x z = a * G z := by
          simpa [a, G, Pi.smul_apply, smul_eq_mul] using
            (scaled_outer_moreau_penalty_eq_scaled_proximal_objective (f := f) (μ := μ) x z).symm
        _ ≤ a * G y := by
          exact mul_le_mul_of_nonneg_left (hz_univ y) ha_nonneg
        _ = proximal_objective ((((μ + 1 : PosReal) : ℝ) : EReal) • f) x y := by
          simpa [a, G, Pi.smul_apply, smul_eq_mul] using
            scaled_outer_moreau_penalty_eq_scaled_proximal_objective (f := f) (μ := μ) x y
    have hz_singleton : z ∈ ({u} : Set E) := by
      rw [hprox] at hz_mem
      simpa using hz_mem
    simpa using hz_singleton
  ext v
  constructor
  · intro hv
    have hv_min : IsMinOn (proximal_objective (M[μ, f]) x) Set.univ v := by
      simpa [mem_proximal_mapping_iff] using hv
    have hv_min_univ : ∀ z, proximal_objective (M[μ, f]) x v ≤ proximal_objective (M[μ, f]) x z := by
      simpa [isMinOn_univ_iff] using hv_min
    have hTv : IsMinOn (M[ν, G]) Set.univ (T v) := by
      rw [isMinOn_univ_iff]
      intro y
      let z : E := lineMap x y (1 / (((μ + 1 : PosReal) : ℝ)))
      -- Route correction: test the proximal objective against the affine inverse image of `y`.
      calc
        M[ν, G] (T v) = proximal_objective (M[μ, f]) x v := by
          symm
          simpa [ν, T, G] using
            proximal_objective_moreau_envelope_eq_outer_moreau_envelope
              (f := f) (μ := μ) x v
        _ ≤ proximal_objective (M[μ, f]) x z := hv_min_univ z
        _ = M[ν, G] (T z) := by
              simpa [ν, T, G] using
                proximal_objective_moreau_envelope_eq_outer_moreau_envelope
                  (f := f) (μ := μ) x z
        _ = M[ν, G] y := by
              rw [moreau_envelope_apply, moreau_envelope_apply]
              have hTz : T z = y := by
                simpa [T, z] using transport_lineMap_eq_of_moreau (μ := μ) x y
              refine iInf_congr fun w ↦ ?_
              rw [hTz]
    have hTv_outer : IsMinOn (M[ν, outer_moreau_penalty (f := f) (μ := μ) x]) Set.univ (T v) := by
      simpa [G] using hTv
    have hTv_eq_u : T v = u := by
      exact
        eq_of_isMinOn_moreau_envelope_of_unique_outer_penalty_minimizer
          (f := f) (μ := μ) hf_proper hf_closed hf_convex
          (by simpa [G] using hu)
          (by
            intro z hz
            exact huniq z (by simpa [G] using hz))
          hTv_outer
    have hv_eq : v = lineMap x u (1 / (((μ + 1 : PosReal) : ℝ))) := by
      have hline :=
        congrArg (fun w : E ↦ lineMap x w (1 / (((μ + 1 : PosReal) : ℝ)))) hTv_eq_u
      calc
        v = lineMap x (T v) (1 / (((μ + 1 : PosReal) : ℝ))) := by
          simpa [T] using (lineMap_transport_self (μ := μ) x v).symm
        _ = lineMap x u (1 / (((μ + 1 : PosReal) : ℝ))) := hline
    simpa [Set.mem_singleton_iff] using hv_eq
  · intro hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    have hu_moreau : IsMinOn (M[ν, G]) Set.univ u :=
      moreau_envelope_isMinOn_of_isMinOn (ν := ν) hu
    have hu_moreau_univ : ∀ y, M[ν, G] u ≤ M[ν, G] y := by
      simpa [isMinOn_univ_iff] using hu_moreau
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro z
    calc
      proximal_objective (M[μ, f]) x (lineMap x u (1 / (((μ + 1 : PosReal) : ℝ))))
          = M[ν, G] (T (lineMap x u (1 / (((μ + 1 : PosReal) : ℝ))))) := by
              simpa [ν, T, G] using
                proximal_objective_moreau_envelope_eq_outer_moreau_envelope
                  (f := f) (μ := μ) x (lineMap x u (1 / (((μ + 1 : PosReal) : ℝ))))
      _ = M[ν, G] u := by
            rw [moreau_envelope_apply, moreau_envelope_apply]
            have hTu :
                T (lineMap x u (1 / (((μ + 1 : PosReal) : ℝ)))) = u := by
              simpa [T] using transport_lineMap_eq_of_moreau (μ := μ) x u
            refine iInf_congr fun w ↦ ?_
            rw [hTu]
      _ ≤ M[ν, G] (T z) := hu_moreau_univ (T z)
      _ = proximal_objective (M[μ, f]) x z := by
            symm
            simpa [ν, T, G] using
              proximal_objective_moreau_envelope_eq_outer_moreau_envelope
                (f := f) (μ := μ) x z

-- Proof sketch: apply Theorem 6.3 to the scaled function `((μ + 1 : ℝ) : EReal) • f` to obtain
-- the unique proximal point `u` at `x`; positive scaling preserves properness, closedness, and
-- convexity, and properness excludes `⊥`. Then apply the singleton bridge theorem below to
-- convert that scaled proximal singleton into the singleton formula for `prox[M[μ, f]] x`.
/-- Theorem 6.63: if `f` is a proper closed convex extended-real-valued function, then at every
point `x` there is a unique proximal point `u` of the scaled function `(μ + 1) f`, and the
proximal set of the Moreau envelope `M[μ, f]` at `x` is the singleton containing
`lineMap x u (1 / (μ + 1))`. This is the chapter's set-valued rendering of the textbook formula
`prox_{M_f^μ}(x) = x + (1 / (μ + 1)) (prox_{(μ + 1) f}(x) - x)`, stated without promoting a
chosen proximal point to primitive data. -/
theorem prox_moreau_envelope_eq_singleton_of_proper_closed_convex
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f) (x : E) :
    ∃ u : E,
      prox[((μ + 1 : ℝ) : EReal) • f] x = {u} ∧
      prox[M[μ, f]] x = {lineMap x u (1 / (μ + 1) : ℝ)} := by
  -- First extract the unique scaled proximal point promised by Theorem 6.3.
  rcases
      scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex (μ + 1) with
    ⟨hscaled_proper, hscaled_closed, hscaled_convex⟩
  rcases
      prox_eq_singleton_of_proper_closed_convex (((μ + 1 : ℝ) : EReal) • f)
        hscaled_proper hscaled_closed hscaled_convex x with
    ⟨u, hprox⟩
  refine ⟨u, hprox, ?_⟩
  -- The repaired bridge theorem transports the singleton scaled proximal set to the prox of the
  -- Moreau envelope by the two-stage minimization identity.
  exact
    prox_moreau_envelope_eq_singleton_of_scaled_prox_eq_singleton_strong
      (f := f) (μ := μ) hf_proper hf_closed hf_convex hprox

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable (f : E → EReal) (μ : PosReal)

-- Proof sketch: expand the proximal objective of `M[μ, f]` at `x` as
-- `v ↦ M[μ, f] v + (1 / 2) ‖v - x‖²`, unfold `M[μ, f]` as an infimum over `y`, and complete the
-- square in `v`. The minimizing `v` for fixed `y` is `lineMap x y (1 / (μ + 1))`, while the
-- remaining outer minimization over `y` is exactly the scaled proximal problem. The hypothesis
-- `hf_ne_bot` excludes the `⊥` pathology, and `hprox` supplies the needed attainment.
/-- If the proximal set of the scaled function `(μ + 1) f` at `x` is the singleton `{u}`, then
the proximal set of the Moreau envelope at `x` is the singleton containing
`lineMap x u (1 / (μ + 1))`, equivalently the weighted average
`x + (1 / (μ + 1)) • (u - x)`. Under the same non-`⊥` hypothesis and `μ > 0`, this is the
chapter's singleton-valued rendering of the textbook identity
`prox_{M_f^μ}(x) = (μ x + u) / (μ + 1)`. -/
theorem prox_moreau_envelope_eq_singleton_of_scaled_prox_eq_singleton
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f) {x u : E}
    (hprox : prox[((μ + 1 : ℝ) : EReal) • f] x = {u}) :
    prox[M[μ, f]] x = {lineMap x u (1 / (μ + 1) : ℝ)} := by
  -- Reuse the stronger repaired bridge theorem from the proper/closed/convex section above.
  exact
    prox_moreau_envelope_eq_singleton_of_scaled_prox_eq_singleton_strong
      (f := f) (μ := μ) hf_proper hf_closed hf_convex hprox

end

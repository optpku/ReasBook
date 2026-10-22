/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Text_13_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g : E → EReal}

open scoped Gradient

local notation "f₀" => fun y ↦ EReal.toReal (f y)
local notation "F" => composite_model_objective f g
local notation "F_opt" => generalized_conditional_gradient_optimal_value f g

/- Domain sampling for this item uses the Chapter 13 owners already present in the project.
This lemma is `source-facing`, but its owner layer is already canonical in the chapter:

- `generalized_conditional_gradient_norm` from Text 13.2, written `S[f, g](x)`, is the chapter's
  canonical gap owner as the supremum of generalized gap values;
- `generalized_conditional_gradient_optimal_value` from Assumption 13.1 is the canonical optimal
  value owner, defined as `sInf (Set.range (composite_model_objective f g))`;
- `composite_model_objective` is the chapter owner for the source objective `F`;
- `convexOn_toReal_of_is_convex_function` is the Chapter 2 bridge from convex extended-real data
  to the real-valued restriction used by the gradient term.

The optimizer set is derived existence data, not primitive input for this bound: once the
right-hand side is phrased with the canonical infimum owner
`generalized_conditional_gradient_optimal_value f g`, optimizer attainment is mathematically
redundant in the public API. The proof only needs base-point finiteness and differentiability
data at `x`, not a global inclusion `effective_domain g ⊆ effective_domain f`, so the public
statement records `x ∈ effective_domain f` directly. By contrast, the Chapter 2 bridge from
`is_convex_function f` to convexity of `fun y ↦ (f y).toReal` genuinely uses the honest
global no-`⊥` hypothesis on `f`, so the theorem states that assumption directly rather than
disguising it as a domain-restricted variant. -/

-- Proof sketch: since `S[f₀, g](x)` is the supremum of all generalized gap
-- values at `x`, it dominates the gap value obtained at any comparison point `y`. Expand that
-- value with `generalized_conditional_gradient_gap_objective_apply`, use convexity of the
-- finite-valued restriction `f₀` on `effective_domain f` together with the explicit base-point
-- finiteness hypothesis `hx_f` to bound the inner-product term from below by
-- `F x - F y`, and conclude by comparing `F_opt = sInf (Set.range F)` with `F y`.
/-- Helper for Lemma 13.12: convexity of the finite-valued restriction `f₀` gives the supporting
hyperplane inequality at the base point `x`. -/
lemma convex_support_toReal_at_basepoint
    {x y : E}
    (hf_ne_bot : ∀ z, f z ≠ ⊥)
    (hf_convex : is_convex_function f)
    (hx_f : x ∈ effective_domain f)
    (hx_diff : DifferentiableAt ℝ f₀ x)
    (hy_f : y ∈ effective_domain f) :
    (f y).toReal ≥ (f x).toReal + inner ℝ (∇ f₀ x) (y - x) := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let φ : ℝ → ℝ := fun t ↦ f₀ (line t)
  have hconv : ConvexOn ℝ (effective_domain f) f₀ :=
    convexOn_toReal_of_is_convex_function hf_convex (fun z _ ↦ hf_ne_bot z)
  have hφ_convex :
      ConvexOn ℝ (line ⁻¹' effective_domain f) φ := by
    -- Restrict the convex real-valued model to the line segment from `x` to `y`.
    simpa [φ, line] using hconv.comp_affineMap line
  have hφ_zero :
      (0 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hx_f
  have hφ_one :
      (1 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hy_f
  have hφ_deriv :
      HasDerivAt φ (inner ℝ (∇ f₀ x) (y - x)) 0 := by
    -- Differentiate the segment restriction by the chain rule and identify the derivative with the
    -- ambient gradient paired against the segment direction.
    have hcomp :
        HasDerivAt φ (fderiv ℝ f₀ x (y - x)) 0 := by
      have hbase :
          HasFDerivAt f₀ (fderiv ℝ f₀ x) (line 0) := by
        simpa [line] using hx_diff.hasFDerivAt
      have hline : HasDerivAt line (y - x) 0 := by
        simpa [line] using
          (show HasDerivAt (AffineMap.lineMap x y) (y - x) (0 : ℝ) from
            AffineMap.hasDerivAt_lineMap)
      simpa [φ, line] using
        HasFDerivAt.comp_hasDerivAt 0 hbase hline
    have hgrad :
        fderiv ℝ f₀ x (y - x) = inner ℝ (∇ f₀ x) (y - x) := by
      simpa using
        (show
            fderiv ℝ f₀ x (y - x) = inner ℝ (∇ f₀ x) (y - x) from
          HasGradientAt.fderiv_apply hx_diff.hasGradientAt)
    simpa [hgrad] using hcomp
  have hsecant :
      inner ℝ (∇ f₀ x) (y - x) ≤ slope φ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hφ_convex.le_slope_of_hasDerivAt hφ_zero hφ_one zero_lt_one hφ_deriv
  have hsecant' :
      inner ℝ (∇ f₀ x) (y - x) ≤ (f y).toReal - (f x).toReal := by
    simpa [φ, line, slope] using hsecant
  linarith

/-- Helper for Lemma 13.12: every comparison point `y` bounds the objective value
`F x - generalized_conditional_gradient_gap_objective f₀ g x y` from above. -/
lemma objective_minus_gap_le_objective_value
    {x : E}
    (hf_ne_bot : ∀ z, f z ≠ ⊥)
    (hf_convex : is_convex_function f)
    (hx_f : x ∈ effective_domain f)
    (hx_diff : DifferentiableAt ℝ f₀ x)
    (hx : x ∈ effective_domain g)
    (y : E) :
    F x - generalized_conditional_gradient_gap_objective f₀ g x y ≤ F y := by
  by_cases hgx_bot : g x = ⊥
  · -- If the base regularizer value is `⊥`, then the whole left-hand side collapses to `⊥`.
    simp [generalized_conditional_gradient_gap_objective_apply, hgx_bot]
  by_cases hgy_bot : g y = ⊥
  · -- If the comparison regularizer value is `⊥`, then the gap value is `⊤`, so subtracting it
    -- from `F x` yields `⊥`.
    have hgap_top :
        generalized_conditional_gradient_gap_objective f₀ g x y = ⊤ := by
      have hsum_ne_bot :
          (((inner ℝ (∇ f₀ x) (x - y) : ℝ) : EReal) + g x) ≠ ⊥ := by
        exact (EReal.add_ne_bot_iff).2 ⟨EReal.coe_ne_bot _, hgx_bot⟩
      rw [generalized_conditional_gradient_gap_objective_apply, hgy_bot, EReal.sub_bot hsum_ne_bot]
    rw [hgap_top]
    simp [hgy_bot]
  by_cases hy_f : y ∈ effective_domain f
  · by_cases hy_g : y ∈ effective_domain g
    · -- In the finite branch, cancel the regularizer terms and compare the smooth terms using the
      -- convex support inequality at `x`.
      have hfx_top : f x ≠ ⊤ := (mem_effective_domain.mp hx_f).ne
      have hfy_top : f y ≠ ⊤ := (mem_effective_domain.mp hy_f).ne
      have hgx_top : g x ≠ ⊤ := (mem_effective_domain.mp hx).ne
      have hgy_top : g y ≠ ⊤ := (mem_effective_domain.mp hy_g).ne
      have hfx_val : f x = (((f x).toReal : ℝ) : EReal) := by
        exact (EReal.coe_toReal hfx_top (hf_ne_bot x)).symm
      have hfy_val : f y = (((f y).toReal : ℝ) : EReal) := by
        exact (EReal.coe_toReal hfy_top (hf_ne_bot y)).symm
      have hgx_val : g x = (((g x).toReal : ℝ) : EReal) := by
        exact (EReal.coe_toReal hgx_top hgx_bot).symm
      have hgy_val : g y = (((g y).toReal : ℝ) : EReal) := by
        exact (EReal.coe_toReal hgy_top hgy_bot).symm
      have hFy_ne_top : F y ≠ ⊤ := by
        rw [composite_model_objective_apply, hfy_val, hgy_val]
        exact (EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)).ne
      have hFy_ne_bot : F y ≠ ⊥ := by
        rw [composite_model_objective_apply, hfy_val, hgy_val]
        exact (EReal.add_ne_bot_iff).2 ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩
      have hinner_rev :
          inner ℝ (∇ f₀ x) (y - x) = -inner ℝ (∇ f₀ x) (x - y) := by
        have hsub : y - x = -(x - y) := by
          abel
        rw [hsub, inner_neg_right]
      have hsupport :
          (f x).toReal ≤ (f y).toReal + inner ℝ (∇ f₀ x) (x - y) := by
        -- Rewrite the first-order convexity bound into the source proof's `x - y` form.
        have hbase :=
          convex_support_toReal_at_basepoint hf_ne_bot hf_convex hx_f hx_diff hy_f
        rw [hinner_rev] at hbase
        linarith
      apply (EReal.sub_le_iff_le_add (Or.inr hFy_ne_top) (Or.inr hFy_ne_bot)).2
      rw [composite_model_objective_apply, composite_model_objective_apply,
        generalized_conditional_gradient_gap_objective_apply, hfx_val, hfy_val, hgx_val, hgy_val]
      let fyE : EReal := (((f y).toReal : ℝ) : EReal)
      let gyE : EReal := (((g y).toReal : ℝ) : EReal)
      let gxE : EReal := (((g x).toReal : ℝ) : EReal)
      let innerE : EReal := ((inner ℝ (∇ f₀ x) (x - y) : ℝ) : EReal)
      have hrewrite :
          fyE + gyE + (innerE + gxE - gyE) =
            ((((f y).toReal + inner ℝ (∇ f₀ x) (x - y) : ℝ) : EReal)) + gxE := by
        have hcancel : gyE + (innerE + gxE - gyE) = innerE + gxE := by
          rw [← add_sub_assoc, EReal.add_sub_cancel_left]
        -- Move the finite `g y` term next to the subtraction and cancel it.
        calc
          fyE + gyE + (innerE + gxE - gyE) = fyE + (gyE + (innerE + gxE - gyE)) := by
            rw [add_assoc]
          _ = fyE + (innerE + gxE) := by
            rw [hcancel]
          _ = ((((f y).toReal + inner ℝ (∇ f₀ x) (x - y) : ℝ) : EReal)) +
                gxE := by
            rw [← add_assoc, ← EReal.coe_add]
      rw [hrewrite]
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (EReal.coe_le_coe hsupport) gxE
    · -- Outside `dom(g)`, the comparison objective takes the value `⊤`.
      have hgy_top : g y = ⊤ := by
        have hnot_lt : ¬ g y < ⊤ := by
          simpa [effective_domain] using hy_g
        exact le_antisymm le_top (not_lt.mp hnot_lt)
      have hFy_top : F y = ⊤ := by
        rw [composite_model_objective_apply, hgy_top]
        exact EReal.add_top_of_ne_bot (hf_ne_bot y)
      rw [hFy_top]
      exact le_top
  · -- Outside `dom(f)`, the smooth term is `⊤`; because `g y ≠ ⊥` in this branch, the composite
    -- objective is also `⊤`.
    have hfy_top : f y = ⊤ := by
      have hnot_lt : ¬ f y < ⊤ := by
        simpa [effective_domain] using hy_f
      exact le_antisymm le_top (not_lt.mp hnot_lt)
    have hFy_top : F y = ⊤ := by
      rw [composite_model_objective_apply, hfy_top]
      exact EReal.top_add_iff_ne_bot.mpr hgy_bot
    rw [hFy_top]
    exact le_top

/-- Helper for Lemma 13.12: every individual gap value is bounded above by the supremal
conditional-gradient norm `S[f₀, g](x)`. -/
lemma gap_objective_le_conditional_gradient_norm
    (x y : E) :
    generalized_conditional_gradient_gap_objective f₀ g x y ≤ S[f₀, g](x) := by
  -- Rewrite `S` as the `sSup` of its defining range and insert the witness `y`.
  rw [generalized_conditional_gradient_norm_eq_sSup_gap_objective]
  exact le_sSup ⟨y, rfl⟩

/-- Lemma 13.12: if `f` is convex, never takes the value `⊥`, and `f₀` is differentiable at the
base point `x ∈ dom(f) ∩ dom(g)`, then the canonical generalized conditional-gradient norm
dominates the objective gap `F x - F_opt`. Under Assumption 13.1, the differentiability
hypothesis is supplied at every feasible point by Theorem 13.6. -/
theorem generalized_conditional_gradient_gap_ge_objective_gap
    {x : E}
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_convex : is_convex_function f)
    (hx_f : x ∈ effective_domain f)
    (hx_diff : DifferentiableAt ℝ f₀ x)
    (hx : x ∈ effective_domain g) :
    S[f₀, g](x) ≥ F x - F_opt := by
  by_cases hS_top : S[f₀, g](x) = ⊤
  · -- If the supremal gap is already `⊤`, the claimed lower bound is automatic.
    simp [hS_top]
  have hFx_lt_top : F x < ⊤ := by
    -- The base objective is finite because both summands are finite at `x`.
    rw [composite_model_objective_apply]
    exact EReal.add_lt_top (mem_effective_domain.mp hx_f).ne (mem_effective_domain.mp hx).ne
  have hFopt_le_Fx : F_opt ≤ F x := by
    -- The canonical optimal value is the infimum of the attained objective values.
    rw [generalized_conditional_gradient_optimal_value_eq_sInf]
    exact sInf_le ⟨x, rfl⟩
  have hFopt_ne_top : F_opt ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hFopt_le_Fx hFx_lt_top)
  have hlower :
      F x - S[f₀, g](x) ≤ F_opt := by
    rw [generalized_conditional_gradient_optimal_value_eq_sInf]
    apply le_sInf
    rintro _ ⟨y, rfl⟩
    have hpoint :
        F x - generalized_conditional_gradient_gap_objective f₀ g x y ≤ F y :=
      objective_minus_gap_le_objective_value
        hf_ne_bot hf_convex hx_f hx_diff hx y
    have hgap :
        generalized_conditional_gradient_gap_objective f₀ g x y ≤ S[f₀, g](x) :=
      gap_objective_le_conditional_gradient_norm x y
    -- Lowering the subtracted gap term preserves the objective comparison.
    exact (EReal.sub_le_sub le_rfl hgap).trans hpoint
  -- Convert the lower-bound statement `F x - S ≤ F_opt` back to the desired gap inequality.
  have hadd : F x ≤ F_opt + S[f₀, g](x) :=
    (EReal.sub_le_iff_le_add (Or.inr hFopt_ne_top) (Or.inl hS_top)).1 hlower
  exact
    (EReal.sub_le_iff_le_add (Or.inr hS_top) (Or.inl hFopt_ne_top)).2
      (by simpa [add_comm] using hadd)

end

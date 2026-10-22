/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_10
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open InnerProductSpace (toDual)
open scoped Gradient

/- `prompt_add/` is absent in this workspace, so the statement design is checked against the local
owners for the actual mathematics of Theorem 13.6:

- `generalized_conditional_gradient_norm` and Lemma 13.5 for the Chapter 13 gap quantity `S(x)`;
- `fenchel_inequality` and `pairing_eq_add_conjugate_iff_mem_subdifferential` for the Chapter 4
  Fenchel/Fenchel--Young characterization;
- `is_stationary_point` for the finite-dimensional Chapter 3 stationarity owner.

This item is `source-facing`. The primitive data is the gap quantity `S[f₀, g](x)` together with
the `g`-side Fenchel/subdifferential hypotheses actually used by the characterization. Assumption
13.1 is not the owner of that characterization: it is only a `bridge/view` that later supplies the
pointwise differentiability hypothesis needed to rewrite the subdifferential condition as
stationarity. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g : E → EReal}

local notation "f₀" => fun y ↦ EReal.toReal (f y)

/-- Helper for Theorem 13.6: evaluating the negative-gradient Riesz functional at `x` gives the
negative inner-product term appearing in Lemma 13.5. -/
private lemma neg_gradient_pairing_eq_neg_inner (x : E) :
    (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) =
      -(((inner ℝ (∇ f₀ x) x : ℝ) : EReal)) := by
  -- Identify the Chapter 4 pairing with the Chapter 13 inner-product expression.
  simp [InnerProductSpace.toDual_apply_eq_toDualMap_apply,
    InnerProductSpace.toDualMap_apply_apply]

-- Proof sketch: rewrite `S(x)` by Lemma 13.5 as
-- `⟪∇f(x), x⟫ + g(x) + g∗(-∇f(x))`, then apply Fenchel's inequality to `g` at the pair
-- `(x, -∇ (fun y ↦ (f y).toReal) x)`.
/-- Theorem 13.6 (1): the generalized conditional-gradient norm `S(x)` is nonnegative for every
`x`, under the properness assumptions on `g` actually used by Fenchel's inequality. -/
theorem generalized_conditional_gradient_norm_nonneg
    (hg_proper : IsProperExtendedRealFunction g) (x : E) :
    0 ≤ S[f₀, g](x) := by
  have hfenchel :
      (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) ≤
        g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) := by
    -- Fenchel's inequality identifies the gap as a translated nonnegative residual.
    simpa [add_comm] using
      (fenchel_inequality g x (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) hg_proper)
  have hresidual :
      (0 : EReal) ≤
        g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) -
          (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) := by
    -- Subtract the pairing term to expose the nonnegative Fenchel residual.
    have hpair_ne_top :
        (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) ≠ ⊤ := by
      simp
    have hpair_ne_bot :
        (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) ≠ ⊥ := by
      simp
    exact
      (EReal.sub_nonneg (.inr hpair_ne_top) (.inr hpair_ne_bot)).2 hfenchel
  -- Rewrite the residual back into the Chapter 13 expression for `S(x)`.
  rw [generalized_conditional_gradient_norm_eq_inner_add_value_add_conjugate]
  simpa [neg_gradient_pairing_eq_neg_inner, conjugate_function_primal_apply,
    InnerProductSpace.toDual_apply_eq_toDualMap_apply, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using hresidual

/-- Helper for Theorem 13.6: vanishing of the conditional-gradient norm is exactly the
Fenchel--Young equality for `g` at `(x, -∇ f₀ x)`. -/
private lemma generalized_conditional_gradient_norm_eq_zero_iff_fenchel_young_equality
    (x : E) :
    S[f₀, g](x) = 0 ↔
      (((-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) x : EReal)) =
        g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) := by
  constructor
  · intro hS
    rw [generalized_conditional_gradient_norm_eq_inner_add_value_add_conjugate] at hS
    let r : EReal := g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E)
    have hshift :
        (((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + r) = 0 := by
      -- Rewrite `S(x) = 0` into a single affine-plus-conjugate equality.
      simpa [conjugate_function_primal_apply, InnerProductSpace.toDual_apply_eq_toDualMap_apply,
        r, add_assoc] using hS
    have hcancel :
        r =
          -(((inner ℝ (∇ f₀ x) x : ℝ) : EReal)) := by
      -- Cancel the finite inner-product term from both sides.
      have htranslated := congrArg
        (fun z : EReal ↦ z - (inner ℝ (∇ f₀ x) x : ℝ)) hshift
      calc
        r = ((((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + r) - (inner ℝ (∇ f₀ x) x : ℝ)) := by
              symm
              exact EReal.add_sub_cancel_left
        _ = -(((inner ℝ (∇ f₀ x) x : ℝ) : EReal)) := by
              simpa using htranslated
    simpa [r, neg_gradient_pairing_eq_neg_inner] using hcancel.symm
  · intro hfy
    rw [generalized_conditional_gradient_norm_eq_inner_add_value_add_conjugate]
    have hpair :
        g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E) =
          -(((inner ℝ (∇ f₀ x) x : ℝ) : EReal)) := by
      -- Convert the Fenchel--Young equality back to the affine-plus-conjugate form.
      simpa [neg_gradient_pairing_eq_neg_inner] using hfy.symm
    -- Substitute the equality case into Lemma 13.5 and collapse the finite term.
    calc
      ((inner ℝ (∇ f₀ x) x : ℝ) : EReal) + g x + (g∗) (-∇ f₀ x) =
          ((inner ℝ (∇ f₀ x) x : ℝ) : EReal) +
            (g x + conjugate_function g (-toDual ℝ E (∇ f₀ x) : Module.Dual ℝ E)) := by
              simp [conjugate_function_primal_apply,
                InnerProductSpace.toDual_apply_eq_toDualMap_apply, add_assoc]
      _ = ((inner ℝ (∇ f₀ x) x : ℝ) : EReal) +
            (-(((inner ℝ (∇ f₀ x) x : ℝ) : EReal))) := by
              rw [hpair]
      _ = 0 := by
              simpa [sub_eq_add_neg] using
                (EReal.sub_self (by simp) (by simp))

-- Proof sketch: rewrite `S(xStar)` by Lemma 13.5. The equality `S(xStar) = 0` is exactly the
-- Fenchel--Young equality case for `g` at `(xStar, -∇ (fun y ↦ (f y).toReal) xStar)`, so Theorem
-- 4.10 rewrites it as subdifferential membership. Only the no-`⊥` hypothesis on `g` is active.
/-- Theorem 13.6 (2), source-facing form: the generalized
conditional-gradient norm vanishes if and only if the negative gradient belongs to the
subdifferential of `g` at `xStar`. -/
theorem generalized_conditional_gradient_norm_eq_zero_iff_neg_gradient_mem_subdifferential
    (hg_ne_bot : ∀ z, g z ≠ ⊥) (xStar : E) :
    S[f₀, g](xStar) = 0 ↔
      (-toDual ℝ E (∇ f₀ xStar) : Module.Dual ℝ E) ∈ ∂ g(xStar) := by
  -- Route correction: match the source proof through Fenchel--Young equality, not by unfolding
  -- the subdifferential definition directly.
  rw [generalized_conditional_gradient_norm_eq_zero_iff_fenchel_young_equality]
  -- The Chapter 4 equality criterion is exactly the required subdifferential characterization.
  simpa using
    (pairing_eq_add_conjugate_iff_mem_subdifferential g hg_ne_bot xStar
      (-toDual ℝ E (∇ f₀ xStar) : Module.Dual ℝ E))

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g : E → EReal}

local notation "f₀" => fun y ↦ EReal.toReal (f y)

local instance theorem13_6_completeSpace : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

-- Proof sketch: use
-- `generalized_conditional_gradient_norm_eq_zero_iff_neg_gradient_mem_subdifferential`, then
-- combine the resulting subdifferential membership with the explicit differentiability hypothesis
-- and unfold `is_stationary_point`.
/-- The finite-dimensional Chapter 3 stationarity owner rewrites the vanishing gap condition as
stationarity once differentiability of `f` at `xStar` is supplied explicitly. -/
theorem
    generalized_conditional_gradient_norm_eq_zero_iff_is_stationary_point_of_is_differentiable_at
    (hg_ne_bot : ∀ z, g z ≠ ⊥) (xStar : E) (hdiff : is_differentiable_at f xStar) :
    S[f₀, g](xStar) = 0 ↔
      is_stationary_point f g xStar := by
  rw [is_stationary_point_iff]
  constructor
  · intro hx
    exact
      ⟨hdiff,
        (generalized_conditional_gradient_norm_eq_zero_iff_neg_gradient_mem_subdifferential
          hg_ne_bot xStar).1 hx⟩
  · rintro ⟨_, hxsub⟩
    exact
      (generalized_conditional_gradient_norm_eq_zero_iff_neg_gradient_mem_subdifferential
        hg_ne_bot xStar).2 hxsub

-- Proof sketch: Assumption 13.1 contributes only the pointwise differentiability hypothesis
-- through `IsGeneralizedConditionalGradientProblem.is_differentiable_at`, so the stationarity
-- equivalence is a direct bridge corollary from the owner-level theorem above.
/-- Under Assumption 13.1, the explicit differentiability hypothesis in the stationarity
reformulation is supplied automatically. -/
theorem generalized_conditional_gradient_norm_eq_zero_iff_is_stationary_point
    {Lf : NNReal} (hproblem : IsGeneralizedConditionalGradientProblem f g Lf)
    (xStar : effective_domain f) :
    S[f₀, g](xStar) = 0 ↔
      is_stationary_point f g xStar :=
  generalized_conditional_gradient_norm_eq_zero_iff_is_stationary_point_of_is_differentiable_at
    hproblem.ne_bot xStar (hproblem.is_differentiable_at xStar)

end

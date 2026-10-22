/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Example 9.31: the hypothesis `f 0 = 0` makes the origin belong to the effective
domain. -/
lemma zero_mem_effectiveDomain_of_zero_value
    (f : H → Set.Ioi (⊥ : EReal)) (hzero : (f 0 : EReal) = 0) :
    0 ∈ effectiveDomain f := by
  -- Rewriting the value at the origin shows directly that it is finite.
  rw [mem_effectiveDomain_iff, hzero]
  simp

omit [CompleteSpace H] in
/-- Helper for Example 9.31: positive homogeneity collapses the scaled ray based at the origin to
the constant value `f y`. -/
lemma scaled_ray_at_origin_eq_constant_of_positivelyHomogeneous
    (f : H → Set.Ioi (⊥ : EReal))
    (hph : ∀ ⦃a : ℝ⦄, 0 < a → ∀ x : H,
      (f (a • x) : EReal) = (a : EReal) * (f x : EReal))
    (y : H) :
    (fun α : Set.Ioi (0 : ℝ) ↦ (f (0 + (α : ℝ) • y) : EReal) / (α : ℝ)) =
      fun _ ↦ (f y : EReal) := by
  funext α
  -- Rewrite the numerator with positive homogeneity and cancel the positive scalar.
  rw [zero_add, hph α.2 y]
  have hαE : (0 : EReal) < (α : EReal) := by
    exact_mod_cast α.2
  exact
    (EReal.div_eq_iff (ne_bot_of_gt hαE) (EReal.coe_ne_top (α : ℝ)) (ne_of_gt hαE)).2
      (by simp [mul_comm])

/-- Helper for Example 9.31: the pointwise value of the recession function agrees with `f` under
the strengthened origin and positive-homogeneity hypotheses. -/
lemma recessionFunction_eq_value_pointwise_of_positivelyHomogeneous
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hzero : (f 0 : EReal) = 0)
    (hph : ∀ ⦃a : ℝ⦄, 0 < a → ∀ x : H,
      (f (a • x) : EReal) = (a : EReal) * (f x : EReal))
    (y : H) :
    (recessionFunction f hf.2.nonempty y : EReal) = (f y : EReal) := by
  have h0dom : 0 ∈ effectiveDomain f :=
    zero_mem_effectiveDomain_of_zero_value f hzero
  have hleft :
      Filter.Tendsto
        (fun α : Set.Ioi (0 : ℝ) ↦ (f (0 + (α : ℝ) • y) : EReal) / (α : ℝ))
        Filter.atTop
        (nhds ((recessionFunction f hf.2.nonempty y : EReal))) := by
    -- Proposition 9.30(iii) evaluates the recession function through the scaled ray at `x = 0`.
    exact tendsto_scaled_ray_values_to_recessionFunction (f := f) (hf := hf) (hx := h0dom) y
  have hright :
      Filter.Tendsto
        (fun _ : Set.Ioi (0 : ℝ) ↦ (f y : EReal))
        Filter.atTop
        (nhds (f y : EReal)) := by
    -- The rewritten scaled ray is constant, so its limit is the constant value.
    exact tendsto_const_nhds
  have hleft' :
      Filter.Tendsto
        (fun _ : Set.Ioi (0 : ℝ) ↦ (f y : EReal))
        Filter.atTop
        (nhds ((recessionFunction f hf.2.nonempty y : EReal))) := by
    -- Positive homogeneity turns the scaled ray into the constant map from the previous helper.
    rw [← scaled_ray_at_origin_eq_constant_of_positivelyHomogeneous (f := f) hph y]
    exact hleft
  -- The common ray has both limits, so uniqueness identifies the recession value with `f y`.
  exact tendsto_nhds_unique hleft' hright

/-- Example 9.31: a positively homogeneous function in `Γ₀(H)` that is finite and zero at the
origin coincides with its recession function. -/
-- Proof sketch: use Proposition 9.30(iii) or (iv) to express the recession function through
-- scaled ray values or directional quotients, then simplify those expressions with positive
-- homogeneity.
theorem recessionFunction_eq_self_of_positivelyHomogeneous
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hzero : (f 0 : EReal) = 0)
    (hph : ∀ ⦃a : ℝ⦄, 0 < a → ∀ x : H, (f (a • x) : EReal) = (a : EReal) * (f x : EReal)) :
    recessionFunction f hf.2.nonempty = f := by
  funext y
  -- The helper reduces the function equality to the pointwise `EReal` equality already proved.
  apply Subtype.ext
  exact recessionFunction_eq_value_pointwise_of_positivelyHomogeneous f hf hzero hph y

end ERealFunction

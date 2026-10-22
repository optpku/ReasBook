/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 3.14 is a `source-facing` theorem in the chapter convex-analysis API. Its owner
declarations are already the chapter/project primitives `effective_domain`, `is_subgradient_at`,
and `subdifferential`, so this file contributes only the positive-scaling calculus theorems. -/
recall effective_domain
recall is_subgradient_at
recall subdifferential
recall mem_subdifferential

-- Proof sketch: for `α > 0`, multiplication by `(α : EReal)` is order-preserving and sends `⊤`
-- to `⊤`, so `((α : EReal) * f x) < ⊤` holds exactly when `f x < ⊤`. Extensionality on points
-- then gives equality of the two effective domains.
/-- Helper for Theorem 3.14: positive real scaling preserves the effective domain of an
extended-real-valued function. -/
private theorem effective_domain_pos_real_mul {E : Type u} (f : E → EReal) (α : ℝ) (hα : 0 < α) :
    effective_domain (fun x ↦ (α : EReal) * f x) = effective_domain f := by
  have hαE_pos : (0 : EReal) < (α : EReal) := by
    simpa using hα
  have hαE_nonneg : (0 : EReal) ≤ (α : EReal) := le_of_lt hαE_pos
  have hαE_not_le_zero : ¬ (α : EReal) ≤ 0 := not_le_of_gt hαE_pos
  have hαE_ne_bot : (α : EReal) ≠ ⊥ := by
    simp
  have hαE_ne_top : (α : EReal) ≠ ⊤ := by
    simp
  ext x
  -- Reduce both domain memberships to `≠ ⊤` and simplify the positive-scalar product criterion.
  rw [mem_effective_domain, mem_effective_domain, lt_top_iff_ne_top, lt_top_iff_ne_top]
  simp [EReal.mul_ne_top, hαE_nonneg, hαE_not_le_zero, hαE_ne_bot, hαE_ne_top]

/-- Helper for Theorem 3.14: the affine support inequality for `α f` is equivalent to the
corresponding inequality for `f` after transporting the dual vector by `α⁻¹`. -/
private theorem supportInequality_pos_real_mul_iff
    (f : E → EReal) (α : ℝ) (hα : 0 < α) {x y : E} {g : Module.Dual ℝ E} :
    ((α : EReal) * f y ≥ (α : EReal) * f x + (g (y - x) : EReal)) ↔
      f y ≥ f x + ((((α⁻¹ • g) (y - x) : ℝ) : EReal)) := by
  let αE : EReal := α
  let transported : EReal := (((α⁻¹ • g) (y - x) : ℝ) : EReal)
  have hαE_pos : 0 < αE := by
    simpa [αE] using hα
  have hαE_nonneg : 0 ≤ αE := le_of_lt hαE_pos
  have hαE_ne_bot : αE ≠ ⊥ := by
    simp [αE]
  have hαE_ne_top : αE ≠ ⊤ := by
    simp [αE]
  have hαE_ne_zero : αE ≠ 0 := by
    simpa [αE] using (ne_of_gt hα : α ≠ 0)
  have htransportReal : ((α⁻¹ • g) (y - x)) * α = g (y - x) := by
    -- Evaluate the inverse-scaled dual vector and cancel `α⁻¹ * α` on the real side.
    rw [LinearMap.smul_apply, map_sub, smul_eq_mul]
    calc
      α⁻¹ * (g y - g x) * α = (α⁻¹ * α) * g y - (α⁻¹ * α) * g x := by ring
      _ = g y - g x := by
        simp [inv_mul_cancel₀ (ne_of_gt hα)]
  have htransport : transported * αE = (g (y - x) : EReal) := by
    -- Lift the real cancellation identity to `EReal`.
    dsimp [transported, αE]
    change ((((α⁻¹ • g) (y - x)) * α : ℝ) : EReal) = (g (y - x) : EReal)
    exact congrArg (fun r : ℝ ↦ (r : EReal)) htransportReal
  constructor
  · intro h
    -- Rewrite the scaled inequality as a right-multiplied inequality and divide by `α`.
    have hscaled : (f x + transported) * αE ≤ αE * f y := by
      calc
        (f x + transported) * αE = f x * αE + transported * αE := by
          exact EReal.right_distrib_of_nonneg_of_ne_top hαE_nonneg hαE_ne_top _ _
        _ = αE * f x + (g (y - x) : EReal) := by
          rw [htransport, mul_comm]
        _ ≤ αE * f y := by
          simpa [αE, ge_iff_le] using h
    have hdiv : f x + transported ≤ (αE * f y) / αE := by
      exact (EReal.le_div_iff_mul_le hαE_pos hαE_ne_top).2 hscaled
    have hcancel : (αE * f y) / αE = f y := by
      have hcancel' : f y * αE / ((1 : EReal) * αE) = f y / (1 : EReal) :=
        EReal.mul_div_mul_cancel hαE_ne_bot hαE_ne_top hαE_ne_zero
      simpa [mul_comm, one_mul, div_one] using hcancel'
    simpa [transported, ge_iff_le, hcancel] using hdiv
  · intro h
    -- Multiply the unscaled inequality by `α` and simplify the transported dual term.
    have hscaled : (f x + transported) * αE ≤ f y * αE := by
      exact mul_le_mul_of_nonneg_right (by simpa [transported, ge_iff_le] using h) hαE_nonneg
    have hrewritten : αE * f x + (g (y - x) : EReal) ≤ αE * f y := by
      calc
        αE * f x + (g (y - x) : EReal) = f x * αE + transported * αE := by
          rw [mul_comm αE (f x), ← htransport]
        _ = (f x + transported) * αE := by
          symm
          exact EReal.right_distrib_of_nonneg_of_ne_top hαE_nonneg hαE_ne_top _ _
        _ ≤ f y * αE := hscaled
        _ = αE * f y := by
          rw [mul_comm]
    simpa [αE, ge_iff_le] using hrewritten

-- Proof sketch: rewrite both sides using `mem_subdifferential` and `is_subgradient_at`; the
-- domain clause is transported by `effective_domain_pos_real_mul`, and the supporting inequality
-- is equivalent after dividing by the positive scalar `α`.
/-- Companion to Theorem 3.14: membership in the subdifferential of a positive scalar multiple is
equivalent to membership after inverse scalar transport on the dual side. -/
theorem mem_subdifferential_pos_real_mul_iff
    (f : E → EReal) (α : ℝ) (hα : 0 < α) (x : E) (g : Module.Dual ℝ E) :
    g ∈ ∂ (((α : EReal) • f))(x) ↔ α⁻¹ • g ∈ ∂ f(x) := by
  change g ∈ subdifferential (fun y ↦ (α : EReal) * f y) x ↔ α⁻¹ • g ∈ ∂ f(x)
  rw [mem_subdifferential, mem_subdifferential]
  rw [is_subgradient_at_iff_forall_mem_effective_domain,
    is_subgradient_at_iff_forall_mem_effective_domain]
  constructor
  · rintro ⟨hx, hg⟩
    refine ⟨?_, ?_⟩
    · -- Transport the base-point domain condition through positive scaling.
      simpa [effective_domain_pos_real_mul f α hα] using hx
    · intro y hy
      have hyScaled : y ∈ effective_domain (fun z ↦ (α : EReal) * f z) := by
        simpa [effective_domain_pos_real_mul f α hα] using hy
      -- Rewrite the scaled support inequality in the unscaled owner form.
      exact (supportInequality_pos_real_mul_iff f α hα).1 (hg y hyScaled)
  · rintro ⟨hx, hg⟩
    refine ⟨?_, ?_⟩
    · -- The same domain transport closes the reverse implication.
      simpa [effective_domain_pos_real_mul f α hα] using hx
    · intro y hy
      have hyUnscaled : y ∈ effective_domain f := by
        simpa [effective_domain_pos_real_mul f α hα] using hy
      -- Push the owner-level inequality forward by multiplying through by `α`.
      exact (supportInequality_pos_real_mul_iff f α hα).2 (hg y hyUnscaled)

-- Proof sketch: extensionality on `g`; rewrite membership in the scaled set with the canonical
-- pointwise-scalar lemma `Set.mem_smul_set_iff_inv_smul_mem₀`, then apply the owner-level
-- equivalence `mem_subdifferential_pos_real_mul_iff`. No extra domain/properness assumptions are
-- needed in the public theorem because positive scaling preserves the effective domain, so both
-- sides are empty whenever `x ∉ effective_domain f`.
/-- Theorem 3.14: for `α > 0`, scaling an extended-real-valued function `f` by `α` scales its
subdifferential at `x` by the same positive scalar. -/
theorem subdifferential_pos_real_mul (f : E → EReal) (α : ℝ) (hα : 0 < α) (x : E) :
    ∂ (((α : EReal) • f))(x) = α • ∂ f(x) := by
  ext g
  -- Rewrite pointwise scalar-set membership into the inverse-scaled owner predicate.
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hα)]
  -- The private owner-level equivalence matches the function-side pointwise scaling exactly.
  simpa [Pi.smul_apply, smul_eq_mul] using mem_subdifferential_pos_real_mul_iff f α hα x g

end

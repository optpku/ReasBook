/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 7.18 lies in the Chapter 7 strict-positivity / closed-convex weighted-sum
subdifferential domain.

Mandatory domain-style sampling before refinement:
- `StrictlyPositiveOn` and `StrictlyPositiveOn.inequality` in `Definition_7_81`, the source-facing
  owner and its primitive projection lemma;
- `ClosedConvexFunction` in `Chap03/Definition_3_1_1_5`, the canonical closed-convex owner for
  `WithTop ℝ`-valued functions, used on the chapter’s standard pointwise lift
  `fun x ↦ (f x : WithTop ℝ)`;
- `ClosedConvexFunction.nonneg_weighted_add` and
  `subdifferential_nonneg_weighted_add_eq_of_pos` in `Chap03/Lemma_3_1_12`, the chapter's
  closed-convex weighted-sum API written directly on the canonical pointwise combination
  `α₁ • f₁ + α₂ • f₂`;
- `ClosedConvexOn.nonneg_smul` in `Chap03/Theorem_3_1_5`, the owner pattern behind the zero-weight
  and one-summand branches.

Best owner abstraction:
- source-facing: `StrictlyPositiveOn Q f`;
- core/canonical: the closed-convex owner
  `ClosedConvexFunction (fun x ↦ (f x : WithTop ℝ))` together with the canonical pointwise
  weighted sum `α₁ • f₁ + α₂ • f₂`;
- bridge/view: the source-facing closure theorems in this file, which keep the conclusion on
  `StrictlyPositiveOn` while routing the genuinely two-summand case through the Chapter 3
  closed-convex sum rule.

Primitive data:
- the set `Q`;
- the summands `f₁`, `f₂`;
- the closed-convex owner witnesses `hcc₁`, `hcc₂` for the lifted summands;
- the weights `α₁`, `α₂`;
- the owner witnesses `hf₁`, `hf₂`.

Derived API:
- `StrictlyPositiveOn.nonneg_smul`;
- `StrictlyPositiveOn.nonnegative_linear_combination`.
-/

/-- Helper for Lemma 7.18: the lifted `WithTop ℝ` subdifferential of a real-valued function is
the whole-space real-valued subdifferential. -/
lemma mem_lifted_subdifferential_iff_mem_subdifferential_univ
    {h : E → ℝ} {x g : E} :
    g ∈ ∂ (fun z ↦ (h z : WithTop ℝ))(x) ↔ g ∈ ∂[Set.univ] h(x) := by
  -- Rewrite both owners to the same global affine lower-support inequality.
  rw [mem_subdifferential_coe_real_iff, mem_subdifferentialWithin_iff]
  simp

/-- Helper for Lemma 7.18: a whole-space subgradient of a positive weighted sum of lifted
functions decomposes into the corresponding weighted sum of whole-space subgradients. -/
lemma exists_subgradient_decomposition_of_mem_weighted_sum_subdifferential
    {f₁ f₂ : E → ℝ}
    (hcc₁ : ClosedConvexFunction (fun x ↦ (f₁ x : WithTop ℝ)))
    (hcc₂ : ClosedConvexFunction (fun x ↦ (f₂ x : WithTop ℝ)))
    {α₁ α₂ : ℝ} (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    {x g : E}
    (hg : g ∈ ∂[Set.univ] (α₁ • f₁ + α₂ • f₂)(x)) :
    ∃ g₁ g₂,
      g₁ ∈ ∂[Set.univ] f₁(x) ∧
      g₂ ∈ ∂[Set.univ] f₂(x) ∧
      g = α₁ • g₁ + α₂ • g₂ := by
  have hx :
      x ∈ interior
        (dom
          (((α₁ : WithTop ℝ) • (fun z ↦ (f₁ z : WithTop ℝ)) +
            (α₂ : WithTop ℝ) • (fun z ↦ (f₂ z : WithTop ℝ)))) ) := by
    -- Real-valued lifts are finite everywhere, so the weighted sum has full interior domain.
    rw [interior_effectiveDomain_nonneg_weighted_add_eq_of_pos hα₁ hα₂]
    simp [withTopEffectiveDomain]
  have hg_lifted_base :
      g ∈ ∂ (fun z ↦ (((α₁ • f₁ + α₂ • f₂) z : ℝ) : WithTop ℝ))(x) :=
    (mem_lifted_subdifferential_iff_mem_subdifferential_univ).2 hg
  have hg_lifted :
      g ∈ ∂
        (((α₁ : WithTop ℝ) • (fun z ↦ (f₁ z : WithTop ℝ)) +
          (α₂ : WithTop ℝ) • (fun z ↦ (f₂ z : WithTop ℝ))))(x) := by
    -- Move the source-facing real-valued subgradient to the Chapter 3 lifted surface.
    simpa [Pi.smul_apply, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hg_lifted_base
  rw [subdifferential_nonneg_weighted_add_eq_of_pos hcc₁ hcc₂ hα₁ hα₂ hx] at hg_lifted
  rcases Set.mem_add.1 hg_lifted with ⟨u, hu, v, hv, hsum⟩
  have hu' : α₁⁻¹ • u ∈ ∂ (fun z ↦ (f₁ z : WithTop ℝ))(x) := by
    -- Undo the positive scalar action on the first summand subdifferential.
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hα₁.ne'] at hu
    simpa using hu
  have hv' : α₂⁻¹ • v ∈ ∂ (fun z ↦ (f₂ z : WithTop ℝ))(x) := by
    -- Undo the positive scalar action on the second summand subdifferential.
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hα₂.ne'] at hv
    simpa using hv
  refine ⟨α₁⁻¹ • u, α₂⁻¹ • v, ?_, ?_, ?_⟩
  · -- Return to the source-facing whole-space real-valued owner for the first summand.
    exact (mem_lifted_subdifferential_iff_mem_subdifferential_univ).mp hu'
  · -- Return to the source-facing whole-space real-valued owner for the second summand.
    exact (mem_lifted_subdifferential_iff_mem_subdifferential_univ).mp hv'
  · -- Reassemble the original subgradient from the two weighted pieces.
    calc
      g = u + v := hsum.symm
      _ = α₁ • (α₁⁻¹ • u) + α₂ • (α₂⁻¹ • v) := by
        rw [smul_inv_smul₀ hα₁.ne', smul_inv_smul₀ hα₂.ne']

-- Proof sketch: if `α = 0`, the target is the zero function, whose only whole-space subgradient
-- is `0`; if `α > 0`, divide the defining subgradient inequality for `α • f` by `α` to recover a
-- subgradient of `f`, then rescale the strict-positivity inequality.
theorem StrictlyPositiveOn.nonneg_smul
    {Q : Set E} {f : E → ℝ} (hf : StrictlyPositiveOn Q f)
    {α : ℝ} (hα : 0 ≤ α) :
    StrictlyPositiveOn Q (α • f) := by
  intro x y g hx hy hg
  by_cases hα_zero : α = 0
  · rcases mem_subdifferentialWithin_iff.mp hg with ⟨-, hsubgrad⟩
    have hgg : 0 ≥ inner ℝ g g := by
      -- Evaluate the zero-function support inequality at `x + g`.
      -- This forces the whole-space subgradient to vanish.
      simpa [hα_zero, Pi.smul_apply] using hsubgrad (by simp : x + g ∈ Set.univ)
    have hnorm_sq : ‖g‖ ^ (2 : ℕ) ≤ 0 := by
      simpa [real_inner_self_eq_norm_sq] using hgg
    have hnorm : ‖g‖ = 0 := by
      nlinarith [sq_nonneg ‖g‖, hnorm_sq]
    have hg_zero : g = 0 := norm_eq_zero.mp hnorm
    -- Once the only whole-space subgradient is `0`, the strict-positivity inequality is trivial.
    simp [hα_zero, hg_zero, Pi.smul_apply]
  · have hα_pos : 0 < α := lt_of_le_of_ne hα (by
        intro hzero
        exact hα_zero hzero.symm)
    let g' : E := α⁻¹ • g
    have hg' : g' ∈ ∂[Set.univ] f(x) := by
      rw [mem_subdifferentialWithin_iff] at hg ⊢
      rcases hg with ⟨-, hsubgrad⟩
      refine ⟨by simp, ?_⟩
      intro z hz
      have hz' : α * f z ≥ α * f x + inner ℝ g (z - x) := by
        -- Expand the scalar multiple of `f` to expose a positive scalar factor.
        simpa [Pi.smul_apply, smul_eq_mul] using hsubgrad hz
      have hz'' : α * (f x + inner ℝ g' (z - x)) ≤ α * f z := by
        calc
          α * (f x + inner ℝ g' (z - x))
              = α * f x + inner ℝ g (z - x) := by
                rw [mul_add]
                congr 1
                calc
                  α * inner ℝ g' (z - x)
                      = α * (α⁻¹ * inner ℝ g (z - x)) := by
                          simp [g', real_inner_smul_left]
                  _ = inner ℝ g (z - x) := by
                    field_simp [hα_pos.ne']
          _ ≤ α * f z := by linarith
      -- Divide the support inequality by the positive weight to recover a subgradient of `f`.
      exact le_of_mul_le_mul_left hz'' hα_pos
    have hineq : 0 ≤ f y + f x + inner ℝ g' (y - x) :=
      hf.inequality hx hy hg'
    have hrewrite :
        α * (f y + f x + inner ℝ g' (y - x)) =
          (α • f) y + (α • f) x + inner ℝ g (y - x) := by
      calc
        α * (f y + f x + inner ℝ g' (y - x))
            = α * f y + α * f x + α * inner ℝ g' (y - x) := by
              ring
        _ = α * f y + α * f x + inner ℝ g (y - x) := by
          congr 1
          calc
            α * inner ℝ g' (y - x)
                = α * (α⁻¹ * inner ℝ g (y - x)) := by
                    simp [g', real_inner_smul_left]
            _ = inner ℝ g (y - x) := by
              field_simp [hα_pos.ne']
        _ = (α • f) y + (α • f) x + inner ℝ g (y - x) := by
          simp [Pi.smul_apply, smul_eq_mul]
    -- Scale the verified strict-positivity inequality for `f` back by the nonnegative weight.
    rw [← hrewrite]
    exact mul_nonneg hα hineq

-- Proof sketch: split the zero-weight branches and dispatch them with
-- `StrictlyPositiveOn.nonneg_smul`. In the genuinely two-summand branch `α₁, α₂ > 0`, use
-- `subdifferential_nonneg_weighted_add_eq_of_pos` for the canonical `WithTop` lifts to write a
-- subgradient of `α₁ • f₁ + α₂ • f₂` as `α₁ • g₁ + α₂ • g₂`, then combine the defining
-- inequalities from `hf₁` and `hf₂`.
/-- Lemma 7.18: if the canonical `WithTop ℝ` lifts of `f₁` and `f₂` are closed convex and each
is strictly positive on `Q`, then every nonnegative linear combination `α₁ • f₁ + α₂ • f₂` is
strictly positive on `Q`. -/
theorem StrictlyPositiveOn.nonnegative_linear_combination
    {Q : Set E} {f₁ f₂ : E → ℝ}
    (hf₁ : StrictlyPositiveOn Q f₁) (hf₂ : StrictlyPositiveOn Q f₂)
    (hcc₁ : ClosedConvexFunction (fun x ↦ (f₁ x : WithTop ℝ)))
    (hcc₂ : ClosedConvexFunction (fun x ↦ (f₂ x : WithTop ℝ)))
    {α₁ α₂ : ℝ} (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂) :
    StrictlyPositiveOn Q (α₁ • f₁ + α₂ • f₂) := by
  by_cases hα₁_zero : α₁ = 0
  · -- Collapse the first summand and reuse the scalar-cone theorem for `f₂`.
    simpa [hα₁_zero] using (hf₂.nonneg_smul hα₂)
  · have hα₁_pos : 0 < α₁ := lt_of_le_of_ne hα₁ (by
        intro hzero
        exact hα₁_zero hzero.symm)
    by_cases hα₂_zero : α₂ = 0
    · -- Collapse the second summand and reuse the scalar-cone theorem for `f₁`.
      simpa [hα₂_zero, add_comm] using (hf₁.nonneg_smul hα₁)
    · have hα₂_pos : 0 < α₂ := lt_of_le_of_ne hα₂ (by
          intro hzero
          exact hα₂_zero hzero.symm)
      intro x y g hx hy hg
      rcases exists_subgradient_decomposition_of_mem_weighted_sum_subdifferential
          hcc₁ hcc₂ hα₁_pos hα₂_pos hg with
        ⟨g₁, g₂, hg₁, hg₂, hdecomp⟩
      have hineq₁ : 0 ≤ f₁ y + f₁ x + inner ℝ g₁ (y - x) :=
        hf₁.inequality hx hy hg₁
      have hineq₂ : 0 ≤ f₂ y + f₂ x + inner ℝ g₂ (y - x) :=
        hf₂.inequality hx hy hg₂
      have hsum :
          0 ≤ α₁ * (f₁ y + f₁ x + inner ℝ g₁ (y - x)) +
            α₂ * (f₂ y + f₂ x + inner ℝ g₂ (y - x)) := by
        -- Weight the two verified strict-positivity inequalities and add them.
        exact add_nonneg (mul_nonneg hα₁ hineq₁) (mul_nonneg hα₂ hineq₂)
      rw [hdecomp]
      -- Expand the weighted sum and the decomposed subgradient into the same affine expression.
      simpa [Pi.smul_apply, smul_eq_mul, inner_add_left, real_inner_smul_left,
        mul_add, add_mul, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        using hsum

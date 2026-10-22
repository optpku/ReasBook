/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Example 5.3.1.4 lies in the Chapter 5 self-concordant-barrier / logarithmic-sublevel-barrier
domain.

Sampled owner-style declarations in this domain:
* `quadraticAffineObjective` in `Example_5_1_2`, the chapter source-facing owner for affine-
  quadratic objectives;
* `logAffineQuadraticBarrier_isStandardSelfConcordantOn` in `Example_5_1_4`, the canonical
  standard-self-concordance theorem for this exact logarithmic barrier;
* `IsSelfConcordantOnWith.sublevelLogBarrier_gradient_inner_sq_le` in `Theorem_5_1_4`, the
  canonical owner-level squared barrier inequality for logarithmic sublevel barriers;
* `barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the canonical bridge
  from that squared inequality to the barrier-parameter owner;
* `selfAdjointPart`, together with the bridge lemmas from `Example_5_3_1_2`, the canonical
  projection showing that this barrier depends only on the symmetric quadratic form.

Source/core/bridge triage:
* source-facing: the logarithmic barrier of the concave affine-quadratic potential
  `φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`;
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* bridge/view: the canonical strict sublevel barrier
  `sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0`.

Primitive data:
* `α`, `a`, and `A`;
* nonnegativity of the quadratic form `u ↦ ⟪u, A u⟫`.

Derived API:
* the self-adjoint part `selfAdjointPart ℝ A`, which preserves the quadratic term and carries the
  positivity owner needed upstream;
* standard self-concordance of the logarithmic barrier, reused from `Example_5_1_4`;
* the barrier inequality with parameter `1`, derived from the canonical owner-level sublevel-
  barrier estimate and `Proposition_5.3.3`.

This refinement keeps the theorem source-facing, but deletes the duplicate-wheel direct
differentiation route in favor of the upstream Chapter 5 owners already attached to the same
barrier. -/

-- Proof sketch: rewrite the source-facing barrier as the canonical strict sublevel barrier
-- `sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0`. Theorem `5.1.4` gives the
-- squared gradient-versus-local-norm estimate for this sublevel barrier, Proposition `5.3.3`
-- converts that estimate into the barrier-parameter inequality with `ν = 1`, and
-- `Example_5_1_4` already supplies the standard-self-concordance part of the barrier owner.
/-- Example 5.3.1.4: if the quadratic form `u ↦ ⟪u, A u⟫` is nonnegative, then the logarithmic
barrier associated to the concave affine-quadratic potential
`φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`
is a `1`-self-concordant barrier on its positivity domain `{x | φ(x) > 0}`. -/
theorem negLog_concaveQuadratic_isSelfConcordantBarrierOnWith
    (α : ℝ) (a : E) (A : E →L[ℝ] E)
    (hA_posSemidef : ∀ u : E, 0 ≤ inner ℝ u (A u)) :
    IsSelfConcordantBarrierOnWith
      {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x}
      1
      (fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x)) := by
  let S : E →L[ℝ] E := selfAdjointPart ℝ A
  let f : E → ℝ := quadraticAffineObjective (-α) (-a) S
  have hS_selfAdjoint : IsSelfAdjoint S := by
    simpa [S] using (selfAdjointPart ℝ A).2
  have hS_pos : S.IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff']
    refine ⟨hS_selfAdjoint, ?_⟩
    intro u
    calc
      0 ≤ inner ℝ u (A u) := hA_posSemidef u
      _ = inner ℝ (S u) u := by
            rw [real_inner_comm]
            simpa [S] using (selfAdjointPart_apply_inner_eq A u).symm
  have hstd :
      IsStandardSelfConcordantOn
        {x : E | f x < 0}
        (sublevelLogBarrier f 0) := by
    convert logAffineQuadraticBarrier_isStandardSelfConcordantOn α a S hS_pos using 1
    · simpa [f] using quadraticAffineObjective_neg_strictSublevel_eq α a S
    · simpa [f] using sublevelLogBarrier_quadraticAffineObjective_neg_eq α a S
  have hf_self : IsSelfConcordantOnWith (Set.univ : Set E) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-a) S hS_pos
  have hbarrier :
      IsSelfConcordantBarrierOnWith
        {x : E | f x < 0}
        1
        (sublevelLogBarrier f 0) := by
    refine
      { toIsStandardSelfConcordantOn := hstd
        barrier_parameter_bound := ?_ }
    intro x hx u
    have hbarrier_one :
        ∀ v : E,
          2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
              inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ) := by
      have hiff :
          (∀ v : E,
            2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ)) ↔
              ∀ v : E,
                (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                  (1 : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) := by
        simpa using
          (show
            (∀ v : E,
              2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                  inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤
                    ((1 : NNReal) : ℝ)) ↔
              ∀ v : E,
                (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                  ((1 : NNReal) : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) from
            barrier_parameter_bound_iff_gradient_inner_sq_le
              (hstd.hessian_isPositive hx))
      refine hiff.2 ?_
      intro v
      simpa using
        (hf_self.sublevelLogBarrier_gradient_inner_sq_le 0 (by simp) hx :
          (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
            ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ))
    exact hbarrier_one u
  have hdom :
      {x : E | f x < 0} =
        {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x} := by
    calc
      {x : E | f x < 0}
          = {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (S x) x} := by
              simpa [f] using quadraticAffineObjective_neg_strictSublevel_eq α a S
      _ = {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x} := by
            ext x
            have hquad : inner ℝ (S x) x = inner ℝ (A x) x := by
              simpa [S] using selfAdjointPart_apply_inner_eq A x
            simp [hquad]
  have hfun :
      sublevelLogBarrier f 0 =
        fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x) := by
    calc
      sublevelLogBarrier f 0
          = fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (S x) x) := by
              simpa [f] using sublevelLogBarrier_quadraticAffineObjective_neg_eq α a S
      _ = fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x) := by
            funext x
            have hquad : inner ℝ (S x) x = inner ℝ (A x) x := by
              simpa [S] using selfAdjointPart_apply_inner_eq A x
            simp [hquad]
  simpa [hdom, hfun] using hbarrier

end

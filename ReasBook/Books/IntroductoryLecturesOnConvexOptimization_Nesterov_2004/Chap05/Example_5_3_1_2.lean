/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 5.3.1.2 lies in the Chapter 5 self-concordant-barrier / quadratic-objective domain.

Sampled owner-style declarations in this domain:
* `quadraticAffineObjective` together with `quadraticAffineObjective_hessian_eq` in
  `Example_5_1_2`, the source-facing owner and its canonical Hessian API for affine-quadratic
  objectives;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for `ν`-self-
  concordant barriers;
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the chapter owner for positive-definite
  Hessians on a domain;
* `selfAdjointPart` in mathlib, the canonical projection from an operator to its self-adjoint
  part.

Best owner abstraction:
* source-facing: the affine-quadratic objective `quadraticAffineObjective α a A`;
* core/canonical: `IsSelfConcordantBarrierOnWith` and `HasPositiveDefiniteHessianOn`;
* bridge/view: passage from `A` to the canonical mathlib owner `selfAdjointPart ℝ A`, which
  preserves both the quadratic-affine objective and the quadratic form `u ↦ ⟪u, A u⟫`.

Primitive data:
* the scalar offset `α`;
* the linear coefficient `a`;
* the bounded operator `A`;
* strict positivity of the quadratic form `u ↦ ⟪u, A u⟫` on nonzero directions.

Derived API:
* the self-adjoint part `selfAdjointPart ℝ A`, which is the actual Hessian owner of the quadratic
  objective;
* positive definiteness of the Hessian of `quadraticAffineObjective α a A` on `Set.univ`;
* the barrier contradiction obtained from the owner inequality on `Set.univ`.

This refinement keeps the example source-facing, but removes the redundant self-adjointness binder
from the main theorems and reuses the existing Chapter 5 Hessian-positivity owner after passing to
the canonical self-adjoint part of the quadratic operator. -/

variable [CompleteSpace E]

/-- Passing to `selfAdjointPart ℝ A` does not change the quadratic term `⟪A x, x⟫`. -/
theorem selfAdjointPart_apply_inner_eq (A : E →L[ℝ] E) (x : E) :
    inner ℝ ((selfAdjointPart ℝ A : E →L[ℝ] E) x) x = inner ℝ (A x) x := by
  rw [show (selfAdjointPart ℝ A : E →L[ℝ] E) = (⅟2 : ℝ) • (A + A.adjoint) by
    rw [selfAdjointPart_apply_coe, ContinuousLinearMap.star_eq_adjoint]]
  calc
    inner ℝ (((⅟2 : ℝ) • (A + A.adjoint)) x) x
        = (⅟2 : ℝ) * inner ℝ (A x) x + (⅟2 : ℝ) * inner ℝ (A.adjoint x) x := by
            simp [inner_add_left, inner_smul_left]
    _ = (⅟2 : ℝ) * inner ℝ (A x) x + (⅟2 : ℝ) * inner ℝ (A x) x := by
          rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
    _ = inner ℝ (A x) x := by
          have htwo : (⅟2 : ℝ) * 2 = 1 := by norm_num
          calc
            (⅟2 : ℝ) * inner ℝ (A x) x + (⅟2 : ℝ) * inner ℝ (A x) x
                = ((⅟2 : ℝ) * 2) * inner ℝ (A x) x := by ring
            _ = inner ℝ (A x) x := by rw [htwo, one_mul]

/-- Passing to `selfAdjointPart ℝ A` does not change the quadratic form `u ↦ ⟪u, A u⟫`. -/
theorem inner_selfAdjointPart_apply_eq (A : E →L[ℝ] E) (u : E) :
    inner ℝ u ((selfAdjointPart ℝ A : E →L[ℝ] E) u) = inner ℝ u (A u) := by
  rw [show (selfAdjointPart ℝ A : E →L[ℝ] E) = (⅟2 : ℝ) • (A + A.adjoint) by
    rw [selfAdjointPart_apply_coe, ContinuousLinearMap.star_eq_adjoint]]
  calc
    inner ℝ u (((⅟2 : ℝ) • (A + A.adjoint)) u)
        = (⅟2 : ℝ) * inner ℝ u (A u) + (⅟2 : ℝ) * inner ℝ u (A.adjoint u) := by
            simp [inner_add_right, inner_smul_right]
    _ = (⅟2 : ℝ) * inner ℝ u (A u) + (⅟2 : ℝ) * inner ℝ u (A u) := by
          rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    _ = inner ℝ u (A u) := by
          have htwo : (⅟2 : ℝ) * 2 = 1 := by norm_num
          calc
            (⅟2 : ℝ) * inner ℝ u (A u) + (⅟2 : ℝ) * inner ℝ u (A u)
                = ((⅟2 : ℝ) * 2) * inner ℝ u (A u) := by ring
            _ = inner ℝ u (A u) := by rw [htwo, one_mul]

/-- Passing to `selfAdjointPart ℝ A` does not change the affine-quadratic objective. -/
theorem quadraticAffineObjective_selfAdjointPart_eq (α : ℝ) (a : E) (A : E →L[ℝ] E) :
    quadraticAffineObjective α a A = quadraticAffineObjective α a (selfAdjointPart ℝ A) := by
  ext x
  rw [quadraticAffineObjective, quadraticAffineObjective, selfAdjointPart_apply_inner_eq]

-- Proof sketch: replace `A` by its self-adjoint part `S := selfAdjointPart ℝ A`. The quadratic
-- objective and the quadratic form `u ↦ inner ℝ u (A u)` are unchanged by this replacement,
-- while `S` is self-adjoint. The constant-Hessian formula for `quadraticAffineObjective α a S`
-- then identifies the Hessian with `S`, so the strict positivity hypothesis transfers pointwise
-- to all Hessian quadratic forms on `Set.univ`.
/-- If the quadratic form `u ↦ ⟪u, A u⟫` is strictly positive on nonzero directions, then the
quadratic-affine objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` has positive-definite Hessian on
all of `E`. -/
theorem quadraticAffineObjective_hasPositiveDefiniteHessianOn
    (α : ℝ) (a : E) (A : E →L[ℝ] E)
    (hApos : ∀ u : E, u ≠ 0 → 0 < inner ℝ u (A u)) :
    HasPositiveDefiniteHessianOn (Set.univ : Set E) (quadraticAffineObjective α a A) := by
  let S : E →L[ℝ] E := selfAdjointPart ℝ A
  have hS : IsSelfAdjoint S := by
    simpa [S] using (selfAdjointPart ℝ A).2
  have hobj : quadraticAffineObjective α a A = quadraticAffineObjective α a S := by
    simpa [S] using quadraticAffineObjective_selfAdjointPart_eq α a A
  have hHess (x : E) : hessian (quadraticAffineObjective α a A) x = S := by
    rw [hobj]
    exact quadraticAffineObjective_hessian_eq α a S hS x
  refine ⟨?_, ?_⟩
  · intro x _
    have hSpos : S.IsPositive := by
      rw [ContinuousLinearMap.isPositive_iff']
      refine ⟨hS, ?_⟩
      intro u
      by_cases hu : u = 0
      · simp [hu]
      · rw [selfAdjointPart_apply_inner_eq]
        exact le_of_lt (by simpa [real_inner_comm] using hApos u hu)
    exact hHess x ▸ hSpos
  · intro x _ u hu
    rw [hHess x, inner_selfAdjointPart_apply_eq]
    exact hApos u hu

-- Proof sketch: if the quadratic objective were a `ν`-self-concordant barrier on all of `E`,
-- then the barrier-parameter inequality would hold for every base point and every direction.
-- Passing first to the self-adjoint part `S := selfAdjointPart ℝ A` does not change the quadratic
-- objective, while the gradient/Hessian API identifies `∇f x = a + S x` and `∇²f x = S`. Along
-- the ray `x = t • u` with `u ≠ 0`, the barrier expression becomes
-- `2 * ⟪a, u⟫ + (2 * t - 1) * ⟪u, A u⟫`, which is affine in `t` with positive slope because
-- `⟪u, A u⟫ > 0`. Choosing `t` so that this value equals `ν + 1` contradicts the uniform upper
-- bound by `ν`.
/-- Example 5.3.1.2: if the quadratic form `u ↦ ⟪u, A u⟫` is strictly positive on nonzero
directions, then the quadratic function `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` on all of `E` is not
a `ν`-self-concordant barrier. -/
theorem quadraticAffineObjective_not_isSelfConcordantBarrierOnWith
    [Nontrivial E]
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (ν : NNReal)
    (hApos : ∀ u : E, u ≠ 0 → 0 < inner ℝ u (A u)) :
    ¬ IsSelfConcordantBarrierOnWith (Set.univ : Set E) ν
      (quadraticAffineObjective α a A) := by
  intro hbar
  let S : E →L[ℝ] E := selfAdjointPart ℝ A
  have hS : IsSelfAdjoint S := by
    simpa [S] using (selfAdjointPart ℝ A).2
  -- Replace `A` by its self-adjoint part so the existing differential API applies directly.
  have hgrad (x : E) : ∇ (quadraticAffineObjective α a A) x = a + S x := by
    rw [quadraticAffineObjective_selfAdjointPart_eq α a A]
    simpa [S] using congrFun (quadraticAffineObjective_gradient_eq α a S hS) x
  have hhess (x : E) : hessian (quadraticAffineObjective α a A) x = S := by
    rw [quadraticAffineObjective_selfAdjointPart_eq α a A]
    simpa [S] using quadraticAffineObjective_hessian_eq α a S hS x
  -- Choose any nonzero ray direction; the positivity assumption makes its quadratic coefficient
  -- strictly positive.
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  let b : ℝ := inner ℝ a u
  let c : ℝ := inner ℝ u (A u)
  have hc : 0 < c := by
    simpa [c] using hApos u hu
  let t : ℝ := (((ν : ℝ) + 1) - 2 * b) / (2 * c) + (1 / 2 : ℝ)
  have hbound :=
    hbar.barrier_parameter_bound (show t • u ∈ (Set.univ : Set E) by simp) u
  -- Normalize the barrier expression along the ray `x = t • u` to an affine function of `t`.
  have hSu : inner ℝ u (S u) = c := by
    simpa [S, c] using inner_selfAdjointPart_apply_eq A u
  have hSu' : inner ℝ (S u) u = c := by
    calc
      inner ℝ (S u) u = inner ℝ u (S u) := by rw [real_inner_comm]
      _ = c := hSu
  have hray :
      2 * inner ℝ (∇ (quadraticAffineObjective α a A) (t • u)) u -
          inner ℝ u (hessian (quadraticAffineObjective α a A) (t • u) u) =
        2 * b + (2 * t - 1) * c := by
    rw [hgrad, hhess]
    calc
      2 * inner ℝ (a + S (t • u)) u - inner ℝ u (S u)
          = 2 * (b + t * c) - c := by
              rw [inner_add_left]
              simp [b, hSu, hSu', inner_smul_left, mul_comm]
      _ = 2 * b + (2 * t - 1) * c := by ring
  have hbound' : 2 * b + (2 * t - 1) * c ≤ (ν : ℝ) := by
    simpa [hray] using hbound
  -- The explicit choice of `t` forces the affine expression to equal `ν + 1`.
  have ht : 2 * b + (2 * t - 1) * c = (ν : ℝ) + 1 := by
    dsimp [t]
    field_simp [ne_of_gt hc]
    ring
  linarith

end

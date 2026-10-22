/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

/- Example 5.3.1.1 lies in the Chapter 5 self-concordant-barrier / affine-objective domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrier_parameter_bound`, the primitive owner inequality used to
  contradict barrierhood on `Set.univ`;
* `quadraticAffineObjective` in `Example_5_1_2`, the chapter source-facing owner for affine-
  quadratic objectives;
* `quadraticAffineObjective_gradient_eq` and `quadraticAffineObjective_hessian_eq`, the canonical
  differential API for that owner.

Best owner abstraction:
* source-facing: the scalar affine function `x ↦ α + a x`;
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* bridge/view: the zero-Hessian specialization
  `quadraticAffineObjective α a (0 : ℝ →L[ℝ] ℝ)`.

Primitive data:
* the scalar offset `α`;
* the nonzero slope `a`;
* the barrier parameter `ν`.

Derived API:
* the affine-quadratic owner view of `x ↦ α + a x`;
* the constant gradient formula `∇f(x) = a`;
* the vanishing Hessian formula `∇²f(x) = 0`.

This refinement keeps the theorem source-facing, but removes the ad hoc differential computation
route in favor of the existing affine-quadratic owner and the primitive barrier-owner inequality. -/

-- Proof sketch: if `f x = α + a * x` were a `ν`-self-concordant barrier on `ℝ`, then the
-- barrier-parameter inequality from `IsSelfConcordantBarrierOnWith` would read `2 * a * u ≤ ν`
-- for every direction `u : ℝ` because the Hessian vanishes identically. Taking `u` with the same
-- sign as `a` and arbitrarily large magnitude contradicts this when `a ≠ 0`.
/-- Example 5.3.1.1: the affine function `x ↦ α + a x` on all of `ℝ` is not a
`ν`-self-concordant barrier whenever `a ≠ 0`. In particular, the nonconstant linear
specialization `x ↦ a x` cannot be a self-concordant barrier because its Hessian is zero. -/
theorem affineFunction_not_isSelfConcordantBarrierOnWith
    (α a : ℝ) (ν : NNReal) (ha : a ≠ 0) :
    ¬ IsSelfConcordantBarrierOnWith (Set.univ : Set ℝ) ν (fun x : ℝ ↦ α + a * x) := by
  intro h
  let A : ℝ →L[ℝ] ℝ := 0
  have hzero : quadraticAffineObjective α a A = fun x : ℝ ↦ α + inner ℝ a x := by
    exact quadraticAffineObjective_zero_operator α a
  have hobj : quadraticAffineObjective α a A = fun x : ℝ ↦ α + a * x := by
    calc
      quadraticAffineObjective α a A = fun x : ℝ ↦ α + inner ℝ a x := hzero
      _ = fun x : ℝ ↦ α + a * x := by
        funext x
        have hinner : inner ℝ a x = x * a := RCLike.inner_apply a x
        calc
          α + inner ℝ a x = α + x * a := by rw [hinner]
          _ = α + a * x := by ring
  have hbarrier :
      IsSelfConcordantBarrierOnWith (Set.univ : Set ℝ) ν (quadraticAffineObjective α a A) := by
    simpa [hobj] using h
  let u : ℝ := ((ν : ℝ) + 1) / a
  have hbound := hbarrier.barrier_parameter_bound
    (show (0 : ℝ) ∈ (Set.univ : Set ℝ) by simp) u
  have hA : IsSelfAdjoint A :=
    ContinuousLinearMap.isPositive_zero.isSelfAdjoint
  have hgrad : ∇ (quadraticAffineObjective α a A) 0 = a := by
    simpa [A] using congrFun (quadraticAffineObjective_gradient_eq α a A hA) 0
  have hhess : hessian (quadraticAffineObjective α a A) 0 = A := by
    simpa using quadraticAffineObjective_hessian_eq α a A hA 0
  have hu : a * u = (ν : ℝ) + 1 := by
    dsimp [u]
    field_simp [ha]
  have hcontr : 2 * ((ν : ℝ) + 1) ≤ (ν : ℝ) := by
    calc
      2 * ((ν : ℝ) + 1) =
          2 * inner ℝ (∇ (quadraticAffineObjective α a A) 0) u -
            inner ℝ u (hessian (quadraticAffineObjective α a A) 0 u) := by
        rw [hgrad, hhess]
        have hinner : inner ℝ a u = u * a := RCLike.inner_apply a u
        have hau : inner ℝ a u = (ν : ℝ) + 1 := by
          calc
            inner ℝ a u = u * a := hinner
            _ = a * u := by ring
            _ = (ν : ℝ) + 1 := hu
        simp [A, hau]
      _ ≤ (ν : ℝ) := hbound
  linarith

end

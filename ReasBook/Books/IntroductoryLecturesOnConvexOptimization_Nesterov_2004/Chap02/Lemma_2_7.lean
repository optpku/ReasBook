/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap

/-
Primary domain: estimating-sequence gap bounds for real-valued function families.

Sampled owner-style declarations:
* `AffineMap.lineMap`
* `AffineMap.lineMap_apply_module`
* `IsMinOn f Set.univ xStar`
* the downstream owner predicate `IsEstimatingSequence` in `Definition_2_21`

Best owner abstraction for this file:
* source-facing: the gap-control lemmas of Lemma 2.7
* core/canonical: the function-space affine upper model `lineMap f (phi 0) (lam k)` together with
  the minimizer owner `IsMinOn f Set.univ xStar`
* bridge/view: the pointwise textbook expansion of `lineMap` given by `lineMap_apply_module`

Primitive data:
* the domain `X`, objective `f`, auxiliary models `phi k`, coefficients `lam k`, minimum values
  `phiStar k`, and sampled points `x k`
* the canonical function-space affine upper bound `phi k ≤ lineMap f (phi 0) (lam k)`
* a minimizer `xStar` of `f` on `Set.univ`

Derived API:
* the interval estimate for the optimality gap
* convergence of that gap to `0` under `lam ⟶ 0`

This file keeps the source-facing gap lemmas but uses the canonical affine owner `lineMap`
instead of a parallel raw affine-combination shell.
-/

section

variable
    {X : Type*}
    {f : X → ℝ}
    {phi : ℕ → X → ℝ}
    {lam : ℕ → ℝ}

section Gap

variable
    (xStar : X)
    (phiStar : ℕ → ℝ)
    (x : ℕ → X)

/-- Lemma 2.7: if each iterate value is bounded above by the minimum of `phi k`, and the
estimating functions `phi k` are bounded above by the canonical affine model
`lineMap f (phi 0) (lam k)`, then the optimality gap at stage
`k` lies in the interval `[0, lambda_k * (phi0 x* - f x*)]`. The source chapter applies this to
functions on `ℝⁿ`, but the proof is purely pointwise and therefore lives on an arbitrary domain
`X`. -/
-- Proof sketch: use `IsMinOn f Set.univ xStar` to obtain `f xStar ≤ f (x k)`, giving the lower
-- endpoint of the interval. For the upper endpoint, combine the hypothesis `f (x k) ≤ phiStar k`
-- with the fact that `phiStar k` is the minimum value of `phi k`, use the estimating-sequence
-- upper bound `phi k ≤ lineMap f (phi 0) (lam k)`, and then evaluate that affine model at
-- `xStar`.
lemma estimatingSequence_gap_mem_Icc
    (hmin : IsMinOn f Set.univ xStar)
    (hphiUpper : ∀ k, phi k ≤ lineMap f (phi 0) (lam k))
    (hphiStar : ∀ k, IsLeast (Set.range (phi k)) (phiStar k))
    (hx : ∀ k, f (x k) ≤ phiStar k)
    (k : ℕ) :
    f (x k) - f xStar ∈ Set.Icc 0 (lam k * (phi 0 xStar - f xStar)) := by
  have hmin_le : ∀ y, f xStar ≤ f y := isMinOn_univ_iff.mp hmin
  -- The minimizer property of `xStar` gives the lower endpoint `0 ≤ f (x k) - f xStar`.
  have hLower : 0 ≤ f (x k) - f xStar := by
    exact sub_nonneg.mpr (hmin_le (x k))
  -- Evaluate the minimum value of `phi k` at `xStar`, then compare with the affine upper model.
  have hphi_at_minimizer : phiStar k ≤ phi k xStar := by
    exact (hphiStar k).2 ⟨xStar, rfl⟩
  have hphi_line : phiStar k ≤ lineMap f (phi 0) (lam k) xStar := by
    exact le_trans hphi_at_minimizer (hphiUpper k xStar)
  -- Rewrite the affine model at `xStar` into the textbook convex combination.
  have hx' : f (x k) ≤ lineMap f (phi 0) (lam k) xStar := by
    exact le_trans (hx k) hphi_line
  have hx'' : f (x k) ≤ (1 - lam k) * f xStar + lam k * phi 0 xStar := by
    simpa [lineMap_apply_module] using hx'
  have hUpper : f (x k) - f xStar ≤ lam k * (phi 0 xStar - f xStar) := by
    linarith
  exact ⟨hLower, hUpper⟩

/-- Under the assumptions of `estimatingSequence_gap_mem_Icc`, the optimality gap converges to
`0`. -/
-- Proof sketch: the previous interval estimate gives
-- `0 ≤ f (x k) - f xStar ≤ lam k * (phi 0 xStar - f xStar)` for every `k`. Since `lam k → 0`,
-- the
-- right-hand side tends to `0`, and the squeeze theorem yields convergence of the gap to `0`.
lemma estimatingSequence_gap_tendsto_zero
    (hmin : IsMinOn f Set.univ xStar)
    (hLam : Filter.Tendsto lam Filter.atTop (nhds 0))
    (hphiUpper : ∀ k, phi k ≤ lineMap f (phi 0) (lam k))
    (hphiStar : ∀ k, IsLeast (Set.range (phi k)) (phiStar k))
    (hx : ∀ k, f (x k) ≤ phiStar k) :
    Filter.Tendsto (fun k ↦ f (x k) - f xStar) Filter.atTop (nhds 0) := by
  -- Reuse the interval estimate to get a pointwise squeeze between `0` and the scaled model gap.
  have hgap :
      ∀ k, f (x k) - f xStar ∈ Set.Icc 0 (lam k * (phi 0 xStar - f xStar)) := fun k ↦
        estimatingSequence_gap_mem_Icc xStar phiStar x hmin hphiUpper hphiStar hx k
  -- The upper endpoint tends to `0` because it is a constant multiple of `lam k`.
  have hUpperT :
      Filter.Tendsto
        (fun k ↦ lam k * (phi 0 xStar - f xStar))
        Filter.atTop
        (nhds 0) := by
    simpa using hLam.mul_const (phi 0 xStar - f xStar)
  -- Apply the squeeze theorem with lower bound `0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpperT ?_ ?_
  · intro k
    exact (hgap k).1
  · intro k
    exact (hgap k).2

end Gap

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/-
Lemma 7.23 lies in the scalar recurrence / partial-sum accumulation domain.

Sampled owner-style declarations:
* current mathlib's ordered-field scalar bundle `[Field α] [LinearOrder α]
  [IsStrictOrderedRing α]`, which replaces the old bundled `LinearOrderedField` owner in this
  environment and is the canonical scalar layer for the recurrence and `nlinarith` step;
* mathlib `Finset.sum_range_zero`, the canonical base-case owner for sums over `Finset.range 0`;
* mathlib `Finset.sum_range_succ`, the canonical step decomposition of a partial sum on
  `Finset.range`;
* project `estimating_function_le_weighted_transformed_objective_add_initial` in `Lemma_7_21`,
  the nearby Chapter 7 recurrence-accumulation pattern;
* project `accumulatedWeights` in `Chap06/Definition_6_53`, the chapter owner for inclusive
  accumulated sums.

Best owner abstraction:
* source-facing: the lower recursion for the optimal values `ψ_k^*`;
* core/canonical: the current mathlib ordered-field scalar bundle together with the `Finset.range`
  partial-sum API;
* bridge/view: `accumulatedWeights (fun i ↦ a i * hatF i)` is the natural chapter bridge for
  inclusive sums, but it is not the main owner here because the textbook statement is intrinsically
  the source-facing predecessor partial sum `∑_{i=0}^{k-1} a_i \hat f(x_i)`.

Primitive data:
* the scalar sequences `ψStar`, `a`, `hatF`, and `dualGradNormSq`;
* the initial lower bound `0 ≤ ψStar 0`;
* the one-step recursion and progress identity.

Derived API:
* the accumulated lower bound for `ψ_k^*`.

No upstream project theorem has this exact stage-dependent lower-recursion interface, so the file
keeps the source-facing statement and uses the canonical `Finset.range` owner directly rather than
introducing a parallel wrapper.
-/

-- Proof sketch: argue by induction on `k`. The base case is `hzero`, since the sum over
-- `Finset.range 0` is zero. For the induction step, apply `hupdate` at stage `k`, substitute the
-- progress identity `hprogress k` to rewrite the quadratic loss term as `δ a_k \hat f(x_k)`, and
-- then combine the inductive lower bound with the decomposition of the sum over
-- `Finset.range (k + 1)`.
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Lemma 7.23: if the optimal values `ψStar k = ψ_k^*` of the quasi-Newton estimating functions
satisfy the one-step lower recursion induced by the update `(7.4.12)` and the progress identity
`(7.4.15)`, then
`ψ_k^* ≥ (1 - δ) * ∑_{i=0}^{k-1} a_i \hat f(x_i)`. Here `hatF k` abbreviates `\hat f(x_k)` and
`dualGradNormSq k` abbreviates `(\| \hat g(x_k) \|_{G_{k+1}}^*)^2`. -/
theorem quasiNewtonEstimatingOptimalValue_lower_bound
    (ψStar a hatF dualGradNormSq : ℕ → α) (δ : α)
    (hzero : 0 ≤ ψStar 0)
    (hupdate :
      ∀ k : ℕ,
        ψStar (k + 1) ≥
          ψStar k + a k * hatF k - (1 / 2 : α) * (a k) ^ (2 : ℕ) * dualGradNormSq k)
    (hprogress :
      ∀ k : ℕ,
        (1 / 2 : α) * (a k) ^ (2 : ℕ) * dualGradNormSq k = δ * a k * hatF k)
    (k : ℕ) :
    ψStar k ≥ (1 - δ) * (∑ i ∈ Finset.range k, a i * hatF i) := by
  induction k with
  | zero =>
      simpa using hzero
  | succ k ih =>
      have hstep :
          ψStar (k + 1) ≥ ψStar k + (1 - δ) * (a k * hatF k) := by
        have hupdate' := hupdate k
        rw [hprogress k] at hupdate'
        nlinarith
      have hsum :
          ψStar (k + 1) ≥
            (1 - δ) * (∑ i ∈ Finset.range k, a i * hatF i) + (1 - δ) * (a k * hatF k) := by
        nlinarith
      simpa [Finset.sum_range_succ, mul_add, add_comm, add_left_comm, add_assoc] using hsum

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped StandardSimplex

noncomputable section

/- Proposition 6.16 lies in the finite simplex / entropy-smoothing domain.

Sampled owner declarations:
* `normalizedEntropyProxFunction` and `normalizedEntropyProxFunction_apply` in
  `Chap06/Definition_6_14`;
* `entropyRegularizedSimplexObjective` and `entropyRegularizedSimplexObjective_apply` in
  `Chap06/Lemma_6_4`;
* `smoothedPrimalObjective` in `Chap06/Definition_6_30`.

Best owner abstraction:
* source-facing: the entropy-smoothed simplex supremum attached to the affine scores
  `j ↦ ⟪a_j, x⟫ + b_j`;
* core/canonical: `normalizedEntropyProxFunction`, with the later chapter owners
  `entropyRegularizedSimplexObjective` and `smoothedPrimalObjective` for the same smoothing
  pattern;
* bridge/view: Proposition 6.16's explicit expansion of the normalized entropy prox term.

Primitive data:
* a real inner-product space `E`;
* the finite affine family `a`, `b`, the linear term `c`, the simplex size `m`, and the
  smoothing parameter `μ`.

Derived API:
* the explicit source-facing entropy expansion of the smoothed simplex supremum.

The previous version introduced a local wrapper `entropySmoothedAffineObjective` whose only role
was to restate the displayed supremum formula. This file now states the proposition directly in the
canonical simplex/entropy language and removes the duplicate owner-shaped definition.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: compare the two `Set.range` supremum sets pointwise, then expand
-- `normalizedEntropyProxFunction m u = Real.log (m : ℝ) + ∑ j, u j * Real.log (u j)` inside the
-- supremum.
/-- Proposition 6.16: the entropy-smoothed approximation of
`x ↦ ⟪c, x⟫ + max_j (⟪a_j, x⟫ + b_j)` is obtained by replacing the entropy prox-function on
`Δ_m` with its explicit formula `log m + ∑_j u_j log u_j`. -/
theorem entropySmoothedAffineSup_eq_entropyExpansion
    (m : ℕ+) (c x : E) (a : Fin (m : ℕ) → E) (b : Fin (m : ℕ) → ℝ) (μ : ℝ) :
    inner ℝ c x +
      sSup
        (Set.range fun u : Δ[m] ↦
          (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
            μ * normalizedEntropyProxFunction m u) =
      inner ℝ c x +
        sSup
          (Set.range fun u : Δ[m] ↦
            (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
              μ * ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
                μ * Real.log (m : ℝ)) := by
  refine congrArg (fun s : Set ℝ ↦ inner ℝ c x + sSup s) ?_
  ext y
  constructor <;> intro hy <;> rcases hy with ⟨u, rfl⟩ <;> refine ⟨u, ?_⟩
  · change
      (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
          μ * ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
            μ * Real.log (m : ℝ) =
        (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
          μ * normalizedEntropyProxFunction m u
    rw [normalizedEntropyProxFunction_apply]
    ring
  · change
      (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
          μ * normalizedEntropyProxFunction m u =
        (∑ j : Fin (m : ℕ), u j * (inner ℝ (a j) x + b j)) -
          μ * ∑ j : Fin (m : ℕ), u j * Real.log (u j) -
            μ * Real.log (m : ℝ)
    rw [normalizedEntropyProxFunction_apply]
    ring

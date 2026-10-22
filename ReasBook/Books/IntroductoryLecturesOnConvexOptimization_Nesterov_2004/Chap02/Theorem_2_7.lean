/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E : Type u} {β : Type v}
variable [Preorder β]

/- Primary domain: stage-restricted lower-complexity comparisons. The source theorem is used for
first-order arguments on `ℝⁿ`, but its statement only depends on the underlying stage sets and the
order structure of the objective values.

Relevant owner-style declarations sampled before refining:
* `Set.EqOn` in mathlib `Data.Set.Function`, the canonical owner notion of agreement on a set;
* `lowerBounds` in mathlib `Order.Bounds.Defs`, the canonical owner notion of a lower bound for an
  image set;
* `IsLeast` in mathlib `Order.Bounds.Basic`, the attained-minimum companion notion whose second
  field recovers the lower-bound data actually used here;
* `SatisfiesSpanCondition` in `Definition_2_9`, showing that linear-algebraic stage constraints
  belong upstream in the owner hypothesis that produces the stage sets, rather than in this
  comparison lemma itself;
* `coordinateSubspace` in `Text_2_13` / `Definition_2_12`, the chapter's canonical example of a
  concrete stage family whose underlying sets can later be passed to this theorem.

Best owner abstraction:
* source-facing: a family of stage sets `𝓛 : ℕ → Set E` and a family of ordered-valued
  objectives `f`;
* core/canonical: agreement on a stage set via `(𝓛 k).EqOn ...` and lower bounds via
  `fStar k ∈ lowerBounds (f k '' 𝓛 k)`;
* bridge/view: the chapter specialization from concrete coordinate subspaces or spans to their
  underlying sets.

Source/core/bridge triage:
* source-facing: Theorem 2.7's comparison of `f_p (x_k)` with the stage minimum value `f_k^*`
  over a prescribed feasible stage;
* core/canonical: the owner pair `EqOn` plus `lowerBounds` on the stage image set;
* bridge/view: specializing the generic set theorem to the chapter's concrete Euclidean stage
  subspaces.

Primitive data:
* the stage sets `𝓛`,
* the objective family `f`,
* the iterate family `x`,
* the lower-bound values `fStar`.

Derived API:
* if `x k ∈ 𝓛 k`, `f p` agrees with `f k` on `𝓛 k`, and `fStar k` is a lower bound for `f k`
  on `𝓛 k`, then `f p (x k) ≥ fStar k`;
* the attained-minimum source statement is then a thin companion obtained by projecting the
  lower-bound field from `IsLeast`.
-/

section

variable (p : ℕ) (𝓛 : ℕ → Set E) (f : ℕ → E → β) (x : ℕ → E) (fStar : ℕ → β)
variable (hx_mem : ∀ ⦃k : ℕ⦄, k ≤ p → x k ∈ 𝓛 k)
variable (hagree : ∀ ⦃k : ℕ⦄, k ≤ p → (𝓛 k).EqOn (f p) (f k))

/-- Owner form of Theorem 2.7: if the `k`-th iterate lies in the stage set `𝓛_k`, the terminal
objective `f_p` agrees on `𝓛_k` with the stage objective `f_k`, and `f_k^*` is a lower bound for
the stage values `f_k` on `𝓛_k`, then `f_p (x_k) ≥ f_k^*`. -/
-- Proof sketch: since `x_k ∈ 𝓛_k`, the lower-bound hypothesis for `f_k` on `𝓛_k` gives
-- `f_k^* ≤ f_k (x_k)`; the `EqOn` hypothesis then rewrites this value to `f_p (x_k)`.
theorem agreeing_family_value_ge_stage_lower_bound
    (hx_mem : ∀ ⦃k : ℕ⦄, k ≤ p → x k ∈ 𝓛 k)
    (hagree : ∀ ⦃k : ℕ⦄, k ≤ p → (𝓛 k).EqOn (f p) (f k))
    (hlower : ∀ ⦃k : ℕ⦄, k ≤ p → fStar k ∈ lowerBounds (f k '' 𝓛 k))
    {k : ℕ} (hk : k ≤ p) :
    f p (x k) ≥ fStar k := by
  have hstage : fStar k ≤ f k (x k) :=
    hlower hk <| Set.mem_image_of_mem _ (hx_mem hk)
  have hagree_value : f p (x k) = f k (x k) :=
    hagree hk (hx_mem hk)
  simpa [hagree_value] using hstage

/-- Theorem 2.7: if the `k`-th iterate lies in the stage set `𝓛_k`, the terminal objective `f_p`
agrees on `𝓛_k` with the stage objective `f_k`, and `f_k^*` is the minimum value of `f_k` on
`𝓛_k`, then `f_p (x_k) ≥ f_k^*`. -/
theorem agreeing_family_value_ge_level_minimum
    (hx_mem : ∀ ⦃k : ℕ⦄, k ≤ p → x k ∈ 𝓛 k)
    (hagree : ∀ ⦃k : ℕ⦄, k ≤ p → (𝓛 k).EqOn (f p) (f k))
    (hmin : ∀ ⦃k : ℕ⦄, k ≤ p → IsLeast (f k '' 𝓛 k) (fStar k))
    {k : ℕ} (hk : k ≤ p) :
    f p (x k) ≥ fStar k :=
  agreeing_family_value_ge_stage_lower_bound p 𝓛 f x fStar hx_mem hagree
    (fun {_k} hk ↦ (hmin hk).2) hk

end

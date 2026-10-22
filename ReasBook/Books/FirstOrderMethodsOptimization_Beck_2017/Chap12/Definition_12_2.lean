/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set

noncomputable section

section

variable {E : Type u} {Y : Type v}

/- Definition 12.2 is `bridge/view`: it rewrites the Chapter 12 primal objective into a split
optimization problem on pairs `(x, z)` constrained by `z = A x`.

Domain sampling identifies the owner abstractions already present upstream:
- `source-facing`: the split reformulation of the primal infimum;
- `core/canonical`: Chapter 10's `composite_model_objective` for pointwise sums, Chapter 12's
  `dual_based_proximal_gradient_primal_optimal_value` for the primal infimum, and mathlib's
  `Set.graphOn` for the graph constraint;
- `bridge/view`: restricting the canonical product objective
  `composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)` to `univ.graphOn A`, which recovers
  the canonical primal objective `composite_model_objective f (g ∘ A)`.

Primitive data are only the summands `f`, `g`, and the map `A`; the product-space objective and
feasible set should therefore be thin specializations of those owners rather than bespoke wrapper
definitions. -/
recall composite_model_objective
recall composite_model_objective_apply
recall dual_based_proximal_gradient_primal_optimal_value_eq_sInf

-- Proof sketch: identify the feasible set with the graph of `A`; every feasible pair has the form
-- `(x, A x)`, and on that graph the canonical product objective
-- `composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)` coincides with the Chapter 12 primal
-- objective `composite_model_objective f (g ∘ A)`, so the split infimum is exactly the canonical
-- primal optimal value.
/-- Definition 12.2: the primal problem `min_x (f x + g (A x))` can equivalently be rewritten as
minimizing the split objective `(x, z) ↦ f x + g z` over the graph-feasible pairs satisfying
`A x = z`. -/
theorem dual_based_proximal_gradient_primal_optimal_value_eq_split_infimum
    (f : E → EReal) (g : Y → EReal) (A : E → Y) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      sInf (Set.image (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd))
        (univ.graphOn A)) := by
  rw [dual_based_proximal_gradient_primal_optimal_value_eq_sInf]
  have himage :
      Set.image (composite_model_objective (f ∘ Prod.fst) (g ∘ Prod.snd)) (univ.graphOn A) =
        Set.range (composite_model_objective f (g ∘ A)) := by
    ext r
    constructor
    · rintro ⟨⟨x, z⟩, hxz, rfl⟩
      have hz : A x = z := by
        simpa using hxz
      subst z
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(x, A x), by simp, rfl⟩
  exact congrArg sInf himage.symm

end

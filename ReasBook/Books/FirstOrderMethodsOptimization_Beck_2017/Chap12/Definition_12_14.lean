/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_16
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

section

variable {E : Type u}

/- Definition 12.14 is a `bridge/view` recall: the block primal objective
`x ↦ f x + ∑ i : Fin p, g i x` is already owned by the Chapter 10 composite objective applied to
the Chapter 8 finite-sum aggregate.

Domain sampling in the surrounding project identifies:
- `core/canonical`: `composite_model_objective` for the outer two-term split;
- `core/canonical`: `finite_sum_objective` for the block family `g`;
- `bridge/view`: the specialization to a family indexed by `Fin p`.

Primitive data are only `f` and the finite family `g`. Since the source introduces no new owner
beyond that specialization, this file should recall the existing owners and their pointwise
evaluation formulas directly, rather than keep a parallel Chapter 12 alias. -/

/- Definition 12.14: the dual block proximal-gradient primal objective is exactly the Chapter 10
composite objective specialized to the Chapter 8 finite-sum term. -/
recall composite_model_objective
recall finite_sum_objective

/- In source-facing form, Definition 12.14 is the specialization
`fun f g ↦ composite_model_objective f (finite_sum_objective g)`. -/
#check fun {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) ↦
  composite_model_objective f (finite_sum_objective g)

/- Pointwise, the same owner is the block objective `x ↦ f x + ∑ i : Fin p, g i x`. -/
#check fun {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) (x : E) ↦
  f x + ∑ i : Fin p, g i x

end

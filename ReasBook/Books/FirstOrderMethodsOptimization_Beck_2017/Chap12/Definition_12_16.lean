/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

section

variable {E : Type u}

/- Definition 12.16 is `bridge/view`: Definition 12.14 already fixes the finite-sum primal owner
as `composite_model_objective f (finite_sum_objective g)`. The present item should therefore not
rebuild the same objective from a raw lambda; it identifies that existing owner with the Chapter
12.1 block composite-model presentation obtained by taking the block space to be `E^p`,
represented in Lean by `Fin p → E`, the nonsmooth term to be the separable block sum, and the
linear map to be the diagonal duplication map.

Domain sampling identifies the existing owners:
- `core/canonical`: `composite_model_objective` for the outer two-term split;
- `core/canonical`: `finite_sum_objective` for the scalar finite-sum term from Definition 12.14;
- `bridge/view`: `separableSum g ∘ Function.const (Fin p)` for the same term in block form.

The primitive data are therefore only `f` and the finite family `g`; the block-separable term and
duplication map are derived from those owners rather than new Chapter 12 declarations. -/

/- Definition 12.16: the finite-sum problem `min_x {f x + ∑ i, g i x}` fits the Chapter 12.1
composite model by taking `V = E^p` (implemented as `Fin p → E`),
`g(x₁, ..., x_p) = ∑ i, g i (x_i)`, and `A z = (z, ..., z)`. -/
recall composite_model_objective
recall composite_model_objective_apply
recall finite_sum_objective
recall finite_sum_objective_apply
recall separableSum
recall separableSum_apply

/- In source-facing form, the Definition 12.16 specialization of the Chapter 12.1 owner is
`fun f g ↦ composite_model_objective f (separableSum g ∘ Function.const (Fin p))`. -/
#check fun {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) ↦
  composite_model_objective f (separableSum g ∘ Function.const (Fin p))

/-- The Definition 12.14 finite-sum term is the separable block sum evaluated on the diagonal
embedding `x ↦ (x, ..., x)`. -/
theorem finite_sum_objective_eq_separableSum_comp_const
    {p : ℕ} (g : Fin p → E → EReal) :
    finite_sum_objective g = separableSum g ∘ Function.const (Fin p) := by
  funext x
  simp [finite_sum_objective_apply, Function.comp_apply, separableSum_apply]

end

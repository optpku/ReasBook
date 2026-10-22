/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {ι : Type u} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable {Li : (i : ι) → PosReal}

/- Definition 11.13 is `source-facing`: it records the standing assumptions for the randomized
block proximal gradient method. The shared blockwise data already live in the Chapter 11
`core/canonical` owner `IsBlockProximalGradientProblem`, so this file should add only the extra
source-facing hypotheses not already owned there: convexity of `f` and differentiability of
`(fun x ↦ (f x).toReal)` on `interior (effective_domain f)`. -/

/-- Definition 11.13: Assumption 11.21 for the randomized block proximal gradient method fixes
block penalties `g_i : E_i → (-∞, ∞]`, a smooth term `f : (Π i, E_i) → (-∞, ∞]`,
chosen block partial gradients `block_gradient i x = ∇_i f(x)`, explicit positive block
Lipschitz constants `L_i`, and optimality data `XStar = X^*`, `FOpt = F_opt`, such that
(A) each `g_i` is proper, closed, and convex; (B) `f` is proper, closed, and convex, the
effective domain of `x ↦ ∑ i, g_i(x_i)` is contained in `interior (effective_domain f)`, and
`(fun x ↦ (f x).toReal)` is differentiable on that interior; (C) each chosen block partial
gradient is the gradient of the one-block slice
`d ↦ f(block_coordinate_update x i d)` at `d = 0` and is `L_i`-Lipschitz along the `i`-th block
direction; and (D) `XStar` is the nonempty optimal set of the composite objective with optimal
value `FOpt`. -/
class RandomizedBlockProximalGradientAssumptions
    (f : ((i : ι) → Ei i) → EReal) (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (XStar : Set ((i : ι) → Ei i)) (FOpt : ℝ)
    (Li : (i : ι) → PosReal) : Prop
    extends IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li where
  f_convex : is_convex_function f
  f_toReal_differentiableOn_interior_effective_domain :
    DifferentiableOn ℝ (fun x ↦ (f x).toReal) (interior (effective_domain f))

/-- The randomized block proximal-gradient assumptions inherit the shared Chapter 11
block proximal-gradient problem owner. -/
instance instIsBlockProximalGradientProblemOfRandomizedBlockProximalGradientAssumptions
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Li : (i : ι) → PosReal}
    (h : RandomizedBlockProximalGradientAssumptions f g block_gradient XStar FOpt Li) :
    IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
  h.toIsBlockProximalGradientProblem

namespace RandomizedBlockProximalGradientAssumptions

/-- The randomized block proximal-gradient assumptions are obtained from the Chapter 11 core owner
plus the two extra source-facing clauses specific to Definition 11.13: convexity of `f` and
differentiability of `x ↦ (f x).toReal` on `interior (effective_domain f)`. -/
theorem ofIsBlockProximalGradientProblem
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    (h :
      IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (hf_convex : is_convex_function f)
    (hfdiff :
      DifferentiableOn ℝ (fun x ↦ (f x).toReal) (interior (effective_domain f))) :
    RandomizedBlockProximalGradientAssumptions f g block_gradient XStar FOpt Li where
  toIsBlockProximalGradientProblem := h
  f_convex := hf_convex
  f_toReal_differentiableOn_interior_effective_domain := hfdiff

end RandomizedBlockProximalGradientAssumptions

namespace BlockProximalGradientAssumptions

/-- A block proximal-gradient assumption package together with convexity of the smooth term `f`
induces the randomized block proximal-gradient assumptions by forgetting the separate global
`L_f`-smoothness field and retaining the shared blockwise data. -/
theorem toRandomizedBlockProximalGradientAssumptions
    {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
    {Lf : NNReal}
    (h : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (hf_convex : is_convex_function f) :
    RandomizedBlockProximalGradientAssumptions f g block_gradient XStar FOpt Li :=
  RandomizedBlockProximalGradientAssumptions.ofIsBlockProximalGradientProblem
    h.toIsBlockProximalGradientProblem
    hf_convex
    h.f_toReal_differentiableOn_interior_effective_domain

end BlockProximalGradientAssumptions

end

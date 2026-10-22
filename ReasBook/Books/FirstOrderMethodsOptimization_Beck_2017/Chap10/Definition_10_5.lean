/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Definition 10.5 is `source-facing`: the textbook introduces the gradient mapping
`G_L^{f,g}(x) = L (x - T_L^{f,g}(x))` using the prox-grad operator from the preceding definition.
The canonical owner in this chapter is therefore a direct definition on
`interior (effective_domain f)`, reusing `prox_grad_operator` rather than repackaging the same
operator through a new problem structure. -/

instance instLowerSemicontinuousOfFact (g : E → EReal) [Fact (LowerSemicontinuous g)] :
    LowerSemicontinuous g :=
  ‹Fact (LowerSemicontinuous g)›.1

instance instIsConvexFunctionOfFact (g : E → EReal) [Fact (is_convex_function g)] :
    is_convex_function g :=
  ‹Fact (is_convex_function g)›.1

/-- Definition 10.5: for a positive parameter `L`, the gradient mapping `G_L^{f,g}` of the
composite pair `(f, g)` sends `x ∈ interior (effective_domain f)` to the scaled residual
`L • (x - T_L^{f,g}(x))`, where `T_L^{f,g}` is the prox-grad operator. -/
def gradient_mapping (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (L : PosReal) :
    interior (effective_domain f) → E :=
  fun x ↦
    (L : ℝ) • ((x : E) - T[L, f, g] x)

@[inherit_doc] scoped[Gradient] notation:max "G[" L ", " f ", " g "]" =>
  gradient_mapping f g L

/-- Evaluating the gradient mapping at `x` gives the textbook formula
`L • (x - T_L^{f,g}(x))`. -/
@[simp] theorem gradient_mapping_apply
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (L : PosReal)
    (x : interior (effective_domain f)) :
    G[L, f, g] x =
      (L : ℝ) • ((x : E) - T[L, f, g] x) := rfl

section CoeReal

variable (f : E → ℝ) (g : E → EReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/- The core owner remains `gradient_mapping` on `interior (effective_domain f)`. For a
real-valued smooth term, the source-facing Chapter 10 theorems use the canonical bridge
`interior_effective_domain_point_of_real` from Definition 10.9 to view that owner as a map on
`E`. -/

/-- The proximal-gradient mapping for a real-valued smooth term `f`, obtained by evaluating the
Chapter 10 owner `gradient_mapping` of `f.toEReal` at the canonical interior-domain point
associated to `x`. -/
abbrev prox_gradient_mapping
    (f : E → ℝ) (g : E → EReal)
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (L : PosReal) : E → E :=
  fun x ↦
    G[L, f.toEReal, g] (interior_effective_domain_point_of_real f x)

syntax:max "G[" term "; " term ", " term "]" : term

set_option quotPrecheck false in
macro_rules
  | `(G[$L; $f, $g]) => `(prox_gradient_mapping $f $g $L)

/-- Evaluating `prox_gradient_mapping` at `x` recovers the Chapter 10 gradient mapping of
`f.toEReal` at the canonical interior-domain point associated to `x`. -/
@[simp] theorem prox_gradient_mapping_apply (L : PosReal) (x : E) :
    G[L; f, g] x = G[L, f.toEReal, g] (interior_effective_domain_point_of_real f x) := rfl

end CoeReal

end

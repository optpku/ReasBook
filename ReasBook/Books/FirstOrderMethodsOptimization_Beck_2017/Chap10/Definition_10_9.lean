/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-
Definition 10.9 is `bridge/view` in the Chapter 10 proximal-gradient stack:

- `prox[...]` from Chapter 6 remains the `core/canonical` proximal owner;
- `proximal_gradient_step` from Algorithm 10.1 is the Chapter 10 `source-facing` set-valued
  prox-gradient step;
- `prox_grad_operator` below is the single-valued bridge obtained when that step is known to be a
  singleton.

The public API should therefore reuse `proximal_gradient_step` rather than restating its defining
proximal-set expression.
-/

section CoeReal

variable {E : Type u} [NormedAddCommGroup E]

-- Proof sketch: a real-valued function has finite value everywhere after coercion to `EReal`, so
-- its effective domain is `Set.univ`; the interior of `Set.univ` is again `Set.univ`.
/-- Every point belongs to the interior of the effective domain of the `EReal` coercion of a
real-valued function. -/
theorem mem_interior_effective_domain_of_coe_real
    (f : E → ℝ) (x : E) :
    x ∈ interior (effective_domain (Function.toEReal f)) := by
  simp [effective_domain]

/-- A point of `E` canonically determines a point of the interior effective domain of the
`EReal` coercion of a real-valued function. -/
def interior_effective_domain_point_of_real
    (f : E → ℝ) (x : E) :
    interior (effective_domain (Function.toEReal f)) :=
  ⟨x, mem_interior_effective_domain_of_coe_real f x⟩

end CoeReal

-- Proof sketch: positive scaling by `1 / L` preserves properness, lower semicontinuity, and
-- convexity of `g` by `scaled_function_proper_closed_convex_of_pos`. Theorem 6.3 then makes the
-- source-facing prox-gradient step `proximal_gradient_step f g x L` a singleton.
/-- Under the proper closed convex hypotheses on `g`, the Chapter 10 prox-gradient step at `x` is
a singleton. -/
theorem proximal_gradient_step_eq_singleton
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal) (x : E) :
    ∃ y : E, proximal_gradient_step f g x L = {y} := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  let hg_scaled :=
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
  simpa [proximal_gradient_step] using
    prox_eq_singleton_of_proper_closed_convex
      ((((1 / L : PosReal) : EReal) • g))
      hg_scaled.1
      hg_scaled.2.1
      hg_scaled.2.2
      ((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E))

/-- Definition 10.9: for a proper closed convex function `g` and a positive parameter `L`, the
prox-grad operator sends `x ∈ interior (dom f)` to the unique point of the Chapter 10 owner
`proximal_gradient_step f g x L`. -/
def prox_grad_operator (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] (L : PosReal) :
    interior (effective_domain f) → E :=
  fun x ↦
    Classical.choose <|
      proximal_gradient_step_eq_singleton f g L (x : E)

/- Textbook notation for the Chapter 10 prox-gradient update `T_L^{f,g}`. The supporting
regularity assumptions on `g` are ordinary ambient instance data; in particular they can be
supplied directly by local hypotheses or via an ambient `IsCompositeSmoothMinimizationProblem`
instance from Definition 10.3. -/
@[inherit_doc] scoped[Gradient] notation:max "T[" L ", " f ", " g "]" =>
  prox_grad_operator f g L

-- Proof sketch: `prox_grad_operator` is defined by choosing the unique element of the singleton
-- `proximal_gradient_step f g x L`.
/-- The prox-grad operator is the unique point of the Chapter 10 prox-gradient step. -/
theorem prox_grad_operator_eq_singleton
    (f g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (L : PosReal) (x : interior (effective_domain f)) :
    proximal_gradient_step f g (x : E) L =
      {T[L, f, g] x} :=
  Classical.choose_spec <| proximal_gradient_step_eq_singleton f g L (x : E)

section CoeReal

variable (f : E → ℝ) (g : E → EReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/- The core owner remains `prox_grad_operator` on `interior (effective_domain f)`. For a
real-valued smooth term, the source-facing Chapter 10 theorems use the canonical bridge
`interior_effective_domain_point_of_real` above to view that owner as a map on `E`. -/

/-- The proximal-gradient operator for a real-valued smooth term `f`, obtained by evaluating the
Chapter 10 owner `prox_grad_operator` of `f.toEReal` at the canonical interior-domain point
associated to `x`. -/
abbrev prox_gradient_operator
    (f : E → ℝ) (g : E → EReal)
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (L : PosReal) : E → E :=
  fun x ↦
    T[L, f.toEReal, g] (interior_effective_domain_point_of_real f x)

@[inherit_doc] scoped[Gradient] notation:max "T[" L "; " f ", " g "]" =>
  prox_gradient_operator f g L

/-- Evaluating `prox_gradient_operator` at `x` recovers the Chapter 10 prox-gradient operator of
`f.toEReal` at the canonical interior-domain point associated to `x`. -/
@[simp] theorem prox_gradient_operator_apply (L : PosReal) (x : E) :
    T[L; f, g] x = T[L, f.toEReal, g] (interior_effective_domain_point_of_real f x) := rfl

end CoeReal

end

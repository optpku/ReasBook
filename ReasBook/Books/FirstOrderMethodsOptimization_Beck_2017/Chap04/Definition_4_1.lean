/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 4.1 is `source-facing`: it introduces the Fenchel conjugate itself. In Chapter 4,
this file is also the `core/canonical` owner for that construction, so downstream files should
reuse `conjugate_function` rather than restating the same supremum formula under parallel local
names. The only primitive data here is the conjugate function; its evaluation formula is derived
API. -/

/-- Definition 4.1: the conjugate function `f*` of an extended-real-valued function `f` is the
extended-real-valued function on the dual space `E* = Module.Dual ℝ E` sending `y` to the
supremum of the values `y x - f x` over all `x : E`. This is the canonical `EReal` formulation
of the textbook formula (4.1). -/
noncomputable def conjugate_function (f : E → EReal) : Module.Dual ℝ E → EReal :=
  fun y ↦ sSup (Set.range fun x : E ↦ (y x : EReal) - f x)

/-- Evaluating the conjugate function at `y` gives the supremum of the dual pairing minus `f`
over all points of `E`. -/
theorem conjugate_function_apply (f : E → EReal) (y : Module.Dual ℝ E) :
    conjugate_function f y = sSup (Set.range fun x : E ↦ (y x : EReal) - f x) :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The primal-space view of the Fenchel conjugate, obtained by evaluating the Chapter 4 owner
`conjugate_function` along the Riesz map `toDualMap ℝ E : E → E*`. -/
noncomputable abbrev conjugate_function_primal (f : E → EReal) : E → EReal :=
  fun x ↦ conjugate_function f (toDualMap ℝ E x)

end

/-- Textbook postfix notation for the primal-space Fenchel conjugate. -/
postfix:max "∗" => conjugate_function_primal

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Evaluating `f∗` at `x` is the same as evaluating `conjugate_function f` at the dual vector
corresponding to `x`. -/
theorem conjugate_function_primal_apply (f : E → EReal) (x : E) :
    (f∗) x = conjugate_function f (toDualMap ℝ E x) :=
  rfl

end

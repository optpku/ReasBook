/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Definition 4.2 is `source-facing`: it introduces the biconjugate `f**`. The `core/canonical`
owner abstraction is still the chapter Fenchel-conjugate operator `conjugate_function` from
Definition 4.1, so the only primitive data here should be the canonical double-dual evaluation
`x ↦ Module.Dual.eval ℝ E x` together with a second application of that owner. The textbook
supremum formula is derived API.
-/
/-- Definition 4.2: the biconjugate `f**` of an extended-real-valued function `f` is the
extended-real-valued function on `E` obtained by applying the Chapter 4 owner
`conjugate_function` from Definition 4.1 to `f*` on the dual space and then restricting along the
canonical double-dual evaluation map `E → E**`. Equivalently, it is the supremum over the dual
space `E* = Module.Dual ℝ E` of the values `y x - f*(y)`. -/
noncomputable def biconjugate_function (f : E → EReal) : E → EReal :=
  fun x ↦ conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x)

/-- Evaluating the biconjugate at `x` gives the supremum of `y x - f*(y)` over all dual vectors
`y`. -/
theorem biconjugate_function_apply (f : E → EReal) (x : E) :
    biconjugate_function f x =
      sSup (Set.range fun y : Module.Dual ℝ E ↦ (y x : EReal) - conjugate_function f y) :=
  by
    let g : Module.Dual ℝ E → EReal := conjugate_function f
    simpa [biconjugate_function, g] using
      conjugate_function_apply g (Module.Dual.eval ℝ E x)

end

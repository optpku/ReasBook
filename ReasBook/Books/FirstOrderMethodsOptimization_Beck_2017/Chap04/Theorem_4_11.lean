/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 4.11 is `source-facing`: it rewrites Fenchel--Young equality in the textbook's
`argmax` language. The owner abstractions are already upstream: `conjugate_function` from
Definition 4.1 and Mathlib's `IsMaxOn`. This file is therefore only a `bridge/view` layer and
reuses those owners directly instead of repeating local copies of the same convex-analysis data. -/

recall conjugate_function

-- Proof sketch: unfold `conjugate_function`; by `isMaxOn_univ_iff`, saying that `x` maximizes the
-- affine-minus-`f` objective over `E` is exactly the statement that the value at `x` attains the
-- supremum defining `conjugate_function f y`.
/-- Helper for Theorem 4.11: the equality `f*(y) = ⟨y, x⟩ - f(x)` can be rewritten as the
statement that `x` is an argmax of the affine-minus-`f` objective, rendered in Lean as
`IsMaxOn ... Set.univ x`. -/
theorem conjugate_function_eq_iff_isMaxOn_pairing_sub_function
    (f : E → EReal) (x : E) (y : Module.Dual ℝ E) :
    conjugate_function f y = (y x : EReal) - f x ↔
      IsMaxOn (fun x' : E ↦ (y x' : EReal) - f x') Set.univ x := by
  -- Unfold the conjugate and rewrite the argmax statement into pointwise dominance on `Set.univ`.
  rw [conjugate_function_apply, isMaxOn_univ_iff]
  constructor
  · intro hEq x'
    -- Any value of the affine-minus-`f` objective is bounded above by the defining supremum.
    have hx' :
        ((y x' : EReal) - f x') ≤
          sSup (Set.range fun z : E ↦ (y z : EReal) - f z) :=
      le_sSup (Set.mem_range_self x')
    simpa [hEq] using hx'
  · intro hmax
    apply le_antisymm
    · -- The global upper bound on the objective bounds the whole range by the value at `x`.
      refine sSup_le ?_
      rintro _ ⟨x', rfl⟩
      exact hmax x'
    · -- The value at `x` is one of the terms in the supremum range.
      exact le_sSup (Set.mem_range_self x)

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall is_convex_function
recall conjugate_function

-- Proof sketch: rewrite the right-hand side as the statement that `y` attains the supremum in
-- the definition of `f**(x)`, then use
-- `biconjugate_function_eq_self_of_proper_closed_convex` to identify `f**` with `f`.
/-- Theorem 4.11 (2): under the chapter properness, closedness, and convexity hypotheses,
the equality `f(x) = ⟨x, y⟩ - f*(y)` is equivalent to saying that `y` is an argmax of the
affine-minus-`f*` objective on the dual space. -/
theorem self_eq_pairing_sub_conjugate_iff_isMaxOn_dual_of_proper_closed_convex
    (f : E → EReal) (hproper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f) (hconvex : is_convex_function f)
    (x : E) (y : Module.Dual ℝ E) :
    f x = (y x : EReal) - conjugate_function f y ↔
      IsMaxOn
        (fun y' : Module.Dual ℝ E ↦ (y' x : EReal) - conjugate_function f y')
        Set.univ y := by
  -- Route correction: reuse the primal bridge theorem on `f*`, then identify `f**` with `f`.
  have hdual :
      conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) =
          ((Module.Dual.eval ℝ E x) y : EReal) - conjugate_function f y ↔
        IsMaxOn
          (fun y' : Module.Dual ℝ E ↦
            ((Module.Dual.eval ℝ E x) y' : EReal) - conjugate_function f y')
          Set.univ y := by
    -- The first theorem applied to `f*` turns dual attainment into an `IsMaxOn` statement.
    simpa using
      (conjugate_function_eq_iff_isMaxOn_pairing_sub_function
        (f := conjugate_function f) (x := y) (y := Module.Dual.eval ℝ E x))
  have hbiconj :
      conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) = f x := by
    -- The closed proper convex hypotheses identify the double conjugate with `f` pointwise.
    simpa [biconjugate_function] using
      congrArg (fun g : E → EReal ↦ g x)
        (biconjugate_function_eq_self_of_proper_closed_convex
          f hproper hclosed hconvex)
  constructor
  · intro hEq
    have hEq' :
        conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) =
          ((Module.Dual.eval ℝ E x) y : EReal) - conjugate_function f y := by
      -- Rewrite the primal equality into the `f**` spelling expected by the first bridge.
      simpa [hbiconj] using hEq
    -- Normalize the evaluation functional back to the textbook pairing `y' x`.
    simpa using hdual.mp hEq'
  · intro hmax
    have hmax' :
        IsMaxOn
          (fun y' : Module.Dual ℝ E ↦
            ((Module.Dual.eval ℝ E x) y' : EReal) - conjugate_function f y')
          Set.univ y := by
      -- The double-dual evaluation objective is definitionally the same dual pairing objective.
      simpa using hmax
    have hEq' :
        conjugate_function (conjugate_function f) (Module.Dual.eval ℝ E x) =
          ((Module.Dual.eval ℝ E x) y : EReal) - conjugate_function f y :=
      hdual.mpr hmax'
    -- Replace `f**(x)` by `f x` to recover the claimed Fenchel--Young equality.
    simpa [hbiconj] using hEq'

end

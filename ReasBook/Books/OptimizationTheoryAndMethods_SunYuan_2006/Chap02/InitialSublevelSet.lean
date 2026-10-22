/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic

universe u

variable {E : Type u}

/-- The initial sublevel set `{y | f y ≤ f x0}` attached to the starting point `x0`. -/
abbrev initialSublevelSet (f : E → ℝ) (x0 : E) : Set E :=
  {y | f y ≤ f x0}

/-- Membership in `initialSublevelSet f x0` is exactly the inequality `f y ≤ f x0`. -/
theorem mem_initialSublevelSet {f : E → ℝ} {x0 y : E} :
    y ∈ initialSublevelSet f x0 ↔ f y ≤ f x0 :=
  Iff.rfl

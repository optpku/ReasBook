/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.Instances.Nat

/-!
# The real `C0Seq` model

This module provides the real `c₀` sequence model and its convergence and
coordinatewise API.
-/

public section

open Topology

/-- The real sequence space `c₀`, modeled as continuous maps on the discrete space `ℕ`
that vanish at infinity. -/
abbrev C0Seq : Type := ZeroAtInftyContinuousMap ℕ ℝ

namespace C0Seq

/-- Every real `c₀` sequence tends to zero along `Filter.atTop`. -/
theorem tendsto_zero (x : C0Seq) : Filter.Tendsto x Filter.atTop (𝓝 0) := by
  -- Route correction: use the coercion-facing API instead of the `toFun`-spelled projection.
  -- On `ℕ`, rewrite `atTop` as the cocompact filter from the vanishing condition.
  rw [← cocompact_eq_atTop]
  exact zero_at_infty x

/-- A real sequence tending to zero along `Filter.atTop` determines an element of `C0Seq`. -/
def ofTendsto (x : ℕ → ℝ) (hx : Filter.Tendsto x Filter.atTop (𝓝 0)) : C0Seq where
  toFun := x
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := cocompact_eq_atTop (α := ℕ) ▸ hx

/-- The element of `C0Seq` constructed from a convergent sequence has the same coordinates. -/
@[simp]
theorem ofTendsto_apply (x : ℕ → ℝ) (hx : Filter.Tendsto x Filter.atTop (𝓝 0))
    (n : ℕ) : ofTendsto x hx n = x n := by
  -- Evaluating the bundled map reduces to its defining coordinate function.
  rfl

end C0Seq

/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.WolfeCounterexample.HolderSharpness

/-!
# Theorem 1: strong Wolfe counterexample

Paper label: `thm:main` in `main-new.tex`.

For every `0 < c₁ < 2 / 3` and `2 / 3 ≤ c₂ < 1`, there is a `C²` objective
with globally one-half Hölder Hessian and Hessian bounds `(1 / 2, 3 / 2)`.
Classical DFP has a well-defined positive-step orbit satisfying strong Wolfe
whose gradient norms converge to a positive limit. This holds in every
dimension at least two.

The declaration below also proves that no Hölder exponent greater than one half
works on the initial sublevel. Its proof is in the imported `HolderSharpness`
module. This file checks the existing declaration for paper navigation.
-/

#check DFP.existsStrongWolfeCounterexampleHolderSharp_of_dimension_ge_two

/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_26_Derivative_formulas_and_scale_bounds_for_affine_cutoff_bumps_AffineBump.lean
-/

module

public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump

public section

open Set
open scoped ContDiff

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The affine cutoff bump formed from `χ`, centered at `x`, with scale `ρ` and
linear coefficient `a`. -/
abbrev affineCutoffBump (χ : E → ℝ) (x : E) (ρ : ℝ) (a : E) : E → ℝ :=
  AffineBump.scaledLinearBump χ x ρ a

/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_2_Positive_definiteness_preservation_for_inverse_form_DFP_InverseDFP.lean
-/

module

public import ReasLib.Optimization.DFP.InverseUpdate

open scoped Matrix

universe u

/- A compatibility check for the reusable inverse-form DFP update. -/
#check (Matrix.inverseDFPUpdate :
  ∀ {n : Type u} [Fintype n], Matrix n n ℝ → (n → ℝ) → (n → ℝ) → Matrix n n ℝ)

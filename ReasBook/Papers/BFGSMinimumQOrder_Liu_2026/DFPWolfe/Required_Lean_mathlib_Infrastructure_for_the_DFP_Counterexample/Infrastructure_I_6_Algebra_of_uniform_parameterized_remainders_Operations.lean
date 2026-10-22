/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_6_Algebra_of_uniform_parameterized_remainders_Operations.lean
-/

module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.Algebra
public import ReasLib.Analysis.Asymptotics.UniformRemainder.Matrix
public import ReasLib.Analysis.Asymptotics.UniformRemainder.Reparameterization
public import ReasLib.Analysis.Asymptotics.UniformRemainder.Sqrt

public section

universe u v

/- This compatibility bridge exposes the shared uniform-remainder algebra API. -/
#check (Asymptotics.IsUniformRemainderOn.add :
  ∀ {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R S : Θ → ℝ → E} {s : Set Θ} {C D q : ℝ},
    Asymptotics.IsUniformRemainderOn R s C q →
      Asymptotics.IsUniformRemainderOn S s D q →
      Asymptotics.IsUniformRemainderOn (fun θ ε ↦ R θ ε + S θ ε) s (C + D) q)

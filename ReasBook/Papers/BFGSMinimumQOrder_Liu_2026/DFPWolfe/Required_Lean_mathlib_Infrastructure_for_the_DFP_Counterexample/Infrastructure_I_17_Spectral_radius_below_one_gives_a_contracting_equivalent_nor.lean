/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_17_Spectral_radius_below_one_gives_a_contracting_equivalent_nor.lean
-/

module

public import ReasLib.LinearAlgebra.SpectralRadius.ContractingNorm

public section

universe u

/- Infrastructure I.17 (Spectral radius below one gives a contracting equivalent norm):
the explicit weighted-iterate seminorm is equivalent to the ambient norm and contracts the
endomorphism below every rate strictly between its complex spectral radius and one. -/
#check (LinearMap.adaptedSeminorm_spec :
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Module.End ℝ E) (r : NNReal),
    L.complexSpectralRadius < r → r < 1 →
      (L.adaptedSeminorm r).IsEquivalent (normSeminorm ℝ E) ∧
        (L.adaptedSeminorm r).IsContracting L r)

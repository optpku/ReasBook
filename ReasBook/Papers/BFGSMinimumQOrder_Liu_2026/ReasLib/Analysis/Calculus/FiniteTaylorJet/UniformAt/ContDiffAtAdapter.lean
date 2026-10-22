/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Analysis/Calculus/FiniteTaylorJet/UniformAt/ContDiffAtAdapter.lean
-/

module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformAt

public section

universe u v w

namespace FiniteTaylorJet

variable {Θ : Type u} {E : Type v} {F : Type w}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A compact parameter fiber with pointwise joint `C^m` regularity yields the uniform
derivative-constructed order-`m` jet required by `IsUniformOn`. -/
theorem isUniformOn_of_contDiffAt_via_uniformJetData (m : ℕ) (f : Θ → E → F) (a : E)
    (K : Set Θ) (hK : IsCompact K)
    (hf : ∀ θ ∈ K, ContDiffAt ℝ m (Function.uncurry f) (θ, a)) :
    IsUniformOn f (fun θ ↦ ofFunction ℝ m (f θ) a) a K := by
  exact (IsUniformOn.spec f (fun θ ↦ ofFunction ℝ m (f θ) a) a K).mpr
    (uniformJetData_of_contDiffAt m f a K hK hf)

end FiniteTaylorJet

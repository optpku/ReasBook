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

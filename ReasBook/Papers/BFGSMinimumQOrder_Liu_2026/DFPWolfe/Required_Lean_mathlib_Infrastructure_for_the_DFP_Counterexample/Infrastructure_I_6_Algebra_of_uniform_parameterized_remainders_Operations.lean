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

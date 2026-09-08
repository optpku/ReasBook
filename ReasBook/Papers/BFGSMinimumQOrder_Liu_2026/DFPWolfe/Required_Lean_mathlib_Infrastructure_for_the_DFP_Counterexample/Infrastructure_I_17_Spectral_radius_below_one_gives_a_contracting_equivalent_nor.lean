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

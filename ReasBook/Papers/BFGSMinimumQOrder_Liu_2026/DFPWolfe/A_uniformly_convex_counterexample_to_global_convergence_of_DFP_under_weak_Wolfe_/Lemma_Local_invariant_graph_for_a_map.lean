module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph

public section

open Filter
open scoped Topology

universe u

/- Lemma (Local invariant graph for a map): a finite-smooth center-stable map whose
stable linear part has complex spectral radius below one admits a local forward-invariant
`C^ν` graph through zero tangent to the center axis, without any invertibility assumption. -/
#check (LocalInvariantGraph.existsOfComplexSpectralRadiusLtOne :
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (ν : ℕ) (F : ℝ × X → ℝ × X) (L : Module.End ℝ X),
    2 ≤ ν →
      ContDiffAt ℝ ν F (0, 0) →
        F (0, 0) = (0, 0) →
          HasFDerivAt F
              (LocalCutoff.centerStable (Module.End.toContinuousLinearMap X L)) (0, 0) →
            L.complexSpectralRadius < 1 →
              ∃ ζ : ℝ → X,
                ContDiffAt ℝ ν ζ 0 ∧
                  ζ 0 = 0 ∧
                    HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
                      (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0]
                        fun u ↦ ζ (F (u, ζ u)).1)

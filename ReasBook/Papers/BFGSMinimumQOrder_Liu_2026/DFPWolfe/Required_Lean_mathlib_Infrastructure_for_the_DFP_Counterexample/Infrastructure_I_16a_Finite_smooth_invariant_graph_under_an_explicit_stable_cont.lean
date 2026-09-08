module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.MetricCutoff
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.FiniteSmoothBridge

public section

open Filter
open scoped Topology

universe u

/- Infrastructure I.16a (Finite-smooth invariant graph under an explicit stable contraction):
if a local `C^ν` center-stable map fixes zero, has derivative `(u, z) ↦ (u, L z)`, and
`‖L‖ < 1` in the chosen norm, then it has a local forward-invariant `C^ν` graph through zero
tangent to the center axis. No invertibility of `L` or of the full derivative is assumed. -/
#check (LocalInvariantGraph.existsOfNormLtOne :
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (ν : ℕ) (F : ℝ × X → ℝ × X) (L : X →L[ℝ] X),
    2 ≤ ν →
      ContDiffAt ℝ ν F (0, 0) →
        F (0, 0) = (0, 0) →
          HasFDerivAt F (LocalCutoff.centerStable L) (0, 0) →
            ‖L‖ < 1 →
              ∃ ζ : ℝ → X,
                ContDiffAt ℝ ν ζ 0 ∧
                  ζ 0 = 0 ∧
                    HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
                      (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦ ζ (F (u, ζ u)).1)

module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.FiniteSmooth

public section

noncomputable section

open Filter
open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {radius slope : ℝ≥0}

/-!
# Paper-facing finite-smooth graph certificates

This module names the quantitative hypotheses consumed by the explicit graph-transform
construction.  It is intentionally a certificate interface: a local derivative estimate by
itself does not supply the cutoff support, inverse-center bounds, or finite-order bunching
inequalities needed below.
-/

/-- Helper for Infrastructure I.16a: the finite-order bunching inequalities attached to a
quantitative graph-transform package. -/
def finiteSmoothBunching
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope)) : Prop :=
  ∀ r, 1 ≤ r → r ≤ d.ν →
    LocalCutoff.GraphTransform.rate d.lower d.linearRate d.stableCenter d.stableFiber
      d.centerFiber slope * (d.lower : ℝ)⁻¹ ^ r < 1

/-- Helper for Infrastructure I.16a: a paper-facing certificate supplies the quantitative
data, the center-stable derivative at the fixed point, and an eventual germ agreement for the
original map. -/
structure FiniteSmoothInvariantGraphCertificate
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (F : ℝ × X → ℝ × X) : Prop where
  bunching : finiteSmoothBunching d
  centerStableDeriv : HasFDerivAt
    (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N)
    (LocalCutoff.centerStable d.L) (0, 0)
  germ : F =ᶠ[𝓝 (0, 0)]
    LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N

/-- Infrastructure I.16a (paper-facing finite-smooth invariant graph): a quantitative cutoff
certificate and a certified original-map germ produce a finite-smooth invariant graph through
the fixed point with zero stable tangent.  The certificate remains an explicit input; this
theorem does not claim that the bare local hypotheses construct it automatically. -/
theorem invariantGraph_of_finiteSmoothCertificate
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (F : ℝ × X → ℝ × X)
    (certificate : FiniteSmoothInvariantGraphCertificate d F) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ d.ν ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦ ζ (F (u, ζ u)).1 := by
  exact invariantGraph_of_bunched_cutoff_germ d certificate.bunching
    certificate.centerStableDeriv F certificate.germ

end LocalInvariantGraph

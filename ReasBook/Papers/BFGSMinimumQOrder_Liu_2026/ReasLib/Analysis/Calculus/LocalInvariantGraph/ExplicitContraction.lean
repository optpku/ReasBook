module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ContractionData
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.Tangent
public import ReasLib.Analysis.Calculus.LocalCutoff.CenterStable
import all ReasLib.Analysis.Calculus.LocalCutoff.CenterStable

public section

noncomputable section

open Filter
open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {radius slope : ℝ≥0}

/-- Infrastructure I.16a (Finite-smooth invariant graph under an explicit stable contraction):
quantitative graph-transform data together with a finite-smoothness witness yields the invariant
graph, its zero value, and the zero stable tangent required by the source statement. -/
theorem exists_invariantGraph_of_explicit_contraction
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (hF_deriv : HasFDerivAt
      (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N)
      (LocalCutoff.centerStable d.L) (0, 0))
    (hregular : ∀ ζ : SmallLipschitzGraph X radius slope,
      d.transform ζ = ζ → ContDiffAt ℝ d.ν (ζ : ℝ → X) 0) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ d.ν ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N
              (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦
              ζ (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N
                (u, ζ u)).1 := by
  obtain ⟨ζ, hζ_fixed⟩ := d.exists_fixedGraph
  have hζ_smooth : ContDiffAt ℝ d.ν (ζ : ℝ → X) 0 := hregular ζ hζ_fixed
  have hF_zero : LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N (0, 0) = (0, 0) := by
    change LocalCutoff.linearize d.χ d.ρ (LocalCutoff.centerStable d.L) d.N
      (0 : ℝ × X) = (0 : ℝ × X)
    exact LocalCutoff.linearize_zero d.χ d.ρ (LocalCutoff.centerStable d.L) d.N d.hN_zero
  have hzero_lt_two : (0 : ℕ) < 2 := by norm_num
  have hν_pos : 0 < d.ν := hzero_lt_two.trans_le d.hν
  have hν_ne : d.ν ≠ 0 := Nat.ne_of_gt hν_pos
  have hζ_deriv : HasFDerivAt (ζ : ℝ → X) (fderiv ℝ ζ 0) 0 := by
    exact (hζ_smooth.differentiableAt (Nat.cast_ne_zero.mpr hν_ne)).hasFDerivAt
  have hlinearRate_real : (d.linearRate : ℝ) < 1 := by
    exact_mod_cast d.h_linearRate
  have hL : ‖d.L‖ < 1 := d.hL.trans_lt hlinearRate_real
  have hinvariant :
      (fun u ↦ (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N
        (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦
          ζ (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N
            (u, ζ u)).1 := by
    filter_upwards [] with u
    have hpoint := d.fixedGraph_invariant ζ hζ_fixed u
    rw [LocalCutoff.CenterProjection.map_apply] at hpoint
    exact hpoint.symm
  have htangent := tangent_zero_of_centerStable_invariant
    ζ (fderiv ℝ ζ 0)
    (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N)
    d.L (SmallLipschitzGraph.zero_apply ζ) hζ_deriv hF_zero hF_deriv hinvariant hL
  refine ⟨ζ, hζ_smooth, SmallLipschitzGraph.zero_apply ζ, htangent, ?_⟩
  exact hinvariant

end LocalInvariantGraph

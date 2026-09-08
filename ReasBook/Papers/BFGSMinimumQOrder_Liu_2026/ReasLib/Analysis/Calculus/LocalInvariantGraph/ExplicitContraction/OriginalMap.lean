module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction

public section

open Filter
open scoped NNReal Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {radius slope : ℝ≥0}

/-!
This companion is the final map-transfer interface for Infrastructure I.16a.  The
quantitative contraction package constructs the graph for a cutoff model; the only
additional fact needed to use it for a source map is equality of the two maps as
germs at the fixed point.
-/

/-- Helper for Infrastructure I.16a: a cutoff-model invariant graph transfers to an
original map that has the same germ at the fixed point. -/
theorem invariantGraph_of_cutoff_germ
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (hS_deriv : HasFDerivAt
      (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N)
      (LocalCutoff.centerStable d.L) (0, 0))
    (hregular : ∀ ζ : SmallLipschitzGraph X radius slope,
      d.transform ζ = ζ → ContDiffAt ℝ d.ν (ζ : ℝ → X) 0)
    (F : ℝ × X → ℝ × X)
    (hF_germ : F =ᶠ[𝓝 (0, 0)]
      LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ d.ν ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦ ζ (F (u, ζ u)).1 := by
  obtain ⟨ζ, hζ_smooth, hζ_zero, hζ_deriv, hS_invariant⟩ :=
    exists_invariantGraph_of_explicit_contraction d hS_deriv hregular
  have hζ_cont : Tendsto ζ (𝓝 0) (𝓝 (ζ 0)) :=
    hζ_smooth.continuousAt
  rw [hζ_zero] at hζ_cont
  have hgraph_tendsto : Tendsto (fun u : ℝ ↦ (u, ζ u))
      (𝓝 0) (𝓝 (0, 0)) := by
    have hfirst : Tendsto (fun u : ℝ ↦ u) (𝓝 0) (𝓝 (0 : ℝ)) := tendsto_id
    simpa only [nhds_prod_eq] using hfirst.prodMk hζ_cont
  have hF_graph : (fun u : ℝ ↦ F (u, ζ u)) =ᶠ[𝓝 0]
      (fun u ↦ LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N (u, ζ u)) := by
    simpa only [Function.comp_def] using hF_germ.comp_tendsto hgraph_tendsto
  refine ⟨ζ, hζ_smooth, hζ_zero, hζ_deriv, ?_⟩
  filter_upwards [hS_invariant, hF_graph] with u hu hFu
  rw [hFu] at *
  exact hu

/-- Helper for Infrastructure I.16a: a zero-valued, zero-derivative nonlinear remainder
gives the center-stable derivative required by the cutoff contraction certificate. -/
theorem centerStableLinearize_hasFDerivAt_of_zeroDerivative
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (hχ : DifferentiableAt ℝ
      (fun x : ℝ × X ↦ d.χ (d.ρ⁻¹ • x)) 0)
    (hN : HasFDerivAt d.N (0 : (ℝ × X) →L[ℝ] (ℝ × X)) 0)
    (hN_zero : d.N 0 = 0) :
    HasFDerivAt
      (LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N)
      (LocalCutoff.centerStable d.L) (0, 0) := by
  have hprod_add :
      (Prod.instAddCommGroup : AddCommGroup (ℝ × X)) =
        Prod.normedAddCommGroup.toAddCommGroup := by
    with_reducible_and_instances rfl
  have hprod_module :
      (Prod.instModule : Module ℝ (ℝ × X)) =
        Prod.normedSpace.toModule := by
    with_reducible_and_instances rfl
  have hprod_top :
      (instTopologicalSpaceProd : TopologicalSpace (ℝ × X)) =
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    with_reducible_and_instances rfl
  have hrem_raw := hχ.hasFDerivAt.smul hN
  have hrem_deriv_zero :
      d.χ (d.ρ⁻¹ • (0 : ℝ × X)) •
          (0 : (ℝ × X) →L[ℝ] (ℝ × X)) +
          (fderiv ℝ (fun x : ℝ × X ↦ d.χ (d.ρ⁻¹ • x)) 0).smulRight (d.N 0) =
        (0 : (ℝ × X) →L[ℝ] (ℝ × X)) := by
    rw [hN_zero, ContinuousLinearMap.smulRight_zero, add_zero, smul_zero]
  have hrem : HasFDerivAt (LocalCutoff.remainder d.χ d.ρ d.N)
      (0 : (ℝ × X) →L[ℝ] (ℝ × X)) 0 := by
    have hrem_raw' := hrem_raw.congr_fderiv hrem_deriv_zero
    convert hrem_raw' using 1
    funext x
    simp only [LocalCutoff.remainder_apply, Pi.smul_apply']
  have hlinear := (LocalCutoff.centerStable d.L).hasFDerivAt.add hrem
  have hlinear_fun :
      LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N =
        (LocalCutoff.centerStable d.L : ℝ × X → ℝ × X) +
          LocalCutoff.remainder d.χ d.ρ d.N := by
    funext x
    simp only [LocalCutoff.centerStableLinearize_apply, Pi.add_apply,
      LocalCutoff.remainder_apply]
  rw [← hlinear_fun] at hlinear
  simpa only [hprod_add, hprod_module, hprod_top, add_zero, Prod.mk_zero_zero] using hlinear

/-- Helper for Infrastructure I.16a: combines the zero-derivative remainder bridge with
the cutoff-germ transfer, so an original map can consume the quantitative contraction data
without separately constructing the derivative certificate. -/
theorem invariantGraph_of_zeroDerivative_cutoff_germ
    [CompleteSpace X] [FiniteDimensional ℝ X]
    (d : GraphTransformContractionData (X := X) (radius := radius) (slope := slope))
    (hχ : DifferentiableAt ℝ
      (fun x : ℝ × X ↦ d.χ (d.ρ⁻¹ • x)) 0)
    (hN : HasFDerivAt d.N (0 : (ℝ × X) →L[ℝ] (ℝ × X)) 0)
    (hN_zero : d.N 0 = 0)
    (hregular : ∀ ζ : SmallLipschitzGraph X radius slope,
      d.transform ζ = ζ → ContDiffAt ℝ d.ν (ζ : ℝ → X) 0)
    (F : ℝ × X → ℝ × X)
    (hF_germ : F =ᶠ[𝓝 (0, 0)]
      LocalCutoff.centerStableLinearize d.χ d.ρ d.L d.N) :
    ∃ ζ : ℝ → X,
      ContDiffAt ℝ d.ν ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] X) 0 ∧
            (fun u ↦ (F (u, ζ u)).2) =ᶠ[𝓝 0] fun u ↦ ζ (F (u, ζ u)).1 := by
  have hderiv := centerStableLinearize_hasFDerivAt_of_zeroDerivative d hχ hN hN_zero
  exact invariantGraph_of_cutoff_germ d hderiv hregular F hF_germ

end LocalInvariantGraph

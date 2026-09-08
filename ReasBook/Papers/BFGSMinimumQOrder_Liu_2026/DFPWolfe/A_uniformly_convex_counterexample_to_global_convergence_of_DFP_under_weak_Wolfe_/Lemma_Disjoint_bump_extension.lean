module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.GlobalRegularity

open Filter Set
open scoped ContDiff Topology

/- Lemma (Disjoint-bump extension): the global correction is C², vanishes on
the limiting circle, interpolates the endpoint jets, and has a scale-uniform
Hessian bound. -/
#check (DFP.TwoLeg.SlowCurve.bumpCorrectionExtension :
  ∀ curve : DFP.TwoLeg.SlowCurve,
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ContDiff ℝ 2 (orbit.bumpCorrection Clim Glim) ∧
                  EqOn (orbit.bumpCorrection Clim Glim) 0
                    (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ∧
                  (∀ k : ℕ,
                    orbit.bumpCorrection Clim Glim (orbit.endpoint k) = 0) ∧
                  (∀ k : ℕ,
                    gradient (orbit.bumpCorrection Clim Glim) (orbit.endpoint k) =
                      orbit.endpointCorrection Clim k) ∧
                  ∀ z : EuclideanSpace ℝ (Fin 2),
                    ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z‖ ≤
                      K * ε₀)

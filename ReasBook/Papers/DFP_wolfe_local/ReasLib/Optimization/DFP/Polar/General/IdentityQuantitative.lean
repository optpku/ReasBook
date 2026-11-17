module

public import ReasLib.Optimization.DFP.Polar.General.Transport
public import DFPWolfe.V21.IdentityQuantitative

public section

noncomputable section

open Filter
open DFP.Polar
open DFPWolfe.V21.IdentityQuantitative
open scoped Topology

namespace DFP.Polar.General.IdentityQuantitative

/-- Helper for cor:identity-initialization: the same arbitrary-exponent planar source witness has
the exact square-root spectral bounds and gradient lower limit from the manuscript.
The identity-block extension preserves the normalized planar gradient norms;
normalization and extension preserve the original accepted step lengths. -/
theorem quantitativeIdentityExtension (n : ℕ) (hn : 2 ≤ n) {β ε c1 c2 : ℝ}
    (source : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c1 c2)
    (h : Transport.CounterexampleProperties β ε source LinearIsometry.id) (hβ : 0 ≤ β) :
    0 < initialMinEigenvalue source ∧ 0 < initialMaxEigenvalue source ∧
      ∃ (P : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
        (m M : ℝ)
        (planar : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate 2 m M c1 c2)
        (result : DFP.WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate n
          (min m 1) (max M 1) c1 c2),
        P = (source.iteration.inverseHessianPosDef 0).sqrtEquiv ∧
          DFP.Polar.IdentityInitialization.PullbackData source.iteration planar.iteration P ∧
          DFP.Polar.IdentityInitialization.DimensionExtensionData n hn planar.iteration result.iteration ∧
          Transport.EllipseObjectiveProperties β result.iteration
            ((OrthogonalExtension.planeEmbedding n hn).toLinearMap.comp P.symm.toLinearMap) ∧
          HasHessianBounds (initialMinEigenvalue source / 2)
            (3 * initialMaxEigenvalue source / 2) planar.iteration.objective ∧
          Real.sqrt (initialMinEigenvalue source) ≤
            liminf (fun k ↦ ‖DFP.gradients planar.iteration.objective planar.iteration.point k‖) atTop ∧
          HasHessianBounds (min (initialMinEigenvalue source / 2) 1)
            (max (3 * initialMaxEigenvalue source / 2) 1) result.iteration.objective ∧
          Real.sqrt (initialMinEigenvalue source) ≤
            liminf (fun k ↦ ‖DFP.gradients result.iteration.objective result.iteration.point k‖) atTop ∧
          result.iteration.stepLength = source.iteration.stepLength ∧
          ∀ k, ‖DFP.gradients result.iteration.objective result.iteration.point k‖ =
            ‖DFP.gradients planar.iteration.objective planar.iteration.point k‖ := by
  obtain ⟨P, m, M, planar, hP, hdata, hEllipse⟩ :=
    Transport.normalizeCertificateWithProperties le_rfl source LinearIsometry.id h hβ
  have hPlanarEllipse : Transport.EllipseObjectiveProperties β planar.iteration P.symm.toLinearMap := by
    simpa only [LinearIsometry.id_toLinearMap, LinearMap.comp_id] using hEllipse
  obtain ⟨result, hExtension, hFinal⟩ :=
    Transport.extendNormalizedPlanar n hn planar P.symm.toLinearMap hPlanarEllipse hβ
  have hEigen := initialEigenvalues_pos source
  have hPlanar := pullback_hessian_bounds source hP hdata
  have hGradient := pullback_gradient_liminf source h.gradientLimit hP hdata
  have hExtended := extension_hessian_bounds hExtension planar.objectiveContDiff
    (half_pos hEigen.1) hPlanar
  have hNorm := extension_gradient_norm hExtension
  have hLiminf : Real.sqrt (initialMinEigenvalue source) ≤
      liminf (fun k ↦ ‖DFP.gradients result.iteration.objective result.iteration.point k‖) atTop := by
    simpa only [hNorm] using hGradient
  have hAlpha : result.iteration.stepLength = source.iteration.stepLength :=
    hExtension.stepLength.trans hdata.stepLength
  exact ⟨hEigen.1, hEigen.2, P, m, M, planar, result, hP, hdata, hExtension, hFinal,
    hPlanar, hGradient, hExtended, hLiminf, hAlpha, hNorm⟩

end DFP.Polar.General.IdentityQuantitative

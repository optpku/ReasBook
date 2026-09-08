module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_5_3_Disjoint_endpoint_bump_corrections_Bump
public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump
import all DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_5_3_Disjoint_endpoint_bump_corrections_Bump

public section

noncomputable section

open scoped ContDiff

namespace DFP.TwoPhaseOrbit

/-- Lemma 5.4 (First and second derivative formulas for each bump) (1):
the first Fréchet derivative of an endpoint correction bump. -/
theorem endpointBump_fderiv (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ)
    (z : EuclideanSpace ℝ (Fin 2))
    (hρ : 0 < orbit.interpolationRadius C G k) :
    fderiv ℝ (orbit.endpointBump C G k) z =
      EuclideanPlane.smoothCutoff
          ((orbit.interpolationRadius C G k)⁻¹ • (z - orbit.endpoint k)) •
        innerSL ℝ (orbit.endpointCorrection C k) +
      ((orbit.interpolationRadius C G k)⁻¹ *
          inner ℝ (orbit.endpointCorrection C k) (z - orbit.endpoint k)) •
        fderiv ℝ EuclideanPlane.smoothCutoff
          ((orbit.interpolationRadius C G k)⁻¹ • (z - orbit.endpoint k)) := by
  have htwo_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
    have htwo_nat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr htwo_nat
  have hcutoff : ContDiff ℝ 2 EuclideanPlane.smoothCutoff :=
    EuclideanPlane.contDiff_smoothCutoff.of_le htwo_le_infty
  simpa [affineCutoffBump, DFP.TwoPhaseOrbit.endpointBump_eq_scaledLinearBump] using
    AffineBump.fderiv_scaledLinearBump EuclideanPlane.smoothCutoff hcutoff
      (orbit.endpoint k) (orbit.interpolationRadius C G k)
      (orbit.endpointCorrection C k) z hρ

/-- Lemma 5.4 (First and second derivative formulas for each bump) (2):
the second Fréchet derivative of an endpoint correction bump, evaluated on two directions. -/
theorem endpointBump_secondFDeriv_apply (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ)
    (z v u : EuclideanSpace ℝ (Fin 2))
    (hρ : 0 < orbit.interpolationRadius C G k) :
    fderiv ℝ (fderiv ℝ (orbit.endpointBump C G k)) z v u =
      (orbit.interpolationRadius C G k)⁻¹ *
          (fderiv ℝ EuclideanPlane.smoothCutoff
                ((orbit.interpolationRadius C G k)⁻¹ • (z - orbit.endpoint k)) v *
              inner ℝ (orbit.endpointCorrection C k) u +
            inner ℝ (orbit.endpointCorrection C k) v *
              fderiv ℝ EuclideanPlane.smoothCutoff
                ((orbit.interpolationRadius C G k)⁻¹ • (z - orbit.endpoint k)) u) +
        (orbit.interpolationRadius C G k)⁻¹ ^ 2 *
          inner ℝ (orbit.endpointCorrection C k) (z - orbit.endpoint k) *
            fderiv ℝ (fderiv ℝ EuclideanPlane.smoothCutoff)
              ((orbit.interpolationRadius C G k)⁻¹ • (z - orbit.endpoint k)) v u := by
  have htwo_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
    have htwo_nat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr htwo_nat
  have hcutoff : ContDiff ℝ 2 EuclideanPlane.smoothCutoff :=
    EuclideanPlane.contDiff_smoothCutoff.of_le htwo_le_infty
  simpa [affineCutoffBump, DFP.TwoPhaseOrbit.endpointBump_eq_scaledLinearBump] using
    AffineBump.secondFDeriv_scaledLinearBump_apply EuclideanPlane.smoothCutoff hcutoff
      (orbit.endpoint k) (orbit.interpolationRadius C G k)
      (orbit.endpointCorrection C k) z v u hρ

end DFP.TwoPhaseOrbit

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GradientNormSmoothness
public import ReasLib.Geometry.Euclidean.Plane.OrientedAngleToReal
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GradientNormSmoothness
import all ReasLib.Geometry.Euclidean.Plane.OrientedAngleToReal

/-!
# Smooth endpoint-angle representatives for the two-leg observable map
-/

public section

noncomputable section

open scoped EuclideanSpace Matrix Nat ContDiff

namespace DFP.TwoLeg

/-- The principal real representative of the first endpoint-gradient angle is smooth to every
order at the common canceled base state. -/
@[fun_prop]
theorem firstEndpointAngleIncrement_toReal_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (observableMap x).firstEndpointAngleIncrement.toReal)
    (0, 2, 1) := by
  have ha : ContDiffAt ℝ k (fun _ : ℝ × ℝ × ℝ ↦ (1 : ℝ)) (0, 2, 1) := by
    fun_prop
  have hb : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦ x.2.1 * x.1 ^ 2) (0, 2, 1) := by
    fun_prop
  have hc := (DFP.FirstLeg.outputGradientEntry_analyticAt 0).contDiffAt (n := k)
  have hd := (DFP.FirstLeg.outputGradientEntry_analyticAt 1).contDiffAt (n := k)
  change ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
    (EuclideanPlane.orientation.oangle
      (!₂[(1 : ℝ), x.2.1 * x.1 ^ 2] : EuclideanSpace ℝ (Fin 2))
      (!₂[DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 0,
        DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 1] :
          EuclideanSpace ℝ (Fin 2))).toReal) (0, 2, 1)
  apply EuclideanPlane.contDiffAt_oangle_toReal_of_pos k ha hb hc hd
  · norm_num
  · norm_num [DFP.FirstLeg.outputGradient]

/-- The principal real representative of the second endpoint-gradient angle is smooth to every
order at the common canceled base state. -/
@[fun_prop]
theorem secondEndpointAngleIncrement_toReal_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (observableMap x).secondEndpointAngleIncrement.toReal)
    (0, 2, 1) := by
  have ha := (DFP.FirstLeg.outputGradientEntry_analyticAt 0).contDiffAt (n := k)
  have hb := (DFP.FirstLeg.outputGradientEntry_analyticAt 1).contDiffAt (n := k)
  have hF (i j : Fin 2) : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.frame x.1 x.2.1 x.2.2 i j)
      (0, 2, 1) := (DFP.FirstLeg.frameEntry_analyticAt i j).contDiffAt
  have hg (i : Fin 2) : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2 i)
      (0, 2, 1) := (DFP.SecondLeg.outputGradientEntry_analyticAt i).contDiffAt
  have hc : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) 0) (0, 2, 1) := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop
  have hd : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) 1) (0, 2, 1) := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop
  have hspectral : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradient : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  have hfinalPos : 0 < (DFP.FirstLeg.frame 0 2 1 *ᵥ
      DFP.SecondLeg.outputGradient 0 2 1) 0 := by
    norm_num [DFP.FirstLeg.frame, DFP.FirstLeg.outputMetric,
      DFP.SecondLeg.outputGradient, hspectral, hgradient,
      RealSymmetric2.lowVector, RealSymmetric2.lowRaw, RealSymmetric2.lowDenom,
      RealSymmetric2.low, RealSymmetric2.gap, EuclideanPlane.frame,
      EuclideanPlane.perp_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hsmooth : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
      (EuclideanPlane.orientation.oangle
        (!₂[DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 0,
          DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 1] :
            EuclideanSpace ℝ (Fin 2))
        (!₂[(DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
            DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) 0,
          (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
            DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) 1] :
            EuclideanSpace ℝ (Fin 2))).toReal) (0, 2, 1) := by
    apply EuclideanPlane.contDiffAt_oangle_toReal_of_pos k ha hb hc hd
    · norm_num [DFP.FirstLeg.outputGradient]
    · exact hfinalPos
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [] with x
  have hprojection := congrArg (fun pair ↦ pair.2.toReal)
    (observableMap_endpointAngleIncrements x.1 x.2.1 x.2.2)
  dsimp only at hprojection
  have hvecOne :
      WithLp.toLp 2 (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2) =
        (!₂[DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 0,
          DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 1] :
            EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i
    · rfl
    · rfl
  have hvecTwo :
      WithLp.toLp 2 (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) =
        (!₂[(DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
            DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) 0,
          (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
            DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) 1] :
            EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i
    · rfl
    · rfl
  rwa [hvecOne, hvecTwo] at hprojection

end DFP.TwoLeg

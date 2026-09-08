module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterSmoothness
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterSmoothness
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth gradient norms for the two-leg observable map

The three endpoint gradients stay nonzero at the canceled base state.  Their norms are therefore
smooth there to every order.
-/

public section

noncomputable section

open scoped EuclideanSpace Matrix Nat ContDiff

namespace DFP.TwoLeg

/-- Helper for Infrastructure I.16a: the initial endpoint gradient path. -/
private def initialGradientPath (x : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(1 : ℝ), x.2.1 * x.1 ^ 2]

/-- Helper for Infrastructure I.16a: the intermediate endpoint gradient path. -/
private def intermediateGradientPath (x : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2)

/-- Helper for Infrastructure I.16a: the final endpoint gradient path. -/
private def finalGradientPath (x : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
    DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2)

/-- Helper for Infrastructure I.16a: regularity of the initial gradient path. -/
private theorem initialGradientPath_contDiffAt (k : ℕ∞ω) :
    ContDiffAt ℝ k initialGradientPath (0, 2, 1) := by
  unfold initialGradientPath
  fun_prop

/-- Helper for Infrastructure I.16a: regularity of the intermediate gradient path. -/
private theorem intermediateGradientPath_contDiffAt (k : ℕ∞ω) :
    ContDiffAt ℝ k intermediateGradientPath (0, 2, 1) := by
  have hpi : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
    rw [contDiffAt_pi]
    intro i
    exact (DFP.FirstLeg.outputGradientEntry_analyticAt i).contDiffAt
  unfold intermediateGradientPath
  fun_prop

/-- Helper for Infrastructure I.16a: regularity of the final gradient path. -/
private theorem finalGradientPath_contDiffAt (k : ℕ∞ω) :
    ContDiffAt ℝ k finalGradientPath (0, 2, 1) := by
  have hF (i j : Fin 2) : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.frame x.1 x.2.1 x.2.2 i j)
      (0, 2, 1) := (DFP.FirstLeg.frameEntry_analyticAt i j).contDiffAt
  have hg (i : Fin 2) : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2 i)
      (0, 2, 1) := (DFP.SecondLeg.outputGradientEntry_analyticAt i).contDiffAt
  have hmul : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
      DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2) (0, 2, 1) := by
    rw [contDiffAt_pi]
    intro i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      fun_prop
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      fun_prop
  unfold finalGradientPath
  fun_prop

/-- Helper for Infrastructure I.16a: the initial gradient path is nonzero at the base. -/
private theorem initialGradientPath_base_ne : initialGradientPath (0, 2, 1) ≠ 0 := by
  intro h
  have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
  norm_num [initialGradientPath] at hzero

/-- Helper for Infrastructure I.16a: the intermediate gradient path is nonzero at the base. -/
private theorem intermediateGradientPath_base_ne :
    intermediateGradientPath (0, 2, 1) ≠ 0 := by
  intro h
  have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
  norm_num [intermediateGradientPath, DFP.FirstLeg.outputGradient] at hzero

/-- Helper for Infrastructure I.16a: the final gradient path is nonzero at the base. -/
private theorem finalGradientPath_base_ne : finalGradientPath (0, 2, 1) ≠ 0 := by
  have hspectral : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradient : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  intro h
  have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
  norm_num [finalGradientPath, DFP.FirstLeg.frame, DFP.FirstLeg.outputMetric,
    DFP.SecondLeg.outputGradient, hspectral, hgradient,
    RealSymmetric2.lowVector, RealSymmetric2.lowRaw, RealSymmetric2.lowDenom,
    RealSymmetric2.low, RealSymmetric2.gap, EuclideanPlane.frame,
    EuclideanPlane.perp_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hzero

/-- The initial-gradient norm is smooth to every order at the common canceled base state. -/
@[fun_prop]
theorem initialGradientNorm_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (observableMap x).initialGradientNorm) (0, 2, 1) := by
  have hnorm := (initialGradientPath_contDiffAt k).norm ℝ initialGradientPath_base_ne
  change ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦ ‖initialGradientPath x‖) (0, 2, 1)
  exact hnorm

/-- The intermediate-gradient norm is smooth to every order at the common canceled base state. -/
@[fun_prop]
theorem intermediateGradientNorm_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (observableMap x).intermediateGradientNorm) (0, 2, 1) := by
  have hnorm :=
    (intermediateGradientPath_contDiffAt k).norm ℝ intermediateGradientPath_base_ne
  change ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦ ‖intermediateGradientPath x‖) (0, 2, 1)
  exact hnorm

/-- The final-gradient norm is smooth to every order at the common canceled base state. -/
@[fun_prop]
theorem finalGradientNorm_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (observableMap x).finalGradientNorm) (0, 2, 1) := by
  have hnorm := (finalGradientPath_contDiffAt k).norm ℝ finalGradientPath_base_ne
  change ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦ ‖finalGradientPath x‖) (0, 2, 1)
  exact hnorm

end DFP.TwoLeg

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketScaleGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketScaleGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketGerm

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-!
This companion separates the regularity calculation for the scalar weighted center
bracket from the source-specific frame and displacement identities.  Its entry-point
theorems work on the joint parameter-radius space, so a source proof can provide five
small regularity certificates instead of unfolding the full bracket construction.
-/

/-- Helper for Infrastructure I.16a: the joint scalar coordinate normal form of a weighted
center bracket. -/
def coordZeroJoint
    (F : ((ℝ × ℝ × ℝ) × ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (u₀ u₁ : ((ℝ × ℝ × ℝ) × ℝ) → Fin 2 → ℝ) :
    ((ℝ × ℝ × ℝ) × ℝ) → ℝ :=
  fun z ↦ -(u₀ z 1) +
    2 * (F z 0 0 * u₁ z 1 + F z 0 1 * u₁ z 0)

/-- Helper for Infrastructure I.16a: entry regularity is preserved by the scalar weighted
center-bracket coordinate formula. -/
theorem coordZeroJoint_contDiffAt_of_entryRegularity
    {F : ((ℝ × ℝ × ℝ) × ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : ((ℝ × ℝ × ℝ) × ℝ) → Fin 2 → ℝ}
    {z₀ : (ℝ × ℝ × ℝ) × ℝ}
    (hF00 : ContDiffAt ℝ 3 (fun z ↦ F z 0 0) z₀)
    (hF01 : ContDiffAt ℝ 3 (fun z ↦ F z 0 1) z₀)
    (hu₀ : ContDiffAt ℝ 3 (fun z ↦ u₀ z 1) z₀)
    (hu₁₀ : ContDiffAt ℝ 3 (fun z ↦ u₁ z 0) z₀)
    (hu₁₁ : ContDiffAt ℝ 3 (fun z ↦ u₁ z 1) z₀) :
    ContDiffAt ℝ 3 (coordZeroJoint F u₀ u₁) z₀ := by
  have hfirst : ContDiffAt ℝ 3 (fun z ↦ F z 0 0 * u₁ z 1) z₀ :=
    hF00.mul hu₁₁
  have hsecond : ContDiffAt ℝ 3 (fun z ↦ F z 0 1 * u₁ z 0) z₀ :=
    hF01.mul hu₁₀
  have hsum : ContDiffAt ℝ 3
      (fun z ↦ F z 0 0 * u₁ z 1 + F z 0 1 * u₁ z 0) z₀ :=
    hfirst.add hsecond
  have hscaled : ContDiffAt ℝ 3
      (fun z ↦ 2 * (F z 0 0 * u₁ z 1 + F z 0 1 * u₁ z 0)) z₀ :=
    (contDiffAt_const (x := z₀) (c := (2 : ℝ))).mul hsum
  have hnegative : ContDiffAt ℝ 3 (fun z ↦ -(u₀ z 1)) z₀ :=
    hu₀.neg
  have hresult := hnegative.add hscaled
  change ContDiffAt ℝ 3
    (fun z ↦ -(u₀ z 1) +
      2 * (F z 0 0 * u₁ z 1 + F z 0 1 * u₁ z 0)) z₀
  exact hresult

/-- Helper for Infrastructure I.16a: analytic entry certificates provide the joint
`C³` regularity required by the bracket remainder transport. -/
theorem coordZeroJoint_contDiffAt_of_analyticEntries
    {F : ((ℝ × ℝ × ℝ) × ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    {u₀ u₁ : ((ℝ × ℝ × ℝ) × ℝ) → Fin 2 → ℝ}
    {z₀ : (ℝ × ℝ × ℝ) × ℝ}
    (hF00 : AnalyticAt ℝ (fun z ↦ F z 0 0) z₀)
    (hF01 : AnalyticAt ℝ (fun z ↦ F z 0 1) z₀)
    (hu₀ : AnalyticAt ℝ (fun z ↦ u₀ z 1) z₀)
    (hu₁₀ : AnalyticAt ℝ (fun z ↦ u₁ z 0) z₀)
    (hu₁₁ : AnalyticAt ℝ (fun z ↦ u₁ z 1) z₀) :
    ContDiffAt ℝ 3 (coordZeroJoint F u₀ u₁) z₀ := by
  have hF00' : ContDiffAt ℝ 3 (fun z ↦ F z 0 0) z₀ := hF00.contDiffAt
  have hF01' : ContDiffAt ℝ 3 (fun z ↦ F z 0 1) z₀ := hF01.contDiffAt
  have hu₀' : ContDiffAt ℝ 3 (fun z ↦ u₀ z 1) z₀ := hu₀.contDiffAt
  have hu₁₀' : ContDiffAt ℝ 3 (fun z ↦ u₁ z 0) z₀ := hu₁₀.contDiffAt
  have hu₁₁' : ContDiffAt ℝ 3 (fun z ↦ u₁ z 1) z₀ := hu₁₁.contDiffAt
  exact coordZeroJoint_contDiffAt_of_entryRegularity
    hF00' hF01' hu₀' hu₁₀' hu₁₁'

/-- Helper for Infrastructure I.16a: the canonical bracket is definitionally represented by
the joint scalar coordinate normal form. -/
theorem canonicalCenterBracket_uncurry_eq_coordZeroJoint :
    Function.uncurry canonicalCenterBracket =
      coordZeroJoint
        (fun z ↦ canonicalFirstFrame z.1 z.2)
        (fun z ↦ canonicalFirstNormalizedDisplacement z.1 z.2)
        (fun z ↦ canonicalSecondNormalizedDisplacement z.1 z.2) := by
  funext z
  dsimp [canonicalCenterBracket, coordZeroJoint]
  exact WeightedCenterBracket.coord_zero_apply
    (canonicalFirstFrame z.1 z.2)
    (canonicalFirstNormalizedDisplacement z.1 z.2)
    (canonicalSecondNormalizedDisplacement z.1 z.2)

/-- Infrastructure I.16a: joint entry regularity gives joint `C³` regularity of the canonical
weighted center bracket. -/
theorem canonicalCenterBracket_contDiffAt_of_entryRegularity
    {z₀ : (ℝ × ℝ × ℝ) × ℝ}
    (hF00 : ContDiffAt ℝ 3
      (fun z ↦ (canonicalFirstFrame z.1 z.2) 0 0) z₀)
    (hF01 : ContDiffAt ℝ 3
      (fun z ↦ (canonicalFirstFrame z.1 z.2) 0 1) z₀)
    (hu₀ : ContDiffAt ℝ 3
      (fun z ↦ (canonicalFirstNormalizedDisplacement z.1 z.2) 1) z₀)
    (hu₁₀ : ContDiffAt ℝ 3
      (fun z ↦ (canonicalSecondNormalizedDisplacement z.1 z.2) 0) z₀)
    (hu₁₁ : ContDiffAt ℝ 3
      (fun z ↦ (canonicalSecondNormalizedDisplacement z.1 z.2) 1) z₀) :
    ContDiffAt ℝ 3 (Function.uncurry canonicalCenterBracket) z₀ := by
  rw [canonicalCenterBracket_uncurry_eq_coordZeroJoint]
  exact coordZeroJoint_contDiffAt_of_entryRegularity hF00 hF01 hu₀ hu₁₀ hu₁₁

/-- Infrastructure I.16a: joint analytic entry certificates give the canonical bracket
regularity needed by `truncatedGerm_of_coordZero_quadraticGerm`. -/
theorem canonicalCenterBracket_contDiffAt_of_analyticEntries
    {z₀ : (ℝ × ℝ × ℝ) × ℝ}
    (hF00 : AnalyticAt ℝ
      (fun z ↦ (canonicalFirstFrame z.1 z.2) 0 0) z₀)
    (hF01 : AnalyticAt ℝ
      (fun z ↦ (canonicalFirstFrame z.1 z.2) 0 1) z₀)
    (hu₀ : AnalyticAt ℝ
      (fun z ↦ (canonicalFirstNormalizedDisplacement z.1 z.2) 1) z₀)
    (hu₁₀ : AnalyticAt ℝ
      (fun z ↦ (canonicalSecondNormalizedDisplacement z.1 z.2) 0) z₀)
    (hu₁₁ : AnalyticAt ℝ
      (fun z ↦ (canonicalSecondNormalizedDisplacement z.1 z.2) 1) z₀) :
    ContDiffAt ℝ 3 (Function.uncurry canonicalCenterBracket) z₀ := by
  have hF00' : ContDiffAt ℝ 3
      (fun z ↦ (canonicalFirstFrame z.1 z.2) 0 0) z₀ :=
    hF00.contDiffAt (n := 3)
  have hF01' : ContDiffAt ℝ 3
      (fun z ↦ (canonicalFirstFrame z.1 z.2) 0 1) z₀ :=
    hF01.contDiffAt (n := 3)
  have hu₀' : ContDiffAt ℝ 3
      (fun z ↦ (canonicalFirstNormalizedDisplacement z.1 z.2) 1) z₀ :=
    hu₀.contDiffAt (n := 3)
  have hu₁₀' : ContDiffAt ℝ 3
      (fun z ↦ (canonicalSecondNormalizedDisplacement z.1 z.2) 0) z₀ :=
    hu₁₀.contDiffAt (n := 3)
  have hu₁₁' : ContDiffAt ℝ 3
      (fun z ↦ (canonicalSecondNormalizedDisplacement z.1 z.2) 1) z₀ :=
    hu₁₁.contDiffAt (n := 3)
  exact canonicalCenterBracket_contDiffAt_of_entryRegularity
    hF00' hF01' hu₀' hu₁₀' hu₁₁'

end DFP.TwoLeg.Mixed

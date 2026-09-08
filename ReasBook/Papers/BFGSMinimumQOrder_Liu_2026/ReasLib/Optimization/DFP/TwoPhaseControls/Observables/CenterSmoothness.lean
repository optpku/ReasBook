module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.Smoothness
public import ReasLib.Analysis.Calculus.ContDiff.MatrixMulVec
public import ReasLib.Analysis.Calculus.ContDiff.MatrixDiagonal
public import ReasLib.Analysis.Calculus.ContDiff.MatrixOf
public import ReasLib.Analysis.Calculus.ContDiff.VecCons
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.Smoothness
import all ReasLib.Analysis.Calculus.ContDiff.MatrixMulVec
import all ReasLib.Analysis.Calculus.ContDiff.MatrixDiagonal
import all ReasLib.Analysis.Calculus.ContDiff.MatrixOf
import all ReasLib.Analysis.Calculus.ContDiff.VecCons

public section

noncomputable section

open Filter
open scoped EuclideanSpace Matrix Topology Nat ContDiff

namespace DFP.TwoLeg.CenterCancellation

def firstDisplacement (ε p : ℝ) : Fin 2 → ℝ :=
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let c := 2 * (p + 1) / (3 * B)
  ![-c * ε ^ 4, -c * ε ^ 2]

def secondEnergyFactor (ε p h : ℝ) : ℝ :=
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let w₁ := ε * L * Q - 2 * H * U
  let w₂ := H * U - 2 * ε ^ 3 * L * Q
  ε ^ 3 * L * Q * w₁ + H * U * w₂

def secondDisplacement (ε p h : ℝ) : Fin 2 → ℝ :=
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let delta := L * Q ^ 2 + H * U ^ 2
  let beta := secondEnergyFactor ε p h
  ![-(delta * ε ^ 4 * L * Q / (3 * beta)),
    -(delta * ε ^ 2 * H * U / (3 * beta))]

private def firstRawDisplacement (ε p h : ℝ) : Fin 2 → ℝ :=
  let g : Fin 2 → ℝ := ![(1 : ℝ), p * ε ^ 2]
  let H : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * ε ^ 4, h]
  let Hg := H *ᵥ g
  let A := (TwoPhaseControls.first ε).matrix
  let alpha := (TwoPhaseControls.first ε).tau * (g ⬝ᵥ Hg) /
    (Hg ⬝ᵥ (A *ᵥ Hg))
  let displacement := -(alpha • Hg)
  displacement

private def secondRawDisplacement (ε p h : ℝ) : Fin 2 → ℝ :=
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![ε ^ 4 * spectral.1, spectral.2]
  let g : Fin 2 → ℝ := ![gradient.1, ε ^ 2 * gradient.2]
  let Hg := H *ᵥ g
  let A := (TwoPhaseControls.second ε).matrix
  let alpha := (TwoPhaseControls.second ε).tau * (g ⬝ᵥ Hg) /
    (Hg ⬝ᵥ (A *ᵥ Hg))
  let displacement := -(alpha • Hg)
  displacement

private theorem firstDisplacement_eq_raw (ε p h : ℝ)
    (hp : p ≠ 0) (hh : h ≠ 0)
    (hB : 1 + 2 * ε ^ 3 + ε ^ 4 ≠ 0) :
    firstDisplacement ε p = firstRawDisplacement ε p h := by
  ext i
  have hB' : 1 + ε ^ 3 * 2 + ε ^ 4 ≠ 0 := by
    simpa [mul_comm] using hB
  fin_cases i
  all_goals
    simp [firstDisplacement, firstRawDisplacement, TwoPhaseControls.first_tau,
      TwoPhaseControls.first_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals
    by_cases hε : ε = 0
    · simp [hε]
    · field_simp [hp, hh, hB, hB', hε]
      have hunit : (1 + ε ^ 3 * 2 + ε ^ 4) *
          (1 + ε ^ 3 * 2 + ε ^ 4)⁻¹ = 1 :=
        mul_inv_cancel₀ hB'
      calc
        p + 1 = (p + 1) * 1 := by ring
        _ = (p + 1) * ((1 + ε ^ 3 * 2 + ε ^ 4) *
            (1 + ε ^ 3 * 2 + ε ^ 4)⁻¹) := by rw [hunit]
        _ = _ := by ring

private theorem secondDisplacement_eq_raw (ε p h : ℝ) :
    secondDisplacement ε p h = secondRawDisplacement ε p h := by
  ext i
  fin_cases i
  all_goals
    simp [secondDisplacement, secondRawDisplacement, secondEnergyFactor,
      TwoPhaseControls.second_tau, TwoPhaseControls.second_matrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals
    by_cases hε : ε = 0
    · simp [hε]
    · field_simp [hε]
      ring

private theorem firstSpectralFactors_base :
    DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
  simpa only [DFP.FirstLeg.factors] using
    congrArg Prod.fst DFP.FirstLeg.factorsBase

private theorem firstGradientFactors_base :
    DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
  simpa only [DFP.FirstLeg.factors] using
    congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase

private theorem firstSpectralFactors_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2)
    (0, 2, 1) := by
  exact (analyticAt_fst.comp DFP.FirstLeg.factorsAnalytic).contDiffAt

private theorem firstGradientFactors_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2)
    (0, 2, 1) := by
  exact ((analyticAt_fst.comp analyticAt_snd).comp
    DFP.FirstLeg.factorsAnalytic).contDiffAt

@[fun_prop]
theorem firstDisplacement_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ firstDisplacement x.1 x.2.1) (0, 2, 1) := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · unfold firstDisplacement
    dsimp
    fun_prop (disch := norm_num)
  · unfold firstDisplacement
    dsimp
    fun_prop (disch := norm_num)

theorem secondEnergyFactor_base : secondEnergyFactor 0 2 1 = 1 := by
  norm_num [secondEnergyFactor, firstSpectralFactors_base,
    firstGradientFactors_base]

@[fun_prop]
theorem secondEnergyFactor_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ secondEnergyFactor x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have hspectral := firstSpectralFactors_contDiffAt k
  have hgradient := firstGradientFactors_contDiffAt k
  have hL := contDiffAt_fst.comp (0, 2, 1) hspectral
  have hH := contDiffAt_snd.comp (0, 2, 1) hspectral
  have hQ := contDiffAt_fst.comp (0, 2, 1) hgradient
  have hU := contDiffAt_snd.comp (0, 2, 1) hgradient
  unfold secondEnergyFactor
  dsimp
  fun_prop

@[fun_prop]
theorem secondDisplacement_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ secondDisplacement x.1 x.2.1 x.2.2) (0, 2, 1) := by
  have hspectral := firstSpectralFactors_contDiffAt k
  have hgradient := firstGradientFactors_contDiffAt k
  have hL := contDiffAt_fst.comp (0, 2, 1) hspectral
  have hH := contDiffAt_snd.comp (0, 2, 1) hspectral
  have hQ := contDiffAt_fst.comp (0, 2, 1) hgradient
  have hU := contDiffAt_snd.comp (0, 2, 1) hgradient
  have hbeta := secondEnergyFactor_contDiffAt k
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · unfold secondDisplacement
    dsimp
    fun_prop (disch := norm_num [secondEnergyFactor_base])
  · unfold secondDisplacement
    dsimp
    fun_prop (disch := norm_num [secondEnergyFactor_base])

/-- The first center displacement written with the line-search singularity removed. -/
def canceledHalfCenterDisplacement (x : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  let ε := x.1
  let p := x.2.1
  let g₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(1 : ℝ), p * ε ^ 2]
  let g₁ : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (DFP.FirstLeg.outputGradient ε p x.2.2)
  let s₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (firstDisplacement ε p)
  s₀ - (g₁ - g₀)

/-- The full center displacement written with both line-search singularities removed. -/
def canceledFullCenterDisplacement (x : ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let F₁ := DFP.FirstLeg.frame ε p h
  let g₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(1 : ℝ), p * ε ^ 2]
  let g₂ : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (F₁ *ᵥ DFP.SecondLeg.outputGradient ε p h)
  let s₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (firstDisplacement ε p)
  let s₁ : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (F₁ *ᵥ secondDisplacement ε p h)
  s₀ + s₁ - (g₂ - g₀)

private theorem centerDisplacements_eventuallyEq :
    (fun x : ℝ × ℝ × ℝ ↦
      ((DFP.TwoLeg.observableMap x).halfCenterDisplacement,
        (DFP.TwoLeg.observableMap x).fullCenterDisplacement)) =ᶠ[𝓝 (0, 2, 1)]
      (fun x ↦ (canceledHalfCenterDisplacement x,
        canceledFullCenterDisplacement x)) := by
  have hpContinuous : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
    continuousAt_fst.comp continuousAt_snd
  have hhContinuous : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2) (0, 2, 1) :=
    continuousAt_snd.comp continuousAt_snd
  let B : ℝ × ℝ × ℝ → ℝ := fun x ↦ 1 + 2 * x.1 ^ 3 + x.1 ^ 4
  have hBContinuous : ContinuousAt B (0, 2, 1) := by
    dsimp only [B]
    fun_prop
  have hpBase : ((0, 2, 1) : ℝ × ℝ × ℝ).2.1 ≠ 0 := by
    norm_num
  have hhBase : ((0, 2, 1) : ℝ × ℝ × ℝ).2.2 ≠ 0 := by
    norm_num
  have hBBase : B (0, 2, 1) ≠ 0 := by
    norm_num [B]
  have hp : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.2.1 ≠ 0 :=
    hpContinuous.eventually_ne hpBase
  have hh : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.2.2 ≠ 0 :=
    hhContinuous.eventually_ne hhBase
  have hB : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), B x ≠ 0 :=
    hBContinuous.eventually_ne hBBase
  filter_upwards [hp, hh, hB] with x hpx hhx hBx
  have hBx' : 1 + 2 * x.1 ^ 3 + x.1 ^ 4 ≠ 0 := by
    simpa only [B] using hBx
  unfold canceledHalfCenterDisplacement canceledFullCenterDisplacement
  unfold DFP.TwoLeg.observableMap
  dsimp only
  rw [firstDisplacement_eq_raw x.1 x.2.1 x.2.2 hpx hhx hBx']
  rw [secondDisplacement_eq_raw]
  rfl

/-- Each coordinate of the cancelled first center displacement is smooth at the base. -/
@[fun_prop]
theorem canceledHalfCenterDisplacement_contDiffAt (k : ℕ∞ω) (i : Fin 2) :
    ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦ canceledHalfCenterDisplacement x i)
      (0, 2, 1) := by
  have hs₀ := firstDisplacement_contDiffAt k
  have hg₁ := (DFP.FirstLeg.outputGradientEntry_analyticAt i).contDiffAt (n := k)
  unfold canceledHalfCenterDisplacement
  dsimp
  fun_prop

/-- Each coordinate of the cancelled full center displacement is smooth at the base. -/
@[fun_prop]
theorem canceledFullCenterDisplacement_contDiffAt (k : ℕ∞ω) (i : Fin 2) :
    ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦ canceledFullCenterDisplacement x i)
      (0, 2, 1) := by
  have hs₀ := firstDisplacement_contDiffAt k
  have hs₁ := secondDisplacement_contDiffAt k
  have hF00 := (DFP.FirstLeg.frameEntry_analyticAt 0 0).contDiffAt (n := k)
  have hF01 := (DFP.FirstLeg.frameEntry_analyticAt 0 1).contDiffAt (n := k)
  have hF10 := (DFP.FirstLeg.frameEntry_analyticAt 1 0).contDiffAt (n := k)
  have hF11 := (DFP.FirstLeg.frameEntry_analyticAt 1 1).contDiffAt (n := k)
  have hg₂0 := (DFP.SecondLeg.outputGradientEntry_analyticAt 0).contDiffAt (n := k)
  have hg₂1 := (DFP.SecondLeg.outputGradientEntry_analyticAt 1).contDiffAt (n := k)
  fin_cases i
  · unfold canceledFullCenterDisplacement
    dsimp
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop
  · unfold canceledFullCenterDisplacement
    dsimp
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop

/-- Each original first-center observable coordinate is smooth after removal of the line-search
singularity. -/
@[fun_prop]
theorem halfCenterDisplacement_contDiffAt (k : ℕ∞ω) (i : Fin 2) :
    ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ (DFP.TwoLeg.observableMap x).halfCenterDisplacement i)
      (0, 2, 1) := by
  apply (canceledHalfCenterDisplacement_contDiffAt k i).congr_of_eventuallyEq
  filter_upwards [centerDisplacements_eventuallyEq] with x hx
  exact congrArg (fun y ↦ y.1 i) hx

/-- Each original full-center observable coordinate is smooth after removal of both line-search
singularities. -/
@[fun_prop]
theorem fullCenterDisplacement_contDiffAt (k : ℕ∞ω) (i : Fin 2) :
    ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ (DFP.TwoLeg.observableMap x).fullCenterDisplacement i)
      (0, 2, 1) := by
  apply (canceledFullCenterDisplacement_contDiffAt k i).congr_of_eventuallyEq
  filter_upwards [centerDisplacements_eventuallyEq] with x hx
  exact congrArg (fun y ↦ y.2 i) hx

/-- The nonvanishing factor left after extracting `ε²` from the first displacement. -/
def firstDisplacementFactor (ε p : ℝ) : Fin 2 → ℝ :=
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let c := 2 * (p + 1) / (3 * B)
  ![-c * ε ^ 2, -c]

/-- The nonvanishing factor left after extracting `ε²` from the second displacement. -/
def secondDisplacementFactor (ε p h : ℝ) : Fin 2 → ℝ :=
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let delta := L * Q ^ 2 + H * U ^ 2
  let beta := secondEnergyFactor ε p h
  ![-(delta * ε ^ 2 * L * Q / (3 * beta)),
    -(delta * H * U / (3 * beta))]

theorem firstDisplacement_eq_scale (ε p : ℝ) :
    firstDisplacement ε p = ε ^ 2 • firstDisplacementFactor ε p := by
  ext i
  fin_cases i
  · simp [firstDisplacement, firstDisplacementFactor]
    ring
  · simp [firstDisplacement, firstDisplacementFactor]
    ring

theorem secondDisplacement_eq_scale (ε p h : ℝ) :
    secondDisplacement ε p h = ε ^ 2 • secondDisplacementFactor ε p h := by
  ext i
  fin_cases i
  · simp [secondDisplacement, secondDisplacementFactor]
    ring
  · simp [secondDisplacement, secondDisplacementFactor]
    ring

@[fun_prop]
theorem firstDisplacementFactor_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ firstDisplacementFactor x.1 x.2.1) (0, 2, 1) := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · unfold firstDisplacementFactor
    dsimp
    fun_prop (disch := norm_num)
  · unfold firstDisplacementFactor
    dsimp
    fun_prop (disch := norm_num)

@[fun_prop]
theorem secondDisplacementFactor_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ secondDisplacementFactor x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
  have hspectral := firstSpectralFactors_contDiffAt k
  have hgradient := firstGradientFactors_contDiffAt k
  have hL := contDiffAt_fst.comp (0, 2, 1) hspectral
  have hH := contDiffAt_snd.comp (0, 2, 1) hspectral
  have hQ := contDiffAt_fst.comp (0, 2, 1) hgradient
  have hU := contDiffAt_snd.comp (0, 2, 1) hgradient
  have hbeta := secondEnergyFactor_contDiffAt k
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · unfold secondDisplacementFactor
    dsimp
    fun_prop (disch := norm_num [secondEnergyFactor_base])
  · unfold secondDisplacementFactor
    dsimp
    fun_prop (disch := norm_num [secondEnergyFactor_base])

private theorem firstDisplacementFactor_base_ne :
    WithLp.toLp 2 (firstDisplacementFactor 0 2) ≠
      (0 : EuclideanSpace ℝ (Fin 2)) := by
  intro h
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) h
  norm_num [firstDisplacementFactor] at hcoord

private theorem secondFramedDisplacementFactor_base_ne :
    WithLp.toLp 2 (DFP.FirstLeg.frame 0 2 1 *ᵥ
      secondDisplacementFactor 0 2 1) ≠ (0 : EuclideanSpace ℝ (Fin 2)) := by
  intro h
  have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) h
  norm_num [secondDisplacementFactor, secondEnergyFactor,
    firstSpectralFactors_base, firstGradientFactors_base,
    DFP.FirstLeg.frame, DFP.FirstLeg.outputMetric,
    RealSymmetric2.lowVector, RealSymmetric2.lowRaw, RealSymmetric2.lowDenom,
    RealSymmetric2.low, RealSymmetric2.gap, EuclideanPlane.frame,
    EuclideanPlane.perp_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hcoord

private theorem canceledFirstStepNorm_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦
      ‖WithLp.toLp 2 (firstDisplacement x.1 x.2.1)‖) (0, 2, 1) := by
  have hfactor : ContDiffAt ℝ k
      (fun x : ℝ × ℝ × ℝ ↦ WithLp.toLp 2
        (firstDisplacementFactor x.1 x.2.1)) (0, 2, 1) := by
    have hf := firstDisplacementFactor_contDiffAt k
    fun_prop
  have hnorm := hfactor.norm ℝ firstDisplacementFactor_base_ne
  have hsmooth : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
      x.1 ^ 2 * ‖WithLp.toLp 2 (firstDisplacementFactor x.1 x.2.1)‖)
      (0, 2, 1) := by
    fun_prop
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [] with x
  rw [firstDisplacement_eq_scale]
  simp [norm_smul, Real.norm_eq_abs]

private theorem canceledSecondStepNorm_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ ‖WithLp.toLp 2
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        secondDisplacement x.1 x.2.1 x.2.2)‖) (0, 2, 1) := by
  have hfactor := secondDisplacementFactor_contDiffAt k
  have hF00 := (DFP.FirstLeg.frameEntry_analyticAt 0 0).contDiffAt (n := k)
  have hF01 := (DFP.FirstLeg.frameEntry_analyticAt 0 1).contDiffAt (n := k)
  have hF10 := (DFP.FirstLeg.frameEntry_analyticAt 1 0).contDiffAt (n := k)
  have hF11 := (DFP.FirstLeg.frameEntry_analyticAt 1 1).contDiffAt (n := k)
  have hmul : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦
      DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        secondDisplacementFactor x.1 x.2.1 x.2.2) (0, 2, 1) := by
    rw [contDiffAt_pi]
    intro i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      fun_prop
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      fun_prop
  have hlp : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦ WithLp.toLp 2
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        secondDisplacementFactor x.1 x.2.1 x.2.2)) (0, 2, 1) := by
    fun_prop
  have hnorm := hlp.norm ℝ secondFramedDisplacementFactor_base_ne
  have hsmooth : ContDiffAt ℝ k (fun x : ℝ × ℝ × ℝ ↦ x.1 ^ 2 *
      ‖WithLp.toLp 2 (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        secondDisplacementFactor x.1 x.2.1 x.2.2)‖) (0, 2, 1) := by
    fun_prop
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [] with x
  rw [secondDisplacement_eq_scale]
  simp [Matrix.mulVec_smul, norm_smul, Real.norm_eq_abs]

private theorem stepNorms_eventuallyEq :
    (fun x : ℝ × ℝ × ℝ ↦
      ((DFP.TwoLeg.observableMap x).firstStepNorm,
        (DFP.TwoLeg.observableMap x).secondStepNorm)) =ᶠ[𝓝 (0, 2, 1)]
      (fun x ↦
        (‖WithLp.toLp 2 (firstDisplacement x.1 x.2.1)‖,
          ‖WithLp.toLp 2 (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
            secondDisplacement x.1 x.2.1 x.2.2)‖)) := by
  have hpContinuous : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
    continuousAt_fst.comp continuousAt_snd
  have hhContinuous : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2) (0, 2, 1) :=
    continuousAt_snd.comp continuousAt_snd
  let B : ℝ × ℝ × ℝ → ℝ := fun x ↦ 1 + 2 * x.1 ^ 3 + x.1 ^ 4
  have hBContinuous : ContinuousAt B (0, 2, 1) := by
    dsimp only [B]
    fun_prop
  have hpBase : ((0, 2, 1) : ℝ × ℝ × ℝ).2.1 ≠ 0 := by
    norm_num
  have hhBase : ((0, 2, 1) : ℝ × ℝ × ℝ).2.2 ≠ 0 := by
    norm_num
  have hBBase : B (0, 2, 1) ≠ 0 := by
    norm_num [B]
  have hp : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.2.1 ≠ 0 :=
    hpContinuous.eventually_ne hpBase
  have hh : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.2.2 ≠ 0 :=
    hhContinuous.eventually_ne hhBase
  have hB : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), B x ≠ 0 :=
    hBContinuous.eventually_ne hBBase
  filter_upwards [hp, hh, hB] with x hpx hhx hBx
  have hBx' : 1 + 2 * x.1 ^ 3 + x.1 ^ 4 ≠ 0 := by
    simpa only [B] using hBx
  unfold DFP.TwoLeg.observableMap
  dsimp only
  change
    (‖WithLp.toLp 2 (firstRawDisplacement x.1 x.2.1 x.2.2)‖,
      ‖WithLp.toLp 2 (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        secondRawDisplacement x.1 x.2.1 x.2.2)‖) =
    (‖WithLp.toLp 2 (firstDisplacement x.1 x.2.1)‖,
      ‖WithLp.toLp 2 (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        secondDisplacement x.1 x.2.1 x.2.2)‖)
  rw [← firstDisplacement_eq_raw x.1 x.2.1 x.2.2 hpx hhx hBx']
  rw [← secondDisplacement_eq_raw]

/-- The first raw step norm is smooth after extracting its even scale factor. -/
@[fun_prop]
theorem firstStepNorm_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (DFP.TwoLeg.observableMap x).firstStepNorm)
      (0, 2, 1) := by
  apply (canceledFirstStepNorm_contDiffAt k).congr_of_eventuallyEq
  filter_upwards [stepNorms_eventuallyEq] with x hx
  exact congrArg Prod.fst hx

/-- The second raw step norm is smooth after extracting its even scale factor. -/
@[fun_prop]
theorem secondStepNorm_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦ (DFP.TwoLeg.observableMap x).secondStepNorm)
      (0, 2, 1) := by
  apply (canceledSecondStepNorm_contDiffAt k).congr_of_eventuallyEq
  filter_upwards [stepNorms_eventuallyEq] with x hx
  exact congrArg Prod.snd hx

end DFP.TwoLeg.CenterCancellation

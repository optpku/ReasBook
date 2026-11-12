/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.FourierGeometry
public import glowinski_admm_counterexample.ReasLib.ADMM.RefinedEndpoint.DataChecks
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.RefinedConstants
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Instances.AddCircle.Real

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM.RefinedEndpoint.Period1024

noncomputable section

abbrev Phase := ZMod ADMM.RefinedEndpoint.Data.period
abbrev Coordinate := Fin 75
abbrev Ambient := EuclideanSpace ℂ Coordinate

instance period_neZero : NeZero ADMM.RefinedEndpoint.Data.period := ⟨by decide⟩

/-- The exact `h`th input factor; no factor is dropped or merged. -/
def factor (h : Coordinate) : ADMM.RefinedEndpoint.Data.FourierFactor :=
  ADMM.RefinedEndpoint.Data.fourierFactors.get
    ⟨h.val, by simpa only [ADMM.RefinedEndpoint.Data.fourierFactors_length] using h.isLt⟩

/-- The factor lookup always returns one of the original 75 records. -/
theorem factor_mem (h : Coordinate) : factor h ∈ ADMM.RefinedEndpoint.Data.fourierFactors :=
  List.get_mem _ _

/-- The positive Fourier mode attached to a coordinate plane. -/
def mode (h : Coordinate) : ℕ := (factor h).mode

theorem mode_in_range (h : Coordinate) :
    1 ≤ mode h ∧ mode h ≤ ADMM.RefinedEndpoint.Data.period / 2 := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp ADMM.RefinedEndpoint.Data.fourierFactors_in_range)
      (factor h) (factor_mem h))

/-- The Nyquist plane has multiplicity one; the other planes have multiplicity two. -/
def multiplicity (h : Coordinate) : ℝ :=
  if mode h = ADMM.RefinedEndpoint.Data.period / 2 then 1 else 2

theorem multiplicity_pos (h : Coordinate) : 0 < multiplicity h := by
  unfold multiplicity
  split <;> norm_num

/-- The normalization `sqrt(m_j/N)` used in Appendix C.3. -/
def normalization (h : Coordinate) : ℝ :=
  Real.sqrt (multiplicity h / ADMM.RefinedEndpoint.Data.period)

theorem normalization_pos (h : Coordinate) : 0 < normalization h := by
  apply Real.sqrt_pos.2
  exact div_pos (multiplicity_pos h) (by norm_num [ADMM.RefinedEndpoint.Data.period])

theorem normalization_sq (h : Coordinate) :
    normalization h ^ 2 = multiplicity h / ADMM.RefinedEndpoint.Data.period := by
  exact Real.sq_sqrt (le_of_lt (div_pos (multiplicity_pos h)
    (by norm_num [ADMM.RefinedEndpoint.Data.period])))

/-- The first rational complex coefficient, with the common integer denominator. -/
def etaCoefficient (h : Coordinate) : ℂ :=
  ((factor h).etaRe + Complex.I * (factor h).etaIm) /
    ADMM.RefinedEndpoint.Data.denominator

/-- The scaled-multiplier rational complex coefficient with the same denominator. -/
def multiplierCoefficient (h : Coordinate) : ℂ :=
  ((factor h).wRe + Complex.I * (factor h).wIm) /
    ADMM.RefinedEndpoint.Data.denominator

def etaAmplitude (h : Coordinate) : ℂ := (normalization h : ℂ) * etaCoefficient h
def multiplierAmplitude (h : Coordinate) : ℂ :=
  (normalization h : ℂ) * multiplierCoefficient h

/-- Actual roots-of-unity phases, using the standard character constructed
from Mathlib's maps `ZMod 1024 → ℝ/ℤ → Circle`. -/
def phase (h : Coordinate) (i : Phase) : ℂ :=
  AddCircle.toCircle (ZMod.toAddCircle ((mode h : Phase) * i))

/-- Every concrete phase factor has unit norm. -/
theorem phase_norm (h : Coordinate) (i : Phase) : ‖phase h i‖ = 1 := by
  exact Circle.norm_coe _

/-- The true roots of unity satisfy the cyclic successor law exactly. -/
theorem phase_succ (h : Coordinate) (i : Phase) :
    phase h (i + 1) = phase h 1 * phase h i := by
  simp only [phase, mul_add, map_add, AddCircle.toCircle_add, Circle.coe_mul]
  exact mul_comm _ _

@[simp]
theorem phase_zero (h : Coordinate) : phase h 0 = 1 := by
  simp [phase]

/-- The character is exactly the exponential Fourier formula in the manuscript. -/
theorem phase_natCast (h : Coordinate) (k : ℕ) :
    phase h (k : Phase) =
      Complex.exp (2 * Real.pi * Complex.I * (mode h * k : ℕ) /
        ADMM.RefinedEndpoint.Data.period) := by
  unfold phase
  rw [← Nat.cast_mul, ZMod.toAddCircle_natCast,
    AddCircle.toCircle_apply_mk, Circle.coe_exp]
  push_cast
  congr 1
  ring

/-- The paper's first image family in 75 complex planes, viewed as a real space. -/
def eta : Phase → Ambient := fourierFamily phase etaAmplitude

/-- The paper's scaled-multiplier family in the same real coordinate space. -/
def scaledMultiplier : Phase → Ambient := fourierFamily phase multiplierAmplitude

@[simp]
theorem eta_apply (i : Phase) (h : Coordinate) :
    eta i h = phase h i * ((normalization h : ℂ) * etaCoefficient h) := rfl

@[simp]
theorem scaledMultiplier_apply (i : Phase) (h : Coordinate) :
    scaledMultiplier i h =
      phase h i * ((normalization h : ℂ) * multiplierCoefficient h) := rfl

/-- One real orthogonal map advances the concrete 1024-phase data. -/
theorem hasOrthogonalCyclicSymmetry :
    ProjectionCycle.HasOrthogonalCyclicSymmetry eta scaledMultiplier := by
  exact fourierFamily_hasOrthogonalCyclicSymmetry phase
    (fun h ↦ phase_norm h 1) phase_succ etaAmplitude multiplierAmplitude

/-- The actual Fourier data has a positive-semidefinite real Gram matrix. -/
theorem gram_posSemidef :
    (Matrix.gram ℝ (fun p : Fin 2 × Phase ↦
      if p.1 = 0 then eta p.2 else scaledMultiplier p.2)).PosSemidef := by
  exact fourier_gram_posSemidef phase etaAmplitude multiplierAmplitude

/-- This is only the final assembly interface for the numerical certificate.
The 2048 strict phase-zero support checks and positive residual are still
explicit hypotheses; this theorem does not assert the refined upper bound. -/
theorem endpoint_lt_upper_of_supports
    (hfirst : ZeroPhaseStrictSupports (imageVertex eta scaledMultiplier)
      (firstSupportNormal ADMM.RefinedEndpoint.upper eta scaledMultiplier))
    (hsecond : ZeroPhaseStrictSupports eta
      (secondSupportNormal ADMM.RefinedEndpoint.upper scaledMultiplier))
    (hresidual : 0 < ‖displacement scaledMultiplier 0‖ ^ 2) :
    ADMM.uniformConvergenceEndpoint < ADMM.RefinedEndpoint.upper := by
  apply endpoint_lt_of_scaled_zeroPhase _ eta scaledMultiplier
    (by norm_num [ADMM.RefinedEndpoint.Data.period])
    (ADMM.RefinedEndpoint.lower_pos.trans ADMM.RefinedEndpoint.lower_lt_upper)
    ADMM.RefinedEndpoint.upper_lt_two hasOrthogonalCyclicSymmetry hfirst hsecond hresidual

end

end ConsensusADMM.RefinedEndpoint.Period1024

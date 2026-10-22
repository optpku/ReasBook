/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.TwoCycle

open scoped Topology

/- v21 eq:polar-two-cycle
The checks identify the explicit rational branch, its local inverse, the two
normalized states, the alternating limiting stages, and their reference data.
-/
#check (DFP.Polar.TwoCycle.parameterSet : Set ℝ)
#check (DFP.Polar.TwoCycle.parameterSet_def :
  DFP.Polar.TwoCycle.parameterSet =
    Set.Ioo (3 * DFP.Polar.baseAngle / 4) (5 * DFP.Polar.baseAngle / 4))
#check (DFP.Polar.TwoCycle.normalizationSet : Set ℝ)
#check (DFP.Polar.TwoCycle.normalizationSet_def :
  DFP.Polar.TwoCycle.normalizationSet =
    DFP.Polar.cycleK '' DFP.Polar.TwoCycle.parameterSet)
#check (DFP.Polar.TwoCycle.kZero : ℝ)
#check (DFP.Polar.TwoCycle.kZero_def :
  DFP.Polar.TwoCycle.kZero = DFP.Polar.cycleK DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.inverseParameter : ℝ → ℝ)
#check (DFP.Polar.TwoCycle.inverseParameter_mapsTo :
  Set.MapsTo DFP.Polar.TwoCycle.inverseParameter
    DFP.Polar.TwoCycle.normalizationSet DFP.Polar.TwoCycle.parameterSet)
#check (DFP.Polar.TwoCycle.inverseParameter_invOn :
  Set.InvOn DFP.Polar.TwoCycle.inverseParameter DFP.Polar.cycleK
    DFP.Polar.TwoCycle.parameterSet DFP.Polar.TwoCycle.normalizationSet)
#check (DFP.Polar.TwoCycle.evenState : ℝ → ℝ × ℝ × ℝ)
#check (DFP.Polar.TwoCycle.evenState_apply :
  ∀ K : ℝ, DFP.Polar.TwoCycle.evenState K =
    (K, K * DFP.Polar.cycleW (DFP.Polar.TwoCycle.inverseParameter K),
      1 + K * DFP.Polar.cycleW (DFP.Polar.TwoCycle.inverseParameter K) ^ 2))
#check (DFP.Polar.TwoCycle.oddState : ℝ → ℝ × ℝ × ℝ)
#check (DFP.Polar.TwoCycle.oddState_apply :
  ∀ K : ℝ, DFP.Polar.TwoCycle.oddState K =
    (K, K * DFP.Polar.cycleZ (DFP.Polar.TwoCycle.inverseParameter K),
      1 + K * DFP.Polar.cycleZ (DFP.Polar.TwoCycle.inverseParameter K) ^ 2))
#check (DFP.Polar.TwoCycle.evenReference : ℝ × ℝ × ℝ)
#check (DFP.Polar.TwoCycle.evenReference_def :
  DFP.Polar.TwoCycle.evenReference =
    (DFP.Polar.TwoCycle.kZero, 1 / DFP.Polar.baseAngle, 3))
#check (DFP.Polar.TwoCycle.oddReference : ℝ × ℝ × ℝ)
#check (DFP.Polar.TwoCycle.oddReference_def :
  DFP.Polar.TwoCycle.oddReference =
    (DFP.Polar.TwoCycle.kZero, 1 / (2 * DFP.Polar.baseAngle), 3 / 2))
#check (DFP.Polar.TwoCycle.cycleW_sub_cycleZ :
  ∀ (ν : ℝ), ν ∈ DFP.Polar.TwoCycle.parameterSet →
    DFP.Polar.cycleW ν - DFP.Polar.cycleZ ν = ν)
#check (DFP.Polar.TwoCycle.one_div_cycleK_mul_cycleZ :
  ∀ (ν : ℝ), ν ∈ DFP.Polar.TwoCycle.parameterSet →
    1 / (DFP.Polar.cycleK ν * DFP.Polar.cycleZ ν) = DFP.Polar.baseAngle + ν)
#check (DFP.Polar.TwoCycle.one_div_cycleK_mul_cycleW :
  ∀ (ν : ℝ), ν ∈ DFP.Polar.TwoCycle.parameterSet →
    1 / (DFP.Polar.cycleK ν * DFP.Polar.cycleW ν) = 2 * DFP.Polar.baseAngle - ν)
#check (DFP.Polar.TwoCycle.evenToOdd :
  ∀ (K : ℝ), K ∈ DFP.Polar.TwoCycle.normalizationSet →
    DFP.Polar.Normalized.leadingStage (2 * DFP.Polar.baseAngle)
      (DFP.Polar.TwoCycle.evenState K) = DFP.Polar.TwoCycle.oddState K)
#check (DFP.Polar.TwoCycle.oddToEven :
  ∀ (K : ℝ), K ∈ DFP.Polar.TwoCycle.normalizationSet →
    DFP.Polar.Normalized.leadingStage DFP.Polar.baseAngle
      (DFP.Polar.TwoCycle.oddState K) = DFP.Polar.TwoCycle.evenState K)
#check (DFP.Polar.TwoCycle.evenState_det :
  ∀ (K : ℝ), K ∈ DFP.Polar.TwoCycle.normalizationSet →
    Matrix.det
      (RealSymmetric2.matrix (DFP.Polar.TwoCycle.evenState K).1
        (DFP.Polar.TwoCycle.evenState K).2.1
        (DFP.Polar.TwoCycle.evenState K).2.2) = K)
#check (DFP.Polar.TwoCycle.oddState_det :
  ∀ (K : ℝ), K ∈ DFP.Polar.TwoCycle.normalizationSet →
    Matrix.det
      (RealSymmetric2.matrix (DFP.Polar.TwoCycle.oddState K).1
        (DFP.Polar.TwoCycle.oddState K).2.1
        (DFP.Polar.TwoCycle.oddState K).2.2) = K)
#check (DFP.Polar.TwoCycle.slope_evenState :
  ∀ (K : ℝ), K ∈ DFP.Polar.TwoCycle.normalizationSet →
    DFP.Polar.Normalized.slope (DFP.Polar.TwoCycle.evenState K) =
      DFP.Polar.cycleZ (DFP.Polar.TwoCycle.inverseParameter K) +
        2 * DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.slope_oddState :
  ∀ (K : ℝ), K ∈ DFP.Polar.TwoCycle.normalizationSet →
    DFP.Polar.Normalized.slope (DFP.Polar.TwoCycle.oddState K) =
      DFP.Polar.cycleW (DFP.Polar.TwoCycle.inverseParameter K) + DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.kZero_eq :
  DFP.Polar.TwoCycle.kZero = 1 / (2 * DFP.Polar.baseAngle ^ 2))
#check (DFP.Polar.TwoCycle.hasDerivAt_cycleK_baseAngle :
  HasDerivAt DFP.Polar.cycleK (3 / (4 * DFP.Polar.baseAngle ^ 3))
    DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.hasStrictDerivAt_cycleK_baseAngle :
  HasStrictDerivAt DFP.Polar.cycleK (3 / (4 * DFP.Polar.baseAngle ^ 3))
    DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.cycleK_derivCoefficient_pos :
  0 < 3 / (4 * DFP.Polar.baseAngle ^ 3))
#check (DFP.Polar.TwoCycle.parameterSet_mem_nhds :
  DFP.Polar.TwoCycle.parameterSet ∈ 𝓝 DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.cycleK_bijOn_parameterSet :
  Set.BijOn DFP.Polar.cycleK DFP.Polar.TwoCycle.parameterSet
    DFP.Polar.TwoCycle.normalizationSet)
#check (DFP.Polar.TwoCycle.normalizationSet_mem_nhds :
  DFP.Polar.TwoCycle.normalizationSet ∈ 𝓝 DFP.Polar.TwoCycle.kZero)
#check (DFP.Polar.TwoCycle.cycleFamily_mapsTo_positive :
  Set.MapsTo
    (fun ν : ℝ ↦ (DFP.Polar.cycleK ν, DFP.Polar.cycleZ ν, DFP.Polar.cycleW ν))
    DFP.Polar.TwoCycle.parameterSet (Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.Ioi 0)))
#check (DFP.Polar.TwoCycle.evenState_mapsTo_positive :
  Set.MapsTo DFP.Polar.TwoCycle.evenState DFP.Polar.TwoCycle.normalizationSet
    (Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.univ)))
#check (DFP.Polar.TwoCycle.oddState_mapsTo_positive :
  Set.MapsTo DFP.Polar.TwoCycle.oddState DFP.Polar.TwoCycle.normalizationSet
    (Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.univ)))
#check (DFP.Polar.TwoCycle.inverseParameter_kZero :
  DFP.Polar.TwoCycle.inverseParameter DFP.Polar.TwoCycle.kZero = DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.cycleZ_inverseParameter_kZero :
  DFP.Polar.cycleZ (DFP.Polar.TwoCycle.inverseParameter DFP.Polar.TwoCycle.kZero) =
    DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.cycleW_inverseParameter_kZero :
  DFP.Polar.cycleW (DFP.Polar.TwoCycle.inverseParameter DFP.Polar.TwoCycle.kZero) =
    2 * DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.evenState_kZero :
  DFP.Polar.TwoCycle.evenState DFP.Polar.TwoCycle.kZero =
    DFP.Polar.TwoCycle.evenReference)
#check (DFP.Polar.TwoCycle.oddState_kZero :
  DFP.Polar.TwoCycle.oddState DFP.Polar.TwoCycle.kZero =
    DFP.Polar.TwoCycle.oddReference)
#check (DFP.Polar.TwoCycle.slope_evenReference :
  DFP.Polar.Normalized.slope DFP.Polar.TwoCycle.evenReference =
    3 * DFP.Polar.baseAngle)
#check (DFP.Polar.TwoCycle.slope_oddReference :
  DFP.Polar.Normalized.slope DFP.Polar.TwoCycle.oddReference =
    3 * DFP.Polar.baseAngle)

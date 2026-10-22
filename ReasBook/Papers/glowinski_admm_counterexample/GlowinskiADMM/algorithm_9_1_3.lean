/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Coefficient
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.GramMatrix
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Threshold

@[expose] public section

/- Algorithm 9.1.3: for the support tests, form `H = 2K - I₉₆ + 3hhᵀ` by eq:H,
work with the coefficient vectors `ηᵢ = eᵢ` and `wᵢ = e₄₈₊ᵢ / γ₀`, and interpret
every inner product as `zᵀHw`. Set `ρᵢ = wᵢ - wᵢ₋₁`, `ξᵢ = ηᵢ + ρᵢ`, and use the
affine normals `aᵢ(γ) = ηᵢ₋₁ - γ wᵢ₋₁ - ξᵢ` and `cᵢ(γ) = γ wᵢ₋₁ + ρᵢ` of Proposition
prop:fixed. At phase zero the support is evaluated against the origin and against
every other phase, for both blocks. These `96` rational affine expressions give
all `4608` supports by cyclic shifts; their slopes and endpoint values satisfy
Table 2 and the single exceptional expression is eq:active, so the displayed
inputs determine every check needed for Proposition prop:fixed. -/
#check (ConsensusADMM.Period48.Coefficient.support :
  Fin 2 → ℝ → ZMod 48 → ZMod 48 → ℝ)
#check ConsensusADMM.Period48.Coefficient.eta
#check ConsensusADMM.Period48.Coefficient.nu
#check ConsensusADMM.Period48.Coefficient.w
#check ConsensusADMM.Period48.Coefficient.rho
#check ConsensusADMM.Period48.Coefficient.xi
#check ConsensusADMM.Period48.Coefficient.firstNormal
#check ConsensusADMM.Period48.Coefficient.secondNormal
#check ConsensusADMM.Period48.Coefficient.vertex
#check ConsensusADMM.Period48.Coefficient.normal
#check ConsensusADMM.Period48.Coefficient.testVector
#check ConsensusADMM.Period48.Coefficient.supportAtCritical
#check ConsensusADMM.Period48.Coefficient.supportSlope
#check ConsensusADMM.Period48.Coefficient.support_def
#check ConsensusADMM.Period48.Coefficient.supportCyclic
#check ConsensusADMM.Period48.Coefficient.phaseZeroTest_card
#check ConsensusADMM.Period48.Coefficient.supportTest_card
#check ConsensusADMM.Period48.Coefficient.support_affine
#check ConsensusADMM.Period48.Coefficient.firstSlopeBound
#check ConsensusADMM.Period48.Coefficient.secondSlopeBound
#check ConsensusADMM.Period48.Coefficient.firstValueBound
#check ConsensusADMM.Period48.Coefficient.secondValueBound
#check ConsensusADMM.Period48.Coefficient.activeSupport
#check ConsensusADMM.Period48.Coefficient.allSupportsNonneg
#check ConsensusADMM.Period48.Coefficient.support_nonneg_iff_pairing
#check ConsensusADMM.Period48.Coefficient.support_eq_inner
#check (ConsensusADMM.Period48.gramMatrix :
  Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
#check ConsensusADMM.Period48.gammaZero
#check ConsensusADMM.criticalFactor

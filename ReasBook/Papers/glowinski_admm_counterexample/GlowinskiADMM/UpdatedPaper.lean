/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM
public import glowinski_admm_counterexample.GlowinskiADMM.lemma_3_2_reduced
public import glowinski_admm_counterexample.GlowinskiADMM.UpdatedTargets
public import glowinski_admm_counterexample.GlowinskiADMM.UpdatedAssembly
public import glowinski_admm_counterexample.GlowinskiADMM.UpdatedResults
public import glowinski_admm_counterexample.GlowinskiADMM.UnitCircleTiltedValues
public import glowinski_admm_counterexample.ReasLib.ADMM.RefinedEndpoint.DataChecks
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.RefinedConstants
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Symbol
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.DiscountRemoval
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.BernsteinCertificate
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.ConcreteWeights
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.MomentRegrouping
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.CoercivityInterpolation
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.PhaseZero
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.ScaledCycle
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.FourierGeometry
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Period1024
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.DiscountedCoercivity

/-!
Complete updated-paper entry, retaining the previous results and exporting
the strengthened Theorem 2.1, the full unit-circle convergence criterion,
the concrete lower and upper certificates, and the strict endpoint enclosure.
`UpdatedTargets` fixes their statements; `UpdatedResults` supplies the
unconditional main and endpoint theorems.
-/

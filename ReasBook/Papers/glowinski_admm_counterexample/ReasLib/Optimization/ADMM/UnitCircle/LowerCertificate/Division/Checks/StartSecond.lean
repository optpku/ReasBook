/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.Normalization
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.LagData
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.FastForms
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.QuotientData

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Division

set_option maxRecDepth 32768 in
-- Check every exact rational term after the proved finite normalization.
theorem divisionStartSecond :
    normalForm (fastSecond (377 / 200) normalizedLag0) =
      normalForm (laurentMultiply delayNorm startSecondQuotient) := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Division

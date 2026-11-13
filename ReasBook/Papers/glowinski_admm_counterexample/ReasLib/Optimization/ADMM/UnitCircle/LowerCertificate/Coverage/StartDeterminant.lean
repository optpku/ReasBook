/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coverage.Assembly
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant00.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant01.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant02.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant03.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant04.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant05.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant06.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant07.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.StartDeterminant08.Proof

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Coverage

/-- All exact kernel-verified leaf certificates give strict positivity on
the entire closed real frequency interval for the StartDeterminant polynomial. -/
theorem startDeterminant_positive {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 < evaluate Data.StartDeterminant x := by
  exact startDeterminant_positive_of_leaves
    (fun x hx ↦ Certificates.StartDeterminant00.positive (by simpa using hx))
    (fun x hx ↦ Certificates.StartDeterminant01.positive (by simpa using hx))
    (fun x hx ↦ Certificates.StartDeterminant02.positive (by simpa using hx))
    (fun x hx ↦ Certificates.StartDeterminant03.positive (by simpa using hx))
    (fun x hx ↦ Certificates.StartDeterminant04.positive (by simpa using hx))
    (fun x hx ↦ Certificates.StartDeterminant05.positive (by simpa using hx))
    (fun x hx ↦ Certificates.StartDeterminant06.positive (by simpa using hx))
    (fun x hx ↦ Certificates.StartDeterminant07.positive (by simpa using hx))
    (fun x hx ↦ Certificates.StartDeterminant08.positive (by simpa using hx))
    hx

end ADMM.UnitCircle.LowerCertificate.Coverage

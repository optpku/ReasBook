/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coverage.Assembly
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant00.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant01.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant02.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant03.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant04.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant05.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant06.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant07.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant08.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant09.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant10.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant11.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant12.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant13.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant14.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant15.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant16.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant17.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant18.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant19.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant20.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant21.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant22.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.LowerDeterminant23.Proof

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Coverage

/-- All exact kernel-verified leaf certificates give strict positivity on
the entire closed real frequency interval for the LowerDeterminant polynomial. -/
theorem lowerDeterminant_positive {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 < evaluate Data.LowerDeterminant x := by
  exact lowerDeterminant_positive_of_leaves
    (fun x hx ↦ Certificates.LowerDeterminant00.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant01.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant02.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant03.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant04.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant05.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant06.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant07.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant08.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant09.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant10.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant11.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant12.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant13.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant14.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant15.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant16.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant17.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant18.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant19.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant20.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant21.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant22.positive (by simpa using hx))
    (fun x hx ↦ Certificates.LowerDeterminant23.positive (by simpa using hx))
    hx

end ADMM.UnitCircle.LowerCertificate.Coverage

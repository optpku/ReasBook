/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coverage.Assembly
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Leaves.Diagonal00
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal01.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal02.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal03.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal04.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal05.Proof
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal06.Proof

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Coverage

/-- All exact kernel-verified leaf certificates give strict positivity on
the entire closed real frequency interval for the Diagonal polynomial. -/
theorem diagonal_positive {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 < evaluate Data.Diagonal x := by
  exact diagonal_positive_of_leaves
    (fun x hx ↦ Leaves.diagonal00_positive hx)
    (fun x hx ↦ Certificates.Diagonal01.positive (by simpa using hx))
    (fun x hx ↦ Certificates.Diagonal02.positive (by simpa using hx))
    (fun x hx ↦ Certificates.Diagonal03.positive (by simpa using hx))
    (fun x hx ↦ Certificates.Diagonal04.positive (by simpa using hx))
    (fun x hx ↦ Certificates.Diagonal05.positive (by simpa using hx))
    (fun x hx ↦ Certificates.Diagonal06.positive (by simpa using hx))
    hx

end ADMM.UnitCircle.LowerCertificate.Coverage

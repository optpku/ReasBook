/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal04.Data

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal04

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk00 : ∀ i : Fin 8,
    leftCoefficient (i.val + 0) = rightCoefficient (i.val + 0) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk01 : ∀ i : Fin 8,
    leftCoefficient (i.val + 8) = rightCoefficient (i.val + 8) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk02 : ∀ i : Fin 8,
    leftCoefficient (i.val + 16) = rightCoefficient (i.val + 16) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk03 : ∀ i : Fin 8,
    leftCoefficient (i.val + 24) = rightCoefficient (i.val + 24) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk04 : ∀ i : Fin 8,
    leftCoefficient (i.val + 32) = rightCoefficient (i.val + 32) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk05 : ∀ i : Fin 8,
    leftCoefficient (i.val + 40) = rightCoefficient (i.val + 40) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk06 : ∀ i : Fin 8,
    leftCoefficient (i.val + 48) = rightCoefficient (i.val + 48) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk07 : ∀ i : Fin 8,
    leftCoefficient (i.val + 56) = rightCoefficient (i.val + 56) := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal04

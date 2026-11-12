/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal01.Data

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal01

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk08 : ∀ i : Fin 8,
    leftCoefficient (i.val + 64) = rightCoefficient (i.val + 64) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk09 : ∀ i : Fin 8,
    leftCoefficient (i.val + 72) = rightCoefficient (i.val + 72) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk10 : ∀ i : Fin 8,
    leftCoefficient (i.val + 80) = rightCoefficient (i.val + 80) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk11 : ∀ i : Fin 8,
    leftCoefficient (i.val + 88) = rightCoefficient (i.val + 88) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk12 : ∀ i : Fin 8,
    leftCoefficient (i.val + 96) = rightCoefficient (i.val + 96) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk13 : ∀ i : Fin 8,
    leftCoefficient (i.val + 104) = rightCoefficient (i.val + 104) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk14 : ∀ i : Fin 8,
    leftCoefficient (i.val + 112) = rightCoefficient (i.val + 112) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk15 : ∀ i : Fin 8,
    leftCoefficient (i.val + 120) = rightCoefficient (i.val + 120) := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal01

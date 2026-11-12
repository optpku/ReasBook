/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal03.Data

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal03

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk16 : ∀ i : Fin 8,
    leftCoefficient (i.val + 128) = rightCoefficient (i.val + 128) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk17 : ∀ i : Fin 8,
    leftCoefficient (i.val + 136) = rightCoefficient (i.val + 136) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk18 : ∀ i : Fin 8,
    leftCoefficient (i.val + 144) = rightCoefficient (i.val + 144) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk19 : ∀ i : Fin 8,
    leftCoefficient (i.val + 152) = rightCoefficient (i.val + 152) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk20 : ∀ i : Fin 8,
    leftCoefficient (i.val + 160) = rightCoefficient (i.val + 160) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk21 : ∀ i : Fin 8,
    leftCoefficient (i.val + 168) = rightCoefficient (i.val + 168) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk22 : ∀ i : Fin 8,
    leftCoefficient (i.val + 176) = rightCoefficient (i.val + 176) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk23 : ∀ i : Fin 8,
    leftCoefficient (i.val + 184) = rightCoefficient (i.val + 184) := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal03

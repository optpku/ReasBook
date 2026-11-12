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
theorem chunk24 : ∀ i : Fin 8,
    leftCoefficient (i.val + 192) = rightCoefficient (i.val + 192) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk25 : ∀ i : Fin 8,
    leftCoefficient (i.val + 200) = rightCoefficient (i.val + 200) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk26 : ∀ i : Fin 8,
    leftCoefficient (i.val + 208) = rightCoefficient (i.val + 208) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk27 : ∀ i : Fin 8,
    leftCoefficient (i.val + 216) = rightCoefficient (i.val + 216) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk28 : ∀ i : Fin 8,
    leftCoefficient (i.val + 224) = rightCoefficient (i.val + 224) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk29 : ∀ i : Fin 8,
    leftCoefficient (i.val + 232) = rightCoefficient (i.val + 232) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk30 : ∀ i : Fin 8,
    leftCoefficient (i.val + 240) = rightCoefficient (i.val + 240) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
-- Eight exact integer coefficient checks keep kernel memory bounded.
theorem chunk31 : ∀ i : Fin 8,
    leftCoefficient (i.val + 248) = rightCoefficient (i.val + 248) := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Certificates.Diagonal01

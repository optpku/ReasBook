/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Data.Diagonal00Context

@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

namespace ADMM.UnitCircle.LowerCertificate.Leaves

theorem diagonal00Chunk13 : ∀ i : Fin 8,
    diagonalAffine00.getD (i.val + 104) 0 = diagonalExpansion00.getD (i.val + 104) 0 := by
  decide +kernel

end ADMM.UnitCircle.LowerCertificate.Leaves

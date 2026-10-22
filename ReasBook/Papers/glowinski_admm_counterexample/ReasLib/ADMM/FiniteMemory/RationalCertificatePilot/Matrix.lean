/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixAssembly
public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixData

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction.Pilot

open MatrixAssembly

/-- The final lower-matrix comparison only needs the independently checked
storage, interpolation weights, and finite entry arithmetic. -/
theorem lowerMatrix_eq_of_layers
    (hP : storageMatrix caseData .upper = literalP)
    (hmu : ∀ b a d, reconstructMu caseData b a d = literalMu b a d)
    (hentries : ∀ i j : Fin 9 × Fin 2,
      (literalP i j + literalP j i) / 2 -
        (∑ b : Block, ∑ a : Option (Fin 8), ∑ d : Option (Fin 8),
          literalMu b a d * interpolationEntry (endpointGamma caseData .upper) b a d i j) -
        caseData.zeta * currentPairMatrix 8 i j = candidateK i j) :
    lowerMatrix caseData .upper = candidateK := by
  ext i j
  rw [lowerMatrix_factored, hP]
  simp_rw [hmu]
  exact hentries i j

/-- Replacing the supply matrix by its checked literal is sufficient for the
constant-mode action layer. -/
theorem action_eq_of_layers
    (hQ : supplyMatrix caseData (endpointGamma caseData .upper) = literalQ)
    (haction : literalQ * constantModes 10 = literalAction) :
    supplyConstantModes caseData (endpointGamma caseData .upper) = literalAction := by
  rw [supplyConstantModes, hQ, haction]

/-- Checked constant-mode values reduce the prefix layer to small finite sums. -/
theorem prefix_eq_of_layers
    (hact : supplyConstantModes caseData (endpointGamma caseData .upper) = literalAction)
    (hprefix : ∀ i : Fin 9 × Fin 2, ∀ j : Fin 2,
      -(∑ t : Fin 10, if t ≤ i.1.castSucc then literalAction (t, i.2) j else 0) =
        literalPrefix i j) :
    cumulativePrefix caseData (endpointGamma caseData .upper) = literalPrefix := by
  ext i j
  rw [cumulativePrefix_apply, hact]
  exact hprefix i j

/-- The off-diagonal layer only uses the checked prefix and supplied triangle. -/
theorem offDiagonal_eq_of_layers
    (hprefix : cumulativePrefix caseData (endpointGamma caseData .upper) = literalPrefix)
    (hA : upperTriangleMatrix caseData .upper = literalA)
    (hT : ∀ i : Fin 8 × Fin 2, ∀ j : Fin 2,
      literalPrefix (i.1.castSucc, i.2) j - (literalA * constantModes 8) i j = literalT i j) :
    storageOffDiagonal caseData .upper = literalT := by
  ext i j
  rw [storageOffDiagonal_apply, hprefix, hA]
  exact hT i j

/-- The terminal layer uses only the checked prefix and off-diagonal block. -/
theorem terminal_eq_of_layers
    (hprefix : cumulativePrefix caseData (endpointGamma caseData .upper) = literalPrefix)
    (hT : storageOffDiagonal caseData .upper = literalT)
    (hW : ∀ i j : Fin 2,
      literalPrefix (Fin.last 8, i) j -
        (∑ k : Fin 8 × Fin 2, literalT k i * constantModes 8 k j) = literalW i j) :
    storageTerminal caseData .upper = literalW := by
  ext i j
  rw [storageTerminal_apply, hprefix, hT]
  exact hW i j

/-- The storage layer is a block lookup after the three constituent identities. -/
theorem storage_eq_of_layers
    (hA : upperTriangleMatrix caseData .upper = literalA)
    (hT : storageOffDiagonal caseData .upper = literalT)
    (hW : storageTerminal caseData .upper = literalW)
    (hP : ∀ i j : Fin 9 × Fin 2,
      (if hi : i.1 < 8 then
        if hj : j.1 < 8 then literalA (⟨i.1, hi⟩, i.2) (⟨j.1, hj⟩, j.2)
        else literalT (⟨i.1, hi⟩, i.2) j.2
      else if hj : j.1 < 8 then literalT (⟨j.1, hj⟩, j.2) i.2
      else literalW i.2 j.2) = literalP i j) :
    storageMatrix caseData .upper = literalP := by
  ext i j
  simp only [storageMatrix, hA, hT, hW]
  exact hP i j

end ADMM.FiniteMemory.Reconstruction.Pilot

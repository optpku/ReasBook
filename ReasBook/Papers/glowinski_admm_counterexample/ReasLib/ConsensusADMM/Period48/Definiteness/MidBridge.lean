module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.Core

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

/-- A specialization whose memoization keys do not carry the large literal
midpoint matrix as a higher-order argument. -/
def midEntry : ℕ → ℕ → ℕ → ℤ
  | 0, i, j => stageMid (Fin.ofNat 96 i) (Fin.ofNat 96 j)
  | k + 1, i, j =>
    let pivot := (k + 48) % 96
    let previous := (k + 48 - 1) % 96
    if pivot < i ∧ pivot < j then
      (midEntry k pivot pivot * midEntry k i j -
        midEntry k i pivot * midEntry k pivot j) /
          (if k + 48 = 0 then 1 else midEntry k previous previous)
    else midEntry k i j

theorem midEntry_eq_keyed (n i j : ℕ) :
    midEntry n i j = keyedEntry 48 stageMid n i j := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [midEntry, keyedEntry, ih]

def midPivots (n : ℕ) : List ℤ :=
  (List.range n).map fun k ↦ midEntry k ((k + 48) % 96) ((k + 48) % 96)

theorem midPivots_eq_runFromAt (n : ℕ) :
    midPivots n = (runFromAt 48 stageMid n).2 := by
  rw [← keyedPivots_eq_runFromAt]
  simp only [midPivots, keyedPivots, midEntry_eq_keyed]

end ConsensusADMM.Period48.FractionFree

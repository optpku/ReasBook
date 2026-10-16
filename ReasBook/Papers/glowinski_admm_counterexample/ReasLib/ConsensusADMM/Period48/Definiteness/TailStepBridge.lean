module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TailBridge
public import Mathlib.Data.List.GetD

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

/-- One elimination step on an explicit integer row. The input is a literal
certificate row, so evaluating this step does not unfold earlier stages. -/
def tailRowStep (n i : ℕ) (row : List ℤ) : List ℤ :=
  List.ofFn fun j : Fin 96 =>
    if n < i ∧ n < j.val then
      (stageMid (Fin.ofNat 96 n) (Fin.ofNat 96 n) * row.getD j.val 0 -
        stageMid (Fin.ofNat 96 n) (Fin.ofNat 96 i) *
          stageMid (Fin.ofNat 96 n) j) /
        (if n = 0 then 1 else stageMid (Fin.ofNat 96 (n - 1)) (Fin.ofNat 96 (n - 1)))
    else row.getD j.val 0

lemma ofFn_getD (f : Fin 96 → ℤ) (j : Fin 96) :
    (List.ofFn f).getD j.val 0 = f j := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn]

/-- A local row certificate advances a previously established stage. -/
theorem tailRow_succ_of_step (n i : ℕ) (row next : List ℤ)
    (hrow : List.ofFn (fun j : Fin 96 => tailEntry n i j.val) = row)
    (hstep : tailRowStep n i row = next) :
    List.ofFn (fun j : Fin 96 => tailEntry (n + 1) i j.val) = next := by
  rw [← hstep, ← hrow]
  unfold tailRowStep
  congr 1
  funext j
  simp only [tailEntry, ofFn_getD, Fin.ofNat_eq_cast, Fin.cast_val_eq_self]

end ConsensusADMM.Period48.FractionFree

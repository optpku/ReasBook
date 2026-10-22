/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.TailBridge

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

/-- Pointwise finite row operations can be checked as literal list operations. -/
theorem zipWith_ofFn_rows {n : ℕ} (op : ℤ → ℤ → ℤ) (f g : Fin n → ℤ) :
    List.zipWith op (List.ofFn f) (List.ofFn g) =
      List.ofFn (fun j => op (f j) (g j)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zipWith, List.getElem_ofFn]

/-- A certificate step uses closed integer coefficients and two explicit rows.
Its previous row is already proved, so no earlier arithmetic is recomputed. -/
theorem tailTrailingRow_succ (n i : ℕ) (hn : n < 48) (hi : 48 ≤ i)
    (row right next : List ℤ) (p a d : ℤ)
    (hrow : List.ofFn (fun j : Fin 48 => tailEntry n i (j.val + 48)) = row)
    (hp : stageMid (Fin.ofNat 96 n) (Fin.ofNat 96 n) = p)
    (ha : stageMid (Fin.ofNat 96 n) (Fin.ofNat 96 i) = a)
    (hd : (if n = 0 then 1 else
      stageMid (Fin.ofNat 96 (n - 1)) (Fin.ofNat 96 (n - 1))) = d)
    (hright : List.ofFn (fun j : Fin 48 =>
      stageMid (Fin.ofNat 96 n) (Fin.ofNat 96 (j.val + 48))) = right)
    (hstep : List.zipWith (fun x b => (p * x - a * b) / d) row right = next) :
    List.ofFn (fun j : Fin 48 => tailEntry (n + 1) i (j.val + 48)) = next := by
  rw [← hstep, ← hrow, ← hright, zipWith_ofFn_rows]
  congr 1
  funext j
  have hij : n < i ∧ n < j.val + 48 := by omega
  simp only [tailEntry, if_pos hij, hp, ha, hd]

/-- Symmetry supplies the leading columns; only the trailing row needs an
arithmetic recurrence certificate. -/
theorem stageMidTailRow_of_halves (i : ℕ) (hi : 48 ≤ i) (hi96 : i < 96)
    (hleft : ∀ j : Fin 48,
      stageMid ⟨i, hi96⟩ ⟨j.val, by omega⟩ =
        stageMid ⟨j.val, by omega⟩ ⟨i, hi96⟩)
    (hright : List.ofFn (fun j : Fin 48 => tailEntry 48 i (j.val + 48)) =
      List.ofFn (fun j : Fin 48 =>
        stageMid ⟨i, hi96⟩ ⟨j.val + 48, by omega⟩)) :
    (runFromAt 0 j0 48).1 ⟨i, hi96⟩ = stageMid ⟨i, hi96⟩ := by
  funext j
  by_cases hj : j.val < 48
  · rw [runFromAt_symm]
    exact (stageMidLeadingRows ⟨j.val, hj⟩ ⟨i, hi96⟩).trans (hleft ⟨j.val, hj⟩).symm
  · let k : Fin 48 := ⟨j.val - 48, by omega⟩
    have hidx : j = (⟨k.val + 48, by omega⟩ : Fin 96) := Fin.ext (by dsimp [k]; omega)
    rw [hidx, ← tailEntry_eq_runFromAt stageMidLeadingRows 48 (by omega)]
    exact congrFun (List.ofFn_inj.mp hright) k

end ConsensusADMM.Period48.FractionFree

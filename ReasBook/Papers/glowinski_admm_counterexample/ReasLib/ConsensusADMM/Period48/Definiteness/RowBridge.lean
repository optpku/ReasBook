/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.FirstPivots

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

/-- Equality of finite integer row lists proves equality of the corresponding
lists of row functions. This avoids deciding equality at a function type. -/
theorem rows_eq_of_entryLists_eq {m n : ℕ} (f g : Fin m → Fin n → ℤ)
    (h : List.ofFn (fun i => List.ofFn (f i)) =
      List.ofFn (fun i => List.ofFn (g i))) : List.ofFn f = List.ofFn g := by
  apply List.ofFn_inj.mpr
  funext i
  exact List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp h) i)

/-- Entries stop changing once either coordinate reaches the pivot index.
Truncating the recursion at that index avoids traversing inert later stages. -/
theorem keyedEntry_min (M : Matrix (Fin 96) (Fin 96) ℤ)
    (n i j : ℕ) (hn : n ≤ 96) :
    keyedEntry 0 M n i j = keyedEntry 0 M (min n (min i j)) i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases h : n + 1 ≤ min i j
    · rw [Nat.min_eq_left h]
    · have hle : min i j ≤ n := by omega
      have hnot : ¬ (n < i ∧ n < j) := by omega
      have hstep : keyedEntry 0 M (n + 1) i j = keyedEntry 0 M n i j := by
        simp only [keyedEntry, Nat.add_zero, Nat.mod_eq_of_lt (show n < 96 by omega),
          hnot, if_false]
      rw [hstep, ih (by omega), Nat.min_eq_right hle,
        Nat.min_eq_right (show min i j ≤ n + 1 by omega)]

/-- Whole-matrix form of the truncated entry recurrence. -/
theorem runFromAt_fst_eq_keyed_min (M : Matrix (Fin 96) (Fin 96) ℤ)
    (n : ℕ) (hn : n ≤ 96) : (runFromAt 0 M n).1 = fun i j ↦
      keyedEntry 0 M (min n (min i.val j.val)) i.val j.val := by
  ext i j
  rw [runFromAt_fst_eq_keyed]
  exact keyedEntry_min M n i.val j.val hn

end ConsensusADMM.Period48.FractionFree

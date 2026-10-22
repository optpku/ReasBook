/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Definiteness.MidpointRows2

@[expose] public section

namespace ConsensusADMM.Period48.FractionFree

/-- The first three certified blocks provide all leading forty-eight rows. -/
lemma stageMidLeadingRow (c : Fin 3) (k : Fin 16) :
    (fun j : Fin 96 => (runFromAt 0 j0 48).1 ⟨k.val + 16 * c.val, by omega⟩ j) =
      (fun j : Fin 96 => stageMid ⟨k.val + 16 * c.val, by omega⟩ j) := by
  fin_cases c
  · exact congrFun (List.ofFn_inj.mp stageMidBlockFst_checked) k
  · exact congrFun (List.ofFn_inj.mp stageMidBlockSnd_checked) k
  · exact congrFun (List.ofFn_inj.mp stageMidBlockThird_checked) k

lemma stageMidLeadingRows (k : Fin 48) (j : Fin 96) :
    (runFromAt 0 j0 48).1 ⟨k.val, by omega⟩ j = stageMid ⟨k.val, by omega⟩ j := by
  have hdecomp : (⟨k.val, by omega⟩ : Fin 96) =
      (⟨k.val % 16 + 16 * (k.val / 16), by omega⟩ : Fin 96) :=
    Fin.ext (Nat.mod_add_div k.val 16).symm
  rw [hdecomp]
  exact congrFun (stageMidLeadingRow ⟨k.val / 16, by omega⟩ ⟨k.val % 16, by omega⟩) j

/-- Symmetry is preserved by every fraction-free elimination update. -/
theorem runFromAt_symm (n : ℕ) (i j : Fin 96) :
    (runFromAt 0 j0 n).1 i j = (runFromAt 0 j0 n).1 j i := by
  induction n generalizing i j with
  | zero => exact j0_isSymm.apply j i
  | succ n ih =>
    simp only [runFromAt, Nat.add_zero, bareissStep]
    by_cases h : Fin.ofNat 96 n < i ∧ Fin.ofNat 96 n < j
    · have hflip : Fin.ofNat 96 n < j ∧ Fin.ofNat 96 n < i := h.symm
      have hoff : (runFromAt 0 j0 n).1 i (Fin.ofNat 96 n) *
          (runFromAt 0 j0 n).1 (Fin.ofNat 96 n) j =
          (runFromAt 0 j0 n).1 j (Fin.ofNat 96 n) *
            (runFromAt 0 j0 n).1 (Fin.ofNat 96 n) i := by
        rw [ih i (Fin.ofNat 96 n), ih (Fin.ofNat 96 n) j]
        exact mul_comm _ _
      simp only [if_pos h, if_pos hflip, ih i j, hoff]
    · have hflip : ¬ (Fin.ofNat 96 n < j ∧ Fin.ofNat 96 n < i) := by tauto
      simp only [if_neg h, if_neg hflip, ih i j]

/-- Once a coordinate is behind the pivot, later stages preserve the entry. -/
theorem runFromAt_entry_frozen (n m : ℕ) (hnm : n ≤ m) (hm : m ≤ 96)
    (i j : Fin 96) (hij : i.val ≤ n ∨ j.val ≤ n) :
    (runFromAt 0 j0 n).1 i j = (runFromAt 0 j0 m).1 i j := by
  rw [runFromAt_fst_eq_keyed_min j0 n (by omega),
    runFromAt_fst_eq_keyed_min j0 m hm]
  change keyedEntry 0 j0 (min n (min i.val j.val)) i.val j.val =
    keyedEntry 0 j0 (min m (min i.val j.val)) i.val j.val
  have hmin : min n (min i.val j.val) = min m (min i.val j.val) := by omega
  rw [hmin]

/-- Previously certified leading rows supply every elimination coefficient. -/
theorem runFromAt_coefficient
    (hrows : ∀ (k : Fin 48) (j : Fin 96),
      (runFromAt 0 j0 48).1 ⟨k.val, by omega⟩ j = stageMid ⟨k.val, by omega⟩ j)
    (n k : ℕ) (hn : n ≤ 48) (hk : k < 48) (hkn : k ≤ n) (j : Fin 96) :
    (runFromAt 0 j0 n).1 ⟨k, by omega⟩ j = stageMid ⟨k, by omega⟩ j := by
  exact (runFromAt_entry_frozen n 48 hn (by omega) ⟨k, by omega⟩ j
    (Or.inl hkn)).trans (hrows ⟨k, hk⟩ j)

/-- The remaining block evolves using the already recorded leading rows. -/
def tailEntry : ℕ → ℕ → ℕ → ℤ
  | 0, i, j => j0 (Fin.ofNat 96 i) (Fin.ofNat 96 j)
  | n + 1, i, j =>
    if n < i ∧ n < j then
      (stageMid (Fin.ofNat 96 n) (Fin.ofNat 96 n) * tailEntry n i j -
        stageMid (Fin.ofNat 96 n) (Fin.ofNat 96 i) *
          stageMid (Fin.ofNat 96 n) (Fin.ofNat 96 j)) /
        (if n = 0 then 1 else stageMid (Fin.ofNat 96 (n - 1)) (Fin.ofNat 96 (n - 1)))
    else tailEntry n i j

theorem tailEntry_eq_runFromAt
    (hrows : ∀ (k : Fin 48) (j : Fin 96),
      (runFromAt 0 j0 48).1 ⟨k.val, by omega⟩ j = stageMid ⟨k.val, by omega⟩ j)
    (n : ℕ) (hn : n ≤ 48) (i j : Fin 96) :
    tailEntry n i.val j.val = (runFromAt 0 j0 n).1 i j := by
  induction n generalizing i j with
  | zero => simp [tailEntry, runFromAt, Fin.ofNat_eq_cast]
  | succ n ih =>
    have hn48 : n < 48 := by omega
    have hn96 : n < 96 := by omega
    have hpk : Fin.ofNat 96 n = (⟨n, hn96⟩ : Fin 96) := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt hn96]
    have hcoef (j : Fin 96) := runFromAt_coefficient hrows n n (by omega) hn48 le_rfl j
    have hprev : (if n = 0 then 1 else
        (runFromAt 0 j0 n).1 (Fin.ofNat 96 (n - 1)) (Fin.ofNat 96 (n - 1))) =
        (if n = 0 then 1 else stageMid (Fin.ofNat 96 (n - 1)) (Fin.ofNat 96 (n - 1))) := by
      split_ifs with hzero
      · rfl
      · have hp : n - 1 < 96 := by omega
        have heq : Fin.ofNat 96 (n - 1) = (⟨n - 1, hp⟩ : Fin 96) := by
          apply Fin.ext
          simp [Fin.ofNat, Nat.mod_eq_of_lt hp]
        rw [heq]
        exact runFromAt_coefficient hrows n (n - 1) (by omega) (by omega) (by omega) _
    have hi : Fin.ofNat 96 i.val = i := by simp [Fin.ofNat_eq_cast]
    have hj : Fin.ofNat 96 j.val = j := by simp [Fin.ofNat_eq_cast]
    simp only [tailEntry, runFromAt, Nat.add_zero, bareissStep]
    simp only [ih (by omega) i j, hprev, hi, hj, hpk]
    simp only [runFromAt_symm n i ⟨n, hn96⟩, hcoef i, hcoef j, hcoef ⟨n, hn96⟩]
    rfl

/-- Frozen positions require no further tail updates. -/
theorem tailEntry_min (n i j : ℕ) :
    tailEntry n i j = tailEntry (min n (min i j)) i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases h : n + 1 ≤ min i j
    · rw [Nat.min_eq_left h]
    · have hle : min i j ≤ n := by omega
      have hnot : ¬ (n < i ∧ n < j) := by omega
      have hstep : tailEntry (n + 1) i j = tailEntry n i j := by
        simp only [tailEntry, hnot, if_false]
      rw [hstep, ih, Nat.min_eq_right hle,
        Nat.min_eq_right (show min i j ≤ n + 1 by omega)]

theorem runFromAt_fst_eq_tail_min
    (hrows : ∀ (k : Fin 48) (j : Fin 96),
      (runFromAt 0 j0 48).1 ⟨k.val, by omega⟩ j = stageMid ⟨k.val, by omega⟩ j)
    (n : ℕ) (hn : n ≤ 48) : (runFromAt 0 j0 n).1 = fun i j ↦
      tailEntry (min n (min i.val j.val)) i.val j.val := by
  ext i j
  rw [← tailEntry_eq_runFromAt hrows n hn i j]
  exact tailEntry_min n i.val j.val

end ConsensusADMM.Period48.FractionFree

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_2

-- Declarations for this item will be appended below by the statement pipeline.

variable {n k p : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
open scoped CoordinateSubspace

-- Proof sketch: unfold `fk` on both sides. If `x ∈ coordinateSubspace k n`,
-- then `mem_coordinateSubspace_iff` says that every coordinate with index at least `k` vanishes,
-- so the extra adjacent-difference terms and tail terms introduced when passing from `f_k` to
-- `f_{k+p}` are all zero, while the shared terms and the linear term `-x^{(1)}` are unchanged.
/-- Lemma 4.3.2: if `x` lies in the coordinate subspace `ℝ^{k,n}`, then enlarging the hard-instance
index from `k` to `k + p` does not change the value of the textbook function `f_k`. -/
theorem fk_add_eq_of_mem_coordinateSubspace
    (hkpn : k + p ≤ n) {x : E}
    (hx : x ∈ ℝ^{k,n}) :
    fk hkpn x =
      fk (le_trans (Nat.le_add_right k p) hkpn) x := by
  have hkn : k ≤ n := le_trans (Nat.le_add_right k p) hkpn
  by_cases hp0 : p = 0
  · subst p
    exact congrArg (fun h : k ≤ n ↦ fk h x) (Subsingleton.elim _ _)
  have hp : 0 < p := Nat.pos_of_ne_zero hp0
  have hx0 := mem_coordinateSubspace_iff.mp hx
  have hx_tail {j : ℕ} (hkj : k ≤ j) (hjn : j < n) : x ⟨j, hjn⟩ = 0 :=
    hx0 ⟨j, hjn⟩ hkj
  by_cases hk : 0 < k
  · have hkppos : 0 < k + p := Nat.add_pos_left hk p
    rw [fk_apply, fk_apply]
    simp [hk, hkppos]
    let tailk : ℕ → ℝ := fun j ↦ if hj : k + j < n then |x ⟨k + j, hj⟩| ^ (3 : ℕ) else 0
    let tailkp : ℕ → ℝ := fun j ↦
      if hj : k + p + j < n then |x ⟨k + p + j, hj⟩| ^ (3 : ℕ) else 0
    let diff : ℕ → ℝ := fun j ↦
      if hj : j + 1 < n then |x ⟨j, Nat.lt_of_succ_lt hj⟩ - x ⟨j + 1, hj⟩| ^ (3 : ℕ) else 0
    have htailk_left :
        (∑ i : Fin (n - k), |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ)) =
          ∑ i : Fin (n - k), tailk i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi' : k + (i : ℕ) < n := by
        omega
      have hcast : (Fin.natAdd_castLEEmb (Nat.sub_le n k) i : Fin n) = ⟨k + i, hi'⟩ := by
        ext
        simp [Fin.natAdd_castLEEmb]
        omega
      simp [tailk, hi', hcast]
    have htailk :
        (∑ i : Fin (n - k), |x (Fin.natAdd_castLEEmb (Nat.sub_le n k) i)| ^ (3 : ℕ)) = 0 := by
      rw [htailk_left]
      rw [show (∑ i : Fin (n - k), tailk i) = ∑ j ∈ Finset.range (n - k), tailk j by
        simpa using (Fin.sum_univ_eq_sum_range tailk (n - k))]
      apply Finset.sum_eq_zero
      intro j hj
      have hjlt : k + j < n := by
        have : j < n - k := Finset.mem_range.mp hj
        omega
      have hxj : x ⟨k + j, hjlt⟩ = 0 := hx_tail (Nat.le_add_right k j) hjlt
      simp [tailk, hjlt, hxj]
    have htailkp_left :
        (∑ i : Fin (n - (k + p)), |x (Fin.natAdd_castLEEmb (Nat.sub_le n (k + p)) i)| ^
          (3 : ℕ)) =
          ∑ i : Fin (n - (k + p)), tailkp i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi' : k + p + (i : ℕ) < n := by
        omega
      have hcast : (Fin.natAdd_castLEEmb (Nat.sub_le n (k + p)) i : Fin n) = ⟨k + p + i, hi'⟩ := by
        ext
        simp [Fin.natAdd_castLEEmb]
        omega
      simp [tailkp, hi', hcast]
    have htailkp :
        (∑ i : Fin (n - (k + p)), |x (Fin.natAdd_castLEEmb (Nat.sub_le n (k + p)) i)| ^
          (3 : ℕ)) = 0 := by
      rw [htailkp_left]
      rw [show (∑ i : Fin (n - (k + p)), tailkp i) = ∑ j ∈ Finset.range (n - (k + p)), tailkp j by
        simpa using (Fin.sum_univ_eq_sum_range tailkp (n - (k + p)))]
      apply Finset.sum_eq_zero
      intro j hj
      have hjlt : k + p + j < n := by
        have : j < n - (k + p) := Finset.mem_range.mp hj
        omega
      have hxj : x ⟨k + p + j, hjlt⟩ = 0 := by
        refine hx_tail ?_ hjlt
        omega
      simp [tailkp, hjlt, hxj]
    have hdiff_small_left :
        (∑ i : Fin (k - 1),
          |x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ)) =
          ∑ i : Fin (k - 1), diff i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      change |x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ) = diff i
      have hi' : (i : ℕ) + 1 < n := by
        omega
      have hleft : (Fin.castLE (by omega) i : Fin n) = ⟨i, Nat.lt_of_succ_lt hi'⟩ := by
        ext
        simp
      have hright : (Fin.castLE (by omega) i.succ : Fin n) = ⟨i + 1, hi'⟩ := by
        ext
        simp
      simp [diff, hleft, hright, hi']
    have hdiff_small :
        (∑ i : Fin (k - 1),
          |x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ)) =
          ∑ j ∈ Finset.range (k - 1), diff j := by
      rw [hdiff_small_left]
      simpa [diff] using (Fin.sum_univ_eq_sum_range diff (k - 1))
    have hdiff_large_left :
        (∑ i : Fin (k + p - 1),
          |x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ)) =
          ∑ i : Fin (k + p - 1), diff i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      change |x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ) = diff i
      have hi' : (i : ℕ) + 1 < n := by
        omega
      have hleft : (Fin.castLE (by omega) i : Fin n) = ⟨i, Nat.lt_of_succ_lt hi'⟩ := by
        ext
        simp
      have hright : (Fin.castLE (by omega) i.succ : Fin n) = ⟨i + 1, hi'⟩ := by
        ext
        simp
      simp [diff, hleft, hright, hi']
    have hdiff_large :
        (∑ i : Fin (k + p - 1),
          |x (Fin.castLE (by omega) i) - x (Fin.castLE (by omega) i.succ)| ^ (3 : ℕ)) =
          ∑ j ∈ Finset.range (k + p - 1), diff j := by
      rw [hdiff_large_left]
      simpa [diff] using (Fin.sum_univ_eq_sum_range diff (k + p - 1))
    have hsplit :
        ∑ j ∈ Finset.range (k + p - 1), diff j =
          ∑ j ∈ Finset.range (k - 1), diff j + ∑ j ∈ Finset.Ico (k - 1) (k + p - 1), diff j := by
      exact (Finset.sum_range_add_sum_Ico diff (show k - 1 ≤ k + p - 1 by
        omega)).symm
    have hdiff_km1 : diff (k - 1) = |x ⟨k - 1, by omega⟩| ^ (3 : ℕ) := by
      have hklt : k < n := by
        omega
      have hxk : x ⟨k, hklt⟩ = 0 := hx_tail le_rfl hklt
      have hsame : k - 1 + 1 = k := by
        omega
      simp [diff, hsame, hklt, hxk]
    have hrest_zero : ∑ j ∈ Finset.Ico k (k + p - 1), diff j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjk : k ≤ j := (Finset.mem_Ico.mp hj).1
      have hjlt : j + 1 < n := by
        have hjup : j < k + p - 1 := (Finset.mem_Ico.mp hj).2
        omega
      have hxj : x ⟨j, by omega⟩ = 0 := hx_tail hjk (by omega)
      have hxj1 : x ⟨j + 1, hjlt⟩ = 0 := by
        refine hx_tail ?_ hjlt
        omega
      simp [diff, hjlt, hxj, hxj1]
    have hextra :
        ∑ j ∈ Finset.Ico (k - 1) (k + p - 1), diff j = |x ⟨k - 1, by omega⟩| ^ (3 : ℕ) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (show k - 1 < k + p - 1 by
        omega) diff]
      have hrest_zero' : ∑ j ∈ Finset.Ico (k - 1 + 1) (k + p - 1), diff j = 0 := by
        simpa [show k - 1 + 1 = k by
          omega] using hrest_zero
      simpa [hdiff_km1] using hrest_zero'
    have hterm_small : |x (Fin.castLE (by omega) (Fin.last (k - 1)))| ^ (3 : ℕ) =
        |x ⟨k - 1, by omega⟩| ^ (3 : ℕ) := by
      have hlast : (Fin.castLE (by omega) (Fin.last (k - 1)) : Fin n) = ⟨k - 1, by omega⟩ := by
        ext
        simp
      simp [hlast]
    have hterm_large : |x (Fin.castLE (by omega) (Fin.last (k + p - 1)))| ^ (3 : ℕ) = 0 := by
      have hlast :
          (Fin.castLE (by omega) (Fin.last (k + p - 1)) : Fin n) = ⟨k + p - 1, by omega⟩ := by
        ext
        simp
      have hxlast : x ⟨k + p - 1, by omega⟩ = 0 := by
        refine hx_tail ?_ (by omega)
        omega
      simp [hlast, hxlast]
    rw [hdiff_large, hdiff_small, htailkp, htailk, hsplit, hextra, hterm_small, hterm_large]
    ring_nf
    congr 1
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    have hxzero : x = 0 := by
      ext i
      exact hx0 i (Nat.zero_le i.1)
    simp [fk_apply, hxzero]

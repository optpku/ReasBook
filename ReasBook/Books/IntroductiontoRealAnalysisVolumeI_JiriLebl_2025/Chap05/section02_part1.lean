/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap02.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap03.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section01

open Filter Topology
open scoped Matrix
open scoped BigOperators
open scoped Pointwise

section Chap05
section Section02

/-- A three-point partition of `[a, c]` with an interior point `b`. -/
lemma intervalPartition_three_points {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    ∃ P : IntervalPartition a c, b ∈ Set.range P.points := by
  classical
  let P : IntervalPartition a c :=
    { n := 2
      points := ![a, b, c]
      mono := by
        refine (Fin.strictMono_iff_lt_succ (f := ![a, b, c])).2 ?_
        intro i
        fin_cases i <;> simp [hab, hbc]
      left_eq := by simp
      right_eq := by simp }
  refine ⟨P, ?_⟩
  · refine ⟨1, by simp [P]⟩

/-- Any partition of `[a, c]` admits a refinement that includes `b`. -/
lemma intervalPartition_refine_with_point {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (P : IntervalPartition a c) :
    ∃ Q : IntervalPartition a c,
      IntervalPartition.IsRefinement P Q ∧ b ∈ Set.range Q.points := by
  classical
  rcases intervalPartition_three_points (a := a) (b := b) (c := c) hab hbc with ⟨P0, hb⟩
  rcases intervalPartition_common_refinement (a := a) (b := c) P P0 with ⟨Q, hPQ, hP0Q⟩
  refine ⟨Q, hPQ, ?_⟩
  exact hP0Q hb

/-- A uniform partition of `[a, b]` with mesh smaller than `δ`. -/
lemma intervalPartition_small_delta {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ P : IntervalPartition a b, ∀ i : Fin P.n, P.delta i < δ := by
  classical
  have hbapos : 0 < b - a := sub_pos.mpr hab
  have hpos : 0 < δ / (b - a) := by
    exact div_pos hδ hbapos
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hpos
  let N : ℕ := n + 1
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.succ_pos n)
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show (N : ℕ) ≠ 0 by simp [N])
  have hstep_lt : (b - a) / (N : ℝ) < δ := by
    have hn' : 1 / (N : ℝ) < δ / (b - a) := by
      simpa [N] using hn
    have hmul := mul_lt_mul_of_pos_left hn' hbapos
    have hba_ne : (b - a) ≠ 0 := by linarith
    calc
      (b - a) / (N : ℝ) = (b - a) * (1 / (N : ℝ)) := by
        simp [div_eq_mul_inv, mul_comm]
      _ < (b - a) * (δ / (b - a)) := hmul
      _ = δ := by
        field_simp [hba_ne]
  let P : IntervalPartition a b :=
    { n := N
      points := fun i : Fin (N + 1) => a + (i : ℝ) * ((b - a) / (N : ℝ))
      mono := by
        refine (Fin.strictMono_iff_lt_succ (f := fun i : Fin (N + 1) =>
          a + (i : ℝ) * ((b - a) / (N : ℝ)))).2 ?_
        intro i
        have hi : (i : ℝ) < (i.succ : ℝ) := by
          exact_mod_cast (Fin.castSucc_lt_succ (i := i))
        have hstep_pos : 0 < (b - a) / (N : ℝ) := by
          exact div_pos hbapos hNpos
        have hmul :
            (i : ℝ) * ((b - a) / (N : ℝ)) <
              (i.succ : ℝ) * ((b - a) / (N : ℝ)) :=
          mul_lt_mul_of_pos_right hi hstep_pos
        simpa using (add_lt_add_left hmul a)
      left_eq := by
        simp
      right_eq := by
        calc
          a + (N : ℝ) * ((b - a) / (N : ℝ)) = a + (b - a) := by
            simp [div_eq_mul_inv, hNne, mul_left_comm]
          _ = b := by ring }
  have hdelta : ∀ i : Fin P.n, P.delta i = (b - a) / (N : ℝ) := by
    intro i
    have :
        a + ((i : ℝ) + 1) * ((b - a) / (N : ℝ)) -
          (a + (i : ℝ) * ((b - a) / (N : ℝ)))
          = (b - a) / (N : ℝ) := by
      ring
    simpa [IntervalPartition.delta, P, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm,
      add_assoc] using this
  refine ⟨P, ?_⟩
  intro i
  simpa [hdelta i] using hstep_lt

/-- Restrict lower/upper Darboux integrals to partitions containing a point. -/
lemma darbouxIntegral_restrict_to_partitions_with_point {a b c : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hbc : b < c)
    (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a c, |f x| ≤ M) :
    lowerDarbouxIntegral f a c =
        sSup (Set.range (fun P :
          {P : IntervalPartition a c // b ∈ Set.range P.points} =>
            lowerDarbouxSum f P.1)) ∧
      upperDarbouxIntegral f a c =
        sInf (Set.range (fun P :
          {P : IntervalPartition a c // b ∈ Set.range P.points} =>
            upperDarbouxSum f P.1)) := by
  classical
  rcases hbound with ⟨M, hM⟩
  have hbound' : ∃ M : ℝ, ∀ x ∈ Set.Icc a c, |f x| ≤ M := ⟨M, hM⟩
  have hmin : ∀ x ∈ Set.Icc a c, -M ≤ f x := by
    intro x hx
    exact (abs_le.mp (hM x hx)).1
  have hmax : ∀ x ∈ Set.Icc a c, f x ≤ M := by
    intro x hx
    exact (abs_le.mp (hM x hx)).2
  have hac : a ≤ c := le_trans (le_of_lt hab) (le_of_lt hbc)
  let S : Set ℝ := Set.range (fun P : IntervalPartition a c => lowerDarbouxSum f P)
  let S' : Set ℝ := Set.range (fun P :
      {P : IntervalPartition a c // b ∈ Set.range P.points} =>
        lowerDarbouxSum f P.1)
  let T : Set ℝ := Set.range (fun P : IntervalPartition a c => upperDarbouxSum f P)
  let T' : Set ℝ := Set.range (fun P :
      {P : IntervalPartition a c // b ∈ Set.range P.points} =>
        upperDarbouxSum f P.1)
  have hS_bdd : BddAbove S := by
    refine ⟨M * (c - a), ?_⟩
    intro y hy
    rcases hy with ⟨P, rfl⟩
    have hsum :=
      lower_upper_sum_bounds (f := f) (a := a) (b := c) (m := -M) (M := M) hmin hmax P
    exact le_trans hsum.2.1 hsum.2.2
  have hS'_bdd : BddAbove S' := by
    refine ⟨M * (c - a), ?_⟩
    intro y hy
    rcases hy with ⟨P, rfl⟩
    have hsum :=
      lower_upper_sum_bounds (f := f) (a := a) (b := c) (m := -M) (M := M) hmin hmax P.1
    exact le_trans hsum.2.1 hsum.2.2
  have hT_bdd : BddBelow T := by
    refine ⟨(-M) * (c - a), ?_⟩
    intro y hy
    rcases hy with ⟨P, rfl⟩
    have hsum :=
      lower_upper_sum_bounds (f := f) (a := a) (b := c) (m := -M) (M := M) hmin hmax P
    exact le_trans hsum.1 hsum.2.1
  have hT'_bdd : BddBelow T' := by
    refine ⟨(-M) * (c - a), ?_⟩
    intro y hy
    rcases hy with ⟨P, rfl⟩
    have hsum :=
      lower_upper_sum_bounds (f := f) (a := a) (b := c) (m := -M) (M := M) hmin hmax P.1
    exact le_trans hsum.1 hsum.2.1
  have hS_nonempty : S.Nonempty := by
    obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := c) hac
    refine ⟨lowerDarbouxSum f P0, ?_⟩
    exact ⟨P0, rfl⟩
  have hT_nonempty : T.Nonempty := by
    obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := c) hac
    refine ⟨upperDarbouxSum f P0, ?_⟩
    exact ⟨P0, rfl⟩
  have hS'_nonempty : S'.Nonempty := by
    rcases intervalPartition_three_points (a := a) (b := b) (c := c) hab hbc with ⟨P0, hbP0⟩
    refine ⟨lowerDarbouxSum f P0, ?_⟩
    exact ⟨⟨P0, hbP0⟩, rfl⟩
  have hT'_nonempty : T'.Nonempty := by
    rcases intervalPartition_three_points (a := a) (b := b) (c := c) hab hbc with ⟨P0, hbP0⟩
    refine ⟨upperDarbouxSum f P0, ?_⟩
    exact ⟨⟨P0, hbP0⟩, rfl⟩
  have hS'_subset : S' ⊆ S := by
    intro y hy
    rcases hy with ⟨P, rfl⟩
    exact ⟨P.1, rfl⟩
  have hT'_subset : T' ⊆ T := by
    intro y hy
    rcases hy with ⟨P, rfl⟩
    exact ⟨P.1, rfl⟩
  have hS_le : sSup S ≤ sSup S' := by
    refine csSup_le hS_nonempty ?_
    intro y hy
    rcases hy with ⟨P, rfl⟩
    rcases intervalPartition_refine_with_point (a := a) (b := b) (c := c) hab hbc P with
      ⟨Q, hPQ, hbQ⟩
    have hle := (lower_upper_sum_refinement (f := f) (a := a) (b := c) hbound' hPQ).1
    have hmem : lowerDarbouxSum f Q ∈ S' := by
      exact ⟨⟨Q, hbQ⟩, rfl⟩
    exact le_trans hle (le_csSup hS'_bdd hmem)
  have hS_ge : sSup S' ≤ sSup S :=
    csSup_le_csSup hS_bdd hS'_nonempty hS'_subset
  have hT_le : sInf T ≤ sInf T' :=
    csInf_le_csInf hT_bdd hT'_nonempty hT'_subset
  have hT_ge : sInf T' ≤ sInf T := by
    refine le_csInf hT_nonempty ?_
    intro y hy
    rcases hy with ⟨P, rfl⟩
    rcases intervalPartition_refine_with_point (a := a) (b := b) (c := c) hab hbc P with
      ⟨Q, hPQ, hbQ⟩
    have hle := (lower_upper_sum_refinement (f := f) (a := a) (b := c) hbound' hPQ).2
    have hmem : upperDarbouxSum f Q ∈ T' := by
      exact ⟨⟨Q, hbQ⟩, rfl⟩
    exact le_trans (csInf_le hT'_bdd hmem) hle
  refine ⟨?_, ?_⟩
  · have hSupEq : sSup S = sSup S' := le_antisymm hS_le hS_ge
    simpa [lowerDarbouxIntegral, S] using hSupEq
  · have hInfEq : sInf T = sInf T' := le_antisymm hT_le hT_ge
    simpa [upperDarbouxIntegral, T] using hInfEq

/-- Split a partition that contains `b` into left/right partitions. -/
lemma intervalPartition_split_at_point {a b c : ℝ} {f : ℝ → ℝ}
    (P : IntervalPartition a c) (hb : b ∈ Set.range P.points) :
    ∃ P1 : IntervalPartition a b, ∃ P2 : IntervalPartition b c,
      lowerDarbouxSum f P = lowerDarbouxSum f P1 + lowerDarbouxSum f P2 ∧
      upperDarbouxSum f P = upperDarbouxSum f P1 + upperDarbouxSum f P2 := by
  classical
  rcases hb with ⟨k, hk⟩
  let n1 : ℕ := k.val
  have hk_le : n1 ≤ P.n := Nat.le_of_lt_succ k.isLt
  let n2 : ℕ := P.n - n1
  have hcast1 : n1 + 1 ≤ P.n + 1 := Nat.succ_le_succ hk_le
  let points1 : Fin (n1 + 1) → ℝ := fun i => P.points (Fin.castLE hcast1 i)
  have hmono1 : StrictMono points1 := P.mono.comp (Fin.strictMono_castLE hcast1)
  have hleft1 : points1 0 = a := by
    have : (Fin.castLE hcast1 (0 : Fin (n1 + 1)) : Fin (P.n + 1)) = 0 := by
      apply Fin.ext
      simp
    simp [points1, this, P.left_eq]
  have hright1 : points1 ⟨n1, Nat.lt_succ_self n1⟩ = b := by
    have : (Fin.castLE hcast1 ⟨n1, Nat.lt_succ_self n1⟩ : Fin (P.n + 1)) = k := by
      apply Fin.ext
      simp [n1]
    simp [points1, this, hk]
  let P1 : IntervalPartition a b :=
    { n := n1
      points := points1
      mono := hmono1
      left_eq := hleft1
      right_eq := hright1 }
  have hcast2 : n2 + 1 + n1 = P.n + 1 := by
    dsimp [n2, n1]
    omega
  let points2 : Fin (n2 + 1) → ℝ :=
    fun i => P.points (Fin.cast hcast2 (Fin.addNat i n1))
  have hmono2 : StrictMono points2 := by
    have hmono_add : StrictMono (fun i : Fin (n2 + 1) => Fin.addNat i n1) :=
      Fin.strictMono_addNat n1
    have hmono_cast : StrictMono (fun i : Fin (n2 + 1 + n1) => Fin.cast hcast2 i) :=
      Fin.cast_strictMono hcast2
    exact P.mono.comp (hmono_cast.comp hmono_add)
  have hleft2 : points2 0 = b := by
    have : (Fin.cast hcast2 (Fin.addNat (0 : Fin (n2 + 1)) n1) : Fin (P.n + 1)) = k := by
      apply Fin.ext
      simp [n1]
    simp [points2, this, hk]
  have hright2 : points2 ⟨n2, Nat.lt_succ_self n2⟩ = c := by
    have hsum : n2 + n1 = P.n := by
      dsimp [n2, n1]
      exact Nat.sub_add_cancel hk_le
    have hcast_last : (Fin.cast hcast2 (Fin.addNat ⟨n2, Nat.lt_succ_self n2⟩ n1) :
        Fin (P.n + 1)) = ⟨P.n, Nat.lt_succ_self P.n⟩ := by
      apply Fin.ext
      simp [hsum, n1]
    simp [points2, P.right_eq, hsum]
  let P2 : IntervalPartition b c :=
    { n := n2
      points := points2
      mono := hmono2
      left_eq := hleft2
      right_eq := hright2 }
  refine ⟨P1, P2, ?_⟩
  have hsum_n2n1 : n2 + n1 = P.n := by
    dsimp [n2, n1]
    exact Nat.sub_add_cancel hk_le
  have hsum_n1n2 : n1 + n2 = P.n := by
    simpa [Nat.add_comm] using hsum_n2n1
  have hcast_castSucc (i : Fin n1) :
      (Fin.castLE hcast1 (Fin.castSucc i) : Fin (P.n + 1)) =
        Fin.castSucc (Fin.castLE hk_le i) := by
    apply Fin.ext
    simp
  have hcast_succ (i : Fin n1) :
      (Fin.castLE hcast1 i.succ : Fin (P.n + 1)) =
        (Fin.castLE hk_le i).succ := by
    apply Fin.ext
    simp
  have htag1 (i : Fin n1) :
      lowerTag f P1 i = lowerTag f P (Fin.castLE hk_le i) := by
    simp [lowerTag, P1, points1, hcast_castSucc, hcast_succ]
  have hdelta1 (i : Fin n1) :
      P1.delta i = P.delta (Fin.castLE hk_le i) := by
    simp [IntervalPartition.delta, P1, points1, hcast_castSucc, hcast_succ]
  have htag1_upper (i : Fin n1) :
      upperTag f P1 i = upperTag f P (Fin.castLE hk_le i) := by
    simp [upperTag, P1, points1, hcast_castSucc, hcast_succ]
  have hdelta1_upper (i : Fin n1) :
      P1.delta i = P.delta (Fin.castLE hk_le i) := by
    simp [IntervalPartition.delta, P1, points1, hcast_castSucc, hcast_succ]
  have hindex2 (i : Fin n2) : i.val + n1 < P.n := by
    have hi : i.val < n2 := i.isLt
    have hi' : i.val + n1 < n2 + n1 := Nat.add_lt_add_right hi n1
    simpa [hsum_n2n1] using hi'
  have hindex2_val (i : Fin n2) : i.val + n1 < P.n + 1 := by
    exact Nat.lt_succ_of_lt (hindex2 i)
  have hindex2_succ (i : Fin n2) : i.val + n1 + 1 < P.n + 1 := by
    exact Nat.succ_lt_succ (hindex2 i)
  have hpoints2_castSucc (i : Fin n2) :
      (Fin.cast hcast2 (Fin.addNat (Fin.castSucc i) n1) : Fin (P.n + 1)) =
        ⟨i.val + n1, hindex2_val i⟩ := by
    apply Fin.ext
    simp
  have hpoints2_succ (i : Fin n2) :
      (Fin.cast hcast2 (Fin.addNat i.succ n1) : Fin (P.n + 1)) =
        ⟨i.val + n1 + 1, hindex2_succ i⟩ := by
    apply Fin.ext
    simp [Nat.add_assoc, Nat.add_comm]
  have htag2 (i : Fin n2) :
      lowerTag f P2 i = lowerTag f P ⟨i.val + n1, hindex2 i⟩ := by
    simp [lowerTag, P2, points2, hpoints2_castSucc, hpoints2_succ]
  have hdelta2 (i : Fin n2) :
      P2.delta i = P.delta ⟨i.val + n1, hindex2 i⟩ := by
    simp [IntervalPartition.delta, P2, points2, hpoints2_castSucc, hpoints2_succ]
  have htag2_upper (i : Fin n2) :
      upperTag f P2 i = upperTag f P ⟨i.val + n1, hindex2 i⟩ := by
    simp [upperTag, P2, points2, hpoints2_castSucc, hpoints2_succ]
  have hdelta2_upper (i : Fin n2) :
      P2.delta i = P.delta ⟨i.val + n1, hindex2 i⟩ := by
    simp [IntervalPartition.delta, P2, points2, hpoints2_castSucc, hpoints2_succ]
  have hsum_lower :
      lowerDarbouxSum f P =
        lowerDarbouxSum f P1 + lowerDarbouxSum f P2 := by
    classical
    let F : ℕ → ℝ := fun i =>
      if h : i < P.n then lowerTag f P ⟨i, h⟩ * P.delta ⟨i, h⟩ else 0
    have hsumP :
        lowerDarbouxSum f P = ∑ i ∈ Finset.range P.n, F i := by
      have hsum' : lowerDarbouxSum f P = ∑ i : Fin P.n, F i := by
        unfold lowerDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) < P.n := i.isLt
        simp [F, hiP]
      have hsum := (Fin.sum_univ_eq_sum_range (f := F) (n := P.n))
      exact Eq.trans hsum' hsum
    have hsumP1 :
        lowerDarbouxSum f P1 = ∑ i ∈ Finset.range n1, F i := by
      have hsum' : lowerDarbouxSum f P1 = ∑ i : Fin n1, F i := by
        unfold lowerDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) < P.n := lt_of_lt_of_le i.isLt hk_le
        have hcast : (Fin.castLE hk_le i : Fin P.n) = ⟨i, hiP⟩ := by
          rfl
        simp [F, hiP, htag1, hdelta1, hcast]
      have hsum := (Fin.sum_univ_eq_sum_range (f := F) (n := n1))
      exact Eq.trans hsum' hsum
    have hsumP2 :
        lowerDarbouxSum f P2 = ∑ i ∈ Finset.range n2, F (i + n1) := by
      have hsum' : lowerDarbouxSum f P2 = ∑ i : Fin n2, F (i + n1) := by
        unfold lowerDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) + n1 < P.n := by
          have hi'' : (i : ℕ) + n1 < n2 + n1 := Nat.add_lt_add_right i.isLt n1
          simpa [hsum_n2n1] using hi''
        have hcast : (⟨(i : ℕ) + n1, hiP⟩ : Fin P.n) = ⟨(i : ℕ) + n1, hiP⟩ := rfl
        have htag2' :
            lowerTag f P2 i = lowerTag f P ⟨(i : ℕ) + n1, hiP⟩ := by
          simpa using (htag2 i)
        have hdelta2' :
            P2.delta i = P.delta ⟨(i : ℕ) + n1, hiP⟩ := by
          simpa using (hdelta2 i)
        have hF : F ((i : ℕ) + n1) =
            lowerTag f P ⟨(i : ℕ) + n1, hiP⟩ * P.delta ⟨(i : ℕ) + n1, hiP⟩ := by
          simp [F, hiP]
        simp [hF, htag2', hdelta2']
      have hsum := (Fin.sum_univ_eq_sum_range (f := fun i => F (i + n1)) (n := n2))
      exact Eq.trans hsum' hsum
    have hsplit :
        (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i =
          ∑ i ∈ Finset.range P.n, F i := by
      exact Finset.sum_range_add_sum_Ico F hk_le
    have hsplit' :
        ∑ i ∈ Finset.range P.n, F i =
            (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i := by
      simpa using hsplit.symm
    have hIco :
        ∑ i ∈ Finset.Ico n1 P.n, F i =
          ∑ i ∈ Finset.range n2, F (i + n1) := by
      have hshift :=
        (Finset.sum_Ico_add (f := F) (a := 0) (b := n2) (c := n1))
      have hshift' :
          ∑ x ∈ Finset.Ico n1 P.n, F x =
            ∑ x ∈ Finset.Ico 0 n2, F (n1 + x) := by
        simpa [hsum_n1n2, Nat.add_comm] using hshift.symm
      simpa [Nat.add_comm] using hshift'
    calc
      lowerDarbouxSum f P =
          ∑ i ∈ Finset.range P.n, F i := hsumP
      _ =
          (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i := hsplit'
      _ =
          (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.range n2, F (i + n1) := by
            simp [hIco]
      _ =
          lowerDarbouxSum f P1 + lowerDarbouxSum f P2 := by
            simp [hsumP1.symm, hsumP2.symm]
  have hsum_upper :
      upperDarbouxSum f P =
        upperDarbouxSum f P1 + upperDarbouxSum f P2 := by
    classical
    let F : ℕ → ℝ := fun i =>
      if h : i < P.n then upperTag f P ⟨i, h⟩ * P.delta ⟨i, h⟩ else 0
    have hsumP :
        upperDarbouxSum f P = ∑ i ∈ Finset.range P.n, F i := by
      have hsum' : upperDarbouxSum f P = ∑ i : Fin P.n, F i := by
        unfold upperDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) < P.n := i.isLt
        simp [F, hiP]
      have hsum := (Fin.sum_univ_eq_sum_range (f := F) (n := P.n))
      exact Eq.trans hsum' hsum
    have hsumP1 :
        upperDarbouxSum f P1 = ∑ i ∈ Finset.range n1, F i := by
      have hsum' : upperDarbouxSum f P1 = ∑ i : Fin n1, F i := by
        unfold upperDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) < P.n := lt_of_lt_of_le i.isLt hk_le
        have hcast : (Fin.castLE hk_le i : Fin P.n) = ⟨i, hiP⟩ := by
          rfl
        simp [F, hiP, htag1_upper, hdelta1_upper, hcast]
      have hsum := (Fin.sum_univ_eq_sum_range (f := F) (n := n1))
      exact Eq.trans hsum' hsum
    have hsumP2 :
        upperDarbouxSum f P2 = ∑ i ∈ Finset.range n2, F (i + n1) := by
      have hsum' : upperDarbouxSum f P2 = ∑ i : Fin n2, F (i + n1) := by
        unfold upperDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) + n1 < P.n := by
          have hi'' : (i : ℕ) + n1 < n2 + n1 := Nat.add_lt_add_right i.isLt n1
          simpa [hsum_n2n1] using hi''
        have hcast : (⟨(i : ℕ) + n1, hiP⟩ : Fin P.n) = ⟨(i : ℕ) + n1, hiP⟩ := rfl
        have htag2' :
            upperTag f P2 i = upperTag f P ⟨(i : ℕ) + n1, hiP⟩ := by
          simpa using (htag2_upper i)
        have hdelta2' :
            P2.delta i = P.delta ⟨(i : ℕ) + n1, hiP⟩ := by
          simpa using (hdelta2_upper i)
        have hF : F ((i : ℕ) + n1) =
            upperTag f P ⟨(i : ℕ) + n1, hiP⟩ * P.delta ⟨(i : ℕ) + n1, hiP⟩ := by
          simp [F, hiP]
        simp [hF, htag2', hdelta2']
      have hsum := (Fin.sum_univ_eq_sum_range (f := fun i => F (i + n1)) (n := n2))
      exact Eq.trans hsum' hsum
    have hsplit :
        (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i =
          ∑ i ∈ Finset.range P.n, F i := by
      exact Finset.sum_range_add_sum_Ico F hk_le
    have hsplit' :
        ∑ i ∈ Finset.range P.n, F i =
            (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i := by
      simpa using hsplit.symm
    have hIco :
        ∑ i ∈ Finset.Ico n1 P.n, F i =
          ∑ i ∈ Finset.range n2, F (i + n1) := by
      have hshift :=
        (Finset.sum_Ico_add (f := F) (a := 0) (b := n2) (c := n1))
      have hshift' :
          ∑ x ∈ Finset.Ico n1 P.n, F x =
            ∑ x ∈ Finset.Ico 0 n2, F (n1 + x) := by
        simpa [hsum_n1n2, Nat.add_comm] using hshift.symm
      simpa [Nat.add_comm] using hshift'
    calc
      upperDarbouxSum f P =
          ∑ i ∈ Finset.range P.n, F i := hsumP
      _ =
          (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i := hsplit'
      _ =
          (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.range n2, F (i + n1) := by
            simp [hIco]
      _ =
          upperDarbouxSum f P1 + upperDarbouxSum f P2 := by
            simp [hsumP1.symm, hsumP2.symm]
  exact ⟨hsum_lower, hsum_upper⟩

/-- Append a left/right partition into a partition of `[a, c]`. -/
lemma intervalPartition_append {a b c : ℝ} {f : ℝ → ℝ}
    (P1 : IntervalPartition a b) (P2 : IntervalPartition b c) :
    ∃ P : IntervalPartition a c, b ∈ Set.range P.points ∧
      lowerDarbouxSum f P = lowerDarbouxSum f P1 + lowerDarbouxSum f P2 ∧
      upperDarbouxSum f P = upperDarbouxSum f P1 + upperDarbouxSum f P2 := by
  classical
  let n1 : ℕ := P1.n
  let n2 : ℕ := P2.n
  let points : Fin (n1 + n2 + 1) → ℝ := fun i =>
    if h : (i : ℕ) ≤ n1 then
      P1.points ⟨i, Nat.lt_succ_of_le h⟩
    else
      P2.points ⟨i - n1, by
        have hi' : n1 < i.val := Nat.lt_of_not_ge h
        have hi'' : i.val ≤ n1 + n2 := Nat.le_of_lt_succ i.isLt
        have hi : i.val - n1 ≤ n2 := by
          omega
        exact Nat.lt_succ_of_le hi⟩
  have hmono : StrictMono points := by
    refine (Fin.strictMono_iff_lt_succ (f := points)).2 ?_
    intro i
    by_cases hlt : (i : ℕ) < n1
    · have hi_le : (i : ℕ) ≤ n1 := le_of_lt hlt
      have hisucc_le : (i.succ : ℕ) ≤ n1 := Nat.succ_le_of_lt hlt
      have hisucc_le' : (i : ℕ) + 1 ≤ n1 := by
        simpa using hisucc_le
      have hidx :
          (⟨i.val, Nat.lt_succ_of_le hi_le⟩ : Fin (n1 + 1)) <
            ⟨i.val + 1, Nat.succ_lt_succ hlt⟩ :=
        (Fin.lt_def).2 (Nat.lt_succ_self i.val)
      have hleft : points i.castSucc = P1.points ⟨i.val, Nat.lt_succ_of_le hi_le⟩ := by
        simp [points, hi_le]
      have hright : points i.succ = P1.points ⟨i.val + 1, Nat.succ_lt_succ hlt⟩ := by
        simp [points, hisucc_le']
      simpa [hleft, hright] using P1.mono hidx
    · have hge : n1 ≤ (i : ℕ) := le_of_not_gt hlt
      by_cases hEq : (i : ℕ) = n1
      · have hsucc_not_le : ¬ (i.succ : ℕ) ≤ n1 := by
          exact not_le_of_gt (by simp [hEq])
        have hpos : (i.succ : ℕ) - n1 = 1 := by
          simp [hEq]
        have hlt' : n1 < n1 + n2 := by
          simpa [hEq] using i.isLt
        have hposn2 : 0 < n2 := by
          omega
        have h1 : (1 : ℕ) ≤ n2 := Nat.succ_le_iff.mpr hposn2
        have hmono2' := (Fin.strictMono_iff_lt_succ (f := P2.points)).1 P2.mono
        have hmono2 : P2.points 0 < P2.points ⟨1, Nat.lt_succ_of_le h1⟩ := by
          simpa using hmono2' ⟨0, hposn2⟩
        have hleft2 : P2.points 0 = b := P2.left_eq
        have hright2 :
            points i.succ = P2.points ⟨1, by
              exact Nat.lt_succ_of_le h1⟩ := by
          have hsucc_not_le' : ¬ (i : ℕ) + 1 ≤ n1 := by
            simpa using hsucc_not_le
          have hpos' : (i : ℕ) + 1 - n1 = 1 := by
            simpa using hpos
          simp [points, hsucc_not_le', hpos']
        have hleft1 : points i.castSucc = b := by
          have hi_le' : (i : ℕ) ≤ n1 := by
            simp [hEq]
          have hpoints : points i.castSucc = P1.points ⟨n1, Nat.lt_succ_self n1⟩ := by
            simp [points, hEq]
          simpa [hpoints] using P1.right_eq
        have hgt : points i.castSucc < points i.succ := by
          simpa [hleft1, hleft2, hright2] using hmono2
        simpa using hgt
      · have hgt : n1 < (i : ℕ) := lt_of_le_of_ne hge (Ne.symm hEq)
        have hnot_le : ¬ (i : ℕ) ≤ n1 := not_le_of_gt hgt
        have hsucc_not_le : ¬ (i.succ : ℕ) ≤ n1 := by
          exact not_le_of_gt (lt_trans hgt (Nat.lt_succ_self i.val))
        have hsucc_not_le' : ¬ (i : ℕ) + 1 ≤ n1 := by
          simpa using hsucc_not_le
        have hidx :
            (⟨i.val - n1, by
              have h1 : i.val - n1 ≤ n2 := by omega
              exact Nat.lt_succ_of_le h1⟩ : Fin (n2 + 1)) <
              ⟨i.val + 1 - n1, by
                have h1 : i.val + 1 - n1 ≤ n2 := by omega
                exact Nat.lt_succ_of_le h1⟩ :=
          by
            have hlt' : i.val - n1 < i.val + 1 - n1 := by
              apply Nat.sub_lt_sub_right (c := n1) (a := i.val) (b := i.val + 1)
              · exact le_of_lt hgt
              · exact Nat.lt_succ_self i.val
            exact (Fin.lt_def).2 hlt'
        have hgt' : points i.castSucc < points i.succ := by
          have hmono2 := P2.mono hidx
          simpa [points, hnot_le, hsucc_not_le'] using hmono2
        simpa using hgt'
  have hleft : points 0 = a := by
    have h0 : (0 : ℕ) ≤ n1 := Nat.zero_le n1
    simp [points, h0, P1.left_eq]
  have hright : points ⟨n1 + n2, Nat.lt_succ_self _⟩ = c := by
    by_cases h2 : n2 = 0
    · have hbc' : b = c := by
        have hright' : P2.points 0 = c := by simpa [n2, h2] using P2.right_eq
        calc
          b = P2.points 0 := by simpa using P2.left_eq.symm
          _ = c := hright'
      have hle : (n1 + n2 : ℕ) ≤ n1 := by simp [h2]
      have hpoints : points ⟨n1 + n2, Nat.lt_succ_self _⟩ =
          P1.points ⟨n1, Nat.lt_succ_self n1⟩ := by
        simp [points, h2]
      calc
        points ⟨n1 + n2, Nat.lt_succ_self _⟩ = P1.points ⟨n1, by
            exact Nat.lt_succ_self n1⟩ := hpoints
        _ = b := P1.right_eq
        _ = c := hbc'
    · have hnot_le : ¬ (n1 + n2 : ℕ) ≤ n1 := by
        have hpos : 0 < n2 := Nat.pos_of_ne_zero h2
        exact not_le_of_gt (Nat.lt_add_of_pos_right (n := n1) hpos)
      have hsub : (n1 + n2 : ℕ) - n1 = n2 := by
        exact Nat.add_sub_cancel_left n1 n2
      have hpoints : points ⟨n1 + n2, Nat.lt_succ_self _⟩ =
          P2.points ⟨n2, Nat.lt_succ_self n2⟩ := by
        simp [points, hnot_le, hsub]
      simpa [hsub] using (Eq.trans hpoints P2.right_eq)
  let P : IntervalPartition a c :=
    { n := n1 + n2
      points := points
      mono := hmono
      left_eq := hleft
      right_eq := hright }
  have hbP : b ∈ Set.range P.points := by
    refine ⟨⟨n1, Nat.lt_succ_of_le (Nat.le_add_right n1 n2)⟩, ?_⟩
    have hle : (n1 : ℕ) ≤ n1 := le_rfl
    have hpoints : points ⟨n1, Nat.lt_succ_of_le (Nat.le_add_right n1 n2)⟩ =
        P1.points ⟨n1, Nat.lt_succ_self n1⟩ := by
      simp [points]
    calc
      P.points ⟨n1, Nat.lt_succ_of_le (Nat.le_add_right n1 n2)⟩ =
          points ⟨n1, Nat.lt_succ_of_le (Nat.le_add_right n1 n2)⟩ := rfl
      _ = P1.points ⟨n1, Nat.lt_succ_self n1⟩ := hpoints
      _ = b := P1.right_eq
  have hcast1 : n1 + 1 ≤ n1 + n2 + 1 :=
    Nat.succ_le_succ (Nat.le_add_right n1 n2)
  have htag1 (i : Fin n1) :
      lowerTag f P1 i = lowerTag f P (Fin.castLE (Nat.le_add_right n1 n2) i) := by
    cases i with
    | mk i hi =>
        have hi_le : i ≤ n1 := le_of_lt hi
        have hisucc_le : i + 1 ≤ n1 := Nat.succ_le_iff.mpr hi
        simp [lowerTag, P, points, hi_le, hisucc_le]
  have hdelta1 (i : Fin n1) :
      P1.delta i = P.delta (Fin.castLE (Nat.le_add_right n1 n2) i) := by
    cases i with
    | mk i hi =>
        have hi_le : i ≤ n1 := le_of_lt hi
        have hisucc_le : i + 1 ≤ n1 := Nat.succ_le_iff.mpr hi
        simp [IntervalPartition.delta, P, points, hi_le, hisucc_le]
  have htag2 (i : Fin n2) :
      lowerTag f P2 i = lowerTag f P ⟨i.val + n1, by
        have hi' : i.val + n1 < n2 + n1 := Nat.add_lt_add_right i.isLt n1
        dsimp [P]
        rw [Nat.add_comm n1 n2]
        exact hi'⟩ := by
    cases i with
    | mk i hi =>
        by_cases hzero : i = 0
        · subst hzero
          have hposn2 : 0 < n2 := by
            simpa using hi
          have hle : (n1 : ℕ) ≤ n1 := le_rfl
          have hnot_le : ¬ ((n1 + 1 : ℕ) ≤ n1) := by
            exact not_le_of_gt (Nat.lt_succ_self n1)
          have hright1 : P1.points ⟨n1, Nat.lt_succ_of_le hle⟩ = b := by
            simpa using P1.right_eq
          simp [lowerTag, P, points, hnot_le, hright1, P2.left_eq]
        · have hgt : ¬ ((i + n1 : ℕ) ≤ n1) := by
            have hi' : 0 < i := Nat.pos_of_ne_zero hzero
            have hlt : n1 < i + n1 := by
              simpa [Nat.add_comm] using (Nat.lt_add_of_pos_right (n := n1) hi')
            exact not_le_of_gt hlt
          have hgt' : ¬ ((i + n1 + 1 : ℕ) ≤ n1) := by
            have hlt' : n1 < i + n1 + 1 := by
              omega
            exact not_le_of_gt hlt'
          have hsub : i + n1 + 1 - n1 = i + 1 := by
            omega
          simp [lowerTag, P, points, hgt, hgt', hsub]
  have hdelta2 (i : Fin n2) :
      P2.delta i = P.delta ⟨i.val + n1, by
        have hi' : i.val + n1 < n2 + n1 := Nat.add_lt_add_right i.isLt n1
        dsimp [P]
        rw [Nat.add_comm n1 n2]
        exact hi'⟩ := by
    cases i with
    | mk i hi =>
        by_cases hzero : i = 0
        · subst hzero
          have hposn2 : 0 < n2 := by
            simpa using hi
          have hle : (n1 : ℕ) ≤ n1 := le_rfl
          have hnot_le : ¬ ((n1 + 1 : ℕ) ≤ n1) := by
            exact not_le_of_gt (Nat.lt_succ_self n1)
          have hright1 : P1.points ⟨n1, Nat.lt_succ_of_le hle⟩ = b := by
            simpa using P1.right_eq
          simp [IntervalPartition.delta, P, points, hnot_le, hright1, P2.left_eq]
        · have hgt : ¬ ((i + n1 : ℕ) ≤ n1) := by
            have hi' : 0 < i := Nat.pos_of_ne_zero hzero
            have hlt : n1 < i + n1 := by
              simpa [Nat.add_comm] using (Nat.lt_add_of_pos_right (n := n1) hi')
            exact not_le_of_gt hlt
          have hgt' : ¬ ((i + n1 + 1 : ℕ) ≤ n1) := by
            have hlt' : n1 < i + n1 + 1 := by
              omega
            exact not_le_of_gt hlt'
          have hsub : i + n1 + 1 - n1 = i + 1 := by
            omega
          simp [IntervalPartition.delta, P, points, hgt, hgt', hsub]
  have htag1_upper (i : Fin n1) :
      upperTag f P1 i = upperTag f P (Fin.castLE (Nat.le_add_right n1 n2) i) := by
    cases i with
    | mk i hi =>
        have hi_le : i ≤ n1 := le_of_lt hi
        have hisucc_le : i + 1 ≤ n1 := Nat.succ_le_iff.mpr hi
        simp [upperTag, P, points, hi_le, hisucc_le]
  have hdelta1_upper (i : Fin n1) :
      P1.delta i = P.delta (Fin.castLE (Nat.le_add_right n1 n2) i) := by
    simpa using hdelta1 i
  have htag2_upper (i : Fin n2) :
      upperTag f P2 i = upperTag f P ⟨i.val + n1, by
        have hi' : i.val + n1 < n2 + n1 := Nat.add_lt_add_right i.isLt n1
        dsimp [P]
        rw [Nat.add_comm n1 n2]
        exact hi'⟩ := by
    cases i with
    | mk i hi =>
        by_cases hzero : i = 0
        · subst hzero
          have hposn2 : 0 < n2 := by
            simpa using hi
          have hle : (n1 : ℕ) ≤ n1 := le_rfl
          have hnot_le : ¬ ((n1 + 1 : ℕ) ≤ n1) := by
            exact not_le_of_gt (Nat.lt_succ_self n1)
          have hright1 : P1.points ⟨n1, Nat.lt_succ_of_le hle⟩ = b := by
            simpa using P1.right_eq
          simp [upperTag, P, points, hnot_le, hright1, P2.left_eq]
        · have hgt : ¬ ((i + n1 : ℕ) ≤ n1) := by
            have hi' : 0 < i := Nat.pos_of_ne_zero hzero
            have hlt : n1 < i + n1 := by
              simpa [Nat.add_comm] using (Nat.lt_add_of_pos_right (n := n1) hi')
            exact not_le_of_gt hlt
          have hgt' : ¬ ((i + n1 + 1 : ℕ) ≤ n1) := by
            have hlt' : n1 < i + n1 + 1 := by
              omega
            exact not_le_of_gt hlt'
          have hsub : i + n1 + 1 - n1 = i + 1 := by
            omega
          simp [upperTag, P, points, hgt, hgt', hsub]
  have hdelta2_upper (i : Fin n2) :
      P2.delta i = P.delta ⟨i.val + n1, by
        have hi' : i.val + n1 < n2 + n1 := Nat.add_lt_add_right i.isLt n1
        dsimp [P]
        rw [Nat.add_comm n1 n2]
        exact hi'⟩ := by
    simpa using hdelta2 i
  have hsum_lower :
      lowerDarbouxSum f P = lowerDarbouxSum f P1 + lowerDarbouxSum f P2 := by
    classical
    let F : ℕ → ℝ := fun i =>
      if h : i < P.n then lowerTag f P ⟨i, h⟩ * P.delta ⟨i, h⟩ else 0
    have hsumP :
        lowerDarbouxSum f P = ∑ i ∈ Finset.range P.n, F i := by
      have hsum' : lowerDarbouxSum f P = ∑ i : Fin P.n, F i := by
        unfold lowerDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) < P.n := i.isLt
        simp [F, hiP]
      have hsum := (Fin.sum_univ_eq_sum_range (f := F) (n := P.n))
      exact Eq.trans hsum' hsum
    have hsumP1 :
        lowerDarbouxSum f P1 = ∑ i ∈ Finset.range n1, F i := by
      have hsum' : lowerDarbouxSum f P1 = ∑ i : Fin n1, F i := by
        unfold lowerDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) < P.n := by
          have hi'' : (i : ℕ) < n1 + n2 := Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
          simpa [P] using hi''
        have hcast : (Fin.castLE (Nat.le_add_right n1 n2) i : Fin P.n) = ⟨i, hiP⟩ := by
          rfl
        simp [F, hiP, htag1, hdelta1, hcast]
      have hsum := (Fin.sum_univ_eq_sum_range (f := F) (n := n1))
      exact Eq.trans hsum' hsum
    have hsumP2 :
        lowerDarbouxSum f P2 = ∑ i ∈ Finset.range n2, F (i + n1) := by
      have hsum' : lowerDarbouxSum f P2 = ∑ i : Fin n2, F (i + n1) := by
        unfold lowerDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) + n1 < P.n := by
          have hi'' : (i : ℕ) + n1 < n2 + n1 := Nat.add_lt_add_right i.isLt n1
          simpa [Nat.add_comm, P] using hi''
        have htag2' :
            lowerTag f P2 i = lowerTag f P ⟨(i : ℕ) + n1, hiP⟩ := by
          simpa using (htag2 i)
        have hdelta2' :
            P2.delta i = P.delta ⟨(i : ℕ) + n1, hiP⟩ := by
          simpa using (hdelta2 i)
        have hF : F ((i : ℕ) + n1) =
            lowerTag f P ⟨(i : ℕ) + n1, hiP⟩ * P.delta ⟨(i : ℕ) + n1, hiP⟩ := by
          simp [F, hiP]
        simp [hF, htag2', hdelta2']
      have hsum := (Fin.sum_univ_eq_sum_range (f := fun i => F (i + n1)) (n := n2))
      exact Eq.trans hsum' hsum
    have hsplit :
        (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i =
          ∑ i ∈ Finset.range P.n, F i := by
      exact Finset.sum_range_add_sum_Ico F (Nat.le_add_right n1 n2)
    have hsplit' :
        ∑ i ∈ Finset.range P.n, F i =
            (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i := by
      simpa using hsplit.symm
    have hIco :
        ∑ i ∈ Finset.Ico n1 P.n, F i =
          ∑ i ∈ Finset.range n2, F (i + n1) := by
      have hshift :=
        (Finset.sum_Ico_add (f := F) (a := 0) (b := n2) (c := n1))
      have hshift' :
          ∑ x ∈ Finset.Ico n1 P.n, F x =
            ∑ x ∈ Finset.Ico 0 n2, F (n1 + x) := by
        simpa [P, Nat.add_comm] using hshift.symm
      simpa [Nat.add_comm] using hshift'
    calc
      lowerDarbouxSum f P =
          ∑ i ∈ Finset.range P.n, F i := hsumP
      _ =
          (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i := hsplit'
      _ =
          (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.range n2, F (i + n1) := by
            simp [hIco]
      _ =
          lowerDarbouxSum f P1 + lowerDarbouxSum f P2 := by
            simp [hsumP1.symm, hsumP2.symm]
  have hsum_upper :
      upperDarbouxSum f P =
        upperDarbouxSum f P1 + upperDarbouxSum f P2 := by
    classical
    let F : ℕ → ℝ := fun i =>
      if h : i < P.n then upperTag f P ⟨i, h⟩ * P.delta ⟨i, h⟩ else 0
    have hsumP :
        upperDarbouxSum f P = ∑ i ∈ Finset.range P.n, F i := by
      have hsum' : upperDarbouxSum f P = ∑ i : Fin P.n, F i := by
        unfold upperDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) < P.n := i.isLt
        simp [F, hiP]
      have hsum := (Fin.sum_univ_eq_sum_range (f := F) (n := P.n))
      exact Eq.trans hsum' hsum
    have hsumP1 :
        upperDarbouxSum f P1 = ∑ i ∈ Finset.range n1, F i := by
      have hsum' : upperDarbouxSum f P1 = ∑ i : Fin n1, F i := by
        unfold upperDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) < P.n := by
          have hi'' : (i : ℕ) < n1 + n2 := Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
          simpa [P] using hi''
        have hcast : (Fin.castLE (Nat.le_add_right n1 n2) i : Fin P.n) = ⟨i, hiP⟩ := by
          rfl
        simp [F, hiP, htag1_upper, hdelta1_upper, hcast]
      have hsum := (Fin.sum_univ_eq_sum_range (f := F) (n := n1))
      exact Eq.trans hsum' hsum
    have hsumP2 :
        upperDarbouxSum f P2 = ∑ i ∈ Finset.range n2, F (i + n1) := by
      have hsum' : upperDarbouxSum f P2 = ∑ i : Fin n2, F (i + n1) := by
        unfold upperDarbouxSum
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hiP : (i : ℕ) + n1 < P.n := by
          have hi'' : (i : ℕ) + n1 < n2 + n1 := Nat.add_lt_add_right i.isLt n1
          simpa [Nat.add_comm, P] using hi''
        have htag2' :
            upperTag f P2 i = upperTag f P ⟨(i : ℕ) + n1, hiP⟩ := by
          simpa using (htag2_upper i)
        have hdelta2' :
            P2.delta i = P.delta ⟨(i : ℕ) + n1, hiP⟩ := by
          simpa using (hdelta2_upper i)
        have hF : F ((i : ℕ) + n1) =
            upperTag f P ⟨(i : ℕ) + n1, hiP⟩ * P.delta ⟨(i : ℕ) + n1, hiP⟩ := by
          simp [F, hiP]
        simp [hF, htag2', hdelta2']
      have hsum := (Fin.sum_univ_eq_sum_range (f := fun i => F (i + n1)) (n := n2))
      exact Eq.trans hsum' hsum
    have hsplit :
        (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i =
          ∑ i ∈ Finset.range P.n, F i := by
      exact Finset.sum_range_add_sum_Ico F (Nat.le_add_right n1 n2)
    have hsplit' :
        ∑ i ∈ Finset.range P.n, F i =
            (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i := by
      simpa using hsplit.symm
    have hIco :
        ∑ i ∈ Finset.Ico n1 P.n, F i =
          ∑ i ∈ Finset.range n2, F (i + n1) := by
      have hshift :=
        (Finset.sum_Ico_add (f := F) (a := 0) (b := n2) (c := n1))
      have hshift' :
          ∑ x ∈ Finset.Ico n1 P.n, F x =
            ∑ x ∈ Finset.Ico 0 n2, F (n1 + x) := by
        simpa [P, Nat.add_comm] using hshift.symm
      simpa [Nat.add_comm] using hshift'
    calc
      upperDarbouxSum f P =
          ∑ i ∈ Finset.range P.n, F i := hsumP
      _ =
          (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.Ico n1 P.n, F i := hsplit'
      _ =
          (∑ i ∈ Finset.range n1, F i) +
            ∑ i ∈ Finset.range n2, F (i + n1) := by
            simp [hIco]
      _ =
          upperDarbouxSum f P1 + upperDarbouxSum f P2 := by
            simp [hsumP1.symm, hsumP2.symm]
  exact ⟨P, hbP, hsum_lower, hsum_upper⟩

end Section02
end Chap05

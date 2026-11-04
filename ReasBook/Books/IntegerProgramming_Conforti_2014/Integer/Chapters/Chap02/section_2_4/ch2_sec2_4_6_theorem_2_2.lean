/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_theorem_2_2.Transport
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_theorem_2_2.Bose
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_theorem_2_2.Skolem
public import Mathlib.Tactic
public import Mathlib.Data.Nat.ModEq
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_definition_2_26

public section

namespace SteinerTripleSystem

open scoped BigOperators

/-- On the canonical ground set `Finset.univ : Finset (Fin n)`, the source-facing owner
`IsOfOrder n` is equivalent to the primitive Steiner-system owner `IsOn`. -/
theorem isOfOrder_univ_iff_isOn {n : ℕ} {S : Set (Finset (Fin n))} :
    IsOfOrder n Finset.univ S ↔ IsOn Finset.univ S := by
  constructor
  · intro h
    exact h.isOn
  · intro h
    exact IsOfOrder.ofCardEqAndIsOn (by simp) h

/-- Helper for Theorem 2.2: counting pair incidences identifies the `2`-subsets of `Fin n` with
the data of a block together with one of its internal pairs. -/
lemma pairCount_eq_three_mul_blocks {n : ℕ} {S : Set (Finset (Fin n))}
    (h : IsOn Finset.univ S) :
    Nat.choose n 2 = 3 * Nat.card {s : Finset (Fin n) // s ∈ S} := by
  classical
  let pairToBlockPair :
      {p : Finset (Fin n) // p ∈ Finset.univ.powersetCard 2} →
        Sigma fun s : {s : Finset (Fin n) // s ∈ S} ↦
          {p : Finset (Fin n) // p ∈ s.1.powersetCard 2} := fun p ↦
      let hs := Classical.choose (ExistsUnique.exists (h.pair_cover p.1 p.2))
      let hhs := Classical.choose_spec (ExistsUnique.exists (h.pair_cover p.1 p.2))
      ⟨⟨hs, hhs.1⟩, ⟨p.1, Finset.mem_powersetCard.mpr ⟨hhs.2, (Finset.mem_powersetCard.mp p.2).2⟩⟩⟩
  have hbij : Function.Bijective pairToBlockPair := by
    constructor
    · intro p q hpq
      exact Subtype.ext (congrArg (fun sp ↦ sp.2.1) hpq)
    · intro sp
      rcases sp with ⟨⟨s, hsS⟩, ⟨p, hp⟩⟩
      refine ⟨⟨p, ?_⟩, ?_⟩
      · rcases Finset.mem_powersetCard.mp hp with ⟨hps, hp2⟩
        exact Finset.mem_powersetCard.mpr ⟨fun a ha ↦ h.subset_ground _ hsS (hps ha), hp2⟩
      · -- Uniqueness of the covering block forces the forward map to recover `s`.
        have hpUniv : p ∈ Finset.univ.powersetCard 2 := by
          rcases Finset.mem_powersetCard.mp hp with ⟨hps, hp2⟩
          exact Finset.mem_powersetCard.mpr ⟨fun a ha ↦ h.subset_ground _ hsS (hps ha), hp2⟩
        have huniq := h.pair_cover p hpUniv
        have hs_eq : Classical.choose (ExistsUnique.exists huniq) = s := by
          apply ExistsUnique.unique huniq
          · exact Classical.choose_spec (ExistsUnique.exists huniq)
          · exact ⟨hsS, (Finset.mem_powersetCard.mp hp).1⟩
        cases hs_eq
        simp [pairToBlockPair]
  calc
    Nat.choose n 2 = Nat.card {p : Finset (Fin n) // p ∈ Finset.univ.powersetCard 2} := by
      rw [Nat.card_eq_finsetCard (Finset.univ.powersetCard 2), Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
    _ = Nat.card
          (Sigma fun s : {s : Finset (Fin n) // s ∈ S} ↦
            {p : Finset (Fin n) // p ∈ s.1.powersetCard 2}) := by
      exact Nat.card_congr (Equiv.ofBijective pairToBlockPair hbij)
    _ = ∑ s : {s : Finset (Fin n) // s ∈ S},
          Nat.card {p : Finset (Fin n) // p ∈ s.1.powersetCard 2} := by
      rw [Nat.card_sigma]
    _ = ∑ _s : {s : Finset (Fin n) // s ∈ S}, 3 := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      rw [Nat.card_eq_finsetCard (s.1.powersetCard 2), Finset.card_powersetCard, h.sized s.2]
      norm_num
    _ = 3 * Nat.card {s : Finset (Fin n) // s ∈ S} := by
      simp [Nat.mul_comm]

/-- Helper for Theorem 2.2: fixing one point partitions the remaining points into the pairs that
appear with it in the unique covering blocks. -/
lemma predCount_eq_two_mul_blocksThrough {n : ℕ} {S : Set (Finset (Fin n))}
    (h : IsOn Finset.univ S) (x : Fin n) :
    n - 1 = 2 * Nat.card {s : Finset (Fin n) // s ∈ S ∧ x ∈ s} := by
  classical
  let pointToBlockPoint :
      {y : Fin n // y ≠ x} →
        Sigma fun s : {s : Finset (Fin n) // s ∈ S ∧ x ∈ s} ↦
          {y : Fin n // y ∈ s.1.erase x} := fun y ↦
      let p : Finset (Fin n) := insert x ({y.1} : Finset (Fin n))
      have hp : p ∈ Finset.univ.powersetCard 2 := by
        refine Finset.mem_powersetCard.mpr ?_
        refine ⟨by simp, ?_⟩
        have hx_not_mem : x ∉ ({y.1} : Finset (Fin n)) := by
          simpa [Finset.mem_singleton, eq_comm] using y.2
        rw [Finset.card_insert_of_notMem hx_not_mem, Finset.card_singleton]
      let hs := Classical.choose (ExistsUnique.exists (h.pair_cover p hp))
      let hhs := Classical.choose_spec (ExistsUnique.exists (h.pair_cover p hp))
      have hx_mem : x ∈ hs := hhs.2 (by simp [p])
      have hy_mem : y.1 ∈ hs := hhs.2 (by simp [p])
      ⟨⟨hs, hhs.1, hx_mem⟩, ⟨y.1, Finset.mem_erase.mpr ⟨y.2, hy_mem⟩⟩⟩
  have hbij : Function.Bijective pointToBlockPoint := by
    constructor
    · intro y z hyz
      exact Subtype.ext (congrArg (fun sp ↦ sp.2.1) hyz)
    · intro sp
      rcases sp with ⟨⟨s, hsS, hxS⟩, ⟨y, hy⟩⟩
      refine ⟨⟨y, (Finset.mem_erase.mp hy).1⟩, ?_⟩
      -- The chosen block is unique because `{x, y}` is covered exactly once.
      have hpUniv : insert x ({y} : Finset (Fin n)) ∈ Finset.univ.powersetCard 2 := by
        refine Finset.mem_powersetCard.mpr ?_
        refine ⟨by simp, ?_⟩
        rw [Finset.card_insert_of_notMem]
        · simp
        · simpa [eq_comm] using (Finset.mem_erase.mp hy).1
      have huniq := h.pair_cover (insert x ({y} : Finset (Fin n))) hpUniv
      have hs_eq : Classical.choose (ExistsUnique.exists huniq) = s := by
        apply ExistsUnique.unique huniq
        · exact Classical.choose_spec (ExistsUnique.exists huniq)
        · refine ⟨hsS, ?_⟩
          intro a ha
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact hxS
          · exact Finset.mem_of_mem_erase hy
      cases hs_eq
      simp [pointToBlockPoint]
  calc
    n - 1 = Nat.card {y : Fin n // y ≠ x} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun y : Fin n ↦ y = x),
        Fintype.card_fin]
      simp
    _ = Nat.card
          (Sigma fun s : {s : Finset (Fin n) // s ∈ S ∧ x ∈ s} ↦
            {y : Fin n // y ∈ s.1.erase x}) := by
      exact Nat.card_congr (Equiv.ofBijective pointToBlockPoint hbij)
    _ = ∑ s : {s : Finset (Fin n) // s ∈ S ∧ x ∈ s},
          Nat.card {y : Fin n // y ∈ s.1.erase x} := by
      rw [Nat.card_sigma]
    _ = ∑ _s : {s : Finset (Fin n) // s ∈ S ∧ x ∈ s}, 2 := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      rw [Nat.card_eq_finsetCard (s.1.erase x), Finset.card_erase_of_mem s.2.2, h.sized s.2.1]
    _ = 2 * Nat.card {s : Finset (Fin n) // s ∈ S ∧ x ∈ s} := by
      simp [Nat.mul_comm]

/-- Helper for Theorem 2.2: the pair count shows `6 ∣ n * (n - 1)`. -/
lemma sixDvdMulPred_of_isOn {n : ℕ} {S : Set (Finset (Fin n))}
    (h : IsOn Finset.univ S) :
    6 ∣ n * (n - 1) := by
  -- Count all pairs globally, then clear the factor `2` from `choose n 2`.
  refine ⟨Nat.card {s : Finset (Fin n) // s ∈ S}, ?_⟩
  have hdouble : 2 * Nat.choose n 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd : n * (n - 1) / 2 * 2 = n * (n - 1))
  calc
    n * (n - 1) = 2 * Nat.choose n 2 := hdouble.symm
    _ = 2 * (3 * Nat.card {s : Finset (Fin n) // s ∈ S}) := by
      rw [pairCount_eq_three_mul_blocks h]
    _ = (2 * 3) * Nat.card {s : Finset (Fin n) // s ∈ S} := by
      rw [Nat.mul_assoc]
    _ = 6 * Nat.card {s : Finset (Fin n) // s ∈ S} := by
      norm_num

/-- Helper for Theorem 2.2: fixing one point shows that `n - 1` is even. -/
lemma twoDvdPred_of_isOn {n : ℕ} {S : Set (Finset (Fin n))}
    (hn : 0 < n) (h : IsOn Finset.univ S) :
    2 ∣ n - 1 := by
  let x : Fin n := ⟨0, hn⟩
  -- Count the points paired with `x`; each covering block through `x` contributes exactly two.
  exact ⟨Nat.card {s : Finset (Fin n) // s ∈ S ∧ x ∈ s}, predCount_eq_two_mul_blocksThrough h x⟩

/-- Helper for Theorem 2.2: the two divisibility conditions force the admissible congruence
classes modulo `6`. -/
lemma modEqOneOrThree_of_divisibilityData {n : ℕ}
    (hn : 0 < n) (hsix : 6 ∣ n * (n - 1)) (htwo : 2 ∣ n - 1) :
    n ≡ 1 [MOD 6] ∨ n ≡ 3 [MOD 6] := by
  have hthree : 3 ∣ n * (n - 1) := dvd_trans (by decide : 3 ∣ 6) hsix
  rcases hthree with ⟨a, ha⟩
  rcases htwo with ⟨b, hb⟩
  have hn : n = 2 * b + 1 := by
    omega
  have hbdecomp : b % 3 + 3 * (b / 3) = b := Nat.mod_add_div b 3
  have hb_lt : b % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hmod : b % 3
  · have hnmod : n % 6 = 1 := by
      omega
    left
    simpa [hnmod] using (Nat.mod_modEq n 6).symm
  · have hnmod : n % 6 = 3 := by
      omega
    right
    simpa [hnmod] using (Nat.mod_modEq n 6).symm
  · exfalso
    have hnform : n = 6 * (b / 3) + 5 := by
      omega
    have hprodmod : (n * (n - 1)) % 3 = 2 := by
      rw [hnform]
      simp [Nat.add_mod, Nat.mul_mod]
    rw [ha] at hprodmod
    simp at hprodmod

/-- Helper for Theorem 2.2: the `1 mod 6` congruence class rewrites as `1 + 6k`. -/
lemma exists_eq_one_add_six_mul_of_modEq_one {n : ℕ} (hmod : n ≡ 1 [MOD 6]) :
    ∃ k : ℕ, n = 1 + 6 * k := by
  have hle : 1 ≤ n := by
    -- Rewriting through the division algorithm makes the lower bound explicit.
    have hmod' : n % 6 = 1 := by
      simpa [Nat.ModEq] using hmod
    rw [← Nat.mod_add_div n 6, hmod']
    omega
  exact (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm

/-- Helper for Theorem 2.2: the `3 mod 6` congruence class rewrites as `3 + 6k`. -/
lemma exists_eq_three_add_six_mul_of_modEq_three {n : ℕ} (hmod : n ≡ 3 [MOD 6]) :
    ∃ k : ℕ, n = 3 + 6 * k := by
  have hle : 3 ≤ n := by
    -- Rewriting through the division algorithm makes the lower bound explicit.
    have hmod' : n % 6 = 3 := by
      simpa [Nat.ModEq] using hmod
    rw [← Nat.mod_add_div n 6, hmod']
    omega
  exact (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm

/-- Helper for Theorem 2.2: the order-one system is the empty block family on `Fin 1`. -/
lemma existsOnFin_one :
    ∃ S : Set (Finset (Fin 1)), IsOn Finset.univ S := by
  classical
  refine ⟨∅, IsOn.ofSubsetGroundSizedAndPairCover ?_ ?_ ?_⟩
  · -- No block belongs to the empty family.
    intro s hs
    simp at hs
  · -- Uniformity is vacuous because the family is empty.
    intro s hs
    simp at hs
  · -- There are no `2`-subsets of a singleton ground set.
    intro p hp
    have hp_card : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
    have hp_le : p.card ≤ 1 := by
      exact le_trans (Finset.card_le_univ p) (by simp)
    omega

/-- Helper for Theorem 2.2: every order congruent to `1` modulo `6` should admit a Steiner triple
system on the canonical ground set `Fin n`. -/
theorem existsOnFin_of_modEq_one {n : ℕ} (hmod : n ≡ 1 [MOD 6]) :
    ∃ S : Set (Finset (Fin n)), IsOn Finset.univ S := by
  obtain ⟨k, hk⟩ := exists_eq_one_add_six_mul_of_modEq_one hmod
  rcases k with _ | k
  · -- The base case `n = 1` is handled directly by the empty-family Steiner system.
    rw [hk]
    simpa using existsOnFin_one
  · -- Route correction: the nontrivial `1 mod 6` branch is now only arithmetic plus transport
    -- from the Skolem model, so the remaining blocker is the model theorem itself.
    exact existsOnFin_of_cardEq (skolemExistsOnSucc k) (by
      -- The model type has exactly `6 * (k + 1) + 1` points, which matches the branch normal form.
      rw [Fintype.card_option, Fintype.card_prod, ZMod.card, Fintype.card_fin, hk]
      omega)

/-- Helper for Theorem 2.2: every order congruent to `3` modulo `6` should admit a Steiner triple
system on the canonical ground set `Fin n`. -/
theorem existsOnFin_of_modEq_three {n : ℕ} (hmod : n ≡ 3 [MOD 6]) :
    ∃ S : Set (Finset (Fin n)), IsOn Finset.univ S := by
  obtain ⟨k, hk⟩ := exists_eq_three_add_six_mul_of_modEq_three hmod
  -- Route correction: this branch is now only arithmetic plus transport from the Bose model, so
  -- the remaining blocker is the explicit model theorem rather than a direct `Fin n` construction.
  exact existsOnFin_of_cardEq (boseExistsOn k) (by
    -- The Bose model type has exactly `3 * (2 * k + 1) = 3 + 6k` points.
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin, hk]
    omega)

/-- Helper for Theorem 2.2: the admissible congruence classes dispatch to the corresponding
canonical `Fin n` construction theorem. -/
theorem existsOnFin_of_modEq {n : ℕ} (hmod : n ≡ 1 [MOD 6] ∨ n ≡ 3 [MOD 6]) :
    ∃ S : Set (Finset (Fin n)), IsOn Finset.univ S := by
  -- The wrapper theorem only performs the residue-class split; the branch constructions carry
  -- the genuine combinatorial content.
  rcases hmod with hmod | hmod
  · exact existsOnFin_of_modEq_one hmod
  · exact existsOnFin_of_modEq_three hmod

/-- Theorem 2.2 (Existence of Steiner triple systems): a Steiner triple system of order `n`
exists if and only if `n ≡ 1 [MOD 6]` or `n ≡ 3 [MOD 6]`. -/
theorem existsOfOrder_iff_modEq (n : ℕ) (hn : 0 < n) :
    (∃ S : Set (Finset (Fin n)), IsOfOrder n Finset.univ S) ↔
      n ≡ 1 [MOD 6] ∨ n ≡ 3 [MOD 6] := by
  constructor
  · rintro ⟨S, hS⟩
    have hOn : IsOn Finset.univ S := (isOfOrder_univ_iff_isOn.mp hS)
    -- The source proof first extracts the two counting divisibility invariants.
    have hsix : 6 ∣ n * (n - 1) := sixDvdMulPred_of_isOn hOn
    have htwo : 2 ∣ n - 1 := twoDvdPred_of_isOn hn hOn
    -- The arithmetic closing step is isolated so the main theorem stays flat.
    exact modEqOneOrThree_of_divisibilityData hn hsix htwo
  · intro hmod
    -- Route correction: the source proof delegates the converse to an external existence theorem,
    -- so the main theorem now only wraps the canonical `IsOn` witness back into `IsOfOrder`.
    rcases existsOnFin_of_modEq hmod with ⟨S, hS⟩
    exact ⟨S, IsOfOrder.ofCardEqAndIsOn (by simp) hS⟩

/-- Existence of a Steiner triple system on the canonical ground set `Fin n`, stated directly
with the primitive owner `IsOn`. -/
theorem existsOnFin_iff_modEq (n : ℕ) (hn : 0 < n) :
    (∃ S : Set (Finset (Fin n)), IsOn Finset.univ S) ↔
      n ≡ 1 [MOD 6] ∨ n ≡ 3 [MOD 6] := by
  simpa [isOfOrder_univ_iff_isOn] using existsOfOrder_iff_modEq n hn

end SteinerTripleSystem

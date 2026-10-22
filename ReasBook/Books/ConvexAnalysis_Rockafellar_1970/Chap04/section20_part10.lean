/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part9

open scoped BigOperators Pointwise

section Chap04
section Section20

/-- Helper for Theorem 20.2: classical extraction of a contains-right separator witness
from the negation of its negation. -/
lemma helperForTheorem_20_2_exists_contains_right_separator_of_not_no_contains_right
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hNotNoContainsRight :
      ¬ ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H := by
  classical
  exact Classical.not_not.mp hNotNoContainsRight

/-- Helper for Theorem 20.2: from a proper separator that contains `C₂`, extract oriented
normal/level data together with a strict left-side witness. -/
lemma helperForTheorem_20_2_oriented_data_of_contains_right_separator
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hContainsRight :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H) :
    ∃ b : Fin n → ℝ, ∃ β : ℝ,
      b ≠ 0 ∧
        (∃ x : Fin n → ℝ, x ∈ C₁ ∧ β < x ⬝ᵥ b) ∧
          (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b = β) ∧
            (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b ≤ β) := by
  rcases hContainsRight with ⟨H, hHsep, hC₂subsetH⟩
  rcases hyperplaneSeparatesProperly_oriented n H C₁ C₂ hHsep with
    ⟨b, β, hb0, hHdef, hC₁ge, hC₂le, hnotBoth⟩
  have hC₁notSubsetH : ¬ C₁ ⊆ H := by
    intro hC₁subsetH
    exact hnotBoth ⟨hC₁subsetH, hC₂subsetH⟩
  rcases Set.not_subset.mp hC₁notSubsetH with ⟨x, hxC₁, hxNotH⟩
  have hxNe : x ⬝ᵥ b ≠ β := by
    intro hxEq
    have hxH : x ∈ H := by
      simpa [hHdef, hxEq]
    exact hxNotH hxH
  have hxGt : β < x ⬝ᵥ b := by
    exact lt_of_le_of_ne (hC₁ge x hxC₁) (by simpa [eq_comm] using hxNe)
  have hC₂eqLevel : ∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b = β := by
    intro y hyC₂
    have hyH : y ∈ H := hC₂subsetH hyC₂
    simpa [hHdef] using hyH
  exact ⟨b, β, hb0, ⟨x, hxC₁, hxGt⟩, hC₂eqLevel, hC₂le⟩

/-- Helper for Theorem 20.2: oriented full data imply the level-hyperplane subset and
left noncontainment facts. -/
lemma helperForTheorem_20_2_level_subset_and_left_not_subset_of_oriented_full_data
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    {b : Fin n → ℝ} {β : ℝ}
    (hData :
      (∃ x : Fin n → ℝ, x ∈ C₁ ∧ β < x ⬝ᵥ b) ∧
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b = β)) :
    C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β} ∧
      ¬ C₁ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β} := by
  rcases hData with ⟨hleftWitness, hC₂eqLevel⟩
  constructor
  · intro y hyC₂
    exact hC₂eqLevel y hyC₂
  · intro hC₁subsetLevel
    rcases hleftWitness with ⟨x, hxC₁, hxGt⟩
    have hxEq : x ⬝ᵥ b = β := hC₁subsetLevel hxC₁
    have : β < β := by simpa [hxEq] using hxGt
    exact (lt_irrefl β) this

/-- Helper for Theorem 20.2: projection of oriented full data onto the right-subset
level-hyperplane clause. -/
lemma helperForTheorem_20_2_subset_level_hyperplane_of_oriented_contains_right_data
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    {b : Fin n → ℝ} {β : ℝ}
    (hData :
      (∃ x : Fin n → ℝ, x ∈ C₁ ∧ β < x ⬝ᵥ b) ∧
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b = β)) :
    C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β} := by
  exact
    (helperForTheorem_20_2_level_subset_and_left_not_subset_of_oriented_full_data
      (n := n) (C₁ := C₁) (C₂ := C₂) (b := b) (β := β) hData).1

/-- Helper for Theorem 20.2: projection of oriented full data onto the left-not-subset
level-hyperplane clause. -/
lemma helperForTheorem_20_2_not_subset_level_hyperplane_of_oriented_contains_right_data
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    {b : Fin n → ℝ} {β : ℝ}
    (hData :
      (∃ x : Fin n → ℝ, x ∈ C₁ ∧ β < x ⬝ᵥ b) ∧
        (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b = β)) :
    ¬ C₁ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β} := by
  exact
    (helperForTheorem_20_2_level_subset_and_left_not_subset_of_oriented_full_data
      (n := n) (C₁ := C₁) (C₂ := C₂) (b := b) (β := β) hData).2

/-- Helper for Theorem 20.2: from level-subset and left-not-subset data, orient
the normal so the strict side is `β' < x ⬝ᵥ b'`. -/
lemma helperForTheorem_20_2_exists_oriented_full_and_level_data_of_level_subset_and_left_not_subset
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    {b : Fin n → ℝ} {β : ℝ}
    (hb0 : b ≠ 0)
    (hC₂subsetLevel : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β})
    (hC₁notSubsetLevel : ¬ C₁ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β}) :
    ∃ b' : Fin n → ℝ, ∃ β' : ℝ,
      b' ≠ 0 ∧
        (∃ x : Fin n → ℝ, x ∈ C₁ ∧ β' < x ⬝ᵥ b') ∧
          (∀ y : Fin n → ℝ, y ∈ C₂ → y ⬝ᵥ b' = β') ∧
            C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b' = β'} ∧
              ¬ C₁ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b' = β'} := by
  rcases Set.not_subset.mp hC₁notSubsetLevel with ⟨x, hxC₁, hxNotLevel⟩
  have hxNe : x ⬝ᵥ b ≠ β := by
    intro hxEq
    exact hxNotLevel hxEq
  rcases lt_or_gt_of_ne hxNe with hxLt | hxGt
  · refine ⟨-b, -β, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using (neg_ne_zero.mpr hb0)
    · refine ⟨x, hxC₁, ?_⟩
      have : -β < -(x ⬝ᵥ b) := by simpa using (neg_lt_neg hxLt)
      simpa [dotProduct_neg] using this
    · intro y hyC₂
      have hyEq : y ⬝ᵥ b = β := hC₂subsetLevel hyC₂
      simpa [dotProduct_neg, hyEq]
    · intro y hyC₂
      have hyEq : y ⬝ᵥ b = β := hC₂subsetLevel hyC₂
      simpa [dotProduct_neg, hyEq]
    · intro hC₁subsetNegLevel
      have hxEqNeg : x ⬝ᵥ (-b) = -β := hC₁subsetNegLevel hxC₁
      have hxEq : x ⬝ᵥ b = β := by
        have : -(x ⬝ᵥ b) = -β := by simpa [dotProduct_neg] using hxEqNeg
        exact neg_injective this
      have : x ⬝ᵥ b < x ⬝ᵥ b := by simpa [hxEq] using hxLt
      exact (lt_irrefl (x ⬝ᵥ b)) this
  · refine ⟨b, β, hb0, ?_, ?_, hC₂subsetLevel, hC₁notSubsetLevel⟩
    · exact ⟨x, hxC₁, hxGt⟩
    · intro y hyC₂
      exact hC₂subsetLevel hyC₂

/-- Helper for Theorem 20.2: in the no-contains-right branch, obtain a proper separator
that does not contain `C₂`. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_no_contains_right
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hNoContainsRight :
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  have hC₁conv : Convex ℝ C₁ :=
    helperForTheorem_19_1_polyhedral_isConvex n C₁ hC₁poly
  have hDisjRi : Disjoint (intrinsicInterior ℝ C₁) (intrinsicInterior ℝ C₂) := by
    refine Set.disjoint_left.2 ?_
    intro x hxriC₁ hxriC₂
    have hxC₁ : x ∈ C₁ := intrinsicInterior_subset hxriC₁
    have hxInter : x ∈ C₁ ∩ intrinsicInterior ℝ C₂ := ⟨hxC₁, hxriC₂⟩
    have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
      simpa [hleftRiEmpty] using hxInter
    exact hxEmpty.elim
  have hSepExists : ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ := by
    exact
      (exists_hyperplaneSeparatesProperly_iff_disjoint_intrinsicInterior
        n C₁ C₂ hC₁ne hC₂ne hC₁conv hC₂conv).2 hDisjRi
  rcases hSepExists with ⟨H, hHsep⟩
  have hC₂notSubsetH : ¬ C₂ ⊆ H := by
    intro hC₂subsetH
    exact hNoContainsRight ⟨H, hHsep, hC₂subsetH⟩
  exact ⟨H, hHsep, hC₂notSubsetH⟩

/-- Helper for Theorem 20.2: in the no-contains-right branch, obtain a proper separator
that does not contain `C₂` by combining Theorem 11.3 existence with the branch hypothesis. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_level_subset_and_left_not_subset_under_left_ri_empty_of_no_contains_right
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hNoContainsRight :
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H)
    {b : Fin n → ℝ} {β : ℝ}
    (_hb0 : b ≠ 0)
    (_hC₂subsetLevel : C₂ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β})
    (_hC₁notSubsetLevel : ¬ C₁ ⊆ {y : Fin n → ℝ | y ⬝ᵥ b = β}) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  exact
    helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_no_contains_right
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hNoContainsRight

/-- Helper for Theorem 20.2: if no noncontainment separator exists, then no-contains-right
is impossible. -/
lemma helperForTheorem_20_2_not_not_contains_right_of_no_noncontainment_under_left_ri_empty_polyLeft
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hNoNoncontainment :
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) :
    ¬ ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H := by
  intro hNoContainsRight
  have hNoncontainment :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H :=
    helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_no_contains_right
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hNoContainsRight
  exact hNoNoncontainment hNoncontainment

/-- Helper for Theorem 20.2: under left-`ri` emptiness and polyhedral-left hypotheses,
absence of noncontainment separators forces existence of a contains-right separator. -/
lemma helperForTheorem_20_2_exists_contains_right_of_no_noncontainment_under_left_ri_empty_polyLeft
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hNoNoncontainment :
      ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H := by
  have hNotNoContainsRight :
      ¬ ¬ ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H :=
    helperForTheorem_20_2_not_not_contains_right_of_no_noncontainment_under_left_ri_empty_polyLeft
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hNoNoncontainment
  exact
    helperForTheorem_20_2_exists_contains_right_separator_of_not_no_contains_right
      (n := n) (C₁ := C₁) (C₂ := C₂) hNotNoContainsRight

/-- Helper for Theorem 20.2: bridge packaging from a contains-right-to-noncontainment
implication into an unconditional noncontainment separator under left-`ri` emptiness. -/
lemma helperForTheorem_20_2_noncontainment_separator_of_left_inter_ri_empty_polyLeft_of_contains_right_bridge
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty) (hC₂ne : C₂.Nonempty)
    (hC₂conv : Convex ℝ C₂)
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hleftRiEmpty : C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)))
    (hContainsRightBridge :
      (∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H) →
        ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H := by
  by_cases hNoncontainment :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H
  · exact hNoncontainment
  · have hContainsRight :
        ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ C₂ ⊆ H :=
      helperForTheorem_20_2_exists_contains_right_of_no_noncontainment_under_left_ri_empty_polyLeft
        (n := n) (C₁ := C₁) (C₂ := C₂)
        hC₁ne hC₂ne hC₂conv hC₁poly hleftRiEmpty hNoncontainment
    exact hContainsRightBridge hContainsRight

/-- Helper for Theorem 20.2: any proper separator not containing `C₂` forces
`C₁ ∩ intrinsicInterior ℝ C₂ = ∅` under convex-right/polyhedral-left hypotheses. -/
lemma helperForTheorem_20_2_inter_empty_of_exists_separator_not_subset_right
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    {hC₂conv : Convex ℝ C₂}
    (hsep :
      ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesProperly n H C₁ C₂ ∧ ¬ C₂ ⊆ H) :
    C₁ ∩ intrinsicInterior ℝ C₂ = (∅ : Set (Fin n → ℝ)) := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro x hxInter
  rcases hsep with ⟨H, hHsep, hC₂notSubsetH⟩
  rcases hyperplaneSeparatesProperly_oriented n H C₁ C₂ hHsep with
    ⟨b, β, hb0, hHdef, hC₁ge, hC₂le, _hnotBoth⟩
  have hxC₁ : x ∈ C₁ := hxInter.1
  have hxriC₂ : x ∈ intrinsicInterior ℝ C₂ := hxInter.2
  have hxC₂ : x ∈ C₂ := intrinsicInterior_subset hxriC₂
  have hxGe : β ≤ x ⬝ᵥ b := hC₁ge x hxC₁
  have hxLe : x ⬝ᵥ b ≤ β := hC₂le x hxC₂
  have hxEq : x ⬝ᵥ b = β := le_antisymm hxLe hxGe
  have hxH : x ∈ H := by simpa [hHdef, hxEq]
  have hHsupport : IsSupportingHyperplane n C₂ H := by
    refine ⟨b, β, hb0, hHdef, ?_, ?_⟩
    · intro y hyC₂
      exact hC₂le y hyC₂
    · exact ⟨x, hxC₂, hxEq⟩
  have hHnontriv : IsNontrivialSupportingHyperplane n C₂ H := ⟨hHsupport, hC₂notSubsetH⟩
  have hSingleSub : ({x} : Set (Fin n → ℝ)) ⊆ C₂ := by
    intro y hy
    have hyEq : y = x := by simpa [Set.mem_singleton_iff] using hy
    simpa [hyEq] using hxC₂
  have hDisjSingle :
      Disjoint ({x} : Set (Fin n → ℝ)) (intrinsicInterior ℝ C₂) := by
    have hiff :=
      exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior
        (n := n) (C := C₂) (D := ({x} : Set (Fin n → ℝ)))
        hC₂conv (Set.singleton_nonempty x) (convex_singleton x) hSingleSub
    refine hiff.1 ?_
    refine ⟨H, hHnontriv, ?_⟩
    intro y hy
    have hyEq : y = x := by simpa [Set.mem_singleton_iff] using hy
    simpa [hyEq] using hxH
  have hxNotRi : x ∉ intrinsicInterior ℝ C₂ := (Set.disjoint_singleton_left).1 hDisjSingle
  exact hxNotRi hxriC₂

/-- Theorem 20.4: Let `C` be a non-empty closed bounded convex set, and let `D`
be a convex set with `C ⊆ interior D`. Then there exists a polyhedral convex
set `P` such that `P ⊆ interior D` and `C ⊆ interior P`. -/
theorem Theorem_20_4
    (n : ℕ) (C D : Set (Fin n → ℝ))
    (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hDconv : Convex ℝ D) (hCD : C ⊆ interior D) :
    ∃ P : Set (Fin n → ℝ),
      IsPolyhedralConvexSet n P ∧ P ⊆ interior D ∧ C ⊆ interior P := by
  haveI : ProperSpace (Fin n → ℝ) := FiniteDimensional.proper ℝ (Fin n → ℝ)
  have hCcompact : IsCompact C := by
    exact (Metric.isCompact_iff_isClosed_bounded).2 ⟨hCclosed, hCbounded⟩
  have hInteriorNhds : interior D ∈ nhdsSet C := by
    exact (isOpen_interior.mem_nhdsSet).2 hCD
  rcases
      Convex.exists_subset_interior_convexHull_finset_of_isCompact
        (s := C) (t := interior D) hCconv hCcompact hInteriorNhds with
    ⟨u, hCsubsetInteriorHull, hHullSubsetInteriorD⟩
  have hUFinite : (((u : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))).Finite := by
    exact (u : Finset (Fin n → ℝ)).finite_toSet
  have hEmptyFinite : (∅ : Set (Fin n → ℝ)).Finite := by
    exact Set.finite_empty
  have hPolyHull : IsPolyhedralConvexSet n (convexHull ℝ ((u : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))) := by
    have hPolyMixed :
        IsPolyhedralConvexSet n
          (mixedConvexHull (((u : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))) (∅ : Set (Fin n → ℝ))) := by
      exact
        helperForTheorem_19_1_mixedConvexHull_polyhedral_of_finite_generators
          (S₀ := (((u : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))))
          (S₁ := (∅ : Set (Fin n → ℝ))) hUFinite hEmptyFinite
    simpa [mixedConvexHull_empty_directions_eq_convexHull] using hPolyMixed
  refine
    ⟨convexHull ℝ ((u : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
      hPolyHull, hHullSubsetInteriorD, hCsubsetInteriorHull⟩


end Section20
end Chap04

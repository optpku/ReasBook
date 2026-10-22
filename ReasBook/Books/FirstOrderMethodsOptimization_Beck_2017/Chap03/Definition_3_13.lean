/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Interval.Finset.Fin

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Definition 3.13 is `source-facing` at the finite-set median set itself. There is no earlier
chapter owner or mathlib owner for this exact notion, so the public root stays `median_set A :
Set ℝ`. The pointwise notion of being a median is expressed directly by membership
`β ∈ median_set A`, and the middle tuple indices below are represented by canonical `Fin.ofNat`
terms rather than local wrapper definitions. -/

/-- Definition 3.13: `median_set A` is the set of real numbers `β`
such that at least half of the elements of the finite nonempty set `A` lie below `β` and at least
half lie above `β`. -/
def median_set (A : Finset ℝ) : Set ℝ :=
  if A.Nonempty then
    {β | A.card ≤ 2 * (A.filter (fun a ↦ a ≤ β)).card} ∩
      {β | A.card ≤ 2 * (A.filter (fun a ↦ β ≤ a)).card}
  else
    ∅

/-- The median set of the empty finite set is empty. -/
@[simp] theorem median_set_empty : median_set (∅ : Finset ℝ) = ∅ := by
  simp [median_set]

/-- For a nonempty finite set, `median_set A` is exactly the intersection of the two defining
counting conditions. -/
theorem median_set_eq_inter_of_nonempty {A : Finset ℝ} (hA : A.Nonempty) :
    median_set A =
      {β | A.card ≤ 2 * (A.filter (fun a ↦ a ≤ β)).card} ∩
        {β | A.card ≤ 2 * (A.filter (fun a ↦ β ≤ a)).card} := by
  simp [median_set, hA]

/-- For a nonempty finite set, membership in `median_set A` means satisfying the two median-count
inequalities. -/
theorem mem_median_set_iff_of_nonempty {A : Finset ℝ} (hA : A.Nonempty) {β : ℝ} :
    β ∈ median_set A ↔
      A.card ≤ 2 * (A.filter (fun a ↦ a ≤ β)).card ∧
        A.card ≤ 2 * (A.filter (fun a ↦ β ≤ a)).card := by
  simp [median_set, hA]

/-- Membership in `median_set A` is equivalent to `A` being nonempty together with the two
median-count inequalities. -/
@[simp] lemma mem_median_set_iff {A : Finset ℝ} {β : ℝ} :
    β ∈ median_set A ↔
      A.Nonempty ∧
        A.card ≤ 2 * (A.filter (fun a ↦ a ≤ β)).card ∧
          A.card ≤ 2 * (A.filter (fun a ↦ β ≤ a)).card := by
  by_cases hA : A.Nonempty <;> simp [median_set, hA]

/-- Helper for Definition 3.13: every value indexed by `Finset.Iic i` lies below any threshold
that is at least `a i`. -/
private lemma imageIic_subset_filter_le {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    {i : Fin n} {β : ℝ} (h : a i ≤ β) :
    Finset.image a (Finset.Iic i) ⊆ (Finset.univ.image a).filter (fun x ↦ x ≤ β) := by
  -- Move from a value in the image back to its index, then compare indices via strict monotonicity.
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
  rw [Finset.mem_filter]
  constructor
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  · exact le_trans ((StrictMono.le_iff_le ha).2 (Finset.mem_Iic.mp hj)) h

/-- Helper for Definition 3.13: every value indexed by `Finset.Ici i` lies above any threshold
that is at most `a i`. -/
private lemma imageIci_subset_filter_ge {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    {i : Fin n} {β : ℝ} (h : β ≤ a i) :
    Finset.image a (Finset.Ici i) ⊆ (Finset.univ.image a).filter (fun x ↦ β ≤ x) := by
  -- The upper median condition uses the same index-to-value comparison,
  -- but in the opposite direction.
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
  rw [Finset.mem_filter]
  constructor
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  · exact le_trans h ((StrictMono.le_iff_le ha).2 (Finset.mem_Ici.mp hj))

/-- Helper for Definition 3.13: if `β < a i`, then every tuple value at most `β` comes from an
index in `Finset.Iio i`. -/
private lemma filterLe_subset_imageIio {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    {i : Fin n} {β : ℝ} (h : β < a i) :
    ((Finset.univ.image a).filter (fun x ↦ x ≤ β)) ⊆ Finset.image a (Finset.Iio i) := by
  -- A value below `a i` must come from an index strictly before `i`.
  intro x hx
  rw [Finset.mem_filter] at hx
  rcases Finset.mem_image.mp hx.1 with ⟨j, -, rfl⟩
  refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
  apply Finset.mem_Iio.mpr
  exact (StrictMono.lt_iff_lt ha).1 (lt_of_le_of_lt hx.2 h)

/-- Helper for Definition 3.13: if `a i < β`, then every tuple value at least `β` comes from an
index in `Finset.Ioi i`. -/
private lemma filterGe_subset_imageIoi {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    {i : Fin n} {β : ℝ} (h : a i < β) :
    ((Finset.univ.image a).filter (fun x ↦ β ≤ x)) ⊆ Finset.image a (Finset.Ioi i) := by
  -- A value above `a i` must come from an index strictly after `i`.
  intro x hx
  rw [Finset.mem_filter] at hx
  rcases Finset.mem_image.mp hx.1 with ⟨j, -, rfl⟩
  refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
  apply Finset.mem_Ioi.mpr
  exact (StrictMono.lt_iff_lt ha).1 (lt_of_lt_of_le h hx.2)

/-- Helper for Definition 3.13: a strictly monotone image preserves the cardinality of any finite
set of indices. -/
private lemma card_image_eq_card_of_strictMono {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    (s : Finset (Fin n)) :
    (Finset.image a s).card = s.card := by
  -- Strict monotonicity gives injectivity, so no image points are identified.
  rw [Finset.card_image_of_injective _ ha.injective]

-- Proof sketch: for a strictly increasing tuple of odd length, exactly `m + 1` entries lie below
-- the middle element and exactly `m + 1` entries lie above it, while any other candidate fails
-- one of the two counting inequalities.
/-- The odd-case characterization from Definition 3.13: for a strictly increasing odd tuple,
the median set is the singleton containing the middle entry. -/
theorem median_set_eq_singleton_of_strictMono_odd (m : ℕ) (a : Fin (2 * m + 1) → ℝ)
    (ha : StrictMono a) :
    median_set (Finset.univ.image a) = ({a (Fin.ofNat (2 * m + 1) m)} : Set ℝ) := by
  have hm_lt : m < 2 * m + 1 := by
    omega
  let mid : Fin (2 * m + 1) := ⟨m, hm_lt⟩
  have hA : (Finset.univ.image a).Nonempty := by
    -- The image is nonempty because it contains the middle entry.
    exact ⟨a mid, Finset.mem_image.mpr ⟨mid, Finset.mem_univ _, rfl⟩⟩
  have hcardA : (Finset.univ.image a).card = 2 * m + 1 := by
    -- Strict monotonicity keeps all `2 * m + 1` indices distinct in the image.
    simpa using
      (Finset.card_image_of_injective (Finset.univ : Finset (Fin (2 * m + 1))) ha.injective)
  have hcardIic : (Finset.image a (Finset.Iic mid)).card = m + 1 := by
    -- The lower closed interval has exactly `m + 1` indices.
    rw [card_image_eq_card_of_strictMono ha, Fin.card_Iic]
  have hcardIci : (Finset.image a (Finset.Ici mid)).card = m + 1 := by
    -- The upper closed interval also has exactly `m + 1` indices.
    rw [card_image_eq_card_of_strictMono ha, Fin.card_Ici]
    simp [mid]
    omega
  have hcardIio : (Finset.image a (Finset.Iio mid)).card = m := by
    -- The strict lower interval has exactly `m` indices.
    rw [card_image_eq_card_of_strictMono ha, Fin.card_Iio]
  have hcardIoi : (Finset.image a (Finset.Ioi mid)).card = m := by
    -- The strict upper interval has exactly `m` indices.
    rw [card_image_eq_card_of_strictMono ha, Fin.card_Ioi]
    simp [mid]
    omega
  have hmain : median_set (Finset.univ.image a) = ({a mid} : Set ℝ) := by
    ext β
    constructor
    · intro hβ
      rw [Set.mem_singleton_iff]
      -- Use the median count inequalities to exclude both sides
      -- of the middle value.
      have hmedian := (mem_median_set_iff_of_nonempty hA).1 hβ
      by_cases hlt : β < a mid
      · have hcount_le : ((Finset.univ.image a).filter (fun x ↦ x ≤ β)).card ≤ m := by
          -- Values below `β` come from indices strictly before the middle.
          calc
            ((Finset.univ.image a).filter (fun x ↦ x ≤ β)).card
                ≤ (Finset.image a (Finset.Iio mid)).card :=
                  Finset.card_le_card (filterLe_subset_imageIio ha hlt)
            _ = m := hcardIio
        omega
      · by_cases hgt : a mid < β
        · have hcount_le : ((Finset.univ.image a).filter (fun x ↦ β ≤ x)).card ≤ m := by
            -- Values above `β` come from indices strictly after the middle.
            calc
              ((Finset.univ.image a).filter (fun x ↦ β ≤ x)).card
                  ≤ (Finset.image a (Finset.Ioi mid)).card :=
                    Finset.card_le_card (filterGe_subset_imageIoi ha hgt)
              _ = m := hcardIoi
          omega
        · exact le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
    · intro hβ
      rw [Set.mem_singleton_iff] at hβ
      subst hβ
      -- The middle value satisfies both counting inequalities because
      -- each closed side contains `m + 1` indices.
      refine (mem_median_set_iff_of_nonempty hA).2 ?_
      constructor
      · have hcount_ge : m + 1 ≤ ((Finset.univ.image a).filter (fun x ↦ x ≤ a mid)).card := by
          calc
            m + 1 = (Finset.image a (Finset.Iic mid)).card := hcardIic.symm
            _ ≤ ((Finset.univ.image a).filter (fun x ↦ x ≤ a mid)).card :=
              Finset.card_le_card (imageIic_subset_filter_le ha le_rfl)
        omega
      · have hcount_ge : m + 1 ≤ ((Finset.univ.image a).filter (fun x ↦ a mid ≤ x)).card := by
          calc
            m + 1 = (Finset.image a (Finset.Ici mid)).card := hcardIci.symm
            _ ≤ ((Finset.univ.image a).filter (fun x ↦ a mid ≤ x)).card :=
              Finset.card_le_card (imageIci_subset_filter_ge ha le_rfl)
        omega
  simpa [mid, Fin.ofNat, Nat.mod_eq_of_lt hm_lt] using hmain

-- Proof sketch: for a strictly increasing tuple of even length `2 * (m + 1)`, the two counting
-- inequalities hold exactly for those `β` between the two middle entries `a_m` and `a_{m+1}`.
/-- The even-case characterization from Definition 3.13: for a strictly increasing even tuple,
the median set is the closed interval between the two middle entries. -/
theorem median_set_eq_Icc_of_strictMono_even (m : ℕ) (a : Fin (2 * (m + 1)) → ℝ)
    (ha : StrictMono a) :
    median_set (Finset.univ.image a) =
      Set.Icc (a (Fin.ofNat (2 * (m + 1)) m)) (a (Fin.ofNat (2 * (m + 1)) (m + 1))) := by
  have hleft_lt : m < 2 * (m + 1) := by
    omega
  have hright_lt : m + 1 < 2 * (m + 1) := by
    omega
  let left : Fin (2 * (m + 1)) := ⟨m, hleft_lt⟩
  let right : Fin (2 * (m + 1)) := ⟨m + 1, hright_lt⟩
  have hA : (Finset.univ.image a).Nonempty := by
    -- The image is nonempty because it contains the left middle entry.
    exact ⟨a left, Finset.mem_image.mpr ⟨left, Finset.mem_univ _, rfl⟩⟩
  have hcardA : (Finset.univ.image a).card = 2 * (m + 1) := by
    -- Distinct indices stay distinct under a strictly monotone map.
    simpa using
      (Finset.card_image_of_injective (Finset.univ : Finset (Fin (2 * (m + 1)))) ha.injective)
  have hcardIic : (Finset.image a (Finset.Iic left)).card = m + 1 := by
    -- The left closed half already contributes `m + 1` values below any `β ≥ a left`.
    rw [card_image_eq_card_of_strictMono ha, Fin.card_Iic]
  have hcardIci : (Finset.image a (Finset.Ici right)).card = m + 1 := by
    -- The right closed half contributes `m + 1` values above any `β ≤ a right`.
    rw [card_image_eq_card_of_strictMono ha, Fin.card_Ici]
    simp [right]
    omega
  have hcardIio : (Finset.image a (Finset.Iio left)).card = m := by
    -- Falling strictly below the interval leaves at most the first `m` entries.
    rw [card_image_eq_card_of_strictMono ha, Fin.card_Iio]
  have hcardIoi : (Finset.image a (Finset.Ioi right)).card = m := by
    -- Rising strictly above the interval leaves at most the last `m` entries.
    rw [card_image_eq_card_of_strictMono ha, Fin.card_Ioi]
    simp [right]
    omega
  have hmain : median_set (Finset.univ.image a) = Set.Icc (a left) (a right) := by
    ext β
    constructor
    · intro hβ
      rw [Set.mem_Icc]
      -- The median inequalities force `β` to stay inside
      -- the closed interval between the middle entries.
      have hmedian := (mem_median_set_iff_of_nonempty hA).1 hβ
      constructor
      · by_contra hleft
        have hβleft : β < a left := lt_of_not_ge hleft
        have hcount_le : ((Finset.univ.image a).filter (fun x ↦ x ≤ β)).card ≤ m := by
          calc
            ((Finset.univ.image a).filter (fun x ↦ x ≤ β)).card
                ≤ (Finset.image a (Finset.Iio left)).card :=
                  Finset.card_le_card (filterLe_subset_imageIio ha hβleft)
            _ = m := hcardIio
        omega
      · by_contra hright
        have hrightβ : a right < β := lt_of_not_ge hright
        have hcount_le : ((Finset.univ.image a).filter (fun x ↦ β ≤ x)).card ≤ m := by
          calc
            ((Finset.univ.image a).filter (fun x ↦ β ≤ x)).card
                ≤ (Finset.image a (Finset.Ioi right)).card :=
                  Finset.card_le_card (filterGe_subset_imageIoi ha hrightβ)
            _ = m := hcardIoi
        omega
    · intro hβ
      rw [Set.mem_Icc] at hβ
      -- Any `β` inside the interval sees at least `m + 1` entries on each side.
      refine (mem_median_set_iff_of_nonempty hA).2 ?_
      constructor
      · have hcount_ge : m + 1 ≤ ((Finset.univ.image a).filter (fun x ↦ x ≤ β)).card := by
          calc
            m + 1 = (Finset.image a (Finset.Iic left)).card := hcardIic.symm
            _ ≤ ((Finset.univ.image a).filter (fun x ↦ x ≤ β)).card :=
              Finset.card_le_card (imageIic_subset_filter_le ha hβ.1)
        omega
      · have hcount_ge : m + 1 ≤ ((Finset.univ.image a).filter (fun x ↦ β ≤ x)).card := by
          calc
            m + 1 = (Finset.image a (Finset.Ici right)).card := hcardIci.symm
            _ ≤ ((Finset.univ.image a).filter (fun x ↦ β ≤ x)).card :=
              Finset.card_le_card (imageIci_subset_filter_ge ha hβ.2)
        omega
  simpa [left, right, Fin.ofNat, Nat.mod_eq_of_lt hleft_lt, Nat.mod_eq_of_lt hright_lt] using hmain

end

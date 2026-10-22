/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Finset
open scoped BigOperators ENNReal

universe u

variable {Ω : Type u} {C : Set (Set Ω)}

section InclusionExclusionHelpers

variable {ι : Type*} [DecidableEq ι]

/-- Helper for Theorem 1.33: the binary inclusion-exclusion identity for a content becomes an
equality in `ℝ` after passing to `ENNReal.toReal` under a finiteness hypothesis. -/
lemma toReal_addContent_union_add_inter (hC : IsSetRing C) (μ : AddContent ℝ≥0∞ C)
    {A B : Set Ω} (hA : A ∈ C) (hB : B ∈ C) (hfinite : μ (A ∪ B) < ⊤) :
    ENNReal.toReal (μ (A ∪ B)) + ENNReal.toReal (μ (A ∩ B)) =
      ENNReal.toReal (μ A) + ENNReal.toReal (μ B) := by
  -- First express `μ (A ∪ B)` and `μ B` through the disjoint decompositions using `B \ A`.
  have h_union :
      μ (A ∪ B) = μ A + μ (B \ A) := by
    have hset : A ∪ B = A ∪ (B \ A) := by
      ext x
      by_cases hx : x ∈ A <;> simp [hx]
    rw [hset, MeasureTheory.addContent_union hC hA (hC.diff_mem hB hA) disjoint_sdiff_right]
  have h_right :
      μ B = μ (A ∩ B) + μ (B \ A) := by
    have h_right' :
        μ ((A ∩ B) ∪ (B \ A)) = μ (A ∩ B) + μ (B \ A) := by
      exact MeasureTheory.addContent_union hC (hC.inter_mem hA hB) (hC.diff_mem hB hA)
        (by
          rw [Set.disjoint_iff_inter_eq_empty]
          ext x
          constructor
          · intro hx
            rcases hx with ⟨hxAB, hxDiff⟩
            exact (hxDiff.2 hxAB.1).elim
          · intro hx
            simp at hx)
    have hset : B = (A ∩ B) ∪ (B \ A) := by
      ext x
      by_cases hx : x ∈ A <;> simp [hx]
    rw [← hset] at h_right'
    exact h_right'
  have h_add :
      μ (A ∪ B) + μ (A ∩ B) = μ A + μ B := by
    calc
      μ (A ∪ B) + μ (A ∩ B)
          = (μ A + μ (B \ A)) + μ (A ∩ B) := by rw [h_union]
      _ = μ A + (μ (A ∩ B) + μ (B \ A)) := by simp [add_left_comm, add_comm]
      _ = μ A + μ B := by rw [h_right]
  have hAfinite : μ A < ⊤ := by
    refine lt_of_le_of_lt ?_ hfinite
    exact MeasureTheory.addContent_mono hC.isSetSemiring hA (hC.union_mem hA hB) subset_union_left
  have hBfinite : μ B < ⊤ := by
    refine lt_of_le_of_lt ?_ hfinite
    exact MeasureTheory.addContent_mono hC.isSetSemiring hB (hC.union_mem hA hB) subset_union_right
  have hInterfinite : μ (A ∩ B) < ⊤ := by
    refine lt_of_le_of_lt ?_ hfinite
    exact MeasureTheory.addContent_mono hC.isSetSemiring (hC.inter_mem hA hB)
      (hC.union_mem hA hB) (by
        intro x hx
        exact Or.inl hx.1)
  -- Then `toReal` turns the additive identity in `ℝ≥0∞` into the desired real equality.
  simpa [ENNReal.toReal_add, ne_of_lt hfinite, ne_of_lt hInterfinite, ne_of_lt hAfinite,
    ne_of_lt hBfinite] using congrArg ENNReal.toReal h_add

/-- Helper for Theorem 1.33: summing over the powerset splits into the empty subset and the
nonempty subsets. -/
lemma sum_powerset_eq_empty_add_sum_filter_nonempty (t : Finset ι) (F : Finset ι → ℝ) :
    ∑ S ∈ t.powerset, F S = F ∅ + ∑ S ∈ t.powerset.filter Finset.Nonempty, F S := by
  -- Split the powerset into the nonempty subsets and the complementary singleton `{∅}`.
  have hfilter : t.powerset.filter (fun S : Finset ι ↦ ¬ S.Nonempty) = {∅} := by
    ext S
    constructor
    · intro hS
      have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp (Finset.mem_filter.mp hS).2
      simp [hEmpty]
    · intro hS
      have hEmpty : S = ∅ := by simpa using hS
      subst hEmpty
      simp
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s := t.powerset) (p := Finset.Nonempty) (f := F)
  rw [hfilter] at hsplit
  simpa [add_comm] using hsplit.symm

/-- Helper for Theorem 1.33: the nonempty subsets of `insert a t` split into the nonempty subsets
of `t` and the subsets obtained by adjoining `a`. -/
lemma sum_filter_nonempty_powerset_insert {a : ι} {t : Finset ι} (ha : a ∉ t)
    (F : Finset ι → ℝ) :
    ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty, F S =
      ∑ S ∈ t.powerset.filter Finset.Nonempty, F S + ∑ S ∈ t.powerset, F (insert a S) := by
  -- Use the built-in powerset split with the indicatorized summand `if Nonempty then F else 0`.
  have hsplit :=
    Finset.sum_powerset_insert ha (fun S : Finset ι ↦ if S.Nonempty then F S else 0)
  simpa [Finset.sum_filter] using hsplit

/-- Helper for Theorem 1.33: intersecting a nonempty finite intersection with one more set can be
pushed inside each factor. -/
lemma inter_biInter_eq_biInter_inter {a : ι} {t : Finset ι} (ht : t.Nonempty)
    (A : ι → Set Ω) :
    A a ∩ ⋂ i ∈ t, A i = ⋂ i ∈ t, A i ∩ A a := by
  -- A witness from the nonempty index set recovers the missing `A a` factor on the right.
  rcases ht with ⟨i, hi⟩
  ext x
  constructor
  · intro hx
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hx ⊢
    intro j hj
    exact ⟨hx.2 j hj, hx.1⟩
  · intro hx
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hx ⊢
    refine ⟨(hx i hi).2, ?_⟩
    intro j hj
    exact (hx j hj).1

/-- Helper for Theorem 1.33: adjoining a fixed set to a nonempty finite union can be pushed into
each union term. -/
lemma union_biUnion_eq_biUnion_union {a : ι} {t : Finset ι} (ht : t.Nonempty)
    (A : ι → Set Ω) :
    A a ∪ ⋃ i ∈ t, A i = ⋃ i ∈ t, A a ∪ A i := by
  -- A witness from `t` supplies the index needed when the point already lies in `A a`.
  rcases ht with ⟨i, hi⟩
  ext x
  constructor
  · intro hx
    simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
    rcases hx with hxa | hx
    · exact ⟨i, hi, Or.inl hxa⟩
    · rcases hx with ⟨j, hj, hxj⟩
      exact ⟨j, hj, Or.inr hxj⟩
  · intro hx
    simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
    rcases hx with ⟨j, hj, hxa | hxj⟩
    · exact Or.inl hxa
    · exact Or.inr ⟨j, hj, hxj⟩

/-- Helper for Theorem 1.33: adjoining a fixed set to a finite intersection can be pushed inside
every factor. -/
lemma union_biInter_eq_biInter_union {a : ι} {t : Finset ι} (A : ι → Set Ω) :
    A a ∪ ⋂ i ∈ t, A i = ⋂ i ∈ t, A a ∪ A i := by
  -- If `x ∉ A a`, then every right-hand factor forces `x` into the corresponding `A i`.
  ext x
  constructor
  · intro hx
    simp only [Set.mem_union, Set.mem_iInter] at hx ⊢
    intro j hj
    rcases hx with hxa | hxt
    · exact Or.inl hxa
    · exact Or.inr (hxt j hj)
  · intro hx
    simp only [Set.mem_union, Set.mem_iInter] at hx ⊢
    by_cases hxa : x ∈ A a
    · exact Or.inl hxa
    · right
      intro j hj
      rcases hx j hj with hxa' | hxj
      · exact (hxa hxa').elim
      · exact hxj

/-- Helper for Theorem 1.33: the alternating intersection sum over `insert a t` separates into the
singleton contribution `A a`, the old alternating sum, and the transformed family
`i ↦ A i ∩ A a`. -/
lemma alternating_sum_biInter_insert (μ : AddContent ℝ≥0∞ C) {a : ι} {t : Finset ι}
    (ha : a ∉ t) (A : ι → Set Ω) :
    ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty,
      (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i)) =
      ENNReal.toReal (μ (A a))
        + ∑ S ∈ t.powerset.filter Finset.Nonempty,
            (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i))
        - ∑ S ∈ t.powerset.filter Finset.Nonempty,
            (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i ∩ A a)) := by
  -- Route correction: replace the earlier ad hoc reindexing with the stable insert split.
  have hsplit :=
    (show ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty,
        ((-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i))) =
      ∑ S ∈ t.powerset.filter Finset.Nonempty,
        ((-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i))) +
      ∑ S ∈ t.powerset,
        ((-1 : ℝ) ^ ((insert a S).card + 1) * ENNReal.toReal (μ (⋂ i ∈ insert a S, A i))) from
      sum_filter_nonempty_powerset_insert (ha := ha)
        (F := fun S ↦ (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i))))
  have hInserted :
      ∑ S ∈ t.powerset,
          (-1 : ℝ) ^ ((insert a S).card + 1) * ENNReal.toReal (μ (⋂ i ∈ insert a S, A i)) =
        ENNReal.toReal (μ (A a))
          - ∑ S ∈ t.powerset.filter Finset.Nonempty,
              (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i ∩ A a)) := by
    have hcongr :
        ∑ S ∈ t.powerset,
            (-1 : ℝ) ^ ((insert a S).card + 1) * ENNReal.toReal (μ (⋂ i ∈ insert a S, A i)) =
          ∑ S ∈ t.powerset,
            (-1 : ℝ) ^ (S.card + 2) * ENNReal.toReal (μ (A a ∩ ⋂ i ∈ S, A i)) := by
      -- Every subset of `t` avoids `a`, so `card` and `biInter` rewrite through `insert`.
      apply Finset.sum_congr rfl
      intro S hS
      have hSa : a ∉ S := Finset.notMem_of_mem_powerset_of_notMem hS ha
      rw [Finset.card_insert_of_notMem hSa, Finset.set_biInter_insert]
    rw [hcongr, sum_powerset_eq_empty_add_sum_filter_nonempty]
    congr 1
    · simp
    · calc
        ∑ S ∈ t.powerset.filter Finset.Nonempty,
            (-1 : ℝ) ^ (S.card + 2) * ENNReal.toReal (μ (A a ∩ ⋂ i ∈ S, A i)) =
          ∑ S ∈ t.powerset.filter Finset.Nonempty,
            -(((-1 : ℝ) ^ (S.card + 1)) * ENNReal.toReal (μ (⋂ i ∈ S, A i ∩ A a))) := by
              apply Finset.sum_congr rfl
              intro S hS
              have hSnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
              rw [inter_biInter_eq_biInter_inter (ht := hSnonempty) (A := A), pow_succ]
              ring
        _ = - ∑ S ∈ t.powerset.filter Finset.Nonempty,
              (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i ∩ A a)) := by
              simpa [neg_mul] using
                (Finset.sum_neg_distrib
                  (s := t.powerset.filter Finset.Nonempty)
                  (f := fun S ↦
                    (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i ∩ A a))))
  calc
    ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty,
        (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i)) =
      ∑ S ∈ t.powerset.filter Finset.Nonempty,
        (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i)) +
      (ENNReal.toReal (μ (A a)) -
        ∑ S ∈ t.powerset.filter Finset.Nonempty,
          (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i ∩ A a))) := by
            rw [hsplit, hInserted]
    _ = ENNReal.toReal (μ (A a))
          + ∑ S ∈ t.powerset.filter Finset.Nonempty,
              (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i))
          - ∑ S ∈ t.powerset.filter Finset.Nonempty,
              (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i ∩ A a)) := by
            ring

/-- Helper for Theorem 1.33: the alternating union sum over `insert a t` separates into the
singleton contribution `A a`, the old alternating sum, and the transformed family
`i ↦ A a ∪ A i`. -/
lemma alternating_sum_biUnion_insert (μ : AddContent ℝ≥0∞ C) {a : ι} {t : Finset ι}
    (ha : a ∉ t) (A : ι → Set Ω) :
    ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty,
      (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i)) =
      ENNReal.toReal (μ (A a))
        + ∑ S ∈ t.powerset.filter Finset.Nonempty,
            (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i))
        - ∑ S ∈ t.powerset.filter Finset.Nonempty,
            (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A a ∪ A i)) := by
  -- Route correction: the same insert split also gives the dual alternating reindexing.
  have hsplit :=
    (show ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty,
        ((-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i))) =
      ∑ S ∈ t.powerset.filter Finset.Nonempty,
        ((-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i))) +
      ∑ S ∈ t.powerset,
        ((-1 : ℝ) ^ ((insert a S).card + 1) * ENNReal.toReal (μ (⋃ i ∈ insert a S, A i))) from
      sum_filter_nonempty_powerset_insert (ha := ha)
        (F := fun S ↦ (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i))))
  have hInserted :
      ∑ S ∈ t.powerset,
          (-1 : ℝ) ^ ((insert a S).card + 1) * ENNReal.toReal (μ (⋃ i ∈ insert a S, A i)) =
        ENNReal.toReal (μ (A a))
          - ∑ S ∈ t.powerset.filter Finset.Nonempty,
              (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A a ∪ A i)) := by
    have hcongr :
        ∑ S ∈ t.powerset,
            (-1 : ℝ) ^ ((insert a S).card + 1) * ENNReal.toReal (μ (⋃ i ∈ insert a S, A i)) =
          ∑ S ∈ t.powerset,
            (-1 : ℝ) ^ (S.card + 2) * ENNReal.toReal (μ (A a ∪ ⋃ i ∈ S, A i)) := by
      -- The inserted branch contributes `A a` together with the old finite union.
      apply Finset.sum_congr rfl
      intro S hS
      have hSa : a ∉ S := Finset.notMem_of_mem_powerset_of_notMem hS ha
      rw [Finset.card_insert_of_notMem hSa, Finset.set_biUnion_insert]
    rw [hcongr, sum_powerset_eq_empty_add_sum_filter_nonempty]
    congr 1
    · simp
    · calc
        ∑ S ∈ t.powerset.filter Finset.Nonempty,
            (-1 : ℝ) ^ (S.card + 2) * ENNReal.toReal (μ (A a ∪ ⋃ i ∈ S, A i)) =
          ∑ S ∈ t.powerset.filter Finset.Nonempty,
            -(((-1 : ℝ) ^ (S.card + 1)) * ENNReal.toReal (μ (⋃ i ∈ S, A a ∪ A i))) := by
              apply Finset.sum_congr rfl
              intro S hS
              have hSnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
              rw [union_biUnion_eq_biUnion_union (ht := hSnonempty) (A := A), pow_succ]
              ring
        _ = - ∑ S ∈ t.powerset.filter Finset.Nonempty,
              (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A a ∪ A i)) := by
              simpa [neg_mul] using
                (Finset.sum_neg_distrib
                  (s := t.powerset.filter Finset.Nonempty)
                  (f := fun S ↦
                    (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A a ∪ A i))))
  calc
    ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty,
        (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i)) =
      ∑ S ∈ t.powerset.filter Finset.Nonempty,
        (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i)) +
      (ENNReal.toReal (μ (A a)) -
        ∑ S ∈ t.powerset.filter Finset.Nonempty,
          (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A a ∪ A i))) := by
            rw [hsplit, hInserted]
    _ = ENNReal.toReal (μ (A a))
          + ∑ S ∈ t.powerset.filter Finset.Nonempty,
              (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i))
          - ∑ S ∈ t.powerset.filter Finset.Nonempty,
              (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A a ∪ A i)) := by
            ring

/-- Helper for Theorem 1.33: finite inclusion-exclusion for a `Finset`-indexed union. -/
lemma addContent_biUnion_eq_sum_powerset_biInter (hC : IsSetRing C) (μ : AddContent ℝ≥0∞ C)
    (t : Finset ι) (A : ι → Set Ω) (hA : ∀ i ∈ t, A i ∈ C)
    (hfinite : μ (⋃ i ∈ t, A i) < ⊤) :
    ENNReal.toReal (μ (⋃ i ∈ t, A i)) =
      ∑ S ∈ t.powerset.filter Finset.Nonempty,
        (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i)) := by
  -- Route correction: quantify over the family before induction so the transformed family
  -- `i ↦ A i ∩ A a` can reuse the induction hypothesis.
  revert A hA hfinite
  refine Finset.induction_on t ?_ ?_
  · intro A hA hfinite
    -- The empty family contributes no nonempty subsets.
    have hfilter : (∅ : Finset ι).powerset.filter Finset.Nonempty = ∅ := by
      simp [Finset.powerset_empty]
    rw [hfilter]
    simp
  · intro a t ha ih A hA hfinite
    have hAa : A a ∈ C := hA a (by simp)
    have hAt : ∀ i ∈ t, A i ∈ C := by
      intro i hi
      exact hA i (by simp [hi])
    have hUnion_mem : (⋃ i ∈ t, A i) ∈ C := hC.biUnion_mem t hAt
    have hFull_mem : (⋃ i ∈ insert a t, A i) ∈ C := hC.biUnion_mem (insert a t) hA
    have hfinite_t : μ (⋃ i ∈ t, A i) < ⊤ := by
      -- The smaller finite union is contained in the full union over `insert a t`.
      refine lt_of_le_of_lt ?_ hfinite
      exact MeasureTheory.addContent_mono hC.isSetSemiring hUnion_mem hFull_mem (by
        intro x hx
        simp only [Set.mem_iUnion] at hx ⊢
        rcases hx with ⟨i, hi, hxi⟩
        exact ⟨i, by simp [hi], hxi⟩)
    have hInterUnion_eq : A a ∩ ⋃ i ∈ t, A i = ⋃ i ∈ t, A i ∩ A a := by
      -- Intersecting the old union with `A a` produces the transformed family.
      ext x
      constructor
      · intro hx
        simp only [Set.mem_inter_iff, Set.mem_iUnion] at hx ⊢
        rcases hx with ⟨hxa, i, hi, hxi⟩
        exact ⟨i, hi, hxi, hxa⟩
      · intro hx
        simp only [Set.mem_inter_iff, Set.mem_iUnion] at hx ⊢
        rcases hx with ⟨i, hi, hxi, hxa⟩
        exact ⟨hxa, i, hi, hxi⟩
    have hfinite_inter : μ (⋃ i ∈ t, A i ∩ A a) < ⊤ := by
      -- This transformed union is contained in the full union because it lies inside `A a`.
      have haux : μ (A a ∩ ⋃ i ∈ t, A i) < ⊤ := by
        refine lt_of_le_of_lt ?_ hfinite
        exact MeasureTheory.addContent_mono hC.isSetSemiring (hC.inter_mem hAa hUnion_mem) hFull_mem
          (by
            intro x hx
            simp only [Set.mem_inter_iff, Set.mem_iUnion] at hx ⊢
            exact ⟨a, by simp, hx.1⟩)
      rwa [hInterUnion_eq] at haux
    have hbinary :
        ENNReal.toReal (μ (⋃ i ∈ insert a t, A i)) =
          ENNReal.toReal (μ (A a)) + ENNReal.toReal (μ (⋃ i ∈ t, A i))
            - ENNReal.toReal (μ (⋃ i ∈ t, A i ∩ A a)) := by
      -- Apply the binary identity to `A a` and the old finite union.
      have hfinite_union : μ (A a ∪ ⋃ i ∈ t, A i) < ⊤ := by
        simpa [Finset.set_biUnion_insert] using hfinite
      have hbin := toReal_addContent_union_add_inter hC μ hAa hUnion_mem hfinite_union
      have hbin' :
          ENNReal.toReal (μ (⋃ i ∈ insert a t, A i))
            + ENNReal.toReal (μ (⋃ i ∈ t, A i ∩ A a)) =
            ENNReal.toReal (μ (A a)) + ENNReal.toReal (μ (⋃ i ∈ t, A i)) := by
        simpa [Finset.set_biUnion_insert, hInterUnion_eq] using hbin
      linarith
    have hInterA : ∀ i ∈ t, A i ∩ A a ∈ C := by
      intro i hi
      exact hC.inter_mem (hAt i hi) hAa
    calc
      ENNReal.toReal (μ (⋃ i ∈ insert a t, A i)) =
        ENNReal.toReal (μ (A a)) + ENNReal.toReal (μ (⋃ i ∈ t, A i))
          - ENNReal.toReal (μ (⋃ i ∈ t, A i ∩ A a)) := hbinary
      _ = ENNReal.toReal (μ (A a))
            + (∑ S ∈ t.powerset.filter Finset.Nonempty,
                (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i)))
            - (∑ S ∈ t.powerset.filter Finset.Nonempty,
                (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i ∩ A a))) := by
              rw [ih A hAt hfinite_t, ih (fun i ↦ A i ∩ A a) hInterA hfinite_inter]
      _ = ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty,
            (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i)) := by
              symm
              exact alternating_sum_biInter_insert (μ := μ) (ha := ha) (A := A)

/-- Helper for Theorem 1.33: finite inclusion-exclusion for a nonempty `Finset`-indexed
intersection. -/
lemma addContent_biInter_eq_sum_powerset_biUnion (hC : IsSetRing C) (μ : AddContent ℝ≥0∞ C)
    (t : Finset ι) (ht : t.Nonempty) (A : ι → Set Ω) (hA : ∀ i ∈ t, A i ∈ C)
    (hfinite : μ (⋃ i ∈ t, A i) < ⊤) :
    ENNReal.toReal (μ (⋂ i ∈ t, A i)) =
      ∑ S ∈ t.powerset.filter Finset.Nonempty,
        (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i)) := by
  -- Route correction: carry the family parameter through the nonempty induction so the
  -- transformed family `i ↦ A a ∪ A i` remains inside the induction hypothesis.
  revert A hA hfinite
  refine Finset.Nonempty.cons_induction ?_ ?_ ht
  · intro a A hA hfinite
    -- The singleton case has exactly one nonempty subset.
    have hfilter : ({a} : Finset ι).powerset.filter Finset.Nonempty = {{a}} := by
      ext S
      constructor
      · intro hS
        rcases Finset.mem_filter.mp hS with ⟨hpow, hne⟩
        have hsub : S ⊆ ({a} : Finset ι) := Finset.mem_powerset.mp hpow
        have hcases := Finset.subset_singleton_iff.mp hsub
        rcases hcases with rfl | rfl
        · cases hne.ne_empty rfl
        · simp
      · intro hS
        have hEq : S = {a} := by simpa using hS
        subst hEq
        simp
    rw [hfilter]
    simp
  · intro a t ha ht ih A hA hfinite
    have hAinsert : ∀ i ∈ insert a t, A i ∈ C := by
      simpa [Finset.cons_eq_insert, ha] using hA
    have hfiniteInsert : μ (⋃ i ∈ insert a t, A i) < ⊤ := by
      simpa [Finset.cons_eq_insert, ha] using hfinite
    have hAa : A a ∈ C := hAinsert a (by simp)
    have hAt : ∀ i ∈ t, A i ∈ C := by
      intro i hi
      exact hAinsert i (by simp [hi])
    have hInter_mem : (⋂ i ∈ t, A i) ∈ C := hC.biInter_mem t ht hAt
    have hFull_mem : (⋃ i ∈ insert a t, A i) ∈ C := hC.biUnion_mem (insert a t) hAinsert
    have hfinite_t : μ (⋃ i ∈ t, A i) < ⊤ := by
      -- The old union is contained in the enlarged union.
      refine lt_of_le_of_lt ?_ hfiniteInsert
      exact MeasureTheory.addContent_mono hC.isSetSemiring (hC.biUnion_mem t hAt) hFull_mem (by
        intro x hx
        simp only [Set.mem_iUnion] at hx ⊢
        rcases hx with ⟨i, hi, hxi⟩
        exact ⟨i, by simp [hi], hxi⟩)
    have hfinite_inter : μ (A a ∪ ⋂ i ∈ t, A i) < ⊤ := by
      -- The auxiliary binary union is still contained in the enlarged finite union.
      refine lt_of_le_of_lt ?_ hfiniteInsert
      exact MeasureTheory.addContent_mono hC.isSetSemiring (hC.union_mem hAa hInter_mem) hFull_mem
        (by
          intro x hx
          simp only [Set.mem_union, Set.mem_iInter, Set.mem_iUnion] at hx ⊢
          rcases hx with hxa | hxI
          · exact ⟨a, by simp, hxa⟩
          · rcases ht with ⟨i, hi⟩
            exact ⟨i, by simp [hi], hxI i hi⟩)
    have hbinary :
        ENNReal.toReal (μ (⋂ i ∈ insert a t, A i)) =
          ENNReal.toReal (μ (A a)) + ENNReal.toReal (μ (⋂ i ∈ t, A i))
            - ENNReal.toReal (μ (⋂ i ∈ t, A a ∪ A i)) := by
      -- Apply the binary identity to `A a` and the old finite intersection.
      have hbin := toReal_addContent_union_add_inter hC μ hAa hInter_mem hfinite_inter
      have hbin' :
          ENNReal.toReal (μ (⋂ i ∈ insert a t, A i))
            + ENNReal.toReal (μ (A a ∪ ⋂ i ∈ t, A i)) =
            ENNReal.toReal (μ (A a)) + ENNReal.toReal (μ (⋂ i ∈ t, A i)) := by
        simpa [Finset.set_biInter_insert, add_comm] using hbin
      rw [union_biInter_eq_biInter_union (A := A)] at hbin'
      linarith
    have hUnionA : ∀ i ∈ t, A a ∪ A i ∈ C := by
      intro i hi
      exact hC.union_mem hAa (hAt i hi)
    have hfinite_unionA : μ (⋃ i ∈ t, A a ∪ A i) < ⊤ := by
      -- The transformed union is exactly the enlarged finite union.
      have hEq : ⋃ i ∈ t, A a ∪ A i = A a ∪ ⋃ i ∈ t, A i := by
        symm
        exact union_biUnion_eq_biUnion_union (ht := ht) (A := A)
      rw [hEq]
      simpa [Finset.set_biUnion_insert] using hfiniteInsert
    have hcalc :
        ENNReal.toReal (μ (⋂ i ∈ insert a t, A i)) =
          ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty,
            (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i)) := by
      calc
        ENNReal.toReal (μ (⋂ i ∈ insert a t, A i)) =
          ENNReal.toReal (μ (A a)) + ENNReal.toReal (μ (⋂ i ∈ t, A i))
            - ENNReal.toReal (μ (⋂ i ∈ t, A a ∪ A i)) := hbinary
        _ = ENNReal.toReal (μ (A a))
              + (∑ S ∈ t.powerset.filter Finset.Nonempty,
                  (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i)))
              - (∑ S ∈ t.powerset.filter Finset.Nonempty,
                  (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A a ∪ A i))) := by
                rw [ih A hAt hfinite_t, ih (fun i ↦ A a ∪ A i) hUnionA hfinite_unionA]
        _ = ∑ S ∈ (insert a t).powerset.filter Finset.Nonempty,
              (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i)) := by
                symm
                exact alternating_sum_biUnion_insert (μ := μ) (ha := ha) (A := A)
    simpa [Finset.cons_eq_insert, ha] using hcalc

end InclusionExclusionHelpers

-- Proof sketch: argue by induction on the finite index set. The base case is the two-set identity
-- from the earlier inclusion-exclusion lemma, and the induction step separates one set from the
-- remaining union and reapplies the induction hypothesis to the resulting intersections.
/-- Theorem 1.33 (1): For a finite family in a ring of sets, the content of the union is the
inclusion-exclusion alternating sum of the contents of the nonempty finite intersections, written
in `ℝ` via `ENNReal.toReal`. -/
theorem addContent_union_eq_sum_powerset_inter (hC : IsSetRing C) (μ : AddContent ℝ≥0∞ C)
    {n : ℕ} (A : Fin n → Set Ω) (hA : ∀ i, A i ∈ C) (hμfinite : μ (⋃ i, A i) < ⊤) :
    ENNReal.toReal (μ (⋃ i, A i)) =
      Finset.sum (univ.powerset.filter (fun S : Finset (Fin n) ↦ 0 < S.card))
        (fun S ↦ (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋂ i ∈ S, A i))) := by
  -- Specialize the finite-set helper to the full index set `Fin n`.
  simpa [Finset.card_pos] using
    addContent_biUnion_eq_sum_powerset_biInter (hC := hC) (μ := μ) (t := (univ : Finset (Fin n)))
      (A := A) (hA := fun i _ ↦ hA i) (hfinite := by simpa using hμfinite)

-- Proof sketch: apply the union formula to the complements inside a fixed member of the family, or
-- equivalently induct on the finite family while using the binary identity for intersections and
-- unions together with monotonicity to justify finiteness of every intermediate term.
/-- Theorem 1.33 (2): For a nonempty finite family in a ring of sets, the content of the
intersection is the inclusion-exclusion alternating sum of the contents of the nonempty finite
unions, written in `ℝ` via `ENNReal.toReal`. -/
theorem addContent_inter_eq_sum_powerset_union (hC : IsSetRing C) (μ : AddContent ℝ≥0∞ C)
    {n : ℕ} (hn : 0 < n) (A : Fin n → Set Ω) (hA : ∀ i, A i ∈ C) (hμfinite : μ (⋃ i, A i) < ⊤) :
    ENNReal.toReal (μ (⋂ i, A i)) =
      Finset.sum (univ.powerset.filter (fun S : Finset (Fin n) ↦ 0 < S.card))
        (fun S ↦ (-1 : ℝ) ^ (S.card + 1) * ENNReal.toReal (μ (⋃ i ∈ S, A i))) := by
  -- Specialize the nonempty finite-set helper to `Fin n`, using `hn` to witness nonemptiness.
  have hnonempty : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, by simp⟩
  simpa [Finset.card_pos] using
    addContent_biInter_eq_sum_powerset_biUnion (hC := hC) (μ := μ)
      (t := (univ : Finset (Fin n))) (ht := hnonempty) (A := A)
      (hA := fun i _ ↦ hA i) (hfinite := by simpa using hμfinite)

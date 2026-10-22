/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {ι : Type v} [Countable ι]

/-- Theorem 8.6: for a countable measurable partition `(B i)`, pairwise disjoint and with union of
probability `1`, the probability of a measurable event `A` is the countable sum of the
conditional probabilities `P[A | B i]` weighted by the probabilities `P (B i)`. -/
-- Proof sketch: first use the full-measure assumption to rewrite `P A` as
-- `P (A ∩ ⋃ i, B i) = P (⋃ i, A ∩ B i)`. Then apply countable additivity to the measurable,
-- pairwise disjoint sets `A ∩ B i`, and finally use `cond_mul_eq_inter` on each summand to
-- identify `P[A | B i] * P (B i)` with `P (A ∩ B i)`.
theorem probability_eq_tsum_cond_mul_of_countable_partition
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Set Ω) (B : ι → Set Ω)
    (hA : MeasurableSet A)
    (hB : ∀ i, MeasurableSet (B i))
    (h_disjoint : Pairwise fun i j ↦ Disjoint (B i) (B j))
    (h_cover : P (⋃ i, B i) = 1) :
    P A = ∑' i, P[A | B i] * P (B i) := by
  have h_union_meas : MeasurableSet (⋃ i, B i) := MeasurableSet.iUnion hB
  -- First replace `A` by its intersection with the full-measure union of the partition pieces.
  have h_cover_ae : (⋃ i, B i) =ᵐ[P] Set.univ := by
    refine ae_eq_univ.mpr ?_
    simpa [h_cover] using
      (measure_compl h_union_meas (measure_ne_top P (⋃ i, B i)))
  have h_inter_eq : P A = P (A ∩ ⋃ i, B i) := by
    exact (measure_congr (inter_ae_eq_left_of_ae_eq_univ h_cover_ae)).symm
  -- The family `A ∩ B i` stays pairwise disjoint because each term is contained in `B i`.
  have h_disjoint_inter : Pairwise fun i j ↦ Disjoint (A ∩ B i) (A ∩ B j) := by
    intro i j hij
    exact (h_disjoint hij).mono Set.inter_subset_right Set.inter_subset_right
  calc
    P A = P (A ∩ ⋃ i, B i) := h_inter_eq
    -- Rewrite the event as the union of the partition pieces inside `A`.
    _ = P (⋃ i, A ∩ B i) := by rw [Set.inter_iUnion]
    -- Countable additivity applies to the measurable pairwise disjoint family `A ∩ B i`.
    _ = ∑' i, P (A ∩ B i) := by
      rw [measure_iUnion h_disjoint_inter]
      intro i
      exact hA.inter (hB i)
    -- Each summand is exactly the conditional-probability term from Definition 8.2.
    _ = ∑' i, P[A | B i] * P (B i) := by
      refine tsum_congr fun i ↦ ?_
      simpa [Set.inter_comm] using (cond_mul_eq_inter (hB i) A P).symm

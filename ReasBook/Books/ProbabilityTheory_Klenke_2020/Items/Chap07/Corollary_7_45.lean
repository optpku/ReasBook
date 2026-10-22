/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace MeasureTheory
namespace SignedMeasure

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Corollary 7.45: a Hahn positive set bounds every measurable
difference `s A - s Aᶜ`. -/
private theorem diff_compl_le_of_hahn (s : SignedMeasure Ω) {P A : Set Ω}
    (hP : MeasurableSet P) (hA : MeasurableSet A)
    (hpos : 0 ≤[P] s) (hneg : s ≤[Pᶜ] 0) :
    s A - s Aᶜ ≤ s P - s Pᶜ := by
  -- Split both `A` and `P` into positive and negative pieces of the Hahn decomposition.
  have h_disj_PA : Disjoint (P ∩ A) (Pᶜ ∩ A) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.1 hx.1
  have h_disj_PAc : Disjoint (P ∩ Aᶜ) (Pᶜ ∩ Aᶜ) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.1 hx.1
  have h_disj_AP : Disjoint (A ∩ P) (Aᶜ ∩ P) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.1 hx.1
  have h_disj_APc : Disjoint (A ∩ Pᶜ) (Aᶜ ∩ Pᶜ) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx'.1 hx.1
  have h_union_A : (P ∩ A) ∪ (Pᶜ ∩ A) = A := by
    ext x
    by_cases hx : x ∈ P <;> simp [hx]
  have h_union_Ac : (P ∩ Aᶜ) ∪ (Pᶜ ∩ Aᶜ) = Aᶜ := by
    ext x
    by_cases hx : x ∈ P <;> simp [hx]
  have h_union_P : (A ∩ P) ∪ (Aᶜ ∩ P) = P := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  have h_union_Pc : (A ∩ Pᶜ) ∪ (Aᶜ ∩ Pᶜ) = Pᶜ := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hA_split : s A = s (P ∩ A) + s (Pᶜ ∩ A) := by
    rw [← h_union_A, VectorMeasure.of_union h_disj_PA]
    all_goals measurability
  have hAc_split : s Aᶜ = s (P ∩ Aᶜ) + s (Pᶜ ∩ Aᶜ) := by
    rw [← h_union_Ac, VectorMeasure.of_union h_disj_PAc]
    all_goals measurability
  have hP_split_aux : s P = s (A ∩ P) + s (Aᶜ ∩ P) := by
    rw [← h_union_P, VectorMeasure.of_union h_disj_AP]
    all_goals measurability
  have hP_split : s P = s (P ∩ A) + s (P ∩ Aᶜ) := by
    simpa [Set.inter_comm] using hP_split_aux
  have hPc_split_aux : s Pᶜ = s (A ∩ Pᶜ) + s (Aᶜ ∩ Pᶜ) := by
    rw [← h_union_Pc, VectorMeasure.of_union h_disj_APc]
    all_goals measurability
  have hPc_split : s Pᶜ = s (Pᶜ ∩ A) + s (Pᶜ ∩ Aᶜ) := by
    simpa [Set.inter_comm] using hPc_split_aux
  -- The mixed term on `P` is nonnegative, while the mixed term on `Pᶜ` is nonpositive.
  have hPAc_nonneg : 0 ≤ s (P ∩ Aᶜ) := by
    exact s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hP Set.inter_subset_left hpos)
  have hPcA_nonpos : s (Pᶜ ∩ A) ≤ 0 := by
    exact
      s.nonpos_of_restrict_le_zero
        (s.restrict_le_zero_subset hP.compl Set.inter_subset_left hneg)
  linarith

/-- Helper for Corollary 7.45: the measurable values `s A - s Aᶜ` are bounded above. -/
private theorem measurable_diff_compl_bddAbove (s : SignedMeasure Ω) :
    BddAbove {r : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ r = s A - s Aᶜ} := by
  -- The Hahn set from the Jordan decomposition gives a uniform upper bound.
  obtain ⟨i, hi₁, hi₂, hi₃, -, -⟩ := s.toJordanDecomposition_spec
  refine ⟨s i - s iᶜ, ?_⟩
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  exact diff_compl_le_of_hahn s hi₁ hA hi₂ hi₃

/-- The total variation mass is the supremum of `s A - s Aᶜ` over measurable sets. -/
-- Proof sketch: compare the supremum formula with a Hahn decomposition of `s`, show the Hahn
-- positive set realizes the supremum, and then identify the resulting value with `s.totalVariation`.
theorem totalVariation_real_univ_eq_sSup (s : SignedMeasure Ω) :
    s.totalVariation.real univ =
      sSup {r : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ r = s A - s Aᶜ} := by
  let S : Set ℝ := {r : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ r = s A - s Aᶜ}
  obtain ⟨i, hi₁, hi₂, hi₃, hμ, hν⟩ := s.toJordanDecomposition_spec
  -- The Jordan Hahn set computes the total variation mass exactly.
  have h_tv : s.totalVariation.real univ = s i - s iᶜ := by
    rw [SignedMeasure.totalVariation, measureReal_add_apply, hμ, hν,
      SignedMeasure.toMeasureOfZeroLE_real_apply _ hi₂ hi₁ MeasurableSet.univ,
      SignedMeasure.toMeasureOfLEZero_real_apply _ hi₃ hi₁.compl MeasurableSet.univ]
    simp [sub_eq_add_neg]
  have hS_nonempty : S.Nonempty := ⟨s i - s iᶜ, ⟨i, hi₁, rfl⟩⟩
  have hS_bddAbove : BddAbove S := measurable_diff_compl_bddAbove s
  refine le_antisymm ?_ ?_
  · rw [h_tv]
    exact le_csSup hS_bddAbove ⟨i, hi₁, rfl⟩
  · refine csSup_le hS_nonempty ?_
    intro r hr
    rcases hr with ⟨A, hA, rfl⟩
    rw [h_tv]
    exact diff_compl_le_of_hahn s hi₁ hA hi₂ hi₃

/-- The total variation mass can be computed from any Hahn decomposition. -/
-- Proof sketch: use the positive/negative restrictions on `OmegaPos` and `OmegaPosᶜ`
-- to identify the Jordan positive and negative parts with the corresponding restricted measures.
theorem totalVariation_real_univ_eq_hahn (s : SignedMeasure Ω) {OmegaPos : Set Ω}
    (hOmegaPos : MeasurableSet OmegaPos) (hpos : 0 ≤[OmegaPos] s) (hneg : s ≤[OmegaPosᶜ] 0) :
    s.totalVariation.real univ = s OmegaPos - s OmegaPosᶜ := by
  have hS_nonempty :
      {r : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ r = s A - s Aᶜ}.Nonempty :=
    ⟨s OmegaPos - s OmegaPosᶜ, ⟨OmegaPos, hOmegaPos, rfl⟩⟩
  -- The chosen Hahn set both belongs to the supremum set and bounds it from above.
  refine le_antisymm ?_ ?_
  · rw [totalVariation_real_univ_eq_sSup]
    exact csSup_le hS_nonempty fun r hr ↦ by
      rcases hr with ⟨A, hA, rfl⟩
      exact diff_compl_le_of_hahn s hOmegaPos hA hpos hneg
  · rw [totalVariation_real_univ_eq_sSup]
    exact le_csSup (measurable_diff_compl_bddAbove s) ⟨OmegaPos, hOmegaPos, rfl⟩

/-- The total variation mass is the sum of the Jordan positive and negative masses. -/
-- Proof sketch: unfold `SignedMeasure.totalVariation`,
-- then use additivity of `Measure.real` on finite measures.
theorem totalVariation_real_univ_eq_jordan (s : SignedMeasure Ω) :
    s.totalVariation.real univ =
      let j := s.toJordanDecomposition
      j.posPart.real univ + j.negPart.real univ := by
  -- This is the defining formula for `totalVariation`, evaluated at `univ`.
  simp [SignedMeasure.totalVariation, measureReal_add_apply]

/-- Helper for Corollary 7.45: every measurable difference `s A - s Aᶜ` is controlled by the
total variation mass. -/
private theorem le_totalVariation_real_univ_of_measurable (s : SignedMeasure Ω) {A : Set Ω}
    (hA : MeasurableSet A) : s A - s Aᶜ ≤ s.totalVariation.real univ := by
  -- The measurable value belongs to the supremum set from the previous theorem.
  rw [totalVariation_real_univ_eq_sSup]
  exact le_csSup (measurable_diff_compl_bddAbove s) ⟨A, hA, rfl⟩

/-- The total variation mass is subadditive. -/
-- Proof sketch: choose a Hahn decomposition for `s + t`, expand on its positive and negative
-- parts, and bound each term by the corresponding Hahn decomposition values for `s` and `t`.
private theorem totalVariation_real_univ_add_le (s t : SignedMeasure Ω) :
    (s + t).totalVariation.real univ ≤
      s.totalVariation.real univ + t.totalVariation.real univ := by
  -- Follow the textbook proof on a Hahn decomposition of `s + t`.
  obtain ⟨P, hP, hpos, hneg⟩ := (s + t).exists_compl_positive_negative
  calc
    (s + t).totalVariation.real univ = (s + t) P - (s + t) Pᶜ := by
      exact totalVariation_real_univ_eq_hahn (s + t) hP hpos hneg
    _ = (s P - s Pᶜ) + (t P - t Pᶜ) := by
      rw [VectorMeasure.add_apply, VectorMeasure.add_apply]
      ring
    _ ≤ s.totalVariation.real univ + t.totalVariation.real univ := by
      exact
        add_le_add (le_totalVariation_real_univ_of_measurable s hP)
          (le_totalVariation_real_univ_of_measurable t hP)

/-- Vanishing total variation forces a signed measure to be zero. -/
-- Proof sketch: convert the vanishing of `s.totalVariation.real univ` into vanishing of
-- `s.totalVariation univ`, use `SignedMeasure.null_of_totalVariation_zero` on all sets,
-- and conclude by extensionality.
private theorem eq_zero_of_totalVariation_real_univ_eq_zero (s : SignedMeasure Ω)
    (hs : s.totalVariation.real univ = 0) : s = 0 := by
  have hfin : s.totalVariation univ ≠ ⊤ := by
    rw [SignedMeasure.totalVariation, Measure.add_apply]
    simp
  have h_univ : s.totalVariation univ = 0 :=
    (measureReal_eq_zero_iff hfin).1 hs
  have htv : s.totalVariation = 0 := Measure.measure_univ_eq_zero.mp h_univ
  ext A hA
  have hA0 : s.totalVariation A = 0 := by simp [htv]
  simpa using s.null_of_totalVariation_zero hA0

/-- Corollary 7.45: The total variation functional on signed measures, given equivalently by the
supremum formula, by any Hahn decomposition, and by the Jordan decomposition, defines an additive
group norm on `MeasureTheory.SignedMeasure Ω`. -/
noncomputable def totalVariationNorm (Ω : Type u) [MeasurableSpace Ω] :
    AddGroupNorm (SignedMeasure Ω) :=
  AddGroupNorm.mk
    (AddGroupSeminorm.mk
      (fun s ↦ s.totalVariation.real univ)
      (by simp [SignedMeasure.totalVariation_zero])
      totalVariation_real_univ_add_le
      (by
        intro s
        simp [SignedMeasure.totalVariation_neg]))
    eq_zero_of_totalVariation_real_univ_eq_zero

end SignedMeasure
end MeasureTheory

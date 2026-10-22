/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_37
import Mathlib.MeasureTheory.Measure.PreVariation

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators MeasureTheory NNReal ENNReal

noncomputable section

universe u

namespace MeasureTheory
namespace Measure

variable {Ω : Type u} [MeasurableSpace Ω]

attribute [local instance] Classical.propDecidable

local notation "MeasurableFinpartition" =>
  Finpartition (⊤ : Subtype (MeasurableSet : Set Ω → Prop))

variable (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The piecewise constant density attached to a finite measurable partition, obtained by averaging
`ν` over each partition cell with respect to `μ`. This auxiliary density is only exposed in the
finite-measure setting of Example 7.39, so the cell averages are faithful real-valued quantities. -/
def partitionAverageDensity (Z : MeasurableFinpartition) : Ω → ℝ :=
  fun ω ↦
    ∑ C ∈ Z.parts,
      C.1.indicator
        (fun _ ↦ if μ C.1 = 0 then 0 else (ν C.1).toReal / (μ C.1).toReal) ω

/-- Helper for Example 7.39: the real-valued average `ν(C) / μ(C)` attached to a measurable
partition cell, with the zero-denominator case normalized to `0`. -/
private def cellAverage
    (C : Subtype (MeasurableSet : Set Ω → Prop)) : ℝ :=
  if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal / (μ (C : Set Ω)).toReal

/-- Helper for Example 7.39: the union of a finite family of measurable partition cells. -/
private def cellUnion
    (S : Finset (Subtype (MeasurableSet : Set Ω → Prop))) : Set Ω :=
  ⋃ C ∈ S, ((C : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)

/-- Helper for Example 7.39: the measurable cells of a finite measurable partition cover `Ω`. -/
private theorem biUnion_parts_eq_univ (Z : MeasurableFinpartition) :
    (⋃ s ∈ Z.parts, ((s : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) = Set.univ := by
  -- Reinterpret the supremum identity of the partition as a union identity of measurable sets.
  simpa [MeasureTheory.preVariation.Finset.sup_measurableSetSubtype_eq_biUnion] using
    congrArg (fun s : Subtype (MeasurableSet : Set Ω → Prop) ↦ (s : Set Ω)) Z.sup_parts

/-- Helper for Example 7.39: distinct cells of a measurable finite partition are disjoint as
subsets of `Ω`. -/
private theorem disjoint_coe_of_mem_parts
    {Z : MeasurableFinpartition}
    {C D : Subtype (MeasurableSet : Set Ω → Prop)}
    (hC : C ∈ Z.parts) (hD : D ∈ Z.parts) (hCD : C ≠ D) :
    Disjoint ((C : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)
      ((D : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) := by
  -- The lattice disjointness from `Finpartition` becomes set disjointness after coercion.
  have hdisj : Disjoint C D := Z.disjoint hC hD hCD
  exact (disjoint_subtype_iff (fun {_ _} hx hy ↦ hx.inter hy) MeasurableSet.empty).1 hdisj

/-- Helper for Example 7.39: each partition-average density is integrable on the finite measure
space `(Ω, μ)`. -/
private theorem partitionAverageDensity_integrable
    (Z : MeasurableFinpartition) :
    Integrable (partitionAverageDensity μ ν Z) μ := by
  -- Finite sums of indicator constants are integrable under `IsFiniteMeasure μ`.
  unfold partitionAverageDensity
  refine integrable_finset_sum Z.parts ?_
  intro C hC
  exact (integrable_const _).indicator C.2

/-- Helper for Example 7.39: each partition-average density is `μ`-a.e. strongly measurable. -/
private theorem partitionAverageDensity_aestronglyMeasurable
    (Z : MeasurableFinpartition) :
    AEStronglyMeasurable (partitionAverageDensity μ ν Z) μ :=
  (partitionAverageDensity_integrable (μ := μ) (ν := ν) Z).aestronglyMeasurable

/-- Helper for Example 7.39: the `ρ`-mass of a finite union of cells is the sum of the masses of
those cells. -/
private theorem measureReal_biUnion_eq_sum_of_subset
    {ρ : Measure Ω} [IsFiniteMeasure ρ]
    (Z : MeasurableFinpartition)
    (S : Finset (Subtype (MeasurableSet : Set Ω → Prop)))
    (hS : S ⊆ Z.parts) :
    ρ.real (cellUnion S) =
      ∑ C ∈ S, ρ.real (C : Set Ω) := by
  -- Restrict finite additivity to the selected cells of the ambient partition.
  rw [Measure.real]
  simp only [cellUnion]
  rw [measure_biUnion_finset]
  · rw [ENNReal.toReal_sum]
    · simp [Measure.real]
    · intro C hC
      exact measure_lt_top ρ (C : Set Ω) |>.ne
  · intro C hC D hD hCD
    exact disjoint_coe_of_mem_parts (hS hC) (hS hD) hCD
  · intro C hC
    exact C.2

/-- Helper for Example 7.39: intersecting the union of chosen cells with one chosen cell recovers
that cell. -/
private theorem inter_cellUnion_eq_self_of_mem
    {S : Finset (Subtype (MeasurableSet : Set Ω → Prop))}
    {C : Subtype (MeasurableSet : Set Ω → Prop)}
    (hC : C ∈ S) :
    cellUnion S ∩ (C : Set Ω) = (C : Set Ω) := by
  -- Membership in a chosen cell already puts a point inside the chosen union.
  ext ω
  constructor
  · intro hω
    exact hω.2
  · intro hω
    refine ⟨?_, hω⟩
    exact Set.mem_iUnion.2 ⟨C, Set.mem_iUnion.2 ⟨hC, hω⟩⟩

/-- Helper for Example 7.39: intersecting the chosen-cell union with an unchosen partition cell is
empty. -/
private theorem inter_cellUnion_eq_empty_of_notMem
    {Z : MeasurableFinpartition}
    {S : Finset (Subtype (MeasurableSet : Set Ω → Prop))}
    (hS : S ⊆ Z.parts)
    {C : Subtype (MeasurableSet : Set Ω → Prop)}
    (hCZ : C ∈ Z.parts)
    (hCS : C ∉ S) :
    cellUnion S ∩ (C : Set Ω) = ∅ := by
  -- A point cannot lie in two distinct cells of the partition.
  ext ω
  constructor
  · intro hω
    rcases Set.mem_iUnion.1 hω.1 with ⟨D, hωD⟩
    rcases Set.mem_iUnion.1 hωD with ⟨hDS, hωD'⟩
    have hDC : D ≠ C := by
      intro hDC
      apply hCS
      simpa [hDC] using hDS
    exact (disjoint_coe_of_mem_parts (hS hDS) hCZ hDC).le_bot ⟨hωD', hω.2⟩
  · simp

/-- Helper for Example 7.39: integrating the partition-average density over a finite union of
selected partition cells collapses to the corresponding finite sum of cell masses. -/
private theorem setIntegral_partitionAverageDensity_eq_sum_of_subset
    (Z : MeasurableFinpartition)
    (S : Finset (Subtype (MeasurableSet : Set Ω → Prop)))
    (hS : S ⊆ Z.parts) :
    ∫ ω in cellUnion S, partitionAverageDensity μ ν Z ω ∂μ =
      ∑ C ∈ S, if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal := by
  -- Expand the density as a finite sum and integrate each indicator constant separately.
  unfold partitionAverageDensity
  calc
    ∫ ω in cellUnion S,
        ∑ C ∈ Z.parts,
          (C : Set Ω).indicator
            (fun _ ↦ if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal / (μ (C : Set Ω)).toReal)
            ω ∂μ =
        ∑ C ∈ Z.parts,
          ∫ ω in cellUnion S,
            (C : Set Ω).indicator
              (fun _ ↦ if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal / (μ (C : Set Ω)).toReal)
              ω ∂μ := by
      rw [integral_finset_sum]
      intro C hCZ
      exact (integrable_const _).indicator C.2
    _ = ∑ C ∈ S,
          ∫ ω in cellUnion S,
            (C : Set Ω).indicator
              (fun _ ↦ if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal / (μ (C : Set Ω)).toReal)
              ω ∂μ := by
      -- Cells outside `S` contribute zero because their intersection with `cellUnion S` is empty.
      symm
      refine Finset.sum_subset hS ?_
      intro C hCZ hCS
      rw [integral_indicator_const _ C.2, measureReal_restrict_apply C.2, smul_eq_mul,
        Set.inter_comm, inter_cellUnion_eq_empty_of_notMem hS hCZ hCS]
      simp
    _ = ∑ C ∈ S, if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal := by
      -- On a chosen cell, the restricted measure is just `μ(C)`, so the average recovers `ν(C)`.
      refine Finset.sum_congr rfl ?_
      intro C hCS
      rw [integral_indicator_const _ C.2, measureReal_restrict_apply C.2, smul_eq_mul,
        Set.inter_comm, inter_cellUnion_eq_self_of_mem hCS]
      by_cases hμC : μ (C : Set Ω) = 0
      · simp [hμC]
      · have hμC_toReal : (μ (C : Set Ω)).toReal ≠ 0 := by
          exact ENNReal.toReal_ne_zero.mpr ⟨hμC, by finiteness⟩
        rw [Measure.real, if_neg hμC]
        calc
          (μ (C : Set Ω)).toReal * ((ν (C : Set Ω)).toReal / (μ (C : Set Ω)).toReal)
            = ((ν (C : Set Ω)).toReal / (μ (C : Set Ω)).toReal) * (μ (C : Set Ω)).toReal := by
                ring
          _ = (ν (C : Set Ω)).toReal * ((μ (C : Set Ω)).toReal)⁻¹ * (μ (C : Set Ω)).toReal := by
                rw [div_eq_mul_inv]
          _ = (ν (C : Set Ω)).toReal * (((μ (C : Set Ω)).toReal)⁻¹ * (μ (C : Set Ω)).toReal) := by
                ring
          _ = (ν (C : Set Ω)).toReal := by
                rw [inv_mul_cancel₀ hμC_toReal, mul_one]
          _ = if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal := by
                simp [hμC]

-- Proof sketch: unfold `partitionAverageDensity`; each summand is an indicator of a nonnegative
-- constant, so every term in the finite sum is nonnegative.
/-- The partition-average density associated to a measurable finite partition is pointwise
nonnegative. -/
private theorem partitionAverageDensity_nonneg
    (Z : MeasurableFinpartition) (ω : Ω) :
    0 ≤ partitionAverageDensity μ ν Z ω := by
  -- Every summand is either `0` or a nonnegative cell average.
  unfold partitionAverageDensity
  refine Finset.sum_nonneg ?_
  intro C hC
  by_cases hωC : ω ∈ (C : Set Ω)
  · by_cases hμC : μ (C : Set Ω) = 0
    · simp [Set.indicator_of_mem, hωC, hμC]
    · simp [Set.indicator_of_mem, hωC, hμC, div_nonneg]
  · simp [Set.indicator_of_notMem, hωC]

/-- Helper for Example 7.39: every cell average `ν(C) / μ(C)` is nonnegative. -/
private theorem cellAverage_nonneg
    (C : Subtype (MeasurableSet : Set Ω → Prop)) :
    0 ≤ cellAverage (μ := μ) (ν := ν) C := by
  -- A finite-measure ratio is nonnegative, and the zero-denominator branch is normalized to `0`.
  unfold cellAverage
  by_cases hμC : μ (C : Set Ω) = 0
  · simp [hμC]
  · simp [hμC, div_nonneg]

/-- Helper for Example 7.39: the finite union of measurable partition cells is measurable. -/
private theorem measurableSet_cellUnion
    (S : Finset (Subtype (MeasurableSet : Set Ω → Prop))) :
    MeasurableSet (cellUnion S) := by
  -- `cellUnion` is a finite measurable union of measurable cells.
  unfold cellUnion
  exact Finset.measurableSet_biUnion _ fun C _ ↦ C.2

/-- Helper for Example 7.39: on a partition cell, the partition-average density equals the
corresponding cell average. -/
private theorem partitionAverageDensity_eq_cellAverage_of_mem
    {Z : MeasurableFinpartition}
    {C : Subtype (MeasurableSet : Set Ω → Prop)}
    (hCZ : C ∈ Z.parts) {ω : Ω} (hωC : ω ∈ (C : Set Ω)) :
    partitionAverageDensity μ ν Z ω = cellAverage (μ := μ) (ν := ν) C := by
  -- Collapse the partition sum to the unique cell containing `ω`.
  unfold partitionAverageDensity cellAverage
  rw [Finset.sum_eq_single_of_mem C hCZ]
  · simp [Set.indicator_of_mem, hωC]
  · intro D hDZ hDC
    have hωD : ω ∉ (D : Set Ω) := by
      intro hωD
      exact (disjoint_coe_of_mem_parts hDZ hCZ hDC).le_bot ⟨hωD, hωC⟩
    simp [Set.indicator_of_notMem, hωD]

/-- Helper for Example 7.39: the `L¹` tail set of a partition-average density is exactly the
union of the cells whose average is at least the threshold. -/
private theorem tailSet_partitionAverageDensity_eq_cellUnion_highRatio
    (Z : MeasurableFinpartition) (K : ℝ≥0) :
    {ω | K ≤ ‖partitionAverageDensity μ ν Z ω‖₊} =
      cellUnion (Z.parts.filter fun C ↦ (K : ℝ) ≤ cellAverage (μ := μ) (ν := ν) C) := by
  -- Normalize the tail predicate by choosing the unique partition cell containing `ω`.
  ext ω
  constructor
  · intro hω
    have hcover : ω ∈ ⋃ C ∈ Z.parts, ((C : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) := by
      simp [biUnion_parts_eq_univ Z]
    rcases Set.mem_iUnion.1 hcover with ⟨C, hωC⟩
    rcases Set.mem_iUnion.1 hωC with ⟨hCZ, hωC⟩
    have hcell :=
      partitionAverageDensity_eq_cellAverage_of_mem (μ := μ) (ν := ν) hCZ hωC
    have hω' : (K : ℝ) ≤ partitionAverageDensity μ ν Z ω := by
      simpa [Real.nnnorm_of_nonneg (partitionAverageDensity_nonneg (μ := μ) (ν := ν) Z ω)] using hω
    have hKle : (K : ℝ) ≤ cellAverage (μ := μ) (ν := ν) C := by
      simpa [hcell] using hω'
    exact Set.mem_iUnion.2 ⟨C, Set.mem_iUnion.2 ⟨Finset.mem_filter.2 ⟨hCZ, hKle⟩, hωC⟩⟩
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨C, hωC⟩
    rcases Set.mem_iUnion.1 hωC with ⟨hCS, hωC⟩
    rcases Finset.mem_filter.1 hCS with ⟨hCZ, hKle⟩
    have hcell :=
      partitionAverageDensity_eq_cellAverage_of_mem (μ := μ) (ν := ν) hCZ hωC
    have hω' : (K : ℝ) ≤ partitionAverageDensity μ ν Z ω := by
      simpa [hcell] using hKle
    simpa [Real.nnnorm_of_nonneg (partitionAverageDensity_nonneg (μ := μ) (ν := ν) Z ω)] using hω'

/-- Helper for Example 7.39: if every selected cell has positive `μ`-mass, then integrating the
partition-average density over their union recovers the `ν`-mass of that union. -/
private theorem setIntegral_partitionAverageDensity_eq_measureReal_cellUnion_of_subset
    (Z : MeasurableFinpartition)
    (S : Finset (Subtype (MeasurableSet : Set Ω → Prop)))
    (hS : S ⊆ Z.parts)
    (hμS : ∀ C ∈ S, μ (C : Set Ω) ≠ 0) :
    ∫ ω in cellUnion S, partitionAverageDensity μ ν Z ω ∂μ = ν.real (cellUnion S) := by
  -- The zero-denominator cells are absent, so the finite-sum formula is exactly the `ν`-mass sum.
  calc
    ∫ ω in cellUnion S, partitionAverageDensity μ ν Z ω ∂μ
      = ∑ C ∈ S, if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal := by
          exact setIntegral_partitionAverageDensity_eq_sum_of_subset (μ := μ) (ν := ν) Z S hS
    _ = ∑ C ∈ S, ν.real (C : Set Ω) := by
          refine Finset.sum_congr rfl ?_
          intro C hCS
          simp [Measure.real, hμS C hCS]
    _ = ν.real (cellUnion S) := by
          symm
          exact measureReal_biUnion_eq_sum_of_subset (ρ := ν) Z S hS

/-- Helper for Example 7.39: the `L¹`-norm of the indicator tail of a nonnegative
partition-average density is the integral of that density over the tail set. -/
private theorem eLpNorm_indicator_partitionAverageDensity_eq_setIntegral
    (Z : MeasurableFinpartition)
    (S : Finset (Subtype (MeasurableSet : Set Ω → Prop))) :
    eLpNorm (cellUnion S |>.indicator (partitionAverageDensity μ ν Z)) 1 μ =
      ENNReal.ofReal (∫ ω in cellUnion S, partitionAverageDensity μ ν Z ω ∂μ) := by
  -- At exponent `1`, the tail `eLpNorm` is the `lintegral` of the pointwise absolute value, which
  -- collapses to the set integral because the density is nonnegative.
  have hS_meas : MeasurableSet (cellUnion S) := measurableSet_cellUnion (S := S)
  have hInt :
      Integrable ((cellUnion S).indicator (partitionAverageDensity μ ν Z)) μ :=
    (partitionAverageDensity_integrable (μ := μ) (ν := ν) Z).indicator hS_meas
  have hnonneg :
      0 ≤ᵐ[μ] (cellUnion S).indicator (partitionAverageDensity μ ν Z) := by
    filter_upwards with ω
    by_cases hω : ω ∈ cellUnion S
    · simp [Set.indicator_of_mem, hω, partitionAverageDensity_nonneg]
    · simp [Set.indicator_of_notMem, hω]
  calc
    eLpNorm (cellUnion S |>.indicator (partitionAverageDensity μ ν Z)) 1 μ
      = ∫⁻ ω, ENNReal.ofReal (((cellUnion S).indicator (partitionAverageDensity μ ν Z)) ω) ∂μ := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          congr 1
          ext ω
          by_cases hω : ω ∈ cellUnion S
          · rw [Set.indicator_of_mem hω, Real.enorm_eq_ofReal]
            exact partitionAverageDensity_nonneg (μ := μ) (ν := ν) Z ω
          · simp [Set.indicator_of_notMem, hω]
    _ = ENNReal.ofReal (∫ ω, ((cellUnion S).indicator (partitionAverageDensity μ ν Z)) ω ∂μ) := by
          symm
          exact ofReal_integral_eq_lintegral_ofReal hInt hnonneg
    _ = ENNReal.ofReal (∫ ω in cellUnion S, partitionAverageDensity μ ν Z ω ∂μ) := by
          rw [integral_indicator hS_meas]

/-- Helper for Example 7.39: a selected high-ratio cell has positive `μ`-mass and satisfies the
cellwise inequality `K * μ(C) ≤ ν(C)` on real masses. -/
private theorem highRatioCell_nonzero_and_mulMeasureReal_le
    (Z : MeasurableFinpartition) {K : ℝ} (hK : 0 < K)
    {C : Subtype (MeasurableSet : Set Ω → Prop)}
    (hC : C ∈ Z.parts.filter fun C ↦ K ≤ cellAverage (μ := μ) (ν := ν) C) :
    μ (C : Set Ω) ≠ 0 ∧ K * μ.real (C : Set Ω) ≤ ν.real (C : Set Ω) := by
  -- The high-ratio condition rules out the zero-denominator branch and then clears the division.
  rcases Finset.mem_filter.1 hC with ⟨_, hKC⟩
  have hμC : μ (C : Set Ω) ≠ 0 := by
    intro hμC
    have : K ≤ 0 := by
      simpa [cellAverage, hμC] using hKC
    exact (not_le_of_gt hK) this
  have hμC_toReal_pos : 0 < (μ (C : Set Ω)).toReal :=
    ENNReal.toReal_pos hμC (by finiteness)
  have hμC_toReal_ne : (μ (C : Set Ω)).toReal ≠ 0 := hμC_toReal_pos.ne'
  refine ⟨hμC, ?_⟩
  have hKC' :
      K * (μ (C : Set Ω)).toReal ≤
        cellAverage (μ := μ) (ν := ν) C * (μ (C : Set Ω)).toReal :=
    mul_le_mul_of_nonneg_right hKC hμC_toReal_pos.le
  calc
    K * μ.real (C : Set Ω) = K * (μ (C : Set Ω)).toReal := rfl
    _ ≤ cellAverage (μ := μ) (ν := ν) C * (μ (C : Set Ω)).toReal := hKC'
    _ = ν.real (C : Set Ω) := by
      rw [Measure.real, cellAverage, if_neg hμC]
      field_simp [hμC_toReal_ne]

private theorem measureReal_cellUnion_highRatio_le_div
    (Z : MeasurableFinpartition) {K : ℝ} (hK : 0 < K) :
    μ.real
        (cellUnion (Z.parts.filter fun C ↦ K ≤ cellAverage (μ := μ) (ν := ν) C)) ≤
      ν.real Set.univ / K := by
  -- Sum the cellwise high-ratio inequalities and rewrite both sums as masses of the filtered union.
  let S := Z.parts.filter fun C ↦ K ≤ cellAverage (μ := μ) (ν := ν) C
  have hS : S ⊆ Z.parts := by
    intro C hC
    exact (Finset.mem_filter.1 hC).1
  have hsum :
      K * ∑ C ∈ S, μ.real (C : Set Ω) ≤
        ∑ C ∈ S, ν.real (C : Set Ω) := by
    calc
      K * ∑ C ∈ S, μ.real (C : Set Ω)
        = ∑ C ∈ S, K * μ.real (C : Set Ω) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ C ∈ S, ν.real (C : Set Ω) := by
            refine Finset.sum_le_sum ?_
            intro C hC
            exact (highRatioCell_nonzero_and_mulMeasureReal_le
              (μ := μ) (ν := ν) Z hK hC).2
  have hμUnion :
      μ.real (cellUnion S) = ∑ C ∈ S, μ.real (C : Set Ω) :=
    measureReal_biUnion_eq_sum_of_subset (ρ := μ) Z S hS
  have hνUnion :
      ν.real (cellUnion S) = ∑ C ∈ S, ν.real (C : Set Ω) :=
    measureReal_biUnion_eq_sum_of_subset (ρ := ν) Z S hS
  have hcellUnion :
      K * μ.real (cellUnion S) ≤ ν.real (cellUnion S) := by
    rw [hμUnion, hνUnion]
    exact hsum
  have hνUnion_le : ν.real (cellUnion S) ≤ ν.real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  exact (le_div_iff₀ hK).2 <| by
    simpa [mul_comm] using le_trans hcellUnion hνUnion_le

/-- Helper for Example 7.39: absolute continuity gives the tail bound required by
`uniformIntegrable_of` for the partition-average family. -/
private theorem tailBound_partitionAverageDensity_of_absolutelyContinuous
    (hνμ : ν ≪ μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ≥0,
      ∀ Z : MeasurableFinpartition,
        eLpNorm
            ({ω | K ≤ ‖partitionAverageDensity μ ν Z ω‖₊}.indicator
              (partitionAverageDensity μ ν Z)) 1 μ ≤ ENNReal.ofReal ε := by
  -- Route correction: use total continuity directly on the normalized tail union instead of
  -- reopening the small-set criterion from the source proof.
  have htc : TotallyContinuous ν μ :=
    (absolutelyContinuous_iff_totallyContinuous (μ := μ) (ν := ν)).1 hνμ
  have hε_enn : 0 < ENNReal.ofReal ε := by
    simpa using hε
  obtain ⟨δ, hδ_pos, hδ⟩ := htc hε_enn
  have tailBound_of_measureBound :
      ∀ {K : ℝ≥0}, 0 < (K : ℝ) →
        (∀ Z : MeasurableFinpartition,
          μ (cellUnion (Z.parts.filter fun C ↦ (K : ℝ) ≤ cellAverage (μ := μ) (ν := ν) C)) < δ) →
        ∀ Z : MeasurableFinpartition,
          eLpNorm
              ({ω | K ≤ ‖partitionAverageDensity μ ν Z ω‖₊}.indicator
                (partitionAverageDensity μ ν Z)) 1 μ ≤ ENNReal.ofReal ε := by
    intro K hK hμtail Z
    let S := Z.parts.filter fun C ↦ (K : ℝ) ≤ cellAverage (μ := μ) (ν := ν) C
    have hS : S ⊆ Z.parts := by
      intro C hC
      exact (Finset.mem_filter.1 hC).1
    have hμS : ∀ C ∈ S, μ (C : Set Ω) ≠ 0 := by
      intro C hC
      exact (highRatioCell_nonzero_and_mulMeasureReal_le
        (μ := μ) (ν := ν) Z hK hC).1
    have hνtail : ν (cellUnion S) < ENNReal.ofReal ε :=
      hδ (measurableSet_cellUnion (S := S)) (hμtail Z)
    calc
      eLpNorm
          ({ω | K ≤ ‖partitionAverageDensity μ ν Z ω‖₊}.indicator
            (partitionAverageDensity μ ν Z)) 1 μ
        = eLpNorm (cellUnion S |>.indicator (partitionAverageDensity μ ν Z)) 1 μ := by
            simpa [S] using congrArg
              (fun s : Set Ω ↦ eLpNorm (s.indicator (partitionAverageDensity μ ν Z)) 1 μ)
              (tailSet_partitionAverageDensity_eq_cellUnion_highRatio
                (μ := μ) (ν := ν) Z K)
      _ = ENNReal.ofReal (∫ ω in cellUnion S, partitionAverageDensity μ ν Z ω ∂μ) := by
            exact eLpNorm_indicator_partitionAverageDensity_eq_setIntegral
              (μ := μ) (ν := ν) Z S
      _ = ENNReal.ofReal (ν.real (cellUnion S)) := by
            congr 1
            exact setIntegral_partitionAverageDensity_eq_measureReal_cellUnion_of_subset
              (μ := μ) (ν := ν) Z S hS hμS
      _ ≤ ENNReal.ofReal ε := by
            exact ENNReal.ofReal_le_ofReal
              (ENNReal.toReal_lt_of_lt_ofReal hνtail).le
  by_cases hδ_top : δ = ∞
  · -- If the total-continuity radius is `∞`, every finite-measure tail set is already small.
    refine ⟨1, tailBound_of_measureBound (K := 1) (by norm_num) ?_⟩
    intro Z
    simpa [hδ_top] using
      (measure_lt_top μ
        (cellUnion (Z.parts.filter fun C ↦ (1 : ℝ) ≤ cellAverage (μ := μ) (ν := ν) C)))
  · -- Otherwise choose a real threshold large enough to force the normalized tail union below `δ`.
    have hδ_real_pos : 0 < δ.toReal :=
      ENNReal.toReal_pos hδ_pos.ne' hδ_top
    let K0 : ℝ := ν.real Set.univ / δ.toReal + 1
    have hK0_pos : 0 < K0 := by
      dsimp [K0]
      positivity
    refine ⟨⟨K0, hK0_pos.le⟩, tailBound_of_measureBound (K := ⟨K0, hK0_pos.le⟩) hK0_pos ?_⟩
    intro Z
    let S := Z.parts.filter fun C ↦ K0 ≤ cellAverage (μ := μ) (ν := ν) C
    have hμreal_le : μ.real (cellUnion S) ≤ ν.real Set.univ / K0 := by
      simpa [S, K0] using
        measureReal_cellUnion_highRatio_le_div (μ := μ) (ν := ν) Z hK0_pos
    have hμreal_lt : μ.real (cellUnion S) < δ.toReal := by
      refine hμreal_le.trans_lt ?_
      have hδ_real_ne : δ.toReal ≠ 0 := ne_of_gt hδ_real_pos
      refine (div_lt_iff₀ hK0_pos).2 ?_
      dsimp [K0]
      field_simp [hδ_real_ne]
      nlinarith [measureReal_nonneg (μ := ν) (s := (Set.univ : Set Ω)), hδ_real_pos]
    have hμlt_ofReal : μ (cellUnion S) < ENNReal.ofReal δ.toReal :=
      (ENNReal.lt_ofReal_iff_toReal_lt (by finiteness)).2 hμreal_lt
    simpa [ENNReal.ofReal_toReal hδ_top] using hμlt_ofReal

/-- Helper for Example 7.39: the two measurable cells `A` and `Aᶜ` used in the reverse
implication. -/
private def twoCellParts (A : Set Ω) (hA : MeasurableSet A) :
    Finset (Subtype (MeasurableSet : Set Ω → Prop)) :=
  {⟨A, hA⟩, ⟨Aᶜ, hA.compl⟩}

/-- Helper for Example 7.39: the two candidate cells `A` and `Aᶜ` are pairwise disjoint. -/
private theorem twoCellParts_supIndep (A : Set Ω) (hA : MeasurableSet A) :
    (twoCellParts (Ω := Ω) A hA).SupIndep id := by
  -- The only distinct parts are `A` and `Aᶜ`, which are disjoint.
  refine Finset.supIndep_iff_pairwiseDisjoint.mpr ?_
  intro C hC D hD hCD
  have hC_cases :
      C = (⟨A, hA⟩ : Subtype (MeasurableSet : Set Ω → Prop)) ∨
        C = ⟨Aᶜ, hA.compl⟩ := by
    simpa [twoCellParts] using hC
  have hD_cases :
      D = (⟨A, hA⟩ : Subtype (MeasurableSet : Set Ω → Prop)) ∨
        D = ⟨Aᶜ, hA.compl⟩ := by
    simpa [twoCellParts] using hD
  rcases hC_cases with rfl | rfl <;> rcases hD_cases with rfl | rfl
  · exact (hCD rfl).elim
  · exact
      (disjoint_subtype_iff (fun {_ _} hx hy ↦ hx.inter hy) MeasurableSet.empty).2 <| by
        simpa using disjoint_compl_right
  · exact
      (disjoint_subtype_iff (fun {_ _} hx hy ↦ hx.inter hy) MeasurableSet.empty).2 <| by
        simpa using disjoint_compl_left
  · exact (hCD rfl).elim

/-- Helper for Example 7.39: the two candidate cells `A` and `Aᶜ` cover `Ω`. -/
private theorem twoCellParts_sup_eq_top (A : Set Ω) (hA : MeasurableSet A) :
    (twoCellParts (Ω := Ω) A hA).sup id = ⊤ := by
  -- The supremum of the two cells is exactly the measurable whole space.
  apply Subtype.ext
  ext ω
  simp [twoCellParts]

/-- Helper for Example 7.39: the measurable two-cell partition `{A, Aᶜ}` of `Ω`. -/
private noncomputable def twoCellPartition (A : Set Ω) (hA : MeasurableSet A) :
    MeasurableFinpartition :=
  Finpartition.ofErase (twoCellParts (Ω := Ω) A hA)
    (twoCellParts_supIndep (Ω := Ω) A hA)
    (twoCellParts_sup_eq_top (Ω := Ω) A hA)

/-- Helper for Example 7.39: the parts of the two-cell partition are the nonempty members of
`{A, Aᶜ}`. -/
private theorem twoCellPartition_parts
    (A : Set Ω) (hA : MeasurableSet A) :
    (twoCellPartition (Ω := Ω) A hA).parts =
      (twoCellParts (Ω := Ω) A hA).erase ⊥ := by
  -- Unfold the `Finpartition.ofErase` constructor once so later proofs can reason on the parts.
  simp [twoCellPartition, twoCellParts]

/-- Helper for Example 7.39: when `μ A = 0` and `μ ≠ 0`, the complement cell survives in the
two-cell partition. -/
private theorem compl_mem_twoCellPartition_parts_of_null
    {A : Set Ω} (hA : MeasurableSet A) (hμA : μ A = 0) (hμ : μ ≠ 0) :
    (⟨Aᶜ, hA.compl⟩ : Subtype (MeasurableSet : Set Ω → Prop)) ∈
      (twoCellPartition (Ω := Ω) A hA).parts := by
  -- The complement cell would be erased only if it were empty, but that would force `μ = 0`.
  have hμAc_ne : μ Aᶜ ≠ 0 := by
    intro hμAc
    apply hμ
    exact Measure.measure_univ_eq_zero.mp <| by
      rw [← measure_add_measure_compl hA, hμA, hμAc, zero_add]
  have hAc_ne_bot :
      (⟨Aᶜ, hA.compl⟩ : Subtype (MeasurableSet : Set Ω → Prop)) ≠ ⊥ := by
    intro hbot
    apply hμAc_ne
    simpa using congrArg (fun s : Subtype (MeasurableSet : Set Ω → Prop) ↦ μ (s : Set Ω)) hbot
  rw [twoCellPartition_parts]
  simp [twoCellParts, hAc_ne_bot]

/-- Helper for Example 7.39: every part of the two-cell partition is either `A` or `Aᶜ`. -/
private theorem eq_self_or_compl_of_mem_twoCellPartition_parts
    {A : Set Ω} (hA : MeasurableSet A)
    {C : Subtype (MeasurableSet : Set Ω → Prop)}
    (hC : C ∈ (twoCellPartition (Ω := Ω) A hA).parts) :
    C = (⟨A, hA⟩ : Subtype (MeasurableSet : Set Ω → Prop)) ∨ C = ⟨Aᶜ, hA.compl⟩ := by
  -- The partition is built from exactly the two cells `A` and `Aᶜ`.
  have hC' : C ∈ twoCellParts (Ω := Ω) A hA := Finset.mem_of_mem_erase <| by
    rw [← twoCellPartition_parts (Ω := Ω) A hA]
    exact hC
  simpa [twoCellParts] using hC'

/-- Helper for Example 7.39: when `A` is `μ`-null and `μ ≠ 0`, the partition-average density for
the two-cell partition `{A, Aᶜ}` integrates to `ν(Aᶜ)`. -/
private theorem integral_partitionAverageDensity_twoCell_of_null
    {A : Set Ω} (hA : MeasurableSet A) (hμA : μ A = 0) (hμ : μ ≠ 0) :
    ∫ ω, partitionAverageDensity μ ν (twoCellPartition (Ω := Ω) A hA) ω ∂μ = ν.real Aᶜ := by
  -- Collapse the full-partition integral to the complement cell, whose average survives because
  -- `μ ≠ 0`.
  let Z := twoCellPartition (Ω := Ω) A hA
  have hAc_mem :
      (⟨Aᶜ, hA.compl⟩ : Subtype (MeasurableSet : Set Ω → Prop)) ∈ Z.parts := by
    simpa [Z] using
      compl_mem_twoCellPartition_parts_of_null (μ := μ) (hA := hA) hμA hμ
  have hμAc_ne : μ Aᶜ ≠ 0 := by
    intro hμAc
    apply hμ
    exact Measure.measure_univ_eq_zero.mp <| by
      rw [← measure_add_measure_compl hA, hμA, hμAc, zero_add]
  have hAc_ne_bot :
      (⟨Aᶜ, hA.compl⟩ : Subtype (MeasurableSet : Set Ω → Prop)) ≠ ⊥ := by
    intro hbot
    apply hμAc_ne
    simpa using congrArg (fun s : Subtype (MeasurableSet : Set Ω → Prop) ↦ μ (s : Set Ω)) hbot
  rw [← setIntegral_univ]
  calc
    ∫ ω in Set.univ, partitionAverageDensity μ ν Z ω ∂μ
      = ∑ C ∈ Z.parts, if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal := by
          simpa [Z, cellUnion, biUnion_parts_eq_univ Z] using
            setIntegral_partitionAverageDensity_eq_sum_of_subset
              (μ := μ) (ν := ν) Z Z.parts subset_rfl
    _ = if μ Aᶜ = 0 then 0 else (ν Aᶜ).toReal := by
          rw [twoCellPartition_parts]
          by_cases hA_bot : (⟨A, hA⟩ : Subtype (MeasurableSet : Set Ω → Prop)) = ⊥
          · have hparts :
                (twoCellParts (Ω := Ω) A hA).erase ⊥ =
                  {⟨Aᶜ, hA.compl⟩} := by
              ext C
              by_cases hC_bot : C = ⊥
              · subst C
                simp [twoCellParts, hA_bot]
                simpa [eq_comm] using hAc_ne_bot
              · simp [twoCellParts, hA_bot, hC_bot]
            rw [hparts]
            simp [hμAc_ne]
          · have hparts :
                (twoCellParts (Ω := Ω) A hA).erase ⊥ =
                  twoCellParts (Ω := Ω) A hA := by
              ext C
              by_cases hC_bot : C = ⊥
              · subst C
                simp [twoCellParts]
                constructor
                · simpa [eq_comm] using hA_bot
                · simpa [eq_comm] using hAc_ne_bot
              · simp [twoCellParts, hC_bot]
            rw [hparts]
            simp [twoCellParts, hμA, hμAc_ne]
    _ = ν.real Aᶜ := by
          simp [Measure.real, hμAc_ne]

/-- Helper for Example 7.39: the partition-average criterion forces `ν` to vanish on every
measurable `μ`-null set. -/
private theorem nullOfPartitionAverageCriterion
    (hcrit :
      UniformIntegrable (fun Z : MeasurableFinpartition ↦ partitionAverageDensity μ ν Z) 1 μ ∧
        ∀ Z : MeasurableFinpartition,
          ∫ ω, partitionAverageDensity μ ν Z ω ∂μ = (ν Set.univ).toReal)
    {A : Set Ω} (hA : MeasurableSet A) (hμA : μ A = 0) :
    ν A = 0 := by
  -- Test the criterion on `{A, Aᶜ}`; if `μ = 0`, first force `ν = 0` from the total-mass clause.
  by_cases hμ : μ = 0
  · have hνuniv_toReal : (ν Set.univ).toReal = 0 := by
      simpa [hμ, partitionAverageDensity] using (hcrit.2 (⊤ : MeasurableFinpartition)).symm
    have hνuniv : ν Set.univ = 0 :=
      ((ENNReal.toReal_eq_zero_iff (ν Set.univ)).1 hνuniv_toReal).resolve_right
        (measure_lt_top ν Set.univ).ne
    exact measure_mono_null (Set.subset_univ A) hνuniv
  · have hIntegral_univ :
        ∫ ω, partitionAverageDensity μ ν (twoCellPartition (Ω := Ω) A hA) ω ∂μ =
          ν.real Set.univ :=
      hcrit.2 (twoCellPartition (Ω := Ω) A hA)
    have hIntegral_compl :
        ∫ ω, partitionAverageDensity μ ν (twoCellPartition (Ω := Ω) A hA) ω ∂μ =
          ν.real Aᶜ :=
      integral_partitionAverageDensity_twoCell_of_null (μ := μ) (ν := ν) hA hμA hμ
    have hνcompl : ν.real Aᶜ = ν.real Set.univ := by
      rw [← hIntegral_compl, hIntegral_univ]
    have hνA_toReal : (ν A).toReal = 0 := by
      have hsum : ν.real A + ν.real Aᶜ = ν.real Set.univ :=
        measureReal_add_measureReal_compl (μ := ν) hA
      rw [hνcompl] at hsum
      have hsum' : ν.real A + ν.real Set.univ = 0 + ν.real Set.univ := by
        simpa using hsum
      exact add_right_cancel hsum'
    exact ((ENNReal.toReal_eq_zero_iff (ν A)).1 hνA_toReal).resolve_right
      (measure_lt_top ν A).ne

/-- Helper for Example 7.39: under `ν ≪ μ`, every partition-average density integrates to the
total mass `ν(Ω)`. -/
private theorem integral_partitionAverageDensity_eq_totalMass
    (hνμ : ν ≪ μ)
    (Z : MeasurableFinpartition) :
    ∫ ω, partitionAverageDensity μ ν Z ω ∂μ = ν.real Set.univ := by
  -- First collapse the full-cell union integral to the finite sum over partition atoms.
  rw [← setIntegral_univ]
  calc
    ∫ ω in Set.univ, partitionAverageDensity μ ν Z ω ∂μ
      = ∑ C ∈ Z.parts, if μ (C : Set Ω) = 0 then 0 else (ν (C : Set Ω)).toReal := by
          simpa [cellUnion, biUnion_parts_eq_univ Z] using
            setIntegral_partitionAverageDensity_eq_sum_of_subset
              (μ := μ) (ν := ν) Z Z.parts subset_rfl
    _ = ∑ C ∈ Z.parts, ν.real (C : Set Ω) := by
          refine Finset.sum_congr rfl ?_
          intro C hCZ
          by_cases hμC : μ (C : Set Ω) = 0
          · have hνC : ν (C : Set Ω) = 0 := hνμ hμC
            simp [hμC, hνC, Measure.real]
          · simp [hμC, Measure.real]
    _ = ν.real (cellUnion Z.parts) := by
          symm
          exact measureReal_biUnion_eq_sum_of_subset (ρ := ν) Z Z.parts subset_rfl
    _ = ν.real Set.univ := by
          simp [cellUnion, biUnion_parts_eq_univ Z]

/-- The partition-average criterion from Example 7.39: the family of densities obtained by
averaging `ν` over the cells of each finite measurable partition is uniformly integrable in
`L¹(μ)`, and every such density integrates to the total mass `ν(Ω)`. -/
def PartitionAverageCriterion : Prop :=
  UniformIntegrable (fun Z : MeasurableFinpartition ↦ partitionAverageDensity μ ν Z) 1 μ ∧
    ∀ Z : MeasurableFinpartition,
      ∫ ω, partitionAverageDensity μ ν Z ω ∂μ = (ν Set.univ).toReal

-- Proof sketch: for `ν ≪ μ`, the preceding theorem gives total continuity, and the source proof
-- then yields the uniform-integrability criterion for the partition averages together with the
-- integral identity. Conversely, if the family is uniformly integrable and every partition average
-- integrates to `ν(Ω)`, test the two-cell partition `{A, Aᶜ}` for a `μ`-null set `A`.
/-- Example 7.39: for finite measures `μ` and `ν`, the family of partition-average densities
associated to finite measurable partitions of `Ω` is uniformly integrable in `L¹(μ)` and each
member integrates to `ν(Ω)` if and only if `ν` is absolutely continuous with respect to `μ`. This
is the canonical core statement; the equivalent total-continuity formulation is recorded below. -/
theorem partitionAverageDensities_uniformIntegrable_integral_iff_absolutelyContinuous :
    PartitionAverageCriterion μ ν ↔ ν ≪ μ := by
  constructor
  · intro hcrit
    -- The reverse direction only needs the exact integral clause; the two-cell partition detects
    -- every measurable `μ`-null set.
    refine AbsolutelyContinuous.mk fun A hA hμA ↦ ?_
    exact nullOfPartitionAverageCriterion (μ := μ) (ν := ν) hcrit hA hμA
  · intro hνμ
    -- The forward direction is split into the tail bound for `uniformIntegrable_of` and the exact
    -- total-mass formula from the finite-sum computation already proved above.
    refine ⟨?_, integral_partitionAverageDensity_eq_totalMass (μ := μ) (ν := ν) hνμ⟩
    refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
      (fun Z ↦ partitionAverageDensity_aestronglyMeasurable (μ := μ) (ν := ν) Z) ?_
    intro ε hε
    exact tailBound_partitionAverageDensity_of_absolutelyContinuous (μ := μ) (ν := ν) hνμ hε

-- Proof sketch: combine the preceding equivalence with
-- `absolutelyContinuous_iff_totallyContinuous`.
/-- Example 7.39: for finite measures `μ` and `ν`, the following are equivalent: the family of
partition-average densities associated to finite measurable partitions of `Ω` is uniformly
integrable in `L¹(μ)` and each member integrates to `ν(Ω)`; `ν` is absolutely continuous with
respect to `μ`; and `ν` is totally continuous with respect to `μ`. -/
theorem partitionAverageDensities_tfae_absolutelyContinuous_totallyContinuous :
    List.TFAE [PartitionAverageCriterion μ ν, ν ≪ μ, TotallyContinuous ν μ] := by
  -- Package the two already-established equivalences into the standard three-term `TFAE`.
  tfae_have 1 ↔ 2 := by
    exact partitionAverageDensities_uniformIntegrable_integral_iff_absolutelyContinuous
      (μ := μ) (ν := ν)
  tfae_have 2 ↔ 3 := by
    exact absolutelyContinuous_iff_totallyContinuous (μ := μ) (ν := ν)
  tfae_finish

end Measure
end MeasureTheory

/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9_part2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_16.OrderedFlowCoverApi
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_claim_5_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_15

open scoped BigOperators

-- Domain sampling for this theorem:
-- * primary domain: single-node flow covers and their lifted facet-defining inequalities
-- * core/canonical owner reused here: `single_node_flow_set`, `IsFlowCover`, `flow_cover_excess`,
--   and especially the zero-lifted cover owner `flow_cover_value`
-- * source-facing data kept here: an ordering of the cover `C`, its derived ordered coefficients
--   and partial sums, the cut index `r`, and the admissible lifting pairs from Theorem 7.16

section Theorem716

variable {n : ℕ}

open OrderedFlowCover

namespace OrderedFlowCover

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the linear part of the lifted
flow-cover functional. -/
noncomputable def flowCoverLiftedSupportLinearMap
    (a α β : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
  flowCoverSupportLinearMap a b C +
    ∑ i ∈ Finset.univ \ C,
      (α i • ((LinearMap.proj i).comp (LinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))) +
        β i • ((LinearMap.proj i).comp (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ))))

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: evaluation of the canonical
lifted support map separates the cover and outside-coordinate terms. -/
theorem flowCoverLiftedSupportLinearMap_apply
    (a α β : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flowCoverLiftedSupportLinearMap a α β b C p =
      flowCoverSupportLinearMap a b C p +
        ∑ i ∈ Finset.univ \ C, (α i * p.2 i + β i * p.1 i) := by
  classical
  -- Evaluate each projection in the finite sum, keeping the support-map normal form explicit.
  simp [flowCoverLiftedSupportLinearMap]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the lifted value is its linear
support map plus the fixed cover penalty. -/
theorem flow_cover_lifted_value_eq_support_add_constant
    (a α β : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    flow_cover_lifted_value a b C α β p =
      flowCoverLiftedSupportLinearMap a α β b C p +
        ∑ j ∈ C, flowCoverSupportCoeff a b C j := by
  classical
  have hbase :
      flow_cover_value a b C p =
        flowCoverSupportLinearMap a b C p +
          ∑ j ∈ C, flowCoverSupportCoeff a b C j := by
    -- Normalize the older support-map theorem to its named linear-map interface.
    simpa [flowCoverSupportLinearMap, flowCoverSupportCoeff] using
      flow_cover_value_eq_linear_part_add_constant a b C p
  -- Substitute both linear-part formulas and reassociate the scalar sums.
  rw [flow_cover_lifted_value_eq, hbase, flowCoverLiftedSupportLinearMap_apply]
  ring

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: projection onto the cover
coordinates in a single variable block. -/
noncomputable def flowCoverCoordinateProjection
    (C : Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi (fun i ↦ if i ∈ C then LinearMap.proj i else 0)

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: projection of both variable
blocks onto the cover coordinates. -/
noncomputable def flowCoverPairProjection
    (C : Finset (Fin n)) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ((flowCoverCoordinateProjection C).comp
      (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ))).prod
    ((flowCoverCoordinateProjection C).comp
      (LinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)))

end OrderedFlowCover

/-- Helper for Theorem 7.16: every entry of an enumerating order belongs to the cover it
enumerates. -/
theorem coverOrder_mem_cover
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (hcoverOrder : enumerates C coverOrder)
    (h : Fin C.card) :
    coverOrder h ∈ C := by
  -- Read membership directly from the range description of the ordered cover.
  have hmem : coverOrder h ∈ Set.range coverOrder := ⟨h, rfl⟩
  rw [enumerates] at hcoverOrder
  rw [hcoverOrder] at hmem
  exact hmem

/-- Helper for Theorem 7.16: a valid cut index forces the cover to be nonempty. -/
theorem cutIndex_nonempty
    (a : Fin n → ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    {lam : ℝ} {r : ℕ}
    (hr : isCutIndex a C coverOrder lam r) :
    C.Nonempty := by
  -- Unpack the source cut-index bounds to see that the ordered cover has positive cardinality.
  rcases hr with ⟨hr_pos, hr_le, _, _⟩
  have hcard_pos : 0 < C.card := lt_of_lt_of_le hr_pos hr_le
  exact Finset.card_pos.mp hcard_pos

/-- Helper for Theorem 7.16: a valid cut index exhibits a cover coefficient strictly above the
excess parameter `λ`. -/
theorem isCutIndex_exists_gt
    (a : Fin n → ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    {lam : ℝ} {r : ℕ}
    (hcoverOrder : enumerates C coverOrder)
    (hr : isCutIndex a C coverOrder lam r) :
    ∃ j ∈ C, lam < a j := by
  rcases hr with ⟨hr_pos, hr_le, hlt, _⟩
  have hpred_lt_r : r - 1 < r := Nat.pred_lt (Nat.ne_of_gt hr_pos)
  have hpred_lt_card : r - 1 < C.card := lt_of_lt_of_le hpred_lt_r hr_le
  have hweight :
      weight C a coverOrder r = a (coverOrder ⟨r - 1, hpred_lt_card⟩) := by
    -- Specialize `weight_succ` before rewriting the dependent index bound.
    have hweightPred := weight_succ C a coverOrder hpred_lt_card
    rw [Nat.sub_add_cancel hr_pos] at hweightPred
    exact hweightPred
  refine ⟨coverOrder ⟨r - 1, hpred_lt_card⟩, ?_, ?_⟩
  · -- The cut position lies in the enumerated cover.
    exact coverOrder_mem_cover C coverOrder hcoverOrder ⟨r - 1, hpred_lt_card⟩
  · -- The strict source inequality `λ < a_{j_r}` is exactly the required witness.
    simpa [hweight] using hlt

/-- Helper for Theorem 7.16: the cut-index inequality supplies the `λ < max_{j ∈ C} a j`
hypothesis needed for the zero-lift facet theorem. -/
theorem isCutIndex_lt_coverSup
    (a : Fin n → ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    {lam : ℝ} {r : ℕ}
    (hcoverOrder : enumerates C coverOrder)
    (hr : isCutIndex a C coverOrder lam r) :
    lam < C.sup' (cutIndex_nonempty a C coverOrder hr) a := by
  -- Convert the explicit witness from `isCutIndex_exists_gt` into the `sup'` formulation.
  exact
    (Finset.lt_sup'_iff (cutIndex_nonempty a C coverOrder hr)).2
      (isCutIndex_exists_gt a C coverOrder hcoverOrder hr)

/-- Helper for Theorem 7.16: the cut-index data already certifies the base zero-lifted flow-cover
inequality as facet-defining. -/
theorem zeroLiftingFacetDefining_of_isCutIndex
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    flow_cover_inequality_facet_defining a b C := by
  -- Record the canonical excess data needed by Theorem 7.9.
  have hCnonempty : C.Nonempty := cutIndex_nonempty a C coverOrder hr
  have hlam_pos : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
  have hcover_sum : C.sum a = b + flow_cover_excess a b C := by
    -- Rearrange the definition of the excess into the source sum equation.
    rw [flow_cover_excess_eq_sum_sub]
    linarith
  have hlam_max :
      flow_cover_excess a b C < C.sup' hCnonempty a := by
    -- The cut index directly supplies the strict-cover-maximum witness.
    exact isCutIndex_lt_coverSup a C coverOrder hcoverOrder hr
  exact
    flow_cover_zero_lifting_facet_defining_of_lt_max
      b
      a
      C
      (flow_cover_excess a b C)
      ha_nonneg
      hCnonempty
      hcover_sum
      hlam_pos
      hlam_max

/-- Helper for Theorem 7.16: enumerating the cover does not change the flow-cover excess after
reindexing the cover capacities by `coverOrder`. -/
theorem flowCoverExcess_comp_coverOrder_eq
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (hcoverOrder : enumerates C coverOrder) :
    flow_cover_excess (a ∘ coverOrder) b Finset.univ = flow_cover_excess a b C := by
  classical
  -- Reindex the universal sum along the embedding realizing the ordered cover.
  have himage : Finset.univ.map coverOrder = C := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, -, rfl⟩
      exact coverOrder_mem_cover C coverOrder hcoverOrder i
    · intro hj
      have hjSet : j ∈ (↑C : Set (Fin n)) := by
        simpa using hj
      rw [← hcoverOrder] at hjSet
      rcases hjSet with ⟨i, rfl⟩
      exact Finset.mem_map.mpr ⟨i, by simp, rfl⟩
  calc
    flow_cover_excess (a ∘ coverOrder) b Finset.univ
        = (∑ i ∈ Finset.univ, a (coverOrder i)) - b := by
            rw [flow_cover_excess_eq_sum_sub]
            simp only [Function.comp_apply]
    _ = (∑ j ∈ Finset.univ.map coverOrder, a j) - b := by
          rw [Finset.sum_map]
    _ = C.sum a - b := by
          rw [himage]
    _ = flow_cover_excess a b C := by
          rw [flow_cover_excess_eq_sum_sub]

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: reindexing a flow cover by an
enumerating order gives a full-support flow cover. -/
theorem isFlowCover_comp_coverOrder
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder) :
    IsFlowCover (a ∘ coverOrder) b Finset.univ := by
  have hexcess := flowCoverExcess_comp_coverOrder_eq a b C coverOrder hcoverOrder
  rw [flow_cover_excess_eq_sum_sub, flow_cover_excess_eq_sum_sub] at hexcess
  simp only [Function.comp_apply] at hexcess
  -- The reindexed sum is the original cover sum, so strict cover excess is preserved.
  rw [isFlowCover_iff]
  change b < ∑ j : Fin C.card, a (coverOrder j)
  linarith [hC.sum_gt_rhs]

/-- Helper for Theorem 7.16: the excess parameter `λ` lies below the first ordered cover
coefficient. -/
theorem flowCoverExcess_lt_firstOrderedWeight
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    flow_cover_excess a b C < weight C a coverOrder 1 := by
  rcases hr with ⟨hr_pos, hr_le, hcut, _⟩
  have hzero_lt_card : 0 < C.card := lt_of_lt_of_le hr_pos hr_le
  have hpred_lt_card : r - 1 < C.card := lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hr_pos)) hr_le
  have hcutWeight :
      weight C a coverOrder r = a (coverOrder ⟨r - 1, hpred_lt_card⟩) := by
    -- Specialize `weight_succ` before rewriting the dependent index bound.
    have hweightPred := weight_succ C a coverOrder hpred_lt_card
    rw [Nat.sub_add_cancel hr_pos] at hweightPred
    exact hweightPred
  have hfirstWeight :
      weight C a coverOrder 1 = a (coverOrder ⟨0, hzero_lt_card⟩) := by
    -- The first source coefficient is the zeroth entry of the ordered enumeration.
    simpa using weight_succ C a coverOrder hzero_lt_card
  have hmono :
      a (coverOrder ⟨r - 1, hpred_lt_card⟩) ≤ a (coverOrder ⟨0, hzero_lt_card⟩) := by
    -- Antitonicity makes the first ordered coefficient dominate every later one.
    exact hordered
      (show (⟨0, hzero_lt_card⟩ : Fin C.card) ≤ ⟨r - 1, hpred_lt_card⟩ from Nat.zero_le _)
  rw [hfirstWeight]
  exact lt_of_lt_of_le (by simpa [hcutWeight] using hcut) hmono

/-- Helper for Theorem 7.16: the excess parameter `λ` lies strictly below the full cover sum. -/
theorem flowCoverExcess_lt_coverSum
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    flow_cover_excess a b C < ∑ j ∈ C, a j := by
  have hzero_lt_card : 0 < C.card := by
    rcases hr with ⟨hr_pos, hr_le, _, _⟩
    exact lt_of_lt_of_le hr_pos hr_le
  have hfirst_mem : coverOrder ⟨0, hzero_lt_card⟩ ∈ C :=
    coverOrder_mem_cover C coverOrder hcoverOrder ⟨0, hzero_lt_card⟩
  have hfirst_le_sum :
      a (coverOrder ⟨0, hzero_lt_card⟩) ≤ ∑ j ∈ C, a j := by
    -- A single nonnegative cover coefficient is bounded by the whole nonnegative cover sum.
    exact Finset.single_le_sum (fun j hj ↦ ha_nonneg j) hfirst_mem
  have hlt_first :
      flow_cover_excess a b C < weight C a coverOrder 1 :=
    flowCoverExcess_lt_firstOrderedWeight a b C coverOrder r hordered hr
  have hfirstWeight :
      weight C a coverOrder 1 = a (coverOrder ⟨0, hzero_lt_card⟩) := by
    -- Normalize the first ordered weight before comparing it to the cover sum.
    simpa using weight_succ C a coverOrder hzero_lt_card
  rw [hfirstWeight] at hlt_first
  exact lt_of_lt_of_le hlt_first hfirst_le_sum

/-- Helper for Theorem 7.16: the common lifting function takes the source value `0` at the
origin. -/
theorem flowCoverLiftingFunction_zero
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    flow_cover_lifting_function
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder)
        0 = 0 := by
  have hb_pos : 0 < b := by
    -- The cut-index coefficient bound forces the excess to stay strictly below the cover sum.
    have hlt_sum :
        flow_cover_excess a b C < ∑ j ∈ C, a j :=
      flowCoverExcess_lt_coverSum a b C coverOrder r ha_nonneg hcoverOrder hordered hr
    rw [flow_cover_excess_eq_sum_sub] at hlt_sum
    linarith
  have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨le_rfl, hb_pos.le⟩
  have hzero_lt_r : 0 < r := by
    rcases hr with ⟨hr_pos, _, _, _⟩
    exact Nat.succ_le_iff.mp hr_pos
  have hlt_first :
      flow_cover_excess a b C < weight C a coverOrder 1 :=
    flowCoverExcess_lt_firstOrderedWeight a b C coverOrder r hordered hr
  have hzpiece :
      (0 : ℝ) ∈
        Set.Ico
          (partialSum C a coverOrder 0)
          (partialSum C a coverOrder (0 + 1) - flow_cover_excess a b C) := by
    constructor
    · -- The origin is the left endpoint of the first cover interval.
      simp [partialSum]
    · -- The first cover interval is nontrivial because the first ordered weight exceeds `λ`.
      have hlt_partial :
          flow_cover_excess a b C < partialSum C a coverOrder 1 := by
        simpa [partialSum_succ, partialSum] using hlt_first
      linarith
  have hzeroEval :=
    flow_cover_lifting_function_eq_constant_on_cover_intervals
      a
      b
      C
      coverOrder
      r
      0
      ha_nonneg
      hC
      hcoverOrder
      hordered
      hr
      hz
      hzero_lt_r
      hzpiece
  -- The origin belongs to the first constant piece, so Lemma 7.13 returns the zero value.
  simpa using hzeroEval

/-- Helper for Theorem 7.16: the common lifting function satisfies the nonnegativity hypothesis at
the origin required by Lemma 7.12. -/
theorem flowCoverLiftingFunction_zero_nonneg
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    0 ≤
      flow_cover_lifting_function
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder)
        0 := by
  -- Reuse the normalized value at the origin instead of reopening the interval decomposition.
  simp [flowCoverLiftingFunction_zero a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr]

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: the ordered flow-cover lifting
profile is nonnegative throughout its feasible residual interval. -/
theorem flowCoverLiftingFunction_nonneg
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b) :
    0 ≤
      flow_cover_lifting_function
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder)
        z := by
  have hmono :=
    flowCoverLiftingFunction_mono
      b
      (flow_cover_excess a b C)
      (a ∘ coverOrder)
      (fun i ↦ ha_nonneg (coverOrder i))
      hz.1
      hz.2
  -- Monotonicity from the normalized origin gives the desired lower bound.
  rw [flowCoverLiftingFunction_zero a b C coverOrder r
    ha_nonneg hC hcoverOrder hordered hr] at hmono
  exact hmono

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: the ordered-cover lifting profile
is superadditive on the feasible residual interval. -/
theorem flowCoverLiftingFunction_superadditive
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder) :
    SequenceIndependentLifting.is_superadditive_on_Icc
      (flow_cover_lifting_function
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder))
      b := by
  have hsuper :=
    flow_cover_lifting_function_is_superadditive_on_Icc
      b
      (a ∘ coverOrder)
      (fun i ↦ ha_nonneg (coverOrder i))
      (isFlowCover_comp_coverOrder a b C coverOrder hC hcoverOrder)
  -- Normalize the reindexed excess in the profile supplied by Lemma 7.14.
  rw [flowCoverExcess_comp_coverOrder_eq a b C coverOrder hcoverOrder] at hsuper
  exact hsuper

/-- Helper for Theorem 7.16: every ordered cover coefficient before the cut index still exceeds
the excess parameter `λ`. -/
theorem flowCoverExcess_lt_coverWeight_of_lt_cutIndex
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h : ℕ} (hh : h < r) :
    flow_cover_excess a b C < weight C a coverOrder (h + 1) := by
  rcases hr with ⟨hr_pos, hr_le, hcut, _⟩
  have hh_card : h < C.card := lt_of_lt_of_le hh hr_le
  have hpred_lt_card : r - 1 < C.card := by
    exact lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hr_pos)) hr_le
  have hh_le_pred : h ≤ r - 1 := by
    omega
  have hweight_r :
      weight C a coverOrder r = a (coverOrder ⟨r - 1, hpred_lt_card⟩) := by
    -- Specialize `weight_succ` before rewriting the dependent index bound.
    have hweightPred := weight_succ C a coverOrder hpred_lt_card
    rw [Nat.sub_add_cancel hr_pos] at hweightPred
    exact hweightPred
  have hweight_h :
      weight C a coverOrder (h + 1) = a (coverOrder ⟨h, hh_card⟩) := by
    -- Rewrite the earlier position into the corresponding ordered coefficient.
    simpa using weight_succ C a coverOrder hh_card
  have hmono :
      a (coverOrder ⟨r - 1, hpred_lt_card⟩) ≤ a (coverOrder ⟨h, hh_card⟩) := by
    -- Antitonicity makes earlier ordered coefficients dominate the cut coefficient.
    exact hordered (show (⟨h, hh_card⟩ : Fin C.card) ≤ ⟨r - 1, hpred_lt_card⟩ from hh_le_pred)
  rw [hweight_h]
  exact lt_of_lt_of_le (by simpa [hweight_r] using hcut) hmono

/-- Helper for Theorem 7.16: at the cover breakpoint `μ_h`, the common lifting function takes the
source value `h λ`. -/
theorem flowCoverLiftingFunction_evalAtCoverBreakpoint
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h : ℕ} (hh : h < r)
    (hz : partialSum C a coverOrder h ∈ Set.Icc (0 : ℝ) b) :
    flow_cover_lifting_function
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder)
        (partialSum C a coverOrder h) =
      (h : ℝ) * flow_cover_excess a b C := by
  have hlt_weight :
      flow_cover_excess a b C < weight C a coverOrder (h + 1) :=
    flowCoverExcess_lt_coverWeight_of_lt_cutIndex a b C coverOrder r hordered hr hh
  have hzpiece :
      partialSum C a coverOrder h ∈
        Set.Ico
          (partialSum C a coverOrder h)
          (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C) := by
    constructor
    · -- The breakpoint is the left endpoint of the next constant interval.
      exact le_rfl
    · -- The next ordered cover weight still exceeds `λ`, so the interval is nontrivial.
      rw [partialSum_succ]
      linarith
  -- Apply the constant-piece formula exactly at the left endpoint `μ_h`.
  simpa using
    flow_cover_lifting_function_eq_constant_on_cover_intervals
      a
      b
      C
      coverOrder
      r
      (partialSum C a coverOrder h)
      ha_nonneg
      hC
      hcoverOrder
      hordered
      hr
      hz
      hh
      hzpiece

/-- Helper for Theorem 7.16: at the left endpoint `μ_h - λ` of a gap interval, the common
lifting function takes the source value `(h - 1) λ`. -/
theorem flowCoverLiftingFunction_evalAtGapLeftBreakpoint
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hlam_pos : 0 < flow_cover_excess a b C)
    {h : ℕ} (hh₁ : 1 ≤ h) (hh₂ : h < r)
    (hz : partialSum C a coverOrder h - flow_cover_excess a b C ∈ Set.Icc (0 : ℝ) b) :
    flow_cover_lifting_function
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder)
        (partialSum C a coverOrder h - flow_cover_excess a b C) =
      ((h : ℝ) - 1) * flow_cover_excess a b C := by
  have hzpiece :
      partialSum C a coverOrder h - flow_cover_excess a b C ∈
        Set.Ico
          (partialSum C a coverOrder h - flow_cover_excess a b C)
          (partialSum C a coverOrder h) := by
    constructor
    · -- The left breakpoint belongs to the corresponding gap interval.
      exact le_rfl
    · -- Positive excess makes the gap interval nontrivial.
      linarith
  have hEval :=
    flow_cover_lifting_function_eq_affine_on_gap_intervals
      a
      b
      C
      coverOrder
      r
      (partialSum C a coverOrder h - flow_cover_excess a b C)
      ha_nonneg
      hC
      hcoverOrder
      hordered
      hr
      hz
      hh₁
      hh₂
      hzpiece
  -- Evaluate the affine formula at the left endpoint of the gap.
  calc
    flow_cover_lifting_function
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder)
        (partialSum C a coverOrder h - flow_cover_excess a b C)
      = (partialSum C a coverOrder h - flow_cover_excess a b C) -
          partialSum C a coverOrder h +
          (h : ℝ) * flow_cover_excess a b C := by
            exact hEval
    _ = ((h : ℝ) - 1) * flow_cover_excess a b C := by
          ring

/-- Helper for Theorem 7.16: at the final breakpoint `μ_r - λ`, the common lifting function takes
the source value `(r - 1) λ`. -/
theorem flowCoverLiftingFunction_evalAtFinalBreakpoint
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hz : partialSum C a coverOrder r - flow_cover_excess a b C ∈ Set.Icc (0 : ℝ) b) :
    flow_cover_lifting_function
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder)
        (partialSum C a coverOrder r - flow_cover_excess a b C) =
      ((r : ℝ) - 1) * flow_cover_excess a b C := by
  have hzpiece :
      partialSum C a coverOrder r - flow_cover_excess a b C ∈
        Set.Icc
          (partialSum C a coverOrder r - flow_cover_excess a b C)
          b := by
    -- The final breakpoint is the left endpoint of the terminal affine interval.
    exact ⟨le_rfl, hz.2⟩
  have hEval :=
    flow_cover_lifting_function_eq_affine_on_final_interval
      a
      b
      C
      coverOrder
      r
      (partialSum C a coverOrder r - flow_cover_excess a b C)
      ha_nonneg
      hC
      hcoverOrder
      hordered
      hr
      hz
      hzpiece
  -- Evaluate the final affine formula at its left endpoint.
  calc
    flow_cover_lifting_function
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder)
        (partialSum C a coverOrder r - flow_cover_excess a b C)
      = (partialSum C a coverOrder r - flow_cover_excess a b C) -
          partialSum C a coverOrder r +
          (r : ℝ) * flow_cover_excess a b C := by
            exact hEval
    _ = ((r : ℝ) - 1) * flow_cover_excess a b C := by
          ring

/-- Helper for Theorem 7.16: the source one-index criterion requires the affine line
`u ↦ αᵢ u + βᵢ` to lie below the common lifting function on `[0, a i]` and to meet it at two
distinct points of that interval. -/
def outsideStepCriterion
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (i : Fin n)
    (αᵢ βᵢ : ℝ) : Prop :=
  let f := flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder)
  (∀ y ∈ Set.Icc (0 : ℝ) (a i), αᵢ * y + βᵢ ≤ f y) ∧
    ∃ y' ∈ Set.Icc (0 : ℝ) (a i),
      ∃ y'' ∈ Set.Icc (0 : ℝ) (a i),
        y' ≠ y'' ∧
          αᵢ * y' + βᵢ = f y' ∧
            αᵢ * y'' + βᵢ = f y''

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: capped one-step lifting
criterion
records validity and two distinct contacts on the effective flow interval `[0, min aᵢ b]`. -/
def cappedOneStepCriterion
    (b aᵢ : ℝ) (f : ℝ → ℝ) (αᵢ βᵢ : ℝ) : Prop :=
  (∀ y ∈ Set.Icc (0 : ℝ) (min aᵢ b), αᵢ * y + βᵢ ≤ f y) ∧
    ∃ y' ∈ Set.Icc (0 : ℝ) (min aᵢ b),
      ∃ y'' ∈ Set.Icc (0 : ℝ) (min aᵢ b),
        y' ≠ y'' ∧
          αᵢ * y' + βᵢ = f y' ∧
            αᵢ * y'' + βᵢ = f y''

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: capped interval validity is
equivalent to validity on the one-step flow set with the effective capacity `min aᵢ b`. -/
theorem cappedOneStepCriterion_iff_oneStepData
    (b aᵢ : ℝ) (f : ℝ → ℝ) (αᵢ βᵢ : ℝ)
    (hf_zero_nonneg : 0 ≤ f 0) :
    cappedOneStepCriterion b aᵢ f αᵢ βᵢ ↔
      one_step_lifting_valid (min aᵢ b) f αᵢ βᵢ ∧
        ∃ y' y'',
          y' ≠ y'' ∧
            one_step_lifting_tight_point (min aᵢ b) f αᵢ βᵢ y' ∧
              one_step_lifting_tight_point (min aᵢ b) f αᵢ βᵢ y'' := by
  constructor
  · intro hdata
    -- Translate the interval half and the two contact witnesses through Lemma 7.12.
    rcases hdata with ⟨hvalid, htight⟩
    refine ⟨(lemma_7_12_valid_iff_interval_condition hf_zero_nonneg).2 hvalid, ?_⟩
    exact lemma_7_12_two_distinct_tight_points_iff.mpr htight
  · rintro ⟨hvalid, htight⟩
    -- Recover the capped interval formulation from the canonical one-step predicates.
    refine ⟨(lemma_7_12_valid_iff_interval_condition hf_zero_nonneg).1 hvalid, ?_⟩
    exact lemma_7_12_two_distinct_tight_points_iff.mp htight

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: agreement with a superadditive
reference function is preserved by a one-step update whose affine cost is valid on the effective
interval `[0, min aᵢ b]`. -/
theorem flowCoverRecursiveLiftingStep_eq_of_cappedValid
    {b aᵢ : ℝ} {f g : ℝ → ℝ} {αᵢ βᵢ z : ℝ}
    (hsuper : SequenceIndependentLifting.is_superadditive_on_Icc f b)
    (heq : Set.EqOn g f (Set.Icc (0 : ℝ) b))
    (hvalid : ∀ y ∈ Set.Icc (0 : ℝ) (min aᵢ b), αᵢ * y + βᵢ ≤ g y)
    (hz : z ∈ Set.Icc (0 : ℝ) b) :
    flow_cover_recursive_lifting_step b aᵢ g αᵢ βᵢ z = f z := by
  have hlower :
      ∀ v ∈ flow_cover_recursive_lifting_step_values b aᵢ g αᵢ βᵢ z, f z ≤ v := by
    intro v hv
    rcases mem_flow_cover_recursive_lifting_step_values_iff.mp hv with
      ⟨p, hp, hz_add, rfl⟩
    rcases mem_one_step_flow_set_iff.mp hp with ⟨hx, hy_nonneg, hy_capacity⟩
    rcases hx with hx | hx
    · have hy_zero : p.2 0 = 0 := by
        apply le_antisymm
        · simpa [hx] using hy_capacity
        · exact hy_nonneg
      -- On the zero selector branch the candidate is exactly the current profile value.
      simp [hx, hy_zero, (heq hz).symm]
    · have hy_le_capacity : p.2 0 ≤ aᵢ := by
        simpa [hx] using hy_capacity
      have hy_le_rhs : p.2 0 ≤ b := by
        linarith [hz.1, hz_add.2]
      have hy : p.2 0 ∈ Set.Icc (0 : ℝ) (min aᵢ b) :=
        ⟨hy_nonneg, le_min hy_le_capacity hy_le_rhs⟩
      have hseparate : f z ≤ f (z + p.2 0) - f (p.2 0) := by
        linarith [hsuper hz ⟨hy_nonneg, hy_le_rhs⟩ hz_add]
      -- Agreement transports both profile values, and capped validity removes the affine cost.
      calc
        f z ≤ f (z + p.2 0) - f (p.2 0) := hseparate
        _ = g (z + p.2 0) - g (p.2 0) := by rw [heq hz_add, heq ⟨hy_nonneg, hy_le_rhs⟩]
        _ ≤ g (z + p.2 0) - (αᵢ * p.2 0 + βᵢ * p.1 0) := by
          rw [hx]
          simpa using sub_le_sub_left (hvalid (p.2 0) hy) (g (z + p.2 0))
  have hbdd : BddBelow (flow_cover_recursive_lifting_step_values b aᵢ g αᵢ βᵢ z) :=
    ⟨f z, hlower⟩
  have hf_mem : f z ∈ flow_cover_recursive_lifting_step_values b aᵢ g αᵢ βᵢ z := by
    refine mem_flow_cover_recursive_lifting_step_values_iff.mpr ?_
    refine ⟨((fun _ : Fin 1 ↦ (0 : ℝ)), fun _ : Fin 1 ↦ (0 : ℝ)),
      zero_mem_one_step_flow_set aᵢ, ?_, ?_⟩
    · simpa using hz
    · simpa using (heq hz).symm
  have hnonempty :
      (flow_cover_recursive_lifting_step_values b aᵢ g αᵢ βᵢ z).Nonempty :=
    ⟨f z, hf_mem⟩
  -- The zero candidate attains the lower bound established for every feasible candidate.
  rw [flow_cover_recursive_lifting_step_eq]
  exact le_antisymm (csInf_le hbdd hf_mem) (le_csInf hnonempty hlower)

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: capped one-step validity
preserves agreement of every bounded recursive stage with a superadditive reference profile. -/
theorem flowCoverRecursiveLiftingFunction_eq_of_cappedValid
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ)
    (hsuper :
      SequenceIndependentLifting.is_superadditive_on_Icc
        (flow_cover_lifting_function
          b
          (flow_cover_excess coverCapacity b Finset.univ)
          coverCapacity)
        b)
    (hvalid :
      ∀ i : Fin m,
        cappedOneStepCriterion
          b
          (liftCapacity i)
          (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β i)
          (α i)
          (β i))
    {k : ℕ} (hk : k ≤ m) :
    Set.EqOn
      (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β k)
      (flow_cover_lifting_function
        b
        (flow_cover_excess coverCapacity b Finset.univ)
        coverCapacity)
      (Set.Icc (0 : ℝ) b) := by
  induction k with
  | zero =>
      -- The recursive family starts at the canonical lifting profile.
      intro z hz
      simp only [flow_cover_recursive_lifting_function_zero]
  | succ k ih =>
      have hklt : k < m := Nat.lt_of_succ_le hk
      have hk_le : k ≤ m := Nat.le_of_lt hklt
      intro z hz
      rw [flow_cover_recursive_lifting_function_succ b coverCapacity liftCapacity α β hklt]
      -- The capped step lemma closes the successor using the induction hypothesis on `[0,b]`.
      exact
        flowCoverRecursiveLiftingStep_eq_of_cappedValid
          hsuper (ih hk_le) (hvalid ⟨k, hklt⟩).1 hz

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: the zero affine pair has two
distinct contacts with the ordered lifting profile on every positive effective interval. -/
theorem cappedOneStepCriterion_zero
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (i : Fin n)
    (hi_pos : 0 < a i) :
    cappedOneStepCriterion
      b
      (a i)
      (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
      0
      0 := by
  have hb_pos : 0 < b := by
    have hlt_sum : flow_cover_excess a b C < ∑ j ∈ C, a j :=
      flowCoverExcess_lt_coverSum a b C coverOrder r ha_nonneg hcoverOrder hordered hr
    rw [flow_cover_excess_eq_sum_sub] at hlt_sum
    linarith
  have hcap_pos : 0 < min (a i) b := lt_min hi_pos hb_pos
  have hlt_first :
      flow_cover_excess a b C < weight C a coverOrder 1 :=
    flowCoverExcess_lt_firstOrderedWeight a b C coverOrder r hordered hr
  have hpartial_first :
      partialSum C a coverOrder 1 = weight C a coverOrder 1 := by
    simp [partialSum]
  have hgap_pos :
      0 < partialSum C a coverOrder 1 - flow_cover_excess a b C := by
    linarith
  let y :=
    min
      (min (a i) b)
      (partialSum C a coverOrder 1 - flow_cover_excess a b C) / 2
  have hy_pos : 0 < y := by
    dsimp [y]
    have hmin_pos :
        0 < min
          (min (a i) b)
          (partialSum C a coverOrder 1 - flow_cover_excess a b C) :=
      lt_min hcap_pos hgap_pos
    linarith
  have hy_cap : y ≤ min (a i) b := by
    dsimp [y]
    have hmin_le :
        min
            (min (a i) b)
            (partialSum C a coverOrder 1 - flow_cover_excess a b C) ≤
          min (a i) b :=
      min_le_left _ _
    linarith [hmin_le, hcap_pos.le]
  have hy_gap :
      y < partialSum C a coverOrder 1 - flow_cover_excess a b C := by
    dsimp [y]
    have hmin_le :
        min
            (min (a i) b)
            (partialSum C a coverOrder 1 - flow_cover_excess a b C) ≤
          partialSum C a coverOrder 1 - flow_cover_excess a b C :=
      min_le_right _ _
    linarith
  have hyIcc : y ∈ Set.Icc (0 : ℝ) b :=
    ⟨hy_pos.le, hy_cap.trans (min_le_right _ _)⟩
  have hr_pos : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_one hr.1
  have hyPiece :
      y ∈
        Set.Ico
          (partialSum C a coverOrder 0)
          (partialSum C a coverOrder (0 + 1) - flow_cover_excess a b C) := by
    simpa [partialSum] using And.intro hy_pos.le hy_gap
  have hyEval :
      flow_cover_lifting_function
          b
          (flow_cover_excess a b C)
          (a ∘ coverOrder)
          y = 0 := by
    simpa using
      flow_cover_lifting_function_eq_constant_on_cover_intervals
        a
        b
        C
        coverOrder
        r
        y
        ha_nonneg
        hC
        hcoverOrder
        hordered
        hr
        hyIcc
        hr_pos
        hyPiece
  refine ⟨?_, 0, ?_, y, ?_, ?_, ?_, ?_⟩
  · intro z hz
    -- Nonnegativity of the profile proves validity of the zero affine minorant.
    simpa using
      flowCoverLiftingFunction_nonneg
        a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
        ⟨hz.1, hz.2.trans (min_le_right _ _)⟩
  · exact ⟨le_rfl, hcap_pos.le⟩
  · exact ⟨hy_pos.le, hy_cap⟩
  · exact ne_of_lt hy_pos
  · simpa using
      (flowCoverLiftingFunction_zero a b C coverOrder r
        ha_nonneg hC hcoverOrder hordered hr).symm
  · simpa using hyEval.symm

/-- Helper for Theorem 7.16: the source interval-and-two-tight-points criterion is exactly the
Lemma 7.12 one-step validity data for the common lifting function. -/
theorem outsideStepCriterion_iff_oneStepData
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (i : Fin n)
    (αᵢ βᵢ : ℝ)
    (hf_zero_nonneg :
      0 ≤
        flow_cover_lifting_function
          b
          (flow_cover_excess a b C)
          (a ∘ coverOrder)
          0) :
    outsideStepCriterion a b C coverOrder i αᵢ βᵢ ↔
      one_step_lifting_valid
        (a i)
        (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
        αᵢ
        βᵢ ∧
      ∃ y' y'',
        y' ≠ y'' ∧
          one_step_lifting_tight_point
            (a i)
            (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
            αᵢ
            βᵢ
            y' ∧
          one_step_lifting_tight_point
            (a i)
            (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
            αᵢ
            βᵢ
            y'' := by
  let f := flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder)
  constructor
  · intro hcriterion
    -- Rewrite the source interval criterion through Lemma 7.12's one-step validity API.
    dsimp [outsideStepCriterion, f] at hcriterion
    rcases hcriterion with ⟨hinterval, htight⟩
    refine ⟨?_, ?_⟩
    · rw [lemma_7_12_valid_iff_interval_condition hf_zero_nonneg]
      · simpa [f] using hinterval
    · rw [lemma_7_12_two_distinct_tight_points_iff]
      simpa [f] using htight
  · rintro ⟨hvalid, htight⟩
    -- Convert the Lemma 7.12 data back to the source-facing interval-and-two-points language.
    dsimp [outsideStepCriterion, f]
    refine ⟨?_, ?_⟩
    · rw [← lemma_7_12_valid_iff_interval_condition hf_zero_nonneg]
      · simpa [f] using hvalid
    · rw [lemma_7_12_two_distinct_tight_points_iff] at htight
      simpa [f] using htight

/-- Helper for Theorem 7.16: under the cut-index hypotheses, the source interval-and-two-points
criterion is exactly the Lemma 7.12 one-step validity data. -/
theorem outsideStepCriterion_iff_oneStepData_of_isCutIndex
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (i : Fin n)
    (αᵢ βᵢ : ℝ) :
    outsideStepCriterion a b C coverOrder i αᵢ βᵢ ↔
      one_step_lifting_valid
        (a i)
        (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
        αᵢ
        βᵢ ∧
      ∃ y' y'',
        y' ≠ y'' ∧
          one_step_lifting_tight_point
            (a i)
            (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
            αᵢ
            βᵢ
            y' ∧
          one_step_lifting_tight_point
            (a i)
            (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
            αᵢ
            βᵢ
            y'' := by
  -- Reuse the zero-value normalization to discharge the Lemma 7.12 side condition once.
  exact
    outsideStepCriterion_iff_oneStepData
      a
      b
      C
      coverOrder
      i
      αᵢ
      βᵢ
      (flowCoverLiftingFunction_zero_nonneg
        a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr)

/-- Helper for Theorem 7.16: zero lifting coefficients cut out exactly the zero-lifted flow-cover
face from Theorem 7.9. -/
theorem flow_cover_lifted_face_zero
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n)) :
    flow_cover_lifted_face a b C (fun _ ↦ 0) (fun _ ↦ 0) b =
      flow_cover_face a b C := by
  -- Extensionality reduces the face equality to the already-normalized value equality.
  ext p
  rw [mem_flow_cover_lifted_face_iff, mem_flow_cover_face_iff, flow_cover_lifted_value_zero]

/-- Helper for Theorem 7.16: the lifted facet owner specializes to the zero-lifted owner when all
outside lifting coefficients vanish. -/
theorem flow_cover_lifted_inequality_facet_defining_zero_iff
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n)) :
    flow_cover_lifted_inequality_facet_defining a b C (fun _ ↦ 0) (fun _ ↦ 0) b ↔
      flow_cover_inequality_facet_defining a b C := by
  constructor
  · intro hfacet
    -- Unfold both owners and rewrite the lifted pieces to the zero-lifted ones.
    rw [flow_cover_lifted_inequality_facet_defining_iff] at hfacet
    rw [flow_cover_inequality_facet_defining_iff]
    constructor
    · intro p hp
      have hpValid := hfacet.1 hp
      simpa [flow_cover_lifted_value_zero] using hpValid
    · simpa [flow_cover_lifted_face_zero] using hfacet.2
  · intro hfacet
    -- The converse direction is the same normalization in reverse.
    rw [flow_cover_lifted_inequality_facet_defining_iff]
    rw [flow_cover_inequality_facet_defining_iff] at hfacet
    constructor
    · intro p hp
      have hpValid := hfacet.1 hp
      simpa [flow_cover_lifted_value_zero] using hpValid
    · simpa [flow_cover_lifted_face_zero] using hfacet.2

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: every feasible residual lies
in a pre-cut affine gap, the following constant interval, or the final affine interval. -/
theorem orderedFlowCoverIntervalPartition
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b) :
    z ∈ Set.Icc
        (partialSum C a coverOrder r - flow_cover_excess a b C)
        b ∨
      ∃ h, h < r ∧
        (z ∈ Set.Ico
            (partialSum C a coverOrder h - flow_cover_excess a b C)
            (partialSum C a coverOrder h) ∨
          z ∈ Set.Ico
            (partialSum C a coverOrder h)
            (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C)) := by
  have hprofile :=
    flowCoverLiftingFunction_stageProfile
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hz
  rcases hprofile with hfinal | ⟨h, hh, hlower, hupper, -⟩
  · -- The terminal profile branch already records both endpoints of the final interval.
    exact Or.inl ⟨hfinal.1, hz.2⟩
  · refine Or.inr ⟨h, hh, ?_⟩
    by_cases hz_mu : z < partialSum C a coverOrder h
    · -- Before `μ h` the point lies in the affine gap.
      exact Or.inl ⟨hlower, hz_mu⟩
    · -- At or after `μ h` it lies in the following constant interval.
      exact Or.inr ⟨le_of_not_gt hz_mu, hupper⟩

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: capped one-step data only
depends on the lifting profile over the feasible residual interval. -/
theorem cappedOneStepCriterion_congr
    {b aᵢ : ℝ} {f g : ℝ → ℝ} {αᵢ βᵢ : ℝ}
    (hfg : Set.EqOn f g (Set.Icc (0 : ℝ) b)) :
    cappedOneStepCriterion b aᵢ f αᵢ βᵢ ↔
      cappedOneStepCriterion b aᵢ g αᵢ βᵢ := by
  constructor
  · rintro ⟨hvalid, y', hy', y'', hy'', hne, hy'Eq, hy''Eq⟩
    refine ⟨?_, y', hy', y'', hy'', hne, ?_, ?_⟩
    · intro y hy
      -- Every capped point lies in `[0,b]`, where the two profiles agree.
      rw [← hfg ⟨hy.1, hy.2.trans (min_le_right _ _)⟩]
      exact hvalid y hy
    · rw [← hfg ⟨hy'.1, hy'.2.trans (min_le_right _ _)⟩]
      exact hy'Eq
    · rw [← hfg ⟨hy''.1, hy''.2.trans (min_le_right _ _)⟩]
      exact hy''Eq
  · rintro ⟨hvalid, y', hy', y'', hy'', hne, hy'Eq, hy''Eq⟩
    refine ⟨?_, y', hy', y'', hy'', hne, ?_, ?_⟩
    · intro y hy
      -- Rewrite in the reverse direction on the same effective interval.
      rw [hfg ⟨hy.1, hy.2.trans (min_le_right _ _)⟩]
      exact hvalid y hy
    · rw [hfg ⟨hy'.1, hy'.2.trans (min_le_right _ _)⟩]
      exact hy'Eq
    · rw [hfg ⟨hy''.1, hy''.2.trans (min_le_right _ _)⟩]
      exact hy''Eq

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: when `a i ≤ b`, the capped
criterion is definitionally the source interval-and-two-contact criterion. -/
theorem cappedOneStepCriterion_iff_outsideStepCriterion_of_le
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (i : Fin n)
    (αᵢ βᵢ : ℝ)
    (hi_le_b : a i ≤ b) :
    cappedOneStepCriterion
        b
        (a i)
        (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
        αᵢ
        βᵢ ↔
      outsideStepCriterion a b C coverOrder i αᵢ βᵢ := by
  -- The capacity hypothesis removes the only difference between the two interval owners.
  simp only [cappedOneStepCriterion, outsideStepCriterion, min_eq_left hi_le_b]

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: capped validity against one
common superadditive profile keeps every sequential recursive stage equal to that profile. -/
theorem flowCoverRecursiveLiftingFunction_eq_of_commonCappedValid
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ)
    (hsuper :
      SequenceIndependentLifting.is_superadditive_on_Icc
        (flow_cover_lifting_function
          b
          (flow_cover_excess coverCapacity b Finset.univ)
          coverCapacity)
        b)
    (hcommon :
      ∀ i : Fin m,
        cappedOneStepCriterion
          b
          (liftCapacity i)
          (flow_cover_lifting_function
            b
            (flow_cover_excess coverCapacity b Finset.univ)
            coverCapacity)
          (α i)
          (β i))
    {k : ℕ} (hk : k ≤ m) :
    Set.EqOn
      (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β k)
      (flow_cover_lifting_function
        b
        (flow_cover_excess coverCapacity b Finset.univ)
        coverCapacity)
      (Set.Icc (0 : ℝ) b) := by
  induction k with
  | zero =>
      -- The recursive construction starts at the common profile.
      intro z hz
      simp only [flow_cover_recursive_lifting_function_zero]
  | succ k ih =>
      have hklt : k < m := Nat.lt_of_succ_le hk
      have hk_le : k ≤ m := Nat.le_of_lt hklt
      have heq := ih hk_le
      have hstage :
          cappedOneStepCriterion
            b
            (liftCapacity ⟨k, hklt⟩)
            (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β k)
            (α ⟨k, hklt⟩)
            (β ⟨k, hklt⟩) := by
        -- Transport the common criterion to the current recursive profile.
        exact (cappedOneStepCriterion_congr heq).mpr (hcommon ⟨k, hklt⟩)
      intro z hz
      rw [flow_cover_recursive_lifting_function_succ b coverCapacity liftCapacity α β hklt]
      -- Capped validity and superadditivity identify the next recursive update pointwise.
      exact flowCoverRecursiveLiftingStep_eq_of_cappedValid hsuper heq hstage.1 hz

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: the lifted flow-cover value
preserves affine combinations. -/
theorem flowCoverLiftedValue_affineCombination
    (a α β : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p q : (Fin n → ℝ) × (Fin n → ℝ))
    (u v : ℝ) (huv : u + v = 1) :
    flow_cover_lifted_value a b C α β (u • p + v • q) =
      u * flow_cover_lifted_value a b C α β p +
        v * flow_cover_lifted_value a b C α β q := by
  classical
  have hcoverFlow :
      (∑ j ∈ C, (u • p + v • q).2 j) =
        u * (∑ j ∈ C, p.2 j) + v * (∑ j ∈ C, q.2 j) := by
    simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hcoverPenalty :
      (∑ j ∈ C,
          max (a j - flow_cover_excess a b C) 0 * (1 - (u • p + v • q).1 j)) =
        u * (∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j)) +
          v * (∑ j ∈ C, max (a j - flow_cover_excess a b C) 0 * (1 - q.1 j)) := by
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    linear_combination -(max (a i - flow_cover_excess a b C) 0) * huv
  have houtside :
      (Finset.univ \ C).sum
          (fun i ↦ α i * (u • p + v • q).2 i + β i * (u • p + v • q).1 i) =
        u * (Finset.univ \ C).sum (fun i ↦ α i * p.2 i + β i * p.1 i) +
          v * (Finset.univ \ C).sum (fun i ↦ α i * q.2 i + β i * q.1 i) := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  -- The three affine pieces now recombine into the two endpoint values.
  simp only [flow_cover_lifted_value, flow_cover_value]
  rw [hcoverFlow, hcoverPenalty, houtside]
  ring

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: a lifted flow-cover
sublevel set is convex. -/
theorem convex_flowCoverLiftedValue_sublevel
    (a α β : Fin n → ℝ) (b δ : ℝ) (C : Finset (Fin n)) :
    Convex ℝ {p | flow_cover_lifted_value a b C α β p ≤ δ} := by
  intro p hp q hq u v hu hv huv
  -- Affinity reduces the sublevel calculation to a convex combination of two scalar bounds.
  change flow_cover_lifted_value a b C α β p ≤ δ at hp
  change flow_cover_lifted_value a b C α β q ≤ δ at hq
  change flow_cover_lifted_value a b C α β (u • p + v • q) ≤ δ
  rw [flowCoverLiftedValue_affineCombination a α β b C p q u v huv]
  calc
    u * flow_cover_lifted_value a b C α β p +
          v * flow_cover_lifted_value a b C α β q ≤
        u * δ + v * δ :=
      add_le_add (mul_le_mul_of_nonneg_left hp hu) (mul_le_mul_of_nonneg_left hq hv)
    _ = δ := by rw [← add_mul, huv, one_mul]

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: summation along an enumerating
order is summation over the cover. -/
theorem sum_comp_coverOrder_eq
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (hcoverOrder : enumerates C coverOrder)
    (g : Fin n → ℝ) :
    ∑ i : Fin C.card, g (coverOrder i) = ∑ j ∈ C, g j := by
  classical
  have himage : Finset.univ.map coverOrder = C := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, -, rfl⟩
      exact coverOrder_mem_cover C coverOrder hcoverOrder i
    · intro hj
      have hjSet : j ∈ (↑C : Set (Fin n)) := by simpa using hj
      rw [← hcoverOrder] at hjSet
      rcases hjSet with ⟨i, rfl⟩
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  calc
    ∑ i : Fin C.card, g (coverOrder i) =
        ∑ j ∈ Finset.univ.map coverOrder, g j := by rw [Finset.sum_map]
    _ = ∑ j ∈ C, g j := by rw [himage]

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: the cover part of every feasible
single-node point is a feasible value in the residual lifting optimization problem. -/
theorem flowCoverValue_mem_objectiveValues_of_mem_singleNodeFlowSet
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (hcoverOrder : enumerates C coverOrder)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ single_node_flow_set a b) :
    flow_cover_value a b C p ∈
      flow_cover_lifting_objective_values
        b
        (flow_cover_excess a b C)
        (a ∘ coverOrder)
        ((Finset.univ \ C).sum p.2) := by
  classical
  rcases (mem_single_node_flow_set_iff a b p).mp hp with
    ⟨hx_binary, hy_nonneg, hy_sum, hy_capacity⟩
  let x : Fin C.card → Bool := fun i ↦ decide (p.1 (coverOrder i) = 1)
  let y : Fin C.card → ℝ := fun i ↦ p.2 (coverOrder i)
  have hx_real (i : Fin C.card) :
      (if x i then (1 : ℝ) else 0) = p.1 (coverOrder i) := by
    rcases hx_binary (coverOrder i) with hzero | hone
    · simp [x, hzero]
    · simp [x, hone]
  have hcover_sum :
      ∑ i : Fin C.card, y i = ∑ j ∈ C, p.2 j := by
    simpa [y] using sum_comp_coverOrder_eq C coverOrder hcoverOrder p.2
  have hsum_split :
      (Finset.univ \ C).sum p.2 + C.sum p.2 = Finset.univ.sum p.2 := by
    exact Finset.sum_sdiff (Finset.subset_univ C) (f := p.2)
  refine (mem_flow_cover_lifting_objective_values_iff
    b (flow_cover_excess a b C) (a ∘ coverOrder)
    ((Finset.univ \ C).sum p.2) (flow_cover_value a b C p)).2 ?_
  refine ⟨x, y, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hy_nonneg (coverOrder i)
  · rw [hcover_sum]
    have hall_sum : Finset.univ.sum p.2 = ∑ j : Fin n, p.2 j := by rfl
    rw [hall_sum] at hsum_split
    linarith
  · intro i
    rw [hx_real]
    exact hy_capacity (coverOrder i)
  · rw [flow_cover_value_eq, ← hcover_sum]
    rw [Finset.sum_add_distrib]
    apply congrArg₂ (· + ·)
    · rfl
    · rw [← sum_comp_coverOrder_eq C coverOrder hcoverOrder]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hx_real]
      rfl

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: every feasible residual has an
ordered-cover optimizer attaining the complementary value of the lifting profile. -/
theorem flowCoverLiftingFunction_complement_mem_objectiveValues
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b) :
    b - flow_cover_lifting_function
          b (flow_cover_excess a b C) (a ∘ coverOrder) z ∈
      flow_cover_lifting_objective_values
        b (flow_cover_excess a b C) (a ∘ coverOrder) z := by
  have hdemand_nonneg : 0 ≤ b - z := by
    linarith [hz.2]
  rcases orderedFlowCoverIntervalPartition
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hz with
    hfinal | ⟨h, hh, hgap | hconstant⟩
  · have hvalue :=
      flow_cover_lifting_function_eq_affine_on_final_interval
        a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz hfinal
    have hcard :
        partialSum C a coverOrder C.card = b + flow_cover_excess a b C := by
      simpa using
        partialSum_card_eq_rhs_add_excess
          (a := a) (b := b) (C := C) (coverOrder := coverOrder) hcoverOrder
    have htail :
        b - z ≤ partialSum C a coverOrder C.card - partialSum C a coverOrder r := by
      rw [hcard]
      linarith [hfinal.1]
    have hobjective :=
      thresholdSelector_objective_eq
        (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r) (z := z)
        hordered hr le_rfl
    rw [min_eq_left htail] at hobjective
    have hmem :=
      selectorObjective_mem
        (lam := flow_cover_excess a b C)
        (fun i ↦ ha_nonneg (coverOrder i)) hdemand_nonneg
        (thresholdSelector (t := C.card) r)
    -- The terminal optimizer and the terminal profile formula are complementary around `b`.
    change
      selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z
          (thresholdSelector r) ∈
        flow_cover_lifting_objective_values
          b (flow_cover_excess a b C) (a ∘ coverOrder) z at hmem
    rw [hobjective] at hmem
    convert hmem using 1
    rw [hvalue]
    ring
  · have hh_pos : 1 ≤ h := by
      by_contra hnot
      have hzero : h = 0 := by omega
      subst h
      simp [partialSum] at hgap
      linarith [hz.1]
    have hvalue :=
      flow_cover_lifting_function_eq_affine_on_gap_intervals
        a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz
        hh_pos hh hgap
    have hobjective :=
      gapInterval_thresholdSelector_objective_eq
        (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r) (z := z)
        hcoverOrder hordered hr hh hgap
    have hmem :=
      selectorObjective_mem
        (lam := flow_cover_excess a b C)
        (fun i ↦ ha_nonneg (coverOrder i)) hdemand_nonneg
        (thresholdSelector (t := C.card) h)
    -- The gap optimizer realizes `b` minus the affine-piece value.
    change
      selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z
          (thresholdSelector h) ∈
        flow_cover_lifting_objective_values
          b (flow_cover_excess a b C) (a ∘ coverOrder) z at hmem
    rw [hobjective] at hmem
    convert hmem using 1
    rw [hvalue]
    ring
  · have hvalue :=
      flow_cover_lifting_function_eq_constant_on_cover_intervals
        a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz hh hconstant
    have hobjective :=
      constantInterval_thresholdSelector_objective_eq
        (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r) (z := z)
        hcoverOrder hordered hr hh hconstant
    have hmem :=
      selectorObjective_mem
        (lam := flow_cover_excess a b C)
        (fun i ↦ ha_nonneg (coverOrder i)) hdemand_nonneg
        (thresholdSelector (t := C.card) (h + 1))
    -- The constant-piece optimizer realizes `b` minus the plateau value.
    change
      selectorObjective b (flow_cover_excess a b C) (a ∘ coverOrder) z
          (thresholdSelector (h + 1)) ∈
        flow_cover_lifting_objective_values
          b (flow_cover_excess a b C) (a ∘ coverOrder) z at hmem
    rw [hobjective] at hmem
    simpa [hvalue] using hmem

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: an attained ordered-cover
objective extends by one outside flow coordinate to a feasible single-node point. -/
theorem flowCoverObjective_extensionPoint
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (hcoverOrder : enumerates C coverOrder)
    (hCnonempty : C.Nonempty)
    (i : Fin n)
    (hiC : i ∉ C)
    {z v : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) (min (a i) b))
    (hv : v ∈
      flow_cover_lifting_objective_values
        b (flow_cover_excess a b C) (a ∘ coverOrder) z) :
    ∃ p : (Fin n → ℝ) × (Fin n → ℝ),
      p ∈ single_node_flow_set a b ∧
        p.1 i = 1 ∧
          p.2 i = z ∧
            flow_cover_value a b C p = v ∧
              ∀ j, j ∉ C → j ≠ i → p.1 j = 0 ∧ p.2 j = 0 := by
  classical
  rcases (mem_flow_cover_lifting_objective_values_iff
    b (flow_cover_excess a b C) (a ∘ coverOrder) z v).mp hv with
    ⟨xCover, yCover, hy_nonneg, hy_sum, hy_capacity, hv_eq⟩
  -- Local instance justification (explicit inverse): `Function.invFun coverOrder` needs a
  -- default ordered-cover index, supplied canonically by the assumed nonempty cover.
  letI : Nonempty (Fin C.card) :=
    Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hCnonempty)
  let x : Fin n → ℝ := fun j ↦
    if hj : j ∈ C then
      if xCover (Function.invFun coverOrder j) then 1 else 0
    else if j = i then 1 else 0
  let y : Fin n → ℝ := fun j ↦
    if hj : j ∈ C then yCover (Function.invFun coverOrder j)
    else if j = i then z else 0
  let p : (Fin n → ℝ) × (Fin n → ℝ) := (x, y)
  have hinv (k : Fin C.card) :
      Function.invFun coverOrder (coverOrder k) = k :=
    Function.leftInverse_invFun coverOrder.injective k
  have hcoverY : C.sum y = ∑ k : Fin C.card, yCover k := by
    rw [← sum_comp_coverOrder_eq C coverOrder hcoverOrder y]
    apply Finset.sum_congr rfl
    intro k hk
    simp [y, coverOrder_mem_cover C coverOrder hcoverOrder k, hinv]
  have houtsideY : (Finset.univ \ C).sum y = z := by
    have hiOutside : i ∈ Finset.univ \ C := by simp [hiC]
    rw [Finset.sum_eq_single_of_mem i hiOutside]
    · simp [hiC]
    · intro j hj hji
      have hjC : j ∉ C := (Finset.mem_sdiff.mp hj).2
      simp only [dif_neg hjC, if_neg hji]
  have htotalY : (∑ j : Fin n, y j) = C.sum y + (Finset.univ \ C).sum y := by
    have hsplit := Finset.sum_sdiff (Finset.subset_univ C) (f := y)
    linarith
  have hpenalty :
      C.sum (fun j ↦
          max (a j - flow_cover_excess a b C) 0 * (1 - x j)) =
        ∑ k : Fin C.card,
          max (a (coverOrder k) - flow_cover_excess a b C) 0 *
            (1 - if xCover k then (1 : ℝ) else 0) := by
    rw [← sum_comp_coverOrder_eq C coverOrder hcoverOrder]
    apply Finset.sum_congr rfl
    intro k hk
    simp [x, coverOrder_mem_cover C coverOrder hcoverOrder k, hinv]
  have hp_mem : p ∈ single_node_flow_set a b := by
    rw [mem_single_node_flow_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hjC : j ∈ C
      · cases hxc : xCover (Function.invFun coverOrder j)
        · left
          simp [p, x, hjC, hxc]
        · right
          simp [p, x, hjC, hxc]
      · by_cases hji : j = i
        · subst j
          right
          simp [p, x, hiC]
        · left
          simp [p, x, hjC, hji]
    · intro j
      by_cases hjC : j ∈ C
      · have hjRange : j ∈ Set.range coverOrder := by
          rw [hcoverOrder]
          exact hjC
        rcases hjRange with ⟨k, rfl⟩
        simpa [p, y, coverOrder_mem_cover C coverOrder hcoverOrder k, hinv] using hy_nonneg k
      · by_cases hji : j = i
        · subst j
          simpa [p, y, hiC] using hz.1
        · simp [p, y, hjC, hji]
    · change ∑ j : Fin n, y j ≤ b
      rw [htotalY, hcoverY, houtsideY]
      linarith
    · intro j
      by_cases hjC : j ∈ C
      · have hjRange : j ∈ Set.range coverOrder := by
          rw [hcoverOrder]
          exact hjC
        rcases hjRange with ⟨k, rfl⟩
        simpa [p, x, y, coverOrder_mem_cover C coverOrder hcoverOrder k, hinv,
          Function.comp_apply] using hy_capacity k
      · by_cases hji : j = i
        · subst j
          simpa [p, x, y, hiC] using hz.2.trans (min_le_left _ _)
        · simp [p, x, y, hjC, hji]
  refine ⟨p, hp_mem, ?_, ?_, ?_, ?_⟩
  · simp [p, x, hiC]
  · simp [p, y, hiC]
  · rw [flow_cover_value_eq]
    change C.sum y +
        C.sum (fun j ↦ max (a j - flow_cover_excess a b C) 0 * (1 - x j)) = v
    rw [hcoverY, hpenalty, ← Finset.sum_add_distrib]
    exact hv_eq.symm
  · intro j hjC hji
    simp [p, x, y, hjC, hji]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: a contact of one outside
affine cost with the lifting profile extends to a point of the lifted equality face, supported
outside the cover only at that coordinate. -/
theorem flowCoverContact_extensionPoint_mem_liftedFace
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (i : Fin n)
    (hiC : i ∉ C)
    {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) (min (a i) b))
    (hcontact :
      α i * z + β i =
        flow_cover_lifting_function
          b (flow_cover_excess a b C) (a ∘ coverOrder) z) :
    ∃ p : (Fin n → ℝ) × (Fin n → ℝ),
      p ∈ flow_cover_lifted_face a b C α β b ∧
        p.1 i = 1 ∧
          p.2 i = z ∧
            ∀ j, j ∉ C → j ≠ i → p.1 j = 0 ∧ p.2 j = 0 := by
  classical
  have hoptimizer :=
    flowCoverLiftingFunction_complement_mem_objectiveValues
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
      ⟨hz.1, hz.2.trans (min_le_right _ _)⟩
  rcases flowCoverObjective_extensionPoint
      a b C coverOrder hcoverOrder (cutIndex_nonempty a C coverOrder hr)
      i hiC hz hoptimizer with
    ⟨p, hp, hpx, hpy, hpCover, hpOutside⟩
  have hiOutside : i ∈ Finset.univ \ C := by
    simp [hiC]
  have houtside :
      (Finset.univ \ C).sum (fun j ↦ α j * p.2 j + β j * p.1 j) =
        α i * z + β i := by
    rw [Finset.sum_eq_single_of_mem i hiOutside]
    · rw [hpx, hpy]
      ring
    · intro j hj hji
      have hjC : j ∉ C := (Finset.mem_sdiff.mp hj).2
      rcases hpOutside j hjC hji with ⟨hxj, hyj⟩
      rw [hxj, hyj]
      ring
  refine ⟨p, ?_, hpx, hpy, hpOutside⟩
  rw [mem_flow_cover_lifted_face_iff, flow_cover_lifted_value_eq, houtside,
    hpCover, hcontact]
  exact ⟨subset_convexHull ℝ (single_node_flow_set a b) hp, sub_add_cancel _ _⟩

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: global validity of a lifted
flow-cover inequality implies each outside affine cost is valid on its effective interval. -/
theorem cappedValid_of_flowCoverLiftedValid
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hglobal :
      ∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (single_node_flow_set a b) →
          flow_cover_lifted_value a b C α β p ≤ b)
    (i : Fin n)
    (hiC : i ∉ C) :
    ∀ y ∈ Set.Icc (0 : ℝ) (min (a i) b),
      α i * y + β i ≤
        flow_cover_lifting_function
          b (flow_cover_excess a b C) (a ∘ coverOrder) y := by
  intro y hy
  have hoptimizer :=
    flowCoverLiftingFunction_complement_mem_objectiveValues
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
      ⟨hy.1, hy.2.trans (min_le_right _ _)⟩
  rcases flowCoverObjective_extensionPoint
      a b C coverOrder hcoverOrder (cutIndex_nonempty a C coverOrder hr) i hiC hy hoptimizer with
    ⟨p, hp, hpx, hpy, hpCover, hpOutside⟩
  have hpValid := hglobal (subset_convexHull ℝ (single_node_flow_set a b) hp)
  have hiOutside : i ∈ Finset.univ \ C := by simp [hiC]
  have houtside :
      (Finset.univ \ C).sum (fun j ↦ α j * p.2 j + β j * p.1 j) =
        α i * y + β i := by
    rw [Finset.sum_eq_single_of_mem i hiOutside]
    · rw [hpx, hpy]
      ring
    · intro j hj hji
      have hjC : j ∉ C := (Finset.mem_sdiff.mp hj).2
      rcases hpOutside j hjC hji with ⟨hxj, hyj⟩
      rw [hxj, hyj]
      ring
  -- Substitute the attained cover objective and isolate the chosen outside affine cost.
  rw [flow_cover_lifted_value_eq, houtside, hpCover] at hpValid
  linarith

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: pointwise capped validity on all
outside coordinates implies validity of the lifted flow-cover inequality on the whole convex
hull. -/
theorem flowCoverLiftedValid_of_all_cappedValid
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hvalid :
      ∀ i, i ∉ C →
        ∀ y ∈ Set.Icc (0 : ℝ) (min (a i) b),
          α i * y + β i ≤
            flow_cover_lifting_function
              b (flow_cover_excess a b C) (a ∘ coverOrder) y) :
    ∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
      p ∈ convexHull ℝ (single_node_flow_set a b) →
        flow_cover_lifted_value a b C α β p ≤ b := by
  let f := flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder)
  have hf_zero : f 0 = 0 := by
    exact flowCoverLiftingFunction_zero
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
  have hsuper : SequenceIndependentLifting.is_superadditive_on_Icc f b := by
    exact flowCoverLiftingFunction_superadditive a b C coverOrder ha_nonneg hC hcoverOrder
  have hsource :
      single_node_flow_set a b ⊆ {p | flow_cover_lifted_value a b C α β p ≤ b} := by
    intro p hp
    rcases (mem_single_node_flow_set_iff a b p).mp hp with
      ⟨hx_binary, hy_nonneg, hy_sum, hy_capacity⟩
    let J : Finset (Fin n) := Finset.univ \ C
    let z : ℝ := J.sum p.2
    have hcover_nonneg : 0 ≤ C.sum p.2 :=
      Finset.sum_nonneg fun j hj ↦ hy_nonneg j
    have hsum_split : J.sum p.2 + C.sum p.2 = ∑ j : Fin n, p.2 j := by
      dsimp [J]
      exact Finset.sum_sdiff (Finset.subset_univ C) (f := p.2)
    have hz : z ∈ Set.Icc (0 : ℝ) b := by
      constructor
      · exact Finset.sum_nonneg fun j hj ↦ hy_nonneg j
      · dsimp [z]
        linarith
    have hcover_mem :
        flow_cover_value a b C p ∈
          flow_cover_lifting_objective_values
            b (flow_cover_excess a b C) (a ∘ coverOrder) z := by
      simpa [z, J] using
        flowCoverValue_mem_objectiveValues_of_mem_singleNodeFlowSet
          a b C coverOrder hcoverOrder hp
    have hcover_sup :
        flow_cover_value a b C p ≤
          sSup
            (flow_cover_lifting_objective_values
              b (flow_cover_excess a b C) (a ∘ coverOrder) z) :=
      le_csSup
        (flow_cover_lifting_objective_values_bddAbove
          b (flow_cover_excess a b C) (a ∘ coverOrder) z)
        hcover_mem
    have hcover_bound : flow_cover_value a b C p ≤ b - f z := by
      dsimp [f]
      rw [flow_cover_lifting_function]
      linarith
    have hterm :
        ∀ i ∈ J,
          α i * p.2 i + β i * p.1 i ≤ f (p.2 i) := by
      intro i hi
      have hiC : i ∉ C := (Finset.mem_sdiff.mp hi).2
      rcases hx_binary i with hxi | hxi
      · have hy_zero : p.2 i = 0 := by
          have hy_upper := hy_capacity i
          rw [hxi] at hy_upper
          simpa using le_antisymm (by simpa using hy_upper) (hy_nonneg i)
        simp [hxi, hy_zero, hf_zero]
      · have hy_le_b : p.2 i ≤ b := by
          have hrest_nonneg : 0 ≤ ∑ j ∈ Finset.univ.erase i, p.2 j :=
            Finset.sum_nonneg fun j hj ↦ hy_nonneg j
          have hsplit :
              (∑ j : Fin n, p.2 j) = p.2 i + ∑ j ∈ Finset.univ.erase i, p.2 j := by
            rw [add_comm]
            exact
              (Finset.sum_erase_add (s := Finset.univ) (f := p.2) (Finset.mem_univ i)).symm
          rw [hsplit] at hy_sum
          linarith
        have hy_le_a : p.2 i ≤ a i := by
          simpa [hxi] using hy_capacity i
        have hy_interval : p.2 i ∈ Set.Icc (0 : ℝ) (min (a i) b) :=
          ⟨hy_nonneg i, le_min hy_le_a hy_le_b⟩
        simpa [hxi, f] using hvalid i hiC (p.2 i) hy_interval
    have houtside_bound :
        J.sum (fun i ↦ α i * p.2 i + β i * p.1 i) ≤ f z := by
      calc
        J.sum (fun i ↦ α i * p.2 i + β i * p.1 i) ≤
            J.sum (fun i ↦ f (p.2 i)) := Finset.sum_le_sum hterm
        _ ≤ f z := by
          by_cases hJ : J.Nonempty
          · exact
              SequenceIndependentLifting.superadditive_sum_le_of_nonempty
                p.2 f b hsuper J hJ
                (fun j hj ↦ ⟨hy_nonneg j, (Finset.single_le_sum
                  (fun k hk ↦ hy_nonneg k) hj).trans hz.2⟩)
                hz
          · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
            simp [hJempty, z, hf_zero]
    -- The cover contribution and all local contributions fit below the common profile budget.
    change flow_cover_lifted_value a b C α β p ≤ b
    rw [flow_cover_lifted_value_eq]
    dsimp [J] at houtside_bound
    linarith
  intro p hp
  -- Convexity extends validity from the original mixed-binary set to its convex hull.
  exact
    convexHull_min hsource (convex_flowCoverLiftedValue_sublevel a α β b b C) hp

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: at a tight original
single-node-flow point, every selected outside coordinate is a contact of its affine lifting cost
with the common profile. -/
theorem flowCoverSourcePoint_contact_of_tight
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hvalid :
      ∀ i, i ∉ C →
        ∀ y ∈ Set.Icc (0 : ℝ) (min (a i) b),
          α i * y + β i ≤
            flow_cover_lifting_function
              b (flow_cover_excess a b C) (a ∘ coverOrder) y)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ single_node_flow_set a b)
    (hpTight : flow_cover_lifted_value a b C α β p = b)
    (i : Fin n) (hiC : i ∉ C) (hxi : p.1 i = 1) :
    α i * p.2 i + β i =
      flow_cover_lifting_function
        b (flow_cover_excess a b C) (a ∘ coverOrder) (p.2 i) := by
  classical
  let f := flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder)
  let J : Finset (Fin n) := Finset.univ \ C
  let z : ℝ := J.sum p.2
  rcases (mem_single_node_flow_set_iff a b p).mp hp with
    ⟨hx_binary, hy_nonneg, hy_sum, hy_capacity⟩
  have hcover_nonneg : 0 ≤ C.sum p.2 :=
    Finset.sum_nonneg fun j hj ↦ hy_nonneg j
  have hsum_split : J.sum p.2 + C.sum p.2 = ∑ j : Fin n, p.2 j := by
    dsimp [J]
    exact Finset.sum_sdiff (Finset.subset_univ C) (f := p.2)
  have hz : z ∈ Set.Icc (0 : ℝ) b := by
    constructor
    · exact Finset.sum_nonneg fun j hj ↦ hy_nonneg j
    · dsimp [z]
      linarith
  have hcover_mem :
      flow_cover_value a b C p ∈
        flow_cover_lifting_objective_values
          b (flow_cover_excess a b C) (a ∘ coverOrder) z := by
    simpa [z, J] using
      flowCoverValue_mem_objectiveValues_of_mem_singleNodeFlowSet
        a b C coverOrder hcoverOrder hp
  have hcover_sup :
      flow_cover_value a b C p ≤
        sSup
          (flow_cover_lifting_objective_values
            b (flow_cover_excess a b C) (a ∘ coverOrder) z) :=
    le_csSup
      (flow_cover_lifting_objective_values_bddAbove
        b (flow_cover_excess a b C) (a ∘ coverOrder) z)
      hcover_mem
  have hcover_bound : flow_cover_value a b C p ≤ b - f z := by
    dsimp [f]
    rw [flow_cover_lifting_function]
    linarith
  have hf_zero : f 0 = 0 := by
    exact flowCoverLiftingFunction_zero
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
  have hterm :
      ∀ j ∈ J, α j * p.2 j + β j * p.1 j ≤ f (p.2 j) := by
    intro j hj
    have hjC : j ∉ C := (Finset.mem_sdiff.mp hj).2
    rcases hx_binary j with hxj | hxj
    · have hyj : p.2 j = 0 := by
        have hupper := hy_capacity j
        rw [hxj] at hupper
        exact le_antisymm (by simpa using hupper) (hy_nonneg j)
      simp [hxj, hyj, hf_zero]
    · have hy_le_b : p.2 j ≤ b := by
        have hrest_nonneg : 0 ≤ ∑ k ∈ Finset.univ.erase j, p.2 k :=
          Finset.sum_nonneg fun k hk ↦ hy_nonneg k
        have hsplit :
            (∑ k : Fin n, p.2 k) = p.2 j + ∑ k ∈ Finset.univ.erase j, p.2 k := by
          rw [add_comm]
          exact
            (Finset.sum_erase_add (s := Finset.univ) (f := p.2) (Finset.mem_univ j)).symm
        rw [hsplit] at hy_sum
        linarith
      have hy_le_a : p.2 j ≤ a j := by
        simpa [hxj] using hy_capacity j
      have hy_interval : p.2 j ∈ Set.Icc (0 : ℝ) (min (a j) b) :=
        ⟨hy_nonneg j, le_min hy_le_a hy_le_b⟩
      simpa [hxj, f] using hvalid j hjC (p.2 j) hy_interval
  have hsuper : SequenceIndependentLifting.is_superadditive_on_Icc f b := by
    exact flowCoverLiftingFunction_superadditive a b C coverOrder ha_nonneg hC hcoverOrder
  have hprofileSum : J.sum (fun j ↦ f (p.2 j)) ≤ f z := by
    by_cases hJ : J.Nonempty
    · exact
        SequenceIndependentLifting.superadditive_sum_le_of_nonempty
          p.2 f b hsuper J hJ
          (fun j hj ↦ ⟨hy_nonneg j, (Finset.single_le_sum
            (fun k hk ↦ hy_nonneg k) hj).trans hz.2⟩)
          hz
    · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      simp [hJempty, z, hf_zero]
  apply le_antisymm
  · simpa [hxi, f] using hterm i (by simp [J, hiC])
  · by_contra hnot
    have hiStrict : f (p.2 i) > α i * p.2 i + β i := lt_of_not_ge hnot
    have houtsideStrict :
        J.sum (fun j ↦ α j * p.2 j + β j * p.1 j) <
          J.sum (fun j ↦ f (p.2 j)) := by
      refine Finset.sum_lt_sum hterm ?_
      exact ⟨i, by simp [J, hiC], by simpa [hxi] using hiStrict⟩
    have htotalStrict : flow_cover_lifted_value a b C α β p < b := by
      rw [flow_cover_lifted_value_eq]
      dsimp [J] at houtsideStrict
      linarith
    linarith

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the flow at a selected
coordinate of a feasible single-node point lies in its effective capped interval. -/
theorem singleNodeFlow_selectedCoordinate_mem_cappedInterval
    (a : Fin n → ℝ) (b : ℝ)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ single_node_flow_set a b)
    (i : Fin n) (hxi : p.1 i = 1) :
    p.2 i ∈ Set.Icc (0 : ℝ) (min (a i) b) := by
  rcases (mem_single_node_flow_set_iff a b p).mp hp with
    ⟨-, hy_nonneg, hy_sum, hy_capacity⟩
  have hy_le_a : p.2 i ≤ a i := by
    simpa [hxi] using hy_capacity i
  have hrest_nonneg : 0 ≤ ∑ j ∈ Finset.univ.erase i, p.2 j :=
    Finset.sum_nonneg fun j hj ↦ hy_nonneg j
  have hsplit :
      (∑ j : Fin n, p.2 j) = p.2 i + ∑ j ∈ Finset.univ.erase i, p.2 j := by
    rw [add_comm]
    exact
      (Finset.sum_erase_add (s := Finset.univ) (f := p.2) (Finset.mem_univ i)).symm
  have hy_le_b : p.2 i ≤ b := by
    rw [hsplit] at hy_sum
    linarith
  exact ⟨hy_nonneg i, le_min hy_le_a hy_le_b⟩

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: global lifted validity is
equivalent to validity of every outside affine cost on its effective interval. -/
theorem flowCoverLiftedValidity_iff_all_cappedValid
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (single_node_flow_set a b) →
          flow_cover_lifted_value a b C α β p ≤ b) ↔
      ∀ i, i ∉ C →
        ∀ y ∈ Set.Icc (0 : ℝ) (min (a i) b),
          α i * y + β i ≤
            flow_cover_lifting_function
              b (flow_cover_excess a b C) (a ∘ coverOrder) y := by
  constructor
  · intro hglobal i hiC
    -- Optimizer-backed extension points test the global inequality one coordinate at a time.
    exact cappedValid_of_flowCoverLiftedValid
      a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hglobal i hiC
  · intro hlocal
    -- Superadditivity combines all locally valid outside contributions.
    exact flowCoverLiftedValid_of_all_cappedValid
      a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hlocal

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: zeroing both variable blocks
outside the cover preserves feasibility of a single-node flow point. -/
theorem flowCoverPairProjection_mem_singleNodeFlowSet
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ single_node_flow_set a b) :
    flowCoverPairProjection C p ∈ single_node_flow_set a b := by
  classical
  rcases (mem_single_node_flow_set_iff a b p).mp hp with
    ⟨hx, hy_nonneg, hy_sum, hy_capacity⟩
  rw [mem_single_node_flow_set_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ C
    · simpa [flowCoverPairProjection, flowCoverCoordinateProjection, hi] using hx i
    · exact Or.inl (by simp [flowCoverPairProjection, flowCoverCoordinateProjection, hi])
  · intro i
    by_cases hi : i ∈ C
    · simpa [flowCoverPairProjection, flowCoverCoordinateProjection, hi] using hy_nonneg i
    · simp [flowCoverPairProjection, flowCoverCoordinateProjection, hi]
  · have hsum_le :
        ∑ i, (flowCoverPairProjection C p).2 i ≤ ∑ i, p.2 i := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiC : i ∈ C
      · simp [flowCoverPairProjection, flowCoverCoordinateProjection, hiC]
      · simpa [flowCoverPairProjection, flowCoverCoordinateProjection, hiC] using hy_nonneg i
    exact hsum_le.trans hy_sum
  · intro i
    by_cases hi : i ∈ C
    · simpa [flowCoverPairProjection, flowCoverCoordinateProjection, hi] using hy_capacity i
    · simp [flowCoverPairProjection, flowCoverCoordinateProjection, hi]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the cover projection maps the
single-node convex hull into itself. -/
theorem flowCoverPairProjection_mem_convexHull
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ convexHull ℝ (single_node_flow_set a b)) :
    flowCoverPairProjection C p ∈ convexHull ℝ (single_node_flow_set a b) := by
  let R := flowCoverPairProjection (n := n) C
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (single_node_flow_set a b)
  have hpreimageConvex : Convex ℝ (R ⁻¹' P) := by
    exact (convex_convexHull ℝ (single_node_flow_set a b)).linear_preimage R
  have hgenerators : single_node_flow_set a b ⊆ R ⁻¹' P := by
    intro q hq
    exact subset_convexHull ℝ _ (flowCoverPairProjection_mem_singleNodeFlowSet a b C hq)
  exact convexHull_min hgenerators hpreimageConvex hp

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the cover projection maps
ambient single-node-flow directions back into the ambient direction. -/
theorem flowCoverPairProjection_mem_ambientDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    {v : (Fin n → ℝ) × (Fin n → ℝ)}
    (hv : v ∈ (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction) :
    flowCoverPairProjection C v ∈
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction := by
  let R := flowCoverPairProjection (n := n) C
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (single_node_flow_set a b)
  have himage : R '' P ⊆ P := by
    rintro q ⟨p, hp, rfl⟩
    exact flowCoverPairProjection_mem_convexHull a b C hp
  have hmapAffineLe : (affineSpan ℝ P).map R.toAffineMap ≤ affineSpan ℝ P := by
    rw [AffineSubspace.map_span]
    exact affineSpan_mono ℝ himage
  have hmapDirectionLe : Submodule.map R (affineSpan ℝ P).direction ≤
      (affineSpan ℝ P).direction := by
    have hdirection := AffineSubspace.direction_le hmapAffineLe
    simpa only [AffineSubspace.map_direction] using hdirection
  exact hmapDirectionLe (Submodule.mem_map.mpr ⟨v, hv, rfl⟩)

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: at a positive-capacity
coordinate outside the cover, every pair of selector and flow coordinate values occurs in an
ambient single-node-flow direction. -/
theorem flowCoverOutsideCoordinatePair_mem_ambientDirection
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j)
    {i : Fin n} (hiC : i ∉ C) (hi_pos : 0 < a i)
    (sx sy : ℝ) :
    ((fun j ↦ if j = i then sx else 0),
        fun j ↦ if j = i then sy else 0) ∈
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction := by
  rcases h_excess_lt_some with ⟨j₀, hj₀C, hj₀lt⟩
  have hbaseDirection :=
    flowCoverOutsideSupportedPair_mem_faceDirection
      a b C ha_nonneg hC hj₀C hj₀lt hiC sx sy
      (fun hai ↦ by linarith)
  exact AffineSubspace.direction_le
    (affineSpan_mono ℝ (fun p hp ↦ (mem_flow_cover_face_iff a b C p).mp hp |>.1))
    hbaseDirection

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: projecting a point of the
zero-lifted face onto the cover gives a point of every lifted face. -/
theorem flowCoverPairProjection_mem_liftedFace
    (a α β : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ flow_cover_face a b C) :
    flowCoverPairProjection C p ∈ flow_cover_lifted_face a b C α β b := by
  classical
  have hpData := (mem_flow_cover_face_iff a b C p).mp hp
  rw [mem_flow_cover_lifted_face_iff]
  refine ⟨flowCoverPairProjection_mem_convexHull a b C hpData.1, ?_⟩
  have hcoverValue :
      flow_cover_value a b C (flowCoverPairProjection C p) = flow_cover_value a b C p := by
    apply flowCoverValue_eq_of_coverCoordinateAgreement a b C
    · intro j hj
      simp [flowCoverPairProjection, flowCoverCoordinateProjection, hj]
    · intro j hj
      simp [flowCoverPairProjection, flowCoverCoordinateProjection, hj]
  rw [flow_cover_lifted_value_eq, hcoverValue, hpData.2]
  have houtside :
      ∑ i ∈ Finset.univ \ C,
          (α i * (flowCoverPairProjection C p).2 i +
            β i * (flowCoverPairProjection C p).1 i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiC : i ∉ C := (Finset.mem_sdiff.mp hi).2
    simp [flowCoverPairProjection, flowCoverCoordinateProjection, hiC]
  rw [houtside, add_zero]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: every cover-supported
direction of the zero-lifted face is a direction of the lifted face. -/
theorem flowCoverSupportedDirection_mem_liftedFaceDirection
    (a α β : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    {v : (Fin n → ℝ) × (Fin n → ℝ)}
    (hv : v ∈ (affineSpan ℝ (flow_cover_face a b C)).direction)
    (hsupport : flowCoverPairProjection C v = v) :
    v ∈ (affineSpan ℝ (flow_cover_lifted_face a b C α β b)).direction := by
  let R := flowCoverPairProjection (n := n) C
  let F₀ : Set ((Fin n → ℝ) × (Fin n → ℝ)) := flow_cover_face a b C
  let F : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    flow_cover_lifted_face a b C α β b
  have himage : R '' F₀ ⊆ F := by
    rintro q ⟨p, hp, rfl⟩
    exact flowCoverPairProjection_mem_liftedFace a α β b C hp
  have hmapAffineLe : (affineSpan ℝ F₀).map R.toAffineMap ≤ affineSpan ℝ F := by
    rw [AffineSubspace.map_span]
    exact affineSpan_mono ℝ himage
  have hmapDirectionLe :
      Submodule.map R (affineSpan ℝ F₀).direction ≤ (affineSpan ℝ F).direction := by
    -- Pass to directions after mapping the affine span, then use the named map formula.
    have hdirection := AffineSubspace.direction_le hmapAffineLe
    simpa only [AffineSubspace.map_direction] using hdirection
  have hvMap : v ∈ Submodule.map R (affineSpan ℝ F₀).direction := by
    exact Submodule.mem_map.mpr ⟨v, hv, hsupport⟩
  exact hmapDirectionLe hvMap

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the direction of a nonempty
lifted equality face lies in the ambient direction and in the kernel of its canonical support
map. -/
theorem flowCoverLiftedFaceDirection_le_ambient_inf_supportKer
    (a α β : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (hfaceNonempty : (flow_cover_lifted_face a b C α β b).Nonempty) :
    (affineSpan ℝ (flow_cover_lifted_face a b C α β b)).direction ≤
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction ⊓
        LinearMap.ker (flowCoverLiftedSupportLinearMap a α β b C) := by
  classical
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (single_node_flow_set a b)
  let F : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    flow_cover_lifted_face a b C α β b
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    flowCoverLiftedSupportLinearMap a α β b C
  let δ : ℝ := b - ∑ j ∈ C, flowCoverSupportCoeff a b C j
  rcases hfaceNonempty with ⟨q, hqF⟩
  have hlevel : ∀ x ∈ F, L x = δ := by
    intro x hx
    have hxValue := (mem_flow_cover_lifted_face_iff a b C α β b x).mp hx |>.2
    have hsplit := flow_cover_lifted_value_eq_support_add_constant a α β b C x
    dsimp [L, δ]
    linarith
  have hspanLevel :
      (affineSpan ℝ F : Set ((Fin n → ℝ) × (Fin n → ℝ))) ⊆ {x | L x = δ} := by
    intro x hx
    -- Constancy of a linear functional is an affine condition, so it extends to the span.
    refine affineSpan_induction (k := ℝ) (s := F)
      (p := fun y : (Fin n → ℝ) × (Fin n → ℝ) ↦ L y = δ) hx ?_ ?_
    · intro y hy
      exact hlevel y hy
    · intro t x y z hx hy hz
      simp [hx, hy, hz, sub_eq_add_neg, add_comm]
  intro v hv
  refine ⟨?_, ?_⟩
  · -- Forgetting equality preserves membership in the ambient affine direction.
    exact AffineSubspace.direction_le
      (affineSpan_mono ℝ (fun x hx ↦
        (mem_flow_cover_lifted_face_iff a b C α β b x).mp hx |>.1)) hv
  · have hqSpan : q ∈ affineSpan ℝ F := subset_affineSpan ℝ F hqF
    change L v = 0
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hqSpan] at hv
    rcases hv with ⟨x, hxSpan, rfl⟩
    have hxLevel : L x = δ := hspanLevel hxSpan
    have hqLevel : L q = δ := hlevel q hqF
    simp [vsub_eq_sub, hxLevel, hqLevel]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: two distinct contacts in
every outside coordinate span all outside directions; after removing them, the cover projection
transports the residual zero-lifted direction into the lifted face. -/
theorem flowCoverLiftedFaceDirection_eq_ambient_inf_supportKer_of_contacts
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hcontacts :
      ∀ i, i ∉ C →
        ∃ y' ∈ Set.Icc (0 : ℝ) (min (a i) b),
          ∃ y'' ∈ Set.Icc (0 : ℝ) (min (a i) b),
            y' ≠ y'' ∧
              α i * y' + β i =
                flow_cover_lifting_function
                  b (flow_cover_excess a b C) (a ∘ coverOrder) y' ∧
              α i * y'' + β i =
                flow_cover_lifting_function
                  b (flow_cover_excess a b C) (a ∘ coverOrder) y'') :
    (affineSpan ℝ (flow_cover_lifted_face a b C α β b)).direction =
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction ⊓
        LinearMap.ker (flowCoverLiftedSupportLinearMap a α β b C) := by
  classical
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (single_node_flow_set a b)
  let F₀ : Set ((Fin n → ℝ) × (Fin n → ℝ)) := flow_cover_face a b C
  let F : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    flow_cover_lifted_face a b C α β b
  let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ P).direction
  let FD : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) := (affineSpan ℝ F).direction
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    flowCoverLiftedSupportLinearMap a α β b C
  have hzeroFacet :=
    zeroLiftingFacetDefining_of_isCutIndex
      a b C coverOrder r ha_nonneg hC hcoverOrder hr
  rcases (isFacetOf_iff.mp hzeroFacet.2).1 with ⟨q₀, hq₀F⟩
  let q := flowCoverPairProjection C q₀
  have hqF : q ∈ F := by
    exact flowCoverPairProjection_mem_liftedFace a α β b C hq₀F
  have hqOutside (j : Fin n) (hjC : j ∉ C) : q.1 j = 0 ∧ q.2 j = 0 := by
    simp [q, flowCoverPairProjection, flowCoverCoordinateProjection, hjC]
  have hcontactData :
      ∀ k : {i : Fin n // i ∉ C},
        ∃ y' ∈ Set.Icc (0 : ℝ) (min (a k.1) b),
          ∃ y'' ∈ Set.Icc (0 : ℝ) (min (a k.1) b),
            y' ≠ y'' ∧
              α k.1 * y' + β k.1 =
                flow_cover_lifting_function
                  b (flow_cover_excess a b C) (a ∘ coverOrder) y' ∧
              α k.1 * y'' + β k.1 =
                flow_cover_lifting_function
                  b (flow_cover_excess a b C) (a ∘ coverOrder) y'' := by
    intro k
    exact hcontacts k.1 k.2
  choose y₁ hy₁ y₂ hy₂ hyNe hy₁Contact hy₂Contact using hcontactData
  have hp₁Exists :
      ∀ k : {i : Fin n // i ∉ C},
        ∃ p : (Fin n → ℝ) × (Fin n → ℝ),
          p ∈ F ∧ p.1 k.1 = 1 ∧ p.2 k.1 = y₁ k ∧
            ∀ j, j ∉ C → j ≠ k.1 → p.1 j = 0 ∧ p.2 j = 0 := by
    intro k
    exact flowCoverContact_extensionPoint_mem_liftedFace
      a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
      k.1 k.2 (hy₁ k) (hy₁Contact k)
  have hp₂Exists :
      ∀ k : {i : Fin n // i ∉ C},
        ∃ p : (Fin n → ℝ) × (Fin n → ℝ),
          p ∈ F ∧ p.1 k.1 = 1 ∧ p.2 k.1 = y₂ k ∧
            ∀ j, j ∉ C → j ≠ k.1 → p.1 j = 0 ∧ p.2 j = 0 := by
    intro k
    exact flowCoverContact_extensionPoint_mem_liftedFace
      a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
      k.1 k.2 (hy₂ k) (hy₂Contact k)
  choose p₁ hp₁F hp₁x hp₁y hp₁Outside using hp₁Exists
  choose p₂ hp₂F hp₂x hp₂y hp₂Outside using hp₂Exists
  let dX : {i : Fin n // i ∉ C} → (Fin n → ℝ) × (Fin n → ℝ) := fun k ↦ p₁ k - q
  let dY : {i : Fin n // i ∉ C} → (Fin n → ℝ) × (Fin n → ℝ) := fun k ↦ p₂ k - p₁ k
  have hdXMem (k : {i : Fin n // i ∉ C}) : dX k ∈ FD := by
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ F (hp₁F k)) (subset_affineSpan ℝ F hqF)
  have hdYMem (k : {i : Fin n // i ∉ C}) : dY k ∈ FD := by
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ F (hp₂F k)) (subset_affineSpan ℝ F (hp₁F k))
  have hdXFstSelf (k : {i : Fin n // i ∉ C}) : (dX k).1 k.1 = 1 := by
    simp [dX, hp₁x k, (hqOutside k.1 k.2).1]
  have hdXSndSelf (k : {i : Fin n // i ∉ C}) : (dX k).2 k.1 = y₁ k := by
    simp [dX, hp₁y k, (hqOutside k.1 k.2).2]
  have hdXFstOther (k : {i : Fin n // i ∉ C}) (j : Fin n)
      (hjC : j ∉ C) (hjk : j ≠ k.1) : (dX k).1 j = 0 := by
    rcases hp₁Outside k j hjC hjk with ⟨hpj, -⟩
    simp [dX, hpj, (hqOutside j hjC).1]
  have hdXSndOther (k : {i : Fin n // i ∉ C}) (j : Fin n)
      (hjC : j ∉ C) (hjk : j ≠ k.1) : (dX k).2 j = 0 := by
    rcases hp₁Outside k j hjC hjk with ⟨-, hpj⟩
    simp [dX, hpj, (hqOutside j hjC).2]
  have hdYFstSelf (k : {i : Fin n // i ∉ C}) : (dY k).1 k.1 = 0 := by
    simp [dY, hp₁x k, hp₂x k]
  have hdYSndSelf (k : {i : Fin n // i ∉ C}) : (dY k).2 k.1 = y₂ k - y₁ k := by
    simp [dY, hp₁y k, hp₂y k]
  have hdYFstOther (k : {i : Fin n // i ∉ C}) (j : Fin n)
      (hjC : j ∉ C) (hjk : j ≠ k.1) : (dY k).1 j = 0 := by
    rcases hp₁Outside k j hjC hjk with ⟨hp₁j, -⟩
    rcases hp₂Outside k j hjC hjk with ⟨hp₂j, -⟩
    simp [dY, hp₁j, hp₂j]
  have hdYSndOther (k : {i : Fin n // i ∉ C}) (j : Fin n)
      (hjC : j ∉ C) (hjk : j ≠ k.1) : (dY k).2 j = 0 := by
    rcases hp₁Outside k j hjC hjk with ⟨-, hp₁j⟩
    rcases hp₂Outside k j hjC hjk with ⟨-, hp₂j⟩
    simp [dY, hp₁j, hp₂j]
  apply le_antisymm
  · simpa only [FD, D, L, F, P] using
      flowCoverLiftedFaceDirection_le_ambient_inf_supportKer
        a α β b C ⟨q, hqF⟩
  · intro v hv
    let outsideTerm : {i : Fin n // i ∉ C} → (Fin n → ℝ) × (Fin n → ℝ) := fun k ↦
      v.1 k.1 • dX k +
        ((v.2 k.1 - v.1 k.1 * y₁ k) / (y₂ k - y₁ k)) • dY k
    let w : (Fin n → ℝ) × (Fin n → ℝ) := ∑ k, outsideTerm k
    have houtsideTermMem (k : {i : Fin n // i ∉ C}) : outsideTerm k ∈ FD := by
      exact FD.add_mem
        (FD.smul_mem (v.1 k.1) (hdXMem k))
        (FD.smul_mem ((v.2 k.1 - v.1 k.1 * y₁ k) / (y₂ k - y₁ k)) (hdYMem k))
    have hwMem : w ∈ FD := by
      exact Submodule.sum_mem FD (fun k hk ↦ houtsideTermMem k)
    have houtsideTermFstSelf (k : {i : Fin n // i ∉ C}) :
        (outsideTerm k).1 k.1 = v.1 k.1 := by
      simp [outsideTerm, hdXFstSelf k, hdYFstSelf k]
    have houtsideTermSndSelf (k : {i : Fin n // i ∉ C}) :
        (outsideTerm k).2 k.1 = v.2 k.1 := by
      have hden : y₂ k - y₁ k ≠ 0 := sub_ne_zero.mpr (Ne.symm (hyNe k))
      simp only [outsideTerm, Prod.snd_add, Pi.add_apply, Prod.smul_snd, Pi.smul_apply,
        smul_eq_mul,
        hdXSndSelf k, hdYSndSelf k]
      rw [div_mul_cancel₀ _ hden]
      ring
    have houtsideTermFstOther (k : {i : Fin n // i ∉ C}) (j : Fin n)
        (hjC : j ∉ C) (hjk : j ≠ k.1) : (outsideTerm k).1 j = 0 := by
      simp [outsideTerm, hdXFstOther k j hjC hjk, hdYFstOther k j hjC hjk]
    have houtsideTermSndOther (k : {i : Fin n // i ∉ C}) (j : Fin n)
        (hjC : j ∉ C) (hjk : j ≠ k.1) : (outsideTerm k).2 j = 0 := by
      simp [outsideTerm, hdXSndOther k j hjC hjk, hdYSndOther k j hjC hjk]
    have hwFst (j : Fin n) (hjC : j ∉ C) : w.1 j = v.1 j := by
      let k₀ : {i : Fin n // i ∉ C} := ⟨j, hjC⟩
      dsimp only [w]
      rw [Prod.fst_sum, Finset.sum_apply, Fintype.sum_eq_single k₀]
      · exact houtsideTermFstSelf k₀
      · intro k hkk₀
        apply houtsideTermFstOther k j hjC
        intro hjk
        apply hkk₀
        apply Subtype.ext
        exact hjk.symm
    have hwSnd (j : Fin n) (hjC : j ∉ C) : w.2 j = v.2 j := by
      let k₀ : {i : Fin n // i ∉ C} := ⟨j, hjC⟩
      dsimp only [w]
      rw [Prod.snd_sum, Finset.sum_apply, Fintype.sum_eq_single k₀]
      · exact houtsideTermSndSelf k₀
      · intro k hkk₀
        apply houtsideTermSndOther k j hjC
        intro hjk
        apply hkk₀
        apply Subtype.ext
        exact hjk.symm
    let u := v - w
    have huOutside (j : Fin n) (hjC : j ∉ C) : u.1 j = 0 ∧ u.2 j = 0 := by
      constructor
      · simp [u, hwFst j hjC]
      · simp [u, hwSnd j hjC]
    have hfaceLe : FD ≤ D ⊓ LinearMap.ker L := by
      simpa only [FD, D, L, F, P] using
        flowCoverLiftedFaceDirection_le_ambient_inf_supportKer
          a α β b C ⟨q, hqF⟩
    have huCut : u ∈ D ⊓ LinearMap.ker L := by
      exact sub_mem hv (hfaceLe hwMem)
    have hsupportMapsAgree :
        flowCoverLiftedSupportLinearMap a α β b C u =
          flowCoverSupportLinearMap a b C u := by
      rw [flowCoverLiftedSupportLinearMap_apply]
      have houtsideSum :
          ∑ i ∈ Finset.univ \ C, (α i * u.2 i + β i * u.1 i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hiC : i ∉ C := (Finset.mem_sdiff.mp hi).2
        rw [(huOutside i hiC).1, (huOutside i hiC).2]
        ring
      rw [houtsideSum, add_zero]
    have huBaseCut :
        u ∈ D ⊓ LinearMap.ker (flowCoverSupportLinearMap a b C) := by
      refine ⟨huCut.1, ?_⟩
      change flowCoverSupportLinearMap a b C u = 0
      rw [← hsupportMapsAgree]
      exact huCut.2
    have huBaseDirection : u ∈ (affineSpan ℝ F₀).direction := by
      rw [flowCoverFaceDirection_eq_polyDirection_inf_supportKer
        a b C ha_nonneg hC (isCutIndex_exists_gt a C coverOrder hcoverOrder hr)]
      exact huBaseCut
    have huSupported : flowCoverPairProjection C u = u := by
      apply Prod.ext
      · funext j
        by_cases hjC : j ∈ C
        · simp [flowCoverPairProjection, flowCoverCoordinateProjection, hjC]
        · simp [flowCoverPairProjection, flowCoverCoordinateProjection, hjC,
            (huOutside j hjC).1]
      · funext j
        by_cases hjC : j ∈ C
        · simp [flowCoverPairProjection, flowCoverCoordinateProjection, hjC]
        · simp [flowCoverPairProjection, flowCoverCoordinateProjection, hjC,
            (huOutside j hjC).2]
    have huMem : u ∈ FD := by
      exact flowCoverSupportedDirection_mem_liftedFaceDirection
        a α β b C huBaseDirection huSupported
    simpa [u, add_comm] using FD.add_mem hwMem huMem

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the lifted support map has a
normalized ambient direction supported entirely on the cover. -/
theorem flowCoverLiftedSupport_has_coverNormalizedDirection
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    ∃ w ∈ (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction,
      (∀ i, i ∉ C → w.1 i = 0 ∧ w.2 i = 0) ∧
        flowCoverLiftedSupportLinearMap a α β b C w = 1 := by
  classical
  let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
  let L₀ : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := flowCoverSupportLinearMap a b C
  have hbaseCodim :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L₀) + 1 = Module.finrank ℝ ↥D := by
    simpa only [D, L₀] using
      flowCoverSupportKerCodimOne a b C ha_nonneg hC h_excess_lt_some
  have hbaseNonzero : ∃ v ∈ D, L₀ v ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hcutEq : D ⊓ LinearMap.ker L₀ = D := by
      apply le_antisymm inf_le_left
      intro v hv
      exact ⟨hv, hnone v hv⟩
    rw [hcutEq] at hbaseCodim
    omega
  rcases hbaseNonzero with ⟨v, hvD, hvNonzero⟩
  let q := flowCoverPairProjection C v
  have hqD : q ∈ D := by
    exact flowCoverPairProjection_mem_ambientDirection a b C hvD
  have hqOutside (i : Fin n) (hiC : i ∉ C) : q.1 i = 0 ∧ q.2 i = 0 := by
    simp [q, flowCoverPairProjection, flowCoverCoordinateProjection, hiC]
  have hL₀Projection : L₀ q = L₀ v := by
    dsimp [L₀, flowCoverSupportLinearMap]
    apply congrArg₂ (· - ·)
    · apply Finset.sum_congr rfl
      intro i hiC
      simp [q, flowCoverPairProjection, flowCoverCoordinateProjection, hiC]
    · apply Finset.sum_congr rfl
      intro i hiC
      simp [q, flowCoverPairProjection, flowCoverCoordinateProjection, hiC]
  have hLiftedProjection : flowCoverLiftedSupportLinearMap a α β b C q = L₀ q := by
    rw [flowCoverLiftedSupportLinearMap_apply]
    have houtside : ∑ i ∈ Finset.univ \ C, (α i * q.2 i + β i * q.1 i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hiC : i ∉ C := (Finset.mem_sdiff.mp hi).2
      rw [(hqOutside i hiC).1, (hqOutside i hiC).2]
      ring
    rw [houtside, add_zero]
  let w := (L₀ q)⁻¹ • q
  have hwD : w ∈ D := D.smul_mem (L₀ q)⁻¹ hqD
  have hwOutside (i : Fin n) (hiC : i ∉ C) : w.1 i = 0 ∧ w.2 i = 0 := by
    rcases hqOutside i hiC with ⟨hqx, hqy⟩
    simp [w, hqx, hqy]
  have hqNonzero : L₀ q ≠ 0 := by
    rwa [hL₀Projection]
  refine ⟨w, hwD, hwOutside, ?_⟩
  calc
    flowCoverLiftedSupportLinearMap a α β b C w =
        (L₀ q)⁻¹ * flowCoverLiftedSupportLinearMap a α β b C q := by simp [w]
    _ = (L₀ q)⁻¹ * L₀ q := by rw [hLiftedProjection]
    _ = 1 := by field_simp [hqNonzero]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the canonical lifted support
map cuts the ambient single-node-flow direction by one dimension. -/
theorem flowCoverLiftedSupportKerCodimOne
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (h_excess_lt_some : ∃ j ∈ C, flow_cover_excess a b C < a j) :
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
      flowCoverLiftedSupportLinearMap a α β b C
    let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
  dsimp
  rcases flowCoverLiftedSupport_has_coverNormalizedDirection
      a α β b C ha_nonneg hC h_excess_lt_some with ⟨w, hwD, -, hwEval⟩
  exact submodule_finrank_inf_ker_add_one_of_eval_one _ _ hwD hwEval

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: a valid lifted flow-cover
inequality cuts out the exposed face defined by its canonical linear support map. -/
theorem flowCoverLiftedFace_isExposed
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hglobal :
      ∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (single_node_flow_set a b) →
          flow_cover_lifted_value a b C α β p ≤ b) :
    IsExposed ℝ
      (convexHull ℝ (single_node_flow_set a b))
      (flow_cover_lifted_face a b C α β b) := by
  classical
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (single_node_flow_set a b)
  let F : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    flow_cover_lifted_face a b C α β b
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    flowCoverLiftedSupportLinearMap a α β b C
  let δ : ℝ := b - ∑ j ∈ C, flowCoverSupportCoeff a b C j
  have hvalidLinear : ∀ p ∈ P, L p ≤ δ := by
    intro p hp
    have hpValid := hglobal hp
    have hsplit := flow_cover_lifted_value_eq_support_add_constant a α β b C p
    dsimp [L, δ]
    linarith
  have hzeroFacet :=
    zeroLiftingFacetDefining_of_isCutIndex
      a b C coverOrder r ha_nonneg hC hcoverOrder hr
  rcases (isFacetOf_iff.mp hzeroFacet.2).1 with ⟨q₀, hq₀F⟩
  let q := flowCoverPairProjection C q₀
  have hqF : q ∈ F := flowCoverPairProjection_mem_liftedFace a α β b C hq₀F
  have hqP : q ∈ P :=
    (mem_flow_cover_lifted_face_iff a b C α β b q).mp hqF |>.1
  have hqEq : L q = δ := by
    have hqValue := (mem_flow_cover_lifted_face_iff a b C α β b q).mp hqF |>.2
    have hsplit := flow_cover_lifted_value_eq_support_add_constant a α β b C q
    dsimp [L, δ]
    linarith
  have hfaceEq : F = {p | p ∈ P ∧ L p = δ} := by
    ext p
    rw [mem_flow_cover_lifted_face_iff]
    have hsplit := flow_cover_lifted_value_eq_support_add_constant a α β b C p
    dsimp [F, P, L, δ] at *
    constructor
    · rintro ⟨hp, hpEq⟩
      exact ⟨hp, by linarith⟩
    · rintro ⟨hp, hpEq⟩
      exact ⟨hp, by linarith⟩
  have hexposed : IsExposed ℝ P F := by
    rw [hfaceEq, separatorEqualitySet_eq_toExposed_of_mem hvalidLinear hqP hqEq]
    exact ContinuousLinearMap.toExposed.isExposed
  simpa only [P, F] using hexposed

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: under validity, the lifted
equality face is the convex hull of the original single-node-flow points that are tight. -/
theorem flowCoverLiftedFace_eq_convexHull_tightSource
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (hglobal :
      ∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (single_node_flow_set a b) →
          flow_cover_lifted_value a b C α β p ≤ b) :
    flow_cover_lifted_face a b C α β b =
      convexHull ℝ
        {p | p ∈ single_node_flow_set a b ∧
          flow_cover_lifted_value a b C α β p = b} := by
  classical
  let A : Set ((Fin n → ℝ) × (Fin n → ℝ)) := single_node_flow_set a b
  let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
    flowCoverLiftedSupportLinearMap a α β b C
  let δ : ℝ := b - ∑ j ∈ C, flowCoverSupportCoeff a b C j
  have hsource : A ⊆ L ⁻¹' Set.Iic δ := by
    intro p hp
    have hpValid := hglobal (subset_convexHull ℝ A hp)
    have hsplit := flow_cover_lifted_value_eq_support_add_constant a α β b C p
    change L p ≤ δ
    calc
      L p = flow_cover_lifted_value a b C α β p -
          ∑ j ∈ C, flowCoverSupportCoeff a b C j := by linarith
      _ ≤ b - ∑ j ∈ C, flowCoverSupportCoeff a b C j :=
        sub_le_sub_right hpValid _
      _ = δ := by rfl
  have hboundary := convexHull_inter_hyperplane_eq A L δ hsource
  calc
    flow_cover_lifted_face a b C α β b =
        convexHull ℝ A ∩ L ⁻¹' {δ} := by
          ext p
          rw [mem_flow_cover_lifted_face_iff]
          have hsplit := flow_cover_lifted_value_eq_support_add_constant a α β b C p
          dsimp [A, L, δ] at *
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
          constructor
          · rintro ⟨hp, hpEq⟩
            exact ⟨hp, by linarith⟩
          · rintro ⟨hp, hpEq⟩
            exact ⟨hp, by linarith⟩
    _ = convexHull ℝ (A ∩ L ⁻¹' {δ}) := hboundary
    _ = convexHull ℝ
        {p | p ∈ single_node_flow_set a b ∧
          flow_cover_lifted_value a b C α β p = b} := by
          congr 1
          ext p
          have hsplit := flow_cover_lifted_value_eq_support_add_constant a α β b C p
          dsimp [A, L, δ] at *
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
          constructor
          · rintro ⟨hp, hpEq⟩
            exact ⟨hp, by linarith⟩
          · rintro ⟨hp, hpEq⟩
            exact ⟨hp, by linarith⟩

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: any homogeneous linear
equation satisfied by all tight original points also holds on every lifted-face direction. -/
theorem flowCoverLiftedFaceDirection_le_ker_of_tightSource_eq_zero
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (K : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ)
    (hglobal :
      ∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (single_node_flow_set a b) →
          flow_cover_lifted_value a b C α β p ≤ b)
    (hsource :
      ∀ p ∈ single_node_flow_set a b,
        flow_cover_lifted_value a b C α β p = b → K p = 0) :
    (affineSpan ℝ (flow_cover_lifted_face a b C α β b)).direction ≤
      LinearMap.ker K := by
  let S : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    {p | p ∈ single_node_flow_set a b ∧ flow_cover_lifted_value a b C α β p = b}
  have hspanLe :
      affineSpan ℝ (flow_cover_lifted_face a b C α β b) ≤
        (LinearMap.ker K).toAffineSubspace := by
    rw [flowCoverLiftedFace_eq_convexHull_tightSource a α β b C hglobal,
      affineSpan_convexHull]
    rw [affineSpan_le]
    intro p hp
    exact hsource p hp.1 hp.2
  have hdirection := AffineSubspace.direction_le hspanLe
  simpa only [Submodule.toAffineSubspace_direction] using hdirection

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: ordered cover weights are
antitone at positive source positions. -/
lemma flowCoverWeight_antitoneBetween
    (a : Fin n → ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    {h k : ℕ} (hh_pos : 1 ≤ h) (hhk : h ≤ k) (hk_card : k ≤ C.card) :
    weight C a coverOrder k ≤ weight C a coverOrder h := by
  have hh_pred : h - 1 < C.card := by omega
  have hk_pred : k - 1 < C.card := by omega
  have hindices :
      (⟨h - 1, hh_pred⟩ : Fin C.card) ≤ ⟨k - 1, hk_pred⟩ := by
    exact_mod_cast Nat.sub_le_sub_right hhk 1
  have hmono := hordered hindices
  have hh_succ : h - 1 + 1 = h := Nat.sub_add_cancel hh_pos
  have hk_succ : k - 1 + 1 = k := Nat.sub_add_cancel (hh_pos.trans hhk)
  rw [← hh_succ, ← hk_succ]
  simpa only [weight_succ C a coverOrder hh_pred,
    weight_succ C a coverOrder hk_pred] using hmono

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: an ordered prefix difference
dominates its length times the last weight. -/
lemma cardMulWeight_le_partialSum_sub
    (a : Fin n → ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    {k h : ℕ} (hk_pos : 1 ≤ k) (hkh : k ≤ h) (hh_card : h ≤ C.card) :
    ((h - k : ℕ) : ℝ) * weight C a coverOrder h ≤
      partialSum C a coverOrder h - partialSum C a coverOrder k := by
  induction h, hkh using Nat.le_induction with
  | base => simp
  | @succ h hkh ih =>
      have hh_pos : 1 ≤ h := hk_pos.trans hkh
      have hh_card' : h ≤ C.card := by omega
      have hsucc_card : h + 1 ≤ C.card := hh_card
      have hweight_le :
          weight C a coverOrder (h + 1) ≤ weight C a coverOrder h :=
        flowCoverWeight_antitoneBetween a C coverOrder hordered hh_pos
          (Nat.le_succ h) hsucc_card
      have hcast : (((h + 1 - k : ℕ) : ℝ)) = (h - k : ℕ) + 1 := by
        norm_cast
        omega
      rw [partialSum_succ, hcast]
      have hcount_nonneg : 0 ≤ ((h - k : ℕ) : ℝ) := Nat.cast_nonneg _
      have ih' := ih hh_card'
      nlinarith

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: an ordered suffix difference
is bounded by its length times the first weight. -/
lemma partialSum_sub_le_cardMulWeight
    (a : Fin n → ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    {h k : ℕ} (hh_pos : 1 ≤ h) (hhk : h ≤ k) (hk_card : k ≤ C.card) :
    partialSum C a coverOrder k - partialSum C a coverOrder h ≤
      ((k - h : ℕ) : ℝ) * weight C a coverOrder h := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | @succ k hhk ih =>
      have hk_pos : 1 ≤ k := hh_pos.trans hhk
      have hk_card' : k ≤ C.card := by omega
      have hsucc_card : k + 1 ≤ C.card := hk_card
      have hweight_le :
          weight C a coverOrder (k + 1) ≤ weight C a coverOrder h :=
        flowCoverWeight_antitoneBetween a C coverOrder hordered hh_pos
          (hhk.trans (Nat.le_succ k)) hsucc_card
      have hcast : (((k + 1 - h : ℕ) : ℝ)) = (k - h : ℕ) + 1 := by
        norm_cast
        omega
      rw [partialSum_succ, hcast]
      have ih' := ih hk_card'
      nlinarith

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the adjusted prefix values
`μ_h - h λ` are monotone through the cut index. -/
lemma partialSum_sub_cardMulExcess_monoToCutIndex
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {k h : ℕ} (hkh : k ≤ h) (hh : h ≤ r) :
    partialSum C a coverOrder k - (k : ℝ) * flow_cover_excess a b C ≤
      partialSum C a coverOrder h - (h : ℝ) * flow_cover_excess a b C := by
  induction h, hkh using Nat.le_induction with
  | base => exact le_rfl
  | @succ h hkh ih =>
      have hh_cut : h < r := by omega
      have hweight_gt :
          flow_cover_excess a b C < weight C a coverOrder (h + 1) :=
        coverWeight_gt_excess_before_cutIndex
          (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
          hordered hr hh_cut
      have ih' := ih (Nat.le_of_succ_le hh)
      rw [partialSum_succ]
      push_cast
      nlinarith

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: every positive gap-left
breakpoint through the cut index lies in the feasible interval. -/
lemma flowCoverGapLeft_mem_Icc
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h : ℕ} (hh_pos : 1 ≤ h) (hh_cut : h ≤ r) :
    partialSum C a coverOrder h - flow_cover_excess a b C ∈ Set.Icc (0 : ℝ) b := by
  have hfirst_lt :
      flow_cover_excess a b C < weight C a coverOrder 1 :=
    flowCoverExcess_lt_firstOrderedWeight a b C coverOrder r hordered hr
  have hfirst_sum :
      partialSum C a coverOrder 1 = weight C a coverOrder 1 := by
    simp [partialSum]
  have hprefix_lower :
      partialSum C a coverOrder 1 ≤ partialSum C a coverOrder h :=
    partialSum_mono_of_nonneg
      (a := a) (C := C) (coverOrder := coverOrder)
      ha_nonneg hh_pos (hh_cut.trans hr.2.1)
  have hfull :
      partialSum C a coverOrder C.card = b + flow_cover_excess a b C :=
    partialSum_card_eq_rhs_add_excess
      (a := a) (b := b) (C := C) (coverOrder := coverOrder) hcoverOrder
  have hprefix_upper :
      partialSum C a coverOrder h ≤ partialSum C a coverOrder C.card :=
    partialSum_mono_of_nonneg
      (a := a) (C := C) (coverOrder := coverOrder)
      ha_nonneg (hh_cut.trans hr.2.1) le_rfl
  rw [hfirst_sum] at hprefix_lower
  rw [hfull] at hprefix_upper
  constructor <;> linarith

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the lifting profile takes
value `(h - 1) λ` at every positive gap-left breakpoint through the cut index. -/
lemma flowCoverLiftingFunction_evalAtGapLeft
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h : ℕ} (hh_pos : 1 ≤ h) (hh_cut : h ≤ r) :
    flow_cover_lifting_function
        b (flow_cover_excess a b C) (a ∘ coverOrder)
        (partialSum C a coverOrder h - flow_cover_excess a b C) =
      ((h : ℝ) - 1) * flow_cover_excess a b C := by
  have hmem :=
    flowCoverGapLeft_mem_Icc a b C coverOrder r ha_nonneg hcoverOrder hordered hr
      hh_pos hh_cut
  rcases Nat.lt_or_eq_of_le hh_cut with hh_lt | rfl
  · -- Before the cut, use the ordinary affine-gap breakpoint formula.
    exact flowCoverLiftingFunction_evalAtGapLeftBreakpoint
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
      (flow_cover_excess_pos a b C hC) hh_pos hh_lt hmem
  · -- At the cut, use the terminal affine-piece breakpoint formula.
    exact flowCoverLiftingFunction_evalAtFinalBreakpoint
      a b C coverOrder h ha_nonneg hC hcoverOrder hordered hr hmem

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: breakpoint bounds and a cap
bound certify an affine minorant of the capped ordered lifting profile. -/
lemma affine_le_flowCoverProfile_of_breakpointBounds
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {A α β : ℝ} (hA_nonneg : 0 ≤ A) (hA_le : A ≤ b)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hbreak : ∀ h : ℕ, 1 ≤ h → h ≤ r →
      partialSum C a coverOrder h - flow_cover_excess a b C ≤ A →
      α * (partialSum C a coverOrder h - flow_cover_excess a b C) + β ≤
        ((h : ℝ) - 1) * flow_cover_excess a b C)
    (hcap : α * A + β ≤
      flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) A) :
    ∀ z ∈ Set.Icc (0 : ℝ) A,
      α * z + β ≤
        flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z := by
  intro z hz
  have hz_b : z ∈ Set.Icc (0 : ℝ) b := ⟨hz.1, hz.2.trans hA_le⟩
  rcases orderedFlowCoverIntervalPartition
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hz_b with
    hfinal | ⟨h, hh, hgap | hconstant⟩
  · have hnode := hbreak r hr.1 le_rfl (hfinal.1.trans hz.2)
    have hmove :
        α * (z - (partialSum C a coverOrder r - flow_cover_excess a b C)) ≤
          z - (partialSum C a coverOrder r - flow_cover_excess a b C) :=
      mul_le_of_le_one_left (sub_nonneg.mpr hfinal.1) hα_le_one
    have hvalue := flow_cover_lifting_function_eq_affine_on_final_interval
      a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz_b hfinal
    rw [hvalue]
    nlinarith
  · have hh_pos : 1 ≤ h := by
      by_contra hh_zero
      have hh_eq : h = 0 := by omega
      subst h
      simp [partialSum] at hgap
      linarith [hgap.2, hz.1]
    have hnode := hbreak h hh_pos (Nat.le_of_lt hh) (hgap.1.trans hz.2)
    have hmove :
        α * (z - (partialSum C a coverOrder h - flow_cover_excess a b C)) ≤
          z - (partialSum C a coverOrder h - flow_cover_excess a b C) :=
      mul_le_of_le_one_left (sub_nonneg.mpr hgap.1) hα_le_one
    have hvalue := flow_cover_lifting_function_eq_affine_on_gap_intervals
      a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz_b hh_pos hh hgap
    rw [hvalue]
    nlinarith
  · by_cases hnext_cap :
        partialSum C a coverOrder (h + 1) - flow_cover_excess a b C ≤ A
    · have hnode := hbreak (h + 1) (Nat.succ_le_succ (Nat.zero_le h))
          (Nat.succ_le_of_lt hh) hnext_cap
      have hmove :
          α * z ≤
            α * (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C) :=
        mul_le_mul_of_nonneg_left (le_of_lt hconstant.2) hα_nonneg
      have hvalue := flow_cover_lifting_function_eq_constant_on_cover_intervals
        a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz_b hh hconstant
      rw [hvalue]
      norm_num at hnode ⊢
      nlinarith
    · have hA_piece :
          A ∈ Set.Ico
            (partialSum C a coverOrder h)
            (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C) :=
        ⟨hconstant.1.trans hz.2, lt_of_not_ge hnext_cap⟩
      have hA_mem : A ∈ Set.Icc (0 : ℝ) b := ⟨hA_nonneg, hA_le⟩
      have hA_value := flow_cover_lifting_function_eq_constant_on_cover_intervals
        a b C coverOrder r A ha_nonneg hC hcoverOrder hordered hr hA_mem hh hA_piece
      have hmove : α * z ≤ α * A :=
        mul_le_mul_of_nonneg_left hz.2 hα_nonneg
      rw [hA_value] at hcap
      have hvalue := flow_cover_lifting_function_eq_constant_on_cover_intervals
        a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz_b hh hconstant
      rw [hvalue]
      nlinarith [hmove, hcap]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: a family-two secant lies below
every gap-left breakpoint of the ordered lifting profile. -/
lemma familyTwo_le_gapLeftBreakpoint
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r h k : ℕ)
    (hC : IsFlowCover a b C)
    (hordered : Antitone fun j : Fin C.card ↦ a (coverOrder j))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hh_two : 2 ≤ h) (hh_cut : h ≤ r) (hk_pos : 1 ≤ k) (hk_cut : k ≤ r) :
    (flow_cover_excess a b C / weight C a coverOrder h) *
          (partialSum C a coverOrder k - flow_cover_excess a b C) +
        flow_cover_excess a b C *
          (((h - 1 : ℕ) : ℝ) -
            (partialSum C a coverOrder h - flow_cover_excess a b C) /
              weight C a coverOrder h) ≤
      ((k : ℝ) - 1) * flow_cover_excess a b C := by
  have hlam_pos : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
  have hh_pos : 1 ≤ h := by omega
  have hh_pred_cut : h - 1 < r := by omega
  have hweight_gt :
      flow_cover_excess a b C < weight C a coverOrder h := by
    have hweight := coverWeight_gt_excess_before_cutIndex
      (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
      hordered hr hh_pred_cut
    simpa [Nat.sub_add_cancel hh_pos] using hweight
  have hweight_pos : 0 < weight C a coverOrder h := hlam_pos.trans hweight_gt
  have hslope_nonneg :
      0 ≤ flow_cover_excess a b C / weight C a coverOrder h :=
    div_nonneg hlam_pos.le hweight_pos.le
  have hnormalize :
      (flow_cover_excess a b C / weight C a coverOrder h) *
            (partialSum C a coverOrder k - flow_cover_excess a b C) +
          flow_cover_excess a b C *
            (((h - 1 : ℕ) : ℝ) -
              (partialSum C a coverOrder h - flow_cover_excess a b C) /
                weight C a coverOrder h) =
        (((h - 1 : ℕ) : ℝ) * flow_cover_excess a b C) +
          (flow_cover_excess a b C / weight C a coverOrder h) *
            (partialSum C a coverOrder k - partialSum C a coverOrder h) := by
    field_simp
    ring
  rw [hnormalize]
  by_cases hkh : k ≤ h
  · have hgap := cardMulWeight_le_partialSum_sub
      a C coverOrder hordered hk_pos hkh (hh_cut.trans hr.2.1)
    have hgap' :
        partialSum C a coverOrder k - partialSum C a coverOrder h ≤
          -((h - k : ℕ) : ℝ) * weight C a coverOrder h := by
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hgap' hslope_nonneg
    have hcancel :
        (flow_cover_excess a b C / weight C a coverOrder h) *
            weight C a coverOrder h = flow_cover_excess a b C := by
      field_simp
    have hscaled' :
        (flow_cover_excess a b C / weight C a coverOrder h) *
            (partialSum C a coverOrder k - partialSum C a coverOrder h) ≤
          -((h - k : ℕ) : ℝ) * flow_cover_excess a b C := by
      calc
        _ ≤ (flow_cover_excess a b C / weight C a coverOrder h) *
            (-((h - k : ℕ) : ℝ) * weight C a coverOrder h) := hscaled
        _ = -((h - k : ℕ) : ℝ) * flow_cover_excess a b C := by
          calc
            _ = -((h - k : ℕ) : ℝ) *
                ((flow_cover_excess a b C / weight C a coverOrder h) *
                  weight C a coverOrder h) := by ring
            _ = _ := by rw [hcancel]
    have hcast : (((h - 1 : ℕ) : ℝ) - (h - k : ℕ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hh_pos, Nat.cast_sub hkh]
      ring
    nlinarith [hscaled']
  · have hhk : h ≤ k := le_of_not_ge hkh
    have hgap := partialSum_sub_le_cardMulWeight
      a C coverOrder hordered hh_pos hhk (hk_cut.trans hr.2.1)
    have hscaled := mul_le_mul_of_nonneg_left hgap hslope_nonneg
    have hcancel :
        (flow_cover_excess a b C / weight C a coverOrder h) *
            weight C a coverOrder h = flow_cover_excess a b C := by
      field_simp
    have hscaled' :
        (flow_cover_excess a b C / weight C a coverOrder h) *
            (partialSum C a coverOrder k - partialSum C a coverOrder h) ≤
          ((k - h : ℕ) : ℝ) * flow_cover_excess a b C := by
      calc
        _ ≤ (flow_cover_excess a b C / weight C a coverOrder h) *
            (((k - h : ℕ) : ℝ) * weight C a coverOrder h) := hscaled
        _ = ((k - h : ℕ) : ℝ) *
            ((flow_cover_excess a b C / weight C a coverOrder h) *
              weight C a coverOrder h) := by ring
        _ = _ := by rw [hcancel]
    have hcast : (((h - 1 : ℕ) : ℝ) + (k - h : ℕ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hh_pos, Nat.cast_sub hhk]
      ring
    nlinarith [hscaled']

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: every source family-two pair
is a valid affine minorant with its two adjacent gap-left contacts. -/
lemma outsideStepCriterion_of_familyTwo
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (i : Fin n)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hi_pos : 0 < a i)
    (hi_le_b : a i ≤ b)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun j : Fin C.card ↦ a (coverOrder j))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h : ℕ} (hh_two : 2 ≤ h) (hh_cut : h ≤ r)
    (hh_cap : partialSum C a coverOrder h - flow_cover_excess a b C ≤ a i) :
    outsideStepCriterion a b C coverOrder i
      (flow_cover_excess a b C / weight C a coverOrder h)
      (flow_cover_excess a b C *
        (((h - 1 : ℕ) : ℝ) -
          (partialSum C a coverOrder h - flow_cover_excess a b C) /
            weight C a coverOrder h)) := by
  let lam := flow_cover_excess a b C
  let wh := weight C a coverOrder h
  let q : ℕ → ℝ := fun k ↦ partialSum C a coverOrder k - lam
  let slope := lam / wh
  let intercept := lam * (((h - 1 : ℕ) : ℝ) - q h / wh)
  have hb_nonneg : 0 ≤ b := (hi_pos.trans_le hi_le_b).le
  have hlam_pos : 0 < lam := by
    simpa [lam] using flow_cover_excess_pos a b C hC
  have hh_pos : 1 ≤ h := by omega
  have hh_pred_cut : h - 1 < r := by omega
  have hweight_gt : lam < wh := by
    have hweight := coverWeight_gt_excess_before_cutIndex
      (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
      hordered hr hh_pred_cut
    simpa [lam, wh, Nat.sub_add_cancel hh_pos] using hweight
  have hwh_pos : 0 < wh := hlam_pos.trans hweight_gt
  have hslope_nonneg : 0 ≤ slope := div_nonneg hlam_pos.le hwh_pos.le
  have hslope_le_one : slope ≤ 1 := (div_le_one hwh_pos).2 hweight_gt.le
  have hbreak : ∀ k : ℕ, 1 ≤ k → k ≤ r → q k ≤ b →
      slope * q k + intercept ≤ ((k : ℝ) - 1) * lam := by
    intro k hk_pos hk_cut hk_b
    simpa [lam, wh, q, slope, intercept] using
      familyTwo_le_gapLeftBreakpoint
        a b C coverOrder r h k hC hordered hr hh_two hh_cut hk_pos hk_cut
  have hqr_mem : q r ∈ Set.Icc (0 : ℝ) b := by
    simpa [lam, q] using
      flowCoverGapLeft_mem_Icc
        a b C coverOrder r ha_nonneg hcoverOrder hordered hr hr.1 le_rfl
  have hnode_r := hbreak r hr.1 le_rfl hqr_mem.2
  have hmove : slope * (b - q r) ≤ b - q r :=
    mul_le_of_le_one_left (sub_nonneg.mpr hqr_mem.2) hslope_le_one
  have hb_value := flow_cover_lifting_function_eq_affine_on_final_interval
    a b C coverOrder r b ha_nonneg hC hcoverOrder hordered hr
      ⟨hb_nonneg, le_rfl⟩ ⟨hqr_mem.2, le_rfl⟩
  have hcap : slope * b + intercept ≤
      flow_cover_lifting_function b lam (a ∘ coverOrder) b := by
    rw [hb_value]
    dsimp [lam, q] at hnode_r hmove ⊢
    nlinarith
  have hvalid : ∀ z ∈ Set.Icc (0 : ℝ) (a i),
      slope * z + intercept ≤
        flow_cover_lifting_function b lam (a ∘ coverOrder) z := by
    intro z hz
    exact affine_le_flowCoverProfile_of_breakpointBounds
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
      hb_nonneg le_rfl hslope_nonneg hslope_le_one hbreak hcap z
      ⟨hz.1, hz.2.trans hi_le_b⟩
  have hprev_pos : 1 ≤ h - 1 := by omega
  have hprev_cut : h - 1 ≤ r := by omega
  have hqprev_mem : q (h - 1) ∈ Set.Icc (0 : ℝ) b := by
    simpa [lam, q] using
      flowCoverGapLeft_mem_Icc
        a b C coverOrder r ha_nonneg hcoverOrder hordered hr hprev_pos hprev_cut
  have hqh_mem : q h ∈ Set.Icc (0 : ℝ) b := by
    simpa [lam, q] using
      flowCoverGapLeft_mem_Icc
        a b C coverOrder r ha_nonneg hcoverOrder hordered hr hh_pos hh_cut
  have hsum : partialSum C a coverOrder h =
      partialSum C a coverOrder (h - 1) + wh := by
    have hsum' := partialSum_succ C a coverOrder (h - 1)
    simpa [wh, Nat.sub_add_cancel hh_pos] using hsum'
  have hq_lt : q (h - 1) < q h := by
    dsimp [q]
    linarith
  have hqprev_cap : q (h - 1) ≤ a i := (le_of_lt hq_lt).trans hh_cap
  have hprev_value := flowCoverLiftingFunction_evalAtGapLeft
    a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hprev_pos hprev_cut
  have hh_value := flowCoverLiftingFunction_evalAtGapLeft
    a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hh_pos hh_cut
  have hline_h : slope * q h + intercept = ((h : ℝ) - 1) * lam := by
    dsimp [slope, intercept]
    rw [Nat.cast_sub hh_pos]
    field_simp [ne_of_gt hwh_pos]
    ring
  have hline_prev :
      slope * q (h - 1) + intercept = (((h - 1 : ℕ) : ℝ) - 1) * lam := by
    have hqdiff : q h - q (h - 1) = wh := by
      dsimp [q]
      linarith
    have hslope_weight : slope * wh = lam := by
      dsimp [slope]
      field_simp [ne_of_gt hwh_pos]
    calc
      slope * q (h - 1) + intercept =
          slope * q h + intercept - slope * wh := by
        rw [← hqdiff]
        ring
      _ = ((h : ℝ) - 1) * lam - lam := by rw [hline_h, hslope_weight]
      _ = (((h - 1 : ℕ) : ℝ) - 1) * lam := by
        rw [Nat.cast_sub hh_pos]
        ring
  dsimp [outsideStepCriterion]
  refine ⟨?_, q (h - 1), ?_, q h, ?_, ne_of_lt hq_lt, ?_, ?_⟩
  · simpa [slope, intercept, lam, wh, q] using hvalid
  · exact ⟨hqprev_mem.1, hqprev_cap⟩
  · exact ⟨hqh_mem.1, hh_cap⟩
  · rw [hline_prev]
    simpa [lam, q] using hprev_value.symm
  · rw [hline_h]
    simpa [lam, q] using hh_value.symm

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: every source family-three
pair is the active slope-one piece ending at the outside capacity. -/
lemma outsideStepCriterion_of_familyThree
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (i : Fin n)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hi_pos : 0 < a i)
    (hi_le_b : a i ≤ b)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun j : Fin C.card ↦ a (coverOrder j))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {ell : ℕ}
    (hleft : partialSum C a coverOrder ell - flow_cover_excess a b C < a i)
    (hell : ell = r ∨ ell < r ∧ a i ≤ partialSum C a coverOrder ell) :
    outsideStepCriterion a b C coverOrder i 1
      ((ell : ℝ) * flow_cover_excess a b C - partialSum C a coverOrder ell) := by
  let lam := flow_cover_excess a b C
  let q : ℕ → ℝ := fun k ↦ partialSum C a coverOrder k - lam
  let intercept := (ell : ℝ) * lam - partialSum C a coverOrder ell
  have hell_pos : 1 ≤ ell := by
    rcases hell with rfl | ⟨hell_cut, hA_mu⟩
    · exact hr.1
    · by_contra hell_zero
      have hell_eq : ell = 0 := by omega
      subst ell
      simp [partialSum] at hA_mu
      linarith
  have hell_cut : ell ≤ r := by
    rcases hell with rfl | ⟨hell_lt, -⟩
    · exact le_rfl
    · exact Nat.le_of_lt hell_lt
  have hbreak : ∀ k : ℕ, 1 ≤ k → k ≤ r → q k ≤ a i →
      q k + intercept ≤ ((k : ℝ) - 1) * lam := by
    intro k hk_pos hk_cut hk_cap
    have hk_ell : k ≤ ell := by
      rcases hell with rfl | ⟨hell_lt, hA_mu⟩
      · exact hk_cut
      · by_contra hk_not
        have hell_succ_k : ell + 1 ≤ k := by omega
        have hweight_gt := coverWeight_gt_excess_before_cutIndex
          (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
          hordered hr hell_lt
        have hprefix := partialSum_mono_of_nonneg
          (a := a) (C := C) (coverOrder := coverOrder)
          ha_nonneg hell_succ_k (hk_cut.trans hr.2.1)
        rw [partialSum_succ] at hprefix
        dsimp [q, lam] at hk_cap
        linarith
    have hpref := partialSum_sub_cardMulExcess_monoToCutIndex
      a b C coverOrder r hordered hr hk_ell hell_cut
    dsimp [q, intercept, lam]
    nlinarith
  have hq_mem : q ell ∈ Set.Icc (0 : ℝ) b := by
    simpa [q, lam] using
      flowCoverGapLeft_mem_Icc
        a b C coverOrder r ha_nonneg hcoverOrder hordered hr hell_pos hell_cut
  have hA_mem : a i ∈ Set.Icc (0 : ℝ) b := ⟨hi_pos.le, hi_le_b⟩
  have hA_value :
      flow_cover_lifting_function b lam (a ∘ coverOrder) (a i) = a i + intercept := by
    rcases hell with rfl | ⟨hell_lt, hA_mu⟩
    · have hfinal : a i ∈ Set.Icc (q ell) b := ⟨le_of_lt hleft, hi_le_b⟩
      have hvalue := flow_cover_lifting_function_eq_affine_on_final_interval
        a b C coverOrder ell (a i) ha_nonneg hC hcoverOrder hordered hr hA_mem
          (by simpa [q, lam] using hfinal)
      convert hvalue using 1
      simp [intercept, lam]
      ring
    · by_cases hA_lt : a i < partialSum C a coverOrder ell
      · have hpiece : a i ∈ Set.Ico (q ell) (partialSum C a coverOrder ell) :=
          ⟨le_of_lt hleft, hA_lt⟩
        have hvalue := flow_cover_lifting_function_eq_affine_on_gap_intervals
          a b C coverOrder r (a i) ha_nonneg hC hcoverOrder hordered hr hA_mem
            hell_pos hell_lt (by simpa [q, lam] using hpiece)
        convert hvalue using 1
        simp [intercept, lam]
        ring
      · have hA_eq : a i = partialSum C a coverOrder ell :=
          le_antisymm hA_mu (le_of_not_gt hA_lt)
        have hweight_gt := coverWeight_gt_excess_before_cutIndex
          (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
          hordered hr hell_lt
        have hpiece : a i ∈ Set.Ico
            (partialSum C a coverOrder ell)
            (partialSum C a coverOrder (ell + 1) - lam) := by
          rw [hA_eq, partialSum_succ]
          exact ⟨le_rfl, by linarith⟩
        have hvalue := flow_cover_lifting_function_eq_constant_on_cover_intervals
          a b C coverOrder r (a i) ha_nonneg hC hcoverOrder hordered hr hA_mem
            hell_lt (by simpa [lam] using hpiece)
        rw [hA_eq] at hvalue ⊢
        simpa [intercept, lam] using hvalue
  have hvalid : ∀ z ∈ Set.Icc (0 : ℝ) (a i),
      z + intercept ≤
        flow_cover_lifting_function b lam (a ∘ coverOrder) z := by
    have hvalid' := affine_le_flowCoverProfile_of_breakpointBounds
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
      (A := a i) (α := 1) (β := intercept)
      hi_pos.le hi_le_b (by norm_num) (by norm_num)
      (fun k hk_pos hk_cut hk_cap ↦ by
        norm_num
        exact hbreak k hk_pos hk_cut hk_cap)
      (by nlinarith [hA_value])
    intro z hz
    simpa [lam] using hvalid' z hz
  have hq_value := flowCoverLiftingFunction_evalAtGapLeft
    a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hell_pos hell_cut
  have hline_q : q ell + intercept = ((ell : ℝ) - 1) * lam := by
    dsimp [q, intercept]
    ring
  dsimp [outsideStepCriterion]
  refine ⟨?_, q ell, ?_, a i, ⟨hi_pos.le, le_rfl⟩, ne_of_lt hleft, ?_, ?_⟩
  · simpa [intercept, lam] using hvalid
  · exact ⟨hq_mem.1, le_of_lt hleft⟩
  · norm_num
    rw [hline_q]
    simpa [q, lam] using hq_value.symm
  · simpa [intercept, lam] using hA_value.symm

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: every source family-four
pair is the terminal secant from a gap-left breakpoint to the capped endpoint. -/
lemma outsideStepCriterion_of_familyFour
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (i : Fin n)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hi_pos : 0 < a i)
    (hi_le_b : a i ≤ b)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun j : Fin C.card ↦ a (coverOrder j))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {ell : ℕ} (hell_pos : 1 ≤ ell) (hell_cut : ell < r)
    (hmu_lt : partialSum C a coverOrder ell < a i)
    (hcap_next :
      a i ≤ partialSum C a coverOrder (ell + 1) - flow_cover_excess a b C) :
    outsideStepCriterion a b C coverOrder i
      (flow_cover_excess a b C /
        (a i + flow_cover_excess a b C - partialSum C a coverOrder ell))
      ((ell : ℝ) * flow_cover_excess a b C -
        (flow_cover_excess a b C * a i) /
          (a i + flow_cover_excess a b C - partialSum C a coverOrder ell)) := by
  let lam := flow_cover_excess a b C
  let q : ℕ → ℝ := fun k ↦ partialSum C a coverOrder k - lam
  let d := a i + lam - partialSum C a coverOrder ell
  let slope := lam / d
  let intercept := (ell : ℝ) * lam - slope * a i
  have hlam_pos : 0 < lam := by
    simpa [lam] using flow_cover_excess_pos a b C hC
  have hd_gt_lam : lam < d := by
    dsimp [d, lam]
    linarith
  have hd_pos : 0 < d := hlam_pos.trans hd_gt_lam
  have hslope_nonneg : 0 ≤ slope := div_nonneg hlam_pos.le hd_pos.le
  have hslope_le_one : slope ≤ 1 := (div_le_one hd_pos).2 hd_gt_lam.le
  have hnext_cut : ell + 1 ≤ r := Nat.succ_le_of_lt hell_cut
  have hnext_card : ell + 1 ≤ C.card := hnext_cut.trans hr.2.1
  have hd_le_nextWeight : d ≤ weight C a coverOrder (ell + 1) := by
    dsimp [d, lam]
    rw [partialSum_succ] at hcap_next
    linarith
  have hbreak : ∀ k : ℕ, 1 ≤ k → k ≤ r → q k ≤ a i →
      slope * q k + intercept ≤ ((k : ℝ) - 1) * lam := by
    intro k hk_pos hk_cut hk_cap
    by_cases hkell : k ≤ ell
    · have hell_card : ell ≤ C.card := (Nat.le_of_lt hell_cut).trans hr.2.1
      have hsum := cardMulWeight_le_partialSum_sub
        a C coverOrder hordered hk_pos hkell hell_card
      have hweight_order :
          weight C a coverOrder (ell + 1) ≤ weight C a coverOrder ell :=
        flowCoverWeight_antitoneBetween a C coverOrder hordered hell_pos
          (Nat.le_succ ell) hnext_card
      have hd_le_weight : d ≤ weight C a coverOrder ell :=
        hd_le_nextWeight.trans hweight_order
      have hcount_nonneg : 0 ≤ (((ell - k : ℕ) : ℝ)) := Nat.cast_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hd_le_weight hcount_nonneg
      have hgap :
          ((ell - k : ℕ) : ℝ) * d ≤
            partialSum C a coverOrder ell - partialSum C a coverOrder k :=
        hmul.trans hsum
      have hgap' :
          partialSum C a coverOrder k - partialSum C a coverOrder ell ≤
            -((ell - k : ℕ) : ℝ) * d := by
        linarith
      have hscaled := mul_le_mul_of_nonneg_left hgap' hslope_nonneg
      have hcancel : slope * d = lam := by
        dsimp [slope]
        field_simp [ne_of_gt hd_pos]
      have hscaled' :
          slope * (partialSum C a coverOrder k - partialSum C a coverOrder ell) ≤
            -((ell - k : ℕ) : ℝ) * lam := by
        calc
          _ ≤ slope * (-((ell - k : ℕ) : ℝ) * d) := hscaled
          _ = -((ell - k : ℕ) : ℝ) * (slope * d) := by ring
          _ = _ := by rw [hcancel]
      have hnormalize :
          slope * q k + intercept =
            (ell : ℝ) * lam - lam +
              slope * (partialSum C a coverOrder k - partialSum C a coverOrder ell) := by
        calc
          slope * q k + intercept =
              (ell : ℝ) * lam +
                slope * (partialSum C a coverOrder k - lam - a i) := by
            dsimp [q, intercept]
            ring
          _ = (ell : ℝ) * lam - slope * d +
                slope * (partialSum C a coverOrder k - partialSum C a coverOrder ell) := by
            dsimp [d]
            ring
          _ = _ := by rw [hcancel]
      have hcast :
          (ell : ℝ) - 1 - (ell - k : ℕ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hkell]
        ring
      rw [hnormalize]
      nlinarith [hscaled']
    · have hell_lt_k : ell < k := lt_of_not_ge hkell
      have hk_eq : k = ell + 1 := by
        by_contra hk_ne
        have hell_succ_lt_k : ell + 1 < k := by omega
        have hk_pred_cut : k - 1 < r := by omega
        have hweight_gt' := coverWeight_gt_excess_before_cutIndex
          (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
          hordered hr hk_pred_cut
        have hweight_gt : lam < weight C a coverOrder k := by
          simpa [lam, Nat.sub_add_cancel hk_pos] using hweight_gt'
        have hsum := cardMulWeight_le_partialSum_sub
          a C coverOrder hordered (Nat.succ_le_succ (Nat.zero_le ell))
            (Nat.le_of_lt hell_succ_lt_k) (hk_cut.trans hr.2.1)
        have hcount_pos : 0 < (((k - (ell + 1) : ℕ) : ℝ)) := by
          exact_mod_cast Nat.sub_pos_of_lt hell_succ_lt_k
        dsimp [q, lam] at hk_cap hcap_next
        have hweight_pos : 0 < weight C a coverOrder k := hlam_pos.trans hweight_gt
        nlinarith
      subst k
      have hq_eq : q (ell + 1) = a i := le_antisymm hk_cap (by
        simpa [q, lam] using hcap_next)
      rw [hq_eq]
      dsimp [intercept]
      push_cast
      ring_nf
      exact le_rfl
  have hA_mem : a i ∈ Set.Icc (0 : ℝ) b := ⟨hi_pos.le, hi_le_b⟩
  have hA_value :
      flow_cover_lifting_function b lam (a ∘ coverOrder) (a i) =
        (ell : ℝ) * lam := by
    by_cases hcap_strict : a i < q (ell + 1)
    · have hpiece : a i ∈ Set.Ico
          (partialSum C a coverOrder ell)
          (partialSum C a coverOrder (ell + 1) - flow_cover_excess a b C) := by
        exact ⟨hmu_lt.le, by simpa [q, lam] using hcap_strict⟩
      exact flow_cover_lifting_function_eq_constant_on_cover_intervals
        a b C coverOrder r (a i) ha_nonneg hC hcoverOrder hordered hr hA_mem
          hell_cut hpiece
    · have hA_eq : a i = q (ell + 1) :=
        le_antisymm hcap_next (le_of_not_gt hcap_strict)
      have hnext_value := flowCoverLiftingFunction_evalAtGapLeft
        a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
          (Nat.succ_le_succ (Nat.zero_le ell)) hnext_cut
      rw [hA_eq]
      simpa [q, lam] using hnext_value
  have hline_A : slope * a i + intercept = (ell : ℝ) * lam := by
    dsimp [intercept]
    ring
  have hvalid : ∀ z ∈ Set.Icc (0 : ℝ) (a i),
      slope * z + intercept ≤
        flow_cover_lifting_function b lam (a ∘ coverOrder) z := by
    exact affine_le_flowCoverProfile_of_breakpointBounds
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
      (A := a i) (α := slope) (β := intercept)
      hi_pos.le hi_le_b hslope_nonneg hslope_le_one hbreak
      (by rw [hline_A, hA_value])
  have hq_mem : q ell ∈ Set.Icc (0 : ℝ) b := by
    simpa [q, lam] using flowCoverGapLeft_mem_Icc
      a b C coverOrder r ha_nonneg hcoverOrder hordered hr hell_pos
        (Nat.le_of_lt hell_cut)
  have hq_value := flowCoverLiftingFunction_evalAtGapLeft
    a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hell_pos
      (Nat.le_of_lt hell_cut)
  have hq_lt_A : q ell < a i := by
    dsimp [q, lam]
    linarith
  have hline_q : slope * q ell + intercept = ((ell : ℝ) - 1) * lam := by
    have hqdiff : a i - q ell = d := by
      dsimp [q, d]
      ring
    have hslope_d : slope * d = lam := by
      dsimp [slope]
      field_simp [ne_of_gt hd_pos]
    dsimp [intercept]
    rw [← hqdiff] at hslope_d
    nlinarith
  have hintercept_eq :
      (ell : ℝ) * flow_cover_excess a b C -
          (flow_cover_excess a b C * a i) /
            (a i + flow_cover_excess a b C - partialSum C a coverOrder ell) =
        intercept := by
    dsimp [intercept, slope, d, lam]
    ring
  dsimp [outsideStepCriterion]
  refine ⟨?_, q ell, ?_, a i, ⟨hi_pos.le, le_rfl⟩, ne_of_lt hq_lt_A, ?_, ?_⟩
  · intro z hz
    rw [hintercept_eq]
    simpa [slope, lam, d] using hvalid z hz
  · exact ⟨hq_mem.1, le_of_lt hq_lt_A⟩
  · rw [hintercept_eq, hline_q]
    simpa [q, lam] using hq_value.symm
  · rw [hintercept_eq, hline_A]
    simpa [lam] using hA_value.symm

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: a valid slope-one gap line
cannot extend beyond the right endpoint of that gap. -/
lemma cap_le_coverBreakpoint_of_slopeOneValid
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r h : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun j : Fin C.card ↦ a (coverOrder j))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {A : ℝ} (hA_nonneg : 0 ≤ A) (hA_le : A ≤ b) (hh : h < r)
    (hvalid : ∀ z ∈ Set.Icc (0 : ℝ) A,
      z + ((h : ℝ) * flow_cover_excess a b C - partialSum C a coverOrder h) ≤
        flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z) :
    A ≤ partialSum C a coverOrder h := by
  by_contra hA_not
  have hmu_lt : partialSum C a coverOrder h < A := lt_of_not_ge hA_not
  have hweight_gt := coverWeight_gt_excess_before_cutIndex
    (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
    hordered hr hh
  by_cases hA_next :
      A < partialSum C a coverOrder (h + 1) - flow_cover_excess a b C
  · have hA_piece : A ∈ Set.Ico
        (partialSum C a coverOrder h)
        (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C) :=
      ⟨hmu_lt.le, hA_next⟩
    have hA_value := flow_cover_lifting_function_eq_constant_on_cover_intervals
      a b C coverOrder r A ha_nonneg hC hcoverOrder hordered hr
        ⟨hA_nonneg, hA_le⟩ hh hA_piece
    have hbound := hvalid A ⟨hA_nonneg, le_rfl⟩
    rw [hA_value] at hbound
    linarith
  · let qnext := partialSum C a coverOrder (h + 1) - flow_cover_excess a b C
    have hqnext_le : qnext ≤ A := le_of_not_gt hA_next
    have hqnext_mem := flowCoverGapLeft_mem_Icc
      a b C coverOrder r ha_nonneg hcoverOrder hordered hr
        (Nat.succ_le_succ (Nat.zero_le h)) (Nat.succ_le_of_lt hh)
    have hqnext_value := flowCoverLiftingFunction_evalAtGapLeft
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
        (Nat.succ_le_succ (Nat.zero_le h)) (Nat.succ_le_of_lt hh)
    have hbound := hvalid qnext ⟨hqnext_mem.1, hqnext_le⟩
    dsimp [qnext] at hbound
    rw [hqnext_value] at hbound
    rw [partialSum_succ] at hbound
    push_cast at hbound
    linarith

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the affine gap formula remains
valid at the closed right endpoint. -/
lemma flowCoverLiftingFunction_eq_on_gapClosure
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r h : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun j : Fin C.card ↦ a (coverOrder j))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hh_pos : 1 ≤ h) (hh : h < r)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b)
    (hz_gap : z ∈ Set.Icc
      (partialSum C a coverOrder h - flow_cover_excess a b C)
      (partialSum C a coverOrder h)) :
    flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
      z - partialSum C a coverOrder h + (h : ℝ) * flow_cover_excess a b C := by
  by_cases hz_lt : z < partialSum C a coverOrder h
  · exact flow_cover_lifting_function_eq_affine_on_gap_intervals
      a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz hh_pos hh
        ⟨hz_gap.1, hz_lt⟩
  · have hz_eq : z = partialSum C a coverOrder h :=
      le_antisymm hz_gap.2 (le_of_not_gt hz_lt)
    have hweight_gt := coverWeight_gt_excess_before_cutIndex
      (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
      hordered hr hh
    have hz_piece : z ∈ Set.Ico
        (partialSum C a coverOrder h)
        (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C) := by
      rw [hz_eq, partialSum_succ]
      exact ⟨le_rfl, by linarith⟩
    have hvalue := flow_cover_lifting_function_eq_constant_on_cover_intervals
      a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz hh hz_piece
    rw [hz_eq] at hvalue ⊢
    simpa using hvalue

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: the constant-piece formula
remains valid at its gap-left right endpoint. -/
lemma flowCoverLiftingFunction_eq_on_constantClosure
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r h : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun j : Fin C.card ↦ a (coverOrder j))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hh : h < r)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b)
    (hz_constant : z ∈ Set.Icc
      (partialSum C a coverOrder h)
      (partialSum C a coverOrder (h + 1) - flow_cover_excess a b C)) :
    flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
      (h : ℝ) * flow_cover_excess a b C := by
  by_cases hz_lt : z < partialSum C a coverOrder (h + 1) - flow_cover_excess a b C
  · exact flow_cover_lifting_function_eq_constant_on_cover_intervals
      a b C coverOrder r z ha_nonneg hC hcoverOrder hordered hr hz hh
        ⟨hz_constant.1, hz_lt⟩
  · have hz_eq : z = partialSum C a coverOrder (h + 1) - flow_cover_excess a b C :=
      le_antisymm hz_constant.2 (le_of_not_gt hz_lt)
    have hnext_value := flowCoverLiftingFunction_evalAtGapLeft
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
        (Nat.succ_le_succ (Nat.zero_le h)) (Nat.succ_le_of_lt hh)
    rw [hz_eq]
    simpa using hnext_value

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean`: two ordered contacts of a valid
affine minorant determine one of the four source coefficient families. -/
lemma admissiblePair_of_orderedContacts
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (i : Fin n)
    (α β u v : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hi_pos : 0 < a i)
    (hi_le_b : a i ≤ b)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun j : Fin C.card ↦ a (coverOrder j))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hvalid : ∀ z ∈ Set.Icc (0 : ℝ) (a i),
      α * z + β ≤
        flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z)
    (hu : u ∈ Set.Icc (0 : ℝ) (a i))
    (hv : v ∈ Set.Icc (0 : ℝ) (a i))
    (huv : u < v)
    (hu_contact : α * u + β =
      flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) u)
    (hv_contact : α * v + β =
      flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) v) :
    OrderedFlowCover.admissiblePair a b C coverOrder r i α β := by
  let lam := flow_cover_excess a b C
  let q : ℕ → ℝ := fun k ↦ partialSum C a coverOrder k - lam
  have hlam_pos : 0 < lam := by
    simpa [lam] using flow_cover_excess_pos a b C hC
  have hu_b : u ∈ Set.Icc (0 : ℝ) b := ⟨hu.1, hu.2.trans hi_le_b⟩
  have hv_b : v ∈ Set.Icc (0 : ℝ) b := ⟨hv.1, hv.2.trans hi_le_b⟩
  rcases orderedFlowCoverIntervalPartition
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hu_b with
    hfinal | ⟨h, hh, hgap | hconstant⟩
  · -- Two contacts after the final breakpoint determine the terminal slope-one family.
    have hv_final : v ∈ Set.Icc (q r) b := ⟨hfinal.1.trans (le_of_lt huv), hv_b.2⟩
    have hu_value := flow_cover_lifting_function_eq_affine_on_final_interval
      a b C coverOrder r u ha_nonneg hC hcoverOrder hordered hr hu_b
        (by simpa [q, lam] using hfinal)
    have hv_value := flow_cover_lifting_function_eq_affine_on_final_interval
      a b C coverOrder r v ha_nonneg hC hcoverOrder hordered hr hv_b
        (by simpa [q, lam] using hv_final)
    have hα : α = 1 := by
      rw [hu_value] at hu_contact
      rw [hv_value] at hv_contact
      nlinarith
    have hβ : β = (r : ℝ) * lam - partialSum C a coverOrder r := by
      rw [hu_value, hα] at hu_contact
      linarith
    unfold OrderedFlowCover.admissiblePair
    exact Or.inr (Or.inr (Or.inl ⟨r, by linarith [hfinal.1, huv, hv.2], Or.inl rfl,
      hα, by simpa [lam] using hβ⟩))
  · have hh_pos : 1 ≤ h := by
      by_contra hh_zero
      have hh_eq : h = 0 := by omega
      subst h
      simp [partialSum] at hgap
      linarith [hgap.2, hu.1]
    have hq_mem := flowCoverGapLeft_mem_Icc
      a b C coverOrder r ha_nonneg hcoverOrder hordered hr hh_pos (Nat.le_of_lt hh)
    have hq_value := flowCoverLiftingFunction_evalAtGapLeft
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hh_pos (Nat.le_of_lt hh)
    have hu_value := flow_cover_lifting_function_eq_affine_on_gap_intervals
      a b C coverOrder r u ha_nonneg hC hcoverOrder hordered hr hu_b hh_pos hh hgap
    by_cases hu_left : u = q h
    · subst u
      by_cases hv_mu : v ≤ partialSum C a coverOrder h
      · have hv_value := flowCoverLiftingFunction_eq_on_gapClosure
          a b C coverOrder r h ha_nonneg hC hcoverOrder hordered hr hh_pos hh hv_b
            ⟨by simpa [q, lam] using le_of_lt huv, hv_mu⟩
        have hα : α = 1 := by
          rw [hq_value] at hu_contact
          rw [hv_value] at hv_contact
          dsimp [q, lam] at hu_contact huv
          nlinarith
        have hβ : β = (h : ℝ) * lam - partialSum C a coverOrder h := by
          rw [hα] at hu_contact
          rw [hq_value] at hu_contact
          dsimp [q, lam] at hu_contact
          linarith
        have hcap_le := cap_le_coverBreakpoint_of_slopeOneValid
          a b C coverOrder r h ha_nonneg hC hcoverOrder hordered hr
            hi_pos.le hi_le_b hh (by
              intro z hz
              simpa [hα, hβ, lam] using hvalid z hz)
        unfold OrderedFlowCover.admissiblePair
        exact Or.inr (Or.inr (Or.inl ⟨h, huv.trans_le hv.2,
          Or.inr ⟨hh, hcap_le⟩, hα, by simpa [lam] using hβ⟩))
      · have hmu_lt_v : partialSum C a coverOrder h < v := lt_of_not_ge hv_mu
        let qnext := q (h + 1)
        by_cases hv_next : v < qnext
        · have hv_value := flowCoverLiftingFunction_eq_on_constantClosure
            a b C coverOrder r h ha_nonneg hC hcoverOrder hordered hr hh hv_b
              ⟨hmu_lt_v.le, le_of_lt hv_next⟩
          have hα_pos : 0 < α := by
            rw [hq_value] at hu_contact
            rw [hv_value] at hv_contact
            dsimp [q, lam] at hu_contact huv
            nlinarith
          have hA_eq : a i = v := by
            apply le_antisymm
            · by_contra hA_not
              have hv_A : v < a i := lt_of_not_ge hA_not
              by_cases hA_next : a i < qnext
              · have hA_value := flowCoverLiftingFunction_eq_on_constantClosure
                  a b C coverOrder r h ha_nonneg hC hcoverOrder hordered hr hh
                    ⟨hi_pos.le, hi_le_b⟩ ⟨hmu_lt_v.le.trans (le_of_lt hv_A), le_of_lt hA_next⟩
                have hA_bound := hvalid (a i) ⟨hi_pos.le, le_rfl⟩
                rw [hA_value] at hA_bound
                rw [hv_value] at hv_contact
                nlinarith
              · have hqnext_le : qnext ≤ a i := le_of_not_gt hA_next
                have hqnext_mem := flowCoverGapLeft_mem_Icc
                  a b C coverOrder r ha_nonneg hcoverOrder hordered hr
                    (Nat.succ_le_succ (Nat.zero_le h)) (Nat.succ_le_of_lt hh)
                have hqnext_value := flowCoverLiftingFunction_evalAtGapLeft
                  a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
                    (Nat.succ_le_succ (Nat.zero_le h)) (Nat.succ_le_of_lt hh)
                have hqnext_bound := hvalid qnext ⟨hqnext_mem.1, hqnext_le⟩
                rw [hqnext_value] at hqnext_bound
                push_cast at hqnext_bound
                rw [hv_value] at hv_contact
                dsimp [qnext, q, lam] at hqnext_bound hv_next
                nlinarith
            · exact hv.2
          have hden_pos :
              0 < a i + lam - partialSum C a coverOrder h := by
            rw [hA_eq]
            dsimp [q, lam] at huv
            linarith
          have hu_contact' :
              α * (partialSum C a coverOrder h - lam) + β =
                ((h : ℝ) - 1) * lam := by
            simpa [q, lam] using hu_contact.trans hq_value
          have hv_contact' : α * a i + β = (h : ℝ) * lam := by
            calc
              α * a i + β = α * v + β := by rw [hA_eq]
              _ = flow_cover_lifting_function b
                  (flow_cover_excess a b C) (a ∘ coverOrder) v := hv_contact
              _ = (h : ℝ) * lam := by simpa [lam] using hv_value
          have hα : α = lam / (a i + lam - partialSum C a coverOrder h) := by
            apply (eq_div_iff (ne_of_gt hden_pos)).2
            nlinarith only [hu_contact', hv_contact']
          have hβ : β = (h : ℝ) * lam -
              (lam * a i) / (a i + lam - partialSum C a coverOrder h) := by
            calc
              β = (h : ℝ) * lam -
                  (lam / (a i + lam - partialSum C a coverOrder h)) * a i := by
                rw [← hα]
                linarith only [hv_contact']
              _ = (h : ℝ) * lam -
                  (lam * a i) / (a i + lam - partialSum C a coverOrder h) := by ring
          unfold OrderedFlowCover.admissiblePair
          exact Or.inr (Or.inr (Or.inr ⟨h, hh_pos, hh, hmu_lt_v.trans_eq hA_eq.symm,
            by simpa [q, lam, hA_eq] using le_of_lt hv_next, hα, by simpa [lam] using hβ⟩))
        · have hqnext_le_v : qnext ≤ v := le_of_not_gt hv_next
          have hqnext_cap : qnext ≤ a i := hqnext_le_v.trans hv.2
          have hedge := outsideStepCriterion_of_familyTwo
            a b C coverOrder r i ha_nonneg hi_pos hi_le_b hC hcoverOrder hordered hr
              (h := h + 1) (by omega) (Nat.succ_le_of_lt hh)
              (by simpa [qnext, q, lam] using hqnext_cap)
          have hedge_valid := hedge.1
          let slope := lam / weight C a coverOrder (h + 1)
          let intercept := lam * ((h : ℝ) - qnext / weight C a coverOrder (h + 1))
          have hweight_gt := coverWeight_gt_excess_before_cutIndex
            (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
            hordered hr hh
          have hweight_pos : 0 < weight C a coverOrder (h + 1) := hlam_pos.trans hweight_gt
          have hqnext_mem := flowCoverGapLeft_mem_Icc
            a b C coverOrder r ha_nonneg hcoverOrder hordered hr
              (Nat.succ_le_succ (Nat.zero_le h)) (Nat.succ_le_of_lt hh)
          have hqnext_value := flowCoverLiftingFunction_evalAtGapLeft
            a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
              (Nat.succ_le_succ (Nat.zero_le h)) (Nat.succ_le_of_lt hh)
          have hline_u : slope * q h + intercept = ((h : ℝ) - 1) * lam := by
            have hsum := partialSum_succ C a coverOrder h
            dsimp [slope, intercept, qnext, q]
            field_simp [ne_of_gt hweight_pos]
            nlinarith
          have hline_next : slope * qnext + intercept = (h : ℝ) * lam := by
            dsimp [slope, intercept]
            field_simp [ne_of_gt hweight_pos]
            ring
          have hL_next := hvalid qnext ⟨hqnext_mem.1, hqnext_cap⟩
          have hE_v : slope * v + intercept ≤
              flow_cover_lifting_function b lam (a ∘ coverOrder) v := by
            simpa [slope, intercept, qnext, q, lam] using hedge_valid v hv
          have hα : α = slope := by
            rw [hqnext_value] at hL_next
            rw [← hv_contact] at hE_v
            rw [hq_value] at hu_contact
            have hq_lt_next : q h < qnext := by
              dsimp [qnext, q]
              rw [partialSum_succ]
              linarith
            have hL_next' : α * qnext + β ≤ (h : ℝ) * lam := by
              simpa [lam] using hL_next
            have hupper : α * (qnext - q h) ≤ lam := by
              calc
                α * (qnext - q h) =
                    (α * qnext + β) - (α * q h + β) := by ring
                _ ≤ (h : ℝ) * lam - ((h : ℝ) - 1) * lam :=
                  sub_le_sub hL_next' (le_of_eq hu_contact.symm)
                _ = lam := by ring
            have hlower : slope * (v - q h) ≤ α * (v - q h) := by
              calc
                slope * (v - q h) =
                    (slope * v + intercept) - (slope * q h + intercept) := by ring
                _ ≤ (α * v + β) - (α * q h + β) :=
                  sub_le_sub hE_v (le_of_eq (hline_u.trans hu_contact.symm).symm)
                _ = α * (v - q h) := by ring
            have hslope_weight : slope * weight C a coverOrder (h + 1) = lam := by
              dsimp [slope]
              field_simp [ne_of_gt hweight_pos]
            have hqdiff : qnext - q h = weight C a coverOrder (h + 1) := by
              dsimp [qnext, q]
              rw [partialSum_succ]
              ring
            have hslope_le : slope ≤ α := by
              nlinarith only [hlower, huv]
            have hα_le : α ≤ slope := by
              rw [hqdiff, ← hslope_weight] at hupper
              nlinarith only [hupper, hweight_pos]
            exact le_antisymm hα_le hslope_le
          have hβ : β = intercept := by
            rw [hα, hq_value] at hu_contact
            nlinarith [hline_u]
          unfold OrderedFlowCover.admissiblePair
          exact Or.inr (Or.inl ⟨h + 1, by omega, Nat.succ_le_of_lt hh,
            by simpa [qnext, q, lam] using hqnext_cap, by simpa [slope, lam] using hα,
            by simpa [intercept, qnext, q, lam] using hβ⟩)
    · -- An interior contact in a gap forces slope one; crossing the right endpoint is impossible.
      have hq_lt_u : q h < u := lt_of_le_of_ne hgap.1 (Ne.symm hu_left)
      have hq_bound := hvalid (q h) ⟨hq_mem.1, hgap.1.trans hu.2⟩
      have hα_ge : 1 ≤ α := by
        rw [hq_value] at hq_bound
        rw [hu_value] at hu_contact
        have hdifference : u - q h ≤ α * (u - q h) := by
          calc
            u - q h =
                (u - partialSum C a coverOrder h + (h : ℝ) * lam) -
                  (((h : ℝ) - 1) * lam) := by
              dsimp [q, lam]
              ring
            _ = (α * u + β) - (((h : ℝ) - 1) * lam) := by rw [hu_contact]
            _ ≤ (α * u + β) - (α * q h + β) :=
              sub_le_sub_left hq_bound _
            _ = α * (u - q h) := by ring
        nlinarith only [hdifference, hq_lt_u]
      by_cases hv_mu : v ≤ partialSum C a coverOrder h
      · have hv_value := flowCoverLiftingFunction_eq_on_gapClosure
          a b C coverOrder r h ha_nonneg hC hcoverOrder hordered hr hh_pos hh hv_b
            ⟨hgap.1.trans (le_of_lt huv), hv_mu⟩
        have hα : α = 1 := by
          rw [hu_value] at hu_contact
          rw [hv_value] at hv_contact
          have hscaled : α * (v - u) = 1 * (v - u) := by
            calc
              α * (v - u) = (α * v + β) - (α * u + β) := by ring
              _ =
                  (v - partialSum C a coverOrder h + (h : ℝ) * lam) -
                    (u - partialSum C a coverOrder h + (h : ℝ) * lam) := by
                rw [hu_contact, hv_contact]
              _ = 1 * (v - u) := by ring
          nlinarith only [hscaled, huv]
        have hβ : β = (h : ℝ) * lam - partialSum C a coverOrder h := by
          rw [hu_value, hα] at hu_contact
          linarith
        have hcap_le := cap_le_coverBreakpoint_of_slopeOneValid
          a b C coverOrder r h ha_nonneg hC hcoverOrder hordered hr
            hi_pos.le hi_le_b hh (by
              intro z hz
              simpa [hα, hβ, lam] using hvalid z hz)
        unfold OrderedFlowCover.admissiblePair
        exact Or.inr (Or.inr (Or.inl ⟨h, hq_lt_u.trans_le hu.2,
          Or.inr ⟨hh, hcap_le⟩, hα, by simpa [lam] using hβ⟩))
      · have hmu_lt_v : partialSum C a coverOrder h < v := lt_of_not_ge hv_mu
        have hq_le_mu : q h ≤ partialSum C a coverOrder h := by
          dsimp [q, lam]
          linarith
        have hmu_b : partialSum C a coverOrder h ∈ Set.Icc (0 : ℝ) b :=
          ⟨hq_mem.1.trans hq_le_mu, hmu_lt_v.le.trans hv_b.2⟩
        have hmu_value := flowCoverLiftingFunction_eq_on_gapClosure
          a b C coverOrder r h ha_nonneg hC hcoverOrder hordered hr hh_pos hh hmu_b
            ⟨hq_le_mu, le_rfl⟩
        have hmu_bound := hvalid (partialSum C a coverOrder h)
          ⟨hmu_b.1, hmu_lt_v.le.trans hv.2⟩
        have hα_le : α ≤ 1 := by
          rw [hmu_value] at hmu_bound
          rw [hu_value] at hu_contact
          have hmu_bound' :
              α * partialSum C a coverOrder h + β ≤ (h : ℝ) * lam := by
            simpa [lam] using hmu_bound
          have hdifference :
              α * (partialSum C a coverOrder h - u) ≤
                1 * (partialSum C a coverOrder h - u) := by
            calc
              α * (partialSum C a coverOrder h - u) =
                  (α * partialSum C a coverOrder h + β) - (α * u + β) := by ring
              _ ≤ (h : ℝ) * lam - (α * u + β) :=
                sub_le_sub_right hmu_bound' _
              _ = 1 * (partialSum C a coverOrder h - u) := by
                rw [hu_contact]
                ring
          nlinarith only [hdifference, hgap.2]
        have hα : α = 1 := le_antisymm hα_le hα_ge
        have hβ : β = (h : ℝ) * lam - partialSum C a coverOrder h := by
          rw [hu_value, hα] at hu_contact
          linarith
        have hcap_le := cap_le_coverBreakpoint_of_slopeOneValid
          a b C coverOrder r h ha_nonneg hC hcoverOrder hordered hr
            hi_pos.le hi_le_b hh (by
              intro z hz
              simpa [hα, hβ, lam] using hvalid z hz)
        exfalso
        exact (not_le_of_gt (hmu_lt_v.trans_le hv.2)) hcap_le
  · -- A contact on a constant cell either stays on the initial zero edge or is impossible.
    have hu_lt_qnext : u < q (h + 1) := by simpa [q, lam] using hconstant.2
    have hu_value := flow_cover_lifting_function_eq_constant_on_cover_intervals
      a b C coverOrder r u ha_nonneg hC hcoverOrder hordered hr hu_b hh hconstant
    by_cases hh_zero : h = 0
    · subst h
      have hv_nonneg := flowCoverLiftingFunction_nonneg
        a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hv_b
      norm_num at hu_value
      rw [hu_value] at hu_contact
      rw [← hv_contact] at hv_nonneg
      have hα_nonneg : 0 ≤ α := by
        nlinarith only [hu_contact, hv_nonneg, huv]
      by_cases hv_q : v < q 1
      · have hv_value := flowCoverLiftingFunction_eq_on_constantClosure
          a b C coverOrder r 0 ha_nonneg hC hcoverOrder hordered hr (by omega) hv_b
            ⟨hv.1, le_of_lt hv_q⟩
        norm_num at hv_value
        rw [hv_value] at hv_contact
        have hα : α = 0 := by
          nlinarith only [hu_contact, hv_contact, huv]
        have hβ : β = 0 := by
          rw [hα] at hu_contact
          linarith only [hu_contact]
        unfold OrderedFlowCover.admissiblePair
        exact Or.inl ⟨hα, hβ⟩
      · have hq_le : q 1 ≤ v := le_of_not_gt hv_q
        have hq_mem := flowCoverGapLeft_mem_Icc
          a b C coverOrder r ha_nonneg hcoverOrder hordered hr
            (h := 1) le_rfl (by exact hh)
        have hq_value := flowCoverLiftingFunction_evalAtGapLeft
          a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
            (h := 1) le_rfl (by exact hh)
        have hq_bound := hvalid (q 1) ⟨hq_mem.1, hq_le.trans hv.2⟩
        norm_num at hq_value
        rw [hq_value] at hq_bound
        have hα_nonpos : α ≤ 0 := by
          have hdifference : α * (q 1 - u) ≤ 0 * (q 1 - u) := by
            calc
              α * (q 1 - u) = (α * q 1 + β) - (α * u + β) := by ring
              _ ≤ 0 - 0 := sub_le_sub hq_bound (le_of_eq hu_contact.symm)
              _ = 0 * (q 1 - u) := by ring
          nlinarith only [hdifference, hu_lt_qnext]
        have hα : α = 0 := le_antisymm hα_nonpos hα_nonneg
        have hβ : β = 0 := by
          rw [hα] at hu_contact
          linarith only [hu_contact]
        unfold OrderedFlowCover.admissiblePair
        exact Or.inl ⟨hα, hβ⟩
    · have hh_pos : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr hh_zero
      have hq_mem := flowCoverGapLeft_mem_Icc
        a b C coverOrder r ha_nonneg hcoverOrder hordered hr hh_pos (Nat.le_of_lt hh)
      have hq_value := flowCoverLiftingFunction_evalAtGapLeft
        a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hh_pos (Nat.le_of_lt hh)
      have hq_lt_u : q h < u := by
        dsimp [q, lam]
        linarith [hconstant.1, hlam_pos]
      have hq_bound := hvalid (q h) ⟨hq_mem.1, hq_lt_u.le.trans hu.2⟩
      rw [hu_value] at hu_contact
      rw [hq_value] at hq_bound
      have hα_pos : 0 < α := by
        have hdifference : lam ≤ α * (u - q h) := by
          calc
            lam = (h : ℝ) * lam - ((h : ℝ) - 1) * lam := by ring
            _ = (α * u + β) - ((h : ℝ) - 1) * lam := by rw [hu_contact]
            _ ≤ (α * u + β) - (α * q h + β) :=
              sub_le_sub_left hq_bound _
            _ = α * (u - q h) := by ring
        by_contra hα_not_pos
        have hα_nonpos : α ≤ 0 := le_of_not_gt hα_not_pos
        have hproduct_nonpos := mul_nonpos_of_nonpos_of_nonneg hα_nonpos
          (sub_pos.mpr hq_lt_u).le
        exact (not_lt_of_ge (hdifference.trans hproduct_nonpos)) hlam_pos
      by_cases hv_next : v < q (h + 1)
      · have hv_value := flowCoverLiftingFunction_eq_on_constantClosure
          a b C coverOrder r h ha_nonneg hC hcoverOrder hordered hr hh hv_b
            ⟨hconstant.1.trans (le_of_lt huv), le_of_lt hv_next⟩
        rw [hv_value] at hv_contact
        have hscaled : α * (v - u) = 0 * (v - u) := by
          calc
            α * (v - u) = (α * v + β) - (α * u + β) := by ring
            _ = 0 * (v - u) := by rw [hu_contact, hv_contact]; ring
        have hα_zero : α = 0 := by nlinarith only [hscaled, huv]
        exfalso
        exact (ne_of_gt hα_pos) hα_zero
      · have hqnext_le : q (h + 1) ≤ v := le_of_not_gt hv_next
        have hqnext_mem := flowCoverGapLeft_mem_Icc
          a b C coverOrder r ha_nonneg hcoverOrder hordered hr
            (Nat.succ_le_succ (Nat.zero_le h)) (Nat.succ_le_of_lt hh)
        have hqnext_value := flowCoverLiftingFunction_evalAtGapLeft
          a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr
            (Nat.succ_le_succ (Nat.zero_le h)) (Nat.succ_le_of_lt hh)
        have hqnext_bound := hvalid (q (h + 1))
          ⟨hqnext_mem.1, hqnext_le.trans hv.2⟩
        rw [hqnext_value] at hqnext_bound
        have hdifference : α * (q (h + 1) - u) ≤ 0 := by
          calc
            α * (q (h + 1) - u) =
                (α * q (h + 1) + β) - (α * u + β) := by ring
            _ ≤ (h : ℝ) * lam - (h : ℝ) * lam := by
              simpa [lam] using sub_le_sub hqnext_bound (le_of_eq hu_contact.symm)
            _ = 0 := by ring
        exfalso
        exact (not_lt_of_ge hdifference) (mul_pos hα_pos (sub_pos.mpr hu_lt_qnext))

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: when the outside capacity is
normalized by `a i ≤ b`, the four admissible source families are exactly the affine minorants with
two contacts on the effective flow interval, since `[0, min (a i) b] = [0, a i]`. -/
theorem admissiblePair_iff_cappedOneStepCriterion
    (a : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (i : Fin n)
    (αᵢ βᵢ : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hi_pos : 0 < a i)
    (hi_le_b : a i ≤ b)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    OrderedFlowCover.admissiblePair a b C coverOrder r i αᵢ βᵢ ↔
    cappedOneStepCriterion
        b
        (a i)
        (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
        αᵢ
        βᵢ := by
  -- Normalize the effective interval first; only the affine-support classification remains.
  rw [cappedOneStepCriterion_iff_outsideStepCriterion_of_le
    a b C coverOrder i αᵢ βᵢ hi_le_b]
  constructor
  · intro hadmissible
    unfold OrderedFlowCover.admissiblePair at hadmissible
    rcases hadmissible with hzero | hnonzero
    · rcases hzero with ⟨rfl, rfl⟩
      -- The initial positive-length plateau supplies the two contacts for the zero family.
      exact
        (cappedOneStepCriterion_iff_outsideStepCriterion_of_le
          a b C coverOrder i 0 0 hi_le_b).mp
          (cappedOneStepCriterion_zero
            a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr i hi_pos)
    · -- Each nonzero source family is the secant of one exposed lower-hull edge.
      rcases hnonzero with htwo | hthree | hfour
      · rcases htwo with ⟨h, hh_two, hh_cut, hh_cap, rfl, rfl⟩
        exact outsideStepCriterion_of_familyTwo
          a b C coverOrder r i ha_nonneg hi_pos hi_le_b hC hcoverOrder hordered hr
            hh_two hh_cut hh_cap
      · rcases hthree with ⟨ell, hleft, hell, rfl, rfl⟩
        exact outsideStepCriterion_of_familyThree
          a b C coverOrder r i ha_nonneg hi_pos hi_le_b hC hcoverOrder hordered hr
            hleft hell
      · rcases hfour with
          ⟨ell, hell_pos, hell_cut, hmu_lt, hcap_next, rfl, rfl⟩
        exact outsideStepCriterion_of_familyFour
          a b C coverOrder r i ha_nonneg hi_pos hi_le_b hC hcoverOrder hordered hr
            hell_pos hell_cut hmu_lt hcap_next
  · intro hcriterion
    by_cases hzero : αᵢ = 0 ∧ βᵢ = 0
    · unfold OrderedFlowCover.admissiblePair
      exact Or.inl hzero
    · -- Order the two contacts, then classify the first one by the profile partition.
      rcases hcriterion with ⟨hvalid, y', hy', y'', hy'', hne, hy'Contact, hy''Contact⟩
      rcases lt_or_gt_of_ne hne with hylt | hygt
      · exact admissiblePair_of_orderedContacts
          a b C coverOrder r i αᵢ βᵢ y' y'' ha_nonneg hi_pos hi_le_b hC hcoverOrder
            hordered hr hvalid hy' hy'' hylt hy'Contact hy''Contact
      · exact admissiblePair_of_orderedContacts
          a b C coverOrder r i αᵢ βᵢ y'' y' ha_nonneg hi_pos hi_le_b hC hcoverOrder
            hordered hr hvalid hy'' hy' hygt hy''Contact hy'Contact

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: once all outside affine costs
are valid, the lifted equality face is a facet exactly when each cost has two distinct contacts
with the common lifting profile. -/
theorem flowCoverLiftedFace_isFacet_iff_all_cappedContacts
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (ha_outside_pos : ∀ i, i ∉ C → 0 < a i)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    (hvalid :
      ∀ i, i ∉ C →
        ∀ y ∈ Set.Icc (0 : ℝ) (min (a i) b),
          α i * y + β i ≤
            flow_cover_lifting_function
              b (flow_cover_excess a b C) (a ∘ coverOrder) y) :
    IsFacetOf
        (convexHull ℝ (single_node_flow_set a b))
        (flow_cover_lifted_face a b C α β b) ↔
      ∀ i, i ∉ C →
        ∃ y' ∈ Set.Icc (0 : ℝ) (min (a i) b),
          ∃ y'' ∈ Set.Icc (0 : ℝ) (min (a i) b),
            y' ≠ y'' ∧
              α i * y' + β i =
                flow_cover_lifting_function
                  b (flow_cover_excess a b C) (a ∘ coverOrder) y' ∧
              α i * y'' + β i =
                flow_cover_lifting_function
                  b (flow_cover_excess a b C) (a ∘ coverOrder) y'' := by
  have hglobal :=
    flowCoverLiftedValid_of_all_cappedValid
      a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hvalid
  constructor
  · intro hfacet
    let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
    let FD : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
      (affineSpan ℝ (flow_cover_lifted_face a b C α β b)).direction
    let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
      flowCoverLiftedSupportLinearMap a α β b C
    have hdirectionLe : FD ≤ D ⊓ LinearMap.ker L := by
      simpa only [FD, D, L] using
        flowCoverLiftedFaceDirection_le_ambient_inf_supportKer
          a α β b C (isFacetOf_iff.mp hfacet).1
    have hfacetCodim : Module.finrank ℝ ↥FD + 1 = Module.finrank ℝ ↥D := by
      simpa only [FD, D] using (isFacetOf_iff.mp hfacet).2.2
    have hsupportCodim :
        Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
      simpa only [D, L] using
        flowCoverLiftedSupportKerCodimOne
          a α β b C ha_nonneg hC
            (isCutIndex_exists_gt a C coverOrder hcoverOrder hr)
    have hdirection : FD = D ⊓ LinearMap.ker L := by
      apply Submodule.eq_of_le_of_finrank_eq hdirectionLe
      omega
    rcases flowCoverLiftedSupport_has_coverNormalizedDirection
        a α β b C ha_nonneg hC
          (isCutIndex_exists_gt a C coverOrder hcoverOrder hr) with
      ⟨wCover, hwCoverD, hwCoverOutside, hwCoverEval⟩
    intro i hiC
    by_contra htwo
    have hcontactUnique :
        ∀ {y z : ℝ},
          y ∈ Set.Icc (0 : ℝ) (min (a i) b) →
          α i * y + β i =
            flow_cover_lifting_function
              b (flow_cover_excess a b C) (a ∘ coverOrder) y →
          z ∈ Set.Icc (0 : ℝ) (min (a i) b) →
          α i * z + β i =
            flow_cover_lifting_function
              b (flow_cover_excess a b C) (a ∘ coverOrder) z →
          y = z := by
      intro y z hy hyContact hz hzContact
      by_contra hyz
      exact htwo ⟨y, hy, z, hz, hyz, hyContact, hzContact⟩
    by_cases hcontactExists :
        ∃ y ∈ Set.Icc (0 : ℝ) (min (a i) b),
          α i * y + β i =
            flow_cover_lifting_function
              b (flow_cover_excess a b C) (a ∘ coverOrder) y
    · rcases hcontactExists with ⟨y₀, hy₀, hy₀Contact⟩
      let K : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
        ((LinearMap.proj i).comp (LinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))) -
          y₀ • ((LinearMap.proj i).comp (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)))
      have hsourceEq :
          ∀ p ∈ single_node_flow_set a b,
            flow_cover_lifted_value a b C α β p = b → K p = 0 := by
        intro p hp hpTight
        rcases (mem_single_node_flow_set_iff a b p).mp hp with
          ⟨hxBinary, hyNonneg, -, hyCapacity⟩
        rcases hxBinary i with hxi | hxi
        · have hyZero : p.2 i = 0 := by
            have hyUpper := hyCapacity i
            rw [hxi] at hyUpper
            exact le_antisymm (by simpa using hyUpper) (hyNonneg i)
          simp [K, hxi, hyZero]
        · have hyInterval :=
            singleNodeFlow_selectedCoordinate_mem_cappedInterval a b hp i hxi
          have hyContact :=
            flowCoverSourcePoint_contact_of_tight
              a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hvalid
              hp hpTight i hiC hxi
          have hyEq : p.2 i = y₀ :=
            hcontactUnique hyInterval hyContact hy₀ hy₀Contact
          simp [K, hxi, hyEq]
      have hfaceKer : FD ≤ LinearMap.ker K := by
        simpa only [FD] using
          flowCoverLiftedFaceDirection_le_ker_of_tightSource_eq_zero
            a α β b C K hglobal hsourceEq
      let e : (Fin n → ℝ) × (Fin n → ℝ) :=
        ((fun _ ↦ (0 : ℝ)), fun j ↦ if j = i then 1 else 0)
      have heD : e ∈ D := by
        simpa [e, D] using
          flowCoverOutsideCoordinatePair_mem_ambientDirection
            a b C ha_nonneg hC
              (isCutIndex_exists_gt a C coverOrder hcoverOrder hr)
              hiC (ha_outside_pos i hiC) 0 1
      have heK : K e = 1 := by
        simp [K, e]
      have hwCoverK : K wCover = 0 := by
        rcases hwCoverOutside i hiC with ⟨hwx, hwy⟩
        simp [K, hwx, hwy]
      let v := e - (L e) • wCover
      have hvD : v ∈ D := D.sub_mem heD (D.smul_mem (L e) hwCoverD)
      have hvL : L v = 0 := by
        change L (e - (L e) • wCover) = 0
        rw [LinearMap.map_sub, LinearMap.map_smul, hwCoverEval]
        ring
      have hvK : K v = 1 := by
        simp [v, heK, hwCoverK]
      have hvFD : v ∈ FD := by
        rw [hdirection]
        exact ⟨hvD, hvL⟩
      have hvKZero := hfaceKer hvFD
      change K v = 0 at hvKZero
      rw [hvK] at hvKZero
      exact one_ne_zero hvKZero
    · let K : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
        (LinearMap.proj i).comp (LinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ))
      have hsourceEq :
          ∀ p ∈ single_node_flow_set a b,
            flow_cover_lifted_value a b C α β p = b → K p = 0 := by
        intro p hp hpTight
        rcases (mem_single_node_flow_set_iff a b p).mp hp with
          ⟨hxBinary, -, -, -⟩
        rcases hxBinary i with hxi | hxi
        · simp [K, hxi]
        · have hyInterval :=
            singleNodeFlow_selectedCoordinate_mem_cappedInterval a b hp i hxi
          have hyContact :=
            flowCoverSourcePoint_contact_of_tight
              a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hvalid
              hp hpTight i hiC hxi
          exfalso
          exact hcontactExists ⟨p.2 i, hyInterval, hyContact⟩
      have hfaceKer : FD ≤ LinearMap.ker K := by
        simpa only [FD] using
          flowCoverLiftedFaceDirection_le_ker_of_tightSource_eq_zero
            a α β b C K hglobal hsourceEq
      let e : (Fin n → ℝ) × (Fin n → ℝ) :=
        ((fun j ↦ if j = i then 1 else 0), fun _ ↦ (0 : ℝ))
      have heD : e ∈ D := by
        simpa [e, D] using
          flowCoverOutsideCoordinatePair_mem_ambientDirection
            a b C ha_nonneg hC
              (isCutIndex_exists_gt a C coverOrder hcoverOrder hr)
              hiC (ha_outside_pos i hiC) 1 0
      have heK : K e = 1 := by
        simp [K, e]
      have hwCoverK : K wCover = 0 := by
        exact (hwCoverOutside i hiC).1
      let v := e - (L e) • wCover
      have hvD : v ∈ D := D.sub_mem heD (D.smul_mem (L e) hwCoverD)
      have hvL : L v = 0 := by
        change L (e - (L e) • wCover) = 0
        rw [LinearMap.map_sub, LinearMap.map_smul, hwCoverEval]
        ring
      have hvK : K v = 1 := by
        simp [v, heK, hwCoverK]
      have hvFD : v ∈ FD := by
        rw [hdirection]
        exact ⟨hvD, hvL⟩
      have hvKZero := hfaceKer hvFD
      change K v = 0 at hvKZero
      rw [hvK] at hvKZero
      exact one_ne_zero hvKZero
  · intro hcontacts
    have hzeroFacet :=
      zeroLiftingFacetDefining_of_isCutIndex
        a b C coverOrder r ha_nonneg hC hcoverOrder hr
    rcases (isFacetOf_iff.mp hzeroFacet.2).1 with ⟨q₀, hq₀F⟩
    let q := flowCoverPairProjection C q₀
    have hqF : q ∈ flow_cover_lifted_face a b C α β b :=
      flowCoverPairProjection_mem_liftedFace a α β b C hq₀F
    rw [isFacetOf_iff]
    refine ⟨⟨q, hqF⟩, ?_, ?_⟩
    · -- Validity identifies the equality slice as the exposed face of the lifted support map.
      exact flowCoverLiftedFace_isExposed
        a α β b C coverOrder r ha_nonneg hC hcoverOrder hr hglobal
    · let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
        (affineSpan ℝ (convexHull ℝ (single_node_flow_set a b))).direction
      let L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
        flowCoverLiftedSupportLinearMap a α β b C
      have hdirection :
          (affineSpan ℝ (flow_cover_lifted_face a b C α β b)).direction =
            D ⊓ LinearMap.ker L := by
        simpa [D, L] using
          flowCoverLiftedFaceDirection_eq_ambient_inf_supportKer_of_contacts
            a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hcontacts
      have hcodim :
          Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
        simpa [D, L] using
          flowCoverLiftedSupportKerCodimOne
            a α β b C ha_nonneg hC
              (isCutIndex_exists_gt a C coverOrder hcoverOrder hr)
      rw [hdirection]
      exact hcodim

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean: the lifted inequality is a
facet exactly when every outside coordinate supplies capped one-step lifting data. -/
theorem flowCoverLiftedFacet_iff_all_cappedOneStepCriterion
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (ha_outside_pos : ∀ i, i ∉ C → 0 < a i)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    flow_cover_lifted_inequality_facet_defining a b C α β b ↔
      ∀ i, i ∉ C →
        cappedOneStepCriterion
          b
          (a i)
          (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder))
          (α i)
          (β i) := by
  rw [flow_cover_lifted_inequality_facet_defining_iff]
  constructor
  · rintro ⟨hglobal, hfacet⟩
    have hvalid :=
      (flowCoverLiftedValidity_iff_all_cappedValid
        a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr).mp hglobal
    have hcontacts :=
      (flowCoverLiftedFace_isFacet_iff_all_cappedContacts
        a α β b C coverOrder r ha_nonneg ha_outside_pos hC hcoverOrder hordered hr hvalid).mp
        hfacet
    intro i hiC
    -- Facetness supplies the contact half, while global validity supplies the interval half.
    exact ⟨hvalid i hiC, hcontacts i hiC⟩
  · intro hall
    have hvalid :
        ∀ i, i ∉ C →
          ∀ y ∈ Set.Icc (0 : ℝ) (min (a i) b),
            α i * y + β i ≤
              flow_cover_lifting_function
                b (flow_cover_excess a b C) (a ∘ coverOrder) y := by
      intro i hiC
      exact (hall i hiC).1
    have hcontacts :
        ∀ i, i ∉ C →
          ∃ y' ∈ Set.Icc (0 : ℝ) (min (a i) b),
            ∃ y'' ∈ Set.Icc (0 : ℝ) (min (a i) b),
              y' ≠ y'' ∧
                α i * y' + β i =
                  flow_cover_lifting_function
                    b (flow_cover_excess a b C) (a ∘ coverOrder) y' ∧
                α i * y'' + β i =
                  flow_cover_lifting_function
                    b (flow_cover_excess a b C) (a ∘ coverOrder) y'' := by
      intro i hiC
      exact (hall i hiC).2
    constructor
    · -- The analytic validity half is now fully discharged by the global/local equivalence.
      exact
        (flowCoverLiftedValidity_iff_all_cappedValid
          a α β b C coverOrder r ha_nonneg hC hcoverOrder hordered hr).mpr hvalid
    · -- The two-contact rank characterization supplies the remaining facet half.
      exact
        (flowCoverLiftedFace_isFacet_iff_all_cappedContacts
          a α β b C coverOrder r ha_nonneg ha_outside_pos hC hcoverOrder hordered hr hvalid).mpr
          hcontacts

-- The preceding facet characterization's proof closes the entry.
/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_theorem_7_16.lean

Theorem 7.16 (Gu et al. [191]). Let `T = single_node_flow_set a b` with nonnegative
capacities `a`, let `C` be a flow cover for `T`, let `λ = flow_cover_excess a b C`, let
`coverOrder` enumerate the elements of `C` in nonincreasing order of their coefficients
`a_{j_h}`, let `r` be the last ordered cover position with `a_{j_r} > λ`, and assume every
noncover capacity lies in `(0, b]`. Then the lifted flow-cover inequality `(7.16)` is
facet-defining for `T` if and only if, for each `i ∉ C`, the pair `(α_i, β_i)` is one of the four
source families listed in Theorem 7.16. -/
theorem flow_cover_inequality_facet_defining_iff_all_outside_pairs_admissible
    (a α β : Fin n → ℝ)
    (b : ℝ)
    (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (ha_outside_pos : ∀ i, i ∉ C → 0 < a i)
    (ha_outside_le_b : ∀ i, i ∉ C → a i ≤ b)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r) :
    flow_cover_lifted_inequality_facet_defining a b C α β b ↔
      ∀ i, i ∉ C → OrderedFlowCover.admissiblePair a b C coverOrder r i (α i) (β i) := by
  -- Route correction: the capped interval bridge matches the source interval once every outside
  -- capacity is normalized by `a i ≤ b`.
  rw [flowCoverLiftedFacet_iff_all_cappedOneStepCriterion
    a α β b C coverOrder r ha_nonneg ha_outside_pos hC hcoverOrder hordered hr]
  constructor
  · intro hall i hi
    -- Convert the capped one-step data supplied by the global facet bridge to the source family.
    exact
      (admissiblePair_iff_cappedOneStepCriterion
        a b C coverOrder r i (α i) (β i) ha_nonneg (ha_outside_pos i hi) (ha_outside_le_b i hi)
        hC hcoverOrder hordered hr).mpr (hall i hi)
  · intro hall i hi
    -- Convert each source family back to the capped data consumed by the global facet bridge.
    exact
      (admissiblePair_iff_cappedOneStepCriterion
        a b C coverOrder r i (α i) (β i) ha_nonneg (ha_outside_pos i hi) (ha_outside_le_b i hi)
        hC hcoverOrder hordered hr).mp (hall i hi)

end Theorem716

#print axioms flow_cover_inequality_facet_defining_iff_all_outside_pairs_admissible

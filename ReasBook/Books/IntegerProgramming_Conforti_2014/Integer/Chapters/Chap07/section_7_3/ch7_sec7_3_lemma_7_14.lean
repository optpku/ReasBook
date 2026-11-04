/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_13
import Mathlib.Data.Fin.Tuple.Sort

-- Declarations for this item will be appended below by the statement pipeline.

section Lemma714

open scoped BigOperators
open SequenceIndependentLifting
open OrderedFlowCover

/- The proof follows the source decomposition from Lemma 7.13.  We first make the ordered
representation invisible to the lifting function, then prove the adjusted-prefix invariant used
to combine two active stages. -/

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: reindexing all
coordinates by a finite equivalence preserves the feasible lifting objective values. -/
lemma flowCoverLiftingObjectiveValues_comp_equiv
    {m n : ℕ} (e : Fin m ≃ Fin n) (b lam z : ℝ) (a : Fin n → ℝ) :
    flow_cover_lifting_objective_values b lam (a ∘ e) z =
      flow_cover_lifting_objective_values b lam a z := by
  -- Transport both Boolean selectors and continuous fills along the coordinate equivalence.
  ext v
  constructor
  · intro hv
    rcases (mem_flow_cover_lifting_objective_values_iff b lam (a ∘ e) z v).1 hv with
      ⟨x, y, hy_nonneg, hy_sum, hy_cap, rfl⟩
    refine (mem_flow_cover_lifting_objective_values_iff b lam a z _).2 ?_
    refine ⟨x ∘ e.symm, y ∘ e.symm, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hy_nonneg (e.symm i)
    · simpa [Equiv.sum_comp] using hy_sum
    · intro i
      simpa [Function.comp_def] using hy_cap (e.symm i)
    · simpa [Function.comp_def] using
        (e.sum_comp (fun i : Fin n ↦
          y (e.symm i) +
            max (a i - lam) 0 * (1 - if x (e.symm i) then (1 : ℝ) else 0)))
  · intro hv
    rcases (mem_flow_cover_lifting_objective_values_iff b lam a z v).1 hv with
      ⟨x, y, hy_nonneg, hy_sum, hy_cap, rfl⟩
    refine (mem_flow_cover_lifting_objective_values_iff b lam (a ∘ e) z _).2 ?_
    refine ⟨x ∘ e, y ∘ e, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hy_nonneg (e i)
    · simpa [Equiv.sum_comp] using hy_sum
    · intro i
      simpa [Function.comp_def] using hy_cap (e i)
    · simpa [Function.comp_def] using
        (e.sum_comp (fun i : Fin n ↦
          y i + max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0))).symm

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: the flow-cover lifting
function is invariant under a finite equivalence of its coordinates. -/
lemma flowCoverLiftingFunction_comp_equiv
    {m n : ℕ} (e : Fin m ≃ Fin n) (b lam z : ℝ) (a : Fin n → ℝ) :
    flow_cover_lifting_function b lam (a ∘ e) z =
      flow_cover_lifting_function b lam a z := by
  -- Rewrite the optimization set through the preceding reindexing identity.
  rw [flow_cover_lifting_function, flow_cover_lifting_function,
    flowCoverLiftingObjectiveValues_comp_equiv e b lam z a]

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: every finite real tuple
admits a full-cover enumeration on which its coefficients are antitone. -/
lemma existsAntitoneFullCoverOrder
    {t : ℕ} (a : Fin t → ℝ) :
    ∃ e : Fin (Finset.univ : Finset (Fin t)).card ≃ Fin t,
      enumerates Finset.univ e.toEmbedding ∧ Antitone (a ∘ e) := by
  have hcard : (Finset.univ : Finset (Fin t)).card = t := by
    simp
  let cardEquiv : Fin (Finset.univ : Finset (Fin t)).card ≃ Fin t :=
    finCongr hcard
  let sortEquiv : Equiv.Perm (Fin t) := Tuple.sort (OrderDual.toDual ∘ a)
  refine ⟨cardEquiv.trans sortEquiv, ?_, ?_⟩
  · -- Surjectivity of the equivalence identifies its range with the full cover.
    rw [enumerates]
    simpa only [Finset.coe_univ] using Set.range_eq_univ.mpr (cardEquiv.trans sortEquiv).surjective
  · -- Sorting in the dual order is precisely descending order in `ℝ`.
    intro i j hij
    have hcast : cardEquiv i ≤ cardEquiv j := by
      exact_mod_cast hij
    have hmono := Tuple.monotone_sort (OrderDual.toDual ∘ a) hcast
    simpa [cardEquiv, sortEquiv, Function.comp_def] using hmono

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: on a feasible residual
interval, a nonnegative lifting function built from a cover sum exceeding `b` lies below the
identity. -/
lemma flowCoverLiftingFunction_le_self
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ)
    (ha_nonneg : ∀ i, 0 ≤ a i)
    (hcover : b < ∑ i, a i)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b) :
    flow_cover_lifting_function b lam a z ≤ z := by
  let allSelected : Fin t → Bool := fun _ ↦ true
  have hdemand_nonneg : 0 ≤ b - z := by
    linarith [hz.2]
  have hdemand_le_capacity : b - z ≤ ∑ i, a i := by
    linarith [hz.1, hcover]
  have hobjective : selectorObjective b lam a z allSelected = b - z := by
    -- Selecting every coordinate removes all penalties and leaves exactly the residual demand.
    simp [allSelected, selectorObjective, selectorCapacity, selectorPenalty,
      min_eq_left hdemand_le_capacity]
  have hmem : b - z ∈ flow_cover_lifting_objective_values b lam a z := by
    rw [← hobjective]
    exact selectorObjective_mem ha_nonneg hdemand_nonneg allSelected
  have hsup : b - z ≤ sSup (flow_cover_lifting_objective_values b lam a z) :=
    le_csSup (flow_cover_lifting_objective_values_bddAbove b lam a z) hmem
  -- Subtracting the supremum reverses the witness bound into `f z ≤ z`.
  rw [flow_cover_lifting_function]
  linarith

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: increasing the lifted
coordinate can only increase the flow-cover lifting function while residual demand remains
nonnegative. -/
lemma flowCoverLiftingFunction_mono
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ)
    (ha_nonneg : ∀ i, 0 ≤ a i)
    {u v : ℝ} (huv : u ≤ v) (hv : v ≤ b) :
    flow_cover_lifting_function b lam a u ≤
      flow_cover_lifting_function b lam a v := by
  let Su := flow_cover_lifting_objective_values b lam a u
  let Sv := flow_cover_lifting_objective_values b lam a v
  have hsubset : Sv ⊆ Su := by
    intro q hq
    rcases (mem_flow_cover_lifting_objective_values_iff b lam a v q).1 hq with
      ⟨x, y, hy_nonneg, hy_sum, hy_cap, hq_eq⟩
    refine (mem_flow_cover_lifting_objective_values_iff b lam a u q).2 ?_
    refine ⟨x, y, hy_nonneg, ?_, hy_cap, hq_eq⟩
    linarith
  have hSv_nonempty : Sv.Nonempty := by
    let allSelected : Fin t → Bool := fun _ ↦ true
    have hdemand_nonneg : 0 ≤ b - v := by
      linarith
    refine ⟨selectorObjective b lam a v allSelected, ?_⟩
    simpa [Sv] using selectorObjective_mem ha_nonneg hdemand_nonneg allSelected
  have hSu_bdd : BddAbove Su := by
    simpa [Su] using flow_cover_lifting_objective_values_bddAbove b lam a u
  have hsup : sSup Sv ≤ sSup Su := by
    refine csSup_le hSv_nonempty ?_
    intro q hq
    exact le_csSup hSu_bdd (hsubset hq)
  -- The common leading constant turns monotonicity of the suprema into monotonicity of `f`.
  simp only [flow_cover_lifting_function]
  simpa [Su, Sv] using sub_le_sub_left hsup b

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: if every coefficient is
at most the excess parameter, the lifting function is the identity on `[0,b]`. -/
lemma flowCoverLiftingFunction_eq_self_of_forall_le
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ)
    (ha_nonneg : ∀ i, 0 ≤ a i)
    (hcover : b < ∑ i, a i)
    (ha_le : ∀ i, a i ≤ lam)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b) :
    flow_cover_lifting_function b lam a z = z := by
  let S := flow_cover_lifting_objective_values b lam a z
  let allSelected : Fin t → Bool := fun _ ↦ true
  have hdemand_nonneg : 0 ≤ b - z := by
    linarith [hz.2]
  have hS_nonempty : S.Nonempty := by
    refine ⟨selectorObjective b lam a z allSelected, ?_⟩
    simpa [S] using selectorObjective_mem ha_nonneg hdemand_nonneg allSelected
  have hobjective_upper : ∀ {q : ℝ}, q ∈ S → q ≤ b - z := by
    intro q hq
    rcases (mem_flow_cover_lifting_objective_values_iff b lam a z q).1 hq with
      ⟨x, y, hy_nonneg, hy_sum, hy_cap, hq_eq⟩
    have hpenalty_zero :
        ∑ i : Fin t, max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [max_eq_right]
      · simp
      · exact sub_nonpos.mpr (ha_le i)
    rw [hq_eq, Finset.sum_add_distrib, hpenalty_zero, add_zero]
    exact hy_sum
  have hsup_upper : sSup S ≤ b - z := by
    refine csSup_le hS_nonempty ?_
    intro q hq
    exact hobjective_upper hq
  have hlower : z ≤ flow_cover_lifting_function b lam a z := by
    rw [flow_cover_lifting_function]
    simpa [S] using sub_le_sub_left hsup_upper b
  -- Combine the universal upper bound with the all-selected witness bound.
  exact le_antisymm
    (flowCoverLiftingFunction_le_self b lam a ha_nonneg hcover hz)
    hlower

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: subtracting a linear
term from a prefix sum turns its successor rule into addition of one adjusted weight. -/
lemma adjustedPartialSum_succ
    {n : ℕ} (a : Fin n → ℝ) (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n) (lam : ℝ) (k : ℕ) :
    partialSum C a coverOrder (k + 1) - (k + 1 : ℝ) * lam =
      (partialSum C a coverOrder k - (k : ℝ) * lam) +
        (weight C a coverOrder (k + 1) - lam) := by
  -- Expand the next prefix once; the remaining identity is purely additive normalization.
  rw [partialSum_succ]
  ring

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: before the cut index,
the capped adjusted prefix sums `μ_h - h λ` are subadditive. -/
lemma adjustedPartialSum_min_add_le
    {n : ℕ} (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n) (r : ℕ)
    (hordered : Antitone fun i : Fin C.card ↦ a (coverOrder i))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {h k : ℕ} (hh : h ≤ r) (hk : k ≤ r) :
    partialSum C a coverOrder (min r (h + k)) -
        ((min r (h + k) : ℕ) : ℝ) * flow_cover_excess a b C ≤
      (partialSum C a coverOrder h - (h : ℝ) * flow_cover_excess a b C) +
        (partialSum C a coverOrder k - (k : ℝ) * flow_cover_excess a b C) := by
  let lam := flow_cover_excess a b C
  induction k with
  | zero =>
      -- Capping `h + 0` does nothing, and the adjusted zeroth prefix is zero.
      simp [Nat.min_eq_right hh, partialSum]
  | succ k ih =>
      have hk_le : k ≤ r := by
        omega
      have hstep :
          partialSum C a coverOrder (k + 1) - (k + 1 : ℝ) * lam =
            (partialSum C a coverOrder k - (k : ℝ) * lam) +
              (weight C a coverOrder (k + 1) - lam) := by
        -- Peel off the last adjusted weight using the normalized successor interface.
        exact adjustedPartialSum_succ a C coverOrder lam k
      by_cases hsum : h + k < r
      · have hsum_card : h + k < C.card := lt_of_lt_of_le hsum hr.2.1
        have hk_card : k < C.card := by
          omega
        have hweight :
            weight C a coverOrder (h + k + 1) ≤ weight C a coverOrder (k + 1) := by
          rw [weight_succ C a coverOrder hsum_card, weight_succ C a coverOrder hk_card]
          have hindex : (⟨k, hk_card⟩ : Fin C.card) ≤ ⟨h + k, hsum_card⟩ := by
            exact_mod_cast Nat.le_add_left k h
          exact hordered hindex
        have hleftStep :
            partialSum C a coverOrder (h + k + 1) - (h + k + 1 : ℝ) * lam =
              (partialSum C a coverOrder (h + k) - (h + k : ℝ) * lam) +
                (weight C a coverOrder (h + k + 1) - lam) := by
          -- Advance the uncapped sum by the same adjusted-weight successor rule.
          simpa only [Nat.cast_add, Nat.cast_one] using
            adjustedPartialSum_succ a C coverOrder lam (h + k)
        have hmin_old : min r (h + k) = h + k := Nat.min_eq_right hsum.le
        have hmin_new : min r (h + (k + 1)) = h + k + 1 := by
          omega
        have ih' := ih hk_le
        rw [hmin_old] at ih'
        push_cast at ih'
        rw [hmin_new]
        push_cast
        dsimp [lam] at hleftStep hstep
        rw [hleftStep, hstep]
        linarith
      · have hmin_old : min r (h + k) = r := Nat.min_eq_left (Nat.le_of_not_gt hsum)
        have hmin_new : min r (h + (k + 1)) = r := by
          omega
        have hk_lt : k < r := by
          omega
        have hweight_pos : lam < weight C a coverOrder (k + 1) := by
          simpa [lam] using
            coverWeight_gt_excess_before_cutIndex
              (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
              hordered hr hk_lt
        have ih' := ih hk_le
        rw [hmin_old] at ih'
        rw [hmin_new]
        push_cast
        dsimp [lam] at hstep
        rw [hstep]
        linarith

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: a nonempty strict
superlevel set of an antitone finite tuple has a last position, which is a valid cut index. -/
lemma existsCutIndex_of_exists_gt
    {n : ℕ} (a : Fin n → ℝ) (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n) (lam : ℝ)
    (hordered : Antitone fun i : Fin C.card ↦ a (coverOrder i))
    (hexists : ∃ i : Fin C.card, lam < a (coverOrder i)) :
    ∃ r, isCutIndex a C coverOrder lam r := by
  -- Count the strict superlevel set; antitonicity makes its last member the desired cut.
  let r := (Finset.univ.filter (fun i : Fin C.card ↦ lam < a (coverOrder i))).card
  have hr_pos : 1 ≤ r := by
    rw [Nat.one_le_iff_ne_zero]
    intro hr_zero
    rcases hexists with ⟨i, hi⟩
    have himem : i ∈ Finset.univ.filter (fun j : Fin C.card ↦ lam < a (coverOrder j)) := by
      simp [hi]
    have hempty : Finset.univ.filter (fun j : Fin C.card ↦ lam < a (coverOrder j)) = ∅ := by
      exact Finset.card_eq_zero.mp hr_zero
    rw [hempty] at himem
    simp at himem
  have hr_le : r ≤ C.card := by
    calc
      r ≤ (Finset.univ : Finset (Fin C.card)).card := by
        dsimp [r]
        exact Finset.card_filter_le
          (Finset.univ : Finset (Fin C.card))
          (fun i : Fin C.card ↦ lam < a (coverOrder i))
      _ = C.card := by simp
  refine ⟨r, hr_pos, hr_le, ?_, ?_⟩
  · have hpred_lt_r : r - 1 < r := Nat.pred_lt (Nat.ne_of_gt hr_pos)
    have hpred_lt_card : r - 1 < C.card := lt_of_lt_of_le hpred_lt_r hr_le
    have hentry :
        lam < a (coverOrder ⟨r - 1, hpred_lt_card⟩) := by
      apply (Tuple.lt_card_gt_iff_apply_gt_of_antitone hordered).1
      simpa [r] using hpred_lt_r
    have hweight :
        weight C a coverOrder r = a (coverOrder ⟨r - 1, hpred_lt_card⟩) := by
      have hweightPred := weight_succ C a coverOrder hpred_lt_card
      rw [Nat.sub_add_cancel hr_pos] at hweightPred
      exact hweightPred
    rwa [hweight]
  · intro h hrh hhcard
    have hpred_lt_h : h - 1 < h := Nat.pred_lt (Nat.ne_of_gt (lt_of_lt_of_le hr_pos hrh.le))
    have hpred_lt_card : h - 1 < C.card := lt_of_lt_of_le hpred_lt_h hhcard
    have hr_le_pred : r ≤ h - 1 := by
      omega
    have hnot : ¬ lam < a (coverOrder ⟨h - 1, hpred_lt_card⟩) := by
      intro hgt
      have hpred_lt_count :
          (⟨h - 1, hpred_lt_card⟩ : Fin C.card) <
            (Finset.univ.filter (fun i : Fin C.card ↦ lam < a (coverOrder i))).card :=
        (Tuple.lt_card_gt_iff_apply_gt_of_antitone hordered).2 hgt
      have hpred_lt_r : h - 1 < r := by
        simpa [r] using hpred_lt_count
      exact (not_lt_of_ge hr_le_pred) hpred_lt_r
    have hh_pos : 1 ≤ h := lt_of_lt_of_le hr_pos hrh.le
    have hweight :
        weight C a coverOrder h = a (coverOrder ⟨h - 1, hpred_lt_card⟩) := by
      have hweightPred := weight_succ C a coverOrder hpred_lt_card
      rw [Nat.sub_add_cancel hh_pos] at hweightPred
      exact hweightPred
    rw [hweight]
    exact le_of_not_gt hnot

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: every point of `[0,b]`
is either on the final affine piece or has one active pre-cut stage with a max-deficit formula. -/
lemma flowCoverLiftingFunction_stageProfile
    {n : ℕ} (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n) (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun i : Fin C.card ↦ a (coverOrder i))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b) :
    (partialSum C a coverOrder r - flow_cover_excess a b C ≤ z ∧
      flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
        z - partialSum C a coverOrder r + (r : ℝ) * flow_cover_excess a b C) ∨
    ∃ h, h < r ∧
      partialSum C a coverOrder h - flow_cover_excess a b C ≤ z ∧
      z < partialSum C a coverOrder (h + 1) - flow_cover_excess a b C ∧
      flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z =
        (h : ℝ) * flow_cover_excess a b C -
          max 0 (partialSum C a coverOrder h - z) := by
  let lam := flow_cover_excess a b C
  have hlam_pos : 0 < lam := by
    simpa [lam] using flow_cover_excess_pos a b C hC
  by_cases hfinal : partialSum C a coverOrder r - lam ≤ z
  · left
    refine ⟨hfinal, ?_⟩
    -- Lemma 7.13 supplies the terminal affine formula directly.
    simpa [lam] using
      flow_cover_lifting_function_eq_affine_on_final_interval
        (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r) (z := z)
        ha_nonneg hC hcoverOrder hordered hr hz ⟨hfinal, hz.2⟩
  · have hz_lt_final : z < partialSum C a coverOrder r - lam := lt_of_not_ge hfinal
    have hr_pos : 1 ≤ r := hr.1
    have hr_pred : r - 1 < r := Nat.pred_lt (Nat.ne_of_gt hr_pos)
    have hr_succ : r - 1 + 1 = r := Nat.sub_add_cancel hr_pos
    have hexists :
        ∃ q : ℕ, q < r ∧ z < partialSum C a coverOrder (q + 1) - lam := by
      exact ⟨r - 1, hr_pred, by simpa [hr_succ] using hz_lt_final⟩
    let h := Nat.find hexists
    have hh : h < r := (Nat.find_spec hexists).1
    have hupper : z < partialSum C a coverOrder (h + 1) - lam :=
      (Nat.find_spec hexists).2
    have hlower : partialSum C a coverOrder h - lam ≤ z := by
      by_cases hh_zero : h = 0
      · have hpartial_zero : partialSum C a coverOrder h = 0 := by
          simp [hh_zero, partialSum]
        rw [hpartial_zero]
        linarith [hz.1]
      · have hh_pos : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr hh_zero
        by_contra hnot
        have hprev :
            h - 1 < r ∧ z < partialSum C a coverOrder (h - 1 + 1) - lam := by
          have hprev_lt : h - 1 < r := by
            omega
          have hprev_upper : z < partialSum C a coverOrder (h - 1 + 1) - lam := by
            simpa [Nat.sub_add_cancel hh_pos] using lt_of_not_ge hnot
          exact ⟨hprev_lt, hprev_upper⟩
        have hfind_le : h ≤ h - 1 := by
          simpa [h] using Nat.find_min' hexists hprev
        omega
    right
    refine ⟨h, hh, hlower, hupper, ?_⟩
    by_cases hz_mu : z < partialSum C a coverOrder h
    · have hh_pos : 1 ≤ h := by
        by_contra hnot
        have hh_zero : h = 0 := by omega
        have hnot_lt : ¬ z < partialSum C a coverOrder h := by
          simpa [hh_zero, partialSum] using not_lt_of_ge hz.1
        exact hnot_lt hz_mu
      have hgap :=
        flow_cover_lifting_function_eq_affine_on_gap_intervals
          (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r) (z := z)
          ha_nonneg hC hcoverOrder hordered hr hz hh_pos hh ⟨hlower, hz_mu⟩
      have hdeficit_nonneg : 0 ≤ partialSum C a coverOrder h - z := by
        linarith
      rw [max_eq_right hdeficit_nonneg]
      rw [hgap]
      ring
    · have hconstant :=
        flow_cover_lifting_function_eq_constant_on_cover_intervals
          (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r) (z := z)
          ha_nonneg hC hcoverOrder hordered hr hz hh ⟨le_of_not_gt hz_mu, hupper⟩
      have hdeficit_nonpos : partialSum C a coverOrder h - z ≤ 0 := by
        linarith
      rw [max_eq_left hdeficit_nonpos]
      simpa [lam] using hconstant

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: once `z` has reached
the start `μ_s - λ` of a stage, that stage's max-deficit line is a lower support for the lifting
function. -/
lemma flowCoverLiftingFunction_stageSupport
    {n : ℕ} (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n) (r : ℕ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun i : Fin C.card ↦ a (coverOrder i))
    (hr : isCutIndex a C coverOrder (flow_cover_excess a b C) r)
    {s : ℕ} (hs : s ≤ r)
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b)
    (hstart : partialSum C a coverOrder s - flow_cover_excess a b C ≤ z) :
    (s : ℝ) * flow_cover_excess a b C -
        max 0 (partialSum C a coverOrder s - z) ≤
      flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder) z := by
  let lam := flow_cover_excess a b C
  have hlam_pos : 0 < lam := by
    simpa [lam] using flow_cover_excess_pos a b C hC
  have hprofile :=
    flowCoverLiftingFunction_stageProfile
      a b C coverOrder r ha_nonneg hC hcoverOrder hordered hr hz
  rcases hprofile with hfinal | ⟨q, hq, hq_lower, hq_upper, hq_value⟩
  · by_cases hsr : s = r
    · subst s
      by_cases hz_mu : z ≤ partialSum C a coverOrder r
      · have hdeficit_nonneg : 0 ≤ partialSum C a coverOrder r - z := by
          linarith
        rw [max_eq_right hdeficit_nonneg, hfinal.2]
        linarith
      · have hdeficit_nonpos : partialSum C a coverOrder r - z ≤ 0 := by
          linarith
        rw [max_eq_left hdeficit_nonpos, hfinal.2]
        linarith
    · have hs_lt : s < r := lt_of_le_of_ne hs hsr
      have hs_cast : (s : ℝ) ≤ (r : ℝ) - 1 := by
        have hs_succ : s + 1 ≤ r := Nat.succ_le_iff.mpr hs_lt
        have hs_succ_cast : (s : ℝ) + 1 ≤ (r : ℝ) := by
          exact_mod_cast hs_succ
        linarith
      have hsupport_le :
          (s : ℝ) * lam - max 0 (partialSum C a coverOrder s - z) ≤
            (s : ℝ) * lam := by
        linarith [le_max_left (0 : ℝ) (partialSum C a coverOrder s - z)]
      have hfinal_ge :
          ((r : ℝ) - 1) * lam ≤
            flow_cover_lifting_function b lam (a ∘ coverOrder) z := by
        rw [hfinal.2]
        linarith [hfinal.1]
      dsimp [lam] at hsupport_le hfinal_ge ⊢
      nlinarith
  · have hs_le_q : s ≤ q := by
      by_contra hnot
      have hq_s : q + 1 ≤ s := by
        omega
      have hs_card : s ≤ C.card := le_trans hs hr.2.1
      have hpartial :
          partialSum C a coverOrder (q + 1) ≤ partialSum C a coverOrder s :=
        partialSum_mono_of_nonneg
          (a := a) (C := C) (coverOrder := coverOrder) ha_nonneg hq_s hs_card
      linarith
    rcases Nat.eq_or_lt_of_le hs_le_q with rfl | hs_lt
    · -- At the active stage, the support line is the exact profile formula.
      simpa [lam] using le_of_eq hq_value.symm
    · have hs_cast : (s : ℝ) ≤ (q : ℝ) - 1 := by
        have hs_succ : s + 1 ≤ q := Nat.succ_le_iff.mpr hs_lt
        have hs_succ_cast : (s : ℝ) + 1 ≤ (q : ℝ) := by
          exact_mod_cast hs_succ
        linarith
      have hdeficit_le : max 0 (partialSum C a coverOrder q - z) ≤ lam := by
        have hraw_le : partialSum C a coverOrder q - z ≤ lam := by
          linarith [hq_lower]
        exact max_le_iff.mpr ⟨hlam_pos.le, hraw_le⟩
      have hsupport_le :
          (s : ℝ) * lam - max 0 (partialSum C a coverOrder s - z) ≤
            (s : ℝ) * lam := by
        linarith [le_max_left (0 : ℝ) (partialSum C a coverOrder s - z)]
      have hactive_ge :
          ((q : ℝ) - 1) * lam ≤
            flow_cover_lifting_function b lam (a ∘ coverOrder) z := by
        rw [hq_value]
        linarith
      dsimp [lam] at hsupport_le hactive_ge ⊢
      nlinarith

/-- Helper for sorry cleanup existing repo batch3 ch7_sec7_3_lemma_7_14: the flow-cover lifting
function is superadditive after the cover has been put in antitone order. -/
lemma flowCoverLiftingFunction_superadditive_of_ordered
    {n : ℕ} (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (coverOrder : Fin C.card ↪ Fin n)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun i : Fin C.card ↦ a (coverOrder i)) :
    is_superadditive_on_Icc
      (flow_cover_lifting_function b (flow_cover_excess a b C) (a ∘ coverOrder)) b := by
  let lam := flow_cover_excess a b C
  have hlam_pos : 0 < lam := by
    simpa [lam] using flow_cover_excess_pos a b C hC
  have hordered_sum : ∑ i : Fin C.card, a (coverOrder i) = ∑ j ∈ C, a j := by
    have hprefix :
        partialSum C a coverOrder C.card = ∑ i : Fin C.card, a (coverOrder i) := by
      simpa using
        (prefixPenaltySum_eq
          (a := a) (C := C) (coverOrder := coverOrder) (lam := (0 : ℝ))
          (k := C.card) le_rfl).symm
    calc
      ∑ i : Fin C.card, a (coverOrder i) = partialSum C a coverOrder C.card := hprefix.symm
      _ = ∑ j ∈ C, a j := partialSum_card_eq_cover_sum a C coverOrder hcoverOrder
  have hcover_sum : b < ∑ i : Fin C.card, (a ∘ coverOrder) i := by
    simpa [Function.comp_def, hordered_sum] using hC.sum_gt_rhs
  by_cases hlarge : ∃ i : Fin C.card, lam < a (coverOrder i)
  · obtain ⟨r, hr⟩ :=
      existsCutIndex_of_exists_gt a C coverOrder lam hordered hlarge
    have hrSource :
        isCutIndex a C coverOrder (flow_cover_excess a b C) r := by
      simpa [lam] using hr
    intro u v hu hv huv
    have hprofile_u :=
      flowCoverLiftingFunction_stageProfile
        a b C coverOrder r ha_nonneg hC hcoverOrder hordered hrSource hu
    have hprofile_v :=
      flowCoverLiftingFunction_stageProfile
        a b C coverOrder r ha_nonneg hC hcoverOrder hordered hrSource hv
    rcases hprofile_u with hfinal_u | ⟨h, hh, hu_lower, hu_upper, hfu⟩
    · have hsum_final : partialSum C a coverOrder r - lam ≤ u + v := by
        linarith [hfinal_u.1, hv.1]
      have hsum_final_source :
          partialSum C a coverOrder r - flow_cover_excess a b C ≤ u + v := by
        simpa [lam] using hsum_final
      have hsum_piece :
          u + v ∈ Set.Icc
            (partialSum C a coverOrder r - flow_cover_excess a b C) b :=
        ⟨hsum_final_source, huv.2⟩
      have hsum_value :=
        flow_cover_lifting_function_eq_affine_on_final_interval
          (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r) (z := u + v)
          ha_nonneg hC hcoverOrder hordered hrSource huv hsum_piece
      have hfv_le :
          flow_cover_lifting_function b lam (a ∘ coverOrder) v ≤ v :=
        flowCoverLiftingFunction_le_self b lam (a ∘ coverOrder)
          (fun i ↦ ha_nonneg (coverOrder i)) hcover_sum hv
      have hgoal :
          flow_cover_lifting_function b lam (a ∘ coverOrder) u +
              flow_cover_lifting_function b lam (a ∘ coverOrder) v ≤
            flow_cover_lifting_function b lam (a ∘ coverOrder) (u + v) := by
        rw [hfinal_u.2, hsum_value]
        linarith
      simpa [lam] using hgoal
    · rcases hprofile_v with hfinal_v | ⟨k, hk, hv_lower, hv_upper, hfv⟩
      · have hsum_final : partialSum C a coverOrder r - lam ≤ u + v := by
          linarith [hfinal_v.1, hu.1]
        have hsum_final_source :
            partialSum C a coverOrder r - flow_cover_excess a b C ≤ u + v := by
          simpa [lam] using hsum_final
        have hsum_piece :
            u + v ∈ Set.Icc
              (partialSum C a coverOrder r - flow_cover_excess a b C) b :=
          ⟨hsum_final_source, huv.2⟩
        have hsum_value :=
          flow_cover_lifting_function_eq_affine_on_final_interval
            (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r) (z := u + v)
            ha_nonneg hC hcoverOrder hordered hrSource huv hsum_piece
        have hfu_le :
            flow_cover_lifting_function b lam (a ∘ coverOrder) u ≤ u :=
          flowCoverLiftingFunction_le_self b lam (a ∘ coverOrder)
            (fun i ↦ ha_nonneg (coverOrder i)) hcover_sum hu
        have hgoal :
            flow_cover_lifting_function b lam (a ∘ coverOrder) u +
                flow_cover_lifting_function b lam (a ∘ coverOrder) v ≤
              flow_cover_lifting_function b lam (a ∘ coverOrder) (u + v) := by
          rw [hfinal_v.2, hsum_value]
          linarith
        simpa [lam] using hgoal
      · by_cases hh_zero : h = 0
        · subst h
          have hfu_zero : flow_cover_lifting_function b lam (a ∘ coverOrder) u = 0 := by
            have hdeficit : max 0 (partialSum C a coverOrder 0 - u) = 0 := by
              simp [partialSum, hu.1]
            simpa [lam, hdeficit] using hfu
          have hv_le_sum : v ≤ u + v := by
            linarith [hu.1]
          have hmono :
              flow_cover_lifting_function b lam (a ∘ coverOrder) v ≤
                flow_cover_lifting_function b lam (a ∘ coverOrder) (u + v) :=
            flowCoverLiftingFunction_mono b lam (a ∘ coverOrder)
              (fun i ↦ ha_nonneg (coverOrder i)) hv_le_sum huv.2
          simpa [lam, hfu_zero] using hmono
        · by_cases hk_zero : k = 0
          · subst k
            have hfv_zero : flow_cover_lifting_function b lam (a ∘ coverOrder) v = 0 := by
              have hdeficit : max 0 (partialSum C a coverOrder 0 - v) = 0 := by
                simp [partialSum, hv.1]
              simpa [lam, hdeficit] using hfv
            have hu_le_sum : u ≤ u + v := by
              linarith [hv.1]
            have hmono :
                flow_cover_lifting_function b lam (a ∘ coverOrder) u ≤
                  flow_cover_lifting_function b lam (a ∘ coverOrder) (u + v) :=
              flowCoverLiftingFunction_mono b lam (a ∘ coverOrder)
                (fun i ↦ ha_nonneg (coverOrder i)) hu_le_sum huv.2
            simpa [lam, hfv_zero] using hmono
          · have hh_pos : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr hh_zero
            have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk_zero
            let A := max 0 (partialSum C a coverOrder h - u)
            let B := max 0 (partialSum C a coverOrder k - v)
            have hA_nonneg : 0 ≤ A := le_max_left _ _
            have hB_nonneg : 0 ≤ B := le_max_left _ _
            have hu_mu : partialSum C a coverOrder h ≤ u + A := by
              dsimp [A]
              linarith [le_max_right (0 : ℝ) (partialSum C a coverOrder h - u)]
            have hv_mu : partialSum C a coverOrder k ≤ v + B := by
              dsimp [B]
              linarith [le_max_right (0 : ℝ) (partialSum C a coverOrder k - v)]
            have hsum_value :
                flow_cover_lifting_function b lam (a ∘ coverOrder) u +
                    flow_cover_lifting_function b lam (a ∘ coverOrder) v =
                  (h + k : ℕ) * lam - (A + B) := by
              dsimp [A, B]
              rw [hfu, hfv]
              push_cast
              ring
            have hD :=
              adjustedPartialSum_min_add_le
                a b C coverOrder r hordered hrSource hh.le hk.le
            by_cases hsum_le : h + k ≤ r
            · have hmin : min r (h + k) = h + k := Nat.min_eq_right hsum_le
              rw [hmin] at hD
              push_cast at hD
              have hpartial :
                  partialSum C a coverOrder (h + k) ≤
                    partialSum C a coverOrder h + partialSum C a coverOrder k := by
                linarith
              by_cases hAB : A + B < lam
              · have hraw :
                    partialSum C a coverOrder (h + k) - (u + v) ≤ A + B := by
                  linarith [hu_mu, hv_mu, hpartial]
                have hstart :
                    partialSum C a coverOrder (h + k) - lam ≤ u + v := by
                  linarith
                have hstartSource :
                    partialSum C a coverOrder (h + k) - flow_cover_excess a b C ≤
                      u + v := by
                  simpa [lam] using hstart
                have hmax :
                    max 0 (partialSum C a coverOrder (h + k) - (u + v)) ≤ A + B :=
                  max_le_iff.mpr ⟨add_nonneg hA_nonneg hB_nonneg, hraw⟩
                have hsupport :=
                  flowCoverLiftingFunction_stageSupport
                    a b C coverOrder r ha_nonneg hC hcoverOrder hordered
                    hrSource hsum_le huv hstartSource
                rw [hsum_value]
                have hgoal :
                    (h + k : ℕ) * lam - (A + B) ≤
                      flow_cover_lifting_function b lam (a ∘ coverOrder) (u + v) := by
                  push_cast
                  linarith
                simpa [lam] using hgoal
              · have hAB_ge : lam ≤ A + B := le_of_not_gt hAB
                let s := h + k - 1
                have hs_lt : s < r := by
                  dsimp [s]
                  omega
                have hs_succ : s + 1 = h + k := by
                  dsimp [s]
                  omega
                have hweight_pos : lam < weight C a coverOrder (s + 1) := by
                  simpa [lam] using
                    coverWeight_gt_excess_before_cutIndex
                      (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r)
                      hordered hrSource hs_lt
                have hprev :
                    partialSum C a coverOrder s + lam ≤
                      partialSum C a coverOrder h + partialSum C a coverOrder k := by
                  rw [← hs_succ, partialSum_succ] at hpartial
                  linarith
                have hstart : partialSum C a coverOrder s - lam ≤ u + v := by
                  have hu_start : partialSum C a coverOrder h - lam ≤ u := by
                    simpa [lam] using hu_lower
                  have hv_start : partialSum C a coverOrder k - lam ≤ v := by
                    simpa [lam] using hv_lower
                  linarith
                have hstartSource :
                    partialSum C a coverOrder s - flow_cover_excess a b C ≤ u + v := by
                  simpa [lam] using hstart
                have hraw :
                    partialSum C a coverOrder s - (u + v) ≤ A + B - lam := by
                  linarith [hu_mu, hv_mu, hprev]
                have hmax :
                    max 0 (partialSum C a coverOrder s - (u + v)) ≤ A + B - lam := by
                  have hright_nonneg : 0 ≤ A + B - lam := by
                    linarith
                  exact max_le_iff.mpr ⟨hright_nonneg, hraw⟩
                have hs_le : s ≤ r := hs_lt.le
                have hsupport :=
                  flowCoverLiftingFunction_stageSupport
                    a b C coverOrder r ha_nonneg hC hcoverOrder hordered
                    hrSource hs_le huv hstartSource
                have hs_cast : (s : ℝ) = ((h + k : ℕ) : ℝ) - 1 := by
                  have hsum_pos : 1 ≤ h + k := by
                    omega
                  dsimp [s]
                  rw [Nat.cast_sub hsum_pos]
                  norm_num
                rw [hsum_value]
                have hgoal :
                    (h + k : ℕ) * lam - (A + B) ≤
                      flow_cover_lifting_function b lam (a ∘ coverOrder) (u + v) := by
                  rw [hs_cast] at hsupport
                  push_cast
                  nlinarith
                simpa [lam] using hgoal
            · have hr_sum : r + 1 ≤ h + k := by
                omega
              have hmin : min r (h + k) = r := Nat.min_eq_left (Nat.le_of_not_ge hsum_le)
              rw [hmin] at hD
              have hgap_cast : (1 : ℝ) ≤ (h + k : ℕ) - (r : ℝ) := by
                have hr_cast : (r : ℝ) + 1 ≤ ((h + k : ℕ) : ℝ) := by
                  exact_mod_cast hr_sum
                linarith
              have hsum_final : partialSum C a coverOrder r - lam ≤ u + v := by
                have hu_start : partialSum C a coverOrder h - lam ≤ u := by
                  simpa [lam] using hu_lower
                have hv_start : partialSum C a coverOrder k - lam ≤ v := by
                  simpa [lam] using hv_lower
                nlinarith
              have hsum_final_source :
                  partialSum C a coverOrder r - flow_cover_excess a b C ≤ u + v := by
                simpa [lam] using hsum_final
              have hsum_piece :
                  u + v ∈ Set.Icc
                    (partialSum C a coverOrder r - flow_cover_excess a b C) b :=
                ⟨hsum_final_source, huv.2⟩
              have hsum_final_value :=
                flow_cover_lifting_function_eq_affine_on_final_interval
                  (a := a) (b := b) (C := C) (coverOrder := coverOrder) (r := r) (z := u + v)
                  ha_nonneg hC hcoverOrder hordered hrSource huv hsum_piece
              rw [hsum_value]
              have hgoal :
                  (h + k : ℕ) * lam - (A + B) ≤
                    flow_cover_lifting_function b lam (a ∘ coverOrder) (u + v) := by
                rw [hsum_final_value]
                push_cast
                nlinarith [hu_mu, hv_mu]
              simpa [lam] using hgoal
  · have ha_le : ∀ i : Fin C.card, (a ∘ coverOrder) i ≤ lam := by
      intro i
      exact le_of_not_gt (not_exists.mp hlarge i)
    intro u v hu hv huv
    -- With no positive penalty coefficient, all three lifting values are their arguments.
    rw [flowCoverLiftingFunction_eq_self_of_forall_le b lam (a ∘ coverOrder)
        (fun i ↦ ha_nonneg (coverOrder i)) hcover_sum ha_le hu,
      flowCoverLiftingFunction_eq_self_of_forall_le b lam (a ∘ coverOrder)
        (fun i ↦ ha_nonneg (coverOrder i)) hcover_sum ha_le hv,
      flowCoverLiftingFunction_eq_self_of_forall_le b lam (a ∘ coverOrder)
        (fun i ↦ ha_nonneg (coverOrder i)) hcover_sum ha_le huv]

/- Lemma 7.14 is the `source-facing` theorem asserting that the flow-cover lifting function for a
nonnegative ordered flow cover with canonical excess `flow_cover_excess a b Finset.univ` is
superadditive on `[0, b]`.
Exercise 7.16 reuses this exact statement as a `bridge/view` recall, so the owner declaration
lives here in Section 7.3 rather than downstream in the exercise file. -/
/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_lemma_7_14.lean
Lemma 7.14. For nonnegative
ordered coefficients whose full support is a flow cover, the flow-cover lifting function with
excess `flow_cover_excess a b Finset.univ` is superadditive on `[0, b]`. -/
theorem flow_cover_lifting_function_is_superadditive_on_Icc
    {t : ℕ} (b : ℝ) (a : Fin t → ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b Finset.univ) :
    is_superadditive_on_Icc
      (flow_cover_lifting_function b (flow_cover_excess a b Finset.univ) a) b := by
  classical
  -- Sort the full cover once, prove the ordered statement, and transport all three evaluations
  -- back through the same coordinate equivalence.
  obtain ⟨e, hcoverOrder, hordered⟩ := existsAntitoneFullCoverOrder a
  have horderedEmbedding : Antitone (a ∘ e.toEmbedding) := by
    simpa using hordered
  have hsuperOrdered :=
    flowCoverLiftingFunction_superadditive_of_ordered
      a b Finset.univ e.toEmbedding ha_nonneg hC hcoverOrder horderedEmbedding
  have hsuperEquiv :
      is_superadditive_on_Icc
        (flow_cover_lifting_function b (flow_cover_excess a b Finset.univ) (a ∘ e)) b := by
    simpa using hsuperOrdered
  intro u v hu hv huv
  calc
    flow_cover_lifting_function b (flow_cover_excess a b Finset.univ) a u +
        flow_cover_lifting_function b (flow_cover_excess a b Finset.univ) a v =
      flow_cover_lifting_function b (flow_cover_excess a b Finset.univ) (a ∘ e) u +
        flow_cover_lifting_function b (flow_cover_excess a b Finset.univ) (a ∘ e) v := by
          rw [flowCoverLiftingFunction_comp_equiv e b
              (flow_cover_excess a b Finset.univ) u a,
            flowCoverLiftingFunction_comp_equiv e b
              (flow_cover_excess a b Finset.univ) v a]
    _ ≤ flow_cover_lifting_function b (flow_cover_excess a b Finset.univ) (a ∘ e) (u + v) :=
      hsuperEquiv hu hv huv
    _ = flow_cover_lifting_function b (flow_cover_excess a b Finset.univ) a (u + v) :=
      flowCoverLiftingFunction_comp_equiv e b
        (flow_cover_excess a b Finset.univ) (u + v) a

end Lemma714

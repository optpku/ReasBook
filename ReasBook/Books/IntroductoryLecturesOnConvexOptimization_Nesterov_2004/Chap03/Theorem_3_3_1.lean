/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_71
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_1

noncomputable section

open scoped LevelMethodNotation

/- Theorem 3.3.1 lies in the chapter's level-method scalar-history domain.

Sampled owner declarations:
* `LevelMethodHistory` in `Lemma_3_3_1`, the owner bundle for `(\hat f_k^*, f_k^*)`
* `LevelMethodHistory.gap` in `Lemma_3_3_1`, the canonical gap `δ_k`
* `LevelMethodHistory.shouldStop` in `Lemma_3_3_1`, the canonical stopping predicate `δ_k ≤ ε`
* `LevelMethodHistory.optimalValue_sub_fStar_le_epsilon_of_shouldStop` in `Lemma_3_3_1`, the
  owner consequence of the stopping test

Best owner abstraction:
* `LevelMethodHistory`

Primitive data:
* `history.approximateOptimalValue`
* `history.optimalValue`

Derived API:
* `history.gap`
* `history.shouldStop`

This file therefore keeps only the iteration-cap statement and reuses the scalar-history owner API
instead of repeating separate global definitions for the gap and stopping rule.
-/

/-- The textbook worst-case iteration cap
`⌊M_f^2 D^2 / (ε^2 α (1 - α)^2 (2 - α))⌋ + 1` for the Level Method. -/
def levelMethodIterationCap (M_f D ε α : ℝ) : ℕ :=
  Nat.floor
      (M_f ^ (2 : ℕ) * D ^ (2 : ℕ) /
        (ε ^ (2 : ℕ) * levelParameterObjective α)) +
    1

/-- Helper for Theorem 3.3.1: a positive terminal gap determines the minimal start of the last
block whose terminal gap is still at least `(1 - α)` times the block-start gap. -/
private theorem minimal_block_start_of_gap_pos
    (history : LevelMethodHistory) {α : ℝ} {p : ℕ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hgap_pos : 0 < δ[history](p)) :
    ∃ k ≤ p,
      δ[history](p) ≥ (1 - α) * δ[history](k) ∧
      ∀ ⦃i : ℕ⦄, i < k → δ[history](p) < (1 - α) * δ[history](i) := by
  rcases hα with ⟨hα0, hα1⟩
  let P : ℕ → Prop := fun k ↦
    k ≤ p ∧ δ[history](p) ≥ (1 - α) * δ[history](k)
  have hP : ∃ k, P k := by
    refine ⟨p, le_rfl, ?_⟩
    -- The terminal index itself is admissible because `α * δ_p > 0`.
    have hscaled_lt : (1 - α) * δ[history](p) < δ[history](p) := by
      nlinarith [mul_pos hα0 hgap_pos]
    exact hscaled_lt.le
  refine ⟨Nat.find hP, (Nat.find_spec hP).1, (Nat.find_spec hP).2, ?_⟩
  intro i hik
  have hnot : ¬ P i := Nat.find_min hP hik
  have hnot_large : ¬ δ[history](p) ≥ (1 - α) * δ[history](i) := by
    intro hlarge
    have hip : i ≤ p := (Nat.le_of_lt hik).trans (Nat.find_spec hP).1
    exact hnot ⟨hip, hlarge⟩
  exact lt_of_not_ge hnot_large

/-- Helper for Theorem 3.3.1: the scaled-threshold prefix contribution and the terminal-block
contribution add up to the full iteration-cap denominator. -/
private theorem scaled_tolerance_prefix_denominator_eq
    {α τ C : ℝ}
    (hτ : 0 < τ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    C / (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) +
      C / ((1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ)) =
      C / (τ ^ (2 : ℕ) * levelParameterObjective α) := by
  rcases hα with ⟨hα0, hα1⟩
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ
  have hOneSub_ne : 1 - α ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα1)
  have hTwoSub_ne : 2 - α ≠ 0 := sub_ne_zero.mpr (by linarith)
  -- Clear the denominators once and reduce the claim to a polynomial identity.
  have hlevel_pos : 0 < levelParameterObjective α := levelParameterObjective_pos ⟨hα0, hα1⟩
  unfold levelParameterObjective
  field_simp [hτ_ne, hOneSub_ne, hTwoSub_ne, ne_of_gt hlevel_pos]
  ring

/-- Helper for Theorem 3.3.1: if every gap on a prefix stays above a threshold `τ`, then the
prefix length is controlled by the chapter's iteration-cap quotient. -/
private theorem prefix_length_le_div_of_forall_lt_gap
    (history : LevelMethodHistory) {M_f D α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hblock :
      ∀ {k p : ℕ}, k ≤ p →
        δ[history](p) ≥ (1 - α) * δ[history](k) →
        0 < δ[history](p) →
        ((p + 1 - k : ℕ) : ℝ) ≤
          (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ))) :
    ∀ p : ℕ, ∀ τ : ℝ,
      0 < τ →
      (∀ i ≤ p, τ < δ[history](i)) →
      ((p + 1 : ℕ) : ℝ) ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          (τ ^ (2 : ℕ) * levelParameterObjective α) := by
  intro p
  refine Nat.strong_induction_on p ?_
  intro p ih τ hτ hgap_gt
  have hOneSub_pos : 0 < 1 - α := sub_pos.mpr hα.2
  have hnum_nonneg : 0 ≤ M_f ^ (2 : ℕ) * D ^ (2 : ℕ) := by
    positivity
  have hgap_p : τ < δ[history](p) := hgap_gt p le_rfl
  have hgap_p_pos : 0 < δ[history](p) := lt_trans hτ hgap_p
  -- Pick the minimal start of the last block ending at `p`.
  obtain ⟨k, hkp, hgap_large, hminimal⟩ :=
    minimal_block_start_of_gap_pos history hα hgap_p_pos
  have hlast_raw :
      ((p + 1 - k : ℕ) : ℝ) ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ)) :=
    hblock hkp hgap_large hgap_p_pos
  have hsq_le : τ ^ (2 : ℕ) ≤ δ[history](p) ^ (2 : ℕ) := by
    nlinarith
  have hden_le :
      (1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ) ≤
        (1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hsq_le (by positivity)
  have hden_pos : 0 < (1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ) := by
    positivity
  have hlast :
      ((p + 1 - k : ℕ) : ℝ) ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          ((1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ)) :=
    hlast_raw.trans <|
      div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
  have hprefix :
      (k : ℝ) ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) := by
    by_cases hk : k = 0
    · -- No earlier prefix remains when the last block starts at zero.
      have hscaled_den_pos :
          0 <
            ((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α := by
        have hτ_scaled : 0 < τ / (1 - α) := div_pos hτ hOneSub_pos
        exact mul_pos (by positivity) (levelParameterObjective_pos hα)
      have hzero_bound :
          (0 : ℝ) ≤
            (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
              (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) :=
        div_nonneg hnum_nonneg hscaled_den_pos.le
      simpa [hk] using hzero_bound
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      have hτ_scaled : 0 < τ / (1 - α) := div_pos hτ hOneSub_pos
      have hscaled_gap_gt :
          ∀ i ≤ k - 1, τ / (1 - α) < δ[history](i) := by
        intro i hik
        have hik_lt : i < k := lt_of_le_of_lt hik (Nat.sub_one_lt hk)
        have hlt_scaled : τ < (1 - α) * δ[history](i) :=
          (hgap_gt p le_rfl).trans (hminimal hik_lt)
        -- Minimality of `k` forces the previous block-start gaps to grow by `(1 - α)⁻¹`.
        rw [div_lt_iff₀ hOneSub_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hlt_scaled
      have hprefix_raw :
          ((k - 1 + 1 : ℕ) : ℝ) ≤
            (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
              (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) :=
        ih (k - 1) (lt_of_lt_of_le (Nat.sub_one_lt hk) hkp) (τ / (1 - α)) hτ_scaled
          hscaled_gap_gt
      have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk_pos)
      simpa [hk_eq] using hprefix_raw
  have hdecomp_nat : k + (p + 1 - k) = p + 1 :=
    Nat.add_sub_of_le (hkp.trans (Nat.le_succ p))
  have hdecomp_real : (k : ℝ) + ((p + 1 - k : ℕ) : ℝ) = ((p + 1 : ℕ) : ℝ) := by
    exact_mod_cast hdecomp_nat
  -- Add the prefix estimate and the last-block estimate, then collapse the scalar identity.
  calc
    ((p + 1 : ℕ) : ℝ) = (k : ℝ) + ((p + 1 - k : ℕ) : ℝ) := by
      symm
      exact hdecomp_real
    _ ≤
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            (((τ / (1 - α)) ^ (2 : ℕ)) * levelParameterObjective α) +
          (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * τ ^ (2 : ℕ)) :=
      add_le_add hprefix hlast
    _ =
        (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          (τ ^ (2 : ℕ) * levelParameterObjective α) :=
      scaled_tolerance_prefix_denominator_eq hτ hα

/-- Theorem 3.3.1 (iteration-cap part): if each level-method block `[k, p]` that is still in the
positive-gap regime and satisfies `δ_p ≥ (1 - α) δ_k` obeys the interval bound from
Lemma `3.3.3`, then the Level Method reaches the canonical stopping predicate `δ_k ≤ ε` after at
most
`⌊M_f^2 D^2 / (ε^2 α (1 - α)^2 (2 - α))⌋ + 1` iterations. -/
-- Proof sketch: argue by contradiction and assume `history.gap k > ε` for every
-- `k ≤ levelMethodIterationCap M_f D ε α`. Partition the indices into maximal consecutive blocks
-- on which the terminal gap stays at least `(1 - α)` times the initial gap. The block bound
-- `hblock` controls the length of each block, while the block-start gaps grow geometrically by
-- the factor `(1 - α)⁻¹`; summing the resulting geometric series yields the displayed iteration
-- cap.
theorem exists_stopping_index_le_levelMethodIterationCap
    (history : LevelMethodHistory) {M_f D ε α : ℝ}
    (hε : 0 < ε)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hblock :
      ∀ {k p : ℕ}, k ≤ p →
        δ[history](p) ≥ (1 - α) * δ[history](k) →
        0 < δ[history](p) →
        ((p + 1 - k : ℕ) : ℝ) ≤
          (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ))) :
    ∃ k ≤ levelMethodIterationCap M_f D ε α,
      history.shouldStop ε k := by
  let R :=
    (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
      (ε ^ (2 : ℕ) * levelParameterObjective α)
  let p := Nat.floor R
  by_contra hnostop
  push Not at hnostop
  have hgap_gt :
      ∀ i ≤ p, ε < δ[history](i) := by
    intro i hip
    have hi_cap : i ≤ levelMethodIterationCap M_f D ε α := by
      -- The contradiction uses the whole floor-prefix `[0, p]`.
      dsimp [p, R]
      unfold levelMethodIterationCap
      exact hip.trans (Nat.le_succ _)
    have hi_not_stop : ¬ history.shouldStop ε i := hnostop i hi_cap
    rw [LevelMethodHistory.shouldStop_iff] at hi_not_stop
    exact lt_of_not_ge hi_not_stop
  have hprefix :
      ((p + 1 : ℕ) : ℝ) ≤ R := by
    dsimp [R]
    exact prefix_length_le_div_of_forall_lt_gap history hα hblock p ε hε hgap_gt
  have hprefix' : (p : ℝ) + 1 ≤ R := by
    simpa [Nat.cast_add] using hprefix
  have hfloor : R < (p : ℝ) + 1 := by
    simpa [p, Nat.cast_add] using Nat.lt_floor_add_one R
  -- The prefix bound contradicts the universal property of `Nat.floor`.
  linarith

/-- Theorem 3.3.1: if each level-method block `[k, p]` that is still in the positive-gap regime
and satisfies `δ_p ≥ (1 - α) δ_k` obeys the interval bound from Lemma `3.3.3`, then the Level
Method terminates after at most
`⌊M_f^2 D^2 / (ε^2 α (1 - α)^2 (2 - α))⌋ + 1` iterations. Moreover, the stopping criterion
guarantees `f_k^* - f^* ≤ ε`. -/
-- Proof sketch: argue by contradiction and assume `history.gap k > ε` for every
-- `k ≤ levelMethodIterationCap M_f D ε α`. Partition the indices into maximal consecutive blocks
-- on which the terminal gap stays at least `(1 - α)` times the initial gap. The block bound
-- `hblock` controls the length of each block, while the block-start gaps grow geometrically by
-- the factor `(1 - α)⁻¹`; summing the resulting geometric series yields the displayed iteration
-- cap, yielding `exists_stopping_index_le_levelMethodIterationCap`. For the optimality-gap claim,
-- apply
-- `history.optimalValue_sub_fStar_le_epsilon_of_shouldStop`.
theorem exists_stopping_index_le_levelMethodIterationCap_and_optimalValue_sub_fStar_le_epsilon
    (history : LevelMethodHistory) {fStar M_f D ε α : ℝ}
    (hε : 0 < ε)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hvalidLower : ∀ k : ℕ, history.approximateOptimalValue k ≤ fStar)
    (hblock :
      ∀ {k p : ℕ}, k ≤ p →
        δ[history](p) ≥ (1 - α) * δ[history](k) →
        0 < δ[history](p) →
        ((p + 1 - k : ℕ) : ℝ) ≤
          (M_f ^ (2 : ℕ) * D ^ (2 : ℕ)) /
            ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ))) :
    (∃ k ≤ levelMethodIterationCap M_f D ε α,
      history.shouldStop ε k) ∧
      ∀ k : ℕ,
        history.shouldStop ε k →
          history.optimalValue k - fStar ≤ ε := by
  refine ⟨exists_stopping_index_le_levelMethodIterationCap history hε hα hblock, ?_⟩
  intro k hk
  exact history.optimalValue_sub_fStar_le_epsilon_of_shouldStop k (hvalidLower k) hk

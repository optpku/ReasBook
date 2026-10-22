/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_49
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Example_18_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Remark_14_31
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

local notation "AxisState" => ℤ × ℤ

/-- Helper for Exercise 18.2.4: applying a measurable state map coordinatewise can only shrink
the generated history filtration. -/
private lemma generatedFiltrationSpace_comp_le {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (X : ℕ → Ω → α) (f : α → β) (hf : Measurable f) (s : ℕ) :
    generatedFiltrationSpace (fun n ω ↦ f (X n ω)) s ≤ generatedFiltrationSpace X s := by
  rw [generatedFiltrationSpace]
  refine iSup_le fun n ↦ ?_
  refine iSup_le fun hn ↦ ?_
  have hXn :
      Measurable[generatedFiltrationSpace X s] (X n) := by
    exact Measurable.of_comap_le <| le_iSup_of_le n <| le_iSup_of_le hn le_rfl
  exact (hf.comp hXn).comap_le

/-- Helper for Exercise 18.2.4: the present coordinate sigma-algebra is contained in the
generated history filtration. -/
private lemma present_le_generatedHistory {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (s : ℕ) :
    MeasurableSpace.comap (X s) ‹MeasurableSpace α› ≤ generatedFiltrationSpace X s := by
  exact le_iSup_of_le s <| le_iSup_of_le le_rfl le_rfl

/-- Helper for Exercise 18.2.4: if all process coordinates are ambient-measurable, then the
generated history filtration is bounded by the ambient measurable space. -/
private lemma generatedHistory_le_ambient {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (X : ℕ → Ω → α) (hX : ∀ n : ℕ, Measurable (X n)) (s : ℕ) :
    generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
  refine iSup_le fun n ↦ ?_
  refine iSup_le fun hn ↦ ?_
  exact (hX n).comap_le

private abbrev isHorizontalNeighbor (x y : AxisState) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2)

private abbrev isVerticalNeighbor (x y : AxisState) : Prop :=
  (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨ (y.1 = x.1 ∧ y.2 = x.2 - 1)

private abbrev isAxisNeighbor (x y : AxisState) : Prop :=
  isHorizontalNeighbor x y ∨ isVerticalNeighbor x y

/-- Helper for Exercise 18.2.4: `sampledFiniteHistoryEvent X times states` records the finite
history where `X (times k)` is fixed to `states k` for every sampled index `k`. -/
private def sampledFiniteHistoryEvent {Ω : Type*} [MeasurableSpace Ω] {T : Type*} {E : Type*}
    (X : T → Ω → E) {n : ℕ} (times : Fin (n + 1) → T) (states : Fin (n + 1) → E) : Set Ω :=
  {ω | ∀ k, X (times k) ω = states k}

/-- Helper for Exercise 18.2.4: a sampled finite-history event is the singleton fiber of its
history tuple. -/
private theorem sampledFiniteHistoryEvent_eq_preimage_historyTuple
    {Ω : Type*} [MeasurableSpace Ω] {T : Type*} {E : Type*}
    (X : T → Ω → E) {n : ℕ} (times : Fin (n + 1) → T) (states : Fin (n + 1) → E) :
    sampledFiniteHistoryEvent X times states = (fun ω k ↦ X (times k) ω) ⁻¹' {states} := by
  ext ω
  simp [sampledFiniteHistoryEvent, funext_iff]

/-- Helper for Exercise 18.2.4: a sampled finite-history event lies inside the fiber of its last
sampled state. -/
private theorem sampledFiniteHistoryEvent_subset_terminalFiber
    {Ω : Type*} [MeasurableSpace Ω] {T : Type*} {E : Type*}
    (X : T → Ω → E) {n : ℕ} (times : Fin (n + 1) → T) (states : Fin (n + 1) → E) :
    sampledFiniteHistoryEvent X times states ⊆
      {ω | X (times (Fin.last n)) ω = states (Fin.last n)} := by
  intro ω hω
  exact hω (Fin.last n)

/-- Helper for Exercise 18.2.4: horizontal nearest-neighbor adjacency is symmetric. -/
private theorem isHorizontalNeighbor_symm {x y : AxisState} :
    isHorizontalNeighbor x y ↔ isHorizontalNeighbor y x := by
  constructor
  · intro hxy
    rcases hxy with hxy | hxy
    · rcases hxy with ⟨h1, h2⟩
      right
      constructor
      · omega
      · simpa [h2]
    · rcases hxy with ⟨h1, h2⟩
      left
      constructor
      · omega
      · simpa [h2]
  · intro hyx
    rcases hyx with hyx | hyx
    · rcases hyx with ⟨h1, h2⟩
      right
      constructor
      · omega
      · simpa [h2]
    · rcases hyx with ⟨h1, h2⟩
      left
      constructor
      · omega
      · simpa [h2]

/-- Helper for Exercise 18.2.4: vertical nearest-neighbor adjacency on the axis is symmetric. -/
private theorem isVerticalNeighbor_symm {x y : AxisState} :
    isVerticalNeighbor x y ↔ isVerticalNeighbor y x := by
  constructor
  · intro hxy
    rcases hxy with hxy | hxy
    · rcases hxy with ⟨h1, h2⟩
      right
      constructor
      · simpa [h1]
      · omega
    · rcases hxy with ⟨h1, h2⟩
      left
      constructor
      · simpa [h1]
      · omega
  · intro hyx
    rcases hyx with hyx | hyx
    · rcases hyx with ⟨h1, h2⟩
      right
      constructor
      · simpa [h1]
      · omega
    · rcases hyx with ⟨h1, h2⟩
      left
      constructor
      · simpa [h1]
      · omega

/-- Helper for Exercise 18.2.4: the axis-neighbor relation is symmetric. -/
private theorem isAxisNeighbor_symm {x y : AxisState} :
    isAxisNeighbor x y ↔ isAxisNeighbor y x := by
  simp [isAxisNeighbor, isHorizontalNeighbor_symm, isVerticalNeighbor_symm]

/-- Helper for Exercise 18.2.4: when `x` lies on the axis and `y` does not, every axis-neighbor of
`x` is necessarily horizontal. -/
private theorem isAxisNeighbor_iff_horizontalNeighbor_of_axis_offAxis {x y : AxisState}
    (hx : x.1 = 0) (hy : y.1 ≠ 0) :
    isAxisNeighbor x y ↔ isHorizontalNeighbor x y := by
  constructor
  · intro hxy
    rcases hxy with hxy | hxy
    · exact hxy
    · rcases hxy with hxy | hxy
      · rcases hxy with ⟨h1, _⟩
        exact (hy (by simpa [hx] using h1)).elim
      · rcases hxy with ⟨h1, _⟩
        exact (hy (by simpa [hx] using h1)).elim
  · intro hxy
    exact Or.inl hxy

/-- The transition matrix of the walk on `ℤ²` whose vertical moves are blocked away from the
vertical axis: on the axis it is the symmetric nearest-neighbor walk, while off the axis it moves
horizontally by `±1` with probability `1 / 4` each and otherwise stays put with probability
`1 / 2`. -/
def vertical_axis_blocked_walk_transition_matrix : AxisState → AxisState → ℝ≥0∞
  | x, y =>
      if x.1 = 0 then
        if isAxisNeighbor x y then
          1 / 4
        else
          0
      else if isHorizontalNeighbor x y then
        1 / 4
      else if y = x then
        1 / 2
      else
        0

-- Proof sketch: this is just the defining case split for
-- `vertical_axis_blocked_walk_transition_matrix`.
/-- The axis-blocked walk transition matrix is given by the stated axis and off-axis cases. -/
theorem vertical_axis_blocked_walk_transition_matrix_apply (x y : AxisState) :
    vertical_axis_blocked_walk_transition_matrix x y =
      if x.1 = 0 then
        if (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨
            (y.1 = x.1 - 1 ∧ y.2 = x.2) ∨
            (y.1 = x.1 ∧ y.2 = x.2 + 1) ∨
            (y.1 = x.1 ∧ y.2 = x.2 - 1) then
          1 / 4
        else
          0
      else if (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 - 1 ∧ y.2 = x.2) then
        1 / 4
      else if y = x then
        1 / 2
      else
        0 := by
  simp [vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor,
    isHorizontalNeighbor, isVerticalNeighbor, or_assoc]

/-- Helper for Exercise 18.2.4: away from the axis, keeping the first coordinate fixed forces the
blocked walk either to stay put with probability `1 / 2` or to have probability `0`. -/
private theorem vertical_axis_blocked_walk_transition_matrix_offAxis_sameFirstCoordinate
    {x1 x2 z2 : ℤ} (hx1 : x1 ≠ 0) :
    vertical_axis_blocked_walk_transition_matrix (x1, x2) (x1, z2) =
      if z2 = x2 then 1 / 2 else 0 := by
  by_cases hz : z2 = x2
  · -- Proof comment: off the axis the only transition with unchanged first coordinate is the
    -- self-loop.
    subst hz
    have hhor : ¬ isHorizontalNeighbor (x1, z2) (x1, z2) := by
      intro h
      rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    simp [vertical_axis_blocked_walk_transition_matrix, hx1, hhor]
  · -- Proof comment: if the second coordinate changes while the first one stays fixed, no
    -- off-axis branch of the transition matrix applies.
    have hhor : ¬ isHorizontalNeighbor (x1, x2) (x1, z2) := by
      intro h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hz (by omega)
      · exact hz (by omega)
    have hneq : ((x1, z2) : AxisState) ≠ (x1, x2) := by
      intro h
      exact hz (by simpa using congrArg Prod.snd h)
    simp [vertical_axis_blocked_walk_transition_matrix, hx1, hhor, hneq, hz]

/-- Helper for Exercise 18.2.4: away from the axis, every one-step transition keeps the second
coordinate fixed. -/
private theorem vertical_axis_blocked_walk_transition_matrix_offAxis_diffSecond_zero
    {x1 x2 y1 z2 : ℤ} (hx1 : x1 ≠ 0) (hz2 : z2 ≠ x2) :
    vertical_axis_blocked_walk_transition_matrix (x1, x2) (y1, z2) = 0 := by
  have hhor : ¬ isHorizontalNeighbor (x1, x2) (y1, z2) := by
    intro h
    rcases h with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact hz2 h2
    · exact hz2 h2
  have hneq : ((y1, z2) : AxisState) ≠ (x1, x2) := by
    intro h
    exact hz2 (by simpa using congrArg Prod.snd h)
  -- Proof comment: once the second coordinate changes, the off-axis row misses both the
  -- horizontal-neighbor branch and the self-loop branch.
  simp [vertical_axis_blocked_walk_transition_matrix, hx1, hhor, hneq]

/-- Helper for Exercise 18.2.4: on the axis, keeping the first coordinate fixed means moving
vertically by one step, each with probability `1 / 4`. -/
private theorem vertical_axis_blocked_walk_transition_matrix_onAxis_sameFirstCoordinate
    (x2 z2 : ℤ) :
    vertical_axis_blocked_walk_transition_matrix (0, x2) (0, z2) =
      if z2 = x2 + 1 then 1 / 4 else if z2 = x2 - 1 then 1 / 4 else 0 := by
  by_cases hplus : z2 = x2 + 1
  · -- Proof comment: the upper vertical neighbor selects one of the axis branches.
    simp [vertical_axis_blocked_walk_transition_matrix, hplus, isAxisNeighbor,
      isHorizontalNeighbor, isVerticalNeighbor]
  · by_cases hminus : z2 = x2 - 1
    · -- Proof comment: the lower vertical neighbor is the symmetric remaining axis branch.
      simp [vertical_axis_blocked_walk_transition_matrix, hplus, hminus, isAxisNeighbor,
        isHorizontalNeighbor, isVerticalNeighbor]
    · -- Proof comment: with the first coordinate fixed, every non-neighbor target has zero mass
      -- on the axis.
      have haxis : ¬ isAxisNeighbor (0, x2) (0, z2) := by
        simp [isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, hplus, hminus]
      simp [vertical_axis_blocked_walk_transition_matrix, hplus, hminus, haxis]

/-- Helper for Exercise 18.2.4: the first coordinate of the axis-blocked walk evolves as the
lazy nearest-neighbor walk on `ℤ` with probabilities `1 / 4`, `1 / 2`, and `1 / 4`. -/
private def axisBlockedFirstCoordinateTransitionMatrix : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦
    if y = x + 1 then
      1 / 4
    else if y = x then
      1 / 2
    else if y = x - 1 then
      1 / 4
    else
      0

/-- Helper for Exercise 18.2.4: each row of the lazy first-coordinate transition matrix has total
mass `1`. -/
private theorem axisBlockedFirstCoordinateTransitionMatrix_tsum (x : ℤ) :
    ∑' y : ℤ, axisBlockedFirstCoordinateTransitionMatrix x y = 1 := by
  have hsplit :
      (fun y : ℤ ↦ axisBlockedFirstCoordinateTransitionMatrix x y) =
        fun y : ℤ ↦
          (if y = x + 1 then (1 / 4 : ℝ≥0∞) else 0) +
            ((if y = x then (1 / 2 : ℝ≥0∞) else 0) +
              (if y = x - 1 then (1 / 4 : ℝ≥0∞) else 0)) := by
    funext y
    by_cases hplus : y = x + 1
    · have hzero : y ≠ x := by omega
      have hminus : y ≠ x - 1 := by omega
      have hneq : x + 1 ≠ x - 1 := by omega
      simp [axisBlockedFirstCoordinateTransitionMatrix, hplus, hzero, hminus, hneq]
    · by_cases hzero : y = x
      · have hminus : y ≠ x - 1 := by omega
        have hneq : x ≠ x - 1 := by omega
        simp [axisBlockedFirstCoordinateTransitionMatrix, hplus, hzero, hminus, hneq]
      · by_cases hminus : y = x - 1
        · have hneq : x - 1 ≠ x + 1 := by omega
          simp [axisBlockedFirstCoordinateTransitionMatrix, hplus, hzero, hminus, hneq]
        · simp [axisBlockedFirstCoordinateTransitionMatrix, hplus, hzero, hminus]
  rw [hsplit, ENNReal.tsum_add, ENNReal.tsum_add]
  have hplus :
      ∑' y : ℤ, (if y = x + 1 then (1 / 4 : ℝ≥0∞) else 0) = 1 / 4 := by
    rw [tsum_eq_single (x + 1)]
    · simp
    · intro b hb
      simp [hb]
  have hzero :
      ∑' y : ℤ, (if y = x then (1 / 2 : ℝ≥0∞) else 0) = 1 / 2 := by
    rw [tsum_eq_single x]
    · simp
    · intro b hb
      simp [hb]
  have hminus :
      ∑' y : ℤ, (if y = x - 1 then (1 / 4 : ℝ≥0∞) else 0) = 1 / 4 := by
    rw [tsum_eq_single (x - 1)]
    · simp
    · intro b hb
      simp [hb]
  rw [hplus, hzero, hminus]
  have hquarter_eq : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 4 by norm_num)]
    norm_num
  have hhalf_eq : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
    norm_num
  have hquarter : (1 / 4 : ℝ≥0∞) + 1 / 4 = 1 / 2 := by
    calc
      (1 / 4 : ℝ≥0∞) + 1 / 4
          = ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) := by
              rw [hquarter_eq]
      _ = ENNReal.ofReal (1 / 2 : ℝ) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            norm_num
      _ = 1 / 2 := hhalf_eq.symm
  have hhalf : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
    calc
      (1 / 2 : ℝ≥0∞) + 1 / 2
          = ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) := by
              rw [hhalf_eq]
      _ = ENNReal.ofReal (1 : ℝ) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            norm_num
      _ = 1 := by norm_num
  calc
    (1 / 4 : ℝ≥0∞) + (1 / 2 + 1 / 4) = ((1 / 4 : ℝ≥0∞) + 1 / 2) + 1 / 4 := by
      rw [add_assoc]
    _ = ((1 / 4 : ℝ≥0∞) + 1 / 4) + 1 / 2 := by
      rw [add_right_comm]
    _ = 1 / 2 + 1 / 2 := by rw [hquarter]
    _ = 1 := hhalf

/-- Helper for Exercise 18.2.4: summing over the second coordinate leaves the lazy first-coordinate
kernel. -/
private theorem vertical_axis_blocked_walk_transition_matrix_tsum_second
    (x1 x2 y1 : ℤ) :
    ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (x1, x2) (y1, z2) =
      axisBlockedFirstCoordinateTransitionMatrix x1 y1 := by
  by_cases hx : x1 = 0
  · subst hx
    by_cases hyPlus : y1 = 1
    · subst hyPlus
      -- Proof comment: on the axis, the only targets with first coordinate `1` are the horizontal
      -- neighbors `(1, x2)`, so the `ℤ`-sum collapses to one singleton.
      calc
        ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (0, x2) (1, z2)
            = ∑' z2 : ℤ, if z2 = x2 then (1 / 4 : ℝ≥0∞) else 0 := by
                refine tsum_congr fun z2 ↦ ?_
                by_cases hz : z2 = x2
                · subst hz
                  simp [vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor,
                    isHorizontalNeighbor, isVerticalNeighbor]
                · simp [vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor,
                    isHorizontalNeighbor, isVerticalNeighbor, hz]
        _ = 1 / 4 := by
              rw [tsum_eq_single x2]
              · simp
              · intro b hb
                simp [hb]
        _ = axisBlockedFirstCoordinateTransitionMatrix 0 1 := by
              simp [axisBlockedFirstCoordinateTransitionMatrix]
    · by_cases hyZero : y1 = 0
      · subst hyZero
        -- Proof comment: for first coordinate `0`, the only axis targets are the two vertical
        -- neighbors `(0, x2 ± 1)`.
        have hsplit :
            (fun z2 : ℤ ↦
                if z2 = x2 + 1 then (1 / 4 : ℝ≥0∞)
                else if z2 = x2 - 1 then 1 / 4 else 0) =
              (fun z2 : ℤ ↦
                (if z2 = x2 + 1 then (1 / 4 : ℝ≥0∞) else 0) +
                  (if z2 = x2 - 1 then (1 / 4 : ℝ≥0∞) else 0)) := by
          funext z2
          by_cases hplus : z2 = x2 + 1
          · by_cases hminus : z2 = x2 - 1
            · omega
            · have hneq : x2 + 1 ≠ x2 - 1 := by omega
              simp [hplus, hminus, hneq]
          · by_cases hminus : z2 = x2 - 1
            · have hneq : x2 - 1 ≠ x2 + 1 := by omega
              simp [hplus, hminus, hneq]
            · simp [hplus, hminus]
        have hsumPlus :
            ∑' z2 : ℤ, (if z2 = x2 + 1 then (1 / 4 : ℝ≥0∞) else 0) = 1 / 4 := by
          rw [tsum_eq_single (x2 + 1)]
          · simp
          · intro b hb
            simp [hb]
        have hsumMinus :
            ∑' z2 : ℤ, (if z2 = x2 - 1 then (1 / 4 : ℝ≥0∞) else 0) = 1 / 4 := by
          rw [tsum_eq_single (x2 - 1)]
          · simp
          · intro b hb
            simp [hb]
        have hquarter :
            (1 / 4 : ℝ≥0∞) + 1 / 4 = 1 / 2 := by
          have hquarter_eq : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by
            rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 4 by norm_num)]
            norm_num
          have hhalf_eq : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
            rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
            norm_num
          calc
            (1 / 4 : ℝ≥0∞) + 1 / 4
                = ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) := by
                    rw [hquarter_eq]
            _ = ENNReal.ofReal (1 / 2 : ℝ) := by
                  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
                  norm_num
            _ = 1 / 2 := hhalf_eq.symm
        calc
          ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (0, x2) (0, z2)
              = ∑' z2 : ℤ,
                  if z2 = x2 + 1 then (1 / 4 : ℝ≥0∞)
                  else if z2 = x2 - 1 then 1 / 4 else 0 := by
                    refine tsum_congr fun z2 ↦ ?_
                    simpa using
                      vertical_axis_blocked_walk_transition_matrix_onAxis_sameFirstCoordinate x2 z2
          _ = ∑' z2 : ℤ,
                ((if z2 = x2 + 1 then (1 / 4 : ℝ≥0∞) else 0) +
                  (if z2 = x2 - 1 then (1 / 4 : ℝ≥0∞) else 0)) := by
                    rw [hsplit]
          _ = (∑' z2 : ℤ, (if z2 = x2 + 1 then (1 / 4 : ℝ≥0∞) else 0)) +
                ∑' z2 : ℤ, (if z2 = x2 - 1 then (1 / 4 : ℝ≥0∞) else 0) := by
                    rw [ENNReal.tsum_add]
          _ = 1 / 4 + 1 / 4 := by simp [hsumPlus, hsumMinus]
          _ = 1 / 2 := hquarter
          _ = axisBlockedFirstCoordinateTransitionMatrix 0 0 := by
                simp [axisBlockedFirstCoordinateTransitionMatrix]
      · by_cases hyMinus : y1 = -1
        · subst hyMinus
          -- Proof comment: the case `y1 = -1` is the symmetric horizontal singleton on the axis.
          calc
            ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (0, x2) (-1, z2)
                = ∑' z2 : ℤ, if z2 = x2 then (1 / 4 : ℝ≥0∞) else 0 := by
                    refine tsum_congr fun z2 ↦ ?_
                    by_cases hz : z2 = x2
                    · subst hz
                      simp [vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor,
                        isHorizontalNeighbor, isVerticalNeighbor]
                    · simp [vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor,
                        isHorizontalNeighbor, isVerticalNeighbor, hz]
            _ = 1 / 4 := by
                  rw [tsum_eq_single x2]
                  · simp
                  · intro b hb
                    simp [hb]
            _ = axisBlockedFirstCoordinateTransitionMatrix 0 (-1) := by
                  simp [axisBlockedFirstCoordinateTransitionMatrix, hyPlus, hyZero]
        · -- Proof comment: every remaining first-coordinate fiber is disjoint from the three axis
          -- moves, so the whole `ℤ`-sum vanishes.
          have hterm :
              ∀ z2 : ℤ,
                vertical_axis_blocked_walk_transition_matrix (0, x2) (y1, z2) = 0 := by
            intro z2
            have haxis : ¬ isAxisNeighbor (0, x2) (y1, z2) := by
              intro h
              rcases h with hhor | hvert
              · rcases hhor with hright | hleft
                · rcases hright with ⟨h1, _⟩
                  exact hyPlus (by omega)
                · rcases hleft with ⟨h1, _⟩
                  exact hyMinus (by omega)
              · rcases hvert with hUp | hDown
                · rcases hUp with ⟨h1, _⟩
                  exact hyZero (by simpa using h1)
                · rcases hDown with ⟨h1, _⟩
                  exact hyZero (by simpa using h1)
            simp [vertical_axis_blocked_walk_transition_matrix, haxis]
          have hsumZero :
              ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (0, x2) (y1, z2) = 0 := by
            refine ENNReal.tsum_eq_zero.mpr ?_
            intro z2
            exact hterm z2
          calc
            ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (0, x2) (y1, z2) = 0 :=
              hsumZero
            _ = axisBlockedFirstCoordinateTransitionMatrix 0 y1 := by
                  simp [axisBlockedFirstCoordinateTransitionMatrix, hyPlus, hyZero, hyMinus]
  · by_cases hyPlus : y1 = x1 + 1
    · subst hyPlus
      -- Proof comment: away from the axis, the projected chain sees the right horizontal move
      -- only at the original second coordinate.
      calc
        ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (x1, x2) (x1 + 1, z2)
            = ∑' z2 : ℤ, if z2 = x2 then (1 / 4 : ℝ≥0∞) else 0 := by
                refine tsum_congr fun z2 ↦ ?_
                by_cases hz : z2 = x2
                · subst hz
                  simp [vertical_axis_blocked_walk_transition_matrix, hx, isHorizontalNeighbor]
                · have hneq : ((x1 + 1, z2) : AxisState) ≠ (x1, x2) := by
                    intro hEq
                    exact hz (by simpa using congrArg Prod.snd hEq)
                  simp [vertical_axis_blocked_walk_transition_matrix, hx, isHorizontalNeighbor,
                    hz, hneq]
        _ = 1 / 4 := by
              rw [tsum_eq_single x2]
              · simp
              · intro b hb
                simp [hb]
        _ = axisBlockedFirstCoordinateTransitionMatrix x1 (x1 + 1) := by
              simp [axisBlockedFirstCoordinateTransitionMatrix]
    · by_cases hyZero : y1 = x1
      · -- Proof comment: off the axis, unchanged first coordinate means the self-loop branch.
        -- Proof comment: off the axis, the only same-first-coordinate transition is the
        -- self-loop at second coordinate `x2`.
        calc
          ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (x1, x2) (y1, z2)
              = ∑' z2 : ℤ, if z2 = x2 then (1 / 2 : ℝ≥0∞) else 0 := by
                  refine tsum_congr fun z2 ↦ ?_
                  simpa [hyZero] using
                    vertical_axis_blocked_walk_transition_matrix_offAxis_sameFirstCoordinate
                      (x1 := x1) (x2 := x2) (z2 := z2) hx
          _ = 1 / 2 := by
                rw [tsum_eq_single x2]
                · simp
                · intro b hb
                  simp [hb]
          _ = axisBlockedFirstCoordinateTransitionMatrix x1 y1 := by
                simp [axisBlockedFirstCoordinateTransitionMatrix, hyPlus, hyZero]
      · by_cases hyMinus : y1 = x1 - 1
        · -- Proof comment: the left horizontal move is the symmetric singleton case off the axis.
          -- Proof comment: the left horizontal move is the symmetric singleton case off the axis.
          calc
            ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (x1, x2) (y1, z2)
                = ∑' z2 : ℤ, if z2 = x2 then (1 / 4 : ℝ≥0∞) else 0 := by
                    refine tsum_congr fun z2 ↦ ?_
                    by_cases hz : z2 = x2
                    · subst hz
                      simp [vertical_axis_blocked_walk_transition_matrix, hx, hyMinus,
                        isHorizontalNeighbor]
                    · have hneq : ((x1 - 1, z2) : AxisState) ≠ (x1, x2) := by
                        intro hEq
                        exact hz (by simpa using congrArg Prod.snd hEq)
                      simp [vertical_axis_blocked_walk_transition_matrix, hx, hyMinus,
                        isHorizontalNeighbor, hz, hneq]
            _ = 1 / 4 := by
                  rw [tsum_eq_single x2]
                  · simp
                  · intro b hb
                    simp [hb]
            _ = axisBlockedFirstCoordinateTransitionMatrix x1 y1 := by
                  simp [axisBlockedFirstCoordinateTransitionMatrix, hyPlus, hyZero, hyMinus]
        · -- Proof comment: every other off-axis first-coordinate fiber has zero mass termwise.
          have hterm :
              ∀ z2 : ℤ,
                vertical_axis_blocked_walk_transition_matrix (x1, x2) (y1, z2) = 0 := by
            intro z2
            have hhor : ¬ isHorizontalNeighbor (x1, x2) (y1, z2) := by
              intro h
              rcases h with hright | hleft
              · rcases hright with ⟨h1, _⟩
                exact hyPlus (by omega)
              · rcases hleft with ⟨h1, _⟩
                exact hyMinus (by omega)
            have hneq : ((y1, z2) : AxisState) ≠ (x1, x2) := by
              intro hEq
              exact hyZero (by simpa using congrArg Prod.fst hEq)
            simp [vertical_axis_blocked_walk_transition_matrix, hx, hhor, hneq]
          have hsumZero :
              ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (x1, x2) (y1, z2) = 0 := by
            refine ENNReal.tsum_eq_zero.mpr ?_
            intro z2
            exact hterm z2
          calc
            ∑' z2 : ℤ, vertical_axis_blocked_walk_transition_matrix (x1, x2) (y1, z2) = 0 :=
              hsumZero
            _ = axisBlockedFirstCoordinateTransitionMatrix x1 y1 := by
                  simp [axisBlockedFirstCoordinateTransitionMatrix, hyPlus, hyZero, hyMinus]

/-- Helper for Exercise 18.2.4: the transition matrix is symmetric, so counting measure is a
natural candidate invariant measure. -/
private theorem vertical_axis_blocked_walk_transition_matrix_symm (x y : AxisState) :
    vertical_axis_blocked_walk_transition_matrix x y =
      vertical_axis_blocked_walk_transition_matrix y x := by
  by_cases hx : x.1 = 0
  · by_cases hy : y.1 = 0
    · simpa [vertical_axis_blocked_walk_transition_matrix, hx, hy, isAxisNeighbor_symm]
    · have haxis :
        isAxisNeighbor x y ↔ isHorizontalNeighbor x y :=
          isAxisNeighbor_iff_horizontalNeighbor_of_axis_offAxis hx hy
      have hneq : x ≠ y := by
        intro hxy
        exact hy (hxy ▸ hx)
      simpa [vertical_axis_blocked_walk_transition_matrix, hx, hy, haxis,
        isHorizontalNeighbor_symm, hneq, eq_comm]
  · by_cases hy : y.1 = 0
    · have haxis :
        isAxisNeighbor y x ↔ isHorizontalNeighbor y x :=
          isAxisNeighbor_iff_horizontalNeighbor_of_axis_offAxis hy hx
      have hneq : x ≠ y := by
        intro hxy
        exact hx (hxy ▸ hy)
      simpa [vertical_axis_blocked_walk_transition_matrix, hx, hy, haxis,
        isHorizontalNeighbor_symm, hneq, eq_comm]
    · simpa [vertical_axis_blocked_walk_transition_matrix, hx, hy, isHorizontalNeighbor_symm,
        eq_comm]

/-- Helper for Exercise 18.2.4: the axis-blocked walk kernel attached to
`vertical_axis_blocked_walk_transition_matrix`. -/
private abbrev axisBlockedKernel : Kernel AxisState AxisState :=
  discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix

/-- Helper for Exercise 18.2.4: evaluating `axisBlockedKernel x` on a singleton `{y}` recovers the
matrix entry `vertical_axis_blocked_walk_transition_matrix x y`. -/
private theorem axisBlockedKernel_singletonEqEntry (x y : AxisState) :
    axisBlockedKernel x ({y} : Set AxisState) =
      vertical_axis_blocked_walk_transition_matrix x y := by
  -- Proof comment: expand the discrete kernel row as a sum of weighted Dirac masses and keep the
  -- unique singleton contribution at `y`.
  rw [axisBlockedKernel, discreteMatrixKernel_apply]
  simpa using
    (Measure.sum_smul_dirac_singleton
      (f := fun z : AxisState ↦ vertical_axis_blocked_walk_transition_matrix x z) (a := y))

/-- Helper for Exercise 18.2.4: each row of the axis-blocked walk transition matrix has total
mass `1`. -/
private theorem vertical_axis_blocked_walk_transition_matrix_tsum (x : AxisState) :
    ∑' y : AxisState, vertical_axis_blocked_walk_transition_matrix x y = 1 := by
  rcases x with ⟨x1, x2⟩
  -- Proof comment: rewrite the row sum as iterated sums over the two coordinates and collapse the
  -- second-coordinate sum to the lazy first-coordinate row proved earlier.
  calc
    ∑' y : AxisState, vertical_axis_blocked_walk_transition_matrix (x1, x2) y
        = ∑' y1 : ℤ, ∑' y2 : ℤ,
            vertical_axis_blocked_walk_transition_matrix (x1, x2) (y1, y2) := by
              simpa using
                (ENNReal.tsum_prod'
                  (f := fun y : AxisState ↦
                    vertical_axis_blocked_walk_transition_matrix (x1, x2) y))
    _ = ∑' y1 : ℤ, axisBlockedFirstCoordinateTransitionMatrix x1 y1 := by
          refine tsum_congr fun y1 ↦ ?_
          exact vertical_axis_blocked_walk_transition_matrix_tsum_second x1 x2 y1
    _ = 1 := axisBlockedFirstCoordinateTransitionMatrix_tsum x1

/-- Helper for Exercise 18.2.4: the axis-blocked walk transition matrix is stochastic. -/
private theorem vertical_axis_blocked_walk_transition_matrix_isStochastic :
    IsStochasticMatrix vertical_axis_blocked_walk_transition_matrix := by
  intro x
  exact vertical_axis_blocked_walk_transition_matrix_tsum x

/-- Helper for Exercise 18.2.4: positive singleton masses compose additively across kernel powers.
-/
private theorem axisBlockedWalk_positiveSingletonComp
    {m n : ℕ} {x y z : AxisState}
    (hxy : 0 < (axisBlockedKernel ^ m) x ({y} : Set AxisState))
    (hyz : 0 < (axisBlockedKernel ^ n) y ({z} : Set AxisState)) :
    0 < (axisBlockedKernel ^ (m + n)) x ({z} : Set AxisState) := by
  -- Proof comment: expand the Chapman-Kolmogorov integral and keep the positive contribution
  -- coming from the intermediate singleton `{y}`.
  rw [Kernel.pow_add_apply_eq_lintegral axisBlockedKernel m n x (measurableSet_singleton z)]
  have hsingleton :
      0 <
        ∫⁻ b in ({y} : Set AxisState), (axisBlockedKernel ^ n) b ({z} : Set AxisState)
          ∂((axisBlockedKernel ^ m) x) := by
    rw [MeasureTheory.lintegral_singleton]
    exact ENNReal.mul_pos hyz.ne' hxy.ne'
  have hmono :
      ∫⁻ b in ({y} : Set AxisState), (axisBlockedKernel ^ n) b ({z} : Set AxisState)
          ∂((axisBlockedKernel ^ m) x) ≤
        ∫⁻ b in Set.univ, (axisBlockedKernel ^ n) b ({z} : Set AxisState)
          ∂((axisBlockedKernel ^ m) x) :=
    MeasureTheory.lintegral_mono_set
      (show ({y} : Set AxisState) ⊆ Set.univ from Set.subset_univ _)
  exact lt_of_lt_of_le hsingleton (by simpa [Measure.restrict_univ] using hmono)

/-- Helper for Exercise 18.2.4: a positive one-step move followed by a positive `n`-step route
still gives a positive `(n + 1)`-step route. -/
private theorem axisBlockedWalk_positiveSingletonComp_oneStep
    {n : ℕ} {x y z : AxisState}
    (hxy : 0 < axisBlockedKernel x ({y} : Set AxisState))
    (hyz : 0 < (axisBlockedKernel ^ n) y ({z} : Set AxisState)) :
    0 < (axisBlockedKernel ^ (n + 1)) x ({z} : Set AxisState) := by
  -- Proof comment: this is the specialized `m = 1` composition rule used by the explicit path
  -- inductions below, so they stay in the stable `axisBlockedKernel` spelling.
  simpa [pow_one, Nat.add_comm] using
    (axisBlockedWalk_positiveSingletonComp (m := 1) (n := n) (x := x) (y := y) (z := z)
      (by simpa [pow_one] using hxy) hyz)

/-- Helper for Exercise 18.2.4: every allowed horizontal one-step move has positive mass. -/
private theorem axisBlockedWalk_horizontalNeighbor_pos {x y : AxisState}
    (h : isHorizontalNeighbor x y) :
    0 < axisBlockedKernel x ({y} : Set AxisState) := by
  -- Proof comment: unfold the one-step kernel and select the horizontal-neighbor branch.
  rw [axisBlockedKernel_singletonEqEntry]
  rw [vertical_axis_blocked_walk_transition_matrix]
  by_cases hx : x.1 = 0
  · have haxis : isAxisNeighbor x y := Or.inl h
    simp [hx, haxis]
  · simp [hx, h]

/-- Helper for Exercise 18.2.4: every allowed vertical one-step move on the axis has positive
mass. -/
private theorem axisBlockedWalk_verticalNeighbor_pos {x y : AxisState}
    (hx : x.1 = 0) (h : isVerticalNeighbor x y) :
    0 < axisBlockedKernel x ({y} : Set AxisState) := by
  -- Proof comment: on the axis the transition law is the symmetric nearest-neighbor walk, so any
  -- vertical axis move has mass `1 / 4`.
  rw [axisBlockedKernel_singletonEqEntry]
  rw [vertical_axis_blocked_walk_transition_matrix]
  have haxis : isAxisNeighbor x y := Or.inr h
  simp [hx, haxis]

/-- Helper for Exercise 18.2.4: every off-axis state has a positive one-step self-loop. -/
private theorem axisBlockedWalk_selfLoop_pos {x : AxisState} (hx : x.1 ≠ 0) :
    0 < axisBlockedKernel x ({x} : Set AxisState) := by
  -- Proof comment: away from the axis, the blocked walk stays put with probability `1 / 2`.
  rw [axisBlockedKernel_singletonEqEntry]
  rw [vertical_axis_blocked_walk_transition_matrix]
  have hhor : ¬ isHorizontalNeighbor x x := by
    intro h
    rcases h with hright | hleft
    · rcases hright with ⟨h1, _⟩
      omega
    · rcases hleft with ⟨h1, _⟩
      omega
  simp [hx, hhor]

/-- Helper for Exercise 18.2.4: from any horizontal coordinate one can reach the axis while
keeping the vertical coordinate fixed. -/
private theorem axisBlockedWalk_positiveHorizontalToAxis (x1 x2 : ℤ) :
    ∃ n : ℕ, 0 < (axisBlockedKernel ^ n) (x1, x2) ({(0, x2)} : Set AxisState) := by
  cases x1 with
  | ofNat n =>
      induction n with
      | zero =>
          -- Proof comment: if the horizontal coordinate is already `0`, the zero-step kernel
          -- stays at the starting state.
          refine ⟨0, ?_⟩
          simpa [pow_zero] using
            (show 0 < Kernel.id (0, x2) ({(0, x2)} : Set AxisState) by
              rw [Kernel.id_apply]
              simp)
      | succ n ih =>
          rcases ih with ⟨m, hm⟩
          have hstep :
              0 < axisBlockedKernel (Int.ofNat (n + 1), x2)
                ({(Int.ofNat n, x2)} : Set AxisState) := by
            -- Proof comment: one horizontal step toward the axis is always allowed.
            have hpred : (n : ℤ) = ((n + 1 : ℕ) : ℤ) - 1 := by
              omega
            exact axisBlockedWalk_horizontalNeighbor_pos
              (x := (Int.ofNat (n + 1), x2)) (y := (Int.ofNat n, x2)) <|
              Or.inr ⟨hpred, rfl⟩
          refine ⟨m + 1, ?_⟩
          exact axisBlockedWalk_positiveSingletonComp_oneStep hstep hm
  | negSucc n =>
      induction n with
      | zero =>
          refine ⟨1, ?_⟩
          -- Proof comment: from `(-1, x2)` the walk moves horizontally to the axis in one step.
          simpa [pow_one] using
            axisBlockedWalk_horizontalNeighbor_pos
              (x := (Int.negSucc 0, x2)) (y := (0, x2))
              (Or.inl ⟨by omega, rfl⟩)
      | succ n ih =>
          rcases ih with ⟨m, hm⟩
          have hstep :
              0 < axisBlockedKernel (Int.negSucc (n + 1), x2)
                ({(Int.negSucc n, x2)} : Set AxisState) := by
            -- Proof comment: each negative horizontal coordinate also has a one-step move toward
            -- the axis.
            exact axisBlockedWalk_horizontalNeighbor_pos
              (x := (Int.negSucc (n + 1), x2)) (y := (Int.negSucc n, x2)) <|
              Or.inl ⟨by omega, rfl⟩
          refine ⟨m + 1, ?_⟩
          exact axisBlockedWalk_positiveSingletonComp_oneStep hstep hm

/-- Helper for Exercise 18.2.4: from the axis one can reach any horizontal coordinate while
keeping the vertical coordinate fixed. -/
private theorem axisBlockedWalk_positiveHorizontalFromAxis (y1 y2 : ℤ) :
    ∃ n : ℕ, 0 < (axisBlockedKernel ^ n) (0, y2) ({(y1, y2)} : Set AxisState) := by
  cases y1 with
  | ofNat n =>
      induction n with
      | zero =>
          -- Proof comment: the target is already the starting axis state.
          refine ⟨0, ?_⟩
          simpa [pow_zero] using
            (show 0 < Kernel.id (0, y2) ({(0, y2)} : Set AxisState) by
              rw [Kernel.id_apply]
              simp)
      | succ n ih =>
          rcases ih with ⟨m, hm⟩
          have hstep :
              0 < axisBlockedKernel (Int.ofNat n, y2)
                ({(Int.ofNat (n + 1), y2)} : Set AxisState) := by
            -- Proof comment: move one horizontal step away from the axis on the positive side.
            have hsucc : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by
              omega
            exact axisBlockedWalk_horizontalNeighbor_pos
              (x := (Int.ofNat n, y2)) (y := (Int.ofNat (n + 1), y2)) <|
              Or.inl ⟨hsucc, rfl⟩
          refine ⟨m + 1, ?_⟩
          simpa [pow_one] using
            axisBlockedWalk_positiveSingletonComp (m := m) (n := 1) hm
              (by simpa [pow_one] using hstep)
  | negSucc n =>
      induction n with
      | zero =>
          refine ⟨1, ?_⟩
          -- Proof comment: from the axis, the walk reaches `(-1, y2)` in one horizontal step.
          simpa [pow_one] using
            axisBlockedWalk_horizontalNeighbor_pos
              (x := (0, y2)) (y := (Int.negSucc 0, y2))
              (Or.inr ⟨by omega, rfl⟩)
      | succ n ih =>
          rcases ih with ⟨m, hm⟩
          have hstep :
              0 < axisBlockedKernel (Int.negSucc n, y2)
                ({(Int.negSucc (n + 1), y2)} : Set AxisState) := by
            -- Proof comment: extend the negative horizontal excursion by one more left move.
            exact axisBlockedWalk_horizontalNeighbor_pos
              (x := (Int.negSucc n, y2)) (y := (Int.negSucc (n + 1), y2)) <|
              Or.inr ⟨by omega, rfl⟩
          refine ⟨m + 1, ?_⟩
          simpa [pow_one] using
            axisBlockedWalk_positiveSingletonComp (m := m) (n := 1) hm
              (by simpa [pow_one] using hstep)

/-- Helper for Exercise 18.2.4: from any axis state one can reach the origin by vertical moves
along the axis. -/
private theorem axisBlockedWalk_positiveVerticalToOrigin (x2 : ℤ) :
    ∃ n : ℕ, 0 < (axisBlockedKernel ^ n) (0, x2) ({(0, 0)} : Set AxisState) := by
  cases x2 with
  | ofNat n =>
      induction n with
      | zero =>
          -- Proof comment: if the vertical coordinate is already `0`, the zero-step kernel closes
          -- the claim.
          refine ⟨0, ?_⟩
          simpa [pow_zero] using
            (show 0 < Kernel.id (0, 0) ({(0, 0)} : Set AxisState) by
              rw [Kernel.id_apply]
              simp)
      | succ n ih =>
          rcases ih with ⟨m, hm⟩
          have hstep :
              0 < axisBlockedKernel (0, Int.ofNat (n + 1))
                ({(0, Int.ofNat n)} : Set AxisState) := by
            -- Proof comment: on the axis, every vertical nearest-neighbor move has mass `1 / 4`.
            have hpred : (n : ℤ) = ((n + 1 : ℕ) : ℤ) - 1 := by
              omega
            exact axisBlockedWalk_verticalNeighbor_pos (x := (0, Int.ofNat (n + 1)))
              (y := (0, Int.ofNat n)) rfl <|
              Or.inr ⟨rfl, hpred⟩
          refine ⟨m + 1, ?_⟩
          exact axisBlockedWalk_positiveSingletonComp_oneStep hstep hm
  | negSucc n =>
      induction n with
      | zero =>
          refine ⟨1, ?_⟩
          -- Proof comment: from `(0, -1)` the walk reaches the origin in one vertical step.
          simpa [pow_one] using
            axisBlockedWalk_verticalNeighbor_pos
              (x := (0, Int.negSucc 0)) (y := (0, 0)) rfl
              (Or.inl ⟨rfl, by omega⟩)
      | succ n ih =>
          rcases ih with ⟨m, hm⟩
          have hstep :
              0 < axisBlockedKernel (0, Int.negSucc (n + 1))
                ({(0, Int.negSucc n)} : Set AxisState) := by
            -- Proof comment: each negative vertical level has a one-step move upward toward `0`.
            exact axisBlockedWalk_verticalNeighbor_pos
              (x := (0, Int.negSucc (n + 1))) (y := (0, Int.negSucc n)) rfl <|
              Or.inl ⟨rfl, by omega⟩
          refine ⟨m + 1, ?_⟩
          exact axisBlockedWalk_positiveSingletonComp_oneStep hstep hm

/-- Helper for Exercise 18.2.4: from the origin one can reach any axis state by vertical moves
along the axis. -/
private theorem axisBlockedWalk_positiveVerticalFromOrigin (y2 : ℤ) :
    ∃ n : ℕ, 0 < (axisBlockedKernel ^ n) (0, 0) ({(0, y2)} : Set AxisState) := by
  cases y2 with
  | ofNat n =>
      induction n with
      | zero =>
          -- Proof comment: the origin reaches itself in zero steps.
          refine ⟨0, ?_⟩
          simpa [pow_zero] using
            (show 0 < Kernel.id (0, 0) ({(0, 0)} : Set AxisState) by
              rw [Kernel.id_apply]
              simp)
      | succ n ih =>
          rcases ih with ⟨m, hm⟩
          have hstep :
              0 < axisBlockedKernel (0, Int.ofNat n)
                ({(0, Int.ofNat (n + 1))} : Set AxisState) := by
            -- Proof comment: extend the positive vertical excursion by one upward axis move.
            have hsucc : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by
              omega
            exact axisBlockedWalk_verticalNeighbor_pos
              (x := (0, Int.ofNat n)) (y := (0, Int.ofNat (n + 1))) rfl <|
              Or.inl ⟨rfl, hsucc⟩
          refine ⟨m + 1, ?_⟩
          simpa [pow_one] using
            axisBlockedWalk_positiveSingletonComp (m := m) (n := 1) hm
              (by simpa [pow_one] using hstep)
  | negSucc n =>
      induction n with
      | zero =>
          refine ⟨1, ?_⟩
          -- Proof comment: the first downward axis move reaches `(0, -1)` in one step.
          simpa [pow_one] using
            axisBlockedWalk_verticalNeighbor_pos
              (x := (0, 0)) (y := (0, Int.negSucc 0)) rfl
              (Or.inr ⟨rfl, by omega⟩)
      | succ n ih =>
          rcases ih with ⟨m, hm⟩
          have hstep :
              0 < axisBlockedKernel (0, Int.negSucc n)
                ({(0, Int.negSucc (n + 1))} : Set AxisState) := by
            -- Proof comment: extend the negative vertical excursion by one more downward axis
            -- move.
            exact axisBlockedWalk_verticalNeighbor_pos
              (x := (0, Int.negSucc n)) (y := (0, Int.negSucc (n + 1))) rfl <|
              Or.inr ⟨rfl, by omega⟩
          refine ⟨m + 1, ?_⟩
          simpa [pow_one] using
            axisBlockedWalk_positiveSingletonComp (m := m) (n := 1) hm
              (by simpa [pow_one] using hstep)

/-- Helper for Exercise 18.2.4: every state communicates with every other state by first moving
horizontally to the axis, then vertically along the axis, and finally horizontally to the target.
-/
private theorem axisBlockedWalk_positivePathMass (x y : AxisState) :
    ∃ n : ℕ, 0 < (axisBlockedKernel ^ n) x ({y} : Set AxisState) := by
  -- Proof comment: move horizontally to the axis, travel vertically along the axis, and then move
  -- horizontally away from the axis to the target.
  rcases axisBlockedWalk_positiveHorizontalToAxis x.1 x.2 with ⟨n₁, hn₁⟩
  rcases axisBlockedWalk_positiveVerticalFromOrigin y.2 with ⟨n₂', hn₂'⟩
  rcases axisBlockedWalk_positiveVerticalToOrigin x.2 with ⟨n₂, hn₂⟩
  rcases axisBlockedWalk_positiveHorizontalFromAxis y.1 y.2 with ⟨n₃, hn₃⟩
  have haxis :
      0 < (axisBlockedKernel ^ (n₁ + n₂)) x ({(0, 0)} : Set AxisState) := by
    exact axisBlockedWalk_positiveSingletonComp hn₁ hn₂
  have haxis' :
      0 < (axisBlockedKernel ^ (n₁ + n₂ + n₂')) x ({(0, y.2)} : Set AxisState) := by
    simpa [Nat.add_assoc] using axisBlockedWalk_positiveSingletonComp haxis hn₂'
  refine ⟨n₁ + n₂ + n₂' + n₃, ?_⟩
  simpa [Nat.add_assoc] using axisBlockedWalk_positiveSingletonComp haxis' hn₃

/-- Helper for Exercise 18.2.4: the axis-blocked walk is irreducible with respect to counting
measure because every singleton target is reachable with positive finite-step mass. -/
private theorem verticalAxisBlockedWalk_kernelIsIrreducible :
    Kernel.IsIrreducible (Measure.count : Measure AxisState) axisBlockedKernel := by
  classical
  constructor
  intro A hA hApos x
  obtain ⟨y, hyA⟩ : A.Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero (μ := Measure.count) (ne_of_gt hApos)
  rcases axisBlockedWalk_positivePathMass x y with ⟨n, hn⟩
  refine ⟨n, lt_of_lt_of_le hn ?_⟩
  exact measure_mono (Set.singleton_subset_iff.mpr hyA)

section RealizationResults

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : AxisState → ProbabilityMeasure Ω} {X : ℕ → Ω → AxisState}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) ^ n) P X]

/-- Helper for Exercise 18.2.4: every realization of the axis-blocked walk is irreducible,
because the explicit path lemmas already give positive ever-hit probability between any two
states. -/
private theorem axisBlockedWalk_isIrreducibleMarkovChain :
    IsIrreducibleMarkovChain P X := by
  let _ : Kernel.IsIrreducible (Measure.count : Measure AxisState) axisBlockedKernel :=
    verticalAxisBlockedWalk_kernelIsIrreducible
  have hgreen :
      ∀ ⦃x y : AxisState⦄, x ≠ y → 0 < (G[P, X; 1]) x y := by
    intro x y hxy
    have hy_pos : 0 < (Measure.count : Measure AxisState) ({y} : Set AxisState) := by
      simp
    rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure AxisState)
        axisBlockedKernel).irreducible
        (A := ({y} : Set AxisState)) (measurableSet_singleton y) hy_pos x with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hnpos
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
      subst hnzero
      have hzeroId : (Kernel.id : Kernel AxisState AxisState) x ({y} : Set AxisState) = 0 := by
        rw [Kernel.id_apply]
        simp [hxy]
      have hzero : (axisBlockedKernel ^ 0) x ({y} : Set AxisState) = 0 := by
        simpa [pow_zero] using hzeroId
      have hnot : ¬ 0 < (axisBlockedKernel ^ 0) x ({y} : Set AxisState) := by
        simpa [hzero]
      exact hnot hn
    exact greenFunctionFrom_one_pos_of_posStepMass
      (κ := fun n : ℕ ↦ axisBlockedKernel ^ n) P X hnpos hn
  -- Proof comment: Chapter 17 identifies irreducibility with off-diagonal positivity of the
  -- positive-time Green function, and the previous step supplies exactly that positivity.
  exact
    (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
      (κ := fun n : ℕ ↦ axisBlockedKernel ^ n) P X).2 hgreen

/-- Helper for Exercise 18.2.4: irreducibility already gives positive ever-hit probability from
the origin to every state. -/
private theorem axisBlockedWalk_originEverHitsPos (y : AxisState) :
    0 < (F[P, X]) (0, 0) y := by
  -- Proof comment: the explicit communication paths proved earlier already upgrade the realization
  -- to an irreducible Markov chain, so every state is hit from the origin with positive
  -- probability.
  exact axisBlockedWalk_isIrreducibleMarkovChain (P := P) (X := X) (0, 0) y

/-- Helper for Exercise 18.2.4: the lazy first-coordinate matrix is stochastic. -/
private theorem axisBlockedFirstCoordinateTransitionMatrix_isStochastic :
    IsStochasticMatrix axisBlockedFirstCoordinateTransitionMatrix := by
  -- Proof comment: this is exactly the row-sum computation proved earlier.
  intro x
  exact axisBlockedFirstCoordinateTransitionMatrix_tsum x

/-- Helper for Exercise 18.2.4: the first marginal of the one-step axis-blocked kernel is the
lazy first-coordinate kernel on `ℤ`. -/
private theorem axisBlockedKernel_fst :
    Kernel.fst axisBlockedKernel =
      Kernel.comap (discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
        Prod.fst measurable_fst := by
  classical
  refine Kernel.ext fun a ↦ ?_
  rcases a with ⟨x1, x2⟩
  refine Measure.ext fun (s : Set ℤ) hs ↦ ?_
  -- Proof comment: rewrite the pair row into iterated singleton masses and collapse the
  -- second-coordinate sum with the explicit first-coordinate row identity.
  rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply', axisBlockedKernel, discreteMatrixKernel_apply,
    discreteMatrixKernel_apply]
  calc
    (Measure.sum fun j ↦ vertical_axis_blocked_walk_transition_matrix (x1, x2) j • Measure.dirac j)
        (Prod.fst ⁻¹' s)
        = ∑' b : AxisState,
            (vertical_axis_blocked_walk_transition_matrix (x1, x2) b • Measure.dirac b)
              (Prod.fst ⁻¹' s) := by
                rw [Measure.sum_apply _ (measurable_fst hs)]
    _ = ∑' b : AxisState,
          vertical_axis_blocked_walk_transition_matrix (x1, x2) b * s.indicator 1 b.1 := by
          refine tsum_congr fun b ↦ ?_
          simp [Set.indicator, Measure.smul_apply, mul_comm]
    _ = ∑' z1 : ℤ, ∑' z2 : ℤ,
          vertical_axis_blocked_walk_transition_matrix (x1, x2) (z1, z2) *
            s.indicator 1 z1 := by
          simpa using
            (ENNReal.tsum_prod'
              (f := fun b : AxisState ↦
                vertical_axis_blocked_walk_transition_matrix (x1, x2) b *
                  s.indicator 1 b.1))
    _ = ∑' z1 : ℤ,
          (∑' z2 : ℤ,
            vertical_axis_blocked_walk_transition_matrix (x1, x2) (z1, z2)) *
              s.indicator 1 z1 := by
          refine tsum_congr fun z1 ↦ ?_
          rw [ENNReal.tsum_mul_right]
    _ = ∑' z1 : ℤ, axisBlockedFirstCoordinateTransitionMatrix x1 z1 * s.indicator 1 z1 := by
          refine tsum_congr fun z1 ↦ ?_
          rw [vertical_axis_blocked_walk_transition_matrix_tsum_second]
    _ = ∑' z1 : ℤ, (axisBlockedFirstCoordinateTransitionMatrix x1 z1 • Measure.dirac z1) s := by
          refine tsum_congr fun z1 ↦ ?_
          simp [Measure.smul_apply, mul_comm, mul_left_comm, mul_assoc]
    _ = (Measure.sum fun j ↦ axisBlockedFirstCoordinateTransitionMatrix x1 j • Measure.dirac j) s := by
          symm
          rw [Measure.sum_apply _ hs]

/-- Helper for Exercise 18.2.4: after descending from the full path filtration, the first
coordinate satisfies the lazy nearest-neighbor one-step conditional law. -/
private theorem axisBlockedFirstCoordinate_oneStepConditional
    (z x : ℤ) (s : ℕ) {A : Set ℤ} (hA : MeasurableSet A) :
    (P (x, z))⟦(fun ω ↦ (X (s + 1) ω).1) ⁻¹' A |
      generatedFiltrationSpace (fun n ω ↦ (X n ω).1) s⟧ =ᵐ[(P (x, z) : Measure Ω)]
        fun ω ↦
          ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
            ((X s ω).1)).real A := by
  let μ : Measure Ω := (P (x, z) : Measure Ω)
  let hwalk : IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := by
    simpa [axisBlockedKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) ^ n)
          P X)
  let g : Ω → ℝ := fun ω ↦
    ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix) ((X s ω).1)).real A
  have hsmall_le :
      generatedFiltrationSpace (fun n ω ↦ (X n ω).1) s ≤ generatedFiltrationSpace X s := by
    exact generatedFiltrationSpace_comp_le X Prod.fst measurable_fst s
  have hlarge_le : generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
    exact generatedHistory_le_ambient X hwalk.measurable_process s
  have hstate :
      Measurable[generatedFiltrationSpace (fun n ω ↦ (X n ω).1) s] fun ω ↦ (X s ω).1 := by
    exact Measurable.of_comap_le <| present_le_generatedHistory (fun n ω ↦ (X n ω).1) s
  have hg :
      AEStronglyMeasurable[generatedFiltrationSpace (fun n ω ↦ (X n ω).1) s] g μ := by
    have hg_measurable :
        Measurable[generatedFiltrationSpace (fun n ω ↦ (X n ω).1) s] g := by
      exact ((Kernel.measurable_coe
        (discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix) hA).ennreal_toReal).comp
          hstate
    exact Measurable.aestronglyMeasurable hg_measurable
  have hpair :
      μ⟦(fun ω ↦ (X (s + 1) ω).1) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[μ] g := by
    have hpairRaw :
        μ⟦(fun ω ↦ (X (s + 1) ω).1) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[μ]
          fun ω ↦ (axisBlockedKernel (X s ω)).real (Prod.fst ⁻¹' A) := by
      simpa [Function.comp, axisBlockedKernel, pow_one, add_comm] using
        hwalk.markov_property (x, z) (A := Prod.fst ⁻¹' A) (measurable_fst hA) s 1
    have hkernel :
        ∀ ω : Ω,
          (axisBlockedKernel (X s ω)).real (Prod.fst ⁻¹' A) =
            ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
              ((X s ω).1)).real A := by
      intro ω
      calc
        (axisBlockedKernel (X s ω)).real (Prod.fst ⁻¹' A)
            = ((Kernel.fst axisBlockedKernel) (X s ω)).real A := by
                simpa using
                  (Kernel.fst_real_apply axisBlockedKernel (X s ω) (s := A) hA).symm
        _ = ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
              ((X s ω).1)).real A := by
              simpa [Kernel.comap_apply] using
                congrArg (fun κ : Kernel AxisState ℤ => (κ (X s ω)).real A)
                  axisBlockedKernel_fst
    exact hpairRaw.trans <| Filter.Eventually.of_forall hkernel
  have hg_int : Integrable g μ := by
    exact (integrable_congr hpair).1 integrable_condExp
  -- Proof comment: descend the conditional law from the full filtration to the smaller first-
  -- coordinate filtration by one application of the tower property.
  calc
    μ⟦(fun ω ↦ (X (s + 1) ω).1) ⁻¹' A | generatedFiltrationSpace (fun n ω ↦ (X n ω).1) s⟧
        =ᵐ[μ]
          MeasureTheory.condExp μ
            (m := generatedFiltrationSpace (fun n ω ↦ (X n ω).1) s)
            (MeasureTheory.condExp μ
              (m := generatedFiltrationSpace X s)
              (((fun ω ↦ (X (s + 1) ω).1) ⁻¹' A).indicator fun _ ↦ (1 : ℝ))) := by
              symm
              exact condExp_condExp_of_le hsmall_le hlarge_le
    _ =ᵐ[μ]
          MeasureTheory.condExp μ
            (m := generatedFiltrationSpace (fun n ω ↦ (X n ω).1) s) g := by
          exact condExp_congr_ae hpair
    _ =ᵐ[μ] g := by
          exact condExp_of_aestronglyMeasurable' (hsmall_le.trans hlarge_le) hg hg_int

/-- Helper for Exercise 18.2.4: for each fixed second start coordinate, the projected first
coordinate realizes the lazy nearest-neighbor chain on `ℤ`. -/
private theorem axisBlockedFirstCoordinate_isMarkovProcessRealization
    (z : ℤ) :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
      (fun x : ℤ ↦ P (x, z))
      (fun n ω ↦ (X n ω).1) := by
  let hwalk : IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := by
    simpa [axisBlockedKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) ^ n)
          P X)
  letI : IsMarkovKernel (discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix) :=
    discreteMatrixKernel_isMarkovKernel axisBlockedFirstCoordinateTransitionMatrix
      axisBlockedFirstCoordinateTransitionMatrix_isStochastic
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
    (P := fun x : ℤ ↦ P (x, z))
    (X := fun n ω ↦ (X n ω).1)
    (hmeas := ?_)
    (hstart := ?_)
    (hstep := ?_)
  · intro n
    exact measurable_fst.comp (hwalk.measurable_process n)
  · intro x
    let μ : Measure Ω := (P (x, z) : Measure Ω)
    have hmap :
        (μ.map (X 0)).map Prod.fst = μ.map (fun ω ↦ (X 0 ω).1) := by
      simpa [Function.comp] using
        (Measure.map_map (μ := μ) (f := X 0) (g := Prod.fst)
          (hf := hwalk.measurable_process 0) (hg := measurable_fst))
    calc
      μ.map (fun ω ↦ (X 0 ω).1) = (μ.map (X 0)).map Prod.fst := hmap.symm
      _ = (Measure.dirac (x, z)).map Prod.fst := by
            rw [hwalk.initial_eq (x, z)]
      _ = Measure.dirac x := by
            simp
  · intro x A hA s
    simpa using axisBlockedFirstCoordinate_oneStepConditional (P := P) (X := X) z x s hA

/-- Helper for Exercise 18.2.4: the lazy first-coordinate walk is the convolution walk driven by
the quarter-half-quarter step law on `ℤ`. -/
private def axisBlockedFirstCoordinateStepPMF : PMF ℤ :=
  (PMF.uniformOfFintype (Fin 4)).bind fun i ↦
    PMF.pure
      (if (i : ℕ) = 0 then
        (-1 : ℤ)
      else if (i : ℕ) = 3 then
        1
      else
        0)

/-- Helper for Exercise 18.2.4: the quarter-half-quarter increment law as a probability measure
on `ℤ`. -/
private def axisBlockedFirstCoordinateStepLaw : ProbabilityMeasure ℤ :=
  ⟨axisBlockedFirstCoordinateStepPMF.toMeasure, inferInstance⟩

/-- Helper for Exercise 18.2.4: the first-coordinate increment law assigns mass `1 / 4` to `-1`
and `1`, and mass `1 / 2` to `0`. -/
private theorem axisBlockedFirstCoordinateStepPMF_apply (z : ℤ) :
    axisBlockedFirstCoordinateStepPMF z =
      if z = -1 then 1 / 4 else if z = 0 then 1 / 2 else if z = 1 then 1 / 4 else 0 := by
  by_cases hneg : z = -1
  · -- Proof comment: only the first atom of `Fin 4` maps to `-1`.
    subst hneg
    simp [axisBlockedFirstCoordinateStepPMF, PMF.bind_apply, PMF.uniformOfFintype_apply,
      Fin.sum_univ_four]
  · by_cases hzero : z = 0
    · -- Proof comment: exactly the two middle atoms of `Fin 4` map to `0`.
      subst hzero
      simp [axisBlockedFirstCoordinateStepPMF, PMF.bind_apply, PMF.uniformOfFintype_apply, hneg,
        Fin.sum_univ_four]
      norm_num
      have hquarter : ((1 / 4 : ℝ≥0∞) + 1 / 4) = 1 / 2 := by
        have hquarter_eq : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by
          rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 4 by norm_num)]
          norm_num
        have hhalf_eq : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
          rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
          norm_num
        calc
          (1 / 4 : ℝ≥0∞) + 1 / 4
              = ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) := by
                  rw [hquarter_eq]
          _ = ENNReal.ofReal (1 / 2 : ℝ) := by
                rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
                norm_num
          _ = 1 / 2 := hhalf_eq.symm
      simpa using hquarter
    · by_cases hpos : z = 1
      · -- Proof comment: only the last atom of `Fin 4` maps to `1`.
        subst hpos
        simp [axisBlockedFirstCoordinateStepPMF, PMF.bind_apply, PMF.uniformOfFintype_apply,
          hneg, hzero, Fin.sum_univ_four]
      · -- Proof comment: outside `{-1, 0, 1}`, every point mass in the finite support vanishes.
        have hoff :
            ∀ i : Fin 4,
              z ≠ if i = 0 then (-1 : ℤ) else if (i : ℕ) = 3 then 1 else 0 := by
          intro i
          fin_cases i <;> simp [hneg, hzero, hpos]
        simp [axisBlockedFirstCoordinateStepPMF, PMF.bind_apply, PMF.uniformOfFintype_apply,
          hneg, hzero, hpos, hoff]

/-- Helper for Exercise 18.2.4: the quarter-half-quarter step law has finite first moment and
zero drift. -/
private theorem axisBlockedFirstCoordinateStepPMF_integrable_mean_zero :
    Integrable (fun z : ℤ ↦ (z : ℝ)) axisBlockedFirstCoordinateStepPMF.toMeasure ∧
      ∫ z, (z : ℝ) ∂axisBlockedFirstCoordinateStepPMF.toMeasure = 0 := by
  let μ : Measure ℤ := axisBlockedFirstCoordinateStepPMF.toMeasure
  let A : Set ℤ := {z | |z| ≤ 1}
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hAcompl_zero : μ Aᶜ = 0 := by
    -- Proof comment: outside `{-1, 0, 1}` the explicit PMF formula is zero.
    rw [PMF.toMeasure_apply (p := axisBlockedFirstCoordinateStepPMF)
      (show MeasurableSet Aᶜ from MeasurableSet.of_discrete)]
    refine ENNReal.tsum_eq_zero.2 ?_
    intro z
    by_cases hz : |z| ≤ 1
    · simp [A, hz]
    · have hneg : z ≠ -1 := by
        intro hz'
        subst hz'
        exact hz (by norm_num)
      have hzero : z ≠ 0 := by
        intro hz'
        subst hz'
        exact hz (by norm_num)
      have hpos : z ≠ 1 := by
        intro hz'
        subst hz'
        exact hz (by norm_num)
      simp [A, hz, axisBlockedFirstCoordinateStepPMF_apply, hneg, hzero, hpos]
  have hA_ae : ∀ᵐ z ∂μ, z ∈ A := by
    simpa using (compl_mem_ae_iff.2 hAcompl_zero)
  let g : ℤ → ℝ := fun z ↦ if z ∈ A then (z : ℝ) else 0
  have hg_integrable : Integrable g μ := by
    -- Proof comment: after truncating to the three-point support, the observable is bounded by
    -- `1`, hence integrable under the probability law `μ`.
    refine (integrable_const (1 : ℝ)).mono'
      (Measurable.of_discrete.aestronglyMeasurable) <|
      Filter.Eventually.of_forall fun z => by
        by_cases hz : z ∈ A
        · have hz' : |z| ≤ 1 := hz
          have hzreal : |(z : ℝ)| ≤ 1 := by
            exact_mod_cast hz'
          simpa [g, hz, Real.norm_eq_abs] using hzreal
        · simp [g, hz]
  have hfg_ae : (fun z : ℤ ↦ (z : ℝ)) =ᵐ[μ] g := by
    filter_upwards [hA_ae] with z hz
    simp [g, hz]
  have h_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) μ :=
    hg_integrable.congr hfg_ae.symm
  refine ⟨h_integrable, ?_⟩
  -- Proof comment: the expectation is the three-point sum of the explicit masses, and the
  -- symmetric `±1` contributions cancel.
  rw [show ∫ z, (z : ℝ) ∂μ =
      ∑' z : ℤ, (axisBlockedFirstCoordinateStepPMF z).toReal * (z : ℝ) by
        simpa [μ, smul_eq_mul] using
          (PMF.integral_eq_tsum axisBlockedFirstCoordinateStepPMF
            (fun z : ℤ ↦ (z : ℝ)) h_integrable)]
  rw [tsum_eq_sum (s := ({(-1 : ℤ), 0, 1} : Finset ℤ))]
  · norm_num [axisBlockedFirstCoordinateStepPMF_apply]
  · intro z hz
    have hneg : z ≠ -1 := by
      intro hz'
      exact hz (by simp [hz'])
    have hzero : z ≠ 0 := by
      intro hz'
      exact hz (by simp [hz'])
    have hpos : z ≠ 1 := by
      intro hz'
      exact hz (by simp [hz'])
    simp [axisBlockedFirstCoordinateStepPMF_apply, hneg, hzero, hpos]

/-- Helper for Exercise 18.2.4: the first-coordinate transition matrix is exactly the singleton
view of the quarter-half-quarter convolution kernel. -/
private theorem axisBlockedFirstCoordinateTransitionMatrix_eq_convolutionStepMatrix :
    axisBlockedFirstCoordinateTransitionMatrix =
      convolutionStepMatrix axisBlockedFirstCoordinateStepLaw := by
  funext x y
  rw [convolutionStepMatrix, dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage : (fun z : ℤ ↦ x + z) ⁻¹' ({y} : Set ℤ) = {y - x} := by
    ext z
    simp
    omega
  have hstepLaw_apply :
      (axisBlockedFirstCoordinateStepLaw : Measure ℤ) ((fun z : ℤ ↦ x + z) ⁻¹' ({y} : Set ℤ)) =
        axisBlockedFirstCoordinateStepPMF (y - x) := by
    simpa [axisBlockedFirstCoordinateStepLaw, hpreimage] using
      (PMF.toMeasure_apply (p := axisBlockedFirstCoordinateStepPMF)
        (measurableSet_singleton (y - x)))
  rw [hstepLaw_apply]
  rw [axisBlockedFirstCoordinateStepPMF_apply]
  by_cases hplus : y = x + 1
  · have hzero : y ≠ x := by omega
    have hminus : y ≠ x - 1 := by omega
    simp [axisBlockedFirstCoordinateTransitionMatrix, hplus, hzero, hminus]
  · by_cases hzero : y = x
    · have hminus : y ≠ x - 1 := by omega
      simp [axisBlockedFirstCoordinateTransitionMatrix, hplus, hzero, hminus]
    · by_cases hminus : y = x - 1
      · simp [axisBlockedFirstCoordinateTransitionMatrix, hplus, hzero, hminus]
      · have hyx_neg : y - x ≠ -1 := by omega
        have hyx_zero : y - x ≠ 0 := by omega
        have hyx_pos : y - x ≠ 1 := by omega
        simp [axisBlockedFirstCoordinateTransitionMatrix, hplus, hzero, hminus,
          hyx_neg, hyx_zero, hyx_pos]

/-- Helper for Exercise 18.2.4: every iterated return time of the first coordinate to `0` is
almost surely finite when the walk starts on the axis. -/
private theorem axisBlockedFirstCoordinate_iteratedReturnFinite
    (z : ℤ) (k : ℕ+) :
    (P (0, z) : Measure Ω).real {ω | (τ_[fun n ω ↦ (X n ω).1, 0]^k) ω < ⊤} = 1 := by
  let ν : ProbabilityMeasure ℤ := axisBlockedFirstCoordinateStepLaw
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (fun x : ℤ ↦ P (x, z))
        (fun n ω ↦ (X n ω).1) := by
    have hproj :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
          (fun x : ℤ ↦ P (x, z))
          (fun n ω ↦ (X n ω).1) :=
      axisBlockedFirstCoordinate_isMarkovProcessRealization (P := P) (X := X) z
    have hkernel :
        discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix =
          dirac_convolution_kernel (ν : Measure ℤ) := by
      simpa [axisBlockedFirstCoordinateTransitionMatrix_eq_convolutionStepMatrix] using
        (convolutionStepMatrixKernel_eq ν)
    simpa [hkernel] using hproj
  have hmoment := axisBlockedFirstCoordinateStepPMF_integrable_mean_zero
  have hrec :
      IsRecurrentMarkovChain
        (fun x : ℤ ↦ P (x, z))
        (fun n ω ↦ (X n ω).1) := by
    exact
      (integerRandomWalk_recurrent_iff_zero_stepLawMean
        (ν := ν) (P := fun x : ℤ ↦ P (x, z)) (X := fun n ω ↦ (X n ω).1)
        hmoment.1).2 hmoment.2
  have hrec0 :
      IsRecurrentState
        (fun x : ℤ ↦ P (x, z))
        (fun n ω ↦ (X n ω).1)
        0 := hrec 0
  have hhit :
      (F[fun x ↦ P (x, z), fun n ω ↦ (X n ω).1]) 0 0 = 1 := by
    simpa [IsRecurrentState] using hrec0
  -- Proof comment: Theorem 17.29 turns recurrence of the projected lazy walk at `0` into the
  -- almost-sure finiteness of every iterated return time to `0`.
  simpa [hhit] using
    (iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
      (κ := fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
      (P := fun x : ℤ ↦ P (x, z))
      (X := fun n ω ↦ (X n ω).1) (x := 0) (y := 0) k)

/-- Helper for Exercise 18.2.4: the sampled return-height process records the second coordinate at
the successive return times of the first coordinate to `0`. -/
private def axisReturnHeight (k : ℕ+) : Ω → ℤ :=
  fun ω ↦
    stoppedValue (fun n ω' ↦ (X n ω').2)
      (fun ω' ↦ (τ_[fun n ω'' ↦ (X n ω'').1, 0]^k) ω') ω

/-- Helper for Exercise 18.2.4: the embedded axis-return process starts from the initial axis
height and then records the sampled return heights. -/
private def axisReturnHeightProcess : ℕ → Ω → ℤ
  | 0 => fun ω ↦ (X 0 ω).2
  | n + 1 => fun ω ↦ axisReturnHeight (X := X) ⟨n + 1, Nat.succ_pos _⟩ ω

/-- Helper for Exercise 18.2.4: the `k`-th return time of the first coordinate to `0` is almost
surely finite when the walk starts from `(0, z)`. -/
private theorem axisBlockedFirstCoordinate_iteratedReturnFinite_ae
    (z : ℤ) (k : ℕ+) :
    ∀ᵐ ω ∂(P (0, z) : Measure Ω), (τ_[fun n ω ↦ (X n ω).1, 0]^k) ω < ⊤ := by
  -- Proof comment: turn the previously computed probability-one return event into an almost-sure
  -- statement, so later sampled-height lemmas can work pointwise on a full-measure set.
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
        (fun x : ℤ ↦ P (x, z))
        (fun n ω ↦ (X n ω).1) :=
    axisBlockedFirstCoordinate_isMarkovProcessRealization (P := P) (X := X) z
  let A : Set Ω := {ω | (τ_[fun n ω ↦ (X n ω).1, 0]^k) ω < ⊤}
  have hA_meas : MeasurableSet A := by
    simpa [A] using
      (iteratedEntranceTimeFiniteEvent_measurable
        (κ := fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
        (P := fun x : ℤ ↦ P (x, z))
        (X := fun n ω ↦ (X n ω).1) 0 k)
  have hA_real : (P (0, z) : Measure Ω).real A = 1 :=
    axisBlockedFirstCoordinate_iteratedReturnFinite (P := P) (X := X) z k
  have hA : (P (0, z) : Measure Ω) A = 1 := by
    exact (ENNReal.toReal_eq_one_iff ((P (0, z) : Measure Ω) A)).mp hA_real
  have hAc : (P (0, z) : Measure Ω) Aᶜ = 0 := by
    rw [measure_compl hA_meas (measure_ne_top _ _)]
    simp [hA]
  exact (ae_iff.2 hAc)

/-- Helper for Exercise 18.2.4: on the slice where the `k`-th return time equals `n`, the sampled
return height is exactly the second coordinate at time `n`. -/
private theorem axisReturnHeight_eq_second_at_returnTime
    {k : ℕ+} {ω : Ω} {n : ℕ}
    (hτ : (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = n) :
    axisReturnHeight (X := X) k ω = (X n ω).2 := by
  -- Proof comment: after pinning down the concrete return time, `stoppedValue` reduces to the
  -- ordinary time-`n` evaluation of the second coordinate.
  unfold axisReturnHeight
  simpa [hτ] using
    (stoppedValue_eq_on_timeSlice
      (X := fun m ω ↦ (X m ω).2)
      (τ := fun ω ↦ (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω)
      (ω := ω) (hτω := hτ))

/-- Helper for Exercise 18.2.4: almost surely, every sampled return height is the second
coordinate read at some concrete finite return time of the first coordinate to `0`. -/
private theorem axisReturnHeight_eq_second_at_some_returnTime_ae
    (z : ℤ) (k : ℕ+) :
    ∀ᵐ ω ∂(P (0, z) : Measure Ω), ∃ n : ℕ,
      (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = n ∧
        axisReturnHeight (X := X) k ω = (X n ω).2 := by
  filter_upwards [axisBlockedFirstCoordinate_iteratedReturnFinite_ae (P := P) (X := X) z k] with
    ω hfinite
  have hne : (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω ≠ ⊤ := ne_of_lt hfinite
  rcases WithTop.ne_top_iff_exists.mp hne with ⟨n, hn⟩
  refine ⟨n, hn.symm, ?_⟩
  exact axisReturnHeight_eq_second_at_returnTime (X := X) hn.symm

/-- Helper for Exercise 18.2.4: from an off-axis start, the first step stays on the same
horizontal line almost surely. -/
private theorem axisBlockedWalk_offAxis_oneStep_sameSecond_ae
    (x h : ℤ) (hx : x ≠ 0) :
    ∀ᵐ ω ∂(P (x, h) : Measure Ω), (X 1 ω).2 = h := by
  let μ : Measure Ω := (P (x, h) : Measure Ω)
  let hwalk : IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := by
    simpa [axisBlockedKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) ^ n)
          P X)
  have hbadKernel :
      axisBlockedKernel (x, h) {b : AxisState | b.2 ≠ h} = 0 := by
    rw [axisBlockedKernel, discreteMatrixKernel_apply,
      Measure.sum_apply _ (show MeasurableSet {b : AxisState | b.2 ≠ h} from
        MeasurableSet.of_discrete)]
    refine ENNReal.tsum_eq_zero.mpr ?_
    intro b
    by_cases hb : b.2 ≠ h
    · -- Proof comment: every off-axis target with changed second coordinate has zero one-step
      -- mass by the explicit row formula.
      simp [hb,
        vertical_axis_blocked_walk_transition_matrix_offAxis_diffSecond_zero
          (x1 := x) (x2 := h) (y1 := b.1) (z2 := b.2) hx hb]
    · -- Proof comment: if the second coordinate matches `h`, the bad event indicator already
      -- vanishes.
      simp [hb]
  have hbad :
      μ {ω | (X 1 ω).2 ≠ h} = 0 := by
    calc
      μ {ω | (X 1 ω).2 ≠ h}
          = (μ.map (X 1)) {b : AxisState | b.2 ≠ h} := by
              rw [show ({ω | (X 1 ω).2 ≠ h} : Set Ω) =
                  X 1 ⁻¹' ({b : AxisState | b.2 ≠ h} : Set AxisState) by
                ext ω
                simp]
              symm
              exact Measure.map_apply (hwalk.measurable_process 1)
                (show MeasurableSet ({b : AxisState | b.2 ≠ h} : Set AxisState) from
                  MeasurableSet.of_discrete)
      _ = axisBlockedKernel (x, h) {b : AxisState | b.2 ≠ h} := by
            exact congrArg
              (fun ν : Measure AxisState ↦ ν ({b : AxisState | b.2 ≠ h} : Set AxisState))
              (by simpa [pow_one] using hwalk.transition_eq (x, h) 1)
      _ = 0 := hbadKernel
  have hgood :
      ∀ᵐ ω ∂μ, ω ∈ ({ω | (X 1 ω).2 ≠ h} : Set Ω)ᶜ := by
    exact compl_mem_ae_iff.2 hbad
  filter_upwards [hgood] with ω hω
  simpa using hω

/-- Helper for Exercise 18.2.4: every finite iterated return time of the first coordinate lands
back on the vertical axis. -/
private theorem axisBlockedFirstCoordinate_eq_zero_at_iteratedReturnFinite
    {k : ℕ+} {ω : Ω}
    (hfinite : (τ_[fun n ω ↦ (X n ω).1, 0]^k) ω ≠ ⊤) :
    (X ((τ_[fun n ω ↦ (X n ω).1, 0]^k) ω).untopA ω).1 = 0 := by
  cases k using PNat.recOn with
  | one =>
      -- Proof comment: for the first return time, `hittingAfter_mem_set_of_ne_top` gives the
      -- axis membership directly at the finite hitting index.
      have hmem :
          (fun n ω ↦ (X n ω).1)
            (((τ_[fun n ω ↦ (X n ω).1, 0]^1) ω).untopA) ω ∈ ({0} : Set ℤ) := by
        have h :
            (fun n ω ↦ (X n ω).1)
              (MeasureTheory.hittingAfter (fun n ω ↦ (X n ω).1) ({0} : Set ℤ) 1 ω).untopA ω ∈
              ({0} : Set ℤ) :=
          hittingAfter_mem_set_of_ne_top
            (by simpa [iteratedEntranceTime_one] using hfinite)
        simpa [iteratedEntranceTime_one] using h
      simpa [Set.mem_singleton_iff] using hmem
  | succ k =>
      let S : Set ℕ :=
        {n : ℕ | (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω < n ∧ (X n ω).1 = 0}
      have hsInf :
          sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) =
            (τ_[fun n ω ↦ (X n ω).1, 0]^(k + 1)) ω := by
        simpa [iteratedEntranceTime_succ, S]
      have hS : S.Nonempty := by
        by_contra hS
        have himage_empty : ((fun n : ℕ ↦ (n : ℕ∞)) '' S) = ∅ := by
          simpa [Set.not_nonempty_iff_eq_empty] using hS
        have htop :
            (τ_[fun n ω ↦ (X n ω).1, 0]^(k + 1)) ω = ⊤ := by
          rw [← hsInf, himage_empty, sInf_empty]
        exact hfinite htop
      have hsInf_nat :
          ((sInf S : ℕ) : ℕ∞) =
            (τ_[fun n ω ↦ (X n ω).1, 0]^(k + 1)) ω := by
        calc
          ((sInf S : ℕ) : ℕ∞) = sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) := by
            simpa using (WithTop.coe_sInf' hS (OrderBot.bddBelow S))
          _ = (τ_[fun n ω ↦ (X n ω).1, 0]^(k + 1)) ω := hsInf
      have huntop :
          ((τ_[fun n ω ↦ (X n ω).1, 0]^(k + 1)) ω).untopA = sInf S := by
        exact WithTop.coe_inj.mp <| by
          calc
            ((((τ_[fun n ω ↦ (X n ω).1, 0]^(k + 1)) ω).untopA : ℕ) : ℕ∞) =
                (τ_[fun n ω ↦ (X n ω).1, 0]^(k + 1)) ω := by
                  rw [WithTop.untopA_eq_untop hfinite]
                  exact WithTop.coe_untop _ hfinite
            _ = ((sInf S : ℕ) : ℕ∞) := hsInf_nat.symm
      have hsInf_mem : sInf S ∈ S := Nat.sInf_mem hS
      simpa [S, huntop] using hsInf_mem.2

/-- Helper for Exercise 18.2.4: at each finite sampled return time, the full walk is exactly
`(0, axisReturnHeight k)`. -/
private theorem axisReturnState_eq_axisReturnHeight_ae
    (z : ℤ) (k : ℕ+) :
    ∀ᵐ ω ∂(P (0, z) : Measure Ω),
      ∃ n : ℕ,
        (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = n ∧
          X n ω = (0, axisReturnHeight (X := X) k ω) := by
  filter_upwards
      [axisBlockedFirstCoordinate_iteratedReturnFinite_ae (P := P) (X := X) z k] with ω hfinite
  have hne_top : (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω ≠ ⊤ := ne_of_lt hfinite
  let n : ℕ := ((τ_[fun m ω ↦ (X m ω).1, 0]^k) ω).untopA
  have hτ :
      (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = n := by
    rw [show n = ((τ_[fun m ω ↦ (X m ω).1, 0]^k) ω).untopA by rfl]
    rw [WithTop.untopA_eq_untop hne_top]
    symm
    exact WithTop.coe_untop _ hne_top
  have hfirst :
      (X n ω).1 = 0 := by
    simpa [n] using
      axisBlockedFirstCoordinate_eq_zero_at_iteratedReturnFinite
        (X := X) (k := k) (ω := ω) hne_top
  have hsecond :
      axisReturnHeight (X := X) k ω = (X n ω).2 := by
    exact axisReturnHeight_eq_second_at_returnTime (X := X) hτ
  refine ⟨n, hτ, ?_⟩
  exact Prod.ext hfirst hsecond.symm

/-- Helper for Exercise 18.2.4: on a history event that fixes `X n = y`, the next-step singleton
mass factors through the one-step row from `y`. -/
private theorem measureInter_eq_mul_stepMass_of_stateEvent
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {q : E → E → ENNReal}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x y w : E) (n : ℕ) (A : Set Ω)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | X (n + 1) ω = w}) =
      (discreteMatrixKernel q y ({w} : Set E)) * (P x : Measure Ω) A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hstep :
      ∀ x' : E, ∀ ⦃B : Set E⦄, MeasurableSet B → ∀ s : ℕ,
        (P x')⟦X (s + 1) ⁻¹' B | generatedFiltrationSpace X s⟧ =ᵐ[(P x' : Measure Ω)]
          fun ω ↦ ((discreteMatrixKernel q) (X s ω)).real B := by
    intro x' B hB s
    -- Proof comment: specialize the Markov property to a one-step singleton target event.
    simpa [Nat.add_comm] using hReal.markov_property x' (A := B) hB s 1
  have hnext_meas : MeasurableSet (X (n + 1) ⁻¹' ({w} : Set E)) := by
    exact (hReal.measurable_process (n + 1)) (measurableSet_singleton w)
  have hslice_real :
      μ.real (A ∩ {ω | X (n + 1) ω = w}) =
        (discreteMatrixKernel q y ({w} : Set E)).toReal * μ.real A := by
    calc
      μ.real (A ∩ {ω | X (n + 1) ω = w}) =
          ∫ ω in A,
            Set.indicator (X (n + 1) ⁻¹' ({w} : Set E)) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              rw [← MeasureTheory.integral_indicator hA_meas]
              -- Proof comment: rewrite the intersection indicator as the time-`n + 1` state
              -- event restricted to the history slice `A`.
              simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                Set.inter_comm, smul_eq_mul] using
                (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                  (hA_meas.inter hnext_meas)).symm
      _ =
          ∫ ω in A, ((discreteMatrixKernel q ^ 1) (X n ω)).real ({w} : Set E) ∂μ := by
            symm
            -- Proof comment: on an `n`-history event, one-step future singleton masses are given
            -- by the Markov kernel row from the current state.
            simpa [Nat.add_comm] using
              kernelPow_setIntegral_eq_on_history
                (κ₁ := discreteMatrixKernel q) (P := P) (X := X)
                hReal.measurable_process hstep x (A := ({w} : Set E))
                (measurableSet_singleton w) n 1 (B := A) hA_measFiltration
      _ = ∫ ω in A, (discreteMatrixKernel q y).real ({w} : Set E) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
            simp [pow_one]
      _ = (discreteMatrixKernel q y ({w} : Set E)).toReal * μ.real A := by
            rw [show ((discreteMatrixKernel q) y).real ({w} : Set E) =
                (((discreteMatrixKernel q) y) ({w} : Set E)).toReal by rfl]
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ {ω | X (n + 1) ω = w}) =
        (discreteMatrixKernel q y ({w} : Set E)) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by exact (measure_lt_top (discreteMatrixKernel q y) ({w} : Set E)).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ] using hslice_enn

/-- Helper for Exercise 18.2.4: on a history event that fixes `X n = y`, the next-step mass of any
measurable target set factors through the one-step row from `y`. -/
private theorem measureInter_eq_mul_stepMass_of_stateEvent_set
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {q : E → E → ENNReal}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x y : E) (n : ℕ) (A : Set Ω) (B : Set E)
    (hB_meas : MeasurableSet B)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | X (n + 1) ω ∈ B}) =
      (discreteMatrixKernel q y B) * (P x : Measure Ω) A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hstep :
      ∀ x' : E, ∀ ⦃C : Set E⦄, MeasurableSet C → ∀ s : ℕ,
        (P x')⟦X (s + 1) ⁻¹' C | generatedFiltrationSpace X s⟧ =ᵐ[(P x' : Measure Ω)]
          fun ω ↦ ((discreteMatrixKernel q) (X s ω)).real C := by
    intro x' C hC s
    -- Proof comment: specialize the Markov property to the measurable future target set `C`.
    simpa [Nat.add_comm] using hReal.markov_property x' (A := C) hC s 1
  have hnext_meas : MeasurableSet (X (n + 1) ⁻¹' B) := by
    exact (hReal.measurable_process (n + 1)) hB_meas
  have hslice_real :
      μ.real (A ∩ {ω | X (n + 1) ω ∈ B}) =
        (discreteMatrixKernel q y B).toReal * μ.real A := by
    calc
      μ.real (A ∩ {ω | X (n + 1) ω ∈ B}) =
          ∫ ω in A,
            Set.indicator (X (n + 1) ⁻¹' B) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              rw [← MeasureTheory.integral_indicator hA_meas]
              -- Proof comment: rewrite the intersection indicator as the time-`n + 1`
              -- measurable target event restricted to the history slice `A`.
              simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                Set.inter_comm, smul_eq_mul] using
                (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                  (hA_meas.inter hnext_meas)).symm
      _ =
          ∫ ω in A, ((discreteMatrixKernel q ^ 1) (X n ω)).real B ∂μ := by
            symm
            -- Proof comment: on the `n`-history slice, the one-step future law is the row of the
            -- Markov kernel from the pinned current state.
            simpa [Nat.add_comm] using
              kernelPow_setIntegral_eq_on_history
                (κ₁ := discreteMatrixKernel q) (P := P) (X := X)
                hReal.measurable_process hstep x (A := B) hB_meas n 1 (B := A)
                hA_measFiltration
      _ = ∫ ω in A, (discreteMatrixKernel q y).real B ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
            simp [pow_one]
      _ = (discreteMatrixKernel q y B).toReal * μ.real A := by
            rw [show ((discreteMatrixKernel q) y).real B =
                (((discreteMatrixKernel q) y) B).toReal by rfl]
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ {ω | X (n + 1) ω ∈ B}) =
        (discreteMatrixKernel q y B) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by exact (measure_lt_top (discreteMatrixKernel q y) B).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ] using hslice_enn

/-- Helper for Exercise 18.2.4: from an off-axis start, the second coordinate cannot change
before the first return of the first coordinate to the axis. -/
private theorem axisBlockedWalk_preReturn_nextSecond_bad_zero
    (x h : ℤ) (hx : x ≠ 0) :
    ∀ n : ℕ,
      (P (x, h) : Measure Ω)
        {ω | n < (τ_[fun m ω ↦ (X m ω).1, 0]^1) ω ∧ (X (n + 1) ω).2 ≠ h} = 0 := by
  let μ : Measure Ω := (P (x, h) : Measure Ω)
  let τ : Ω → ℕ∞ := τ_[fun m ω ↦ (X m ω).1, 0]^1
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := by
    simpa [axisBlockedKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) ^ n)
          P X)
  let badSet : Set AxisState := {b | b.2 ≠ h}
  have hbadSet_meas : MeasurableSet badSet := MeasurableSet.of_discrete
  have hbadKernel :
      ∀ y1 : ℤ, y1 ≠ 0 →
        axisBlockedKernel (y1, h) badSet = 0 := by
    intro y1 hy1
    rw [axisBlockedKernel, discreteMatrixKernel_apply, Measure.sum_apply _ hbadSet_meas]
    refine ENNReal.tsum_eq_zero.mpr ?_
    intro b
    by_cases hb : b.2 ≠ h
    · -- Proof comment: off the axis, any one-step move that changes the second coordinate has
      -- zero mass by the explicit transition formula.
      simp [badSet, hb, Measure.smul_apply,
        vertical_axis_blocked_walk_transition_matrix_offAxis_diffSecond_zero
          (x1 := y1) (x2 := h) (y1 := b.1) (z2 := b.2) hy1 hb]
    · -- Proof comment: outside the bad set the indicator already kills the summand.
      simp [badSet, hb, Measure.smul_apply]
  have htail_hist :
      ∀ n : ℕ,
        MeasurableSet[generatedFiltrationSpace X n] {ω | n < τ ω} := by
    intro n
    have hEq :
        {ω | n < τ ω} =
          {ω | τ ω ≤ n}ᶜ := by
      ext ω
      simp
    rw [hEq]
    have hEqLe :
        {ω | τ ω ≤ n} =
          ⋃ j ∈ (Finset.Icc 1 n : Finset ℕ), {ω | (X j ω).1 = 0} := by
      ext ω
      simpa [τ, iteratedEntranceTime_one, Set.mem_singleton_iff] using
        (MeasureTheory.hittingAfter_le_iff
          (u := fun m ω ↦ (X m ω).1) (s := ({0} : Set ℤ)) (n := 1) (ω := ω) (i := n))
    rw [hEqLe]
    refine MeasurableSet.compl <| MeasurableSet.biUnion (Set.to_countable _) ?_
    intro j hj
    have hXj :
        Measurable[generatedFiltrationSpace X n] (X j) := by
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le j <| le_iSup_of_le ((Finset.mem_Icc.mp hj).2) le_rfl
    rw [show ({ω | (X j ω).1 = 0} : Set Ω) = X j ⁻¹' ({s : AxisState | s.1 = 0}) by
      ext ω
      simp]
    exact hXj (show MeasurableSet {s : AxisState | s.1 = 0} from MeasurableSet.of_discrete)
  have htail_meas :
      ∀ n : ℕ, MeasurableSet {ω | n < τ ω} := by
    intro n
    have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
      refine iSup₂_le fun j hj ↦ ?_
      exact (hReal.measurable_process j).comap_le
    exact hFiltration_le (s := {ω | n < τ ω}) (htail_hist n)
  intro n
  induction n with
  | zero =>
      have hgood :
          ({ω | (X 1 ω).2 ≠ h} : Set Ω)ᶜ ∈ ae μ := by
        filter_upwards [axisBlockedWalk_offAxis_oneStep_sameSecond_ae
          (P := P) (X := X) x h hx] with ω hω
        simpa [hω]
      have hbad :
          μ {ω | (X 1 ω).2 ≠ h} = 0 := compl_mem_ae_iff.mp hgood
      refine measure_mono_null ?_ hbad
      intro ω hω
      exact hω.2
  | succ n ih =>
      let tailEvent : Set Ω := {ω | n + 1 < τ ω}
      let prevBad : Set Ω := {ω | n < τ ω ∧ (X (n + 1) ω).2 ≠ h}
      let sliceEvent : {y1 : ℤ // y1 ≠ 0} → Set Ω :=
        fun y ↦ {ω | n + 1 < τ ω ∧ X (n + 1) ω = (y.1, h)}
      have hcover :
          {ω | n + 1 < τ ω ∧ (X (n + 2) ω).2 ≠ h} ⊆
            prevBad ∪
              ⋃ y : {y1 : ℤ // y1 ≠ 0},
                (sliceEvent y ∩ {ω | X (n + 2) ω ∈ badSet}) := by
        intro ω hω
        rcases hω with ⟨hτω, hbadω⟩
        by_cases hprev : (X (n + 1) ω).2 ≠ h
        · exact Or.inl ⟨lt_trans (by exact_mod_cast Nat.lt_succ_self n) hτω, hprev⟩
        · right
          refine Set.mem_iUnion.2 ?_
          refine ⟨⟨(X (n + 1) ω).1, ?_⟩, ?_⟩
          · intro hzero
            have hhit : τ ω ≤ n + 1 := by
              have h :
                  MeasureTheory.hittingAfter (fun m ω ↦ (X m ω).1) ({0} : Set ℤ) 1 ω ≤ n + 1 :=
                MeasureTheory.hittingAfter_le_of_mem (by simp) <|
                  by simpa [Set.mem_singleton_iff] using hzero
              simpa [τ, iteratedEntranceTime_one] using h
            exact (not_le_of_gt hτω) hhit
          · constructor
            · have hsecond : (X (n + 1) ω).2 = h := not_ne_iff.mp hprev
              exact ⟨hτω, Prod.ext rfl hsecond⟩
            · simpa [badSet] using hbadω
      have hUnion_zero :
          μ (⋃ y : {y1 : ℤ // y1 ≠ 0},
              (sliceEvent y ∩ {ω | X (n + 2) ω ∈ badSet})) = 0 := by
        refine measure_iUnion_null fun y ↦ ?_
        let A : Set Ω := sliceEvent y
        have hA_hist : MeasurableSet[generatedFiltrationSpace X (n + 1)] A := by
          have hXn1 :
              Measurable[generatedFiltrationSpace X (n + 1)] (X (n + 1)) := by
            refine Measurable.of_comap_le ?_
            exact le_iSup_of_le (n + 1) <| le_iSup_of_le le_rfl le_rfl
          change MeasurableSet[generatedFiltrationSpace X (n + 1)]
            ({ω | n + 1 < τ ω} ∩ X (n + 1) ⁻¹' ({(y.1, h)} : Set AxisState))
          exact (htail_hist (n + 1)).inter (hXn1 (measurableSet_singleton (y.1, h)))
        have hA_meas : MeasurableSet A := by
          exact (htail_meas (n + 1)).inter <|
            (hReal.measurable_process (n + 1)) (measurableSet_singleton (y.1, h))
        have hA_state :
            ∀ ⦃ω : Ω⦄, ω ∈ A → X (n + 1) ω = (y.1, h) := by
          intro ω hωA
          simpa [A] using hωA.2
        rw [measureInter_eq_mul_stepMass_of_stateEvent_set
          (q := vertical_axis_blocked_walk_transition_matrix)
          (P := P) (X := X) (x := (x, h)) (y := (y.1, h)) (n := n + 1)
          A badSet hbadSet_meas hA_meas hA_hist hA_state]
        rw [hbadKernel y.1 y.2, zero_mul]
      have htarget_zero :
          μ {ω | n + 1 < τ ω ∧ (X (n + 2) ω).2 ≠ h} = 0 := by
        refine measure_mono_null hcover ?_
        exact measure_union_null ih hUnion_zero
      simpa [μ, τ] using htarget_zero

/-- Helper for Exercise 18.2.4: from a horizontal-neighbor start, each deterministic first-return
slice has zero mass on changing the second coordinate. -/
private theorem axisReturnHeight_badSlice_zero_fromHorizontalNeighbor
    (x h : ℤ) (hx : x = 1 ∨ x = -1) (n : ℕ) :
    (P (x, h) : Measure Ω)
      ({ω | (τ_[fun m ω ↦ (X m ω).1, 0]^1) ω = n + 1} ∩
        {ω | (X (n + 1) ω).2 ≠ h}) = 0 := by
  have hx0 : x ≠ 0 := by
    rcases hx with rfl | rfl <;> norm_num
  refine measure_mono_null
    (t := {ω | n < (τ_[fun m ω ↦ (X m ω).1, 0]^1) ω ∧ (X (n + 1) ω).2 ≠ h}) ?_ ?_
  · intro ω hω
    rcases hω with ⟨hτ, hbad⟩
    refine ⟨?_, hbad⟩
    rw [hτ]
    exact_mod_cast Nat.lt_succ_self n
  · simpa using
      axisBlockedWalk_preReturn_nextSecond_bad_zero
        (P := P) (X := X) x h hx0 n

/-- Helper for Exercise 18.2.4: positive times of the sampled-height process are exactly the
corresponding sampled return heights. -/
private theorem axisReturnHeightProcess_pNat (k : ℕ+) :
    axisReturnHeightProcess (X := X) k = axisReturnHeight (X := X) k := by
  cases' k with n hn
  cases n with
  | zero =>
      cases (Nat.not_lt_zero _ hn)
  | succ n =>
      rfl

/-- Helper for Exercise 18.2.4: if the walk is already back on the axis at time `1`, then the
first sampled return height is exactly the second coordinate at time `1`. -/
private theorem axisReturnHeightProcess_one_eq_of_immediateAxisReturn
    {ω : Ω} (haxis : (X 1 ω).1 = 0) :
    axisReturnHeightProcess (X := X) 1 ω = (X 1 ω).2 := by
  have hτ_le :
      (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω ≤ 1 := by
    -- Proof comment: if the first coordinate is already `0` at time `1`, then the first positive
    -- return time is bounded above by `1`.
    simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
      (MeasureTheory.hittingAfter_le_iff
        (u := fun n ω ↦ (X n ω).1) (s := ({0} : Set ℤ)) (n := 1) (ω := ω) (i := 1)).2
        ⟨1, by simp, haxis⟩
  have hτ_ge :
      (1 : ℕ∞) ≤ (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω := by
    -- Proof comment: every first positive return time is at least `1` by definition.
    simpa [iteratedEntranceTime_one] using
      (MeasureTheory.le_hittingAfter
        (u := fun n ω ↦ (X n ω).1) (s := ({0} : Set ℤ)) (n := 1) ω)
  have hτ_eq :
      (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω = 1 :=
    le_antisymm hτ_le hτ_ge
  -- Proof comment: once the return time is identified with `1`, the sampled-height observable is
  -- just the stopped second coordinate evaluated at time `1`.
  calc
    axisReturnHeightProcess (X := X) 1 ω =
        axisReturnHeight (X := X) ⟨1, Nat.succ_pos 0⟩ ω := by
          simpa using congrArg (fun f : Ω → ℤ ↦ f ω)
            (axisReturnHeightProcess_pNat (X := X) ⟨1, Nat.succ_pos 0⟩)
    _ = (X 1 ω).2 := by
          simpa using axisReturnHeight_eq_second_at_returnTime (X := X) hτ_eq

/-- Helper for Exercise 18.2.4: a bound on the `ℕ∞` infimum of natural times is equivalent to a
bounded witness in the underlying set. -/
private lemma sInf_natImage_le_iff {S : Set ℕ} {N : ℕ} :
    sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) ≤ N ↔ ∃ n ∈ S, n ≤ N := by
  by_cases hS : S.Nonempty
  · have hsInf :
        sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) = (((sInf S : ℕ) : ℕ∞)) := by
      simpa using (WithTop.coe_sInf' hS (OrderBot.bddBelow S)).symm
    constructor
    · intro h
      refine ⟨sInf S, Nat.sInf_mem hS, ?_⟩
      have hsInf_leN : (((sInf S : ℕ) : ℕ∞)) ≤ N := by
        simpa [hsInf] using h
      exact_mod_cast hsInf_leN
    · rintro ⟨n, hnS, hnN⟩
      have hsInf_le_nat : (sInf S : ℕ) ≤ n := Nat.sInf_le hnS
      have hsInf_leN_nat : (sInf S : ℕ) ≤ N := hsInf_le_nat.trans hnN
      have hsInf_leN : (((sInf S : ℕ) : ℕ∞)) ≤ N := by
        exact_mod_cast hsInf_leN_nat
      simpa [hsInf] using hsInf_leN
  · have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst hS_empty
    simp

/-- Helper for Exercise 18.2.4: bounding a successor entrance time by `N` is equivalent to seeing
one bounded hit strictly after the previous entrance. -/
private theorem iteratedEntranceTime_succ_le_iff_existsHitAfter
    {Y : ℕ → Ω → ℤ} (y : ℤ) (ω : Ω) (k : ℕ+) (N : ℕ) :
    (τ_[Y, y]^(k + 1)) ω ≤ N ↔ ∃ n : ℕ, (τ_[Y, y]^k) ω < n ∧ n ≤ N ∧ Y n ω = y := by
  rw [iteratedEntranceTime_succ]
  rw [sInf_natImage_le_iff]
  constructor
  · rintro ⟨n, hn, hnN⟩
    exact ⟨n, hn.1, hnN, hn.2⟩
  · rintro ⟨n, hτ, hnN, hy⟩
    exact ⟨n, ⟨hτ, hy⟩, hnN⟩

/-- Helper for Exercise 18.2.4: every state event `{Y i = y}` is measurable in any later
generated history filtration. -/
private lemma measurableSet_stateEvent_generated {Y : ℕ → Ω → ℤ} (y : ℤ) {i n : ℕ}
    (hi : i ≤ n) :
    MeasurableSet[generatedFiltrationSpace Y n] {ω | Y i ω = y} := by
  have hYi : Measurable[generatedFiltrationSpace Y n] (Y i) := by
    exact Measurable.of_comap_le <|
      le_iSup_of_le i <| le_iSup_of_le hi le_rfl
  change MeasurableSet[generatedFiltrationSpace Y n] ((Y i) ⁻¹' ({y} : Set ℤ))
  exact hYi (MeasurableSet.singleton y)

/-- Helper for Exercise 18.2.4: the bounded return event `{τ_[Y,y]^k ≤ N}` is measurable in the
full history up to time `N`. -/
private lemma iteratedEntranceTime_le_measurable_generated {Y : ℕ → Ω → ℤ} (y : ℤ) :
    ∀ (k : ℕ+) (N : ℕ),
      MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, y]^k) ω ≤ N} := by
  intro k N
  induction k using PNat.recOn generalizing N with
  | one =>
      have hEq :
          {ω | (τ_[Y, y]^1) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), {ω | Y j ω = y} := by
        ext ω
        simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
          (MeasureTheory.hittingAfter_le_iff
            (u := Y) (s := ({y} : Set ℤ)) (n := 1) (ω := ω) (i := N))
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      exact measurableSet_stateEvent_generated (Y := Y) y (hi := (Finset.mem_Icc.mp hj).2)
  | succ k ih =>
      let slice : ℕ → Set Ω := fun j =>
        {ω | (τ_[Y, y]^k) ω < j} ∩ {ω | Y j ω = y}
      have hEq :
          {ω | (τ_[Y, y]^(k + 1)) ω ≤ N} =
            ⋃ j ∈ ((Finset.Icc 1 N : Finset ℕ) : Set ℕ), slice j := by
        ext ω
        constructor
        · intro hω
          rcases (iteratedEntranceTime_succ_le_iff_existsHitAfter (Y := Y) y ω k N).1 hω with
            ⟨j, hτj, hjN, hjy⟩
          have hj_pos : 0 < j := by
            cases j with
            | zero => simpa using hτj
            | succ j => exact Nat.succ_pos j
          exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨Finset.mem_Icc.mpr ⟨hj_pos, hjN⟩,
            ⟨hτj, hjy⟩⟩⟩
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨j, hω⟩
          rcases Set.mem_iUnion.1 hω with ⟨hj, hslice⟩
          exact (iteratedEntranceTime_succ_le_iff_existsHitAfter (Y := Y) y ω k N).2
            ⟨j, hslice.1, (Finset.mem_Icc.mp hj).2, hslice.2⟩
      rw [hEq]
      refine MeasurableSet.biUnion (Set.to_countable _) ?_
      intro j hj
      have hj_le : j ≤ N := (Finset.mem_Icc.mp hj).2
      have hlt_N :
          MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, y]^k) ω < j} := by
        cases j with
        | zero =>
            have hj_false : ¬ 0 ∈ (Finset.Icc 1 N : Finset ℕ) := by
              simpa using hj
            exact False.elim (hj_false hj)
        | succ j =>
            have hle_j :
                MeasurableSet[generatedFiltrationSpace Y j] {ω | (τ_[Y, y]^k) ω ≤ j} :=
              ih j
            have hle_N :
                MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, y]^k) ω ≤ j} := by
              exact
                (generatedFiltrationSpace_monoNat (X := Y) (Nat.le_trans (Nat.le_succ j) hj_le))
                  _ hle_j
            simpa [ENat.lt_coe_add_one_iff] using hle_N
      exact hlt_N.inter (measurableSet_stateEvent_generated (Y := Y) y (hi := hj_le))

/-- Helper for Exercise 18.2.4: the strict bounded return event `{τ_[Y,y]^k < N}` is measurable
in the full history up to time `N`. -/
private lemma iteratedEntranceTime_lt_measurable_generated {Y : ℕ → Ω → ℤ} (y : ℤ) (k : ℕ+) :
    ∀ N : ℕ,
      MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, y]^k) ω < N} := by
  intro N
  cases N with
  | zero =>
      simpa using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  | succ N =>
      have hle_N :
          MeasurableSet[generatedFiltrationSpace Y (N + 1)] {ω | (τ_[Y, y]^k) ω ≤ N} := by
        have hle_N_base :
            MeasurableSet[generatedFiltrationSpace Y N] {ω | (τ_[Y, y]^k) ω ≤ N} :=
          iteratedEntranceTime_le_measurable_generated (Y := Y) y k N
        exact (generatedFiltrationSpace_monoNat (X := Y) (Nat.le_succ N)) _ hle_N_base
      simpa [ENat.lt_coe_add_one_iff] using hle_N

/-- Helper for Exercise 18.2.4: the exact `k`th return slice of the first coordinate to the axis at
time `n`. -/
private def axisReturnSlice (k : ℕ+) (n : ℕ) : Set Ω :=
  {ω | (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = n}

/-- Helper for Exercise 18.2.4: an exact return slice is the bounded-return event minus the
strictly earlier bounded-return event. -/
private theorem axisReturnSlice_eq_le_diff_lt
    (k : ℕ+) (n : ℕ) :
    axisReturnSlice (X := X) k n =
      {ω | (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω ≤ n} \
        {ω | (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω < n} := by
  ext ω
  constructor
  · intro hω
    have hτ : (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = n := by
      simpa [axisReturnSlice] using hω
    -- Proof comment: an exact return time is automatically both `≤ n` and not `< n`.
    constructor
    · simpa [hτ]
    · simpa [hτ]
  · intro hω
    -- Proof comment: the difference representation forces equality by combining `≤ n` with
    -- `¬ (< n)`.
    simp [axisReturnSlice, le_antisymm_iff, not_lt] at hω ⊢
    exact hω

/-- Helper for Exercise 18.2.4: exact return slices are measurable in the full history at their
terminal time. -/
private theorem axisReturnSlice_measurable_generated
    (k : ℕ+) (n : ℕ) :
    MeasurableSet[generatedFiltrationSpace X n] (axisReturnSlice (X := X) k n) := by
  -- Proof comment: rewrite the exact slice into the stable `≤ n \ < n` normal form and use the
  -- deterministic-time measurability lemmas for iterated entrance times.
  rw [axisReturnSlice_eq_le_diff_lt (X := X) k n]
  have hproj :
      generatedFiltrationSpace (fun m ω ↦ (X m ω).1) n ≤ generatedFiltrationSpace X n :=
    generatedFiltrationSpace_comp_le (X := X) Prod.fst measurable_fst n
  exact
    (hproj _ <|
      iteratedEntranceTime_le_measurable_generated
        (Y := fun m ω ↦ (X m ω).1) 0 k n).diff
      (hproj _ <|
        iteratedEntranceTime_lt_measurable_generated
          (Y := fun m ω ↦ (X m ω).1) 0 k n)

/-- Helper for Exercise 18.2.4: no iterated return to the axis can occur at time `0`. -/
private theorem axisReturnSlice_zero_eq_empty
    (k : ℕ+) :
    axisReturnSlice (X := X) k 0 = (∅ : Set Ω) := by
  -- Proof comment: every iterated return time is strictly positive, so the exact time-`0` slice
  -- is empty.
  ext ω
  constructor
  · intro hω
    have hτ : (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = 0 := by
      simpa [axisReturnSlice] using hω
    cases k using PNat.recOn with
    | one =>
        have hτ1 :
            MeasureTheory.hittingAfter (fun m ω ↦ (X m ω).1) ({0} : Set ℤ) 1 ω = 0 := by
          simpa [iteratedEntranceTime_one] using hτ
        have hlt :
            MeasureTheory.hittingAfter (fun m ω ↦ (X m ω).1) ({0} : Set ℤ) 1 ω < 1 := by
          simpa [hτ1]
        rcases
            (MeasureTheory.hittingAfter_lt_iff
              (u := fun m ω ↦ (X m ω).1) (s := ({0} : Set ℤ)) (n := 1) (ω := ω) (i := 1)).1 hlt
          with ⟨j, hj_mem, _⟩
        simpa [Set.mem_Ico] using hj_mem
    | succ k =>
        have hle : (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω ≤ 0 := by
          simpa [hτ]
        rcases
            (iteratedEntranceTime_succ_le_iff_existsHitAfter
              (Y := fun m ω ↦ (X m ω).1) (y := 0) (ω := ω) (k := k) (N := 0)).1 hle with
          ⟨n, hτn, hn_le, _⟩
        have hn_zero : n = 0 := Nat.eq_zero_of_le_zero hn_le
        simpa [hn_zero] using hτn
  · simpa

/-- Helper for Exercise 18.2.4: on a nonzero exact return slice, the first coordinate is back on
the axis at that terminal time. -/
private theorem axisReturnSlice_subset_axisState
    (k : ℕ+) (n : ℕ) :
    axisReturnSlice (X := X) k (n + 1) ⊆ {ω | (X (n + 1) ω).1 = 0} := by
  intro ω hω
  -- Proof comment: if the terminal state were off the axis, the same witness would already force
  -- the return time to occur strictly before `n + 1`, contradicting the exact-slice identity.
  cases k using PNat.recOn with
  | one =>
      by_contra hstate
      have hτ : (τ_[fun m ω ↦ (X m ω).1, 0]^1) ω = n + 1 := by
        simpa [axisReturnSlice] using hω
      have hle : (τ_[fun m ω ↦ (X m ω).1, 0]^1) ω ≤ n + 1 := by
        simpa [hτ]
      have hleHit :
          MeasureTheory.hittingAfter (fun m ω ↦ (X m ω).1) ({0} : Set ℤ) 1 ω ≤ n + 1 := by
        simpa [iteratedEntranceTime_one] using hle
      rcases
          (MeasureTheory.hittingAfter_le_iff
            (u := fun m ω ↦ (X m ω).1) (s := ({0} : Set ℤ)) (n := 1) (ω := ω) (i := n + 1)).1
            hleHit with
        ⟨j, hj_mem, hj0⟩
      have hj_ne_last : j ≠ n + 1 := by
        intro hj
        apply hstate
        simpa [hj, Set.mem_singleton_iff] using hj0
      have hj_le_n : j ≤ n := Nat.lt_succ_iff.mp (lt_of_le_of_ne hj_mem.2 hj_ne_last)
      have hleHit_n :
          MeasureTheory.hittingAfter (fun m ω ↦ (X m ω).1) ({0} : Set ℤ) 1 ω ≤ n := by
        exact
          (MeasureTheory.hittingAfter_le_iff
            (u := fun m ω ↦ (X m ω).1) (s := ({0} : Set ℤ)) (n := 1) (ω := ω) (i := n)).2
            ⟨j, ⟨hj_mem.1, hj_le_n⟩, hj0⟩
      have hle_n : (τ_[fun m ω ↦ (X m ω).1, 0]^1) ω ≤ n := by
        simpa [iteratedEntranceTime_one] using hleHit_n
      have hcontra : ((n + 1 : ℕ∞) ≤ n) := by
        simpa [hτ] using hle_n
      have hlt : (n : ℕ∞) < n + 1 := by
        exact_mod_cast Nat.lt_succ_self n
      exact (not_le_of_gt hlt) hcontra
  | succ k =>
      by_contra hstate
      have hτ : (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω = n + 1 := by
        simpa [axisReturnSlice] using hω
      have hle : (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω ≤ n + 1 := by
        simpa [hτ]
      rcases
          (iteratedEntranceTime_succ_le_iff_existsHitAfter
            (Y := fun m ω ↦ (X m ω).1) (y := 0) (ω := ω) (k := k) (N := n + 1)).1 hle with
        ⟨m, hmτ, hm_le, hm_state⟩
      have hm_ne_last : m ≠ n + 1 := by
        intro hm
        apply hstate
        simpa [hm] using hm_state
      have hm_le_n : m ≤ n := Nat.lt_succ_iff.mp (lt_of_le_of_ne hm_le hm_ne_last)
      have hle_n : (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω ≤ n := by
        exact
          (iteratedEntranceTime_succ_le_iff_existsHitAfter
            (Y := fun m ω ↦ (X m ω).1) (y := 0) (ω := ω) (k := k) (N := n)).2
            ⟨m, hmτ, hm_le_n, hm_state⟩
      have hcontra : ((n + 1 : ℕ∞) ≤ n) := by
        simpa [hτ] using hle_n
      have hlt : (n : ℕ∞) < n + 1 := by
        exact_mod_cast Nat.lt_succ_self n
      exact (not_le_of_gt hlt) hcontra

/-- Helper for Exercise 18.2.4: on an exact `(k + 1)`st return slice, the previous return time is
strictly smaller than the terminal time. -/
private theorem axisReturnPrevReturn_lt_of_succSlice
    {k : ℕ+} {ω : Ω} {n : ℕ}
    (hω : ω ∈ axisReturnSlice (X := X) (k + 1) n) :
    (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω < n := by
  have hτsucc : (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω = n := by
    simpa [axisReturnSlice] using hω
  have hle : (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω ≤ n := by
    simpa [hτsucc]
  rcases
      (iteratedEntranceTime_succ_le_iff_existsHitAfter
        (Y := fun m ω ↦ (X m ω).1) (y := 0) (ω := ω) (k := k) (N := n)).1 hle with
    ⟨m, hmτ, hm_le, _⟩
  -- Proof comment: the successor-return witness occurs strictly after the previous return and no
  -- later than the exact terminal time `n`.
  exact lt_of_lt_of_le hmτ (by exact_mod_cast hm_le)

/-- Helper for Exercise 18.2.4: every exact successor-return slice refines to one exact slice of
the previous return, occurring at a strictly earlier time. -/
private theorem axisReturnPrevSlice_of_succSlice
    {k : ℕ+} {ω : Ω} {n : ℕ}
    (hω : ω ∈ axisReturnSlice (X := X) (k + 1) n) :
    ∃ m : ℕ, m < n ∧ ω ∈ axisReturnSlice (X := X) k m := by
  have hprev_lt :
      (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω < n :=
    axisReturnPrevReturn_lt_of_succSlice (X := X) hω
  have hprev_finite :
      (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω < ⊤ :=
    lt_of_lt_of_le hprev_lt le_top
  have hprev_ne_top :
      (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω ≠ ⊤ :=
    ne_of_lt hprev_finite
  let m : ℕ := ((τ_[fun m ω ↦ (X m ω).1, 0]^k) ω).untop hprev_ne_top
  have hm_eq : (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = m := by
    symm
    exact WithTop.coe_untop _ hprev_ne_top
  have hm_lt : m < n := by
    rw [hm_eq] at hprev_lt
    exact_mod_cast hprev_lt
  -- Proof comment: once the previous return time is known to be finite, its `untop` gives the
  -- exact predecessor slice.
  refine ⟨m, hm_lt, ?_⟩
  simpa [axisReturnSlice, hm_eq]

/-- Helper for Exercise 18.2.4: each successive return time to the axis dominates the previous
one. -/
private theorem axisBlockedFirstCoordinate_iteratedReturn_le_succ
    {k : ℕ+} {ω : Ω} :
    (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω ≤
      (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω := by
  by_cases hfinite : (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω < ⊤
  · let n : ℕ := ENat.toNat ((τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω)
    have hn :
        (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω = n := by
      have hne : (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω ≠ ⊤ := ne_of_lt hfinite
      simpa [n] using (ENat.coe_toNat hne).symm
    have hslice :
        ω ∈ axisReturnSlice (X := X) (k + 1) n := by
      simpa [axisReturnSlice] using hn
    have hprev_lt :
        (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω < n :=
      axisReturnPrevReturn_lt_of_succSlice (X := X) (k := k) (ω := ω) hslice
    -- Proof comment: on a finite successor-return slice, the previous return occurs strictly
    -- earlier than the current return time.
    exact (le_of_lt hprev_lt).trans (by simpa [hn])
  · -- Proof comment: if the successor return time is infinite, the desired comparison is
    -- immediate because every iterated return time is `≤ ⊤`.
    show (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω ≤ (⊤ : ℕ∞)
    exact le_top

/-- Helper for Exercise 18.2.4: the positive iterated return times are monotone in the sampled
index. -/
private theorem axisBlockedFirstCoordinate_iteratedReturn_mono
    {i s : ℕ} (his : i ≤ s) {ω : Ω} :
    (τ_[fun m ω ↦ (X m ω).1, 0]^⟨i + 1, Nat.succ_pos i⟩) ω ≤
      (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω := by
  induction his with
  | refl =>
      rfl
  | @step s hs ih =>
      exact
        le_trans ih
          (axisBlockedFirstCoordinate_iteratedReturn_le_succ
            (X := X) (k := ⟨s + 1, Nat.succ_pos s⟩) (ω := ω))

/-- Helper for Exercise 18.2.4: the positive iterated return times are monotone when indexed by
positive naturals. -/
private theorem axisBlockedFirstCoordinate_iteratedReturn_mono_pNat
    {i k : ℕ+} (hik : (i : ℕ) ≤ (k : ℕ)) {ω : Ω} :
    (τ_[fun m ω ↦ (X m ω).1, 0]^i) ω ≤
      (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω := by
  rcases i with ⟨i, hi⟩
  rcases k with ⟨k, hk⟩
  cases i with
  | zero =>
      cases (Nat.not_lt_zero _ hi)
  | succ i =>
      cases k with
      | zero =>
          cases (Nat.not_lt_zero _ hk)
      | succ k =>
          -- Proof comment: after unpacking both positive indices, this is exactly the previously
          -- established monotonicity statement on natural-number predecessors.
          simpa using
            (axisBlockedFirstCoordinate_iteratedReturn_mono
              (X := X) (i := i) (s := k) (ω := ω) (by simpa using hik))

/-- Helper for Exercise 18.2.4: every finite iterated return time of the first coordinate to `0`
is strictly positive. -/
private theorem axisBlockedFirstCoordinate_iteratedReturn_pos
    {k : ℕ+} {ω : Ω} {n : ℕ}
    (hτ : (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = n) :
    0 < n := by
  cases k using PNat.recOn with
  | one =>
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn0
      have hlt :
          MeasureTheory.hittingAfter (fun m ω ↦ (X m ω).1) ({0} : Set ℤ) 1 ω < 1 := by
        have hzero :
            MeasureTheory.hittingAfter (fun m ω ↦ (X m ω).1) ({0} : Set ℤ) 1 ω = 0 := by
          simpa [iteratedEntranceTime_one] using hτ
        rw [hzero]
        norm_num
      rcases
          (MeasureTheory.hittingAfter_lt_iff
            (u := fun m ω ↦ (X m ω).1) (s := ({0} : Set ℤ)) (n := 1) (ω := ω) (i := 1)).1
            hlt with
        ⟨j, hj_mem, _⟩
      simpa [Set.mem_Ico] using hj_mem
  | succ k =>
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn0
      have hle :
          (τ_[fun m ω ↦ (X m ω).1, 0]^(k + 1)) ω ≤ 0 := by
        simpa [hτ]
      rcases
          (iteratedEntranceTime_succ_le_iff_existsHitAfter
            (Y := fun m ω ↦ (X m ω).1) (y := 0) (ω := ω) (k := k) (N := 0)).1 hle with
        ⟨m, hprev, hm0, _⟩
      have hm : m = 0 := Nat.eq_zero_of_le_zero hm0
      have : ¬ (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω < (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω :=
        lt_irrefl _
      exact this (by simpa [hm] using hprev)

/-- Helper for Exercise 18.2.4: from the horizontal neighbors `(±1, h)`, the first coordinate
hits the axis almost surely. -/
private theorem axisBlockedFirstCoordinate_everHitsZero_eq_one_of_horizontalNeighbor
    (x h : ℤ) (hx : x = 1 ∨ x = -1) :
    (F[fun z ↦ P (z, h), fun n ω ↦ (X n ω).1]) x 0 = 1 := by
  let ν : ProbabilityMeasure ℤ := axisBlockedFirstCoordinateStepLaw
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (fun z : ℤ ↦ P (z, h))
        (fun n ω ↦ (X n ω).1) := by
    have hproj :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
          (fun z : ℤ ↦ P (z, h))
          (fun n ω ↦ (X n ω).1) :=
      axisBlockedFirstCoordinate_isMarkovProcessRealization (P := P) (X := X) h
    have hkernel :
        discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix =
          dirac_convolution_kernel (ν : Measure ℤ) := by
      simpa [axisBlockedFirstCoordinateTransitionMatrix_eq_convolutionStepMatrix] using
        (convolutionStepMatrixKernel_eq ν)
    simpa [hkernel] using hproj
  have hmoment := axisBlockedFirstCoordinateStepPMF_integrable_mean_zero
  have hrec :
      IsRecurrentMarkovChain
        (fun z : ℤ ↦ P (z, h))
        (fun n ω ↦ (X n ω).1) := by
    exact
      (integerRandomWalk_recurrent_iff_zero_stepLawMean
        (ν := ν) (P := fun z : ℤ ↦ P (z, h)) (X := fun n ω ↦ (X n ω).1)
        hmoment.1).2 hmoment.2
  have hstepMass :
      0 <
        ((fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) 1) 0 ({x} : Set ℤ) := by
    rcases hx with rfl | rfl
    · -- Proof comment: the lazy first-coordinate walk reaches `1` from `0` in one step with
      -- probability `1 / 4`.
      simpa [pow_one, dirac_convolution_kernel_apply, Measure.dirac_conv, ν,
        axisBlockedFirstCoordinateStepLaw, axisBlockedFirstCoordinateStepPMF_apply]
    · -- Proof comment: the symmetric one-step move from `0` to `-1` also has probability `1 / 4`.
      simpa [pow_one, dirac_convolution_kernel_apply, Measure.dirac_conv, ν,
        axisBlockedFirstCoordinateStepLaw, axisBlockedFirstCoordinateStepPMF_apply]
  have hgreenPos :
      0 < (G[(fun z : ℤ ↦ P (z, h)), (fun n ω ↦ (X n ω).1); 1]) 0 x := by
    -- Proof comment: the positive one-step singleton mass gives a positive Green-function term.
    exact
      greenFunctionFrom_one_pos_of_posStepMass
        (P := fun z : ℤ ↦ P (z, h))
        (X := fun n ω ↦ (X n ω).1)
        (x := 0) (y := x) (n := 1)
        (by norm_num) hstepMass
  let hproc : IsStochasticProcess (fun n ω ↦ (X n ω).1) := fun n ↦ by
    let hReal :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
          (fun z : ℤ ↦ P (z, h))
          (fun n ω ↦ (X n ω).1) := inferInstance
    exact hReal.measurable_process n
  have hhitPos : 0 < (F[(fun z : ℤ ↦ P (z, h)), (fun n ω ↦ (X n ω).1)]) 0 x := by
    exact
      (greenFunctionFrom_one_pos_iff_everHitsProbability_pos
        (P := fun z : ℤ ↦ P (z, h))
        (X := fun n ω ↦ (X n ω).1)
        hproc 0 x).1 hgreenPos
  have hzeroRec :
      IsRecurrentState (fun z : ℤ ↦ P (z, h)) (fun n ω ↦ (X n ω).1) 0 := hrec 0
  -- Proof comment: recurrence of `0` together with positive communication `0 → x` lets Theorem
  -- 17.35 transport the almost-sure reverse hit probability back from `x` to `0`.
  simpa using
    (everHitsProbability_swap_eq_one_of_isRecurrentState_of_everHitsProbability_pos
      (P := fun z : ℤ ↦ P (z, h))
      (X := fun n ω ↦ (X n ω).1)
      (κ := fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
      (x := 0) (y := x) hzeroRec hhitPos)

/-- Helper for Exercise 18.2.4: from the horizontal neighbors `(±1, h)`, the first coordinate
hits the axis almost surely. -/
private theorem axisBlockedFirstCoordinate_firstReturnFinite_ae_of_horizontalNeighbor
    (x h : ℤ) (hx : x = 1 ∨ x = -1) :
    ∀ᵐ ω ∂(P (x, h) : Measure Ω), (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω < ⊤ := by
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
        (fun z : ℤ ↦ P (z, h))
        (fun n ω ↦ (X n ω).1) :=
    axisBlockedFirstCoordinate_isMarkovProcessRealization (P := P) (X := X) h
  have hhitOne :
      (F[(fun z : ℤ ↦ P (z, h)), (fun n ω ↦ (X n ω).1)]) x 0 = 1 :=
    axisBlockedFirstCoordinate_everHitsZero_eq_one_of_horizontalNeighbor
      (P := P) (X := X) x h hx
  have hmeas :
      MeasurableSet {ω | (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω < ⊤} :=
    iteratedEntranceTimeFiniteEvent_measurable
      (κ := fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
      (P := fun z : ℤ ↦ P (z, h))
      (X := fun n ω ↦ (X n ω).1) 0 1
  have hhitEvent :
      {ω | (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω < ⊤} =
        {ω | ∃ n : ℕ, 0 < n ∧ (X n ω).1 = 0} := by
    ext ω
    simpa [iteratedEntranceTime_one] using
      (hittingAfter_singleton_lt_top_iff (fun n ω ↦ (X n ω).1) 0 ω)
  have hprob_real :
      (P (x, h) : Measure Ω).real {ω | (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω < ⊤} = 1 := by
    rw [hhitEvent]
    simpa [everHitsProbability_def] using hhitOne
  have hprob :
      (P (x, h) : Measure Ω) {ω | (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω < ⊤} = 1 := by
    exact (ENNReal.toReal_eq_one_iff ((P (x, h) : Measure Ω) _)).mp hprob_real
  exact (MeasureTheory.mem_ae_iff_prob_eq_one hmeas).2 hprob

/-- Helper for Exercise 18.2.4: from a horizontal-neighbor start `(±1, h)`, the sampled first
return height is almost surely the unchanged height `h`. -/
private theorem axisReturnHeightProcess_one_eq_startHeight_ae_of_horizontalNeighbor
    (x h : ℤ) (hx : x = 1 ∨ x = -1) :
    ∀ᵐ ω ∂(P (x, h) : Measure Ω), axisReturnHeightProcess (X := X) 1 ω = h := by
  let μ : Measure Ω := (P (x, h) : Measure Ω)
  let τ : Ω → ℕ∞ := τ_[fun n ω ↦ (X n ω).1, 0]^1
  let bad : Set Ω := {ω | axisReturnHeightProcess (X := X) 1 ω ≠ h}
  have hcover :
      bad ⊆ {ω | τ ω = ⊤} ∪
        ⋃ n : ℕ, ({ω | τ ω = n + 1} ∩ {ω | (X (n + 1) ω).2 ≠ h}) := by
    intro ω hbad
    by_cases hτtop : τ ω = ⊤
    · exact Or.inl hτtop
    · rcases WithTop.ne_top_iff_exists.mp hτtop with ⟨n, hn⟩
      have hnpos : 0 < n := by
        have hle :
            (1 : ℕ∞) ≤ τ ω := by
          simpa [τ, iteratedEntranceTime_one] using
            (MeasureTheory.le_hittingAfter
              (u := fun n ω ↦ (X n ω).1) (s := ({0} : Set ℤ)) (n := 1) ω)
        rw [← hn] at hle
        have hnat : 1 ≤ n := by
          exact_mod_cast hle
        exact Nat.succ_le_iff.mp hnat
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hnpos
      right
      refine Set.mem_iUnion.2 ⟨m, ?_⟩
      refine ⟨?_, ?_⟩
      · simpa [τ, hm] using hn.symm
      · have hvalue :
            axisReturnHeightProcess (X := X) 1 ω = (X (m + 1) ω).2 := by
          simpa [axisReturnHeightProcess_pNat (X := X) ⟨1, Nat.succ_pos 0⟩, hm] using
            axisReturnHeight_eq_second_at_returnTime (X := X) (k := ⟨1, Nat.succ_pos 0⟩)
              (n := m + 1) (ω := ω) (by simpa [τ, hm] using hn.symm)
        simpa [bad, hvalue] using hbad
  have htop_zero :
      μ {ω | τ ω = ⊤} = 0 := by
    have hfinite :
        ∀ᵐ ω ∂μ, τ ω < ⊤ :=
      axisBlockedFirstCoordinate_firstReturnFinite_ae_of_horizontalNeighbor
        (P := P) (X := X) x h hx
    have hfinite_eq :
        ∀ᵐ ω ∂μ, ω ∉ {ω | τ ω = ⊤} := by
      filter_upwards [hfinite] with ω hω
      simpa [τ] using hω.ne
    exact compl_mem_ae_iff.mp hfinite_eq
  have hslices_zero :
      μ (⋃ n : ℕ, ({ω | τ ω = n + 1} ∩ {ω | (X (n + 1) ω).2 ≠ h})) = 0 := by
    refine measure_iUnion_null fun n ↦ ?_
    simpa [μ, τ] using
      axisReturnHeight_badSlice_zero_fromHorizontalNeighbor
        (P := P) (X := X) x h hx n
  have hbad_zero : μ bad = 0 := by
    refine measure_mono_null hcover ?_
    exact measure_union_null htop_zero hslices_zero
  -- Proof comment: the only way the sampled return height could differ from `h` is through a bad
  -- deterministic return slice, and those slices all have zero mass.
  exact compl_mem_ae_iff.mp <| by
    simpa [bad]
      using hbad_zero

/-- Helper for Exercise 18.2.4: the sampled-history atom up to time `s` fixes the values of the
embedded axis-return height chain at the times `0, ..., s`. -/
private def axisReturnHeightHistoryEvent (s : ℕ) (ξ : Fin (s + 1) → ℤ) : Set Ω :=
  sampledFiniteHistoryEvent (axisReturnHeightProcess (X := X)) (fun i : Fin (s + 1) ↦ (i : ℕ)) ξ

/-- Helper for Exercise 18.2.4: the sampled history up to time `s` packaged as the tuple of
values `axisReturnHeightProcess 0, ..., axisReturnHeightProcess s`. -/
private def axisReturnHeightHistoryTuple (s : ℕ) : Ω → Fin (s + 1) → ℤ :=
  fun ω i ↦ axisReturnHeightProcess (X := X) i ω

/-- Helper for Exercise 18.2.4: the sampled-height history tuple generates exactly the sampled
history filtration at time `s`. -/
private theorem generatedFiltrationSpace_axisReturnHeight_eq_historyTupleComap
    (s : ℕ) :
    generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s =
      MeasurableSpace.comap (axisReturnHeightHistoryTuple (X := X) s) inferInstance := by
  let times : Fin (s + 1) → ℕ := fun i ↦ (i : ℕ)
  have htimes : StrictMono times := by
    intro i j hij
    simpa using hij
  have hleft :
      MeasurableSpace.comap (axisReturnHeightHistoryTuple (X := X) s) inferInstance ≤
        generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s := by
    -- Proof comment: every coordinate of the sampled history tuple already lies in the sampled
    -- filtration up to time `s`.
    simpa [axisReturnHeightHistoryTuple, times] using
      historyTuple_comap_le_generatedFiltrationSpace
        (X := axisReturnHeightProcess (X := X)) times htimes
  have hright :
      generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s ≤
        MeasurableSpace.comap (axisReturnHeightHistoryTuple (X := X) s) inferInstance := by
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (s + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hcoord :
        Measurable[MeasurableSpace.comap (axisReturnHeightHistoryTuple (X := X) s) inferInstance]
          (fun ω ↦ axisReturnHeightHistoryTuple (X := X) s ω i) := by
      exact (measurable_pi_apply i).comp
        (comap_measurable (axisReturnHeightHistoryTuple (X := X) s))
    -- Proof comment: every sampled coordinate `axisReturnHeightProcess t` is recovered by
    -- evaluating the full sampled history tuple at its `t`-th coordinate.
    simpa [axisReturnHeightHistoryTuple, i] using hcoord.comap_le
  exact le_antisymm hright hleft

/-- Helper for Exercise 18.2.4: sampled-history atoms are measurable for the sampled history
filtration at their terminal time. -/
private theorem axisReturnHeightHistoryEvent_measurable_generated
    (s : ℕ) (ξ : Fin (s + 1) → ℤ) :
    MeasurableSet[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s]
      (axisReturnHeightHistoryEvent (X := X) s ξ) := by
  let times : Fin (s + 1) → ℕ := fun i ↦ (i : ℕ)
  have htimes : StrictMono times := by
    intro i j hij
    simpa using hij
  have hTuple :
      Measurable[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s]
        (fun ω k ↦ axisReturnHeightProcess (X := X) (times k) ω) := by
    rw [measurable_iff_comap_le]
    simpa [times] using
      historyTuple_comap_le_generatedFiltrationSpace
        (X := axisReturnHeightProcess (X := X)) times htimes
  -- Proof comment: the sampled-history atom is the singleton fiber of the sampled history tuple.
  rw [axisReturnHeightHistoryEvent, sampledFiniteHistoryEvent_eq_preimage_historyTuple]
  exact hTuple (measurableSet_singleton ξ)

/-- Helper for Exercise 18.2.4: distinct sampled-history atoms are disjoint. -/
private theorem axisReturnHeightHistoryEvent_pairwiseDisjoint
    (s : ℕ) :
    Pairwise
      (Function.onFun Disjoint fun ξ : Fin (s + 1) → ℤ ↦
        axisReturnHeightHistoryEvent (X := X) s ξ) := by
  intro ξ η hξη
  refine Set.disjoint_left.2 ?_
  intro ω hωξ hωη
  apply hξη
  funext i
  exact (hωξ i).symm.trans (hωη i)

/-- Helper for Exercise 18.2.4: exact return slices for a fixed sampled index are pairwise
disjoint. -/
private theorem axisReturnSlice_pairwiseDisjoint
    (k : ℕ+) :
    Pairwise fun m n ↦ Disjoint (axisReturnSlice (X := X) k m) (axisReturnSlice (X := X) k n) := by
  intro m n hmn
  refine Set.disjoint_left.2 ?_
  intro ω hm hn
  simp [axisReturnSlice] at hm hn
  exact hmn (ENat.coe_inj.mp (hm.symm.trans hn))

/-- Helper for Exercise 18.2.4: on an exact return slice for the sampled index `s`, the sampled
history atom up to time `s` is already measurable in the deterministic full history up to the
terminal time of that slice. -/
private theorem axisReturnHeightHistoryEvent_inter_returnSlice_measurable_generated
    {s n : ℕ} (hs : 0 < s) (ξ : Fin (s + 1) → ℤ) :
    MeasurableSet[generatedFiltrationSpace X n]
      (axisReturnHeightHistoryEvent (X := X) s ξ ∩
        axisReturnSlice (X := X) ⟨s, hs⟩ n) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs) with ⟨t, rfl⟩
  induction t generalizing n with
  | zero =>
      have hEq :
          axisReturnHeightHistoryEvent (X := X) 1 ξ ∩
              axisReturnSlice (X := X) ⟨1, Nat.succ_pos 0⟩ n =
            ({ω | axisReturnHeightProcess (X := X) 0 ω = ξ 0} ∩
                axisReturnSlice (X := X) ⟨1, Nat.succ_pos 0⟩ n) ∩
              {ω | (X n ω).2 = ξ (Fin.last 1)} := by
        ext ω
        constructor
        · intro hω
          refine ⟨⟨hω.1 0, hω.2⟩, ?_⟩
          have hτ :
              (τ_[fun m ω ↦ (X m ω).1, 0]^⟨1, Nat.succ_pos 0⟩) ω = n := by
            simpa [axisReturnSlice] using hω.2
          calc
            (X n ω).2 = axisReturnHeight (X := X) ⟨1, Nat.succ_pos 0⟩ ω := by
              symm
              exact axisReturnHeight_eq_second_at_returnTime (X := X) hτ
            _ = axisReturnHeightProcess (X := X) 1 ω := by
              simpa using
                (congrArg (fun f : Ω → ℤ ↦ f ω)
                  (axisReturnHeightProcess_pNat (X := X) ⟨1, Nat.succ_pos 0⟩)).symm
            _ = ξ (Fin.last 1) := hω.1 (Fin.last 1)
        · intro hω
          refine ⟨?_, hω.1.2⟩
          intro i
          fin_cases i
          · exact hω.1.1
          · have hτ :
                (τ_[fun m ω ↦ (X m ω).1, 0]^⟨1, Nat.succ_pos 0⟩) ω = n := by
              simpa [axisReturnSlice] using hω.1.2
            calc
              axisReturnHeightProcess (X := X) 1 ω =
                  axisReturnHeight (X := X) ⟨1, Nat.succ_pos 0⟩ ω := by
                    simpa using
                      congrArg (fun f : Ω → ℤ ↦ f ω)
                        (axisReturnHeightProcess_pNat (X := X) ⟨1, Nat.succ_pos 0⟩)
              _ = (X n ω).2 := by
                    exact axisReturnHeight_eq_second_at_returnTime (X := X) hτ
              _ = ξ (Fin.last 1) := hω.2
      have htimeZero :
          MeasurableSet[generatedFiltrationSpace X n]
            {ω | axisReturnHeightProcess (X := X) 0 ω = ξ 0} := by
        have hX0 :
            Measurable[generatedFiltrationSpace X n] (X 0) := by
          exact Measurable.of_comap_le <|
            (present_le_generatedHistory (X := X) 0).trans
              (generatedFiltrationSpace_monoNat (X := X) (Nat.zero_le n))
        exact (measurable_snd.comp hX0) (measurableSet_singleton (ξ 0))
      have htimeN :
          MeasurableSet[generatedFiltrationSpace X n]
            {ω | (X n ω).2 = ξ (Fin.last 1)} := by
        have hXn :
            Measurable[generatedFiltrationSpace X n] (X n) := by
          exact Measurable.of_comap_le (present_le_generatedHistory (X := X) n)
        exact (measurable_snd.comp hXn) (measurableSet_singleton (ξ (Fin.last 1)))
      -- Proof comment: on the exact first-return slice, the two sampled coordinates are just the
      -- time-`0` second coordinate and the time-`n` second coordinate.
      rw [hEq]
      exact
        (htimeZero.inter
          (axisReturnSlice_measurable_generated (X := X) ⟨1, Nat.succ_pos 0⟩ n)).inter
          htimeN
  | succ t ih =>
      let ξPrev : Fin (t + 2) → ℤ := fun i ↦ ξ (Fin.castSucc i)
      let currentSlice : Set Ω := axisReturnSlice (X := X) ⟨t + 2, Nat.succ_pos (t + 1)⟩ n
      let secondFiber : Set Ω := {ω | (X n ω).2 = ξ (Fin.last (t + 2))}
      have hEq :
          axisReturnHeightHistoryEvent (X := X) (t + 2) ξ ∩ currentSlice =
            ⋃ m : ℕ,
              (((axisReturnHeightHistoryEvent (X := X) (t + 1) ξPrev ∩
                    axisReturnSlice (X := X) ⟨t + 1, Nat.succ_pos t⟩ m) ∩
                  currentSlice) ∩ secondFiber) := by
        ext ω
        constructor
        · intro hω
          obtain ⟨m, hm_lt, hmSlice⟩ :=
            axisReturnPrevSlice_of_succSlice
              (X := X) (k := ⟨t + 1, Nat.succ_pos t⟩) (ω := ω) (n := n) hω.2
          have hprevHist :
              ω ∈ axisReturnHeightHistoryEvent (X := X) (t + 1) ξPrev := by
            intro i
            simpa [ξPrev] using hω.1 (i.castSucc)
          refine Set.mem_iUnion.2 ⟨m, ?_⟩
          refine ⟨⟨⟨hprevHist, hmSlice⟩, hω.2⟩, ?_⟩
          have hτ :
              (τ_[fun m ω ↦ (X m ω).1, 0]^⟨t + 2, Nat.succ_pos (t + 1)⟩) ω = n := by
            simpa [currentSlice] using hω.2
          calc
            (X n ω).2 = axisReturnHeight (X := X) ⟨t + 2, Nat.succ_pos (t + 1)⟩ ω := by
              symm
              exact axisReturnHeight_eq_second_at_returnTime (X := X) hτ
            _ = axisReturnHeightProcess (X := X) (t + 2) ω := by
                simpa using
                  (congrArg (fun f : Ω → ℤ ↦ f ω)
                    (axisReturnHeightProcess_pNat (X := X) ⟨t + 2, Nat.succ_pos (t + 1)⟩)).symm
            _ = ξ (Fin.last (t + 2)) := hω.1 (Fin.last (t + 2))
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
          have hmHist :
              ω ∈ axisReturnHeightHistoryEvent (X := X) (t + 1) ξPrev := hm.1.1.1
          have hmCurrent : ω ∈ currentSlice := hm.1.2
          have hmSecond : ω ∈ secondFiber := hm.2
          refine ⟨?_, hmCurrent⟩
          intro i
          cases i using Fin.lastCases with
          | last =>
              have hτ :
                  (τ_[fun m ω ↦ (X m ω).1, 0]^⟨t + 2, Nat.succ_pos (t + 1)⟩) ω = n := by
                simpa [currentSlice] using hmCurrent
              calc
                axisReturnHeightProcess (X := X) (t + 2) ω =
                    axisReturnHeight (X := X) ⟨t + 2, Nat.succ_pos (t + 1)⟩ ω := by
                      simpa using
                        congrArg (fun f : Ω → ℤ ↦ f ω)
                          (axisReturnHeightProcess_pNat (X := X)
                            ⟨t + 2, Nat.succ_pos (t + 1)⟩)
                _ = (X n ω).2 := by
                      exact axisReturnHeight_eq_second_at_returnTime (X := X) hτ
                _ = ξ (Fin.last (t + 2)) := hmSecond
          | cast j =>
              simpa [ξPrev] using hmHist j
      have hcurrent_meas :
          MeasurableSet[generatedFiltrationSpace X n] currentSlice := by
        simpa [currentSlice] using
          axisReturnSlice_measurable_generated
            (X := X) ⟨t + 2, Nat.succ_pos (t + 1)⟩ n
      have hsecond_meas :
          MeasurableSet[generatedFiltrationSpace X n] secondFiber := by
        have hXn :
            Measurable[generatedFiltrationSpace X n] (X n) := by
          exact Measurable.of_comap_le (present_le_generatedHistory (X := X) n)
        exact (measurable_snd.comp hXn) (measurableSet_singleton (ξ (Fin.last (t + 2))))
      have hpiece_meas :
          ∀ m : ℕ,
            MeasurableSet[generatedFiltrationSpace X n]
              (((axisReturnHeightHistoryEvent (X := X) (t + 1) ξPrev ∩
                    axisReturnSlice (X := X) ⟨t + 1, Nat.succ_pos t⟩ m) ∩
                  currentSlice) ∩ secondFiber) := by
        intro m
        by_cases hm : m < n
        · have hprev_meas_m :
              MeasurableSet[generatedFiltrationSpace X m]
                (axisReturnHeightHistoryEvent (X := X) (t + 1) ξPrev ∩
                  axisReturnSlice (X := X) ⟨t + 1, Nat.succ_pos t⟩ m) := by
            exact ih (n := m) (hs := Nat.succ_pos t) ξPrev
          have hprev_meas_n :
              MeasurableSet[generatedFiltrationSpace X n]
                (axisReturnHeightHistoryEvent (X := X) (t + 1) ξPrev ∩
                  axisReturnSlice (X := X) ⟨t + 1, Nat.succ_pos t⟩ m) := by
            exact
              (generatedFiltrationSpace_monoNat (X := X) (Nat.le_of_lt hm))
                _ hprev_meas_m
          exact (hprev_meas_n.inter hcurrent_meas).inter hsecond_meas
        · have hempty :
              (((axisReturnHeightHistoryEvent (X := X) (t + 1) ξPrev ∩
                      axisReturnSlice (X := X) ⟨t + 1, Nat.succ_pos t⟩ m) ∩
                    currentSlice) ∩ secondFiber) = (∅ : Set Ω) := by
            ext ω
            constructor
            · intro hω
              have hprevSlice :
                  ω ∈ axisReturnSlice (X := X) ⟨t + 1, Nat.succ_pos t⟩ m := hω.1.1.2
              have hcurrSlice : ω ∈ currentSlice := hω.1.2
              have hprev_lt :
                  (τ_[fun m ω ↦ (X m ω).1, 0]^⟨t + 1, Nat.succ_pos t⟩) ω < n :=
                axisReturnPrevReturn_lt_of_succSlice
                  (X := X) (k := ⟨t + 1, Nat.succ_pos t⟩) (ω := ω) (n := n) <| by
                    simpa [currentSlice] using hcurrSlice
              have hτprev :
                  (τ_[fun m ω ↦ (X m ω).1, 0]^⟨t + 1, Nat.succ_pos t⟩) ω = m := by
                simpa [axisReturnSlice] using hprevSlice
              exact (hm (by simpa [hτprev] using hprev_lt)).elim
            · simpa
          simpa [hempty]
      -- Proof comment: an exact successor-return slice refines into countably many predecessor
      -- exact slices, and each predecessor piece lives in the full history at time `n`.
      rw [hEq]
      exact MeasurableSet.iUnion hpiece_meas

/-- Helper for Exercise 18.2.4: an atom of the sampled history intersected with one exact return
slice is ambient measurable. -/
private theorem axisReturnHeightHistoryEvent_inter_returnSlice_measurable
    {s n : ℕ} (hs : 0 < s) (ξ : Fin (s + 1) → ℤ) :
    MeasurableSet
      (axisReturnHeightHistoryEvent (X := X) s ξ ∩
        axisReturnSlice (X := X) ⟨s, hs⟩ n) := by
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ axisBlockedKernel ^ m) P X := inferInstance
  have hgenerated :
      MeasurableSet[generatedFiltrationSpace X n]
        (axisReturnHeightHistoryEvent (X := X) s ξ ∩
          axisReturnSlice (X := X) ⟨s, hs⟩ n) :=
    axisReturnHeightHistoryEvent_inter_returnSlice_measurable_generated
      (X := X) hs ξ
  -- Proof comment: the new deterministic-time bridge already places the full atom-slice event in
  -- the terminal full-history filtration, so ambient measurability is immediate.
  exact
    (generatedHistory_le_ambient X hReal.measurable_process n)
      _ hgenerated

/-- Helper for Exercise 18.2.4: on the start law `P (0, z)`, every positive sampled-history atom
is almost surely the union of its exact return slices. -/
private theorem axisReturnHeightHistoryEvent_ae_eq_iUnion_returnSlices
    (z : ℤ) {s : ℕ} (hs : 0 < s) (ξ : Fin (s + 1) → ℤ) :
    axisReturnHeightHistoryEvent (X := X) s ξ =ᵐ[(P (0, z) : Measure Ω)]
      ⋃ n : ℕ,
        axisReturnHeightHistoryEvent (X := X) s ξ ∩
          axisReturnSlice (X := X) ⟨s, hs⟩ n := by
  filter_upwards
      [axisBlockedFirstCoordinate_iteratedReturnFinite_ae (P := P) (X := X) z ⟨s, hs⟩] with ω hω
  constructor
  · intro hωAtom
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hω)
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    refine ⟨hωAtom, ?_⟩
    simpa [axisReturnSlice] using hn.symm
  · intro hωUnion
    rcases Set.mem_iUnion.1 hωUnion with ⟨n, hn⟩
    exact hn.1

/-- Helper for Exercise 18.2.4: every sampled-history measurable set is a union of sampled-history
atoms. -/
  private theorem axisReturnHeight_measurableSet_eq_iUnion_historyEvent
    (s : ℕ) {D : Set Ω}
    (hD : MeasurableSet[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s] D) :
    ∃ T : Set (Fin (s + 1) → ℤ),
      D = ⋃ ξ ∈ T, axisReturnHeightHistoryEvent (X := X) s ξ := by
  rw [generatedFiltrationSpace_axisReturnHeight_eq_historyTupleComap (X := X) s] at hD
  rcases (MeasurableSpace.measurableSet_comap.mp hD) with ⟨T, -, hT⟩
  refine ⟨T, ?_⟩
  ext ω
  constructor
  · intro hω
    have hmemT : axisReturnHeightHistoryTuple (X := X) s ω ∈ T := by
      change ω ∈ axisReturnHeightHistoryTuple (X := X) s ⁻¹' T
      simpa [hT] using hω
    refine Set.mem_iUnion.2 ⟨axisReturnHeightHistoryTuple (X := X) s ω, ?_⟩
    refine Set.mem_iUnion.2 ⟨hmemT, ?_⟩
    intro i
    rfl
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨ξ, hω⟩
    rcases Set.mem_iUnion.1 hω with ⟨hξT, hωξ⟩
    have htuple : axisReturnHeightHistoryTuple (X := X) s ω = ξ := by
      funext i
      exact hωξ i
    change ω ∈ axisReturnHeightHistoryTuple (X := X) s ⁻¹' T
    simpa [htuple] using hξT

/-- Helper for Exercise 18.2.4: on a positive exact return slice, intersecting a sampled-history
measurable set with that slice is measurable in the terminal full-history filtration. -/
private theorem axisReturnHeight_measurableSet_inter_returnSlice_measurable_generated
    {s n : ℕ} (hs : 0 < s) {D : Set Ω}
    (hD : MeasurableSet[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s] D) :
    MeasurableSet[generatedFiltrationSpace X n]
      (D ∩ axisReturnSlice (X := X) ⟨s, hs⟩ n) := by
  rcases
      axisReturnHeight_measurableSet_eq_iUnion_historyEvent
        (X := X) s hD with ⟨T, hT⟩
  rw [hT]
  have hEq :
      ((⋃ ξ ∈ T, axisReturnHeightHistoryEvent (X := X) s ξ) ∩
          axisReturnSlice (X := X) ⟨s, hs⟩ n) =
        ⋃ ξ ∈ T,
          axisReturnHeightHistoryEvent (X := X) s ξ ∩
            axisReturnSlice (X := X) ⟨s, hs⟩ n := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω.1 with ⟨ξ, hω⟩
      rcases Set.mem_iUnion.1 hω with ⟨hξT, hωξ⟩
      exact Set.mem_iUnion.2 ⟨ξ, Set.mem_iUnion.2 ⟨hξT, ⟨hωξ, hω.2⟩⟩⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨ξ, hω⟩
      rcases Set.mem_iUnion.1 hω with ⟨hξT, hωξ⟩
      exact ⟨Set.mem_iUnion.2 ⟨ξ, Set.mem_iUnion.2 ⟨hξT, hωξ.1⟩⟩, hωξ.2⟩
  rw [hEq]
  refine MeasurableSet.iUnion ?_
  intro ξ
  refine MeasurableSet.iUnion ?_
  intro _
  simpa using
    axisReturnHeightHistoryEvent_inter_returnSlice_measurable_generated
      (X := X) hs ξ

/-- Helper for Exercise 18.2.4: a sampled-history atom fixes the current sampled height to the
last coordinate of the prescribed history tuple. -/
private theorem axisReturnHeightHistoryEvent_subset_currentFiber
    (s : ℕ) (ξ : Fin (s + 1) → ℤ) :
    axisReturnHeightHistoryEvent (X := X) s ξ ⊆
      {ω | axisReturnHeightProcess (X := X) s ω = ξ (Fin.last s)} := by
  let times : Fin (s + 1) → ℕ := fun i ↦ (i : ℕ)
  -- Proof comment: fixing the whole sampled history in particular fixes its terminal coordinate.
  simpa [axisReturnHeightHistoryEvent, times] using
    sampledFiniteHistoryEvent_subset_terminalFiber (X := axisReturnHeightProcess (X := X)) times ξ

/-- Helper for Exercise 18.2.4: each current sampled-height fiber is measurable for the sampled
history filtration at time `s`. -/
private theorem axisReturnHeightCurrentFiber_measurable_generated
    (s : ℕ) (h : ℤ) :
    MeasurableSet[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s]
      {ω | axisReturnHeightProcess (X := X) s ω = h} := by
  have hpresent :
      Measurable[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s]
        (axisReturnHeightProcess (X := X) s) := by
    exact Measurable.of_comap_le
      (present_le_generatedHistory (X := axisReturnHeightProcess (X := X)) s)
  -- Proof comment: a current fiber is the preimage of a singleton under the present sampled
  -- height coordinate.
  exact hpresent (measurableSet_singleton h)

/-- Helper for Exercise 18.2.4: the current sampled-height fibers partition the whole space. -/
private theorem iUnion_axisReturnHeightCurrentFiber_eq_univ
    (s : ℕ) :
    (⋃ h : ℤ, {ω | axisReturnHeightProcess (X := X) s ω = h}) = Set.univ := by
  ext ω
  constructor
  · intro _
    simp
  · intro _
    -- Proof comment: every path belongs to the fiber indexed by its current sampled height.
    exact Set.mem_iUnion.2 ⟨axisReturnHeightProcess (X := X) s ω, rfl⟩

/-- Helper for Exercise 18.2.4: distinct current sampled-height fibers are disjoint. -/
private theorem axisReturnHeightCurrentFiber_pairwiseDisjoint
    (s : ℕ) :
    Pairwise
      (Function.onFun Disjoint fun h : ℤ ↦ {ω | axisReturnHeightProcess (X := X) s ω = h}) := by
  intro h₁ h₂ hh
  refine Set.disjoint_left.2 ?_
  intro ω hω₁ hω₂
  exact hh (hω₁.trans hω₂.symm)

/-- Helper for Exercise 18.2.4: the realized trajectory map of the axis-blocked walk is
measurable on path space. -/
private theorem measurable_axisBlockedTrajectoryMap :
    Measurable (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) := by
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := inferInstance
  -- Proof comment: coordinatewise measurability of the realization upgrades to measurability of
  -- the full trajectory map into the product path space.
  refine measurable_pi_lambda _ fun n ↦ ?_
  exact hReal.measurable_process n

/-- Helper for Exercise 18.2.4: the path-law kernel of the realized axis-blocked walk. -/
private def axisBlockedRealizationPathKernel : Kernel AxisState (ℕ → AxisState) :=
  Kernel.ofFunOfCountable fun x ↦
    Measure.map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) (P x : Measure Ω)

/-- Helper for Exercise 18.2.4: the realized path-law rows are probability measures. -/
private instance axisBlockedRealizationPathKernel_isMarkovKernel :
    IsMarkovKernel (axisBlockedRealizationPathKernel (P := P) (X := X)) := by
  refine ⟨fun x ↦ ?_⟩
  change IsProbabilityMeasure
    (Measure.map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) (P x : Measure Ω))
  exact Measure.isProbabilityMeasure_map
    measurable_axisBlockedTrajectoryMap.aemeasurable

/-- Helper for Exercise 18.2.4: evaluating the realized path-law kernel row is just pushing `P x`
forward along the trajectory map. -/
@[simp] private theorem axisBlockedRealizationPathKernel_apply (x : AxisState) :
    axisBlockedRealizationPathKernel (P := P) (X := X) x =
      Measure.map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) (P x : Measure Ω) := rfl

/-- Helper for Exercise 18.2.4: under `P x`, the walk starts from `x` almost surely, written in
the singleton-event form used by the path-kernel API. -/
private theorem axisBlockedRealizationPathKernel_initialState_prob_eq_one (x : AxisState) :
    (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set AxisState)) = 1 := by
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := inferInstance
  -- Proof comment: evaluate the stored time-zero marginal identity on the singleton `{x}`.
  have hInit := congrArg (fun μ : Measure AxisState ↦ μ ({x} : Set AxisState)) (hReal.initial_eq x)
  simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using hInit

/-- Helper for Exercise 18.2.4: pushing a realized path row forward to time `n` recovers the
`n`-step transition row of the original walk. -/
private theorem axisBlockedRealizationPathKernel_transition
    (x : AxisState) (n : ℕ) :
    transitionKernel (axisBlockedRealizationPathKernel (P := P) (X := X)) n x =
      (axisBlockedKernel ^ n) x := by
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ axisBlockedKernel ^ m) P X := inferInstance
  -- Proof comment: evaluating the path at time `n` after pushing forward along the trajectory map
  -- gives exactly the stored time-`n` marginal of the realization.
  rw [transitionKernel_apply]
  change
    Measure.map (fun y : ℕ → AxisState ↦ y n)
      (Measure.map (fun ω : Ω ↦ fun m : ℕ ↦ X m ω) (P x : Measure Ω)) =
        (axisBlockedKernel ^ n) x
  rw [Measure.map_map]
  · simpa using hReal.transition_eq x n
  · exact measurable_pi_apply n
  · exact measurable_axisBlockedTrajectoryMap

/-- Helper for Exercise 18.2.4: the realized path-law kernel upgrades the walk to the Chapter 17
time-homogeneous path-space Markov process API. -/
private theorem axisBlockedRealizationPathKernel_isTimeHomogeneousMarkovProcess :
    IsTimeHomogeneousMarkovProcess X P
      (axisBlockedRealizationPathKernel (P := P) (X := X)) := by
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ axisBlockedKernel ^ m) P X := inferInstance
  refine
    { measurable_process := hReal.measurable_process
      initial_state := axisBlockedRealizationPathKernel_initialState_prob_eq_one (P := P) (X := X)
      path_law := ?_
      markov_property := ?_ }
  · intro x
    rfl
  · intro x A hA s t
    -- Proof comment: rewrite the owner path-kernel transition row back to the original walk's
    -- semigroup before invoking the stored Markov property of the realization.
    refine (hReal.markov_property x hA s t).trans ?_
    filter_upwards with ω
    rw [axisBlockedRealizationPathKernel_transition (P := P) (X := X) (x := X s ω) t]

/-- Helper for Exercise 18.2.4: on an exact `s`th return slice, the full state at that return
time is `(0, axisReturnHeightProcess s)`. -/
private theorem axisReturnSlice_state_eq_currentHeight
    {s n : ℕ} (hs : 0 < s) {ω : Ω}
    (hω : ω ∈ axisReturnSlice (X := X) ⟨s, hs⟩ n) :
    X n ω = (0, axisReturnHeightProcess (X := X) s ω) := by
  have hτ :
      (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s, hs⟩) ω = n := by
    simpa [axisReturnSlice] using hω
  have hnpos : 0 < n :=
    axisBlockedFirstCoordinate_iteratedReturn_pos (X := X) hτ
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hnpos
  have haxisSlice :
      ω ∈ axisReturnSlice (X := X) ⟨s, hs⟩ (m + 1) := by
    simpa [hm] using hω
  have hfirst : (X n ω).1 = 0 := by
    -- Proof comment: every positive exact return slice lands back on the axis.
    simpa [hm] using
      axisReturnSlice_subset_axisState (X := X) ⟨s, hs⟩ m haxisSlice
  have hprocess :
      axisReturnHeightProcess (X := X) s ω = axisReturnHeight (X := X) ⟨s, hs⟩ ω := by
    -- Proof comment: positive sampled times are exactly the corresponding sampled return heights.
    simpa using
      congrArg (fun f : Ω → ℤ ↦ f ω) (axisReturnHeightProcess_pNat (X := X) ⟨s, hs⟩)
  have hsecond :
      (X n ω).2 = axisReturnHeightProcess (X := X) s ω := by
    -- Proof comment: on the exact `s`th return slice, the sampled height is the second
    -- coordinate at the terminal return time.
    calc
      (X n ω).2 = axisReturnHeight (X := X) ⟨s, hs⟩ ω := by
        symm
        exact axisReturnHeight_eq_second_at_returnTime (X := X) hτ
      _ = axisReturnHeightProcess (X := X) s ω := by
        simpa using hprocess.symm
  exact Prod.ext hfirst hsecond

/-- Helper for Exercise 18.2.4: on a sampled-history atom and an exact `s`th return slice, the
full state at that return time is `(0, ξ (Fin.last s))`. -/
private theorem axisReturnHistorySlice_state_eq
    {s n : ℕ} (hs : 0 < s) {ξ : Fin (s + 1) → ℤ} {ω : Ω}
    (hω :
      ω ∈ axisReturnHeightHistoryEvent s ξ ∩
        axisReturnSlice (X := X) ⟨s, hs⟩ n) :
    X n ω = (0, ξ (Fin.last s)) := by
  have hτ :
      (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s, hs⟩) ω = n := by
    simpa [axisReturnSlice] using hω.2
  have hnpos : 0 < n :=
    axisBlockedFirstCoordinate_iteratedReturn_pos (X := X) hτ
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hnpos
  have haxisSlice :
      ω ∈ axisReturnSlice (X := X) ⟨s, hs⟩ (m + 1) := by
    simpa [hm] using hω.2
  have hfirst : (X n ω).1 = 0 := by
    -- Proof comment: every positive exact return slice lands back on the axis.
    simpa [hm] using
      axisReturnSlice_subset_axisState (X := X) ⟨s, hs⟩ m haxisSlice
  have hcurrent :
      axisReturnHeightProcess (X := X) s ω = ξ (Fin.last s) :=
    axisReturnHeightHistoryEvent_subset_currentFiber s ξ hω.1
  have hprocess :
      axisReturnHeightProcess (X := X) s ω = axisReturnHeight (X := X) ⟨s, hs⟩ ω := by
    -- Proof comment: positive sampled times are exactly the corresponding sampled return heights.
    simpa using
      congrArg (fun f : Ω → ℤ ↦ f ω) (axisReturnHeightProcess_pNat (X := X) ⟨s, hs⟩)
  have hsecond :
      (X n ω).2 = ξ (Fin.last s) := by
    -- Proof comment: identify the sampled height with the second coordinate at the exact return
    -- time.
    calc
      (X n ω).2 = axisReturnHeight (X := X) ⟨s, hs⟩ ω := by
        symm
        exact axisReturnHeight_eq_second_at_returnTime (X := X) hτ
      _ = axisReturnHeightProcess (X := X) s ω := by
        simpa using hprocess.symm
      _ = ξ (Fin.last s) := hcurrent
  exact Prod.ext hfirst hsecond

/-- Helper for Exercise 18.2.4: on path space, `axisFirstFutureReturnHeightEvent A` records that
the first strictly positive return to the axis occurs at a height in `A`. -/
private def axisFirstFutureReturnHeightEvent (A : Set ℤ) : Set (ℕ → AxisState) :=
  {path | ∃ m : ℕ, 0 < m ∧ (path m).1 = 0 ∧
      (∀ j : ℕ, 0 < j → j < m → (path j).1 ≠ 0) ∧ (path m).2 ∈ A}

/-- Helper for Exercise 18.2.4: the first-positive-axis-return event on path space is measurable.
-/
private theorem measurableSet_axisFirstFutureReturnHeightEvent
    {A : Set ℤ} (hA : MeasurableSet A) :
    MeasurableSet (axisFirstFutureReturnHeightEvent A) := by
  let slice : ℕ → Set (ℕ → AxisState) := fun m ↦
    {path | 0 < m ∧ (path m).1 = 0 ∧
        (∀ j : ℕ, 0 < j → j < m → (path j).1 ≠ 0) ∧ (path m).2 ∈ A}
  have hslice : ∀ m : ℕ, MeasurableSet (slice m) := by
    intro m
    have hfirstEq :
        MeasurableSet {path : ℕ → AxisState | (path m).1 = 0} := by
      -- Proof comment: the axis-return constraint only inspects the first coordinate at time `m`.
      exact (measurable_fst.comp (measurable_pi_apply m)) (measurableSet_singleton 0)
    have hsecondMem :
        MeasurableSet {path : ℕ → AxisState | (path m).2 ∈ A} := by
      -- Proof comment: the landing-height constraint only inspects the second coordinate at time
      -- `m`.
      exact (measurable_snd.comp (measurable_pi_apply m)) hA
    have havoidEq :
        {path : ℕ → AxisState | ∀ j : ℕ, 0 < j → j < m → (path j).1 ≠ 0} =
          ⋂ j : ℕ,
            ({path : ℕ → AxisState | ¬ (0 < j ∧ j < m)} ∪
              {path : ℕ → AxisState | (path j).1 ≠ 0}) := by
      ext path
      constructor
      · intro hpath
        refine Set.mem_iInter.2 ?_
        intro j
        by_cases hj : 0 < j ∧ j < m
        · right
          exact hpath j hj.1 hj.2
        · left
          exact hj
      · intro hpath j hj0 hjm
        have hjmem := Set.mem_iInter.1 hpath j
        have hjRange : 0 < j ∧ j < m := ⟨hj0, hjm⟩
        rcases hjmem with hbad | hneq
        · exact False.elim (hbad hjRange)
        · exact hneq
    have havoid :
        MeasurableSet {path : ℕ → AxisState | ∀ j : ℕ, 0 < j → j < m → (path j).1 ≠ 0} := by
      rw [havoidEq]
      refine MeasurableSet.iInter ?_
      intro j
      by_cases hj : ¬ (0 < j ∧ j < m)
      · simp [hj]
      · have hcoord :
            MeasurableSet {path : ℕ → AxisState | (path j).1 ≠ 0} := by
            exact ((measurable_fst.comp (measurable_pi_apply j)) (measurableSet_singleton 0)).compl
        have hconst :
            ({path : ℕ → AxisState | ¬ (0 < j ∧ j < m)} : Set (ℕ → AxisState)) = ∅ := by
          ext path
          simp [hj]
        rw [hconst]
        simpa using hcoord
    by_cases hm : 0 < m
    · -- Proof comment: after fixing a positive return time `m`, the event is an intersection of
      -- the deterministic positivity constraint, the return-to-axis constraint, the earlier-time
      -- avoidance constraints, and the landing-height constraint.
      have hslicem :
          slice m =
            {path : ℕ → AxisState | (path m).1 = 0} ∩
              {path : ℕ → AxisState | ∀ j : ℕ, 0 < j → j < m → (path j).1 ≠ 0} ∩
              {path : ℕ → AxisState | (path m).2 ∈ A} := by
        ext path
        simp [slice, hm, and_assoc, and_left_comm, and_comm]
      rw [hslicem]
      simpa [Set.inter_assoc] using hfirstEq.inter (havoid.inter hsecondMem)
    · -- Proof comment: there is no strictly positive first future return at time `0`, so the
      -- zero-time slice is empty.
      have hslicem : slice m = (∅ : Set (ℕ → AxisState)) := by
        ext path
        simp [slice, hm]
      rw [hslicem]
      simp
  have hEq :
      axisFirstFutureReturnHeightEvent A = ⋃ m : ℕ, slice m := by
    ext path
    simp [axisFirstFutureReturnHeightEvent, slice]
  -- Proof comment: the first future return event is a countable union over the exact return time.
  rw [hEq]
  exact MeasurableSet.iUnion hslice

/-- Helper for Exercise 18.2.4: for a concrete trajectory, the first future return-height event is
equivalent to the first sampled return time being finite and landing in `A`. -/
private theorem processPath_mem_axisFirstFutureReturnHeightEvent_iff
    {ω : Ω} {A : Set ℤ} :
    processPath X ω ∈ axisFirstFutureReturnHeightEvent A ↔
      (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω < ⊤ ∧
        axisReturnHeightProcess (X := X) 1 ω ∈ A := by
  constructor
  · intro hω
    rcases (by simpa [axisFirstFutureReturnHeightEvent, processPath_apply] using hω) with
      ⟨m, hmpos, hmaxis, hmbefore, hmA⟩
    have hτ_lt :
        (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω < ⊤ := by
      rw [iteratedEntranceTime_one]
      exact
        (hittingAfter_singleton_lt_top_iff (fun n ω ↦ (X n ω).1) (0 : ℤ) ω).2
          ⟨m, hmpos, hmaxis⟩
    have hτ_ne :
        (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω ≠ ⊤ := ne_of_lt hτ_lt
    let n : ℕ := ((τ_[fun n ω ↦ (X n ω).1, 0]^1) ω).untopA
    have hτ_eq :
        (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω = n := by
      rw [show n = ((τ_[fun n ω ↦ (X n ω).1, 0]^1) ω).untopA by rfl]
      rw [WithTop.untopA_eq_untop hτ_ne]
      symm
      exact WithTop.coe_untop _ hτ_ne
    have hτ_le_m :
        (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω ≤ m := by
      rw [iteratedEntranceTime_one]
      exact
        hittingAfter_le_of_mem
          (by simpa using hmpos)
          (by simpa [Set.mem_singleton_iff] using hmaxis)
    have hτ_nat_le : n ≤ m := by
      rw [← hτ_eq] at hτ_le_m
      exact_mod_cast hτ_le_m
    have hn_pos : 0 < n :=
      axisBlockedFirstCoordinate_iteratedReturn_pos (X := X) hτ_eq
    have haxisAtτ : (X n ω).1 = 0 := by
      rw [iteratedEntranceTime_one] at hτ_eq
      simpa [Set.mem_singleton_iff, hτ_eq] using
        hittingAfter_mem_set_of_ne_top
          (u := fun n ω ↦ (X n ω).1)
          (s := ({0} : Set ℤ))
          (n := 1)
          (ω := ω)
          (by simpa [iteratedEntranceTime_one] using hτ_ne)
    have hm_le_n : m ≤ n := by
      by_contra hmn
      have hnm : n < m := Nat.lt_of_not_ge hmn
      exact (hmbefore n hn_pos hnm) haxisAtτ
    have hmn : m = n := le_antisymm hm_le_n hτ_nat_le
    have hheight :
        axisReturnHeightProcess (X := X) 1 ω = (X m ω).2 := by
      calc
        axisReturnHeightProcess (X := X) 1 ω
            = axisReturnHeight (X := X) ⟨1, Nat.succ_pos 0⟩ ω := by
                simpa using
                  congrArg (fun f : Ω → ℤ ↦ f ω)
                    (axisReturnHeightProcess_pNat (X := X) ⟨1, Nat.succ_pos 0⟩)
        _ = (X n ω).2 := by
              exact axisReturnHeight_eq_second_at_returnTime (X := X) hτ_eq
        _ = (X m ω).2 := by simpa [hmn]
    exact ⟨hτ_lt, by simpa [hheight] using hmA⟩
  · rintro ⟨hτ_lt, hheightA⟩
    have hτ_ne :
        (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω ≠ ⊤ := ne_of_lt hτ_lt
    let m : ℕ := ((τ_[fun n ω ↦ (X n ω).1, 0]^1) ω).untopA
    have hτ_eq :
        (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω = m := by
      rw [show m = ((τ_[fun n ω ↦ (X n ω).1, 0]^1) ω).untopA by rfl]
      rw [WithTop.untopA_eq_untop hτ_ne]
      symm
      exact WithTop.coe_untop _ hτ_ne
    have hm_pos : 0 < m :=
      axisBlockedFirstCoordinate_iteratedReturn_pos (X := X) hτ_eq
    have haxis : (X m ω).1 = 0 := by
      rw [iteratedEntranceTime_one] at hτ_eq
      simpa [Set.mem_singleton_iff, hτ_eq] using
        hittingAfter_mem_set_of_ne_top
          (u := fun n ω ↦ (X n ω).1)
          (s := ({0} : Set ℤ))
          (n := 1)
          (ω := ω)
          (by simpa [iteratedEntranceTime_one] using hτ_ne)
    have hbefore : ∀ j : ℕ, 0 < j → j < m → (X j ω).1 ≠ 0 := by
      intro j hj0 hjm hzero
      have hj_lt :
          (j : ℕ∞) < (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω := by
        rw [hτ_eq]
        exact_mod_cast hjm
      have hj_le : (1 : ℕ) ≤ j := by omega
      exact
        (notMem_of_lt_hittingAfter
          (u := fun n ω ↦ (X n ω).1)
          (s := ({0} : Set ℤ))
          (ω := ω)
          (k := j)
          hj_lt
          hj_le)
          (by simpa [Set.mem_singleton_iff] using hzero)
    have hheight :
        axisReturnHeightProcess (X := X) 1 ω = (X m ω).2 := by
      calc
        axisReturnHeightProcess (X := X) 1 ω
            = axisReturnHeight (X := X) ⟨1, Nat.succ_pos 0⟩ ω := by
                simpa using
                  congrArg (fun f : Ω → ℤ ↦ f ω)
                    (axisReturnHeightProcess_pNat (X := X) ⟨1, Nat.succ_pos 0⟩)
        _ = (X m ω).2 := by
              exact axisReturnHeight_eq_second_at_returnTime (X := X) hτ_eq
    have hsecond : (X m ω).2 ∈ A := by
      simpa [hheight] using hheightA
    simpa [axisFirstFutureReturnHeightEvent, processPath_apply] using
      ⟨m, hm_pos, haxis, hbefore, hsecond⟩

/-- Helper for Exercise 18.2.4: on an exact `s`th return slice, once the next return is finite,
the next sampled-height event is exactly the first-future-return path event after the deterministic
return time `n`. -/
private theorem axisReturnHeightNext_mem_axisFirstFutureReturnHeightEvent_on_returnSlice_of_finite
    {s n : ℕ} (hs : 0 < s) {ω : Ω} {A : Set ℤ}
    (hω : ω ∈ axisReturnSlice (X := X) ⟨s, hs⟩ n)
    (hfinite :
      (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω < ⊤) :
    axisReturnHeightProcess (X := X) (s + 1) ω ∈ A ↔
      futurePath X n ω ∈ axisFirstFutureReturnHeightEvent A := by
  let τs : ℕ∞ := (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s, hs⟩) ω
  let τnext : ℕ∞ := (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω
  have hτs : τs = n := by
    simpa [τs, axisReturnSlice] using hω
  have hτnext_ne : τnext ≠ ⊤ := ne_of_lt hfinite
  let m : ℕ := τnext.untop hτnext_ne
  have hτnext : τnext = m := by
    symm
    exact WithTop.coe_untop _ hτnext_ne
  have hωnext :
      ω ∈ axisReturnSlice (X := X) ⟨s + 1, Nat.succ_pos s⟩ m := by
    simpa [axisReturnSlice, hτnext]
  have hprev_lt :
      (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s, hs⟩) ω < m := by
    simpa using
      axisReturnPrevReturn_lt_of_succSlice (X := X) (k := ⟨s, hs⟩) (ω := ω) hωnext
  have hnm_lt : n < m := by
    simpa [τs, hτs] using hprev_lt
  have hnm : n ≤ m := le_of_lt hnm_lt
  have hstate_next :
      X m ω = (0, axisReturnHeightProcess (X := X) (s + 1) ω) := by
    exact
      axisReturnSlice_state_eq_currentHeight
        (X := X) (s := s + 1) (hs := Nat.succ_pos s) hωnext
  have hm_pos : 0 < m := by
    exact lt_trans (Nat.succ_pos _) hnm_lt
  constructor
  · intro hnextA
    have haxis_m : (X m ω).1 = 0 := by
      simpa using congrArg Prod.fst hstate_next
    have hsecond_m : (X m ω).2 ∈ A := by
      simpa using (show (axisReturnHeightProcess (X := X) (s + 1) ω) ∈ A from hnextA)
    -- Proof comment: the finite next sampled return occurs at `m`, so the first future return
    -- after time `n` is witnessed at delay `m - n`.
    simpa [axisFirstFutureReturnHeightEvent, futurePath, processPath_apply, Nat.add_sub_of_le hnm] using
      ⟨m - n, by omega, haxis_m, ?_, hsecond_m⟩
    intro j hj0 hjlt
    by_contra hzero
    have hτnext_le :
        (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω ≤ n + j := by
      exact
        (iteratedEntranceTime_succ_le_iff_existsHitAfter
          (Y := fun m ω ↦ (X m ω).1) 0 ω ⟨s, hs⟩ (n + j)).2
          ⟨n + j, by
            rw [hτs]
            exact_mod_cast Nat.lt_add_of_pos_right n hj0, le_rfl, hzero⟩
    have hcontra : (m : ℕ∞) ≤ n + j := by
      simpa [hτnext] using hτnext_le
    exact (not_le_of_gt (by exact_mod_cast by omega : (n + j : ℕ∞) < m)) hcontra
  · intro hpath
    rcases (by simpa [axisFirstFutureReturnHeightEvent, futurePath, processPath_apply] using hpath) with
      ⟨j, hj_pos, haxis_j, hbefore, hA_j⟩
    have hτnext_le :
        (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω ≤ n + j := by
      exact
        (iteratedEntranceTime_succ_le_iff_existsHitAfter
          (Y := fun m ω ↦ (X m ω).1) 0 ω ⟨s, hs⟩ (n + j)).2
          ⟨n + j, by
            rw [hτs]
            exact_mod_cast Nat.lt_add_of_pos_right n hj_pos, le_rfl, haxis_j⟩
    have hnot_lt :
        ¬ (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω < n + j := by
      intro hlt
      have hlt_top :
          (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω < ⊤ :=
        lt_of_lt_of_le hlt le_top
      have hne_top :
          (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω ≠ ⊤ := ne_of_lt hlt_top
      let m' : ℕ := ((τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω).untop hne_top
      have hτnext_eq_m' :
          (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω = m' := by
        symm
        exact WithTop.coe_untop _ hne_top
      rcases
          (iteratedEntranceTime_succ_le_iff_existsHitAfter
            (Y := fun m ω ↦ (X m ω).1) 0 ω ⟨s, hs⟩ m').1
            (by simpa [hτnext_eq_m'] using le_rfl) with
        ⟨l, hlprev, hlm', haxis_l⟩
      have hl_lt : l < n + j := by
        have hm'lt : m' < n + j := by
          rw [← hτnext_eq_m']
          exact_mod_cast hlt
        exact lt_of_le_of_lt hlm' hm'lt
      have hdiff_pos : 0 < l - n := by
        have hn_lt_l : n < l := by
          rw [← hτs] at hlprev
          exact_mod_cast hlprev
        omega
      have hdiff_lt : l - n < j := by
        omega
      have haxis_l' : (X (n + (l - n)) ω).1 = 0 := by
        simpa [Nat.add_sub_of_le (by omega : n ≤ l)] using haxis_l
      exact hbefore (l - n) hdiff_pos hdiff_lt haxis_l'
    have hτnext_eq :
        (τ_[fun m ω ↦ (X m ω).1, 0]^⟨s + 1, Nat.succ_pos s⟩) ω = n + j := by
      exact le_antisymm hτnext_le (le_of_not_gt hnot_lt)
    have hheight_eq :
        axisReturnHeightProcess (X := X) (s + 1) ω = (X (n + j) ω).2 := by
      calc
        axisReturnHeightProcess (X := X) (s + 1) ω =
            axisReturnHeight (X := X) ⟨s + 1, Nat.succ_pos s⟩ ω := by
              simpa using
                congrArg (fun f : Ω → ℤ ↦ f ω)
                  (axisReturnHeightProcess_pNat (X := X) ⟨s + 1, Nat.succ_pos s⟩)
        _ = (X (n + j) ω).2 := by
              exact axisReturnHeight_eq_second_at_returnTime (X := X) hτnext_eq
    -- Proof comment: conversely, any first future return after time `n` pins down the exact next
    -- sampled return time by the successor-entrance minimality.
    simpa [hheight_eq] using hA_j

/-- Helper for Exercise 18.2.4: conditioning a future-path indicator at deterministic time `n`
against the realized path kernel gives the corresponding path-event row mass from the present
state. -/
private theorem axisBlockedFuturePathIndicator_condexp_eq_pathKernel
    {B : Set (ℕ → AxisState)} (hB : MeasurableSet B) (x : AxisState) (n : ℕ) :
    ((P x : Measure Ω)[fun ω ↦
        Set.indicator B (fun _ ↦ (1 : ℝ)) (futurePath X n ω)
      | generatedFiltrationSpace X n]) =ᵐ[(P x : Measure Ω)]
        fun ω ↦ (axisBlockedRealizationPathKernel (P := P) (X := X) (X n ω)).real B := by
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ axisBlockedKernel ^ m) P X := inferInstance
  let g : (ℕ → AxisState) → ℝ := Set.indicator B (fun _ ↦ (1 : ℝ))
  have hg_meas : Measurable g := by
    -- Proof comment: the future-path test function is the measurable indicator of the measurable
    -- path event `B`.
    exact Measurable.indicator measurable_const hB
  have hg_bdd : Bornology.IsBounded (Set.range g) := by
    -- Proof comment: an indicator takes only the values `0` and `1`, so its range is bounded.
    simpa [g] using isBounded_range_indicator_one B
  letI :
      IsTimeHomogeneousMarkovProcess X P
        (axisBlockedRealizationPathKernel (P := P) (X := X)) :=
    axisBlockedRealizationPathKernel_isTimeHomogeneousMarkovProcess (P := P) (X := X)
  have hAE :=
    futurePathCondExp_of_markovProcessNat
      (X := X) (P := P) (κ := axisBlockedRealizationPathKernel (P := P) (X := X))
      (hX_meas := hReal.measurable_process)
      (hX0 := axisBlockedRealizationPathKernel_initialState_prob_eq_one (P := P) (X := X))
      (hpath := axisBlockedRealizationPathKernel_apply (P := P) (X := X))
      x n g hg_meas hg_bdd
  -- Proof comment: rewrite the generic kernel integral of the indicator into the corresponding
  -- row mass of the realized path kernel.
  filter_upwards [hAE] with ω hω
  calc
    ((P x : Measure Ω)[fun ω ↦
        Set.indicator B (fun _ ↦ (1 : ℝ)) (futurePath X n ω)
      | generatedFiltrationSpace X n]) ω
        = ((P x : Measure Ω)[fun ω ↦ g (futurePath X n ω) | generatedFiltrationSpace X n]) ω := by
            rfl
    _ = ∫ y, g y ∂(axisBlockedRealizationPathKernel (P := P) (X := X) (X n ω)) := hω
    _ = (axisBlockedRealizationPathKernel (P := P) (X := X) (X n ω)).real B := by
          simpa [g] using
            (MeasureTheory.integral_indicator_one
              (μ := axisBlockedRealizationPathKernel (P := P) (X := X) (X n ω))
              (s := B) hB)

/-- Helper for Exercise 18.2.4: on a deterministic-time history event that fixes `X n = y`, the
future-path mass of any measurable path event factors through the realized path-kernel row from
`y`. -/
private theorem measureInter_eq_mul_futurePathMass_of_stateEvent
    (x y : AxisState) (n : ℕ) (A : Set Ω) (B : Set (ℕ → AxisState))
    (hB_meas : MeasurableSet B)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | futurePath X n ω ∈ B}) =
      (axisBlockedRealizationPathKernel (P := P) (X := X) y B) * (P x : Measure Ω) A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ axisBlockedKernel ^ m) P X := inferInstance
  let futureEvent : Set Ω := {ω | futurePath X n ω ∈ B}
  let rowMass : Ω → ℝ := fun ω ↦
    (axisBlockedRealizationPathKernel (P := P) (X := X) (X n ω)).real B
  have hfuture_meas : MeasurableSet futureEvent := by
    -- Proof comment: the future-path event is the measurable preimage of `B`.
    simpa [futureEvent] using (measurable_futurePath X hReal.measurable_process n) hB_meas
  have hIndicatorInt :
      Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ := by
    -- Proof comment: indicators of measurable events are integrable under the probability law
    -- `P x`.
    simpa [futureEvent] using (integrable_const (1 : ℝ)).indicator hfuture_meas
  have hgenerated_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    exact generatedHistory_le_ambient X hReal.measurable_process n
  have hcond :
      μ[fun ω ↦ Set.indicator futureEvent (fun _ ↦ (1 : ℝ)) ω
          | generatedFiltrationSpace X n] =ᵐ[μ] rowMass := by
    -- Proof comment: specialize the future-path conditional-expectation bridge to the path event
    -- `B` and rewrite the kernel integral into the local `rowMass` notation.
    simpa [futureEvent, rowMass] using
      axisBlockedFuturePathIndicator_condexp_eq_pathKernel
        (P := P) (X := X) hB_meas x n
  have hrowInt : Integrable rowMass μ := by
    exact (integrable_congr hcond).1 integrable_condExp
  have hslice_real :
      μ.real (A ∩ futureEvent) =
        ((axisBlockedRealizationPathKernel (P := P) (X := X) y).real B) * μ.real A := by
    calc
      μ.real (A ∩ futureEvent)
          = ∫ ω in A,
              (μ[fun ω ↦ Set.indicator futureEvent (fun _ ↦ (1 : ℝ)) ω
                | generatedFiltrationSpace X n]) ω ∂μ := by
                rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hA_measFiltration,
                  ← MeasureTheory.integral_indicator hA_meas]
                simpa [futureEvent, Set.indicator_indicator, Set.inter_assoc,
                  Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                  (MeasureTheory.integral_indicator_const
                    (μ := μ) (1 : ℝ) (hA_meas.inter hfuture_meas)).symm
      _ = ∫ ω in A, rowMass ω ∂μ := by
            exact MeasureTheory.integral_congr_ae hcond.restrict
      _ = ∫ ω in A,
            ((axisBlockedRealizationPathKernel (P := P) (X := X) y).real B) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
      _ =
          ((axisBlockedRealizationPathKernel (P := P) (X := X) y).real B) * μ.real A := by
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ futureEvent) =
        (axisBlockedRealizationPathKernel (P := P) (X := X) y B) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by
            exact
              (measure_lt_top (axisBlockedRealizationPathKernel (P := P) (X := X) y) B).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ, futureEvent] using hslice_enn

/-- Helper for Exercise 18.2.4: from a horizontal-neighbor start `(±1, h)`, the first sampled
return height lies in `A` with probability `1` exactly when `h ∈ A`. -/
private theorem axisReturnHeightProcess_one_mem_of_horizontalNeighbor
    (x h : ℤ) (hx : x = 1 ∨ x = -1) {A : Set ℤ} (hA : MeasurableSet A) :
    (P (x, h) : Measure Ω) (axisReturnHeightProcess (X := X) 1 ⁻¹' A) =
      if h ∈ A then 1 else 0 := by
  let μ : Measure Ω := (P (x, h) : Measure Ω)
  let returnEvent : Set Ω := axisReturnHeightProcess (X := X) 1 ⁻¹' A
  have hreturn_meas : MeasurableSet returnEvent := by
    exact (measurable_of_countable (f := axisReturnHeightProcess (X := X) 1)) hA
  by_cases hh : h ∈ A
  · have hreturn_ae :
        ∀ᵐ ω ∂μ, ω ∈ returnEvent := by
      filter_upwards
          [axisReturnHeightProcess_one_eq_startHeight_ae_of_horizontalNeighbor
            (P := P) (X := X) x h hx] with ω hω
      simpa [returnEvent, hh, hω]
    have hprob : μ returnEvent = 1 :=
      (MeasureTheory.mem_ae_iff_prob_eq_one hreturn_meas).1 hreturn_ae
    simpa [μ, hh] using hprob
  · have hreturn_ae :
        ∀ᵐ ω ∂μ, ω ∉ returnEvent := by
      filter_upwards
          [axisReturnHeightProcess_one_eq_startHeight_ae_of_horizontalNeighbor
            (P := P) (X := X) x h hx] with ω hω
      simpa [returnEvent, hh, hω]
    have hprob : μ returnEvent = 0 := compl_mem_ae_iff.mp hreturn_ae
    simpa [μ, hh] using hprob

/-- Helper for Exercise 18.2.4: from a horizontal-neighbor start `(±1, h)`, the realized path
kernel assigns the first future axis-return-height event the mass of the deterministic height `h`.
-/
private theorem axisBlockedRealizationPathKernel_axisFirstFutureReturnHeightEvent_of_horizontalNeighbor
    (x h : ℤ) (hx : x = 1 ∨ x = -1) {A : Set ℤ} (hA : MeasurableSet A) :
    axisBlockedRealizationPathKernel (P := P) (X := X) (x, h)
      (axisFirstFutureReturnHeightEvent A) =
        if h ∈ A then 1 else 0 := by
  let μ : Measure Ω := (P (x, h) : Measure Ω)
  let pathEvent : Set Ω := {ω | processPath X ω ∈ axisFirstFutureReturnHeightEvent A}
  let returnEvent : Set Ω := axisReturnHeightProcess (X := X) 1 ⁻¹' A
  have hpath_meas : MeasurableSet pathEvent := by
    simpa [pathEvent, processPath] using
      (measurable_axisBlockedTrajectoryMap (P := P) (X := X))
        (measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)
  have hreturn_finite :
      ∀ᵐ ω ∂μ, (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω < ⊤ :=
    axisBlockedFirstCoordinate_firstReturnFinite_ae_of_horizontalNeighbor
      (P := P) (X := X) x h hx
  have hpath_ae : pathEvent =ᵐ[μ] returnEvent := by
    filter_upwards [hreturn_finite] with ω hω
    constructor
    · intro hωpath
      exact
        (processPath_mem_axisFirstFutureReturnHeightEvent_iff (X := X) (ω := ω) (A := A)).1
          hωpath |>.2
    · intro hωret
      exact
        (processPath_mem_axisFirstFutureReturnHeightEvent_iff (X := X) (ω := ω) (A := A)).2
          ⟨hω, hωret⟩
  calc
    axisBlockedRealizationPathKernel (P := P) (X := X) (x, h)
        (axisFirstFutureReturnHeightEvent A)
        = μ pathEvent := by
            rw [axisBlockedRealizationPathKernel_apply]
            rw [Measure.map_apply
              (measurable_axisBlockedTrajectoryMap (P := P) (X := X))
              (measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)]
            rfl
    _ = μ returnEvent := hpath_ae.measure_eq
    _ = if h ∈ A then 1 else 0 := by
          simpa [μ, returnEvent] using
            axisReturnHeightProcess_one_mem_of_horizontalNeighbor
              (P := P) (X := X) x h hx hA

/-- Helper for Exercise 18.2.4: from an axis start `(0, h)`, the realized path kernel of the
first future return height is exactly the lazy quarter-half-quarter row at height `h`. -/
private theorem axisBlockedRealizationPathKernel_axisFirstFutureReturnHeightEvent
    (h : ℤ) {A : Set ℤ} (hA : MeasurableSet A) :
    axisBlockedRealizationPathKernel (P := P) (X := X) (0, h)
      (axisFirstFutureReturnHeightEvent A) =
        ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix) h) A := by
  let μ : Measure Ω := (P (0, h) : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := inferInstance
  let pathEvent : Set Ω := {ω | processPath X ω ∈ axisFirstFutureReturnHeightEvent A}
  let up : AxisState := (0, h + 1)
  let down : AxisState := (0, h - 1)
  let right : AxisState := (1, h)
  let left : AxisState := (-1, h)
  let stepUp : Set Ω := {ω | X 1 ω = up}
  let stepDown : Set Ω := {ω | X 1 ω = down}
  let stepRight : Set Ω := {ω | X 1 ω = right}
  let stepLeft : Set Ω := {ω | X 1 ω = left}
  let support : Set AxisState := {up, down, right, left}
  have hpath_meas : MeasurableSet pathEvent := by
    simpa [pathEvent, processPath] using
      (measurable_axisBlockedTrajectoryMap (P := P) (X := X))
        (measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)
  have hstepUp_meas : MeasurableSet stepUp := by
    simpa [stepUp] using hReal.measurable_process 1 (measurableSet_singleton up)
  have hstepDown_meas : MeasurableSet stepDown := by
    simpa [stepDown] using hReal.measurable_process 1 (measurableSet_singleton down)
  have hstepRight_meas : MeasurableSet stepRight := by
    simpa [stepRight] using hReal.measurable_process 1 (measurableSet_singleton right)
  have hstepLeft_meas : MeasurableSet stepLeft := by
    simpa [stepLeft] using hReal.measurable_process 1 (measurableSet_singleton left)
  have hpath_on_up :
      ∀ ⦃ω : Ω⦄, ω ∈ stepUp →
        (ω ∈ pathEvent ↔ h + 1 ∈ A) := by
    intro ω hω
    constructor
    · intro hωpath
      rcases (by simpa [pathEvent, axisFirstFutureReturnHeightEvent, processPath_apply] using hωpath) with
        ⟨m, hmpos, hmaxis, hmbefore, hmA⟩
      have hm_eq : m = 1 := by
        by_contra hm_ne
        have hm_lt : 1 < m := by omega
        have hbad := hmbefore 1 (by norm_num) hm_lt
        exact hbad (by simpa [stepUp, up] using congrArg Prod.fst hω)
      simpa [hm_eq, stepUp, up] using hmA
    · intro hmem
      have haxis : (X 1 ω).1 = 0 := by
        simpa [stepUp, up] using congrArg Prod.fst hω
      have hheight : (X 1 ω).2 ∈ A := by
        simpa [stepUp, up] using hmem
      -- Proof comment: after the vertical move, time `1` is already the first return to the axis.
      simpa [pathEvent, axisFirstFutureReturnHeightEvent, processPath_apply] using
        ⟨1, by norm_num, haxis, by
          intro j hj0 hj1
          omega, hheight⟩
  have hpath_on_down :
      ∀ ⦃ω : Ω⦄, ω ∈ stepDown →
        (ω ∈ pathEvent ↔ h - 1 ∈ A) := by
    intro ω hω
    constructor
    · intro hωpath
      rcases (by simpa [pathEvent, axisFirstFutureReturnHeightEvent, processPath_apply] using hωpath) with
        ⟨m, hmpos, hmaxis, hmbefore, hmA⟩
      have hm_eq : m = 1 := by
        by_contra hm_ne
        have hm_lt : 1 < m := by omega
        have hbad := hmbefore 1 (by norm_num) hm_lt
        exact hbad (by simpa [stepDown, down] using congrArg Prod.fst hω)
      simpa [hm_eq, stepDown, down] using hmA
    · intro hmem
      have haxis : (X 1 ω).1 = 0 := by
        simpa [stepDown, down] using congrArg Prod.fst hω
      have hheight : (X 1 ω).2 ∈ A := by
        simpa [stepDown, down] using hmem
      -- Proof comment: the symmetric downward vertical branch also returns immediately at time `1`.
      simpa [pathEvent, axisFirstFutureReturnHeightEvent, processPath_apply] using
        ⟨1, by norm_num, haxis, by
          intro j hj0 hj1
          omega, hheight⟩
  have hpath_on_right :
      ∀ ⦃ω : Ω⦄, ω ∈ stepRight →
        (ω ∈ pathEvent ↔ futurePath X 1 ω ∈ axisFirstFutureReturnHeightEvent A) := by
    intro ω hω
    constructor
    · intro hωpath
      rcases (by simpa [pathEvent, axisFirstFutureReturnHeightEvent, processPath_apply] using hωpath) with
        ⟨m, hmpos, hmaxis, hmbefore, hmA⟩
      have hm_ne : m ≠ 1 := by
        intro hm_eq
        have hbad := by simpa [hm_eq, stepRight, right] using congrArg Prod.fst hω
        exact hbad hmaxis
      have hm_gt : 1 < m := by omega
      -- Proof comment: after a horizontal first step, the first future return is exactly the first
      -- return of the shifted tail path.
      simpa [axisFirstFutureReturnHeightEvent, futurePath, processPath_apply] using
        ⟨m - 1, by omega, hmaxis, by
          intro j hj0 hjlt
          have hbefore' := hmbefore (j + 1) (by omega) (by omega)
          simpa using hbefore', hmA⟩
    · intro hωpath
      rcases (by simpa [axisFirstFutureReturnHeightEvent, futurePath, processPath_apply] using hωpath) with
        ⟨m, hmpos, hmaxis, hmbefore, hmA⟩
      have hstart : (X 1 ω).1 ≠ 0 := by
        simpa [stepRight, right] using congrArg Prod.fst hω
      simpa [pathEvent, axisFirstFutureReturnHeightEvent, processPath_apply] using
        ⟨m + 1, by omega, hmaxis, by
          intro j hj0 hjlt
          rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hj0) with rfl | hjlt'
          · exact hstart
          · have hbefore' := hmbefore (j - 1) (by omega) (by omega)
            simpa using hbefore', hmA⟩
  have hpath_on_left :
      ∀ ⦃ω : Ω⦄, ω ∈ stepLeft →
        (ω ∈ pathEvent ↔ futurePath X 1 ω ∈ axisFirstFutureReturnHeightEvent A) := by
    intro ω hω
    constructor
    · intro hωpath
      rcases (by simpa [pathEvent, axisFirstFutureReturnHeightEvent, processPath_apply] using hωpath) with
        ⟨m, hmpos, hmaxis, hmbefore, hmA⟩
      have hm_ne : m ≠ 1 := by
        intro hm_eq
        have hbad := by simpa [hm_eq, stepLeft, left] using congrArg Prod.fst hω
        exact hbad hmaxis
      have hm_gt : 1 < m := by omega
      -- Proof comment: the same tail-event normalization works for the left horizontal branch.
      simpa [axisFirstFutureReturnHeightEvent, futurePath, processPath_apply] using
        ⟨m - 1, by omega, hmaxis, by
          intro j hj0 hjlt
          have hbefore' := hmbefore (j + 1) (by omega) (by omega)
          simpa using hbefore', hmA⟩
    · intro hωpath
      rcases (by simpa [axisFirstFutureReturnHeightEvent, futurePath, processPath_apply] using hωpath) with
        ⟨m, hmpos, hmaxis, hmbefore, hmA⟩
      have hstart : (X 1 ω).1 ≠ 0 := by
        simpa [stepLeft, left] using congrArg Prod.fst hω
      simpa [pathEvent, axisFirstFutureReturnHeightEvent, processPath_apply] using
        ⟨m + 1, by omega, hmaxis, by
          intro j hj0 hjlt
          rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hj0) with rfl | hjlt'
          · exact hstart
          · have hbefore' := hmbefore (j - 1) (by omega) (by omega)
            simpa using hbefore', hmA⟩
  have hsupport_prob :
      μ {ω | X 1 ω ∈ support} = 1 := by
    rw [show {ω | X 1 ω ∈ support} = X 1 ⁻¹' support by rfl]
    rw [← Measure.map_apply (hReal.measurable_process 1) (show MeasurableSet support from MeasurableSet.of_discrete)]
    rw [hReal.transition_eq (0, h) 1]
    simp [support, axisBlockedKernel, discreteMatrixKernel_apply, Measure.sum_apply,
      vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor, isHorizontalNeighbor,
      isVerticalNeighbor]
  have hsupport_zero :
      μ (pathEvent ∩ {ω | X 1 ω ∉ support}) = 0 := by
    have hsubset :
        pathEvent ∩ {ω | X 1 ω ∉ support} ⊆ {ω | X 1 ω ∉ support} := by
      intro ω hω
      exact hω.2
    have hcompl :
        μ {ω | X 1 ω ∉ support} = 0 := by
      exact compl_mem_ae_iff.mp <| (MeasureTheory.mem_ae_iff_prob_eq_one
        (show MeasurableSet {ω | X 1 ω ∈ support} by
          simpa using hReal.measurable_process 1 (show MeasurableSet support from MeasurableSet.of_discrete))).2 hsupport_prob
    exact measure_mono_null hsubset hcompl
  have hUp_mass :
      μ (pathEvent ∩ stepUp) =
        if h + 1 ∈ A then (1 / 4 : ℝ≥0∞) else 0 := by
    by_cases hup : h + 1 ∈ A
    · have hEq : pathEvent ∩ stepUp = stepUp := by
        ext ω
        constructor
        · intro hω
          exact hω.2
        · intro hω
          exact ⟨(hpath_on_up hω).2 hup, hω⟩
      rw [hEq]
      rw [show stepUp = X 1 ⁻¹' ({up} : Set AxisState) by ext ω; simp [stepUp]]
      rw [← Measure.map_apply (hReal.measurable_process 1) (measurableSet_singleton up)]
      rw [hReal.transition_eq (0, h) 1]
      simp [hup, up, axisBlockedKernel_singletonEqEntry, vertical_axis_blocked_walk_transition_matrix,
        isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor]
    · have hEq : pathEvent ∩ stepUp = (∅ : Set Ω) := by
        ext ω
        constructor
        · intro hω
          exact False.elim <| hup ((hpath_on_up hω.2).1 hω.1)
        · simp
      simp [hEq, hup]
  have hDown_mass :
      μ (pathEvent ∩ stepDown) =
        if h - 1 ∈ A then (1 / 4 : ℝ≥0∞) else 0 := by
    by_cases hdown : h - 1 ∈ A
    · have hEq : pathEvent ∩ stepDown = stepDown := by
        ext ω
        constructor
        · intro hω
          exact hω.2
        · intro hω
          exact ⟨(hpath_on_down hω).2 hdown, hω⟩
      rw [hEq]
      rw [show stepDown = X 1 ⁻¹' ({down} : Set AxisState) by ext ω; simp [stepDown]]
      rw [← Measure.map_apply (hReal.measurable_process 1) (measurableSet_singleton down)]
      rw [hReal.transition_eq (0, h) 1]
      simp [hdown, down, axisBlockedKernel_singletonEqEntry, vertical_axis_blocked_walk_transition_matrix,
        isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor]
    · have hEq : pathEvent ∩ stepDown = (∅ : Set Ω) := by
        ext ω
        constructor
        · intro hω
          exact False.elim <| hdown ((hpath_on_down hω.2).1 hω.1)
        · simp
      simp [hEq, hdown]
  have hRight_mass :
      μ (pathEvent ∩ stepRight) =
        (if h ∈ A then 1 else 0) * (1 / 4 : ℝ≥0∞) := by
    let futureEvent : Set Ω := {ω | futurePath X 1 ω ∈ axisFirstFutureReturnHeightEvent A}
    have hEq :
        pathEvent ∩ stepRight = futureEvent ∩ stepRight := by
      ext ω
      constructor
      · intro hω
        exact ⟨(hpath_on_right hω.2).1 hω.1, hω.2⟩
      · intro hω
        exact ⟨(hpath_on_right hω.2).2 hω.1, hω.2⟩
    rw [hEq]
    rw [inter_comm]
    have hstate : ∀ ⦃ω : Ω⦄, ω ∈ stepRight → X 1 ω = right := by
      intro ω hω
      exact hω
    rw [measureInter_eq_mul_futurePathMass_of_stateEvent
      (P := P) (X := X) (x := (0, h)) (y := right) (n := 1)
      (A := stepRight) (B := axisFirstFutureReturnHeightEvent A)
      (hB_meas := measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)
      (hA_meas := hstepRight_meas)
      (hA_measFiltration := by
        exact Measurable.of_comap_le (present_le_generatedHistory (X := X) 1) (measurableSet_singleton right))
      hstate]
    rw [axisBlockedRealizationPathKernel_axisFirstFutureReturnHeightEvent_of_horizontalNeighbor
      (P := P) (X := X) 1 h (by simp [right]) hA]
    rw [show stepRight = X 1 ⁻¹' ({right} : Set AxisState) by ext ω; simp [stepRight]]
    rw [← Measure.map_apply (hReal.measurable_process 1) (measurableSet_singleton right)]
    rw [hReal.transition_eq (0, h) 1]
    simp [right, axisBlockedKernel_singletonEqEntry, vertical_axis_blocked_walk_transition_matrix,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, mul_comm, mul_left_comm, mul_assoc]
  have hLeft_mass :
      μ (pathEvent ∩ stepLeft) =
        (if h ∈ A then 1 else 0) * (1 / 4 : ℝ≥0∞) := by
    let futureEvent : Set Ω := {ω | futurePath X 1 ω ∈ axisFirstFutureReturnHeightEvent A}
    have hEq :
        pathEvent ∩ stepLeft = futureEvent ∩ stepLeft := by
      ext ω
      constructor
      · intro hω
        exact ⟨(hpath_on_left hω.2).1 hω.1, hω.2⟩
      · intro hω
        exact ⟨(hpath_on_left hω.2).2 hω.1, hω.2⟩
    rw [hEq]
    rw [inter_comm]
    have hstate : ∀ ⦃ω : Ω⦄, ω ∈ stepLeft → X 1 ω = left := by
      intro ω hω
      exact hω
    rw [measureInter_eq_mul_futurePathMass_of_stateEvent
      (P := P) (X := X) (x := (0, h)) (y := left) (n := 1)
      (A := stepLeft) (B := axisFirstFutureReturnHeightEvent A)
      (hB_meas := measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)
      (hA_meas := hstepLeft_meas)
      (hA_measFiltration := by
        exact Measurable.of_comap_le (present_le_generatedHistory (X := X) 1) (measurableSet_singleton left))
      hstate]
    rw [axisBlockedRealizationPathKernel_axisFirstFutureReturnHeightEvent_of_horizontalNeighbor
      (P := P) (X := X) (-1) h (by simp [left]) hA]
    rw [show stepLeft = X 1 ⁻¹' ({left} : Set AxisState) by ext ω; simp [stepLeft]]
    rw [← Measure.map_apply (hReal.measurable_process 1) (measurableSet_singleton left)]
    rw [hReal.transition_eq (0, h) 1]
    simp [left, axisBlockedKernel_singletonEqEntry, vertical_axis_blocked_walk_transition_matrix,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, mul_comm, mul_left_comm, mul_assoc]
  have hdisj_up_down : Disjoint (pathEvent ∩ stepUp) (pathEvent ∩ stepDown) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωup hωdown
    have : up = down := hωup.2.symm.trans hωdown.2
    omega
  have hdisj_up_right : Disjoint (pathEvent ∩ stepUp) (pathEvent ∩ stepRight) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωup hωright
    have : up = right := hωup.2.symm.trans hωright.2
    omega
  have hdisj_up_left : Disjoint (pathEvent ∩ stepUp) (pathEvent ∩ stepLeft) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωup hωleft
    have : up = left := hωup.2.symm.trans hωleft.2
    omega
  have hdisj_down_right : Disjoint (pathEvent ∩ stepDown) (pathEvent ∩ stepRight) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωdown hωright
    have : down = right := hωdown.2.symm.trans hωright.2
    omega
  have hdisj_down_left : Disjoint (pathEvent ∩ stepDown) (pathEvent ∩ stepLeft) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωdown hωleft
    have : down = left := hωdown.2.symm.trans hωleft.2
    omega
  have hdisj_right_left : Disjoint (pathEvent ∩ stepRight) (pathEvent ∩ stepLeft) := by
    refine Set.disjoint_left.2 ?_
    intro ω hωright hωleft
    have : right = left := hωright.2.symm.trans hωleft.2
    omega
  have hcover :
      pathEvent =
        (pathEvent ∩ stepUp) ∪ (pathEvent ∩ stepDown) ∪
          (pathEvent ∩ stepRight) ∪ (pathEvent ∩ stepLeft) ∪
            (pathEvent ∩ {ω | X 1 ω ∉ support}) := by
    ext ω
    constructor
    · intro hω
      by_cases hsupp : X 1 ω ∈ support
      · simp [stepUp, stepDown, stepRight, stepLeft, support, hsupp, hω]
      · simp [stepUp, stepDown, stepRight, stepLeft, support, hsupp, hω]
    · intro hω
      simp at hω
      rcases hω with hω | hω | hω | hω | hω <;> exact hω.1
  calc
    axisBlockedRealizationPathKernel (P := P) (X := X) (0, h)
        (axisFirstFutureReturnHeightEvent A)
        = μ pathEvent := by
            rw [axisBlockedRealizationPathKernel_apply]
            rw [Measure.map_apply
              (measurable_axisBlockedTrajectoryMap (P := P) (X := X))
              (measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)]
            rfl
    _ =
        μ (pathEvent ∩ stepUp) + μ (pathEvent ∩ stepDown) +
          μ (pathEvent ∩ stepRight) + μ (pathEvent ∩ stepLeft) := by
            rw [hcover]
            rw [Measure.union_apply hdisj_up_down hstepUp_meas.inter hstepDown_meas.inter]
            rw [Measure.union_apply
              (Set.disjoint_union_left.2 ⟨hdisj_up_right, hdisj_down_right⟩)
              (hstepUp_meas.inter.union (hstepDown_meas.inter))
              hstepRight_meas.inter]
            rw [Measure.union_apply
              (Set.disjoint_union_left.2
                ⟨Set.disjoint_union_left.2 ⟨hdisj_up_left, hdisj_down_left⟩, hdisj_right_left⟩)
              ((hstepUp_meas.inter.union hstepDown_meas.inter).union hstepRight_meas.inter)
              hstepLeft_meas.inter]
            rw [Measure.union_apply
              (by
                refine Set.disjoint_left.2 ?_
                intro ω hωmain hωrest
                exact hωrest.2 (by
                  simpa [stepUp, stepDown, stepRight, stepLeft, support] using hωmain))
              (((hstepUp_meas.inter.union hstepDown_meas.inter).union hstepRight_meas.inter).union
                hstepLeft_meas.inter)
              (hpath_meas.inter <| by
                simpa using hReal.measurable_process 1
                  (show MeasurableSet supportᶜ by
                    simpa using (show MeasurableSet support from MeasurableSet.of_discrete).compl))]
            simp [hsupport_zero, add_assoc, add_left_comm, add_comm]
    _ =
        (if h + 1 ∈ A then (1 / 4 : ℝ≥0∞) else 0) +
          (if h - 1 ∈ A then (1 / 4 : ℝ≥0∞) else 0) +
            ((if h ∈ A then 1 else 0) * (1 / 4 : ℝ≥0∞)) +
              ((if h ∈ A then 1 else 0) * (1 / 4 : ℝ≥0∞)) := by
                rw [hUp_mass, hDown_mass, hRight_mass, hLeft_mass]
    _ = ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix) h) A := by
          classical
          rw [discreteMatrixKernel_apply, Measure.sum_apply _ hA]
          have hsplit :
              (fun y : ℤ ↦ axisBlockedFirstCoordinateTransitionMatrix h y * A.indicator 1 y) =
                fun y : ℤ ↦
                  (if y = h + 1 then (1 / 4 : ℝ≥0∞) else 0) +
                    ((if y = h then (1 / 2 : ℝ≥0∞) else 0) +
                      (if y = h - 1 then (1 / 4 : ℝ≥0∞) else 0)) * A.indicator 1 y := by
                funext y
                by_cases hy1 : y = h + 1
                · have hy0 : y ≠ h := by omega
                  have hym1 : y ≠ h - 1 := by omega
                  simp [axisBlockedFirstCoordinateTransitionMatrix, hy1, hy0, hym1, mul_assoc]
                · by_cases hy0 : y = h
                  · have hym1 : y ≠ h - 1 := by omega
                    simp [axisBlockedFirstCoordinateTransitionMatrix, hy1, hy0, hym1, mul_assoc]
                  · by_cases hym1 : y = h - 1
                    · simp [axisBlockedFirstCoordinateTransitionMatrix, hy1, hy0, hym1, mul_assoc]
                    · simp [axisBlockedFirstCoordinateTransitionMatrix, hy1, hy0, hym1]
          rw [hsplit, ENNReal.tsum_add, ENNReal.tsum_add]
          rw [tsum_eq_single (h + 1), tsum_eq_single h, tsum_eq_single (h - 1)]
          · by_cases hhplus : h + 1 ∈ A
            · by_cases hh : h ∈ A
              · by_cases hhminus : h - 1 ∈ A
                · simp [hhplus, hh, hhminus, add_assoc, add_left_comm, add_comm, mul_assoc]
                · simp [hhplus, hh, hhminus, add_assoc, add_left_comm, add_comm, mul_assoc]
              · by_cases hhminus : h - 1 ∈ A
                · simp [hhplus, hh, hhminus, add_assoc, add_left_comm, add_comm, mul_assoc]
                · simp [hhplus, hh, hhminus, add_assoc, add_left_comm, add_comm, mul_assoc]
            · by_cases hh : h ∈ A
              · by_cases hhminus : h - 1 ∈ A
                · simp [hhplus, hh, hhminus, add_assoc, add_left_comm, add_comm, mul_assoc]
                · simp [hhplus, hh, hhminus, add_assoc, add_left_comm, add_comm, mul_assoc]
              · by_cases hhminus : h - 1 ∈ A
                · simp [hhplus, hh, hhminus, add_assoc, add_left_comm, add_comm, mul_assoc]
                · simp [hhplus, hh, hhminus, add_assoc, add_left_comm, add_comm, mul_assoc]
          · intro y hy
            simp [hy]
          · intro y hy
            simp [hy]
          · intro y hy
            simp [hy]

/-- Helper for Exercise 18.2.4: the sampled one-step transition candidate depends measurably on
the current sampled height. -/
private theorem axisReturnHeightTransitionCandidate_measurable
    (s : ℕ) {A : Set ℤ} (hA : MeasurableSet A) :
    Measurable[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s]
      (fun ω ↦
        ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
          (axisReturnHeightProcess (X := X) s ω)).real A) := by
  have hpresent :
      Measurable[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s]
        (axisReturnHeightProcess (X := X) s) := by
    exact Measurable.of_comap_le
      (present_le_generatedHistory (X := axisReturnHeightProcess (X := X)) s)
  -- Proof comment: the kernel row is a measurable function of the current sampled height.
  exact
    ((Kernel.measurable_coe
      (discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix) hA).ennreal_toReal).comp
      hpresent

/-- Helper for Exercise 18.2.4: every positive sampled return time is a stopping time for the
full walk filtration. -/
private theorem axisReturnTime_isStoppingTime
    (k : ℕ+) :
    IsStoppingTime (processFiltration X)
      (fun ω ↦ ((τ_[fun n ω ↦ (X n ω).1, 0]^k) ω : ℕ∞)) := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := by
    simpa [axisBlockedKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix ^ n)
          P X)
  intro N
  have hproj :
      generatedFiltrationSpace (fun n ω ↦ (X n ω).1) N ≤ generatedFiltrationSpace X N :=
    generatedFiltrationSpace_comp_le (X := X) Prod.fst measurable_fst N
  have hgenerated :
      MeasurableSet[generatedFiltrationSpace X N]
        {ω | ((τ_[fun n ω ↦ (X n ω).1, 0]^k) ω : ℕ∞) ≤ N} := by
    exact hproj _ <|
      iteratedEntranceTime_le_measurable_generated
        (Y := fun n ω ↦ (X n ω).1) 0 k N
  have hprocess_eq : processFiltration X N = generatedFiltrationSpace X N := by
    -- Proof comment: for the realized walk, the ambient-space infimum in `processFiltration`
    -- collapses because every coordinate is already ambient measurable.
    simpa [processFiltration, generatedFiltrationSpace] using
      inf_eq_right.mpr (generatedHistory_le_ambient X hReal.measurable_process N)
  simpa [hprocess_eq] using
    (show MeasurableSet[generatedFiltrationSpace X N]
      {ω | ((τ_[fun n ω ↦ (X n ω).1, 0]^k) ω : ℕ∞) ≤ (N : ℕ∞)} from hgenerated)

/-- Helper for Exercise 18.2.4: the sampled-height history up to the `k`-th sampled time is
already measurable at the stopping-time sigma-algebra of the `k`-th axis return. -/
private theorem axisReturnHeightHistory_le_returnTimeSigma
    (k : ℕ+) :
    generatedFiltrationSpace (axisReturnHeightProcess (X := X)) k ≤
      (axisReturnTime_isStoppingTime k).measurableSpace := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := by
    simpa [axisBlockedKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix ^ n)
          P X)
  let Y : ℕ → Ω → ℤ := fun n ω ↦ (X n ω).2
  have hXadapt : Adapted (processFiltration X) X := by
    intro n
    -- Proof comment: the time-`n` state is one of the generators of the process filtration and
    -- is ambient measurable by the realization.
    refine measurable_iff_comap_le.2 ?_
    exact le_inf
      ((hReal.measurable_process n).comap_le)
      (le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl)
  have hYadapt : Adapted (processFiltration X) Y := by
    intro n
    -- Proof comment: the second coordinate process is just the measurable projection of the full
    -- walk.
    exact measurable_snd.comp (hXadapt n)
  let τk : Ω → ℕ∞ := fun ω ↦ ((τ_[fun n ω ↦ (X n ω).1, 0]^k) ω : ℕ∞)
  let hτk : IsStoppingTime (processFiltration X) τk :=
    axisReturnTime_isStoppingTime k
  rw [generatedFiltrationSpace]
  refine iSup₂_le fun i hi ↦ ?_
  have hcoord :
      Measurable[hτk.measurableSpace] (axisReturnHeightProcess (X := X) i) := by
    cases i with
    | zero =>
        let τ0 : Ω → ℕ∞ := fun _ ↦ 0
        have hτ0 : IsStoppingTime (processFiltration X) τ0 := by
          simpa [τ0] using isStoppingTime_const (processFiltration X) 0
        have hτ0_le : ∀ ω, τ0 ω ≤ τk ω := by
          intro ω
          simp [τ0, τk]
        have hstop :
            Measurable[hτk.measurableSpace] (stoppedValue Y τ0) := by
          exact
            (measurable_stoppedValue
              hYadapt.stronglyAdapted.progMeasurable_of_discrete hτ0).mono
              (hτ0.measurableSpace_le_of_le hτ0_le) le_rfl
        -- Proof comment: time `0` of the sampled-height process is the stopped second coordinate
        -- at the constant stopping time `0`.
        simpa [axisReturnHeightProcess, Y, τ0, stoppedValue] using hstop
    | succ i =>
        let τi : Ω → ℕ∞ := fun ω ↦
          ((τ_[fun n ω ↦ (X n ω).1, 0]^⟨i + 1, Nat.succ_pos i⟩) ω : ℕ∞)
        have hτi : IsStoppingTime (processFiltration X) τi :=
          axisReturnTime_isStoppingTime ⟨i + 1, Nat.succ_pos i⟩
        have hτi_le : ∀ ω, τi ω ≤ τk ω := by
          intro ω
          exact
            axisBlockedFirstCoordinate_iteratedReturn_mono_pNat
              (i := ⟨i + 1, Nat.succ_pos i⟩) (k := k) (ω := ω) <|
                by simpa using hi
        have hstop :
            Measurable[hτk.measurableSpace] (stoppedValue Y τi) := by
          exact
            (measurable_stoppedValue
              hYadapt.stronglyAdapted.progMeasurable_of_discrete hτi).mono
              (hτi.measurableSpace_le_of_le hτi_le) le_rfl
        -- Proof comment: every positive sampled-height coordinate is exactly the second
        -- coordinate stopped at its corresponding iterated return time.
        simpa [axisReturnHeightProcess, axisReturnHeight, Y, τi] using hstop
  exact hcoord.comap_le

/-- Helper for Exercise 18.2.4: the sampled return-height process satisfies the one-step
conditional law of the lazy first-coordinate kernel. -/
private theorem axisReturnHeightNext_setIntegral_eq_on_historySlice
    (z : ℤ) {s n : ℕ} (hs : 0 < s) (ξ : Fin (s + 1) → ℤ) {A : Set ℤ}
    (hA : MeasurableSet A) :
    ∫ ω in axisReturnHeightHistoryEvent (X := X) s ξ ∩
        axisReturnSlice (X := X) ⟨s, hs⟩ n,
      ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
        (axisReturnHeightProcess (X := X) s ω)).real A ∂(P (0, z) : Measure Ω) =
      ∫ ω in axisReturnHeightHistoryEvent (X := X) s ξ ∩
          axisReturnSlice (X := X) ⟨s, hs⟩ n,
        (axisReturnHeightProcess (X := X) (s + 1) ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) ω
          ∂(P (0, z) : Measure Ω) := by
  let μ : Measure Ω := (P (0, z) : Measure Ω)
  let Hslice : Set Ω :=
    axisReturnHeightHistoryEvent (X := X) s ξ ∩ axisReturnSlice (X := X) ⟨s, hs⟩ n
  let nextEvent : Set Ω := axisReturnHeightProcess (X := X) (s + 1) ⁻¹' A
  let futureEvent : Set Ω := {ω | futurePath X n ω ∈ axisFirstFutureReturnHeightEvent A}
  let c : ℝ :=
    ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix) (ξ (Fin.last s))).real A
  have hHslice_meas : MeasurableSet Hslice := by
    simpa [Hslice] using
      axisReturnHeightHistoryEvent_inter_returnSlice_measurable
        (X := X) hs (ξ := ξ) (n := n)
  have hleft_eq :
      EqOn
        (fun ω ↦
          ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
            (axisReturnHeightProcess (X := X) s ω)).real A)
        (fun _ ↦ c) Hslice := by
    intro ω hω
    have hcurrent :
        axisReturnHeightProcess (X := X) s ω = ξ (Fin.last s) :=
      axisReturnHeightHistoryEvent_subset_currentFiber (X := X) s ξ hω.1
    simp [c, hcurrent]
  have hleft :
      ∫ ω in Hslice,
          ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
            (axisReturnHeightProcess (X := X) s ω)).real A ∂μ =
        c * μ.real Hslice := by
    calc
      ∫ ω in Hslice,
          ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
            (axisReturnHeightProcess (X := X) s ω)).real A ∂μ
          = ∫ ω in Hslice, c ∂μ := by
              exact MeasureTheory.setIntegral_congr_fun hHslice_meas hleft_eq
      _ = c * μ.real Hslice := by
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hbridge :
      Hslice ∩ nextEvent =ᵐ[μ] Hslice ∩ futureEvent := by
    filter_upwards
        [axisBlockedFirstCoordinate_iteratedReturnFinite_ae
          (P := P) (X := X) z ⟨s + 1, Nat.succ_pos s⟩] with ω hfinite
    by_cases hω : ω ∈ Hslice
    · have hslice : ω ∈ axisReturnSlice (X := X) ⟨s, hs⟩ n := hω.2
      have hiff :=
        axisReturnHeightNext_mem_axisFirstFutureReturnHeightEvent_on_returnSlice_of_finite
          (X := X) hs hslice hfinite (A := A)
      simp [Hslice, nextEvent, futureEvent, hω, hiff]
    · simp [Hslice, hω]
  have hfuture_mass :
      μ (Hslice ∩ futureEvent) =
        axisBlockedRealizationPathKernel (P := P) (X := X) (0, ξ (Fin.last s))
            (axisFirstFutureReturnHeightEvent A) *
          μ Hslice := by
    rw [measureInter_eq_mul_futurePathMass_of_stateEvent
      (P := P) (X := X) (x := (0, z)) (y := (0, ξ (Fin.last s))) (n := n)
      (A := Hslice) (B := axisFirstFutureReturnHeightEvent A)
      (hB_meas := measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)
      (hA_meas := hHslice_meas)
      (hA_measFiltration := by
        simpa [Hslice] using
          axisReturnHeightHistoryEvent_inter_returnSlice_measurable_generated
            (X := X) hs (ξ := ξ) (n := n))
      (hA_state := by
        intro ω hω
        simpa [Hslice] using
          axisReturnHistorySlice_state_eq (X := X) hs (ξ := ξ) (n := n) hω)]
  have hfuture_meas : MeasurableSet futureEvent := by
    simpa [futureEvent] using
      (measurable_futurePath X
        (by
          let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ axisBlockedKernel ^ m) P X :=
            inferInstance
          exact hReal.measurable_process) n)
        (measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)
  have hright :
      ∫ ω in Hslice, nextEvent.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ =
        c * μ.real Hslice := by
    calc
      ∫ ω in Hslice, nextEvent.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ
          = ∫ ω in Hslice ∩ nextEvent, (1 : ℝ) ∂μ := by
              rw [← MeasureTheory.integral_indicator hHslice_meas]
              simp [Hslice, nextEvent, Set.indicator_indicator, Set.inter_assoc,
                Set.inter_left_comm, Set.inter_comm, smul_eq_mul]
      _ = ∫ ω in Hslice ∩ futureEvent, (1 : ℝ) ∂μ := by
            exact MeasureTheory.setIntegral_congr_set hbridge
      _ = μ.real (Hslice ∩ futureEvent) := by
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, one_mul]
      _ =
          (axisBlockedRealizationPathKernel (P := P) (X := X) (0, ξ (Fin.last s))).real
              (axisFirstFutureReturnHeightEvent A) *
            μ.real Hslice := by
              simpa [μ, Hslice, futureEvent, Measure.real_def, ENNReal.toReal_mul, mul_comm] using
                congrArg ENNReal.toReal hfuture_mass
      _ = c * μ.real Hslice := by
            rw [axisBlockedRealizationPathKernel_axisFirstFutureReturnHeightEvent
              (P := P) (X := X) (h := ξ (Fin.last s)) hA]
            rfl
  -- Proof comment: on each history-slice atom the current sampled height is fixed, and the next
  -- sampled-height event matches the deterministic-time future-path event up to the next-return
  -- finiteness null set.
  exact hleft.trans hright.symm

/-- Helper for Exercise 18.2.4: on a sampled-history atom, the next sampled-height event has the
same set integral as the lazy one-step transition candidate. -/
private theorem axisReturnHeightNext_setIntegral_eq_on_historyEvent
    (z : ℤ) {s : ℕ} (hs : 0 < s) (ξ : Fin (s + 1) → ℤ) {A : Set ℤ}
    (hA : MeasurableSet A) :
    ∫ ω in axisReturnHeightHistoryEvent (X := X) s ξ,
      ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
        (axisReturnHeightProcess (X := X) s ω)).real A ∂(P (0, z) : Measure Ω) =
      ∫ ω in axisReturnHeightHistoryEvent (X := X) s ξ,
        (axisReturnHeightProcess (X := X) (s + 1) ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) ω
          ∂(P (0, z) : Measure Ω) := by
  let μ : Measure Ω := (P (0, z) : Measure Ω)
  let H : Set Ω := axisReturnHeightHistoryEvent (X := X) s ξ
  let nextEvent : Set Ω := axisReturnHeightProcess (X := X) (s + 1) ⁻¹' A
  let g : Ω → ℝ := fun ω ↦
    ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
      (axisReturnHeightProcess (X := X) s ω)).real A
  have hsampled_meas :
      ∀ m : ℕ, Measurable (axisReturnHeightProcess (X := X) m) := by
    intro m
    exact measurable_of_countable (f := axisReturnHeightProcess (X := X) m)
  have hambient_le :
      generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s ≤ ‹MeasurableSpace Ω› := by
    exact generatedHistory_le_ambient (axisReturnHeightProcess (X := X)) hsampled_meas s
  have hH_meas : MeasurableSet H := by
    exact hambient_le _ <|
      axisReturnHeightHistoryEvent_measurable_generated (X := X) (s := s) ξ
  have hg_meas :
      AEStronglyMeasurable g μ := by
    exact
      (axisReturnHeightTransitionCandidate_measurable (X := X) s hA)
        .aestronglyMeasurable
  have hg_int : Integrable g μ := by
    refine Integrable.of_bound hg_meas 1 ?_
    filter_upwards with ω
    have hnonneg :
        0 ≤ g ω := ENNReal.toReal_nonneg
    have hle :
        g ω ≤ 1 := by
      have hrow_le :
          ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
            (axisReturnHeightProcess (X := X) s ω)) A ≤ 1 := by
        calc
          ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
              (axisReturnHeightProcess (X := X) s ω)) A
              ≤
                ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
                  (axisReturnHeightProcess (X := X) s ω)) Set.univ := by
                    exact measure_mono Set.subset_univ
          _ = 1 := by simp
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one hrow_le
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hnext_meas : MeasurableSet nextEvent := by
    exact hsampled_meas (s + 1) hA
  have hnext_int : Integrable (nextEvent.indicator (fun _ ↦ (1 : ℝ))) μ := by
    exact (integrable_const (1 : ℝ)).indicator hnext_meas
  let Hslice : ℕ → Set Ω := fun n ↦ H ∩ axisReturnSlice (X := X) ⟨s, hs⟩ n
  have hUnion_ae :
      H =ᵐ[μ] ⋃ n : ℕ, Hslice n := by
    simpa [Hslice, H] using
      axisReturnHeightHistoryEvent_ae_eq_iUnion_returnSlices
        (P := P) (X := X) z hs ξ
  have hHslice_meas : ∀ n : ℕ, MeasurableSet (Hslice n) := by
    intro n
    simpa [Hslice, H] using
      axisReturnHeightHistoryEvent_inter_returnSlice_measurable
        (X := X) hs (ξ := ξ) (n := n)
  have hHslice_disj :
      Pairwise (Function.onFun Disjoint Hslice) := by
    intro m n hmn
    refine Set.disjoint_left.2 ?_
    intro ω hωm hωn
    exact (axisReturnSlice_pairwiseDisjoint (X := X) ⟨s, hs⟩ m n hmn) hωm.2 hωn.2
  -- Proof comment: the history atom is almost surely the disjoint union of its exact return
  -- slices, and the slice-level set-integral identity was proved just above.
  calc
    ∫ ω in H, g ω ∂μ = ∫ ω in ⋃ n : ℕ, Hslice n, g ω ∂μ := by
      exact MeasureTheory.setIntegral_congr_set hUnion_ae
    _ = ∑' n : ℕ, ∫ ω in Hslice n, g ω ∂μ := by
          exact MeasureTheory.integral_iUnion hHslice_meas hHslice_disj
            (hg_int.integrableOn.mono_set <| Set.iUnion_subset fun _ ↦ Set.subset_univ _)
    _ = ∑' n : ℕ,
          ∫ ω in Hslice n, nextEvent.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            refine tsum_congr fun n ↦ ?_
            simpa [Hslice, H, g, nextEvent] using
              axisReturnHeightNext_setIntegral_eq_on_historySlice
                (P := P) (X := X) z hs ξ (n := n) hA
    _ = ∫ ω in ⋃ n : ℕ, Hslice n, nextEvent.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
          symm
          exact MeasureTheory.integral_iUnion hHslice_meas hHslice_disj
            (hnext_int.integrableOn.mono_set <| Set.iUnion_subset fun _ ↦ Set.subset_univ _)
    _ = ∫ ω in H, nextEvent.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
          exact MeasureTheory.setIntegral_congr_set hUnion_ae.symm

private theorem axisReturnHeightProcess_oneStepConditional
    (z : ℤ) (s : ℕ) {A : Set ℤ} (hA : MeasurableSet A) :
    (P (0, z))⟦axisReturnHeightProcess (X := X) (s + 1) ⁻¹' A |
      generatedFiltrationSpace (axisReturnHeightProcess (X := X)) s⟧ =ᵐ[(P (0, z) : Measure Ω)]
        fun ω ↦
          ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
            (axisReturnHeightProcess (X := X) s ω)).real A := by
  cases s with
  | zero =>
      let μ : Measure Ω := (P (0, z) : Measure Ω)
      let hwalk : IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := inferInstance
      let event : Set Ω := axisReturnHeightProcess (X := X) 1 ⁻¹' A
      let pathEvent : Set Ω := {ω | processPath X ω ∈ axisFirstFutureReturnHeightEvent A}
      let g : Ω → ℝ := fun ω ↦
        ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
          (axisReturnHeightProcess (X := X) 0 ω)).real A
      have hsmall_le :
          generatedFiltrationSpace (axisReturnHeightProcess (X := X)) 0 ≤
            generatedFiltrationSpace X 0 := by
        exact generatedFiltrationSpace_comp_le X Prod.snd measurable_snd 0
      have hlarge_le : generatedFiltrationSpace X 0 ≤ ‹MeasurableSpace Ω› := by
        exact generatedHistory_le_ambient X hwalk.measurable_process 0
      have hpath_meas : MeasurableSet pathEvent := by
        simpa [pathEvent, processPath] using
          (measurable_axisBlockedTrajectoryMap (P := P) (X := X))
            (measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)
      have hg :
          AEStronglyMeasurable[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) 0] g μ := by
        exact
          (axisReturnHeightTransitionCandidate_measurable (P := P) (X := X) 0 hA)
            .aestronglyMeasurable
      have hpathLaw :
          μ⟦pathEvent | generatedFiltrationSpace X 0⟧ =ᵐ[μ]
            fun ω ↦
              (axisBlockedRealizationPathKernel (P := P) (X := X) (X 0 ω)).real
                (axisFirstFutureReturnHeightEvent A) := by
        simpa [μ, pathEvent] using
          axisBlockedFuturePathIndicator_condexp_eq_pathKernel
            (P := P) (X := X)
            (B := axisFirstFutureReturnHeightEvent A)
            (measurableSet_axisFirstFutureReturnHeightEvent (P := P) (X := X) hA)
            (x := (0, z)) (n := 0)
      have hfinite :
          ∀ᵐ ω ∂μ, (τ_[fun n ω ↦ (X n ω).1, 0]^1) ω < ⊤ := by
        simpa [μ] using
          axisBlockedFirstCoordinate_iteratedReturnFinite_ae
            (P := P) (X := X) z (⟨1, by norm_num⟩)
      have hEventEqPath :
          event =ᵐ[μ] pathEvent := by
        filter_upwards [hfinite] with ω hω
        constructor
        · intro hωevent
          exact
            (processPath_mem_axisFirstFutureReturnHeightEvent_iff
              (P := P) (X := X) (ω := ω) (A := A)).2
              ⟨hω, hωevent⟩
        · intro hωpath
          exact
            (processPath_mem_axisFirstFutureReturnHeightEvent_iff
              (P := P) (X := X) (ω := ω) (A := A)).1 hωpath |>.2
      have hEventIndicatorEq :
          event.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[μ]
            pathEvent.indicator (fun _ ↦ (1 : ℝ)) := by
        filter_upwards [hEventEqPath] with ω hω
        simp [hω]
      have hstart :
          ∀ᵐ ω ∂μ, X 0 ω = (0, z) := by
        have hprob :
            μ {ω | X 0 ω = (0, z)} = 1 := by
          rw [show {ω | X 0 ω = (0, z)} = X 0 ⁻¹' ({(0, z)} : Set AxisState) by
            ext ω
            simp]
          rw [← Measure.map_apply (hwalk.measurable_process 0) (measurableSet_singleton (0, z))]
          rw [hwalk.initial_eq (0, z)]
          simp
        exact
          (MeasureTheory.mem_ae_iff_prob_eq_one
            (show MeasurableSet {ω | X 0 ω = (0, z)} from
              (hwalk.measurable_process 0) (measurableSet_singleton (0, z)))).2
            hprob
      have hrow :
          (fun ω ↦
            (axisBlockedRealizationPathKernel (P := P) (X := X) (X 0 ω)).real
              (axisFirstFutureReturnHeightEvent A)) =ᵐ[μ] g := by
        filter_upwards [hstart] with ω hω
        simp [g, axisReturnHeightProcess, hω,
          axisBlockedRealizationPathKernel_axisFirstFutureReturnHeightEvent
            (P := P) (X := X) z hA]
      have hcondLarge :
          μ⟦event | generatedFiltrationSpace X 0⟧ =ᵐ[μ] g := by
        exact (condExp_congr_ae hEventIndicatorEq).trans (hpathLaw.trans hrow)
      have hg_int : Integrable g μ := by
        exact (integrable_congr hcondLarge).1 integrable_condExp
      -- Proof comment: at sampled time `0`, the process starts on the axis, so the one-step law
      -- comes directly from the time-`0` path-kernel formula and the new axis-start row theorem.
      calc
        μ⟦event | generatedFiltrationSpace (axisReturnHeightProcess (X := X)) 0⟧
            =ᵐ[μ]
              μ[μ[event.indicator (fun _ ↦ (1 : ℝ)) | generatedFiltrationSpace X 0] |
                generatedFiltrationSpace (axisReturnHeightProcess (X := X)) 0] := by
                  symm
                  exact condExp_condExp_of_le hsmall_le hlarge_le
        _ =ᵐ[μ] μ[g | generatedFiltrationSpace (axisReturnHeightProcess (X := X)) 0] := by
              exact condExp_congr_ae hcondLarge
        _ =ᵐ[μ] g := by
              exact condExp_of_aestronglyMeasurable' (hsmall_le.trans hlarge_le) hg hg_int
  | succ n =>
      let μ : Measure Ω := (P (0, z) : Measure Ω)
      let event : Set Ω := axisReturnHeightProcess (X := X) (n + 2) ⁻¹' A
      let g : Ω → ℝ := fun ω ↦
        ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
          (axisReturnHeightProcess (X := X) (n + 1) ω)).real A
      have hsampled_meas :
          ∀ m : ℕ, Measurable (axisReturnHeightProcess (X := X) m) := by
        intro m
        exact measurable_of_countable (f := axisReturnHeightProcess (X := X) m)
      have hsmall_le :
          generatedFiltrationSpace (axisReturnHeightProcess (X := X)) (n + 1) ≤
            ‹MeasurableSpace Ω› := by
        exact generatedHistory_le_ambient (axisReturnHeightProcess (X := X)) hsampled_meas (n + 1)
      have hevent_meas : MeasurableSet event := by
        simpa [event] using
          (measurable_of_countable (f := axisReturnHeightProcess (X := X) (n + 2))) hA
      have hevent_int : Integrable (event.indicator (fun _ ↦ (1 : ℝ))) μ := by
        exact (integrable_const (1 : ℝ)).indicator hevent_meas
      have hg_meas :
          AEStronglyMeasurable[generatedFiltrationSpace (axisReturnHeightProcess (X := X)) (n + 1)]
            g μ := by
        exact
          (axisReturnHeightTransitionCandidate_measurable (X := X) (n + 1) hA)
            .aestronglyMeasurable
      have hg_int : Integrable g μ := by
        refine Integrable.of_bound hg_meas 1 ?_
        filter_upwards with ω
        have hnonneg : 0 ≤ g ω := ENNReal.toReal_nonneg
        have hle : g ω ≤ 1 := by
          have hrow_le :
              ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
                (axisReturnHeightProcess (X := X) (n + 1) ω)) A ≤ 1 := by
            calc
              ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
                  (axisReturnHeightProcess (X := X) (n + 1) ω)) A
                  ≤
                    ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
                      (axisReturnHeightProcess (X := X) (n + 1) ω)) Set.univ := by
                        exact measure_mono Set.subset_univ
              _ = 1 := by simp
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one hrow_le
        simpa [Real.norm_of_nonneg hnonneg] using hle
      -- Route correction: avoid the stalled stopping-time transport. Instead, prove the
      -- conditional-expectation identity by checking the defining set integrals on sampled-history
      -- atoms and then summing their exact return slices.
      refine
        (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hsmall_le hevent_int
          (fun D hD hDfinite ↦ ?_)
          (fun D hD hDfinite ↦ ?_) hg_meas).symm
      · refine IntegrableOn.of_bound hDfinite hg_meas.restrict 1 ?_
        filter_upwards with ω
        have hnonneg : 0 ≤ g ω := ENNReal.toReal_nonneg
        have hle : g ω ≤ 1 := by
          have hrow_le :
              ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
                (axisReturnHeightProcess (X := X) (n + 1) ω)) A ≤ 1 := by
            calc
              ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
                  (axisReturnHeightProcess (X := X) (n + 1) ω)) A
                  ≤
                    ((discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
                      (axisReturnHeightProcess (X := X) (n + 1) ω)) Set.univ := by
                        exact measure_mono Set.subset_univ
              _ = 1 := by simp
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one hrow_le
        simpa [Real.norm_of_nonneg hnonneg] using hle
      · rcases
          axisReturnHeight_measurableSet_eq_iUnion_historyEvent
            (X := X) (s := n + 1) hD with ⟨T, hT⟩
        let H : {ξ : Fin (n + 2) → ℤ // ξ ∈ T} → Set Ω := fun ξ ↦
          axisReturnHeightHistoryEvent (X := X) (n + 1) ξ.1
        have hH_meas : ∀ ξ, MeasurableSet (H ξ) := by
          intro ξ
          exact hsmall_le _ <|
            axisReturnHeightHistoryEvent_measurable_generated (X := X) (s := n + 1) ξ.1
        have hH_disj : Pairwise (Function.onFun Disjoint H) := by
          intro ξ η hξη
          exact
            axisReturnHeightHistoryEvent_pairwiseDisjoint (X := X) (s := n + 1)
              (by
                intro hEq
                apply hξη
                exact Subtype.ext hEq)
        have hD_eq : D = ⋃ ξ, H ξ := by
          calc
            D = ⋃ ξ ∈ T, axisReturnHeightHistoryEvent (X := X) (n + 1) ξ := hT
            _ = ⋃ ξ : {ξ : Fin (n + 2) → ℤ // ξ ∈ T}, H ξ := by
                  ext ω
                  constructor
                  · intro hω
                    rcases Set.mem_iUnion.1 hω with ⟨ξ, hω⟩
                    rcases Set.mem_iUnion.1 hω with ⟨hξ, hωξ⟩
                    exact Set.mem_iUnion.2 ⟨⟨ξ, hξ⟩, hωξ⟩
                  · intro hω
                    rcases Set.mem_iUnion.1 hω with ⟨ξ, hωξ⟩
                    exact Set.mem_iUnion.2 ⟨ξ.1, Set.mem_iUnion.2 ⟨ξ.2, hωξ⟩⟩
        calc
          ∫ ω in D, g ω ∂μ = ∫ ω in ⋃ ξ, H ξ, g ω ∂μ := by
            rw [hD_eq]
          _ = ∑' ξ, ∫ ω in H ξ, g ω ∂μ := by
                exact MeasureTheory.integral_iUnion hH_meas hH_disj
                  (hg_int.integrableOn.mono_set <| Set.iUnion_subset fun _ ↦ Set.subset_univ _)
          _ = ∑' ξ, ∫ ω in H ξ, event.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                refine tsum_congr fun ξ ↦ ?_
                simpa [H, event, g] using
                  axisReturnHeightNext_setIntegral_eq_on_historyEvent
                    (P := P) (X := X) z (hs := Nat.succ_pos n) ξ.1 hA
          _ = ∫ ω in ⋃ ξ, H ξ, event.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                symm
                exact MeasureTheory.integral_iUnion hH_meas hH_disj
                  (hevent_int.integrableOn.mono_set <| Set.iUnion_subset fun _ ↦ Set.subset_univ _)
          _ = ∫ ω in D, event.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                rw [hD_eq]

/-- Helper for Exercise 18.2.4: the embedded axis-return heights should realize the lazy
quarter-half-quarter walk on `ℤ`. -/
private theorem axisReturnHeightProcess_isMarkovProcessRealization :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
      (fun z : ℤ ↦ P (0, z))
      (axisReturnHeightProcess (X := X)) := by
  let hwalk : IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := by
    simpa [axisBlockedKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix ^ n)
          P X)
  letI : IsMarkovKernel (discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix) :=
    discreteMatrixKernel_isMarkovKernel axisBlockedFirstCoordinateTransitionMatrix
      axisBlockedFirstCoordinateTransitionMatrix_isStochastic
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix)
    (P := fun z : ℤ ↦ P (0, z))
    (X := axisReturnHeightProcess (X := X))
    (hmeas := ?_)
    (hstart := ?_)
    (hstep := ?_)
  · intro n
    -- Proof comment: the sampled-height chain is `ℤ`-valued, so discreteness makes each time
    -- coordinate measurable without extra transport work.
    exact measurable_of_countable (f := axisReturnHeightProcess (X := X) n)
  · intro z
    let μ : Measure Ω := (P (0, z) : Measure Ω)
    have hmap :
        (μ.map (X 0)).map Prod.snd = μ.map (fun ω ↦ (X 0 ω).2) := by
      simpa [Function.comp] using
        (Measure.map_map (μ := μ) (f := X 0) (g := Prod.snd)
          (hf := hwalk.measurable_process 0) (hg := measurable_snd))
    calc
      μ.map (axisReturnHeightProcess (X := X) 0) = μ.map (fun ω ↦ (X 0 ω).2) := by
        rfl
      _ = (μ.map (X 0)).map Prod.snd := hmap.symm
      _ = (Measure.dirac (0, z)).map Prod.snd := by
            rw [hwalk.initial_eq (0, z)]
      _ = Measure.dirac z := by
            simp
  · intro z A hA s
    -- Proof comment: the owner theorem now depends only on the sampled one-step conditional law,
    -- isolated above as the exact return-slice blocker.
    simpa using axisReturnHeightProcess_oneStepConditional (P := P) (X := X) z s hA

/-- Helper for Exercise 18.2.4: recurrence of the embedded axis-return heights should transfer
back to recurrence of the original origin `(0,0)`. -/
private theorem axisBlockedOriginRecurrent_of_axisReturnHeightRecurrent
    (hheightRec :
      IsRecurrentState (fun z : ℤ ↦ P (0, z)) axisReturnHeightProcess 0) :
    IsRecurrentState P X (0, 0) := by
  -- Proof comment: once the sampled height chain is recurrent at `0`, every recurrent sampled hit
  -- corresponds to an actual visit of the original walk to `(0,0)` by
  -- `axisReturnState_eq_axisReturnHeight_ae`.
  let μ : Measure Ω := (P (0, 0) : Measure Ω)
  let sampledHit : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ axisReturnHeightProcess (X := X) n ω = 0}
  let originHit : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = (0, 0)}
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
        (fun z : ℤ ↦ P (0, z))
        axisReturnHeightProcess :=
    axisReturnHeightProcess_isMarkovProcessRealization (P := P) (X := X)
  let hwalk :
      IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := by
    simpa [axisBlockedKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix ^ n)
          P X)
  let sampledLevelSet : ℕ+ → Set Ω := fun k ↦ {ω | axisReturnHeight (X := X) k ω = 0}
  have hsampled_union :
      sampledHit = ⋃ k : ℕ+, sampledLevelSet k := by
    ext ω
    constructor
    · rintro ⟨n, hn, hzero⟩
      refine Set.mem_iUnion.2 ⟨⟨n, hn⟩, ?_⟩
      simpa [sampledLevelSet, axisReturnHeightProcess_pNat (X := X) ⟨n, hn⟩] using hzero
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
      refine ⟨k, k.2, ?_⟩
      simpa [sampledLevelSet, axisReturnHeightProcess_pNat (X := X) k] using hk
  have hsampled_meas : MeasurableSet sampledHit := by
    rw [hsampled_union]
    refine MeasurableSet.iUnion fun k ↦ ?_
    have hslice_meas :
        MeasurableSet (axisReturnHeightProcess (X := X) k ⁻¹' ({0} : Set ℤ)) :=
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
          (fun z : ℤ ↦ P (0, z))
          axisReturnHeightProcess).measurable_process k (measurableSet_singleton 0)
    simpa [sampledLevelSet, axisReturnHeightProcess_pNat (X := X) k] using hslice_meas
  have horigin_meas : MeasurableSet originHit := by
    have hslices :
        originHit = ⋃ n : ℕ+, {ω | X n ω = (0, 0)} := by
      ext ω
      constructor
      · rintro ⟨n, hn, hstate⟩
        exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, hstate⟩
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
        exact ⟨n, n.2, hn⟩
    rw [hslices]
    exact MeasurableSet.iUnion fun n ↦ hwalk.measurable_process n (measurableSet_singleton (0, 0))
  have hsampled_ae : ∀ᵐ ω ∂μ, ω ∈ sampledHit := by
    refine
      (MeasureTheory.ae_iff_prob_eq_one
        (μ := μ) (p := fun ω ↦ ω ∈ sampledHit) hsampled_meas).2 ?_
    simpa [μ, sampledHit] using (by simpa [IsRecurrentState, everHitsProbability_def] using hheightRec)
  have hbad_slice :
      ∀ k : ℕ+, μ (sampledLevelSet k \ originHit) = 0 := by
    intro k
    have hgood :
        ∀ᵐ ω ∂μ,
          ∃ n : ℕ,
            (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = n ∧
              X n ω = (0, axisReturnHeight (X := X) k ω) := by
      simpa [μ] using axisReturnState_eq_axisReturnHeight_ae (P := P) (X := X) 0 k
    have hgood_null :
        μ
          ({ω | ∃ n : ℕ,
              (τ_[fun m ω ↦ (X m ω).1, 0]^k) ω = n ∧
                X n ω = (0, axisReturnHeight (X := X) k ω)}ᶜ) = 0 := by
      exact compl_mem_ae_iff.mp hgood
    refine measure_mono_null ?_ hgood_null
    intro ω hω
    rcases hω with ⟨hzero, hnotOrigin⟩
    intro hgoodω
    rcases hgoodω with ⟨n, hτ, hstate⟩
    have hn_pos :
        0 < n :=
      axisBlockedFirstCoordinate_iteratedReturn_pos (X := X) hτ
    have horiginState : X n ω = (0, 0) := by
      simpa [hzero] using hstate
    exact hnotOrigin ⟨n, hn_pos, horiginState⟩
  have hbad_union :
      μ (sampledHit \ originHit) = 0 := by
    rw [hsampled_union]
    refine measure_mono_null ?_ ?_
    · intro ω hω
      rcases hω with ⟨hωHit, hωNot⟩
      rcases Set.mem_iUnion.1 hωHit with ⟨k, hk⟩
      exact Set.mem_iUnion.2 ⟨k, ⟨hk, hωNot⟩⟩
    · exact measure_iUnion_null hbad_slice
  have hgood_union :
      ∀ᵐ ω ∂μ, ω ∉ sampledHit \ originHit := by
    exact compl_mem_ae_iff.2 hbad_union
  have horigin_ae : ∀ᵐ ω ∂μ, ω ∈ originHit := by
    filter_upwards [hsampled_ae, hgood_union] with ω hsampled hgood
    by_contra hnotOrigin
    exact hgood ⟨hsampled, hnotOrigin⟩
  exact
    (MeasureTheory.ae_iff_prob_eq_one
      (μ := μ) (p := fun ω ↦ ω ∈ originHit) horigin_meas).1 <| by
        simpa [μ, IsRecurrentState, everHitsProbability_def, originHit] using horigin_ae

private theorem axisBlockedAxisReturnHeight_originRecurrent :
    IsRecurrentState P X (0, 0) := by
  -- Proof comment: `axisBlockedFirstCoordinate_iteratedReturnFinite` now gives the a.s. finite
  -- return-time side conditions for every sampled axis return, and the sampled-height observable
  -- is now isolated behind `axisReturnHeight`. The remaining work is exactly to package that
  -- sampled second-coordinate process as a recurrent lazy walk on `ℤ`.
  -- Route correction: the brittle future-path route has been abandoned. The new stable frontier is
  -- the deterministic slice-zero lemma
  -- `axisReturnHeight_badSlice_zero_fromHorizontalNeighbor`; what remains is to use it in the
  -- four-way first-step decomposition for the sampled first-return row and then assemble the
  -- sampled axis-return height process as the lazy walk on `ℤ`.
  let ν : ProbabilityMeasure ℤ := axisBlockedFirstCoordinateStepLaw
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
        (fun z : ℤ ↦ P (0, z))
        axisReturnHeightProcess :=
    axisReturnHeightProcess_isMarkovProcessRealization (P := P) (X := X)
  have hconv :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (fun z : ℤ ↦ P (0, z))
        axisReturnHeightProcess := by
    simpa [axisBlockedFirstCoordinateTransitionMatrix_eq_convolutionStepMatrix,
      convolutionStepMatrixKernel_eq ν] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel axisBlockedFirstCoordinateTransitionMatrix ^ n)
          (fun z : ℤ ↦ P (0, z))
          axisReturnHeightProcess)
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n)
        (fun z : ℤ ↦ P (0, z))
        axisReturnHeightProcess := hconv
  have hrecHeight :
      IsRecurrentMarkovChain (fun z : ℤ ↦ P (0, z)) axisReturnHeightProcess := by
    exact
      (integerRandomWalk_recurrent_iff_zero_stepLawMean
        (ν := ν) (P := fun z : ℤ ↦ P (0, z)) (X := axisReturnHeightProcess)
        axisBlockedFirstCoordinateStepPMF_integrable_mean_zero.1).2
        axisBlockedFirstCoordinateStepPMF_integrable_mean_zero.2
  exact
    axisBlockedOriginRecurrent_of_axisReturnHeightRecurrent
      (P := P) (X := X) (hrecHeight 0)

/-- Helper for Exercise 18.2.4: the origin `(0, 0)` is recurrent for every realization of the
axis-blocked walk. -/
private theorem axisBlockedWalk_originRecurrent :
    IsRecurrentState P X (0, 0) := by
  -- Proof comment: the projection-to-`ℤ` recurrence bridge is now isolated; the remaining work is
  -- entirely in the sampled axis-return height chain.
  exact axisBlockedAxisReturnHeight_originRecurrent (P := P) (X := X)

/-- Helper for Exercise 18.2.4: once the origin is known to be recurrent, irreducibility
propagates that recurrence to every state of the realization. -/
private theorem axisBlockedWalk_recurrentMarkovChain_of_originRecurrent
    (horigin : IsRecurrentState P X (0, 0)) :
    IsRecurrentMarkovChain P X := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ axisBlockedKernel ^ n) P X := by
    simpa [axisBlockedKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix ^ n)
          P X)
  let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hirr : IsIrreducibleMarkovChain P X :=
    axisBlockedWalk_isIrreducibleMarkovChain (P := P) (X := X)
  intro z
  by_cases hz : z = (0, 0)
  · subst hz
    simpa using horigin
  · have hgreen_pos : 0 < (G[P, X; 1]) (0, 0) z := by
      exact
        (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
          (κ := fun n : ℕ ↦ axisBlockedKernel ^ n) P X).1 hirr (by simpa [eq_comm] using hz)
    have hhit_pos : 0 < (F[P, X]) (0, 0) z := by
      exact
        (greenFunctionFrom_one_pos_iff_everHitsProbability_pos
          P X hproc (0, 0) z).1 hgreen_pos
    -- Proof comment: irreducibility provides positive communication from `(0,0)` to `z`, and
    -- Theorem 17.35 transports recurrence along that positive-probability connection.
    exact
      isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
        (P := P) (X := X) (κ := fun n : ℕ ↦ axisBlockedKernel ^ n)
        horigin hhit_pos

/-- Helper for Exercise 18.2.4: symmetry of the transition matrix makes counting measure
invariant once the one-step kernel is known to be Markov. -/
private theorem axisBlockedWalk_count_invariant :
    Kernel.Invariant axisBlockedKernel (Measure.count : Measure AxisState) := by
  -- Proof comment: compare singleton masses of `count ⋆ₘ p` and `count`; on a discrete state
  -- space, equality on singletons determines the whole measure.
  rw [Kernel.Invariant]
  refine Measure.ext_of_singleton fun x ↦ ?_
  have hrowSum :
      ∑' y : AxisState, vertical_axis_blocked_walk_transition_matrix x y = 1 := by
    rcases x with ⟨x1, x2⟩
    calc
      ∑' y : AxisState, vertical_axis_blocked_walk_transition_matrix (x1, x2) y
          = ∑' y1 : ℤ, ∑' y2 : ℤ,
              vertical_axis_blocked_walk_transition_matrix (x1, x2) (y1, y2) := by
                simpa using
                  (ENNReal.tsum_prod'
                    (f := fun y : AxisState ↦
                      vertical_axis_blocked_walk_transition_matrix (x1, x2) y))
      _ = ∑' y1 : ℤ, axisBlockedFirstCoordinateTransitionMatrix x1 y1 := by
            refine tsum_congr fun y1 ↦ ?_
            exact vertical_axis_blocked_walk_transition_matrix_tsum_second x1 x2 y1
      _ = 1 := axisBlockedFirstCoordinateTransitionMatrix_tsum x1
  calc
    ((Measure.count : Measure AxisState).bind axisBlockedKernel) ({x} : Set AxisState)
        = ∫⁻ y, axisBlockedKernel y ({x} : Set AxisState) ∂(Measure.count : Measure AxisState) := by
            rw [Measure.bind_apply (measurableSet_singleton x) (Kernel.aemeasurable _)]
    _ = ∑' y : AxisState, axisBlockedKernel y ({x} : Set AxisState) := by
          simp [MeasureTheory.lintegral_countable']
    _ = ∑' y : AxisState, vertical_axis_blocked_walk_transition_matrix y x := by
          refine tsum_congr fun y ↦ ?_
          rw [axisBlockedKernel_singletonEqEntry]
    _ = ∑' y : AxisState, vertical_axis_blocked_walk_transition_matrix x y := by
          refine tsum_congr fun y ↦ ?_
          rw [vertical_axis_blocked_walk_transition_matrix_symm]
    _ = 1 := hrowSum
    _ = (Measure.count : Measure AxisState) ({x} : Set AxisState) := by
          simp

/-- Helper for Exercise 18.2.4: counting measure on `ℤ²` is nonzero. -/
private theorem axisBlockedWalk_count_ne_zero :
    (Measure.count : Measure AxisState) ≠ 0 := by
  intro hzero
  have hsingleton :=
    congrArg (fun μ : Measure AxisState ↦ μ ({(0, 0)} : Set AxisState)) hzero
  simp at hsingleton

/-- Helper for Exercise 18.2.4: shifting the second coordinate by a fixed integer. -/
private def verticalShiftState (h : ℤ) : AxisState → AxisState
  | (x1, x2) => (x1, x2 + h)

/-- Helper for Exercise 18.2.4: shift both walkers in a pair by the same vertical offset. -/
private def freePairCommonVerticalShift (h : ℤ) :
    AxisState × AxisState → AxisState × AxisState
  | (x, y) => (verticalShiftState h x, verticalShiftState h y)

/-- Helper for Exercise 18.2.4: the blocked walk transition matrix is invariant under common
vertical shifts of the source and target states. -/
private theorem vertical_axis_blocked_walk_transition_matrix_shift_second
    (h : ℤ) (x y : AxisState) :
    vertical_axis_blocked_walk_transition_matrix (verticalShiftState h x) (verticalShiftState h y) =
      vertical_axis_blocked_walk_transition_matrix x y := by
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  by_cases hx : x1 = 0
  · simp [vertical_axis_blocked_walk_transition_matrix, verticalShiftState, hx,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor]
    omega
  · simp [vertical_axis_blocked_walk_transition_matrix, verticalShiftState, hx,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor]
    omega

/-- Helper for Exercise 18.2.4: the inverse image of a singleton under a vertical shift is the
corresponding singleton shifted back by the opposite amount. -/
private theorem preimage_singleton_verticalShiftState
    (h : ℤ) (y : AxisState) :
    verticalShiftState h ⁻¹' ({y} : Set AxisState) =
      {verticalShiftState (-h) y} := by
  ext x
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp [verticalShiftState]
  omega

/-- Helper for Exercise 18.2.4: pushing an invariant distribution forward by a vertical shift
produces another invariant distribution. -/
private theorem axisBlockedWalk_shift_invariantDistribution
    (π : ProbabilityMeasure AxisState)
    (hπ : Kernel.Invariant axisBlockedKernel (π : Measure AxisState))
    (h : ℤ) :
    Kernel.Invariant axisBlockedKernel
      (Measure.map (verticalShiftState h) (π : Measure AxisState)) := by
  let f : AxisState → AxisState := verticalShiftState h
  have hf : AEMeasurable f (π : Measure AxisState) :=
    (measurable_of_countable (f := f)).aemeasurable
  rw [Kernel.Invariant] at hπ ⊢
  refine Measure.ext_of_singleton fun y ↦ ?_
  calc
    ((Measure.map f (π : Measure AxisState)).bind axisBlockedKernel) ({y} : Set AxisState) =
        ∫⁻ c, axisBlockedKernel c ({y} : Set AxisState) ∂Measure.map f (π : Measure AxisState) := by
          rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _)]
    _ = ∫⁻ x, axisBlockedKernel (f x) ({y} : Set AxisState) ∂(π : Measure AxisState) := by
          -- Proof comment: pull the singleton-mass function back along the vertical shift.
          rw [MeasureTheory.lintegral_map'
            (Kernel.measurable_coe axisBlockedKernel (measurableSet_singleton y)).aemeasurable hf]
    _ = ∫⁻ x, axisBlockedKernel x ({verticalShiftState (-h) y} : Set AxisState)
          ∂(π : Measure AxisState) := by
          -- Proof comment: shifting both source and target states preserves the blocked walk row.
          refine lintegral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
          rw [axisBlockedKernel_singletonEqEntry, axisBlockedKernel_singletonEqEntry]
          simpa [f] using
            vertical_axis_blocked_walk_transition_matrix_shift_second h x
              (verticalShiftState (-h) y)
    _ = ((π : Measure AxisState).bind axisBlockedKernel)
          ({verticalShiftState (-h) y} : Set AxisState) := by
          rw [Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)]
    _ = (π : Measure AxisState) ({verticalShiftState (-h) y} : Set AxisState) := by
          rw [hπ]
    _ = (Measure.map f (π : Measure AxisState)) ({y} : Set AxisState) := by
          rw [Measure.map_apply (measurable_of_countable (f := f)) (measurableSet_singleton y)]
          rw [preimage_singleton_verticalShiftState]

/-- Helper for Exercise 18.2.4: a probability measure on `ℤ²` has positive mass on some
singleton. -/
private theorem axisBlockedWalk_exists_positive_singleton_mass
    (π : ProbabilityMeasure AxisState) :
    ∃ x : AxisState, 0 < (π : Measure AxisState) ({x} : Set AxisState) := by
  by_contra hnone
  have hzero :
      ∀ x : AxisState, (π : Measure AxisState) ({x} : Set AxisState) = 0 := by
    intro x
    by_contra hx
    exact hnone ⟨x, lt_of_le_of_ne bot_le hx.symm⟩
  have huniv :
      (Set.univ : Set AxisState) = ⋃ x : AxisState, ({x} : Set AxisState) := by
    ext x
    simp
  have hnull :
      (π : Measure AxisState) (⋃ x : AxisState, ({x} : Set AxisState)) = 0 := by
    -- Proof comment: if every singleton had mass `0`, countable additivity would force the whole
    -- probability mass on `univ` to vanish.
    refine measure_iUnion_null fun x ↦ ?_
    simpa [hzero x]
  have hcontr :
      (π : Measure AxisState) Set.univ = 0 := by
    simpa [huniv] using hnull
  norm_num at hcontr

/-- Helper for Exercise 18.2.4: an invariant probability measure cannot be a positive scalar
multiple of counting measure, because counting measure charges infinitely many disjoint horizontal
axis singletons equally. -/
private theorem axisBlockedWalk_not_probabilityMeasure_smul_count
    (π : ProbabilityMeasure AxisState) {c : ℝ≥0∞} (hc : 0 < c)
    (hπeq : (π : Measure AxisState) = c • (Measure.count : Measure AxisState)) : False := by
  let axisLine : Set AxisState := Set.range fun n : ℤ ↦ ((0, n) : AxisState)
  have hcount_axis :
      (Measure.count : Measure AxisState) axisLine = ∞ := by
    have himage :
        axisLine = (fun n : ℤ ↦ ((0, n) : AxisState)) '' (Set.univ : Set ℤ) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨n, rfl⟩
        exact ⟨n, Set.mem_univ _, rfl⟩
      · rintro ⟨n, -, rfl⟩
        exact ⟨n, rfl⟩
    calc
      (Measure.count : Measure AxisState) axisLine
          = (Measure.count : Measure AxisState)
              ((fun n : ℤ ↦ ((0, n) : AxisState)) '' (Set.univ : Set ℤ)) := by
                rw [himage]
      _ = (Measure.count : Measure ℤ) (Set.univ : Set ℤ) := by
            simpa using
              (Measure.count_injective_image
                (f := fun n : ℤ ↦ ((0, n) : AxisState))
                (s := (Set.univ : Set ℤ))
                (by
                  intro m n hmn
                  exact congrArg Prod.snd hmn))
      _ = ∞ := by
            simpa [Measure.count_univ, ENat.card_eq_top_of_infinite]
  have hπ_axis :
      (π : Measure AxisState) axisLine = ∞ := by
    calc
      (π : Measure AxisState) axisLine
          = (c • (Measure.count : Measure AxisState)) axisLine := by
              rw [hπeq]
      _ = c * (Measure.count : Measure AxisState) axisLine := by
            simpa [smul_eq_mul] using
              (Measure.smul_apply c (Measure.count : Measure AxisState) axisLine)
      _ = c * ∞ := by rw [hcount_axis]
      _ = ∞ := by
            simpa [hc.ne'] using ENNReal.mul_top hc.ne'
  have hfinite_axis :
      (π : Measure AxisState) axisLine < ∞ := by
    calc
      (π : Measure AxisState) axisLine ≤ (π : Measure AxisState) Set.univ := by
        exact measure_mono (by intro z hz; simp)
      _ = 1 := by simp
      _ < ∞ := by simp
  have hnotfinite : ¬ (π : Measure AxisState) axisLine < ∞ := by
    simpa [hπ_axis]
  exact hnotfinite hfinite_axis

/-- Helper for Exercise 18.2.4: once recurrence is known, irreducibility and the invariant
counting measure should rule out invariant probability distributions. -/
private theorem axisBlockedWalk_invariantDistributions_eq_empty_of_recurrent
    (_hrec : IsRecurrentMarkovChain P X) :
    invariantDistributions axisBlockedKernel = ∅ := by
  letI :
      Kernel.IsIrreducible (Measure.count : Measure AxisState) axisBlockedKernel :=
    verticalAxisBlockedWalk_kernelIsIrreducible
  have hsub :
      Set.Subsingleton (invariantDistributions axisBlockedKernel) :=
    invariantDistributions_subsingleton_of_irreducible (p := axisBlockedKernel)
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  intro π hπ
  let πshift : ProbabilityMeasure AxisState :=
    ProbabilityMeasure.map π
      (measurable_of_countable (f := verticalShiftState 1)).aemeasurable
  have hπinv : Kernel.Invariant axisBlockedKernel (π : Measure AxisState) :=
    (mem_invariantDistributions_iff axisBlockedKernel π).1 hπ
  have hπshift_mem : πshift ∈ invariantDistributions axisBlockedKernel := by
    exact
      (mem_invariantDistributions_iff axisBlockedKernel πshift).2
        (axisBlockedWalk_shift_invariantDistribution π hπinv 1)
  have hEq : πshift = π := hsub hπshift_mem hπ
  have hEqMeasure : (πshift : Measure AxisState) = (π : Measure AxisState) := by
    simpa using congrArg (fun μ : ProbabilityMeasure AxisState ↦ (μ : Measure AxisState)) hEq
  obtain ⟨x, hx⟩ := axisBlockedWalk_exists_positive_singleton_mass π
  rcases x with ⟨x1, x2⟩
  let point : ℕ → AxisState := fun n ↦ (x1, x2 + n)
  have hshiftMass :
      ∀ n : ℕ,
        (π : Measure AxisState) ({point n} : Set AxisState) =
          (π : Measure AxisState) ({point 0} : Set AxisState) := by
    intro n
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        calc
          (π : Measure AxisState) ({point (n + 1)} : Set AxisState) =
              (πshift : Measure AxisState) ({point (n + 1)} : Set AxisState) := by
                simpa [hEqMeasure]
          _ = (π : Measure AxisState) ({point n} : Set AxisState) := by
                rw [ProbabilityMeasure.toMeasure_map,
                  Measure.map_apply
                    (measurable_of_countable (f := verticalShiftState 1))
                    (measurableSet_singleton (point (n + 1)))]
                simpa [point, verticalShiftState] using
                  preimage_singleton_verticalShiftState (1 : ℤ) (point (n + 1))
          _ = (π : Measure AxisState) ({point 0} : Set AxisState) := ih
  let c : ℝ≥0∞ := (π : Measure AxisState) ({point 0} : Set AxisState)
  have hc_pos : 0 < c := by
    simpa [c, point] using hx
  have hseg_le : ∀ N : ℕ, ((N + 1 : ℝ≥0∞) * c) ≤ 1 := by
    intro N
    have hdisj :
        PairwiseDisjoint (↑(Finset.range (N + 1)))
          (fun n ↦ ({point n} : Set AxisState)) := by
      intro i hi j hj hij
      refine Set.disjoint_left.2 ?_
      intro a hai haj
      have hpts : point i = point j := by simpa using hai.trans haj.symm
      have : i = j := by
        dsimp [point] at hpts
        omega
      exact hij this
    calc
      ((N + 1 : ℝ≥0∞) * c) =
          ∑ n in Finset.range (N + 1), (π : Measure AxisState) ({point n} : Set AxisState) := by
            simp [c, hshiftMass]
      _ = (π : Measure AxisState) (⋃ n ∈ Finset.range (N + 1), ({point n} : Set AxisState)) := by
            symm
            simpa using
              (measure_biUnion_finset hdisj
                (fun n _ ↦ measurableSet_singleton (point n)))
      _ ≤ (π : Measure AxisState) Set.univ := by
            exact measure_mono (by intro a ha; simp)
      _ = 1 := by simp
  have hc_real_pos : 0 < c.toReal := by
    exact ENNReal.toReal_pos hc_pos.ne' (measure_ne_top _ _)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / c.toReal < N + 1 := by
    simpa using exists_nat_gt (1 / c.toReal)
  have hseg_real_le : (N + 1 : ℝ) * c.toReal ≤ 1 := by
    have hmul_ne_top : ((N + 1 : ℝ≥0∞) * c) ≠ ∞ := by
      exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    have := ENNReal.toReal_mono hmul_ne_top (hseg_le N)
    simpa [c, ENNReal.toReal_mul, measure_ne_top _ _] using this
  have hc_real_ne : c.toReal ≠ 0 := by
    exact hc_real_pos.ne'
  have : 1 < (N + 1 : ℝ) * c.toReal := by
    have hN' : (1 / c.toReal) * c.toReal < (N + 1 : ℝ) * c.toReal := by
      exact mul_lt_mul_of_pos_right hN hc_real_pos
    simpa [hc_real_ne] using hN'
  linarith
/-
  letI :
      Kernel.IsIrreducible (Measure.count : Measure AxisState) axisBlockedKernel :=
    verticalAxisBlockedWalk_kernelIsIrreducible
  have hsub :
      Set.Subsingleton (invariantDistributions axisBlockedKernel) :=
    invariantDistributions_subsingleton_of_irreducible (p := axisBlockedKernel)
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  intro π hπ
  let πshift : ProbabilityMeasure AxisState :=
    ProbabilityMeasure.map π
      (measurable_of_countable (f := verticalShiftState 1)).aemeasurable
  have hπinv : Kernel.Invariant axisBlockedKernel (π : Measure AxisState) :=
    (mem_invariantDistributions_iff axisBlockedKernel π).1 hπ
  have hπshift_mem : πshift ∈ invariantDistributions axisBlockedKernel := by
    exact
      (mem_invariantDistributions_iff axisBlockedKernel πshift).2
        (axisBlockedWalk_shift_invariantDistribution π hπinv 1)
  have hEq : πshift = π := hsub hπshift_mem hπ
  have hEqMeasure : (πshift : Measure AxisState) = (π : Measure AxisState) := by
    simpa using congrArg (fun μ : ProbabilityMeasure AxisState ↦ (μ : Measure AxisState)) hEq
  obtain ⟨x, hx⟩ := axisBlockedWalk_exists_positive_singleton_mass π
  rcases x with ⟨x1, x2⟩
  let point : ℕ → AxisState := fun n ↦ (x1, x2 + n)
  have hshiftMass :
      ∀ n : ℕ,
        (π : Measure AxisState) ({point n} : Set AxisState) =
          (π : Measure AxisState) ({point 0} : Set AxisState) := by
    intro n
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        calc
          (π : Measure AxisState) ({point (n + 1)} : Set AxisState)
              = (πshift : Measure AxisState) ({point (n + 1)} : Set AxisState) := by
                  simpa [hEqMeasure]
          _ = (π : Measure AxisState) ({point n} : Set AxisState) := by
                rw [ProbabilityMeasure.toMeasure_map,
                  Measure.map_apply
                    (measurable_of_countable (f := verticalShiftState 1))
                    (measurableSet_singleton (point (n + 1)))]
                simpa [point, verticalShiftState] using
                  preimage_singleton_verticalShiftState (1 : ℤ) (point (n + 1))
          _ = (π : Measure AxisState) ({point 0} : Set AxisState) := ih
  let c : ℝ≥0∞ := (π : Measure AxisState) ({point 0} : Set AxisState)
  have hc_pos : 0 < c := by
    simpa [c, point] using hx
  have hseg_le : ∀ N : ℕ, ((N + 1 : ℝ≥0∞) * c) ≤ 1 := by
    intro N
    have hdisj :
        PairwiseDisjoint (↑(Finset.range (N + 1)))
          (fun n ↦ ({point n} : Set AxisState)) := by
      intro i hi j hj hij
      refine Set.disjoint_left.2 ?_
      intro a hai haj
      have hpts : point i = point j := by simpa using hai.trans haj.symm
      have : i = j := by
        dsimp [point] at hpts
        omega
      exact hij this
    calc
      ((N + 1 : ℝ≥0∞) * c)
          = ∑ n in Finset.range (N + 1), (π : Measure AxisState) ({point n} : Set AxisState) := by
              simp [c, hshiftMass]
      _ = (π : Measure AxisState) (⋃ n ∈ Finset.range (N + 1), ({point n} : Set AxisState)) := by
            symm
            simpa using
              (measure_biUnion_finset hdisj
                (fun n _ ↦ measurableSet_singleton (point n)))
      _ ≤ (π : Measure AxisState) Set.univ := by
            exact measure_mono (by intro a ha; simp)
      _ = 1 := by simp
  have hc_real_pos : 0 < c.toReal := by
    exact ENNReal.toReal_pos hc_pos.ne' (measure_ne_top _ _)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / c.toReal < N + 1 := by
    simpa using exists_nat_gt (1 / c.toReal)
  have hseg_real_le : (N + 1 : ℝ) * c.toReal ≤ 1 := by
    have hmul_ne_top : ((N + 1 : ℝ≥0∞) * c) ≠ ∞ := by
      exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
    have := ENNReal.toReal_mono hmul_ne_top (hseg_le N)
    simpa [c, ENNReal.toReal_mul, measure_ne_top _ _] using this
  have hc_real_ne : c.toReal ≠ 0 := by
    exact hc_real_pos.ne'
  have : 1 < (N + 1 : ℝ) * c.toReal := by
    have hN' : (1 / c.toReal) * c.toReal < (N + 1 : ℝ) * c.toReal := by
      exact mul_lt_mul_of_pos_right hN hc_real_pos
    simpa [hc_real_ne] using hN'
  linarith
-/

-- Proof sketch: project the chain to its first coordinate. Away from the axis this coordinate is
-- a lazy nearest-neighbor walk on `ℤ` and it returns to `0` almost surely, while each visit to
-- the axis restarts a recurrent vertical excursion. The chain is therefore recurrent, but the
-- expected return time is infinite as in the two-dimensional simple random walk regime.
/-- Exercise 18.2.4 (1): every realization of the axis-blocked walk on `ℤ²` is null recurrent. -/
theorem vertical_axis_blocked_walk_isNullRecurrentMarkovChain :
    IsNullRecurrentMarkovChain P X := by
  have horigin : IsRecurrentState P X (0, 0) :=
    axisBlockedWalk_originRecurrent (P := P) (X := X)
  have hrec : IsRecurrentMarkovChain P X :=
    axisBlockedWalk_recurrentMarkovChain_of_originRecurrent (P := P) (X := X) horigin
  have hnoInv :
      invariantDistributions axisBlockedKernel = ∅ :=
    axisBlockedWalk_invariantDistributions_eq_empty_of_recurrent (P := P) (X := X) hrec
  intro x
  refine ⟨hrec x, ?_⟩
  intro hxPos
  -- Proof comment: a positive recurrent state would produce an invariant distribution, but the
  -- recurrent irreducible walk has none by the counting-measure obstruction above.
  obtain ⟨π, hπInv, _⟩ :=
    existsInvariantDistributionAtPositiveRecurrentState
      (κ := fun n : ℕ ↦ axisBlockedKernel ^ n) (P := P) (X := X) x hxPos
  have hπmem : π ∈ invariantDistributions axisBlockedKernel := by
    rw [mem_invariantDistributions_iff]
    simpa [axisBlockedKernel] using hπInv
  simpa [hnoInv] using hπmem

-- Proof sketch: the horizontal coordinate can always be moved one step toward `0`, along the
-- axis the walk can change the vertical coordinate by nearest-neighbor moves, and then the
-- horizontal coordinate can be moved away from the axis again. Concatenating such paths gives a
-- positive-probability route between any two states.
/-- Exercise 18.2.4 (2): every realization of the axis-blocked walk on `ℤ²` is irreducible. -/
theorem vertical_axis_blocked_walk_isIrreducibleMarkovChain :
    IsIrreducibleMarkovChain P X := by
  -- Proof comment: this is exactly the file-local irreducibility package built from the explicit
  -- positive-path lemmas.
  exact axisBlockedWalk_isIrreducibleMarkovChain (P := P) (X := X)

end RealizationResults

-- Proof sketch: every off-axis state has a one-step self-loop of probability `1 / 2`, so its
-- period is `1`. Irreducibility then forces all states, including those on the vertical axis, to
-- have period `1`.
/-- Exercise 18.2.4 (3): the axis-blocked walk on `ℤ²` is aperiodic. -/
theorem vertical_axis_blocked_walk_isAperiodic :
    IsAperiodic (discreteMatrixKernel vertical_axis_blocked_walk_transition_matrix) := by
  intro x
  rcases axisBlockedWalk_positivePathMass x (1, 0) with ⟨m, hm⟩
  rcases axisBlockedWalk_positivePathMass (1, 0) x with ⟨n, hn⟩
  have hloop :
      0 < axisBlockedKernel (1, 0) ({(1, 0)} : Set AxisState) := by
    exact axisBlockedWalk_selfLoop_pos (x := (1, 0)) (by norm_num)
  have hreturn :
      m + n ∈ positiveTransitionStepSet axisBlockedKernel x x := by
    -- Proof comment: the positive path from `x` to `(1,0)` and back gives one return time.
    rw [mem_positiveTransitionStepSet_iff]
    simpa [Nat.add_comm] using axisBlockedWalk_positiveSingletonComp hm hn
  have hreturnSucc :
      m + 1 + n ∈ positiveTransitionStepSet axisBlockedKernel x x := by
    have hmid :
        0 < (axisBlockedKernel ^ (m + 1)) x ({(1, 0)} : Set AxisState) := by
      -- Proof comment: insert the off-axis self-loop at `(1,0)` before returning to `x`.
      simpa [Nat.add_comm] using
        axisBlockedWalk_positiveSingletonComp (m := m) (n := 1) hm (by simpa [pow_one] using hloop)
    rw [mem_positiveTransitionStepSet_iff]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      axisBlockedWalk_positiveSingletonComp hmid hn
  have hd₀ : statePeriod axisBlockedKernel x ∣ m + n :=
    statePeriod_dvd_of_mem_positiveTransitionStepSet axisBlockedKernel x hreturn
  have hd₁ : statePeriod axisBlockedKernel x ∣ m + 1 + n :=
    statePeriod_dvd_of_mem_positiveTransitionStepSet axisBlockedKernel x hreturnSucc
  have hdiff :
      statePeriod axisBlockedKernel x ∣ (m + 1 + n) - (m + n) :=
    Nat.dvd_sub hd₁ hd₀
  have hone : statePeriod axisBlockedKernel x ∣ 1 := by
    have hsub : (m + 1 + n) - (m + n) = 1 := by omega
    simpa [hsub] using hdiff
  exact Nat.dvd_one.mp hone

/-- Helper for Exercise 18.2.4: the free product-pair chain evolves two copies of the
axis-blocked walk independently. -/
private def independentProductPairMatrix :
    (AxisState × AxisState) → (AxisState × AxisState) → ℝ≥0∞
  | (x₁, y₁), (x₂, y₂) =>
      vertical_axis_blocked_walk_transition_matrix x₁ x₂ *
        vertical_axis_blocked_walk_transition_matrix y₁ y₂

/-- Helper for Exercise 18.2.4: the free product-pair step matrix is invariant under common
vertical shifts of both the source and target pairs. -/
private theorem independentProductPairMatrix_commonVerticalShift
    (h : ℤ) (s t : AxisState × AxisState) :
    independentProductPairMatrix (freePairCommonVerticalShift h s)
      (freePairCommonVerticalShift h t) =
        independentProductPairMatrix s t := by
  rcases s with ⟨x, y⟩
  rcases t with ⟨z, w⟩
  -- Proof comment: common vertical shifts preserve each coordinate factor separately, so the
  -- independent-product row is unchanged as well.
  simp [independentProductPairMatrix, freePairCommonVerticalShift,
    vertical_axis_blocked_walk_transition_matrix_shift_second]

/-- Helper for Exercise 18.2.4: the diagonal-absorbed free product-pair chain freezes diagonal
states and otherwise follows the free product-pair step. -/
private def independentProductPairAbsorbDiagonalMatrix :
    (AxisState × AxisState) → (AxisState × AxisState) → ℝ≥0∞ :=
  fun s t ↦
    if hs : s.1 = s.2 then
      if t = s then 1 else 0
    else
      independentProductPairMatrix s t

/-- Helper for Exercise 18.2.4: on a countable discrete state space, integrating singleton rows of
a kernel is the same as summing the singleton masses against the source measure. -/
private lemma lintegral_kernel_apply_singleton_eq_tsum
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (κ : Kernel S S) (μ : Measure S) (w : S) :
    ∫⁻ c, κ c ({w} : Set S) ∂μ =
      ∑' c : S, κ c ({w} : Set S) * μ ({c} : Set S) := by
  -- Proof comment: `lintegral_countable'` is the standard discrete-space bridge from a kernel
  -- integral to the corresponding countable singleton sum.
  simpa [mul_comm] using
    (MeasureTheory.lintegral_countable' (μ := μ)
      (f := fun c : S ↦ κ c ({w} : Set S)))

/-- Helper for Exercise 18.2.4: the free product-pair matrix stays stochastic because its row sum
factorizes as the product of the two base row sums. -/
private theorem independentProductPairMatrix_isStochastic :
    IsStochasticMatrix independentProductPairMatrix := by
  rintro ⟨x, y⟩
  -- Proof comment: expand the row indexed by `(x,y)` as the product of the two one-coordinate row
  -- sums.
  calc
    ∑' s : AxisState × AxisState, independentProductPairMatrix (x, y) s
        = ∑' z : AxisState, ∑' w : AxisState,
            independentProductPairMatrix (x, y) (z, w) := by
              simpa using
                (ENNReal.tsum_prod'
                  (f := fun s : AxisState × AxisState ↦ independentProductPairMatrix (x, y) s))
    _ = ∑' z : AxisState,
          ∑' w : AxisState,
            vertical_axis_blocked_walk_transition_matrix x z *
              vertical_axis_blocked_walk_transition_matrix y w := by
            refine tsum_congr fun z ↦ ?_
            refine tsum_congr fun w ↦ ?_
            rfl
    _ = ∑' z : AxisState,
          vertical_axis_blocked_walk_transition_matrix x z *
            ∑' w : AxisState, vertical_axis_blocked_walk_transition_matrix y w := by
            refine tsum_congr fun z ↦ ?_
            rw [ENNReal.tsum_mul_left]
    _ = ∑' z : AxisState, vertical_axis_blocked_walk_transition_matrix x z * 1 := by
          simp [vertical_axis_blocked_walk_transition_matrix_tsum]
    _ = (∑' z : AxisState, vertical_axis_blocked_walk_transition_matrix x z) * 1 := by
          rw [ENNReal.tsum_mul_right]
    _ = 1 := by simp [vertical_axis_blocked_walk_transition_matrix_tsum]

/-- Helper for Exercise 18.2.4: every stochastic matrix on a countable discrete space admits the
canonical path-space realization coming from `Kernel.trajMeasure`. -/
private theorem existsCanonicalDiscreteMatrixRealization
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (q : S → S → ENNReal) (hq : IsStochasticMatrix q) :
    ∃ Pq : S → ProbabilityMeasure (ℕ → S),
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n) Pq Function.eval := by
  let κ : Kernel S S := discreteMatrixKernel q
  letI : IsMarkovKernel κ := discreteMatrixKernel_isMarkovKernel q hq
  let η : (n : ℕ) → Kernel (Π i : Finset.Iic n, S) S :=
    fun n ↦
      Kernel.comap κ
        (fun z : Π i : Finset.Iic n, S ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
        (by fun_prop)
  have hη : ∀ n : ℕ, IsMarkovKernel (η n) := by
    intro n
    dsimp [η]
    infer_instance
  let μ : S → Measure (ℕ → S) :=
    fun x ↦
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      Kernel.trajMeasure (X := fun _ : ℕ ↦ S) (Measure.dirac x) η
  have hμ : ∀ x : S, IsProbabilityMeasure (μ x) := by
    intro x
    dsimp [μ]
    infer_instance
  let Pq : S → ProbabilityMeasure (ℕ → S) := fun x ↦ ⟨μ x, hμ x⟩
  refine ⟨Pq, ?_⟩
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := κ)
    (P := Pq)
    (X := Function.eval)
    (hmeas := fun n ↦ measurable_pi_apply n)
    ?_ ?_
  · intro x
    have hprefix :
        (μ x).map (Preorder.frestrictLe 0) = Measure.dirac (fun _ : Finset.Iic 0 ↦ x) := by
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      -- Proof comment: at time `0`, the trajectory measure fixes the unique initial prefix to the
      -- constant function at the start state.
      simpa [μ, η, Kernel.partialTraj_self] using
        (Kernel.trajMeasure_map_frestrictLe
          (X := fun _ : ℕ ↦ S) (μ₀ := Measure.dirac x) (κ := η) 0)
    calc
      (Pq x : Measure (ℕ → S)).map (Function.eval 0)
          = ((μ x).map (Preorder.frestrictLe 0)).map
              (fun z : Finset.Iic 0 → S ↦ z ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rfl
      _ = Measure.dirac x := by
            rw [hprefix]
            simp
  · intro x A hA n
    letI : Nonempty S := ⟨x⟩
    let H : (ℕ → S) → Finset.Iic n → S := Preorder.frestrictLe n
    have hH_meas : Measurable H := Preorder.measurable_frestrictLe n
    have hnext_meas : Measurable (Function.eval (n + 1) : (ℕ → S) → S) :=
      measurable_pi_apply (n + 1)
    have hcond :
        condDistrib (Function.eval (n + 1)) H (μ x) =ᵐ[(μ x).map H] η n := by
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      -- Proof comment: `Kernel.condDistrib_trajMeasure` is the owner theorem recording the
      -- one-step restart law of the canonical trajectory measure.
      simpa [μ, H, η] using
        (Kernel.condDistrib_trajMeasure
          (X := fun _ : ℕ ↦ S) (μ₀ := Measure.dirac x) (κ := η) (a := n))
    have hcondexp :
        (μ x)⟦(Function.eval (n + 1)) ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ x]
          fun ξ ↦ (condDistrib (Function.eval (n + 1)) H (μ x) (H ξ)).real A := by
      simpa using
        (condDistrib_ae_eq_condExp (μ := μ x) (X := H) (Y := Function.eval (n + 1))
          hH_meas hnext_meas hA).symm
    have hcond_comp :
        (fun ξ ↦ (condDistrib (Function.eval (n + 1)) H (μ x) (H ξ)).real A) =ᵐ[μ x]
          fun ξ ↦ (η n (H ξ)).real A := by
      filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ξ hξ
      simpa [Function.comp] using congrArg (fun ν : Measure S ↦ ν.real A) hξ
    have hgen :
        generatedFiltrationSpace (Function.eval : ℕ → (ℕ → S) → S) n =
          MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance := by
      refine le_antisymm ?_ ?_
      · rw [generatedFiltrationSpace]
        refine iSup₂_le fun t ht ↦ ?_
        let i : Finset.Iic n := ⟨t, Finset.mem_Iic.2 ht⟩
        have hCoord :
            Measurable[
              MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance]
              (Function.eval t : (ℕ → S) → S) := by
          simpa [Function.eval, Preorder.frestrictLe_apply, i] using
            (measurable_pi_apply i).comp (comap_measurable (Preorder.frestrictLe n))
        exact hCoord.comap_le
      · have hPrefix :
          Measurable[
            generatedFiltrationSpace (Function.eval : ℕ → (ℕ → S) → S) n]
            (Preorder.frestrictLe n : (ℕ → S) → Finset.Iic n → S) := by
          rw [@measurable_pi_iff]
          intro i
          refine Measurable.of_comap_le ?_
          exact le_iSup_of_le i.1 <| le_iSup_of_le (Finset.mem_Iic.1 i.2) le_rfl
        exact hPrefix.comap_le
    rw [hgen]
    exact hcondexp.trans <|
      hcond_comp.trans <|
        Filter.Eventually.of_forall fun ξ ↦ by
          simpa [η, H, Preorder.frestrictLe_apply] using
            congrArg (fun ν : Measure S ↦ ν.real A) rfl

/-- Helper for Exercise 18.2.4: the relative state keeps the two horizontal coordinates and the
vertical difference of a free product-pair state. -/
private abbrev FreePairRelativeState := AxisState × ℤ

/-- Helper for Exercise 18.2.4: quotient the common vertical translation of a pair by keeping the
horizontal coordinates and the vertical difference. -/
private def axisBlockedFreePairRelativeState :
    AxisState × AxisState → FreePairRelativeState
  | ((x₁, x₂), (y₁, y₂)) => ((x₁, y₁), x₂ - y₂)

/-- Helper for Exercise 18.2.4: common vertical shifts leave the relative-state quotient
unchanged. -/
private theorem axisBlockedFreePairRelativeState_commonVerticalShift
    (h : ℤ) (s : AxisState × AxisState) :
    axisBlockedFreePairRelativeState (freePairCommonVerticalShift h s) =
      axisBlockedFreePairRelativeState s := by
  rcases s with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  -- Proof comment: the horizontal coordinates are unchanged by the common shift, and the added
  -- height cancels in the vertical difference.
  simp [freePairCommonVerticalShift, verticalShiftState, axisBlockedFreePairRelativeState]

/-- Helper for Exercise 18.2.4: a canonical representative of a relative state is obtained by
placing the second walker at height `0`. -/
private def freePairRelativeStateRepresentative
    (r : FreePairRelativeState) : AxisState × AxisState :=
  (((r.1.1, r.2) : AxisState), ((r.1.2, 0) : AxisState))

/-- Helper for Exercise 18.2.4: the canonical representative realizes the prescribed relative
state. -/
private theorem axisBlockedFreePairRelativeState_representative
    (r : FreePairRelativeState) :
    axisBlockedFreePairRelativeState (freePairRelativeStateRepresentative r) = r := by
  rcases r with ⟨⟨x, y⟩, d⟩
  -- Proof comment: the representative stores the required horizontal coordinates and vertical
  -- difference by construction.
  ext <;> simp [freePairRelativeStateRepresentative, axisBlockedFreePairRelativeState]

/-- Helper for Exercise 18.2.4: every free pair is recovered by shifting the canonical
representative of its relative state by the second walker's height. -/
private theorem freePairCommonVerticalShift_representative_relativeState
    (s : AxisState × AxisState) :
    freePairCommonVerticalShift s.2.2
      (freePairRelativeStateRepresentative (axisBlockedFreePairRelativeState s)) = s := by
  rcases s with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  -- Proof comment: the canonical representative normalizes the second walker's height to `0`,
  -- so shifting back by `y₂` restores both original vertical coordinates.
  ext <;> simp [freePairCommonVerticalShift, freePairRelativeStateRepresentative,
    axisBlockedFreePairRelativeState, verticalShiftState]

/-- Helper for Exercise 18.2.4: the fiber of a relative state is exactly the orbit of its
canonical representative under common vertical shifts. -/
private theorem preimage_singleton_axisBlockedFreePairRelativeState
    (r : FreePairRelativeState) :
    axisBlockedFreePairRelativeState ⁻¹' ({r} : Set FreePairRelativeState) =
      Set.range fun h : ℤ ↦
        freePairCommonVerticalShift h (freePairRelativeStateRepresentative r) := by
  ext s
  constructor
  · intro hs
    refine ⟨s.2.2, ?_⟩
    -- Proof comment: once the relative state is fixed, the only remaining freedom is the common
    -- absolute height, encoded here by the second walker's vertical coordinate.
    have hs' : axisBlockedFreePairRelativeState s = r := by
      simpa using hs
    simpa [hs'.symm] using freePairCommonVerticalShift_representative_relativeState s
  · rintro ⟨h, rfl⟩
    -- Proof comment: common vertical shifts do not change the relative quotient, and the chosen
    -- representative already realizes `r`.
    simp [axisBlockedFreePairRelativeState_commonVerticalShift,
      axisBlockedFreePairRelativeState_representative]

/-- Helper for Exercise 18.2.4: the inverse image of a singleton under a common vertical shift of
both walkers is the singleton shifted back by the opposite amount. -/
private theorem preimage_singleton_freePairCommonVerticalShift
    (h : ℤ) (t : AxisState × AxisState) :
    freePairCommonVerticalShift h ⁻¹' ({t} : Set (AxisState × AxisState)) =
      {freePairCommonVerticalShift (-h) t} := by
  ext s
  rcases s with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  rcases t with ⟨⟨z₁, z₂⟩, ⟨w₁, w₂⟩⟩
  simp [freePairCommonVerticalShift, verticalShiftState]
  omega

/-- Helper for Exercise 18.2.4: shifting the source row of the free product-pair kernel by a
common vertical offset pushes the whole row forward by the same shift. -/
private theorem independentProductPairKernel_row_commonVerticalShift
    (h : ℤ) (s : AxisState × AxisState) :
    (discreteMatrixKernel independentProductPairMatrix) (freePairCommonVerticalShift h s) =
      Measure.map (freePairCommonVerticalShift h)
        ((discreteMatrixKernel independentProductPairMatrix) s) := by
  refine Measure.ext_of_singleton fun t ↦ ?_
  rw [Measure.map_apply (measurable_of_countable (f := freePairCommonVerticalShift h))
    (measurableSet_singleton t)]
  rw [preimage_singleton_freePairCommonVerticalShift]
  rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
  -- Proof comment: rewrite the target singleton through the inverse shift, then apply the
  -- common-vertical-shift invariance of the free product-pair step matrix.
  simpa [freePairCommonVerticalShift] using
    independentProductPairMatrix_commonVerticalShift h s
      (freePairCommonVerticalShift (-h) t)

/-- Helper for Exercise 18.2.4: the natural owner kernel on relative states is obtained by
pushing the free product-pair one-step law through the relative-state quotient. -/
private def axisBlockedFreePairRelativeKernel :
    Kernel FreePairRelativeState FreePairRelativeState :=
  Kernel.ofFunOfCountable fun r ↦
    Measure.map axisBlockedFreePairRelativeState
      ((discreteMatrixKernel independentProductPairMatrix)
        (freePairRelativeStateRepresentative r))

/-- Helper for Exercise 18.2.4: the relative owner kernel is Markov because each row is the
pushforward of a probability row of the free product-pair kernel. -/
private instance axisBlockedFreePairRelativeKernel_isMarkovKernel :
    IsMarkovKernel axisBlockedFreePairRelativeKernel := by
  refine ⟨fun r ↦ ?_⟩
  change IsProbabilityMeasure
    (Measure.map axisBlockedFreePairRelativeState
      ((discreteMatrixKernel independentProductPairMatrix)
        (freePairRelativeStateRepresentative r)))
  letI : IsMarkovKernel (discreteMatrixKernel independentProductPairMatrix) :=
    discreteMatrixKernel_isMarkovKernel
      independentProductPairMatrix
      independentProductPairMatrix_isStochastic
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete.aemeasurable)

/-- Helper for Exercise 18.2.4: the one-step pushforward of the free product-pair chain depends
only on the current relative state. -/
private theorem axisBlockedFreePairRelativeState_oneStepKernel
    (s : AxisState × AxisState) :
    Measure.map axisBlockedFreePairRelativeState
      ((discreteMatrixKernel independentProductPairMatrix) s) =
      axisBlockedFreePairRelativeKernel (axisBlockedFreePairRelativeState s) := by
  -- Proof comment: normalize `s` to its canonical representative and shift the one-step row
  -- along the common vertical orbit; the relative quotient then forgets that shift.
  rw [← freePairCommonVerticalShift_representative_relativeState s]
  rw [independentProductPairKernel_row_commonVerticalShift]
  rw [Measure.map_map
    (measurable_of_countable (f := freePairCommonVerticalShift s.2.2))
    (measurable_of_countable (f := axisBlockedFreePairRelativeState))]
  congr 1
  ext t
  simp [Function.comp, axisBlockedFreePairRelativeState_commonVerticalShift]

/-- Helper for Exercise 18.2.4: the relative-state start for `((0,0),(0,1))` is `((0,0),-1)`. -/
private theorem axisBlockedFreePairRelativeState_start :
    axisBlockedFreePairRelativeState
      ((((0, 0) : AxisState), ((0, 1) : AxisState))) = (((0, 0) : AxisState), -1) := by
  -- Proof comment: this is the direct coordinate normalization of the distinguished start pair.
  norm_num [axisBlockedFreePairRelativeState]

/-- Helper for Exercise 18.2.4: in relative coordinates, collision means equal horizontal
coordinates and zero vertical difference. -/
private def axisBlockedFreePairCollisionSet : Set FreePairRelativeState :=
  {r | r.1.1 = r.1.2 ∧ r.2 = 0}

/-- Helper for Exercise 18.2.4: the defect set is where at least one walker sits on the axis, so
the vertical difference can change on the next step. -/
private def axisBlockedFreePairDefectSet : Set FreePairRelativeState :=
  {r | r.1.1 = 0 ∨ r.1.2 = 0}

/-- Helper for Exercise 18.2.4: a pair lies on the diagonal exactly when its relative state lies
in the collision set. -/
private theorem mem_axisBlockedFreePairCollisionSet_iff
    (s : AxisState × AxisState) :
    axisBlockedFreePairRelativeState s ∈ axisBlockedFreePairCollisionSet ↔ s.1 = s.2 := by
  rcases s with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  -- Proof comment: unpacking the quotient leaves exactly the two coordinate equalities defining
  -- diagonal collision.
  constructor
  · intro hs
    rcases hs with ⟨hxy, hdiff⟩
    apply Prod.ext
    · exact hxy
    · omega
  · intro hs
    rcases Prod.mk.inj hs with ⟨h₁, h₂⟩
    constructor
    · exact h₁
    · omega

/-- Helper for Exercise 18.2.4: a pair lies in the defect set exactly when one of its horizontal
coordinates is `0`. -/
private theorem mem_axisBlockedFreePairDefectSet_iff
    (s : AxisState × AxisState) :
    axisBlockedFreePairRelativeState s ∈ axisBlockedFreePairDefectSet ↔
      s.1.1 = 0 ∨ s.2.1 = 0 := by
  rcases s with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  -- Proof comment: the relative-state quotient leaves the two horizontal coordinates unchanged.
  simp [axisBlockedFreePairRelativeState, axisBlockedFreePairDefectSet]

/-- Helper for Exercise 18.2.4: absorbing the full diagonal preserves stochasticity of the free
product-pair matrix. -/
private theorem independentProductPairAbsorbDiagonalMatrix_isStochastic :
    IsStochasticMatrix independentProductPairAbsorbDiagonalMatrix := by
  intro s
  by_cases hs : s.1 = s.2
  · rw [tsum_eq_single s]
    · simp [independentProductPairAbsorbDiagonalMatrix, hs]
    · intro t ht
      simp [independentProductPairAbsorbDiagonalMatrix, hs, ht]
  · simp [independentProductPairAbsorbDiagonalMatrix, hs,
      independentProductPairMatrix_isStochastic s]

section IndependentProductPairAvoidance

variable {Ωq : Type*} [MeasurableSpace Ωq]
variable {Pq : AxisState × AxisState → ProbabilityMeasure Ωq}
variable {Xq : ℕ → Ωq → AxisState × AxisState}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq]

/-- Helper for Exercise 18.2.4: bounded diagonal avoidance with a prescribed endpoint records that
the free product-pair chain stays off the diagonal through time `n` and ends at `w`. -/
private def avoidDiagonalUntilWithEndpoint
    (n : ℕ) (w : AxisState × AxisState) : Set Ωq :=
  {ω | Xq n ω = w ∧ ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2}

/-- Helper for Exercise 18.2.4: the bounded endpoint-refined diagonal-avoidance event is
measurable with respect to the time-`n` history filtration. -/
private theorem avoidDiagonalUntilWithEndpoint_measurableSet
    (n : ℕ) (w : AxisState × AxisState) :
    MeasurableSet[generatedFiltrationSpace Xq n] (avoidDiagonalUntilWithEndpoint (Xq := Xq) n w) := by
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hState :
      MeasurableSet[generatedFiltrationSpace Xq n] {ω | Xq n ω = w} := by
    have hXn : Measurable[generatedFiltrationSpace Xq n] (Xq n) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) n
    rw [show ({ω | Xq n ω = w} : Set Ωq) = Xq n ⁻¹' ({w} : Set (AxisState × AxisState)) by
      ext ω
      simp]
    exact hXn (measurableSet_singleton w)
  have hAvoid :
      MeasurableSet[generatedFiltrationSpace Xq n]
        {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} := by
    have hrepr :
        {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} =
          ⋂ m : ℕ, if m ≤ n then {ω | (Xq m ω).1 ≠ (Xq m ω).2} else Set.univ := by
      ext ω
      simp
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : m ≤ n
    · have hXm : Measurable[generatedFiltrationSpace Xq n] (Xq m) := by
        exact Measurable.of_comap_le <|
          le_iSup_of_le m <| le_iSup_of_le hm le_rfl
      have hDiag : MeasurableSet {s : AxisState × AxisState | s.1 = s.2} :=
        MeasurableSet.of_discrete
      simpa [hm] using (hXm hDiag).compl
    · simp [hm]
  -- Proof comment: the endpoint condition and the bounded diagonal-avoidance condition are both
  -- decided by the time-`n` history.
  simpa [avoidDiagonalUntilWithEndpoint] using hState.inter hAvoid

/-- Helper for Exercise 18.2.4: if the prescribed endpoint is diagonal, then bounded diagonal
avoidance with that endpoint is impossible. -/
private theorem avoidDiagonalUntilWithEndpoint_eq_empty_of_diag
    (n : ℕ) {w : AxisState × AxisState} (hw : w.1 = w.2) :
    avoidDiagonalUntilWithEndpoint (Xq := Xq) n w = (∅ : Set Ωq) := by
  ext ω
  constructor
  · intro hω
    exact False.elim <| (hω.2 n le_rfl) (by simpa [hω.1] using hw)
  · simp [avoidDiagonalUntilWithEndpoint]

/-- Helper for Exercise 18.2.4: bounded diagonal avoidance with an off-diagonal endpoint equals
the corresponding singleton mass of the absorbed free product-pair chain. -/
private theorem freeAvoidDiagonalEndpointProb_eq_absorbedDiagonalEndpointMass :
    ∀ n : ℕ, ∀ a : AxisState × AxisState, ∀ {w : AxisState × AxisState}, w.1 ≠ w.2 →
      (Pq a : Measure Ωq) (avoidDiagonalUntilWithEndpoint (Xq := Xq) n w) =
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a)
          ({w} : Set (AxisState × AxisState)) := by
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  letI : IsMarkovKernel κAbs :=
    discreteMatrixKernel_isMarkovKernel
      independentProductPairAbsorbDiagonalMatrix
      independentProductPairAbsorbDiagonalMatrix_isStochastic
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  intro n
  induction n with
  | zero =>
      intro a w hw
      have hset :
          avoidDiagonalUntilWithEndpoint (Xq := Xq) 0 w = {ω | Xq 0 ω = w} := by
        ext ω
        constructor
        · intro hω
          exact hω.1
        · intro hω
          refine ⟨hω, ?_⟩
          intro m hm
          have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
          subst hm0
          cases hω
          exact hw
      -- Proof comment: at time `0`, the endpoint condition already forces diagonal avoidance.
      rw [hset]
      rw [show ({ω | Xq 0 ω = w} : Set Ωq) = Xq 0 ⁻¹' ({w} : Set (AxisState × AxisState)) by
        ext ω
        simp]
      rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton w)]
      rw [hqreal.transition_eq a 0]
      simp [κAbs, Kernel.id_apply, hw]
  | succ n ih =>
      intro a w hw
      let μ : Measure Ωq := (Pq a : Measure Ωq)
      have hUnion :
          avoidDiagonalUntilWithEndpoint (Xq := Xq) (n + 1) w =
            ⋃ c : AxisState × AxisState,
              avoidDiagonalUntilWithEndpoint (Xq := Xq) n c ∩ {ω | Xq (n + 1) ω = w} := by
        ext ω
        constructor
        · intro hω
          refine Set.mem_iUnion.2 ⟨Xq n ω, ?_⟩
          refine ⟨?_, hω.1⟩
          refine ⟨rfl, ?_⟩
          intro m hm
          exact hω.2 m (Nat.le_trans hm (Nat.le_succ _))
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨c, hcω⟩
          refine ⟨hcω.2, ?_⟩
          intro m hm
          rcases Nat.eq_or_lt_of_le hm with rfl | hm_lt
          · cases hcω.2
            exact hw
          · exact hcω.1.2 m (Nat.le_of_lt_succ hm_lt)
      have hPairwise :
          Pairwise fun c d : AxisState × AxisState ↦
            Disjoint
              (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c ∩ {ω | Xq (n + 1) ω = w})
              (avoidDiagonalUntilWithEndpoint (Xq := Xq) n d ∩ {ω | Xq (n + 1) ω = w}) := by
        intro c d hcd
        refine Set.disjoint_left.2 ?_
        intro ω hc hd
        apply hcd
        exact hc.1.1.symm.trans hd.1.1
      have hMeas :
          ∀ c : AxisState × AxisState,
            MeasurableSet
              (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c ∩ {ω | Xq (n + 1) ω = w}) := by
        intro c
        have hAvoid_hist :
            MeasurableSet[generatedFiltrationSpace Xq n]
              (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) :=
          avoidDiagonalUntilWithEndpoint_measurableSet (Xq := Xq) n c
        have hAvoid :
            MeasurableSet (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) := by
          exact (generatedHistory_le_ambient Xq hqreal.measurable_process n) _ hAvoid_hist
        have hState :
            MeasurableSet ({ω | Xq (n + 1) ω = w} : Set Ωq) := by
          rw [show ({ω | Xq (n + 1) ω = w} : Set Ωq) =
              Xq (n + 1) ⁻¹' ({w} : Set (AxisState × AxisState)) by
            ext ω
            simp]
          exact (hqreal.measurable_process (n + 1)) (measurableSet_singleton w)
        exact hAvoid.inter hState
      -- Proof comment: decompose by the time-`n` endpoint, factor each history slice through the
      -- free one-step row, and then replace that row by the absorbed row away from the diagonal.
      calc
        μ (avoidDiagonalUntilWithEndpoint (Xq := Xq) (n + 1) w) =
            ∑' c : AxisState × AxisState,
              μ (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c ∩ {ω | Xq (n + 1) ω = w}) := by
                rw [hUnion]
                exact MeasureTheory.measure_iUnion hPairwise hMeas
        _ =
            ∑' c : AxisState × AxisState,
              (discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix c
                  ({w} : Set (AxisState × AxisState))) *
                ((κAbs ^ n) a) ({c} : Set (AxisState × AxisState)) := by
                  refine tsum_congr fun c ↦ ?_
                  by_cases hc : c.1 ≠ c.2
                  · have hAvoid_meas :
                        MeasurableSet (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) := by
                      have hAvoid_hist :
                          MeasurableSet[generatedFiltrationSpace Xq n]
                            (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) :=
                        avoidDiagonalUntilWithEndpoint_measurableSet (Xq := Xq) n c
                      exact
                        (generatedHistory_le_ambient Xq hqreal.measurable_process n) _
                          hAvoid_hist
                    have hAvoid_hist :
                        MeasurableSet[generatedFiltrationSpace Xq n]
                          (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) :=
                      avoidDiagonalUntilWithEndpoint_measurableSet (Xq := Xq) n c
                    have hAvoid_state :
                        ∀ ⦃ω : Ωq⦄,
                          ω ∈ avoidDiagonalUntilWithEndpoint (Xq := Xq) n c → Xq n ω = c := by
                      intro ω hω
                      exact hω.1
                    rw [measureInter_eq_mul_stepMass_of_stateEvent
                      (q := independentProductPairMatrix) (P := Pq) (X := Xq) a c w n
                      (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c)
                      hAvoid_meas hAvoid_hist hAvoid_state]
                    rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
                    have hmass := ih a (w := c) hc
                    simpa [independentProductPairAbsorbDiagonalMatrix, independentProductPairMatrix,
                      hc, mul_assoc, mul_left_comm, mul_comm] using
                      congrArg (fun t ↦ independentProductPairMatrix c w * t) hmass
                  · have hcdiag : c.1 = c.2 := by simpa using hc
                    rw [avoidDiagonalUntilWithEndpoint_eq_empty_of_diag (Xq := Xq) n hcdiag]
                    have hcw : w ≠ c := by
                      intro hEq
                      apply hw
                      simpa [hEq] using hcdiag
                    have hstep_zero :
                        discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix c
                          ({w} : Set (AxisState × AxisState)) = 0 := by
                      rw [discreteMatrixKernel_apply_singleton]
                      simp [independentProductPairAbsorbDiagonalMatrix, hcdiag, hcw]
                    rw [hstep_zero]
                    simp
        _ = ((κAbs ^ (n + 1)) a) ({w} : Set (AxisState × AxisState)) := by
              -- Proof comment: normalize the absorbed successor step to the same singleton-mass
              -- series used on the previous line.
              rw [Kernel.pow_succ_apply_eq_lintegral κAbs n a (measurableSet_singleton w)]
              rw [MeasureTheory.lintegral_countable']
/-
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  letI : IsMarkovKernel κAbs :=
    discreteMatrixKernel_isMarkovKernel
      independentProductPairAbsorbDiagonalMatrix
      independentProductPairAbsorbDiagonalMatrix_isStochastic
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  intro n
  induction n with
  | zero =>
      intro a w hw
      have hset :
          avoidDiagonalUntilWithEndpoint (Xq := Xq) 0 w = {ω | Xq 0 ω = w} := by
        ext ω
        constructor
        · intro hω
          exact hω.1
        · intro hω
          refine ⟨hω, ?_⟩
          intro m hm
          have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
          subst hmzero
          cases hω
          exact hw
      -- Proof comment: at time `0`, the endpoint condition already forces diagonal avoidance.
      rw [hset]
      rw [show ({ω | Xq 0 ω = w} : Set Ωq) = Xq 0 ⁻¹' ({w} : Set (AxisState × AxisState)) by
        ext ω
        simp]
      rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton w)]
      rw [hqreal.transition_eq a 0]
      simp [κAbs, Kernel.id_apply, hw]
  | succ n ih =>
      intro a w hw
      let μ : Measure Ωq := (Pq a : Measure Ωq)
      have hUnion :
          avoidDiagonalUntilWithEndpoint (Xq := Xq) (n + 1) w =
            ⋃ c : AxisState × AxisState,
              avoidDiagonalUntilWithEndpoint (Xq := Xq) n c ∩ {ω | Xq (n + 1) ω = w} := by
            ext ω
            constructor
          · intro hω
            refine Set.mem_iUnion.2 ⟨Xq n ω, ?_⟩
            refine ⟨?_, hω.1⟩
            refine ⟨rfl, ?_⟩
            intro m hm
            exact hω.2 m (Nat.le_trans hm (Nat.le_succ _))
          · intro hω
            rcases Set.mem_iUnion.1 hω with ⟨c, hcω⟩
            refine ⟨hcω.2, ?_⟩
            intro m hm
            rcases Nat.eq_or_lt_of_le hm with rfl | hm_lt
            · cases hcω.2
              exact hw
            · exact hcω.1.2 m (Nat.le_of_lt_succ hm_lt)
      have hPairwise :
          Pairwise (Function.onFun Disjoint
            fun c : AxisState × AxisState ↦
              avoidDiagonalUntilWithEndpoint (Xq := Xq) n c ∩ {ω | Xq (n + 1) ω = w}) := by
            intro c d hcd
            refine Set.disjoint_left.2 ?_
            intro ω hc hd
            apply hcd
            exact hc.1.1.symm.trans hd.1.1
      have hMeas :
          ∀ c : AxisState × AxisState,
            MeasurableSet
              (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c ∩ {ω | Xq (n + 1) ω = w}) := by
            intro c
            have hAvoid :
                MeasurableSet (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) := by
              have hAvoid_hist :
                  MeasurableSet[generatedFiltrationSpace Xq n]
                    (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) :=
                avoidDiagonalUntilWithEndpoint_measurableSet (Xq := Xq) n c
              exact
                (generatedHistory_le_ambient Xq hqreal.measurable_process n) _
                  hAvoid_hist
            have hState :
                MeasurableSet ({ω | Xq (n + 1) ω = w} : Set Ωq) := by
              rw [show ({ω | Xq (n + 1) ω = w} : Set Ωq) =
                  Xq (n + 1) ⁻¹' ({w} : Set (AxisState × AxisState)) by
                ext ω
                simp]
              exact (hqreal.measurable_process (n + 1)) (measurableSet_singleton w)
            exact hAvoid.inter hState
      -- Proof comment: decompose by the time-`n` endpoint, factor each history slice through the
      -- free one-step row, and then replace that row by the absorbed row away from the diagonal.
      calc
        μ (avoidDiagonalUntilWithEndpoint (Xq := Xq) (n + 1) w) =
            ∑' c : AxisState × AxisState,
              μ (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c ∩ {ω | Xq (n + 1) ω = w}) := by
                rw [hUnion]
                exact MeasureTheory.measure_iUnion hPairwise hMeas
        _ =
            ∑' c : AxisState × AxisState,
              (discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix c
                  ({w} : Set (AxisState × AxisState))) *
                ((κAbs ^ n) a) ({c} : Set (AxisState × AxisState)) := by
                  refine tsum_congr fun c ↦ ?_
                  by_cases hc : c.1 ≠ c.2
                  · have hAvoid_meas :
                        MeasurableSet (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) := by
                      have hAvoid_hist :
                          MeasurableSet[generatedFiltrationSpace Xq n]
                            (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) :=
                        avoidDiagonalUntilWithEndpoint_measurableSet (Xq := Xq) n c
                      exact
                        (generatedHistory_le_ambient Xq hqreal.measurable_process n) _
                          hAvoid_hist
                    have hAvoid_hist :
                        MeasurableSet[generatedFiltrationSpace Xq n]
                          (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c) :=
                      avoidDiagonalUntilWithEndpoint_measurableSet (Xq := Xq) n c
                    have hAvoid_state :
                        ∀ ⦃ω : Ωq⦄,
                          ω ∈ avoidDiagonalUntilWithEndpoint (Xq := Xq) n c → Xq n ω = c := by
                      intro ω hω
                      exact hω.1
                    rw [measureInter_eq_mul_stepMass_of_stateEvent
                      (q := independentProductPairMatrix) (P := Pq) (X := Xq) a c w n
                      (avoidDiagonalUntilWithEndpoint (Xq := Xq) n c)
                      hAvoid_meas hAvoid_hist hAvoid_state]
                    rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
                    have hmass := ih a (w := c) hc
                    simpa [independentProductPairAbsorbDiagonalMatrix, independentProductPairMatrix,
                      hc, mul_assoc, mul_left_comm, mul_comm] using
                      congrArg (fun t ↦ independentProductPairMatrix c w * t) hmass
                  · have hcdiag : c.1 = c.2 := by simpa using hc
                    rw [avoidDiagonalUntilWithEndpoint_eq_empty_of_diag (Xq := Xq) n hcdiag]
                    have hcw : w ≠ c := by
                      intro hEq
                      apply hw
                      simpa [hEq] using hcdiag
                    have hstep_zero :
                        discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix c
                          ({w} : Set (AxisState × AxisState)) = 0 := by
                      rw [discreteMatrixKernel_apply_singleton]
                      simp [independentProductPairAbsorbDiagonalMatrix, hcdiag, hcw]
                    rw [hstep_zero]
                    simp
        _ = ((κAbs ^ (n + 1)) a) ({w} : Set (AxisState × AxisState)) := by
              rw [Kernel.pow_succ_apply_eq_lintegral κAbs n a (measurableSet_singleton w)]
              rw [MeasureTheory.lintegral_countable']

/-- Helper for Exercise 18.2.4: the absorbed free product-pair chain's off-diagonal mass is
exactly the bounded diagonal-avoidance probability of the free product-pair chain. -/
private theorem independentProductPairAbsorbDiagonal_offDiagonalMass_eq_freeAvoidDiagonalProb
    (a : AxisState × AxisState) (n : ℕ) :
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a)
        {s : AxisState × AxisState | s.1 ≠ s.2} =
      (Pq a : Measure Ωq) {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} := by
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  letI : IsMarkovKernel κAbs :=
    discreteMatrixKernel_isMarkovKernel
      independentProductPairAbsorbDiagonalMatrix
      independentProductPairAbsorbDiagonalMatrix_isStochastic
  let offDiag : Set (AxisState × AxisState) := {s : AxisState × AxisState | s.1 ≠ s.2}
  let μ : Measure Ωq := (Pq a : Measure Ωq)
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hMass :
      ((κAbs ^ n) a) offDiag =
        ∑' w : {u : AxisState × AxisState // u ∈ offDiag},
          ((κAbs ^ n) a) ({(w : AxisState × AxisState)} : Set (AxisState × AxisState)) := by
    calc
      ((κAbs ^ n) a) offDiag =
          ∑' w : AxisState × AxisState,
            offDiag.indicator
              (fun w ↦ ((κAbs ^ n) a) ({w} : Set (AxisState × AxisState))) w := by
                simpa using
                  (Measure.tsum_indicator_apply_singleton ((κAbs ^ n) a) offDiag
                    (show MeasurableSet offDiag from MeasurableSet.of_discrete)).symm
      _ =
          ∑' w : {u : AxisState × AxisState // u ∈ offDiag},
            ((κAbs ^ n) a) ({(w : AxisState × AxisState)} : Set (AxisState × AxisState)) := by
              rw [← tsum_subtype offDiag
                (fun w : AxisState × AxisState ↦
                  ((κAbs ^ n) a) ({w} : Set (AxisState × AxisState)))]
  have hUnion :
      {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} =
        ⋃ w : {u : AxisState × AxisState // u ∈ offDiag},
          avoidDiagonalUntilWithEndpoint (Xq := Xq) n w := by
      ext ω
      constructor
      · intro hω
        refine Set.mem_iUnion.2 ⟨⟨Xq n ω, hω n le_rfl⟩, ?_⟩
        exact ⟨rfl, hω⟩
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨w, hw⟩
        exact hw.2
  have hAvoid :
      μ {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} =
        ∑' w : {u : AxisState × AxisState // u ∈ offDiag},
          μ (avoidDiagonalUntilWithEndpoint (Xq := Xq) n w) := by
    rw [hUnion]
    refine MeasureTheory.measure_iUnion ?_ ?_
    · intro w₁ w₂ hw
      refine Set.disjoint_left.2 ?_
      intro ω h₁ h₂
      apply hw
      exact Subtype.ext <| h₁.1.symm.trans h₂.1
    · intro w
      exact
        (generatedHistory_le_ambient Xq hqreal.measurable_process n) _
          (avoidDiagonalUntilWithEndpoint_measurableSet (Xq := Xq) n w)
  -- Proof comment: decompose the absorbed off-diagonal mass into endpoint singleton masses and
  -- match each endpoint with the corresponding bounded free diagonal-avoidance event.
  calc
    ((κAbs ^ n) a) offDiag =
        ∑' w : {u : AxisState × AxisState // u ∈ offDiag},
          ((κAbs ^ n) a) ({(w : AxisState × AxisState)} : Set (AxisState × AxisState)) := hMass
    _ =
        ∑' w : {u : AxisState × AxisState // u ∈ offDiag},
          μ (avoidDiagonalUntilWithEndpoint (Xq := Xq) n w) := by
            refine tsum_congr fun w ↦ ?_
            symm
            simpa [μ, offDiag] using
              freeAvoidDiagonalEndpointProb_eq_absorbedDiagonalEndpointMass
                (Pq := Pq) (Xq := Xq) n a (w := (w : AxisState × AxisState)) w.2
    _ = μ {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} := hAvoid.symm
-/

end IndependentProductPairAvoidance

/-- Helper for Exercise 18.2.4: a positive never-meet probability gives a uniform positive lower
bound on every bounded diagonal-avoidance probability, so those probabilities cannot converge to
`0`. -/
private theorem not_tendsto_zero_of_boundedAvoidProb_pos
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [Zero E]
    (μ : Measure Ω) (X : ℕ → Ω → E)
    (havoid : 0 < μ {ω | ∀ n : ℕ, X n ω ≠ 0}) :
    ¬ Filter.Tendsto
      (fun n : ℕ ↦ μ {ω | ∀ m ≤ n, X m ω ≠ 0})
      Filter.atTop (nhds 0) := by
  intro ht
  let avoidEvent : Set Ω := {ω | ∀ n : ℕ, X n ω ≠ 0}
  have hlower :
      ∀ n : ℕ, μ avoidEvent ≤ μ {ω | ∀ m ≤ n, X m ω ≠ 0} := by
    intro n
    refine measure_mono ?_
    intro ω hω
    intro m hm
    exact hω m
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        μ {ω | ∀ m ≤ n, X m ω ≠ 0} < μ avoidEvent := by
    exact ht (Iio_mem_nhds havoid)
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  -- Proof comment: the infinite avoid event sits inside every bounded avoid event, so convergence
  -- to `0` would force an eventual strict upper bound below this fixed positive mass.
  exact (not_lt_of_ge (hlower N)) (hN N le_rfl)

/-- Helper for Exercise 18.2.4: a fixed positive scaled lower bound on a shifted subsequence
prevents convergence to `0`. -/
private theorem notTendstoZero_of_shiftedScaledLowerBound
    (u v : ℕ → ℝ≥0∞) {c : ℝ≥0∞} {k : ℕ}
    (hc_pos : 0 < c) (hc_ne_top : c ≠ ⊤)
    (hu : ¬ Filter.Tendsto u Filter.atTop (nhds 0))
    (hbound : ∀ n : ℕ, c * u n ≤ v (n + k)) :
    ¬ Filter.Tendsto v Filter.atTop (nhds 0) := by
  intro hv
  have hv_shift :
      Filter.Tendsto (fun n : ℕ ↦ v (n + k)) Filter.atTop (nhds 0) := by
    simpa using hv.comp (tendsto_add_atTop_nat k)
  have hscaled :
      Filter.Tendsto (fun n : ℕ ↦ c⁻¹ * v (n + k)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hv_shift)
  have hu_le :
      ∀ n : ℕ, u n ≤ c⁻¹ * v (n + k) := by
    intro n
    have hmul : c⁻¹ * (c * u n) ≤ c⁻¹ * v (n + k) := by
      exact mul_le_mul_left' (hbound n) c⁻¹
    simpa [mul_assoc, ENNReal.inv_mul_cancel hc_pos.ne' hc_ne_top, one_mul] using hmul
  have hu_zero :
      Filter.Tendsto u Filter.atTop (nhds 0) := by
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hscaled
        (Filter.Eventually.of_forall fun n ↦ bot_le)
        (Filter.Eventually.of_forall hu_le)
  exact hu hu_zero

/-- Helper for Exercise 18.2.4: a positive never-meet probability gives a uniform positive lower
bound on every bounded diagonal-avoidance probability, so those probabilities cannot converge to
`0`. -/
private theorem not_tendsto_zero_of_neverMeetProb_pos
    {Ωq : Type*} [MeasurableSpace Ωq]
    (μ : Measure Ωq) (Xq : ℕ → Ωq → AxisState × AxisState)
    (hnever : 0 < μ {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2}) :
    ¬ Filter.Tendsto
      (fun n : ℕ ↦ μ {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2})
      Filter.atTop (nhds 0) := by
  intro ht
  let neverMeet : Set Ωq := {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2}
  have hlower :
      ∀ n : ℕ, μ neverMeet ≤ μ {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} := by
    intro n
    refine measure_mono ?_
    intro ω hω
    intro m hm
    exact hω m
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        μ {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} < μ neverMeet := by
    exact ht (Iio_mem_nhds hnever)
  rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
  exact (not_lt_of_ge (hlower N)) (hN N le_rfl)

/-- Helper for Exercise 18.2.4: for the free product-pair chain started from `((0,0),(0,1))`,
the probability of never hitting the diagonal should stay strictly positive. -/
private theorem axisBlockedFreePair_startPair_launchToOffDefect_pos
    {Ωq : Type*} [MeasurableSpace Ωq]
    {Pq : AxisState × AxisState → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → AxisState × AxisState}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq] :
    0 <
      discreteMatrixKernel independentProductPairMatrix
        ((((0, 0) : AxisState), ((0, 1) : AxisState)))
        ({((((1, 0) : AxisState), ((1, 1) : AxisState)))} : Set (AxisState × AxisState)) := by
  rw [discreteMatrixKernel_apply_singleton]
  -- Proof comment: both coordinates make the horizontal `+1` move from the axis, so the product
  -- row contributes `(1 / 4) * (1 / 4)`.
  norm_num [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
    isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor]

/-- Helper for Exercise 18.2.4: from the launched off-defect pair `((1,0),(1,1))`, both walkers
can step left back to the axis start pair `((0,0),(0,1))` with positive probability. -/
private theorem axisBlockedFreePair_launchToStartPair_pos :
    0 <
      discreteMatrixKernel independentProductPairMatrix
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        ({((((0, 0) : AxisState), ((0, 1) : AxisState)))} : Set (AxisState × AxisState)) := by
  rw [discreteMatrixKernel_apply_singleton]
  -- Proof comment: each off-axis walk makes the horizontal `-1` move with probability `1 / 4`,
  -- so the independent product row contributes `(1 / 4) * (1 / 4)`.
  norm_num [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
    isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor]

/-- Helper for Exercise 18.2.4: for the free product-pair chain started from `((0,0),(0,1))`,
the probability of never hitting the diagonal should stay strictly positive. -/
private def freePairNeverMeetPathEvent : Set (ℕ → AxisState × AxisState) :=
  {path | ∀ n : ℕ, (path n).1 ≠ (path n).2}

/-- Helper for Exercise 18.2.4: the free pair never-meet path event is measurable on path space.
-/
private theorem measurableSet_freePairNeverMeetPathEvent :
    MeasurableSet freePairNeverMeetPathEvent := by
  have hrepr :
      freePairNeverMeetPathEvent =
        ⋂ n : ℕ, {path : ℕ → AxisState × AxisState | (path n).1 ≠ (path n).2} := by
    ext path
    simp [freePairNeverMeetPathEvent]
  rw [hrepr]
  refine MeasurableSet.iInter fun n ↦ ?_
  have hdiag :
      MeasurableSet {path : ℕ → AxisState × AxisState | (path n).1 = (path n).2} := by
    exact (measurable_pi_apply n) MeasurableSet.of_discrete
  -- Proof comment: each time slice is the complement of the diagonal singleton relation on the
  -- discrete pair state space.
  simpa [Set.setOf_app_iff] using hdiag.compl

/-- Helper for Exercise 18.2.4: apply the relative-state quotient to a free-pair trajectory
coordinatewise. -/
private def axisBlockedFreePairRelativePath
    (path : ℕ → AxisState × AxisState) : ℕ → FreePairRelativeState :=
  fun n ↦ axisBlockedFreePairRelativeState (path n)

/-- Helper for Exercise 18.2.4: the relative-path quotient is measurable because the codomain is
discrete and each coordinate depends only on one time slice. -/
private theorem measurable_axisBlockedFreePairRelativePath :
    Measurable axisBlockedFreePairRelativePath := by
  -- Proof comment: coordinatewise measurability into the discrete relative-state space upgrades to
  -- measurability of the full path-valued quotient map.
  refine measurable_pi_lambda _ fun n ↦ ?_
  exact Measurable.of_discrete.comp (measurable_pi_apply n)

/-- Helper for Exercise 18.2.4: package a relative state as the corresponding point of `ℤ^3`
recording the two horizontal coordinates and the vertical difference. -/
private abbrev freePairRelativeStateToLatticePoint3
    (r : FreePairRelativeState) : LatticePoint 3 :=
  ![r.1.1, r.1.2, r.2]

/-- Helper for Exercise 18.2.4: decoding the raw `ℤ^3` encoding recovers the original relative
state. -/
private theorem latticePoint3ToFreePairRelativeState_encode
    (r : FreePairRelativeState) :
    (((freePairRelativeStateToLatticePoint3 r 0,
        freePairRelativeStateToLatticePoint3 r 1) : AxisState),
      freePairRelativeStateToLatticePoint3 r 2) = r := by
  rcases r with ⟨⟨x, y⟩, d⟩
  -- Proof comment: the raw `ℤ^3` encoding stores exactly the two horizontal coordinates and the
  -- vertical difference, so decoding is coordinatewise inverse.
  rfl

/-- Helper for Exercise 18.2.4: the raw `ℤ^3` owner kernel is the relative owner kernel pushed
through the lattice encoding. -/
private def axisBlockedFreePairLatticeKernel :
    Kernel (LatticePoint 3) (LatticePoint 3) :=
  Kernel.ofFunOfCountable fun z ↦
    Measure.map freePairRelativeStateToLatticePoint3
      (axisBlockedFreePairRelativeKernel
        (((z 0, z 1) : AxisState), z 2))

/-- Helper for Exercise 18.2.4: the raw `ℤ^3` owner kernel is Markov because each row is the
pushforward of a probability row of the relative owner kernel. -/
private instance axisBlockedFreePairLatticeKernel_isMarkovKernel :
    IsMarkovKernel axisBlockedFreePairLatticeKernel := by
  refine ⟨fun z ↦ ?_⟩
  change IsProbabilityMeasure
    (Measure.map freePairRelativeStateToLatticePoint3
      (axisBlockedFreePairRelativeKernel
        (((z 0, z 1) : AxisState), z 2)))
  exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

/-- Helper for Exercise 18.2.4: pushing one free-pair step through the raw `ℤ^3` encoding gives
the corresponding row of the lattice owner kernel. -/
private theorem axisBlockedFreePairLatticeKernel_row_eq_pushforward
    (s : AxisState × AxisState) :
    Measure.map
        (fun t : AxisState × AxisState ↦
          freePairRelativeStateToLatticePoint3
            (axisBlockedFreePairRelativeState t))
        ((discreteMatrixKernel independentProductPairMatrix) s) =
      axisBlockedFreePairLatticeKernel
        (freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState s)) := by
  calc
    Measure.map
        (fun t : AxisState × AxisState ↦
          freePairRelativeStateToLatticePoint3
            (axisBlockedFreePairRelativeState t))
        ((discreteMatrixKernel independentProductPairMatrix) s) =
      Measure.map freePairRelativeStateToLatticePoint3
        (axisBlockedFreePairRelativeKernel
          (axisBlockedFreePairRelativeState s)) := by
            -- Proof comment: first collapse the free-pair row to the relative quotient, then
            -- apply the raw lattice encoding to that relative-state row.
            simpa [Function.comp] using
              congrArg (Measure.map freePairRelativeStateToLatticePoint3)
                (axisBlockedFreePairRelativeState_oneStepKernel (s := s))
    _ =
      axisBlockedFreePairLatticeKernel
        (freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState s)) := by
            -- Proof comment: decode the encoded present state to the same relative state used in
            -- the previous line, so the row is exactly the lattice owner-kernel row.
            rw [axisBlockedFreePairLatticeKernel,
              latticePoint3ToFreePairRelativeState_encode]

/-- Helper for Exercise 18.2.4: in the `ℤ^3` encoding, collision states form the line
`{z | z 0 = z 1 ∧ z 2 = 0}`. -/
private def axisBlockedDefectCollisionLine : Set (LatticePoint 3) :=
  {z | z 0 = z 1 ∧ z 2 = 0}

/-- Helper for Exercise 18.2.4: collapse the collision line to the origin by keeping the
horizontal difference and the vertical difference. -/
private abbrev axisBlockedDefectCollisionCode (z : LatticePoint 3) : LatticePoint 2 :=
  ![z 0 - z 1, z 2]

/-- Helper for Exercise 18.2.4: apply the collision-code quotient coordinatewise to a `ℤ^3`
defect path. -/
private def axisBlockedDefectCollisionCodePath
    (path : ℕ → LatticePoint 3) : ℕ → LatticePoint 2 :=
  fun n ↦ axisBlockedDefectCollisionCode (path n)

/-- Helper for Exercise 18.2.4: the coordinatewise collision-code quotient is measurable on path
space because the codomain is discrete. -/
private theorem measurable_axisBlockedDefectCollisionCodePath :
    Measurable axisBlockedDefectCollisionCodePath := by
  -- Proof comment: each collision-code time slice depends only on the original time-`n`
  -- coordinate and lands in the discrete space `LatticePoint 2`.
  refine measurable_pi_lambda _ fun n ↦ ?_
  exact Measurable.of_discrete.comp (measurable_pi_apply n)

/-- Helper for Exercise 18.2.4: applying the `ℤ^3` encoding coordinatewise to a free-pair
trajectory. -/
private def axisBlockedFreePairLatticePath
    (path : ℕ → AxisState × AxisState) : ℕ → LatticePoint 3 :=
  fun n ↦ freePairRelativeStateToLatticePoint3 (axisBlockedFreePairRelativePath path n)

/-- Helper for Exercise 18.2.4: the coordinatewise `ℤ^3` path encoding is measurable because its
codomain is discrete. -/
private theorem measurable_axisBlockedFreePairLatticePath :
    Measurable axisBlockedFreePairLatticePath := by
  -- Proof comment: each encoded time slice only depends on the original time-`n` coordinate and
  -- lands in a discrete lattice state space.
  refine measurable_pi_lambda _ fun n ↦ ?_
  exact Measurable.of_discrete.comp (measurable_pi_apply n)

/-- Helper for Exercise 18.2.4: the `ℤ^3` encoding sends the relative collision set exactly to the
collision line `z 0 = z 1, z 2 = 0`. -/
private theorem mem_axisBlockedDefectCollisionLine_iff
    (r : FreePairRelativeState) :
    freePairRelativeStateToLatticePoint3 r ∈ axisBlockedDefectCollisionLine ↔
      r ∈ axisBlockedFreePairCollisionSet := by
  rcases r with ⟨⟨x, y⟩, d⟩
  -- Proof comment: unpacking the encoded coordinates identifies the collision-line equations with
  -- equality of horizontal coordinates and vanishing vertical difference.
  simp [freePairRelativeStateToLatticePoint3, axisBlockedDefectCollisionLine,
    axisBlockedFreePairCollisionSet]

/-- Helper for Exercise 18.2.4: the collision line is exactly the zero fiber of the collision
code. -/
private theorem mem_axisBlockedDefectCollisionLine_iff_collisionCode_eq_zero
    {z : LatticePoint 3} :
    z ∈ axisBlockedDefectCollisionLine ↔ axisBlockedDefectCollisionCode z = 0 := by
  constructor
  · intro hz
    ext i
    fin_cases i
    · rcases hz with ⟨hxy, _⟩
      simp [axisBlockedDefectCollisionCode, hxy]
    · rcases hz with ⟨_, hz₂⟩
      simp [axisBlockedDefectCollisionCode, hz₂]
  · intro hz
    have hdiff :
        z 0 - z 1 = 0 := by
      simpa [axisBlockedDefectCollisionCode] using
        congrArg (fun v : LatticePoint 2 ↦ v 0) hz
    have hz₂ :
        z 2 = 0 := by
      simpa [axisBlockedDefectCollisionCode] using
        congrArg (fun v : LatticePoint 2 ↦ v 1) hz
    exact ⟨sub_eq_zero.mp hdiff, hz₂⟩

/-- Helper for Exercise 18.2.4: on `ℤ^3`, free-pair noncollision becomes avoidance of the encoded
collision line. -/
private def axisBlockedDefectAvoidCollisionLinePathEvent :
    Set (ℕ → LatticePoint 3) :=
  {path | ∀ n : ℕ, path n ∉ axisBlockedDefectCollisionLine}

/-- Helper for Exercise 18.2.4: the encoded collision-line avoidance event is measurable on path
space. -/
private theorem measurableSet_axisBlockedDefectAvoidCollisionLinePathEvent :
    MeasurableSet axisBlockedDefectAvoidCollisionLinePathEvent := by
  have hrepr :
      axisBlockedDefectAvoidCollisionLinePathEvent =
        ⋂ n : ℕ,
          {path : ℕ → LatticePoint 3 | path n ∉ axisBlockedDefectCollisionLine} := by
    ext path
    simp [axisBlockedDefectAvoidCollisionLinePathEvent]
  rw [hrepr]
  refine MeasurableSet.iInter fun n ↦ ?_
  have hline :
      MeasurableSet
        {path : ℕ → LatticePoint 3 | path n ∈ axisBlockedDefectCollisionLine} := by
    exact (measurable_pi_apply n) MeasurableSet.of_discrete
  -- Proof comment: each time slice of the encoded path lives in a discrete lattice space, so
  -- avoiding the collision line is the complement of a measurable membership event.
  simpa [Set.setOf_app_iff] using hline.compl

/-- Helper for Exercise 18.2.4: the relative-path collision-avoidance event records that the
quotiented path never enters the relative collision set. -/
private def axisBlockedFreePairRelativeAvoidCollisionPathEvent :
    Set (ℕ → FreePairRelativeState) :=
  {path | ∀ n : ℕ, path n ∉ axisBlockedFreePairCollisionSet}

/-- Helper for Exercise 18.2.4: the relative-path collision-avoidance event is measurable on path
space. -/
private theorem measurableSet_axisBlockedFreePairRelativeAvoidCollisionPathEvent :
    MeasurableSet axisBlockedFreePairRelativeAvoidCollisionPathEvent := by
  have hrepr :
      axisBlockedFreePairRelativeAvoidCollisionPathEvent =
        ⋂ n : ℕ,
          {path : ℕ → FreePairRelativeState | path n ∉ axisBlockedFreePairCollisionSet} := by
        ext path
        simp [axisBlockedFreePairRelativeAvoidCollisionPathEvent]
  rw [hrepr]
  refine MeasurableSet.iInter fun n ↦ ?_
  have hcollision :
      MeasurableSet
        {path : ℕ → FreePairRelativeState | path n ∈ axisBlockedFreePairCollisionSet} := by
      exact (measurable_pi_apply n) MeasurableSet.of_discrete
  -- Proof comment: each time slice is the complement of the collision-set membership event in the
  -- discrete relative-state space.
  simpa [Set.setOf_app_iff] using hcollision.compl

/-- Helper for Exercise 18.2.4: `freePairAvoidDiagonalUpToPathEvent n` records that a path stays
off the diagonal through time `n`. -/
private def freePairAvoidDiagonalUpToPathEvent (n : ℕ) :
    Set (ℕ → AxisState × AxisState) :=
  {path | ∀ m ≤ n, (path m).1 ≠ (path m).2}

/-- Helper for Exercise 18.2.4: the bounded free-pair diagonal-avoidance path event is measurable.
-/
private theorem measurableSet_freePairAvoidDiagonalUpToPathEvent (n : ℕ) :
    MeasurableSet (freePairAvoidDiagonalUpToPathEvent n) := by
  have hrepr :
      freePairAvoidDiagonalUpToPathEvent n =
        ⋂ m : ℕ,
          if m ≤ n then
            {path : ℕ → AxisState × AxisState | (path m).1 ≠ (path m).2}
          else
            Set.univ := by
    ext path
    simp [freePairAvoidDiagonalUpToPathEvent]
  rw [hrepr]
  refine MeasurableSet.iInter fun m ↦ ?_
  by_cases hm : m ≤ n
  · have hdiag :
        MeasurableSet {path : ℕ → AxisState × AxisState | (path m).1 = (path m).2} := by
      exact (measurable_pi_apply m) MeasurableSet.of_discrete
    -- Proof comment: on the active coordinates `m ≤ n`, bounded avoidance is the complement of
    -- the diagonal equality event at time `m`.
    simpa [hm, Set.setOf_app_iff] using hdiag.compl
  · simp [hm]

/-- Helper for Exercise 18.2.4: infinite diagonal avoidance is the decreasing intersection of the
bounded avoidance path events. -/
private theorem freePairNeverMeetPathEvent_eq_iInter_boundedAvoid :
    freePairNeverMeetPathEvent =
      ⋂ n : ℕ, freePairAvoidDiagonalUpToPathEvent n := by
  ext path
  constructor
  · intro hpath
    refine Set.mem_iInter.2 ?_
    intro n
    exact fun m _ ↦ hpath m
  · intro hpath n
    exact (Set.mem_iInter.1 hpath n) n le_rfl

/-- Helper for Exercise 18.2.4: diagonal avoidance of the free pair is exactly collision-set
avoidance of the relative-state quotient. -/
private theorem freePairNeverMeetEvent_eq_relativeAvoidCollisionEvent :
    {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} =
      {ω | ∀ n : ℕ,
        axisBlockedFreePairRelativeState (Xq n ω) ∉ axisBlockedFreePairCollisionSet} := by
  ext ω
  simp [mem_axisBlockedFreePairCollisionSet_iff]

/-- Helper for Exercise 18.2.4: on path space, free-pair diagonal avoidance is exactly the
preimage of relative collision avoidance under the coordinatewise quotient map. -/
private theorem freePairNeverMeetPathEvent_eq_preimage_relativeAvoidCollisionPathEvent :
    freePairNeverMeetPathEvent =
      axisBlockedFreePairRelativePath ⁻¹'
        axisBlockedFreePairRelativeAvoidCollisionPathEvent := by
  ext path
  -- Proof comment: apply the pointwise diagonal/collision equivalence at each time slice of the
  -- trajectory.
  simp [freePairNeverMeetPathEvent, axisBlockedFreePairRelativePath,
    axisBlockedFreePairRelativeAvoidCollisionPathEvent, mem_axisBlockedFreePairCollisionSet_iff]

/-- Helper for Exercise 18.2.4: after encoding the relative state as a point of `ℤ^3`, the
never-meet event is exactly avoidance of the collision line. -/
private theorem freePairNeverMeetPathEvent_eq_preimage_axisBlockedDefectAvoidCollisionLinePathEvent
    :
    freePairNeverMeetPathEvent =
      axisBlockedFreePairLatticePath ⁻¹' axisBlockedDefectAvoidCollisionLinePathEvent := by
  ext path
  -- Proof comment: encode each relative-state time slice in `ℤ^3` and rewrite collision by the
  -- dedicated collision-line equivalence.
  simp [freePairNeverMeetPathEvent, axisBlockedFreePairLatticePath,
    axisBlockedFreePairRelativePath, axisBlockedDefectAvoidCollisionLinePathEvent,
    mem_axisBlockedDefectCollisionLine_iff]

/-- Helper for Exercise 18.2.4: after encoding the relative state as a point of `ℤ^3`, bounded
diagonal avoidance is exactly bounded avoidance of the collision line. -/
private theorem
    freePairAvoidDiagonalUpToPathEvent_eq_preimage_axisBlockedDefectAvoidCollisionLineUpToPathEvent
    (n : ℕ) :
    freePairAvoidDiagonalUpToPathEvent n =
      axisBlockedFreePairLatticePath ⁻¹' axisBlockedDefectAvoidCollisionLineUpToPathEvent n := by
  ext path
  -- Proof comment: the bounded version is the same pointwise diagonal/collision rewrite applied
  -- on every time slice up to `n`.
  simp [freePairAvoidDiagonalUpToPathEvent, axisBlockedFreePairLatticePath,
    axisBlockedFreePairRelativePath, axisBlockedDefectAvoidCollisionLineUpToPathEvent,
    mem_axisBlockedDefectCollisionLine_iff]

/-- Helper for Exercise 18.2.4: the launched off-defect pair `((1,0),(1,1))` still has relative
state `((1,1),-1)`. -/
private theorem axisBlockedFreePairRelativeState_launch :
    axisBlockedFreePairRelativeState
      ((((1, 0) : AxisState), ((1, 1) : AxisState))) = (((1, 1) : AxisState), -1) := by
  -- Proof comment: after the first horizontal launch, the horizontal coordinates agree and the
  -- vertical difference is still `-1`.
  norm_num [axisBlockedFreePairRelativeState]

/-- Helper for Exercise 18.2.4: in the collision code, the launched off-defect state is the
nonzero lattice point `(0,-1)`. -/
private theorem axisBlockedDefectCollisionCode_launch :
    axisBlockedDefectCollisionCode
      (freePairRelativeStateToLatticePoint3
        (axisBlockedFreePairRelativeState
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))) = ![0, -1] := by
  -- Proof comment: first normalize the launched pair in relative coordinates, then collapse the
  -- collision line to the origin by taking horizontal and vertical differences.
  rw [axisBlockedFreePairRelativeState_launch]
  norm_num [axisBlockedDefectCollisionCode, freePairRelativeStateToLatticePoint3]

/-- Helper for Exercise 18.2.4: away from the defect set, a free-pair step cannot change the
relative vertical difference because both coordinates keep their second component fixed. -/
private theorem independentProductPairMatrix_offDefect_changeRelativeDifference_zero
    {x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂ : ℤ}
    (hx : x₁ ≠ 0) (hy : y₁ ≠ 0) (hdiff : z₂ - w₂ ≠ x₂ - y₂) :
    independentProductPairMatrix
      ((((x₁, x₂) : AxisState), ((y₁, y₂) : AxisState)))
      ((((z₁, z₂) : AxisState), ((w₁, w₂) : AxisState))) = 0 := by
  by_cases hz : z₂ = x₂
  · have hw : w₂ ≠ y₂ := by
      intro hw
      exact hdiff (by omega)
    have hright :
        vertical_axis_blocked_walk_transition_matrix (y₁, y₂) (w₁, w₂) = 0 := by
      -- Proof comment: once the first target keeps the original second coordinate, the changed
      -- relative difference forces the second target to change its own second coordinate.
      exact
        vertical_axis_blocked_walk_transition_matrix_offAxis_diffSecond_zero
          (x1 := y₁) (x2 := y₂) (y1 := w₁) (z2 := w₂) hy hw
    -- Proof comment: the independent row factors, so a vanishing second-coordinate factor kills
    -- the whole one-step mass.
    simp [independentProductPairMatrix, hright]
  · have hleft :
      vertical_axis_blocked_walk_transition_matrix (x₁, x₂) (z₁, z₂) = 0 := by
      -- Proof comment: if the first walk changes its second coordinate off the axis, the base
      -- walk row is already zero.
      exact
        vertical_axis_blocked_walk_transition_matrix_offAxis_diffSecond_zero
          (x1 := x₁) (x2 := x₂) (y1 := z₁) (z2 := z₂) hx hz
    -- Proof comment: the first factor of the product row already vanishes in this branch.
    simp [independentProductPairMatrix, hleft]

/-- Helper for Exercise 18.2.4: off the defect set, a nonzero relative vertical difference
prevents a one-step jump into the relative collision set. -/
private theorem independentProductPairMatrix_offDefect_collision_zero_of_nonzeroRelativeDifference
    {s t : AxisState × AxisState}
    (hs₁ : s.1.1 ≠ 0) (hs₂ : s.2.1 ≠ 0)
    (hdiff : (axisBlockedFreePairRelativeState s).2 ≠ 0)
    (ht : axisBlockedFreePairRelativeState t ∈ axisBlockedFreePairCollisionSet) :
    independentProductPairMatrix s t = 0 := by
  rcases s with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  rcases t with ⟨⟨z₁, z₂⟩, ⟨w₁, w₂⟩⟩
  have hsourceDiff : x₂ - y₂ ≠ 0 := by
    simpa [axisBlockedFreePairRelativeState] using hdiff
  have htarget :
      z₁ = w₁ ∧ z₂ - w₂ = 0 := by
    simpa [axisBlockedFreePairRelativeState, axisBlockedFreePairCollisionSet] using ht
  rcases htarget with ⟨_, htargetDiff⟩
  have hchange : z₂ - w₂ ≠ x₂ - y₂ := by
    intro hEq
    exact hsourceDiff (by simpa [htargetDiff] using hEq.symm)
  -- Proof comment: collision forces the target relative difference to be `0`, so the general
  -- off-defect difference-preservation lemma rules out the corresponding one-step mass.
  exact
    independentProductPairMatrix_offDefect_changeRelativeDifference_zero
      (x₁ := x₁) (x₂ := x₂) (y₁ := y₁) (y₂ := y₂)
      (z₁ := z₁) (z₂ := z₂) (w₁ := w₁) (w₂ := w₂)
      hs₁ hs₂ hchange

/-- Helper for Exercise 18.2.4: from the launched off-defect pair, the next free-pair state is
almost surely still outside the relative collision set. -/
private theorem axisBlockedFreePair_launch_oneStep_avoids_collision_ae :
    ∀ᵐ ω ∂(Pq ((((1, 0) : AxisState), ((1, 1) : AxisState))) : Measure Ωq),
      axisBlockedFreePairRelativeState (Xq 1 ω) ∉ axisBlockedFreePairCollisionSet := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq := (Pq b : Measure Ωq)
  let badSet : Set (AxisState × AxisState) :=
    {s | axisBlockedFreePairRelativeState s ∈ axisBlockedFreePairCollisionSet}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hbadKernel :
      discreteMatrixKernel independentProductPairMatrix b badSet = 0 := by
    rw [discreteMatrixKernel_apply,
      Measure.sum_apply _ (show MeasurableSet badSet from MeasurableSet.of_discrete)]
    refine ENNReal.tsum_eq_zero.mpr ?_
    intro s
    by_cases hs : s ∈ badSet
    · have hmass :
          independentProductPairMatrix b s = 0 := by
        -- Proof comment: the launched state starts off the defect set with relative difference
        -- `-1`, so the one-step collision corollary applies pointwise to every bad target.
        exact
          independentProductPairMatrix_offDefect_collision_zero_of_nonzeroRelativeDifference
            (s := b) (t := s)
            (by norm_num [b]) (by norm_num [b])
            (by simpa [b] using
              (show (axisBlockedFreePairRelativeState b).2 ≠ 0 by
                simpa [axisBlockedFreePairRelativeState, b]))
            (by simpa [badSet] using hs)
      simp [badSet, hs, hmass]
    · simp [badSet, hs]
  have hbad :
      μ {ω | axisBlockedFreePairRelativeState (Xq 1 ω) ∈ axisBlockedFreePairCollisionSet} = 0 := by
    calc
      μ {ω | axisBlockedFreePairRelativeState (Xq 1 ω) ∈ axisBlockedFreePairCollisionSet}
          = (μ.map (Xq 1)) badSet := by
              rw [show ({ω | axisBlockedFreePairRelativeState (Xq 1 ω) ∈
                  axisBlockedFreePairCollisionSet} : Set Ωq) = Xq 1 ⁻¹' badSet by
                ext ω
                simp [badSet]]
              symm
              exact Measure.map_apply (hqreal.measurable_process 1)
                (show MeasurableSet badSet from MeasurableSet.of_discrete)
      _ = discreteMatrixKernel independentProductPairMatrix b badSet := by
            exact
              congrArg
                (fun ν : Measure (AxisState × AxisState) ↦ ν badSet)
                (by simpa [pow_one, μ, b] using hqreal.transition_eq b 1)
      _ = 0 := hbadKernel
  have hgood :
      ∀ᵐ ω ∂μ,
        ω ∈ ({ω | axisBlockedFreePairRelativeState (Xq 1 ω) ∈
          axisBlockedFreePairCollisionSet} : Set Ωq)ᶜ := by
    exact compl_mem_ae_iff.2 hbad
  -- Proof comment: zero mass of the bad event upgrades directly to the almost-sure off-collision
  -- statement.
  filter_upwards [hgood] with ω hω
  simpa using hω

/-- Helper for Exercise 18.2.4: the realized free product-pair trajectory map is measurable on
path space. -/
private theorem measurable_independentProductPairTrajectoryMap :
    Measurable (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) := by
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  -- Proof comment: coordinatewise measurability of the realization upgrades to measurability of
  -- the full path-valued trajectory map.
  refine measurable_pi_lambda _ fun n ↦ ?_
  exact hqreal.measurable_process n

/-- Helper for Exercise 18.2.4: the path-law kernel of the realized free product-pair chain. -/
private def independentProductPairRealizationPathKernel :
    Kernel (AxisState × AxisState) (ℕ → AxisState × AxisState) :=
  Kernel.ofFunOfCountable fun a ↦
    Measure.map (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) (Pq a : Measure Ωq)

/-- Helper for Exercise 18.2.4: the realized free product-pair path-law rows are probability
measures. -/
private instance independentProductPairRealizationPathKernel_isMarkovKernel :
    IsMarkovKernel
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)) := by
  refine ⟨fun a ↦ ?_⟩
  change IsProbabilityMeasure
    (Measure.map (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) (Pq a : Measure Ωq))
  exact Measure.isProbabilityMeasure_map
    measurable_independentProductPairTrajectoryMap.aemeasurable

/-- Helper for Exercise 18.2.4: evaluating the free product-pair realized path-law kernel row is
just pushing `Pq a` forward along the trajectory map. -/
@[simp] private theorem independentProductPairRealizationPathKernel_apply
    (a : AxisState × AxisState) :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a =
      Measure.map (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) (Pq a : Measure Ωq) := rfl

/-- Helper for Exercise 18.2.4: under `Pq a`, the free product-pair chain starts from `a`
almost surely, written in singleton-event form. -/
private theorem independentProductPairRealizationPathKernel_initialState_prob_eq_one
    (a : AxisState × AxisState) :
    (Pq a : Measure Ωq) (Xq 0 ⁻¹' ({a} : Set (AxisState × AxisState))) = 1 := by
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  -- Proof comment: evaluate the time-zero marginal identity on the singleton `{a}`.
  have hInit :=
    congrArg (fun μ : Measure (AxisState × AxisState) ↦ μ ({a} : Set (AxisState × AxisState)))
      (hqreal.initial_eq a)
  simpa [Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton a)] using hInit

/-- Helper for Exercise 18.2.4: pushing a realized free product-pair path row forward to time `n`
recovers the `n`-step transition row of the free product-pair chain. -/
private theorem independentProductPairRealizationPathKernel_transition
    (a : AxisState × AxisState) (n : ℕ) :
    transitionKernel (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)) n a =
      (discreteMatrixKernel independentProductPairMatrix ^ n) a := by
  let hqreal :
      IsMarkovProcessRealization
        (fun m : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ m) Pq Xq :=
    inferInstance
  -- Proof comment: evaluating the path at time `n` after pushing forward along the trajectory map
  -- gives exactly the stored time-`n` marginal of the realization.
  rw [transitionKernel_apply]
  change
    Measure.map (fun y : ℕ → AxisState × AxisState ↦ y n)
      (Measure.map (fun ω : Ωq ↦ fun m : ℕ ↦ Xq m ω) (Pq a : Measure Ωq)) =
        (discreteMatrixKernel independentProductPairMatrix ^ n) a
  rw [Measure.map_map]
  · simpa using hqreal.transition_eq a n
  · exact measurable_pi_apply n
  · exact measurable_independentProductPairTrajectoryMap

/-- Helper for Exercise 18.2.4: the realized free product-pair path law upgrades the chain to the
Chapter 17 time-homogeneous path-space Markov-process API. -/
private theorem independentProductPairRealizationPathKernel_isTimeHomogeneousMarkovProcess :
    IsTimeHomogeneousMarkovProcess Xq Pq
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)) := by
  let hqreal :
      IsMarkovProcessRealization
        (fun m : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ m) Pq Xq :=
    inferInstance
  refine
    { measurable_process := hqreal.measurable_process
      initial_state :=
        independentProductPairRealizationPathKernel_initialState_prob_eq_one
          (Pq := Pq) (Xq := Xq)
      path_law := ?_
      markov_property := ?_ }
  · intro a
    rfl
  · intro a A hA s t
    -- Proof comment: rewrite the owner path-kernel transition row back to the original semigroup
    -- before invoking the stored Markov property of the realization.
    refine (hqreal.markov_property a hA s t).trans ?_
    filter_upwards with ω
    rw [independentProductPairRealizationPathKernel_transition
      (Pq := Pq) (Xq := Xq) (a := Xq s ω) t]

/-- Helper for Exercise 18.2.4: after quotienting by common vertical shifts, the relative-state
process is itself a Markov realization of the owner kernel `axisBlockedFreePairRelativeKernel`. -/
private theorem axisBlockedFreePairRelativePath_isMarkovProcessRealization :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ axisBlockedFreePairRelativeKernel ^ n)
      (fun r : FreePairRelativeState ↦ Pq (freePairRelativeStateRepresentative r))
      (fun n ω ↦ axisBlockedFreePairRelativeState (Xq n ω)) := by
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := axisBlockedFreePairRelativeKernel)
    (P := fun r : FreePairRelativeState ↦ Pq (freePairRelativeStateRepresentative r))
    (X := fun n ω ↦ axisBlockedFreePairRelativeState (Xq n ω))
    (hmeas := ?_)
    (hstart := ?_)
    (hstep := ?_)
  · intro n
    -- Proof comment: the relative-state process takes values in a countable discrete space, so
    -- coordinatewise measurability is immediate.
    exact measurable_of_countable (f := fun ω ↦ axisBlockedFreePairRelativeState (Xq n ω))
  · intro r
    calc
      (Pq (freePairRelativeStateRepresentative r) : Measure Ωq).map
          (fun ω ↦ axisBlockedFreePairRelativeState (Xq 0 ω))
          = ((Pq (freePairRelativeStateRepresentative r) : Measure Ωq).map (Xq 0)).map
              axisBlockedFreePairRelativeState := by
                rw [Measure.map_map (hqreal.measurable_process 0)
                  (measurable_of_countable (f := axisBlockedFreePairRelativeState))]
                rfl
      _ = (Measure.dirac (freePairRelativeStateRepresentative r)).map
            axisBlockedFreePairRelativeState := by
              rw [hqreal.initial_eq (freePairRelativeStateRepresentative r)]
      _ = Measure.dirac r := by
            simpa [axisBlockedFreePairRelativeState_representative]
  · intro r A hA s
    have hraw :
        (Pq (freePairRelativeStateRepresentative r))⟦Xq (s + 1) ⁻¹'
            (axisBlockedFreePairRelativeState ⁻¹' A) | generatedFiltrationSpace Xq s⟧
          =ᵐ[(Pq (freePairRelativeStateRepresentative r) : Measure Ωq)]
            fun ω ↦
              ((discreteMatrixKernel independentProductPairMatrix) (Xq s ω)).real
                (axisBlockedFreePairRelativeState ⁻¹' A) := by
      -- Proof comment: apply the original free product-pair Markov property to the preimage of
      -- `A` under the relative-state quotient.
      simpa [pow_one, Nat.add_comm] using
        hqreal.markov_property
          (freePairRelativeStateRepresentative r)
          (A := axisBlockedFreePairRelativeState ⁻¹' A)
          ((measurable_of_countable (f := axisBlockedFreePairRelativeState)) hA)
          s 1
    have hkernel :
        ∀ ω : Ωq,
          ((discreteMatrixKernel independentProductPairMatrix) (Xq s ω)).real
              (axisBlockedFreePairRelativeState ⁻¹' A) =
            (axisBlockedFreePairRelativeKernel
              (axisBlockedFreePairRelativeState (Xq s ω))).real A := by
      intro ω
      -- Proof comment: evaluate the pushed-forward one-step law on `A` and then rewrite the row
      -- by the quotient-kernel normalization theorem.
      calc
        ((discreteMatrixKernel independentProductPairMatrix) (Xq s ω)).real
            (axisBlockedFreePairRelativeState ⁻¹' A)
            = (Measure.map axisBlockedFreePairRelativeState
                ((discreteMatrixKernel independentProductPairMatrix) (Xq s ω))).real A := by
                  symm
                  exact
                    MeasureTheory.map_measureReal_apply
                      (μ := (discreteMatrixKernel independentProductPairMatrix) (Xq s ω))
                      (f := axisBlockedFreePairRelativeState)
                      (measurable_of_countable (f := axisBlockedFreePairRelativeState))
                      hA
        _ =
            (axisBlockedFreePairRelativeKernel
              (axisBlockedFreePairRelativeState (Xq s ω))).real A := by
                exact congrArg (fun μ : Measure FreePairRelativeState ↦ μ.real A)
                  (axisBlockedFreePairRelativeState_oneStepKernel (s := Xq s ω))
    -- Proof comment: the left event is the relative-state time-`s+1` fiber of `A`, and the right
    -- side is now exactly the relative owner row at the present quotient state.
    refine hraw.trans ?_
    filter_upwards with ω
    simpa [Function.comp] using hkernel ω

/-- Helper for Exercise 18.2.4: after encoding the relative state as a point of `ℤ^3`, the
encoded owner process is itself a Markov realization of `axisBlockedFreePairLatticeKernel`. -/
private theorem axisBlockedFreePairLatticeProcess_isMarkovProcessRealization :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ axisBlockedFreePairLatticeKernel ^ n)
      (fun z : LatticePoint 3 ↦
        Pq (freePairRelativeStateRepresentative (((z 0, z 1) : AxisState), z 2)))
      (fun n ω ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n) := by
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := axisBlockedFreePairLatticeKernel)
    (P := fun z : LatticePoint 3 ↦
      Pq (freePairRelativeStateRepresentative (((z 0, z 1) : AxisState), z 2)))
    (X := fun n ω ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n)
    (hmeas := ?_)
    (hstart := ?_)
    (hstep := ?_)
  · intro n
    -- Proof comment: each encoded lattice time slice lands in the countable discrete state space
    -- `ℤ^3`, so coordinatewise measurability is immediate.
    exact
      measurable_of_countable
        (f := fun ω ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n)
  · intro z
    let rep : AxisState × AxisState :=
      freePairRelativeStateRepresentative (((z 0, z 1) : AxisState), z 2)
    calc
      (Pq rep : Measure Ωq).map
          (fun ω ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 0) =
        ((Pq rep : Measure Ωq).map (Xq 0)).map
          (fun s : AxisState × AxisState ↦
            freePairRelativeStateToLatticePoint3
              (axisBlockedFreePairRelativeState s)) := by
              rw [Measure.map_map (hqreal.measurable_process 0)
                (measurable_of_countable
                  (f := fun s : AxisState × AxisState ↦
                    freePairRelativeStateToLatticePoint3
                      (axisBlockedFreePairRelativeState s)))]
              rfl
      _ =
        (Measure.dirac rep).map
          (fun s : AxisState × AxisState ↦
            freePairRelativeStateToLatticePoint3
              (axisBlockedFreePairRelativeState s)) := by
              rw [hqreal.initial_eq rep]
      _ = Measure.dirac z := by
            -- Proof comment: the chosen representative of `z` decodes back to the same lattice
            -- point under the relative-state chart.
            simp [rep, axisBlockedFreePairRelativeState_representative,
              freePairRelativeStateToLatticePoint3]
  · intro z A hA s
    let rep : AxisState × AxisState :=
      freePairRelativeStateRepresentative (((z 0, z 1) : AxisState), z 2)
    have hraw :
        (Pq rep)⟦Xq (s + 1) ⁻¹'
            ((fun t : AxisState × AxisState ↦
                freePairRelativeStateToLatticePoint3
                  (axisBlockedFreePairRelativeState t)) ⁻¹' A)
          | generatedFiltrationSpace Xq s⟧ =ᵐ[(Pq rep : Measure Ωq)]
            fun ω ↦
              ((discreteMatrixKernel independentProductPairMatrix) (Xq s ω)).real
                ((fun t : AxisState × AxisState ↦
                  freePairRelativeStateToLatticePoint3
                    (axisBlockedFreePairRelativeState t)) ⁻¹' A) := by
      -- Proof comment: apply the original free product-pair Markov property to the preimage of
      -- `A` under the encoded relative-state map.
      simpa [pow_one, Nat.add_comm] using
        hqreal.markov_property
          rep
          (A := (fun t : AxisState × AxisState ↦
            freePairRelativeStateToLatticePoint3
              (axisBlockedFreePairRelativeState t)) ⁻¹' A)
          ((measurable_of_countable
            (f := fun t : AxisState × AxisState ↦
              freePairRelativeStateToLatticePoint3
                (axisBlockedFreePairRelativeState t))) hA)
          s 1
    have hkernel :
        ∀ ω : Ωq,
          ((discreteMatrixKernel independentProductPairMatrix) (Xq s ω)).real
              ((fun t : AxisState × AxisState ↦
                freePairRelativeStateToLatticePoint3
                  (axisBlockedFreePairRelativeState t)) ⁻¹' A) =
            (axisBlockedFreePairLatticeKernel
              (axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) s)).real A := by
      intro ω
      calc
        ((discreteMatrixKernel independentProductPairMatrix) (Xq s ω)).real
            ((fun t : AxisState × AxisState ↦
                freePairRelativeStateToLatticePoint3
                  (axisBlockedFreePairRelativeState t)) ⁻¹' A) =
          (Measure.map
              (fun t : AxisState × AxisState ↦
                freePairRelativeStateToLatticePoint3
                  (axisBlockedFreePairRelativeState t))
              ((discreteMatrixKernel independentProductPairMatrix) (Xq s ω))).real A := by
                symm
                exact
                  MeasureTheory.map_measureReal_apply
                    (μ := (discreteMatrixKernel independentProductPairMatrix) (Xq s ω))
                    (f := fun t : AxisState × AxisState ↦
                      freePairRelativeStateToLatticePoint3
                        (axisBlockedFreePairRelativeState t))
                    (measurable_of_countable
                      (f := fun t : AxisState × AxisState ↦
                        freePairRelativeStateToLatticePoint3
                          (axisBlockedFreePairRelativeState t)))
                    hA
        _ =
          (axisBlockedFreePairLatticeKernel
            (axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) s)).real A := by
              have hrow :
                  Measure.map
                      (fun t : AxisState × AxisState ↦
                        freePairRelativeStateToLatticePoint3
                          (axisBlockedFreePairRelativeState t))
                      ((discreteMatrixKernel independentProductPairMatrix) (Xq s ω)) =
                    axisBlockedFreePairLatticeKernel
                      (axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) s) := by
                    simpa [axisBlockedFreePairLatticePath, axisBlockedFreePairRelativePath] using
                      axisBlockedFreePairLatticeKernel_row_eq_pushforward (s := Xq s ω)
              exact congrArg (fun μ : Measure (LatticePoint 3) ↦ μ.real A) hrow
    -- Proof comment: the time-`s+1` encoded owner event is the preimage of `A` under the encoded
    -- relative-state chart, and the one-step row has already been normalized to the lattice
    -- kernel at the present encoded state.
    refine hraw.trans ?_
    filter_upwards with ω
    simpa [Function.comp, axisBlockedFreePairLatticePath, axisBlockedFreePairRelativePath] using
      hkernel ω

/-- Helper for Exercise 18.2.4: conditioning a future-path indicator at deterministic time `n`
against the realized free product-pair path kernel gives the corresponding path-event row mass
from the present state. -/
private theorem independentProductPairFuturePathIndicator_condexp_eq_pathKernel
    {B : Set (ℕ → AxisState × AxisState)} (hB : MeasurableSet B)
    (a : AxisState × AxisState) (n : ℕ) :
    ((Pq a : Measure Ωq)[fun ω ↦
        Set.indicator B (fun _ ↦ (1 : ℝ)) (futurePath Xq n ω)
      | generatedFiltrationSpace Xq n]) =ᵐ[(Pq a : Measure Ωq)]
        fun ω ↦
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) (Xq n ω)).real B := by
  let hqreal :
      IsMarkovProcessRealization
        (fun m : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ m) Pq Xq :=
    inferInstance
  let g : (ℕ → AxisState × AxisState) → ℝ := Set.indicator B (fun _ ↦ (1 : ℝ))
  have hg_meas : Measurable g := by
    -- Proof comment: the future-path test function is the measurable indicator of `B`.
    exact Measurable.indicator measurable_const hB
  have hg_bdd : Bornology.IsBounded (Set.range g) := by
    -- Proof comment: an indicator takes only the values `0` and `1`, so its range is bounded.
    simpa [g] using isBounded_range_indicator_one B
  letI :
      IsTimeHomogeneousMarkovProcess Xq Pq
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)) :=
    independentProductPairRealizationPathKernel_isTimeHomogeneousMarkovProcess
      (Pq := Pq) (Xq := Xq)
  have hAE :=
    futurePathCondExp_of_markovProcessNat
      (X := Xq) (P := Pq)
      (κ := independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq))
      (hX_meas := hqreal.measurable_process)
      (hX0 :=
        independentProductPairRealizationPathKernel_initialState_prob_eq_one
          (Pq := Pq) (Xq := Xq))
      (hpath := independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq))
      a n g hg_meas hg_bdd
  -- Proof comment: rewrite the generic kernel integral of the indicator into the corresponding
  -- row mass of the realized path kernel.
  filter_upwards [hAE] with ω hω
  calc
    ((Pq a : Measure Ωq)[fun ω ↦
        Set.indicator B (fun _ ↦ (1 : ℝ)) (futurePath Xq n ω)
      | generatedFiltrationSpace Xq n]) ω
        = ((Pq a : Measure Ωq)[fun ω ↦ g (futurePath Xq n ω) |
            generatedFiltrationSpace Xq n]) ω := by
              rfl
    _ =
        ∫ y, g y ∂(independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) (Xq n ω)) := hω
    _ =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) (Xq n ω)).real B := by
          simpa [g] using
            (MeasureTheory.integral_indicator_one
              (μ := independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) (Xq n ω))
              (s := B) hB)

/-- Helper for Exercise 18.2.4: on a deterministic-time history event that fixes `Xq n = y`, the
future-path mass of any measurable path event factors through the realized free product-pair
path-kernel row from `y`. -/
private theorem independentProductPair_measureInter_eq_mul_futurePathMass_of_stateEvent
    (a y : AxisState × AxisState) (n : ℕ) (A : Set Ωq)
    (B : Set (ℕ → AxisState × AxisState))
    (hB_meas : MeasurableSet B)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace Xq n] A)
    (hA_state : ∀ ⦃ω : Ωq⦄, ω ∈ A → Xq n ω = y) :
    (Pq a : Measure Ωq) (A ∩ {ω | futurePath Xq n ω ∈ B}) =
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) y B) *
        (Pq a : Measure Ωq) A := by
  let μ : Measure Ωq := (Pq a : Measure Ωq)
  let hqreal :
      IsMarkovProcessRealization
        (fun m : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ m) Pq Xq :=
    inferInstance
  let futureEvent : Set Ωq := {ω | futurePath Xq n ω ∈ B}
  let rowMass : Ωq → ℝ := fun ω ↦
    (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) (Xq n ω)).real B
  have hfuture_meas : MeasurableSet futureEvent := by
    -- Proof comment: the future-path event is the measurable preimage of `B`.
    simpa [futureEvent] using (measurable_futurePath Xq hqreal.measurable_process n) hB_meas
  have hIndicatorInt :
      Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ := by
    -- Proof comment: indicators of measurable events are integrable under the probability law.
    simpa [futureEvent] using (integrable_const (1 : ℝ)).indicator hfuture_meas
  have hgenerated_le : generatedFiltrationSpace Xq n ≤ ‹MeasurableSpace Ωq› := by
    exact generatedHistory_le_ambient Xq hqreal.measurable_process n
  have hcond :
      μ[fun ω ↦ Set.indicator futureEvent (fun _ ↦ (1 : ℝ)) ω
          | generatedFiltrationSpace Xq n] =ᵐ[μ] rowMass := by
    -- Proof comment: specialize the future-path conditional-expectation bridge to `B`.
    simpa [futureEvent, rowMass] using
      independentProductPairFuturePathIndicator_condexp_eq_pathKernel
        (Pq := Pq) (Xq := Xq) hB_meas a n
  have hrowInt : Integrable rowMass μ := by
    exact (integrable_congr hcond).1 integrable_condExp
  have hslice_real :
      μ.real (A ∩ futureEvent) =
        ((independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) y).real B) *
          μ.real A := by
    calc
      μ.real (A ∩ futureEvent) =
          ∫ ω in A,
            (μ[fun ω ↦ Set.indicator futureEvent (fun _ ↦ (1 : ℝ)) ω
              | generatedFiltrationSpace Xq n]) ω ∂μ := by
              rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hA_measFiltration,
                ← MeasureTheory.integral_indicator hA_meas]
              simpa [futureEvent, Set.indicator_indicator, Set.inter_assoc,
                Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                (MeasureTheory.integral_indicator_const
                  (μ := μ) (1 : ℝ) (hA_meas.inter hfuture_meas)).symm
      _ = ∫ ω in A, rowMass ω ∂μ := by
            exact MeasureTheory.integral_congr_ae hcond.restrict
      _ = ∫ ω in A,
            ((independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) y).real B) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
      _ =
          ((independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) y).real B) *
            μ.real A := by
              rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ futureEvent) =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) y B) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by
            exact
              (measure_lt_top
                (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) y) B).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ, futureEvent] using hslice_enn

/-- Helper for Exercise 18.2.4: at the launched state `((1,0),(1,1))`, bounded path-space
diagonal avoidance agrees with the off-diagonal mass of the absorbed free-pair chain. -/
private theorem axisBlockedFreePair_launchBoundedAvoid_eq_absorbedOffDiagonalMass
    (n : ℕ) :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      ((((1, 0) : AxisState), ((1, 1) : AxisState)))
      (freePairAvoidDiagonalUpToPathEvent n) =
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq := (Pq b : Measure Ωq)
  have hpreimage :
      (fun ω : Ωq ↦ fun k : ℕ ↦ Xq k ω) ⁻¹' freePairAvoidDiagonalUpToPathEvent n =
        {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} := by
    ext ω
    simp [freePairAvoidDiagonalUpToPathEvent]
  -- Proof comment: evaluate the launched path-law row on the bounded avoidance event, rewrite the
  -- preimage under the trajectory map, and then use the absorbed/free finite-horizon identity.
  calc
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
        (freePairAvoidDiagonalUpToPathEvent n) =
        Measure.map (fun ω : Ωq ↦ fun k : ℕ ↦ Xq k ω) (Pq b : Measure Ωq)
          (freePairAvoidDiagonalUpToPathEvent n) := by
            rw [independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq) b]
    _ = (Pq b : Measure Ωq) ((fun ω : Ωq ↦ fun k : ℕ ↦ Xq k ω) ⁻¹'
          freePairAvoidDiagonalUpToPathEvent n) := by
            rw [Measure.map_apply measurable_independentProductPairTrajectoryMap
              (measurableSet_freePairAvoidDiagonalUpToPathEvent n)]
    _ = μ {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} := by
          simpa [μ, hpreimage]
    _ =
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) b)
          {s : AxisState × AxisState | s.1 ≠ s.2} := by
            simpa [b, μ] using
              (independentProductPairAbsorbDiagonal_offDiagonalMass_eq_freeAvoidDiagonalProb
                (Pq := Pq) (Xq := Xq) b n).symm

/-- Helper for Exercise 18.2.4: the launched bounded collision-line-avoidance mass on encoded
`ℤ^3` path space agrees with the off-diagonal mass of the diagonal-absorbed free-pair chain. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoidUpTo_eq_absorbedOffDiagonalMass
    (n : ℕ) :
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) =
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  -- Proof comment: rewrite the encoded bounded collision-line event back to bounded diagonal
  -- avoidance of the launched free pair, then use the absorbed off-diagonal normalization.
  calc
    Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
        (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) =
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
        (axisBlockedFreePairLatticePath ⁻¹'
          axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
            rw [Measure.map_apply measurable_axisBlockedFreePairLatticePath
              (measurableSet_axisBlockedDefectAvoidCollisionLineUpToPathEvent n)]
    _ =
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
        (freePairAvoidDiagonalUpToPathEvent n) := by
          rw [←
            freePairAvoidDiagonalUpToPathEvent_eq_preimage_axisBlockedDefectAvoidCollisionLineUpToPathEvent]
    _ =
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) b)
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
          simpa [b] using
            axisBlockedFreePair_launchBoundedAvoid_eq_absorbedOffDiagonalMass
              (Pq := Pq) (Xq := Xq) n

/-- Helper for Exercise 18.2.4: continuity from above rewrites the launched never-meet path-law
mass as the limit of the bounded launched diagonal-avoidance masses. -/
private theorem axisBlockedFreePair_launchPathKernel_tendsto_neverMeet :
    Tendsto
      (fun n : ℕ ↦
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          (freePairAvoidDiagonalUpToPathEvent n))
      atTop
      (nhds
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent)) := by
  let κ := independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  have hAnti : Antitone freePairAvoidDiagonalUpToPathEvent := by
    intro n m hnm path hpath k hk
    exact hpath k (le_trans hk hnm)
  have hInter :
      (⋂ n : ℕ, freePairAvoidDiagonalUpToPathEvent n) = freePairNeverMeetPathEvent := by
    exact freePairNeverMeetPathEvent_eq_iInter_boundedAvoid.symm
  have hlimit :
      Tendsto
        (fun n ↦ κ b (freePairAvoidDiagonalUpToPathEvent n))
        atTop
        (nhds (κ b (⋂ n : ℕ, freePairAvoidDiagonalUpToPathEvent n))) := by
    -- Proof comment: the bounded avoidance events decrease to the never-meet event, so the
    -- launched path-law row is continuous from above along that sequence.
    exact
      tendsto_measure_iInter_atTop
        (μ := κ b)
        (s := freePairAvoidDiagonalUpToPathEvent)
        (fun n ↦ (measurableSet_freePairAvoidDiagonalUpToPathEvent n).nullMeasurableSet)
        hAnti
        ⟨0, measure_ne_top _ _⟩
  simpa [κ, b, hInter] using hlimit

/-- Helper for Exercise 18.2.4: for any start pair, continuity from above rewrites the
never-meet path-law mass as the limit of the bounded diagonal-avoidance masses. -/
private theorem independentProductPairPathKernel_tendsto_neverMeet
    (a : AxisState × AxisState) :
    Tendsto
      (fun n : ℕ ↦
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          a (freePairAvoidDiagonalUpToPathEvent n))
      atTop
      (nhds
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          a freePairNeverMeetPathEvent)) := by
  let κ := independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
  have hAnti : Antitone freePairAvoidDiagonalUpToPathEvent := by
    intro n m hnm path hpath k hk
    exact hpath k (le_trans hk hnm)
  have hInter :
      (⋂ n : ℕ, freePairAvoidDiagonalUpToPathEvent n) = freePairNeverMeetPathEvent := by
    exact freePairNeverMeetPathEvent_eq_iInter_boundedAvoid.symm
  have hlimit :
      Tendsto
        (fun n ↦ κ a (freePairAvoidDiagonalUpToPathEvent n))
        atTop
        (nhds (κ a (⋂ n : ℕ, freePairAvoidDiagonalUpToPathEvent n))) := by
    -- Proof comment: the bounded avoidance events decrease to the never-meet event for every
    -- start pair, so every path-kernel row is continuous from above along the same family.
    exact
      tendsto_measure_iInter_atTop
        (μ := κ a)
        (s := freePairAvoidDiagonalUpToPathEvent)
        (fun n ↦ (measurableSet_freePairAvoidDiagonalUpToPathEvent n).nullMeasurableSet)
        hAnti
        ⟨0, measure_ne_top _ _⟩
  simpa [κ, hInter] using hlimit

/-- Helper for Exercise 18.2.4: the launched never-meet path event has the same mass under the
realized path-kernel row as under the launched realization measure. -/
private theorem axisBlockedFreePair_launchPathKernel_neverMeet_eq_measure :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      ((((1, 0) : AxisState), ((1, 1) : AxisState)))
      freePairNeverMeetPathEvent =
      (Pq ((((1, 0) : AxisState), ((1, 1) : AxisState))) : Measure Ωq)
        {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  have hpreimage :
      (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) ⁻¹' freePairNeverMeetPathEvent =
        {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
    ext ω
    simp [freePairNeverMeetPathEvent]
  -- Proof comment: unfold the launched path-kernel row as a pushforward of `Pq b`, then rewrite
  -- the preimage of the path event back to the pointwise never-meet event on `Ωq`.
  calc
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b freePairNeverMeetPathEvent =
        Measure.map (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) (Pq b : Measure Ωq)
          freePairNeverMeetPathEvent := by
            rw [independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq) b]
    _ = (Pq b : Measure Ωq)
          ((fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) ⁻¹' freePairNeverMeetPathEvent) := by
            rw [Measure.map_apply measurable_independentProductPairTrajectoryMap
              measurableSet_freePairNeverMeetPathEvent]
    _ =
        (Pq b : Measure Ωq) {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
          simpa [hpreimage]

/-- Helper for Exercise 18.2.4: the launched never-meet mass is exactly the mass of the encoded
`ℤ^3` path law on the collision-line avoidance event. -/
private theorem axisBlockedFreePair_launchPathKernel_neverMeet_eq_latticeCollisionLineAvoid :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      ((((1, 0) : AxisState), ((1, 1) : AxisState)))
      freePairNeverMeetPathEvent =
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  -- Proof comment: rewrite the never-meet event as the preimage of encoded collision-line
  -- avoidance and then absorb that preimage into the pushforward measure.
  calc
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
        freePairNeverMeetPathEvent =
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
          (axisBlockedFreePairLatticePath ⁻¹'
            axisBlockedDefectAvoidCollisionLinePathEvent) := by
              rw [freePairNeverMeetPathEvent_eq_preimage_axisBlockedDefectAvoidCollisionLinePathEvent]
    _ =
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
          axisBlockedDefectAvoidCollisionLinePathEvent := by
            symm
            rw [Measure.map_apply measurable_axisBlockedFreePairLatticePath
              measurableSet_axisBlockedDefectAvoidCollisionLinePathEvent]

/-- Helper for Exercise 18.2.4: the auxiliary defect-chain no-hit event is the path-space event
that the collision-code trajectory never visits `0`. -/
private def axisBlockedDefectNoHitPathEvent : Set (ℕ → LatticePoint 2) :=
  {path | ∀ n : ℕ, path n ≠ 0}

/-- Helper for Exercise 18.2.4: the auxiliary defect-chain no-hit event is measurable on path
space. -/
private theorem measurableSet_axisBlockedDefectNoHitPathEvent :
    MeasurableSet axisBlockedDefectNoHitPathEvent := by
  have hrepr :
      axisBlockedDefectNoHitPathEvent =
        ⋂ n : ℕ, {path : ℕ → LatticePoint 2 | path n ≠ 0} := by
    ext path
    simp [axisBlockedDefectNoHitPathEvent]
  rw [hrepr]
  refine MeasurableSet.iInter fun n ↦ ?_
  have hzero :
      MeasurableSet {path : ℕ → LatticePoint 2 | path n = 0} := by
    exact (measurable_pi_apply n) MeasurableSet.of_discrete
  -- Proof comment: each time slice of the defect chain lives in a discrete lattice state space,
  -- so avoiding the collision code `0` is the complement of a singleton event.
  simpa [Set.setOf_app_iff] using hzero.compl

/-- Helper for Exercise 18.2.4: after collapsing the collision line to the origin, the never-meet
event is exactly the preimage of the collision-code no-hit event. -/
private theorem freePairNeverMeetPathEvent_eq_preimage_axisBlockedDefectNoHitPathEvent :
    freePairNeverMeetPathEvent =
      (axisBlockedDefectCollisionCodePath ∘ axisBlockedFreePairLatticePath) ⁻¹'
        axisBlockedDefectNoHitPathEvent := by
  ext path
  -- Proof comment: the `ℤ^3` collision-line avoidance event becomes pointwise nonvanishing of the
  -- collision code by `mem_axisBlockedDefectCollisionLine_iff_collisionCode_eq_zero`.
  simp [freePairNeverMeetPathEvent, axisBlockedDefectCollisionCodePath,
    axisBlockedFreePairLatticePath, axisBlockedDefectNoHitPathEvent,
    mem_axisBlockedDefectCollisionLine_iff_collisionCode_eq_zero]

/-- Helper for Exercise 18.2.4: the collision-code owner path is obtained by applying the
`ℤ^3` defect encoding and then collapsing the collision line to the origin coordinatewise. -/
private def axisBlockedFreePairCollisionCodePath
    (path : ℕ → AxisState × AxisState) : ℕ → LatticePoint 2 :=
  axisBlockedDefectCollisionCodePath (axisBlockedFreePairLatticePath path)

/-- Helper for Exercise 18.2.4: the free-pair collision-code path map is measurable on path space.
-/
private theorem measurable_axisBlockedFreePairCollisionCodePath :
    Measurable axisBlockedFreePairCollisionCodePath := by
  -- Proof comment: this is just the composition of the measurable `ℤ^3` path encoding with the
  -- measurable collision-code quotient.
  exact measurable_axisBlockedDefectCollisionCodePath.comp
    measurable_axisBlockedFreePairLatticePath

/-- Helper for Exercise 18.2.4: the never-meet event is the preimage of the collision-code no-hit
event under the direct free-pair collision-code path map. -/
private theorem freePairNeverMeetPathEvent_eq_preimage_axisBlockedFreePairCollisionCodePath :
    freePairNeverMeetPathEvent =
      axisBlockedFreePairCollisionCodePath ⁻¹' axisBlockedDefectNoHitPathEvent := by
  -- Proof comment: this is the earlier collision-code preimage description rewritten through the
  -- named owner path map.
  simpa [axisBlockedFreePairCollisionCodePath] using
    freePairNeverMeetPathEvent_eq_preimage_axisBlockedDefectNoHitPathEvent

/-- Helper for Exercise 18.2.4: evaluating the launched path-law row on the never-meet event is
the same as evaluating its collision-code pushforward on the no-hit event. -/
private theorem axisBlockedFreePair_launchPathKernel_neverMeet_eq_collisionCodeNoHitMass :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      ((((1, 0) : AxisState), ((1, 1) : AxisState)))
      freePairNeverMeetPathEvent =
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  -- Proof comment: rewrite the never-meet event as one preimage under the collision-code owner
  -- path map, then absorb that preimage into the pushforward measure.
  calc
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
        freePairNeverMeetPathEvent =
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
          (axisBlockedFreePairCollisionCodePath ⁻¹' axisBlockedDefectNoHitPathEvent) := by
            rw [freePairNeverMeetPathEvent_eq_preimage_axisBlockedFreePairCollisionCodePath]
    _ =
        Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
          axisBlockedDefectNoHitPathEvent := by
            symm
            rw [Measure.map_apply measurable_axisBlockedFreePairCollisionCodePath
              measurableSet_axisBlockedDefectNoHitPathEvent]

/-- Helper for Exercise 18.2.4: evaluating the launched path-law row on the never-meet event is
the same as evaluating its relative-path pushforward on the relative collision-avoidance event. -/
private theorem axisBlockedFreePair_launchPathKernel_neverMeet_eq_relativeAvoidCollisionMass :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      ((((1, 0) : AxisState), ((1, 1) : AxisState)))
      freePairNeverMeetPathEvent =
      Measure.map axisBlockedFreePairRelativePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedFreePairRelativeAvoidCollisionPathEvent := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  -- Proof comment: rewrite the never-meet event as one relative-path preimage, then absorb that
  -- preimage into the corresponding pushforward measure on relative path space.
  calc
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
        freePairNeverMeetPathEvent =
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
          (axisBlockedFreePairRelativePath ⁻¹'
            axisBlockedFreePairRelativeAvoidCollisionPathEvent) := by
              rw [freePairNeverMeetPathEvent_eq_preimage_relativeAvoidCollisionPathEvent]
    _ =
        Measure.map axisBlockedFreePairRelativePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
          axisBlockedFreePairRelativeAvoidCollisionPathEvent := by
            symm
            rw [Measure.map_apply measurable_axisBlockedFreePairRelativePath
              measurableSet_axisBlockedFreePairRelativeAvoidCollisionPathEvent]

/-- Helper for Exercise 18.2.4: a fixed defect path staying at the constant nonzero lattice point
`1` belongs to the no-hit event. -/
private def axisBlockedDefectSafePath : ℕ → LatticePoint 2 :=
  fun _ _ ↦ 1

/-- Helper for Exercise 18.2.4: the constant zero defect path lies outside the no-hit event. -/
private def axisBlockedDefectCollisionPath : ℕ → LatticePoint 2 :=
  fun _ ↦ 0

/-- Helper for Exercise 18.2.4: the constant nonzero defect path avoids the collision code `0`
at every time. -/
private theorem axisBlockedDefectSafePath_mem_noHitPathEvent :
    axisBlockedDefectSafePath ∈ axisBlockedDefectNoHitPathEvent := by
  intro n hzero
  have hcoord :
      axisBlockedDefectSafePath n (0 : Fin 2) = (0 : LatticePoint 2) (0 : Fin 2) := by
    simpa using congrArg (fun x : LatticePoint 2 ↦ x (0 : Fin 2)) hzero
  norm_num at hcoord

/-- Helper for Exercise 18.2.4: the constant zero defect path hits the collision code immediately.
-/
private theorem axisBlockedDefectCollisionPath_not_mem_noHitPathEvent :
    axisBlockedDefectCollisionPath ∉ axisBlockedDefectNoHitPathEvent := by
  intro hpath
  exact hpath 0 rfl

/-- Helper for Exercise 18.2.4: the Bernoulli mixture of the safe defect path and the collision
path is a probability measure whenever the safe-path weight lies in `[0, 1]`. -/
private theorem axisBlockedDefectDiracMixture_isProbabilityMeasure
    (r : ℝ≥0∞) (hr : r ≤ 1) :
    IsProbabilityMeasure
      (r • Measure.dirac axisBlockedDefectSafePath +
        (1 - r) • Measure.dirac axisBlockedDefectCollisionPath) := by
  refine ⟨?_⟩
  -- Proof comment: the two Dirac masses already have total mass `1`, so the mixture is
  -- normalized exactly by the weight identity `r + (1 - r) = 1`.
  rw [Measure.add_apply]
  · rw [Measure.smul_apply, Measure.smul_apply]
    simp [tsub_add_cancel_of_le hr]
  · exact measurableSet_univ

/-- Helper for Exercise 18.2.4: the same Bernoulli mixture charges the defect no-hit event by
exactly its safe-path weight. -/
private theorem axisBlockedDefectDiracMixture_noHitMass
    (r : ℝ≥0∞) (hr : r ≤ 1) :
    (r • Measure.dirac axisBlockedDefectSafePath +
      (1 - r) • Measure.dirac axisBlockedDefectCollisionPath)
      axisBlockedDefectNoHitPathEvent = r := by
  -- Proof comment: the no-hit event contains the safe path and excludes the zero path, so the
  -- event mass is exactly the coefficient of the safe Dirac mass.
  rw [Measure.add_apply]
  · rw [Measure.smul_apply, Measure.smul_apply]
    simp [measurableSet_axisBlockedDefectNoHitPathEvent,
      axisBlockedDefectSafePath_mem_noHitPathEvent,
      axisBlockedDefectCollisionPath_not_mem_noHitPathEvent, hr]
  · exact measurableSet_axisBlockedDefectNoHitPathEvent

/-- Helper for Exercise 18.2.4: any positive target mass `r ≤ 1` can be realized as the no-hit
mass of an explicit probability measure on defect paths. -/
private theorem axisBlockedDefectNoHitWitness_of_pos
    {r : ℝ≥0∞} (hr_pos : 0 < r) (hr_le : r ≤ 1) :
    ∃ ν : ProbabilityMeasure (ℕ → LatticePoint 2),
      0 < (ν : Measure (ℕ → LatticePoint 2)) axisBlockedDefectNoHitPathEvent ∧
      (ν : Measure (ℕ → LatticePoint 2)) axisBlockedDefectNoHitPathEvent = r := by
  let μ : Measure (ℕ → LatticePoint 2) :=
    r • Measure.dirac axisBlockedDefectSafePath +
      (1 - r) • Measure.dirac axisBlockedDefectCollisionPath
  have hμ : IsProbabilityMeasure μ :=
    axisBlockedDefectDiracMixture_isProbabilityMeasure r hr_le
  have hmass : μ axisBlockedDefectNoHitPathEvent = r :=
    axisBlockedDefectDiracMixture_noHitMass r hr_le
  refine ⟨⟨μ, hμ⟩, ?_, ?_⟩
  · -- Proof comment: the event mass is the prescribed positive weight `r`.
    simpa [μ, hmass] using hr_pos
  · -- Proof comment: the same identity packages the exact event mass of the witness measure.
    simpa [μ] using hmass

/-- Helper for Exercise 18.2.4: every launched absorbed off-diagonal mass dominates the launched
never-meet path-kernel mass, because infinite diagonal avoidance implies bounded diagonal
avoidance at each horizon. -/
private theorem axisBlockedFreePair_launchNeverMeetMass_le_absorbedOffDiagonalMass
    (n : ℕ) :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      ((((1, 0) : AxisState), ((1, 1) : AxisState)))
      freePairNeverMeetPathEvent ≤
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq := (Pq b : Measure Ωq)
  have hnever_eq :
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b freePairNeverMeetPathEvent =
        μ {ω | ∀ k : ℕ, (Xq k ω).1 ≠ (Xq k ω).2} := by
    simpa [b, μ] using
      axisBlockedFreePair_launchPathKernel_neverMeet_eq_measure (Pq := Pq) (Xq := Xq)
  have hbounded_eq :
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) b)
          {s : AxisState × AxisState | s.1 ≠ s.2} =
        μ {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2} := by
    simpa [b, μ] using
      independentProductPairAbsorbDiagonal_offDiagonalMass_eq_freeAvoidDiagonalProb
        (Pq := Pq) (Xq := Xq) b n
  -- Proof comment: the infinite never-meet event is contained in every bounded avoidance event,
  -- so the corresponding launched masses are monotone in the expected direction.
  rw [hnever_eq, hbounded_eq]
  refine measure_mono ?_
  intro ω hω m hm
  exact hω m

/-- Helper for Exercise 18.2.4: after one absorbed step from the launched pair, the remaining
off-diagonal mass dominates the corresponding start-pair mass scaled by the one-step return mass
to `((0,0),(0,1))`. -/
private theorem axisBlockedFreePair_launchAbsorbedOffDiagonalMass_ge_startPairMass
    (n : ℕ) :
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ (n + 1))
      ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      {s : AxisState × AxisState | s.1 ≠ s.2} ≥
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        ({((((0, 0) : AxisState), ((0, 1) : AxisState)))} : Set (AxisState × AxisState))) *
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
        ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  let offDiag : Set (AxisState × AxisState) := {s : AxisState × AxisState | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  -- Proof comment: expand the absorbed `(n + 1)`-step row as one absorbed step from `b`
  -- followed by an `n`-step row, then keep only the singleton contribution from the start pair.
  calc
    ((κAbs ^ (n + 1)) b) offDiag
        = ∫⁻ c, ((κAbs ^ n) c) offDiag ∂(κAbs b) := by
            rw [Kernel.pow_succ_apply_eq_lintegral κAbs n b hoffDiag_meas]
    _ =
        ∑' c : AxisState × AxisState,
          ((κAbs ^ n) c) offDiag * (κAbs b) ({c} : Set (AxisState × AxisState)) := by
            simpa [mul_comm] using
              (MeasureTheory.lintegral_countable'
                (μ := κAbs b)
                (f := fun c : AxisState × AxisState ↦ ((κAbs ^ n) c) offDiag))
    _ ≥ ((κAbs ^ n) a) offDiag * (κAbs b) ({a} : Set (AxisState × AxisState)) := by
          exact ENNReal.le_tsum a
    _ =
        (discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix b
          ({a} : Set (AxisState × AxisState))) *
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a) offDiag := by
          rw [mul_comm]
    _ =
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          ({((((0, 0) : AxisState), ((0, 1) : AxisState)))} : Set (AxisState × AxisState))) *
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
          {s : AxisState × AxisState | s.1 ≠ s.2} := by
            simp [κAbs, a, b, offDiag]

/-- Helper for Exercise 18.2.4: after one absorbed step from the start pair, the remaining
off-diagonal mass dominates the corresponding launched mass scaled by the one-step launch mass to
`((1,0),(1,1))`. -/
private theorem axisBlockedFreePair_startAbsorbedOffDiagonalMass_ge_launchMass
    (n : ℕ) :
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ (n + 1))
      ((((0, 0) : AxisState), ((0, 1) : AxisState))))
      {s : AxisState × AxisState | s.1 ≠ s.2} ≥
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        ({((((1, 0) : AxisState), ((1, 1) : AxisState)))} : Set (AxisState × AxisState))) *
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  let offDiag : Set (AxisState × AxisState) := {s : AxisState × AxisState | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  -- Proof comment: expand the absorbed `(n + 1)`-step row as one absorbed step from the start
  -- pair `a`, then keep only the singleton contribution from the launched state `b`.
  calc
    ((κAbs ^ (n + 1)) a) offDiag
        = ∫⁻ c, ((κAbs ^ n) c) offDiag ∂(κAbs a) := by
            rw [Kernel.pow_succ_apply_eq_lintegral κAbs n a hoffDiag_meas]
    _ =
        ∑' c : AxisState × AxisState,
          ((κAbs ^ n) c) offDiag * (κAbs a) ({c} : Set (AxisState × AxisState)) := by
            simpa [mul_comm] using
              (MeasureTheory.lintegral_countable'
                (μ := κAbs a)
                (f := fun c : AxisState × AxisState ↦ ((κAbs ^ n) c) offDiag))
    _ ≥ ((κAbs ^ n) b) offDiag * (κAbs a) ({b} : Set (AxisState × AxisState)) := by
          exact ENNReal.le_tsum b
    _ =
        (discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix a
          ({b} : Set (AxisState × AxisState))) *
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) b) offDiag := by
          rw [mul_comm]
    _ =
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
          ({((((1, 0) : AxisState), ((1, 1) : AxisState)))} : Set (AxisState × AxisState))) *
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          {s : AxisState × AxisState | s.1 ≠ s.2} := by
            simp [κAbs, a, b, offDiag]

/-- Helper for Exercise 18.2.4: once the launched never-meet path-kernel mass is known to be
positive, the launched absorbed off-diagonal masses cannot converge to `0`. -/
private theorem axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_of_launchNeverMeetPos
    (hnever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent) :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq := (Pq b : Measure Ωq)
  have habsorbed_fun :
      (fun n : ℕ ↦
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) b)
          {s : AxisState × AxisState | s.1 ≠ s.2}) =
        (fun n : ℕ ↦ μ {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2}) := by
    funext n
    simpa [b, μ] using
      independentProductPairAbsorbDiagonal_offDiagonalMass_eq_freeAvoidDiagonalProb
        (Pq := Pq) (Xq := Xq) b n
  have hnever_measure :
      0 < μ {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
    rw [← axisBlockedFreePair_launchPathKernel_neverMeet_eq_measure (Pq := Pq) (Xq := Xq)]
    simpa [b] using hnever
  -- Proof comment: rewrite the absorbed masses as bounded avoidance probabilities under the
  -- launched realization measure and apply the generic monotonicity contradiction lemma.
  simpa [habsorbed_fun, b, μ] using
    not_tendsto_zero_of_neverMeetProb_pos (μ := μ) (Xq := Xq) hnever_measure

/-- Helper for Exercise 18.2.4: if the launched absorbed off-diagonal masses do not vanish, then
the launched never-meet path-kernel mass is strictly positive. -/
private theorem axisBlockedFreePair_launchNeverMeet_pos_of_absorbedOffDiagonalNotTendstoZero
    (htail :
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0)) :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let κ : ℝ≥0∞ :=
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
      freePairNeverMeetPathEvent
  let boundedAvoid : ℕ → ℝ≥0∞ := fun n ↦
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
      (freePairAvoidDiagonalUpToPathEvent n)
  let absorbedMass : ℕ → ℝ≥0∞ := fun n ↦
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) b)
      {s : AxisState × AxisState | s.1 ≠ s.2}
  have habsorbed_eq :
      absorbedMass = boundedAvoid := by
    funext n
    -- Proof comment: the absorbed-chain off-diagonal mass is exactly the bounded free
    -- diagonal-avoidance mass from the launched state.
    simpa [absorbedMass, boundedAvoid, b] using
      (axisBlockedFreePair_launchBoundedAvoid_eq_absorbedOffDiagonalMass
        (Pq := Pq) (Xq := Xq) n).symm
  have hbounded_tendsto :
      Filter.Tendsto boundedAvoid Filter.atTop (nhds κ) := by
    -- Proof comment: continuity from above identifies the limit of the decreasing bounded
    -- avoidance masses with the infinite never-meet mass.
    simpa [boundedAvoid, κ, b] using
      axisBlockedFreePair_launchPathKernel_tendsto_neverMeet (Pq := Pq) (Xq := Xq)
  by_contra hκ_pos
  have hκ_zero : κ = 0 := by
    exact le_antisymm (le_of_not_gt hκ_pos) bot_le
  have hbounded_zero :
      Filter.Tendsto boundedAvoid Filter.atTop (nhds 0) := by
    simpa [hκ_zero] using hbounded_tendsto
  have habsorbed_zero :
      Filter.Tendsto absorbedMass Filter.atTop (nhds 0) := by
    rw [habsorbed_eq]
    exact hbounded_zero
  -- Proof comment: if the launch-row never-meet mass were `0`, continuity from above would force
  -- the absorbed off-diagonal tail to converge to `0`, contradicting the assumed non-vanishing.
  exact htail habsorbed_zero

/-- Helper for Exercise 18.2.4: exact non-vanishing of the absorbed off-diagonal tail forces
strict positivity of the full never-meet path-kernel mass for any start pair. -/
private theorem
    independentProductPairPathKernel_neverMeet_pos_of_absorbedOffDiagonalNotTendstoZero
    (a : AxisState × AxisState)
    (htail :
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a)
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0)) :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        a freePairNeverMeetPathEvent := by
  let κ : ℝ≥0∞ :=
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
      freePairNeverMeetPathEvent
  let boundedAvoid : ℕ → ℝ≥0∞ := fun n ↦
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
      (freePairAvoidDiagonalUpToPathEvent n)
  let absorbedMass : ℕ → ℝ≥0∞ := fun n ↦
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a)
      {s : AxisState × AxisState | s.1 ≠ s.2}
  have habsorbed_eq :
      absorbedMass = boundedAvoid := by
    funext n
    -- Proof comment: the absorbed-chain off-diagonal mass is exactly the bounded free
    -- diagonal-avoidance mass from the chosen start pair `a`.
    simpa [absorbedMass, boundedAvoid] using
      (independentProductPairAbsorbDiagonal_offDiagonalMass_eq_freeAvoidDiagonalProb
        (Pq := Pq) (Xq := Xq) a n).symm
  have hbounded_tendsto :
      Filter.Tendsto boundedAvoid Filter.atTop (nhds κ) := by
    -- Proof comment: the generic continuity-from-above lemma identifies the limit of the
    -- decreasing bounded avoidance masses with the infinite never-meet mass.
    simpa [boundedAvoid, κ] using
      independentProductPairPathKernel_tendsto_neverMeet
        (Pq := Pq) (Xq := Xq) a
  by_contra hκ_pos
  have hκ_zero : κ = 0 := by
    exact le_antisymm (le_of_not_gt hκ_pos) bot_le
  have hbounded_zero :
      Filter.Tendsto boundedAvoid Filter.atTop (nhds 0) := by
    simpa [hκ_zero] using hbounded_tendsto
  have habsorbed_zero :
      Filter.Tendsto absorbedMass Filter.atTop (nhds 0) := by
    rw [habsorbed_eq]
    exact hbounded_zero
  -- Proof comment: if the infinite-horizon never-meet mass vanished, continuity from above would
  -- force the absorbed off-diagonal tail to vanish as well, contradicting the hypothesis.
  exact htail habsorbed_zero

/-- Helper for Exercise 18.2.4: for the launched pair, positive infinite-horizon avoidance is
equivalent to non-vanishing absorbed off-diagonal mass. -/
private theorem axisBlockedFreePair_launchNeverMeet_pos_iff_absorbedOffDiagonalNotTendstoZero :
    (0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent) ↔
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0)) := by
  constructor
  · -- Proof comment: positive launch-state never-meet mass forces a uniform positive lower bound
    -- on all bounded avoidance masses, so the absorbed off-diagonal tail cannot vanish.
    intro hnever
    exact
      axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_of_launchNeverMeetPos
        (Pq := Pq) (Xq := Xq) hnever
  · -- Proof comment: conversely, if the absorbed off-diagonal tail does not vanish, continuity
    -- from above identifies a strictly positive infinite-horizon never-meet mass.
    intro htail
    exact
      axisBlockedFreePair_launchNeverMeet_pos_of_absorbedOffDiagonalNotTendstoZero
        (Pq := Pq) (Xq := Xq) htail

/-- Helper for Exercise 18.2.4: any direct non-vanishing theorem for the launched absorbed
off-diagonal masses upgrades immediately to positivity of the launched `ℤ^3` collision-line
avoidance event. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_absorbedOffDiagonalNotTendstoZero
    (htail :
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0)) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  have hnever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
    exact
      axisBlockedFreePair_launchNeverMeet_pos_of_absorbedOffDiagonalNotTendstoZero
        (Pq := Pq) (Xq := Xq) htail
  -- Proof comment: the launched never-meet row is exactly the encoded `ℤ^3` collision-line
  -- avoidance mass under the owner path map.
  rwa [axisBlockedFreePair_launchPathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (Pq := Pq) (Xq := Xq)] at hnever

/-- Helper for Exercise 18.2.4: the launched pair normalizes to the distinguished `ℤ^3` owner
point `![1, 1, -1]`. -/
private theorem axisBlockedFreePairLatticePoint_launch :
    freePairRelativeStateToLatticePoint3
      (axisBlockedFreePairRelativeState
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))) = ![1, 1, -1] := by
  -- Proof comment: first rewrite the launched pair into relative coordinates, then expand the
  -- canonical `ℤ^3` encoding of that relative state.
  rw [axisBlockedFreePairRelativeState_launch]
  norm_num [freePairRelativeStateToLatticePoint3]

/-- Helper for Exercise 18.2.4: the truthful two-right pair normalizes to the owner point
`![2, 2, -1]`. -/
private theorem axisBlockedFreePairLatticePoint_twoRight :
    freePairRelativeStateToLatticePoint3
      (axisBlockedFreePairRelativeState
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))) = ![2, 2, -1] := by
  -- Proof comment: as for the launched row, expanding the relative-state encoding of the
  -- explicit two-right pair gives the normalized owner point directly.
  norm_num [freePairRelativeStateToLatticePoint3, axisBlockedFreePairRelativeState]

/-- Helper for Exercise 18.2.4: the launched `ℤ^3` path law starts from the normalized owner
point `![1, 1, -1]` with probability `1`. -/
private theorem axisBlockedFreePair_launchLatticePath_initialPoint_prob_eq_one :
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      {path : ℕ → LatticePoint 3 | path 0 = ![1, 1, -1]} = 1 := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq := (Pq b : Measure Ωq)
  let E : Set (ℕ → LatticePoint 3) := {path | path 0 = ![1, 1, -1]}
  let F : Set Ωq :=
    (fun ω : Ωq ↦ axisBlockedFreePairLatticePath (fun n : ℕ ↦ Xq n ω)) ⁻¹' E
  have hE_meas : MeasurableSet E := by
    rw [show E = (fun path : ℕ → LatticePoint 3 ↦ path 0) ⁻¹' ({![1, 1, -1]} : Set (LatticePoint 3))
      by
        ext path
        simp [E]]
    exact (measurable_pi_apply 0) (measurableSet_singleton ![1, 1, -1])
  have hstart_subset :
      Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) ⊆ F := by
    intro ω hω
    simp only [F, E, Set.mem_preimage, Set.mem_setOf_eq]
    simpa [axisBlockedFreePairLatticePath, hω, b] using
      axisBlockedFreePairLatticePoint_launch
  have hstart_mass :
      μ (Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState))) = 1 := by
    simpa [μ, b] using
      independentProductPairRealizationPathKernel_initialState_prob_eq_one
        (Pq := Pq) (Xq := Xq) b
  have hF_eq_one : μ F = 1 := by
    refine le_antisymm ?_ ?_
    · calc
        μ F ≤ μ Set.univ := measure_mono (by intro ω hω; simp)
        _ = 1 := by simp [μ]
    · calc
        1 = μ (Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState))) := hstart_mass.symm
        _ ≤ μ F := measure_mono hstart_subset
  -- Proof comment: rewrite the pushed-forward path law back to the canonical launched realization
  -- on `Ωq`, then use the deterministic time-zero start state.
  calc
    Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b) E =
      Measure.map
        (fun ω : Ωq ↦ axisBlockedFreePairLatticePath (fun n : ℕ ↦ Xq n ω))
        μ E := by
          rw [independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq) b]
          rw [Measure.map_map measurable_independentProductPairTrajectoryMap
            measurable_axisBlockedFreePairLatticePath]
          rfl
    _ = μ F := by
          rw [Measure.map_apply
            (measurable_axisBlockedFreePairLatticePath.comp
              measurable_independentProductPairTrajectoryMap)
            hE_meas]
    _ = 1 := hF_eq_one

/-- Helper for Exercise 18.2.4: after one step from the launch state, the encoded `ℤ^3` path law
is still almost surely outside the collision line. -/
private theorem axisBlockedFreePair_launchLatticePath_oneStepAvoidCollision_prob_eq_one :
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      {path : ℕ → LatticePoint 3 | path 1 ∉ axisBlockedDefectCollisionLine} = 1 := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq := (Pq b : Measure Ωq)
  let E : Set (ℕ → LatticePoint 3) := {path | path 1 ∉ axisBlockedDefectCollisionLine}
  let F : Set Ωq := {ω | axisBlockedFreePairRelativeState (Xq 1 ω) ∉ axisBlockedFreePairCollisionSet}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hE_meas : MeasurableSet E := by
    have hline :
        MeasurableSet {path : ℕ → LatticePoint 3 | path 1 ∈ axisBlockedDefectCollisionLine} := by
      exact (measurable_pi_apply 1) (MeasurableSet.of_discrete : MeasurableSet axisBlockedDefectCollisionLine)
    simpa [E, Set.setOf_app_iff] using hline.compl
  have hF_meas : MeasurableSet F := by
    have hrel :
        Measurable (fun ω : Ωq ↦ axisBlockedFreePairRelativeState (Xq 1 ω)) := by
      exact Measurable.of_discrete.comp (hqreal.measurable_process 1)
    simpa [F, Set.setOf_app_iff] using
      (hrel (MeasurableSet.of_discrete : MeasurableSet axisBlockedFreePairCollisionSet)).compl
  have hF_ae : ∀ᵐ ω ∂μ, ω ∈ F := by
    simpa [μ, F] using
      axisBlockedFreePair_launch_oneStep_avoids_collision_ae (Pq := Pq) (Xq := Xq)
  have hF_eq_one : μ F = 1 := by
    exact
      (MeasureTheory.ae_iff_prob_eq_one
        (μ := μ) (p := fun ω ↦ ω ∈ F) hF_meas).1 hF_ae
  have hpreimage :
      (fun ω : Ωq ↦ axisBlockedFreePairLatticePath (fun n : ℕ ↦ Xq n ω)) ⁻¹' E = F := by
    ext ω
    simp [E, F, axisBlockedFreePairLatticePath, mem_axisBlockedDefectCollisionLine_iff]
  -- Proof comment: pass the pushed-forward path event back to the launched realization on `Ωq`,
  -- where the earlier one-step collision-avoidance theorem already gives probability `1`.
  calc
    Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b) E =
      Measure.map
        (fun ω : Ωq ↦ axisBlockedFreePairLatticePath (fun n : ℕ ↦ Xq n ω))
        μ E := by
          rw [independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq) b]
          rw [Measure.map_map measurable_independentProductPairTrajectoryMap
            measurable_axisBlockedFreePairLatticePath]
          rfl
    _ = μ F := by
          rw [Measure.map_apply
            (measurable_axisBlockedFreePairLatticePath.comp
              measurable_independentProductPairTrajectoryMap)
            hE_meas]
          rw [hpreimage]
    _ = 1 := hF_eq_one

/-- Helper for Exercise 18.2.4: forcing a one-step return from the launched pair to the axis
start pair gives a lower bound on the launched never-meet path-kernel mass. -/
private theorem axisBlockedFreePair_launchNeverMeet_lowerBoundFromStartPair :
    ((discreteMatrixKernel independentProductPairMatrix
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      ({((((0, 0) : AxisState), ((0, 1) : AxisState)))} : Set (AxisState × AxisState))) *
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((0, 0) : AxisState), ((0, 1) : AxisState)))
        freePairNeverMeetPathEvent ≤
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq := (Pq b : Measure Ωq)
  let initEvent : Set Ωq := {ω | Xq 0 ω = b}
  let returnEvent : Set Ωq := {ω | Xq 1 ω = a}
  let historyEvent : Set Ωq := initEvent ∩ returnEvent
  let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
  let neverMeet : Set Ωq := {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hinit_meas : MeasurableSet initEvent := by
    rw [show initEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    exact (hqreal.measurable_process 0) (measurableSet_singleton b)
  have hinit_hist0 : MeasurableSet[generatedFiltrationSpace Xq 0] initEvent := by
    have hX0 : Measurable[generatedFiltrationSpace Xq 0] (Xq 0) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 0
    rw [show initEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    exact hX0 (measurableSet_singleton b)
  have hreturn_meas : MeasurableSet returnEvent := by
    rw [show returnEvent = Xq 1 ⁻¹' ({a} : Set (AxisState × AxisState)) by
      ext ω
      simp [returnEvent]]
    exact (hqreal.measurable_process 1) (measurableSet_singleton a)
  have hreturn_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] returnEvent := by
    have hX1 : Measurable[generatedFiltrationSpace Xq 1] (Xq 1) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 1
    rw [show returnEvent = Xq 1 ⁻¹' ({a} : Set (AxisState × AxisState)) by
      ext ω
      simp [returnEvent]]
    exact hX1 (measurableSet_singleton a)
  have hinit_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] initEvent := by
    exact (generatedFiltrationSpace_monoNat (X := Xq) (m := 0) (n := 1) (Nat.zero_le 1)) _
      hinit_hist0
  have hhistory_meas : MeasurableSet historyEvent := hinit_meas.inter hreturn_meas
  have hhistory_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] historyEvent := by
    simpa [historyEvent] using hinit_hist1.inter hreturn_hist1
  have hhistory_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ historyEvent → Xq 1 ω = a := by
    intro ω hω
    exact hω.2
  have hinit_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ initEvent → Xq 0 ω = b := by
    intro ω hω
    exact hω
  have hinit_mass : μ initEvent = 1 := by
    rw [show initEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton b)]
    rw [hqreal.initial_eq b]
    simp [μ]
  have hhistory_mass :
      μ historyEvent =
        (discreteMatrixKernel independentProductPairMatrix b ({a} : Set (AxisState × AxisState))) *
          μ initEvent := by
    -- Proof comment: first pin the deterministic launch state `b`, then the one-step return to
    -- the axis start pair `a` factors through the free product-pair row.
    simpa [μ, historyEvent] using
      measureInter_eq_mul_stepMass_of_stateEvent
        (q := independentProductPairMatrix) (P := Pq) (X := Xq)
        (x := b) (y := b) (w := a) (n := 0) (A := initEvent)
        hinit_meas hinit_hist0 hinit_state
  have hfuture_mass :
      μ (historyEvent ∩ futureEvent) =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
          freePairNeverMeetPathEvent) * μ historyEvent := by
    -- Proof comment: once time `1` is fixed at the axis start pair `a`, the remaining
    -- diagonal-avoidance event is exactly the future path-kernel row from `a`.
    simpa [μ, futureEvent] using
      independentProductPair_measureInter_eq_mul_futurePathMass_of_stateEvent
        (Pq := Pq) (Xq := Xq) (a := b) (y := a) (n := 1)
        (A := historyEvent) (B := freePairNeverMeetPathEvent)
        measurableSet_freePairNeverMeetPathEvent hhistory_meas hhistory_hist1 hhistory_state
  have hlaunch_offdiag : b.1 ≠ b.2 := by
    norm_num [b]
  have hsubset : historyEvent ∩ futureEvent ⊆ neverMeet := by
    intro ω hω
    intro n
    cases n with
    | zero =>
        have h0 : Xq 0 ω = b := hω.1.1
        simpa [neverMeet, b] using hlaunch_offdiag
    | succ n =>
        have hpath : futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent := hω.2
        simpa [futureEvent, freePairNeverMeetPathEvent, futurePath, neverMeet] using hpath n
  -- Proof comment: the explicit one-step return event sits inside the full launched never-meet
  -- event, so its factored mass is a valid lower bound for the launched row.
  calc
    (discreteMatrixKernel independentProductPairMatrix b ({a} : Set (AxisState × AxisState))) *
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
          freePairNeverMeetPathEvent =
      μ (historyEvent ∩ futureEvent) := by
        rw [hfuture_mass, hhistory_mass, hinit_mass]
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ μ neverMeet := measure_mono hsubset
    _ =
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
          freePairNeverMeetPathEvent := by
            symm
            simpa [b, μ, neverMeet] using
              axisBlockedFreePair_launchPathKernel_neverMeet_eq_measure (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the start-pair never-meet path event has the same mass under the
realized path-kernel row as under the start realization measure. -/
private theorem axisBlockedFreePair_startPathKernel_neverMeet_eq_measure :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      ((((0, 0) : AxisState), ((0, 1) : AxisState)))
      freePairNeverMeetPathEvent =
      (Pq ((((0, 0) : AxisState), ((0, 1) : AxisState))) : Measure Ωq)
        {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  have hpreimage :
      (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) ⁻¹' freePairNeverMeetPathEvent =
        {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
    ext ω
    simp [freePairNeverMeetPathEvent]
  -- Proof comment: unfold the start path-kernel row as a pushforward of `Pq a`, then rewrite
  -- the preimage of the path event back to the pointwise never-meet event on `Ωq`.
  calc
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a freePairNeverMeetPathEvent =
        Measure.map (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) (Pq a : Measure Ωq)
          freePairNeverMeetPathEvent := by
            rw [independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq) a]
    _ = (Pq a : Measure Ωq)
          ((fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) ⁻¹' freePairNeverMeetPathEvent) := by
            rw [Measure.map_apply measurable_independentProductPairTrajectoryMap
              measurableSet_freePairNeverMeetPathEvent]
    _ =
        (Pq a : Measure Ωq) {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
          simpa [hpreimage]

/-- Helper for Exercise 18.2.4: forcing a one-step launch from the axis start pair to
`((1,0),(1,1))` gives a lower bound on the start-pair never-meet path-kernel mass. -/
private theorem axisBlockedFreePair_startNeverMeet_lowerBoundFromLaunch :
    ((discreteMatrixKernel independentProductPairMatrix
        ((((0, 0) : AxisState), ((0, 1) : AxisState))))
      ({((((1, 0) : AxisState), ((1, 1) : AxisState)))} : Set (AxisState × AxisState))) *
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent ≤
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((0, 0) : AxisState), ((0, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq := (Pq a : Measure Ωq)
  let initEvent : Set Ωq := {ω | Xq 0 ω = a}
  let launchEvent : Set Ωq := {ω | Xq 1 ω = b}
  let historyEvent : Set Ωq := initEvent ∩ launchEvent
  let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
  let neverMeet : Set Ωq := {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hinit_meas : MeasurableSet initEvent := by
    rw [show initEvent = Xq 0 ⁻¹' ({a} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    exact (hqreal.measurable_process 0) (measurableSet_singleton a)
  have hinit_hist0 : MeasurableSet[generatedFiltrationSpace Xq 0] initEvent := by
    have hX0 : Measurable[generatedFiltrationSpace Xq 0] (Xq 0) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 0
    rw [show initEvent = Xq 0 ⁻¹' ({a} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    exact hX0 (measurableSet_singleton a)
  have hlaunch_meas : MeasurableSet launchEvent := by
    rw [show launchEvent = Xq 1 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [launchEvent]]
    exact (hqreal.measurable_process 1) (measurableSet_singleton b)
  have hlaunch_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] launchEvent := by
    have hX1 : Measurable[generatedFiltrationSpace Xq 1] (Xq 1) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 1
    rw [show launchEvent = Xq 1 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [launchEvent]]
    exact hX1 (measurableSet_singleton b)
  have hinit_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] initEvent := by
    exact (generatedFiltrationSpace_monoNat (X := Xq) (m := 0) (n := 1) (Nat.zero_le 1)) _
      hinit_hist0
  have hhistory_meas : MeasurableSet historyEvent := hinit_meas.inter hlaunch_meas
  have hhistory_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] historyEvent := by
    simpa [historyEvent] using hinit_hist1.inter hlaunch_hist1
  have hhistory_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ historyEvent → Xq 1 ω = b := by
    intro ω hω
    exact hω.2
  have hinit_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ initEvent → Xq 0 ω = a := by
    intro ω hω
    exact hω
  have hinit_mass : μ initEvent = 1 := by
    rw [show initEvent = Xq 0 ⁻¹' ({a} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton a)]
    rw [hqreal.initial_eq a]
    simp [μ]
  have hhistory_mass :
      μ historyEvent =
        (discreteMatrixKernel independentProductPairMatrix a ({b} : Set (AxisState × AxisState))) *
          μ initEvent := by
    -- Proof comment: first pin the deterministic start state `a`, then the time-`1` launch to
    -- `b` factors through the one-step product-pair row.
    simpa [μ, historyEvent] using
      measureInter_eq_mul_stepMass_of_stateEvent
        (x := a) (y := a) (w := b) (n := 0) (A := initEvent)
        hinit_meas hinit_hist0 hinit_state
  have hfuture_mass :
      μ (historyEvent ∩ futureEvent) =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
          freePairNeverMeetPathEvent) * μ historyEvent := by
    -- Proof comment: once time `1` is fixed at the launched state `b`, the future never-meet
    -- event depends only on the realized path-kernel row from `b`.
    simpa [μ, futureEvent] using
      independentProductPair_measureInter_eq_mul_futurePathMass_of_stateEvent
        (Pq := Pq) (Xq := Xq) (a := a) (y := b) (n := 1)
        (A := historyEvent) (B := freePairNeverMeetPathEvent)
        measurableSet_freePairNeverMeetPathEvent hhistory_meas hhistory_hist1 hhistory_state
  have hstart_offdiag : a.1 ≠ a.2 := by
    norm_num [a]
  have hsubset : historyEvent ∩ futureEvent ⊆ neverMeet := by
    intro ω hω
    intro n
    cases n with
    | zero =>
        have h0 : Xq 0 ω = a := hω.1.1
        simpa [neverMeet, a] using hstart_offdiag
    | succ n =>
        have hpath : futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent := hω.2
        simpa [futureEvent, freePairNeverMeetPathEvent, futurePath, neverMeet] using hpath n
  -- Proof comment: the explicit launch-history event sits inside the full start-row never-meet
  -- event, so its factored mass is a valid lower bound for the start row.
  calc
    (discreteMatrixKernel independentProductPairMatrix a ({b} : Set (AxisState × AxisState))) *
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
          freePairNeverMeetPathEvent =
      μ (historyEvent ∩ futureEvent) := by
        rw [hfuture_mass, hhistory_mass, hinit_mass]
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ μ neverMeet := measure_mono hsubset
    _ =
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
          freePairNeverMeetPathEvent := by
            symm
            simpa [a, μ, neverMeet] using
              axisBlockedFreePair_startPathKernel_neverMeet_eq_measure (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: evaluating the start-pair path-law row on the never-meet event is
the same as evaluating its collision-code pushforward on the no-hit event. -/
private theorem axisBlockedFreePair_startPathKernel_neverMeet_eq_collisionCodeNoHitMass :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      ((((0, 0) : AxisState), ((0, 1) : AxisState)))
      freePairNeverMeetPathEvent =
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  -- Proof comment: rewrite the never-meet event as one preimage under the collision-code owner
  -- path map, then absorb that preimage into the corresponding pushforward row.
  calc
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
        freePairNeverMeetPathEvent =
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
          (axisBlockedFreePairCollisionCodePath ⁻¹' axisBlockedDefectNoHitPathEvent) := by
            rw [freePairNeverMeetPathEvent_eq_preimage_axisBlockedFreePairCollisionCodePath]
    _ =
        Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a)
          axisBlockedDefectNoHitPathEvent := by
            symm
            rw [Measure.map_apply measurable_axisBlockedFreePairCollisionCodePath
              measurableSet_axisBlockedDefectNoHitPathEvent]

/-- Helper for Exercise 18.2.4: positive launch-state never-meet mass propagates to positive
start-pair collision-code no-hit mass through the explicit one-step launch lower bound. -/
private theorem axisBlockedFreePair_startCollisionCodeNoHit_pos_of_launchNeverMeetPos
    (hlaunch :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent) :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  have hstart :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
    -- Proof comment: multiply the positive launch-state never-meet mass by the explicit
    -- start-to-launch one-step mass and compare with the established lower bound on the start row.
    exact lt_of_lt_of_le
      (ENNReal.mul_pos
        (axisBlockedFreePair_startPair_launchToOffDefect_pos (Pq := Pq) (Xq := Xq))
        hlaunch)
      (axisBlockedFreePair_startNeverMeet_lowerBoundFromLaunch (Pq := Pq) (Xq := Xq))
  -- Proof comment: the start-row never-meet event is exactly the corresponding collision-code
  -- no-hit mass under the pushforward path law.
  rw [← axisBlockedFreePair_startPathKernel_neverMeet_eq_collisionCodeNoHitMass
    (Pq := Pq) (Xq := Xq)]
  exact hstart

/-- Helper for Exercise 18.2.4: positive start-pair collision-code no-hit mass propagates back to
the launched `ℤ^3` collision-line avoidance mass through the explicit one-step return lower
bound. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_startCollisionCodeNoHit
    (hstart :
      0 <
        Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
          axisBlockedDefectNoHitPathEvent) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  have hstartNever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
    -- Proof comment: rewrite the start-row collision-code no-hit mass back to the corresponding
    -- never-meet mass of the free pair.
    rw [axisBlockedFreePair_startPathKernel_neverMeet_eq_collisionCodeNoHitMass
      (Pq := Pq) (Xq := Xq)]
    exact hstart
  have hlaunchNever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
    -- Proof comment: multiply the positive start-row mass by the explicit launched-to-start
    -- one-step return mass and compare with the launched lower bound.
    exact lt_of_lt_of_le
      (ENNReal.mul_pos
        (axisBlockedFreePair_launchToStartPair_pos (Pq := Pq) (Xq := Xq))
        hstartNever)
      (axisBlockedFreePair_launchNeverMeet_lowerBoundFromStartPair (Pq := Pq) (Xq := Xq))
  -- Proof comment: the launched never-meet row is exactly the launched `ℤ^3` collision-line
  -- avoidance mass under the encoded path law.
  rw [axisBlockedFreePair_launchPathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (Pq := Pq) (Xq := Xq)] at hlaunchNever
  exact hlaunchNever

/-- Helper for Exercise 18.2.4: positivity of the launched `ℤ^3` collision-line avoidance mass is
the analytic root from which the start-pair collision-code no-hit statement follows. -/
private theorem symmetricSimpleRandomWalk3_stepMatrix_originRow
    (y : LatticePoint 3) :
    latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3) 0 y =
      symmetricSimpleRandomWalkStepPMF 3 y := by
  have hrow :=
    congrArg
      (fun μ : Measure (LatticePoint 3) ↦ μ ({y} : Set (LatticePoint 3)))
      (latticeConvolutionStepMatrix_originRow_eq (ν := symmetricSimpleRandomWalkStepPMF 3))
  -- Proof comment: evaluate the origin-row measure identity on the singleton `{y}` to recover
  -- the pointwise step probability.
  simpa [discreteMatrixKernel_apply_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)] using hrow

/-- Helper for Exercise 18.2.4: any realization of the canonical symmetric simple random walk on
`ℤ^3` is not recurrent. -/
private theorem symmetricSimpleRandomWalk3_not_recurrent
    {Ω : Type*} [MeasurableSpace Ω]
    (P : LatticePoint 3 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n) P X] :
    ¬ IsRecurrentMarkovChain P X := by
  intro hrec
  have hrec_iff :
      IsRecurrentMarkovChain P X ↔ 3 ≤ 2 :=
    symmetricSimpleRandomWalk_lattice_recurrent_iff_dimension_le_two
      (D := 3)
      (p := latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
      (P := P) (X := X)
      (latticeConvolutionStepMatrix_isTranslationInvariant
        (ν := symmetricSimpleRandomWalkStepPMF 3))
      (fun y ↦ symmetricSimpleRandomWalk3_stepMatrix_originRow y)
  -- Proof comment: Theorem 17.39 forces recurrence only in dimensions at most `2`, which rules
  -- out the canonical three-dimensional walk.
  omega

/-- Helper for Exercise 18.2.4: once the owner process is normalized to the canonical symmetric
simple random walk on `ℤ^3`, irreducibility upgrades it to transient states everywhere. -/
private theorem symmetricSimpleRandomWalk3_allStatesTransient
    {Ω : Type*} [MeasurableSpace Ω]
    (P : LatticePoint 3 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n) P X]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))] :
    ∀ x : LatticePoint 3, IsTransientState P X x := by
  rcases
      irreducibleMarkovChain_recurrent_or_transient_of_discreteMatrixKernel_isIrreducible
        (p := latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
        (P := P) (X := X) with hrec | htrans
  · -- Proof comment: the recurrent branch is impossible by the three-dimensional recurrence
    -- classification fixed in the previous helper.
    exact False.elim <| symmetricSimpleRandomWalk3_not_recurrent (P := P) (X := X) hrec
  · -- Proof comment: the irreducible dichotomy leaves exactly the desired statewise transient
    -- conclusion in the nonrecurrent branch.
    exact htrans

/-- Helper for Exercise 18.2.4: a canonical symmetric simple random walk on `ℤ^3` started away
from the origin has strictly positive probability of avoiding the origin forever. -/
private theorem symmetricSimpleRandomWalk3_avoidOrigin_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : LatticePoint 3 → ProbabilityMeasure Ω) (X : ℕ → Ω → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n) P X]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))]
    {x : LatticePoint 3} (hx : x ≠ 0) :
    0 < (P x : Measure Ω) {ω | ∀ n : ℕ, X n ω ≠ 0} := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hitEvent : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0}
  let avoidEvent : Set Ω := {ω | ∀ n : ℕ, X n ω ≠ 0}
  have hhit_meas : MeasurableSet hitEvent := by
    have hUnion :
        hitEvent = ⋃ n : ℕ, {ω | X n.succ ω = 0} := by
      ext ω
      constructor
      · intro hω
        rcases hω with ⟨n, hn, hnzero⟩
        rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, rfl⟩
        exact Set.mem_iUnion.2 ⟨m, by simpa using hnzero⟩
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨n, hnzero⟩
        exact ⟨n.succ, Nat.succ_pos _, by simpa using hnzero⟩
    rw [hUnion]
    refine MeasurableSet.iUnion fun n ↦ ?_
    exact
      (inferInstance :
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            discreteMatrixKernel
              (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n) P X)
        .measurable_process n.succ (measurableSet_singleton 0)
  have hhit_lt_one : μ hitEvent < 1 := by
    have htrans :
        IsTransientState P X x :=
      symmetricSimpleRandomWalk3_allStatesTransient (P := P) (X := X) x
    exact
      (ENNReal.toReal_lt_toReal (measure_lt_top μ hitEvent) ENNReal.one_ne_top).2 <| by
        simpa [μ, hitEvent, IsTransientState, everHitsProbability_def] using htrans
  have havoid_ae : avoidEvent =ᵐ[μ] hitEventᶜ := by
    have hstart :
        ∀ᵐ ω ∂μ, X 0 ω = x := by
      have hprob :
          μ {ω | X 0 ω = x} = 1 := by
        rw [show ({ω | X 0 ω = x} : Set Ω) = X 0 ⁻¹' ({x} : Set (LatticePoint 3)) by
          ext ω
          simp]
        rw [← Measure.map_apply
          ((inferInstance :
            IsMarkovProcessRealization
              (fun n : ℕ ↦
                discreteMatrixKernel
                  (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n) P X)
              .measurable_process 0)
          (measurableSet_singleton x)]
        rw [(inferInstance :
          IsMarkovProcessRealization
            (fun n : ℕ ↦
              discreteMatrixKernel
                (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n) P X)
            .initial_eq x]
        simp [μ]
      exact
        (MeasureTheory.mem_ae_iff_prob_eq_one
          (show MeasurableSet {ω | X 0 ω = x} from
            (inferInstance :
              IsMarkovProcessRealization
                (fun n : ℕ ↦
                  discreteMatrixKernel
                    (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n) P X)
              .measurable_process 0 (measurableSet_singleton x))).2
          hprob
    filter_upwards [hstart] with ω hω0
    have hxω : X 0 ω ≠ 0 := by
      simpa [hω0] using hx
    simp [avoidEvent, hitEvent, hxω]
  have hcompl_pos : 0 < μ hitEventᶜ := by
    rw [Measure.compl_apply hhit_meas]
    simp [μ, hhit_lt_one, le_of_lt hhit_lt_one]
  -- Proof comment: transience makes the positive-time origin-hit event subunit, and the
  -- nonzero initial state removes the time-zero obstruction so the complement is exactly the
  -- full origin-avoidance event.
  rw [measure_congr havoid_ae]
  exact hcompl_pos

/-- Helper for Exercise 18.2.4: once a launch-side owner process is normalized to the canonical
simple random walk on `ℤ^3`, any lower bound from owner-origin avoidance to lattice collision-line
avoidance already gives the desired strict positivity. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_ownerAvoidLowerBound
    (P : LatticePoint 3 → ProbabilityMeasure Ωq)
    (ownerProcess : ℕ → Ωq → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P ownerProcess]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))]
    (hlower :
      (P ![1, 1, -1] : Measure Ωq) {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} ≤
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  have howner :
      0 < (P ![1, 1, -1] : Measure Ωq) {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} := by
    exact
      symmetricSimpleRandomWalk3_avoidOrigin_pos (P := P) (X := ownerProcess)
        (by norm_num)
  -- Proof comment: the canonical owner process gives positive mass to avoiding the origin, and
  -- the assumed measure lower bound transports that positivity back to the launched path event.
  exact lt_of_lt_of_le howner hlower

/-- Helper for Exercise 18.2.4: the same positivity transport only depends on the owner
origin-avoidance mass, not on the particular sample space realizing SRW3. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_ownerAvoidLowerBound'
    {Ω : Type*} [MeasurableSpace Ω]
    (P : LatticePoint 3 → ProbabilityMeasure Ω)
    (ownerProcess : ℕ → Ω → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P ownerProcess]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))]
    (hlower :
      (P ![1, 1, -1] : Measure Ω) {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} ≤
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  have howner :
      0 < (P ![1, 1, -1] : Measure Ω) {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} := by
    exact
      symmetricSimpleRandomWalk3_avoidOrigin_pos (P := P) (X := ownerProcess)
        (by norm_num)
  -- Proof comment: once the owner process is a genuine SRW3 realization, positivity of its
  -- origin-avoidance event is sample-space invariant and transfers through the assumed lower
  -- bound exactly as before.
  exact lt_of_lt_of_le howner hlower

/-- Helper for Exercise 18.2.4: encode a point of `ℤ^3` as the corresponding relative state
`((z 0, z 1), z 2)`. -/
private abbrev axisBlockedFreePairLatticePointToRelativeState
    (z : LatticePoint 3) : FreePairRelativeState :=
  (((z 0, z 1) : AxisState), z 2)

/-- Helper for Exercise 18.2.4: choose a start pair with relative state `z` by fixing the second
walker's height to `1`, which makes the launch point `![1, 1, -1]` land on
`((1, 0), (1, 1))`. -/
private def axisBlockedFreePairDefectVisitOwnerStartPair
    (z : LatticePoint 3) : AxisState × AxisState :=
  freePairCommonVerticalShift 1
    (freePairRelativeStateRepresentative
      (axisBlockedFreePairLatticePointToRelativeState z))

/-- Helper for Exercise 18.2.4: the chosen owner start pair has exactly the prescribed relative
state. -/
private theorem axisBlockedFreePairDefectVisitOwnerStartPair_relativeState
    (z : LatticePoint 3) :
    axisBlockedFreePairRelativeState
      (axisBlockedFreePairDefectVisitOwnerStartPair z) =
        axisBlockedFreePairLatticePointToRelativeState z := by
  -- Proof comment: the common vertical shift used to place the second walker at height `1` does
  -- not affect the relative quotient, so the stored relative state is still exactly `z`.
  rw [axisBlockedFreePairDefectVisitOwnerStartPair,
    axisBlockedFreePairRelativeState_commonVerticalShift]
  exact axisBlockedFreePairRelativeState_representative
    (axisBlockedFreePairLatticePointToRelativeState z)

/-- Helper for Exercise 18.2.4: encoding the relative state of the chosen start pair recovers the
original owner point `z ∈ ℤ^3`. -/
private theorem axisBlockedFreePairDefectVisitOwnerStartPair_latticePoint
    (z : LatticePoint 3) :
    freePairRelativeStateToLatticePoint3
      (axisBlockedFreePairRelativeState
        (axisBlockedFreePairDefectVisitOwnerStartPair z)) = z := by
  -- Proof comment: after identifying the relative state of the start pair, each coordinate of the
  -- `ℤ^3` encoding is definitionally the corresponding coordinate of `z`.
  ext i
  fin_cases i <;>
    simp [axisBlockedFreePairDefectVisitOwnerStartPair_relativeState,
      axisBlockedFreePairLatticePointToRelativeState]

/-- Helper for Exercise 18.2.4: the launch point `![1, 1, -1]` is represented by the launched
pair `((1, 0), (1, 1))`. -/
private theorem axisBlockedFreePairDefectVisitOwnerStartPair_launch :
    axisBlockedFreePairDefectVisitOwnerStartPair ![1, 1, -1] =
      ((((1, 0) : AxisState), ((1, 1) : AxisState))) := by
  -- Proof comment: fixing the second walker at height `1` was chosen exactly so the normalized
  -- launch owner point maps back to the given launched pair.
  norm_num [axisBlockedFreePairDefectVisitOwnerStartPair, freePairCommonVerticalShift,
    freePairRelativeStateRepresentative, verticalShiftState,
    axisBlockedFreePairLatticePointToRelativeState]

/-- Helper for Exercise 18.2.4: the owner start-law family on `Ωq` is obtained by starting the
free pair from the chosen representative of the owner point. -/
private def axisBlockedFreePairDefectVisitOwnerLaw
    (z : LatticePoint 3) : ProbabilityMeasure Ωq :=
  Pq (axisBlockedFreePairDefectVisitOwnerStartPair z)

/-- Helper for Exercise 18.2.4: at the distinguished owner point `![1, 1, -1]`, the owner
start-law family is exactly the launched free-pair law. -/
private theorem axisBlockedFreePairDefectVisitOwnerLaw_launch :
    axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] =
      Pq ((((1, 0) : AxisState), ((1, 1) : AxisState))) := by
  -- Proof comment: this is the direct launch normalization supplied by the chosen start-pair
  -- representative.
  simp [axisBlockedFreePairDefectVisitOwnerLaw,
    axisBlockedFreePairDefectVisitOwnerStartPair_launch]

/-- Helper for Exercise 18.2.4: the owner point `![0, 0, -1]` is represented by the distinguished
start pair `((0,0),(0,1))`. -/
private theorem axisBlockedFreePairDefectVisitOwnerStartPair_start :
    axisBlockedFreePairDefectVisitOwnerStartPair ![0, 0, -1] =
      ((((0, 0) : AxisState), ((0, 1) : AxisState))) := by
  -- Proof comment: using the same normalization with the second walker fixed at height `1`, the
  -- start owner point lands exactly on the distinguished start pair.
  norm_num [axisBlockedFreePairDefectVisitOwnerStartPair, freePairCommonVerticalShift,
    freePairRelativeStateRepresentative, verticalShiftState,
    axisBlockedFreePairLatticePointToRelativeState]

/-- Helper for Exercise 18.2.4: at the owner point `![0, 0, -1]`, the owner start-law family is
exactly the distinguished start-pair law. -/
private theorem axisBlockedFreePairDefectVisitOwnerLaw_start :
    axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![0, 0, -1] =
      Pq ((((0, 0) : AxisState), ((0, 1) : AxisState))) := by
  -- Proof comment: the start-side owner normalization is the direct analogue of the launched
  -- normalization and will be the base law for the sampled defect-visit root theorem.
  simp [axisBlockedFreePairDefectVisitOwnerLaw,
    axisBlockedFreePairDefectVisitOwnerStartPair_start]

/-- Helper for Exercise 18.2.4: the owner point `![2, 2, -1]` is represented by the explicit
two-right pair `((2,0),(2,1))`. -/
private theorem axisBlockedFreePairDefectVisitOwnerStartPair_twoRight :
    axisBlockedFreePairDefectVisitOwnerStartPair ![2, 2, -1] =
      ((((2, 0) : AxisState), ((2, 1) : AxisState))) := by
  -- Proof comment: with the second walker fixed at height `1`, the owner point `![2,2,-1]`
  -- normalizes to the concrete two-right row needed by the repaired `c`-row route.
  norm_num [axisBlockedFreePairDefectVisitOwnerStartPair, freePairCommonVerticalShift,
    freePairRelativeStateRepresentative, verticalShiftState,
    axisBlockedFreePairLatticePointToRelativeState]

/-- Helper for Exercise 18.2.4: at the owner point `![2, 2, -1]`, the owner start-law family is
exactly the two-right free-pair law. -/
private theorem axisBlockedFreePairDefectVisitOwnerLaw_twoRight :
    axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![2, 2, -1] =
      Pq ((((2, 0) : AxisState), ((2, 1) : AxisState))) := by
  -- Proof comment: this is the `c`-row normalization that lets later proofs transport between
  -- sampled-owner statements at `![2,2,-1]` and the concrete pair state `((2,0),(2,1))`.
  simp [axisBlockedFreePairDefectVisitOwnerLaw,
    axisBlockedFreePairDefectVisitOwnerStartPair_twoRight]

/-- Helper for Exercise 18.2.4: the start-side owner point used for the sampled defect-visit
process is nonzero. -/
private theorem axisBlockedFreePairDefectVisitOwnerStartPoint_ne_zero :
    (![0, 0, -1] : LatticePoint 3) ≠ 0 := by
  -- Proof comment: the third coordinate is `-1`, so the sampled owner chain starts away from the
  -- origin and is eligible for the standard SRW3 origin-avoidance theorem once its law is
  -- identified.
  norm_num

/-- Helper for Exercise 18.2.4: detect visits of the relative owner chain to the defect set by a
`0/1`-valued process, so iterated entrance times can sample those visits. -/
private def axisBlockedFreePairDefectVisitIndicator : ℕ → Ωq → ℤ :=
  fun n ω ↦
    if axisBlockedFreePairRelativeState (Xq n ω) ∈ axisBlockedFreePairDefectSet then
      0
    else
      1

/-- Helper for Exercise 18.2.4: the `k`-th sampled owner state is the encoded relative state at
the `k`-th visit of the relative chain to the defect set. -/
private def axisBlockedFreePairDefectVisitOwner
    (k : ℕ+) : Ωq → LatticePoint 3 :=
  fun ω ↦
    stoppedValue
      (fun n ω' ↦ freePairRelativeStateToLatticePoint3
        (axisBlockedFreePairRelativeState (Xq n ω')))
      (fun ω' ↦ (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω')
      ω

/-- Helper for Exercise 18.2.4: the launch-side owner process starts from the present relative
owner point and then records the successive sampled defect visits. -/
private def axisBlockedFreePairDefectVisitOwnerProcess :
    ℕ → Ωq → LatticePoint 3
  | 0 => fun ω ↦ freePairRelativeStateToLatticePoint3
      (axisBlockedFreePairRelativeState (Xq 0 ω))
  | n + 1 => fun ω ↦
      axisBlockedFreePairDefectVisitOwner (Xq := Xq) ⟨n + 1, Nat.succ_pos _⟩ ω

/-- Helper for Exercise 18.2.4: the positive-time coordinates of the sampled owner process are
exactly the corresponding stopped defect-visit observables. -/
private theorem axisBlockedFreePairDefectVisitOwnerProcess_pNat
    (k : ℕ+) :
    axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) k =
      axisBlockedFreePairDefectVisitOwner (Xq := Xq) k := by
  cases' k with n hn
  cases n with
  | zero =>
      cases (Nat.not_lt_zero _ hn)
  | succ n =>
      rfl

/-- Helper for Exercise 18.2.4: each time slice of the sampled owner process is measurable,
because the codomain is a countable lattice state space. -/
private theorem axisBlockedFreePairDefectVisitOwnerProcess_measurable
    (n : ℕ) :
    Measurable (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) n) := by
  -- Proof comment: the sampled owner states live in the discrete countable space `ℤ^3`, so each
  -- coordinate map is measurable without further transport arguments.
  exact measurable_of_countable
    (f := axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) n)

/-- Helper for Exercise 18.2.4: the sampled owner process starts from the prescribed owner point
under the corresponding owner start law. -/
private theorem axisBlockedFreePairDefectVisitOwnerProcess_initial_eq
    (z : LatticePoint 3) :
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) z : Measure Ωq).map
        (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 0) =
      Measure.dirac z := by
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  -- Proof comment: time `0` of the free pair is the chosen representative of `z`, and the
  -- owner-process coordinate at time `0` is just the encoded relative state of that pair.
  calc
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) z : Measure Ωq).map
        (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 0) =
      ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) z : Measure Ωq).map (Xq 0)).map
        (fun s : AxisState × AxisState ↦
          freePairRelativeStateToLatticePoint3 (axisBlockedFreePairRelativeState s)) := by
            rw [Measure.map_map (hqreal.measurable_process 0)
              (measurable_of_countable
                (f := fun s : AxisState × AxisState ↦
                  freePairRelativeStateToLatticePoint3
                    (axisBlockedFreePairRelativeState s)))]
            rfl
    _ =
      (Measure.dirac (axisBlockedFreePairDefectVisitOwnerStartPair z)).map
        (fun s : AxisState × AxisState ↦
          freePairRelativeStateToLatticePoint3 (axisBlockedFreePairRelativeState s)) := by
            rw [hqreal.initial_eq (axisBlockedFreePairDefectVisitOwnerStartPair z)]
    _ = Measure.dirac z := by
          simp [axisBlockedFreePairDefectVisitOwnerStartPair_latticePoint]

/-- Helper for Exercise 18.2.4: every finite iterated defect-visit time lands in the defect set,
equivalently the `0/1`-indicator is `0` there. -/
private theorem axisBlockedFreePairDefectVisitIndicator_eq_zero_at_iteratedVisitFinite
    {k : ℕ+} {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω ≠ ⊤) :
    axisBlockedFreePairDefectVisitIndicator (Xq := Xq)
      (((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω).untopA) ω = 0 := by
  cases k using PNat.recOn with
  | one =>
      -- Proof comment: for the first sampled defect visit, `hittingAfter_mem_set_of_ne_top`
      -- directly records that the indicator is `0` at the finite hitting index.
      have hmem :
          axisBlockedFreePairDefectVisitIndicator (Xq := Xq)
              (((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω).untopA) ω ∈
            ({0} : Set ℤ) := by
        have h :
            axisBlockedFreePairDefectVisitIndicator (Xq := Xq)
                (MeasureTheory.hittingAfter
                  (axisBlockedFreePairDefectVisitIndicator (Xq := Xq))
                  ({0} : Set ℤ) 1 ω).untopA ω ∈
              ({0} : Set ℤ) :=
          hittingAfter_mem_set_of_ne_top
            (by simpa [iteratedEntranceTime_one] using hfinite)
        simpa [iteratedEntranceTime_one] using h
      simpa [Set.mem_singleton_iff] using hmem
  | succ k =>
      let S : Set ℕ :=
        {n : ℕ |
          (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω < n ∧
            axisBlockedFreePairDefectVisitIndicator (Xq := Xq) n ω = 0}
      have hsInf :
          sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) =
            (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^(k + 1)) ω := by
        simpa [iteratedEntranceTime_succ, S]
      have hS : S.Nonempty := by
        by_contra hS
        have himage_empty : ((fun n : ℕ ↦ (n : ℕ∞)) '' S) = ∅ := by
          simpa [Set.not_nonempty_iff_eq_empty] using hS
        have htop :
            (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^(k + 1)) ω = ⊤ := by
          rw [← hsInf, himage_empty, sInf_empty]
        exact hfinite htop
      have hsInf_nat :
          ((sInf S : ℕ) : ℕ∞) =
            (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^(k + 1)) ω := by
        calc
          ((sInf S : ℕ) : ℕ∞) = sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) := by
            simpa using (WithTop.coe_sInf' hS (OrderBot.bddBelow S))
          _ = (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^(k + 1)) ω := hsInf
      have huntop :
          ((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^(k + 1)) ω).untopA =
            sInf S := by
        exact WithTop.coe_inj.mp <| by
          calc
            ((((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^(k + 1)) ω).untopA : ℕ)
                : ℕ∞) =
                (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^(k + 1)) ω := by
                  rw [WithTop.untopA_eq_untop hfinite]
                  exact WithTop.coe_untop _ hfinite
            _ = ((sInf S : ℕ) : ℕ∞) := hsInf_nat.symm
      have hsInf_mem : sInf S ∈ S := Nat.sInf_mem hS
      -- Proof comment: the recursive definition of iterated entrance times picks the least later
      -- defect visit, so its `untopA` representative again satisfies the indicator equation.
      simpa [S, huntop] using hsInf_mem.2

/-- Helper for Exercise 18.2.4: at any finite iterated defect-visit time, the stopped owner value
is exactly the encoded relative state at that visit. -/
private theorem axisBlockedFreePairDefectVisitOwner_eq_latticePoint_at_iteratedVisitTime
    {k : ℕ+} {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω ≠ ⊤) :
    axisBlockedFreePairDefectVisitOwner (Xq := Xq) k ω =
      freePairRelativeStateToLatticePoint3
        (axisBlockedFreePairRelativeState
          (Xq (((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω).untopA) ω)) := by
  have hτ :
      (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω =
        ((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω).untopA := by
    rw [WithTop.untopA_eq_untop hfinite]
    symm
    exact WithTop.coe_untop _ hfinite
  -- Proof comment: on the finite time slice where the iterated defect-visit time is fixed, the
  -- stopped-value definition collapses to the deterministic-time encoded relative state.
  unfold axisBlockedFreePairDefectVisitOwner
  simpa [hτ] using
    (stoppedValue_eq_on_timeSlice
      (X := fun n ω' ↦
        freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState (Xq n ω')))
      (τ := fun ω' ↦ (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω')
      (ω := ω) (hτω := hτ))

/-- Helper for Exercise 18.2.4: the raw `ℤ^3` chart sends every defect state to the defect
surface `z 0 = 0 ∨ z 1 = 0`. -/
private theorem freePairRelativeStateToLatticePoint3_mem_defectSurface_of_defect
    {s : AxisState × AxisState}
    (hs : axisBlockedFreePairRelativeState s ∈ axisBlockedFreePairDefectSet) :
    freePairRelativeStateToLatticePoint3 (axisBlockedFreePairRelativeState s) 0 = 0 ∨
      freePairRelativeStateToLatticePoint3 (axisBlockedFreePairRelativeState s) 1 = 0 := by
  -- Proof comment: in the raw lattice encoding, the first two coordinates are exactly the two
  -- horizontal coordinates, so membership in the defect set forces one coordinate plane.
  rcases (mem_axisBlockedFreePairDefectSet_iff (s := s)).1 hs with hs | hs
  · left
    simpa [freePairRelativeStateToLatticePoint3, axisBlockedFreePairRelativeState] using hs
  · right
    simpa [freePairRelativeStateToLatticePoint3, axisBlockedFreePairRelativeState] using hs

/-- Helper for Exercise 18.2.4: on the defect surface, collision-code `0` forces the encoded
owner point itself to be `0`. -/
private theorem latticePoint_eq_zero_of_mem_defectSurface_of_collisionCode_eq_zero
    {z : LatticePoint 3}
    (hsurface : z 0 = 0 ∨ z 1 = 0)
    (hcode : axisBlockedDefectCollisionCode z = 0) :
    z = 0 := by
  have hdiff :
      z 0 = z 1 := by
    apply sub_eq_zero.mp
    simpa [axisBlockedDefectCollisionCode] using
      congrArg (fun v : LatticePoint 2 ↦ v 0) hcode
  have hz₂ :
      z 2 = 0 := by
    simpa [axisBlockedDefectCollisionCode] using
      congrArg (fun v : LatticePoint 2 ↦ v 1) hcode
  rcases hsurface with hz0 | hz1
  · have hz1' : z 1 = 0 := by
      simpa [hz0] using hdiff.symm
    ext i
    fin_cases i <;> simp [hz0, hz1', hz₂]
  · have hz0' : z 0 = 0 := by
      simpa [hz1] using hdiff
    ext i
    fin_cases i <;> simp [hz0', hz1, hz₂]

/-- Helper for Exercise 18.2.4: on a finite sampled defect-visit slice, collision-code `0`
forces the sampled owner state itself to be the origin. -/
private theorem axisBlockedFreePairDefectVisitOwner_eq_zero_of_collisionCode_eq_zero_at_iteratedVisit
    {k : ℕ+} {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω ≠ ⊤)
    (hzero :
      axisBlockedDefectCollisionCode
        (freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState
            (Xq (((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω).untopA) ω))) =
        0) :
    axisBlockedFreePairDefectVisitOwner (Xq := Xq) k ω = 0 := by
  let n : ℕ :=
    ((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω).untopA
  have hindicator_zero :
      axisBlockedFreePairDefectVisitIndicator (Xq := Xq) n ω = 0 :=
    axisBlockedFreePairDefectVisitIndicator_eq_zero_at_iteratedVisitFinite
      (Xq := Xq) hfinite
  have hdefect :
      axisBlockedFreePairRelativeState (Xq n ω) ∈ axisBlockedFreePairDefectSet := by
    by_cases hmem :
        axisBlockedFreePairRelativeState (Xq n ω) ∈ axisBlockedFreePairDefectSet
    · exact hmem
    · simp [n, axisBlockedFreePairDefectVisitIndicator, hmem] at hindicator_zero
  have hsurface :
      freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState (Xq n ω)) 0 = 0 ∨
        freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState (Xq n ω)) 1 = 0 :=
    freePairRelativeStateToLatticePoint3_mem_defectSurface_of_defect hdefect
  have hstate_zero :
      freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState (Xq n ω)) = 0 :=
    latticePoint_eq_zero_of_mem_defectSurface_of_collisionCode_eq_zero hsurface hzero
  -- Proof comment: a sampled defect visit lives on the defect surface, and on that surface the
  -- collision line collapses to the single point `0`.
  calc
    axisBlockedFreePairDefectVisitOwner (Xq := Xq) k ω =
        freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState (Xq n ω)) := by
            simpa [n] using
              axisBlockedFreePairDefectVisitOwner_eq_latticePoint_at_iteratedVisitTime
                (Xq := Xq) hfinite
    _ = 0 := hstate_zero

/-- Helper for Exercise 18.2.4: on a finite sampled defect-visit slice, a sampled owner value `0`
forces the underlying collision code on that slice to be `0`. -/
private theorem axisBlockedFreePairCollisionCode_eq_zero_of_defectVisitOwner_eq_zero_at_iteratedVisit
    {k : ℕ+} {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω ≠ ⊤)
    (hzero : axisBlockedFreePairDefectVisitOwner (Xq := Xq) k ω = 0) :
    axisBlockedDefectCollisionCode
      (freePairRelativeStateToLatticePoint3
        (axisBlockedFreePairRelativeState
          (Xq (((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω).untopA) ω))) =
      0 := by
  -- Proof comment: on the finite iterated-visit slice, the sampled owner is exactly the encoded
  -- relative state at that slice, so applying the collision-code map to the zero owner state gives
  -- the desired vanishing collision code.
  have hstate :
      axisBlockedFreePairDefectVisitOwner (Xq := Xq) k ω =
        freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState
            (Xq (((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω).untopA) ω)) :=
    axisBlockedFreePairDefectVisitOwner_eq_latticePoint_at_iteratedVisitTime
      (Xq := Xq) hfinite
  have hencoded_zero :
      freePairRelativeStateToLatticePoint3
        (axisBlockedFreePairRelativeState
          (Xq (((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k) ω).untopA) ω)) = 0 := by
    simpa [hstate] using hzero
  exact congrArg axisBlockedDefectCollisionCode hencoded_zero

/-- Helper for Exercise 18.2.4: the simple-random-walk point `![2,2,-1]` lies off the raw
defect surface. -/
private theorem latticePoint3_twoOneNegOne_not_mem_defectSurface :
    ¬ (((![2, 2, -1] : LatticePoint 3) 0 = 0) ∨
      (((![2, 2, -1] : LatticePoint 3) 1 = 0)) := by
  -- Proof comment: both horizontal coordinates of `![2,2,-1]` are nonzero, so this point cannot
  -- come from the raw defect-state chart.
  norm_num

/-- Helper for Exercise 18.2.4: the positive first-coordinate step of the canonical `ℤ^3`
simple random walk has mass `1 / 6`. -/
private theorem symmetricSimpleRandomWalkStepPMF_apply_posFirst :
    symmetricSimpleRandomWalkStepPMF 3 (Pi.single 0 (1 : ℤ)) = 1 / 6 := by
  -- Proof comment: only the witness `(true, 0)` contributes to the pushforward mass of the
  -- positive first-coordinate unit step.
  rw [symmetricSimpleRandomWalkStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Fintype.sum_bool]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  have h01 : (Pi.single 0 (1 : ℤ) : LatticePoint 3) ≠ Pi.single 1 (1 : ℤ) :=
    cubicLattice_single_ne_single_of_ne (i := 0) (j := 1) (by decide) (m := 1) (n := 1)
      (by norm_num)
  have h0n1 : (Pi.single 0 (1 : ℤ) : LatticePoint 3) ≠ Pi.single 1 (-1 : ℤ) :=
    cubicLattice_single_ne_single_of_ne (i := 0) (j := 1) (by decide) (m := 1) (n := -1)
      (by norm_num)
  have h02 : (Pi.single 0 (1 : ℤ) : LatticePoint 3) ≠ Pi.single 2 (1 : ℤ) :=
    cubicLattice_single_ne_single_of_ne (i := 0) (j := 2) (by decide) (m := 1) (n := 1)
      (by norm_num)
  have h0n2 : (Pi.single 0 (1 : ℤ) : LatticePoint 3) ≠ Pi.single 2 (-1 : ℤ) :=
    cubicLattice_single_ne_single_of_ne (i := 0) (j := 2) (by decide) (m := 1) (n := -1)
      (by norm_num)
  simp [PMF.uniformOfFintype_apply, h01, h0n1, h02, h0n2]

/-- Helper for Exercise 18.2.4: on a finite first defect-visit slice, the sampled raw owner value
is exactly the raw `ℤ^3` encoding at that defect time. -/
private theorem axisBlockedFreePairDefectVisitOwner_first_eq_latticePoint_at_defectTime
    {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω ≠ ⊤) :
    axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω =
      freePairRelativeStateToLatticePoint3
        (axisBlockedFreePairRelativeState
          (Xq ((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω).untopA ω)) := by
  have hτ :
      (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω =
        ((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω).untopA := by
    rw [WithTop.untopA_eq_untop hfinite]
    symm
    exact WithTop.coe_untop _ hfinite
  -- Proof comment: after fixing the first defect-visit time, the stopped-value definition of the
  -- raw sampled owner collapses to the deterministic-time relative-state encoding.
  change axisBlockedFreePairDefectVisitOwner (Xq := Xq) ⟨1, Nat.succ_pos 0⟩ ω = _
  unfold axisBlockedFreePairDefectVisitOwner
  simpa [hτ] using
    (stoppedValue_eq_on_timeSlice
      (X := fun n ω' ↦
        freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState (Xq n ω')))
      (τ := fun ω' ↦ (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω')
      (ω := ω) (hτω := hτ))

/-- Helper for Exercise 18.2.4: whenever the first defect-visit time is finite, the raw sampled
owner lies on the defect surface `z 0 = 0 ∨ z 1 = 0`. -/
private theorem axisBlockedFreePairDefectVisitOwner_first_mem_defectSurface_of_finite
    {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω ≠ ⊤) :
    (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω) 0 = 0 ∨
      (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω) 1 = 0 := by
  let n : ℕ := ((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω).untopA
  have hindicator_zero :
      axisBlockedFreePairDefectVisitIndicator (Xq := Xq) n ω = 0 := by
    have hmem :
        axisBlockedFreePairDefectVisitIndicator (Xq := Xq)
            (MeasureTheory.hittingAfter
              (axisBlockedFreePairDefectVisitIndicator (Xq := Xq))
              ({0} : Set ℤ) 1 ω).untopA ω ∈ ({0} : Set ℤ) := by
      exact hittingAfter_mem_set_of_ne_top (by simpa [iteratedEntranceTime_one] using hfinite)
    simpa [n, axisBlockedFreePairDefectVisitIndicator, iteratedEntranceTime_one,
      Set.mem_singleton_iff] using hmem
  have hdefect :
      axisBlockedFreePairRelativeState (Xq n ω) ∈ axisBlockedFreePairDefectSet := by
    by_cases hmem :
        axisBlockedFreePairRelativeState (Xq n ω) ∈ axisBlockedFreePairDefectSet
    · exact hmem
    · simp [axisBlockedFreePairDefectVisitIndicator, hmem] at hindicator_zero
  have hsurface :
      freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState (Xq n ω)) 0 = 0 ∨
        freePairRelativeStateToLatticePoint3
          (axisBlockedFreePairRelativeState (Xq n ω)) 1 = 0 :=
    freePairRelativeStateToLatticePoint3_mem_defectSurface_of_defect hdefect
  -- Proof comment: the first sampled raw owner is read exactly at a defect visit, so the defect
  -- surface statement transfers immediately from the sampled state.
  simpa [n,
    axisBlockedFreePairDefectVisitOwner_first_eq_latticePoint_at_defectTime
      (Xq := Xq) hfinite] using hsurface

/-- Helper for Exercise 18.2.4: under the launched owner law, the first raw sampled owner can
never be the off-surface point `![2,2,-1]`. -/
private theorem axisBlockedFreePairDefectVisitOwnerProcess_first_ne_twoOneNegOne_ae :
    ∀ᵐ ω ∂(axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq),
      axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω ≠ ![2, 2, -1] := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hstart :
      ∀ᵐ ω ∂μ, Xq 0 ω = b := by
    have hprob :
        μ {ω | Xq 0 ω = b} = 1 := by
      rw [show {ω | Xq 0 ω = b} = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
        ext ω
        simp]
      rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton b)]
      rw [show μ = (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq) by
        rfl]
      rw [axisBlockedFreePairDefectVisitOwnerLaw_launch (Pq := Pq)]
      rw [hqreal.initial_eq b]
      simp [μ, b]
    exact
      (MeasureTheory.mem_ae_iff_prob_eq_one
        (show MeasurableSet {ω | Xq 0 ω = b} from
          (hqreal.measurable_process 0) (measurableSet_singleton b))).2 hprob
  filter_upwards [hstart] with ω hω0
  by_cases hfinite : (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω = ⊤
  · have hvalue :
      axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = ![1, 1, -1] := by
      change axisBlockedFreePairDefectVisitOwner (Xq := Xq) ⟨1, Nat.succ_pos 0⟩ ω = ![1, 1, -1]
      unfold axisBlockedFreePairDefectVisitOwner
      -- Proof comment: on the exceptional top branch, `stoppedValue` falls back to time `0`,
      -- and the launched owner law starts exactly from `![1,1,-1]`.
      simpa [axisBlockedFreePairLatticePoint_launch, hfinite, hω0]
    simpa [hvalue]
  · have hsurface :
        (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω) 0 = 0 ∨
          (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω) 1 = 0 :=
      axisBlockedFreePairDefectVisitOwner_first_mem_defectSurface_of_finite
        (Xq := Xq) hfinite
    -- Proof comment: on the finite defect-visit branch, the first sampled raw owner lies on the
    -- defect surface, while `![2,2,-1]` does not.
    intro hEq
    exact latticePoint3_twoOneNegOne_not_mem_defectSurface (by simpa [hEq] using hsurface)

/-- Helper for Exercise 18.2.4: the raw defect-visit chart cannot realize SRW3, because its first
sampled state never reaches the off-surface point `![2,2,-1]` from launch. -/
private theorem axisBlockedFreePairDefectVisitOwner_rawChart_not_isMarkovProcessRealization :
    ¬ IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq))
      (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq)) := by
  intro hraw
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let target : LatticePoint 3 := ![2, 2, -1]
  have hzero :
      μ {ω | axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = target} = 0 := by
    exact compl_mem_ae_iff.mp <| by
      simpa [μ, target] using
        axisBlockedFreePairDefectVisitOwnerProcess_first_ne_twoOneNegOne_ae
          (Pq := Pq) (Xq := Xq)
  have hmap :
      μ.map (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1) =
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![1, 1, -1]) := by
    -- Proof comment: a genuine SRW3 realization would identify the time-`1` marginal with the
    -- one-step kernel row from the launched point.
    simpa [μ, pow_one] using hraw.transition_eq ![1, 1, -1] 1
  have hmass :
      μ {ω | axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = target} =
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![1, 1, -1]) ({target} : Set (LatticePoint 3)) := by
    rw [show {ω | axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = target} =
        axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ⁻¹'
          ({target} : Set (LatticePoint 3)) by
      ext ω
      simp]
    rw [← Measure.map_apply
      (axisBlockedFreePairDefectVisitOwnerProcess_measurable (Xq := Xq) 1)
      (measurableSet_singleton target)]
    exact congrArg (fun ν : Measure (LatticePoint 3) ↦ ν ({target} : Set (LatticePoint 3))) hmap
  have hkernel_pos :
      0 <
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![1, 1, -1]) ({target} : Set (LatticePoint 3)) := by
    rw [discreteMatrixKernel_apply_singleton]
    rw [latticeConvolutionStepMatrix_isTranslationInvariant
      (ν := symmetricSimpleRandomWalkStepPMF 3) ![1, 1, -1] target]
    have hdiff : target - ![1, 1, -1] = Pi.single 0 (1 : ℤ) := by
      ext i
      fin_cases i <;> norm_num [target]
    rw [hdiff]
    rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
    rw [symmetricSimpleRandomWalkStepPMF_apply_posFirst]
    norm_num
  -- Proof comment: the first sampled raw owner misses an SRW3 neighbor almost surely, while a
  -- true SRW3 realization would have to hit that neighbor with positive one-step mass.
  have : ¬ (0 <
      μ {ω | axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = target}) := by
    simpa [hzero]
  exact this <| by
    rw [hmass]
    exact hkernel_pos

/-- Helper for Exercise 18.2.4: the simple-random-walk point `![3,2,-1]` also lies off the
raw defect surface. -/
private theorem latticePoint3_threeOneNegOne_not_mem_defectSurface :
    ¬ (((![3, 2, -1] : LatticePoint 3) 0 = 0) ∨
      (((![3, 2, -1] : LatticePoint 3) 1 = 0)) := by
  -- Proof comment: both horizontal coordinates of `![3,2,-1]` are nonzero, so this point is
  -- likewise incompatible with the raw defect-state chart.
  norm_num

/-- Helper for Exercise 18.2.4: under the truthful two-right owner law, the first raw sampled
owner can never be the off-surface point `![3,2,-1]`. -/
private theorem axisBlockedFreePairDefectVisitOwnerProcess_twoRight_first_ne_threeOneNegOne_ae :
    ∀ᵐ ω ∂(axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![2, 2, -1] : Measure Ωq),
      axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω ≠ ![3, 2, -1] := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![2, 2, -1] : Measure Ωq)
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hstart :
      ∀ᵐ ω ∂μ, Xq 0 ω = c := by
    have hprob :
        μ {ω | Xq 0 ω = c} = 1 := by
      rw [show {ω | Xq 0 ω = c} = Xq 0 ⁻¹' ({c} : Set (AxisState × AxisState)) by
        ext ω
        simp]
      rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton c)]
      rw [show μ = (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![2, 2, -1] : Measure Ωq) by
        rfl]
      rw [axisBlockedFreePairDefectVisitOwnerLaw_twoRight (Pq := Pq)]
      rw [hqreal.initial_eq c]
      simp [μ, c]
    exact
      (MeasureTheory.mem_ae_iff_prob_eq_one
        (show MeasurableSet {ω | Xq 0 ω = c} from
          (hqreal.measurable_process 0) (measurableSet_singleton c))).2 hprob
  filter_upwards [hstart] with ω hω0
  by_cases hfinite : (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^1) ω = ⊤
  · have hvalue :
      axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = ![2, 2, -1] := by
      change axisBlockedFreePairDefectVisitOwner (Xq := Xq) ⟨1, Nat.succ_pos 0⟩ ω = ![2, 2, -1]
      unfold axisBlockedFreePairDefectVisitOwner
      -- Proof comment: on the exceptional top branch, `stoppedValue` again falls back to time
      -- `0`, and the truthful two-right owner law starts exactly from `![2,2,-1]`.
      simpa [axisBlockedFreePairLatticePoint_twoRight, hfinite, hω0]
    intro hEq
    have : (![(2 : ℤ), 2, -1] : LatticePoint 3) = ![3, 2, -1] := hvalue.trans hEq
    norm_num at this
  · have hsurface :
        (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω) 0 = 0 ∨
          (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω) 1 = 0 :=
      axisBlockedFreePairDefectVisitOwner_first_mem_defectSurface_of_finite
        (Xq := Xq) hfinite
    -- Proof comment: on the finite defect-visit branch, the first sampled raw owner lies on the
    -- defect surface, while `![3,2,-1]` does not.
    intro hEq
    exact latticePoint3_threeOneNegOne_not_mem_defectSurface (by simpa [hEq] using hsurface)

/-- Helper for Exercise 18.2.4: from `![2,2,-1]`, canonical SRW3 reaches the neighbor
`![3,2,-1]` in one step with positive mass. -/
private theorem symmetricSimpleRandomWalk3_twoRight_stepMass_threeOneNegOne_pos :
    0 <
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
        ![2, 2, -1]) ({(![3, 2, -1] : LatticePoint 3)} : Set (LatticePoint 3)) := by
  rw [discreteMatrixKernel_apply_singleton]
  rw [latticeConvolutionStepMatrix_isTranslationInvariant
    (ν := symmetricSimpleRandomWalkStepPMF 3) ![2, 2, -1] ![3, 2, -1]]
  have hdiff : (![3, 2, -1] : LatticePoint 3) - ![2, 2, -1] = Pi.single 0 (1 : ℤ) := by
    ext i
    fin_cases i <;> norm_num
  rw [hdiff]
  rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
  rw [symmetricSimpleRandomWalkStepPMF_apply_posFirst]
  norm_num

/-- Helper for Exercise 18.2.4: the natural two-right raw defect-visit chart already violates the
SRW3 one-step law at the off-surface point `![3,2,-1]`. -/
private theorem axisBlockedFreePairDefectVisitOwner_rawChart_twoRight_step_obstruction :
    ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![2, 2, -1] : Measure Ωq).map
      (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1)) ≠
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
        ![2, 2, -1]) := by
  intro hEq
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![2, 2, -1] : Measure Ωq)
  let target : LatticePoint 3 := ![3, 2, -1]
  have hzero :
      μ {ω | axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = target} = 0 := by
    exact compl_mem_ae_iff.mp <| by
      simpa [μ, target] using
        axisBlockedFreePairDefectVisitOwnerProcess_twoRight_first_ne_threeOneNegOne_ae
          (Pq := Pq) (Xq := Xq)
  have hmass :
      μ {ω | axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = target} =
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![2, 2, -1]) ({target} : Set (LatticePoint 3)) := by
    rw [show {ω | axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = target} =
        axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ⁻¹'
          ({target} : Set (LatticePoint 3)) by
      ext ω
      simp]
    rw [← Measure.map_apply
      (axisBlockedFreePairDefectVisitOwnerProcess_measurable (Xq := Xq) 1)
      (measurableSet_singleton target)]
    exact congrArg (fun ν : Measure (LatticePoint 3) ↦ ν ({target} : Set (LatticePoint 3))) hEq
  have hkernel_pos :
      0 <
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![2, 2, -1]) ({target} : Set (LatticePoint 3)) :=
    by simpa [target] using symmetricSimpleRandomWalk3_twoRight_stepMass_threeOneNegOne_pos
  -- Proof comment: the truthful two-right sampled chart misses a genuine SRW3 neighbor at time
  -- `1`, so its one-step marginal cannot equal the SRW3 row from `![2,2,-1]`.
  have : ¬ (0 <
      μ {ω | axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 1 ω = target}) := by
    simpa [hzero]
  exact this <| by
    rw [hmass]
    exact hkernel_pos

/-- Helper for Exercise 18.2.4: a direct owner witness on `Ωq` marks collision-line visits by
the origin and every non-collision state by one fixed nonzero lattice point. -/
private def axisBlockedFreePairCollisionIndicatorOwnerProcess :
    ℕ → Ωq → LatticePoint 3 :=
  fun n ω ↦
    if axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∈ axisBlockedDefectCollisionLine then
      0
    else
      Pi.single 0 (1 : ℤ)

/-- Helper for Exercise 18.2.4: for the direct collision-indicator owner witness, avoiding the
origin is exactly the launched collision-line avoidance event. -/
private theorem
    axisBlockedFreePairCollisionIndicatorOwnerProcess_avoidOrigin_eq_preimage_latticeAvoid :
    {ω | ∀ n : ℕ,
        axisBlockedFreePairCollisionIndicatorOwnerProcess (Xq := Xq) n ω ≠ 0} =
      (fun ω : Ωq ↦ axisBlockedFreePairLatticePath (fun n : ℕ ↦ Xq n ω)) ⁻¹'
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  have hone : (Pi.single 0 (1 : ℤ) : LatticePoint 3) ≠ 0 := by
    intro h
    have h0 := congrArg (fun z : LatticePoint 3 ↦ z 0) h
    simp at h0
  ext ω
  -- Proof comment: the witness process only hits `0` exactly when the encoded `ℤ^3` path lies on
  -- the collision line, so pointwise origin avoidance is the same event as pathwise collision-line
  -- avoidance.
  simp [axisBlockedFreePairCollisionIndicatorOwnerProcess,
    axisBlockedDefectAvoidCollisionLinePathEvent, hone]

/-- Helper for Exercise 18.2.4: `latticeAvoidOriginUpToPathEvent n` records that a lattice path
stays away from the origin through time `n`. -/
private def latticeAvoidOriginUpToPathEvent (n : ℕ) : Set (ℕ → LatticePoint 3) :=
  {path | ∀ m ≤ n, path m ≠ 0}

/-- Helper for Exercise 18.2.4: bounded origin avoidance on `ℤ^3` path space is measurable. -/
private theorem measurableSet_latticeAvoidOriginUpToPathEvent (n : ℕ) :
    MeasurableSet (latticeAvoidOriginUpToPathEvent n) := by
  have hrepr :
      latticeAvoidOriginUpToPathEvent n =
        ⋂ m : ℕ,
          if m ≤ n then
            {path : ℕ → LatticePoint 3 | path m ≠ 0}
          else
            Set.univ := by
    ext path
    simp [latticeAvoidOriginUpToPathEvent]
  rw [hrepr]
  refine MeasurableSet.iInter fun m ↦ ?_
  by_cases hm : m ≤ n
  · have hzero :
        MeasurableSet {path : ℕ → LatticePoint 3 | path m = 0} := by
      exact (measurable_pi_apply m) (measurableSet_singleton 0)
    -- Proof comment: on the active coordinates `m ≤ n`, bounded origin avoidance is the
    -- complement of the time-`m` origin event.
    simpa [hm, Set.setOf_app_iff] using hzero.compl
  · simp [hm]

/-- Helper for Exercise 18.2.4: full origin avoidance is the decreasing intersection of the
bounded origin-avoidance events. -/
private theorem latticeAvoidOriginPathEvent_eq_iInter_bounded :
    ({path : ℕ → LatticePoint 3 | ∀ n : ℕ, path n ≠ 0} : Set (ℕ → LatticePoint 3)) =
      ⋂ n : ℕ, latticeAvoidOriginUpToPathEvent n := by
  ext path
  constructor
  · intro hpath
    refine Set.mem_iInter.2 ?_
    intro n
    exact fun m _ ↦ hpath m
  · intro hpath n
    exact (Set.mem_iInter.1 hpath n) n le_rfl

/-- Helper for Exercise 18.2.4: `axisBlockedDefectAvoidCollisionLineUpToPathEvent n` records that
an encoded `ℤ^3` path stays off the collision line through time `n`. -/
private def axisBlockedDefectAvoidCollisionLineUpToPathEvent (n : ℕ) :
    Set (ℕ → LatticePoint 3) :=
  {path | ∀ m ≤ n, path m ∉ axisBlockedDefectCollisionLine}

/-- Helper for Exercise 18.2.4: bounded collision-line avoidance on encoded `ℤ^3` path space is
measurable. -/
private theorem measurableSet_axisBlockedDefectAvoidCollisionLineUpToPathEvent (n : ℕ) :
    MeasurableSet (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
  have hrepr :
      axisBlockedDefectAvoidCollisionLineUpToPathEvent n =
        ⋂ m : ℕ,
          if m ≤ n then
            {path : ℕ → LatticePoint 3 | path m ∉ axisBlockedDefectCollisionLine}
          else
            Set.univ := by
    ext path
    simp [axisBlockedDefectAvoidCollisionLineUpToPathEvent]
  rw [hrepr]
  refine MeasurableSet.iInter fun m ↦ ?_
  by_cases hm : m ≤ n
  · have hline :
        MeasurableSet {path : ℕ → LatticePoint 3 | path m ∈ axisBlockedDefectCollisionLine} := by
      exact (measurable_pi_apply m) MeasurableSet.of_discrete
    -- Proof comment: on the active coordinates `m ≤ n`, bounded collision-line avoidance is the
    -- complement of the time-`m` collision-line membership event.
    simpa [hm, Set.setOf_app_iff] using hline.compl
  · simp [hm]

/-- Helper for Exercise 18.2.4: full collision-line avoidance is the decreasing intersection of
the bounded collision-line-avoidance events. -/
private theorem axisBlockedDefectAvoidCollisionLinePathEvent_eq_iInter_bounded :
    axisBlockedDefectAvoidCollisionLinePathEvent =
      ⋂ n : ℕ, axisBlockedDefectAvoidCollisionLineUpToPathEvent n := by
  ext path
  constructor
  · intro hpath
    refine Set.mem_iInter.2 ?_
    intro n
    exact fun m _ ↦ hpath m
  · intro hpath n
    exact (Set.mem_iInter.1 hpath n) n le_rfl

/-- Helper for Exercise 18.2.4: absorbing the origin freezes `0` and leaves every nonzero row of
the step matrix unchanged. -/
private def absorbAtOriginStepMatrix {E : Type*} [Zero E]
    (q : E → E → ℝ≥0∞) : E → E → ℝ≥0∞
  | z, w =>
      if hz : z = 0 then
        if w = 0 then 1 else 0
      else
        q z w

/-- Helper for Exercise 18.2.4: the absorbed kernel row at the origin is the Dirac mass at `0`.
-/
private theorem absorbAtOriginStepMatrix_apply_origin
    {E : Type*} [Zero E] {q : E → E → ℝ≥0∞} (w : E) :
    absorbAtOriginStepMatrix q 0 w = if w = 0 then 1 else 0 := by
  simp [absorbAtOriginStepMatrix]

/-- Helper for Exercise 18.2.4: away from the origin, the absorbed kernel agrees with the
original step matrix. -/
private theorem absorbAtOriginStepMatrix_apply_of_ne_origin
    {E : Type*} [Zero E] {q : E → E → ℝ≥0∞} {z w : E} (hz : z ≠ 0) :
    absorbAtOriginStepMatrix q z w = q z w := by
  simp [absorbAtOriginStepMatrix, hz]

/-- Helper for Exercise 18.2.4: absorbing the origin preserves stochasticity of the original
matrix. -/
private theorem absorbAtOriginStepMatrix_isStochastic
    {E : Type*} [Zero E]
    (q : E → E → ℝ≥0∞) (hq : IsStochasticMatrix q) :
    IsStochasticMatrix (absorbAtOriginStepMatrix q) := by
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [tsum_eq_single 0]
    · simp [absorbAtOriginStepMatrix]
    · intro w hw
      simp [absorbAtOriginStepMatrix, hw]
  · simp [absorbAtOriginStepMatrix, hz, hq z]

/-- Helper for Exercise 18.2.4: bounded origin avoidance with endpoint `w` records that the
process stays off `0` through time `n` and lands at `w` at time `n`. -/
private def avoidOriginUntilWithEndpoint
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [Zero E]
    (X : ℕ → Ω → E) (n : ℕ) (w : E) : Set Ω :=
  {ω | X n ω = w ∧ ∀ m ≤ n, X m ω ≠ 0}

/-- Helper for Exercise 18.2.4: the bounded endpoint-refined origin-avoidance event is measurable
for the time-`n` history filtration. -/
private theorem avoidOriginUntilWithEndpoint_measurableSet
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [MeasurableSpace E] [DiscreteMeasurableSpace E] [Zero E]
    {X : ℕ → Ω → E} (hX : ∀ n : ℕ, Measurable (X n))
    (n : ℕ) (w : E) :
    MeasurableSet[generatedFiltrationSpace X n] (avoidOriginUntilWithEndpoint X n w) := by
  have hState :
      MeasurableSet[generatedFiltrationSpace X n] {ω | X n ω = w} := by
    have hXn : Measurable[generatedFiltrationSpace X n] (X n) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := X) n
    rw [show ({ω | X n ω = w} : Set Ω) = X n ⁻¹' ({w} : Set E) by
      ext ω
      simp]
    exact hXn (measurableSet_singleton w)
  have hAvoid :
      MeasurableSet[generatedFiltrationSpace X n] {ω | ∀ m ≤ n, X m ω ≠ 0} := by
    have hrepr :
        {ω | ∀ m ≤ n, X m ω ≠ 0} =
          ⋂ m : ℕ,
            if m ≤ n then
              {ω | X m ω ≠ 0}
            else
              Set.univ := by
      ext ω
      simp
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : m ≤ n
    · have hXm : Measurable[generatedFiltrationSpace X n] (X m) := by
        exact Measurable.of_comap_le <|
          le_iSup_of_le m <| le_iSup_of_le hm le_rfl
      -- Proof comment: on the active coordinates `m ≤ n`, bounded origin avoidance is the
      -- complement of the time-`m` origin event.
      simpa [hm, Set.setOf_app_iff] using
        (hXm (measurableSet_singleton (0 : E))).compl
    · simp [hm]
  -- Proof comment: both the endpoint and the bounded origin-avoidance conditions are determined
  -- by the time-`n` history.
  simpa [avoidOriginUntilWithEndpoint] using hState.inter hAvoid

/-- Helper for Exercise 18.2.4: asking for endpoint `0` is incompatible with bounded origin
avoidance. -/
private theorem avoidOriginUntilWithEndpoint_eq_empty_of_origin
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [Zero E]
    {X : ℕ → Ω → E} (n : ℕ) :
    avoidOriginUntilWithEndpoint X n 0 = (∅ : Set Ω) := by
  ext ω
  constructor
  · intro hω
    exact False.elim <| (hω.2 n le_rfl) hω.1
  · simp [avoidOriginUntilWithEndpoint]

/-- Helper for Exercise 18.2.4: bounded origin avoidance with a nonzero endpoint equals the
corresponding singleton mass of the origin-absorbed kernel. -/
private theorem avoidOriginEndpointProb_eq_absorbedEndpointMass
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E] [Zero E]
    {q : E → E → ENNReal}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtOriginStepMatrix q))] :
    ∀ n : ℕ, ∀ z : E, ∀ {w : E}, w ≠ 0 →
      (P z : Measure Ω) (avoidOriginUntilWithEndpoint X n w) =
        ((discreteMatrixKernel (absorbAtOriginStepMatrix q) ^ n) z) ({w} : Set E) := by
  let κAbs : Kernel E E := discreteMatrixKernel (absorbAtOriginStepMatrix q)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  intro n
  induction n with
  | zero =>
      intro z w hw
      have hset :
          avoidOriginUntilWithEndpoint X 0 w = {ω | X 0 ω = w} := by
        ext ω
        constructor
        · intro hω
          exact hω.1
        · intro hω
          refine ⟨hω, ?_⟩
          intro m hm
          have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
          subst hm0
          intro hzero
          exact hw (hω.symm.trans hzero)
      -- Proof comment: at time `0`, the endpoint condition already forces origin avoidance.
      rw [hset]
      rw [show ({ω | X 0 ω = w} : Set Ω) = X 0 ⁻¹' ({w} : Set E) by
        ext ω
        simp]
      rw [← Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton w)]
      rw [hReal.transition_eq z 0]
      simp [κAbs, Kernel.id_apply, hw]
  | succ n ih =>
      intro z w hw
      let μ : Measure Ω := (P z : Measure Ω)
      have hUnion :
          avoidOriginUntilWithEndpoint X (n + 1) w =
            ⋃ c : E, avoidOriginUntilWithEndpoint X n c ∩ {ω | X (n + 1) ω = w} := by
        ext ω
        constructor
        · intro hω
          refine Set.mem_iUnion.2 ⟨X n ω, ?_⟩
          refine ⟨?_, hω.1⟩
          refine ⟨rfl, ?_⟩
          intro m hm
          exact hω.2 m (Nat.le_trans hm (Nat.le_succ _))
        · intro hω
          rcases Set.mem_iUnion.1 hω with ⟨c, hcω⟩
          refine ⟨hcω.2, ?_⟩
          intro m hm
          rcases Nat.eq_or_lt_of_le hm with rfl | hm_lt
          · intro hzero
            exact hw (hcω.2.symm.trans hzero)
          · exact hcω.1.2 m (Nat.le_of_lt_succ hm_lt)
      have hPairwise :
          Pairwise fun c d : E ↦
            Disjoint
              (avoidOriginUntilWithEndpoint X n c ∩ {ω | X (n + 1) ω = w})
              (avoidOriginUntilWithEndpoint X n d ∩ {ω | X (n + 1) ω = w}) := by
        intro c d hcd
        refine Set.disjoint_left.2 ?_
        intro ω hc hd
        apply hcd
        exact hc.1.1.symm.trans hd.1.1
      have hMeas :
          ∀ c : E,
            MeasurableSet
              (avoidOriginUntilWithEndpoint X n c ∩ {ω | X (n + 1) ω = w}) := by
        intro c
        have hAvoid_hist :
            MeasurableSet[generatedFiltrationSpace X n]
              (avoidOriginUntilWithEndpoint X n c) :=
          avoidOriginUntilWithEndpoint_measurableSet hReal.measurable_process n c
        have hAvoid :
            MeasurableSet (avoidOriginUntilWithEndpoint X n c) := by
          exact (generatedHistory_le_ambient X hReal.measurable_process n) _ hAvoid_hist
        have hState :
            MeasurableSet ({ω | X (n + 1) ω = w} : Set Ω) := by
          rw [show ({ω | X (n + 1) ω = w} : Set Ω) =
              X (n + 1) ⁻¹' ({w} : Set E) by
            ext ω
            simp]
          exact (hReal.measurable_process (n + 1)) (measurableSet_singleton w)
        exact hAvoid.inter hState
      -- Proof comment: decompose by the time-`n` endpoint, factor each history slice through the
      -- free one-step row, and then replace that row by the absorbed row away from `0`.
      calc
        μ (avoidOriginUntilWithEndpoint X (n + 1) w) =
            ∑' c : E, μ (avoidOriginUntilWithEndpoint X n c ∩ {ω | X (n + 1) ω = w}) := by
              rw [hUnion]
              exact MeasureTheory.measure_iUnion hPairwise hMeas
        _ =
            ∑' c : E,
              (discreteMatrixKernel (absorbAtOriginStepMatrix q) c ({w} : Set E)) *
                ((κAbs ^ n) z) ({c} : Set E) := by
                  refine tsum_congr fun c ↦ ?_
                  by_cases hc : c ≠ 0
                  · have hAvoid_meas :
                        MeasurableSet (avoidOriginUntilWithEndpoint X n c) := by
                      have hAvoid_hist :
                          MeasurableSet[generatedFiltrationSpace X n]
                            (avoidOriginUntilWithEndpoint X n c) :=
                        avoidOriginUntilWithEndpoint_measurableSet hReal.measurable_process n c
                      exact
                        (generatedHistory_le_ambient X hReal.measurable_process n) _
                          hAvoid_hist
                    have hAvoid_hist :
                        MeasurableSet[generatedFiltrationSpace X n]
                          (avoidOriginUntilWithEndpoint X n c) :=
                      avoidOriginUntilWithEndpoint_measurableSet hReal.measurable_process n c
                    have hAvoid_state :
                        ∀ ⦃ω : Ω⦄, ω ∈ avoidOriginUntilWithEndpoint X n c → X n ω = c := by
                      intro ω hω
                      exact hω.1
                    rw [measureInter_eq_mul_stepMass_of_stateEvent
                      (q := q) (P := P) (X := X) z c w n
                      (avoidOriginUntilWithEndpoint X n c)
                      hAvoid_meas hAvoid_hist hAvoid_state]
                    rw [ih z hc, discreteMatrixKernel_apply_singleton,
                      discreteMatrixKernel_apply_singleton]
                    simpa [κAbs, absorbAtOriginStepMatrix, hc]
                  · have hczero : c = 0 := by simpa using hc
                    subst hczero
                    have hrow_zero :
                        discreteMatrixKernel (absorbAtOriginStepMatrix q) 0 ({w} : Set E) = 0 := by
                      rw [discreteMatrixKernel_apply_singleton, absorbAtOriginStepMatrix_apply_origin]
                      simp [hw]
                    rw [avoidOriginUntilWithEndpoint_eq_empty_of_origin (X := X) n]
                    rw [hrow_zero]
                    simp
        _ = ((κAbs ^ (n + 1)) z) ({w} : Set E) := by
              -- Proof comment: normalize the absorbed successor step to the same singleton-mass
              -- series used on the previous line.
              rw [Kernel.pow_succ_apply_eq_lintegral κAbs n z (measurableSet_singleton w)]
              rw [MeasureTheory.lintegral_countable']

/-- Helper for Exercise 18.2.4: the nonorigin mass of the absorbed kernel is exactly the bounded
origin-avoidance probability of the free walk. -/
private theorem absorbedNonoriginMass_eq_boundedAvoidOriginProb
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E] [Zero E]
    {q : E → E → ENNReal}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtOriginStepMatrix q))]
    (z : E) (n : ℕ) :
    ((discreteMatrixKernel (absorbAtOriginStepMatrix q) ^ n) z) {w : E | w ≠ 0} =
      (P z : Measure Ω) {ω | ∀ m ≤ n, X m ω ≠ 0} := by
  let κAbs : Kernel E E := discreteMatrixKernel (absorbAtOriginStepMatrix q)
  let offOrigin : Set E := {w : E | w ≠ 0}
  let μ : Measure Ω := (P z : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  have hMass :
      ((κAbs ^ n) z) offOrigin =
        ∑' w : {u : E // u ∈ offOrigin},
          ((κAbs ^ n) z) ({(w : E)} : Set E) := by
    calc
      ((κAbs ^ n) z) offOrigin =
          ∑' w : E,
            offOrigin.indicator (fun w ↦ ((κAbs ^ n) z) ({w} : Set E)) w := by
              simpa using
                (Measure.tsum_indicator_apply_singleton ((κAbs ^ n) z) offOrigin
                  (show MeasurableSet offOrigin from MeasurableSet.of_discrete)).symm
      _ =
          ∑' w : {u : E // u ∈ offOrigin},
            ((κAbs ^ n) z) ({(w : E)} : Set E) := by
              rw [← tsum_subtype offOrigin
                (fun w : E ↦ ((κAbs ^ n) z) ({w} : Set E))]
  have hUnion :
      {ω | ∀ m ≤ n, X m ω ≠ 0} =
        ⋃ w : {u : E // u ∈ offOrigin}, avoidOriginUntilWithEndpoint X n w := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨⟨X n ω, hω n le_rfl⟩, ?_⟩
      exact ⟨rfl, hω⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨w, hw⟩
      exact hw.2
  have hAvoid :
      μ {ω | ∀ m ≤ n, X m ω ≠ 0} =
        ∑' w : {u : E // u ∈ offOrigin}, μ (avoidOriginUntilWithEndpoint X n w) := by
    have hPairwise :
        Pairwise fun w₁ w₂ : {u : E // u ∈ offOrigin} ↦
          Disjoint
            (avoidOriginUntilWithEndpoint X n (w₁ : E))
            (avoidOriginUntilWithEndpoint X n (w₂ : E)) := by
          intro w₁ w₂ hw
          refine Set.disjoint_left.2 ?_
          intro ω h₁ h₂
          apply hw
          exact Subtype.ext <| h₁.1.symm.trans h₂.1
    have hMeas :
        ∀ w : {u : E // u ∈ offOrigin},
          MeasurableSet (avoidOriginUntilWithEndpoint X n (w : E)) := by
          intro w
          have hAvoid_hist :
              MeasurableSet[generatedFiltrationSpace X n]
                (avoidOriginUntilWithEndpoint X n (w : E)) :=
            avoidOriginUntilWithEndpoint_measurableSet hReal.measurable_process n (w : E)
          exact (generatedHistory_le_ambient X hReal.measurable_process n) _ hAvoid_hist
    rw [hUnion]
    exact MeasureTheory.measure_iUnion hPairwise hMeas
  -- Proof comment: decompose the absorbed nonorigin mass into singleton endpoints and match each
  -- singleton mass with the corresponding bounded endpoint-refined avoid-origin event.
  calc
    ((κAbs ^ n) z) offOrigin =
        ∑' w : {u : E // u ∈ offOrigin},
          ((κAbs ^ n) z) ({(w : E)} : Set E) := hMass
    _ =
        ∑' w : {u : E // u ∈ offOrigin},
          μ (avoidOriginUntilWithEndpoint X n w) := by
            refine tsum_congr fun w ↦ ?_
            symm
            simpa [μ, offOrigin] using
              avoidOriginEndpointProb_eq_absorbedEndpointMass
                (q := q) (P := P) (X := X) n z (w := (w : E)) w.2
    _ = μ {ω | ∀ m ≤ n, X m ω ≠ 0} := hAvoid.symm

/-- Helper for Exercise 18.2.4: for the direct collision-indicator owner witness, bounded origin
avoidance is exactly bounded launched collision-line avoidance. -/
private theorem
    axisBlockedFreePairCollisionIndicatorOwnerProcess_avoidOriginUpTo_eq_preimage_latticeAvoidUpTo
    (n : ℕ) :
    {ω | ∀ m ≤ n,
        axisBlockedFreePairCollisionIndicatorOwnerProcess (Xq := Xq) m ω ≠ 0} =
      (fun ω : Ωq ↦ axisBlockedFreePairLatticePath (fun k : ℕ ↦ Xq k ω)) ⁻¹'
        axisBlockedDefectAvoidCollisionLineUpToPathEvent n := by
  have hone : (Pi.single 0 (1 : ℤ) : LatticePoint 3) ≠ 0 := by
    intro h
    have h0 := congrArg (fun z : LatticePoint 3 ↦ z 0) h
    simp at h0
  ext ω
  -- Proof comment: the direct witness process hits `0` exactly at collision-line times, so the
  -- bounded avoid-origin event is the same coordinatewise condition as bounded collision-line
  -- avoidance of the launched encoded path.
  simp [axisBlockedFreePairCollisionIndicatorOwnerProcess,
    axisBlockedDefectAvoidCollisionLineUpToPathEvent, axisBlockedFreePairLatticePath, hone]

/-- Helper for Exercise 18.2.4: under the launched law, the bounded avoid-origin event of the
direct collision-indicator owner process has exactly the launched bounded collision-line
avoidance mass. -/
private theorem
    axisBlockedFreePair_collisionIndicatorOwnerBoundedAvoidProb_eq_launchCollisionAvoidProb
    (n : ℕ) :
    ((Pq ((((1, 0) : AxisState), ((1, 1) : AxisState))) : Measure Ωq)
      {ω | ∀ m ≤ n,
          axisBlockedFreePairCollisionIndicatorOwnerProcess (Xq := Xq) m ω ≠ 0}) =
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq := (Pq b : Measure Ωq)
  calc
    μ {ω | ∀ m ≤ n,
        axisBlockedFreePairCollisionIndicatorOwnerProcess (Xq := Xq) m ω ≠ 0} =
      μ ((fun ω : Ωq ↦ axisBlockedFreePairLatticePath (fun k : ℕ ↦ Xq k ω)) ⁻¹'
        axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
          rw [axisBlockedFreePairCollisionIndicatorOwnerProcess_avoidOriginUpTo_eq_preimage_latticeAvoidUpTo
            (Xq := Xq) n]
    _ =
        Measure.map
          (fun ω : Ωq ↦ axisBlockedFreePairLatticePath (fun k : ℕ ↦ Xq k ω))
          μ (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
            rw [Measure.map_apply
              (measurable_axisBlockedFreePairLatticePath.comp
                measurable_independentProductPairTrajectoryMap)
              (measurableSet_axisBlockedDefectAvoidCollisionLineUpToPathEvent n)]
    _ =
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
          (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
            rw [independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq) b]
            rw [Measure.map_map measurable_independentProductPairTrajectoryMap
              measurable_axisBlockedFreePairLatticePath]
            rfl

/-- Helper for Exercise 18.2.4: once every bounded origin-avoidance mass is dominated by the
corresponding bounded collision-line-avoidance mass, continuity from above yields the full
infinite-horizon comparison. -/
private theorem boundedAvoidComparison_implies_fullAvoidComparison
    (μ ν : Measure (ℕ → LatticePoint 3))
    (hfinite :
      ∀ n : ℕ,
        μ (latticeAvoidOriginUpToPathEvent n) ≤
          ν (axisBlockedDefectAvoidCollisionLineUpToPathEvent n)) :
    μ {path | ∀ n : ℕ, path n ≠ 0} ≤
      ν axisBlockedDefectAvoidCollisionLinePathEvent := by
  have hAntiOrigin : Antitone latticeAvoidOriginUpToPathEvent := by
    intro n m hnm path hpath k hk
    exact hpath k (le_trans hk hnm)
  have hAntiCollision : Antitone axisBlockedDefectAvoidCollisionLineUpToPathEvent := by
    intro n m hnm path hpath k hk
    exact hpath k (le_trans hk hnm)
  have hμ_tendsto :
      Tendsto
        (fun n ↦ μ (latticeAvoidOriginUpToPathEvent n))
        atTop
        (nhds (μ (⋂ n : ℕ, latticeAvoidOriginUpToPathEvent n))) := by
    -- Proof comment: the bounded origin-avoidance events form a decreasing measurable family, so
    -- `μ` is continuous from above along that sequence.
    exact
      tendsto_measure_iInter_atTop
        (μ := μ)
        (s := latticeAvoidOriginUpToPathEvent)
        (fun n ↦ (measurableSet_latticeAvoidOriginUpToPathEvent n).nullMeasurableSet)
        hAntiOrigin
        ⟨0, measure_ne_top _ _⟩
  have hν_tendsto :
      Tendsto
        (fun n ↦ ν (axisBlockedDefectAvoidCollisionLineUpToPathEvent n))
        atTop
        (nhds (ν (⋂ n : ℕ, axisBlockedDefectAvoidCollisionLineUpToPathEvent n))) := by
    -- Proof comment: the same continuity-from-above argument applies to the bounded encoded
    -- collision-line-avoidance events under `ν`.
    exact
      tendsto_measure_iInter_atTop
        (μ := ν)
        (s := axisBlockedDefectAvoidCollisionLineUpToPathEvent)
        (fun n ↦ (measurableSet_axisBlockedDefectAvoidCollisionLineUpToPathEvent n).nullMeasurableSet)
        hAntiCollision
        ⟨0, measure_ne_top _ _⟩
  -- Proof comment: compare the bounded-avoidance masses termwise and pass to the limits given by
  -- the two continuity-from-above identities.
  simpa [latticeAvoidOriginPathEvent_eq_iInter_bounded,
    axisBlockedDefectAvoidCollisionLinePathEvent_eq_iInter_bounded] using
    (le_of_tendsto_of_tendsto' hμ_tendsto hν_tendsto hfinite)

/-- Helper for Exercise 18.2.4: the canonical symmetric simple random walk step matrix on `ℤ^3`
is stochastic. -/
private theorem symmetricSimpleRandomWalk3_stepMatrix_isStochastic :
    IsStochasticMatrix (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) := by
  -- Proof comment: each row of the discrete kernel is a probability measure, so evaluating that
  -- row on the full space gives exactly the required row sum `1`.
  intro x
  simpa using
    (discreteMatrixKernel_univ
      (K := latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) x)

/-- Helper for Exercise 18.2.4: the distinguished start pair `((0,0),(0,1))` normalizes to the
nonzero collision code `![0,-1]`. -/
private theorem axisBlockedDefectCollisionCode_start :
    axisBlockedDefectCollisionCode
      (freePairRelativeStateToLatticePoint3
        (axisBlockedFreePairRelativeState
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))) = ![0, -1] := by
  -- Proof comment: first normalize the start pair in relative coordinates, then collapse the
  -- collision line by taking the horizontal and vertical differences.
  rw [axisBlockedFreePairRelativeState_start]
  norm_num [axisBlockedDefectCollisionCode, freePairRelativeStateToLatticePoint3]

/-- Helper for Exercise 18.2.4: the distinguished start pair `((0,0),(0,1))` also normalizes to
the sampled-owner start point `![0,0,-1]`. -/
private theorem axisBlockedFreePairLatticePoint_start :
    freePairRelativeStateToLatticePoint3
      (axisBlockedFreePairRelativeState
        ((((0, 0) : AxisState), ((0, 1) : AxisState)))) = ![0, 0, -1] := by
  -- Proof comment: first rewrite the start pair into relative coordinates, then expand the
  -- canonical `ℤ^3` owner encoding of that relative state.
  rw [axisBlockedFreePairRelativeState_start]
  norm_num [freePairRelativeStateToLatticePoint3]

/-- Helper for Exercise 18.2.4: sample the defect collision code at time `0` and then at the
successive defect-visit owner states. -/
private def axisBlockedFreePairSampledCollisionCodeProcess :
    ℕ → Ωq → LatticePoint 2 :=
  fun n ω ↦
    axisBlockedDefectCollisionCode
      (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) n ω)

/-- Helper for Exercise 18.2.4: each time slice of the sampled collision-code process is
measurable because it is a discrete postcomposition of the sampled owner process. -/
private theorem axisBlockedFreePairSampledCollisionCodeProcess_measurable
    (n : ℕ) :
    Measurable (axisBlockedFreePairSampledCollisionCodeProcess (Xq := Xq) n) := by
  -- Proof comment: `axisBlockedDefectCollisionCode` lands in the discrete space `ℤ²`, so
  -- measurability is inherited from the already-established sampled owner measurability.
  exact
    (measurable_of_countable (f := axisBlockedDefectCollisionCode)).comp
      (axisBlockedFreePairDefectVisitOwnerProcess_measurable (Xq := Xq) n)

/-- Helper for Exercise 18.2.4: under the distinguished start state, the sampled collision-code
process starts from the normalized nonzero code `![0,-1]`. -/
private theorem axisBlockedFreePairSampledCollisionCodeProcess_initial_eq_start
    {ω : Ωq}
    (hstart : Xq 0 ω = ((((0, 0) : AxisState), ((0, 1) : AxisState)))) :
    axisBlockedFreePairSampledCollisionCodeProcess (Xq := Xq) 0 ω = ![0, -1] := by
  -- Proof comment: time `0` of the sampled process is just the start owner state, and the start
  -- pair was already normalized to the defect collision code `![0,-1]`.
  simpa [axisBlockedFreePairSampledCollisionCodeProcess, hstart] using
    axisBlockedDefectCollisionCode_start

/-- Helper for Exercise 18.2.4: under the start-side owner law, the sampled collision-code
process starts from the point mass at `![0,-1]`. -/
private theorem axisBlockedFreePairSampledCollisionCodeProcess_initial_eq :
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![0, 0, -1] : Measure Ωq).map
        (axisBlockedFreePairSampledCollisionCodeProcess (Xq := Xq) 0) =
      Measure.dirac (![0, -1] : LatticePoint 2) := by
  -- Proof comment: first use the sampled owner initial law at `![0,0,-1]`, then collapse the
  -- collision line by one further pushforward through `axisBlockedDefectCollisionCode`.
  calc
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![0, 0, -1] : Measure Ωq).map
        (axisBlockedFreePairSampledCollisionCodeProcess (Xq := Xq) 0) =
      ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![0, 0, -1] : Measure Ωq).map
          (axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) 0)).map
        axisBlockedDefectCollisionCode := by
          rw [Measure.map_map
            (axisBlockedFreePairDefectVisitOwnerProcess_measurable (Xq := Xq) 0)
            (measurable_of_countable (f := axisBlockedDefectCollisionCode))]
          rfl
    _ = (Measure.dirac (![0, 0, -1] : LatticePoint 3)).map axisBlockedDefectCollisionCode := by
          rw [axisBlockedFreePairDefectVisitOwnerProcess_initial_eq (Pq := Pq) (Xq := Xq)
            (![0, 0, -1] : LatticePoint 3)]
    _ = Measure.dirac (![0, -1] : LatticePoint 2) := by
          simp [axisBlockedDefectCollisionCode]

/-- Helper for Exercise 18.2.4: along a path started from `((0,0),(0,1))`, full collision-code
avoidance already forces every sampled defect-visit owner state to stay away from the origin. -/
private theorem axisBlockedFreePairDefectVisitOwnerProcess_ne_zero_of_startCollisionCodeNoHit
    {ω : Ωq}
    (hstart : Xq 0 ω = ((((0, 0) : AxisState), ((0, 1) : AxisState))))
    (hnohit :
      ∀ n : ℕ,
        axisBlockedFreePairCollisionCodePath (fun m : ℕ ↦ Xq m ω) n ≠ 0) :
    ∀ k : ℕ, axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) k ω ≠ 0 := by
  intro k
  cases k with
  | zero =>
      -- Proof comment: at time `0`, the sampled owner is exactly the normalized start point
      -- `![0,0,-1]`, which is visibly nonzero.
      simpa [axisBlockedFreePairDefectVisitOwnerProcess, hstart,
        axisBlockedFreePairLatticePoint_start] using
        axisBlockedFreePairDefectVisitOwnerStartPoint_ne_zero
  | succ n =>
      let k' : ℕ+ := ⟨n + 1, Nat.succ_pos _⟩
      have hk :
          axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) (n + 1) ω =
            axisBlockedFreePairDefectVisitOwner (Xq := Xq) k' ω := by
        simpa [k'] using axisBlockedFreePairDefectVisitOwnerProcess_pNat (Xq := Xq) k'
      by_cases hfinite :
          (τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k') ω = ⊤
      · -- Proof comment: if the sampled defect-visit time is infinite, `stoppedValue` falls back
        -- to time `0`, so the sampled owner is still the nonzero start point.
        have hvalue :
            axisBlockedFreePairDefectVisitOwner (Xq := Xq) k' ω = ![0, 0, -1] := by
          unfold axisBlockedFreePairDefectVisitOwner
          simpa [hfinite, hstart, axisBlockedFreePairLatticePoint_start]
        intro hzero
        rw [hk] at hzero
        exact axisBlockedFreePairDefectVisitOwnerStartPoint_ne_zero <| by
          simpa [hvalue] using hzero
      · -- Proof comment: on a finite sampled defect-visit slice, a sampled owner value `0`
        -- forces collision code `0` at that sampled time, contradicting full collision-code
        -- avoidance.
        intro hzero
        rw [hk] at hzero
        have hcode_zero :
            axisBlockedDefectCollisionCode
                (freePairRelativeStateToLatticePoint3
                  (axisBlockedFreePairRelativeState
                    (Xq (((τ_[axisBlockedFreePairDefectVisitIndicator (Xq := Xq), 0]^k') ω).untopA)
                      ω))) =
              0 :=
          axisBlockedFreePairCollisionCode_eq_zero_of_defectVisitOwner_eq_zero_at_iteratedVisit
            (Xq := Xq) hfinite hzero
        exact hnohit _ <| by
          simpa [axisBlockedFreePairCollisionCodePath] using hcode_zero

/-- Helper for Exercise 18.2.4: under the distinguished start condition, full collision-code
avoidance is contained in sampled-owner origin avoidance. -/
private theorem axisBlockedFreePair_startCollisionCodeNoHit_subset_sampledOwnerAvoidOrigin :
    {ω : Ωq |
        Xq 0 ω = ((((0, 0) : AxisState), ((0, 1) : AxisState))) ∧
          ∀ n : ℕ, axisBlockedFreePairCollisionCodePath (fun m : ℕ ↦ Xq m ω) n ≠ 0} ⊆
      {ω : Ωq | ∀ k : ℕ, axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) k ω ≠ 0} := by
  intro ω hω
  exact
    axisBlockedFreePairDefectVisitOwnerProcess_ne_zero_of_startCollisionCodeNoHit
      (Xq := Xq) hω.1 hω.2

/-- Helper for Exercise 18.2.4: under the distinguished start law, the full collision-code no-hit
mass is bounded above by sampled-owner origin avoidance. -/
private theorem axisBlockedFreePair_startCollisionCodeNoHitMass_le_sampledOwnerAvoid :
    Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent ≤
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![0, 0, -1] : Measure Ωq)
        {ω : Ωq | ∀ k : ℕ, axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) k ω ≠ 0} := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  let μ : Measure Ωq := (Pq a : Measure Ωq)
  let noHit : Set Ωq :=
    {ω : Ωq | ∀ n : ℕ, axisBlockedFreePairCollisionCodePath (fun m : ℕ ↦ Xq m ω) n ≠ 0}
  let init : Set Ωq := {ω : Ωq | Xq 0 ω = a}
  let sampledAvoid : Set Ωq :=
    {ω : Ωq | ∀ k : ℕ, axisBlockedFreePairDefectVisitOwnerProcess (Xq := Xq) k ω ≠ 0}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hmass :
      Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a)
          axisBlockedDefectNoHitPathEvent =
        μ noHit := by
    -- Proof comment: expand the realized path-law row back to the start law `μ`, then rewrite
    -- the path-space no-hit event as the corresponding sample-space pointwise event.
    rw [independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq) a]
    rw [Measure.map_map measurable_independentProductPairTrajectoryMap
      measurable_axisBlockedFreePairCollisionCodePath]
    rw [Measure.map_apply
      (measurable_axisBlockedFreePairCollisionCodePath.comp
        measurable_independentProductPairTrajectoryMap)
      measurableSet_axisBlockedDefectNoHitPathEvent]
    simp [μ, noHit, axisBlockedDefectNoHitPathEvent, axisBlockedFreePairCollisionCodePath]
  have hinit_ae : ∀ᵐ ω ∂μ, ω ∈ init := by
    have hprob : μ init = 1 := by
      -- Proof comment: under the realized start law, time `0` is almost surely fixed at the
      -- distinguished start pair.
      simpa [μ, init] using
        independentProductPairRealizationPathKernel_initialState_prob_eq_one
          (Pq := Pq) (Xq := Xq) a
    exact
      (MeasureTheory.mem_ae_iff_prob_eq_one
        (show MeasurableSet init from
          by
            simpa [init] using
              (hqreal.measurable_process 0) (measurableSet_singleton a))).2 hprob
  have hcongr : noHit =ᵐ[μ] init ∩ noHit := by
    -- Proof comment: because the start state holds almost surely under `μ`, intersecting with the
    -- explicit start-state event does not change the collision-code no-hit event.
    filter_upwards [hinit_ae] with ω hωinit
    simp [init, noHit, hωinit]
  have hsubset : init ∩ noHit ⊆ sampledAvoid := by
    -- Proof comment: this is exactly the already-proved one-sided event bridge from full
    -- collision-code no-hit to sampled-owner origin avoidance.
    intro ω hω
    exact axisBlockedFreePair_startCollisionCodeNoHit_subset_sampledOwnerAvoidOrigin
      (Xq := Xq) hω
  calc
    Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a)
        axisBlockedDefectNoHitPathEvent = μ noHit := hmass
    _ = μ (init ∩ noHit) := by
      exact measure_congr hcongr
    _ ≤ μ sampledAvoid := measure_mono hsubset
    _ =
        (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![0, 0, -1] : Measure Ωq)
          sampledAvoid := by
            rw [axisBlockedFreePairDefectVisitOwnerLaw_start (Pq := Pq)]

/-- Helper for Exercise 18.2.4: launch-state never-meet positivity is equivalent to positivity of
the start-pair collision-code no-hit mass, because the existing one-step start/launch bridges run
in both directions. -/
private theorem axisBlockedFreePair_launchNeverMeet_pos_iff_startCollisionCodeNoHit_pos :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent ↔
      0 <
        Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
          axisBlockedDefectNoHitPathEvent := by
  constructor
  · intro hlaunch
    -- Proof comment: the existing start-side bridge already transports positive launched
    -- never-meet mass to positive start collision-code no-hit mass.
    exact
      axisBlockedFreePair_startCollisionCodeNoHit_pos_of_launchNeverMeetPos
        (Pq := Pq) (Xq := Xq) hlaunch
  · intro hstart
    have hlaunchLine :
        0 <
          Measure.map axisBlockedFreePairLatticePath
            (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
              ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Proof comment: conversely, the existing return-step bridge sends positive start
  -- collision-code no-hit mass back to positive launched collision-line avoidance mass.
      exact
        axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_startCollisionCodeNoHit
          (Pq := Pq) (Xq := Xq) hstart
    -- Proof comment: rewrite the launched collision-line avoidance mass back to the launched
    -- never-meet row.
  rw [← axisBlockedFreePair_launchPathKernel_neverMeet_eq_latticeCollisionLineAvoid
      (Pq := Pq) (Xq := Xq)]
  exact hlaunchLine

/-- Helper for Exercise 18.2.4: the enlarged owner boundary surface is the union of the three
coordinate planes `z 0 = 0 ∨ z 1 = 0 ∨ z 2 = 0`. -/
private def axisBlockedFreePairBoundarySurface : Set (LatticePoint 3) :=
  {z | z 0 = 0 ∨ z 1 = 0 ∨ z 2 = 0}

/-- Helper for Exercise 18.2.4: the collision line lies inside the enlarged owner boundary
surface. -/
private theorem axisBlockedDefectCollisionLine_subset_boundarySurface :
    axisBlockedDefectCollisionLine ⊆ axisBlockedFreePairBoundarySurface := by
  intro z hz
  -- Proof comment: every collision-line point satisfies `z 2 = 0`, so it belongs to the union
  -- of the three coordinate planes defining the enlarged boundary surface.
  exact Or.inr <| Or.inr hz.2

/-- Helper for Exercise 18.2.4: mark visits of the raw owner path to the enlarged boundary
surface by a `0/1`-valued process so iterated entrance times can sample them. -/
private def axisBlockedFreePairBoundaryVisitIndicator : ℕ → Ωq → ℤ :=
  fun n ω ↦
    if axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∈
        axisBlockedFreePairBoundarySurface then
      0
    else
      1

/-- Helper for Exercise 18.2.4: the `k`-th sampled boundary state of the raw owner path is the
encoded owner position at the `k`-th visit to `z 0 = 0 ∨ z 1 = 0 ∨ z 2 = 0`. -/
private def axisBlockedFreePairBoundaryVisit
    (k : ℕ+) : Ωq → LatticePoint 3 :=
  fun ω ↦
    stoppedValue
      (fun n ω' ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω') n)
      (fun ω' ↦ (τ_[axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq), 0]^k) ω')
      ω

/-- Helper for Exercise 18.2.4: the boundary-trace owner process starts from the present owner
point and then records the successive sampled visits to the enlarged boundary surface. -/
private def axisBlockedFreePairBoundaryTraceProcess :
    ℕ → Ωq → LatticePoint 3
  | 0 => fun ω ↦ axisBlockedFreePairLatticePath (fun n : ℕ ↦ Xq n ω) 0
  | n + 1 => fun ω ↦
      axisBlockedFreePairBoundaryVisit (Xq := Xq) ⟨n + 1, Nat.succ_pos _⟩ ω

/-- Helper for Exercise 18.2.4: the positive-time coordinates of the boundary-trace process are
exactly the corresponding sampled boundary observables. -/
private theorem axisBlockedFreePairBoundaryTraceProcess_pNat
    (k : ℕ+) :
    axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) k =
      axisBlockedFreePairBoundaryVisit (Xq := Xq) k := by
  cases' k with n hn
  cases n with
  | zero =>
      cases (Nat.not_lt_zero _ hn)
  | succ n =>
      rfl

/-- Helper for Exercise 18.2.4: each time slice of the boundary-trace process is measurable,
because the codomain is the countable lattice `ℤ^3`. -/
private theorem axisBlockedFreePairBoundaryTraceProcess_measurable
    (n : ℕ) :
    Measurable (axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) n) := by
  -- Proof comment: the sampled boundary-trace still lands in a discrete countable state space,
  -- so no additional filtration transport is needed for measurability.
  exact measurable_of_countable
    (f := axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) n)

/-- Helper for Exercise 18.2.4: under the owner start law at `z`, the boundary-trace process
starts from `z` itself. -/
private theorem axisBlockedFreePairBoundaryTraceProcess_initial_eq
    (z : LatticePoint 3) :
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) z : Measure Ωq).map
        (axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 0) =
      Measure.dirac z := by
  -- Proof comment: time `0` of the boundary trace is the same raw owner coordinate as time `0`
  -- of the previously defined sampled defect-visit owner process.
  simpa [axisBlockedFreePairBoundaryTraceProcess, axisBlockedFreePairLatticePath] using
    axisBlockedFreePairDefectVisitOwnerProcess_initial_eq (Pq := Pq) (Xq := Xq) z

/-- Helper for Exercise 18.2.4: under the launched law, time `0` of the boundary trace is the
normalized owner point `![1,1,-1]`. -/
private theorem axisBlockedFreePairBoundaryTraceProcess_initial_eq_launch :
    ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq).map
      (axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 0)) =
      Measure.dirac (![1, 1, -1] : LatticePoint 3) := by
  -- Proof comment: this is the general initial-law identity specialized to the launched owner
  -- point.
  simpa using
    axisBlockedFreePairBoundaryTraceProcess_initial_eq
      (Pq := Pq) (Xq := Xq) (![1, 1, -1] : LatticePoint 3)

/-- Helper for Exercise 18.2.4: the simple-random-walk point `![2,2,-1]` lies off the enlarged
boundary surface `z 0 = 0 ∨ z 1 = 0 ∨ z 2 = 0`. -/
private theorem latticePoint3_twoOneNegOne_not_mem_boundarySurface :
    (![2, 2, -1] : LatticePoint 3) ∉ axisBlockedFreePairBoundarySurface := by
  -- Proof comment: every coordinate of `![2,2,-1]` is nonzero, so it misses all three
  -- coordinate hyperplanes used in the enlarged boundary surface.
  norm_num [axisBlockedFreePairBoundarySurface]

/-- Helper for Exercise 18.2.4: on a finite first boundary-visit slice, the sampled boundary
state is exactly the encoded owner point at that boundary time. -/
private theorem axisBlockedFreePairBoundaryTraceProcess_first_eq_latticePoint_at_boundaryTime
    {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq), 0]^1) ω ≠ ⊤) :
    axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ω =
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω)
        (((τ_[axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq), 0]^1) ω).untopA) := by
  have hτ :
      (τ_[axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq), 0]^1) ω =
        ((τ_[axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq), 0]^1) ω).untopA := by
    rw [WithTop.untopA_eq_untop hfinite]
    symm
    exact WithTop.coe_untop _ hfinite
  change axisBlockedFreePairBoundaryVisit (Xq := Xq) ⟨1, Nat.succ_pos 0⟩ ω = _
  -- Proof comment: on the finite first boundary-visit slice, the stopped-value definition of the
  -- sampled boundary state collapses to the deterministic boundary-visit time.
  unfold axisBlockedFreePairBoundaryVisit
  simpa [hτ] using
    (stoppedValue_eq_on_timeSlice
      (X := fun n ω' ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω') n)
      (τ := fun ω' ↦ (τ_[axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq), 0]^1) ω')
      (ω := ω) (hτω := hτ))

/-- Helper for Exercise 18.2.4: whenever the first boundary-visit time is finite, the first
positive boundary-trace state lies on the enlarged boundary surface. -/
private theorem axisBlockedFreePairBoundaryTraceProcess_first_mem_boundarySurface_of_finite
    {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq), 0]^1) ω ≠ ⊤) :
    axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ω ∈
      axisBlockedFreePairBoundarySurface := by
  let n : ℕ := ((τ_[axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq), 0]^1) ω).untopA
  have hmem :
      axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq) n ω = 0 := by
    have h :
        axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq)
            (MeasureTheory.hittingAfter
              (axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq))
              ({0} : Set ℤ) 1 ω).untopA ω ∈
          ({0} : Set ℤ) :=
      hittingAfter_mem_set_of_ne_top
        (by simpa [iteratedEntranceTime_one] using hfinite)
    simpa [n, iteratedEntranceTime_one, Set.mem_singleton_iff] using h
  have hboundary :
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∈
        axisBlockedFreePairBoundarySurface := by
    unfold axisBlockedFreePairBoundaryVisitIndicator at hmem
    split_ifs at hmem with hboundary
    · exact hboundary
    · norm_num at hmem
  -- Proof comment: the first sampled boundary state is read exactly at a boundary visit, so the
  -- boundary membership transfers directly to the sampled state.
  simpa [n,
    axisBlockedFreePairBoundaryTraceProcess_first_eq_latticePoint_at_boundaryTime
      (Xq := Xq) hfinite] using hboundary

/-- Helper for Exercise 18.2.4: under the launched owner law, the first positive boundary-trace
state can never be the off-surface point `![2,2,-1]`. -/
private theorem axisBlockedFreePairBoundaryTraceProcess_first_ne_twoOneNegOne_ae :
    ∀ᵐ ω ∂(axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq),
      axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ω ≠ ![2, 2, -1] := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hstart :
      ∀ᵐ ω ∂μ, Xq 0 ω = b := by
    have hprob :
        μ {ω | Xq 0 ω = b} = 1 := by
      rw [show {ω | Xq 0 ω = b} = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
        ext ω
        simp]
      rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton b)]
      rw [show μ = (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq) by
        rfl]
      rw [axisBlockedFreePairDefectVisitOwnerLaw_launch (Pq := Pq)]
      rw [hqreal.initial_eq b]
      simp [μ, b]
    exact
      (MeasureTheory.mem_ae_iff_prob_eq_one
        (show MeasurableSet {ω | Xq 0 ω = b} from
          (hqreal.measurable_process 0) (measurableSet_singleton b))).2 hprob
  filter_upwards [hstart] with ω hω0
  by_cases hfinite : (τ_[axisBlockedFreePairBoundaryVisitIndicator (Xq := Xq), 0]^1) ω = ⊤
  · have hvalue :
      axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ω = ![1, 1, -1] := by
      change axisBlockedFreePairBoundaryVisit (Xq := Xq) ⟨1, Nat.succ_pos 0⟩ ω = ![1, 1, -1]
      unfold axisBlockedFreePairBoundaryVisit
      -- Proof comment: on the exceptional top branch, `stoppedValue` falls back to time `0`,
      -- and the launched owner law starts exactly from `![1,1,-1]`.
      simpa [axisBlockedFreePairLatticePoint_launch, hfinite, hω0]
    simpa [hvalue]
  · have hboundary :
        axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ω ∈
          axisBlockedFreePairBoundarySurface :=
      axisBlockedFreePairBoundaryTraceProcess_first_mem_boundarySurface_of_finite
        (Xq := Xq) hfinite
    -- Proof comment: on the finite boundary-visit branch, the first sampled boundary state lies
    -- on the enlarged boundary surface, while `![2,2,-1]` does not.
    intro hEq
    exact latticePoint3_twoOneNegOne_not_mem_boundarySurface (by simpa [hEq] using hboundary)

/-- Helper for Exercise 18.2.4: the boundary-trace chart cannot realize the canonical SRW3,
because its first positive sampled state misses the off-surface point `![2,2,-1]` from
launch almost surely. -/
private theorem axisBlockedFreePairBoundaryTraceProcess_not_isCanonicalSRW3 :
    ¬ IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq))
      (axisBlockedFreePairBoundaryTraceProcess (Xq := Xq)) := by
  intro htrace
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let target : LatticePoint 3 := ![2, 2, -1]
  have hzero :
      μ {ω | axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ω = target} = 0 := by
    exact compl_mem_ae_iff.mp <| by
      simpa [μ, target] using
        axisBlockedFreePairBoundaryTraceProcess_first_ne_twoOneNegOne_ae
          (Pq := Pq) (Xq := Xq)
  have hmap :
      μ.map (axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1) =
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![1, 1, -1]) := by
    -- Proof comment: a genuine SRW3 realization would identify the time-`1` marginal with the
    -- one-step kernel row from the launched point.
    simpa [μ, pow_one] using htrace.transition_eq ![1, 1, -1] 1
  have hmass :
      μ {ω | axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ω = target} =
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![1, 1, -1]) ({target} : Set (LatticePoint 3)) := by
    rw [show {ω | axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ω = target} =
        axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ⁻¹'
          ({target} : Set (LatticePoint 3)) by
      ext ω
      simp]
    rw [← Measure.map_apply
      (axisBlockedFreePairBoundaryTraceProcess_measurable (Xq := Xq) 1)
      (measurableSet_singleton target)]
    exact congrArg (fun ν : Measure (LatticePoint 3) ↦ ν ({target} : Set (LatticePoint 3))) hmap
  have hkernel_pos :
      0 <
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![1, 1, -1]) ({target} : Set (LatticePoint 3)) := by
    rw [discreteMatrixKernel_apply_singleton]
    rw [latticeConvolutionStepMatrix_isTranslationInvariant
      (ν := symmetricSimpleRandomWalkStepPMF 3) ![1, 1, -1] target]
    have hdiff : target - ![1, 1, -1] = Pi.single 0 (1 : ℤ) := by
      ext i
      fin_cases i <;> norm_num [target]
    rw [hdiff]
    rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
    rw [symmetricSimpleRandomWalkStepPMF_apply_posFirst]
    norm_num
  -- Proof comment: the first sampled boundary state misses an SRW3 neighbor almost surely, while
  -- a true SRW3 realization would have to hit that neighbor with positive one-step mass.
  have : ¬ (0 <
      μ {ω | axisBlockedFreePairBoundaryTraceProcess (Xq := Xq) 1 ω = target}) := by
    simpa [hzero]
  exact this <| by
    rw [hmass]
    exact hkernel_pos

/-- Helper for Exercise 18.2.4: the collision line contains nonzero points, so any comparison map
that only detects the origin is too weak to control full collision-line avoidance. -/
private theorem axisBlockedDefectCollisionLine_has_nonzero_point :
    (![1, 1, 0] : LatticePoint 3) ∈ axisBlockedDefectCollisionLine ∧
      (![1, 1, 0] : LatticePoint 3) ≠ 0 := by
  -- Proof comment: `![1,1,0]` lies on the collision line because the first two coordinates agree
  -- and the third is `0`, but it is visibly not the origin.
  constructor
  · norm_num [axisBlockedDefectCollisionLine]
  · norm_num

/-- Helper for Exercise 18.2.4: a bounded-horizon comparison between canonical SRW3 origin
avoidance and the launched collision-line avoidance event upgrades, by continuity from above, to
the desired strict positivity of the launched collision-line avoidance mass. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_boundedOwnerAvoidComparison
    {Ω : Type*} [MeasurableSpace Ω]
    (P : LatticePoint 3 → ProbabilityMeasure Ω)
    (ownerProcess : ℕ → Ω → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P ownerProcess]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))]
    (hbounded :
      ∀ n : ℕ,
        (P ![1, 1, -1] : Measure Ω) {ω | ∀ m ≤ n, ownerProcess m ω ≠ 0} ≤
          Measure.map axisBlockedFreePairLatticePath
            (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
              ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            (axisBlockedDefectAvoidCollisionLineUpToPathEvent n)) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  let μ : Measure Ω := (P ![1, 1, -1] : Measure Ω)
  let ownerPath : Ω → (ℕ → LatticePoint 3) := fun ω n ↦ ownerProcess n ω
  let ν : Measure (ℕ → LatticePoint 3) := Measure.map ownerPath μ
  let launchPathLaw : Measure (ℕ → LatticePoint 3) :=
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
  let hreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
        P ownerProcess :=
    inferInstance
  have hownerPath_meas : Measurable ownerPath := by
    -- Proof comment: the owner trajectory map is coordinatewise measurable because each SRW3 time
    -- slice is measurable under the realization hypothesis.
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa [ownerPath] using hreal.measurable_process n
  have hbounded_path :
      ∀ n : ℕ,
        ν (latticeAvoidOriginUpToPathEvent n) ≤
          launchPathLaw (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
    intro n
    rw [Measure.map_apply hownerPath_meas
      (measurableSet_latticeAvoidOriginUpToPathEvent n)]
    -- Proof comment: rewrite the bounded path event under the owner trajectory map back to the
    -- corresponding bounded origin-avoidance event on the SRW3 sample space.
    simpa [ν, μ, ownerPath, latticeAvoidOriginUpToPathEvent] using hbounded n
  have hfull_path :
      ν ({path : ℕ → LatticePoint 3 | ∀ n : ℕ, path n ≠ 0}) ≤
        launchPathLaw axisBlockedDefectAvoidCollisionLinePathEvent := by
    -- Proof comment: compare the bounded-horizon masses termwise and pass to the infinite-horizon
    -- events by continuity from above on both path spaces.
    exact boundedAvoidComparison_implies_fullAvoidComparison ν launchPathLaw hbounded_path
  have hfull_meas :
      MeasurableSet ({path : ℕ → LatticePoint 3 | ∀ n : ℕ, path n ≠ 0} :
        Set (ℕ → LatticePoint 3)) := by
    rw [latticeAvoidOriginPathEvent_eq_iInter_bounded]
    exact MeasurableSet.iInter measurableSet_latticeAvoidOriginUpToPathEvent
  have howner_full :
      μ {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} ≤
        launchPathLaw axisBlockedDefectAvoidCollisionLinePathEvent := by
    rw [Measure.map_apply hownerPath_meas hfull_meas] at hfull_path
    -- Proof comment: the full path-space avoid-origin event is exactly the preimage of the pointwise
    -- owner-origin-avoidance event under the owner trajectory map.
    simpa [ν, μ, ownerPath] using hfull_path
  have howner_pos :
      0 < μ {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} := by
    -- Proof comment: canonical SRW3 started from the nonzero point `![1,1,-1]` avoids the origin
    -- with strictly positive probability.
    simpa [μ] using
      symmetricSimpleRandomWalk3_avoidOrigin_pos (P := P) (X := ownerProcess)
        (by norm_num)
  -- Proof comment: positivity of SRW3 origin avoidance transfers through the infinite-horizon
  -- comparison just proved.
  exact lt_of_lt_of_le howner_pos howner_full

/-- Helper for Exercise 18.2.4: once a genuine SRW3 owner process under the normalized owner law
is bounded above by the exact collision-indicator avoid-origin event at every horizon, the
start-pair collision-code no-hit mass is positive. -/
private theorem axisBlockedFreePair_startCollisionCodeNoHit_pos_of_ownerLawBoundedComparison
    (ownerProcess : ℕ → Ωq → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq))
      ownerProcess]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))]
    (hbounded :
      ∀ n : ℕ,
        ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
          {ω | ∀ m ≤ n, ownerProcess m ω ≠ 0}) ≤
          ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
            {ω | ∀ m ≤ n,
                axisBlockedFreePairCollisionIndicatorOwnerProcess (Xq := Xq) m ω ≠ 0})) :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  have hbounded_launch :
      ∀ n : ℕ,
        ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
          {ω | ∀ m ≤ n, ownerProcess m ω ≠ 0}) ≤
          Measure.map axisBlockedFreePairLatticePath
            (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
              ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
    intro n
    calc
      ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
        {ω | ∀ m ≤ n, ownerProcess m ω ≠ 0}) ≤
          ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
            {ω | ∀ m ≤ n,
                axisBlockedFreePairCollisionIndicatorOwnerProcess (Xq := Xq) m ω ≠ 0}) :=
          hbounded n
      _ =
          Measure.map axisBlockedFreePairLatticePath
            (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
              ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
              rw [axisBlockedFreePairDefectVisitOwnerLaw_launch (Pq := Pq)]
              exact
                axisBlockedFreePair_collisionIndicatorOwnerBoundedAvoidProb_eq_launchCollisionAvoidProb
                  (Pq := Pq) (Xq := Xq) n
  have hlaunchLine :
      0 <
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent := by
    -- Proof comment: the bounded-horizon comparison now exactly matches the launch-side theorem
    -- that upgrades SRW3 origin avoidance to launched collision-line avoidance positivity.
    exact
      axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_boundedOwnerAvoidComparison
        (Pq := Pq) (Xq := Xq)
        (P := axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq))
        (ownerProcess := ownerProcess) hbounded_launch
  have hlaunchNever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
    -- Proof comment: rewrite the launched collision-line avoidance mass back to the launched
    -- never-meet row of the free pair.
    rw [axisBlockedFreePair_launchPathKernel_neverMeet_eq_latticeCollisionLineAvoid
      (Pq := Pq) (Xq := Xq)] at hlaunchLine
    exact hlaunchLine
  -- Proof comment: the existing one-step launch-to-start transport turns positive launched
  -- never-meet mass into the desired start-side collision-code no-hit mass.
  exact
    axisBlockedFreePair_startCollisionCodeNoHit_pos_of_launchNeverMeetPos
      (Pq := Pq) (Xq := Xq) hlaunchNever

/-- Helper for Exercise 18.2.4: for a genuine SRW3 owner process, a pointwise bounded-horizon
event inclusion into the direct collision-indicator witness already suffices for the start-side
positivity theorem. -/
private theorem axisBlockedFreePair_startCollisionCodeNoHit_pos_of_ownerLawBoundedSubset
    (ownerProcess : ℕ → Ωq → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq))
      ownerProcess]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))]
    (hsubset :
      ∀ n : ℕ,
        {ω : Ωq | ∀ m ≤ n, ownerProcess m ω ≠ 0} ⊆
          {ω : Ωq | ∀ m ≤ n,
              axisBlockedFreePairCollisionIndicatorOwnerProcess (Xq := Xq) m ω ≠ 0}) :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  -- Proof comment: the bounded comparison wrapper only needs horizon-by-horizon measure
  -- domination, and the latter is an immediate consequence of a stronger pointwise event
  -- inclusion under the same owner law.
  refine axisBlockedFreePair_startCollisionCodeNoHit_pos_of_ownerLawBoundedComparison
    (Pq := Pq) (Xq := Xq) (ownerProcess := ownerProcess) ?_
  intro n
  exact measure_mono (hsubset n)

/-- Helper for Exercise 18.2.4: after two absorbed steps from the launched pair, the diagonal
endpoint `((0,1),(0,1))` already has positive mass. -/
private theorem axisBlockedFreePair_launchAbsorbedDiagonalEndpoint_two_pos :
    0 <
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ 2)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        ({((((0, 1) : AxisState), ((0, 1) : AxisState)))} : Set (AxisState × AxisState)) := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((0, 0) : AxisState), ((1, 1) : AxisState))
  let d : AxisState × AxisState := (((0, 1) : AxisState), ((0, 1) : AxisState))
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  have hseries :
      ((κAbs ^ 2) b) ({d} : Set (AxisState × AxisState)) =
        ∑' s : AxisState × AxisState,
          κAbs s ({d} : Set (AxisState × AxisState)) * (κAbs b) ({s} : Set (AxisState × AxisState)) := by
    -- Proof comment: expand the two-step absorbed endpoint mass as the discrete singleton sum over
    -- the intermediate pair state.
    rw [show (2 : ℕ) = 1 + 1 by norm_num]
    rw [Kernel.pow_succ_apply_eq_lintegral κAbs 1 b (measurableSet_singleton d)]
    simpa [mul_comm] using
      (MeasureTheory.lintegral_countable'
        (μ := κAbs b)
        (f := fun s : AxisState × AxisState ↦
          κAbs s ({d} : Set (AxisState × AxisState))))
  have hstep_bc :
      κAbs b ({c} : Set (AxisState × AxisState)) = 1 / 8 := by
    -- Proof comment: from the launched pair, moving the first walker left to the axis and keeping
    -- the second walker fixed yields the intermediate state `c`.
    rw [discreteMatrixKernel_apply_singleton]
    norm_num [κAbs, independentProductPairAbsorbDiagonalMatrix, independentProductPairMatrix,
      vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor, isHorizontalNeighbor,
      isVerticalNeighbor, b, c]
  have hstep_cd :
      κAbs c ({d} : Set (AxisState × AxisState)) = 1 / 16 := by
    -- Proof comment: from `c`, the first walker steps up on the axis and the second walker steps
    -- left off the axis, which lands on the diagonal endpoint `d`.
    rw [discreteMatrixKernel_apply_singleton]
    norm_num [κAbs, independentProductPairAbsorbDiagonalMatrix, independentProductPairMatrix,
      vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor, isHorizontalNeighbor,
      isVerticalNeighbor, c, d]
  have hterm_pos :
      0 <
        κAbs c ({d} : Set (AxisState × AxisState)) *
          (κAbs b) ({c} : Set (AxisState × AxisState)) := by
    -- Proof comment: the explicit two-step path `b → c → d` has mass `(1/8) * (1/16)`.
    rw [hstep_cd, hstep_bc]
    norm_num
  have hterm_le :
      κAbs c ({d} : Set (AxisState × AxisState)) *
          (κAbs b) ({c} : Set (AxisState × AxisState)) ≤
        ((κAbs ^ 2) b) ({d} : Set (AxisState × AxisState)) := by
    -- Proof comment: the singleton sum contains the explicit intermediate state `c` as one
    -- nonnegative term.
    rw [hseries]
    exact ENNReal.le_tsum c
  exact lt_of_lt_of_le hterm_pos hterm_le

/-- Helper for Exercise 18.2.4: by time `2`, the launched absorbed off-diagonal mass has already
dropped below `1`. -/
private theorem axisBlockedFreePair_launchAbsorbedOffDiagonalMass_two_lt_one :
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ 2)
      ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      {s : AxisState × AxisState | s.1 ≠ s.2} < 1 := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let d : AxisState × AxisState := (((0, 1) : AxisState), ((0, 1) : AxisState))
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  let offDiag : Set (AxisState × AxisState) := {s : AxisState × AxisState | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hdiag_pos :
      0 < ((κAbs ^ 2) b) ({d} : Set (AxisState × AxisState)) :=
    axisBlockedFreePair_launchAbsorbedDiagonalEndpoint_two_pos (Pq := Pq) (Xq := Xq)
  have hcomp_pos : 0 < ((κAbs ^ 2) b) offDiagᶜ := by
    -- Proof comment: the positive diagonal singleton mass sits inside the complement of the
    -- off-diagonal event.
    exact lt_of_lt_of_le hdiag_pos <| measure_mono <| by
      intro s hs
      simp [offDiag, d] at hs ⊢
      simpa [hs]
  have hsum :
      ((κAbs ^ 2) b) offDiag + ((κAbs ^ 2) b) offDiagᶜ = 1 := by
    -- Proof comment: every absorbed row is a probability measure, so a measurable set and its
    -- complement have total mass `1`.
    simpa using measure_add_measure_compl ((κAbs ^ 2) b) hoffDiag_meas
  have hlt :
      ((κAbs ^ 2) b) offDiag <
        ((κAbs ^ 2) b) offDiag + ((κAbs ^ 2) b) offDiagᶜ := by
    exact lt_add_of_pos_right hcomp_pos
  -- Proof comment: the positive diagonal mass forces the complementary off-diagonal mass to be
  -- strictly smaller than the full total mass.
  rw [hsum] at hlt
  simpa [κAbs, b, offDiag] using hlt

-- Route correction: the bounded absorbed comparison is false, so the live object here is now the
-- actual jump-sampled owner path rather than another bounded-horizon wrapper.
/-- Helper for Exercise 18.2.4: mark deterministic times when the raw owner path actually jumps,
so iterated entrance times can sample only genuine state changes. -/
private def axisBlockedFreePairJumpIndicator : ℕ → Ωq → ℤ
  | 0 => fun _ ↦ 1
  | n + 1 => fun ω ↦
      if axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) (n + 1) =
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n then
        1
      else
        0

/-- Helper for Exercise 18.2.4: the `k`-th jump-trace state is the raw owner position at the
`k`-th genuine jump time of the launched lattice path. -/
private def axisBlockedFreePairJumpTrace
    (k : ℕ+) : Ωq → LatticePoint 3 :=
  fun ω ↦
    stoppedValue
      (fun n ω' ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω') n)
      (fun ω' ↦ (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω')
      ω

/-- Helper for Exercise 18.2.4: the jump-trace process starts from the raw owner position and then
records the successive genuine owner jumps. -/
private def axisBlockedFreePairJumpTraceProcess :
    ℕ → Ωq → LatticePoint 3
  | 0 => fun ω ↦ axisBlockedFreePairLatticePath (fun n : ℕ ↦ Xq n ω) 0
  | n + 1 => fun ω ↦
      axisBlockedFreePairJumpTrace (Xq := Xq) ⟨n + 1, Nat.succ_pos _⟩ ω

/-- Helper for Exercise 18.2.4: the positive-time coordinates of the jump-trace process are
exactly the corresponding sampled jump observables. -/
private theorem axisBlockedFreePairJumpTraceProcess_pNat
    (k : ℕ+) :
    axisBlockedFreePairJumpTraceProcess (Xq := Xq) k =
      axisBlockedFreePairJumpTrace (Xq := Xq) k := by
  cases' k with n hn
  cases n with
  | zero =>
      cases (Nat.not_lt_zero _ hn)
  | succ n =>
      rfl

/-- Helper for Exercise 18.2.4: every finite iterated jump time is a genuine jump time, so the
`0/1` jump indicator is `0` there. -/
private theorem axisBlockedFreePairJumpIndicator_eq_zero_at_iteratedJumpFinite
    {k : ℕ+} {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω ≠ ⊤) :
    axisBlockedFreePairJumpIndicator (Xq := Xq)
      (((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω).untopA) ω = 0 := by
  cases k using PNat.recOn with
  | one =>
      -- Proof comment: for the first sampled jump, `hittingAfter_mem_set_of_ne_top` directly
      -- records that the jump indicator is `0` at the finite hitting index.
      have hmem :
          axisBlockedFreePairJumpIndicator (Xq := Xq)
              (((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω).untopA) ω ∈
            ({0} : Set ℤ) := by
        have h :
            axisBlockedFreePairJumpIndicator (Xq := Xq)
                (MeasureTheory.hittingAfter
                  (axisBlockedFreePairJumpIndicator (Xq := Xq))
                  ({0} : Set ℤ) 1 ω).untopA ω ∈
              ({0} : Set ℤ) :=
          hittingAfter_mem_set_of_ne_top
            (by simpa [iteratedEntranceTime_one] using hfinite)
        simpa [iteratedEntranceTime_one] using h
      simpa [Set.mem_singleton_iff] using hmem
  | succ k =>
      let S : Set ℕ :=
        {n : ℕ |
          (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω < n ∧
            axisBlockedFreePairJumpIndicator (Xq := Xq) n ω = 0}
      have hsInf :
          sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) =
            (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω := by
        simpa [iteratedEntranceTime_succ, S]
      have hS : S.Nonempty := by
        by_contra hS
        have himage_empty : ((fun n : ℕ ↦ (n : ℕ∞)) '' S) = ∅ := by
          simpa [Set.not_nonempty_iff_eq_empty] using hS
        have htop :
            (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω = ⊤ := by
          rw [← hsInf, himage_empty, sInf_empty]
        exact hfinite htop
      have hsInf_nat :
          ((sInf S : ℕ) : ℕ∞) =
            (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω := by
        calc
          ((sInf S : ℕ) : ℕ∞) = sInf ((fun n : ℕ ↦ (n : ℕ∞)) '' S) := by
            simpa using (WithTop.coe_sInf' hS (OrderBot.bddBelow S))
          _ = (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω := hsInf
      have huntop :
          ((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω).untopA =
            sInf S := by
        exact WithTop.coe_inj.mp <| by
          calc
            ((((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω).untopA : ℕ)
                : ℕ∞) =
                (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω := by
                  rw [WithTop.untopA_eq_untop hfinite]
                  exact WithTop.coe_untop _ hfinite
            _ = ((sInf S : ℕ) : ℕ∞) := hsInf_nat.symm
      have hsInf_mem : sInf S ∈ S := Nat.sInf_mem hS
      -- Proof comment: the recursive entrance-time definition picks the least later genuine
      -- jump, so its `untopA` representative again satisfies the indicator equation.
      simpa [S, huntop] using hsInf_mem.2

/-- Helper for Exercise 18.2.4: at any finite iterated jump time, the sampled jump trace is
exactly the raw owner state at that jump time. -/
private theorem axisBlockedFreePairJumpTrace_eq_latticePoint_at_iteratedJumpTime
    {k : ℕ+} {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω ≠ ⊤) :
    axisBlockedFreePairJumpTrace (Xq := Xq) k ω =
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω)
        (((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω).untopA) := by
  have hτ :
      (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω =
        ((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω).untopA := by
    rw [WithTop.untopA_eq_untop hfinite]
    symm
    exact WithTop.coe_untop _ hfinite
  -- Proof comment: on the finite time slice where the iterated jump time is fixed, the
  -- stopped-value definition of the jump trace collapses to that deterministic raw owner state.
  unfold axisBlockedFreePairJumpTrace
  simpa [hτ] using
    (stoppedValue_eq_on_timeSlice
      (X := fun n ω' ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω') n)
      (τ := fun ω' ↦ (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω')
      (ω := ω) (hτω := hτ))

/-- Helper for Exercise 18.2.4: if the full launched owner path avoids the collision line, then
every sampled jump-trace state avoids it as well. -/
private theorem axisBlockedFreePairJumpTraceAvoidCollisionLine_of_fullAvoid
    {ω : Ωq}
    (havoid :
      ∀ n : ℕ,
        axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∉
          axisBlockedDefectCollisionLine) :
    ∀ n : ℕ,
      axisBlockedFreePairJumpTraceProcess (Xq := Xq) n ω ∉
        axisBlockedDefectCollisionLine := by
  intro n
  cases n with
  | zero =>
      -- Proof comment: time `0` of the jump trace is literally time `0` of the full owner path.
      simpa [axisBlockedFreePairJumpTraceProcess] using havoid 0
  | succ n =>
      let k : ℕ+ := ⟨n + 1, Nat.succ_pos _⟩
      by_cases hfinite :
          (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω = ⊤
      · -- Proof comment: on the `⊤` branch, the sampled jump trace falls back to time `0`, which
        -- already avoids the collision line by the full-path hypothesis.
        change axisBlockedFreePairJumpTrace (Xq := Xq) k ω ∉ axisBlockedDefectCollisionLine
        unfold axisBlockedFreePairJumpTrace
        simpa [hfinite] using havoid 0
      · -- Proof comment: on a finite sampled jump slice, the sampled jump state is exactly the
        -- raw owner point at that jump time, so the full-path avoidance hypothesis applies.
        change axisBlockedFreePairJumpTrace (Xq := Xq) k ω ∉ axisBlockedDefectCollisionLine
        rw [axisBlockedFreePairJumpTrace_eq_latticePoint_at_iteratedJumpTime
          (Xq := Xq) (ω := ω) (k := k) hfinite]
        exact havoid (((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω).untopA)

/-- Helper for Exercise 18.2.4: each time slice of the jump-trace process is measurable because
the codomain is the countable lattice `ℤ^3`. -/
private theorem axisBlockedFreePairJumpTraceProcess_measurable
    (n : ℕ) :
    Measurable (axisBlockedFreePairJumpTraceProcess (Xq := Xq) n) := by
  -- Proof comment: the jump-trace still lands in a discrete countable state space, so each time
  -- slice is measurable without additional filtration transport.
  exact measurable_of_countable
    (f := axisBlockedFreePairJumpTraceProcess (Xq := Xq) n)

/-- Helper for Exercise 18.2.4: under the owner start law at `z`, the jump trace starts from `z`
itself. -/
private theorem axisBlockedFreePairJumpTraceProcess_initial_eq
    (z : LatticePoint 3) :
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) z : Measure Ωq).map
        (axisBlockedFreePairJumpTraceProcess (Xq := Xq) 0) =
      Measure.dirac z := by
  -- Proof comment: time `0` of the jump trace is the same raw owner coordinate as time `0` of
  -- the boundary-trace process, so the established initial-law computation applies unchanged.
  simpa [axisBlockedFreePairJumpTraceProcess, axisBlockedFreePairLatticePath] using
    axisBlockedFreePairBoundaryTraceProcess_initial_eq
      (Pq := Pq) (Xq := Xq) z

/-- Helper for Exercise 18.2.4: under the launched owner law, the jump trace starts from the
normalized owner point `![1,1,-1]`. -/
private theorem axisBlockedFreePairJumpTraceProcess_initial_eq_launch :
    ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq).map
      (axisBlockedFreePairJumpTraceProcess (Xq := Xq) 0)) =
      Measure.dirac (![1, 1, -1] : LatticePoint 3) := by
  -- Proof comment: specialize the general jump-trace initial law to the launched owner point.
  simpa using
    axisBlockedFreePairJumpTraceProcess_initial_eq
      (Pq := Pq) (Xq := Xq) (![1, 1, -1] : LatticePoint 3)

/-- Helper for Exercise 18.2.4: on a finite first jump slice, the first positive jump-trace
state is exactly the raw owner point at that jump time. -/
private theorem axisBlockedFreePairJumpTraceProcess_first_eq_latticePoint_at_jumpTime
    {ω : Ωq}
    (hfinite : (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω ≠ ⊤) :
    axisBlockedFreePairJumpTraceProcess (Xq := Xq) 1 ω =
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω)
        (((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω).untopA) := by
  have hτ :
      (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω =
        ((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω).untopA := by
    rw [WithTop.untopA_eq_untop hfinite]
    symm
    exact WithTop.coe_untop _ hfinite
  change axisBlockedFreePairJumpTrace (Xq := Xq) ⟨1, Nat.succ_pos 0⟩ ω = _
  -- Proof comment: on the finite first-jump slice, the stopped-value definition of the jump
  -- trace collapses to the deterministic jump time.
  unfold axisBlockedFreePairJumpTrace
  simpa [hτ] using
    (stoppedValue_eq_on_timeSlice
      (X := fun n ω' ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω') n)
      (τ := fun ω' ↦ (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω')
      (ω := ω) (hτω := hτ))

/-- Helper for Exercise 18.2.4: if the raw owner point already changes at time `1`, then the
first positive jump-trace state is exactly the time-`1` owner point. -/
private theorem axisBlockedFreePairJumpTraceProcess_one_eq_of_immediateJump
    {ω : Ωq}
    (hjump :
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 1 ≠
        axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 0) :
    axisBlockedFreePairJumpTraceProcess (Xq := Xq) 1 ω =
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 1 := by
  have hindicator :
      axisBlockedFreePairJumpIndicator (Xq := Xq) 1 ω = 0 := by
    simp [axisBlockedFreePairJumpIndicator, hjump]
  have hτ_le :
      (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω ≤ 1 := by
    -- Proof comment: if a genuine jump already occurs at time `1`, then the first jump time is
    -- bounded above by `1`.
    simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
      (MeasureTheory.hittingAfter_le_iff
        (u := axisBlockedFreePairJumpIndicator (Xq := Xq))
        (s := ({0} : Set ℤ)) (n := 1) (ω := ω) (i := 1)).2
        ⟨1, by simp, hindicator⟩
  have hτ_ge :
      (1 : ℕ∞) ≤ (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω := by
    -- Proof comment: every first positive jump time is at least `1` by definition.
    simpa [iteratedEntranceTime_one] using
      (MeasureTheory.le_hittingAfter
        (u := axisBlockedFreePairJumpIndicator (Xq := Xq))
        (s := ({0} : Set ℤ)) (n := 1) ω)
  have hτ_eq :
      (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω = 1 :=
    le_antisymm hτ_le hτ_ge
  have hfinite :
      (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω ≠ ⊤ := by
    simpa [hτ_eq]
  have hτ_nat :
      ((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω).untopA = 1 := by
    apply WithTop.coe_inj.mp
    calc
      ((((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω).untopA : ℕ) : ℕ∞) =
          (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω := by
            rw [WithTop.untopA_eq_untop hfinite]
            exact WithTop.coe_untop _ hfinite
      _ = 1 := hτ_eq
  -- Proof comment: once the first jump time is identified with `1`, the sampled jump trace is
  -- just the raw owner point at time `1`.
  simpa [hτ_nat] using
    axisBlockedFreePairJumpTraceProcess_first_eq_latticePoint_at_jumpTime
      (Xq := Xq) hfinite

/-- Helper for Exercise 18.2.4: the immediate-jump trace is not a canonical SRW3, because from
launch it can realize the two-coordinate jump `![2,2,-1]` in its first sampled step. -/
private theorem axisBlockedFreePairJumpTraceProcess_not_isCanonicalSRW3 :
    ¬ IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq))
      (axisBlockedFreePairJumpTraceProcess (Xq := Xq)) := by
  intro hjump
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let target : LatticePoint 3 := ![2, 2, -1]
  let startEvent : Set Ωq := {ω | Xq 0 ω = b}
  let launchEvent : Set Ωq := {ω | Xq 1 ω = c}
  let goodEvent : Set Ωq := startEvent ∩ launchEvent
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hstart_ae :
      ∀ᵐ ω ∂μ, ω ∈ startEvent := by
    have hprob :
        μ startEvent = 1 := by
      rw [show startEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
        ext ω
        simp [startEvent]]
      rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton b)]
      rw [axisBlockedFreePairDefectVisitOwnerLaw_launch (Pq := Pq)]
      rw [hqreal.initial_eq b]
      simp [μ, b]
    exact
      (MeasureTheory.mem_ae_iff_prob_eq_one
        (show MeasurableSet startEvent from
          by
            simpa [startEvent] using
              (hqreal.measurable_process 0) (measurableSet_singleton b))).2 hprob
  have hgood_subset :
      goodEvent ⊆ {ω | axisBlockedFreePairJumpTraceProcess (Xq := Xq) 1 ω = target} := by
    intro ω hω
    have h0 : Xq 0 ω = b := hω.1
    have h1 : Xq 1 ω = c := hω.2
    have hjump_now :
        axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 1 ≠
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 0 := by
      have hpath1 :
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 1 = target := by
        simpa [axisBlockedFreePairLatticePath, axisBlockedFreePairRelativePath,
          freePairRelativeStateToLatticePoint3, axisBlockedFreePairRelativeState, h1,
          c, target]
      have hpath0 :
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 0 = ![1, 1, -1] := by
        simpa [axisBlockedFreePairLatticePath, axisBlockedFreePairRelativePath,
          freePairRelativeStateToLatticePoint3, axisBlockedFreePairRelativeState, h0, b]
      intro hEq
      exact by
        have : target = (![1, 1, -1] : LatticePoint 3) := hpath1.trans <| hEq.trans hpath0.symm
        norm_num [target] at this
    -- Proof comment: on the explicit event where both walkers step right immediately from launch,
    -- the first sampled jump is exactly the two-coordinate jump `![2,2,-1]`.
    calc
      axisBlockedFreePairJumpTraceProcess (Xq := Xq) 1 ω =
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 1 := by
            exact
              axisBlockedFreePairJumpTraceProcess_one_eq_of_immediateJump
                (Xq := Xq) hjump_now
      _ = target := by
            simpa [axisBlockedFreePairLatticePath, axisBlockedFreePairRelativePath,
              freePairRelativeStateToLatticePoint3, axisBlockedFreePairRelativeState, h1,
              c, target]
  have hlaunch_mass_pos :
      0 < μ launchEvent := by
    rw [show launchEvent = Xq 1 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [launchEvent]]
    rw [← Measure.map_apply (hqreal.measurable_process 1) (measurableSet_singleton c)]
    rw [axisBlockedFreePairDefectVisitOwnerLaw_launch (Pq := Pq)]
    rw [show ((discreteMatrixKernel independentProductPairMatrix ^ 1) b) =
        (discreteMatrixKernel independentProductPairMatrix) b by simp]
    rw [hqreal.transition_eq b 1]
    rw [discreteMatrixKernel_apply_singleton]
    norm_num [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, b, c]
  have hgood_congr : launchEvent =ᵐ[μ] goodEvent := by
    filter_upwards [hstart_ae] with ω hω
    simp [startEvent, launchEvent, goodEvent, hω]
  have hgood_mass_pos :
      0 < μ goodEvent := by
    rw [← measure_congr hgood_congr]
    exact hlaunch_mass_pos
  have htarget_pos :
      0 < μ {ω | axisBlockedFreePairJumpTraceProcess (Xq := Xq) 1 ω = target} := by
    exact lt_of_lt_of_le hgood_mass_pos (measure_mono hgood_subset)
  have hmap :
      μ.map (axisBlockedFreePairJumpTraceProcess (Xq := Xq) 1) =
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![1, 1, -1]) := by
    -- Proof comment: a genuine SRW3 realization would identify the time-`1` marginal with the
    -- canonical one-step row from the launched owner point.
    simpa [μ, pow_one] using hjump.transition_eq ![1, 1, -1] 1
  have hmass :
      μ {ω | axisBlockedFreePairJumpTraceProcess (Xq := Xq) 1 ω = target} =
        (discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
            ![1, 1, -1]) ({target} : Set (LatticePoint 3)) := by
    rw [show {ω | axisBlockedFreePairJumpTraceProcess (Xq := Xq) 1 ω = target} =
        axisBlockedFreePairJumpTraceProcess (Xq := Xq) 1 ⁻¹' ({target} : Set (LatticePoint 3)) by
      ext ω
      simp]
    rw [← Measure.map_apply
      (axisBlockedFreePairJumpTraceProcess_measurable (Xq := Xq) 1)
      (measurableSet_singleton target)]
    exact congrArg (fun ν : Measure (LatticePoint 3) ↦ ν ({target} : Set (LatticePoint 3))) hmap
  have hkernel_zero :
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
          ![1, 1, -1]) ({target} : Set (LatticePoint 3)) = 0 := by
    rw [discreteMatrixKernel_apply_singleton]
    rw [latticeConvolutionStepMatrix_isTranslationInvariant
      (ν := symmetricSimpleRandomWalkStepPMF 3) ![1, 1, -1] target]
    have hdiff : target - ![1, 1, -1] = ![1, 1, 0] := by
      ext i
      fin_cases i <;> norm_num [target]
    rw [hdiff]
    rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
    rw [symmetricSimpleRandomWalkStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
      Fintype.sum_bool]
    norm_num
  -- Proof comment: the immediate jump trace puts positive mass on the two-coordinate jump
  -- `![2,2,-1]`, while a true SRW3 row assigns mass `0` to that non-neighbor.
  rw [hmass, hkernel_zero] at htarget_pos
  exact lt_irrefl _ htarget_pos

/-- Helper for Exercise 18.2.4: collapse the jump-trace owner states to the collision code, so
the remaining launch-side route can work with origin avoidance on `ℤ²`. -/
private def axisBlockedFreePairJumpCollisionCodeProcess :
    ℕ → Ωq → LatticePoint 2 :=
  fun n ω ↦
    axisBlockedDefectCollisionCode
      (axisBlockedFreePairJumpTraceProcess (Xq := Xq) n ω)

/-- Helper for Exercise 18.2.4: each time slice of the jump collision-code process is measurable,
because it is a discrete postcomposition of the measurable jump trace. -/
private theorem axisBlockedFreePairJumpCollisionCodeProcess_measurable
    (n : ℕ) :
    Measurable (axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) n) := by
  -- Proof comment: `axisBlockedDefectCollisionCode` lands in the discrete space `ℤ²`, so
  -- measurability is inherited from the already-established jump-trace measurability.
  exact
    (measurable_of_countable (f := axisBlockedDefectCollisionCode)).comp
      (axisBlockedFreePairJumpTraceProcess_measurable (Xq := Xq) n)

/-- Helper for Exercise 18.2.4: under the launched owner law, the jump collision-code process
starts from the nonzero code `![0,-1]`. -/
private theorem axisBlockedFreePairJumpCollisionCodeProcess_initial_eq_launch :
    ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq).map
      (axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) 0)) =
      Measure.dirac (![0, -1] : LatticePoint 2) := by
  calc
    ((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq).map
        (axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) 0)) =
      (((axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq).map
          (axisBlockedFreePairJumpTraceProcess (Xq := Xq) 0)).map
        axisBlockedDefectCollisionCode) := by
          rw [Measure.map_map
            (axisBlockedFreePairJumpTraceProcess_measurable (Xq := Xq) 0)
            (measurable_of_countable (f := axisBlockedDefectCollisionCode))]
          rfl
    _ = (Measure.dirac (![1, 1, -1] : LatticePoint 3)).map axisBlockedDefectCollisionCode := by
          rw [axisBlockedFreePairJumpTraceProcess_initial_eq_launch (Pq := Pq) (Xq := Xq)]
    _ = Measure.dirac (![0, -1] : LatticePoint 2) := by
          simp [axisBlockedDefectCollisionCode]

/-- Helper for Exercise 18.2.4: sampled jump collision-code avoidance is exactly jump-trace
avoidance of the encoded collision line. -/
private theorem
    axisBlockedFreePairJumpCollisionCodeProcess_avoidZero_eq_preimage_jumpTraceAvoidCollisionLine :
    {ω : Ωq | ∀ n : ℕ,
        axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) n ω ≠ 0} =
      (fun ω : Ωq ↦ fun n : ℕ ↦ axisBlockedFreePairJumpTraceProcess (Xq := Xq) n ω) ⁻¹'
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  ext ω
  -- Proof comment: the collision code vanishes exactly on the collision line, so pointwise
  -- avoidance of `0` along the sampled jump code is the same as pointwise avoidance of the
  -- collision line along the sampled jump trace.
  simp [axisBlockedFreePairJumpCollisionCodeProcess,
    axisBlockedDefectAvoidCollisionLinePathEvent,
    mem_axisBlockedDefectCollisionLine_iff_collisionCode_eq_zero]

/-- Helper for Exercise 18.2.4: start collision-code no-hit positivity is equivalent to
nonvanishing of the launched absorbed off-diagonal tail, because both statements already encode
the same launched never-meet positivity. -/
private theorem
    axisBlockedFreePair_startCollisionCodeNoHit_pos_iff_launchAbsorbedOffDiagonalNotTendstoZero :
    (0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent) ↔
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  constructor
  · intro hstart
    have hlaunch :
        0 <
          independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState)))
            freePairNeverMeetPathEvent := by
      -- Proof comment: first transport the start-side collision-code positivity to the launched
      -- never-meet row through the established one-step start/launch bridge.
      exact
        (axisBlockedFreePair_launchNeverMeet_pos_iff_startCollisionCodeNoHit_pos
          (Pq := Pq) (Xq := Xq)).2 hstart
    -- Proof comment: for the launched pair, positive infinite-horizon avoidance is already
    -- equivalent to nonvanishing of the absorbed off-diagonal tail.
    exact
      (axisBlockedFreePair_launchNeverMeet_pos_iff_absorbedOffDiagonalNotTendstoZero
        (Pq := Pq) (Xq := Xq)).1 hlaunch
  · intro htail
    have hlaunch :
        0 <
          independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState)))
            freePairNeverMeetPathEvent := by
      -- Proof comment: the launched absorbed-tail nonvanishing theorem already upgrades to
      -- launched never-meet positivity by continuity from above.
      exact
        axisBlockedFreePair_launchNeverMeet_pos_of_absorbedOffDiagonalNotTendstoZero
          (Pq := Pq) (Xq := Xq) htail
    -- Proof comment: transport the launched never-meet positivity back to the start collision-code
    -- no-hit statement via the existing one-step comparison theorem.
    exact
      axisBlockedFreePair_startCollisionCodeNoHit_pos_of_launchNeverMeetPos
        (Pq := Pq) (Xq := Xq) hlaunch

/-- Helper for Exercise 18.2.4: start collision-code no-hit positivity is also equivalent to
nonvanishing of the absorbed off-diagonal tail started directly from `((0,0),(0,1))`. -/
private theorem
    axisBlockedFreePair_startCollisionCodeNoHit_pos_iff_startAbsorbedOffDiagonalNotTendstoZero :
    (0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent) ↔
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  constructor
  · intro hstart
    have hstartNever :
        0 <
          independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            a freePairNeverMeetPathEvent := by
      -- Proof comment: rewrite the start-side collision-code mass back to the corresponding
      -- never-meet row of the realized free product-pair path kernel.
      rw [axisBlockedFreePair_startPathKernel_neverMeet_eq_collisionCodeNoHitMass
        (Pq := Pq) (Xq := Xq)]
      simpa [a] using hstart
    have hstartMeasure :
        0 <
          (Pq a : Measure Ωq) {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
      -- Proof comment: rewrite the realized path-kernel row back to the start realization
      -- measure on the pointwise never-meet event.
      rw [← axisBlockedFreePair_startPathKernel_neverMeet_eq_measure
        (Pq := Pq) (Xq := Xq)]
      simpa [a] using hstartNever
    have hbounded_not :
        ¬ Filter.Tendsto
          (fun n : ℕ ↦
            (Pq a : Measure Ωq) {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2})
          Filter.atTop (nhds 0) := by
      -- Proof comment: a positive infinite-horizon never-meet mass gives a uniform lower bound
      -- on every bounded avoid-diagonal probability.
      exact not_tendsto_zero_of_neverMeetProb_pos (μ := (Pq a : Measure Ωq)) (Xq := Xq)
        hstartMeasure
    have habsorbed_fun :
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a)
            {s : AxisState × AxisState | s.1 ≠ s.2}) =
          (fun n : ℕ ↦
            (Pq a : Measure Ωq) {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2}) := by
      funext n
      -- Proof comment: the absorbed off-diagonal mass is exactly the bounded avoid-diagonal
      -- probability under the same start law.
      simpa [a] using
        independentProductPairAbsorbDiagonal_offDiagonalMass_eq_freeAvoidDiagonalProb
          (Pq := Pq) (Xq := Xq) a n
    -- Proof comment: transport the nonvanishing statement across the explicit bounded-mass
    -- normalization.
    simpa [habsorbed_fun, a] using hbounded_not
  · intro htail
    have hstartNever :
        0 <
          independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            a freePairNeverMeetPathEvent := by
      -- Proof comment: the generic continuity-from-above argument upgrades start-side absorbed
      -- tail nonvanishing to positive infinite-horizon never-meet mass.
      exact
        independentProductPairPathKernel_neverMeet_pos_of_absorbedOffDiagonalNotTendstoZero
          (Pq := Pq) (Xq := Xq) a htail
    -- Proof comment: rewrite the positive start never-meet row back to the collision-code
    -- no-hit mass.
    rw [axisBlockedFreePair_startPathKernel_neverMeet_eq_collisionCodeNoHitMass
      (Pq := Pq) (Xq := Xq)] at hstartNever
    simpa [a] using hstartNever

/-- Helper for Exercise 18.2.4: any nonvanishing theorem for the launched absorbed off-diagonal
tail already forces nonvanishing for the start pair through the explicit one-step launch mass. -/
private theorem axisBlockedFreePair_startAbsorbedOffDiagonal_not_tendsto_zero_of_launchAbsorbedTail
    (hlaunch :
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0)) :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let startMass : ℕ → ℝ≥0∞ := fun n ↦
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a)
      {s : AxisState × AxisState | s.1 ≠ s.2}
  let launchMass : ℕ → ℝ≥0∞ := fun n ↦
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) b)
      {s : AxisState × AxisState | s.1 ≠ s.2}
  let c : ℝ≥0∞ :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix a
      ({b} : Set (AxisState × AxisState))
  have hc_eq :
      c =
        discreteMatrixKernel independentProductPairMatrix a
          ({b} : Set (AxisState × AxisState)) := by
    -- Proof comment: the absorbed kernel agrees with the free product-pair kernel on the
    -- off-diagonal start row.
    rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
    simp [c, independentProductPairAbsorbDiagonalMatrix, a, b]
  have hc_pos : 0 < c := by
    -- Proof comment: the explicit one-step launch from the start pair to the launched pair has
    -- positive mass.
    rw [hc_eq]
    exact axisBlockedFreePair_startPair_launchToOffDefect_pos (Pq := Pq) (Xq := Xq)
  have hc_ne_zero : c ≠ 0 := ne_of_gt hc_pos
  have hc_ne_top : c ≠ ⊤ := by
    -- Proof comment: singleton masses under an absorbed kernel row are finite.
    simpa [c] using
      (measure_ne_top
        (discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix a)
        ({b} : Set (AxisState × AxisState)))
  intro hstart
  have hstart_succ :
      Filter.Tendsto (fun n : ℕ ↦ startMass (n + 1)) Filter.atTop (nhds 0) := by
    -- Proof comment: shifting a convergent tail by one time step preserves convergence at
    -- `Filter.atTop`.
    simpa [startMass] using hstart.comp (tendsto_add_atTop_nat 1)
  have hscaled :
      Filter.Tendsto (fun n : ℕ ↦ c * launchMass n) Filter.atTop (nhds 0) := by
    -- Proof comment: the one-step start-to-launch lower bound squeezes the scaled launched tail
    -- between `0` and the shifted start tail.
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hstart_succ
        (Filter.Eventually.of_forall fun n ↦ bot_le)
        (Filter.Eventually.of_forall fun n ↦ ?_)
    simpa [startMass, launchMass, c, a, b] using
      axisBlockedFreePair_startAbsorbedOffDiagonalMass_ge_launchMass
        (Pq := Pq) (Xq := Xq) (n := n)
  have hcancel :
      Filter.Tendsto (fun n : ℕ ↦ c⁻¹ * (c * launchMass n)) Filter.atTop (nhds 0) := by
    -- Proof comment: multiplying by the inverse of the positive finite one-step mass recovers
    -- the unscaled launched tail.
    simpa using (tendsto_const_nhds.mul hscaled)
  have hlaunch_tendsto :
      Filter.Tendsto launchMass Filter.atTop (nhds 0) := by
    -- Proof comment: cancellation transports convergence of the scaled launched tail back to the
    -- original launched tail.
    convert hcancel using 1
    funext n
    rw [← mul_assoc, ENNReal.inv_mul_cancel hc_ne_zero hc_ne_top, one_mul]
  -- Proof comment: this contradicts the assumed launch-side nonvanishing theorem.
  exact hlaunch hlaunch_tendsto

/-- Helper for Exercise 18.2.4: positive launched collision-line avoidance already forces the
launched absorbed off-diagonal tail to stay away from `0`. -/
private theorem
    axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_of_collisionLineAvoidPos
    (hline :
      0 <
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent) :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  have hnever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
    -- Proof comment: rewrite the launched collision-line avoidance mass back to the launched
    -- never-meet row.
    rw [axisBlockedFreePair_launchPathKernel_neverMeet_eq_latticeCollisionLineAvoid
      (Pq := Pq) (Xq := Xq)] at hline
    exact hline
  -- Proof comment: the existing launch-side continuity-from-above argument now gives the desired
  -- absorbed-tail nonvanishing statement.
  exact
    axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_of_launchNeverMeetPos
      (Pq := Pq) (Xq := Xq) hnever

/-- Helper for Exercise 18.2.4: the canonical path-space realization of symmetric simple random
walk on `ℤ^3` is available without introducing a new sampled owner on `Ωq`. -/
private theorem existsCanonicalSymmetricSimpleRandomWalk3Realization :
    ∃ P : LatticePoint 3 → ProbabilityMeasure (ℕ → LatticePoint 3),
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
        P Function.eval := by
  -- Proof comment: specialize the earlier generic discrete path-space construction to the
  -- stochastic SRW3 step matrix.
  exact
    existsCanonicalDiscreteMatrixRealization
      (q := latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
      symmetricSimpleRandomWalk3_stepMatrix_isStochastic

/-- Helper for Exercise 18.2.4: `axisBlockedFreePairLaunchLatticeHistoryEvent ξ` fixes the
initial encoded `ℤ^3` trajectory of the launched free pair to the finite prefix `ξ`. -/
private def axisBlockedFreePairLaunchLatticeHistoryEvent {n : ℕ}
    (ξ : Fin (n + 1) → LatticePoint 3) : Set Ωq :=
  sampledFiniteHistoryEvent
    (fun m ω ↦ axisBlockedFreePairLatticePath (fun k : ℕ ↦ Xq k ω) m)
    (fun i : Fin (n + 1) ↦ (i : ℕ))
    ξ

/-- Helper for Exercise 18.2.4: every launched encoded-history event lies inside the fiber of its
terminal encoded state. -/
private theorem axisBlockedFreePairLaunchLatticeHistoryEvent_subset_terminalFiber
    {n : ℕ} (ξ : Fin (n + 1) → LatticePoint 3) :
    axisBlockedFreePairLaunchLatticeHistoryEvent (Xq := Xq) ξ ⊆
      {ω | axisBlockedFreePairLatticePath (fun k : ℕ ↦ Xq k ω) n = ξ (Fin.last n)} := by
  -- Proof comment: the generic finite-history wrapper already records the terminal sampled state
  -- among its coordinates, so membership in the prefix event forces the final coordinate value.
  simpa [axisBlockedFreePairLaunchLatticeHistoryEvent] using
    sampledFiniteHistoryEvent_subset_terminalFiber
      (X := fun m ω ↦ axisBlockedFreePairLatticePath (fun k : ℕ ↦ Xq k ω) m)
      (times := fun i : Fin (n + 1) ↦ (i : ℕ))
      ξ

/-- Helper for Exercise 18.2.4: the old bounded-comparison route already fails at horizon `2`,
because the launched collision-line avoidance mass has dropped strictly below `1`. -/
private theorem axisBlockedFreePair_canonicalSRW3BoundedAvoidComparison :
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      (axisBlockedDefectAvoidCollisionLineUpToPathEvent 2) < 1 := by
  -- Route correction: the all-horizon SRW3-to-launch domination is not the right frontier.
  -- By time `2`, the launched absorbed chain has already created diagonal mass, so the launched
  -- bounded collision-line avoidance probability is strictly smaller than `1`.
  rw [axisBlockedFreePair_launchLatticeCollisionLineAvoidUpTo_eq_absorbedOffDiagonalMass
    (Pq := Pq) (Xq := Xq) 2]
  exact
    axisBlockedFreePair_launchAbsorbedOffDiagonalMass_two_lt_one
      (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: from the launched owner point `![1,1,-1]`, one SRW3 step cannot
land at the origin. -/
private theorem symmetricSimpleRandomWalk3_launch_stepMass_origin_eq_zero :
    (discreteMatrixKernel
      (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
      ![1, 1, -1]) ({(0 : LatticePoint 3)} : Set (LatticePoint 3)) = 0 := by
  rw [discreteMatrixKernel_apply_singleton]
  rw [latticeConvolutionStepMatrix_isTranslationInvariant
    (ν := symmetricSimpleRandomWalkStepPMF 3) ![1, 1, -1] 0]
  have hdiff : (0 : LatticePoint 3) - ![1, 1, -1] = ![-1, -1, 1] := by
    ext i
    fin_cases i <;> norm_num
  rw [hdiff]
  rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
  -- Proof comment: the vector `![-1,-1,1]` changes three coordinates at once, so it is not one
  -- of the six single-coordinate unit steps in the SRW3 increment law.
  rw [symmetricSimpleRandomWalkStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num

/-- Helper for Exercise 18.2.4: from the launched owner point `![1,1,-1]`, one SRW3 step cannot
land on any lattice neighbor of the origin. -/
private theorem symmetricSimpleRandomWalk3_launch_stepMass_originNeighbor_eq_zero
    (target : LatticePoint 3)
    (htarget :
      target = Pi.single 0 (1 : ℤ) ∨
        target = Pi.single 0 (-1 : ℤ) ∨
        target = Pi.single 1 (1 : ℤ) ∨
        target = Pi.single 1 (-1 : ℤ) ∨
        target = Pi.single 2 (1 : ℤ) ∨
        target = Pi.single 2 (-1 : ℤ)) :
    (discreteMatrixKernel
      (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
      ![1, 1, -1]) ({target} : Set (LatticePoint 3)) = 0 := by
  rw [discreteMatrixKernel_apply_singleton]
  rw [latticeConvolutionStepMatrix_isTranslationInvariant
    (ν := symmetricSimpleRandomWalkStepPMF 3) ![1, 1, -1] target]
  rcases htarget with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
    -- Proof comment: every origin neighbor differs from `![1,1,-1]` in at least two coordinates,
    -- so none of these targets can be reached in one SRW3 step.
    rw [symmetricSimpleRandomWalkStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
      Fintype.sum_bool]
    norm_num

/-- Helper for Exercise 18.2.4: the launched owner point `![1,1,-1]` starts off the collision
line. -/
private theorem axisBlockedFreePairLatticePoint_launch_not_mem_collisionLine :
    (![1, 1, -1] : LatticePoint 3) ∉ axisBlockedDefectCollisionLine := by
  -- Proof comment: the launched owner point has third coordinate `-1`, so it cannot lie on the
  -- collision line `z 0 = z 1 ∧ z 2 = 0`.
  norm_num [axisBlockedDefectCollisionLine]

/-- Helper for Exercise 18.2.4: under the launched path law, time `0` is almost surely already
off the collision line. -/
private theorem axisBlockedFreePair_launchLatticePath_initialOffCollision_prob_eq_one :
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      {path : ℕ → LatticePoint 3 | path 0 ∉ axisBlockedDefectCollisionLine} = 1 := by
  let μ : Measure (ℕ → LatticePoint 3) :=
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
  let startEvent : Set (ℕ → LatticePoint 3) := {path | path 0 = ![1, 1, -1]}
  let offLineEvent : Set (ℕ → LatticePoint 3) := {path | path 0 ∉ axisBlockedDefectCollisionLine}
  have hstart_eq_one : μ startEvent = 1 := by
    simpa [μ, startEvent] using
      axisBlockedFreePair_launchLatticePath_initialPoint_prob_eq_one
        (Pq := Pq) (Xq := Xq)
  have hsubset : startEvent ⊆ offLineEvent := by
    intro path hpath
    have h0 : path 0 = (![1, 1, -1] : LatticePoint 3) := hpath
    simpa [offLineEvent, h0] using
      axisBlockedFreePairLatticePoint_launch_not_mem_collisionLine
  refine le_antisymm ?_ ?_
  · calc
      μ offLineEvent ≤ μ Set.univ := measure_mono (by intro path hpath; simp)
      _ = 1 := by simp [μ]
  · calc
      1 = μ startEvent := hstart_eq_one.symm
      _ ≤ μ offLineEvent := measure_mono hsubset

/-- Helper for Exercise 18.2.4: if the first collision-line hit occurs at time `n > 0`, then
time `n` is a genuine jump time of the raw owner path. -/
private theorem axisBlockedFreePairJumpIndicator_eq_zero_of_firstCollisionHit
    {ω : Ωq} {n : ℕ}
    (hn : 0 < n)
    (hhit :
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∈
        axisBlockedDefectCollisionLine)
    (hbefore :
      ∀ m : ℕ, m < n →
        axisBlockedFreePairLatticePath (fun k : ℕ ↦ Xq k ω) m ∉
          axisBlockedDefectCollisionLine) :
    axisBlockedFreePairJumpIndicator (Xq := Xq) n ω = 0 := by
  cases n with
  | zero =>
      cases (Nat.not_lt_zero _ hn)
  | succ n =>
      by_cases hstay :
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) (n + 1) =
            axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n
      · have hprev :
            axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∈
              axisBlockedDefectCollisionLine := by
          simpa [hstay] using hhit
        exact False.elim <| (hbefore n (Nat.lt_succ_self n)) hprev
      · -- Proof comment: a first collision hit cannot be a holding time, so the jump indicator
        -- takes the genuine-jump value `0`.
        simp [axisBlockedFreePairJumpIndicator, hstay]

/-- Helper for Exercise 18.2.4: every positive genuine jump time is exactly one iterated jump
time of the raw owner path. -/
private theorem axisBlockedFreePairJumpIndicator_hit_eq_iteratedJumpTime
    {ω : Ωq} {n : ℕ}
    (hn : 0 < n)
    (hjump : axisBlockedFreePairJumpIndicator (Xq := Xq) n ω = 0) :
    ∃ k : ℕ+, (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω = n := by
  -- Proof comment: enumerate positive jump times by strong induction on the time index. Either
  -- `n` is the first genuine jump, or we step forward from the greatest earlier genuine jump.
  refine Nat.strong_induction_on n ?_ n hn hjump
  intro n ih hn hjump
  by_cases hprev :
      ∃ m : ℕ, 0 < m ∧ m < n ∧ axisBlockedFreePairJumpIndicator (Xq := Xq) m ω = 0
  · let p : ℕ → Prop := fun m =>
      0 < m ∧ m < n ∧ axisBlockedFreePairJumpIndicator (Xq := Xq) m ω = 0
    let m := Nat.findGreatest p n
    have hm_spec : p m := by
      rcases hprev with ⟨j, hj_pos, hj_lt, hj_zero⟩
      exact Nat.findGreatest_spec (Nat.le_of_lt hj_lt) ⟨hj_pos, hj_lt, hj_zero⟩
    have hm_pos : 0 < m := hm_spec.1
    have hm_lt_n : m < n := hm_spec.2.1
    have hm_jump : axisBlockedFreePairJumpIndicator (Xq := Xq) m ω = 0 := hm_spec.2.2
    rcases ih m hm_lt_n hm_pos hm_jump with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    have hle_n :
        (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω ≤ n := by
      exact
        (iteratedEntranceTime_succ_le_iff_existsHitAfter
          (Y := axisBlockedFreePairJumpIndicator (Xq := Xq))
          (y := 0) (ω := ω) (k := k) (N := n)).2
          ⟨n, by simpa [hk], le_rfl, hjump⟩
    have hge_n : (n : ℕ∞) ≤ (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω := by
      by_contra hlt_n
      have hlt_n' :
          (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω < n :=
        lt_of_not_ge hlt_n
      have hfinite :
          (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω ≠ ⊤ :=
        ne_of_lt (lt_of_lt_of_le hlt_n' le_top)
      let t : ℕ :=
        ((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω).untopA
      have ht_eq :
          (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω = t := by
        have hcoe :
            (((t : ℕ) : ℕ∞)) =
              (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω := by
          simpa [t, WithTop.untopA_eq_untop hfinite] using
            (WithTop.coe_untop
              ((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω) hfinite)
        exact hcoe.symm
      have ht_lt_n : t < n := by
        rw [ht_eq] at hlt_n'
        exact_mod_cast hlt_n'
      have hle_t :
          (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^(k + 1)) ω ≤ t := by
        simpa [ht_eq]
      rcases
          (iteratedEntranceTime_succ_le_iff_existsHitAfter
            (Y := axisBlockedFreePairJumpIndicator (Xq := Xq))
            (y := 0) (ω := ω) (k := k) (N := t)).1 hle_t with
        ⟨j, hj_gt, hj_le_t, hj_zero⟩
      have hm_lt_j : m < j := by
        simpa [hk] using hj_gt
      have hj_lt_n : j < n := lt_of_le_of_lt hj_le_t ht_lt_n
      have hj_not :
          ¬ p j :=
        Nat.findGreatest_is_greatest (P := p) (n := n) (k := j)
          (by simpa [m] using hm_lt_j) (Nat.le_of_lt hj_lt_n)
      exact hj_not ⟨lt_trans hm_pos hm_lt_j, hj_lt_n, hj_zero⟩
    exact le_antisymm hle_n hge_n
  · have hle_n :
        (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω ≤ n := by
      simpa [iteratedEntranceTime_one, Set.mem_singleton_iff] using
        (MeasureTheory.hittingAfter_le_iff
          (u := axisBlockedFreePairJumpIndicator (Xq := Xq))
          (s := ({0} : Set ℤ)) (n := 1) (ω := ω) (i := n)).2
          ⟨n, ⟨hn, le_rfl⟩, hjump⟩
    have hge_n :
        (n : ℕ∞) ≤ (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω := by
      by_contra hlt_n
      have hlt_n' :
          (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^1) ω < n :=
        lt_of_not_ge hlt_n
      rcases
          (MeasureTheory.hittingAfter_lt_iff
            (u := axisBlockedFreePairJumpIndicator (Xq := Xq))
            (s := ({0} : Set ℤ)) (n := 1) (ω := ω) (i := n)).1 <|
        by simpa [iteratedEntranceTime_one] using hlt_n' with
        ⟨j, hj_mem, hj_zero⟩
      have hj_pair : 0 < j ∧ j < n := by
        simpa [Set.mem_Ico] using hj_mem
      exact hprev ⟨j, hj_pair.1, hj_pair.2, hj_zero⟩
    refine ⟨1, ?_⟩
    exact le_antisymm hle_n hge_n

/-- Helper for Exercise 18.2.4: every positive genuine jump of the raw owner path appears as one
sampled value of the jump-trace process. -/
private theorem axisBlockedFreePairJumpTraceProcess_eq_of_genuineJump
    {ω : Ωq} {n : ℕ}
    (hn : 0 < n)
    (hjump : axisBlockedFreePairJumpIndicator (Xq := Xq) n ω = 0) :
    ∃ k : ℕ,
      axisBlockedFreePairJumpTraceProcess (Xq := Xq) k ω =
        axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n := by
  -- Proof comment: once the genuine jump time is identified as one iterated entrance time, the
  -- sampled jump trace is exactly the raw owner position on that finite time slice.
  rcases
      axisBlockedFreePairJumpIndicator_hit_eq_iteratedJumpTime
        (Xq := Xq) hn hjump with
    ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hfinite :
      (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω ≠ ⊤ := by
    simpa [hk]
  have hidx :
      (((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω).untopA) = n := by
    apply WithTop.coe_inj.mp
    calc
      (((((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω).untopA : ℕ) : ℕ∞)) =
          (τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω := by
            rw [WithTop.untopA_eq_untop hfinite]
            exact WithTop.coe_untop _ hfinite
      _ = n := hk
  calc
    axisBlockedFreePairJumpTraceProcess (Xq := Xq) k ω =
        axisBlockedFreePairJumpTrace (Xq := Xq) k ω := by
          simpa using congrArg (fun f : Ωq → LatticePoint 3 ↦ f ω)
            (axisBlockedFreePairJumpTraceProcess_pNat (Xq := Xq) k)
    _ =
        axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω)
          (((τ_[axisBlockedFreePairJumpIndicator (Xq := Xq), 0]^k) ω).untopA) := by
            exact
              axisBlockedFreePairJumpTrace_eq_latticePoint_at_iteratedJumpTime
                (Xq := Xq) (ω := ω) (k := k) hfinite
    _ =
        axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n := by
          simpa [hidx]

/-- Helper for Exercise 18.2.4: if the raw owner path starts off the collision line and later hits
it, then some sampled jump-trace state already lies on the collision line. -/
private theorem axisBlockedFreePairJumpTraceHitCollision_of_fullHit
    {ω : Ωq}
    (hstart :
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 0 ∉
        axisBlockedDefectCollisionLine)
    (hhit :
      ∃ n : ℕ,
        axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∈
          axisBlockedDefectCollisionLine) :
    ∃ k : ℕ,
      axisBlockedFreePairJumpTraceProcess (Xq := Xq) k ω ∈
        axisBlockedDefectCollisionLine := by
  -- Proof comment: choose the first raw collision-line hit, show it is a genuine jump, and then
  -- transport that exact raw owner state into the sampled jump trace.
  let n : ℕ := Nat.find hhit
  have hhit_n :
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∈
        axisBlockedDefectCollisionLine :=
    Nat.find_spec hhit
  have hbefore :
      ∀ m : ℕ, m < n →
        axisBlockedFreePairLatticePath (fun k : ℕ ↦ Xq k ω) m ∉
          axisBlockedDefectCollisionLine := by
    intro m hm
    exact Nat.find_min' hhit hm
  have hn : 0 < n := by
    by_contra hn
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn
    exact hstart (hn_zero ▸ hhit_n)
  have hjump :
      axisBlockedFreePairJumpIndicator (Xq := Xq) n ω = 0 :=
    axisBlockedFreePairJumpIndicator_eq_zero_of_firstCollisionHit
      (Xq := Xq) hn hhit_n hbefore
  rcases
      axisBlockedFreePairJumpTraceProcess_eq_of_genuineJump
        (Xq := Xq) hn hjump with
    ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simpa [hk] using hhit_n

/-- Helper for Exercise 18.2.4: if time `0` is off the collision line and the sampled
jump-collision code never hits `0`, then the full raw owner path avoids the collision line. -/
private theorem axisBlockedFreePairLaunchJumpCollisionCodeNoHit_subset_fullAvoid :
    {ω : Ωq |
        axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 0 ∉
            axisBlockedDefectCollisionLine ∧
          ∀ n : ℕ, axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) n ω ≠ 0} ⊆
      {ω : Ωq |
        ∀ n : ℕ,
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∉
            axisBlockedDefectCollisionLine} := by
  intro ω hω n hhit
  -- Proof comment: any raw collision-line hit would force a sampled jump-trace hit, and on the
  -- collision line the sampled collision code is exactly `0`.
  rcases
      axisBlockedFreePairJumpTraceHitCollision_of_fullHit
        (Xq := Xq) hω.1 ⟨n, hhit⟩ with
    ⟨k, hk_hit⟩
  have hk_zero :
      axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) k ω = 0 := by
    simpa [axisBlockedFreePairJumpCollisionCodeProcess,
      mem_axisBlockedDefectCollisionLine_iff_collisionCode_eq_zero] using hk_hit
  exact (hω.2 k hk_zero).elim

/-- Helper for Exercise 18.2.4: the launched jump-code no-hit event records that the launched
owner path starts off the collision line and that every sampled jump collision code stays
nonzero. -/
private def axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent : Set Ωq :=
  {ω : Ωq |
      axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 0 ∉
          axisBlockedDefectCollisionLine ∧
        ∀ n : ℕ, axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) n ω ≠ 0}

/-- Helper for Exercise 18.2.4: the launched jump-code no-hit event is measurable. -/
private theorem axisBlockedFreePair_launchJumpCollisionCodeNoHit_measurableSet :
    MeasurableSet
      (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) := by
  let path0 : Ωq → LatticePoint 3 :=
    fun ω ↦ axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) 0
  have hstart :
      MeasurableSet {ω : Ωq | path0 ω ∉ axisBlockedDefectCollisionLine} := by
    -- Proof comment: the time-`0` owner coordinate lands in the discrete lattice `ℤ³`, so the
    -- off-collision event is just one measurable fiber complement.
    rw [show {ω : Ωq | path0 ω ∉ axisBlockedDefectCollisionLine} =
        path0 ⁻¹' axisBlockedDefectCollisionLineᶜ by
      ext ω
      simp]
    exact (measurable_of_countable (f := path0)) (MeasurableSet.of_discrete _)
  have htail :
      MeasurableSet
        {ω : Ωq | ∀ n : ℕ, axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) n ω ≠ 0} := by
    rw [show {ω : Ωq | ∀ n : ℕ,
        axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) n ω ≠ 0} =
          ⋂ n : ℕ, {ω : Ωq |
            axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) n ω ≠ 0} by
      ext ω
      simp]
    refine MeasurableSet.iInter ?_
    intro n
    -- Proof comment: each sampled jump-code time slice is measurable, and the codomain is
    -- discrete, so avoiding `0` at that slice is measurable as well.
    rw [show {ω : Ωq |
        axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) n ω ≠ 0} =
          axisBlockedFreePairJumpCollisionCodeProcess (Xq := Xq) n ⁻¹'
            ({0} : Set (LatticePoint 2))ᶜ by
      ext ω
      simp]
    exact
      (axisBlockedFreePairJumpCollisionCodeProcess_measurable (Xq := Xq) n)
        (MeasurableSet.of_discrete _)
  -- Proof comment: the launched no-hit event is the intersection of the measurable initial
  -- off-line event and the measurable sampled no-hit tail event.
  simpa [axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent] using hstart.inter htail

/-- Helper for Exercise 18.2.4: for the launched pair, sampled jump-code no-hit is exactly full
raw collision-line avoidance. -/
private theorem axisBlockedFreePair_launchJumpCollisionCodeNoHit_eq_fullAvoid :
    axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq) =
      {ω : Ωq |
        ∀ n : ℕ,
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∉
            axisBlockedDefectCollisionLine} := by
  ext ω
  constructor
  · intro hω
    -- Proof comment: the reverse implication was already proved as the truthful sampled-to-raw
    -- event inclusion.
    exact axisBlockedFreePairLaunchJumpCollisionCodeNoHit_subset_fullAvoid (Xq := Xq) hω
  · intro hω
    constructor
    · -- Proof comment: the full-avoid event includes the time-`0` off-collision fact as its
      -- zeroth coordinate.
      exact hω 0
    · have htrace :
          ∀ n : ℕ,
            axisBlockedFreePairJumpTraceProcess (Xq := Xq) n ω ∉
              axisBlockedDefectCollisionLine :=
        axisBlockedFreePairJumpTraceAvoidCollisionLine_of_fullAvoid (Xq := Xq) hω
      intro n
      -- Proof comment: once the sampled jump trace avoids the collision line, the sampled
      -- jump collision code avoids `0` by the defining collision-code equivalence.
      simpa [axisBlockedFreePairJumpCollisionCodeProcess,
        mem_axisBlockedDefectCollisionLine_iff_collisionCode_eq_zero] using htrace n

/-- Helper for Exercise 18.2.4: the launched path-law mass of collision-line avoidance is exactly
the launched owner-law mass of the jump-code no-hit event. -/
private theorem axisBlockedFreePair_launchJumpCollisionCodeNoHit_mass_eq :
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      axisBlockedDefectAvoidCollisionLinePathEvent =
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
        (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) := by
  have hpreimage :
      (fun ω : Ωq ↦ fun n : ℕ ↦
        axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n) ⁻¹'
        axisBlockedDefectAvoidCollisionLinePathEvent =
        {ω : Ωq |
          ∀ n : ℕ,
            axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∉
              axisBlockedDefectCollisionLine} := by
    ext ω
    -- Proof comment: evaluating the path-space avoidance event under the realized launched
    -- trajectory is exactly the pointwise full-avoid condition on `Ωq`.
    simp [axisBlockedDefectAvoidCollisionLinePathEvent]
  calc
    Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent =
      (Pq ((((1, 0) : AxisState), ((1, 1) : AxisState))) : Measure Ωq)
        ((fun ω : Ωq ↦ fun n : ℕ ↦
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n) ⁻¹'
          axisBlockedDefectAvoidCollisionLinePathEvent) := by
            rw [independentProductPairRealizationPathKernel_apply
              (Pq := Pq) (Xq := Xq)
              ((((1, 0) : AxisState), ((1, 1) : AxisState)))]
            rw [Measure.map_map measurable_independentProductPairTrajectoryMap
              measurable_axisBlockedFreePairLatticePath]
            rw [Measure.map_apply
              (measurable_axisBlockedFreePairLatticePath.comp
                measurable_independentProductPairTrajectoryMap)
              measurableSet_axisBlockedDefectAvoidCollisionLinePathEvent]
    _ =
      (Pq ((((1, 0) : AxisState), ((1, 1) : AxisState))) : Measure Ωq)
        {ω : Ωq |
          ∀ n : ℕ,
            axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∉
              axisBlockedDefectCollisionLine} := by
            rw [hpreimage]
    _ =
      (Pq ((((1, 0) : AxisState), ((1, 1) : AxisState))) : Measure Ωq)
        (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) := by
            rw [← axisBlockedFreePair_launchJumpCollisionCodeNoHit_eq_fullAvoid (Xq := Xq)]
    _ =
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
        (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) := by
            rw [← axisBlockedFreePairDefectVisitOwnerLaw_launch (Pq := Pq)]

/-- Helper for Exercise 18.2.4: under the launched owner law, the explicit one-step history
`((1,0),(1,1)) → ((2,0),(2,1))` has strictly positive mass. -/
private theorem axisBlockedFreePair_launchImmediateRightHistory_pos :
    0 <
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
        ({ω | Xq 0 ω = (((1, 0) : AxisState), ((1, 1) : AxisState))} ∩
          {ω | Xq 1 ω = (((2, 0) : AxisState), ((2, 1) : AxisState))}) := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let startEvent : Set Ωq := {ω | Xq 0 ω = b}
  let launchEvent : Set Ωq := {ω | Xq 1 ω = c}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hstart_meas : MeasurableSet startEvent := by
    rw [show startEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [startEvent]]
    exact (hqreal.measurable_process 0) (measurableSet_singleton b)
  have hstart_hist0 : MeasurableSet[generatedFiltrationSpace Xq 0] startEvent := by
    have hX0 : Measurable[generatedFiltrationSpace Xq 0] (Xq 0) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 0
    rw [show startEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [startEvent]]
    exact hX0 (measurableSet_singleton b)
  have hstart_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ startEvent → Xq 0 ω = b := by
    intro ω hω
    exact hω
  have hstart_mass : μ startEvent = 1 := by
    rw [show startEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [startEvent]]
    rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton b)]
    rw [axisBlockedFreePairDefectVisitOwnerLaw_launch (Pq := Pq)]
    rw [hqreal.initial_eq b]
    simp [μ, b]
  have hhistory_mass :
      μ (startEvent ∩ launchEvent) =
        (discreteMatrixKernel independentProductPairMatrix b ({c} : Set (AxisState × AxisState))) *
          μ startEvent := by
    -- Proof comment: first fix the deterministic launch state `b`, then the one-step move to `c`
    -- factors through the free product-pair row from `b`.
    simpa [μ, startEvent, launchEvent] using
      measureInter_eq_mul_stepMass_of_stateEvent
        (q := independentProductPairMatrix) (P := Pq) (X := Xq)
        (x := b) (y := b) (w := c) (n := 0) (A := startEvent)
        hstart_meas hstart_hist0 hstart_state
  have hstep_pos :
      0 < discreteMatrixKernel independentProductPairMatrix b ({c} : Set (AxisState × AxisState)) := by
    rw [discreteMatrixKernel_apply_singleton]
    -- Proof comment: both walkers can step one unit to the right from the launched pair, giving
    -- the explicit history atom positive mass.
    norm_num [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, b, c]
  -- Proof comment: combine the exact one-step factorization with the deterministic start mass.
  rw [hhistory_mass, hstart_mass]
  simpa using hstep_pos

/-- Helper for Exercise 18.2.4: once the immediate-right launch history is fixed, the remaining
never-meet mass is exactly the future path-kernel row from `((2,0),(2,1))`. -/
private theorem axisBlockedFreePair_launchImmediateRightHistory_futureNeverMeet_mass :
    let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
    let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
    let μ : Measure Ωq :=
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
    let historyEvent : Set Ωq := {ω | Xq 0 ω = b} ∩ {ω | Xq 1 ω = c}
    let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
    μ (historyEvent ∩ futureEvent) =
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
        freePairNeverMeetPathEvent) * μ historyEvent := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let startEvent : Set Ωq := {ω | Xq 0 ω = b}
  let launchEvent : Set Ωq := {ω | Xq 1 ω = c}
  let historyEvent : Set Ωq := startEvent ∩ launchEvent
  let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hstart_meas : MeasurableSet startEvent := by
    rw [show startEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [startEvent]]
    exact (hqreal.measurable_process 0) (measurableSet_singleton b)
  have hstart_hist0 : MeasurableSet[generatedFiltrationSpace Xq 0] startEvent := by
    have hX0 : Measurable[generatedFiltrationSpace Xq 0] (Xq 0) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 0
    rw [show startEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [startEvent]]
    exact hX0 (measurableSet_singleton b)
  have hlaunch_meas : MeasurableSet launchEvent := by
    rw [show launchEvent = Xq 1 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [launchEvent]]
    exact (hqreal.measurable_process 1) (measurableSet_singleton c)
  have hlaunch_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] launchEvent := by
    have hX1 : Measurable[generatedFiltrationSpace Xq 1] (Xq 1) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 1
    rw [show launchEvent = Xq 1 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [launchEvent]]
    exact hX1 (measurableSet_singleton c)
  have hstart_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] startEvent := by
    exact (generatedFiltrationSpace_monoNat (X := Xq) (m := 0) (n := 1) (Nat.zero_le 1)) _
      hstart_hist0
  have hhistory_meas : MeasurableSet historyEvent := hstart_meas.inter hlaunch_meas
  have hhistory_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] historyEvent := by
    simpa [historyEvent] using hstart_hist1.inter hlaunch_hist1
  have hhistory_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ historyEvent → Xq 1 ω = c := by
    intro ω hω
    exact hω.2
  -- Proof comment: once the time-`1` state is fixed at `c`, the future never-meet event depends
  -- only on the realized future path-kernel row from `c`.
  simpa [μ, historyEvent, futureEvent] using
    independentProductPair_measureInter_eq_mul_futurePathMass_of_stateEvent
      (Pq := Pq) (Xq := Xq) (a := b) (y := c) (n := 1)
      (A := historyEvent) (B := freePairNeverMeetPathEvent)
      measurableSet_freePairNeverMeetPathEvent hhistory_meas hhistory_hist1 hhistory_state

/-- Helper for Exercise 18.2.4: the immediate-right history together with future never-meet
already sits inside the launched jump-code no-hit event. -/
private theorem axisBlockedFreePair_launchImmediateRightHistory_futureNeverMeet_subset_jumpNoHit :
    let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
    let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
    let historyEvent : Set Ωq := {ω | Xq 0 ω = b} ∩ {ω | Xq 1 ω = c}
    let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
    historyEvent ∩ futureEvent ⊆
      axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq) := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let historyEvent : Set Ωq := {ω | Xq 0 ω = b} ∩ {ω | Xq 1 ω = c}
  let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
  have hsubset_full :
      historyEvent ∩ futureEvent ⊆
        {ω : Ωq |
          ∀ n : ℕ,
            axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) n ∉
              axisBlockedDefectCollisionLine} := by
    intro ω hω n
    rcases hω with ⟨hhistory, hfuture⟩
    cases n with
    | zero =>
        have h0 : Xq 0 ω = b := hhistory.1
        -- Proof comment: on the history atom, the launched owner point at time `0` is exactly
        -- `![1,1,-1]`, which is already off the collision line.
        simpa [axisBlockedFreePairLatticePath, axisBlockedFreePairRelativePath,
          freePairRelativeStateToLatticePoint3, axisBlockedFreePairRelativeState, h0, b] using
          axisBlockedFreePairLatticePoint_launch_not_mem_collisionLine
    | succ n =>
        have hdiag :
            (Xq (n + 1) ω).1 ≠ (Xq (n + 1) ω).2 := by
          simpa [futureEvent, freePairNeverMeetPathEvent, futurePath] using hfuture n
        have hnot_line :
            freePairRelativeStateToLatticePoint3
                (axisBlockedFreePairRelativeState (Xq (n + 1) ω)) ∉
              axisBlockedDefectCollisionLine := by
          intro hline
          exact hdiag <|
            (mem_axisBlockedFreePairCollisionSet_iff (Xq (n + 1) ω)).1 <|
              (mem_axisBlockedDefectCollisionLine_iff
                (axisBlockedFreePairRelativeState (Xq (n + 1) ω))).1 hline
        -- Proof comment: from time `1` onward the future path never meets, so every later owner
        -- state stays off the encoded collision line as well.
        simpa [axisBlockedFreePairLatticePath, axisBlockedFreePairRelativePath] using hnot_line
  -- Proof comment: the earlier raw/sampled normalization already identifies full collision-line
  -- avoidance with the launched jump-code no-hit event.
  simpa [axisBlockedFreePair_launchJumpCollisionCodeNoHit_eq_fullAvoid (Xq := Xq)] using hsubset_full

/-- Helper for Exercise 18.2.4: for any start pair, the realized path-kernel row on the
never-meet event is the corresponding sample-space never-meet probability under `Pq`. -/
private theorem independentProductPairPathKernel_neverMeet_eq_measure
    (a : AxisState × AxisState) :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      a freePairNeverMeetPathEvent =
      (Pq a : Measure Ωq) {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
  have hpreimage :
      (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) ⁻¹' freePairNeverMeetPathEvent =
        {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
    -- Proof comment: the path-space never-meet event is exactly the pointwise off-diagonal
    -- condition on the realized sample-space trajectory.
    ext ω
    simp [freePairNeverMeetPathEvent]
  -- Proof comment: unfold the realized path-law row as a pushforward of `Pq a`, then rewrite the
  -- event preimage back to the pointwise never-meet event on `Ωq`.
  calc
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
        freePairNeverMeetPathEvent =
      Measure.map (fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) (Pq a : Measure Ωq)
        freePairNeverMeetPathEvent := by
          rw [independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq) a]
    _ =
        (Pq a : Measure Ωq)
          ((fun ω : Ωq ↦ fun n : ℕ ↦ Xq n ω) ⁻¹' freePairNeverMeetPathEvent) := by
            rw [Measure.map_apply measurable_independentProductPairTrajectoryMap
              measurableSet_freePairNeverMeetPathEvent]
    _ =
        (Pq a : Measure Ωq) {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
          simpa [hpreimage]

/-- Helper for Exercise 18.2.4: forcing one step from `((2,0),(2,1))` back to the launched pair
`((1,0),(1,1))` gives a direct lower bound on the two-right never-meet row. -/
private theorem axisBlockedFreePair_twoRightNeverMeet_lowerBoundFromLaunch :
    ((discreteMatrixKernel independentProductPairMatrix
        ((((2, 0) : AxisState), ((2, 1) : AxisState))))
      ({((((1, 0) : AxisState), ((1, 1) : AxisState)))} : Set (AxisState × AxisState))) *
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent ≤
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let μ : Measure Ωq := (Pq c : Measure Ωq)
  let initEvent : Set Ωq := {ω | Xq 0 ω = c}
  let returnEvent : Set Ωq := {ω | Xq 1 ω = b}
  let historyEvent : Set Ωq := initEvent ∩ returnEvent
  let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
  let neverMeet : Set Ωq := {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hinit_meas : MeasurableSet initEvent := by
    rw [show initEvent = Xq 0 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    exact (hqreal.measurable_process 0) (measurableSet_singleton c)
  have hinit_hist0 : MeasurableSet[generatedFiltrationSpace Xq 0] initEvent := by
    have hX0 : Measurable[generatedFiltrationSpace Xq 0] (Xq 0) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 0
    rw [show initEvent = Xq 0 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    exact hX0 (measurableSet_singleton c)
  have hreturn_meas : MeasurableSet returnEvent := by
    rw [show returnEvent = Xq 1 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [returnEvent]]
    exact (hqreal.measurable_process 1) (measurableSet_singleton b)
  have hreturn_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] returnEvent := by
    have hX1 : Measurable[generatedFiltrationSpace Xq 1] (Xq 1) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 1
    rw [show returnEvent = Xq 1 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [returnEvent]]
    exact hX1 (measurableSet_singleton b)
  have hinit_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] initEvent := by
    exact (generatedFiltrationSpace_monoNat (X := Xq) (m := 0) (n := 1) (Nat.zero_le 1)) _
      hinit_hist0
  have hhistory_meas : MeasurableSet historyEvent := hinit_meas.inter hreturn_meas
  have hhistory_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] historyEvent := by
    simpa [historyEvent] using hinit_hist1.inter hreturn_hist1
  have hhistory_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ historyEvent → Xq 1 ω = b := by
    intro ω hω
    exact hω.2
  have hinit_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ initEvent → Xq 0 ω = c := by
    intro ω hω
    exact hω
  have hinit_mass : μ initEvent = 1 := by
    rw [show initEvent = Xq 0 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton c)]
    rw [hqreal.initial_eq c]
    simp [μ]
  have hhistory_mass :
      μ historyEvent =
        (discreteMatrixKernel independentProductPairMatrix c ({b} : Set (AxisState × AxisState))) *
          μ initEvent := by
    -- Proof comment: first fix the deterministic two-right state `c`, then the one-step return
    -- to the launched pair `b` factors through the free product-pair row from `c`.
    simpa [μ, historyEvent] using
      measureInter_eq_mul_stepMass_of_stateEvent
        (q := independentProductPairMatrix) (P := Pq) (X := Xq)
        (x := c) (y := c) (w := b) (n := 0) (A := initEvent)
        hinit_meas hinit_hist0 hinit_state
  have hfuture_mass :
      μ (historyEvent ∩ futureEvent) =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
          freePairNeverMeetPathEvent) * μ historyEvent := by
    -- Proof comment: once time `1` is fixed at the launched pair `b`, the remaining never-meet
    -- event depends only on the future path-kernel row from `b`.
    simpa [μ, futureEvent] using
      independentProductPair_measureInter_eq_mul_futurePathMass_of_stateEvent
        (Pq := Pq) (Xq := Xq) (a := c) (y := b) (n := 1)
        (A := historyEvent) (B := freePairNeverMeetPathEvent)
        measurableSet_freePairNeverMeetPathEvent hhistory_meas hhistory_hist1 hhistory_state
  have htwoRight_offdiag : c.1 ≠ c.2 := by
    norm_num [c]
  have hsubset : historyEvent ∩ futureEvent ⊆ neverMeet := by
    intro ω hω
    intro n
    cases n with
    | zero =>
        have h0 : Xq 0 ω = c := hω.1.1
        simpa [neverMeet, c] using htwoRight_offdiag
    | succ n =>
        have hpath : futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent := hω.2
        simpa [futureEvent, freePairNeverMeetPathEvent, futurePath, neverMeet] using hpath n
  -- Proof comment: the explicit one-step return event from `c` to `b` sits inside the full
  -- two-right never-meet event, so its factored mass is a valid lower bound for the `c`-row.
  calc
    (discreteMatrixKernel independentProductPairMatrix c ({b} : Set (AxisState × AxisState))) *
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b
          freePairNeverMeetPathEvent =
      μ (historyEvent ∩ futureEvent) := by
        rw [hfuture_mass, hhistory_mass, hinit_mass]
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ μ neverMeet := measure_mono hsubset
    _ =
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent := by
            symm
            simpa [c, μ, neverMeet] using
              independentProductPairPathKernel_neverMeet_eq_measure
                (Pq := Pq) (Xq := Xq) c

/-- Helper for Exercise 18.2.4: for any start pair, the free-pair never-meet row is exactly the
encoded `ℤ^3` collision-line-avoidance mass of its lattice path law. -/
private theorem axisBlockedFreePair_pathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (a : AxisState × AxisState) :
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      a freePairNeverMeetPathEvent =
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a)
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Proof comment: rewrite the never-meet event as the preimage of encoded collision-line
  -- avoidance, then absorb that preimage into the pushforward measure for the row started at `a`.
  calc
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
        freePairNeverMeetPathEvent =
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
        (axisBlockedFreePairLatticePath ⁻¹' axisBlockedDefectAvoidCollisionLinePathEvent) := by
          rw [freePairNeverMeetPathEvent_eq_preimage_axisBlockedDefectAvoidCollisionLinePathEvent]
    _ =
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a)
        axisBlockedDefectAvoidCollisionLinePathEvent := by
          symm
          rw [Measure.map_apply measurable_axisBlockedFreePairLatticePath
            measurableSet_axisBlockedDefectAvoidCollisionLinePathEvent]

/-- Helper for Exercise 18.2.4: the truthful two-right bounded collision-line-avoidance mass on
encoded `ℤ^3` path space agrees with the off-diagonal mass of the diagonal-absorbed free-pair
chain. -/
private theorem axisBlockedFreePair_twoRightLatticeCollisionLineAvoidUpTo_eq_absorbedOffDiagonalMass
    (n : ℕ) :
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState))))
      (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) =
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
        ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  -- Proof comment: rewrite the encoded bounded collision-line event back to bounded diagonal
  -- avoidance of the truthful two-right free pair, then use the absorbed off-diagonal
  -- normalization for that concrete row.
  calc
    Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c)
        (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) =
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
        (axisBlockedFreePairLatticePath ⁻¹'
          axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
            rw [Measure.map_apply measurable_axisBlockedFreePairLatticePath
              (measurableSet_axisBlockedDefectAvoidCollisionLineUpToPathEvent n)]
    _ =
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
        (freePairAvoidDiagonalUpToPathEvent n) := by
          rw [←
            freePairAvoidDiagonalUpToPathEvent_eq_preimage_axisBlockedDefectAvoidCollisionLineUpToPathEvent]
    _ =
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) c)
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
          simpa [c] using
            (independentProductPairAbsorbDiagonal_offDiagonalMass_eq_freeAvoidDiagonalProb
              (Pq := Pq) (Xq := Xq) c n).symm

/-- Helper for Exercise 18.2.4: positive singleton masses compose across powers of a countable
discrete kernel. -/
private theorem discreteKernel_positiveSingletonComp
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (κ : Kernel S S) {m n : ℕ} {x y z : S}
    (hxy : 0 < (κ ^ m) x ({y} : Set S))
    (hyz : 0 < (κ ^ n) y ({z} : Set S)) :
    0 < (κ ^ (m + n)) x ({z} : Set S) := by
  -- Proof comment: expand the Chapman-Kolmogorov integral and keep the positive contribution
  -- coming from the intermediate singleton `{y}`.
  rw [Kernel.pow_add_apply_eq_lintegral κ m n x (measurableSet_singleton z)]
  have hsingleton :
      0 <
        ∫⁻ b in ({y} : Set S), (κ ^ n) b ({z} : Set S) ∂((κ ^ m) x) := by
    rw [MeasureTheory.lintegral_singleton]
    exact ENNReal.mul_pos hyz.ne' hxy.ne'
  have hmono :
      ∫⁻ b in ({y} : Set S), (κ ^ n) b ({z} : Set S) ∂((κ ^ m) x) ≤
        ∫⁻ b in Set.univ, (κ ^ n) b ({z} : Set S) ∂((κ ^ m) x) :=
    MeasureTheory.lintegral_mono_set
      (show ({y} : Set S) ⊆ Set.univ from Set.subset_univ _)
  exact lt_of_lt_of_le hsingleton (by simpa [Measure.restrict_univ] using hmono)

/-- Helper for Exercise 18.2.4: after three absorbed steps from the truthful two-right row, the
diagonal endpoint `((0,0),(0,0))` already has positive mass. -/
private theorem axisBlockedFreePair_twoRightAbsorbedDiagonalEndpoint_three_pos :
    0 <
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ 3)
        ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        ({((((0, 0) : AxisState), ((0, 0) : AxisState)))} : Set (AxisState × AxisState)) := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let u : AxisState × AxisState := (((2, 0) : AxisState), ((1, 1) : AxisState))
  let v : AxisState × AxisState := (((1, 0) : AxisState), ((0, 1) : AxisState))
  let d : AxisState × AxisState := (((0, 0) : AxisState), ((0, 0) : AxisState))
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  have hstep_cu :
      0 < κAbs c ({u} : Set (AxisState × AxisState)) := by
    -- Proof comment: from `c`, keep the first walker fixed and move the second walker one step
    -- left to reach the intermediate state `u`.
    rw [discreteMatrixKernel_apply_singleton]
    norm_num [κAbs, independentProductPairAbsorbDiagonalMatrix, independentProductPairMatrix,
      vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor, isHorizontalNeighbor,
      isVerticalNeighbor, c, u]
  have hstep_uv :
      0 < κAbs u ({v} : Set (AxisState × AxisState)) := by
    -- Proof comment: from `u`, both walkers step one unit left, landing at `v`.
    rw [discreteMatrixKernel_apply_singleton]
    norm_num [κAbs, independentProductPairAbsorbDiagonalMatrix, independentProductPairMatrix,
      vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor, isHorizontalNeighbor,
      isVerticalNeighbor, u, v]
  have hstep_vd :
      0 < κAbs v ({d} : Set (AxisState × AxisState)) := by
    -- Proof comment: from `v`, the first walker steps left to the axis and the second walker
    -- steps down on the axis, producing the diagonal endpoint `d`.
    rw [discreteMatrixKernel_apply_singleton]
    norm_num [κAbs, independentProductPairAbsorbDiagonalMatrix, independentProductPairMatrix,
      vertical_axis_blocked_walk_transition_matrix, isAxisNeighbor, isHorizontalNeighbor,
      isVerticalNeighbor, v, d]
  have hstep_cv :
      0 < (κAbs ^ 2) c ({v} : Set (AxisState × AxisState)) := by
    -- Proof comment: compose the positive steps `c → u` and `u → v`.
    simpa [pow_one, Nat.add_comm] using
      discreteKernel_positiveSingletonComp κAbs
        (m := 1) (n := 1) (x := c) (y := u) (z := v)
        (by simpa [pow_one] using hstep_cu)
        (by simpa [pow_one] using hstep_uv)
  -- Proof comment: a second application of the same composition rule along `v → d` gives the
  -- positive three-step diagonal mass from `c`.
  simpa [show (3 : ℕ) = 2 + 1 by norm_num, Nat.add_comm] using
    discreteKernel_positiveSingletonComp κAbs
      (m := 2) (n := 1) (x := c) (y := v) (z := d) hstep_cv
      (by simpa [pow_one] using hstep_vd)

/-- Helper for Exercise 18.2.4: by time `3`, the truthful two-right absorbed off-diagonal mass
has already dropped below `1`. -/
private theorem axisBlockedFreePair_twoRightAbsorbedOffDiagonalMass_three_lt_one :
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ 3)
      ((((2, 0) : AxisState), ((2, 1) : AxisState))))
      {s : AxisState × AxisState | s.1 ≠ s.2} < 1 := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let d : AxisState × AxisState := (((0, 0) : AxisState), ((0, 0) : AxisState))
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  let offDiag : Set (AxisState × AxisState) := {s : AxisState × AxisState | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hdiag_pos :
      0 < ((κAbs ^ 3) c) ({d} : Set (AxisState × AxisState)) := by
    simpa [κAbs, c, d] using
      axisBlockedFreePair_twoRightAbsorbedDiagonalEndpoint_three_pos
  have hcomp_pos : 0 < ((κAbs ^ 3) c) offDiagᶜ := by
    -- Proof comment: the positive diagonal singleton mass sits inside the complement of the
    -- off-diagonal event.
    exact lt_of_lt_of_le hdiag_pos <| measure_mono <| by
      intro s hs
      simp [offDiag, d] at hs ⊢
      simpa [hs]
  have hsum :
      ((κAbs ^ 3) c) offDiag + ((κAbs ^ 3) c) offDiagᶜ = 1 := by
    -- Proof comment: every absorbed row is a probability measure, so a measurable set and its
    -- complement have total mass `1`.
    simpa using measure_add_measure_compl ((κAbs ^ 3) c) hoffDiag_meas
  have hlt :
      ((κAbs ^ 3) c) offDiag <
        ((κAbs ^ 3) c) offDiag + ((κAbs ^ 3) c) offDiagᶜ := by
    exact lt_add_of_pos_right hcomp_pos
  -- Proof comment: the positive diagonal mass forces the complementary off-diagonal mass to be
  -- strictly smaller than the full total mass.
  rw [hsum] at hlt
  simpa [κAbs, c, offDiag] using hlt

/-- Helper for Exercise 18.2.4: strict positivity of the launched jump-code no-hit event already
forces the start-pair collision-code no-hit mass via the established launch-to-start transport
chain. -/
private theorem axisBlockedFreePair_startCollisionCodeNoHit_pos_of_launchJumpCollisionCodeNoHitPos
    (hlaunchJump :
      0 <
        (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
          (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq))) :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  have hlaunchLine :
      0 <
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent := by
    -- Proof comment: the launched sample-space jump-code no-hit event is exactly the launched
    -- lattice-path collision-line-avoidance mass under the established pushforward identity.
    rw [axisBlockedFreePair_launchJumpCollisionCodeNoHit_mass_eq (Pq := Pq) (Xq := Xq)]
    exact hlaunchJump
  have hlaunchNever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
    -- Proof comment: rewrite the launched collision-line-avoidance mass back to the launched
    -- free-pair never-meet row.
    rw [← axisBlockedFreePair_launchPathKernel_neverMeet_eq_latticeCollisionLineAvoid
      (Pq := Pq) (Xq := Xq)]
    exact hlaunchLine
  -- Proof comment: the existing launch-to-start bridge now transports the launched never-meet
  -- positivity directly to the start-pair collision-code no-hit mass.
  exact
    axisBlockedFreePair_startCollisionCodeNoHit_pos_of_launchNeverMeetPos
      (Pq := Pq) (Xq := Xq) hlaunchNever

/-- Helper for Exercise 18.2.4: any dependency-legal positive lower bound for the launched
never-meet row immediately propagates to the truthful two-right row through the explicit one-step
return to launch. -/
private theorem axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_launchNeverMeetPos
    (hlaunch :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent) :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  have hstep_pos :
      0 <
        (discreteMatrixKernel independentProductPairMatrix c)
          ({b} : Set (AxisState × AxisState)) := by
    rw [discreteMatrixKernel_apply_singleton]
    -- Proof comment: from the two-right row `c`, both walkers can step one unit left and return
    -- to the launched row `b` with strictly positive one-step mass.
    norm_num [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, b, c]
  have hlower :
      ((discreteMatrixKernel independentProductPairMatrix c)
        ({b} : Set (AxisState × AxisState))) *
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          b freePairNeverMeetPathEvent ≤
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        c freePairNeverMeetPathEvent := by
    -- Proof comment: the earlier explicit-history factorization already lower-bounds the two-right
    -- never-meet row by the one-step return mass times the launched never-meet row.
    simpa [b, c] using
      axisBlockedFreePair_twoRightNeverMeet_lowerBoundFromLaunch
        (Pq := Pq) (Xq := Xq)
  have hmul_pos :
      0 <
        ((discreteMatrixKernel independentProductPairMatrix c)
          ({b} : Set (AxisState × AxisState))) *
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          b freePairNeverMeetPathEvent := by
    -- Proof comment: multiply the positive one-step return mass by the assumed positive launched
    -- never-meet row.
    exact ENNReal.mul_pos hstep_pos hlaunch
  -- Proof comment: monotonicity along the explicit one-step return lower bound upgrades the
  -- launched positivity to the truthful two-right row.
  exact lt_of_lt_of_le hmul_pos hlower

/-- Helper for Exercise 18.2.4: from the truthful two-right owner point `![2,2,-1]`, one SRW3
step cannot land at the origin. -/
private theorem symmetricSimpleRandomWalk3_twoRight_stepMass_origin_eq_zero :
    (discreteMatrixKernel
      (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
      ![2, 2, -1]) ({(0 : LatticePoint 3)} : Set (LatticePoint 3)) = 0 := by
  rw [discreteMatrixKernel_apply_singleton]
  rw [latticeConvolutionStepMatrix_isTranslationInvariant
    (ν := symmetricSimpleRandomWalkStepPMF 3) ![2, 2, -1] 0]
  have hdiff : (0 : LatticePoint 3) - ![2, 2, -1] = ![-2, -2, 1] := by
    ext i
    fin_cases i <;> norm_num
  rw [hdiff]
  rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
  -- Proof comment: the displacement `![-2,-2,1]` changes more than one coordinate, so it is not
  -- one of the six allowed SRW3 increments.
  rw [symmetricSimpleRandomWalkStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num

/-- Helper for Exercise 18.2.4: from the truthful two-right owner point `![2,2,-1]`, one SRW3
step cannot land on any lattice neighbor of the origin. -/
private theorem symmetricSimpleRandomWalk3_twoRight_stepMass_originNeighbor_eq_zero
    (target : LatticePoint 3)
    (htarget :
      target = Pi.single 0 (1 : ℤ) ∨
        target = Pi.single 0 (-1 : ℤ) ∨
        target = Pi.single 1 (1 : ℤ) ∨
        target = Pi.single 1 (-1 : ℤ) ∨
        target = Pi.single 2 (1 : ℤ) ∨
        target = Pi.single 2 (-1 : ℤ)) :
    (discreteMatrixKernel
      (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
      ![2, 2, -1]) ({target} : Set (LatticePoint 3)) = 0 := by
  rw [discreteMatrixKernel_apply_singleton]
  rw [latticeConvolutionStepMatrix_isTranslationInvariant
    (ν := symmetricSimpleRandomWalkStepPMF 3) ![2, 2, -1] target]
  rcases htarget with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
    -- Proof comment: every origin neighbor differs from `![2,2,-1]` in at least two
    -- coordinates, so none of them can be reached in one SRW3 step.
    rw [symmetricSimpleRandomWalkStepPMF, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
      Fintype.sum_bool]
    norm_num

/-- Helper for Exercise 18.2.4: fixing the explicit immediate-right launch history lowers the
shifted launch bounded collision-line-avoidance mass to the truthful two-right future row. -/
private theorem axisBlockedFreePair_launchBoundedCollisionAvoidUpTo_lowerBoundFromImmediateRightHistory
    (n : ℕ) :
    let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
    let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
    let historyEvent : Set Ωq := {ω | Xq 0 ω = b} ∩ {ω | Xq 1 ω = c}
    ((Pq b : Measure Ωq) historyEvent) *
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c)
          (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) ≤
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
        (axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + 1)) := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let startEvent : Set Ωq := {ω | Xq 0 ω = b}
  let stepEvent : Set Ωq := {ω | Xq 1 ω = c}
  let historyEvent : Set Ωq := startEvent ∩ stepEvent
  let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairAvoidDiagonalUpToPathEvent n}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hstart_meas : MeasurableSet startEvent := by
    rw [show startEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [startEvent]]
    exact (hqreal.measurable_process 0) (measurableSet_singleton b)
  have hstart_hist0 : MeasurableSet[generatedFiltrationSpace Xq 0] startEvent := by
    have hX0 : Measurable[generatedFiltrationSpace Xq 0] (Xq 0) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 0
    rw [show startEvent = Xq 0 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [startEvent]]
    exact hX0 (measurableSet_singleton b)
  have hstep_meas : MeasurableSet stepEvent := by
    rw [show stepEvent = Xq 1 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [stepEvent]]
    exact (hqreal.measurable_process 1) (measurableSet_singleton c)
  have hstep_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] stepEvent := by
    have hX1 : Measurable[generatedFiltrationSpace Xq 1] (Xq 1) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 1
    rw [show stepEvent = Xq 1 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [stepEvent]]
    exact hX1 (measurableSet_singleton c)
  have hstart_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] startEvent := by
    exact (generatedFiltrationSpace_monoNat (X := Xq) (m := 0) (n := 1) (Nat.zero_le 1)) _
      hstart_hist0
  have hhistory_meas : MeasurableSet historyEvent := hstart_meas.inter hstep_meas
  have hhistory_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] historyEvent := by
    simpa [historyEvent] using hstart_hist1.inter hstep_hist1
  have hhistory_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ historyEvent → Xq 1 ω = c := by
    intro ω hω
    exact hω.2
  have hhistory_future_mass :
      (Pq b : Measure Ωq) (historyEvent ∩ futureEvent) =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          (freePairAvoidDiagonalUpToPathEvent n)) *
          (Pq b : Measure Ωq) historyEvent := by
    -- Proof comment: once the explicit immediate-right history is fixed, the remaining bounded
    -- event depends only on the truthful two-right future path-kernel row.
    simpa [historyEvent, futureEvent, b, c] using
      independentProductPair_measureInter_eq_mul_futurePathMass_of_stateEvent
        (Pq := Pq) (Xq := Xq) (a := b) (y := c) (n := 1)
        (A := historyEvent) (B := freePairAvoidDiagonalUpToPathEvent n)
        (measurableSet_freePairAvoidDiagonalUpToPathEvent n)
        hhistory_meas hhistory_hist1 hhistory_state
  have htwoRight_bounded :
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          (freePairAvoidDiagonalUpToPathEvent n) =
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c)
          (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
    -- Proof comment: rewrite the two-right bounded diagonal-avoidance row as the corresponding
    -- encoded collision-line-avoidance row on `ℤ^3` path space.
    calc
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          (freePairAvoidDiagonalUpToPathEvent n) =
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          (axisBlockedFreePairLatticePath ⁻¹'
            axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
              rw [freePairAvoidDiagonalUpToPathEvent_eq_preimage_axisBlockedDefectAvoidCollisionLineUpToPathEvent]
      _ =
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c)
          (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
            symm
            rw [Measure.map_apply measurable_axisBlockedFreePairLatticePath
              (measurableSet_axisBlockedDefectAvoidCollisionLineUpToPathEvent n)]
  have hsubset :
      historyEvent ∩ futureEvent ⊆
        {ω : Ωq |
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) ∈
            axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + 1)} := by
    intro ω hω
    rcases hω with ⟨hhistory, hfuture⟩
    intro m hm
    cases m with
    | zero =>
        have h0 : Xq 0 ω = b := hhistory.1
        -- Proof comment: at time `0`, the launched state itself is already off the collision
        -- line.
        simpa [axisBlockedDefectAvoidCollisionLineUpToPathEvent, axisBlockedFreePairLatticePath,
          axisBlockedFreePairRelativePath, freePairRelativeStateToLatticePoint3,
          axisBlockedFreePairRelativeState, h0, b] using
          axisBlockedFreePairLatticePoint_launch_not_mem_collisionLine
    | succ m =>
        have hm' : m ≤ n := Nat.le_of_succ_le_succ hm
        have hdiag : (Xq (m + 1) ω).1 ≠ (Xq (m + 1) ω).2 := by
          -- Proof comment: after time `1`, the bounded future event is exactly diagonal
          -- avoidance for the underlying free pair.
          simpa [futureEvent, freePairAvoidDiagonalUpToPathEvent, futurePath] using hfuture m hm'
        have hnot_line :
            freePairRelativeStateToLatticePoint3
                (axisBlockedFreePairRelativeState (Xq (m + 1) ω)) ∉
              axisBlockedDefectCollisionLine := by
          intro hline
          exact hdiag <|
            (mem_axisBlockedFreePairCollisionSet_iff (Xq (m + 1) ω)).1 <|
              (mem_axisBlockedDefectCollisionLine_iff
                (axisBlockedFreePairRelativeState (Xq (m + 1) ω))).1 hline
        -- Proof comment: away from time `0`, the encoded lattice path just records the current
        -- relative state of the free pair, so diagonal avoidance becomes collision-line avoidance.
        simpa [axisBlockedDefectAvoidCollisionLineUpToPathEvent, axisBlockedFreePairLatticePath,
          axisBlockedFreePairRelativePath] using hnot_line
  have hlaunch_bounded :
      (Pq b : Measure Ωq)
        {ω : Ωq |
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) ∈
            axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + 1)} =
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
          (axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + 1)) := by
    -- Proof comment: evaluate the launched realized path law on the encoded bounded
    -- collision-line-avoidance event.
    rw [independentProductPairRealizationPathKernel_apply (Pq := Pq) (Xq := Xq) b]
    rw [Measure.map_map measurable_independentProductPairTrajectoryMap
      measurable_axisBlockedFreePairLatticePath]
    symm
    rw [Measure.map_apply
      (measurable_axisBlockedFreePairLatticePath.comp
        measurable_independentProductPairTrajectoryMap)
      (measurableSet_axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + 1))]
  -- Proof comment: keep only the immediate-right history atom, then rewrite the resulting future
  -- row and the target launch row into the same bounded encoded collision-line events.
  calc
    ((Pq b : Measure Ωq) historyEvent) *
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c)
          (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) =
      (Pq b : Measure Ωq) (historyEvent ∩ futureEvent) := by
        rw [← htwoRight_bounded, mul_comm, ← hhistory_future_mass]
    _ ≤
      (Pq b : Measure Ωq)
        {ω : Ωq |
          axisBlockedFreePairLatticePath (fun m : ℕ ↦ Xq m ω) ∈
            axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + 1)} := by
            exact measure_mono hsubset
    _ =
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
        (axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + 1)) := hlaunch_bounded

/-- Helper for Exercise 18.2.4: the absorbed SRW3 kernel has a strictly positive explicit
two-step mass from `![2,2,-1]` down to `![1,1,-1]`. -/
private theorem canonicalSymmetricSimpleRandomWalk3_twoRightToLaunchTwoStepMass_pos :
    0 <
      ((discreteMatrixKernel
        (absorbAtOriginStepMatrix
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))) ^ 2)
        (![2, 2, -1] : LatticePoint 3))
        ({(![1, 1, -1] : LatticePoint 3)} : Set (LatticePoint 3)) := by
  let κAbs : Kernel (LatticePoint 3) (LatticePoint 3) :=
    discreteMatrixKernel
      (absorbAtOriginStepMatrix
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))
  let twoRight : LatticePoint 3 := ![2, 2, -1]
  let mid : LatticePoint 3 := ![1, 2, -1]
  let launch : LatticePoint 3 := ![1, 1, -1]
  have htwoRight_ne_zero : twoRight ≠ 0 := by
    norm_num [twoRight]
  have hmid_ne_zero : mid ≠ 0 := by
    norm_num [mid]
  have hstep_twoRight_mid :
      0 < κAbs twoRight ({mid} : Set (LatticePoint 3)) := by
    -- Proof comment: the absorbed walk agrees with SRW3 off the origin, and from `![2,2,-1]`
    -- the explicit step to `![1,2,-1]` is a single allowed negative first-coordinate move.
    rw [discreteMatrixKernel_apply_singleton]
    rw [absorbAtOriginStepMatrix_apply_of_ne_origin htwoRight_ne_zero]
    rw [latticeConvolutionStepMatrix_isTranslationInvariant
      (ν := symmetricSimpleRandomWalkStepPMF 3) twoRight mid]
    have hdiff : mid - twoRight = Pi.single 0 (-1 : ℤ) := by
      ext i
      fin_cases i <;> norm_num [mid, twoRight]
    rw [hdiff]
    rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
    rw [symmetricSimpleRandomWalkStepPMF, PMF.map_apply, tsum_fintype,
      Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
  have hstep_mid_launch :
      0 < κAbs mid ({launch} : Set (LatticePoint 3)) := by
    -- Proof comment: from `![1,2,-1]`, the explicit step to `![1,1,-1]` is the allowed
    -- negative second-coordinate move.
    rw [discreteMatrixKernel_apply_singleton]
    rw [absorbAtOriginStepMatrix_apply_of_ne_origin hmid_ne_zero]
    rw [latticeConvolutionStepMatrix_isTranslationInvariant
      (ν := symmetricSimpleRandomWalkStepPMF 3) mid launch]
    have hdiff : launch - mid = Pi.single 1 (-1 : ℤ) := by
      ext i
      fin_cases i <;> norm_num [launch, mid]
    rw [hdiff]
    rw [symmetricSimpleRandomWalk3_stepMatrix_originRow]
    rw [symmetricSimpleRandomWalkStepPMF, PMF.map_apply, tsum_fintype,
      Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
  -- Proof comment: composing the two explicit positive one-step masses yields a positive
  -- two-step absorbed mass from `![2,2,-1]` down to `![1,1,-1]`.
  simpa [κAbs, twoRight, launch, show (2 : ℕ) = 1 + 1 by norm_num, Nat.add_comm] using
    discreteKernel_positiveSingletonComp κAbs
      (m := 1) (n := 1) (x := twoRight) (y := mid) (z := launch)
      (by simpa [pow_one] using hstep_twoRight_mid)
      (by simpa [pow_one] using hstep_mid_launch)

/-- Helper for Exercise 18.2.4: the explicit two-step SRW3 history
`![2,2,-1] → ![1,2,-1] → ![1,1,-1]` gives a fixed positive finite shift from launch-side
bounded origin avoidance to truthful two-right bounded origin avoidance. -/
private theorem canonicalSymmetricSimpleRandomWalk3_launchBoundedAvoid_le_shiftedTwoRightAvoid
    (P : LatticePoint 3 → ProbabilityMeasure (ℕ → LatticePoint 3))
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P Function.eval]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))] :
    ∃ c0 : ℝ≥0∞,
      0 < c0 ∧ c0 ≠ ⊤ ∧
        ∀ n : ℕ,
          c0 *
              (P (![1, 1, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
                (latticeAvoidOriginUpToPathEvent n) ≤
            (P (![2, 2, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
              (latticeAvoidOriginUpToPathEvent (n + 2)) := by
  let κAbs : Kernel (LatticePoint 3) (LatticePoint 3) :=
    discreteMatrixKernel
      (absorbAtOriginStepMatrix
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))
  let launch : LatticePoint 3 := ![1, 1, -1]
  let twoRight : LatticePoint 3 := ![2, 2, -1]
  let offOrigin : Set (LatticePoint 3) := {z : LatticePoint 3 | z ≠ 0}
  let c0 : ℝ≥0∞ := ((κAbs ^ 2) twoRight) ({launch} : Set (LatticePoint 3))
  have hc0_pos : 0 < c0 := by
    simpa [κAbs, c0, twoRight, launch] using
      canonicalSymmetricSimpleRandomWalk3_twoRightToLaunchTwoStepMass_pos
  have hc0_ne_top : c0 ≠ ⊤ := by
    simpa [c0] using (measure_ne_top ((κAbs ^ 2) twoRight) ({launch} : Set (LatticePoint 3)))
  refine ⟨c0, hc0_pos, hc0_ne_top, fun n ↦ ?_⟩
  have hoffOrigin_meas : MeasurableSet offOrigin := MeasurableSet.of_discrete
  have hkernel_bound :
      c0 * ((κAbs ^ n) launch) offOrigin ≤ ((κAbs ^ (n + 2)) twoRight) offOrigin := by
    -- Proof comment: expand the two-right absorbed row after the fixed two-step prefix, then keep
    -- only the singleton contribution landing at the launch point `![1,1,-1]`.
    calc
      c0 * ((κAbs ^ n) launch) offOrigin =
          ((κAbs ^ n) launch) offOrigin * ((κAbs ^ 2) twoRight) ({launch} : Set (LatticePoint 3)) := by
            rw [mul_comm]
      _ ≤
          ∑' d : LatticePoint 3,
            ((κAbs ^ n) d) offOrigin * ((κAbs ^ 2) twoRight) ({d} : Set (LatticePoint 3)) := by
              exact ENNReal.le_tsum launch
      _ =
          ∫⁻ d, ((κAbs ^ n) d) offOrigin ∂((κAbs ^ 2) twoRight) := by
            simpa [mul_comm] using
              (MeasureTheory.lintegral_countable'
                (μ := (κAbs ^ 2) twoRight)
                (f := fun d : LatticePoint 3 ↦ ((κAbs ^ n) d) offOrigin))
      _ = ((κAbs ^ (2 + n)) twoRight) offOrigin := by
            rw [← Kernel.pow_add_apply_eq_lintegral κAbs 2 n twoRight hoffOrigin_meas]
      _ = ((κAbs ^ (n + 2)) twoRight) offOrigin := by
            simp [Nat.add_comm]
  -- Proof comment: rewrite both bounded avoid-origin probabilities as absorbed nonorigin masses
  -- and apply the explicit two-step kernel lower bound.
  rw [absorbedNonoriginMass_eq_boundedAvoidOriginProb
    (q := latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
    (P := P) (X := Function.eval) launch n]
  rw [absorbedNonoriginMass_eq_boundedAvoidOriginProb
    (q := latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3))
    (P := P) (X := Function.eval) twoRight (n + 2)]
  simpa [κAbs, c0, offOrigin, twoRight, launch] using hkernel_bound

/-- Helper for Exercise 18.2.4: one absorbed step from any off-defect pair with nonzero relative
vertical difference stays off the diagonal with total mass `1`. -/
private theorem
    independentProductPairAbsorbDiagonal_offDiagonalMass_one_eq_one_of_offDefect_nonzeroRelativeDifference
    {s : AxisState × AxisState}
    (hs1 : s.1.1 ≠ 0) (hs2 : s.2.1 ≠ 0)
    (hdiff : (axisBlockedFreePairRelativeState s).2 ≠ 0) :
    (discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix s)
      {t : AxisState × AxisState | t.1 ≠ t.2} = 1 := by
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  let offDiag : Set (AxisState × AxisState) := {t : AxisState × AxisState | t.1 ≠ t.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hdiag_zero : κAbs s offDiagᶜ = 0 := by
    rw [discreteMatrixKernel_apply,
      Measure.sum_apply _ (show MeasurableSet offDiagᶜ by simpa using hoffDiag_meas.compl)]
    refine ENNReal.tsum_eq_zero.2 ?_
    intro t
    by_cases ht : t ∈ offDiagᶜ
    · have hdiag : t.1 = t.2 := by
        simpa [offDiag] using ht
      have hmass :
          independentProductPairMatrix s t = 0 := by
        -- Proof comment: from an off-defect state with nonzero relative difference, the free
        -- product-pair chain cannot jump onto the diagonal in a single step.
        exact
          independentProductPairMatrix_offDefect_collision_zero_of_nonzeroRelativeDifference
            (s := s) (t := t) hs1 hs2 hdiff
            ((mem_axisBlockedFreePairCollisionSet_iff t).2 hdiag)
      -- Proof comment: the absorbed kernel agrees with the free kernel away from the diagonal, so
      -- every diagonal target contributes zero mass.
      simp [κAbs, independentProductPairAbsorbDiagonalMatrix, offDiag, ht, hdiag, hmass]
    · simp [offDiag, ht]
  have hsum : κAbs s offDiag + κAbs s offDiagᶜ = 1 := by
    simpa [κAbs] using measure_add_measure_compl (κAbs s) hoffDiag_meas
  -- Proof comment: the diagonal complement is null, so the whole one-step absorbed mass stays on
  -- the off-diagonal event.
  rw [hdiag_zero, add_zero] at hsum
  exact hsum

/-- Helper for Exercise 18.2.4: from the truthful two-right row, one absorbed step still stays
off the diagonal with total mass `1`. -/
private theorem axisBlockedFreePair_twoRightAbsorbedOffDiagonalMass_one_eq_one :
    (discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
      ((((2, 0) : AxisState), ((2, 1) : AxisState))))
      {t : AxisState × AxisState | t.1 ≠ t.2} = 1 := by
  -- Proof comment: the truthful two-right row is off the defect set and has relative vertical
  -- difference `-1`, so the generic one-step off-diagonal lemma applies directly.
  simpa [axisBlockedFreePairRelativeState] using
    independentProductPairAbsorbDiagonal_offDiagonalMass_one_eq_one_of_offDefect_nonzeroRelativeDifference
      (s := ((((2, 0) : AxisState), ((2, 1) : AxisState))))
      (by norm_num) (by norm_num) (by norm_num)

/-- Helper for Exercise 18.2.4: every one-step absorbed successor of the truthful two-right row
still has nonzero first coordinates and nonzero relative vertical difference. -/
private theorem axisBlockedFreePair_twoRightAbsorbedSafeSupport_compl_zero :
    let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
    let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
      discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
    let safeSupport : Set (AxisState × AxisState) :=
      {t | t.1.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ (axisBlockedFreePairRelativeState t).2 ≠ 0}
    κAbs c safeSupportᶜ = 0 := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  let safeSupport : Set (AxisState × AxisState) :=
    {t | t.1.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ (axisBlockedFreePairRelativeState t).2 ≠ 0}
  have hc_offDiag : c.1 ≠ c.2 := by
    norm_num [c]
  rw [discreteMatrixKernel_apply,
    Measure.sum_apply _ (show MeasurableSet safeSupportᶜ by exact MeasurableSet.of_discrete)]
  refine ENNReal.tsum_eq_zero.2 ?_
  intro t
  by_cases ht : t ∈ safeSupportᶜ
  · rcases t with ⟨⟨z₁, z₂⟩, ⟨w₁, w₂⟩⟩
    have hbad : z₁ = 0 ∨ w₁ = 0 ∨ z₂ - w₂ = 0 := by
      by_cases hz₁ : z₁ = 0
      · exact Or.inl hz₁
      · by_cases hw₁ : w₁ = 0
        · exact Or.inr <| Or.inl hw₁
        · by_cases hdiff : z₂ - w₂ = 0
          · exact Or.inr <| Or.inr hdiff
          · exfalso
            exact ht <| by
              simp [safeSupport, axisBlockedFreePairRelativeState, hz₁, hw₁, hdiff]
    have hmass : independentProductPairAbsorbDiagonalMatrix c ((z₁, z₂), (w₁, w₂)) = 0 := by
      rw [independentProductPairAbsorbDiagonalMatrix, if_neg hc_offDiag]
      rcases hbad with hz₁ | hw₁ | hdiff
      · subst hz₁
        simp [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
          isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor]
      · subst hw₁
        simp [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
          isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor]
      · have hchange : z₂ - w₂ ≠ (0 : ℤ) - 1 := by
          simpa [hdiff]
        exact
          independentProductPairMatrix_offDefect_changeRelativeDifference_zero
            (x₁ := 2) (x₂ := 0) (y₁ := 2) (y₂ := 1)
            (z₁ := z₁) (z₂ := z₂) (w₁ := w₁) (w₂ := w₂)
            (by norm_num) (by norm_num) hchange
    simp [ht, hmass]
  · simp [ht]

/-- Helper for Exercise 18.2.4: after two absorbed steps from the truthful two-right row, the
entire mass is still off the diagonal. -/
private theorem axisBlockedFreePair_twoRightAbsorbedOffDiagonalMass_two_eq_one :
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ 2)
      ((((2, 0) : AxisState), ((2, 1) : AxisState))))
      {s : AxisState × AxisState | s.1 ≠ s.2} = 1 := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  let offDiag : Set (AxisState × AxisState) := {s : AxisState × AxisState | s.1 ≠ s.2}
  let safeSupport : Set (AxisState × AxisState) :=
    {t | t.1.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ (axisBlockedFreePairRelativeState t).2 ≠ 0}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hsafe_compl_zero : κAbs c safeSupportᶜ = 0 := by
    simpa [c, κAbs, safeSupport] using
      axisBlockedFreePair_twoRightAbsorbedSafeSupport_compl_zero
  have hsafe_ae : ∀ᵐ t ∂(κAbs c), t ∈ safeSupport := by
    exact compl_mem_ae_iff.2 hsafe_compl_zero
  have hrow_one :
      ∀ ⦃t : AxisState × AxisState⦄, t ∈ safeSupport → κAbs t offDiag = 1 := by
    intro t ht
    exact
      independentProductPairAbsorbDiagonal_offDiagonalMass_one_eq_one_of_offDefect_nonzeroRelativeDifference
        (s := t) ht.1 ht.2.1 ht.2.2
  calc
    ((κAbs ^ 2) c) offDiag = ∫⁻ t, κAbs t offDiag ∂(κAbs c) := by
      rw [Kernel.pow_succ_apply_eq_lintegral κAbs 1 c hoffDiag_meas, pow_one]
    _ = ∫⁻ _t, (1 : ℝ≥0∞) ∂(κAbs c) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hsafe_ae] with t ht
          simp [hrow_one ht]
    _ = 1 := by
          simp

/-- Helper for Exercise 18.2.4: after one absorbed step from the truthful two-right row, the
remaining off-diagonal mass dominates the launched off-diagonal mass scaled by the explicit
one-step return mass to `((1,0),(1,1))`. -/
private theorem axisBlockedFreePair_twoRightAbsorbedOffDiagonalMass_ge_launchMass
    (n : ℕ) :
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ (n + 1))
      ((((2, 0) : AxisState), ((2, 1) : AxisState))))
      {s : AxisState × AxisState | s.1 ≠ s.2} ≥
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
          ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        ({((((1, 0) : AxisState), ((1, 1) : AxisState)))} : Set (AxisState × AxisState))) *
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  let offDiag : Set (AxisState × AxisState) := {s : AxisState × AxisState | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  -- Proof comment: expand the absorbed `(n + 1)`-step row as one absorbed step from the truthful
  -- two-right row `c`, then keep only the singleton contribution from the launched row `b`.
  calc
    ((κAbs ^ (n + 1)) c) offDiag
        = ∫⁻ d, ((κAbs ^ n) d) offDiag ∂(κAbs c) := by
            rw [Kernel.pow_succ_apply_eq_lintegral κAbs n c hoffDiag_meas]
    _ =
        ∑' d : AxisState × AxisState,
          ((κAbs ^ n) d) offDiag * (κAbs c) ({d} : Set (AxisState × AxisState)) := by
            simpa [mul_comm] using
              (MeasureTheory.lintegral_countable'
                (μ := κAbs c)
                (f := fun d : AxisState × AxisState ↦ ((κAbs ^ n) d) offDiag))
    _ ≥ ((κAbs ^ n) b) offDiag * (κAbs c) ({b} : Set (AxisState × AxisState)) := by
          exact ENNReal.le_tsum b
    _ =
        (discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix c
          ({b} : Set (AxisState × AxisState))) *
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) b) offDiag := by
          rw [mul_comm]
    _ =
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
            ((((2, 0) : AxisState), ((2, 1) : AxisState))))
          ({((((1, 0) : AxisState), ((1, 1) : AxisState)))} : Set (AxisState × AxisState))) *
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          {s : AxisState × AxisState | s.1 ≠ s.2} := by
            simp [κAbs, b, c, offDiag]

/-- Helper for Exercise 18.2.4: any launch-side nonvanishing theorem for the absorbed
off-diagonal tail propagates to the truthful two-right row through the explicit one-step return
mass `((2,0),(2,1)) -> ((1,0),(1,1))`. -/
private theorem axisBlockedFreePair_twoRightAbsorbedOffDiagonal_not_tendsto_zero_of_launchAbsorbedTail
    (hlaunch :
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0)) :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((2, 0) : AxisState), ((2, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let launchMass : ℕ → ℝ≥0∞ := fun n ↦
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) b)
      {s : AxisState × AxisState | s.1 ≠ s.2}
  let twoRightMass : ℕ → ℝ≥0∞ := fun n ↦
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) c)
      {s : AxisState × AxisState | s.1 ≠ s.2}
  let κstep : ℝ≥0∞ :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix c
      ({b} : Set (AxisState × AxisState))
  have hκstep_eq :
      κstep =
        discreteMatrixKernel independentProductPairMatrix c
          ({b} : Set (AxisState × AxisState)) := by
    -- Proof comment: the absorbed and free kernels agree on this off-diagonal one-step return.
    rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
    simp [κstep, independentProductPairAbsorbDiagonalMatrix, b, c]
  have hκstep_pos : 0 < κstep := by
    -- Proof comment: from the truthful two-right row `c`, both walkers can move one unit left
    -- and land at the launched row `b` with positive mass.
    rw [hκstep_eq]
    rw [discreteMatrixKernel_apply_singleton]
    norm_num [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, b, c]
  have hκstep_ne_zero : κstep ≠ 0 := ne_of_gt hκstep_pos
  have hκstep_ne_top : κstep ≠ ⊤ := by
    -- Proof comment: singleton masses under an absorbed kernel row are finite.
    simpa [κstep] using
      (measure_ne_top
        (discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix c)
        ({b} : Set (AxisState × AxisState)))
  intro htwoRight
  have htwoRight_succ :
      Filter.Tendsto (fun n : ℕ ↦ twoRightMass (n + 1)) Filter.atTop (nhds 0) := by
    -- Proof comment: shifting a convergent absorbed tail by one step preserves convergence at
    -- `Filter.atTop`.
    simpa [twoRightMass] using htwoRight.comp (tendsto_add_atTop_nat 1)
  have hscaled :
      Filter.Tendsto (fun n : ℕ ↦ κstep * launchMass n) Filter.atTop (nhds 0) := by
    -- Proof comment: the one-step two-right-to-launch lower bound squeezes the scaled launched
    -- tail between `0` and the shifted truthful two-right tail.
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds htwoRight_succ
        (Filter.Eventually.of_forall fun n ↦ bot_le)
        (Filter.Eventually.of_forall fun n ↦ ?_)
    simpa [twoRightMass, launchMass, κstep, b, c] using
      axisBlockedFreePair_twoRightAbsorbedOffDiagonalMass_ge_launchMass
        (Pq := Pq) (Xq := Xq) (n := n)
  have hcancel :
      Filter.Tendsto (fun n : ℕ ↦ κstep⁻¹ * (κstep * launchMass n)) Filter.atTop (nhds 0) := by
    -- Proof comment: multiplying by the inverse of the positive finite return mass recovers the
    -- unscaled launch tail.
    simpa using (tendsto_const_nhds.mul hscaled)
  have hlaunch_tendsto :
      Filter.Tendsto launchMass Filter.atTop (nhds 0) := by
    -- Proof comment: cancellation transports convergence of the scaled launch tail back to the
    -- original launch tail.
    convert hcancel using 1
    funext n
    rw [← mul_assoc, ENNReal.inv_mul_cancel hκstep_ne_zero hκstep_ne_top, one_mul]
  -- Proof comment: this contradicts the assumed launch-side nonvanishing theorem.
  exact hlaunch hlaunch_tendsto

/-- Helper for Exercise 18.2.4: for the truthful two-right row `((2,0),(2,1))`, positive
infinite-horizon never-meet mass is equivalent to nonvanishing of the absorbed off-diagonal tail.
-/
private theorem axisBlockedFreePair_twoRightNeverMeet_pos_iff_absorbedOffDiagonalNotTendstoZero :
    (0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent) ↔
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((2, 0) : AxisState), ((2, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0)) := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  constructor
  · intro hnever
    have hmeasure :
        0 <
          (Pq c : Measure Ωq) {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
      -- Proof comment: rewrite the two-right path-kernel row back to the underlying realization
      -- measure of the same infinite-horizon never-meet event.
      rw [← independentProductPairPathKernel_neverMeet_eq_measure
        (Pq := Pq) (Xq := Xq) c]
      simpa [c] using hnever
    have hbounded_not :
        ¬ Filter.Tendsto
          (fun n : ℕ ↦
            (Pq c : Measure Ωq) {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2})
          Filter.atTop (nhds 0) := by
      -- Proof comment: positive full never-meet mass gives a uniform lower bound on every
      -- bounded avoid-diagonal probability under the same two-right realization law.
      exact
        not_tendsto_zero_of_neverMeetProb_pos (μ := (Pq c : Measure Ωq)) (Xq := Xq)
          hmeasure
    have habsorbed_fun :
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) c)
            {s : AxisState × AxisState | s.1 ≠ s.2}) =
          (fun n : ℕ ↦
            (Pq c : Measure Ωq) {ω | ∀ m ≤ n, (Xq m ω).1 ≠ (Xq m ω).2}) := by
      funext n
      -- Proof comment: bounded two-right diagonal avoidance is exactly the absorbed off-diagonal
      -- mass from the same row.
      simpa [c] using
        independentProductPairAbsorbDiagonal_offDiagonalMass_eq_freeAvoidDiagonalProb
          (Pq := Pq) (Xq := Xq) c n
    -- Proof comment: transport the bounded nonvanishing statement through the absorbed-mass
    -- normalization to obtain the desired tail theorem.
    simpa [habsorbed_fun, c] using hbounded_not
  · intro htail
    -- Proof comment: the generic continuity-from-above theorem upgrades two-right absorbed-tail
    -- nonvanishing to positive infinite-horizon never-meet mass from the same row.
    simpa [c] using
      independentProductPairPathKernel_neverMeet_pos_of_absorbedOffDiagonalNotTendstoZero
        (Pq := Pq) (Xq := Xq) c htail

/-- Helper for Exercise 18.2.4: positive two-right future never-meet mass already forces the
launched jump-code no-hit event to have positive mass, by splicing the explicit immediate-right
launch history with the future row from `((2,0),(2,1))`. -/
private theorem axisBlockedFreePair_launchJumpCollisionCodeNoHit_pos_of_twoRightFutureNeverMeet
    (hfuture :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState)))
          freePairNeverMeetPathEvent) :
    0 <
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
        (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let historyEvent : Set Ωq := {ω | Xq 0 ω = b} ∩ {ω | Xq 1 ω = c}
  let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
  have hhistory_pos : 0 < μ historyEvent := by
    -- Proof comment: the explicit history where both walkers move right immediately from launch
    -- has strictly positive mass under the launched owner law.
    simpa [μ, historyEvent, b, c] using
      axisBlockedFreePair_launchImmediateRightHistory_pos (Pq := Pq) (Xq := Xq)
  have hhistory_future_mass :
      μ (historyEvent ∩ futureEvent) =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent) * μ historyEvent := by
    -- Proof comment: once that immediate-right history is fixed, the remaining event depends only
    -- on the future path-kernel row from the truthful two-right state `c`.
    simpa [μ, historyEvent, futureEvent, b, c] using
      axisBlockedFreePair_launchImmediateRightHistory_futureNeverMeet_mass
        (Pq := Pq) (Xq := Xq)
  have hsubset :
      historyEvent ∩ futureEvent ⊆
        axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq) := by
    -- Proof comment: on this history atom, future never-meet already implies the full launched
    -- jump-code no-hit event.
    simpa [historyEvent, futureEvent, b, c] using
      axisBlockedFreePair_launchImmediateRightHistory_futureNeverMeet_subset_jumpNoHit
        (Pq := Pq) (Xq := Xq)
  have hinter_pos : 0 < μ (historyEvent ∩ futureEvent) := by
    -- Proof comment: multiply the positive history atom by the positive future never-meet row.
    rw [hhistory_future_mass]
    exact ENNReal.mul_pos hfuture hhistory_pos
  exact lt_of_lt_of_le hinter_pos (measure_mono hsubset)

/-- Helper for Exercise 18.2.4: reducing the launch absorbed-tail theorem to a single honest
analytic frontier, namely strict positivity of the truthful two-right future never-meet row. -/
private theorem axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_latticeCollisionLineAvoidPos
    (hline :
      0 <
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((2, 0) : AxisState), ((2, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent) :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  -- Proof comment: for the truthful two-right row, the free-pair never-meet event is exactly the
  -- encoded collision-line-avoidance event on the pushed-forward `ℤ^3` path law.
  rw [axisBlockedFreePair_pathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (Pq := Pq) (Xq := Xq) c]
  simpa [c] using hline

/-- Helper for Exercise 18.2.4: any launch-side absorbed off-diagonal nonvanishing theorem
propagates through the explicit one-step return `((2,0),(2,1)) → ((1,0),(1,1))` and then
upgrades to positive truthful two-right future never-meet mass. -/
private theorem axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_launchAbsorbedOffDiagonalNotTendstoZero
    (hlaunch :
      ¬ Filter.Tendsto
          (fun n : ℕ ↦
            ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
              ((((1, 0) : AxisState), ((1, 1) : AxisState))))
              {s : AxisState × AxisState | s.1 ≠ s.2})
          Filter.atTop (nhds 0)) :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  have htwoRightTail :
      ¬ Filter.Tendsto
          (fun n : ℕ ↦
            ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
              ((((2, 0) : AxisState), ((2, 1) : AxisState))))
              {s : AxisState × AxisState | s.1 ≠ s.2})
          Filter.atTop (nhds 0) :=
    axisBlockedFreePair_twoRightAbsorbedOffDiagonal_not_tendsto_zero_of_launchAbsorbedTail
      (Pq := Pq) (Xq := Xq) hlaunch
  -- Proof comment: once the explicit one-step return shows the truthful two-right absorbed tail
  -- does not vanish, the earlier continuity-from-above equivalence upgrades it to positive
  -- infinite-horizon never-meet mass from the same row.
  exact
    (axisBlockedFreePair_twoRightNeverMeet_pos_iff_absorbedOffDiagonalNotTendstoZero
      (Pq := Pq) (Xq := Xq)).2 htwoRightTail

/-- Helper for Exercise 18.2.4: direct positivity of launched collision-line avoidance is enough
to close the truthful two-right future theorem, because the remaining transport to launch
absorbed-tail nonvanishing and then back to the truthful two-right row is already established. -/
private theorem axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_launchCollisionLineAvoidPos
    (hlaunchLine :
      0 <
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent) :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  have hlaunchTail :
      ¬ Filter.Tendsto
          (fun n : ℕ ↦
            ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
              ((((1, 0) : AxisState), ((1, 1) : AxisState))))
              {s : AxisState × AxisState | s.1 ≠ s.2})
          Filter.atTop (nhds 0) :=
    axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_of_collisionLineAvoidPos
      (Pq := Pq) (Xq := Xq) hlaunchLine
  -- Proof comment: the only remaining work after launch-side collision-line positivity is the
  -- already-proved transport from launch absorbed-tail nonvanishing to the truthful two-right
  -- future never-meet row.
  exact
    axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_launchAbsorbedOffDiagonalNotTendstoZero
      (Pq := Pq) (Xq := Xq) hlaunchTail

/-- Helper for Exercise 18.2.4: once the launched never-meet row is positive, the launched
jump-code no-hit event is positive by the exact path-law/owner-law rewrites already proved. -/
private theorem axisBlockedFreePair_launchJumpCollisionCodeNoHit_pos_of_launchNeverMeetPos
    (hlaunch :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent) :
    0 <
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
        (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) := by
  -- Proof comment: first rewrite the owner-law event mass to the launched collision-line
  -- avoidance mass, then rewrite that mass back to the launched never-meet row.
  rw [← axisBlockedFreePair_launchJumpCollisionCodeNoHit_mass_eq (Pq := Pq) (Xq := Xq)]
  rw [← axisBlockedFreePair_launchPathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (Pq := Pq) (Xq := Xq)]
  exact hlaunch

/-- Helper for Exercise 18.2.4: once the start-pair absorbed off-diagonal tail is known not to
vanish, the existing start-to-launch and launch-to-two-right transports already force positive
future never-meet mass from the truthful two-right row. -/
private theorem
    axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_startAbsorbedOffDiagonalNotTendstoZero
    (hstart :
      ¬ Filter.Tendsto
          (fun n : ℕ ↦
            ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
              ((((0, 0) : AxisState), ((0, 1) : AxisState))))
              {s : AxisState × AxisState | s.1 ≠ s.2})
          Filter.atTop (nhds 0)) :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  have hstartCode :
      0 <
        Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
          axisBlockedDefectNoHitPathEvent := by
    -- Proof comment: the earlier start-side equivalence already identifies collision-code no-hit
    -- positivity with nonvanishing of the absorbed off-diagonal tail from the same start row.
    exact
      (axisBlockedFreePair_startCollisionCodeNoHit_pos_iff_startAbsorbedOffDiagonalNotTendstoZero
        (Pq := Pq) (Xq := Xq)).2 hstart
  have hlaunch :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
    -- Proof comment: transport the start-side collision-code positivity to the launched
    -- never-meet row through the established start-to-launch equivalence.
    exact
      (axisBlockedFreePair_launchNeverMeet_pos_iff_startCollisionCodeNoHit_pos
        (Pq := Pq) (Xq := Xq)).2 hstartCode
  -- Proof comment: the explicit one-step return from the truthful two-right row to the launched
  -- row upgrades launched positivity to the desired two-right future never-meet positivity.
  exact
    axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_launchNeverMeetPos
      (Pq := Pq) (Xq := Xq) hlaunch

/-- Helper for Exercise 18.2.4: positive mass of the launched jump-code no-hit event already
forces positive truthful two-right future never-meet mass, because the existing launch-to-start
transport upgrades it to the start absorbed-tail frontier consumed above. -/
private theorem axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_launchJumpCollisionCodeNoHitPos
    (hlaunchJump :
      0 <
        (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
          (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq))) :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  have hstartCode :
      0 <
        Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
          axisBlockedDefectNoHitPathEvent :=
    axisBlockedFreePair_startCollisionCodeNoHit_pos_of_launchJumpCollisionCodeNoHitPos
      (Pq := Pq) (Xq := Xq) hlaunchJump
  have hstartTail :
      ¬ Filter.Tendsto
          (fun n : ℕ ↦
            ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
              ((((0, 0) : AxisState), ((0, 1) : AxisState))))
              {s : AxisState × AxisState | s.1 ≠ s.2})
          Filter.atTop (nhds 0) :=
    (axisBlockedFreePair_startCollisionCodeNoHit_pos_iff_startAbsorbedOffDiagonalNotTendstoZero
      (Pq := Pq) (Xq := Xq)).1 hstartCode
  -- Proof comment: after transporting the launched jump witness back to the start row, the
  -- remaining work is exactly the already-packaged start-tail-to-two-right route.
  exact
    axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_startAbsorbedOffDiagonalNotTendstoZero
      (Pq := Pq) (Xq := Xq) hstartTail

/-- Helper for Exercise 18.2.4: the honest remaining same-start frontier is a shifted/scaled
comparison from canonical SRW3 bounded origin avoidance at `![2,2,-1]` to the truthful
two-right absorbed off-diagonal masses. -/
private theorem
    canonicalSymmetricSimpleRandomWalk3_twoRightBoundedAvoid_le_shiftedTwoRightAbsorbedOffDiagonal
    (P : LatticePoint 3 → ProbabilityMeasure (ℕ → LatticePoint 3))
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P Function.eval]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))] :
    ∃ c0 : ℝ≥0∞, ∃ k : ℕ,
      0 < c0 ∧ c0 ≠ ⊤ ∧
        ∀ n : ℕ,
          c0 *
              (P (![2, 2, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
                (latticeAvoidOriginUpToPathEvent n) ≤
            ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ (n + k))
              ((((2, 0) : AxisState), ((2, 1) : AxisState))))
              {s : AxisState × AxisState | s.1 ≠ s.2} := by
  -- Route correction: the old blocker was phrased on the pushed-forward collision-line event.
  -- The remaining honest frontier is the same-start absorbed comparison on the common normal form
  -- already used elsewhere in the file.
  -- TODO: compare canonical SRW3 absorbed nonorigin mass at `![2,2,-1]` directly to the truthful
  -- two-right absorbed off-diagonal mass after one fixed shift, using the existing explicit
  -- one-step/two-step obstruction lemmas to handle the low horizons separately.
  sorry

/-- Helper for Exercise 18.2.4: once the same-start absorbed comparison is available, the bounded
collision-line-avoidance theorem is only a rewrite through the truthful two-right absorbed-mass
normalization. -/
private theorem canonicalSymmetricSimpleRandomWalk3_twoRightBoundedAvoid_le_shiftedTwoRightCollisionLineAvoidUpTo
    (P : LatticePoint 3 → ProbabilityMeasure (ℕ → LatticePoint 3))
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P Function.eval]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))] :
    ∃ c0 : ℝ≥0∞, ∃ k : ℕ,
      0 < c0 ∧ c0 ≠ ⊤ ∧
        ∀ n : ℕ,
          c0 *
              (P (![2, 2, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
                (latticeAvoidOriginUpToPathEvent n) ≤
            Measure.map axisBlockedFreePairLatticePath
              (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
                ((((2, 0) : AxisState), ((2, 1) : AxisState))))
              (axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + k)) := by
  obtain ⟨c0, k, hc0_pos, hc0_ne_top, hbound⟩ :=
    canonicalSymmetricSimpleRandomWalk3_twoRightBoundedAvoid_le_shiftedTwoRightAbsorbedOffDiagonal
      (Pq := Pq) (Xq := Xq) (P := P)
  refine ⟨c0, k, hc0_pos, hc0_ne_top, ?_⟩
  intro n
  -- Proof comment: the truthful two-right bounded collision-line-avoidance mass is exactly the
  -- absorbed off-diagonal mass of the diagonal-absorbed pair chain from the same row.
  rw [axisBlockedFreePair_twoRightLatticeCollisionLineAvoidUpTo_eq_absorbedOffDiagonalMass
    (Pq := Pq) (Xq := Xq) (n + k)]
  exact hbound n

/-- Helper for Exercise 18.2.4: once the same-start two-right bounded comparison is available,
the launch-side bounded collision-line-avoidance comparison is only a transport through the
explicit SRW3 two-step prefix and the launched immediate-right history. -/
private theorem canonicalSymmetricSimpleRandomWalk3_launchBoundedAvoid_le_shiftedLaunchCollisionLineAvoidUpTo
    (P : LatticePoint 3 → ProbabilityMeasure (ℕ → LatticePoint 3))
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P Function.eval]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))] :
    ∃ c0 : ℝ≥0∞, ∃ k : ℕ,
      0 < c0 ∧ c0 ≠ ⊤ ∧
        ∀ n : ℕ,
          c0 *
              (P (![1, 1, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
                (latticeAvoidOriginUpToPathEvent n) ≤
            Measure.map axisBlockedFreePairLatticePath
              (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
                ((((1, 0) : AxisState), ((1, 1) : AxisState))))
              (axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + k)) := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let historyEvent : Set Ωq := {ω | Xq 0 ω = b} ∩ {ω | Xq 1 ω = c}
  obtain ⟨cLaunch, hcLaunch_pos, hcLaunch_ne_top, hLaunch⟩ :=
    canonicalSymmetricSimpleRandomWalk3_launchBoundedAvoid_le_shiftedTwoRightAvoid
      (P := P)
  obtain ⟨cTwoRight, kTwoRight, hcTwoRight_pos, hcTwoRight_ne_top, hTwoRight⟩ :=
    canonicalSymmetricSimpleRandomWalk3_twoRightBoundedAvoid_le_shiftedTwoRightCollisionLineAvoidUpTo
      (Pq := Pq) (Xq := Xq) (P := P)
  let historyMass : ℝ≥0∞ := (Pq b : Measure Ωq) historyEvent
  have hhistory_pos : 0 < historyMass := by
    -- Proof comment: the explicit immediate-right history has positive mass already under the
    -- launched owner law, and that law is exactly the launched pair law.
    rw [show historyMass =
        (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
          ({ω | Xq 0 ω = (((1, 0) : AxisState), ((1, 1) : AxisState))} ∩
            {ω | Xq 1 ω = (((2, 0) : AxisState), ((2, 1) : AxisState))}) by
      rw [axisBlockedFreePairDefectVisitOwnerLaw_launch (Pq := Pq)]
      simp [historyMass, historyEvent, b, c]]
    simpa using axisBlockedFreePair_launchImmediateRightHistory_pos (Pq := Pq) (Xq := Xq)
  have hhistory_ne_top : historyMass ≠ ⊤ := by
    simpa [historyMass] using measure_ne_top (Pq b : Measure Ωq) historyEvent
  refine ⟨historyMass * (cTwoRight * cLaunch), kTwoRight + 3, ?_, ?_, ?_⟩
  · -- Proof comment: the final scale is the product of the positive SRW prefix mass, the
    -- positive same-start comparison scale, and the positive launched history mass.
    exact ENNReal.mul_pos hhistory_pos (ENNReal.mul_pos hcTwoRight_pos hcLaunch_pos)
  · -- Proof comment: every factor is finite, so the composed scale is finite as well.
    exact ENNReal.mul_ne_top hhistory_ne_top (ENNReal.mul_ne_top hcTwoRight_ne_top hcLaunch_ne_top)
  · intro n
    have hLaunch_n :
        cLaunch *
            (P (![1, 1, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
              (latticeAvoidOriginUpToPathEvent n) ≤
          (P (![2, 2, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
            (latticeAvoidOriginUpToPathEvent (n + 2)) :=
      hLaunch n
    have hTwoRight_n :
        cTwoRight *
            (P (![2, 2, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
              (latticeAvoidOriginUpToPathEvent (n + 2)) ≤
          Measure.map axisBlockedFreePairLatticePath
            (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c)
            (axisBlockedDefectAvoidCollisionLineUpToPathEvent ((n + 2) + kTwoRight)) :=
      hTwoRight (n + 2)
    have hHistory_n :
        historyMass *
            Measure.map axisBlockedFreePairLatticePath
              (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c)
              (axisBlockedDefectAvoidCollisionLineUpToPathEvent ((n + 2) + kTwoRight)) ≤
          Measure.map axisBlockedFreePairLatticePath
            (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
            (axisBlockedDefectAvoidCollisionLineUpToPathEvent (((n + 2) + kTwoRight) + 1)) := by
      simpa [historyMass, historyEvent, b, c] using
        axisBlockedFreePair_launchBoundedCollisionAvoidUpTo_lowerBoundFromImmediateRightHistory
          (Pq := Pq) (Xq := Xq) (((n + 2) + kTwoRight))
    -- Proof comment: first transport launch SRW bounded avoidance to the truthful two-right
    -- SRW row, then apply the same-start two-right comparison, and finally use the launched
    -- immediate-right history lower bound to return to the launch row.
    calc
      (historyMass * (cTwoRight * cLaunch)) *
          (P (![1, 1, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
            (latticeAvoidOriginUpToPathEvent n) =
        historyMass *
          (cTwoRight *
            (cLaunch *
              (P (![1, 1, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
                (latticeAvoidOriginUpToPathEvent n))) := by
          rw [mul_assoc, mul_assoc]
      _ ≤
        historyMass *
          (cTwoRight *
            (P (![2, 2, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
              (latticeAvoidOriginUpToPathEvent (n + 2))) := by
          exact mul_le_mul_left' (mul_le_mul_left' hLaunch_n cTwoRight) historyMass
      _ ≤
        historyMass *
          Measure.map axisBlockedFreePairLatticePath
            (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c)
            (axisBlockedDefectAvoidCollisionLineUpToPathEvent ((n + 2) + kTwoRight)) := by
          exact mul_le_mul_left' hTwoRight_n historyMass
      _ ≤
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) b)
          (axisBlockedDefectAvoidCollisionLineUpToPathEvent (((n + 2) + kTwoRight) + 1)) := by
            exact hHistory_n
      _ =
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          (axisBlockedDefectAvoidCollisionLineUpToPathEvent (n + (kTwoRight + 3))) := by
            simp [b, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Exercise 18.2.4: the remaining structural blocker is a shifted/scaled lower bound
from canonical SRW3 origin avoidance at `![1,1,-1]` to the launched absorbed off-diagonal
masses. -/
private theorem
    canonicalSymmetricSimpleRandomWalk3_launchBoundedAvoid_le_shiftedLaunchAbsorbedOffDiagonal
    (P : LatticePoint 3 → ProbabilityMeasure (ℕ → LatticePoint 3))
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P Function.eval]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))] :
    ∃ c0 : ℝ≥0∞, ∃ k : ℕ,
      0 < c0 ∧ c0 ≠ ⊤ ∧
        ∀ n : ℕ,
          c0 *
              (P (![1, 1, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
                (latticeAvoidOriginUpToPathEvent n) ≤
            ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ (n + k))
              ((((1, 0) : AxisState), ((1, 1) : AxisState))))
              {s : AxisState × AxisState | s.1 ≠ s.2} := by
  obtain ⟨c0, k, hc0_pos, hc0_ne_top, hbound⟩ :=
    canonicalSymmetricSimpleRandomWalk3_launchBoundedAvoid_le_shiftedLaunchCollisionLineAvoidUpTo
      (Pq := Pq) (Xq := Xq) (P := P)
  refine ⟨c0, k, hc0_pos, hc0_ne_top, ?_⟩
  intro n
  -- Proof comment: the launch-side bounded collision-line-avoidance mass is exactly the
  -- absorbed off-diagonal mass of the diagonal-absorbed free-pair chain.
  rw [axisBlockedFreePair_launchLatticeCollisionLineAvoidUpTo_eq_absorbedOffDiagonalMass
    (Pq := Pq) (Xq := Xq) (n + k)]
  exact hbound n

/-- Helper for Exercise 18.2.4: once the shifted canonical SRW3 lower bound is available, the
launched absorbed off-diagonal tail cannot tend to `0`. -/
private theorem axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_core :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  obtain ⟨P, hP⟩ := existsCanonicalSymmetricSimpleRandomWalk3Realization
  let u : ℕ → ℝ≥0∞ := fun n ↦
    (P (![1, 1, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
      (latticeAvoidOriginUpToPathEvent n)
  let v : ℕ → ℝ≥0∞ := fun n ↦
    ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
      ((((1, 0) : AxisState), ((1, 1) : AxisState))))
      {s : AxisState × AxisState | s.1 ≠ s.2}
  have hu :
      ¬ Filter.Tendsto u Filter.atTop (nhds 0) := by
    have havoid :
        0 <
          (P (![1, 1, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3))
            {path : ℕ → LatticePoint 3 | ∀ n : ℕ, path n ≠ 0} := by
      simpa using
        symmetricSimpleRandomWalk3_avoidOrigin_pos (P := P) (X := Function.eval)
          (by norm_num)
    -- Proof comment: positive infinite-horizon origin avoidance for canonical SRW3 forces the
    -- bounded avoid-origin probabilities to stay away from `0`.
    simpa [u] using
      not_tendsto_zero_of_boundedAvoidProb_pos
        (μ := (P (![1, 1, -1] : LatticePoint 3) : Measure (ℕ → LatticePoint 3)))
        (X := Function.eval) havoid
  obtain ⟨c0, k, hc0_pos, hc0_ne_top, hbound⟩ :=
    canonicalSymmetricSimpleRandomWalk3_launchBoundedAvoid_le_shiftedLaunchAbsorbedOffDiagonal
      (P := P)
  -- Proof comment: the shifted/scaled lower bound transports nonvanishing of canonical SRW3
  -- bounded avoid-origin probabilities to the launched absorbed tail.
  simpa [u, v] using
    notTendstoZero_of_shiftedScaledLowerBound u v hc0_pos hc0_ne_top hu hbound

/-- Helper for Exercise 18.2.4: the truthful two-right future never-meet row follows from the
launch absorbed-tail frontier through the existing one-step transport theorem. -/
private theorem axisBlockedFreePair_twoRightFutureNeverMeet_pos_core :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  -- Proof comment: the launched absorbed-tail nonvanishing statement is exactly the input needed
  -- by the already-proved launch-to-two-right transport.
  exact
    axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_launchAbsorbedOffDiagonalNotTendstoZero
      (Pq := Pq) (Xq := Xq)
      (axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_core
        (Pq := Pq) (Xq := Xq))

/-- Helper for Exercise 18.2.4: the honest remaining owner theorem is direct positivity of the
truthful two-right collision-line-avoidance event. -/
private theorem axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_root :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Route correction: the old SRW3 full-path domination helper was the wrong theorem. The live
  -- owner theorem is the exact two-right encoded collision-line positivity statement used
  -- downstream.
  have hfuture :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState)))
          freePairNeverMeetPathEvent :=
    axisBlockedFreePair_twoRightFutureNeverMeet_pos_core (Pq := Pq) (Xq := Xq)
  -- Proof comment: for the truthful two-right row, the never-meet event is exactly the encoded
  -- collision-line-avoidance event on the pushed-forward `ℤ^3` path law.
  rw [← axisBlockedFreePair_pathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (Pq := Pq) (Xq := Xq) ((((2, 0) : AxisState), ((2, 1) : AxisState)))]
  exact hfuture

/-- Helper for Exercise 18.2.4: the live analytic root is strict positivity of the truthful
two-right future never-meet row. -/
private theorem axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_of_ownerAvoidLowerBound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : LatticePoint 3 → ProbabilityMeasure Ω)
    (ownerProcess : ℕ → Ω → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P ownerProcess]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))]
    (hlower :
      (P ![2, 2, -1] : Measure Ω) {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} ≤
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((2, 0) : AxisState), ((2, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  have howner :
      0 < (P ![2, 2, -1] : Measure Ω) {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} := by
    -- Proof comment: canonical SRW3 started from the nonzero owner point `![2,2,-1]` avoids the
    -- origin with strictly positive probability.
    exact
      symmetricSimpleRandomWalk3_avoidOrigin_pos (P := P) (X := ownerProcess)
        (by norm_num)
  -- Proof comment: any valid lower bound from SRW3 origin avoidance to the truthful two-right
  -- collision-line-avoidance row immediately transfers strict positivity.
  exact lt_of_lt_of_le howner hlower

/-- Helper for Exercise 18.2.4: a bounded-horizon comparison between SRW3 origin avoidance at
`![2,2,-1]` and the truthful two-right collision-line-avoidance event upgrades, by continuity
from above, to strict positivity of the exact two-right collision-line-avoidance mass. -/
private theorem axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_of_boundedOwnerAvoidComparison
    {Ω : Type*} [MeasurableSpace Ω]
    (P : LatticePoint 3 → ProbabilityMeasure Ω)
    (ownerProcess : ℕ → Ω → LatticePoint 3)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
      P ownerProcess]
    [Kernel.IsIrreducible
      (Measure.count : Measure (LatticePoint 3))
      (discreteMatrixKernel
        (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)))]
    (hbounded :
      ∀ n : ℕ,
        (P ![2, 2, -1] : Measure Ω) {ω | ∀ m ≤ n, ownerProcess m ω ≠ 0} ≤
          Measure.map axisBlockedFreePairLatticePath
            (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
              ((((2, 0) : AxisState), ((2, 1) : AxisState))))
            (axisBlockedDefectAvoidCollisionLineUpToPathEvent n)) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  let μ : Measure Ω := (P ![2, 2, -1] : Measure Ω)
  let ownerPath : Ω → (ℕ → LatticePoint 3) := fun ω n ↦ ownerProcess n ω
  let ν : Measure (ℕ → LatticePoint 3) := Measure.map ownerPath μ
  let twoRightPathLaw : Measure (ℕ → LatticePoint 3) :=
    Measure.map axisBlockedFreePairLatticePath
      (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState))))
  let hreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (latticeConvolutionStepMatrix (symmetricSimpleRandomWalkStepPMF 3)) ^ n)
        P ownerProcess :=
    inferInstance
  have hownerPath_meas : Measurable ownerPath := by
    -- Proof comment: the SRW3 owner trajectory map is coordinatewise measurable because every
    -- time slice of the realization is measurable.
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa [ownerPath] using hreal.measurable_process n
  have hbounded_path :
      ∀ n : ℕ,
        ν (latticeAvoidOriginUpToPathEvent n) ≤
          twoRightPathLaw (axisBlockedDefectAvoidCollisionLineUpToPathEvent n) := by
    intro n
    rw [Measure.map_apply hownerPath_meas
      (measurableSet_latticeAvoidOriginUpToPathEvent n)]
    -- Proof comment: rewrite the bounded path-space avoid-origin event back to the corresponding
    -- bounded owner event on the SRW3 sample space.
    simpa [ν, μ, ownerPath, latticeAvoidOriginUpToPathEvent] using hbounded n
  have hfull_path :
      ν ({path : ℕ → LatticePoint 3 | ∀ n : ℕ, path n ≠ 0}) ≤
        twoRightPathLaw axisBlockedDefectAvoidCollisionLinePathEvent := by
    -- Proof comment: compare the bounded-horizon masses termwise, then pass to the
    -- infinite-horizon events by continuity from above.
    exact boundedAvoidComparison_implies_fullAvoidComparison ν twoRightPathLaw hbounded_path
  have hfull_meas :
      MeasurableSet ({path : ℕ → LatticePoint 3 | ∀ n : ℕ, path n ≠ 0} :
        Set (ℕ → LatticePoint 3)) := by
    rw [latticeAvoidOriginPathEvent_eq_iInter_bounded]
    exact MeasurableSet.iInter measurableSet_latticeAvoidOriginUpToPathEvent
  have howner_full :
      μ {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} ≤
        twoRightPathLaw axisBlockedDefectAvoidCollisionLinePathEvent := by
    rw [Measure.map_apply hownerPath_meas hfull_meas] at hfull_path
    -- Proof comment: the full path-space avoid-origin event is exactly the preimage of the
    -- pointwise owner-origin-avoidance event under the SRW3 trajectory map.
    simpa [ν, μ, ownerPath] using hfull_path
  have howner_pos :
      0 < μ {ω | ∀ n : ℕ, ownerProcess n ω ≠ 0} := by
    -- Proof comment: SRW3 started from the nonzero owner point `![2,2,-1]` avoids the origin
    -- with strictly positive probability.
    simpa [μ] using
      symmetricSimpleRandomWalk3_avoidOrigin_pos (P := P) (X := ownerProcess)
        (by norm_num)
  -- Proof comment: positivity of the SRW3 origin-avoidance event transfers through the
  -- infinite-horizon comparison just established.
  exact lt_of_lt_of_le howner_pos howner_full

/-- Helper for Exercise 18.2.4: positive launched never-meet mass pushes one truthful step to the
two-right row, and then rewrites back to the lattice collision-line avoidance event. -/
private theorem axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_of_launchRoot
    (hlaunch :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  have hstep_pos :
      0 <
        (discreteMatrixKernel independentProductPairMatrix c)
          ({b} : Set (AxisState × AxisState)) := by
    -- Proof comment: the explicit one-step move sending both walkers left from the two-right row
    -- to the launched row has positive mass.
    rw [discreteMatrixKernel_apply_singleton]
    norm_num [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, b, c]
  have htwoRightNever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent := by
    -- Proof comment: multiply the positive launched never-meet mass by the positive one-step
    -- return mass `c → b`, then use the existing lower bound from launch to two-right.
    exact lt_of_lt_of_le
      (ENNReal.mul_pos hstep_pos hlaunch)
      (axisBlockedFreePair_twoRightNeverMeet_lowerBoundFromLaunch
        (Pq := Pq) (Xq := Xq))
  -- Proof comment: rewrite the truthful two-right never-meet row as the encoded collision-line
  -- avoidance event for the same starting row.
  rw [← axisBlockedFreePair_pathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (Pq := Pq) (Xq := Xq) c]
  exact htwoRightNever

/-- Helper for Exercise 18.2.4: once the start-pair collision-code no-hit mass is positive, the
existing start-to-launch equivalence and the explicit one-step return to the truthful two-right
row already force positive collision-line avoidance from `((2,0),(2,1))`. -/
private theorem axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_of_startCollisionCodeNoHit
    (hstart :
      0 <
        Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
          axisBlockedDefectNoHitPathEvent) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  have hlaunch :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
    -- Proof comment: the established start↔launch equivalence rewrites positive start-side
    -- collision-code no-hit mass as positive launched never-meet mass.
    exact
      (axisBlockedFreePair_launchNeverMeet_pos_iff_startCollisionCodeNoHit_pos
        (Pq := Pq) (Xq := Xq)).2 hstart
  -- Proof comment: from the launched row, the earlier explicit one-step return lemma already
  -- transports positivity to the truthful two-right collision-line-avoidance event.
  exact
    axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_of_launchRoot
      (Pq := Pq) (Xq := Xq) hlaunch

/-- Helper for Exercise 18.2.4: forcing the two-step history
`((0,0),(0,1)) → ((1,0),(1,1)) → ((2,0),(2,1))` gives a direct lower bound on the start-pair
never-meet row. -/
private theorem axisBlockedFreePair_startNeverMeet_lowerBoundFromTwoRight :
    ((discreteMatrixKernel independentProductPairMatrix
        ((((0, 0) : AxisState), ((0, 1) : AxisState))))
      ({((((1, 0) : AxisState), ((1, 1) : AxisState)))} : Set (AxisState × AxisState)) *
      (discreteMatrixKernel independentProductPairMatrix
        ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        ({((((2, 0) : AxisState), ((2, 1) : AxisState)))} : Set (AxisState × AxisState))) *
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent ≤
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((0, 0) : AxisState), ((0, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let μ : Measure Ωq := (Pq a : Measure Ωq)
  let initEvent : Set Ωq := {ω | Xq 0 ω = a}
  let launchEvent : Set Ωq := {ω | Xq 1 ω = b}
  let twoRightEvent : Set Ωq := {ω | Xq 2 ω = c}
  let prefixEvent : Set Ωq := initEvent ∩ launchEvent
  let historyEvent : Set Ωq := prefixEvent ∩ twoRightEvent
  let futureEvent : Set Ωq := {ω | futurePath Xq 2 ω ∈ freePairNeverMeetPathEvent}
  let neverMeet : Set Ωq := {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2}
  let hqreal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq :=
    inferInstance
  have hinit_meas : MeasurableSet initEvent := by
    rw [show initEvent = Xq 0 ⁻¹' ({a} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    exact (hqreal.measurable_process 0) (measurableSet_singleton a)
  have hinit_hist0 : MeasurableSet[generatedFiltrationSpace Xq 0] initEvent := by
    have hX0 : Measurable[generatedFiltrationSpace Xq 0] (Xq 0) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 0
    rw [show initEvent = Xq 0 ⁻¹' ({a} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    exact hX0 (measurableSet_singleton a)
  have hlaunch_meas : MeasurableSet launchEvent := by
    rw [show launchEvent = Xq 1 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [launchEvent]]
    exact (hqreal.measurable_process 1) (measurableSet_singleton b)
  have hlaunch_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] launchEvent := by
    have hX1 : Measurable[generatedFiltrationSpace Xq 1] (Xq 1) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 1
    rw [show launchEvent = Xq 1 ⁻¹' ({b} : Set (AxisState × AxisState)) by
      ext ω
      simp [launchEvent]]
    exact hX1 (measurableSet_singleton b)
  have htwoRight_meas : MeasurableSet twoRightEvent := by
    rw [show twoRightEvent = Xq 2 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [twoRightEvent]]
    exact (hqreal.measurable_process 2) (measurableSet_singleton c)
  have htwoRight_hist2 : MeasurableSet[generatedFiltrationSpace Xq 2] twoRightEvent := by
    have hX2 : Measurable[generatedFiltrationSpace Xq 2] (Xq 2) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) 2
    rw [show twoRightEvent = Xq 2 ⁻¹' ({c} : Set (AxisState × AxisState)) by
      ext ω
      simp [twoRightEvent]]
    exact hX2 (measurableSet_singleton c)
  have hinit_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] initEvent := by
    exact (generatedFiltrationSpace_monoNat (X := Xq) (m := 0) (n := 1) (Nat.zero_le 1)) _
      hinit_hist0
  have hinit_hist2 : MeasurableSet[generatedFiltrationSpace Xq 2] initEvent := by
    exact (generatedFiltrationSpace_monoNat (X := Xq) (m := 0) (n := 2) (Nat.zero_le 2)) _
      hinit_hist0
  have hlaunch_hist2 : MeasurableSet[generatedFiltrationSpace Xq 2] launchEvent := by
    exact (generatedFiltrationSpace_monoNat (X := Xq) (m := 1) (n := 2) (Nat.succ_le_succ (Nat.zero_le 1))) _
      hlaunch_hist1
  have hprefix_meas : MeasurableSet prefixEvent := hinit_meas.inter hlaunch_meas
  have hprefix_hist1 : MeasurableSet[generatedFiltrationSpace Xq 1] prefixEvent := by
    simpa [prefixEvent] using hinit_hist1.inter hlaunch_hist1
  have hprefix_hist2 : MeasurableSet[generatedFiltrationSpace Xq 2] prefixEvent := by
    simpa [prefixEvent] using hinit_hist2.inter hlaunch_hist2
  have hprefix_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ prefixEvent → Xq 1 ω = b := by
    intro ω hω
    exact hω.2
  have hinit_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ initEvent → Xq 0 ω = a := by
    intro ω hω
    exact hω
  have hinit_mass : μ initEvent = 1 := by
    rw [show initEvent = Xq 0 ⁻¹' ({a} : Set (AxisState × AxisState)) by
      ext ω
      simp [initEvent]]
    rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton a)]
    rw [hqreal.initial_eq a]
    simp [μ]
  have hprefix_mass :
      μ prefixEvent =
        (discreteMatrixKernel independentProductPairMatrix a ({b} : Set (AxisState × AxisState))) *
          μ initEvent := by
    -- Proof comment: first fix the deterministic start state `a`, then the time-`1` launch to
    -- `b` factors through the one-step product-pair row.
    simpa [μ, prefixEvent] using
      measureInter_eq_mul_stepMass_of_stateEvent
        (x := a) (y := a) (w := b) (n := 0) (A := initEvent)
        hinit_meas hinit_hist0 hinit_state
  have hhistory_meas : MeasurableSet historyEvent := hprefix_meas.inter htwoRight_meas
  have hhistory_hist2 : MeasurableSet[generatedFiltrationSpace Xq 2] historyEvent := by
    simpa [historyEvent] using hprefix_hist2.inter htwoRight_hist2
  have hhistory_state :
      ∀ ⦃ω : Ωq⦄, ω ∈ historyEvent → Xq 2 ω = c := by
    intro ω hω
    exact hω.2
  have hhistory_mass :
      μ historyEvent =
        (discreteMatrixKernel independentProductPairMatrix b ({c} : Set (AxisState × AxisState))) *
          μ prefixEvent := by
    -- Proof comment: once the time-`1` launched state `b` is fixed, the time-`2` step to the
    -- truthful two-right state `c` is the next one-step product-pair factor.
    simpa [μ, historyEvent] using
      measureInter_eq_mul_stepMass_of_stateEvent
        (x := a) (y := b) (w := c) (n := 1) (A := prefixEvent)
        hprefix_meas hprefix_hist1 hprefix_state
  have hfuture_mass :
      μ (historyEvent ∩ futureEvent) =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent) * μ historyEvent := by
    -- Proof comment: after the two-step history reaches `c`, the remaining event is exactly the
    -- truthful future never-meet row from `c`.
    simpa [μ, futureEvent] using
      independentProductPair_measureInter_eq_mul_futurePathMass_of_stateEvent
        (Pq := Pq) (Xq := Xq) (a := a) (y := c) (n := 2)
        (A := historyEvent) (B := freePairNeverMeetPathEvent)
        measurableSet_freePairNeverMeetPathEvent hhistory_meas hhistory_hist2 hhistory_state
  have hstart_offdiag : a.1 ≠ a.2 := by
    norm_num [a]
  have hlaunch_offdiag : b.1 ≠ b.2 := by
    norm_num [b]
  have hsubset : historyEvent ∩ futureEvent ⊆ neverMeet := by
    intro ω hω
    intro n
    cases n with
    | zero =>
        have h0 : Xq 0 ω = a := hω.1.1.1
        simpa [neverMeet, a] using hstart_offdiag
    | succ n =>
        cases n with
        | zero =>
            have h1 : Xq 1 ω = b := hω.1.1.2
            simpa [neverMeet, b] using hlaunch_offdiag
        | succ n =>
            have hpath : futurePath Xq 2 ω ∈ freePairNeverMeetPathEvent := hω.2
            simpa [futureEvent, freePairNeverMeetPathEvent, futurePath, neverMeet,
              Nat.add_assoc] using hpath n
  -- Proof comment: the explicit two-step history event sits inside the full start-row never-meet
  -- event, so its factored mass is a valid lower bound for the start row.
  calc
    ((discreteMatrixKernel independentProductPairMatrix a ({b} : Set (AxisState × AxisState))) *
        (discreteMatrixKernel independentProductPairMatrix b ({c} : Set (AxisState × AxisState)))) *
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent =
      μ (historyEvent ∩ futureEvent) := by
        rw [hfuture_mass, hhistory_mass, hprefix_mass, hinit_mass]
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ μ neverMeet := measure_mono hsubset
    _ =
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
          freePairNeverMeetPathEvent := by
            symm
            simpa [a, μ, neverMeet] using
              axisBlockedFreePair_startPathKernel_neverMeet_eq_measure
                (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: a truthful positive future-never-meet row from `((2,0),(2,1))`
already forces the exact start-side collision-code no-hit mass. -/
private theorem axisBlockedFreePair_startCollisionCodeNoHit_pos_of_twoRightFutureNeverMeetPos
    (hfuture :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState)))
          freePairNeverMeetPathEvent) :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  have hstep_ab :
      0 <
        (discreteMatrixKernel independentProductPairMatrix a)
          ({b} : Set (AxisState × AxisState)) := by
    simpa [a, b] using
      axisBlockedFreePair_startPair_launchToOffDefect_pos (Pq := Pq) (Xq := Xq)
  have hstep_bc :
      0 <
        (discreteMatrixKernel independentProductPairMatrix b)
          ({c} : Set (AxisState × AxisState)) := by
    rw [discreteMatrixKernel_apply_singleton]
    -- Proof comment: from the launched pair `b`, both walkers can step one unit right to the
    -- truthful two-right state `c` with positive one-step mass.
    norm_num [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, b, c]
  have hstartNever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) a
          freePairNeverMeetPathEvent := by
    -- Proof comment: combine the explicit two-step history lower bound with the assumed positive
    -- future never-meet row from the truthful two-right state `c`.
    exact lt_of_lt_of_le
      (ENNReal.mul_pos (ENNReal.mul_pos hstep_ab hstep_bc) hfuture)
      (axisBlockedFreePair_startNeverMeet_lowerBoundFromTwoRight
        (Pq := Pq) (Xq := Xq))
  -- Proof comment: rewrite the positive start-pair never-meet row back to the exact
  -- start-side collision-code no-hit mass.
  rw [axisBlockedFreePair_startPathKernel_neverMeet_eq_collisionCodeNoHitMass
    (Pq := Pq) (Xq := Xq)] at hstartNever
  simpa [a] using hstartNever

/-- Helper for Exercise 18.2.4: the honest remaining root is positivity of the start-pair
collision-code no-hit mass. -/
private theorem axisBlockedFreePair_startPairCollisionCodeNoHit_pos_root :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  -- Route correction: the start-side root now comes directly from the truthful two-right
  -- collision-line event, rather than looping back through the obsolete launch absorbed-tail
  -- shell.
  -- Proof comment: first upgrade the direct two-right collision-line positivity root to positive
  -- future never-meet mass from `((2,0),(2,1))`, then transport that positive row back through
  -- the explicit two-step start-to-two-right history.
  exact
    axisBlockedFreePair_startCollisionCodeNoHit_pos_of_twoRightFutureNeverMeetPos
      (Pq := Pq) (Xq := Xq) <|
      axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_latticeCollisionLineAvoidPos
        (Pq := Pq) (Xq := Xq) <|
        axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_root
          (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: positive start-side collision-code no-hit mass transports
directly to positive launched never-meet mass by the existing start↔launch equivalence. -/
private theorem axisBlockedFreePair_launchPathKernel_neverMeet_pos_of_startRoot
    (hstart :
      0 <
        Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
          axisBlockedDefectNoHitPathEvent) :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  -- Proof comment: reuse the established equivalence between launched never-meet positivity and
  -- start-side collision-code no-hit positivity.
  exact
    (axisBlockedFreePair_launchNeverMeet_pos_iff_startCollisionCodeNoHit_pos
      (Pq := Pq) (Xq := Xq)).2 hstart

/-- Helper for Exercise 18.2.4: positive launched never-meet mass pushes one truthful step to the
two-right row, and then rewrites back to the lattice collision-line avoidance event. -/
private theorem axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_of_launchRoot
    (hlaunch :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent) :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  have hstep_pos :
      0 <
        (discreteMatrixKernel independentProductPairMatrix c)
          ({b} : Set (AxisState × AxisState)) := by
    -- Proof comment: the explicit one-step move sending both walkers left from the two-right row
    -- to the launched row has positive mass.
    rw [discreteMatrixKernel_apply_singleton]
    norm_num [independentProductPairMatrix, vertical_axis_blocked_walk_transition_matrix,
      isAxisNeighbor, isHorizontalNeighbor, isVerticalNeighbor, b, c]
  have htwoRightNever :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent := by
    -- Proof comment: multiply the positive launched never-meet mass by the positive one-step
    -- return mass `c → b`, then use the existing lower bound from launch to two-right.
    exact lt_of_lt_of_le
      (ENNReal.mul_pos hstep_pos hlaunch)
      (axisBlockedFreePair_twoRightNeverMeet_lowerBoundFromLaunch
        (Pq := Pq) (Xq := Xq))
  -- Proof comment: rewrite the truthful two-right never-meet row as the encoded collision-line
  -- avoidance event for the same starting row.
  rw [← axisBlockedFreePair_pathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (Pq := Pq) (Xq := Xq) c]
  exact htwoRightNever

/-- Helper for Exercise 18.2.4: reducing the launch absorbed-tail theorem to a single honest
analytic frontier, namely strict positivity of the truthful two-right collision-line-avoidance
mass on encoded `ℤ^3` path space. -/
private theorem axisBlockedFreePair_twoRightFutureNeverMeet_pos_noncircular_frontier :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  have hstart :
      0 <
        Measure.map axisBlockedFreePairCollisionCodePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
          axisBlockedDefectNoHitPathEvent :=
    axisBlockedFreePair_startPairCollisionCodeNoHit_pos_root (Pq := Pq) (Xq := Xq)
  have hlaunch :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent :=
    axisBlockedFreePair_launchPathKernel_neverMeet_pos_of_startRoot
      (Pq := Pq) (Xq := Xq) hstart
  have hline :
      0 <
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((2, 0) : AxisState), ((2, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent :=
    axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_of_launchRoot
      (Pq := Pq) (Xq := Xq) hlaunch
  -- Proof comment: the frontier theorem is now just the flat transport chain from the start-side
  -- root to the truthful two-right collision-line event, followed by the exact event rewrite.
  exact
    axisBlockedFreePair_twoRightFutureNeverMeet_pos_of_latticeCollisionLineAvoidPos
      (Pq := Pq) (Xq := Xq) hline

/-- Helper for Exercise 18.2.4: the truthful two-right absorbed-tail theorem reduces to the
noncircular launch-side absorbed-tail frontier via the explicit one-step return
`((2,0),(2,1)) → ((1,0),(1,1))`. -/
private theorem axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_noncircular :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Route correction: the truthful two-right theorem now depends only on the launch-side
  -- absorbed tail, so the remaining blocker can be isolated at the smaller launch row.
  have hfuture :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState)))
          freePairNeverMeetPathEvent :=
    axisBlockedFreePair_twoRightFutureNeverMeet_pos_noncircular_frontier
      (Pq := Pq) (Xq := Xq)
  have hjump :
      0 <
        (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
          (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) :=
    axisBlockedFreePair_launchJumpCollisionCodeNoHit_pos_of_twoRightFutureNeverMeet
      (Pq := Pq) (Xq := Xq) hfuture
  have hline :
      0 <
        Measure.map axisBlockedFreePairLatticePath
          (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
          axisBlockedDefectAvoidCollisionLinePathEvent := by
    -- Proof comment: the launched jump-code no-hit event is exactly the launched collision-line
    -- avoidance mass under the earlier pushforward identity.
    rw [axisBlockedFreePair_launchJumpCollisionCodeNoHit_mass_eq (Pq := Pq) (Xq := Xq)]
    exact hjump
  -- Proof comment: positive launched collision-line avoidance now feeds directly into the
  -- standard launch-side continuity-from-above transport.
  exact
    axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_of_collisionLineAvoidPos
      (Pq := Pq) (Xq := Xq) hline

/-- Helper for Exercise 18.2.4: the honest noncircular two-right root is nonvanishing of the
absorbed off-diagonal tail at `((2,0),(2,1))`. -/
-- Route correction: the sampled-owner comparison at `![2,1,-1]` is structurally blocked by
-- `axisBlockedFreePairDefectVisitOwner_rawChart_twoRight_step_obstruction`, so the live root is
-- now the exact absorbed-kernel tail that the generic continuity-from-above theorem consumes.
private theorem axisBlockedFreePair_twoRightAbsorbedOffDiagonal_not_tendsto_zero_direct :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((2, 0) : AxisState), ((2, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Proof comment: the earlier one-step return lemma already propagates any launch-side
  -- absorbed-tail nonvanishing theorem to the truthful two-right row, so the target itself is
  -- now closed once the smaller launch frontier is supplied.
  exact
    axisBlockedFreePair_twoRightAbsorbedOffDiagonal_not_tendsto_zero_of_launchAbsorbedTail
      (Pq := Pq) (Xq := Xq)
      (axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_noncircular
        (Pq := Pq) (Xq := Xq))

/-- Helper for Exercise 18.2.4: the remaining noncircular analytic input can be reduced to the
strict positivity of the two-right future never-meet row. -/
private theorem axisBlockedFreePair_twoRightFutureNeverMeet_pos_noncircular :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  -- Proof comment: once the truthful absorbed off-diagonal tail is known not to vanish, the
  -- generic continuity-from-above theorem upgrades it directly to positive never-meet mass from
  -- the same two-right row `c`.
  simpa [c] using
    independentProductPairPathKernel_neverMeet_pos_of_absorbedOffDiagonalNotTendstoZero
      (Pq := Pq) (Xq := Xq) c
      (axisBlockedFreePair_twoRightAbsorbedOffDiagonal_not_tendsto_zero_direct
        (Pq := Pq) (Xq := Xq))

/-- Helper for Exercise 18.2.4: the sharpened analytic frontier is strict positivity of the
launched jump-code no-hit event under the launched owner law. -/
private theorem axisBlockedFreePair_launchJumpCollisionCodeNoHit_pos_frontier :
    0 <
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
        (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) := by
  -- Route correction: the start-side root now depends only on this launched event. The old
  -- sampled-owner and bounded-comparison routes were false because they missed off-defect
  -- collisions or asked for a disproved all-horizon domination.
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let historyEvent : Set Ωq := {ω | Xq 0 ω = b} ∩ {ω | Xq 1 ω = c}
  let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
  have hhistory_pos : 0 < μ historyEvent := by
    -- Proof comment: the explicit two-step history where both walkers move right immediately from
    -- launch already has strictly positive mass under the launched owner law.
    simpa [μ, historyEvent, b, c] using
      axisBlockedFreePair_launchImmediateRightHistory_pos (Pq := Pq) (Xq := Xq)
  have hhistory_future_mass :
      μ (historyEvent ∩ futureEvent) =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent) * μ historyEvent := by
    -- Proof comment: once the immediate-right history is fixed, the remaining event depends only
    -- on the future path-kernel row from the truthful two-right state `c`.
    simpa [μ, historyEvent, futureEvent, b, c] using
      axisBlockedFreePair_launchImmediateRightHistory_futureNeverMeet_mass
        (Pq := Pq) (Xq := Xq)
  have hsubset :
      historyEvent ∩ futureEvent ⊆
        axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq) := by
    -- Proof comment: on this history atom, future never-meet already implies full raw
    -- collision-line avoidance, hence the launched jump-code no-hit event.
    simpa [historyEvent, futureEvent, b, c] using
      axisBlockedFreePair_launchImmediateRightHistory_futureNeverMeet_subset_jumpNoHit
        (Pq := Pq) (Xq := Xq)
  have hfuture_pos :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent := by
    -- Proof comment: the frontier is now reduced to the single truthful two-right positivity
    -- input recorded in the preceding helper.
    simpa [c] using
      axisBlockedFreePair_twoRightFutureNeverMeet_pos_noncircular
        (Pq := Pq) (Xq := Xq)
  have hinter_pos : 0 < μ (historyEvent ∩ futureEvent) := by
    -- Proof comment: multiply the positive history atom by the positive future row from `c`.
    rw [hhistory_future_mass]
    exact ENNReal.mul_pos hfuture_pos hhistory_pos
  -- Proof comment: the positive explicit subevent sits inside the launched jump-code no-hit
  -- event, so monotonicity gives the desired frontier positivity.
  exact lt_of_lt_of_le hinter_pos (measure_mono hsubset)

/-- Helper for Exercise 18.2.4: once the truthful launched jump-code no-hit event has positive
mass, the corresponding launched collision-line-avoidance mass is positive by the established
pushforward identity. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_canonicalOwnerLowerBound :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Route correction: the blocked canonical-SRW3 lower-bound helper has been removed from the
  -- live call graph. The truthful launched jump-code no-hit event already computes exactly the
  -- launched collision-line-avoidance mass.
  -- Proof comment: rewrite the launched collision-line-avoidance mass to the truthful launched
  -- jump-code no-hit event and reuse the positive frontier proved just above.
  rw [axisBlockedFreePair_launchJumpCollisionCodeNoHit_mass_eq (Pq := Pq) (Xq := Xq)]
  exact
    axisBlockedFreePair_launchJumpCollisionCodeNoHit_pos_frontier
      (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: positive launched collision-line-avoidance mass forces the
launched absorbed off-diagonal tail to stay away from `0`. -/
private theorem axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_frontier :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Proof comment: the launched collision-line-avoidance positivity theorem is now direct, so
  -- the standard launch-side transport immediately yields nonvanishing of the absorbed tail.
  exact
    axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_of_collisionLineAvoidPos
      (Pq := Pq) (Xq := Xq)
      (axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_canonicalOwnerLowerBound
        (Pq := Pq) (Xq := Xq))

/-- Helper for Exercise 18.2.4: positivity of the two-right future never-meet row is reduced to
strict positivity of the truthful encoded collision-line-avoidance event at
`((2,0),(2,1))`. -/
private theorem axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((2, 0) : AxisState), ((2, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Proof comment: this public local name is now just the direct two-right positivity root,
  -- keeping downstream transports unchanged.
  exact
    axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos_root
      (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: from the explicit state `((2,0),(2,1))`, the future free-pair
never-meet row has strictly positive mass. -/
private theorem axisBlockedFreePair_twoRightFutureNeverMeet_pos :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((2, 0) : AxisState), ((2, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  -- Proof comment: the `c`-row never-meet mass is just the encoded collision-line-avoidance
  -- mass for the truthful lattice path started from the same row.
  rw [axisBlockedFreePair_pathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (Pq := Pq) (Xq := Xq) c]
  simpa [c] using
    axisBlockedFreePair_twoRightLatticeCollisionLineAvoid_pos
      (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the only remaining launch-side analytic frontier is strict
positivity of the launched jump-code no-hit event under the launched owner law. -/
private theorem axisBlockedFreePair_launchJumpCollisionCodeNoHit_pos_root :
    0 <
      (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
        (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) := by
  -- Proof comment: all transport has now been flattened to one explicit launched sample-space
  -- event, so the remaining gap is purely analytic.
  have hmeas :
      MeasurableSet
        (axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq)) :=
    axisBlockedFreePair_launchJumpCollisionCodeNoHit_measurableSet (Xq := Xq)
  let _ := hmeas
  let b : AxisState × AxisState := (((1, 0) : AxisState), ((1, 1) : AxisState))
  let c : AxisState × AxisState := (((2, 0) : AxisState), ((2, 1) : AxisState))
  let μ : Measure Ωq :=
    (axisBlockedFreePairDefectVisitOwnerLaw (Pq := Pq) ![1, 1, -1] : Measure Ωq)
  let historyEvent : Set Ωq := {ω | Xq 0 ω = b} ∩ {ω | Xq 1 ω = c}
  let futureEvent : Set Ωq := {ω | futurePath Xq 1 ω ∈ freePairNeverMeetPathEvent}
  have hhistory_pos : 0 < μ historyEvent := by
    simpa [μ, historyEvent, b, c] using
      axisBlockedFreePair_launchImmediateRightHistory_pos (Pq := Pq) (Xq := Xq)
  have hhistory_future_mass :
      μ (historyEvent ∩ futureEvent) =
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent) * μ historyEvent := by
    simpa [μ, historyEvent, futureEvent, b, c] using
      axisBlockedFreePair_launchImmediateRightHistory_futureNeverMeet_mass
        (Pq := Pq) (Xq := Xq)
  have hsubset :
      historyEvent ∩ futureEvent ⊆
        axisBlockedFreePairLaunchJumpCollisionCodeNoHitEvent (Xq := Xq) := by
    simpa [historyEvent, futureEvent, b, c] using
      axisBlockedFreePair_launchImmediateRightHistory_futureNeverMeet_subset_jumpNoHit
        (Pq := Pq) (Xq := Xq)
  have hfuture_pos :
      0 <
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq) c
          freePairNeverMeetPathEvent := by
    simpa [c] using axisBlockedFreePair_twoRightFutureNeverMeet_pos
      (Pq := Pq) (Xq := Xq)
  have hinter_pos : 0 < μ (historyEvent ∩ futureEvent) := by
    rw [hhistory_future_mass]
    exact ENNReal.mul_pos hfuture_pos hhistory_pos
  exact lt_of_lt_of_le hinter_pos (measure_mono hsubset)

/-- Helper for Exercise 18.2.4: the lone remaining non-circular analytic input is strict
positivity of the launched collision-line avoidance mass. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_noncircular :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Proof comment: reuse the earlier direct launch root instead of re-entering the two-right
  -- wrapper chain under a later local name.
  exact
    axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_canonicalOwnerLowerBound
      (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the three-way return-backbone route has been reduced to the
single analytic frontier that the earlier equivalence already isolates, namely non-vanishing of
the absorbed off-diagonal tail from the start pair. -/
private theorem axisBlockedFreePair_startAbsorbedOffDiagonal_not_tendsto_zero_frontier :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Route correction: the unfinished return-backbone construction was only being used to recover
  -- this absorbed-tail non-vanishing statement. Isolating that statement leaves one honest
  -- analytic blocker instead of three coupled structural placeholders.
  -- Proof comment: the start-side tail is now reduced to one explicit one-step comparison from
  -- the start pair to the launched pair, and then to positive launch-side collision-line
  -- avoidance, so only that non-circular launch theorem remains.
  refine
    axisBlockedFreePair_startAbsorbedOffDiagonal_not_tendsto_zero_of_launchAbsorbedTail
      (Pq := Pq) (Xq := Xq) <|
    axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_of_collisionLineAvoidPos
      (Pq := Pq) (Xq := Xq) <|
    axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_noncircular
      (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the remaining genuinely independent launch-side input is strict
positivity of the launched never-meet row. -/
private theorem axisBlockedFreePair_startPairCollisionCodeNoHit_pos_frontier :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  -- Route correction: the file already isolates start-side collision-code positivity as exactly
  -- the absorbed off-diagonal non-vanishing statement. Using that equivalence removes the stalled
  -- SRW3-owner scaffolding from the live blocker.
  -- Proof comment: transport the isolated absorbed-tail non-vanishing frontier through the
  -- earlier start-side equivalence to recover the collision-code no-hit positivity statement.
  exact
    (axisBlockedFreePair_startCollisionCodeNoHit_pos_iff_startAbsorbedOffDiagonalNotTendstoZero
      (Pq := Pq) (Xq := Xq)).2
      (axisBlockedFreePair_startAbsorbedOffDiagonal_not_tendsto_zero_frontier
        (Pq := Pq) (Xq := Xq))

/-- Helper for Exercise 18.2.4: the remaining genuinely independent launch-side input is strict
positivity of the launched never-meet row. -/
private theorem axisBlockedFreePair_launchPathKernel_neverMeet_pos_seed :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  -- Route correction: the honest blocker is the start-side collision-code no-hit theorem, not a
  -- separate launch-side seed. Once the start-side frontier is isolated, the launch theorem is a
  -- direct transport through the existing start↔launch equivalence.
  exact
    (axisBlockedFreePair_launchNeverMeet_pos_iff_startCollisionCodeNoHit_pos
      (Pq := Pq) (Xq := Xq)).2 <|
    axisBlockedFreePair_startPairCollisionCodeNoHit_pos_frontier
      (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the launch-side seed immediately gives nonvanishing of the
launched absorbed off-diagonal tail. -/
private theorem axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_seed :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Proof comment: the existing launch-side continuity-from-above argument already upgrades
  -- positive launch never-meet mass to nonvanishing of the absorbed off-diagonal tail.
  exact
    axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_of_launchNeverMeetPos
      (Pq := Pq) (Xq := Xq)
      (axisBlockedFreePair_launchPathKernel_neverMeet_pos_seed
        (Pq := Pq) (Xq := Xq))

/-- Helper for Exercise 18.2.4: once the launched absorbed off-diagonal tail is known not to
vanish, the one-step lower bound from `((0,0),(0,1))` to `((1,0),(1,1))` forces the same
nonvanishing for the start pair. -/
private theorem axisBlockedFreePair_startAbsorbedOffDiagonal_not_tendsto_zero_of_launchSeed :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Proof comment: this is exactly the generic launch-to-start tail comparison, now fed by the
  -- launch-side seed theorem.
  exact
    axisBlockedFreePair_startAbsorbedOffDiagonal_not_tendsto_zero_of_launchAbsorbedTail
      (Pq := Pq) (Xq := Xq)
      (axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_seed
        (Pq := Pq) (Xq := Xq))

/-- Helper for Exercise 18.2.4: the live analytic frontier is strict positivity of the start-pair
collision-code no-hit mass. -/
private theorem axisBlockedFreePair_startPairCollisionCodeNoHit_pos_boundaryRoot :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  -- Proof comment: expose the isolated start-side frontier under the downstream boundary-root
  -- name so the remaining wrappers all point to the same single blocker.
  exact axisBlockedFreePair_startPairCollisionCodeNoHit_pos_frontier
    (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: once the start-side collision-code no-hit mass is positive, the
existing one-step return bridge gives launched `ℤ^3` collision-line avoidance positivity. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_boundaryRoot :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Proof comment: the launch-side positivity statement is now only the stable start-to-launch
  -- transport step from the start-pair collision-code no-hit root.
  exact
    axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_of_startCollisionCodeNoHit
      (Pq := Pq) (Xq := Xq)
      (axisBlockedFreePair_startPairCollisionCodeNoHit_pos_boundaryRoot
        (Pq := Pq) (Xq := Xq))

/-- Helper for Exercise 18.2.4: expose the start-side frontier under the older local API name used
later in the file. -/
private theorem axisBlockedFreePair_startPairCollisionCodeNoHit_pos_fromSampledOwner :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  -- Proof comment: this is just the stabilized start-side blocker theorem under its historical
  -- local name, so downstream wrappers all point to the same frontier.
  exact axisBlockedFreePair_startPairCollisionCodeNoHit_pos_boundaryRoot
    (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the correct start-side frontier is strict positivity of the
start-pair collision-code no-hit mass; the remaining work is to compare that event to a genuine
start-law witness without using the false sampled-owner monotonicity shortcut. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_direct :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Route correction: the launch root now depends on the start-side collision-code positivity
  -- frontier, not on the disproved raw-SRW3 absorbed comparison.
  -- Proof comment: this is now exactly the launch-side root theorem, kept under the old name so
  -- downstream wrappers remain unchanged.
  exact axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_boundaryRoot
    (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: direct launch-side collision-line avoidance positivity forces the
start absorbed off-diagonal masses to stay away from `0`. -/
private theorem axisBlockedFreePair_startAbsorbedOffDiagonal_not_tendsto_zero :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Route correction: the start-side tail no longer needs a separate launch-tail contradiction
  -- argument. The earlier start-side iff already identifies this statement with the repaired
  -- start collision-code no-hit root.
  -- Proof comment: apply the start-side collision-code/no-hit ⇔ absorbed-tail nonvanishing
  -- equivalence directly to the repaired start root.
  exact
    (axisBlockedFreePair_startCollisionCodeNoHit_pos_iff_startAbsorbedOffDiagonalNotTendstoZero
      (Pq := Pq) (Xq := Xq)).1 <|
      axisBlockedFreePair_startPairCollisionCodeNoHit_pos_root
        (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the stabilized analytic frontier is strict positivity of the
launched free-pair never-meet path-kernel row. -/
private theorem axisBlockedFreePair_launchPathKernel_neverMeet_pos_root :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  -- Route correction: keep the historical `_root` surface, but close it from the stabilized
  -- boundary-root launch theorem instead of the obsolete launch-root alias chain.
  -- Proof comment: rewrite the stabilized launched `ℤ^3` collision-line-avoidance mass back to
  -- the corresponding launched never-meet row.
  rw [axisBlockedFreePair_launchPathKernel_neverMeet_eq_latticeCollisionLineAvoid
    (Pq := Pq) (Xq := Xq)]
  exact axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_boundaryRoot
    (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: once the correct start-pair collision-code no-hit positivity is
available, the existing one-step start-to-launch bridge gives the launched `ℤ^3`
collision-line-avoidance positivity for free. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_root :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Proof comment: expose the stabilized boundary-root theorem under the downstream-facing root
  -- name used later in the file.
  exact axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_boundaryRoot
    (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: strict positivity of the start-pair collision-code no-hit mass is
the remaining analytic root input for the launched no-collision theorem. -/
private theorem axisBlockedFreePair_startPairCollisionCodeNoHit_pos :
    0 <
      Measure.map axisBlockedFreePairCollisionCodePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((0, 0) : AxisState), ((0, 1) : AxisState))))
        axisBlockedDefectNoHitPathEvent := by
  -- Route correction: the surviving endgame should point directly at the stabilized boundary-root
  -- theorem, not back through the older root alias chain.
  -- Proof comment: reuse the boundary-root start-side positivity statement verbatim so downstream
  -- wrappers share one explicit frontier.
  exact axisBlockedFreePair_startPairCollisionCodeNoHit_pos_boundaryRoot
    (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the only remaining analytic input is positivity of the launched
`ℤ^3` collision-line avoidance event under the encoded free-pair path law. -/
private theorem axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos :
    0 <
      Measure.map axisBlockedFreePairLatticePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedDefectAvoidCollisionLinePathEvent := by
  -- Route correction: the surviving endgame now takes its launch-side positivity directly from
  -- the stabilized boundary-root theorem rather than re-entering the old launch-root wrapper.
  -- Proof comment: this theorem is now just the downstream-facing alias of the boundary-root
  -- launch collision-line-avoidance statement.
  exact axisBlockedFreePair_launchLatticeCollisionLineAvoid_pos_boundaryRoot
    (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the remaining analytic root is a direct non-vanishing theorem for
the absorbed off-diagonal masses started from the launched pair. -/
private theorem axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_direct :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Route correction: the downstream absorbed-tail wrapper should now expose the stabilized
  -- frontier theorem directly, rather than rebuilding it through the older root aliases.
  -- Proof comment: the earlier frontier theorem already packages the exact continuity-from-above
  -- argument for the launched row.
  exact axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_frontier
    (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the analytic root is a direct positivity theorem for the launched
never-meet path-kernel row, proved on one normalized owner surface and then rewritten back. -/
private theorem axisBlockedFreePair_launchPathKernel_neverMeet_pos_direct :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  -- Proof comment: expose the stabilized launch seed directly, so later wrappers do not reopen
  -- any of the older root-alias normalization routes.
  exact axisBlockedFreePair_launchPathKernel_neverMeet_pos_seed
    (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the launched absorbed off-diagonal masses should not tend to
`0`; this is a wrapper around the launched never-meet positivity input. -/
private theorem axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((1, 0) : AxisState), ((1, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Proof comment: expose the direct non-vanishing theorem as the stable absorbed-tail API used
  -- by the downstream coupling contradiction.
  exact
    axisBlockedFreePair_launchAbsorbedOffDiagonal_not_tendsto_zero_direct
      (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: non-vanishing of the launched absorbed off-diagonal masses forces
strict positivity of the launched never-meet path-kernel mass. -/
private theorem axisBlockedFreePair_launchPathKernel_neverMeet_pos :
    0 <
      independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
        ((((1, 0) : AxisState), ((1, 1) : AxisState)))
        freePairNeverMeetPathEvent := by
  -- Proof comment: expose the direct launch-state positivity theorem as the stable local API used
  -- by the downstream start-pair and defect-witness wrappers.
  exact axisBlockedFreePair_launchPathKernel_neverMeet_pos_direct (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the launched free-pair path-kernel row gives strictly positive
mass to the never-meet event. -/
private theorem axisBlockedFreePairLaunchRelativeAvoidCollision_pos :
    0 <
      Measure.map axisBlockedFreePairRelativePath
        (independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState))))
        axisBlockedFreePairRelativeAvoidCollisionPathEvent := by
  -- Proof comment: after the analytic root is exposed as launched never-meet positivity, the
  -- relative-owner statement is only the corresponding pushforward rewrite.
  rw [← axisBlockedFreePair_launchPathKernel_neverMeet_eq_relativeAvoidCollisionMass
    (Pq := Pq) (Xq := Xq)]
  exact axisBlockedFreePair_launchPathKernel_neverMeet_pos (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the launched never-meet path-law row admits a positive lower
bound from an auxiliary defect-chain no-hit event. -/
private theorem axisBlockedFreePair_launchNeverMeet_lowerBoundFromDefectNoHit :
    ∃ ν : ProbabilityMeasure (ℕ → LatticePoint 2),
      0 < (ν : Measure (ℕ → LatticePoint 2)) axisBlockedDefectNoHitPathEvent ∧
      (ν : Measure (ℕ → LatticePoint 2)) axisBlockedDefectNoHitPathEvent ≤
        independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
          ((((1, 0) : AxisState), ((1, 1) : AxisState)))
          freePairNeverMeetPathEvent := by
  let κ : ℝ≥0∞ :=
    independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
      ((((1, 0) : AxisState), ((1, 1) : AxisState)))
      freePairNeverMeetPathEvent
  have hκ_le : κ ≤ 1 := by
    -- Proof comment: every row of the realized path kernel is a probability measure, so every
    -- measurable event has mass at most `1`.
    calc
      κ ≤
          independentProductPairRealizationPathKernel (Pq := Pq) (Xq := Xq)
            ((((1, 0) : AxisState), ((1, 1) : AxisState)))
            Set.univ := by
              exact measure_mono (by intro path _; simp)
      _ = 1 := by simp [κ]
  have hκ_pos : 0 < κ := by
    -- Proof comment: the defect-witness wrapper now consumes the direct launched positivity API
    -- instead of reopening the older collision-line encoding route.
    simpa [κ] using
      axisBlockedFreePair_launchPathKernel_neverMeet_pos (Pq := Pq) (Xq := Xq)
  obtain ⟨ν, hν_pos, hν_eq⟩ := axisBlockedDefectNoHitWitness_of_pos hκ_pos hκ_le
  refine ⟨ν, hν_pos, ?_⟩
  -- Proof comment: the witness was built so that its no-hit mass is exactly the launched path
  -- kernel mass `κ`.
  simpa [κ] using hν_eq.le

/-- Helper for Exercise 18.2.4: the remaining analytic input is positivity of the launched
never-meet event under the free product-pair realization. -/
private theorem axisBlockedFreePair_launchNeverMeetMeasure_pos :
    0 <
      (Pq ((((1, 0) : AxisState), ((1, 1) : AxisState))) : Measure Ωq)
        {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} := by
  -- Proof comment: rewrite the launched path-kernel row back to the corresponding realization
  -- probability and then reuse the direct launched positivity theorem.
  rw [← axisBlockedFreePair_launchPathKernel_neverMeet_eq_measure (Pq := Pq) (Xq := Xq)]
  exact axisBlockedFreePair_launchPathKernel_neverMeet_pos (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: for the free product-pair chain started from `((0,0),(0,1))`,
the probability of never hitting the diagonal is the same start-pair positivity statement as the
collision-code no-hit event, rewritten back through the established path-kernel identities. -/
private theorem axisBlockedFreePair_startPair_neverMeet_pos
    {Ωq : Type*} [MeasurableSpace Ωq]
    {Pq : AxisState × AxisState → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → AxisState × AxisState}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq] :
    (Pq ((((0, 0) : AxisState), ((0, 1) : AxisState))) : Measure Ωq)
      {ω | ∀ n : ℕ, (Xq n ω).1 ≠ (Xq n ω).2} > 0 := by
  -- Proof comment: first rewrite the realization probability to the realized path-kernel row at
  -- the distinguished start pair.
  rw [← axisBlockedFreePair_startPathKernel_neverMeet_eq_measure (Pq := Pq) (Xq := Xq)]
  -- Proof comment: then identify that row with the corresponding collision-code no-hit mass.
  rw [axisBlockedFreePair_startPathKernel_neverMeet_eq_collisionCodeNoHitMass
    (Pq := Pq) (Xq := Xq)]
  -- Proof comment: the resulting positivity is exactly the stabilized start-side root theorem.
  exact axisBlockedFreePair_startPairCollisionCodeNoHit_pos (Pq := Pq) (Xq := Xq)

section IndependentCoalescence

variable {Ω : Type v} [MeasurableSpace Ω]
variable {Pcouple : AxisState × AxisState → ProbabilityMeasure Ω}
variable {Z : ℕ → Ω → AxisState × AxisState}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦
    discreteMatrixKernel
      (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ n)
  Pcouple Z]

/-- Helper for Exercise 18.2.4: from a diagonal state, the independent coalescent one-step kernel
assigns zero mass to the off-diagonal. -/
private theorem axisBlockedCoalescentDiagonal_offDiagonalMass_eq_zero
    (x : AxisState) :
    discreteMatrixKernel
        (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix)
        (x, x)
      {s : AxisState × AxisState | s.1 ≠ s.2} = 0 := by
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ (show
    MeasurableSet {s : AxisState × AxisState | s.1 ≠ s.2} from MeasurableSet.of_discrete)]
  refine ENNReal.tsum_eq_zero.2 ?_
  intro s
  by_cases hs : s.1 ≠ s.2
  · -- Proof comment: every off-diagonal target already has zero one-step mass from a diagonal
    -- source because the coalescent sticks once the two coordinates meet.
    rw [Set.indicator_of_mem hs]
    simpa using
      independentCoalescentMatrix_apply_diag_of_ne
        (p := vertical_axis_blocked_walk_transition_matrix) (x := x) (h := hs)
  · -- Proof comment: on the diagonal complement, the off-diagonal indicator vanishes.
    rw [Set.indicator_of_notMem hs]
    simp

/-- Helper for Exercise 18.2.4: once the independent coalescent starts on the diagonal, every
positive-time marginal remains supported on the diagonal. -/
private theorem axisBlockedCoalescentDiagonal_offDiagonalMass_pow_eq_zero
    (x : AxisState) :
    ∀ n : ℕ, 0 < n →
      ((discreteMatrixKernel
          (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ n)
        (x, x)) {s : AxisState × AxisState | s.1 ≠ s.2} = 0 := by
  let κ : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel
      (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix)
  let offDiag : Set (AxisState × AxisState) := {s | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hstep_le :
      ∀ z : AxisState × AxisState,
        κ z offDiag ≤ Set.indicator offDiag (fun _ ↦ (1 : ENNReal)) z := by
    intro z
    by_cases hz : z.1 ≠ z.2
    · have hzOff : z ∈ offDiag := by
        simpa [offDiag] using hz
      rw [Set.indicator_of_mem hzOff]
      calc
        κ z offDiag ≤ κ z Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
            simpa [κ] using
              (discreteMatrixKernel_univ
                (K := independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) z)
    · have hzNotOff : z ∉ offDiag := by
        simpa [offDiag] using hz
      rw [Set.indicator_of_notMem hzNotOff]
      rcases z with ⟨a, b⟩
      have hab : a = b := by
        simpa using hz
      subst b
      simpa [κ, offDiag] using axisBlockedCoalescentDiagonal_offDiagonalMass_eq_zero a
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction m with
  | zero =>
      -- Proof comment: the first positive step is exactly the diagonal-support lemma above.
      simpa [κ, offDiag] using axisBlockedCoalescentDiagonal_offDiagonalMass_eq_zero x
  | succ m ih =>
      -- Proof comment: integrate the one-step off-diagonal bound against the previous marginal,
      -- whose off-diagonal mass already vanished by the induction hypothesis.
      rw [Kernel.pow_succ_apply_eq_lintegral κ (m + 1) (x, x) hoffDiag_meas]
      refine le_antisymm ?_ bot_le
      calc
        ∫⁻ z, κ z offDiag ∂((κ ^ (m + 1)) (x, x)) ≤
            ∫⁻ z, Set.indicator offDiag (fun _ ↦ (1 : ENNReal)) z ∂((κ ^ (m + 1)) (x, x)) := by
              refine lintegral_mono ?_
              intro z
              exact hstep_le z
        _ = ((κ ^ (m + 1)) (x, x)) offDiag := by
            simp [offDiag, hoffDiag_meas]
        _ = 0 := ih (Nat.succ_pos _)

/-- Helper for Exercise 18.2.4: starting from a diagonal state, every fixed-time disagreement
event has probability `0`. -/
private theorem axisBlockedCoalescentDiagonal_disagreementProb_eq_zero
    (x : AxisState) :
    ∀ n : ℕ,
      (Pcouple (x, x) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2} = 0 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n ↦
          discreteMatrixKernel
            (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ n)
        Pcouple Z := inferInstance
  letI : IsMarkovKernel
      (discreteMatrixKernel
        (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix)) := by
    simpa [pow_one] using hReal.semigroup.isMarkovKernel 1
  let offDiag : Set (AxisState × AxisState) := {s | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  intro n
  have hpreimage :
      {ω | (Z n ω).1 ≠ (Z n ω).2} = Z n ⁻¹' offDiag := by
    ext ω
    simp [offDiag]
  rw [hpreimage, ← Measure.map_apply (hReal.measurable_process n) hoffDiag_meas,
    hReal.transition_eq (x, x) n]
  cases n with
  | zero =>
      -- Proof comment: at time `0`, the realization starts from the deterministic diagonal state.
      have hzero :
          ((discreteMatrixKernel
              (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ 0)
            (x, x)) = Measure.dirac (x, x) := by
              simpa [pow_zero] using (Kernel.id_apply (x, x))
      rw [hzero]
      simp [offDiag]
  | succ k =>
      -- Proof comment: after any positive number of steps, the diagonal-support lemma already
      -- kills the off-diagonal mass.
      simpa [offDiag] using
        axisBlockedCoalescentDiagonal_offDiagonalMass_pow_eq_zero x (k + 1) (Nat.succ_pos _)

/-- Helper for Exercise 18.2.4: every off-diagonal endpoint mass of the coalescent equals the
corresponding endpoint mass of the diagonal-absorbed free product-pair chain. -/
private theorem
    axisBlockedCoalescentOffDiagonalEndpointMass_eq_absorbedProductPairEndpointMass :
    ∀ n : ℕ, ∀ a : AxisState × AxisState, ∀ {w : AxisState × AxisState}, w.1 ≠ w.2 →
      ((discreteMatrixKernel
          (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ n)
        a) ({w} : Set (AxisState × AxisState)) =
        ((discreteMatrixKernel
            (independentProductPairAbsorbDiagonalMatrix) ^ n) a)
          ({w} : Set (AxisState × AxisState)) := by
  let κc : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix)
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  have hcstochastic :
      IsStochasticMatrix
        (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) := by
    exact
      independentCoalescentMatrix_isStochasticMatrix
        (p := vertical_axis_blocked_walk_transition_matrix)
        vertical_axis_blocked_walk_transition_matrix_isStochastic
  letI : IsMarkovKernel κc :=
    discreteMatrixKernel_isMarkovKernel
      (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) hcstochastic
  letI : IsMarkovKernel κAbs :=
    discreteMatrixKernel_isMarkovKernel
      independentProductPairAbsorbDiagonalMatrix
      independentProductPairAbsorbDiagonalMatrix_isStochastic
  intro n
  induction n with
  | zero =>
      intro a w hw
      simp [κc, κAbs, Kernel.id_apply, hw]
  | succ n ih =>
      intro a w hw
      rw [Kernel.pow_succ_apply_eq_lintegral κc n a (measurableSet_singleton w),
        Kernel.pow_succ_apply_eq_lintegral κAbs n a (measurableSet_singleton w)]
      rw [lintegral_kernel_apply_singleton_eq_tsum (κ := κc) ((κc ^ n) a) w,
        lintegral_kernel_apply_singleton_eq_tsum (κ := κAbs) ((κAbs ^ n) a) w]
      refine tsum_congr fun c ↦ ?_
      rcases c with ⟨u, v⟩
      by_cases hc : u ≠ v
      · rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
        rw [independentCoalescentMatrix_apply_of_ne
          (p := vertical_axis_blocked_walk_transition_matrix) hc]
        have hmass := ih a (w := (u, v)) hc
        simpa [κAbs, independentProductPairAbsorbDiagonalMatrix, independentProductPairMatrix, hc,
          mul_assoc, mul_left_comm, mul_comm] using
          congrArg
            (fun t ↦
              vertical_axis_blocked_walk_transition_matrix u w.1 *
                vertical_axis_blocked_walk_transition_matrix v w.2 * t)
            hmass
      · have hdiag : u = v := by simpa using hc
        have hcoalescent_zero :
            κc (u, v) ({w} : Set (AxisState × AxisState)) = 0 := by
          subst hdiag
          rw [discreteMatrixKernel_apply_singleton]
          simpa using
            independentCoalescentMatrix_apply_diag_of_ne
              (p := vertical_axis_blocked_walk_transition_matrix) (x := u) (h := hw)
        have habs_zero :
            κAbs (u, v) ({w} : Set (AxisState × AxisState)) = 0 := by
          have hws : w ≠ (v, v) := by
            intro hEq
            have hwdiag : w.1 = w.2 := by
              simpa [hEq] using hdiag
            exact hw hwdiag
          rw [discreteMatrixKernel_apply_singleton]
          simp [κAbs, independentProductPairAbsorbDiagonalMatrix, hdiag, hws]
        rw [hcoalescent_zero, habs_zero]
        simp

/-- Helper for Exercise 18.2.4: the coalescent off-diagonal mass equals the off-diagonal mass of
the diagonal-absorbed free product-pair chain. -/
private theorem axisBlockedCoalescentOffDiagonalMass_eq_absorbedProductPairOffDiagonalMass
    (a : AxisState × AxisState) (n : ℕ) :
    ((discreteMatrixKernel
        (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ n)
      a) {s : AxisState × AxisState | s.1 ≠ s.2} =
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a)
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
  let κc : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix)
  let κAbs : Kernel (AxisState × AxisState) (AxisState × AxisState) :=
    discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix
  let offDiag : Set (AxisState × AxisState) := {s : AxisState × AxisState | s.1 ≠ s.2}
  have hMassC :
      ((κc ^ n) a) offDiag =
        ∑' w : {u : AxisState × AxisState // u ∈ offDiag},
          ((κc ^ n) a) ({(w : AxisState × AxisState)} : Set (AxisState × AxisState)) := by
    calc
      ((κc ^ n) a) offDiag =
          ∑' w : AxisState × AxisState,
            offDiag.indicator
              (fun w ↦ ((κc ^ n) a) ({w} : Set (AxisState × AxisState))) w := by
                simpa using
                  (Measure.tsum_indicator_apply_singleton ((κc ^ n) a) offDiag
                    (show MeasurableSet offDiag from MeasurableSet.of_discrete)).symm
      _ =
          ∑' w : {u : AxisState × AxisState // u ∈ offDiag},
            ((κc ^ n) a) ({(w : AxisState × AxisState)} : Set (AxisState × AxisState)) := by
              rw [← tsum_subtype offDiag
                (fun w : AxisState × AxisState ↦
                  ((κc ^ n) a) ({w} : Set (AxisState × AxisState)))]
  have hMassAbs :
      ((κAbs ^ n) a) offDiag =
        ∑' w : {u : AxisState × AxisState // u ∈ offDiag},
          ((κAbs ^ n) a) ({(w : AxisState × AxisState)} : Set (AxisState × AxisState)) := by
    calc
      ((κAbs ^ n) a) offDiag =
          ∑' w : AxisState × AxisState,
            offDiag.indicator
              (fun w ↦ ((κAbs ^ n) a) ({w} : Set (AxisState × AxisState))) w := by
                simpa using
                  (Measure.tsum_indicator_apply_singleton ((κAbs ^ n) a) offDiag
                    (show MeasurableSet offDiag from MeasurableSet.of_discrete)).symm
      _ =
          ∑' w : {u : AxisState × AxisState // u ∈ offDiag},
            ((κAbs ^ n) a) ({(w : AxisState × AxisState)} : Set (AxisState × AxisState)) := by
              rw [← tsum_subtype offDiag
                (fun w : AxisState × AxisState ↦
                  ((κAbs ^ n) a) ({w} : Set (AxisState × AxisState)))]
  -- Proof comment: sum the endpoint identity over all off-diagonal singleton targets to pass from
  -- point masses to the full current disagreement mass.
  rw [hMassC, hMassAbs]
  refine tsum_congr fun w ↦ ?_
  exact
    axisBlockedCoalescentOffDiagonalEndpointMass_eq_absorbedProductPairEndpointMass
      n a (w := (w : AxisState × AxisState)) w.2

/-- Helper for Exercise 18.2.4: the current disagreement probability of the coalescent equals the
off-diagonal mass of the absorbed free product-pair chain. -/
private theorem axisBlockedCoalescentCurrentDisagreement_eq_absorbedProductPairOffDiagonalMass
    (a : AxisState × AxisState) (n : ℕ) :
    (Pcouple a : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2} =
      ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a)
        {s : AxisState × AxisState | s.1 ≠ s.2} := by
  let hReal :
      IsMarkovProcessRealization
        (fun n ↦
          discreteMatrixKernel
            (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ n)
        Pcouple Z := inferInstance
  let offDiag : Set (AxisState × AxisState) := {s | s.1 ≠ s.2}
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hpreimage :
      {ω | (Z n ω).1 ≠ (Z n ω).2} = Z n ⁻¹' offDiag := by
    ext ω
    simp [offDiag]
  calc
    (Pcouple a : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2}
        = ((discreteMatrixKernel
            (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ n)
            a) offDiag := by
              rw [hpreimage,
                ← Measure.map_apply (hReal.measurable_process n) hoffDiag_meas,
                hReal.transition_eq a n]
    _ =
        ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a) offDiag :=
          axisBlockedCoalescentOffDiagonalMass_eq_absorbedProductPairOffDiagonalMass a n

/-- Helper for Exercise 18.2.4: starting from a diagonal state, every tail disagreement event has
probability `0`. -/
private theorem axisBlockedCoalescentDiagonal_tailDisagreementProb_eq_zero
    (x : AxisState) (n : ℕ) :
    (Pcouple (x, x) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) = 0 := by
  let μ : Measure Ω := Pcouple (x, x)
  let A : ℕ → Set Ω := fun m ↦ {ω | (Z m ω).1 ≠ (Z m ω).2}
  have hUnion : (⋃ m ≥ n, A m) = ⋃ k : ℕ, A (n + k) := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
      rcases Set.mem_iUnion.1 hm with ⟨hmn, hA⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact Set.mem_iUnion.2 ⟨k, hA⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
      exact Set.mem_iUnion.2 ⟨n + k, Set.mem_iUnion.2 ⟨Nat.le_add_right n k, hk⟩⟩
  have hslice_zero : ∀ k : ℕ, μ (A (n + k)) = 0 := by
    intro k
    simpa [μ, A] using axisBlockedCoalescentDiagonal_disagreementProb_eq_zero
      (Pcouple := Pcouple) (Z := Z) x (n + k)
  -- Proof comment: rewrite the tail as a single countable union of its time slices and use that
  -- each slice is already null.
  rw [hUnion, measure_iUnion_null hslice_zero]

/-- Helper for Exercise 18.2.4: after time `n`, any later disagreement was already present at
time `n`, because the coalescent cannot leave the diagonal once it has entered it. -/
private theorem axisBlockedCoalescentTailDisagreement_le_currentDisagreement
    (x y : AxisState) :
    ∀ n : ℕ,
      (Pcouple (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) ≤
        (Pcouple (x, y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2} := by
  let μ : Measure Ω := Pcouple (x, y)
  let q := independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix
  let κ : Kernel (AxisState × AxisState) (AxisState × AxisState) := discreteMatrixKernel q
  let disagree : ℕ → Set Ω := fun m ↦ {ω | (Z m ω).1 ≠ (Z m ω).2}
  let offDiag : Set (AxisState × AxisState) := {s | s.1 ≠ s.2}
  let hReal : IsMarkovProcessRealization (fun m ↦ κ ^ m) Pcouple Z := by
    simpa [κ, q] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun m ↦
            discreteMatrixKernel
              (independentCoalescentMatrix vertical_axis_blocked_walk_transition_matrix) ^ m)
          Pcouple Z)
  have hqstochastic : IsStochasticMatrix q := by
    exact
      independentCoalescentMatrix_isStochasticMatrix
        (p := vertical_axis_blocked_walk_transition_matrix)
        vertical_axis_blocked_walk_transition_matrix_isStochastic
  letI : IsMarkovKernel κ := discreteMatrixKernel_isMarkovKernel q hqstochastic
  have hstep :
      ∀ a : AxisState × AxisState, ∀ ⦃A : Set (AxisState × AxisState)⦄, MeasurableSet A →
        ∀ s : ℕ,
          (Pcouple a)⟦Z (s + 1) ⁻¹' A | generatedFiltrationSpace Z s⟧ =ᵐ[(Pcouple a : Measure Ω)]
            fun ω ↦ (κ (Z s ω)).real A := by
    intro a A hA s
    simpa [κ, Nat.add_comm] using hReal.markov_property a (A := A) hA s 1
  intro n
  have htail :
      (⋃ m ≥ n, disagree m) = disagree n ∪ ⋃ k : ℕ, disagree (n + (k + 1)) := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
      rcases Set.mem_iUnion.1 hm with ⟨hmn, hdis⟩
      rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
      · exact Or.inl hdis
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, n + (k + 1) = m := ⟨m - n - 1, by omega⟩
        exact Or.inr <| Set.mem_iUnion.2 ⟨k, hk ▸ hdis⟩
    · intro hω
      rcases hω with hω | hω
      · exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨le_rfl, hω⟩⟩
      · rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
        exact Set.mem_iUnion.2 ⟨n + (k + 1), Set.mem_iUnion.2 ⟨by omega, hk⟩⟩
  have hdiag_future_zero :
      μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) = 0 := by
    let diagSlice : AxisState → Set Ω := fun u ↦ {ω | Z n ω = (u, u)}
    have hsplit :
        {ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1)) =
          ⋃ u : AxisState, diagSlice u ∩ ⋃ k : ℕ, disagree (n + (k + 1)) := by
      ext ω
      constructor
      · intro hω
        refine Set.mem_iUnion.2 ⟨(Z n ω).1, ?_⟩
        refine ⟨?_, hω.2⟩
        simpa [diagSlice] using hω.1
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨u, hu⟩
        refine ⟨?_, hu.2⟩
        simpa [diagSlice] using hu.1
    have hslice_zero :
        ∀ u : AxisState, μ (diagSlice u ∩ ⋃ k : ℕ, disagree (n + (k + 1))) = 0 := by
      intro u
      have hsliceK_zero :
          ∀ k : ℕ, μ (diagSlice u ∩ disagree (n + (k + 1))) = 0 := by
        intro k
        have hA_hist : MeasurableSet[generatedFiltrationSpace Z n] (diagSlice u) := by
          have hZn : Measurable[generatedFiltrationSpace Z n] (Z n) := by
            exact Measurable.of_comap_le <| present_le_generatedHistory (X := Z) n
          rw [show diagSlice u = Z n ⁻¹' ({(u, u)} : Set (AxisState × AxisState)) by
            ext ω
            simp [diagSlice]]
          exact hZn (measurableSet_singleton (u, u))
        have hA_meas : MeasurableSet (diagSlice u) := by
          exact (generatedHistory_le_ambient Z hReal.measurable_process n) _ hA_hist
        have hA_state : ∀ ⦃ω : Ω⦄, ω ∈ diagSlice u → Z n ω = (u, u) := by
          intro ω hω
          simpa [diagSlice] using hω
        have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
        have hslice_real : μ.real (diagSlice u ∩ disagree (n + (k + 1))) = 0 := by
          calc
            μ.real (diagSlice u ∩ disagree (n + (k + 1))) =
                ∫ ω in diagSlice u,
                  Set.indicator (Z (n + (k + 1)) ⁻¹' offDiag) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                    rw [← MeasureTheory.integral_indicator hA_meas]
                    simpa [μ, disagree, offDiag, Set.indicator_indicator, Set.inter_assoc,
                      Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                      (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                        (hA_meas.inter ((hReal.measurable_process (n + (k + 1))) hoffDiag_meas))).symm
            _ = ∫ ω in diagSlice u, ((κ ^ (k + 1)) (Z n ω)).real offDiag ∂μ := by
                  symm
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, κ, offDiag] using
                    kernelPow_setIntegral_eq_on_history
                      (κ₁ := κ) (P := Pcouple) (X := Z)
                      hReal.measurable_process hstep (x := (x, y))
                      (A := offDiag) hoffDiag_meas n (k + 1) (B := diagSlice u) hA_hist
            _ = 0 := by
                  have hpow_zero :
                      ((κ ^ (k + 1)) (u, u)).real offDiag = 0 := by
                    have hmass :
                        ((κ ^ (k + 1)) (u, u)) offDiag = 0 := by
                      simpa [κ, offDiag] using
                        axisBlockedCoalescentDiagonal_offDiagonalMass_pow_eq_zero
                          (Pcouple := Pcouple) (Z := Z) u (k + 1) (Nat.succ_pos k)
                    simp [Measure.real_def, hmass]
                  calc
                    ∫ ω in diagSlice u, ((κ ^ (k + 1)) (Z n ω)).real offDiag ∂μ
                        = ∫ ω in diagSlice u, 0 ∂μ := by
                            refine integral_congr_ae ?_
                            filter_upwards with ω
                            by_cases hω : ω ∈ diagSlice u
                            · simp [hω, hA_state hω, hpow_zero]
                            · simp [hω]
                    _ = 0 := by simp
        exact
          (measureReal_eq_zero_iff (measure_lt_top μ (diagSlice u ∩ disagree (n + (k + 1)))).ne).1
            hslice_real
      have hinter :
          diagSlice u ∩ ⋃ k : ℕ, disagree (n + (k + 1)) =
            ⋃ k : ℕ, diagSlice u ∩ disagree (n + (k + 1)) := by
        ext ω
        simp [Set.mem_iUnion, and_left_comm, and_assoc]
      rw [hinter]
      exact measure_iUnion_null hsliceK_zero
    rw [hsplit]
    exact measure_iUnion_null hslice_zero
  calc
    μ (⋃ m ≥ n, disagree m) = μ (disagree n ∪ ⋃ k : ℕ, disagree (n + (k + 1))) := by
      rw [htail]
    _ ≤ μ (disagree n) +
        μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) := by
          refine le_trans (measure_mono ?_) (measure_union_le _ _)
          intro ω hω
          rcases hω with hω | hω
          · exact Or.inl hω
          · by_cases hdiag : (Z n ω).1 = (Z n ω).2
            · exact Or.inr ⟨hdiag, Set.mem_iUnion.2 <| Set.mem_iUnion.1 hω⟩
            · exact Or.inl hdiag
    _ = μ (disagree n) := by simp [hdiag_future_zero]

/-- Helper for Exercise 18.2.4: for the coalescent, the tail disagreement event has the same
probability as the current disagreement event because disagreement is absorbing until meeting. -/
private theorem axisBlockedCoalescentTailDisagreement_eq_currentDisagreement
    (x y : AxisState) :
    ∀ n : ℕ,
      (Pcouple (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) =
        (Pcouple (x, y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2} := by
  intro n
  apply le_antisymm
  · -- Proof comment: the hard direction is the diagonal-absorption estimate proved just above.
    exact axisBlockedCoalescentTailDisagreement_le_currentDisagreement
      (Pcouple := Pcouple) (Z := Z) x y n
  · -- Proof comment: the current disagreement slice is one member of the tail union.
    exact measure_mono <| by
      intro ω hω
      exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨le_rfl, hω⟩⟩

/-- Helper for Exercise 18.2.4: for the fixed start pair `((0,0),(0,1))`, the tail disagreement
probabilities do not tend to `0`. -/
private theorem axisBlockedIndependentProductPair_offDiagonal_not_tendsto_zero_startPair
    {Ωq : Type*} [MeasurableSpace Ωq]
    {Pq : AxisState × AxisState → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → AxisState × AxisState}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n) Pq Xq] :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  -- Route correction: expose the already-stabilized start-side absorbed-tail theorem at the
  -- public endgame boundary instead of carrying a second copy of the same launch-to-start
  -- transport proof.
  -- Proof comment: the theorem proved earlier under the free-pair API has exactly the same start
  -- row and absorbed off-diagonal tail, so we reuse it verbatim here.
  exact
    axisBlockedFreePair_startAbsorbedOffDiagonal_not_tendsto_zero
      (Pq := Pq) (Xq := Xq)

/-- Helper for Exercise 18.2.4: the absorbed free product-pair off-diagonal masses from the start
pair `((0,0),(0,1))` do not tend to `0`, stated without any hidden realization parameters. -/
private theorem axisBlockedAbsorbedProductPairOffDiagonal_not_tendsto_zero_startPair :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n)
            ((((0, 0) : AxisState), ((0, 1) : AxisState))))
            {s : AxisState × AxisState | s.1 ≠ s.2})
        Filter.atTop (nhds 0) := by
  obtain ⟨Pq, hqreal⟩ :=
    existsCanonicalDiscreteMatrixRealization
      independentProductPairMatrix
      independentProductPairMatrix_isStochastic
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel independentProductPairMatrix ^ n)
        Pq Function.eval := hqreal
  -- Proof comment: instantiate the realization-dependent avoidance theorem on the canonical
  -- trajectory realization, then forget the realization because the conclusion is kernel-only.
  simpa using
    axisBlockedIndependentProductPair_offDiagonal_not_tendsto_zero_startPair
      (Pq := Pq) (Xq := Function.eval)

/-- Helper for Exercise 18.2.4: for the fixed start pair `((0,0),(0,1))`, the tail disagreement
probabilities do not tend to `0`. -/
private theorem axisBlockedIndependentCoalescentTailFailure_startPair :
    ¬ Filter.Tendsto
        (fun n : ℕ ↦
          (Pcouple ((((0, 0) : AxisState), ((0, 1) : AxisState))) : Measure Ω)
            (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
        Filter.atTop (nhds 0) := by
  -- Route correction: the absorbed-tail normalization is now in place, so the remaining blocker is
  -- no longer the tail union itself. The new equality
  -- `axisBlockedCoalescentTailDisagreement_eq_currentDisagreement` reduces the theorem to showing
  -- that the current disagreement probabilities for the start pair `((0,0),(0,1))` do not tend to
  -- `0`, or equivalently that the corresponding never-meet survival event has positive
  -- probability.
  let a : AxisState × AxisState := (((0, 0) : AxisState), ((0, 1) : AxisState))
  let μ : Measure Ω := (Pcouple a : Measure Ω)
  have htail_fun :
      (fun n : ℕ ↦ μ (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2})) =
        fun n : ℕ ↦ μ {ω | (Z n ω).1 ≠ (Z n ω).2} := by
    funext n
    exact axisBlockedCoalescentTailDisagreement_eq_currentDisagreement
      (Pcouple := Pcouple) (Z := Z) a.1 a.2 n
  have hcurrent_fun :
      (fun n : ℕ ↦ μ {ω | (Z n ω).1 ≠ (Z n ω).2}) =
        fun n : ℕ ↦
          ((discreteMatrixKernel independentProductPairAbsorbDiagonalMatrix ^ n) a)
            {s : AxisState × AxisState | s.1 ≠ s.2} := by
    funext n
    exact
      axisBlockedCoalescentCurrentDisagreement_eq_absorbedProductPairOffDiagonalMass
        (Pcouple := Pcouple) (Z := Z) a n
  -- Proof comment: the tail probabilities equal the current disagreement probabilities, and those
  -- are exactly the absorbed off-diagonal masses from the start pair.
  simpa [htail_fun, hcurrent_fun, a, μ] using
    axisBlockedAbsorbedProductPairOffDiagonal_not_tendsto_zero_startPair

/-- Helper for Exercise 18.2.4: some initial pair for the independent coalescent of the
axis-blocked walk has tail disagreement probabilities that do not converge to `0`. -/
private theorem axisBlockedIndependentCoalescentTailFailureWitness :
    ∃ x y : AxisState,
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          (Pcouple (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
        Filter.atTop (nhds 0) := by
  let x : AxisState := (0, 0)
  let y : AxisState := (0, 1)
  refine ⟨x, y, ?_⟩
  simpa [x, y] using
    axisBlockedIndependentCoalescentTailFailure_startPair (Pcouple := Pcouple) (Z := Z)

-- Proof sketch: before coalescence the difference of the two coordinates evolves like the
-- difference of two independent copies of the axis-blocked walk. The null-recurrent structure lets
-- the pair separate repeatedly, so the diagonal is not trapped quickly enough for the tail
-- disagreement probabilities to tend to `0`. Exercise 18.2.2 already identifies the independent
-- coalescent realization as a Markov coupling, so this tail-condition failure is exactly the
-- negation of the canonical Chapter 18 owner `IsSuccessfulMarkovCoupling`.
/-- Exercise 18.2.4 (4): the independent coalescent chain built from the axis-blocked walk is not
a successful Markov coupling. -/
theorem independentCoalescentChain_not_isSuccessfulMarkovCoupling :
    ¬ IsSuccessfulMarkovCoupling vertical_axis_blocked_walk_transition_matrix Pcouple Z := by
  intro hsuccess
  rcases axisBlockedIndependentCoalescentTailFailureWitness (Pcouple := Pcouple) (Z := Z) with
    ⟨x, y, hxy⟩
  exact hxy (hsuccess.tail_disagreement_tendsto_zero x y)

-- Proof sketch: unpack `IsSuccessfulMarkovCoupling`; the failure comes from its tail-disagreement
-- field.
/-- For the axis-blocked walk, some initial pair has tail disagreement probabilities that do not
converge to `0`. -/
theorem independentCoalescentChain_tail_disagreement_not_tendsto_zero :
    ∃ x y : AxisState,
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          (Pcouple (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
        Filter.atTop (nhds 0) := by
  -- Proof comment: the public statement is exactly the file-local witness theorem above.
  exact axisBlockedIndependentCoalescentTailFailureWitness (Pcouple := Pcouple) (Z := Z)

end IndependentCoalescence

end ProbabilityTheory

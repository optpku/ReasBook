/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_4.ch5_sec5_2_4_definition_5_2_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_5.ch5_sec5_2_5_theorem_5_19

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` on "Gomory lexicographic cutting plane method" was not
-- informative for this repair, so the owner/API choice follows the verified local Chapter 5
-- patterns: keep the source-facing stagewise periodic run, but expose the sampled checkpoint
-- subsequence through an explicit bridge to `GomoryLexicographicCuttingPlaneMethod`.

section Exercise512

/-- A stage-indexed periodic Gomory fractional cutting-plane run for a bounded pure integer
program adds a Gomory fractional cut at every nonterminal iteration, while every positive
multiple of `period` satisfies the Rule-1/2/3 hypotheses used in the lexicographic cutting-plane
argument. -/
structure PeriodicGomoryFractionalCuttingPlaneMethod (n : ℕ) where
  period : ℕ
  period_pos : 0 < period
  feasibleRegion : Set (Fin (n + 1) → ℝ)
  bounded_feasibleRegion : Bornology.IsBounded feasibleRegion
  relaxation : ℕ → Set (Fin n → ℝ)
  iterates : ℕ → Fin (n + 1) → ℝ
  iterates_mem_feasibleRegion : ∀ t : ℕ, iterates t ∈ feasibleRegion
  iterates_mem_relaxation : ∀ t : ℕ, (fun j ↦ iterates t j.succ) ∈ relaxation t
  selectedRow : ℕ → Option (Fin (n + 1))
  selectedRow_none_iff :
    ∀ t : ℕ, selectedRow t = none ↔
      ∀ k : Fin (n + 1), iterates t k ∈ Set.range (Int.cast : ℤ → ℝ)
  cutColumns : ℕ → Finset (Fin n)
  cutCoeff : ℕ → Fin n → ℚ
  cutRhs : ℕ → ℚ
  relaxation_step :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      relaxation (t + 1) =
        relaxation t ∩ gomory_fractional_cut (cutColumns t) (cutCoeff t) (cutRhs t)
  periodic_lexicographically_nonincreasing :
    ∀ p : ℕ, toLex (iterates ((p + 2) * period)) ≤ toLex (iterates ((p + 1) * period))
  periodic_selectedRow_spec :
    ∀ ⦃p : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow ((p + 1) * period) = some k →
      (∀ i : Fin (n + 1), i < k → iterates ((p + 1) * period) i ∈ Set.range (Int.cast : ℤ → ℝ)) ∧
        iterates ((p + 1) * period) k ∉ Set.range (Int.cast : ℤ → ℝ)
  periodic_strict_progress_on_fractional_step :
    ∀ ⦃p : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow ((p + 1) * period) = some k →
      toLex (iterates ((p + 2) * period)) < toLex (iterates ((p + 1) * period))
  periodic_selectedRow_eventually_forces_floor :
    ∀ ⦃p : ℕ⦄ ⦃k : Fin (n + 1)⦄,
      selectedRow ((p + 1) * period) = some k →
      ∀ {m : ℤ},
      iterates ((p + 1) * period) k < (m : ℝ) + 1 →
      (∀ i : Fin (n + 1), i < k →
        ∃ z : ℤ, ∀ q ≥ p + 1, iterates ((q + 1) * period) i = (z : ℝ)) →
      ∀ q ≥ p + 1, iterates ((q + 1) * period) k ≤ (m : ℝ)

namespace PeriodicGomoryFractionalCuttingPlaneMethod

/-- The `p`-th periodic checkpoint is the positive multiple `(p + 1) * period`. -/
def checkpoint {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) (p : ℕ) : ℕ :=
  (p + 1) * A.period

@[simp] theorem checkpoint_zero
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) :
    A.checkpoint 0 = A.period := by
  simp [checkpoint]

@[simp] theorem checkpoint_succ
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) (p : ℕ) :
    A.checkpoint (p + 1) = (p + 2) * A.period := by
  simp [checkpoint, Nat.add_assoc]

/-- A periodic run stops at stage `t` when no tableau row is selected for the next Gomory cut. -/
def StopsAt {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) (t : ℕ) : Prop :=
  A.selectedRow t = none

/-- The periodic run stops exactly when the current tableau iterate is integral in every
coordinate. -/
theorem stopsAt_iff
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) (t : ℕ) :
    A.StopsAt t ↔
      ∀ k : Fin (n + 1), A.iterates t k ∈ Set.range (Int.cast : ℤ → ℝ) :=
  A.selectedRow_none_iff t

/-- Every nonterminal step strengthens the current relaxation by the recorded Gomory fractional
cut. -/
theorem relaxation_step_of_not_stopsAt
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) {t : ℕ}
    (ht : ¬ A.StopsAt t) :
    A.relaxation (t + 1) =
      A.relaxation t ∩ gomory_fractional_cut (A.cutColumns t) (A.cutCoeff t) (A.cutRhs t) := by
  cases hrow : A.selectedRow t with
  | none =>
      exact False.elim <| ht hrow
  | some k =>
      exact A.relaxation_step hrow

/-- Helper for Exercise 5.12: the checkpoint cut at stage `p` is the Gomory fractional cut
recorded at the `p`th periodic checkpoint. -/
def checkpointCut
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) (p : ℕ) :
    Set (Fin n → ℝ) :=
  gomory_fractional_cut
    (A.cutColumns (A.checkpoint p))
    (A.cutCoeff (A.checkpoint p))
    (A.cutRhs (A.checkpoint p))

/-- Helper for Exercise 5.12: the sampled relaxation at checkpoint `p` consists of the points
that satisfy every earlier checkpoint cut. -/
def sampledRelaxation
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) (p : ℕ) :
    Set (Fin n → ℝ) :=
  {x | ∀ q : ℕ, q < p → x ∈ A.checkpointCut q}

/-- Helper for Exercise 5.12: membership in the sampled relaxation means satisfying every earlier
checkpoint cut. -/
@[simp] theorem mem_sampledRelaxation
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) (p : ℕ) (x : Fin n → ℝ) :
    x ∈ A.sampledRelaxation p ↔ ∀ q : ℕ, q < p → x ∈ A.checkpointCut q :=
  Iff.rfl

/-- Helper for Exercise 5.12: an earlier checkpoint cut is already active by every later
checkpoint. -/
theorem checkpointSuccLeCheckpointOfLt
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) {q p : ℕ}
    (hqp : q < p) :
    A.checkpoint q + 1 ≤ A.checkpoint p := by
  -- Compare successive checkpoints using the positive period length.
  have hperiod : 1 ≤ A.period := Nat.succ_le_of_lt A.period_pos
  have hq2 : q + 2 ≤ p + 1 := Nat.succ_le_succ (Nat.succ_le_of_lt hqp)
  calc
    A.checkpoint q + 1 = (q + 1) * A.period + 1 := by
      simp [checkpoint]
    _ ≤ (q + 1) * A.period + A.period := Nat.add_le_add_left hperiod ((q + 1) * A.period)
    _ = Nat.succ (q + 1) * A.period := by
      symm
      exact Nat.succ_mul (q + 1) A.period
    _ = (q + 2) * A.period := by
      rfl
    _ ≤ (p + 1) * A.period := Nat.mul_le_mul_right A.period hq2
    _ = A.checkpoint p := by
      simp [checkpoint]

/-- Helper for Exercise 5.12: if the periodic method never stops, then later actual relaxations
are nested inside earlier ones. -/
theorem relaxationSubsetOfLeOfNoStop
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n)
    (hnever : ∀ t : ℕ, ¬ A.StopsAt t) {s t : ℕ} (hst : s ≤ t) :
    A.relaxation t ⊆ A.relaxation s := by
  -- Peel off one nonterminal step at a time and discard the newly added cut.
  induction hst with
  | refl =>
      exact Set.Subset.rfl
  | @step t hst ih =>
      have hstep :
          A.relaxation (t + 1) =
            A.relaxation t ∩ gomory_fractional_cut (A.cutColumns t) (A.cutCoeff t) (A.cutRhs t) :=
        A.relaxation_step_of_not_stopsAt (hnever t)
      have hsubsetStep : A.relaxation (t + 1) ⊆ A.relaxation t := by
        intro x hx
        rw [hstep] at hx
        exact hx.1
      exact Set.Subset.trans hsubsetStep ih

/-- Helper for Exercise 5.12: under the no-stop hypothesis, the iterate at a later checkpoint
satisfies every earlier checkpoint cut. -/
theorem checkpointIterateMemCheckpointCutOfLtOfNoStop
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n)
    (hnever : ∀ t : ℕ, ¬ A.StopsAt t) {q p : ℕ} (hqp : q < p) :
    (fun j ↦ A.iterates (A.checkpoint p) j.succ) ∈ A.checkpointCut q := by
  -- Move the later iterate back into the relaxation obtained immediately after checkpoint `q`.
  have hmemCheckpoint :
      (fun j ↦ A.iterates (A.checkpoint p) j.succ) ∈ A.relaxation (A.checkpoint p) :=
    A.iterates_mem_relaxation (A.checkpoint p)
  have hsubset :
      A.relaxation (A.checkpoint p) ⊆ A.relaxation (A.checkpoint q + 1) :=
    A.relaxationSubsetOfLeOfNoStop hnever (A.checkpointSuccLeCheckpointOfLt hqp)
  have hmemNext :
      (fun j ↦ A.iterates (A.checkpoint p) j.succ) ∈ A.relaxation (A.checkpoint q + 1) :=
    hsubset hmemCheckpoint
  -- Unfold the nonterminal step at checkpoint `q` and read off cut membership.
  have hstep :
      A.relaxation (A.checkpoint q + 1) =
        A.relaxation (A.checkpoint q) ∩ A.checkpointCut q := by
    simpa [checkpointCut] using
      A.relaxation_step_of_not_stopsAt (hnever (A.checkpoint q))
  rw [hstep] at hmemNext
  exact hmemNext.2

/-- Helper for Exercise 5.12: under the no-stop hypothesis, the checkpoint iterate at stage `p`
belongs to the synthetic relaxation generated by the earlier checkpoint cuts. -/
theorem checkpointIterateMemSampledRelaxationOfNoStop
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n)
    (hnever : ∀ t : ℕ, ¬ A.StopsAt t) (p : ℕ) :
    (fun j ↦ A.iterates (A.checkpoint p) j.succ) ∈ A.sampledRelaxation p := by
  -- The sampled relaxation records exactly the earlier checkpoint cuts.
  rw [A.mem_sampledRelaxation]
  intro q hq
  exact A.checkpointIterateMemCheckpointCutOfLtOfNoStop hnever hq

/-- Helper for Exercise 5.12: the sampled relaxation is updated by adjoining the next checkpoint
cut by construction. -/
theorem sampledRelaxation_succ
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) (p : ℕ) :
    A.sampledRelaxation (p + 1) = A.sampledRelaxation p ∩ A.checkpointCut p := by
  -- Split the `q < p + 1` side condition into the old cuts and the new checkpoint cut.
  ext x
  rw [A.mem_sampledRelaxation, Set.mem_inter_iff, A.mem_sampledRelaxation]
  constructor
  · intro hx
    constructor
    · intro q hq
      exact hx q (Nat.lt_succ_of_lt hq)
    · exact hx p (Nat.lt_succ_self p)
  · intro hx q hq
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hq) with hlt | rfl
    · exact hx.1 q hlt
    · exact hx.2

/-- Helper for Exercise 5.12: the synthetic sampled relaxation has the required one-step update
equation at every checkpoint stage. -/
theorem sampledRelaxation_step
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n)
    {p : ℕ} {k : Fin (n + 1)}
    (_hk : A.selectedRow (A.checkpoint p) = some k) :
    A.sampledRelaxation (p + 1) = A.sampledRelaxation p ∩ A.checkpointCut p := by
  -- The sampled relaxation update is definitional and does not depend on the selected row.
  exact A.sampledRelaxation_succ p

/-- Helper for Exercise 5.12: the sampled relaxation step can be stated directly with the
canonical `gomory_fractional_cut` spelling expected by the lexicographic owner. -/
theorem sampledRelaxation_step_eq_gomory
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n)
    {p : ℕ} {k : Fin (n + 1)}
    (hk : A.selectedRow (A.checkpoint p) = some k) :
    A.sampledRelaxation (p + 1) =
      A.sampledRelaxation p ∩
        gomory_fractional_cut (A.cutColumns (A.checkpoint p)) (A.cutCoeff (A.checkpoint p))
          (A.cutRhs (A.checkpoint p)) := by
  -- Rewrite the checkpoint-cut alias back to the canonical Gomory cut expression.
  simpa [checkpointCut] using A.sampledRelaxation_step hk

/-- Helper for Exercise 5.12: under the hypothesis that no actual stage is terminal, the sampled
checkpoint subsequence forms a genuine lexicographic cutting-plane method. -/
def toGomoryLexicographicCuttingPlaneMethodOfNoStop
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n)
    (hnever : ∀ t : ℕ, ¬ A.StopsAt t) :
    GomoryLexicographicCuttingPlaneMethod n where
  feasibleRegion := A.feasibleRegion
  bounded_feasibleRegion := A.bounded_feasibleRegion
  relaxation := A.sampledRelaxation
  iterates := fun p ↦ A.iterates (A.checkpoint p)
  iterates_mem_feasibleRegion := fun p ↦ A.iterates_mem_feasibleRegion (A.checkpoint p)
  iterates_mem_relaxation := A.checkpointIterateMemSampledRelaxationOfNoStop hnever
  selectedRow := fun p ↦ A.selectedRow (A.checkpoint p)
  selectedRow_none_iff := fun p ↦ A.selectedRow_none_iff (A.checkpoint p)
  cutColumns := fun p ↦ A.cutColumns (A.checkpoint p)
  cutCoeff := fun p ↦ A.cutCoeff (A.checkpoint p)
  cutRhs := fun p ↦ A.cutRhs (A.checkpoint p)
  relaxation_step := fun {_p} {_k} hk ↦ A.sampledRelaxation_step_eq_gomory hk
  lexicographically_nonincreasing := A.periodic_lexicographically_nonincreasing
  selectedRow_spec := A.periodic_selectedRow_spec
  strict_progress_on_fractional_step := A.periodic_strict_progress_on_fractional_step
  selectedRow_eventually_forces_floor := A.periodic_selectedRow_eventually_forces_floor

/-- Helper for Exercise 5.12: the synthetic checkpoint bridge stops exactly when the periodic run
stops at the corresponding actual checkpoint. -/
@[simp] theorem toGomoryLexicographicCuttingPlaneMethodOfNoStop_stopsAt_iff
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n)
    (hnever : ∀ t : ℕ, ¬ A.StopsAt t) (p : ℕ) :
    (A.toGomoryLexicographicCuttingPlaneMethodOfNoStop hnever).StopsAt p ↔
      A.StopsAt (A.checkpoint p) :=
  Iff.rfl

end PeriodicGomoryFractionalCuttingPlaneMethod

/-- Exercise 5.12. Consider a pure integer program. Suppose that Gomory fractional cuts are added
in an iterative fashion as outlined after Eq. (5.25). Furthermore assume that Rules 1-3 of
Gomory's lexicographic cutting plane method are applied periodically, at iterations
`k, 2k, ..., pk, ...` where `k` is a positive integer. Prove that such a cutting plane method
terminates in a finite number of iterations. -/
theorem periodic_gomory_fractional_cutting_plane_method_terminates
    {n : ℕ} (A : PeriodicGomoryFractionalCuttingPlaneMethod n) :
    ∃ T : ℕ, A.StopsAt T := by
  -- Route correction: the raw checkpoint relaxation bridge requires a full-period equality that
  -- the periodic hypotheses do not provide, so we work under a no-stop contradiction hypothesis
  -- and build the checkpoint subsequence with an accumulated-cut relaxation.
  by_contra htermination
  have hnever : ∀ t : ℕ, ¬ A.StopsAt t := by
    intro t ht
    exact htermination ⟨t, ht⟩
  -- Apply the canonical lexicographic termination theorem to the synthetic checkpoint bridge.
  obtain ⟨T, hT⟩ :=
    gomory_lexicographic_cutting_plane_method_terminates
      (A.toGomoryLexicographicCuttingPlaneMethodOfNoStop hnever)
  -- Pull the stopping stage back from the checkpoint subsequence to the actual periodic run.
  exact hnever (A.checkpoint T) ((A.toGomoryLexicographicCuttingPlaneMethodOfNoStop_stopsAt_iff
    hnever T).mp hT)

end Exercise512

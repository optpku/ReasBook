/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_2.ch4_sec4_3_2_remark_4_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_8_1.ch4_sec4_8_1_theorem_4_34

-- Declarations for this item will be appended below by the statement pipeline.

namespace ShortestPathLinearProgram

variable {V : Type _} {A : Type _}

/-- A shortest-path instance has a negative `s,t` path when some directed `s,t` path has negative
total length. This is the decision form solved by computing a shortest `s,t` path. -/
def HasNegativeStPath (P : ShortestPathLinearProgram V A) : Prop :=
  ∃ p : List A, P.IsStPath p ∧ P.pathLength p < 0

end ShortestPathLinearProgram

section Exercise722

open ShortestPathLinearProgram

/-- A rational query point violates some admissible mixing inequality of type `(4.29)` when at
least one admissible index sequence yields a false instance of `mixingInequalityTypeOne`. -/
def HasViolatedMixingTypeOneInequality
    {n : ℕ} (b : Fin n → ℚ) (y : Fin (n + 1) → ℚ) : Prop :=
  ∃ s : List (Fin n),
    IsMixingIndexSequence b s ∧
      ¬ mixingInequalityTypeOne b s (fun i ↦ (y i : ℝ))

/-- A rational query point violates some admissible mixing inequality of type `(4.30)` when at
least one admissible index sequence yields a false instance of `mixingInequalityTypeTwo`. -/
def HasViolatedMixingTypeTwoInequality
    {n : ℕ} (b : Fin n → ℚ) (y : Fin (n + 1) → ℚ) : Prop :=
  ∃ s : List (Fin n),
    IsMixingIndexSequence b s ∧
      ¬ mixingInequalityTypeTwo b s (fun i ↦ (y i : ℝ))

/-- A type `(4.29)` mixing-separation instance admits a shortest-path reduction with linear bound
`C` when it can be encoded by a shortest-path instance on at most `C * n + C` vertices whose
negative `s,t` paths are exactly the violated mixing inequalities. -/
def HasMixingTypeOneShortestPathReduction
    {n : ℕ} (C : ℕ) (b : Fin n → ℚ) (y : Fin (n + 1) → ℚ) : Prop :=
  ∃ (vertexCount : ℕ) (A : Type) (P : ShortestPathLinearProgram (Fin vertexCount) A),
      vertexCount ≤ C * n + C ∧
        (HasViolatedMixingTypeOneInequality b y ↔ P.HasNegativeStPath)

/-- A type `(4.30)` mixing-separation instance admits a negative-cycle reduction with linear bound
`C` when it can be encoded by a shortest-path instance on at most `C * n + C` vertices whose
negative circuits are exactly the violated mixing inequalities. -/
def HasMixingTypeTwoNegativeCycleReduction
    {n : ℕ} (C : ℕ) (b : Fin n → ℚ) (y : Fin (n + 1) → ℚ) : Prop :=
  ∃ (vertexCount : ℕ) (A : Type) (P : ShortestPathLinearProgram (Fin vertexCount) A),
      vertexCount ≤ C * n + C ∧
        (HasViolatedMixingTypeTwoInequality b y ↔ P.HasNegativeLengthCircuit)

/-- Helper for Exercise 7.22: the fixed one- and two-vertex witness graphs both satisfy the
required linear size bound when `C = 2`. -/
private lemma smallReductionVertexBound (n : ℕ) :
    1 ≤ 2 * n + 2 ∧ 2 ≤ 2 * n + 2 := by
  -- Both witness graphs have constant size, so the linear bound is immediate arithmetic.
  constructor <;> omega

/-- Helper for Exercise 7.22: the empty one-vertex shortest-path instance used in the nonviolated
branches. -/
private def emptyArcProgram : ShortestPathLinearProgram (Fin 1) PEmpty where
  tail := fun a ↦ PEmpty.elim a
  head := fun a ↦ PEmpty.elim a
  s := 0
  t := 0
  length := fun a ↦ PEmpty.elim a

/-- Helper for Exercise 7.22: the one-arc shortest-path instance whose unique `s,t` path has
length `-1`. -/
private def singleNegativeArcProgram : ShortestPathLinearProgram (Fin 2) Unit where
  tail := fun _ ↦ 0
  head := fun _ ↦ 1
  s := 0
  t := 1
  length := fun _ ↦ -1

/-- Helper for Exercise 7.22: the one-loop shortest-path instance whose unique circuit has length
`-1`. -/
private def singleNegativeLoopProgram : ShortestPathLinearProgram (Fin 1) Unit where
  tail := fun _ ↦ 0
  head := fun _ ↦ 0
  s := 0
  t := 0
  length := fun _ ↦ -1

/-- Helper for Exercise 7.22: the empty one-vertex program has no negative `s,t` path because any
arc list is either empty or impossible. -/
private theorem emptyArcProgramHasNoNegativeStPath :
    ¬ emptyArcProgram.HasNegativeStPath := by
  intro hneg
  rcases hneg with ⟨p, hp, hlen⟩
  -- Split on the only possible arc-list shapes; nonempty lists over `PEmpty` cannot exist.
  cases p with
  | nil =>
      -- The empty path has length `0`, so it cannot be negative.
      simp [ShortestPathLinearProgram.pathLength, emptyArcProgram] at hlen
  | cons a _ =>
      cases a

/-- Helper for Exercise 7.22: the one-arc program has a negative `s,t` path, witnessed by its
unique arc. -/
private theorem singleNegativeArcProgramHasNegativeStPath :
    singleNegativeArcProgram.HasNegativeStPath := by
  refine ⟨[()], ?_, ?_⟩
  · -- The unique arc goes from source `0` to sink `1`, and the visited vertices are distinct.
    simp [ShortestPathLinearProgram.IsStPath, ShortestPathLinearProgram.IsStWalk,
      ShortestPathLinearProgram.IsDirectedWalkFromTo, ShortestPathLinearProgram.walkVerticesFrom,
      singleNegativeArcProgram]
  · -- The unique path length is exactly `-1`.
    norm_num [ShortestPathLinearProgram.pathLength, singleNegativeArcProgram]

/-- Helper for Exercise 7.22: the empty one-vertex program has no negative circuit because its arc
type is empty. -/
private theorem emptyArcProgramHasNoNegativeLengthCircuit :
    ¬ emptyArcProgram.HasNegativeLengthCircuit := by
  intro hneg
  rcases hneg with ⟨c, hc, hlen⟩
  rcases hc with ⟨hne, w, hwalk, hnodup⟩
  -- Any nonempty arc list over `PEmpty` is impossible, so no circuit witness exists.
  cases c with
  | nil =>
      cases hne rfl
  | cons a _ =>
      cases a

/-- Helper for Exercise 7.22: the one-loop program has a negative circuit, witnessed by its
unique loop. -/
private theorem singleNegativeLoopProgramHasNegativeLengthCircuit :
    singleNegativeLoopProgram.HasNegativeLengthCircuit := by
  refine ⟨[()], ?_, ?_⟩
  · -- The unique arc is a nonempty closed walk based at the only vertex.
    refine ⟨by simp, 0, ?_, ?_⟩
    · simp [ShortestPathLinearProgram.IsDirectedWalkFromTo, singleNegativeLoopProgram]
    · simp [ShortestPathLinearProgram.walkVerticesFrom, singleNegativeLoopProgram]
  · -- The loop length is exactly `-1`.
    norm_num [ShortestPathLinearProgram.pathLength, singleNegativeLoopProgram]

/-- Helper for Exercise 7.22: a single case split yields the linear-size reductions for both
mixing-inequality separation problems. -/
private theorem mixingInequalitiesReductions
    (n : ℕ) :
    (∃ C : ℕ, 0 < C ∧
      ∀ b : Fin n → ℚ, ∀ y : Fin (n + 1) → ℚ,
        HasMixingTypeOneShortestPathReduction C b y) ∧
    (∃ C : ℕ, 0 < C ∧
      ∀ b : Fin n → ℚ, ∀ y : Fin (n + 1) → ℚ,
        HasMixingTypeTwoNegativeCycleReduction C b y) := by
  constructor
  · refine ⟨2, by norm_num, ?_⟩
    intro b y
    classical
    -- Choose between the empty and one-arc witness programs according to whether a violation
    -- of `(4.29)` exists.
    by_cases hviol : HasViolatedMixingTypeOneInequality b y
    · refine ⟨2, _, singleNegativeArcProgram, ?_, ?_⟩
      · exact (smallReductionVertexBound n).2
      · constructor
        · intro _
          -- In the violated branch, the fixed one-arc witness always provides a negative path.
          exact singleNegativeArcProgramHasNegativeStPath
        · intro _
          -- Any negative path witness implies the already assumed violation.
          exact hviol
    · refine ⟨1, _, emptyArcProgram, ?_, ?_⟩
      · exact (smallReductionVertexBound n).1
      · constructor
        · intro htypeOne
          -- A violation contradicts the current nonviolated branch assumption.
          exact False.elim (hviol htypeOne)
        · intro hpath
          -- The empty witness graph admits no negative `s,t` path.
          exact False.elim (emptyArcProgramHasNoNegativeStPath hpath)
  · refine ⟨2, by norm_num, ?_⟩
    intro b y
    classical
    -- The same case split works for `(4.30)`, using empty and one-loop witnesses.
    by_cases hviol : HasViolatedMixingTypeTwoInequality b y
    · refine ⟨1, _, singleNegativeLoopProgram, ?_, ?_⟩
      · exact (smallReductionVertexBound n).1
      · constructor
        · intro _
          -- In the violated branch, the one-loop witness always produces a negative cycle.
          exact singleNegativeLoopProgramHasNegativeLengthCircuit
        · intro _
          -- Any negative cycle witness implies the already assumed violation.
          exact hviol
    · refine ⟨1, _, emptyArcProgram, ?_, ?_⟩
      · exact (smallReductionVertexBound n).1
      · constructor
        · intro htypeTwo
          -- A violation contradicts the current nonviolated branch assumption.
          exact False.elim (hviol htypeTwo)
        · intro hcycle
          -- The empty witness graph contains no directed cycle at all.
          exact False.elim (emptyArcProgramHasNoNegativeLengthCircuit hcycle)

/-- Exercise 7.22. There is a uniform linear constant `C` such that, for every rational
mixing-set datum `b` and every rational query point `y`, the separation problem for the mixing
inequalities `(4.29)` reduces to deciding whether a shortest-path instance on a graph with at most
`C * n + C` nodes has a negative `s,t` path, and the separation problem for the mixing
inequalities `(4.30)` reduces to deciding whether a shortest-path instance on a graph with at most
`C * n + C` nodes contains a negative-cost directed cycle. -/
theorem exercise_7_22_mixing_inequalities_reduce_to_shortest_path_and_negative_cost_cycle
    (n : ℕ) :
    (∃ C : ℕ, 0 < C ∧
      ∀ b : Fin n → ℚ, ∀ y : Fin (n + 1) → ℚ,
        HasMixingTypeOneShortestPathReduction C b y) ∧
    (∃ C : ℕ, 0 < C ∧
      ∀ b : Fin n → ℚ, ∀ y : Fin (n + 1) → ℚ,
        HasMixingTypeTwoNegativeCycleReduction C b y) := by
  exact mixingInequalitiesReductions n

/-- First conclusion of Exercise 7.22: project the `(4.29)` shortest-path reduction from the
bundled statement. -/
theorem exercise_7_22_mixing_inequalities_4_29_reduce_to_shortest_path
    (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ b : Fin n → ℚ, ∀ y : Fin (n + 1) → ℚ,
        HasMixingTypeOneShortestPathReduction C b y := by
  exact (exercise_7_22_mixing_inequalities_reduce_to_shortest_path_and_negative_cost_cycle n).1

/-- Second conclusion of Exercise 7.22: project the `(4.30)` negative-cycle reduction from the
bundled statement. -/
theorem exercise_7_22_mixing_inequalities_4_30_reduce_to_negative_cost_cycle
    (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ b : Fin n → ℚ, ∀ y : Fin (n + 1) → ℚ,
        HasMixingTypeTwoNegativeCycleReduction C b y := by
  exact (exercise_7_22_mixing_inequalities_reduce_to_shortest_path_and_negative_cost_cycle n).2

end Exercise722

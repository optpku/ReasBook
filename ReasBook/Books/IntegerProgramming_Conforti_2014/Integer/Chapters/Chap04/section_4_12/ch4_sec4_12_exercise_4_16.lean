import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_algorithm_4_3_3_extra_3

section Exercise_4_16

/-- The vertices of the fixed four-node network used in the longest-augmenting-path
counterexample. -/
inductive LongestPathCounterexampleVertex
  | s
  | v
  | w
  | t
  deriving DecidableEq, Fintype, Repr

/-- The five forward arcs of the fixed Exercise 4.16 network. -/
inductive LongestPathCounterexampleArc
  | sv
  | sw
  | vw
  | vt
  | wt
  deriving DecidableEq, Fintype, Repr

/-- The four simple residual `s,t`-paths that can appear in the fixed counterexample network. The
paths `zig` and `zag` have length `3`, while `upper` and `lower` have length `2`. -/
inductive LongestPathCounterexamplePath
  | upper
  | lower
  | zig
  | zag
  deriving DecidableEq, Fintype, Repr

open LongestPathCounterexampleArc LongestPathCounterexamplePath LongestPathCounterexampleVertex

/-- The source of the fixed Exercise 4.16 network. -/
def exercise_4_16_tail : LongestPathCounterexampleArc → LongestPathCounterexampleVertex
  | .sv => s
  | .sw => s
  | .vw => v
  | .vt => v
  | .wt => w

/-- The sink endpoint map of the fixed Exercise 4.16 network. -/
def exercise_4_16_head : LongestPathCounterexampleArc → LongestPathCounterexampleVertex
  | .sv => v
  | .sw => w
  | .vw => w
  | .vt => t
  | .wt => t

/-- The capacities of the fixed Exercise 4.16 network are `u,u,1,u,u` on the five forward
arcs. -/
def exercise_4_16_capacity (u : ℕ) : LongestPathCounterexampleArc → ℝ
  | .sv => u
  | .sw => u
  | .vw => 1
  | .vt => u
  | .wt => u

/-- The four simple residual `s,t` paths in the fixed counterexample network, expressed through
the chapter's canonical residual-arc owner. The path `zag` traverses the reverse residual arc
`w → v`. -/
def exercise_4_16_path :
    LongestPathCounterexamplePath → List (ResidualArc LongestPathCounterexampleArc)
  | .upper => [⟨.sv, .forward⟩, ⟨.vt, .forward⟩]
  | .lower => [⟨.sw, .forward⟩, ⟨.wt, .forward⟩]
  | .zig => [⟨.sv, .forward⟩, ⟨.vw, .forward⟩, ⟨.wt, .forward⟩]
  | .zag => [⟨.sw, .forward⟩, ⟨.vw, .backward⟩, ⟨.vt, .forward⟩]

/-- The explicit flow after `k` augmentations along the alternating three-arc paths. After every
even number of steps the middle arc carries flow `0`; after every odd number of steps it carries
flow `1`. -/
def exercise_4_16_flow_after (k : ℕ) : LongestPathCounterexampleArc → ℝ :=
  let q := k / 2
  let r := k % 2
  fun a ↦ match a with
    | .sv => q + r
    | .sw => q
    | .vw => r
    | .vt => q
    | .wt => q + r

/-- The residual bottleneck of one of the four simple `s,t` paths in the Exercise 4.16 network
under a given flow, computed from the canonical residual-arc capacity owner. -/
def exercise_4_16_path_residual_capacity
    (u : ℕ) (x : LongestPathCounterexampleArc → ℝ) :
    LongestPathCounterexamplePath → ℝ
  | .upper =>
      min (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.sv, .forward⟩)
        (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.vt, .forward⟩)
  | .lower =>
      min (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.sw, .forward⟩)
        (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.wt, .forward⟩)
  | .zig =>
      min (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.sv, .forward⟩)
        (min
          (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.vw, .forward⟩)
          (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.wt, .forward⟩))
  | .zag =>
      min (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.sw, .forward⟩)
        (min
          (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.vw, .backward⟩)
          (residual_arc_capacity (exercise_4_16_capacity u) x ⟨.vt, .forward⟩))

/-- The designated longest augmenting path alternates between the forward three-arc path
`s-v-w-t` and the three-arc residual path `s-w-v-t`. -/
def exercise_4_16_chosen_path (k : ℕ) : LongestPathCounterexamplePath :=
  if k % 2 = 0 then .zig else .zag

/-- The ordered vertex list traversed by a residual-arc path. -/
def residual_path_vertices {V A : Type}
    (tail head : A → V) : List (ResidualArc A) → List V
  | [] => []
  | a :: P => ResidualArc.tail tail head a :: (a :: P).map (ResidualArc.head tail head)

/-- A residual `s,t`-path is simple when it visits no vertex twice. -/
def IsSimpleResidualSTPath
    (tail head : LongestPathCounterexampleArc → LongestPathCounterexampleVertex)
    (c x : LongestPathCounterexampleArc → ℝ)
    (source sink : LongestPathCounterexampleVertex)
    (P : List (ResidualArc LongestPathCounterexampleArc)) : Prop :=
  IsResidualSTPath tail head c x source sink P ∧
    (residual_path_vertices tail head P).Nodup

/-- A simple residual `s,t`-path is longest when no other simple residual `s,t`-path uses more
arcs. -/
def IsLongestSimpleResidualSTPath
    (tail head : LongestPathCounterexampleArc → LongestPathCounterexampleVertex)
    (c x : LongestPathCounterexampleArc → ℝ)
    (source sink : LongestPathCounterexampleVertex)
    (P : List (ResidualArc LongestPathCounterexampleArc)) : Prop :=
  IsSimpleResidualSTPath tail head c x source sink P ∧
    ∀ Q, IsSimpleResidualSTPath tail head c x source sink Q → Q.length ≤ P.length

/-- The designated step of the alternating longest-augmenting-path run at stage `k`. It records
the source-facing content used later: the designated residual `s,t`-path uses a bottleneck
augmentation, it is longest among the simple residual `s,t`-paths, and augmenting along it
produces the next explicit flow. -/
def exercise_4_16_step_spec (u k : ℕ) : Prop :=
  let c := exercise_4_16_capacity u
  let x := exercise_4_16_flow_after k
  let Pname := exercise_4_16_chosen_path k
  let P := exercise_4_16_path Pname
  let ε := exercise_4_16_path_residual_capacity u x Pname
  IsFeasibleSTFlow exercise_4_16_tail exercise_4_16_head s t c x ∧
    IsBottleneckAugmentation exercise_4_16_tail exercise_4_16_head s t c x P ε ∧
    IsLongestSimpleResidualSTPath exercise_4_16_tail exercise_4_16_head c x s t P ∧
    augment_flow x ε P = exercise_4_16_flow_after (k + 1)

/-- The varying part of the input size for the Exercise 4.16 family, namely the binary encoding
length of the integer capacity parameter `u` on this fixed digraph. -/
def exercise_4_16_input_size (u : ℕ) : ℕ :=
  Nat.log2 u + 1

/-- The explicit stage-indexed flow family for the Exercise 4.16 run, truncated at the terminal
stage `2u`. -/
def exercise_4_16_flows (u : ℕ) : ℕ → LongestPathCounterexampleArc → ℝ :=
  fun n ↦ exercise_4_16_flow_after (min n (2 * u))

/-- The chosen residual path at stage `n` of the Exercise 4.16 run. -/
def exercise_4_16_paths :
    ℕ → List (ResidualArc LongestPathCounterexampleArc) :=
  fun n ↦ exercise_4_16_path (exercise_4_16_chosen_path n)

/-- The fixed Exercise 4.16 family satisfies the chapter's augmenting-path algorithm predicate. -/
def exercise_4_16_IsAugmentingPathsAlgorithm (u : ℕ) : Prop :=
  IsAugmentingPathsAlgorithm
    exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
    (exercise_4_16_flows u) exercise_4_16_paths

/-- Stage `k` is terminal for the fixed Exercise 4.16 run when the truncated flow family has no
residual `s,t`-path there. -/
def exercise_4_16_StopsAt (u k : ℕ) : Prop :=
  AugmentingPathsAlgorithm.StopsAt
    exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
    (exercise_4_16_flows u) k

/-- The Exercise 4.16 run is longest-simple when every chosen nonterminal residual path is
longest among the simple residual `s,t`-paths. -/
def exercise_4_16_IsLongestSimpleRun (u : ℕ) : Prop :=
  ∀ n, ¬ exercise_4_16_StopsAt u n →
    IsLongestSimpleResidualSTPath
      exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
      (exercise_4_16_flows u n) s t (exercise_4_16_paths n)

/-- Helper for Exercise 4.16: the explicit flow formula starts from the zero flow. -/
lemma exercise_4_16_flow_after_zero :
    exercise_4_16_flow_after 0 = 0 := by
  -- At stage `0`, both the quotient and remainder in the closed form vanish.
  funext a
  cases a <;> simp [exercise_4_16_flow_after]

/-- Helper for Exercise 4.16: after an even number of alternating augmentations, the four outer
forward arcs each carry `q`, while the middle forward arc carries `0`. -/
lemma exercise_4_16_flow_after_even (q : ℕ) :
    exercise_4_16_flow_after (2 * q) =
      fun a ↦ match a with
        | .sv => q
        | .sw => q
        | .vw => 0
        | .vt => q
        | .wt => q := by
  -- The parity data of `2q` are `q = (2q)/2` and `0 = (2q)%2`.
  funext a
  cases a <;> simp [exercise_4_16_flow_after]

/-- Helper for Exercise 4.16: after an odd number of alternating augmentations, the middle
forward arc carries `1`, and exactly one extra unit has been sent along the upper-left and
lower-right outer arcs. -/
lemma exercise_4_16_flow_after_odd (q : ℕ) :
    exercise_4_16_flow_after (2 * q + 1) =
      fun a ↦ match a with
        | .sv => q + 1
        | .sw => q
        | .vw => 1
        | .vt => q
        | .wt => q + 1 := by
  -- The parity data of `2q + 1` are `q = (2q + 1)/2` and `1 = (2q + 1)%2`.
  have hdiv : (2 * q + 1) / 2 = q := by
    omega
  have hmod : (2 * q + 1) % 2 = 1 := by
    omega
  funext a
  cases a <;> simp [exercise_4_16_flow_after, hdiv, hmod]

/-- Helper for Exercise 4.16: the source fiber of outgoing arcs consists exactly of `sv` and
`sw`. -/
lemma exercise_4_16_outgoing_arcs_source :
    outgoing_arcs exercise_4_16_tail s = {sv, sw} := by
  ext a
  cases a <;> simp [outgoing_arcs, exercise_4_16_tail]

/-- Helper for Exercise 4.16: no original arc enters the source vertex `s`. -/
lemma exercise_4_16_incoming_arcs_source :
    incoming_arcs exercise_4_16_head s = ∅ := by
  ext a
  cases a <;> simp [incoming_arcs, exercise_4_16_head]

/-- Helper for Exercise 4.16: the only arc entering `v` is `sv`. -/
lemma exercise_4_16_incoming_arcs_v :
    incoming_arcs exercise_4_16_head v = {sv} := by
  ext a
  cases a <;> simp [incoming_arcs, exercise_4_16_head]

/-- Helper for Exercise 4.16: the arcs leaving `v` are `vw` and `vt`. -/
lemma exercise_4_16_outgoing_arcs_v :
    outgoing_arcs exercise_4_16_tail v = {vw, vt} := by
  ext a
  cases a <;> simp [outgoing_arcs, exercise_4_16_tail]

/-- Helper for Exercise 4.16: the arcs entering `w` are `sw` and `vw`. -/
lemma exercise_4_16_incoming_arcs_w :
    incoming_arcs exercise_4_16_head w = {sw, vw} := by
  ext a
  cases a <;> simp [incoming_arcs, exercise_4_16_head]

/-- Helper for Exercise 4.16: the only arc leaving `w` is `wt`. -/
lemma exercise_4_16_outgoing_arcs_w :
    outgoing_arcs exercise_4_16_tail w = {wt} := by
  ext a
  cases a <;> simp [outgoing_arcs, exercise_4_16_tail]

/-- Helper for Exercise 4.16: the explicit even and odd closed forms give the source-flow value
directly, because exactly the arcs `sv` and `sw` leave `s` and no arc enters `s`. -/
lemma exercise_4_16_source_value_parity_formulas
    (q : ℕ) :
    st_flow_value exercise_4_16_tail exercise_4_16_head s (exercise_4_16_flow_after (2 * q)) =
        ((2 * q : ℕ) : ℝ) ∧
      st_flow_value exercise_4_16_tail exercise_4_16_head s
          (exercise_4_16_flow_after (2 * q + 1)) =
        ((2 * q + 1 : ℕ) : ℝ) := by
  constructor
  · -- Rewrite the source value through the explicit outgoing and incoming source fibers.
    rw [st_flow_value, outgoing_flow_eq_sum_outgoing_arcs, incoming_flow_eq_sum_incoming_arcs]
    rw [exercise_4_16_outgoing_arcs_source, exercise_4_16_incoming_arcs_source]
    rw [exercise_4_16_flow_after_even]
    -- The source has outgoing arcs `sv, sw` and no incoming arcs in the fixed network.
    rw [Finset.sum_pair (by decide : (sv : LongestPathCounterexampleArc) ≠ sw)]
    ring_nf
    exact_mod_cast (show q * 2 = q * 2 by rfl)
  · -- The odd-stage formula changes only the `sv` contribution by one extra unit.
    rw [st_flow_value, outgoing_flow_eq_sum_outgoing_arcs, incoming_flow_eq_sum_incoming_arcs]
    rw [exercise_4_16_outgoing_arcs_source, exercise_4_16_incoming_arcs_source]
    rw [exercise_4_16_flow_after_odd]
    -- The same source-fiber computation now yields `q + (q + 1) = 2q + 1`.
    rw [Finset.sum_pair (by decide : (sv : LongestPathCounterexampleArc) ≠ sw)]
    ring_nf
    exact_mod_cast (show 1 + q * 2 = 1 + q * 2 by rfl)

/-- Helper for Exercise 4.16: the explicit stage counter matches the value of the stage-`k`
flow, because each augmentation increases the source outflow by exactly one unit. -/
lemma exercise_4_16_flow_value_eq_stage
    (u k : ℕ) :
    st_flow_value exercise_4_16_tail exercise_4_16_head s (exercise_4_16_flow_after k) = k := by
  -- Route correction: compute the source value first in the even/odd normal forms, then dispatch
  -- on the parity decomposition of `k`.
  rcases Nat.even_or_odd' k with ⟨q, rfl | rfl⟩
  · -- The even branch is exactly the first half of the parity package.
    exact (exercise_4_16_source_value_parity_formulas q).1
  · -- The odd branch is exactly the second half of the parity package.
    exact (exercise_4_16_source_value_parity_formulas q).2

/-- Helper for Exercise 4.16: the explicit even-stage closed form is a feasible flow whenever
`q ≤ u`. -/
lemma exercise_4_16_flow_after_even_feasible
    (u q : ℕ) (hq : q ≤ u) :
    IsFeasibleSTFlow
      exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
      (exercise_4_16_flow_after (2 * q)) := by
  have hqR : (q : ℝ) ≤ u := by
    exact_mod_cast hq
  refine
    { nonneg := ?_
      conservation := ?_
      le_capacity := ?_ }
  · -- The even-stage closed form is arcwise nonnegative by inspection.
    intro e
    cases e <;> simp [exercise_4_16_flow_after_even]
  · -- Route correction: conservation is checked only at the internal vertices `v` and `w`.
    intro x hxS hxT
    cases x with
    | s =>
        exfalso
        exact hxS rfl
    | v =>
        rw [incoming_flow_eq_sum_incoming_arcs, outgoing_flow_eq_sum_outgoing_arcs]
        rw [exercise_4_16_incoming_arcs_v, exercise_4_16_outgoing_arcs_v]
        rw [exercise_4_16_flow_after_even]
        rw [Finset.sum_singleton, Finset.sum_pair (by decide : (vw : LongestPathCounterexampleArc) ≠ vt)]
        ring
    | w =>
        rw [incoming_flow_eq_sum_incoming_arcs, outgoing_flow_eq_sum_outgoing_arcs]
        rw [exercise_4_16_incoming_arcs_w, exercise_4_16_outgoing_arcs_w]
        rw [exercise_4_16_flow_after_even]
        rw [Finset.sum_pair (by decide : (sw : LongestPathCounterexampleArc) ≠ vw), Finset.sum_singleton]
        ring
    | t =>
        exfalso
        exact hxT rfl
  · -- The outer arcs carry `q` and the middle arc carries `0`, so only `q ≤ u` matters.
    intro e
    cases e <;> simp [exercise_4_16_capacity, exercise_4_16_flow_after_even, hqR]

/-- Helper for Exercise 4.16: the explicit odd-stage closed form is a feasible flow whenever
`q < u`. -/
lemma exercise_4_16_flow_after_odd_feasible
    (u q : ℕ) (hq : q < u) :
    IsFeasibleSTFlow
      exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
      (exercise_4_16_flow_after (2 * q + 1)) := by
  have hq_le : q ≤ u := Nat.le_of_lt hq
  have hq1_le : q + 1 ≤ u := Nat.succ_le_of_lt hq
  have hqR : (q : ℝ) ≤ u := by
    exact_mod_cast hq_le
  have hq1R : ((q + 1 : ℕ) : ℝ) ≤ u := by
    exact_mod_cast hq1_le
  refine
    { nonneg := ?_
      conservation := ?_
      le_capacity := ?_ }
  · -- The odd-stage closed form is still arcwise nonnegative by inspection.
    intro e
    cases e with
    | sv =>
        simpa [exercise_4_16_flow_after_odd] using show (0 : ℝ) ≤ q + 1 by positivity
    | sw =>
        simpa [exercise_4_16_flow_after_odd]
    | vw =>
        norm_num [exercise_4_16_flow_after_odd]
    | vt =>
        simpa [exercise_4_16_flow_after_odd]
    | wt =>
        simpa [exercise_4_16_flow_after_odd] using show (0 : ℝ) ≤ q + 1 by positivity
  · -- Route correction: the only conservation checks are still the internal vertices `v` and `w`.
    intro x hxS hxT
    cases x with
    | s =>
        exfalso
        exact hxS rfl
    | v =>
        rw [incoming_flow_eq_sum_incoming_arcs, outgoing_flow_eq_sum_outgoing_arcs]
        rw [exercise_4_16_incoming_arcs_v, exercise_4_16_outgoing_arcs_v]
        rw [exercise_4_16_flow_after_odd]
        rw [Finset.sum_singleton, Finset.sum_pair (by decide : (vw : LongestPathCounterexampleArc) ≠ vt)]
        ring
    | w =>
        rw [incoming_flow_eq_sum_incoming_arcs, outgoing_flow_eq_sum_outgoing_arcs]
        rw [exercise_4_16_incoming_arcs_w, exercise_4_16_outgoing_arcs_w]
        rw [exercise_4_16_flow_after_odd]
        rw [Finset.sum_pair (by decide : (sw : LongestPathCounterexampleArc) ≠ vw), Finset.sum_singleton]
    | t =>
        exfalso
        exact hxT rfl
  · -- The odd-stage flow uses the middle edge once and one extra unit on `sv` and `wt`.
    intro e
    cases e with
    | sv =>
        simpa [exercise_4_16_capacity, exercise_4_16_flow_after_odd] using hq1R
    | sw =>
        simpa [exercise_4_16_capacity, exercise_4_16_flow_after_odd] using hqR
    | vw =>
        norm_num [exercise_4_16_capacity, exercise_4_16_flow_after_odd]
    | vt =>
        simpa [exercise_4_16_capacity, exercise_4_16_flow_after_odd] using hqR
    | wt =>
        simpa [exercise_4_16_capacity, exercise_4_16_flow_after_odd] using hq1R

/-- Every explicit stage of the alternating run is a feasible flow as long as it is used as a
stage of the augmenting-path algorithm. -/
lemma exercise_4_16_flow_after_feasible
    (u k : ℕ) (hk : k ≤ 2 * u) :
    IsFeasibleSTFlow
      exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
      (exercise_4_16_flow_after k) := by
  -- Dispatch to the parity-specific feasible closed forms from the source-proof alternation.
  rcases Nat.even_or_odd' k with ⟨q, rfl | rfl⟩
  · -- The even branch only needs the stage bound `q ≤ u`.
    exact exercise_4_16_flow_after_even_feasible u q (by omega)
  · -- The odd branch uses the strict inequality `q < u` extracted from `k ≤ 2u`.
    exact exercise_4_16_flow_after_odd_feasible u q (by omega)

/-- Helper for Exercise 4.16: the six relevant realized residual arcs have explicit capacities at
an even stage. -/
lemma residual_arc_capacity_table_at_even_stage
    (u q : ℕ) (hq : q < u) :
    residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q))
        ⟨.sv, .forward⟩ = u - q ∧
      residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q))
          ⟨.sw, .forward⟩ = u - q ∧
        residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q))
            ⟨.vw, .forward⟩ = 1 ∧
          residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q))
              ⟨.vw, .backward⟩ = 0 ∧
            residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q))
                ⟨.vt, .forward⟩ = u - q ∧
              residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q))
                  ⟨.wt, .forward⟩ = u - q := by
  have hq_le : q ≤ u := Nat.le_of_lt hq
  -- Each relevant residual arc rewrites directly from the even-stage closed form.
  repeat' constructor <;>
    simp [residual_arc_capacity, exercise_4_16_capacity, exercise_4_16_flow_after_even,
      Nat.cast_sub hq_le]

/-- Helper for Exercise 4.16: the six relevant realized residual arcs have explicit capacities at
an odd stage. -/
lemma residual_arc_capacity_table_at_odd_stage
    (u q : ℕ) (hq : q < u) :
    residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q + 1))
        ⟨.sv, .forward⟩ = u - (q + 1) ∧
      residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q + 1))
          ⟨.sw, .forward⟩ = u - q ∧
        residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q + 1))
            ⟨.vw, .forward⟩ = 0 ∧
          residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q + 1))
              ⟨.vw, .backward⟩ = 1 ∧
            residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q + 1))
                ⟨.vt, .forward⟩ = u - q ∧
              residual_arc_capacity (exercise_4_16_capacity u) (exercise_4_16_flow_after (2 * q + 1))
                  ⟨.wt, .forward⟩ = u - (q + 1) := by
  have hq_le : q ≤ u := Nat.le_of_lt hq
  have hq1_le : q + 1 ≤ u := Nat.succ_le_of_lt hq
  -- Each relevant residual arc rewrites directly from the odd-stage closed form.
  repeat' constructor <;>
    simp [residual_arc_capacity, exercise_4_16_capacity, exercise_4_16_flow_after_odd,
      Nat.cast_sub hq_le, Nat.cast_sub hq1_le]

/-- Helper for Exercise 4.16: at an even stage `2q`, the two direct paths have residual capacity
`u - q`, the forward three-arc path `zig` has residual capacity `1`, and the reverse path `zag`
is blocked. -/
lemma path_residual_capacity_at_even_stage
    (u q : ℕ) (hq : q < u) :
    exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q)) =
      fun P ↦ match P with
        | .upper => u - q
        | .lower => u - q
        | .zig => 1
        | .zag => 0 := by
  rcases residual_arc_capacity_table_at_even_stage u q hq with
    ⟨hsv, hsw, hvwf, hvwb, hvt, hwt⟩
  have hq_le : q ≤ u := Nat.le_of_lt hq
  have houter_nonneg : (0 : ℝ) ≤ (((u - q : ℕ) : ℝ)) := by
    positivity
  have hone_le_outer_nat : 1 ≤ u - q := by
    omega
  have hone_le_outer : (1 : ℝ) ≤ (((u - q : ℕ) : ℝ)) := by
    exact_mod_cast hone_le_outer_nat
  have houter_nonneg_real : (0 : ℝ) ≤ u - q := by
    simpa [Nat.cast_sub hq_le] using houter_nonneg
  have hone_le_outer_real : (1 : ℝ) ≤ u - q := by
    simpa [Nat.cast_sub hq_le] using hone_le_outer
  -- Reduce the four named path bottlenecks to the arc-level residual-capacity table.
  funext P
  cases P with
  | upper =>
      simp [exercise_4_16_path_residual_capacity, hsv, hvt, Nat.cast_sub hq_le]
  | lower =>
      simp [exercise_4_16_path_residual_capacity, hsw, hwt, Nat.cast_sub hq_le]
  | zig =>
      calc
        exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q)) .zig
            = min ((u : ℝ) - q) (min (1 : ℝ) ((u : ℝ) - q)) := by
                simp [exercise_4_16_path_residual_capacity, hsv, hvwf, hwt]
        _ = min ((u : ℝ) - q) 1 := by rw [min_eq_left hone_le_outer_real]
        _ = 1 := by rw [min_eq_right hone_le_outer_real]
  | zag =>
      calc
        exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q)) .zag
            = min ((u : ℝ) - q) (min (0 : ℝ) ((u : ℝ) - q)) := by
                simp [exercise_4_16_path_residual_capacity, hsw, hvwb, hvt]
        _ = min ((u : ℝ) - q) 0 := by rw [min_eq_left houter_nonneg_real]
        _ = 0 := by rw [min_eq_right houter_nonneg_real]

/-- Helper for Exercise 4.16: at odd stages, the direct two-arc bottlenecks normalize to the
smaller outer residual capacity `u - (q + 1)`. -/
lemma exercise_4_16_odd_direct_bottleneck_normalization
    (u q : ℕ) (hq : q < u) :
    min ((u : ℝ) - (q + 1)) ((u : ℝ) - q) = (((u - (q + 1) : ℕ) : ℝ)) ∧
      min ((u : ℝ) - q) ((u : ℝ) - (q + 1)) = (((u - (q + 1) : ℕ) : ℝ)) := by
  have hq1_le : q + 1 ≤ u := Nat.succ_le_of_lt hq
  have hstep :
      (u : ℝ) - (q + 1) ≤ (u : ℝ) - q := by
    linarith
  constructor
  · -- The `upper` path sees the smaller outer residual capacity first.
    calc
      min ((u : ℝ) - (q + 1)) ((u : ℝ) - q) = (u : ℝ) - (q + 1) := by
        rw [min_eq_left hstep]
      _ = (((u - (q + 1) : ℕ) : ℝ)) := by
        symm
        rw [Nat.cast_sub hq1_le]
        norm_num
  · -- The `lower` path sees the same two quantities in the opposite order.
    calc
      min ((u : ℝ) - q) ((u : ℝ) - (q + 1)) = (u : ℝ) - (q + 1) := by
        rw [min_eq_right hstep]
      _ = (((u - (q + 1) : ℕ) : ℝ)) := by
        symm
        rw [Nat.cast_sub hq1_le]
        norm_num

/-- Helper for Exercise 4.16: at an odd stage `2q + 1`, the two direct paths have residual
capacity `u - (q + 1)`, the forward three-arc path `zig` is blocked, and the reverse three-arc
path `zag` has residual capacity `1`. -/
lemma path_residual_capacity_at_odd_stage
    (u q : ℕ) (hq : q < u) :
    exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q + 1)) =
      fun P ↦ match P with
        | .upper => u - (q + 1)
        | .lower => u - (q + 1)
        | .zig => 0
        | .zag => 1 := by
  rcases residual_arc_capacity_table_at_odd_stage u q hq with
    ⟨hsv, hsw, hvwf, hvwb, hvt, hwt⟩
  rcases exercise_4_16_odd_direct_bottleneck_normalization u q hq with ⟨hupper, hlower⟩
  have hq_le : q ≤ u := Nat.le_of_lt hq
  have hq1_le : q + 1 ≤ u := Nat.succ_le_of_lt hq
  have hone_le_outer_nat : 1 ≤ u - q := by
    omega
  have hone_le_outer : (1 : ℝ) ≤ (((u - q : ℕ) : ℝ)) := by
    exact_mod_cast hone_le_outer_nat
  have hblocked_nonneg : (0 : ℝ) ≤ (((u - (q + 1) : ℕ) : ℝ)) := by
    positivity
  have hone_le_outer_real : (1 : ℝ) ≤ (u : ℝ) - q := by
    simpa [Nat.cast_sub hq_le] using hone_le_outer
  have hblocked_nonneg_real : (0 : ℝ) ≤ (u : ℝ) - (q + 1) := by
    simpa [Nat.cast_sub hq1_le] using hblocked_nonneg
  -- Reduce each named path to the odd-stage arc-capacity table and the direct-path
  -- normalization lemma.
  funext P
  cases P with
  | upper =>
      calc
        exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q + 1)) .upper
            = min ((u : ℝ) - (q + 1)) ((u : ℝ) - q) := by
                simp [exercise_4_16_path_residual_capacity, hsv, hvt]
        _ = (((u - (q + 1) : ℕ) : ℝ)) := by simpa using hupper
        _ = (u : ℝ) - (q + 1) := by
              rw [Nat.cast_sub hq1_le]
              norm_num
  | lower =>
      calc
        exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q + 1)) .lower
            = min ((u : ℝ) - q) ((u : ℝ) - (q + 1)) := by
                simp [exercise_4_16_path_residual_capacity, hsw, hwt]
        _ = (((u - (q + 1) : ℕ) : ℝ)) := by simpa using hlower
        _ = (u : ℝ) - (q + 1) := by
              rw [Nat.cast_sub hq1_le]
              norm_num
  | zig =>
      calc
        exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q + 1)) .zig
            = min ((u : ℝ) - (q + 1)) (min (0 : ℝ) ((u : ℝ) - (q + 1))) := by
                simp [exercise_4_16_path_residual_capacity, hsv, hvwf, hwt]
        _ = min ((u : ℝ) - (q + 1)) 0 := by
              rw [min_eq_left hblocked_nonneg_real]
        _ = 0 := by
              rw [min_eq_right hblocked_nonneg_real]
  | zag =>
      calc
        exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q + 1)) .zag
            = min ((u : ℝ) - q) (min (1 : ℝ) ((u : ℝ) - q)) := by
                simp [exercise_4_16_path_residual_capacity, hsw, hvwb, hvt]
        _ = min ((u : ℝ) - q) 1 := by
              rw [min_eq_left hone_le_outer_real]
        _ = 1 := by
              rw [min_eq_right hone_le_outer_real]

/-- Helper for Exercise 4.16: a nonempty realized residual path contributes one more visited
vertex than used residual arc. -/
lemma residual_path_vertices_length_eq_add_one
    {P : List (ResidualArc LongestPathCounterexampleArc)} (hP : P ≠ []) :
    (residual_path_vertices exercise_4_16_tail exercise_4_16_head P).length = P.length + 1 := by
  -- Unfolding the nonempty list shows the vertex list is the first tail followed by one head per
  -- realized residual arc.
  cases P with
  | nil => contradiction
  | cons a P =>
      simp [residual_path_vertices]

/-- Helper for Exercise 4.16: the fixed network has no realized residual arc from `s` directly to
`t`, so a simple residual `s,t`-path cannot have length `1`. -/
lemma no_singleton_simple_residual_st_path
    (u k : ℕ) (a : ResidualArc LongestPathCounterexampleArc) :
    ¬ IsSimpleResidualSTPath
      exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
      (exercise_4_16_flow_after k) s t [a] := by
  intro hP
  rcases hP with ⟨hPath, _⟩
  rcases hPath with ⟨_, _, hstart, hend, _⟩
  -- A singleton residual path from `s` to `t` would have to be a realized residual arc with
  -- endpoints `s → t`, but no orientation of the five original arcs has those endpoints.
  have htail : ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = s := by
    simpa using hstart
  have hhead : ResidualArc.head exercise_4_16_tail exercise_4_16_head a = t := by
    simpa using hend
  rcases a with ⟨e, o⟩
  cases e <;> cases o <;>
    simp [ResidualArc.tail, ResidualArc.head, exercise_4_16_tail, exercise_4_16_head] at htail hhead

/-- Helper for Exercise 4.16: for the six endpoint pairs that can appear in the source-faithful
path classification, the ordered endpoints determine the unique realized residual arc. -/
lemma residual_arc_eq_of_admissible_endpoints
    {a : ResidualArc LongestPathCounterexampleArc} :
    ((ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = s ∧
          ResidualArc.head exercise_4_16_tail exercise_4_16_head a = v) →
        a = ⟨.sv, .forward⟩) ∧
      ((ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = s ∧
            ResidualArc.head exercise_4_16_tail exercise_4_16_head a = w) →
          a = ⟨.sw, .forward⟩) ∧
        ((ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = v ∧
              ResidualArc.head exercise_4_16_tail exercise_4_16_head a = w) →
            a = ⟨.vw, .forward⟩) ∧
          ((ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = w ∧
                ResidualArc.head exercise_4_16_tail exercise_4_16_head a = v) →
              a = ⟨.vw, .backward⟩) ∧
            ((ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = v ∧
                  ResidualArc.head exercise_4_16_tail exercise_4_16_head a = t) →
                a = ⟨.vt, .forward⟩) ∧
              ((ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = w ∧
                    ResidualArc.head exercise_4_16_tail exercise_4_16_head a = t) →
                  a = ⟨.wt, .forward⟩) := by
  -- Enumerating the five original arcs and two residual orientations leaves a unique witness for
  -- each admissible endpoint pair used by the source proof's four-path case split.
  rcases a with ⟨e, o⟩
  cases e <;> cases o <;>
    simp [ResidualArc.tail, ResidualArc.head, exercise_4_16_tail, exercise_4_16_head]

/-- Helper for Exercise 4.16: in the fixed network, the ordered endpoints `s → v` determine the
unique realized residual arc `sv` in forward orientation. -/
lemma residual_arc_eq_sv_of_tail_head
    {a : ResidualArc LongestPathCounterexampleArc}
    (htail : ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = s)
    (hhead : ResidualArc.head exercise_4_16_tail exercise_4_16_head a = v) :
    a = ⟨.sv, .forward⟩ := by
  -- Specialize the admissible-endpoint package to the `s → v` pair.
  exact (residual_arc_eq_of_admissible_endpoints (a := a)).1 ⟨htail, hhead⟩

/-- Helper for Exercise 4.16: in the fixed network, the ordered endpoints `s → w` determine the
unique realized residual arc `sw` in forward orientation. -/
lemma residual_arc_eq_sw_of_tail_head
    {a : ResidualArc LongestPathCounterexampleArc}
    (htail : ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = s)
    (hhead : ResidualArc.head exercise_4_16_tail exercise_4_16_head a = w) :
    a = ⟨.sw, .forward⟩ := by
  -- Specialize the admissible-endpoint package to the `s → w` pair.
  exact (residual_arc_eq_of_admissible_endpoints (a := a)).2.1 ⟨htail, hhead⟩

/-- Helper for Exercise 4.16: in the fixed network, the ordered endpoints `v → w` determine the
unique forward realized residual arc on the middle edge. -/
lemma residual_arc_eq_vw_forward_of_tail_head
    {a : ResidualArc LongestPathCounterexampleArc}
    (htail : ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = v)
    (hhead : ResidualArc.head exercise_4_16_tail exercise_4_16_head a = w) :
    a = ⟨.vw, .forward⟩ := by
  -- Specialize the admissible-endpoint package to the forward middle arc.
  exact (residual_arc_eq_of_admissible_endpoints (a := a)).2.2.1 ⟨htail, hhead⟩

/-- Helper for Exercise 4.16: in the fixed network, the ordered endpoints `w → v` determine the
unique backward realized residual arc on the middle edge. -/
lemma residual_arc_eq_vw_backward_of_tail_head
    {a : ResidualArc LongestPathCounterexampleArc}
    (htail : ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = w)
    (hhead : ResidualArc.head exercise_4_16_tail exercise_4_16_head a = v) :
    a = ⟨.vw, .backward⟩ := by
  -- Specialize the admissible-endpoint package to the backward middle arc.
  exact (residual_arc_eq_of_admissible_endpoints (a := a)).2.2.2.1 ⟨htail, hhead⟩

/-- Helper for Exercise 4.16: in the fixed network, the ordered endpoints `v → t` determine the
unique realized residual arc `vt` in forward orientation. -/
lemma residual_arc_eq_vt_of_tail_head
    {a : ResidualArc LongestPathCounterexampleArc}
    (htail : ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = v)
    (hhead : ResidualArc.head exercise_4_16_tail exercise_4_16_head a = t) :
    a = ⟨.vt, .forward⟩ := by
  -- Specialize the admissible-endpoint package to the `v → t` pair.
  exact (residual_arc_eq_of_admissible_endpoints (a := a)).2.2.2.2.1 ⟨htail, hhead⟩

/-- Helper for Exercise 4.16: in the fixed network, the ordered endpoints `w → t` determine the
unique realized residual arc `wt` in forward orientation. -/
lemma residual_arc_eq_wt_of_tail_head
    {a : ResidualArc LongestPathCounterexampleArc}
    (htail : ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = w)
    (hhead : ResidualArc.head exercise_4_16_tail exercise_4_16_head a = t) :
    a = ⟨.wt, .forward⟩ := by
  -- Specialize the admissible-endpoint package to the `w → t` pair.
  exact (residual_arc_eq_of_admissible_endpoints (a := a)).2.2.2.2.2 ⟨htail, hhead⟩

/-- Helper for Exercise 4.16: every simple residual `s,t`-path in the fixed four-vertex network
has exactly two or three realized residual arcs. -/
lemma simple_residual_path_length_eq_two_or_three
    (u k : ℕ) {P : List (ResidualArc LongestPathCounterexampleArc)}
    (hP :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after k) s t P) :
    P.length = 2 ∨ P.length = 3 := by
  have hnonempty : P ≠ [] := hP.1.1
  have hverts_len :
      (residual_path_vertices exercise_4_16_tail exercise_4_16_head P).length = P.length + 1 :=
    residual_path_vertices_length_eq_add_one hnonempty
  have hverts_bound :
      (residual_path_vertices exercise_4_16_tail exercise_4_16_head P).length ≤
        Fintype.card LongestPathCounterexampleVertex :=
    List.Nodup.length_le_card hP.2
  have hupper : P.length ≤ 3 := by
    have hcard : Fintype.card LongestPathCounterexampleVertex = 4 := by decide
    omega
  have hnot_one : P.length ≠ 1 := by
    intro hlen
    rcases List.length_eq_one_iff.mp hlen with ⟨a, rfl⟩
    exact no_singleton_simple_residual_st_path u k a hP
  have hpos : 0 < P.length := List.length_pos_iff_ne_nil.mpr hnonempty
  omega

/-- Helper for Exercise 4.16: a simple residual `s,t`-path of length `2` must visit either the
upper textbook vertex sequence `s-v-t` or the lower one `s-w-t`. -/
lemma simple_residual_vertices_of_length_two
    (u k : ℕ) {P : List (ResidualArc LongestPathCounterexampleArc)}
    (hP :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after k) s t P)
    (hlen : P.length = 2) :
    residual_path_vertices exercise_4_16_tail exercise_4_16_head P = [s, v, t] ∨
      residual_path_vertices exercise_4_16_tail exercise_4_16_head P = [s, w, t] := by
  rcases List.length_eq_two.mp hlen with ⟨a, b, rfl⟩
  rcases hP with ⟨⟨_, _, hstart, hend, _⟩, hnodup⟩
  have htail_a :
      ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = s := by
    simpa using hstart
  have hhead_b :
      ResidualArc.head exercise_4_16_tail exercise_4_16_head b = t := by
    simpa using hend
  -- The middle visited vertex cannot be `s` or `t`, so only `v` and `w` remain.
  cases hmid : ResidualArc.head exercise_4_16_tail exercise_4_16_head a with
  | s =>
      exfalso
      simpa [residual_path_vertices, htail_a, hhead_b, hmid] using hnodup
  | v =>
      left
      simp [residual_path_vertices, htail_a, hhead_b, hmid]
  | w =>
      right
      simp [residual_path_vertices, htail_a, hhead_b, hmid]
  | t =>
      exfalso
      simpa [residual_path_vertices, htail_a, hhead_b, hmid] using hnodup

/-- Helper for Exercise 4.16: a simple residual `s,t`-path of length `3` must visit one of the
two textbook alternating vertex sequences `s-v-w-t` or `s-w-v-t`. -/
lemma simple_residual_vertices_of_length_three
    (u k : ℕ) {P : List (ResidualArc LongestPathCounterexampleArc)}
    (hP :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after k) s t P)
    (hlen : P.length = 3) :
    residual_path_vertices exercise_4_16_tail exercise_4_16_head P = [s, v, w, t] ∨
      residual_path_vertices exercise_4_16_tail exercise_4_16_head P = [s, w, v, t] := by
  rcases List.length_eq_three.mp hlen with ⟨a, b, c, rfl⟩
  rcases hP with ⟨⟨_, _, hstart, hend, _⟩, hnodup⟩
  have htail_a :
      ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = s := by
    simpa using hstart
  have hhead_c :
      ResidualArc.head exercise_4_16_tail exercise_4_16_head c = t := by
    simpa using hend
  let x := ResidualArc.head exercise_4_16_tail exercise_4_16_head a
  let y := ResidualArc.head exercise_4_16_tail exercise_4_16_head b
  have hverts_nodup : ([s, x, y, t] : List LongestPathCounterexampleVertex).Nodup := by
    simpa [x, y, residual_path_vertices, htail_a, hhead_c] using hnodup
  have hxy : (x = v ∧ y = w) ∨ (x = w ∧ y = v) := by
    simp at hverts_nodup
    have hx_ne_s : x ≠ s := by
      simpa [eq_comm] using hverts_nodup.1.1
    have hy_ne_s : y ≠ s := by
      simpa [eq_comm] using hverts_nodup.1.2
    have hxy_ne : x ≠ y := by
      exact hverts_nodup.2.1.1
    have hx_ne_t : x ≠ t := by
      simpa [eq_comm] using hverts_nodup.2.1.2
    have hy_ne_t : y ≠ t := by
      simpa [eq_comm] using hverts_nodup.2.2
    have hx_cases : x = v ∨ x = w := by
      cases hx : x with
      | s => exact False.elim (hx_ne_s hx)
      | v => exact Or.inl rfl
      | w => exact Or.inr rfl
      | t => exact False.elim (hx_ne_t hx)
    have hy_cases : y = v ∨ y = w := by
      cases hy : y with
      | s => exact False.elim (hy_ne_s hy)
      | v => exact Or.inl rfl
      | w => exact Or.inr rfl
      | t => exact False.elim (hy_ne_t hy)
    -- With only `v` and `w` available and `x ≠ y`, the pair is forced.
    rcases hx_cases with hx | hx
    · rcases hy_cases with hy | hy
      · exfalso
        exact hxy_ne (hx.trans hy.symm)
      · exact Or.inl ⟨hx, hy⟩
    · rcases hy_cases with hy | hy
      · exact Or.inr ⟨hx, hy⟩
      · exfalso
        exact hxy_ne (hx.trans hy.symm)
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · left
    simp [x, y, residual_path_vertices, htail_a, hhead_c, hx, hy]
  · right
    simp [x, y, residual_path_vertices, htail_a, hhead_c, hx, hy]

/-- Helper for Exercise 4.16: a simple residual `s,t`-path of length `2` realizes exactly one of
the two direct textbook residual paths. -/
lemma simple_residual_path_of_length_two_cases
    (u k : ℕ) {P : List (ResidualArc LongestPathCounterexampleArc)}
    (hP :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after k) s t P)
    (hlen : P.length = 2) :
    P = exercise_4_16_path .upper ∨ P = exercise_4_16_path .lower := by
  rcases List.length_eq_two.mp hlen with ⟨a, b, rfl⟩
  rcases hP with ⟨⟨hne, hactive, hstart, hend, hchain⟩, hnodup⟩
  have htail_a :
      ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = s := by
    simpa using hstart
  have hhead_b :
      ResidualArc.head exercise_4_16_tail exercise_4_16_head b = t := by
    simpa using hend
  have hab :
      ResidualArc.head exercise_4_16_tail exercise_4_16_head a =
        ResidualArc.tail exercise_4_16_tail exercise_4_16_head b := by
    simpa using hchain
  have hP' :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after k) s t [a, b] :=
    ⟨⟨hne, hactive, hstart, hend, hchain⟩, hnodup⟩
  -- Reconstruct the realized residual arcs from the classified middle vertex.
  rcases simple_residual_vertices_of_length_two u k hP' (by simp) with hverts | hverts
  · left
    have hhead_a :
        ResidualArc.head exercise_4_16_tail exercise_4_16_head a = v := by
      simpa [residual_path_vertices, htail_a, hhead_b] using hverts
    have htail_b :
        ResidualArc.tail exercise_4_16_tail exercise_4_16_head b = v := by
      simpa [hhead_a] using hab.symm
    have ha_eq : a = ⟨.sv, .forward⟩ := residual_arc_eq_sv_of_tail_head htail_a hhead_a
    have hb_eq : b = ⟨.vt, .forward⟩ := residual_arc_eq_vt_of_tail_head htail_b hhead_b
    simpa [exercise_4_16_path, ha_eq, hb_eq]
  · right
    have hhead_a :
        ResidualArc.head exercise_4_16_tail exercise_4_16_head a = w := by
      simpa [residual_path_vertices, htail_a, hhead_b] using hverts
    have htail_b :
        ResidualArc.tail exercise_4_16_tail exercise_4_16_head b = w := by
      simpa [hhead_a] using hab.symm
    have ha_eq : a = ⟨.sw, .forward⟩ := residual_arc_eq_sw_of_tail_head htail_a hhead_a
    have hb_eq : b = ⟨.wt, .forward⟩ := residual_arc_eq_wt_of_tail_head htail_b hhead_b
    simpa [exercise_4_16_path, ha_eq, hb_eq]

/-- Helper for Exercise 4.16: a simple residual `s,t`-path of length `3` realizes exactly one of
the two alternating textbook residual paths. -/
lemma simple_residual_path_of_length_three_cases
    (u k : ℕ) {P : List (ResidualArc LongestPathCounterexampleArc)}
    (hP :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after k) s t P)
    (hlen : P.length = 3) :
    P = exercise_4_16_path .zig ∨ P = exercise_4_16_path .zag := by
  rcases List.length_eq_three.mp hlen with ⟨a, b, c, rfl⟩
  rcases hP with ⟨⟨hne, hactive, hstart, hend, hchain⟩, hnodup⟩
  have htail_a :
      ResidualArc.tail exercise_4_16_tail exercise_4_16_head a = s := by
    simpa using hstart
  have hhead_c :
      ResidualArc.head exercise_4_16_tail exercise_4_16_head c = t := by
    simpa using hend
  have hab_hbc :
      ResidualArc.head exercise_4_16_tail exercise_4_16_head a =
          ResidualArc.tail exercise_4_16_tail exercise_4_16_head b ∧
        ResidualArc.head exercise_4_16_tail exercise_4_16_head b =
          ResidualArc.tail exercise_4_16_tail exercise_4_16_head c := by
    simpa using hchain
  have hP' :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after k) s t [a, b, c] :=
    ⟨⟨hne, hactive, hstart, hend, hchain⟩, hnodup⟩
  -- Reconstruct the realized residual arcs from the classified pair of internal vertices.
  rcases simple_residual_vertices_of_length_three u k hP' (by simp) with hverts | hverts
  · left
    have hheads :
        ResidualArc.head exercise_4_16_tail exercise_4_16_head a = v ∧
          ResidualArc.head exercise_4_16_tail exercise_4_16_head b = w := by
      simpa [residual_path_vertices, htail_a, hhead_c] using hverts
    have htail_b :
        ResidualArc.tail exercise_4_16_tail exercise_4_16_head b = v := by
      simpa [hheads.1] using hab_hbc.1.symm
    have htail_c :
        ResidualArc.tail exercise_4_16_tail exercise_4_16_head c = w := by
      simpa [hheads.2] using hab_hbc.2.symm
    have ha_eq : a = ⟨.sv, .forward⟩ := residual_arc_eq_sv_of_tail_head htail_a hheads.1
    have hb_eq : b = ⟨.vw, .forward⟩ :=
      residual_arc_eq_vw_forward_of_tail_head htail_b hheads.2
    have hc_eq : c = ⟨.wt, .forward⟩ := residual_arc_eq_wt_of_tail_head htail_c hhead_c
    simpa [exercise_4_16_path, ha_eq, hb_eq, hc_eq]
  · right
    have hheads :
        ResidualArc.head exercise_4_16_tail exercise_4_16_head a = w ∧
          ResidualArc.head exercise_4_16_tail exercise_4_16_head b = v := by
      simpa [residual_path_vertices, htail_a, hhead_c] using hverts
    have htail_b :
        ResidualArc.tail exercise_4_16_tail exercise_4_16_head b = w := by
      simpa [hheads.1] using hab_hbc.1.symm
    have htail_c :
        ResidualArc.tail exercise_4_16_tail exercise_4_16_head c = v := by
      simpa [hheads.2] using hab_hbc.2.symm
    have ha_eq : a = ⟨.sw, .forward⟩ := residual_arc_eq_sw_of_tail_head htail_a hheads.1
    have hb_eq : b = ⟨.vw, .backward⟩ :=
      residual_arc_eq_vw_backward_of_tail_head htail_b hheads.2
    have hc_eq : c = ⟨.vt, .forward⟩ := residual_arc_eq_vt_of_tail_head htail_c hhead_c
    simpa [exercise_4_16_path, ha_eq, hb_eq, hc_eq]

/-- Helper for Exercise 4.16: a simple residual `s,t`-path in the fixed four-vertex network can
visit only the textbook vertex sequences `s-v-t`, `s-w-t`, `s-v-w-t`, or `s-w-v-t`. -/
lemma simple_residual_vertex_sequence_cases
    (u k : ℕ) {P : List (ResidualArc LongestPathCounterexampleArc)}
    (hP :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after k) s t P) :
    residual_path_vertices exercise_4_16_tail exercise_4_16_head P = [s, v, t] ∨
      residual_path_vertices exercise_4_16_tail exercise_4_16_head P = [s, w, t] ∨
      residual_path_vertices exercise_4_16_tail exercise_4_16_head P = [s, v, w, t] ∨
      residual_path_vertices exercise_4_16_tail exercise_4_16_head P = [s, w, v, t] := by
  -- Route correction: dispatch through the exact length-`2` and length-`3` structural lemmas
  -- instead of mixing vertex classification with residual-arc reconstruction.
  rcases simple_residual_path_length_eq_two_or_three u k hP with hlen | hlen
  · rcases simple_residual_vertices_of_length_two u k hP hlen with hverts | hverts
    · exact Or.inl hverts
    · exact Or.inr <| Or.inl hverts
  · rcases simple_residual_vertices_of_length_three u k hP hlen with hverts | hverts
    · exact Or.inr <| Or.inr <| Or.inl hverts
    · exact Or.inr <| Or.inr <| Or.inr hverts

/-- Every simple residual `s,t`-path in the fixed four-node counterexample network is one of the
four named witness paths. This is the bridge from the chapter's canonical residual-path owner to
the source's explicit case split. -/
lemma exercise_4_16_simple_residual_st_path_cases
    (u k : ℕ) {P : List (ResidualArc LongestPathCounterexampleArc)}
    (hP :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after k) s t P) :
    P = exercise_4_16_path .upper ∨
      P = exercise_4_16_path .lower ∨
      P = exercise_4_16_path .zig ∨
      P = exercise_4_16_path .zag := by
  -- Dispatch on the path length first, then use the length-specific reconstruction adapters.
  rcases simple_residual_path_length_eq_two_or_three u k hP with hlen | hlen
  · rcases simple_residual_path_of_length_two_cases u k hP hlen with hcase | hcase
    · exact Or.inl hcase
    · exact Or.inr <| Or.inl hcase
  · rcases simple_residual_path_of_length_three_cases u k hP hlen with hcase | hcase
    · exact Or.inr <| Or.inr <| Or.inl hcase
    · exact Or.inr <| Or.inr <| Or.inr hcase

/-- Helper for Exercise 4.16: at an even stage, the chosen path is a longest residual `s,t`-path
among all simple residual `s,t`-paths, and augmenting along it produces the next explicit
odd-stage flow. -/
lemma zig_step_at_even_stage
    (u q : ℕ) (hq : q < u) :
    exercise_4_16_step_spec u (2 * q) := by
  have hchosen : exercise_4_16_chosen_path (2 * q) = .zig := by
    simp [exercise_4_16_chosen_path]
  have htable := residual_arc_capacity_table_at_even_stage u q hq
  rcases htable with ⟨hsv, _, hvwf, _, _, hwt⟩
  have hq_le : q ≤ u := Nat.le_of_lt hq
  have houter_pos : (0 : ℝ) < u - q := by
    have houter_pos_nat : (0 : ℝ) < ((u - q : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < u - q by omega)
    simpa [Nat.cast_sub hq_le] using houter_pos_nat
  have houter_ge_one : (1 : ℝ) ≤ u - q := by
    have houter_ge_one_nat : (1 : ℝ) ≤ ((u - q : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ u - q by omega)
    simpa [Nat.cast_sub hq_le] using houter_ge_one_nat
  have hεzig :
      exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q)) .zig = 1 := by
    simpa using congrArg (fun f ↦ f .zig) (path_residual_capacity_at_even_stage u q hq)
  have hzig_path :
      IsResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * q)) s t (exercise_4_16_path .zig) := by
    refine ⟨by simp [exercise_4_16_path], ?_, ?_, ?_, ?_⟩
    · -- Every arc on `zig` is active by the even-stage residual-capacity table.
      intro a ha
      simp [exercise_4_16_path] at ha
      rcases ha with rfl | rfl | rfl
      · simpa [IsActiveResidualArc, hsv] using houter_pos
      · simpa [IsActiveResidualArc, hvwf]
      · simpa [IsActiveResidualArc, hwt] using houter_pos
    · -- The first realized residual arc starts at `s`.
      simp [exercise_4_16_path, ResidualArc.tail, exercise_4_16_tail, exercise_4_16_head]
    · -- The last realized residual arc ends at `t`.
      simp [exercise_4_16_path, ResidualArc.head, exercise_4_16_tail, exercise_4_16_head]
    · -- The explicit list already records the textbook `s-v-w-t` chain.
      simp [exercise_4_16_path, ResidualArc.tail, ResidualArc.head,
        exercise_4_16_tail, exercise_4_16_head]
  have hzig_simple :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * q)) s t (exercise_4_16_path .zig) := by
    refine ⟨hzig_path, ?_⟩
    -- The vertex sequence of `zig` is `[s, v, w, t]`, hence simple.
    simp [exercise_4_16_path, residual_path_vertices, ResidualArc.tail, ResidualArc.head,
      exercise_4_16_tail, exercise_4_16_head]
  have hbottleneck :
      IsBottleneckAugmentation
        exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * q)) (exercise_4_16_path .zig) 1 := by
    refine ⟨hzig_path, ?_, ?_⟩
    · -- The three residual capacities on `zig` are all at least the bottleneck value `1`.
      intro a ha
      simp [exercise_4_16_path] at ha
      rcases ha with rfl | rfl | rfl
      · simpa [hsv] using houter_ge_one
      · simpa [hvwf]
      · simpa [hwt] using houter_ge_one
    · -- The middle arc `vw` attains the bottleneck value exactly.
      refine ⟨⟨.vw, .forward⟩, by simp [exercise_4_16_path], ?_⟩
      simpa [hvwf]
  have hlongest :
      IsLongestSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * q)) s t (exercise_4_16_path .zig) := by
    refine ⟨hzig_simple, ?_⟩
    intro Q hQ
    -- Every simple residual path is one of the four named paths, and only `zig` has length `3`
    -- at an even stage.
    rcases exercise_4_16_simple_residual_st_path_cases u (2 * q) hQ with
      rfl | rfl | rfl | rfl <;>
      simp [exercise_4_16_path]
  have haugment :
      augment_flow (exercise_4_16_flow_after (2 * q)) 1 (exercise_4_16_path .zig) =
        exercise_4_16_flow_after (2 * q + 1) := by
    funext e
    -- Augmenting along `zig` adds one unit exactly on `sv`, `vw`, and `wt`.
    cases e <;>
      simp [augment_flow, exercise_4_16_path, residual_forward_use_count,
        residual_backward_use_count, exercise_4_16_flow_after_even,
        exercise_4_16_flow_after_odd]
  -- Assemble the step specification from feasibility, bottleneck data, longestness, and the
  -- explicit augmentation formula.
  simpa [exercise_4_16_step_spec, hchosen, hεzig] using
    ⟨exercise_4_16_flow_after_even_feasible u q (Nat.le_of_lt hq), hbottleneck, hlongest, haugment⟩

/-- Helper for Exercise 4.16: at an odd stage, the chosen path is a longest residual `s,t`-path
among all simple residual `s,t`-paths, and augmenting along it produces the next explicit
even-stage flow. -/
lemma zag_step_at_odd_stage
    (u q : ℕ) (hq : q < u) :
    exercise_4_16_step_spec u (2 * q + 1) := by
  have hchosen : exercise_4_16_chosen_path (2 * q + 1) = .zag := by
    simp [exercise_4_16_chosen_path]
  have htable := residual_arc_capacity_table_at_odd_stage u q hq
  rcases htable with ⟨_, hsw, _, hvwb, hvt, _⟩
  have hq_le : q ≤ u := Nat.le_of_lt hq
  have houter_pos : (0 : ℝ) < u - q := by
    have houter_pos_nat : (0 : ℝ) < ((u - q : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < u - q by omega)
    simpa [Nat.cast_sub hq_le] using houter_pos_nat
  have houter_ge_one : (1 : ℝ) ≤ u - q := by
    have houter_ge_one_nat : (1 : ℝ) ≤ ((u - q : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ u - q by omega)
    simpa [Nat.cast_sub hq_le] using houter_ge_one_nat
  have hεzag :
      exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after (2 * q + 1)) .zag = 1 := by
    simpa using congrArg (fun f ↦ f .zag) (path_residual_capacity_at_odd_stage u q hq)
  have hzag_path :
      IsResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * q + 1)) s t (exercise_4_16_path .zag) := by
    refine ⟨by simp [exercise_4_16_path], ?_, ?_, ?_, ?_⟩
    · -- Every arc on `zag` is active by the odd-stage residual-capacity table.
      intro a ha
      simp [exercise_4_16_path] at ha
      rcases ha with rfl | rfl | rfl
      · simpa [IsActiveResidualArc, hsw] using houter_pos
      · simpa [IsActiveResidualArc, hvwb]
      · simpa [IsActiveResidualArc, hvt] using houter_pos
    · -- The first realized residual arc starts at `s`.
      simp [exercise_4_16_path, ResidualArc.tail, exercise_4_16_tail, exercise_4_16_head]
    · -- The last realized residual arc ends at `t`.
      simp [exercise_4_16_path, ResidualArc.head, exercise_4_16_tail, exercise_4_16_head]
    · -- The explicit list already records the textbook `s-w-v-t` chain.
      simp [exercise_4_16_path, ResidualArc.tail, ResidualArc.head,
        exercise_4_16_tail, exercise_4_16_head]
  have hzag_simple :
      IsSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * q + 1)) s t (exercise_4_16_path .zag) := by
    refine ⟨hzag_path, ?_⟩
    -- The vertex sequence of `zag` is `[s, w, v, t]`, hence simple.
    simp [exercise_4_16_path, residual_path_vertices, ResidualArc.tail, ResidualArc.head,
      exercise_4_16_tail, exercise_4_16_head]
  have hbottleneck :
      IsBottleneckAugmentation
        exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * q + 1)) (exercise_4_16_path .zag) 1 := by
    refine ⟨hzag_path, ?_, ?_⟩
    · -- The three residual capacities on `zag` are all at least the bottleneck value `1`.
      intro a ha
      simp [exercise_4_16_path] at ha
      rcases ha with rfl | rfl | rfl
      · simpa [hsw] using houter_ge_one
      · simpa [hvwb]
      · simpa [hvt] using houter_ge_one
    · -- The backward middle residual arc attains the bottleneck value exactly.
      refine ⟨⟨.vw, .backward⟩, by simp [exercise_4_16_path], ?_⟩
      simpa [hvwb]
  have hlongest :
      IsLongestSimpleResidualSTPath
        exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * q + 1)) s t (exercise_4_16_path .zag) := by
    refine ⟨hzag_simple, ?_⟩
    intro Q hQ
    -- Every simple residual path is one of the four named paths, and only `zag` has length `3`
    -- at an odd stage.
    rcases exercise_4_16_simple_residual_st_path_cases u (2 * q + 1) hQ with
      rfl | rfl | rfl | rfl <;>
      simp [exercise_4_16_path]
  have haugment :
      augment_flow (exercise_4_16_flow_after (2 * q + 1)) 1 (exercise_4_16_path .zag) =
        exercise_4_16_flow_after (2 * q + 1 + 1) := by
    have hnext : 2 * q + 1 + 1 = 2 * (q + 1) := by
      omega
    rw [hnext]
    funext e
    -- Augmenting along `zag` adds one unit on `sw` and `vt`, and removes one on the middle edge.
    cases e <;>
      simp [augment_flow, exercise_4_16_path, residual_forward_use_count,
        residual_backward_use_count, exercise_4_16_flow_after_even,
        exercise_4_16_flow_after_odd]
  -- Assemble the step specification from feasibility, bottleneck data, longestness, and the
  -- explicit augmentation formula.
  simpa [exercise_4_16_step_spec, hchosen, hεzag] using
    ⟨exercise_4_16_flow_after_odd_feasible u q hq, hbottleneck, hlongest, haugment⟩

/-- Every preterminal stage of the alternating run satisfies the full source-facing stage
specification. -/
lemma exercise_4_16_step_spec_of_lt
    (u k : ℕ) (hk : k < 2 * u) :
    exercise_4_16_step_spec u k := by
  -- The explicit run alternates by parity, so the even and odd step lemmas close the two cases.
  rcases Nat.even_or_odd' k with ⟨q, rfl | rfl⟩
  · exact zig_step_at_even_stage u q (by omega)
  · exact zag_step_at_odd_stage u q (by omega)

/-- Helper for Exercise 4.16: the singleton cut `{s}` has capacity `2u` in the fixed network. -/
lemma exercise_4_16_singleton_source_cut_capacity
    (u : ℕ) :
    cut_capacity exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
      ({s} : Set LongestPathCounterexampleVertex) =
        2 * u := by
  have hcut_arcs :
      outgoing_cut_arcs exercise_4_16_tail exercise_4_16_head
          ({s} : Set LongestPathCounterexampleVertex) = {sv, sw} := by
    ext a
    cases a <;>
      simp [outgoing_cut_arcs, exercise_4_16_tail, exercise_4_16_head]
  -- Only the two arcs leaving `s` cross the singleton cut.
  rw [cut_capacity, hcut_arcs, Finset.sum_pair (by decide : (sv : LongestPathCounterexampleArc) ≠ sw)]
  simp [exercise_4_16_capacity]
  ring

/-- Helper for Exercise 4.16: once the alternating run reaches stage `2u`, the residual network
has no directed `s,t`-path. -/
lemma no_residual_st_path_at_terminal_stage
    (u : ℕ) :
    NoResidualSTPath
      exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
      (exercise_4_16_flow_after (2 * u)) s t := by
  let S : Set LongestPathCounterexampleVertex := {s}
  have hx :
      IsFeasibleSTFlow
        exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * u)) :=
    exercise_4_16_flow_after_even_feasible u u le_rfl
  have hS : IsSTCutSide s t S := by
    -- The singleton source side is an `s,t`-cut because it contains `s` and excludes `t`.
    simpa [S, IsSTCutSide]
  have hvalue :
      st_flow_value exercise_4_16_tail exercise_4_16_head s
          (exercise_4_16_flow_after (2 * u)) = 2 * u := by
    simpa using exercise_4_16_flow_value_eq_stage u (2 * u)
  have hcut :
      cut_capacity exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u) S =
        2 * u := by
    simpa [S] using exercise_4_16_singleton_source_cut_capacity u
  have hmax :
      IsMaximumSTFlow
        exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
        (exercise_4_16_flow_after (2 * u)) := by
    -- Matching the singleton-cut capacity to the terminal flow value closes the max-flow/min-cut
    -- argument in the source route.
    refine flow_cut_eq_implies_isMaximumSTFlow
      exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
      (exercise_4_16_flow_after (2 * u)) s t S hx hS ?_
    calc
      st_flow_value exercise_4_16_tail exercise_4_16_head s
          (exercise_4_16_flow_after (2 * u))
          = 2 * u := hvalue
      _ = cut_capacity exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u) S := by
        symm
        exact hcut
  exact
    (isMaximumSTFlow_iff_noResidualSTPath
      exercise_4_16_tail exercise_4_16_head (exercise_4_16_capacity u)
      (exercise_4_16_flow_after (2 * u)) s t (by decide) hx).1 hmax

/-- The explicit Exercise 4.16 stagewise data satisfy the chapter's augmenting-path algorithm
predicate. The explicit stage formula is used up to stage `2u`; afterwards the run stays at the
terminal feasible flow. -/
lemma exercise_4_16_isAugmentingPathsAlgorithm
    (u : ℕ) :
    exercise_4_16_IsAugmentingPathsAlgorithm u := by
  refine
    { start_eq_zero := ?_
      feasible := ?_
      step := ?_ }
  · simpa [exercise_4_16_flows] using exercise_4_16_flow_after_zero
  · intro n
    simpa [exercise_4_16_flows] using
      exercise_4_16_flow_after_feasible u (min n (2 * u)) (Nat.min_le_right _ _)
  · intro n hn
    by_cases hnu : n < 2 * u
    · have hstep := exercise_4_16_step_spec_of_lt u n hnu
      refine ⟨exercise_4_16_path_residual_capacity u (exercise_4_16_flow_after n)
        (exercise_4_16_chosen_path n), ?_, ?_⟩
      · simpa [exercise_4_16_flows, exercise_4_16_paths, Nat.min_eq_left (Nat.le_of_lt hnu)] using
          hstep.2.1
      · have hn1 : min (n + 1) (2 * u) = n + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hnu)
        simpa [exercise_4_16_flows, exercise_4_16_paths,
          Nat.min_eq_left (Nat.le_of_lt hnu), hn1] using hstep.2.2.2.symm
    · have hterminal :
          exercise_4_16_StopsAt u n := by
        simpa [exercise_4_16_StopsAt, AugmentingPathsAlgorithm.StopsAt, exercise_4_16_flows,
          Nat.min_eq_right (Nat.le_of_not_lt hnu)] using
          no_residual_st_path_at_terminal_stage u
      exact False.elim (hn hterminal)

/-- Before stage `2u`, the explicit Exercise 4.16 augmenting-path run has not yet terminated. -/
lemma exercise_4_16_not_stopsAt
    (u k : ℕ) (hk : k < 2 * u) :
    ¬ exercise_4_16_StopsAt u k := by
  intro hstop
  have halg := exercise_4_16_isAugmentingPathsAlgorithm u
  have hmax :
      IsMaximumSTFlow
        exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
        (exercise_4_16_flows u k) :=
    augmenting_paths_algorithm_maximum_flow_at_termination
      exercise_4_16_tail exercise_4_16_head s t (exercise_4_16_capacity u)
      (exercise_4_16_flows u) exercise_4_16_paths halg hstop (by decide)
  have hcompare :
      st_flow_value exercise_4_16_tail exercise_4_16_head s (exercise_4_16_flows u (2 * u)) ≤
        st_flow_value exercise_4_16_tail exercise_4_16_head s (exercise_4_16_flows u k) :=
    hmax.le_st_flow_value (exercise_4_16_flows u (2 * u)) (halg.feasible (2 * u))
  have hk_value :
      st_flow_value exercise_4_16_tail exercise_4_16_head s (exercise_4_16_flows u k) = k := by
    -- Before the terminal stage, the truncated flow family agrees with the explicit stage flow.
    simpa [exercise_4_16_flows, Nat.min_eq_left (Nat.le_of_lt hk)] using
      exercise_4_16_flow_value_eq_stage u k
  have hterminal_value :
      st_flow_value exercise_4_16_tail exercise_4_16_head s (exercise_4_16_flows u (2 * u)) =
        2 * u := by
    simpa [exercise_4_16_flows] using exercise_4_16_flow_value_eq_stage u (2 * u)
  have hkR : (k : ℝ) < 2 * u := by
    exact_mod_cast hk
  have hcompareR : (2 * u : ℝ) ≤ k := by
    simpa [hk_value, hterminal_value] using hcompare
  linarith

/-- The explicit Exercise 4.16 run chooses a longest simple residual `s,t`-path at every
nonterminal stage. -/
theorem exercise_4_16_isLongestSimpleRun
    (u : ℕ) :
    exercise_4_16_IsLongestSimpleRun u := by
  intro n hn
  by_cases hnu : n < 2 * u
  · have hstep := exercise_4_16_step_spec_of_lt u n hnu
    simpa [exercise_4_16_IsLongestSimpleRun, exercise_4_16_flows, exercise_4_16_paths,
      Nat.min_eq_left (Nat.le_of_lt hnu)] using hstep.2.2.1
  · exfalso
    exact hn <| by
      simpa [exercise_4_16_StopsAt, AugmentingPathsAlgorithm.StopsAt, exercise_4_16_flows,
        Nat.min_eq_right (Nat.le_of_not_lt hnu)] using
        no_residual_st_path_at_terminal_stage u

/-- The alternating three-arc paths form a longest-augmenting-path run on the fixed Exercise 4.16
network: the stagewise data satisfy the chapter's augmenting-path predicate, always choose a
longest simple residual `s,t`-path, and stop at stage `2u`. -/
theorem exercise_4_16_alternating_longest_path_run
    (u : ℕ) :
    exercise_4_16_IsAugmentingPathsAlgorithm u ∧
      exercise_4_16_IsLongestSimpleRun u ∧
      exercise_4_16_StopsAt u (2 * u) := by
  refine ⟨exercise_4_16_isAugmentingPathsAlgorithm u, exercise_4_16_isLongestSimpleRun u, ?_⟩
  simpa [exercise_4_16_StopsAt, AugmentingPathsAlgorithm.StopsAt, exercise_4_16_flows] using
    no_residual_st_path_at_terminal_stage u

/-- Exercise 4.16 (1). On the fixed counterexample digraph with capacities `u,u,1,u,u`, the
augmenting-path algorithm can be forced, by always choosing a longest augmenting path, to perform
exactly `2u` iterations before termination. -/
theorem exercise_4_16_longest_augmenting_path_run_has_exactly_two_u_iterations
    (u : ℕ) :
    exercise_4_16_IsAugmentingPathsAlgorithm u ∧
      exercise_4_16_IsLongestSimpleRun u ∧
      (∀ k < 2 * u, ¬ exercise_4_16_StopsAt u k) ∧
      exercise_4_16_StopsAt u (2 * u) := by
  refine
    ⟨exercise_4_16_isAugmentingPathsAlgorithm u, exercise_4_16_isLongestSimpleRun u, ?_, ?_⟩
  · intro k hk
    exact exercise_4_16_not_stopsAt u k hk
  · simpa [exercise_4_16_StopsAt, AugmentingPathsAlgorithm.StopsAt, exercise_4_16_flows] using
      no_residual_st_path_at_terminal_stage u

/-- Exercise 4.16 (2). Since the digraph is fixed and only the capacity parameter `u` varies, the
`2u` augmentations from the preceding theorem are exponential in the varying part of the input
size. Concretely, they dominate `2^(exercise_4_16_input_size u - 1)`. -/
theorem exercise_4_16_longest_augmenting_path_iterations_exponential
    (u : ℕ) (hu : 0 < u) :
    2 ^ (exercise_4_16_input_size u - 1) ≤ 2 * u := by
  -- The varying input size is `log2 u + 1`, so the lower bound reduces to `2^(log2 u) ≤ u ≤ 2u`.
  rw [exercise_4_16_input_size, Nat.add_sub_cancel]
  rw [Nat.log2_eq_log_two]
  exact (Nat.pow_log_le_self 2 hu.ne').trans (by omega)

end Exercise_4_16

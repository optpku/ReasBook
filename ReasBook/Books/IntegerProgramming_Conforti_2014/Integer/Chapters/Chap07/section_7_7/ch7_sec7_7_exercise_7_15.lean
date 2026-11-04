/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9_part2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_claim_5_4_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch`, so this file follows the local Chapter 7 mixed-integer / facet API
-- precedent already used for flow-cover statements.

section Exercise715

variable {n : ℕ}

/-- The source index block `{1, …, k}` on `Fin n`, encoded using the zero-based condition
`j.1 < k`. -/
def exercise_7_15_head_indices (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ j.1 < k

/-- Membership in `exercise_7_15_head_indices k` means that the zero-based index lies strictly
before `k`, i.e. it belongs to the source block `{1, …, k}`. -/
theorem mem_exercise_7_15_head_indices_iff
    (k : ℕ) (j : Fin n) :
    j ∈ exercise_7_15_head_indices k ↔ j.1 < k := by
  -- This is just membership in a filtered copy of `Finset.univ`.
  simp [exercise_7_15_head_indices]

/-- The source index block `{k + 1, …, n}` on `Fin n`, encoded using the zero-based condition
`k ≤ j.1`. -/
def exercise_7_15_tail_indices (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ k ≤ j.1

/-- Membership in `exercise_7_15_tail_indices k` means that the zero-based index is at least
`k`, i.e. it belongs to the source block `{k + 1, …, n}`. -/
theorem mem_exercise_7_15_tail_indices_iff
    (k : ℕ) (j : Fin n) :
    j ∈ exercise_7_15_tail_indices k ↔ k ≤ j.1 := by
  -- This is the same filtered-universal membership computation for the tail block.
  simp [exercise_7_15_tail_indices]

/-- The source complement `\bar L = {k + 1, …, n} \setminus L` used in Exercise 7.15. -/
def exercise_7_15_tail_complement (k : ℕ) (L : Finset (Fin n)) : Finset (Fin n) :=
  exercise_7_15_tail_indices k \ L

/-- Membership in `exercise_7_15_tail_complement k L` means belonging to the source tail block
while not belonging to `L`. -/
theorem mem_exercise_7_15_tail_complement_iff
    (k : ℕ) (L : Finset (Fin n)) (j : Fin n) :
    j ∈ exercise_7_15_tail_complement k L ↔
      k ≤ j.1 ∧ j ∉ L := by
  -- The source complement is a finset difference of the tail block by `L`.
  simp [exercise_7_15_tail_complement, mem_exercise_7_15_tail_indices_iff]

/-- The mixed integer set `T` from Exercise 7.15, where the source blocks `1, …, k` and
`k + 1, …, n` are encoded on `Fin n` as `j.1 < k` and `k ≤ j.1`. -/
def exercise_7_15_mixed_integer_set
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
      (∀ j, p.1 j = 0 ∨ p.1 j = 1) ∧
      (∀ j, 0 ≤ p.2 j) ∧
        ((Finset.sum (exercise_7_15_head_indices k) fun j ↦ p.2 j) -
            (Finset.sum (exercise_7_15_tail_indices k) fun j ↦ p.2 j)) ≤
          b ∧
          ∀ j, p.2 j ≤ a j * p.1 j}

/-- Membership in `exercise_7_15_mixed_integer_set k b a` is exactly the binary,
nonnegativity, signed-balance, and upper-bound system from Exercise 7.15. -/
theorem mem_exercise_7_15_mixed_integer_set_iff
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ exercise_7_15_mixed_integer_set k b a ↔
      (∀ j, p.1 j = 0 ∨ p.1 j = 1) ∧
        (∀ j, 0 ≤ p.2 j) ∧
          ((Finset.sum (exercise_7_15_head_indices k) fun j ↦ p.2 j) -
              (Finset.sum (exercise_7_15_tail_indices k) fun j ↦ p.2 j)) ≤
            b ∧
            ∀ j, p.2 j ≤ a j * p.1 j := by
  -- Membership is definitionally the conjunction of the four source constraints.
  rfl

/-- The left-hand side of the Exercise 7.15 lifted inequality evaluated at a point `(x, y)`. -/
def exercise_7_15_lifted_flow_cover_value
    (k : ℕ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ((Finset.sum C fun j ↦ p.2 j) -
    (Finset.sum (exercise_7_15_tail_complement k L) fun j ↦ p.2 j)) +
      (Finset.sum C fun j ↦ max (a j - lam) 0 * (1 - p.1 j)) -
        (Finset.sum L fun j ↦ lam * p.1 j)

/-- `exercise_7_15_lifted_flow_cover_value k a C L λ p` expands to the source inequality left-hand
side `∑_{j ∈ C} y_j - ∑_{j ∈ \bar L} y_j + ∑_{j ∈ C} (a_j - λ)^+ (1 - x_j) - ∑_{j ∈ L} λ x_j`.
-/
theorem exercise_7_15_lifted_flow_cover_value_eq
    (k : ℕ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    exercise_7_15_lifted_flow_cover_value k a C L lam p =
      ((Finset.sum C fun j ↦ p.2 j) -
        (Finset.sum (exercise_7_15_tail_complement k L) fun j ↦ p.2 j)) +
          (Finset.sum C fun j ↦ max (a j - lam) 0 * (1 - p.1 j)) -
            (Finset.sum L fun j ↦ lam * p.1 j) := by
  -- The left-hand side is introduced precisely by this definition.
  rfl

/-- Helper for Exercise 7.15: inserting one tail index into `L` replaces the corresponding
`-y_i` contribution by `-λ x_i`, so the lifted value changes by `y_i - λ x_i`. -/
theorem exercise_7_15_value_insert_tail
    (k : ℕ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ))
    {i : Fin n}
    (hiL : i ∉ L)
    (htail : k ≤ i.1) :
    exercise_7_15_lifted_flow_cover_value k a C (insert i L) lam p =
      exercise_7_15_lifted_flow_cover_value k a C L lam p + p.2 i - lam * p.1 i := by
  have hsplit_tail :
      Finset.sum (exercise_7_15_tail_indices k \ L) (fun j ↦ p.2 j) =
        p.2 i + Finset.sum (exercise_7_15_tail_indices k \ insert i L) (fun j ↦ p.2 j) := by
    -- The old tail complement is the new one plus the single index `i`.
    have hset :
        exercise_7_15_tail_indices k \ L =
          insert i (exercise_7_15_tail_indices k \ insert i L) := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [exercise_7_15_tail_indices, hiL, htail]
      · simp [exercise_7_15_tail_indices, hji]
    rw [hset]
    have hi_not_mem :
        i ∉ exercise_7_15_tail_indices k \ insert i L := by
      simp [exercise_7_15_tail_indices]
    rw [Finset.sum_insert hi_not_mem]
  have hsplit_L :
      Finset.sum (insert i L) (fun j ↦ lam * p.1 j) =
        lam * p.1 i + Finset.sum L (fun j ↦ lam * p.1 j) := by
    -- The lifted `L`-term gains exactly the new coefficient at `i`.
    rw [Finset.sum_insert hiL]
  -- After splitting the two affected sums, the identity is a polynomial rearrangement.
  rw [exercise_7_15_lifted_flow_cover_value, exercise_7_15_lifted_flow_cover_value,
    exercise_7_15_tail_complement, exercise_7_15_tail_complement, hsplit_tail, hsplit_L]
  ring

/-- Helper for Exercise 7.15: the staged owner for the proof route, where `S` is the released
tail set and `L ⊆ S` is the lifted subset. Released-but-unlifted tails contribute `-y_i`, lifted
tails contribute `-λ x_i`, and tails outside `S` are omitted from the stage value because the
stage face will later freeze them to `(x_i, y_i) = (0, 0)`. -/
def exercise715StageValue
    (a : Fin n → ℝ) (C S L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ((Finset.sum C fun j ↦ p.2 j) -
    (Finset.sum (S \ L) fun j ↦ p.2 j)) +
      (Finset.sum C fun j ↦ max (a j - lam) 0 * (1 - p.1 j)) -
        (Finset.sum L fun j ↦ lam * p.1 j)

/-- Helper for Exercise 7.15: stage `S = ∅`, `L = ∅` is the zero-tail owner, so only the head
cover sum and the zero-lift penalty remain. -/
theorem exercise715StageValue_empty
    (a : Fin n → ℝ) (C : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    exercise715StageValue a C ∅ ∅ lam p =
      (Finset.sum C fun j ↦ p.2 j) +
        (Finset.sum C fun j ↦ max (a j - lam) 0 * (1 - p.1 j)) := by
  -- At the zero-tail stage both tail-indexed sums vanish.
  simp [exercise715StageValue]

/-- Helper for Exercise 7.15: the staged ambient set where the unreleased tail coordinates are
frozen to `y_j = 0`. -/
def exercise715StageSet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n)) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    p ∈ exercise_7_15_mixed_integer_set k b a ∧
      ∀ j, k ≤ j.1 → j ∉ S → p.2 j = 0}

/-- Membership in `exercise715StageSet k b a S` means mixed-set feasibility together with the
stage freeze `y_j = 0` on every unreleased tail coordinate. -/
theorem mem_exercise715StageSet_iff
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ exercise715StageSet k b a S ↔
      p ∈ exercise_7_15_mixed_integer_set k b a ∧
        ∀ j, k ≤ j.1 → j ∉ S → p.2 j = 0 := by
  -- The staged ambient owner is defined by this mixed-set plus freeze conjunction.
  rfl

/-- Helper for Exercise 7.15: the equality face cut out by a staged owner. -/
def exercise715StageFace
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    p ∈ convexHull ℝ (exercise715StageSet k b a S) ∧
      exercise715StageValue a C S L lam p = b}

/-- Membership in `exercise715StageFace k b a C S L lam` means lying in the convex hull of the
staged ambient set and meeting the staged inequality at equality. -/
theorem mem_exercise715StageFace_iff
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ exercise715StageFace k b a C S L lam ↔
      p ∈ convexHull ℝ (exercise715StageSet k b a S) ∧
        exercise715StageValue a C S L lam p = b := by
  -- The staged face owner is defined as this equality slice.
  rfl

/-- Helper for Exercise 7.15: at the zero-tail stage the mixed ambient owner is exactly the
single-node flow set with tail capacities truncated to `0`. -/
theorem exercise715ZeroTailStageSet_eq_singleNodeFlowSet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j) :
    exercise715StageSet k b a ∅ =
      single_node_flow_set (fun j ↦ if j.1 < k then a j else 0) b := by
  ext p
  constructor
  · rintro ⟨hp, hfreeze⟩
    rcases (mem_exercise_7_15_mixed_integer_set_iff k b a p).mp hp with
      ⟨hx_bin, hy_nonneg, hbalance, hcap⟩
    refine (mem_single_node_flow_set_iff (fun j ↦ if j.1 < k then a j else 0) b p).mpr ?_
    refine ⟨hx_bin, hy_nonneg, ?_, ?_⟩
    · have hsplit_univ :
        Finset.sum (exercise_7_15_head_indices k) (fun j ↦ p.2 j) +
            Finset.sum (exercise_7_15_tail_indices k) (fun j ↦ p.2 j) =
          ∑ j, p.2 j := by
        -- Split the total `y`-sum into the head block and the tail block.
        simpa [exercise_7_15_head_indices, exercise_7_15_tail_indices, Nat.not_lt] using
          (Finset.sum_filter_add_sum_filter_not
            (s := Finset.univ) (p := fun j : Fin n ↦ j.1 < k) (f := fun j ↦ p.2 j))
      have htail_zero :
          Finset.sum (exercise_7_15_tail_indices k) (fun j ↦ p.2 j) = 0 := by
        -- Every tail coordinate is frozen to `0` at the base stage.
        refine Finset.sum_eq_zero ?_
        intro j hj
        exact hfreeze j ((mem_exercise_7_15_tail_indices_iff k j).mp hj) (by simp)
      have hhead_le :
          Finset.sum (exercise_7_15_head_indices k) (fun j ↦ p.2 j) ≤ b := by
        -- The signed balance reduces to the head-capacity bound once the tail sum vanishes.
        simpa [htail_zero] using hbalance
      calc
        ∑ j, p.2 j =
            Finset.sum (exercise_7_15_head_indices k) (fun j ↦ p.2 j) +
              Finset.sum (exercise_7_15_tail_indices k) (fun j ↦ p.2 j) := by
              simpa using hsplit_univ.symm
        _ = Finset.sum (exercise_7_15_head_indices k) (fun j ↦ p.2 j) := by simp [htail_zero]
        _ ≤ b := hhead_le
    · intro j
      by_cases hj : j.1 < k
      · -- On head coordinates the truncated capacities agree with the original capacities.
        simpa [hj] using hcap j
      · have hy_zero : p.2 j = 0 := by
          -- Tail coordinates are frozen to `0` at the base stage.
          exact hfreeze j (Nat.not_lt.mp hj) (by simp)
        -- On frozen tails the truncated right-hand side is also zero.
        simp [hj, hy_zero]
  · intro hp
    rcases (mem_single_node_flow_set_iff (fun j ↦ if j.1 < k then a j else 0) b p).mp hp with
      ⟨hx_bin, hy_nonneg, hsum, hcap⟩
    have htail_zero_point : ∀ j, k ≤ j.1 → p.2 j = 0 := by
      intro j htail
      have hle_zero : p.2 j ≤ 0 := by
        -- Tail capacities are zero in the truncated single-node owner.
        simpa [if_neg (Nat.not_lt.mpr htail)] using hcap j
      exact le_antisymm hle_zero (hy_nonneg j)
    have hsplit_univ :
        Finset.sum (exercise_7_15_head_indices k) (fun j ↦ p.2 j) +
            Finset.sum (exercise_7_15_tail_indices k) (fun j ↦ p.2 j) =
          ∑ j, p.2 j := by
      -- Use the same head-tail partition of `Fin n` to recover the mixed balance inequality.
      simpa [exercise_7_15_head_indices, exercise_7_15_tail_indices, Nat.not_lt] using
        (Finset.sum_filter_add_sum_filter_not
          (s := Finset.univ) (p := fun j : Fin n ↦ j.1 < k) (f := fun j ↦ p.2 j))
    have htail_zero_sum :
        Finset.sum (exercise_7_15_tail_indices k) (fun j ↦ p.2 j) = 0 := by
      -- The truncated single-node model forces every tail `y_j` to be zero.
      refine Finset.sum_eq_zero ?_
      intro j hj
      exact htail_zero_point j ((mem_exercise_7_15_tail_indices_iff k j).mp hj)
    have hhead_le :
        Finset.sum (exercise_7_15_head_indices k) (fun j ↦ p.2 j) ≤ b := by
      -- The total single-node capacity bound becomes the mixed head bound after removing zeros.
      calc
        Finset.sum (exercise_7_15_head_indices k) (fun j ↦ p.2 j) =
            ∑ j, p.2 j := by
              rw [← hsplit_univ, htail_zero_sum, add_zero]
        _ ≤ b := hsum
    refine ⟨(mem_exercise_7_15_mixed_integer_set_iff k b a p).mpr ?_, ?_⟩
    · refine ⟨hx_bin, hy_nonneg, ?_, ?_⟩
      · -- The mixed signed balance again reduces to the head bound because the tail sum is zero.
        simpa [htail_zero_sum] using hhead_le
      · intro j
        by_cases hj : j.1 < k
        · -- On the head coordinates the original and truncated capacities coincide.
          simpa [hj] using hcap j
        · have hy_zero : p.2 j = 0 := htail_zero_point j (Nat.not_lt.mp hj)
          have hx_nonneg : 0 ≤ p.1 j := by
            rcases hx_bin j with hzero | hone <;> linarith
          have hax_nonneg : 0 ≤ a j * p.1 j := mul_nonneg (ha_nonneg j) hx_nonneg
          -- Frozen tails satisfy the original upper bound because the right-hand side is
          -- nonnegative.
          simpa [hy_zero] using hax_nonneg
    · intro j htail hjS
      -- The zero-tail stage remembers exactly the tail coordinates forced to vanish.
      exact htail_zero_point j htail

/-- Helper for Exercise 7.15: on the zero-tail stage the staged owner is exactly the canonical
flow-cover owner for the truncated capacity function. -/
theorem exercise715ZeroTailStageValue_eq_flowCoverValue
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C : Finset (Fin n)) (lam : ℝ)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hcover : C.sum a = b + lam)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    exercise715StageValue a C ∅ ∅ lam p =
      flow_cover_value (fun j ↦ if j.1 < k then a j else 0) b C p := by
  let a0 : Fin n → ℝ := fun j ↦ if j.1 < k then a j else 0
  have hcover0 : C.sum a0 = b + lam := by
    -- The truncated capacity function agrees with `a` on the cover `C`.
    calc
      C.sum a0 = C.sum a := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [a0, hCsub hj]
      _ = b + lam := hcover
  have hpenalty :
      ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) =
        ∑ j ∈ C, max (a0 j - lam) 0 * (1 - p.1 j) := by
    -- The positive-part coefficients also agree on `C`.
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [a0, hCsub hj]
  -- Expand the staged owner and then rewrite it to the canonical zero-lifted owner on `a0`.
  rw [exercise715StageValue_empty, hpenalty]
  symm
  simpa [a0] using flow_cover_value_eq_zero_lifted_value a0 b lam C hcover0 p

/-- Helper for Exercise 7.15: releasing one new tail index into the staged owner adds exactly the
`-y_i` term for that coordinate. -/
theorem exercise715StageValue_insertReleasedTail
    (a : Fin n → ℝ) (C S L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ))
    {i : Fin n}
    (hiS : i ∉ S)
    (hiL : i ∉ L) :
    exercise715StageValue a C (insert i S) L lam p =
      exercise715StageValue a C S L lam p - p.2 i := by
  have hset : insert i S \ L = insert i (S \ L) := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [hiL]
    · simp [hji]
  have hi_not_mem : i ∉ S \ L := by
    simp [hiS]
  -- Split the released-tail sum at the new coordinate and rearrange the affine expression.
  rw [exercise715StageValue, exercise715StageValue, hset, Finset.sum_insert hi_not_mem]
  ring

/-- Helper for Exercise 7.15: once a released tail index is lifted, its staged contribution
changes from `-y_i` to `-λ x_i`. -/
theorem exercise715StageValue_insertLiftedTail
    (a : Fin n → ℝ) (C S L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ))
    {i : Fin n}
    (hiS : i ∈ S)
    (hiL : i ∉ L) :
    exercise715StageValue a C S (insert i L) lam p =
      exercise715StageValue a C S L lam p + p.2 i - lam * p.1 i := by
  have hsplit_released :
      Finset.sum (S \ L) (fun j ↦ p.2 j) =
        p.2 i + Finset.sum (S \ insert i L) (fun j ↦ p.2 j) := by
    have hset : S \ L = insert i (S \ insert i L) := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [hiS, hiL]
      · simp [hji]
    rw [hset]
    have hi_not_mem : i ∉ S \ insert i L := by
      simp
    rw [Finset.sum_insert hi_not_mem]
  have hsplit_L :
      Finset.sum (insert i L) (fun j ↦ lam * p.1 j) =
        lam * p.1 i + Finset.sum L (fun j ↦ lam * p.1 j) := by
    -- The lifted sum gains only the new `i`-coordinate.
    rw [Finset.sum_insert hiL]
  -- After isolating the old `-y_i` term and the new `-λ x_i` term, the stage update is linear.
  rw [exercise715StageValue, exercise715StageValue, hsplit_released, hsplit_L]
  ring

/-- Helper for Exercise 7.15: releasing and lifting a previously unreleased tail index changes
the staged value only by the selector term `-lam * x_i`. -/
theorem exercise715StageValue_insertReleasedAndLiftedTail
    (a : Fin n → ℝ) (C S L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ))
    {i : Fin n}
    (hiS : i ∉ S)
    (hLsub : L ⊆ S) :
    exercise715StageValue a C (insert i S) (insert i L) lam p =
      exercise715StageValue a C S L lam p - lam * p.1 i := by
  have hiL : i ∉ L := fun hi ↦ hiS (hLsub hi)
  have hiInsert : i ∈ insert i S := Finset.mem_insert_self i S
  -- First expose the released flow term, then cancel it against the lifted update.
  rw [exercise715StageValue_insertLiftedTail a C (insert i S) L lam p hiInsert hiL]
  rw [exercise715StageValue_insertReleasedTail a C S L lam p hiS hiL]
  ring

/-- Helper for Exercise 7.15: when every tail coordinate has been released, the staged owner is
exactly the target lifted-flow-cover owner from the theorem statement. -/
theorem exercise715FullReleasedStageEqTarget
    (k : ℕ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    exercise715StageValue a C (exercise_7_15_tail_indices k) L lam p =
      exercise_7_15_lifted_flow_cover_value k a C L lam p := by
  -- The full released stage uses the same tail-complement owner as the target definition.
  rfl

/-- Helper for Exercise 7.15: once every tail index is released, the staged ambient set is the
original mixed integer set. -/
theorem exercise715FullReleasedStageSet_eq_mixedIntegerSet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) :
    exercise715StageSet k b a (exercise_7_15_tail_indices k) =
      exercise_7_15_mixed_integer_set k b a := by
  ext p
  constructor
  · intro hp
    -- Forgetting the vacuous full-release freeze returns the original mixed feasibility.
    exact hp.1
  · intro hp
    refine (mem_exercise715StageSet_iff k b a (exercise_7_15_tail_indices k) p).mpr ?_
    refine ⟨hp, ?_⟩
    intro j htail hjS
    -- Every tail index already belongs to the full released set, so the freeze condition is
    -- vacuous here.
    exact False.elim (hjS ((mem_exercise_7_15_tail_indices_iff k j).2 htail))

/-- Helper for Exercise 7.15: the zero-tail staged face is exactly the canonical flow-cover face
for the truncated capacity function `a0`. -/
theorem exercise715ZeroTailStageFace_eq_flowCoverFace
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C : Finset (Fin n)) (lam : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hcover : C.sum a = b + lam) :
    exercise715StageFace k b a C ∅ ∅ lam =
      flow_cover_face (fun j ↦ if j.1 < k then a j else 0) b C := by
  ext p
  -- Normalize the base-stage ambient set and the staged owner to the canonical flow-cover API.
  rw [mem_exercise715StageFace_iff, mem_flow_cover_face_iff,
    exercise715ZeroTailStageSet_eq_singleNodeFlowSet k b a ha_nonneg,
    exercise715ZeroTailStageValue_eq_flowCoverValue k b a C lam hCsub hcover]

/-- Helper for Exercise 7.15: the zero-tail staged inequality is already a facet of the zero-tail
ambient polytope because it is the canonical flow-cover facet for the truncated capacities. -/
theorem exercise715ZeroTailStageFacet
    (k : ℕ)
    (b : ℝ) (a : Fin n → ℝ)
    (C : Finset (Fin n)) (lam : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hCnonempty : C.Nonempty)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hmax : ∃ j ∈ C, lam < a j)
    (hcover : C.sum a = b + lam) :
    (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (exercise715StageSet k b a ∅) →
          exercise715StageValue a C ∅ ∅ lam p ≤ b) ∧
      IsFacetOf
        (convexHull ℝ (exercise715StageSet k b a ∅))
        (exercise715StageFace k b a C ∅ ∅ lam) := by
  let a0 : Fin n → ℝ := fun j ↦ if j.1 < k then a j else 0
  have ha0_nonneg : ∀ j, 0 ≤ a0 j := by
    intro j
    by_cases hj : j.1 < k
    · simpa [a0, hj] using ha_nonneg j
    · simp [a0, hj]
  have hcover0 : C.sum a0 = b + lam := by
    -- The truncated capacities agree with `a` on the flow cover `C`.
    calc
      C.sum a0 = C.sum a := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [a0, hCsub hj]
      _ = b + lam := hcover
  have hlam_max0 : lam < C.sup' hCnonempty a0 := by
    rcases hmax with ⟨j, hjC, hjlt⟩
    refine (Finset.lt_sup'_iff hCnonempty).2 ?_
    refine ⟨j, hjC, ?_⟩
    simpa [a0, hCsub hjC] using hjlt
  have hfacet0 :
      flow_cover_inequality_facet_defining a0 b C :=
    flow_cover_zero_lifting_facet_defining_of_lt_max
      b a0 C lam ha0_nonneg hCnonempty hcover0 (by linarith [hC.sum_gt_rhs, hcover]) hlam_max0
  rw [flow_cover_inequality_facet_defining_iff] at hfacet0
  constructor
  · intro p hp
    have hp0 : p ∈ convexHull ℝ (single_node_flow_set a0 b) := by
      -- Transport the staged ambient point to the canonical zero-tail single-node owner.
      simpa [exercise715ZeroTailStageSet_eq_singleNodeFlowSet k b a ha_nonneg] using hp
    have hvalid0 := hfacet0.1 hp0
    -- The staged value is the canonical flow-cover value on the truncated owner.
    simpa [exercise715ZeroTailStageValue_eq_flowCoverValue k b a C lam hCsub hcover]
      using hvalid0
  · -- The zero-tail face is literally the canonical face after the same normalization.
    simpa [exercise715ZeroTailStageSet_eq_singleNodeFlowSet k b a ha_nonneg,
      exercise715ZeroTailStageFace_eq_flowCoverFace k b a C lam ha_nonneg hCsub hcover] using
      hfacet0.2

/-- Helper for Exercise 7.15: when every released tail coordinate already has zero flow, the
released-stage owner with `L = ∅` collapses back to the zero-tail stage owner. -/
theorem exercise715StageValue_eq_zeroTail_of_releasedZero
    (a : Fin n → ℝ) (C S : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ))
    (hzero : ∀ j ∈ S, p.2 j = 0) :
    exercise715StageValue a C S ∅ lam p =
      exercise715StageValue a C ∅ ∅ lam p := by
  have hsumS : ∑ j ∈ S, p.2 j = 0 := by
    -- Every released coordinate contributes zero to the released-tail sum.
    refine Finset.sum_eq_zero ?_
    intro j hj
    exact hzero j hj
  -- Once the released-tail sum vanishes, the only surviving terms are the zero-tail ones.
  simp [exercise715StageValue, hsumS]

/-- Helper for Exercise 7.15: the canonical zero-tail anchor point remains on every release-stage
face because all released tails still carry zero flow there. -/
theorem exercise715AnchorPoint_mem_stageFace
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S : Finset (Fin n)) (lam : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hC : IsFlowCover a b C)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (hcover : C.sum a = b + lam)
    (hlam_pos : 0 < lam)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : lam < a j0) :
    ((fun j ↦ if j ∈ C then 1 else 0),
        fun j ↦ (if j ∈ C then a j else 0) - if j = j0 then lam else 0) ∈
      exercise715StageFace k b a C S ∅ lam := by
  let a0 : Fin n → ℝ := fun j ↦ if j.1 < k then a j else 0
  let pAnchor : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j ∈ C then 1 else 0),
      fun j ↦ (if j ∈ C then a j else 0) - if j = j0 then lam else 0)
  have ha0_nonneg : ∀ j, 0 ≤ a0 j := by
    intro j
    by_cases hj : j.1 < k
    · simpa [a0, hj] using ha_nonneg j
    · simp [a0, hj]
  have hcover0 : C.sum a0 = b + lam := by
    -- The truncated capacity vector agrees with `a` on the cover `C`.
    calc
      C.sum a0 = C.sum a := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [a0, hCsub hj]
      _ = b + lam := hcover
  have hC0 : IsFlowCover a0 b C := by
    -- The same cover sum still exceeds `b` after truncating only the noncover tails.
    rw [isFlowCover_iff]
    calc
      b < b + lam := by linarith
      _ = C.sum a0 := hcover0.symm
  have hj0lt0 : flow_cover_excess a0 b C < a0 j0 := by
    -- The distinguished anchor remains the unique cover coordinate whose slack absorbs `lam`.
    calc
      flow_cover_excess a0 b C = lam :=
        flow_cover_excess_eq_of_sum_eq_add a0 b lam C hcover0
      _ < a j0 := hj0lt
      _ = a0 j0 := by
        simp [a0, hCsub hj0C]
  have hbase : pAnchor ∈ exercise715StageFace k b a C ∅ ∅ lam := by
    have hbase0 :
        pAnchor ∈ flow_cover_face a0 b C := by
      -- Route correction: transport the anchor through the already-proved zero-tail owner,
      -- rather than rebuilding the base face inside the mixed stage owner.
      have hbase0' :
          ((fun j ↦ if j ∈ C then 1 else 0),
              fun j ↦ (if j ∈ C then a0 j else 0) - if j = j0 then lam else 0) ∈
            flow_cover_face a0 b C := by
        simpa [flow_cover_excess_eq_of_sum_eq_add a0 b lam C hcover0] using
          (flow_cover_anchor_point_mem_face a0 b C ha0_nonneg hC0 hj0C hj0lt0)
      have hanchor_eq :
          ((fun j ↦ if j ∈ C then 1 else 0),
              fun j ↦ (if j ∈ C then a0 j else 0) - if j = j0 then lam else 0) = pAnchor := by
        apply Prod.ext
        · funext j
          simp [pAnchor]
        · funext j
          by_cases hj : j ∈ C
          · have hjHead : j.1 < k := hCsub hj
            simp [pAnchor, a0, hj, hjHead]
          · simp [pAnchor, a0, hj]
      exact hanchor_eq ▸ hbase0'
    simpa [exercise715ZeroTailStageFace_eq_flowCoverFace k b a C lam ha_nonneg hCsub hcover,
      pAnchor, a0] using hbase0
  rcases (mem_exercise715StageFace_iff k b a C ∅ ∅ lam pAnchor).mp hbase with ⟨hconv0, hEq0⟩
  have hstageSubset :
      exercise715StageSet k b a ∅ ⊆ exercise715StageSet k b a S := by
    intro p hp
    rcases (mem_exercise715StageSet_iff k b a ∅ p).mp hp with ⟨hpT, hfreeze⟩
    refine (mem_exercise715StageSet_iff k b a S p).mpr ⟨hpT, ?_⟩
    intro j hjtail hjS
    exact hfreeze j hjtail (by simp)
  have hconvS : pAnchor ∈ convexHull ℝ (exercise715StageSet k b a S) := by
    exact convexHull_mono hstageSubset hconv0
  have hzeroReleased : ∀ j ∈ S, pAnchor.2 j = 0 := by
    intro j hjS
    have hjtail : k ≤ j.1 := hSsub hjS
    have hjC : j ∉ C := by
      intro hj
      exact not_le_of_gt (hCsub hj) hjtail
    have hj0 : j ≠ j0 := by
      intro hEq
      subst hEq
      exact hjC hj0C
    -- Released tails are still zero at the transported anchor point.
    simp [pAnchor, hjC, hj0]
  have hEqS :
      exercise715StageValue a C S ∅ lam pAnchor = b := by
    -- The stage value is unchanged because the released-tail part is still zero.
    rw [exercise715StageValue_eq_zeroTail_of_releasedZero a C S lam pAnchor hzeroReleased]
    exact hEq0
  exact (mem_exercise715StageFace_iff k b a C S ∅ lam pAnchor).mpr ⟨hconvS, hEqS⟩

/-- Helper for Exercise 7.15: releasing one tail coordinate admits an explicit tight point with
positive released flow, obtained by coupling that tail with the anchor cover coordinate. -/
theorem exercise715ReleaseTailCoupledPoint_mem_stageFace
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S : Finset (Fin n)) (lam : ℝ)
    (ha : ∀ j, 0 < a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (hcover : C.sum a = b + lam)
    (hlam_pos : 0 < lam)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : lam < a j0)
    (hiS : i ∉ S)
    (htail : k ≤ i.1) :
    let p : (Fin n → ℝ) × (Fin n → ℝ) :=
      ((fun j ↦ if j = i then 1 else if j ∈ C then 1 else 0),
        fun j ↦
          if j = j0 then a j0 - lam + min (a i) lam
          else if j = i then min (a i) lam
          else if j ∈ C.erase j0 then a j else 0)
    p ∈ exercise715StageFace k b a C (insert i S) ∅ lam ∧ 0 < p.2 i := by
  let t : ℝ := min (a i) lam
  let p : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C then 1 else 0),
      fun j ↦
        if j = j0 then a j0 - lam + t
        else if j = i then t
        else if j ∈ C.erase j0 then a j else 0)
  suffices hp : p ∈ exercise715StageFace k b a C (insert i S) ∅ lam ∧ 0 < p.2 i by
    simpa [p, t] using hp
  have hiC : i ∉ C := by
    intro hiC
    exact not_le_of_gt (hCsub hiC) htail
  have hij0 : i ≠ j0 := by
    intro hEq
    subst hEq
    exact hiC hj0C
  have ht_pos : 0 < t := by
    -- The coupled released flow is the positive minimum of the tail capacity and `lam`.
    exact lt_min (ha i) hlam_pos
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_le_ai : t ≤ a i := min_le_left _ _
  have ht_le_lam : t ≤ lam := min_le_right _ _
  have hp_stageSet : p ∈ exercise715StageSet k b a (insert i S) := by
    refine (mem_exercise715StageSet_iff k b a (insert i S) p).mpr ?_
    refine ⟨(mem_exercise_7_15_mixed_integer_set_iff k b a p).mpr ?_, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst hji
        simp [p, hiC]
      · by_cases hjC : j ∈ C
        · simp [p, hji, hjC]
        · simp [p, hji, hjC]
    · intro j
      by_cases hj0 : j = j0
        -- The anchor flow stays nonnegative because the anchor slack is positive.
      · have hslack : 0 ≤ a j0 - lam := by
          linarith [hj0lt]
        have hnonneg : 0 ≤ a j0 - lam + t := by
          linarith
        simpa [p, hj0] using hnonneg
      · by_cases hji : j = i
        · subst hji
          simpa [p, hij0] using ht_nonneg
        · by_cases hj : j ∈ C.erase j0
          · have hjC : j ∈ C := (Finset.mem_erase.mp hj).2
            have hji' : j ≠ i := by
              intro hEq
              subst hEq
              exact hiC hjC
            exact (by simpa [p, hj0, hji', hj] using (ha j).le)
          · simp [p, hj0, hji, hj]
    · have hsumC :
          ∑ j ∈ C, p.2 j = C.sum a - lam + t := by
        have hrest :
            ∑ j ∈ C.erase j0, p.2 j = ∑ j ∈ C.erase j0, a j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj0 : j ≠ j0 := (Finset.mem_erase.mp hj).1
          have hjC : j ∈ C := (Finset.mem_erase.mp hj).2
          have hji : j ≠ i := by
            intro hEq
            subst hEq
            exact hiC hjC
          simp [p, hj0, hji, hj]
        calc
          ∑ j ∈ C, p.2 j
              = p.2 j0 + ∑ j ∈ C.erase j0, p.2 j := by
                  simpa [add_comm] using
                    (Finset.sum_erase_add (s := C) (f := fun j ↦ p.2 j) hj0C).symm
          _ = p.2 j0 + ∑ j ∈ C.erase j0, a j := by
                rw [hrest]
          _ = (a j0 - lam + t) + ∑ j ∈ C.erase j0, a j := by
                simp [p]
          _ = C.sum a - lam + t := by
                rw [← Finset.sum_erase_add (s := C) (f := a) hj0C]
                ring
      have hheadEq :
          ∑ j ∈ exercise_7_15_head_indices k, p.2 j = ∑ j ∈ C, p.2 j := by
        have hCsubset : C ⊆ exercise_7_15_head_indices k := by
          intro j hj
          exact (mem_exercise_7_15_head_indices_iff k j).2 (hCsub hj)
        calc
          ∑ j ∈ exercise_7_15_head_indices k, p.2 j
              = ∑ j ∈ C, p.2 j + ∑ j ∈ exercise_7_15_head_indices k \ C, p.2 j := by
                  simpa [add_comm] using
                    (Finset.sum_sdiff
                      (s₁ := C)
                      (s₂ := exercise_7_15_head_indices k)
                      (f := fun j ↦ p.2 j)
                      hCsubset).symm
          _ = ∑ j ∈ C, p.2 j := by
                have hzero :
                    ∑ j ∈ exercise_7_15_head_indices k \ C, p.2 j = 0 := by
                  refine Finset.sum_eq_zero ?_
                  intro j hj
                  have hjHead : j.1 < k := by
                    exact (mem_exercise_7_15_head_indices_iff k j).mp
                      ((Finset.mem_sdiff.mp hj).1)
                  have hjC : j ∉ C := (Finset.mem_sdiff.mp hj).2
                  have hji : j ≠ i := by
                    intro hEq
                    subst hEq
                    exact not_lt_of_ge htail hjHead
                  have hj0' : j ≠ j0 := by
                    intro hEq
                    subst hEq
                    exact hjC hj0C
                  simp [p, hji, hjC, hj0']
                rw [hzero, add_zero]
      have htailEq :
          ∑ j ∈ exercise_7_15_tail_indices k, p.2 j = t := by
        have hiTail : i ∈ exercise_7_15_tail_indices k :=
          (mem_exercise_7_15_tail_indices_iff k i).2 htail
        rw [Finset.sum_eq_single i]
        · simp [p, hij0]
        · intro j hj hji
          have hjC : j ∉ C := by
            intro hjC
            exact not_le_of_gt (hCsub hjC)
              ((mem_exercise_7_15_tail_indices_iff k j).mp hj)
          have hj0 : j ≠ j0 := by
            intro hEq
            subst hEq
            exact hjC hj0C
          simp [p, hj0, hji, hjC]
        · intro hiNotTail
          exact False.elim (hiNotTail hiTail)
      -- The added tail flow is mirrored on the anchor, so the mixed balance stays tight.
      calc
        (∑ j ∈ exercise_7_15_head_indices k, p.2 j) -
            ∑ j ∈ exercise_7_15_tail_indices k, p.2 j
            = (C.sum a - lam + t) - t := by rw [hheadEq, hsumC, htailEq]
        _ = b := by
          rw [hcover]
          ring
        _ ≤ b := le_rfl
    · intro j
      by_cases hji : j = i
      · subst hji
        simpa [p, hij0] using ht_le_ai
      · by_cases hj0 : j = j0
        · have hslack : a j0 - lam + t ≤ a j0 := by
            linarith
          simpa [p, hj0, hj0C, hij0] using hslack
        · by_cases hj : j ∈ C.erase j0
          · have hjC : j ∈ C := (Finset.mem_erase.mp hj).2
            simp [p, hji, hj0, hj, hjC]
          · have hjC : j ∉ C := by
              intro hjC
              exact hj (by simp [hj0, hjC])
            simp [p, hji, hj0, hj, hjC]
    · intro j hjtail hjNotReleased
      have hji : j ≠ i := by
        intro hEq
        subst hEq
        exact hjNotReleased (by simp)
      have hjC : j ∉ C := by
        intro hjC
        exact not_le_of_gt (hCsub hjC) hjtail
      have hj0 : j ≠ j0 := by
        intro hEq
        subst hEq
        exact hjC hj0C
      have hj : j ∉ C.erase j0 := by simp [hjC, hj0]
      -- Unreleased tail coordinates are still frozen to zero in the explicit witness.
      simp [p, hji, hj0, hj]
  have hzeroS : ∀ j ∈ S, p.2 j = 0 := by
    intro j hjS
    have hjtail : k ≤ j.1 := hSsub hjS
    have hji : j ≠ i := by
      intro hEq
      subst hEq
      exact hiS hjS
    have hjC : j ∉ C := by
      intro hjC
      exact not_le_of_gt (hCsub hjC) hjtail
    have hj0 : j ≠ j0 := by
      intro hEq
      subst hEq
      exact hjC hj0C
    have hj : j ∉ C.erase j0 := by simp [hjC, hj0]
    -- Previously released tails stay at zero in the coupled witness as well.
    simp [p, hji, hj0, hj]
  have hsumReleased :
      ∑ j ∈ insert i S, p.2 j = t := by
    have hsumS : ∑ j ∈ S, p.2 j = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      exact hzeroS j hj
    -- The only positive released-tail contribution comes from the newly released coordinate `i`.
    rw [Finset.sum_insert hiS, hsumS]
    simp [p, hij0]
  have hsumC :
      ∑ j ∈ C, p.2 j = C.sum a - lam + t := by
    have hrest :
        ∑ j ∈ C.erase j0, p.2 j = ∑ j ∈ C.erase j0, a j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj0 : j ≠ j0 := (Finset.mem_erase.mp hj).1
      have hjC : j ∈ C := (Finset.mem_erase.mp hj).2
      have hji : j ≠ i := by
        intro hEq
        subst hEq
        exact hiC hjC
      simp [p, hj0, hji, hj]
    calc
      ∑ j ∈ C, p.2 j
          = p.2 j0 + ∑ j ∈ C.erase j0, p.2 j := by
              simpa [add_comm] using
                (Finset.sum_erase_add (s := C) (f := fun j ↦ p.2 j) hj0C).symm
      _ = p.2 j0 + ∑ j ∈ C.erase j0, a j := by
            rw [hrest]
      _ = (a j0 - lam + t) + ∑ j ∈ C.erase j0, a j := by
            simp [p]
      _ = C.sum a - lam + t := by
            rw [← Finset.sum_erase_add (s := C) (f := a) hj0C]
            ring
  have hvalueEq : exercise715StageValue a C (insert i S) ∅ lam p = b := by
    have hsumReleased' :
        ∑ j ∈ insert i S \ ∅, p.2 j = t := by
      simpa using hsumReleased
    have hpenalty :
        ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      simp [p, hj, hiC]
    -- The stage value is the cover sum `b + t` minus the released-tail sum `t`.
    rw [exercise715StageValue, hsumC, hsumReleased', hpenalty, hcover]
    ring
  refine ⟨(mem_exercise715StageFace_iff k b a C (insert i S) ∅ lam p).mpr ?_, ?_⟩
  · -- The explicit coupled point belongs to the new stage set, hence to its convex hull.
    exact ⟨subset_convexHull ℝ _ hp_stageSet, hvalueEq⟩
  · -- The released coordinate is strictly positive by construction.
    simpa [p, t, hij0] using ht_pos

/-- Helper for Exercise 7.15: after simultaneously releasing and lifting a tail index, every
flow level `t ∈ [lam, a i]` gives an explicit tight mixed-integer point. -/
theorem exercise715LiftedTailPoint_mem_stageFace
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam t : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (hLsub : L ⊆ S)
    (hcover : C.sum a = b + lam)
    (hlam_nonneg : 0 ≤ lam)
    {i : Fin n}
    (hiS : i ∉ S)
    (hiTail : k ≤ i.1)
    (htLower : lam ≤ t)
    (htUpper : t ≤ a i) :
    let p : (Fin n → ℝ) × (Fin n → ℝ) :=
      ((fun j ↦ if j = i then 1 else if j ∈ C then 1 else 0),
        fun j ↦ if j = i then t else if j ∈ C then a j else 0)
    p ∈ exercise715StageFace k b a C (insert i S) (insert i L) lam := by
  classical
  let p : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C then 1 else 0),
      fun j ↦ if j = i then t else if j ∈ C then a j else 0)
  have hiC : i ∉ C := by
    intro hi
    exact not_le_of_gt (hCsub hi) hiTail
  have hiL : i ∉ L := fun hi ↦ hiS (hLsub hi)
  have htNonneg : 0 ≤ t := le_trans hlam_nonneg htLower
  have hInsertSub : ∀ ⦃j : Fin n⦄, j ∈ insert i S → k ≤ j.1 := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hjS
    · simpa [hji] using hiTail
    · exact hSsub hjS
  have hsumC : ∑ j ∈ C, p.2 j = C.sum a := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := by
      intro hEq
      subst hEq
      exact hiC hj
    simp [p, hji, hj]
  have hpStage : p ∈ exercise715StageSet k b a (insert i S) := by
    refine (mem_exercise715StageSet_iff k b a (insert i S) p).mpr ⟨?_, ?_⟩
    refine (mem_exercise_7_15_mixed_integer_set_iff k b a p).mpr ⟨?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · simp [p, hji]
      · by_cases hjC : j ∈ C
        · simp [p, hji, hjC]
        · simp [p, hji, hjC]
    · intro j
      by_cases hji : j = i
      · simpa [p, hji] using htNonneg
      · by_cases hjC : j ∈ C
        · simpa [p, hji, hjC] using ha_nonneg j
        · simp [p, hji, hjC]
    · have hCsubset : C ⊆ exercise_7_15_head_indices k := by
        intro j hj
        exact (mem_exercise_7_15_head_indices_iff k j).2 (hCsub hj)
      have hheadEq :
          ∑ j ∈ exercise_7_15_head_indices k, p.2 j = C.sum a := by
        calc
          ∑ j ∈ exercise_7_15_head_indices k, p.2 j =
              (∑ j ∈ C, p.2 j) +
                ∑ j ∈ exercise_7_15_head_indices k \ C, p.2 j := by
                  simpa [add_comm] using
                    (Finset.sum_sdiff
                      (s₁ := C)
                      (s₂ := exercise_7_15_head_indices k)
                      (f := fun j ↦ p.2 j)
                      hCsubset).symm
          _ = C.sum a := by
            rw [hsumC]
            have hzero :
                ∑ j ∈ exercise_7_15_head_indices k \ C, p.2 j = 0 := by
              refine Finset.sum_eq_zero ?_
              intro j hj
              have hjC : j ∉ C := (Finset.mem_sdiff.mp hj).2
              have hjHead : j.1 < k :=
                (mem_exercise_7_15_head_indices_iff k j).mp (Finset.mem_sdiff.mp hj).1
              have hji : j ≠ i := by
                intro hEq
                subst hEq
                exact not_lt_of_ge hiTail hjHead
              simp [p, hji, hjC]
            rw [hzero, add_zero]
      have hiTailMem : i ∈ exercise_7_15_tail_indices k :=
        (mem_exercise_7_15_tail_indices_iff k i).2 hiTail
      have htailEq :
          ∑ j ∈ exercise_7_15_tail_indices k, p.2 j = t := by
        rw [Finset.sum_eq_single i]
        · simp [p]
        · intro j hj hji
          have hjC : j ∉ C := by
            intro hjC
            exact not_le_of_gt (hCsub hjC)
              ((mem_exercise_7_15_tail_indices_iff k j).mp hj)
          simp [p, hji, hjC]
        · intro hiNotTail
          exact False.elim (hiNotTail hiTailMem)
      rw [hheadEq, htailEq, hcover]
      linarith
    · intro j
      by_cases hji : j = i
      · subst hji
        simpa [p] using htUpper
      · by_cases hjC : j ∈ C
        · simp [p, hji, hjC]
        · simp [p, hji, hjC]
    · intro j hjTail hjNotInsert
      have hji : j ≠ i := by
        intro hEq
        subst hEq
        exact hjNotInsert (Finset.mem_insert_self j S)
      have hjC : j ∉ C := by
        intro hjC
        exact not_le_of_gt (hCsub hjC) hjTail
      simp [p, hji, hjC]
  have hreleasedZero :
      ∑ j ∈ insert i S \ insert i L, p.2 j = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hjData := Finset.mem_sdiff.mp hj
    have hji : j ≠ i := by
      intro hEq
      subst hEq
      exact hjData.2 (Finset.mem_insert_self j L)
    have hjTail : k ≤ j.1 := hInsertSub hjData.1
    have hjC : j ∉ C := by
      intro hjC
      exact not_le_of_gt (hCsub hjC) hjTail
    simp [p, hji, hjC]
  have hpenaltyZero :
      ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hji : j ≠ i := by
      intro hEq
      subst hEq
      exact hiC hj
    simp [p, hji, hj]
  have hliftedSum :
      ∑ j ∈ insert i L, lam * p.1 j = lam := by
    rw [Finset.sum_insert hiL]
    have hsumL : ∑ j ∈ L, lam * p.1 j = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hjTail : k ≤ j.1 := hSsub (hLsub hj)
      have hjC : j ∉ C := by
        intro hjC
        exact not_le_of_gt (hCsub hjC) hjTail
      have hji : j ≠ i := by
        intro hEq
        subst hEq
        exact hiL hj
      simp [p, hji, hjC]
    rw [hsumL]
    simp [p]
  have hvalue : exercise715StageValue a C (insert i S) (insert i L) lam p = b := by
    -- On this point the full cover contributes `b + lam`, while the lifted selector pays `lam`.
    rw [exercise715StageValue, hsumC, hreleasedZero, hpenaltyZero, hliftedSum, hcover]
    ring
  -- The explicit mixed-integer point therefore lies on the new equality face.
  exact (mem_exercise715StageFace_iff k b a C (insert i S) (insert i L) lam p).mpr
    ⟨subset_convexHull ℝ _ hpStage, hvalue⟩

/-- Helper for Exercise 7.15: evaluation of the released-tail coordinate is linear on the product
space. -/
theorem exercise715TailCoordinateLinearMap_map_add
    (i : Fin n)
    (p q : (Fin n → ℝ) × (Fin n → ℝ)) :
    (p + q).2 i = p.2 i + q.2 i := by
  -- Product-space addition acts coordinatewise on the released `y_i` coordinate.
  simp

/-- Helper for Exercise 7.15: released-tail coordinate evaluation commutes with scalar
multiplication. -/
theorem exercise715TailCoordinateLinearMap_map_smul
    (i : Fin n)
    (t : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (t • p).2 i = t * p.2 i := by
  -- Product-space scalar multiplication also acts coordinatewise on the released `y_i`
  -- coordinate.
  simp

/-- Helper for Exercise 7.15: the linear map extracting the released-tail coordinate `y_i`. -/
def exercise715TailCoordinateLinearMap
    (i : Fin n) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
  { toFun := fun p ↦ p.2 i
    map_add' := exercise715TailCoordinateLinearMap_map_add i
    map_smul' := exercise715TailCoordinateLinearMap_map_smul i }

/-- Helper for Exercise 7.15: evaluation of a selector coordinate is additive on the product
space. -/
theorem exercise715SelectorCoordinateLinearMap_map_add
    (i : Fin n)
    (p q : (Fin n → ℝ) × (Fin n → ℝ)) :
    (p + q).1 i = p.1 i + q.1 i := by
  -- Product-space addition acts coordinatewise on the selector coordinate.
  simp

/-- Helper for Exercise 7.15: selector-coordinate evaluation commutes with scalar
multiplication. -/
theorem exercise715SelectorCoordinateLinearMap_map_smul
    (i : Fin n)
    (t : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (t • p).1 i = t * p.1 i := by
  -- Product-space scalar multiplication acts coordinatewise on the selector coordinate.
  simp

/-- Helper for Exercise 7.15: the linear map extracting the selector coordinate `x_i`. -/
def exercise715SelectorCoordinateLinearMap
    (i : Fin n) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
  { toFun := fun p ↦ p.1 i
    map_add' := exercise715SelectorCoordinateLinearMap_map_add i
    map_smul' := exercise715SelectorCoordinateLinearMap_map_smul i }

/-- Helper for Exercise 7.15: the linear projection that replaces `x_i` by zero and leaves all
other coordinates unchanged. -/
def exercise715ZeroSelectorLinearMap
    (i : Fin n) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ]
      ((Fin n → ℝ) × (Fin n → ℝ)) :=
  LinearMap.id -
    (exercise715SelectorCoordinateLinearMap i).smulRight
      ((Pi.single i (1 : ℝ), 0) : (Fin n → ℝ) × (Fin n → ℝ))

/-- Helper for Exercise 7.15: the zero-selector projection sets its chosen selector coordinate to
zero and preserves every other selector coordinate. -/
theorem exercise715ZeroSelectorLinearMap_fst_apply
    (i j : Fin n)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (exercise715ZeroSelectorLinearMap i p).1 j = if j = i then 0 else p.1 j := by
  by_cases hji : j = i
  · subst hji
    simp [exercise715ZeroSelectorLinearMap, exercise715SelectorCoordinateLinearMap]
  · simp [exercise715ZeroSelectorLinearMap, exercise715SelectorCoordinateLinearMap, hji]

/-- Helper for Exercise 7.15: the zero-selector projection leaves the entire flow block
unchanged. -/
theorem exercise715ZeroSelectorLinearMap_snd_apply
    (i : Fin n)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (exercise715ZeroSelectorLinearMap i p).2 = p.2 := by
  -- The subtracted standard-basis vector has zero flow component.
  simp [exercise715ZeroSelectorLinearMap, exercise715SelectorCoordinateLinearMap]

/-- Helper for Exercise 7.15: the linear coordinate subspace in which precisely the unreleased
tail-flow coordinates vanish. -/
def exercise715StageCoordinateSubmodule
    (k : ℕ) (S : Finset (Fin n)) :
    Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ⨅ j, ⨅ (_ : k ≤ j.1 ∧ j ∉ S), LinearMap.ker (exercise715TailCoordinateLinearMap j)

/-- Helper for Exercise 7.15: membership in the staged coordinate subspace is exactly vanishing
of every unreleased tail-flow coordinate. -/
theorem mem_exercise715StageCoordinateSubmodule_iff
    (k : ℕ) (S : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ exercise715StageCoordinateSubmodule k S ↔
      ∀ j, k ≤ j.1 → j ∉ S → p.2 j = 0 := by
  -- Membership in the iterated infimum of coordinate kernels is pointwise vanishing.
  simp [exercise715StageCoordinateSubmodule, exercise715TailCoordinateLinearMap]

/-- Helper for Exercise 7.15: the staged inequality is an affine functional with this linear
part. -/
theorem exercise715StageLinearMap_map_add
    (a : Fin n → ℝ) (C S L : Finset (Fin n)) (lam : ℝ)
    (p q : (Fin n → ℝ) × (Fin n → ℝ)) :
    (((Finset.sum C fun j ↦ (p + q).2 j) -
          (Finset.sum (S \ L) fun j ↦ (p + q).2 j)) -
        (Finset.sum C fun j ↦ max (a j - lam) 0 * (p + q).1 j) -
          (Finset.sum L fun j ↦ lam * (p + q).1 j)) =
      (((Finset.sum C fun j ↦ p.2 j) -
            (Finset.sum (S \ L) fun j ↦ p.2 j)) -
          (Finset.sum C fun j ↦ max (a j - lam) 0 * p.1 j) -
            (Finset.sum L fun j ↦ lam * p.1 j)) +
        (((Finset.sum C fun j ↦ q.2 j) -
              (Finset.sum (S \ L) fun j ↦ q.2 j)) -
            (Finset.sum C fun j ↦ max (a j - lam) 0 * q.1 j) -
              (Finset.sum L fun j ↦ lam * q.1 j)) := by
  -- Expanding the four sums shows that the staged linear part is additive.
  simp [Finset.sum_add_distrib, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add]

/-- Helper for Exercise 7.15: the staged linear part is homogeneous. -/
theorem exercise715StageLinearMap_map_smul
    (a : Fin n → ℝ) (C S L : Finset (Fin n)) (lam : ℝ)
    (t : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (((Finset.sum C fun j ↦ (t • p).2 j) -
          (Finset.sum (S \ L) fun j ↦ (t • p).2 j)) -
        (Finset.sum C fun j ↦ max (a j - lam) 0 * (t • p).1 j) -
          (Finset.sum L fun j ↦ lam * (t • p).1 j)) =
      t *
        (((Finset.sum C fun j ↦ p.2 j) -
              (Finset.sum (S \ L) fun j ↦ p.2 j)) -
            (Finset.sum C fun j ↦ max (a j - lam) 0 * p.1 j) -
              (Finset.sum L fun j ↦ lam * p.1 j)) := by
  -- Push the scalar through each finite sum and factor the common multiplier.
  calc
    (((Finset.sum C fun j ↦ (t • p).2 j) -
          (Finset.sum (S \ L) fun j ↦ (t • p).2 j)) -
        (Finset.sum C fun j ↦ max (a j - lam) 0 * (t • p).1 j) -
          (Finset.sum L fun j ↦ lam * (t • p).1 j)) =
        (((Finset.sum C fun j ↦ t * p.2 j) -
              (Finset.sum (S \ L) fun j ↦ t * p.2 j)) -
            (Finset.sum C fun j ↦ t * (max (a j - lam) 0 * p.1 j)) -
              (Finset.sum L fun j ↦ t * (lam * p.1 j))) := by
          simp [Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm]
    _ = ((t * ∑ j ∈ C, p.2 j) -
            (t * ∑ j ∈ S \ L, p.2 j)) -
          (t * ∑ j ∈ C, max (a j - lam) 0 * p.1 j) -
            (t * ∑ j ∈ L, lam * p.1 j) := by
              simp [Finset.mul_sum, Finset.sum_mul, sub_eq_add_neg, mul_assoc]
    _ = t *
          (((Finset.sum C fun j ↦ p.2 j) -
                (Finset.sum (S \ L) fun j ↦ p.2 j)) -
              (Finset.sum C fun j ↦ max (a j - lam) 0 * p.1 j) -
                (Finset.sum L fun j ↦ lam * p.1 j)) := by
          ring

/-- Helper for Exercise 7.15: the linear part of the staged supporting functional. -/
def exercise715StageLinearMap
    (a : Fin n → ℝ) (C S L : Finset (Fin n)) (lam : ℝ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ :=
  { toFun := fun p ↦
      ((Finset.sum C fun j ↦ p.2 j) -
        (Finset.sum (S \ L) fun j ↦ p.2 j)) -
          (Finset.sum C fun j ↦ max (a j - lam) 0 * p.1 j) -
            (Finset.sum L fun j ↦ lam * p.1 j)
    map_add' := exercise715StageLinearMap_map_add a C S L lam
    map_smul' := exercise715StageLinearMap_map_smul a C S L lam }

/-- Helper for Exercise 7.15: `exercise715StageValue` is the staged linear part plus a constant
offset. -/
theorem exercise715StageValue_eq_linear_part_add_constant
    (a : Fin n → ℝ) (C S L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    exercise715StageValue a C S L lam p =
      exercise715StageLinearMap a C S L lam p +
        ∑ j ∈ C, max (a j - lam) 0 := by
  have hpenalty :
      ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) =
        (∑ j ∈ C, max (a j - lam) 0) -
          ∑ j ∈ C, max (a j - lam) 0 * p.1 j := by
    -- Split the positive-part penalty into its constant and linear pieces.
    calc
      ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) =
          ∑ j ∈ C, (max (a j - lam) 0 - max (a j - lam) 0 * p.1 j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ = (∑ j ∈ C, max (a j - lam) 0) -
            ∑ j ∈ C, max (a j - lam) 0 * p.1 j := by
              rw [Finset.sum_sub_distrib]
  -- After expanding the penalty, only a constant remains outside the staged linear part.
  simp [exercise715StageValue, exercise715StageLinearMap, hpenalty]
  ring

/-- Helper for Exercise 7.15: the staged inequality is valid on every mixed-integer generator
whose released and lifted sets consist of tail indices. -/
theorem exercise715StageValue_le_of_mem_stageSet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (hLsub : L ⊆ S)
    (hcover : C.sum a = b + lam)
    (hlam_pos : 0 < lam)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ exercise715StageSet k b a S) :
    exercise715StageValue a C S L lam p ≤ b := by
  classical
  rcases (mem_exercise715StageSet_iff k b a S p).mp hp with ⟨hpMixed, hfreeze⟩
  rcases (mem_exercise_7_15_mixed_integer_set_iff k b a p).mp hpMixed with
    ⟨hxBinary, hyNonneg, hbalance, hcapacity⟩
  have hCsubset : C ⊆ exercise_7_15_head_indices k := by
    intro j hj
    exact (mem_exercise_7_15_head_indices_iff k j).2 (hCsub hj)
  have hSsubset : S ⊆ exercise_7_15_tail_indices k := by
    intro j hj
    exact (mem_exercise_7_15_tail_indices_iff k j).2 (hSsub hj)
  have hcoverTerm :
      ∀ j ∈ C,
        p.2 j + max (a j - lam) 0 * (1 - p.1 j) ≤ a j := by
    intro j hj
    rcases hxBinary j with hxZero | hxOne
    · have hyZero : p.2 j = 0 := by
        have hyLe : p.2 j ≤ 0 := by
          simpa [hxZero] using hcapacity j
        exact le_antisymm hyLe (hyNonneg j)
      have hmaxLe : max (a j - lam) 0 ≤ a j := by
        exact max_le (by linarith) (ha_nonneg j)
      simpa [hxZero, hyZero] using hmaxLe
    · simpa [hxOne] using hcapacity j
  have hcoverSum :
      (∑ j ∈ C, p.2 j) +
          ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) ≤
        C.sum a := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hcoverTerm
  by_cases hactive : ∃ i ∈ L, p.1 i = 1
  · rcases hactive with ⟨i, hiL, hxi⟩
    have hxNonneg : ∀ j ∈ L, 0 ≤ p.1 j := by
      intro j hj
      rcases hxBinary j with hxZero | hxOne
      · simp [hxZero]
      · simp [hxOne]
    have hliftedLower : lam ≤ ∑ j ∈ L, lam * p.1 j := by
      have htermNonneg : ∀ j ∈ L, 0 ≤ lam * p.1 j := by
        intro j hj
        exact mul_nonneg hlam_pos.le (hxNonneg j hj)
      calc
        lam = lam * p.1 i := by rw [hxi, mul_one]
        _ ≤ ∑ j ∈ L, lam * p.1 j := by
          exact Finset.single_le_sum htermNonneg hiL
    have hreleasedNonneg : 0 ≤ ∑ j ∈ S \ L, p.2 j := by
      exact Finset.sum_nonneg fun j hj ↦ hyNonneg j
    -- An active lifted selector pays at least one full `lam`; the remaining cover terms are
    -- bounded by the total cover capacity `b + lam`.
    rw [exercise715StageValue]
    linarith [hcoverSum]
  · have hxLiftedZero : ∀ j ∈ L, p.1 j = 0 := by
      intro j hj
      rcases hxBinary j with hxZero | hxOne
      · exact hxZero
      · exact False.elim (hactive ⟨j, hj, hxOne⟩)
    have hyLiftedZero : ∀ j ∈ L, p.2 j = 0 := by
      intro j hj
      have hyLe : p.2 j ≤ 0 := by
        simpa [hxLiftedZero j hj] using hcapacity j
      exact le_antisymm hyLe (hyNonneg j)
    have htailSum :
        ∑ j ∈ S \ L, p.2 j =
          ∑ j ∈ exercise_7_15_tail_indices k, p.2 j := by
      refine Finset.sum_subset ?_ ?_
      · intro j hj
        exact hSsubset (Finset.mem_sdiff.mp hj).1
      · intro j hjTail hjNotReleased
        by_cases hjS : j ∈ S
        · have hjL : j ∈ L := by
            by_contra hjNotL
            exact hjNotReleased (Finset.mem_sdiff.mpr ⟨hjS, hjNotL⟩)
          exact hyLiftedZero j hjL
        · exact hfreeze j ((mem_exercise_7_15_tail_indices_iff k j).mp hjTail) hjS
    have hcoverBalance :
        (∑ j ∈ C, p.2 j) - ∑ j ∈ S \ L, p.2 j ≤ b := by
      have hheadOutsideNonneg :
          0 ≤ ∑ j ∈ exercise_7_15_head_indices k \ C, p.2 j := by
        exact Finset.sum_nonneg fun j hj ↦ hyNonneg j
      have hheadSplit :
          ∑ j ∈ exercise_7_15_head_indices k, p.2 j =
            (∑ j ∈ C, p.2 j) +
              ∑ j ∈ exercise_7_15_head_indices k \ C, p.2 j := by
        simpa [add_comm] using
          (Finset.sum_sdiff
            (s₁ := C)
            (s₂ := exercise_7_15_head_indices k)
            (f := fun j ↦ p.2 j)
            hCsubset).symm
      rw [hheadSplit, ← htailSum] at hbalance
      linarith
    let M : Finset (Fin n) := C.filter (fun j ↦ p.1 j = 0)
    have hpenaltyEq :
        ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) =
          ∑ j ∈ M, max (a j - lam) 0 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rcases hxBinary j with hxZero | hxOne
      · simp [hxZero]
      · simp [hxOne]
    have hweightedEq :
        ∑ j ∈ C, a j * p.1 j = C.sum a - M.sum a := by
      have hsplit :
          C.sum a = M.sum a + (C.filter (fun j ↦ p.1 j ≠ 0)).sum a := by
        simpa [M, add_comm, add_left_comm, add_assoc] using
          (Finset.sum_filter_add_sum_filter_not
            (s := C) (p := fun j ↦ p.1 j = 0) a).symm
      calc
        ∑ j ∈ C, a j * p.1 j = (C.filter (fun j ↦ p.1 j ≠ 0)).sum a := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro j hj
          rcases hxBinary j with hxZero | hxOne
          · simp [hxZero]
          · simp [hxOne]
        _ = C.sum a - M.sum a := by linarith
    have hflowLeGap :
        (∑ j ∈ C, p.2 j) - ∑ j ∈ S \ L, p.2 j ≤
          b - max (M.sum a - lam) 0 := by
      have hcapacityBound :
          (∑ j ∈ C, p.2 j) - ∑ j ∈ S \ L, p.2 j ≤
            b - (M.sum a - lam) := by
        have hreleasedNonneg : 0 ≤ ∑ j ∈ S \ L, p.2 j := by
          exact Finset.sum_nonneg fun j hj ↦ hyNonneg j
        have hsumCap : ∑ j ∈ C, p.2 j ≤ ∑ j ∈ C, a j * p.1 j := by
          exact Finset.sum_le_sum fun j hj ↦ hcapacity j
        calc
          (∑ j ∈ C, p.2 j) - ∑ j ∈ S \ L, p.2 j ≤
              (∑ j ∈ C, a j * p.1 j) - ∑ j ∈ S \ L, p.2 j := by
                exact sub_le_sub_right hsumCap _
          _ ≤ ∑ j ∈ C, a j * p.1 j := by linarith
          _ = b - (M.sum a - lam) := by
                rw [hweightedEq, hcover]
                ring
      by_cases hgap : 0 ≤ M.sum a - lam
      · rwa [max_eq_left hgap]
      · rw [max_eq_right (le_of_not_ge hgap)]
        simpa using hcoverBalance
    have hpenaltyLe :
        ∑ j ∈ M, max (a j - lam) 0 ≤ max (M.sum a - lam) 0 :=
      coverPenalty_le_missingGap a lam M ha_nonneg hlam_pos
    have hliftedSumZero : ∑ j ∈ L, lam * p.1 j = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      simp [hxLiftedZero j hj]
    -- With no active lifted selector, all lifted flows vanish and the ordinary flow-cover
    -- missing-set estimate combines with the signed-balance bound.
    rw [exercise715StageValue, hpenaltyEq, hliftedSumZero]
    linarith

/-- Helper for Exercise 7.15: staged validity extends from the mixed-integer generators to their
real convex hull. -/
theorem exercise715StageValue_le_of_mem_convexHull
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (hLsub : L ⊆ S)
    (hcover : C.sum a = b + lam)
    (hlam_pos : 0 < lam)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ convexHull ℝ (exercise715StageSet k b a S)) :
    exercise715StageValue a C S L lam p ≤ b := by
  let A := exercise715StageLinearMap a C S L lam
  let c : ℝ := ∑ j ∈ C, max (a j - lam) 0
  let H : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {q | A q ≤ b - c}
  have hsplit :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        exercise715StageValue a C S L lam q = A q + c := by
    intro q
    simpa [A, c] using exercise715StageValue_eq_linear_part_add_constant a C S L lam q
  have hconvex : Convex ℝ H := by
    simpa [H] using convex_halfSpace_le A.isLinear (b - c)
  have hsubset : exercise715StageSet k b a S ⊆ H := by
    intro q hq
    have hqValid :=
      exercise715StageValue_le_of_mem_stageSet
        k b a C S L lam ha_nonneg hCsub hSsub hLsub hcover hlam_pos hq
    have hqSplit := hsplit q
    dsimp [H]
    linarith
  have hpH : p ∈ H := convexHull_min hsubset hconvex hp
  have hpSplit := hsplit p
  dsimp [H] at hpH
  linarith

/-- Helper for Exercise 7.15: the origin belongs to every staged mixed-integer set when `b` is
nonnegative. -/
theorem exercise715ZeroPoint_mem_stageSet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hb_nonneg : 0 ≤ b) :
    ((0, 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ exercise715StageSet k b a S := by
  -- All flow coordinates vanish, so the mixed constraints and every stage freeze are immediate.
  rw [mem_exercise715StageSet_iff, mem_exercise_7_15_mixed_integer_set_iff]
  simp [hb_nonneg]

/-- Helper for Exercise 7.15: every selector standard-basis point belongs to every staged set
when capacities are nonnegative and `b` is nonnegative. -/
theorem exercise715SelectorBasisPoint_mem_stageSet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hb_nonneg : 0 ≤ b)
    (i : Fin n) :
    ((Pi.single i (1 : ℝ), 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈
      exercise715StageSet k b a S := by
  rw [mem_exercise715StageSet_iff, mem_exercise_7_15_mixed_integer_set_iff]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [Pi.single_eq_of_ne hji]
  · simp
  · simpa using hb_nonneg
  · intro j
    by_cases hji : j = i
    · change 0 ≤ a j * (Pi.single i (1 : ℝ) : Fin n → ℝ) j
      rw [hji, Pi.single_eq_same, mul_one]
      exact ha_nonneg i
    · simp [Pi.single_eq_of_ne hji]
  · intro j hjTail hjS
    simp

/-- Helper for Exercise 7.15: a positive standard-basis flow point is feasible on every head
coordinate and on every released tail coordinate. -/
theorem exercise715FlowBasisPoint_mem_stageSet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hb : 0 < b)
    (ha : ∀ j, 0 < a j)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (i : Fin n)
    (hiAllowed : i.1 < k ∨ i ∈ S) :
    let t := min (a i) b
    ((Pi.single i (1 : ℝ), Pi.single i t) :
        (Fin n → ℝ) × (Fin n → ℝ)) ∈ exercise715StageSet k b a S := by
  let t : ℝ := min (a i) b
  have ht_pos : 0 < t := lt_min (ha i) hb
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have ht_le_ai : t ≤ a i := min_le_left _ _
  have ht_le_b : t ≤ b := min_le_right _ _
  have hpMixed :
      ((Pi.single i (1 : ℝ), Pi.single i t) :
          (Fin n → ℝ) × (Fin n → ℝ)) ∈
        exercise_7_15_mixed_integer_set k b a := by
    rw [mem_exercise_7_15_mixed_integer_set_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst hji
        simp
      · simp [Pi.single_eq_of_ne hji]
    · intro j
      by_cases hji : j = i
      · subst hji
        simpa using ht_nonneg
      · simp [Pi.single_eq_of_ne hji]
    · rcases hiAllowed with hiHead | hiS
      · have hiHeadMem : i ∈ exercise_7_15_head_indices k :=
          (mem_exercise_7_15_head_indices_iff k i).2 hiHead
        have hiNotTail : i ∉ exercise_7_15_tail_indices k := by
          intro hiTail
          exact not_le_of_gt hiHead ((mem_exercise_7_15_tail_indices_iff k i).mp hiTail)
        simpa [Finset.sum_ite_irrel, Pi.single_apply, hiHeadMem, hiNotTail] using ht_le_b
      · have hiTail : k ≤ i.1 := hSsub hiS
        have hiTailMem : i ∈ exercise_7_15_tail_indices k :=
          (mem_exercise_7_15_tail_indices_iff k i).2 hiTail
        have hiNotHead : i ∉ exercise_7_15_head_indices k := by
          intro hiHead
          exact not_le_of_gt ((mem_exercise_7_15_head_indices_iff k i).mp hiHead) hiTail
        have hneg : -t ≤ b := by linarith
        simpa [Finset.sum_ite_irrel, Pi.single_apply, hiTailMem, hiNotHead] using hneg
    · intro j
      by_cases hji : j = i
      · subst hji
        simpa using ht_le_ai
      · simp [Pi.single_eq_of_ne hji, ha j]
  refine (mem_exercise715StageSet_iff k b a S _).mpr ⟨hpMixed, ?_⟩
  intro j hjTail hjNotS
  have hji : j ≠ i := by
    intro hEq
    subst hEq
    rcases hiAllowed with hiHead | hiS
    · exact not_le_of_gt hiHead hjTail
    · exact hjNotS hiS
  -- Only the allowed coordinate `i` carries flow, so every unreleased tail remains frozen.
  simp [Pi.single_eq_of_ne hji]

/-- Helper for Exercise 7.15: the direction of a staged ambient affine span is exactly the
coordinate subspace obtained by freezing the unreleased tail-flow coordinates. -/
theorem exercise715StageSet_direction_affineSpan_eq
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hb : 0 < b)
    (ha : ∀ j, 0 < a j)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1) :
    (affineSpan ℝ (convexHull ℝ (exercise715StageSet k b a S))).direction =
      exercise715StageCoordinateSubmodule k S := by
  classical
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (exercise715StageSet k b a S)
  let D : Submodule ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (affineSpan ℝ P).direction
  have hzeroP : ((0, 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ P := by
    exact subset_convexHull ℝ _ (exercise715ZeroPoint_mem_stageSet k b a S hb.le)
  have hzeroAff :
      ((0, 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ affineSpan ℝ P :=
    subset_affineSpan ℝ _ hzeroP
  have hxBasis :
      ∀ i : Fin n,
        ((Pi.single i (1 : ℝ), 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ D := by
    intro i
    have hpointP :
        ((Pi.single i (1 : ℝ), 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ P := by
      exact subset_convexHull ℝ _
        (exercise715SelectorBasisPoint_mem_stageSet k b a S (fun j ↦ (ha j).le) hb.le i)
    have hpointAff :
        ((Pi.single i (1 : ℝ), 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈
          affineSpan ℝ P := subset_affineSpan ℝ _ hpointP
    rw [show D = (affineSpan ℝ P).direction by rfl]
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hzeroAff]
    refine ⟨(Pi.single i (1 : ℝ), 0), hpointAff, ?_⟩
    simp [vsub_eq_sub]
  have hyBasis :
      ∀ i : Fin n, i.1 < k ∨ i ∈ S →
        ((0, Pi.single i (1 : ℝ)) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ D := by
    intro i hiAllowed
    let t : ℝ := min (a i) b
    have ht_pos : 0 < t := lt_min (ha i) hb
    have hxPointP :
        ((Pi.single i (1 : ℝ), 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ P := by
      exact subset_convexHull ℝ _
        (exercise715SelectorBasisPoint_mem_stageSet k b a S (fun j ↦ (ha j).le) hb.le i)
    have hflowPointP :
        ((Pi.single i (1 : ℝ), Pi.single i t) :
            (Fin n → ℝ) × (Fin n → ℝ)) ∈ P := by
      exact subset_convexHull ℝ _
        (exercise715FlowBasisPoint_mem_stageSet k b a S hb ha hSsub i hiAllowed)
    have hxPointAff :
        ((Pi.single i (1 : ℝ), 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈
          affineSpan ℝ P := subset_affineSpan ℝ _ hxPointP
    have hflowPointAff :
        ((Pi.single i (1 : ℝ), Pi.single i t) :
            (Fin n → ℝ) × (Fin n → ℝ)) ∈ affineSpan ℝ P :=
      subset_affineSpan ℝ _ hflowPointP
    have hscaledFlow :
        ((0, Pi.single i t) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ D := by
      rw [show D = (affineSpan ℝ P).direction by rfl]
      rw [AffineSubspace.mem_direction_iff_eq_vsub_right hxPointAff]
      refine ⟨(Pi.single i (1 : ℝ), Pi.single i t), hflowPointAff, ?_⟩
      simp [vsub_eq_sub]
    have hnormalized := D.smul_mem t⁻¹ hscaledFlow
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have hnormalize : t⁻¹ • Pi.single i t = Pi.single i (1 : ℝ) := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [ht_ne]
      · simp [Pi.single_eq_of_ne hji]
    have hnormalizePair :
        t⁻¹ • ((0, Pi.single i t) : (Fin n → ℝ) × (Fin n → ℝ)) =
          (0, Pi.single i (1 : ℝ)) := by
      apply Prod.ext
      · simp
      · exact hnormalize
    rw [hnormalizePair] at hnormalized
    exact hnormalized
  apply le_antisymm
  · have hstageSubset :
        exercise715StageSet k b a S ⊆
          (exercise715StageCoordinateSubmodule k S :
            Set ((Fin n → ℝ) × (Fin n → ℝ))) := by
      intro p hp
      rcases (mem_exercise715StageSet_iff k b a S p).mp hp with ⟨hpMixed, hfreeze⟩
      exact (mem_exercise715StageCoordinateSubmodule_iff k S p).2 hfreeze
    have hconvSubset :
        P ⊆
          (exercise715StageCoordinateSubmodule k S :
            Set ((Fin n → ℝ) × (Fin n → ℝ))) := by
      exact convexHull_min hstageSubset (exercise715StageCoordinateSubmodule k S).convex
    have haffineLe :
        affineSpan ℝ P ≤ (exercise715StageCoordinateSubmodule k S).toAffineSubspace :=
      affineSpan_le.2 hconvSubset
    have hdirectionLe := AffineSubspace.direction_le haffineLe
    simpa [D, P] using hdirectionLe
  · intro p hp
    have hpFrozen := (mem_exercise715StageCoordinateSubmodule_iff k S p).1 hp
    have hxExpansion :
        p.1 = ∑ i : Fin n, p.1 i • Pi.single i (1 : ℝ) := by
      simpa using ((Pi.basisFun ℝ (Fin n)).sum_repr p.1).symm
    have hyExpansion :
        p.2 = ∑ i : Fin n, p.2 i • Pi.single i (1 : ℝ) := by
      simpa using ((Pi.basisFun ℝ (Fin n)).sum_repr p.2).symm
    have hxMem :
        ((p.1, 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ D := by
      have hsum :
          ∑ i : Fin n,
              p.1 i •
                ((Pi.single i (1 : ℝ), 0) :
                  (Fin n → ℝ) × (Fin n → ℝ)) ∈ D := by
        exact Submodule.sum_mem D fun i hi ↦ D.smul_mem (p.1 i) (hxBasis i)
      have hpairExpansion :
          ((p.1, 0) : (Fin n → ℝ) × (Fin n → ℝ)) =
            ∑ i : Fin n,
              p.1 i •
                ((Pi.single i (1 : ℝ), 0) :
                  (Fin n → ℝ) × (Fin n → ℝ)) := by
        apply Prod.ext
        · calc
            p.1 = ∑ i : Fin n, p.1 i • Pi.single i (1 : ℝ) := hxExpansion
            _ = (∑ i : Fin n,
                p.1 i •
                  ((Pi.single i (1 : ℝ), 0) :
                    (Fin n → ℝ) × (Fin n → ℝ))).1 := by
              rw [Prod.fst_sum]
              simp
        · rw [Prod.snd_sum]
          simp
      rw [hpairExpansion]
      exact hsum
    have hyMem :
        ((0, p.2) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ D := by
      have hsum :
          ∑ i : Fin n,
              p.2 i •
                ((0, Pi.single i (1 : ℝ)) :
                  (Fin n → ℝ) × (Fin n → ℝ)) ∈ D := by
        refine Submodule.sum_mem D ?_
        intro i hi
        by_cases hiAllowed : i.1 < k ∨ i ∈ S
        · exact D.smul_mem (p.2 i) (hyBasis i hiAllowed)
        · have hiTail : k ≤ i.1 := Nat.not_lt.mp (not_or.mp hiAllowed).1
          have hiS : i ∉ S := (not_or.mp hiAllowed).2
          have hpi : p.2 i = 0 := hpFrozen i hiTail hiS
          simp [hpi]
      have hpairExpansion :
          ((0, p.2) : (Fin n → ℝ) × (Fin n → ℝ)) =
            ∑ i : Fin n,
              p.2 i •
                ((0, Pi.single i (1 : ℝ)) :
                  (Fin n → ℝ) × (Fin n → ℝ)) := by
        apply Prod.ext
        · rw [Prod.fst_sum]
          simp
        · calc
            p.2 = ∑ i : Fin n, p.2 i • Pi.single i (1 : ℝ) := hyExpansion
            _ = (∑ i : Fin n,
                p.2 i •
                  ((0, Pi.single i (1 : ℝ)) :
                    (Fin n → ℝ) × (Fin n → ℝ))).2 := by
              rw [Prod.snd_sum]
              simp
      rw [hpairExpansion]
      exact hsum
    -- The two coordinate-block expansions reconstruct the arbitrary vector in the staged
    -- coordinate subspace.
    have hdecomp :
        p = ((p.1, 0) : (Fin n → ℝ) × (Fin n → ℝ)) + (0, p.2) := by
      ext <;> simp
    rw [hdecomp]
    simpa only [D, P] using D.add_mem hxMem hyMem

/-- Helper for Exercise 7.15: releasing one new tail-flow coordinate raises the staged ambient
affine dimension by exactly one. -/
theorem exercise715StageSet_finrank_direction_insert
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hb : 0 < b)
    (ha : ∀ j, 0 < a j)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    {i : Fin n}
    (hiS : i ∉ S)
    (hiTail : k ≤ i.1) :
    Module.finrank ℝ
        (affineSpan ℝ (convexHull ℝ (exercise715StageSet k b a (insert i S)))).direction =
      Module.finrank ℝ
          (affineSpan ℝ (convexHull ℝ (exercise715StageSet k b a S))).direction + 1 := by
  classical
  let eY : (Fin n → ℝ) × (Fin n → ℝ) := (0, Pi.single i (1 : ℝ))
  let Kold := exercise715StageCoordinateSubmodule (n := n) k S
  let Knew := exercise715StageCoordinateSubmodule (n := n) k (insert i S)
  have hKoldLe : Kold ≤ Knew := by
    intro p hp
    rw [mem_exercise715StageCoordinateSubmodule_iff] at hp ⊢
    intro j hjTail hjNotInsert
    exact hp j hjTail (fun hjS ↦ hjNotInsert (Finset.mem_insert_of_mem hjS))
  have heYNew : eY ∈ Knew := by
    rw [mem_exercise715StageCoordinateSubmodule_iff]
    intro j hjTail hjNotInsert
    have hji : j ≠ i := by
      intro hEq
      subst hEq
      exact hjNotInsert (by simp)
    simp [eY, Pi.single_eq_of_ne hji]
  have heYNotOld : eY ∉ Kold := by
    intro heY
    have hzero :=
      (mem_exercise715StageCoordinateSubmodule_iff k S eY).1 heY i hiTail hiS
    simpa [eY] using hzero
  have hKnewEq : Knew = Kold ⊔ Submodule.span ℝ {eY} := by
    apply le_antisymm
    · intro p hp
      let p0 : (Fin n → ℝ) × (Fin n → ℝ) := p - p.2 i • eY
      have hpNew := (mem_exercise715StageCoordinateSubmodule_iff k (insert i S) p).1 hp
      have hp0Old : p0 ∈ Kold := by
        rw [mem_exercise715StageCoordinateSubmodule_iff]
        intro j hjTail hjNotS
        by_cases hji : j = i
        · subst hji
          simp [p0, eY]
        · have hjNotInsert : j ∉ insert i S := by simp [hji, hjNotS]
          have hpj : p.2 j = 0 := hpNew j hjTail hjNotInsert
          simp [p0, eY, hpj, Pi.single_eq_of_ne hji]
      have hline : p.2 i • eY ∈ Submodule.span ℝ {eY} := by
        exact (Submodule.span ℝ {eY}).smul_mem (p.2 i) (Submodule.subset_span (by simp))
      have hp0Sup : p0 ∈ Kold ⊔ Submodule.span ℝ {eY} :=
        (show Kold ≤ Kold ⊔ Submodule.span ℝ {eY} from le_sup_left) hp0Old
      have hlineSup : p.2 i • eY ∈ Kold ⊔ Submodule.span ℝ {eY} :=
        (show Submodule.span ℝ {eY} ≤ Kold ⊔ Submodule.span ℝ {eY} from le_sup_right) hline
      have hpDecomp : p = p0 + p.2 i • eY := by
        apply Prod.ext
        · simp [p0, eY]
        · funext j
          by_cases hji : j = i
          · subst hji
            simp [p0, eY]
          · simp [p0, eY, Pi.single_eq_of_ne hji]
      rw [hpDecomp]
      exact (Kold ⊔ Submodule.span ℝ {eY}).add_mem hp0Sup hlineSup
    · refine sup_le hKoldLe ?_
      exact Submodule.span_le.2 (Set.singleton_subset_iff.2 heYNew)
  have hInsertSub :
      ∀ ⦃j : Fin n⦄, j ∈ insert i S → k ≤ j.1 := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hjS
    · simpa [hji] using hiTail
    · exact hSsub hjS
  rw [exercise715StageSet_direction_affineSpan_eq k b a (insert i S) hb ha hInsertSub,
    exercise715StageSet_direction_affineSpan_eq k b a S hb ha hSsub]
  change Module.finrank ℝ Knew = Module.finrank ℝ Kold + 1
  rw [hKnewEq]
  exact Submodule.finrank_sup_span_singleton heYNotOld

/-- Helper for Exercise 7.15: if an unreleased tail coordinate is projected to `x_i = 0`, a
staged mixed-integer generator remains in the same staged set. -/
theorem exercise715ZeroSelectorLinearMap_mem_stageSet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    {i : Fin n}
    (hiS : i ∉ S)
    (hiTail : k ≤ i.1)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ exercise715StageSet k b a S) :
    exercise715ZeroSelectorLinearMap i p ∈ exercise715StageSet k b a S := by
  rcases (mem_exercise715StageSet_iff k b a S p).mp hp with ⟨hpMixed, hfreeze⟩
  rcases (mem_exercise_7_15_mixed_integer_set_iff k b a p).mp hpMixed with
    ⟨hxBinary, hyNonneg, hbalance, hcapacity⟩
  have hyiZero : p.2 i = 0 := hfreeze i hiTail hiS
  refine (mem_exercise715StageSet_iff k b a S _).mpr ⟨?_, ?_⟩
  · refine (mem_exercise_7_15_mixed_integer_set_iff k b a _).mpr ⟨?_, ?_, ?_, ?_⟩
    · intro j
      rw [exercise715ZeroSelectorLinearMap_fst_apply]
      by_cases hji : j = i
      · simp [hji]
      · simpa [hji] using hxBinary j
    · intro j
      rw [exercise715ZeroSelectorLinearMap_snd_apply]
      exact hyNonneg j
    · simpa [exercise715ZeroSelectorLinearMap_snd_apply] using hbalance
    · intro j
      rw [exercise715ZeroSelectorLinearMap_snd_apply,
        exercise715ZeroSelectorLinearMap_fst_apply]
      by_cases hji : j = i
      · subst hji
        simp [hyiZero]
      · simpa [hji] using hcapacity j
  · intro j hjTail hjNotS
    rw [exercise715ZeroSelectorLinearMap_snd_apply]
    exact hfreeze j hjTail hjNotS

/-- Helper for Exercise 7.15: projecting an unreleased tail selector to zero maps the staged
convex hull into itself. -/
theorem exercise715ZeroSelectorLinearMap_mem_convexHull
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    {i : Fin n}
    (hiS : i ∉ S)
    (hiTail : k ≤ i.1)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ convexHull ℝ (exercise715StageSet k b a S)) :
    exercise715ZeroSelectorLinearMap i p ∈
      convexHull ℝ (exercise715StageSet k b a S) := by
  let R := exercise715ZeroSelectorLinearMap (n := n) i
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (exercise715StageSet k b a S)
  have hpreimageConvex : Convex ℝ (R ⁻¹' P) := by
    exact (convex_convexHull ℝ (exercise715StageSet k b a S)).linear_preimage R
  have hgenerators : exercise715StageSet k b a S ⊆ R ⁻¹' P := by
    intro q hq
    exact subset_convexHull ℝ _
      (exercise715ZeroSelectorLinearMap_mem_stageSet k b a S hiS hiTail hq)
  exact convexHull_min hgenerators hpreimageConvex hp

/-- Helper for Exercise 7.15: before an index is released, zeroing its selector leaves the staged
value unchanged. -/
theorem exercise715StageValue_zeroSelector
    (k : ℕ) (a : Fin n → ℝ) (C S L : Finset (Fin n)) (lam : ℝ)
    {i : Fin n}
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hLsub : L ⊆ S)
    (hiS : i ∉ S)
    (hiTail : k ≤ i.1)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    exercise715StageValue a C S L lam (exercise715ZeroSelectorLinearMap i p) =
      exercise715StageValue a C S L lam p := by
  have hiC : i ∉ C := by
    intro hiC
    exact not_le_of_gt (hCsub hiC) hiTail
  have hiL : i ∉ L := fun hiL ↦ hiS (hLsub hiL)
  have hcoverPenalty :
      ∑ j ∈ C,
          max (a j - lam) 0 * (1 - (exercise715ZeroSelectorLinearMap i p).1 j) =
        ∑ j ∈ C, max (a j - lam) 0 * (1 - p.1 j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [exercise715ZeroSelectorLinearMap_fst_apply]
    have hji : j ≠ i := fun hEq ↦ hiC (hEq ▸ hj)
    simp [hji]
  have hlifted :
      ∑ j ∈ L, lam * (exercise715ZeroSelectorLinearMap i p).1 j =
        ∑ j ∈ L, lam * p.1 j := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [exercise715ZeroSelectorLinearMap_fst_apply]
    have hji : j ≠ i := fun hEq ↦ hiL (hEq ▸ hj)
    simp [hji]
  -- The flow block is fixed, and neither selector sum is supported at the unreleased index.
  rw [exercise715StageValue, exercise715StageValue,
    exercise715ZeroSelectorLinearMap_snd_apply, hcoverPenalty, hlifted]

/-- Helper for Exercise 7.15: zeroing an unreleased tail selector sends every old staged-face
point into its `x_i = 0` slice. -/
theorem exercise715ZeroSelectorLinearMap_mem_stageFace
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hLsub : L ⊆ S)
    {i : Fin n}
    (hiS : i ∉ S)
    (hiTail : k ≤ i.1)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ exercise715StageFace k b a C S L lam) :
    exercise715ZeroSelectorLinearMap i p ∈ exercise715StageFace k b a C S L lam ∩
      {q | q.1 i = 0} := by
  rcases (mem_exercise715StageFace_iff k b a C S L lam p).mp hp with ⟨hpP, hpEq⟩
  refine ⟨(mem_exercise715StageFace_iff k b a C S L lam _ |>.2 ⟨?_, ?_⟩), ?_⟩
  · exact exercise715ZeroSelectorLinearMap_mem_convexHull k b a S hiS hiTail hpP
  · rw [exercise715StageValue_zeroSelector k a C S L lam hCsub hLsub hiS hiTail p]
    exact hpEq
  · simp [exercise715ZeroSelectorLinearMap_fst_apply]

/-- Helper for Exercise 7.15: slicing an old staged face by `x_i = 0` lowers its affine
dimension by at most one when `i` has not yet been released. -/
theorem exercise715StageFace_finrank_le_zeroSelectorSlice_add_one
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hLsub : L ⊆ S)
    {i : Fin n}
    (hiS : i ∉ S)
    (hiTail : k ≤ i.1)
    {p0 : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp0 : p0 ∈ exercise715StageFace k b a C S L lam) :
    Module.finrank ℝ (affineSpan ℝ (exercise715StageFace k b a C S L lam)).direction ≤
      Module.finrank ℝ
          (affineSpan ℝ
            (exercise715StageFace k b a C S L lam ∩ {q | q.1 i = 0})).direction + 1 := by
  let F : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    exercise715StageFace k b a C S L lam
  let Z : Set ((Fin n → ℝ) × (Fin n → ℝ)) := F ∩ {q | q.1 i = 0}
  let R := exercise715ZeroSelectorLinearMap (n := n) i
  let D := (affineSpan ℝ F).direction
  let DZ := (affineSpan ℝ Z).direction
  let RD := R.domRestrict D
  have hproject : ∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄, p ∈ F → R p ∈ Z := by
    intro p hp
    simpa [F, Z, R] using
      exercise715ZeroSelectorLinearMap_mem_stageFace
        k b a C S L lam hCsub hLsub hiS hiTail hp
  have himageSubset : R '' F ⊆ Z := by
    rintro q ⟨p, hp, rfl⟩
    exact hproject hp
  have hmapAffineLe :
      (affineSpan ℝ F).map R.toAffineMap ≤ affineSpan ℝ Z := by
    rw [AffineSubspace.map_span]
    exact affineSpan_mono ℝ himageSubset
  have hp0F : p0 ∈ F := by
    simpa [F] using hp0
  have hp0Aff : p0 ∈ affineSpan ℝ F :=
    subset_affineSpan ℝ F hp0F
  have hRp0Z : R p0 ∈ Z := hproject hp0
  have hRp0Aff : R p0 ∈ affineSpan ℝ Z := subset_affineSpan ℝ Z hRp0Z
  have hRDirection : ∀ v ∈ D, R v ∈ DZ := by
    intro v hv
    have hDDef : D = (affineSpan ℝ F).direction := rfl
    rw [hDDef] at hv
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hp0Aff] at hv
    rcases hv with ⟨q, hqAff, rfl⟩
    have hRqMap : R q ∈ (affineSpan ℝ F).map R.toAffineMap := by
      exact ⟨q, hqAff, rfl⟩
    have hRqAff : R q ∈ affineSpan ℝ Z := hmapAffineLe hRqMap
    have hdiff : R q - R p0 ∈ (affineSpan ℝ Z).direction := by
      simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hRqAff hRp0Aff
    simpa [R, DZ] using hdiff
  have hRangeLe : LinearMap.range RD ≤ DZ := by
    rintro v ⟨w, rfl⟩
    exact hRDirection w w.property
  have hRangeRank : Module.finrank ℝ (LinearMap.range RD) ≤ Module.finrank ℝ DZ :=
    Submodule.finrank_mono hRangeLe
  let X := exercise715SelectorCoordinateLinearMap (n := n) i
  let Kcoord : LinearMap.ker RD →ₗ[ℝ] ℝ :=
    X.comp (D.subtype.comp (LinearMap.ker RD).subtype)
  have hKcoordInjective : Function.Injective Kcoord := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    have huR : R (u : (Fin n → ℝ) × (Fin n → ℝ)) = 0 := by
      have huKernel := LinearMap.mem_ker.mp u.property
      exact huKernel
    have hvR : R (v : (Fin n → ℝ) × (Fin n → ℝ)) = 0 := by
      have hvKernel := LinearMap.mem_ker.mp v.property
      exact hvKernel
    apply Prod.ext
    · funext j
      by_cases hji : j = i
      · subst hji
        simpa [Kcoord, X, exercise715SelectorCoordinateLinearMap] using huv
      · have huCoord := congrArg (fun q : (Fin n → ℝ) × (Fin n → ℝ) ↦ q.1 j) huR
        have hvCoord := congrArg (fun q : (Fin n → ℝ) × (Fin n → ℝ) ↦ q.1 j) hvR
        change (exercise715ZeroSelectorLinearMap i (u :
          (Fin n → ℝ) × (Fin n → ℝ))).1 j = 0 at huCoord
        change (exercise715ZeroSelectorLinearMap i (v :
          (Fin n → ℝ) × (Fin n → ℝ))).1 j = 0 at hvCoord
        rw [exercise715ZeroSelectorLinearMap_fst_apply] at huCoord hvCoord
        simp [hji] at huCoord hvCoord
        rw [huCoord, hvCoord]
    · have huFlow := congrArg (fun q : (Fin n → ℝ) × (Fin n → ℝ) ↦ q.2) huR
      have hvFlow := congrArg (fun q : (Fin n → ℝ) × (Fin n → ℝ) ↦ q.2) hvR
      change (exercise715ZeroSelectorLinearMap i (u :
        (Fin n → ℝ) × (Fin n → ℝ))).2 = 0 at huFlow
      change (exercise715ZeroSelectorLinearMap i (v :
        (Fin n → ℝ) × (Fin n → ℝ))).2 = 0 at hvFlow
      rw [exercise715ZeroSelectorLinearMap_snd_apply] at huFlow hvFlow
      rw [huFlow, hvFlow]
  have hKernelRank : Module.finrank ℝ (LinearMap.ker RD) ≤ 1 := by
    simpa using Kcoord.finrank_le_finrank_of_injective hKcoordInjective
  have hRankNullity := RD.finrank_range_add_finrank_ker
  -- Rank-nullity bounds the lost selector direction by the one-dimensional kernel.
  change Module.finrank ℝ D ≤ Module.finrank ℝ DZ + 1
  omega

/-- Helper for Exercise 7.15: the all-one selector with zero flow is feasible at every stage. -/
theorem exercise715LoosePoint_mem_stageSet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    (hb_nonneg : 0 ≤ b)
    (ha_nonneg : ∀ j, 0 ≤ a j) :
    ((fun _ ↦ (1 : ℝ)), fun _ ↦ (0 : ℝ)) ∈ exercise715StageSet k b a S := by
  rw [mem_exercise715StageSet_iff, mem_exercise_7_15_mixed_integer_set_iff]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j
    exact Or.inr rfl
  · simp
  · simpa using hb_nonneg
  · intro j
    simpa using ha_nonneg j
  · intro j hjTail hjS
    rfl

/-- Helper for Exercise 7.15: every nonempty staged equality face has strictly smaller affine
dimension than its staged ambient hull when `b > 0` and `lam ≥ 0`. -/
theorem exercise715StageFace_finrank_lt_ambient
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ)
    (hb : 0 < b)
    (ha_nonneg : ∀ j, 0 ≤ a j)
    (hlam_nonneg : 0 ≤ lam)
    {p0 : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp0 : p0 ∈ exercise715StageFace k b a C S L lam) :
    Module.finrank ℝ (affineSpan ℝ (exercise715StageFace k b a C S L lam)).direction <
      Module.finrank ℝ
        (affineSpan ℝ (convexHull ℝ (exercise715StageSet k b a S))).direction := by
  let P : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (exercise715StageSet k b a S)
  let F : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    exercise715StageFace k b a C S L lam
  let A := exercise715StageLinearMap a C S L lam
  let c : ℝ := ∑ j ∈ C, max (a j - lam) 0
  let pLoose : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun _ ↦ (1 : ℝ)), fun _ ↦ (0 : ℝ))
  have hfaceSubset : F ⊆ P := by
    intro q hq
    exact (mem_exercise715StageFace_iff k b a C S L lam q).mp hq |>.1
  have hpLooseP : pLoose ∈ P := by
    exact subset_convexHull ℝ _
      (exercise715LoosePoint_mem_stageSet k b a S hb.le ha_nonneg)
  have hpLooseValue : exercise715StageValue a C S L lam pLoose < b := by
    have hLamSumNonneg : 0 ≤ ∑ j ∈ L, lam := by
      exact Finset.sum_nonneg fun j hj ↦ hlam_nonneg
    have hvalueEq :
        exercise715StageValue a C S L lam pLoose = -(∑ j ∈ L, lam) := by
      simp [exercise715StageValue, pLoose]
    rw [hvalueEq]
    linarith
  have hfaceAffineLevel :
      ∀ q ∈ affineSpan ℝ F, A q = b - c := by
    intro q hq
    refine affineSpan_induction (k := ℝ) (s := F) (p := fun z ↦ A z = b - c) hq ?_ ?_
    · intro z hz
      have hzEq := (mem_exercise715StageFace_iff k b a C S L lam z).mp hz |>.2
      have hsplit := exercise715StageValue_eq_linear_part_add_constant a C S L lam z
      dsimp [A, c]
      linarith
    · intro t x y z hx hy hz
      simp only [vsub_eq_sub, vadd_eq_add, map_add, map_sub, map_smul]
      rw [hx, hy, hz]
      ring
  have hpLooseNotAff : pLoose ∉ affineSpan ℝ F := by
    intro hpLooseAff
    have hlevel := hfaceAffineLevel pLoose hpLooseAff
    have hsplit := exercise715StageValue_eq_linear_part_add_constant a C S L lam pLoose
    dsimp [A, c] at hlevel
    linarith
  have hAffineLe : affineSpan ℝ F ≤ affineSpan ℝ P := affineSpan_mono ℝ hfaceSubset
  have hAffineNotGe : ¬ affineSpan ℝ P ≤ affineSpan ℝ F := by
    intro hge
    exact hpLooseNotAff (hge (subset_affineSpan ℝ P hpLooseP))
  have hAffineNe : affineSpan ℝ F ≠ affineSpan ℝ P := by
    intro hEq
    apply hAffineNotGe
    rw [hEq]
  have hAffineLt : affineSpan ℝ F < affineSpan ℝ P :=
    lt_of_le_of_ne hAffineLe hAffineNe
  have hAffineNonempty :
      (affineSpan ℝ F : Set ((Fin n → ℝ) × (Fin n → ℝ))).Nonempty := by
    exact ⟨p0, subset_affineSpan ℝ F hp0⟩
  have hDirectionLt :
      (affineSpan ℝ F).direction < (affineSpan ℝ P).direction :=
    AffineSubspace.direction_lt_of_nonempty hAffineLt hAffineNonempty
  -- Strict inclusion of finite-dimensional direction spaces is strict inequality of finranks.
  simpa [F, P] using Submodule.finrank_lt_finrank_of_lt hDirectionLt

/-- Helper for Exercise 7.15: every staged equality face is exposed once the staged inequality is
known to be valid and sharp at one point. -/
theorem exercise715StageFace_isExposed_of_valid
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ)
    (hvalid :
      ∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (exercise715StageSet k b a S) →
          exercise715StageValue a C S L lam p ≤ b)
    {p0 : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp0 : p0 ∈ exercise715StageFace k b a C S L lam) :
    IsExposed ℝ
      (convexHull ℝ (exercise715StageSet k b a S))
      (exercise715StageFace k b a C S L lam) := by
  let Lmap := exercise715StageLinearMap a C S L lam
  let δ : ℝ := b - ∑ j ∈ C, max (a j - lam) 0
  have hvalue_split :
      ∀ q : (Fin n → ℝ) × (Fin n → ℝ),
        exercise715StageValue a C S L lam q =
          Lmap q + ∑ j ∈ C, max (a j - lam) 0 := by
    intro q
    -- The staged owner is already normalized to this affine form.
    simpa [Lmap] using exercise715StageValue_eq_linear_part_add_constant a C S L lam q
  rcases (mem_exercise715StageFace_iff k b a C S L lam p0).mp hp0 with ⟨hp0P, hp0EqFace⟩
  have hvalid_linear :
      ∀ q ∈ convexHull ℝ (exercise715StageSet k b a S), Lmap q ≤ δ := by
    intro q hq
    have hqValid := hvalid hq
    have hsplit := hvalue_split q
    dsimp [δ] at *
    linarith
  have hp0_eq : Lmap p0 = δ := by
    -- The chosen face point attains the exposing level.
    have hsplit := hvalue_split p0
    dsimp [δ] at *
    linarith
  have hface_eq :
      exercise715StageFace k b a C S L lam =
        {q | q ∈ convexHull ℝ (exercise715StageSet k b a S) ∧ Lmap q = δ} := by
    ext q
    constructor
    · intro hq
      rcases (mem_exercise715StageFace_iff k b a C S L lam q).mp hq with ⟨hqP, hqEq⟩
      refine ⟨hqP, ?_⟩
      have hsplit := hvalue_split q
      dsimp [δ] at *
      linarith
    · intro hq
      rcases hq with ⟨hqP, hqEq⟩
      refine (mem_exercise715StageFace_iff k b a C S L lam q).mpr ⟨hqP, ?_⟩
      have hsplit := hvalue_split q
      dsimp [δ] at *
      linarith
  have hface_toExposed :
      exercise715StageFace k b a C S L lam =
        (⟨Lmap, Lmap.continuous_of_finiteDimensional⟩ :
          ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ℝ).toExposed
            (convexHull ℝ (exercise715StageSet k b a S)) := by
    rw [hface_eq]
    exact separatorEqualitySet_eq_toExposed_of_mem hvalid_linear hp0P hp0_eq
  -- Rewriting the staged equality set as a `toExposed` set yields exposedness directly.
  rw [hface_toExposed]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 7.15: releasing one tail coordinate enlarges the staged ambient set by
freeing only the `y_i` coordinate, so the old stage is the `y_i = 0` slice of the new one. -/
theorem exercise715ReleaseTailAmbient_zeroSlice
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (S : Finset (Fin n))
    {i : Fin n}
    (hiS : i ∉ S)
    (htail : k ≤ i.1) :
    convexHull ℝ (exercise715StageSet k b a S) =
      convexHull ℝ (exercise715StageSet k b a (insert i S)) ∩ {p | p.2 i = 0} := by
  let yi : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ := -exercise715TailCoordinateLinearMap i
  have hslice_eq :
      yi ⁻¹' ({0} : Set ℝ) = {p | p.2 i = 0} := by
    ext p
    -- The zero hyperplane for `-y_i` is exactly the slice `y_i = 0`.
    simp [yi, exercise715TailCoordinateLinearMap]
  have hsubset_half :
      exercise715StageSet k b a (insert i S) ⊆ yi ⁻¹' Set.Iic (0 : ℝ) := by
    intro p hp
    rcases (mem_exercise715StageSet_iff k b a (insert i S) p).mp hp with ⟨hpT, _⟩
    rcases (mem_exercise_7_15_mixed_integer_set_iff k b a p).mp hpT with
      ⟨_, hy_nonneg, _, _⟩
    -- New-stage points still satisfy the ambient nonnegativity `0 ≤ y_i`.
    change -p.2 i ≤ 0
    linarith [hy_nonneg i]
  have hstage_eq :
      exercise715StageSet k b a S =
        exercise715StageSet k b a (insert i S) ∩ {p | p.2 i = 0} := by
    ext p
    constructor
    · intro hp
      rcases (mem_exercise715StageSet_iff k b a S p).mp hp with ⟨hpT, hfreeze⟩
      refine ⟨(mem_exercise715StageSet_iff k b a (insert i S) p).mpr ⟨hpT, ?_⟩, ?_⟩
      · intro j hjtail hjNotInsert
        -- Any coordinate frozen before release stays frozen after release unless it is `i`,
        -- which cannot happen under `j ∉ insert i S`.
        have hjInfo : j ≠ i ∧ j ∉ S := by
          simpa using hjNotInsert
        exact hfreeze j hjtail hjInfo.2
      · -- The old stage also freezes the newly released tail coordinate.
        exact hfreeze i htail hiS
    · rintro ⟨hpInsert, hzero⟩
      rcases (mem_exercise715StageSet_iff k b a (insert i S) p).mp hpInsert with
        ⟨hpT, hfreezeInsert⟩
      refine (mem_exercise715StageSet_iff k b a S p).mpr ⟨hpT, ?_⟩
      intro j hjtail hjNotS
      by_cases hji : j = i
      · -- The zero-slice condition restores the old freeze at the newly released coordinate.
        subst hji
        exact hzero
      · -- All other unreleased tails are still frozen by the larger stage owner.
        exact hfreezeInsert j hjtail (by simp [hji, hjNotS])
  calc
    convexHull ℝ (exercise715StageSet k b a S) =
        convexHull ℝ
          (exercise715StageSet k b a (insert i S) ∩ yi ⁻¹' ({0} : Set ℝ)) := by
            rw [hstage_eq, hslice_eq]
    _ = convexHull ℝ (exercise715StageSet k b a (insert i S)) ∩ yi ⁻¹' ({0} : Set ℝ) := by
          exact (convexHull_inter_hyperplane_eq
            (exercise715StageSet k b a (insert i S))
            yi
            0
            hsubset_half).symm
    _ = convexHull ℝ (exercise715StageSet k b a (insert i S)) ∩ {p | p.2 i = 0} := by
          rw [hslice_eq]

/-- Helper for Exercise 7.15: the old equality face is the `y_i = 0` slice of the next release
stage when `L = ∅`. -/
theorem exercise715ReleaseTailFace_zeroSlice
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S : Finset (Fin n)) (lam : ℝ)
    {i : Fin n}
    (hiS : i ∉ S)
    (htail : k ≤ i.1) :
    exercise715StageFace k b a C S ∅ lam =
      exercise715StageFace k b a C (insert i S) ∅ lam ∩ {p | p.2 i = 0} := by
  ext p
  constructor
  · intro hp
    rcases (mem_exercise715StageFace_iff k b a C S ∅ lam p).mp hp with ⟨hpConv, hpEq⟩
    have hpSlice :
        p ∈ convexHull ℝ (exercise715StageSet k b a (insert i S)) ∩ {p | p.2 i = 0} := by
      simpa [exercise715ReleaseTailAmbient_zeroSlice k b a S hiS htail] using hpConv
    have hpZeroEq : p.2 i = 0 := by
      simpa using hpSlice.2
    refine ⟨(mem_exercise715StageFace_iff k b a C (insert i S) ∅ lam p).mpr ⟨hpSlice.1, ?_⟩,
      hpSlice.2⟩
    -- On the zero slice, releasing `i` does not change the staged value.
    have hsame :
        exercise715StageValue a C (insert i S) ∅ lam p =
          exercise715StageValue a C S ∅ lam p := by
      calc
        exercise715StageValue a C (insert i S) ∅ lam p =
            exercise715StageValue a C S ∅ lam p - p.2 i := by
              exact exercise715StageValue_insertReleasedTail a C S ∅ lam p hiS (by simp)
        _ = exercise715StageValue a C S ∅ lam p := by simp [hpZeroEq]
    rw [hsame, hpEq]
  · rintro ⟨hp, hpZero⟩
    rcases (mem_exercise715StageFace_iff k b a C (insert i S) ∅ lam p).mp hp with
      ⟨hpConvInsert, hpEqInsert⟩
    have hpZeroEq : p.2 i = 0 := by
      simpa using hpZero
    have hpConv :
        p ∈ convexHull ℝ (exercise715StageSet k b a S) := by
      have hpSlice :
          p ∈ convexHull ℝ (exercise715StageSet k b a (insert i S)) ∩ {p | p.2 i = 0} :=
        ⟨hpConvInsert, hpZero⟩
      simpa [exercise715ReleaseTailAmbient_zeroSlice k b a S hiS htail] using hpSlice
    have hpEq :
        exercise715StageValue a C S ∅ lam p = b := by
      -- The same zero-slice rewrite now transports the equality back to the old stage.
      have hrewrite :=
        exercise715StageValue_insertReleasedTail a C S ∅ lam p hiS (by simp)
      have hsame :
          exercise715StageValue a C (insert i S) ∅ lam p =
            exercise715StageValue a C S ∅ lam p := by
        calc
          exercise715StageValue a C (insert i S) ∅ lam p =
              exercise715StageValue a C S ∅ lam p - p.2 i := hrewrite
          _ = exercise715StageValue a C S ∅ lam p := by simp [hpZeroEq]
      rw [hsame] at hpEqInsert
      exact hpEqInsert
    exact (mem_exercise715StageFace_iff k b a C S ∅ lam p).mpr ⟨hpConv, hpEq⟩

/-- Helper for Exercise 7.15: releasing one unlifted tail coordinate preserves staged validity
and facetness. -/
theorem exercise715ReleaseTailFacetStepZeroL
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S : Finset (Fin n)) (lam : ℝ)
    (hb : 0 < b)
    (ha : ∀ j, 0 < a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (hcover : C.sum a = b + lam)
    (hlam_pos : 0 < lam)
    {j0 i : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : lam < a j0)
    (hiS : i ∉ S)
    (hiTail : k ≤ i.1)
    (hOldFacet :
      IsFacetOf
        (convexHull ℝ (exercise715StageSet k b a S))
        (exercise715StageFace k b a C S ∅ lam)) :
    (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (exercise715StageSet k b a (insert i S)) →
          exercise715StageValue a C (insert i S) ∅ lam p ≤ b) ∧
      IsFacetOf
        (convexHull ℝ (exercise715StageSet k b a (insert i S)))
        (exercise715StageFace k b a C (insert i S) ∅ lam) := by
  let Pold : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (exercise715StageSet k b a S)
  let Pnew : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (exercise715StageSet k b a (insert i S))
  let Fold : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    exercise715StageFace k b a C S ∅ lam
  let Fnew : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    exercise715StageFace k b a C (insert i S) ∅ lam
  have hInsertSub : ∀ ⦃j : Fin n⦄, j ∈ insert i S → k ≤ j.1 := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hjS
    · simpa [hji] using hiTail
    · exact hSsub hjS
  have hvalidNew :
      ∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ Pnew → exercise715StageValue a C (insert i S) ∅ lam p ≤ b := by
    intro p hp
    exact exercise715StageValue_le_of_mem_convexHull
      k b a C (insert i S) ∅ lam (fun j ↦ (ha j).le) hCsub hInsertSub (by simp)
      hcover hlam_pos hp
  rcases hOldFacet.1 with ⟨p0, hp0⟩
  rcases exercise715ReleaseTailCoupledPoint_mem_stageFace
      k b a C S lam ha hCsub hSsub hcover hlam_pos hj0C hj0lt hiS hiTail with
    ⟨hq, hqiPos⟩
  let q : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C then 1 else 0),
      fun j ↦
        if j = j0 then a j0 - lam + min (a i) lam
        else if j = i then min (a i) lam
        else if j ∈ C.erase j0 then a j else 0)
  have hqFnew : q ∈ Fnew := by
    simpa [q, Fnew] using hq
  have hqiPos' : 0 < q.2 i := by
    simpa [q] using hqiPos
  have hFoldSubset : Fold ⊆ Fnew := by
    intro p hp
    have hslice := exercise715ReleaseTailFace_zeroSlice k b a C S lam hiS hiTail
    have hp' : p ∈ exercise715StageFace k b a C S ∅ lam := by simpa [Fold] using hp
    rw [hslice] at hp'
    simpa [Fnew] using hp'.1
  have hp0Fnew : p0 ∈ Fnew := hFoldSubset hp0
  have hp0Zero : p0.2 i = 0 := by
    have hp0Ambient := (mem_exercise715StageFace_iff k b a C S ∅ lam p0).mp hp0 |>.1
    have hslice := exercise715ReleaseTailAmbient_zeroSlice k b a S hiS hiTail
    rw [hslice] at hp0Ambient
    exact hp0Ambient.2
  have hFaceDirectionLe :
      (affineSpan ℝ Fold).direction ≤ (affineSpan ℝ Fnew).direction :=
    AffineSubspace.direction_le (affineSpan_mono ℝ hFoldSubset)
  have hqSubP0New : q - p0 ∈ (affineSpan ℝ Fnew).direction := by
    have hp0Aff : p0 ∈ affineSpan ℝ Fnew := subset_affineSpan ℝ _ hp0Fnew
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hp0Aff]
    refine ⟨q, subset_affineSpan ℝ _ hqFnew, ?_⟩
    simp [vsub_eq_sub]
  have hqSubP0NotOld : q - p0 ∉ (affineSpan ℝ Fold).direction := by
    intro hOldDirection
    have hFoldAmbient : Fold ⊆ Pold := by
      intro p hp
      exact (mem_exercise715StageFace_iff k b a C S ∅ lam p).mp hp |>.1
    have hInOldAmbient :
        q - p0 ∈ (affineSpan ℝ Pold).direction :=
      AffineSubspace.direction_le (affineSpan_mono ℝ hFoldAmbient) hOldDirection
    have hFrozen : (q - p0).2 i = 0 := by
      rw [show (affineSpan ℝ Pold).direction =
          exercise715StageCoordinateSubmodule k S by
        simpa [Pold] using exercise715StageSet_direction_affineSpan_eq k b a S hb ha hSsub]
        at hInOldAmbient
      exact (mem_exercise715StageCoordinateSubmodule_iff k S (q - p0)).1
        hInOldAmbient i hiTail hiS
    have hcoord : (q - p0).2 i = q.2 i := by simp [hp0Zero]
    linarith
  have hFaceDirectionLt :
      (affineSpan ℝ Fold).direction < (affineSpan ℝ Fnew).direction := by
    exact lt_of_le_of_ne hFaceDirectionLe (fun hEq ↦ hqSubP0NotOld (hEq.symm ▸ hqSubP0New))
  have hFaceFinrankLt :
      Module.finrank ℝ (affineSpan ℝ Fold).direction <
        Module.finrank ℝ (affineSpan ℝ Fnew).direction :=
    Submodule.finrank_lt_finrank_of_lt hFaceDirectionLt
  have hAmbientFinrank :
      Module.finrank ℝ (affineSpan ℝ Pnew).direction =
        Module.finrank ℝ (affineSpan ℝ Pold).direction + 1 := by
    simpa [Pnew, Pold] using
      exercise715StageSet_finrank_direction_insert k b a S hb ha hSsub hiS hiTail
  have hNewProper :
      Module.finrank ℝ (affineSpan ℝ Fnew).direction <
        Module.finrank ℝ (affineSpan ℝ Pnew).direction := by
    simpa [Fnew, Pnew] using
      exercise715StageFace_finrank_lt_ambient
        k b a C (insert i S) ∅ lam hb (fun j ↦ (ha j).le) hlam_pos.le hqFnew
  have hOldCodim :
      Module.finrank ℝ (affineSpan ℝ Fold).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ Pold).direction := by
    simpa [Fold, Pold] using hOldFacet.2.2
  have hNewCodim :
      Module.finrank ℝ (affineSpan ℝ Fnew).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ Pnew).direction := by
    omega
  refine ⟨hvalidNew, ?_⟩
  rw [isFacetOf_iff]
  refine ⟨⟨q, hqFnew⟩, ?_, hNewCodim⟩
  -- Validity and the explicit tight point expose the new staged equality face.
  simpa [Pnew, Fnew] using
    exercise715StageFace_isExposed_of_valid k b a C (insert i S) ∅ lam hvalidNew hqFnew

/-- Helper for Exercise 7.15: simultaneously releasing and lifting one tail coordinate preserves
staged validity and facetness. -/
theorem exercise715LiftedReleaseTailFacetStep
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ)
    (hb : 0 < b)
    (ha : ∀ j, 0 < a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (hLsub : L ⊆ S)
    (hcover : C.sum a = b + lam)
    (hlam_pos : 0 < lam)
    {i : Fin n}
    (hiS : i ∉ S)
    (hiTail : k ≤ i.1)
    (hlam_lt_ai : lam < a i)
    (hOldFacet :
      IsFacetOf
        (convexHull ℝ (exercise715StageSet k b a S))
        (exercise715StageFace k b a C S L lam)) :
    (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (exercise715StageSet k b a (insert i S)) →
          exercise715StageValue a C (insert i S) (insert i L) lam p ≤ b) ∧
      IsFacetOf
        (convexHull ℝ (exercise715StageSet k b a (insert i S)))
        (exercise715StageFace k b a C (insert i S) (insert i L) lam) := by
  classical
  let Pold : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (exercise715StageSet k b a S)
  let Pnew : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    convexHull ℝ (exercise715StageSet k b a (insert i S))
  let Fold : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    exercise715StageFace k b a C S L lam
  let Fnew : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    exercise715StageFace k b a C (insert i S) (insert i L) lam
  let Z : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    Fold ∩ {q | q.1 i = 0}
  let pLam : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C then 1 else 0),
      fun j ↦ if j = i then lam else if j ∈ C then a j else 0)
  let pAi : (Fin n → ℝ) × (Fin n → ℝ) :=
    ((fun j ↦ if j = i then 1 else if j ∈ C then 1 else 0),
      fun j ↦ if j = i then a i else if j ∈ C then a j else 0)
  have hInsertSub : ∀ ⦃j : Fin n⦄, j ∈ insert i S → k ≤ j.1 := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hjS
    · simpa [hji] using hiTail
    · exact hSsub hjS
  have hInsertLSub : insert i L ⊆ insert i S := by
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hjL
    · exact Finset.mem_insert.mpr (Or.inl hji)
    · exact Finset.mem_insert_of_mem (hLsub hjL)
  have hvalidNew :
      ∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ Pnew → exercise715StageValue a C (insert i S) (insert i L) lam p ≤ b := by
    intro p hp
    exact exercise715StageValue_le_of_mem_convexHull
      k b a C (insert i S) (insert i L) lam (fun j ↦ (ha j).le) hCsub hInsertSub
      hInsertLSub hcover hlam_pos hp
  have hpLamNew : pLam ∈ Fnew := by
    -- The first new tight point has profile `(x_i,y_i) = (1,lam)`.
    simpa [pLam, Fnew] using
      exercise715LiftedTailPoint_mem_stageFace
        k b a C S L lam lam (fun j ↦ (ha j).le) hCsub hSsub hLsub hcover
        hlam_pos.le hiS hiTail le_rfl hlam_lt_ai.le
  have hpAiNew : pAi ∈ Fnew := by
    -- The second new tight point has profile `(x_i,y_i) = (1,a_i)`.
    simpa [pAi, Fnew] using
      exercise715LiftedTailPoint_mem_stageFace
        k b a C S L lam (a i) (fun j ↦ (ha j).le) hCsub hSsub hLsub hcover
        hlam_pos.le hiS hiTail hlam_lt_ai.le le_rfl
  rcases hOldFacet.1 with ⟨p0, hp0⟩
  let z0 := exercise715ZeroSelectorLinearMap i p0
  have hz0Z : z0 ∈ Z := by
    simpa [z0, Z, Fold] using
      exercise715ZeroSelectorLinearMap_mem_stageFace
        k b a C S L lam hCsub hLsub hiS hiTail hp0
  have hZSubsetNew : Z ⊆ Fnew := by
    intro q hq
    have hqOld : q ∈ exercise715StageFace k b a C S L lam := by
      simpa [Z, Fold] using hq.1
    have hqXi : q.1 i = 0 := by
      simpa [Z] using hq.2
    have hqOldData :=
      (mem_exercise715StageFace_iff k b a C S L lam q).mp hqOld
    have hqNewAmbient : q ∈ Pnew := by
      have hslice := exercise715ReleaseTailAmbient_zeroSlice k b a S hiS hiTail
      rw [hslice] at hqOldData
      simpa [Pnew] using hqOldData.1.1
    have hqNewValue :
        exercise715StageValue a C (insert i S) (insert i L) lam q = b := by
      calc
        exercise715StageValue a C (insert i S) (insert i L) lam q =
            exercise715StageValue a C S L lam q - lam * q.1 i :=
          exercise715StageValue_insertReleasedAndLiftedTail a C S L lam q hiS hLsub
        _ = b := by rw [hqOldData.2, hqXi, mul_zero, sub_zero]
    simpa [Fnew] using
      (mem_exercise715StageFace_iff k b a C (insert i S) (insert i L) lam q).mpr
        ⟨hqNewAmbient, hqNewValue⟩
  let X := exercise715SelectorCoordinateLinearMap (n := n) i
  have hAffineZSelectorZero :
      affineSpan ℝ Z ≤ (LinearMap.ker X).toAffineSubspace := by
    rw [affineSpan_le]
    intro q hq
    change X q = 0
    simpa [X, Z] using hq.2
  have hpLamNotAffineZ : pLam ∉ affineSpan ℝ Z := by
    intro hpLam
    have hzero := hAffineZSelectorZero hpLam
    change X pLam = 0 at hzero
    simpa [X, pLam, exercise715SelectorCoordinateLinearMap] using hzero
  let G : Set ((Fin n → ℝ) × (Fin n → ℝ)) := insert pLam Z
  let profileMap :=
    exercise715TailCoordinateLinearMap (n := n) i -
      lam • exercise715SelectorCoordinateLinearMap (n := n) i
  have hZProfile : ∀ ⦃q : (Fin n → ℝ) × (Fin n → ℝ)⦄, q ∈ Z → profileMap q = 0 := by
    intro q hq
    have hqOld : q ∈ exercise715StageFace k b a C S L lam := by
      simpa [Z, Fold] using hq.1
    have hqXi : q.1 i = 0 := by
      simpa [Z] using hq.2
    have hqOldAmbient :=
      (mem_exercise715StageFace_iff k b a C S L lam q).mp hqOld |>.1
    have hslice := exercise715ReleaseTailAmbient_zeroSlice k b a S hiS hiTail
    rw [hslice] at hqOldAmbient
    have hqYi : q.2 i = 0 := by simpa using hqOldAmbient.2
    simp [profileMap, exercise715TailCoordinateLinearMap,
      exercise715SelectorCoordinateLinearMap, hqXi, hqYi]
  have hAffineGProfileZero :
      affineSpan ℝ G ≤ (LinearMap.ker profileMap).toAffineSubspace := by
    rw [affineSpan_le]
    intro q hq
    change profileMap q = 0
    rcases hq with hqpLam | hqZ
    · subst q
      simp [profileMap, exercise715TailCoordinateLinearMap,
        exercise715SelectorCoordinateLinearMap, pLam]
    · exact hZProfile hqZ
  have hpAiNotAffineG : pAi ∉ affineSpan ℝ G := by
    intro hpAi
    have hzero := hAffineGProfileZero hpAi
    change profileMap pAi = 0 at hzero
    simp [profileMap, exercise715TailCoordinateLinearMap,
      exercise715SelectorCoordinateLinearMap, pAi] at hzero
    linarith
  have hAffineZLtG : affineSpan ℝ Z < affineSpan ℝ G := by
    have hle : affineSpan ℝ Z ≤ affineSpan ℝ G := by
      exact affineSpan_mono ℝ (Set.subset_insert pLam Z)
    refine lt_of_le_of_ne hle ?_
    intro hEq
    apply hpLamNotAffineZ
    rw [hEq]
    exact subset_affineSpan ℝ G (Set.mem_insert pLam Z)
  have hAffineGLeNew : affineSpan ℝ G ≤ affineSpan ℝ Fnew := by
    apply affineSpan_mono ℝ
    intro q hq
    rcases hq with hqpLam | hqZ
    · simpa [hqpLam] using hpLamNew
    · exact hZSubsetNew hqZ
  have hAffineGLtNew : affineSpan ℝ G < affineSpan ℝ Fnew := by
    refine lt_of_le_of_ne hAffineGLeNew ?_
    intro hEq
    apply hpAiNotAffineG
    rw [hEq]
    exact subset_affineSpan ℝ Fnew hpAiNew
  have hZNonempty : (affineSpan ℝ Z : Set ((Fin n → ℝ) × (Fin n → ℝ))).Nonempty :=
    ⟨z0, subset_affineSpan ℝ Z hz0Z⟩
  have hGNonempty : (affineSpan ℝ G : Set ((Fin n → ℝ) × (Fin n → ℝ))).Nonempty :=
    ⟨pLam, subset_affineSpan ℝ G (Set.mem_insert pLam Z)⟩
  have hDirectionZLtG :
      (affineSpan ℝ Z).direction < (affineSpan ℝ G).direction :=
    AffineSubspace.direction_lt_of_nonempty hAffineZLtG hZNonempty
  have hDirectionGLtNew :
      (affineSpan ℝ G).direction < (affineSpan ℝ Fnew).direction :=
    AffineSubspace.direction_lt_of_nonempty hAffineGLtNew hGNonempty
  have hFinrankZLtG :
      Module.finrank ℝ (affineSpan ℝ Z).direction <
        Module.finrank ℝ (affineSpan ℝ G).direction :=
    Submodule.finrank_lt_finrank_of_lt hDirectionZLtG
  have hFinrankGLtNew :
      Module.finrank ℝ (affineSpan ℝ G).direction <
        Module.finrank ℝ (affineSpan ℝ Fnew).direction :=
    Submodule.finrank_lt_finrank_of_lt hDirectionGLtNew
  have hOldLeZAddOne :
      Module.finrank ℝ (affineSpan ℝ Fold).direction ≤
        Module.finrank ℝ (affineSpan ℝ Z).direction + 1 := by
    simpa [Fold, Z] using
      exercise715StageFace_finrank_le_zeroSelectorSlice_add_one
        k b a C S L lam hCsub hLsub hiS hiTail hp0
  have hAmbientFinrank :
      Module.finrank ℝ (affineSpan ℝ Pnew).direction =
        Module.finrank ℝ (affineSpan ℝ Pold).direction + 1 := by
    simpa [Pnew, Pold] using
      exercise715StageSet_finrank_direction_insert k b a S hb ha hSsub hiS hiTail
  have hOldCodim :
      Module.finrank ℝ (affineSpan ℝ Fold).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ Pold).direction := by
    simpa [Fold, Pold] using hOldFacet.2.2
  have hNewProper :
      Module.finrank ℝ (affineSpan ℝ Fnew).direction <
        Module.finrank ℝ (affineSpan ℝ Pnew).direction := by
    simpa [Fnew, Pnew] using
      exercise715StageFace_finrank_lt_ambient
        k b a C (insert i S) (insert i L) lam hb (fun j ↦ (ha j).le) hlam_pos.le hpAiNew
  have hNewCodim :
      Module.finrank ℝ (affineSpan ℝ Fnew).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ Pnew).direction := by
    omega
  refine ⟨hvalidNew, ?_⟩
  rw [isFacetOf_iff]
  refine ⟨⟨pAi, hpAiNew⟩, ?_, hNewCodim⟩
  -- Validity exposes the lifted face, and the two strict affine-span extensions force the
  -- required codimension-one equality.
  simpa [Pnew, Fnew] using
    exercise715StageFace_isExposed_of_valid
      k b a C (insert i S) (insert i L) lam hvalidNew hpAiNew

/-- The equality face of `conv(T)` cut out by the Exercise 7.15 lifted inequality. -/
def exercise_7_15_lifted_flow_cover_face
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p |
    p ∈ convexHull ℝ (exercise_7_15_mixed_integer_set k b a) ∧
      exercise_7_15_lifted_flow_cover_value k a C L lam p = b}

/-- Membership in `exercise_7_15_lifted_flow_cover_face k b a C L λ` means belonging to `conv(T)`
and meeting the Exercise 7.15 lifted inequality at equality. -/
theorem mem_exercise_7_15_lifted_flow_cover_face_iff
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ) (C L : Finset (Fin n)) (lam : ℝ)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    p ∈ exercise_7_15_lifted_flow_cover_face k b a C L lam ↔
      p ∈ convexHull ℝ (exercise_7_15_mixed_integer_set k b a) ∧
        exercise_7_15_lifted_flow_cover_value k a C L lam p = b := by
  -- The face owner is defined as this equality slice inside `conv(T)`.
  rfl

/-- Helper for Exercise 7.15: the fully released staged face is exactly the target face from the
theorem statement. -/
theorem exercise715FullReleasedStageFace_eq_target
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C L : Finset (Fin n)) (lam : ℝ) :
    exercise715StageFace k b a C (exercise_7_15_tail_indices k) L lam =
      exercise_7_15_lifted_flow_cover_face k b a C L lam := by
  ext p
  -- Rewrite both face owners through the fully released ambient set and staged value.
  rw [mem_exercise715StageFace_iff, mem_exercise_7_15_lifted_flow_cover_face_iff,
    exercise715FullReleasedStageSet_eq_mixedIntegerSet, exercise715FullReleasedStageEqTarget]

/-- Helper for Exercise 7.15: the one-step affine pair `(1, -lam)` is valid against the residual
profile `z ↦ max (z - lam) 0`. -/
theorem exercise715TailLiftProfileValid
    {a_i lam : ℝ}
    (hlam_nonneg : 0 ≤ lam) :
    one_step_lifting_valid a_i (fun z ↦ max (z - lam) 0) 1 (-lam) := by
  -- Rewrite the one-step validity claim to the interval condition from Lemma 7.12.
  rw [lemma_7_12_valid_iff_interval_condition
      (a_i := a_i)
      (f_i := fun z ↦ max (z - lam) 0)
      (α_i := 1)
      (β_i := -lam)]
  · intro y hy
    -- The affine function `y - lam` is pointwise bounded by its positive part.
    simpa [one_mul] using (le_max_left (y - lam) (0 : ℝ))
  · -- At the origin the profile value is `0` because `lam` is nonnegative.
    have hneg : 0 - lam ≤ 0 := by
      linarith
    simpa [max_eq_right hneg]

/-- Helper for Exercise 7.15: if `lam < a_i`, then the same one-step profile has two distinct
Lemma 7.12 tight points at `lam` and `a_i`. -/
theorem exercise715TailLiftProfileTightPoints
    {a_i lam : ℝ}
    (hlam_nonneg : 0 ≤ lam)
    (hlam_lt_ai : lam < a_i) :
    ∃ y' y'',
      y' ≠ y'' ∧
        one_step_lifting_tight_point a_i (fun z ↦ max (z - lam) 0) 1 (-lam) y' ∧
        one_step_lifting_tight_point a_i (fun z ↦ max (z - lam) 0) 1 (-lam) y'' := by
  -- Choose the explicit source values where the positive-part profile is exact.
  have hlam_mem : lam ∈ Set.Icc (0 : ℝ) a_i := ⟨hlam_nonneg, hlam_lt_ai.le⟩
  have hai_nonneg : 0 ≤ a_i := le_trans hlam_nonneg hlam_lt_ai.le
  have hai_mem : a_i ∈ Set.Icc (0 : ℝ) a_i := ⟨hai_nonneg, le_rfl⟩
  refine ⟨lam, a_i, by linarith, ⟨hlam_mem, by simp⟩, ⟨hai_mem, ?_⟩⟩
  -- At `y = a_i`, the positive-part formula is just the affine expression itself.
  change 1 * a_i + -lam = max (a_i - lam) 0
  rw [max_eq_left (sub_nonneg.mpr hlam_lt_ai.le)]
  ring

/-- Helper for Exercise 7.15: the source tight point `(x_i, y_i) = (0, 0)` is feasible in the
one-step flow set. -/
theorem exercise715ZeroPoint_mem_oneStepFlowSet
    {a_i : ℝ} :
    ((fun _ : Fin 1 ↦ (0 : ℝ)), fun _ : Fin 1 ↦ (0 : ℝ)) ∈ one_step_flow_set a_i := by
  -- Unfold the one-coordinate feasibility conditions directly.
  rw [mem_one_step_flow_set_iff]
  refine ⟨Or.inl rfl, le_rfl, ?_⟩
  simp

/-- Helper for Exercise 7.15: the source tight point `(x_i, y_i) = (1, lam)` is feasible in the
one-step flow set whenever `0 ≤ lam ≤ a_i`. -/
theorem exercise715LamPoint_mem_oneStepFlowSet
    {a_i lam : ℝ}
    (hlam_nonneg : 0 ≤ lam)
    (hlam_le_ai : lam ≤ a_i) :
    ((fun _ : Fin 1 ↦ (1 : ℝ)), fun _ : Fin 1 ↦ lam) ∈ one_step_flow_set a_i := by
  -- This is the `x_i = 1` branch of the one-step constraints with `y_i = lam`.
  rw [mem_one_step_flow_set_iff]
  refine ⟨Or.inr rfl, hlam_nonneg, ?_⟩
  simpa using hlam_le_ai

/-- Helper for Exercise 7.15: releasing any finite set of tail coordinates transports the
zero-tail facet to the corresponding unlifted staged facet. -/
theorem exercise715ReleaseTailFinsetFacet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S : Finset (Fin n)) (lam : ℝ)
    (hb : 0 < b)
    (ha : ∀ j, 0 < a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (hcover : C.sum a = b + lam)
    (hlam_pos : 0 < lam)
    {j0 : Fin n}
    (hj0C : j0 ∈ C)
    (hj0lt : lam < a j0)
    (hBase :
      (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
          p ∈ convexHull ℝ (exercise715StageSet k b a ∅) →
            exercise715StageValue a C ∅ ∅ lam p ≤ b) ∧
        IsFacetOf
          (convexHull ℝ (exercise715StageSet k b a ∅))
          (exercise715StageFace k b a C ∅ ∅ lam)) :
    (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (exercise715StageSet k b a S) →
          exercise715StageValue a C S ∅ lam p ≤ b) ∧
      IsFacetOf
        (convexHull ℝ (exercise715StageSet k b a S))
        (exercise715StageFace k b a C S ∅ lam) := by
  -- Induct on the released set, using the one-coordinate rank jump at each insertion.
  have hAll :
      ∀ T : Finset (Fin n),
        (∀ ⦃j : Fin n⦄, j ∈ T → k ≤ j.1) →
          (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
              p ∈ convexHull ℝ (exercise715StageSet k b a T) →
                exercise715StageValue a C T ∅ lam p ≤ b) ∧
            IsFacetOf
              (convexHull ℝ (exercise715StageSet k b a T))
              (exercise715StageFace k b a C T ∅ lam) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        simpa using hBase
    | @insert i T hiT ih =>
        intro hInsertSub
        have hTsub : ∀ ⦃j : Fin n⦄, j ∈ T → k ≤ j.1 := by
          intro j hj
          exact hInsertSub (Finset.mem_insert_of_mem hj)
        have hiTail : k ≤ i.1 := hInsertSub (Finset.mem_insert_self i T)
        exact exercise715ReleaseTailFacetStepZeroL
          k b a C T lam hb ha hCsub hTsub hcover hlam_pos hj0C hj0lt hiT hiTail
          (ih hTsub).2
  exact hAll S hSsub

/-- Helper for Exercise 7.15: lifting a finite tail set disjoint from an already released base
transports the base facet to the stage in which all of those coordinates are lifted. -/
theorem exercise715LiftTailFinsetFacet
    (k : ℕ) (b : ℝ) (a : Fin n → ℝ)
    (C S L : Finset (Fin n)) (lam : ℝ)
    (hb : 0 < b)
    (ha : ∀ j, 0 < a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hSsub : ∀ ⦃j : Fin n⦄, j ∈ S → k ≤ j.1)
    (hLsub : ∀ ⦃j : Fin n⦄, j ∈ L → k ≤ j.1)
    (hdisjoint : ∀ ⦃j : Fin n⦄, j ∈ L → j ∉ S)
    (hcover : C.sum a = b + lam)
    (hlam_pos : 0 < lam)
    (hLgt : ∀ ⦃j : Fin n⦄, j ∈ L → lam < a j)
    (hBase :
      (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
          p ∈ convexHull ℝ (exercise715StageSet k b a S) →
            exercise715StageValue a C S ∅ lam p ≤ b) ∧
        IsFacetOf
          (convexHull ℝ (exercise715StageSet k b a S))
          (exercise715StageFace k b a C S ∅ lam)) :
    (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (exercise715StageSet k b a (S ∪ L)) →
          exercise715StageValue a C (S ∪ L) L lam p ≤ b) ∧
      IsFacetOf
        (convexHull ℝ (exercise715StageSet k b a (S ∪ L)))
        (exercise715StageFace k b a C (S ∪ L) L lam) := by
  -- Induct on the lifted set; the two tight profiles supply the two required face directions.
  have hAll :
      ∀ U : Finset (Fin n),
        (∀ ⦃j : Fin n⦄, j ∈ U → k ≤ j.1) →
        (∀ ⦃j : Fin n⦄, j ∈ U → j ∉ S) →
        (∀ ⦃j : Fin n⦄, j ∈ U → lam < a j) →
          (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
              p ∈ convexHull ℝ (exercise715StageSet k b a (S ∪ U)) →
                exercise715StageValue a C (S ∪ U) U lam p ≤ b) ∧
            IsFacetOf
              (convexHull ℝ (exercise715StageSet k b a (S ∪ U)))
              (exercise715StageFace k b a C (S ∪ U) U lam) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
        intro _ _ _
        simpa using hBase
    | @insert i U hiU ih =>
        intro hInsertSub hInsertDisjoint hInsertLarge
        have hUsub : ∀ ⦃j : Fin n⦄, j ∈ U → k ≤ j.1 := by
          intro j hj
          exact hInsertSub (Finset.mem_insert_of_mem hj)
        have hUdisjoint : ∀ ⦃j : Fin n⦄, j ∈ U → j ∉ S := by
          intro j hj
          exact hInsertDisjoint (Finset.mem_insert_of_mem hj)
        have hULarge : ∀ ⦃j : Fin n⦄, j ∈ U → lam < a j := by
          intro j hj
          exact hInsertLarge (Finset.mem_insert_of_mem hj)
        have hiTail : k ≤ i.1 := hInsertSub (Finset.mem_insert_self i U)
        have hiS : i ∉ S := hInsertDisjoint (Finset.mem_insert_self i U)
        have hStageSub : ∀ ⦃j : Fin n⦄, j ∈ S ∪ U → k ≤ j.1 := by
          intro j hj
          rcases Finset.mem_union.mp hj with hjS | hjU
          · exact hSsub hjS
          · exact hUsub hjU
        have hUsubStage : U ⊆ S ∪ U := Finset.subset_union_right
        have hiStage : i ∉ S ∪ U := by
          intro hi
          rcases Finset.mem_union.mp hi with hiS' | hiU'
          · exact hiS hiS'
          · exact hiU hiU'
        have hiLarge : lam < a i := hInsertLarge (Finset.mem_insert_self i U)
        have hStep := exercise715LiftedReleaseTailFacetStep
          k b a C (S ∪ U) U lam hb ha hCsub hStageSub hUsubStage hcover hlam_pos
          hiStage hiTail hiLarge (ih hUsub hUdisjoint hULarge).2
        -- The helper inserts the new coordinate on the left; union normalization gives the target.
        simpa [Finset.union_insert] using hStep
  exact hAll L hLsub hdisjoint hLgt

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_15.lean.
Exercise 7.15. Let
`T = {(x,y) ∈ {0,1}^n × ℝ^n_+ | ∑_{j=1}^k y_j - ∑_{j=k+1}^n y_j ≤ b, y_j ≤ a_j x_j for all j}`
with `b > 0` and `a_j > 0` for all `j`. Let `C ⊆ {1, …, k}` be a flow cover, let
`λ = flow_cover_excess a b C = ∑_{j ∈ C} a_j - b`, and let
`L ⊆ {k + 1, …, n}` with `\bar L = {k + 1, …, n} \setminus L`. If `max_{j ∈ C} a_j > λ` and
`a_j > λ` for all `j ∈ L`, then the inequality
`∑_{j ∈ C} y_j - ∑_{j ∈ \bar L} y_j + ∑_{j ∈ C} (a_j - λ)^+ (1 - x_j) - ∑_{j ∈ L} λ x_j ≤ b`
is valid for `conv(T)` and its equality face is a facet of `conv(T)`. The source hypothesis
`max_{j ∈ C} a_j > λ` is recorded directly by asking for some `j ∈ C` with `a_j > λ`. -/
theorem exercise_7_15_lifted_flow_cover_inequality_defines_facet
    (k : ℕ)
    (b : ℝ) (a : Fin n → ℝ)
    (C L : Finset (Fin n))
    (hb : 0 < b)
    (ha : ∀ j, 0 < a j)
    (hCsub : ∀ ⦃j : Fin n⦄, j ∈ C → j.1 < k)
    (hC : IsFlowCover a b C)
    (hmax : ∃ j ∈ C, flow_cover_excess a b C < a j)
    (hLsub : ∀ ⦃j : Fin n⦄, j ∈ L → k ≤ j.1)
    (hLgt : ∀ ⦃j : Fin n⦄, j ∈ L → flow_cover_excess a b C < a j) :
    (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
        p ∈ convexHull ℝ (exercise_7_15_mixed_integer_set k b a) →
          exercise_7_15_lifted_flow_cover_value k a C L (flow_cover_excess a b C) p ≤ b) ∧
      IsFacetOf
        (convexHull ℝ (exercise_7_15_mixed_integer_set k b a))
        (exercise_7_15_lifted_flow_cover_face k b a C L (flow_cover_excess a b C)) := by
  let lam := flow_cover_excess a b C
  -- Record the common excess parameter and its one-step lift data up front.
  have hlam_pos : 0 < lam := by
    change 0 < flow_cover_excess a b C
    exact flow_cover_excess_pos a b C hC
  have hlam_nonneg : 0 ≤ lam := le_of_lt hlam_pos
  have hCnonempty : C.Nonempty := flow_cover_nonempty a b C (le_of_lt hb) hC
  have ha_nonneg : ∀ j, 0 ≤ a j := fun j ↦ (ha j).le
  have hcover : C.sum a = b + lam := by
    -- Rewrite the textbook excess parameter back to the source equality `∑_{j ∈ C} a_j = b + λ`.
    change C.sum a = b + flow_cover_excess a b C
    rw [flow_cover_excess_eq_sum_sub]
    linarith
  have hZeroTailFacet :
      (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
          p ∈ convexHull ℝ (exercise715StageSet k b a ∅) →
            exercise715StageValue a C ∅ ∅ lam p ≤ b) ∧
        IsFacetOf
          (convexHull ℝ (exercise715StageSet k b a ∅))
          (exercise715StageFace k b a C ∅ ∅ lam) := by
    -- The base stage is now reduced to Theorem 7.9 on the truncated full-domain owner `a0`.
    have hmax_lam : ∃ j ∈ C, lam < a j := by
      change ∃ j ∈ C, flow_cover_excess a b C < a j
      exact hmax
    exact exercise715ZeroTailStageFacet k b a C lam ha_nonneg hC hCnonempty hCsub
      hmax_lam hcover
  rcases hmax with ⟨j0, hj0C, hj0lt⟩
  -- Route correction: the theorem now uses the staged owner from Agent C's plan, so the previous
  -- conflation of "release a tail coordinate" with "lift a released tail coordinate" is gone.
  have hReleasedSub :
      ∀ ⦃j : Fin n⦄, j ∈ exercise_7_15_tail_indices k \ L → k ≤ j.1 := by
    intro j hj
    exact (mem_exercise_7_15_tail_indices_iff k j).mp (Finset.mem_sdiff.mp hj).1
  have hReleasedStage := exercise715ReleaseTailFinsetFacet
    k b a C (exercise_7_15_tail_indices k \ L) lam hb ha hCsub hReleasedSub hcover
    hlam_pos hj0C hj0lt hZeroTailFacet
  have hReleasedDisjoint :
      ∀ ⦃j : Fin n⦄, j ∈ L → j ∉ exercise_7_15_tail_indices k \ L := by
    intro j hjL hjDiff
    exact (Finset.mem_sdiff.mp hjDiff).2 hjL
  have hLiftedStage := exercise715LiftTailFinsetFacet
    k b a C (exercise_7_15_tail_indices k \ L) L lam hb ha hCsub hReleasedSub hLsub
    hReleasedDisjoint hcover hlam_pos (fun j hj ↦ hLgt hj) hReleasedStage
  have hFullStage :
      (exercise_7_15_tail_indices k \ L) ∪ L = exercise_7_15_tail_indices k := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hiDiff | hiL
      · exact (Finset.mem_sdiff.mp hiDiff).1
      · exact (mem_exercise_7_15_tail_indices_iff k i).mpr (hLsub hiL)
    · intro hiTail
      by_cases hiL : i ∈ L
      · exact Finset.mem_union_right _ hiL
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hiTail, hiL⟩)
  have hLiftedFull :
      (∀ ⦃p : (Fin n → ℝ) × (Fin n → ℝ)⦄,
          p ∈ convexHull ℝ
            (exercise715StageSet k b a (exercise_7_15_tail_indices k)) →
            exercise715StageValue a C (exercise_7_15_tail_indices k) L lam p ≤ b) ∧
        IsFacetOf
          (convexHull ℝ (exercise715StageSet k b a (exercise_7_15_tail_indices k)))
          (exercise715StageFace k b a C (exercise_7_15_tail_indices k) L lam) := by
    simpa only [hFullStage] using hLiftedStage
  refine ⟨?_, ?_⟩
  · intro p hp
    have hpStage :
        p ∈ convexHull ℝ (exercise715StageSet k b a (exercise_7_15_tail_indices k)) := by
      rwa [exercise715FullReleasedStageSet_eq_mixedIntegerSet]
    have hvalue := hLiftedFull.1 hpStage
    -- At the full stage the staged functional is the lifted inequality from the statement.
    rwa [exercise715FullReleasedStageEqTarget] at hvalue
  · -- The same two full-stage rewrites identify both the ambient set and the equality face.
    simpa only [exercise715FullReleasedStageSet_eq_mixedIntegerSet,
      exercise715FullReleasedStageFace_eq_target] using hLiftedFull.2

end Exercise715

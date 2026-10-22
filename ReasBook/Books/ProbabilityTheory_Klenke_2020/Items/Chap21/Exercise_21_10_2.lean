/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58

-- Declarations for this item will be appended below by the statement pipeline.

open BigOperators Filter MeasureTheory ProbabilityTheory

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

-- Semantic recall: `lean_leansearch` points to mathlib's Stieltjes owner through
-- `Monotone.stieltjesFunction` and `StieltjesFunction.measure`. Definition 21.58 only packages
-- existence of a continuous witness, so this file keeps the local chosen owner internally and
-- exposes source-facing bracket/measure aliases for the public `𝒞_qvAlong P` statement.

/-- The canonical continuous square-variation path attached to `hX : HasContinuousSquareVariationAlongPartition X P`.
-/
noncomputable def squareVariationBracket
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) : PathSpace :=
  Classical.choose hX

/-- The chosen path `squareVariationBracket X P hX` is a continuous square-variation witness of `X`
along `P`. -/
theorem squareVariationBracket_spec
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) :
    HasSquareVariationAlongPartition X P (squareVariationBracket X P hX) := by
  -- Proof comment: `squareVariationBracket` is exactly the witness chosen from the owner
  -- property `HasContinuousSquareVariationAlongPartition`.
  simpa [squareVariationBracket] using Classical.choose_spec hX

/-- Helper for Exercise 21.10.2: the truncation index at the horizon `0` is the initial index
`0`. -/
lemma partitionBoundIndex_zero
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    partitionBoundIndex P n 0 = 0 := by
  -- Proof comment: admissibility gives `P n 0 = 0`, so the least row index reaching `0` is
  -- already the initial one.
  apply Nat.le_antisymm
  · change Nat.find (exists_partition_index_le_time P n 0) ≤ 0
    refine Nat.find_min' (exists_partition_index_le_time P n 0) ?_
    rw [IsAdmissiblePartitionSequence.zero_eq (P := P) n]
  · exact Nat.zero_le _

/-- Helper for Exercise 21.10.2: the square-variation partition sum on the degenerate interval
`[0, 0]` vanishes. -/
lemma partitionSquareVariationSum_zero
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) :
    partitionPVariationSum P 2 X 0 n = 0 := by
  -- Proof comment: at the zero horizon the truncated partition range is empty.
  rw [partitionPVariationSum, partitionBoundIndex_zero]
  simp

/-- Helper for Exercise 21.10.2: every square-variation witness along `P` starts from `0`. -/
lemma hasSquareVariationAlongPartition_zero
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {V : PathwiseProcess} (hX : HasSquareVariationAlongPartition X P V) :
    V 0 = 0 := by
  have hlimX :
      Tendsto (partitionPVariationSum P 2 X 0) atTop (nhds (V 0)) :=
    HasSquareVariationAlongPartition.tendsto_partition_sum hX 0
  have hlim0 :
      Tendsto (partitionPVariationSum P 2 X 0) atTop (nhds (0 : ℝ)) := by
    have hzeroSeq : partitionPVariationSum P 2 X 0 = fun _ ↦ (0 : ℝ) := by
      funext n
      exact partitionSquareVariationSum_zero X P n
    rw [hzeroSeq]
    exact tendsto_const_nhds
  -- Proof comment: the defining square sums at time `0` are identically zero, so the witness
  -- must have the same value at `0`.
  exact tendsto_nhds_unique hlimX hlim0

/-- Helper for Exercise 21.10.2: for a fixed row, the truncation index is monotone in the
terminal time. This early local copy keeps the full-sum monotonicity route available before the
later boundary-point API block. -/
lemma partitionBoundIndexMonotoneEarly
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) {S T : NNReal} (hST : S ≤ T) :
    partitionBoundIndex P n S ≤ partitionBoundIndex P n T := by
  refine Nat.find_min' (exists_partition_index_le_time P n S) ?_
  exact le_trans hST (le_partitionBoundIndex_time P n T)

/-- Helper for Exercise 21.10.2: every left endpoint strictly before the truncation index lies
strictly below the horizon. This early local copy supports the full-sum bridge. -/
lemma partitionPointLtTimeOfLtPartitionBoundIndexEarly
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k < T := by
  have hk_not : ¬ T ≤ P n k := by
    intro hkT
    have hmin :
        partitionBoundIndex P n T ≤ k := by
      simpa [partitionBoundIndex] using
        (Nat.find_min' (exists_partition_index_le_time P n T) hkT)
    exact (not_le_of_gt hk) hmin
  exact lt_of_not_ge hk_not

/-- Helper for Exercise 21.10.2: the predecessor partition point immediately before the horizon
`T`. This early local copy keeps the full-sum route self-contained. -/
noncomputable def partitionPredecessorPointEarly
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) (T : NNReal) : NNReal :=
  P n (partitionBoundIndex P n T - 1)

/-- Helper for Exercise 21.10.2: the early predecessor point lies in `[0, T]`. -/
lemma partitionPredecessorPointEarly_le_time
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) (T : NNReal) :
    partitionPredecessorPointEarly P n T ≤ T := by
  rcases Nat.eq_zero_or_pos (partitionBoundIndex P n T) with hidx | hidx
  · have hzero : P n 0 = 0 := hP.zero_eq n
    have hT0 : T = 0 := by
      have hle0 : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0' : T ≤ 0 := by simpa [hzero] using hle0
      exact le_antisymm hle0' bot_le
    have hidx0 : partitionBoundIndex P n 0 = 0 := by
      simpa [hT0] using hidx
    simp [partitionPredecessorPointEarly, hidx0, hT0, hzero]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P n T = k + 1 :=
      ⟨partitionBoundIndex P n T - 1, (Nat.sub_add_cancel hidx).symm⟩
    have hk_lt : k < partitionBoundIndex P n T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hk_time : P n k < T :=
      partitionPointLtTimeOfLtPartitionBoundIndexEarly P n k T hk_lt
    have hpred : partitionPredecessorPointEarly P n T = P n k := by
      simp [partitionPredecessorPointEarly, hk]
    simpa [hpred] using le_of_lt hk_time

/-- Helper for Exercise 21.10.2: a clipped successor interval has size at most one mesh width.
This early local copy supports the predecessor-point convergence used in the full-sum bridge. -/
lemma edist_partitionPoint_partitionNextPointUpTo_le_partitionMeshEarly
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    edist (P n k) (partitionNextPointUpTo P n k T) ≤ partitionMesh P n := by
  have hleft :
      P n k ≤ partitionNextPointUpTo P n k T := by
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt ((hP.strictMono n) (Nat.lt_succ_self k))
    · exact le_of_lt (partitionPointLtTimeOfLtPartitionBoundIndexEarly P n k T hk)
  have hright :
      partitionNextPointUpTo P n k T ≤ P n (k + 1) := by
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hdist :
      edist (P n k) (partitionNextPointUpTo P n k T) ≤ edist (P n k) (P n (k + 1)) := by
    have hsucc : P n k < P n (k + 1) := (hP.strictMono n) (Nat.lt_succ_self k)
    rw [edist_nndist, edist_nndist, NNReal.nndist_eq, NNReal.nndist_eq,
      tsub_eq_zero_of_le hleft, tsub_eq_zero_of_le (le_of_lt hsucc), max_eq_right, max_eq_right]
    · exact_mod_cast tsub_le_tsub_right hright _
    · simp
    · simp
  calc
    edist (P n k) (partitionNextPointUpTo P n k T)
        ≤ edist (P n k) (P n (k + 1)) := hdist
    _ ≤ partitionMesh P n := by
      rw [partitionMesh]
      exact le_iSup (fun j ↦ edist (P n j) (P n (j + 1))) k

/-- Helper for Exercise 21.10.2: the early predecessor point lies within one mesh width of the
horizon. -/
lemma partitionPredecessorPointWithinMeshEarly
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) (T : NNReal) :
    edist (partitionPredecessorPointEarly P n T) T ≤ partitionMesh P n := by
  rcases Nat.eq_zero_or_pos (partitionBoundIndex P n T) with hidx | hidx
  · have hzero : P n 0 = 0 := hP.zero_eq n
    have hT0 : T = 0 := by
      have hle0 : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0' : T ≤ 0 := by simpa [hzero] using hle0
      exact le_antisymm hle0' bot_le
    have hidx0 : partitionBoundIndex P n 0 = 0 := by
      simpa [hT0] using hidx
    simp [partitionPredecessorPointEarly, hidx0, hT0, hzero]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P n T = k + 1 :=
      ⟨partitionBoundIndex P n T - 1, (Nat.sub_add_cancel hidx).symm⟩
    have hk_lt : k < partitionBoundIndex P n T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hT_le_next : T ≤ P n (k + 1) := by
      simpa [hk] using le_partitionBoundIndex_time P n T
    have hpred : partitionPredecessorPointEarly P n T = P n k := by
      simp [partitionPredecessorPointEarly, hk]
    have hnext : partitionNextPointUpTo P n k T = T := by
      rw [partitionNextPointUpTo, min_eq_right hT_le_next]
    simpa [hpred, hnext] using
      edist_partitionPoint_partitionNextPointUpTo_le_partitionMeshEarly P n k T hk_lt

/-- Helper for Exercise 21.10.2: the monotone full square-sum obtained by discarding the final
clipped increment whenever the next partition point has already crossed the horizon `T`. -/
noncomputable def partitionSquareVariationFullSum
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    if P n (k + 1) ≤ T then
      (X (P n (k + 1)) - X (P n k)) ^ 2
    else 0

/-- Helper for Exercise 21.10.2: for each fixed partition row, the full square-sum is monotone in
the time horizon. -/
lemma partitionSquareVariationFullSum_monotone
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) :
    Monotone (fun T ↦ partitionSquareVariationFullSum X P T n) := by
  intro S T hST
  let term : NNReal → ℕ → ℝ := fun U k ↦
    if P n (k + 1) ≤ U then
      (X (P n (k + 1)) - X (P n k)) ^ 2
    else 0
  have hterm_nonneg :
      ∀ U k, 0 ≤ term U k := by
    intro U k
    by_cases hk : P n (k + 1) ≤ U
    · simpa [term, hk] using sq_nonneg (X (P n (k + 1)) - X (P n k))
    · simp [term, hk]
  have hsubset :
      Finset.range (partitionBoundIndex P n S) ⊆
        Finset.range (partitionBoundIndex P n T) :=
    Finset.range_subset_range.2 (partitionBoundIndexMonotoneEarly P n hST)
  calc
    partitionSquareVariationFullSum X P S n
        = Finset.sum (Finset.range (partitionBoundIndex P n S)) (term S) := by
            simp [partitionSquareVariationFullSum, term]
    _ ≤ Finset.sum (Finset.range (partitionBoundIndex P n S)) (term T) := by
      -- Proof comment: on the common initial range, increasing the horizon can only switch a
      -- zero term on to the corresponding square increment.
      refine Finset.sum_le_sum ?_
      intro k hk
      by_cases hS' : P n (k + 1) ≤ S
      · have hT' : P n (k + 1) ≤ T := le_trans hS' hST
        simpa [term, hS', hT'] using sq_nonneg (X (P n (k + 1)) - X (P n k))
      · by_cases hT' : P n (k + 1) ≤ T
        · simpa [term, hS', hT'] using sq_nonneg (X (P n (k + 1)) - X (P n k))
        · simp [term, hS', hT']
    _ ≤ Finset.sum (Finset.range (partitionBoundIndex P n T)) (term T) := by
      -- Proof comment: enlarging the range adds only nonnegative square increments.
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro k hk hknot
        exact hterm_nonneg T k)
    _ = partitionSquareVariationFullSum X P T n := by
        simp [partitionSquareVariationFullSum, term]

/-- Helper for Exercise 21.10.2: replacing the clipped final increment in the square-variation sum
by `0` changes the sum by at most the last boundary square. -/
lemma partitionSquareVariationSum_sub_fullSum_le_boundary
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    0 ≤ partitionPVariationSum P 2 X T n - partitionSquareVariationFullSum X P T n ∧
      partitionPVariationSum P 2 X T n - partitionSquareVariationFullSum X P T n ≤
        (X T - X (partitionPredecessorPointEarly P n T)) ^ 2 := by
  let core : ℕ → ℝ := fun j ↦ (X (P n (j + 1)) - X (P n j)) ^ 2
  rcases Nat.eq_zero_or_pos (partitionBoundIndex P n T) with hidx | hidx
  · -- Proof comment: if the truncation index is `0`, then `T = 0`, so both sums are empty.
    have hzero : P n 0 = 0 := hP.zero_eq n
    have hT0 : T = 0 := by
      have hle0 : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0' : T ≤ 0 := by simpa [hzero] using hle0
      exact le_antisymm hle0' bot_le
    subst hT0
    simp [partitionPVariationSum, partitionSquareVariationFullSum, partitionPredecessorPointEarly,
      partitionBoundIndex_zero, hzero]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P n T = k + 1 :=
      ⟨partitionBoundIndex P n T - 1, (Nat.sub_add_cancel hidx).symm⟩
    have hk_lt : k < partitionBoundIndex P n T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hT_le_next : T ≤ P n (k + 1) := by
      simpa [hk] using le_partitionBoundIndex_time P n T
    have hboundary :
        partitionPredecessorPointEarly P n T = P n k := by
      simp [partitionPredecessorPointEarly, hk]
    have hboundary_sq :
        (X T - X (P n k)) ^ 2 = (X T - X (partitionPredecessorPointEarly P n T)) ^ 2 := by
      rw [hboundary]
    have hclipped :
        partitionPVariationSum P 2 X T n =
          Finset.sum (Finset.range k) core +
            (X T - X (partitionPredecessorPointEarly P n T)) ^ 2 := by
      -- Proof comment: split off the final clipped increment at index `k`; earlier intervals lie
      -- fully inside `[0, T]`.
      rw [partitionPVariationSum, hk, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro j hj
        have hj_succ_lt : j + 1 < partitionBoundIndex P n T := by
          simpa [hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hj_time : P n (j + 1) < T :=
          partitionPointLtTimeOfLtPartitionBoundIndexEarly P n (j + 1) T hj_succ_lt
        simp [core, Real.rpow_natCast, partitionNextPointUpTo, min_eq_left (le_of_lt hj_time),
          sq_abs]
      · simp [Real.rpow_natCast, partitionNextPointUpTo, min_eq_right hT_le_next, sq_abs,
          hboundary_sq]
    have hfull :
        partitionSquareVariationFullSum X P T n =
          Finset.sum (Finset.range k) core +
            (if P n (k + 1) ≤ T then
              (X (P n (k + 1)) - X (P n k)) ^ 2
            else 0) := by
      -- Proof comment: the full sum has the same initial block, followed by the final
      -- untruncated interval only when its right endpoint is still within the horizon.
      rw [partitionSquareVariationFullSum, hk, Finset.sum_range_succ]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj_succ_lt : j + 1 < partitionBoundIndex P n T := by
        simpa [hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
      have hj_time : P n (j + 1) < T :=
        partitionPointLtTimeOfLtPartitionBoundIndexEarly P n (j + 1) T hj_succ_lt
      rw [if_pos (le_of_lt hj_time)]
    by_cases hlast : P n (k + 1) ≤ T
    · have hlast_eq : P n (k + 1) = T := le_antisymm hlast hT_le_next
      have hlast_sq :
          (X (P n (k + 1)) - X (P n k)) ^ 2 =
            (X T - X (partitionPredecessorPointEarly P n T)) ^ 2 := by
        rw [hlast_eq, hboundary]
      rw [hclipped, hfull, if_pos hlast, hlast_sq]
      constructor
      · ring_nf
        norm_num
      · ring_nf
        nlinarith [sq_nonneg (X T - X (partitionPredecessorPointEarly P n T))]
    · rw [hclipped, hfull, if_neg hlast, add_zero]
      constructor
      · ring_nf
        nlinarith [sq_nonneg (X T - X (partitionPredecessorPointEarly P n T))]
      · ring_nf
        rfl

/-- Helper for Exercise 21.10.2: the full square-sums have the same limit as the clipped
square-variation partition sums. -/
lemma tendsto_partitionSquareVariationFullSum
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {V : PathwiseProcess} (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    Tendsto (partitionSquareVariationFullSum X P T) atTop (nhds (V T)) := by
  have hpoint :
      Tendsto (fun n ↦ partitionPredecessorPointEarly P n T) atTop (nhds T) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP.mesh_tendsto_zero
      (fun n ↦ bot_le) ?_
    intro n
    simpa [edist_comm] using partitionPredecessorPointWithinMeshEarly P n T
  have hboundary :
      Tendsto
        (fun n ↦ (X T - X (partitionPredecessorPointEarly P n T)) ^ 2)
        atTop
        (nhds 0) := by
    -- Proof comment: continuity of `X` turns convergence of the boundary point into vanishing of
    -- the omitted terminal increment.
    have hcont : Continuous fun x : NNReal ↦ (X T - X x) ^ 2 :=
      (continuous_const.sub X.continuous).pow 2
    simpa using hcont.continuousAt.tendsto.comp hpoint
  have hdiff :
      Tendsto
        (fun n ↦ partitionPVariationSum P 2 X T n - partitionSquareVariationFullSum X P T n)
        atTop
        (nhds 0) := by
    refine squeeze_zero
      (fun n ↦ (partitionSquareVariationSum_sub_fullSum_le_boundary X P T n).1)
      (fun n ↦ (partitionSquareVariationSum_sub_fullSum_le_boundary X P T n).2)
      hboundary
  have hsum :
      Tendsto (partitionPVariationSum P 2 X T) atTop (nhds (V T)) :=
    HasSquareVariationAlongPartition.tendsto_partition_sum hX T
  -- Proof comment: subtract the vanishing boundary error from the clipped partition sums.
  simpa [sub_eq_add_neg, sub_sub_cancel] using hsum.sub hdiff

/-- The canonical bracket `squareVariationBracket X P hX` starts at `0` and is monotone, so it
determines its canonical Stieltjes measure. -/
theorem squareVariationBracket_zero_and_monotone
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) :
    squareVariationBracket X P hX 0 = 0 ∧ Monotone (squareVariationBracket X P hX) := by
  have hspec := squareVariationBracket_spec X P hX
  refine ⟨hasSquareVariationAlongPartition_zero X P hspec, ?_⟩
  intro s t hst
  -- Proof comment: compare the monotone full partition sums at the horizons `s` and `t`, then
  -- pass to the limit along the chosen square-variation witness.
  exact
    le_of_tendsto_of_tendsto'
      (tendsto_partitionSquareVariationFullSum X P hspec s)
      (tendsto_partitionSquareVariationFullSum X P hspec t)
      (fun n ↦ partitionSquareVariationFullSum_monotone X P n hst)

/-- The canonical Stieltjes measure `d⟨X⟩` attached to the chosen bracket witness
`squareVariationBracket X P hX`. -/
noncomputable def squareVariationBracketMeasure
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) : Measure NNReal :=
  (((squareVariationBracket_zero_and_monotone X P hX).2).stieltjesFunction).measure

/-- Helper for Exercise 21.10.2: the canonical bracket measure has finite mass on each interval
`Set.Icc 0 T`. -/
lemma squareVariationBracketMeasure_Icc_lt_top
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) (T : NNReal) :
    squareVariationBracketMeasure X P hX (Set.Icc 0 T) ≠ ⊤ := by
  obtain ⟨hzero, hmono⟩ := squareVariationBracket_zero_and_monotone X P hX
  have hright :
      Function.rightLim (squareVariationBracket X P hX) T = squareVariationBracket X P hX T := by
    exact ((squareVariationBracket X P hX).continuous.continuousAt.continuousWithinAt).rightLim_eq
  have hleft :
      Function.leftLim (hmono.stieltjesFunction) 0 = 0 := by
    have hleft_eval :
        Function.leftLim (hmono.stieltjesFunction) 0 = hmono.stieltjesFunction 0 :=
      leftLim_eq_of_isBot isBot_bot
    have hright0 :
        Function.rightLim (squareVariationBracket X P hX) 0 = 0 := by
      simpa [hzero] using
        ((squareVariationBracket X P hX).continuous.continuousAt.continuousWithinAt.rightLim_eq
          (a := (0 : NNReal)))
    have hzero_eval : hmono.stieltjesFunction 0 = 0 := by
      rw [Monotone.stieltjesFunction_eq]
      exact hright0
    exact hleft_eval.trans hzero_eval
  have hnonneg : 0 ≤ squareVariationBracket X P hX T := by
    rw [← hzero]
    exact hmono bot_le
  -- Proof comment: `measure_Icc` computes the interval mass explicitly as an `ENNReal.ofReal`
  -- value, hence that mass is finite.
  rw [squareVariationBracketMeasure, StieltjesFunction.measure_Icc]
  simp [Monotone.stieltjesFunction_eq, hright, hleft, hnonneg]

/-- Helper for Exercise 21.10.2: the canonical bracket measure realizes the chosen bracket path on
intervals `Set.Icc 0 T`. -/
lemma squareVariationBracketMeasure_realizes_path
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) :
    ∀ T : NNReal,
      squareVariationBracket X P hX T =
        ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂(squareVariationBracketMeasure X P hX) := by
  obtain ⟨hzero, hmono⟩ := squareVariationBracket_zero_and_monotone X P hX
  intro T
  have hright :
      Function.rightLim (squareVariationBracket X P hX) T = squareVariationBracket X P hX T := by
    -- Proof comment: continuity removes the right-limit correction in the Stieltjes function.
    exact ((squareVariationBracket X P hX).continuous.continuousAt.continuousWithinAt).rightLim_eq
  have hleft :
      Function.leftLim (hmono.stieltjesFunction) 0 = 0 := by
    -- Proof comment: continuity at the left endpoint identifies the Stieltjes left limit with
    -- the initial value `0`.
    have hleft_eval :
        Function.leftLim (hmono.stieltjesFunction) 0 = hmono.stieltjesFunction 0 :=
      leftLim_eq_of_isBot isBot_bot
    have hright0 :
        Function.rightLim (squareVariationBracket X P hX) 0 = 0 := by
      simpa [hzero] using
        ((squareVariationBracket X P hX).continuous.continuousAt.continuousWithinAt.rightLim_eq
          (a := (0 : NNReal)))
    have hzero_eval : hmono.stieltjesFunction 0 = 0 := by
      rw [Monotone.stieltjesFunction_eq]
      exact hright0
    exact hleft_eval.trans hzero_eval
  have hnonneg : 0 ≤ squareVariationBracket X P hX T := by
    -- Proof comment: monotonicity and the normalization at `0` force the bracket to stay
    -- nonnegative on `[0, ∞)`.
    rw [← hzero]
    exact hmono bot_le
  have hmass :
      (squareVariationBracketMeasure X P hX).real (Set.Icc 0 T) =
        squareVariationBracket X P hX T := by
    -- Proof comment: `measure_Icc` computes the interval mass by the endpoint increment of the
    -- associated Stieltjes function.
    rw [Measure.real_def, squareVariationBracketMeasure, StieltjesFunction.measure_Icc]
    simp [Monotone.stieltjesFunction_eq, hright, hleft, hnonneg]
  simpa using hmass.symm

/-- The source-facing bracket `⟨X⟩` attached to `hX : X ∈ 𝒞_qvAlong P`. -/
noncomputable def continuousSquareVariationBracketAlong
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : X ∈ 𝒞_qvAlong P) : PathSpace :=
  squareVariationBracket X P ((mem_𝒞_qvAlong_iff X).1 hX)

/-- The source-facing Stieltjes measure `d⟨X⟩` attached to `hX : X ∈ 𝒞_qvAlong P`. -/
noncomputable def continuousSquareVariationMeasureAlong
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : X ∈ 𝒞_qvAlong P) : Measure NNReal :=
  squareVariationBracketMeasure X P ((mem_𝒞_qvAlong_iff X).1 hX)

/-- Helper for Exercise 21.10.2: the weighted quadratic partition sum of a path on `[0,T]`
along the `n`-th row of an admissible partition sequence. -/
def weightedPartitionQuadraticVariationApproximationUpTo
    (f : NNReal → ℝ) (X : NNReal → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    f (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2

/-- Helper for Exercise 21.10.2: unfolding
`weightedPartitionQuadraticVariationApproximationUpTo` exposes the defining weighted sum. -/
@[simp] theorem weightedPartitionQuadraticVariationApproximationUpTo_def
    (f : NNReal → ℝ) (X : NNReal → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) :
    weightedPartitionQuadraticVariationApproximationUpTo f X P T n =
      Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
        f (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2 := by
  -- Unfold the local weighted-sum definition.
  rfl

-- Proof sketch: first prove the claim for step functions that are constant on partition
-- intervals, where the weighted sums become finite linear combinations of the defining
-- convergence in `HasSquareVariationAlongPartition`. Then approximate a continuous `f` on
-- `[0, T]` uniformly by such step functions, use the vanishing mesh of `P`, and pass to the
-- Lebesgue--Stieltjes integral against the chosen representing measure `μV.measure`.
/-- Helper for Exercise 21.10.2: every left endpoint that appears before
`partitionBoundIndex P n T` lies strictly below `T`. -/
lemma partitionPoint_lt_time_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k < T := by
  -- Use the minimality of `partitionBoundIndex` to rule out `T ≤ P n k`.
  have hk_not : ¬ T ≤ P n k := by
    intro hkT
    have hmin :
        partitionBoundIndex P n T ≤ k := by
      simpa [partitionBoundIndex] using
        (Nat.find_min' (exists_partition_index_le_time P n T) hkT)
    exact (not_le_of_gt hk) hmin
  exact lt_of_not_ge hk_not

/-- Helper for Exercise 21.10.2: every left endpoint that contributes to the truncated weighted
quadratic sum up to `T` belongs to `Set.Icc 0 T`. -/
lemma partitionPoint_mem_Icc_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k ∈ Set.Icc 0 T := by
  -- Combine nonnegativity in `NNReal` with the strict upper bound from the previous lemma.
  constructor
  · exact bot_le
  · exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n k T hk)

/-- Helper for Exercise 21.10.2: constant weight `1` rewrites the weighted quadratic sum as the
square-variation partition sum from Definition 21.58. -/
lemma weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n =
      partitionPVariationSum P 2 X T n := by
  -- Normalize both sides to the same finite sum of squared increments.
  rw [weightedPartitionQuadraticVariationApproximationUpTo_def, partitionPVariationSum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  -- Replace `|ΔX| ^ 2` by the ordinary square `ΔX ^ 2`.
  simpa [sq_abs]

/-- Helper for Exercise 21.10.2: the representing measure identifies the interval mass on
`Set.Icc 0 T` with the chosen square-variation value `V T`. -/
lemma squareVariationMeasure_real_Icc_eq
    {V : PathwiseProcess} (μV : Measure NNReal)
    (hμV :
      ∀ T : NNReal,
        V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μV)
    (T : NNReal) :
    μV.real (Set.Icc 0 T) = V T := by
  -- Rewrite the set integral of the constant function `1` as the interval mass of `μV`.
  simpa using (hμV T).symm

/-- Helper for Exercise 21.10.2: the representing measure identifies the real mass of
`Set.Ioc a b` with the increment `V b - V a`. -/
lemma squareVariationMeasure_real_Ioc_eq_sub
    {V : PathwiseProcess} (μV : Measure NNReal)
    (hμV :
      ∀ T : NNReal,
        V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μV)
    {a b : NNReal} (ha : 0 ≤ a) (hab : a ≤ b)
    (hfin : μV (Set.Icc 0 b) ≠ ⊤) :
    μV.real (Set.Ioc a b) = V b - V a := by
  have hunion : Set.Icc 0 b = Set.Icc 0 a ∪ Set.Ioc a b := by
    ext x
    constructor
    · intro hx
      by_cases hxa : x ≤ a
      · exact Or.inl ⟨hx.1, hxa⟩
      · exact Or.inr ⟨lt_of_not_ge hxa, hx.2⟩
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, le_trans hx.2 hab⟩
      · exact ⟨le_trans ha (le_of_lt hx.1), hx.2⟩
  have hdisj : Disjoint (Set.Icc 0 a) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro x hxIcc hxIoc
    exact (not_lt_of_ge hxIcc.2) hxIoc.1
  have hmass :
      μV.real (Set.Icc 0 b) =
        μV.real (Set.Icc 0 a) + μV.real (Set.Ioc a b) := by
    have hmassUnion :
        μV.real (Set.Icc 0 a ∪ Set.Ioc a b) =
          μV.real (Set.Icc 0 a) + μV.real (Set.Ioc a b) := by
      simpa using
        (measureReal_union₀
          measurableSet_Ioc.nullMeasurableSet hdisj.aedisjoint
          (measure_ne_top_of_subset (by
            intro x hx
            exact ⟨hx.1, le_trans hx.2 hab⟩) hfin)
          (measure_ne_top_of_subset (by
            intro x hx
            exact ⟨le_trans ha (le_of_lt hx.1), hx.2⟩) hfin))
    simpa [hunion] using hmassUnion
  linarith [hmass, squareVariationMeasure_real_Icc_eq μV hμV a,
    squareVariationMeasure_real_Icc_eq μV hμV b]

/-- Helper for Exercise 21.10.2: integrating a constant weight over `Set.Icc 0 T` against the
representing measure multiplies that constant by the square-variation value `V T`. -/
lemma setIntegral_const_eq_mul_squareVariation
    {V : PathwiseProcess} (μV : Measure NNReal)
    (hμV :
      ∀ T : NNReal,
        V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μV)
    (T : NNReal) (c : ℝ) :
    ∫ _ in Set.Icc 0 T, c ∂μV = c * V T := by
  -- Reduce the constant integral to the interval mass and rewrite that mass as `V T`.
  rw [MeasureTheory.integral_const, smul_eq_mul]
  calc
    (μV.restrict (Set.Icc 0 T)).real Set.univ * c = μV.real (Set.Icc 0 T) * c := by simp
    _ = V T * c := by rw [squareVariationMeasure_real_Icc_eq μV hμV T]
    _ = c * V T := by ring

/-- Helper for Exercise 21.10.2: integrating the prefix indicator `Set.Icc 0 τ` over `Set.Icc 0 T`
recovers the square-variation value `V τ` when `τ ≤ T`. -/
lemma setIntegral_indicator_Icc_eq_squareVariation
    {V : PathwiseProcess} (μV : Measure NNReal)
    (hμV :
      ∀ T : NNReal,
        V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μV)
    {τ T : NNReal} (hτT : τ ≤ T) :
    ∫ s in Set.Icc 0 T,
        Set.indicator (Set.Icc 0 τ) (fun _ ↦ (1 : ℝ)) s ∂μV =
      V τ := by
  have hinter :
      Set.Icc (0 : NNReal) T ∩ Set.Icc (0 : NNReal) τ = Set.Icc (0 : NNReal) τ := by
    ext s
    constructor
    · intro hs
      exact hs.2
    · intro hs
      exact ⟨⟨hs.1, le_trans hs.2 hτT⟩, hs⟩
  have hsubset : Set.Icc (0 : NNReal) τ ⊆ Set.Icc (0 : NNReal) T := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 hτT⟩
  have hinter' :
      Set.Icc (0 : NNReal) τ ∩ Set.Icc (0 : NNReal) T = Set.Icc (0 : NNReal) τ := by
    rw [Set.inter_comm, hinter]
  -- Proof comment: collapse the outer restriction with the inner prefix indicator.
  calc
    ∫ s in Set.Icc 0 T, Set.indicator (Set.Icc 0 τ) (fun _ ↦ (1 : ℝ)) s ∂μV
        = ∫ s, Set.indicator (Set.Icc 0 τ) (fun _ ↦ (1 : ℝ)) s
            ∂(μV.restrict (Set.Icc 0 T)) := by
          rfl
    _ = ∫ s in Set.Icc 0 τ, (1 : ℝ) ∂(μV.restrict (Set.Icc 0 T)) := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ s in Set.Icc 0 τ, (1 : ℝ) ∂μV := by
          simp [Measure.restrict_restrict, hinter']
    _ = V τ := by
          simpa using (hμV τ).symm

/-- Helper for Exercise 21.10.2: the unweighted quadratic sums are nonnegative term by term. -/
lemma weightedPartitionQuadraticVariationApproximationUpTo_one_nonneg
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    0 ≤ weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n := by
  -- Each summand is a square, so the whole finite sum stays nonnegative.
  rw [weightedPartitionQuadraticVariationApproximationUpTo_def]
  refine Finset.sum_nonneg ?_
  intro k hk
  simpa using sq_nonneg (X (partitionNextPointUpTo P n k T) - X (P n k))

/-- Helper for Exercise 21.10.2: specializing the weight to `1` recovers the convergence already
packaged in `HasSquareVariationAlongPartition`. -/
lemma tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {V : PathwiseProcess} (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    Tendsto
      (fun n : ℕ ↦ weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n)
      atTop
      (nhds (V T)) := by
  -- Rewrite the constant-weight sums to the defining square-variation partition sums.
  convert HasSquareVariationAlongPartition.tendsto_partition_sum hX T using 1
  ext n
  exact _root_.weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum X P T n

/-- Helper for Exercise 21.10.2: the constant-weight quadratic masses are eventually bounded by
`|V T| + 1` once they converge to `V T`. -/
lemma eventually_le_weightedPartitionQuadraticVariationApproximationUpTo_one_abs_add_one
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {V : PathwiseProcess} (hX : HasSquareVariationAlongPartition X P V)
    (T : NNReal) :
    ∀ᶠ n in atTop,
      weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n ≤
        |V T| + 1 := by
  -- Convergence to `V T` eventually traps the nonnegative masses inside the radius-`1` ball.
  have hconst :
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) X P T n)
        atTop
        (nhds (V T)) :=
    tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one X P hX T
  filter_upwards [hconst (Metric.ball_mem_nhds _ zero_lt_one)] with n hn
  have hball :
      V T <
          1 + weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n ∧
        weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n - V T < 1 := by
    simpa [Metric.ball, Real.dist_eq, abs_lt] using hn
  have hupper :
      weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n < V T + 1 := by
    linarith
  have hV_abs : V T + 1 ≤ |V T| + 1 := by
    gcongr
    exact le_abs_self (V T)
  exact le_of_lt (lt_of_lt_of_le hupper hV_abs)

/-- Helper for Exercise 21.10.2: a uniform error bound on `[0,T]` controls the difference of the
corresponding weighted quadratic sums by the unweighted quadratic mass. -/
lemma abs_sub_weightedPartitionQuadraticVariationApproximationUpTo_le
    (g h : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (T : NNReal) (ε : ℝ)
    (hε : ∀ s ∈ Set.Icc 0 T, |g s - h s| ≤ ε)
    (n : ℕ) :
    |weightedPartitionQuadraticVariationApproximationUpTo g X P T n -
        weightedPartitionQuadraticVariationApproximationUpTo h X P T n| ≤
      ε * weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n := by
  have hrewrite :
      weightedPartitionQuadraticVariationApproximationUpTo g X P T n -
          weightedPartitionQuadraticVariationApproximationUpTo h X P T n =
        Finset.sum (Finset.range (partitionBoundIndex P n T))
          (fun k ↦
            (g (P n k) - h (P n k)) *
              (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2) := by
    -- Rewrite the difference of weighted sums into one sum with coefficient `g - h`.
    rw [weightedPartitionQuadraticVariationApproximationUpTo_def,
      weightedPartitionQuadraticVariationApproximationUpTo_def, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k hk
    ring
  calc
    |weightedPartitionQuadraticVariationApproximationUpTo g X P T n -
        weightedPartitionQuadraticVariationApproximationUpTo h X P T n|
        = |Finset.sum (Finset.range (partitionBoundIndex P n T))
            (fun k ↦
              (g (P n k) - h (P n k)) *
                (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2)| := by
            rw [hrewrite]
    _ ≤ Finset.sum (Finset.range (partitionBoundIndex P n T))
          (fun k ↦
            |(g (P n k) - h (P n k)) *
              (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2|) := by
      exact
        Finset.abs_sum_le_sum_abs
          (fun k ↦
            (g (P n k) - h (P n k)) *
              (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2)
          (Finset.range (partitionBoundIndex P n T))
    _ = Finset.sum (Finset.range (partitionBoundIndex P n T))
          (fun k ↦
            |g (P n k) - h (P n k)| *
              (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hsquare_nonneg :
          0 ≤ (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2 := by
        exact sq_nonneg (X (partitionNextPointUpTo P n k T) - X (P n k))
      rw [abs_mul, abs_of_nonneg hsquare_nonneg]
    _ ≤ Finset.sum (Finset.range (partitionBoundIndex P n T))
          (fun k ↦ ε * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk' : k < partitionBoundIndex P n T := by
        exact Finset.mem_range.mp hk
      have hk_mem : P n k ∈ Set.Icc 0 T :=
        partitionPoint_mem_Icc_of_lt_partitionBoundIndex P n k T hk'
      have hpoint : |g (P n k) - h (P n k)| ≤ ε :=
        hε _ hk_mem
      have hsquare_nonneg :
          0 ≤ (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2 := by
        exact sq_nonneg (X (partitionNextPointUpTo P n k T) - X (P n k))
      have habs :
          |(g (P n k) - h (P n k)) *
              (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2|
            = |g (P n k) - h (P n k)| *
                (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2 := by
        rw [abs_mul, abs_of_nonneg hsquare_nonneg]
      -- Normalize the absolute value of the product before applying the coefficient bound.
      simpa [habs] using mul_le_mul_of_nonneg_right hpoint hsquare_nonneg
    _ = ε * weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n := by
      -- Factor out the constant coefficient `ε` and recover the constant-weight quadratic mass.
      rw [weightedPartitionQuadraticVariationApproximationUpTo_def, Finset.mul_sum]
      simp only [one_mul]

/-- Helper for Exercise 21.10.2: the weighted quadratic partition sum is additive in the weight.
-/
lemma weightedPartitionQuadraticVariationApproximationUpTo_add
    (g h : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    weightedPartitionQuadraticVariationApproximationUpTo (fun s ↦ g s + h s) X P T n =
      weightedPartitionQuadraticVariationApproximationUpTo g X P T n +
        weightedPartitionQuadraticVariationApproximationUpTo h X P T n := by
  -- Proof comment: expand the defining sum and distribute the coefficient over each square.
  rw [weightedPartitionQuadraticVariationApproximationUpTo_def,
    weightedPartitionQuadraticVariationApproximationUpTo_def,
    weightedPartitionQuadraticVariationApproximationUpTo_def]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

/-- Helper for Exercise 21.10.2: scaling the weight scales the weighted quadratic partition sum.
-/
lemma weightedPartitionQuadraticVariationApproximationUpTo_const_mul
    (c : ℝ) (g : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    weightedPartitionQuadraticVariationApproximationUpTo (fun s ↦ c * g s) X P T n =
      c * weightedPartitionQuadraticVariationApproximationUpTo g X P T n := by
  -- Proof comment: factor the scalar `c` out of the defining finite sum.
  rw [weightedPartitionQuadraticVariationApproximationUpTo_def,
    weightedPartitionQuadraticVariationApproximationUpTo_def, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  ring

/-- Helper for Exercise 21.10.2: a constant weight is the constant multiple of the unweighted
quadratic mass. -/
lemma weightedPartitionQuadraticVariationApproximationUpTo_const
    (c : ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ c) X P T n =
      c * weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n := by
  -- Proof comment: this is the scaling lemma specialized to the constant function `1`.
  simpa using
    weightedPartitionQuadraticVariationApproximationUpTo_const_mul
      c (fun _ ↦ (1 : ℝ)) X P T n

/-- Helper for Exercise 21.10.2: the weighted quadratic partition sum commutes with a finite sum
of weights. -/
lemma weightedPartitionQuadraticVariationApproximationUpTo_finset_sum
    {ι : Type*} (s : Finset ι) (w : ι → NNReal → ℝ)
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    weightedPartitionQuadraticVariationApproximationUpTo
        (fun t ↦ Finset.sum s fun i ↦ w i t) X P T n =
      Finset.sum s fun i ↦ weightedPartitionQuadraticVariationApproximationUpTo (w i) X P T n := by
  -- Proof comment: expand the outer weighted sum, distribute the inner finite sum over each square,
  -- and commute the two finite summations.
  simp_rw [weightedPartitionQuadraticVariationApproximationUpTo_def]
  calc
    Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
        (Finset.sum s fun i ↦ w i (P n k)) *
          (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2)
        =
          Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
            Finset.sum s fun i ↦
              w i (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [Finset.sum_mul]
    _ =
          Finset.sum s fun i ↦
            Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
              w i (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2) := by
            rw [Finset.sum_comm]
    _ =
          Finset.sum s fun i ↦
            weightedPartitionQuadraticVariationApproximationUpTo (w i) X P T n := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [weightedPartitionQuadraticVariationApproximationUpTo_def]

/-- Helper for Exercise 21.10.2: every coarse endpoint from the `m`-th partition row reappears in
every finer row. -/
lemma coarseEndpointIndexInRefinement
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (m i n : ℕ) (hmn : m ≤ n) :
    ∃ j : ℕ, P n j = P m i := by
  -- Move the coarse endpoint through the nested partition-point sets until row `n`.
  induction hmn with
  | refl =>
      exact ⟨i, rfl⟩
  | @step n hmn ih =>
      rcases ih with ⟨j, hj⟩
      have hmem : P m i ∈ partitionPointSet P (n + 1) := by
        exact hP.nested n ⟨j, hj⟩
      rcases hmem with ⟨j', hj'⟩
      exact ⟨j', hj'⟩

/-- Helper for Exercise 21.10.2: choose the index of the coarse endpoint `P m i` inside the finer
row `n` whenever `n ≥ m`. -/
noncomputable def coarseEndpointRefinementIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m i n : ℕ) : ℕ :=
  if hmn : m ≤ n then Classical.choose (coarseEndpointIndexInRefinement P m i n hmn) else 0

/-- Helper for Exercise 21.10.2: the chosen refinement index really evaluates to the original
coarse endpoint. -/
lemma coarseEndpointRefinementIndex_spec
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m i n : ℕ) (hmn : m ≤ n) :
    P n (coarseEndpointRefinementIndex P m i n) = P m i := by
  -- Unfold the choice and read off the witness equation.
  rw [coarseEndpointRefinementIndex, dif_pos hmn]
  exact Classical.choose_spec (coarseEndpointIndexInRefinement P m i n hmn)

/-- Helper for Exercise 21.10.2: any partition point strictly before `T` occurs strictly before
the truncation index `partitionBoundIndex P n T`. -/
lemma lt_partitionBoundIndex_of_partitionPoint_lt_time
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n j : ℕ) (T : NNReal) (hjT : P n j < T) :
    j < partitionBoundIndex P n T := by
  -- If `j` were beyond the truncation index, strict monotonicity would force `P n j ≥ T`.
  by_contra hj
  have hbound : partitionBoundIndex P n T ≤ j := Nat.not_lt.mp hj
  have hmono :
      P n (partitionBoundIndex P n T) ≤ P n j :=
    (hP.strictMono n).monotone hbound
  exact not_le_of_gt hjT (le_trans (le_partitionBoundIndex_time P n T) hmono)

/-- Helper for Exercise 21.10.2: if the horizon is itself the partition point `P n k`, then the
truncation index is exactly `k`. -/
lemma partitionBoundIndex_eq_of_partitionPoint
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n k : ℕ) :
    partitionBoundIndex P n (P n k) = k := by
  apply Nat.le_antisymm
  · -- Proof comment: `k` itself reaches the horizon `P n k`.
    simpa [partitionBoundIndex] using
      (Nat.find_min' (exists_partition_index_le_time P n (P n k))
        (show P n k ≤ P n k from le_rfl))
  · -- Proof comment: any smaller index still lies strictly before `P n k`.
    exact Nat.le_of_not_gt fun hklt ↦
      (not_lt_of_ge (le_partitionBoundIndex_time P n (P n k)))
        ((hP.strictMono n) hklt)

/-- Helper for Exercise 21.10.2: the truncation index is monotone in the time horizon. -/
lemma partitionBoundIndex_monotone
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) {S T : NNReal} (hST : S ≤ T) :
    partitionBoundIndex P n S ≤ partitionBoundIndex P n T := by
  -- Proof comment: the index that already reaches `T` also reaches every smaller horizon `S`.
  refine Nat.find_min' (exists_partition_index_le_time P n S) ?_
  exact le_trans hST (le_partitionBoundIndex_time P n T)

/-- Helper for Exercise 21.10.2: the predecessor partition point immediately before the truncation
time `T` in the `n`-th row. When `partitionBoundIndex P n T = 0`, this defaults to the initial
point `P n 0 = 0`. -/
noncomputable def partitionPredecessorPoint
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) (T : NNReal) : NNReal :=
  P n (partitionBoundIndex P n T - 1)

/-- Helper for Exercise 21.10.2: the predecessor partition point lies in `[0,T]`. -/
lemma partitionPredecessorPoint_le_time
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) (T : NNReal) :
    partitionPredecessorPoint P n T ≤ T := by
  rcases Nat.eq_zero_or_pos (partitionBoundIndex P n T) with hidx | hidx
  · -- Proof comment: if the truncation index is `0`, then `T` is already the initial time.
    have hzero : P n 0 = 0 := hP.zero_eq n
    have hT0 : T = 0 := by
      have hle0 : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0' : T ≤ 0 := by simpa [hzero] using hle0
      exact le_antisymm hle0' bot_le
    have hidx0 : partitionBoundIndex P n 0 = 0 := by
      simpa [hT0] using hidx
    simp [partitionPredecessorPoint, hidx0, hT0, hzero]
  · -- Proof comment: otherwise the predecessor is the row entry immediately before the first
    -- point that reaches `T`.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P n T = k + 1 :=
      ⟨partitionBoundIndex P n T - 1, (Nat.sub_add_cancel hidx).symm⟩
    have hk_lt : k < partitionBoundIndex P n T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hk_time : P n k < T :=
      partitionPoint_lt_time_of_lt_partitionBoundIndex P n k T hk_lt
    have hpred : partitionPredecessorPoint P n T = P n k := by
      simp [partitionPredecessorPoint, hk]
    simpa [hpred] using le_of_lt hk_time

/-- Helper for Exercise 21.10.2: a clipped successor interval in the `n`-th row has size at most
one mesh width whenever its left endpoint lies before `T`. -/
lemma edist_partitionPoint_partitionNextPointUpTo_le_partitionMesh
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    edist (P n k) (partitionNextPointUpTo P n k T) ≤ partitionMesh P n := by
  have hleft :
      P n k ≤ partitionNextPointUpTo P n k T := by
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt ((hP.strictMono n) (Nat.lt_succ_self k))
    · exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n k T hk)
  have hright :
      partitionNextPointUpTo P n k T ≤ P n (k + 1) := by
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hdist :
      edist (P n k) (partitionNextPointUpTo P n k T) ≤ edist (P n k) (P n (k + 1)) := by
    have hsucc :
        P n k < P n (k + 1) := by
      exact (hP.strictMono n) (Nat.lt_succ_self k)
    rw [edist_nndist, edist_nndist, NNReal.nndist_eq, NNReal.nndist_eq,
      tsub_eq_zero_of_le hleft, tsub_eq_zero_of_le (le_of_lt hsucc), max_eq_right, max_eq_right]
    · exact_mod_cast tsub_le_tsub_right hright _
    · simp
    · simp
  calc
    edist (P n k) (partitionNextPointUpTo P n k T)
        ≤ edist (P n k) (P n (k + 1)) := hdist
    _ ≤ partitionMesh P n := by
      rw [partitionMesh]
      exact le_iSup (fun j ↦ edist (P n j) (P n (j + 1))) k

/-- Helper for Exercise 21.10.2: the predecessor partition point lies within one mesh width of the
horizon. -/
lemma partitionPredecessorPointWithinMesh
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) (T : NNReal) :
    edist (partitionPredecessorPoint P n T) T ≤ partitionMesh P n := by
  rcases Nat.eq_zero_or_pos (partitionBoundIndex P n T) with hidx | hidx
  · -- Proof comment: when the truncation index is `0`, admissibility again forces `T = 0`.
    have hzero : P n 0 = 0 := hP.zero_eq n
    have hT0 : T = 0 := by
      have hle0 : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0' : T ≤ 0 := by simpa [hzero] using hle0
      exact le_antisymm hle0' bot_le
    have hidx0 : partitionBoundIndex P n 0 = 0 := by
      simpa [hT0] using hidx
    simp [partitionPredecessorPoint, hidx0, hT0, hzero]
  · -- Proof comment: identify the predecessor with a partition point and rewrite the clipped
    -- successor to `T`, so the one-mesh interval estimate applies directly.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P n T = k + 1 :=
      ⟨partitionBoundIndex P n T - 1, (Nat.sub_add_cancel hidx).symm⟩
    have hk_lt : k < partitionBoundIndex P n T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hT_le_next : T ≤ P n (k + 1) := by
      simpa [hk] using le_partitionBoundIndex_time P n T
    have hpred : partitionPredecessorPoint P n T = P n k := by
      simp [partitionPredecessorPoint, hk]
    have hnext : partitionNextPointUpTo P n k T = T := by
      rw [partitionNextPointUpTo, min_eq_right hT_le_next]
    simpa [hpred, hnext] using
      edist_partitionPoint_partitionNextPointUpTo_le_partitionMesh P n k T hk_lt

/-- Helper for Exercise 21.10.2: after reindexing a coarse endpoint inside a finer row, the next
clipped successor still lies within one mesh width of that coarse endpoint. -/
lemma edist_coarseEndpoint_partitionNextPointUpTo_le_partitionMesh
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m i n : ℕ) (T : NNReal) (hmn : m ≤ n) (hiT : P m i < T) :
    edist (P m i)
        (partitionNextPointUpTo P n (coarseEndpointRefinementIndex P m i n) T) ≤
      partitionMesh P n := by
  let j := coarseEndpointRefinementIndex P m i n
  have hjEq : P n j = P m i :=
    coarseEndpointRefinementIndex_spec P m i n hmn
  have hjT : P n j < T := by
    simpa [hjEq] using hiT
  have hjBound : j < partitionBoundIndex P n T :=
    lt_partitionBoundIndex_of_partitionPoint_lt_time P n j T hjT
  -- Rewrite the coarse endpoint through the chosen refinement index and apply the one-mesh bound.
  simpa [j, hjEq] using
    edist_partitionPoint_partitionNextPointUpTo_le_partitionMesh P n
      (coarseEndpointRefinementIndex P m i n) T hjBound

/-- Helper for Exercise 21.10.2: if the indicator weight is the prefix
`Set.indicator (Set.Icc 0 (P n j)) (fun _ ↦ 1)`, then the weighted quadratic sum up to `T` splits
into the constant-weight sum up to `P n j` plus the single boundary increment that starts at
`P n j`. -/
lemma weightedPartitionQuadraticVariationApproximationUpTo_indicatorIcc_eq_endpointPlusBoundary
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n j : ℕ) (T : NNReal) (hjT : P n j < T) :
    weightedPartitionQuadraticVariationApproximationUpTo
        (Set.indicator (Set.Icc 0 (P n j)) (fun _ ↦ (1 : ℝ))) X P T n =
      weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P (P n j) n +
        (X (partitionNextPointUpTo P n j T) - X (P n j)) ^ 2 := by
  let term : ℕ → ℝ := fun k ↦
    Set.indicator (Set.Icc 0 (P n j)) (fun _ ↦ (1 : ℝ)) (P n k) *
      (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2
  have hjBound : j < partitionBoundIndex P n T :=
    lt_partitionBoundIndex_of_partitionPoint_lt_time P n j T hjT
  have hboundEq : partitionBoundIndex P n (P n j) = j :=
    partitionBoundIndex_eq_of_partitionPoint P n j
  have htruncate :
      weightedPartitionQuadraticVariationApproximationUpTo
          (Set.indicator (Set.Icc 0 (P n j)) (fun _ ↦ (1 : ℝ))) X P T n =
        Finset.sum (Finset.range (j + 1)) term := by
    rw [weightedPartitionQuadraticVariationApproximationUpTo_def]
    have hsplit :
        Finset.sum (Finset.range (partitionBoundIndex P n T)) term =
          Finset.sum (Finset.range (j + 1)) term +
            Finset.sum (Finset.Ico (j + 1) (partitionBoundIndex P n T)) term := by
      symm
      exact Finset.sum_range_add_sum_Ico term (Nat.succ_le_of_lt hjBound)
    have htail :
        Finset.sum (Finset.Ico (j + 1) (partitionBoundIndex P n T)) term = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hjk : j < k := by
        exact lt_of_lt_of_le (Nat.lt_succ_self j) (Finset.mem_Ico.mp hk).1
      have hnotmem : P n k ∉ Set.Icc 0 (P n j) := by
        have hlt : P n j < P n k :=
          (hP.strictMono n) hjk
        simp [Set.mem_Icc, not_le_of_gt hlt]
      -- Proof comment: once the left endpoint lies strictly beyond `P n j`, the indicator
      -- coefficient vanishes.
      simp [term, hnotmem]
    rw [hsplit, htail, add_zero]
  have hprefix :
      Finset.sum (Finset.range j) term =
        weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P (P n j) n := by
    rw [weightedPartitionQuadraticVariationApproximationUpTo_def, hboundEq]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < j := Finset.mem_range.mp hk
    have hk_mem : P n k ∈ Set.Icc 0 (P n j) := by
      constructor
      · exact bot_le
      · exact
          (hP.strictMono n).monotone
            (Nat.le_of_lt hklt)
    have hk1_le : k + 1 ≤ j := Nat.succ_le_of_lt hklt
    have hk1_le_endpoint :
        P n (k + 1) ≤ P n j :=
      (hP.strictMono n).monotone hk1_le
    have hk1_le_time : P n (k + 1) ≤ T := le_trans hk1_le_endpoint (le_of_lt hjT)
    -- Proof comment: before the coarse endpoint `P n j`, both truncations use the same successor.
    simp [term, hk_mem, partitionNextPointUpTo, min_eq_left hk1_le_endpoint,
      min_eq_left hk1_le_time]
  have hj_mem : P n j ∈ Set.Icc 0 (P n j) := by
    constructor
    · exact bot_le
    · exact le_rfl
  -- Proof comment: split off the unique nonzero boundary term at the endpoint `P n j`.
  calc
    weightedPartitionQuadraticVariationApproximationUpTo
        (Set.indicator (Set.Icc 0 (P n j)) (fun _ ↦ (1 : ℝ))) X P T n
        = Finset.sum (Finset.range (j + 1)) term := htruncate
    _ = Finset.sum (Finset.range j) term + term j := by
          rw [Finset.sum_range_succ]
    _ = weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P (P n j) n +
          (X (partitionNextPointUpTo P n j T) - X (P n j)) ^ 2 := by
          rw [hprefix]
          simp [term, hj_mem]

/-- Helper for Exercise 21.10.2: after reindexing a coarse endpoint into a finer row, the
`Set.Icc`-indicator weighted sum splits into the endpoint value and one boundary increment. -/
lemma weightedPartitionQuadraticVariationApproximationUpTo_indicatorIcc_eq_coarseEndpointPlusBoundary
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m i n : ℕ) (T : NNReal) (hmn : m ≤ n) (hiT : P m i < T) :
    weightedPartitionQuadraticVariationApproximationUpTo
        (Set.indicator (Set.Icc 0 (P m i)) (fun _ ↦ (1 : ℝ))) X P T n =
      weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P (P m i) n +
        (X (partitionNextPointUpTo P n (coarseEndpointRefinementIndex P m i n) T) -
            X (P m i)) ^ 2 := by
  let j := coarseEndpointRefinementIndex P m i n
  have hjEq : P n j = P m i :=
    coarseEndpointRefinementIndex_spec P m i n hmn
  have hjT : P n j < T := by
    simpa [j, hjEq] using hiT
  -- Proof comment: rewrite the coarse endpoint through its refined-row index and use the single
  -- partition-point decomposition.
  simpa [j, hjEq] using
    weightedPartitionQuadraticVariationApproximationUpTo_indicatorIcc_eq_endpointPlusBoundary
      X P n j T hjT

/-- Helper for Exercise 21.10.2: the canonical coarse staircase on `[0,T]` built from the
`m`-th partition row, written as a constant plus nested prefix indicators. -/
noncomputable def coarseIccStep
    (f : NNReal → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m : ℕ) (T : NNReal) : NNReal → ℝ :=
  fun s ↦
    f (P m (partitionBoundIndex P m T - 1)) +
      Finset.sum (Finset.range (partitionBoundIndex P m T - 1)) fun i ↦
        (f (P m i) - f (P m (i + 1))) *
          Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ)) s

/-- Helper for Exercise 21.10.2: on `[0,T]`, the canonical coarse `Set.Icc`-staircase equals the
value of `f` at the predecessor partition point of the evaluation time. -/
lemma coarseIccStep_eq_partitionPredecessorValue
    (f : NNReal → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (m : ℕ) (T s : NNReal) (hsT : s ∈ Set.Icc 0 T) :
    coarseIccStep f P m T s = f (partitionPredecessorPoint P m s) := by
  let N := partitionBoundIndex P m T
  let q := partitionBoundIndex P m s
  rcases Nat.eq_zero_or_pos q with hq | hq
  · have hs0 : s = 0 := by
      have hzero : P m 0 = 0 := hP.zero_eq m
      have hle0 : s ≤ P m 0 := by
        simpa [q, hq] using le_partitionBoundIndex_time P m s
      have hs_le_zero : s ≤ 0 := by simpa [hzero] using hle0
      exact le_antisymm hs_le_zero hsT.1
    have hpred : partitionPredecessorPoint P m s = P m 0 := by
      simp [partitionPredecessorPoint, q, hq]
    have hall :
        ∀ i ∈ Finset.range (N - 1),
          Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ)) s = 1 := by
      intro i hi
      have hs_mem : s ∈ Set.Icc 0 (P m (i + 1)) := by
        constructor
        · simpa [hs0] using hsT.1
        · simpa [hs0] using (bot_le : (0 : NNReal) ≤ P m (i + 1))
      simp [hs_mem]
    have hallTerm :
        ∀ i ∈ Finset.range (N - 1),
          (f (P m i) - f (P m (i + 1))) *
              Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ)) s =
            (f (P m i) - f (P m (i + 1))) := by
      intro i hi
      rw [hall i hi, mul_one]
    -- Proof comment: when `s = 0`, every prefix indicator is active and the staircase telescopes
    -- back to the initial endpoint value.
    calc
      coarseIccStep f P m T s
          = f (P m (N - 1)) +
              Finset.sum (Finset.range (N - 1)) (fun i ↦ f (P m i) - f (P m (i + 1))) := by
                rw [coarseIccStep]
                simp only [N]
                congr 1
                refine Finset.sum_congr rfl ?_
                intro i hi
                exact hallTerm i hi
      _ = f (P m 0) := by
            rw [Finset.sum_range_sub']
            ring
      _ = f (partitionPredecessorPoint P m s) := by
            simpa [hpred] using congrArg f hpred.symm
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, q = j + 1 := ⟨q - 1, (Nat.sub_add_cancel hq).symm⟩
    have hq_le_N : q ≤ N := by
      simpa [q, N] using partitionBoundIndex_monotone P m hsT.2
    have hj_lt_N : j < N := by
      have : j + 1 ≤ N := by simpa [hj] using hq_le_N
      exact lt_of_lt_of_le (Nat.lt_succ_self j) this
    have hj_le_Nm1 : j ≤ N - 1 := Nat.le_pred_of_lt hj_lt_N
    have hpred : partitionPredecessorPoint P m s = P m j := by
      simp [partitionPredecessorPoint, q, hj]
    let term : ℕ → ℝ := fun i ↦
      (f (P m i) - f (P m (i + 1))) *
        Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ)) s
    have hsplit :
        Finset.sum (Finset.range (N - 1)) term =
          Finset.sum (Finset.range j) term + Finset.sum (Finset.Ico j (N - 1)) term := by
      symm
      exact Finset.sum_range_add_sum_Ico term hj_le_Nm1
    have hleft :
        Finset.sum (Finset.range j) term = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hi_lt : i < j := Finset.mem_range.mp hi
      have hi_lt_q : i + 1 < q := by simpa [hj] using Nat.succ_lt_succ hi_lt
      have hi_time : P m (i + 1) < s :=
        partitionPoint_lt_time_of_lt_partitionBoundIndex P m (i + 1) s hi_lt_q
      have hnotmem : s ∉ Set.Icc 0 (P m (i + 1)) := by
        simp [Set.mem_Icc, not_le_of_gt hi_time]
      -- Proof comment: before the predecessor interval, the corresponding prefix indicators are
      -- already off.
      simp [term, hnotmem]
    have hright :
        Finset.sum (Finset.Ico j (N - 1)) term =
          Finset.sum (Finset.Ico j (N - 1)) (fun i ↦ f (P m i) - f (P m (i + 1))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hq_time : s ≤ P m (j + 1) := by
        simpa [q, hj] using le_partitionBoundIndex_time P m s
      have hi_ge : j ≤ i := (Finset.mem_Ico.mp hi).1
      have hs_le : s ≤ P m (i + 1) := by
        refine le_trans hq_time ?_
        exact
          (hP.strictMono m).monotone
            (Nat.succ_le_succ hi_ge)
      have hs_mem : s ∈ Set.Icc 0 (P m (i + 1)) := ⟨hsT.1, hs_le⟩
      -- Proof comment: from the predecessor interval onward, every prefix indicator is active.
      simp [term, hs_mem]
    have htail :
        Finset.sum (Finset.Ico j (N - 1)) (fun i ↦ f (P m i) - f (P m (i + 1))) =
          f (P m j) - f (P m (N - 1)) := by
      rw [Finset.sum_Ico_eq_sub _ hj_le_Nm1, Finset.sum_range_sub', Finset.sum_range_sub']
      ring
    -- Proof comment: once the zero and one regions are separated, the remaining finite
    -- difference sum telescopes to the predecessor endpoint value.
    calc
      coarseIccStep f P m T s
          = f (P m (N - 1)) + Finset.sum (Finset.range (N - 1)) term := by
              simp [coarseIccStep, N, term]
      _ = f (P m (N - 1)) +
            (Finset.sum (Finset.range j) term + Finset.sum (Finset.Ico j (N - 1)) term) := by
              rw [hsplit]
      _ = f (P m (N - 1)) + Finset.sum (Finset.Ico j (N - 1)) term := by
              simp [hleft]
      _ = f (P m (N - 1)) +
            Finset.sum (Finset.Ico j (N - 1)) (fun i ↦ f (P m i) - f (P m (i + 1))) := by
              rw [hright]
      _ = f (P m j) := by
            rw [htail]
            ring
      _ = f (partitionPredecessorPoint P m s) := by
            simpa [hpred] using congrArg f hpred.symm

/-- Helper for Exercise 21.10.2: some coarse `Set.Icc`-staircase uniformly approximates the
continuous weight `f` on `[0,T]`. -/
lemma exists_coarseIccStep_uniformApprox
    (f : NNReal → ℝ) (hf : Continuous f)
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (T : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∀ s ∈ Set.Icc 0 T, |f s - coarseIccStep f P m T s| ≤ ε := by
  have hUC :
      UniformContinuousOn f (Set.Icc 0 T) :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).uniformContinuousOn_of_continuous
      hf.continuousOn
  rcases (Metric.uniformContinuousOn_iff_le.mp hUC) ε hε with ⟨δ, hδ, hδclose⟩
  have hmesh :
      ∀ᶠ m in atTop, partitionMesh P m ≤ ENNReal.ofReal δ := by
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          hP.mesh_tendsto_zero)
          (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) with
      ⟨M, hM⟩
    exact Filter.eventually_atTop.2 ⟨M, hM⟩
  rcases Filter.eventually_atTop.1 hmesh with ⟨m, hm⟩
  have hm0 : partitionMesh P m ≤ ENNReal.ofReal δ := hm m le_rfl
  refine ⟨m, ?_⟩
  intro s hs
  have hpred_mem : partitionPredecessorPoint P m s ∈ Set.Icc 0 T := by
    constructor
    · exact bot_le
    · exact le_trans (partitionPredecessorPoint_le_time P m s) hs.2
  have hpred_dist :
      dist s (partitionPredecessorPoint P m s) ≤ δ := by
    have hedist :
        edist s (partitionPredecessorPoint P m s) ≤ partitionMesh P m := by
      simpa [edist_comm] using partitionPredecessorPointWithinMesh P m s
    have hedist' :
        edist s (partitionPredecessorPoint P m s) ≤ ENNReal.ofReal δ :=
      le_trans hedist hm0
    exact
      (ENNReal.ofReal_le_ofReal_iff hδ.le).mp
        (by simpa [edist_dist] using hedist')
  have hclose :
      dist (f s) (f (partitionPredecessorPoint P m s)) ≤ ε :=
    hδclose s hs (partitionPredecessorPoint P m s) hpred_mem hpred_dist
  -- Proof comment: the staircase value is the predecessor-point sample of `f`, and that sample
  -- stays within one mesh width of `s`.
  simpa [Real.dist_eq, coarseIccStep_eq_partitionPredecessorValue f P m T s hs] using hclose

/-- Helper for Exercise 21.10.2: the clipped successor of a coarse endpoint converges back to that
endpoint, so the corresponding boundary square vanishes. -/
lemma tendsto_coarseEndpoint_boundaryIncrementSq_zero
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (m i : ℕ) (T : NNReal) (hiT : P m i < T) :
    Tendsto
      (fun n : ℕ ↦
        (X (partitionNextPointUpTo P n (coarseEndpointRefinementIndex P m i n) T) -
            X (P m i)) ^ 2)
      atTop
      (nhds 0) := by
  let q : ℕ → NNReal := fun n ↦
    if hmn : m ≤ n then
      partitionNextPointUpTo P n (coarseEndpointRefinementIndex P m i n) T
    else
      P m i
  have hq :
      Tendsto q atTop (nhds (P m i)) := by
    rw [tendsto_iff_edist_tendsto_0]
    -- Proof comment: after row `m`, every clipped successor stays within one mesh width of the
    -- coarse endpoint, and the mesh tends to `0`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hP.mesh_tendsto_zero
      (fun n ↦ bot_le) ?_
    intro n
    by_cases hmn : m ≤ n
    · simpa [q, hmn, edist_comm] using
        edist_coarseEndpoint_partitionNextPointUpTo_le_partitionMesh P m i n T hmn hiT
    · simp [q, hmn]
  have hXq :
      Tendsto (fun n : ℕ ↦ X (q n)) atTop (nhds (X (P m i))) :=
    ((X.continuousAt (P m i)).tendsto.comp hq)
  have hdiff :
      Tendsto (fun n : ℕ ↦ X (q n) - X (P m i)) atTop (nhds 0) := by
    -- Proof comment: continuity of the path turns the endpoint convergence into vanishing
    -- boundary increments.
    have hconstX :
        Tendsto (fun _ : ℕ ↦ X (P m i)) atTop (nhds (X (P m i))) :=
      tendsto_const_nhds
    simpa using hXq.sub hconstX
  have hsq :
      Tendsto (fun n : ℕ ↦ (X (q n) - X (P m i)) ^ 2) atTop (nhds 0) := by
    -- Proof comment: squaring preserves the convergence of the boundary increment to `0`.
    simpa [pow_two] using hdiff.mul hdiff
  have hevent :
      (fun n : ℕ ↦ (X (q n) - X (P m i)) ^ 2) =ᶠ[atTop]
        (fun n : ℕ ↦
          (X (partitionNextPointUpTo P n (coarseEndpointRefinementIndex P m i n) T) -
              X (P m i)) ^ 2) := by
    filter_upwards [eventually_ge_atTop m] with n hmn
    simp [q, hmn]
  exact Tendsto.congr' hevent hsq

/-- Helper for Exercise 21.10.2: the weighted sum for a single prefix indicator converges to the
matching endpoint value of the square-variation path. -/
lemma tendsto_weightedPartitionQuadraticVariationApproximationUpTo_indicatorIcc
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {V : PathwiseProcess} (hX : HasSquareVariationAlongPartition X P V)
    (m i : ℕ) (T : NNReal) (hiT : P m i < T) :
    Tendsto
      (fun n : ℕ ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (Set.indicator (Set.Icc 0 (P m i)) (fun _ ↦ (1 : ℝ))) X P T n)
      atTop
      (nhds (V (P m i))) := by
  have hendpoint :
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) X P (P m i) n)
        atTop
        (nhds (V (P m i))) :=
    tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one X P hX (P m i)
  have hboundary :
      Tendsto
        (fun n : ℕ ↦
          (X (partitionNextPointUpTo P n (coarseEndpointRefinementIndex P m i n) T) -
              X (P m i)) ^ 2)
        atTop
        (nhds 0) :=
    tendsto_coarseEndpoint_boundaryIncrementSq_zero X P m i T hiT
  have hsplit :
      (fun n : ℕ ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (fun _ ↦ (1 : ℝ)) X P (P m i) n +
            (X (partitionNextPointUpTo P n (coarseEndpointRefinementIndex P m i n) T) -
                X (P m i)) ^ 2) =ᶠ[atTop]
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (Set.indicator (Set.Icc 0 (P m i)) (fun _ ↦ (1 : ℝ))) X P T n) := by
    filter_upwards [eventually_ge_atTop m] with n hmn
    symm
    exact
      weightedPartitionQuadraticVariationApproximationUpTo_indicatorIcc_eq_coarseEndpointPlusBoundary
        X P m i n T hmn hiT
  -- Proof comment: the indicator weight is the endpoint constant-weight sum plus one boundary
  -- square, and that boundary square tends to `0`.
  simpa using Tendsto.congr' hsplit (hendpoint.add hboundary)

/-- Helper for Exercise 21.10.2: the coarse `Set.Icc`-staircase weight has the expected limit as a
finite linear combination of endpoint square-variation values. -/
lemma tendsto_weightedPartitionQuadraticVariationApproximationUpTo_coarseIccStep_linearCombination
    (f : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    {V : PathwiseProcess} (hX : HasSquareVariationAlongPartition X P V)
    (m : ℕ) (T : NNReal) :
    Tendsto
      (fun n : ℕ ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (coarseIccStep f P m T) X P T n)
      atTop
      (nhds
        (f (P m (partitionBoundIndex P m T - 1)) * V T +
          Finset.sum (Finset.range (partitionBoundIndex P m T - 1)) fun i ↦
            (f (P m i) - f (P m (i + 1))) * V (P m (i + 1)))) := by
  let N := partitionBoundIndex P m T
  let cLast : ℝ := f (P m (N - 1))
  let coeff : ℕ → ℝ := fun i ↦ f (P m i) - f (P m (i + 1))
  let indicatorWeight : ℕ → NNReal → ℝ := fun i s ↦
    coeff i * Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ)) s
  have hconst :
      Tendsto
        (fun n : ℕ ↦
          cLast *
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) X P T n)
        atTop
        (nhds (cLast * V T)) := by
    -- Proof comment: the constant part of the staircase uses the already-known constant-weight
    -- convergence.
    simpa [cLast] using
      tendsto_const_nhds.mul
        (tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one X P hX T)
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i *
              weightedPartitionQuadraticVariationApproximationUpTo
                (Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ))) X P T n)
        atTop
        (nhds
          (Finset.sum (Finset.range (N - 1)) fun i ↦ coeff i * V (P m (i + 1)))) := by
    -- Proof comment: every prefix-indicator term converges to the matching endpoint value, and a
    -- finite sum preserves convergence.
    refine tendsto_finset_sum _ fun i hi ↦ ?_
    have hi_lt : i < N - 1 := Finset.mem_range.mp hi
    have hi_succ_lt : i + 1 < (N - 1) + 1 := Nat.succ_lt_succ hi_lt
    have hN : 0 < N := by
      exact lt_of_lt_of_le (Nat.zero_lt_succ i) (le_trans (Nat.succ_le_of_lt hi_lt) (Nat.sub_le _ _))
    have hN_eq : (N - 1) + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hN)
    have hi' : i + 1 < N := by
      simpa [hN_eq] using hi_succ_lt
    have hiT : P m (i + 1) < T :=
      partitionPoint_lt_time_of_lt_partitionBoundIndex P m (i + 1) T hi'
    simpa [coeff] using
      tendsto_const_nhds.mul
        (tendsto_weightedPartitionQuadraticVariationApproximationUpTo_indicatorIcc
          X P hX m (i + 1) T hiT)
  have hsumRewrite :
      ∀ n : ℕ,
        weightedPartitionQuadraticVariationApproximationUpTo
            (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s) X P T n =
          Finset.sum (Finset.range (N - 1)) fun i ↦
            weightedPartitionQuadraticVariationApproximationUpTo (indicatorWeight i) X P T n := by
    intro n
    -- Proof comment: the weighted partition sum is linear in finite sums of weights.
    rw [weightedPartitionQuadraticVariationApproximationUpTo_finset_sum]
  have hcoeffRewrite :
      ∀ n : ℕ,
        (Finset.sum (Finset.range (N - 1)) fun i ↦
            weightedPartitionQuadraticVariationApproximationUpTo (indicatorWeight i) X P T n) =
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i *
              weightedPartitionQuadraticVariationApproximationUpTo
                (Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ))) X P T n := by
    intro n
    -- Proof comment: factor the scalar coefficient out of each indicator summand.
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [weightedPartitionQuadraticVariationApproximationUpTo_const_mul]
  -- Proof comment: rewrite the staircase weight into its constant part plus the finite indicator
  -- family, then combine the two convergence statements above.
  convert hconst.add hsum using 1
  ext n
  calc
    weightedPartitionQuadraticVariationApproximationUpTo
        (coarseIccStep f P m T) X P T n
        =
          weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ cLast) X P T n +
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s) X P T n := by
          change
            weightedPartitionQuadraticVariationApproximationUpTo
                (fun s ↦ (fun _ ↦ cLast) s +
                  Finset.sum (Finset.range (N - 1)) (fun i ↦ indicatorWeight i s)) X P T n =
              weightedPartitionQuadraticVariationApproximationUpTo
                  (fun _ ↦ cLast) X P T n +
                weightedPartitionQuadraticVariationApproximationUpTo
                  (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s) X P T n
          simpa [coarseIccStep, N, cLast, coeff, indicatorWeight] using
            weightedPartitionQuadraticVariationApproximationUpTo_add
              (fun _ ↦ cLast)
              (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s)
              X P T n
    _ =
          cLast *
              weightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ)) X P T n +
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s) X P T n := by
          rw [weightedPartitionQuadraticVariationApproximationUpTo_const]
    _ =
          cLast *
              weightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ)) X P T n +
            Finset.sum (Finset.range (N - 1)) fun i ↦
              weightedPartitionQuadraticVariationApproximationUpTo (indicatorWeight i) X P T n := by
          rw [hsumRewrite n]
    _ =
          cLast *
              weightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ)) X P T n +
            Finset.sum (Finset.range (N - 1)) fun i ↦
              coeff i *
                weightedPartitionQuadraticVariationApproximationUpTo
                  (Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ))) X P T n := by
          rw [hcoeffRewrite n]

/-- Helper for Exercise 21.10.2: the coarse `Set.Icc`-staircase is integrable on `[0,T]` against
the canonical bracket measure. -/
lemma integrableOn_coarseIccStep_squareVariationBracketMeasure
    (f : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P)
    (m : ℕ) (T : NNReal) :
    IntegrableOn (coarseIccStep f P m T) (Set.Icc 0 T) (squareVariationBracketMeasure X P hX) := by
  let μ := squareVariationBracketMeasure X P hX
  let ν : Measure NNReal := μ.restrict (Set.Icc 0 T)
  let N := partitionBoundIndex P m T
  let cLast : ℝ := f (P m (N - 1))
  let coeff : ℕ → ℝ := fun i ↦ f (P m i) - f (P m (i + 1))
  have hν_univ_lt_top : ν Set.univ < ⊤ := by
    simpa [ν] using (squareVariationBracketMeasure_Icc_lt_top X P hX T).lt_top
  letI : IsFiniteMeasure ν := ⟨hν_univ_lt_top⟩
  have hconst :
      Integrable (fun _ : NNReal ↦ cLast) ν := by
    exact integrable_const cLast
  have hindicator :
      ∀ i : ℕ,
        Integrable
          (Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ))) ν := by
    intro i
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  have hsum :
      Integrable
        (fun s : NNReal ↦
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i *
              Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s) ν := by
    exact
      integrable_finset_sum (Finset.range (N - 1)) fun i hi ↦
        (hindicator i).const_mul (coeff i)
  -- Proof comment: the staircase is a constant plus a finite sum of bounded indicator terms, so
  -- integrability follows termwise.
  change
    Integrable
      (fun s : NNReal ↦
        (fun _ : NNReal ↦ cLast) s +
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i *
              Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s) ν
  simpa [coarseIccStep, N, cLast, coeff] using hconst.add hsum

/-- Helper for Exercise 21.10.2: integrating the coarse `Set.Icc`-staircase against the canonical
bracket measure produces the same finite linear combination as on the partition-sum side. -/
lemma setIntegral_coarseIccStep_eq_linearCombination
    (f : NNReal → ℝ) (X : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P)
    (m : ℕ) (T : NNReal) :
    ∫ s in Set.Icc 0 T, coarseIccStep f P m T s ∂(squareVariationBracketMeasure X P hX) =
      f (P m (partitionBoundIndex P m T - 1)) * squareVariationBracket X P hX T +
        Finset.sum (Finset.range (partitionBoundIndex P m T - 1)) fun i ↦
          (f (P m i) - f (P m (i + 1))) *
            squareVariationBracket X P hX (P m (i + 1)) := by
  let μ := squareVariationBracketMeasure X P hX
  let ν : Measure NNReal := μ.restrict (Set.Icc 0 T)
  let V := squareVariationBracket X P hX
  let N := partitionBoundIndex P m T
  let cLast : ℝ := f (P m (N - 1))
  let coeff : ℕ → ℝ := fun i ↦ f (P m i) - f (P m (i + 1))
  have hν_univ_lt_top : ν Set.univ < ⊤ := by
    simpa [ν] using (squareVariationBracketMeasure_Icc_lt_top X P hX T).lt_top
  letI : IsFiniteMeasure ν := ⟨hν_univ_lt_top⟩
  have hμV :
      ∀ S : NNReal, V S = ∫ _ in Set.Icc 0 S, (1 : ℝ) ∂μ := by
    simpa [V, μ] using squareVariationBracketMeasure_realizes_path X P hX
  have hconst :
      Integrable (fun _ : NNReal ↦ cLast) ν := by
    exact integrable_const cLast
  have hindicator :
      ∀ i : ℕ,
        Integrable
          (Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ))) ν := by
    intro i
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  have htermInt :
      ∀ i ∈ Finset.range (N - 1),
        Integrable
          (fun s : NNReal ↦
            coeff i *
              Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s) ν := by
    intro i hi
    exact (hindicator i).const_mul (coeff i)
  have hsum :
      Integrable
        (fun s : NNReal ↦
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i *
              Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s) ν := by
    exact integrable_finset_sum (Finset.range (N - 1)) htermInt
  have htermEval :
      ∀ i ∈ Finset.range (N - 1),
        ∫ s, coeff i *
            Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s ∂ν =
          coeff i * V (P m (i + 1)) := by
    intro i hi
    have hi_lt : i < N - 1 := Finset.mem_range.mp hi
    have hi_succ_lt : i + 1 < (N - 1) + 1 := Nat.succ_lt_succ hi_lt
    have hN : 0 < N := by
      exact lt_of_lt_of_le (Nat.zero_lt_succ i)
        (le_trans (Nat.succ_le_of_lt hi_lt) (Nat.sub_le _ _))
    have hN_eq : (N - 1) + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hN)
    have hi' : i + 1 < N := by
      simpa [hN_eq] using hi_succ_lt
    have hiT : P m (i + 1) ≤ T := by
      exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P m (i + 1) T hi')
    calc
      ∫ s, coeff i *
          Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s ∂ν
          = coeff i *
              ∫ s, Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s ∂ν := by
              rw [integral_const_mul]
      _ = coeff i * V (P m (i + 1)) := by
            simpa [ν] using
              congrArg (fun r : ℝ ↦ coeff i * r)
                (setIntegral_indicator_Icc_eq_squareVariation μ hμV hiT)
  -- Proof comment: expand the staircase into its constant part plus finitely many prefix
  -- indicators, integrate termwise, and then rewrite each term through the bracket realization.
  calc
    ∫ s in Set.Icc 0 T, coarseIccStep f P m T s ∂μ
        = ∫ s, coarseIccStep f P m T s ∂ν := by
            rfl
    _ =
        ∫ s, (fun _ : NNReal ↦ cLast) s ∂ν +
          ∫ s,
            Finset.sum (Finset.range (N - 1)) fun i ↦
              coeff i *
                Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s ∂ν := by
          change
            ∫ s,
              ((fun _ : NNReal ↦ cLast) s +
                Finset.sum (Finset.range (N - 1)) fun i ↦
                  coeff i *
                    Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s) ∂ν =
              _ + _
          rw [integral_add hconst hsum]
    _ =
        cLast * V T +
          ∫ s,
            Finset.sum (Finset.range (N - 1)) fun i ↦
              coeff i *
                Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s ∂ν := by
          simpa [ν] using congrArg
            (fun r : ℝ ↦ r +
              ∫ s,
                Finset.sum (Finset.range (N - 1)) fun i ↦
                  coeff i *
                    Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s ∂ν)
            (setIntegral_const_eq_mul_squareVariation μ hμV T cLast)
    _ =
        cLast * V T +
          Finset.sum (Finset.range (N - 1)) fun i ↦
            ∫ s, coeff i *
                Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ : NNReal ↦ (1 : ℝ)) s ∂ν := by
          rw [integral_finset_sum _ htermInt]
    _ =
        cLast * V T +
          Finset.sum (Finset.range (N - 1)) fun i ↦ coeff i * V (P m (i + 1)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact htermEval i hi
    _ =
        f (P m (partitionBoundIndex P m T - 1)) * squareVariationBracket X P hX T +
          Finset.sum (Finset.range (partitionBoundIndex P m T - 1)) fun i ↦
            (f (P m i) - f (P m (i + 1))) *
              squareVariationBracket X P hX (P m (i + 1)) := by
          simp [V, N, cLast, coeff]

/-- Helper for Exercise 21.10.2: if `X` has continuous square variation along the admissible
partition sequence `P`, then for every continuous `f : [0, ∞) → ℝ` the weighted quadratic
partition sums of `X` converge on `[0, T]` to the Lebesgue--Stieltjes integral of `f` against the
chosen bracket measure `squareVariationBracketMeasure X P hX`. -/
theorem tendsto_weightedPartitionQuadraticVariationApproximationUpTo
    (f : NNReal → ℝ) (hf : Continuous f) (X : PathSpace)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : HasContinuousSquareVariationAlongPartition X P) :
    ∀ T : NNReal,
      Tendsto
        (fun n : ℕ ↦ weightedPartitionQuadraticVariationApproximationUpTo f X P T n)
        atTop
        (nhds
          (∫ s in Set.Icc 0 T, f s ∂(squareVariationBracketMeasure X P hX)))
      := by
  intro T
  let V := squareVariationBracket X P hX
  let μ := squareVariationBracketMeasure X P hX
  let If : ℝ := ∫ s in Set.Icc 0 T, f s ∂μ
  have hVspec : HasSquareVariationAlongPartition X P V := by
    simpa [V] using squareVariationBracket_spec X P hX
  have hzeroMono :
      V 0 = 0 ∧ Monotone V := by
    simpa [V] using squareVariationBracket_zero_and_monotone X P hX
  have hμV :
      ∀ S : NNReal, V S = ∫ _ in Set.Icc 0 S, (1 : ℝ) ∂μ := by
    simpa [V, μ] using squareVariationBracketMeasure_realizes_path X P hX
  have hμIcc_lt_top : μ (Set.Icc 0 T) ≠ ⊤ := by
    simpa [μ] using squareVariationBracketMeasure_Icc_lt_top X P hX T
  have hmass :
      μ.real (Set.Icc 0 T) = V T :=
    squareVariationMeasure_real_Icc_eq μ hμV T
  have hVT_nonneg : 0 ≤ V T := by
    rw [← hzeroMono.1]
    exact hzeroMono.2 bot_le
  let M : ℝ := V T + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    linarith
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let η : ℝ := ε / (3 * M)
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  rcases exists_coarseIccStep_uniformApprox f hf P T hη_pos with ⟨m, hm⟩
  let Ig : ℝ := ∫ s in Set.Icc 0 T, coarseIccStep f P m T s ∂μ
  have hcoarseTendsto :
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (coarseIccStep f P m T) X P T n)
        atTop
        (nhds Ig) := by
    have hlin :=
      tendsto_weightedPartitionQuadraticVariationApproximationUpTo_coarseIccStep_linearCombination
        f X P hVspec m T
    have hIg :
        Ig =
          f (P m (partitionBoundIndex P m T - 1)) * V T +
            Finset.sum (Finset.range (partitionBoundIndex P m T - 1)) fun i ↦
              (f (P m i) - f (P m (i + 1))) * V (P m (i + 1)) := by
      simpa [Ig, V, μ] using setIntegral_coarseIccStep_eq_linearCombination f X P hX m T
    simpa [Ig, V, hIg] using hlin
  have heventMass :
      ∀ᶠ n in atTop,
        weightedPartitionQuadraticVariationApproximationUpTo (fun _ ↦ (1 : ℝ)) X P T n ≤ M := by
    filter_upwards
      [eventually_le_weightedPartitionQuadraticVariationApproximationUpTo_one_abs_add_one
        X P hVspec T] with n hn
    simpa [M, abs_of_nonneg hVT_nonneg] using hn
  have hcoarseInt :
      IntegrableOn (coarseIccStep f P m T) (Set.Icc 0 T) μ := by
    simpa [μ] using
      integrableOn_coarseIccStep_squareVariationBracketMeasure f X P hX m T
  have hfInt :
      IntegrableOn f (Set.Icc 0 T) μ := by
    have honeInt : IntegrableOn (fun _ : NNReal ↦ (1 : ℝ)) (Set.Icc 0 T) μ := by
      refine μ.integrableOn_of_bounded (s := Set.Icc 0 T) (f := fun _ : NNReal ↦ (1 : ℝ))
        hμIcc_lt_top aestronglyMeasurable_const (M := 1) ?_
      exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ by simp
    simpa using
      honeInt.continuousOn_mul_of_subset hf.continuousOn isCompact_Icc measurableSet_Icc
        subset_rfl
  have hIgIf_sub :
      ∫ s in Set.Icc 0 T, (coarseIccStep f P m T s - f s) ∂μ = Ig - If := by
    simpa [Ig, If] using integral_sub hcoarseInt hfInt
  have hIgIf_le :
      |Ig - If| ≤ η * V T := by
    have hpointwise :
        ∀ s ∈ Set.Icc 0 T, ‖coarseIccStep f P m T s - f s‖ ≤ η := by
      intro s hs
      simpa [Real.norm_eq_abs, abs_sub_comm] using hm s hs
    have hnorm :
        ‖∫ s in Set.Icc 0 T, (coarseIccStep f P m T s - f s) ∂μ‖ ≤
          η * μ.real (Set.Icc 0 T) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const hμIcc_lt_top.lt_top hpointwise
    simpa [Real.norm_eq_abs, hIgIf_sub, hmass] using hnorm
  have hη_mul_M : η * M = ε / 3 := by
    calc
      η * M = (ε / (3 * M)) * M := by rfl
      _ = ε / 3 := by
            field_simp [hM_pos.ne']
  have hIgIf_small : |Ig - If| ≤ ε / 3 := by
    have hVT_le_M : V T ≤ M := by
      dsimp [M]
      linarith
    calc
      |Ig - If| ≤ η * V T := hIgIf_le
      _ ≤ η * M := by
            gcongr
      _ = ε / 3 := hη_mul_M
  have hcoarseEvent :
      ∀ᶠ n in atTop,
        dist
            (weightedPartitionQuadraticVariationApproximationUpTo
              (coarseIccStep f P m T) X P T n)
            Ig < ε / 3 :=
    Filter.eventually_atTop.2 (Metric.tendsto_atTop.1 hcoarseTendsto (ε / 3) (by positivity))
  rcases Filter.eventually_atTop.1 heventMass with ⟨Nmass, hNmass⟩
  rcases Filter.eventually_atTop.1 hcoarseEvent with ⟨Ncoarse, hNcoarse⟩
  refine ⟨max Nmass Ncoarse, ?_⟩
  intro n hn
  have hnMass := hNmass n (le_trans (le_max_left _ _) hn)
  have hnCoarse := hNcoarse n (le_trans (le_max_right _ _) hn)
  have hsumDiff :
      |weightedPartitionQuadraticVariationApproximationUpTo f X P T n -
          weightedPartitionQuadraticVariationApproximationUpTo
            (coarseIccStep f P m T) X P T n| ≤
        ε / 3 := by
    have hbase :=
      abs_sub_weightedPartitionQuadraticVariationApproximationUpTo_le
        f (coarseIccStep f P m T) X P T η hm n
    calc
      |weightedPartitionQuadraticVariationApproximationUpTo f X P T n -
          weightedPartitionQuadraticVariationApproximationUpTo
            (coarseIccStep f P m T) X P T n|
          ≤ η *
              weightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ)) X P T n := hbase
      _ ≤ η * M := by
            exact mul_le_mul_of_nonneg_left hnMass hη_nonneg
      _ = ε / 3 := hη_mul_M
  have hcoarseAbs :
      |weightedPartitionQuadraticVariationApproximationUpTo
          (coarseIccStep f P m T) X P T n - Ig| < ε / 3 := by
    simpa [Real.dist_eq, abs_sub_comm] using hnCoarse
  have htriangle :
      |weightedPartitionQuadraticVariationApproximationUpTo f X P T n - If| <
        ε := by
    calc
      |weightedPartitionQuadraticVariationApproximationUpTo f X P T n - If|
          =
            |(weightedPartitionQuadraticVariationApproximationUpTo f X P T n -
                weightedPartitionQuadraticVariationApproximationUpTo
                  (coarseIccStep f P m T) X P T n) +
              ((weightedPartitionQuadraticVariationApproximationUpTo
                  (coarseIccStep f P m T) X P T n - Ig) + (Ig - If))| := by
                ring_nf
      _ ≤
          |weightedPartitionQuadraticVariationApproximationUpTo f X P T n -
              weightedPartitionQuadraticVariationApproximationUpTo
                (coarseIccStep f P m T) X P T n| +
            |(weightedPartitionQuadraticVariationApproximationUpTo
                (coarseIccStep f P m T) X P T n - Ig) + (Ig - If)| := by
              simpa [Real.norm_eq_abs, add_assoc] using
                norm_add_le
                  (weightedPartitionQuadraticVariationApproximationUpTo f X P T n -
                    weightedPartitionQuadraticVariationApproximationUpTo
                      (coarseIccStep f P m T) X P T n)
                  ((weightedPartitionQuadraticVariationApproximationUpTo
                      (coarseIccStep f P m T) X P T n - Ig) + (Ig - If))
      _ ≤
          |weightedPartitionQuadraticVariationApproximationUpTo f X P T n -
              weightedPartitionQuadraticVariationApproximationUpTo
                (coarseIccStep f P m T) X P T n| +
            (|weightedPartitionQuadraticVariationApproximationUpTo
                (coarseIccStep f P m T) X P T n - Ig| + |Ig - If|) := by
              gcongr
              simpa [Real.norm_eq_abs] using
                norm_add_le
                  (weightedPartitionQuadraticVariationApproximationUpTo
                    (coarseIccStep f P m T) X P T n - Ig)
                  (Ig - If)
      _ < ε := by
        linarith
  simpa [If, Real.dist_eq] using htriangle

/-- Exercise 21.10.2: let `f : [0, ∞) → ℝ` be continuous and let `X ∈ 𝒞_qv^P` for the admissible
sequence of partitions `P`. Then for every `T ≥ 0`, the weighted quadratic partition sums of `X`
over `P_T^n` converge to the Lebesgue--Stieltjes integral of `f` against the canonical bracket
measure `d⟨X⟩`, represented here by `continuousSquareVariationMeasureAlong X P hX`. -/
theorem tendsto_weightedPartitionQuadraticVariationApproximationUpTo_of_mem_𝒞_qvAlong
    (f : NNReal → ℝ) (hf : Continuous f) (X : PathSpace)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hX : X ∈ 𝒞_qvAlong P) :
    ∀ T : NNReal,
      Tendsto
        (fun n : ℕ ↦ weightedPartitionQuadraticVariationApproximationUpTo f X P T n)
        atTop
        (nhds
          (∫ s in Set.Icc 0 T, f s ∂(continuousSquareVariationMeasureAlong X P hX))) := by
  -- Proof comment: `X ∈ 𝒞_qvAlong P` is exactly the owner predicate needed by the generic
  -- convergence theorem, and the source-facing measure is the same canonical bracket measure.
  simpa [continuousSquareVariationMeasureAlong] using
    tendsto_weightedPartitionQuadraticVariationApproximationUpTo
      f hf X P ((mem_𝒞_qvAlong_iff X).1 hX)

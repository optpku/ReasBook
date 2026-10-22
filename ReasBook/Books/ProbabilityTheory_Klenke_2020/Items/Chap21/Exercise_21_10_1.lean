/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_56
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_29

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BigOperators
open OrderDual

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Helper for Exercise 21.10.1: the reverse-time process `Yₙ` from the proof of Theorem 21.64,
written as the finite sum of centered squared increments along the partition row up to time `1`.
-/
noncomputable abbrev exercise21101BackwardProcess
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ℕᵒᵈ → Ω → ℝ :=
  fun n ω ↦
    Finset.sum (Finset.range (partitionBoundIndex P (ofDual n) 1)) fun k ↦
      ((W (partitionNextPointUpTo P (ofDual n) k 1) ω - W (P (ofDual n) k) ω) ^ (2 : ℕ) -
        (((partitionNextPointUpTo P (ofDual n) k 1 - P (ofDual n) k : NNReal) : ℝ)))

/-- Helper for Exercise 21.10.1: the centered squared increment of `W` over the deterministic
interval `[s, t]`. -/
noncomputable abbrev exercise21101BlockContribution
    (W : NNReal → Ω → ℝ) (s t : NNReal) : Ω → ℝ :=
  fun ω ↦ (W t ω - W s ω) ^ (2 : ℕ) - (((t - s : NNReal) : ℝ))

/-- Helper for Exercise 21.10.1: a single centered block contribution is strongly measurable. -/
lemma exercise21101BlockContribution_stronglyMeasurable
    (W : NNReal → Ω → ℝ) (hW_meas : ∀ t, StronglyMeasurable (W t))
    (s t : NNReal) :
    StronglyMeasurable (exercise21101BlockContribution W s t) := by
  -- Proof comment: this is the same polynomial measurability calculation as for one summand in
  -- `Yₙ`, now packaged at the block level.
  change StronglyMeasurable
    (fun ω ↦ (W t ω - W s ω) ^ (2 : ℕ) - (((t - s : NNReal) : ℝ)))
  exact ((((hW_meas t).measurable.sub (hW_meas s).measurable).pow_const 2).sub
    measurable_const).stronglyMeasurable

/-- Helper for Exercise 21.10.1: the centered squared Brownian increment over `[s, t]` is
integrable whenever `s ≤ t`. -/
lemma exercise21101BlockContribution_integrable
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {s t : NNReal} (hst : s ≤ t) :
    Integrable (exercise21101BlockContribution W s t) μ := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  -- Proof comment: the Brownian increment is in `L²`, so its centered square is integrable.
  change Integrable (fun ω ↦ (W t ω - W s ω) ^ (2 : ℕ) - (((t - s : NNReal) : ℝ))) μ
  exact
    (brownianIncrement_memLp_two (μ := μ) (B := W) hW (s := s) (t := t) hst).integrable_sq.sub
      (integrable_const _)

/-- Helper for Exercise 21.10.1: a centered squared Brownian increment has expectation `0`. -/
lemma exercise21101BlockContribution_integral_eq_zero
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {s t : NNReal} (hst : s ≤ t) :
    ∫ ω, exercise21101BlockContribution W s t ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let inc : Ω → ℝ := fun ω ↦ W t ω - W s ω
  have hInc_mem : MemLp inc 2 μ := by
    -- Proof comment: the deterministic-time Brownian increment belongs to `L²`.
    simpa [inc] using brownianIncrement_memLp_two (μ := μ) (B := W) hW (s := s) (t := t) hst
  -- Proof comment: the compensator subtracts exactly the increment second moment.
  calc
    ∫ ω, exercise21101BlockContribution W s t ω ∂μ
        = ∫ ω, inc ω ^ (2 : ℕ) ∂μ - ∫ ω, (((t - s : NNReal) : ℝ)) ∂μ := by
            rw [show exercise21101BlockContribution W s t =
              fun ω ↦ inc ω ^ (2 : ℕ) - (((t - s : NNReal) : ℝ)) by
              funext ω
              simp [exercise21101BlockContribution, inc],
              integral_sub hInc_mem.integrable_sq (integrable_const _)]
    _ = (((t - s : NNReal) : ℝ)) - (((t - s : NNReal) : ℝ)) := by
          rw [brownianIncrement_sq_integral_eq_timeLag
            (μ := μ) (B := W) hW (s := s) (t := t) hst,
            integral_const, probReal_univ, one_smul]
    _ = 0 := by ring

/-- Helper for Exercise 21.10.1: splitting a centered square at an intermediate time produces the
two child centered squares plus the usual cross term. -/
lemma exercise21101BlockContribution_split
    (W : NNReal → Ω → ℝ) {s u t : NNReal} (hsu : s ≤ u) (hut : u ≤ t) :
    exercise21101BlockContribution W s t =
      fun ω ↦
        exercise21101BlockContribution W s u ω +
          exercise21101BlockContribution W u t ω +
            2 * (W u ω - W s ω) * (W t ω - W u ω) := by
  -- Proof comment: this is the textbook identity `(x + y)^2 = x^2 + y^2 + 2xy` together with
  -- additivity of the deterministic time lags.
  funext ω
  have hst : s ≤ t := hsu.trans hut
  rw [exercise21101BlockContribution, exercise21101BlockContribution,
    exercise21101BlockContribution, NNReal.coe_sub hst, NNReal.coe_sub hsu, NNReal.coe_sub hut]
  ring

/-- Helper for Exercise 21.10.1: the reverse-time process `Yₙ` is strongly measurable at each
reverse-time index. -/
lemma exercise21101BackwardProcess_stronglyMeasurable
    (W : NNReal → Ω → ℝ) (hW_meas : ∀ t, StronglyMeasurable (W t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕᵒᵈ) :
    StronglyMeasurable
      (exercise21101BackwardProcess W P n) := by
  -- Proof comment: each summand is a polynomial expression in two deterministic-time evaluations
  -- of `W`, and finite sums preserve strong measurability.
  change StronglyMeasurable
    (fun ω ↦
      Finset.sum (Finset.range (partitionBoundIndex P (ofDual n) 1)) fun k ↦
        ((W (partitionNextPointUpTo P (ofDual n) k 1) ω - W (P (ofDual n) k) ω) ^ (2 : ℕ) -
          (((partitionNextPointUpTo P (ofDual n) k 1 - P (ofDual n) k : NNReal) : ℝ))))
  refine (Finset.measurable_sum _ fun k hk => ?_).stronglyMeasurable
  exact
    ((((hW_meas (partitionNextPointUpTo P (ofDual n) k 1)).measurable.sub
      (hW_meas (P (ofDual n) k)).measurable).pow_const 2).sub measurable_const)

/-- Helper for Exercise 21.10.1: before the first partition index reaching `T`, the row point is
still strictly below `T`. -/
lemma exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k < T := by
  -- Proof comment: if `P n k` had already reached `T`, the minimality of `partitionBoundIndex`
  -- would force `partitionBoundIndex P n T ≤ k`, contradicting `hk`.
  refine lt_of_not_ge ?_
  intro hT
  have hbound : partitionBoundIndex P n T ≤ k := by
    exact Nat.find_min' (exists_partition_index_le_time P n T) hT
  exact (not_le_of_gt hk) hbound

/-- Helper for Exercise 21.10.1: every coarse partition endpoint reappears in every finer
partition row. -/
lemma exercise21101CoarseEndpointIndexInRefinement
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (m i n : ℕ) (hmn : m ≤ n) :
    ∃ j : ℕ, P n j = P m i := by
  -- Proof comment: move the coarse endpoint through the nested partition-point sets one row at a
  -- time until reaching the target refinement row.
  induction hmn with
  | refl =>
      exact ⟨i, rfl⟩
  | @step n hmn ih =>
      rcases ih with ⟨j, hj⟩
      have hmem : P m i ∈ partitionPointSet P (n + 1) := by
        exact hP.nested n ⟨j, hj⟩
      rcases hmem with ⟨j', hj'⟩
      exact ⟨j', hj'⟩

/-- Helper for Exercise 21.10.1: choose the occurrence of a coarse endpoint inside a finer
partition row. -/
noncomputable def exercise21101CoarseEndpointRefinementIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m i n : ℕ) : ℕ :=
  if hmn : m ≤ n then Classical.choose (exercise21101CoarseEndpointIndexInRefinement P m i n hmn)
  else 0

/-- Helper for Exercise 21.10.1: the chosen refinement index evaluates to the original coarse
endpoint. -/
lemma exercise21101CoarseEndpointRefinementIndex_spec
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m i n : ℕ) (hmn : m ≤ n) :
    P n (exercise21101CoarseEndpointRefinementIndex P m i n) = P m i := by
  -- Proof comment: unfold the noncomputable choice and read off its witness equation.
  rw [exercise21101CoarseEndpointRefinementIndex, dif_pos hmn]
  exact Classical.choose_spec (exercise21101CoarseEndpointIndexInRefinement P m i n hmn)

/-- Helper for Exercise 21.10.1: copying a coarse endpoint through two refinement levels agrees
with copying it directly to the final row. -/
lemma exercise21101CoarseEndpointRefinementIndex_trans
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {m n M i : ℕ} (hmn : m ≤ n) (hnM : n ≤ M) :
    exercise21101CoarseEndpointRefinementIndex P n
        (exercise21101CoarseEndpointRefinementIndex P m i n) M
      =
        exercise21101CoarseEndpointRefinementIndex P m i M := by
  -- Proof comment: both candidate indices on row `M` represent the same original row-`m`
  -- partition point, so strict monotonicity on row `M` identifies them.
  apply (hP.strictMono M).injective
  rw [exercise21101CoarseEndpointRefinementIndex_spec P n
      (exercise21101CoarseEndpointRefinementIndex P m i n) M hnM,
    exercise21101CoarseEndpointRefinementIndex_spec P m i n hmn,
    exercise21101CoarseEndpointRefinementIndex_spec P m i M (hmn.trans hnM)]

/-- Helper for Exercise 21.10.1: any partition point strictly before the horizon occurs strictly
before the truncation index. -/
lemma exercise21101_lt_partitionBoundIndex_of_partitionPoint_lt_time
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n j : ℕ) (T : NNReal) (hjT : P n j < T) :
    j < partitionBoundIndex P n T := by
  -- Proof comment: if `j` were at or beyond the truncation index, monotonicity would force
  -- `P n j ≥ T`, contradicting the strict inequality.
  by_contra hj
  have hbound : partitionBoundIndex P n T ≤ j := Nat.not_lt.mp hj
  have hmono : P n (partitionBoundIndex P n T) ≤ P n j :=
    (hP.strictMono n).monotone hbound
  exact not_le_of_gt hjT (le_trans (le_partitionBoundIndex_time P n T) hmono)

/-- Helper for Exercise 21.10.1: if the horizon is itself a partition point, then the truncation
index is exactly its row index. -/
lemma exercise21101_partitionBoundIndex_eq_of_partitionPoint
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n k : ℕ) :
    partitionBoundIndex P n (P n k) = k := by
  -- Proof comment: `k` reaches the horizon `P n k`, and every smaller index still lies strictly
  -- before that horizon by strict monotonicity.
  apply Nat.le_antisymm
  · simpa [partitionBoundIndex] using
      (Nat.find_min' (exists_partition_index_le_time P n (P n k))
        (show P n k ≤ P n k from le_rfl))
  · exact Nat.le_of_not_gt fun hklt ↦
      (not_lt_of_ge (le_partitionBoundIndex_time P n (P n k)))
        ((hP.strictMono n) hklt)

/-- Helper for Exercise 21.10.1: truncation indices are monotone in the time horizon. -/
lemma exercise21101PartitionBoundIndex_mono
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) {S T : NNReal} (hST : S ≤ T) :
    partitionBoundIndex P n S ≤ partitionBoundIndex P n T := by
  -- Proof comment: once the later boundary index reaches `T`, it also reaches every earlier
  -- horizon `S ≤ T`, so minimality of `partitionBoundIndex` gives the comparison.
  exact Nat.find_min' (exists_partition_index_le_time P n S)
    (le_trans hST (le_partitionBoundIndex_time P n T))

/-- Helper for Exercise 21.10.1: every partition row has at least one active block before the
horizon `1`. -/
lemma exercise21101_zero_lt_partitionBoundIndex_one
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) :
    0 < partitionBoundIndex P n 1 := by
  -- Proof comment: the initial partition point is `0`, so it lies strictly before the horizon
  -- `1` and therefore forces the truncation index to be positive.
  have hzero_lt_one : P n 0 < (1 : NNReal) := by
    simpa [hP.zero_eq n]
  simpa using
    exercise21101_lt_partitionBoundIndex_of_partitionPoint_lt_time P n 0 1 hzero_lt_one

/-- Helper for Exercise 21.10.1: a coarse endpoint that lies before horizon `T` is indexed before
the finer-row truncation index as well. -/
lemma exercise21101CoarseEndpointRefinementIndex_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (m i n : ℕ) (hmn : m ≤ n) (T : NNReal) (hiT : P m i < T) :
    exercise21101CoarseEndpointRefinementIndex P m i n < partitionBoundIndex P n T := by
  -- Proof comment: transport the strict inequality `P m i < T` to the chosen finer-row index and
  -- then apply the generic truncation-index criterion.
  have hspec : P n (exercise21101CoarseEndpointRefinementIndex P m i n) = P m i :=
    exercise21101CoarseEndpointRefinementIndex_spec P m i n hmn
  have hidxT : P n (exercise21101CoarseEndpointRefinementIndex P m i n) < T := by
    simpa [hspec] using hiT
  exact exercise21101_lt_partitionBoundIndex_of_partitionPoint_lt_time P n
    (exercise21101CoarseEndpointRefinementIndex P m i n) T hidxT

/-- Helper for Exercise 21.10.1: the copied refinement index of the initial partition point is
`0`. -/
lemma exercise21101CoarseEndpointRefinementIndex_zero
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) :
    exercise21101CoarseEndpointRefinementIndex P n 0 (n + 1) = 0 := by
  -- Proof comment: the copied coarse point is `0`, and strict monotonicity makes that occurrence
  -- unique in the finer row.
  have hspec :
      P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n 0 (n + 1)) = P n 0 :=
    exercise21101CoarseEndpointRefinementIndex_spec P n 0 (n + 1) (Nat.le_succ n)
  have hzero :
      P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n 0 (n + 1)) = P (n + 1) 0 := by
    simpa [hP.zero_eq n, hP.zero_eq (n + 1)] using hspec
  exact (hP.strictMono (n + 1)).injective hzero

/-- Helper for Exercise 21.10.1: before the boundary index at horizon `T`, the clipped right
endpoint is just the next partition point. -/
lemma exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i : ℕ) (T : NNReal) (hi : i + 1 < partitionBoundIndex P n T) :
    partitionNextPointUpTo P n i T = P n (i + 1) := by
  -- Proof comment: as long as the next partition endpoint still lies before the clipping horizon
  -- `T`, the truncation does nothing.
  rw [partitionNextPointUpTo, min_eq_left]
  exact le_of_lt <|
    exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P n (i + 1) T hi

/-- Helper for Exercise 21.10.1: a clipped right endpoint is either the next partition point on
the same row or the clipping horizon itself. -/
lemma exercise21101PartitionNextPointUpTo_eq_partitionPoint_or_self
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i : ℕ) (T : NNReal) :
    (∃ k, partitionNextPointUpTo P n i T = P n k ∧
        partitionBoundIndex P n (partitionNextPointUpTo P n i T) = k) ∨
      partitionNextPointUpTo P n i T = T := by
  -- Proof comment: before the clipping horizon we see the genuine next partition point; once the
  -- next point is already at or beyond the boundary, clipping returns the boundary itself.
  by_cases hi : i + 1 < partitionBoundIndex P n T
  · left
    refine ⟨i + 1, ?_, ?_⟩
    · exact
        exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
          P n i T hi
    · rw [exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
        P n i T hi, exercise21101_partitionBoundIndex_eq_of_partitionPoint]
  · right
    rw [partitionNextPointUpTo, min_eq_right]
    exact le_trans (le_partitionBoundIndex_time P n T)
      ((hP.strictMono n).monotone (Nat.le_of_not_gt hi))

/-- Helper for Exercise 21.10.1: for a nonterminal active coarse block, the finer boundary index
is exactly the copied refinement index of the next coarse endpoint. -/
lemma exercise21101NextPointBound_eq_coarseEndpointRefinementIndex_succ
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i : ℕ) (hi : i + 1 < partitionBoundIndex P n 1) :
    partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) =
      exercise21101CoarseEndpointRefinementIndex P n (i + 1) (n + 1) := by
  -- Proof comment: in the nonterminal case the clipped right endpoint is the next coarse point,
  -- and its copied finer-row index is recovered by the partition-bound characterization.
  have hnext :
      partitionNextPointUpTo P n i 1 = P n (i + 1) :=
    exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex P n i 1 hi
  have hspec :
      P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n (i + 1) (n + 1)) = P n (i + 1) :=
    exercise21101CoarseEndpointRefinementIndex_spec P n (i + 1) (n + 1) (Nat.le_succ n)
  rw [hnext, ← hspec, exercise21101_partitionBoundIndex_eq_of_partitionPoint]

/-- Helper for Exercise 21.10.1: the formal coarse-to-fine block decomposition attached to the
active row-`n` block indexed by `i`. This is the owner shape needed later for the martingale step:
it records the finer centered block contributions and the remaining cross terms on row `n + 1`. -/
noncomputable abbrev exercise21101RefinedBlockContribution
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i : ℕ) : Ω → ℝ :=
  fun ω ↦
    Finset.sum
        (Finset.range
          (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
            exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
        (fun r ↦
          exercise21101BlockContribution W
            (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r))
            (partitionNextPointUpTo P (n + 1)
              (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
              (partitionNextPointUpTo P n i 1)) ω) +
      Finset.sum
        (Finset.range
          (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
            exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
        (fun r ↦
          2 *
              (W (P (n + 1)
                (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)) ω -
                W (P n i) ω) *
            (W (partitionNextPointUpTo P (n + 1)
                (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
                (partitionNextPointUpTo P n i 1)) ω -
              W (P (n + 1)
                (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)) ω))

/-- Helper for Exercise 21.10.1: the mixed cross remainder produced when the active coarse
row-`n` block `i` is refined into row `n + 1`. This is the only non-filtration-measurable part
left after rewriting `Yₙ` through the finer row. -/
noncomputable abbrev exercise21101RefinedBlockCrossTerm
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i : ℕ) : Ω → ℝ :=
  fun ω ↦
    Finset.sum
      (Finset.range
        (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
      (fun r ↦
        2 *
            (W (P (n + 1)
              (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)) ω -
              W (P n i) ω) *
          (W (partitionNextPointUpTo P (n + 1)
              (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
              (partitionNextPointUpTo P n i 1)) ω -
            W (P (n + 1)
              (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)) ω))

/-- Helper for Exercise 21.10.1: one refined block contribution splits into its row-`n + 1`
descendant centered blocks plus the mixed cross remainder. -/
lemma exercise21101RefinedBlockContribution_eq_blockSum_add_crossTerm
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i : ℕ) :
    exercise21101RefinedBlockContribution W P n i =
      fun ω ↦
        Finset.sum
          (Finset.range
            (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
              exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
          (fun r ↦
            exercise21101BlockContribution W
              (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r))
              (partitionNextPointUpTo P (n + 1)
                (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
                (partitionNextPointUpTo P n i 1)) ω) +
          exercise21101RefinedBlockCrossTerm W P n i ω := by
  -- Proof comment: this is just the stored definition of the coarse-to-fine refinement, with the
  -- mixed descendants packaged into the dedicated cross-term helper.
  funext ω
  simp [exercise21101RefinedBlockContribution, exercise21101RefinedBlockCrossTerm]

/-- Helper for Exercise 21.10.1: the refined cross remainder of one coarse block is strongly
measurable. -/
lemma exercise21101RefinedBlockCrossTerm_stronglyMeasurable
    (W : NNReal → Ω → ℝ) (hW_meas : ∀ t, StronglyMeasurable (W t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i : ℕ) :
    StronglyMeasurable (exercise21101RefinedBlockCrossTerm W P n i) := by
  -- Proof comment: every summand is a product of two deterministic-time Brownian increments, so
  -- finite summation preserves strong measurability.
  refine (Finset.measurable_sum _ fun r hr => ?_).stronglyMeasurable
  have hleft :
      Measurable
        (fun ω ↦
          W (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)) ω -
            W (P n i) ω) := by
    have hmid_sm :
        StronglyMeasurable
          (W (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r))) :=
      hW_meas (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r))
    have hbase_sm : StronglyMeasurable (W (P n i)) := hW_meas (P n i)
    exact hmid_sm.measurable.sub hbase_sm.measurable
  have hright :
      Measurable
        (fun ω ↦
          W (partitionNextPointUpTo P (n + 1)
              (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
              (partitionNextPointUpTo P n i 1)) ω -
            W (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)) ω) := by
    have hright_sm :
        StronglyMeasurable
          (W
            (partitionNextPointUpTo P (n + 1)
              (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
              (partitionNextPointUpTo P n i 1))) :=
      hW_meas
        (partitionNextPointUpTo P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
          (partitionNextPointUpTo P n i 1))
    have hmid_sm :
        StronglyMeasurable
          (W (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r))) :=
      hW_meas (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r))
    exact hright_sm.measurable.sub hmid_sm.measurable
  simpa [mul_assoc] using (hleft.mul hright).const_mul (2 : ℝ)

/-- Helper for Exercise 21.10.1: each refined cross remainder is integrable. This isolates the
`L¹` side condition needed later for conditional expectations on the future filtration. -/
lemma exercise21101RefinedBlockCrossTerm_integrable
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i : ℕ) :
    Integrable (exercise21101RefinedBlockCrossTerm W P n i) μ := by
  let j := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let bound := partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1)
  let count := bound - j
  let coarseRight := partitionNextPointUpTo P n i 1
  refine integrable_finset_sum _ ?_
  intro r hr
  have hr_lt : r < count := Finset.mem_range.mp hr
  have hj_le_bound : j ≤ bound := by
    by_contra hj_bound
    have hcount_zero : count = 0 := by
      exact Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hj_bound)
    exact Nat.not_lt_zero r (by simpa [count, hcount_zero] using hr_lt)
  have hj_count : j + count = bound := by
    -- Proof comment: `count` records exactly the length of the finer descendant range.
    exact Nat.add_sub_of_le hj_le_bound
  have hmid_lt_bound : j + r < bound := by
    calc
      j + r < j + count := Nat.add_lt_add_left hr_lt j
      _ = bound := hj_count
  have hleft_le_mid :
      P n i ≤ P (n + 1) (j + r) := by
    -- Proof comment: every descendant left endpoint lies to the right of the copied coarse left
    -- endpoint.
    rw [← exercise21101CoarseEndpointRefinementIndex_spec P n i (n + 1) (Nat.le_succ n)]
    exact (hP.strictMono (n + 1)).monotone (Nat.le_add_right j r)
  have hmid_le_right :
      P (n + 1) (j + r) ≤ partitionNextPointUpTo P (n + 1) (j + r) coarseRight := by
    -- Proof comment: before the boundary index, the clipped successor stays to the right of the
    -- current descendant left endpoint.
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt ((hP.strictMono (n + 1)) (Nat.lt_succ_self (j + r)))
    · exact le_of_lt <|
        exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex
          P (n + 1) (j + r) coarseRight hmid_lt_bound
  have hleft_mem :
      MemLp (fun ω ↦ W (P (n + 1) (j + r)) ω - W (P n i) ω) 2 μ := by
    -- Proof comment: the accumulated descendant increment from the coarse left endpoint to the
    -- descendant start lies in `L²`.
    simpa [j] using
      brownianIncrement_memLp_two
        (μ := μ) (B := W) hW (s := P n i) (t := P (n + 1) (j + r)) hleft_le_mid
  have hright_mem :
      MemLp
        (fun ω ↦
          W (partitionNextPointUpTo P (n + 1) (j + r) coarseRight) ω -
            W (P (n + 1) (j + r)) ω)
        2 μ := by
    -- Proof comment: each child increment inside the refined block is also square-integrable.
    simpa [j, coarseRight] using
      brownianIncrement_memLp_two
        (μ := μ) (B := W) hW
        (s := P (n + 1) (j + r))
        (t := partitionNextPointUpTo P (n + 1) (j + r) coarseRight) hmid_le_right
  have hprod_int :
      Integrable
        (fun ω ↦
          (W (P (n + 1) (j + r)) ω - W (P n i) ω) *
            (W (partitionNextPointUpTo P (n + 1) (j + r) coarseRight) ω -
              W (P (n + 1) (j + r)) ω)) μ := by
    -- Proof comment: Hölder turns the two `L²` increment bounds into an `L¹` bound for their
    -- product.
    exact hleft_mem.integrable_mul hright_mem
  simpa [exercise21101RefinedBlockCrossTerm, j, count, coarseRight, mul_assoc] using
    hprod_int.const_mul (2 : ℝ)

/-- Helper for Exercise 21.10.1: the refined copy of the coarse left endpoint lies strictly before
the finer boundary index of the same active coarse block. -/
lemma exercise21101CoarseEndpointRefinementIndex_lt_nextPointBound
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i : ℕ) (hi : i < partitionBoundIndex P n 1) :
    exercise21101CoarseEndpointRefinementIndex P n i (n + 1) <
      partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) := by
  have hab : P n i < partitionNextPointUpTo P n i 1 := by
    -- Proof comment: an active row-`n` block starts strictly before its clipped right endpoint.
    rw [partitionNextPointUpTo]
    refine lt_min ?_ ?_
    · simpa using (hP.strictMono n) (Nat.lt_succ_self i)
    · simpa using exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P n i 1 hi
  exact
    exercise21101CoarseEndpointRefinementIndex_lt_partitionBoundIndex
      P n i (n + 1) (Nat.le_succ n) (partitionNextPointUpTo P n i 1) hab

/-- Helper for Exercise 21.10.1: the row-`n + 1` range attached to an active row-`n` block is
nonempty. This is the arithmetic side condition behind the future refinement decomposition. -/
lemma exercise21101RefinedBlockContribution_range_pos
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i : ℕ) (hi : i < partitionBoundIndex P n 1) :
    0 <
      partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
        exercise21101CoarseEndpointRefinementIndex P n i (n + 1) := by
  -- Proof comment: the refined copy of the coarse left endpoint sits strictly before the finer
  -- boundary index, so the attached row-`n + 1` block range has positive length.
  exact Nat.sub_pos_of_lt <|
    exercise21101CoarseEndpointRefinementIndex_lt_nextPointBound P n i hi

/-- Helper for Exercise 21.10.1: refining one active row-`n` block through all of its row-`n+1`
children reproduces the same centered coarse block contribution. -/
lemma exercise21101BlockContribution_refine
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i : ℕ) (hi : i < partitionBoundIndex P n 1) :
    exercise21101BlockContribution W (P n i) (partitionNextPointUpTo P n i 1) =
      exercise21101RefinedBlockContribution W P n i := by
  let j := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let bound := partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1)
  let count := bound - j
  let coarseRight := partitionNextPointUpTo P n i 1
  let term : ℕ → Ω → ℝ := fun r ω ↦
    exercise21101BlockContribution W
      (P (n + 1) (j + r))
      (partitionNextPointUpTo P (n + 1) (j + r) coarseRight) ω +
      2 * (W (P (n + 1) (j + r)) ω - W (P n i) ω) *
        (W (partitionNextPointUpTo P (n + 1) (j + r) coarseRight) ω -
          W (P (n + 1) (j + r)) ω)
  have hj_spec : P (n + 1) j = P n i := by
    -- Proof comment: the chosen refinement index is exactly the copied coarse left endpoint.
    simpa [j] using
      exercise21101CoarseEndpointRefinementIndex_spec P n i (n + 1) (Nat.le_succ n)
  have hj_lt : j < bound := by
    -- Proof comment: the copied coarse left endpoint lies before the clipped coarse right
    -- endpoint in the finer row.
    simpa [j, bound, coarseRight] using
      exercise21101CoarseEndpointRefinementIndex_lt_nextPointBound P n i hi
  have hcount_pos : 0 < count := by
    -- Proof comment: the active coarse block has at least one finer descendant block.
    simpa [count, j, bound, coarseRight] using
      exercise21101RefinedBlockContribution_range_pos P n i hi
  have hj_count : j + count = bound := by
    -- Proof comment: `count` was defined as the full finer range starting at `j`.
    exact Nat.add_sub_of_le (Nat.le_of_lt hj_lt)
  have hprefix :
      ∀ r : ℕ, r < count →
        (fun ω ↦ Finset.sum (Finset.range r) (fun s ↦ term s ω)) =
          exercise21101BlockContribution W (P n i) (P (n + 1) (j + r)) := by
    intro r hr
    induction r with
    | zero =>
        -- Proof comment: before adding any finer child, both sides are the zero contribution over
        -- the degenerate interval `[P n i, P n i]`.
        funext ω
        simp [exercise21101BlockContribution, hj_spec]
    | succ r ihr =>
        have hr_lt : r < count := Nat.lt_of_succ_lt hr
        have hsum :
            (fun ω ↦ Finset.sum (Finset.range (r + 1)) (fun s ↦ term s ω)) =
              (fun ω ↦ Finset.sum (Finset.range r) (fun s ↦ term s ω) + term r ω) := by
          funext ω
          rw [Finset.sum_range_succ]
        have hnext_lt : j + (r + 1) < bound := by
          calc
            j + (r + 1) < j + count := Nat.add_lt_add_left hr j
            _ = bound := hj_count
        have hsplit_right :
            partitionNextPointUpTo P (n + 1) (j + r) coarseRight = P (n + 1) (j + (r + 1)) := by
          -- Proof comment: before the final descendant, the clipped successor is the genuine next
          -- row-`n + 1` partition point.
          have hpoint_lt :
              P (n + 1) ((j + r) + 1) < coarseRight := by
            simpa [Nat.add_assoc] using
              exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex
                P (n + 1) (j + (r + 1)) coarseRight hnext_lt
          calc
            partitionNextPointUpTo P (n + 1) (j + r) coarseRight
                = P (n + 1) ((j + r) + 1) := by
                    rw [partitionNextPointUpTo, min_eq_left]
                    exact le_of_lt hpoint_lt
            _ = P (n + 1) (j + (r + 1)) := by
                  simp [Nat.add_assoc]
        have hcoarse_le :
            P n i ≤ P (n + 1) (j + r) := by
          -- Proof comment: every descendant start lies to the right of the copied coarse left
          -- endpoint.
          rw [← hj_spec]
          exact (hP.strictMono (n + 1)).monotone (Nat.le_add_right j r)
        have hchild_le :
            P (n + 1) (j + r) ≤ P (n + 1) (j + (r + 1)) := by
          exact le_of_lt <|
            (hP.strictMono (n + 1)) <| by
              simpa [Nat.add_assoc] using Nat.add_lt_add_left (Nat.lt_succ_self r) j
        calc
          (fun ω ↦ Finset.sum (Finset.range (r + 1)) (fun s ↦ term s ω))
              = (fun ω ↦ Finset.sum (Finset.range r) (fun s ↦ term s ω) + term r ω) := hsum
          _ = fun ω ↦
                exercise21101BlockContribution W (P n i) (P (n + 1) (j + r)) ω + term r ω := by
                  funext ω
                  have hω := congrFun (ihr hr_lt) ω
                  simpa [hω]
          _ = exercise21101BlockContribution W (P n i) (P (n + 1) (j + (r + 1))) := by
                -- Proof comment: one application of the centered-square split lemma advances the
                -- coarse contribution across the next finer child block.
                funext ω
                have hsplit :=
                  congrFun
                    (exercise21101BlockContribution_split
                      (W := W) (s := P n i) (u := P (n + 1) (j + r))
                      (t := P (n + 1) (j + (r + 1))) hcoarse_le hchild_le)
                    ω
                change
                  exercise21101BlockContribution W (P n i) (P (n + 1) (j + r)) ω +
                    (exercise21101BlockContribution W (P (n + 1) (j + r))
                        (partitionNextPointUpTo P (n + 1) (j + r) coarseRight) ω +
                      2 * (W (P (n + 1) (j + r)) ω - W (P n i) ω) *
                        (W (partitionNextPointUpTo P (n + 1) (j + r) coarseRight) ω -
                          W (P (n + 1) (j + r)) ω)) =
                    exercise21101BlockContribution W (P n i) (P (n + 1) (j + (r + 1))) ω
                rw [hsplit_right]
                simpa [add_assoc] using hsplit.symm
  have hpred_lt : Nat.pred count < count := Nat.pred_lt (Nat.ne_of_gt hcount_pos)
  have hpred_succ : Nat.pred count + 1 = count := Nat.succ_pred_eq_of_pos hcount_pos
  have hfinal_right :
      partitionNextPointUpTo P (n + 1) (j + Nat.pred count) coarseRight = coarseRight := by
    -- Proof comment: at the last descendant, the clipped successor is the coarse clipped right
    -- endpoint itself.
    have hreach_index : j + Nat.pred count + 1 = bound := by
      calc
        j + Nat.pred count + 1 = j + (Nat.pred count + 1) := by simp [Nat.add_assoc]
        _ = j + count := by rw [hpred_succ]
        _ = bound := hj_count
    rw [partitionNextPointUpTo, min_eq_right]
    have hreach : coarseRight ≤ P (n + 1) (j + Nat.pred count + 1) := by
      rw [hreach_index]
      exact le_partitionBoundIndex_time P (n + 1) coarseRight
    simpa [Nat.add_assoc] using hreach
  have hlast_lt : j + Nat.pred count < bound := by
    calc
      j + Nat.pred count < j + count := Nat.add_lt_add_left hpred_lt j
      _ = bound := hj_count
  have hcoarse_last :
      P n i ≤ P (n + 1) (j + Nat.pred count) := by
    -- Proof comment: the last descendant start is still to the right of the copied coarse left
    -- endpoint.
    rw [← hj_spec]
    exact (hP.strictMono (n + 1)).monotone (Nat.le_add_right j (Nat.pred count))
  have hlast_le_right :
      P (n + 1) (j + Nat.pred count) ≤ coarseRight := by
    -- Proof comment: the last descendant start still lies strictly before the clipped coarse
    -- right endpoint.
    exact le_of_lt <|
      exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex
        P (n + 1) (j + Nat.pred count) coarseRight hlast_lt
  calc
    exercise21101BlockContribution W (P n i) coarseRight
        = (fun ω ↦ Finset.sum (Finset.range count) (fun s ↦ term s ω)) := by
            -- Proof comment: append the final finer child to the inductive prefix decomposition.
            rw [← hpred_succ]
            calc
              exercise21101BlockContribution W (P n i) coarseRight
                  = fun ω ↦
                      exercise21101BlockContribution W (P n i)
                        (P (n + 1) (j + Nat.pred count)) ω +
                        term (Nat.pred count) ω := by
                          funext ω
                          have hsplit :=
                            congrFun
                              (exercise21101BlockContribution_split
                                (W := W) (s := P n i)
                                (u := P (n + 1) (j + Nat.pred count)) (t := coarseRight)
                                hcoarse_last hlast_le_right)
                              ω
                          change
                            exercise21101BlockContribution W (P n i) coarseRight ω =
                              exercise21101BlockContribution W (P n i)
                                  (P (n + 1) (j + Nat.pred count)) ω +
                                (exercise21101BlockContribution W
                                    (P (n + 1) (j + Nat.pred count))
                                    (partitionNextPointUpTo P (n + 1)
                                      (j + Nat.pred count) coarseRight) ω +
                                  2 * (W (P (n + 1) (j + Nat.pred count)) ω - W (P n i) ω) *
                                    (W (partitionNextPointUpTo P (n + 1)
                                      (j + Nat.pred count) coarseRight) ω -
                                      W (P (n + 1) (j + Nat.pred count)) ω))
                          rw [hfinal_right]
                          simpa [add_assoc] using hsplit
              _ = (fun ω ↦ Finset.sum (Finset.range (Nat.pred count))
                    (fun s ↦ term s ω) + term (Nat.pred count) ω) := by
                    rw [← hprefix (Nat.pred count) hpred_lt]
              _ = (fun ω ↦ Finset.sum (Finset.range (Nat.pred count + 1))
                    (fun s ↦ term s ω)) := by
                    funext ω
                    rw [Finset.sum_range_succ]
    _ = exercise21101RefinedBlockContribution W P n i := by
          -- Proof comment: this is exactly the stored coarse-to-fine decomposition.
          funext ω
          simp [exercise21101RefinedBlockContribution, term, j, bound, count, coarseRight,
            Finset.sum_add_distrib]

/-- Helper for Exercise 21.10.1: the stage `Yₙ` is the sum of the refined block decompositions of
its active row-`n` coarse blocks. -/
lemma exercise21101BackwardProcess_eq_sum_refinedBlockContribution
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) :
    exercise21101BackwardProcess W P (toDual n) =
      fun ω ↦
        Finset.sum (Finset.range (partitionBoundIndex P n 1))
          (fun i ↦ exercise21101RefinedBlockContribution W P n i ω) := by
  -- Proof comment: rewrite each active row-`n` centered coarse block by the one-block refinement
  -- identity proved just above.
  funext ω
  rw [exercise21101BackwardProcess]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hblock :=
    congrFun (exercise21101BlockContribution_refine (W := W) (P := P) (n := n) (i := i)
      (Finset.mem_range.mp hi)) ω
  simpa [exercise21101BlockContribution] using hblock

/-- Helper for Exercise 21.10.1: the descendant ranges of the active coarse row partition the full
active fine row up to time `1`, so arbitrary summands may be reorganized blockwise. -/
lemma exercise21101FineRow_sum_eq_sum_coarseDescendantRanges
    {α : Type*} [AddCommMonoid α]
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) (g : ℕ → α) :
    (Finset.sum (Finset.range (partitionBoundIndex P n 1)) fun i ↦
        Finset.sum
          (Finset.range
            (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
              exercise21101CoarseEndpointRefinementIndex P n i (n + 1))) fun r ↦
          g (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r))
      =
        Finset.sum (Finset.range (partitionBoundIndex P (n + 1) 1)) g := by
  let coarseBound := partitionBoundIndex P n 1
  let fineBound := partitionBoundIndex P (n + 1) 1
  let start : ℕ → ℕ := fun i ↦ exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let finish : ℕ → ℕ := fun i ↦ partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1)
  let inner : ℕ → α := fun i ↦
    Finset.sum (Finset.range (finish i - start i)) fun r ↦ g (start i + r)
  have hcoarse_pos : 0 < coarseBound := by
    -- Proof comment: every partition row starts at `0 < 1`, so the first truncation index is
    -- always strictly positive.
    have hzero_lt : P n 0 < 1 := by simpa [hP.zero_eq n]
    exact exercise21101_lt_partitionBoundIndex_of_partitionPoint_lt_time P n 0 1 hzero_lt
  have hprefix :
      ∀ m, m < coarseBound →
        Finset.sum (Finset.range m) inner = Finset.sum (Finset.range (start m)) g := by
    intro m hm
    induction m with
    | zero =>
        -- Proof comment: before the first coarse block there are no descendants, and the copied
        -- initial point is still index `0` on the finer row.
        have hstart0 : start 0 = 0 := exercise21101CoarseEndpointRefinementIndex_zero P n
        simp [inner, hstart0]
    | succ m ih =>
        have hm_lt : m < coarseBound := Nat.lt_of_succ_lt hm
        have hend :
            finish m = start (m + 1) :=
          exercise21101NextPointBound_eq_coarseEndpointRefinementIndex_succ P n m hm
        have hstart_lt : start m < start (m + 1) := by
          rw [← hend]
          exact exercise21101CoarseEndpointRefinementIndex_lt_nextPointBound P n m hm_lt
        calc
          Finset.sum (Finset.range (m + 1)) inner
              = Finset.sum (Finset.range m) inner + inner m := by
                  rw [Finset.sum_range_succ]
          _ = Finset.sum (Finset.range (start m)) g + inner m := by
                rw [ih hm_lt]
          _ = Finset.sum (Finset.range (start m)) g +
                Finset.sum (Finset.Ico (start m) (start (m + 1))) g := by
                  congr 1
                  rw [show inner m =
                    Finset.sum (Finset.range (start (m + 1) - start m))
                      (fun r ↦ g (start m + r)) by simpa [inner, hend]]
                  symm
                  rw [Finset.sum_Ico_eq_sum_range]
          _ = Finset.sum (Finset.range (start (m + 1))) g := by
                exact Finset.sum_range_add_sum_Ico g (Nat.le_of_lt hstart_lt)
  let last := coarseBound - 1
  have hlast_succ : last + 1 = coarseBound := by
    -- Proof comment: `last` is the final active coarse index.
    exact Nat.succ_pred_eq_of_pos hcoarse_pos
  have hlast_lt : last < coarseBound := by
    exact Nat.pred_lt (Nat.ne_of_gt hcoarse_pos)
  have hlast_finish : finish last = fineBound := by
    -- Proof comment: the final active coarse block is exactly the one whose clipped right endpoint
    -- hits time `1`, so its descendant range reaches the full fine-row truncation index.
    have hcoarse_hit : (1 : NNReal) ≤ P n coarseBound := le_partitionBoundIndex_time P n 1
    have hright : partitionNextPointUpTo P n last 1 = 1 := by
      rw [partitionNextPointUpTo, hlast_succ, min_eq_right hcoarse_hit]
    simpa [finish, fineBound] using congrArg (partitionBoundIndex P (n + 1)) hright
  have hlast_start_lt : start last < fineBound := by
    rw [← hlast_finish]
    exact exercise21101CoarseEndpointRefinementIndex_lt_nextPointBound P n last hlast_lt
  calc
    Finset.sum (Finset.range coarseBound) inner
        = Finset.sum (Finset.range last) inner + inner last := by
            rw [← hlast_succ, Finset.sum_range_succ]
    _ = Finset.sum (Finset.range (start last)) g + inner last := by
          rw [hprefix last hlast_lt]
    _ = Finset.sum (Finset.range (start last)) g + Finset.sum (Finset.Ico (start last) fineBound) g := by
          congr 1
          rw [show inner last =
            Finset.sum (Finset.range (fineBound - start last))
              (fun r ↦ g (start last + r)) by simpa [inner, hlast_finish]]
          symm
          rw [Finset.sum_Ico_eq_sum_range]
    _ = Finset.sum (Finset.range fineBound) g := by
          exact Finset.sum_range_add_sum_Ico g (Nat.le_of_lt hlast_start_lt)

/-- Helper for Exercise 21.10.1: every descendant block inside one active coarse block has the same
clipped right endpoint whether we clip at the coarse right edge or directly at time `1`. -/
lemma exercise21101Descendant_nextPointUpTo_eq_one
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i r : ℕ) (hi : i < partitionBoundIndex P n 1)
    (hr :
      r <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    partitionNextPointUpTo P (n + 1)
        (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
        (partitionNextPointUpTo P n i 1)
      =
        partitionNextPointUpTo P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r) 1 := by
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let finish := partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1)
  have hstart_lt_finish : start < finish :=
    exercise21101CoarseEndpointRefinementIndex_lt_nextPointBound P n i hi
  by_cases hnext : i + 1 < partitionBoundIndex P n 1
  · -- Proof comment: before the terminal coarse block, the coarse right endpoint is itself a
    -- finer partition point, so every descendant right endpoint is still clipped by that point.
    have hfinish :
        finish = exercise21101CoarseEndpointRefinementIndex P n (i + 1) (n + 1) :=
      exercise21101NextPointBound_eq_coarseEndpointRefinementIndex_succ P n i hnext
    have hcoarse_right :
        partitionNextPointUpTo P n i 1 = P n (i + 1) :=
      exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex P n i 1 hnext
    have hfinish_spec :
        P (n + 1) finish = partitionNextPointUpTo P n i 1 := by
      rw [hfinish]
      simpa [hcoarse_right] using
        exercise21101CoarseEndpointRefinementIndex_spec P n (i + 1) (n + 1) (Nat.le_succ n)
    have hnext_le_finish : start + (r + 1) ≤ finish := by
      have hlt : start + r < finish := by
        calc
          start + r < start +
              (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) - start) := by
                simpa [start, finish] using Nat.add_lt_add_left hr start
          _ = finish := Nat.add_sub_of_le (Nat.le_of_lt hstart_lt_finish)
      exact Nat.succ_le_of_lt hlt
    have hchild_le_coarse :
        P (n + 1) (start + (r + 1)) ≤ partitionNextPointUpTo P n i 1 := by
      calc
        P (n + 1) (start + (r + 1)) ≤ P (n + 1) finish :=
          (hP.strictMono (n + 1)).monotone hnext_le_finish
        _ = partitionNextPointUpTo P n i 1 := hfinish_spec
    have hchild_lt_one : P (n + 1) (start + (r + 1)) ≤ (1 : NNReal) := by
      exact le_trans hchild_le_coarse (by simp [partitionNextPointUpTo])
    have hchild_le_min :
        P (n + 1) (start + (r + 1)) ≤ min (P n (i + 1)) 1 := by
      refine le_min ?_ hchild_lt_one
      simpa [hcoarse_right] using hchild_le_coarse
    have hchild_le_min' :
        P (n + 1) (start + r + 1) ≤ min (P n (i + 1)) 1 := by
      simpa [Nat.add_assoc] using hchild_le_min
    have hchild_lt_one' :
        P (n + 1) (start + r + 1) ≤ (1 : NNReal) := by
      simpa [Nat.add_assoc] using hchild_lt_one
    have hmin :
        min (P (n + 1) (start + r + 1)) (min (P n (i + 1)) 1) =
          min (P (n + 1) (start + r + 1)) 1 := by
      rw [min_eq_left hchild_le_min', min_eq_left hchild_lt_one']
    simpa [partitionNextPointUpTo, hcoarse_right, Nat.add_assoc] using hmin
  · -- Proof comment: on the terminal coarse block, the coarse right endpoint is already `1`.
    have hlast :
        i + 1 = partitionBoundIndex P n 1 := by
      exact le_antisymm (Nat.succ_le_of_lt hi) (Nat.le_of_not_gt hnext)
    have hcoarse_right : partitionNextPointUpTo P n i 1 = 1 := by
      rw [partitionNextPointUpTo, hlast, min_eq_right (le_partitionBoundIndex_time P n 1)]
    simp [hcoarse_right]

/-- Helper for Exercise 21.10.1: before the last descendant of an active coarse block, the
clipped right endpoint on row `n + 1` is the genuine next finer partition point. -/
lemma exercise21101Descendant_nextPointUpTo_eq_next
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i r : ℕ) (hi : i < partitionBoundIndex P n 1)
    (hr :
      r + 1 <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    partitionNextPointUpTo P (n + 1)
        (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
        (partitionNextPointUpTo P n i 1)
      =
        P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + (r + 1)) := by
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let finish := partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1)
  have hr_lt : r < finish - start := Nat.lt_of_succ_lt hr
  have hclipped :
      partitionNextPointUpTo P (n + 1) (start + r) (partitionNextPointUpTo P n i 1) =
        partitionNextPointUpTo P (n + 1) (start + r) 1 := by
    -- Proof comment: the earlier descendant clipping lemma lets us replace the coarse-right
    -- horizon by the global horizon `1` before normalizing to the next partition point.
    simpa [start] using exercise21101Descendant_nextPointUpTo_eq_one P n i r hi hr_lt
  have hsucc_lt_finish : start + (r + 1) < finish := by
    -- Proof comment: `r + 1` still lies inside the descendant range, so the next finer index is
    -- strictly before the coarse block boundary.
    calc
      start + (r + 1) < start + (finish - start) := by
        simpa [finish, start] using Nat.add_lt_add_left hr start
      _ = finish := Nat.add_sub_of_le <|
          Nat.le_of_lt (exercise21101CoarseEndpointRefinementIndex_lt_nextPointBound P n i hi)
  have hfinish_le_one :
      finish ≤ partitionBoundIndex P (n + 1) 1 := by
    -- Proof comment: the coarse clipped right endpoint is always bounded by `1`, so its row
    -- boundary index is no later than the global horizon-`1` boundary index.
    refine Nat.find_min' (exists_partition_index_le_time P (n + 1) (partitionNextPointUpTo P n i 1))
      ?_
    exact le_trans (by simp [partitionNextPointUpTo]) (le_partitionBoundIndex_time P (n + 1) 1)
  have hsucc_lt_one : start + (r + 1) < partitionBoundIndex P (n + 1) 1 :=
    lt_of_lt_of_le hsucc_lt_finish hfinish_le_one
  calc
    partitionNextPointUpTo P (n + 1) (start + r) (partitionNextPointUpTo P n i 1)
        = partitionNextPointUpTo P (n + 1) (start + r) 1 := hclipped
    _ = P (n + 1) ((start + r) + 1) := by
          exact exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
            P (n + 1) (start + r) 1 hsucc_lt_one
    _ = P (n + 1) (start + (r + 1)) := by
          simp [Nat.add_assoc]

/-- Helper for Exercise 21.10.1: inside one active coarse block, the left endpoint of descendant
`r` is reached by summing the first `r` row-`n + 1` descendant increments. -/
lemma exercise21101Descendant_prefixIncrement_eq_sum
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i r : ℕ) (hi : i < partitionBoundIndex P n 1)
    (hr :
      r <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    (fun ω ↦
      W (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)) ω -
        W (P n i) ω)
      =
        fun ω ↦
          Finset.sum (Finset.range r) fun s ↦
            (W (partitionNextPointUpTo P (n + 1)
              (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
              (partitionNextPointUpTo P n i 1)) ω -
              W (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)) ω) := by
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let coarseRight := partitionNextPointUpTo P n i 1
  let child : ℕ → Ω → ℝ :=
    fun s ω ↦
      W (partitionNextPointUpTo P (n + 1) (start + s) coarseRight) ω -
        W (P (n + 1) (start + s)) ω
  induction r with
  | zero =>
      -- Proof comment: the copied coarse left endpoint is the starting point of the descendant
      -- chain, so the empty prefix sum gives the zero increment.
      funext ω
      have hstart :
          P (n + 1) start = P n i := by
        simpa [start] using
          exercise21101CoarseEndpointRefinementIndex_spec P n i (n + 1) (Nat.le_succ n)
      simp [start, hstart]
  | succ r ih =>
      have hr_lt :
          r <
            partitionBoundIndex P (n + 1) coarseRight - start := Nat.lt_of_succ_lt hr
      have hnext :
          partitionNextPointUpTo P (n + 1) (start + r) coarseRight =
            P (n + 1) (start + (r + 1)) := by
        -- Proof comment: the inductive step advances one descendant block because this is not yet
        -- the final child inside the active coarse block.
        simpa [start, coarseRight] using
          exercise21101Descendant_nextPointUpTo_eq_next P n i r hi hr
      calc
        (fun ω ↦ W (P (n + 1) (start + (r + 1))) ω - W (P n i) ω)
            =
              (fun ω ↦
                (W (P (n + 1) (start + r)) ω - W (P n i) ω) + child r ω) := by
                  -- Proof comment: split the longer descendant prefix at the previous finer
                  -- endpoint and identify the last summand with the current child increment.
                  funext ω
                  rw [show child r ω =
                    W (P (n + 1) (start + (r + 1))) ω - W (P (n + 1) (start + r)) ω by
                    simp [child, hnext]]
                  ring
        _ =
            (fun ω ↦
              Finset.sum (Finset.range r) (fun s ↦ child s ω) + child r ω) := by
                funext ω
                have hih := congrFun (ih hr_lt) ω
                simpa [child, start, coarseRight] using
                  congrArg (fun x : ℝ ↦ x + child r ω) hih
        _ = fun ω ↦ Finset.sum (Finset.range (r + 1)) (fun s ↦ child s ω) := by
              funext ω
              rw [Finset.sum_range_succ]

/-- Helper for Exercise 21.10.1: the clipped row-`m` increments on the index segment beginning at
`j` form a finite vector. -/
noncomputable abbrev exercise21101RowSegmentIncrementVector
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m j : ℕ) (T : NNReal) :
    Ω → Fin (partitionBoundIndex P m T - j) → ℝ :=
  fun ω q ↦
    W (partitionNextPointUpTo P m (j + q) T) ω - W (P m (j + q)) ω

/-- Helper for Exercise 21.10.1: the row-segment increment vector is measurable. -/
lemma exercise21101RowSegmentIncrementVector_measurable
    (W : NNReal → Ω → ℝ) (hW_meas : ∀ t, StronglyMeasurable (W t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m j : ℕ) (T : NNReal) :
    Measurable (exercise21101RowSegmentIncrementVector W P m j T) := by
  -- Proof comment: each coordinate is one deterministic-time Brownian increment, and the finite
  -- product measurability is therefore coordinatewise.
  refine measurable_pi_lambda _ fun q ↦ ?_
  exact
    ((hW_meas (partitionNextPointUpTo P m (j + q) T)).measurable.sub
      (hW_meas (P m (j + q))).measurable)

/-- Helper for Exercise 21.10.1: the row-segment increment vector has the expected finite product
centered-Gaussian law. -/
lemma exercise21101RowSegmentIncrementVector_map_eq_gaussianPi
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m j : ℕ) (T : NNReal)
    (hj : j < partitionBoundIndex P m T) :
    μ.map (exercise21101RowSegmentIncrementVector W P m j T) =
      Measure.pi
        (fun q : Fin (partitionBoundIndex P m T - j) ↦
          gaussianReal (0 : ℝ)
            (partitionNextPointUpTo P m (j + q) T - P m (j + q))) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let bound := partitionBoundIndex P m T
  let N := bound - j
  let τ : ℕ → NNReal := fun k ↦ if h : k < N then P m (j + k) else T
  let Y : ℕ → Ω → ℝ := fun k ω ↦ W (τ (k + 1)) ω - W (τ k) ω
  have hj_le : j ≤ bound := Nat.le_of_lt hj
  have hτmono : Monotone τ := by
    intro a b hab
    by_cases hb : b < N
    · have ha : a < N := lt_of_le_of_lt hab hb
      simp [τ, ha, hb]
      exact (IsAdmissiblePartitionSequence.strictMono (P := P) m).monotone <|
        Nat.add_le_add_left hab j
    · by_cases ha : a < N
      · have haj_lt : j + a < bound := by
          calc
            j + a < j + N := Nat.add_lt_add_left ha j
            _ = bound := by simp [N, bound, Nat.add_sub_of_le hj_le]
        have hτa_le : τ a ≤ T := by
          simp [τ, ha]
          exact le_of_lt <|
            exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P m (j + a) T haj_lt
        simpa [τ, hb] using hτa_le
      · simp [τ, ha, hb]
  have hY_indepNat : iIndepFun Y μ := by
    -- Proof comment: the row segment is cut from one monotone mesh, so Brownian independent
    -- increments apply directly to the full `ℕ`-indexed family.
    simpa [Y, τ, add_assoc, add_left_comm, add_comm] using
      hW.indepIncrements.nat (t := τ) hτmono
  have hτ_self :
      ∀ q : Fin N, τ q = P m (j + q) := by
    intro q
    simp [τ, q.is_lt]
  have hτ_succ :
      ∀ q : Fin N, τ (q + 1) = partitionNextPointUpTo P m (j + q) T := by
    intro q
    by_cases hsucc : (q : ℕ) + 1 < N
    · have hnext_lt : j + q + 1 < bound := by
        calc
          j + (q + 1) < j + N := Nat.add_lt_add_left hsucc j
          _ = bound := by simp [N, bound, Nat.add_sub_of_le hj_le]
      have hnext :
          partitionNextPointUpTo P m (j + q) T = P m (j + q + 1) := by
        exact
          exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
            P m (j + q) T hnext_lt
      simp [τ, hsucc, hnext, Nat.add_assoc]
    · have hq_last : (q : ℕ) + 1 = N := by
        exact le_antisymm (Nat.succ_le_of_lt q.is_lt) (Nat.not_lt.mp hsucc)
      have hjN : j + N = bound := by
        simp [N, bound, Nat.add_sub_of_le hj_le]
      have hbound : j + q + 1 = bound := by
        calc
          j + q + 1 = j + (q + 1) := by simp [Nat.add_assoc]
          _ = j + N := by rw [hq_last]
          _ = bound := hjN
      have hnext :
          partitionNextPointUpTo P m (j + q) T = T := by
        rw [partitionNextPointUpTo, min_eq_right]
        simpa [hbound] using le_partitionBoundIndex_time P m T
      simp [τ, hsucc, hnext]
  have hSegment_indep :
      iIndepFun
        (fun q : Fin N ↦ fun ω ↦ exercise21101RowSegmentIncrementVector W P m j T ω q) μ := by
    -- Proof comment: restricting the `ℕ`-indexed mesh increments to the finite active segment
    -- keeps independence and normalizes the endpoints to the clipped row coordinates.
    simpa [exercise21101RowSegmentIncrementVector, Y, hτ_self, hτ_succ, Nat.add_assoc] using
      hY_indepNat.precomp (g := fun q : Fin N ↦ (q : ℕ)) fun a b h ↦ Fin.ext h
  calc
    μ.map (exercise21101RowSegmentIncrementVector W P m j T)
        = μ.map (fun ω ↦ fun q : Fin N ↦ exercise21101RowSegmentIncrementVector W P m j T ω q) := by
            rfl
    _ =
          Measure.pi
            (fun q : Fin N ↦
              μ.map (fun ω ↦ exercise21101RowSegmentIncrementVector W P m j T ω q)) := by
                exact
                  (iIndepFun_iff_map_fun_eq_pi_map fun q : Fin N ↦
                    (((hW.stronglyMeasurable (partitionNextPointUpTo P m (j + q) T)).measurable.sub
                      (hW.stronglyMeasurable (P m (j + q))).measurable).aemeasurable)).1
                    hSegment_indep
    _ =
        Measure.pi
          (fun q : Fin N ↦
            gaussianReal (0 : ℝ)
              (partitionNextPointUpTo P m (j + q) T - P m (j + q))) := by
            congr 1
            funext q
            have hjq_lt : j + q < bound := by
              calc
                j + q < j + N := Nat.add_lt_add_left q.is_lt j
                _ = bound := by simp [N, bound, Nat.add_sub_of_le hj_le]
            have hst :
                P m (j + q) ≤ partitionNextPointUpTo P m (j + q) T := by
              rw [partitionNextPointUpTo]
              refine le_min ?_ ?_
              · exact le_of_lt <|
                  (IsAdmissiblePartitionSequence.strictMono (P := P) m) (Nat.lt_succ_self (j + q))
              · exact le_of_lt <|
                  exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex
                    P m (j + q) T hjq_lt
            simpa [exercise21101RowSegmentIncrementVector] using
              (brownianIncrement_hasLaw_ofBrownianMotion hW hst).map_eq

/-- Helper for Exercise 21.10.1: the full row-`m` clipped increment vector up to time `1`. -/
noncomputable abbrev exercise21101WholeRowIncrementVector
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m : ℕ) :
    Ω → Fin (partitionBoundIndex P m 1) → ℝ :=
  exercise21101RowSegmentIncrementVector W P m 0 1

/-- Helper for Exercise 21.10.1: the full row-`m` increment vector is measurable. -/
lemma exercise21101WholeRowIncrementVector_measurable
    (W : NNReal → Ω → ℝ) (hW_meas : ∀ t, StronglyMeasurable (W t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m : ℕ) :
    Measurable (exercise21101WholeRowIncrementVector W P m) := by
  -- Proof comment: this is the row-segment measurability statement specialized to the full
  -- segment starting at index `0` and ending at the horizon `1`.
  simpa [exercise21101WholeRowIncrementVector] using
    exercise21101RowSegmentIncrementVector_measurable W hW_meas P m 0 1

/-- Helper for Exercise 21.10.1: the full row-`m` increment vector has the expected centered
Gaussian product law. -/
lemma exercise21101WholeRowIncrementVector_map_eq_gaussianPi
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (m : ℕ) :
    μ.map (exercise21101WholeRowIncrementVector W P m) =
      Measure.pi
        (fun q : Fin (partitionBoundIndex P m 1) ↦
          gaussianReal (0 : ℝ)
            (partitionNextPointUpTo P m q 1 - P m q)) := by
  -- Proof comment: this is the previous row-segment law with starting index `0`; positivity of
  -- the horizon-`1` truncation index supplies the required nonempty active segment.
  simpa [exercise21101WholeRowIncrementVector] using
    exercise21101RowSegmentIncrementVector_map_eq_gaussianPi
      (hW := hW) (P := P) (m := m) (j := 0) (T := 1)
      (exercise21101_zero_lt_partitionBoundIndex_one P m)

/-- Helper for Exercise 21.10.1: along one row segment, the increment from the segment start to
the `r`-th later endpoint is the sum of the first `r` clipped atomic increments. -/
lemma exercise21101RowSegment_prefixIncrement_eq_sum
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (m j r : ℕ) (T : NNReal)
    (hj : j < partitionBoundIndex P m T)
    (hr : r < partitionBoundIndex P m T - j) :
    (fun ω ↦ W (P m (j + r)) ω - W (P m j) ω)
      =
        fun ω ↦
          Finset.sum (Finset.range r) fun s ↦
            (W (partitionNextPointUpTo P m (j + s) T) ω - W (P m (j + s)) ω) := by
  induction r with
  | zero =>
      -- Proof comment: at the segment start, both sides are the zero increment and the empty
      -- prefix sum.
      funext ω
      simp
  | succ r ih =>
      have hr_lt : r < partitionBoundIndex P m T - j := Nat.lt_of_succ_lt hr
      have hnext_lt : j + r + 1 < partitionBoundIndex P m T := by
        calc
          j + (r + 1) < j + (partitionBoundIndex P m T - j) := by
            exact Nat.add_lt_add_left hr j
          _ = partitionBoundIndex P m T := by
            exact Nat.add_sub_of_le (Nat.le_of_lt hj)
      have hnext :
          partitionNextPointUpTo P m (j + r) T = P m (j + r + 1) := by
        exact
          exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
            P m (j + r) T hnext_lt
      calc
        (fun ω ↦ W (P m (j + (r + 1))) ω - W (P m j) ω)
            =
              (fun ω ↦
                (W (P m (j + r)) ω - W (P m j) ω) +
                  (W (partitionNextPointUpTo P m (j + r) T) ω - W (P m (j + r)) ω)) := by
                    -- Proof comment: split the longer segment increment at the previous row point
                    -- and rewrite the last piece by the clipped successor identity.
                    funext ω
                    rw [show
                      W (partitionNextPointUpTo P m (j + r) T) ω - W (P m (j + r)) ω =
                        W (P m (j + r + 1)) ω - W (P m (j + r)) ω by simp [hnext]]
                    ring
        _ =
            (fun ω ↦
              Finset.sum (Finset.range r) (fun s ↦
                (W (partitionNextPointUpTo P m (j + s) T) ω - W (P m (j + s)) ω)) +
                  (W (partitionNextPointUpTo P m (j + r) T) ω - W (P m (j + r)) ω)) := by
                    funext ω
                    have hω := congrFun (ih hr_lt) ω
                    simpa [hω]
        _ =
            (fun ω ↦
              Finset.sum (Finset.range (r + 1)) fun s ↦
                (W (partitionNextPointUpTo P m (j + s) T) ω - W (P m (j + s)) ω)) := by
                  funext ω
                  rw [Finset.sum_range_succ]

/-- Helper for Exercise 21.10.1: between two partition points on the same row, the increment is
the sum of the intervening clipped atomic row increments. -/
lemma exercise21101PartitionPointIncrement_eq_sum_atomicIncrements
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (m a b : ℕ)
    (ha : a < partitionBoundIndex P m 1)
    (hab : a ≤ b)
    (hb : b < partitionBoundIndex P m 1) :
    (fun ω ↦ W (P m b) ω - W (P m a) ω)
      =
        fun ω ↦
          Finset.sum (Finset.range (b - a)) fun s ↦
            (W (partitionNextPointUpTo P m (a + s) 1) ω - W (P m (a + s)) ω) := by
  have hr :
      b - a < partitionBoundIndex P m 1 - a := by
    -- Proof comment: the right endpoint still lies before the row-`m` horizon-`1` truncation
    -- index, so the transported interval length fits inside the remaining atomic segment.
    have hadd :
        a + (b - a) < a + (partitionBoundIndex P m 1 - a) := by
      simpa [Nat.add_sub_of_le hab, Nat.add_sub_of_le (Nat.le_of_lt ha)] using hb
    exact Nat.lt_of_add_lt_add_left hadd
  -- Proof comment: this is the row-segment prefix identity started at the left endpoint `a`.
  simpa [Nat.add_sub_of_le hab] using
    (exercise21101RowSegment_prefixIncrement_eq_sum
      W P m a (b - a) 1 ha hr)

/-- Helper for Exercise 21.10.1: from a partition point on row `m`, the increment up to time `1`
is the sum of the remaining clipped atomic row increments. -/
lemma exercise21101IncrementToOne_eq_sum_atomicIncrements
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (m a : ℕ)
    (ha : a < partitionBoundIndex P m 1) :
    (fun ω ↦ W 1 ω - W (P m a) ω)
      =
        fun ω ↦
          Finset.sum (Finset.range (partitionBoundIndex P m 1 - a)) fun s ↦
            (W (partitionNextPointUpTo P m (a + s) 1) ω - W (P m (a + s)) ω) := by
  let bound := partitionBoundIndex P m 1
  let last := Nat.pred (bound - a)
  have hcount_pos : 0 < bound - a := Nat.sub_pos_of_lt ha
  have hlast_lt : last < bound - a := Nat.pred_lt (Nat.ne_of_gt hcount_pos)
  have hlast_succ : last + 1 = bound - a := Nat.succ_pred_eq_of_pos hcount_pos
  have hlast_index : a + last + 1 = bound := by
    -- Proof comment: the final clipped increment starts at the last partition point before time
    -- `1`, so adding one successor step reaches the boundary index.
    calc
      a + last + 1 = a + (last + 1) := by simp [Nat.add_assoc]
      _ = a + (bound - a) := by rw [hlast_succ]
      _ = bound := Nat.add_sub_of_le (Nat.le_of_lt ha)
  have hfinal :
      partitionNextPointUpTo P m (a + last) 1 = 1 := by
    -- Proof comment: at the last active row coordinate, the clipped successor is exactly the
    -- terminal horizon `1`.
    rw [partitionNextPointUpTo, hlast_index, min_eq_right]
    exact le_partitionBoundIndex_time P m 1
  have hprefix :=
    exercise21101RowSegment_prefixIncrement_eq_sum W P m a last 1 ha hlast_lt
  calc
    (fun ω ↦ W 1 ω - W (P m a) ω)
        =
          (fun ω ↦
            (W (P m (a + last)) ω - W (P m a) ω) +
              (W 1 ω - W (P m (a + last)) ω)) := by
            -- Proof comment: split the full increment at the last partition point before `1`.
            funext ω
            ring
    _ =
        (fun ω ↦
          Finset.sum (Finset.range last) (fun s ↦
            (W (partitionNextPointUpTo P m (a + s) 1) ω - W (P m (a + s)) ω)) +
              (W 1 ω - W (P m (a + last)) ω)) := by
            -- Proof comment: the initial part is the existing row-segment prefix sum.
            funext ω
            have hω := congrFun hprefix ω
            simpa [hω]
    _ =
        (fun ω ↦
          Finset.sum (Finset.range last) (fun s ↦
            (W (partitionNextPointUpTo P m (a + s) 1) ω - W (P m (a + s)) ω)) +
              (W (partitionNextPointUpTo P m (a + last) 1) ω - W (P m (a + last)) ω)) := by
            -- Proof comment: rewrite the final summand using the terminal clipping identity.
            funext ω
            simp [hfinal]
    _ =
        (fun ω ↦
          Finset.sum (Finset.range (last + 1)) fun s ↦
            (W (partitionNextPointUpTo P m (a + s) 1) ω - W (P m (a + s)) ω)) := by
            -- Proof comment: append the terminal clipped increment to the prefix sum.
            funext ω
            rw [Finset.sum_range_succ]
    _ =
        (fun ω ↦
          Finset.sum (Finset.range (bound - a)) fun s ↦
            (W (partitionNextPointUpTo P m (a + s) 1) ω - W (P m (a + s)) ω)) := by
            rw [hlast_succ]

/-- Helper for Exercise 21.10.1: from a partition point on row `m`, the increment up to the
clipped successor of block `k` is the sum of the corresponding clipped atomic row increments. -/
lemma exercise21101IncrementToNextPointUpTo_eq_sum_atomicIncrements
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (m a k : ℕ)
    (ha : a < partitionBoundIndex P m 1)
    (hak : a ≤ k)
    (hk : k < partitionBoundIndex P m 1) :
    (fun ω ↦ W (partitionNextPointUpTo P m k 1) ω - W (P m a) ω)
      =
        fun ω ↦
          Finset.sum
            (Finset.range (partitionBoundIndex P m (partitionNextPointUpTo P m k 1) - a))
            fun s ↦
              (W (partitionNextPointUpTo P m (a + s) 1) ω - W (P m (a + s)) ω) := by
  by_cases hsucc : k + 1 < partitionBoundIndex P m 1
  · have hnext : partitionNextPointUpTo P m k 1 = P m (k + 1) := by
      -- Proof comment: before the final active block, clipping at `1` leaves the genuine next
      -- partition point unchanged.
      exact
        exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
          P m k 1 hsucc
    -- Proof comment: in the interior case this is exactly the partition-point transport lemma.
    simpa [hnext, exercise21101_partitionBoundIndex_eq_of_partitionPoint] using
      (exercise21101PartitionPointIncrement_eq_sum_atomicIncrements
        W P m a (k + 1) ha (Nat.le_trans hak (Nat.le_succ k)) hsucc)
  · have hlast : k + 1 = partitionBoundIndex P m 1 := by
      exact le_antisymm (Nat.succ_le_of_lt hk) (Nat.le_of_not_gt hsucc)
    have hnext : partitionNextPointUpTo P m k 1 = 1 := by
      -- Proof comment: at the final active block, clipping at `1` lands exactly at the horizon.
      rw [partitionNextPointUpTo, hlast, min_eq_right]
      exact le_partitionBoundIndex_time P m 1
    -- Proof comment: the terminal block case is the dedicated increment-to-`1` identity.
    simpa [hnext] using
      (exercise21101IncrementToOne_eq_sum_atomicIncrements W P m a ha)

/-- Helper for Exercise 21.10.1: the refined cross remainder is exactly the descendant increment
polynomial obtained by pairing each child increment with the sum of its predecessors. -/
noncomputable abbrev exercise21101DescendantCrossSummand
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i r : ℕ) : Ω → ℝ :=
  fun ω ↦
    2 *
        (Finset.sum (Finset.range r) fun s ↦
          (W (partitionNextPointUpTo P (n + 1)
            (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
            (partitionNextPointUpTo P n i 1)) ω -
            W (P (n + 1)
              (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)) ω)) *
      (W (partitionNextPointUpTo P (n + 1)
        (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
        (partitionNextPointUpTo P n i 1)) ω -
        W (P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)) ω)

/-- Helper for Exercise 21.10.1: the refined cross remainder is exactly the descendant increment
polynomial obtained by pairing each child increment with the sum of its predecessors. -/
lemma exercise21101RefinedBlockCrossTerm_eq_descendantPrefixProducts
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i : ℕ) (hi : i < partitionBoundIndex P n 1) :
    exercise21101RefinedBlockCrossTerm W P n i =
      fun ω ↦
        Finset.sum
          (Finset.range
            (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
              exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
          (fun r ↦
            2 *
                (Finset.sum (Finset.range r) fun s ↦
                  (W (partitionNextPointUpTo P (n + 1)
                    (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
                    (partitionNextPointUpTo P n i 1)) ω -
                    W (P (n + 1)
                      (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)) ω)) *
              (W (partitionNextPointUpTo P (n + 1)
                (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
                (partitionNextPointUpTo P n i 1)) ω -
                W (P (n + 1)
                  (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)) ω)) := by
  -- Proof comment: rewrite each left factor in the stored cross-term definition by the descendant
  -- prefix-sum identity so that the whole remainder depends only on the descendant increments.
  funext ω
  simp only [exercise21101RefinedBlockCrossTerm]
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hprefix :=
    congrFun (exercise21101Descendant_prefixIncrement_eq_sum W P n i r hi (Finset.mem_range.mp hr)) ω
  simp [hprefix]

/-- Helper for Exercise 21.10.1: the refined cross remainder is the finite sum of its packaged
descendant prefix-product summands. -/
lemma exercise21101RefinedBlockCrossTerm_eq_sum_descendantCrossSummand
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i : ℕ) (hi : i < partitionBoundIndex P n 1) :
    exercise21101RefinedBlockCrossTerm W P n i =
      fun ω ↦
        Finset.sum
          (Finset.range
            (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
              exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
          (fun r ↦ exercise21101DescendantCrossSummand W P n i r ω) := by
  -- Proof comment: this is just the descendant-prefix expansion repackaged with the dedicated
  -- summand name so later set-integral arguments can address one descendant block at a time.
  simpa [exercise21101DescendantCrossSummand] using
    exercise21101RefinedBlockCrossTerm_eq_descendantPrefixProducts W P n i hi

/-- Helper for Exercise 21.10.1: each packaged descendant prefix-product summand is integrable. -/
lemma exercise21101DescendantCrossSummand_integrable
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n i r : ℕ) (hi : i < partitionBoundIndex P n 1)
    (hr :
      r <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    Integrable (exercise21101DescendantCrossSummand W P n i r) μ := by
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let coarseRight := partitionNextPointUpTo P n i 1
  let finish := partitionBoundIndex P (n + 1) coarseRight
  let child : ℕ → Ω → ℝ :=
    fun s ω ↦
      W (partitionNextPointUpTo P (n + 1) (start + s) coarseRight) ω -
        W (P (n + 1) (start + s)) ω
  have hchild_mem :
      ∀ s,
        s < finish - start →
          MemLp (child s) 2 μ := by
    intro s hs
    have hs_lt_finish : start + s < finish := by
      calc
        start + s < start + (finish - start) := Nat.add_lt_add_left hs start
        _ = finish := Nat.add_sub_of_le <|
            Nat.le_of_lt (exercise21101CoarseEndpointRefinementIndex_lt_nextPointBound P n i hi)
    have hfinish_le_one :
        finish ≤ partitionBoundIndex P (n + 1) 1 := by
      -- Proof comment: the coarse clipped right endpoint is bounded by `1`, so its finer
      -- truncation index is no later than the global horizon-`1` truncation index.
      refine Nat.find_min' (exists_partition_index_le_time P (n + 1) coarseRight) ?_
      exact le_trans (by simp [coarseRight, partitionNextPointUpTo]) (le_partitionBoundIndex_time P (n + 1) 1)
    have hs_lt_one : start + s < partitionBoundIndex P (n + 1) 1 :=
      lt_of_lt_of_le hs_lt_finish hfinish_le_one
    have hright_eq :
        partitionNextPointUpTo P (n + 1) (start + s) coarseRight =
          partitionNextPointUpTo P (n + 1) (start + s) 1 := by
      simpa [start, coarseRight, finish] using
        exercise21101Descendant_nextPointUpTo_eq_one P n i s hi hs
    have hleft_le :
        P (n + 1) (start + s) ≤ partitionNextPointUpTo P (n + 1) (start + s) 1 := by
      -- Proof comment: before the horizon-`1` truncation index, the clipped successor still lies
      -- to the right of the current descendant start.
      rw [partitionNextPointUpTo]
      refine le_min ?_ ?_
      · exact le_of_lt ((hP.strictMono (n + 1)) (Nat.lt_succ_self (start + s)))
      · exact le_of_lt
          (exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex
            P (n + 1) (start + s) 1 hs_lt_one)
    simpa [child, hright_eq] using
      brownianIncrement_memLp_two
        (μ := μ) (B := W) hW
        (s := P (n + 1) (start + s))
        (t := partitionNextPointUpTo P (n + 1) (start + s) 1) hleft_le
  have hprefix_mem :
      MemLp (fun ω ↦ Finset.sum (Finset.range r) (fun s ↦ child s ω)) 2 μ := by
    -- Proof comment: a finite prefix of descendant Brownian increments stays in `L²`.
    refine memLp_finset_sum _ ?_
    intro s hs
    exact hchild_mem s (lt_of_lt_of_le (Finset.mem_range.mp hs) (Nat.le_of_lt hr))
  have hcurrent_mem : MemLp (child r) 2 μ := hchild_mem r hr
  have hprod_int :
      Integrable
        (fun ω ↦
          (Finset.sum (Finset.range r) fun s ↦ child s ω) * child r ω) μ := by
    -- Proof comment: Hölder upgrades the two `L²` factors to an `L¹` product.
    exact hprefix_mem.integrable_mul hcurrent_mem
  have hsummand_eq :
      exercise21101DescendantCrossSummand W P n i r =
        fun ω ↦
          2 *
            ((Finset.sum (Finset.range r) fun s ↦ child s ω) * child r ω) := by
    -- Proof comment: unfold the packaged summand and rewrite it in the same product order as the
    -- integrable prefix-current product.
    funext ω
    simp [exercise21101DescendantCrossSummand, child, start, coarseRight, mul_assoc]
  rw [hsummand_eq]
  simpa using hprod_int.const_mul (2 : ℝ)

/-- Helper for Exercise 21.10.1: one backward-process step is the next stage plus the finite sum
of the refined cross remainders. -/
lemma exercise21101BackwardProcess_stepDifference_eq_sum_refinedCross
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    (n : ℕ) :
    exercise21101BackwardProcess W P (toDual n) =
      fun ω ↦
        exercise21101BackwardProcess W P (toDual (n + 1)) ω +
          Finset.sum (Finset.range (partitionBoundIndex P n 1))
            (fun i ↦ exercise21101RefinedBlockCrossTerm W P n i ω) := by
  -- Proof comment: first rewrite `Yₙ` as the sum of refined block decompositions, then reorganize
  -- all descendant block sums into the single active row `n + 1`.
  funext ω
  calc
    exercise21101BackwardProcess W P (toDual n) ω
        = Finset.sum (Finset.range (partitionBoundIndex P n 1))
            (fun i ↦ exercise21101RefinedBlockContribution W P n i ω) := by
              simpa using congrFun
                (exercise21101BackwardProcess_eq_sum_refinedBlockContribution W P n) ω
    _ = Finset.sum (Finset.range (partitionBoundIndex P n 1))
          (fun i ↦
            Finset.sum
              (Finset.range
                (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
                  exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
              (fun r ↦
                exercise21101BlockContribution W
                  (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r))
                  (partitionNextPointUpTo P (n + 1)
                    (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r) 1) ω) +
              exercise21101RefinedBlockCrossTerm W P n i ω) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hblock :=
              congrFun (exercise21101RefinedBlockContribution_eq_blockSum_add_crossTerm W P n i) ω
            rw [hblock]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [exercise21101Descendant_nextPointUpTo_eq_one P n i r (Finset.mem_range.mp hi)
              (Finset.mem_range.mp hr)]
    _ = Finset.sum (Finset.range (partitionBoundIndex P n 1))
          (fun i ↦
            Finset.sum
              (Finset.range
                (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
                  exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
              (fun r ↦
                exercise21101BlockContribution W
                  (P (n + 1) (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r))
                  (partitionNextPointUpTo P (n + 1)
                    (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r) 1) ω)) +
          Finset.sum (Finset.range (partitionBoundIndex P n 1))
            (fun i ↦ exercise21101RefinedBlockCrossTerm W P n i ω) := by
              rw [Finset.sum_add_distrib]
    _ = exercise21101BackwardProcess W P (toDual (n + 1)) ω +
          Finset.sum (Finset.range (partitionBoundIndex P n 1))
            (fun i ↦ exercise21101RefinedBlockCrossTerm W P n i ω) := by
          congr 1
          simpa [exercise21101BackwardProcess, exercise21101BlockContribution] using
            (exercise21101FineRow_sum_eq_sum_coarseDescendantRanges
              (P := P) (n := n)
              (g := fun j ↦
                exercise21101BlockContribution W (P (n + 1) j)
                  (partitionNextPointUpTo P (n + 1) j 1) ω))

/-- Helper for Exercise 21.10.1: each reverse-time stage of `Yₙ` is integrable. -/
lemma exercise21101BackwardProcess_integrable
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕᵒᵈ) :
    Integrable (exercise21101BackwardProcess W P n) μ := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  change Integrable
    (fun ω ↦
      Finset.sum (Finset.range (partitionBoundIndex P (ofDual n) 1)) fun k ↦
        ((W (partitionNextPointUpTo P (ofDual n) k 1) ω - W (P (ofDual n) k) ω) ^ (2 : ℕ) -
          (((partitionNextPointUpTo P (ofDual n) k 1 - P (ofDual n) k : NNReal) : ℝ)))) μ
  refine integrable_finset_sum _ ?_
  intro k hk
  have hk_lt : k < partitionBoundIndex P (ofDual n) 1 := Finset.mem_range.mp hk
  have hst :
      P (ofDual n) k ≤ partitionNextPointUpTo P (ofDual n) k 1 := by
    -- Proof comment: before the truncation index, the clipped successor still lies to the right.
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt ((IsAdmissiblePartitionSequence.strictMono (P := P) (ofDual n))
        (Nat.lt_succ_self k))
    · exact le_of_lt
        (exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P (ofDual n) k 1 hk_lt)
  have hInc_mem :
      MemLp
        (fun ω ↦ W (partitionNextPointUpTo P (ofDual n) k 1) ω - W (P (ofDual n) k) ω)
        2 μ := by
    -- Proof comment: every clipped Brownian increment up to the horizon `1` lies in `L²`.
    exact brownianIncrement_memLp_two
      (μ := μ) (B := W) hW (s := P (ofDual n) k)
      (t := partitionNextPointUpTo P (ofDual n) k 1) hst
  exact hInc_mem.integrable_sq.sub (integrable_const _)

/-- Helper for Exercise 21.10.1: every reverse-time stage of `Yₙ` has expectation `0`. -/
lemma exercise21101BackwardProcess_integral_eq_zero
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕᵒᵈ) :
    ∫ ω, exercise21101BackwardProcess W P n ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  change
    ∫ ω,
        Finset.sum (Finset.range (partitionBoundIndex P (ofDual n) 1)) fun k ↦
          ((W (partitionNextPointUpTo P (ofDual n) k 1) ω - W (P (ofDual n) k) ω) ^ (2 : ℕ) -
            (((partitionNextPointUpTo P (ofDual n) k 1 - P (ofDual n) k : NNReal) : ℝ))) ∂μ = 0
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero ?_
    intro k hk
    have hk_lt : k < partitionBoundIndex P (ofDual n) 1 := Finset.mem_range.mp hk
    have hst :
        P (ofDual n) k ≤ partitionNextPointUpTo P (ofDual n) k 1 := by
      -- Proof comment: the clipped right endpoint dominates the left endpoint before truncation.
      rw [partitionNextPointUpTo]
      refine le_min ?_ ?_
      · exact le_of_lt ((IsAdmissiblePartitionSequence.strictMono (P := P) (ofDual n))
          (Nat.lt_succ_self k))
      · exact le_of_lt
          (exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P (ofDual n) k 1 hk_lt)
    let inc : Ω → ℝ := fun ω ↦
      W (partitionNextPointUpTo P (ofDual n) k 1) ω - W (P (ofDual n) k) ω
    have hInc_mem : MemLp inc 2 μ := by
      -- Proof comment: each clipped Brownian increment is square-integrable.
      simpa [inc] using brownianIncrement_memLp_two
        (μ := μ) (B := W) hW (s := P (ofDual n) k)
        (t := partitionNextPointUpTo P (ofDual n) k 1) hst
    -- Proof comment: the deterministic lag exactly matches the increment second moment.
    calc
      ∫ ω,
          (inc ω ^ (2 : ℕ) -
            (((partitionNextPointUpTo P (ofDual n) k 1 - P (ofDual n) k : NNReal) : ℝ))) ∂μ
          = ∫ ω, inc ω ^ (2 : ℕ) ∂μ -
              ∫ ω,
                (((partitionNextPointUpTo P (ofDual n) k 1 - P (ofDual n) k : NNReal) : ℝ)) ∂μ := by
              rw [integral_sub hInc_mem.integrable_sq (integrable_const _)]
      _ =
          (((partitionNextPointUpTo P (ofDual n) k 1 - P (ofDual n) k : NNReal) : ℝ)) -
            (((partitionNextPointUpTo P (ofDual n) k 1 - P (ofDual n) k : NNReal) : ℝ)) := by
            rw [brownianIncrement_sq_integral_eq_timeLag
              (μ := μ) (B := W) hW (s := P (ofDual n) k)
              (t := partitionNextPointUpTo P (ofDual n) k 1) hst,
              integral_const, probReal_univ, one_smul]
      _ = 0 := by ring
  · intro k hk
    have hk_lt : k < partitionBoundIndex P (ofDual n) 1 := Finset.mem_range.mp hk
    have hst :
        P (ofDual n) k ≤ partitionNextPointUpTo P (ofDual n) k 1 := by
      -- Proof comment: the clipped right endpoint dominates the left endpoint before truncation.
      rw [partitionNextPointUpTo]
      refine le_min ?_ ?_
      · exact le_of_lt ((IsAdmissiblePartitionSequence.strictMono (P := P) (ofDual n))
          (Nat.lt_succ_self k))
      · exact le_of_lt
          (exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P (ofDual n) k 1 hk_lt)
    have hInc_mem :
        MemLp
          (fun ω ↦ W (partitionNextPointUpTo P (ofDual n) k 1) ω - W (P (ofDual n) k) ω)
          2 μ := by
      -- Proof comment: each clipped Brownian increment is square-integrable.
      exact brownianIncrement_memLp_two
        (μ := μ) (B := W) hW (s := P (ofDual n) k)
        (t := partitionNextPointUpTo P (ofDual n) k 1) hst
    exact hInc_mem.integrable_sq.sub (integrable_const _)

/-- Helper for Exercise 21.10.1: the stage-`n` future block array stores every centered block
contribution from rows `m ≥ n`, padded by `0` outside the active future rows and row ranges. -/
noncomputable def exercise21101FutureBlockArray
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) : Ω → ℕ → ℕ → ℝ :=
  fun ω m k ↦
    if n ≤ m then
      if k < partitionBoundIndex P m 1 then
        exercise21101BlockContribution W (P m k) (partitionNextPointUpTo P m k 1) ω
      else 0
    else 0

/-- Helper for Exercise 21.10.1: masking a future block array at stage `n` deletes every row
strictly before `n` and keeps all later coordinates unchanged. -/
noncomputable def exercise21101FutureBlockMask
    (n : ℕ) : (ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ :=
  fun x m k ↦ if n ≤ m then x m k else 0

/-- Helper for Exercise 21.10.1: the row-mask on future block arrays is measurable. -/
lemma exercise21101FutureBlockMask_measurable
    (n : ℕ) :
    Measurable (exercise21101FutureBlockMask n) := by
  -- Proof comment: each output coordinate is either the corresponding input coordinate or the
  -- constant `0`, so the product measurability is coordinatewise.
  refine measurable_pi_lambda _ fun m ↦ ?_
  refine measurable_pi_lambda _ fun k ↦ ?_
  by_cases hnm : n ≤ m
  · simp [exercise21101FutureBlockMask, hnm]
    exact (measurable_pi_apply k).comp (measurable_pi_apply m)
  · simp [exercise21101FutureBlockMask, hnm]

/-- Helper for Exercise 21.10.1: each future block array is measurable as a map into the product
space `ℕ → ℕ → ℝ`. -/
lemma exercise21101FutureBlockArray_measurable
    (W : NNReal → Ω → ℝ) (hW_meas : ∀ t, StronglyMeasurable (W t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    Measurable (exercise21101FutureBlockArray W P n) := by
  -- Proof comment: every coordinate is either one centered block contribution or the constant
  -- `0`, and the full array is measurable coordinatewise.
  refine measurable_pi_lambda _ fun m ↦ ?_
  refine measurable_pi_lambda _ fun k ↦ ?_
  by_cases hnm : n ≤ m
  · by_cases hk : k < partitionBoundIndex P m 1
    · simp [exercise21101FutureBlockArray, hnm, hk]
      exact
        (exercise21101BlockContribution_stronglyMeasurable
          W hW_meas (P m k) (partitionNextPointUpTo P m k 1)).measurable
    · simp [exercise21101FutureBlockArray, hnm, hk]
  · simp [exercise21101FutureBlockArray, hnm]

/-- Helper for Exercise 21.10.1: reconstruct one future-block row from its active coordinates by
padding zeros outside the row range below time `1`. -/
noncomputable def exercise21101FutureBlockRowOfActiveCoordinates
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (m : ℕ) :
    (Fin (partitionBoundIndex P m 1) → ℝ) → ℕ → ℝ :=
  fun z k ↦ if hk : k < partitionBoundIndex P m 1 then z ⟨k, hk⟩ else 0

/-- Helper for Exercise 21.10.1: the zero-padding reconstruction of one future-block row is
measurable. -/
lemma exercise21101FutureBlockRowOfActiveCoordinates_measurable
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (m : ℕ) :
    Measurable (exercise21101FutureBlockRowOfActiveCoordinates P m) := by
  -- Proof comment: each reconstructed coordinate is either one active-coordinate projection or
  -- the constant `0`.
  refine measurable_pi_lambda _ fun k ↦ ?_
  by_cases hk : k < partitionBoundIndex P m 1
  · simp [exercise21101FutureBlockRowOfActiveCoordinates, hk]
    exact
      (measurable_pi_apply (⟨k, hk⟩ : Fin (partitionBoundIndex P m 1)) :
        Measurable (fun z : Fin (partitionBoundIndex P m 1) → ℝ ↦ z ⟨k, hk⟩))
  · simp [exercise21101FutureBlockRowOfActiveCoordinates, hk]

/-- Helper for Exercise 21.10.1: a finite tuple of future-block rows is reconstructed from the
finite tuples of its active coordinates row by row. -/
noncomputable def exercise21101FutureBlockCylinderOwner
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (I : Finset ℕ) :
    ((i : I) → Fin (partitionBoundIndex P i 1) → ℝ) → (i : I) → ℕ → ℝ :=
  fun z i ↦ exercise21101FutureBlockRowOfActiveCoordinates P i (z i)

/-- Helper for Exercise 21.10.1: the rowwise zero-padding owner map on a finite cylinder support
is measurable. -/
lemma exercise21101FutureBlockCylinderOwner_measurable
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (I : Finset ℕ) :
    Measurable (exercise21101FutureBlockCylinderOwner P I) := by
  -- Proof comment: reconstruct each selected row independently from its active finite vector.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact
    (exercise21101FutureBlockRowOfActiveCoordinates_measurable P (i : ℕ)).comp
      (measurable_pi_apply i)

/-- Helper for Exercise 21.10.1: on each selected row, the future-block array is exactly the
zero-padding reconstruction of its active coordinates. -/
lemma exercise21101FutureBlockCylinderOwner_comp_activeCoordinates
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) (I : Finset ℕ) :
    exercise21101FutureBlockCylinderOwner P I ∘
        (fun ω (i : I) (j : Fin (partitionBoundIndex P i 1)) ↦
          exercise21101FutureBlockArray W P n ω i j)
      =
        fun ω (i : I) ↦ exercise21101FutureBlockArray W P n ω i := by
  -- Proof comment: outside the active range every future-block row is already `0`, so the
  -- finite active coordinates determine the full selected-row tuple.
  funext ω i k
  by_cases hk : k < partitionBoundIndex P i 1
  · simp [exercise21101FutureBlockCylinderOwner,
      exercise21101FutureBlockRowOfActiveCoordinates, hk]
  · simp [exercise21101FutureBlockCylinderOwner,
      exercise21101FutureBlockRowOfActiveCoordinates, exercise21101FutureBlockArray, hk]

/-- Helper for Exercise 21.10.1: the preimage of a measurable cylinder under the future-block
array already factors through the finite family of active coordinates on its selected rows. -/
lemma exercise21101FutureBlockArray_cylinderPreimage_eq_activeCoordinatesPreimage
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) {C : Set (ℕ → ℕ → ℝ)}
    (hC : C ∈ MeasureTheory.measurableCylinders (fun _ : ℕ ↦ ℕ → ℝ)) :
    ∃ I : Finset ℕ, ∃ U : Set ((i : I) → ℕ → ℝ), MeasurableSet U ∧
      (exercise21101FutureBlockArray W P n) ⁻¹' C =
        (fun ω (i : I) (j : Fin (partitionBoundIndex P i 1)) ↦
          exercise21101FutureBlockArray W P n ω i j) ⁻¹'
            ((exercise21101FutureBlockCylinderOwner P I) ⁻¹' U) := by
  let I : Finset ℕ := MeasureTheory.measurableCylinders.finset hC
  let U : Set ((i : I) → ℕ → ℝ) := MeasureTheory.measurableCylinders.set hC
  refine ⟨I, U, MeasureTheory.measurableCylinders.measurableSet hC, ?_⟩
  rw [MeasureTheory.measurableCylinders.eq_cylinder hC]
  calc
    (exercise21101FutureBlockArray W P n) ⁻¹' MeasureTheory.cylinder I U
        = (fun ω (i : I) ↦ exercise21101FutureBlockArray W P n ω i) ⁻¹' U := by
            ext ω
            simp [MeasureTheory.cylinder]
            have hrestrict :
                I.restrict (exercise21101FutureBlockArray W P n ω) =
                  (fun i : I ↦ exercise21101FutureBlockArray W P n ω i) := by
              funext i
              rfl
            rw [hrestrict]
    _ =
        (fun ω (i : I) (j : Fin (partitionBoundIndex P i 1)) ↦
          exercise21101FutureBlockArray W P n ω i j) ⁻¹'
            ((exercise21101FutureBlockCylinderOwner P I) ⁻¹' U) := by
          rw [← Set.preimage_comp]
          simp [exercise21101FutureBlockCylinderOwner_comp_activeCoordinates]

/-- Helper for Exercise 21.10.1: a measurable cylinder in the future-block array may be rewritten
directly as a measurable set on finitely many selected future rows. -/
lemma exercise21101FutureBlockArray_cylinderPreimage_eq_selectedRowsPreimage
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n : ℕ) {C : Set (ℕ → ℕ → ℝ)}
    (hC : C ∈ MeasureTheory.measurableCylinders (fun _ : ℕ ↦ ℕ → ℝ)) :
    ∃ I : Finset ℕ, ∃ U : Set ((i : I) → ℕ → ℝ), MeasurableSet U ∧
      (exercise21101FutureBlockArray W P n) ⁻¹' C =
        (fun ω (i : I) ↦ exercise21101FutureBlockArray W P n ω i) ⁻¹' U := by
  rcases exercise21101FutureBlockArray_cylinderPreimage_eq_activeCoordinatesPreimage
      (W := W) (P := P) (n := n) hC with
    ⟨I, U, hU_meas, hpre⟩
  refine ⟨I, U, hU_meas, ?_⟩
  calc
    (exercise21101FutureBlockArray W P n) ⁻¹' C
        =
          (fun ω (i : I) (j : Fin (partitionBoundIndex P i 1)) ↦
            exercise21101FutureBlockArray W P n ω i j) ⁻¹'
            ((exercise21101FutureBlockCylinderOwner P I) ⁻¹' U) := hpre
    _ = (fun ω (i : I) ↦ exercise21101FutureBlockArray W P n ω i) ⁻¹' U := by
          rw [← Set.preimage_comp]
          simp [exercise21101FutureBlockCylinderOwner_comp_activeCoordinates]

/-- Helper for Exercise 21.10.1: later future-block stages are obtained by masking earlier ones. -/
lemma exercise21101FutureBlockArray_eq_mask
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {n m : ℕ} (hnm : n ≤ m) :
    exercise21101FutureBlockArray W P m =
      fun ω ↦ exercise21101FutureBlockMask m (exercise21101FutureBlockArray W P n ω) := by
  -- Proof comment: once `n ≤ m`, the stage-`n` array already contains every stage-`m`
  -- coordinate, so stage `m` is exactly the row mask applied to stage `n`.
  funext ω r k
  by_cases hmr : m ≤ r
  · have hnr : n ≤ r := hnm.trans hmr
    by_cases hk : k < partitionBoundIndex P r 1
    · simp [exercise21101FutureBlockArray, exercise21101FutureBlockMask, hmr, hnr, hk]
    · simp [exercise21101FutureBlockArray, exercise21101FutureBlockMask, hmr, hnr, hk]
  · simp [exercise21101FutureBlockArray, exercise21101FutureBlockMask, hmr]

/-- Helper for Exercise 21.10.1: the decreasing future-block filtration generated by the zero-
padded arrays of centered block contributions. -/
noncomputable def backwardQuadraticVariationTailFiltration
    (W : NNReal → Ω → ℝ) (hW_meas : ∀ t, StronglyMeasurable (W t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    Filtration ℕᵒᵈ ‹MeasurableSpace Ω› where
  seq i :=
    MeasurableSpace.comap (exercise21101FutureBlockArray W P (ofDual i)) MeasurableSpace.pi
  mono' := by
    intro i j hij
    have hji : ofDual j ≤ ofDual i := hij
    refine measurable_iff_comap_le.1 ?_
    rw [exercise21101FutureBlockArray_eq_mask W P hji]
    exact (exercise21101FutureBlockMask_measurable (ofDual i)).comp
      (measurable_iff_comap_le.2 le_rfl)
  le' := by
    intro i
    exact measurable_iff_comap_le.1
      (exercise21101FutureBlockArray_measurable W hW_meas P (ofDual i))

/-- Helper for Exercise 21.10.1: each stage `Yₙ` is strongly measurable with respect to the
future-block filtration at reverse time `toDual n`. -/
lemma backwardProcess_stageStronglyMeasurable
    (W : NNReal → Ω → ℝ) (hW_meas : ∀ t, StronglyMeasurable (W t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    StronglyMeasurable[(backwardQuadraticVariationTailFiltration W hW_meas P) (toDual n)]
      (exercise21101BackwardProcess W P (toDual n)) := by
  -- Proof comment: each row-`n` summand is literally one coordinate of the stage-`n`
  -- future-block array, and finite sums preserve strong measurability.
  change StronglyMeasurable[
      MeasurableSpace.comap (exercise21101FutureBlockArray W P n) MeasurableSpace.pi]
    (fun ω ↦
      Finset.sum (Finset.range (partitionBoundIndex P n 1)) fun k ↦
        ((W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ) -
          (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))))
  refine (Finset.measurable_sum _ fun k hk => ?_).stronglyMeasurable
  have hcoord :
      Measurable[
        MeasurableSpace.comap (exercise21101FutureBlockArray W P n) MeasurableSpace.pi]
        (fun ω ↦ exercise21101FutureBlockArray W P n ω n k) := by
    -- Proof comment: project the stage-`n` array to the fixed row-`n`, index-`k` coordinate.
    have hcoordBase : Measurable (fun x : ℕ → ℕ → ℝ ↦ x n k) := by
      have hrowBase : Measurable (fun x : ℕ → ℕ → ℝ ↦ (x n : ℕ → ℝ)) :=
        measurable_pi_apply n
      exact (measurable_pi_apply k).comp hrowBase
    exact hcoordBase.comp (measurable_iff_comap_le.2 le_rfl)
  have hk_lt : k < partitionBoundIndex P n 1 := Finset.mem_range.mp hk
  have hcoord_eq :
      (fun ω ↦ exercise21101FutureBlockArray W P n ω n k) =
        (fun ω ↦
          ((W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ) -
            (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)))) := by
    -- Proof comment: on row `n` and inside the active range, the zero padding disappears.
    funext ω
    simp [exercise21101FutureBlockArray, hk_lt, exercise21101BlockContribution]
  rw [← hcoord_eq]
  exact hcoord

/-- Helper for Exercise 21.10.1: negate exactly the coordinates indexed by `J` in a finite real
vector. -/
noncomputable def exercise21101SubtreeNeg {n : ℕ} (J : Finset (Fin n)) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fun z i ↦ if i ∈ J then -z i else z i

/-- Helper for Exercise 21.10.1: the finite-coordinate sign flip is its own inverse. -/
lemma exercise21101SubtreeNeg_involutive
    {n : ℕ} (J : Finset (Fin n)) :
    Function.Involutive (exercise21101SubtreeNeg J) := by
  -- Proof comment: every flipped coordinate is negated twice, and every other coordinate is
  -- unchanged.
  intro z
  funext i
  by_cases hi : i ∈ J
  · simp [exercise21101SubtreeNeg, hi]
  · simp [exercise21101SubtreeNeg, hi]

/-- Helper for Exercise 21.10.1: the finite-coordinate sign flip is measurable. -/
lemma exercise21101SubtreeNeg_measurable
    {n : ℕ} (J : Finset (Fin n)) :
    Measurable (exercise21101SubtreeNeg J) := by
  -- Proof comment: each output coordinate is either the input coordinate or its negation.
  refine measurable_pi_lambda _ fun i ↦ ?_
  have hcoord :
      (fun z : Fin n → ℝ ↦ exercise21101SubtreeNeg J z i) =
        (if i ∈ J then (fun z : Fin n → ℝ ↦ -z i) else fun z : Fin n → ℝ ↦ z i) := by
    funext z
    by_cases hi : i ∈ J
    · simp [exercise21101SubtreeNeg, hi]
    · simp [exercise21101SubtreeNeg, hi]
  rw [hcoord]
  by_cases hi : i ∈ J
  · rw [if_pos hi]
    exact measurable_neg.comp (measurable_pi_apply i : Measurable (fun z : Fin n → ℝ ↦ z i))
  · rw [if_neg hi]
    exact (measurable_pi_apply i : Measurable (fun z : Fin n → ℝ ↦ z i))

/-- Helper for Exercise 21.10.1: if every index in a finite sum belongs to the flipped subtree,
then the whole sum changes sign. -/
lemma exercise21101SubtreeNeg_sum_eq_neg_sum_of_subset
    {n : ℕ} (J I : Finset (Fin n)) (hI : I ⊆ J) (z : Fin n → ℝ) :
    Finset.sum I (fun q ↦ exercise21101SubtreeNeg J z q) = -Finset.sum I z := by
  -- Proof comment: every summand lies in the flipped subtree, so each coordinate contributes one
  -- minus sign.
  calc
    Finset.sum I (fun q ↦ exercise21101SubtreeNeg J z q) = Finset.sum I (fun q ↦ -z q) := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      have hqJ : q ∈ J := hI hq
      simp [exercise21101SubtreeNeg, hqJ]
    _ = -Finset.sum I z := by
      simp

/-- Helper for Exercise 21.10.1: if a finite sum is indexed by coordinates disjoint from the
flipped subtree, then the sum is unchanged. -/
lemma exercise21101SubtreeNeg_sum_eq_sum_of_disjoint
    {n : ℕ} (J I : Finset (Fin n)) (hI : Disjoint I J) (z : Fin n → ℝ) :
    Finset.sum I (fun q ↦ exercise21101SubtreeNeg J z q) = Finset.sum I z := by
  -- Proof comment: outside the chosen subtree the coordinatewise sign flip acts trivially.
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hqJ : q ∉ J := by
    exact fun hq_mem ↦ Finset.disjoint_left.mp hI hq hq_mem
  simp [exercise21101SubtreeNeg, hqJ]

/-- Helper for Exercise 21.10.1: a centered squared interval sum is invariant under a subtree
sign flip whenever the whole interval is flipped or missed. -/
lemma exercise21101IntervalBlockContribution_fixedUnderSubtreeNeg
    {n : ℕ} (J I : Finset (Fin n)) (c : ℝ)
    (hI : I ⊆ J ∨ Disjoint I J) (z : Fin n → ℝ) :
    ((Finset.sum I (fun q ↦ exercise21101SubtreeNeg J z q)) ^ (2 : ℕ) - c) =
      ((Finset.sum I z) ^ (2 : ℕ) - c) := by
  -- Proof comment: the interval sum is either negated wholesale or fixed, and squaring removes
  -- that sign information.
  rcases hI with hsub | hdisj
  · rw [exercise21101SubtreeNeg_sum_eq_neg_sum_of_subset J I hsub z]
    ring
  · rw [exercise21101SubtreeNeg_sum_eq_sum_of_disjoint J I hdisj z]

/-- Helper for Exercise 21.10.1: a contiguous block of `len` coordinates starting at `a`
embeds into `Fin n` once its right endpoint stays within `n`. -/
noncomputable abbrev exercise21101ShiftedFinInclusion
    {n a len : ℕ} (h : a + len ≤ n) :
    Fin len → Fin n :=
  fun q ↦ ⟨a + q, lt_of_lt_of_le (Nat.add_lt_add_left q.is_lt a) h⟩

/-- Helper for Exercise 21.10.1: if a contiguous finite block lies inside the flipped subtree,
then its shifted coordinate sum changes sign. -/
lemma exercise21101SubtreeNeg_shiftedFinSum_eq_neg
    {n a len : ℕ} (J : Finset (Fin n)) (h : a + len ≤ n)
    (hmem : ∀ q : Fin len, exercise21101ShiftedFinInclusion h q ∈ J)
    (z : Fin n → ℝ) :
    (∑ q : Fin len, exercise21101SubtreeNeg J z (exercise21101ShiftedFinInclusion h q)) =
      -(∑ q : Fin len, z (exercise21101ShiftedFinInclusion h q)) := by
  -- Proof comment: every shifted coordinate lands in the flipped subtree, so each summand picks
  -- up a minus sign and the whole finite sum is negated.
  calc
    (∑ q : Fin len, exercise21101SubtreeNeg J z (exercise21101ShiftedFinInclusion h q)) =
        ∑ q : Fin len, -z (exercise21101ShiftedFinInclusion h q) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          simp [exercise21101SubtreeNeg, hmem q]
    _ = -(∑ q : Fin len, z (exercise21101ShiftedFinInclusion h q)) := by
          simp

/-- Helper for Exercise 21.10.1: if a contiguous finite block misses the flipped subtree, then
its shifted coordinate sum is unchanged. -/
lemma exercise21101SubtreeNeg_shiftedFinSum_eq
    {n a len : ℕ} (J : Finset (Fin n)) (h : a + len ≤ n)
    (hmem : ∀ q : Fin len, exercise21101ShiftedFinInclusion h q ∉ J)
    (z : Fin n → ℝ) :
    (∑ q : Fin len, exercise21101SubtreeNeg J z (exercise21101ShiftedFinInclusion h q)) =
      ∑ q : Fin len, z (exercise21101ShiftedFinInclusion h q) := by
  -- Proof comment: outside the chosen subtree the sign flip acts as the identity coordinatewise,
  -- so the shifted block sum stays fixed.
  refine Finset.sum_congr rfl ?_
  intro q hq
  simp [exercise21101SubtreeNeg, hmem q]

/-- Helper for Exercise 21.10.1: package the finite-coordinate sign flip as a measurable
equivalence so it can be fed directly into the symmetry integral lemmas. -/
noncomputable def exercise21101SubtreeNegEquiv {n : ℕ} (J : Finset (Fin n)) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  { toEquiv :=
      { toFun := exercise21101SubtreeNeg J
        invFun := exercise21101SubtreeNeg J
        left_inv := exercise21101SubtreeNeg_involutive J
        right_inv := exercise21101SubtreeNeg_involutive J }
    measurable_toFun := exercise21101SubtreeNeg_measurable J
    measurable_invFun := exercise21101SubtreeNeg_measurable J }

/-- Helper for Exercise 21.10.1: pushing a finite product law through the subtree sign flip acts
coordinatewise on the marginals. -/
lemma exercise21101Pi_map_subtreeNeg
    {n : ℕ} (ν : Fin n → Measure ℝ) [∀ i, SigmaFinite (ν i)]
    (J : Finset (Fin n)) :
    (Measure.pi ν).map (exercise21101SubtreeNeg J) =
      Measure.pi
        (fun i ↦ (ν i).map (if i ∈ J then (fun x : ℝ ↦ -x) else fun x : ℝ ↦ x)) := by
  let f : Fin n → ℝ → ℝ :=
    fun i ↦ if i ∈ J then (fun x : ℝ ↦ -x) else fun x : ℝ ↦ x
  have hf_ae : ∀ i : Fin n, AEMeasurable (f i) (ν i) := by
    intro i
    by_cases hi : i ∈ J
    · simpa [f, hi] using
        (measurable_neg.aemeasurable : AEMeasurable (fun x : ℝ ↦ -x) (ν i))
    · simpa [f, hi] using
        (measurable_id.aemeasurable : AEMeasurable (fun x : ℝ ↦ x) (ν i))
  letI : ∀ i : Fin n, SigmaFinite ((ν i).map (f i)) := by
    intro i
    by_cases hi : i ∈ J
    · simpa [f, hi] using
        ((MeasurableEquiv.neg ℝ).sigmaFinite_map (μ := ν i))
    · simpa [f, hi] using
        (show SigmaFinite (ν i) from inferInstance)
  have hsubtree :
      exercise21101SubtreeNeg J = fun z i ↦ f i (z i) := by
    -- Proof comment: both maps perform the same coordinatewise case split on membership in `J`.
    funext z i
    by_cases hi : i ∈ J
    · simp [exercise21101SubtreeNeg, f, hi]
    · simp [exercise21101SubtreeNeg, f, hi]
  rw [hsubtree, Measure.pi_map_pi hf_ae]

/-- Helper for Exercise 21.10.1: if each flipped marginal is invariant under negation, then the
whole finite product law is invariant under the subtree sign flip. -/
lemma exercise21101Pi_map_subtreeNeg_eq_self_of_map_neg_eq_self
    {n : ℕ} (ν : Fin n → Measure ℝ) [∀ i, SigmaFinite (ν i)]
    (J : Finset (Fin n))
    (hν : ∀ i, i ∈ J → (ν i).map (fun x : ℝ ↦ -x) = ν i) :
    (Measure.pi ν).map (exercise21101SubtreeNeg J) = Measure.pi ν := by
  -- Proof comment: the previous coordinatewise transport collapses because every flipped
  -- marginal is symmetric.
  rw [exercise21101Pi_map_subtreeNeg]
  congr 1
  funext i
  by_cases hi : i ∈ J
  · simpa [hi] using hν i hi
  · simp [hi]

/-- Helper for Exercise 21.10.1: a finite product of centered Gaussian laws is invariant under
negating any chosen coordinate subset. -/
lemma exercise21101GaussianPi_map_subtreeNeg_eq_self
    {n : ℕ} (v : Fin n → NNReal) (J : Finset (Fin n)) :
    (Measure.pi (fun i : Fin n ↦ gaussianReal (0 : ℝ) (v i))).map
        (exercise21101SubtreeNeg J)
      =
        Measure.pi (fun i : Fin n ↦ gaussianReal (0 : ℝ) (v i)) := by
  -- Proof comment: each centered Gaussian marginal is symmetric under negation, so the generic
  -- product symmetry lemma applies coordinatewise.
  refine exercise21101Pi_map_subtreeNeg_eq_self_of_map_neg_eq_self
    (ν := fun i : Fin n ↦ gaussianReal (0 : ℝ) (v i)) J ?_
  intro i hi
  simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := v i)

/-- Helper for Exercise 21.10.1: if a measurable equivalence preserves the law and flips the sign
of an integrand, then that integrand has mean `0`. -/
lemma exercise21101Integral_eq_zero_of_map_equiv_eq_self_of_anti
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (e : α ≃ᵐ α)
    {f : α → ℝ}
    (hν : ν.map e = ν)
    (hf_int : Integrable f ν)
    (hf_anti : ∀ z : α, f (e z) = -f z) :
    ∫ z, f z ∂ν = 0 := by
  have hf_comp : Integrable (fun z : α ↦ f (e z)) ν := by
    -- Proof comment: the anti-invariance turns the transported integrand into `-f`, so
    -- integrability is inherited from the original function.
    have hcomp :
        (fun z : α ↦ f (e z)) = (fun z : α ↦ -(f z)) := by
      funext z
      simp [hf_anti]
    rw [hcomp]
    exact hf_int.neg
  have hf_map : Integrable f (ν.map e) := by
    exact (integrable_map_equiv (μ := ν) e f).2 hf_comp
  have hmap :
      ∫ z, f z ∂ν.map e = -∫ z, f z ∂ν := by
    -- Proof comment: transport the integral through the symmetry `e` and rewrite the reflected
    -- integrand by the anti-invariance hypothesis.
    calc
      ∫ z, f z ∂ν.map e = ∫ z, f (e z) ∂ν := by
          simpa using (integral_map_equiv (μ := ν) e f)
      _ = ∫ z, -(f z) ∂ν := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            simp [hf_anti]
      _ = -∫ z, f z ∂ν := by
            rw [integral_neg]
  let _ := hf_map
  have hself : ∫ z, f z ∂ν = -∫ z, f z ∂ν := by
    -- Proof comment: the symmetry hypothesis identifies the pushed-forward law with the
    -- original one.
    simpa [hν] using hmap
  linarith

/-- Helper for Exercise 21.10.1: if a measurable equivalence preserves the law, fixes an owner
map, and flips the sign of the integrand, then the integrand still has zero mean on owner
preimages. -/
lemma exercise21101Integral_indicator_preimage_eq_zero_of_map_equiv_eq_self
    {α β : Type*} [MeasurableSpace α] (ν : Measure α) (e : α ≃ᵐ α)
    {owner : α → β} {S : Set β} {f : α → ℝ}
    (hν : ν.map e = ν)
    (howner_fixed : ∀ z : α, owner (e z) = owner z)
    (hf_anti : ∀ z : α, f (e z) = -f z)
    (hf_int : Integrable (Set.indicator (owner ⁻¹' S) f) ν) :
    ∫ z, Set.indicator (owner ⁻¹' S) f z ∂ν = 0 := by
  -- Proof comment: the indicator of an invariant preimage preserves anti-invariance, so the
  -- general symmetry lemma applies directly to the truncated integrand.
  refine exercise21101Integral_eq_zero_of_map_equiv_eq_self_of_anti ν e hν hf_int ?_
  intro z
  by_cases hz : z ∈ owner ⁻¹' S
  · have hez : e z ∈ owner ⁻¹' S := by
      simpa [Set.mem_preimage, howner_fixed z] using hz
    simp [Set.indicator_of_mem, hz, hez, hf_anti]
  · have hez : e z ∉ owner ⁻¹' S := by
      intro hez
      apply hz
      simpa [Set.mem_preimage, howner_fixed z] using hez
    simp [Set.indicator, hz, hez]

/-- Helper for Exercise 21.10.1: an odd integrand on a finite real vector space has mean `0`
under any law invariant under global negation. -/
lemma exercise21101Integral_eq_zero_of_map_neg_eq_self_of_odd
    {n : ℕ} (ν : Measure (Fin n → ℝ))
    {f : (Fin n → ℝ) → ℝ}
    (hν : ν.map (fun z : Fin n → ℝ ↦ -z) = ν)
    (hf_int : Integrable f ν)
    (hf_odd : ∀ z : Fin n → ℝ, f (-z) = -f z) :
    ∫ z, f z ∂ν = 0 := by
  -- Proof comment: this is the global-negation specialization of the measurable-equivalence
  -- symmetry lemma above.
  simpa using
    (exercise21101Integral_eq_zero_of_map_equiv_eq_self_of_anti
      (ν := ν) (e := MeasurableEquiv.neg (Fin n → ℝ)) hν hf_int hf_odd)

/-- Helper for Exercise 21.10.1: an odd integrand still has zero integral on every preimage of a
set under an even owner map, provided the law is invariant under global negation. -/
lemma exercise21101Integral_indicator_preimage_eq_zero_of_map_neg_eq_self
    {n : ℕ} {α : Type*} (ν : Measure (Fin n → ℝ))
    {owner : (Fin n → ℝ) → α} {S : Set α} {f : (Fin n → ℝ) → ℝ}
    (hν : ν.map (fun z : Fin n → ℝ ↦ -z) = ν)
    (howner_even : ∀ z : Fin n → ℝ, owner (-z) = owner z)
    (hf_odd : ∀ z : Fin n → ℝ, f (-z) = -f z)
    (hf_int : Integrable (Set.indicator (owner ⁻¹' S) f) ν) :
    ∫ z, Set.indicator (owner ⁻¹' S) f z ∂ν = 0 := by
  -- Proof comment: this is the global-negation specialization of the owner-preimage symmetry
  -- lemma above.
  simpa using
    (exercise21101Integral_indicator_preimage_eq_zero_of_map_equiv_eq_self
      (ν := ν) (e := MeasurableEquiv.neg (Fin n → ℝ)) hν howner_even hf_odd hf_int)

/-- Helper for Exercise 21.10.1: a finite centered-Gaussian product law kills any integrand that
is odd under a subtree sign flip while the owner is fixed by the same flip. -/
lemma exercise21101Integral_indicator_preimage_eq_zero_of_gaussianPi_subtreeNeg
    {n : ℕ} {α : Type*} [MeasurableSpace α]
    (v : Fin n → NNReal) (J : Finset (Fin n))
    {owner : (Fin n → ℝ) → α} {S : Set α} {f : (Fin n → ℝ) → ℝ}
    (howner_fixed : ∀ z : Fin n → ℝ, owner (exercise21101SubtreeNeg J z) = owner z)
    (hf_anti : ∀ z : Fin n → ℝ, f (exercise21101SubtreeNeg J z) = -f z)
    (hf_int :
      Integrable
        (Set.indicator (owner ⁻¹' S) f)
        (Measure.pi (fun i : Fin n ↦ gaussianReal (0 : ℝ) (v i)))) :
    ∫ z, Set.indicator (owner ⁻¹' S) f z
        ∂(Measure.pi (fun i : Fin n ↦ gaussianReal (0 : ℝ) (v i))) = 0 := by
  -- Proof comment: package the subtree sign flip as a measurable equivalence and feed the
  -- centered-Gaussian product symmetry into the general indicator-preimage lemma.
  refine exercise21101Integral_indicator_preimage_eq_zero_of_map_equiv_eq_self
    (ν := Measure.pi (fun i : Fin n ↦ gaussianReal (0 : ℝ) (v i)))
    (e := exercise21101SubtreeNegEquiv J)
    ?_ howner_fixed hf_anti hf_int
  simpa using exercise21101GaussianPi_map_subtreeNeg_eq_self v J

/-- Helper for Exercise 21.10.1: one packaged descendant summand already factors through the
active descendant increment vector on row `n + 1`, and it is odd under flipping exactly the
current descendant coordinate. -/
lemma exercise21101DescendantCrossSummand_factorThroughActiveDescendantVector
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i r : ℕ)
    (hr :
      r <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    ∃ f :
        (Fin
          (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
            exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) → ℝ) → ℝ,
      exercise21101DescendantCrossSummand W P n i r =
        f ∘
          exercise21101RowSegmentIncrementVector W P (n + 1)
            (exercise21101CoarseEndpointRefinementIndex P n i (n + 1))
            (partitionNextPointUpTo P n i 1) ∧
      ∀ z,
        f
            (exercise21101SubtreeNeg
              ({⟨r, hr⟩} :
                Finset
                  (Fin
                    (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
                      exercise21101CoarseEndpointRefinementIndex P n i (n + 1))))
              z) =
          -f z := by
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let count := partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) - start
  let f : (Fin count → ℝ) → ℝ := fun z ↦
    2 * (∑ s : Fin r, z (Fin.castLT s (lt_trans s.is_lt hr))) * z ⟨r, hr⟩
  refine ⟨f, ?_, ?_⟩
  · -- Proof comment: unfolding the row-segment vector shows that the packaged summand already is
    -- the expected polynomial in the active descendant coordinates.
    funext ω
    let child : ℕ → ℝ := fun s ↦
      W (partitionNextPointUpTo P (n + 1) (start + s) (partitionNextPointUpTo P n i 1)) ω -
        W (P (n + 1) (start + s)) ω
    rw [exercise21101DescendantCrossSummand]
    change 2 * (Finset.sum (Finset.range r) child) * child r =
      2 * (∑ s : Fin r, child s) * child r
    rw [Fin.sum_univ_eq_sum_range]
  · -- Proof comment: the singleton subtree flip touches only the current descendant coordinate,
    -- leaving every earlier prefix coordinate fixed and negating the current factor.
    intro z
    have hprefix :
        (∑ s : Fin r,
            exercise21101SubtreeNeg ({⟨r, hr⟩} : Finset (Fin count)) z
              (Fin.castLT s (lt_trans s.is_lt hr))) =
          ∑ s : Fin r, z (Fin.castLT s (lt_trans s.is_lt hr)) := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      have hs_ne :
          (Fin.castLT s (lt_trans s.is_lt hr) : Fin count) ≠ ⟨r, hr⟩ := by
        intro hsr
        exact (Nat.ne_of_lt s.is_lt) (congrArg Fin.val hsr)
      simp [exercise21101SubtreeNeg, Finset.mem_singleton, hs_ne]
    have hcurrent :
        exercise21101SubtreeNeg ({⟨r, hr⟩} : Finset (Fin count)) z ⟨r, hr⟩ = -z ⟨r, hr⟩ := by
      simp [exercise21101SubtreeNeg, Finset.mem_singleton]
    simp only [f]
    rw [hprefix, hcurrent]
    ring

/-- Helper for Exercise 21.10.1: on a common refinement row `M`, the chosen descendant block is
represented by the finite set of atomic coordinates lying between its copied endpoints. -/
noncomputable def exercise21101DescendantSubtreeIndices
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i r M : ℕ) :
    Finset (Fin (partitionBoundIndex P M 1)) :=
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let childStart := exercise21101CoarseEndpointRefinementIndex P (n + 1) (start + r) M
  let childStop :=
    partitionBoundIndex P M
      (partitionNextPointUpTo P (n + 1) (start + r) (partitionNextPointUpTo P n i 1))
  Finset.univ.filter fun q ↦ childStart ≤ (q : ℕ) ∧ (q : ℕ) < childStop

/-- Helper for Exercise 21.10.1: copied refinement indices preserve the order of the original
partition points. -/
lemma exercise21101CoarseEndpointRefinementIndex_mono
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {m i j M : ℕ} (hmM : m ≤ M) (hij : i ≤ j) :
    exercise21101CoarseEndpointRefinementIndex P m i M ≤
      exercise21101CoarseEndpointRefinementIndex P m j M := by
  -- Proof comment: both copied indices represent the original row-`m` endpoints on the finer row
  -- `M`, so strict monotonicity of row `M` forces their order to match the order on row `m`.
  by_contra h
  have hji :
      exercise21101CoarseEndpointRefinementIndex P m j M <
        exercise21101CoarseEndpointRefinementIndex P m i M :=
    lt_of_not_ge h
  have hlt_M :
      P M (exercise21101CoarseEndpointRefinementIndex P m j M) <
        P M (exercise21101CoarseEndpointRefinementIndex P m i M) :=
    (hP.strictMono M) hji
  rw [exercise21101CoarseEndpointRefinementIndex_spec P m j M hmM,
    exercise21101CoarseEndpointRefinementIndex_spec P m i M hmM] at hlt_M
  exact (not_lt_of_ge ((hP.strictMono m).monotone hij)) hlt_M

/-- Helper for Exercise 21.10.1: away from the terminal active block, transporting the clipped
right endpoint of a row-`m` block to a finer row `M` just copies the next row-`m` endpoint. -/
lemma exercise21101NextPointBound_eq_coarseEndpointRefinementIndex
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {m j M : ℕ} (hmM : m ≤ M) (hj : j + 1 < partitionBoundIndex P m 1) :
    partitionBoundIndex P M (partitionNextPointUpTo P m j 1) =
      exercise21101CoarseEndpointRefinementIndex P m (j + 1) M := by
  -- Proof comment: in the nonterminal case, the clipped right endpoint is exactly the next
  -- partition point on row `m`, and copied endpoints are recovered by `partitionBoundIndex`.
  have hnext :
      partitionNextPointUpTo P m j 1 = P m (j + 1) :=
    exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex P m j 1 hj
  have hspec :
      P M (exercise21101CoarseEndpointRefinementIndex P m (j + 1) M) = P m (j + 1) :=
    exercise21101CoarseEndpointRefinementIndex_spec P m (j + 1) M hmM
  rw [hnext, ← hspec, exercise21101_partitionBoundIndex_eq_of_partitionPoint]

/-- Helper for Exercise 21.10.1: if one copied atomic interval lies inside another, then every
shifted coordinate from the smaller range belongs to the larger interval finset. -/
lemma exercise21101Mem_descendantSubtreeIndices_of_shiftedIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {n i r M a b : ℕ}
    (hab : a ≤ b)
    (hb1 : b ≤ partitionBoundIndex P M 1)
    (hleft :
      exercise21101CoarseEndpointRefinementIndex P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r) M ≤ a)
    (hright :
      b ≤ partitionBoundIndex P M
        (partitionNextPointUpTo P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
          (partitionNextPointUpTo P n i 1)))
    {s : ℕ} (hs : s < b - a) :
    (⟨a + s, by
      have hlt_b : a + s < b := by
        calc
          a + s < a + (b - a) := Nat.add_lt_add_left hs a
          _ = b := Nat.add_sub_of_le hab
      exact lt_of_lt_of_le hlt_b hb1⟩ :
      Fin (partitionBoundIndex P M 1))
      ∈ exercise21101DescendantSubtreeIndices P n i r M := by
  -- Proof comment: the shifted index lands between the copied subtree endpoints because the whole
  -- transported block interval sits inside those endpoints.
  simp [exercise21101DescendantSubtreeIndices]
  constructor
  · exact le_trans hleft (Nat.le_add_right a s)
  · have hlt_b : a + s < b := by
      calc
        a + s < a + (b - a) := Nat.add_lt_add_left hs a
        _ = b := Nat.add_sub_of_le hab
    exact lt_of_lt_of_le hlt_b hright

/-- Helper for Exercise 21.10.1: if a copied atomic interval lies entirely before or after the
descendant subtree interval, then every shifted coordinate from that interval misses the subtree
finset. -/
lemma exercise21101NotMem_descendantSubtreeIndices_of_shiftedIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {n i r M a b : ℕ}
    (hab : a ≤ b)
    (hb1 : b ≤ partitionBoundIndex P M 1)
    (hsep :
      b ≤ exercise21101CoarseEndpointRefinementIndex P (n + 1)
            (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r) M ∨
        partitionBoundIndex P M
            (partitionNextPointUpTo P (n + 1)
              (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r)
              (partitionNextPointUpTo P n i 1))
          ≤ a)
    {s : ℕ} (hs : s < b - a) :
    (⟨a + s, by
      have hlt_b : a + s < b := by
        calc
          a + s < a + (b - a) := Nat.add_lt_add_left hs a
          _ = b := Nat.add_sub_of_le hab
      exact lt_of_lt_of_le hlt_b hb1⟩ :
      Fin (partitionBoundIndex P M 1))
      ∉ exercise21101DescendantSubtreeIndices P n i r M := by
  -- Proof comment: the shifted index is either strictly before the copied subtree start or at/after
  -- the copied subtree stop, so it cannot satisfy the interval-membership predicate.
  intro hmem
  simp [exercise21101DescendantSubtreeIndices] at hmem
  rcases hsep with hbefore | hafter
  · have hlt_b : a + s < b := by
      calc
        a + s < a + (b - a) := Nat.add_lt_add_left hs a
        _ = b := Nat.add_sub_of_le hab
    exact not_le_of_gt hlt_b (le_trans hbefore hmem.1)
  · exact
      not_lt_of_ge (le_trans hafter (Nat.le_add_right a s)) hmem.2

/-- Helper for Exercise 21.10.1: every copied prefix descendant block ends no later than the
copied start of the current descendant block on any finer common row. -/
lemma exercise21101CopiedDescendantPrefixBlock_right_le_currentStart
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {n i r s M : ℕ} (hnM : n + 1 ≤ M)
    (hr :
      r <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1))
    (hs : s < r) :
    partitionBoundIndex P M
        (partitionNextPointUpTo P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
          (partitionNextPointUpTo P n i 1))
      ≤
        exercise21101CoarseEndpointRefinementIndex P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + r) M := by
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let coarseRight := partitionNextPointUpTo P n i 1
  have hs_succ :
      s + 1 <
        partitionBoundIndex P (n + 1) coarseRight - start := by
    exact lt_of_le_of_lt (Nat.succ_le_of_lt hs) (by simpa [start, coarseRight] using hr)
  have hstart_le :
      start ≤ partitionBoundIndex P (n + 1) coarseRight := by
    have hstart_lt :
        start < partitionBoundIndex P (n + 1) coarseRight := by
      -- Proof comment: the existence of the current descendant index forces the copied coarse
      -- left endpoint to lie strictly before the descendant boundary on row `n + 1`.
      omega
    exact Nat.le_of_lt hstart_lt
  have hs_active :
      start + (s + 1) < partitionBoundIndex P (n + 1) coarseRight := by
    calc
      start + (s + 1) < start +
          (partitionBoundIndex P (n + 1) coarseRight - start) := by
            exact Nat.add_lt_add_left hs_succ start
      _ = partitionBoundIndex P (n + 1) coarseRight := by
            rw [Nat.add_sub_of_le hstart_le]
  have hprefix_eq :
      partitionNextPointUpTo P (n + 1) (start + s) coarseRight =
        P (n + 1) (start + (s + 1)) := by
    exact
      exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
        P (n + 1) (start + s) coarseRight (by simpa [Nat.add_assoc] using hs_active)
  have htime :
      partitionNextPointUpTo P (n + 1) (start + s) coarseRight ≤
        P (n + 1) (start + r) := by
    rw [hprefix_eq]
    exact (hP.strictMono (n + 1)).monotone <|
      by simpa [Nat.add_assoc] using Nat.add_le_add_left (Nat.succ_le_of_lt hs) start
  have hcurrent_eq :
      partitionBoundIndex P M (P (n + 1) (start + r)) =
        exercise21101CoarseEndpointRefinementIndex P (n + 1) (start + r) M := by
    rw [← exercise21101CoarseEndpointRefinementIndex_spec P (n + 1) (start + r) M hnM,
      exercise21101_partitionBoundIndex_eq_of_partitionPoint]
  -- Proof comment: the prefix child's copied right endpoint is the copied occurrence of a row
  -- `n + 1` partition point that lies at or before the current child's left endpoint.
  simpa [start, coarseRight, hcurrent_eq] using
    (exercise21101PartitionBoundIndex_mono P M htime)

/-- Helper for Exercise 21.10.1: transporting one active row-`m` block to any finer row `M`
rewrites its increment as the sum of the copied row-`M` atomic increments. -/
lemma exercise21101FutureBlockIncrement_eq_sum_fineRowAtomicIncrements
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {m M j : ℕ} (hmM : m ≤ M) (hj : j < partitionBoundIndex P m 1) :
    let a := exercise21101CoarseEndpointRefinementIndex P m j M
    let b := partitionBoundIndex P M (partitionNextPointUpTo P m j 1)
    (fun ω ↦ W (partitionNextPointUpTo P m j 1) ω - W (P m j) ω) =
      fun ω ↦
        Finset.sum (Finset.range (b - a)) fun s ↦
          (W (partitionNextPointUpTo P M (a + s) 1) ω - W (P M (a + s)) ω) := by
  let a := exercise21101CoarseEndpointRefinementIndex P m j M
  let b := partitionBoundIndex P M (partitionNextPointUpTo P m j 1)
  have ha_lt_m : P m j < (1 : NNReal) := by
    -- Proof comment: an active row-`m` block starts strictly before the horizon `1`.
    exact exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P m j 1 hj
  have ha : a < partitionBoundIndex P M 1 := by
    -- Proof comment: the copied left endpoint remains strictly before the horizon-`1` boundary
    -- on every finer row.
    simpa [a] using
      exercise21101CoarseEndpointRefinementIndex_lt_partitionBoundIndex
        P m j M hmM 1 ha_lt_m
  by_cases hnext : j + 1 < partitionBoundIndex P m 1
  · have hright :
        partitionNextPointUpTo P m j 1 = P m (j + 1) := by
      -- Proof comment: away from the final active block, clipping at `1` leaves the genuine next
      -- coarse endpoint unchanged.
      exact
        exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
          P m j 1 hnext
    have hb :
        b = exercise21101CoarseEndpointRefinementIndex P m (j + 1) M := by
      -- Proof comment: on the finer row, the transported right endpoint is exactly the copied
      -- occurrence of the next coarse partition point.
      show partitionBoundIndex P M (partitionNextPointUpTo P m j 1) =
          exercise21101CoarseEndpointRefinementIndex P m (j + 1) M
      rw [hright]
      rw [← exercise21101CoarseEndpointRefinementIndex_spec P m (j + 1) M hmM]
      rw [exercise21101_partitionBoundIndex_eq_of_partitionPoint]
    have hb_lt_m : P m (j + 1) < (1 : NNReal) := by
      -- Proof comment: the copied right endpoint is still an active coarse point, hence also
      -- strictly before the horizon `1`.
      exact
        exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P m (j + 1) 1 hnext
    have hb_lt : b < partitionBoundIndex P M 1 := by
      -- Proof comment: the copied right endpoint remains strictly before the finer-row horizon
      -- boundary as well.
      rw [hb]
      exact
        exercise21101CoarseEndpointRefinementIndex_lt_partitionBoundIndex
          P m (j + 1) M hmM 1 hb_lt_m
    have hab : a ≤ b := by
      -- Proof comment: strict monotonicity of the finer row prevents the copied right endpoint
      -- from occurring before the copied left endpoint.
      by_contra hab
      have hba : b < a := lt_of_not_ge hab
      have hspec_a :
          P M a = P m j := by
        simpa [a] using exercise21101CoarseEndpointRefinementIndex_spec P m j M hmM
      have hspec_b :
          P M b = P m (j + 1) := by
        rw [hb]
        exact exercise21101CoarseEndpointRefinementIndex_spec P m (j + 1) M hmM
      have hlt_M : P M b < P M a := (hP.strictMono M) hba
      have hlt_m : P m j < P m (j + 1) := (hP.strictMono m) (Nat.lt_succ_self j)
      rw [hspec_b, hspec_a] at hlt_M
      exact (not_lt_of_gt hlt_m) hlt_M
    have hinc :=
      exercise21101PartitionPointIncrement_eq_sum_atomicIncrements W P M a b ha hab hb_lt
    have hspec_a :
        P M a = P m j := by
      simpa [a] using exercise21101CoarseEndpointRefinementIndex_spec P m j M hmM
    have hspec_b :
        P M b = partitionNextPointUpTo P m j 1 := by
      rw [show partitionNextPointUpTo P m j 1 = P m (j + 1) by exact hright]
      rw [hb]
      exact exercise21101CoarseEndpointRefinementIndex_spec P m (j + 1) M hmM
    calc
      (fun ω ↦ W (partitionNextPointUpTo P m j 1) ω - W (P m j) ω)
          = (fun ω ↦ W (P M b) ω - W (P M a) ω) := by
              -- Proof comment: replace the coarse endpoints by their copied occurrences on row
              -- `M`.
              funext ω
              simp [hspec_a, hspec_b]
      _ =
          (fun ω ↦
            Finset.sum (Finset.range (b - a)) fun s ↦
              (W (partitionNextPointUpTo P M (a + s) 1) ω - W (P M (a + s)) ω)) := hinc
  · have hlast :
        j + 1 = partitionBoundIndex P m 1 := by
      -- Proof comment: if the successor index is no longer active, the current block is the
      -- terminal active block on row `m`.
      exact le_antisymm (Nat.succ_le_of_lt hj) (Nat.le_of_not_gt hnext)
    have hright : partitionNextPointUpTo P m j 1 = 1 := by
      -- Proof comment: terminal active blocks clip exactly at the horizon `1`.
      rw [partitionNextPointUpTo, hlast, min_eq_right]
      exact le_partitionBoundIndex_time P m 1
    have hinc := exercise21101IncrementToOne_eq_sum_atomicIncrements W P M a ha
    calc
      (fun ω ↦ W (partitionNextPointUpTo P m j 1) ω - W (P m j) ω)
          = (fun ω ↦ W 1 ω - W (P M a) ω) := by
              -- Proof comment: in the terminal case, only the copied left endpoint has to be
              -- transported to row `M`.
              funext ω
              have hspec_a :
                  P M a = P m j := by
                simpa [a] using exercise21101CoarseEndpointRefinementIndex_spec P m j M hmM
              simp [hright, hspec_a]
      _ =
          (fun ω ↦
            Finset.sum
              (Finset.range (partitionBoundIndex P M 1 - a)) fun s ↦
                (W (partitionNextPointUpTo P M (a + s) 1) ω - W (P M (a + s)) ω)) := hinc
      _ =
          (fun ω ↦
            Finset.sum (Finset.range (b - a)) fun s ↦
              (W (partitionNextPointUpTo P M (a + s) 1) ω - W (P M (a + s)) ω)) := by
              simp [b, hright]

/-- Helper for Exercise 21.10.1: each valid row-`n + 1` descendant child increment can be
transported further to any common refinement row `M` as the sum of the copied row-`M` atomic
increments over that child interval. -/
lemma exercise21101CopiedDescendantChildIncrement_eq_sum_fineRowAtomicIncrements
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {n i s M : ℕ} (hnM : n + 1 ≤ M)
    (hs :
      s <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    let a := exercise21101CoarseEndpointRefinementIndex P (n + 1)
      (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s) M
    let b := partitionBoundIndex P M
      (partitionNextPointUpTo P (n + 1)
        (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
        (partitionNextPointUpTo P n i 1))
    (fun ω ↦
      W (partitionNextPointUpTo P (n + 1)
        (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
        (partitionNextPointUpTo P n i 1)) ω -
        W (P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)) ω)
      =
        fun ω ↦
          Finset.sum (Finset.range (b - a)) fun q ↦
            (W (partitionNextPointUpTo P M (a + q) 1) ω - W (P M (a + q)) ω) := by
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let coarseRight := partitionNextPointUpTo P n i 1
  let finish := partitionBoundIndex P (n + 1) coarseRight
  have hcount_pos : 0 < finish - start := by
    -- Proof comment: the descendant index hypothesis already says that the copied coarse block
    -- contains at least one row-`n + 1` child.
    exact lt_of_le_of_lt (Nat.zero_le s) hs
  have hstart_lt_finish : start < finish := by
    omega
  have hstart_spec :
      P (n + 1) start = P n i := by
    -- Proof comment: the copied coarse left endpoint on row `n + 1` is the original row-`n`
    -- left endpoint of the active coarse block.
    simpa [start] using
      exercise21101CoarseEndpointRefinementIndex_spec P n i (n + 1) (Nat.le_succ n)
  have hstart_lt_time : P n i < coarseRight := by
    -- Proof comment: a positive descendant range means the copied coarse left endpoint still lies
    -- strictly before the coarse clipped right endpoint.
    have hlt :
        P (n + 1) start < coarseRight := by
      exact exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P (n + 1) start
        coarseRight hstart_lt_finish
    simpa [hstart_spec] using hlt
  have hi : i < partitionBoundIndex P n 1 := by
    -- Proof comment: once the coarse left endpoint lies before `coarseRight ≤ 1`, the coarse
    -- block index `i` is active on row `n`.
    refine exercise21101_lt_partitionBoundIndex_of_partitionPoint_lt_time P n i 1 ?_
    exact lt_of_lt_of_le hstart_lt_time (by simp [coarseRight, partitionNextPointUpTo])
  have hs_active : start + s < finish := by
    -- Proof comment: the `s`-th descendant child starts before the row-`n + 1` boundary of the
    -- active coarse block.
    calc
      start + s < start + (finish - start) := Nat.add_lt_add_left hs start
      _ = finish := Nat.add_sub_of_le (Nat.le_of_lt hstart_lt_finish)
  have hfinish_le_one : finish ≤ partitionBoundIndex P (n + 1) 1 := by
    -- Proof comment: the coarse clipped right endpoint is bounded by `1`, so its row-`n + 1`
    -- boundary index is also bounded by the global horizon-`1` boundary index.
    exact exercise21101PartitionBoundIndex_mono P (n + 1) (by simp [coarseRight, partitionNextPointUpTo])
  have hj : start + s < partitionBoundIndex P (n + 1) 1 :=
    lt_of_lt_of_le hs_active hfinish_le_one
  have hclipped :
      partitionNextPointUpTo P (n + 1) (start + s) coarseRight =
        partitionNextPointUpTo P (n + 1) (start + s) 1 := by
    -- Proof comment: valid descendants sit fully inside the active coarse block, so clipping at
    -- the coarse right endpoint agrees with clipping at the global horizon `1`.
    simpa [start, coarseRight] using
      exercise21101Descendant_nextPointUpTo_eq_one P n i s hi hs
  have hinc :=
    exercise21101FutureBlockIncrement_eq_sum_fineRowAtomicIncrements
      (W := W) (P := P) (m := n + 1) (M := M) (j := start + s) hnM hj
  -- Proof comment: after normalizing the clipped right endpoint, this is exactly the generic
  -- row-`m` to row-`M` increment-transport lemma specialized to one descendant child.
  simpa [start, coarseRight, hclipped] using hinc

/-- Helper for Exercise 21.10.1: every valid copied descendant child occupies a nonempty interval
of common-row coordinates that still lies inside the horizon-`1` truncation range. -/
lemma exercise21101CopiedDescendantChild_bounds
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {n i s M : ℕ} (hnM : n + 1 ≤ M)
    (hs :
      s <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    let a := exercise21101CoarseEndpointRefinementIndex P (n + 1)
      (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s) M
    let b := partitionBoundIndex P M
      (partitionNextPointUpTo P (n + 1)
        (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
        (partitionNextPointUpTo P n i 1))
    a < b ∧ b ≤ partitionBoundIndex P M 1 := by
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let coarseRight := partitionNextPointUpTo P n i 1
  let finish := partitionBoundIndex P (n + 1) coarseRight
  let a := exercise21101CoarseEndpointRefinementIndex P (n + 1) (start + s) M
  let b := partitionBoundIndex P M
    (partitionNextPointUpTo P (n + 1) (start + s) coarseRight)
  have hstart_lt_finish : start < finish := by
    -- Proof comment: the existence of a valid descendant index forces the copied coarse left
    -- endpoint to lie strictly before the coarse-right boundary on row `n + 1`.
    have hdiff_pos : 0 < finish - start := lt_of_le_of_lt (Nat.zero_le s) hs
    exact Nat.sub_pos_iff_lt.mp hdiff_pos
  have hs_lt_finish : start + s < finish := by
    calc
      start + s < start + (finish - start) := Nat.add_lt_add_left hs start
      _ = finish := Nat.add_sub_of_le (Nat.le_of_lt hstart_lt_finish)
  have hleft_lt_time :
      P (n + 1) (start + s) < coarseRight := by
    -- Proof comment: a valid descendant child starts strictly before the coarse clipped right
    -- endpoint on row `n + 1`.
    exact exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P (n + 1) (start + s)
      coarseRight hs_lt_finish
  have hleft_lt_right :
      P (n + 1) (start + s) <
        partitionNextPointUpTo P (n + 1) (start + s) coarseRight := by
    -- Proof comment: the clipped right endpoint remains strictly to the right of the child start
    -- because the next row-`n + 1` point is also to the right and the clip still lies before the
    -- coarse-right boundary.
    rw [partitionNextPointUpTo]
    refine lt_min ?_ hleft_lt_time
    simpa using (hP.strictMono (n + 1)) (Nat.lt_succ_self (start + s))
  have ha_lt_b : a < b := by
    -- Proof comment: the copied start of the child stays strictly before the copied boundary of
    -- its clipped right endpoint on the common row `M`.
    simpa [a, b, start, coarseRight] using
      exercise21101CoarseEndpointRefinementIndex_lt_partitionBoundIndex
        P (n + 1) (start + s) M hnM
        (partitionNextPointUpTo P (n + 1) (start + s) coarseRight) hleft_lt_right
  have hb1 : b ≤ partitionBoundIndex P M 1 := by
    -- Proof comment: every copied descendant child still lies inside the global horizon `1`.
    refine exercise21101PartitionBoundIndex_mono P M ?_
    exact le_trans (min_le_right _ _) (by simp [coarseRight, partitionNextPointUpTo])
  simpa [a, b, start, coarseRight] using ⟨ha_lt_b, hb1⟩

/-- Helper for Exercise 21.10.1: a valid copied descendant child increment is exactly the sum of
the corresponding contiguous common-row coordinates of `exercise21101WholeRowIncrementVector`. -/
lemma exercise21101CopiedDescendantChildIncrement_eq_commonRowChildSum
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {n i s M : ℕ} (hnM : n + 1 ≤ M)
    (hs :
      s <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    let a := exercise21101CoarseEndpointRefinementIndex P (n + 1)
      (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s) M
    let b := partitionBoundIndex P M
      (partitionNextPointUpTo P (n + 1)
        (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
        (partitionNextPointUpTo P n i 1))
    (fun ω ↦
      W (partitionNextPointUpTo P (n + 1)
        (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
        (partitionNextPointUpTo P n i 1)) ω -
        W (P (n + 1)
          (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)) ω) =
      fun ω ↦
        ∑ q : Fin (b - a),
          exercise21101WholeRowIncrementVector W P M ω
            (exercise21101ShiftedFinInclusion
              (by
                have hbounds :=
                  exercise21101CopiedDescendantChild_bounds
                    (P := P) (n := n) (i := i) (s := s) (M := M) hnM hs
                have hab : a ≤ b := Nat.le_of_lt hbounds.1
                calc
                  a + (b - a) = b := Nat.add_sub_of_le hab
                  _ ≤ partitionBoundIndex P M 1 := hbounds.2)
              q) := by
  let a := exercise21101CoarseEndpointRefinementIndex P (n + 1)
    (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s) M
  let b := partitionBoundIndex P M
    (partitionNextPointUpTo P (n + 1)
      (exercise21101CoarseEndpointRefinementIndex P n i (n + 1) + s)
      (partitionNextPointUpTo P n i 1))
  have hsum :=
    exercise21101CopiedDescendantChildIncrement_eq_sum_fineRowAtomicIncrements
      (W := W) (P := P) (n := n) (i := i) (s := s) (M := M) hnM hs
  funext ω
  have hω := congrFun hsum ω
  have hvec :
      (∑ q : Fin (b - a),
          exercise21101WholeRowIncrementVector W P M ω
            (exercise21101ShiftedFinInclusion
              (by
                have hbounds :=
                  exercise21101CopiedDescendantChild_bounds
                    (P := P) (n := n) (i := i) (s := s) (M := M) hnM hs
                have hab : a ≤ b := Nat.le_of_lt hbounds.1
                calc
                  a + (b - a) = b := Nat.add_sub_of_le hab
                  _ ≤ partitionBoundIndex P M 1 := hbounds.2)
              q)) =
        Finset.sum (Finset.range (b - a)) fun q ↦
          (W (partitionNextPointUpTo P M (a + q) 1) ω - W (P M (a + q)) ω) := by
    calc
      (∑ q : Fin (b - a),
          exercise21101WholeRowIncrementVector W P M ω
            (exercise21101ShiftedFinInclusion
              (by
                have hbounds :=
                  exercise21101CopiedDescendantChild_bounds
                    (P := P) (n := n) (i := i) (s := s) (M := M) hnM hs
                have hab : a ≤ b := Nat.le_of_lt hbounds.1
                calc
                  a + (b - a) = b := Nat.add_sub_of_le hab
                  _ ≤ partitionBoundIndex P M 1 := hbounds.2)
              q))
          =
            ∑ q : Fin (b - a),
              (W (partitionNextPointUpTo P M (a + q) 1) ω - W (P M (a + q)) ω) := by
                refine Finset.sum_congr rfl ?_
                intro q hq
                simp [exercise21101WholeRowIncrementVector,
                  exercise21101RowSegmentIncrementVector, exercise21101ShiftedFinInclusion]
      _ = Finset.sum (Finset.range (b - a)) fun q ↦
            (W (partitionNextPointUpTo P M (a + q) 1) ω - W (P M (a + q)) ω) := by
              symm
              simpa using
                (Fin.sum_univ_eq_sum_range
                  (n := b - a)
                  (f := fun q : ℕ ↦
                    (W (partitionNextPointUpTo P M (a + q) 1) ω - W (P M (a + q)) ω))).symm
  -- Proof comment: the common-row vector coordinate is definitionally the copied row-`M` atomic
  -- increment, so only the indexing normal form changes.
  exact hω.trans hvec.symm

/-- Helper for Exercise 21.10.1: the centered contribution of one active row-`m` block may be
rewritten as the centered square of the corresponding copied fine-row atomic increment sum. -/
lemma exercise21101FutureBlockContribution_eq_sum_fineRowAtomicIncrements
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {m M j : ℕ} (hmM : m ≤ M) (hj : j < partitionBoundIndex P m 1) :
    let a := exercise21101CoarseEndpointRefinementIndex P m j M
    let b := partitionBoundIndex P M (partitionNextPointUpTo P m j 1)
    exercise21101BlockContribution W (P m j) (partitionNextPointUpTo P m j 1) =
      fun ω ↦
        ((Finset.sum (Finset.range (b - a)) fun s ↦
            (W (partitionNextPointUpTo P M (a + s) 1) ω - W (P M (a + s)) ω)) ^ (2 : ℕ) -
          (((partitionNextPointUpTo P m j 1 - P m j : NNReal) : ℝ))) := by
  let a := exercise21101CoarseEndpointRefinementIndex P m j M
  let b := partitionBoundIndex P M (partitionNextPointUpTo P m j 1)
  have hinc :=
    exercise21101FutureBlockIncrement_eq_sum_fineRowAtomicIncrements
      (W := W) (P := P) (hmM := hmM) (hj := hj)
  funext ω
  -- Proof comment: after transporting the underlying increment to row `M`, the centered square
  -- is just the defining polynomial of one block contribution.
  have hω := congrFun hinc ω
  simp [exercise21101BlockContribution, hω]

/-- Helper for Exercise 21.10.1: transporting an active row-`m` future block to a finer row `M`
produces a nonempty common-row interval that still lies inside the horizon-`1` truncation range.
-/
lemma exercise21101FutureBlock_commonRowBounds
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {m M j : ℕ} (hmM : m ≤ M) (hj : j < partitionBoundIndex P m 1) :
    let a := exercise21101CoarseEndpointRefinementIndex P m j M
    let b := partitionBoundIndex P M (partitionNextPointUpTo P m j 1)
    a < b ∧ b ≤ partitionBoundIndex P M 1 := by
  let a := exercise21101CoarseEndpointRefinementIndex P m j M
  let b := partitionBoundIndex P M (partitionNextPointUpTo P m j 1)
  have hleft_lt_right : P m j < partitionNextPointUpTo P m j 1 := by
    -- Proof comment: every active block starts strictly before its clipped right endpoint.
    by_cases hnext : j + 1 < partitionBoundIndex P m 1
    · rw [exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
        P m j 1 hnext]
      exact (hP.strictMono m) (Nat.lt_succ_self j)
    · have hlast : j + 1 = partitionBoundIndex P m 1 := by
        exact le_antisymm (Nat.succ_le_of_lt hj) (Nat.le_of_not_gt hnext)
      rw [partitionNextPointUpTo, hlast, min_eq_right]
      · exact exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex P m j 1 hj
      · exact le_partitionBoundIndex_time P m 1
  have ha_lt_b : a < b := by
    -- Proof comment: the copied left endpoint stays strictly before the copied right boundary on
    -- the common row `M`.
    simpa [a, b] using
      (exercise21101CoarseEndpointRefinementIndex_lt_partitionBoundIndex
        P m j M hmM (partitionNextPointUpTo P m j 1) hleft_lt_right)
  have hb1 : b ≤ partitionBoundIndex P M 1 := by
    -- Proof comment: clipping at time `1` keeps every transported future interval inside the
    -- global row-`M` horizon.
    refine exercise21101PartitionBoundIndex_mono P M ?_
    simp [partitionNextPointUpTo]
  simpa [a, b] using ⟨ha_lt_b, hb1⟩

/-- Helper for Exercise 21.10.1: the common-row length proof for a transported active future block
may be reused as the shifted-index embedding bound. -/
lemma exercise21101FutureBlock_commonRowLength_le
    (P : ℕ → ℕ → NNReal) [hP : IsAdmissiblePartitionSequence P]
    {m M j : ℕ} (hmM : m ≤ M) (hj : j < partitionBoundIndex P m 1) :
    let a := exercise21101CoarseEndpointRefinementIndex P m j M
    let b := partitionBoundIndex P M (partitionNextPointUpTo P m j 1)
    a + (b - a) ≤ partitionBoundIndex P M 1 := by
  let a := exercise21101CoarseEndpointRefinementIndex P m j M
  let b := partitionBoundIndex P M (partitionNextPointUpTo P m j 1)
  have hbounds := exercise21101FutureBlock_commonRowBounds
    (P := P) (m := m) (M := M) (j := j) hmM hj
  have hab : a ≤ b := Nat.le_of_lt hbounds.1
  calc
    a + (b - a) = b := Nat.add_sub_of_le hab
    _ ≤ partitionBoundIndex P M 1 := hbounds.2

/-- Helper for Exercise 21.10.1: on any row `m ≥ n + 1`, the right endpoint of an active
row-`m` future block lies wholly before, inside, or after the copied current descendant child. -/
lemma exercise21101FutureBlock_indexTrichotomyAgainstDescendantChild
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {n i r m j : ℕ} (hnm : n + 1 ≤ m)
    (hr :
      r <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
    let u := exercise21101CoarseEndpointRefinementIndex P (n + 1) (start + r) m
    let v := partitionBoundIndex P m
      (partitionNextPointUpTo P (n + 1) (start + r) (partitionNextPointUpTo P n i 1))
    j + 1 ≤ u ∨ (u ≤ j ∧ j + 1 ≤ v) ∨ v ≤ j := by
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let u := exercise21101CoarseEndpointRefinementIndex P (n + 1) (start + r) m
  let v := partitionBoundIndex P m
    (partitionNextPointUpTo P (n + 1) (start + r) (partitionNextPointUpTo P n i 1))
  have huv :
      u < v ∧ v ≤ partitionBoundIndex P m 1 := by
    -- Proof comment: the valid current descendant child still occupies a genuine interval on row
    -- `m`.
    simpa [start, u, v] using
      (exercise21101CopiedDescendantChild_bounds
        (P := P) (n := n) (i := i) (s := r) (M := m) hnm hr)
  by_cases hu : j + 1 ≤ u
  · exact Or.inl hu
  · have hu' : u ≤ j := Nat.lt_succ_iff.mp (lt_of_not_ge hu)
    by_cases hv : v ≤ j
    · exact Or.inr (Or.inr hv)
    · have hv' : j + 1 ≤ v := Nat.succ_le_of_lt (lt_of_not_ge hv)
      exact Or.inr (Or.inl ⟨hu', hv'⟩)

/-- Helper for Exercise 21.10.1: the finitely many active future coordinates in a cylinder event
factor through one common finest-row increment vector, and the resulting owner map is fixed by the
descendant-subtree sign flip on that row. -/
lemma exercise21101FutureActiveCoordinates_factorThroughCommonFineRow
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i r : ℕ) (I : Finset ℕ) :
    let M := max (n + 1) (I.sup id)
    let J := exercise21101DescendantSubtreeIndices P n i r M
    ∃ owner :
        (Fin (partitionBoundIndex P M 1) → ℝ) →
          ((m : I) → Fin (partitionBoundIndex P m 1) → ℝ),
      Measurable owner ∧
        (fun ω (m : I) (j : Fin (partitionBoundIndex P m 1)) ↦
          exercise21101FutureBlockArray W P (n + 1) ω m j) =
          owner ∘ exercise21101WholeRowIncrementVector W P M ∧
        ∀ z, owner (exercise21101SubtreeNeg J z) = owner z := by
  classical
  dsimp
  set M := max (n + 1) (I.sup id) with hM
  set J := exercise21101DescendantSubtreeIndices P n i r M with hJ
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let coarseRight := partitionNextPointUpTo P n i 1
  let childRight := partitionNextPointUpTo P (n + 1) (start + r) coarseRight
  let childStart := exercise21101CoarseEndpointRefinementIndex P (n + 1) (start + r) M
  let childStop := partitionBoundIndex P M childRight
  have hnM : n + 1 ≤ M := by
    rw [hM]
    exact le_max_left _ _
  have hmM_of_mem : ∀ m : I, (m : ℕ) ≤ M := by
    intro m
    rw [hM]
    exact le_trans
      (by
        simpa using
          (Finset.le_sup (s := I) (f := id) m.property : (m : ℕ) ≤ I.sup id))
      (le_max_right _ _)
  have hchildRight_partitionPoint_or_one :
      ∀ {m : ℕ}, n + 1 ≤ m →
        (∃ k : ℕ, childRight = P m k ∧ partitionBoundIndex P m childRight = k) ∨
          childRight = 1 := by
    intro m hnm
    rcases
        exercise21101PartitionNextPointUpTo_eq_partitionPoint_or_self
          P (n + 1) (start + r) coarseRight with
      ⟨k, hk_time, hk_bound⟩ | hk_self
    · let km := exercise21101CoarseEndpointRefinementIndex P (n + 1) k m
      left
      have hchild_eq : childRight = P m km := by
        calc
          childRight = P (n + 1) k := by simpa [childRight] using hk_time
          _ = P m km := by
            symm
            simpa [km] using
              (exercise21101CoarseEndpointRefinementIndex_spec P (n + 1) k m hnm)
      refine ⟨km, hchild_eq, ?_⟩
      simpa [hchild_eq] using
        (exercise21101_partitionBoundIndex_eq_of_partitionPoint
          (P := P) (n := m) (k := km))
    · rcases
          exercise21101PartitionNextPointUpTo_eq_partitionPoint_or_self
            P n i 1 with
        ⟨k, hk_time, hk_bound⟩ | hk_one
      · let km := exercise21101CoarseEndpointRefinementIndex P n k m
        left
        have hchild_eq : childRight = P m km := by
          calc
            childRight = P n k := by simpa [childRight, coarseRight, hk_self] using hk_time
            _ = P m km := by
              symm
              simpa [km] using
                (exercise21101CoarseEndpointRefinementIndex_spec P n k m
                  (Nat.le_trans (Nat.le_succ n) hnm))
        refine ⟨km, hchild_eq, ?_⟩
        simpa [hchild_eq] using
          (exercise21101_partitionBoundIndex_eq_of_partitionPoint
            (P := P) (n := m) (k := km))
      · right
        simpa [childRight, coarseRight, hk_self] using hk_one
  let owner :
      (Fin (partitionBoundIndex P M 1) → ℝ) →
        ((m : I) → Fin (partitionBoundIndex P m 1) → ℝ) :=
    fun z m j ↦
      if hnm : n < (m : ℕ) then
        let a := exercise21101CoarseEndpointRefinementIndex P (m : ℕ) j M
        let b := partitionBoundIndex P M (partitionNextPointUpTo P (m : ℕ) j 1)
        ((∑ q : Fin (b - a),
            z (exercise21101ShiftedFinInclusion
              (exercise21101FutureBlock_commonRowLength_le
                (P := P) (m := (m : ℕ)) (M := M) (j := j) (hmM_of_mem m) j.is_lt) q)) ^
            (2 : ℕ) -
          (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ)))
      else
        0
  have howner_meas : Measurable owner := by
    -- Proof comment: each owner coordinate is either `0` or a finite polynomial in the common
    -- row-`M` atomic increment coordinates.
    refine measurable_pi_lambda _ fun m ↦ ?_
    refine measurable_pi_lambda _ fun j ↦ ?_
    by_cases hnm : n < (m : ℕ)
    · let a := exercise21101CoarseEndpointRefinementIndex P (m : ℕ) j M
      let b := partitionBoundIndex P M (partitionNextPointUpTo P (m : ℕ) j 1)
      let hlen :=
        exercise21101FutureBlock_commonRowLength_le
          (P := P) (m := (m : ℕ)) (M := M) (j := j) (hmM_of_mem m) j.is_lt
      have hsum_meas :
          Measurable
            (fun z : Fin (partitionBoundIndex P M 1) → ℝ ↦
              ∑ q : Fin (b - a), z (exercise21101ShiftedFinInclusion hlen q)) := by
        refine Finset.measurable_sum _ ?_
        intro q hq
        exact measurable_pi_apply (exercise21101ShiftedFinInclusion hlen q)
      have hcoord_meas :
          Measurable
            (fun z : Fin (partitionBoundIndex P M 1) → ℝ ↦
              ((∑ q : Fin (b - a), z (exercise21101ShiftedFinInclusion hlen q)) ^ (2 : ℕ) -
                (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ)))) :=
        (hsum_meas.pow_const 2).sub measurable_const
      simpa [owner, hnm, a, b, hlen] using hcoord_meas
    · simp [owner, hnm]
  have howner_eq :
      (fun ω (m : I) (j : Fin (partitionBoundIndex P m 1)) ↦
        exercise21101FutureBlockArray W P (n + 1) ω m j) =
        owner ∘ exercise21101WholeRowIncrementVector W P M := by
    -- Proof comment: rows below `n + 1` vanish by definition, while rows from `n + 1` onward
    -- rewrite through the common row-`M` interval formula proved just above.
    funext ω m j
    by_cases hnm : n + 1 ≤ (m : ℕ)
    · let a := exercise21101CoarseEndpointRefinementIndex P (m : ℕ) j M
      let b := partitionBoundIndex P M (partitionNextPointUpTo P (m : ℕ) j 1)
      have hnm' : n < (m : ℕ) := Nat.succ_le_iff.mp hnm
      have hcoord :=
        congrFun
          (exercise21101FutureBlockContribution_eq_sum_fineRowAtomicIncrements
            (W := W) (P := P) (m := (m : ℕ)) (M := M) (j := j) (hmM_of_mem m) j.is_lt)
          ω
      have hvec :
          (∑ q : Fin (b - a),
              exercise21101WholeRowIncrementVector W P M ω
                (exercise21101ShiftedFinInclusion
                  (exercise21101FutureBlock_commonRowLength_le
                    (P := P) (m := (m : ℕ)) (M := M) (j := j) (hmM_of_mem m) j.is_lt) q)) =
            Finset.sum (Finset.range (b - a)) fun s ↦
              (W (partitionNextPointUpTo P M (a + s) 1) ω - W (P M (a + s)) ω) := by
        calc
          (∑ q : Fin (b - a),
              exercise21101WholeRowIncrementVector W P M ω
                (exercise21101ShiftedFinInclusion
                  (exercise21101FutureBlock_commonRowLength_le
                    (P := P) (m := (m : ℕ)) (M := M) (j := j) (hmM_of_mem m) j.is_lt) q))
              =
                ∑ q : Fin (b - a),
                  (W (partitionNextPointUpTo P M (a + q) 1) ω - W (P M (a + q)) ω) := by
                    refine Finset.sum_congr rfl ?_
                    intro q hq
                    simp [exercise21101WholeRowIncrementVector, exercise21101RowSegmentIncrementVector,
                      exercise21101ShiftedFinInclusion, a]
          _ = Finset.sum (Finset.range (b - a)) fun s ↦
                (W (partitionNextPointUpTo P M (a + s) 1) ω - W (P M (a + s)) ω) := by
                  symm
                  simpa using
                    (Fin.sum_univ_eq_sum_range
                      (n := b - a)
                      (f := fun s : ℕ ↦
                        (W (partitionNextPointUpTo P M (a + s) 1) ω - W (P M (a + s)) ω))).symm
      have hcoord' :
          exercise21101BlockContribution W (P (m : ℕ) j) (partitionNextPointUpTo P (m : ℕ) j 1) ω =
            ((∑ q : Fin (b - a),
                exercise21101WholeRowIncrementVector W P M ω
                  (exercise21101ShiftedFinInclusion
                    (exercise21101FutureBlock_commonRowLength_le
                      (P := P) (m := (m : ℕ)) (M := M) (j := j) (hmM_of_mem m) j.is_lt) q)) ^
                (2 : ℕ) -
              (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ))) := by
        calc
          exercise21101BlockContribution W (P (m : ℕ) j) (partitionNextPointUpTo P (m : ℕ) j 1) ω
              =
                ((Finset.sum (Finset.range (b - a)) fun s ↦
                    (W (partitionNextPointUpTo P M (a + s) 1) ω - W (P M (a + s)) ω)) ^
                  (2 : ℕ) -
                (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ))) := hcoord
          _ =
              ((∑ q : Fin (b - a),
                  exercise21101WholeRowIncrementVector W P M ω
                    (exercise21101ShiftedFinInclusion
                      (exercise21101FutureBlock_commonRowLength_le
                        (P := P) (m := (m : ℕ)) (M := M) (j := j) (hmM_of_mem m) j.is_lt) q)) ^
                  (2 : ℕ) -
                (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ))) := by
                  rw [← hvec]
      simpa [Function.comp, owner, exercise21101FutureBlockArray, hnm, hnm', a, b] using hcoord'
    · have hnm' : ¬ n < (m : ℕ) := by
        simpa [Nat.succ_le_iff] using hnm
      simp [Function.comp, owner, exercise21101FutureBlockArray, hnm, hnm']
  have howner_fixed : ∀ z, owner (exercise21101SubtreeNeg J z) = owner z := by
    intro z
    funext m j
    by_cases hnm : n + 1 ≤ (m : ℕ)
    · let a := exercise21101CoarseEndpointRefinementIndex P (m : ℕ) j M
      let b := partitionBoundIndex P M (partitionNextPointUpTo P (m : ℕ) j 1)
      let hlen :=
        exercise21101FutureBlock_commonRowLength_le
          (P := P) (m := (m : ℕ)) (M := M) (j := j) (hmM_of_mem m) j.is_lt
      have hnm' : n < (m : ℕ) := Nat.succ_le_iff.mp hnm
      let u := exercise21101CoarseEndpointRefinementIndex P (n + 1) (start + r) (m : ℕ)
      let v := partitionBoundIndex P (m : ℕ) childRight
      have hbounds :=
        exercise21101FutureBlock_commonRowBounds
          (P := P) (m := (m : ℕ)) (M := M) (j := j) (hmM_of_mem m) j.is_lt
      have hab : a ≤ b := Nat.le_of_lt hbounds.1
      have hu_spec_m :
          P (m : ℕ) u = P (n + 1) (start + r) := by
        simpa [u, start] using
          exercise21101CoarseEndpointRefinementIndex_spec
            P (n + 1) (start + r) (m : ℕ) hnm
      have hchildStart_spec :
          P M childStart = P (n + 1) (start + r) := by
        simpa [childStart, start] using
          exercise21101CoarseEndpointRefinementIndex_spec
            P (n + 1) (start + r) M hnM
      by_cases hdeg : childStop ≤ childStart
      · have hJnot : ∀ q : Fin (partitionBoundIndex P M 1), q ∉ J := by
          intro q
          intro hq
          have hq' : childStart ≤ (q : ℕ) ∧ (q : ℕ) < childStop := by
            simpa [J, hJ, childStart, childStop, childRight, coarseRight, start,
              exercise21101DescendantSubtreeIndices] using hq
          exact not_lt_of_ge (le_trans hdeg hq'.1) hq'.2
        have hsubtree_id : exercise21101SubtreeNeg J z = z := by
          funext q
          simp [exercise21101SubtreeNeg, hJnot q]
        simpa [owner, hnm', a, b, hlen] using
          congrArg (fun zz ↦ owner zz m j) hsubtree_id
      · have hchild_nonempty : childStart < childStop := lt_of_not_ge hdeg
        have hleft_time :
            P (n + 1) (start + r) < childRight := by
          have hrow :=
            exercise21101_partitionPoint_lt_time_of_lt_partitionBoundIndex
              P M childStart childRight hchild_nonempty
          simpa [hchildStart_spec] using hrow
        have hr_valid :
            r <
              partitionBoundIndex P (n + 1) coarseRight - start := by
          have hidx :
              start + r < partitionBoundIndex P (n + 1) coarseRight := by
            simpa [start, coarseRight, childRight] using
              (exercise21101_lt_partitionBoundIndex_of_partitionPoint_lt_time
                P (n + 1) (start + r) coarseRight
                (lt_of_lt_of_le hleft_time (by simp [childRight, partitionNextPointUpTo])))
          omega
        have htrich :
            j + 1 ≤ u ∨ (u ≤ j ∧ j + 1 ≤ v) ∨ v ≤ j := by
          simpa [u, v, start, coarseRight, childRight] using
            (exercise21101FutureBlock_indexTrichotomyAgainstDescendantChild
              (P := P) (n := n) (i := i) (r := r) (m := (m : ℕ)) (j := j)
              hnm hr_valid)
        rcases htrich with hbefore | hinside | hafter
        · have htime_before :
            partitionNextPointUpTo P (m : ℕ) j 1 ≤ P (m : ℕ) u := by
            by_cases hnext : j + 1 < partitionBoundIndex P (m : ℕ) 1
            · rw [exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
                P (m : ℕ) j 1 hnext]
              exact
                (IsAdmissiblePartitionSequence.strictMono (P := P) (m : ℕ)).monotone hbefore
            · have hlast : j + 1 = partitionBoundIndex P (m : ℕ) 1 := by
                exact le_antisymm (Nat.succ_le_of_lt j.is_lt) (Nat.le_of_not_gt hnext)
              rw [partitionNextPointUpTo, hlast, min_eq_right]
              · have hboundary_le :
                    partitionBoundIndex P (m : ℕ) 1 ≤ u := by
                  simpa [hlast] using hbefore
                exact le_trans (le_partitionBoundIndex_time P (m : ℕ) 1)
                  ((IsAdmissiblePartitionSequence.strictMono (P := P) (m : ℕ)).monotone
                    hboundary_le)
              · exact le_partitionBoundIndex_time P (m : ℕ) 1
          have hbefore_M : b ≤ childStart := by
            calc
              b = partitionBoundIndex P M (partitionNextPointUpTo P (m : ℕ) j 1) := rfl
              _ ≤ partitionBoundIndex P M (P (m : ℕ) u) :=
                exercise21101PartitionBoundIndex_mono P M htime_before
              _ = partitionBoundIndex P M (P M childStart) := by
                rw [hu_spec_m, hchildStart_spec]
              _ = childStart := by
                rw [exercise21101_partitionBoundIndex_eq_of_partitionPoint]
          have hnotmem :
              ∀ q : Fin (b - a),
                exercise21101ShiftedFinInclusion hlen q ∉ J := by
            intro q
            simpa [J, hJ, a, b, childStart, childStop, childRight, coarseRight, start, hlen,
              exercise21101ShiftedFinInclusion] using
              (exercise21101NotMem_descendantSubtreeIndices_of_shiftedIndex
                (P := P) (n := n) (i := i) (r := r) (M := M) (a := a) (b := b)
                hab hbounds.2 (Or.inl hbefore_M) q.is_lt)
          have hsum_fixed :=
            exercise21101SubtreeNeg_shiftedFinSum_eq (J := J) (h := hlen) hnotmem z
          have hcoord_fixed :
              ((∑ q : Fin (b - a),
                  exercise21101SubtreeNeg J z
                    (exercise21101ShiftedFinInclusion hlen q)) ^ (2 : ℕ) -
                (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ))) =
                ((∑ q : Fin (b - a),
                  z (exercise21101ShiftedFinInclusion hlen q)) ^ (2 : ℕ) -
                (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ))) := by
            rw [hsum_fixed]
          simpa [owner, hnm', a, b, hlen] using hcoord_fixed
        · have hleft_M : childStart ≤ a := by
            calc
              childStart = partitionBoundIndex P M (P M childStart) := by
                rw [exercise21101_partitionBoundIndex_eq_of_partitionPoint]
              _ ≤ partitionBoundIndex P M (P (m : ℕ) j) := by
                refine exercise21101PartitionBoundIndex_mono P M ?_
                calc
                  P M childStart = P (n + 1) (start + r) := hchildStart_spec
                  _ = P (m : ℕ) u := hu_spec_m.symm
                  _ ≤ P (m : ℕ) j :=
                    (IsAdmissiblePartitionSequence.strictMono (P := P) (m : ℕ)).monotone
                      hinside.1
              _ = a := by
                rw [← exercise21101CoarseEndpointRefinementIndex_spec
                  P (m : ℕ) j M (hmM_of_mem m)]
                rw [exercise21101_partitionBoundIndex_eq_of_partitionPoint]
          have htime_inside_right :
              partitionNextPointUpTo P (m : ℕ) j 1 ≤ childRight := by
            by_cases hchild_one : childRight = 1
            · simpa [hchild_one] using
                (show partitionNextPointUpTo P (m : ℕ) j 1 ≤ (1 : NNReal) by
                  simp [partitionNextPointUpTo])
            · rcases hchildRight_partitionPoint_or_one (m := (m : ℕ)) hnm with
                ⟨k, hk_time, hk_bound⟩ | hk_one
              · have hchild_lt_one : childRight < 1 := by
                  exact lt_of_le_of_ne (by simp [childRight, coarseRight, partitionNextPointUpTo])
                    hchild_one
                have hk_time_lt : P (m : ℕ) k < 1 := by
                  simpa [hk_time] using hchild_lt_one
                have hk_lt : k < partitionBoundIndex P (m : ℕ) 1 := by
                  exact
                    exercise21101_lt_partitionBoundIndex_of_partitionPoint_lt_time
                      P (m : ℕ) k 1 hk_time_lt
                have hv_lt : v < partitionBoundIndex P (m : ℕ) 1 := by
                  simpa [v, hk_bound] using hk_lt
                have hnext :
                    partitionNextPointUpTo P (m : ℕ) j 1 = P (m : ℕ) (j + 1) := by
                  exact
                    exercise21101_partitionNextPointUpTo_eq_next_of_succ_lt_partitionBoundIndex
                      P (m : ℕ) j 1 (lt_of_le_of_lt hinside.2 hv_lt)
                calc
                  partitionNextPointUpTo P (m : ℕ) j 1 = P (m : ℕ) (j + 1) := hnext
                  _ ≤ P (m : ℕ) k :=
                    (IsAdmissiblePartitionSequence.strictMono (P := P) (m : ℕ)).monotone <| by
                    simpa [v, hk_bound] using hinside.2
                  _ = childRight := hk_time.symm
              · exact (hchild_one hk_one).elim
          have hright_M : b ≤ childStop := by
            exact exercise21101PartitionBoundIndex_mono P M htime_inside_right
          have hmem :
              ∀ q : Fin (b - a),
                exercise21101ShiftedFinInclusion hlen q ∈ J := by
            intro q
            simpa [J, hJ, a, b, childStart, childStop, childRight, coarseRight, start, hlen,
              exercise21101ShiftedFinInclusion] using
              (exercise21101Mem_descendantSubtreeIndices_of_shiftedIndex
                (P := P) (n := n) (i := i) (r := r) (M := M) (a := a) (b := b)
                hab hbounds.2 hleft_M hright_M q.is_lt)
          have hsum_neg :=
            exercise21101SubtreeNeg_shiftedFinSum_eq_neg (J := J) (h := hlen) hmem z
          have hcoord_fixed :
              ((∑ q : Fin (b - a),
                  exercise21101SubtreeNeg J z
                    (exercise21101ShiftedFinInclusion hlen q)) ^ (2 : ℕ) -
                (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ))) =
                ((∑ q : Fin (b - a),
                  z (exercise21101ShiftedFinInclusion hlen q)) ^ (2 : ℕ) -
                (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ))) := by
            rw [hsum_neg]
            ring
          simpa [owner, hnm', a, b, hlen] using hcoord_fixed
        · have htime_after : childRight ≤ P (m : ℕ) j := by
            calc
              childRight ≤ P (m : ℕ) v := le_partitionBoundIndex_time P (m : ℕ) childRight
              _ ≤ P (m : ℕ) j :=
                (IsAdmissiblePartitionSequence.strictMono (P := P) (m : ℕ)).monotone hafter
          have hafter_M : childStop ≤ a := by
            calc
              childStop = partitionBoundIndex P M childRight := rfl
              _ ≤ partitionBoundIndex P M (P (m : ℕ) j) :=
                exercise21101PartitionBoundIndex_mono P M htime_after
              _ = a := by
                rw [← exercise21101CoarseEndpointRefinementIndex_spec
                  P (m : ℕ) j M (hmM_of_mem m)]
                rw [exercise21101_partitionBoundIndex_eq_of_partitionPoint]
          have hnotmem :
              ∀ q : Fin (b - a),
                exercise21101ShiftedFinInclusion hlen q ∉ J := by
            intro q
            simpa [J, hJ, a, b, childStart, childStop, childRight, coarseRight, start, hlen,
              exercise21101ShiftedFinInclusion] using
              (exercise21101NotMem_descendantSubtreeIndices_of_shiftedIndex
                (P := P) (n := n) (i := i) (r := r) (M := M) (a := a) (b := b)
                hab hbounds.2 (Or.inr hafter_M) q.is_lt)
          have hsum_fixed :=
            exercise21101SubtreeNeg_shiftedFinSum_eq (J := J) (h := hlen) hnotmem z
          have hcoord_fixed :
              ((∑ q : Fin (b - a),
                  exercise21101SubtreeNeg J z
                    (exercise21101ShiftedFinInclusion hlen q)) ^ (2 : ℕ) -
                (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ))) =
                ((∑ q : Fin (b - a),
                  z (exercise21101ShiftedFinInclusion hlen q)) ^ (2 : ℕ) -
                (((partitionNextPointUpTo P (m : ℕ) j 1 - P (m : ℕ) j : NNReal) : ℝ))) := by
            rw [hsum_fixed]
          simpa [owner, hnm', a, b, hlen] using hcoord_fixed
    · have hnm' : ¬ n < (m : ℕ) := by
        simpa [Nat.succ_le_iff] using hnm
      simp [owner, hnm, hnm']
  exact ⟨owner, howner_meas, howner_eq, howner_fixed⟩

/-- Helper for Exercise 21.10.1: the descendant prefix-product summand also factors through the
same common finest-row increment vector and is odd under the corresponding descendant-subtree sign
flip. -/
lemma exercise21101DescendantCrossSummand_factorThroughCommonFineRow
    (W : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i r : ℕ)
    (hr :
      r <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1))
    (I : Finset ℕ) :
    let M := max (n + 1) (I.sup id)
    let J := exercise21101DescendantSubtreeIndices P n i r M
    ∃ f : (Fin (partitionBoundIndex P M 1) → ℝ) → ℝ,
      StronglyMeasurable f ∧
        exercise21101DescendantCrossSummand W P n i r =
          f ∘ exercise21101WholeRowIncrementVector W P M ∧
        ∀ z, f (exercise21101SubtreeNeg J z) = -f z := by
  classical
  dsimp
  set M := max (n + 1) (I.sup id) with hM
  set J := exercise21101DescendantSubtreeIndices P n i r M with hJ
  let start := exercise21101CoarseEndpointRefinementIndex P n i (n + 1)
  let count :=
    partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) - start
  let childStart : ℕ → ℕ := fun s ↦
    exercise21101CoarseEndpointRefinementIndex P (n + 1) (start + s) M
  let childStop : ℕ → ℕ := fun s ↦
    partitionBoundIndex P M
      (partitionNextPointUpTo P (n + 1) (start + s) (partitionNextPointUpTo P n i 1))
  have hnM : n + 1 ≤ M := by
    rw [hM]
    exact le_max_left _ _
  have hchildBounds :
      ∀ s, s < count →
        childStart s < childStop s ∧ childStop s ≤ partitionBoundIndex P M 1 := by
    intro s hs
    simpa [count, start, childStart, childStop] using
      (exercise21101CopiedDescendantChild_bounds
        (P := P) (n := n) (i := i) (s := s) (M := M) hnM hs)
  have hchildLen :
      ∀ s, s < count →
        childStart s + (childStop s - childStart s) ≤ partitionBoundIndex P M 1 := by
    intro s hs
    have hbounds := hchildBounds s hs
    have hab : childStart s ≤ childStop s := Nat.le_of_lt hbounds.1
    calc
      childStart s + (childStop s - childStart s) = childStop s := Nat.add_sub_of_le hab
      _ ≤ partitionBoundIndex P M 1 := hbounds.2
  let childSum :
      ∀ s, s < count → (Fin (partitionBoundIndex P M 1) → ℝ) → ℝ :=
    fun s hs z ↦
      ∑ q : Fin (childStop s - childStart s),
        z (exercise21101ShiftedFinInclusion (hchildLen s hs) q)
  let prefixSum : (Fin (partitionBoundIndex P M 1) → ℝ) → ℝ :=
    fun z ↦ ∑ s : Fin r, childSum s (lt_trans s.is_lt hr) z
  let currentSum : (Fin (partitionBoundIndex P M 1) → ℝ) → ℝ :=
    fun z ↦ childSum r hr z
  let f : (Fin (partitionBoundIndex P M 1) → ℝ) → ℝ :=
    fun z ↦ 2 * prefixSum z * currentSum z
  have hchild_meas :
      ∀ s hs, Measurable (childSum s hs) := by
    intro s hs
    -- Proof comment: each common-row child sum is a finite sum of coordinate projections of the
    -- common-row increment vector.
    simp only [childSum]
    refine Finset.measurable_sum _ ?_
    intro q hq
    exact measurable_pi_apply (exercise21101ShiftedFinInclusion (hchildLen s hs) q)
  have hprefix_meas : Measurable prefixSum := by
    -- Proof comment: the descendant prefix sum is a finite sum of the measurable child sums.
    simp only [prefixSum]
    refine Finset.measurable_sum _ ?_
    intro s hs
    exact hchild_meas s (lt_trans s.is_lt hr)
  have hcurrent_meas : Measurable currentSum := by
    simpa [currentSum] using hchild_meas r hr
  have hprod_sm : StronglyMeasurable (fun z ↦ prefixSum z * currentSum z) := by
    exact hprefix_meas.stronglyMeasurable.mul hcurrent_meas.stronglyMeasurable
  have hf_sm : StronglyMeasurable f := by
    -- Proof comment: the explicit polynomial `2 * prefixSum * currentSum` is measurable on the
    -- finite-dimensional common-row coordinate space.
    simpa [f, mul_assoc, mul_left_comm, mul_comm] using hprod_sm.const_mul (2 : ℝ)
  have hprefix_eq_fin :
      (fun ω ↦
        ∑ s : Fin r,
          (W (partitionNextPointUpTo P (n + 1) (start + s) (partitionNextPointUpTo P n i 1)) ω -
            W (P (n + 1) (start + s)) ω)) =
        fun ω ↦ prefixSum (exercise21101WholeRowIncrementVector W P M ω) := by
    -- Proof comment: on the `Fin r` indexing set, each descendant child increment rewrites once
    -- through the common-row child sum bridge.
    funext ω
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hchild :=
      congrFun
        (exercise21101CopiedDescendantChildIncrement_eq_commonRowChildSum
          (W := W) (P := P) (n := n) (i := i) (s := s) (M := M) hnM
          (lt_trans s.is_lt hr)) ω
    simpa [count, start, childStart, childStop, childSum, prefixSum] using hchild
  have hprefix_eq :
      (fun ω ↦
        Finset.sum (Finset.range r) fun s ↦
          (W (partitionNextPointUpTo P (n + 1) (start + s) (partitionNextPointUpTo P n i 1)) ω -
            W (P (n + 1) (start + s)) ω)) =
        fun ω ↦ prefixSum (exercise21101WholeRowIncrementVector W P M ω) := by
    -- Proof comment: every prefix descendant increment rewrites once through the common-row child
    -- sum bridge, and the outer prefix sum is then just `prefixSum`.
    calc
      (fun ω ↦
        Finset.sum (Finset.range r) fun s ↦
          (W (partitionNextPointUpTo P (n + 1) (start + s) (partitionNextPointUpTo P n i 1)) ω -
            W (P (n + 1) (start + s)) ω))
          =
            (fun ω ↦
              ∑ s : Fin r,
                (W (partitionNextPointUpTo P (n + 1) (start + s)
                    (partitionNextPointUpTo P n i 1)) ω -
                  W (P (n + 1) (start + s)) ω)) := by
              funext ω
              symm
              simpa using
                (Fin.sum_univ_eq_sum_range
                  (n := r)
                  (f := fun s : ℕ ↦
                    (W (partitionNextPointUpTo P (n + 1) (start + s)
                        (partitionNextPointUpTo P n i 1)) ω -
                      W (P (n + 1) (start + s)) ω)))
      _ = fun ω ↦ prefixSum (exercise21101WholeRowIncrementVector W P M ω) := hprefix_eq_fin
  have hcurrent_eq :
      (fun ω ↦
        W (partitionNextPointUpTo P (n + 1) (start + r) (partitionNextPointUpTo P n i 1)) ω -
          W (P (n + 1) (start + r)) ω) =
        fun ω ↦ currentSum (exercise21101WholeRowIncrementVector W P M ω) := by
    -- Proof comment: the current descendant child is the same common-row child sum specialized to
    -- the index `r`.
    funext ω
    have hchild :=
      congrFun
        (exercise21101CopiedDescendantChildIncrement_eq_commonRowChildSum
          (W := W) (P := P) (n := n) (i := i) (s := r) (M := M) hnM hr) ω
    simpa [count, start, childStart, childStop, childSum, currentSum] using hchild
  refine ⟨f, hf_sm, ?_, ?_⟩
  · -- Proof comment: after rewriting the prefix and current descendant increments through the
    -- common-row child sums, the summand is exactly the explicit polynomial `f`.
    funext ω
    rw [exercise21101DescendantCrossSummand]
    rw [show (Finset.sum (Finset.range r) fun s ↦
        (W (partitionNextPointUpTo P (n + 1) (start + s) (partitionNextPointUpTo P n i 1)) ω -
          W (P (n + 1) (start + s)) ω)) =
        prefixSum (exercise21101WholeRowIncrementVector W P M ω) from congrFun hprefix_eq ω]
    rw [show
        W (partitionNextPointUpTo P (n + 1) (start + r) (partitionNextPointUpTo P n i 1)) ω -
          W (P (n + 1) (start + r)) ω =
        currentSum (exercise21101WholeRowIncrementVector W P M ω) from congrFun hcurrent_eq ω]
    simp [f, Function.comp]
  · intro z
    have hprefix_fixed :
        prefixSum (exercise21101SubtreeNeg J z) = prefixSum z := by
      -- Proof comment: every prefix child lies strictly before the current child, so its common-
      -- row coordinates are disjoint from the flipped descendant subtree.
      change ∑ s : Fin r, childSum s (lt_trans s.is_lt hr) (exercise21101SubtreeNeg J z) =
        ∑ s : Fin r, childSum s (lt_trans s.is_lt hr) z
      refine Finset.sum_congr rfl ?_
      intro s hs
      have hs_prefix : (s : ℕ) < r := s.is_lt
      have hs_count : (s : ℕ) < count := lt_trans s.is_lt hr
      have hsep :
          childStop s ≤ childStart r := by
        simpa [start, childStart, childStop] using
          (exercise21101CopiedDescendantPrefixBlock_right_le_currentStart
            (P := P) (n := n) (i := i) (r := r) (s := s) (M := M) hnM hr hs_prefix)
      have hnotmem :
          ∀ q : Fin (childStop s - childStart s),
            exercise21101ShiftedFinInclusion (hchildLen s hs_count) q ∉ J := by
        intro q
        have hbounds := hchildBounds s hs_count
        have hab : childStart s ≤ childStop s := Nat.le_of_lt hbounds.1
        simpa [J, hJ, childStart, childStop, exercise21101ShiftedFinInclusion] using
          (exercise21101NotMem_descendantSubtreeIndices_of_shiftedIndex
            (P := P) (n := n) (i := i) (r := r) (M := M)
            (a := childStart s) (b := childStop s)
            hab hbounds.2 (Or.inl hsep) q.is_lt)
      simpa [childSum] using
        (exercise21101SubtreeNeg_shiftedFinSum_eq
          (J := J) (h := hchildLen s hs_count) hnotmem z)
    have hcurrent_neg :
        currentSum (exercise21101SubtreeNeg J z) = -currentSum z := by
      -- Proof comment: the current child interval is exactly the flipped descendant subtree, so
      -- the corresponding common-row child sum changes sign.
      have hmem :
          ∀ q : Fin (childStop r - childStart r),
            exercise21101ShiftedFinInclusion (hchildLen r hr) q ∈ J := by
        intro q
        have hbounds := hchildBounds r hr
        have hab : childStart r ≤ childStop r := Nat.le_of_lt hbounds.1
        simpa [J, hJ, childStart, childStop, exercise21101ShiftedFinInclusion] using
          (exercise21101Mem_descendantSubtreeIndices_of_shiftedIndex
            (P := P) (n := n) (i := i) (r := r) (M := M)
            (a := childStart r) (b := childStop r)
            hab hbounds.2 le_rfl le_rfl q.is_lt)
      simpa [childSum, currentSum] using
        (exercise21101SubtreeNeg_shiftedFinSum_eq_neg
          (J := J) (h := hchildLen r hr) hmem z)
    -- Route correction: the oddness proof now stays entirely in the stable common-row child-sum
    -- normal form instead of rebuilding a separate descendant-vector transport.
    simp [f, hprefix_fixed, hcurrent_neg]

/-- Helper for Exercise 21.10.1: once the backward process is a martingale for the larger future-
block tail filtration, Chapter 9 transfers it to the natural filtration of the process itself. -/
lemma exercise21101BackwardProcess_martingale_naturalFiltration_of_tailMartingale
    {W : NNReal → Ω → ℝ}
    (hW_meas : ∀ t, StronglyMeasurable (W t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] [IsFiniteMeasure μ]
    (hTail :
      Martingale
        (exercise21101BackwardProcess W P)
        (backwardQuadraticVariationTailFiltration W hW_meas P)
        μ) :
    Martingale
      (exercise21101BackwardProcess W P)
      (Filtration.natural
        (exercise21101BackwardProcess W P)
        (exercise21101BackwardProcess_stronglyMeasurable W hW_meas P))
      μ := by
  have hnat := martingale_natural_filtration hTail
  have hwitness :
      (fun n ↦
        (hTail.stronglyAdapted n).mono
          ((backwardQuadraticVariationTailFiltration W hW_meas P).le n)) =
        exercise21101BackwardProcess_stronglyMeasurable W hW_meas P := by
    -- Proof comment: both sides are proofs of the same strong measurability statement.
    funext n
    exact Subsingleton.elim _ _
  -- Proof comment: only the strong-measurability witness differs from the canonical one used in
  -- the statement of the exercise.
  simpa [hwitness] using hnat

/-- Helper for Exercise 21.10.1: on `OrderDual ℕ`, a one-step conditional-expectation identity
already implies the full martingale family of identities. -/
lemma orderDualMartingale_of_condExp_succ
    {f : ℕᵒᵈ → Ω → ℝ} {ℱ : Filtration ℕᵒᵈ ‹MeasurableSpace Ω›} [IsFiniteMeasure μ]
    (hadp : StronglyAdapted ℱ f)
    (hint : ∀ n : ℕ, Integrable (f (toDual n)) μ)
    (hsucc : ∀ n : ℕ, μ[f (toDual n) | ℱ (toDual (n + 1))] =ᵐ[μ] f (toDual (n + 1))) :
    Martingale f ℱ μ := by
  refine ⟨hadp, ?_⟩
  intro i j hij
  change μ[f (toDual (ofDual j)) | ℱ (toDual (ofDual i))] =ᵐ[μ] f (toDual (ofDual i))
  let m : ℕ := ofDual j
  let n : ℕ := ofDual i
  have hmn : m ≤ n := hij
  -- Proof comment: iterate the one-step identity down the reversed index chain by the tower
  -- property for conditional expectation.
  have haux :
      ∀ n' : ℕ, m ≤ n' → μ[f (toDual m) | ℱ (toDual n')] =ᵐ[μ] f (toDual n') := by
    intro n' hmn'
    induction hmn' with
    | refl =>
        -- Proof comment: conditioning a stage on its own `σ`-algebra does nothing.
        exact Filter.EventuallyEq.of_eq
          (condExp_of_stronglyMeasurable (ℱ.le (toDual m)) (hadp (toDual m)) (hint m))
    | @step n' hmn' ih =>
        calc
          μ[f (toDual m) | ℱ (toDual (n' + 1))]
              =ᵐ[μ] μ[μ[f (toDual m) | ℱ (toDual n')] | ℱ (toDual (n' + 1))] := by
                  -- Proof comment: first condition at stage `n`, then push one step further by
                  -- the tower property along the decreasing filtration.
                  symm
                  simpa using
                    (ℱ.condExp_condExp (f (toDual m))
                      (by
                        exact Nat.le_succ n'))
          _ =ᵐ[μ] μ[f (toDual n') | ℱ (toDual (n' + 1))] := by
                exact condExp_congr_ae ih
          _ =ᵐ[μ] f (toDual (n' + 1)) := hsucc n'
  have hcond : μ[f (toDual m) | ℱ (toDual n)] =ᵐ[μ] f (toDual n) := haux n hmn
  simpa [m, n] using hcond

/-- Helper for Exercise 21.10.1: each refined cross remainder has conditional expectation `0`
with respect to the stage-`n + 1` future-block tail filtration. -/
lemma exercise21101DescendantCrossSummand_setIntegral_eq_zero_on_tailCylinder
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i r : ℕ) (hi : i < partitionBoundIndex P n 1)
    (hr :
      r <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    ∀ C,
      C ∈ MeasureTheory.measurableCylinders (fun _ : ℕ ↦ ℕ → ℝ) →
        ∫ ω in (exercise21101FutureBlockArray W P (n + 1)) ⁻¹' C,
          exercise21101DescendantCrossSummand W P n i r ω ∂μ = 0 := by
  classical
  intro C hC
  rcases
      exercise21101FutureBlockArray_cylinderPreimage_eq_activeCoordinatesPreimage
        (W := W) (P := P) (n := n + 1) hC with
    ⟨I, U, hU_meas, hC_preimage⟩
  let S : Set ((i : I) → Fin (partitionBoundIndex P i 1) → ℝ) :=
    (exercise21101FutureBlockCylinderOwner P I) ⁻¹' U
  have hS_meas : MeasurableSet S := by
    -- Proof comment: the active-coordinate owner is measurable, so its pullback preserves the
    -- measurable cylinder set on the finite row support.
    simpa [S] using hU_meas.preimage (exercise21101FutureBlockCylinderOwner_measurable P I)
  let M := max (n + 1) (I.sup id)
  let X := exercise21101WholeRowIncrementVector W P M
  let J := exercise21101DescendantSubtreeIndices P n i r M
  obtain ⟨owner, howner_meas, howner_eq, howner_fixed⟩ := by
    -- Proof comment: package the finite active future coordinates through one common row-`M`
    -- Gaussian vector so the cylinder owner becomes a measurable finite-dimensional map.
    simpa [M, J, X] using
      (exercise21101FutureActiveCoordinates_factorThroughCommonFineRow
        (W := W) (P := P) (n := n) (i := i) (r := r) I)
  obtain ⟨f, hf_sm, hf_eq, hf_anti⟩ := by
    -- Proof comment: transport the descendant cross summand to the same row-`M` coordinates,
    -- where it remains odd under the identical descendant-subtree sign flip.
    simpa [M, J, X] using
      (exercise21101DescendantCrossSummand_factorThroughCommonFineRow
        (W := W) (P := P) (n := n) (i := i) (r := r) hr I)
  have hX_meas : Measurable X :=
    exercise21101WholeRowIncrementVector_measurable W hW.stronglyMeasurable P M
  have howner_pre_meas : MeasurableSet (owner ⁻¹' S) := hS_meas.preimage howner_meas
  have hpreimageX :
      X ⁻¹' (owner ⁻¹' S) = (exercise21101FutureBlockArray W P (n + 1)) ⁻¹' C := by
    -- Proof comment: after the cylinder reduction, the event really is the owner preimage of the
    -- active-coordinate set `S`, and the common-row factorization identifies those coordinates as
    -- `owner ∘ X`.
    calc
      X ⁻¹' (owner ⁻¹' S) = (owner ∘ X) ⁻¹' S := by
        rfl
      _ =
          (fun ω (m : I) (j : Fin (partitionBoundIndex P m 1)) ↦
            exercise21101FutureBlockArray W P (n + 1) ω m j) ⁻¹' S := by
              rw [← howner_eq]
      _ = (exercise21101FutureBlockArray W P (n + 1)) ⁻¹' C := by
            simpa [S] using hC_preimage.symm
  have hfuture_meas :
      MeasurableSet ((exercise21101FutureBlockArray W P (n + 1)) ⁻¹' C) := by
    -- Proof comment: measurability comes from pulling the measurable owner set back along the
    -- measurable common-row increment vector.
    simpa [hpreimageX] using howner_pre_meas.preimage hX_meas
  have hf_comp :
      f ∘ X = exercise21101DescendantCrossSummand W P n i r := by
    simpa [X] using hf_eq.symm
  have hindicator_sm : StronglyMeasurable (Set.indicator (owner ⁻¹' S) f) :=
    hf_sm.indicator howner_pre_meas
  have hindicator_comp_eq :
      (fun ω ↦ Set.indicator (owner ⁻¹' S) f (X ω)) =
        Set.indicator ((exercise21101FutureBlockArray W P (n + 1)) ⁻¹' C)
          (exercise21101DescendantCrossSummand W P n i r) := by
    -- Proof comment: the pullback event is exactly the future-block cylinder preimage, and the
    -- transported integrand is exactly the descendant summand.
    funext ω
    by_cases hω : X ω ∈ owner ⁻¹' S
    · have hωX : ω ∈ X ⁻¹' (owner ⁻¹' S) := by
        simpa using hω
      have hω' : ω ∈ (exercise21101FutureBlockArray W P (n + 1)) ⁻¹' C := by
        simpa [hpreimageX] using hωX
      have hfω : f (X ω) = exercise21101DescendantCrossSummand W P n i r ω := by
        simpa [Function.comp] using congrFun hf_comp ω
      simp [Set.indicator, hω, hω', hfω]
    · have hωX : ω ∉ X ⁻¹' (owner ⁻¹' S) := by
        simpa using hω
      have hω' : ω ∉ (exercise21101FutureBlockArray W P (n + 1)) ⁻¹' C := by
        simpa [hpreimageX] using hωX
      simp [Set.indicator, hω, hω']
  have hindicator_comp_int :
      Integrable ((Set.indicator (owner ⁻¹' S) f) ∘ X) μ := by
    -- Proof comment: after identifying the pulled-back indicator integrand with the restricted
    -- descendant summand, integrability follows from the already proved `L¹` bound on that
    -- summand.
    change Integrable (fun ω ↦ Set.indicator (owner ⁻¹' S) f (X ω)) μ
    rw [hindicator_comp_eq]
    exact
      (exercise21101DescendantCrossSummand_integrable hW P n i r hi hr).indicator hfuture_meas
  have hindicator_int :
      Integrable (Set.indicator (owner ⁻¹' S) f) (μ.map X) := by
    -- Proof comment: transport integrability from the original probability space to the
    -- pushforward law of the common row-`M` increment vector.
    exact
      (integrable_map_measure hindicator_sm.aestronglyMeasurable hX_meas.aemeasurable).2
        hindicator_comp_int
  have hgauss_int :
      Integrable (Set.indicator (owner ⁻¹' S) f)
        (Measure.pi
          (fun q : Fin (partitionBoundIndex P M 1) ↦
            gaussianReal (0 : ℝ) (partitionNextPointUpTo P M q 1 - P M q))) := by
    -- Proof comment: the pushforward law of the common row-`M` increment vector is exactly the
    -- centered Gaussian product law recorded above.
    rw [← exercise21101WholeRowIncrementVector_map_eq_gaussianPi (hW := hW) (P := P) (m := M)]
    exact hindicator_int
  have hgauss_zero :
      ∫ z, Set.indicator (owner ⁻¹' S) f z
          ∂(Measure.pi
            (fun q : Fin (partitionBoundIndex P M 1) ↦
              gaussianReal (0 : ℝ) (partitionNextPointUpTo P M q 1 - P M q))) = 0 := by
    -- Proof comment: centered Gaussian product symmetry kills the odd descendant summand once the
    -- owner is known to be invariant under the same descendant-subtree sign flip.
    exact
      exercise21101Integral_indicator_preimage_eq_zero_of_gaussianPi_subtreeNeg
        (v := fun q : Fin (partitionBoundIndex P M 1) ↦
          partitionNextPointUpTo P M q 1 - P M q)
        (J := J) howner_fixed hf_anti hgauss_int
  -- Route correction: the proof now reduces the cylinder integral to a Gaussian product integral
  -- on one common refinement row. The only remaining missing ingredients are the two structural
  -- common-row factorization lemmas introduced just above.
  calc
    ∫ ω in (exercise21101FutureBlockArray W P (n + 1)) ⁻¹' C,
        exercise21101DescendantCrossSummand W P n i r ω ∂μ
        =
          ∫ ω,
            Set.indicator ((exercise21101FutureBlockArray W P (n + 1)) ⁻¹' C)
              (exercise21101DescendantCrossSummand W P n i r) ω ∂μ := by
            symm
            exact MeasureTheory.integral_indicator hfuture_meas
    _ = ∫ ω, Set.indicator (owner ⁻¹' S) f (X ω) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro ω
          exact (congrFun hindicator_comp_eq ω).symm
    _ = ∫ z, Set.indicator (owner ⁻¹' S) f z ∂μ.map X := by
          symm
          exact MeasureTheory.integral_map hX_meas.aemeasurable hindicator_sm.aestronglyMeasurable
    _ = ∫ z, Set.indicator (owner ⁻¹' S) f z
          ∂(Measure.pi
            (fun q : Fin (partitionBoundIndex P M 1) ↦
              gaussianReal (0 : ℝ) (partitionNextPointUpTo P M q 1 - P M q))) := by
            rw [exercise21101WholeRowIncrementVector_map_eq_gaussianPi (hW := hW) (P := P)
              (m := M)]
    _ = 0 := hgauss_zero

/-- Helper for Exercise 21.10.1: once the descendant summand vanishes on measurable-cylinder
preimages of the future-block array, it also vanishes on every stage-`n + 1` tail event. -/
lemma exercise21101DescendantCrossSummand_setIntegral_eq_zero_on_tailSet
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i r : ℕ) (hi : i < partitionBoundIndex P n 1)
    (hr :
      r <
        partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
          exercise21101CoarseEndpointRefinementIndex P n i (n + 1)) :
    ∀ s,
      MeasurableSet[
        (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
          (toDual (n + 1))] s →
        ∫ ω in s, exercise21101DescendantCrossSummand W P n i r ω ∂μ = 0 := by
  intro s hs
  let futureArray := exercise21101FutureBlockArray W P (n + 1)
  let G : Set (Set Ω) :=
    Set.preimage futureArray '' MeasureTheory.measurableCylinders (fun _ : ℕ ↦ ℕ → ℝ)
  let desc := exercise21101DescendantCrossSummand W P n i r
  have hGenerated :
      (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
          (toDual (n + 1)) =
        MeasurableSpace.generateFrom G := by
    -- Proof comment: the tail filtration stage is exactly the pullback of the product
    -- `σ`-algebra along the future-block array, and that product `σ`-algebra is generated by
    -- measurable cylinders.
    change
      MeasurableSpace.comap futureArray MeasurableSpace.pi =
        MeasurableSpace.generateFrom G
    calc
      MeasurableSpace.comap futureArray MeasurableSpace.pi
          =
            MeasurableSpace.comap futureArray
              (MeasurableSpace.generateFrom
                (MeasureTheory.measurableCylinders (fun _ : ℕ ↦ ℕ → ℝ))) := by
              rw [MeasureTheory.generateFrom_measurableCylinders]
      _ = MeasurableSpace.generateFrom G := by
            rw [MeasurableSpace.comap_generateFrom]
  have hGeneratedEmpty :
      (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
          (toDual (n + 1)) =
        MeasurableSpace.generateFrom (insert ∅ G) := by
    -- Proof comment: adjoining the empty generator makes the induction basis explicit without
    -- changing the generated tail `σ`-algebra.
    calc
      (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
            (toDual (n + 1)) =
          MeasurableSpace.generateFrom G := hGenerated
      _ = MeasurableSpace.generateFrom (insert ∅ G) := by
            symm
            exact MeasurableSpace.generateFrom_insert_empty (S := G)
  have hG : IsPiSystem G := by
    have hmc : IsPiSystem (MeasureTheory.measurableCylinders (fun _ : ℕ ↦ ℕ → ℝ)) := by
      simpa using
        (MeasureTheory.isPiSystem_measurableCylinders :
          IsPiSystem (MeasureTheory.measurableCylinders (fun _ : ℕ ↦ ℕ → ℝ)))
    intro t ht u hu htu
    rcases ht with ⟨t', ht', rfl⟩
    rcases hu with ⟨u', hu', rfl⟩
    have htu' : (t' ∩ u').Nonempty := by
      rcases htu with ⟨ω, hωt, hωu⟩
      exact ⟨futureArray ω, hωt, hωu⟩
    refine ⟨t' ∩ u', hmc t' ht' u' hu' htu', ?_⟩
    ext ω
    rfl
  have hdesc_int : Integrable desc μ :=
    exercise21101DescendantCrossSummand_integrable hW P n i r hi hr
  have hdesc_total :
      ∫ ω, desc ω ∂μ = 0 := by
    -- Proof comment: the whole space corresponds to the trivial measurable cylinder.
    simpa [desc, futureArray, MeasureTheory.setIntegral_univ] using
      exercise21101DescendantCrossSummand_setIntegral_eq_zero_on_tailCylinder
        hW P n i r hi hr Set.univ
        (MeasureTheory.univ_mem_measurableCylinders (fun _ : ℕ ↦ ℕ → ℝ))
  -- Proof comment: extend the cylinder-level symmetry from the generating `π`-system of
  -- future-block events to every measurable tail event by induction on intersections.
  refine
    MeasurableSpace.induction_on_inter hGeneratedEmpty hG.insert_empty ?_ ?_ ?_ ?_ s hs
  · simp
  · intro t ht
    rcases ht with rfl | ht
    · simp
    · rcases ht with ⟨C, hC, rfl⟩
      exact
        exercise21101DescendantCrossSummand_setIntegral_eq_zero_on_tailCylinder
          hW P n i r hi hr C hC
  · intro t ht h_ind
    have ht_meas : MeasurableSet t :=
      (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P).le
        (toDual (n + 1)) _ ht
    calc
      ∫ ω in tᶜ, desc ω ∂μ = ∫ ω, desc ω ∂μ - ∫ ω in t, desc ω ∂μ := by
          exact setIntegral_compl ht_meas hdesc_int
      _ = 0 - 0 := by rw [hdesc_total, h_ind]
      _ = 0 := by ring
  · intro f hfd hfm hf
    have hfm_meas : ∀ m, MeasurableSet (f m) := by
      intro m
      exact (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P).le
        (toDual (n + 1)) _ (hfm m)
    calc
      ∫ ω in ⋃ m, f m, desc ω ∂μ = ∑' m, ∫ ω in f m, desc ω ∂μ := by
          exact integral_iUnion hfm_meas hfd
            (hdesc_int.integrableOn.mono_set <| Set.iUnion_subset fun _ ↦ Set.subset_univ _)
      _ = ∑' m, (0 : ℝ) := by
            exact tsum_congr hf
      _ = 0 := by simp

/-- Helper for Exercise 21.10.1: once every descendant prefix-product summand has zero integral on
tail events, the whole refined cross remainder has zero integral on those same tail events. -/
lemma exercise21101RefinedBlockCross_setIntegral_eq_zero_on_tailSet
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i : ℕ) (hi : i < partitionBoundIndex P n 1) :
    ∀ s,
      MeasurableSet[
        (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
          (toDual (n + 1))] s →
        ∫ ω in s, exercise21101RefinedBlockCrossTerm W P n i ω ∂μ = 0 := by
  intro s hs
  -- Proof comment: rewrite the cross remainder as the finite sum of descendant summands and use
  -- the one-descendant symmetry statement termwise on the restricted integral.
  calc
    ∫ ω in s, exercise21101RefinedBlockCrossTerm W P n i ω ∂μ
        =
          ∫ ω in s,
            Finset.sum
              (Finset.range
                (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
                  exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
              (fun r ↦ exercise21101DescendantCrossSummand W P n i r ω) ∂μ := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun ω ↦ by
              simpa using congrFun
                (exercise21101RefinedBlockCrossTerm_eq_sum_descendantCrossSummand W P n i hi) ω
    _ =
        Finset.sum
          (Finset.range
            (partitionBoundIndex P (n + 1) (partitionNextPointUpTo P n i 1) -
              exercise21101CoarseEndpointRefinementIndex P n i (n + 1)))
          (fun r ↦ ∫ ω in s, exercise21101DescendantCrossSummand W P n i r ω ∂μ) := by
            rw [integral_finset_sum]
            intro r hr
            exact
              (exercise21101DescendantCrossSummand_integrable hW P n i r hi
                (Finset.mem_range.mp hr)).integrableOn
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro r hr
          exact
            exercise21101DescendantCrossSummand_setIntegral_eq_zero_on_tailSet
              hW P n i r hi (Finset.mem_range.mp hr) s hs

/-- Helper for Exercise 21.10.1: the conditional-expectation identity follows once the cross term
has zero integral on every stage-`n + 1` tail event. -/
lemma exercise21101RefinedBlockCross_condExp_eq_zero_of_setIntegral_eq_zero_on_tailSet
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i : ℕ)
    (hzero :
      ∀ s,
        MeasurableSet[
          (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
            (toDual (n + 1))] s →
          ∫ ω in s, exercise21101RefinedBlockCrossTerm W P n i ω ∂μ = 0) :
    μ[exercise21101RefinedBlockCrossTerm W P n i |
      (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
        (toDual (n + 1))] =ᵐ[μ] 0 := by
  -- Proof comment: conditional-expectation uniqueness reduces the target to the already isolated
  -- vanishing set integrals on the stage-`n + 1` tail `σ`-algebra.
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  letI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [MeasureTheory.measure_univ]
    simp
  letI :
      SigmaFinite
        (μ.trim
          ((backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P).le
            (toDual (n + 1)))) := by
    infer_instance
  symm
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    ((backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P).le
      (toDual (n + 1)))
    (exercise21101RefinedBlockCrossTerm_integrable hW P n i)
    (fun s hs hμs ↦ by
      refine ⟨aestronglyMeasurable_const, ?_⟩
      show HasFiniteIntegral (fun _ : Ω ↦ (0 : ℝ)) (μ.restrict s)
      simpa using (hasFiniteIntegral_zero (α := Ω) (μ := μ.restrict s) (ε := ℝ)))
    ?_ ?_
  · intro s hs hμs
    simp [hzero s hs]
  · simpa using
      (aestronglyMeasurable_const :
        AEStronglyMeasurable[
          (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
            (toDual (n + 1))] (fun _ : Ω ↦ (0 : ℝ)) μ)

lemma exercise21101RefinedBlockCross_condExp_eq_zero
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n i : ℕ) (hi : i < partitionBoundIndex P n 1) :
    μ[exercise21101RefinedBlockCrossTerm W P n i |
      (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
        (toDual (n + 1))] =ᵐ[μ] 0 := by
  -- Proof comment: the conditional-expectation uniqueness step is now packaged, so only the
  -- tail-event set-integral vanishing of the refined cross remainder remains, already reduced to
  -- one descendant summand at a time.
  exact
    exercise21101RefinedBlockCross_condExp_eq_zero_of_setIntegral_eq_zero_on_tailSet
      hW P n i
      (exercise21101RefinedBlockCross_setIntegral_eq_zero_on_tailSet hW P n i hi)

/-- Helper for Exercise 21.10.1: the backward process satisfies the one-step martingale identity
for the future-block tail filtration. -/
lemma exercise21101BackwardProcess_condExp_succ
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
      μ[exercise21101BackwardProcess W P (toDual n) |
        (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
          (toDual (n + 1))] =ᵐ[μ]
      exercise21101BackwardProcess W P (toDual (n + 1)) := by
  -- Route correction: the coarse-to-fine algebra is now packaged by
  -- `exercise21101BlockContribution_refine` and
  -- `exercise21101BackwardProcess_eq_sum_refinedBlockContribution`. The remaining step is purely
  -- probabilistic: isolate the refined cross remainders and prove that each has conditional
  -- expectation `0` with respect to the stage-`n + 1` future-block filtration by the planned
  -- finite-cylinder sign-symmetry argument.
  -- TODO: combine `exercise21101BackwardProcess_stepDifference_eq_sum_refinedCross` with
  -- `condExp_add`/`condExp_finset_sum`, then use
  -- `exercise21101RefinedBlockCross_condExp_eq_zero` to kill the cross-term sum and
  -- `condExp_of_stronglyMeasurable` for the stage-`n + 1` backward process.
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let crossSum : Ω → ℝ :=
    fun ω ↦
      Finset.sum (Finset.range (partitionBoundIndex P n 1))
        (fun i ↦ exercise21101RefinedBlockCrossTerm W P n i ω)
  have hnext_int :
      Integrable (exercise21101BackwardProcess W P (toDual (n + 1))) μ :=
    exercise21101BackwardProcess_integrable hW P (toDual (n + 1))
  have hcross_int : Integrable crossSum μ := by
    -- Proof comment: the cross remainder is a finite sum of the already-packaged integrable
    -- blockwise cross terms.
    refine integrable_finset_sum _ ?_
    intro i hi
    exact exercise21101RefinedBlockCrossTerm_integrable hW P n i
  have hcross_eq :
      crossSum =
        fun ω ↦
          Finset.sum (Finset.range (partitionBoundIndex P n 1))
            (fun i ↦ exercise21101RefinedBlockCrossTerm W P n i ω) := by
    rfl
  have hcross_fun_eq :
      (fun ω ↦
        Finset.sum (Finset.range (partitionBoundIndex P n 1))
          (fun i ↦ exercise21101RefinedBlockCrossTerm W P n i ω)) =
        ∑ i ∈ Finset.range (partitionBoundIndex P n 1), exercise21101RefinedBlockCrossTerm W P n i := by
    funext ω
    simp [Finset.sum_apply]
  have hnext_meas :
      StronglyMeasurable[
        (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
          (toDual (n + 1))] (exercise21101BackwardProcess W P (toDual (n + 1))) :=
    backwardProcess_stageStronglyMeasurable W hW.stronglyMeasurable P (n + 1)
  have hcross_zero :
      μ[crossSum |
        (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
          (toDual (n + 1))] =ᵐ[μ] 0 := by
    -- Proof comment: condition the finite sum termwise and collapse each block by the remaining
    -- refined-cross conditional-expectation lemma.
    calc
      μ[crossSum |
          (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
            (toDual (n + 1))] =ᵐ[μ]
          μ[(fun ω ↦
              Finset.sum (Finset.range (partitionBoundIndex P n 1))
                (fun i ↦ exercise21101RefinedBlockCrossTerm W P n i ω)) |
            (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
              (toDual (n + 1))] := by
              exact condExp_congr_ae <| Filter.EventuallyEq.of_eq hcross_eq
      _ =ᵐ[μ]
          μ[∑ i ∈ Finset.range (partitionBoundIndex P n 1), exercise21101RefinedBlockCrossTerm W P n i |
            (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
              (toDual (n + 1))] := by
              exact condExp_congr_ae <| Filter.EventuallyEq.of_eq hcross_fun_eq
      _ =ᵐ[μ]
          Finset.sum (Finset.range (partitionBoundIndex P n 1))
            (fun i ↦
              μ[exercise21101RefinedBlockCrossTerm W P n i |
                (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
                  (toDual (n + 1))]) := by
              exact
                condExp_finset_sum
                  (μ := μ)
                  (s := Finset.range (partitionBoundIndex P n 1))
                  (f := fun i ↦ exercise21101RefinedBlockCrossTerm W P n i)
                  (fun i _ ↦ exercise21101RefinedBlockCrossTerm_integrable hW P n i)
                  ((backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
                    (toDual (n + 1)))
      _ =ᵐ[μ]
          Finset.sum (Finset.range (partitionBoundIndex P n 1))
            (fun _ ↦ (0 : Ω → ℝ)) := by
              exact eventuallyEq_sum fun i hi ↦
                exercise21101RefinedBlockCross_condExp_eq_zero hW P n i
                  (Finset.mem_range.mp hi)
      _ =ᵐ[μ] 0 := by
            exact Filter.Eventually.of_forall fun _ ↦ by simp
  calc
    μ[exercise21101BackwardProcess W P (toDual n) |
        (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
          (toDual (n + 1))] =ᵐ[μ]
        μ[(fun ω ↦ exercise21101BackwardProcess W P (toDual (n + 1)) ω + crossSum ω) |
          (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
            (toDual (n + 1))] := by
          exact condExp_congr_ae <|
            Filter.EventuallyEq.of_eq
              (exercise21101BackwardProcess_stepDifference_eq_sum_refinedCross W P n)
    _ =ᵐ[μ]
        μ[exercise21101BackwardProcess W P (toDual (n + 1)) |
            (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
              (toDual (n + 1))] +
          μ[crossSum |
            (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
              (toDual (n + 1))] := by
          exact
            condExp_add hnext_int hcross_int
              ((backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
                (toDual (n + 1)))
    _ =ᵐ[μ]
        exercise21101BackwardProcess W P (toDual (n + 1)) +
          μ[crossSum |
            (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
              (toDual (n + 1))] := by
          exact
            (Filter.EventuallyEq.of_eq <|
              condExp_of_stronglyMeasurable
                ((backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P).le
                  (toDual (n + 1)))
                hnext_meas
                hnext_int).add Filter.EventuallyEq.rfl
    _ =ᵐ[μ] exercise21101BackwardProcess W P (toDual (n + 1)) + 0 := by
          exact Filter.EventuallyEq.rfl.add hcross_zero
    _ =ᵐ[μ] exercise21101BackwardProcess W P (toDual (n + 1)) := by
          exact Filter.Eventually.of_forall fun _ ↦ by simp

namespace IsBrownianMotion

-- Semantic recall note: the source-facing process is the centered `Yₙ` from the proof of
-- Theorem 21.64, not the raw backward quadratic-sum process.
/-- Exercise 21.10.1: for Brownian motion `W` and an admissible partition sequence `P`, the
random variables `Y_n` from the proof of Theorem 21.64, written as the reverse-time process of
centered squared partition increments up to time `1`, form a backwards martingale. -/
theorem partitionQuadraticVariationApproximationUpTo_one_backwardsMartingale
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    Martingale
      (exercise21101BackwardProcess W P)
      (Filtration.natural
        (exercise21101BackwardProcess W P)
        (exercise21101BackwardProcess_stronglyMeasurable W hW.stronglyMeasurable P))
      μ := by
  -- Route correction: the coarse-row filtration is not enough here; the textbook backward
  -- martingale uses a larger decreasing sign-symmetric filtration on the future refinements and
  -- then transfers to the natural filtration. The transfer step is now isolated in
  -- `exercise21101BackwardProcess_martingale_naturalFiltration_of_tailMartingale`, so only the
  -- owner martingale on the future-block filtration remains.
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hTail :
      Martingale
        (exercise21101BackwardProcess W P)
        (backwardQuadraticVariationTailFiltration W hW.stronglyMeasurable P)
        μ := by
    refine orderDualMartingale_of_condExp_succ ?_ ?_ ?_
    · intro n
      -- Proof comment: each reversed stage is already measurable in the future-block filtration at
      -- the matching reverse index.
      exact backwardProcess_stageStronglyMeasurable W hW.stronglyMeasurable P (ofDual n)
    · intro n
      -- Proof comment: every centered partition row is integrable because it is a finite sum of
      -- square-integrable Brownian block contributions.
      exact exercise21101BackwardProcess_integrable hW P (toDual n)
    · intro n
      -- Proof comment: this is the remaining owner-symmetry frontier for the future-block
      -- filtration.
      exact exercise21101BackwardProcess_condExp_succ hW P n
  -- Proof comment: once the larger decreasing filtration martingale is available, the transfer to
  -- the natural filtration is already packaged above.
  exact
    exercise21101BackwardProcess_martingale_naturalFiltration_of_tailMartingale
      (W := W) hW.stronglyMeasurable P hTail

end IsBrownianMotion

end ProbabilityTheory

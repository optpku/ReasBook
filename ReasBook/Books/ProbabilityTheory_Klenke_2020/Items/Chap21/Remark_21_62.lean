/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

/- Remark 21.62 splits into:
* the `core/canonical` owner-level closure statement that `𝒞_qv` is stable under `C¹`
  composition;
* a `bridge/view` witness-level Stieltjes formula for a chosen continuous square-variation path.

Domain-style sampling:
* `HasSquareVariationAlong` is the witness-level dyadic square-variation predicate from
  Definition 21.58.
* `HasContinuousSquareVariation` is the owner property for continuous paths with continuous square
  variation.
* `𝒞_qv` is the source-facing set-level view of that owner property.

Primitive data versus derived API:
* primitive data: the path `G` and the owner hypothesis `HasContinuousSquareVariation G`;
* derived API: closure under `C¹` composition, the set-level `𝒞_qv` bridge, and the chosen
  Stieltjes-measure identity for a particular continuous square-variation realization `VG`. -/

-- Semantic recall: the source-facing owner statement needs the canonical bracket path `⟨G⟩` and
-- its Stieltjes measure `d⟨G⟩`, so this file exposes those dyadic owners directly from the
-- `𝒞_qv` witness API.

variable {G VG : PathSpace}

namespace HasSquareVariationAlong

/-- Helper for Remark 21.62: the dyadic square-variation predicate exposes its defining
partition-sum limit at each fixed terminal time. -/
theorem tendsto_partition_sum
    {G : PathSpace} {V : PathwiseProcess}
    (hV : HasSquareVariationAlong G V) (T : NNReal) :
    Tendsto (dyadic_p_variation_sum 2 G T) atTop (nhds (V T)) :=
  HasSquareVariationAlongPartition.tendsto_partition_sum hV T

end HasSquareVariationAlong

/-- Helper for Remark 21.62: every dyadic partition point strictly before the truncation index
lies strictly below the time horizon `T`. -/
lemma dyadicPartition_lt_time_of_lt_boundIndex
    (n : ℕ) {T : NNReal} {k : ℕ}
    (hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    Definition2158.dyadicPartitionSequence n k < T := by
  -- Proof comment: otherwise `k` would already be a valid witness for the truncation index,
  -- contradicting its minimality.
  by_contra hnot
  have hle : T ≤ Definition2158.dyadicPartitionSequence n k := le_of_not_gt hnot
  have hmin :
      partitionBoundIndex Definition2158.dyadicPartitionSequence n T ≤ k :=
    Nat.find_min' (exists_partition_index_le_time Definition2158.dyadicPartitionSequence n T) hle
  exact (not_le_of_gt hk) hmin

/-- Helper for Remark 21.62: the dyadic truncation index is monotone in the time horizon. -/
lemma dyadicPartitionBoundIndex_monotone (n : ℕ) :
    Monotone (fun T ↦ partitionBoundIndex Definition2158.dyadicPartitionSequence n T) := by
  intro s t hst
  -- Proof comment: the witness index for `t` is also a valid witness for every smaller `s`.
  exact
    Nat.find_min'
      (exists_partition_index_le_time Definition2158.dyadicPartitionSequence n s)
      (le_trans hst (le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n t))

/-- Helper for Remark 21.62: the dyadic weighted quadratic sum obtained by weighting each squared
increment of `G` with the left endpoint value of `w`. -/
noncomputable def weightedDyadicSquareVariationSum
    (w : NNReal → ℝ) (G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum
    (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    (fun k ↦
      w (Definition2158.dyadicPartitionSequence n k) *
        (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
          G (Definition2158.dyadicPartitionSequence n k)) ^ 2)

/-- Helper for Remark 21.62: every dyadic left endpoint that contributes before
`partitionBoundIndex` lies in `Set.Icc 0 T`. -/
lemma dyadicPartitionPoint_mem_Icc_of_lt_partitionBoundIndex
    (n k : ℕ) (T : NNReal)
    (hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    Definition2158.dyadicPartitionSequence n k ∈ Set.Icc 0 T := by
  -- Proof comment: specialize the generic admissible-partition endpoint lemma to the dyadic row.
  constructor
  · exact bot_le
  · have hk_mem :=
      dyadicPartition_lt_time_of_lt_boundIndex n hk
    exact le_of_lt hk_mem

/-- Helper for Remark 21.62: the constant weight `1` recovers the usual dyadic square-variation
sum from Definition 21.58. -/
lemma weightedDyadicSquareVariationSum_one_eq
    (G : PathSpace) (T : NNReal) (n : ℕ) :
    weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n =
      dyadic_p_variation_sum 2 G T n := by
  -- Proof comment: normalize both sides to the same finite sum of squared increments.
  rw [weightedDyadicSquareVariationSum, dyadic_p_variation_sum, partitionPVariationSum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [sq_abs]

/-- Helper for Remark 21.62: the first dyadic partition index that reaches time `0` is `0`. -/
lemma dyadicPartitionBoundIndex_zero (n : ℕ) :
    partitionBoundIndex Definition2158.dyadicPartitionSequence n 0 = 0 := by
  -- Proof comment: admissible dyadic rows start at `0`, so the minimal index hitting time `0`
  -- is already the initial point.
  have hzero_reaches : (0 : NNReal) ≤ Definition2158.dyadicPartitionSequence n 0 := by
    simp [Definition2158.dyadicPartitionSequence]
  have hmin : partitionBoundIndex Definition2158.dyadicPartitionSequence n 0 ≤ 0 := by
    change Nat.find (exists_partition_index_le_time Definition2158.dyadicPartitionSequence n 0) ≤ 0
    exact
      Nat.find_min' (exists_partition_index_le_time Definition2158.dyadicPartitionSequence n 0)
        hzero_reaches
  exact Nat.le_zero.mp hmin

/-- Helper for Remark 21.62: the dyadic square-variation sum on the degenerate interval `[0,0]`
vanishes. -/
lemma dyadicSquareVariationSum_zero (G : PathSpace) (n : ℕ) :
    dyadic_p_variation_sum 2 G 0 n = 0 := by
  -- Proof comment: when the terminal time is `0`, the truncated dyadic partition contributes no
  -- nontrivial increment.
  rw [dyadic_p_variation_sum, partitionPVariationSum, dyadicPartitionBoundIndex_zero]
  simp

/-- Helper for Remark 21.62: every dyadic square-variation witness starts from `0`. -/
lemma hasSquareVariationAlong_zero
    {VG : PathwiseProcess} (hVG : HasSquareVariationAlong G VG) :
    VG 0 = 0 := by
  -- Proof comment: at time `0`, the approximating dyadic quadratic sums vanish identically, so
  -- their limit must also be `0`.
  have hlimVG :
      Tendsto (dyadic_p_variation_sum 2 G 0) atTop (nhds (VG 0)) :=
    HasSquareVariationAlong.tendsto_partition_sum hVG 0
  have hlim0 :
      Tendsto (dyadic_p_variation_sum 2 G 0) atTop (nhds (0 : ℝ)) := by
    have hzero : dyadic_p_variation_sum 2 G 0 = fun _ ↦ (0 : ℝ) := by
      funext n
      exact dyadicSquareVariationSum_zero G n
    rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlimVG hlim0

/-- Helper for Remark 21.62: the constant-weight dyadic quadratic sum is nonnegative term by term.
-/
lemma weightedDyadicSquareVariationSum_one_nonneg
    (G : PathSpace) (T : NNReal) (n : ℕ) :
    0 ≤ weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n := by
  -- Proof comment: each summand is a square, so the finite sum stays nonnegative.
  rw [weightedDyadicSquareVariationSum]
  refine Finset.sum_nonneg ?_
  intro k hk
  simpa using sq_nonneg
    (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      G (Definition2158.dyadicPartitionSequence n k))

/-- Helper for Remark 21.62: specializing the weight to `1` recovers the defining convergence
already packaged in `HasSquareVariationAlong`. -/
lemma tendsto_weightedDyadicSquareVariationSum_one
    {VG : PathwiseProcess} (hVG : HasSquareVariationAlong G VG) (T : NNReal) :
    Tendsto
      (weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T)
      atTop
      (nhds (VG T)) := by
  -- Proof comment: after collapsing the weight `1`, this is exactly the owner convergence axiom.
  have hone :
      weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T =
        dyadic_p_variation_sum 2 G T := by
    funext n
    exact weightedDyadicSquareVariationSum_one_eq G T n
  rw [hone]
  exact HasSquareVariationAlong.tendsto_partition_sum hVG T

/-- Helper for Remark 21.62: the constant-weight dyadic quadratic masses are eventually bounded by
`|VG T| + 1` once they converge to `VG T`. -/
lemma eventually_le_weightedDyadicSquareVariationSum_one_abs_add_one
    {VG : PathwiseProcess} (hVG : HasSquareVariationAlong G VG) (T : NNReal) :
    ∀ᶠ n in atTop,
      weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n ≤
        |VG T| + 1 := by
  -- Proof comment: convergence to `VG T` eventually traps the nonnegative sums inside the radius-1
  -- ball around `VG T`, and `|VG T|` absorbs the center.
  have hconst :
      Tendsto
        (weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T)
        atTop
        (nhds (VG T)) :=
    tendsto_weightedDyadicSquareVariationSum_one hVG T
  filter_upwards [hconst (Metric.ball_mem_nhds _ zero_lt_one)] with n hn
  have hball :
      |weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n - VG T| < 1 := by
    simpa [Metric.ball, Real.dist_eq] using hn
  have hupper :
      weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n < VG T + 1 := by
    have hright : weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n - VG T < 1 :=
      (abs_lt.mp hball).2
    linarith
  have hVG_abs : VG T + 1 ≤ |VG T| + 1 := by
    gcongr
    exact le_abs_self (VG T)
  exact le_of_lt (lt_of_lt_of_le hupper hVG_abs)

/-- Helper for Remark 21.62: any dyadic partition point strictly before the time horizon appears
strictly before the dyadic truncation index. -/
lemma lt_partitionBoundIndex_of_dyadicPartitionPoint_lt_time
    (n j : ℕ) (T : NNReal)
    (hjT : Definition2158.dyadicPartitionSequence n j < T) :
    j < partitionBoundIndex Definition2158.dyadicPartitionSequence n T := by
  -- Proof comment: if `j` were already beyond the truncation index, monotonicity of the dyadic row
  -- would force the `j`-th point to lie at or beyond `T`.
  have hstrict : StrictMono (Definition2158.dyadicPartitionSequence n) :=
    Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n
  by_contra hj
  have hbound : partitionBoundIndex Definition2158.dyadicPartitionSequence n T ≤ j :=
    Nat.not_lt.mp hj
  have hmono :
      Definition2158.dyadicPartitionSequence n
          (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) ≤
        Definition2158.dyadicPartitionSequence n j :=
    hstrict.monotone hbound
  exact not_le_of_gt hjT
    (le_trans
      (le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T)
      hmono)

/-- Helper for Remark 21.62: if the horizon is itself a dyadic partition point, then the dyadic
truncation index is exactly that point's index. -/
lemma partitionBoundIndex_eq_of_dyadicPartitionPoint
    (n k : ℕ) :
    partitionBoundIndex Definition2158.dyadicPartitionSequence n
        (Definition2158.dyadicPartitionSequence n k) = k := by
  have hstrict : StrictMono (Definition2158.dyadicPartitionSequence n) :=
    Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n
  apply Nat.le_antisymm
  · -- Proof comment: the `k`-th dyadic partition point already reaches the horizon.
    simpa [partitionBoundIndex] using
      (Nat.find_min'
        (exists_partition_index_le_time Definition2158.dyadicPartitionSequence n
          (Definition2158.dyadicPartitionSequence n k))
        (show
          Definition2158.dyadicPartitionSequence n k ≤
            Definition2158.dyadicPartitionSequence n k from le_rfl))
  · -- Proof comment: every smaller index stays strictly before the `k`-th dyadic partition point.
    exact Nat.le_of_not_gt fun hklt ↦
      (not_lt_of_ge
        (le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n
          (Definition2158.dyadicPartitionSequence n k)))
        (hstrict hklt)

/-- Helper for Remark 21.62: a coarse dyadic endpoint reappears in every finer dyadic row at the
explicit refinement index `2 ^ (n - m) * i`. -/
lemma dyadicRefinementIndex_spec
    (m i n : ℕ) (hmn : m ≤ n) :
    Definition2158.dyadicPartitionSequence n (2 ^ (n - m) * i) =
      Definition2158.dyadicPartitionSequence m i := by
  induction hmn with
  | refl =>
      -- Proof comment: on the same dyadic row, the refinement index is the original index.
      simp
  | @step n hmn ih =>
      have hindex :
          2 ^ ((n + 1) - m) * i = 2 * (2 ^ (n - m) * i) := by
        simp [Nat.succ_sub hmn, pow_succ, Nat.mul_left_comm, Nat.mul_comm]
      have hstep :
          Definition2158.dyadicPartitionSequence (n + 1)
              (2 * (2 ^ (n - m) * i)) =
            Definition2158.dyadicPartitionSequence n (2 ^ (n - m) * i) := by
        rw [Definition2158.dyadicPartitionSequence, Definition2158.dyadicPartitionSequence]
        rw [pow_succ, Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
        calc
          ((2 : NNReal) * ↑(2 ^ (n - m) * i)) * ((2 : NNReal)⁻¹ * ((2 : NNReal) ^ n)⁻¹)
              = ↑(2 ^ (n - m) * i) *
                  ((2 : NNReal) * (2 : NNReal)⁻¹ * ((2 : NNReal) ^ n)⁻¹) := by
                    ac_rfl
          _ = ↑(2 ^ (n - m) * i) * ((2 : NNReal) ^ n)⁻¹ := by
                simp
          _ = ↑(2 ^ (n - m) * i) / (2 : NNReal) ^ n := by
                rw [div_eq_mul_inv]
      -- Proof comment: each refinement step doubles the index while preserving the endpoint.
      rw [hindex]
      exact hstep.trans ih

/-- Helper for Remark 21.62: the weighted dyadic quadratic sum is additive in the weight. -/
lemma weightedDyadicSquareVariationSum_add
    (g h : NNReal → ℝ) (G : PathSpace) (T : NNReal) (n : ℕ) :
    weightedDyadicSquareVariationSum (fun s ↦ g s + h s) G T n =
      weightedDyadicSquareVariationSum g G T n +
        weightedDyadicSquareVariationSum h G T n := by
  -- Proof comment: expand the defining sum and distribute the coefficient over each square.
  rw [weightedDyadicSquareVariationSum, weightedDyadicSquareVariationSum,
    weightedDyadicSquareVariationSum]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]

/-- Helper for Remark 21.62: scaling the weight scales the weighted dyadic quadratic sum. -/
lemma weightedDyadicSquareVariationSum_const_mul
    (c : ℝ) (g : NNReal → ℝ) (G : PathSpace) (T : NNReal) (n : ℕ) :
    weightedDyadicSquareVariationSum (fun s ↦ c * g s) G T n =
      c * weightedDyadicSquareVariationSum g G T n := by
  -- Proof comment: factor the scalar `c` out of the defining dyadic finite sum.
  rw [weightedDyadicSquareVariationSum, weightedDyadicSquareVariationSum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  ring

/-- Helper for Remark 21.62: a constant weight is the constant multiple of the unweighted dyadic
quadratic mass. -/
lemma weightedDyadicSquareVariationSum_const
    (c : ℝ) (G : PathSpace) (T : NNReal) (n : ℕ) :
    weightedDyadicSquareVariationSum (fun _ ↦ c) G T n =
      c * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n := by
  -- Proof comment: specialize the scalar-multiplication lemma to the constant function `1`.
  simpa using weightedDyadicSquareVariationSum_const_mul c (fun _ ↦ (1 : ℝ)) G T n

/-- Helper for Remark 21.62: the weighted dyadic quadratic sum commutes with a finite sum of
weights. -/
lemma weightedDyadicSquareVariationSum_finset_sum
    {ι : Type*} (s : Finset ι) (w : ι → NNReal → ℝ)
    (G : PathSpace) (T : NNReal) (n : ℕ) :
    weightedDyadicSquareVariationSum
        (fun t ↦ Finset.sum s fun i ↦ w i t) G T n =
      Finset.sum s fun i ↦ weightedDyadicSquareVariationSum (w i) G T n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty weight family gives the zero weighted sum on both sides.
      simp [weightedDyadicSquareVariationSum]
  | @insert i s hi ih =>
      -- Proof comment: peel off one weight and use additivity of the weighted dyadic sum.
      simp [Finset.sum_insert, hi, weightedDyadicSquareVariationSum_add, ih]

/-- Helper for Remark 21.62: if the indicator weight is the prefix
`Set.indicator (Set.Icc 0 (Definition2158.dyadicPartitionSequence n j)) (fun _ ↦ 1)`, then the
weighted dyadic quadratic sum splits into the endpoint value plus a single boundary increment. -/
lemma weightedDyadicSquareVariationSum_indicatorIcc_eq_endpointPlusBoundary
    (G : PathSpace) (n j : ℕ) (T : NNReal)
    (hjT : Definition2158.dyadicPartitionSequence n j < T) :
    weightedDyadicSquareVariationSum
        (Set.indicator (Set.Icc 0 (Definition2158.dyadicPartitionSequence n j))
          (fun _ ↦ (1 : ℝ))) G T n =
      weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G
          (Definition2158.dyadicPartitionSequence n j) n +
        (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n j T) -
            G (Definition2158.dyadicPartitionSequence n j)) ^ 2 := by
  let term : ℕ → ℝ := fun k ↦
    Set.indicator (Set.Icc 0 (Definition2158.dyadicPartitionSequence n j))
        (fun _ ↦ (1 : ℝ)) (Definition2158.dyadicPartitionSequence n k) *
      (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
          G (Definition2158.dyadicPartitionSequence n k)) ^ 2
  have hstrict : StrictMono (Definition2158.dyadicPartitionSequence n) :=
    Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n
  have hjBound : j < partitionBoundIndex Definition2158.dyadicPartitionSequence n T :=
    lt_partitionBoundIndex_of_dyadicPartitionPoint_lt_time n j T hjT
  have hboundEq :
      partitionBoundIndex Definition2158.dyadicPartitionSequence n
          (Definition2158.dyadicPartitionSequence n j) = j :=
    partitionBoundIndex_eq_of_dyadicPartitionPoint n j
  have htruncate :
      weightedDyadicSquareVariationSum
          (Set.indicator (Set.Icc 0 (Definition2158.dyadicPartitionSequence n j))
            (fun _ ↦ (1 : ℝ))) G T n =
        Finset.sum (Finset.range (j + 1)) term := by
    rw [weightedDyadicSquareVariationSum]
    have hsplit :
        Finset.sum (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
            term =
          Finset.sum (Finset.range (j + 1)) term +
            Finset.sum
              (Finset.Ico (j + 1) (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
              term := by
      symm
      exact Finset.sum_range_add_sum_Ico term (Nat.succ_le_of_lt hjBound)
    have htail :
        Finset.sum
            (Finset.Ico (j + 1) (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
            term = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hjk : j < k := by
        exact lt_of_lt_of_le (Nat.lt_succ_self j) (Finset.mem_Ico.mp hk).1
      have hnotmem :
          Definition2158.dyadicPartitionSequence n k ∉
            Set.Icc 0 (Definition2158.dyadicPartitionSequence n j) := by
        have hlt :
            Definition2158.dyadicPartitionSequence n j <
              Definition2158.dyadicPartitionSequence n k :=
          hstrict hjk
        simp [Set.mem_Icc, not_le_of_gt hlt]
      -- Proof comment: once the left endpoint lies strictly beyond the cutoff point, the
      -- indicator coefficient vanishes.
      simp [hnotmem]
    rw [hsplit, htail, add_zero]
  have hprefix :
      Finset.sum (Finset.range j) term =
        weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G
          (Definition2158.dyadicPartitionSequence n j) n := by
    rw [weightedDyadicSquareVariationSum, hboundEq]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < j := Finset.mem_range.mp hk
    have hk_mem :
        Definition2158.dyadicPartitionSequence n k ∈
          Set.Icc 0 (Definition2158.dyadicPartitionSequence n j) := by
      constructor
      · exact bot_le
      · exact hstrict.monotone (Nat.le_of_lt hklt)
    have hk1_le : k + 1 ≤ j := Nat.succ_le_of_lt hklt
    have hk1_le_endpoint :
        Definition2158.dyadicPartitionSequence n (k + 1) ≤
          Definition2158.dyadicPartitionSequence n j :=
      hstrict.monotone hk1_le
    have hk1_le_time :
        Definition2158.dyadicPartitionSequence n (k + 1) ≤ T :=
      le_trans hk1_le_endpoint (le_of_lt hjT)
    -- Proof comment: before the endpoint `P n j`, both truncations use the same successor.
    simp [term, hk_mem, partitionNextPointUpTo, min_eq_left hk1_le_endpoint,
      min_eq_left hk1_le_time]
  have hj_mem :
      Definition2158.dyadicPartitionSequence n j ∈
        Set.Icc 0 (Definition2158.dyadicPartitionSequence n j) := by
    constructor
    · exact bot_le
    · exact le_rfl
  -- Proof comment: split off the unique nonzero boundary contribution at the cutoff endpoint.
  calc
    weightedDyadicSquareVariationSum
        (Set.indicator (Set.Icc 0 (Definition2158.dyadicPartitionSequence n j))
          (fun _ ↦ (1 : ℝ))) G T n
        = Finset.sum (Finset.range (j + 1)) term := htruncate
    _ = Finset.sum (Finset.range j) term + term j := by
          rw [Finset.sum_range_succ]
    _ = weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G
            (Definition2158.dyadicPartitionSequence n j) n +
          (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n j T) -
              G (Definition2158.dyadicPartitionSequence n j)) ^ 2 := by
          rw [hprefix]
          simp [term, hj_mem]

/-- Helper for Remark 21.62: after reindexing a coarse dyadic endpoint into a finer row, the
prefix-indicator weighted sum splits into the coarse endpoint value plus one boundary increment. -/
lemma weightedDyadicSquareVariationSum_indicatorIcc_eq_coarseEndpointPlusBoundary
    (G : PathSpace) (m i n : ℕ) (T : NNReal)
    (hmn : m ≤ n) (hiT : Definition2158.dyadicPartitionSequence m i < T) :
    weightedDyadicSquareVariationSum
        (Set.indicator (Set.Icc 0 (Definition2158.dyadicPartitionSequence m i))
          (fun _ ↦ (1 : ℝ))) G T n =
      weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G
          (Definition2158.dyadicPartitionSequence m i) n +
        (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (2 ^ (n - m) * i) T) -
            G (Definition2158.dyadicPartitionSequence m i)) ^ 2 := by
  let j := 2 ^ (n - m) * i
  have hjEq : Definition2158.dyadicPartitionSequence n j =
      Definition2158.dyadicPartitionSequence m i :=
    dyadicRefinementIndex_spec m i n hmn
  have hjT : Definition2158.dyadicPartitionSequence n j < T := by
    simpa [j, hjEq] using hiT
  -- Proof comment: rewrite the coarse endpoint through its explicit dyadic refinement index.
  simpa [j, hjEq] using
    weightedDyadicSquareVariationSum_indicatorIcc_eq_endpointPlusBoundary
      G n j T hjT

/-- Helper for Remark 21.62: a clipped successor interval in the `n`-th dyadic row has size at
most one dyadic mesh width whenever its left endpoint lies before `T`. -/
lemma edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh
    (n k : ℕ) (T : NNReal)
    (hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    edist (Definition2158.dyadicPartitionSequence n k)
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) ≤
      partitionMesh Definition2158.dyadicPartitionSequence n := by
  let P := Definition2158.dyadicPartitionSequence
  have hstrict : StrictMono (P n) :=
    by simpa [P] using Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n
  have hleft :
      P n k ≤ partitionNextPointUpTo P n k T := by
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt (hstrict (Nat.lt_succ_self k))
    · exact le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex n hk)
  have hright :
      partitionNextPointUpTo P n k T ≤ P n (k + 1) := by
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hdist :
      edist (P n k) (partitionNextPointUpTo P n k T) ≤ edist (P n k) (P n (k + 1)) := by
    have hsucc : P n k < P n (k + 1) := by
      exact hstrict (Nat.lt_succ_self k)
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

/-- Helper for Remark 21.62: after reindexing a coarse dyadic endpoint into a finer row, the next
clipped successor still lies within one dyadic mesh width of that coarse endpoint. -/
lemma edist_coarseDyadicEndpoint_partitionNextPointUpTo_le_mesh
    (m i n : ℕ) (T : NNReal) (hmn : m ≤ n)
    (hiT : Definition2158.dyadicPartitionSequence m i < T) :
    edist (Definition2158.dyadicPartitionSequence m i)
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
          (2 ^ (n - m) * i) T) ≤
      partitionMesh Definition2158.dyadicPartitionSequence n := by
  let P := Definition2158.dyadicPartitionSequence
  let j := 2 ^ (n - m) * i
  have hjEq : P n j = P m i :=
    dyadicRefinementIndex_spec m i n hmn
  have hjT : P n j < T := by
    simpa [j, hjEq] using hiT
  have hjBound : j < partitionBoundIndex P n T :=
    lt_partitionBoundIndex_of_dyadicPartitionPoint_lt_time n j T hjT
  -- Proof comment: rewrite the coarse endpoint through its explicit refinement index and use the
  -- one-mesh control for a single dyadic partition point.
  simpa [P, j, hjEq] using
    edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh n j T hjBound

/-- Helper for Remark 21.62: the canonical coarse staircase on `[0,T]` built from the `m`-th
dyadic row, written as a constant plus nested prefix indicators. -/
noncomputable def dyadicCoarseIccStep
    (w : NNReal → ℝ) (m : ℕ) (T : NNReal) : NNReal → ℝ :=
  fun s ↦
    w (Definition2158.dyadicPartitionSequence m
        (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) +
      Finset.sum (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
        fun i ↦
          (w (Definition2158.dyadicPartitionSequence m i) -
              w (Definition2158.dyadicPartitionSequence m (i + 1))) *
            Set.indicator
          (Set.Icc 0 (Definition2158.dyadicPartitionSequence m (i + 1)))
          (fun _ ↦ (1 : ℝ)) s

/-- Helper for Remark 21.62: the predecessor dyadic partition point immediately before the
truncation time `T` in the `n`-th row. When the truncation index is `0`, this defaults to the
initial point `0`. -/
noncomputable def dyadicPartitionPredecessorPoint
    (n : ℕ) (T : NNReal) : NNReal :=
  Definition2158.dyadicPartitionSequence n
    (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)

/-- Helper for Remark 21.62: the predecessor dyadic partition point lies in `[0,T]`. -/
lemma dyadicPartitionPredecessorPoint_le_time
    (n : ℕ) (T : NNReal) :
    dyadicPartitionPredecessorPoint n T ≤ T := by
  rcases Nat.eq_zero_or_pos (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) with
    hidx | hidx
  · -- Proof comment: if the truncation index is `0`, admissibility forces `T = 0`, so the
    -- predecessor point is the initial point.
    have hT0 : T = 0 := by
      have hle0 : T ≤ Definition2158.dyadicPartitionSequence n 0 := by
        simpa [hidx] using
          le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
      have hle0' : T ≤ 0 := by
        simpa [Definition2158.dyadicPartitionSequence] using hle0
      exact le_antisymm hle0' bot_le
    have hidx0 : partitionBoundIndex Definition2158.dyadicPartitionSequence n 0 = 0 := by
      simpa [hT0] using hidx
    simp [dyadicPartitionPredecessorPoint, hidx0, hT0, Definition2158.dyadicPartitionSequence]
  · -- Proof comment: otherwise the predecessor is exactly the partition point just before the
    -- first dyadic endpoint that reaches `T`.
    obtain ⟨k, hk⟩ :
        ∃ k : ℕ, partitionBoundIndex Definition2158.dyadicPartitionSequence n T = k + 1 :=
      ⟨partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1,
        (Nat.sub_add_cancel hidx).symm⟩
    have hk_lt : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hk_time : Definition2158.dyadicPartitionSequence n k < T :=
      dyadicPartition_lt_time_of_lt_boundIndex n hk_lt
    have hpred : dyadicPartitionPredecessorPoint n T = Definition2158.dyadicPartitionSequence n k := by
      simp [dyadicPartitionPredecessorPoint, hk]
    simpa [hpred] using le_of_lt hk_time

/-- Helper for Remark 21.62: the predecessor dyadic partition point lies within one dyadic mesh
width of the horizon. -/
lemma dyadicPartitionPredecessorPointWithinMesh
    (n : ℕ) (T : NNReal) :
    edist (dyadicPartitionPredecessorPoint n T) T ≤
      partitionMesh Definition2158.dyadicPartitionSequence n := by
  rcases Nat.eq_zero_or_pos (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) with
    hidx | hidx
  · -- Proof comment: if the truncation index is `0`, then `T = 0`, so the distance vanishes.
    have hT0 : T = 0 := by
      have hle0 : T ≤ Definition2158.dyadicPartitionSequence n 0 := by
        simpa [hidx] using
          le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
      have hle0' : T ≤ 0 := by
        simpa [Definition2158.dyadicPartitionSequence] using hle0
      exact le_antisymm hle0' bot_le
    have hidx0 : partitionBoundIndex Definition2158.dyadicPartitionSequence n 0 = 0 := by
      simpa [hT0] using hidx
    simp [dyadicPartitionPredecessorPoint, hidx0, hT0, Definition2158.dyadicPartitionSequence]
  · -- Proof comment: identify the predecessor with the dyadic endpoint just before the first
    -- endpoint beyond `T`, so the one-mesh interval estimate applies directly.
    obtain ⟨k, hk⟩ :
        ∃ k : ℕ, partitionBoundIndex Definition2158.dyadicPartitionSequence n T = k + 1 :=
      ⟨partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1,
        (Nat.sub_add_cancel hidx).symm⟩
    have hk_lt : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hT_le_next : T ≤ Definition2158.dyadicPartitionSequence n (k + 1) := by
      simpa [hk] using
        le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
    have hpred : dyadicPartitionPredecessorPoint n T = Definition2158.dyadicPartitionSequence n k := by
      simp [dyadicPartitionPredecessorPoint, hk]
    have hnext :
        partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T = T := by
      rw [partitionNextPointUpTo, min_eq_right hT_le_next]
    simpa [hpred, hnext] using
      edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh n k T hk_lt

/-- Helper for Remark 21.62: on `[0,T]`, the coarse dyadic staircase equals the weight sampled at
the predecessor dyadic endpoint of the evaluation time. -/
lemma dyadicCoarseIccStep_eq_partitionPredecessorValue
    (w : NNReal → ℝ) (m : ℕ) (T s : NNReal) (hsT : s ∈ Set.Icc 0 T) :
    dyadicCoarseIccStep w m T s = w (dyadicPartitionPredecessorPoint m s) := by
  let P := Definition2158.dyadicPartitionSequence
  let N := partitionBoundIndex P m T
  let q := partitionBoundIndex P m s
  have hstrict : StrictMono (P m) :=
    by simpa [P] using Definition2158.dyadicPartitionSequence_isAdmissible.strictMono m
  rcases Nat.eq_zero_or_pos q with hq | hq
  · have hs0 : s = 0 := by
      have hle0 : s ≤ P m 0 := by
        simpa [q, hq] using le_partitionBoundIndex_time P m s
      have hs_le_zero : s ≤ 0 := by
        simpa [P, Definition2158.dyadicPartitionSequence] using hle0
      exact le_antisymm hs_le_zero hsT.1
    have hpred : dyadicPartitionPredecessorPoint m s = P m 0 := by
      simp [dyadicPartitionPredecessorPoint, P, q, hq]
    have hall :
        ∀ i ∈ Finset.range (N - 1),
          Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ)) s = 1 := by
      intro i hi
      have hs_mem : s ∈ Set.Icc 0 (P m (i + 1)) := by
        subst hs0
        constructor
        · exact bot_le
        · exact bot_le
      simp [hs_mem]
    have hallTerm :
        ∀ i ∈ Finset.range (N - 1),
          (w (P m i) - w (P m (i + 1))) *
              Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ)) s =
            (w (P m i) - w (P m (i + 1))) := by
      intro i hi
      rw [hall i hi, mul_one]
    -- Proof comment: when `s = 0`, every prefix indicator is active and the staircase telescopes
    -- back to the initial endpoint value.
    calc
      dyadicCoarseIccStep w m T s
          = w (P m (N - 1)) +
              Finset.sum (Finset.range (N - 1)) (fun i ↦ w (P m i) - w (P m (i + 1))) := by
                rw [dyadicCoarseIccStep]
                simp only [P, N]
                congr 1
                refine Finset.sum_congr rfl ?_
                intro i hi
                exact hallTerm i hi
      _ = w (P m 0) := by
            rw [Finset.sum_range_sub']
            ring
      _ = w (dyadicPartitionPredecessorPoint m s) := by
            rw [hpred]
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, q = j + 1 := ⟨q - 1, (Nat.sub_add_cancel hq).symm⟩
    have hq_le_N : q ≤ N := by
      simpa [q, N, P] using dyadicPartitionBoundIndex_monotone m hsT.2
    have hj_lt_N : j < N := by
      have : j + 1 ≤ N := by
        simpa [hj] using hq_le_N
      exact lt_of_lt_of_le (Nat.lt_succ_self j) this
    have hj_le_Nm1 : j ≤ N - 1 := Nat.le_pred_of_lt hj_lt_N
    have hpred : dyadicPartitionPredecessorPoint m s = P m j := by
      simp [dyadicPartitionPredecessorPoint, P, q, hj]
    let term : ℕ → ℝ := fun i ↦
      (w (P m i) - w (P m (i + 1))) *
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
      have hi_lt_q : i + 1 < q := by
        simpa [hj] using Nat.succ_lt_succ hi_lt
      have hi_time : P m (i + 1) < s :=
        dyadicPartition_lt_time_of_lt_boundIndex m hi_lt_q
      have hnotmem : s ∉ Set.Icc 0 (P m (i + 1)) := by
        simp [Set.mem_Icc, not_le_of_gt hi_time]
      -- Proof comment: before the predecessor interval, the prefix indicators are off.
      simp [hnotmem]
    have hright :
        Finset.sum (Finset.Ico j (N - 1)) term =
          Finset.sum (Finset.Ico j (N - 1)) (fun i ↦ w (P m i) - w (P m (i + 1))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hq_time : s ≤ P m (j + 1) := by
        simpa [q, hj] using le_partitionBoundIndex_time P m s
      have hi_ge : j ≤ i := (Finset.mem_Ico.mp hi).1
      have hs_le : s ≤ P m (i + 1) := by
        refine le_trans hq_time ?_
        exact hstrict.monotone (Nat.succ_le_succ hi_ge)
      have hs_mem : s ∈ Set.Icc 0 (P m (i + 1)) := ⟨hsT.1, hs_le⟩
      -- Proof comment: from the predecessor interval onward, every prefix indicator is active.
      simp [term, hs_mem]
    have htail :
        Finset.sum (Finset.Ico j (N - 1)) (fun i ↦ w (P m i) - w (P m (i + 1))) =
          w (P m j) - w (P m (N - 1)) := by
      rw [Finset.sum_Ico_eq_sub _ hj_le_Nm1, Finset.sum_range_sub', Finset.sum_range_sub']
      ring
    -- Proof comment: separating the off and on regions makes the remaining finite difference
    -- sum telescope to the predecessor endpoint value.
    calc
      dyadicCoarseIccStep w m T s
          = w (P m (N - 1)) + Finset.sum (Finset.range (N - 1)) term := by
              simp [dyadicCoarseIccStep, P, N, term]
      _ = w (P m (N - 1)) +
            (Finset.sum (Finset.range j) term + Finset.sum (Finset.Ico j (N - 1)) term) := by
              rw [hsplit]
      _ = w (P m (N - 1)) + Finset.sum (Finset.Ico j (N - 1)) term := by
              simp [hleft]
      _ = w (P m (N - 1)) +
            Finset.sum (Finset.Ico j (N - 1)) (fun i ↦ w (P m i) - w (P m (i + 1))) := by
              rw [hright]
      _ = w (P m j) := by
            rw [htail]
            ring
      _ = w (dyadicPartitionPredecessorPoint m s) := by
            rw [hpred]

/-- Helper for Remark 21.62: some coarse dyadic staircase uniformly approximates a continuous
weight on `[0,T]`. -/
lemma exists_dyadicCoarseIccStep_uniformApprox
    (w : NNReal → ℝ) (hw : Continuous w)
    (T : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∀ s ∈ Set.Icc 0 T, |w s - dyadicCoarseIccStep w m T s| ≤ ε := by
  have hUC :
      UniformContinuousOn w (Set.Icc 0 T) :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).uniformContinuousOn_of_continuous
      hw.continuousOn
  rcases (Metric.uniformContinuousOn_iff_le.mp hUC) ε hε with ⟨δ, hδ, hδclose⟩
  have hmesh :
      ∀ᶠ m in atTop,
        partitionMesh Definition2158.dyadicPartitionSequence m ≤ ENNReal.ofReal δ := by
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
          (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) with
      ⟨M, hM⟩
    exact Filter.eventually_atTop.2 ⟨M, hM⟩
  rcases Filter.eventually_atTop.1 hmesh with ⟨m, hm⟩
  have hm0 :
      partitionMesh Definition2158.dyadicPartitionSequence m ≤ ENNReal.ofReal δ :=
    hm m le_rfl
  refine ⟨m, ?_⟩
  intro s hs
  have hpred_mem : dyadicPartitionPredecessorPoint m s ∈ Set.Icc 0 T := by
    constructor
    · exact bot_le
    · exact le_trans (dyadicPartitionPredecessorPoint_le_time m s) hs.2
  have hpred_dist :
      dist s (dyadicPartitionPredecessorPoint m s) ≤ δ := by
    have hedist :
        edist s (dyadicPartitionPredecessorPoint m s) ≤
          partitionMesh Definition2158.dyadicPartitionSequence m := by
      simpa [edist_comm] using dyadicPartitionPredecessorPointWithinMesh m s
    have hedist' :
        edist s (dyadicPartitionPredecessorPoint m s) ≤ ENNReal.ofReal δ :=
      le_trans hedist hm0
    exact
      (ENNReal.ofReal_le_ofReal_iff hδ.le).mp
        (by simpa [edist_dist] using hedist')
  have hclose :
      dist (w s) (w (dyadicPartitionPredecessorPoint m s)) ≤ ε :=
    hδclose s hs (dyadicPartitionPredecessorPoint m s) hpred_mem hpred_dist
  -- Proof comment: the staircase value is exactly the predecessor-point sample, and that sample
  -- stays within one dyadic mesh width of the evaluation time.
  simpa [Real.dist_eq, dyadicCoarseIccStep_eq_partitionPredecessorValue w m T s hs] using hclose

/-- Helper for Remark 21.62: the clipped successor of a coarse dyadic endpoint converges back to
that endpoint, so the corresponding boundary square vanishes. -/
lemma tendsto_coarseDyadicEndpoint_boundaryIncrementSq_zero
    (G : PathSpace) (m i : ℕ) (T : NNReal)
    (hiT : Definition2158.dyadicPartitionSequence m i < T) :
    Tendsto
      (fun n : ℕ ↦
        (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
              (2 ^ (n - m) * i) T) -
            G (Definition2158.dyadicPartitionSequence m i)) ^ 2)
      atTop
      (nhds 0) := by
  let P := Definition2158.dyadicPartitionSequence
  let q : ℕ → NNReal := fun n ↦
    if hmn : m ≤ n then
      partitionNextPointUpTo P n (2 ^ (n - m) * i) T
    else
      P m i
  have hq :
      Tendsto q atTop (nhds (P m i)) := by
    rw [tendsto_iff_edist_tendsto_0]
    -- Proof comment: after row `m`, every clipped successor stays within one dyadic mesh width of
    -- the coarse endpoint, and the dyadic mesh tends to `0`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      Definition2158.tendsto_partitionMesh_dyadicPartitionSequence
      (fun n ↦ bot_le) ?_
    intro n
    by_cases hmn : m ≤ n
    · simpa [q, P, hmn, edist_comm] using
        edist_coarseDyadicEndpoint_partitionNextPointUpTo_le_mesh m i n T hmn hiT
    · simp [q, P, hmn]
  have hGq :
      Tendsto (fun n : ℕ ↦ G (q n)) atTop (nhds (G (P m i))) :=
    let hGcontAt : ContinuousAt G (P m i) := G.continuous.continuousAt
    hGcontAt.tendsto.comp hq
  have hdiff :
      Tendsto (fun n : ℕ ↦ G (q n) - G (P m i)) atTop (nhds 0) := by
    -- Proof comment: continuity of the path turns endpoint convergence into vanishing increments.
    have hconst :
        Tendsto (fun _ : ℕ ↦ G (P m i)) atTop (nhds (G (P m i))) :=
      tendsto_const_nhds
    simpa using hGq.sub hconst
  have hsq :
      Tendsto (fun n : ℕ ↦ (G (q n) - G (P m i)) ^ 2) atTop (nhds 0) := by
    -- Proof comment: squaring preserves the convergence of the boundary increment to `0`.
    simpa [pow_two] using hdiff.mul hdiff
  have hevent :
      (fun n : ℕ ↦ (G (q n) - G (P m i)) ^ 2) =ᶠ[atTop]
        (fun n : ℕ ↦
          (G (partitionNextPointUpTo P n (2 ^ (n - m) * i) T) -
              G (P m i)) ^ 2) := by
    filter_upwards [eventually_ge_atTop m] with n hmn
    simp [q, P, hmn]
  exact Tendsto.congr' hevent hsq

/-- Helper for Remark 21.62: the weighted dyadic sum for a single prefix indicator converges to
the matching endpoint value of the square-variation path. -/
lemma tendsto_weightedDyadicSquareVariationSum_indicatorIcc
    {VG : PathwiseProcess} (hVG : HasSquareVariationAlong G VG)
    (m i : ℕ) (T : NNReal)
    (hiT : Definition2158.dyadicPartitionSequence m i < T) :
    Tendsto
      (fun n : ℕ ↦
        weightedDyadicSquareVariationSum
          (Set.indicator (Set.Icc 0 (Definition2158.dyadicPartitionSequence m i))
            (fun _ ↦ (1 : ℝ))) G T n)
      atTop
      (nhds (VG (Definition2158.dyadicPartitionSequence m i))) := by
  have hendpoint :
      Tendsto
        (fun n : ℕ ↦
          weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G
            (Definition2158.dyadicPartitionSequence m i) n)
        atTop
        (nhds (VG (Definition2158.dyadicPartitionSequence m i))) :=
    tendsto_weightedDyadicSquareVariationSum_one hVG
      (Definition2158.dyadicPartitionSequence m i)
  have hboundary :
      Tendsto
        (fun n : ℕ ↦
          (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                (2 ^ (n - m) * i) T) -
              G (Definition2158.dyadicPartitionSequence m i)) ^ 2)
        atTop
        (nhds 0) :=
    tendsto_coarseDyadicEndpoint_boundaryIncrementSq_zero G m i T hiT
  have hsplit :
      (fun n : ℕ ↦
        weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G
            (Definition2158.dyadicPartitionSequence m i) n +
          (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n
                (2 ^ (n - m) * i) T) -
              G (Definition2158.dyadicPartitionSequence m i)) ^ 2) =ᶠ[atTop]
        (fun n : ℕ ↦
          weightedDyadicSquareVariationSum
            (Set.indicator (Set.Icc 0 (Definition2158.dyadicPartitionSequence m i))
              (fun _ ↦ (1 : ℝ))) G T n) := by
    filter_upwards [eventually_ge_atTop m] with n hmn
    symm
    exact
      weightedDyadicSquareVariationSum_indicatorIcc_eq_coarseEndpointPlusBoundary
        G m i n T hmn hiT
  -- Proof comment: the indicator weight is the endpoint constant-weight sum plus one boundary
  -- square, and that boundary square tends to `0`.
  simpa using Tendsto.congr' hsplit (hendpoint.add hboundary)

/-- Helper for Remark 21.62: the coarse dyadic `Set.Icc`-staircase weight has the expected limit
as a finite linear combination of endpoint square-variation values. -/
lemma tendsto_weightedDyadicSquareVariationSum_coarseIccStep_linearCombination
    (w : NNReal → ℝ) {VG : PathwiseProcess}
    (hVG : HasSquareVariationAlong G VG)
    (m : ℕ) (T : NNReal) :
    Tendsto
      (fun n : ℕ ↦ weightedDyadicSquareVariationSum (dyadicCoarseIccStep w m T) G T n)
      atTop
      (nhds
        (w (Definition2158.dyadicPartitionSequence m
              (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) * VG T +
          Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
            fun i ↦
              (w (Definition2158.dyadicPartitionSequence m i) -
                  w (Definition2158.dyadicPartitionSequence m (i + 1))) *
                VG (Definition2158.dyadicPartitionSequence m (i + 1)))) := by
  let P := Definition2158.dyadicPartitionSequence
  let N := partitionBoundIndex P m T
  let cLast : ℝ := w (P m (N - 1))
  let coeff : ℕ → ℝ := fun i ↦ w (P m i) - w (P m (i + 1))
  let indicatorWeight : ℕ → NNReal → ℝ := fun i s ↦
    coeff i * Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ)) s
  have hconst :
      Tendsto
        (fun n : ℕ ↦
          cLast * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n)
        atTop
        (nhds (cLast * VG T)) := by
    -- Proof comment: the constant part of the staircase uses the known constant-weight
    -- convergence of the dyadic square-variation sums.
    simpa [cLast] using
      tendsto_const_nhds.mul (tendsto_weightedDyadicSquareVariationSum_one hVG T)
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i *
              weightedDyadicSquareVariationSum
                (Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ))) G T n)
        atTop
        (nhds
          (Finset.sum (Finset.range (N - 1)) fun i ↦ coeff i * VG (P m (i + 1)))) := by
    -- Proof comment: each prefix-indicator term converges to the matching endpoint value, and a
    -- finite sum preserves convergence.
    refine tendsto_finset_sum _ fun i hi ↦ ?_
    have hi_lt : i < N - 1 := Finset.mem_range.mp hi
    have hi_succ_lt : i + 1 < (N - 1) + 1 := Nat.succ_lt_succ hi_lt
    have hN : 0 < N := by
      exact lt_of_lt_of_le (Nat.zero_lt_succ i)
        (le_trans (Nat.succ_le_of_lt hi_lt) (Nat.sub_le _ _))
    have hN_eq : (N - 1) + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hN)
    have hi' : i + 1 < N := by
      simpa [hN_eq] using hi_succ_lt
    have hiT : P m (i + 1) < T :=
      dyadicPartition_lt_time_of_lt_boundIndex m hi'
    simpa [coeff] using
      tendsto_const_nhds.mul
        (tendsto_weightedDyadicSquareVariationSum_indicatorIcc hVG m (i + 1) T hiT)
  have hsumRewrite :
      ∀ n : ℕ,
        weightedDyadicSquareVariationSum
            (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s) G T n =
          Finset.sum (Finset.range (N - 1)) fun i ↦
            weightedDyadicSquareVariationSum (indicatorWeight i) G T n := by
    intro n
    -- Proof comment: the weighted dyadic quadratic sum is linear in finite sums of weights.
    rw [weightedDyadicSquareVariationSum_finset_sum]
  have hcoeffRewrite :
      ∀ n : ℕ,
        (Finset.sum (Finset.range (N - 1)) fun i ↦
            weightedDyadicSquareVariationSum (indicatorWeight i) G T n) =
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i *
              weightedDyadicSquareVariationSum
                (Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ))) G T n := by
    intro n
    -- Proof comment: factor the scalar coefficient out of each indicator summand.
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [weightedDyadicSquareVariationSum_const_mul]
  -- Proof comment: rewrite the staircase weight into its constant part plus the finite indicator
  -- family, then combine the two convergence statements above.
  convert hconst.add hsum using 1
  ext n
  calc
    weightedDyadicSquareVariationSum (dyadicCoarseIccStep w m T) G T n =
        weightedDyadicSquareVariationSum (fun _ ↦ cLast) G T n +
          weightedDyadicSquareVariationSum
            (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s) G T n := by
      change
        weightedDyadicSquareVariationSum
            (fun s ↦ (fun _ ↦ cLast) s +
              Finset.sum (Finset.range (N - 1)) (fun i ↦ indicatorWeight i s)) G T n =
          weightedDyadicSquareVariationSum (fun _ ↦ cLast) G T n +
            weightedDyadicSquareVariationSum
              (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s) G T n
      simpa [dyadicCoarseIccStep, P, N, cLast, coeff, indicatorWeight] using
        weightedDyadicSquareVariationSum_add
          (fun _ ↦ cLast)
          (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s)
          G T n
    _ =
        cLast * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n +
          weightedDyadicSquareVariationSum
            (fun s ↦ Finset.sum (Finset.range (N - 1)) fun i ↦ indicatorWeight i s) G T n := by
      rw [weightedDyadicSquareVariationSum_const]
    _ =
        cLast * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n +
          Finset.sum (Finset.range (N - 1)) fun i ↦
            weightedDyadicSquareVariationSum (indicatorWeight i) G T n := by
      rw [hsumRewrite n]
    _ =
        cLast * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n +
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i *
              weightedDyadicSquareVariationSum
                (Set.indicator (Set.Icc 0 (P m (i + 1))) (fun _ ↦ (1 : ℝ))) G T n := by
      rw [hcoeffRewrite n]

/-- Helper for Remark 21.62: a uniform coefficient bound on `[0,T]` controls the difference of the
corresponding weighted dyadic quadratic sums by the unweighted quadratic mass. -/
lemma abs_sub_weightedDyadicSquareVariationSum_le
    (g h : NNReal → ℝ) (G : PathSpace) (T : NNReal) (ε : ℝ)
    (hε : ∀ s ∈ Set.Icc 0 T, |g s - h s| ≤ ε)
    (n : ℕ) :
    |weightedDyadicSquareVariationSum g G T n -
        weightedDyadicSquareVariationSum h G T n| ≤
      ε * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n := by
  have hrewrite :
      weightedDyadicSquareVariationSum g G T n -
          weightedDyadicSquareVariationSum h G T n =
        Finset.sum (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            (g (Definition2158.dyadicPartitionSequence n k) -
                h (Definition2158.dyadicPartitionSequence n k)) *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2) := by
    -- Proof comment: rewrite the difference of weighted sums as one sum with coefficient `g - h`.
    rw [weightedDyadicSquareVariationSum, weightedDyadicSquareVariationSum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k hk
    ring
  calc
    |weightedDyadicSquareVariationSum g G T n -
        weightedDyadicSquareVariationSum h G T n|
        = |Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
            (fun k ↦
              (g (Definition2158.dyadicPartitionSequence n k) -
                  h (Definition2158.dyadicPartitionSequence n k)) *
                (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                    G (Definition2158.dyadicPartitionSequence n k)) ^ 2)| := by
            rw [hrewrite]
    _ ≤ Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            |(g (Definition2158.dyadicPartitionSequence n k) -
                h (Definition2158.dyadicPartitionSequence n k)) *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2|) := by
      exact
        Finset.abs_sum_le_sum_abs
          (fun k ↦
            (g (Definition2158.dyadicPartitionSequence n k) -
                h (Definition2158.dyadicPartitionSequence n k)) *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2)
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    _ = Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            |g (Definition2158.dyadicPartitionSequence n k) -
                h (Definition2158.dyadicPartitionSequence n k)| *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hsquare_nonneg :
          0 ≤
            (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                G (Definition2158.dyadicPartitionSequence n k)) ^ 2 := by
        exact
          sq_nonneg
            (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              G (Definition2158.dyadicPartitionSequence n k))
      rw [abs_mul, abs_of_nonneg hsquare_nonneg]
    _ ≤ Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            ε *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2) := by
      -- Proof comment: apply the uniform coefficient bound at every dyadic left endpoint in
      -- `Set.Icc 0 T`.
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk' : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T :=
        Finset.mem_range.mp hk
      have hk_mem :
          Definition2158.dyadicPartitionSequence n k ∈ Set.Icc 0 T :=
        dyadicPartitionPoint_mem_Icc_of_lt_partitionBoundIndex n k T hk'
      have hpoint :
          |g (Definition2158.dyadicPartitionSequence n k) -
              h (Definition2158.dyadicPartitionSequence n k)| ≤ ε :=
        hε _ hk_mem
      have hsquare_nonneg :
          0 ≤
            (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                G (Definition2158.dyadicPartitionSequence n k)) ^ 2 := by
        exact
          sq_nonneg
            (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              G (Definition2158.dyadicPartitionSequence n k))
      have habs :
          |(g (Definition2158.dyadicPartitionSequence n k) -
                h (Definition2158.dyadicPartitionSequence n k)) *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2|
            =
              |g (Definition2158.dyadicPartitionSequence n k) -
                  h (Definition2158.dyadicPartitionSequence n k)| *
                (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                    G (Definition2158.dyadicPartitionSequence n k)) ^ 2 := by
        rw [abs_mul, abs_of_nonneg hsquare_nonneg]
      simpa [habs] using mul_le_mul_of_nonneg_right hpoint hsquare_nonneg
    _ = ε * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n := by
      -- Proof comment: factor out the constant coefficient and recover the unweighted mass.
      rw [weightedDyadicSquareVariationSum, Finset.mul_sum]
      simp only [one_mul]

/-- Helper for Remark 21.62: the derivative weight `s ↦ (deriv f (G s)) ^ 2` is continuous on
`[0,∞)` when `f ∈ C¹(ℝ)` and `G` is continuous. -/
lemma continuous_derivSq_comp
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (G : PathSpace) :
    Continuous fun s : NNReal ↦ (deriv f (G s)) ^ 2 := by
  -- Proof comment: `ContDiff ℝ 1` gives continuity of `deriv f`, and composition with `G`
  -- preserves continuity before squaring.
  exact (hf.continuous_deriv_one.comp G.continuous).pow 2

/-- Helper for Remark 21.62: the monotone full dyadic square-sum obtained by discarding the
terminal clipped increment whenever the untruncated successor has already crossed `T`. -/
noncomputable def dyadicSquareVariationFullSum
    (H : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum
    (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    (fun k ↦
      if Definition2158.dyadicPartitionSequence n (k + 1) ≤ T then
        Real.rpow
          (|H (Definition2158.dyadicPartitionSequence n (k + 1)) -
              H (Definition2158.dyadicPartitionSequence n k)|)
          2
      else 0)

/-- Helper for Remark 21.62: the full dyadic square-sum is monotone in the time horizon for each
fixed dyadic row. -/
lemma dyadicSquareVariationFullSum_monotone
    (H : PathSpace) (n : ℕ) :
    Monotone (fun T ↦ dyadicSquareVariationFullSum H T n) := by
  intro s t hst
  let term : NNReal → ℕ → ℝ := fun T k ↦
    if Definition2158.dyadicPartitionSequence n (k + 1) ≤ T then
      Real.rpow
        (|H (Definition2158.dyadicPartitionSequence n (k + 1)) -
            H (Definition2158.dyadicPartitionSequence n k)|)
        2
    else 0
  have hterm_nonneg :
      ∀ T k, 0 ≤ term T k := by
    intro T k
    by_cases hk : Definition2158.dyadicPartitionSequence n (k + 1) ≤ T
    · simpa [term, hk, sq_abs] using
        sq_nonneg
          (H (Definition2158.dyadicPartitionSequence n (k + 1)) -
            H (Definition2158.dyadicPartitionSequence n k))
    · simp [term, hk]
  have hsubset :
      Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n s) ⊆
        Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t) :=
    Finset.range_subset_range.2 (dyadicPartitionBoundIndex_monotone n hst)
  calc
    dyadicSquareVariationFullSum H s n
        = Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n s))
            (term s) := by
              simp [dyadicSquareVariationFullSum, term]
    _ ≤ Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n s))
          (term t) := by
      -- Proof comment: on the common initial range, enlarging the terminal time can only switch
      -- zero summands to the corresponding square term.
      refine Finset.sum_le_sum ?_
      intro k hk
      by_cases hs' : Definition2158.dyadicPartitionSequence n (k + 1) ≤ s
      · have ht' : Definition2158.dyadicPartitionSequence n (k + 1) ≤ t :=
          le_trans hs' hst
        simp [hs', ht', sq_abs]
      · by_cases ht' : Definition2158.dyadicPartitionSequence n (k + 1) ≤ t
        · have hsq_nonneg :
              0 ≤
                (H (Definition2158.dyadicPartitionSequence n (k + 1)) -
                    H (Definition2158.dyadicPartitionSequence n k)) ^ 2 := by
            positivity
          simpa [hs', ht', sq_abs] using hsq_nonneg
        · simp [hs', ht']
    _ ≤ Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n t))
          (term t) := by
      -- Proof comment: extending the range adds only nonnegative square terms.
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro k hk hknot
        exact hterm_nonneg t k)
    _ = dyadicSquareVariationFullSum H t n := by
      simp [dyadicSquareVariationFullSum, term]

/-- Helper for Remark 21.62: the predecessor of the dyadic truncation index is the boundary point
whose distance to `T` is controlled by the dyadic mesh. -/
noncomputable def dyadicSquareVariationBoundaryPoint
    (T : NNReal) (n : ℕ) : NNReal :=
  Definition2158.dyadicPartitionSequence n
    (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)

/-- Helper for Remark 21.62: the dyadic boundary point converges to `T`. -/
lemma tendsto_dyadicSquareVariationBoundaryPoint
    (T : NNReal) :
    Tendsto (fun n ↦ dyadicSquareVariationBoundaryPoint T n) atTop (nhds T) := by
  have hpow :
      Tendsto (fun n : ℕ ↦ (((2 : NNReal)⁻¹) ^ n : NNReal)) atTop (nhds (0 : NNReal)) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hpow_real :
      Tendsto (fun n : ℕ ↦ ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ)) atTop (nhds (0 : ℝ)) :=
    NNReal.tendsto_coe.2 hpow
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  rcases Metric.tendsto_atTop.1 hpow_real ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  rcases Nat.eq_zero_or_pos (partitionBoundIndex Definition2158.dyadicPartitionSequence n T) with
    hidx | hidx
  · have hT0 : T = 0 := by
      have hle0 : T ≤ Definition2158.dyadicPartitionSequence n 0 := by
        simpa [hidx] using
          le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
      have hle0' : T ≤ 0 := by
        simpa [Definition2158.dyadicPartitionSequence] using hle0
      exact le_antisymm hle0' bot_le
    have hidx0 : partitionBoundIndex Definition2158.dyadicPartitionSequence n 0 = 0 := by
      simpa [hT0] using hidx
    have hdist :
        dist (dyadicSquareVariationBoundaryPoint T n) T = 0 := by
      rw [hT0, dyadicSquareVariationBoundaryPoint, hidx0, Definition2158.dyadicPartitionSequence]
      simp
    simpa [hdist] using hε
  · obtain ⟨k, hk⟩ :
      ∃ k : ℕ,
        partitionBoundIndex Definition2158.dyadicPartitionSequence n T = k + 1 :=
      ⟨partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1,
        (Nat.sub_add_cancel hidx).symm⟩
    have hk_lt :
        k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hk_time :
        Definition2158.dyadicPartitionSequence n k < T :=
      dyadicPartition_lt_time_of_lt_boundIndex n hk_lt
    have hk_leT : Definition2158.dyadicPartitionSequence n k ≤ T := le_of_lt hk_time
    have hT_le_next :
        T ≤ Definition2158.dyadicPartitionSequence n (k + 1) := by
      simpa [hk] using
        le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n T
    have hboundary :
        dyadicSquareVariationBoundaryPoint T n =
          Definition2158.dyadicPartitionSequence n k := by
      simp [dyadicSquareVariationBoundaryPoint, hk]
    have hnext_ge :
        Definition2158.dyadicPartitionSequence n k ≤
          Definition2158.dyadicPartitionSequence n (k + 1) := by
      rw [Definition2158.dyadicPartitionSequence, Definition2158.dyadicPartitionSequence]
      exact
        (div_le_div_iff_of_pos_right (show 0 < (2 : NNReal) ^ n by positivity)).2 <| by
          exact_mod_cast Nat.le_succ k
    have hdist_le_gap :
        dist (dyadicSquareVariationBoundaryPoint T n) T ≤
          ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ) := by
      have hdist_edist :
          edist (dyadicSquareVariationBoundaryPoint T n) T ≤
            edist (Definition2158.dyadicPartitionSequence n k)
              (Definition2158.dyadicPartitionSequence n (k + 1)) := by
        -- Proof comment: the boundary point and `T` lie inside a single dyadic mesh interval.
        rw [hboundary, edist_nndist, edist_nndist, NNReal.nndist_eq, NNReal.nndist_eq,
          tsub_eq_zero_of_le hk_leT, tsub_eq_zero_of_le hnext_ge,
          max_eq_right, max_eq_right]
        · exact_mod_cast tsub_le_tsub_right hT_le_next _
        · exact zero_le _
        · exact zero_le _
      have hgap :
          edist (Definition2158.dyadicPartitionSequence n k)
              (Definition2158.dyadicPartitionSequence n (k + 1)) =
            (((2 : ℝ≥0∞)⁻¹) ^ n) := by
        simpa using Definition2158.dyadicPartitionSequence_succGap n k
      have hdist_edist' :
          edist (dyadicSquareVariationBoundaryPoint T n) T ≤ (((2 : ℝ≥0∞)⁻¹) ^ n) := by
        simpa [hgap] using hdist_edist
      have hpow_finite : (((2 : ℝ≥0∞)⁻¹) ^ n) ≠ ∞ := by simp
      have hdist_finite : edist (dyadicSquareVariationBoundaryPoint T n) T ≠ ∞ :=
        edist_ne_top _ _
      have hdist_real :
          dist (dyadicSquareVariationBoundaryPoint T n) T ≤ ((((2 : ℝ≥0∞)⁻¹) ^ n).toReal) := by
        exact (ENNReal.toReal_le_toReal hdist_finite hpow_finite).2 hdist_edist'
      simpa using hdist_real
    have hgap_lt : ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ) < ε := by
      simpa using hN n hn
    exact lt_of_le_of_lt hdist_le_gap hgap_lt

/-- Helper for Remark 21.62: replacing the clipped terminal dyadic increment by `0` changes the
dyadic square-variation sum by at most the square of the last boundary increment. -/
lemma dyadicSquareVariationSum_sub_fullSum_le_boundary
    (H : PathSpace) (T : NNReal) (n : ℕ) :
    0 ≤ dyadic_p_variation_sum 2 H T n - dyadicSquareVariationFullSum H T n ∧
      dyadic_p_variation_sum 2 H T n - dyadicSquareVariationFullSum H T n ≤
        (H T - H (dyadicSquareVariationBoundaryPoint T n)) ^ 2 := by
  let P := Definition2158.dyadicPartitionSequence
  let core : ℕ → ℝ := fun j ↦ Real.rpow (|H (P n (j + 1)) - H (P n j)|) 2
  rcases Nat.eq_zero_or_pos (partitionBoundIndex P n T) with hidx | hidx
  · -- Proof comment: if the truncation index is `0`, both sums are empty and the boundary point is
    -- exactly `0 = T`.
    have hT0 : T = 0 := by
      have hle0 : T ≤ P n 0 := by
        simpa [hidx] using le_partitionBoundIndex_time P n T
      have hle0' : T ≤ 0 := by
        simpa [P, Definition2158.dyadicPartitionSequence] using hle0
      exact le_antisymm hle0' bot_le
    subst hT0
    simp [dyadicSquareVariationSum_zero, dyadicSquareVariationFullSum,
      dyadicSquareVariationBoundaryPoint, dyadicPartitionBoundIndex_zero,
      Definition2158.dyadicPartitionSequence]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, partitionBoundIndex P n T = k + 1 :=
      ⟨partitionBoundIndex P n T - 1, (Nat.sub_add_cancel hidx).symm⟩
    have hk_lt :
        k < partitionBoundIndex P n T := by
      rw [hk]
      exact Nat.lt_succ_self k
    have hT_le_next : T ≤ P n (k + 1) := by
      simpa [hk] using le_partitionBoundIndex_time P n T
    have hboundary :
        dyadicSquareVariationBoundaryPoint T n = P n k := by
      simp [dyadicSquareVariationBoundaryPoint, hk, P]
    have hboundary_sq :
        Real.rpow (|H T - H (P n k)|) 2 =
          (H T - H (dyadicSquareVariationBoundaryPoint T n)) ^ 2 := by
      rw [hboundary]
      simp [sq_abs]
    have hdyadic :
        dyadic_p_variation_sum 2 H T n =
          Finset.sum (Finset.range k) core +
            (H T - H (dyadicSquareVariationBoundaryPoint T n)) ^ 2 := by
      -- Proof comment: split off the final truncated increment at index `k`; earlier intervals are
      -- fully contained in `[0,T]`.
      rw [dyadic_p_variation_sum, partitionPVariationSum, hk, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro j hj
        have hj_succ_lt : j + 1 < partitionBoundIndex P n T := by
          simpa [hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hj_time : P n (j + 1) < T :=
          dyadicPartition_lt_time_of_lt_boundIndex n hj_succ_lt
        rw [partitionNextPointUpTo, min_eq_left (le_of_lt hj_time)]
      · rw [partitionNextPointUpTo, min_eq_right hT_le_next, hboundary_sq]
    have hfull :
        dyadicSquareVariationFullSum H T n =
          Finset.sum (Finset.range k) core +
            (if P n (k + 1) ≤ T then
              Real.rpow (|H (P n (k + 1)) - H (P n k)|) 2
            else 0) := by
      -- Proof comment: the full sum has the same initial block, followed by the final untruncated
      -- interval only when its right endpoint has already reached `T`.
      rw [dyadicSquareVariationFullSum, hk, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl ?_
        intro j hj
        have hj_succ_lt : j + 1 < partitionBoundIndex P n T := by
          simpa [hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hj_time : P n (j + 1) < T :=
          dyadicPartition_lt_time_of_lt_boundIndex n hj_succ_lt
        rw [if_pos (le_of_lt hj_time)]
    by_cases hlast : P n (k + 1) ≤ T
    · have hlast_eq : P n (k + 1) = T := le_antisymm hlast hT_le_next
      have hlast_sq :
          Real.rpow (|H (P n (k + 1)) - H (P n k)|) 2 =
            (H T - H (dyadicSquareVariationBoundaryPoint T n)) ^ 2 := by
        rw [hlast_eq, hboundary]
        simp [sq_abs]
      rw [hdyadic, hfull, if_pos hlast, hlast_sq]
      constructor
      · ring_nf
        norm_num
      · ring_nf
        nlinarith [sq_nonneg (H T - H (dyadicSquareVariationBoundaryPoint T n))]
    · rw [hdyadic, hfull, if_neg hlast, add_zero]
      constructor
      · ring_nf
        nlinarith [sq_nonneg (H T - H (dyadicSquareVariationBoundaryPoint T n))]
      · ring_nf
        rfl

/-- Helper for Remark 21.62: the full dyadic square-sums have the same limit as the clipped
dyadic square-variation sums. -/
lemma tendsto_dyadicSquareVariationFullSum
    {H : PathSpace} {brH : PathwiseProcess} (hH : HasSquareVariationAlong H brH) (T : NNReal) :
    Tendsto (dyadicSquareVariationFullSum H T) atTop (nhds (brH T)) := by
  have hpoint :
      Tendsto (fun n ↦ dyadicSquareVariationBoundaryPoint T n) atTop (nhds T) :=
    tendsto_dyadicSquareVariationBoundaryPoint T
  have hboundary :
      Tendsto
        (fun n ↦ (H T - H (dyadicSquareVariationBoundaryPoint T n)) ^ 2)
        atTop
        (nhds 0) := by
    -- Proof comment: the omitted boundary increment vanishes because the dyadic boundary point
    -- tends to `T`.
    have hcont : Continuous fun x : NNReal ↦ (H T - H x) ^ 2 :=
      (continuous_const.sub H.continuous).pow 2
    let hcontAt : ContinuousAt (fun x : NNReal ↦ (H T - H x) ^ 2) T := hcont.continuousAt
    simpa using hcontAt.tendsto.comp hpoint
  have hdiff :
      Tendsto
        (fun n ↦ dyadic_p_variation_sum 2 H T n - dyadicSquareVariationFullSum H T n)
        atTop
        (nhds 0) := by
    refine squeeze_zero
      (fun n ↦ (dyadicSquareVariationSum_sub_fullSum_le_boundary H T n).1)
      (fun n ↦ (dyadicSquareVariationSum_sub_fullSum_le_boundary H T n).2)
      hboundary
  have hsum : Tendsto (dyadic_p_variation_sum 2 H T) atTop (nhds (brH T)) :=
    HasSquareVariationAlong.tendsto_partition_sum hH T
  -- Proof comment: subtract the vanishing boundary error from the clipped dyadic sums.
  simpa [sub_eq_add_neg, sub_sub_cancel] using hsum.sub hdiff

/-- Helper for Remark 21.62: every continuous dyadic square-variation witness starts at `0` and
is monotone in time. -/
lemma hasSquareVariationAlong_zero_and_monotone
    {H : PathSpace} {brH : PathSpace} (hH : HasSquareVariationAlong H brH) :
    brH 0 = 0 ∧ Monotone brH := by
  refine ⟨hasSquareVariationAlong_zero hH, ?_⟩
  intro s t hst
  -- Proof comment: compare the two monotone full-sum approximations pointwise and pass to the
  -- limit using the shared convergence theorem.
  exact
    le_of_tendsto_of_tendsto'
      (tendsto_dyadicSquareVariationFullSum hH s)
      (tendsto_dyadicSquareVariationFullSum hH t)
      (fun n ↦ dyadicSquareVariationFullSum_monotone H n hst)

/-- Helper for Remark 21.62: a continuous monotone path starting at `0` admits a Stieltjes-measure
realization on intervals `Set.Icc 0 T`. -/
lemma stieltjesMeasure_of_monotonePath_zero
    (V : PathSpace) (hmono : Monotone V) (hzero : V 0 = 0) :
    ∃ μ : Measure NNReal, ∀ T : NNReal, V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μ := by
  refine ⟨(hmono.stieltjesFunction).measure, ?_⟩
  intro T
  have hright : Function.rightLim V T = V T := by
    let hVcontWithinT : ContinuousWithinAt V (Set.Ici T) T :=
      (V.continuous.continuousAt).continuousWithinAt
    exact hVcontWithinT.rightLim_eq
  have hleft : Function.leftLim (hmono.stieltjesFunction) 0 = 0 := by
    have hleft_eval :
        Function.leftLim (hmono.stieltjesFunction) 0 = hmono.stieltjesFunction 0 :=
      leftLim_eq_of_isBot isBot_bot
    have hright0 : Function.rightLim V 0 = 0 := by
      let hVcontWithin0 : ContinuousWithinAt V (Set.Ici (0 : NNReal)) 0 :=
        (V.continuous.continuousAt).continuousWithinAt
      simpa [hzero] using hVcontWithin0.rightLim_eq
    have hzero_eval : hmono.stieltjesFunction 0 = 0 := by
      rw [Monotone.stieltjesFunction_eq]
      exact hright0
    exact hleft_eval.trans hzero_eval
  have hnonneg : 0 ≤ V T := by
    rw [← hzero]
    exact hmono bot_le
  have hmass :
      ((hmono.stieltjesFunction).measure).real (Set.Icc 0 T) = V T := by
    -- Proof comment: `measure_Icc` computes the interval mass by the endpoint increment of `V`.
    rw [Measure.real_def, StieltjesFunction.measure_Icc]
    simp [Monotone.stieltjesFunction_eq, hright, hleft, hnonneg]
  simpa using hmass.symm

/-- Helper for Remark 21.62: the canonical Stieltjes measure of a continuous monotone path has no
atoms. -/
lemma noAtoms_stieltjesMeasure_of_continuous_monotone
    (V : PathSpace) (hmono : Monotone V) :
    NoAtoms (hmono.stieltjesFunction).measure := by
  have hstieltjes :
      (hmono.stieltjesFunction : NNReal → ℝ) = V := by
    -- Proof comment: continuity identifies the Stieltjes right-limit representative with the
    -- original path pointwise.
    funext x
    rw [Monotone.stieltjesFunction_eq]
    let hVcontWithinX : ContinuousWithinAt V (Set.Ici x) x :=
      (V.continuous.continuousAt).continuousWithinAt
    exact hVcontWithinX.rightLim_eq
  refine ⟨?_⟩
  intro a
  rw [StieltjesFunction.measure_singleton]
  have hvalue : hmono.stieltjesFunction a = V a := by
    -- Proof comment: specialize the pointwise identification of the Stieltjes function at `a`.
    simpa using congrFun hstieltjes a
  have hleft : Function.leftLim (hmono.stieltjesFunction) a = V a := by
    -- Proof comment: once the representative is rewritten back to `V`, left continuity of the
    -- continuous path removes the singleton jump.
    rw [hstieltjes]
    let hVcontWithinA : ContinuousWithinAt V (Set.Iic a) a :=
      (V.continuous.continuousAt).continuousWithinAt
    exact hVcontWithinA.leftLim_eq
  rw [hvalue, hleft, sub_self, ENNReal.ofReal_zero]

/-- Helper for Remark 21.62: the canonical Stieltjes measure of a continuous monotone path
recovers the path values on intervals `Set.Icc 0 T`. -/
lemma stieltjesFunction_measure_realizes_path
    (V : PathSpace) (hmono : Monotone V) (hzero : V 0 = 0) :
    ∀ T : NNReal, V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂((hmono.stieltjesFunction).measure) := by
  intro T
  have hright : Function.rightLim V T = V T := by
    -- Proof comment: continuity removes the right-limit correction in the Stieltjes function.
    let hVcontWithinT : ContinuousWithinAt V (Set.Ici T) T :=
      (V.continuous.continuousAt).continuousWithinAt
    exact hVcontWithinT.rightLim_eq
  have hleft : Function.leftLim (hmono.stieltjesFunction) 0 = 0 := by
    -- Proof comment: continuity at the left endpoint identifies the Stieltjes left limit with the
    -- actual initial value `V 0 = 0`.
    have hleft_eval :
        Function.leftLim (hmono.stieltjesFunction) 0 = hmono.stieltjesFunction 0 :=
      leftLim_eq_of_isBot isBot_bot
    have hright0 : Function.rightLim V 0 = 0 := by
      let hVcontWithin0 : ContinuousWithinAt V (Set.Ici (0 : NNReal)) 0 :=
        (V.continuous.continuousAt).continuousWithinAt
      simpa [hzero] using hVcontWithin0.rightLim_eq
    have hzero_eval : hmono.stieltjesFunction 0 = 0 := by
      rw [Monotone.stieltjesFunction_eq]
      exact hright0
    exact hleft_eval.trans hzero_eval
  have hnonneg : 0 ≤ V T := by
    -- Proof comment: monotonicity and the normalization `V 0 = 0` force the path to stay
    -- nonnegative on `[0, ∞)`.
    rw [← hzero]
    exact hmono bot_le
  have hmass :
      ((hmono.stieltjesFunction).measure).real (Set.Icc 0 T) = V T := by
    -- Proof comment: `measure_Icc` computes the interval mass by the endpoint increment of the
    -- associated Stieltjes function.
    rw [Measure.real_def, StieltjesFunction.measure_Icc]
    simp [Monotone.stieltjesFunction_eq, hright, hleft, hnonneg]
  simpa using hmass.symm

/-- Helper for Remark 21.62: a chosen continuous dyadic square-variation witness admits a
canonical Stieltjes-measure realization. -/
noncomputable def squareVariationStieltjesMeasure
    {G VG : PathSpace} (hVG : HasSquareVariationAlong G VG) : Measure NNReal :=
  ((((hasSquareVariationAlong_zero_and_monotone hVG).2).stieltjesFunction).measure)

/-- Helper for Remark 21.62: the canonical Stieltjes measure attached to `VG` realizes `VG` on
intervals `Set.Icc 0 T`. -/
lemma squareVariationStieltjesMeasure_realizes_path
    {G VG : PathSpace} (hVG : HasSquareVariationAlong G VG) :
    ∀ T : NNReal,
      VG T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂(squareVariationStieltjesMeasure hVG) := by
  obtain ⟨hzero, hmono⟩ := hasSquareVariationAlong_zero_and_monotone hVG
  simpa [squareVariationStieltjesMeasure] using
    stieltjesFunction_measure_realizes_path VG hmono hzero

/-- Helper for Remark 21.62: the canonical Stieltjes measure of `VG` has finite mass on each
interval `Set.Icc 0 T`. -/
lemma squareVariationStieltjesMeasure_Icc_lt_top
    {G VG : PathSpace} (hVG : HasSquareVariationAlong G VG) (T : NNReal) :
    squareVariationStieltjesMeasure hVG (Set.Icc 0 T) ≠ ⊤ := by
  obtain ⟨hzero, hmono⟩ := hasSquareVariationAlong_zero_and_monotone hVG
  have hright : Function.rightLim VG T = VG T := by
    exact (VG.continuous.continuousAt.continuousWithinAt).rightLim_eq
  have hleft : Function.leftLim (hmono.stieltjesFunction) 0 = 0 := by
    have hleft_eval :
        Function.leftLim (hmono.stieltjesFunction) 0 = hmono.stieltjesFunction 0 :=
      leftLim_eq_of_isBot isBot_bot
    have hright0 : Function.rightLim VG 0 = 0 := by
      simpa [hzero] using
        (VG.continuous.continuousAt.continuousWithinAt.rightLim_eq (a := (0 : NNReal)))
    have hzero_eval : hmono.stieltjesFunction 0 = 0 := by
      rw [Monotone.stieltjesFunction_eq]
      exact hright0
    exact hleft_eval.trans hzero_eval
  have hnonneg : 0 ≤ VG T := by
    rw [← hzero]
    exact hmono bot_le
  -- Proof comment: `measure_Icc` computes the mass explicitly as an `ENNReal.ofReal` value.
  rw [squareVariationStieltjesMeasure, StieltjesFunction.measure_Icc]
  simp [Monotone.stieltjesFunction_eq, hright, hleft]

/-- Helper for Remark 21.62: a chosen continuous dyadic square-variation witness admits the
canonical Stieltjes-measure realization attached to `VG`. -/
lemma exists_stieltjesMeasure_of_hasSquareVariation
    (G : PathSpace) (VG : PathSpace) (hVG : HasSquareVariationAlong G VG) :
    ∃ μG : Measure NNReal,
      μG = squareVariationStieltjesMeasure hVG ∧
        ∀ T : NNReal, VG T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μG := by
  refine ⟨squareVariationStieltjesMeasure hVG, rfl, ?_⟩
  exact squareVariationStieltjesMeasure_realizes_path hVG

/-- Helper for Remark 21.62: the canonical dyadic square-variation bracket `⟨G⟩` attached to the
owner hypothesis `hG : G ∈ 𝒞_qv`. -/
noncomputable def continuousSquareVariationBracket
    (G : PathSpace) (hG : G ∈ 𝒞_qv) : PathSpace :=
  Classical.choose ((mem_𝒞_qv_iff G).1 hG)

/-- Helper for Remark 21.62: the canonical dyadic bracket `⟨G⟩` is a square-variation witness of
`G`. -/
theorem continuousSquareVariationBracket_spec
    (G : PathSpace) (hG : G ∈ 𝒞_qv) :
    HasSquareVariationAlong G (continuousSquareVariationBracket G hG) :=
  Classical.choose_spec ((mem_𝒞_qv_iff G).1 hG)

/-- Helper for Remark 21.62: the canonical Stieltjes measure `d⟨G⟩` attached to the dyadic
bracket of `G`. -/
noncomputable def continuousSquareVariationMeasure
    (G : PathSpace) (hG : G ∈ 𝒞_qv) : Measure NNReal :=
  squareVariationStieltjesMeasure (continuousSquareVariationBracket_spec G hG)

/-- Helper for Remark 21.62: the canonical Stieltjes primitive with density
`s ↦ (deriv f (G s)) ^ 2` is a continuous path. -/
lemma continuous_stieltjesIntegral_derivSq_comp
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (G VG : PathSpace) (hmonoVG : Monotone VG) :
    Continuous
      (fun T : NNReal ↦
        ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2 ∂((hmonoVG.stieltjesFunction).measure)) := by
  let w : NNReal → ℝ := fun s ↦ (deriv f (G s)) ^ 2
  let μ : Measure NNReal := (hmonoVG.stieltjesFunction).measure
  have hw : Continuous w := continuous_derivSq_comp f hf G
  have hμ_noAtoms : NoAtoms μ := by
    simpa [μ] using noAtoms_stieltjesMeasure_of_continuous_monotone VG hmonoVG
  have hrepr :
      (fun T : NNReal ↦ ∫ s in Set.Icc 0 T, w s ∂μ) =
        fun T : NNReal ↦ ∫ s, Set.indicator (Set.Icc 0 T) w s ∂μ := by
    -- Proof comment: rewrite each truncated primitive as the unrestricted integral of the
    -- matching interval indicator.
    funext T
    rw [MeasureTheory.integral_indicator measurableSet_Icc]
  rw [hrepr]
  rw [continuous_iff_continuousAt]
  intro T₀
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : NNReal) (T₀ + 1), ‖w s‖ ≤ C :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) (T₀ + 1))).exists_bound_of_continuousOn
      hw.continuousOn
  have hC_nonneg : 0 ≤ C := by
    have hzero_mem : (0 : NNReal) ∈ Set.Icc (0 : NNReal) (T₀ + 1) := by
      constructor
      · rfl
      · exact bot_le
    exact le_trans (norm_nonneg _) (hC 0 hzero_mem)
  let bound : NNReal → ℝ := Set.indicator (Set.Icc (0 : NNReal) (T₀ + 1)) (fun _ ↦ C)
  have hbound_integrableOn :
      IntegrableOn (fun _ : NNReal ↦ C) (Set.Icc (0 : NNReal) (T₀ + 1)) μ := by
    refine Measure.integrableOn_of_bounded
      (μ := μ) (s := Set.Icc (0 : NNReal) (T₀ + 1))
      ?_ (by fun_prop) (M := C) ?_
    · exact (measure_Icc_lt_top (μ := μ) (a := (0 : NNReal)) (b := T₀ + 1)).ne
    · filter_upwards [MeasureTheory.ae_restrict_mem (μ := μ) measurableSet_Icc] with s hs
      simp [Real.norm_eq_abs, abs_of_nonneg hC_nonneg]
  have hbound_integrable : Integrable bound μ := by
    -- Proof comment: the dominating function is the constant bound restricted to the compact
    -- interval `[0, T₀ + 1]`.
    exact (integrable_indicator_iff measurableSet_Icc).2 hbound_integrableOn
  have hF_meas :
      ∀ᶠ T in 𝓝 T₀,
        AEStronglyMeasurable (Set.indicator (Set.Icc 0 T) w) μ := by
    exact Filter.Eventually.of_forall fun T ↦ hw.aestronglyMeasurable.indicator measurableSet_Icc
  have h_bound :
      ∀ᶠ T in 𝓝 T₀,
        ∀ᵐ s ∂μ, ‖Set.indicator (Set.Icc 0 T) w s‖ ≤ bound s := by
    have hT₀_lt : T₀ < T₀ + 1 := by
      exact lt_add_of_pos_right T₀ zero_lt_one
    filter_upwards [Iio_mem_nhds hT₀_lt] with T hT
    filter_upwards with s
    by_cases hsT : s ∈ Set.Icc (0 : NNReal) T
    · have hsBound : s ∈ Set.Icc (0 : NNReal) (T₀ + 1) := by
        constructor
        · exact hsT.1
        · exact le_trans hsT.2 (le_of_lt hT)
      simpa [bound, hsT, hsBound] using hC s hsBound
    · by_cases hsBound : s ∈ Set.Icc (0 : NNReal) (T₀ + 1)
      · simpa [bound, hsT, hsBound] using hC_nonneg
      · simp [bound, hsT, hsBound]
  have h_lim :
      ∀ᵐ s ∂μ,
        Tendsto (fun T : NNReal ↦ Set.indicator (Set.Icc 0 T) w s) (𝓝 T₀)
          (𝓝 (Set.indicator (Set.Icc 0 T₀) w s)) := by
    letI : NoAtoms μ := hμ_noAtoms
    have hsingleton : μ {T₀} = 0 := measure_singleton T₀
    filter_upwards [compl_mem_ae_iff.mpr hsingleton] with s hs
    rcases lt_or_gt_of_ne hs with hslt | hsgt
    · have hT₀_mem : s ∈ Set.Icc (0 : NNReal) T₀ := ⟨bot_le, le_of_lt hslt⟩
      have h_event :
          (fun T : NNReal ↦ Set.indicator (Set.Icc 0 T) w s) =ᶠ[𝓝 T₀] fun _ ↦ w s := by
        filter_upwards [Ioi_mem_nhds hslt] with T hT
        have hs_mem : s ∈ Set.Icc (0 : NNReal) T := ⟨bot_le, le_of_lt hT⟩
        simp [hs_mem]
      -- Proof comment: away from the endpoint `T₀`, the prefix indicator eventually stabilizes.
      have hconst :
          Tendsto (fun _ : NNReal ↦ w s) (𝓝 T₀)
            (𝓝 (Set.indicator (Set.Icc 0 T₀) w s)) := by
        simp [hT₀_mem]
      exact hconst.congr' h_event.symm
    · have hT₀_not_mem : s ∉ Set.Icc (0 : NNReal) T₀ := by
        simp [not_le_of_gt hsgt]
      have h_event :
          (fun T : NNReal ↦ Set.indicator (Set.Icc 0 T) w s) =ᶠ[𝓝 T₀] fun _ ↦ (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hsgt] with T hT
        have hs_not_mem : s ∉ Set.Icc (0 : NNReal) T := by
          have hTs : T < s := hT
          simp [not_le_of_gt hTs]
        simp [hs_not_mem]
      -- Proof comment: if `s` lies strictly to the right of `T₀`, the indicator is eventually
      -- identically zero near `T₀`.
      have hconst :
          Tendsto (fun _ : NNReal ↦ (0 : ℝ)) (𝓝 T₀)
            (𝓝 (Set.indicator (Set.Icc 0 T₀) w s)) := by
        simp [hT₀_not_mem]
      exact hconst.congr' h_event.symm
  -- Proof comment: dominated convergence upgrades the almost-everywhere stabilization of the
  -- interval indicators to continuity of the truncated Stieltjes primitive.
  simpa [bound] using
    (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      bound hF_meas h_bound hbound_integrable h_lim)

/-- Helper for Remark 21.62: the canonical Stieltjes measure of `VG` identifies the real mass of
`Set.Icc 0 T` with `VG T`. -/
lemma dyadicSquareVariationMeasure_real_Icc_eq
    {G VG : PathSpace} (hVG : HasSquareVariationAlong G VG)
    (T : NNReal) :
    (squareVariationStieltjesMeasure hVG).real (Set.Icc 0 T) = VG T := by
  simpa using (squareVariationStieltjesMeasure_realizes_path hVG T).symm

/-- Helper for Remark 21.62: integrating a constant against the canonical Stieltjes measure of
`VG` multiplies that constant by `VG T`. -/
lemma dyadicSetIntegral_const_eq_mul_squareVariation
    {G VG : PathSpace} (hVG : HasSquareVariationAlong G VG)
    (T : NNReal) (c : ℝ) :
    ∫ _ in Set.Icc 0 T, c ∂(squareVariationStieltjesMeasure hVG) = c * VG T := by
  -- Proof comment: reduce the constant integral to the interval mass and rewrite that mass as
  -- the square-variation value `VG T`.
  rw [MeasureTheory.integral_const, smul_eq_mul]
  calc
    ((squareVariationStieltjesMeasure hVG).restrict (Set.Icc 0 T)).real Set.univ * c =
        (squareVariationStieltjesMeasure hVG).real (Set.Icc 0 T) * c := by
          simp
    _ = VG T * c := by
          rw [dyadicSquareVariationMeasure_real_Icc_eq hVG T]
    _ = c * VG T := by
          ring

/-- Helper for Remark 21.62: integrating the prefix indicator `Set.Icc 0 τ` over `Set.Icc 0 T`
against the canonical Stieltjes measure of `VG` recovers `VG τ` whenever `τ ≤ T`. -/
lemma dyadicSetIntegral_indicator_Icc_eq_squareVariation
    {G VG : PathSpace} (hVG : HasSquareVariationAlong G VG)
    {τ T : NNReal} (hτT : τ ≤ T) :
    ∫ s in Set.Icc 0 T,
        Set.indicator (Set.Icc 0 τ) (fun _ ↦ (1 : ℝ)) s
          ∂(squareVariationStieltjesMeasure hVG) =
      VG τ := by
  have hinter :
      Set.Icc (0 : NNReal) T ∩ Set.Icc (0 : NNReal) τ = Set.Icc (0 : NNReal) τ := by
    ext s
    constructor
    · intro hs
      exact hs.2
    · intro hs
      exact ⟨⟨hs.1, le_trans hs.2 hτT⟩, hs⟩
  have hinter' :
      Set.Icc (0 : NNReal) τ ∩ Set.Icc (0 : NNReal) T = Set.Icc (0 : NNReal) τ := by
    rw [Set.inter_comm, hinter]
  -- Proof comment: collapse the outer restriction with the inner prefix indicator.
  calc
    ∫ s in Set.Icc 0 T, Set.indicator (Set.Icc 0 τ) (fun _ ↦ (1 : ℝ)) s
          ∂(squareVariationStieltjesMeasure hVG)
        = ∫ s, Set.indicator (Set.Icc 0 τ) (fun _ ↦ (1 : ℝ)) s
            ∂((squareVariationStieltjesMeasure hVG).restrict (Set.Icc 0 T)) := by
              rfl
    _ =
        ∫ s in Set.Icc 0 τ, (1 : ℝ)
          ∂((squareVariationStieltjesMeasure hVG).restrict (Set.Icc 0 T)) := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ s in Set.Icc 0 τ, (1 : ℝ) ∂(squareVariationStieltjesMeasure hVG) := by
          simp [Measure.restrict_restrict, hinter']
    _ = VG τ := by
          simpa using (squareVariationStieltjesMeasure_realizes_path hVG τ).symm

/-- Helper for Remark 21.62: integrating a finite prefix-step weight over `Set.Icc 0 T` against
the canonical Stieltjes measure of `VG` evaluates to the corresponding linear combination of
square-variation values. -/
lemma setIntegral_prefixStep_eq_linearCombination
    {ι : Type*} {G VG : PathSpace} (hVG : HasSquareVariationAlong G VG) (S : Finset ι)
    (τ : ι → NNReal) (a : ι → ℝ) (c : ℝ)
    (T : NNReal)
    (hτ : ∀ i ∈ S, τ i ≤ T) :
    ∫ s,
        (fun t ↦
          c + Finset.sum S (fun i ↦
            a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) t)) s
          ∂((squareVariationStieltjesMeasure hVG).restrict (Set.Icc 0 T)) =
      c * VG T + Finset.sum S (fun i ↦ a i * VG (τ i)) := by
  let ν : Measure NNReal := (squareVariationStieltjesMeasure hVG).restrict (Set.Icc 0 T)
  have hν_univ_lt_top : ν Set.univ < ⊤ := by
    simpa [ν] using (squareVariationStieltjesMeasure_Icc_lt_top hVG T).lt_top
  letI : IsFiniteMeasure ν := ⟨hν_univ_lt_top⟩
  have hconst :
      Integrable (fun _ : NNReal ↦ c) ν := by
    exact integrable_const c
  have hindicator :
      ∀ i : ι,
        Integrable
          (Set.indicator (Set.Icc 0 (τ i)) (fun _ : NNReal ↦ (1 : ℝ))) ν := by
    intro i
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  have htermInt :
      ∀ i ∈ S,
        Integrable
          (fun s : NNReal ↦
            a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ : NNReal ↦ (1 : ℝ)) s) ν := by
    intro i hi
    exact (hindicator i).const_mul (a i)
  have hsum :
      Integrable
        (fun s : NNReal ↦
          Finset.sum S fun i ↦
            a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ : NNReal ↦ (1 : ℝ)) s) ν := by
    exact integrable_finset_sum S htermInt
  have htermEval :
      ∀ i ∈ S,
        ∫ s, a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ : NNReal ↦ (1 : ℝ)) s ∂ν =
          a i * VG (τ i) := by
    intro i hi
    calc
      ∫ s, a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν =
          a i *
            ∫ s, Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν := by
              rw [integral_const_mul]
      _ = a i * VG (τ i) := by
            simpa [ν] using
              congrArg (fun r : ℝ ↦ a i * r)
                (dyadicSetIntegral_indicator_Icc_eq_squareVariation hVG (hτ i hi))
  -- Proof comment: expand the prefix-step integrand into its constant part plus finitely many
  -- indicator terms, then integrate termwise and rewrite each interval mass through `VG`.
  calc
    ∫ s,
        (fun t ↦
          c + Finset.sum S (fun i ↦
            a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) t)) s ∂ν
        = ∫ s, (fun _ : NNReal ↦ c) s ∂ν +
            ∫ s,
              Finset.sum S fun i ↦
                a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν := by
            change
              ∫ s,
                ((fun _ : NNReal ↦ c) s +
                  Finset.sum S fun i ↦
                    a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s) ∂ν =
                _ + _
            rw [integral_add hconst hsum]
    _ = c * VG T +
          ∫ s,
            Finset.sum S fun i ↦
              a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν := by
            simpa [ν] using
              congrArg
                (fun r : ℝ ↦
                  r +
                    ∫ s,
                      Finset.sum S fun i ↦
                        a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν)
                (dyadicSetIntegral_const_eq_mul_squareVariation hVG T c)
    _ = c * VG T + Finset.sum S fun i ↦
          ∫ s, a i * Set.indicator (Set.Icc 0 (τ i)) (fun _ ↦ (1 : ℝ)) s ∂ν := by
            rw [integral_finset_sum _ htermInt]
    _ = c * VG T + Finset.sum S (fun i ↦ a i * VG (τ i)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact htermEval i hi

/-- Helper for Remark 21.62: the coarse dyadic `Set.Icc`-staircase integrates against the
canonical Stieltjes measure of `VG` to the same finite linear combination that appears in its
dyadic-sum convergence formula. -/
lemma dyadicSetIntegral_coarseIccStep_eq_linearCombination
    {G VG : PathSpace} (hVG : HasSquareVariationAlong G VG)
    (w : NNReal → ℝ) (m : ℕ) (T : NNReal) :
    ∫ s in Set.Icc 0 T, dyadicCoarseIccStep w m T s ∂(squareVariationStieltjesMeasure hVG) =
      w (Definition2158.dyadicPartitionSequence m
            (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1)) * VG T +
        Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence m T - 1))
          fun i ↦
            (w (Definition2158.dyadicPartitionSequence m i) -
                w (Definition2158.dyadicPartitionSequence m (i + 1))) *
              VG (Definition2158.dyadicPartitionSequence m (i + 1)) := by
  let P := Definition2158.dyadicPartitionSequence
  let N := partitionBoundIndex P m T
  let cLast : ℝ := w (P m (N - 1))
  let coeff : ℕ → ℝ := fun i ↦ w (P m i) - w (P m (i + 1))
  have hτ :
      ∀ i ∈ Finset.range (N - 1), P m (i + 1) ≤ T := by
    intro i hi
    have hi_lt : i < N - 1 := Finset.mem_range.mp hi
    have hi_succ_lt : i + 1 < (N - 1) + 1 := Nat.succ_lt_succ hi_lt
    have hN : 0 < N := by
      exact lt_of_lt_of_le (Nat.zero_lt_succ i)
        (le_trans (Nat.succ_le_of_lt hi_lt) (Nat.sub_le _ _))
    have hN_eq : (N - 1) + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hN)
    have hi' : i + 1 < N := by
      simpa [hN_eq] using hi_succ_lt
    exact le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex m hi')
  -- Proof comment: `dyadicCoarseIccStep` is exactly the finite prefix-step integrand already handled
  -- by the previous lemma.
  simpa [dyadicCoarseIccStep, P, N, cLast, coeff] using
    setIntegral_prefixStep_eq_linearCombination
      (hVG := hVG)
      (S := Finset.range (N - 1))
      (τ := fun i ↦ P m (i + 1))
      (a := coeff)
      (c := cLast)
      T hτ

/-- Helper for Remark 21.62: a continuous weight on `Set.Icc 0 T` is the limit of the weighted
dyadic quadratic sums against the canonical square-variation Stieltjes measure. -/
lemma tendsto_weightedDyadicSquareVariationSum_of_continuous
    (w : NNReal → ℝ) (hw : Continuous w)
    {VG : PathSpace} (hVG : HasSquareVariationAlong G VG) :
    ∀ T : NNReal,
      Tendsto
        (fun n ↦ weightedDyadicSquareVariationSum w G T n)
        atTop
        (nhds (∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG))) := by
  intro T
  let B : ℝ := |VG T| + 1
  have hBpos : 0 < B := by
    -- Proof comment: the radius `|VG T| + 1` is strictly positive, so it safely normalizes the
    -- three error terms in the coarse-step approximation.
    dsimp [B]
    linarith [abs_nonneg (VG T)]
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let δ : ℝ := ε / (3 * B)
  have hδpos : 0 < δ := by
    -- Proof comment: the coarse-step approximation error is a positive fraction of `ε`.
    dsimp [δ]
    positivity
  rcases exists_dyadicCoarseIccStep_uniformApprox w hw T hδpos with ⟨m, hm⟩
  let q : NNReal → ℝ := dyadicCoarseIccStep w m T
  have hcoarse :
      Tendsto
        (fun n ↦ weightedDyadicSquareVariationSum q G T n)
        atTop
        (nhds (∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG))) := by
    -- Proof comment: the finite staircase weight is already covered by the explicit linear-
    -- combination convergence theorem.
    simpa [q, dyadicSetIntegral_coarseIccStep_eq_linearCombination, hVG] using
      tendsto_weightedDyadicSquareVariationSum_coarseIccStep_linearCombination
        (G := G) w hVG m T
  have hmassBound :
      ∀ᶠ n in atTop,
        |weightedDyadicSquareVariationSum w G T n -
            weightedDyadicSquareVariationSum q G T n| ≤
          δ * B := by
    filter_upwards [eventually_le_weightedDyadicSquareVariationSum_one_abs_add_one hVG T] with
      n hn
    have hstep :
        |weightedDyadicSquareVariationSum w G T n -
            weightedDyadicSquareVariationSum q G T n| ≤
          δ * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n := by
      -- Proof comment: the uniform approximation on `[0,T]` turns coefficient error into a
      -- dyadic-mass error.
      exact abs_sub_weightedDyadicSquareVariationSum_le w q G T δ hm n
    have hδnonneg : 0 ≤ δ := le_of_lt hδpos
    calc
      |weightedDyadicSquareVariationSum w G T n -
          weightedDyadicSquareVariationSum q G T n|
          ≤ δ * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n := hstep
      _ ≤ δ * B := by
            exact mul_le_mul_of_nonneg_left hn hδnonneg
  have hVG_nonneg : 0 ≤ VG T := by
    -- Proof comment: every square-variation witness is monotone from `0`, so its values are
    -- nonnegative.
    obtain ⟨hzero, hmonoVG⟩ := hasSquareVariationAlong_zero_and_monotone hVG
    rw [← hzero]
    exact hmonoVG bot_le
  have hIntegralApprox :
      |∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG) -
          ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| ≤
        δ * VG T := by
    let ν : Measure NNReal := (squareVariationStieltjesMeasure hVG).restrict (Set.Icc 0 T)
    have hν_univ_lt_top : ν Set.univ < ⊤ := by
      simpa [ν] using (squareVariationStieltjesMeasure_Icc_lt_top hVG T).lt_top
    letI : IsFiniteMeasure ν := ⟨hν_univ_lt_top⟩
    have hq_integrable : Integrable q ν := by
      -- Proof comment: the coarse staircase is a finite sum of constant and indicator terms over
      -- a finite-mass restricted measure.
      dsimp [q, dyadicCoarseIccStep]
      refine (integrable_const _).add ?_
      refine integrable_finset_sum _ ?_
      intro i hi
      exact ((integrable_const (1 : ℝ)).indicator measurableSet_Icc).const_mul _
    have hw_integrable : Integrable w ν := by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw.continuousOn
      have hbound_w :
          ∀ᵐ s ∂ν, ‖w s‖ ≤ C := by
        filter_upwards [MeasureTheory.ae_restrict_mem (μ := squareVariationStieltjesMeasure hVG)
          measurableSet_Icc] with s hs
        exact hC s hs
      -- Proof comment: on the finite restricted measure, boundedness on the compact interval
      -- `Set.Icc 0 T` is enough for integrability.
      exact MeasureTheory.Integrable.of_bound hw.aestronglyMeasurable C hbound_w
    have hboundν :
        ∀ᵐ s ∂ν, ‖q s - w s‖ ≤ δ := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := squareVariationStieltjesMeasure hVG)
        measurableSet_Icc] with s hs
      simpa [Real.norm_eq_abs, abs_sub_comm] using hm s hs
    have hnorm :
        ‖∫ s, (q s - w s) ∂ν‖ ≤ δ * ν.real Set.univ :=
      MeasureTheory.norm_integral_le_of_norm_le_const (μ := ν) (f := fun s ↦ q s - w s) hboundν
    have hrewrite :
        ∫ s, (q s - w s) ∂ν =
          ∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG) -
            ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG) := by
      simp [ν, MeasureTheory.integral_sub hq_integrable hw_integrable]
    have hmass :
        ν.real Set.univ = VG T := by
      simpa [ν] using dyadicSquareVariationMeasure_real_Icc_eq hVG T
    simpa [Real.norm_eq_abs, hrewrite, hmass] using hnorm
  have hVG_le_B : VG T ≤ B := by
    -- Proof comment: `B = |VG T| + 1` dominates the endpoint square-variation value.
    dsimp [B]
    linarith [le_abs_self (VG T)]
  have hδB : δ * B = ε / 3 := by
    have hB_ne : B ≠ 0 := ne_of_gt hBpos
    calc
      δ * B = (ε / (3 * B)) * B := by rfl
      _ = ε / 3 := by
            field_simp [hB_ne]
  have hIntegralApprox' :
      |∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG) -
          ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| ≤
        ε / 3 := by
    calc
      |∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG) -
          ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| ≤
          δ * VG T := hIntegralApprox
      _ ≤ δ * B := by
            exact mul_le_mul_of_nonneg_left hVG_le_B (le_of_lt hδpos)
      _ = ε / 3 := hδB
  have hmassBound' :
      ∀ᶠ n in atTop,
        |weightedDyadicSquareVariationSum w G T n -
            weightedDyadicSquareVariationSum q G T n| ≤
          ε / 3 := by
    filter_upwards [hmassBound] with n hn
    simpa [hδB] using hn
  have hcoarse' :
      ∀ᶠ n in atTop,
        |weightedDyadicSquareVariationSum q G T n -
            ∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG)| <
          ε / 3 := by
    -- Proof comment: the staircase-weighted dyadic sums converge directly to the matching
    -- staircase integral.
    simpa [Real.dist_eq] using Metric.tendsto_atTop.1 hcoarse (ε / 3) (by positivity)
  rcases Filter.eventually_atTop.1 hmassBound' with ⟨N₁, hN₁⟩
  rcases Filter.eventually_atTop.1 hcoarse' with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hnMass : |weightedDyadicSquareVariationSum w G T n -
      weightedDyadicSquareVariationSum q G T n| ≤ ε / 3 :=
    hN₁ n (le_of_max_le_left hn)
  have hnCoarse : |weightedDyadicSquareVariationSum q G T n -
      ∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG)| < ε / 3 :=
    hN₂ n (le_of_max_le_right hn)
  have htri₁ :
      |weightedDyadicSquareVariationSum w G T n -
          ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| ≤
        |weightedDyadicSquareVariationSum w G T n -
            weightedDyadicSquareVariationSum q G T n| +
          |weightedDyadicSquareVariationSum q G T n -
              ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| := by
    exact abs_sub_le _ _ _
  have htri₂ :
      |weightedDyadicSquareVariationSum q G T n -
          ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| ≤
        |weightedDyadicSquareVariationSum q G T n -
            ∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG)| +
          |∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG) -
              ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| := by
    exact abs_sub_le _ _ _
  have htri :
      |weightedDyadicSquareVariationSum w G T n -
          ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| ≤
        |weightedDyadicSquareVariationSum w G T n -
            weightedDyadicSquareVariationSum q G T n| +
          |weightedDyadicSquareVariationSum q G T n -
              ∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG)| +
          |∫ s in Set.Icc 0 T, q s ∂(squareVariationStieltjesMeasure hVG) -
              ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| := by
    linarith
  have hfinal :
      |weightedDyadicSquareVariationSum w G T n -
          ∫ s in Set.Icc 0 T, w s ∂(squareVariationStieltjesMeasure hVG)| < ε := by
    linarith
  simpa [Real.dist_eq] using hfinal

/-- Helper for Remark 21.62: the mean-value theorem can be packaged as a square-slope identity on
every nontrivial interval. -/
lemma exists_sq_deriv_eq_sq_slope
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Set.Ioo a b, (f b - f a) ^ 2 = (deriv f c) ^ 2 * (b - a) ^ 2 := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo a b) := by
    intro x hx
    exact (hf.differentiable (by norm_num) x).differentiableWithinAt
  rcases exists_deriv_eq_slope f hab hf.continuous.continuousOn hdiff with
    ⟨c, hc, hcDeriv⟩
  refine ⟨c, hc, ?_⟩
  have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hslope : deriv f c * (b - a) = f b - f a := by
    rw [hcDeriv]
    field_simp [hba_ne]
  -- Proof comment: multiply the mean-value identity by the interval length and square it.
  calc
    (f b - f a) ^ 2 = (deriv f c * (b - a)) ^ 2 := by rw [hslope]
    _ = (deriv f c) ^ 2 * (b - a) ^ 2 := by ring

/-- Helper for Remark 21.62: every time interval `[a, b]` contains a sample point whose derivative
weight realizes the squared increment of `f ∘ G` on that interval. -/
lemma exists_timeSample_sqSlope_eq_incrementSq
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (G : PathSpace)
    {a b : NNReal} (hab : a ≤ b) :
    ∃ u ∈ Set.Icc a b,
      (f (G b) - f (G a)) ^ 2 = (deriv f (G u)) ^ 2 * (G b - G a) ^ 2 := by
  by_cases hEq : G a = G b
  · refine ⟨a, ?_, ?_⟩
    · exact ⟨le_rfl, hab⟩
    · simp [hEq]
  · have hcontOn : ContinuousOn G (Set.Icc a b) := G.continuous.continuousOn
    have hsurj :
        Set.SurjOn G (Set.Icc a b) (Set.uIcc (G a) (G b)) :=
      hcontOn.surjOn_uIcc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    rcases lt_or_gt_of_ne hEq with hlt | hgt
    · rcases exists_sq_deriv_eq_sq_slope f hf hlt with ⟨c, hc, hcEq⟩
      have hcMem : c ∈ Set.uIcc (G a) (G b) := by
        simp [Set.uIcc_of_le (le_of_lt hlt), le_of_lt hc.1, le_of_lt hc.2]
      rcases hsurj hcMem with ⟨u, hu, rfl⟩
      exact ⟨u, hu, hcEq⟩
    · rcases exists_sq_deriv_eq_sq_slope f hf hgt with ⟨c, hc, hcEq⟩
      have hcMem : c ∈ Set.uIcc (G a) (G b) := by
        simp [Set.uIcc_of_ge (le_of_lt hgt), le_of_lt hc.1, le_of_lt hc.2]
      rcases hsurj hcMem with ⟨u, hu, huEq⟩
      refine ⟨u, hu, ?_⟩
      -- Proof comment: the reversed-value mean-value identity is orientation-free after squaring.
      rw [huEq]
      calc
        (f (G b) - f (G a)) ^ 2 = (f (G a) - f (G b)) ^ 2 := by ring
        _ = (deriv f c) ^ 2 * (G a - G b) ^ 2 := hcEq
        _ = (deriv f c) ^ 2 * (G b - G a) ^ 2 := by ring

/-- Helper for Remark 21.62: a chosen sample point inside an active dyadic interval stays within
one dyadic mesh width of the left endpoint. -/
lemma edist_timeSample_dyadicLeft_le_mesh
    (n k : ℕ) (T u : NNReal)
    (hu :
      u ∈ Set.Icc (Definition2158.dyadicPartitionSequence n k)
        (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T))
    (hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    edist u (Definition2158.dyadicPartitionSequence n k) ≤
      partitionMesh Definition2158.dyadicPartitionSequence n := by
  let P := Definition2158.dyadicPartitionSequence
  have hstrict : StrictMono (P n) :=
    by simpa [P] using Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n
  have hbase :
      P n k ≤ partitionNextPointUpTo P n k T := by
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt (hstrict (Nat.lt_succ_self k))
    · exact le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex n hk)
  have hdist :
      edist u (P n k) ≤ edist (partitionNextPointUpTo P n k T) (P n k) := by
    have hdistR :
        dist u (P n k) ≤ dist (partitionNextPointUpTo P n k T) (P n k) := by
      have hu1_real : (P n k : ℝ) ≤ u := by
        exact_mod_cast hu.1
      have hbase_real : (P n k : ℝ) ≤ partitionNextPointUpTo P n k T := by
        exact_mod_cast hbase
      rw [NNReal.dist_eq, NNReal.dist_eq, abs_of_nonneg, abs_of_nonneg]
      · exact sub_le_sub_right (by exact_mod_cast hu.2) _
      · exact sub_nonneg.mpr hbase_real
      · exact sub_nonneg.mpr hu1_real
    rw [edist_dist, edist_dist]
    exact ENNReal.ofReal_le_ofReal hdistR
  -- Proof comment: compare the sampled point to the left endpoint through the enclosing clipped
  -- interval, then appeal to the one-mesh control for the whole interval.
  calc
    edist u (P n k) ≤ edist (partitionNextPointUpTo P n k T) (P n k) := hdist
    _ = edist (P n k) (partitionNextPointUpTo P n k T) := by rw [edist_comm]
    _ ≤ partitionMesh P n := edist_dyadicPartitionPoint_partitionNextPointUpTo_le_mesh n k T hk

/-- Helper for Remark 21.62: a nonnegative pointwise coefficient error controls the difference
between the sampled dyadic quadratic sum and the left-endpoint weighted dyadic sum. -/
lemma abs_sub_sampledWeightDyadicSum_le
    (w : NNReal → ℝ) (G : PathSpace) (T : NNReal) (n : ℕ)
    (ε : ℝ) (u : ℕ → NNReal)
    (hεu :
      ∀ k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T,
        |w (u k) - w (Definition2158.dyadicPartitionSequence n k)| ≤ ε) :
    |Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            w (u k) *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2) -
        weightedDyadicSquareVariationSum w G T n| ≤
      ε * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n := by
  have hrewrite :
      Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
            (fun k ↦
              w (u k) *
                (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                    G (Definition2158.dyadicPartitionSequence n k)) ^ 2) -
          weightedDyadicSquareVariationSum w G T n =
        Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            (w (u k) - w (Definition2158.dyadicPartitionSequence n k)) *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2) := by
    -- Proof comment: rewrite the difference of the two dyadic sums as one sum with coefficient
    -- `w (u k) - w (P n k)`.
    rw [weightedDyadicSquareVariationSum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k hk
    ring
  calc
    |Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            w (u k) *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2) -
        weightedDyadicSquareVariationSum w G T n|
        = |Finset.sum
            (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
            (fun k ↦
              (w (u k) - w (Definition2158.dyadicPartitionSequence n k)) *
                (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                    G (Definition2158.dyadicPartitionSequence n k)) ^ 2)| := by
            rw [hrewrite]
    _ ≤ Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            |(w (u k) - w (Definition2158.dyadicPartitionSequence n k)) *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2|) := by
      exact
        Finset.abs_sum_le_sum_abs
          (fun k ↦
            (w (u k) - w (Definition2158.dyadicPartitionSequence n k)) *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2)
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
    _ = Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            |w (u k) - w (Definition2158.dyadicPartitionSequence n k)| *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hsquare_nonneg :
          0 ≤
            (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                G (Definition2158.dyadicPartitionSequence n k)) ^ 2 := by
        exact
          sq_nonneg
            (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              G (Definition2158.dyadicPartitionSequence n k))
      rw [abs_mul, abs_of_nonneg hsquare_nonneg]
    _ ≤ Finset.sum
          (Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T))
          (fun k ↦
            ε *
              (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (Definition2158.dyadicPartitionSequence n k)) ^ 2) := by
      -- Proof comment: bound each coefficient error by the common `ε` and keep the nonnegative
      -- squared increment factor.
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk' : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T :=
        Finset.mem_range.mp hk
      have hpoint :
          |w (u k) - w (Definition2158.dyadicPartitionSequence n k)| ≤ ε :=
        hεu k hk'
      have hsquare_nonneg :
          0 ≤
            (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                G (Definition2158.dyadicPartitionSequence n k)) ^ 2 := by
        exact
          sq_nonneg
            (G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              G (Definition2158.dyadicPartitionSequence n k))
      simpa using mul_le_mul_of_nonneg_right hpoint hsquare_nonneg
    _ = ε * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n := by
      -- Proof comment: factor the constant `ε` out of the dyadic sum and recover the unweighted
      -- quadratic mass.
      rw [weightedDyadicSquareVariationSum, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k hk
      ring

/-- Helper for Remark 21.62: the dyadic quadratic sums of `f ∘ G` differ from the derivative-
weighted dyadic quadratic sums of `G` by a quantity that tends to `0`. -/
lemma tendsto_dyadicSquareVariation_comp_minus_weighted_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    {VG : PathwiseProcess} (hVG : HasSquareVariationAlong G VG) :
    ∀ T : NNReal,
      Tendsto
        (fun n ↦
          dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T n -
            weightedDyadicSquareVariationSum (fun s ↦ (deriv f (G s)) ^ 2) G T n)
        atTop
        (nhds 0) := by
  intro T
  let P := Definition2158.dyadicPartitionSequence
  let w : NNReal → ℝ := fun s ↦ (deriv f (G s)) ^ 2
  have hw : Continuous w := continuous_derivSq_comp f hf G
  have hUC :
      UniformContinuousOn w (Set.Icc 0 T) :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).uniformContinuousOn_of_continuous
      hw.continuousOn
  let B : ℝ := |VG T| + 1
  have hBpos : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg (VG T)]
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let η : ℝ := ε / (2 * B)
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  rcases (Metric.uniformContinuousOn_iff_le.mp hUC) η hηpos with ⟨δ, hδpos, hδclose⟩
  have hmesh :
      ∀ᶠ n in atTop, partitionMesh P n ≤ ENNReal.ofReal δ := by
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
          (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδpos) with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  rcases Filter.eventually_atTop.1 hmesh with ⟨N₁, hN₁⟩
  rcases Filter.eventually_atTop.1
      (eventually_le_weightedDyadicSquareVariationSum_one_abs_add_one hVG T) with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hnmesh : partitionMesh P n ≤ ENNReal.ofReal δ := hN₁ n (le_of_max_le_left hn)
  have hnmass :
      weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n ≤ B :=
    hN₂ n (le_of_max_le_right hn)
  let N := partitionBoundIndex P n T
  have hleft :
      ∀ k < N, P n k ≤ partitionNextPointUpTo P n k T := by
    intro k hk
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt ((Definition2158.dyadicPartitionSequence_isAdmissible.strictMono n)
        (Nat.lt_succ_self k))
    · exact le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex n hk)
  have hsamples :
      ∀ k < N,
        ∃ u ∈ Set.Icc (P n k) (partitionNextPointUpTo P n k T),
          (f (G (partitionNextPointUpTo P n k T)) - f (G (P n k))) ^ 2 =
            (deriv f (G u)) ^ 2 * (G (partitionNextPointUpTo P n k T) - G (P n k)) ^ 2 := by
    intro k hk
    exact exists_timeSample_sqSlope_eq_incrementSq f hf G (a := P n k)
      (b := partitionNextPointUpTo P n k T) (hleft k hk)
  classical
  choose u hu_mem hu_eq using hsamples
  let sample : ℕ → NNReal := fun k ↦ if hk : k < N then u k hk else 0
  have hsample_mem :
      ∀ k < N, sample k ∈ Set.Icc (P n k) (partitionNextPointUpTo P n k T) := by
    intro k hk
    simpa [sample, hk] using hu_mem k hk
  have hactual :
      dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T n =
        Finset.sum (Finset.range N) (fun k ↦
          w (sample k) * (G (partitionNextPointUpTo P n k T) - G (P n k)) ^ 2) := by
    -- Proof comment: choose one mean-value sample on each active interval and rewrite every
    -- quadratic increment of `f ∘ G` through that sampled derivative weight.
    rw [dyadic_p_variation_sum, partitionPVariationSum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk' : k < N := Finset.mem_range.mp hk
    simpa [w, sample, hk', sq_abs] using hu_eq k hk'
  have hcoeff :
      ∀ k < N, |w (sample k) - w (P n k)| ≤ η := by
    intro k hk
    have hleft_mem : P n k ∈ Set.Icc (0 : NNReal) T :=
      dyadicPartitionPoint_mem_Icc_of_lt_partitionBoundIndex n k T hk
    have hsample_memT : sample k ∈ Set.Icc (0 : NNReal) T := by
      have hsamp := hsample_mem k hk
      constructor
      · exact bot_le
      · exact le_trans hsamp.2 (by
          rw [partitionNextPointUpTo]
          exact min_le_right _ _)
    have hsample_dist :
        dist (sample k) (P n k) ≤ δ := by
      have hedist :
          edist (sample k) (P n k) ≤ partitionMesh P n := by
        simpa [P] using edist_timeSample_dyadicLeft_le_mesh n k T (sample k)
          (hsample_mem k hk) hk
      have hedist' :
          edist (sample k) (P n k) ≤ ENNReal.ofReal δ :=
        le_trans hedist hnmesh
      exact
        (ENNReal.ofReal_le_ofReal_iff hδpos.le).mp
          (by simpa [edist_dist] using hedist')
    have hclose :
        dist (w (sample k)) (w (P n k)) ≤ η :=
      hδclose (sample k) hsample_memT (P n k) hleft_mem hsample_dist
    simpa [Real.dist_eq] using hclose
  have hmainBound :
      |dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T n -
          weightedDyadicSquareVariationSum w G T n| ≤
        η * weightedDyadicSquareVariationSum (fun _ ↦ (1 : ℝ)) G T n := by
    -- Proof comment: the sampled-slope representation turns the chain-rule error into a pure
    -- coefficient error, which is controlled by uniform continuity of the derivative weight.
    rw [hactual]
    exact abs_sub_sampledWeightDyadicSum_le w G T n η sample hcoeff
  have hbound :
      |dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T n -
          weightedDyadicSquareVariationSum w G T n| ≤
        η * B := by
    exact le_trans hmainBound (mul_le_mul_of_nonneg_left hnmass (le_of_lt hηpos))
  have hηB :
      η * B = ε / 2 := by
    have hB_ne : B ≠ 0 := ne_of_gt hBpos
    calc
      η * B = (ε / (2 * B)) * B := by rfl
      _ = ε / 2 := by
            field_simp [hB_ne]
  have hfinal :
      |dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T n -
          weightedDyadicSquareVariationSum w G T n| < ε := by
    have hhalf : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt (by simpa [B, η, w, hηB] using hbound) hhalf
  simpa [Real.dist_eq, w] using hfinal

-- Proof sketch: the actual chain-rule work is carried out against the canonical Stieltjes measure
-- attached to the monotone square-variation path `VG`, and the public theorems below expose that
-- source-faithful formula at the owner and witness levels.
/-- Remark 21.62: a chosen dyadic square-variation witness `VG` of `G` yields a
continuous square-variation witness of `f ∘ G` whose Lebesgue--Stieltjes formula is computed with
respect to the canonical Stieltjes measure attached to `VG`, not an arbitrary measure merely
matching the constant test function on intervals `Set.Icc 0 T`. -/
theorem exists_squareVariationComp_universalStieltjesWitness
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hVG : HasSquareVariationAlong G VG) :
    ∃ VfG : PathSpace,
      HasSquareVariationAlong ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) VfG ∧
        ∀ T : NNReal,
          VfG T =
            ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2
              ∂((((hasSquareVariationAlong_zero_and_monotone hVG).2).stieltjesFunction).measure) :=
      by
  obtain ⟨hzero, hmonoVG⟩ := hasSquareVariationAlong_zero_and_monotone hVG
  let μVG : Measure NNReal := (hmonoVG.stieltjesFunction).measure
  have hμVG :
      ∀ T : NNReal, VG T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μVG :=
    stieltjesFunction_measure_realizes_path VG hmonoVG hzero
  let VfG : PathSpace :=
    { toFun := fun T ↦ ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2 ∂μVG
      continuous_toFun := continuous_stieltjesIntegral_derivSq_comp f hf G VG hmonoVG }
  refine ⟨VfG, ?_⟩
  -- Route correction: the structural square-variation setup is now in place (the monotone
  -- witness `hmonoVG`, the canonical Stieltjes realization `hμVG`, and the continuous candidate
  -- path `VfG` built from the canonical Stieltjes primitive). The dyadic staircase package is
  -- also closed on both sides: `dyadicSetIntegral_coarseIccStep_eq_linearCombination` handles the
  -- measure side, and `tendsto_weightedDyadicSquareVariationSum_of_continuous` upgrades the
  -- dyadic coarse-step convergence to the continuous weight
  -- `w := fun s ↦ (deriv f (G s)) ^ 2`.
  -- TODO: the first remaining blocker is continuity of the primitive
  -- `T ↦ ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2 ∂μVG`, which is still needed to package `VfG`
  -- as a `PathSpace`. The second blocker is the mean-value comparison between the actual dyadic
  -- square-variation sums of `f ∘ G` and the derivative-weighted dyadic sums of `G`. Once those
  -- two bridges are proved, the final bookkeeping is the direct limit identity for this canonical
  -- Stieltjes measure; no transport to arbitrary interval-realizing measures is part of the
  -- source-faithful statement.
  refine ⟨?_, ?_⟩
  · intro T
    have hzero :
        Tendsto
          (fun n ↦
            dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T n -
              weightedDyadicSquareVariationSum (fun s ↦ (deriv f (G s)) ^ 2) G T n)
          atTop
          (nhds 0) :=
      tendsto_dyadicSquareVariation_comp_minus_weighted_zero (G := G) (VG := VG) f hf hVG T
    have hweighted :
        Tendsto
          (fun n ↦
            weightedDyadicSquareVariationSum (fun s ↦ (deriv f (G s)) ^ 2) G T n)
          atTop
          (nhds (∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2 ∂μVG)) := by
      simpa [squareVariationStieltjesMeasure, μVG] using
        tendsto_weightedDyadicSquareVariationSum_of_continuous
          (G := G) (VG := VG) (fun s ↦ (deriv f (G s)) ^ 2)
          (continuous_derivSq_comp f hf G) hVG T
    have hsum :
        Tendsto
          (fun n ↦
            (dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T n -
                weightedDyadicSquareVariationSum (fun s ↦ (deriv f (G s)) ^ 2) G T n) +
              weightedDyadicSquareVariationSum (fun s ↦ (deriv f (G s)) ^ 2) G T n)
          atTop
          (nhds (0 + ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2 ∂μVG)) :=
      hzero.add hweighted
    have hrewrite :
        (fun n ↦
          (dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T n -
              weightedDyadicSquareVariationSum (fun s ↦ (deriv f (G s)) ^ 2) G T n) +
            weightedDyadicSquareVariationSum (fun s ↦ (deriv f (G s)) ^ 2) G T n) =
          dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T := by
      funext n
      ring
    -- Proof comment: the actual dyadic sums are the sum of the vanishing comparison error and
    -- the derivative-weighted sums, so the two convergence statements assemble directly.
    rw [hrewrite] at hsum
    simpa [VfG, μVG] using hsum
  · intro T
    rfl

-- Proof sketch: this is the witness-level bridge identity for chosen square-variation paths.
/-- Helper for Remark 21.62: if `f ∈ C¹(ℝ)` and `VG`, `VfG` are chosen continuous square-variation
paths for `G` and `f ∘ G`, then in the Lebesgue--Stieltjes sense
`VfG T = ∫ s in Set.Icc 0 T, (deriv f (G s))^2 ∂(squareVariationStieltjesMeasure hVG)`. -/
theorem squareVariation_comp_eq_lebesgueStieltjesIntegral_of_realizations
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hVG : HasSquareVariationAlong G VG)
    {VfG : PathSpace}
    (hVfG : HasSquareVariationAlong ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) VfG) :
    ∀ T : NNReal,
      VfG T =
        ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2 ∂(squareVariationStieltjesMeasure hVG) := by
  intro T
  rcases exists_squareVariationComp_universalStieltjesWitness
      (G := G) (VG := VG) f hf hVG with ⟨VfG', hVfG', hVfG'_formula⟩
  have hlim :
      Tendsto
        (dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T)
        atTop
        (nhds (VfG T)) :=
    HasSquareVariationAlong.tendsto_partition_sum hVfG T
  have hlim' :
      Tendsto
        (dyadic_p_variation_sum 2 ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) T)
        atTop
        (nhds (VfG' T)) :=
    HasSquareVariationAlong.tendsto_partition_sum hVfG' T
  have hEq : VfG T = VfG' T :=
    tendsto_nhds_unique hlim hlim'
  calc
    VfG T = VfG' T := hEq
    _ = ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2 ∂(squareVariationStieltjesMeasure hVG) := by
          simpa [squareVariationStieltjesMeasure] using hVfG'_formula T

-- Proof sketch: choose a continuous square-variation path `VG` for `G`; the earlier dyadic
-- monotonicity companion theorem upgrades `VG` to a monotone Stieltjes path, and the witness-level
-- theorem above then supplies the composed square-variation path.
/-- Helper for Remark 21.62: if `f ∈ C¹(ℝ)` and `G` has continuous square variation along the
dyadic partitions, then the composed path `t ↦ f (G t)` again has continuous square variation. -/
theorem hasContinuousSquareVariation_comp
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hG : HasContinuousSquareVariation G) :
    HasContinuousSquareVariation ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) := by
  rcases hG with ⟨VG, hVG⟩
  -- Proof comment: the universal witness theorem already returns a continuous square-variation path
  -- of `f ∘ G`; the owner-level statement keeps only that path and its convergence property.
  rcases exists_squareVariationComp_universalStieltjesWitness f hf hVG with ⟨VfG, hVfG, -⟩
  exact ⟨VfG, hVfG⟩

-- Proof sketch: this is the owner-level closure theorem above, rewritten through the source-facing
-- identification `𝒞_qv = {G | HasContinuousSquareVariation G}` from Definition 21.58.
/-- Source-facing closure corollary for Remark 21.62. -/
theorem mem_𝒞_qv_comp
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hG : G ∈ 𝒞_qv) :
    ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) ∈ 𝒞_qv := by
  simpa [mem_𝒞_qv_iff] using
    hasContinuousSquareVariation_comp f hf ((mem_𝒞_qv_iff G).1 hG)

-- Proof sketch: this is the source-facing owner statement, using the canonical bracket and
-- canonical Stieltjes measure attached to the dyadic square-variation owner.
/-- Source-facing formula for Remark 21.62: if `f ∈ C¹(ℝ)` and `G ∈ 𝒞_qv`, then in the
Lebesgue--Stieltjes sense
`⟨f(G)⟩_T = ∫ s in Set.Icc 0 T, (deriv f (G s))^2 d⟨G⟩_s`. -/
theorem squareVariation_comp_eq_lebesgueStieltjesIntegral
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hG : G ∈ 𝒞_qv) :
    ∀ T : NNReal,
      continuousSquareVariationBracket
          ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G)
          (mem_𝒞_qv_comp f hf hG) T =
        ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2
          ∂(continuousSquareVariationMeasure G hG) := by
  intro T
  -- Proof comment: specialize the realization theorem to the canonical brackets of `G` and
  -- `f ∘ G`.
  simpa [continuousSquareVariationMeasure] using
    squareVariation_comp_eq_lebesgueStieltjesIntegral_of_realizations
      (G := G)
      (VG := continuousSquareVariationBracket G hG)
      (VfG := continuousSquareVariationBracket
        ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G)
        (mem_𝒞_qv_comp f hf hG))
      f hf
      (continuousSquareVariationBracket_spec G hG)
      (continuousSquareVariationBracket_spec
        ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G)
        (mem_𝒞_qv_comp f hf hG))
      T

-- Proof sketch: this is the existence version of the source formula for a chosen square-variation
-- path `VG`, using the canonical Stieltjes measure attached to its monotone representative.
/-- Witness-level existence companion for Remark 21.62: if `VG` is a chosen continuous
square-variation path of `G`, then `f ∘ G` admits a continuous square-variation path whose value
at time `T` is the Lebesgue--Stieltjes integral of `(f'(G_s))²` against the canonical measure
`d⟨G⟩`. -/
theorem exists_squareVariation_comp_eq_lebesgueStieltjesIntegral
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hVG : HasSquareVariationAlong G VG) :
    ∃ VfG : PathSpace,
      HasSquareVariationAlong ((⟨f, hf.continuous⟩ : C(ℝ, ℝ)).comp G) VfG ∧
        ∀ T : NNReal,
          VfG T =
            ∫ s in Set.Icc 0 T, (deriv f (G s)) ^ 2
              ∂((((hasSquareVariationAlong_zero_and_monotone hVG).2).stieltjesFunction).measure) :=
      by
  -- Proof comment: the stronger witness theorem already packages the canonical Stieltjes formula,
  -- so we simply keep that source-faithful identity.
  rcases exists_squareVariationComp_universalStieltjesWitness f hf hVG with
      ⟨VfG, hVfG, hVfG_formula⟩
  refine ⟨VfG, hVfG, ?_⟩
  exact hVfG_formula

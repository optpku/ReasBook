/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open Filter
open scoped ENNReal Topology

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ
local notation "dyadicPartitionSequence" => Definition2158.dyadicPartitionSequence

namespace HasSquareVariationAlong

/-- Helper for Remark 21.61: the dyadic square-variation predicate exposes its defining
partition-sum limit at each fixed terminal time. -/
theorem tendsto_partition_sum
    {G : PathSpace} {V : PathwiseProcess}
    (hV : HasSquareVariationAlong G V) (T : NNReal) :
    Tendsto (dyadic_p_variation_sum 2 G T) atTop (nhds (V T)) :=
  HasSquareVariationAlongPartition.tendsto_partition_sum hV T

end HasSquareVariationAlong

/- Remark 21.61 is a `bridge/view` item in the Chapter 21 dyadic square-variation API.
Its owner abstractions are the dyadic square-variation and quadratic-covariation predicates from
Definition 21.58 together with mathlib's total-variation owner `eVariationOn`. The primitive data
are chosen square-variation paths `⟨F + G⟩`, `⟨F - G⟩`, `⟨F⟩`, `⟨G⟩`, and a chosen covariation path
`⟨F,G⟩`; the polarization formula and the first-variation bound are derived API for those owner
objects. -/

/-- Helper for Remark 21.61: the dyadic square-variation sum of `F + G` expands into the two
square-variation sums plus twice the dyadic quadratic covariation sum. -/
lemma dyadicSquareVariationSum_add_eq
    (F G : PathSpace) (T : NNReal) (n : ℕ) :
    dyadic_p_variation_sum 2 (F + G) T n =
      dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
        dyadic_p_variation_sum 2 G T n := by
  let N := partitionBoundIndex Definition2158.dyadicPartitionSequence n T
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      F (Definition2158.dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      G (Definition2158.dyadicPartitionSequence n k)
  -- Proof comment: expand each dyadic increment of `F + G`, then regroup the finite sum into
  -- the `F`-, mixed-, and `G`-parts.
  rw [dyadic_p_variation_sum, partitionPVariationSum]
  calc
    Finset.sum (Finset.range N)
        (fun k ↦
          Real.rpow
            (|((F + G) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T)) -
                ((F + G) (Definition2158.dyadicPartitionSequence n k))|)
            2) =
        Finset.sum (Finset.range N) (fun k ↦ (ΔF k + ΔG k) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [← Real.rpow_natCast]
          have hadd :
              (F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) +
                  G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T)) -
                (F (Definition2158.dyadicPartitionSequence n k) +
                  G (Definition2158.dyadicPartitionSequence n k)) =
                ΔF k + ΔG k := by
            dsimp [ΔF, ΔG]
            ring
          rw [ContinuousMap.add_apply, ContinuousMap.add_apply, hadd]
          simp [sq_abs]
    _ = Finset.sum (Finset.range N) (fun k ↦ (ΔF k) ^ 2 + 2 * (ΔF k * ΔG k) + (ΔG k) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = (Finset.sum (Finset.range N) fun k ↦ (ΔF k) ^ 2) +
          2 * Finset.sum (Finset.range N) (fun k ↦ ΔF k * ΔG k) +
          Finset.sum (Finset.range N) (fun k ↦ (ΔG k) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
          dyadic_p_variation_sum 2 G T n := by
          simp [N, ΔF, ΔG, dyadic_p_variation_sum, dyadic_quadratic_covariation_sum,
            partitionPVariationSum, partitionQuadraticCovariationSum, sq_abs]

/-- Helper for Remark 21.61: the dyadic square-variation sum of `F - G` expands into the two
square-variation sums minus twice the dyadic quadratic covariation sum. -/
lemma dyadicSquareVariationSum_sub_eq
    (F G : PathSpace) (T : NNReal) (n : ℕ) :
    dyadic_p_variation_sum 2 (F - G) T n =
      dyadic_p_variation_sum 2 F T n - 2 * dyadic_quadratic_covariation_sum F G T n +
        dyadic_p_variation_sum 2 G T n := by
  let N := partitionBoundIndex Definition2158.dyadicPartitionSequence n T
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      F (Definition2158.dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      G (Definition2158.dyadicPartitionSequence n k)
  -- Proof comment: expand each dyadic increment of `F - G`, then regroup the finite sum into
  -- the `F`-, mixed-, and `G`-parts with the mixed term carrying the opposite sign.
  rw [dyadic_p_variation_sum, partitionPVariationSum]
  calc
    Finset.sum (Finset.range N)
        (fun k ↦
          Real.rpow
            (|((F - G) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T)) -
                ((F - G) (Definition2158.dyadicPartitionSequence n k))|)
            2) =
        Finset.sum (Finset.range N) (fun k ↦ (ΔF k - ΔG k) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [← Real.rpow_natCast]
          have hsub :
              (F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                  G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T)) -
                (F (Definition2158.dyadicPartitionSequence n k) -
                  G (Definition2158.dyadicPartitionSequence n k)) =
                ΔF k - ΔG k := by
            dsimp [ΔF, ΔG]
            ring
          rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, hsub]
          simp [sq_abs]
    _ = Finset.sum (Finset.range N)
          (fun k ↦ (ΔF k) ^ 2 - 2 * (ΔF k * ΔG k) + (ΔG k) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = Finset.sum (Finset.range N) (fun k ↦ (ΔF k) ^ 2 - 2 * (ΔF k * ΔG k)) +
          Finset.sum (Finset.range N) (fun k ↦ (ΔG k) ^ 2) := by
          rw [Finset.sum_add_distrib]
    _ = (Finset.sum (Finset.range N) fun k ↦ (ΔF k) ^ 2) -
          Finset.sum (Finset.range N) (fun k ↦ 2 * (ΔF k * ΔG k)) +
          Finset.sum (Finset.range N) (fun k ↦ (ΔG k) ^ 2) := by
          rw [Finset.sum_sub_distrib]
    _ = (Finset.sum (Finset.range N) fun k ↦ (ΔF k) ^ 2) -
          2 * Finset.sum (Finset.range N) (fun k ↦ ΔF k * ΔG k) +
          Finset.sum (Finset.range N) (fun k ↦ (ΔG k) ^ 2) := by
          rw [Finset.mul_sum]
    _ = dyadic_p_variation_sum 2 F T n - 2 * dyadic_quadratic_covariation_sum F G T n +
          dyadic_p_variation_sum 2 G T n := by
          simp [N, ΔF, ΔG, dyadic_p_variation_sum, dyadic_quadratic_covariation_sum,
            partitionPVariationSum, partitionQuadraticCovariationSum, sq_abs]

/-- Helper for Remark 21.61: square-variation witnesses for `F`, `G`, and their quadratic
covariation combine into the canonical square-variation witness for `F + G`. -/
lemma hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong
    {F G : PathSpace} {brF brG covFG : PathwiseProcess}
    (hF : HasSquareVariationAlong F brF)
    (hG : HasSquareVariationAlong G brG)
    (hFG : HasQuadraticCovariationAlong F G covFG) :
    HasSquareVariationAlong (F + G) (fun T ↦ brF T + 2 * covFG T + brG T) := by
  intro T
  have hFsum := HasSquareVariationAlong.tendsto_partition_sum hF T
  have hGsum := HasSquareVariationAlong.tendsto_partition_sum hG T
  have hFGsum := HasQuadraticCovariationAlong.tendsto_partition_sum hFG T
  -- Proof comment: rewrite the dyadic square sum of `F + G` into the sum of the three dyadic
  -- limits and then pass to the limit termwise.
  have hsum :
      Tendsto
        (fun n ↦
          dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
            dyadic_p_variation_sum 2 G T n)
        atTop
        (nhds (brF T + 2 * covFG T + brG T)) := by
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hFsum.add ((hFGsum.const_mul 2).add hGsum)
  convert hsum using 1
  ext n
  simpa [dyadic_p_variation_sum] using (dyadicSquareVariationSum_add_eq F G T n)

/-- Helper for Remark 21.61: square-variation witnesses for `F`, `G`, and their quadratic
covariation combine into the canonical square-variation witness for `F - G`. -/
lemma hasSquareVariationAlong_sub_of_hasQuadraticCovariationAlong
    {F G : PathSpace} {brF brG covFG : PathwiseProcess}
    (hF : HasSquareVariationAlong F brF)
    (hG : HasSquareVariationAlong G brG)
    (hFG : HasQuadraticCovariationAlong F G covFG) :
    HasSquareVariationAlong (F - G) (fun T ↦ brF T - 2 * covFG T + brG T) := by
  intro T
  have hFsum := HasSquareVariationAlong.tendsto_partition_sum hF T
  have hGsum := HasSquareVariationAlong.tendsto_partition_sum hG T
  have hFGsum := HasQuadraticCovariationAlong.tendsto_partition_sum hFG T
  -- Proof comment: rewrite the dyadic square sum of `F - G` into the same three dyadic limits
  -- with the mixed term carrying the opposite sign.
  have hsum :
      Tendsto
        (fun n ↦
          dyadic_p_variation_sum 2 F T n - 2 * dyadic_quadratic_covariation_sum F G T n +
            dyadic_p_variation_sum 2 G T n)
        atTop
        (nhds (brF T - 2 * covFG T + brG T)) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using
      (hFsum.sub (hFGsum.const_mul 2)).add hGsum
  convert hsum using 1
  ext n
  simpa [dyadic_p_variation_sum] using (dyadicSquareVariationSum_sub_eq F G T n)

/-- Helper for Remark 21.61: on `[s, t]`, the variation of a difference of monotone real-valued
processes is bounded by the sum of their endpoint increments. -/
theorem eVariationOn_Icc_sub_le_of_monotone_process
    {G Gplus Gminus : PathwiseProcess} (hG : G = Gplus - Gminus) (hGplus_mono : Monotone Gplus)
    (hGminus_mono : Monotone Gminus) {s t : NNReal} (_hst : s ≤ t) :
    eVariationOn G (Icc s t) ≤
      ENNReal.ofReal ((Gplus t - Gplus s) + (Gminus t - Gminus s)) := by
  have hEqOn : EqOn G (fun x ↦ Gplus x - Gminus x) (Icc s t) := by
    intro x hx
    simp [hG]
  rw [eVariationOn.eq_of_eqOn hEqOn]
  -- Proof comment: every partition increment of `Gplus - Gminus` is bounded by the sum of the
  -- nonnegative monotone increments of `Gplus` and `Gminus`, and those sums telescope.
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    ∑ i ∈ Finset.range n, edist ((fun x ↦ Gplus x - Gminus x) (u (i + 1)))
        ((fun x ↦ Gplus x - Gminus x) (u i))
        ≤ ∑ i ∈ Finset.range n,
            ENNReal.ofReal
              ((Gplus (u (i + 1)) - Gplus (u i)) + (Gminus (u (i + 1)) - Gminus (u i))) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hplus_nonneg : 0 ≤ Gplus (u (i + 1)) - Gplus (u i) := by
            exact sub_nonneg_of_le (hGplus_mono (hu (Nat.le_succ i)))
          have hminus_nonneg : 0 ≤ Gminus (u (i + 1)) - Gminus (u i) := by
            exact sub_nonneg_of_le (hGminus_mono (hu (Nat.le_succ i)))
          rw [edist_dist, Real.dist_eq]
          refine ENNReal.ofReal_le_ofReal ?_
          let dplus := Gplus (u (i + 1)) - Gplus (u i)
          let dminus := Gminus (u (i + 1)) - Gminus (u i)
          have hdecomp :
              (fun x ↦ Gplus x - Gminus x) (u (i + 1)) -
                  (fun x ↦ Gplus x - Gminus x) (u i) =
                dplus + (-dminus) := by
            dsimp [dplus, dminus]
            ring
          rw [hdecomp]
          calc
            |dplus + (-dminus)| ≤ |dplus| + |-dminus| := abs_add_le _ _
            _ = dplus + dminus := by
              rw [abs_of_nonneg hplus_nonneg]
              rw [abs_of_nonpos (neg_nonpos.mpr hminus_nonneg)]
              ring
    _ = ENNReal.ofReal
          (∑ i ∈ Finset.range n,
            ((Gplus (u (i + 1)) - Gplus (u i)) + (Gminus (u (i + 1)) - Gminus (u i)))) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i hi
          exact add_nonneg
            (sub_nonneg_of_le (hGplus_mono (hu (Nat.le_succ i))))
            (sub_nonneg_of_le (hGminus_mono (hu (Nat.le_succ i))))
    _ = ENNReal.ofReal
          ((Gplus (u n) - Gplus (u 0)) + (Gminus (u n) - Gminus (u 0))) := by
          rw [Finset.sum_add_distrib, Finset.sum_range_sub fun i ↦ Gplus (u i),
            Finset.sum_range_sub fun i ↦ Gminus (u i)]
    _ ≤ ENNReal.ofReal ((Gplus t - Gplus s) + (Gminus t - Gminus s)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact add_le_add
            (sub_le_sub (hGplus_mono (us n).2) (hGplus_mono (us 0).1))
            (sub_le_sub (hGminus_mono (us n).2) (hGminus_mono (us 0).1))

/-- Helper for Remark 21.61: scaling a path by `c` scales its dyadic square-variation sum by
`c ^ 2`. -/
lemma dyadicSquareVariationSum_smul_eq
    (c : ℝ) (F : PathSpace) (T : NNReal) (n : ℕ) :
    dyadic_p_variation_sum 2 (c • F) T n = c ^ 2 * dyadic_p_variation_sum 2 F T n := by
  let N := partitionBoundIndex Definition2158.dyadicPartitionSequence n T
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      F (Definition2158.dyadicPartitionSequence n k)
  -- Proof comment: each dyadic increment scales by `c`, so each squared increment scales by
  -- `c ^ 2`, which factors out of the finite sum.
  rw [dyadic_p_variation_sum, partitionPVariationSum]
  calc
    Finset.sum (Finset.range N)
        (fun k ↦
          Real.rpow
            (|((c • F) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T)) -
                ((c • F) (Definition2158.dyadicPartitionSequence n k))|)
            2) =
        Finset.sum (Finset.range N) (fun k ↦ (c * ΔF k) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [← Real.rpow_natCast]
      have hsmul :
          c * F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              c * F (Definition2158.dyadicPartitionSequence n k) =
            c * ΔF k := by
        dsimp [ΔF]
        ring
      simp [Pi.smul_apply, hsmul]
      simpa [sq_abs] using (sq_abs (c * ΔF k))
    _ = Finset.sum (Finset.range N) (fun k ↦ c ^ 2 * (ΔF k) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      ring
    _ = c ^ 2 * Finset.sum (Finset.range N) (fun k ↦ (ΔF k) ^ 2) := by
      rw [Finset.mul_sum]
    _ = c ^ 2 * dyadic_p_variation_sum 2 F T n := by
      simp [N, ΔF, dyadic_p_variation_sum, partitionPVariationSum, sq_abs]

/-- Helper for Remark 21.61: scaling `F` and `G` by `a` and `b` scales the dyadic mixed sum by
`a * b`. -/
lemma dyadicQuadraticCovariationSum_smul_eq
    (a b : ℝ) (F G : PathSpace) (T : NNReal) (n : ℕ) :
    dyadic_quadratic_covariation_sum (a • F) (b • G) T n =
      (a * b) * dyadic_quadratic_covariation_sum F G T n := by
  let N := partitionBoundIndex Definition2158.dyadicPartitionSequence n T
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      F (Definition2158.dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      G (Definition2158.dyadicPartitionSequence n k)
  -- Proof comment: the two scalar factors pull through each mixed increment and combine into
  -- the product `a * b`.
  rw [dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum]
  have hscaled :
      Finset.sum (Finset.range N)
          (fun k ↦
            ((a • F) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                (a • F) (Definition2158.dyadicPartitionSequence n k)) *
              ((b • G) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
                (b • G) (Definition2158.dyadicPartitionSequence n k)) ) =
        Finset.sum (Finset.range N) (fun k ↦ (a * ΔF k) * (b * ΔG k)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hFsmul :
        a * F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
            a * F (Definition2158.dyadicPartitionSequence n k) =
          a * ΔF k := by
      dsimp [ΔF]
      ring
    have hGsmul :
        b * G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
            b * G (Definition2158.dyadicPartitionSequence n k) =
          b * ΔG k := by
      dsimp [ΔG]
      ring
    simp [Pi.smul_apply, hFsmul, hGsmul]
  calc
    Finset.sum (Finset.range N)
        (fun k ↦
          ((a • F) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              (a • F) (Definition2158.dyadicPartitionSequence n k)) *
            ((b • G) (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
              (b • G) (Definition2158.dyadicPartitionSequence n k))) =
        Finset.sum (Finset.range N) (fun k ↦ (a * ΔF k) * (b * ΔG k)) := hscaled
    _ = Finset.sum (Finset.range N) (fun k ↦ (a * b) * (ΔF k * ΔG k)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = (a * b) * Finset.sum (Finset.range N) (fun k ↦ ΔF k * ΔG k) := by
          rw [Finset.mul_sum]
    _ = (a * b) * dyadic_quadratic_covariation_sum F G T n := by
          simp [N, ΔF, ΔG, dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum]

/-- Helper for Remark 21.61: scaling a square-variation witness by `c` scales the bracket path by
`c ^ 2`. -/
lemma hasSquareVariationAlong_smul
    {F : PathSpace} {brF : PathwiseProcess} (hF : HasSquareVariationAlong F brF) (c : ℝ) :
    HasSquareVariationAlong (c • F) (fun T ↦ c ^ 2 * brF T) := by
  intro T
  have hsum := HasSquareVariationAlong.tendsto_partition_sum hF T
  -- Proof comment: rewrite each dyadic square sum after scaling and then pull the constant
  -- factor through the limit.
  convert hsum.const_mul (c ^ 2) using 1
  ext n
  simpa [dyadic_p_variation_sum] using (dyadicSquareVariationSum_smul_eq c F T n)

/-- Helper for Remark 21.61: scaling the two paths scales the quadratic-covariation witness by the
product of the two scalars. -/
lemma hasQuadraticCovariationAlong_smul
    {F G : PathSpace} {covFG : PathwiseProcess}
    (hFG : HasQuadraticCovariationAlong F G covFG) (a b : ℝ) :
    HasQuadraticCovariationAlong (a • F) (b • G) (fun T ↦ (a * b) * covFG T) := by
  intro T
  have hsum := HasQuadraticCovariationAlong.tendsto_partition_sum hFG T
  -- Proof comment: rewrite the scaled mixed dyadic sum and then move the scalar factor outside
  -- the limit.
  convert hsum.const_mul (a * b) using 1
  ext n
  simpa [dyadic_quadratic_covariation_sum] using
    (dyadicQuadraticCovariationSum_smul_eq a b F G T n)

/-- Helper for Remark 21.61: the first dyadic partition index that reaches time `0` is `0`. -/
lemma partitionBoundIndex_zero (n : ℕ) :
    partitionBoundIndex Definition2158.dyadicPartitionSequence n 0 = 0 := by
  -- Proof comment: admissible partitions start at `0`, so the minimizing index is already the
  -- initial index.
  have hmin : partitionBoundIndex Definition2158.dyadicPartitionSequence n 0 ≤ 0 := by
    rw [partitionBoundIndex]
    exact
      Nat.find_min' (exists_partition_index_le_time Definition2158.dyadicPartitionSequence n 0)
        (by simp)
  exact Nat.le_zero.mp hmin

/-- Helper for Remark 21.61: the dyadic square-variation sum on the degenerate interval `[0,0]`
vanishes. -/
lemma dyadicSquareVariationSum_zero (H : PathSpace) (n : ℕ) :
    dyadic_p_variation_sum 2 H 0 n = 0 := by
  -- Proof comment: at time `0` the truncated dyadic partition has no nontrivial increment.
  rw [dyadic_p_variation_sum, partitionPVariationSum, partitionBoundIndex_zero]
  simp

/-- Helper for Remark 21.61: every dyadic square-variation witness starts from `0`. -/
lemma hasSquareVariationAlong_zero
    {H : PathSpace} {brH : PathwiseProcess} (hH : HasSquareVariationAlong H brH) :
    brH 0 = 0 := by
  -- Proof comment: compare the defining limit at time `0` with the identically vanishing dyadic
  -- square sums.
  have hlimH :
      Tendsto (dyadic_p_variation_sum 2 H 0) atTop (nhds (brH 0)) :=
    HasSquareVariationAlong.tendsto_partition_sum hH 0
  have hlim0 :
      Tendsto (dyadic_p_variation_sum 2 H 0) atTop (nhds (0 : ℝ)) := by
    have hzero : dyadic_p_variation_sum 2 H 0 = fun _ ↦ (0 : ℝ) := by
      funext n
      exact dyadicSquareVariationSum_zero H n
    rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlimH hlim0

/-- Helper for Remark 21.61: every dyadic square-variation increment is nonnegative. -/
lemma dyadicSquareVariationIncrement_nonneg
    (H : PathSpace) (T : NNReal) (n k : ℕ) :
    0 ≤
      Real.rpow
        (|H (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
            H (Definition2158.dyadicPartitionSequence n k)|)
        2 := by
  -- Proof comment: for exponent `2`, the dyadic square-variation term is an ordinary square.
  exact Real.rpow_nonneg (abs_nonneg _) _

/-- Helper for Remark 21.61: every dyadic partition point strictly before the truncation index
lies strictly below the time horizon `T`. -/
lemma dyadicPartition_lt_time_of_lt_boundIndex
    (n : ℕ) {T : NNReal} {k : ℕ}
    (hk : k < partitionBoundIndex Definition2158.dyadicPartitionSequence n T) :
    Definition2158.dyadicPartitionSequence n k < T := by
  -- Proof comment: otherwise `k` would already be a valid witness for `partitionBoundIndex`,
  -- contradicting the minimality of the chosen index.
  by_contra hnot
  have hle : T ≤ Definition2158.dyadicPartitionSequence n k := le_of_not_gt hnot
  have hmin :
      partitionBoundIndex Definition2158.dyadicPartitionSequence n T ≤ k :=
    Nat.find_min' (exists_partition_index_le_time Definition2158.dyadicPartitionSequence n T) hle
  exact (not_le_of_gt hk) hmin

/-- Helper for Remark 21.61: the dyadic truncation index is monotone in the time horizon. -/
lemma partitionBoundIndex_monotone (n : ℕ) :
    Monotone (fun T ↦ partitionBoundIndex Definition2158.dyadicPartitionSequence n T) := by
  intro s t hst
  -- Proof comment: the witness for `t` is also a valid witness for every smaller `s`.
  exact
    Nat.find_min'
      (exists_partition_index_le_time Definition2158.dyadicPartitionSequence n s)
      (le_trans hst
        (le_partitionBoundIndex_time Definition2158.dyadicPartitionSequence n t))

/-- Helper for Remark 21.61: the full dyadic square-sum only counts partition intervals whose
right endpoint is already at most `T`. -/
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

/-- Helper for Remark 21.61: the full dyadic square-sum is monotone in the terminal time `T`. -/
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
    Finset.range_subset_range.2 (partitionBoundIndex_monotone n hst)
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
            exact sq_nonneg
              (H (Definition2158.dyadicPartitionSequence n (k + 1)) -
                H (Definition2158.dyadicPartitionSequence n k))
          simpa only [Real.rpow_eq_pow, Real.rpow_ofNat, term, hs', ht', sq_abs] using hsq_nonneg
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

/-- Helper for Remark 21.61: the predecessor of the dyadic truncation index is the boundary point
whose distance to `T` is controlled by the dyadic mesh. -/
noncomputable def dyadicSquareVariationBoundaryPoint
    (T : NNReal) (n : ℕ) : NNReal :=
  Definition2158.dyadicPartitionSequence n
    (partitionBoundIndex Definition2158.dyadicPartitionSequence n T - 1)

/-- Helper for Remark 21.61: the dyadic boundary point converges to the terminal time `T`. -/
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

/-- Helper for Remark 21.61: replacing the clipped terminal dyadic increment by `0` changes the
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
      dyadicSquareVariationBoundaryPoint, partitionBoundIndex_zero,
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
      · simp
      · nlinarith [sq_nonneg (H T - H (dyadicSquareVariationBoundaryPoint T n))]
    · rw [hdyadic, hfull, if_neg hlast, add_zero]
      constructor
      · nlinarith [sq_nonneg (H T - H (dyadicSquareVariationBoundaryPoint T n))]
      · nlinarith

/-- Helper for Remark 21.61: the full dyadic square-sums have the same limit as the clipped
dyadic square-variation sums. -/
lemma tendsto_dyadicSquareVariationFullSum
    {H : PathSpace} {brH : PathwiseProcess} (hH : HasSquareVariationAlong H brH) (T : NNReal) :
    Tendsto (dyadicSquareVariationFullSum H T) atTop (nhds (brH T)) := by
  have hboundary_eval :
      Tendsto (fun n ↦ H (dyadicSquareVariationBoundaryPoint T n)) atTop (nhds (H T)) :=
    H.continuous.continuousAt.tendsto.comp (tendsto_dyadicSquareVariationBoundaryPoint T)
  have hboundary_sq :
      Tendsto (fun n ↦ (H T - H (dyadicSquareVariationBoundaryPoint T n)) ^ 2)
        atTop (nhds 0) := by
    -- Proof comment: continuity of `H` turns convergence of the boundary point into vanishing of
    -- the boundary increment, and squaring preserves the zero limit.
    have hsub :
        Tendsto (fun n ↦ H T - H (dyadicSquareVariationBoundaryPoint T n)) atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℕ ↦ H T) atTop (nhds (H T)) := tendsto_const_nhds
      simpa using hconst.sub hboundary_eval
    simpa using hsub.pow 2
  have herror :
      Tendsto
        (fun n ↦ dyadic_p_variation_sum 2 H T n - dyadicSquareVariationFullSum H T n)
        atTop
        (nhds 0) := by
    -- Proof comment: the correction term is trapped between `0` and the boundary square.
    refine
      squeeze_zero
        (fun n ↦ (dyadicSquareVariationSum_sub_fullSum_le_boundary H T n).1)
        (fun n ↦ (dyadicSquareVariationSum_sub_fullSum_le_boundary H T n).2)
        hboundary_sq
  have hsum :
      Tendsto (dyadic_p_variation_sum 2 H T) atTop (nhds (brH T)) :=
    HasSquareVariationAlong.tendsto_partition_sum hH T
  have hfull :
      Tendsto
        (fun n ↦
          dyadic_p_variation_sum 2 H T n -
            (dyadic_p_variation_sum 2 H T n - dyadicSquareVariationFullSum H T n))
        atTop
        (nhds (brH T - 0)) :=
    hsum.sub herror
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hfull

/-- Helper for Remark 21.61: a dyadic square-variation witness should start from `0` and be
monotone in time. -/
lemma hasSquareVariationAlong_zero_and_monotone
    {H : PathSpace} {brH : PathwiseProcess} (hH : HasSquareVariationAlong H brH) :
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

/-- Helper for Remark 21.61: scaling a real-valued path by `a` scales its total variation by at
most `|a|`. -/
lemma eVariationOn_const_mul_le
    {f : NNReal → ℝ} {a : ℝ} {T : NNReal} :
    eVariationOn (fun t ↦ a * f t) (Icc 0 T) ≤
      (‖a‖₊ : ℝ≥0∞) * eVariationOn f (Icc 0 T) := by
  -- Proof comment: scalar multiplication on `ℝ` is Lipschitz with constant `‖a‖`, so compose
  -- the variation of `f` with that Lipschitz map.
  simpa [Function.comp, Pi.smul_apply, smul_eq_mul] using
    ((lipschitzWith_smul a).lipschitzOnWith.comp_eVariationOn_le
      (g := f) (s := Icc 0 T) (mapsTo_univ f _))

/-- Helper for Remark 21.61: the `ENNReal` norm of `1 / 4` agrees with `ENNReal.ofReal (1 / 4)`.
-/
lemma ennreal_enorm_one_quarter :
    (‖(1 / 4 : ℝ)‖₊ : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by
  rw [show (‖(1 / 4 : ℝ)‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖(1 / 4 : ℝ)‖ by
    exact (ofReal_norm_eq_enorm (1 / 4 : ℝ)).symm]
  norm_num

/-- Helper for Remark 21.61: after reciprocal rescaling of `F` and `G`, the variation of the
covariation path is bounded by the corresponding weighted endpoint sum. -/
lemma eVariationOn_Icc_le_weighted_sum_of_hasQuadraticCovariationAlong
    {F G : PathSpace} {brF brG covFG : PathwiseProcess}
    (hF : HasSquareVariationAlong F brF)
    (hG : HasSquareVariationAlong G brG)
    (hFG : HasQuadraticCovariationAlong F G covFG)
    (T : NNReal) {c : ℝ} (hc : c ≠ 0) :
    eVariationOn covFG (Icc 0 T) ≤
      ENNReal.ofReal ((c ^ 2 * brF T + (c⁻¹) ^ 2 * brG T) / 2) := by
  let plusV : PathwiseProcess := fun t ↦ c ^ 2 * brF t + 2 * covFG t + (c⁻¹) ^ 2 * brG t
  let minusV : PathwiseProcess := fun t ↦ c ^ 2 * brF t - 2 * covFG t + (c⁻¹) ^ 2 * brG t
  have hFscaled : HasSquareVariationAlong (c • F) (fun t ↦ c ^ 2 * brF t) :=
    hasSquareVariationAlong_smul hF c
  have hGscaled : HasSquareVariationAlong (c⁻¹ • G) (fun t ↦ (c⁻¹) ^ 2 * brG t) :=
    hasSquareVariationAlong_smul hG c⁻¹
  have hFGscaled : HasQuadraticCovariationAlong (c • F) (c⁻¹ • G) covFG := by
    -- Proof comment: the reciprocal scaling keeps the mixed bracket path unchanged because
    -- `c * c⁻¹ = 1`.
    simpa [mul_inv_cancel₀ hc] using hasQuadraticCovariationAlong_smul hFG c c⁻¹
  have hplus : HasSquareVariationAlong ((c • F) + (c⁻¹ • G)) plusV := by
    -- Proof comment: the rescaled plus-combination has the explicit square-variation witness
    -- predicted by the polarization identity.
    simpa [plusV] using
      (hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong hFscaled hGscaled hFGscaled)
  have hminus : HasSquareVariationAlong ((c • F) - (c⁻¹ • G)) minusV := by
    -- Proof comment: the rescaled minus-combination has the companion explicit witness.
    simpa [minusV] using
      (hasSquareVariationAlong_sub_of_hasQuadraticCovariationAlong hFscaled hGscaled hFGscaled)
  obtain ⟨hplus_zero, hplus_mono⟩ := hasSquareVariationAlong_zero_and_monotone hplus
  obtain ⟨hminus_zero, hminus_mono⟩ := hasSquareVariationAlong_zero_and_monotone hminus
  have hquarter :
      ((1 / 4 : ℝ) • (plusV - minusV)) = covFG := by
    -- Proof comment: the quarter-difference of the two explicit witnesses is exactly the
    -- original covariation path.
    funext t
    simp [Pi.smul_apply, Pi.sub_apply, plusV, minusV, smul_eq_mul]
    ring_nf
  have hendpoint :
      (plusV T - plusV 0) + (minusV T - minusV 0) =
        2 * (c ^ 2 * brF T + (c⁻¹) ^ 2 * brG T) := by
    -- Proof comment: the monotone witnesses both start at `0`, so only their terminal values
    -- contribute to the variation bound.
    rw [hplus_zero, hminus_zero]
    simp only [plusV, minusV]
    ring
  calc
    eVariationOn covFG (Icc 0 T)
        = eVariationOn (((1 / 4 : ℝ) • (plusV - minusV))) (Icc 0 T) := by
            rw [hquarter]
    _ ≤ (‖(1 / 4 : ℝ)‖₊ : ℝ≥0∞) * eVariationOn (plusV - minusV) (Icc 0 T) := by
          -- Proof comment: total variation is Lipschitz under multiplication by a constant.
          simpa [Pi.smul_apply, smul_eq_mul] using
            (eVariationOn_const_mul_le (f := plusV - minusV) (a := (1 / 4 : ℝ)) (T := T))
    _ ≤ (‖(1 / 4 : ℝ)‖₊ : ℝ≥0∞) *
          ENNReal.ofReal ((plusV T - plusV 0) + (minusV T - minusV 0)) := by
          -- Proof comment: the difference of two monotone witnesses has variation controlled by
          -- the sum of their endpoint increments.
          have hvarBound :
              eVariationOn (plusV - minusV) (Icc 0 T) ≤
                ENNReal.ofReal ((plusV T - plusV 0) + (minusV T - minusV 0)) := by
            simpa using
              (eVariationOn_Icc_sub_le_of_monotone_process
                (G := plusV - minusV) (Gplus := plusV) (Gminus := minusV)
                rfl hplus_mono hminus_mono (s := 0) (t := T) bot_le)
          have hscaled :
              (‖(1 / 4 : ℝ)‖₊ : ℝ≥0∞) * eVariationOn (plusV - minusV) (Icc 0 T) ≤
                (‖(1 / 4 : ℝ)‖₊ : ℝ≥0∞) *
                  ENNReal.ofReal ((plusV T - plusV 0) + (minusV T - minusV 0)) :=
            mul_le_mul_right hvarBound (‖(1 / 4 : ℝ)‖₊ : ℝ≥0∞)
          simpa [mul_comm] using hscaled
    _ = ENNReal.ofReal ((c ^ 2 * brF T + (c⁻¹) ^ 2 * brG T) / 2) := by
          rw [ennreal_enorm_one_quarter,
            ← ENNReal.ofReal_mul (show 0 ≤ (1 / 4 : ℝ) by positivity), hendpoint]
          congr 1
          ring

/-- Helper for Remark 21.61: the fourth-root optimizer makes the weighted endpoint average equal
to the geometric mean `Real.sqrt (a * b)` when `a, b > 0`. -/
lemma weightedEndpointHalf_eq_sqrt_mul
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    let c : ℝ := Real.sqrt (Real.sqrt (b / a))
    (c ^ 2 * a + (c⁻¹) ^ 2 * b) / 2 = Real.sqrt (a * b) := by
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  let c : ℝ := Real.sqrt (Real.sqrt (b / a))
  have hc_sq : c ^ 2 = Real.sqrt (b / a) := by
    -- Proof comment: squaring the fourth-root optimizer removes one layer of `sqrt`.
    dsimp [c]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hcinv_sq : (c⁻¹) ^ 2 = Real.sqrt (a / b) := by
    -- Proof comment: the reciprocal square corresponds to swapping the quotient.
    calc
      (c⁻¹) ^ 2 = (c ^ 2)⁻¹ := by rw [inv_pow]
      _ = (Real.sqrt (b / a))⁻¹ := by rw [hc_sq]
      _ = Real.sqrt ((b / a)⁻¹) := by rw [← Real.sqrt_inv]
      _ = Real.sqrt (a / b) := by
          congr 1
          field_simp [ha_pos.ne', hb_pos.ne']
  have htermF : c ^ 2 * a = Real.sqrt (a * b) := by
    -- Proof comment: the optimizer makes the first weighted term equal to the geometric mean.
    let sa : ℝ := Real.sqrt a
    let sb : ℝ := Real.sqrt b
    have hsa_pos : 0 < sa := by
      dsimp [sa]
      exact Real.sqrt_pos.2 ha_pos
    have hsa_ne : sa ≠ 0 := hsa_pos.ne'
    calc
      c ^ 2 * a = (sb / sa) * (sa * sa) := by
        rw [hc_sq, Real.sqrt_div hb a, ← Real.sq_sqrt ha]
        rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
        dsimp [sa, sb]
        rw [pow_two]
      _ = sb * sa := by
          field_simp [hsa_ne]
      _ = Real.sqrt (a * b) := by
          dsimp [sa, sb]
          rw [mul_comm, ← Real.sqrt_mul ha b]
  have htermG : (c⁻¹) ^ 2 * b = Real.sqrt (a * b) := by
    -- Proof comment: the reciprocal weighted term matches the same geometric mean.
    let sa : ℝ := Real.sqrt a
    let sb : ℝ := Real.sqrt b
    have hsb_pos : 0 < sb := by
      dsimp [sb]
      exact Real.sqrt_pos.2 hb_pos
    have hsb_ne : sb ≠ 0 := hsb_pos.ne'
    calc
      (c⁻¹) ^ 2 * b = (sa / sb) * (sb * sb) := by
        rw [hcinv_sq, Real.sqrt_div ha b, ← Real.sq_sqrt hb]
        rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
        dsimp [sa, sb]
        rw [pow_two]
      _ = sa * sb := by
          field_simp [hsb_ne]
      _ = Real.sqrt (a * b) := by
          dsimp [sa, sb]
          rw [← Real.sqrt_mul ha b]
  -- Proof comment: both weighted terms coincide with the same optimal value.
  dsimp [c]
  rw [htermF, htermG]
  ring

-- Proof sketch: the mixed dyadic increment sum is the polarization combination of the dyadic
-- square-variation sums for `F + G` and `F - G`, so the limit path is
-- `t ↦ (⟨F + G⟩_t - ⟨F - G⟩_t) / 4`.
/-- Polarization companion for the dyadic bracket API: if `brAdd` and `brSub` are chosen square-
variation realizations of `F + G` and `F - G`, then `((1 / 4) • (brAdd - brSub))` realizes the
quadratic covariation of `F` and `G`; equivalently,
`⟨F,G⟩_T = (⟨F + G⟩_T - ⟨F - G⟩_T) / 4`. -/
theorem hasQuadraticCovariationAlong_polarization
    {F G : PathSpace} {brAdd brSub : PathwiseProcess}
    (hAdd : HasSquareVariationAlong (F + G) brAdd)
    (hSub : HasSquareVariationAlong (F - G) brSub) :
    HasQuadraticCovariationAlong F G ((1 / 4 : ℝ) • (brAdd - brSub)) := by
  intro T
  have hpolarized :
      Tendsto
        (fun n ↦
          ((dyadic_p_variation_sum 2 (F + G) T n) -
            (dyadic_p_variation_sum 2 (F - G) T n)) / 4)
        atTop
        (nhds (((1 / 4 : ℝ) • (brAdd - brSub)) T)) := by
    -- Proof comment: the mixed dyadic sums are the polarized difference of the two square
    -- variation sums, so their limit is the same polarized difference of the witness paths.
    simpa [Pi.smul_apply, Pi.sub_apply, div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm,
      mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((HasSquareVariationAlong.tendsto_partition_sum hAdd T).sub
        (HasSquareVariationAlong.tendsto_partition_sum hSub T)).mul_const (1 / 4 : ℝ)
  convert hpolarized using 1
  ext n
  simpa [dyadic_quadratic_covariation_sum, dyadic_p_variation_sum] using
    (partitionQuadraticCovariationSum_eq_polarization
      Definition2158.dyadicPartitionSequence F G T n)

-- Proof sketch: apply the pointwise Cauchy--Schwarz bound to the approximating sums and pass to
-- the limit; the dyadic first variations of the approximating mixed sums are bounded by
-- Cauchy--Schwarz. This is the mathlib-owner form of the textbook bound
-- `V_T^1(⟨F,G⟩) ≤ √(⟨F⟩_T * ⟨G⟩_T)`.
/-- Remark 21.61: for a chosen dyadic quadratic-covariation path `covFG` and chosen square
variation paths `brF`, `brG`, the total variation of `covFG` on `[0, T]` is bounded by
`Real.sqrt (brF T * brG T)`. This is clause `(ii)` of the source remark; equivalently, in
textbook notation, `V_T^1(⟨F,G⟩) ≤ Real.sqrt (⟨F⟩_T * ⟨G⟩_T)`. -/
theorem eVariationOn_Icc_le_sqrt_mul_of_hasQuadraticCovariationAlong
    {F G : PathSpace} {brF brG covFG : PathwiseProcess}
    (hF : HasSquareVariationAlong F brF)
    (hG : HasSquareVariationAlong G brG)
    (hFG : HasQuadraticCovariationAlong F G covFG)
    (T : NNReal) :
    eVariationOn covFG (Icc 0 T) ≤ ENNReal.ofReal (Real.sqrt (brF T * brG T)) := by
  obtain ⟨hbrF_zero, hbrF_mono⟩ := hasSquareVariationAlong_zero_and_monotone hF
  obtain ⟨hbrG_zero, hbrG_mono⟩ := hasSquareVariationAlong_zero_and_monotone hG
  have hbrF_nonneg : 0 ≤ brF T := by
    simpa [hbrF_zero] using hbrF_mono (show (0 : NNReal) ≤ T by exact bot_le)
  have hbrG_nonneg : 0 ≤ brG T := by
    simpa [hbrG_zero] using hbrG_mono (show (0 : NNReal) ≤ T by exact bot_le)
  have hinv_nat : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (nhds 0) := by
    simpa [one_mul] using
      (tendsto_mul_add_inv_atTop_nhds_zero 1 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hsq_nat : Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹) ^ 2) atTop (nhds 0) := by
    -- Proof comment: the reciprocal square still tends to `0`.
    simpa using hinv_nat.pow 2
  by_cases hbrF_T_zero : brF T = 0
  · have hbound :
        ∀ n : ℕ,
          eVariationOn covFG (Icc 0 T) ≤
            ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2 * brG T / 2) := by
      intro n
      -- Proof comment: if `brF T = 0`, the weighted estimate with `c = n + 1` leaves only the
      -- vanishing reciprocal-square term.
      simpa [hbrF_T_zero] using
        (eVariationOn_Icc_le_weighted_sum_of_hasQuadraticCovariationAlong
          hF hG hFG T (c := (n : ℝ) + 1) (by positivity))
    have hbound_tendsto_real :
        Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹) ^ 2 * brG T / 2) atTop (nhds 0) := by
      -- Proof comment: the remaining real bound is a fixed multiple of a reciprocal square.
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (hsq_nat.const_mul (brG T / 2))
    have hbound_tendsto :
        Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2 * brG T / 2))
          atTop
          (nhds 0) := by
      simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbound_tendsto_real
    have hle_zero : eVariationOn covFG (Icc 0 T) ≤ 0 := by
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds hbound_tendsto hbound
    simpa [hbrF_T_zero] using hle_zero
  · by_cases hbrG_T_zero : brG T = 0
    · have hbound :
          ∀ n : ℕ,
            eVariationOn covFG (Icc 0 T) ≤
              ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2 * brF T / 2) := by
        intro n
        -- Proof comment: if `brG T = 0`, use the weighted estimate with `c = (n + 1)⁻¹`.
        simpa [hbrG_T_zero, pow_two, inv_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          using
            (eVariationOn_Icc_le_weighted_sum_of_hasQuadraticCovariationAlong
              hF hG hFG T (c := ((n : ℝ) + 1)⁻¹) (by positivity))
      have hbound_tendsto_real :
          Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹) ^ 2 * brF T / 2) atTop (nhds 0) := by
        -- Proof comment: again the weighted endpoint bound decays like a reciprocal square.
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          (hsq_nat.const_mul (brF T / 2))
      have hbound_tendsto :
          Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((((n : ℝ) + 1)⁻¹) ^ 2 * brF T / 2))
            atTop
            (nhds 0) := by
        simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbound_tendsto_real
      have hle_zero : eVariationOn covFG (Icc 0 T) ≤ 0 := by
        exact le_of_tendsto_of_tendsto' tendsto_const_nhds hbound_tendsto hbound
      simpa [hbrG_T_zero] using hle_zero
    · have hbrF_pos : 0 < brF T := lt_of_le_of_ne hbrF_nonneg (Ne.symm hbrF_T_zero)
      have hbrG_pos : 0 < brG T := lt_of_le_of_ne hbrG_nonneg (Ne.symm hbrG_T_zero)
      let c : ℝ := Real.sqrt (Real.sqrt (brG T / brF T))
      have hc : c ≠ 0 := by
        -- Proof comment: in the strictly positive case, the fourth-root optimizer is nonzero.
        dsimp [c]
        exact Real.sqrt_ne_zero'.2 (Real.sqrt_pos.2 (div_pos hbrG_pos hbrF_pos))
      have hweighted :=
        eVariationOn_Icc_le_weighted_sum_of_hasQuadraticCovariationAlong
          hF hG hFG T (c := c) hc
      have hopt :
          (c ^ 2 * brF T + (c⁻¹) ^ 2 * brG T) / 2 =
            Real.sqrt (brF T * brG T) := by
        -- Proof comment: the fourth-root choice of `c` realizes the weighted bound exactly at
        -- the geometric mean.
        simpa [c] using
          (weightedEndpointHalf_eq_sqrt_mul hbrF_nonneg hbrG_nonneg hbrF_T_zero hbrG_T_zero)
      rw [hopt] at hweighted
      exact hweighted

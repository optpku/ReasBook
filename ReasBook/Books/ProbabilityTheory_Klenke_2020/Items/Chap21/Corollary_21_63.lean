/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_59

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open Set
open scoped BigOperators ENNReal Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

/-- Helper for Corollary 21.63: the `k`-th dyadic time in the `n`-th row is `k / 2^n`. -/
noncomputable def dyadicTime (n k : ℕ) : NNReal :=
  (k : NNReal) / (2 : NNReal) ^ n

/-- Helper for Corollary 21.63: `dyadicPointUpTo T n k` truncates the `k`-th dyadic time at `T`. -/
noncomputable def dyadicPointUpTo (T : NNReal) (n k : ℕ) : NNReal :=
  min T (dyadicTime n k)

/-- Helper for Corollary 21.63: `dyadicCutoff T n` is the dyadic resolution index used for the
truncated partition of `[0,T]`. -/
noncomputable def dyadicCutoff (T : NNReal) (n : ℕ) : ℕ :=
  Nat.ceil (T * (2 : NNReal) ^ n)

/-- Helper for Corollary 21.63: the `k`-th increment of `G` along the truncated `n`-th dyadic
partition of `[0,T]`. -/
noncomputable def dyadicIncrement (G : PathSpace) (T : NNReal) (n k : ℕ) : ℝ :=
  G (dyadicPointUpTo T n (k + 1)) - G (dyadicPointUpTo T n k)

/-- Helper for Corollary 21.63: the truncated dyadic quadratic-variation sum up to time `T`. -/
noncomputable def dyadicSquareVariationSum (G : PathSpace) (T : NNReal) (n : ℕ) : ℝ≥0∞ :=
  Finset.sum (Finset.range (dyadicCutoff T n)) fun k ↦
    (ENNReal.ofReal |dyadicIncrement G T n k|) ^ (2 : ℝ)

/-- Helper for Corollary 21.63: the truncated dyadic mixed variation sum up to time `T`. -/
noncomputable def dyadicQuadraticCovariationSum
    (F G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (dyadicCutoff T n)) fun k ↦
    dyadicIncrement F T n k * dyadicIncrement G T n k

/-- Helper for Corollary 21.63: the truncated dyadic row is monotone in the partition index. -/
lemma dyadicPointUpTo_mono (T : NNReal) (n : ℕ) :
    Monotone (dyadicPointUpTo T n) := by
  -- Proof comment: both the dyadic row and truncation by `min T` preserve monotonicity.
  intro i j hij
  apply min_le_min_left T
  dsimp [dyadicTime]
  have hpow : 0 ≤ (2 : NNReal) ^ n := by
    positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hpow

/-- Helper for Corollary 21.63: every truncated dyadic partition point lies in `Icc 0 T`. -/
lemma dyadicPointUpTo_mem_Icc (T : NNReal) (n i : ℕ) :
    dyadicPointUpTo T n i ∈ Icc 0 T := by
  -- Proof comment: truncation by `min T` keeps the dyadic point inside the interval bounds.
  constructor
  · positivity
  · exact min_le_left _ _

/-- Helper for Corollary 21.63: two square-variation realizations of the same path must agree. -/
lemma squareVariation_eq_of_twoRealizations
    {G : PathSpace} {V W : PathwiseProcess}
    (hV : HasSquareVariationAlong G V)
    (hW : HasSquareVariationAlong G W) :
    V = W := by
  -- Proof comment: compare the two pointwise limits of the same dyadic approximating sequence.
  funext T
  exact tendsto_nhds_unique (hV T) (hW T)

/- Corollary 21.63 is a `source-facing` bridge in the Chapter 21 dyadic square-variation API.
Its core owners are `HasSquareVariationAlong`, `HasQuadraticCovariationAlong`, and mathlib's
variation owner `LocallyBoundedVariationOn`; the relevant derived upstream API is the vanishing
textbook quadratic-variation result of Remark 21.59 and the polarization/covariation API of
Remark 21.61. The primitive data here are only chosen square-variation and covariation paths, and
the corollary records the special zero-right-bracket consequences for those owner objects. -/

variable {F G : PathSpace} {V VF VFG : PathwiseProcess}

-- Proof sketch: this is the preceding vanishing-bracket criterion specialized to a chosen
-- square-variation realization of a path of locally finite variation. Remark 21.59 shows that the
-- textbook quadratic variation is zero, so the dyadic square-variation owner is realized by the
-- zero path.
/-- A continuous path of locally finite variation has zero square variation along the dyadic
partitions. This is the owner-level bridge behind the parenthetical clause in Corollary 21.63. -/
theorem hasSquareVariationAlong_zero_of_locallyFiniteVariation
    (hG : LocallyBoundedVariationOn G univ) :
    HasSquareVariationAlong G 0 := by
  -- Proof comment: Remark 21.59 already gives the canonical dyadic `p = 2` convergence to `0`
  -- for every path of locally finite variation.
  intro T
  simpa using dyadicPVariationSumTwo_tendsto_zero_of_locallyBoundedVariationOn hG T

-- Proof sketch: compare an arbitrary chosen square-variation realization with the canonical zero
-- realization from `hasSquareVariationAlong_zero_of_locallyFiniteVariation`; uniqueness of limits
-- forces the chosen realization to equal `0`.
/-- A continuous path of locally finite variation has identically vanishing square variation along
every chosen square-variation realization. This is the witness-level companion to
`hasSquareVariationAlong_zero_of_locallyFiniteVariation`. -/
theorem squareVariation_eq_zero_of_locallyFiniteVariation
    (hV : HasSquareVariationAlong G V)
    (hG : LocallyBoundedVariationOn G univ) :
    V = 0 := by
  -- Proof comment: compare the chosen realization with the canonical zero realization.
  exact squareVariation_eq_of_twoRealizations hV
    (hasSquareVariationAlong_zero_of_locallyFiniteVariation hG)

/-- Helper for Corollary 21.63: the ENNReal dyadic square-variation sum reduces to the real finite
sum of squared increments. -/
lemma dyadicSquareVariationSum_toReal_eq
    (G : PathSpace) (T : NNReal) (n : ℕ) :
    (dyadicSquareVariationSum G T n).toReal =
      Finset.sum (Finset.range (dyadicCutoff T n)) (fun k ↦ (dyadicIncrement G T n k) ^ 2) := by
  -- Proof comment: rewrite the ENNReal square sum termwise into ordinary real squares.
  rw [dyadicSquareVariationSum, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro k hk
    simp [sq_abs]
  · intro k hk
    simp

/-- Helper for Corollary 21.63: the dyadic mixed sum is bounded by the geometric mean of the two
dyadic square sums. -/
lemma abs_dyadicQuadraticCovariationSum_le_sqrt_mul
    (F G : PathSpace) (T : NNReal) (n : ℕ) :
    |dyadicQuadraticCovariationSum F G T n| ≤
      Real.sqrt ((dyadicSquareVariationSum F T n).toReal) *
        Real.sqrt ((dyadicSquareVariationSum G T n).toReal) := by
  let s := Finset.range (dyadicCutoff T n)
  have hAbs :
      |dyadicQuadraticCovariationSum F G T n| ≤
        Finset.sum s (fun k ↦ |dyadicIncrement F T n k| * |dyadicIncrement G T n k|) := by
    -- Proof comment: first bound the absolute value of the mixed finite sum by the sum of the
    -- absolute mixed increments.
    simpa [dyadicQuadraticCovariationSum, s, abs_mul] using
      (Finset.abs_sum_le_sum_abs (s := s)
        (f := fun k ↦ dyadicIncrement F T n k * dyadicIncrement G T n k))
  have hCS :
      Finset.sum s (fun k ↦ |dyadicIncrement F T n k| * |dyadicIncrement G T n k|) ≤
        Real.sqrt (Finset.sum s (fun k ↦ |dyadicIncrement F T n k| ^ 2)) *
          Real.sqrt (Finset.sum s (fun k ↦ |dyadicIncrement G T n k| ^ 2)) := by
    -- Proof comment: apply the finite-dimensional Cauchy-Schwarz inequality to the absolute
    -- increment sequences.
    exact Real.sum_mul_le_sqrt_mul_sqrt s
      (fun k ↦ |dyadicIncrement F T n k|)
      (fun k ↦ |dyadicIncrement G T n k|)
  exact hAbs.trans <| by
    simpa [s, dyadicSquareVariationSum_toReal_eq, sq_abs] using hCS

/-- Helper for Corollary 21.63: the canonical dyadic mixed sum is bounded by the geometric mean
of the canonical dyadic square sums. -/
lemma abs_dyadicQuadraticCovariationAlong_le_sqrt_mul
    (F G : PathSpace) (T : NNReal) (n : ℕ) :
    |dyadic_quadratic_covariation_sum F G T n| ≤
      Real.sqrt (dyadic_p_variation_sum 2 F T n) *
        Real.sqrt (dyadic_p_variation_sum 2 G T n) := by
  let s := Finset.range (partitionBoundIndex Definition2158.dyadicPartitionSequence n T)
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      F (Definition2158.dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo Definition2158.dyadicPartitionSequence n k T) -
      G (Definition2158.dyadicPartitionSequence n k)
  have hAbs :
      |dyadic_quadratic_covariation_sum F G T n| ≤
        Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) := by
    simpa [dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum, s, ΔF, ΔG, abs_mul]
      using
        (Finset.abs_sum_le_sum_abs (s := s) (f := fun k ↦ ΔF k * ΔG k))
  have hCS :
      Finset.sum s (fun k ↦ |ΔF k| * |ΔG k|) ≤
        Real.sqrt (Finset.sum s (fun k ↦ |ΔF k| ^ 2)) *
          Real.sqrt (Finset.sum s (fun k ↦ |ΔG k| ^ 2)) := by
    exact Real.sum_mul_le_sqrt_mul_sqrt s (fun k ↦ |ΔF k|) (fun k ↦ |ΔG k|)
  exact hAbs.trans <| by
    simpa [dyadic_p_variation_sum, dyadic_quadratic_covariation_sum, partitionPVariationSum,
      partitionQuadraticCovariationSum, s, ΔF, ΔG, sq_abs] using hCS

-- Proof sketch: apply the vanishing-covariation criterion from the square-variation theory to the
-- pair `(F,G)` using that `F` admits a locally finite square-variation realization and that the
-- chosen square variation of `G` is zero.
/-- If `F` has locally finite square variation and `G` has zero square variation, then the zero
path is a quadratic-covariation realization of `F` and `G`. -/
theorem hasQuadraticCovariationAlong_zero_of_right_zeroSquareVariation
    (hVF : HasSquareVariationAlong F VF)
    (hVF_var : LocallyBoundedVariationOn VF univ)
    (hG : HasSquareVariationAlong G 0) :
    HasQuadraticCovariationAlong F G 0 := by
  let _ := hVF_var
  intro T
  have hFsqrt :
      Tendsto (fun n ↦ Real.sqrt (dyadic_p_variation_sum 2 F T n))
        atTop (nhds (Real.sqrt (VF T))) := by
    -- Proof comment: transport the square-variation limit of `F` through continuity of `sqrt`.
    exact Real.continuous_sqrt.continuousAt.tendsto.comp
      (show Tendsto (dyadic_p_variation_sum 2 F T) atTop (nhds (VF T)) from hVF T)
  have hGsqrt :
      Tendsto (fun n ↦ Real.sqrt (dyadic_p_variation_sum 2 G T n))
        atTop (nhds 0) := by
    -- Proof comment: the right square-variation path is identically zero, so its square-root
    -- approximants also converge to `0`.
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (show Tendsto (dyadic_p_variation_sum 2 G T) atTop (nhds 0) from hG T))
  have hBound :
      Tendsto
        (fun n ↦
          Real.sqrt (dyadic_p_variation_sum 2 F T n) *
            Real.sqrt (dyadic_p_variation_sum 2 G T n))
        atTop
        (nhds 0) := by
    -- Proof comment: the product bound tends to `0` because the right factor tends to `0`.
    simpa [Real.sqrt_zero] using hFsqrt.mul hGsqrt
  -- Proof comment: squeeze the mixed dyadic sums between `0` and the vanishing Cauchy-Schwarz
  -- bound.
  exact (tendsto_zero_iff_norm_tendsto_zero).2 <| by
    simpa [Real.norm_eq_abs] using
      (squeeze_zero
        (fun n ↦ abs_nonneg _)
        (fun n ↦ abs_dyadicQuadraticCovariationAlong_le_sqrt_mul F G T n)
        hBound)

/-- Helper for Corollary 21.63: the dyadic square sum of `F + G` expands into the square sums of
`F` and `G` plus twice the mixed dyadic sum. -/
lemma dyadicSquareVariationSum_add_toReal_eq
    (F G : PathSpace) (T : NNReal) (n : ℕ) :
    (dyadicSquareVariationSum (F + G) T n).toReal =
      (dyadicSquareVariationSum F T n).toReal + 2 * dyadicQuadraticCovariationSum F G T n +
        (dyadicSquareVariationSum G T n).toReal := by
  let s := Finset.range (dyadicCutoff T n)
  let fTerm : ℕ → ℝ := fun k ↦ (dyadicIncrement F T n k) ^ 2
  let gTerm : ℕ → ℝ := fun k ↦ (dyadicIncrement G T n k) ^ 2
  let fgTerm : ℕ → ℝ := fun k ↦ dyadicIncrement F T n k * dyadicIncrement G T n k
  calc
    (dyadicSquareVariationSum (F + G) T n).toReal =
        Finset.sum s (fun k ↦ (dyadicIncrement (F + G) T n k) ^ 2) := by
      -- Proof comment: first normalize the left dyadic square sum to a real finite sum.
      simpa [s] using dyadicSquareVariationSum_toReal_eq (F + G) T n
    _ = Finset.sum s (fun k ↦ fTerm k + 2 * fgTerm k + gTerm k) := by
      -- Proof comment: each squared increment of `F + G` expands by `(a + b)^2`.
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp only [fTerm, gTerm, fgTerm, dyadicIncrement, ContinuousMap.add_apply]
      ring
    _ = Finset.sum s fTerm + 2 * Finset.sum s fgTerm + Finset.sum s gTerm := by
      -- Proof comment: regroup the finite sums into the three canonical dyadic pieces.
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (dyadicSquareVariationSum F T n).toReal + 2 * dyadicQuadraticCovariationSum F G T n +
          (dyadicSquareVariationSum G T n).toReal := by
      -- Proof comment: rewrite the grouped sums back into the local owner API.
      rw [dyadicSquareVariationSum_toReal_eq, dyadicSquareVariationSum_toReal_eq]
      simp [dyadicQuadraticCovariationSum, s, fTerm, gTerm, fgTerm]

/-- Helper for Corollary 21.63: the canonical dyadic square sum of `F + G` expands into the
canonical square sums of `F` and `G` plus twice the canonical mixed dyadic sum. -/
lemma dyadicPVariationSumTwo_add_eq
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
  -- Proof comment: expand each canonical dyadic increment of `F + G` and regroup the finite sum
  -- into the `F`-, mixed-, and `G`-parts.
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

-- Proof sketch: from the chosen square-variation paths of `F + G`, `F`, and `G = 0`, the dyadic
-- identity `[F + G] = [F] + 2[F,G] + [G]` yields a quadratic-covariation realization
-- `((1 / 2) • (VFG - VF))` for `(F,G)`. Part (1) forces that covariation path to vanish, and then
-- the bracket identity reduces to `VFG = VF`.
/-- Corollary 21.63: if `F` has locally finite square variation and `G` has zero square
variation, then every chosen square-variation path of `F + G` equals the chosen square-variation
path of `F`. -/
theorem squareVariation_add_eq_left_of_right_zeroSquareVariation
    (hVF : HasSquareVariationAlong F VF)
    (hVF_var : LocallyBoundedVariationOn VF univ)
    (hG : HasSquareVariationAlong G 0)
    (hVFG : HasSquareVariationAlong (F + G) VFG) :
    VFG = VF := by
  have hFGzero : HasQuadraticCovariationAlong F G 0 :=
    hasQuadraticCovariationAlong_zero_of_right_zeroSquareVariation hVF hVF_var hG
  refine squareVariation_eq_of_twoRealizations hVFG ?_
  intro T
  have hFsum : Tendsto (dyadic_p_variation_sum 2 F T) atTop (nhds (VF T)) := hVF T
  have hGsum : Tendsto (dyadic_p_variation_sum 2 G T) atTop (nhds 0) := hG T
  have hFGsum : Tendsto (dyadic_quadratic_covariation_sum F G T) atTop (nhds 0) := hFGzero T
  have hsum :
      Tendsto
        (fun n ↦
          dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
            dyadic_p_variation_sum 2 G T n)
        atTop
        (nhds (VF T)) := by
    -- Proof comment: transport the three convergences of `F`, `[F,G] = 0`, and `G` through the
    -- dyadic add-expansion.
    simpa [add_assoc] using hFsum.add ((hFGsum.const_mul 2).add hGsum)
  -- Proof comment: the dyadic square sums of `F + G` have the same pointwise limit as those of
  -- `F`, so uniqueness of realizations identifies `VFG` with `VF`.
  convert hsum using 1
  ext n
  simpa using dyadicPVariationSumTwo_add_eq F G T n

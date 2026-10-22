/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Corollary_21_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_56
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_10_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_10_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_4_6

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory BigOperators OrderDual
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "PathSpace" => C(NNReal, ℝ)

/-- Helper for Theorem 21.64: the constant-weight quadratic partition sum, viewed as a real random
variable on the sample space. -/
noncomputable def partitionQuadraticVariationApproximationUpToRandomVariable
    (X : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    weightedPartitionQuadraticVariationApproximationUpTo
      (fun _ ↦ (1 : ℝ)) (fun t ↦ X t ω) P T n

section

variable (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]

/-- Unfolding the random-variable bridge recovers the underlying pathwise quadratic partition sum.
-/
theorem partitionQuadraticVariationApproximationUpToRandomVariable_def
    (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) :
    partitionQuadraticVariationApproximationUpToRandomVariable X P T n =
      fun ω ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (fun _ ↦ (1 : ℝ)) (fun t ↦ X t ω) P T n :=
  rfl

end

/-- Helper for Theorem 21.64: a Brownian increment over `[s, t]` has fourth moment
`3 * (t - s)^2`. -/
-- TODO: prove this by a local centered-Gaussian fourth-moment calculation, avoiding the broken
-- upstream Exercise 21.2.1 import.
lemma brownianIncrement_fourth_integral_eq_three_mul_sq_timeLag
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {s t : NNReal} (hst : s ≤ t) :
    ∫ ω, (W t ω - W s ω) ^ (4 : ℕ) ∂μ = 3 * (((t - s : NNReal) : ℝ) ^ (2 : ℕ)) := by
  let lag : NNReal := t - s
  let c : ℝ := Real.sqrt (lag : ℝ)
  have hLaw : HasLaw (fun ω ↦ W t ω - W s ω) (gaussianReal 0 lag) μ :=
    brownianIncrement_hasLaw_ofBrownianMotion hW hst
  have hStdId : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    { aemeasurable := measurable_id'.aemeasurable
      map_eq := by simp }
  have hStdFourth :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 = 3 := by
    -- Proof comment: the standard Gaussian fourth moment is the even-moment formula at `k = 2`.
    have hMoment :=
      (gaussianReal_even_moments_eq_factorial_ratio
        (P' := gaussianReal 0 1) (Y := id) hStdId 2)
    norm_num at hMoment
    exact hMoment
  have hScaleLaw :
      HasLaw (fun x : ℝ ↦ c * x) (gaussianReal 0 lag) (gaussianReal 0 1) := by
    -- Proof comment: `N(0, lag)` is the image of the standard Gaussian under multiplication by
    -- `sqrt lag`.
    simpa [c, lag, sq_abs, Real.sq_sqrt] using
      (gaussianReal_const_mul
        (P := gaussianReal 0 1) (X := id) (μ := (0 : ℝ)) (v := (1 : NNReal)) hStdId c)
  have hFourthBase :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 lag = 3 * ((lag : ℝ) ^ (2 : ℕ)) := by
    calc
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 lag
          = ∫ x : ℝ, (c * x) ^ (4 : ℕ) ∂gaussianReal 0 1 := by
              symm
              simpa [Function.comp] using
                (hScaleLaw.integral_comp
                  (f := fun x : ℝ ↦ x ^ (4 : ℕ))
                  ((continuous_pow 4).aestronglyMeasurable))
      _ = ∫ x : ℝ, c ^ (4 : ℕ) * x ^ (4 : ℕ) ∂gaussianReal 0 1 := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [mul_pow]
      _ = c ^ (4 : ℕ) * ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 := by
            rw [integral_const_mul]
      _ = c ^ (4 : ℕ) * 3 := by
            rw [hStdFourth]
      _ = 3 * ((lag : ℝ) ^ (2 : ℕ)) := by
            have hlag_nonneg : 0 ≤ (lag : ℝ) := by
              exact_mod_cast lag.2
            have hsq : c ^ (2 : ℕ) = (lag : ℝ) := by
              simp [c, Real.sq_sqrt, hlag_nonneg]
            have hpow : c ^ (4 : ℕ) = (lag : ℝ) ^ (2 : ℕ) := by
              rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
            rw [hpow, mul_comm]
  -- Proof comment: transport the quartic moment from the Brownian increment to its Gaussian owner.
  calc
    ∫ ω, (W t ω - W s ω) ^ (4 : ℕ) ∂μ
        = ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 lag := by
            exact
              hLaw.integral_comp
                (f := fun x : ℝ ↦ x ^ (4 : ℕ))
                ((continuous_pow 4).aestronglyMeasurable)
    _ = 3 * ((lag : ℝ) ^ (2 : ℕ)) := hFourthBase
    _ = 3 * (((t - s : NNReal) : ℝ) ^ (2 : ℕ)) := by
          simp [lag]

/-- Helper for Theorem 21.64: the centered squared Brownian increment has variance
`2 * (t - s)^2`. -/
-- TODO: expand the centered square and evaluate the second and fourth moments termwise.
lemma brownianIncrement_sq_sub_timeLag_variance_eq_two_mul_sq_timeLag
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {s t : NNReal} (hst : s ≤ t) :
    Var[fun ω ↦ (W t ω - W s ω) ^ (2 : ℕ) - ((t - s : NNReal) : ℝ); μ] =
      2 * (((t - s : NNReal) : ℝ) ^ (2 : ℕ)) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let inc : Ω → ℝ := fun ω ↦ W t ω - W s ω
  let lag : ℝ := ((t - s : NNReal) : ℝ)
  have hInc_gauss : HasGaussianLaw inc μ :=
    (brownianIncrement_hasLaw_ofBrownianMotion hW hst).hasGaussianLaw
  have hInc_memFour : MemLp inc 4 μ := hInc_gauss.memLp (by norm_num)
  have hIncSq_memTwo : MemLp (fun ω ↦ inc ω ^ (2 : ℕ)) 2 μ := by
    refine
      (memLp_two_iff_integrable_sq
        ((continuous_pow 2).aestronglyMeasurable.comp_aemeasurable hInc_gauss.aemeasurable)).2 ?_
    refine (hInc_memFour.integrable_norm_pow').congr ?_
    filter_upwards with ω
    have habs_sq : |inc ω| ^ (2 : ℕ) = inc ω ^ (2 : ℕ) := by
      simpa [sq_abs]
    calc
      ‖inc ω‖ ^ (4 : ℕ) = |inc ω| ^ (4 : ℕ) := by simp [Real.norm_eq_abs]
      _ = (|inc ω| ^ (2 : ℕ)) ^ (2 : ℕ) := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = (inc ω ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [habs_sq]
  have hVarSq : Var[fun ω ↦ inc ω ^ (2 : ℕ); μ] = 2 * (lag ^ (2 : ℕ)) := by
    rw [variance_eq_sub hIncSq_memTwo]
    have hSecond : ∫ ω, inc ω ^ (2 : ℕ) ∂μ = lag := by
      -- Proof comment: the raw second moment of the increment is its time lag.
      simpa [inc, lag] using
        brownianIncrement_sq_integral_eq_timeLag (μ := μ) (B := W) hW hst
    have hFourth : ∫ ω, inc ω ^ (4 : ℕ) ∂μ = 3 * (lag ^ (2 : ℕ)) := by
      -- Proof comment: the quartic moment is the Gaussian fourth moment from the previous lemma.
      simpa [inc, lag] using
        brownianIncrement_fourth_integral_eq_three_mul_sq_timeLag
          (μ := μ) (W := W) hW hst
    have hFourthSq :
        ∫ ω, ((fun ω ↦ inc ω ^ (2 : ℕ)) ^ (2 : ℕ)) ω ∂μ = 3 * (lag ^ (2 : ℕ)) := by
      calc
        ∫ ω, ((fun ω ↦ inc ω ^ (2 : ℕ)) ^ (2 : ℕ)) ω ∂μ
            = ∫ ω, inc ω ^ (4 : ℕ) ∂μ := by
                refine integral_congr_ae ?_
                filter_upwards with ω
                simp only [Pi.pow_apply]
                rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
        _ = 3 * (lag ^ (2 : ℕ)) := hFourth
    rw [hFourthSq, hSecond]
    ring
  -- Proof comment: subtracting a deterministic constant does not change the variance.
  calc
    Var[fun ω ↦ inc ω ^ (2 : ℕ) - lag; μ] = Var[fun ω ↦ inc ω ^ (2 : ℕ); μ] := by
      simpa using
        (ProbabilityTheory.variance_sub_const hIncSq_memTwo.aestronglyMeasurable lag)
    _ = 2 * (lag ^ (2 : ℕ)) := hVarSq
    _ = 2 * (((t - s : NNReal) : ℝ) ^ (2 : ℕ)) := by
          simp [lag]

/-- Helper for Theorem 21.64: a centered squared Brownian increment over `[s, t]` belongs to
`L²`. -/
-- TODO: deduce `L²` from the explicit variance formula once the centered-square variance lemma is
-- restored.
lemma brownianIncrement_sq_sub_timeLag_memLp_two
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    {s t : NNReal} (hst : s ≤ t) :
    MemLp (fun ω ↦ (W t ω - W s ω) ^ (2 : ℕ) - ((t - s : NNReal) : ℝ)) 2 μ := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let inc : Ω → ℝ := fun ω ↦ W t ω - W s ω
  let lag : ℝ := ((t - s : NNReal) : ℝ)
  have hInc_gauss : HasGaussianLaw inc μ :=
    (brownianIncrement_hasLaw_ofBrownianMotion hW hst).hasGaussianLaw
  have hInc_memFour : MemLp inc 4 μ := hInc_gauss.memLp (by norm_num)
  have hIncSq_memTwo : MemLp (fun ω ↦ inc ω ^ (2 : ℕ)) 2 μ := by
    refine
      (memLp_two_iff_integrable_sq
        ((continuous_pow 2).aestronglyMeasurable.comp_aemeasurable hInc_gauss.aemeasurable)).2 ?_
    refine (hInc_memFour.integrable_norm_pow').congr ?_
    filter_upwards with ω
    have habs_sq : |inc ω| ^ (2 : ℕ) = inc ω ^ (2 : ℕ) := by
      simpa [sq_abs]
    calc
      ‖inc ω‖ ^ (4 : ℕ) = |inc ω| ^ (4 : ℕ) := by simp [Real.norm_eq_abs]
      _ = (|inc ω| ^ (2 : ℕ)) ^ (2 : ℕ) := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = (inc ω ^ (2 : ℕ)) ^ (2 : ℕ) := by rw [habs_sq]
  -- Proof comment: the centered square is the `L²` increment square shifted by a deterministic
  -- constant.
  simpa [inc, lag] using hIncSq_memTwo.sub (memLp_const lag)

/-- Helper for Theorem 21.64: the clipped partition intervals up to the horizon `1` telescope to
total length `1`. -/
lemma partitionPoint_le_partitionNextPointUpTo_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) {T : NNReal} (hk : k < partitionBoundIndex P n T) :
    P n k ≤ partitionNextPointUpTo P n k T := by
  -- Proof comment: before the truncation index, the clipped successor is the minimum of the next
  -- row point and the horizon, both of which lie to the right of `P n k`.
  rw [partitionNextPointUpTo]
  refine le_min ?_ ?_
  · exact le_of_lt ((IsAdmissiblePartitionSequence.strictMono (P := P) n) (Nat.lt_succ_self k))
  · exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n k T hk)

/-- Helper for Theorem 21.64: before the clipping index at horizon `1`, the clipped interval
length is exactly the `edist` between the left endpoint and its clipped successor. -/
lemma partitionIntervalEdist_eq_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (hk : k < partitionBoundIndex P n 1) :
    edist (P n k) (partitionNextPointUpTo P n k 1) =
      ENNReal.ofReal ((((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))) := by
  have hst : P n k ≤ partitionNextPointUpTo P n k 1 :=
    partitionPoint_le_partitionNextPointUpTo_of_lt_partitionBoundIndex P n k hk
  -- Proof comment: swap the endpoints so that `NNReal.dist_eq` exposes the nonnegative interval
  -- length, then coerce the `NNReal` subtraction to `ℝ`.
  rw [edist_comm, edist_dist, NNReal.dist_eq, abs_of_nonneg]
  · rw [NNReal.coe_sub hst]
  · exact sub_nonneg.mpr (by exact_mod_cast hst)

/-- Helper for Theorem 21.64: the clipped partition intervals up to the horizon `1` telescope to
total length `1`. -/
lemma sum_partitionNextPointUpTo_sub_partitionPoint_eq_one
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    Finset.sum (Finset.range (partitionBoundIndex P n 1))
      (fun k ↦ (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))) = 1 := by
  let m := partitionBoundIndex P n 1
  have hm_ne : m ≠ 0 := by
    intro hm
    have hle : (1 : NNReal) ≤ P n 0 := by
      simpa [m, hm] using le_partitionBoundIndex_time P n 1
    simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
  have hsum :
      ∀ r : ℕ,
        (Finset.sum (Finset.range r) fun j ↦ ((P n (j + 1) : NNReal) : ℝ) - (P n j : ℝ)) =
          (P n r : ℝ) - (P n 0 : ℝ) := by
    intro r
    induction r with
    | zero =>
        simp
    | succ r ihr =>
        rw [Finset.sum_range_succ, ihr]
        ring
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne
  have hkm : partitionBoundIndex P n 1 = k.succ := by
    simpa [m] using hk
  have hprefix :
      (Finset.sum (Finset.range k) fun j ↦
          (((partitionNextPointUpTo P n j 1 - P n j : NNReal) : ℝ))) =
        (P n k : ℝ) - (P n 0 : ℝ) := by
    -- Proof comment: before the last contributing index, the clipped successor is the genuine
    -- next partition point, so the row telescopes exactly.
    have hraw :
        (Finset.sum (Finset.range k) fun j ↦
            (((partitionNextPointUpTo P n j 1 - P n j : NNReal) : ℝ))) =
          Finset.sum (Finset.range k) fun j ↦ ((P n (j + 1) : NNReal) : ℝ) - (P n j : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj_lt : j + 1 < partitionBoundIndex P n 1 := by
        simpa [m, hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
      have hnext : partitionNextPointUpTo P n j 1 = P n (j + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (j + 1) 1 hj_lt)
      rw [hnext]
      exact
        NNReal.coe_sub
          (le_of_lt ((IsAdmissiblePartitionSequence.strictMono (P := P) n) (Nat.lt_succ_self j)))
    exact hraw.trans (hsum k)
  have hlast :
      (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)) = 1 - (P n k : ℝ) := by
    -- Proof comment: the final clipped successor is the horizon `1` itself.
    have hk_lt : k < partitionBoundIndex P n 1 := by
      simpa [hkm] using Nat.lt_succ_self k
    have hnext : partitionNextPointUpTo P n k 1 = 1 := by
      rw [partitionNextPointUpTo, min_eq_right]
      simpa [m, hk] using le_partitionBoundIndex_time P n 1
    rw [hnext]
    rw [NNReal.coe_sub (le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n k 1 hk_lt))]
    simp
  rw [hkm, Finset.sum_range_succ, hprefix, hlast]
  simp [IsAdmissiblePartitionSequence.zero_eq (P := P) n]

/-- Helper for Theorem 21.64: after subtracting the deterministic horizon `1`, the fixed-time
quadratic partition sum is the finite sum of centered squared Brownian increments. -/
lemma partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_eq_sum_centeredSquares
    {μ : Measure Ω} {W : NNReal → Ω → ℝ}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    (fun ω ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1) =
      fun ω ↦
        Finset.sum (Finset.range (partitionBoundIndex P n 1)) (fun k ↦
          ((W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ) -
            (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)))) := by
  -- Proof comment: rewrite the deterministic compensator `1` as the telescoping sum of clipped
  -- interval lengths, then merge the two finite sums termwise.
  funext ω
  rw [partitionQuadraticVariationApproximationUpToRandomVariable_def]
  simp only [weightedPartitionQuadraticVariationApproximationUpTo_def, one_mul]
  rw [show (1 : ℝ) =
      Finset.sum (Finset.range (partitionBoundIndex P n 1))
        (fun k ↦ (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))) by
        symm
        exact sum_partitionNextPointUpTo_sub_partitionPoint_eq_one P n]
  rw [← Finset.sum_sub_distrib]

/-- Helper for Theorem 21.64: the centered clipped squared increments in the horizon-`1` row are
independent. -/
private lemma centeredClippedRow_iIndepFun
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    iIndepFun
      (fun i : Fin (partitionBoundIndex P n 1) ↦
        fun ω ↦
          (W (partitionNextPointUpTo P n i 1) ω - W (P n i) ω) ^ (2 : ℕ) -
            (((partitionNextPointUpTo P n i 1 - P n i : NNReal) : ℝ)))
      μ := by
  let m := partitionBoundIndex P n 1
  let τ : ℕ → NNReal := fun k ↦ if h : k < m then P n k else 1
  let Y : ℕ → Ω → ℝ := fun k ω ↦ W (τ (k + 1)) ω - W (τ k) ω
  have hτmono : Monotone τ := by
    intro a b hab
    by_cases hb : b < m
    · have ha : a < m := lt_of_le_of_lt hab hb
      simp [τ, ha, hb]
      exact (IsAdmissiblePartitionSequence.strictMono (P := P) n).monotone hab
    · by_cases ha : a < m
      · have hτa_le : τ a ≤ 1 := by
          simp [τ, ha]
          exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n a 1 ha)
        simpa [τ, hb] using hτa_le
      · simp [τ, ha, hb]
  have hY_indepNat : iIndepFun Y μ := by
    -- Proof comment: the clipped row is obtained from Brownian increments along one monotone mesh
    -- `τ`, so the Brownian independent-increments axiom applies directly.
    simpa [Y, τ, add_assoc, add_left_comm, add_comm] using
      hW.indepIncrements.nat (t := τ) hτmono
  have hτ_self :
      ∀ i : Fin m, τ i = P n i := by
    intro i
    simp [τ, i.is_lt]
  have hτ_succ :
      ∀ i : Fin m, τ (i + 1) = partitionNextPointUpTo P n i 1 := by
    intro i
    by_cases hsucc : (i : ℕ) + 1 < m
    · have hnext : partitionNextPointUpTo P n i 1 = P n (i + 1) := by
        rw [partitionNextPointUpTo, min_eq_left]
        exact le_of_lt (partitionPoint_lt_time_of_lt_partitionBoundIndex P n (i + 1) 1 hsucc)
      simp [τ, hsucc, hnext]
    · have hm : m = (i : ℕ) + 1 := by
        exact le_antisymm (Nat.not_lt.mp hsucc) (Nat.succ_le_of_lt i.is_lt)
      have hnext : partitionNextPointUpTo P n i 1 = 1 := by
        rw [partitionNextPointUpTo, min_eq_right]
        simpa [m, hm] using le_partitionBoundIndex_time P n 1
      simp [τ, hsucc, hm, hnext]
  have hIncrement_indep :
      iIndepFun
        (fun i : Fin m ↦ fun ω ↦ W (partitionNextPointUpTo P n i 1) ω - W (P n i) ω)
        μ := by
    -- Proof comment: restricting the `ℕ`-indexed increment family to `Fin m` keeps independence,
    -- and the mesh identities `τ i = P n i`, `τ (i+1) = partitionNextPointUpTo ...` normalize the
    -- endpoints back to the clipped partition row.
    simpa [Y, hτ_self, hτ_succ] using
      hY_indepNat.precomp (g := fun i : Fin m ↦ (i : ℕ)) fun a b h ↦ Fin.ext h
  -- Proof comment: measurable coordinatewise postcomposition by `x ↦ x^2 - cᵢ` preserves
  -- independence of the clipped Brownian increment family.
  simpa using
    hIncrement_indep.comp
      (fun i x ↦ x ^ (2 : ℕ) - (((partitionNextPointUpTo P n i 1 - P n i : NNReal) : ℝ)))
      (fun _ ↦ (continuous_pow 2).measurable.sub measurable_const)

/-- Helper for Theorem 21.64: the centered clipped squared increments in the horizon-`1` row are
pairwise uncorrelated. -/
private lemma centeredClippedRow_pairwiseUncorrelated
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    Pairwise fun i j : Fin (partitionBoundIndex P n 1) ↦
      cov[
        (fun ω ↦
          (W (partitionNextPointUpTo P n i 1) ω - W (P n i) ω) ^ (2 : ℕ) -
            (((partitionNextPointUpTo P n i 1 - P n i : NNReal) : ℝ))),
        (fun ω ↦
          (W (partitionNextPointUpTo P n j 1) ω - W (P n j) ω) ^ (2 : ℕ) -
            (((partitionNextPointUpTo P n j 1 - P n j : NNReal) : ℝ)));
        μ] = 0 := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hRow_indep := centeredClippedRow_iIndepFun (μ := μ) (W := W) hW P n
  have hterm_mem :
      ∀ i : Fin (partitionBoundIndex P n 1),
        MemLp
          (fun ω ↦
            (W (partitionNextPointUpTo P n i 1) ω - W (P n i) ω) ^ (2 : ℕ) -
              (((partitionNextPointUpTo P n i 1 - P n i : NNReal) : ℝ)))
          2 μ := by
    intro i
    have hst :
        P n i ≤ partitionNextPointUpTo P n i 1 :=
      partitionPoint_le_partitionNextPointUpTo_of_lt_partitionBoundIndex P n i i.is_lt
    -- Proof comment: each centered row entry is exactly one centered Brownian increment square.
    simpa using
      brownianIncrement_sq_sub_timeLag_memLp_two
        (μ := μ) (W := W) hW
        (s := P n i) (t := partitionNextPointUpTo P n i 1) hst
  intro i j hij
  -- Proof comment: independent square-integrable row entries have zero covariance.
  exact (hRow_indep.indepFun hij).covariance_eq_zero (hterm_mem i) (hterm_mem j)

/-- Helper for Theorem 21.64: the centered horizon-`1` quadratic partition sum has variance
bounded by `2 * ((partitionMesh P n) ⊓ 1).toReal`. -/
lemma partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_variance_le_two_mul_partitionMesh
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    Var[fun ω ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1; μ] ≤
      2 * ((partitionMesh P n) ⊓ 1).toReal := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let m := partitionBoundIndex P n 1
  let Z : Fin m → Ω → ℝ := fun i ω ↦
    (W (partitionNextPointUpTo P n i 1) ω - W (P n i) ω) ^ (2 : ℕ) -
      (((partitionNextPointUpTo P n i 1 - P n i : NNReal) : ℝ))
  let lag : Fin m → ℝ := fun i ↦
    (((partitionNextPointUpTo P n i 1 - P n i : NNReal) : ℝ))
  have hZ_indep : iIndepFun Z μ := by
    simpa [Z, m] using centeredClippedRow_iIndepFun (μ := μ) (W := W) hW P n
  have hZ_mem :
      ∀ i : Fin m, MemLp (Z i) 2 μ := by
    intro i
    have hst :
        P n i ≤ partitionNextPointUpTo P n i 1 :=
      partitionPoint_le_partitionNextPointUpTo_of_lt_partitionBoundIndex P n i (by simpa [m] using i.is_lt)
    -- Proof comment: the variance estimate uses the same `L²` Brownian increment package
    -- termwise on the clipped row.
    simpa [Z, m] using
      brownianIncrement_sq_sub_timeLag_memLp_two
        (μ := μ) (W := W) hW
        (s := P n i) (t := partitionNextPointUpTo P n i 1) hst
  have hRowEq :
      (fun ω ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1) =
        fun ω ↦ ∑ i : Fin m, Z i ω := by
    funext ω
    have hsum :=
      congrFun
        (partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_eq_sum_centeredSquares
          (μ := μ) (W := W) P n)
        ω
    rw [hsum]
    symm
    simpa [Z, m] using
      (Fin.sum_univ_eq_sum_range
        (fun k : ℕ ↦
          ((W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ) -
            (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))))
        m)
  have hVarSum :
      Var[∑ i : Fin m, Z i; μ] = ∑ i : Fin m, Var[Z i; μ] := by
    -- Proof comment: once the centered row is expressed as an independent finite family, the
    -- finite variance-additivity theorem collapses the row variance to the sum of diagonal terms.
    simpa using
      ProbabilityTheory.IndepFun.variance_sum
        (μ := μ) (X := Z) (s := Finset.univ)
        (hs := fun i _ ↦ hZ_mem i)
        (by
          intro i _ j _ hij
          exact hZ_indep.indepFun hij)
  have hVarEntry :
      ∀ i : Fin m, Var[Z i; μ] = 2 * (lag i ^ (2 : ℕ)) := by
    intro i
    have hst :
        P n i ≤ partitionNextPointUpTo P n i 1 :=
      partitionPoint_le_partitionNextPointUpTo_of_lt_partitionBoundIndex P n i (by simpa [m] using i.is_lt)
    -- Proof comment: each diagonal variance is the centered Brownian increment variance
    -- `2 * (Δt)^2`.
    simpa [Z, lag, m] using
      brownianIncrement_sq_sub_timeLag_variance_eq_two_mul_sq_timeLag
        (μ := μ) (W := W) hW
        (s := P n i) (t := partitionNextPointUpTo P n i 1) hst
  have hlag_sum : ∑ i : Fin m, lag i = 1 := by
    calc
      ∑ i : Fin m, lag i
          = Finset.sum (Finset.range m)
              (fun k ↦ (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))) := by
                simpa [lag] using
                  (Fin.sum_univ_eq_sum_range
                    (fun k : ℕ ↦ (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))) m)
      _ = 1 := by
            simpa [m] using sum_partitionNextPointUpTo_sub_partitionPoint_eq_one P n
  have hlag_le :
      ∀ i : Fin m, lag i ≤ ((partitionMesh P n) ⊓ 1).toReal := by
    intro i
    have hk : (i : ℕ) < partitionBoundIndex P n 1 := by
      simpa [m] using i.is_lt
    have hmesh :
        ENNReal.ofReal (lag i) ≤ (partitionMesh P n) ⊓ 1 := by
      refine le_inf ?_ ?_
      · rw [← partitionIntervalEdist_eq_of_lt_partitionBoundIndex P n i hk]
        exact edist_partitionPoint_partitionNextPointUpTo_le_partitionMesh P n i 1 hk
      · have hlag_le_one : lag i ≤ 1 := by
          have hnext_le : partitionNextPointUpTo P n i 1 ≤ 1 := by
            rw [partitionNextPointUpTo]
            exact min_le_right _ _
          exact le_trans (by exact_mod_cast (tsub_le_self : partitionNextPointUpTo P n i 1 - P n i ≤ partitionNextPointUpTo P n i 1))
            (by exact_mod_cast hnext_le)
        simpa using ENNReal.ofReal_le_ofReal hlag_le_one
    exact (ENNReal.ofReal_le_iff_le_toReal (by simp : ((partitionMesh P n) ⊓ 1) ≠ ⊤)).1 hmesh
  have hSumBound :
      ∑ i : Fin m, 2 * (lag i ^ (2 : ℕ)) ≤ 2 * ((partitionMesh P n) ⊓ 1).toReal := by
    have hterm :
        ∀ i : Fin m,
          2 * (lag i ^ (2 : ℕ)) ≤
            2 * ((((partitionMesh P n) ⊓ 1).toReal) * lag i) := by
      intro i
      have hlag_nonneg : 0 ≤ lag i := by positivity
      nlinarith [hlag_nonneg, hlag_le i]
    calc
      ∑ i : Fin m, 2 * (lag i ^ (2 : ℕ))
          ≤ ∑ i : Fin m, 2 * ((((partitionMesh P n) ⊓ 1).toReal) * lag i) := by
              exact Finset.sum_le_sum fun i _ ↦ hterm i
      _ = ∑ i : Fin m, (2 * ((partitionMesh P n) ⊓ 1).toReal) * lag i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = (2 * ((partitionMesh P n) ⊓ 1).toReal) * ∑ i : Fin m, lag i := by
            rw [← Finset.mul_sum]
      _ = 2 * ((partitionMesh P n) ⊓ 1).toReal := by
            rw [hlag_sum, mul_one]
  have hsum_fn : (fun ω ↦ ∑ i : Fin m, Z i ω) = ∑ i : Fin m, Z i := by
    funext ω
    simp [Finset.sum_apply]
  calc
    Var[fun ω ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1; μ] =
        Var[fun ω ↦ ∑ i : Fin m, Z i ω; μ] := by rw [hRowEq]
    _ = Var[∑ i : Fin m, Z i; μ] := by rw [hsum_fn]
    _ = ∑ i : Fin m, Var[Z i; μ] := hVarSum
    _ = ∑ i : Fin m, 2 * (lag i ^ (2 : ℕ)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hVarEntry i
    _ ≤ 2 * ((partitionMesh P n) ⊓ 1).toReal := hSumBound

/-- Helper for Theorem 21.64: the centered horizon-`1` quadratic partition sum is square
integrable. -/
-- TODO: rewrite the row as a finite sum of `L²` centered increments and close by induction on the
-- finite range.
lemma partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_memLp_two
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    MemLp (fun ω ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1) 2 μ := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  rw [partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_eq_sum_centeredSquares
    (μ := μ) (W := W) P n]
  have hSquares :
      MemLp
        (fun ω ↦
          ∑ k ∈ Finset.range (partitionBoundIndex P n 1),
            (W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ))
        2 μ := by
    -- Proof comment: each unclipped square term is the centered square plus its deterministic lag.
    have hRaw :
        MemLp
          (∑ i ∈ Finset.range (partitionBoundIndex P n 1), fun ω ↦
            (W (partitionNextPointUpTo P n i 1) ω - W (P n i) ω) ^ (2 : ℕ))
          2 μ :=
      (memLp_finset_sum'
        (s := Finset.range (partitionBoundIndex P n 1))
        (f := fun k ω ↦
          (W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ)) ?_)
    convert hRaw using 1
    ext ω
    simp
    intro k hk
    have hk_lt : k < partitionBoundIndex P n 1 := Finset.mem_range.mp hk
    have hst :
        P n k ≤ partitionNextPointUpTo P n k 1 :=
      partitionPoint_le_partitionNextPointUpTo_of_lt_partitionBoundIndex P n k hk_lt
    have hCentered :
        MemLp
          (fun ω ↦
            (W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ) -
              (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)))
          2 μ :=
      brownianIncrement_sq_sub_timeLag_memLp_two
        (μ := μ) (W := W) hW
        (s := P n k) (t := partitionNextPointUpTo P n k 1) hst
    have hSquare_eq :
        (fun ω ↦ (W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ)) =
          (fun ω ↦
            (W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ) -
              (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))) +
            fun _ : Ω ↦ (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)) := by
      funext ω
      change
        (W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ) =
          ((W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ) -
              (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))) +
            (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))
      ring
    change MemLp (fun ω ↦ (W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ)) 2 μ
    rw [hSquare_eq]
    exact
      hCentered.add
        (memLp_const (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)))
  have hConst :
      MemLp
        (fun _ : Ω ↦
          ∑ k ∈ Finset.range (partitionBoundIndex P n 1),
            (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)))
        2 μ :=
    memLp_const _
  -- Proof comment: the centered row is the raw square sum minus the deterministic compensator
  -- sum, so `L²` is stable under subtraction.
  simpa [Finset.sum_sub_distrib] using hSquares.sub hConst

/-- Helper for Theorem 21.64: the centered horizon-`1` quadratic partition sum has expectation
zero. -/
-- TODO: integrate the normalized centered row termwise once the row-rewrite lemma is restored.
lemma partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_integral_eq_zero
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    ∫ ω, (partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1) ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  rw [partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_eq_sum_centeredSquares
    (μ := μ) (W := W) P n]
  have hterm_int :
      ∀ k ∈ Finset.range (partitionBoundIndex P n 1),
        Integrable
          (fun ω ↦
            (W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω) ^ (2 : ℕ) -
              (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))) μ := by
    intro k hk
    have hk_lt : k < partitionBoundIndex P n 1 := Finset.mem_range.mp hk
    have hst :
        P n k ≤ partitionNextPointUpTo P n k 1 :=
      partitionPoint_le_partitionNextPointUpTo_of_lt_partitionBoundIndex P n k hk_lt
    exact
      (brownianIncrement_sq_sub_timeLag_memLp_two
        (μ := μ) (W := W) hW (s := P n k) (t := partitionNextPointUpTo P n k 1) hst).integrable
        (by norm_num)
  rw [integral_finset_sum _ hterm_int]
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hk_lt : k < partitionBoundIndex P n 1 := Finset.mem_range.mp hk
  have hst :
      P n k ≤ partitionNextPointUpTo P n k 1 :=
    partitionPoint_le_partitionNextPointUpTo_of_lt_partitionBoundIndex P n k hk_lt
  let inc : Ω → ℝ := fun ω ↦ W (partitionNextPointUpTo P n k 1) ω - W (P n k) ω
  have hInc_mem : MemLp inc 2 μ := by
    -- Proof comment: each clipped Brownian increment is square-integrable.
    simpa [inc] using
      brownianIncrement_memLp_two
        (μ := μ) (B := W) hW
        (s := P n k) (t := partitionNextPointUpTo P n k 1) hst
  -- Proof comment: each centered summand has mean zero because the raw second moment equals the
  -- deterministic time lag from Exercise 21.2.2.
  calc
    ∫ ω, (inc ω ^ (2 : ℕ) - (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ))) ∂μ
        = ∫ ω, inc ω ^ (2 : ℕ) ∂μ -
            ∫ ω, (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)) ∂μ := by
              rw [integral_sub hInc_mem.integrable_sq (integrable_const _)]
    _ = (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)) -
          (((partitionNextPointUpTo P n k 1 - P n k : NNReal) : ℝ)) := by
            rw [brownianIncrement_sq_integral_eq_timeLag
              (μ := μ) (B := W) hW (s := P n k) (t := partitionNextPointUpTo P n k 1) hst,
              integral_const, probReal_univ, one_smul]
    _ = 0 := by ring

/-- Helper for Theorem 21.64: at horizon `1`, the centered quadratic partition sums converge in
probability to `0`. -/
theorem tendstoInMeasure_partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_zero
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    TendstoInMeasure μ
      (fun n : ℕ ↦ fun ω ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1)
      atTop
      0 := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let X : ℕ → Ω → ℝ := fun n ω ↦
    partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1
  have hMean : ∀ n, μ[X n] = 0 := by
    intro n
    -- Proof comment: the centered horizon-`1` row was normalized so that each term has mean zero.
    simpa [X] using
      partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_integral_eq_zero
        (μ := μ) (W := W) hW P n
  have hMem : ∀ n, MemLp (X n) 2 μ := by
    intro n
    -- Proof comment: each centered row belongs to `L²`, which is the exact hypothesis needed
    -- for Chebyshev's variance bound.
    simpa [X] using
      partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_memLp_two
        (μ := μ) (W := W) hW P n
  have hVar :
      ∀ n, Var[X n; μ] ≤ 2 * ((partitionMesh P n) ⊓ 1).toReal := by
    intro n
    simpa [X] using
      partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_variance_le_two_mul_partitionMesh
        (μ := μ) (W := W) hW P n
  rw [MeasureTheory.tendstoInMeasure_iff_norm]
  intro ε hε
  have hBound :
      ∀ n,
        μ {ω | ε ≤ ‖X n ω - 0‖} ≤
          ENNReal.ofReal ((2 * ((partitionMesh P n) ⊓ 1).toReal) / ε ^ (2 : ℕ)) := by
    intro n
    have hEvent :
        {ω | ε ≤ ‖X n ω - 0‖} = {ω | ε ≤ |X n ω - μ[X n]|} := by
      ext ω
      simp [Real.norm_eq_abs, hMean n]
    rw [hEvent]
    calc
      μ {ω | ε ≤ |X n ω - μ[X n]|}
          ≤ ENNReal.ofReal (Var[X n; μ] / ε ^ (2 : ℕ)) := by
              exact ProbabilityTheory.meas_ge_le_variance_div_sq (hMem n) hε
      _ ≤ ENNReal.ofReal ((2 * ((partitionMesh P n) ⊓ 1).toReal) / ε ^ (2 : ℕ)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            exact div_le_div_of_nonneg_right (hVar n) (by positivity)
  have hMeshReal :
      Tendsto (fun n : ℕ ↦ (((partitionMesh P n) ⊓ 1).toReal)) atTop (nhds 0) := by
    -- Proof comment: clipping the mesh by `1` makes it finite, so `toReal` preserves the
    -- convergence of the mesh to `0`.
    have hMeshInf :
        Tendsto (fun n : ℕ ↦ (partitionMesh P n) ⊓ (1 : ENNReal)) atTop (𝓝 (0 : ENNReal)) := by
      exact
        tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds
          (IsAdmissiblePartitionSequence.mesh_tendsto_zero (P := P))
          (fun n ↦ by simp)
          (fun n ↦ inf_le_left)
    simpa using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hMeshInf
  have hBoundReal :
      Tendsto
        (fun n : ℕ ↦ (2 * (((partitionMesh P n) ⊓ 1).toReal)) / ε ^ (2 : ℕ))
        atTop
        (nhds 0) := by
    have hScaled :
        Tendsto
          (fun n : ℕ ↦ 2 * (((partitionMesh P n) ⊓ 1).toReal))
          atTop
          (nhds (2 * 0)) := by
      exact tendsto_const_nhds.mul hMeshReal
    simpa using hScaled.div_const (ε ^ (2 : ℕ))
  have hBoundENN :
      Tendsto
        (fun n : ℕ ↦ ENNReal.ofReal ((2 * (((partitionMesh P n) ⊓ 1).toReal)) / ε ^ (2 : ℕ)))
        atTop
        (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hBoundReal
  -- Proof comment: squeeze the tail probabilities between `0` and the deterministic Chebyshev
  -- bound coming from the variance estimate.
  simpa [X] using
    (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hBoundENN
      (fun n ↦ by exact zero_le _)
      hBound)

/-- Helper for Theorem 21.64: the omitted boundary square vanishes because predecessor points stay
within one mesh width of the target time and the path is continuous. -/
-- TODO: combine predecessor-point convergence with continuity of the path and square the vanishing
-- increment.
lemma boundarySquare_tendsto_zero
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) :
    Tendsto
      (fun n ↦ (X T - X (partitionPredecessorPointEarly P n T)) ^ 2)
      atTop
      (nhds 0) := by
  have hpoint :
      Tendsto (fun n ↦ partitionPredecessorPointEarly P n T) atTop (nhds T) := by
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (IsAdmissiblePartitionSequence.mesh_tendsto_zero (P := P))
      (fun n ↦ bot_le) ?_
    intro n
    simpa [edist_comm] using partitionPredecessorPointWithinMeshEarly P n T
  -- Proof comment: continuity of the path turns convergence of the predecessor points into the
  -- vanishing of the missing boundary square.
  have hcont : Continuous fun x : NNReal ↦ (X T - X x) ^ 2 :=
    (continuous_const.sub X.continuous).pow 2
  simpa using hcont.continuousAt.tendsto.comp hpoint

/-- Helper for Theorem 21.64: rational-time convergence of the full quadratic sums extends to all
times by monotonicity and continuity of the limiting path. -/
-- TODO: prove the left/right order convergence bounds using rational approximation and
-- monotonicity of the full quadratic sums.
lemma tendsto_allTimes_of_ratConvergence_fullSumsLocal
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {Aω : NNReal → ℝ} (hAcont : Continuous Aω)
    (hRat :
      ∀ q : ℚ≥0,
        Tendsto
          (fun n ↦ partitionSquareVariationFullSum X P (q : NNReal) n)
          atTop
          (nhds (Aω q))) :
    ∀ T : NNReal,
      Tendsto
        (fun n ↦ partitionSquareVariationFullSum X P T n)
        atTop
        (nhds (Aω T)) := by
  intro T
  by_cases hT0 : T = 0
  · -- Proof comment: the degenerate horizon `0` is already one of the rational-time limits.
    subst hT0
    simpa using hRat (0 : ℚ≥0)
  -- Route correction: instead of building a separate deterministic API, squeeze the monotone full
  -- sums between nearby rational horizons exactly as in the later all-times upgrade pattern.
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    by_cases ha_neg : a < 0
    · filter_upwards with n
      have hnonneg :
          0 ≤ partitionSquareVariationFullSum X P T n := by
        rw [partitionSquareVariationFullSum]
        refine Finset.sum_nonneg ?_
        intro k hk
        by_cases hle : P n (k + 1) ≤ T
        · simp [hle, sq_nonneg]
        · simp [hle]
      exact lt_of_lt_of_le ha_neg hnonneg
    · have hU : {t : NNReal | a < Aω t} ∈ 𝓝 T :=
        (hAcont.isOpen_preimage _ isOpen_Ioi).mem_nhds ha
      have hUleft : {t : NNReal | a < Aω t} ∈ 𝓝[<] T :=
        mem_nhdsWithin_of_mem_nhds hU
      have hTpos : (0 : NNReal) < T := pos_iff_ne_zero.mpr hT0
      rcases (mem_nhdsLT_iff_exists_Ioo_subset' hTpos).mp hUleft with ⟨l, hlT, hsubset⟩
      rcases (NNReal.lt_iff_exists_rat_btwn l T).mp hlT with ⟨q, hq0, hlq, hqT⟩
      let qNN : ℚ≥0 := ⟨q, hq0⟩
      have haq : a < Aω qNN := by
        exact hsubset ⟨by
          simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hlq, by
          simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hqT⟩
      have hqEventually :
          ∀ᶠ n : ℕ in atTop, a < partitionSquareVariationFullSum X P (qNN : NNReal) n :=
        ((tendsto_order.1 (hRat qNN)).1) a <| by
          simpa [qNN] using haq
      filter_upwards [hqEventually] with n hn
      exact lt_of_lt_of_le hn <|
        partitionSquareVariationFullSum_monotone X P n (le_of_lt <| by
          simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hqT)
  · intro b hb
    have hU : {t : NNReal | Aω t < b} ∈ 𝓝 T :=
      (hAcont.isOpen_preimage _ isOpen_Iio).mem_nhds hb
    have hUright : {t : NNReal | Aω t < b} ∈ 𝓝[>] T :=
      mem_nhdsWithin_of_mem_nhds hU
    have hTsucc : T < T + 1 := by
      simpa using lt_add_of_pos_right T (show (0 : NNReal) < 1 by norm_num)
    rcases (mem_nhdsGT_iff_exists_Ioo_subset' hTsucc).mp hUright with ⟨u, hTu, hsubset⟩
    rcases (NNReal.lt_iff_exists_rat_btwn T u).mp hTu with ⟨q, hq0, hTq, hqu⟩
    let qNN : ℚ≥0 := ⟨q, hq0⟩
    have hqb : Aω qNN < b := by
      exact hsubset ⟨by
        simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hTq, by
        simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hqu⟩
    have hqEventually :
        ∀ᶠ n : ℕ in atTop, partitionSquareVariationFullSum X P (qNN : NNReal) n < b :=
      ((tendsto_order.1 (hRat qNN)).2) b <| by
        simpa [qNN] using hqb
    filter_upwards [hqEventually] with n hn
    exact lt_of_le_of_lt
      (partitionSquareVariationFullSum_monotone X P n (le_of_lt <| by
        simpa [qNN, Real.toNNReal_of_nonneg (Rat.cast_nonneg.mpr hq0)] using hTq))
      hn

/-- Helper for Theorem 21.64: fixed-time convergence on nonnegative rational horizons upgrades to
every horizon by first passing to the full sums and then adding back the vanishing boundary term.
-/
-- TODO: first pass from clipped sums to full sums via the vanishing boundary square, then use the
-- deterministic rational-to-all-times extension.
lemma tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one_of_tendstoOnNNRat
    (X : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (hRat :
      ∀ q : ℚ≥0,
        Tendsto
          (fun n : ℕ ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) X P (q : NNReal) n)
          atTop
          (nhds (q : ℝ))) :
    ∀ T : NNReal,
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) X P T n)
        atTop
        (nhds (T : ℝ)) := by
  have hRatFull :
      ∀ q : ℚ≥0,
        Tendsto
          (fun n ↦ partitionSquareVariationFullSum X P (q : NNReal) n)
          atTop
          (𝓝 (q : ℝ)) := by
    intro q
    have hclip :
        Tendsto
          (fun n : ℕ ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) X P (q : NNReal) n)
          atTop
          (𝓝 (q : ℝ)) := hRat q
    have hdiff :
        Tendsto
          (fun n ↦
            weightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ)) X P (q : NNReal) n -
              partitionSquareVariationFullSum X P (q : NNReal) n)
          atTop
          (𝓝 0) := by
      -- Proof comment: the clipped/full-sum discrepancy is squeezed by the vanishing boundary
      -- square at the rational horizon.
      refine squeeze_zero ?_ ?_ (boundarySquare_tendsto_zero X P (q : NNReal))
      · intro n
        rw [weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum]
        exact (partitionSquareVariationSum_sub_fullSum_le_boundary X P (q : NNReal) n).1
      · intro n
        rw [weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum]
        exact (partitionSquareVariationSum_sub_fullSum_le_boundary X P (q : NNReal) n).2
    -- Proof comment: subtract the vanishing boundary discrepancy to recover rational full-sum
    -- convergence from the assumed clipped convergence.
    simpa [sub_eq_add_neg, sub_sub_cancel] using hclip.sub hdiff
  have hAllFull :
      ∀ T : NNReal,
        Tendsto
          (fun n ↦ partitionSquareVariationFullSum X P T n)
          atTop
          (𝓝 (T : ℝ)) :=
    tendsto_allTimes_of_ratConvergence_fullSumsLocal X P NNReal.continuous_coe hRatFull
  intro T
  have hdiffT :
      Tendsto
        (fun n ↦
          weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) X P T n -
            partitionSquareVariationFullSum X P T n)
        atTop
        (𝓝 0) := by
    -- Proof comment: the same boundary control works at the final horizon `T`.
    refine squeeze_zero ?_ ?_ (boundarySquare_tendsto_zero X P T)
    · intro n
      rw [weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum]
      exact (partitionSquareVariationSum_sub_fullSum_le_boundary X P T n).1
    · intro n
      rw [weightedPartitionQuadraticVariationApproximationUpTo_one_eq_partitionPVariationSum]
      exact (partitionSquareVariationSum_sub_fullSum_le_boundary X P T n).2
  have hEq :
      (fun n : ℕ ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (fun _ ↦ (1 : ℝ)) X P T n) =
        fun n ↦
          partitionSquareVariationFullSum X P T n +
            (weightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ)) X P T n -
              partitionSquareVariationFullSum X P T n) := by
    funext n
    ring
  -- Proof comment: add the vanishing boundary discrepancy back to the all-times full-sum limit
  -- to recover the original clipped quadratic partition sums.
  rw [hEq]
  simpa using (hAllFull T).add hdiffT

/-- Helper for Theorem 21.64: dividing every partition time by the positive factor `c`. -/
private noncomputable def dividedPartition
    (c : NNReal) (P : ℕ → ℕ → NNReal) : ℕ → ℕ → NNReal :=
  fun n k ↦ P n k / c

/-- Helper for Theorem 21.64: the mesh of the divided partition is bounded by the original mesh
divided by the same positive factor. -/
-- TODO: compare each divided row gap with the corresponding original gap after dividing by `c`.
private lemma partitionMesh_dividedPartition_le
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] {c : NNReal} (hc : 0 < c)
    (n : ℕ) :
    partitionMesh (dividedPartition c P) n ≤ partitionMesh P n / c := by
  -- Proof comment: each successor gap in the divided row is exactly the corresponding original
  -- gap divided by `c`, so the supremum mesh scales by the same factor.
  rw [partitionMesh, partitionMesh]
  refine iSup_le ?_
  intro k
  have hgap :
      edist (dividedPartition c P n k) (dividedPartition c P n (k + 1)) =
        edist (P n k) (P n (k + 1)) / c := by
    have hc' : (c : ℝ) ≠ 0 := by
      exact_mod_cast hc.ne'
    have hdiv :
        ((P n k : ℝ) / c - (P n (k + 1) : ℝ) / c) =
          (((P n k : ℝ) - (P n (k + 1) : ℝ)) / c) := by
      field_simp [hc']
    calc
      edist (dividedPartition c P n k) (dividedPartition c P n (k + 1))
          = ENNReal.ofReal |((P n k : ℝ) / c) - ((P n (k + 1) : ℝ) / c)| := by
              rw [dividedPartition, dividedPartition, edist_dist, NNReal.dist_eq, NNReal.coe_div,
                NNReal.coe_div]
      _ = ENNReal.ofReal (|((P n k : ℝ) - (P n (k + 1) : ℝ))| / c) := by
            rw [hdiv, abs_div, abs_of_pos (show (0 : ℝ) < c from hc)]
      _ = ENNReal.ofReal |(P n k : ℝ) - (P n (k + 1) : ℝ)| / c := by
            rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < c from hc), ENNReal.ofReal_coe_nnreal]
      _ = edist (P n k) (P n (k + 1)) / c := by
            rw [edist_dist, NNReal.dist_eq]
  rw [hgap]
  exact ENNReal.div_le_div_right (le_iSup (fun j ↦ edist (P n j) (P n (j + 1))) k) c

/-- Helper for Theorem 21.64: dividing an admissible partition sequence by a positive constant
preserves admissibility. -/
-- TODO: transport each axiom of admissibility through the division map `t ↦ t / c`.
private lemma isAdmissiblePartitionSequence_dividedPartition
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] {c : NNReal} (hc : 0 < c) :
    IsAdmissiblePartitionSequence (dividedPartition c P) := by
  refine
    { zero_eq := ?_
      strictMono := ?_
      nested := ?_
      tendsto_atTop := ?_
      mesh_tendsto_zero := ?_ }
  · intro n
    -- Proof comment: dividing the initial partition point `0` by `c` keeps it at `0`.
    simp [dividedPartition, IsAdmissiblePartitionSequence.zero_eq (P := P) n]
  · intro n i j hij
    -- Proof comment: positive division is strictly monotone on `NNReal`, so each row remains
    -- strictly increasing after scaling.
    have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_lt_mul_of_pos_right ((IsAdmissiblePartitionSequence.strictMono (P := P) n) hij) hcinv
  · intro n x hx
    -- Proof comment: refinement is preserved because every divided partition point comes from an
    -- original partition point, which already appears in the next row.
    rcases hx with ⟨k, rfl⟩
    rcases IsAdmissiblePartitionSequence.nested (P := P) n ⟨k, rfl⟩ with ⟨j, hj⟩
    exact ⟨j, by simp [partitionPointSet, dividedPartition, hj]⟩
  · intro n
    -- Proof comment: dividing a sequence tending to `∞` by a fixed positive constant still tends
    -- to `∞`.
    simpa [dividedPartition] using
      (IsAdmissiblePartitionSequence.tendsto_atTop (P := P) n).atTop_div_const hc
  · -- Proof comment: the divided meshes are squeezed between `0` and the original meshes scaled
    -- by `1 / c`, and the latter still tends to `0`.
    let d : ENNReal := c
    have hd : d ≠ 0 := by
      simpa [d] using (show (c : ENNReal) ≠ 0 by exact_mod_cast hc.ne')
    have hmesh_div :
        Tendsto (fun n : ℕ ↦ partitionMesh P n / d) atTop (𝓝 ((0 : ENNReal) / d)) := by
      exact ENNReal.Tendsto.div_const
        (IsAdmissiblePartitionSequence.mesh_tendsto_zero (P := P))
        (Or.inr hd)
    have hupper : Tendsto (fun n : ℕ ↦ partitionMesh P n / d) atTop (𝓝 0) := by
      simpa [d] using hmesh_div
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        (f := fun n : ℕ ↦ partitionMesh (dividedPartition c P) n)
        (g := fun _ : ℕ ↦ (0 : ENNReal))
        (h := fun n : ℕ ↦ partitionMesh P n / d)
        tendsto_const_nhds
        hupper
        (fun n ↦ bot_le)
        (fun n ↦ by simpa [d] using partitionMesh_dividedPartition_le P hc n)

/-- Helper for Theorem 21.64: choosing the Brownian scaling factor `√T` makes the time-change
equal to `T`. -/
private lemma brownianScalingTime_sqrtNNReal (T : NNReal) :
    ProbabilityTheory.brownianScalingTime (Real.sqrt (T : ℝ)) = T := by
  -- Proof comment: `brownianScalingTime` is just the squared scaling factor viewed in `NNReal`.
  ext
  simp [ProbabilityTheory.brownianScalingTime, Real.sq_sqrt]

/-- Helper for Theorem 21.64: dividing the partition row by `q` makes the horizon `1` truncation
index coincide with the original horizon `q` truncation index. -/
private lemma partitionBoundIndex_dividedPartition_one
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] {q : NNReal}
    [IsAdmissiblePartitionSequence (dividedPartition q P)] (hq : 0 < q)
    (n : ℕ) :
    partitionBoundIndex (dividedPartition q P) n 1 = partitionBoundIndex P n q := by
  -- Proof comment: crossing the level `1` in the divided row is exactly the same inequality as
  -- crossing the level `q` in the original row.
  apply Nat.le_antisymm
  · refine Nat.find_min' (exists_partition_index_le_time (dividedPartition q P) n 1) ?_
    rw [dividedPartition]
    exact (one_le_div hq).2 (le_partitionBoundIndex_time P n q)
  · refine Nat.find_min' (exists_partition_index_le_time P n q) ?_
    have hdiv :
        (1 : NNReal) ≤
          dividedPartition q P n (partitionBoundIndex (dividedPartition q P) n 1) := by
      exact le_partitionBoundIndex_time (dividedPartition q P) n 1
    rw [dividedPartition] at hdiv
    exact (one_le_div hq).1 hdiv

/-- Helper for Theorem 21.64: multiplying a divided partition point by the scale factor recovers
the original partition point. -/
private lemma partitionPoint_dividedPartition_mul
    (P : ℕ → ℕ → NNReal) {q : NNReal} (hq : 0 < q) (n k : ℕ) :
    q * dividedPartition q P n k = P n k := by
  -- Proof comment: the divided row was defined by division by `q`, so multiplying back by the
  -- positive scale factor restores the original point.
  rw [dividedPartition, mul_comm, div_mul_cancel₀ _ hq.ne']

/-- Helper for Theorem 21.64: multiplying the horizon-`1` clipped successor of the divided
partition by `q` recovers the horizon-`q` clipped successor of the original partition. -/
private lemma partitionNextPointUpTo_dividedPartition_one_mul
    (P : ℕ → ℕ → NNReal) {q : NNReal} (hq : 0 < q) (n k : ℕ) :
    q * partitionNextPointUpTo (dividedPartition q P) n k 1 =
      partitionNextPointUpTo P n k q := by
  -- Proof comment: compare whether the original successor already lies before `q`; in each case
  -- the clipping is explicit and multiplication by `q` cancels the division.
  rw [partitionNextPointUpTo, partitionNextPointUpTo]
  by_cases h : P n (k + 1) ≤ q
  · have hdiv : dividedPartition q P n (k + 1) ≤ 1 := by
      rw [dividedPartition]
      exact (div_le_one hq).2 h
    rw [min_eq_left hdiv, min_eq_left h]
    exact partitionPoint_dividedPartition_mul P hq n (k + 1)
  · have hq_le : q ≤ P n (k + 1) := le_of_not_ge h
    have hdiv : 1 ≤ dividedPartition q P n (k + 1) := by
      rw [dividedPartition]
      exact (one_le_div hq).2 hq_le
    rw [min_eq_right hdiv, min_eq_right hq_le]
    simp

/-- Helper for Theorem 21.64: Brownian scaling rewrites the horizon-`q` quadratic partition sum
of `W` as `q` times the horizon-`1` sum of the scaled Brownian motion along the divided partition.
-/
private lemma partitionQuadraticVariationApproximationUpToRandomVariable_nnrat_eq_brownianScaling
    {W : NNReal → Ω → ℝ}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] {q : ℚ≥0}
    [IsAdmissiblePartitionSequence (dividedPartition (q : NNReal) P)] (hq : q ≠ 0) (n : ℕ) :
    partitionQuadraticVariationApproximationUpToRandomVariable W P (q : NNReal) n =
      fun ω ↦
        (q : ℝ) *
          partitionQuadraticVariationApproximationUpToRandomVariable
            (brownianScaling W (Real.sqrt (q : ℝ)))
            (dividedPartition (q : NNReal) P) 1 n ω := by
  have hqNN_ne : (q : NNReal) ≠ 0 := by
    exact_mod_cast hq
  have hqNN : 0 < (q : NNReal) := pos_iff_ne_zero.mpr hqNN_ne
  have hq_nonneg : 0 ≤ (q : ℝ) := by
    exact_mod_cast q.2
  have hq_pos : 0 < (q : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hq : (0 : ℚ≥0) < q)
  have hsqrt_ne : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hq_pos
  have hcoeff : (q : ℝ) * (Real.sqrt (q : ℝ))⁻¹ ^ (2 : ℕ) = 1 := by
    have hpow : (Real.sqrt (q : ℝ)) ^ (2 : ℕ) = (q : ℝ) := by
      simpa [pow_two] using Real.sq_sqrt hq_nonneg
    have hsq_inv : (Real.sqrt (q : ℝ))⁻¹ ^ (2 : ℕ) = (q : ℝ)⁻¹ := by
      rw [inv_pow, hpow]
    calc
      (q : ℝ) * (Real.sqrt (q : ℝ))⁻¹ ^ (2 : ℕ)
          = (q : ℝ) * (q : ℝ)⁻¹ := by
              rw [hsq_inv]
      _ = 1 := by
            field_simp [show (q : ℝ) ≠ 0 by exact ne_of_gt hq_pos]
  have hTimeScale : brownianScalingTime (Real.sqrt (q : ℝ)) = (q : NNReal) := by
    ext
    simp [ProbabilityTheory.brownianScalingTime, Real.sq_sqrt, hq_nonneg]
    rfl
  funext ω
  -- Proof comment: first align the truncation ranges, then rewrite the time-changed scaled
  -- process back to the original partition times.
  simp [partitionQuadraticVariationApproximationUpToRandomVariable_def,
    weightedPartitionQuadraticVariationApproximationUpTo_def]
  rw [partitionBoundIndex_dividedPartition_one P hqNN n, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hScaledNext :
      (Real.sqrt (q : ℝ))⁻¹ *
          W (brownianScalingTime (Real.sqrt (q : ℝ)) *
            partitionNextPointUpTo (dividedPartition (q : NNReal) P) n k 1) ω =
        (Real.sqrt (q : ℝ))⁻¹ * W (partitionNextPointUpTo P n k (q : NNReal)) ω := by
    rw [hTimeScale, partitionNextPointUpTo_dividedPartition_one_mul P hqNN n k]
  have hScaledPoint :
      (Real.sqrt (q : ℝ))⁻¹ *
          W (brownianScalingTime (Real.sqrt (q : ℝ)) * dividedPartition (q : NNReal) P n k) ω =
        (Real.sqrt (q : ℝ))⁻¹ * W (P n k) ω := by
    rw [hTimeScale, partitionPoint_dividedPartition_mul P hqNN n k]
  rw [hScaledNext, hScaledPoint]
  have hdiff :
      (Real.sqrt (q : ℝ))⁻¹ * W (partitionNextPointUpTo P n k (q : NNReal)) ω -
          (Real.sqrt (q : ℝ))⁻¹ * W (P n k) ω =
        (Real.sqrt (q : ℝ))⁻¹ *
          (W (partitionNextPointUpTo P n k (q : NNReal)) ω - W (P n k) ω) := by
    ring
  rw [hdiff, mul_pow]
  symm
  calc
    (q : ℝ) *
        ((Real.sqrt (q : ℝ))⁻¹ ^ (2 : ℕ) *
          (W (partitionNextPointUpTo P n k (q : NNReal)) ω - W (P n k) ω) ^ (2 : ℕ))
        = ((q : ℝ) * (Real.sqrt (q : ℝ))⁻¹ ^ (2 : ℕ)) *
            (W (partitionNextPointUpTo P n k (q : NNReal)) ω - W (P n k) ω) ^ (2 : ℕ) := by
              ring
    _ = (W (partitionNextPointUpTo P n k (q : NNReal)) ω - W (P n k) ω) ^ (2 : ℕ) := by
          rw [hcoeff, one_mul]

namespace IsBrownianMotion

/-- Helper for Theorem 21.64: almost every Brownian sample path is continuous on `NNReal`. -/
theorem ae_continuous_path
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W) :
    ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω) := by
  -- Proof comment: this is exactly the continuity field already stored in `IsBrownianMotion`.
  simpa [HasAlmostSurelyContinuousPaths, processPath] using hW.continuous_paths

/-- Helper for Theorem 21.64: the centered horizon-`1` quadratic partition sums admit an almost-
surely convergent strict-mono subsequence. -/
theorem ae_tendsto_partitionQuadraticVariationApproximationUpToRandomVariable_one_subseq
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∀ᵐ ω ∂μ,
          Tendsto
            (fun n : ℕ ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 (φ n) ω)
            atTop
            (nhds 1) := by
  obtain ⟨φ, hφ, hφae⟩ :=
    MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae
      (tendstoInMeasure_partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_zero
        (μ := μ) (W := W) hW P)
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hφae] with ω hω
  -- Proof comment: add back the deterministic compensator `1` after extracting the almost-surely
  -- convergent subsequence of the centered row.
  have hAdd :
      Tendsto
        (fun n : ℕ ↦
          (partitionQuadraticVariationApproximationUpToRandomVariable W P 1 (φ n) ω - 1) + 1)
        atTop
        (nhds (0 + 1)) :=
    hω.add tendsto_const_nhds
  simpa [sub_eq_add_neg, add_assoc] using hAdd

/-- Helper for Theorem 21.64: the centered horizon-`1` row is exactly the backward process from
Exercise 21.10.1 evaluated at the corresponding reverse-time index. -/
private lemma partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_eq_backwardProcess
    {μ : Measure Ω} {W : NNReal → Ω → ℝ}
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (n : ℕ) :
    (fun ω ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1) =
      exercise21101BackwardProcess W P (toDual n) := by
  -- Proof comment: both sides are the same centered finite sum of clipped squared increments.
  funext ω
  rw [exercise21101BackwardProcess]
  simpa using
    congrFun
      (partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_eq_sum_centeredSquares
        (μ := μ) (W := W) P n)
      ω

/-- Helper for Theorem 21.64: at horizon `1`, the quadratic partition sums converge almost surely
to `1` along the full partition sequence. -/
theorem ae_tendsto_partitionQuadraticVariationApproximationUpToRandomVariable_one
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω)
        atTop
        (nhds 1) := by
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  let ℱ : Filtration ℕᵒᵈ mΩ :=
    Filtration.natural
      (exercise21101BackwardProcess W P)
      (exercise21101BackwardProcess_stronglyMeasurable W hW.stronglyMeasurable P)
  let L : Ω → ℝ := fun ω ↦
    μ[exercise21101BackwardProcess W P 0 | tailMeasurableSpace (ℱ ∘ toDual)] ω
  have hBackward_ae :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n ↦ exercise21101BackwardProcess W P (toDual n) ω) atTop (𝓝 (L ω)) := by
    -- Proof comment: the centered horizon-`1` row is a backward martingale, so it converges
    -- almost surely to its tail conditional expectation.
    simpa [ℱ, L] using
      backward_martingale_ae_tendsto_limit
        (μ := μ)
        (X := exercise21101BackwardProcess W P)
        (ℱ := ℱ)
        (hW.partitionQuadraticVariationApproximationUpTo_one_backwardsMartingale P)
  have hBackward_meas :
      ∀ n, AEStronglyMeasurable (fun ω ↦ exercise21101BackwardProcess W P (toDual n) ω) μ := by
    intro n
    exact
      (exercise21101BackwardProcess_stronglyMeasurable
        W hW.stronglyMeasurable P (toDual n)).aestronglyMeasurable
  have hBackward_measure :
      TendstoInMeasure μ
        (fun n ↦ exercise21101BackwardProcess W P (toDual n))
        atTop
        L :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae hBackward_meas hBackward_ae
  have hCentered_measure :
      TendstoInMeasure μ
        (fun n ↦ exercise21101BackwardProcess W P (toDual n))
        atTop
        0 := by
    -- Proof comment: rewrite the already controlled centered quadratic sums into the backward
    -- process spelling before invoking uniqueness of convergence in measure.
    refine
      (tendstoInMeasure_partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_zero
        (μ := μ) (W := W) hW P).congr_left ?_
    intro n
    filter_upwards with ω
    simpa using
      congrFun
        (partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_eq_backwardProcess
          (μ := μ) (W := W) P n)
        ω
  have hLimit_zero : L =ᵐ[μ] (0 : Ω → ℝ) :=
    MeasureTheory.tendstoInMeasure_ae_unique hBackward_measure hCentered_measure
  filter_upwards [hBackward_ae, hLimit_zero] with ω hω hLω
  have hCentered_ae :
      Tendsto
        (fun n : ℕ ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1)
        atTop
        (nhds 0) := by
    have hProcess_zero :
        Tendsto (fun n ↦ exercise21101BackwardProcess W P (toDual n) ω) atTop (𝓝 0) := by
      simpa [hLω] using hω
    have hRowEq :
        (fun n : ℕ ↦ partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1) =
          fun n ↦ exercise21101BackwardProcess W P (toDual n) ω := by
      funext n
      simpa using
        congrFun
          (partitionQuadraticVariationApproximationUpToRandomVariable_one_sub_one_eq_backwardProcess
            (μ := μ) (W := W) P n)
          ω
    simpa [hRowEq] using hProcess_zero
  -- Proof comment: once the centered row tends to `0`, adding back the deterministic compensator
  -- `1` gives the desired almost-sure limit of the raw quadratic sums.
  have hAdd :
      Tendsto
        (fun n : ℕ ↦
          (partitionQuadraticVariationApproximationUpToRandomVariable W P 1 n ω - 1) + 1)
        atTop
        (nhds (0 + 1)) :=
    hCentered_ae.add tendsto_const_nhds
  simpa [sub_eq_add_neg, add_assoc] using hAdd

/-- Helper for Theorem 21.64: at every nonnegative rational horizon, the quadratic partition sums
converge almost surely to the rational time value. -/
theorem ae_tendsto_partitionQuadraticVariationApproximationUpTo_nnrat
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∀ᵐ ω ∂μ, ∀ q : ℚ≥0,
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (fun t ↦ W t ω) P (q : NNReal) n)
        atTop
        (nhds (q : ℝ)) := by
  rw [ae_all_iff]
  intro q
  by_cases hq : q = 0
  · subst hq
    filter_upwards with ω
    -- Proof comment: at the degenerate horizon `0`, the truncated partition range is empty, so
    -- the quadratic sums are identically zero.
    simpa [weightedPartitionQuadraticVariationApproximationUpTo_def, partitionBoundIndex_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · have hqNN_ne : (q : NNReal) ≠ 0 := by
      exact_mod_cast hq
    have hqNN : 0 < (q : NNReal) := pos_iff_ne_zero.mpr hqNN_ne
    letI : IsAdmissiblePartitionSequence (dividedPartition (q : NNReal) P) :=
      isAdmissiblePartitionSequence_dividedPartition P hqNN
    have hq_pos : 0 < (q : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hq : (0 : ℚ≥0) < q)
    have hsqrt_ne : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hq_pos
    have hScaled :
        IsBrownianMotion μ (brownianScaling W (Real.sqrt (q : ℝ))) :=
      hW.scaling hsqrt_ne
    have hScaled_ae :
        ∀ᵐ ω ∂μ,
          Tendsto
            (fun n : ℕ ↦
              partitionQuadraticVariationApproximationUpToRandomVariable
                (brownianScaling W (Real.sqrt (q : ℝ)))
                (dividedPartition (q : NNReal) P) 1 n ω)
            atTop
            (nhds 1) :=
      ae_tendsto_partitionQuadraticVariationApproximationUpToRandomVariable_one
        (μ := μ)
        (W := brownianScaling W (Real.sqrt (q : ℝ)))
        hScaled
        (dividedPartition (q : NNReal) P)
    filter_upwards [hScaled_ae] with ω hω
    have hScaleEq :
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (fun t ↦ W t ω) P (q : NNReal) n) =
          fun n ↦
            (q : ℝ) *
              partitionQuadraticVariationApproximationUpToRandomVariable
                (brownianScaling W (Real.sqrt (q : ℝ)))
                (dividedPartition (q : NNReal) P) 1 n ω := by
      funext n
      simpa [partitionQuadraticVariationApproximationUpToRandomVariable_def] using
        congrFun
          (partitionQuadraticVariationApproximationUpToRandomVariable_nnrat_eq_brownianScaling
            (W := W) P hq n)
          ω
    -- Proof comment: multiply the horizon-`1` almost-sure limit for the scaled Brownian motion
    -- by the deterministic factor `q` to recover the original horizon.
    have hMul :
        Tendsto
          (fun n ↦
            (q : ℝ) *
              partitionQuadraticVariationApproximationUpToRandomVariable
                (brownianScaling W (Real.sqrt (q : ℝ)))
                (dividedPartition (q : NNReal) P) 1 n ω)
          atTop
          (nhds ((q : ℝ) * 1)) :=
      tendsto_const_nhds.mul hω
    rw [hScaleEq]
    simpa using hMul

-- Proof sketch: first solve the probabilistic rational-time owner, then use the deterministic
-- full-sum rational-sandwich lemma to pass to every horizon.
/-- Helper for Theorem 21.64: the Brownian quadratic partition sums converge almost surely to the
identity path simultaneously for all horizons. -/
theorem ae_tendsto_partitionQuadraticVariationApproximationUpTo_core
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∀ᵐ ω ∂μ, ∀ T : NNReal,
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (fun t ↦ W t ω) P T n)
        atTop
        (nhds (T : ℝ)) := by
  have hRat :
      ∀ᵐ ω ∂μ, ∀ q : ℚ≥0,
        Tendsto
          (fun n : ℕ ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) (fun t ↦ W t ω) P (q : NNReal) n)
          atTop
          (nhds (q : ℝ)) :=
    ae_tendsto_partitionQuadraticVariationApproximationUpTo_nnrat (μ := μ) (W := W) hW P
  have hCont :
      ∀ᵐ ω ∂μ, Continuous (fun t : NNReal ↦ W t ω) :=
    ae_continuous_path (μ := μ) (W := W) hW
  filter_upwards [hRat, hCont] with ω hRatω hContω
  let Xω : PathSpace := ⟨fun t : NNReal ↦ W t ω, hContω⟩
  have hRatX :
      ∀ q : ℚ≥0,
        Tendsto
          (fun n : ℕ ↦
            weightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ)) Xω P (q : NNReal) n)
          atTop
          (nhds (q : ℝ)) := by
    intro q
    simpa [Xω] using hRatω q
  -- Proof comment: once a sample path is continuous and the rational-time limits are known, the
  -- deterministic extension lemma upgrades them to every horizon simultaneously.
  intro T
  simpa [Xω] using
    tendsto_weightedPartitionQuadraticVariationApproximationUpTo_one_of_tendstoOnNNRat
      Xω P hRatX T

-- Proof sketch: the displayed theorem is exactly the isolated probabilistic core statement for
-- this item.
/-- Theorem 21.64: for Brownian motion `W` and every admissible sequence of partitions `P`, the
quadratic partition sums along `P` converge almost surely to `T` simultaneously for all
`T ≥ 0`; equivalently, the quadratic variation satisfies `⟨W⟩_T = T`. -/
-- TODO: this final wrapper should be a direct application of the theorem-local core result once
-- the probabilistic and deterministic helper lemmas above are restored.
theorem ae_tendsto_partitionQuadraticVariationApproximationUpTo
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    ∀ᵐ ω ∂μ, ∀ T : NNReal,
      Tendsto
        (fun n : ℕ ↦
          weightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ)) (fun t ↦ W t ω) P T n)
        atTop
        (nhds (T : ℝ)) := by
  -- Proof comment: the displayed theorem is exactly the already-isolated core almost-sure
  -- convergence statement for this item.
  exact ae_tendsto_partitionQuadraticVariationApproximationUpTo_core hW P

end IsBrownianMotion

end ProbabilityTheory

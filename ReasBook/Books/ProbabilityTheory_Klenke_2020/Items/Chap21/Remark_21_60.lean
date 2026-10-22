/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators ENNReal Topology

noncomputable section

open Set

local notation "dyadicPartitionSequence" => Definition2158.dyadicPartitionSequence

/-- Helper for Remark 21.60: the dyadic row of level `n`, clipped at the terminal time `T`. -/
def truncatedDyadicPoint (T : NNReal) (n k : ℕ) : NNReal :=
  min T (dyadicPartitionSequence n k)

/-- Helper for Remark 21.60: clipping is compatible with passing from a dyadic point to the same
point viewed in the next refined row. -/
lemma truncatedDyadicPoint_refine_even (T : NNReal) (n k : ℕ) :
    truncatedDyadicPoint T n k = truncatedDyadicPoint T (n + 1) (2 * k) := by
  rw [truncatedDyadicPoint, truncatedDyadicPoint]
  congr 1
  rw [Definition2158.dyadicPartitionSequence, Definition2158.dyadicPartitionSequence, pow_succ,
    Nat.cast_mul, Nat.cast_ofNat]
  ring_nf

/-- Helper for Remark 21.60: once the dyadic index has crossed the truncation threshold, the
clipped dyadic row stays at the terminal time `T`. -/
lemma truncatedDyadicPoint_eq_time_of_le_ceil
    (T : NNReal) (n k : ℕ) (hk : Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) ≤ k) :
    truncatedDyadicPoint T n k = T := by
  apply min_eq_left
  have hk_real : ((Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hceil : (T : ℝ) * (2 : ℝ) ^ n ≤ (k : ℝ) := by
    exact le_trans (Nat.le_ceil ((T : ℝ) * (2 : ℝ) ^ n)) hk_real
  rw [Definition2158.dyadicPartitionSequence]
  have hpow : 0 < (2 : ℝ) ^ n := by
    positivity
  have hk' : (T : ℝ) ≤ (k : ℝ) / (2 : ℝ) ^ n := by
    exact (le_div_iff₀ hpow).2 hceil
  exact_mod_cast hk'

/-- Helper for Remark 21.60: the clipped dyadic row is monotone in the mesh index. -/
lemma truncatedDyadicPoint_monotone (T : NNReal) (n : ℕ) :
    Monotone (truncatedDyadicPoint T n) := by
  intro a b hab
  exact min_le_min le_rfl <| by
    rw [Definition2158.dyadicPartitionSequence, Definition2158.dyadicPartitionSequence]
    exact
      (div_le_div_iff_of_pos_right (show 0 < (2 : NNReal) ^ n by positivity)).2 <| by
        exact_mod_cast hab

/-- Helper for Remark 21.60: every clipped dyadic point lies in the interval `Set.Icc 0 T`. -/
lemma truncatedDyadicPoint_mem_Icc (T : NNReal) (n k : ℕ) :
    truncatedDyadicPoint T n k ∈ Set.Icc 0 T := by
  constructor
  · exact bot_le
  · exact min_le_left _ _

/-- Helper for Remark 21.60: the refined dyadic truncation index is bounded by twice the coarse
truncation index. -/
lemma dyadicRefinedBound_le_double (T : NNReal) (n : ℕ) :
    Nat.ceil ((T : ℝ) * (2 : ℝ) ^ (n + 1)) ≤ 2 * Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) := by
  have hsplit :
      (T : ℝ) * (2 : ℝ) ^ (n + 1) =
        ((T : ℝ) * (2 : ℝ) ^ n) + ((T : ℝ) * (2 : ℝ) ^ n) := by
    rw [pow_succ]
    ring
  rw [hsplit]
  simpa [two_mul] using Nat.ceil_add_le ((T : ℝ) * (2 : ℝ) ^ n) ((T : ℝ) * (2 : ℝ) ^ n)

/-- Helper for Remark 21.60: pairing the even and odd summands of a sequence recovers the sum
over the doubled initial range. -/
lemma sum_pairs_eq_sum_range_double (f : ℕ → ℝ≥0∞) :
    ∀ m : ℕ, Finset.sum (Finset.range m) (fun k ↦ f (2 * k) + f (2 * k + 1)) =
      Finset.sum (Finset.range (2 * m)) f
  | 0 => by
      simp
  | m + 1 => by
      -- Proof comment: append the new even/odd pair and split the doubled range at its last two
      -- indices.
      rw [Finset.sum_range_succ, sum_pairs_eq_sum_range_double f m]
      have hsplit : 2 * (m + 1) = 2 * m + 1 + 1 := by
        ring
      rw [hsplit, Finset.sum_range_succ, Finset.sum_range_succ]
      ring

/-- Helper for Remark 21.60: a sum over a longer initial range agrees with the shorter one when
all tail terms vanish. -/
lemma sum_range_eq_of_tail_zero (f : ℕ → ℝ≥0∞) {m n : ℕ} (hmn : m ≤ n)
    (hzero : ∀ k, m ≤ k → f k = 0) :
    Finset.sum (Finset.range n) f = Finset.sum (Finset.range m) f := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Finset.sum_range_add]
  have htail : Finset.sum (Finset.range l) (fun x ↦ f (m + x)) = 0 := by
    -- Proof comment: after the truncation index both clipped dyadic endpoints equal `T`, so the
    -- remaining increments vanish.
    refine Finset.sum_eq_zero ?_
    intro x hx
    exact hzero (m + x) (Nat.le_add_right m x)
  rw [htail, add_zero]

/-- Helper for Remark 21.60: a clipped dyadic increment is the corresponding `edist` increment in
the target metric space `ℝ`. -/
lemma truncatedDyadicIncrement_eq_edist
    (G : C(NNReal, ℝ)) (T : NNReal) (n k : ℕ) :
    ENNReal.ofReal
        |G (truncatedDyadicPoint T n (k + 1)) - G (truncatedDyadicPoint T n k)| =
      edist (G (truncatedDyadicPoint T n (k + 1))) (G (truncatedDyadicPoint T n k)) := by
  rw [edist_dist, Real.dist_eq]

/-- Helper for Remark 21.60: a coarse clipped dyadic increment is bounded by the sum of the two
corresponding refined increments. -/
lemma coarseDyadicIncrement_le_refinedPair
    (G : C(NNReal, ℝ)) (T : NNReal) (n k : ℕ) :
    ENNReal.ofReal
        |G (truncatedDyadicPoint T n (k + 1)) - G (truncatedDyadicPoint T n k)| ≤
      ENNReal.ofReal
          |G (truncatedDyadicPoint T (n + 1) (2 * k + 1)) -
            G (truncatedDyadicPoint T (n + 1) (2 * k))| +
        ENNReal.ofReal
          |G (truncatedDyadicPoint T (n + 1) (2 * k + 2)) -
            G (truncatedDyadicPoint T (n + 1) (2 * k + 1))| := by
  -- Proof comment: identify the coarse endpoints with the even refined endpoints and then apply
  -- the triangle inequality with the odd refined midpoint.
  have hleft :
      truncatedDyadicPoint T n k = truncatedDyadicPoint T (n + 1) (2 * k) :=
    truncatedDyadicPoint_refine_even T n k
  have hright :
      truncatedDyadicPoint T n (k + 1) = truncatedDyadicPoint T (n + 1) (2 * k + 2) := by
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using
      truncatedDyadicPoint_refine_even T n (k + 1)
  rw [truncatedDyadicIncrement_eq_edist, truncatedDyadicIncrement_eq_edist,
    truncatedDyadicIncrement_eq_edist]
  rw [hleft, hright]
  simpa [two_mul, add_assoc, add_left_comm, add_comm] using
    edist_triangle (G (truncatedDyadicPoint T (n + 1) (2 * k + 2)))
      (G (truncatedDyadicPoint T (n + 1) (2 * k + 1)))
      (G (truncatedDyadicPoint T (n + 1) (2 * k)))

/-- The dyadic first-variation approximation on `[0, T]`, obtained by summing the absolute
increments of `G` along the truncated dyadic mesh of order `n`. -/
def dyadicVariationSumUpTo (G : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) : ℝ≥0∞ :=
  Finset.sum (Finset.range (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n))) fun k ↦
    ENNReal.ofReal
      |G (min T (((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n)) -
        G (min T ((k : NNReal) / (2 : NNReal) ^ n))|

/-- Helper for Remark 21.60: every clipped dyadic first-variation sum is bounded above by the
total variation on `Set.Icc 0 T`. -/
lemma dyadicVariationSumUpTo_le_eVariationOn_Icc
    (G : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) :
    dyadicVariationSumUpTo G T n ≤ eVariationOn G (Set.Icc 0 T) := by
  let point : ℕ → NNReal := truncatedDyadicPoint T n
  let m : ℕ := Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n)
  have hpoint_mono : Monotone point := truncatedDyadicPoint_monotone T n
  have hpoint_mem : ∀ i, point i ∈ Set.Icc 0 T := fun i ↦ truncatedDyadicPoint_mem_Icc T n i
  -- Proof comment: the clipped dyadic row is an admissible monotone parameterization of points in
  -- `Set.Icc 0 T`, so its increment sum is controlled by `eVariationOn.sum_le`.
  simpa [dyadicVariationSumUpTo, point, m, truncatedDyadicPoint,
    Definition2158.dyadicPartitionSequence, edist_dist, Real.dist_eq] using
    (eVariationOn.sum_le (f := G) (s := Set.Icc 0 T) (n := m) (u := point) hpoint_mono hpoint_mem)

-- Proof sketch: each interval of the order-`n` truncated dyadic partition is split into two
-- consecutive subintervals at level `n + 1`; apply the triangle inequality to the corresponding
-- increment of `G` and sum over all coarse intervals.
/-- Refining the truncated dyadic partition can only increase the first-variation sum. -/
theorem dyadicVariationSumUpTo_monotone (G : C(NNReal, ℝ)) (T : NNReal) :
    Monotone (dyadicVariationSumUpTo G T) := by
  refine monotone_nat_of_le_succ ?_
  intro n
  let coarseBound : ℕ := Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n)
  let refinedBound : ℕ := Nat.ceil ((T : ℝ) * (2 : ℝ) ^ (n + 1))
  let refinedTerm : ℕ → ℝ≥0∞ := fun j ↦
    ENNReal.ofReal
      |G (truncatedDyadicPoint T (n + 1) (j + 1)) - G (truncatedDyadicPoint T (n + 1) j)|
  have hpointwise :
      ∀ k ∈ Finset.range coarseBound,
        ENNReal.ofReal
            |G (truncatedDyadicPoint T n (k + 1)) - G (truncatedDyadicPoint T n k)| ≤
          refinedTerm (2 * k) + refinedTerm (2 * k + 1) := by
    intro k hk
    simpa [refinedTerm] using coarseDyadicIncrement_le_refinedPair G T n k
  have htail_zero :
      ∀ j, refinedBound ≤ j → refinedTerm j = 0 := by
    intro j hj
    have hj_succ : refinedBound ≤ j + 1 := le_trans hj (Nat.le_succ _)
    simp [refinedTerm, truncatedDyadicPoint_eq_time_of_le_ceil T (n + 1) j hj,
      truncatedDyadicPoint_eq_time_of_le_ceil T (n + 1) (j + 1) hj_succ]
  have hbound :
      refinedBound ≤ 2 * coarseBound := dyadicRefinedBound_le_double T n
  -- Proof comment: compare each coarse increment with the corresponding refined pair, then note
  -- that every refined term after the truncation index vanishes because the clipped dyadic row has
  -- already reached the terminal time `T`.
  unfold dyadicVariationSumUpTo
  calc
    Finset.sum (Finset.range coarseBound) (fun k ↦
        ENNReal.ofReal
          |G (min T (((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n)) -
            G (min T ((k : NNReal) / (2 : NNReal) ^ n))|)
        ≤ Finset.sum (Finset.range coarseBound) fun k ↦
            refinedTerm (2 * k) + refinedTerm (2 * k + 1) := by
          refine Finset.sum_le_sum hpointwise
    _ = Finset.sum (Finset.range (2 * coarseBound)) refinedTerm := by
      simpa using sum_pairs_eq_sum_range_double refinedTerm coarseBound
    _ = Finset.sum (Finset.range refinedBound) refinedTerm := by
      exact sum_range_eq_of_tail_zero refinedTerm hbound htail_zero
    _ = Finset.sum (Finset.range refinedBound) (fun k ↦
          ENNReal.ofReal
            |G (min T (((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ (n + 1))) -
              G (min T ((k : NNReal) / (2 : NNReal) ^ (n + 1)))|) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [refinedTerm, truncatedDyadicPoint, Definition2158.dyadicPartitionSequence]
    _ = dyadicVariationSumUpTo G T (n + 1) := by
      rfl

/-- Helper for Remark 21.60: the rounded-up dyadic index of `x` at mesh level `n`. -/
def upperTruncatedDyadicIndex (n : ℕ) (x : NNReal) : ℕ :=
  Nat.ceil ((x : ℝ) * (2 : ℝ) ^ n)

/-- Helper for Remark 21.60: the rounded-up clipped dyadic sample point attached to `x` at level
`n`. -/
def upperTruncatedDyadicPoint (T : NNReal) (n : ℕ) (x : NNReal) : NNReal :=
  truncatedDyadicPoint T n (upperTruncatedDyadicIndex n x)

/-- Helper for Remark 21.60: the rounded-up dyadic index is monotone, and on `Set.Icc 0 T` it
stays below the truncation index of `T`. -/
lemma upperTruncatedDyadicIndex_monotone (n : ℕ) :
    Monotone (upperTruncatedDyadicIndex n) := by
  -- Proof comment: `Nat.ceil` preserves order, and multiplying by the fixed positive dyadic factor
  -- keeps the time variable monotone.
  intro x y hxy
  apply Nat.ceil_mono
  gcongr

/-- Helper for Remark 21.60: the rounded-up dyadic index of a point in `Set.Icc 0 T` stays inside
the active truncated dyadic row. -/
lemma upperTruncatedDyadicIndex_le (T : NNReal) (n : ℕ) {x : NNReal}
    (hx : x ∈ Set.Icc 0 T) :
    upperTruncatedDyadicIndex n x ≤ Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) := by
  -- Proof comment: once `x ≤ T`, the same monotonicity for `Nat.ceil` bounds the rounded-up index
  -- by the rounded-up terminal index.
  apply Nat.ceil_mono
  gcongr
  exact hx.2

/-- Helper for Remark 21.60: rounding `x` up to the clipped dyadic row never moves it to the left.
-/
lemma le_upperTruncatedDyadicPoint (T : NNReal) (n : ℕ) {x : NNReal}
    (hx : x ∈ Set.Icc 0 T) :
    x ≤ upperTruncatedDyadicPoint T n x := by
  -- Proof comment: the dyadic ceiling produces a sample time at or to the right of `x`, and the
  -- final truncation by `T` does not change that because `x ≤ T`.
  dsimp [upperTruncatedDyadicPoint, truncatedDyadicPoint, upperTruncatedDyadicIndex]
  apply le_min hx.2
  have hpow : 0 < (2 : ℝ) ^ n := by
    positivity
  have hceil : (x : ℝ) * (2 : ℝ) ^ n ≤ Nat.ceil ((x : ℝ) * (2 : ℝ) ^ n) := Nat.le_ceil _
  have hdiv : (x : ℝ) ≤ (Nat.ceil ((x : ℝ) * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n := by
    exact (le_div_iff₀ hpow).2 hceil
  rw [Definition2158.dyadicPartitionSequence]
  exact (NNReal.coe_le_coe).mp <| by
    simpa [NNReal.coe_div, NNReal.coe_pow, hpow.ne'] using hdiv

/-- Helper for Remark 21.60: rounding `x` up to the clipped dyadic row overshoots by at most one
dyadic mesh. -/
lemma upperTruncatedDyadicPoint_le_add_mesh (T : NNReal) (n : ℕ) {x : NNReal} :
    upperTruncatedDyadicPoint T n x ≤ x + ((2 : NNReal)⁻¹) ^ n := by
  -- Proof comment: the ceiling index differs from `x * 2^n` by less than `1`, so dividing by
  -- `2^n` bounds the overshoot by one mesh interval.
  dsimp [upperTruncatedDyadicPoint, truncatedDyadicPoint, upperTruncatedDyadicIndex]
  refine le_trans (min_le_right _ _) ?_
  have hpow : 0 < (2 : ℝ) ^ n := by
    positivity
  have hxnonneg : 0 ≤ (x : ℝ) * (2 : ℝ) ^ n := by
    positivity
  have hceil : (Nat.ceil ((x : ℝ) * (2 : ℝ) ^ n) : ℝ) < (x : ℝ) * (2 : ℝ) ^ n + 1 :=
    Nat.ceil_lt_add_one hxnonneg
  have hdiv : (Nat.ceil ((x : ℝ) * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n ≤
      (x : ℝ) + ((2 : ℝ) ^ n)⁻¹ := by
    have hlt :
        (Nat.ceil ((x : ℝ) * (2 : ℝ) ^ n) : ℝ) <
          (((x : ℝ) + ((2 : ℝ) ^ n)⁻¹) * (2 : ℝ) ^ n) := by
      simpa [mul_add, add_mul, div_eq_mul_inv, hpow.ne', mul_assoc, inv_mul_cancel₀] using hceil
    exact (div_le_iff₀ hpow).2 hlt.le
  have hmesh : (((2 : NNReal)⁻¹) ^ n : NNReal) = (1 : NNReal) / (2 : NNReal) ^ n := by
    simp [div_eq_mul_inv]
  rw [hmesh]
  exact (NNReal.coe_le_coe).mp <| by
    simpa [NNReal.coe_div, NNReal.coe_pow, hpow.ne', div_eq_mul_inv] using hdiv

/-- Helper for Remark 21.60: the rounded-up clipped dyadic sample points converge down to the
original point on `Set.Icc 0 T`. -/
lemma upperTruncatedDyadicPoint_tendsto (T : NNReal) {x : NNReal} (hx : x ∈ Set.Icc 0 T) :
    Tendsto (fun n ↦ upperTruncatedDyadicPoint T n x) atTop (𝓝 x) := by
  -- Proof comment: the rounded-up samples are squeezed between the constant sequence `x` and the
  -- one-mesh overshoot `x + 2^{-n}`.
  have hpow : Tendsto (fun n : ℕ ↦ ((2 : NNReal)⁻¹) ^ n) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n ↦ upperTruncatedDyadicPoint T n x)
    (g := fun _ : ℕ ↦ x)
    (h := fun n ↦ x + ((2 : NNReal)⁻¹) ^ n)
    tendsto_const_nhds
    (by simpa using tendsto_const_nhds.add hpow)
    (Filter.Eventually.of_forall fun n ↦ le_upperTruncatedDyadicPoint T n hx)
    (Filter.Eventually.of_forall fun n ↦ upperTruncatedDyadicPoint_le_add_mesh T n)

/-- Helper for Remark 21.60: the direct increment between two points of a discrete chain is
dominated by the sum of the consecutive increments between them. -/
lemma increment_le_sum_Ico (F : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    edist (F b) (F a) ≤ ∑ j ∈ Finset.Ico a b, edist (F (j + 1)) (F j) := by
  -- Proof comment: expand the jump from `a` to `b` one adjacent step at a time and iterate the
  -- triangle inequality.
  induction' hab with b hab ih
  · simp
  · calc
      edist (F (b + 1)) (F a) ≤ edist (F (b + 1)) (F b) + edist (F b) (F a) :=
        edist_triangle _ _ _
      _ ≤ edist (F (b + 1)) (F b) + ∑ j ∈ Finset.Ico a b, edist (F (j + 1)) (F j) := by
        gcongr
      _ = ∑ j ∈ Finset.Ico a (b + 1), edist (F (j + 1)) (F j) := by
        rw [Finset.sum_Ico_succ_top hab]
        simp [add_comm]

/-- Helper for Remark 21.60: summing consecutive interval sums along a monotone discrete chain
collapses to the single sum over the full interval between its endpoints. -/
lemma sumIntervals_eq_sum_Ico (f : ℕ → ℝ≥0∞) {u : ℕ → ℕ} (hu : Monotone u) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ico (u i) (u (i + 1)), f j) =
      ∑ j ∈ Finset.Ico (u 0) (u n), f j := by
  -- Proof comment: consecutive `Ico` blocks along a monotone index chain glue together without
  -- overlap.
  induction' n with n ih
  · simp
  · have hu0n : u 0 ≤ u n := hu (Nat.zero_le _)
    have hun : u n ≤ u (n + 1) := hu (Nat.le_succ _)
    rw [Finset.sum_range_succ, ih, ← Finset.sum_union]
    · simp [Finset.Ico_union_Ico_eq_Ico hu0n hun]
    · exact Finset.Ico_disjoint_Ico_consecutive _ _ _

/-- Helper for Remark 21.60: a monotone discrete subchain of a finite chain has no more total
increment than the full chain. -/
lemma selectedChain_le_fullChain (F : ℕ → ℝ) {u : ℕ → ℕ} (hu : Monotone u) {n m : ℕ}
    (hum : ∀ i ≤ n, u i ≤ m) :
    ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i)) ≤
      ∑ j ∈ Finset.range m, edist (F (j + 1)) (F j) := by
  -- Proof comment: each selected jump is dominated by the adjacent increments over its index
  -- interval, and the union of those intervals stays inside the full chain up to `m`.
  calc
    ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))
      ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ico (u i) (u (i + 1)), edist (F (j + 1)) (F j) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact increment_le_sum_Ico F (hu (Nat.le_succ _))
    _ = ∑ j ∈ Finset.Ico (u 0) (u n), edist (F (j + 1)) (F j) := by
          simpa using sumIntervals_eq_sum_Ico (fun j ↦ edist (F (j + 1)) (F j)) hu n
    _ ≤ ∑ j ∈ Finset.range m, edist (F (j + 1)) (F j) := by
          exact Finset.sum_mono_set (f := fun j ↦ edist (F (j + 1)) (F j)) <| by
            intro j hj
            rw [Finset.mem_Ico] at hj
            rw [Finset.mem_range]
            exact lt_of_lt_of_le hj.2 (hum n le_rfl)

/-- Helper for Remark 21.60: any monotone subchain of the clipped dyadic row contributes no more
variation than the full consecutive dyadic row up to the truncation index. -/
lemma selectedChain_le_fullDyadicChain
    (G : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) {u : ℕ → ℕ} (hu : Monotone u) {k : ℕ}
    (hum : ∀ i ≤ k, u i ≤ Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n)) :
    ∑ i ∈ Finset.range k,
        edist (G (truncatedDyadicPoint T n (u (i + 1)))) (G (truncatedDyadicPoint T n (u i))) ≤
      dyadicVariationSumUpTo G T n := by
  -- Proof comment: each selected jump is bounded by the adjacent dyadic increments across the
  -- corresponding index interval, and those index intervals merge into one subset of the active
  -- dyadic range.
  let F : ℕ → ℝ := fun j ↦ G (truncatedDyadicPoint T n j)
  calc
    ∑ i ∈ Finset.range k, edist (G (truncatedDyadicPoint T n (u (i + 1))))
        (G (truncatedDyadicPoint T n (u i)))
      = ∑ i ∈ Finset.range k, edist (F (u (i + 1))) (F (u i)) := by
          rfl
    _ ≤ ∑ j ∈ Finset.range (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n)), edist (F (j + 1)) (F j) := by
          refine selectedChain_le_fullChain F hu ?_
          intro i hi
          exact hum i hi
    _ = dyadicVariationSumUpTo G T n := by
          unfold dyadicVariationSumUpTo
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa [F, truncatedDyadicPoint, Definition2158.dyadicPartitionSequence] using
            (truncatedDyadicIncrement_eq_edist G T n j).symm

-- Proof sketch: the preceding monotonicity gives existence of the limit in `ℝ≥0∞`, and the
-- characterization of total variation as the supremum over partition sums identifies that limit
-- with `variationUpTo G T`.
/-- Remark 21.60: for a continuous path `G` on `[0, ∞)`, the first-variation sums along the
truncated dyadic partitions of `[0, T]` converge to the total variation `eVariationOn G (Set.Icc
0 T)`, i.e. the `V¹` quantity from Definition 21.52; hence the `p = 1` partition limit is
independent of the chosen dyadic approximation. -/
theorem dyadicVariationSumUpTo_tendsto_eVariationOn_Icc (G : C(NNReal, ℝ)) (T : NNReal) :
    Tendsto (fun n ↦ dyadicVariationSumUpTo G T n) atTop (𝓝 (eVariationOn G (Set.Icc 0 T))) := by
  have hmono : Monotone (dyadicVariationSumUpTo G T) := dyadicVariationSumUpTo_monotone G T
  have hupper :
      ∀ n, dyadicVariationSumUpTo G T n ≤ eVariationOn G (Set.Icc 0 T) :=
    dyadicVariationSumUpTo_le_eVariationOn_Icc G T
  have htendstoSup :
      Tendsto (fun n ↦ dyadicVariationSumUpTo G T n) atTop
        (𝓝 (⨆ n, dyadicVariationSumUpTo G T n)) :=
    tendsto_atTop_iSup hmono
  have hSup_le :
      (⨆ n, dyadicVariationSumUpTo G T n) ≤ eVariationOn G (Set.Icc 0 T) := by
    exact iSup_le hupper
  have hle_iSup :
      eVariationOn G (Set.Icc 0 T) ≤ ⨆ n, dyadicVariationSumUpTo G T n := by
    -- Route correction: instead of constructing a global dyadic refinement of every strict
    -- partition, approximate one fixed finite witness for `eVariationOn` by rounding each witness
    -- point up to the dyadic mesh and compare the resulting discrete chain with the full dyadic
    -- row.
    refine le_of_forall_lt ?_
    intro v hv
    obtain ⟨k, u, hu, huv⟩ : ∃ k u, (Monotone u ∧ ∀ i, u i ∈ Set.Icc 0 T) ∧
        v < ∑ i ∈ Finset.range k, edist (G (u (i + 1))) (G (u i)) := by
      simpa [eVariationOn, lt_iSup_iff] using hv
    rcases hu with ⟨hu_mono, hu_mem⟩
    let approxIndex : ℕ → ℕ → ℕ := fun n i ↦ upperTruncatedDyadicIndex n (u i)
    let approxPoint : ℕ → ℕ → NNReal := fun n i ↦ upperTruncatedDyadicPoint T n (u i)
    let approxSum : ℕ → ℝ≥0∞ := fun n ↦
      ∑ i ∈ Finset.range k, edist (G (approxPoint n (i + 1))) (G (approxPoint n i))
    have happrox :
        Tendsto approxSum atTop
          (𝓝 (∑ i ∈ Finset.range k, edist (G (u (i + 1))) (G (u i)))) := by
      -- Proof comment: each rounded-up witness point converges back to the original witness point,
      -- so the corresponding finite sum of metric increments converges to the witness sum.
      refine tendsto_finset_sum _ ?_
      intro i hi
      have hleft :
          Tendsto (fun n ↦ G (approxPoint n (i + 1))) atTop (𝓝 (G (u (i + 1)))) := by
        exact (G.continuous.continuousAt).tendsto.comp
          (upperTruncatedDyadicPoint_tendsto T (hu_mem (i + 1)))
      have hright :
          Tendsto (fun n ↦ G (approxPoint n i)) atTop (𝓝 (G (u i))) := by
        exact (G.continuous.continuousAt).tendsto.comp
          (upperTruncatedDyadicPoint_tendsto T (hu_mem i))
      exact Tendsto.edist hleft hright
    have hv_eventually : ∀ᶠ n in atTop, v < approxSum n := happrox.eventually_const_lt huv
    have hchain :
        ∀ n, approxSum n ≤ dyadicVariationSumUpTo G T n := by
      intro n
      have happrox_mono : Monotone (approxIndex n) :=
        (upperTruncatedDyadicIndex_monotone n).comp hu_mono
      have happrox_bound :
          ∀ i ≤ k, approxIndex n i ≤ Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) := by
        intro i hi
        exact upperTruncatedDyadicIndex_le T n (hu_mem i)
      -- Proof comment: the rounded witness indices form a monotone dyadic subchain inside the
      -- active clipped row, so their variation is controlled by the full dyadic chain.
      simpa [approxSum, approxIndex, approxPoint] using
        selectedChain_le_fullDyadicChain G T n happrox_mono happrox_bound
    rcases Filter.eventually_atTop.1 (hv_eventually.mono fun n hn ↦ hn.trans_le (hchain n)) with
      ⟨N, hN⟩
    exact lt_iSup_iff.mpr ⟨N, hN N le_rfl⟩
  have hEq :
      (⨆ n, dyadicVariationSumUpTo G T n) = eVariationOn G (Set.Icc 0 T) :=
    le_antisymm hSup_le hle_iSup
  -- Proof comment: the monotone dyadic sums converge to their supremum, and the two-sided order
  -- comparison identifies that supremum with the total variation on `Set.Icc 0 T`.
  simpa [hEq] using htendstoSup

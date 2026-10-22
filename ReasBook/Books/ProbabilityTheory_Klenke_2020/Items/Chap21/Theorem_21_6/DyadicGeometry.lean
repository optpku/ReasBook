/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_5

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoEMetricSpace E]
variable {μ : Measure Ω}

variable (μ)

/-- The source-facing Kolmogorov condition on the finite interval `[0,T]`: the exponents `α` and
`β` are strictly positive, and the restricted process satisfies the canonical mathlib owner
`ProbabilityTheory.IsKolmogorovProcess` with exponents `α` and `1 + β`. This is the thin bridge
from the textbook finite-interval formulation to the global owner abstraction. -/
def IsKolmogorovProcessOnIcc (X : NNReal → Ω → E) (T α β C : ℝ≥0) : Prop :=
  0 < α ∧
    0 < β ∧
      IsKolmogorovProcess (fun t : Set.Icc (0 : NNReal) T ↦ X t) μ (α : ℝ) (1 + (β : ℝ)) C

theorem IsKolmogorovProcessOnIcc.alpha_pos
    {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C) :
    0 < α := by
  rcases h with ⟨hα, -, -⟩
  exact hα

theorem IsKolmogorovProcessOnIcc.beta_pos
    {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C) :
    0 < β := by
  rcases h with ⟨-, hβ, -⟩
  exact hβ

theorem IsKolmogorovProcessOnIcc.isKolmogorovProcess
    {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C) :
    IsKolmogorovProcess (fun t : Set.Icc (0 : NNReal) T ↦ X t) μ (α : ℝ) (1 + (β : ℝ)) C := by
  rcases h with ⟨-, -, hX⟩
  exact hX

variable {μ}

-- Proof sketch: apply the owner lemma `IsKolmogorovProcess.kolmogorovCondition` to the restricted
-- process on `Set.Icc (0, T)` and then simplify the subtype coercions.
/-- A finite-interval Kolmogorov condition gives the stated increment estimate on `[0,T]`. -/
theorem IsKolmogorovProcessOnIcc.increment_lintegral_le
    {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    {s t : NNReal} (hs : s ≤ T) (ht : t ≤ T) :
    ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤
      (C : ℝ≥0∞) * edist t s ^ (1 + (β : ℝ)) := by
  have hs' : s ∈ Set.Icc (0 : NNReal) T := by simpa using hs
  have ht' : t ∈ Set.Icc (0 : NNReal) T := by simpa using ht
  simpa [edist_comm] using h.isKolmogorovProcess.kolmogorovCondition ⟨s, hs'⟩ ⟨t, ht'⟩

variable [IsProbabilityMeasure μ]

/-- Helper for Theorem 21.6: use the canonical ceiling dyadic mesh to approximate a fixed time
from the right. -/
noncomputable def dyadicCutoff (T : NNReal) (n : ℕ) : ℕ :=
  Nat.ceil (T : ℝ) * 2 ^ n

/-- Helper for Theorem 21.6: the `k`-th sample time on the dyadic row of mesh `2^{-n}`, clipped
to the finite horizon `T`. -/
noncomputable def dyadicPointUpTo (T : NNReal) (n k : ℕ) : NNReal :=
  min T ((k : NNReal) / (2 : NNReal) ^ n)

/-- Helper for Theorem 21.6: every clipped dyadic sample time lies in the target interval
`[0, T]`. -/
lemma dyadicPointUpTo_mem_Icc (T : NNReal) (n k : ℕ) :
    dyadicPointUpTo T n k ∈ Set.Icc (0 : NNReal) T := by
  -- Proof comment: the dyadic sample time is defined by truncating with `min T`, so only the
  -- upper bound is nontrivial.
  refine Set.mem_Icc.mpr ⟨zero_le _, min_le_left _ _⟩

/-- Helper for Theorem 21.6: the deterministic cutoff index lands exactly at the terminal time
`T`. -/
lemma dyadicPointUpTo_cutoff (T : NNReal) (n : ℕ) :
    dyadicPointUpTo T n (dyadicCutoff T n) = T := by
  -- Proof comment: at the cutoff index the untruncated dyadic time is at least `⌈T⌉`, so the
  -- clipping `min T` collapses to `T`.
  unfold dyadicPointUpTo dyadicCutoff
  apply min_eq_left
  have hceil : T ≤ (Nat.ceil (T : ℝ) : NNReal) := by
    exact_mod_cast Nat.le_ceil (T : ℝ)
  have hpow_ne : (2 : NNReal) ^ n ≠ 0 := by
    positivity
  have hcutoff :
      ((Nat.ceil (T : ℝ) * 2 ^ n : ℕ) : NNReal) / (2 : NNReal) ^ n =
        (Nat.ceil (T : ℝ) : NNReal) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_div_cancel₀ (Nat.ceil (T : ℝ) : NNReal) hpow_ne)
  calc
    T ≤ (Nat.ceil (T : ℝ) : NNReal) := hceil
    _ = ((Nat.ceil (T : ℝ) * 2 ^ n : ℕ) : NNReal) / (2 : NNReal) ^ n := hcutoff.symm

/-- Helper for Theorem 21.6: refining the dyadic mesh by one step preserves the old row values at
even indices. -/
lemma dyadicPointUpTo_even (T : NNReal) (n k : ℕ) :
    dyadicPointUpTo T (n + 1) (2 * k) = dyadicPointUpTo T n k := by
  -- Proof comment: doubling the row index exactly compensates for the extra factor of `2` in the
  -- refined mesh denominator.
  unfold dyadicPointUpTo
  have htwo : (2 : NNReal) ≠ 0 := by
    positivity
  calc
    min T (((2 * k : ℕ) : NNReal) / (2 : NNReal) ^ (n + 1))
        = min T (((k : NNReal) * 2) / ((2 : NNReal) ^ n * 2)) := by
            simp [Nat.cast_mul, pow_succ, mul_comm]
    _ = min T ((k : NNReal) / (2 : NNReal) ^ n) := by
          rw [mul_div_mul_right _ _ htwo]

/-- Helper for Theorem 21.6: any coarse dyadic row sample reappears on a finer row after the
obvious index rescaling. -/
lemma dyadicPointUpTo_refine
    (T : NNReal) (m r k : ℕ) :
    dyadicPointUpTo T (m + r) (k * 2 ^ r) = dyadicPointUpTo T m k := by
  induction r generalizing k with
  | zero =>
      -- Proof comment: no refinement means no change in the row or the index.
      simp [dyadicPointUpTo]
  | succ r ihr =>
      -- Proof comment: peel off one refinement step, rewrite the rescaled index as an even
      -- index, and then invoke the one-step compatibility lemma.
      calc
        dyadicPointUpTo T (m + r.succ) (k * 2 ^ r.succ)
            = dyadicPointUpTo T ((m + r) + 1) (2 * (k * 2 ^ r)) := by
                have hk :
                    k * 2 ^ r.succ = 2 * (k * 2 ^ r) := by
                  simp [pow_succ, Nat.mul_left_comm, Nat.mul_comm]
                rw [hk, Nat.add_assoc]
        _ = dyadicPointUpTo T (m + r) (k * 2 ^ r) := by
              simpa using dyadicPointUpTo_even (T := T) (n := m + r) (k := k * 2 ^ r)
        _ = dyadicPointUpTo T m k := ihr k

/-- Helper for Theorem 21.6: the right-dyadic approximant index stays below the deterministic row
cutoff on any horizon containing the target time. -/
lemma dyadicRightApprox_index_le_cutoff {t T : NNReal} (htT : t ≤ T) (n : ℕ) :
    Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) ≤ dyadicCutoff T n := by
  -- Proof comment: once `t ≤ T ≤ ⌈T⌉`, scaling by `2^n` bounds the dyadic ceil-index by the row
  -- cutoff.
  unfold dyadicCutoff
  refine Nat.ceil_le.mpr ?_
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
  calc
    (t : ℝ) * (2 : ℝ) ^ n ≤ (T : ℝ) * (2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast htT) hpow_nonneg
    _ ≤ (Nat.ceil (T : ℝ) : ℝ) * (2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil (T : ℝ)) hpow_nonneg
    _ = ((Nat.ceil (T : ℝ) * 2 ^ n : ℕ) : ℝ) := by
      simp [Nat.cast_mul, Nat.cast_pow]

noncomputable def dyadicRightApprox (t : NNReal) (n : ℕ) : NNReal :=
  ((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : NNReal) / (2 : NNReal) ^ n

/-- Helper for Theorem 21.6: the canonical dyadic approximants stay to the right of the target
time. -/
lemma le_dyadicRightApprox (t : NNReal) (n : ℕ) :
    t ≤ dyadicRightApprox t n := by
  -- Proof comment: `Nat.ceil` rounds the scaled time upward, so dividing back by `2^n` does not
  -- move the sample time to the left of `t`.
  unfold dyadicRightApprox
  have hpow_pos : 0 < (2 : NNReal) ^ n := by
    positivity
  rw [le_div_iff₀ hpow_pos]
  exact_mod_cast Nat.le_ceil ((t : ℝ) * (2 : ℝ) ^ n)

/-- Helper for Theorem 21.6: the canonical dyadic approximants converge back to the target
time. -/
lemma tendsto_dyadicRightApprox (t : NNReal) :
    Filter.Tendsto (dyadicRightApprox t) Filter.atTop (nhds t) := by
  -- Proof comment: this is the standard `ceil (t * 2^n) / 2^n → t` limit on the dyadic mesh.
  refine (NNReal.tendsto_coe).mp ?_
  simpa [dyadicRightApprox] using
    (tendsto_nat_ceil_mul_div_atTop (a := (t : ℝ)) t.2).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Helper for Theorem 21.6: the clipped right-dyadic approximant is the right-dyadic
approximant truncated back to the finite horizon `T`. -/
noncomputable def clippedDyadicApprox (T t : NNReal) (n : ℕ) : NNReal :=
  dyadicPointUpTo T n (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n))

/-- Helper for Theorem 21.6: every clipped right-dyadic approximant stays inside `[0, T]`. -/
lemma clippedDyadicApprox_mem_Icc (T t : NNReal) (n : ℕ) :
    clippedDyadicApprox T t n ∈ Set.Icc (0 : NNReal) T := by
  -- Proof comment: this is the interval-membership lemma for the dyadic row specialized to the
  -- canonical ceil-index of `t`.
  simpa [clippedDyadicApprox] using
    dyadicPointUpTo_mem_Icc T n (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n))

/-- Helper for Theorem 21.6: the clipped approximant is literally `min T` applied to the raw
right-dyadic approximant. -/
lemma clippedDyadicApprox_eq_min_dyadicRightApprox (T t : NNReal) (n : ℕ) :
    clippedDyadicApprox T t n = min T (dyadicRightApprox t n) := by
  -- Proof comment: unfolding both definitions shows that the clipped finite-horizon approximant
  -- is exactly the right-dyadic approximant followed by truncation at `T`.
  rfl

/-- Helper for Theorem 21.6: if the target time lies in `[0, T]`, then the clipped right-dyadic
approximants still converge to that time. -/
lemma tendsto_clippedDyadicApprox {t T : NNReal} (htT : t ≤ T) :
    Filter.Tendsto (clippedDyadicApprox T t) Filter.atTop (nhds t) := by
  -- Proof comment: clipping by `min T` is continuous, and at the limit point `t` the clipping is
  -- inactive because `t ≤ T`.
  have hmin :
      Filter.Tendsto (fun x : NNReal ↦ min T x) (nhds t) (nhds (min T t)) :=
    (continuous_const.min continuous_id).continuousAt.tendsto
  have hclip :
      Filter.Tendsto (fun n ↦ min T (dyadicRightApprox t n)) Filter.atTop (nhds (min T t)) :=
    hmin.comp (tendsto_dyadicRightApprox t)
  simpa [clippedDyadicApprox_eq_min_dyadicRightApprox, min_eq_right htT] using hclip

/-- Helper for Theorem 21.6: every finite prefix of the clipped approximant sequence sits inside a
single sufficiently fine clipped dyadic row on `[0, T]`. -/
lemma clippedDyadicApprox_prefix_embeds_in_row
    {t T : NNReal} (htT : t ≤ T) {m N : ℕ} (hmN : m ≤ N) :
    let k := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ m) * 2 ^ (N - m)
    k ≤ dyadicCutoff T N ∧
      dyadicPointUpTo T N k = clippedDyadicApprox T t m := by
  let j : ℕ := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ m)
  let k : ℕ := j * 2 ^ (N - m)
  have hj_le : j ≤ dyadicCutoff T m := by
    -- Proof comment: the coarse right-dyadic approximant index already lies below the clipped row
    -- cutoff on the finite horizon.
    exact dyadicRightApprox_index_le_cutoff (t := t) (T := T) htT m
  have hk_le : k ≤ dyadicCutoff T N := by
    have hk_le' : j * 2 ^ (N - m) ≤ dyadicCutoff T m * 2 ^ (N - m) :=
      Nat.mul_le_mul_right (2 ^ (N - m)) hj_le
    have hcutoff_refine :
        dyadicCutoff T m * 2 ^ (N - m) = dyadicCutoff T N := by
      unfold dyadicCutoff
      calc
        Nat.ceil ↑T * 2 ^ m * 2 ^ (N - m)
            = Nat.ceil ↑T * (2 ^ m * 2 ^ (N - m)) := by rw [Nat.mul_assoc]
        _ = Nat.ceil ↑T * 2 ^ (m + (N - m)) := by rw [← pow_add]
        _ = Nat.ceil ↑T * 2 ^ N := by rw [Nat.add_sub_of_le hmN]
    exact hk_le'.trans_eq hcutoff_refine
  have hk_eq : dyadicPointUpTo T N k = clippedDyadicApprox T t m := by
    -- Proof comment: the fine-row sample at the rescaled index collapses back to the coarse
    -- clipped approximant via the refinement lemma.
    calc
      dyadicPointUpTo T N k = dyadicPointUpTo T m j := by
        simpa [k, j, Nat.add_sub_of_le hmN, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using dyadicPointUpTo_refine (T := T) m (N - m) j
      _ = clippedDyadicApprox T t m := by
        rfl
  simpa [k, j] using And.intro hk_le hk_eq

/-- Helper for Theorem 21.6: the dyadic increment threshold at row `n` for exponent `q` is the
mesh size `2^{-q n}` written in the ambient real arithmetic. -/
noncomputable def dyadicStepThreshold (q : ℝ≥0) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((q : ℝ) * n))

/-- Helper for Theorem 21.6: the row-`n` bad event is that at least one adjacent clipped dyadic
increment exceeds the threshold `2^{-q n}`. -/
def dyadicRowBadEvent
    (X : NNReal → Ω → ℝ) (T q : ℝ≥0) (n : ℕ) : Set Ω :=
  {ω | ∃ k < dyadicCutoff T n,
      dyadicStepThreshold q n <
        dist (X (dyadicPointUpTo T n (k + 1)) ω) (X (dyadicPointUpTo T n k) ω)}

/-- Helper for Theorem 21.6: outside the bad event for row `n`, every adjacent clipped dyadic
increment on that row is bounded by the threshold `2^{-q n}`. -/
lemma dist_le_dyadicStepThreshold_of_notMem_dyadicRowBadEvent
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {n k : ℕ} {ω : Ω}
    (hgood : ω ∉ dyadicRowBadEvent (X := X) T q n)
    (hk : k < dyadicCutoff T n) :
    dist (X (dyadicPointUpTo T n (k + 1)) ω) (X (dyadicPointUpTo T n k) ω) ≤
      dyadicStepThreshold q n := by
  -- Proof comment: if one adjacent increment were larger than the threshold, that witness would
  -- place `ω` back into the bad event by definition.
  by_contra hdist
  exact hgood ⟨k, hk, lt_of_not_ge hdist⟩

/-- Helper for Theorem 21.6: adjacent points on a clipped dyadic row are separated by at most one
mesh size `2^{-n}`. -/
lemma dist_dyadicPointUpTo_succ_le_mesh (T : NNReal) (n k : ℕ) :
    dist (dyadicPointUpTo T n (k + 1)) (dyadicPointUpTo T n k) ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
  have hpow_pos : 0 < (2 : ℝ) ^ n := by
    positivity
  have hmin :
      |min (T : ℝ) ((((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ) -
          min (T : ℝ) ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ)| ≤
        |((((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ) -
          ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ)| := by
    calc
      |min (T : ℝ) ((((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ) -
          min (T : ℝ) ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ)|
          ≤ max
              |(T : ℝ) - (T : ℝ)|
              |((((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ) -
                ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ)| := by
              simpa using
                abs_min_sub_min_le_max
                  (T : ℝ)
                  ((((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ)
                  (T : ℝ)
                  ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ)
      _ = |((((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ) -
            ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ)| := by
            simp
  have hraw_eq :
      ((((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ) -
          ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ) =
        (1 : ℝ) / (2 : ℝ) ^ n := by
    norm_num [Nat.cast_add, Nat.cast_one, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow]
    ring
  have hraw_nonneg :
      0 ≤
        ((((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ) -
          ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n : NNReal) : ℝ) := by
    rw [hraw_eq]
    positivity
  -- Proof comment: clipping by `min T` is 1-Lipschitz, so the row increment cannot exceed the
  -- mesh size of the unclipped dyadic grid.
  rw [NNReal.dist_eq]
  exact (hmin.trans_eq <| by rw [abs_of_nonneg hraw_nonneg, hraw_eq])

/-- Helper for Theorem 21.6: the refined right-dyadic index is either the doubled coarse index or
the immediately preceding index on the finer row. -/
lemma refinedDyadicApproxIndices_adjacent (t : NNReal) (n : ℕ) :
    let j := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)
    let j' := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ (n + 1))
    j' ≤ 2 * j ∧ 2 * j ≤ j' + 1 := by
  let x : ℝ := (t : ℝ) * (2 : ℝ) ^ n
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hrefine :
      ((t : ℝ) * (2 : ℝ) ^ (n + 1)) = 2 * x := by
    -- Proof comment: the refined dyadic scale is just the coarse scale multiplied by `2`.
    dsimp [x]
    rw [pow_succ]
    ring
  constructor
  · -- Proof comment: `⌈2x⌉` is bounded by `2⌈x⌉` because `x ≤ ⌈x⌉`.
    rw [hrefine]
    refine Nat.ceil_le.2 ?_
    calc
      2 * x ≤ 2 * (Nat.ceil x : ℝ) := by
        gcongr
        exact Nat.le_ceil x
      _ = ((2 * Nat.ceil x : ℕ) : ℝ) := by norm_num
  · -- Proof comment: the strict upper bound `⌈x⌉ < x + 1` implies
    -- `2⌈x⌉ < ⌈2x⌉ + 2`, which is the same as `2⌈x⌉ ≤ ⌈2x⌉ + 1` for naturals.
    rw [hrefine]
    have hceil_lt : ((Nat.ceil x : ℝ)) < x + 1 := Nat.ceil_lt_add_one hx_nonneg
    have hdouble_lt :
        (2 * (Nat.ceil x : ℝ)) < (Nat.ceil (2 * x) : ℝ) + 2 := by
      have hleft : (2 * (Nat.ceil x : ℝ)) < 2 * x + 2 := by
        nlinarith
      have hright : 2 * x + 2 ≤ (Nat.ceil (2 * x) : ℝ) + 2 := by
        gcongr
        exact Nat.le_ceil (2 * x)
      exact lt_of_lt_of_le hleft hright
    have hdouble_nat : 2 * Nat.ceil x < Nat.ceil (2 * x) + 2 := by
      exact_mod_cast hdouble_lt
    have hsucc : 2 * Nat.ceil x < (Nat.ceil (2 * x) + 1).succ := by
      simpa [Nat.add_assoc] using hdouble_nat
    exact Nat.lt_succ_iff.mp hsucc

/-- Helper for Theorem 21.6: if two times are within one mesh `2^{-n}` and ordered, then their
right-dyadic row indices at level `n` differ by at most one. -/
lemma dyadicApproxIndices_adjacent_of_dist_le
    {s t : NNReal} {n : ℕ}
    (hst : s ≤ t)
    (hclose : dist s t ≤ (1 : ℝ) / (2 : ℝ) ^ n) :
    Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) ≤ Nat.ceil ((s : ℝ) * (2 : ℝ) ^ n) + 1 := by
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := by
    positivity
  have hst_real : (s : ℝ) ≤ t := by
    exact_mod_cast hst
  have hdist_eq : dist s t = (t : ℝ) - s := by
    rw [NNReal.dist_eq, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr hst_real
  have hsub_le : (t : ℝ) - s ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
    simpa [hdist_eq] using hclose
  have hmul_le : (t : ℝ) * (2 : ℝ) ^ n ≤ (s : ℝ) * (2 : ℝ) ^ n + 1 := by
    have hscaled := mul_le_mul_of_nonneg_right hsub_le hpow_nonneg
    have hpow_pos : 0 < (2 : ℝ) ^ n := by
      positivity
    have hpow_ne : (2 : ℝ) ^ n ≠ 0 := hpow_pos.ne'
    have hunit : ((1 : ℝ) / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = 1 := by
      field_simp [hpow_ne]
    have hscaled' : ((t : ℝ) - s) * (2 : ℝ) ^ n ≤ 1 := by
      simpa [hunit] using hscaled
    nlinarith
  -- Proof comment: after scaling by `2^n`, a one-mesh time gap becomes a difference of at most
  -- `1`, so the ceiling indices can differ by at most one.
  have hs_nonneg : 0 ≤ (s : ℝ) * (2 : ℝ) ^ n := by
    positivity
  exact le_trans (Nat.ceil_mono hmul_le) <|
    by simpa using (Nat.ceil_add_natCast hs_nonneg 1).le

/-- Helper for Theorem 21.6: on a good dyadic row, two clipped right-dyadic approximants at the
same level and within one mesh differ by at most one threshold jump. -/
lemma clippedDyadicApprox_pair_le_of_rowGood_of_dist_le
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {s t : NNReal} {n : ℕ} {ω : Ω}
    (hsT : s ≤ T)
    (htT : t ≤ T)
    (hst : s ≤ t)
    (hclose : dist s t ≤ (1 : ℝ) / (2 : ℝ) ^ n)
    (hgood : ω ∉ dyadicRowBadEvent (X := X) T q n) :
    dist (X (clippedDyadicApprox T t n) ω) (X (clippedDyadicApprox T s n) ω) ≤
      dyadicStepThreshold q n := by
  let i := Nat.ceil ((s : ℝ) * (2 : ℝ) ^ n)
  let j := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)
  have hij_le : j ≤ i + 1 :=
    dyadicApproxIndices_adjacent_of_dist_le (s := s) (t := t) (n := n) hst hclose
  have hij_mono : i ≤ j := by
    have hscaled : (s : ℝ) * (2 : ℝ) ^ n ≤ (t : ℝ) * (2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hst) (by positivity)
    exact Nat.ceil_mono hscaled
  by_cases hij : i = j
  · -- Proof comment: if the dyadic indices coincide, then the clipped approximants are equal.
    have hsame : clippedDyadicApprox T t n = clippedDyadicApprox T s n := by
      simp [clippedDyadicApprox, i, j, hij]
    have hnonneg : 0 ≤ dyadicStepThreshold q n := by
      unfold dyadicStepThreshold
      positivity
    simpa [hsame] using hnonneg
  · have hj_eq : j = i + 1 := by
      omega
    have hj_le_cutoff : j ≤ dyadicCutoff T n := by
      simpa [j] using dyadicRightApprox_index_le_cutoff (t := t) (T := T) htT n
    have hi_lt_cutoff : i < dyadicCutoff T n := by
      omega
    have hrow :
        dist (X (dyadicPointUpTo T n (i + 1)) ω) (X (dyadicPointUpTo T n i) ω) ≤
          dyadicStepThreshold q n :=
      dist_le_dyadicStepThreshold_of_notMem_dyadicRowBadEvent
        (X := X) (T := T) (q := q) (n := n) hgood hi_lt_cutoff
    -- Proof comment: if the indices differ, they are consecutive, so the row-good estimate
    -- applies directly to that adjacent pair.
    simpa [clippedDyadicApprox, i, j, hj_eq] using hrow

/-- Helper for Theorem 21.6: if the refined dyadic row is good at `ω`, then two successive clipped
right-dyadic approximants of the same time differ by at most one good-row increment. -/
lemma clippedDyadicApprox_step_le_of_rowGood
    {X : NNReal → Ω → ℝ} {T q : ℝ≥0} {t : NNReal} {n : ℕ} {ω : Ω}
    (htT : t ≤ T)
    (hgood : ω ∉ dyadicRowBadEvent (X := X) T q (n + 1)) :
    dist (X (clippedDyadicApprox T t (n + 1)) ω) (X (clippedDyadicApprox T t n) ω) ≤
      dyadicStepThreshold q (n + 1) := by
  let j := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)
  let j' := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ (n + 1))
  have hcoarse :
      clippedDyadicApprox T t n = dyadicPointUpTo T (n + 1) (2 * j) := by
    -- Proof comment: the coarse clipped approximant reappears on the refined row at the doubled
    -- coarse index.
    change dyadicPointUpTo T n j = dyadicPointUpTo T (n + 1) (2 * j)
    symm
    simpa [j] using dyadicPointUpTo_even (T := T) (n := n) (k := j)
  have hindices := refinedDyadicApproxIndices_adjacent (t := t) n
  dsimp [j, j'] at hindices
  rcases hindices with ⟨hj'le, htwice_le⟩
  by_cases hsame : j' = 2 * j
  · -- Proof comment: in the equal-index case the two clipped approximants coincide exactly.
    have hsamePoint : clippedDyadicApprox T t (n + 1) = clippedDyadicApprox T t n := by
      calc
        clippedDyadicApprox T t (n + 1) = dyadicPointUpTo T (n + 1) j' := rfl
        _ = dyadicPointUpTo T (n + 1) (2 * j) := by rw [hsame]
        _ = clippedDyadicApprox T t n := hcoarse.symm
    have hnonneg : 0 ≤ dyadicStepThreshold q (n + 1) := by
      unfold dyadicStepThreshold
      positivity
    simpa [hsamePoint] using hnonneg
  · have hadj : j' + 1 = 2 * j := by
      omega
    have hj_le : j ≤ dyadicCutoff T n := by
      exact dyadicRightApprox_index_le_cutoff (t := t) (T := T) htT n
    have h2j_le : 2 * j ≤ dyadicCutoff T (n + 1) := by
      -- Proof comment: doubling a valid coarse-row index keeps it inside the refined-row cutoff.
      calc
        2 * j ≤ 2 * dyadicCutoff T n := Nat.mul_le_mul_left 2 hj_le
        _ = dyadicCutoff T (n + 1) := by
          unfold dyadicCutoff
          simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hj'_lt : j' < dyadicCutoff T (n + 1) := by
      omega
    have hrow :
        dist (X (dyadicPointUpTo T (n + 1) (j' + 1)) ω) (X (dyadicPointUpTo T (n + 1) j') ω) ≤
          dyadicStepThreshold q (n + 1) :=
      dist_le_dyadicStepThreshold_of_notMem_dyadicRowBadEvent
        (X := X) (T := T) (q := q) (n := n + 1) hgood hj'_lt
    -- Proof comment: in the adjacent-index case, the two clipped approximants are neighboring
    -- refined-row points, so the row-good bound applies directly.
    calc
      dist (X (clippedDyadicApprox T t (n + 1)) ω) (X (clippedDyadicApprox T t n) ω)
          = dist (X (dyadicPointUpTo T (n + 1) j') ω)
              (X (dyadicPointUpTo T (n + 1) (j' + 1)) ω) := by
                rw [show clippedDyadicApprox T t (n + 1) = dyadicPointUpTo T (n + 1) j' by rfl,
                  hcoarse, hadj]
      _ = dist (X (dyadicPointUpTo T (n + 1) (j' + 1)) ω)
            (X (dyadicPointUpTo T (n + 1) j') ω) := by
              rw [dist_comm]
      _ ≤ dyadicStepThreshold q (n + 1) := hrow

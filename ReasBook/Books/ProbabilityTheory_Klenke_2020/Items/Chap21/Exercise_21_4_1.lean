/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The running supremum `|X|*_T` of a real-valued continuous-time process on the interval
`[0, T]`, represented canonically as an `ℝ≥0∞`-valued interval supremum. -/
def continuousRunningAbsSup (X : NNReal → Ω → ℝ) (T : NNReal) : Ω → ℝ≥0∞ :=
  fun ω ↦ ⨆ t : Set.Icc (0 : NNReal) T, ENNReal.ofReal |X t ω|

syntax:max "|" term "|*_" term : term

macro_rules
  | `(|$X|*_$T) => `(continuousRunningAbsSup $X $T)

-- Proof sketch: unfold `|X|*_T`; the statement is exactly its defining equation.
/-- Unfolding formula for the running supremum `|X|*_T`. -/
theorem continuousRunningAbsSup_apply (X : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    (|X|*_T) ω =
      ⨆ t : Set.Icc (0 : NNReal) T, ENNReal.ofReal |X t ω| :=
  rfl

section DoobLp

variable [mΩ : MeasurableSpace Ω]

variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {X : NNReal → Ω → ℝ}

/-- Helper for Exercise 21.4.1: the dyadic row `n` is sampled up to the deterministic cutoff
`⌈T⌉ 2^n`, which ensures that the terminal time `T` appears on the grid after truncation by
`min T`. -/
private def dyadicCutoff (T : NNReal) (n : ℕ) : ℕ :=
  Nat.ceil (T : ℝ) * 2 ^ n

/-- Helper for Exercise 21.4.1: the `k`-th dyadic sample time in the row of mesh `2^{-n}`,
truncated at `T`. -/
private def dyadicPointUpTo (T : NNReal) (n k : ℕ) : NNReal :=
  min T ((k : NNReal) / (2 : NNReal) ^ n)

/-- Helper for Exercise 21.4.1: the dyadic sample times stay inside the interval `[0, T]`. -/
private lemma dyadicPointUpTo_mem_Icc (T : NNReal) (n k : ℕ) :
    dyadicPointUpTo T n k ∈ Set.Icc (0 : NNReal) T := by
  -- Proof comment: the dyadic sample time is a minimum with `T`, so only the upper bound needs
  -- attention.
  refine Set.mem_Icc.mpr ⟨zero_le _, ?_⟩
  exact min_le_left _ _

/-- Helper for Exercise 21.4.1: along a fixed dyadic row, the sample times are monotone in the
grid index. -/
private lemma dyadicPointUpTo_mono (T : NNReal) (n : ℕ) :
    Monotone (dyadicPointUpTo T n) := by
  intro i j hij
  -- Proof comment: `k ↦ k / 2^n` is monotone, and taking `min T` preserves order.
  refine min_le_min le_rfl ?_
  have hij' : (i : NNReal) ≤ (j : NNReal) := by
    exact_mod_cast hij
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hij' (inv_nonneg.mpr (show 0 ≤ (2 : NNReal) ^ n by positivity))

/-- Helper for Exercise 21.4.1: the cutoff index samples the terminal time `T` exactly. -/
private lemma dyadicPointUpTo_cutoff (T : NNReal) (n : ℕ) :
    dyadicPointUpTo T n (dyadicCutoff T n) = T := by
  -- Proof comment: at the cutoff, the untruncated dyadic time is at least `⌈T⌉`, so the `min`
  -- collapses to `T`.
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

/-- Helper for Exercise 21.4.1: refining the dyadic mesh preserves the old sample points as the
even-indexed points of the next row. -/
private lemma dyadicPointUpTo_even (T : NNReal) (n k : ℕ) :
    dyadicPointUpTo T (n + 1) (2 * k) = dyadicPointUpTo T n k := by
  -- Proof comment: after coercing to `ℝ`, the dyadic-time identity is the elementary equality
  -- `(2 * k) / 2^(n + 1) = k / 2^n`.
  apply Subtype.ext
  have hratio :
      (((2 * k : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) = ((k : ℝ) / (2 : ℝ) ^ n) := by
    rw [Nat.cast_mul, pow_succ]
    have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by
      positivity
    field_simp [hpow_ne]
    ring
  simpa [dyadicPointUpTo] using congrArg (min (T : ℝ)) hratio

/-- Helper for Exercise 21.4.1: the right-dyadic approximation of `t` at mesh `2^{-n}`. -/
private def dyadicRightApprox (t : NNReal) (n : ℕ) : NNReal :=
  ((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : NNReal) / (2 : NNReal) ^ n

/-- Helper for Exercise 21.4.1: the dyadic right approximation stays to the right of the target
time. -/
private lemma le_dyadicRightApprox (t : NNReal) (n : ℕ) :
    t ≤ dyadicRightApprox t n := by
  -- Proof comment: `Nat.ceil` rounds the scaled time upward, so dividing back by `2^n` stays on
  -- or to the right of `t`.
  unfold dyadicRightApprox
  have hpow_pos : 0 < (2 : NNReal) ^ n := by positivity
  have hceil :
      (t : ℝ) * (2 : ℝ) ^ n ≤ (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) := by
    exact Nat.le_ceil _
  rw [le_div_iff₀ hpow_pos]
  exact_mod_cast hceil

/-- Helper for Exercise 21.4.1: the right-dyadic approximations converge back to `t`. -/
private lemma tendsto_dyadicRightApprox (t : NNReal) :
    Tendsto (dyadicRightApprox t) atTop (𝓝 t) := by
  -- Proof comment: this is the standard `ceil (t x) / x → t` limit with `x = 2^n`.
  refine (NNReal.tendsto_coe).mp ?_
  simpa [dyadicRightApprox] using
    (tendsto_nat_ceil_mul_div_atTop (a := (t : ℝ)) t.2).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Helper for Exercise 21.4.1: the right-dyadic approximation index is always inside the cutoff
range for the horizon `T`. -/
private lemma dyadicRightApprox_index_le_cutoff {t T : NNReal} (htT : t ≤ T) (n : ℕ) :
    Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) ≤ dyadicCutoff T n := by
  -- Proof comment: `t ≤ T ≤ ⌈T⌉`, so after scaling by `2^n` the ceil-index for `t` is bounded by
  -- the terminal cutoff index.
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

/-- Helper for Exercise 21.4.1: the deterministic dyadic samples inherit a discrete filtration from
the original continuous-time filtration. -/
private def dyadicSampleFiltration (ℱ : Filtration NNReal mΩ) (T : NNReal) (n : ℕ) :
    Filtration ℕ mΩ :=
  { seq := fun k ↦ ℱ (dyadicPointUpTo T n k)
    mono' := fun i j hij ↦ ℱ.mono ((dyadicPointUpTo_mono T n) hij)
    le' := fun k ↦ ℱ.le _ }

/-- Helper for Exercise 21.4.1: the finite dyadic index set is nonempty because it contains the
initial time `0`. -/
private lemma dyadicGridIndex_nonempty (T : NNReal) (n : ℕ) :
    (Finset.range (dyadicCutoff T n + 1)).Nonempty :=
  (Finset.nonempty_range_iff).2 (Nat.succ_ne_zero _)

/-- Helper for Exercise 21.4.1: the deterministic dyadic sample of `X` along the row of mesh
`2^{-n}`. -/
private def dyadicSampleProcess (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) : ℕ → Ω → ℝ :=
  fun k ω ↦ X (dyadicPointUpTo T n k) ω

/-- Helper for Exercise 21.4.1: the dyadic running maximum on the row of mesh `2^{-n}` up to the
terminal time `T`. -/
private def dyadicGridAbsMax (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    (Finset.range (dyadicCutoff T n + 1)).sup' (dyadicGridIndex_nonempty T n)
      (fun k ↦ |dyadicSampleProcess X T n k ω|)

/-- Helper for Exercise 21.4.1: deterministic dyadic sampling preserves the martingale or
nonnegative-submartingale alternative needed for the discrete Doob inequality. -/
private lemma dyadicSample_martingaleOrSubmartingale
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    (T : NNReal) (n : ℕ) :
    Martingale (dyadicSampleProcess X T n) (dyadicSampleFiltration ℱ T n) μ ∨
      Submartingale (dyadicSampleProcess X T n) (dyadicSampleFiltration ℱ T n) μ ∧
        0 ≤ dyadicSampleProcess X T n := by
  rcases hX with hX | ⟨hX, hX_nonneg⟩
  · left
    refine ⟨?_, ?_⟩
    · -- Proof comment: each sampled time uses the same filtration slice as in the original
      -- martingale.
      intro k
      simpa [dyadicSampleProcess, dyadicSampleFiltration] using
        hX.stronglyAdapted (dyadicPointUpTo T n k)
    · -- Proof comment: the conditional expectation identity transfers along the monotone
      -- deterministic time change.
      intro i j hij
      simpa [dyadicSampleProcess, dyadicSampleFiltration] using
        hX.2 (dyadicPointUpTo T n i) (dyadicPointUpTo T n j) ((dyadicPointUpTo_mono T n) hij)
  · right
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · -- Proof comment: each sampled coordinate is measurable with respect to the matching sampled
      -- filtration stage.
      intro k
      simpa [dyadicSampleProcess, dyadicSampleFiltration] using
        hX.stronglyAdapted (dyadicPointUpTo T n k)
    · -- Proof comment: the submartingale conditional-expectation inequality is stable under the
      -- deterministic monotone reindexing.
      intro i j hij
      simpa [dyadicSampleProcess, dyadicSampleFiltration] using
        hX.ae_le_condExp ((dyadicPointUpTo_mono T n) hij)
    · -- Proof comment: integrability is inherited termwise from the original submartingale.
      intro k
      simpa [dyadicSampleProcess] using hX.integrable (dyadicPointUpTo T n k)
    · -- Proof comment: nonnegativity is preserved pointwise under sampling.
      intro k ω
      simpa [dyadicSampleProcess] using hX_nonneg (dyadicPointUpTo T n k) ω

/-- Helper for Exercise 21.4.1: every dyadic sampled value contributing to the rowwise maximum is
already one of the values entering the continuous running supremum on `[0, T]`. -/
private lemma dyadicGridAbsMax_le_continuousRunningAbsSup
    (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal (dyadicGridAbsMax X T n ω) ≤ (|X|*_T) ω := by
  -- Proof comment: compare each finite-grid sample with the interval supremum and then take the
  -- finite supremum.
  let s := Finset.range (dyadicCutoff T n + 1)
  have hs : s.Nonempty := dyadicGridIndex_nonempty T n
  rcases Finset.exists_mem_eq_sup' (s := s) hs (fun k ↦ |dyadicSampleProcess X T n k ω|) with
    ⟨k, hk, hk_eq⟩
  have hsample :
      ENNReal.ofReal |dyadicSampleProcess X T n k ω| ≤ (|X|*_T) ω := by
    refine le_iSup_of_le ⟨dyadicPointUpTo T n k, dyadicPointUpTo_mem_Icc T n k⟩ ?_
    simp [dyadicSampleProcess]
  simpa [dyadicGridAbsMax, s, hk_eq] using hsample

/-- Helper for Exercise 21.4.1: every dyadic row maximum is measurable. -/
private lemma dyadicGridAbsMax_measurable
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    (T : NNReal) (n : ℕ) :
    Measurable (dyadicGridAbsMax X T n) := by
  -- Proof comment: each sampled coordinate is strongly measurable by the sampled
  -- martingale/submartingale package, and finite suprema preserve measurability.
  have hsample_sm : ∀ k, StronglyMeasurable (dyadicSampleProcess X T n k) := by
    intro k
    rcases dyadicSample_martingaleOrSubmartingale (X := X) (ℱ := ℱ) (μ := μ) hX T n with
      hXn | ⟨hXn, _⟩
    · exact (hXn.stronglyMeasurable k).mono ((dyadicSampleFiltration ℱ T n).le k)
    · exact (hXn.stronglyMeasurable k).mono ((dyadicSampleFiltration ℱ T n).le k)
  simpa [dyadicGridAbsMax] using
    (Finset.measurable_range_sup'' (n := dyadicCutoff T n) fun k hk ↦
      (hsample_sm k).measurable.abs)

/-- Helper for Exercise 21.4.1: the dyadic running maxima increase under refinement of the dyadic
grid. -/
private lemma dyadicGridAbsMax_mono (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) (ω : Ω) :
    dyadicGridAbsMax X T n ω ≤ dyadicGridAbsMax X T (n + 1) ω := by
  -- Proof comment: each coarse-grid sample reappears at an even index of the refined row, so the
  -- coarse finite supremum is bounded by the refined finite supremum.
  let s := Finset.range (dyadicCutoff T n + 1)
  have hs : s.Nonempty := dyadicGridIndex_nonempty T n
  have hcutoff_succ : dyadicCutoff T (n + 1) = 2 * dyadicCutoff T n := by
    unfold dyadicCutoff
    simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hbound :
      s.sup' hs (fun k ↦ |dyadicSampleProcess X T n k ω|) ≤ dyadicGridAbsMax X T (n + 1) ω := by
    refine Finset.sup'_le (H := hs) (f := fun k : ℕ ↦ |dyadicSampleProcess X T n k ω|) ?_
    intro k hk
    have hk_le : k ≤ dyadicCutoff T n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk' : 2 * k ∈ Finset.range (dyadicCutoff T (n + 1) + 1) := by
      refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
      calc
        2 * k ≤ 2 * dyadicCutoff T n := Nat.mul_le_mul_left 2 hk_le
        _ = dyadicCutoff T (n + 1) := hcutoff_succ.symm
    calc
      |dyadicSampleProcess X T n k ω| = |dyadicSampleProcess X T (n + 1) (2 * k) ω| := by
        simp [dyadicSampleProcess, dyadicPointUpTo_even]
      _ ≤
          (Finset.range (dyadicCutoff T (n + 1) + 1)).sup' (dyadicGridIndex_nonempty T (n + 1))
            (fun j ↦ |dyadicSampleProcess X T (n + 1) j ω|) := by
          exact Finset.le_sup' (f := fun j : ℕ ↦ |dyadicSampleProcess X T (n + 1) j ω|) hk'
  simpa [dyadicGridAbsMax, s] using hbound

/-- Helper for Exercise 21.4.1: right continuity at an interior witness time produces a dyadic row
whose sampled maximum still crosses the same strict threshold. -/
private lemma rightContinuousStrictThreshold_dyadicWitness
    (hX_rc : HasRightContinuousPaths X) {a : ℝ} {t T : NNReal} {ω : Ω}
    (ht_mem : t ∈ Set.Icc (0 : NNReal) T) (ht_ltT : t < T) (ha : a < |X t ω|) :
    ∃ n : ℕ, a < dyadicGridAbsMax X T n ω := by
  -- Route correction: the interior case should first move the strict witness along the
  -- right-dyadic approximants, and only then compare that sampled value with the rowwise maximum.
  have habs_cont :
      ContinuousWithinAt (fun s : NNReal ↦ |X s ω|) (Set.Ici t) t := by
    -- Proof comment: the sample path is right continuous, and absolute value preserves
    -- continuity.
    exact continuous_abs.continuousAt.comp_continuousWithinAt (hX_rc ω t)
  have hstrict_eventually : ∀ᶠ s in 𝓝[Set.Ici t] t, a < |X s ω| := by
    -- Proof comment: strict positivity over the threshold is open in the target variable.
    simpa [Set.mem_Ioi] using habs_cont (Ioi_mem_nhds ha)
  have happrox_mem : ∀ᶠ n in atTop, dyadicRightApprox t n ∈ Set.Ici t := by
    -- Proof comment: every right-dyadic approximant stays to the right of `t`.
    exact Eventually.of_forall (fun n ↦ le_dyadicRightApprox t n)
  have happroxWithin :
      Tendsto (dyadicRightApprox t) atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_dyadicRightApprox t)
      happrox_mem
  have hstrict_approx : ∀ᶠ n in atTop, a < |X (dyadicRightApprox t n) ω| := by
    -- Proof comment: the approximating dyadic times eventually stay inside the right-continuity
    -- neighborhood on which the strict inequality is preserved.
    exact happroxWithin hstrict_eventually
  have hltT_approx : ∀ᶠ n in atTop, dyadicRightApprox t n < T := by
    -- Proof comment: because `t < T` and the approximants converge to `t`, they are eventually
    -- still strictly below the terminal time.
    exact (tendsto_dyadicRightApprox t) (Iio_mem_nhds ht_ltT)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (hstrict_approx.and hltT_approx)
  let n : ℕ := n₀
  have hstrict_n : a < |X (dyadicRightApprox t n) ω| := (hn₀ n le_rfl).1
  have hltT_n : dyadicRightApprox t n < T := (hn₀ n le_rfl).2
  let k : ℕ := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)
  have hk : k ∈ Finset.range (dyadicCutoff T n + 1) := by
    -- Proof comment: the dyadic ceil index stays below the deterministic cutoff because the
    -- witness time lies in `[0, T]`.
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    simpa [k] using dyadicRightApprox_index_le_cutoff (t := t) (T := T) ht_mem.2 n
  have hpoint :
      dyadicPointUpTo T n k = dyadicRightApprox t n := by
    -- Proof comment: once the approximant is strictly below `T`, truncation by `min T` disappears.
    have happrox_le :
        ((k : NNReal) / (2 : NNReal) ^ n) ≤ T := by
      simpa [dyadicRightApprox, k] using (le_of_lt hltT_n)
    simp [dyadicPointUpTo, dyadicRightApprox, k, min_eq_right happrox_le]
  refine ⟨n, ?_⟩
  -- Proof comment: the chosen dyadic sample is one of the values entering the rowwise maximum.
  have hsample_le :
      |dyadicSampleProcess X T n k ω| ≤ dyadicGridAbsMax X T n ω := by
    simpa [dyadicGridAbsMax] using
      (Finset.le_sup' (s := Finset.range (dyadicCutoff T n + 1))
        (f := fun j : ℕ ↦ |dyadicSampleProcess X T n j ω|) hk)
  calc
    a < |X (dyadicRightApprox t n) ω| := hstrict_n
    _ = |dyadicSampleProcess X T n k ω| := by
      simp [dyadicSampleProcess, hpoint]
    _ ≤ dyadicGridAbsMax X T n ω := hsample_le

/-- Helper for Exercise 21.4.1: every strict-threshold event for the continuous running supremum
is the increasing union of the dyadic strict-threshold events. -/
private lemma strictThreshold_event_iUnion_dyadic
    (hX_rc : HasRightContinuousPaths X) {a : ℝ} (ha : 0 < a) (T : NNReal) :
    {ω | ENNReal.ofReal a < (|X|*_T) ω} =
      ⋃ n : ℕ, {ω | a < dyadicGridAbsMax X T n ω} := by
  -- Route correction: split the witness time into the endpoint case `t = T` and the interior case
  -- `t < T`; only the interior branch uses right continuity.
  ext ω
  constructor
  · intro hω
    change ENNReal.ofReal a < (|X|*_T) ω at hω
    rw [continuousRunningAbsSup_apply] at hω
    rcases lt_iSup_iff.mp hω with ⟨t, ht⟩
    have hstrict_t : a < |X t ω| := by
      exact (ENNReal.ofReal_lt_ofReal_iff').mp ht |>.1
    by_cases htT : (t : NNReal) = T
    · rw [Set.mem_iUnion]
      refine ⟨0, ?_⟩
      have hk : dyadicCutoff T 0 ∈ Finset.range (dyadicCutoff T 0 + 1) :=
        Finset.self_mem_range_succ (dyadicCutoff T 0)
      have hsample_le :
          |dyadicSampleProcess X T 0 (dyadicCutoff T 0) ω| ≤ dyadicGridAbsMax X T 0 ω := by
        simpa [dyadicGridAbsMax] using
          (Finset.le_sup' (s := Finset.range (dyadicCutoff T 0 + 1))
            (f := fun j : ℕ ↦ |dyadicSampleProcess X T 0 j ω|) hk)
      have hstrict_T : a < |X T ω| := by
        simpa [htT] using hstrict_t
      calc
        a < |X T ω| := hstrict_T
        _ = |dyadicSampleProcess X T 0 (dyadicCutoff T 0) ω| := by
          simp [dyadicSampleProcess, dyadicPointUpTo_cutoff]
        _ ≤ dyadicGridAbsMax X T 0 ω := hsample_le
    · have ht_ltT : (t : NNReal) < T := by
        exact lt_of_le_of_ne t.2.2 htT
      rw [Set.mem_iUnion]
      exact rightContinuousStrictThreshold_dyadicWitness (X := X) hX_rc t.2 ht_ltT hstrict_t
  · intro hω
    rw [Set.mem_iUnion] at hω
    rcases hω with ⟨n, hn⟩
    have hstrict_n :
        ENNReal.ofReal a < ENNReal.ofReal (dyadicGridAbsMax X T n ω) := by
      exact (ENNReal.ofReal_lt_ofReal_iff').2 ⟨hn, lt_trans ha hn⟩
    exact lt_of_lt_of_le hstrict_n (dyadicGridAbsMax_le_continuousRunningAbsSup X T n ω)

/-- Helper for Exercise 21.4.1: the continuous running supremum is the monotone supremum of the
dyadic running maxima. -/
private lemma continuousRunningAbsSup_eq_iSup_dyadicGrid
    (hX_rc : HasRightContinuousPaths X) (T : NNReal) (ω : Ω) :
    (|X|*_T) ω = ⨆ n : ℕ, ENNReal.ofReal (dyadicGridAbsMax X T n ω) := by
  -- Proof comment: the dyadic maxima are always bounded by the continuous running supremum, and
  -- the strict-threshold union shows that every positive level below the latter is attained by
  -- some dyadic row.
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_nnreal_lt ?_
    intro r hrpos hrlt
    have hω :
        ω ∈ {ω | ENNReal.ofReal (r : ℝ) < (|X|*_T) ω} := by
      simpa using hrlt
    rw [strictThreshold_event_iUnion_dyadic (X := X) hX_rc (a := (r : ℝ))
      (show 0 < (r : ℝ) by exact_mod_cast hrpos) T] at hω
    rw [Set.mem_iUnion] at hω
    rcases hω with ⟨n, hn⟩
    have hr_le :
        (r : ℝ≥0∞) ≤ ENNReal.ofReal (dyadicGridAbsMax X T n ω) := by
      exact le_of_lt (by simpa using hn)
    exact le_trans hr_le (le_iSup (fun n : ℕ ↦ ENNReal.ofReal (dyadicGridAbsMax X T n ω)) n)
  · refine iSup_le fun n ↦ ?_
    exact dyadicGridAbsMax_le_continuousRunningAbsSup X T n ω

/-- Helper for Exercise 21.4.1: the discrete running maximum of the sampled dyadic row is exactly
the local dyadic-grid maximum. -/
private lemma dyadicSampleAbsMaxUpTo_eq_dyadicGridAbsMax
    (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) (ω : Ω) :
    (Finset.range (dyadicCutoff T n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ |dyadicSampleProcess X T n k ω|) =
      dyadicGridAbsMax X T n ω := by
  -- Proof comment: both sides are the same finite supremum over the dyadic row, written with the
  -- Chapter 11 owner normalization on the left and the local canonical wrapper on the right.
  simp [dyadicGridAbsMax]

/-- Helper for Exercise 21.4.1: crossing the dyadic row maximum is equivalent to crossing one
sample on that row. -/
private lemma threshold_le_dyadicGridAbsMax_iff
    (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) (ω : Ω) {threshold : ℝ} :
    threshold ≤ dyadicGridAbsMax X T n ω ↔
      ∃ k ≤ dyadicCutoff T n, threshold ≤ |dyadicSampleProcess X T n k ω| := by
  constructor
  · intro h
    let s := Finset.range (dyadicCutoff T n + 1)
    have hs : s.Nonempty := dyadicGridIndex_nonempty T n
    rcases Finset.exists_mem_eq_sup' (s := s) hs (fun k ↦ |dyadicSampleProcess X T n k ω|) with
      ⟨k, hk, hk_eq⟩
    have h' : threshold ≤ s.sup' hs (fun k ↦ |dyadicSampleProcess X T n k ω|) := by
      simpa [dyadicGridAbsMax, s] using h
    refine ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), ?_⟩
    rwa [hk_eq] at h'
  · rintro ⟨k, hk, hk_threshold⟩
    have hk_mem : k ∈ Finset.range (dyadicCutoff T n + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
    calc
      threshold ≤ |dyadicSampleProcess X T n k ω| := hk_threshold
      _ ≤ dyadicGridAbsMax X T n ω := by
            simpa [dyadicGridAbsMax] using
              (Finset.le_sup' (s := Finset.range (dyadicCutoff T n + 1))
                (f := fun j : ℕ ↦ |dyadicSampleProcess X T n j ω|) hk_mem)

/-- Helper for Exercise 21.4.1: the Chapter 11 discrete Doob tail theorem transfers verbatim to a
single dyadic row. -/
private lemma dyadicRow_doobLp_tail_bound
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    {p threshold : ℝ} (hp : 1 ≤ p) (hthreshold : 0 < threshold)
    (T : NNReal) (n : ℕ) :
    ENNReal.ofReal (Real.rpow threshold p) *
        μ {ω | threshold ≤ dyadicGridAbsMax X T n ω} ≤
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ := by
  -- Proof comment: specialize the owner theorem to the sampled row and rewrite only the rowwise
  -- maximum and the terminal sample back to the local continuous-time objects.
  have hset_eq :
      {ω | threshold ≤ dyadicGridAbsMax X T n ω} =
        {ω | ∃ b ≤ dyadicCutoff T n, threshold ≤ |dyadicSampleProcess X T n b ω|} := by
    ext ω
    simpa using threshold_le_dyadicGridAbsMax_iff X T n ω (threshold := threshold)
  rw [hset_eq]
  simpa [dyadicSampleProcess, dyadicPointUpTo_cutoff] using
    (doobLp_tail_bound
      (X := dyadicSampleProcess X T n)
      (ℱ := dyadicSampleFiltration ℱ T n)
      (μ := μ)
      (dyadicSample_martingaleOrSubmartingale
        (X := X) (ℱ := ℱ) (μ := μ) hX T n)
      hp hthreshold (dyadicCutoff T n))

/-- Helper for Exercise 21.4.1: along each sample point, the dyadic row maxima form a monotone
sequence. -/
private lemma dyadicGridAbsMax_monotone
    (X : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    Monotone fun n ↦ dyadicGridAbsMax X T n ω := by
  intro n m hnm
  induction hnm with
  | refl =>
      exact le_rfl
  | @step m hnm ih =>
      exact ih.trans (dyadicGridAbsMax_mono X T m ω)

/-- Helper for Exercise 21.4.1: every dyadic row maximum is nonnegative because it is a finite
supremum of absolute values. -/
private lemma dyadicGridAbsMax_nonneg
    (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) (ω : Ω) :
    0 ≤ dyadicGridAbsMax X T n ω := by
  let s := Finset.range (dyadicCutoff T n + 1)
  have hs : s.Nonempty := dyadicGridIndex_nonempty T n
  rcases Finset.exists_mem_eq_sup' (s := s) hs (fun k ↦ |dyadicSampleProcess X T n k ω|) with
    ⟨k, hk, hk_eq⟩
  rw [dyadicGridAbsMax, hk_eq]
  exact abs_nonneg _

/-- Helper for Exercise 21.4.1: the Chapter 11 discrete Doob moment theorem transfers verbatim to
a single dyadic row. -/
private lemma dyadicRow_doobLp_runningMaxMoment_le
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    {p : ℝ} (hp : 1 < p) (T : NNReal) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.rpow (dyadicGridAbsMax X T n ω) p) ∂μ ≤
      ENNReal.ofReal (Real.rpow (p / (p - 1)) p) *
        ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ := by
  -- Proof comment: as in the tail bound, the owner theorem already has the right inequality once
  -- the discrete maximum and the terminal sample are rewritten through the dyadic row API.
  simpa [dyadicSampleAbsMaxUpTo_eq_dyadicGridAbsMax, dyadicSampleProcess, dyadicPointUpTo_cutoff]
    using
      (doobLp_runningMaxMoment_le
        (X := dyadicSampleProcess X T n)
        (ℱ := dyadicSampleFiltration ℱ T n)
        (μ := μ)
        (dyadicSample_martingaleOrSubmartingale
          (X := X) (ℱ := ℱ) (μ := μ) hX T n)
        hp (dyadicCutoff T n))

-- Proof sketch: stop the process at the first time its absolute value reaches `threshold`, reduce
-- to bounded stopping times, and apply optional sampling to the nonnegative submartingale
-- `t ↦ |X t|^p`; right continuity identifies the stopped event with the hitting event of the
-- running supremum.
/-- Exercise 21.4.1 (1): on a finite measure space, for a martingale or nonnegative submartingale
with right-continuous paths, Doob's `L^p` tail estimate controls the event `{|X|*_T ≥ λ}` by the
terminal `p`-th moment. -/
theorem doobLp_tail_bound_rightContinuous
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    (hX_rc : HasRightContinuousPaths X)
    {p threshold : ℝ} (hp : 1 ≤ p) (hthreshold : 0 < threshold) (T : NNReal) :
    ENNReal.ofReal (Real.rpow threshold p) *
        μ {ω | ENNReal.ofReal threshold ≤ (|X|*_T) ω} ≤
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ := by
  let A : Set Ω := {ω | ENNReal.ofReal threshold ≤ (|X|*_T) ω}
  let I : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  -- Route correction: instead of a limit in the threshold parameter, use strict approximations
  -- inside `ENNReal.mul_le_of_forall_lt` and select one dyadic row already carrying enough mass.
  suffices ENNReal.ofReal (Real.rpow threshold p) * μ A ≤ I by
    simpa [A, I] using this
  refine ENNReal.mul_le_of_forall_lt ?_
  intro a' ha' b' hb'
  have ha'_ne_top : a' ≠ ∞ := ne_of_lt (lt_of_lt_of_le ha' le_top)
  have ha'_real : a'.toReal < Real.rpow threshold p := by
    simpa [ENNReal.toReal_ofReal (Real.rpow_nonneg hthreshold.le p)] using
      (ENNReal.toReal_lt_toReal ha'_ne_top (by simp)).2 ha'
  let s : ℝ := a'.toReal ^ (1 / p)
  have hs_lt_threshold : s < threshold := by
    simpa [s, one_div] using
      (Real.rpow_inv_lt_iff_of_pos ENNReal.toReal_nonneg hthreshold.le hp_pos).2 ha'_real
  let r : ℝ := (s + threshold) / 2
  have hs_nonneg : 0 ≤ s := by
    positivity
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_lt_threshold : r < threshold := by
    dsimp [r]
    linarith
  have ha'_lt_rpow_real : a'.toReal < Real.rpow r p := by
    have hs_lt_r : s < r := by
      dsimp [r]
      linarith
    calc
      a'.toReal = Real.rpow s p := by
        symm
        simpa [s, one_div] using
          (Real.rpow_inv_rpow ENNReal.toReal_nonneg hp_pos.ne')
      _ < Real.rpow r p := Real.rpow_lt_rpow hs_nonneg hs_lt_r hp_pos
  have ha'_lt_rpow : a' < ENNReal.ofReal (Real.rpow r p) := by
    have ha'_lt_rpow_toReal :
        a'.toReal < (ENNReal.ofReal (Real.rpow r p)).toReal := by
      simpa [ENNReal.toReal_ofReal (Real.rpow_nonneg hr_pos.le p)] using ha'_lt_rpow_real
    exact (ENNReal.toReal_lt_toReal ha'_ne_top (by simp)).1 ha'_lt_rpow_toReal
  let Er : ℕ → Set Ω := fun n ↦ {ω | r < dyadicGridAbsMax X T n ω}
  have hEr_mono : Monotone Er := by
    intro n m hnm ω hω
    exact lt_of_lt_of_le hω (dyadicGridAbsMax_monotone X T ω hnm)
  have hmeasure_iUnion : μ (⋃ n : ℕ, Er n) = ⨆ n : ℕ, μ (Er n) := by
    rw [hEr_mono.measure_iUnion]
  have hA_subset_strict : A ⊆ {ω | ENNReal.ofReal r < (|X|*_T) ω} := by
    intro ω hω
    have hr_lt :
        ENNReal.ofReal r < ENNReal.ofReal threshold := by
      simpa using (ENNReal.ofReal_lt_ofReal_iff hthreshold).2 hr_lt_threshold
    exact lt_of_lt_of_le hr_lt hω
  have hb'_lt_iSup : b' < ⨆ n : ℕ, μ (Er n) := by
    have hstrict_union : b' < μ (⋃ n : ℕ, Er n) := by
      have hstrict :
          b' < μ {ω | ENNReal.ofReal r < (|X|*_T) ω} := by
        exact lt_of_lt_of_le hb' (measure_mono hA_subset_strict)
      rw [strictThreshold_event_iUnion_dyadic (X := X) hX_rc hr_pos T] at hstrict
      simpa [Er] using hstrict
    rw [hmeasure_iUnion] at hstrict_union
    exact hstrict_union
  rcases lt_iSup_iff.mp hb'_lt_iSup with ⟨n, hb'_n⟩
  have hb'_le_closed :
      b' ≤ μ {ω | r ≤ dyadicGridAbsMax X T n ω} := by
    have hsubset : Er n ⊆ {ω | r ≤ dyadicGridAbsMax X T n ω} := by
      intro ω hω
      simpa [Er] using (le_of_lt hω : r ≤ dyadicGridAbsMax X T n ω)
    exact le_of_lt (lt_of_lt_of_le hb'_n (measure_mono hsubset))
  calc
    a' * b' ≤ ENNReal.ofReal (Real.rpow r p) *
        μ {ω | r ≤ dyadicGridAbsMax X T n ω} := by
          exact mul_le_mul' ha'_lt_rpow.le hb'_le_closed
    _ ≤ I := by
          simpa [I] using
            (dyadicRow_doobLp_tail_bound
              (X := X) (ℱ := ℱ) (μ := μ) hX (p := p) (threshold := r) hp hr_pos T n)

end DoobLp

section RunningSupMoment

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Helper for Exercise 21.4.1: the terminal absolute value at time `T` is one of the values
entering the running supremum on `[0, T]`. -/
lemma terminalAbs_le_continuousRunningAbsSup
    (X : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    ENNReal.ofReal |X T ω| ≤ (|X|*_T) ω := by
  -- Proof comment: evaluate the interval supremum at the endpoint `T`.
  refine le_iSup_of_le ⟨T, Set.mem_Icc.mpr ⟨zero_le _, le_rfl⟩⟩ ?_
  rfl

-- Proof sketch: for every sample point `ω`, the terminal value `|X T ω|` is one of the values
-- whose supremum defines `|X|*_T ω`, so monotonicity of `x ↦ x^p` on `ℝ≥0∞` for `p ≥ 0` gives
-- `|X T ω|^p ≤ (|X|*_T ω)^p`; integrate this pointwise inequality.
/-- Exercise 21.4.1 (2): for every nonnegative exponent `p`, the terminal `p`-th moment is bounded
by the `p`-th moment of `|X|*_T`. This is the left inequality in clause `(ii)`, stated with the
minimal exponent range used by its pointwise proof. -/
theorem terminalMoment_le_continuousRunningAbsSupMoment
    {p : ℝ} (hp : 0 ≤ p) (X : NNReal → Ω → ℝ) (T : NNReal) :
    ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ ≤
      ∫⁻ ω, ((|X|*_T) ω) ^ p ∂μ := by
  -- Proof comment: integrate the pointwise comparison between the terminal value and the running
  -- supremum.
  refine MeasureTheory.lintegral_mono fun ω ↦ ?_
  calc
    ENNReal.ofReal (Real.rpow |X T ω| p)
        = (ENNReal.ofReal |X T ω|) ^ p := by
            simpa using (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (X T ω)) hp).symm
    _ ≤ ((|X|*_T) ω) ^ p := by
      exact ENNReal.rpow_le_rpow (terminalAbs_le_continuousRunningAbsSup X T ω) hp

end RunningSupMoment

section DoobLp

variable [mΩ : MeasurableSpace Ω]

variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {X : NNReal → Ω → ℝ}

-- Proof sketch: integrate the tail estimate from clause `(1)` against `p λ^(p-1)`, use the layer-
-- cake representation of the `p`-th moment of `|X|*_T`, and optimize the resulting Hölder bound to
-- obtain the classical constant `(p / (p - 1))^p`.
/-- Exercise 21.4.1 (3): on a finite measure space, for `p > 1`, the `p`-th moment of `|X|*_T` is
bounded by the classical Doob constant `(p / (p - 1))^p` times the terminal `p`-th moment. This
is the right inequality in clause `(ii)`. -/
theorem continuousRunningAbsSupMoment_le_doobConstant_mul_terminalMoment
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    (hX_rc : HasRightContinuousPaths X)
    {p : ℝ} (hp : 1 < p) (T : NNReal) :
    ∫⁻ ω, ((|X|*_T) ω) ^ p ∂μ ≤
      ENNReal.ofReal (Real.rpow (p / (p - 1)) p) *
        ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp0_le : 0 ≤ p := le_of_lt hp0
  have hpointwise :
      (fun ω ↦ ((|X|*_T) ω) ^ p) =
        fun ω ↦ ⨆ n : ℕ, ENNReal.ofReal (Real.rpow (dyadicGridAbsMax X T n ω) p) := by
    funext ω
    rw [continuousRunningAbsSup_eq_iSup_dyadicGrid (X := X) hX_rc T ω]
    calc
      (⨆ n : ℕ, ENNReal.ofReal (dyadicGridAbsMax X T n ω)) ^ p =
          ⨆ n : ℕ, (ENNReal.ofReal (dyadicGridAbsMax X T n ω)) ^ p := by
            exact
              (ENNReal.orderIsoRpow p (lt_trans zero_lt_one hp)).map_iSup
                (fun n : ℕ ↦ ENNReal.ofReal (dyadicGridAbsMax X T n ω))
      _ = ⨆ n : ℕ, ENNReal.ofReal (Real.rpow (dyadicGridAbsMax X T n ω) p) := by
            congr with n
            exact ENNReal.ofReal_rpow_of_nonneg
              (dyadicGridAbsMax_nonneg X T n ω) hp0_le
  have hf_meas :
      ∀ n, AEMeasurable (fun ω ↦ ENNReal.ofReal (Real.rpow (dyadicGridAbsMax X T n ω) p)) μ := by
    intro n
    have hmeas :
        Measurable (fun ω ↦ Real.rpow (dyadicGridAbsMax X T n ω) p) :=
      (Real.continuous_rpow_const hp0_le).measurable.comp
        (dyadicGridAbsMax_measurable (X := X) (ℱ := ℱ) (μ := μ) hX T n)
    exact hmeas.ennreal_ofReal.aemeasurable
  have hf_mono :
      ∀ᵐ ω ∂μ, Monotone fun n ↦ ENNReal.ofReal (Real.rpow (dyadicGridAbsMax X T n ω) p) := by
    refine Filter.Eventually.of_forall fun ω n m hnm ↦ ?_
    exact ENNReal.ofReal_le_ofReal <|
      Real.rpow_le_rpow
        (dyadicGridAbsMax_nonneg X T n ω)
        (dyadicGridAbsMax_monotone X T ω hnm) hp0_le
  rw [hpointwise, MeasureTheory.lintegral_iSup' hf_meas hf_mono]
  refine iSup_le fun n ↦ ?_
  exact dyadicRow_doobLp_runningMaxMoment_le
    (X := X) (ℱ := ℱ) (μ := μ) hX hp T n

end DoobLp

section Counterexample

local notation "unitIntervalVolume" => (volume.restrict (Set.Icc (0 : ℝ) 1) : Measure ℝ)

/-- Helper for Exercise 21.4.1: the restricted Lebesgue measure on `[0, 1]` is a probability
measure. -/
private lemma unitIntervalVolume_isProbability :
    IsProbabilityMeasure unitIntervalVolume := by
  -- Proof comment: the restricted volume of `[0, 1]` evaluates to `1` on the full space.
  refine ⟨?_⟩
  change (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1
  rw [Measure.restrict_apply₀]
  · simp [Real.volume_Icc]
  · measurability

/-- Helper for Exercise 21.4.1: the spike process places a unit mass at the unique time equal to
the sample point. -/
private def spikeProcess : NNReal → ℝ → ℝ :=
  fun t ↦ Set.indicator ({(t : ℝ)} : Set ℝ) (fun _ ↦ (1 : ℝ))

/-- Helper for Exercise 21.4.1: each time slice of the spike process is measurable. -/
private lemma spikeProcess_stronglyMeasurable (t : NNReal) :
    StronglyMeasurable (spikeProcess t) := by
  -- Proof comment: the spike slice is an indicator of a measurable singleton with constant value
  -- `1`.
  simpa [spikeProcess] using
    (stronglyMeasurable_const.indicator (MeasurableSet.singleton (t : ℝ)))

/-- Helper for Exercise 21.4.1: each spike slice is integrable because it is a bounded indicator on
the finite-measure space `[0, 1]`. -/
private lemma spikeProcess_integrable (t : NNReal) :
    Integrable (spikeProcess t) unitIntervalVolume := by
  -- Proof comment: each spike slice is a constant integrable function cut down by a measurable
  -- singleton.
  letI : IsProbabilityMeasure unitIntervalVolume := unitIntervalVolume_isProbability
  have hconst : Integrable (fun _ : ℝ ↦ (1 : ℝ)) unitIntervalVolume := by
    simpa using (integrable_const (c := (1 : ℝ)))
  simpa [spikeProcess] using hconst.indicator (MeasurableSet.singleton (t : ℝ))

/-- Helper for Exercise 21.4.1: every spike slice vanishes almost everywhere under the atomless
measure on `[0, 1]`. -/
private lemma spikeProcess_ae_eq_zero (t : NNReal) :
    spikeProcess t =ᵐ[unitIntervalVolume] 0 := by
  -- Proof comment: the spike lives on a singleton, and singletons have zero restricted Lebesgue
  -- measure.
  have hsingleton : unitIntervalVolume ({(t : ℝ)} : Set ℝ) = 0 := by
    have hsubs : ({(t : ℝ)} : Set ℝ).Subsingleton := by
      intro x hx y hy
      simpa using hx.trans hy.symm
    exact hsubs.measure_zero unitIntervalVolume
  simpa [spikeProcess] using
    (indicator_meas_zero (μ := unitIntervalVolume) (f := fun _ : ℝ ↦ (1 : ℝ)) hsingleton)

/-- Helper for Exercise 21.4.1: under the full filtration, the spike process is a martingale
because every time slice is almost surely zero. -/
private lemma spikeProcess_martingale :
    Martingale (m0 := Real.measureSpace.toMeasurableSpace) spikeProcess
      (⊤ : Filtration NNReal Real.measureSpace.toMeasurableSpace) unitIntervalVolume := by
  -- Proof comment: under the full filtration, conditional expectation fixes each measurable slice,
  -- and all slices are almost surely equal because they are all almost surely zero.
  refine ⟨?_, ?_⟩
  · intro t
    simpa using spikeProcess_stronglyMeasurable t
  · intro i j hij
    rw [condExp_of_stronglyMeasurable
      ((⊤ : Filtration NNReal Real.measureSpace.toMeasurableSpace).le i)
      (by simpa using spikeProcess_stronglyMeasurable j)
      (spikeProcess_integrable j)]
    exact (spikeProcess_ae_eq_zero j).trans (spikeProcess_ae_eq_zero i).symm

/-- Helper for Exercise 21.4.1: on the support interval `[0, 1]`, the running supremum of the
spike process up to time `1` is at least `1`, hence exceeds the threshold `1 / 2`. -/
private lemma half_le_continuousRunningAbsSup_spikeProcess
    {ω : ℝ} (hω : ω ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ (|spikeProcess|*_(1 : NNReal)) ω := by
  -- Proof comment: the path has a unit spike exactly at time `t = ω`, which is available because
  -- `ω ∈ [0, 1]`.
  let tω : NNReal := ⟨ω, hω.1⟩
  have htω : tω ∈ Set.Icc (0 : NNReal) (1 : NNReal) := by
    refine Set.mem_Icc.mpr ⟨zero_le _, ?_⟩
    exact_mod_cast hω.2
  have hvalue : spikeProcess tω ω = 1 := by
    simp [spikeProcess, tω]
  calc
    ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal |spikeProcess tω ω| := by
      rw [hvalue]
      norm_num
    _ ≤ (|spikeProcess|*_(1 : NNReal)) ω := by
      refine le_iSup_of_le ⟨tω, htω⟩ ?_
      rfl

/-- Helper for Exercise 21.4.1: the threshold event for the spike process contains the full support
interval `[0, 1]`. -/
private lemma unitInterval_subset_spikeEvent :
    Set.Icc (0 : ℝ) 1 ⊆ {ω | ENNReal.ofReal (1 / 2 : ℝ) ≤ (|spikeProcess|*_(1 : NNReal)) ω} := by
  -- Proof comment: every point of `[0, 1]` witnesses its own spike time.
  intro ω hω
  exact half_le_continuousRunningAbsSup_spikeProcess hω

/-- Helper for Exercise 21.4.1: the terminal `L¹` moment at time `1` vanishes for the spike
process because the terminal spike occurs on a singleton. -/
private lemma spikeProcess_terminalMoment_eq_zero :
    ∫⁻ ω, ENNReal.ofReal (Real.rpow |spikeProcess 1 ω| (1 : ℝ)) ∂unitIntervalVolume = 0 := by
  -- Proof comment: the terminal slice is almost everywhere zero, so its `L¹` moment vanishes.
  have hzero :
      (fun ω ↦ ENNReal.ofReal (Real.rpow |spikeProcess 1 ω| (1 : ℝ))) =ᵐ[unitIntervalVolume] 0 := by
    filter_upwards [spikeProcess_ae_eq_zero (1 : NNReal)] with ω hω
    simp [hω]
  exact MeasureTheory.lintegral_eq_zero_of_ae_eq_zero hzero

/-- Helper for Exercise 21.4.1: the spike process is not right continuous at the sample point
`ω = 0` and time `t = 0`. -/
private lemma spikeProcess_not_rightContinuous :
    ¬ HasRightContinuousPaths spikeProcess := by
  intro hrc
  have hcont := hrc 0 0
  rw [Metric.continuousWithinAt_iff] at hcont
  -- Proof comment: right continuity at `0` would force the path to stay within `1 / 2` of the
  -- value `1` on a small right-neighborhood of `0`.
  rcases hcont (1 / 2) (by norm_num) with ⟨δ, hδ_pos, hδ⟩
  let x : NNReal := ⟨δ / 2, by positivity⟩
  have hx_mem : x ∈ Set.Ici (0 : NNReal) := by
    exact show 0 ≤ x from zero_le _
  have hx_dist : dist x (0 : NNReal) < δ := by
    rw [NNReal.dist_eq]
    change |((x : NNReal) : ℝ) - 0| < δ
    rw [show ((x : NNReal) : ℝ) = δ / 2 by rfl, sub_zero,
      abs_of_nonneg (by positivity)]
    exact half_lt_self hδ_pos
  have hx_val : spikeProcess x 0 = 0 := by
    have hx_ne : ((x : NNReal) : ℝ) ≠ 0 := by
      rw [show ((x : NNReal) : ℝ) = δ / 2 by rfl]
      positivity
    simp [spikeProcess, hx_ne]
  have hzero_val : spikeProcess 0 0 = 1 := by
    simp [spikeProcess]
  have hclose : dist (spikeProcess x 0) (spikeProcess 0 0) < 1 / 2 := hδ hx_mem hx_dist
  rw [hx_val, hzero_val, Real.dist_eq] at hclose
  norm_num at hclose

end Counterexample

section LiftedCounterexample

local notation "unitIntervalVolume" => (volume.restrict (Set.Icc (0 : ℝ) 1) : Measure ℝ)

/-- Helper for Exercise 21.4.1: the lifted sample space places the spike counterexample in the
ambient universe `u`. -/
private abbrev LiftedSpikeSpace : Type u := ULift.{u} ℝ

/-- Helper for Exercise 21.4.1: push the unit-interval probability measure forward along
`ULift.up`. -/
private def liftedUnitIntervalVolume : Measure LiftedSpikeSpace :=
  Measure.map ULift.up unitIntervalVolume

/-- Helper for Exercise 21.4.1: the lifted spike process is the base spike process composed with
`ULift.down`. -/
private def liftedSpikeProcess : NNReal → LiftedSpikeSpace → ℝ :=
  fun t ω ↦ spikeProcess t ω.down

/-- Helper for Exercise 21.4.1: the lifted unit-interval measure is still a probability measure. -/
private lemma liftedUnitIntervalVolume_isProbability :
    IsProbabilityMeasure liftedUnitIntervalVolume := by
  -- Proof comment: the pushforward of a probability measure along a measurable equivalence is
  -- again a probability measure.
  refine ⟨?_⟩
  change Measure.map ULift.up unitIntervalVolume Set.univ = 1
  rw [Measure.map_apply measurable_up]
  · change unitIntervalVolume Set.univ = 1
    rw [Measure.restrict_apply₀]
    · simp [Real.volume_Icc]
    · measurability
  · measurability

/-- Helper for Exercise 21.4.1: each lifted spike slice is strongly measurable. -/
private lemma liftedSpikeProcess_stronglyMeasurable (t : NNReal) :
    StronglyMeasurable (liftedSpikeProcess t) := by
  -- Proof comment: compose the measurable base slice with `ULift.down`.
  simpa [liftedSpikeProcess] using
    (spikeProcess_stronglyMeasurable t).comp_measurable measurable_down

/-- Helper for Exercise 21.4.1: each lifted spike slice is integrable. -/
private lemma liftedSpikeProcess_integrable (t : NNReal) :
    Integrable (liftedSpikeProcess t) liftedUnitIntervalVolume := by
  -- Proof comment: the lifted slice is still a bounded indicator of a measurable singleton-like
  -- fiber under `ULift.down`.
  letI : IsProbabilityMeasure liftedUnitIntervalVolume := liftedUnitIntervalVolume_isProbability
  have hconst : Integrable (fun _ : LiftedSpikeSpace ↦ (1 : ℝ)) liftedUnitIntervalVolume := by
    simpa using (integrable_const (c := (1 : ℝ)))
  have hset : MeasurableSet (ULift.down ⁻¹' ({(t : ℝ)} : Set ℝ)) := by
    exact measurable_down (measurableSet_singleton (t : ℝ))
  simpa [liftedSpikeProcess, spikeProcess] using hconst.indicator hset

/-- Helper for Exercise 21.4.1: every lifted spike slice is still almost everywhere zero. -/
private lemma liftedSpikeProcess_ae_eq_zero (t : NNReal) :
    liftedSpikeProcess t =ᵐ[liftedUnitIntervalVolume] 0 := by
  -- Proof comment: rewrite the pushed-forward law as a map along `ULift.up` and pull the base
  -- almost-everywhere-zero statement forward.
  rw [Filter.EventuallyEq, liftedUnitIntervalVolume, MeasureTheory.ae_map_iff
    measurable_up.aemeasurable]
  · simpa [liftedSpikeProcess]
      using (spikeProcess_ae_eq_zero t : spikeProcess t =ᵐ[unitIntervalVolume] 0)
  · exact measurableSet_eq_fun (liftedSpikeProcess_stronglyMeasurable t).measurable measurable_const

/-- Helper for Exercise 21.4.1: the lifted spike process is a martingale for the full filtration.
-/
private lemma liftedSpikeProcess_martingale :
    Martingale (m0 := inferInstance) liftedSpikeProcess
      (⊤ : Filtration NNReal (inferInstance : MeasurableSpace LiftedSpikeSpace))
      liftedUnitIntervalVolume := by
  -- Proof comment: under the full filtration, the lifted slices are measurable and almost surely
  -- equal because they are all almost surely zero.
  letI : IsProbabilityMeasure liftedUnitIntervalVolume := liftedUnitIntervalVolume_isProbability
  refine ⟨?_, ?_⟩
  · intro t
    simpa using liftedSpikeProcess_stronglyMeasurable t
  · intro i j hij
    rw [condExp_of_stronglyMeasurable
      ((⊤ : Filtration NNReal (inferInstance : MeasurableSpace LiftedSpikeSpace)).le i)
      (by simpa using liftedSpikeProcess_stronglyMeasurable j)
      (liftedSpikeProcess_integrable j)]
    exact (liftedSpikeProcess_ae_eq_zero j).trans (liftedSpikeProcess_ae_eq_zero i).symm

/-- Helper for Exercise 21.4.1: on the lifted support points `ULift.up ω` with `ω ∈ [0,1]`, the
running supremum still exceeds `1 / 2`. -/
private lemma half_le_continuousRunningAbsSup_liftedSpikeProcess
    {ω : ℝ} (hω : ω ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ (|liftedSpikeProcess|*_(1 : NNReal)) (ULift.up ω) := by
  -- Proof comment: evaluate the lifted process at `ULift.up ω`; it is definitionally the base
  -- spike path at `ω`.
  simpa [liftedSpikeProcess, continuousRunningAbsSup_apply] using
    half_le_continuousRunningAbsSup_spikeProcess hω

/-- Helper for Exercise 21.4.1: the lifted half-threshold event at time `1`. -/
private def liftedSpikeHalfEvent : Set LiftedSpikeSpace :=
  {ω | ENNReal.ofReal (1 / 2 : ℝ) ≤ (continuousRunningAbsSup liftedSpikeProcess (1 : NNReal)) ω}

/-- Helper for Exercise 21.4.1: the lifted threshold event has full mass at least `1`. -/
private lemma liftedSpikeEvent_measure_ge_one :
    (1 : ENNReal) ≤ liftedUnitIntervalVolume liftedSpikeHalfEvent := by
  let supportSet : Set LiftedSpikeSpace := ULift.down ⁻¹' Set.Icc (0 : ℝ) 1
  have hsupport_subset : supportSet ⊆ liftedSpikeHalfEvent := by
    intro ω hω
    simpa [supportSet, liftedSpikeHalfEvent] using
      half_le_continuousRunningAbsSup_liftedSpikeProcess (ω := ω.down) hω
  have hsupport_meas : MeasurableSet supportSet := by
    exact measurable_down measurableSet_Icc
  have hsupport_measure : liftedUnitIntervalVolume supportSet = 1 := by
    rw [liftedUnitIntervalVolume, Measure.map_apply measurable_up hsupport_meas]
    change unitIntervalVolume (Set.Icc (0 : ℝ) 1) = 1
    rw [Measure.restrict_apply₀]
    · simp [Real.volume_Icc]
    · measurability
  calc
    (1 : ENNReal) = liftedUnitIntervalVolume supportSet := hsupport_measure.symm
    _ ≤ liftedUnitIntervalVolume liftedSpikeHalfEvent := measure_mono hsupport_subset

/-- Helper for Exercise 21.4.1: the lifted terminal `L¹` moment still vanishes. -/
private lemma liftedSpikeProcess_terminalMoment_eq_zero :
    ∫⁻ ω, ENNReal.ofReal (Real.rpow |liftedSpikeProcess 1 ω| (1 : ℝ))
      ∂liftedUnitIntervalVolume = 0 := by
  -- Proof comment: the lifted terminal slice is still almost everywhere zero, so its `L¹`
  -- moment vanishes exactly as in the base-space argument.
  have hzero :
      (fun ω ↦ ENNReal.ofReal (Real.rpow |liftedSpikeProcess 1 ω| (1 : ℝ))) =ᵐ[
        liftedUnitIntervalVolume] 0 := by
    filter_upwards [liftedSpikeProcess_ae_eq_zero (1 : NNReal)] with ω hω
    simp [hω]
  exact MeasureTheory.lintegral_eq_zero_of_ae_eq_zero hzero

/-- Helper for Exercise 21.4.1: lifting the sample space does not repair the failure of right
continuity. -/
private lemma liftedSpikeProcess_not_rightContinuous :
    ¬ HasRightContinuousPaths liftedSpikeProcess := by
  -- Proof comment: a right-continuity witness on the lifted space would restrict along `ULift.up`
  -- to a right-continuity witness for the original spike process.
  intro hrc
  apply spikeProcess_not_rightContinuous
  intro ω t
  simpa [liftedSpikeProcess] using hrc (ULift.up ω) t

/-- Helper for Exercise 21.4.1: the lifted spike process violates the `L¹` tail bound with
`threshold = 1 / 2` and `T = 1`. -/
private lemma liftedSpikeProcess_fails_tail_bound :
    ∫⁻ ω, ENNReal.ofReal (Real.rpow |liftedSpikeProcess 1 ω| (1 : ℝ))
      ∂liftedUnitIntervalVolume <
      ENNReal.ofReal (Real.rpow (1 / 2 : ℝ) (1 : ℝ)) *
        liftedUnitIntervalVolume liftedSpikeHalfEvent := by
  -- Proof comment: the left-hand side is zero, while the right-hand side is bounded below by the
  -- positive constant `(1 / 2)^1` because the event has mass at least `1`.
  rw [liftedSpikeProcess_terminalMoment_eq_zero]
  have hhalf_pos : 0 < ENNReal.ofReal (Real.rpow (1 / 2 : ℝ) (1 : ℝ)) := by
    norm_num
  have hhalf_le :
      ENNReal.ofReal (Real.rpow (1 / 2 : ℝ) (1 : ℝ)) ≤
        ENNReal.ofReal (Real.rpow (1 / 2 : ℝ) (1 : ℝ)) *
          liftedUnitIntervalVolume liftedSpikeHalfEvent := by
    simpa using
      (mul_le_mul_left' liftedSpikeEvent_measure_ge_one
        (ENNReal.ofReal (Real.rpow (1 / 2 : ℝ) (1 : ℝ))))
  exact lt_of_lt_of_le hhalf_pos hhalf_le

end LiftedCounterexample

-- Proof sketch: choose a filtered probability space carrying a martingale or a nonnegative
-- submartingale with a jump visible only at a non-right-continuous exceptional time; the terminal
-- `p`-th moment stays too small compared with the probability of a large earlier excursion, so the
-- tail bound from clause `(1)` fails.
/-- Exercise 21.4.1 (4): right continuity is essential. There exists a martingale or a nonnegative
submartingale without right-continuous paths for which the tail estimate in clause `(i)` fails. -/
theorem exists_process_without_rightContinuous_paths_failing_doobLp_tail_bound :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (μ : Measure Ω') (ℱ : Filtration NNReal mΩ')
      (X : NNReal → Ω' → ℝ) (T : NNReal) (p threshold : ℝ),
      IsProbabilityMeasure μ ∧
        (Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) ∧
        ¬ HasRightContinuousPaths X ∧
        1 ≤ p ∧
        0 < threshold ∧
        ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ <
          ENNReal.ofReal (Real.rpow threshold p) *
            μ {ω | ENNReal.ofReal threshold ≤ (|X|*_T) ω} := by
  -- Proof comment: use the spike process on `ULift ℝ` with the pushed-forward unit-interval
  -- measure; the lifted helper package already records the martingale property, the failure of
  -- right continuity, and the explicit violation of the tail bound.
  refine ⟨LiftedSpikeSpace, inferInstance, liftedUnitIntervalVolume,
    (⊤ : Filtration NNReal (inferInstance : MeasurableSpace LiftedSpikeSpace)),
    liftedSpikeProcess, (1 : NNReal), (1 : ℝ), (1 / 2 : ℝ), ?_⟩
  refine ⟨liftedUnitIntervalVolume_isProbability, Or.inl liftedSpikeProcess_martingale,
    liftedSpikeProcess_not_rightContinuous, by norm_num, by norm_num, ?_⟩
  simpa [liftedSpikeHalfEvent] using liftedSpikeProcess_fails_tail_bound

end ProbabilityTheory

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Theorem_9_32
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Corollary_8_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Exercise_11_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6.DyadicGeometry
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_3.StoppingApprox

open Filter MeasureTheory
open MeasureTheory.Filtration
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}
variable {X : NNReal → Ω → ℝ}

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable [UsualConditions ℱ μ]

/-- Helper for Theorem 21.24: the canonical deterministic right-approximation sequence used to
probe the future of a fixed time `t`. -/
private def rightApproxTime (t : NNReal) (n : ℕ) : NNReal :=
  t + ((n + 1 : ℕ) : NNReal)⁻¹

/-- Helper for Theorem 21.24: every deterministic right approximation stays strictly to the right
of its base time. -/
private lemma lt_rightApproxTime (t : NNReal) (n : ℕ) :
    t < rightApproxTime t n := by
  -- Proof comment: the reciprocal mesh is strictly positive, so adding it moves us to the right.
  dsimp [rightApproxTime]
  have hpos : 0 < (((n + 1 : ℕ) : NNReal)⁻¹) := by
    positivity
  exact lt_add_of_pos_right t hpos

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.24: under the usual conditions, every `μ`-null event is measurable in
every time slice of the filtration. -/
private lemma measurableSet_filtration_of_null (t : NNReal) {s : Set Ω} (hs : μ s = 0) :
    MeasurableSet[ℱ t] s := by
  -- Proof comment: time-zero completeness propagates forward by filtration monotonicity.
  exact
    initialAmbientNullMeasurable_mono ℱ μ (usualConditions_timeZeroComplete ℱ μ) t hs

omit [UsualConditions ℱ μ] in
/-- Helper for Theorem 21.24: if a supermartingale does not lose expectation between `t` and `s`,
then the conditional-expectation inequality at time `t` is actually an equality. -/
private lemma supermartingale_condExp_ae_eq_of_expectation_eq
    (hX : Supermartingale X ℱ μ) {t s : NNReal} (hts : t ≤ s)
    (hEX : μ[X s] = μ[X t]) :
    μ[X s | ℱ t] =ᵐ[μ] X t := by
  -- Proof comment: start from the defining supermartingale inequality.
  have hle : μ[X s | ℱ t] ≤ᵐ[μ] X t := hX.condExp_ae_le hts
  -- Proof comment: equality of expectations upgrades the almost-everywhere inequality to equality.
  have hIntegralEq : ∫ ω, μ[X s | ℱ t] ω ∂μ = ∫ ω, X t ω ∂μ := by
    calc
      ∫ ω, μ[X s | ℱ t] ω ∂μ = μ[X s] := by
        simpa using integral_condExp (ℱ.le t) (μ := μ) (f := X s)
      _ = μ[X t] := hEX
      _ = ∫ ω, X t ω ∂μ := by
        rfl
  exact (integral_eq_iff_of_ae_le integrable_condExp (hX.integrable t) hle).mp hIntegralEq

/-- Helper for Theorem 21.24: the canonical dyadic future approximants are cofinal in the
right-neighborhood filtration, so taking the infimum over their time slices recovers `ℱ t`. -/
private lemma filtration_iInf_dyadicRightApprox_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] [UsualConditions ℱ μ] (t : NNReal) :
    (⨅ n : ℕ, ℱ (dyadicRightApprox t n)) = ℱ t := by
  let hUsual : UsualConditions ℱ μ := inferInstance
  letI : Filtration.IsRightContinuous ℱ := hUsual.toIsRightContinuous
  refine le_antisymm ?_ ?_
  · -- Proof comment: every future time `u > t` eventually dominates the dyadic approximants, so
    -- the dyadic infimum is below the reciprocal-mesh infimum already identified in
    -- `StoppingApprox`.
    have hleReciprocal :
        (⨅ n : ℕ, ℱ (dyadicRightApprox t n)) ≤ ⨅ m : ℕ, ℱ (rightApproxTime t m) := by
      refine le_iInf fun m : ℕ => ?_
      have hm_eventually :
            ∀ᶠ n : ℕ in atTop, dyadicRightApprox t n < rightApproxTime t m :=
          tendsto_dyadicRightApprox t (Iio_mem_nhds (lt_rightApproxTime t m))
      rw [Filter.eventually_atTop] at hm_eventually
      rcases hm_eventually with ⟨N, hN⟩
      exact (iInf_le _ N).trans (ℱ.mono (le_of_lt (hN N le_rfl)))
    exact hleReciprocal.trans <| by
      simpa [rightApproxTime] using (filtration_iInf_add_inv_succ_eq (ℱ := ℱ) t).le
  · -- Proof comment: each dyadic approximation stays to the right of `t`, so `ℱ t` sits below
    -- every sampled sigma-algebra and hence below their infimum.
    refine le_iInf fun n ↦ ℱ.mono (le_dyadicRightApprox t n)

/-- Helper for Theorem 21.24: deterministic monotone sampling of the filtration produces the
discrete filtration seen by the sampled process. -/
private def sampledFiltration21_24 (τ : ℕ → NNReal) (hτ : Monotone τ) :
    Filtration ℕ mΩ :=
  Filtration.mk (fun n => ℱ (τ n))
    (fun _ _ hij => ℱ.mono (hτ hij))
    (fun n => ℱ.le (τ n))

/-- Helper for Theorem 21.24: the clipped dyadic row map `k ↦ dyadicPointUpTo q n k` is monotone
in the row index. -/
private lemma dyadicPointUpTo_monotone21_24 (q : NNReal) (n : ℕ) :
    Monotone (dyadicPointUpTo q n) := by
  intro i j hij
  dsimp [dyadicPointUpTo]
  refine min_le_min le_rfl ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

/-- Helper for Theorem 21.24: the first point of every clipped dyadic row is the initial time `0`.
-/
private lemma dyadicPointUpTo_zero21_24 (q : NNReal) (n : ℕ) :
    dyadicPointUpTo q n 0 = 0 := by
  simp [dyadicPointUpTo]

/-- Helper for Theorem 21.24: a submartingale remains a discrete submartingale after monotone
deterministic sampling. -/
private lemma sampledSubmartingaleOfMonotone21_24
    {Y : NNReal → Ω → ℝ}
    (hY : Submartingale Y ℱ μ)
    {τ : ℕ → NNReal} (hτ : Monotone τ) :
    Submartingale (fun n ω ↦ Y (τ n) ω) (sampledFiltration21_24 (ℱ := ℱ) τ hτ) μ := by
  -- Proof comment: adaptation, integrability, and the conditional-expectation inequality all
  -- transport directly through the deterministic monotone time change.
  refine submartingale_nat ?_ ?_ ?_
  · intro n
    simpa [sampledFiltration21_24] using hY.stronglyAdapted (τ n)
  · intro n
    exact hY.integrable (τ n)
  · intro n
    simpa [sampledFiltration21_24] using
      hY.ae_le_condExp (i := τ n) (j := τ (n + 1)) (hτ (Nat.le_succ n))

/-- Helper for Theorem 21.24: a supermartingale remains a discrete supermartingale after monotone
deterministic sampling. -/
private lemma sampledSupermartingaleOfMonotone21_24
    {Y : NNReal → Ω → ℝ}
    (hY : Supermartingale Y ℱ μ)
    {τ : ℕ → NNReal} (hτ : Monotone τ) :
    Supermartingale (fun n ω ↦ Y (τ n) ω) (sampledFiltration21_24 (ℱ := ℱ) τ hτ) μ := by
  -- Proof comment: the one-step supermartingale inequality survives the same deterministic time
  -- change as in the submartingale case.
  refine supermartingale_nat ?_ ?_ ?_
  · intro n
    simpa [sampledFiltration21_24] using hY.stronglyAdapted (τ n)
  · intro n
    exact hY.integrable (τ n)
  · intro n
    simpa [sampledFiltration21_24] using
      hY.condExp_ae_le (hτ (Nat.le_succ n))

/-- Helper for Theorem 21.24: the dyadic grid maximum on `[0, q]` at mesh `2⁻ⁿ` records the
largest absolute sampled value on that clipped row. -/
private def dyadicGridAbsMax21_24 (q : NNReal) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (dyadicCutoff q n + 1)).sup' Finset.nonempty_range_add_one
    (fun k ↦ |X (dyadicPointUpTo q n k) ω|)

/-- Helper for Theorem 21.24: refining the dyadic row can only increase the bounded-horizon
sampled absolute maximum. -/
private lemma dyadicGridAbsMax21_24_mono (q : NNReal) (n : ℕ) (ω : Ω) :
    dyadicGridAbsMax21_24 (X := X) q n ω ≤ dyadicGridAbsMax21_24 (X := X) q (n + 1) ω := by
  let s := Finset.range (dyadicCutoff q n + 1)
  have hs : s.Nonempty := Finset.nonempty_range_add_one
  have hcutoff_succ : dyadicCutoff q (n + 1) = 2 * dyadicCutoff q n := by
    unfold dyadicCutoff
    simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hbound :
      s.sup' hs (fun k ↦ |X (dyadicPointUpTo q n k) ω|) ≤ dyadicGridAbsMax21_24 (X := X) q (n + 1) ω := by
    refine Finset.sup'_le (H := hs) (f := fun k : ℕ ↦ |X (dyadicPointUpTo q n k) ω|) ?_
    intro k hk
    have hk_le : k ≤ dyadicCutoff q n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk' : 2 * k ∈ Finset.range (dyadicCutoff q (n + 1) + 1) := by
      refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
      calc
        2 * k ≤ 2 * dyadicCutoff q n := Nat.mul_le_mul_left 2 hk_le
        _ = dyadicCutoff q (n + 1) := hcutoff_succ.symm
    calc
      |X (dyadicPointUpTo q n k) ω| = |X (dyadicPointUpTo q (n + 1) (2 * k)) ω| := by
        rw [dyadicPointUpTo_even]
      _ ≤
          (Finset.range (dyadicCutoff q (n + 1) + 1)).sup' Finset.nonempty_range_add_one
            (fun j ↦ |X (dyadicPointUpTo q (n + 1) j) ω|) := by
          exact Finset.le_sup' (f := fun j : ℕ ↦ |X (dyadicPointUpTo q (n + 1) j) ω|) hk'
  simpa [dyadicGridAbsMax21_24, s] using hbound

/-- Helper for Theorem 21.24: each dyadic bounded-horizon sampled row satisfies the Chapter 11
absolute-maximal tail bound with constants depending only on `X 0` and `X q`. -/
private lemma dyadicGridAbsMax21_24_tail_bound
    (hX : Supermartingale X ℱ μ)
    (q : NNReal) (n : ℕ) (c : NNReal) (hc : 0 < c) :
    c * μ {ω | (c : ℝ) ≤ dyadicGridAbsMax21_24 (X := X) q n ω} ≤
      ENNReal.ofReal (12 * μ[fun ω ↦ |X 0 ω|] + 9 * μ[fun ω ↦ |X q ω|]) := by
  let τ : ℕ → NNReal := dyadicPointUpTo q n
  have hτ : Monotone τ := dyadicPointUpTo_monotone21_24 q n
  have hrow :
      Supermartingale (fun k ω ↦ X (τ k) ω) (sampledFiltration21_24 (ℱ := ℱ) τ hτ) μ := by
    -- Proof comment: the clipped dyadic row is just a deterministic monotone sampling of the
    -- ambient supermartingale.
    simpa [τ] using
      sampledSupermartingaleOfMonotone21_24
        (μ := μ)
        (ℱ := ℱ)
        (Y := X)
        hX
        hτ
  -- Proof comment: identify the dyadic grid maximum with the discrete running maximum up to the
  -- cutoff time and then apply the sampled Chapter 11 absolute-maximal inequality.
  simpa [dyadicGridAbsMax21_24, τ, dyadicPointUpTo_zero21_24, dyadicPointUpTo_cutoff] using
    (submartingale_or_supermartingale_absMaxUpTo_tail_bound
      (μ := μ)
      (ℱ := sampledFiltration21_24 (ℱ := ℱ) τ hτ)
      (X := fun k ω ↦ X (τ k) ω)
      (Or.inr hrow)
      (dyadicCutoff q n)
      c
      hc)

/-- Helper for Theorem 21.24: if one dyadic row maximum on `[0, q]` is bounded at `ω`, then the
corresponding exact dyadic right-approximation sample is bounded by the same constant whenever that
sample time still lies in `[0, q]`. -/
private lemma abs_dyadicRightApprox_le_of_dyadicGridAbsMax21_24
    {q t : NNReal} {n : ℕ} {ω : Ω} {C : ℝ}
    (hq : dyadicRightApprox t n ≤ q)
    (hC : dyadicGridAbsMax21_24 (X := X) q n ω ≤ C) :
    |X (dyadicRightApprox t n) ω| ≤ C := by
  let k : ℕ := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)
  have htq : t ≤ q := le_trans (le_dyadicRightApprox t n) hq
  have hk : k ∈ Finset.range (dyadicCutoff q n + 1) := by
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    simpa [k] using dyadicRightApprox_index_le_cutoff (t := t) (T := q) htq n
  have hpoint : dyadicPointUpTo q n k = dyadicRightApprox t n := by
    have hkq :
        ((k : NNReal) / (2 : NNReal) ^ n) ≤ q := by
      simpa [dyadicRightApprox, k] using hq
    simp [dyadicPointUpTo, dyadicRightApprox, k, min_eq_right hkq]
  have hsample :
      |X (dyadicPointUpTo q n k) ω| ≤ dyadicGridAbsMax21_24 (X := X) q n ω := by
    simpa [dyadicGridAbsMax21_24] using
      (Finset.le_sup' (s := Finset.range (dyadicCutoff q n + 1))
        (f := fun j : ℕ ↦ |X (dyadicPointUpTo q n j) ω|) hk)
  calc
    |X (dyadicRightApprox t n) ω| = |X (dyadicPointUpTo q n k) ω| := by rw [hpoint]
    _ ≤ dyadicGridAbsMax21_24 (X := X) q n ω := hsample
    _ ≤ C := hC

/-- Helper for Theorem 21.24: for a strictly positive time, the dyadic predecessor sample on mesh
`2⁻ⁿ` is obtained by subtracting one from the dyadic ceiling index. -/
private def dyadicLeftApprox (t : Set.Ioi (0 : NNReal)) (n : ℕ) : NNReal :=
  (((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1 : ℕ) : NNReal) / (2 : NNReal) ^ n)

/-- Helper for Theorem 21.24: every dyadic predecessor sample stays strictly below the base time.
-/
private lemma dyadicLeftApprox_lt_self21_24
    (t : Set.Ioi (0 : NNReal)) (n : ℕ) :
    dyadicLeftApprox t n < (t : NNReal) := by
  have harg_pos : 0 < (t.1 : ℝ) * (2 : ℝ) ^ n := by
    have ht_pos : 0 < (t : NNReal) := t.2
    exact mul_pos (by exact_mod_cast ht_pos) (by positivity)
  have hpow_pos : 0 < (2 : ℝ) ^ n := by
    positivity
  have hceil_pos :
      0 <
        Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) := by
    -- Proof comment: the scaled positive time is strictly positive on every dyadic mesh.
    exact Nat.ceil_pos.mpr harg_pos
  have hnum_lt :
      (((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1 : ℕ) : ℝ)) <
        (t.1 : ℝ) * (2 : ℝ) ^ n := by
    have hceil_lt :
        (Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) : ℝ) <
          (t.1 : ℝ) * (2 : ℝ) ^ n + 1 := by
      exact Nat.ceil_lt_add_one harg_pos.le
    have hcast :
        (((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1 : ℕ) : ℝ)) =
          (Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hceil_pos), Nat.cast_one]
    rw [hcast]
    linarith
  have hdiv :
      (((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) < (t.1 : ℝ) := by
    refine (div_lt_iff₀ hpow_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum_lt
  have hdiv' :
      (((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) <
        (t : NNReal) := by
    exact_mod_cast hdiv
  -- Proof comment: dividing by the positive mesh denominator preserves the strict predecessor
  -- inequality.
  simpa [dyadicLeftApprox] using hdiv'

/-- Helper for Theorem 21.24: if one dyadic row maximum on `[0, q]` is bounded at `ω`, then the
positive-time dyadic left-approximation sample is bounded by the same constant whenever the
corresponding right approximation still lies in `[0, q]`. -/
private lemma abs_dyadicLeftApprox_le_of_dyadicGridAbsMax21_24
    {q : NNReal} {t : Set.Ioi (0 : NNReal)} {n : ℕ} {ω : Ω} {C : ℝ}
    (hq : dyadicRightApprox t.1 n ≤ q)
    (hC : dyadicGridAbsMax21_24 (X := X) q n ω ≤ C) :
    |X (dyadicLeftApprox t n) ω| ≤ C := by
  let k : ℕ := Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1
  have htq : t.1 ≤ q := le_trans (le_dyadicRightApprox t.1 n) hq
  have hk : k ∈ Finset.range (dyadicCutoff q n + 1) := by
    refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    calc
      k ≤ Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) := Nat.sub_le _ _
      _ ≤ dyadicCutoff q n := by
        simpa using dyadicRightApprox_index_le_cutoff (t := t.1) (T := q) htq n
  have hleft_le_q :
      (((k : ℕ) : NNReal) / (2 : NNReal) ^ n) ≤ q := by
    have hk_le_ceil : k ≤ Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) := by
      -- Proof comment: the predecessor index is bounded by the original ceil index.
      dsimp [k]
      exact Nat.sub_le _ _
    calc
      (((k : ℕ) : NNReal) / (2 : NNReal) ^ n)
          ≤ ((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) : NNReal) / (2 : NNReal) ^ n) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast hk_le_ceil)
              (by positivity)
      _ = dyadicRightApprox t.1 n := by simp [dyadicRightApprox]
      _ ≤ q := hq
  have hpoint :
      dyadicPointUpTo q n k = dyadicLeftApprox t n := by
    -- Proof comment: once the predecessor-ceil index still lies before the horizon cutoff, the
    -- clipped row sample is exactly the left dyadic approximant.
    rw [dyadicPointUpTo, min_eq_right hleft_le_q, dyadicLeftApprox]
  have hsample :
      |X (dyadicPointUpTo q n k) ω| ≤ dyadicGridAbsMax21_24 (X := X) q n ω := by
    simpa [dyadicGridAbsMax21_24] using
      (Finset.le_sup' (s := Finset.range (dyadicCutoff q n + 1))
        (f := fun j : ℕ ↦ |X (dyadicPointUpTo q n j) ω|) hk)
  calc
    |X (dyadicLeftApprox t n) ω| = |X (dyadicPointUpTo q n k) ω| := by rw [hpoint]
    _ ≤ dyadicGridAbsMax21_24 (X := X) q n ω := hsample
    _ ≤ C := hC

/-- Helper for Theorem 21.24: once a right-dyadic sample lies below a finite horizon `q`, any
finer dyadic row contains the same sample at the rescaled index. -/
private lemma dyadicRightApprox_refine_into_commonRow21_24
    {q t : NNReal} {m N : ℕ} (hmN : m ≤ N)
    (hq : dyadicRightApprox t m ≤ q) :
    let k := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ m) * 2 ^ (N - m)
    k ≤ dyadicCutoff q N ∧
      dyadicPointUpTo q N k = dyadicRightApprox t m := by
  have htq : t ≤ q := le_trans (le_dyadicRightApprox t m) hq
  -- Proof comment: specialize the generic clipped-row refinement lemma and note that the clipping
  -- is inactive because this exact right sample already stays below the chosen horizon.
  simpa [clippedDyadicApprox_eq_min_dyadicRightApprox, min_eq_right hq] using
    (clippedDyadicApprox_prefix_embeds_in_row (t := t) (T := q) htq (m := m) (N := N) hmN)

/-- Helper for Theorem 21.24: the exact left-dyadic predecessor sample is bounded above by the
matching right-dyadic sample on the same mesh. -/
private lemma dyadicLeftApprox_le_dyadicRightApprox21_24
    (t : Set.Ioi (0 : NNReal)) (n : ℕ) :
    dyadicLeftApprox t n ≤ dyadicRightApprox t.1 n := by
  -- Proof comment: both samples use the same dyadic denominator, and the predecessor-ceil index
  -- is obtained by subtracting one from the right-sample ceil index.
  rw [dyadicLeftApprox, dyadicRightApprox, div_eq_mul_inv, div_eq_mul_inv]
  exact
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Nat.sub_le (Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n)) 1))
      (by positivity)

/-- Helper for Theorem 21.24: the canonical left-dyadic predecessor times increase with the mesh.
-/
private lemma dyadicLeftApprox_le_succ21_24
    (t : Set.Ioi (0 : NNReal)) (n : ℕ) :
    dyadicLeftApprox t n ≤ dyadicLeftApprox t (n + 1) := by
  let c : ℕ := Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n)
  let c' : ℕ := Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ (n + 1))
  have ht_pos : 0 < (t.1 : ℝ) * (2 : ℝ) ^ n := by
    exact mul_pos (by exact_mod_cast t.2) (by positivity)
  have hc_pos : 0 < c := by
    exact Nat.ceil_pos.mpr ht_pos
  have hstep_nat : 2 * (c - 1) ≤ c' - 1 := by
    have hlt : 2 * (c - 1) < c' := by
      rw [Nat.lt_ceil]
      have hpred : ((c - 1 : ℕ) : ℝ) < (t.1 : ℝ) * (2 : ℝ) ^ n := by
        rw [Nat.cast_sub (Nat.succ_le_of_lt hc_pos), Nat.cast_one, sub_lt_iff_lt_add]
        simpa [c] using (Nat.ceil_lt_add_one (show 0 ≤ (t.1 : ℝ) * (2 : ℝ) ^ n by positivity))
      calc
        ((2 * (c - 1) : ℕ) : ℝ) = 2 * (((c - 1 : ℕ) : ℝ)) := by norm_num
        _ < 2 * ((t.1 : ℝ) * (2 : ℝ) ^ n) := by gcongr
        _ = (t.1 : ℝ) * (2 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            ring
    omega
  have hstep_real :
      (2 : ℝ) * ((c - 1 : ℕ) : ℝ) ≤ ((c' - 1 : ℕ) : ℝ) := by
    exact_mod_cast hstep_nat
  have hpow_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  change
    (((c - 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) ≤
      (((c' - 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))
  rw [pow_succ]
  have hrewrite :
      (((c - 1 : ℕ) : ℝ) / ((2 : ℝ) ^ n)) =
        (2 * (((c - 1 : ℕ) : ℝ))) / (((2 : ℝ) ^ n) * 2) := by
    field_simp [hpow_ne]
  rw [hrewrite]
  have hden_pos : 0 < ((2 : ℝ) ^ n) * 2 := by positivity
  rw [div_le_div_iff₀ hden_pos hden_pos]
  have hscaled :
      ((2 : ℝ) ^ n) * (2 * (((c - 1 : ℕ) : ℝ))) ≤
        ((2 : ℝ) ^ n) * (((c' - 1 : ℕ) : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hstep_real (by positivity)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Helper for Theorem 21.24: once the exact left-dyadic predecessor sample stays below a finite
horizon `q`, any finer dyadic row contains the same predecessor sample at the rescaled index. -/
private lemma dyadicLeftApprox_refine_into_commonRow21_24
    {q : NNReal} {t : Set.Ioi (0 : NNReal)} {m N : ℕ} (hmN : m ≤ N)
    (hq : dyadicRightApprox t.1 m ≤ q) :
    let k := (Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ m) - 1) * 2 ^ (N - m)
    k ≤ dyadicCutoff q N ∧
      dyadicPointUpTo q N k = dyadicLeftApprox t m := by
  let j : ℕ := Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ m) - 1
  have htq : t.1 ≤ q := le_trans (le_dyadicRightApprox t.1 m) hq
  have hj_le : j ≤ dyadicCutoff q m := by
    calc
      j ≤ Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ m) := Nat.sub_le _ _
      _ ≤ dyadicCutoff q m := by
        simpa using dyadicRightApprox_index_le_cutoff (t := t.1) (T := q) htq m
  have hk_le : j * 2 ^ (N - m) ≤ dyadicCutoff q N := by
    have hk_le' : j * 2 ^ (N - m) ≤ dyadicCutoff q m * 2 ^ (N - m) :=
      Nat.mul_le_mul_right (2 ^ (N - m)) hj_le
    have hcutoff_refine :
        dyadicCutoff q m * 2 ^ (N - m) = dyadicCutoff q N := by
      unfold dyadicCutoff
      calc
        Nat.ceil ↑q * 2 ^ m * 2 ^ (N - m)
            = Nat.ceil ↑q * (2 ^ m * 2 ^ (N - m)) := by rw [Nat.mul_assoc]
        _ = Nat.ceil ↑q * 2 ^ (m + (N - m)) := by rw [← pow_add]
        _ = Nat.ceil ↑q * 2 ^ N := by rw [Nat.add_sub_of_le hmN]
    exact hk_le'.trans_eq hcutoff_refine
  have hleft_le_q : dyadicLeftApprox t m ≤ q := by
    exact (dyadicLeftApprox_le_dyadicRightApprox21_24 t m).trans hq
  have hleft_le_q' :
      (((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ m) - 1 : ℕ) : NNReal) / (2 : NNReal) ^ m) ≤ q := by
    simpa [dyadicLeftApprox] using hleft_le_q
  have hpoint_m : dyadicPointUpTo q m j = dyadicLeftApprox t m := by
    -- Proof comment: on the coarse row, the predecessor-ceil index is still below the horizon, so
    -- the clipped sample is exactly the left dyadic approximant.
    dsimp [j, dyadicPointUpTo, dyadicLeftApprox]
    rw [min_eq_right hleft_le_q']
  have hpoint :
      dyadicPointUpTo q N (j * 2 ^ (N - m)) = dyadicLeftApprox t m := by
    -- Proof comment: refine the coarse predecessor index to the common row and then identify the
    -- coarse row value with the exact left sample.
    calc
      dyadicPointUpTo q N (j * 2 ^ (N - m)) = dyadicPointUpTo q m j := by
        simpa [Nat.add_sub_of_le hmN, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (dyadicPointUpTo_refine (T := q) m (N - m) j)
      _ = dyadicLeftApprox t m := hpoint_m
  simpa [j] using And.intro hk_le hpoint

/-- Helper for Theorem 21.24: the positive-time left dyadic approximants approach `t` from below.
-/
private lemma tendsto_dyadicLeftApprox21_24
    (t : Set.Ioi (0 : NNReal)) :
    Tendsto (dyadicLeftApprox t) atTop (𝓝[<] (t : NNReal)) := by
  let mesh : ℕ → NNReal := fun n ↦ ((2 : NNReal) ^ n)⁻¹
  have hmesh :
      Tendsto mesh atTop (𝓝 (0 : NNReal)) := by
    -- Proof comment: the dyadic mesh widths are inverse powers of `2`, so they vanish at
    -- infinity.
    exact
      tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (show (1 : NNReal) < 2 by norm_num))
  have hidentity :
      ∀ n : ℕ, dyadicLeftApprox t n + mesh n = dyadicRightApprox t.1 n := by
    intro n
    have harg_pos : 0 < (t.1 : ℝ) * (2 : ℝ) ^ n := by
      have ht_pos : 0 < (t : NNReal) := t.2
      exact mul_pos (by exact_mod_cast ht_pos) (by positivity)
    have hceil_pos :
        0 <
          Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) := by
      -- Proof comment: the scaled positive time is strictly positive, so its ceiling is positive.
      exact Nat.ceil_pos.mpr harg_pos
    have hsub :
        (Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1 : ℕ) + 1 =
          Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) := by
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt hceil_pos)
    have hsub' :
        (((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1 : ℕ) : NNReal) + 1) =
          (Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) : NNReal) := by
      exact_mod_cast hsub
    -- Proof comment: the predecessor-ceil sample differs from the right approximant by exactly
    -- one dyadic mesh width.
    calc
      dyadicLeftApprox t n + mesh n
          = (((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1 : ℕ) : NNReal) *
                ((2 : NNReal) ^ n)⁻¹) +
              (1 * ((2 : NNReal) ^ n)⁻¹) := by
                dsimp [mesh]
                rw [dyadicLeftApprox, div_eq_mul_inv, one_mul]
      _ = ((((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1 : ℕ) : NNReal) + 1) *
            ((2 : NNReal) ^ n)⁻¹) := by
            rw [← add_mul]
      _ = ((Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) : ℕ) : NNReal) * ((2 : NNReal) ^ n)⁻¹ := by
            rw [hsub']
      _ = dyadicRightApprox t.1 n := by
            rw [dyadicRightApprox, div_eq_mul_inv]
  have hstrict :
      ∀ n : ℕ, dyadicLeftApprox t n < (t : NNReal) := by
    intro n
    exact dyadicLeftApprox_lt_self21_24 t n
  have hnhds :
      Tendsto (dyadicLeftApprox t) atTop (𝓝 (t : NNReal)) := by
    refine tendsto_order.2 ?_
    constructor
    · intro a ha
      have hgap : 0 < (t : NNReal) - a := tsub_pos_of_lt ha
      have hsmall : ∀ᶠ n : ℕ in atTop, mesh n < (t : NNReal) - a :=
        (tendsto_order.1 hmesh).2 _ hgap
      filter_upwards [hsmall] with n hn
      have hsum_lt : a + mesh n < (t : NNReal) := by
        rwa [lt_tsub_iff_right, add_comm] at hn
      have hleft_ge : (t : NNReal) ≤ dyadicLeftApprox t n + mesh n := by
        rw [hidentity n]
        exact le_dyadicRightApprox t.1 n
      have hcompare :
          a + mesh n < dyadicLeftApprox t n + mesh n :=
        lt_of_lt_of_le hsum_lt hleft_ge
      -- Proof comment: once the mesh width is smaller than `t - a`, cancelling the common mesh
      -- term shows the predecessor sample lies above `a`.
      exact lt_of_add_lt_add_right hcompare
    · intro b hb
      filter_upwards with n
      exact lt_trans (hstrict n) hb
  -- Proof comment: the predecessor samples converge in the ordinary neighborhood filter and stay
  -- strictly below `t`, so the limit upgrades to the strict-left filter.
  simpa using
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (f := dyadicLeftApprox t)
      (s := Set.Iio (t : NNReal))
      hnhds
      (Eventually.of_forall fun n ↦ hstrict n))

/-- Helper for Theorem 21.24: an alternating lower/upper witness prefix for a real sequence
forces the finite-horizon upcrossing count to exceed the prefix length. -/
private lemma lt_upcrossingsBefore_ofWitnessPrefix
    {f : ℕ → Ω → ℝ} {ω : Ω} {a b : ℝ} {K : ℕ}
    (hab : a < b)
    (lowerIndex upperIndex : Fin (K + 1) → ℕ)
    (hLowerValue : ∀ k : Fin (K + 1), f (lowerIndex k) ω < a)
    (hUpperValue : ∀ k : Fin (K + 1), b < f (upperIndex k) ω)
    (hLowerLeUpper : ∀ k : Fin (K + 1), lowerIndex k ≤ upperIndex k)
    (hUpperLeNextLower :
      ∀ j : ℕ, ∀ hj : j < K,
        upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
          lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩) :
    K < upcrossingsBefore a b f (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1) ω := by
  have hPrefix :
      ∀ j : ℕ, ∀ hj : j ≤ K,
        j < upcrossingsBefore a b f (upperIndex ⟨j, Nat.lt_succ_of_le hj⟩ + 1) ω := by
    intro j
    induction j with
    | zero =>
        intro hj
        let k0 : Fin (K + 1) := ⟨0, Nat.succ_pos _⟩
        have hStep :
            upcrossingsBefore a b f 0 ω <
              upcrossingsBefore a b f (upperIndex k0 + 1) ω := by
          -- Proof comment: the first lower/upper witness pair already realizes one upcrossing.
          refine MeasureTheory.upcrossingsBefore_lt_of_exists_upcrossing
            (a := a)
            (b := b)
            (f := f)
            (N := 0)
            (N₁ := lowerIndex k0)
            (N₂ := upperIndex k0)
            (ω := ω)
            hab
            ?_
            ?_
            ?_
            ?_
          · exact zero_le (lowerIndex k0)
          · exact hLowerValue k0
          · exact hLowerLeUpper k0
          · exact hUpperValue k0
        simpa [k0, MeasureTheory.upcrossingsBefore_zero] using hStep
    | succ j ih =>
        intro hj
        have hj' : j ≤ K := Nat.le_of_succ_le hj
        let kj : Fin (K + 1) := ⟨j, Nat.lt_succ_of_le hj'⟩
        let kj1 : Fin (K + 1) := ⟨j + 1, Nat.lt_succ_of_le hj⟩
        have hjlt : j < K := lt_of_lt_of_le (Nat.lt_succ_self j) hj
        have hSep : upperIndex kj < lowerIndex kj1 := by
          have hWeak : upperIndex kj ≤ lowerIndex kj1 := hUpperLeNextLower j hjlt
          refine lt_of_le_of_ne hWeak ?_
          intro hEq
          have hUpperLt : f (upperIndex kj) ω < a := by
            simpa [hEq] using hLowerValue kj1
          exact (not_lt_of_ge hab.le) (lt_trans (hUpperValue kj) hUpperLt)
        have hStep :
            upcrossingsBefore a b f (upperIndex kj + 1) ω <
              upcrossingsBefore a b f (upperIndex kj1 + 1) ω := by
          -- Proof comment: the next lower witness appears strictly after the previous upper
          -- witness, so the upcrossing counter increases once more.
          refine MeasureTheory.upcrossingsBefore_lt_of_exists_upcrossing
            (a := a)
            (b := b)
            (f := f)
            (N := upperIndex kj + 1)
            (N₁ := lowerIndex kj1)
            (N₂ := upperIndex kj1)
            (ω := ω)
            hab
            ?_
            ?_
            ?_
            ?_
          · exact Nat.succ_le_of_lt hSep
          · exact hLowerValue kj1
          · exact hLowerLeUpper kj1
          · exact hUpperValue kj1
        have ihSucc :
            j + 1 ≤ upcrossingsBefore a b f (upperIndex kj + 1) ω := by
          exact Nat.succ_le_of_lt (ih hj')
        exact lt_of_le_of_lt ihSucc hStep
  -- Proof comment: applying the inductive prefix bound at the full witness length gives the
  -- required strict lower bound on the terminal finite-horizon upcrossing count.
  exact hPrefix K le_rfl

/-- Helper for Theorem 21.24: a witness prefix on one clipped dyadic row of `-X` feeds directly
into the generic finite-prefix upcrossing lower bound on the sign-reversed interval
`[-(b : ℝ), -(a : ℝ)]`. -/
private lemma commonRowWitnessPrefix_lt_rowUpcrossingsBefore21_24
    {q : NNReal} {N K : ℕ} {ω : Ω} {a b : ℚ}
    (hab : a < b)
    (lowerIndex upperIndex : Fin (K + 1) → ℕ)
    (hLowerValue :
      ∀ k : Fin (K + 1),
        -X (dyadicPointUpTo q N (lowerIndex k)) ω < -(b : ℝ))
    (hUpperValue :
      ∀ k : Fin (K + 1),
        -(a : ℝ) < -X (dyadicPointUpTo q N (upperIndex k)) ω)
    (hLowerLeUpper : ∀ k : Fin (K + 1), lowerIndex k ≤ upperIndex k)
    (hUpperLeNextLower :
      ∀ j : ℕ, ∀ hj : j < K,
        upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
          lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩) :
    K <
      upcrossingsBefore
        (-(b : ℝ))
        (-(a : ℝ))
        (fun k ω ↦ -X (dyadicPointUpTo q N k) ω)
        (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1)
        ω := by
  have hneg : (-(b : ℝ)) < -(a : ℝ) := by
    -- Proof comment: reversing signs swaps the rational interval endpoints.
    exact neg_lt_neg (Rat.cast_lt.2 hab)
  -- Proof comment: the row process already has the right lower/upper witness shape, so the
  -- generic prefix lemma applies without any further transport.
  simpa using
    lt_upcrossingsBefore_ofWitnessPrefix
      (f := fun k ω ↦ -X (dyadicPointUpTo q N k) ω)
      (ω := ω)
      (a := -(b : ℝ))
      (b := -(a : ℝ))
      hneg
      lowerIndex
      upperIndex
      hLowerValue
      hUpperValue
      hLowerLeUpper
      hUpperLeNextLower

/-- Helper for Theorem 21.24: a single closed witness pair `f N₁ ω ≤ a ≤ b ≤ f N₂ ω` still
forces one extra upcrossing before `N₂ + 1`. This is the closed-value companion of
`MeasureTheory.upcrossingsBefore_lt_of_exists_upcrossing`, tailored to the crossing-time API,
which produces `≤`/`≥` rather than strict inequalities. -/
private lemma upcrossingsBefore_lt_of_exists_closedUpcrossing21_24
    {f : ℕ → Ω → ℝ} {ω : Ω} {a b : ℝ} {N N₁ N₂ : ℕ}
    (hab : a < b)
    (hN₁ : N ≤ N₁)
    (hN₁' : f N₁ ω ≤ a)
    (hN₂ : N₁ ≤ N₂)
    (hN₂' : b ≤ f N₂ ω) :
    upcrossingsBefore a b f N ω < upcrossingsBefore a b f (N₂ + 1) ω := by
  -- Proof comment: the standard upcrossing-step argument only uses the lower witness in `Iic a`
  -- and the upper witness in `Ici b`, so the same proof works with closed inequalities.
  refine lt_of_lt_of_le (Nat.lt_succ_self _) (le_csSup (MeasureTheory.upperCrossingTime_lt_bddAbove hab) ?_)
  rw [Set.mem_setOf_eq, MeasureTheory.upperCrossingTime_succ_eq, MeasureTheory.hittingBtwn_lt_iff _ le_rfl]
  refine ⟨N₂, ⟨?_, Nat.lt_succ_self _⟩, hN₂'⟩
  rw [MeasureTheory.lowerCrossingTime, MeasureTheory.hittingBtwn_le_iff_of_lt _ (Nat.lt_succ_self _)]
  refine ⟨N₁, ⟨le_trans ?_ hN₁, hN₂⟩, hN₁'⟩
  by_cases hN : 0 < N
  · have hCross :
      MeasureTheory.upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
        Nat.sSup_mem
          (MeasureTheory.upperCrossingTime_lt_nonempty hN)
          (MeasureTheory.upperCrossingTime_lt_bddAbove hab)
    rw [MeasureTheory.upperCrossingTime_eq_upperCrossingTime_of_lt
      (hN₁.trans (hN₂.trans <| Nat.le_succ _)) hCross]
    exact hCross.le
  · rw [Nat.eq_zero_of_not_pos hN, MeasureTheory.upcrossingsBefore_zero, MeasureTheory.upperCrossingTime_zero,
      Pi.bot_apply, bot_eq_zero']

/-- Helper for Theorem 21.24: an alternating closed lower/upper witness prefix already forces the
finite-horizon upcrossing count to exceed the prefix length. This is the closed-value companion of
`lt_upcrossingsBefore_ofWitnessPrefix`, so the exact crossing-time API can be consumed without
artificially shrinking the interval. -/
private lemma lt_upcrossingsBefore_ofClosedWitnessPrefix21_24
    {f : ℕ → Ω → ℝ} {ω : Ω} {a b : ℝ} {K : ℕ}
    (hab : a < b)
    (lowerIndex upperIndex : Fin (K + 1) → ℕ)
    (hLowerValue : ∀ k : Fin (K + 1), f (lowerIndex k) ω ≤ a)
    (hUpperValue : ∀ k : Fin (K + 1), b ≤ f (upperIndex k) ω)
    (hLowerLeUpper : ∀ k : Fin (K + 1), lowerIndex k ≤ upperIndex k)
    (hUpperLeNextLower :
      ∀ j : ℕ, ∀ hj : j < K,
        upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
          lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩) :
    K < upcrossingsBefore a b f (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1) ω := by
  have hPrefix :
      ∀ j : ℕ, ∀ hj : j ≤ K,
        j < upcrossingsBefore a b f (upperIndex ⟨j, Nat.lt_succ_of_le hj⟩ + 1) ω := by
    intro j
    induction j with
    | zero =>
        intro hj
        let k0 : Fin (K + 1) := ⟨0, Nat.succ_pos _⟩
        have hStep :
            upcrossingsBefore a b f 0 ω <
              upcrossingsBefore a b f (upperIndex k0 + 1) ω := by
          -- Proof comment: the first closed lower/upper witness pair already realizes one
          -- upcrossing before the terminal upper index.
          refine upcrossingsBefore_lt_of_exists_closedUpcrossing21_24
            (ω := ω)
            (N := 0)
            (N₁ := lowerIndex k0)
            (N₂ := upperIndex k0)
            hab
            ?_
            ?_
            ?_
            ?_
          · exact zero_le (lowerIndex k0)
          · exact hLowerValue k0
          · exact hLowerLeUpper k0
          · exact hUpperValue k0
        simpa [k0, MeasureTheory.upcrossingsBefore_zero] using hStep
    | succ j ih =>
        intro hj
        have hj' : j ≤ K := Nat.le_of_succ_le hj
        let kj : Fin (K + 1) := ⟨j, Nat.lt_succ_of_le hj'⟩
        let kj1 : Fin (K + 1) := ⟨j + 1, Nat.lt_succ_of_le hj⟩
        have hjlt : j < K := lt_of_lt_of_le (Nat.lt_succ_self j) hj
        have hSep : upperIndex kj < lowerIndex kj1 := by
          have hWeak : upperIndex kj ≤ lowerIndex kj1 := hUpperLeNextLower j hjlt
          refine lt_of_le_of_ne hWeak ?_
          intro hEq
          have hUpperLe : b ≤ f (upperIndex kj) ω := hUpperValue kj
          have hLowerLe : f (upperIndex kj) ω ≤ a := by simpa [hEq] using hLowerValue kj1
          exact (not_le_of_gt hab) (le_trans hUpperLe hLowerLe)
        have hStep :
            upcrossingsBefore a b f (upperIndex kj + 1) ω <
              upcrossingsBefore a b f (upperIndex kj1 + 1) ω := by
          -- Proof comment: once the next lower witness occurs strictly after the previous upper
          -- witness, the closed lower/upper pair contributes one more upcrossing.
          refine upcrossingsBefore_lt_of_exists_closedUpcrossing21_24
            (ω := ω)
            (N := upperIndex kj + 1)
            (N₁ := lowerIndex kj1)
            (N₂ := upperIndex kj1)
            hab
            ?_
            ?_
            ?_
            ?_
          · exact Nat.succ_le_of_lt hSep
          · exact hLowerValue kj1
          · exact hLowerLeUpper kj1
          · exact hUpperValue kj1
        have ihSucc :
            j + 1 ≤ upcrossingsBefore a b f (upperIndex kj + 1) ω := by
          exact Nat.succ_le_of_lt (ih hj')
        exact lt_of_le_of_lt ihSucc hStep
  -- Proof comment: apply the inductive prefix estimate at the full witness length.
  exact hPrefix K le_rfl

/-- Helper for Theorem 21.24: a closed witness prefix on one clipped dyadic row of `-X` yields the
matching finite-prefix upcrossing lower bound on the sign-reversed interval `[-(b : ℝ), -(a : ℝ)]`.
This is the rowwise closed-value companion used by the exact crossing-time transport. -/
private lemma commonRowClosedWitnessPrefix_lt_rowUpcrossingsBefore21_24
    {q : NNReal} {N K : ℕ} {ω : Ω} {a b : ℚ}
    (hab : a < b)
    (lowerIndex upperIndex : Fin (K + 1) → ℕ)
    (hLowerValue :
      ∀ k : Fin (K + 1),
        -X (dyadicPointUpTo q N (lowerIndex k)) ω ≤ -(b : ℝ))
    (hUpperValue :
      ∀ k : Fin (K + 1),
        -(a : ℝ) ≤ -X (dyadicPointUpTo q N (upperIndex k)) ω)
    (hLowerLeUpper : ∀ k : Fin (K + 1), lowerIndex k ≤ upperIndex k)
    (hUpperLeNextLower :
      ∀ j : ℕ, ∀ hj : j < K,
        upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
          lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩) :
    K <
      upcrossingsBefore
        (-(b : ℝ))
        (-(a : ℝ))
        (fun k ω ↦ -X (dyadicPointUpTo q N k) ω)
        (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1)
        ω := by
  have hneg : (-(b : ℝ)) < -(a : ℝ) := by
    -- Proof comment: reversing signs swaps the rational interval endpoints.
    exact neg_lt_neg (Rat.cast_lt.2 hab)
  -- Proof comment: the sign-reversed row process already has the closed witness-prefix shape
  -- needed by the companion lower-bound lemma.
  simpa using
    lt_upcrossingsBefore_ofClosedWitnessPrefix21_24
      (f := fun k ω ↦ -X (dyadicPointUpTo q N k) ω)
      (ω := ω)
      (a := -(b : ℝ))
      (b := -(a : ℝ))
      hneg
      lowerIndex
      upperIndex
      hLowerValue
      hUpperValue
      hLowerLeUpper
      hUpperLeNextLower

/-- Helper for Theorem 21.24: right continuity of the expectation function transports directly
along the canonical dyadic right-approximation sequence. -/
private lemma tendsto_expectation_dyadicRightApprox
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (t : NNReal) :
    Tendsto (fun n : ℕ ↦ μ[X (dyadicRightApprox t n)]) atTop (𝓝 (μ[X t])) := by
  have happrox_mem : ∀ᶠ n : ℕ in atTop, dyadicRightApprox t n ∈ Set.Ici t := by
    -- Proof comment: every dyadic right approximation stays on the right side of `t`.
    exact Eventually.of_forall fun n ↦ le_dyadicRightApprox t n
  have happrox :
      Tendsto (dyadicRightApprox t) atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_dyadicRightApprox t) happrox_mem
  -- Proof comment: compose the right-continuous expectation map with the dyadic approximants.
  simpa [Function.comp] using Filter.Tendsto.comp (hEX_rc t) happrox

/-- Helper for Theorem 21.24: the conditional expectations of the dyadic future samples back to
time `t` converge to `X t` in `L¹`. -/
private lemma tendsto_eLpNorm_condExp_dyadicRightApprox_sub_slice
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (t : NNReal) :
    Tendsto
      (fun n : ℕ ↦
        eLpNorm
          (fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)
          1 μ)
      atTop
      (𝓝 0) := by
  have hExpTendsto :
      Tendsto (fun n : ℕ ↦ μ[X (dyadicRightApprox t n)]) atTop (𝓝 (μ[X t])) :=
    tendsto_expectation_dyadicRightApprox (X := X) (μ := μ) hEX_rc t
  have hGapTendsto :
      Tendsto (fun n : ℕ ↦ μ[X t] - μ[X (dyadicRightApprox t n)]) atTop (𝓝 0) := by
    -- Proof comment: subtracting the dyadic expectations from the time-`t` expectation produces
    -- a nonnegative gap that vanishes by right continuity.
    simpa using hExpTendsto.const_sub (μ[X t])
  have hEq :
      (fun n : ℕ ↦
        eLpNorm
          (fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)
          1 μ) =
        fun n : ℕ ↦ ENNReal.ofReal (μ[X t] - μ[X (dyadicRightApprox t n)]) := by
    funext n
    have hle : μ[X (dyadicRightApprox t n) | ℱ t] ≤ᵐ[μ] X t :=
      hX.condExp_ae_le (le_dyadicRightApprox t n)
    have hnonneg :
        0 ≤ᵐ[μ] fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω := by
      filter_upwards [hle] with ω hω
      exact sub_nonneg.mpr hω
    have hInt :
        Integrable
          (fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω) μ :=
      (hX.integrable t).sub integrable_condExp
    calc
      eLpNorm
          (fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)
          1 μ
          = ENNReal.ofReal
              (∫ ω, ‖X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω‖ ∂μ) := by
            rw [eLpNorm_one_eq_lintegral_enorm,
              ← ofReal_integral_norm_eq_lintegral_enorm hInt]
      _ = ENNReal.ofReal
            (∫ ω, (X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω) ∂μ) := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [hnonneg] with ω hω
          rw [Real.norm_eq_abs, abs_of_nonneg hω]
      _ = ENNReal.ofReal (μ[X t] - μ[X (dyadicRightApprox t n)]) := by
          rw [integral_sub (hX.integrable t) integrable_condExp,
            integral_condExp (ℱ.le t)]
  rw [hEq]
  -- Proof comment: after rewriting the `L¹` norm as the expectation gap, continuity of `ENNReal`
  -- `ofReal` transports the vanishing real gap to the desired `eLpNorm` limit.
  simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hGapTendsto

/-- Helper for Theorem 21.24: the time-`t` conditional expectations of the dyadic future samples
converge back to the original slice `X t` in measure. -/
private lemma tendstoInMeasure_condExp_dyadicRightApprox_to_slice
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (t : NNReal) :
    TendstoInMeasure
      μ
      (fun n ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω)
      atTop
      (fun ω ↦ X t ω) := by
  have hmeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω) μ := by
    intro n
    exact (stronglyMeasurable_condExp.mono (ℱ.le t)).aestronglyMeasurable
  have hXt_meas : AEStronglyMeasurable (fun ω ↦ X t ω) μ :=
    ((hX.stronglyMeasurable t).mono (ℱ.le t)).aestronglyMeasurable
  have hL1 :
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω) - fun ω ↦ X t ω)
            1 μ)
        atTop
        (𝓝 0) := by
    have hEq :
        (fun n : ℕ ↦
          eLpNorm
            ((fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω) - fun ω ↦ X t ω)
            1 μ) =
          fun n : ℕ ↦
            eLpNorm
              (fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)
              1 μ := by
      funext n
      calc
        eLpNorm
            ((fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω) - fun ω ↦ X t ω)
            1 μ
            = eLpNorm
                (fun ω ↦ -(X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω))
                1 μ := by
                  refine eLpNorm_congr_ae ?_
                  exact ae_of_all μ (fun ω ↦ by
                    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc])
        _ = eLpNorm
              (fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)
              1 μ := by
                have hneg :
                    (fun ω ↦ -(X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)) =
                      -(fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω) := rfl
                rw [hneg, eLpNorm_neg]
    rw [hEq]
    exact
      tendsto_eLpNorm_condExp_dyadicRightApprox_sub_slice
        (X := X) (μ := μ) (ℱ := ℱ) hX hEX_rc t
  -- Proof comment: `L¹` convergence of the conditional expectations is stronger than
  -- convergence in measure.
  exact
    tendstoInMeasure_of_tendsto_eLpNorm
      one_ne_zero
      hmeas
      hXt_meas
      hL1

/-- Helper for Theorem 21.24: almost-sure convergence of the dyadic future samples to an
`ℱ t`-measurable candidate already gives convergence in measure to that same candidate. -/
private lemma tendstoInMeasure_dyadicRightApprox_to_candidate
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (dyadicRightApprox t n) ω) atTop (𝓝 (Xtilde t ω))) :
    TendstoInMeasure
      μ
      (fun n ω ↦ X (dyadicRightApprox t n) ω)
      atTop
      (fun ω ↦ Xtilde t ω) := by
  have hmeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω ↦ X (dyadicRightApprox t n) ω) μ := by
    intro n
    exact ((hX.stronglyMeasurable (dyadicRightApprox t n)).mono
      (ℱ.le (dyadicRightApprox t n))).aestronglyMeasurable
  -- Proof comment: convergence almost everywhere of an a.e.-strongly measurable family upgrades
  -- directly to convergence in measure.
  exact tendstoInMeasure_of_tendsto_ae hmeas hXt_lim

/-- Helper for Theorem 21.24: once the dyadic future samples form a uniformly integrable family,
their conditional expectations back to `ℱ t` converge in measure to the `ℱ t`-measurable
candidate limit. -/
private lemma tendstoInMeasure_condExp_dyadicRightApprox_to_candidate_of_ui
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (dyadicRightApprox t n) ω) atTop (𝓝 (Xtilde t ω)))
    (hFutureUI :
      UniformIntegrable (fun n : ℕ => fun ω ↦ X (dyadicRightApprox t n) ω) 1 μ) :
    TendstoInMeasure
      μ
      (fun n ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω)
      atTop
      (fun ω ↦ Xtilde t ω) := by
  have hFutureMeasure :
      TendstoInMeasure
        μ
        (fun n ω ↦ X (dyadicRightApprox t n) ω)
        atTop
        (fun ω ↦ Xtilde t ω) :=
    tendstoInMeasure_dyadicRightApprox_to_candidate
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_lim
  have hXtInt : Integrable (fun ω ↦ Xtilde t ω) μ :=
    hFutureUI.integrable_of_tendstoInMeasure hFutureMeasure
  have hXt_memLp : MemLp (fun ω ↦ Xtilde t ω) 1 μ :=
    memLp_one_iff_integrable.2 hXtInt
  have hFutureMeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω ↦ X (dyadicRightApprox t n) ω) μ := by
    intro n
    exact ((hX.stronglyMeasurable (dyadicRightApprox t n)).mono
      (ℱ.le (dyadicRightApprox t n))).aestronglyMeasurable
  have hXtAEMeas : AEStronglyMeasurable (fun ω ↦ Xtilde t ω) μ :=
    (hXt_meas.mono (ℱ.le t)).aestronglyMeasurable
  have hFutureL1 :
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun ω ↦ X (dyadicRightApprox t n) ω) - fun ω ↦ Xtilde t ω)
            1 μ)
        atTop
        (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure
      le_rfl
      ENNReal.one_ne_top
      hFutureMeas
      hXt_memLp
      hFutureUI.2.1
      hFutureMeasure
  have hCondL1 :
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω) - fun ω ↦ Xtilde t ω)
            1 μ)
        atTop
        (𝓝 0) := by
    have hbound :
        ∀ n : ℕ,
          eLpNorm
              ((fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω) - fun ω ↦ Xtilde t ω)
              1 μ
            ≤
              eLpNorm
                ((fun ω ↦ X (dyadicRightApprox t n) ω) - fun ω ↦ Xtilde t ω)
                1 μ := by
      intro n
      have hcondSub :
          μ[(fun ω ↦ X (dyadicRightApprox t n) ω - Xtilde t ω) | ℱ t] =ᵐ[μ]
            (fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω) - fun ω ↦ Xtilde t ω := by
        -- Proof comment: separate the conditional expectation of the difference and collapse the
        -- candidate term because it is already `ℱ t`-measurable.
        calc
          μ[(fun ω ↦ X (dyadicRightApprox t n) ω - Xtilde t ω) | ℱ t]
              =ᵐ[μ]
                μ[(fun ω ↦ X (dyadicRightApprox t n) ω) | ℱ t] -
                  μ[(fun ω ↦ Xtilde t ω) | ℱ t] := by
                    exact condExp_sub (hX.integrable (dyadicRightApprox t n)) hXtInt (ℱ t)
          _ = (fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω) - fun ω ↦ Xtilde t ω := by
                rw [condExp_of_stronglyMeasurable (ℱ.le t) hXt_meas hXtInt]
      calc
        eLpNorm
            ((fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω) - fun ω ↦ Xtilde t ω)
            1 μ
            =
              eLpNorm
                (μ[(fun ω ↦ X (dyadicRightApprox t n) ω - Xtilde t ω) | ℱ t])
                1 μ := by
                  exact eLpNorm_congr_ae hcondSub.symm
        _ ≤ eLpNorm
              ((fun ω ↦ X (dyadicRightApprox t n) ω) - fun ω ↦ Xtilde t ω)
              1 μ := by
                exact eLpNorm_one_condExp_le_eLpNorm _
    -- Proof comment: conditional expectation is an `L¹` contraction, so the dyadic `L¹` limit
    -- to the candidate persists after conditioning back to `ℱ t`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      hFutureL1
      (Eventually.of_forall fun n ↦ zero_le _)
      (Eventually.of_forall hbound)
  -- Proof comment: `L¹` convergence of the conditioned sequence is stronger than convergence in
  -- measure.
  exact
    tendstoInMeasure_of_tendsto_eLpNorm
      one_ne_zero
      (fun n ↦ (stronglyMeasurable_condExp.mono (ℱ.le t)).aestronglyMeasurable)
      hXtAEMeas
      hCondL1

/-- Helper for Theorem 21.24: precomposing a uniformly integrable family with a deterministic
index map preserves uniform integrability. -/
private lemma uniformIntegrable_comp
    {ι κ : Type*} {f : ι → Ω → ℝ}
    (hf : UniformIntegrable f 1 μ) (τ : κ → ι) :
    UniformIntegrable (fun k ω ↦ f (τ k) ω) 1 μ := by
  refine ⟨fun k ↦ hf.aestronglyMeasurable (τ k), ?_, ?_⟩
  · -- Proof comment: the small-set control is inherited pointwise from the original family.
    intro ε hε
    rcases hf.unifIntegrable hε with ⟨δ, hδ, hδ_bound⟩
    exact ⟨δ, hδ, fun k s hs hμs ↦ hδ_bound (τ k) s hs hμs⟩
  · -- Proof comment: the same global `L¹` bound works after deterministic reindexing.
    rcases hf.2.2 with ⟨C, hC⟩
    exact ⟨C, fun k ↦ hC (τ k)⟩

/-- Helper for Theorem 21.24: on a bounded horizon, the negative part of an earlier slice is
dominated by the conditional expectation of the terminal negative part. -/
private lemma negPart_slice_le_condExp_terminalNegPart
    (hX : Supermartingale X ℱ μ) {q : NNReal} (s : {u : NNReal // u ≤ q}) :
    (fun ω ↦ (-X s.1 ω)⁺) ≤ᵐ[μ] μ[(fun ω ↦ (-X q ω)⁺) | ℱ s.1] := by
  have hslice :
      -X s.1 ≤ᵐ[μ] μ[(fun ω ↦ -X q ω) | ℱ s.1] :=
    hX.neg.ae_le_condExp s.2
  have hmono :
      μ[(fun ω ↦ -X q ω) | ℱ s.1] ≤ᵐ[μ] μ[(fun ω ↦ (-X q ω)⁺) | ℱ s.1] := by
    refine condExp_mono (m := ℱ s.1) (hX.integrable q).neg (hX.integrable q).neg_part ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      exact le_max_left (-X q ω) 0
  have hnonneg :
      0 ≤ᵐ[μ] μ[(fun ω ↦ (-X q ω)⁺) | ℱ s.1] :=
    condExp_nonneg <| Filter.Eventually.of_forall fun ω ↦ posPart_nonneg (-X q ω)
  -- Proof comment: combine the supermartingale lower bound for `-X` with monotonicity of
  -- conditional expectation and nonnegativity of the terminal negative part.
  filter_upwards [hslice, hmono, hnonneg] with ω hsliceω hmonoω hnonnegω
  change max (-X s.1 ω) 0 ≤ μ[(fun ω ↦ (-X q ω)⁺) | ℱ s.1] ω
  exact max_le_iff.mpr ⟨le_trans hsliceω hmonoω, hnonnegω⟩

/-- Helper for Theorem 21.24: the bounded-horizon negative-part slice family is uniformly
integrable. -/
private lemma boundedHorizonNegPartUniformIntegrable
    (hX : Supermartingale X ℱ μ) (q : NNReal) :
    UniformIntegrable (fun s : {u : NNReal // u ≤ q} ↦ fun ω ↦ (-X s.1 ω)⁺) 1 μ := by
  let g : Ω → ℝ := fun ω ↦ (-X q ω)⁺
  have hUIg :
      UniformIntegrable
        (fun s : {u : NNReal // u ≤ q} ↦ μ[g | ℱ s.1])
        1 μ := by
    simpa [g] using
      (Integrable.uniformIntegrable_condExp
        (μ := μ)
        (hint := (hX.integrable q).neg_part)
        (ℱ := fun s : {u : NNReal // u ≤ q} ↦ ℱ s.1)
        (fun s : {u : NNReal // u ≤ q} ↦ ℱ.le s.1))
  refine MeasureTheory.uniformIntegrable_of le_rfl ENNReal.one_ne_top ?_ ?_
  · intro s
    -- Proof comment: each negative-part slice is measurable because each supermartingale slice is.
    have hsMeas :
        Measurable (fun ω ↦ (-X s.1 ω)⁺) :=
      (((hX.stronglyMeasurable s.1).mono (ℱ.le s.1)).measurable.neg.max measurable_const)
    exact hsMeas.aestronglyMeasurable
  · intro ε hε
    obtain ⟨C, hC⟩ := hUIg.spec one_ne_zero ENNReal.one_ne_top hε
    refine ⟨C, fun s ↦ ?_⟩
    have hnonneg :
        0 ≤ᵐ[μ] μ[g | ℱ s.1] :=
      condExp_nonneg <| Filter.Eventually.of_forall fun ω ↦ by
        dsimp [g]
        exact posPart_nonneg (-X q ω)
    have hdom :
        ∀ᵐ ω ∂μ,
          ‖({ω | C ≤ ‖(-X s.1 ω)⁺‖₊}.indicator (fun ω ↦ (-X s.1 ω)⁺) ω)‖ ≤
            {ω | C ≤ ‖μ[g | ℱ s.1] ω‖₊}.indicator (fun ω ↦ μ[g | ℱ s.1] ω) ω := by
      filter_upwards
        [negPart_slice_le_condExp_terminalNegPart (X := X) (μ := μ) (ℱ := ℱ) hX s, hnonneg] with
          ω hle hnonnegω
      by_cases hCω : C ≤ ‖(-X s.1 ω)⁺‖₊
      · have hle' : (-X s.1 ω)⁺ ≤ μ[g | ℱ s.1] ω := hle
        have hCωNeg : C ≤ ‖(X s.1 ω)⁻‖₊ := by
          simpa using hCω
        have hCω' : C ≤ ‖μ[g | ℱ s.1] ω‖₊ := by
          rw [Real.nnnorm_of_nonneg (posPart_nonneg (-X s.1 ω))] at hCω
          rw [Real.nnnorm_of_nonneg hnonnegω]
          exact hCω.trans hle'
        have hleft :
            ‖({ω | C ≤ ‖(-X s.1 ω)⁺‖₊}.indicator (fun ω ↦ (-X s.1 ω)⁺) ω)‖ =
              (X s.1 ω)⁻ := by
          simp [hCωNeg, Real.norm_eq_abs, abs_of_nonneg (negPart_nonneg (X s.1 ω))]
        have hright :
            {ω | C ≤ ‖μ[g | ℱ s.1] ω‖₊}.indicator (fun ω ↦ μ[g | ℱ s.1] ω) ω =
              μ[g | ℱ s.1] ω := by
          simp [hCω']
        rw [hleft, hright]
        exact hle'
      · have hRhsNonneg :
            0 ≤ {ω | C ≤ ‖μ[g | ℱ s.1] ω‖₊}.indicator (fun ω ↦ μ[g | ℱ s.1] ω) ω := by
          by_cases hCω' : C ≤ ‖μ[g | ℱ s.1] ω‖₊
          · simpa [hCω'] using hnonnegω
          · simp [hCω']
        have hCωNeg : ¬ C ≤ ‖(X s.1 ω)⁻‖₊ := by
          simpa using hCω
        have hleft :
            ‖({ω | C ≤ ‖(-X s.1 ω)⁺‖₊}.indicator (fun ω ↦ (-X s.1 ω)⁺) ω)‖ = 0 := by
          simp [hCωNeg]
        rw [hleft]
        exact hRhsNonneg
    -- Proof comment: the dominated tail indicators inherit the owner tail bound from the
    -- conditional-expectation family.
    exact (eLpNorm_mono_ae_real hdom).trans (hC s)

/-- Helper for Theorem 21.24: bounded-horizon deterministic slices of a supermartingale have a
uniform `L¹` bound. -/
private lemma boundedHorizonELpNormOneBounded
    (hX : Supermartingale X ℱ μ) (q : NNReal) :
    ∃ C : NNReal, ∀ s : {u : NNReal // u ≤ q}, eLpNorm (X s.1) 1 μ ≤ C := by
  have hNegUI :
      UniformIntegrable (fun s : {u : NNReal // u ≤ q} ↦ fun ω ↦ (-X s.1 ω)⁺) 1 μ :=
    boundedHorizonNegPartUniformIntegrable (X := X) (μ := μ) (ℱ := ℱ) hX q
  rcases hNegUI.2.2 with ⟨Cneg, hCneg⟩
  have hnegBound : ∀ s : {u : NNReal // u ≤ q}, μ[fun ω ↦ (-X s.1 ω)⁺] ≤ (Cneg : ℝ) := by
    intro s
    have hsInt : Integrable (fun ω ↦ (-X s.1 ω)⁺) μ := by
      simpa using (hX.integrable s.1).neg_part
    have hsBound : eLpNorm (fun ω ↦ (-X s.1 ω)⁺) 1 μ ≤ Cneg := hCneg s
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm hsInt] at hsBound
    -- Proof comment: for the nonnegative negative-part owner, the `L¹` norm is exactly the
    -- expectation itself.
    simpa [Real.norm_eq_abs, abs_of_nonneg, negPart_nonneg] using
      (ENNReal.ofReal_le_coe).1 hsBound
  let C : NNReal := ⟨|μ[X 0]| + 2 * (Cneg : ℝ), by positivity⟩
  refine ⟨C, fun s ↦ ?_⟩
  have hmono : μ[X s.1] ≤ μ[X 0] := by
    -- Proof comment: supermartingale expectations decrease along deterministic times.
    simpa [MeasureTheory.setIntegral_univ] using
      hX.setIntegral_le (show (0 : NNReal) ≤ s.1 by exact zero_le _) MeasurableSet.univ
  have hdecomp :
      μ[X s.1] = μ[fun ω ↦ (X s.1 ω)⁺] - μ[fun ω ↦ (-X s.1 ω)⁺] := by
    -- Proof comment: split the slice expectation into positive and negative parts.
    simpa using integral_eq_integral_pos_part_sub_integral_neg_part (hX.integrable s.1)
  have hposBound : μ[fun ω ↦ (X s.1 ω)⁺] ≤ |μ[X 0]| + (Cneg : ℝ) := by
    -- Proof comment: once the negative-part expectation is uniformly bounded, the
    -- supermartingale expectation monotonicity bounds the positive parts as well.
    have haux : μ[fun ω ↦ (X s.1 ω)⁺] ≤ μ[X 0] + μ[fun ω ↦ (-X s.1 ω)⁺] := by
      linarith [hmono, hdecomp]
    exact le_trans haux <| by
      calc
        μ[X 0] + μ[fun ω ↦ (-X s.1 ω)⁺] ≤ |μ[X 0]| + μ[fun ω ↦ (-X s.1 ω)⁺] := by
          exact add_le_add (le_abs_self _) le_rfl
        _ ≤ |μ[X 0]| + (Cneg : ℝ) := add_le_add le_rfl (hnegBound s)
  have hposInt : Integrable (fun ω ↦ (X s.1 ω)⁺) μ := by
    simpa using (hX.integrable s.1).pos_part
  have hnegInt : Integrable (fun ω ↦ (-X s.1 ω)⁺) μ := by
    simpa using (hX.integrable s.1).neg_part
  have hnorm_eq : ∀ ω, ‖X s.1 ω‖ = (X s.1 ω)⁺ + (-X s.1 ω)⁺ := by
    intro ω
    by_cases hω : 0 ≤ X s.1 ω
    · -- Proof comment: on the nonnegative branch, the negative part vanishes.
      rw [Real.norm_eq_abs, abs_of_nonneg hω, posPart_eq_self.2 hω, posPart_eq_zero.2 (neg_nonpos.mpr hω),
        add_zero]
    · have hω' : X s.1 ω ≤ 0 := le_of_not_ge hω
      -- Proof comment: on the nonpositive branch, the positive part vanishes and the negative
      -- part records the absolute value.
      rw [Real.norm_eq_abs, abs_of_nonpos hω', posPart_eq_zero.2 hω',
        posPart_eq_self.2 (neg_nonneg.mpr hω'), zero_add]
  have hnormBound : ∫ ω, ‖X s.1 ω‖ ∂μ ≤ |μ[X 0]| + 2 * (Cneg : ℝ) := by
    -- Proof comment: rewrite the norm as positive plus negative part and combine the two horizon
    -- expectation bounds.
    calc
      ∫ ω, ‖X s.1 ω‖ ∂μ = ∫ ω, ((X s.1 ω)⁺ + (-X s.1 ω)⁺) ∂μ := by
        refine integral_congr_ae ?_
        exact ae_of_all μ hnorm_eq
      _ = μ[fun ω ↦ (X s.1 ω)⁺] + μ[fun ω ↦ (-X s.1 ω)⁺] := by
        rw [integral_add hposInt hnegInt]
      _ ≤ (|μ[X 0]| + (Cneg : ℝ)) + (Cneg : ℝ) := add_le_add hposBound (hnegBound s)
      _ = |μ[X 0]| + 2 * (Cneg : ℝ) := by ring
  calc
    eLpNorm (X s.1) 1 μ = ENNReal.ofReal (∫ ω, ‖X s.1 ω‖ ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm,
        ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable s.1)]
    _ ≤ ENNReal.ofReal (|μ[X 0]| + 2 * (Cneg : ℝ)) := ENNReal.ofReal_le_ofReal hnormBound
    _ = C := by
      simpa [C] using
        (ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ |μ[X 0]| + 2 * (Cneg : ℝ) by positivity))

/-- Helper for Theorem 21.24: the clipped dyadic row `k ↦ dyadicPointUpTo q n k` is monotone in
the row index. -/
private lemma monotone_dyadicPointUpTo (q : NNReal) (n : ℕ) :
    Monotone (dyadicPointUpTo q n) := by
  intro i j hij
  -- Proof comment: the unclipped dyadic times are monotone in `k`, and taking `min q` preserves
  -- that monotonicity.
  dsimp [dyadicPointUpTo]
  refine min_le_min_left _ ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hij' : (i : NNReal) ≤ j := by
    exact_mod_cast hij
  have hinv_nonneg : 0 ≤ ((2 : NNReal) ^ n)⁻¹ := by
    positivity
  exact mul_le_mul_of_nonneg_right hij' hinv_nonneg

/-- Helper for Theorem 21.24: on a fixed bounded horizon, each clipped dyadic row of `-X` has
almost surely finite rational upcrossings. -/
private lemma aeLtTop_boundedHorizonDyadicNegRowUpcrossings
    (hX : Supermartingale X ℱ μ)
    (q : NNReal) (n : ℕ) {a b : ℚ} (hab : a < b) :
    ∀ᵐ ω ∂μ,
      upcrossings (a : ℝ) (b : ℝ) (fun k ω ↦ -X (dyadicPointUpTo q n k) ω) ω < ∞ := by
  let τ : ℕ → NNReal := dyadicPointUpTo q n
  have hτ : Monotone τ := monotone_dyadicPointUpTo q n
  have hrow :
      Submartingale (fun k ω ↦ -X (τ k) ω) (sampledFiltration21_24 (ℱ := ℱ) τ hτ) μ := by
    -- Proof comment: negating the supermartingale turns the clipped row into a discrete
    -- submartingale on the sampled filtration.
    simpa [τ] using
      sampledSubmartingaleOfMonotone21_24
        (μ := μ)
        (ℱ := ℱ)
        (Y := fun t ω ↦ -X t ω)
        hX.neg
        hτ
  obtain ⟨R, hR⟩ :=
    boundedHorizonELpNormOneBounded
      (X := X)
      (μ := μ)
      (ℱ := ℱ)
      hX
      q
  -- Proof comment: the bounded-horizon `L¹` owner controls every clipped row term, so the
  -- discrete upcrossing theorem applies to the sampled submartingale.
  exact hrow.upcrossings_ae_lt_top'
    (R := R)
    (a := (a : ℝ))
    (b := (b : ℝ))
    (hab := Rat.cast_lt.2 hab)
    (fun k ↦ by
      have hτk_le : τ k ≤ q := (dyadicPointUpTo_mem_Icc q n k).2
      calc
        eLpNorm (fun ω ↦ -X (dyadicPointUpTo q n k) ω) 1 μ
            = eLpNorm (fun ω ↦ X (dyadicPointUpTo q n k) ω) 1 μ := by
                have hneg :
                    (fun ω ↦ -X (dyadicPointUpTo q n k) ω) =
                      -(fun ω ↦ X (dyadicPointUpTo q n k) ω) := rfl
                rw [hneg, eLpNorm_neg]
        _ ≤ R := by
            simpa [τ] using hR ⟨τ k, hτk_le⟩)

/-- Helper for Theorem 21.24: for one fixed bounded horizon `q`, almost every sample point has
finite rational upcrossings on every clipped dyadic row of `-X`. -/
private lemma aeAll_boundedHorizonDyadicNegRowUpcrossings
    (hX : Supermartingale X ℱ μ) (q : NNReal) :
    ∀ᵐ ω ∂μ,
      ∀ n : ℕ, ∀ a b : ℚ, a < b →
        upcrossings (a : ℝ) (b : ℝ) (fun k ω ↦ -X (dyadicPointUpTo q n k) ω) ω < ∞ := by
  -- Proof comment: intersect the rowwise discrete upcrossing events over the countable family of
  -- dyadic rows and rational intervals on the fixed horizon `q`.
  simp only [ae_all_iff, eventually_imp_distrib_left]
  intro n a b hab
  exact aeLtTop_boundedHorizonDyadicNegRowUpcrossings
    (X := X)
    (μ := μ)
    (ℱ := ℱ)
    hX
    q
    n
    hab

/-- Helper for Theorem 21.24: refining one clipped dyadic row to the next finer row doubles the
available horizon while preserving every coarse crossing witness at the corresponding even index. -/
private lemma dyadicNegRowCrossingTime_le_refine21_24
    {q : NNReal} {a b : ℝ} (n N k : ℕ) (ω : Ω) :
    upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q (n + 1) j) ω) (2 * N) k ω ≤
        2 * upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N k ω ∧
      lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q (n + 1) j) ω) (2 * N) k ω ≤
        2 * lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N k ω := by
  induction k with
  | zero =>
      refine ⟨by simp, ?_⟩
      by_cases hcoarse :
          lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N 0 ω = N
      · -- Proof comment: if the coarse lower crossing already stops at the horizon, the refined
        -- lower crossing is bounded by the doubled horizon automatically.
        simpa [hcoarse] using
          (lowerCrossingTime_le
            (a := a)
            (b := b)
            (f := fun j ω ↦ -X (dyadicPointUpTo q (n + 1) j) ω)
            (N := 2 * N)
            (n := 0)
            (ω := ω))
      · have hcoarse_lt :
            lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N 0 ω < N :=
          lt_of_le_of_ne lowerCrossingTime_le hcoarse
        have hmem :
            -X (dyadicPointUpTo q n
              (lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N 0 ω)) ω ∈
              Set.Iic a := by
          -- Proof comment: a genuine coarse lower crossing gives a lower-barrier witness on the
          -- coarse row.
          simpa [lowerCrossingTime] using
            (hittingBtwn_mem_set_of_hittingBtwn_lt
              (u := fun j ω ↦ -X (dyadicPointUpTo q n j) ω)
              (s := Set.Iic a)
              (n :=
                upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N 0 ω)
              (m := N)
              (ω := ω)
              hcoarse_lt)
        have hmem_refined :
            -X (dyadicPointUpTo q (n + 1)
              (2 *
                lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N 0 ω)) ω ∈
              Set.Iic a := by
          have hrefine :
              dyadicPointUpTo q (n + 1)
                  (2 *
                    lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N 0 ω) =
                dyadicPointUpTo q n
                  (lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N 0 ω) := by
            simpa using
              (dyadicPointUpTo_even (T := q) n
                (lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N 0 ω))
          rw [hrefine]
          exact hmem
        -- Proof comment: the same even index is a valid lower-crossing witness on the refined
        -- row.
        rw [lowerCrossingTime]
        refine hittingBtwn_le_of_mem ?_ ?_ hmem_refined
        · simp
        · exact Nat.mul_le_mul_left 2 lowerCrossingTime_le
  | succ k ih =>
      have ihUpper := ih.1
      have ihLower := ih.2
      have hUpper :
          upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q (n + 1) j) ω) (2 * N) (k + 1) ω ≤
            2 * upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω := by
        by_cases hcoarse :
            upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω = N
        · -- Proof comment: once the coarse upper crossing has stabilized at the horizon, the
          -- refined upper crossing is bounded by the doubled horizon for free.
          simpa [hcoarse] using
            (upperCrossingTime_le
              (a := a)
              (b := b)
              (f := fun j ω ↦ -X (dyadicPointUpTo q (n + 1) j) ω)
              (N := 2 * N)
              (n := k + 1)
              (ω := ω))
        · have hcoarse_lt :
              upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω < N :=
            lt_of_le_of_ne upperCrossingTime_le hcoarse
          have hmem :
              -X (dyadicPointUpTo q n
                (upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω)) ω ∈
                Set.Ici b := by
            -- Proof comment: a genuine coarse upper crossing remains an upper witness after
            -- doubling the index.
            simpa [upperCrossingTime_succ_eq (ω := ω)] using
              (hittingBtwn_mem_set_of_hittingBtwn_lt
                (u := fun j ω ↦ -X (dyadicPointUpTo q n j) ω)
                (s := Set.Ici b)
                (n :=
                  lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N k ω)
                (m := N)
                (ω := ω)
                hcoarse_lt)
          have hmem_refined :
              -X (dyadicPointUpTo q (n + 1)
                (2 *
                  upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω)) ω ∈
                Set.Ici b := by
            have hrefine :
                dyadicPointUpTo q (n + 1)
                    (2 *
                      upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω) =
                  dyadicPointUpTo q n
                    (upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω) := by
              simpa using
                (dyadicPointUpTo_even (T := q) n
                  (upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω))
            rw [hrefine]
            exact hmem
          rw [upperCrossingTime_succ_eq ω]
          refine hittingBtwn_le_of_mem ?_ ?_ hmem_refined
          · exact le_trans ihLower (Nat.mul_le_mul_left 2 lowerCrossingTime_le_upperCrossingTime_succ)
          · exact Nat.mul_le_mul_left 2 upperCrossingTime_le
      have hLower :
          lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q (n + 1) j) ω) (2 * N) (k + 1) ω ≤
            2 * lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω := by
        by_cases hcoarse :
            lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω = N
        · -- Proof comment: the lower crossing case has the same stabilization behavior.
          simpa [hcoarse] using
            (lowerCrossingTime_le
              (a := a)
              (b := b)
              (f := fun j ω ↦ -X (dyadicPointUpTo q (n + 1) j) ω)
              (N := 2 * N)
              (n := k + 1)
              (ω := ω))
        · have hcoarse_lt :
              lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω < N :=
            lt_of_le_of_ne lowerCrossingTime_le hcoarse
          have hmem :
              -X (dyadicPointUpTo q n
                (lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω)) ω ∈
                Set.Iic a := by
            -- Proof comment: after the refined upper crossing, the doubled coarse lower crossing
            -- is still a valid lower witness.
            simpa [lowerCrossingTime] using
              (hittingBtwn_mem_set_of_hittingBtwn_lt
                (u := fun j ω ↦ -X (dyadicPointUpTo q n j) ω)
                (s := Set.Iic a)
                (n :=
                  upperCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω)
                (m := N)
                (ω := ω)
                hcoarse_lt)
          have hmem_refined :
              -X (dyadicPointUpTo q (n + 1)
                (2 *
                  lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω)) ω ∈
                Set.Iic a := by
            have hrefine :
                dyadicPointUpTo q (n + 1)
                    (2 *
                      lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω) =
                  dyadicPointUpTo q n
                    (lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω) := by
              simpa using
                (dyadicPointUpTo_even (T := q) n
                  (lowerCrossingTime a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N (k + 1) ω))
            rw [hrefine]
            exact hmem
          rw [lowerCrossingTime]
          refine hittingBtwn_le_of_mem ?_ ?_ hmem_refined
          · exact le_trans hUpper (Nat.mul_le_mul_left 2 upperCrossingTime_le_lowerCrossingTime)
          · exact Nat.mul_le_mul_left 2 lowerCrossingTime_le
      exact ⟨hUpper, hLower⟩

/-- Helper for Theorem 21.24: refining the clipped dyadic row cannot decrease finite-horizon
upcrossings of `-X`. -/
private lemma dyadicNegRowUpcrossingsBefore_le_succ21_24
    {q : NNReal} {a b : ℝ} (hab : a < b) (n N : ℕ) (ω : Ω) :
    upcrossingsBefore a b (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) N ω ≤
      upcrossingsBefore a b (fun j ω ↦ -X (dyadicPointUpTo q (n + 1) j) ω) (2 * N) ω := by
  -- Proof comment: every coarse crossing survives in the refined row at an even index before the
  -- doubled horizon.
  simp only [upcrossingsBefore]
  gcongr sSup {k | ?_} with k
  · exact upperCrossingTime_lt_bddAbove hab
  · intro hk
    exact lt_of_le_of_lt
      (dyadicNegRowCrossingTime_le_refine21_24 (X := X) (q := q) (a := a) (b := b) n N k ω).1
      (Nat.mul_lt_mul_of_pos_left hk (by decide))

/-- Helper for Theorem 21.24: the full upcrossing count of a clipped dyadic row of `-X` is
monotone under row refinement. -/
private lemma dyadicNegRowUpcrossings_mono21_24
    {q : NNReal} {a b : ℚ} (hab : a < b) (ω : Ω) :
    Monotone (fun n ↦
      upcrossings (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo q n j) ω) ω) := by
  -- Proof comment: taking the supremum over finite horizons turns the doubled-horizon comparison
  -- into monotonicity of the full clipped-row envelope.
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [upcrossings]
  refine iSup_le fun N ↦ ?_
  refine le_iSup_of_le (2 * N) ?_
  exact_mod_cast
    (dyadicNegRowUpcrossingsBefore_le_succ21_24
      (X := X)
      (q := q)
      (a := (a : ℝ))
      (b := (b : ℝ))
      (hab := Rat.cast_lt.2 hab)
      n
      N
      ω)

/-- Helper for Theorem 21.24: on one fixed natural horizon, the monotone envelope of all clipped
dyadic-row upcrossings of `-X` is almost surely finite. -/
private lemma aeLtTop_boundedHorizonDyadicNegRowEnvelope21_24
    (hX : Supermartingale X ℱ μ)
    (q : ℕ) {a b : ℚ} (hab : a < b) :
    ∀ᵐ ω ∂μ,
      (⨆ n : ℕ,
        upcrossings (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω) < ∞ := by
  obtain ⟨R, hR⟩ :=
    boundedHorizonELpNormOneBounded (X := X) (μ := μ) (ℱ := ℱ) hX (q : NNReal)
  let U : ℕ → Ω → ℝ≥0∞ := fun n ω ↦
    upcrossings (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω
  let C : ℝ≥0∞ := R + ‖(a : ℝ)‖₊ * μ Set.univ
  have hR' :
      ∀ s : {u : NNReal // u ≤ (q : NNReal)},
        ∫⁻ ω, ‖-X s.1 ω - (a : ℝ)‖₊ ∂μ ≤ C := by
    intro s
    refine
      (lintegral_mono ?_ :
        ∫⁻ ω, ‖-X s.1 ω - (a : ℝ)‖₊ ∂μ ≤
          ∫⁻ ω, ‖-X s.1 ω‖₊ + ‖(a : ℝ)‖₊ ∂μ).trans ?_
    · intro ω
      simp_rw [sub_eq_add_neg, ← nnnorm_neg (a : ℝ), ← ENNReal.coe_add, ENNReal.coe_le_coe]
      exact nnnorm_add_le _ _
    · simp_rw [lintegral_add_right _ measurable_const]
      rw [lintegral_const]
      have hnormX :
          ∫⁻ ω, ‖X s.1 ω‖₊ ∂μ ≤ R := by
        simpa [eLpNorm_one_eq_lintegral_enorm] using hR s
      have hnorm :
          ∫⁻ ω, ‖-X s.1 ω‖₊ ∂μ ≤ R := by
        simpa using hnormX
      exact add_le_add hnorm le_rfl
  have hrow :
      ∀ n,
        Submartingale
          (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω)
          (sampledFiltration21_24 (ℱ := ℱ) (dyadicPointUpTo (q : NNReal) n)
            (monotone_dyadicPointUpTo (q : NNReal) n))
          μ := by
    intro n
    -- Proof comment: each clipped row of `-X` is a deterministically sampled discrete
    -- submartingale.
    simpa using
      sampledSubmartingaleOfMonotone21_24
        (μ := μ)
        (ℱ := ℱ)
        (Y := fun t ω ↦ -X t ω)
        hX.neg
        (monotone_dyadicPointUpTo (q : NNReal) n)
  have hmeas : ∀ n, Measurable (U n) := by
    intro n
    -- Proof comment: upcrossings are measurable because the sampled row is strongly adapted.
    exact (hrow n).stronglyAdapted.measurable_upcrossings (Rat.cast_lt.2 hab)
  have hrowBound :
      ∀ n, ∫⁻ ω, U n ω ∂μ ≤ C / ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
    intro n
    have hup :
        ENNReal.ofReal ((b : ℝ) - (a : ℝ)) * ∫⁻ ω, U n ω ∂μ ≤
          ⨆ N : ℕ,
            ∫⁻ ω,
              ENNReal.ofReal
                (((fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) N ω - (a : ℝ))⁺) ∂μ := by
      simpa [U] using
        (hrow n).mul_lintegral_upcrossings_le_lintegral_pos_part
          (a := (a : ℝ))
          (b := (b : ℝ))
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le] at hup
    · refine hup.trans ?_
      gcongr
      refine iSup_le fun N ↦ ?_
      have hpointwise :
          ∀ ω,
            ENNReal.ofReal
                (((fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) N ω - (a : ℝ))⁺) ≤
              ‖-X (dyadicPointUpTo (q : NNReal) n N) ω - (a : ℝ)‖₊ := by
        intro ω
        rw [ENNReal.ofReal_le_iff_le_toReal, ENNReal.coe_toReal, coe_nnnorm]
        · by_cases hnonneg : 0 ≤ -X (dyadicPointUpTo (q : NNReal) n N) ω - (a : ℝ)
          · rw [posPart_eq_self.2 hnonneg, Real.norm_eq_abs, abs_of_nonneg hnonneg]
          · have hnonpos : -X (dyadicPointUpTo (q : NNReal) n N) ω - (a : ℝ) ≤ 0 :=
              le_of_not_ge hnonneg
            rw [posPart_eq_zero.2 hnonpos]
            exact norm_nonneg _
        · finiteness
      have hτN :
          dyadicPointUpTo (q : NNReal) n N ≤ (q : NNReal) :=
        (dyadicPointUpTo_mem_Icc (q : NNReal) n N).2
      exact
        (lintegral_mono hpointwise).trans
          (by
            simpa [C] using
              hR' ⟨dyadicPointUpTo (q : NNReal) n N, hτN⟩)
    · left
      simp only [Ne, ENNReal.ofReal_eq_zero, sub_nonpos, not_le]
      exact Rat.cast_lt.2 hab
    · left
      finiteness
  have hlintegral :
      ∫⁻ ω, (⨆ n : ℕ, U n ω) ∂μ = ⨆ n : ℕ, ∫⁻ ω, U n ω ∂μ := by
    -- Proof comment: monotonicity of the clipped-row envelope lets monotone convergence move the
    -- supremum past the integral.
    rw [lintegral_iSup']
    · intro n
      exact (hmeas n).aemeasurable
    · filter_upwards with ω n m hnm
      exact dyadicNegRowUpcrossings_mono21_24 (X := X) (q := (q : NNReal)) hab ω hnm
  have hEnvelopeBound :
      ∫⁻ ω, (⨆ n : ℕ, U n ω) ∂μ ≤ C / ENNReal.ofReal ((b : ℝ) - (a : ℝ)) := by
    rw [hlintegral]
    exact iSup_le hrowBound
  have hEnvelopeMeas : Measurable (fun ω ↦ ⨆ n : ℕ, U n ω) := by
    exact Measurable.iSup fun n ↦ hmeas n
  have hEnvelopeFinite : ∫⁻ ω, (⨆ n : ℕ, U n ω) ∂μ ≠ ∞ := by
    refine (lt_of_le_of_lt hEnvelopeBound ?_).ne
    have hden : ENNReal.ofReal ((b : ℝ) - (a : ℝ)) ≠ 0 := by
      have hsubpos : 0 < (b : ℝ) - (a : ℝ) := sub_pos.mpr (Rat.cast_lt.2 hab)
      exact (ENNReal.ofReal_pos.mpr hsubpos).ne'
    exact ENNReal.div_lt_top
      (by simpa [C] using ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, by simp⟩)
      hden
  filter_upwards [ae_lt_top hEnvelopeMeas hEnvelopeFinite] with ω hω
  exact hω

/-- Helper for Theorem 21.24: for one fixed natural horizon, the clipped-row envelope is almost
surely finite simultaneously for all rational intervals. -/
private lemma aeAll_boundedHorizonDyadicNegRowEnvelope21_24
    (hX : Supermartingale X ℱ μ) (q : ℕ) :
    ∀ᵐ ω ∂μ,
      ∀ a b : ℚ, a < b →
        (⨆ n : ℕ,
          upcrossings (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω) < ∞ := by
  simp only [ae_all_iff, eventually_imp_distrib_left]
  intro a b hab
  exact aeLtTop_boundedHorizonDyadicNegRowEnvelope21_24
    (X := X)
    (μ := μ)
    (ℱ := ℱ)
    hX
    q
    hab

/-- Helper for Theorem 21.24: there is one full-measure event on which every natural-horizon
clipped dyadic-row envelope of `-X` is finite on every rational interval. -/
private lemma existsFullMeasureDyadicNegRowEnvelopeEvent
    (hX : Supermartingale X ℱ μ)
    (hNullMeas : ∀ t : NNReal, ∀ {s : Set Ω}, μ s = 0 → MeasurableSet[ℱ t] s) :
    ∃ A : Set Ω,
      μ Aᶜ = 0 ∧
        (∀ t : NNReal, MeasurableSet[ℱ t] A) ∧
        ∀ ω ∈ A,
          ∀ q : ℕ, ∀ a b : ℚ, a < b →
            (⨆ n : ℕ,
              upcrossings (a : ℝ) (b : ℝ)
                (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω) < ∞ := by
  let A : Set Ω := {ω |
    ∀ q : ℕ, ∀ a b : ℚ, a < b →
      (⨆ n : ℕ,
        upcrossings (a : ℝ) (b : ℝ)
          (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω) < ∞}
  have hAprop :
      ∀ᵐ ω ∂μ,
        ∀ q : ℕ, ∀ a b : ℚ, a < b →
          (⨆ n : ℕ,
            upcrossings (a : ℝ) (b : ℝ)
              (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω) < ∞ := by
    rw [ae_all_iff]
    intro q
    exact aeAll_boundedHorizonDyadicNegRowEnvelope21_24
      (X := X)
      (μ := μ)
      (ℱ := ℱ)
      hX
      q
  have hAae : ∀ᵐ ω ∂μ, ω ∈ A := by
    -- Proof comment: intersect the fixed-horizon envelope events over all natural horizons.
    simpa [A] using hAprop
  have hAc : μ Aᶜ = 0 := by
    simpa using (ae_iff.1 hAae)
  refine ⟨A, hAc, ?_, ?_⟩
  · intro t
    simpa using (hNullMeas t (s := Aᶜ) hAc).compl
  · intro ω hω q a b hab
    exact hω q a b hab

/-- Helper for Theorem 21.24: a finite clipped-row envelope on one rational interval gives one
uniform natural-number bound for every row and every finite horizon on that interval. -/
private lemma natBoundOfBoundedHorizonDyadicNegRowEnvelope21_24
    {ω : Ω} {q : ℕ} {a b : ℚ}
    (hω_sup :
      (⨆ n : ℕ,
        upcrossings (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω) < ∞) :
    ∃ K : ℕ, ∀ n N : ℕ,
      upcrossingsBefore (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) N ω ≤ K := by
  let envelope : ℝ≥0∞ :=
    ⨆ n : ℕ,
      upcrossings (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω
  lift envelope to NNReal using hω_sup.ne with r hr
  obtain ⟨K, hK⟩ := exists_nat_ge r
  refine ⟨K, ?_⟩
  intro n N
  have hBefore :
      (upcrossingsBefore (a : ℝ) (b : ℝ)
        (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) N ω : ℝ≥0∞) ≤
        upcrossings (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω := by
    exact le_iSup
      (fun M : ℕ ↦
        (upcrossingsBefore (a : ℝ) (b : ℝ)
          (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) M ω : ℝ≥0∞))
      N
  have hRow :
      upcrossings (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) n j) ω) ω ≤
        envelope := by
    exact le_iSup
      (fun m : ℕ ↦
        upcrossings (a : ℝ) (b : ℝ) (fun j ω ↦ -X (dyadicPointUpTo (q : NNReal) m j) ω) ω)
      n
  have hEnvelopeLe : envelope ≤ (K : ℝ≥0∞) := by
    have hrK : (r : ℝ≥0∞) ≤ (K : ℝ≥0∞) := by
      exact_mod_cast hK
    simpa [hr] using hrK
  -- Proof comment: each finite-horizon row count is bounded by the rowwise full upcrossing count
  -- and then by the common clipped-row envelope bound.
  simpa using hBefore.trans (hRow.trans hEnvelopeLe)

/-- Helper for Theorem 21.24: there is one full-measure event on which every natural-horizon
clipped dyadic row of `-X` has finite rational upcrossings. -/
private lemma existsFullMeasureDyadicNegRowEvent
    (hX : Supermartingale X ℱ μ)
    (hNullMeas : ∀ t : NNReal, ∀ {s : Set Ω}, μ s = 0 → MeasurableSet[ℱ t] s) :
    ∃ A : Set Ω,
      μ Aᶜ = 0 ∧
        (∀ t : NNReal, MeasurableSet[ℱ t] A) ∧
        ∀ ω ∈ A, ∀ q n : ℕ, ∀ a b : ℚ, a < b →
          upcrossings (a : ℝ) (b : ℝ)
            (fun k ω ↦ -X (dyadicPointUpTo (q : NNReal) n k) ω) ω < ∞ := by
  let A : Set Ω := {ω |
    ∀ q n : ℕ, ∀ a b : ℚ, a < b →
      upcrossings (a : ℝ) (b : ℝ)
        (fun k ω ↦ -X (dyadicPointUpTo (q : NNReal) n k) ω) ω < ∞}
  have hAprop :
      ∀ᵐ ω ∂μ,
        ∀ q n : ℕ, ∀ a b : ℚ, a < b →
          upcrossings (a : ℝ) (b : ℝ)
            (fun k ω ↦ -X (dyadicPointUpTo (q : NNReal) n k) ω) ω < ∞ := by
    rw [ae_all_iff]
    intro q
    exact aeAll_boundedHorizonDyadicNegRowUpcrossings
      (X := X)
      (μ := μ)
      (ℱ := ℱ)
      hX
      (q : NNReal)
  have hAae :
      ∀ᵐ ω ∂μ, ω ∈ A := by
    -- Proof comment: intersect the fixed-horizon owner over all natural horizons.
    simpa [A] using hAprop
  have hAc : μ Aᶜ = 0 := by
    simpa using (ae_iff.1 hAae)
  refine ⟨A, hAc, ?_, ?_⟩
  · intro t
    simpa using (hNullMeas t (s := Aᶜ) hAc).compl
  · intro ω hω q n a b hab
    exact hω q n a b hab

/-- Helper for Theorem 21.24: each bounded-horizon dyadic grid maximum is measurable because it is
the supremum of finitely many measurable sampled absolute values. -/
private lemma measurable_dyadicGridAbsMax21_24
    (hX : Supermartingale X ℱ μ) (q : NNReal) (n : ℕ) :
    Measurable (dyadicGridAbsMax21_24 (X := X) q n) := by
  -- Proof comment: each grid sample comes from one deterministic time slice of the
  -- supermartingale, so the finite supremum over the row is measurable.
  simpa [dyadicGridAbsMax21_24] using
    (Finset.measurable_range_sup'' (n := dyadicCutoff q n) fun k hk ↦
      ((hX.stronglyMeasurable (dyadicPointUpTo q n k)).mono
        (ℱ.le (dyadicPointUpTo q n k))).measurable.norm)

/-- Helper for Theorem 21.24: on every fixed natural horizon `q`, there is a full-measure event on
which the monotone dyadic grid maxima stay bounded across all mesh levels. -/
private lemma existsFullMeasureDyadicGridBoundedEvent
    (hX : Supermartingale X ℱ μ) (q : ℕ) :
    ∃ B : Set Ω,
      μ Bᶜ = 0 ∧
        ∀ ω ∈ B, ∃ C : ℝ, ∀ n : ℕ, dyadicGridAbsMax21_24 (X := X) (q : NNReal) n ω ≤ C := by
  let K : ℝ := 12 * μ[fun ω ↦ |X 0 ω|] + 9 * μ[fun ω ↦ |X (q : NNReal) ω|]
  let E : ℕ → ℕ → Set Ω := fun M n ↦
    {ω | ((M + 1 : ℕ) : ℝ) ≤ dyadicGridAbsMax21_24 (X := X) (q : NNReal) n ω}
  let bad : Set Ω := ⋂ M : ℕ, ⋃ n : ℕ, E M n
  have hE_meas : ∀ M n, MeasurableSet (E M n) := by
    intro M n
    exact measurableSet_le measurable_const
      (measurable_dyadicGridAbsMax21_24 (X := X) (μ := μ) (ℱ := ℱ) hX (q : NNReal) n)
  have hGridMono : ∀ ω : Ω, Monotone (fun n ↦ dyadicGridAbsMax21_24 (X := X) (q : NNReal) n ω) := by
    intro ω
    exact monotone_nat_of_le_succ fun n ↦
      dyadicGridAbsMax21_24_mono (X := X) (q : NNReal) n ω
  have hE_antitone : Antitone fun M ↦ ⋃ n : ℕ, E M n := by
    intro M N hMN
    refine Set.iUnion_subset fun n ↦ ?_
    intro ω hω
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    have hMN' : ((M + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hMN
    exact le_trans hMN' hω
  have hRow_mono : ∀ M : ℕ, Monotone (E M) := by
    intro M n m hnm ω hω
    exact le_trans hω (hGridMono ω hnm)
  have hUnionBound :
      ∀ M : ℕ,
        μ (⋃ n : ℕ, E M n) ≤ ENNReal.ofReal K / (((M + 1 : ℕ) : ℝ≥0∞)) := by
    intro M
    calc
      μ (⋃ n : ℕ, E M n) = ⨆ n : ℕ, μ (E M n) := by
        exact (hRow_mono M).measure_iUnion
      _ ≤ ENNReal.ofReal K / (((M + 1 : ℕ) : ℝ≥0∞)) := by
        refine iSup_le fun n ↦ ?_
        have htail :
            (((M + 1 : ℕ) : NNReal) : ℝ≥0∞) * μ (E M n) ≤ ENNReal.ofReal K := by
          -- Proof comment: the tail estimate is uniform in the row index `n`, so it controls
          -- every bad-threshold event on the fixed horizon `q`.
          simpa [E, K] using
            dyadicGridAbsMax21_24_tail_bound
              (X := X)
              (μ := μ)
              (ℱ := ℱ)
              hX
              (q : NNReal)
              n
              ((M + 1 : ℕ) : NNReal)
              (by positivity)
        have hμle :
            μ (E M n) ≤ ENNReal.ofReal K / (((M + 1 : ℕ) : ℝ≥0∞)) := by
          exact
            (ENNReal.le_div_iff_mul_le
              (Or.inl (by positivity : (((M + 1 : ℕ) : ℝ≥0∞)) ≠ 0))
              (Or.inl (by simp : (((M + 1 : ℕ) : ℝ≥0∞)) ≠ ∞))).2 <| by
                simpa [mul_comm] using htail
        exact hμle
  have hbad_tendsto :
      Tendsto (fun M : ℕ ↦ μ (⋃ n : ℕ, E M n)) atTop (𝓝 (μ bad)) := by
    -- Proof comment: the bad sets form a decreasing family in the threshold parameter `M`, so
    -- continuity from above identifies the measure of their intersection as the limiting value.
    simpa [bad] using
      tendsto_measure_iInter_atTop
        (μ := μ)
        (s := fun M : ℕ ↦ ⋃ n : ℕ, E M n)
        (fun M ↦ (MeasurableSet.iUnion fun n ↦ hE_meas M n).nullMeasurableSet)
        hE_antitone
        ⟨0, measure_ne_top μ _⟩
  have hBound_tendsto_zero :
      Tendsto (fun M : ℕ ↦ ENNReal.ofReal K / (((M + 1 : ℕ) : ℝ≥0∞))) atTop (𝓝 0) := by
    have hreal :
        Tendsto (fun M : ℕ ↦ K / (((M + 1 : ℕ) : ℝ) : ℝ)) atTop (𝓝 0) := by
      have hcomp :
          (fun M : ℕ ↦ K / (((M + 1 : ℕ) : ℝ) : ℝ)) =
            ((fun n : ℕ ↦ K / (n : ℝ)) ∘ fun a : ℕ ↦ a + 1) := by
        funext M
        simp [Function.comp]
      rw [hcomp]
      exact (tendsto_const_div_atTop_nhds_zero_nat K).comp (tendsto_add_atTop_nat 1)
    have hEq :
        (fun M : ℕ ↦ ENNReal.ofReal K / (((M + 1 : ℕ) : ℝ≥0∞))) =
          fun M : ℕ ↦ ENNReal.ofReal (K / ((M + 1 : ℕ) : ℝ)) := by
      funext M
      rw [← ENNReal.ofReal_natCast (M + 1)]
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < ((M + 1 : ℕ) : ℝ))]
    rw [hEq]
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  have hbad_zero :
      Tendsto (fun M : ℕ ↦ μ (⋃ n : ℕ, E M n)) atTop (𝓝 0) := by
    -- Proof comment: the uniform tail bound squeezes the bad-threshold measures down to zero as
    -- the threshold tends to infinity.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      hBound_tendsto_zero
      (Eventually.of_forall fun M ↦ bot_le)
      (Eventually.of_forall hUnionBound)
  have hbad_null : μ bad = 0 := by
    simpa using tendsto_nhds_unique hbad_tendsto hbad_zero
  refine ⟨badᶜ, by simpa [bad], ?_⟩
  intro ω hω
  have hω' : ∃ M : ℕ, ω ∉ ⋃ n : ℕ, E M n := by
    simpa [bad] using hω
  rcases hω' with ⟨M, hM⟩
  refine ⟨(M + 1 : ℕ), ?_⟩
  intro n
  have hnot : ω ∉ E M n := by
    intro hEn
    exact hM (Set.mem_iUnion.2 ⟨n, hEn⟩)
  have hlt : dyadicGridAbsMax21_24 (X := X) (q : NNReal) n ω < (M + 1 : ℕ) := by
    exact lt_of_not_ge (by simpa [E] using hnot)
  exact hlt.le

/-- Helper for Theorem 21.24: the master dyadic control event stores the bounded-horizon clipped
row-envelope bounds for `-X` together with bounded dyadic-grid maxima. -/
private abbrev dyadicControlProperty21_24 (A : Set Ω) : Prop :=
  ∀ ω ∈ A,
    (∀ q : ℕ, ∀ a b : ℚ, a < b →
      (⨆ n : ℕ,
        upcrossings (a : ℝ) (b : ℝ)
          (fun k ω ↦ -X (dyadicPointUpTo (q : NNReal) n k) ω) ω) < ∞) ∧
    (∀ q : ℕ, ∃ C : ℝ, ∀ n : ℕ, dyadicGridAbsMax21_24 (X := X) (q : NNReal) n ω ≤ C)

/-- Helper for Theorem 21.24: there is one full-measure dyadic control event carrying both finite
bounded-horizon clipped-row envelopes for `-X` and bounded dyadic grid maxima on every natural
horizon. -/
private lemma existsFullMeasureDyadicControlEvent
    (hX : Supermartingale X ℱ μ)
    (hNullMeas : ∀ t : NNReal, ∀ {s : Set Ω}, μ s = 0 → MeasurableSet[ℱ t] s) :
    ∃ A : Set Ω,
      μ Aᶜ = 0 ∧
        (∀ t : NNReal, MeasurableSet[ℱ t] A) ∧
        dyadicControlProperty21_24 (X := X) A := by
  obtain ⟨Aenv, hAenvc, hAenv_meas, hAenv⟩ :=
    existsFullMeasureDyadicNegRowEnvelopeEvent (X := X) (μ := μ) (ℱ := ℱ) hX hNullMeas
  choose B hBc hB using
    fun q : ℕ ↦ existsFullMeasureDyadicGridBoundedEvent (X := X) (μ := μ) (ℱ := ℱ) hX q
  let A : Set Ω := Aenv ∩ ⋂ q : ℕ, B q
  have hBallc : μ (⋃ q : ℕ, (B q)ᶜ) = 0 := by
    exact measure_iUnion_null fun q ↦ hBc q
  have hBiInterc : μ (⋂ q : ℕ, B q)ᶜ = 0 := by
    have hcompl : (⋂ q : ℕ, B q)ᶜ = ⋃ q : ℕ, (B q)ᶜ := by
      ext ω
      simp
    rw [hcompl]
    exact hBallc
  have hAc : μ Aᶜ = 0 := by
    -- Proof comment: the complement of the combined control event lies in the union of the two
    -- null exceptional sets coming from the clipped-row envelope and dyadic-grid boundedness.
    have hsubset : Aᶜ ⊆ Aenvᶜ ∪ (⋂ q : ℕ, B q)ᶜ := by
      intro ω hω
      have hω' : ω ∈ Aenv → ∃ q : ℕ, ω ∉ B q := by
        simpa [A] using hω
      by_cases hAenvω : ω ∈ Aenv
      · right
        rcases hω' hAenvω with ⟨q, hq⟩
        exact fun hAll ↦ hq ((Set.mem_iInter.mp hAll) q)
      · left
        simpa using hAenvω
    have hle : μ Aᶜ ≤ μ (Aenvᶜ ∪ (⋂ q : ℕ, B q)ᶜ) := measure_mono hsubset
    have hnull : μ (Aenvᶜ ∪ (⋂ q : ℕ, B q)ᶜ) = 0 := measure_union_null hAenvc hBiInterc
    have hAc_le : μ Aᶜ ≤ 0 := by
      calc
        μ Aᶜ ≤ μ (Aenvᶜ ∪ (⋂ q : ℕ, B q)ᶜ) := hle
        _ = 0 := hnull
    exact le_antisymm hAc_le bot_le
  refine ⟨A, hAc, ?_⟩
  refine ⟨?_, ?_⟩
  · intro t
    simpa using (hNullMeas t (s := Aᶜ) hAc).compl
  · intro ω hω
    rcases hω with ⟨hωAenv, hωB⟩
    constructor
    · intro q a b hab
      exact hAenv ω hωAenv q a b hab
    · intro q
      have hωBq : ω ∈ B q := (Set.mem_iInter.mp hωB) q
      exact hB q ω hωBq

/-- Helper for Theorem 21.24: the dyadic right approximants stay within one unit of their base
time. -/
private lemma dyadicRightApprox_le_self_add_one (t : NNReal) (n : ℕ) :
    dyadicRightApprox t n ≤ t + 1 := by
  have hmesh : dyadicRightApprox t n ≤ t + ((2 : NNReal) ^ n)⁻¹ := by
    let c : NNReal := (2 : NNReal) ^ n
    have hc_pos : 0 < c := by
      dsimp [c]
      positivity
    have hceil : (Nat.ceil (((c * t : NNReal) : ℝ)) : NNReal) ≤ c * t + 1 := by
      simpa using (Nat.ceil_lt_add_one (show 0 ≤ (c * t : NNReal) by positivity)).le
    dsimp [dyadicRightApprox, c]
    rw [div_le_iff₀ hc_pos]
    calc
      (Nat.ceil (((t : NNReal) * (2 : NNReal) ^ n : NNReal) : ℝ) : NNReal)
          ≤ t * (2 : NNReal) ^ n + 1 := by
            simpa [mul_comm] using hceil
      _ = t * (2 : NNReal) ^ n + (((2 : NNReal) ^ n)⁻¹ * (2 : NNReal) ^ n) := by
            rw [inv_mul_cancel₀]
            positivity
      _ = (t + ((2 : NNReal) ^ n)⁻¹) * (2 : NNReal) ^ n := by
            rw [add_mul]
  have hunit : ((2 : NNReal) ^ n)⁻¹ ≤ 1 := by
    have hpow : (1 : NNReal) ≤ (2 : NNReal) ^ n := by
      simpa using (one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 2) : (1 : NNReal) ≤ (2 : NNReal) ^ n)
    exact inv_le_one_of_one_le₀ hpow
  calc
    dyadicRightApprox t n ≤ t + ((2 : NNReal) ^ n)⁻¹ := hmesh
    _ ≤ t + 1 := by
      simpa [add_comm] using add_le_add_right hunit t

/-- Helper for Theorem 21.24: the negative parts of the fixed-time dyadic future samples are
uniformly integrable after reindexing the bounded-horizon owner at horizon `t + 1`. -/
private lemma dyadicRightApproxNegPartUniformIntegrable
    (hX : Supermartingale X ℱ μ) (t : NNReal) :
    UniformIntegrable (fun n : ℕ ↦ fun ω ↦ (-X (dyadicRightApprox t n) ω)⁺) 1 μ := by
  let q : NNReal := t + 1
  let τ : ℕ → {u : NNReal // u ≤ q} := fun n ↦
    ⟨dyadicRightApprox t n, by
      -- Proof comment: the dyadic right approximants stay inside the deterministic horizon
      -- needed for the bounded-horizon negative-part owner.
      simpa [q] using dyadicRightApprox_le_self_add_one t n⟩
  have hUIq :
      UniformIntegrable (fun s : {u : NNReal // u ≤ q} ↦ fun ω ↦ (-X s.1 ω)⁺) 1 μ :=
    boundedHorizonNegPartUniformIntegrable (X := X) (μ := μ) (ℱ := ℱ) hX q
  -- Proof comment: deterministic reindexing preserves uniform integrability of the negative-part
  -- bounded-horizon owner.
  simpa [τ] using uniformIntegrable_comp (μ := μ) hUIq τ

/-- Helper for Theorem 21.24: restricted set integrals inherit `L¹` convergence. -/
private lemma tendstoRestrictedIntegralOfTendstoL1
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {s : Set Ω}
    (hg : Integrable g μ) (hfi : ∀ n, Integrable (f n) μ)
    (hL1 : Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω in s, f n ω ∂μ) atTop (𝓝 (∫ ω in s, g ω ∂μ)) := by
  have hL1_restrict :
      Tendsto (fun n ↦ eLpNorm (fun ω ↦ f n ω - g ω) 1 (μ.restrict s)) atTop (𝓝 0) := by
    -- Proof comment: restricting the measure can only decrease the `L¹` seminorm.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 ?_ ?_
    · intro n
      exact bot_le
    · intro n
      exact eLpNorm_mono_measure (fun ω ↦ f n ω - g ω) Measure.restrict_le_self
  -- Proof comment: once the difference tends to zero on the restricted measure, continuity of the
  -- integral on `L¹` gives the restricted set-integral limit.
  exact tendsto_integral_of_L1' g hg.restrict
    (Filter.Eventually.of_forall fun n ↦ (hfi n).restrict) hL1_restrict

/-- Helper for Theorem 21.24: refining the dyadic mesh can only move the ceiling approximation
closer to the base time. -/
private lemma dyadicRightApprox_succ_le (t : NNReal) (n : ℕ) :
    dyadicRightApprox t (n + 1) ≤ dyadicRightApprox t n := by
  have hceil :
      Nat.ceil ((t : ℝ) * (2 : ℝ) ^ (n + 1)) ≤ 2 * Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) := by
    -- Proof comment: splitting the refined dyadic scale into two equal coarse blocks reduces the
    -- refined ceiling to the sum of two identical coarse ceilings.
    have hsplit :
        (t : ℝ) * (2 : ℝ) ^ (n + 1) =
          ((t : ℝ) * (2 : ℝ) ^ n) + ((t : ℝ) * (2 : ℝ) ^ n) := by
      rw [pow_succ]
      ring
    rw [hsplit]
    simpa [two_mul] using Nat.ceil_add_le ((t : ℝ) * (2 : ℝ) ^ n) ((t : ℝ) * (2 : ℝ) ^ n)
  change
    (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ (n + 1)) : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) ≤
      (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : ℝ) / (2 : ℝ) ^ n)
  have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
  rw [pow_succ]
  have hceil_real :
      (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ (n + 1)) : ℕ) : ℝ)) ≤
        2 * (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : ℝ)) := by
    exact_mod_cast hceil
  have hceil_real' :
      (((Nat.ceil ((t : ℝ) * ((2 : ℝ) ^ n * 2)) : ℕ) : ℝ)) ≤
        2 * (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : ℝ)) := by
    simpa [pow_succ, mul_assoc] using hceil_real
  have hhalf :
      (((Nat.ceil ((t : ℝ) * ((2 : ℝ) ^ n * 2)) : ℕ) : ℝ) / 2) ≤
        (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : ℝ)) := by
    refine (div_le_iff₀ zero_lt_two).2 ?_
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hceil_real'
  have hrewrite :
      (((Nat.ceil ((t : ℝ) * ((2 : ℝ) ^ n * 2)) : ℕ) : ℝ) / ((2 : ℝ) ^ n * 2)) =
        ((((Nat.ceil ((t : ℝ) * ((2 : ℝ) ^ n * 2)) : ℕ) : ℝ) / 2) / (2 : ℝ) ^ n) := by
    simpa [div_div, mul_comm, mul_left_comm, mul_assoc]
  rw [hrewrite]
  exact (div_le_div_iff_of_pos_right hpow_pos).2 hhalf

/-- Helper for Theorem 21.24: the dyadic right-approximation sequence decreases to the base time.
-/
private lemma dyadicRightApprox_antitone (t : NNReal) :
    Antitone (dyadicRightApprox t) :=
  antitone_nat_of_succ_le (dyadicRightApprox_succ_le t)

/-- Helper for Theorem 21.24: shifting the decreasing dyadic filtration family does not change
its infimum. -/
private lemma iInf_filtration_dyadicRightApprox_add_eq
    (hFiltration :
      ∀ t : NNReal, (⨅ n : ℕ, ℱ (dyadicRightApprox t n)) = ℱ t)
    (t : NNReal) (m : ℕ) :
    (⨅ n : ℕ, ℱ (dyadicRightApprox t (n + m))) = ℱ t := by
  have hanti : Antitone (dyadicRightApprox t) := dyadicRightApprox_antitone t
  refine le_antisymm ?_ ?_
  · -- Proof comment: the tail infimum is below each unshifted stage because the dyadic family is
    -- decreasing and every unshifted stage is dominated by a suitable tail stage.
    have hTailLe :
        (⨅ n : ℕ, ℱ (dyadicRightApprox t (n + m))) ≤ ⨅ n : ℕ, ℱ (dyadicRightApprox t n) := by
      refine le_iInf fun k ↦ ?_
      by_cases hmk : m ≤ k
      · rcases Nat.exists_eq_add_of_le hmk with ⟨j, rfl⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (iInf_le (fun n : ℕ ↦ ℱ (dyadicRightApprox t (n + m))) j)
      · have hkm : k ≤ m := (Nat.lt_of_not_ge hmk).le
        exact
          (iInf_le (fun n : ℕ ↦ ℱ (dyadicRightApprox t (n + m))) 0).trans
            (ℱ.mono (by simpa using hanti hkm))
    simpa [hFiltration t] using hTailLe
  · -- Proof comment: every shifted stage still lies to the right of `t`, so `ℱ t` is below the
    -- whole tail family.
    refine le_iInf fun n ↦ ℱ.mono (le_dyadicRightApprox t (n + m))

/-- Helper for Theorem 21.24: the negative parts of the fixed-time dyadic future samples converge
to the candidate negative part in `L¹`. -/
private lemma tendsto_eLpNorm_negPart_dyadicRightApprox_to_candidate
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (dyadicRightApprox t n) ω) atTop (𝓝 (Xtilde t ω))) :
    Integrable (fun ω ↦ (-Xtilde t ω)⁺) μ ∧
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ (-X (dyadicRightApprox t n) ω)⁺ - (-Xtilde t ω)⁺)
            1 μ)
        atTop
        (𝓝 0) := by
  have hNegUI :
      UniformIntegrable (fun n : ℕ ↦ fun ω ↦ (-X (dyadicRightApprox t n) ω)⁺) 1 μ :=
    dyadicRightApproxNegPartUniformIntegrable (X := X) (μ := μ) (ℱ := ℱ) hX t
  have hNegAe :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (-X (dyadicRightApprox t n) ω)⁺) atTop
        (𝓝 ((-Xtilde t ω)⁺)) := by
    -- Proof comment: the negative-part map is continuous, so it preserves the pointwise dyadic
    -- future limit.
    filter_upwards [hXt_lim] with ω hω
    exact ((continuous_id.neg.max continuous_const).tendsto _).comp hω
  have hNegInt : Integrable (fun ω ↦ (-Xtilde t ω)⁺) μ :=
    hNegUI.integrable_of_ae_tendsto hNegAe
  have hNegMemLp : MemLp (fun ω ↦ (-Xtilde t ω)⁺) 1 μ :=
    memLp_one_iff_integrable.2 hNegInt
  have hNegL1 :
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ (-X (dyadicRightApprox t n) ω)⁺ - (-Xtilde t ω)⁺)
            1 μ)
        atTop
        (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae
      le_rfl
      ENNReal.one_ne_top
      (fun n ↦ hNegUI.aestronglyMeasurable n)
      hNegMemLp
      hNegUI.unifIntegrable
      hNegAe
  exact ⟨hNegInt, hNegL1⟩

/-- Helper for Theorem 21.24: the dyadic future candidate is integrable at each fixed time. -/
private lemma integrable_candidate_of_dyadicRightApprox
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (dyadicRightApprox t n) ω) atTop (𝓝 (Xtilde t ω))) :
    Integrable (Xtilde t) μ := by
  have hNeg :=
    tendsto_eLpNorm_negPart_dyadicRightApprox_to_candidate
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_lim
  have hNegInt : Integrable (fun ω ↦ (-Xtilde t ω)⁺) μ := hNeg.1
  let q : NNReal := t + 1
  obtain ⟨C, hC⟩ := boundedHorizonELpNormOneBounded (X := X) (μ := μ) (ℱ := ℱ) hX q
  have hPosMeas :
      ∀ n, AEMeasurable (fun ω ↦ ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺)) μ := by
    intro n
    have hmeas :
        AEMeasurable (fun ω ↦ (X (dyadicRightApprox t n) ω)⁺) μ :=
      ((hX.integrable (dyadicRightApprox t n)).pos_part).aestronglyMeasurable.aemeasurable
    exact hmeas.ennreal_ofReal
  have hPosTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺))
          atTop
          (𝓝 (ENNReal.ofReal ((Xtilde t ω)⁺))) := by
    -- Proof comment: the positive-part map is continuous as well, so the dyadic future limit
    -- transfers to the candidate positive part.
    filter_upwards [hXt_lim] with ω hω
    exact ((ENNReal.continuous_ofReal.comp (continuous_id.max continuous_const)).tendsto _).comp hω
  have hFatou :
      ∫⁻ ω, ENNReal.ofReal ((Xtilde t ω)⁺) ∂μ ≤
        liminf
          (fun n ↦ ∫⁻ ω, ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺) ∂μ)
          atTop := by
    -- Proof comment: Fatou controls the lower integral of the candidate positive part by the
    -- liminf of the dyadic future positive-part integrals.
    calc
      ∫⁻ ω, ENNReal.ofReal ((Xtilde t ω)⁺) ∂μ
          = ∫⁻ ω,
              liminf (fun n ↦ ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺)) atTop ∂μ := by
                refine lintegral_congr_ae ?_
                filter_upwards [hPosTendsto] with ω hω
                exact hω.liminf_eq.symm
      _ ≤
          liminf
            (fun n ↦ ∫⁻ ω, ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺) ∂μ)
            atTop := by
              exact MeasureTheory.lintegral_liminf_le' hPosMeas
  have hPosIntegralBound :
      ∀ᶠ n : ℕ in atTop,
        ∫⁻ ω, ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺) ∂μ ≤ (C : ℝ≥0∞) := by
    filter_upwards with n
    have hs :
        eLpNorm (X (dyadicRightApprox t n)) 1 μ ≤ C :=
      hC ⟨dyadicRightApprox t n, by simpa [q] using dyadicRightApprox_le_self_add_one t n⟩
    have hdom :
        ∀ᵐ ω ∂μ,
          ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺) ≤
            (↑‖X (dyadicRightApprox t n) ω‖₊ : ENNReal) := by
      filter_upwards [] with ω
      have hpoint : (X (dyadicRightApprox t n) ω)⁺ ≤ |X (dyadicRightApprox t n) ω| := by
        by_cases hω : 0 ≤ X (dyadicRightApprox t n) ω
        · simp [Real.norm_eq_abs, hω, abs_of_nonneg hω]
        · have hω' : X (dyadicRightApprox t n) ω ≤ 0 := le_of_not_ge hω
          simp [posPart_eq_zero.2 hω', abs_of_nonpos hω', hω']
      exact_mod_cast hpoint
    calc
      ∫⁻ ω, ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺) ∂μ
          ≤ ∫⁻ ω, (↑‖X (dyadicRightApprox t n) ω‖₊ : ENNReal) ∂μ :=
            lintegral_mono_ae hdom
      _ = ∫⁻ ω, ‖X (dyadicRightApprox t n) ω‖ₑ ∂μ := by
            refine lintegral_congr_ae ?_
            exact ae_of_all μ (fun ω ↦ by simp [enorm_eq_nnnorm])
      _ = eLpNorm (X (dyadicRightApprox t n)) 1 μ := by
            rw [eLpNorm_one_eq_lintegral_enorm]
      _ ≤ C := hs
  have hPosLintegralNeTop :
      ∫⁻ ω, ENNReal.ofReal ((Xtilde t ω)⁺) ∂μ ≠ ∞ := by
    apply lt_top_iff_ne_top.mp
    exact lt_of_le_of_lt
      (hFatou.trans (Filter.liminf_le_of_frequently_le hPosIntegralBound.frequently))
      (by simp)
  have hPosInt : Integrable (fun ω ↦ (Xtilde t ω)⁺) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((((hXt_meas.mono (ℱ.le t)).measurable.max measurable_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ posPart_nonneg (Xtilde t ω))).1 hPosLintegralNeTop
  have hNormInt :
      Integrable (fun ω ↦ (Xtilde t ω)⁺ + (-Xtilde t ω)⁺) μ :=
    hPosInt.add hNegInt
  have hNormEq :
      ∀ ω, ‖Xtilde t ω‖ = (Xtilde t ω)⁺ + (-Xtilde t ω)⁺ := by
    intro ω
    by_cases hω : 0 ≤ Xtilde t ω
    · rw [Real.norm_eq_abs, abs_of_nonneg hω, posPart_eq_self.2 hω,
        posPart_eq_zero.2 (neg_nonpos.mpr hω), add_zero]
    · have hω' : Xtilde t ω ≤ 0 := le_of_not_ge hω
      rw [Real.norm_eq_abs, abs_of_nonpos hω', posPart_eq_zero.2 hω',
        posPart_eq_self.2 (neg_nonneg.mpr hω'), zero_add]
  have hNormInt' : Integrable (fun ω ↦ ‖Xtilde t ω‖) μ := by
    refine hNormInt.congr ?_
    exact ae_of_all μ (fun ω ↦ (hNormEq ω).symm)
  exact
    (integrable_norm_iff ((hXt_meas.mono (ℱ.le t)).aestronglyMeasurable)).1 hNormInt'

/-- Helper for Theorem 21.24: each fixed dyadic future slice conditioned back to time `t` lies
below the dyadic-limit candidate. -/
private lemma condExp_futureSlice_ae_le_candidate
    (hX : Supermartingale X ℱ μ)
    (hFiltration :
      ∀ t : NNReal, (⨅ n : ℕ, ℱ (dyadicRightApprox t n)) = ℱ t)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal) (m : ℕ)
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (dyadicRightApprox t n) ω) atTop (𝓝 (Xtilde t ω))) :
    μ[X (dyadicRightApprox t m) | ℱ t] ≤ᵐ[μ] Xtilde t := by
  let mFamily : ℕ → MeasurableSpace Ω := fun n ↦ ℱ (dyadicRightApprox t (n + m))
  have hm_le : ∀ n, mFamily n ≤ mΩ := fun n ↦ ℱ.le _
  have hm_anti : Antitone mFamily := by
    intro i j hij
    exact ℱ.mono ((dyadicRightApprox_antitone t) (Nat.add_le_add_right hij m))
  have hTailFiltration : (⨅ n : ℕ, mFamily n) = ℱ t :=
    iInf_filtration_dyadicRightApprox_add_eq (ℱ := ℱ) hFiltration t m
  have hCondTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ μ[X (dyadicRightApprox t m) | mFamily n] ω)
          atTop
          (𝓝 (μ[X (dyadicRightApprox t m) | ℱ t] ω)) := by
    -- Proof comment: reverse Lévy applies to the decreasing dyadic filtration tail.
    simpa [mFamily, hTailFiltration] using
      tendsto_ae_condExp_iInf_of_antitone
        (μ := μ)
        (m := mFamily)
        hm_le
        hm_anti
        (hX.integrable (dyadicRightApprox t m))
  have hFutureLe :
      ∀ n : ℕ,
        μ[X (dyadicRightApprox t m) | mFamily n] ≤ᵐ[μ]
          fun ω ↦ X (dyadicRightApprox t (n + m)) ω := by
    intro n
    have htime :
        dyadicRightApprox t (n + m) ≤ dyadicRightApprox t m :=
      (dyadicRightApprox_antitone t) (Nat.le_add_left m n)
    simpa [mFamily] using hX.condExp_ae_le htime
  have hTailLimit :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ X (dyadicRightApprox t (n + m)) ω)
          atTop
          (𝓝 (Xtilde t ω)) := by
    -- Proof comment: shifting a convergent dyadic future sequence preserves its pointwise limit.
    filter_upwards [hXt_lim] with ω hω
    exact hω.comp (tendsto_add_atTop_nat m)
  -- Proof comment: compare the reverse-Lévy conditional-expectation limit with the shifted dyadic
  -- future limit and use uniqueness of real limits under the pointwise inequalities.
  have hFutureLeAll :
      ∀ᵐ ω ∂μ,
        ∀ n : ℕ,
          μ[X (dyadicRightApprox t m) | mFamily n] ω ≤ X (dyadicRightApprox t (n + m)) ω :=
    ae_all_iff.2 hFutureLe
  filter_upwards [hCondTendsto, hTailLimit, hFutureLeAll] with ω hωCond hωTail hωLe
  exact le_of_tendsto_of_tendsto' hωCond hωTail hωLe

/-- Helper for Theorem 21.24: on every `ℱ t`-measurable test set, the dyadic future candidate has
no larger integral than the time-`t` slice. -/
private lemma candidate_setIntegral_le_fixedTime
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (dyadicRightApprox t n) ω) atTop (𝓝 (Xtilde t ω)))
    {s : Set Ω} (hs : MeasurableSet[ℱ t] s) :
    ∫ ω in s, Xtilde t ω ∂μ ≤ ∫ ω in s, X t ω ∂μ := by
  have hXt_int :
      Integrable (Xtilde t) μ :=
    integrable_candidate_of_dyadicRightApprox
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim
  have hNegInt :
      Integrable (fun ω ↦ (-Xtilde t ω)⁺) μ
      ∧
        Tendsto
          (fun n : ℕ ↦
            eLpNorm
              (fun ω ↦ (-X (dyadicRightApprox t n) ω)⁺ - (-Xtilde t ω)⁺)
              1 μ)
          atTop
          (𝓝 0) :=
    tendsto_eLpNorm_negPart_dyadicRightApprox_to_candidate
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_lim
  have hNegSet :
      Tendsto
        (fun n : ℕ ↦ ∫ ω in s, (-X (dyadicRightApprox t n) ω)⁺ ∂μ)
        atTop
        (𝓝 (∫ ω in s, (-Xtilde t ω)⁺ ∂μ)) :=
    tendstoRestrictedIntegralOfTendstoL1
      (μ := μ)
      (g := fun ω ↦ (-Xtilde t ω)⁺)
      hNegInt.1
      (fun n ↦ (hX.integrable (dyadicRightApprox t n)).neg_part)
      hNegInt.2
  have hSliceDecomp :
      ∀ n : ℕ,
        ∫ ω in s, X (dyadicRightApprox t n) ω ∂μ =
          ∫ ω in s, (X (dyadicRightApprox t n) ω)⁺ ∂μ -
            ∫ ω in s, (-X (dyadicRightApprox t n) ω)⁺ ∂μ := by
    intro n
    -- Proof comment: on the restricted measure, each dyadic sample splits into positive and
    -- negative parts exactly as on the whole space.
    simpa using
      (integral_eq_integral_pos_part_sub_integral_neg_part
        (μ := μ.restrict s)
        (hX.integrable (dyadicRightApprox t n)).restrict)
  have hCandidateDecomp :
      ∫ ω in s, Xtilde t ω ∂μ =
        ∫ ω in s, (Xtilde t ω)⁺ ∂μ -
          ∫ ω in s, (-Xtilde t ω)⁺ ∂μ := by
    -- Proof comment: the candidate admits the same positive/negative-part decomposition on the
    -- restricted test set.
    simpa using
      (integral_eq_integral_pos_part_sub_integral_neg_part
        (μ := μ.restrict s)
        hXt_int.restrict)
  have hPosMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun ω ↦ ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺))
          (μ.restrict s) := by
    intro n
    exact ((hX.integrable (dyadicRightApprox t n)).pos_part.restrict.aestronglyMeasurable
      ).aemeasurable.ennreal_ofReal
  have hPosTendsto :
      ∀ᵐ ω ∂μ.restrict s,
        Tendsto
          (fun n ↦ ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺))
          atTop
          (𝓝 (ENNReal.ofReal ((Xtilde t ω)⁺))) := by
    -- Proof comment: restricting to the test set preserves the pointwise dyadic convergence, and
    -- the positive-part map stays continuous after composing with `ENNReal.ofReal`.
    refine ae_restrict_of_ae ?_
    filter_upwards [hXt_lim] with ω hω
    exact ((ENNReal.continuous_ofReal.comp (continuous_id.max continuous_const)).tendsto _).comp hω
  have hPosIntegralEq :
      (fun n : ℕ ↦
        ∫⁻ ω, ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺) ∂μ.restrict s) =
        fun n : ℕ ↦ ENNReal.ofReal (∫ ω in s, (X (dyadicRightApprox t n) ω)⁺ ∂μ) := by
    funext n
    let f : Ω → ℝ := fun ω ↦ (X (dyadicRightApprox t n) ω)⁺
    have hf_int : Integrable f (μ.restrict s) := ((hX.integrable (dyadicRightApprox t n)).pos_part).restrict
    have hf_nonneg : 0 ≤ᵐ[μ.restrict s] f := Eventually.of_forall fun ω ↦ posPart_nonneg _
    simpa [f] using
      (ofReal_integral_eq_lintegral_ofReal (μ := μ.restrict s) hf_int hf_nonneg).symm
  have hFatou :
      ENNReal.ofReal (∫ ω in s, (Xtilde t ω)⁺ ∂μ) ≤
        liminf
          (fun n : ℕ ↦ ENNReal.ofReal (∫ ω in s, (X (dyadicRightApprox t n) ω)⁺ ∂μ))
          atTop := by
    -- Proof comment: Fatou on the restricted measure bounds the candidate positive part by the
    -- liminf of the dyadic future positive parts.
    calc
      ENNReal.ofReal (∫ ω in s, (Xtilde t ω)⁺ ∂μ)
          = ∫⁻ ω, ENNReal.ofReal ((Xtilde t ω)⁺) ∂μ.restrict s := by
              let f : Ω → ℝ := fun ω ↦ (Xtilde t ω)⁺
              have hf_int : Integrable f (μ.restrict s) := hXt_int.pos_part.restrict
              have hf_nonneg : 0 ≤ᵐ[μ.restrict s] f := Eventually.of_forall fun ω ↦ posPart_nonneg _
              simpa [f] using
                ofReal_integral_eq_lintegral_ofReal (μ := μ.restrict s) hf_int hf_nonneg
      _ = ∫⁻ ω,
            liminf (fun n ↦ ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺)) atTop
            ∂μ.restrict s := by
              refine lintegral_congr_ae ?_
              filter_upwards [hPosTendsto] with ω hω
              exact hω.liminf_eq.symm
      _ ≤
          liminf
            (fun n : ℕ ↦
              ∫⁻ ω, ENNReal.ofReal ((X (dyadicRightApprox t n) ω)⁺) ∂μ.restrict s)
            atTop := by
              exact MeasureTheory.lintegral_liminf_le' hPosMeas
      _ =
          liminf
            (fun n : ℕ ↦ ENNReal.ofReal (∫ ω in s, (X (dyadicRightApprox t n) ω)⁺ ∂μ))
            atTop := by
              rw [hPosIntegralEq]
  have hPosUpper :
      ∀ n : ℕ,
        ∫ ω in s, (X (dyadicRightApprox t n) ω)⁺ ∂μ ≤
          ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (dyadicRightApprox t n) ω)⁺ ∂μ := by
    intro n
    have hSliceLe :
        ∫ ω in s, X (dyadicRightApprox t n) ω ∂μ ≤ ∫ ω in s, X t ω ∂μ :=
      hX.setIntegral_le (le_dyadicRightApprox t n) hs
    -- Proof comment: rewrite the dyadic slice integral by positive and negative parts, then move
    -- the negative contribution to the right side.
    linarith [hSliceLe, hSliceDecomp n]
  have hFutureCarrierNonneg :
      ∀ n : ℕ,
        0 ≤ ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (dyadicRightApprox t n) ω)⁺ ∂μ := by
    intro n
    have hPosNonneg :
        0 ≤ ∫ ω in s, (X (dyadicRightApprox t n) ω)⁺ ∂μ := by
      exact integral_nonneg_of_ae (μ := μ.restrict s) <|
        Eventually.of_forall fun ω ↦ posPart_nonneg (X (dyadicRightApprox t n) ω)
    exact hPosNonneg.trans (hPosUpper n)
  have hFutureCarrierTendsto :
      Tendsto
        (fun n : ℕ ↦
          ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (dyadicRightApprox t n) ω)⁺ ∂μ)
        atTop
        (𝓝 (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ)) :=
    tendsto_const_nhds.add hNegSet
  have hFutureCarrierNonnegLimit :
      0 ≤ ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ := by
    have hEventuallyNonneg :
        ∀ᶠ n : ℕ in atTop,
          ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (dyadicRightApprox t n) ω)⁺ ∂μ ∈ Set.Ici 0 :=
      Eventually.of_forall fun n ↦ hFutureCarrierNonneg n
    exact IsClosed.mem_of_tendsto isClosed_Ici hFutureCarrierTendsto hEventuallyNonneg
  have hFatouUpper :
      ENNReal.ofReal (∫ ω in s, (Xtilde t ω)⁺ ∂μ) ≤
        ENNReal.ofReal (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ) := by
    -- Proof comment: combine Fatou with the termwise dyadic slice bounds and pass to the limit in
    -- the negative-part integrals.
    calc
      ENNReal.ofReal (∫ ω in s, (Xtilde t ω)⁺ ∂μ)
          ≤
            liminf
              (fun n : ℕ ↦ ENNReal.ofReal (∫ ω in s, (X (dyadicRightApprox t n) ω)⁺ ∂μ))
              atTop := hFatou
      _ ≤
          liminf
            (fun n : ℕ ↦
              ENNReal.ofReal
                (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (dyadicRightApprox t n) ω)⁺ ∂μ))
            atTop := by
              exact Filter.liminf_le_liminf <| Eventually.of_forall fun n ↦ ENNReal.ofReal_le_ofReal (hPosUpper n)
      _ = ENNReal.ofReal (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ) := by
            simpa using
              (ENNReal.continuous_ofReal.tendsto
                (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ)).comp
                hFutureCarrierTendsto |>.liminf_eq
  have hPosCandidateLe :
      ∫ ω in s, (Xtilde t ω)⁺ ∂μ ≤
        ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ := by
    exact (ENNReal.ofReal_le_ofReal_iff hFutureCarrierNonnegLimit).mp hFatouUpper
  -- Proof comment: subtract the converged negative part from the positive-part Fatou bound to
  -- recover the desired upper inequality for the candidate itself.
  linarith [hCandidateDecomp, hPosCandidateLe]

/-- Helper for Theorem 21.24: the set-integral upper sandwich upgrades to the almost-everywhere
fixed-time inequality `Xtilde t ≤ X t`. -/
private lemma candidate_ae_le_fixedTime
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (dyadicRightApprox t n) ω) atTop (𝓝 (Xtilde t ω))) :
    Xtilde t ≤ᵐ[μ] X t := by
  have hXt_int :
      Integrable (Xtilde t) μ :=
    integrable_candidate_of_dyadicRightApprox
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim
  have hSliceMeas : StronglyMeasurable[ℱ t] (X t) := hX.stronglyMeasurable t
  have hTrimLe :
      Xtilde t ≤ᵐ[μ.trim (ℱ.le t)] X t := by
    refine MeasureTheory.ae_le_of_forall_setIntegral_le
      (hXt_int.trim (ℱ.le t) hXt_meas)
      ((hX.integrable t).trim (ℱ.le t) hSliceMeas) ?_
    intro s hs _hμs
    calc
      ∫ ω in s, Xtilde t ω ∂μ.trim (ℱ.le t) = ∫ ω in s, Xtilde t ω ∂μ := by
          symm
          exact MeasureTheory.setIntegral_trim (ℱ.le t) hXt_meas hs
      _ ≤ ∫ ω in s, X t ω ∂μ := by
          exact
            candidate_setIntegral_le_fixedTime
              (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim hs
      _ = ∫ ω in s, X t ω ∂μ.trim (ℱ.le t) := by
          exact MeasureTheory.setIntegral_trim (ℱ.le t) hSliceMeas hs
  exact
    (MeasureTheory.StronglyMeasurable.ae_le_trim_iff
      (ℱ.le t) hXt_meas hSliceMeas).mp hTrimLe

/-- Helper for Theorem 21.24: the conditioned dyadic future slices converge back up to the
candidate, so the time-`t` slice is almost surely bounded above by the candidate. -/
private lemma slice_ae_le_candidate_of_dyadicRightApprox
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (hFiltration :
      ∀ t : NNReal, (⨅ n : ℕ, ℱ (dyadicRightApprox t n)) = ℱ t)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (dyadicRightApprox t n) ω) atTop (𝓝 (Xtilde t ω))) :
    X t ≤ᵐ[μ] Xtilde t := by
  have hXt_int :
      Integrable (Xtilde t) μ :=
    integrable_candidate_of_dyadicRightApprox
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim
  have hCondL1 :
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)
            1 μ)
        atTop
        (𝓝 0) :=
    tendsto_eLpNorm_condExp_dyadicRightApprox_sub_slice
      (X := X) (μ := μ) (ℱ := ℱ) hX hEX_rc t
  have hCondL1' :
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω - X t ω)
            1 μ)
        atTop
        (𝓝 0) := by
    have hEq :
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω - X t ω)
            1 μ) =
          fun n : ℕ ↦
            eLpNorm
              (fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)
              1 μ := by
      funext n
      calc
        eLpNorm
            (fun ω ↦ μ[X (dyadicRightApprox t n) | ℱ t] ω - X t ω)
            1 μ
            = eLpNorm
                (fun ω ↦ -(X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω))
                1 μ := by
                  refine eLpNorm_congr_ae ?_
                  exact ae_of_all μ fun ω ↦ by ring
        _ = eLpNorm
              (fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)
              1 μ := by
                rw [show
                    (fun ω ↦ -(X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω)) =
                      -(fun ω ↦ X t ω - μ[X (dyadicRightApprox t n) | ℱ t] ω) from rfl,
                  eLpNorm_neg]
    rw [hEq]
    exact hCondL1
  have hSliceMeas : StronglyMeasurable[ℱ t] (X t) := hX.stronglyMeasurable t
  have hTrimLe :
      X t ≤ᵐ[μ.trim (ℱ.le t)] Xtilde t := by
    refine MeasureTheory.ae_le_of_forall_setIntegral_le
      ((hX.integrable t).trim (ℱ.le t) hSliceMeas)
      (hXt_int.trim (ℱ.le t) hXt_meas) ?_
    intro s hs _hμs
    have hCondSet :
        Tendsto
          (fun n : ℕ ↦ ∫ ω in s, μ[X (dyadicRightApprox t n) | ℱ t] ω ∂μ)
          atTop
          (𝓝 (∫ ω in s, X t ω ∂μ)) :=
      tendstoRestrictedIntegralOfTendstoL1
        (μ := μ)
        (g := X t)
        (hX.integrable t)
        (fun n ↦ integrable_condExp)
        hCondL1'
    have hCondUpper :
        ∀ n : ℕ,
          ∫ ω in s, μ[X (dyadicRightApprox t n) | ℱ t] ω ∂μ ≤ ∫ ω in s, Xtilde t ω ∂μ := by
      intro n
      have hPointwise :
          μ[X (dyadicRightApprox t n) | ℱ t] ≤ᵐ[μ] Xtilde t :=
        condExp_futureSlice_ae_le_candidate
          (X := X) (μ := μ) (ℱ := ℱ) hX hFiltration t n hXt_lim
      exact
        integral_mono_ae
          (integrable_condExp.restrict)
          hXt_int.restrict
          (ae_restrict_of_ae hPointwise)
    have hSetLe :
        ∫ ω in s, X t ω ∂μ ≤ ∫ ω in s, Xtilde t ω ∂μ := by
      -- Proof comment: the conditioned dyadic future integrals stay below the candidate on every
      -- test set, and their `L¹` convergence forces the time-`t` set integral below the same
      -- bound.
      exact le_of_tendsto_of_tendsto' hCondSet tendsto_const_nhds hCondUpper
    calc
      ∫ ω in s, X t ω ∂μ.trim (ℱ.le t) = ∫ ω in s, X t ω ∂μ := by
          symm
          exact MeasureTheory.setIntegral_trim (ℱ.le t) hSliceMeas hs
      _ ≤ ∫ ω in s, Xtilde t ω ∂μ := hSetLe
      _ = ∫ ω in s, Xtilde t ω ∂μ.trim (ℱ.le t) := by
          exact MeasureTheory.setIntegral_trim (ℱ.le t) hXt_meas hs
  exact
    (MeasureTheory.StronglyMeasurable.ae_le_trim_iff
      (ℱ.le t) hSliceMeas hXt_meas).mp hTrimLe

/-- Helper for Theorem 21.24: once the dyadic future samples converge almost surely to an
`ℱ t`-measurable candidate, the supermartingale inequality and right continuity of expectations
identify that candidate with `X t` almost surely. -/
private lemma aeEq_fixedTime_of_dyadicRightApprox
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (hFiltration :
      ∀ t : NNReal, (⨅ n : ℕ, ℱ (dyadicRightApprox t n)) = ℱ t)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (dyadicRightApprox t n) ω) atTop (𝓝 (Xtilde t ω))) :
    Xtilde t =ᵐ[μ] X t := by
  -- Proof comment: the upper sandwich comes from Fatou on positive parts, while the lower
  -- sandwich comes from the conditioned dyadic future slices converging back to `X t`.
  exact
    (candidate_ae_le_fixedTime
        (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim).antisymm
      (slice_ae_le_candidate_of_dyadicRightApprox
        (X := X) (μ := μ) (ℱ := ℱ) hX hEX_rc hFiltration t hXt_meas hXt_lim)

/-- Helper for Theorem 21.24: the dyadic control candidate keeps the `limUnder` value on the
full-measure control event and is zero on the exceptional set. -/
private noncomputable def dyadicControlCandidate
    (X : NNReal → Ω → ℝ) (A : Set Ω) [DecidablePred (· ∈ A)] (t : NNReal) (ω : Ω) : ℝ :=
  if hω : ω ∈ A then
    limUnder atTop (fun n ↦ X (dyadicRightApprox t n) ω)
  else
    0

/-- Helper for Theorem 21.24: on the control event, the packaged candidate is exactly the
`limUnder` of the exact right-dyadic tail. -/
private lemma dyadicControlCandidate_eq_limUnder_of_mem21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    {t : NNReal} {ω : Ω}
    (hω : ω ∈ A) :
    dyadicControlCandidate X A t ω = limUnder atTop (fun n ↦ X (dyadicRightApprox t n) ω) := by
  -- Proof comment: on the control branch the definition unfolds to the pathwise dyadic limit.
  simp [dyadicControlCandidate, hω]

/-- Helper for Theorem 21.24: outside the control event, the packaged candidate vanishes exactly.
-/
private lemma dyadicControlCandidate_eq_zero_of_not_mem21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    {t : NNReal} {ω : Ω}
    (hω : ω ∉ A) :
    dyadicControlCandidate X A t ω = 0 := by
  -- Proof comment: the exceptional branch of the packaged candidate is the constant zero path.
  simp [dyadicControlCandidate, hω]

/-- Helper for Theorem 21.24: whenever the unclipped dyadic rational already lies below the
horizon `q`, the clipping in `dyadicPointUpTo q N k` is inactive. -/
private lemma dyadicPointUpTo_eq_div_of_le_cutoff21_24
    {q : NNReal} {N k : ℕ}
    (hk : ((k : ℕ) : NNReal) / (2 : NNReal) ^ N ≤ q) :
    dyadicPointUpTo q N k = ((k : ℕ) : NNReal) / (2 : NNReal) ^ N := by
  -- Proof comment: the hypothesis states exactly that the underlying dyadic rational already lies
  -- below `q`, so `min q` leaves it unchanged.
  unfold dyadicPointUpTo
  rw [min_eq_right hk]

/-- Helper for Theorem 21.24: on one common clipped row, the refined exact right-dyadic sample
indices are antitone in the dyadic mesh level. -/
private lemma commonRowRightApproxIndex_antitone21_24
    {q t : NNReal} {m n N : ℕ}
    (hmn : m ≤ n)
    (hnN : n ≤ N)
    (hq : dyadicRightApprox t m ≤ q) :
    let km := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ m) * 2 ^ (N - m)
    let kn := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) * 2 ^ (N - n)
    kn ≤ km := by
  let km : ℕ := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ m) * 2 ^ (N - m)
  let kn : ℕ := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) * 2 ^ (N - n)
  have hmN : m ≤ N := le_trans hmn hnN
  have htail_antitone : dyadicRightApprox t n ≤ dyadicRightApprox t m :=
    (dyadicRightApprox_antitone t) hmn
  have hkm_div :
      ((km : ℕ) : NNReal) / (2 : NNReal) ^ N = dyadicRightApprox t m := by
    -- Proof comment: the common-row index for mesh `m` is just the dyadic-right numerator scaled
    -- by the remaining power of `2`, so dividing by `2^N` cancels that refinement factor.
    have hpow_split : (2 : NNReal) ^ N = (2 : NNReal) ^ m * (2 : NNReal) ^ (N - m) := by
      rw [← pow_add, Nat.add_sub_of_le hmN]
    calc
      ((km : ℕ) : NNReal) / (2 : NNReal) ^ N
          = (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ m) : ℕ) : NNReal) * (2 : NNReal) ^ (N - m)) /
              ((2 : NNReal) ^ m * (2 : NNReal) ^ (N - m)) := by
                simp [km, hpow_split, Nat.cast_mul, Nat.cast_pow]
      _ = (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ m) : ℕ) : NNReal) / (2 : NNReal) ^ m) := by
            exact mul_div_mul_right _ _ (show (2 : NNReal) ^ (N - m) ≠ 0 by positivity)
      _ = dyadicRightApprox t m := by
            simp [dyadicRightApprox]
  have hkn_div :
      ((kn : ℕ) : NNReal) / (2 : NNReal) ^ N = dyadicRightApprox t n := by
    -- Proof comment: the same denominator-cancellation identity holds for the finer mesh `n`.
    have hpow_split : (2 : NNReal) ^ N = (2 : NNReal) ^ n * (2 : NNReal) ^ (N - n) := by
      rw [← pow_add, Nat.add_sub_of_le hnN]
    calc
      ((kn : ℕ) : NNReal) / (2 : NNReal) ^ N
          = (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : NNReal) * (2 : NNReal) ^ (N - n)) /
              ((2 : NNReal) ^ n * (2 : NNReal) ^ (N - n)) := by
                simp [kn, hpow_split, Nat.cast_mul, Nat.cast_pow]
      _ = (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : NNReal) / (2 : NNReal) ^ n) := by
            exact mul_div_mul_right _ _ (show (2 : NNReal) ^ (N - n) ≠ 0 by positivity)
      _ = dyadicRightApprox t n := by
            simp [dyadicRightApprox]
  have hpoint_le :
      ((kn : ℕ) : NNReal) / (2 : NNReal) ^ N ≤ ((km : ℕ) : NNReal) / (2 : NNReal) ^ N := by
    -- Proof comment: after rewriting both common-row indices back to their exact dyadic samples,
    -- the desired order is exactly the antitone order of the right approximants.
    simpa [hkn_div, hkm_div] using htail_antitone
  change kn ≤ km
  exact_mod_cast
    (div_le_div_iff_of_pos_right (show 0 < (2 : NNReal) ^ N by positivity)).1 hpoint_le

/-- Helper for Theorem 21.24: a finite exact upcrossing prefix of the right-dyadic tail refines,
after reversing the pair order, to a closed witness prefix on one common clipped row of `-X`. -/
private lemma rightTailCrossingPrefix_refinesToCommonRow21_24
    {ω : Ω} {t q : NNReal} {N K : ℕ} {a b : ℚ}
    (hN : 0 < N)
    (hab : a < b)
    (hq :
      ∀ m : ℕ, m < N → dyadicRightApprox t m ≤ q)
    (hK :
      K <
        upcrossingsBefore
          (a : ℝ)
          (b : ℝ)
          (fun n ω ↦ X (dyadicRightApprox t n) ω)
          N
          ω) :
    ∃ M : ℕ,
      K <
        upcrossingsBefore
          (-(b : ℝ))
          (-(a : ℝ))
          (fun k ω ↦ -X (dyadicPointUpTo q N k) ω)
          M
          ω := by
  let f : ℕ → Ω → ℝ := fun n ω ↦ X (dyadicRightApprox t n) ω
  let tailLower : Fin (K + 1) → ℕ := fun k ↦
    MeasureTheory.lowerCrossingTime (a : ℝ) (b : ℝ) f N (K - (k : ℕ)) ω
  let tailUpper : Fin (K + 1) → ℕ := fun k ↦
    MeasureTheory.upperCrossingTime (a : ℝ) (b : ℝ) f N (K - (k : ℕ) + 1) ω
  let rowIndex : ℕ → ℕ := fun m ↦ Nat.ceil ((t : ℝ) * (2 : ℝ) ^ m) * 2 ^ (N - m)
  let lowerIndex : Fin (K + 1) → ℕ := fun k ↦ rowIndex (tailUpper k)
  let upperIndex : Fin (K + 1) → ℕ := fun k ↦ rowIndex (tailLower k)
  have habReal : (a : ℝ) < (b : ℝ) := Rat.cast_lt.2 hab
  have hKsucc :
      K + 1 ≤ upcrossingsBefore (a : ℝ) (b : ℝ) f N ω :=
    Nat.succ_le_of_lt hK
  have htailLower_lt :
      ∀ k : Fin (K + 1), tailLower k < N := by
    intro k
    have hk_lt :
        K - (k : ℕ) < upcrossingsBefore (a : ℝ) (b : ℝ) f N ω := by
      exact lt_of_le_of_lt (Nat.sub_le K (k : ℕ)) hK
    -- Proof comment: each lower crossing time in the witness prefix occurs strictly before the
    -- finite prefix horizon `N`.
    simpa [tailLower] using
      (MeasureTheory.lowerCrossingTime_lt_of_lt_upcrossingsBefore
        (a := (a : ℝ))
        (b := (b : ℝ))
        (f := f)
        (N := N)
        (n := K - (k : ℕ))
        (ω := ω)
        hN
        habReal
        hk_lt)
  have htailUpper_lt :
      ∀ k : Fin (K + 1), tailUpper k < N := by
    intro k
    have hk_le :
        K - (k : ℕ) + 1 ≤ upcrossingsBefore (a : ℝ) (b : ℝ) f N ω := by
      exact le_trans (Nat.succ_le_succ (Nat.sub_le K (k : ℕ))) hKsucc
    -- Proof comment: the matching upper crossing time also occurs before `N`.
    simpa [tailUpper] using
      (MeasureTheory.upperCrossingTime_lt_of_le_upcrossingsBefore
        (a := (a : ℝ))
        (b := (b : ℝ))
        (f := f)
        (N := N)
        (n := K - (k : ℕ) + 1)
        (ω := ω)
        hN
        habReal
        hk_le)
  have hLowerValue :
      ∀ k : Fin (K + 1),
        -X (dyadicPointUpTo q N (lowerIndex k)) ω ≤ -(b : ℝ) := by
    intro k
    have hupper_val :
        (b : ℝ) ≤ X (dyadicRightApprox t (tailUpper k)) ω := by
      have hstopped :=
        MeasureTheory.stoppedValue_upperCrossingTime
          (a := (a : ℝ))
          (b := (b : ℝ))
          (f := f)
          (N := N)
          (n := K - (k : ℕ))
          (ω := ω)
          (htailUpper_lt k).ne
      simpa [f, tailUpper, MeasureTheory.stoppedValue, (htailUpper_lt k).ne] using hstopped
    have hrefine :
        dyadicPointUpTo q N (lowerIndex k) = dyadicRightApprox t (tailUpper k) := by
      have := dyadicRightApprox_refine_into_commonRow21_24
        (q := q)
        (t := t)
        (m := tailUpper k)
        (N := N)
        (Nat.le_of_lt (htailUpper_lt k))
        (hq (tailUpper k) (htailUpper_lt k))
      simpa [lowerIndex, rowIndex] using this.2
    -- Proof comment: an upper crossing of `X` becomes a lower closed witness for `-X` after the
    -- common-row refinement.
    simpa [hrefine] using neg_le_neg hupper_val
  have hUpperValue :
      ∀ k : Fin (K + 1),
        -(a : ℝ) ≤ -X (dyadicPointUpTo q N (upperIndex k)) ω := by
    intro k
    have hlower_val :
        X (dyadicRightApprox t (tailLower k)) ω ≤ (a : ℝ) := by
      have hstopped :=
        MeasureTheory.stoppedValue_lowerCrossingTime
          (a := (a : ℝ))
          (b := (b : ℝ))
          (f := f)
          (N := N)
          (n := K - (k : ℕ))
          (ω := ω)
          (htailLower_lt k).ne
      simpa [f, tailLower, MeasureTheory.stoppedValue, (htailLower_lt k).ne] using hstopped
    have hrefine :
        dyadicPointUpTo q N (upperIndex k) = dyadicRightApprox t (tailLower k) := by
      have := dyadicRightApprox_refine_into_commonRow21_24
        (q := q)
        (t := t)
        (m := tailLower k)
        (N := N)
        (Nat.le_of_lt (htailLower_lt k))
        (hq (tailLower k) (htailLower_lt k))
      simpa [upperIndex, rowIndex] using this.2
    -- Proof comment: a lower crossing of `X` becomes an upper closed witness for `-X` on the
    -- sign-reversed interval.
    simpa [hrefine] using neg_le_neg hlower_val
  have hLowerLeUpper :
      ∀ k : Fin (K + 1), lowerIndex k ≤ upperIndex k := by
    intro k
    have hchron :
        tailLower k ≤ tailUpper k :=
      MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ
        (a := (a : ℝ))
        (b := (b : ℝ))
        (f := f)
        (N := N)
        (n := K - (k : ℕ))
        (ω := ω)
    -- Proof comment: chronological order on the exact tail turns into the reversed row-index
    -- order via the antitone common-row embedding.
    simpa [lowerIndex, upperIndex, rowIndex] using
      (commonRowRightApproxIndex_antitone21_24
        (q := q)
        (t := t)
        (m := tailLower k)
        (n := tailUpper k)
        (N := N)
        hchron
        (Nat.le_of_lt (htailUpper_lt k))
        (hq (tailLower k) (htailLower_lt k)))
  have hUpperLeNextLower :
      ∀ j : ℕ, ∀ hj : j < K,
        upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
          lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ := by
    intro j hj
    have hsub :
        K - (j + 1) + 1 = K - j := by
      omega
    have hchron :
        MeasureTheory.upperCrossingTime (a : ℝ) (b : ℝ) f N (K - j) ω ≤
          MeasureTheory.lowerCrossingTime (a : ℝ) (b : ℝ) f N (K - j) ω :=
      MeasureTheory.upperCrossingTime_le_lowerCrossingTime
        (a := (a : ℝ))
        (b := (b : ℝ))
        (f := f)
        (N := N)
        (n := K - j)
        (ω := ω)
    have hupper_lt :
        MeasureTheory.upperCrossingTime (a : ℝ) (b : ℝ) f N (K - j) ω < N := by
      have hk_le :
          K - j ≤ upcrossingsBefore (a : ℝ) (b : ℝ) f N ω := by
        exact le_trans (Nat.sub_le K j) hK.le
      simpa using
        (MeasureTheory.upperCrossingTime_lt_of_le_upcrossingsBefore
          (a := (a : ℝ))
          (b := (b : ℝ))
          (f := f)
          (N := N)
          (n := K - j)
          (ω := ω)
          hN
          habReal
          hk_le)
    have hlower_lt :
        MeasureTheory.lowerCrossingTime (a : ℝ) (b : ℝ) f N (K - j) ω < N := by
      have hk_lt :
          K - j < upcrossingsBefore (a : ℝ) (b : ℝ) f N ω := by
        exact lt_of_le_of_lt (Nat.sub_le K j) hK
      simpa using
        (MeasureTheory.lowerCrossingTime_lt_of_lt_upcrossingsBefore
          (a := (a : ℝ))
          (b := (b : ℝ))
          (f := f)
          (N := N)
          (n := K - j)
          (ω := ω)
          hN
          habReal
          hk_lt)
    -- Proof comment: adjacent reversed pairs are ordered because the previous upper crossing
    -- precedes the next lower crossing before transport to the common row.
    simpa [lowerIndex, upperIndex, tailLower, tailUpper, rowIndex, hsub] using
      (commonRowRightApproxIndex_antitone21_24
        (q := q)
        (t := t)
        (m := MeasureTheory.upperCrossingTime (a : ℝ) (b : ℝ) f N (K - j) ω)
        (n := MeasureTheory.lowerCrossingTime (a : ℝ) (b : ℝ) f N (K - j) ω)
        (N := N)
        hchron
        (Nat.le_of_lt hlower_lt)
        (hq _ hupper_lt))
  refine ⟨upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1, ?_⟩
  exact
    commonRowClosedWitnessPrefix_lt_rowUpcrossingsBefore21_24
      (X := X)
      (q := q)
      (N := N)
      (K := K)
      (ω := ω)
      hab
      lowerIndex
      upperIndex
      hLowerValue
      hUpperValue
      hLowerLeUpper
      hUpperLeNextLower

/-- Helper for Theorem 21.24: one uniform clipped-row envelope bound on the sign-reversed interval
controls every finite exact right-dyadic prefix on the original interval. -/
private lemma rightTailUpcrossingsBefore_le_ofCommonRowEnvelope21_24
    {ω : Ω} {t q : NNReal} {N K : ℕ} {a b : ℚ}
    (hab : a < b)
    (hRowBound :
      ∀ n M : ℕ,
        upcrossingsBefore
            (-(b : ℝ))
            (-(a : ℝ))
            (fun k ω ↦ -X (dyadicPointUpTo q n k) ω)
            M
            ω ≤
          K)
    (hq :
      ∀ m : ℕ, m < N → dyadicRightApprox t m ≤ q) :
    upcrossingsBefore
        (a : ℝ)
        (b : ℝ)
        (fun n ω ↦ X (dyadicRightApprox t n) ω)
        N
        ω ≤
      K := by
  by_cases hN : N = 0
  · -- Proof comment: the zero-length prefix has no upcrossings.
    subst hN
    simp [MeasureTheory.upcrossingsBefore_zero]
  · have hNpos : 0 < N := Nat.pos_iff_ne_zero.mpr hN
    by_contra hBound
    have hlt :
        K <
          upcrossingsBefore
            (a : ℝ)
            (b : ℝ)
            (fun n ω ↦ X (dyadicRightApprox t n) ω)
            N
            ω := by
      exact Nat.lt_of_not_ge hBound
    obtain ⟨M, hM⟩ :=
      rightTailCrossingPrefix_refinesToCommonRow21_24
        (X := X)
        (ω := ω)
        (t := t)
        (q := q)
        (N := N)
        (K := K)
        hNpos
        hab
        hq
        hlt
    -- Proof comment: a strict excess on the exact-right prefix would transport to the common row,
    -- contradicting the assumed row-independent envelope bound there.
    exact (not_le_of_gt hM) (hRowBound N M)

/-- Helper for Theorem 21.24: on the dyadic control event, every exact right-dyadic tail has
finite rational upcrossings because any long exact witness prefix refines to one common clipped row
of `-X`. -/
private lemma dyadicRightTailUpcrossings_lt_top_of_memDyadicControlEvent21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A) (t : NNReal) {a b : ℚ} (hab : a < b) :
    upcrossings (a : ℝ) (b : ℝ) (fun n ω ↦ X (dyadicRightApprox t n) ω) ω < ∞ := by
  let q : ℕ := Nat.ceil (t : ℝ) + 1
  have hneg : (-b) < (-a) := neg_lt_neg hab
  have hEnvelopeRaw :
      (⨆ n : ℕ,
        upcrossings
          (((-b : ℚ) : ℝ))
          (((-a : ℚ) : ℝ))
          (fun k ω ↦ -X (dyadicPointUpTo (q : NNReal) n k) ω)
          ω) < ∞ :=
    (hAcontrol ω hω).1 q (-b) (-a) hneg
  have hEnvelope :
      (⨆ n : ℕ,
        upcrossings
          (-(b : ℝ))
          (-(a : ℝ))
          (fun k ω ↦ -X (dyadicPointUpTo (q : NNReal) n k) ω)
          ω) < ∞ := by
    simpa using hEnvelopeRaw
  obtain ⟨K, hK⟩ :=
    natBoundOfBoundedHorizonDyadicNegRowEnvelope21_24
      (X := X)
      (ω := ω)
      (q := q)
      (a := -b)
      (b := -a)
      hEnvelopeRaw
  have hceil : t ≤ (Nat.ceil (t : ℝ) : NNReal) := by
    exact_mod_cast Nat.le_ceil (t : ℝ)
  have hq :
      ∀ m : ℕ, dyadicRightApprox t m ≤ (q : NNReal) := by
    intro m
    calc
      dyadicRightApprox t m ≤ t + 1 := dyadicRightApprox_le_self_add_one t m
      _ ≤ (Nat.ceil (t : ℝ) : NNReal) + 1 := by
          simpa [add_comm] using add_le_add_right hceil (1 : NNReal)
      _ = (q : NNReal) := by
          simp [q, Nat.cast_add]
  -- Proof comment: after fixing one natural horizon `q` and one row-independent bound `K`, the
  -- common-row bridge turns every finite exact-right prefix into a bounded clipped-row prefix.
  rw [MeasureTheory.upcrossings_lt_top_iff]
  refine ⟨K, ?_⟩
  intro N
  exact
    rightTailUpcrossingsBefore_le_ofCommonRowEnvelope21_24
      (X := X)
      (ω := ω)
      (t := t)
      (q := (q : NNReal))
      (N := N)
      (K := K)
      hab
      (fun n M ↦ by simpa using hK n M)
      (fun m _ ↦ hq m)

/-- Helper for Theorem 21.24: the bounded-grid branch of the dyadic control event forces the exact
right-dyadic tail to have finite norm `liminf` along any fixed time `t`. -/
private lemma dyadicRightApprox_liminf_lt_top_of_memDyadicControlEvent21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A) (t : NNReal) :
    liminf (fun n ↦ (‖X (dyadicRightApprox t n) ω‖₊ : ℝ≥0∞)) atTop < ∞ := by
  let q : ℕ := Nat.ceil (t : ℝ) + 1
  obtain ⟨C, hC⟩ := (hAcontrol ω hω).2 q
  have hAbs :
      ∀ n : ℕ, |X (dyadicRightApprox t n) ω| ≤ |C| := by
    intro n
    have hceil : t ≤ (Nat.ceil (t : ℝ) : NNReal) := by
      exact_mod_cast Nat.le_ceil (t : ℝ)
    have hq :
        dyadicRightApprox t n ≤ (q : NNReal) := by
      calc
        dyadicRightApprox t n ≤ t + 1 := dyadicRightApprox_le_self_add_one t n
        _ ≤ (Nat.ceil (t : ℝ) : NNReal) + 1 := by
            simpa [add_comm] using add_le_add_right hceil (1 : NNReal)
        _ = (q : NNReal) := by
            simp [q, Nat.cast_add]
    have hAbsC :
        |X (dyadicRightApprox t n) ω| ≤ C := by
      exact
        abs_dyadicRightApprox_le_of_dyadicGridAbsMax21_24
          (X := X)
          (q := (q : NNReal))
          (t := t)
          (n := n)
          (ω := ω)
          hq
          (hC n)
    exact hAbsC.trans (le_abs_self C)
  have hFreq :
      ∃ᶠ n : ℕ in atTop, (‖X (dyadicRightApprox t n) ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal |C| := by
    -- Proof comment: the grid bound gives a uniform absolute-value bound on every exact
    -- right-dyadic sample along the fixed horizon `q`.
    let Cnn : NNReal := ⟨|C|, abs_nonneg C⟩
    exact Filter.Frequently.of_forall fun n ↦ by
      have hnn :
          (‖X (dyadicRightApprox t n) ω‖₊ : NNReal) ≤ Cnn := by
        exact_mod_cast hAbs n
      have hnn' :
          ((‖X (dyadicRightApprox t n) ω‖₊ : NNReal) : ℝ≥0∞) ≤
            (Cnn : ℝ≥0∞) := by
        exact_mod_cast hnn
      have hCnn : ENNReal.ofReal |C| = (Cnn : ℝ≥0∞) := by
        simpa [Cnn] using (ENNReal.ofReal_eq_coe_nnreal (abs_nonneg C))
      exact hnn'.trans_eq hCnn.symm
  exact lt_of_le_of_lt (Filter.liminf_le_of_frequently_le' hFreq) (by simp)

/-- Helper for Theorem 21.24: on the dyadic control event, the exact right-dyadic tail converges
to the packaged `limUnder` candidate. -/
private lemma tendsto_dyadicRightApprox_of_memDyadicControlEvent
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A) (t : NNReal) :
    Tendsto
      (fun n ↦ X (dyadicRightApprox t n) ω)
      atTop
      (𝓝 (dyadicControlCandidate X A t ω)) := by
  have hLiminf :
      liminf (fun n ↦ (‖X (dyadicRightApprox t n) ω‖₊ : ℝ≥0∞)) atTop < ∞ :=
    dyadicRightApprox_liminf_lt_top_of_memDyadicControlEvent21_24
      (X := X)
      hAcontrol
      hω
      t
  obtain ⟨c, hc⟩ :=
    MeasureTheory.tendsto_of_uncrossing_lt_top
      (f := fun n ω ↦ X (dyadicRightApprox t n) ω)
      (ω := ω)
      hLiminf
      (fun a b hab ↦
        dyadicRightTailUpcrossings_lt_top_of_memDyadicControlEvent21_24
          (X := X)
          hAcontrol
          hω
          t
          hab)
  have hCandidate :
      dyadicControlCandidate X A t ω = c := by
    -- Proof comment: on the control event, the packaged candidate is exactly the `limUnder` of
    -- this exact-right dyadic tail, and a convergent sequence has `limUnder` equal to its limit.
    rw [dyadicControlCandidate_eq_limUnder_of_mem21_24 (X := X) hω]
    exact hc.limUnder_eq
  simpa [hCandidate] using hc

/-- Helper for Theorem 21.24: a dyadic rational time with denominator `2 ^ n` is fixed by every
finer right-dyadic approximation. -/
private lemma dyadicRightApprox_eq_gridTime21_24
    (k n m : ℕ) (hnm : n ≤ m) :
    dyadicRightApprox ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n)) m =
      (((k : ℕ) : NNReal) / (2 : NNReal) ^ n) := by
  have hceil :
      Nat.ceil
          (((((((k : ℕ) : NNReal) / (2 : NNReal) ^ n) : NNReal) : ℝ) * (2 : ℝ) ^ m)) =
        k * 2 ^ (m - n) := by
    have hpow_split : (2 : NNReal) ^ m = (2 : NNReal) ^ n * (2 : NNReal) ^ (m - n) := by
      rw [← pow_add, Nat.add_sub_of_le hnm]
    have hcalc :
        ((((k : ℕ) : NNReal) / (2 : NNReal) ^ n) : NNReal) * (2 : NNReal) ^ m =
          (k : NNReal) * (2 : NNReal) ^ (m - n) := by
      -- Proof comment: once the finer denominator is split into `2 ^ n * 2 ^ (m - n)`,
      -- cancellation shows that scaling the dyadic grid point by `2 ^ m` gives an integer.
      calc
        (((k : ℕ) : NNReal) / (2 : NNReal) ^ n) * (2 : NNReal) ^ m =
            (((k : NNReal) / (2 : NNReal) ^ n) *
              ((2 : NNReal) ^ n * (2 : NNReal) ^ (m - n))) := by
              rw [hpow_split]
        _ = (k : NNReal) * (2 : NNReal) ^ (m - n) := by
              field_simp
    have hcalcR :
        (((((((k : ℕ) : NNReal) / (2 : NNReal) ^ n) : NNReal) : ℝ) * (2 : ℝ) ^ m)) =
          ((k * 2 ^ (m - n) : ℕ) : ℝ) := by
      simpa [Nat.cast_pow] using congrArg (fun x : NNReal => (x : ℝ)) hcalc
    rw [hcalcR]
    simpa using (Nat.ceil_natCast (R := ℝ) (k * 2 ^ (m - n)))
  unfold dyadicRightApprox
  rw [hceil, Nat.cast_mul, Nat.cast_pow]
  have hpow_split : (2 : NNReal) ^ m = (2 : NNReal) ^ n * (2 : NNReal) ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_of_le hnm]
  rw [hpow_split]
  have hcalc :
      (↑k * ↑(2 ^ (m - n)) : NNReal) / (2 ^ n * 2 ^ (m - n)) = (k : NNReal) / 2 ^ n := by
    -- Proof comment: cancel the common refinement factor from numerator and denominator.
    field_simp
  simpa [Nat.cast_pow] using hcalc

/-- Helper for Theorem 21.24: once a right-dyadic approximation is already exact at mesh `n`, all
finer right-dyadic approximations stay fixed at that same time. -/
private lemma dyadicRightApprox_eq_of_exactMesh21_24
    {s : NNReal} {n m : ℕ}
    (hs : dyadicRightApprox s n = s)
    (hnm : n ≤ m) :
    dyadicRightApprox s m = s := by
  apply le_antisymm
  · calc
      dyadicRightApprox s m ≤ dyadicRightApprox s n := dyadicRightApprox_antitone s hnm
      _ = s := hs
  · exact le_dyadicRightApprox s m

/-- Helper for Theorem 21.24: every finer right approximation of the dyadic right sample
`dyadicRightApprox t n` is still that same sample. -/
private lemma dyadicRightApprox_eq_rightApprox21_24
    (t : NNReal) (n m : ℕ) (hnm : n ≤ m) :
    dyadicRightApprox (dyadicRightApprox t n) m = dyadicRightApprox t n := by
  let k : ℕ := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)
  have hExact :
      dyadicRightApprox (dyadicRightApprox t n) n = dyadicRightApprox t n := by
    -- Proof comment: `dyadicRightApprox t n` is itself a dyadic rational with denominator
    -- `2 ^ n`, so applying the same mesh again does not move it.
    simpa [dyadicRightApprox, k] using
      dyadicRightApprox_eq_gridTime21_24 k n n le_rfl
  exact dyadicRightApprox_eq_of_exactMesh21_24 hExact hnm

/-- Helper for Theorem 21.24: every finer right approximation of the dyadic left sample
`dyadicLeftApprox t n` is still that same sample. -/
private lemma dyadicRightApprox_eq_leftApprox21_24
    (t : Set.Ioi (0 : NNReal)) (n m : ℕ) (hnm : n ≤ m) :
    dyadicRightApprox (dyadicLeftApprox t n) m = dyadicLeftApprox t n := by
  let k : ℕ := Nat.ceil ((t.1 : ℝ) * (2 : ℝ) ^ n) - 1
  have hExact :
      dyadicRightApprox (dyadicLeftApprox t n) n = dyadicLeftApprox t n := by
    -- Proof comment: the left dyadic sample is also a dyadic rational on the same mesh `2 ^ n`.
    simpa [dyadicLeftApprox, dyadicRightApprox, k] using
      dyadicRightApprox_eq_gridTime21_24 k n n le_rfl
  exact dyadicRightApprox_eq_of_exactMesh21_24 hExact hnm

/-- Helper for Theorem 21.24: if the future right-dyadic tail of `s` is eventually constant, then
the packaged candidate at time `s` agrees with that exact sample value. -/
private lemma dyadicControlCandidate_eq_exact_of_stableRightApprox21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    {ω : Ω} (hω : ω ∈ A)
    {s : NNReal} {n : ℕ}
    (hstable : ∀ m : ℕ, n ≤ m → dyadicRightApprox s m = s) :
    dyadicControlCandidate X A s ω = X s ω := by
  rw [dyadicControlCandidate_eq_limUnder_of_mem21_24 (X := X) hω]
  have hEventuallyConst :
      (fun m ↦ X (dyadicRightApprox s m) ω) =ᶠ[atTop] fun _ : ℕ ↦ X s ω := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨n, ?_⟩
    intro m hm
    simp [hstable m hm]
  -- Proof comment: replace the tail by the eventually constant exact sample sequence and take
  -- its `limUnder`.
  exact
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ X s ω) atTop (𝓝 (X s ω))).congr'
      hEventuallyConst.symm).limUnder_eq

/-- Helper for Theorem 21.24: at every exact dyadic right sample time, the packaged candidate
agrees with the raw sample value. -/
private lemma dyadicControlCandidate_eq_exact_rightApprox_of_mem21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    {ω : Ω} (hω : ω ∈ A)
    (t : NNReal) (n : ℕ) :
    dyadicControlCandidate X A (dyadicRightApprox t n) ω =
      X (dyadicRightApprox t n) ω := by
  refine
    dyadicControlCandidate_eq_exact_of_stableRightApprox21_24
      (X := X)
      (A := A)
      hω
      (s := dyadicRightApprox t n)
      (n := n)
      ?_
  intro m hm
  exact dyadicRightApprox_eq_rightApprox21_24 t n m hm

/-- Helper for Theorem 21.24: at every exact dyadic left sample time, the packaged candidate
agrees with the raw sample value. -/
private lemma dyadicControlCandidate_eq_exact_leftApprox_of_mem21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    {ω : Ω} (hω : ω ∈ A)
    (t : Set.Ioi (0 : NNReal)) (n : ℕ) :
    dyadicControlCandidate X A (dyadicLeftApprox t n) ω =
      X (dyadicLeftApprox t n) ω := by
  refine
    dyadicControlCandidate_eq_exact_of_stableRightApprox21_24
      (X := X)
      (A := A)
      hω
      (s := dyadicLeftApprox t n)
      (n := n)
      ?_
  intro m hm
  exact dyadicRightApprox_eq_leftApprox21_24 t n m hm

/-- Helper for Theorem 21.24: a strict upper bound on the packaged candidate at time `s`
eventually bounds every exact right-dyadic sample of the raw path below the same level. -/
private lemma eventually_lt_exactRightApprox_of_candidate_lt21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    {s : NNReal} {c : ℝ}
    (hsc : dyadicControlCandidate X A s ω < c) :
    ∀ᶠ n : ℕ in atTop, X (dyadicRightApprox s n) ω < c := by
  have hTail :
      Tendsto
        (fun n ↦ X (dyadicRightApprox s n) ω)
        atTop
        (𝓝 (dyadicControlCandidate X A s ω)) :=
    tendsto_dyadicRightApprox_of_memDyadicControlEvent
      (X := X)
      hAcontrol
      hω
      s
  -- Proof comment: once the exact right-dyadic tail converges to the packaged candidate value,
  -- every strict upper neighborhood of that limit eventually contains the tail.
  exact (tendsto_order.1 hTail).2 _ hsc

/-- Helper for Theorem 21.24: a strict lower bound on the packaged candidate at time `s`
eventually bounds every exact right-dyadic sample of the raw path above the same level. -/
private lemma eventually_exactRightApprox_lt_of_lt_candidate21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    {s : NNReal} {c : ℝ}
    (hcs : c < dyadicControlCandidate X A s ω) :
    ∀ᶠ n : ℕ in atTop, c < X (dyadicRightApprox s n) ω := by
  have hTail :
      Tendsto
        (fun n ↦ X (dyadicRightApprox s n) ω)
        atTop
        (𝓝 (dyadicControlCandidate X A s ω)) :=
    tendsto_dyadicRightApprox_of_memDyadicControlEvent
      (X := X)
      hAcontrol
      hω
      s
  -- Proof comment: the same order-neighborhood argument gives the eventual strict lower bound.
  exact (tendsto_order.1 hTail).1 _ hcs

/-- Helper for Theorem 21.24: finitely many strict candidate lower/upper witnesses can be
realized simultaneously on one exact right-dyadic mesh. -/
private lemma commonMeshExactRightWitnesses_of_candidatePrefix21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    {K : ℕ}
    (lowerTime upperTime : Fin (K + 1) → NNReal)
    {cLower cUpper : ℝ}
    (hLower :
      ∀ k : Fin (K + 1), cLower < dyadicControlCandidate X A (lowerTime k) ω)
    (hUpper :
      ∀ k : Fin (K + 1), dyadicControlCandidate X A (upperTime k) ω < cUpper) :
    ∃ N : ℕ,
      (∀ k : Fin (K + 1), cLower < X (dyadicRightApprox (lowerTime k) N) ω) ∧
      ∀ k : Fin (K + 1), X (dyadicRightApprox (upperTime k) N) ω < cUpper := by
  have hLowerEventually :
      ∀ k : Fin (K + 1),
        ∃ N : ℕ, ∀ n ≥ N, cLower < X (dyadicRightApprox (lowerTime k) n) ω := by
    intro k
    -- Proof comment: each lower witness gives one eventual lower bound on the exact right tail.
    simpa [Filter.eventually_atTop] using
      eventually_exactRightApprox_lt_of_lt_candidate21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
        (s := lowerTime k)
        (c := cLower)
        (hLower k)
  have hUpperEventually :
      ∀ k : Fin (K + 1),
        ∃ N : ℕ, ∀ n ≥ N, X (dyadicRightApprox (upperTime k) n) ω < cUpper := by
    intro k
    -- Proof comment: each upper witness gives one eventual upper bound on the exact right tail.
    simpa [Filter.eventually_atTop] using
      eventually_lt_exactRightApprox_of_candidate_lt21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
        (s := upperTime k)
        (c := cUpper)
        (hUpper k)
  choose lowerMesh hLowerMesh using hLowerEventually
  choose upperMesh hUpperMesh using hUpperEventually
  let N : ℕ := max (Finset.univ.sup lowerMesh) (Finset.univ.sup upperMesh)
  refine ⟨N, ?_, ?_⟩
  · intro k
    have hkLower : lowerMesh k ≤ N := by
      exact le_trans (Finset.le_sup (s := Finset.univ) (f := lowerMesh) (by simp)) (le_max_left _ _)
    -- Proof comment: taking the maximum of all lower thresholds forces every lower witness on the
    -- same common mesh.
    exact hLowerMesh k N hkLower
  · intro k
    have hkUpper : upperMesh k ≤ N := by
      exact le_trans (Finset.le_sup (s := Finset.univ) (f := upperMesh) (by simp)) (le_max_right _ _)
    -- Proof comment: the same common mesh also dominates every upper-witness threshold.
    exact hUpperMesh k N hkUpper

/-- Helper for Theorem 21.24: along the canonical right-dyadic anchor sequence, the packaged
candidate converges to its value at `t`. -/
private lemma tendsto_dyadicControlCandidateAlongRightApprox_of_memDyadicControlEvent21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A) (t : NNReal) :
    Tendsto
      (fun n ↦ dyadicControlCandidate X A (dyadicRightApprox t n) ω)
      atTop
      (𝓝 (dyadicControlCandidate X A t ω)) := by
  have hTail :
      Tendsto
        (fun n ↦ X (dyadicRightApprox t n) ω)
        atTop
        (𝓝 (dyadicControlCandidate X A t ω)) :=
    tendsto_dyadicRightApprox_of_memDyadicControlEvent
      (X := X)
      hAcontrol
      hω
      t
  have hEq :
      (fun n ↦ dyadicControlCandidate X A (dyadicRightApprox t n) ω) =ᶠ[atTop]
        (fun n ↦ X (dyadicRightApprox t n) ω) := by
    filter_upwards with n
    exact dyadicControlCandidate_eq_exact_rightApprox_of_mem21_24 (X := X) hω t n
  -- Proof comment: each candidate value on the right-dyadic anchor is already the exact sample,
  -- so the raw exact-right convergence theorem identifies the anchor limit for the packaged path.
  exact hTail.congr' hEq.symm

/-- Helper for Theorem 21.24: one bounded dyadic grid on `[0, q]` bounds the packaged candidate
at every time whose exact right approximants stay in that horizon. -/
private lemma abs_dyadicControlCandidate_le_of_gridBound21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    {t q : NNReal} {C : ℝ}
    (hC : ∀ n : ℕ, dyadicGridAbsMax21_24 (X := X) q n ω ≤ C)
    (htq : t + 1 ≤ q) :
    |dyadicControlCandidate X A t ω| ≤ |C| := by
  have hTail :
      Tendsto
        (fun n ↦ X (dyadicRightApprox t n) ω)
        atTop
        (𝓝 (dyadicControlCandidate X A t ω)) :=
    tendsto_dyadicRightApprox_of_memDyadicControlEvent
      (X := X)
      hAcontrol
      hω
      t
  have hSamples :
      ∀ n : ℕ, X (dyadicRightApprox t n) ω ∈ Set.Icc (-|C|) |C| := by
    intro n
    have hq :
        dyadicRightApprox t n ≤ q := by
      exact (dyadicRightApprox_le_self_add_one t n).trans htq
    have hAbsC :
        |X (dyadicRightApprox t n) ω| ≤ C :=
      abs_dyadicRightApprox_le_of_dyadicGridAbsMax21_24
        (X := X)
        (q := q)
        (t := t)
        (n := n)
        (ω := ω)
        hq
        (hC n)
    have hAbs : |X (dyadicRightApprox t n) ω| ≤ |C| := hAbsC.trans (le_abs_self C)
    exact abs_le.mp hAbs
  have hCandidateMem :
      dyadicControlCandidate X A t ω ∈ Set.Icc (-|C|) |C| := by
    -- Proof comment: the interval is closed, so it contains the limit of the bounded exact-right
    -- dyadic tail.
    exact
      isClosed_Icc.mem_of_tendsto
        hTail
        (Filter.Eventually.of_forall hSamples)
  exact abs_le.2 hCandidateMem

/-- Helper for Theorem 21.24: bounded candidate samples have finite norm liminf on the dyadic
control event. -/
private lemma candidateNormLiminf_lt_top_of_boundedSeq_of_memDyadicControlEvent21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    (τ : ℕ → NNReal)
    (hτ : ∃ q : ℕ, ∀ n : ℕ, τ n ≤ q) :
    liminf (fun n ↦ (‖dyadicControlCandidate X A (τ n) ω‖₊ : ℝ≥0∞)) atTop < ∞ := by
  rcases hτ with ⟨q, hq⟩
  obtain ⟨C, hC⟩ := (hAcontrol ω hω).2 (q + 1)
  have hAbs :
      ∀ n : ℕ, |dyadicControlCandidate X A (τ n) ω| ≤ |C| := by
    intro n
    have hτq :
        τ n + 1 ≤ ((q + 1 : ℕ) : NNReal) := by
      calc
        τ n + 1 = 1 + τ n := by rw [add_comm]
        _ ≤ 1 + (q : NNReal) := by
          simpa [add_comm] using add_le_add_left (hq n) (1 : NNReal)
        _ = (q : NNReal) + 1 := by rw [add_comm]
        _ = ((q + 1 : ℕ) : NNReal) := by
            simp [Nat.cast_add]
    exact
      abs_dyadicControlCandidate_le_of_gridBound21_24
        (X := X)
        hAcontrol
        hω
        (t := τ n)
        (q := ((q + 1 : ℕ) : NNReal))
        (C := C)
        hC
        hτq
  have hFreq :
      ∃ᶠ n : ℕ in atTop,
        (‖dyadicControlCandidate X A (τ n) ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal |C| := by
    -- Proof comment: the bounded-horizon candidate estimate gives a uniform norm bound on every
    -- sampled candidate value, hence certainly on a frequent tail.
    let Cnn : NNReal := ⟨|C|, abs_nonneg C⟩
    exact Filter.Frequently.of_forall fun n ↦ by
      have hnn :
          (‖dyadicControlCandidate X A (τ n) ω‖₊ : NNReal) ≤ Cnn := by
        exact_mod_cast hAbs n
      have hnn' :
          ((‖dyadicControlCandidate X A (τ n) ω‖₊ : NNReal) : ℝ≥0∞) ≤
            (Cnn : ℝ≥0∞) := by
        exact_mod_cast hnn
      have hCnn : ENNReal.ofReal |C| = (Cnn : ℝ≥0∞) := by
        simpa [Cnn] using (ENNReal.ofReal_eq_coe_nnreal (abs_nonneg C))
      exact hnn'.trans_eq hCnn.symm
  exact lt_of_le_of_lt (Filter.liminf_le_of_frequently_le' hFreq) (by simp)

/-- Helper for Theorem 21.24: every rational interval contains two rational interior points. -/
private lemma exists_two_rat_between21_24
    {a b : ℚ} (hab : a < b) :
    ∃ r s : ℚ, a < r ∧ r < s ∧ s < b := by
  refine ⟨(2 * a + b) / 3, (a + 2 * b) / 3, ?_, ?_, ?_⟩ <;> linarith

/-- Helper for Theorem 21.24: on one fixed common mesh, the dyadic-row index is monotone in the
sample time. -/
private lemma commonMeshIndex_mono21_24
    {N : ℕ} {s t : NNReal} (hst : s ≤ t) :
    Nat.ceil ((s : ℝ) * (2 : ℝ) ^ N) ≤ Nat.ceil ((t : ℝ) * (2 : ℝ) ^ N) := by
  -- Proof comment: scaling by the positive mesh denominator preserves the time order, and
  -- `Nat.ceil` is monotone on real numbers.
  refine Nat.ceil_mono ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hst) (by positivity)

/-- Helper for Theorem 21.24: if the sampled times are monotone increasing and bounded, then the
negated candidate samples have finite rational upcrossings on the control event. -/
private lemma monotoneNegCandidateUpcrossings_lt_top_of_memDyadicControlEvent21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    {τ : ℕ → NNReal} (hτmono : Monotone τ)
    (hτbdd : ∃ q : ℕ, ∀ n : ℕ, τ n ≤ q)
    {a b : ℚ} (hab : a < b) :
    upcrossings (a : ℝ) (b : ℝ)
      (fun n ω ↦ -dyadicControlCandidate X A (τ n) ω) ω < ∞ := by
  rcases hτbdd with ⟨q, hq⟩
  obtain ⟨r, s, har, hrs, hsb⟩ :=
    exists_two_rat_between21_24 (a := a) (b := b) hab
  obtain ⟨K, hK⟩ :=
    natBoundOfBoundedHorizonDyadicNegRowEnvelope21_24
      (X := X)
      (ω := ω)
      (q := q + 1)
      (a := r)
      (b := s)
      ((hAcontrol ω hω).1 (q + 1) r s hrs)
  rw [MeasureTheory.upcrossings_lt_top_iff]
  refine ⟨K, ?_⟩
  intro M
  by_cases hM : M = 0
  · subst hM
    simp [MeasureTheory.upcrossingsBefore_zero]
  · have hMpos : 0 < M := Nat.pos_iff_ne_zero.mpr hM
    by_contra hBound
    have hlt :
        K <
          upcrossingsBefore
            (a : ℝ)
            (b : ℝ)
            (fun n ω ↦ -dyadicControlCandidate X A (τ n) ω)
            M
            ω := Nat.lt_of_not_ge hBound
    let f : ℕ → Ω → ℝ := fun n ω ↦ -dyadicControlCandidate X A (τ n) ω
    let lowerStep : Fin (K + 1) → ℕ := fun k ↦
      MeasureTheory.lowerCrossingTime (a : ℝ) (b : ℝ) f M (k : ℕ) ω
    let upperStep : Fin (K + 1) → ℕ := fun k ↦
      MeasureTheory.upperCrossingTime (a : ℝ) (b : ℝ) f M ((k : ℕ) + 1) ω
    let lowerTime : Fin (K + 1) → NNReal := fun k ↦ τ (lowerStep k)
    let upperTime : Fin (K + 1) → NNReal := fun k ↦ τ (upperStep k)
    have habReal : (a : ℝ) < (b : ℝ) := Rat.cast_lt.2 hab
    have hKsucc :
        K + 1 ≤
          upcrossingsBefore
            (a : ℝ)
            (b : ℝ)
            (fun n ω ↦ -dyadicControlCandidate X A (τ n) ω)
            M
            ω := Nat.succ_le_of_lt hlt
    obtain ⟨N, hLowerMesh, hUpperMesh⟩ :=
      commonMeshExactRightWitnesses_of_candidatePrefix21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
        lowerTime
        upperTime
        (cLower := (-((r : ℚ) : ℝ)))
        (cUpper := (-((s : ℚ) : ℝ)))
        (fun k ↦ by
          have hLowerLt :
              lowerStep k < M := by
            have hk_lt :
                (k : ℕ) <
                  upcrossingsBefore
                    (a : ℝ)
                    (b : ℝ)
                    (fun n ω ↦ -dyadicControlCandidate X A (τ n) ω)
                    M
                    ω := lt_of_le_of_lt (Nat.le_of_lt_succ k.2) hlt
            -- Proof comment: each lower crossing in the witness prefix occurs strictly before the
            -- finite horizon `M`.
            simpa [lowerStep] using
              (MeasureTheory.lowerCrossingTime_lt_of_lt_upcrossingsBefore
                (a := (a : ℝ))
                (b := (b : ℝ))
                (f := f)
                (N := M)
                (n := k.1)
                (ω := ω)
                hMpos
                habReal
                hk_lt)
          have hStopped :=
            MeasureTheory.stoppedValue_lowerCrossingTime
              (a := (a : ℝ))
              (b := (b : ℝ))
              (f := f)
              (N := M)
              (n := k.1)
              (ω := ω)
              hLowerLt.ne
          -- Proof comment: a lower crossing for the negated sampled candidate means the original
          -- candidate is already above the inner lower rational barrier `-r`.
          have hCandidateGe :
              -((a : ℚ) : ℝ) ≤ dyadicControlCandidate X A (lowerTime k) ω := by
            simpa [f, lowerStep, lowerTime, MeasureTheory.stoppedValue, hLowerLt.ne] using
              (neg_le_neg hStopped)
          exact lt_of_lt_of_le (show -((r : ℚ) : ℝ) < -((a : ℚ) : ℝ) by
            exact neg_lt_neg (Rat.cast_lt.2 har)) hCandidateGe)
        (fun k ↦ by
          have hUpperLt :
              upperStep k < M := by
            have hk_le :
                (k : ℕ) + 1 ≤
                  upcrossingsBefore
                    (a : ℝ)
                    (b : ℝ)
                    (fun n ω ↦ -dyadicControlCandidate X A (τ n) ω)
                    M
                    ω := le_trans (Nat.succ_le_succ (Nat.le_of_lt_succ k.2)) hKsucc
            -- Proof comment: the matching upper crossings also occur before the finite horizon.
            simpa [upperStep] using
              (MeasureTheory.upperCrossingTime_lt_of_le_upcrossingsBefore
                (a := (a : ℝ))
                (b := (b : ℝ))
                (f := f)
                (N := M)
                (n := (k : ℕ) + 1)
                (ω := ω)
                hMpos
                habReal
                hk_le)
          have hStopped :=
            MeasureTheory.stoppedValue_upperCrossingTime
              (a := (a : ℝ))
              (b := (b : ℝ))
              (f := f)
              (N := M)
              (n := k.1)
              (ω := ω)
              hUpperLt.ne
          -- Proof comment: an upper crossing for the negated candidate forces the original
          -- candidate below the inner upper rational barrier `-s`.
          have hCandidateLe :
              dyadicControlCandidate X A (upperTime k) ω ≤ -((b : ℚ) : ℝ) := by
            simpa [f, upperStep, upperTime, MeasureTheory.stoppedValue, hUpperLt.ne] using
              (neg_le_neg hStopped)
          exact lt_of_le_of_lt hCandidateLe (show -((b : ℚ) : ℝ) < -((s : ℚ) : ℝ) by
            exact neg_lt_neg (Rat.cast_lt.2 hsb)))
    let lowerIndex : Fin (K + 1) → ℕ := fun k ↦ Nat.ceil (((lowerTime k : NNReal) : ℝ) * (2 : ℝ) ^ N)
    let upperIndex : Fin (K + 1) → ℕ := fun k ↦ Nat.ceil (((upperTime k : NNReal) : ℝ) * (2 : ℝ) ^ N)
    have hLowerValue :
        ∀ k : Fin (K + 1),
          -X (dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N (lowerIndex k)) ω < -((-r : ℚ) : ℝ) := by
      intro k
      have hUpperBound :
          dyadicRightApprox (lowerTime k) N ≤ ((q + 1 : ℕ) : NNReal) := by
        calc
          dyadicRightApprox (lowerTime k) N ≤ lowerTime k + 1 :=
            dyadicRightApprox_le_self_add_one (lowerTime k) N
          _ ≤ (q : NNReal) + 1 := by
              simpa [lowerTime] using add_le_add_right (hq (lowerStep k)) (1 : NNReal)
          _ = ((q + 1 : ℕ) : NNReal) := by simp [Nat.cast_add]
      have hRefine :
          dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N (lowerIndex k) =
            dyadicRightApprox (lowerTime k) N := by
        have hk :
            ((lowerIndex k : ℕ) : NNReal) / (2 : NNReal) ^ N ≤ ((q + 1 : ℕ) : NNReal) := by
          simpa [lowerIndex, dyadicRightApprox] using hUpperBound
        rw [dyadicPointUpTo_eq_div_of_le_cutoff21_24 hk, dyadicRightApprox]
      -- Proof comment: after moving the lower witnesses onto one mesh, sign reversal turns the
      -- exact sample inequality into a lower witness for the row of `-X`.
      rw [hRefine]
      simpa using neg_lt_neg (hLowerMesh k)
    have hUpperValue :
        ∀ k : Fin (K + 1),
          -((-s : ℚ) : ℝ) < -X (dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N (upperIndex k)) ω := by
      intro k
      have hUpperBound :
          dyadicRightApprox (upperTime k) N ≤ ((q + 1 : ℕ) : NNReal) := by
        calc
          dyadicRightApprox (upperTime k) N ≤ upperTime k + 1 :=
            dyadicRightApprox_le_self_add_one (upperTime k) N
          _ ≤ (q : NNReal) + 1 := by
              simpa [upperTime] using add_le_add_right (hq (upperStep k)) (1 : NNReal)
          _ = ((q + 1 : ℕ) : NNReal) := by simp [Nat.cast_add]
      have hRefine :
          dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N (upperIndex k) =
            dyadicRightApprox (upperTime k) N := by
        have hk :
            ((upperIndex k : ℕ) : NNReal) / (2 : NNReal) ^ N ≤ ((q + 1 : ℕ) : NNReal) := by
          simpa [upperIndex, dyadicRightApprox] using hUpperBound
        rw [dyadicPointUpTo_eq_div_of_le_cutoff21_24 hk, dyadicRightApprox]
      -- Proof comment: the upper exact witnesses similarly become upper witnesses on the row of
      -- `-X`.
      rw [hRefine]
      simpa using neg_lt_neg (hUpperMesh k)
    have hLowerLeUpper :
        ∀ k : Fin (K + 1), lowerIndex k ≤ upperIndex k := by
      intro k
      have hChron :
          lowerStep k ≤ upperStep k :=
        MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ
          (a := (a : ℝ))
          (b := (b : ℝ))
          (f := f)
          (N := M)
          (n := k)
          (ω := ω)
      -- Proof comment: for increasing sampled times, the common-mesh row indices preserve the
      -- lower/upper chronology of the sampled candidate crossings.
      change
        Nat.ceil (((lowerTime k : NNReal) : ℝ) * (2 : ℝ) ^ N) ≤
          Nat.ceil (((upperTime k : NNReal) : ℝ) * (2 : ℝ) ^ N)
      exact commonMeshIndex_mono21_24 (N := N) (hτmono hChron)
    have hUpperLeNextLower :
        ∀ j : ℕ, ∀ hj : j < K,
          upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
            lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ := by
      intro j hj
      have hChron :
          upperStep ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
            lowerStep ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ :=
        MeasureTheory.upperCrossingTime_le_lowerCrossingTime
          (a := (a : ℝ))
          (b := (b : ℝ))
          (f := f)
          (N := M)
          (n := j + 1)
          (ω := ω)
      -- Proof comment: the next lower witness comes after the current upper witness, and the
      -- deterministic time change keeps that order on the common mesh.
      change
        Nat.ceil ((((upperTime ⟨j, Nat.lt_succ_of_lt hj⟩ : NNReal) : ℝ) * (2 : ℝ) ^ N)) ≤
          Nat.ceil
            ((((lowerTime ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ : NNReal) : ℝ) *
              (2 : ℝ) ^ N))
      exact commonMeshIndex_mono21_24 (N := N) (hτmono hChron)
    have hRow :
        K <
          upcrossingsBefore
            (r : ℝ)
            (s : ℝ)
            (fun k ω ↦ -X (dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N k) ω)
            (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1)
            ω := by
      simpa using
        (commonRowWitnessPrefix_lt_rowUpcrossingsBefore21_24
          (X := X)
          (q := ((q + 1 : ℕ) : NNReal))
          (N := N)
          (K := K)
          (ω := ω)
          (a := -s)
          (b := -r)
          (by exact neg_lt_neg hrs)
          lowerIndex
          upperIndex
          hLowerValue
          hUpperValue
          hLowerLeUpper
          hUpperLeNextLower)
    exact (not_le_of_gt hRow) (by simpa using hK N (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1))

/-- Helper for Theorem 21.24: if the sampled times are monotone decreasing and bounded, then the
candidate samples have finite rational upcrossings on the control event. -/
private lemma antitoneCandidateUpcrossings_lt_top_of_memDyadicControlEvent21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    {τ : ℕ → NNReal} (hτanti : Antitone τ)
    (hτbdd : ∃ q : ℕ, ∀ n : ℕ, τ n ≤ q)
    {a b : ℚ} (hab : a < b) :
    upcrossings (a : ℝ) (b : ℝ)
      (fun n ω ↦ dyadicControlCandidate X A (τ n) ω) ω < ∞ := by
  rcases hτbdd with ⟨q, hq⟩
  obtain ⟨r, s, har, hrs, hsb⟩ :=
    exists_two_rat_between21_24 (a := a) (b := b) hab
  have hnegInterval : (-s : ℚ) < -r := by
    exact neg_lt_neg hrs
  obtain ⟨K, hK⟩ :=
    natBoundOfBoundedHorizonDyadicNegRowEnvelope21_24
      (X := X)
      (ω := ω)
      (q := q + 1)
      (a := -s)
      (b := -r)
      ((hAcontrol ω hω).1 (q + 1) (-s) (-r) hnegInterval)
  rw [MeasureTheory.upcrossings_lt_top_iff]
  refine ⟨K, ?_⟩
  intro M
  by_cases hM : M = 0
  · subst hM
    simp [MeasureTheory.upcrossingsBefore_zero]
  · have hMpos : 0 < M := Nat.pos_iff_ne_zero.mpr hM
    by_contra hBound
    have hlt :
        K <
          upcrossingsBefore
            (a : ℝ)
            (b : ℝ)
            (fun n ω ↦ dyadicControlCandidate X A (τ n) ω)
            M
            ω := Nat.lt_of_not_ge hBound
    let f : ℕ → Ω → ℝ := fun n ω ↦ dyadicControlCandidate X A (τ n) ω
    let tailLower : Fin (K + 1) → ℕ := fun k ↦
      MeasureTheory.lowerCrossingTime (a : ℝ) (b : ℝ) f M (K - (k : ℕ)) ω
    let tailUpper : Fin (K + 1) → ℕ := fun k ↦
      MeasureTheory.upperCrossingTime (a : ℝ) (b : ℝ) f M (K - (k : ℕ) + 1) ω
    let lowerTime : Fin (K + 1) → NNReal := fun k ↦ τ (tailUpper k)
    let upperTime : Fin (K + 1) → NNReal := fun k ↦ τ (tailLower k)
    have habReal : (a : ℝ) < (b : ℝ) := Rat.cast_lt.2 hab
    have hKsucc :
        K + 1 ≤
          upcrossingsBefore
            (a : ℝ)
            (b : ℝ)
            (fun n ω ↦ dyadicControlCandidate X A (τ n) ω)
            M
            ω := Nat.succ_le_of_lt hlt
    obtain ⟨N, hLowerMesh, hUpperMesh⟩ :=
      commonMeshExactRightWitnesses_of_candidatePrefix21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
        lowerTime
        upperTime
        (cLower := (s : ℝ))
        (cUpper := (r : ℝ))
        (fun k ↦ by
          have hUpperLt :
              tailUpper k < M := by
            have hk_le :
                K - (k : ℕ) + 1 ≤
                  upcrossingsBefore
                    (a : ℝ)
                    (b : ℝ)
                    (fun n ω ↦ dyadicControlCandidate X A (τ n) ω)
                    M
                    ω := le_trans (Nat.succ_le_succ (Nat.sub_le K (k : ℕ))) hKsucc
            -- Proof comment: the reversed upper-crossing witnesses are still inside the finite
            -- sampled prefix.
            simpa [tailUpper] using
              (MeasureTheory.upperCrossingTime_lt_of_le_upcrossingsBefore
                (a := (a : ℝ))
                (b := (b : ℝ))
                (f := f)
                (N := M)
                (n := K - (k : ℕ) + 1)
                (ω := ω)
                hMpos
                habReal
                hk_le)
          have hStopped :=
            MeasureTheory.stoppedValue_upperCrossingTime
              (a := (a : ℝ))
              (b := (b : ℝ))
              (f := f)
              (N := M)
              (n := K - (k : ℕ))
              (ω := ω)
              hUpperLt.ne
          -- Proof comment: an upper crossing of the sampled candidate sits above the interior
          -- upper rational `s`.
          have hCandidateGe :
              ((b : ℚ) : ℝ) ≤ dyadicControlCandidate X A (lowerTime k) ω := by
            simpa [f, tailUpper, lowerTime, MeasureTheory.stoppedValue, hUpperLt.ne] using hStopped
          exact lt_of_lt_of_le (show (s : ℝ) < (b : ℝ) by exact_mod_cast hsb) hCandidateGe)
        (fun k ↦ by
          have hLowerLt :
              tailLower k < M := by
            have hk_lt :
                K - (k : ℕ) <
                  upcrossingsBefore
                    (a : ℝ)
                    (b : ℝ)
                    (fun n ω ↦ dyadicControlCandidate X A (τ n) ω)
                    M
                    ω := lt_of_le_of_lt (Nat.sub_le K (k : ℕ)) hlt
            -- Proof comment: the matching reversed lower crossings also stay before the finite
            -- horizon.
            simpa [tailLower] using
              (MeasureTheory.lowerCrossingTime_lt_of_lt_upcrossingsBefore
                (a := (a : ℝ))
                (b := (b : ℝ))
                (f := f)
                (N := M)
                (n := K - (k : ℕ))
                (ω := ω)
                hMpos
                habReal
                hk_lt)
          have hStopped :=
            MeasureTheory.stoppedValue_lowerCrossingTime
              (a := (a : ℝ))
              (b := (b : ℝ))
              (f := f)
              (N := M)
              (n := K - (k : ℕ))
              (ω := ω)
              hLowerLt.ne
          -- Proof comment: a lower crossing is already below the interior lower rational `r`.
          have hCandidateLe :
              dyadicControlCandidate X A (upperTime k) ω ≤ ((a : ℚ) : ℝ) := by
            simpa [f, tailLower, upperTime, MeasureTheory.stoppedValue, hLowerLt.ne] using hStopped
          exact lt_of_le_of_lt hCandidateLe (show (a : ℝ) < (r : ℝ) by exact_mod_cast har))
    let lowerIndex : Fin (K + 1) → ℕ := fun k ↦ Nat.ceil (((lowerTime k : NNReal) : ℝ) * (2 : ℝ) ^ N)
    let upperIndex : Fin (K + 1) → ℕ := fun k ↦ Nat.ceil (((upperTime k : NNReal) : ℝ) * (2 : ℝ) ^ N)
    have hLowerValue :
        ∀ k : Fin (K + 1),
          -X (dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N (lowerIndex k)) ω < -((s : ℚ) : ℝ) := by
      intro k
      have hUpperBound :
          dyadicRightApprox (lowerTime k) N ≤ ((q + 1 : ℕ) : NNReal) := by
        calc
          dyadicRightApprox (lowerTime k) N ≤ lowerTime k + 1 :=
            dyadicRightApprox_le_self_add_one (lowerTime k) N
          _ ≤ (q : NNReal) + 1 := by
              simpa [lowerTime] using add_le_add_right (hq (tailUpper k)) (1 : NNReal)
          _ = ((q + 1 : ℕ) : NNReal) := by simp [Nat.cast_add]
      have hRefine :
          dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N (lowerIndex k) =
            dyadicRightApprox (lowerTime k) N := by
        have hk :
            ((lowerIndex k : ℕ) : NNReal) / (2 : NNReal) ^ N ≤ ((q + 1 : ℕ) : NNReal) := by
          simpa [lowerIndex, dyadicRightApprox] using hUpperBound
        rw [dyadicPointUpTo_eq_div_of_le_cutoff21_24 hk, dyadicRightApprox]
      -- Proof comment: the reversed upper witnesses for the candidate become lower witnesses on
      -- the sign-reversed common row.
      rw [hRefine]
      simpa using neg_lt_neg (hLowerMesh k)
    have hUpperValue :
        ∀ k : Fin (K + 1),
          -((r : ℚ) : ℝ) < -X (dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N (upperIndex k)) ω := by
      intro k
      have hUpperBound :
          dyadicRightApprox (upperTime k) N ≤ ((q + 1 : ℕ) : NNReal) := by
        calc
          dyadicRightApprox (upperTime k) N ≤ upperTime k + 1 :=
            dyadicRightApprox_le_self_add_one (upperTime k) N
          _ ≤ (q : NNReal) + 1 := by
              simpa [upperTime] using add_le_add_right (hq (tailLower k)) (1 : NNReal)
          _ = ((q + 1 : ℕ) : NNReal) := by simp [Nat.cast_add]
      have hRefine :
          dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N (upperIndex k) =
            dyadicRightApprox (upperTime k) N := by
        have hk :
            ((upperIndex k : ℕ) : NNReal) / (2 : NNReal) ^ N ≤ ((q + 1 : ℕ) : NNReal) := by
          simpa [upperIndex, dyadicRightApprox] using hUpperBound
        rw [dyadicPointUpTo_eq_div_of_le_cutoff21_24 hk, dyadicRightApprox]
      -- Proof comment: the reversed lower witnesses become upper witnesses on the same row of
      -- `-X`.
      rw [hRefine]
      simpa using neg_lt_neg (hUpperMesh k)
    have hLowerLeUpper :
        ∀ k : Fin (K + 1), lowerIndex k ≤ upperIndex k := by
      intro k
      have hChron :
          tailLower k ≤ tailUpper k :=
        MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ
          (a := (a : ℝ))
          (b := (b : ℝ))
          (f := f)
          (N := M)
          (n := K - (k : ℕ))
          (ω := ω)
      -- Proof comment: after reversing the witness prefix, the antitone time change turns the
      -- candidate chronology into increasing common-row indices.
      change
        Nat.ceil (((lowerTime k : NNReal) : ℝ) * (2 : ℝ) ^ N) ≤
          Nat.ceil (((upperTime k : NNReal) : ℝ) * (2 : ℝ) ^ N)
      exact commonMeshIndex_mono21_24 (N := N) (hτanti hChron)
    have hUpperLeNextLower :
        ∀ j : ℕ, ∀ hj : j < K,
          upperIndex ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
            lowerIndex ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ := by
      intro j hj
      have hsub :
          K - (j + 1) + 1 = K - j := by
        omega
      have hChron :
          MeasureTheory.upperCrossingTime (a : ℝ) (b : ℝ) f M (K - j) ω ≤
            MeasureTheory.lowerCrossingTime (a : ℝ) (b : ℝ) f M (K - j) ω :=
        MeasureTheory.upperCrossingTime_le_lowerCrossingTime
          (a := (a : ℝ))
          (b := (b : ℝ))
          (f := f)
          (N := M)
          (n := K - j)
          (ω := ω)
      have hTime :
          upperTime ⟨j, Nat.lt_succ_of_lt hj⟩ ≤
            lowerTime ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ := by
        simpa [upperTime, lowerTime, tailLower, tailUpper, hsub] using hτanti hChron
      -- Proof comment: adjacent reversed pairs are ordered because the previous upper crossing is
      -- still before the next lower crossing before applying the antitone time change.
      change
        Nat.ceil ((((upperTime ⟨j, Nat.lt_succ_of_lt hj⟩ : NNReal) : ℝ) * (2 : ℝ) ^ N)) ≤
          Nat.ceil
            ((((lowerTime ⟨j + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hj)⟩ : NNReal) : ℝ) *
              (2 : ℝ) ^ N))
      exact commonMeshIndex_mono21_24 (N := N) hTime
    have hRow :
        K <
          upcrossingsBefore
            (-((s : ℚ) : ℝ))
            (-((r : ℚ) : ℝ))
            (fun k ω ↦ -X (dyadicPointUpTo ((q + 1 : ℕ) : NNReal) N k) ω)
            (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1)
            ω := by
      simpa using
        (commonRowWitnessPrefix_lt_rowUpcrossingsBefore21_24
          (X := X)
          (q := ((q + 1 : ℕ) : NNReal))
          (N := N)
          (K := K)
          (ω := ω)
          (a := r)
          (b := s)
          hrs
          lowerIndex
          upperIndex
          hLowerValue
          hUpperValue
          hLowerLeUpper
          hUpperLeNextLower)
    exact (not_le_of_gt hRow) (by simpa using hK N (upperIndex ⟨K, Nat.lt_succ_self K⟩ + 1))

/-- Helper for Theorem 21.24: every bounded ordered sampling of the packaged candidate converges on
the control event. -/
private lemma tendsto_candidate_of_boundedOrderedSeq21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    (τ : ℕ → NNReal)
    (hτbdd : ∃ q : ℕ, ∀ n : ℕ, τ n ≤ q)
    (hτord : Monotone τ ∨ Antitone τ) :
    ∃ c, Tendsto (fun n ↦ dyadicControlCandidate X A (τ n) ω) atTop (𝓝 c) := by
  rcases hτord with hτmono | hτanti
  · have hLiminf :
        liminf (fun n ↦ (‖-dyadicControlCandidate X A (τ n) ω‖₊ : ℝ≥0∞)) atTop < ∞ := by
      simpa using
        candidateNormLiminf_lt_top_of_boundedSeq_of_memDyadicControlEvent21_24
          (X := X)
          hAcontrol
          hω
          τ
          hτbdd
    obtain ⟨c, hc⟩ :=
      MeasureTheory.tendsto_of_uncrossing_lt_top
        (f := fun n ω ↦ -dyadicControlCandidate X A (τ n) ω)
        (ω := ω)
        hLiminf
        (fun a b hab ↦
          monotoneNegCandidateUpcrossings_lt_top_of_memDyadicControlEvent21_24
            (X := X)
            (A := A)
            hAcontrol
            hω
            hτmono
            hτbdd
            hab)
    -- Proof comment: convergence of the negated sampled candidate is equivalent to convergence of
    -- the original sampled candidate.
    refine ⟨-c, ?_⟩
    simpa using hc.neg
  · have hLiminf :
        liminf (fun n ↦ (‖dyadicControlCandidate X A (τ n) ω‖₊ : ℝ≥0∞)) atTop < ∞ :=
      candidateNormLiminf_lt_top_of_boundedSeq_of_memDyadicControlEvent21_24
        (X := X)
        hAcontrol
        hω
        τ
        hτbdd
    exact
      MeasureTheory.tendsto_of_uncrossing_lt_top
        (f := fun n ω ↦ dyadicControlCandidate X A (τ n) ω)
        (ω := ω)
        hLiminf
        (fun a b hab ↦
          antitoneCandidateUpcrossings_lt_top_of_memDyadicControlEvent21_24
            (X := X)
            (A := A)
            hAcontrol
            hω
            hτanti
            hτbdd
            hab)

/-- Helper for Theorem 21.24: the deterministic reciprocal-mesh right approximants converge back
to their base time. -/
private lemma tendsto_rightApproxTime21_24
    (t : NNReal) :
    Tendsto (rightApproxTime t) atTop (𝓝 t) := by
  refine (NNReal.tendsto_coe).mp ?_
  -- Proof comment: after coercing to `ℝ`, this is the standard limit `t + (n + 1)⁻¹ → t`.
  simpa [rightApproxTime, Nat.cast_add, Nat.cast_one] using
    (tendsto_const_nhds.add <|
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1))

/-- Helper for Theorem 21.24: the reciprocal-mesh right approximants move monotonically down
towards their base time. -/
private lemma rightApproxTime_antitone21_24
    (t : NNReal) :
    Antitone (rightApproxTime t) := by
  intro m n hmn
  -- Proof comment: increasing the mesh index only decreases the reciprocal increment.
  have hcast :
      ((rightApproxTime t n : NNReal) : ℝ) ≤ ((rightApproxTime t m : NNReal) : ℝ) := by
    change (t : ℝ) + (((n + 1 : ℕ) : ℝ)⁻¹) ≤ (t : ℝ) + (((m + 1 : ℕ) : ℝ)⁻¹)
    have hmnR : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hmn
    have hdiv :
        1 / (((n + 1 : ℕ) : ℝ) : ℝ) ≤ 1 / (((m + 1 : ℕ) : ℝ) : ℝ) := by
      exact
        one_div_le_one_div_of_le
          (by positivity : (0 : ℝ) < ((m + 1 : ℕ) : ℝ))
          hmnR
    simpa [one_div] using add_le_add_left hdiv (t : ℝ)
  exact_mod_cast hcast

/-- Helper for Theorem 21.24: a bad set frequent on the right of `t` yields an antitone bad
sequence interleaved with a strictly decreasing reciprocal-mesh anchor above `t`. -/
private lemma existsAntitoneRightBadSeq_ofFrequently21_24
    {S : Set NNReal} {t : NNReal}
    (hS : ∃ᶠ s in 𝓝[>] t, s ∈ S) :
    ∃ N : ℕ → ℕ, ∃ τ : ℕ → NNReal,
      StrictMono N ∧
        Antitone τ ∧
        (∀ n : ℕ, τ n ∈ S ∩ Set.Ioc t (rightApproxTime t (N n))) ∧
        ∀ n : ℕ, rightApproxTime t (N (n + 1)) < τ n := by
  classical
  have hBase :
      ∃ s : NNReal, s ∈ S ∩ Set.Ioc t (rightApproxTime t 0) := by
    -- Proof comment: the initial bad point is chosen in the first deterministic right
    -- neighborhood of `t`.
    rcases (hS.and_eventually (Ioc_mem_nhdsGT (lt_rightApproxTime t 0))).exists with
      ⟨s, hsS, hsI⟩
    exact ⟨s, ⟨hsS, hsI⟩⟩
  have hStep :
      ∀ p : ℕ × NNReal,
        p.2 ∈ S ∩ Set.Ioc t (rightApproxTime t p.1) →
          ∃ q : ℕ × NNReal,
            p.1 < q.1 ∧
              q.2 ∈ S ∩ Set.Ioc t (rightApproxTime t q.1) ∧
              rightApproxTime t q.1 < p.2 := by
    intro p hp
    have hpgt : t < p.2 := hp.2.1
    have hClose :
        ∀ᶠ m : ℕ in atTop, rightApproxTime t m < p.2 :=
      (tendsto_order.1 (tendsto_rightApproxTime21_24 t)).2 _ hpgt
    rw [Filter.eventually_atTop] at hClose
    rcases hClose with ⟨M, hM⟩
    let m : ℕ := max (p.1 + 1) M
    have hpm : p.1 < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    have hmClose : rightApproxTime t m < p.2 := hM m (le_max_right _ _)
    -- Proof comment: once the next anchor sits strictly below the current bad point, frequency of
    -- `S` on the right gives a new bad point below that old ceiling.
    rcases (hS.and_eventually (Ioc_mem_nhdsGT (lt_rightApproxTime t m))).exists with
      ⟨s, hsS, hsI⟩
    exact ⟨(m, s), hpm, ⟨hsS, hsI⟩, hmClose⟩
  let data : ℕ → {p : ℕ × NNReal // p.2 ∈ S ∩ Set.Ioc t (rightApproxTime t p.1)} :=
    Nat.rec
      ⟨(0, Classical.choose hBase), by
        simpa using (Classical.choose_spec hBase)⟩
      (fun _ prev =>
        let q := Classical.choose (hStep prev.1 prev.2)
        ⟨q, (Classical.choose_spec (hStep prev.1 prev.2)).2.1⟩)
  have hDataStep :
      ∀ n : ℕ, (data n).1.1 < (data (n + 1)).1.1 := by
    intro n
    simpa [data] using (Classical.choose_spec (hStep (data n).1 (data n).2)).1
  have hDataInterleave :
      ∀ n : ℕ, rightApproxTime t (data (n + 1)).1.1 < (data n).1.2 := by
    intro n
    simpa [data] using (Classical.choose_spec (hStep (data n).1 (data n).2)).2.2
  refine
    ⟨fun n ↦ (data n).1.1, fun n ↦ (data n).1.2,
      strictMono_nat_of_lt_succ hDataStep, ?_, ?_, ?_⟩
  · refine antitone_nat_of_succ_le fun n ↦ ?_
    exact ((data (n + 1)).2.2.2).trans (hDataInterleave n).le
  · intro n
    simpa using (data n).2
  · intro n
    simpa using hDataInterleave n

/-- Helper for Theorem 21.24: a bad set frequent on the left of a positive time yields a monotone
bad sequence interleaved with the canonical dyadic-left anchor. -/
private lemma existsMonotoneLeftBadSeq_ofFrequently21_24
    {t : Set.Ioi (0 : NNReal)} {S : Set NNReal}
    (hS : ∃ᶠ s in 𝓝[<] (t : NNReal), s ∈ S) :
    ∃ N : ℕ → ℕ, ∃ τ : ℕ → NNReal,
      StrictMono N ∧
        Monotone τ ∧
        (∀ n : ℕ, τ n ∈ S ∩ Set.Ioc (dyadicLeftApprox t (N n)) (t : NNReal)) ∧
        ∀ n : ℕ, τ n < dyadicLeftApprox t (N (n + 1)) := by
  classical
  have hBase :
      ∃ s : NNReal, s ∈ S ∩ Set.Ioo (dyadicLeftApprox t 0) (t : NNReal) := by
    -- Proof comment: the initial left bad point is chosen in the first dyadic predecessor
    -- neighborhood of `t`.
    rcases
        (hS.and_eventually (Ioo_mem_nhdsLT (dyadicLeftApprox_lt_self21_24 t 0))).exists with
      ⟨s, hsS, hsI⟩
    exact ⟨s, ⟨hsS, hsI⟩⟩
  have hStep :
      ∀ p : ℕ × NNReal,
        p.2 ∈ S ∩ Set.Ioo (dyadicLeftApprox t p.1) (t : NNReal) →
          ∃ q : ℕ × NNReal,
            p.1 < q.1 ∧
              q.2 ∈ S ∩ Set.Ioo (dyadicLeftApprox t q.1) (t : NNReal) ∧
              p.2 < dyadicLeftApprox t q.1 := by
    intro p hp
    have hplt : p.2 < (t : NNReal) := hp.2.2
    have hRaise :
        ∀ᶠ m : ℕ in atTop, p.2 < dyadicLeftApprox t m := by
      have hNhds : Set.Ioi p.2 ∈ 𝓝[<] (t : NNReal) :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hplt)
      exact (tendsto_dyadicLeftApprox21_24 t) hNhds
    rw [Filter.eventually_atTop] at hRaise
    rcases hRaise with ⟨M, hM⟩
    let m : ℕ := max (p.1 + 1) M
    have hpm : p.1 < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    have hmRaise : p.2 < dyadicLeftApprox t m := hM m (le_max_right _ _)
    -- Proof comment: once the next dyadic-left anchor sits strictly above the current bad point,
    -- frequency of `S` on the left produces the next bad sample beyond that anchor.
    rcases
        (hS.and_eventually (Ioo_mem_nhdsLT (dyadicLeftApprox_lt_self21_24 t m))).exists with
      ⟨s, hsS, hsI⟩
    exact ⟨(m, s), hpm, ⟨hsS, hsI⟩, hmRaise⟩
  let data : ℕ → {p : ℕ × NNReal // p.2 ∈ S ∩ Set.Ioo (dyadicLeftApprox t p.1) (t : NNReal)} :=
    Nat.rec
      ⟨(0, Classical.choose hBase), by
        simpa using (Classical.choose_spec hBase)⟩
      (fun _ prev =>
        let q := Classical.choose (hStep prev.1 prev.2)
        ⟨q, (Classical.choose_spec (hStep prev.1 prev.2)).2.1⟩)
  have hDataStep :
      ∀ n : ℕ, (data n).1.1 < (data (n + 1)).1.1 := by
    intro n
    simpa [data] using (Classical.choose_spec (hStep (data n).1 (data n).2)).1
  have hDataInterleave :
      ∀ n : ℕ, (data n).1.2 < dyadicLeftApprox t (data (n + 1)).1.1 := by
    intro n
    simpa [data] using (Classical.choose_spec (hStep (data n).1 (data n).2)).2.2
  refine
    ⟨fun n ↦ (data n).1.1, fun n ↦ (data n).1.2,
      strictMono_nat_of_lt_succ hDataStep, ?_, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun n ↦ ?_
    exact (hDataInterleave n).le.trans (data (n + 1)).2.2.1.le
  · intro n
    exact ⟨(data n).2.1, ⟨(data n).2.2.1, (data n).2.2.2.le⟩⟩
  · intro n
    simpa using hDataInterleave n

/-- Helper for Theorem 21.24: the standard parity interleaving recovers its even and odd source
sequences without any ad hoc `Nat.div` normalization in the main proof. -/
private lemma interleaveParity_apply_even_odd21_24
    {γ : Type*} (α β : ℕ → γ) (n : ℕ) :
    let σ : ℕ → γ := fun k ↦ if Even k then α (k / 2) else β (k / 2)
    σ (2 * n) = α n ∧ σ (2 * n + 1) = β n := by
  -- Proof comment: `2 * n` is even and `2 * n + 1` is odd, while integer division by `2`
  -- recovers the original index in both cases.
  dsimp
  constructor
  · simp
  · have hdiv : (2 * n + 1) / 2 = n := by omega
    simp [hdiv]

/-- Helper for Theorem 21.24: if a path `f` has a strict left limit at `t` and right limits at
every earlier time, then the right-limit regularization `Function.rightLim f` tends to the same
strict left limit at `t`. -/
private lemma tendsto_rightLim_left_of_leftLimit21_24
    (f : NNReal → ℝ)
    (hRight : ∀ t : NNReal, ∃ c, Tendsto f (𝓝[>] t) (𝓝 c))
    {t : NNReal} (ht : 0 < t)
    (hLeft : ∃ c, Tendsto f (𝓝[<] t) (𝓝 c)) :
    Tendsto (Function.rightLim f) (𝓝[<] t) (𝓝 (Function.leftLim f t)) := by
  have hLeftLim : Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)) :=
    tendsto_leftLim_of_tendsto hLeft
  -- Proof comment: refine the strict-left convergence of `f` to one open interval and then use
  -- the right-limit owner at each interior point to transport that interval control to
  -- `Function.rightLim f`.
  apply (closed_nhds_basis (Function.leftLim f t)).tendsto_right_iff.2
  rintro s ⟨hsMem, hsClosed⟩
  obtain ⟨b, hbne⟩ : (Set.Iio t).Nonempty := by
    refine ⟨t / 2, show t / 2 < t from half_lt_self ht⟩
  obtain ⟨u, hu, hsub⟩ : ∃ u, u < t ∧ Set.Ioo u t ⊆ {x | f x ∈ s} := by
    have hs :=
      (closed_nhds_basis (Function.leftLim f t)).tendsto_right_iff.1 hLeftLim s ⟨hsMem, hsClosed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hbne).1 hs
  filter_upwards [Ioo_mem_nhdsLT hu] with c hc
  obtain ⟨y, hy⟩ := hRight c
  apply hsClosed.mem_of_tendsto (tendsto_rightLim_of_tendsto ⟨y, hy⟩)
  filter_upwards [Ioo_mem_nhdsGT_of_mem ⟨hc.1.le, hc.2⟩] with d hd using hsub hd

/-- Helper for Theorem 21.24: once a path has right limits at every time and strict left limits at
every positive time, its right-limit regularization is càdlàg. -/
private lemma isCadlag_rightLim_of_oneSidedLimits21_24
    (f : NNReal → ℝ)
    (hRight : ∀ t : NNReal, ∃ c, Tendsto f (𝓝[>] t) (𝓝 c))
    (hLeft : ∀ t : Set.Ioi (0 : NNReal), ∃ c, Tendsto f (𝓝[<] (t : NNReal)) (𝓝 c)) :
    IsCadlag (Function.rightLim f) := by
  refine ⟨?_, ?_⟩
  · intro t
    -- Proof comment: a right limit of `f` at `t` makes `Function.rightLim f` right continuous at
    -- the same point by the standard `rightLim` continuity theorem.
    exact continuousWithinAt_rightLim_Ici (tendsto_rightLim_of_tendsto (hRight t))
  · intro t
    have hTendsto :
        Tendsto (Function.rightLim f) (𝓝[<] (t : NNReal))
          (𝓝 (Function.leftLim f (t : NNReal))) :=
      tendsto_rightLim_left_of_leftLimit21_24 f hRight t.2 (hLeft t)
    have hne : (Set.Iio (t : NNReal)).Nonempty :=
      ⟨(t : NNReal) / 2, show (t : NNReal) / 2 < (t : NNReal) from half_lt_self t.2⟩
    have hNeBot : (𝓝[<] (t : NNReal)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot]
      simp [closure_Iio' hne]
    have hEq :
        Function.leftLim (Function.rightLim f) (t : NNReal) =
          Function.leftLim f (t : NNReal) := by
      exact leftLim_eq_of_tendsto (neBot_iff.mp hNeBot) hTendsto
    -- Proof comment: identify the strict left limit of the regularized path with the left limit
    -- of the original path, then reuse the transported convergence.
    simpa [hEq] using hTendsto

/-- Helper for Theorem 21.24: if the raw sample path has the candidate as its actual right limit at
every time, then the packaged candidate path agrees pointwise with the `rightLim`
regularization of the raw path. -/
private lemma dyadicControlCandidate_eq_rightLim_of_rightTendsto21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    {ω : Ω} (hω : ω ∈ A)
    (hRight :
      ∀ t : NNReal,
        Tendsto
          (fun s : NNReal ↦ X s ω)
          (𝓝[>] t)
          (𝓝 (dyadicControlCandidate X A t ω))) :
    (fun t ↦ dyadicControlCandidate X A t ω) =
      Function.rightLim (fun s : NNReal ↦ X s ω) := by
  -- Proof comment: identify each candidate value with the actual right limit of the raw path and
  -- then assemble those pointwise identities into a pathwise equality.
  funext t
  exact
    (rightLim_eq_of_tendsto
      (show (𝓝[>] t) ≠ ⊥ from (show (𝓝[>] t).NeBot from inferInstance).ne)
      (hRight t)).symm

/-- Helper for Theorem 21.24: once the packaged candidate path has the required one-sided limits,
it is càdlàg on that sample point. -/
private lemma isCadlag_dyadicControlCandidate_of_oneSidedLimits21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    {ω : Ω}
    (hRight :
      ∀ t : NNReal,
        Tendsto
          (fun s : NNReal ↦ dyadicControlCandidate X A s ω)
          (𝓝[>] t)
          (𝓝 (dyadicControlCandidate X A t ω)))
    (hLeft :
      ∀ t : Set.Ioi (0 : NNReal),
        ∃ c,
          Tendsto
            (fun s : NNReal ↦ dyadicControlCandidate X A s ω)
            (𝓝[<] (t : NNReal))
            (𝓝 c)) :
    IsCadlag (fun t ↦ dyadicControlCandidate X A t ω) := by
  refine ⟨?_, ?_⟩
  · intro t
    -- Proof comment: the right branch already gives right continuity on `(t, ∞)`, and the
    -- standard order-topology equivalence upgrades it to continuity on `[t, ∞)`.
    exact
      (continuousWithinAt_Ioi_iff_Ici).1
        (show ContinuousWithinAt (fun s : NNReal ↦ dyadicControlCandidate X A s ω)
            (Set.Ioi t) t from hRight t)
  · intro t
    rcases hLeft t with ⟨c, hc⟩
    -- Proof comment: once the strict left limit exists, `Function.leftLim` records exactly that
    -- limit value.
    simpa using
      (tendsto_leftLim_of_tendsto
        (f := fun s : NNReal ↦ dyadicControlCandidate X A s ω)
        ⟨c, hc⟩)

/-- Helper for Theorem 21.24: on the dyadic control event, the packaged candidate path has the
one-sided limits needed for the direct càdlàg wrapper. -/
private lemma exists_leftLimit_dyadicControlCandidate_of_memDyadicControlEvent21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    (t : Set.Ioi (0 : NNReal)) :
    ∃ c,
      Tendsto
        (fun s : NNReal ↦ dyadicControlCandidate X A s ω)
        (𝓝[<] (t : NNReal))
        (𝓝 c) := by
  let f : NNReal → ℝ := fun s ↦ dyadicControlCandidate X A s ω
  have hAnchorMono : Monotone (dyadicLeftApprox t) := by
    -- Proof comment: the exact left-dyadic predecessors move monotonically upward to `t`.
    exact monotone_nat_of_le_succ (dyadicLeftApprox_le_succ21_24 t)
  have htCeil : (t : NNReal) ≤ (Nat.ceil (t : ℝ) : NNReal) := by
    exact_mod_cast Nat.le_ceil (t : ℝ)
  have hAnchorBdd : ∃ q : ℕ, ∀ n : ℕ, dyadicLeftApprox t n ≤ q := by
    refine ⟨Nat.ceil (t : ℝ), ?_⟩
    intro n
    exact (dyadicLeftApprox_lt_self21_24 t n).le.trans htCeil
  obtain ⟨c, hc⟩ :=
    tendsto_candidate_of_boundedOrderedSeq21_24
      (X := X)
      (A := A)
      hAcontrol
      hω
      (dyadicLeftApprox t)
      hAnchorBdd
      (Or.inl hAnchorMono)
  have hBadSeqTendsto :
      ∀ {N : ℕ → ℕ} {τ : ℕ → NNReal},
        StrictMono N →
          (∀ n : ℕ, τ n ∈ Set.Ioc (dyadicLeftApprox t (N n)) (t : NNReal)) →
          (∀ n : ℕ, τ n < dyadicLeftApprox t (N (n + 1))) →
          Tendsto (fun n ↦ f (τ n)) atTop (𝓝 c) := by
    intro N τ hN hτmem hτgap
    let β : ℕ → NNReal := fun n ↦ dyadicLeftApprox t (N (n + 1))
    let σ : ℕ → NNReal := fun k ↦ if Even k then τ (k / 2) else β (k / 2)
    have hσeven : ∀ n : ℕ, σ (2 * n) = τ n := by
      intro n
      exact (interleaveParity_apply_even_odd21_24 τ β n).1
    have hσodd : ∀ n : ℕ, σ (2 * n + 1) = β n := by
      intro n
      exact (interleaveParity_apply_even_odd21_24 τ β n).2
    have hσmono : Monotone σ := by
      refine monotone_nat_of_le_succ ?_
      intro n
      rcases Nat.even_or_odd n with hEven | hOdd
      · rcases hEven with ⟨m, rfl⟩
        calc
          σ (m + m) = τ m := by simpa [two_mul] using hσeven m
          _ ≤ β m := (hτgap m).le
          _ = σ (m + m + 1) := by simpa [two_mul] using (hσodd m).symm
      · rcases hOdd with ⟨m, rfl⟩
        calc
          σ (2 * m + 1) = β m := by
            simpa using hσodd m
          _ ≤ τ (m + 1) := (hτmem (m + 1)).1.le
          _ = σ (2 * m + 1 + 1) := by
            simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (hσeven (m + 1)).symm
    have hσbdd : ∃ q : ℕ, ∀ n : ℕ, σ n ≤ q := by
      refine ⟨Nat.ceil (t : ℝ), ?_⟩
      intro n
      rcases Nat.even_or_odd n with hEven | hOdd
      · rcases hEven with ⟨m, rfl⟩
        calc
          σ (m + m) = τ m := by simpa [two_mul] using hσeven m
          _ ≤ (Nat.ceil (t : ℝ) : NNReal) := ((hτmem m).2).trans htCeil
      · rcases hOdd with ⟨m, rfl⟩
        calc
          σ (2 * m + 1) = β m := by
            simpa using hσodd m
          _ ≤ (Nat.ceil (t : ℝ) : NNReal) := by
            exact (dyadicLeftApprox_lt_self21_24 t (N (m + 1))).le.trans htCeil
    obtain ⟨d, hd⟩ :=
      tendsto_candidate_of_boundedOrderedSeq21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
        σ
        hσbdd
        (Or.inl hσmono)
    have hEvenMono : StrictMono (fun n : ℕ ↦ 2 * n) := by
      intro m n hmn
      exact Nat.mul_lt_mul_of_pos_left hmn (by decide : 0 < 2)
    have hOddMono : StrictMono (fun n : ℕ ↦ 2 * n + 1) := by
      intro m n hmn
      exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hmn (by decide : 0 < 2)) 1
    have hNSuccMono : StrictMono (fun n : ℕ ↦ N (n + 1)) := by
      intro m n hmn
      exact hN (Nat.succ_lt_succ hmn)
    have hBetaTendstoD :
        Tendsto (fun n ↦ f (β n)) atTop (𝓝 d) := by
    -- Proof comment: the odd subsequence of the mixed ordered sampling is exactly the anchor
    -- subsequence `β`.
      convert hd.comp (StrictMono.tendsto_atTop hOddMono) using 1
      funext n
      simp [Function.comp, f, hσodd n]
    have hBetaTendstoC :
        Tendsto (fun n ↦ f (β n)) atTop (𝓝 c) := by
      -- Proof comment: `β` is just a strict subsequence of the canonical dyadic-left anchor.
      simpa [Function.comp, β] using hc.comp (StrictMono.tendsto_atTop hNSuccMono)
    have hdc : d = c := tendsto_nhds_unique hBetaTendstoD hBetaTendstoC
    have hTauTendstoD :
        Tendsto (fun n ↦ f (τ n)) atTop (𝓝 d) := by
      -- Proof comment: the even subsequence of the mixed ordered sampling is exactly the bad
      -- sequence `τ`.
      convert hd.comp (StrictMono.tendsto_atTop hEvenMono) using 1
      funext n
      simp [Function.comp, f, hσeven n]
    simpa [hdc] using hTauTendstoD
  refine ⟨c, ?_⟩
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    by_contra hLower
    have hFreq :
        ∃ᶠ s in 𝓝[<] (t : NNReal), f s ≤ a := by
      rw [Filter.Frequently]
      simpa [not_le] using hLower
    rcases
        existsMonotoneLeftBadSeq_ofFrequently21_24
          (t := t)
          (S := {s : NNReal | f s ≤ a})
          hFreq with
      ⟨N, τ, hN, _, hτmem, hτgap⟩
    have hTauTendsto :
        Tendsto (fun n ↦ f (τ n)) atTop (𝓝 c) :=
      hBadSeqTendsto hN (fun n ↦ (hτmem n).2) hτgap
    have hEventuallyAbove : ∀ᶠ n : ℕ in atTop, a < f (τ n) :=
      (tendsto_order.1 hTauTendsto).1 _ ha
    have hBoth :
        ∀ᶠ n : ℕ in atTop, a < f (τ n) ∧ f (τ n) ≤ a :=
      hEventuallyAbove.and <| Filter.Eventually.of_forall fun n ↦ (hτmem n).1
    rcases hBoth.exists with ⟨n, hnlt, hnle⟩
    exact (not_le_of_gt hnlt) hnle
  · intro b hb
    by_contra hUpper
    have hFreq :
        ∃ᶠ s in 𝓝[<] (t : NNReal), b ≤ f s := by
      rw [Filter.Frequently]
      simpa [not_le] using hUpper
    rcases
        existsMonotoneLeftBadSeq_ofFrequently21_24
          (t := t)
          (S := {s : NNReal | b ≤ f s})
          hFreq with
      ⟨N, τ, hN, _, hτmem, hτgap⟩
    have hTauTendsto :
        Tendsto (fun n ↦ f (τ n)) atTop (𝓝 c) :=
      hBadSeqTendsto hN (fun n ↦ (hτmem n).2) hτgap
    have hEventuallyBelow : ∀ᶠ n : ℕ in atTop, f (τ n) < b :=
      (tendsto_order.1 hTauTendsto).2 _ hb
    have hBoth :
        ∀ᶠ n : ℕ in atTop, f (τ n) < b ∧ b ≤ f (τ n) :=
      hEventuallyBelow.and <| Filter.Eventually.of_forall fun n ↦ (hτmem n).1
    rcases hBoth.exists with ⟨n, hnlt, hnle⟩
    exact (not_le_of_gt hnlt) hnle

/-- Helper for Theorem 21.24: if `t` is not already fixed by any canonical exact right-dyadic sample, one can choose a strict exact-dyadic subsequence between successive reciprocal-mesh anchors above `t`. -/
private lemma strictDyadicRightSubseq_betweenRightApproxTimes21_24
    (t : NNReal)
    (hNotExact : ¬ ∃ m : ℕ, dyadicRightApprox t m = t) :
    ∃ N M : ℕ → ℕ,
      StrictMono N ∧
        StrictMono M ∧
        (∀ n : ℕ, dyadicRightApprox t (M n) ∈ Set.Ioc t (rightApproxTime t (N n))) ∧
        ∀ n : ℕ, rightApproxTime t (N (n + 1)) < dyadicRightApprox t (M n) := by
  classical
  have hStrict : ∀ m : ℕ, t < dyadicRightApprox t m := by
    intro m
    refine lt_of_le_of_ne (le_dyadicRightApprox t m) ?_
    intro hEq
    exact hNotExact ⟨m, hEq.symm⟩
  have hBase :
      ∃ p : ℕ × ℕ, dyadicRightApprox t p.2 ∈ Set.Ioc t (rightApproxTime t p.1) := by
    have hEventually :
        ∀ᶠ m : ℕ in atTop, dyadicRightApprox t m < rightApproxTime t 0 :=
      tendsto_dyadicRightApprox t (Iio_mem_nhds (lt_rightApproxTime t 0))
    rw [Filter.eventually_atTop] at hEventually
    rcases hEventually with ⟨M0, hM0⟩
    refine ⟨(0, M0), ?_⟩
    exact ⟨hStrict M0, (hM0 M0 le_rfl).le⟩
  have hStep :
      ∀ p : ℕ × ℕ,
        dyadicRightApprox t p.2 ∈ Set.Ioc t (rightApproxTime t p.1) →
          ∃ q : ℕ × ℕ,
            p.1 < q.1 ∧
              p.2 < q.2 ∧
              dyadicRightApprox t q.2 ∈ Set.Ioc t (rightApproxTime t q.1) ∧
              rightApproxTime t q.1 < dyadicRightApprox t p.2 := by
    intro p hp
    have hAnchorEventually :
        ∀ᶠ n : ℕ in atTop, rightApproxTime t n < dyadicRightApprox t p.2 :=
      (tendsto_order.1 (tendsto_rightApproxTime21_24 t)).2 _ hp.1
    rw [Filter.eventually_atTop] at hAnchorEventually
    rcases hAnchorEventually with ⟨N0, hN0⟩
    let N1 : ℕ := max (p.1 + 1) N0
    have hpN1 : p.1 < N1 := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    have hGap :
        rightApproxTime t N1 < dyadicRightApprox t p.2 :=
      hN0 N1 (le_max_right _ _)
    have hDyadicEventually :
        ∀ᶠ m : ℕ in atTop, dyadicRightApprox t m < rightApproxTime t N1 :=
      tendsto_dyadicRightApprox t (Iio_mem_nhds (lt_rightApproxTime t N1))
    rw [Filter.eventually_atTop] at hDyadicEventually
    rcases hDyadicEventually with ⟨M0, hM0⟩
    let M1 : ℕ := max (p.2 + 1) M0
    have hpM1 : p.2 < M1 := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    have hUpper :
        dyadicRightApprox t M1 < rightApproxTime t N1 :=
      hM0 M1 (le_max_right _ _)
    refine ⟨(N1, M1), hpN1, hpM1, ?_, hGap⟩
    exact ⟨hStrict M1, hUpper.le⟩
  let data : ℕ → {p : ℕ × ℕ // dyadicRightApprox t p.2 ∈ Set.Ioc t (rightApproxTime t p.1)} :=
    Nat.rec
      ⟨Classical.choose hBase, Classical.choose_spec hBase⟩
      (fun _ prev =>
        let q := Classical.choose (hStep prev.1 prev.2)
        ⟨q, (Classical.choose_spec (hStep prev.1 prev.2)).2.2.1⟩)
  have hDataNStep : ∀ n : ℕ, (data n).1.1 < (data (n + 1)).1.1 := by
    intro n
    simpa [data] using (Classical.choose_spec (hStep (data n).1 (data n).2)).1
  have hDataMStep : ∀ n : ℕ, (data n).1.2 < (data (n + 1)).1.2 := by
    intro n
    simpa [data] using (Classical.choose_spec (hStep (data n).1 (data n).2)).2.1
  have hDataGap :
      ∀ n : ℕ, rightApproxTime t (data (n + 1)).1.1 < dyadicRightApprox t (data n).1.2 := by
    intro n
    simpa [data] using (Classical.choose_spec (hStep (data n).1 (data n).2)).2.2.2
  refine
    ⟨fun n ↦ (data n).1.1, fun n ↦ (data n).1.2,
      strictMono_nat_of_lt_succ hDataNStep, strictMono_nat_of_lt_succ hDataMStep, ?_, ?_⟩
  · intro n
    simpa using (data n).2
  · intro n
    simpa using hDataGap n

/-- Helper for Theorem 21.24: at an exact dyadic mesh level `m0`, the reciprocal-mesh indices
`2 ^ (m0 + n + 1) - 1` pick out the strict power-of-two successors `t + 2 ^ -(m0 + n + 1)`. -/
private def exactRightApproxTimeMesh21_24 (m0 n : ℕ) : ℕ :=
  2 ^ (m0 + n + 1) - 1

/-- Helper for Theorem 21.24: the exact-mesh strict-right anchor associated to `t` and `m0`. -/
private def exactRightApproxTime21_24 (t : NNReal) (m0 n : ℕ) : NNReal :=
  rightApproxTime t (exactRightApproxTimeMesh21_24 m0 n)

/-- Helper for Theorem 21.24: the power-of-two reciprocal indices form a strict subsequence of the
canonical reciprocal-mesh anchor. -/
private lemma exactRightApproxTimeMesh_strictMono21_24 (m0 : ℕ) :
    StrictMono (exactRightApproxTimeMesh21_24 m0) := by
  intro i j hij
  unfold exactRightApproxTimeMesh21_24
  have hpow :
      2 ^ (m0 + i + 1) < 2 ^ (m0 + j + 1) := by
    exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  have hi_pos : 1 ≤ 2 ^ (m0 + i + 1) := by
    exact Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
  have hj_pos : 1 ≤ 2 ^ (m0 + j + 1) := by
    exact Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
  omega

/-- Helper for Theorem 21.24: the power-of-two reciprocal subsequence stays strictly between
successive reciprocal-mesh anchors. -/
private lemma rightApproxTime_exactRightApproxTimeMesh_gap21_24
    (t : NNReal) (m0 n : ℕ) :
    exactRightApproxTime21_24 t m0 (n + 1) <
      exactRightApproxTime21_24 t m0 n := by
  have hpow :
      ((2 ^ (m0 + n + 1) : ℕ) : NNReal) <
        ((2 ^ (m0 + n + 2) : ℕ) : NNReal) := by
    exact_mod_cast Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  have hInv :
      (((2 ^ (m0 + n + 2) : ℕ) : NNReal)⁻¹) <
        (((2 ^ (m0 + n + 1) : ℕ) : NNReal)⁻¹) := by
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (show (0 : NNReal) < ((2 ^ (m0 + n + 1) : ℕ) : NNReal) by positivity) hpow)
  have hsucc_succ :
      exactRightApproxTimeMesh21_24 m0 (n + 1) + 1 = 2 ^ (m0 + n + 2) := by
    unfold exactRightApproxTimeMesh21_24
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2)))
  have hsucc :
      exactRightApproxTimeMesh21_24 m0 n + 1 = 2 ^ (m0 + n + 1) := by
    unfold exactRightApproxTimeMesh21_24
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2)))
  calc
    exactRightApproxTime21_24 t m0 (n + 1)
        = t + (((2 ^ (m0 + n + 2) : ℕ) : NNReal)⁻¹) := by
            simp [exactRightApproxTime21_24, rightApproxTime, hsucc_succ]
    _ < t + (((2 ^ (m0 + n + 1) : ℕ) : NNReal)⁻¹) := by gcongr
    _ = exactRightApproxTime21_24 t m0 n := by
          simp [exactRightApproxTime21_24, rightApproxTime, hsucc]

/-- Helper for Theorem 21.24: a bad set frequent on the right of `t` yields an antitone bad
sequence interleaved with the strict exact-mesh anchor
`n ↦ rightApproxTime t (exactRightApproxTimeMesh21_24 m0 n)`. -/
private lemma existsAntitoneRightBadSeq_ofFrequently_exactRightApproxTimeMesh21_24
    {S : Set NNReal} {t : NNReal} (m0 : ℕ)
    (hS : ∃ᶠ s in 𝓝[>] t, s ∈ S) :
    ∃ N : ℕ → ℕ, ∃ τ : ℕ → NNReal,
      StrictMono N ∧
        Antitone τ ∧
        (∀ n : ℕ,
          τ n ∈ S ∩ Set.Ioc t (exactRightApproxTime21_24 t m0 (N n))) ∧
        ∀ n : ℕ,
          exactRightApproxTime21_24 t m0 (N (n + 1)) < τ n := by
  classical
  let β : ℕ → NNReal := exactRightApproxTime21_24 t m0
  have hβTendsto : Tendsto β atTop (𝓝 t) := by
    -- Proof comment: the exact-mesh anchor is a strict subsequence of the reciprocal mesh.
    simpa [β] using
      (tendsto_rightApproxTime21_24 t).comp
        (StrictMono.tendsto_atTop (exactRightApproxTimeMesh_strictMono21_24 m0))
  have hBase :
      ∃ s : NNReal, s ∈ S ∩ Set.Ioc t (β 0) := by
    -- Proof comment: choose the initial bad point inside the first exact-mesh right neighborhood.
    have hβ0 : t < β 0 := by
      simpa [β, exactRightApproxTime21_24] using
        lt_rightApproxTime t (exactRightApproxTimeMesh21_24 m0 0)
    rcases (hS.and_eventually (Ioc_mem_nhdsGT hβ0)).exists with
      ⟨s, hsS, hsI⟩
    exact ⟨s, ⟨hsS, hsI⟩⟩
  have hStep :
      ∀ p : ℕ × NNReal,
        p.2 ∈ S ∩ Set.Ioc t (β p.1) →
          ∃ q : ℕ × NNReal,
            p.1 < q.1 ∧
              q.2 ∈ S ∩ Set.Ioc t (β q.1) ∧
              β q.1 < p.2 := by
    intro p hp
    have hpgt : t < p.2 := hp.2.1
    have hClose :
        ∀ᶠ m : ℕ in atTop, β m < p.2 :=
      (tendsto_order.1 hβTendsto).2 _ hpgt
    rw [Filter.eventually_atTop] at hClose
    rcases hClose with ⟨M, hM⟩
    let m : ℕ := max (p.1 + 1) M
    have hpm : p.1 < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    have hmClose : β m < p.2 := hM m (le_max_right _ _)
    -- Proof comment: once the next exact-mesh anchor lies below the current bad point, the
    -- right-frequency of `S` yields the next bad point between them.
    have hβm : t < β m := by
      simpa [β, exactRightApproxTime21_24] using
        lt_rightApproxTime t (exactRightApproxTimeMesh21_24 m0 m)
    rcases (hS.and_eventually (Ioc_mem_nhdsGT hβm)).exists with
      ⟨s, hsS, hsI⟩
    exact ⟨(m, s), hpm, ⟨hsS, hsI⟩, hmClose⟩
  let data : ℕ → {p : ℕ × NNReal // p.2 ∈ S ∩ Set.Ioc t (β p.1)} :=
    Nat.rec
      ⟨(0, Classical.choose hBase), by
        simpa using (Classical.choose_spec hBase)⟩
      (fun _ prev =>
        let q := Classical.choose (hStep prev.1 prev.2)
        ⟨q, (Classical.choose_spec (hStep prev.1 prev.2)).2.1⟩)
  have hDataStep :
      ∀ n : ℕ, (data n).1.1 < (data (n + 1)).1.1 := by
    intro n
    simpa [data] using (Classical.choose_spec (hStep (data n).1 (data n).2)).1
  have hDataInterleave :
      ∀ n : ℕ, β ((data (n + 1)).1.1) < (data n).1.2 := by
    intro n
    simpa [data] using (Classical.choose_spec (hStep (data n).1 (data n).2)).2.2
  refine
    ⟨fun n ↦ (data n).1.1, fun n ↦ (data n).1.2,
      strictMono_nat_of_lt_succ hDataStep, ?_, ?_, ?_⟩
  · refine antitone_nat_of_succ_le fun n ↦ ?_
    exact ((data (n + 1)).2.2.2).trans (hDataInterleave n).le
  · intro n
    simpa [β] using (data n).2
  · intro n
    simpa [β] using hDataInterleave n

/-- Helper for Theorem 21.24: any antitone right-neighborhood sequence squeezed between successive
exact-mesh anchors converges to the same candidate limit as that anchor. -/
private lemma tendsto_candidate_of_exactRightApproxTimeMeshSqueezedSeq21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A) {t : NNReal} {m0 : ℕ} {c : ℝ}
    (hc :
      Tendsto
        (fun n ↦
          dyadicControlCandidate X A (exactRightApproxTime21_24 t m0 n) ω)
        atTop
        (𝓝 c))
    {N : ℕ → ℕ} {τ : ℕ → NNReal}
    (hN : StrictMono N)
    (hτmem :
      ∀ n : ℕ,
        τ n ∈ Set.Ioc t (exactRightApproxTime21_24 t m0 (N n)))
    (hτgap :
      ∀ n : ℕ,
        exactRightApproxTime21_24 t m0 (N (n + 1)) < τ n) :
    Tendsto
      (fun n ↦ dyadicControlCandidate X A (τ n) ω)
      atTop
      (𝓝 c) := by
  let f : NNReal → ℝ := fun s ↦ dyadicControlCandidate X A s ω
  let β : ℕ → NNReal := fun n ↦ exactRightApproxTime21_24 t m0 (N (n + 1))
  let σ : ℕ → NNReal := fun k ↦ if Even k then τ (k / 2) else β (k / 2)
  have hσeven : ∀ n : ℕ, σ (2 * n) = τ n := by
    intro n
    exact (interleaveParity_apply_even_odd21_24 τ β n).1
  have hσodd : ∀ n : ℕ, σ (2 * n + 1) = β n := by
    intro n
    exact (interleaveParity_apply_even_odd21_24 τ β n).2
  have hσanti : Antitone σ := by
    refine antitone_nat_of_succ_le ?_
    intro n
    rcases Nat.even_or_odd n with hEven | hOdd
    · rcases hEven with ⟨m, rfl⟩
      have hOddEq : σ (m + m + 1) = β m := by
        simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hσodd m
      have hEvenEq : σ (m + m) = τ m := by
        simpa [two_mul] using hσeven m
      rw [hOddEq, hEvenEq]
      exact (hτgap m).le
    · rcases hOdd with ⟨m, rfl⟩
      have hSuccEq : σ (2 * m + 1 + 1) = τ (m + 1) := by
        simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hσeven (m + 1)
      have hOddEq : σ (2 * m + 1) = β m := hσodd m
      rw [hSuccEq, hOddEq]
      exact (hτmem (m + 1)).2
  have htCeil :
      t + 1 ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := by
    exact_mod_cast Nat.le_ceil ((t : ℝ) + 1)
  have hσbdd : ∃ q : ℕ, ∀ n : ℕ, σ n ≤ q := by
    refine ⟨Nat.ceil ((t : ℝ) + 1), ?_⟩
    intro n
    rcases Nat.even_or_odd n with hEven | hOdd
    · rcases hEven with ⟨m, rfl⟩
      calc
        σ (m + m) = τ m := by simpa [two_mul] using hσeven m
        _ ≤ exactRightApproxTime21_24 t m0 (N m) := (hτmem m).2
        _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := by
          have hOneLe :
              (1 : NNReal) ≤
                ((exactRightApproxTimeMesh21_24 m0 (N m) + 1 : ℕ) : NNReal) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
          have hInvLe :
              (((exactRightApproxTimeMesh21_24 m0 (N m) + 1 : ℕ) : NNReal)⁻¹) ≤ 1 := by
            simpa using
              one_div_le_one_div_of_le (show (0 : NNReal) < 1 from zero_lt_one) hOneLe
          calc
            exactRightApproxTime21_24 t m0 (N m) =
                t + (((exactRightApproxTimeMesh21_24 m0 (N m) + 1 : ℕ) : NNReal)⁻¹) := by
                  simp [exactRightApproxTime21_24, rightApproxTime]
            _ ≤ t + 1 := by gcongr
            _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := htCeil
    · rcases hOdd with ⟨m, rfl⟩
      calc
        σ (2 * m + 1) = β m := by
          simpa using hσodd m
        _ = exactRightApproxTime21_24 t m0 (N (m + 1)) := by
          simp [β]
        _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := by
          have hOneLe :
              (1 : NNReal) ≤
                ((exactRightApproxTimeMesh21_24 m0 (N (m + 1)) + 1 : ℕ) : NNReal) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
          have hInvLe :
              (((exactRightApproxTimeMesh21_24 m0 (N (m + 1)) + 1 : ℕ) : NNReal)⁻¹) ≤ 1 := by
            simpa using
              one_div_le_one_div_of_le (show (0 : NNReal) < 1 from zero_lt_one) hOneLe
          calc
            exactRightApproxTime21_24 t m0 (N (m + 1)) =
                t + (((exactRightApproxTimeMesh21_24 m0 (N (m + 1)) + 1 : ℕ) : NNReal)⁻¹) := by
                  simp [exactRightApproxTime21_24, rightApproxTime]
            _ ≤ t + 1 := by gcongr
            _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := htCeil
  obtain ⟨d, hd⟩ :=
    tendsto_candidate_of_boundedOrderedSeq21_24
      (X := X)
      (A := A)
      hAcontrol
      hω
      σ
      hσbdd
      (Or.inr hσanti)
  have hEvenMono : StrictMono (fun n : ℕ ↦ 2 * n) := by
    intro m n hmn
    exact Nat.mul_lt_mul_of_pos_left hmn (by decide : 0 < 2)
  have hOddMono : StrictMono (fun n : ℕ ↦ 2 * n + 1) := by
    intro m n hmn
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hmn (by decide : 0 < 2)) 1
  have hNSuccMono : StrictMono (fun n : ℕ ↦ N (n + 1)) := by
    intro m n hmn
    exact hN (Nat.succ_lt_succ hmn)
  have hBetaTendstoD :
      Tendsto (fun n ↦ f (β n)) atTop (𝓝 d) := by
    -- Proof comment: the odd subsequence of the mixed sampling is exactly the shifted exact-mesh
    -- anchor subsequence.
    convert hd.comp (StrictMono.tendsto_atTop hOddMono) using 1
    funext n
    simp [Function.comp, f, hσodd n]
  have hBetaTendstoC :
      Tendsto (fun n ↦ f (β n)) atTop (𝓝 c) := by
    -- Proof comment: `β` is a strict subsequence of the original exact-mesh anchor.
    simpa [Function.comp, β, f] using hc.comp (StrictMono.tendsto_atTop hNSuccMono)
  have hdc : d = c := tendsto_nhds_unique hBetaTendstoD hBetaTendstoC
  have hTauTendstoD :
      Tendsto (fun n ↦ f (τ n)) atTop (𝓝 d) := by
    -- Proof comment: the even subsequence of the mixed sampling is the squeezed bad sequence.
    convert hd.comp (StrictMono.tendsto_atTop hEvenMono) using 1
    funext n
    simp [Function.comp, f, hσeven n]
  simpa [hdc] using hTauTendstoD

/-- Helper for Theorem 21.24: any antitone right-neighborhood sequence squeezed between successive
reciprocal-mesh anchors has the same candidate limit as the anchor itself. -/
private lemma tendsto_candidate_of_rightSqueezedSeq_toAnchorLimit21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A) {t : NNReal} {c : ℝ}
    (hc :
      Tendsto
        (fun n ↦ dyadicControlCandidate X A (rightApproxTime t n) ω)
        atTop
        (𝓝 c))
    {N : ℕ → ℕ} {τ : ℕ → NNReal}
    (hN : StrictMono N)
    (hτmem : ∀ n : ℕ, τ n ∈ Set.Ioc t (rightApproxTime t (N n)))
    (hτgap : ∀ n : ℕ, rightApproxTime t (N (n + 1)) < τ n) :
    Tendsto
      (fun n ↦ dyadicControlCandidate X A (τ n) ω)
      atTop
      (𝓝 c) := by
  let f : NNReal → ℝ := fun s ↦ dyadicControlCandidate X A s ω
  let β : ℕ → NNReal := fun n ↦ rightApproxTime t (N (n + 1))
  let σ : ℕ → NNReal := fun k ↦ if Even k then τ (k / 2) else β (k / 2)
  have hσeven : ∀ n : ℕ, σ (2 * n) = τ n := by
    intro n
    exact (interleaveParity_apply_even_odd21_24 τ β n).1
  have hσodd : ∀ n : ℕ, σ (2 * n + 1) = β n := by
    intro n
    exact (interleaveParity_apply_even_odd21_24 τ β n).2
  have hσanti : Antitone σ := by
    refine antitone_nat_of_succ_le ?_
    intro n
    rcases Nat.even_or_odd n with hEven | hOdd
    · rcases hEven with ⟨m, rfl⟩
      have hOddEq : σ (m + m + 1) = β m := by
        simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hσodd m
      have hEvenEq : σ (m + m) = τ m := by
        simpa [two_mul] using hσeven m
      rw [hOddEq, hEvenEq]
      exact (hτgap m).le
    · rcases hOdd with ⟨m, rfl⟩
      have hSuccEq : σ (2 * m + 1 + 1) = τ (m + 1) := by
        simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hσeven (m + 1)
      have hOddEq : σ (2 * m + 1) = β m := hσodd m
      rw [hSuccEq, hOddEq]
      exact (hτmem (m + 1)).2
  have htCeil :
      t + 1 ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := by
    exact_mod_cast Nat.le_ceil ((t : ℝ) + 1)
  have hσbdd : ∃ q : ℕ, ∀ n : ℕ, σ n ≤ q := by
    refine ⟨Nat.ceil ((t : ℝ) + 1), ?_⟩
    intro n
    rcases Nat.even_or_odd n with hEven | hOdd
    · rcases hEven with ⟨m, rfl⟩
      calc
        σ (m + m) = τ m := by simpa [two_mul] using hσeven m
        _ ≤ rightApproxTime t (N m) := (hτmem m).2
        _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := by
            have hOneLe : (1 : NNReal) ≤ ((N m + 1 : ℕ) : NNReal) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le (N m))
            have hInvLe :
                (((N m + 1 : ℕ) : NNReal)⁻¹) ≤ 1 := by
              simpa using
                one_div_le_one_div_of_le (show (0 : NNReal) < 1 from zero_lt_one) hOneLe
            calc
              rightApproxTime t (N m) = t + (((N m + 1 : ℕ) : NNReal)⁻¹) := by
                simp [rightApproxTime]
              _ ≤ t + 1 := by gcongr
              _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := htCeil
    · rcases hOdd with ⟨m, rfl⟩
      calc
        σ (2 * m + 1) = β m := by
          simpa using hσodd m
        _ = rightApproxTime t (N (m + 1)) := by
          simp [β]
        _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := by
            have hOneLe : (1 : NNReal) ≤ ((N (m + 1) + 1 : ℕ) : NNReal) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le (N (m + 1)))
            have hInvLe :
                (((N (m + 1) + 1 : ℕ) : NNReal)⁻¹) ≤ 1 := by
              simpa using
                one_div_le_one_div_of_le (show (0 : NNReal) < 1 from zero_lt_one) hOneLe
            calc
              rightApproxTime t (N (m + 1)) = t + (((N (m + 1) + 1 : ℕ) : NNReal)⁻¹) := by
                simp [rightApproxTime]
              _ ≤ t + 1 := by gcongr
              _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := htCeil
  obtain ⟨d, hd⟩ :=
    tendsto_candidate_of_boundedOrderedSeq21_24
      (X := X)
      (A := A)
      hAcontrol
      hω
      σ
      hσbdd
      (Or.inr hσanti)
  have hEvenMono : StrictMono (fun n : ℕ ↦ 2 * n) := by
    intro m n hmn
    exact Nat.mul_lt_mul_of_pos_left hmn (by decide : 0 < 2)
  have hOddMono : StrictMono (fun n : ℕ ↦ 2 * n + 1) := by
    intro m n hmn
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hmn (by decide : 0 < 2)) 1
  have hNSuccMono : StrictMono (fun n : ℕ ↦ N (n + 1)) := by
    intro m n hmn
    exact hN (Nat.succ_lt_succ hmn)
  have hBetaTendstoD :
      Tendsto (fun n ↦ f (β n)) atTop (𝓝 d) := by
    -- Proof comment: the odd subsequence of the mixed sampling is exactly the anchor subsequence.
    convert hd.comp (StrictMono.tendsto_atTop hOddMono) using 1
    funext n
    simp [Function.comp, f, hσodd n]
  have hBetaTendstoC :
      Tendsto (fun n ↦ f (β n)) atTop (𝓝 c) := by
    -- Proof comment: `β` is the shifted subsequence of the original reciprocal-mesh anchor.
    simpa [Function.comp, β, f] using hc.comp (StrictMono.tendsto_atTop hNSuccMono)
  have hdc : d = c := tendsto_nhds_unique hBetaTendstoD hBetaTendstoC
  have hTauTendstoD :
      Tendsto (fun n ↦ f (τ n)) atTop (𝓝 d) := by
    -- Proof comment: the even subsequence of the mixed sampling is exactly the squeezed sequence.
    convert hd.comp (StrictMono.tendsto_atTop hEvenMono) using 1
    funext n
    simp [Function.comp, f, hσeven n]
  simpa [hdc] using hTauTendstoD

/-- Helper for Theorem 21.24: on the dyadic control event, the packaged candidate has a strict
right limit at every time. -/
private lemma exists_rightLimit_dyadicControlCandidate_of_memDyadicControlEvent21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    {ω : Ω} (hω : ω ∈ A)
    (t : NNReal) :
    ∃ c,
      Tendsto
        (fun s : NNReal ↦ dyadicControlCandidate X A s ω)
        (𝓝[>] t)
        (𝓝 c) := by
  let f : NNReal → ℝ := fun s ↦ dyadicControlCandidate X A s ω
  by_cases hExact : ∃ m : ℕ, dyadicRightApprox t m = t
  · obtain ⟨m0, hm0⟩ := hExact
    have hAnchorAnti : Antitone (exactRightApproxTime21_24 t m0) := by
      refine antitone_nat_of_succ_le ?_
      intro n
      exact (rightApproxTime_exactRightApproxTimeMesh_gap21_24 t m0 n).le
    have htCeil :
        t + 1 ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := by
      exact_mod_cast Nat.le_ceil ((t : ℝ) + 1)
    have hAnchorBdd : ∃ q : ℕ, ∀ n : ℕ, exactRightApproxTime21_24 t m0 n ≤ q := by
      refine ⟨Nat.ceil ((t : ℝ) + 1), ?_⟩
      intro n
      have hOneLe :
          (1 : NNReal) ≤
            ((exactRightApproxTimeMesh21_24 m0 n + 1 : ℕ) : NNReal) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
      have hInvLe :
          (((exactRightApproxTimeMesh21_24 m0 n + 1 : ℕ) : NNReal)⁻¹) ≤ 1 := by
        simpa using
          one_div_le_one_div_of_le (show (0 : NNReal) < 1 from zero_lt_one) hOneLe
      calc
        exactRightApproxTime21_24 t m0 n =
            t + (((exactRightApproxTimeMesh21_24 m0 n + 1 : ℕ) : NNReal)⁻¹) := by
              simp [exactRightApproxTime21_24, rightApproxTime]
        _ ≤ t + 1 := by gcongr
        _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := htCeil
    obtain ⟨c, hc⟩ :=
      tendsto_candidate_of_boundedOrderedSeq21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
        (exactRightApproxTime21_24 t m0)
        hAnchorBdd
        (Or.inr hAnchorAnti)
    refine ⟨c, ?_⟩
    refine tendsto_order.2 ?_
    constructor
    · intro a ha
      by_contra hLower
      have hFreq :
          ∃ᶠ s in 𝓝[>] t, f s ≤ a := by
        rw [Filter.Frequently]
        simpa [not_le] using hLower
      rcases
          existsAntitoneRightBadSeq_ofFrequently_exactRightApproxTimeMesh21_24
            (t := t)
            (S := {s : NNReal | f s ≤ a})
            m0
            hFreq with
        ⟨N, τ, hN, _, hτmem, hτgap⟩
      have hTauTendsto :
          Tendsto (fun n ↦ f (τ n)) atTop (𝓝 c) :=
        tendsto_candidate_of_exactRightApproxTimeMeshSqueezedSeq21_24
          (X := X)
          (A := A)
          hAcontrol
          hω
          hc
          hN
          (fun n ↦ (hτmem n).2)
          hτgap
      have hEventuallyAbove : ∀ᶠ n : ℕ in atTop, a < f (τ n) :=
        (tendsto_order.1 hTauTendsto).1 _ ha
      have hBoth :
          ∀ᶠ n : ℕ in atTop, a < f (τ n) ∧ f (τ n) ≤ a :=
        hEventuallyAbove.and <| Filter.Eventually.of_forall fun n ↦ (hτmem n).1
      rcases hBoth.exists with ⟨n, hnlt, hnle⟩
      exact (not_le_of_gt hnlt) hnle
    · intro b hb
      by_contra hUpper
      have hFreq :
          ∃ᶠ s in 𝓝[>] t, b ≤ f s := by
        rw [Filter.Frequently]
        simpa [not_le] using hUpper
      rcases
          existsAntitoneRightBadSeq_ofFrequently_exactRightApproxTimeMesh21_24
            (t := t)
            (S := {s : NNReal | b ≤ f s})
            m0
            hFreq with
        ⟨N, τ, hN, _, hτmem, hτgap⟩
      have hTauTendsto :
          Tendsto (fun n ↦ f (τ n)) atTop (𝓝 c) :=
        tendsto_candidate_of_exactRightApproxTimeMeshSqueezedSeq21_24
          (X := X)
          (A := A)
          hAcontrol
          hω
          hc
          hN
          (fun n ↦ (hτmem n).2)
          hτgap
      have hEventuallyBelow : ∀ᶠ n : ℕ in atTop, f (τ n) < b :=
        (tendsto_order.1 hTauTendsto).2 _ hb
      have hBoth :
          ∀ᶠ n : ℕ in atTop, f (τ n) < b ∧ b ≤ f (τ n) :=
        hEventuallyBelow.and <| Filter.Eventually.of_forall fun n ↦ (hτmem n).1
      rcases hBoth.exists with ⟨n, hnlt, hnle⟩
      exact (not_le_of_gt hnlt) hnle
  · have hAnchorAnti : Antitone (rightApproxTime t) := rightApproxTime_antitone21_24 t
    have htCeil :
        t + 1 ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := by
      exact_mod_cast Nat.le_ceil ((t : ℝ) + 1)
    have hAnchorBdd : ∃ q : ℕ, ∀ n : ℕ, rightApproxTime t n ≤ q := by
      refine ⟨Nat.ceil ((t : ℝ) + 1), ?_⟩
      intro n
      have hOneLe : (1 : NNReal) ≤ ((n + 1 : ℕ) : NNReal) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hInvLe :
          (((n + 1 : ℕ) : NNReal)⁻¹) ≤ 1 := by
        simpa using one_div_le_one_div_of_le (show (0 : NNReal) < 1 from zero_lt_one) hOneLe
      calc
        rightApproxTime t n = t + (((n + 1 : ℕ) : NNReal)⁻¹) := by
          simp [rightApproxTime]
        _ ≤ t + 1 := by gcongr
        _ ≤ (Nat.ceil ((t : ℝ) + 1) : NNReal) := htCeil
    obtain ⟨c, hc⟩ :=
      tendsto_candidate_of_boundedOrderedSeq21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
        (rightApproxTime t)
        hAnchorBdd
        (Or.inr hAnchorAnti)
    refine ⟨c, ?_⟩
    refine tendsto_order.2 ?_
    constructor
    · intro a ha
      by_contra hLower
      have hFreq :
          ∃ᶠ s in 𝓝[>] t, f s ≤ a := by
        rw [Filter.Frequently]
        simpa [not_le] using hLower
      rcases
          existsAntitoneRightBadSeq_ofFrequently21_24
            (t := t)
            (S := {s : NNReal | f s ≤ a})
            hFreq with
        ⟨N, τ, hN, _, hτmem, hτgap⟩
      have hTauTendsto :
          Tendsto (fun n ↦ f (τ n)) atTop (𝓝 c) :=
        tendsto_candidate_of_rightSqueezedSeq_toAnchorLimit21_24
          (X := X)
          (A := A)
          hAcontrol
          hω
          hc
          hN
          (fun n ↦ (hτmem n).2)
          hτgap
      have hEventuallyAbove : ∀ᶠ n : ℕ in atTop, a < f (τ n) :=
        (tendsto_order.1 hTauTendsto).1 _ ha
      have hBoth :
          ∀ᶠ n : ℕ in atTop, a < f (τ n) ∧ f (τ n) ≤ a :=
        hEventuallyAbove.and <| Filter.Eventually.of_forall fun n ↦ (hτmem n).1
      rcases hBoth.exists with ⟨n, hnlt, hnle⟩
      exact (not_le_of_gt hnlt) hnle
    · intro b hb
      by_contra hUpper
      have hFreq :
          ∃ᶠ s in 𝓝[>] t, b ≤ f s := by
        rw [Filter.Frequently]
        simpa [not_le] using hUpper
      rcases
          existsAntitoneRightBadSeq_ofFrequently21_24
            (t := t)
            (S := {s : NNReal | b ≤ f s})
            hFreq with
        ⟨N, τ, hN, _, hτmem, hτgap⟩
      have hTauTendsto :
          Tendsto (fun n ↦ f (τ n)) atTop (𝓝 c) :=
        tendsto_candidate_of_rightSqueezedSeq_toAnchorLimit21_24
          (X := X)
          (A := A)
          hAcontrol
          hω
          hc
          hN
          (fun n ↦ (hτmem n).2)
          hτgap
      have hEventuallyBelow : ∀ᶠ n : ℕ in atTop, f (τ n) < b :=
        (tendsto_order.1 hTauTendsto).2 _ hb
      have hBoth :
          ∀ᶠ n : ℕ in atTop, f (τ n) < b ∧ b ≤ f (τ n) :=
        hEventuallyBelow.and <| Filter.Eventually.of_forall fun n ↦ (hτmem n).1
      rcases hBoth.exists with ⟨n, hnlt, hnle⟩
      exact (not_le_of_gt hnlt) hnle

/-- Helper for Theorem 21.24: the `rightLim` regularization of the packaged candidate has càdlàg
paths on the dyadic control event, and also on its zero complement branch. -/
private lemma hasCadlagPaths_rightLimDyadicControlCandidate21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hAcontrol : dyadicControlProperty21_24 (X := X) A) :
    HasCadlagPaths
      (fun t ω ↦ Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t) := by
  intro ω
  by_cases hω : ω ∈ A
  · have hRight :
        ∀ t : NNReal,
          ∃ c,
            Tendsto
              (fun s : NNReal ↦ dyadicControlCandidate X A s ω)
              (𝓝[>] t)
              (𝓝 c) :=
      exists_rightLimit_dyadicControlCandidate_of_memDyadicControlEvent21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
    have hLeft :
        ∀ t : Set.Ioi (0 : NNReal),
          ∃ c,
            Tendsto
              (fun s : NNReal ↦ dyadicControlCandidate X A s ω)
              (𝓝[<] (t : NNReal))
              (𝓝 c) :=
      exists_leftLimit_dyadicControlCandidate_of_memDyadicControlEvent21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
    -- Proof comment: once the packaged candidate has one-sided limits, the generic `rightLim`
    -- wrapper upgrades it to a càdlàg path.
    exact isCadlag_rightLim_of_oneSidedLimits21_24 _ hRight hLeft
  · have hZero :
        (fun s : NNReal ↦ dyadicControlCandidate X A s ω) = fun _ ↦ (0 : ℝ) := by
      funext s
      exact dyadicControlCandidate_eq_zero_of_not_mem21_24 (X := X) hω
    have hRight :
        ∀ t : NNReal,
          ∃ c,
            Tendsto
              (fun s : NNReal ↦ dyadicControlCandidate X A s ω)
              (𝓝[>] t)
              (𝓝 c) := by
      intro t
      refine ⟨0, ?_⟩
      simpa [hZero] using
        (tendsto_const_nhds : Tendsto (fun _ : NNReal ↦ (0 : ℝ)) (𝓝[>] t) (𝓝 0))
    have hLeft :
        ∀ t : Set.Ioi (0 : NNReal),
          ∃ c,
            Tendsto
              (fun s : NNReal ↦ dyadicControlCandidate X A s ω)
              (𝓝[<] (t : NNReal))
              (𝓝 c) := by
      intro t
      refine ⟨0, ?_⟩
      simpa [hZero] using
        (tendsto_const_nhds : Tendsto (fun _ : NNReal ↦ (0 : ℝ)) (𝓝[<] (t : NNReal)) (𝓝 0))
    -- Proof comment: off the control event, the candidate path is zero, so its `rightLim`
    -- regularization is also a constant càdlàg path.
    exact isCadlag_rightLim_of_oneSidedLimits21_24 _ hRight hLeft

/-- Helper for Theorem 21.24: the dyadic control candidate is measurable in each filtration slice.
-/
private lemma stronglyMeasurable_dyadicControlCandidate
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (hAc : μ Aᶜ = 0)
    (hAmeas : ∀ t : NNReal, MeasurableSet[ℱ t] A)
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    (hFiltration :
      ∀ t : NNReal, (⨅ n : ℕ, ℱ (dyadicRightApprox t n)) = ℱ t) :
    ∀ t : NNReal, StronglyMeasurable[ℱ t] (dyadicControlCandidate X A t) := by
  -- Route correction: proving strong measurability through `aeEq_fixedTime_of_dyadicRightApprox`
  -- is circular because that theorem already assumes the target measurability. Instead, realize
  -- the candidate as a piecewise shifted `limUnder`, prove that every shifted tail is measurable
  -- in each future slice, and then descend to the infimum filtration.
  intro t
  have hSliceMeas :
      ∀ m : ℕ,
        StronglyMeasurable[ℱ (dyadicRightApprox t m)] (dyadicControlCandidate X A t) := by
    intro m
    let mSlice : MeasurableSpace Ω := ℱ (dyadicRightApprox t m)
    have hTailMeas :
        StronglyMeasurable[mSlice]
          (fun ω ↦ limUnder atTop (fun n ↦ X (dyadicRightApprox t (n + m)) ω)) := by
      letI : MeasurableSpace Ω := mSlice
      -- Proof comment: every shifted dyadic sample is measurable in the fixed future slice
      -- `ℱ (dyadicRightApprox t m)`, so the pointwise `limUnder` is measurable there as well.
      simpa [mSlice] using
        (MeasureTheory.StronglyMeasurable.limUnder
          (l := atTop)
          (f := fun n ω ↦ X (dyadicRightApprox t (n + m)) ω)
          (hf := fun n ↦ by
            exact
              (hX.stronglyMeasurable (dyadicRightApprox t (n + m))).mono
                (ℱ.mono ((dyadicRightApprox_antitone t) (Nat.le_add_left m n)))))
    have hPiecewiseEq :
        dyadicControlCandidate X A t =
          A.piecewise
            (fun ω ↦ limUnder atTop (fun n ↦ X (dyadicRightApprox t (n + m)) ω))
            (fun _ ↦ (0 : ℝ)) := by
      funext ω
      by_cases hω : ω ∈ A
      · -- Proof comment: on the control event, the candidate agrees with every shifted tail
        -- `limUnder`.
        have hconv :
            Tendsto
              (fun n ↦ X (dyadicRightApprox t (n + m)) ω)
              atTop
              (𝓝 (dyadicControlCandidate X A t ω)) := by
          exact
            (tendsto_dyadicRightApprox_of_memDyadicControlEvent
              (X := X)
              hAcontrol
              hω
              t).comp
              (tendsto_add_atTop_nat m)
        simp [Set.piecewise, hω, hconv.limUnder_eq]
      · -- Proof comment: off the control event, the candidate is exactly the zero branch.
        simp [Set.piecewise, dyadicControlCandidate, hω]
    have hPiecewiseMeas :
        StronglyMeasurable[mSlice]
          (A.piecewise
            (fun ω ↦ limUnder atTop (fun n ↦ X (dyadicRightApprox t (n + m)) ω))
            (fun _ ↦ (0 : ℝ))) := by
      -- Proof comment: combine the shifted-tail measurability on `A` with the constant-zero branch
      -- on `Aᶜ`.
      exact hTailMeas.piecewise (hAmeas (dyadicRightApprox t m)) stronglyMeasurable_const
    -- Proof comment: rewrite the candidate into the measurable piecewise normal form at the slice
    -- `ℱ (dyadicRightApprox t m)`.
    simpa [hPiecewiseEq] using hPiecewiseMeas
  have hMeasInf :
      Measurable[(⨅ n : ℕ, ℱ (dyadicRightApprox t n))] (dyadicControlCandidate X A t) := by
    -- Proof comment: measurability with respect to the infimum filtration is equivalent to
    -- measurability in every future dyadic slice.
    rw [measurable_iff_comap_le]
    refine le_iInf fun n ↦ ?_
    exact measurable_iff_comap_le.mp (hSliceMeas n).measurable
  rw [← hFiltration t, stronglyMeasurable_iff_measurable_separable]
  refine ⟨hMeasInf, ?_⟩
  -- Proof comment: any one future-slice strongly measurable representation already gives the
  -- required separable range.
  exact (hSliceMeas 0).isSeparable_range

/-- Helper for Theorem 21.24: the `rightLim` regularization of the dyadic control candidate is
measurable in each filtration slice. -/
private lemma stronglyMeasurable_rightLimDyadicControlCandidate21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (hAc : μ Aᶜ = 0)
    (hAmeas : ∀ t : NNReal, MeasurableSet[ℱ t] A)
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    (hFiltration :
      ∀ t : NNReal, (⨅ n : ℕ, ℱ (dyadicRightApprox t n)) = ℱ t) :
    ∀ t : NNReal,
      StronglyMeasurable[ℱ t]
        (fun ω ↦ Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t) := by
  -- Route correction: the final cadlag owner is the `rightLim` regularization, so measurability
  -- is proved by representing that value on `A` as a reciprocal-mesh `limUnder` and descending
  -- from all future slices `ℱ (rightApproxTime t m)`.
  intro t
  have hCandidateMeas :
      ∀ s : NNReal, StronglyMeasurable[ℱ s] (dyadicControlCandidate X A s) :=
    stronglyMeasurable_dyadicControlCandidate
      (X := X)
      (μ := μ)
      (ℱ := ℱ)
      hX
      hEX_rc
      hAc
      hAmeas
      hAcontrol
      hFiltration
  have hSliceMeas :
      ∀ m : ℕ,
        StronglyMeasurable[ℱ (rightApproxTime t m)]
          (fun ω ↦ Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t) := by
    intro m
    let mSlice : MeasurableSpace Ω := ℱ (rightApproxTime t m)
    have hTailMeas :
        StronglyMeasurable[mSlice]
          (fun ω ↦
            limUnder atTop
              (fun n ↦ dyadicControlCandidate X A (rightApproxTime t (n + m)) ω)) := by
      letI : MeasurableSpace Ω := mSlice
      -- Proof comment: every shifted reciprocal sample of the candidate is measurable in the
      -- fixed future slice `ℱ (rightApproxTime t m)`, so the pointwise `limUnder` is measurable
      -- there as well.
      simpa [mSlice] using
        (MeasureTheory.StronglyMeasurable.limUnder
          (l := atTop)
          (f := fun n ω ↦ dyadicControlCandidate X A (rightApproxTime t (n + m)) ω)
          (hf := fun n ↦ by
            exact
              (hCandidateMeas (rightApproxTime t (n + m))).mono
                (ℱ.mono ((rightApproxTime_antitone21_24 t) (Nat.le_add_left m n)))))
    have hPiecewiseEq :
        (fun ω ↦ Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t) =
          A.piecewise
            (fun ω ↦
              limUnder atTop
                (fun n ↦ dyadicControlCandidate X A (rightApproxTime t (n + m)) ω))
            (fun _ ↦ (0 : ℝ)) := by
      funext ω
      by_cases hω : ω ∈ A
      · obtain ⟨c, hc⟩ :=
          exists_rightLimit_dyadicControlCandidate_of_memDyadicControlEvent21_24
            (X := X)
            (A := A)
            hAcontrol
            hω
            t
        have hShift :
            Tendsto
              (fun n ↦ dyadicControlCandidate X A (rightApproxTime t (n + m)) ω)
              atTop
              (𝓝 c) := by
          have hTimes :
              Tendsto (fun n ↦ rightApproxTime t (n + m)) atTop (𝓝[>] t) := by
            apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
            · simpa [Function.comp] using
                (tendsto_rightApproxTime21_24 t).comp (tendsto_add_atTop_nat m)
            · exact Filter.Eventually.of_forall fun n ↦ lt_rightApproxTime t (n + m)
          exact hc.comp hTimes
        have hRightEq :
            Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t = c := by
          exact
            rightLim_eq_of_tendsto
              (show (𝓝[>] t) ≠ ⊥ from (show (𝓝[>] t).NeBot from inferInstance).ne)
              hc
        -- Proof comment: on the control event, both the `rightLim` value and the shifted
        -- reciprocal tail record the same strict right limit `c`.
        simp [Set.piecewise, hω, hRightEq, hShift.limUnder_eq]
      · have hZero :
            (fun s : NNReal ↦ dyadicControlCandidate X A s ω) = fun _ ↦ (0 : ℝ) := by
          funext s
          exact dyadicControlCandidate_eq_zero_of_not_mem21_24 (X := X) hω
        have hRightZero :
            Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t = 0 := by
          exact
            rightLim_eq_of_tendsto
              (show (𝓝[>] t) ≠ ⊥ from (show (𝓝[>] t).NeBot from inferInstance).ne)
              (by simpa [hZero] using
                (tendsto_const_nhds :
                  Tendsto (fun _ : NNReal ↦ (0 : ℝ)) (𝓝[>] t) (𝓝 0)))
        -- Proof comment: off the control event, the candidate is the zero path, so both owners
        -- reduce to the constant-zero branch.
        simp [Set.piecewise, hω, hRightZero]
    have hPiecewiseMeas :
        StronglyMeasurable[mSlice]
          (A.piecewise
            (fun ω ↦
              limUnder atTop
                (fun n ↦ dyadicControlCandidate X A (rightApproxTime t (n + m)) ω))
            (fun _ ↦ (0 : ℝ))) := by
      -- Proof comment: combine the shifted reciprocal-tail measurability on `A` with the
      -- constant-zero exceptional branch.
      exact hTailMeas.piecewise (hAmeas (rightApproxTime t m)) stronglyMeasurable_const
    -- Proof comment: rewrite the `rightLim` regularization into the measurable piecewise normal
    -- form at the future slice `ℱ (rightApproxTime t m)`.
    simpa [hPiecewiseEq] using hPiecewiseMeas
  have hMeasInf :
      Measurable[(⨅ n : ℕ, ℱ (rightApproxTime t n))]
        (fun ω ↦ Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t) := by
    -- Proof comment: measurability with respect to the reciprocal-mesh infimum is equivalent to
    -- measurability in every future reciprocal slice.
    rw [measurable_iff_comap_le]
    refine le_iInf fun n ↦ ?_
    exact measurable_iff_comap_le.mp (hSliceMeas n).measurable
  have hMeasAtT :
      Measurable[ℱ t]
        (fun ω ↦ Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t) := by
    rw [← filtration_iInf_add_inv_succ_eq (ℱ := ℱ) t]
    simpa [rightApproxTime] using hMeasInf
  rw [stronglyMeasurable_iff_measurable_separable]
  refine ⟨hMeasAtT, ?_⟩
  -- Proof comment: any one future-slice strongly measurable representation already gives the
  -- required separable range for the `rightLim` regularization.
  exact (hSliceMeas 0).isSeparable_range

/-- Helper for Theorem 21.24: every reciprocal future sample stays within one unit of its base
time. -/
private lemma rightApproxTime_le_self_add_one (t : NNReal) (n : ℕ) :
    rightApproxTime t n ≤ t + 1 := by
  have hOneLe : (1 : NNReal) ≤ ((n + 1 : ℕ) : NNReal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hInvLe :
      (((n + 1 : ℕ) : NNReal)⁻¹) ≤ 1 := by
    simpa using
      one_div_le_one_div_of_le (show (0 : NNReal) < 1 from zero_lt_one) hOneLe
  simpa [rightApproxTime] using add_le_add_left hInvLe t

/-- Helper for Theorem 21.24: right continuity of the expectation function transports directly
along the reciprocal right-approximation sequence. -/
private lemma tendsto_expectation_rightApproxTime21_24
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (t : NNReal) :
    Tendsto (fun n : ℕ ↦ μ[X (rightApproxTime t n)]) atTop (𝓝 (μ[X t])) := by
  have happrox_mem : ∀ᶠ n : ℕ in atTop, rightApproxTime t n ∈ Set.Ici t := by
    -- Proof comment: every reciprocal future sample stays on the right side of `t`.
    exact Eventually.of_forall fun n ↦ (lt_rightApproxTime t n).le
  have happrox :
      Tendsto (rightApproxTime t) atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_rightApproxTime21_24 t)
      happrox_mem
  -- Proof comment: compose the right-continuous expectation map with the reciprocal future mesh.
  simpa [Function.comp] using Filter.Tendsto.comp (hEX_rc t) happrox

/-- Helper for Theorem 21.24: the conditional expectations of the reciprocal future samples back
to time `t` converge to `X t` in `L¹`. -/
private lemma tendsto_eLpNorm_condExp_rightApproxTime_sub_slice21_24
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (t : NNReal) :
    Tendsto
      (fun n : ℕ ↦
        eLpNorm
          (fun ω ↦ X t ω - μ[X (rightApproxTime t n) | ℱ t] ω)
          1 μ)
      atTop
      (𝓝 0) := by
  have hExpTendsto :
      Tendsto (fun n : ℕ ↦ μ[X (rightApproxTime t n)]) atTop (𝓝 (μ[X t])) :=
    tendsto_expectation_rightApproxTime21_24 (X := X) (μ := μ) hEX_rc t
  have hGapTendsto :
      Tendsto (fun n : ℕ ↦ μ[X t] - μ[X (rightApproxTime t n)]) atTop (𝓝 0) := by
    -- Proof comment: the reciprocal expectation gap is nonnegative and vanishes by right
    -- continuity.
    simpa using hExpTendsto.const_sub (μ[X t])
  have hEq :
      (fun n : ℕ ↦
        eLpNorm
          (fun ω ↦ X t ω - μ[X (rightApproxTime t n) | ℱ t] ω)
          1 μ) =
        fun n : ℕ ↦ ENNReal.ofReal (μ[X t] - μ[X (rightApproxTime t n)]) := by
    funext n
    have hle : μ[X (rightApproxTime t n) | ℱ t] ≤ᵐ[μ] X t :=
      hX.condExp_ae_le (lt_rightApproxTime t n).le
    have hnonneg :
        0 ≤ᵐ[μ] fun ω ↦ X t ω - μ[X (rightApproxTime t n) | ℱ t] ω := by
      filter_upwards [hle] with ω hω
      exact sub_nonneg.mpr hω
    have hInt :
        Integrable
          (fun ω ↦ X t ω - μ[X (rightApproxTime t n) | ℱ t] ω) μ :=
      (hX.integrable t).sub integrable_condExp
    calc
      eLpNorm
          (fun ω ↦ X t ω - μ[X (rightApproxTime t n) | ℱ t] ω)
          1 μ
          = ENNReal.ofReal
              (∫ ω, ‖X t ω - μ[X (rightApproxTime t n) | ℱ t] ω‖ ∂μ) := by
            rw [eLpNorm_one_eq_lintegral_enorm,
              ← ofReal_integral_norm_eq_lintegral_enorm hInt]
      _ = ENNReal.ofReal
            (∫ ω, (X t ω - μ[X (rightApproxTime t n) | ℱ t] ω) ∂μ) := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [hnonneg] with ω hω
          rw [Real.norm_eq_abs, abs_of_nonneg hω]
      _ = ENNReal.ofReal (μ[X t] - μ[X (rightApproxTime t n)]) := by
          rw [integral_sub (hX.integrable t) integrable_condExp,
            integral_condExp (ℱ.le t)]
  rw [hEq]
  -- Proof comment: once the `L¹` norm is rewritten as the reciprocal expectation gap, continuity
  -- of `ENNReal.ofReal` transports the vanishing real gap to the desired limit.
  simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hGapTendsto

/-- Helper for Theorem 21.24: the negative parts of the reciprocal future samples are uniformly
integrable after reindexing the bounded-horizon owner at horizon `t + 1`. -/
private lemma rightApproxTimeNegPartUniformIntegrable21_24
    (hX : Supermartingale X ℱ μ) (t : NNReal) :
    UniformIntegrable (fun n : ℕ ↦ fun ω ↦ (-X (rightApproxTime t n) ω)⁺) 1 μ := by
  let q : NNReal := t + 1
  let τ : ℕ → {u : NNReal // u ≤ q} := fun n ↦
    ⟨rightApproxTime t n, by
      -- Proof comment: the reciprocal future samples stay inside the deterministic horizon
      -- needed for the bounded-horizon negative-part owner.
      simpa [q] using rightApproxTime_le_self_add_one t n⟩
  have hUIq :
      UniformIntegrable (fun s : {u : NNReal // u ≤ q} ↦ fun ω ↦ (-X s.1 ω)⁺) 1 μ :=
    boundedHorizonNegPartUniformIntegrable (X := X) (μ := μ) (ℱ := ℱ) hX q
  -- Proof comment: deterministic reindexing preserves uniform integrability of the bounded-
  -- horizon negative-part owner.
  simpa [τ] using uniformIntegrable_comp (μ := μ) hUIq τ

/-- Helper for Theorem 21.24: shifting the decreasing reciprocal filtration family does not change
its infimum. -/
private lemma iInf_filtration_rightApproxTime_add_eq21_24
    (μ : Measure Ω) [UsualConditions ℱ μ] (t : NNReal) (m : ℕ) :
    (⨅ n : ℕ, ℱ (rightApproxTime t (n + m))) = ℱ t := by
  let hUsual : UsualConditions ℱ μ := inferInstance
  letI : Filtration.IsRightContinuous ℱ := hUsual.toIsRightContinuous
  have hanti : Antitone (rightApproxTime t) := rightApproxTime_antitone21_24 t
  refine le_antisymm ?_ ?_
  · have hTailLe :
        (⨅ n : ℕ, ℱ (rightApproxTime t (n + m))) ≤ ⨅ n : ℕ, ℱ (rightApproxTime t n) := by
      refine le_iInf fun k ↦ ?_
      by_cases hmk : m ≤ k
      · rcases Nat.exists_eq_add_of_le hmk with ⟨j, rfl⟩
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (iInf_le (fun n : ℕ ↦ ℱ (rightApproxTime t (n + m))) j)
      · have hkm : k ≤ m := (Nat.lt_of_not_ge hmk).le
        exact
          (iInf_le (fun n : ℕ ↦ ℱ (rightApproxTime t (n + m))) 0).trans
            (ℱ.mono (by simpa using hanti hkm))
    calc
      (⨅ n : ℕ, ℱ (rightApproxTime t (n + m))) ≤ ⨅ n : ℕ, ℱ (rightApproxTime t n) := hTailLe
      _ = ℱ t := by
          simpa [rightApproxTime] using filtration_iInf_add_inv_succ_eq (ℱ := ℱ) t
  · -- Proof comment: every shifted reciprocal stage still lies strictly to the right of `t`, so
    -- `ℱ t` is below the whole tail family.
    refine le_iInf fun n ↦ ℱ.mono (lt_rightApproxTime t (n + m)).le

/-- Helper for Theorem 21.24: the negative parts of the reciprocal future samples converge to the
candidate negative part in `L¹`. -/
private lemma tendsto_eLpNorm_negPart_rightApproxTime_to_candidate21_24
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (rightApproxTime t n) ω) atTop (𝓝 (Xtilde t ω))) :
    Integrable (fun ω ↦ (-Xtilde t ω)⁺) μ ∧
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ (-X (rightApproxTime t n) ω)⁺ - (-Xtilde t ω)⁺)
            1 μ)
        atTop
        (𝓝 0) := by
  have hNegUI :
      UniformIntegrable (fun n : ℕ ↦ fun ω ↦ (-X (rightApproxTime t n) ω)⁺) 1 μ :=
    rightApproxTimeNegPartUniformIntegrable21_24 (X := X) (μ := μ) (ℱ := ℱ) hX t
  have hNegAe :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (-X (rightApproxTime t n) ω)⁺) atTop
        (𝓝 ((-Xtilde t ω)⁺)) := by
    -- Proof comment: the negative-part map is continuous, so it preserves the reciprocal future
    -- limit.
    filter_upwards [hXt_lim] with ω hω
    exact ((continuous_id.neg.max continuous_const).tendsto _).comp hω
  have hNegInt : Integrable (fun ω ↦ (-Xtilde t ω)⁺) μ :=
    hNegUI.integrable_of_ae_tendsto hNegAe
  have hNegMemLp : MemLp (fun ω ↦ (-Xtilde t ω)⁺) 1 μ :=
    memLp_one_iff_integrable.2 hNegInt
  have hNegL1 :
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ (-X (rightApproxTime t n) ω)⁺ - (-Xtilde t ω)⁺)
            1 μ)
        atTop
        (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae
      le_rfl
      ENNReal.one_ne_top
      (fun n ↦ hNegUI.aestronglyMeasurable n)
      hNegMemLp
      hNegUI.unifIntegrable
      hNegAe
  exact ⟨hNegInt, hNegL1⟩

/-- Helper for Theorem 21.24: the reciprocal future candidate is integrable at each fixed time.
-/
private lemma integrable_candidate_of_rightApproxTime21_24
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (rightApproxTime t n) ω) atTop (𝓝 (Xtilde t ω))) :
    Integrable (Xtilde t) μ := by
  have hNeg :=
    tendsto_eLpNorm_negPart_rightApproxTime_to_candidate21_24
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_lim
  have hNegInt : Integrable (fun ω ↦ (-Xtilde t ω)⁺) μ := hNeg.1
  let q : NNReal := t + 1
  obtain ⟨C, hC⟩ := boundedHorizonELpNormOneBounded (X := X) (μ := μ) (ℱ := ℱ) hX q
  have hPosMeas :
      ∀ n, AEMeasurable (fun ω ↦ ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺)) μ := by
    intro n
    have hmeas :
        AEMeasurable (fun ω ↦ (X (rightApproxTime t n) ω)⁺) μ :=
      ((hX.integrable (rightApproxTime t n)).pos_part).aestronglyMeasurable.aemeasurable
    exact hmeas.ennreal_ofReal
  have hPosTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺))
          atTop
          (𝓝 (ENNReal.ofReal ((Xtilde t ω)⁺))) := by
    -- Proof comment: the positive-part map is continuous too, so the reciprocal future limit
    -- transfers to the candidate positive part.
    filter_upwards [hXt_lim] with ω hω
    exact ((ENNReal.continuous_ofReal.comp (continuous_id.max continuous_const)).tendsto _).comp
      hω
  have hFatou :
      ∫⁻ ω, ENNReal.ofReal ((Xtilde t ω)⁺) ∂μ ≤
        liminf
          (fun n ↦ ∫⁻ ω, ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺) ∂μ)
          atTop := by
    -- Proof comment: Fatou controls the lower integral of the candidate positive part by the
    -- liminf of the reciprocal future positive-part integrals.
    calc
      ∫⁻ ω, ENNReal.ofReal ((Xtilde t ω)⁺) ∂μ
          = ∫⁻ ω,
              liminf (fun n ↦ ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺)) atTop ∂μ := by
                refine lintegral_congr_ae ?_
                filter_upwards [hPosTendsto] with ω hω
                exact hω.liminf_eq.symm
      _ ≤
          liminf
            (fun n ↦ ∫⁻ ω, ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺) ∂μ)
            atTop := by
              exact MeasureTheory.lintegral_liminf_le' hPosMeas
  have hPosIntegralBound :
      ∀ᶠ n : ℕ in atTop,
        ∫⁻ ω, ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺) ∂μ ≤ (C : ℝ≥0∞) := by
    filter_upwards with n
    have hs :
        eLpNorm (X (rightApproxTime t n)) 1 μ ≤ C :=
      hC ⟨rightApproxTime t n, by simpa [q] using rightApproxTime_le_self_add_one t n⟩
    have hdom :
        ∀ᵐ ω ∂μ,
          ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺) ≤
            (↑‖X (rightApproxTime t n) ω‖₊ : ENNReal) := by
      filter_upwards [] with ω
      have hpoint :
          (X (rightApproxTime t n) ω)⁺ ≤ |X (rightApproxTime t n) ω| := by
        by_cases hω : 0 ≤ X (rightApproxTime t n) ω
        · simp [Real.norm_eq_abs, hω, abs_of_nonneg hω]
        · have hω' : X (rightApproxTime t n) ω ≤ 0 := le_of_not_ge hω
          simp [posPart_eq_zero.2 hω', abs_of_nonpos hω', hω']
      exact_mod_cast hpoint
    calc
      ∫⁻ ω, ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺) ∂μ
          ≤ ∫⁻ ω, (↑‖X (rightApproxTime t n) ω‖₊ : ENNReal) ∂μ :=
            lintegral_mono_ae hdom
      _ = ∫⁻ ω, ‖X (rightApproxTime t n) ω‖ₑ ∂μ := by
            refine lintegral_congr_ae ?_
            exact ae_of_all μ (fun ω ↦ by simp [enorm_eq_nnnorm])
      _ = eLpNorm (X (rightApproxTime t n)) 1 μ := by
            rw [eLpNorm_one_eq_lintegral_enorm]
      _ ≤ C := hs
  have hPosLintegralNeTop :
      ∫⁻ ω, ENNReal.ofReal ((Xtilde t ω)⁺) ∂μ ≠ ∞ := by
    apply lt_top_iff_ne_top.mp
    exact lt_of_le_of_lt
      (hFatou.trans (Filter.liminf_le_of_frequently_le hPosIntegralBound.frequently))
      (by simp)
  have hPosInt : Integrable (fun ω ↦ (Xtilde t ω)⁺) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((((hXt_meas.mono (ℱ.le t)).measurable.max measurable_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ posPart_nonneg (Xtilde t ω))).1 hPosLintegralNeTop
  have hNormInt :
      Integrable (fun ω ↦ (Xtilde t ω)⁺ + (-Xtilde t ω)⁺) μ :=
    hPosInt.add hNegInt
  have hNormEq :
      ∀ ω, ‖Xtilde t ω‖ = (Xtilde t ω)⁺ + (-Xtilde t ω)⁺ := by
    intro ω
    by_cases hω : 0 ≤ Xtilde t ω
    · rw [Real.norm_eq_abs, abs_of_nonneg hω, posPart_eq_self.2 hω,
        posPart_eq_zero.2 (neg_nonpos.mpr hω), add_zero]
    · have hω' : Xtilde t ω ≤ 0 := le_of_not_ge hω
      rw [Real.norm_eq_abs, abs_of_nonpos hω', posPart_eq_zero.2 hω',
        posPart_eq_self.2 (neg_nonneg.mpr hω'), zero_add]
  have hNormInt' : Integrable (fun ω ↦ ‖Xtilde t ω‖) μ := by
    refine hNormInt.congr ?_
    exact ae_of_all μ (fun ω ↦ (hNormEq ω).symm)
  exact
    (integrable_norm_iff ((hXt_meas.mono (ℱ.le t)).aestronglyMeasurable)).1 hNormInt'

/-- Helper for Theorem 21.24: each fixed reciprocal future slice conditioned back to time `t`
lies below the reciprocal-limit candidate. -/
private lemma condExp_futureSlice_ae_le_candidate_of_rightApproxTime21_24
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal) (m : ℕ)
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (rightApproxTime t n) ω) atTop (𝓝 (Xtilde t ω))) :
    μ[X (rightApproxTime t m) | ℱ t] ≤ᵐ[μ] Xtilde t := by
  let mFamily : ℕ → MeasurableSpace Ω := fun n ↦ ℱ (rightApproxTime t (n + m))
  have hm_le : ∀ n, mFamily n ≤ mΩ := fun n ↦ ℱ.le _
  have hm_anti : Antitone mFamily := by
    intro i j hij
    exact ℱ.mono ((rightApproxTime_antitone21_24 t) (Nat.add_le_add_right hij m))
  have hTailFiltration : (⨅ n : ℕ, mFamily n) = ℱ t :=
    iInf_filtration_rightApproxTime_add_eq21_24 (ℱ := ℱ) (μ := μ) t m
  have hCondTendsto :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ μ[X (rightApproxTime t m) | mFamily n] ω)
          atTop
          (𝓝 (μ[X (rightApproxTime t m) | ℱ t] ω)) := by
    -- Proof comment: reverse Lévy applies to the decreasing reciprocal filtration tail.
    simpa [mFamily, hTailFiltration] using
      tendsto_ae_condExp_iInf_of_antitone
        (μ := μ)
        (m := mFamily)
        hm_le
        hm_anti
        (hX.integrable (rightApproxTime t m))
  have hFutureLe :
      ∀ n : ℕ,
        μ[X (rightApproxTime t m) | mFamily n] ≤ᵐ[μ]
          fun ω ↦ X (rightApproxTime t (n + m)) ω := by
    intro n
    have htime :
        rightApproxTime t (n + m) ≤ rightApproxTime t m :=
      (rightApproxTime_antitone21_24 t) (Nat.le_add_left m n)
    simpa [mFamily] using hX.condExp_ae_le htime
  have hTailLimit :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ X (rightApproxTime t (n + m)) ω)
          atTop
          (𝓝 (Xtilde t ω)) := by
    -- Proof comment: shifting a convergent reciprocal future sequence preserves its pointwise
    -- limit.
    filter_upwards [hXt_lim] with ω hω
    exact hω.comp (tendsto_add_atTop_nat m)
  have hFutureLeAll :
      ∀ᵐ ω ∂μ,
        ∀ n : ℕ,
          μ[X (rightApproxTime t m) | mFamily n] ω ≤ X (rightApproxTime t (n + m)) ω :=
    ae_all_iff.2 hFutureLe
  filter_upwards [hCondTendsto, hTailLimit, hFutureLeAll] with ω hωCond hωTail hωLe
  exact le_of_tendsto_of_tendsto' hωCond hωTail hωLe

/-- Helper for Theorem 21.24: on every `ℱ t`-measurable test set, the reciprocal future candidate
has no larger integral than the time-`t` slice. -/
private lemma candidate_setIntegral_le_fixedTime_of_rightApproxTime21_24
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (rightApproxTime t n) ω) atTop (𝓝 (Xtilde t ω)))
    {s : Set Ω} (hs : MeasurableSet[ℱ t] s) :
    ∫ ω in s, Xtilde t ω ∂μ ≤ ∫ ω in s, X t ω ∂μ := by
  have hXt_int :
      Integrable (Xtilde t) μ :=
    integrable_candidate_of_rightApproxTime21_24
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim
  have hNegInt :
      Integrable (fun ω ↦ (-Xtilde t ω)⁺) μ
      ∧
        Tendsto
          (fun n : ℕ ↦
            eLpNorm
              (fun ω ↦ (-X (rightApproxTime t n) ω)⁺ - (-Xtilde t ω)⁺)
              1 μ)
          atTop
          (𝓝 0) :=
    tendsto_eLpNorm_negPart_rightApproxTime_to_candidate21_24
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_lim
  have hNegSet :
      Tendsto
        (fun n : ℕ ↦ ∫ ω in s, (-X (rightApproxTime t n) ω)⁺ ∂μ)
        atTop
        (𝓝 (∫ ω in s, (-Xtilde t ω)⁺ ∂μ)) :=
    tendstoRestrictedIntegralOfTendstoL1
      (μ := μ)
      (g := fun ω ↦ (-Xtilde t ω)⁺)
      hNegInt.1
      (fun n ↦ (hX.integrable (rightApproxTime t n)).neg_part)
      hNegInt.2
  have hSliceDecomp :
      ∀ n : ℕ,
        ∫ ω in s, X (rightApproxTime t n) ω ∂μ =
          ∫ ω in s, (X (rightApproxTime t n) ω)⁺ ∂μ -
            ∫ ω in s, (-X (rightApproxTime t n) ω)⁺ ∂μ := by
    intro n
    -- Proof comment: on the restricted measure, each reciprocal future sample splits into
    -- positive and negative parts exactly as on the whole space.
    simpa using
      (integral_eq_integral_pos_part_sub_integral_neg_part
        (μ := μ.restrict s)
        (hX.integrable (rightApproxTime t n)).restrict)
  have hCandidateDecomp :
      ∫ ω in s, Xtilde t ω ∂μ =
        ∫ ω in s, (Xtilde t ω)⁺ ∂μ -
          ∫ ω in s, (-Xtilde t ω)⁺ ∂μ := by
    -- Proof comment: the candidate admits the same positive/negative-part decomposition on the
    -- restricted test set.
    simpa using
      (integral_eq_integral_pos_part_sub_integral_neg_part
        (μ := μ.restrict s)
        hXt_int.restrict)
  have hPosMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun ω ↦ ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺))
          (μ.restrict s) := by
    intro n
    exact ((hX.integrable (rightApproxTime t n)).pos_part.restrict.aestronglyMeasurable
      ).aemeasurable.ennreal_ofReal
  have hPosTendsto :
      ∀ᵐ ω ∂μ.restrict s,
        Tendsto
          (fun n ↦ ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺))
          atTop
          (𝓝 (ENNReal.ofReal ((Xtilde t ω)⁺))) := by
    -- Proof comment: restricting to the test set preserves the pointwise reciprocal future
    -- convergence, and the positive-part map stays continuous after composing with
    -- `ENNReal.ofReal`.
    refine ae_restrict_of_ae ?_
    filter_upwards [hXt_lim] with ω hω
    exact ((ENNReal.continuous_ofReal.comp (continuous_id.max continuous_const)).tendsto _).comp
      hω
  have hPosIntegralEq :
      (fun n : ℕ ↦
        ∫⁻ ω, ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺) ∂μ.restrict s) =
        fun n : ℕ ↦ ENNReal.ofReal (∫ ω in s, (X (rightApproxTime t n) ω)⁺ ∂μ) := by
    funext n
    let f : Ω → ℝ := fun ω ↦ (X (rightApproxTime t n) ω)⁺
    have hf_int : Integrable f (μ.restrict s) :=
      ((hX.integrable (rightApproxTime t n)).pos_part).restrict
    have hf_nonneg : 0 ≤ᵐ[μ.restrict s] f := Eventually.of_forall fun ω ↦ posPart_nonneg _
    simpa [f] using
      (ofReal_integral_eq_lintegral_ofReal (μ := μ.restrict s) hf_int hf_nonneg).symm
  have hFatou :
      ENNReal.ofReal (∫ ω in s, (Xtilde t ω)⁺ ∂μ) ≤
        liminf
          (fun n : ℕ ↦ ENNReal.ofReal (∫ ω in s, (X (rightApproxTime t n) ω)⁺ ∂μ))
          atTop := by
    -- Proof comment: Fatou on the restricted measure bounds the candidate positive part by the
    -- liminf of the reciprocal future positive parts.
    calc
      ENNReal.ofReal (∫ ω in s, (Xtilde t ω)⁺ ∂μ)
          = ∫⁻ ω, ENNReal.ofReal ((Xtilde t ω)⁺) ∂μ.restrict s := by
              let f : Ω → ℝ := fun ω ↦ (Xtilde t ω)⁺
              have hf_int : Integrable f (μ.restrict s) := hXt_int.pos_part.restrict
              have hf_nonneg : 0 ≤ᵐ[μ.restrict s] f := Eventually.of_forall fun ω ↦ posPart_nonneg _
              simpa [f] using
                ofReal_integral_eq_lintegral_ofReal (μ := μ.restrict s) hf_int hf_nonneg
      _ = ∫⁻ ω,
            liminf (fun n ↦ ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺)) atTop
            ∂μ.restrict s := by
              refine lintegral_congr_ae ?_
              filter_upwards [hPosTendsto] with ω hω
              exact hω.liminf_eq.symm
      _ ≤
          liminf
            (fun n : ℕ ↦
              ∫⁻ ω, ENNReal.ofReal ((X (rightApproxTime t n) ω)⁺) ∂μ.restrict s)
            atTop := by
              exact MeasureTheory.lintegral_liminf_le' hPosMeas
      _ =
          liminf
            (fun n : ℕ ↦ ENNReal.ofReal (∫ ω in s, (X (rightApproxTime t n) ω)⁺ ∂μ))
            atTop := by
              rw [hPosIntegralEq]
  have hPosUpper :
      ∀ n : ℕ,
        ∫ ω in s, (X (rightApproxTime t n) ω)⁺ ∂μ ≤
          ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (rightApproxTime t n) ω)⁺ ∂μ := by
    intro n
    have hSliceLe :
        ∫ ω in s, X (rightApproxTime t n) ω ∂μ ≤ ∫ ω in s, X t ω ∂μ :=
      hX.setIntegral_le (lt_rightApproxTime t n).le hs
    -- Proof comment: rewrite the reciprocal future slice integral by positive and negative parts,
    -- then move the negative contribution to the right side.
    linarith [hSliceLe, hSliceDecomp n]
  have hFutureCarrierNonneg :
      ∀ n : ℕ,
        0 ≤ ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (rightApproxTime t n) ω)⁺ ∂μ := by
    intro n
    have hPosNonneg :
        0 ≤ ∫ ω in s, (X (rightApproxTime t n) ω)⁺ ∂μ := by
      exact integral_nonneg_of_ae (μ := μ.restrict s) <|
        Eventually.of_forall fun ω ↦ posPart_nonneg (X (rightApproxTime t n) ω)
    exact hPosNonneg.trans (hPosUpper n)
  have hFutureCarrierTendsto :
      Tendsto
        (fun n : ℕ ↦
          ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (rightApproxTime t n) ω)⁺ ∂μ)
        atTop
        (𝓝 (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ)) :=
    tendsto_const_nhds.add hNegSet
  have hFutureCarrierNonnegLimit :
      0 ≤ ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ := by
    have hEventuallyNonneg :
        ∀ᶠ n : ℕ in atTop,
          ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (rightApproxTime t n) ω)⁺ ∂μ ∈ Set.Ici 0 :=
      Eventually.of_forall fun n ↦ hFutureCarrierNonneg n
    exact IsClosed.mem_of_tendsto isClosed_Ici hFutureCarrierTendsto hEventuallyNonneg
  have hFatouUpper :
      ENNReal.ofReal (∫ ω in s, (Xtilde t ω)⁺ ∂μ) ≤
        ENNReal.ofReal (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ) := by
    -- Proof comment: combine Fatou with the termwise reciprocal future bounds and pass to the
    -- limit in the negative-part integrals.
    calc
      ENNReal.ofReal (∫ ω in s, (Xtilde t ω)⁺ ∂μ)
          ≤
            liminf
              (fun n : ℕ ↦ ENNReal.ofReal (∫ ω in s, (X (rightApproxTime t n) ω)⁺ ∂μ))
              atTop := hFatou
      _ ≤
          liminf
            (fun n : ℕ ↦
              ENNReal.ofReal
                (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-X (rightApproxTime t n) ω)⁺ ∂μ))
            atTop := by
              exact Filter.liminf_le_liminf <|
                Eventually.of_forall fun n ↦ ENNReal.ofReal_le_ofReal (hPosUpper n)
      _ = ENNReal.ofReal (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ) := by
            simpa using
              (ENNReal.continuous_ofReal.tendsto
                (∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ)).comp
                hFutureCarrierTendsto |>.liminf_eq
  have hPosCandidateLe :
      ∫ ω in s, (Xtilde t ω)⁺ ∂μ ≤
        ∫ ω in s, X t ω ∂μ + ∫ ω in s, (-Xtilde t ω)⁺ ∂μ := by
    exact (ENNReal.ofReal_le_ofReal_iff hFutureCarrierNonnegLimit).mp hFatouUpper
  -- Proof comment: subtract the converged negative part from the positive-part Fatou bound to
  -- recover the desired upper inequality for the candidate itself.
  linarith [hCandidateDecomp, hPosCandidateLe]

/-- Helper for Theorem 21.24: the set-integral upper sandwich upgrades to the almost-everywhere
fixed-time inequality `Xtilde t ≤ X t` along the reciprocal future mesh. -/
private lemma candidate_ae_le_fixedTime_of_rightApproxTime21_24
    (hX : Supermartingale X ℱ μ)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (rightApproxTime t n) ω) atTop (𝓝 (Xtilde t ω))) :
    Xtilde t ≤ᵐ[μ] X t := by
  have hXt_int :
      Integrable (Xtilde t) μ :=
    integrable_candidate_of_rightApproxTime21_24
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim
  have hSliceMeas : StronglyMeasurable[ℱ t] (X t) := hX.stronglyMeasurable t
  have hTrimLe :
      Xtilde t ≤ᵐ[μ.trim (ℱ.le t)] X t := by
    refine MeasureTheory.ae_le_of_forall_setIntegral_le
      (hXt_int.trim (ℱ.le t) hXt_meas)
      ((hX.integrable t).trim (ℱ.le t) hSliceMeas) ?_
    intro s hs _hμs
    calc
      ∫ ω in s, Xtilde t ω ∂μ.trim (ℱ.le t) = ∫ ω in s, Xtilde t ω ∂μ := by
          symm
          exact MeasureTheory.setIntegral_trim (ℱ.le t) hXt_meas hs
      _ ≤ ∫ ω in s, X t ω ∂μ := by
          exact
            candidate_setIntegral_le_fixedTime_of_rightApproxTime21_24
              (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim hs
      _ = ∫ ω in s, X t ω ∂μ.trim (ℱ.le t) := by
          exact MeasureTheory.setIntegral_trim (ℱ.le t) hSliceMeas hs
  exact
    (MeasureTheory.StronglyMeasurable.ae_le_trim_iff
      (ℱ.le t) hXt_meas hSliceMeas).mp hTrimLe

/-- Helper for Theorem 21.24: the conditioned reciprocal future slices converge back up to the
candidate, so the time-`t` slice is almost surely bounded above by the candidate. -/
private lemma slice_ae_le_candidate_of_rightApproxTime21_24
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (rightApproxTime t n) ω) atTop (𝓝 (Xtilde t ω))) :
    X t ≤ᵐ[μ] Xtilde t := by
  have hXt_int :
      Integrable (Xtilde t) μ :=
    integrable_candidate_of_rightApproxTime21_24
      (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim
  have hCondL1 :
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ X t ω - μ[X (rightApproxTime t n) | ℱ t] ω)
            1 μ)
        atTop
        (𝓝 0) :=
    tendsto_eLpNorm_condExp_rightApproxTime_sub_slice21_24
      (X := X) (μ := μ) (ℱ := ℱ) hX hEX_rc t
  have hCondL1' :
      Tendsto
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ μ[X (rightApproxTime t n) | ℱ t] ω - X t ω)
            1 μ)
        atTop
        (𝓝 0) := by
    have hEq :
        (fun n : ℕ ↦
          eLpNorm
            (fun ω ↦ μ[X (rightApproxTime t n) | ℱ t] ω - X t ω)
            1 μ) =
          fun n : ℕ ↦
            eLpNorm
              (fun ω ↦ X t ω - μ[X (rightApproxTime t n) | ℱ t] ω)
              1 μ := by
      funext n
      calc
        eLpNorm
            (fun ω ↦ μ[X (rightApproxTime t n) | ℱ t] ω - X t ω)
            1 μ
            = eLpNorm
                (fun ω ↦ -(X t ω - μ[X (rightApproxTime t n) | ℱ t] ω))
                1 μ := by
                  refine eLpNorm_congr_ae ?_
                  exact ae_of_all μ fun ω ↦ by ring
        _ = eLpNorm
              (fun ω ↦ X t ω - μ[X (rightApproxTime t n) | ℱ t] ω)
              1 μ := by
                rw [show
                    (fun ω ↦ -(X t ω - μ[X (rightApproxTime t n) | ℱ t] ω)) =
                      -(fun ω ↦ X t ω - μ[X (rightApproxTime t n) | ℱ t] ω) from rfl,
                  eLpNorm_neg]
    rw [hEq]
    exact hCondL1
  have hSliceMeas : StronglyMeasurable[ℱ t] (X t) := hX.stronglyMeasurable t
  have hTrimLe :
      X t ≤ᵐ[μ.trim (ℱ.le t)] Xtilde t := by
    refine MeasureTheory.ae_le_of_forall_setIntegral_le
      ((hX.integrable t).trim (ℱ.le t) hSliceMeas)
      (hXt_int.trim (ℱ.le t) hXt_meas) ?_
    intro s hs _hμs
    have hCondSet :
        Tendsto
          (fun n : ℕ ↦ ∫ ω in s, μ[X (rightApproxTime t n) | ℱ t] ω ∂μ)
          atTop
          (𝓝 (∫ ω in s, X t ω ∂μ)) :=
      tendstoRestrictedIntegralOfTendstoL1
        (μ := μ)
        (g := X t)
        (hX.integrable t)
        (fun n ↦ integrable_condExp)
        hCondL1'
    have hCondUpper :
        ∀ n : ℕ,
          ∫ ω in s, μ[X (rightApproxTime t n) | ℱ t] ω ∂μ ≤ ∫ ω in s, Xtilde t ω ∂μ := by
      intro n
      have hPointwise :
          μ[X (rightApproxTime t n) | ℱ t] ≤ᵐ[μ] Xtilde t :=
        condExp_futureSlice_ae_le_candidate_of_rightApproxTime21_24
          (X := X) (μ := μ) (ℱ := ℱ) hX t n hXt_lim
      exact
        integral_mono_ae
          (integrable_condExp.restrict)
          hXt_int.restrict
          (ae_restrict_of_ae hPointwise)
    have hSetLe :
        ∫ ω in s, X t ω ∂μ ≤ ∫ ω in s, Xtilde t ω ∂μ := by
      -- Proof comment: the conditioned reciprocal future integrals stay below the candidate on
      -- every test set, and their `L¹` convergence forces the time-`t` set integral below the
      -- same bound.
      exact le_of_tendsto_of_tendsto' hCondSet tendsto_const_nhds hCondUpper
    calc
      ∫ ω in s, X t ω ∂μ.trim (ℱ.le t) = ∫ ω in s, X t ω ∂μ := by
          symm
          exact MeasureTheory.setIntegral_trim (ℱ.le t) hSliceMeas hs
      _ ≤ ∫ ω in s, Xtilde t ω ∂μ := hSetLe
      _ = ∫ ω in s, Xtilde t ω ∂μ.trim (ℱ.le t) := by
          exact MeasureTheory.setIntegral_trim (ℱ.le t) hXt_meas hs
  exact
    (MeasureTheory.StronglyMeasurable.ae_le_trim_iff
      (ℱ.le t) hSliceMeas hXt_meas).mp hTrimLe

/-- Helper for Theorem 21.24: once the reciprocal future samples converge almost surely to an
`ℱ t`-measurable candidate, the supermartingale inequality and right continuity of expectations
identify that candidate with `X t` almost surely. -/
private lemma aeEq_fixedTime_of_rightApproxTime21_24
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    {Xtilde : NNReal → Ω → ℝ} (t : NNReal)
    (hXt_meas : StronglyMeasurable[ℱ t] (Xtilde t))
    (hXt_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X (rightApproxTime t n) ω) atTop (𝓝 (Xtilde t ω))) :
    Xtilde t =ᵐ[μ] X t := by
  -- Proof comment: the upper sandwich comes from Fatou on positive parts, while the lower
  -- sandwich comes from the conditioned reciprocal future slices converging back to `X t`.
  exact
    (candidate_ae_le_fixedTime_of_rightApproxTime21_24
        (X := X) (μ := μ) (ℱ := ℱ) hX t hXt_meas hXt_lim).antisymm
      (slice_ae_le_candidate_of_rightApproxTime21_24
        (X := X) (μ := μ) (ℱ := ℱ) hX hEX_rc t hXt_meas hXt_lim)

/-- Helper for Theorem 21.24: the strict-right raw samples converge almost surely to the
`Function.rightLim` regularization once the future-time dyadic fixed-time theorem is threaded
through the full-measure control event. -/
private lemma ae_tendsto_rightApproxTime_to_rightLimDyadicControlCandidate21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (hAc : μ Aᶜ = 0)
    (hAmeas : ∀ s : NNReal, MeasurableSet[ℱ s] A)
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    (hFiltration :
      ∀ s : NNReal, (⨅ n : ℕ, ℱ (dyadicRightApprox s n)) = ℱ s)
    (t : NNReal) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦ X (rightApproxTime t n) ω)
        atTop
        (𝓝 (Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t)) := by
  have hAae : ∀ᵐ ω ∂μ, ω ∈ A := by
    simpa using (ae_iff.2 hAc)
  have hCandidateMeas :
      ∀ s : NNReal, StronglyMeasurable[ℱ s] (dyadicControlCandidate X A s) :=
    stronglyMeasurable_dyadicControlCandidate
      (X := X)
      (μ := μ)
      (ℱ := ℱ)
      hX
      hEX_rc
      hAc
      hAmeas
      hAcontrol
      hFiltration
  have hFutureDyadicLim :
      ∀ s : NNReal,
        ∀ᵐ ω ∂μ,
          Tendsto
            (fun n ↦ X (dyadicRightApprox s n) ω)
            atTop
            (𝓝 (dyadicControlCandidate X A s ω)) := by
    intro s
    filter_upwards [hAae] with ω hω
    exact
      tendsto_dyadicRightApprox_of_memDyadicControlEvent
        (X := X)
        hAcontrol
        hω
        s
  have hFutureEq :
      ∀ᵐ ω ∂μ,
        ∀ n : ℕ,
          X (rightApproxTime t n) ω = dyadicControlCandidate X A (rightApproxTime t n) ω := by
    rw [ae_all_iff]
    intro n
    simpa using
      (aeEq_fixedTime_of_dyadicRightApprox
        (X := X)
        (μ := μ)
        (ℱ := ℱ)
        hX
        hEX_rc
        hFiltration
        (t := rightApproxTime t n)
        (hCandidateMeas (rightApproxTime t n))
        (hFutureDyadicLim (rightApproxTime t n))).symm
  have hCandidateRightLim :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ dyadicControlCandidate X A (rightApproxTime t n) ω)
          atTop
          (𝓝 (Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t)) := by
    filter_upwards [hAae] with ω hω
    obtain ⟨c, hc⟩ :=
      exists_rightLimit_dyadicControlCandidate_of_memDyadicControlEvent21_24
        (X := X)
        (A := A)
        hAcontrol
        hω
        t
    have hTimes :
        Tendsto (fun n ↦ rightApproxTime t n) atTop (𝓝[>] t) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      · simpa [Function.comp] using tendsto_rightApproxTime21_24 t
      · exact Filter.Eventually.of_forall fun n ↦ lt_rightApproxTime t n
    have hShift :
        Tendsto
          (fun n ↦ dyadicControlCandidate X A (rightApproxTime t n) ω)
          atTop
          (𝓝 c) := by
      exact hc.comp hTimes
    have hRightEq :
        Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t = c := by
      exact
        rightLim_eq_of_tendsto
          (show (𝓝[>] t) ≠ ⊥ from (show (𝓝[>] t).NeBot from inferInstance).ne)
          hc
    -- Proof comment: on the control event, the reciprocal future samples of the candidate tend
    -- to the same right limit recorded by the `Function.rightLim` wrapper.
    simpa [hRightEq] using hShift
  filter_upwards [hFutureEq, hCandidateRightLim] with ω hωEq hωLim
  have hEventuallyEq :
      (fun n ↦ X (rightApproxTime t n) ω) =ᶠ[atTop]
        fun n ↦ dyadicControlCandidate X A (rightApproxTime t n) ω :=
    Filter.Eventually.of_forall hωEq
  exact hωLim.congr' hEventuallyEq.symm

/-- Helper for Theorem 21.24: the final fixed-time identification must now be proved for the
`rightLim` regularization of the dyadic control candidate. -/
private lemma aeEq_fixedTime_of_rightLimDyadicControlCandidate21_24
    {A : Set Ω}
    [DecidablePred (· ∈ A)]
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t)
    (hAc : μ Aᶜ = 0)
    (hAmeas : ∀ s : NNReal, MeasurableSet[ℱ s] A)
    (hAcontrol : dyadicControlProperty21_24 (X := X) A)
    (hFiltration :
      ∀ s : NNReal, (⨅ n : ℕ, ℱ (dyadicRightApprox s n)) = ℱ s)
    (t : NNReal)
    (hXt_meas :
      StronglyMeasurable[ℱ t]
        (fun ω ↦ Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t)) :
    (fun ω ↦ Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t) =ᵐ[μ] X t := by
  -- Route correction: the cadlag owner is now the `rightLim` regularization, so the old
  -- fixed-time closure along the eventually constant exact dyadic mesh no longer applies.
  have hXt_lim :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ X (rightApproxTime t n) ω)
          atTop
          (𝓝 (Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t)) :=
    ae_tendsto_rightApproxTime_to_rightLimDyadicControlCandidate21_24
      (X := X)
      (A := A)
      (μ := μ)
      (ℱ := ℱ)
      hX
      hEX_rc
      hAc
      hAmeas
      hAcontrol
      hFiltration
      t
  -- Proof comment: once the strict-right raw samples converge to the `rightLim` witness, the
  -- reciprocal fixed-time sandwich identifies that witness with `X t` almost surely.
  exact
    aeEq_fixedTime_of_rightApproxTime21_24
      (X := X)
      (Xtilde := fun s ω ↦
        Function.rightLim (fun u : NNReal ↦ dyadicControlCandidate X A u ω) s)
      (μ := μ)
      (ℱ := ℱ)
      hX
      hEX_rc
      t
      hXt_meas
      hXt_lim

/-- Theorem 21.24: Doob's regularization theorem. A supermartingale on a filtration satisfying the
usual conditions whose expectation function `t ↦ μ[X t]` is right continuous admits a
modification with càdlàg paths. -/
theorem exists_modification_with_cadlag_paths_of_supermartingale
    (hX : Supermartingale X ℱ μ)
    (hEX_rc :
      ∀ t : NNReal, ContinuousWithinAt (fun s : NNReal ↦ μ[X s]) (Set.Ici t) t) :
    ∃ Xtilde : NNReal → Ω → ℝ,
      AreModifications μ X Xtilde ∧ HasCadlagPaths Xtilde := by
  -- Route correction: pivot from the old reciprocal-mesh tail to the public dyadic approximation
  -- API, so the remaining frontier is exactly the bounded-horizon master-event and fixed-time
  -- identification lemmas rather than more bespoke witness-prefix transport.
  have hNullMeas : ∀ t : NNReal, ∀ {s : Set Ω}, μ s = 0 → MeasurableSet[ℱ t] s := by
    intro t s hs
    exact measurableSet_filtration_of_null (μ := μ) (ℱ := ℱ) t hs
  have hDyadicFiltration :
      ∀ t : NNReal, (⨅ n : ℕ, ℱ (dyadicRightApprox t n)) = ℱ t := by
    intro t
    exact filtration_iInf_dyadicRightApprox_eq (μ := μ) (ℱ := ℱ) t
  classical
  obtain ⟨A, hAc, hAmeas, hAcontrol⟩ :=
    existsFullMeasureDyadicControlEvent (X := X) (μ := μ) (ℱ := ℱ) hX hNullMeas
  let Xtilde : NNReal → Ω → ℝ :=
    fun t ω ↦ Function.rightLim (fun s : NNReal ↦ dyadicControlCandidate X A s ω) t
  have hcadlag : HasCadlagPaths Xtilde :=
    hasCadlagPaths_rightLimDyadicControlCandidate21_24
      (X := X)
      (A := A)
      hAcontrol
  have hmeas :
      ∀ t : NNReal, StronglyMeasurable[ℱ t] (Xtilde t) :=
    stronglyMeasurable_rightLimDyadicControlCandidate21_24
      (X := X)
      (A := A)
      (μ := μ)
      (ℱ := ℱ)
      hX
      hEX_rc
      hAc
      hAmeas
      hAcontrol
      hDyadicFiltration
  refine ⟨Xtilde, ?_, hcadlag⟩
  intro t
  -- Proof comment: the cadlag witness is now the `rightLim` regularization of the candidate.
  -- The remaining fixed-time frontier is to prove that this strict-right regularization still
  -- agrees almost surely with the original supermartingale slice.
  simpa [Xtilde] using
    (aeEq_fixedTime_of_rightLimDyadicControlCandidate21_24
      (X := X)
      (A := A)
      (μ := μ)
      (ℱ := ℱ)
      hX
      hEX_rc
      hAc
      hAmeas
      hAcontrol
      hDyadicFiltration
      t
      (hmeas t)).symm

end ProbabilityTheory

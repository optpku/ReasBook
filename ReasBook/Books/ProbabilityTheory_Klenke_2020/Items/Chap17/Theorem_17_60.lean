/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_59
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_57
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

private theorem measurable_natToFin1Real : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)) := by
  simpa using (Measurable.of_discrete : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)))

/-- View a probability law on `ℕ` as a one-dimensional law in the chapter's ambient state space
`Fin 1 → ℝ`. -/
abbrev toFin1Real (μ : ProbabilityMeasure ℕ) : ProbabilityMeasure (Fin 1 → ℝ) :=
  ProbabilityMeasure.map μ measurable_natToFin1Real.aemeasurable

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

/-- Helper for Theorem 17.60: the nat-valued embedding into `Fin 1 → ℝ` sends the tail
`Set.Ici (![k])` back to the discrete tail `Set.Ici k`. -/
private lemma natToFin1Real_preimage_Ici (k : ℕ) :
    (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)) ⁻¹' Set.Ici (![k] : Fin 1 → ℝ) = Set.Ici k := by
  -- Proof comment: in dimension `1`, the coordinatewise order on singleton vectors is just the
  -- usual order on their unique coordinates.
  ext n
  simp [Pi.le_def]

/-- Helper for Theorem 17.60: on `ℕ`, the lower tail `Set.Iic n` is the complement of the upper
tail `Set.Ici (n + 1)`. -/
private lemma natMeasure_Iic_toReal_eq_one_sub_tail
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    (μ (Set.Iic n)).toReal = 1 - (μ (Set.Ici (n + 1))).toReal := by
  have hcompl : ((Set.Iic n : Set ℕ)ᶜ) = Set.Ici (n + 1) := by
    -- Proof comment: for natural numbers, not being at most `n` is the same as being at least
    -- `n + 1`.
    ext k
    simp
  have hsplit : μ.real (Set.Iic n) + μ.real (Set.Ici (n + 1)) = 1 := by
    -- Proof comment: split the unit total mass into a measurable set and its complement.
    simpa [hcompl] using
      (show μ.real (Set.Iic n) + μ.real ((Set.Iic n : Set ℕ)ᶜ) = μ.real Set.univ from
        MeasureTheory.measureReal_add_measureReal_compl measurableSet_Iic)
  have htail : μ.real (Set.Iic n) = 1 - μ.real (Set.Ici (n + 1)) := by
    -- Proof comment: isolate the prefix mass from the complement identity.
    linarith
  simpa [Measure.real_def] using htail

/-- Helper for Theorem 17.60: the first upper tail `μ([1, ∞))` is the complement of the atom at
`0`. -/
private lemma natMeasure_tail_Ici_one_toReal (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (μ (Set.Ici 1)).toReal = 1 - (μ ({0} : Set ℕ)).toReal := by
  -- Proof comment: identify `Set.Iic 0` with `{0}` and reuse the complement formula for the
  -- first nontrivial tail.
  have hzero : (Set.Iic 0 : Set ℕ) = ({0} : Set ℕ) := by
    ext n
    simp
  have hprefix : (μ ({0} : Set ℕ)).toReal = 1 - (μ (Set.Ici 1)).toReal := by
    simpa [hzero] using natMeasure_Iic_toReal_eq_one_sub_tail (μ := μ) 0
  linarith

/-- Helper for Theorem 17.60: the zero-atom of `Bin(n, p)` equals `(1 - p)^n`. -/
private lemma binomial_apply_zero_toReal (n : ℕ) (p : I) :
    (Bin(n, p) ({0} : Set ℕ)).toReal = (1 - (p : ℝ)) ^ n := by
  -- Proof comment: specialize the singleton-mass formula for the binomial law at `0`.
  simpa using binomial_apply_singleton_toReal n 0 p

/-- Helper for Theorem 17.60: the binomial law `Bin(n, p)` has no mass above `n`. -/
private lemma binomial_apply_tail_succ_eq_zero (n : ℕ) (p : I) :
    Bin(n, p) (Set.Ici (n + 1)) = 0 := by
  have hBound : ∀ᵐ k : ℕ ∂Bin(n, p), k ≤ n := by
    -- Proof comment: the nat-valued binomial law is supported on `[0, n]`.
    simpa using
      (ProbabilityTheory.ae_le_of_hasLaw_binomial (n := n) (p := p)
        (X := id) (P := Bin(n, p)) (ProbabilityTheory.HasLaw.id (μ := Bin(n, p))))
  have hNotMem : ∀ᵐ k : ℕ ∂Bin(n, p), k ∉ Set.Ici (n + 1) := by
    -- Proof comment: every support point stays below the first impossible tail level `n + 1`.
    filter_upwards [hBound] with k hk
    simp [Set.mem_Ici]
    omega
  exact (MeasureTheory.measure_eq_zero_iff_ae_notMem).2 hNotMem

/-- Helper for Theorem 17.60: the clipped monotone staircase built from successive increments of a
sequence telescopes to the clipped value `g (min N n)`. -/
private lemma monotone_nat_truncation_eq (g : ℕ → ℝ) (N n : ℕ) :
    g 0 +
        Finset.sum (Finset.range N)
          (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0)) =
      g (min N n) := by
  induction N with
  | zero =>
      -- Proof comment: with no increments, the clipped staircase is just the initial value.
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases hNn : N < n
      · -- Proof comment: if the new index is still below `n`, the next increment is active and
        -- the telescoping sum advances from `g N` to `g (N + 1)`.
        have hmin : min N n = N := Nat.min_eq_left (Nat.le_of_lt hNn)
        have hmin' : min (N + 1) n = N + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hNn)
        have ih' :
            g 0 +
                Finset.sum (Finset.range N)
                  (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0)) =
              g N := by
          simpa [hmin] using ih
        calc
          g 0 +
              (Finset.sum (Finset.range N)
                (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0)) +
                (g (N + 1) - g N) * (if N < n then (1 : ℝ) else 0))
              = (g 0 +
                  Finset.sum (Finset.range N)
                    (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0))) +
                  (g (N + 1) - g N) * (if N < n then (1 : ℝ) else 0) := by
                    ring
          _ = g N + (g (N + 1) - g N) * (if N < n then (1 : ℝ) else 0) := by
                rw [ih']
          _ = g (N + 1) := by
                simp [hNn]
          _ = g (min (N + 1) n) := by
                simpa [hmin']
      · -- Proof comment: once `n ≤ N`, every later increment is clipped to zero, so the value
        -- stays frozen at `g n`.
        have hle : n ≤ N := Nat.le_of_not_gt hNn
        have hmin : min N n = n := Nat.min_eq_right hle
        have hmin' : min (N + 1) n = n := Nat.min_eq_right (Nat.le_trans hle (Nat.le_succ N))
        have ih' :
            g 0 +
                Finset.sum (Finset.range N)
                  (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0)) =
              g n := by
          simpa [hmin] using ih
        calc
          g 0 +
              (Finset.sum (Finset.range N)
                (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0)) +
                (g (N + 1) - g N) * (if N < n then (1 : ℝ) else 0))
              = (g 0 +
                  Finset.sum (Finset.range N)
                    (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0))) +
                  (g (N + 1) - g N) * (if N < n then (1 : ℝ) else 0) := by
                    ring
          _ = g n + (g (N + 1) - g N) * (if N < n then (1 : ℝ) else 0) := by
                rw [ih']
          _ = g n := by
                simp [hNn]
          _ = g (min (N + 1) n) := by
                simpa [hmin']

/-- Helper for Theorem 17.60: a monotone nat sequence with a finite upper bound is integrable
against any probability measure on `ℕ`. -/
private lemma integrable_of_monotone_nat_of_bddAbove
    (μ : ProbabilityMeasure ℕ) {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ n : ℕ, g n ≤ B) :
    Integrable g (μ : Measure ℕ) := by
  rcases hB with ⟨B, hB⟩
  refine Integrable.mono' (integrable_const (max |g 0| |B|)) ?_ ?_
  · simpa using (Measurable.of_discrete : Measurable g).aestronglyMeasurable
  · filter_upwards with n
    exact abs_le_max_abs_abs (hg_mono (Nat.zero_le n)) (hB n)

/-- Helper for Theorem 17.60: a single tail step is an indicator of the discrete upper tail
`Set.Ici (k + 1)`. -/
private lemma nat_tail_step_eq_indicator (c : ℝ) (k : ℕ) :
    (fun n : ℕ ↦ c * (if k < n then (1 : ℝ) else 0)) =
      (Set.Ici (k + 1)).indicator (fun _ : ℕ ↦ c) := by
  funext n
  by_cases hkn : k < n
  · simp [Set.indicator, hkn]
  · simp [Set.indicator, hkn]

/-- Helper for Theorem 17.60: each finite tail-step function is integrable under a probability
measure on `ℕ`. -/
private lemma nat_tail_step_integrable
    (μ : ProbabilityMeasure ℕ) (c : ℝ) (k : ℕ) :
    Integrable (fun n : ℕ ↦ c * (if k < n then (1 : ℝ) else 0)) (μ : Measure ℕ) := by
  rw [nat_tail_step_eq_indicator c k]
  exact (integrable_const c).indicator measurableSet_Ici

/-- Helper for Theorem 17.60: integrating one tail step recovers the corresponding upper-tail
mass. -/
private lemma nat_tail_step_integral
    (μ : ProbabilityMeasure ℕ) (c : ℝ) (k : ℕ) :
    ∫ n, c * (if k < n then (1 : ℝ) else 0) ∂(μ : Measure ℕ) =
      c * ((μ : Measure ℕ) (Set.Ici (k + 1))).toReal := by
  rw [nat_tail_step_eq_indicator c k, integral_indicator_const, Measure.real_def]
  · rw [smul_eq_mul, mul_comm]
  · exact measurableSet_Ici

/-- Helper for Theorem 17.60: if a monotone sequence on `ℕ` is bounded above, then each clipped
sequence `n ↦ g (min N n)` is integrable under any probability measure on `ℕ`. -/
private lemma integrable_nat_truncation_of_monotone_bddAbove
    (μ : ProbabilityMeasure ℕ) {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ n : ℕ, g n ≤ B) (N : ℕ) :
    Integrable (fun n : ℕ ↦ g (min N n)) (μ : Measure ℕ) := by
  rcases hB with ⟨B, hB⟩
  refine Integrable.mono' (integrable_const (max |g 0| |B|)) ?_ ?_
  · simpa using
      (Measurable.of_discrete : Measurable (fun n : ℕ ↦ g (min N n))).aestronglyMeasurable
  · filter_upwards with n
    exact abs_le_max_abs_abs (hg_mono (Nat.zero_le (min N n))) (hB (min N n))

/-- Helper for Theorem 17.60: the integral of a clipped monotone sequence is the head value plus
the finite weighted sum of upper-tail masses. -/
private lemma integral_nat_truncation_eq
    (μ : ProbabilityMeasure ℕ) (g : ℕ → ℝ) (N : ℕ) :
    ∫ n, g (min N n) ∂(μ : Measure ℕ) =
      g 0 +
        Finset.sum (Finset.range N)
          (fun k ↦ (g (k + 1) - g k) * ((μ : Measure ℕ) (Set.Ici (k + 1))).toReal) := by
  have hsumIntegrable :
      Integrable
        (fun n : ℕ ↦
          Finset.sum (Finset.range N)
            (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0)))
        (μ : Measure ℕ) := by
    -- Proof comment: the clipped staircase is a finite sum of integrable tail-step indicators.
    exact
      integrable_finset_sum (Finset.range N) fun k hk ↦
        nat_tail_step_integrable μ (g (k + 1) - g k) k
  have hrewrite :
      (fun n : ℕ ↦ g (min N n)) =ᵐ[(μ : Measure ℕ)]
        (fun n : ℕ ↦
          g 0 +
            Finset.sum (Finset.range N)
              (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0))) := by
    -- Proof comment: the pointwise clipped-value formula is exactly
    -- `monotone_nat_truncation_eq`.
    exact Filter.Eventually.of_forall fun n ↦ (monotone_nat_truncation_eq g N n).symm
  calc
    ∫ n, g (min N n) ∂(μ : Measure ℕ)
        =
          ∫ n,
            g 0 +
              Finset.sum (Finset.range N)
                (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0))
            ∂(μ : Measure ℕ) := by
              exact integral_congr_ae hrewrite
    _ =
        ∫ _ : ℕ, g 0 ∂(μ : Measure ℕ) +
          ∫ n,
            Finset.sum (Finset.range N)
              (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0))
            ∂(μ : Measure ℕ) := by
              rw [integral_add (integrable_const (g 0)) hsumIntegrable]
    _ =
        g 0 +
          ∫ n,
            Finset.sum (Finset.range N)
              (fun k ↦ (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0))
            ∂(μ : Measure ℕ) := by
              simp
    _ =
        g 0 +
          Finset.sum (Finset.range N)
            (fun k ↦
              ∫ n, (g (k + 1) - g k) * (if k < n then (1 : ℝ) else 0) ∂(μ : Measure ℕ)) := by
              rw [MeasureTheory.integral_finset_sum (Finset.range N)]
              intro k hk
              simpa using nat_tail_step_integrable μ (g (k + 1) - g k) k
    _ =
        g 0 +
          Finset.sum (Finset.range N)
            (fun k ↦ (g (k + 1) - g k) * ((μ : Measure ℕ) (Set.Ici (k + 1))).toReal) := by
              refine congrArg (fun t : ℝ => g 0 + t) ?_
              refine Finset.sum_congr rfl fun k hk ↦ ?_
              exact nat_tail_step_integral μ (g (k + 1) - g k) k

/-- Helper for Theorem 17.60: upper-tail domination on `ℕ` compares the integrals of every
bounded monotone test function. -/
private lemma integralNat_le_of_upperTail
    (μ₁ μ₂ : ProbabilityMeasure ℕ) {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ n : ℕ, g n ≤ B)
    (htail : ∀ k : ℕ, (μ₁ : Measure ℕ) (Set.Ici k) ≤ (μ₂ : Measure ℕ) (Set.Ici k)) :
    ∫ n, g n ∂(μ₁ : Measure ℕ) ≤ ∫ n, g n ∂(μ₂ : Measure ℕ) := by
  have htrunc_le :
      ∀ N : ℕ,
        ∫ n, g (min N n) ∂(μ₁ : Measure ℕ) ≤
          ∫ n, g (min N n) ∂(μ₂ : Measure ℕ) := by
    intro N
    have hsum_le :
        Finset.sum (Finset.range N)
            (fun k ↦ (g (k + 1) - g k) * ((μ₁ : Measure ℕ) (Set.Ici (k + 1))).toReal) ≤
          Finset.sum (Finset.range N)
            (fun k ↦ (g (k + 1) - g k) * ((μ₂ : Measure ℕ) (Set.Ici (k + 1))).toReal) := by
      -- Proof comment: each truncation coefficient is a nonnegative increment of `g`, so the
      -- assumed upper-tail inequalities compare the finite weighted sums termwise.
      refine Finset.sum_le_sum fun k hk ↦ ?_
      have hcoeff_nonneg : 0 ≤ g (k + 1) - g k := by
        exact sub_nonneg.mpr (hg_mono (Nat.le_succ k))
      have htail_real :
          (((μ₁ : Measure ℕ) (Set.Ici (k + 1))).toReal) ≤
            (((μ₂ : Measure ℕ) (Set.Ici (k + 1))).toReal) := by
        exact ENNReal.toReal_mono (measure_ne_top (μ₂ : Measure ℕ) (Set.Ici (k + 1)))
          (htail (k + 1))
      exact mul_le_mul_of_nonneg_left htail_real hcoeff_nonneg
    calc
      ∫ n, g (min N n) ∂(μ₁ : Measure ℕ)
          = g 0 +
              Finset.sum (Finset.range N)
                (fun k ↦ (g (k + 1) - g k) *
                  ((μ₁ : Measure ℕ) (Set.Ici (k + 1))).toReal) := by
              exact integral_nat_truncation_eq μ₁ g N
      _ ≤ g 0 +
            Finset.sum (Finset.range N)
              (fun k ↦ (g (k + 1) - g k) * ((μ₂ : Measure ℕ) (Set.Ici (k + 1))).toReal) := by
            simpa [add_comm] using add_le_add_left hsum_le (g 0)
      _ = ∫ n, g (min N n) ∂(μ₂ : Measure ℕ) := by
            symm
            exact integral_nat_truncation_eq μ₂ g N
  have htrunc_mono :
      ∀ n : ℕ, Monotone fun N : ℕ ↦ g (min N n) := by
    -- Proof comment: for fixed `n`, the clipped index `min N n` increases with the truncation
    -- level `N`.
    intro n N M hNM
    exact hg_mono (by omega)
  have htrunc_tendsto :
      ∀ n : ℕ, Filter.Tendsto (fun N : ℕ ↦ g (min N n)) Filter.atTop (nhds (g n)) := by
    -- Proof comment: once `N ≥ n`, the clipped sequence stabilizes at the terminal value `g n`.
    intro n
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.eventually_atTop.2 ?_
    exact ⟨n, fun N hN ↦ by simp [Nat.min_eq_right hN]⟩
  have hμ₁_tendsto :
      Filter.Tendsto
        (fun N : ℕ ↦ ∫ n, g (min N n) ∂(μ₁ : Measure ℕ))
        Filter.atTop
        (nhds (∫ n, g n ∂(μ₁ : Measure ℕ))) := by
    -- Proof comment: monotone convergence upgrades the finite truncation bounds to the full
    -- `μ₁`-integral.
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      (μ := (μ₁ : Measure ℕ)) (f := fun N n ↦ g (min N n)) (F := g) ?_ ?_ ?_ ?_
    · intro N
      exact integrable_nat_truncation_of_monotone_bddAbove μ₁ hg_mono hB N
    · exact integrable_of_monotone_nat_of_bddAbove μ₁ hg_mono hB
    · exact Filter.Eventually.of_forall htrunc_mono
    · exact Filter.Eventually.of_forall htrunc_tendsto
  have hμ₂_tendsto :
      Filter.Tendsto
        (fun N : ℕ ↦ ∫ n, g (min N n) ∂(μ₂ : Measure ℕ))
        Filter.atTop
        (nhds (∫ n, g n ∂(μ₂ : Measure ℕ))) := by
    -- Proof comment: the same truncation argument identifies the `μ₂`-limit.
    refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      (μ := (μ₂ : Measure ℕ)) (f := fun N n ↦ g (min N n)) (F := g) ?_ ?_ ?_ ?_
    · intro N
      exact integrable_nat_truncation_of_monotone_bddAbove μ₂ hg_mono hB N
    · exact integrable_of_monotone_nat_of_bddAbove μ₂ hg_mono hB
    · exact Filter.Eventually.of_forall htrunc_mono
    · exact Filter.Eventually.of_forall htrunc_tendsto
  -- Proof comment: all finite truncations are ordered, so the full integrals are ordered after
  -- passing to the monotone-convergence limit.
  exact le_of_tendsto_of_tendsto hμ₁_tendsto hμ₂_tendsto
    (Filter.Eventually.of_forall htrunc_le)

/-- Helper for Theorem 17.60: integrating over the embedded law `μ.toFin1Real` is the same as
integrating over `μ` after pulling the test function back along `n ↦ (![n] : Fin 1 → ℝ)`. -/
private lemma integral_toFin1Real_eq_integral_nat
    (μ : ProbabilityMeasure ℕ) {f : (Fin 1 → ℝ) → ℝ} (hf_meas : Measurable f) :
    ∫ x, f x ∂((μ.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) =
      ∫ n, f (![n] : Fin 1 → ℝ) ∂(μ : Measure ℕ) := by
  -- Proof comment: `μ.toFin1Real` is a pushforward, so the integral is the standard `integral_map`
  -- rewrite along the singleton-vector embedding.
  have hEmbedMeas : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)) := by
    simpa using
      (Measurable.of_discrete : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)))
  simpa [MeasureTheory.ProbabilityMeasure.toFin1Real] using
    (MeasureTheory.integral_map
      (μ := (μ : Measure ℕ))
      hEmbedMeas.aemeasurable
      (f := f)
      hf_meas.aestronglyMeasurable)

-- Proof sketch: in one dimension, increasing bounded measurable test functions on the embedded
-- laws are equivalent to increasing bounded measurable functions on `ℕ`; the indicator functions
-- of the upper tails `Set.Ici k` recover the textbook inequalities, and conversely the tail
-- family determines the stochastic order on laws supported on `ℕ`.
/-- For nat-valued laws embedded into `Fin 1 → ℝ`, the chapter owner `StochasticLE` is equivalent
to comparison of all upper tails `μ([k, ∞))`. -/
theorem stochasticLE_toFin1Real_iff_upper_tail (μ₁ μ₂ : ProbabilityMeasure ℕ) :
    StochasticLE μ₁.toFin1Real μ₂.toFin1Real ↔
      ∀ k : ℕ, (μ₁ : Measure ℕ) (Set.Ici k) ≤ (μ₂ : Measure ℕ) (Set.Ici k) := by
  constructor
  · intro hst k
    let s : Set (Fin 1 → ℝ) := Set.Ici (![k] : Fin 1 → ℝ)
    let tailIndicator : (Fin 1 → ℝ) → ℝ := s.indicator (fun _ ↦ (1 : ℝ))
    have hEmbedMeas : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)) := by
      simpa using
        (Measurable.of_discrete : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)))
    have htailIndicator_mono : Monotone tailIndicator := by
      -- Proof comment: the indicator of an upper tail is increasing because `Set.Ici (![k])` is
      -- itself upward closed.
      intro x y hxy
      by_cases hx : x ∈ s
      · have hy : y ∈ s := by exact le_trans hx hxy
        simp [tailIndicator, hx, hy]
      · by_cases hy : y ∈ s
        · simp [tailIndicator, hx, hy]
        · simp [tailIndicator, hx, hy]
    have htailIndicator_bdd : Bornology.IsBounded (Set.range tailIndicator) := by
      -- Proof comment: the tail indicator only takes the values `0` and `1`.
      refine (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).isBounded.subset ?_
      rintro y ⟨x, rfl⟩
      by_cases hx : x ∈ s <;> simp [tailIndicator, hx]
    have htailIndicator_meas : Measurable tailIndicator := by
      exact measurable_const.indicator measurableSet_Ici
    have hs_meas : MeasurableSet s := by
      simpa [s] using (measurableSet_Ici : MeasurableSet (Set.Ici (![k] : Fin 1 → ℝ)))
    have hIntegral :
        ∫ x, s.indicator (fun _ ↦ (1 : ℝ)) x
            ∂((μ₁.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) ≤
          ∫ x, s.indicator (fun _ ↦ (1 : ℝ)) x
            ∂((μ₂.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) := by
      simpa [tailIndicator] using hst htailIndicator_mono htailIndicator_bdd htailIndicator_meas
    have hμ₁_tail :
        (((μ₁.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) s) =
          (μ₁ : Measure ℕ) (Set.Ici k) := by
      -- Proof comment: pull the ambient tail back along the singleton-vector embedding.
      simpa [MeasureTheory.ProbabilityMeasure.toFin1Real, s, natToFin1Real_preimage_Ici] using
        (Measure.map_apply (μ := (μ₁ : Measure ℕ))
          hEmbedMeas (measurableSet_Ici : MeasurableSet s))
    have hμ₂_tail :
        (((μ₂.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) s) =
          (μ₂ : Measure ℕ) (Set.Ici k) := by
      -- Proof comment: the same pullback identifies the second embedded tail.
      simpa [MeasureTheory.ProbabilityMeasure.toFin1Real, s, natToFin1Real_preimage_Ici] using
        (Measure.map_apply (μ := (μ₂ : Measure ℕ))
          hEmbedMeas (measurableSet_Ici : MeasurableSet s))
    have hTailCompare :
        (((μ₁.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) s) ≤
          (((μ₂.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) s) := by
      -- Proof comment: integrating the indicator is exactly the corresponding tail mass.
      rw [integral_indicator_const (μ := ((μ₁.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) :
            Measure (Fin 1 → ℝ))) (1 : ℝ) hs_meas,
        integral_indicator_const (μ := ((μ₂.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) :
            Measure (Fin 1 → ℝ))) (1 : ℝ) hs_meas] at hIntegral
      simpa [Measure.real_def] using hIntegral
    rw [hμ₁_tail, hμ₂_tail] at hTailCompare
    exact hTailCompare
  · intro htail
    -- Route correction: the reverse direction now stays in explicit nat-tail normal form instead
    -- of relying on implicit `Measure.map` transport through the embedding.
    intro f hf_mono hf_bdd hf_meas
    let g : ℕ → ℝ := fun n ↦ f (![n] : Fin 1 → ℝ)
    have hsingleton_mono :
        ∀ {m n : ℕ}, m ≤ n → (![m] : Fin 1 → ℝ) ≤ (![n] : Fin 1 → ℝ) := by
      intro m n hmn i
      fin_cases i
      simpa using (show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn)
    have hg_mono : Monotone g := by
      -- Proof comment: on singleton vectors, coordinatewise monotonicity is the usual nat order.
      intro m n hmn
      exact hf_mono (hsingleton_mono hmn)
    have hB : ∃ B : ℝ, ∀ n : ℕ, g n ≤ B := by
      -- Proof comment: a bounded test function on the ambient space stays bounded after
      -- restriction to singleton vectors.
      obtain ⟨R, hR⟩ := hf_bdd.exists_norm_le
      refine ⟨R, ?_⟩
      intro n
      have hnorm : ‖g n‖ ≤ R := by
        exact hR (g n) ⟨(![n] : Fin 1 → ℝ), rfl⟩
      exact le_trans (le_abs_self (g n)) hnorm
    have hNatIntegral_le :
        ∫ n, g n ∂(μ₁ : Measure ℕ) ≤ ∫ n, g n ∂(μ₂ : Measure ℕ) := by
      -- Proof comment: the extracted nat-tail comparison turns the upper-tail assumptions into
      -- the desired integral comparison on `ℕ`.
      exact integralNat_le_of_upperTail μ₁ μ₂ hg_mono hB htail
    -- Proof comment: rewrite the ambient integrals back to the nat-valued laws and insert the
    -- integral comparison just obtained on `ℕ`.
    calc
      ∫ x, f x ∂((μ₁.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ))
          = ∫ n, g n ∂(μ₁ : Measure ℕ) := by
              simpa [g] using integral_toFin1Real_eq_integral_nat μ₁ hf_meas
      _ ≤ ∫ n, g n ∂(μ₂ : Measure ℕ) := hNatIntegral_le
      _ = ∫ x, f x ∂((μ₂.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) := by
            symm
            simpa [g] using integral_toFin1Real_eq_integral_nat μ₂ hf_meas

/-- Any stochastic-order comparison between probability laws on `ℕ` compares their upper tails at
each threshold `k`. -/
theorem StochasticLE.upper_tail_nat {μ₁ μ₂ : ProbabilityMeasure ℕ}
    (h : StochasticLE μ₁.toFin1Real μ₂.toFin1Real) (k : ℕ) :
    (μ₁ : Measure ℕ) (Set.Ici k) ≤ (μ₂ : Measure ℕ) (Set.Ici k) := by
  -- Proof comment: the forward implication of the nat-tail characterization is exactly this
  -- upper-tail comparison.
  exact (stochasticLE_toFin1Real_iff_upper_tail μ₁ μ₂).1 h k

/-- Helper for Theorem 17.60: an ordered coupling of nat-valued laws yields stochastic order after
embedding into the chapter's ambient one-dimensional space `Fin 1 → ℝ`. -/
private lemma stochasticLE_toFin1Real_of_natCoupling
    {μ₁ μ₂ : ProbabilityMeasure ℕ} {φ : ProbabilityMeasure (ℕ × ℕ)}
    (hCoupling : IsCoupling φ μ₁ μ₂)
    (hOrdered : ∀ᵐ z ∂(φ : Measure (ℕ × ℕ)), z.1 ≤ z.2) :
    StochasticLE μ₁.toFin1Real μ₂.toFin1Real := by
  intro f hf_mono hf_bdd hf_meas
  rcases hCoupling with ⟨hfst, hsnd⟩
  have hNatEmbedMeas : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)) := by
    simpa using
      (Measurable.of_discrete : Measurable (fun n : ℕ ↦ (![n] : Fin 1 → ℝ)))
  have hNatTestMeas : Measurable (fun n : ℕ ↦ f (![n] : Fin 1 → ℝ)) := by
    exact hf_meas.comp hNatEmbedMeas
  have hfstTestMeas : Measurable (fun z : ℕ × ℕ ↦ f (![z.1] : Fin 1 → ℝ)) := by
    exact hNatTestMeas.comp measurable_fst
  have hsndTestMeas : Measurable (fun z : ℕ × ℕ ↦ f (![z.2] : Fin 1 → ℝ)) := by
    exact hNatTestMeas.comp measurable_snd
  have hfstIntegrable : Integrable (fun z : ℕ × ℕ ↦ f (![z.1] : Fin 1 → ℝ))
      (φ : Measure (ℕ × ℕ)) := by
    obtain ⟨R, hR⟩ := hf_bdd.exists_norm_le
    -- Proof comment: bounded range turns the pulled-back test function into an integrable
    -- function on the coupling space.
    refine Integrable.mono' (integrable_const R) hfstTestMeas.aestronglyMeasurable ?_
    filter_upwards with z
    simpa using hR (f (![z.1] : Fin 1 → ℝ)) ⟨(![z.1] : Fin 1 → ℝ), rfl⟩
  have hsndIntegrable : Integrable (fun z : ℕ × ℕ ↦ f (![z.2] : Fin 1 → ℝ))
      (φ : Measure (ℕ × ℕ)) := by
    obtain ⟨R, hR⟩ := hf_bdd.exists_norm_le
    -- Proof comment: the same boundedness estimate controls the second coordinate pullback.
    refine Integrable.mono' (integrable_const R) hsndTestMeas.aestronglyMeasurable ?_
    filter_upwards with z
    simpa using hR (f (![z.2] : Fin 1 → ℝ)) ⟨(![z.2] : Fin 1 → ℝ), rfl⟩
  have hOrderedTest :
      ∀ᵐ z ∂(φ : Measure (ℕ × ℕ)), f (![z.1] : Fin 1 → ℝ) ≤ f (![z.2] : Fin 1 → ℝ) := by
    -- Proof comment: the nat-ordering in the coupling lifts to the coordinatewise order on the
    -- embedded singleton vectors.
    filter_upwards [hOrdered] with z hz
    exact hf_mono (by simpa [Pi.le_def] using hz)
  have hfstMap : Measure.map Prod.fst (φ : Measure (ℕ × ℕ)) = (μ₁ : Measure ℕ) := by
    simpa [Measure.fst] using hfst
  have hsndMap : Measure.map Prod.snd (φ : Measure (ℕ × ℕ)) = (μ₂ : Measure ℕ) := by
    simpa [Measure.snd] using hsnd
  -- Proof comment: rewrite both target integrals through the coupling marginals and compare the
  -- two pulled-back test functions pointwise almost everywhere.
  calc
    ∫ x, f x ∂((μ₁.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ))
        = ∫ n, f (![n] : Fin 1 → ℝ) ∂(μ₁ : Measure ℕ) :=
          integral_toFin1Real_eq_integral_nat μ₁ hf_meas
    _ = ∫ z, f (![z.1] : Fin 1 → ℝ) ∂(φ : Measure (ℕ × ℕ)) := by
          rw [← hfstMap]
          simpa using
            (MeasureTheory.integral_map
              (μ := (φ : Measure (ℕ × ℕ)))
              measurable_fst.aemeasurable
              (f := fun n : ℕ ↦ f (![n] : Fin 1 → ℝ))
              hNatTestMeas.aestronglyMeasurable)
    _ ≤ ∫ z, f (![z.2] : Fin 1 → ℝ) ∂(φ : Measure (ℕ × ℕ)) := by
          exact MeasureTheory.integral_mono_ae hfstIntegrable hsndIntegrable hOrderedTest
    _ = ∫ n, f (![n] : Fin 1 → ℝ) ∂(μ₂ : Measure ℕ) := by
          rw [← hsndMap]
          simpa using
            (MeasureTheory.integral_map
              (μ := (φ : Measure (ℕ × ℕ)))
              measurable_snd.aemeasurable
              (f := fun n : ℕ ↦ f (![n] : Fin 1 → ℝ))
              hNatTestMeas.aestronglyMeasurable).symm
    _ = ∫ x, f x ∂((μ₂.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) := by
          symm
          exact integral_toFin1Real_eq_integral_nat μ₂ hf_meas

/-- Helper for Theorem 17.60: the common-rate binomial success probability attached to `λ` and `n`
is `1 - exp (-λ / n)`. -/
private def commonRateProb (lam : NNReal) (n : ℕ) : ℝ :=
  1 - Real.exp (-(lam : ℝ) / n)

/-- Helper for Theorem 17.60: the common-rate success probability is nonnegative. -/
private lemma commonRateProb_nonneg (lam : NNReal) (n : ℕ) :
    0 ≤ commonRateProb lam n := by
  -- Proof comment: `exp x ≤ 1` for `x ≤ 0`, and here `x = -λ / n`.
  dsimp [commonRateProb]
  have hnonneg : 0 ≤ (lam : ℝ) / n := by
    exact div_nonneg lam.2 (by positivity)
  have hnonpos : -(lam : ℝ) / n ≤ 0 := by
    have hneg : -((lam : ℝ) / n) ≤ 0 := neg_nonpos.mpr hnonneg
    simpa [neg_div] using hneg
  have hexp : Real.exp (-(lam : ℝ) / n) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr hnonpos
  linarith

/-- Helper for Theorem 17.60: the common-rate success probability is at most `1`. -/
private lemma commonRateProb_le_one (lam : NNReal) (n : ℕ) :
    commonRateProb lam n ≤ 1 := by
  -- Proof comment: subtracting a nonnegative exponential term can only decrease `1`.
  dsimp [commonRateProb]
  have hexp_nonneg : 0 ≤ Real.exp (-(lam : ℝ) / n) := by positivity
  linarith

/-- Helper for Theorem 17.60: coercing the packaged common-rate probability back to `ℝ` removes
the `Real.toNNReal` wrapper. -/
private lemma commonRateProb_toNNReal_coe (lam : NNReal) (n : ℕ) :
    (((Real.toNNReal (commonRateProb lam n)) : NNReal) : ℝ) = commonRateProb lam n := by
  -- Proof comment: the common-rate success probability already lies in `[0, ∞)`.
  simp [Real.toNNReal, max_eq_left (commonRateProb_nonneg lam n)]

/-- Helper for Theorem 17.60: the common-rate success probability lies in the unit interval. -/
private lemma commonRateParameter_mem_unitInterval (lam : NNReal) (n : ℕ) :
    Set.Icc (0 : NNReal) 1 (Real.toNNReal (commonRateProb lam n)) := by
  constructor
  · positivity
  · rw [← NNReal.coe_le_coe, commonRateProb_toNNReal_coe]
    exact commonRateProb_le_one lam n

/-- Helper for Theorem 17.60: package the common-rate success probability as an element of the
unit interval `I`. -/
private def commonRateParameter (lam : NNReal) (n : ℕ) : I :=
  ⟨Real.toNNReal (commonRateProb lam n), commonRateParameter_mem_unitInterval lam n⟩

/-- Helper for Theorem 17.60: coercing `commonRateParameter λ n` to `ℝ` gives the expected
success probability `1 - exp (-λ / n)`. -/
private lemma commonRateParameter_coe (lam : NNReal) (n : ℕ) :
    ((commonRateParameter lam n : I) : ℝ) = commonRateProb lam n := by
  exact commonRateProb_toNNReal_coe lam n

/-- Helper for Theorem 17.60: the singleton mass of `poissonMeasure r` is the explicit Poisson
weight `poissonPMFReal r k`. -/
private lemma poissonMeasure_apply_singleton (r : NNReal) (k : ℕ) :
    poissonMeasure r ({k} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r k) := by
  -- Proof comment: rewrite the Poisson law as the measure attached to its canonical PMF.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) k (measurableSet_singleton k))

/-- Helper for Theorem 17.60: the one-coordinate occupied/not-occupied indicator of a Poisson
count. -/
private def poissonPositiveIndicator : ℕ → ℕ :=
  fun k ↦ if 0 < k then 1 else 0

/-- Helper for Theorem 17.60: counting the positive Poisson coordinates in a finite family. -/
private def poissonPositiveCount (n : ℕ) : (Fin n → ℕ) → ℕ :=
  fun x ↦ ∑ i, poissonPositiveIndicator (x i)

/-- Helper for Theorem 17.60: the positive-indicator map on `ℕ` is measurable. -/
private lemma measurable_poissonPositiveIndicator :
    Measurable poissonPositiveIndicator := by
  -- Proof comment: nat-valued functions are measurable on the discrete measurable space.
  simpa [poissonPositiveIndicator] using
    (Measurable.of_discrete : Measurable poissonPositiveIndicator)

/-- Helper for Theorem 17.60: the positive-count map on a finite Poisson product is measurable. -/
private lemma measurable_poissonPositiveCount (n : ℕ) :
    Measurable (poissonPositiveCount n) := by
  -- Proof comment: each coordinate indicator is measurable, and finite sums preserve
  -- measurability.
  classical
  simpa [poissonPositiveCount] using
    Finset.measurable_sum Finset.univ fun i _ ↦
      measurable_poissonPositiveIndicator.comp (measurable_pi_apply i)

/-- Helper for Theorem 17.60: the finite product law of `n` independent `Poi_r` variables. -/
private abbrev poissonCube (n : ℕ) (r : NNReal) : Measure (Fin n → ℕ) :=
  Measure.pi fun _ : Fin n ↦ poissonMeasure r

/-- Helper for Theorem 17.60: a single Poisson positivity indicator has the Bernoulli/binomial
one-trial law with success probability `1 - exp (-r)`. -/
private lemma poissonPositiveIndicator_hasLaw_binomialOne (r : NNReal) :
    HasLaw poissonPositiveIndicator (Bin(1, commonRateParameter r 1)) (poissonMeasure r) := by
  refine ⟨measurable_poissonPositiveIndicator.aemeasurable, ?_⟩
  refine Measure.ext_of_singleton fun k ↦ ?_
  by_cases hk0 : k = 0
  · subst hk0
    rw [Measure.map_apply measurable_poissonPositiveIndicator (measurableSet_singleton 0)]
    have hpreimage : poissonPositiveIndicator ⁻¹' ({0} : Set ℕ) = ({0} : Set ℕ) := by
      ext x
      simp [poissonPositiveIndicator]
    rw [hpreimage, poissonMeasure_apply_singleton]
    apply (ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
    rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, binomial_apply_singleton_toReal]
    simp [poissonPMFReal, commonRateParameter_coe, commonRateProb]
  · by_cases hk1 : k = 1
    · subst hk1
      rw [Measure.map_apply measurable_poissonPositiveIndicator (measurableSet_singleton 1)]
      have hpreimage : poissonPositiveIndicator ⁻¹' ({1} : Set ℕ) = Set.Ici 1 := by
        ext x
        simp [poissonPositiveIndicator, Nat.succ_le_iff]
      rw [hpreimage]
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      rw [natMeasure_tail_Ici_one_toReal, poissonMeasure_apply_singleton,
        binomial_apply_singleton_toReal]
      rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg]
      simp [poissonPMFReal, commonRateParameter_coe, commonRateProb]
    · have hk2 : 1 < k := by
        omega
      rw [Measure.map_apply measurable_poissonPositiveIndicator (measurableSet_singleton k)]
      have hpreimage : poissonPositiveIndicator ⁻¹' ({k} : Set ℕ) = (∅ : Set ℕ) := by
        ext x
        by_cases hx : 0 < x
        · have hk_ne_one : (1 : ℕ) ≠ k := by omega
          simp [poissonPositiveIndicator, hx, hk_ne_one]
        · have hk_ne_zero : (0 : ℕ) ≠ k := by omega
          simp [poissonPositiveIndicator, hx, hk_ne_zero]
      rw [hpreimage, measure_empty]
      rw [← ENNReal.ofReal_zero]
      apply (ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
      rw [ENNReal.toReal_ofReal (by positivity), binomial_apply_singleton_toReal]
      have hchoose : Nat.choose 1 k = 0 := Nat.choose_eq_zero_of_lt hk2
      simp [hchoose]

/-- Helper for Theorem 17.60: splitting off the zero coordinate sends the finite Poisson product
to the product of the head `Poi_r` law and the remaining `n` coordinates. -/
private lemma poissonCube_map_piFinSuccAboveZero (n : ℕ) (r : NNReal) :
    (poissonCube (n + 1) r).map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℕ) 0) =
      (poissonMeasure r).prod (poissonCube n r) := by
  -- Proof comment: this is the canonical finite-product split specialized to identical Poisson
  -- coordinate laws.
  simpa [poissonCube, Fin.zero_succAbove] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ poissonMeasure r) 0).map_eq

/-- Helper for Theorem 17.60: after splitting off the head coordinate, the positive-count map is
the head indicator plus the tail positive count. -/
private lemma poissonPositiveCountSplitSymm (n : ℕ) (r : NNReal) (u : ℕ) (x : Fin n → ℕ) :
    poissonPositiveCount (n + 1)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℕ) 0).symm (u, x)) =
      poissonPositiveIndicator u + poissonPositiveCount n x := by
  let split : (Fin (n + 1) → ℕ) ≃ᵐ ℕ × (Fin n → ℕ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℕ) 0
  have hfst : (split.symm (u, x)) 0 = u := by
    simp [split]
  have hsnd : (fun i : Fin n ↦ (split.symm (u, x)) i.succ) = x := by
    calc
      (fun i : Fin n ↦ (split.symm (u, x)) i.succ)
        = Prod.snd (split (split.symm (u, x))) := by
            funext i
            simp [split]
      _ = x := by
            exact congrArg Prod.snd (split.apply_symm_apply (u, x))
  have htail :
      ∑ i : Fin n, poissonPositiveIndicator ((split.symm (u, x)) i.succ) =
        poissonPositiveCount n x := by
    simpa [poissonPositiveCount] using
      congrArg
        (fun f : Fin n → ℕ ↦ ∑ i : Fin n, poissonPositiveIndicator (f i))
        hsnd
  -- Proof comment: split the finite sum into the zero coordinate and the successor tail.
  calc
    poissonPositiveCount (n + 1) (split.symm (u, x))
      = poissonPositiveIndicator ((split.symm (u, x)) 0) +
          ∑ i : Fin n, poissonPositiveIndicator ((split.symm (u, x)) i.succ) := by
            simp [poissonPositiveCount, Fin.sum_univ_succ]
    _ = poissonPositiveIndicator u + poissonPositiveCount n x := by
          rw [hfst, htail]

/-- Helper for Theorem 17.60: on a finite Poisson product, counting positive coordinates gives the
binomial law with success probability `1 - exp (-r)`. -/
private lemma poissonPositiveCount_hasLaw_binomial (n : ℕ) (r : NNReal) :
    HasLaw (poissonPositiveCount n) (Bin(n, commonRateParameter r 1)) (poissonCube n r) := by
  induction n with
  | zero =>
      refine ⟨(measurable_poissonPositiveCount 0).aemeasurable, ?_⟩
      rw [show poissonPositiveCount 0 = fun _ : Fin 0 → ℕ ↦ 0 by
        funext x
        simp [poissonPositiveCount]]
      simpa [binomial_zero_left] using
        (Measure.map_apply (μ := poissonCube 0 r) measurable_const (measurableSet_singleton 0))
  | succ n ih =>
      let split : (Fin (n + 1) → ℕ) ≃ᵐ ℕ × (Fin n → ℕ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℕ) 0
      have hSplit :
          HasLaw split ((poissonMeasure r).prod (poissonCube n r)) (poissonCube (n + 1) r) := by
        refine ⟨split.measurable.aemeasurable, ?_⟩
        exact poissonCube_map_piFinSuccAboveZero n r
      have hHead :
          HasLaw (fun z : ℕ × (Fin n → ℕ) ↦ poissonPositiveIndicator z.1)
            (Bin(1, commonRateParameter r 1))
            ((poissonMeasure r).prod (poissonCube n r)) := by
        -- Proof comment: under the product law, the head coordinate is still `Poi_r`.
        simpa [Function.comp] using
          HasLaw.comp (poissonPositiveIndicator_hasLaw_binomialOne r)
            ((measurePreserving_fst (μ := poissonMeasure r) (ν := poissonCube n r)).hasLaw)
      have hTail :
          HasLaw (fun z : ℕ × (Fin n → ℕ) ↦ poissonPositiveCount n z.2)
            (Bin(n, commonRateParameter r 1))
            ((poissonMeasure r).prod (poissonCube n r)) := by
        -- Proof comment: the tail coordinates keep the inductive positive-count law.
        simpa [Function.comp] using
          HasLaw.comp ih
            ((measurePreserving_snd (μ := poissonMeasure r) (ν := poissonCube n r)).hasLaw)
      have hIndep :
          (fun z : ℕ × (Fin n → ℕ) ↦ poissonPositiveIndicator z.1) ⟂ᵢ[
            (poissonMeasure r).prod (poissonCube n r)]
            (fun z : ℕ × (Fin n → ℕ) ↦ poissonPositiveCount n z.2) := by
        -- Proof comment: on the product space, the head coordinate and the tail block are
        -- independent.
        exact indepFun_prod measurable_poissonPositiveIndicator
          (measurable_poissonPositiveCount n)
      have hSum :
          HasLaw
            (fun z : ℕ × (Fin n → ℕ) ↦
              poissonPositiveIndicator z.1 + poissonPositiveCount n z.2)
            (Bin(1, commonRateParameter r 1) ∗ Bin(n, commonRateParameter r 1))
            ((poissonMeasure r).prod (poissonCube n r)) :=
        hIndep.hasLaw_add hHead hTail
      have hSplitCount :
          HasLaw
            (fun y : Fin (n + 1) → ℕ ↦
              poissonPositiveIndicator (split y).1 + poissonPositiveCount n (split y).2)
            (Bin(1, commonRateParameter r 1) ∗ Bin(n, commonRateParameter r 1))
            (poissonCube (n + 1) r) :=
        HasLaw.comp hSum hSplit
      have hCountEq :
          (fun y : Fin (n + 1) → ℕ ↦ poissonPositiveCount (n + 1) y) =ᵐ[poissonCube (n + 1) r]
            (fun y : Fin (n + 1) → ℕ ↦
              poissonPositiveIndicator (split y).1 + poissonPositiveCount n (split y).2) := by
        -- Proof comment: after rewriting through the standard split equivalence, the positive
        -- count becomes the head indicator plus the tail positive count.
        refine Filter.Eventually.of_forall fun y ↦ ?_
        calc
          poissonPositiveCount (n + 1) y
            = poissonPositiveCount (n + 1) (split.symm (split y)) := by
                rw [split.symm_apply_apply y]
          _ =
              poissonPositiveIndicator (split y).1 + poissonPositiveCount n (split y).2 := by
                simpa [split] using poissonPositiveCountSplitSymm n r (split y).1 (split y).2
      have hCountConv :
          HasLaw (poissonPositiveCount (n + 1))
            (Bin(1, commonRateParameter r 1) ∗ Bin(n, commonRateParameter r 1))
            (poissonCube (n + 1) r) :=
        hSplitCount.congr hCountEq
      refine ⟨hCountConv.aemeasurable, ?_⟩
      -- Proof comment: convolution of one Bernoulli step with the `n`-coordinate count is the
      -- standard binomial recursion.
      simpa [Nat.add_comm] using
        hCountConv.map_eq.trans
          (example_3_4_binomial_conv 1 n (commonRateParameter r 1))

/-- Helper for Theorem 17.60: the regular grid on `[0,1]` with denominator `n`. -/
private def equalGrid (n : ℕ) : Fin (n + 1) → I :=
  fun i ↦
    ⟨(i : ℝ) / n, by
      constructor
      · positivity
      · have hi : (i : ℝ) ≤ n := by
          exact_mod_cast (Nat.le_of_lt_succ i.is_lt)
        exact div_le_one_of_le₀ hi (by positivity)⟩

/-- Helper for Theorem 17.60: the regular grid starts at `0`. -/
private lemma equalGrid_zero (n : ℕ) :
    equalGrid n 0 = 0 := by
  -- Proof comment: the zeroth grid point has numerator `0`.
  ext
  simp [equalGrid]

/-- Helper for Theorem 17.60: the regular grid ends at `1` when `n ≥ 1`. -/
private lemma equalGrid_last {n : ℕ} (hn : 1 ≤ n) :
    equalGrid n (Fin.last n) = 1 := by
  -- Proof comment: the final grid point has numerator and denominator both equal to `n`.
  ext
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [equalGrid, Fin.val_last, hn0]

/-- Helper for Theorem 17.60: the regular grid is monotone. -/
private lemma equalGrid_mono (n : ℕ) : Monotone (equalGrid n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (show (i : ℝ) ≤ j by exact_mod_cast hij) (by positivity)

/-- Helper for Theorem 17.60: consecutive regular-grid points differ by `1 / n`. -/
private lemma equalGrid_sub_eq_inv {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    ((equalGrid n i.succ : I) : ℝ) - ((equalGrid n i.castSucc : I) : ℝ) = 1 / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  -- Proof comment: consecutive grid points differ by a numerator increment of exactly `1`.
  change ((i.succ : ℕ) : ℝ) / n - ((i.castSucc : ℕ) : ℝ) / n = 1 / n
  have hsucc : ((i.succ : ℕ) : ℝ) = (i.castSucc : ℕ) + 1 := by
    norm_num [Fin.succ, Fin.castSucc]
  rw [hsucc]
  field_simp [hn0]
  ring

/-- Helper for Theorem 17.60: the canonical source model combines a `Poi_λ` count with an
independent infinite sequence of uniform marks in `I`. -/
private abbrev poissonizedEqualGridMeasure (lam : NNReal) : Measure (ℕ × (ℕ → I)) :=
  (poissonMeasure lam).prod (Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I)))

/-- Helper for Theorem 17.60: the textbook marks are reindexed so that
`poissonizedEqualGridMark (n + 1)` is the `n`th coordinate of the canonical infinite product
sample. -/
private def poissonizedEqualGridMark (k : ℕ) (ω : ℕ × (ℕ → I)) : I :=
  ω.2 (k - 1)

/-- Helper for Theorem 17.60: each shifted mark coordinate is uniform on `I` in the canonical
Poisson/uniform product model. -/
private lemma poissonizedEqualGridShiftedMark_hasLaw (lam : NNReal) (n : ℕ) :
    HasLaw
      (fun ω : ℕ × (ℕ → I) ↦ poissonizedEqualGridMark (n + 1) ω)
      (volume : Measure I)
      (poissonizedEqualGridMeasure lam) := by
  -- Proof comment: first forget the Poisson count by projecting to the mark sequence, then
  -- evaluate the `n`th coordinate of the infinite uniform product.
  simpa [poissonizedEqualGridMeasure, poissonizedEqualGridMark, Function.comp] using
    HasLaw.comp
      ((measurePreserving_eval_infinitePi (fun _ : ℕ ↦ (volume : Measure I)) n).hasLaw)
      ((measurePreserving_snd
        (μ := poissonMeasure lam)
        (ν := Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I)))).hasLaw)

/-- Helper for Theorem 17.60: the shifted mark sequence is i.i.d. uniform on `I` under the
canonical Poisson/uniform product model. -/
private lemma poissonizedEqualGridShiftedMarks_isIID (lam : NNReal) :
    IsIID
      (fun n : ℕ ↦ fun ω : ℕ × (ℕ → I) ↦ poissonizedEqualGridMark (n + 1) ω)
      (poissonizedEqualGridMeasure lam) := by
  refine ⟨?_, ?_⟩
  · have hmeas :
        ∀ n : ℕ,
          AEMeasurable
            (fun ω : ℕ × (ℕ → I) ↦ poissonizedEqualGridMark (n + 1) ω)
            (poissonizedEqualGridMeasure lam) :=
      fun n ↦ (poissonizedEqualGridShiftedMark_hasLaw lam n).aemeasurable
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' hmeas]
    calc
      (poissonizedEqualGridMeasure lam).map
          (fun ω n ↦ poissonizedEqualGridMark (n + 1) ω)
          =
        (poissonizedEqualGridMeasure lam).map Prod.snd := by
          rfl
      _ = Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I)) := by
            simpa [poissonizedEqualGridMeasure] using
              (measurePreserving_snd
                (μ := poissonMeasure lam)
                (ν := Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I)))).map_eq
      _ =
        Measure.infinitePi
          (fun n : ℕ ↦
            (poissonizedEqualGridMeasure lam).map
              (fun ω : ℕ × (ℕ → I) ↦ poissonizedEqualGridMark (n + 1) ω)) := by
            congr 1
            funext n
            exact (poissonizedEqualGridShiftedMark_hasLaw lam n).map_eq.symm
  · intro i j
    -- Proof comment: every shifted coordinate has the same uniform marginal law.
    exact HasLaw.identDistrib
      (poissonizedEqualGridShiftedMark_hasLaw lam i)
      (poissonizedEqualGridShiftedMark_hasLaw lam j)

/-- Helper for Theorem 17.60: the successor-cell count vector on the equal grid has iid Poisson
coordinates with common rate `λ / n`. -/
private def equalGridSuccCounts (n : ℕ) (hn : 1 ≤ n) :
    (ℕ × (ℕ → I)) → (Fin n → ℕ) :=
  fun ω i ↦
    fullGridCount (equalGrid n) (equalGrid_last hn) Prod.fst poissonizedEqualGridMark ω i.succ

/-- Helper for Theorem 17.60: the equal-grid successor-cell count vector is exactly the iid
Poisson cube predicted by Theorem 5.35. -/
private lemma equalGridSuccCounts_hasLaw_poissonCube
    (lam : NNReal) {n : ℕ} (hn : 1 ≤ n) :
    HasLaw
      (equalGridSuccCounts n hn)
      (poissonCube n (Real.toNNReal ((lam : ℝ) / n)))
      (poissonizedEqualGridMeasure lam) := by
  have hL :
      HasLaw Prod.fst (poissonMeasure lam) (poissonizedEqualGridMeasure lam) := by
    -- Proof comment: the first coordinate of the canonical product model is the Poisson count.
    simpa [poissonizedEqualGridMeasure] using
      ((measurePreserving_fst
        (μ := poissonMeasure lam)
        (ν := Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I)))).hasLaw)
  have hLX_indep :
      IndepFun
        Prod.fst
        (fun ω : ℕ × (ℕ → I) ↦ fun m : ℕ ↦ poissonizedEqualGridMark (m + 1) ω)
        (poissonizedEqualGridMeasure lam) := by
    -- Proof comment: the Poisson count lives on the first coordinate and the entire mark process
    -- lives on the second coordinate of the product space.
    simpa [poissonizedEqualGridMark] using
      (indepFun_prod
        (X := (id : ℕ → ℕ))
        (Y := (id : (ℕ → I) → (ℕ → I)))
        (μ := poissonMeasure lam)
        (ν := Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I)))
        measurable_id
        measurable_id)
  have hX_iid :
      IsIID
        (fun m : ℕ ↦ fun ω : ℕ × (ℕ → I) ↦ poissonizedEqualGridMark (m + 1) ω)
        (poissonizedEqualGridMeasure lam) :=
    poissonizedEqualGridShiftedMarks_isIID lam
  have hX1_law :
      HasLaw
        (poissonizedEqualGridMark 1)
        (volume : Measure I)
        (poissonizedEqualGridMeasure lam) := by
    -- Proof comment: the first textbook-indexed mark is the zeroth coordinate of the uniform
    -- product sample.
    simpa using poissonizedEqualGridShiftedMark_hasLaw lam 0
  let u : Fin (n + 1) → I := equalGrid n
  have hu : Monotone u := equalGrid_mono n
  have h0 : u 0 = 0 := equalGrid_zero n
  have h1 : u (Fin.last n) = 1 := equalGrid_last hn
  have hfullLaw :
      HasLaw
        (fun ω ↦ fun i ↦ fullGridCount u h1 Prod.fst poissonizedEqualGridMark ω i)
        (Measure.pi (fun i ↦ poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 i).toNNReal)))
        (poissonizedEqualGridMeasure lam) :=
    fullGridCountHasLawPiPoisson
      (P := poissonizedEqualGridMeasure lam)
      (α := lam)
      (L := Prod.fst)
      (X := poissonizedEqualGridMark)
      (u := u)
      hu
      h0
      h1
      hL
      hLX_indep
      hX_iid
      hX1_law
  have hfullIndep :
      iIndepFun
        (fun i : Fin (n + 1) ↦ fun ω ↦ fullGridCount u h1 Prod.fst poissonizedEqualGridMark ω i)
        (poissonizedEqualGridMeasure lam) := by
    have hmeas :
        ∀ i : Fin (n + 1),
          AEMeasurable
            (fun ω ↦ fullGridCount u h1 Prod.fst poissonizedEqualGridMark ω i)
            (poissonizedEqualGridMeasure lam) :=
      fun i ↦ (measurable_pi_apply i).aemeasurable.comp_aemeasurable hfullLaw.aemeasurable
    have hcoordLaw :
        ∀ i : Fin (n + 1),
          HasLaw
            (fun ω ↦ fullGridCount u h1 Prod.fst poissonizedEqualGridMark ω i)
            (poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 i).toNNReal))
            (poissonizedEqualGridMeasure lam) := by
      intro i
      have hevalLaw :
          HasLaw
            (Function.eval i)
            (poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 i).toNNReal))
            (Measure.pi
              (fun j ↦ poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 j).toNNReal))) := by
        exact
          (measurePreserving_eval
            (fun j ↦ poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 j).toNNReal))
            i).hasLaw
      -- Proof comment: each coordinate law is read off from the product law of the whole vector.
      simpa [Function.comp] using HasLaw.comp hevalLaw hfullLaw
    have hcoordMap :
        (fun i : Fin (n + 1) ↦
          Measure.map
            (fun ω ↦ fullGridCount u h1 Prod.fst poissonizedEqualGridMark ω i)
            (poissonizedEqualGridMeasure lam))
          =
        fun i ↦ poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 i).toNNReal) := by
      funext i
      exact (hcoordLaw i).map_eq
    refine (iIndepFun_iff_map_fun_eq_pi_map hmeas).2 ?_
    simpa [hcoordMap] using hfullLaw.map_eq
  have hsuccIndep :
      iIndepFun
        (fun i : Fin n ↦ fun ω ↦ equalGridSuccCounts n hn ω i)
        (poissonizedEqualGridMeasure lam) := by
    have hsucc_injective : Function.Injective (fun i : Fin n ↦ i.succ) := by
      intro i j hij
      exact Fin.ext (Nat.succ.inj (congrArg Fin.val hij))
    -- Proof comment: the successor coordinates are a coordinate subfamily of the independent full
    -- grid-count vector.
    simpa [equalGridSuccCounts, u] using hfullIndep.precomp hsucc_injective
  have hsuccCoordLaw :
      ∀ i : Fin n,
        HasLaw
          (fun ω ↦ equalGridSuccCounts n hn ω i)
          (poissonMeasure (Real.toNNReal ((lam : ℝ) / n)))
          (poissonizedEqualGridMeasure lam) := by
    intro i
    have hevalLaw :
        HasLaw
          (fun ω ↦ fullGridCount u h1 Prod.fst poissonizedEqualGridMark ω i.succ)
          (poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 i.succ).toNNReal))
          (poissonizedEqualGridMeasure lam) := by
      have hcoordLaw :
          HasLaw
            (Function.eval i.succ)
            (poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 i.succ).toNNReal))
            (Measure.pi
              (fun j ↦ poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 j).toNNReal))) := by
        exact
          (measurePreserving_eval
            (fun j ↦ poissonMeasure (lam * (fullGridLabelPMF u hu h0 h1 j).toNNReal))
            i.succ).hasLaw
      simpa [Function.comp] using HasLaw.comp hcoordLaw hfullLaw
    have hrate :
        lam * (fullGridLabelPMF u hu h0 h1 i.succ).toNNReal =
          Real.toNNReal ((lam : ℝ) / n) := by
      apply NNReal.coe_injective
      rw [NNReal.coe_mul, fullGridLabelRateSuccEqIntervalLength u hu h0 h1 i,
        equalGrid_sub_eq_inv hn i, Real.toNNReal_of_nonneg (by positivity),
        Real.toNNReal_of_nonneg (by positivity)]
      simpa [div_eq_mul_inv]
    -- Proof comment: every successor cell has the same interval length `1 / n`, so all
    -- coordinates share the common Poisson rate `λ / n`.
    simpa [equalGridSuccCounts, u, hrate] using hevalLaw
  have hmeas :
      ∀ i : Fin n,
        AEMeasurable
          (fun ω ↦ equalGridSuccCounts n hn ω i)
          (poissonizedEqualGridMeasure lam) :=
    fun i ↦ (hsuccCoordLaw i).aemeasurable
  refine ⟨aemeasurable_pi_iff.2 hmeas, ?_⟩
  have hcoordMap :
      (fun i : Fin n ↦
        Measure.map
          (fun ω ↦ equalGridSuccCounts n hn ω i)
          (poissonizedEqualGridMeasure lam)) =
        fun _ : Fin n ↦ poissonMeasure (Real.toNNReal ((lam : ℝ) / n)) := by
    funext i
    exact (hsuccCoordLaw i).map_eq
  -- Proof comment: independence plus the common one-coordinate law upgrades to the full iid
  -- product law on the successor vector.
  simpa [poissonCube, hcoordMap] using
    (iIndepFun_iff_map_fun_eq_pi_map hmeas).1 hsuccIndep

/-- Helper for Theorem 17.60: counting the positive equal-grid successor counts recovers the
common-rate binomial law. -/
private lemma equalGridPoissonizedOccupancy_hasLaw_binomial
    (lam : NNReal) {n : ℕ} (hn : 1 ≤ n) :
    HasLaw
      (fun ω ↦ poissonPositiveCount n (equalGridSuccCounts n hn ω))
      (Bin(n, commonRateParameter lam n))
      (poissonizedEqualGridMeasure lam) := by
  let r : NNReal := Real.toNNReal ((lam : ℝ) / n)
  have hsuccLaw :
      HasLaw
        (equalGridSuccCounts n hn)
        (poissonCube n r)
        (poissonizedEqualGridMeasure lam) := by
    simpa [r] using equalGridSuccCounts_hasLaw_poissonCube lam hn
  have hcountLaw :
      HasLaw
        (poissonPositiveCount n)
        (Bin(n, commonRateParameter r 1))
        (poissonCube n r) :=
    poissonPositiveCount_hasLaw_binomial n r
  have hparam :
      commonRateParameter r 1 = commonRateParameter lam n := by
    apply Subtype.ext
    have hnonneg : 0 ≤ (lam : ℝ) / n := by positivity
    -- Proof comment: `r = λ / n`, so the one-trial common-rate parameter at rate `r` is exactly
    -- the `n`-trial common-rate parameter at rate `λ`.
    rw [commonRateParameter_coe, commonRateProb, commonRateParameter_coe, commonRateProb]
    rw [show ((r : NNReal) : ℝ) = (lam : ℝ) / n by
      simp [r, Real.toNNReal_of_nonneg hnonneg]]
    ring
  simpa [Function.comp, hparam] using HasLaw.comp hcountLaw hsuccLaw

/-- Helper for Theorem 17.60: the equal-grid successor-count vector obtained from the first `t`
marks of a deterministic mark sequence. -/
private def fixedTimeSuccCounts
    (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (marks : ℕ → I) : Fin n → ℕ :=
  equalGridSuccCounts n hn (t, marks)

/-- Helper for Theorem 17.60: the deterministic-time number of occupied equal-grid cells after the
first `t` marks. -/
private def fixedTimePositiveCount
    (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (marks : ℕ → I) : ℕ :=
  poissonPositiveCount n (fixedTimeSuccCounts n hn t marks)

/-- Helper for Theorem 17.60: each deterministic successor-cell count is the corresponding
equal-grid counting-process increment. -/
private lemma fixedTimeSuccCounts_eq_increment
    {n : ℕ} (hn : 1 ≤ n) (t : ℕ) (marks : ℕ → I) (i : Fin n) :
    fixedTimeSuccCounts n hn t marks i =
      poissonizedUniformCountingProcess
          (fun _ : Unit ↦ t)
          (fun k : ℕ ↦ fun _ : Unit ↦ marks (k - 1))
          (equalGrid n i.succ)
          () -
        poissonizedUniformCountingProcess
          (fun _ : Unit ↦ t)
          (fun k : ℕ ↦ fun _ : Unit ↦ marks (k - 1))
          (equalGrid n i.castSucc)
          () := by
  -- Proof comment: specialize the Chapter 5 increment identity to the deterministic prefix length
  -- `t` and the equal grid.
  simpa [fixedTimeSuccCounts] using
    (fullGridCountSuccEqIncrement
      (L := Prod.fst)
      (X := poissonizedEqualGridMark)
      (u := equalGrid n)
      (hu := equalGrid_mono n)
      (h1 := equalGrid_last hn)
      i
      (t, marks))

/-- Helper for Theorem 17.60: the existing Poissonized equal-grid occupancy variable is exactly
the deterministic-time occupied-cell count evaluated at the random Poisson time `ω.1`. -/
private lemma equalGridPoissonizedOccupancy_eq_fixedTimePositiveCount
    {n : ℕ} (hn : 1 ≤ n) (ω : ℕ × (ℕ → I)) :
    poissonPositiveCount n (equalGridSuccCounts n hn ω) =
      fixedTimePositiveCount n hn ω.1 ω.2 := by
  -- Proof comment: both sides are the positive-count functional applied to the same successor-cell
  -- count vector; only the deterministic-time prefix length has been made explicit.
  rfl

/-- Helper for Theorem 17.60: the zero-atom of the common-rate binomial law is exactly
`exp (-λ)`. -/
private lemma commonRateParameter_pow (lam : NNReal) {n : ℕ} (hn : 1 ≤ n) :
    (1 - ((commonRateParameter lam n : I) : ℝ)) ^ n = Real.exp (-(lam : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := by
    exact_mod_cast hn
  -- Proof comment: the factor `1 - q_n` is `exp (-λ / n)`, and the `n`th power collapses the
  -- exponent back to `-λ`.
  rw [commonRateParameter_coe, commonRateProb]
  rw [show 1 - (1 - Real.exp (-(lam : ℝ) / n)) = Real.exp (-(lam : ℝ) / n) by ring]
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [hn_pos.ne']

/-- Helper for Theorem 17.60: normalizing `p ∈ (0, 1)` by its zero-atom recovers `p` as the
common-rate parameter at level `n`. -/
private lemma commonRateParameter_self_eq
    (n : ℕ) (p : I) (hn : 1 ≤ n) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    commonRateParameter (Real.toNNReal (-(n : ℝ) * Real.log (1 - (p : ℝ)))) n = p := by
  apply Subtype.ext
  have harg_pos : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  have hlog_nonpos : Real.log (1 - (p : ℝ)) ≤ 0 := by
    exact Real.log_nonpos harg_pos.le (by linarith)
  have hcore_nonneg : 0 ≤ -(n : ℝ) * Real.log (1 - (p : ℝ)) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hn_pos : (0 : ℝ) < n := by
    exact_mod_cast hn
  -- Proof comment: substituting `λ = -n log (1 - p)` turns `1 - exp (-λ / n)` into
  -- `1 - exp (log (1 - p)) = p`.
  rw [commonRateParameter_coe, commonRateProb]
  rw [show (((Real.toNNReal (-(n : ℝ) * Real.log (1 - (p : ℝ)))) : NNReal) : ℝ) =
      -(n : ℝ) * Real.log (1 - (p : ℝ)) by
      simpa using
        congrArg (fun x : NNReal ↦ (x : ℝ)) (Real.toNNReal_of_nonneg hcore_nonneg)]
  let L : ℝ := Real.log (1 - (p : ℝ))
  have hdiv : -((-((n : ℝ))) * L) / n = L := by
    calc
      -((-((n : ℝ))) * L) / n = ((n : ℝ) * L) / n := by ring
      _ = L := by
            field_simp [hn_pos.ne']
  rw [show -((-((n : ℝ))) * Real.log (1 - (p : ℝ))) / n = Real.log (1 - (p : ℝ)) by
    simpa [L] using hdiv]
  rw [Real.exp_log harg_pos]
  ring

/-- Helper for Theorem 17.60: the power condition determines a common-rate parameter `q₂` at the
larger trial count `n₂`, and that normalized parameter still lies below `p₂`. -/
private lemma commonRateParameter_le_of_powCondition
    (n₁ n₂ : ℕ) (p₁ p₂ : I) (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    (hp₁₀ : 0 < (p₁ : ℝ)) (hp₁₁ : (p₁ : ℝ) < 1)
    (hpow : (1 - (p₁ : ℝ)) ^ n₁ ≥ (1 - (p₂ : ℝ)) ^ n₂) :
    commonRateParameter (Real.toNNReal (-(n₁ : ℝ) * Real.log (1 - (p₁ : ℝ)))) n₂ ≤ p₂ := by
  let lam : NNReal := Real.toNNReal (-(n₁ : ℝ) * Real.log (1 - (p₁ : ℝ)))
  let q₂ : I := commonRateParameter lam n₂
  have hqpow :
      (1 - (q₂ : ℝ)) ^ n₂ = (1 - (p₁ : ℝ)) ^ n₁ := by
    -- Proof comment: both the `n₂`-parameter `q₂` and the original `p₁` share the same
    -- normalized zero-atom `exp (-λ)`.
    calc
      (1 - (q₂ : ℝ)) ^ n₂ = Real.exp (-(lam : ℝ)) := commonRateParameter_pow lam hn₂
      _ = (1 - ((commonRateParameter lam n₁ : I) : ℝ)) ^ n₁ :=
            (commonRateParameter_pow lam hn₁).symm
      _ = (1 - (p₁ : ℝ)) ^ n₁ := by
            rw [show commonRateParameter lam n₁ = p₁ by
              simpa [lam] using commonRateParameter_self_eq n₁ p₁ hn₁ hp₁₀ hp₁₁]
  have hpow' :
      (1 - (p₂ : ℝ)) ^ n₂ ≤ (1 - (q₂ : ℝ)) ^ n₂ := by
    calc
      (1 - (p₂ : ℝ)) ^ n₂ ≤ (1 - (p₁ : ℝ)) ^ n₁ := hpow
      _ = (1 - (q₂ : ℝ)) ^ n₂ := hqpow.symm
  have hq_nonneg : 0 ≤ 1 - (q₂ : ℝ) := by
    rw [show 1 - (q₂ : ℝ) = Real.exp (-(lam : ℝ) / n₂) by
      rw [commonRateParameter_coe, commonRateProb]
      ring]
    positivity
  have hbase :
      1 - (p₂ : ℝ) ≤ 1 - (q₂ : ℝ) := by
    exact
      le_of_pow_le_pow_left₀
        (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn₂)) hq_nonneg hpow'
  -- Proof comment: compare the complementary probabilities and then move back to the success
  -- parameters.
  change (q₂ : ℝ) ≤ (p₂ : ℝ)
  nlinarith

/-- Helper for Theorem 17.60: the finite prefix of equal-grid labels obtained from a deterministic
mark tuple. -/
private def prefixLabelTuple
    (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (y : Fin t → I) : Fin t → Fin (n + 1) :=
  fun j ↦ fullGridLabel (equalGrid n) (equalGrid_last hn) (y j)

/-- Helper for Theorem 17.60: the occupied successor labels in a finite deterministic mark tuple. -/
private def prefixOccupiedLabels
    (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (y : Fin t → I) : Finset (Fin (n + 1)) :=
  (Finset.univ.image (prefixLabelTuple n hn t y)).erase 0

/-- Helper for Theorem 17.60: the number of occupied equal-grid cells in a finite deterministic
mark tuple. -/
private def prefixPositiveCount
    (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (y : Fin t → I) : ℕ :=
  poissonPositiveCount n
    (fun i : Fin n ↦
      Theorem535Local.multinomialCount
        (fun j : Fin t ↦ fun z : Fin t → Fin (n + 1) ↦ z j)
        (prefixLabelTuple n hn t y)
        i.succ)

/-- Helper for Theorem 17.60: the finite equal-grid label tuple is measurable on the finite cube
`I^t`. -/
private lemma measurable_prefixLabelTuple
    (n : ℕ) (hn : 1 ≤ n) (t : ℕ) :
    Measurable (prefixLabelTuple n hn t) := by
  -- Proof comment: each coordinate is evaluation at `j` followed by the measurable equal-grid
  -- label map.
  refine measurable_pi_lambda _ ?_
  intro j
  exact
    (measurable_fullGridLabel (equalGrid n) (equalGrid_mono n) (equalGrid_zero n)
      (equalGrid_last hn)).comp (measurable_pi_apply j)

/-- Helper for Theorem 17.60: the finite occupied-cell count is measurable on `I^t`. -/
private lemma measurable_prefixPositiveCount
    (n : ℕ) (hn : 1 ≤ n) (t : ℕ) :
    Measurable (prefixPositiveCount n hn t) := by
  let countLabels : (Fin t → Fin (n + 1)) → ℕ :=
    fun z ↦
      poissonPositiveCount n
        (fun i : Fin n ↦
          Theorem535Local.multinomialCount
            (fun j : Fin t ↦ fun z' : Fin t → Fin (n + 1) ↦ z' j)
            z
            i.succ)
  have hCountMeas : Measurable countLabels := measurable_of_finite _
  -- Proof comment: the count is a deterministic finite-state functional of the measurable label
  -- tuple.
  simpa [prefixPositiveCount, prefixLabelTuple, countLabels] using
    hCountMeas.comp (measurable_prefixLabelTuple n hn t)

/-- Helper for Theorem 17.60: a multinomial count is positive exactly when the corresponding label
occurs in the sample word. -/
private lemma multinomialCount_pos_iff_mem_image
    {m t : ℕ} (x : Fin t → Fin m) (i : Fin m) :
    0 <
        Theorem535Local.multinomialCount
          (fun j : Fin t ↦ fun y : Fin t → Fin m ↦ y j) x i ↔
      i ∈ Finset.univ.image x := by
  -- Proof comment: positivity of the histogram entry means that some coordinate equals `i`,
  -- which is exactly the image-membership condition.
  constructor
  · intro hi
    rw [Theorem535Local.multinomialCount] at hi
    rcases Finset.card_pos.mp hi with ⟨j, hj⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨j, -, hj⟩
    rw [Theorem535Local.multinomialCount]
    refine Finset.card_pos.mpr ?_
    refine ⟨j, ?_⟩
    simp [hj]

/-- Helper for Theorem 17.60: counting positive successor histogram entries agrees with counting
the occupied successor labels directly. -/
private lemma poissonPositiveCount_multinomial_eq_prefixOccupiedLabels_card
    (n t : ℕ) (x : Fin t → Fin (n + 1)) :
    poissonPositiveCount n
        (fun i : Fin n ↦
          Theorem535Local.multinomialCount
            (fun j : Fin t ↦ fun y : Fin t → Fin (n + 1) ↦ y j) x
            i.succ) =
      (((Finset.univ.image x).erase 0).card) := by
  calc
    poissonPositiveCount n
        (fun i : Fin n ↦
          Theorem535Local.multinomialCount
            (fun j : Fin t ↦ fun y : Fin t → Fin (n + 1) ↦ y j) x
            i.succ)
        =
      ∑ i : Fin n, if i.succ ∈ Finset.univ.image x then 1 else 0 := by
          -- Proof comment: each successor contributes exactly when it appears in the sampled
          -- word.
          simp [poissonPositiveCount, poissonPositiveIndicator, multinomialCount_pos_iff_mem_image]
    _ = (((Finset.univ.image x).erase 0).card) := by
          have hmap :
              Finset.map (Fin.succEmb n)
                  (Finset.univ.filter
                    fun i : Fin n => i.succ ∈ Finset.univ.image x)
                =
                ((Finset.univ.image x).erase 0) := by
            ext a
            constructor
            · intro ha
              rcases Finset.mem_map.mp ha with ⟨i, hi, rfl⟩
              simp at hi
              simp [hi, Fin.succ_ne_zero]
            · intro ha
              have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
              rcases Fin.exists_succ_eq_of_ne_zero ha0 with ⟨i, rfl⟩
              have himage : i.succ ∈ Finset.univ.image x :=
                (Finset.mem_erase.mp ha).2
              have hiFilter :
                  i ∈
                    Finset.univ.filter
                      (fun j : Fin n => j.succ ∈ Finset.univ.image x) := by
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, himage⟩
              refine Finset.mem_map.mpr ?_
              exact ⟨i, hiFilter, rfl⟩
          have hcard :
              (((Finset.univ.image x).erase 0).card) =
                ∑ i : Fin n, if i.succ ∈ Finset.univ.image x then 1 else 0 := by
            calc
              (((Finset.univ.image x).erase 0).card)
                  = (Finset.univ.filter fun i : Fin n => i.succ ∈ Finset.univ.image x).card := by
                      rw [← hmap, Finset.card_map]
              _ = ∑ i : Fin n, if i.succ ∈ Finset.univ.image x then 1 else 0 := by
                      rw [Finset.card_eq_sum_ones]
                      simp
          exact hcard.symm

/-- Helper for Theorem 17.60: the histogram-based finite-prefix occupied-cell count is exactly the
cardinality of the occupied successor-label set. -/
private lemma prefixPositiveCount_eq_prefixOccupiedLabels_card
    (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (y : Fin t → I) :
    prefixPositiveCount n hn t y = (prefixOccupiedLabels n hn t y).card := by
  -- Proof comment: each positive successor histogram entry records exactly one occupied
  -- successor label.
  unfold prefixPositiveCount prefixOccupiedLabels prefixLabelTuple
  simpa using
    poissonPositiveCount_multinomial_eq_prefixOccupiedLabels_card n t
      (fun j : Fin t ↦ fullGridLabel (equalGrid n) (equalGrid_last hn) (y j))

/-- Helper for Theorem 17.60: the deterministic-time occupied-box count depends only on the first
`t` marks, viewed as a finite tuple in `I^t`. -/
private lemma fixedTimePositiveCount_eq_prefixPositiveCount
    {n : ℕ} (hn : 1 ≤ n) (t : ℕ) (marks : ℕ → I) :
    fixedTimePositiveCount n hn t marks =
      prefixPositiveCount n hn t (fun j : Fin t ↦ marks j) := by
  let prefixTuple : Fin t → I := fun j ↦ marks j
  have hcounts :
      ∀ i : Fin n,
        fixedTimeSuccCounts n hn t marks i =
          Theorem535Local.multinomialCount
            (fun j : Fin t ↦
              fun y : Fin t → Fin (n + 1) ↦ y j)
            (prefixLabelTuple n hn t prefixTuple)
            i.succ := by
    intro i
    have hfull :
        fullGridCount (equalGrid n) (equalGrid_last hn) Prod.fst poissonizedEqualGridMark
            (t, marks) =
          Theorem535Local.multinomialCount
            (fun j : Fin t ↦
              fun ω' : Fin t → Fin (n + 1) ↦ ω' j)
            (prefixLabelTuple n hn t prefixTuple) := by
      -- Proof comment: once the deterministic length is fixed to `t`, the Chapter 5 full-grid
      -- count is exactly the histogram of the first `t` equal-grid labels.
      simpa [prefixLabelTuple, prefixTuple, poissonizedEqualGridMark] using
        (fullGridCount_eq_multinomialCount_of_length_eq
          (L := Prod.fst)
          (X := poissonizedEqualGridMark)
          (u := equalGrid n)
          (h1 := equalGrid_last hn)
          (ω := (t, marks))
          rfl)
    exact congrArg (fun v : Fin (n + 1) → ℕ ↦ v i.succ) hfull
  -- Proof comment: rewrite the deterministic successor histogram as a finite label histogram and
  -- then count the occupied successor labels.
  unfold fixedTimePositiveCount prefixPositiveCount
  exact congrArg (poissonPositiveCount n) (funext hcounts)

/-- Helper for Theorem 17.60: the first `t` coordinates of the infinite uniform product already
have the finite product law `uniformCube t`. -/
private lemma infiniteUniformPrefix_hasLaw_uniformCube (t : ℕ) :
    HasLaw
      (fun marks : ℕ → I ↦ fun j : Fin t ↦ marks j)
      (uniformCube t)
      (Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))) := by
  let P : Measure (ℕ → I) := Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))
  have hAllIndep :
      iIndepFun (fun j : ℕ ↦ fun marks : ℕ → I ↦ marks j) P := by
    simpa [P] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun _ : ℕ ↦ (volume : Measure I))
        (X := fun _ x ↦ x)
        (fun _ ↦ measurable_id))
  have hPrefixIndep :
      iIndepFun (fun j : Fin t ↦ fun marks : ℕ → I ↦ marks j) P :=
    hAllIndep.precomp Fin.val_injective
  have hCoordLaw :
      ∀ j : Fin t, HasLaw (fun marks : ℕ → I ↦ marks j) (volume : Measure I) P := by
    intro j
    simpa [P] using
      ((measurePreserving_eval_infinitePi (fun _ : ℕ ↦ (volume : Measure I)) (j : ℕ)).hasLaw)
  have hmeas :
      ∀ j : Fin t, AEMeasurable (fun marks : ℕ → I ↦ marks j) P :=
    fun j ↦ (hCoordLaw j).aemeasurable
  refine ⟨aemeasurable_pi_iff.2 hmeas, ?_⟩
  have hcoordMap :
      (fun j : Fin t ↦ Measure.map (fun marks : ℕ → I ↦ marks j) P) =
        fun _ : Fin t ↦ (volume : Measure I) := by
    funext j
    exact (hCoordLaw j).map_eq
  -- Proof comment: independence of the first `t` coordinates identifies the joint law with the
  -- product unit-interval law.
  simpa [uniformCube, hcoordMap] using
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map hmeas).1 hPrefixIndep

/-- Helper for Theorem 17.60: at deterministic time `t`, the infinite-product occupancy count has
the same law as the finite-prefix occupancy count on `uniformCube t`. -/
private lemma fixedTimePositiveCount_hasLaw_prefixPositiveCount
    {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    HasLaw
      (fun marks : ℕ → I ↦ fixedTimePositiveCount n hn t marks)
      (Measure.map (prefixPositiveCount n hn t) (uniformCube t))
      (Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))) := by
  have hPrefix :
      HasLaw
        (fun marks : ℕ → I ↦ fun j : Fin t ↦ marks j)
        (uniformCube t)
        (Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))) :=
    infiniteUniformPrefix_hasLaw_uniformCube t
  have hCountLaw :
      HasLaw
        (prefixPositiveCount n hn t)
        (Measure.map (prefixPositiveCount n hn t) (uniformCube t))
        (uniformCube t) := by
    refine ⟨(measurable_prefixPositiveCount n hn t).aemeasurable, ?_⟩
    rfl
  -- Proof comment: the deterministic-time count is exactly the finite-prefix count pulled back
  -- along the prefix map.
  simpa [Function.comp, fixedTimePositiveCount_eq_prefixPositiveCount hn t] using
    HasLaw.comp hCountLaw hPrefix

/-- Helper for Theorem 17.60: after splitting off the last coordinate from `I^(t+1)`, the second
component is exactly the `Fin.castSucc` prefix. -/
private theorem piFinSuccAboveLast_snd_eq_castSucc {t : ℕ} :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I) (Fin.last t) =
      fun z : Fin (t + 1) → I ↦ fun i : Fin t ↦ z i.castSucc := by
  funext z i
  -- Proof comment: for `Fin.last`, `succAbove` reduces to `Fin.castSucc`, so the second
  -- component is the whole prefix tuple.
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]

/-- Helper for Theorem 17.60: splitting off the last coordinate sends `uniformCube (t + 1)` to
the product of the fresh uniform mark and the prefix cube `uniformCube t`. -/
private lemma uniformCube_map_piFinSuccAboveLast (t : ℕ) :
    (uniformCube (t + 1)).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I) (Fin.last t)) =
      (volume : Measure I).prod (uniformCube t) := by
  -- Proof comment: this is the standard finite-product factorization at the last coordinate.
  simpa [uniformCube, Fin.succAbove_last] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (t + 1) ↦ (volume : Measure I))
      (Fin.last t)).map_eq

/-- Helper for Theorem 17.60: the deterministic one-step upper-tail kernel for the occupied-box
count with `n` boxes. -/
private def occupancyTailKernel (n l k : ℕ) : ℝ :=
  if k + 1 < l then 0 else if l ≤ k then 1 else 1 - (k : ℝ) / n

/-- Helper for Theorem 17.60: the deterministic occupied-box count always stays within the number
of boxes. -/
private lemma fixedTimePositiveCount_le_boxes
    {n : ℕ} (hn : 1 ≤ n) (t : ℕ) (marks : ℕ → I) :
    fixedTimePositiveCount n hn t marks ≤ n := by
  -- Proof comment: the occupied-box count is a sum of `n` many `0/1` indicators, so it can never
  -- exceed the number of summands.
  dsimp [fixedTimePositiveCount, poissonPositiveCount, poissonPositiveIndicator]
  calc
    ∑ i : Fin n, ite (0 < fixedTimeSuccCounts n hn t marks i) 1 0 ≤ ∑ _i : Fin n, (1 : ℕ) := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      split_ifs <;> omega
    _ = n := by
      simp

/-- Helper for Theorem 17.60: for a fixed box number `n`, the textbook tail kernel is monotone in
the occupied count as long as the states stay in `{0, …, n}`. -/
private lemma occupancyTailKernel_monotoneInCount
    {n l k₁ k₂ : ℕ} (hn : 1 ≤ n) (hk : k₁ ≤ k₂) (hk₂n : k₂ ≤ n) :
    occupancyTailKernel n l k₁ ≤ occupancyTailKernel n l k₂ := by
  by_cases hlk₁ : l ≤ k₁
  · have hlk₂ : l ≤ k₂ := le_trans hlk₁ hk
    have hk₁l : ¬ k₁ + 1 < l := by
      omega
    have hk₂l : ¬ k₂ + 1 < l := by
      omega
    -- Proof comment: once the threshold is already below the current state, both kernel values
    -- are identically `1`.
    simp [occupancyTailKernel, hk₁l, hk₂l, hlk₁, hlk₂]
  · by_cases hk₂l : k₂ + 1 < l
    · have hk₁l : k₁ + 1 < l := by
        omega
      -- Proof comment: if the threshold is still above the larger state plus one, both upper-tail
      -- probabilities vanish.
      simp [occupancyTailKernel, hk₁l, hk₂l]
    · by_cases hlk₂ : l ≤ k₂
      · by_cases hk₁l : k₁ + 1 < l
        · -- Proof comment: the smaller state is still too low to reach the threshold in one step,
          -- while the larger state has already crossed it.
          simp [occupancyTailKernel, hk₁l, hk₂l, hlk₁, hlk₂]
        · have hdiv_nonneg : 0 ≤ (k₁ : ℝ) / n := by
            positivity
          -- Proof comment: the only remaining left-hand case is `l = k₁ + 1`, where the kernel
          -- value is `1 - k₁ / n`, and this is bounded above by `1`.
          simp [occupancyTailKernel, hk₁l, hk₂l, hlk₁, hlk₂]
          linarith
      · have hlEq : l = k₂ + 1 := by
          omega
        by_cases hk₁l : k₁ + 1 < l
        · have hn_pos : (0 : ℝ) < n := by
            exact_mod_cast hn
          have hdiv_le_one : ((k₂ : ℝ) / n : ℝ) ≤ 1 := by
            have hk₂n' : (k₂ : ℝ) ≤ n := by
              exact_mod_cast hk₂n
            exact (div_le_iff₀ hn_pos).2 (by simpa using hk₂n')
          have hkStrict : k₁ < k₂ := by
            omega
          -- Proof comment: here the smaller state is still below the threshold, so the left
          -- kernel is `0`, while the right kernel is the nonnegative one-step value
          -- `1 - k₂ / n`.
          simp [occupancyTailKernel, hk₁l, hk₂l, hlk₁, hlk₂, hlEq, hkStrict]
          exact hdiv_le_one
        · have hkEq : k₁ = k₂ := by
            omega
          -- Proof comment: if both states straddle the same threshold `l = k + 1`, the two
          -- kernel values agree.
          subst hkEq
          simp [occupancyTailKernel, hk₁l, hk₂l, hlk₁, hlk₂]

/-- Helper for Theorem 17.60: for a fixed occupied count `k`, the textbook tail kernel is
monotone in the number of boxes. -/
private lemma occupancyTailKernel_monotoneInBoxes
    {n₁ n₂ l k : ℕ} (hn₁ : 1 ≤ n₁) (hn₁₂ : n₁ ≤ n₂) :
    occupancyTailKernel n₁ l k ≤ occupancyTailKernel n₂ l k := by
  by_cases hklt : k + 1 < l
  · have hlk : ¬ l ≤ k := by
      omega
    -- Proof comment: if `l` lies strictly above `k + 1`, both one-step upper tails vanish.
    simp [occupancyTailKernel, hklt, hlk]
  · by_cases hlk : l ≤ k
    · -- Proof comment: if the current state already meets the threshold, both one-step upper
      -- tails equal `1`.
      simp [occupancyTailKernel, hklt, hlk]
    · have hlEq : l = k + 1 := by
        omega
      have hn₁_pos : (0 : ℝ) < n₁ := by
        exact_mod_cast hn₁
      have hn₂_pos : (0 : ℝ) < n₂ := by
        exact lt_of_lt_of_le hn₁_pos (by exact_mod_cast hn₁₂)
      have hinv : ((n₂ : ℝ)⁻¹) ≤ (n₁ : ℝ)⁻¹ := by
        simpa [one_div] using (one_div_le_one_div_of_le hn₁_pos (by exact_mod_cast hn₁₂))
      have hdiv : ((k : ℝ) / n₂ : ℝ) ≤ (k : ℝ) / n₁ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [show 0 ≤ (k : ℝ) by positivity, hinv]
      -- Proof comment: in the only nontrivial case `l = k + 1`, enlarging the number of boxes
      -- decreases the threshold `k / n` and therefore increases the chance of a jump.
      simp [occupancyTailKernel, hklt, hlk, hlEq]
      linarith

/-- Helper for Theorem 17.60: once the threshold `l` stays within `{0, …, n}`, the textbook
tail kernel is globally monotone in the occupied count. -/
private lemma occupancyTailKernel_monotoneInCount_of_le
    {n l : ℕ} (hn : 1 ≤ n) (hl : l ≤ n) :
    Monotone (occupancyTailKernel n l) := by
  intro k₁ k₂ hk
  by_cases hk₂n : k₂ ≤ n
  · -- Proof comment: inside the valid state space, the earlier monotonicity lemma applies
    -- directly.
    exact occupancyTailKernel_monotoneInCount hn hk hk₂n
  · have hk₂_gt : n < k₂ := lt_of_not_ge hk₂n
    have hlk₂ : l ≤ k₂ := le_trans hl (Nat.le_of_lt hk₂_gt)
    have hk₂l : ¬ k₂ + 1 < l := by
      omega
    have hk₂_top : occupancyTailKernel n l k₂ = 1 := by
      simp [occupancyTailKernel, hk₂l, hlk₂]
    have hk₁_le_one : occupancyTailKernel n l k₁ ≤ 1 := by
      by_cases hk₁l : k₁ + 1 < l
      · have hlk₁ : ¬ l ≤ k₁ := by
          omega
        simp [occupancyTailKernel, hk₁l, hlk₁]
      · by_cases hlk₁ : l ≤ k₁
        · simp [occupancyTailKernel, hk₁l, hlk₁]
        · have hdiv_nonneg : 0 ≤ (k₁ : ℝ) / n := by
            positivity
          -- Proof comment: the only remaining branch is `l = k₁ + 1`, where the kernel equals
          -- `1 - k₁ / n`.
          simp [occupancyTailKernel, hk₁l, hlk₁]
          linarith
    simpa [hk₂_top] using hk₁_le_one

/-- Helper for Theorem 17.60: one occupied-box update can be driven by a fresh uniform mark by
comparing it with the threshold `k / n` attached to the current count `k`. -/
private def occupancyStep (n k : ℕ) (u : I) : ℕ :=
  k + if (k : ℝ) / n < (u : ℝ) then 1 else 0

/-- Helper for Theorem 17.60: if the second chain starts from at least as many occupied boxes and
has at least as many total boxes, then a common uniform update preserves the order. -/
private lemma occupancyStep_mono (u : I) {n₁ n₂ k₁ k₂ : ℕ}
    (hk : k₁ ≤ k₂) (hn : n₁ ≤ n₂) (hn₁ : 1 ≤ n₁) :
    occupancyStep n₁ k₁ u ≤ occupancyStep n₂ k₂ u := by
  by_cases hleft : ((k₁ : ℝ) / n₁ : ℝ) < (u : ℝ)
  · by_cases hkStrict : k₁ < k₂
    · have hbase :
          k₂ ≤ occupancyStep n₂ k₂ u := by
        -- Proof comment: every one-step update is either the current count or that count plus
        -- one, so the right chain always stays above its current state.
        dsimp [occupancyStep]
        split_ifs <;> omega
      have hk1 : k₁ + 1 ≤ k₂ := Nat.succ_le_of_lt hkStrict
      -- Proof comment: if the left chain jumps while the right chain already starts strictly
      -- higher, the order is immediate.
      dsimp [occupancyStep]
      simp [hleft]
      exact le_trans hk1 hbase
    · have hkEq : k₁ = k₂ := le_antisymm hk (Nat.le_of_not_gt hkStrict)
      subst hkEq
      have hn₁' : (0 : ℝ) < n₁ := by
        exact_mod_cast hn₁
      have hn' : (n₁ : ℝ) ≤ n₂ := by
        exact_mod_cast hn
      have hright : ((k₁ : ℝ) / n₂ : ℝ) < (u : ℝ) := by
        have hinv : ((n₂ : ℝ)⁻¹) ≤ (n₁ : ℝ)⁻¹ := by
          simpa [one_div] using (one_div_le_one_div_of_le hn₁' hn')
        have hdiv : ((k₁ : ℝ) / n₂ : ℝ) ≤ (k₁ : ℝ) / n₁ := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          nlinarith [show 0 ≤ (k₁ : ℝ) by positivity, hinv]
        -- Proof comment: when the occupied counts agree, the larger box count lowers the update
        -- threshold and forces the right chain to jump whenever the left chain does.
        exact lt_of_le_of_lt hdiv hleft
      dsimp [occupancyStep]
      simp [hleft, hright]
  · have hbase :
        k₂ ≤ occupancyStep n₂ k₂ u := by
      -- Proof comment: even without a jump on the left, the right chain never drops below its
      -- current state.
      dsimp [occupancyStep]
      split_ifs <;> omega
    dsimp [occupancyStep]
    simp [hleft]
    exact le_trans hk hbase

/-- Helper for Theorem 17.60: iterating the common-uniform update yields an abstract occupied-box
chain whose pathwise order is monotone in the number of boxes. -/
private def occupancyChain (n : ℕ) : ℕ → (ℕ → I) → ℕ
  | 0, _ => 0
  | t + 1, marks => occupancyStep n (occupancyChain n t marks) (marks t)

/-- Helper for Theorem 17.60: under a common sequence of uniform marks, the abstract occupied-box
chains for `n₁` and `n₂` remain ordered at every deterministic time when `n₁ ≤ n₂`. -/
private lemma occupancyChain_mono {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) (hn₁ : 1 ≤ n₁) :
    ∀ t marks, occupancyChain n₁ t marks ≤ occupancyChain n₂ t marks
  | 0, marks => by
      -- Proof comment: both chains start from the empty occupancy state.
      simp [occupancyChain]
  | t + 1, marks => by
      have hprev : occupancyChain n₁ t marks ≤ occupancyChain n₂ t marks :=
        occupancyChain_mono hn hn₁ t marks
      -- Proof comment: apply the one-step monotonicity to the ordered predecessor states.
      simpa [occupancyChain] using occupancyStep_mono (u := marks t) hprev hn hn₁

/-- Helper for Theorem 17.60: splitting off the last coordinate from `I^(t+1)` and rebuilding it
again is exactly `Fin.snoc`. -/
private lemma piFinSuccAboveLast_symm_eq_snoc {t : ℕ} (u : I) (y : Fin t → I) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I) (Fin.last t)).symm (u, y)) =
      Fin.snoc y u := by
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · -- Proof comment: on the prefix coordinates, the inverse split recovers the original tail
    -- tuple.
    simp [Fin.snoc, MeasurableEquiv.piFinSuccAbove]
  · -- Proof comment: on the final coordinate, the inverse split reinserts the fresh mark `u`.
    simp [Fin.snoc, MeasurableEquiv.piFinSuccAbove]

/-- Helper for Theorem 17.60: appending a fresh mark updates the occupied successor-label set by
inserting the new equal-grid label and then erasing `0`. -/
private lemma prefixOccupiedLabels_succ_eq_insert
    {n t : ℕ} (hn : 1 ≤ n) (u : I) (y : Fin t → I) :
    prefixOccupiedLabels n hn (t + 1)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I) (Fin.last t)).symm (u, y)) =
        (insert (fullGridLabel (equalGrid n) (equalGrid_last hn) u)
          (prefixOccupiedLabels n hn t y)).erase 0 := by
  let lbl : Fin (n + 1) := fullGridLabel (equalGrid n) (equalGrid_last hn) u
  have hsnoc :
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I) (Fin.last t)).symm (u, y)) =
        Fin.snoc y u :=
    piFinSuccAboveLast_symm_eq_snoc u y
  have htuple :
      prefixLabelTuple n hn (t + 1) (Fin.snoc y u) =
        Fin.snoc (prefixLabelTuple n hn t y) lbl := by
    -- Proof comment: the equal-grid label map is applied coordinatewise, so it commutes with
    -- appending the last mark.
    simpa [prefixLabelTuple, lbl] using
      (Fin.comp_snoc (fullGridLabel (equalGrid n) (equalGrid_last hn)) y u)
  have himage :
      Finset.univ.image (Fin.snoc (prefixLabelTuple n hn t y) lbl) =
        insert lbl (Finset.univ.image (prefixLabelTuple n hn t y)) := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨i, -, hi⟩
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact Finset.mem_insert_of_mem <|
          Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by simpa [Fin.snoc] using hi⟩
      · exact Finset.mem_insert.mpr <| Or.inl (by simpa [Fin.snoc, lbl] using hi.symm)
    · intro ha
      rcases Finset.mem_insert.mp ha with ha | ha
      · exact Finset.mem_image.mpr ⟨Fin.last t, Finset.mem_univ _, by simpa [Fin.snoc, lbl] using ha.symm⟩
      · rcases Finset.mem_image.mp ha with ⟨j, -, hj⟩
        exact Finset.mem_image.mpr ⟨j.castSucc, Finset.mem_univ _, by simpa [Fin.snoc] using hj⟩
  rw [hsnoc]
  unfold prefixOccupiedLabels
  rw [htuple, himage]
  by_cases hlbl : lbl = 0
  · -- Proof comment: if the fresh mark hits the zero-label atom, erasing `0` leaves the old
    -- occupied successor-label set unchanged.
    rw [hlbl]
    simpa [lbl, hlbl]
  · -- Proof comment: otherwise, erasing `0` commutes with inserting the nonzero fresh label.
    rw [Finset.erase_insert_of_ne hlbl, Finset.erase_insert_of_ne hlbl]
    simp

/-- Helper for Theorem 17.60: after appending one fresh mark, the occupied-box count is the
cardinality of the updated occupied successor-label set. -/
private lemma prefixPositiveCount_succ_eq_insert_card
    {n t : ℕ} (hn : 1 ≤ n) (u : I) (y : Fin t → I) :
    prefixPositiveCount n hn (t + 1)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I) (Fin.last t)).symm (u, y)) =
        ((insert (fullGridLabel (equalGrid n) (equalGrid_last hn) u)
          (prefixOccupiedLabels n hn t y)).erase 0).card := by
  -- Proof comment: combine the histogram-to-occupied-label bridge with the set-update formula.
  rw [prefixPositiveCount_eq_prefixOccupiedLabels_card]
  exact congrArg Finset.card (prefixOccupiedLabels_succ_eq_insert (hn := hn) u y)

/-- Helper for Theorem 17.60: after one fresh mark, the occupied-box count either stays at the
current value or jumps by one depending on whether the new equal-grid label is already occupied
(or is the zero label). -/
private lemma prefixPositiveCount_succ_eq_stepCases
    {n t : ℕ} (hn : 1 ≤ n) (u : I) (y : Fin t → I) :
    prefixPositiveCount n hn (t + 1)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I) (Fin.last t)).symm (u, y)) =
        if fullGridLabel (equalGrid n) (equalGrid_last hn) u ∈
            insert 0 (prefixOccupiedLabels n hn t y) then
          prefixPositiveCount n hn t y
        else
          prefixPositiveCount n hn t y + 1 := by
  let S : Finset (Fin (n + 1)) := prefixOccupiedLabels n hn t y
  let lbl : Fin (n + 1) := fullGridLabel (equalGrid n) (equalGrid_last hn) u
  have hzeroS : (0 : Fin (n + 1)) ∉ S := by
    simp [S, prefixOccupiedLabels]
  have hcardS : S.card = prefixPositiveCount n hn t y := by
    simpa [S] using (prefixPositiveCount_eq_prefixOccupiedLabels_card n hn t y).symm
  rw [prefixPositiveCount_succ_eq_insert_card (hn := hn)]
  by_cases hmem : lbl ∈ insert 0 S
  · have hcard :
        ((insert lbl S).erase 0).card = prefixPositiveCount n hn t y := by
      rcases Finset.mem_insert.mp hmem with hlbl0 | hlblS
      · simpa [hlbl0, hzeroS, hcardS]
      · have hlbl0 : lbl ≠ 0 := by
          intro hEq
          exact hzeroS (hEq ▸ hlblS)
        rw [Finset.insert_eq_of_mem hlblS, Finset.erase_eq_self.mpr hzeroS]
        simpa [hcardS]
    simpa [lbl, S, hmem] using hcard
  · have hlbl0 : lbl ≠ 0 := by
      intro hEq
      exact hmem (Finset.mem_insert.mpr (Or.inl hEq))
    have hlblS : lbl ∉ S := by
      intro hlblS
      exact hmem (Finset.mem_insert.mpr (Or.inr hlblS))
    have hcard :
        ((insert lbl S).erase 0).card = prefixPositiveCount n hn t y + 1 := by
      rw [Finset.erase_insert_of_ne hlbl0, Finset.erase_eq_self.mpr hzeroS,
        Finset.card_insert_of_notMem hlblS]
      simpa [hcardS]
    simpa [lbl, S, hmem] using hcard

/-- Helper for Theorem 17.60: every nonzero equal-grid label has mass `1 / n` under the
pushforward of the uniform law on `I`. -/
private lemma equalGridLabelPMF_apply_nonzero_toReal
    {n : ℕ} (hn : 1 ≤ n) {a : Fin (n + 1)} (ha0 : a ≠ 0) :
    (fullGridLabelPMF (equalGrid n) (equalGrid_mono n) (equalGrid_zero n) (equalGrid_last hn) a).toReal =
      1 / n := by
  rcases Fin.exists_succ_eq_of_ne_zero ha0 with ⟨i, rfl⟩
  rw [fullGridLabel_toPMF_apply_succ (equalGrid n) (equalGrid_mono n) (equalGrid_zero n)
    (equalGrid_last hn) i]
  rw [unitInterval.volume_Ioc]
  rw [ENNReal.toReal_ofReal]
  · simpa [equalGrid_sub_eq_inv hn i]
  · exact sub_nonneg.mpr (show (equalGrid n i.castSucc : ℝ) ≤ equalGrid n i.succ by
      exact equalGrid_mono n (Fin.castSucc_le_succ i))

/-- Helper for Theorem 17.60: the occupied successor-label set with `k` elements carries total
equal-grid label mass `k / n`. -/
private lemma equalGridLabelMeasure_insert_zero_prefixOccupiedLabels_toReal
    {n t : ℕ} (hn : 1 ≤ n) (y : Fin t → I) :
    (((volume : Measure I).map (fullGridLabel (equalGrid n) (equalGrid_last hn))
        ((insert 0 (prefixOccupiedLabels n hn t y) : Finset (Fin (n + 1))) :
          Set (Fin (n + 1)))).toReal) =
      (prefixPositiveCount n hn t y : ℝ) / n := by
  let p : PMF (Fin (n + 1)) :=
    fullGridLabelPMF (equalGrid n) (equalGrid_mono n) (equalGrid_zero n) (equalGrid_last hn)
  have hmap :
      (volume : Measure I).map (fullGridLabel (equalGrid n) (equalGrid_last hn)) = p.toMeasure := by
    simpa [p, fullGridLabelPMF, Measure.toPMF_toMeasure]
  have hzeroS : (0 : Fin (n + 1)) ∉ prefixOccupiedLabels n hn t y := by
    simp [prefixOccupiedLabels]
  rw [hmap, PMF.toMeasure_apply_finset, ENNReal.toReal_sum]
  · rw [Finset.sum_insert hzeroS]
    simp [p, fullGridLabel_toPMF_apply_zero]
    have hconst :
        ∀ a ∈ prefixOccupiedLabels n hn t y, (p a).toReal = 1 / n := by
      intro a ha
      exact equalGridLabelPMF_apply_nonzero_toReal hn (by
        intro hEq
        exact hzeroS (hEq ▸ ha))
    rw [Finset.sum_congr rfl hconst]
    simp [nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
      prefixPositiveCount_eq_prefixOccupiedLabels_card]
  · intro a ha
    exact p.apply_ne_top a

/-- Helper for Theorem 17.60: a finite-prefix occupied-box count never exceeds the number of
available boxes. -/
private lemma prefixPositiveCount_le_boxes
    {n t : ℕ} (hn : 1 ≤ n) (y : Fin t → I) :
    prefixPositiveCount n hn t y ≤ n := by
  rw [prefixPositiveCount_eq_prefixOccupiedLabels_card]
  have hsubset :
      prefixOccupiedLabels n hn t y ⊆ (Finset.univ.erase (0 : Fin (n + 1))) := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, Finset.mem_univ _⟩
  calc
    (prefixOccupiedLabels n hn t y).card ≤ (Finset.univ.erase (0 : Fin (n + 1))).card :=
      Finset.card_le_card hsubset
    _ = n := by
      simp

/-- Helper for Theorem 17.60: the expected value of one occupied-box update against a nat-valued
test function. -/
private def occupancyStepExpectation (n : ℕ) (g : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∫ u, g (occupancyStep n k u) ∂(volume : Measure I)

/-- Helper for Theorem 17.60: on the unit interval, the complement of a measurable event has
`toReal` mass `1 - μ(A)`. -/
private lemma unitInterval_measure_compl_toReal {s : Set I} (hs : MeasurableSet s) :
    (((volume : Measure I) sᶜ)).toReal = 1 - (((volume : Measure I) s)).toReal := by
  have hsplit :
      (((volume : Measure I) s).toReal) + (((volume : Measure I) sᶜ).toReal) = 1 := by
    -- Proof comment: split the unit total mass on `I` into a measurable set and its complement.
    simpa [Measure.real_def] using
      (show (volume : Measure I).real s + (volume : Measure I).real sᶜ =
          (volume : Measure I).real Set.univ from
        MeasureTheory.measureReal_add_measureReal_compl hs)
  linarith

/-- Helper for Theorem 17.60: one occupied-box update has the explicit two-point affine
expectation from the textbook kernel. -/
private lemma occupancyStepExpectation_eq_affine
    {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) (g : ℕ → ℝ) :
    occupancyStepExpectation n g k =
      ((k : ℝ) / n) * g k + (1 - (k : ℝ) / n) * g (k + 1) := by
  have hn_pos : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hk_nonneg : 0 ≤ (k : ℝ) / n := by
    positivity
  have hk_le_one : (k : ℝ) / n ≤ 1 := by
    have hk' : (k : ℝ) ≤ n := by
      exact_mod_cast hk
    exact div_le_one_of_le₀ hk' (by positivity)
  let x : I := ⟨(k : ℝ) / n, ⟨hk_nonneg, hk_le_one⟩⟩
  have hrewrite :
      (fun u : I ↦ g (occupancyStep n k u)) =
        (Set.Iic x).indicator (fun _ : I ↦ g k) +
          (Set.Ioi x).indicator (fun _ : I ↦ g (k + 1)) := by
    funext u
    by_cases hxu : x < u
    · have hku : (k : ℝ) / n < (u : ℝ) := by
        simpa [x] using hxu
      simp [Set.indicator, occupancyStep, hxu, hku, not_le_of_gt hxu]
    · have hux : u ≤ x := le_of_not_gt hxu
      have hku : ¬ (k : ℝ) / n < (u : ℝ) := by
        exact not_lt_of_ge (by simpa [x] using hux)
      simp [Set.indicator, occupancyStep, hxu, hux, hku]
  have hleft :
      Integrable ((Set.Iic x).indicator (fun _ : I ↦ g k)) (volume : Measure I) := by
    exact (integrable_const (g k)).indicator measurableSet_Iic
  have hright :
      Integrable ((Set.Ioi x).indicator (fun _ : I ↦ g (k + 1))) (volume : Measure I) := by
    exact (integrable_const (g (k + 1))).indicator measurableSet_Ioi
  have hIic :
      (((volume : Measure I) (Set.Iic x)).toReal) = (k : ℝ) / n := by
    rw [unitInterval.volume_Iic x]
    simpa [x] using (ENNReal.toReal_ofReal hk_nonneg)
  have hIoi :
      (((volume : Measure I) (Set.Ioi x)).toReal) = 1 - (k : ℝ) / n := by
    rw [unitInterval.volume_Ioi x]
    have hx_nonneg : 0 ≤ 1 - (x : ℝ) := by
      have := x.2.2
      linarith
    simpa [x] using (ENNReal.toReal_ofReal hx_nonneg)
  -- Proof comment: rewrite the update as the disjoint union of the stay and jump regions, then
  -- evaluate those region masses explicitly on `I`.
  calc
    occupancyStepExpectation n g k
        = ∫ u, (Set.Iic x).indicator (fun _ : I ↦ g k) u +
            (Set.Ioi x).indicator (fun _ : I ↦ g (k + 1)) u ∂(volume : Measure I) := by
              unfold occupancyStepExpectation
              exact integral_congr_ae <| Filter.Eventually.of_forall fun u ↦ by
                simpa [hrewrite] using congrArg (fun h : I → ℝ ↦ h u) hrewrite
    _ =
        ∫ u, (Set.Iic x).indicator (fun _ : I ↦ g k) u ∂(volume : Measure I) +
          ∫ u, (Set.Ioi x).indicator (fun _ : I ↦ g (k + 1)) u ∂(volume : Measure I) := by
            rw [integral_add hleft hright]
    _ = (((volume : Measure I) (Set.Iic x)).toReal) * g k +
          (((volume : Measure I) (Set.Ioi x)).toReal) * g (k + 1) := by
            rw [integral_indicator_const, integral_indicator_const]
            · simp [Measure.real_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
            · exact measurableSet_Ioi
            · exact measurableSet_Iic
    _ = ((k : ℝ) / n) * g k + (1 - (k : ℝ) / n) * g (k + 1) := by
          rw [hIic, hIoi]

/-- Helper for Theorem 17.60: a monotone nat-valued test function with a finite upper bound stays
integrable after one occupied-box update. -/
private lemma integrable_occupancyStepValue
    (n k : ℕ) {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ m : ℕ, g m ≤ B) :
    Integrable (fun u : I ↦ g (occupancyStep n k u)) (volume : Measure I) := by
  rcases hB with ⟨B, hB⟩
  -- Proof comment: `occupancyStep n k` is nat-valued, so measurability is automatic, and the
  -- monotonicity of `g` bounds the pullback between `g 0` and the global upper bound `B`.
  have hmeas :
      Measurable (fun u : I ↦ g (occupancyStep n k u)) := by
    have hpiece :
        Measurable (fun u : I ↦
          if (k : ℝ) / n < (u : ℝ) then g (k + 1) else g k) := by
      refine Measurable.piecewise
        (measurableSet_lt measurable_const measurable_subtype_coe)
        measurable_const measurable_const
    convert hpiece using 1
    ext u
    by_cases hu : (k : ℝ) / n < (u : ℝ)
    · simp [occupancyStep, hu]
    · simp [occupancyStep, hu]
  refine Integrable.mono' (integrable_const (max |g 0| |B|)) ?_ ?_
  · exact hmeas.aestronglyMeasurable
  · filter_upwards with u
    exact abs_le_max_abs_abs (hg_mono (Nat.zero_le _)) (hB _)

/-- Helper for Theorem 17.60: if the current occupied count increases, then every monotone test
function sees a larger one-step expected value. -/
private lemma occupancyStepExpectation_monotoneInCount
    {n : ℕ} (hn : 1 ≤ n) {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ m : ℕ, g m ≤ B) :
    Monotone (occupancyStepExpectation n g) := by
  intro k₁ k₂ hk
  -- Proof comment: the common-uniform one-step update is pointwise monotone in the current count,
  -- so integrating the monotone test function preserves the order.
  refine MeasureTheory.integral_mono_ae
    (integrable_occupancyStepValue n k₁ hg_mono hB)
    (integrable_occupancyStepValue n k₂ hg_mono hB) ?_
  filter_upwards with u
  exact hg_mono (occupancyStep_mono (u := u) hk le_rfl hn)

/-- Helper for Theorem 17.60: enlarging the number of boxes increases the one-step expected value
of every monotone occupied-count test function. -/
private lemma occupancyStepExpectation_monotoneInBoxes
    {n₁ n₂ k : ℕ} (hn₁ : 1 ≤ n₁) (hn₁₂ : n₁ ≤ n₂)
    {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ m : ℕ, g m ≤ B) :
    occupancyStepExpectation n₁ g k ≤ occupancyStepExpectation n₂ g k := by
  -- Proof comment: with the same occupied count and fresh mark, increasing the total number of
  -- boxes lowers the jump threshold and therefore increases the updated count pointwise.
  refine MeasureTheory.integral_mono_ae
    (integrable_occupancyStepValue n₁ k hg_mono hB)
    (integrable_occupancyStepValue n₂ k hg_mono hB) ?_
  filter_upwards with u
  exact hg_mono (occupancyStep_mono (u := u) (show k ≤ k by rfl) hn₁₂ hn₁)

/-- Helper for Theorem 17.60: the one-step expected-value transform of a bounded monotone nat
test function is again bounded above. -/
private lemma occupancyStepExpectation_bddAbove
    (n : ℕ) {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ m : ℕ, g m ≤ B) :
    ∃ B : ℝ, ∀ k : ℕ, occupancyStepExpectation n g k ≤ B := by
  rcases hB with ⟨B, hB⟩
  refine ⟨B, fun k ↦ ?_⟩
  -- Proof comment: each one-step pullback stays below the constant upper bound `B`, so the
  -- corresponding expectation is also bounded by `B`.
  have hle :
      ∫ u, g (occupancyStep n k u) ∂(volume : Measure I) ≤
        ∫ _u : I, B ∂(volume : Measure I) := by
    refine MeasureTheory.integral_mono_ae
      (integrable_occupancyStepValue n k hg_mono ⟨B, hB⟩)
      (integrable_const B) ?_
    exact Filter.Eventually.of_forall fun u ↦ hB (occupancyStep n k u)
  simpa [occupancyStepExpectation] using hle

/-- Helper for Theorem 17.60: a bounded monotone nat test function remains integrable after
precomposing with a finite-prefix occupied-box count. -/
private lemma integrable_prefixPositiveCountValue
    {n t : ℕ} (hn : 1 ≤ n) {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ m : ℕ, g m ≤ B) :
    Integrable (fun y : Fin t → I ↦ g (prefixPositiveCount n hn t y)) (uniformCube t) := by
  rcases hB with ⟨B, hB⟩
  -- Proof comment: `prefixPositiveCount` is measurable and nat-valued, so the same monotone
  -- boundedness estimate as in the one-step case gives integrability on the finite cube.
  refine Integrable.mono' (integrable_const (max |g 0| |B|)) ?_ ?_
  · exact
      (((Measurable.of_discrete : Measurable g).comp
        (measurable_prefixPositiveCount n hn t)).aestronglyMeasurable)
  · filter_upwards with y
    exact abs_le_max_abs_abs (hg_mono (Nat.zero_le _)) (hB _)

/-- Helper for Theorem 17.60: for a fixed occupied-prefix configuration, integrating a monotone
nat-valued test function over one fresh mark is exactly the abstract one-step occupied-box
expectation. -/
private lemma prefixPositiveCount_succ_integral_eq_occupancyStepExpectation
    {n t : ℕ} (hn : 1 ≤ n) (g : ℕ → ℝ) (y : Fin t → I) :
    ∫ u : I,
        g (prefixPositiveCount n hn (t + 1)
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
            (Fin.last t)).symm (u, y))) ∂(volume : Measure I)
      =
        occupancyStepExpectation n g (prefixPositiveCount n hn t y) := by
  let k := prefixPositiveCount n hn t y
  let lbl : I → Fin (n + 1) := fullGridLabel (equalGrid n) (equalGrid_last hn)
  let S : Set (Fin (n + 1)) :=
    ((insert 0 (prefixOccupiedLabels n hn t y) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
  let A : Set I := lbl ⁻¹' S
  have hA_meas : MeasurableSet A := by
    -- Proof comment: the occupied-label event is the preimage of a finite subset under the
    -- measurable equal-grid label map.
    simpa [A] using
      (measurable_fullGridLabel (equalGrid n) (equalGrid_mono n) (equalGrid_zero n)
        (equalGrid_last hn)) (by simp [S])
  have hk : k ≤ n := by
    -- Proof comment: the current occupied count is bounded by the total number of boxes.
    simpa [k] using prefixPositiveCount_le_boxes (hn := hn) y
  have hA_mass :
      (((volume : Measure I) A).toReal) = (k : ℝ) / n := by
    have hmap :
        ((volume : Measure I).map lbl) S = (volume : Measure I) A := by
      rw [Measure.map_apply (μ := (volume : Measure I)) (f := lbl)
        (measurable_fullGridLabel (equalGrid n) (equalGrid_mono n) (equalGrid_zero n)
          (equalGrid_last hn)) (by simp [S])]
    rw [← hmap]
    simpa [A, S, lbl, k] using
      equalGridLabelMeasure_insert_zero_prefixOccupiedLabels_toReal (hn := hn) y
  have hrewrite :
      (fun u : I ↦
        g (prefixPositiveCount n hn (t + 1)
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
            (Fin.last t)).symm (u, y)))) =
        A.indicator (fun _ : I ↦ g k) +
          Aᶜ.indicator (fun _ : I ↦ g (k + 1)) := by
    funext u
    by_cases hmem : lbl u ∈ S
    · have hstep :=
        prefixPositiveCount_succ_eq_stepCases (hn := hn) (u := u) (y := y)
      have huA : u ∈ A := by
        simpa [A, S, lbl] using hmem
      have hmem' :
          fullGridLabel (equalGrid n) (equalGrid_last hn) u ∈
            insert 0 (prefixOccupiedLabels n hn t y) := by
        simpa [S, lbl] using hmem
      have hval :
          prefixPositiveCount n hn (t + 1)
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
              (Fin.last t)).symm (u, y)) = k := by
        simpa [k, hmem'] using hstep
      simpa [Set.indicator, huA, piFinSuccAboveLast_symm_eq_snoc] using congrArg g hval
    · have hstep :=
        prefixPositiveCount_succ_eq_stepCases (hn := hn) (u := u) (y := y)
      have huA : u ∉ A := by
        simpa [A, S, lbl] using hmem
      have hmem' :
          fullGridLabel (equalGrid n) (equalGrid_last hn) u ∉
            insert 0 (prefixOccupiedLabels n hn t y) := by
        simpa [S, lbl] using hmem
      have hval :
          prefixPositiveCount n hn (t + 1)
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
              (Fin.last t)).symm (u, y)) = k + 1 := by
        simpa [k, hmem'] using hstep
      simpa [Set.indicator, huA, piFinSuccAboveLast_symm_eq_snoc] using congrArg g hval
  have hleft :
      Integrable (A.indicator (fun _ : I ↦ g k)) (volume : Measure I) := by
    exact (integrable_const (g k)).indicator hA_meas
  have hright :
      Integrable (Aᶜ.indicator (fun _ : I ↦ g (k + 1))) (volume : Measure I) := by
    exact (integrable_const (g (k + 1))).indicator hA_meas.compl
  -- Proof comment: the concrete fresh-mark update and the abstract occupancy step have the same
  -- two-point mixture weights `k / n` and `1 - k / n`.
  calc
    ∫ u : I,
        g (prefixPositiveCount n hn (t + 1)
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
            (Fin.last t)).symm (u, y))) ∂(volume : Measure I)
        =
          ∫ u,
            A.indicator (fun _ : I ↦ g k) u +
              Aᶜ.indicator (fun _ : I ↦ g (k + 1)) u
            ∂(volume : Measure I) := by
              exact integral_congr_ae <| Filter.Eventually.of_forall fun u ↦ by
                simpa [hrewrite] using congrArg (fun h : I → ℝ ↦ h u) hrewrite
    _ =
        ∫ u, A.indicator (fun _ : I ↦ g k) u ∂(volume : Measure I) +
          ∫ u, Aᶜ.indicator (fun _ : I ↦ g (k + 1)) u ∂(volume : Measure I) := by
            rw [integral_add hleft hright]
    _ = (((volume : Measure I) A).toReal) * g k +
          (((volume : Measure I) Aᶜ).toReal) * g (k + 1) := by
            rw [integral_indicator_const, integral_indicator_const]
            · simp [Measure.real_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
            · exact hA_meas.compl
            · exact hA_meas
    _ = ((k : ℝ) / n) * g k + (1 - (k : ℝ) / n) * g (k + 1) := by
          rw [hA_mass, unitInterval_measure_compl_toReal hA_meas, hA_mass]
    _ = occupancyStepExpectation n g (prefixPositiveCount n hn t y) := by
          simpa [k] using (occupancyStepExpectation_eq_affine (hn := hn) (hk := hk) g).symm

/-- Helper for Theorem 17.60: for a fixed occupied-prefix configuration, adding one fresh uniform
mark gives the textbook one-step upper-tail kernel. -/
private lemma prefixPositiveCount_succ_upperTailKernel_toReal
    {n t : ℕ} (hn : 1 ≤ n) (l : ℕ) (y : Fin t → I) :
    (((Measure.map
          (fun u : I ↦
            prefixPositiveCount n hn (t + 1)
              ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
                (Fin.last t)).symm (u, y)))
          (volume : Measure I))
        (Set.Ici l)).toReal) =
      occupancyTailKernel n l (prefixPositiveCount n hn t y) := by
  let k := prefixPositiveCount n hn t y
  let X : I → ℕ := fun u ↦
    prefixPositiveCount n hn (t + 1)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
        (Fin.last t)).symm (u, y))
  let g : ℕ → ℝ := fun m ↦ if l ≤ m then 1 else 0
  have hsymm_snoc :
      (fun u : I ↦
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
          (Fin.last t)).symm (u, y)) =
        fun u : I ↦ @Fin.snoc t (fun _ : Fin (t + 1) ↦ I) y u := by
    funext u
    simpa using piFinSuccAboveLast_symm_eq_snoc u y
  have hsnoc_meas :
      Measurable (fun u : I ↦ @Fin.snoc t (fun _ : Fin (t + 1) ↦ I) y u) := by
    refine measurable_pi_lambda _ ?_
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simpa [Fin.snoc] using (measurable_const : Measurable fun _u : I ↦ y j)
    · simpa [Fin.snoc] using (measurable_id : Measurable fun u : I ↦ u)
  have hX_meas : AEMeasurable X (volume : Measure I) := by
    exact (measurable_prefixPositiveCount n hn (t + 1)).aemeasurable.comp_measurable
      (hsymm_snoc ▸ hsnoc_meas)
  have hg_meas : Measurable g := by
    simpa using (Measurable.of_discrete : Measurable g)
  have hk : k ≤ n := by
    simpa [k] using prefixPositiveCount_le_boxes (hn := hn) y
  have hTailIntegral :
      ∫ m, g m ∂(Measure.map X (volume : Measure I)) =
        (((Measure.map X (volume : Measure I)) (Set.Ici l)).toReal) := by
    simpa [g, Set.indicator, Measure.real_def] using
      (integral_indicator_const (μ := Measure.map X (volume : Measure I))
        (1 : ℝ) measurableSet_Ici)
  -- Proof comment: turn the upper tail into the indicator test `g`, identify the resulting
  -- integral with the one-step expectation, and then evaluate the three kernel cases.
  calc
    (((Measure.map X (volume : Measure I)) (Set.Ici l)).toReal)
        = ∫ m, g m ∂(Measure.map X (volume : Measure I)) := by
            symm
            exact hTailIntegral
    _ = ∫ u : I, g (X u) ∂(volume : Measure I) := by
          simpa [X] using
            (MeasureTheory.integral_map (μ := (volume : Measure I)) hX_meas
              (f := g) hg_meas.aestronglyMeasurable)
    _ = occupancyStepExpectation n g (prefixPositiveCount n hn t y) := by
          simpa [X] using
            prefixPositiveCount_succ_integral_eq_occupancyStepExpectation (hn := hn) g y
    _ = ((k : ℝ) / n) * g k + (1 - (k : ℝ) / n) * g (k + 1) := by
          simpa [k] using (occupancyStepExpectation_eq_affine (hn := hn) (hk := hk) g)
    _ = occupancyTailKernel n l k := by
          by_cases hkl : k + 1 < l
          · have hnk : ¬ l ≤ k := by omega
            simp [g, occupancyTailKernel, hkl, hnk]
          · by_cases hlk : l ≤ k
            · have hlk' : l ≤ k + 1 := le_trans hlk (Nat.le_succ k)
              simp [g, occupancyTailKernel, hkl, hlk, hlk']
            · have hlEq : l = k + 1 := by omega
              simp [g, occupancyTailKernel, hkl, hlk, hlEq]
    _ = occupancyTailKernel n l (prefixPositiveCount n hn t y) := by
          simp [k]

/-- Helper for Theorem 17.60: splitting off the last coordinate turns the deterministic-time
occupied-box integral into the one-step occupied-box expectation applied to the prefix count. -/
private lemma prefixPositiveCount_succ_integral_splitLast
    {n t : ℕ} (hn : 1 ≤ n) {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ m : ℕ, g m ≤ B) :
    ∫ z, g (prefixPositiveCount n hn (t + 1) z) ∂(uniformCube (t + 1)) =
      ∫ y, ∫ u : I,
        g (prefixPositiveCount n hn (t + 1)
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
            (Fin.last t)).symm (u, y))) ∂(volume : Measure I) ∂(uniformCube t) := by
  let e : (Fin (t + 1) → I) ≃ᵐ I × (Fin t → I) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I) (Fin.last t)
  let h : I × (Fin t → I) → ℝ := fun p ↦
    g (prefixPositiveCount n hn (t + 1) (e.symm p))
  have hCubeInt :
      Integrable (fun z : Fin (t + 1) → I ↦ g (prefixPositiveCount n hn (t + 1) z))
        (uniformCube (t + 1)) := by
    exact integrable_prefixPositiveCountValue (hn := hn) hg_mono hB
  have hCubeInt' : Integrable (h ∘ e) (uniformCube (t + 1)) := by
    convert hCubeInt using 1
    ext z
    simp [h]
  have hMapInt : Integrable h (Measure.map e (uniformCube (t + 1))) := by
    exact (integrable_map_equiv e h).2 hCubeInt'
  have hProdInt : Integrable h ((volume : Measure I).prod (uniformCube t)) := by
    rw [← uniformCube_map_piFinSuccAboveLast (t := t)]
    exact hMapInt
  -- Route correction: normalize the cube split once at the integral level, so the main
  -- recursion no longer has to push raw `Measure.map` and `piFinSuccAbove` transport terms.
  calc
    ∫ z, g (prefixPositiveCount n hn (t + 1) z) ∂(uniformCube (t + 1))
        = ∫ p, h p ∂(Measure.map e (uniformCube (t + 1))) := by
            symm
            calc
              ∫ p, h p ∂(Measure.map e (uniformCube (t + 1)))
                  = ∫ z, h (e z) ∂(uniformCube (t + 1)) := by
                      exact MeasureTheory.integral_map
                        (μ := uniformCube (t + 1))
                        e.measurable.aemeasurable
                        (f := h)
                        hMapInt.aestronglyMeasurable
              _ = ∫ z, g (prefixPositiveCount n hn (t + 1) z) ∂(uniformCube (t + 1)) := by
                    refine integral_congr_ae <| Filter.Eventually.of_forall ?_
                    intro z
                    simp [h]
    _ = ∫ p, h p ∂((volume : Measure I).prod (uniformCube t)) := by
          rw [uniformCube_map_piFinSuccAboveLast]
    _ = ∫ u : I, ∫ y, h (u, y) ∂(uniformCube t) ∂(volume : Measure I) := by
          simpa using (MeasureTheory.integral_prod h hProdInt)
    _ = ∫ y, ∫ u : I, h (u, y) ∂(volume : Measure I) ∂(uniformCube t) := by
          simpa using
            (MeasureTheory.integral_integral_swap (f := fun u y ↦ h (u, y)) hProdInt)
    _ = ∫ y, ∫ u : I,
          g (prefixPositiveCount n hn (t + 1)
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
              (Fin.last t)).symm (u, y))) ∂(volume : Measure I) ∂(uniformCube t) := by
            simp [h, e]

/-- Helper for Theorem 17.60: splitting off the last coordinate turns the deterministic-time
occupied-box integral into the one-step occupied-box expectation applied to the prefix count. -/
private lemma prefixPositiveCount_integral_recursion
    {n t : ℕ} (hn : 1 ≤ n) {g : ℕ → ℝ} (hg_mono : Monotone g)
    (hB : ∃ B : ℝ, ∀ m : ℕ, g m ≤ B) :
    ∫ z, g (prefixPositiveCount n hn (t + 1) z) ∂(uniformCube (t + 1)) =
      ∫ y, occupancyStepExpectation n g (prefixPositiveCount n hn t y) ∂(uniformCube t) := by
  -- Proof comment: first rewrite the `(t + 1)`-cube integral in prefix/last order, then replace
  -- the inner fresh-mark integral by the already-proved one-step expectation formula.
  calc
    ∫ z, g (prefixPositiveCount n hn (t + 1) z) ∂(uniformCube (t + 1))
        =
          ∫ y, ∫ u : I,
            g (prefixPositiveCount n hn (t + 1)
              ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (t + 1) ↦ I)
                (Fin.last t)).symm (u, y))) ∂(volume : Measure I) ∂(uniformCube t) :=
          prefixPositiveCount_succ_integral_splitLast (hn := hn) hg_mono hB
    _ = ∫ y, occupancyStepExpectation n g (prefixPositiveCount n hn t y) ∂(uniformCube t) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall ?_
          intro y
          exact prefixPositiveCount_succ_integral_eq_occupancyStepExpectation (hn := hn) g y

/-- Helper for Theorem 17.60: at every deterministic time, the occupied-box count is monotone in
the number of boxes when tested against any bounded monotone nat-valued function. -/
private lemma prefixPositiveCount_integral_mono
    {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₁₂ : n₁ ≤ n₂) :
    ∀ t : ℕ, ∀ {g : ℕ → ℝ}, Monotone g →
      (∃ B : ℝ, ∀ m : ℕ, g m ≤ B) →
      ∫ y, g (prefixPositiveCount n₁ hn₁ t y) ∂(uniformCube t) ≤
        ∫ y, g (prefixPositiveCount n₂ (le_trans hn₁ hn₁₂) t y) ∂(uniformCube t)
  | 0, g, hg_mono, hB => by
      have hzero₁ : ∀ y : Fin 0 → I, prefixPositiveCount n₁ hn₁ 0 y = 0 := by
        intro y
        -- Proof comment: with no sampled marks, the occupied successor-label set is empty.
        rw [prefixPositiveCount_eq_prefixOccupiedLabels_card]
        simp [prefixOccupiedLabels, prefixLabelTuple]
      have hzero₂ : ∀ y : Fin 0 → I, prefixPositiveCount n₂ (le_trans hn₁ hn₁₂) 0 y = 0 := by
        intro y
        -- Proof comment: the same empty-prefix argument applies to the larger box system.
        rw [prefixPositiveCount_eq_prefixOccupiedLabels_card]
        simp [prefixOccupiedLabels, prefixLabelTuple]
      -- Proof comment: both time-zero integrands are the constant value `g 0`, so the two
      -- integrals agree exactly.
      simp [hzero₁, hzero₂]
  | t + 1, g, hg_mono, hB => by
      let hn₂ : 1 ≤ n₂ := le_trans hn₁ hn₁₂
      have hstep₁_mono : Monotone (occupancyStepExpectation n₁ g) :=
        occupancyStepExpectation_monotoneInCount hn₁ hg_mono hB
      have hstep₂_mono : Monotone (occupancyStepExpectation n₂ g) :=
        occupancyStepExpectation_monotoneInCount hn₂ hg_mono hB
      have hstep₁_bdd : ∃ B : ℝ, ∀ k : ℕ, occupancyStepExpectation n₁ g k ≤ B :=
        occupancyStepExpectation_bddAbove n₁ hg_mono hB
      have hstep₂_bdd : ∃ B : ℝ, ∀ k : ℕ, occupancyStepExpectation n₂ g k ≤ B :=
        occupancyStepExpectation_bddAbove n₂ hg_mono hB
      have hmiddle :
          ∫ y, occupancyStepExpectation n₁ g (prefixPositiveCount n₁ hn₁ t y) ∂(uniformCube t)
            ≤
              ∫ y, occupancyStepExpectation n₁ g (prefixPositiveCount n₂ hn₂ t y)
                ∂(uniformCube t) :=
        prefixPositiveCount_integral_mono (hn₁ := hn₁) (hn₁₂ := hn₁₂) t hstep₁_mono hstep₁_bdd
      have hboxes :
          ∫ y, occupancyStepExpectation n₁ g (prefixPositiveCount n₂ hn₂ t y) ∂(uniformCube t)
            ≤
              ∫ y, occupancyStepExpectation n₂ g (prefixPositiveCount n₂ hn₂ t y)
                ∂(uniformCube t) := by
          refine MeasureTheory.integral_mono_ae
            (integrable_prefixPositiveCountValue (hn := hn₂) hstep₁_mono hstep₁_bdd)
            (integrable_prefixPositiveCountValue (hn := hn₂) hstep₂_mono hstep₂_bdd) ?_
          filter_upwards with y
          exact occupancyStepExpectation_monotoneInBoxes hn₁ hn₁₂ hg_mono hB
      -- Proof comment: rewrite both deterministic-time laws by the one-step recursion, apply the
      -- induction hypothesis to the transformed test function, and then enlarge the box count in
      -- the remaining one-step expectation.
      calc
        ∫ y, g (prefixPositiveCount n₁ hn₁ (t + 1) y) ∂(uniformCube (t + 1))
            =
              ∫ y, occupancyStepExpectation n₁ g (prefixPositiveCount n₁ hn₁ t y)
                ∂(uniformCube t) :=
            prefixPositiveCount_integral_recursion (hn := hn₁) hg_mono hB
        _ ≤
            ∫ y, occupancyStepExpectation n₁ g (prefixPositiveCount n₂ hn₂ t y)
              ∂(uniformCube t) :=
            hmiddle
        _ ≤
            ∫ y, occupancyStepExpectation n₂ g (prefixPositiveCount n₂ hn₂ t y)
              ∂(uniformCube t) :=
            hboxes
        _ =
            ∫ y, g (prefixPositiveCount n₂ hn₂ (t + 1) y) ∂(uniformCube (t + 1)) := by
              symm
              exact prefixPositiveCount_integral_recursion (hn := hn₂) hg_mono hB

/-- Helper for Theorem 17.60: for fixed common rate `λ`, the binomial laws
`Bin(n, 1 - exp (-λ / n))` should be stochastically increasing in `n`. -/
private lemma binomial_commonRate_stochasticLE
    (n₁ n₂ : ℕ) (hn₁ : 1 ≤ n₁) (hn₁₂ : n₁ ≤ n₂) (lam : NNReal) :
    StochasticLE
      (ProbabilityMeasure.toFin1Real
        (⟨Bin(n₁, commonRateParameter lam n₁), inferInstance⟩ : ProbabilityMeasure ℕ))
      (ProbabilityMeasure.toFin1Real
        (⟨Bin(n₂, commonRateParameter lam n₂), inferInstance⟩ : ProbabilityMeasure ℕ)) := by
  let μ₁ : ProbabilityMeasure ℕ := ⟨Bin(n₁, commonRateParameter lam n₁), inferInstance⟩
  let μ₂ : ProbabilityMeasure ℕ := ⟨Bin(n₂, commonRateParameter lam n₂), inferInstance⟩
  let P : Measure (ℕ × (ℕ → I)) := poissonizedEqualGridMeasure lam
  let Q : Measure (ℕ → I) := Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure I))
  let X₁ : ℕ × (ℕ → I) → ℕ := fun ω ↦ fixedTimePositiveCount n₁ hn₁ ω.1 ω.2
  let hn₂ : 1 ≤ n₂ := le_trans hn₁ hn₁₂
  let X₂ : ℕ × (ℕ → I) → ℕ := fun ω ↦ fixedTimePositiveCount n₂ hn₂ ω.1 ω.2
  intro f hf_mono hf_bdd hf_meas
  let g : ℕ → ℝ := fun n ↦ f (![n] : Fin 1 → ℝ)
  have hsingleton_mono :
      ∀ {m n : ℕ}, m ≤ n → (![m] : Fin 1 → ℝ) ≤ (![n] : Fin 1 → ℝ) := by
    intro m n hmn i
    fin_cases i
    simpa using (show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn)
  have hg_mono : Monotone g := by
    -- Proof comment: on singleton vectors, the ambient coordinatewise order is the usual nat
    -- order.
    intro m n hmn
    exact hf_mono (hsingleton_mono hmn)
  have hg_meas : Measurable g := by
    simpa using (Measurable.of_discrete : Measurable g)
  have hB : ∃ B : ℝ, ∀ n : ℕ, g n ≤ B := by
    -- Proof comment: boundedness of the ambient test function restricts to boundedness on the
    -- embedded nat-valued laws.
    obtain ⟨R, hR⟩ := hf_bdd.exists_norm_le
    refine ⟨R, ?_⟩
    intro n
    have hnorm : ‖g n‖ ≤ R := by
      exact hR (g n) ⟨(![n] : Fin 1 → ℝ), rfl⟩
    exact le_trans (le_abs_self (g n)) hnorm
  have hg_int₁ : Integrable g (μ₁ : Measure ℕ) := by
    simpa [μ₁] using integrable_of_monotone_nat_of_bddAbove (μ := μ₁) hg_mono hB
  have hg_int₂ : Integrable g (μ₂ : Measure ℕ) := by
    simpa [μ₂] using integrable_of_monotone_nat_of_bddAbove (μ := μ₂) hg_mono hB
  have hLaw₁ :
      HasLaw X₁ (μ₁ : Measure ℕ) P := by
    simpa [μ₁, P, X₁, poissonizedEqualGridMeasure, fixedTimePositiveCount,
      equalGridPoissonizedOccupancy_eq_fixedTimePositiveCount] using
      (equalGridPoissonizedOccupancy_hasLaw_binomial (lam := lam) (hn := hn₁))
  have hLaw₂ :
      HasLaw X₂ (μ₂ : Measure ℕ) P := by
    simpa [μ₂, P, X₂, poissonizedEqualGridMeasure, fixedTimePositiveCount,
      equalGridPoissonizedOccupancy_eq_fixedTimePositiveCount] using
      (equalGridPoissonizedOccupancy_hasLaw_binomial (lam := lam) (hn := hn₂))
  have hIntMap₁ : Integrable g (Measure.map X₁ P) := by
    rw [hLaw₁.map_eq]
    simpa using hg_int₁
  have hIntMap₂ : Integrable g (Measure.map X₂ P) := by
    rw [hLaw₂.map_eq]
    simpa using hg_int₂
  have hProdInt₁ : Integrable (fun ω : ℕ × (ℕ → I) ↦ g (X₁ ω)) P :=
    (integrable_map_measure hg_meas.aestronglyMeasurable hLaw₁.aemeasurable).1 hIntMap₁
  have hProdInt₂ : Integrable (fun ω : ℕ × (ℕ → I) ↦ g (X₂ ω)) P :=
    (integrable_map_measure hg_meas.aestronglyMeasurable hLaw₂.aemeasurable).1 hIntMap₂
  have hNatLaw₁ :
      ∫ n, g n ∂(μ₁ : Measure ℕ) = ∫ ω, g (X₁ ω) ∂P := by
    calc
      ∫ n, g n ∂(μ₁ : Measure ℕ)
          = ∫ n, g n ∂(Measure.map X₁ P) := by
              rw [hLaw₁.map_eq]
      _ = ∫ ω, g (X₁ ω) ∂P := by
            simpa [X₁] using
              (MeasureTheory.integral_map (μ := P) hLaw₁.aemeasurable
                (f := g) hg_meas.aestronglyMeasurable)
  have hNatLaw₂ :
      ∫ n, g n ∂(μ₂ : Measure ℕ) = ∫ ω, g (X₂ ω) ∂P := by
    calc
      ∫ n, g n ∂(μ₂ : Measure ℕ)
          = ∫ n, g n ∂(Measure.map X₂ P) := by
              rw [hLaw₂.map_eq]
      _ = ∫ ω, g (X₂ ω) ∂P := by
            simpa [X₂] using
              (MeasureTheory.integral_map (μ := P) hLaw₂.aemeasurable
                (f := g) hg_meas.aestronglyMeasurable)
  have hTime :
      ∀ t : ℕ,
        ∫ marks, g (fixedTimePositiveCount n₁ hn₁ t marks) ∂Q
          ≤ ∫ marks, g (fixedTimePositiveCount n₂ hn₂ t marks) ∂Q := by
    intro t
    have hFixed₁ :
        ∫ marks, g (fixedTimePositiveCount n₁ hn₁ t marks) ∂Q
          = ∫ y, g (prefixPositiveCount n₁ hn₁ t y) ∂(uniformCube t) := by
            calc
              ∫ marks, g (fixedTimePositiveCount n₁ hn₁ t marks) ∂Q
                  = ∫ m, g m ∂(Measure.map
                      (fun marks : ℕ → I ↦ fixedTimePositiveCount n₁ hn₁ t marks) Q) := by
                        symm
                        simpa using
                          (MeasureTheory.integral_map (μ := Q)
                            ((fixedTimePositiveCount_hasLaw_prefixPositiveCount (hn := hn₁) t).aemeasurable)
                            (f := g) hg_meas.aestronglyMeasurable)
              _ = ∫ m, g m ∂(Measure.map (prefixPositiveCount n₁ hn₁ t) (uniformCube t)) := by
                    rw [(fixedTimePositiveCount_hasLaw_prefixPositiveCount (hn := hn₁) t).map_eq]
              _ = ∫ y, g (prefixPositiveCount n₁ hn₁ t y) ∂(uniformCube t) := by
                    simpa using
                      (MeasureTheory.integral_map (μ := uniformCube t)
                        ((measurable_prefixPositiveCount n₁ hn₁ t).aemeasurable)
                        (f := g) hg_meas.aestronglyMeasurable)
    have hFixed₂ :
        ∫ marks, g (fixedTimePositiveCount n₂ hn₂ t marks) ∂Q
          = ∫ y, g (prefixPositiveCount n₂ hn₂ t y) ∂(uniformCube t) := by
            calc
              ∫ marks, g (fixedTimePositiveCount n₂ hn₂ t marks) ∂Q
                  = ∫ m, g m ∂(Measure.map
                      (fun marks : ℕ → I ↦ fixedTimePositiveCount n₂ hn₂ t marks) Q) := by
                        symm
                        simpa using
                          (MeasureTheory.integral_map (μ := Q)
                            ((fixedTimePositiveCount_hasLaw_prefixPositiveCount (hn := hn₂) t).aemeasurable)
                            (f := g) hg_meas.aestronglyMeasurable)
              _ = ∫ m, g m ∂(Measure.map (prefixPositiveCount n₂ hn₂ t) (uniformCube t)) := by
                    rw [(fixedTimePositiveCount_hasLaw_prefixPositiveCount (hn := hn₂) t).map_eq]
              _ = ∫ y, g (prefixPositiveCount n₂ hn₂ t y) ∂(uniformCube t) := by
                    simpa using
                      (MeasureTheory.integral_map (μ := uniformCube t)
                        ((measurable_prefixPositiveCount n₂ hn₂ t).aemeasurable)
                        (f := g) hg_meas.aestronglyMeasurable)
    rw [hFixed₁, hFixed₂]
    exact prefixPositiveCount_integral_mono hn₁ hn₁₂ t hg_mono hB
  have hOuter :
      ∫ t, ∫ marks, g (fixedTimePositiveCount n₁ hn₁ t marks) ∂Q ∂(poissonMeasure lam)
        ≤
          ∫ t, ∫ marks, g (fixedTimePositiveCount n₂ hn₂ t marks) ∂Q ∂(poissonMeasure lam) := by
    refine MeasureTheory.integral_mono_ae hProdInt₁.integral_prod_left hProdInt₂.integral_prod_left ?_
    exact Filter.Eventually.of_forall hTime
  -- Proof comment: transport the common-rate binomial laws to the Poissonized occupancy model,
  -- compare the deterministic-time inner expectations via `prefixPositiveCount_integral_mono`,
  -- and then average the comparison over the outer Poisson time law.
  calc
    ∫ x, f x ∂((μ₁.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ))
        = ∫ n, g n ∂(μ₁ : Measure ℕ) := by
            simpa [g] using integral_toFin1Real_eq_integral_nat μ₁ hf_meas
    _ = ∫ ω, g (X₁ ω) ∂P := hNatLaw₁
    _ = ∫ t, ∫ marks, g (fixedTimePositiveCount n₁ hn₁ t marks) ∂Q ∂(poissonMeasure lam) := by
          simpa [P, Q, X₁, poissonizedEqualGridMeasure] using
            (MeasureTheory.integral_prod (fun ω : ℕ × (ℕ → I) ↦ g (X₁ ω)) hProdInt₁)
    _ ≤ ∫ t, ∫ marks, g (fixedTimePositiveCount n₂ hn₂ t marks) ∂Q ∂(poissonMeasure lam) := hOuter
    _ = ∫ ω, g (X₂ ω) ∂P := by
          symm
          simpa [P, Q, X₂, poissonizedEqualGridMeasure] using
            (MeasureTheory.integral_prod (fun ω : ℕ × (ℕ → I) ↦ g (X₂ ω)) hProdInt₂)
    _ = ∫ n, g n ∂(μ₂ : Measure ℕ) := hNatLaw₂.symm
    _ = ∫ x, f x ∂((μ₂.toFin1Real : ProbabilityMeasure (Fin 1 → ℝ)) : Measure (Fin 1 → ℝ)) := by
          symm
          simpa [g] using integral_toFin1Real_eq_integral_nat μ₂ hf_meas

-- Proof sketch: express the comparison directly in the chapter owner `StochasticLE` on the
-- embedded one-dimensional laws, then use `stochasticLE_toFin1Real_iff_upper_tail` to recover
-- the textbook tail inequalities. The necessity of (17.30) comes from the atom at `0`, and the
-- necessity of (17.31) comes from comparing the maximal possible values. Sufficiency is obtained
-- by the occupancy coupling from Example 17.59 together with Theorem 17.58 in the interior case
-- `0 < p₂ < 1`; the endpoint cases `p₂ = 0` and `p₂ = 1` reduce directly to degenerate binomial
-- laws and satisfy the same criterion.
/-- Theorem 17.60: for `p₁ ∈ (0,1)` and arbitrary `p₂ : I`, the binomial law `Bin(n₁, p₁)` is
below `Bin(n₂, p₂)` in stochastic order if and only if (17.30)
`(1 - p₁)^n₁ ≥ (1 - p₂)^n₂` and (17.31) `n₁ ≤ n₂`. -/
theorem binomial_stochasticLE_iff
    (n₁ n₂ : ℕ) (p₁ p₂ : I)
    (hp₁₀ : 0 < (p₁ : ℝ)) (hp₁₁ : (p₁ : ℝ) < 1)
    : StochasticLE
        (ProbabilityMeasure.toFin1Real
          (⟨Bin(n₁, p₁), inferInstance⟩ : ProbabilityMeasure ℕ))
        (ProbabilityMeasure.toFin1Real
          (⟨Bin(n₂, p₂), inferInstance⟩ : ProbabilityMeasure ℕ)) ↔
        (1 - (p₁ : ℝ)) ^ n₁ ≥ (1 - (p₂ : ℝ)) ^ n₂ ∧ n₁ ≤ n₂ := by
  constructor
  · intro hst
    have htail_one :
        Bin(n₁, p₁) (Set.Ici 1) ≤ Bin(n₂, p₂) (Set.Ici 1) :=
      ProbabilityTheory.StochasticLE.upper_tail_nat
        (μ₁ := (⟨Bin(n₁, p₁), inferInstance⟩ : ProbabilityMeasure ℕ))
        (μ₂ := (⟨Bin(n₂, p₂), inferInstance⟩ : ProbabilityMeasure ℕ))
        hst 1
    have htail_one_real :
        (Bin(n₁, p₁) (Set.Ici 1)).toReal ≤ (Bin(n₂, p₂) (Set.Ici 1)).toReal := by
      exact ENNReal.toReal_mono (measure_ne_top (Bin(n₂, p₂)) _) htail_one
    have hpow :
        (1 - (p₁ : ℝ)) ^ n₁ ≥ (1 - (p₂ : ℝ)) ^ n₂ := by
      -- Proof comment: the first nontrivial upper tail is the complement of the atom at `0`.
      rw [natMeasure_tail_Ici_one_toReal, natMeasure_tail_Ici_one_toReal,
        binomial_apply_zero_toReal, binomial_apply_zero_toReal] at htail_one_real
      linarith
    have hn : n₁ ≤ n₂ := by
      by_contra hnot
      have hlt : n₂ < n₁ := lt_of_not_ge hnot
      have htail_succ :
          Bin(n₁, p₁) (Set.Ici (n₂ + 1)) ≤ Bin(n₂, p₂) (Set.Ici (n₂ + 1)) :=
        ProbabilityTheory.StochasticLE.upper_tail_nat
          (μ₁ := (⟨Bin(n₁, p₁), inferInstance⟩ : ProbabilityMeasure ℕ))
          (μ₂ := (⟨Bin(n₂, p₂), inferInstance⟩ : ProbabilityMeasure ℕ))
          hst (n₂ + 1)
      have htail_zero : Bin(n₁, p₁) (Set.Ici (n₂ + 1)) = 0 := by
        -- Proof comment: if the second law cannot exceed `n₂`, stochastic domination forces the
        -- first law to have zero mass on the same forbidden tail.
        rw [binomial_apply_tail_succ_eq_zero n₂ p₂] at htail_succ
        exact le_antisymm htail_succ bot_le
      have hsingleton_le_tail :
          Bin(n₁, p₁) ({n₁} : Set ℕ) ≤ Bin(n₁, p₁) (Set.Ici (n₂ + 1)) := by
        -- Proof comment: when `n₂ < n₁`, the top atom `{n₁}` sits inside the tail
        -- `Set.Ici (n₂ + 1)`.
        refine MeasureTheory.measure_mono ?_
        intro x hx
        simp at hx
        simp [hx, Nat.succ_le_of_lt hlt]
      have hsingleton_zero : Bin(n₁, p₁) ({n₁} : Set ℕ) = 0 := by
        exact le_antisymm (le_trans hsingleton_le_tail (by simpa [htail_zero])) bot_le
      have hsingleton_real_pos :
          0 < (Bin(n₁, p₁) ({n₁} : Set ℕ)).toReal := by
        -- Proof comment: the top atom of `Bin(n₁, p₁)` equals `p₁ ^ n₁`, which is strictly
        -- positive because `p₁ ∈ (0, 1)` and `n₁ > 0` under the contradiction hypothesis.
        rw [binomial_apply_singleton_toReal]
        simp [Nat.choose_self, hp₁₀.ne', pow_pos hp₁₀]
      simpa [hsingleton_zero] using hsingleton_real_pos
    exact ⟨hpow, hn⟩
  · intro hcond
    rcases hcond with ⟨hpow, hn₁₂⟩
    by_cases hn₁_zero : n₁ = 0
    · -- Proof comment: when `n₁ = 0`, the left law is `dirac 0`, so every positive upper tail is
      -- zero and the stochastic order is immediate from the tail criterion.
      subst hn₁_zero
      refine
        (ProbabilityTheory.stochasticLE_toFin1Real_iff_upper_tail
          (⟨Bin(0, p₁), inferInstance⟩ : ProbabilityMeasure ℕ)
          (⟨Bin(n₂, p₂), inferInstance⟩ : ProbabilityMeasure ℕ)).2 ?_
      intro k
      cases k with
      | zero =>
          have hIciZero : (Set.Ici (0 : ℕ)) = Set.univ := by
            ext x
            simp
          rw [hIciZero]
          simpa using (measure_univ (μ := Bin(n₂, p₂)))
      | succ j =>
          simp [binomial_zero_left]
    · have hn₁ : 1 ≤ n₁ := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn₁_zero)
      have hn₂ : 1 ≤ n₂ := le_trans hn₁ hn₁₂
      let lam : NNReal := Real.toNNReal (-(n₁ : ℝ) * Real.log (1 - (p₁ : ℝ)))
      let q₂ : I := commonRateParameter lam n₂
      have hp₁_common :
          commonRateParameter lam n₁ = p₁ := by
        -- Proof comment: the normalization `λ = -n₁ log (1 - p₁)` recovers the original success
        -- parameter at level `n₁`.
        simpa [lam] using commonRateParameter_self_eq n₁ p₁ hn₁ hp₁₀ hp₁₁
      have hq₂_le : q₂ ≤ p₂ := by
        -- Proof comment: the power condition forces the normalized `n₂`-parameter to stay below
        -- the original `p₂`.
        simpa [lam, q₂] using
          commonRateParameter_le_of_powCondition n₁ n₂ p₁ p₂ hn₁ hn₂ hp₁₀ hp₁₁ hpow
      have hcommon :
          StochasticLE
            (ProbabilityMeasure.toFin1Real
              (⟨Bin(n₁, p₁), inferInstance⟩ : ProbabilityMeasure ℕ))
            (ProbabilityMeasure.toFin1Real
              (⟨Bin(n₂, q₂), inferInstance⟩ : ProbabilityMeasure ℕ)) := by
        -- Proof comment: after normalizing the zero-atom, only the common-rate comparison remains.
        simpa [q₂] using
          (hp₁_common ▸ binomial_commonRate_stochasticLE n₁ n₂ hn₁ hn₁₂ lam)
      have hsameN :
          StochasticLE
            (ProbabilityMeasure.toFin1Real
              (⟨Bin(n₂, q₂), inferInstance⟩ : ProbabilityMeasure ℕ))
            (ProbabilityMeasure.toFin1Real
              (⟨Bin(n₂, p₂), inferInstance⟩ : ProbabilityMeasure ℕ)) := by
        rcases binomial_success_parameter_coupling n₂ hq₂_le with ⟨hCoupling, hOrdered⟩
        -- Proof comment: Example 17.59 compares equal-trial binomial laws by coupling the same
        -- uniforms under the two thresholds.
        exact stochasticLE_toFin1Real_of_natCoupling hCoupling hOrdered
      -- Proof comment: chain the common-rate comparison with the same-`n₂` success-parameter
      -- comparison.
      intro f hf_mono hf_bdd hf_meas
      exact le_trans
        (hcommon hf_mono hf_bdd hf_meas)
        (hsameN hf_mono hf_bdd hf_meas)

end ProbabilityTheory

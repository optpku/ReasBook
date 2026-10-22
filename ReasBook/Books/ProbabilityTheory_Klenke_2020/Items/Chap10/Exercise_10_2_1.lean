/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

universe u

section

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X : ℕ → Ω → ℝ} {τ : Ω → ℕ}

/-
Exercise 10.2.1 is `source-facing`: the source fixes the square variation `⟨X⟩` of the
square-integrable martingale `X`. The internal truncation helpers and the public exercise
statements therefore use the canonical owner `⟨X⟩[ℱ, μ]` directly.
-/
local notation "τ∞" => fun ω ↦ (τ ω : ℕ∞)
local notation "squareProcess" => fun n ω ↦ (X n ω) ^ 2
local notation "squareVariation" => predictablePart squareProcess ℱ μ

/-- Helper for Exercise 10.2.1: the bounded truncation `τ ∧ n` of the finite stopping time `τ`. -/
noncomputable def truncatedStoppingTime (τ : Ω → ℕ) (n : ℕ) : Ω → ℕ∞ :=
  fun ω ↦ min (τ ω : ℕ∞) n

/-- Helper for Exercise 10.2.1: stopping at the bounded truncation `τ ∧ n` is ordinary
evaluation at the deterministic index `min (τ ω) n`. -/
lemma stoppedValue_truncated_eq_eval {β : Type*} (u : ℕ → Ω → β) (n : ℕ) :
    stoppedValue u (truncatedStoppingTime τ n) = fun ω ↦ u (min (τ ω) n) ω := by
  -- Route correction: normalize finite stopped values through the canonical finite-time API
  -- instead of unfolding `WithTop.untopA` by hand in every proof.
  simpa [truncatedStoppingTime] using
    (stoppedValue_coe_eq_eval u (fun ω ↦ min (τ ω) n) :
      stoppedValue u (fun ω ↦ ((min (τ ω) n : ℕ) : ℕ∞)) = fun ω ↦ u (min (τ ω) n) ω)

/-- Helper for Exercise 10.2.1: stopping at the finite time `τ` is ordinary evaluation at `τ ω`.
-/
lemma stoppedValue_tau_eq_eval {β : Type*} (u : ℕ → Ω → β) :
    stoppedValue u τ∞ = fun ω ↦ u (τ ω) ω := by
  -- The same finite-time normalization applies to the full finite stop `τ`.
  simpa using
    (stoppedValue_coe_eq_eval u τ : stoppedValue u (fun ω ↦ (τ ω : ℕ∞)) = fun ω ↦ u (τ ω) ω)

section TruncationHelpers

/-- Helper for Exercise 10.2.1: partial sums of nonnegative real terms are monotone in the range
cutoff. -/
lemma sumRangeMonotoneOfNonnegative {f : ℕ → ℝ} {n m : ℕ} (hnm : n ≤ m)
    (h_nonneg : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range m, f i := by
  -- Increase the cutoff one step at a time and use that each new summand is nonnegative.
  induction m with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst hn
      simp
  | succ m ih =>
      by_cases hnm' : n ≤ m
      · calc
          ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range m, f i := ih hnm'
          _ ≤ ∑ i ∈ Finset.range (m + 1), f i := by
            rw [Finset.sum_range_succ]
            linarith [h_nonneg m]
      · have hn_eq : n = m + 1 := by
          apply le_antisymm hnm
          exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hnm')
        subst hn_eq
        simp

/-- Helper for Exercise 10.2.1: bounded optional sampling for the truncations `τ ∧ n` preserves
the martingale expectation. -/
lemma expectation_stoppedValue_eq_initial_truncation
    (hX : Martingale X ℱ μ) (hτ : IsStoppingTime ℱ τ∞) (n : ℕ) :
    μ[stoppedValue X (truncatedStoppingTime τ n)] = μ[X 0] := by
  let τn : Ω → ℕ∞ := truncatedStoppingTime τ n
  have hτn : IsStoppingTime ℱ τn := hτ.min_const n
  have hτn_le : ∀ ω, τn ω ≤ n := fun ω ↦ by
    simp [τn, truncatedStoppingTime]
  -- Apply the owner optional-sampling theorem to the bounded truncation `τ ∧ n`.
  calc
    μ[stoppedValue X τn] = μ[μ[X n | hτn.measurableSpace]] := by
      exact integral_congr_ae (hX.stoppedValue_ae_eq_condExp_of_le_const hτn hτn_le)
    _ = μ[X n] := by
      rw [integral_condExp (hτn.measurableSpace_le_of_le hτn_le)]
    _ = μ[X 0] := by
      simpa using (martingale_expectation_eq hX (Nat.zero_le n)).symm

/-- Helper for Exercise 10.2.1: the stopped canonical square variation is almost surely monotone
along the bounded truncations `τ ∧ n`. -/
lemma stoppedSquareVariation_truncation_ae_mono
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    {n m : ℕ} (hnm : n ≤ m) :
    stoppedValue squareVariation (truncatedStoppingTime τ n) ≤ᵐ[μ]
      stoppedValue squareVariation (truncatedStoppingTime τ m) := by
  have hsq :
      ∀ᵐ ω ∂μ, ∀ k : ℕ,
        (⟨X⟩[ℱ, μ]) k ω =
          ∑ i ∈ Finset.range k, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    -- Use the deterministic-time formula for the canonical square variation at every time.
    exact ae_all_iff.2 fun k ↦ squareVariation_eq_sum_condExp_sq_increment hX hXsq k
  have hnonneg :
      ∀ᵐ ω ∂μ, ∀ i : ℕ,
        0 ≤ μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    -- Each conditional expectation of a square is almost surely nonnegative.
    refine ae_all_iff.2 fun i ↦ ?_
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω ↦ sq_nonneg _)
  filter_upwards [hsq, hnonneg] with ω hsqω hnonnegω
  have hmin : min (τ ω) n ≤ min (τ ω) m := min_le_min_left _ hnm
  have hsum :
      ∑ i ∈ Finset.range (min (τ ω) n),
          μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω ≤
        ∑ i ∈ Finset.range (min (τ ω) m),
          μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    -- Compare the partial sums using nonnegativity of the added tail.
    exact sumRangeMonotoneOfNonnegative hmin hnonnegω
  have hleft :
      stoppedValue squareVariation (truncatedStoppingTime τ n) ω =
        ∑ i ∈ Finset.range (min (τ ω) n),
          μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    have hEval :
        stoppedValue squareVariation (truncatedStoppingTime τ n) ω =
          squareVariation (min (τ ω) n) ω :=
      congrFun (stoppedValue_truncated_eq_eval squareVariation n) ω
    -- The adapter reduces the stopped value to the deterministic-time square-variation formula.
    simpa [hEval] using hsqω (min (τ ω) n)
  have hright :
      stoppedValue squareVariation (truncatedStoppingTime τ m) ω =
        ∑ i ∈ Finset.range (min (τ ω) m),
          μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    have hEval :
        stoppedValue squareVariation (truncatedStoppingTime τ m) ω =
          squareVariation (min (τ ω) m) ω :=
      congrFun (stoppedValue_truncated_eq_eval squareVariation m) ω
    -- Apply the same deterministic-time normalization at the larger truncation.
    simpa [hEval] using hsqω (min (τ ω) m)
  rw [hleft, hright]
  exact hsum

/-- Helper for Exercise 10.2.1: the canonical square variation is almost surely nonnegative at
every deterministic time. -/
lemma squareVariation_nonneg_ae
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, 0 ≤ squareVariation k ω := by
  have hsq :
      ∀ᵐ ω ∂μ, ∀ k : ℕ,
        squareVariation k ω =
          ∑ i ∈ Finset.range k, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    -- Normalize the square variation to the finite sum of conditional squared increments.
    exact ae_all_iff.2 fun k ↦ squareVariation_eq_sum_condExp_sq_increment hX hXsq k
  have hnonneg :
      ∀ᵐ ω ∂μ, ∀ i : ℕ,
        0 ≤ μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    -- Each conditional squared increment is almost surely nonnegative.
    refine ae_all_iff.2 fun i ↦ ?_
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω ↦ sq_nonneg _)
  filter_upwards [hsq, hnonneg] with ω hsqω hnonnegω k
  rw [hsqω k]
  exact Finset.sum_nonneg fun i _ ↦ hnonnegω i

/-- Helper for Exercise 10.2.1: bounded optional sampling preserves the expectation of the
compensated squared process `X_n^2 - ⟨X⟩_n` along the truncations `τ ∧ n`. -/
lemma expectation_stoppedSquareSubVariation_eq_initial_truncation
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (n : ℕ) :
    μ[fun ω ↦ (stoppedValue X (truncatedStoppingTime τ n) ω) ^ 2 -
        stoppedValue squareVariation (truncatedStoppingTime τ n) ω] =
      μ[fun ω ↦ (X 0 ω) ^ 2] := by
  let M : ℕ → Ω → ℝ := fun k ω ↦ (X k ω) ^ 2 - squareVariation k ω
  have hM : Martingale M ℱ μ := square_sub_squareVariation_martingale hX hXsq
  -- Apply the bounded optional-sampling identity to the compensated-square martingale.
  calc
    μ[fun ω ↦ (stoppedValue X (truncatedStoppingTime τ n) ω) ^ 2 -
        stoppedValue squareVariation (truncatedStoppingTime τ n) ω] =
      μ[stoppedValue M (truncatedStoppingTime τ n)] := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        simp [M, stoppedValue]
    _ = μ[M 0] := expectation_stoppedValue_eq_initial_truncation hM hτ n
    _ = μ[fun ω ↦ (X 0 ω) ^ 2] := by
      simp [M]

/-- Helper for Exercise 10.2.1: for bounded truncations `τ ∧ n ≤ τ ∧ m`, optional sampling
turns the later stopped value against the earlier one into the earlier square. -/
lemma boundedStoppedCrossTerm_eq_stoppedSquare
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) {n m : ℕ} (hnm : n ≤ m) :
    μ[fun ω ↦ stoppedValue X (truncatedStoppingTime τ m) ω *
        stoppedValue X (truncatedStoppingTime τ n) ω] =
      μ[fun ω ↦ (stoppedValue X (truncatedStoppingTime τ n) ω) ^ 2] := by
  let σ : Ω → ℕ∞ := truncatedStoppingTime τ n
  let ρ : Ω → ℕ∞ := truncatedStoppingTime τ m
  have hσ : IsStoppingTime ℱ σ := hτ.min_const n
  have hρ : IsStoppingTime ℱ ρ := hτ.min_const m
  have hσ_le_ρ : σ ≤ ρ := fun ω ↦ by
    exact min_le_min_left _ (show (n : ℕ∞) ≤ m by exact_mod_cast hnm)
  have hρ_le : ∀ ω, ρ ω ≤ m := fun ω ↦ by
    exact min_le_right (τ ω : ℕ∞) m
  have hX_memLp : ∀ k, MemLp (X k) 2 μ := fun k ↦
    (memLp_two_iff_integrable_sq
      (((hX.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable)).2 (hXsq k)
  have hσ_memLp : MemLp (stoppedValue X σ) 2 μ := by
    exact memLp_stoppedValue hσ hX_memLp (fun ω ↦ min_le_right (τ ω : ℕ∞) n)
  have hρ_memLp : MemLp (stoppedValue X ρ) 2 μ := by
    exact memLp_stoppedValue hρ hX_memLp hρ_le
  have hσ_meas :
      Measurable[hσ.measurableSpace] (stoppedValue X σ) :=
    measurable_stoppedValue hX.stronglyAdapted.progMeasurable_of_discrete hσ
  have hρ_int : Integrable (stoppedValue X ρ) μ := by
    exact integrable_stoppedValue ℕ hρ hX.integrable hρ_le
  have hProd_int :
      Integrable (fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω) μ := by
    simpa [σ, ρ] using MemLp.integrable_mul hρ_memLp hσ_memLp
  have hCond :
      μ[fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω | hσ.measurableSpace] =ᵐ[μ]
        fun ω ↦ (stoppedValue X σ ω) ^ 2 := by
    -- Condition at the earlier stop, pull out the measurable factor, and identify the remaining
    -- conditional expectation by optional sampling.
    calc
      μ[fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω | hσ.measurableSpace] =ᵐ[μ]
          μ[stoppedValue X ρ | hσ.measurableSpace] * stoppedValue X σ := by
            exact condExp_mul_of_stronglyMeasurable_right hσ_meas.stronglyMeasurable
              hProd_int hρ_int
      _ =ᵐ[μ] stoppedValue X σ * stoppedValue X σ := by
            exact
              ((hX.stoppedValue_ae_eq_condExp_of_le hρ hσ hσ_le_ρ hρ_le).symm.mul
                Filter.EventuallyEq.rfl)
      _ =ᵐ[μ] fun ω ↦ (stoppedValue X σ ω) ^ 2 := by
            filter_upwards with ω
            simp [pow_two]
  -- Integrate the conditional-expectation identity to collapse the mixed term.
  calc
    μ[fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω] =
        μ[μ[fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω | hσ.measurableSpace]] := by
          symm
          exact integral_condExp hσ.measurableSpace_le
    _ = μ[fun ω ↦ (stoppedValue X σ ω) ^ 2] := by
          exact integral_congr_ae hCond
    _ = μ[fun ω ↦ (stoppedValue X (truncatedStoppingTime τ n) ω) ^ 2] := by
          simp [σ]

/-- Helper for Exercise 10.2.1: the bounded stopped martingale increments have second moment
exactly equal to the corresponding square-variation increment. -/
lemma boundedStoppedSqIncrement_eq_squareVariationDiff
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) {n m : ℕ} (hnm : n ≤ m) :
    μ[fun ω ↦ (stoppedValue X (truncatedStoppingTime τ m) ω -
        stoppedValue X (truncatedStoppingTime τ n) ω) ^ 2] =
      μ[stoppedValue squareVariation (truncatedStoppingTime τ m)] -
        μ[stoppedValue squareVariation (truncatedStoppingTime τ n)] := by
  let σ : Ω → ℕ∞ := truncatedStoppingTime τ n
  let ρ : Ω → ℕ∞ := truncatedStoppingTime τ m
  have hσ : IsStoppingTime ℱ σ := hτ.min_const n
  have hρ : IsStoppingTime ℱ ρ := hτ.min_const m
  have hX_memLp : ∀ k, MemLp (X k) 2 μ := fun k ↦
    (memLp_two_iff_integrable_sq
      (((hX.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable)).2 (hXsq k)
  have hσ_memLp : MemLp (stoppedValue X σ) 2 μ := by
    exact memLp_stoppedValue hσ hX_memLp (fun ω ↦ min_le_right (τ ω : ℕ∞) n)
  have hρ_memLp : MemLp (stoppedValue X ρ) 2 μ := by
    exact memLp_stoppedValue hρ hX_memLp (fun ω ↦ min_le_right (τ ω : ℕ∞) m)
  have hσ_sq_int : Integrable (fun ω ↦ (stoppedValue X σ ω) ^ 2) μ := by
    simpa [pow_two] using hσ_memLp.integrable_sq
  have hρ_sq_int : Integrable (fun ω ↦ (stoppedValue X ρ ω) ^ 2) μ := by
    simpa [pow_two] using hρ_memLp.integrable_sq
  have hCross_int :
      Integrable (fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω) μ := by
    simpa [σ, ρ] using MemLp.integrable_mul hρ_memLp hσ_memLp
  have hSecondMoment :
      μ[fun ω ↦ (stoppedValue X ρ ω - stoppedValue X σ ω) ^ 2] =
        μ[fun ω ↦ (stoppedValue X ρ ω) ^ 2] -
          (2 : ℝ) * μ[fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω] +
          μ[fun ω ↦ (stoppedValue X σ ω) ^ 2] := by
    have hMid_int :
        Integrable
          (fun ω ↦
            (stoppedValue X ρ ω) ^ 2 -
              (2 : ℝ) * (stoppedValue X ρ ω * stoppedValue X σ ω)) μ := by
      exact hρ_sq_int.sub (hCross_int.const_mul (2 : ℝ))
    have hMid :
        μ[fun ω ↦
          (stoppedValue X ρ ω) ^ 2 -
            (2 : ℝ) * (stoppedValue X ρ ω * stoppedValue X σ ω)] =
          μ[fun ω ↦ (stoppedValue X ρ ω) ^ 2] -
            (2 : ℝ) * μ[fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω] := by
      calc
        μ[fun ω ↦
          (stoppedValue X ρ ω) ^ 2 -
            (2 : ℝ) * (stoppedValue X ρ ω * stoppedValue X σ ω)] =
            μ[fun ω ↦ (stoppedValue X ρ ω) ^ 2] -
              μ[fun ω ↦ (2 : ℝ) * (stoppedValue X ρ ω * stoppedValue X σ ω)] := by
                simpa using integral_sub' hρ_sq_int (hCross_int.const_mul 2)
        _ = μ[fun ω ↦ (stoppedValue X ρ ω) ^ 2] -
              (2 : ℝ) * μ[fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω] := by
                rw [integral_const_mul]
    have hDecomp :
        (fun ω ↦ (stoppedValue X ρ ω - stoppedValue X σ ω) ^ 2) =
          fun ω ↦
            ((stoppedValue X ρ ω) ^ 2 -
                (2 : ℝ) * (stoppedValue X ρ ω * stoppedValue X σ ω)) +
              (stoppedValue X σ ω) ^ 2 := by
      funext ω
      ring
    -- Expand the square and integrate term by term.
    calc
      μ[fun ω ↦ (stoppedValue X ρ ω - stoppedValue X σ ω) ^ 2] =
          μ[fun ω ↦
            ((stoppedValue X ρ ω) ^ 2 -
                (2 : ℝ) * (stoppedValue X ρ ω * stoppedValue X σ ω)) +
              (stoppedValue X σ ω) ^ 2] := by
            rw [hDecomp]
      _ = μ[fun ω ↦ (stoppedValue X ρ ω) ^ 2] -
            (2 : ℝ) * μ[fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω] +
            μ[fun ω ↦ (stoppedValue X σ ω) ^ 2] := by
            rw [integral_add hMid_int hσ_sq_int, hMid]
  have hSquareVariation_int : ∀ k, Integrable (squareVariation k) μ := by
    intro k
    have hSum_int :
        Integrable
          (fun ω ↦
            ∑ i ∈ Finset.range k,
              μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω) μ := by
      exact integrable_finset_sum (Finset.range k) fun i _ ↦
        (integrable_condExp : Integrable
          (μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i]) μ)
    exact hSum_int.congr (squareVariation_eq_sum_condExp_sq_increment hX hXsq k).symm
  have hσ_variation_int : Integrable (stoppedValue squareVariation σ) μ := by
    exact integrable_stoppedValue ℕ hσ hSquareVariation_int (fun ω ↦ min_le_right (τ ω : ℕ∞) n)
  have hρ_variation_int : Integrable (stoppedValue squareVariation ρ) μ := by
    exact integrable_stoppedValue ℕ hρ hSquareVariation_int (fun ω ↦ min_le_right (τ ω : ℕ∞) m)
  have hρ_squareSub :
      μ[fun ω ↦ (stoppedValue X ρ ω) ^ 2 - stoppedValue squareVariation ρ ω] =
        μ[fun ω ↦ (X 0 ω) ^ 2] := by
    simpa [ρ] using
      expectation_stoppedSquareSubVariation_eq_initial_truncation hX hXsq hτ m
  have hσ_squareSub :
      μ[fun ω ↦ (stoppedValue X σ ω) ^ 2 - stoppedValue squareVariation σ ω] =
        μ[fun ω ↦ (X 0 ω) ^ 2] := by
    simpa [σ] using
      expectation_stoppedSquareSubVariation_eq_initial_truncation hX hXsq hτ n
  have hCross :
      μ[fun ω ↦ stoppedValue X ρ ω * stoppedValue X σ ω] =
        μ[fun ω ↦ (stoppedValue X σ ω) ^ 2] := by
    simpa [σ, ρ] using
      boundedStoppedCrossTerm_eq_stoppedSquare hX hXsq hτ hnm
  have hρ_diff :
      μ[fun ω ↦ (stoppedValue X ρ ω) ^ 2] - μ[stoppedValue squareVariation ρ] =
        μ[fun ω ↦ (X 0 ω) ^ 2] := by
    calc
      μ[fun ω ↦ (stoppedValue X ρ ω) ^ 2] - μ[stoppedValue squareVariation ρ] =
          μ[fun ω ↦ (stoppedValue X ρ ω) ^ 2 - stoppedValue squareVariation ρ ω] := by
            symm
            exact integral_sub' hρ_sq_int hρ_variation_int
      _ = μ[fun ω ↦ (X 0 ω) ^ 2] := hρ_squareSub
  have hσ_diff :
      μ[fun ω ↦ (stoppedValue X σ ω) ^ 2] - μ[stoppedValue squareVariation σ] =
        μ[fun ω ↦ (X 0 ω) ^ 2] := by
    calc
      μ[fun ω ↦ (stoppedValue X σ ω) ^ 2] - μ[stoppedValue squareVariation σ] =
          μ[fun ω ↦ (stoppedValue X σ ω) ^ 2 - stoppedValue squareVariation σ ω] := by
            symm
            exact integral_sub' hσ_sq_int hσ_variation_int
      _ = μ[fun ω ↦ (X 0 ω) ^ 2] := hσ_squareSub
  -- The three scalar identities are linear in the stopped square moments, so `linarith`
  -- eliminates them directly.
  have hGoal :
      μ[fun ω ↦ (stoppedValue X ρ ω - stoppedValue X σ ω) ^ 2] =
        μ[stoppedValue squareVariation ρ] - μ[stoppedValue squareVariation σ] := by
    linarith [hSecondMoment, hρ_diff, hσ_diff, hCross]
  simpa [σ, ρ] using hGoal

/-- Helper for Exercise 10.2.1: every bounded truncation of the stopped canonical square
variation is almost surely dominated by the full stopped square variation at `τ`. -/
lemma stoppedSquareVariation_truncation_ae_le
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (n : ℕ) :
    stoppedValue squareVariation (truncatedStoppingTime τ n) ≤ᵐ[μ]
      stoppedValue squareVariation τ∞ := by
  have hsq :
      ∀ᵐ ω ∂μ, ∀ k : ℕ,
        (⟨X⟩[ℱ, μ]) k ω =
          ∑ i ∈ Finset.range k, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    -- Use the deterministic-time square-variation formula at all times once.
    exact ae_all_iff.2 fun k ↦ squareVariation_eq_sum_condExp_sq_increment hX hXsq k
  have hnonneg :
      ∀ᵐ ω ∂μ, ∀ i : ℕ,
        0 ≤ μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    -- Each conditional second moment is almost surely nonnegative.
    refine ae_all_iff.2 fun i ↦ ?_
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω ↦ sq_nonneg _)
  filter_upwards [hsq, hnonneg] with ω hsqω hnonnegω
  have hsum :
      ∑ i ∈ Finset.range (min (τ ω) n),
          μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω ≤
        ∑ i ∈ Finset.range (τ ω),
          μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    exact sumRangeMonotoneOfNonnegative (min_le_left _ _) hnonnegω
  have hleft :
      stoppedValue squareVariation (truncatedStoppingTime τ n) ω =
        ∑ i ∈ Finset.range (min (τ ω) n),
          μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    have hEval :
        stoppedValue squareVariation (truncatedStoppingTime τ n) ω =
          squareVariation (min (τ ω) n) ω :=
      congrFun (stoppedValue_truncated_eq_eval squareVariation n) ω
    -- The bounded stop is now a plain deterministic-time evaluation.
    simpa [hEval] using hsqω (min (τ ω) n)
  have hright :
      stoppedValue squareVariation τ∞ ω =
        ∑ i ∈ Finset.range (τ ω),
          μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
    have hEval :
        stoppedValue squareVariation τ∞ ω = squareVariation (τ ω) ω :=
      congrFun (stoppedValue_tau_eq_eval squareVariation) ω
    -- The full finite stop `τ` is the same deterministic evaluation at index `τ ω`.
    simpa [hEval] using hsqω (τ ω)
  rw [hleft, hright]
  exact hsum

/-- Helper for Exercise 10.2.1: along each path, the truncated stopping times `τ ∧ n` stabilize
to `τ` once `n` reaches the stopping index. -/
lemma truncatedStoppingTime_eventuallyEq (ω : Ω) :
    ∀ᶠ n in atTop, truncatedStoppingTime τ n ω = τ∞ ω := by
  -- After time `τ ω`, the minimum `min τ ω n` is exactly `τ ω`.
  refine Filter.eventually_atTop.2 ?_
  refine ⟨τ ω, fun n hn ↦ ?_⟩
  simp [truncatedStoppingTime, show ((τ ω : ℕ∞) ≤ n) by exact_mod_cast hn]

/-- Helper for Exercise 10.2.1: stopping a process at the truncations `τ ∧ n` is eventually
constant along every path, hence converges almost surely to the stop at `τ`. -/
lemma stoppedValue_truncation_ae_tendsto {β : Type*} [TopologicalSpace β] (u : ℕ → Ω → β) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ stoppedValue u (truncatedStoppingTime τ n) ω) atTop
        (𝓝 (stoppedValue u τ∞ ω)) := by
  -- Each path is eventually constant because the truncation indices stabilize to `τ ω`.
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  have hEq : ∀ᶠ n in atTop, truncatedStoppingTime τ n ω = τ∞ ω :=
    truncatedStoppingTime_eventuallyEq ω
  have hStoppedEq :
      (fun n ↦ stoppedValue u (truncatedStoppingTime τ n) ω) =ᶠ[atTop]
        fun _ ↦ stoppedValue u τ∞ ω := by
    filter_upwards [hEq] with n hn
    simp [stoppedValue, hn]
  exact Filter.Tendsto.congr' hStoppedEq.symm tendsto_const_nhds

/-- Helper for Exercise 10.2.1: the expectations of the stopped canonical square variation along
the bounded truncations converge to the expectation at `τ`. -/
lemma truncatedSquareVariation_expectation_tendsto
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    Tendsto (fun n ↦ μ[stoppedValue squareVariation (truncatedStoppingTime τ n)]) atTop
      (𝓝 μ[stoppedValue squareVariation τ∞]) := by
  have hSquareVariation_int : ∀ k, Integrable (squareVariation k) μ := by
    intro k
    have hSum_int :
        Integrable
          (fun ω ↦
            ∑ i ∈ Finset.range k,
              μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω) μ := by
      exact integrable_finset_sum (Finset.range k) fun i _ ↦
        (integrable_condExp : Integrable
          (μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i]) μ)
    -- The deterministic-time square variation is the finite sum of integrable conditional
    -- squared increments.
    exact hSum_int.congr (squareVariation_eq_sum_condExp_sq_increment hX hXsq k).symm
  have hTrunc_nonneg :
      ∀ n, ∀ᵐ ω ∂μ, 0 ≤ stoppedValue squareVariation (truncatedStoppingTime τ n) ω := by
    intro n
    filter_upwards [squareVariation_nonneg_ae hX hXsq] with ω hω
    have hEval :
        stoppedValue squareVariation (truncatedStoppingTime τ n) ω =
          squareVariation (min (τ ω) n) ω :=
      congrFun (stoppedValue_truncated_eq_eval squareVariation n) ω
    -- Reduce the bounded stop to deterministic evaluation before using pointwise nonnegativity.
    simpa [hEval] using hω (min (τ ω) n)
  have hBound :
      ∀ n, ∀ᵐ ω ∂μ,
        ‖stoppedValue squareVariation (truncatedStoppingTime τ n) ω‖ ≤
          stoppedValue squareVariation τ∞ ω := by
    intro n
    filter_upwards
      [hTrunc_nonneg n, stoppedSquareVariation_truncation_ae_le hX hXsq n] with ω
        h_nonneg h_le
    -- The truncation is nonnegative and dominated by the full stopped square variation.
    simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using h_le
  have hMeas :
      ∀ n, AEStronglyMeasurable (stoppedValue squareVariation (truncatedStoppingTime τ n)) μ := by
    intro n
    have hτn : IsStoppingTime ℱ (truncatedStoppingTime τ n) := hτ.min_const n
    exact
      (integrable_stoppedValue ℕ hτn hSquareVariation_int
        (fun ω ↦ min_le_right (τ ω : ℕ∞) n)).aestronglyMeasurable
  -- Route correction: use dominated convergence directly on the stopped square variation instead
  -- of trying to package this scalar limit through the later `L²` transport layer.
  simpa using
    tendsto_integral_of_dominated_convergence
      (stoppedValue squareVariation τ∞) hMeas hAτ hBound
      (stoppedValue_truncation_ae_tendsto squareVariation)

/-- Helper for Exercise 10.2.1: the centered bounded truncation `X_{τ ∧ n} - X_0` has second
moment exactly equal to the expectation of the truncated square variation. -/
lemma truncatedStoppedCenteredSquare_expectation_eq
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (n : ℕ) :
    μ[fun ω ↦ (stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω) ^ 2] =
      μ[stoppedValue squareVariation (truncatedStoppingTime τ n)] := by
  have hStoppedZero : stoppedValue X (truncatedStoppingTime τ 0) = X 0 := by
    -- The truncation at level `0` evaluates the process at deterministic time `0`.
    simpa using (stoppedValue_truncated_eq_eval X 0)
  have hVariationZero : stoppedValue squareVariation (truncatedStoppingTime τ 0) = 0 := by
    -- The canonical square variation starts at `0`, so the zero truncation vanishes.
    funext ω
    have hEval :
        stoppedValue squareVariation (truncatedStoppingTime τ 0) ω =
          squareVariation (min (τ ω) 0) ω :=
      congrFun (stoppedValue_truncated_eq_eval squareVariation 0) ω
    simpa [squareVariation_zero] using hEval
  -- Normalize the `m = 0` bounded increment identity and collapse the zero-time terms.
  simpa [hStoppedZero, hVariationZero] using
    (boundedStoppedSqIncrement_eq_squareVariationDiff hX hXsq hτ (Nat.zero_le n))

/-- Helper for Exercise 10.2.1: each centered bounded truncation belongs to `L²(μ)`. -/
lemma truncatedStoppedCentered_memLpTwo
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (n : ℕ) :
    MemLp (fun ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω) 2 μ := by
  have hX_memLp : ∀ k, MemLp (X k) 2 μ := fun k ↦
    (memLp_two_iff_integrable_sq
      (((hX.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable)).2 (hXsq k)
  let σn : Ω → ℕ∞ := truncatedStoppingTime τ n
  have hσn : IsStoppingTime ℱ σn := hτ.min_const n
  have hσn_le : ∀ ω, σn ω ≤ n := fun ω ↦ by
    simp [σn, truncatedStoppingTime]
  have hStopped : MemLp (stoppedValue X σn) 2 μ := by
    exact memLp_stoppedValue hσn hX_memLp hσn_le
  simpa [σn] using hStopped.sub (hX_memLp 0)

/-- Helper for Exercise 10.2.1: the centered bounded truncations converge in measure to the
centered stopped value at the finite stopping time `τ`. -/
lemma centeredStoppedTruncation_tendstoInMeasure
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) :
    TendstoInMeasure μ
      (fun n ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω)
      atTop
      (fun ω ↦ stoppedValue X τ∞ ω - X 0 ω) := by
  have hMeas :
      ∀ n, AEStronglyMeasurable
        (fun ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω) μ := by
    intro n
    exact (truncatedStoppedCentered_memLpTwo hX hXsq hτ n).aestronglyMeasurable
  have hAe :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω)
          atTop
          (𝓝 (stoppedValue X τ∞ ω - X 0 ω)) := by
    filter_upwards [stoppedValue_truncation_ae_tendsto X] with ω hω
    -- Subtract the fixed initial value after the stopped process has already stabilized.
    simpa using hω.sub tendsto_const_nhds
  -- The pathwise stabilization of the truncations upgrades directly to convergence in measure.
  exact tendstoInMeasure_of_tendsto_ae hMeas hAe

/-- Helper for Exercise 10.2.1: the truncated stopped square-variation expectations are bounded
above by the expectation at the full stopping time `τ`. -/
lemma truncatedSquareVariation_expectation_le
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) (n : ℕ) :
    μ[stoppedValue squareVariation (truncatedStoppingTime τ n)] ≤
      μ[stoppedValue squareVariation τ∞] := by
  have hSquareVariation_int : ∀ k, Integrable (squareVariation k) μ := by
    intro k
    have hSum_int :
        Integrable
          (fun ω ↦
            ∑ i ∈ Finset.range k,
              μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω) μ := by
      exact integrable_finset_sum (Finset.range k) fun i _ ↦
        (integrable_condExp : Integrable
          (μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i]) μ)
    -- The deterministic-time square variation is the finite sum of integrable conditional
    -- second moments.
    exact hSum_int.congr (squareVariation_eq_sum_condExp_sq_increment hX hXsq k).symm
  have hτn : IsStoppingTime ℱ (truncatedStoppingTime τ n) := hτ.min_const n
  have hτn_int : Integrable (stoppedValue squareVariation (truncatedStoppingTime τ n)) μ := by
    exact integrable_stoppedValue ℕ hτn hSquareVariation_int
      (fun ω ↦ min_le_right (τ ω : ℕ∞) n)
  -- The almost-sure monotonicity from the truncation order upgrades to the integral inequality.
  exact integral_mono_ae hτn_int hAτ
    (stoppedSquareVariation_truncation_ae_le hX hXsq n)

/-- Helper for Exercise 10.2.1: the pairwise second moments of the centered bounded truncations
decay to `0`, because the corresponding square-variation expectations form a Cauchy sequence. -/
lemma truncatedStoppedCenteredPairwiseSquare_expectation_tendsto_zero
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    Tendsto
      (fun nm : ℕ × ℕ ↦
        μ[fun ω ↦
          ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
            (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2])
      atTop (𝓝 0) := by
  let A : ℕ → ℝ := fun n ↦ μ[stoppedValue squareVariation (truncatedStoppingTime τ n)]
  have hA :
      Tendsto A atTop (𝓝 μ[stoppedValue squareVariation τ∞]) :=
    truncatedSquareVariation_expectation_tendsto hX hXsq hτ hAτ
  have hAbs :
      Tendsto (fun nm : ℕ × ℕ ↦ |A nm.1 - A nm.2|) atTop (𝓝 0) := by
    have hA_fst :
        Tendsto (fun nm : ℕ × ℕ ↦ A nm.1) atTop (𝓝 μ[stoppedValue squareVariation τ∞]) := by
      rw [← Filter.prod_atTop_atTop_eq]
      exact hA.comp tendsto_fst
    have hA_snd :
        Tendsto (fun nm : ℕ × ℕ ↦ A nm.2) atTop (𝓝 μ[stoppedValue squareVariation τ∞]) := by
      rw [← Filter.prod_atTop_atTop_eq]
      exact hA.comp tendsto_snd
    have hProd :
        Tendsto (fun nm : ℕ × ℕ ↦ (A nm.1, A nm.2)) atTop
          (𝓝 (μ[stoppedValue squareVariation τ∞], μ[stoppedValue squareVariation τ∞])) := by
      simpa [nhds_prod_eq] using hA_fst.prodMk hA_snd
    -- The scalar square-variation expectations share the same limit, so their pairwise
    -- absolute differences tend to `0`.
    simpa using
      ((((continuous_fst.sub continuous_snd).abs).continuousAt).tendsto.comp hProd)
  have hEq :
      (fun nm : ℕ × ℕ ↦
        μ[fun ω ↦
          ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
            (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2]) =
        fun nm : ℕ × ℕ ↦ |A nm.1 - A nm.2| := by
    funext nm
    rcases le_total nm.1 nm.2 with hnm | hmn
    · have hMoment :
          μ[fun ω ↦
            ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
              (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2] =
            A nm.2 - A nm.1 := by
        calc
          μ[fun ω ↦
            ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
              (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2] =
              μ[fun ω ↦
                (stoppedValue X (truncatedStoppingTime τ nm.2) ω -
                  stoppedValue X (truncatedStoppingTime τ nm.1) ω) ^ 2] := by
                congr 1
                funext ω
                ring
          _ = A nm.2 - A nm.1 := by
                simpa [A] using
                  (boundedStoppedSqIncrement_eq_squareVariationDiff hX hXsq hτ hnm)
      have hNonneg : 0 ≤ A nm.2 - A nm.1 := by
        rw [← hMoment]
        exact integral_nonneg fun ω ↦ sq_nonneg _
      have hNonpos : A nm.1 - A nm.2 ≤ 0 := by linarith
      simpa [abs_of_nonpos hNonpos] using hMoment
    · have hMoment :
          μ[fun ω ↦
            ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
              (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2] =
            A nm.1 - A nm.2 := by
        calc
          μ[fun ω ↦
            ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
              (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2] =
              μ[fun ω ↦
                (stoppedValue X (truncatedStoppingTime τ nm.1) ω -
                  stoppedValue X (truncatedStoppingTime τ nm.2) ω) ^ 2] := by
                congr 1
                funext ω
                ring
          _ = A nm.1 - A nm.2 := by
                simpa [A] using
                  (boundedStoppedSqIncrement_eq_squareVariationDiff hX hXsq hτ hmn)
      have hNonneg : 0 ≤ A nm.1 - A nm.2 := by
        rw [← hMoment]
        exact integral_nonneg fun ω ↦ sq_nonneg _
      simpa [abs_of_nonneg hNonneg] using hMoment
  -- The bounded stopped-increment identity turns the pairwise centered second moments into the
  -- pairwise absolute differences of the truncated square-variation expectations.
  rw [hEq]
  exact hAbs

/-- Helper for Exercise 10.2.1: the pairwise `L²` seminorms of the centered bounded truncations
decay to `0`, which is the exact bridge needed for the `Lp` Cauchy criterion. -/
lemma truncatedStoppedCenteredPairwiseELpNorm_tendsto_zero
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    Tendsto
      (fun nm : ℕ × ℕ ↦
        eLpNorm
          (fun ω ↦
            (stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
            (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω))
          2 μ)
      atTop (𝓝 0) := by
  have hSq :
      Tendsto
        (fun nm : ℕ × ℕ ↦
          μ[fun ω ↦
            ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
              (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2])
        atTop (𝓝 0) :=
    truncatedStoppedCenteredPairwiseSquare_expectation_tendsto_zero hX hXsq hτ hAτ
  have hSqrt :
      Tendsto
        (fun nm : ℕ × ℕ ↦
          Real.sqrt
            (μ[fun ω ↦
              ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
                (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2]))
        atTop (𝓝 0) := by
    -- Take square roots after the scalar second moments have already been shown to vanish.
    simpa using (Real.continuous_sqrt.tendsto 0).comp hSq
  have hEq :
      (fun nm : ℕ × ℕ ↦
        eLpNorm
          (fun ω ↦
            (stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
              (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω))
          2 μ) =
        fun nm : ℕ × ℕ ↦
          ENNReal.ofReal
            (Real.sqrt
              (μ[fun ω ↦
                ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
                  (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2])) := by
    funext nm
    let f : Ω → ℝ := fun ω ↦
      (stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
        (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)
    have hf : MemLp f 2 μ := by
      exact
        (truncatedStoppedCentered_memLpTwo hX hXsq hτ nm.1).sub
          (truncatedStoppedCentered_memLpTwo hX hXsq hτ nm.2)
    calc
      eLpNorm f 2 μ = ENNReal.ofReal (ENNReal.toReal (eLpNorm f 2 μ)) := by
        exact (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
      _ = ENNReal.ofReal (lpNorm f 2 μ) := by
        rw [toReal_eLpNorm hf.aestronglyMeasurable]
      _ = ENNReal.ofReal (Real.sqrt (μ[fun ω ↦ f ω ^ 2])) := by
        rw [lpNorm_two_eq_sqrt_integral_sq hf]
      _ = ENNReal.ofReal
            (Real.sqrt
              (μ[fun ω ↦
                ((stoppedValue X (truncatedStoppingTime τ nm.1) ω - X 0 ω) -
                  (stoppedValue X (truncatedStoppingTime τ nm.2) ω - X 0 ω)) ^ 2])) := by
        rfl
  -- Rewrite the `L²` seminorms through the canonical square-root formula and inherit the scalar
  -- second-moment limit.
  rw [hEq]
  simpa using ENNReal.tendsto_ofReal hSqrt

/-- Helper for Exercise 10.2.1: the centered bounded truncations converge in `L²(μ)` to the
centered stopped value at the true finite stopping time. -/
lemma truncatedStoppedCentered_tendstoInLpTwo
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    TendstoInLp 2 μ
      (fun n ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω)
      (fun ω ↦ stoppedValue X τ∞ ω - X 0 ω) := by
  let fSeq : ℕ → Ω → ℝ := fun n ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω
  have hMemLp : ∀ n, MemLp (fSeq n) 2 μ := by
    intro n
    simpa [fSeq] using truncatedStoppedCentered_memLpTwo hX hXsq hτ n
  let fLp : ℕ → Lp ℝ 2 μ := fun n ↦ (hMemLp n).toLp (fSeq n)
  have hPairwiseEq :
      (fun nm : ℕ × ℕ ↦ eLpNorm (⇑(fLp nm.1) - ⇑(fLp nm.2)) 2 μ) =
        fun nm : ℕ × ℕ ↦ eLpNorm (fSeq nm.1 - fSeq nm.2) 2 μ := by
    funext nm
    apply eLpNorm_congr_ae
    filter_upwards [hMemLp nm.1 |>.coeFn_toLp, hMemLp nm.2 |>.coeFn_toLp] with ω h₁ h₂
    simp [fLp, h₁, h₂]
  have hCauchy : CauchySeq fLp := by
    -- Route correction: first obtain the abstract `L²` limit in the canonical `Lp` space, then
    -- identify it with the concrete stopped value in measure.
    exact (Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm fLp).2 <| by
      simpa only [hPairwiseEq, fSeq] using
        truncatedStoppedCenteredPairwiseELpNorm_tendsto_zero hX hXsq hτ hAτ
  obtain ⟨f, hfLp⟩ := (lp_sequence_has_lp_limit_iff_cauchy fSeq hMemLp).2 hCauchy
  have hMeasure :
      TendstoInMeasure μ fSeq atTop (fun ω ↦ stoppedValue X τ∞ ω - X 0 ω) :=
    centeredStoppedTruncation_tendstoInMeasure hX hXsq hτ
  have hLimitAe :
      f =ᵐ[μ] (fun ω ↦ stoppedValue X τ∞ ω - X 0 ω) :=
    ae_eq_of_tendstoInLp_and_tendstoInMeasure hfLp hMeasure
  have hTargetMemLp :
      MemLp (fun ω ↦ stoppedValue X τ∞ ω - X 0 ω) 2 μ := by
    exact (memLp_congr_ae hLimitAe).1 hfLp.memLp
  refine (tendstoInLp_iff_tendsto_eLpNorm).2 ?_
  refine ⟨hMemLp, hTargetMemLp, ?_⟩
  have hNormEq :
      (fun n ↦ eLpNorm (fSeq n - fun ω ↦ stoppedValue X τ∞ ω - X 0 ω) 2 μ) =
        fun n ↦ eLpNorm (fSeq n - f) 2 μ := by
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hLimitAe] with ω hω
    simp [hω]
  -- Replace the abstract `Lp` limit by the concrete stopped value using a.e.-uniqueness.
  simpa only [hNormEq, fSeq] using hfLp.tendsto_eLpNorm

/-- Helper for Exercise 10.2.1: on a finite measure space, the centered bounded truncations also
converge to the centered stopped value in `L¹(μ)`. -/
lemma truncatedStoppedCentered_tendstoInL1
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    Tendsto
      (fun n ↦
        eLpNorm
          (fun ω ↦
            (stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω) -
              (stoppedValue X τ∞ ω - X 0 ω))
          1 μ)
      atTop (𝓝 0) := by
  let fSeq : ℕ → Ω → ℝ := fun n ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω
  let f : Ω → ℝ := fun ω ↦ stoppedValue X τ∞ ω - X 0 ω
  have hLpTwo : TendstoInLp 2 μ fSeq f :=
    truncatedStoppedCentered_tendstoInLpTwo hX hXsq hτ hAτ
  have hL2 :
      Tendsto (fun n ↦ eLpNorm (fSeq n - f) 2 μ) atTop (𝓝 0) :=
    hLpTwo.tendsto_eLpNorm
  have hBound :
      ∀ n,
        eLpNorm (fSeq n - f) 1 μ ≤
          eLpNorm (fSeq n - f) 2 μ *
            μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := by
    intro n
    -- Compare the `L¹` and `L²` seminorms on the finite measure space.
    simpa using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
        ((hLpTwo.memLpSeq n).sub hLpTwo.memLp).aestronglyMeasurable :
          eLpNorm (fSeq n - f) 1 μ ≤
            eLpNorm (fSeq n - f) 2 μ *
              μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal))
  have hFactorNeTop :
      μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    have hExponentNonneg :
        0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal := by
      norm_num
    exact ENNReal.rpow_ne_top_of_nonneg hExponentNonneg (by finiteness)
  have hUpper :
      Tendsto
        (fun n ↦
          eLpNorm (fSeq n - f) 2 μ *
            μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal))
        atTop (𝓝 0) := by
    simpa [mul_comm, zero_mul] using
      ENNReal.Tendsto.const_mul hL2 (Or.inr hFactorNeTop)
  -- Squeeze the `L¹` seminorms between `0` and the vanishing `L²` upper bound.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper ?_ ?_
  · intro n
    exact zero_le _
  · intro n
    exact hBound n

/-- Helper for Exercise 10.2.1: the squared `L²(μ)` norm of a real `Lp` class is the expectation
of the squared representative. -/
lemma toLpNormSq_eq_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = μ[fun ω ↦ (f ω) ^ 2] := by
  -- Rewrite the `L²` norm through the canonical inner product, then return to the concrete
  -- second moment of the representative.
  calc
    ‖hf.toLp f‖ ^ 2 = inner ℝ (hf.toLp f) (hf.toLp f) := by
      simp
    _ = μ[fun ω ↦ f ω * f ω] := by
      rw [inner_toLp_eq_integral_mul hf hf]
    _ = μ[fun ω ↦ (f ω) ^ 2] := by
      simp [sq]

/-- Helper for Exercise 10.2.1: the second moments of the centered bounded truncations converge
to the second moment at the true finite stopping time. -/
lemma truncatedStoppedCenteredSquare_expectation_tendsto
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    Tendsto
      (fun n ↦ μ[fun ω ↦ (stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω) ^ 2])
      atTop
      (𝓝 μ[fun ω ↦ (stoppedValue X τ∞ ω - X 0 ω) ^ 2]) := by
  let fSeq : ℕ → Ω → ℝ := fun n ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω
  let f : Ω → ℝ := fun ω ↦ stoppedValue X τ∞ ω - X 0 ω
  have hLp :
      TendstoInLp 2 μ fSeq f :=
    truncatedStoppedCentered_tendstoInLpTwo hX hXsq hτ hAτ
  have hMemLp : ∀ n, MemLp (fSeq n) 2 μ := by
    intro n
    simpa [fSeq] using truncatedStoppedCentered_memLpTwo hX hXsq hτ n
  have hf : MemLp f 2 μ := hLp.memLp
  have hNormSq :
      Tendsto (fun n ↦ ‖(hMemLp n).toLp (fSeq n)‖ ^ 2) atTop (𝓝 (‖hf.toLp f‖ ^ 2)) := by
    -- Pass to the canonical `Lp` limit first, then apply continuity of the squared norm.
    exact ((continuous_norm.pow 2).tendsto _).comp hLp.tendsto_toLp
  have hNormSq_eq :
      (fun n ↦ ‖(hMemLp n).toLp (fSeq n)‖ ^ 2) =
        fun n ↦ μ[fun ω ↦ (fSeq n ω) ^ 2] := by
    funext n
    exact toLpNormSq_eq_integral_sq (hMemLp n)
  have hLimit_eq : ‖hf.toLp f‖ ^ 2 = μ[fun ω ↦ (f ω) ^ 2] :=
    toLpNormSq_eq_integral_sq hf
  -- The owner-level `Lp` convergence now matches the scalar second-moment statement exactly.
  rw [hNormSq_eq, hLimit_eq] at hNormSq
  simpa [fSeq, f] using hNormSq

/-- Helper for Exercise 10.2.1: every centered bounded truncation has expectation `0`. -/
lemma truncatedStoppedCentered_integral_eq_zero
    (hX : Martingale X ℱ μ) (hτ : IsStoppingTime ℱ τ∞) (n : ℕ) :
    μ[fun ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω] = 0 := by
  have hStopped_int :
      Integrable (stoppedValue X (truncatedStoppingTime τ n)) μ := by
    exact integrable_stoppedValue ℕ (hτ.min_const n) hX.integrable
      (fun ω ↦ min_le_right (τ ω : ℕ∞) n)
  have hIntegral_sub :
      ∫ ω, (stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω) ∂μ =
        ∫ ω, stoppedValue X (truncatedStoppingTime τ n) ω ∂μ - ∫ ω, X 0 ω ∂μ := by
    simpa using integral_sub' hStopped_int (hX.integrable 0)
  -- Subtract the initial expectation from the bounded optional-sampling identity.
  calc
    μ[fun ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω] =
        ∫ ω, stoppedValue X (truncatedStoppingTime τ n) ω ∂μ - ∫ ω, X 0 ω ∂μ := hIntegral_sub
    _ = 0 := by
          rw [expectation_stoppedValue_eq_initial_truncation hX hτ n, sub_self]

end TruncationHelpers

-- Proof sketch: prove the identity first for the bounded truncations `τ ∧ n` and then pass to
-- the finite stopping time `τ` by dominated convergence for the canonical square variation.
/-- Continuation of Exercise 10.2.1 (1): source clause (i.1). If the stopped square variation
`⟨X⟩_τ` is integrable, then the expected squared increment of the martingale up to the finite
stopping time `τ` equals the expectation of the stopped square variation. -/
theorem expectation_stopped_sq_sub_eq_expectation_stopped_squareVariation
    (τ : Ω → ℕ) [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : ℕ∞)))
    (hSquareVariationτ : Integrable (stoppedValue (⟨X⟩[ℱ, μ]) (fun ω ↦ (τ ω : ℕ∞))) μ) :
    μ[fun ω ↦ (stoppedValue X (fun ω ↦ (τ ω : ℕ∞)) ω - X 0 ω) ^ 2] =
      μ[stoppedValue (⟨X⟩[ℱ, μ]) (fun ω ↦ (τ ω : ℕ∞))] := by
  have hMoment := truncatedStoppedCenteredSquare_expectation_tendsto hX hXsq hτ hSquareVariationτ
  have hVariation := truncatedSquareVariation_expectation_tendsto hX hXsq hτ hSquareVariationτ
  have hMomentEq :
      (fun n ↦ μ[stoppedValue squareVariation (truncatedStoppingTime τ n)]) =
        fun n ↦ μ[fun ω ↦ (stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω) ^ 2] := by
    funext n
    exact (truncatedStoppedCenteredSquare_expectation_eq hX hXsq hτ n).symm
  have hMoment' :
      Tendsto
        (fun n ↦ μ[stoppedValue squareVariation (truncatedStoppingTime τ n)])
        atTop
        (𝓝 μ[fun ω ↦ (stoppedValue X (fun ω ↦ (τ ω : ℕ∞)) ω - X 0 ω) ^ 2]) := by
    -- Replace the scalar second moments of the truncations by the matching square-variation
    -- expectations before comparing the two limits.
    rw [hMomentEq]
    exact hMoment
  -- The two limit descriptions of the same truncation sequence force the claimed identity.
  simpa using tendsto_nhds_unique hMoment' hVariation

-- Proof sketch: combine clause (1) for the canonical square variation with the bounded
-- optional-sampling identities for `τ ∧ n` and the resulting `L¹` control of the stopped
-- martingale.
/-- Continuation of Exercise 10.2.1 (2): source clause (i.2). Under the same integrability
hypothesis on `⟨X⟩_τ`, the
expected value of the martingale at the finite stopping time `τ` agrees with the initial
expectation. -/
theorem expectation_stopped_martingale_eq_initial_of_squareVariation_integrable
    (τ : Ω → ℕ) [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : ℕ∞)))
    (hSquareVariationτ : Integrable (stoppedValue (⟨X⟩[ℱ, μ]) (fun ω ↦ (τ ω : ℕ∞))) μ) :
    μ[stoppedValue X (fun ω ↦ (τ ω : ℕ∞))] = μ[X 0] := by
  have hLpTwo := truncatedStoppedCentered_tendstoInLpTwo hX hXsq hτ hSquareVariationτ
  have hf_integrable :
      Integrable (fun ω ↦ stoppedValue X (fun ω ↦ (τ ω : ℕ∞)) ω - X 0 ω) μ := by
    -- Lower the limit from `L²` to `L¹` to access continuity of the integral.
    exact memLp_one_iff_integrable.1 <| hLpTwo.memLp.mono_exponent (by norm_num)
  have hSeq_integrable :
      ∀ n, Integrable (fun ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω) μ := by
    intro n
    exact memLp_one_iff_integrable.1 <|
      (truncatedStoppedCentered_memLpTwo hX hXsq hτ n).mono_exponent (by norm_num)
  have hCentered :
      Tendsto
        (fun n ↦ μ[fun ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω])
        atTop
        (𝓝 μ[fun ω ↦ stoppedValue X (fun ω ↦ (τ ω : ℕ∞)) ω - X 0 ω]) := by
    -- Apply continuity of the Bochner integral after the centered truncations converge in `L¹`.
    exact MeasureTheory.tendsto_integral_of_L1'
      (fun ω ↦ stoppedValue X (fun ω ↦ (τ ω : ℕ∞)) ω - X 0 ω) hf_integrable
      (Filter.Eventually.of_forall hSeq_integrable)
      (truncatedStoppedCentered_tendstoInL1 hX hXsq hτ hSquareVariationτ)
  have hCenteredZeroSeq :
      Tendsto
        (fun n ↦ μ[fun ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω])
        atTop
        (𝓝 (0 : ℝ)) := by
    -- Every bounded truncation already has mean zero by bounded optional sampling.
    have hZeroEq :
        (fun n ↦ μ[fun ω ↦ stoppedValue X (truncatedStoppingTime τ n) ω - X 0 ω]) =
          fun _ : ℕ ↦ (0 : ℝ) := by
      funext n
      exact truncatedStoppedCentered_integral_eq_zero hX hτ n
    rw [hZeroEq]
    exact tendsto_const_nhds
  have hCenteredZero :
      μ[fun ω ↦ stoppedValue X (fun ω ↦ (τ ω : ℕ∞)) ω - X 0 ω] = 0 :=
    tendsto_nhds_unique hCentered hCenteredZeroSeq
  have hStopped_int :
      Integrable (stoppedValue X (fun ω ↦ (τ ω : ℕ∞))) μ := by
    have hSum :
        Integrable (fun ω ↦ (stoppedValue X (fun ω ↦ (τ ω : ℕ∞)) ω - X 0 ω) + X 0 ω) μ :=
      hf_integrable.add (hX.integrable 0)
    simpa [sub_add_cancel] using hSum
  have hDifference :
      μ[stoppedValue X (fun ω ↦ (τ ω : ℕ∞))] - μ[X 0] = 0 := by
    calc
      μ[stoppedValue X (fun ω ↦ (τ ω : ℕ∞))] - μ[X 0] =
          ∫ ω, (stoppedValue X (fun ω ↦ (τ ω : ℕ∞)) ω - X 0 ω) ∂μ := by
        symm
        exact integral_sub' hStopped_int (hX.integrable 0)
      _ = 0 := by
        simpa using hCenteredZero
  exact sub_eq_zero.mp hDifference

end

section Counterexample

/-- Helper for Exercise 10.2.1: the counterexample uses the fair geometric parameter `1 / 2`. -/
private theorem counterexampleHalfPos : 0 < (1 / 2 : ℝ) := by
  norm_num

/-- Helper for Exercise 10.2.1: the counterexample geometric parameter is at most `1`. -/
private theorem counterexampleHalfLeOne : (1 / 2 : ℝ) ≤ 1 := by
  norm_num

/-- Helper for Exercise 10.2.1: the `NNReal` parameter `1 / 2` is strictly less than `1`. -/
private theorem counterexampleHalfLtOne : (1 / 2 : NNReal) < 1 := by
  norm_num

/-- Helper for Exercise 10.2.1: the geometric law on `ℕ` with parameter `1 / 2`. -/
noncomputable def counterexampleMeasure : Measure ℕ :=
  geometricMeasure counterexampleHalfPos counterexampleHalfLeOne

/-- Helper for Exercise 10.2.1: the geometric law with parameter `1 / 2` is a
probability measure. -/
instance counterexampleMeasure_isProbabilityMeasure : IsProbabilityMeasure counterexampleMeasure :=
  isProbabilityMeasure_geometricMeasure counterexampleHalfPos counterexampleHalfLeOne

/-- Helper for Exercise 10.2.1: the filtration reveals the truncated waiting time
`ω ↦ min ω n`. -/
noncomputable def counterexampleFiltration : Filtration ℕ (inferInstance : MeasurableSpace ℕ) :=
  { seq := fun n ↦ MeasurableSpace.comap (fun ω : ℕ ↦ min ω n) inferInstance
    mono' := by
      intro n m hnm s hs
      rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨t, ht, rfl⟩
      refine MeasurableSpace.measurableSet_comap.2 ?_
      refine ⟨{k : ℕ | min k n ∈ t}, (Set.to_countable _).measurableSet, ?_⟩
      ext ω
      simp [Nat.min_assoc, Nat.min_eq_right hnm]
    le' := by
      intro n s hs
      exact Set.to_countable s |>.measurableSet }

/-- Helper for Exercise 10.2.1: the finite stopping time `τ(ω) = ω + 1`. -/
def counterexampleStoppingTime : ℕ → ℕ := fun ω ↦ ω + 1

/-- Helper for Exercise 10.2.1: the finite stopping time viewed as an `ℕ∞`-valued
stopping time. -/
def counterexampleStoppingTimeInf : ℕ → ℕ∞ := fun ω ↦ (counterexampleStoppingTime ω : ℕ∞)

/-- Helper for Exercise 10.2.1: the Petersburg-style martingale on the geometric
waiting-time space. -/
def counterexampleProcess : ℕ → ℕ → ℝ :=
  fun n ω ↦ if ω < n then 1 else 1 - (2 : ℝ) ^ n

/-- Helper for Exercise 10.2.1: the geometric singleton mass is the explicit power
`(1 / 2)^(n + 1)`. -/
private theorem counterexampleMeasure_apply_singleton (n : ℕ) :
    counterexampleMeasure ({n} : Set ℕ) = (1 / 2 : ENNReal) ^ (n + 1) := by
  have hhalf : (1 - (1 / 2 : NNReal)) = (1 / 2 : NNReal) := by
    apply NNReal.coe_injective
    norm_num [NNReal.coe_sub counterexampleHalfLtOne.le]
  have hhalfENN : ((1 / 2 : NNReal) : ENNReal) = (1 / 2 : ENNReal) := by
    norm_num
  -- Specialize the owner singleton-mass formula for the geometric law at `p = 1 / 2`.
  calc
    counterexampleMeasure ({n} : Set ℕ) =
        ENNReal.ofReal (geometricMass (1 / 2 : NNReal) n) := by
          simpa [counterexampleMeasure] using
            (geometricMeasure_apply_singleton counterexampleHalfPos counterexampleHalfLtOne n)
    _ = ENNReal.ofReal (((1 / 2 : NNReal) ^ n * (1 / 2 : NNReal) : NNReal)) := by
          rw [geometricMass, failurePrefixMass, hhalf]
    _ = ENNReal.ofReal (((1 / 2 : NNReal) ^ (n + 1) : NNReal)) := by
          rw [pow_succ]
    _ = (((1 / 2 : NNReal) ^ (n + 1) : NNReal) : ENNReal) := by
          simp
    _ = (((1 / 2 : NNReal) : ENNReal) ^ (n + 1)) := by
          rfl
    _ = (1 / 2 : ENNReal) ^ (n + 1) := by
          exact congrArg (fun z : ENNReal ↦ z ^ (n + 1)) hhalfENN

/-- Helper for Exercise 10.2.1: the singleton masses of the geometric counterexample expressed as
real numbers. -/
private theorem counterexampleMeasureReal_singleton (n : ℕ) :
    counterexampleMeasure.real ({n} : Set ℕ) = (1 / 2 : ℝ) ^ (n + 1) := by
  -- Convert the explicit `ENNReal` singleton mass into the real-valued measure.
  rw [Measure.real_def]
  rw [counterexampleMeasure_apply_singleton]
  norm_num

/-- Helper for Exercise 10.2.1: the upper tail `{m | n ≤ m}` has geometric mass `(1 / 2)^n`. -/
private theorem counterexampleMeasure_Ici (n : ℕ) :
    counterexampleMeasure (Set.Ici n) = (1 / 2 : ENNReal) ^ n := by
  -- Sum the singleton masses on the finite prefix and convert the complement to the tail mass.
  have hsum :
      counterexampleMeasure.real (Set.Iio n) =
        ∑ k ∈ Finset.range n, counterexampleMeasure.real ({k} : Set ℕ) := by
    symm
    simpa using
      (sum_measureReal_singleton (Finset.range n) :
        (∑ k ∈ Finset.range n, counterexampleMeasure.real ({k} : Set ℕ)) =
          counterexampleMeasure.real (Finset.range n))
  have hsum' :
      counterexampleMeasure.real (Set.Iio n) =
        ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) := by
    rw [hsum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    exact counterexampleMeasureReal_singleton k
  have hIio :
      counterexampleMeasure.real (Set.Iio n) = 1 - (1 / 2 : ℝ) ^ n := by
    have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
      norm_num
    rw [hsum']
    calc
      ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) =
          (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) * (1 / 2 : ℝ) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            rw [pow_succ', mul_comm]
      _ = (∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k) * (1 - (1 / 2 : ℝ)) := by
            rw [hhalf]
      _ = 1 - (1 / 2 : ℝ) ^ n := by
            simpa using (geom_sum_mul_neg (1 / 2 : ℝ) n)
  have hreal :
      counterexampleMeasure.real (Set.Ici n) = (1 / 2 : ℝ) ^ n := by
    rw [show Set.Ici n = (Set.Iio n)ᶜ by
          ext ω
          simp,
      measureReal_compl measurableSet_Iio, probReal_univ, hIio]
    ring
  exact
    (ENNReal.toReal_eq_toReal_iff'
      (ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) (by simp))) (by simp)).mp <|
      by simpa [Measure.real_def] using hreal

/-- Helper for Exercise 10.2.1: the strict tail `{m | n < m}` has mass `(1 / 2)^(n + 1)`. -/
private theorem counterexampleMeasure_Ioi (n : ℕ) :
    counterexampleMeasure (Set.Ioi n) = (1 / 2 : ENNReal) ^ (n + 1) := by
  simpa [Set.Ioi, Nat.succ_eq_add_one] using counterexampleMeasure_Ici (n + 1)

/-- Helper for Exercise 10.2.1: every time slice of the truncated-index process is measurable for
the counterexample filtration. -/
private theorem counterexampleTruncatedIndex_measurable (n : ℕ) :
    Measurable[counterexampleFiltration n] (fun ω : ℕ ↦ min ω n) :=
  comap_measurable _

/-- Helper for Exercise 10.2.1: the counterexample process at time `n` depends only on the
truncated waiting time `min ω n`, hence is `ℱ_n`-measurable. -/
private theorem counterexampleProcess_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable[counterexampleFiltration n] (counterexampleProcess n) := by
  -- Rewrite `Xₙ` as a function of the truncated index and compose with the comap-measurable map.
  let g : ℕ → ℝ := fun k ↦ if k < n then 1 else 1 - (2 : ℝ) ^ n
  have hg : Measurable g := measurable_of_countable g
  have hEq : counterexampleProcess n = g ∘ fun ω : ℕ ↦ min ω n := by
    funext ω
    simp [counterexampleProcess, g]
  rw [hEq]
  exact (hg.comp (counterexampleTruncatedIndex_measurable n)).stronglyMeasurable

/-- Helper for Exercise 10.2.1: the counterexample process is strongly adapted to the truncated
waiting-time filtration. -/
private theorem counterexampleProcess_stronglyAdapted :
    StronglyAdapted counterexampleFiltration counterexampleProcess := by
  intro n
  exact counterexampleProcess_stronglyMeasurable n

/-- Counterexample helper: the explicit geometric waiting time `counterexampleStoppingTimeInf`
is a finite stopping time for the counterexample filtration. -/
theorem counterexampleStoppingTime_isStoppingTime :
    IsStoppingTime counterexampleFiltration counterexampleStoppingTimeInf := by
  -- Route correction: identify the stopping event as the concrete interval `Set.Iio n`.
  intro n
  have hstop :
      {ω | counterexampleStoppingTimeInf ω ≤ n} = Set.Iio n := by
    ext ω
    change ((ω + 1 : ℕ∞) ≤ (n : ℕ∞)) ↔ ω < n
    exact_mod_cast (Nat.succ_le_iff : ω + 1 ≤ n ↔ ω < n)
  have hpre :
      (fun ω : ℕ ↦ min ω n) ⁻¹' Set.Iio n = Set.Iio n := by
    ext ω
    by_cases hω : ω < n
    · simp [hω, Nat.min_eq_left (Nat.le_of_lt hω)]
    · have hle : n ≤ ω := Nat.not_lt.mp hω
      simp [hω, Nat.min_eq_right hle]
  have htarget :
      {ω | counterexampleStoppingTimeInf ω ≤ n} = (fun ω : ℕ ↦ min ω n) ⁻¹' Set.Iio n :=
    hstop.trans hpre.symm
  have hmeas :
      MeasurableSet[counterexampleFiltration n] ((fun ω : ℕ ↦ min ω n) ⁻¹' Set.Iio n) :=
    (counterexampleTruncatedIndex_measurable n) ((Set.to_countable (Set.Iio n)).measurableSet)
  exact htarget.symm ▸ hmeas

/-- Helper for Exercise 10.2.1: the counterexample process starts from `0`. -/
private theorem counterexampleProcess_zero : counterexampleProcess 0 = fun _ ↦ (0 : ℝ) := by
  funext ω
  simp [counterexampleProcess]

/-- Helper for Exercise 10.2.1: the geometric tail masses expressed as real measures. -/
private theorem counterexampleMeasureReal_Ici (n : ℕ) :
    counterexampleMeasure.real (Set.Ici n) = (1 / 2 : ℝ) ^ n := by
  rw [Measure.real_def, counterexampleMeasure_Ici]
  norm_num

/-- Helper for Exercise 10.2.1: the strict geometric tail masses expressed as real measures. -/
private theorem counterexampleMeasureReal_Ioi (n : ℕ) :
    counterexampleMeasure.real (Set.Ioi n) = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [Measure.real_def, counterexampleMeasure_Ioi]
  norm_num

/-- Helper for Exercise 10.2.1: the lower interval `{ω | ω < n}` has mass `1 - 2^{-n}`. -/
private theorem counterexampleMeasureReal_Iio (n : ℕ) :
    counterexampleMeasure.real (Set.Iio n) = 1 - (1 / 2 : ℝ) ^ n := by
  have hComp : Set.Iio n = (Set.Ici n)ᶜ := by
    ext ω
    simp
  rw [hComp, measureReal_compl measurableSet_Ici, probReal_univ, counterexampleMeasureReal_Ici]

end Counterexample

-- Proof sketch: build an explicit square-integrable martingale and a finite stopping time `τ`
-- whose stopped canonical square variation has infinite expectation and for which both
-- identities from `(10.7)` fail.
/-- Helper for Exercise 10.2.1: each time slice of the counterexample process is integrable because
it is piecewise constant on a probability space. -/
private theorem counterexampleProcess_integrable (n : ℕ) :
    Integrable (counterexampleProcess n) counterexampleMeasure := by
  let A : Set ℕ := Set.Iio n
  have hEq :
      counterexampleProcess n =
        A.piecewise (fun _ : ℕ ↦ (1 : ℝ)) (fun _ ↦ 1 - (2 : ℝ) ^ n) := by
    funext ω
    by_cases hω : ω < n
    · simp [counterexampleProcess, A, Set.piecewise, hω]
    · simp [counterexampleProcess, A, Set.piecewise, hω]
  have hleft :
      IntegrableOn (fun _ : ℕ ↦ (1 : ℝ)) A counterexampleMeasure :=
    integrableOn_const (measure_ne_top counterexampleMeasure A) (by simp)
  have hright :
      IntegrableOn (fun _ : ℕ ↦ 1 - (2 : ℝ) ^ n) Aᶜ counterexampleMeasure :=
    integrableOn_const (measure_ne_top counterexampleMeasure Aᶜ) (by simp)
  rw [hEq]
  exact Integrable.piecewise measurableSet_Iio hleft hright

/-- Helper for Exercise 10.2.1: the one-step increment of the counterexample process is `0` before
time `n`, equals `2^n` at the atom `{n}`, and equals `-2^n` on the strict tail `{ω | n < ω}`. -/
private theorem counterexampleIncrement_eq (n : ℕ) :
    (fun ω ↦ counterexampleProcess (n + 1) ω - counterexampleProcess n ω) =
      fun ω ↦ if ω = n then (2 : ℝ) ^ n else if n < ω then -((2 : ℝ) ^ n) else 0 := by
  funext ω
  by_cases hω : ω < n
  · have hω' : ω < n + 1 := Nat.lt_succ_of_lt hω
    simp [counterexampleProcess, hω, hω', Nat.ne_of_lt hω, Nat.not_lt_of_ge (Nat.le_of_lt hω)]
  · by_cases hEq : ω = n
    · subst hEq
      simp [counterexampleProcess]
    · have hne : n ≠ ω := fun h ↦ hEq h.symm
      have hgt : n < ω := lt_of_le_of_ne (Nat.not_lt.mp hω) hne
      have hω' : ¬ ω < n + 1 := by
        exact not_lt.mpr (Nat.succ_le_of_lt hgt)
      simp [counterexampleProcess, hω, hω', hEq, hgt]
      ring

/-- Helper for Exercise 10.2.1: the increment over the tail atom `Set.Ici n` has zero integral
under the geometric counterexample law. -/
private theorem counterexampleIncrement_setIntegral_Ici_eq_zero (n : ℕ) :
    ∫ ω in Set.Ici n,
      (counterexampleProcess (n + 1) ω - counterexampleProcess n ω) ∂counterexampleMeasure = 0 := by
  let inc : ℕ → ℝ := fun ω ↦ counterexampleProcess (n + 1) ω - counterexampleProcess n ω
  -- Split the tail into the atom `{n}` and the strict tail `Set.Ioi n`.
  have hsplit : Set.Ici n = ({n} : Set ℕ) ∪ Set.Ioi n := by
    ext ω
    constructor
    · intro hω
      rcases Nat.eq_or_lt_of_le hω with rfl | hgt
      · exact Or.inl rfl
      · exact Or.inr hgt
    · intro hω
      rcases hω with hω | hω
      · have hEq : ω = n := by
          simpa using hω
        exact hEq.symm.le
      · exact Nat.le_of_lt hω
  have hdisj : Disjoint ({n} : Set ℕ) (Set.Ioi n) := by
    refine Set.disjoint_left.2 ?_
    intro ω hω hω'
    have hEq : ω = n := by simpa using hω
    simpa [hEq] using hω'
  have hsingle :
      ∫ ω in ({n} : Set ℕ), inc ω ∂counterexampleMeasure =
        counterexampleMeasure.real ({n} : Set ℕ) * (2 : ℝ) ^ n := by
    have hEq :
        ∫ ω in ({n} : Set ℕ), inc ω ∂counterexampleMeasure =
          ∫ ω in ({n} : Set ℕ), (2 : ℝ) ^ n ∂counterexampleMeasure := by
      refine setIntegral_congr_ae (MeasurableSet.singleton n) (Filter.Eventually.of_forall ?_)
      intro ω hω
      have : ω = n := by simpa using hω
      subst this
      simp [inc, counterexampleProcess]
    rw [hEq]
    simpa [smul_eq_mul, mul_comm] using
      (setIntegral_const ((2 : ℝ) ^ n) :
        ∫ ω in ({n} : Set ℕ), (2 : ℝ) ^ n ∂counterexampleMeasure =
          counterexampleMeasure.real ({n} : Set ℕ) • (2 : ℝ) ^ n)
  have htail :
      ∫ ω in Set.Ioi n, inc ω ∂counterexampleMeasure =
        counterexampleMeasure.real (Set.Ioi n) * (-((2 : ℝ) ^ n)) := by
    have hEq :
        ∫ ω in Set.Ioi n, inc ω ∂counterexampleMeasure =
          ∫ ω in Set.Ioi n, -((2 : ℝ) ^ n) ∂counterexampleMeasure := by
      refine setIntegral_congr_ae measurableSet_Ioi (Filter.Eventually.of_forall ?_)
      intro ω hω
      have hgt : n < ω := by simpa using hω
      have hne : ω ≠ n := ne_of_gt hgt
      simp [inc, counterexampleIncrement_eq, hne, hgt]
    rw [hEq]
    simpa [smul_eq_mul, mul_comm] using
      (setIntegral_const (-((2 : ℝ) ^ n)) :
        ∫ ω in Set.Ioi n, -((2 : ℝ) ^ n) ∂counterexampleMeasure =
          counterexampleMeasure.real (Set.Ioi n) • (-((2 : ℝ) ^ n)))
  calc
    ∫ ω in Set.Ici n, inc ω ∂counterexampleMeasure =
            ∫ ω in ({n} : Set ℕ), inc ω ∂counterexampleMeasure +
              ∫ ω in Set.Ioi n, inc ω ∂counterexampleMeasure := by
            rw [hsplit]
            exact setIntegral_union hdisj measurableSet_Ioi
              (((counterexampleProcess_integrable (n + 1)).sub
                (counterexampleProcess_integrable n)).integrableOn)
              ((counterexampleProcess_integrable (n + 1)).sub
                (counterexampleProcess_integrable n)).integrableOn
    _ = counterexampleMeasure.real ({n} : Set ℕ) * (2 : ℝ) ^ n +
          counterexampleMeasure.real (Set.Ioi n) * (-((2 : ℝ) ^ n)) := by
            rw [hsingle, htail]
    _ = 0 := by
          rw [counterexampleMeasureReal_singleton, counterexampleMeasureReal_Ioi]
          ring

/-- Helper for Exercise 10.2.1: every one-step increment has conditional expectation `0` with
respect to the current counterexample filtration level. -/
private theorem counterexampleIncrement_condExp_ae_eq_zero (n : ℕ) :
    counterexampleMeasure[fun ω ↦ counterexampleProcess (n + 1) ω - counterexampleProcess n ω
      | counterexampleFiltration n] =ᵐ[counterexampleMeasure] 0 := by
  let inc : ℕ → ℝ := fun ω ↦ counterexampleProcess (n + 1) ω - counterexampleProcess n ω
  have hinc_int : Integrable inc counterexampleMeasure := by
    exact (counterexampleProcess_integrable (n + 1)).sub (counterexampleProcess_integrable n)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (counterexampleFiltration.le n) hinc_int ?_ ?_
    (stronglyMeasurable_zero.aestronglyMeasurable)).symm
  · intro s hs hμs
    exact integrableOn_const hμs.ne (by simp)
  · intro s hs hμs
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    by_cases hn : n ∈ t
    · have hsplit :
          (fun ω : ℕ ↦ min ω n) ⁻¹' t =
            ((fun ω : ℕ ↦ min ω n) ⁻¹' t ∩ Set.Iio n) ∪ Set.Ici n := by
        ext ω
        by_cases hω : ω < n
        · simp [hω]
        · have hle : n ≤ ω := Nat.not_lt.mp hω
          have hmin : min ω n = n := Nat.min_eq_right hle
          simp [hω, hle, hn]
      have hdisj :
          Disjoint (((fun ω : ℕ ↦ min ω n) ⁻¹' t) ∩ Set.Iio n) (Set.Ici n) := by
        rw [Set.disjoint_left]
        intro ω hω hω'
        exact Nat.not_lt_of_le hω' hω.2
      have hsmall_meas :
          MeasurableSet (((fun ω : ℕ ↦ min ω n) ⁻¹' t) ∩ Set.Iio n) :=
        (Set.to_countable _).measurableSet
      have hsmall_zero :
          ∫ ω in ((fun ω : ℕ ↦ min ω n) ⁻¹' t) ∩ Set.Iio n, inc ω ∂counterexampleMeasure = 0 := by
        have hEq :
            ∫ ω in ((fun ω : ℕ ↦ min ω n) ⁻¹' t) ∩ Set.Iio n, inc ω ∂counterexampleMeasure =
              ∫ ω in ((fun ω : ℕ ↦ min ω n) ⁻¹' t) ∩ Set.Iio n, (0 : ℝ) ∂counterexampleMeasure := by
          refine setIntegral_congr_ae hsmall_meas (Filter.Eventually.of_forall ?_)
          intro ω hω
          simp [inc, counterexampleIncrement_eq, Nat.ne_of_lt hω.2,
            Nat.not_lt_of_ge (Nat.le_of_lt hω.2)]
        simpa using hEq
      have hinc_zero :
        ∫ ω in (fun ω : ℕ ↦ min ω n) ⁻¹' t, inc ω ∂counterexampleMeasure =
            0 := by
          have hsmall_inter :
              ((((fun ω : ℕ ↦ min ω n) ⁻¹' t) ∩ Set.Iio n) ∪ Set.Ici n) ∩ Set.Iio n =
                ((fun ω : ℕ ↦ min ω n) ⁻¹' t) ∩ Set.Iio n := by
            ext ω
            constructor
            · intro hω
              rcases hω with ⟨hω, hlt⟩
              rcases hω with hω | hω
              · exact hω
              · exact False.elim (Nat.not_lt_of_le hω hlt)
            · intro hω
              exact ⟨Or.inl hω, hω.2⟩
          calc
            ∫ ω in (fun ω : ℕ ↦ min ω n) ⁻¹' t, inc ω ∂counterexampleMeasure =
                ∫ ω in ((fun ω : ℕ ↦ min ω n) ⁻¹' t) ∩ Set.Iio n, inc ω ∂counterexampleMeasure +
                  ∫ ω in Set.Ici n, inc ω ∂counterexampleMeasure := by
                    rw [hsplit]
                    rw [hsmall_inter]
                    exact
                      setIntegral_union hdisj measurableSet_Ici
                        hinc_int.integrableOn hinc_int.integrableOn
            _ = 0 + 0 := by rw [hsmall_zero, counterexampleIncrement_setIntegral_Ici_eq_zero]
            _ = 0 := by ring
      simpa using hinc_zero.symm
    · have hsubset :
          (fun ω : ℕ ↦ min ω n) ⁻¹' t ⊆ Set.Iio n := by
        intro ω hω
        by_contra hnot
        have hle : n ≤ ω := Nat.not_lt.mp hnot
        have hmin : min ω n = n := Nat.min_eq_right hle
        exact hn (by simpa [hmin] using hω)
      have hsmall_meas : MeasurableSet ((fun ω : ℕ ↦ min ω n) ⁻¹' t) :=
        (Set.to_countable _).measurableSet
      have hEq :
          ∫ ω in (fun ω : ℕ ↦ min ω n) ⁻¹' t, inc ω ∂counterexampleMeasure =
            ∫ ω in (fun ω : ℕ ↦ min ω n) ⁻¹' t, (0 : ℝ) ∂counterexampleMeasure := by
        refine setIntegral_congr_ae hsmall_meas (Filter.Eventually.of_forall ?_)
        intro ω hω
        have hlt : ω < n := hsubset hω
        simp [inc, counterexampleIncrement_eq, Nat.ne_of_lt hlt,
          Nat.not_lt_of_ge (Nat.le_of_lt hlt)]
      simpa using hEq.symm

/-- Counterexample helper: the explicit geometric process is a martingale for the counterexample
filtration and measure. -/
theorem counterexampleProcess_martingale :
    Martingale counterexampleProcess counterexampleFiltration counterexampleMeasure := by
  exact martingale_of_condExp_sub_eq_zero_nat counterexampleProcess_stronglyAdapted
    counterexampleProcess_integrable counterexampleIncrement_condExp_ae_eq_zero

/-- Counterexample helper: every time slice of the explicit geometric counterexample process is
square-integrable. -/
theorem counterexampleProcess_integrable_sq
    (n : ℕ) :
    Integrable (fun ω ↦ (counterexampleProcess n ω) ^ 2) counterexampleMeasure := by
  let A : Set ℕ := Set.Iio n
  have hEq :
      (fun ω ↦ (counterexampleProcess n ω) ^ 2) =
        A.piecewise (fun _ : ℕ ↦ (1 : ℝ)) (fun _ ↦ (1 - (2 : ℝ) ^ n) ^ 2) := by
    funext ω
    by_cases hω : ω < n
    · simp [counterexampleProcess, A, Set.piecewise, hω]
    · simp [counterexampleProcess, A, Set.piecewise, hω]
  have hleft :
      IntegrableOn (fun _ : ℕ ↦ (1 : ℝ)) A counterexampleMeasure :=
    integrableOn_const (measure_ne_top counterexampleMeasure A) (by simp)
  have hright :
      IntegrableOn (fun _ : ℕ ↦ (1 - (2 : ℝ) ^ n) ^ 2) Aᶜ counterexampleMeasure :=
    integrableOn_const (measure_ne_top counterexampleMeasure Aᶜ) (by simp)
  rw [hEq]
  exact Integrable.piecewise measurableSet_Iio hleft hright

/-- Helper for Exercise 10.2.1: squaring the increment size `2^n` gives the normalized power
`4^n`. -/
private theorem counterexampleTwoPow_sq (n : ℕ) :
    (((2 : ℝ) ^ n) ^ 2) = (4 : ℝ) ^ n := by
  calc
    (((2 : ℝ) ^ n) ^ 2) = (2 : ℝ) ^ (n * 2) := by
      rw [← pow_mul]
    _ = (2 : ℝ) ^ (2 * n) := by
      rw [Nat.mul_comm]
    _ = (((2 : ℝ) ^ 2) ^ n) := by
      rw [pow_mul]
    _ = (4 : ℝ) ^ n := by
      norm_num

/-- Helper for Exercise 10.2.1: the squared one-step increment is the deterministic tail indicator
`(4^n) 𝟙_{Set.Ici n}`. -/
private theorem counterexampleSqIncrement_eq (n : ℕ) :
    (fun ω ↦ (counterexampleProcess (n + 1) ω - counterexampleProcess n ω) ^ 2) =
      Set.indicator (Set.Ici n) (fun _ : ℕ ↦ (4 : ℝ) ^ n) := by
  funext ω
  by_cases hω : ω < n
  · have hnot : ¬ n ≤ ω := Nat.not_le.mpr hω
    have hω' : ω < n + 1 := Nat.lt_succ_of_lt hω
    simp [counterexampleProcess, hω, hω', hnot, Set.indicator, Set.mem_Ici]
  · have hle : n ≤ ω := Nat.not_lt.mp hω
    by_cases hEq : ω = n
    · -- On the atom `{n}`, the increment equals `2^n`, so its square is `4^n`.
      have hsquare :
          (counterexampleProcess (n + 1) ω - counterexampleProcess n ω) ^ 2 = (4 : ℝ) ^ n := by
        subst hEq
        simp [counterexampleProcess, counterexampleTwoPow_sq]
      simpa [Set.indicator, Set.mem_Ici, hEq] using hsquare
    · have hgt : n < ω := lt_of_le_of_ne hle (fun h ↦ hEq h.symm)
      -- On the strict tail, the increment is `-2^n`, whose square is again `4^n`.
      have hinc :
          counterexampleProcess (n + 1) ω - counterexampleProcess n ω = -((2 : ℝ) ^ n) := by
        have hne : ω ≠ n := ne_of_gt hgt
        simpa [hne, hgt] using congrFun (counterexampleIncrement_eq n) ω
      have hsquare : (-((2 : ℝ) ^ n)) ^ 2 = (4 : ℝ) ^ n := by
        calc
          (-((2 : ℝ) ^ n)) ^ 2 = (((2 : ℝ) ^ n) ^ 2) := by
            ring
          _ = (4 : ℝ) ^ n := counterexampleTwoPow_sq n
      rw [hinc]
      simpa [Set.indicator, Set.mem_Ici, hle] using hsquare

/-- Helper for Exercise 10.2.1: the conditional expectation of the squared increment is the same
tail indicator because that increment square is already `ℱ_n`-measurable. -/
private theorem counterexampleSqIncrement_condExp_eq (n : ℕ) :
    counterexampleMeasure[
      (fun ω ↦ (counterexampleProcess (n + 1) ω - counterexampleProcess n ω) ^ 2)
      | counterexampleFiltration n] =
      Set.indicator (Set.Ici n) (fun _ : ℕ ↦ (4 : ℝ) ^ n) := by
  let g : ℕ → ℝ := Set.indicator (Set.Ici n) (fun _ : ℕ ↦ (4 : ℝ) ^ n)
  have hg_meas : StronglyMeasurable[counterexampleFiltration n] g := by
    let h : ℕ → ℝ := fun k ↦ if k = n then (4 : ℝ) ^ n else 0
    have hh : Measurable h := measurable_of_countable h
    have hg_eq : g = h ∘ fun ω : ℕ ↦ min ω n := by
      funext ω
      by_cases hω : ω < n
      · have hne : min ω n ≠ n := by
          simp [Nat.min_eq_left hω.le, hω.ne]
        simp [g, h, Set.mem_Ici, Nat.not_le.mpr hω, hne]
      · have hle : n ≤ ω := Nat.not_lt.mp hω
        have hmin : min ω n = n := Nat.min_eq_right hle
        simp [g, h, Set.mem_Ici, hle]
    rw [hg_eq]
    exact (hh.comp (counterexampleTruncatedIndex_measurable n)).stronglyMeasurable
  have hg_int : Integrable g counterexampleMeasure := by
    exact (integrable_const ((4 : ℝ) ^ n)).indicator measurableSet_Ici
  rw [counterexampleSqIncrement_eq n]
  simpa [g] using
    (condExp_of_stronglyMeasurable (counterexampleFiltration.le n) hg_meas hg_int)

/-- Helper for Exercise 10.2.1: the deterministic-time square variation of the counterexample is
the finite sum of the tail indicators `4^i 𝟙_{Set.Ici i}`. -/
private theorem counterexampleSquareVariation_eq_sum_powers (n ω : ℕ) :
    (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure]) n ω =
      ∑ i ∈ Finset.range n, if i ≤ ω then (4 : ℝ) ^ i else 0 := by
  have hsq_ae :=
    squareVariation_eq_sum_condExp_sq_increment
      counterexampleProcess_martingale counterexampleProcess_integrable_sq n
  have hsq :=
    (ae_iff_of_countable.mp hsq_ae) ω <| by
      rw [counterexampleMeasure_apply_singleton]
      exact pow_ne_zero _ (by norm_num)
  rw [hsq]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [congrFun (counterexampleSqIncrement_condExp_eq i) ω]
  by_cases hle : i ≤ ω
  · simp [Set.indicator, Set.mem_Ici, hle]
  · simp [Set.indicator, Set.mem_Ici, hle]

/-- Helper for Exercise 10.2.1: stopping the counterexample process at `τ(ω) = ω + 1` yields the
constant terminal value `1`. -/
private theorem counterexampleStoppedProcess_eq_one :
    stoppedValue counterexampleProcess counterexampleStoppingTimeInf = fun _ ↦ (1 : ℝ) := by
  funext ω
  have hEval :
      stoppedValue counterexampleProcess counterexampleStoppingTimeInf ω =
        counterexampleProcess (counterexampleStoppingTime ω) ω := by
    simpa [counterexampleStoppingTimeInf] using
      congrFun
        (stoppedValue_coe_eq_eval counterexampleProcess counterexampleStoppingTime) ω
  rw [hEval]
  simp [counterexampleStoppingTime, counterexampleProcess]

/-- Helper for Exercise 10.2.1: the stopped square variation at `τ(ω) = ω + 1` is the finite
geometric sum `∑_{i=0}^{ω} 4^i`. -/
private theorem counterexampleStoppedSquareVariation_eq_sum_powers (ω : ℕ) :
    stoppedValue
      (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
      counterexampleStoppingTimeInf ω =
      ∑ i ∈ Finset.range (ω + 1), (4 : ℝ) ^ i := by
  have hEval :
      stoppedValue
        (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
        counterexampleStoppingTimeInf ω =
        (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
          (counterexampleStoppingTime ω) ω := by
    simpa [counterexampleStoppingTimeInf] using
      congrFun
        (stoppedValue_coe_eq_eval
          (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
          counterexampleStoppingTime) ω
  rw [hEval, counterexampleStoppingTime, counterexampleSquareVariation_eq_sum_powers]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi_le : i ≤ ω := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp [hi_le]

/-- Helper for Exercise 10.2.1: for the geometric counterexample, the stopped canonical square
variation has infinite expectation. -/
private theorem counterexample_stopped_squareVariation_infinite_expectation :
    (∫⁻ ω, ENNReal.ofReal
        (stoppedValue
          (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
          counterexampleStoppingTimeInf ω) ∂counterexampleMeasure) = ∞ := by
  let f : ℕ → ℝ≥0∞ := fun ω ↦
    ENNReal.ofReal
      (stoppedValue
        (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
        counterexampleStoppingTimeInf ω)
  have hlower :
      ∀ ω, (1 / 2 : ENNReal) ≤ f ω * counterexampleMeasure {ω} := by
    intro ω
    -- Compare each atom against the last summand in the stopped square variation.
    have hstop_nonneg :
        0 ≤
          stoppedValue
            (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
            counterexampleStoppingTimeInf ω := by
      rw [counterexampleStoppedSquareVariation_eq_sum_powers]
      exact Finset.sum_nonneg fun i hi ↦ by positivity
    have hstop_ge :
        (4 : ℝ) ^ ω ≤
          stoppedValue
            (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
            counterexampleStoppingTimeInf ω := by
      calc
        (4 : ℝ) ^ ω ≤ ∑ i ∈ Finset.range (ω + 1), (4 : ℝ) ^ i := by
          apply Finset.single_le_sum
          · intro i hi
            positivity
          · simp
        _ = stoppedValue
              (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
              counterexampleStoppingTimeInf ω := by
              symm
              exact counterexampleStoppedSquareVariation_eq_sum_powers ω
    have hreal :
        (1 / 2 : ℝ) ≤
          stoppedValue
            (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
            counterexampleStoppingTimeInf ω *
              (1 / 2 : ℝ) ^ (ω + 1) := by
      calc
        (1 / 2 : ℝ) ≤ (4 : ℝ) ^ ω * (1 / 2 : ℝ) ^ (ω + 1) := by
          calc
            (1 / 2 : ℝ) = (1 / 2 : ℝ) * 1 := by ring
            _ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ ω := by
                  gcongr
                  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
            _ = (4 : ℝ) ^ ω * (1 / 2 : ℝ) ^ (ω + 1) := by
                  rw [pow_add, pow_one, ← mul_assoc, ← mul_pow]
                  ring_nf
        _ ≤
            stoppedValue
                (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
                counterexampleStoppingTimeInf ω *
              (1 / 2 : ℝ) ^ (ω + 1) := by
                gcongr
    have hmass :
        counterexampleMeasure {ω} = ENNReal.ofReal ((1 / 2 : ℝ) ^ (ω + 1)) := by
      rw [counterexampleMeasure_apply_singleton]
      simpa using
        (ENNReal.ofReal_pow (show 0 ≤ (1 / 2 : ℝ) by norm_num) (ω + 1)).symm
    have hEq :
        f ω * counterexampleMeasure {ω} =
            ENNReal.ofReal
              (stoppedValue
                  (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
                  counterexampleStoppingTimeInf ω *
                (1 / 2 : ℝ) ^ (ω + 1)) := by
      rw [show f ω =
          ENNReal.ofReal
            (stoppedValue
              (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
              counterexampleStoppingTimeInf ω) by rfl]
      rw [hmass, ← ENNReal.ofReal_mul hstop_nonneg]
    rw [hEq]
    simpa using ENNReal.ofReal_le_ofReal hreal
  calc
    ∫⁻ ω, f ω ∂counterexampleMeasure = ∑' ω, f ω * counterexampleMeasure {ω} := by
      simpa [f] using (lintegral_countable' f : ∫⁻ ω, f ω ∂counterexampleMeasure =
        ∑' ω, f ω * counterexampleMeasure {ω})
    _ = ∞ := by
      apply top_unique
      calc
        ∞ = ∑' _ : ℕ, (1 / 2 : ENNReal) := by
              exact
                (ENNReal.tsum_const_eq_top_of_ne_zero
                  (show (1 / 2 : ENNReal) ≠ 0 by simp)).symm
        _ ≤ ∑' ω, f ω * counterexampleMeasure {ω} := ENNReal.tsum_le_tsum hlower

-- Semantic recall note: `Chap09.Definition_9_7` offers `IsSquareIntegrableProcess`, but source
-- clause `(ii)` is exposed as three atomic labeled counterexample facts rather than a single large
-- conjunction.
/-- Exercise 10.2.1 (3): source clause (ii), first counterexample fact. For the
explicit geometric counterexample, the
stopped canonical square variation has infinite expectation. -/
theorem counterexample_stopped_squareVariation_expectation_eq_top :
    (∫⁻ ω, ENNReal.ofReal
      (stoppedValue
        (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
        counterexampleStoppingTimeInf ω) ∂counterexampleMeasure) = ∞ := by
  -- Reuse the already established infinite-expectation computation for the stopped square
  -- variation.
  simpa using counterexample_stopped_squareVariation_infinite_expectation

/-- Continuation of Exercise 10.2.1 (4): source clause (ii), second counterexample fact. For the
explicit geometric counterexample, the identity
`E[(X_τ - X_0)^2] = E[⟨X⟩_τ]` from `(10.7)` fails. -/
theorem counterexample_stopped_secondMoment_ne_stopped_squareVariation_expectation :
    (∫⁻ ω, ENNReal.ofReal
      ((stoppedValue counterexampleProcess counterexampleStoppingTimeInf ω -
          counterexampleProcess 0 ω) ^ 2) ∂counterexampleMeasure) ≠
      ∫⁻ ω, ENNReal.ofReal
        (stoppedValue
          (⟨counterexampleProcess⟩[counterexampleFiltration, counterexampleMeasure])
          counterexampleStoppingTimeInf ω) ∂counterexampleMeasure := by
  have hLeft :
      (∫⁻ ω, ENNReal.ofReal
        ((stoppedValue counterexampleProcess counterexampleStoppingTimeInf ω -
            counterexampleProcess 0 ω) ^ 2) ∂counterexampleMeasure) = 1 := by
    -- Normalize the stopped increment to the constant value `1`.
    simp [counterexampleStoppedProcess_eq_one, counterexampleProcess_zero]
  -- Compare the finite stopped second moment with the already computed infinite square-variation
  -- expectation.
  rw [hLeft, counterexample_stopped_squareVariation_expectation_eq_top]
  simp

/-- Continuation of Exercise 10.2.1 (5): source clause (ii), third counterexample fact. For the
explicit geometric counterexample, the identity
`E[X_τ] = E[X_0]` from `(10.7)` fails. -/
theorem counterexample_stopped_expectation_ne_initial_expectation :
    counterexampleMeasure[stoppedValue counterexampleProcess counterexampleStoppingTimeInf] ≠
      counterexampleMeasure[counterexampleProcess 0] := by
  have hStopped :
      counterexampleMeasure[
          stoppedValue counterexampleProcess counterexampleStoppingTimeInf] = 1 := by
    -- The stopped counterexample process is the constant function `1`.
    simp [counterexampleStoppedProcess_eq_one]
  have hInitial : counterexampleMeasure[counterexampleProcess 0] = 0 := by
    -- The initial process value is the constant function `0`.
    simp [counterexampleProcess_zero]
  rw [hStopped, hInitial]
  norm_num

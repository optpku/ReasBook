/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Exercise_10_2_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

section

variable {X : ℕ → Ω → ℝ}

/-- Helper for Exercise 11.2.5: center the martingale by subtracting its initial value. -/
def centeredProcess (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω ↦ X n ω - X 0 ω

/-- Helper for Exercise 11.2.5: stop the centered process at the first time its absolute value
reaches the threshold `K`. -/
noncomputable def centeredAbsHitTime (X : ℕ → Ω → ℝ) (K : ℕ) : Ω → ℕ∞ :=
  leastGE (fun n ω ↦ |centeredProcess X n ω|) K

/-- Helper for Exercise 11.2.5: the centered process starts at `0`. -/
@[simp] lemma centeredProcess_zero (X : ℕ → Ω → ℝ) :
    centeredProcess X 0 = 0 := by
  -- Proof comment: the centering subtracts the initial value from itself at time `0`.
  ext ω
  simp [centeredProcess]

/-- Helper for Exercise 11.2.5: centering preserves one-step increments. -/
lemma centeredProcess_sub_eq (X : ℕ → Ω → ℝ) (n : ℕ) :
    centeredProcess X (n + 1) - centeredProcess X n = fun ω ↦ X (n + 1) ω - X n ω := by
  -- Proof comment: the initial offset cancels in the consecutive difference.
  ext ω
  simp [centeredProcess]

/-- Helper for Exercise 11.2.5: the centered process is again a martingale. -/
lemma centeredProcess_martingale [SigmaFiniteFiltration μ ℱ]
    (hX : Martingale X ℱ μ) :
    Martingale (centeredProcess X) ℱ μ := by
  -- Proof comment: subtract the constant path `X 0` from the original martingale.
  simpa [centeredProcess] using
    hX.sub (martingale_const_fun ℱ μ (hX.stronglyMeasurable 0) (hX.integrable 0))

/-- Helper for Exercise 11.2.5: the centered process is deterministically bounded at each fixed
time when the martingale differences are almost surely uniformly bounded. -/
lemma centeredProcess_abs_le_of_bdd_difference
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R) :
    ∀ n, ∀ᵐ ω ∂μ, |centeredProcess X n ω| ≤ n * R := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the centered process vanishes at time `0`.
      filter_upwards with ω
      simp [centeredProcess]
  | succ n ih =>
      -- Proof comment: the next centered value is the previous one plus one bounded increment.
      filter_upwards [ih, ae_all_iff.1 hbdd n] with ω hω hnω
      have habs :
          |centeredProcess X n ω + (X (n + 1) ω - X n ω)| ≤
            |centeredProcess X n ω| + |X (n + 1) ω - X n ω| := by
        refine abs_le.2 ?_
        constructor <;> linarith [neg_abs_le (centeredProcess X n ω),
          le_abs_self (centeredProcess X n ω), neg_abs_le (X (n + 1) ω - X n ω),
          le_abs_self (X (n + 1) ω - X n ω)]
      calc
        |centeredProcess X (n + 1) ω|
            = |centeredProcess X n ω + (X (n + 1) ω - X n ω)| := by
                simp [centeredProcess]
        _ ≤ |centeredProcess X n ω| + |X (n + 1) ω - X n ω| := habs
        _ ≤ n * R + R := add_le_add hω hnω
        _ ≤ ((n : ℝ) + 1) * R := by
              nlinarith
        _ = (((n + 1 : ℕ) : ℝ) * (R : ℝ)) := by
              norm_num

/-- Helper for Exercise 11.2.5: the centered martingale is square-integrable at every
deterministic time. -/
lemma centeredMemLpTwoOfBddDifference [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R) :
    ∀ n, MemLp (centeredProcess X n) 2 μ := by
  intro n
  let hCentered : Martingale (centeredProcess X) ℱ μ :=
    centeredProcess_martingale (μ := μ) (ℱ := ℱ) hX
  -- Proof comment: the stagewise deterministic bound from the bounded increments puts the
  -- centered path into every `Lᵖ`, in particular into `L²`.
  refine MemLp.of_bound (((hCentered.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable)
    (n * R) ?_
  simpa [Real.norm_eq_abs] using centeredProcess_abs_le_of_bdd_difference (X := X) hbdd n

/-- Helper for Exercise 11.2.5: stopping changes one increment by an indicator factor recording
whether the stopping time has already been reached. -/
lemma stoppedProcess_succ_sub_eq_indicator
    (τ : Ω → ℕ∞) (f : ℕ → Ω → ℝ) (n : ℕ) :
    stoppedProcess f τ (n + 1) - stoppedProcess f τ n =
      Set.indicator {ω | τ ω ≤ n}ᶜ (f (n + 1) - f n) := by
  -- Proof comment: after the stopping time both stopped values are frozen, while before the
  -- stopping time the stopped increment is the original increment.
  ext ω
  by_cases h : τ ω ≤ n
  · have h' : τ ω ≤ n + 1 := h.trans (by exact_mod_cast Nat.le_succ n)
    simp [stoppedProcess_eq_of_ge h, stoppedProcess_eq_of_ge h', h]
  · have h' : (n + 1 : ℕ∞) ≤ τ ω := by
      cases hτω : τ ω with
      | top =>
          simp
      | coe a =>
          have hn : ¬ a ≤ n := by
            simpa [hτω] using h
          have hna : n < a := lt_of_not_ge hn
          exact_mod_cast Nat.succ_le_of_lt hna
    have hn : (n : ℕ∞) ≤ τ ω := by
      exact le_trans (by exact_mod_cast Nat.le_succ n) h'
    simp [stoppedProcess_eq_of_le hn, stoppedProcess_eq_of_le h', h]

/-- Helper for Exercise 11.2.5: taking the predictable part commutes with stopping for
integrable real-valued processes. -/
lemma stoppedProcess_predictablePart_ae_eq [SigmaFiniteFiltration μ ℱ]
    {Y : ℕ → Ω → ℝ} (hY : ∀ n, Integrable (Y n) μ) (τ : Ω → ℕ∞)
    (hτ : IsStoppingTime ℱ τ) :
    ∀ n, predictablePart (stoppedProcess Y τ) ℱ μ n =ᵐ[μ]
      stoppedProcess (predictablePart Y ℱ μ) τ n := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: both predictable parts start at `0`, so the stopped process also starts
      -- at `0`.
      filter_upwards with ω
      simp [predictablePart, stoppedProcess]
  | succ n ih =>
      -- Proof comment: compare the one-step predictable increments after rewriting the stopped
      -- increment as an indicator of the original increment.
      have hcond :
          μ[stoppedProcess Y τ (n + 1) - stoppedProcess Y τ n | ℱ n] =ᵐ[μ]
            Set.indicator {ω | τ ω ≤ n}ᶜ (μ[Y (n + 1) - Y n | ℱ n]) := by
        rw [stoppedProcess_succ_sub_eq_indicator]
        exact condExp_indicator ((hY (n + 1)).sub (hY n)) ((hτ.measurableSet_le n).compl)
      calc
        predictablePart (stoppedProcess Y τ) ℱ μ (n + 1)
            = predictablePart (stoppedProcess Y τ) ℱ μ n +
                μ[stoppedProcess Y τ (n + 1) - stoppedProcess Y τ n | ℱ n] := by
                  simp [predictablePart, Finset.sum_range_succ]
        _ =ᵐ[μ] stoppedProcess (predictablePart Y ℱ μ) τ n +
              Set.indicator {ω | τ ω ≤ n}ᶜ (μ[Y (n + 1) - Y n | ℱ n]) := by
              simpa using ih.add hcond
        _ = stoppedProcess (predictablePart Y ℱ μ) τ n +
              Set.indicator {ω | τ ω ≤ n}ᶜ
                (predictablePart Y ℱ μ (n + 1) - predictablePart Y ℱ μ n) := by
              congr 2
              ext ω
              simp [predictablePart, Finset.sum_range_succ]
        _ = stoppedProcess (predictablePart Y ℱ μ) τ (n + 1) := by
              ext ω
              have hω := congrFun
                (stoppedProcess_succ_sub_eq_indicator τ (predictablePart Y ℱ μ) n) ω
              have hω' := sub_eq_iff_eq_add.mp hω
              simpa [add_comm] using hω'.symm

/-- Helper for Exercise 11.2.5: the predictable part of the stopped squared process agrees
almost surely with the stopped square variation. -/
lemma stoppedProcess_predictablePart_sq_ae_eq [SigmaFiniteFiltration μ ℱ]
    (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ) :
    ∀ n, predictablePart (fun n ω ↦ (stoppedProcess X τ n ω) ^ 2) ℱ μ n =ᵐ[μ]
      stoppedProcess (⟨X⟩[ℱ, μ]) τ n := by
  intro n
  change predictablePart (stoppedProcess (fun n ω ↦ (X n ω) ^ 2) τ) ℱ μ n =ᵐ[μ]
    stoppedProcess (predictablePart (fun n ω ↦ (X n ω) ^ 2) ℱ μ) τ n
  exact stoppedProcess_predictablePart_ae_eq (μ := μ) (ℱ := ℱ) hXsq τ hτ n

/-- Helper for Exercise 11.2.5: centering does not change the canonical square variation. -/
lemma centeredSquareVariation_ae_eq [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R) :
    ∀ n, ⟨centeredProcess X⟩[ℱ, μ] n =ᵐ[μ] ⟨X⟩[ℱ, μ] n := by
  intro n
  let Y : ℕ → Ω → ℝ := centeredProcess X
  have hY2 : ∀ k, Integrable (fun ω ↦ (Y k ω) ^ 2) μ := by
    intro k
    -- Proof comment: the centered deterministic-time stages are in `L²`, hence their squares are
    -- integrable.
    exact (memLp_two_iff_integrable_sq
      (((centeredProcess_martingale (μ := μ) (ℱ := ℱ) hX).stronglyMeasurable k).mono
        (ℱ.le k)).aestronglyMeasurable).1
      (centeredMemLpTwoOfBddDifference (μ := μ) (ℱ := ℱ) hX hbdd k)
  have hStep :
      ∀ i,
        μ[(fun ω ↦ (Y (i + 1) ω) ^ 2 - (Y i ω) ^ 2) | ℱ i] =ᵐ[μ]
          μ[(fun ω ↦ (X (i + 1) ω) ^ 2 - (X i ω) ^ 2) | ℱ i] := by
    intro i
    let increment : Ω → ℝ := fun ω ↦ X (i + 1) ω - X i ω
    let cross : Ω → ℝ := fun ω ↦ X 0 ω * increment ω
    let centeredDiff : Ω → ℝ := fun ω ↦ (Y (i + 1) ω) ^ 2 - (Y i ω) ^ 2
    let originalDiff : Ω → ℝ := fun ω ↦ (X (i + 1) ω) ^ 2 - (X i ω) ^ 2
    have hIncrementInt : Integrable increment μ :=
      (hX.integrable (i + 1)).sub (hX.integrable i)
    have hCrossInt : Integrable cross μ := by
      -- Proof comment: the cross term is the integrable initial value times a bounded increment.
      refine (hX.integrable 0).mul_bdd (c := R)
        (((hX.stronglyMeasurable (i + 1)).mono (ℱ.le (i + 1))).sub
          ((hX.stronglyMeasurable i).mono (ℱ.le i))).aestronglyMeasurable ?_
      filter_upwards [ae_all_iff.1 hbdd i] with ω hω
      simpa [increment, Real.norm_eq_abs] using hω
    have hCenteredDiffInt : Integrable centeredDiff μ :=
      (hY2 (i + 1)).sub (hY2 i)
    have hOriginalRewrite : originalDiff = centeredDiff + (2 : ℝ) • cross := by
      funext ω
      simp [originalDiff, centeredDiff, cross, increment, Y, centeredProcess]
      ring
    have hOriginalDiffInt : Integrable originalDiff μ := by
      rw [hOriginalRewrite]
      exact hCenteredDiffInt.add (hCrossInt.const_mul (2 : ℝ))
    have hIncrementZero :
        μ[increment | ℱ i] =ᵐ[μ] 0 := by
      -- Proof comment: martingale increments have zero conditional expectation.
      calc
        μ[increment | ℱ i] =ᵐ[μ] μ[X (i + 1) | ℱ i] - μ[X i | ℱ i] := by
          simpa [increment] using condExp_sub (hX.integrable (i + 1)) (hX.integrable i) (ℱ i)
        _ =ᵐ[μ] X i - X i := by
          simpa using
            (hX.condExp_ae_eq (Nat.le_succ i)).sub (hX.condExp_ae_eq (le_rfl : i ≤ i))
        _ = 0 := by
          simp
    have hCrossZero :
        μ[cross | ℱ i] =ᵐ[μ] 0 := by
      -- Proof comment: the fixed initial value can be pulled out of the conditional expectation,
      -- leaving the zero-mean martingale increment.
      calc
        μ[cross | ℱ i] =ᵐ[μ] X 0 * μ[increment | ℱ i] := by
          simpa [cross] using
            condExp_mul_of_stronglyMeasurable_left
              ((hX.stronglyMeasurable 0).mono (ℱ.mono (Nat.zero_le i))) hCrossInt hIncrementInt
        _ =ᵐ[μ] X 0 * 0 := hIncrementZero.mono fun _ hω ↦ by simp [hω]
        _ = 0 := by
          simp
    have hCenteredRewrite : centeredDiff = originalDiff - (2 : ℝ) • cross := by
      funext ω
      simp [originalDiff, centeredDiff, cross, increment, Y, centeredProcess]
      ring
    calc
      μ[(fun ω ↦ (Y (i + 1) ω) ^ 2 - (Y i ω) ^ 2) | ℱ i] =ᵐ[μ]
          μ[centeredDiff | ℱ i] := by
            rfl
      _ =ᵐ[μ] μ[originalDiff - (2 : ℝ) • cross | ℱ i] := by
            exact condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ by
              simp [hCenteredRewrite])
      _ =ᵐ[μ] μ[originalDiff | ℱ i] - μ[(2 : ℝ) • cross | ℱ i] := by
            exact condExp_sub hOriginalDiffInt ((hCrossInt).const_mul (2 : ℝ)) (ℱ i)
      _ =ᵐ[μ] μ[originalDiff | ℱ i] - (2 : ℝ) • μ[cross | ℱ i] := by
            exact Filter.EventuallyEq.rfl.sub (condExp_smul (2 : ℝ) cross (ℱ i))
      _ =ᵐ[μ] μ[originalDiff | ℱ i] - (2 : ℝ) • 0 := by
            exact (Filter.EventuallyEq.rfl.sub (hCrossZero.const_smul (2 : ℝ)))
      _ =ᵐ[μ] μ[(fun ω ↦ (X (i + 1) ω) ^ 2 - (X i ω) ^ 2) | ℱ i] := by
            simp [originalDiff]
  -- Route correction: compare the square variations at the owner level by matching each
  -- predictable increment, instead of reopening the whole `predictablePart` transport layer.
  simpa [predictablePart, Finset.sum_apply] using
    eventuallyEq_sum (s := Finset.range n) fun i _ ↦ hStep i

/-- Helper for Exercise 11.2.5: subtracting the initial value does not change whether a sample
path converges in `ℝ`. -/
lemma centeredProcess_exists_tendsto_iff (X : ℕ → Ω → ℝ) (ω : Ω) :
    (∃ c : ℝ, Tendsto (fun n ↦ centeredProcess X n ω) atTop (𝓝 c)) ↔
      ∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c + X 0 ω, ?_⟩
    -- Proof comment: add back the constant initial value to recover the original martingale.
    have hconst : Tendsto (fun _ : ℕ ↦ X 0 ω) atTop (𝓝 (X 0 ω)) := tendsto_const_nhds
    refine Tendsto.congr' ?_ (hc.add hconst)
    exact Filter.Eventually.of_forall fun n ↦ by
      simp [centeredProcess, sub_eq_add_neg, add_left_comm, add_comm]
  · rintro ⟨c, hc⟩
    refine ⟨c - X 0 ω, ?_⟩
    -- Proof comment: subtract the same constant from the limit and from every stage.
    have hconst : Tendsto (fun _ : ℕ ↦ X 0 ω) atTop (𝓝 (X 0 ω)) := tendsto_const_nhds
    refine Tendsto.congr' ?_ (hc.sub hconst)
    exact Filter.Eventually.of_forall fun n ↦ by
      simp [centeredProcess]

/-- Helper for Exercise 11.2.5: boundedness of the canonical square variation is unchanged by
centering the martingale. -/
lemma centeredSquareVariation_bddAbove_ae_iff [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R) :
    ∀ᵐ ω ∂μ,
      BddAbove (Set.range fun n ↦ ⟨centeredProcess X⟩[ℱ, μ] n ω) ↔
        BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω) := by
  have hEq :
      ∀ᵐ ω ∂μ, ∀ n, ⟨centeredProcess X⟩[ℱ, μ] n ω = ⟨X⟩[ℱ, μ] n ω := by
    -- Proof comment: upgrade the stagewise almost-everywhere equality to a single full-measure
    -- event where all deterministic times agree simultaneously.
    exact ae_all_iff.2 fun n ↦ centeredSquareVariation_ae_eq (μ := μ) (ℱ := ℱ) hX hbdd n
  filter_upwards [hEq] with ω hω
  have hRange :
      Set.range (fun n ↦ ⟨centeredProcess X⟩[ℱ, μ] n ω) =
        Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω := by
    -- Proof comment: once the pointwise stage values match, the two ranges are literally equal.
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simpa using (hω n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simpa using hω n⟩
  simp [hRange]

/-- Helper for Exercise 11.2.5: stopping and taking absolute values commute pointwise. -/
lemma abs_stoppedProcess_eq (f : ℕ → Ω → ℝ) (τ : Ω → ℕ∞) (n : ℕ) :
    (fun ω ↦ |stoppedProcess f τ n ω|) = stoppedProcess (fun k ω ↦ |f k ω|) τ n := by
  -- Proof comment: both sides evaluate `f` at the same stopped index and then apply `abs`.
  ext ω
  simp [stoppedProcess]

/-- Helper for Exercise 11.2.5: deterministic-time square variation is integrable once the square
stages are integrable. -/
lemma integrableSquareVariation_of_integrableSq [SigmaFiniteFiltration μ ℱ]
    {Y : ℕ → Ω → ℝ} (hY : Martingale Y ℱ μ)
    (hYsq : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ) :
    ∀ n, Integrable (⟨Y⟩[ℱ, μ] n) μ := by
  intro n
  have hSumInt :
      Integrable
        (fun ω ↦
          ∑ i ∈ Finset.range n,
            μ[(fun ω ↦ (Y (i + 1) ω - Y i ω) ^ 2) | ℱ i] ω) μ := by
    -- Proof comment: the owner square-variation formula is a finite sum of integrable
    -- conditional expectations.
    exact integrable_finset_sum (Finset.range n) fun i _ ↦
      (integrable_condExp : Integrable
          (μ[(fun ω ↦ (Y (i + 1) ω - Y i ω) ^ 2) | ℱ i]) μ)
  exact hSumInt.congr (squareVariation_eq_sum_condExp_sq_increment hY hYsq n).symm

/-- Helper for Exercise 11.2.5: casting the bounded truncation of an `ℕ∞`-valued stopping time
back to `ℕ∞` recovers the pointwise minimum with the deterministic horizon. -/
lemma boundedStoppingTimeToNat_cast_eq_min (τ : Ω → ℕ∞) (n : ℕ) :
    (fun ω ↦ (boundedStoppingTimeToNat τ n ω : ℕ∞)) = fun ω ↦ min (n : ℕ∞) (τ ω) := by
  -- Proof comment: normalize the bounded truncation once so later stopped-value rewrites only
  -- see the canonical `min n τ` form.
  funext ω
  by_cases h : τ ω ≤ n
  · cases hτ : τ ω with
    | top =>
        exfalso
        simpa [hτ] using h
    | coe m =>
        have hmn : m ≤ n := by
          simpa [hτ] using h
        rw [boundedStoppingTimeToNat, dif_pos h]
        have hbranch :
            (((WithTop.untop (m : ℕ∞) (show (m : ℕ∞) ≠ ⊤ by simp)) : ℕ) : ℕ∞) =
              min (n : ℕ∞) (m : ℕ∞) := by
          calc
            (((WithTop.untop (m : ℕ∞) (show (m : ℕ∞) ≠ ⊤ by simp)) : ℕ) : ℕ∞) = (m : ℕ∞) := by
              exact WithTop.coe_untop _ (show (m : ℕ∞) ≠ ⊤ by simp)
            _ = min (n : ℕ∞) (m : ℕ∞) := by
              simpa using (min_eq_right hmn).symm
        simpa [hτ] using hbranch
  · -- Proof comment: outside the finite branch, the truncation is exactly the deterministic cap.
    simp [boundedStoppingTimeToNat, h, le_of_not_ge h]

/-- Helper for Exercise 11.2.5: evaluating `stoppedValue` at the bounded truncation of a stopping
time agrees with the deterministic-horizon stopped process. -/
lemma stoppedValue_boundedStoppingTimeToNat_eq_stoppedProcess
    {β : Type*} (u : ℕ → Ω → β) (τ : Ω → ℕ∞) (n : ℕ) :
    stoppedValue u (fun ω ↦ (boundedStoppingTimeToNat τ n ω : ℕ∞)) = stoppedProcess u τ n := by
  -- Proof comment: rewrite the bounded truncation as `min n τ`, then invoke the owner stopped
  -- process normalization.
  ext ω
  rw [stoppedProcess_eq_stoppedValue_apply]
  exact congrArg (fun s ↦ stoppedValue u s ω) (boundedStoppingTimeToNat_cast_eq_min τ n)

/-- Helper for Exercise 11.2.5: the centered square-variation threshold is a stopping time. -/
lemma centeredSquareVariationHit_isStoppingTime [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (K : ℕ) :
    IsStoppingTime ℱ
      (squareVariationHit (X := centeredProcess X) (ℱ := ℱ) (μ := μ) K) := by
  have hadapt : Adapted ℱ (fun n ω ↦ ⟨centeredProcess X⟩[ℱ, μ] (n + 1) ω) := by
    intro n
    simpa using squareVariation_predictable.measurable_add_one n
  -- Proof comment: the shifted centered square variation is adapted, so its first threshold hit
  -- is a stopping time by the generic hitting-time API.
  simpa [squareVariationHit] using
    hadapt.isStoppingTime_hittingAfter (s := Set.Ici (K : ℝ)) measurableSet_Ici

/-- Helper for Exercise 11.2.5: stopping the centered square variation at its own threshold never
exceeds that threshold. -/
lemma stoppedCenteredSquareVariation_le_threshold [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (K n : ℕ) :
    ∀ ω,
      stoppedProcess (⟨centeredProcess X⟩[ℱ, μ])
        (squareVariationHit (X := centeredProcess X) (ℱ := ℱ) (μ := μ) K) n ω ≤ K := by
  intro ω
  let τK : Ω → ℕ∞ := squareVariationHit (X := centeredProcess X) (ℱ := ℱ) (μ := μ) K
  let m := boundedStoppingTimeToNat τK n ω
  have hEval :
      stoppedProcess (⟨centeredProcess X⟩[ℱ, μ]) τK n ω =
        ⟨centeredProcess X⟩[ℱ, μ] m ω := by
    -- Proof comment: evaluate the stopped process through the finite truncation `m`.
    have hStop :
        stoppedValue (⟨centeredProcess X⟩[ℱ, μ])
            (fun ω ↦ (boundedStoppingTimeToNat τK n ω : ℕ∞)) =
          stoppedProcess (⟨centeredProcess X⟩[ℱ, μ]) τK n :=
      stoppedValue_boundedStoppingTimeToNat_eq_stoppedProcess
        (u := ⟨centeredProcess X⟩[ℱ, μ]) (τ := τK) (n := n)
    have hEval' :
        stoppedValue (⟨centeredProcess X⟩[ℱ, μ])
            (fun ω ↦ (boundedStoppingTimeToNat τK n ω : ℕ∞)) ω =
          ⟨centeredProcess X⟩[ℱ, μ] m ω := by
      simpa [m] using
        (congrFun
          (stoppedValue_coe_eq_eval
            (⟨centeredProcess X⟩[ℱ, μ]) (boundedStoppingTimeToNat τK n)) ω)
    simpa [hStop] using hEval'
  cases hm : m with
  | zero =>
      -- Proof comment: the owner square variation starts at `0`.
      rw [hEval, hm, squareVariation_zero]
      positivity
  | succ k =>
      have hcast :
          ((Nat.succ k : ℕ) : ℕ∞) = min (n : ℕ∞) (τK ω) := by
        simpa [m, hm] using
          congrFun (boundedStoppingTimeToNat_cast_eq_min (τ := τK) n) ω
      have hk_lt_min : (k : ℕ∞) < min (n : ℕ∞) (τK ω) := by
        rw [← hcast]
        exact_mod_cast Nat.lt_succ_self k
      have hk_lt_tau : (k : ℕ∞) < τK ω :=
        lt_of_lt_of_le hk_lt_min (min_le_right (n : ℕ∞) (τK ω))
      have hNotMem :
          ⟨centeredProcess X⟩[ℱ, μ] (k + 1) ω ∉ Set.Ici (K : ℝ) := by
        -- Proof comment: reaching the threshold by time `k + 1` would contradict that the hit
        -- time is still strictly larger than `k`.
        simpa [squareVariationHit, Set.mem_Ici] using
          (notMem_of_lt_hittingAfter
            (u := fun j ω ↦ ⟨centeredProcess X⟩[ℱ, μ] (j + 1) ω)
            (s := Set.Ici (K : ℝ)) (n := 0) (ω := ω) hk_lt_tau (by simp))
      have hlt : ⟨centeredProcess X⟩[ℱ, μ] (k + 1) ω < K := by
        simpa [Set.mem_Ici, not_le] using hNotMem
      rw [hEval, hm]
      exact le_of_lt hlt

/-- Helper for Exercise 11.2.5: each centered martingale stopped at a square-variation threshold
converges almost surely. -/
lemma centeredLocalizedAeTendstoExists [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R)
    (K : ℕ) :
    ∀ᵐ ω ∂μ, ∃ c,
      Tendsto
        (fun n ↦ stoppedProcess (centeredProcess X)
          (squareVariationHit (X := centeredProcess X) (ℱ := ℱ) (μ := μ) K) n ω)
        atTop (𝓝 c) := by
  let Y : ℕ → Ω → ℝ := centeredProcess X
  let τK : Ω → ℕ∞ := squareVariationHit (X := Y) (ℱ := ℱ) (μ := μ) K
  let Z : ℕ → Ω → ℝ := stoppedProcess Y τK
  have hY : Martingale Y ℱ μ := centeredProcess_martingale (μ := μ) (ℱ := ℱ) hX
  have hτK : IsStoppingTime ℱ τK :=
    centeredSquareVariationHit_isStoppingTime (μ := μ) (ℱ := ℱ) (X := X) K
  have hY2 : ∀ n, MemLp (Y n) 2 μ := by
    intro n
    exact centeredMemLpTwoOfBddDifference (μ := μ) (ℱ := ℱ) hX hbdd n
  have hYsq : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ := by
    intro n
    exact (memLp_two_iff_integrable_sq
      (((hY.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable)).1 (hY2 n)
  have hZ : Martingale Z ℱ μ := by
    -- Proof comment: stopping preserves both the submartingale and supermartingale halves.
    rw [martingale_iff]
    refine ⟨?_, hY.submartingale.stoppedProcess hτK⟩
    have hStoppedNegSub : Submartingale (stoppedProcess (-Y) τK) ℱ μ :=
      hY.neg.submartingale.stoppedProcess hτK
    have hStoppedNegEq : stoppedProcess (-Y) τK = -Z := by
      funext n ω
      simp [Y, Z, stoppedProcess]
    simpa [hStoppedNegEq] using hStoppedNegSub.neg
  have hZ2 : ∀ n, MemLp (Z n) 2 μ := by
    intro n
    let τKn : Ω → ℕ := boundedStoppingTimeToNat τK n
    have hτKn : IsStoppingTime ℱ (fun ω ↦ (τKn ω : ℕ∞)) := by
      simpa [τKn, boundedStoppingTimeToNat_cast_eq_min, min_comm] using hτK.min_const n
    have hτKn_le : ∀ ω, (τKn ω : ℕ∞) ≤ n := by
      intro ω
      have hcast := congrFun (boundedStoppingTimeToNat_cast_eq_min (τ := τK) n) ω
      rw [hcast]
      exact min_le_left (n : ℕ∞) (τK ω)
    have hMem : MemLp (stoppedValue Y (fun ω ↦ (τKn ω : ℕ∞))) 2 μ :=
      memLp_stoppedValue hτKn hY2 hτKn_le
    simpa [Y, Z, τKn, stoppedValue_boundedStoppingTimeToNat_eq_stoppedProcess] using hMem
  have hBracketEqAll :
      ∀ᵐ ω ∂μ, ∀ n, ⟨Z⟩[ℱ, μ] n ω = stoppedProcess (⟨Y⟩[ℱ, μ]) τK n ω := by
    exact ae_all_iff.2 fun n ↦ by
      simpa [Y, Z] using
        stoppedProcess_predictablePart_sq_ae_eq (μ := μ) (ℱ := ℱ) (X := Y) hYsq τK hτK n
  have hBddSquareVariation :
      ∀ᵐ ω ∂μ, BddAbove (Set.range fun n ↦ ⟨Z⟩[ℱ, μ] n ω) := by
    filter_upwards [hBracketEqAll] with ω hω
    refine ⟨K, ?_⟩
    rintro x ⟨n, rfl⟩
    simpa [hω n] using
      stoppedCenteredSquareVariation_le_threshold (μ := μ) (ℱ := ℱ) (X := X) K n ω
  have hAe :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Z n ω) atTop (𝓝 (ℱ.limitProcess Z μ ω)) :=
    square_integrable_martingale_ae_tendsto_limitProcess_of_ae_bddAbove_squareVariation
      (X := Z) (ℱ := ℱ) (μ := μ) hZ hZ2 hBddSquareVariation
  filter_upwards [hAe] with ω hω
  exact ⟨ℱ.limitProcess Z μ ω, hω⟩

/-- Helper for Exercise 11.2.5: bounded centered square variation implies almost-sure pathwise
convergence of the centered martingale. -/
lemma ae_exists_tendsto_of_bddAbove_centeredSquareVariation [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R) :
    ∀ᵐ ω ∂μ,
      BddAbove (Set.range fun n ↦ ⟨centeredProcess X⟩[ℱ, μ] n ω) →
        ∃ c, Tendsto (fun n ↦ centeredProcess X n ω) atTop (𝓝 c) := by
  have hLocalized :
      ∀ᵐ ω ∂μ, ∀ K : ℕ, ∃ c,
        Tendsto
          (fun n ↦ stoppedProcess (centeredProcess X)
            (squareVariationHit (X := centeredProcess X) (ℱ := ℱ) (μ := μ) K) n ω)
          atTop (𝓝 c) := by
    exact ae_all_iff.2 fun K ↦
      centeredLocalizedAeTendstoExists (μ := μ) (ℱ := ℱ) (X := X) hX hbdd K
  filter_upwards [hLocalized] with ω hLocalizedω hBddω
  obtain ⟨a, ha⟩ := hBddω
  obtain ⟨K, hK⟩ := exists_nat_gt a
  have hHitTop :
      squareVariationHit (X := centeredProcess X) (ℱ := ℱ) (μ := μ) K ω = ⊤ := by
    -- Proof comment: choosing `K` above the pointwise square-variation bound forces the hitting
    -- time to be infinite on this sample path.
    refine (hittingAfter_eq_top_iff
      (u := fun n ω ↦ ⟨centeredProcess X⟩[ℱ, μ] (n + 1) ω)
      (s := Set.Ici (K : ℝ)) (n := 0) (ω := ω)).2 ?_
    intro j _
    have hja : ⟨centeredProcess X⟩[ℱ, μ] (j + 1) ω ≤ a := by
      exact ha ⟨j + 1, rfl⟩
    have hjK : ⟨centeredProcess X⟩[ℱ, μ] (j + 1) ω < K := lt_of_le_of_lt hja hK
    simpa [squareVariationHit, Set.mem_Ici, not_le] using hjK
  obtain ⟨c, hc⟩ := hLocalizedω K
  refine ⟨c, ?_⟩
  have hStoppedEq :
      (fun n ↦
        stoppedProcess (centeredProcess X)
          (squareVariationHit (X := centeredProcess X) (ℱ := ℱ) (μ := μ) K) n ω) =
        fun n ↦ centeredProcess X n ω := by
    -- Proof comment: once the threshold is never hit, the stopped path is the original centered
    -- path at every deterministic time.
    funext n
    exact stoppedProcess_eq_of_le (u := centeredProcess X)
      (τ := squareVariationHit (X := centeredProcess X) (ℱ := ℱ) (μ := μ) K)
      (ω := ω) (i := n) <| by
        rw [hHitTop]
        exact le_top
  simpa [hStoppedEq] using hc

/-- Helper for Exercise 11.2.5: deterministic-time square variation is almost surely monotone in
time. -/
lemma squareVariation_ae_mono_of_integrableSq [SigmaFiniteFiltration μ ℱ]
    {Y : ℕ → Ω → ℝ} (hY : Martingale Y ℱ μ)
    (hYsq : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ 2) μ)
    {n m : ℕ} (hnm : n ≤ m) :
    ∀ᵐ ω ∂μ, ⟨Y⟩[ℱ, μ] n ω ≤ ⟨Y⟩[ℱ, μ] m ω := by
  have hsq :
      ∀ᵐ ω ∂μ, ∀ k : ℕ,
        ⟨Y⟩[ℱ, μ] k ω =
          ∑ i ∈ Finset.range k, μ[(fun ω ↦ (Y (i + 1) ω - Y i ω) ^ 2) | ℱ i] ω := by
    -- Proof comment: rewrite each deterministic-time stage into the canonical finite sum.
    exact ae_all_iff.2 fun k ↦ squareVariation_eq_sum_condExp_sq_increment hY hYsq k
  have hnonneg :
      ∀ᵐ ω ∂μ, ∀ i : ℕ,
        0 ≤ μ[(fun ω ↦ (Y (i + 1) ω - Y i ω) ^ 2) | ℱ i] ω := by
    -- Proof comment: every conditional expectation of a squared increment is nonnegative.
    exact ae_all_iff.2 fun i ↦
      condExp_nonneg (Filter.Eventually.of_forall fun ω ↦ sq_nonneg _)
  filter_upwards [hsq, hnonneg] with ω hsqω hnonnegω
  have hsum :
      ∑ i ∈ Finset.range n, μ[(fun ω ↦ (Y (i + 1) ω - Y i ω) ^ 2) | ℱ i] ω ≤
        ∑ i ∈ Finset.range m, μ[(fun ω ↦ (Y (i + 1) ω - Y i ω) ^ 2) | ℱ i] ω := by
    -- Proof comment: enlarging the finite range only adds nonnegative terms.
    exact sumRangeMonotoneOfNonnegative hnm hnonnegω
  rw [hsqω n, hsqω m]
  exact hsum

/-- Helper for Exercise 11.2.5: the centered martingale stopped at the first absolute-value hit
is uniformly bounded by the overshoot estimate `K + R`. -/
lemma stoppedCentered_abs_le_of_centeredAbsHit [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ]
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R)
    (K n : ℕ) :
    ∀ᵐ ω ∂μ,
      |stoppedProcess (centeredProcess X) (centeredAbsHitTime X K) n ω| ≤ (K : ℝ) + R := by
  have hAbsBdd :
      ∀ᵐ ω ∂μ, ∀ i : ℕ,
        |(|centeredProcess X (i + 1) ω| - |centeredProcess X i ω|)| ≤ R := by
    -- Proof comment: the absolute-value process inherits the same increment envelope by the
    -- reverse triangle inequality.
    filter_upwards [hbdd] with ω hω i
    calc
      |(|centeredProcess X (i + 1) ω| - |centeredProcess X i ω|)| ≤
          |centeredProcess X (i + 1) ω - centeredProcess X i ω| := by
            simpa [Real.dist_eq] using
              (abs_abs_sub_abs_le_abs_sub (centeredProcess X (i + 1) ω) (centeredProcess X i ω))
      _ = |X (i + 1) ω - X i ω| := by
            simpa using congrArg abs (congrFun (centeredProcess_sub_eq X i) ω)
      _ ≤ R := hω i
  have hStoppedAbs :
      ∀ᵐ ω ∂μ,
        stoppedProcess (fun k ω ↦ |centeredProcess X k ω|) (centeredAbsHitTime X K) n ω ≤
          (K : ℝ) + R := by
    -- Proof comment: apply the generic one-step overshoot control to the absolute-value process.
    simpa [centeredAbsHitTime] using
      (stoppedAbove_le (f := fun k ω ↦ |centeredProcess X k ω|) (μ := μ)
        (r := (K : ℝ)) (R := R)
        (show 0 ≤ (K : ℝ) by exact_mod_cast Nat.zero_le K)
        (by
          ext ω
          simp [centeredProcess])
        hAbsBdd n)
  filter_upwards [hStoppedAbs] with ω hω
  simpa [abs_stoppedProcess_eq (f := centeredProcess X) (τ := centeredAbsHitTime X K) (n := n)]
    using hω

/-- Helper for Exercise 11.2.5: the stopped centered square variation has uniformly bounded
expectation. -/
lemma centeredStoppedSquareVariation_expectation_le [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R)
    (K n : ℕ) :
    μ[stoppedProcess (⟨centeredProcess X⟩[ℱ, μ]) (centeredAbsHitTime X K) n] ≤
      ((K : ℝ) + R) ^ 2 := by
  let Y : ℕ → Ω → ℝ := centeredProcess X
  let τK : Ω → ℕ∞ := centeredAbsHitTime X K
  let Z : ℕ → Ω → ℝ := stoppedProcess Y τK
  have hY : Martingale Y ℱ μ := centeredProcess_martingale (μ := μ) (ℱ := ℱ) hX
  have hYsq : ∀ k, Integrable (fun ω ↦ (Y k ω) ^ 2) μ := by
    intro k
    -- Proof comment: each centered deterministic-time stage lies in `L²`.
    exact (memLp_two_iff_integrable_sq
      (((hY.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable)).1
      (centeredMemLpTwoOfBddDifference (μ := μ) (ℱ := ℱ) hX hbdd k)
  have hτK :
      IsStoppingTime ℱ τK := by
    have hAbsStronglyAdapted : StronglyAdapted ℱ (fun k ω ↦ |Y k ω|) := by
      intro k
      simpa [Real.norm_eq_abs] using (hY.stronglyAdapted k).norm
    -- Proof comment: the first absolute-value threshold hit is a stopping time.
    simpa [τK, Y, centeredAbsHitTime, Real.norm_eq_abs] using
      (hAbsStronglyAdapted.isStoppingTime_leastGE (K : ℝ))
  have hZ : Martingale Z ℱ μ := by
    -- Proof comment: stopping preserves both the submartingale and supermartingale halves.
    rw [martingale_iff]
    refine ⟨?_, hY.submartingale.stoppedProcess hτK⟩
    have hStoppedNegSub : Submartingale (stoppedProcess (-Y) τK) ℱ μ :=
      hY.neg.submartingale.stoppedProcess hτK
    have hStoppedNegEq : stoppedProcess (-Y) τK = -Z := by
      funext k ω
      simp [Z, Y, stoppedProcess]
    simpa [hStoppedNegEq] using hStoppedNegSub.neg
  have hZmemLp : ∀ k, MemLp (Z k) 2 μ := by
    intro k
    refine MemLp.of_bound (((hZ.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable)
      ((K : ℝ) + R) ?_
    simpa [Z, Real.norm_eq_abs] using
      stoppedCentered_abs_le_of_centeredAbsHit (μ := μ) (ℱ := ℱ) hbdd K k
  have hZsq : ∀ k, Integrable (fun ω ↦ (Z k ω) ^ 2) μ := by
    intro k
    exact (memLp_two_iff_integrable_sq
      (((hZ.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable)).1 (hZmemLp k)
  have hBracketEq :
      ⟨Z⟩[ℱ, μ] n =ᵐ[μ] stoppedProcess (⟨Y⟩[ℱ, μ]) τK n := by
    -- Proof comment: for the stopped process, the owner square variation is the stopped owner
    -- square variation of the original centered martingale.
    simpa [Z, Y] using stoppedProcess_predictablePart_sq_ae_eq (μ := μ) (ℱ := ℱ) hYsq τK hτK n
  have hBracketInt : Integrable (⟨Z⟩[ℱ, μ] n) μ :=
    integrableSquareVariation_of_integrableSq (μ := μ) (ℱ := ℱ) hZ hZsq n
  have hMomentEq :
      μ[⟨Z⟩[ℱ, μ] n] = μ[fun ω ↦ (Z n ω) ^ 2] := by
    let M : ℕ → Ω → ℝ := fun k ω ↦ (Z k ω) ^ 2 - ⟨Z⟩[ℱ, μ] k ω
    have hM : Martingale M ℱ μ := by
      simpa [M] using
      square_sub_squareVariation_martingale (μ := μ) (ℱ := ℱ) hZ hZsq
    have hZero :
        (∫ ω, M n ω ∂μ) = 0 := by
      calc
        ∫ ω, M n ω ∂μ = ∫ ω, M 0 ω ∂μ := by
              simpa [MeasureTheory.integral, M] using (martingale_expectation_eq hM (Nat.zero_le n)).symm
        _ = 0 := by
              simp [M, Z, Y, τK, stoppedProcess, centeredProcess_zero]
    have hSub :
        (∫ ω, M n ω ∂μ) = μ[fun ω ↦ (Z n ω) ^ 2] - μ[⟨Z⟩[ℱ, μ] n] := by
      exact integral_sub (hZsq n) hBracketInt
    rw [hSub] at hZero
    linarith
  have hMomentLe :
      μ[fun ω ↦ (Z n ω) ^ 2] ≤ ((K : ℝ) + R) ^ 2 := by
    have hSqLe :
        ∀ᵐ ω ∂μ, (Z n ω) ^ 2 ≤ ((K : ℝ) + R) ^ 2 := by
      filter_upwards
        [stoppedCentered_abs_le_of_centeredAbsHit (μ := μ) (ℱ := ℱ) hbdd K n] with ω hω
      rcases abs_le.1 hω with ⟨hneg, hpos⟩
      nlinarith
    calc
      μ[fun ω ↦ (Z n ω) ^ 2] ≤ μ[fun _ : Ω ↦ ((K : ℝ) + R) ^ 2] := by
        exact integral_mono_ae (hZsq n) (integrable_const (((K : ℝ) + R) ^ 2)) hSqLe
      _ = ((K : ℝ) + R) ^ 2 := by
        simp
  calc
    μ[stoppedProcess (⟨centeredProcess X⟩[ℱ, μ]) (centeredAbsHitTime X K) n] =
        μ[⟨Z⟩[ℱ, μ] n] := by
          exact integral_congr_ae hBracketEq.symm
    _ = μ[fun ω ↦ (Z n ω) ^ 2] := hMomentEq
    _ ≤ ((K : ℝ) + R) ^ 2 := hMomentLe

/-- Helper for Exercise 11.2.5: a nonnegative almost-surely monotone family with uniformly
bounded expectations is almost surely bounded above pointwise. -/
lemma ae_bddAbove_range_of_nonneg_mono_integral_bounded
    {f : ℕ → Ω → ℝ} (hInt : ∀ n, Integrable (f n) μ)
    (hNonneg : ∀ n, 0 ≤ᵐ[μ] f n)
    (hMono : ∀ᵐ ω ∂μ, Monotone fun n => f n ω)
    (C : ℝ) (hC : ∀ n, μ[f n] ≤ C) :
    ∀ᵐ ω ∂μ, BddAbove (Set.range fun n ↦ f n ω) := by
  let g : ℕ → Ω → ENNReal := fun n ω ↦ ENNReal.ofReal (f n ω)
  have hGMeas : ∀ n, AEMeasurable (g n) μ := by
    intro n
    exact (hInt n).1.aemeasurable.ennreal_ofReal
  have hGMono : ∀ᵐ ω ∂μ, Monotone fun n => g n ω := by
    filter_upwards [hMono] with ω hω n m hnm
    exact ENNReal.ofReal_le_ofReal (hω hnm)
  have hLint :
      ∀ n, ∫⁻ ω, g n ω ∂μ ≤ ENNReal.ofReal C := by
    intro n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hInt n) (hNonneg n)]
    exact ENNReal.ofReal_le_ofReal (hC n)
  have hSupInt :
      ∫⁻ ω, ⨆ n, g n ω ∂μ ≤ ENNReal.ofReal C := by
    rw [MeasureTheory.lintegral_iSup' hGMeas hGMono]
    exact iSup_le hLint
  have hSupFinite :
      ∀ᵐ ω ∂μ, (⨆ n, g n ω) < ⊤ := by
    exact MeasureTheory.ae_lt_top' (AEMeasurable.iSup hGMeas)
      (ne_top_of_le_ne_top (by simp) hSupInt)
  filter_upwards [hSupFinite] with ω hω
  refine ⟨(⨆ n, g n ω).toReal, ?_⟩
  rintro y ⟨n, rfl⟩
  exact (ENNReal.ofReal_le_iff_le_toReal hω.ne).1 (le_iSup (fun m ↦ g m ω) n)

/-- Helper for Exercise 11.2.5: for each absolute-value threshold, the stopped centered square
variation is almost surely bounded above as a path in `n`. -/
lemma boundedStoppedCenteredSquareVariation_ae [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R)
    (K : ℕ) :
    ∀ᵐ ω ∂μ,
      BddAbove (Set.range fun n ↦
        stoppedProcess (⟨centeredProcess X⟩[ℱ, μ]) (centeredAbsHitTime X K) n ω) := by
  let Y : ℕ → Ω → ℝ := centeredProcess X
  let τK : Ω → ℕ∞ := centeredAbsHitTime X K
  let Z : ℕ → Ω → ℝ := stoppedProcess Y τK
  let A : ℕ → Ω → ℝ := fun n ω ↦ stoppedProcess (⟨Y⟩[ℱ, μ]) τK n ω
  have hY : Martingale Y ℱ μ := centeredProcess_martingale (μ := μ) (ℱ := ℱ) hX
  have hYsq : ∀ k, Integrable (fun ω ↦ (Y k ω) ^ 2) μ := by
    intro k
    exact (memLp_two_iff_integrable_sq
      (((hY.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable)).1
      (centeredMemLpTwoOfBddDifference (μ := μ) (ℱ := ℱ) hX hbdd k)
  have hτK :
      IsStoppingTime ℱ τK := by
    have hAbsStronglyAdapted : StronglyAdapted ℱ (fun k ω ↦ |Y k ω|) := by
      intro k
      simpa [Real.norm_eq_abs] using (hY.stronglyAdapted k).norm
    simpa [τK, Y, centeredAbsHitTime, Real.norm_eq_abs] using
      (hAbsStronglyAdapted.isStoppingTime_leastGE (K : ℝ))
  have hZ : Martingale Z ℱ μ := by
    rw [martingale_iff]
    refine ⟨?_, hY.submartingale.stoppedProcess hτK⟩
    have hStoppedNegSub : Submartingale (stoppedProcess (-Y) τK) ℱ μ :=
      hY.neg.submartingale.stoppedProcess hτK
    have hStoppedNegEq : stoppedProcess (-Y) τK = -Z := by
      funext k ω
      simp [Z, Y, stoppedProcess]
    simpa [hStoppedNegEq] using hStoppedNegSub.neg
  have hZmemLp : ∀ k, MemLp (Z k) 2 μ := by
    intro k
    refine MemLp.of_bound (((hZ.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable)
      ((K : ℝ) + R) ?_
    simpa [Z, Real.norm_eq_abs] using
      stoppedCentered_abs_le_of_centeredAbsHit (μ := μ) (ℱ := ℱ) hbdd K k
  have hZsq : ∀ k, Integrable (fun ω ↦ (Z k ω) ^ 2) μ := by
    intro k
    exact (memLp_two_iff_integrable_sq
      (((hZ.stronglyMeasurable k).mono (ℱ.le k)).aestronglyMeasurable)).1 (hZmemLp k)
  have hBracketEq :
      ∀ n, ⟨Z⟩[ℱ, μ] n =ᵐ[μ] A n := by
    intro n
    simpa [A, Z, Y] using stoppedProcess_predictablePart_sq_ae_eq (μ := μ) (ℱ := ℱ) hYsq τK hτK n
  have hAInt : ∀ n, Integrable (A n) μ := by
    intro n
    exact (integrableSquareVariation_of_integrableSq (μ := μ) (ℱ := ℱ) hZ hZsq n).congr
      (hBracketEq n)
  have hANonneg : ∀ n, 0 ≤ᵐ[μ] A n := by
    intro n
    filter_upwards [squareVariation_nonneg_ae hZ hZsq, hBracketEq n] with ω hω hEq
    simpa [hEq] using hω n
  have hPair :
      ∀ n m, n ≤ m → ∀ᵐ ω ∂μ, A n ω ≤ A m ω := by
    intro n m hnm
    filter_upwards
      [squareVariation_ae_mono_of_integrableSq (μ := μ) (ℱ := ℱ) hZ hZsq hnm,
        hBracketEq n, hBracketEq m] with ω hω hn hm
    simpa [A, hn, hm] using hω
  have hAMono :
      ∀ᵐ ω ∂μ, Monotone fun n ↦ A n ω := by
    have hAll :
        ∀ᵐ ω ∂μ, ∀ n m : ℕ, n ≤ m → A n ω ≤ A m ω := by
      refine ae_all_iff.2 ?_
      intro n
      refine ae_all_iff.2 ?_
      intro m
      by_cases hnm : n ≤ m
      · exact (hPair n m hnm).mono fun _ hω _ ↦ hω
      · exact Filter.Eventually.of_forall fun _ h ↦ False.elim (hnm h)
    filter_upwards [hAll] with ω hω
    exact fun n m hnm ↦ hω n m hnm
  exact ae_bddAbove_range_of_nonneg_mono_integral_bounded
    (μ := μ) hAInt hANonneg hAMono (((K : ℝ) + R) ^ 2)
    (centeredStoppedSquareVariation_expectation_le (μ := μ) (ℱ := ℱ) hX hbdd K)

/-- Helper for Exercise 11.2.5: convergence of the centered path forces bounded canonical square
variation almost surely. -/
lemma ae_bddAbove_squareVariation_of_centered_existsTendsto [SigmaFiniteFiltration μ ℱ]
    [IsProbabilityMeasure μ] (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R) :
    ∀ᵐ ω ∂μ,
      (∃ c : ℝ, Tendsto (fun n ↦ centeredProcess X n ω) atTop (𝓝 c)) →
        BddAbove (Set.range fun n ↦ ⟨centeredProcess X⟩[ℱ, μ] n ω) := by
  have hStoppedAll :
      ∀ᵐ ω ∂μ, ∀ K : ℕ,
        BddAbove (Set.range fun n ↦
          stoppedProcess (⟨centeredProcess X⟩[ℱ, μ]) (centeredAbsHitTime X K) n ω) := by
    exact ae_all_iff.2 fun K ↦ boundedStoppedCenteredSquareVariation_ae (μ := μ) (ℱ := ℱ) hX hbdd K
  filter_upwards [hStoppedAll] with ω hStoppedAll hconv
  rcases hconv with ⟨c, hc⟩
  rcases hc.bddAbove_range with ⟨u, hu⟩
  rcases hc.bddBelow_range with ⟨l, hl⟩
  let B : ℝ := max u (-l)
  have hBnonneg : 0 ≤ B := by
    have h0u : 0 ≤ u := by
      simpa [centeredProcess_zero] using hu (Set.mem_range_self 0)
    exact h0u.trans (le_max_left _ _)
  have hAbsLe : ∀ n, |centeredProcess X n ω| ≤ B := by
    intro n
    have hUpper : centeredProcess X n ω ≤ u := hu (Set.mem_range_self n)
    have hLower : l ≤ centeredProcess X n ω := hl (Set.mem_range_self n)
    have hUpper' : centeredProcess X n ω ≤ B := by
      exact hUpper.trans (le_max_left _ _)
    have hLower' : -B ≤ centeredProcess X n ω := by
      have hBL : -B ≤ l := by
        dsimp [B]
        linarith [le_max_right u (-l)]
      exact hBL.trans hLower
    exact abs_le.2 ⟨hLower', hUpper'⟩
  let K : ℕ := Nat.ceil B + 1
  have hBK : B < (K : ℝ) := by
    have hceil_le : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
    have hceil' : B < (Nat.ceil B : ℝ) + 1 := by
      linarith
    simpa [K, Nat.cast_add] using hceil'
  have hTop : centeredAbsHitTime X K ω = ⊤ := by
    refine (hittingAfter_eq_top_iff
      (u := fun n ω ↦ |centeredProcess X n ω|)
      (s := Set.Ici (K : ℝ)) (n := 0) (ω := ω)).2 ?_
    intro j _
    have hj : |centeredProcess X j ω| ≤ B := hAbsLe j
    have hj' : |centeredProcess X j ω| < (K : ℝ) := lt_of_le_of_lt hj hBK
    simpa [centeredAbsHitTime, leastGE, Set.mem_Ici, not_le] using hj'
  have hStopped :
      BddAbove (Set.range fun n ↦
        stoppedProcess (⟨centeredProcess X⟩[ℱ, μ]) (centeredAbsHitTime X K) n ω) := hStoppedAll K
  have hRange :
      Set.range (fun n ↦
        stoppedProcess (⟨centeredProcess X⟩[ℱ, μ]) (centeredAbsHitTime X K) n ω) =
        Set.range fun n ↦ ⟨centeredProcess X⟩[ℱ, μ] n ω := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨n, ?_⟩
      simpa [hTop] using
        (stoppedProcess_eq_of_le (u := ⟨centeredProcess X⟩[ℱ, μ])
          (τ := centeredAbsHitTime X K) (ω := ω) (i := n) (by
            rw [hTop]
            exact le_top)).symm
    · rintro ⟨n, rfl⟩
      refine ⟨n, ?_⟩
      simpa [hTop] using
        (stoppedProcess_eq_of_le (u := ⟨centeredProcess X⟩[ℱ, μ])
          (τ := centeredAbsHitTime X K) (ω := ω) (i := n) (by
            rw [hTop]
            exact le_top))
  simpa [hRange] using hStopped

/-
Exercise 11.2.5 is `source-facing`: it compares the textbook pathwise properties usually denoted
`C`, `A⁺`, `A⁻`, and `F` for a real-valued martingale. Here the primitive data are only the
martingale `X` and the bounded-difference hypothesis. The `core/canonical` owner for the fourth
event is the chapter square-variation process `⟨X⟩[ℱ, μ]`, while formula-level identities such as
Theorem 10.4 are only `bridge/view` statements. The public theorem below therefore keeps the
owner event itself in the fourth clause instead of a parallel increment-sum presentation.
-/

-- Proof sketch: apply the canonical martingale Borel-Cantelli comparison between pathwise upper
-- and lower boundedness and convergence for bounded-difference martingales. The fourth clause is
-- stated directly in the owner shape from Chapter 10, so no parallel local square-variation API
-- survives in the public statement.
/-- Exercise 11.2.5: for a real-valued martingale with bounded differences, the textbook events
`C`, `A^+`, `A^-`, and `F` are almost surely equivalent. Equivalently, for almost every sample
point, the following are equivalent: the path converges in `ℝ`, its values are bounded above, its
values are bounded below, and the canonical square variation `n ↦ ⟨X⟩[ℱ, μ] n` is bounded above.
-/
theorem martingale_convergence_tfae_of_bdd_difference
    [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ)
    {R : ℝ≥0} (hbdd : ∀ᵐ ω ∂μ, ∀ n, |X (n + 1) ω - X n ω| ≤ R) :
    ∀ᵐ ω ∂μ,
      List.TFAE [
        ∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c),
        BddAbove (Set.range fun n ↦ X n ω),
        BddBelow (Set.range fun n ↦ X n ω),
        BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω)
      ] := by
  classical
  have h12 :
      ∀ᵐ ω ∂μ,
        BddAbove (Set.range fun n ↦ X n ω) ↔
          ∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c) :=
    hX.submartingale.bddAbove_iff_exists_tendsto (R := R) hbdd
  have h23 :
      ∀ᵐ ω ∂μ,
        BddAbove (Set.range fun n ↦ X n ω) ↔
          BddBelow (Set.range fun n ↦ X n ω) :=
    hX.bddAbove_range_iff_bddBelow_range (R := R) hbdd
  have h14Centered :
      ∀ᵐ ω ∂μ,
        (∃ c : ℝ, Tendsto (fun n ↦ centeredProcess X n ω) atTop (𝓝 c)) →
          BddAbove (Set.range fun n ↦ ⟨centeredProcess X⟩[ℱ, μ] n ω) :=
    ae_bddAbove_squareVariation_of_centered_existsTendsto (μ := μ) (ℱ := ℱ) hX hbdd
  have h14 :
      ∀ᵐ ω ∂μ,
        (∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c)) →
          BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω) := by
    filter_upwards
      [h14Centered, centeredSquareVariation_bddAbove_ae_iff (μ := μ) (ℱ := ℱ) hX hbdd] with ω
        hCentered hSquare hConv
    -- Proof comment: convert the convergence event to the centered process, apply the centered
    -- converse, and transport bounded square variation back to `X`.
    exact hSquare.mp (hCentered ((centeredProcess_exists_tendsto_iff X ω).2 hConv))
  have h41Centered :
      ∀ᵐ ω ∂μ,
        BddAbove (Set.range fun n ↦ ⟨centeredProcess X⟩[ℱ, μ] n ω) →
          ∃ c : ℝ, Tendsto (fun n ↦ centeredProcess X n ω) atTop (𝓝 c) :=
    ae_exists_tendsto_of_bddAbove_centeredSquareVariation (μ := μ) (ℱ := ℱ) hX hbdd
  have h41 :
      ∀ᵐ ω ∂μ,
        BddAbove (Set.range fun n ↦ ⟨X⟩[ℱ, μ] n ω) →
          ∃ c : ℝ, Tendsto (fun n ↦ X n ω) atTop (𝓝 c) := by
    filter_upwards
      [h41Centered, centeredSquareVariation_bddAbove_ae_iff (μ := μ) (ℱ := ℱ) hX hbdd] with ω
        hCentered hSquare hBdd
    -- Proof comment: transport the square-variation bound to the centered process, use the
    -- centered localization lemma, then add back the initial value.
    exact (centeredProcess_exists_tendsto_iff X ω).1 (hCentered (hSquare.mpr hBdd))
  filter_upwards [h12, h23, h14, h41] with ω h12ω h23ω h14ω h41ω
  tfae_have 1 ↔ 2 := by
    simpa using h12ω.symm
  tfae_have 2 ↔ 3 := by
    exact h23ω
  tfae_have 1 → 4 := by
    intro hConv
    exact h14ω hConv
  tfae_have 4 → 1 := by
    -- Route correction: the converse direction is proved on the centered martingale by stopping
    -- at square-variation thresholds, then transported back to the original process.
    intro hSquare
    exact h41ω hSquare
  tfae_finish

end

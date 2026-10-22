/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω}
variable {μ : Measure Ω} {ℱ : Filtration ℕ m0}

section

variable {X : ℕ → Ω → ℝ}

local notation "squareProcess" => fun n ω ↦ X n ω ^ 2

/-- Helper for Theorem 10.4: at one time step, the conditional expectation of the square-process
increment agrees with the conditional expectation of the squared martingale increment. -/
lemma condExp_sqMomentDiff_eq_condExp_sqIncrement
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) (i : ℕ) :
    μ[(fun ω ↦ X (i + 1) ω ^ 2 - X i ω ^ 2) | ℱ i] =ᵐ[μ]
      μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] := by
  let inc : Ω → ℝ := fun ω ↦ X (i + 1) ω - X i ω
  let cross : Ω → ℝ := fun ω ↦ inc ω * X i ω
  have hXiMeas : StronglyMeasurable[ℱ i] (X i) := hX.stronglyMeasurable i
  have hXiLp : MemLp (X i) 2 μ :=
    (memLp_two_iff_integrable_sq ((hXiMeas.mono (ℱ.le i)).aestronglyMeasurable)).2 (hXsq i)
  have hXiSuccLp : MemLp (X (i + 1)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (((hX.stronglyMeasurable (i + 1)).mono (ℱ.le (i + 1))).aestronglyMeasurable)).2
      (hXsq (i + 1))
  have hIncLp : MemLp inc 2 μ := by
    simpa [inc] using hXiSuccLp.sub hXiLp
  have hIncInt : Integrable inc μ := by
    simpa [inc] using (hX.integrable (i + 1)).sub (hX.integrable i)
  have hCrossInt : Integrable cross μ := by
    simpa [cross] using MemLp.integrable_mul hIncLp hXiLp
  have hIncZero : μ[inc | ℱ i] =ᵐ[μ] 0 := by
    have hXiCond : μ[X i | ℱ i] =ᵐ[μ] X i := hX.condExp_ae_eq (le_rfl : i ≤ i)
    -- Rewrite the conditional expectation of the increment via the martingale relation.
    refine (condExp_sub (hX.integrable (i + 1)) (hX.integrable i) (ℱ i)).trans ?_
    refine ((hX.condExp_ae_eq (Nat.le_succ i)).sub hXiCond).trans ?_
    simp
  have hScaledCrossZero : (2 : ℝ) • (μ[inc | ℱ i] * X i) =ᵐ[μ] 0 := by
    filter_upwards [hIncZero] with ω hω
    simp [hω]
  -- Split the difference of squares into the squared increment and the martingale cross term.
  calc
    μ[(fun ω ↦ X (i + 1) ω ^ 2 - X i ω ^ 2) | ℱ i] =ᵐ[μ]
        μ[fun ω ↦ inc ω ^ 2 + (2 : ℝ) • cross ω | ℱ i] := by
      refine condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
      simp [inc, cross]
      ring
    _ =ᵐ[μ] μ[fun ω ↦ inc ω ^ 2 | ℱ i] + μ[(2 : ℝ) • cross | ℱ i] := by
      exact condExp_add hIncLp.integrable_sq (hCrossInt.const_mul 2) (ℱ i)
    _ =ᵐ[μ] μ[fun ω ↦ inc ω ^ 2 | ℱ i] + (2 : ℝ) • μ[cross | ℱ i] := by
      exact (Filter.EventuallyEq.rfl.add (condExp_smul (μ := μ) (m := ℱ i) (2 : ℝ) cross))
    _ =ᵐ[μ] μ[fun ω ↦ inc ω ^ 2 | ℱ i] + (2 : ℝ) • (μ[inc | ℱ i] * X i) := by
      filter_upwards [condExp_mul_of_stronglyMeasurable_right hXiMeas hCrossInt hIncInt] with ω hω
      simpa [cross] using hω
    _ =ᵐ[μ] μ[fun ω ↦ inc ω ^ 2 | ℱ i] + 0 := by
      exact Filter.EventuallyEq.rfl.add hScaledCrossZero
    _ =ᵐ[μ] μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] := by
      simp [inc]

/-- Helper for Theorem 10.4: integrating the one-step conditional identity turns the squared
increment into a difference of square moments. -/
lemma integral_sqIncrement_eq_sqMomentDiff [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) (i : ℕ) :
    μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2)] = μ[squareProcess (i + 1)] - μ[squareProcess i] := by
  -- Integrate the conditional-expectation identity and collapse both conditional expectations.
  calc
    μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2)] =
        μ[μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i]] := by
      symm
      exact integral_condExp (ℱ.le i)
    _ = μ[μ[(fun ω ↦ X (i + 1) ω ^ 2 - X i ω ^ 2) | ℱ i]] := by
      exact integral_congr_ae (condExp_sqMomentDiff_eq_condExp_sqIncrement hX hXsq i).symm
    _ = μ[(fun ω ↦ X (i + 1) ω ^ 2 - X i ω ^ 2)] := by
      exact integral_condExp (ℱ.le i)
    _ = μ[squareProcess (i + 1)] - μ[squareProcess i] := by
      simpa using integral_sub' (hXsq (i + 1)) (hXsq i)

/-- Helper for Theorem 10.4: the square-moment differences telescope over a finite range of
increments. -/
lemma sum_sqIncrement_eq_sqMomentDiff [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) :
    ∀ n, (∑ i ∈ Finset.range n, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2)]) =
      μ[squareProcess n] - μ[squareProcess 0]
  | 0 => by
      simp
  | n + 1 => by
      -- Add the last increment and use the one-step identity to telescope the scalar sum.
      rw [Finset.sum_range_succ, sum_sqIncrement_eq_sqMomentDiff hX hXsq n,
        integral_sqIncrement_eq_sqMomentDiff hX hXsq n]
      ring

/-- Helper for Theorem 10.4: the initial value can be pulled out of the terminal cross moment. -/
lemma integral_terminal_mul_initial_eq_initialSq [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) (n : ℕ) :
    μ[(fun ω ↦ X n ω * X 0 ω)] = μ[squareProcess 0] := by
  have hXnLp : MemLp (X n) 2 μ :=
    (memLp_two_iff_integrable_sq
      (((hX.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable)).2 (hXsq n)
  have hX0Lp : MemLp (X 0) 2 μ :=
    (memLp_two_iff_integrable_sq
      (((hX.stronglyMeasurable 0).mono (ℱ.le 0)).aestronglyMeasurable)).2 (hXsq 0)
  have hProdInt : Integrable (fun ω ↦ X n ω * X 0 ω) μ := by
    simpa using MemLp.integrable_mul hXnLp hX0Lp
  have hCond :
      μ[(fun ω ↦ X n ω * X 0 ω) | ℱ 0] =ᵐ[μ] squareProcess 0 := by
    -- Pull the initial value outside the conditional expectation and then use `E[X_n | ℱ_0] = X_0`.
    refine (condExp_mul_of_stronglyMeasurable_right (hX.stronglyMeasurable 0) hProdInt
      (hX.integrable n)).trans ?_
    refine ((hX.condExp_ae_eq (Nat.zero_le n)).mul Filter.EventuallyEq.rfl).trans ?_
    filter_upwards with ω
    change X 0 ω * X 0 ω = X 0 ω ^ 2
    ring
  -- Integrate the conditional identity to obtain the scalar cross-term formula.
  calc
    μ[(fun ω ↦ X n ω * X 0 ω)] = μ[μ[(fun ω ↦ X n ω * X 0 ω) | ℱ 0]] := by
      symm
      exact integral_condExp (ℱ.le 0)
    _ = μ[squareProcess 0] := by
      exact integral_congr_ae hCond

/-- Helper for Theorem 10.4: the variance of the terminal martingale increment equals the
difference of the terminal and initial square moments. -/
lemma variance_terminalIncrement_eq_sqMomentDiff [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) (n : ℕ) :
    Var[fun ω ↦ X n ω - X 0 ω; μ] = μ[squareProcess n] - μ[squareProcess 0] := by
  have hXnLp : MemLp (X n) 2 μ :=
    (memLp_two_iff_integrable_sq
      (((hX.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable)).2 (hXsq n)
  have hX0Lp : MemLp (X 0) 2 μ :=
    (memLp_two_iff_integrable_sq
      (((hX.stronglyMeasurable 0).mono (ℱ.le 0)).aestronglyMeasurable)).2 (hXsq 0)
  have hIncLp : MemLp (fun ω ↦ X n ω - X 0 ω) 2 μ := by
    simpa using hXnLp.sub hX0Lp
  have hCrossInt : Integrable (fun ω ↦ X n ω * X 0 ω) μ := by
    simpa using MemLp.integrable_mul hXnLp hX0Lp
  have hMeanEq : μ[X 0] = μ[X n] := by
    simpa using hX.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ
  have hMeanZero : μ[(fun ω ↦ X n ω - X 0 ω)] = 0 := by
    -- The martingale increment has zero expectation because martingale expectations are constant.
    change ∫ ω, (X n ω - X 0 ω) ∂μ = 0
    calc
      ∫ ω, (X n ω - X 0 ω) ∂μ = μ[X n] - μ[X 0] := by
        simpa using integral_sub' (hX.integrable n) (hX.integrable 0)
      _ = 0 := by rw [← hMeanEq, sub_self]
  have hMidInt : Integrable (fun ω ↦ X n ω ^ 2 - 2 * (X n ω * X 0 ω)) μ := by
    exact (hXsq n).sub (hCrossInt.const_mul 2)
  have hSecondMoment :
      ∫ ω, (X n ω - X 0 ω) ^ 2 ∂μ =
        ∫ ω, X n ω ^ 2 ∂μ - 2 * ∫ ω, X n ω * X 0 ω ∂μ + ∫ ω, X 0 ω ^ 2 ∂μ := by
    have hDecomp :
        (fun ω ↦ (X n ω - X 0 ω) ^ 2) =
          fun ω ↦ (X n ω ^ 2 - 2 * (X n ω * X 0 ω)) + X 0 ω ^ 2 := by
      ext ω
      ring
    have hMid :
        ∫ ω, (X n ω ^ 2 - 2 * (X n ω * X 0 ω)) ∂μ =
          ∫ ω, X n ω ^ 2 ∂μ - 2 * ∫ ω, X n ω * X 0 ω ∂μ := by
      calc
        ∫ ω, (X n ω ^ 2 - 2 * (X n ω * X 0 ω)) ∂μ =
            ∫ ω, X n ω ^ 2 ∂μ - ∫ ω, 2 * (X n ω * X 0 ω) ∂μ := by
          simpa using integral_sub' (hXsq n) (hCrossInt.const_mul 2)
        _ = ∫ ω, X n ω ^ 2 ∂μ - 2 * ∫ ω, X n ω * X 0 ω ∂μ := by
          rw [integral_const_mul]
    rw [hDecomp, integral_add hMidInt (hXsq 0), hMid]
  -- Expand the variance into a second moment and simplify the resulting cross term.
  rw [variance_eq_sub hIncLp]
  suffices hVariance :
      ∫ ω, (X n ω - X 0 ω) ^ 2 ∂μ = μ[squareProcess n] - μ[squareProcess 0] by
    simpa [hMeanZero, Pi.pow_apply] using hVariance
  calc
    ∫ ω, (X n ω - X 0 ω) ^ 2 ∂μ =
        ∫ ω, X n ω ^ 2 ∂μ - 2 * ∫ ω, X n ω * X 0 ω ∂μ + ∫ ω, X 0 ω ^ 2 ∂μ := hSecondMoment
    _ = μ[squareProcess n] - μ[squareProcess 0] := by
      rw [integral_terminal_mul_initial_eq_initialSq hX hXsq n]
      ring_nf

-- Proof sketch: expand the predictable compensator of the squared process and rewrite each
-- squared-process increment `(X (i + 1))^2 - (X i)^2` using the martingale identity so that only
-- the conditional expectation of the squared increment remains; the canonical `condExp` API makes
-- this an almost-everywhere identity at each fixed time.
/-- Formula (10.2) in Theorem 10.4: for a square-integrable discrete-time martingale,
the square variation process `⟨X⟩` realized by the predictable part of the squared process
satisfies formula (10.2)
almost everywhere at each time. -/
theorem predictablePart_sq_eq_sum_condExp_sq_increment
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) :
    ∀ n, ⟨X⟩[ℱ, μ] n =ᵐ[μ]
      fun ω ↦ ∑ i ∈ Finset.range n, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
  intro n
  -- Expand the predictable part into the sum of one-step conditional expectations.
  have hsum :
      (∑ i ∈ Finset.range n, μ[squareProcess (i + 1) - squareProcess i | ℱ i]) =ᵐ[μ]
        ∑ i ∈ Finset.range n, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] :=
    eventuallyEq_sum (s := Finset.range n) fun i _ ↦
      (by simpa [Pi.sub_apply] using
        condExp_sqMomentDiff_eq_condExp_sqIncrement hX hXsq i)
  filter_upwards [hsum] with ω hω
  simpa [predictablePart] using hω

/-- At each fixed time, Theorem 10.4 (1) is an almost-everywhere identity. -/
theorem squareVariation_eq_sum_condExp_sq_increment
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) (n : ℕ) :
    ⟨X⟩[ℱ, μ] n =ᵐ[μ]
      fun ω ↦ ∑ i ∈ Finset.range n, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
  simpa using predictablePart_sq_eq_sum_condExp_sq_increment hX hXsq n

-- Proof sketch: use the almost-everywhere identity from Theorem 10.4 (1) and linearity of
-- expectation to
-- rewrite the expectation of the square variation as a sum of second moments of the martingale
-- increments, then identify that sum with the variance of `X n - X 0` on the probability space.
/-- Theorem 10.4: For a square-integrable discrete-time martingale, the expectation of the
square variation at time `n` equals the variance of the martingale increment `X n - X 0`. -/
theorem squareVariation_expectation_eq_variance [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) (n : ℕ) :
    μ[⟨X⟩[ℱ, μ] n] = Var[fun ω ↦ X n ω - X 0 ω; μ] := by
  -- Normalize the square variation to a telescoping sum of second moments.
  calc
    μ[⟨X⟩[ℱ, μ] n] =
        μ[fun ω ↦ ∑ i ∈ Finset.range n, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω] := by
      exact integral_congr_ae (squareVariation_eq_sum_condExp_sq_increment hX hXsq n)
    _ = ∑ i ∈ Finset.range n, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2)] := by
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl fun i hi ↦ ?_
        exact integral_condExp (ℱ.le i)
      · intro i hi
        exact integrable_condExp
    _ = μ[squareProcess n] - μ[squareProcess 0] := sum_sqIncrement_eq_sqMomentDiff hX hXsq n
    _ = Var[fun ω ↦ X n ω - X 0 ω; μ] := by
      symm
      exact variance_terminalIncrement_eq_sqMomentDiff hX hXsq n

end

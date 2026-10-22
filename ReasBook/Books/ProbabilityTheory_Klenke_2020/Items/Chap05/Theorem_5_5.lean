/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

variable {Ω : Type u}

variable [MeasurableSpace Ω]

/-- Helper for Theorem 5.5: the textbook partial sums satisfy the usual one-step recursion
`S_{n+1} = S_n + X_{n+1}`. -/
theorem textbookPartialSum_succ (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum (fun k ↦ X (k + 1)) (n + 1) ω =
      partialSum (fun k ↦ X (k + 1)) n ω + X (n + 1) ω := by
  -- Split the shifted range sum at its top endpoint to isolate the new increment.
  rw [partialSum_apply, partialSum_apply]
  simpa using (Finset.sum_range_succ (fun i : ℕ ↦ X (i + 1) ω) n)

/-- Helper for Theorem 5.5: every deterministic textbook partial sum is integrable once `X 1`
is integrable and the summands are identically distributed. -/
theorem integrable_textbookPartialSum (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) (hX1_int : Integrable (X 1) P) :
    ∀ n, Integrable (partialSum (fun k ↦ X (k + 1)) n) P := by
  intro n
  induction n with
  | zero =>
      -- The empty partial sum is the zero random variable.
      rw [show partialSum (fun k ↦ X (k + 1)) 0 = (fun _ : Ω ↦ (0 : ℝ)) from by
        funext ω
        simp [partialSum]]
      exact integrable_const (0 : ℝ)
  | succ n ih =>
      -- Add the next increment, which is integrable by identical distribution.
      have hXn_int : Integrable (X (n + 1)) P := (hX_ident n).integrable_iff.mpr hX1_int
      refine (ih.add hXn_int).congr ?_
      filter_upwards with ω
      symm
      exact textbookPartialSum_succ X n ω

/-- Helper for Theorem 5.5: the expectation of the `n`-th textbook partial sum is
`n * 𝔼[X₁]`. -/
theorem integral_textbookPartialSum_eq_nat_mul_expectation (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) (hX1_int : Integrable (X 1) P) :
    ∀ n, ∫ ω, partialSum (fun k ↦ X (k + 1)) n ω ∂P = (n : ℝ) * ∫ ω, X 1 ω ∂P := by
  intro n
  induction n with
  | zero =>
      -- The zeroth partial sum has zero expectation.
      simp [partialSum]
  | succ n ih =>
      have hSn_int : Integrable (partialSum (fun k ↦ X (k + 1)) n) P :=
        integrable_textbookPartialSum P X hX_ident hX1_int n
      have hXn_int : Integrable (X (n + 1)) P := (hX_ident n).integrable_iff.mpr hX1_int
      -- Expand the next partial sum, then use linearity and identical distribution.
      calc
        ∫ ω, partialSum (fun k ↦ X (k + 1)) (n + 1) ω ∂P
            = ∫ ω, (partialSum (fun k ↦ X (k + 1)) n ω + X (n + 1) ω) ∂P := by
                rw [show (fun ω ↦ partialSum (fun k ↦ X (k + 1)) (n + 1) ω) =
                    (fun ω ↦ partialSum (fun k ↦ X (k + 1)) n ω + X (n + 1) ω) from by
                      funext ω
                      exact textbookPartialSum_succ X n ω]
        _ = (∫ ω, partialSum (fun k ↦ X (k + 1)) n ω ∂P) + ∫ ω, X (n + 1) ω ∂P := by
              rw [integral_add hSn_int hXn_int]
        _ = (n : ℝ) * ∫ ω, X 1 ω ∂P + ∫ ω, X 1 ω ∂P := by
              rw [ih, (hX_ident n).integral_eq]
        _ = ((n + 1 : ℕ) : ℝ) * ∫ ω, X 1 ω ∂P := by
              rw [Nat.cast_add, Nat.cast_one]
              ring

/-- Helper for Theorem 5.5: the absolute expectation of the `n`-th textbook partial sum is at
most `n * 𝔼[|X₁|]`. -/
theorem integral_abs_textbookPartialSum_le_nat_mul_integral_abs (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) (hX1_int : Integrable (X 1) P) :
    ∀ n, ∫ ω, |partialSum (fun k ↦ X (k + 1)) n ω| ∂P ≤ (n : ℝ) * ∫ ω, |X 1 ω| ∂P := by
  intro n
  induction n with
  | zero =>
      -- The empty partial sum has zero absolute expectation.
      simp [partialSum]
  | succ n ih =>
      have hSn_int : Integrable (partialSum (fun k ↦ X (k + 1)) n) P :=
        integrable_textbookPartialSum P X hX_ident hX1_int n
      have hXn_int : Integrable (X (n + 1)) P := (hX_ident n).integrable_iff.mpr hX1_int
      have hpoint :
          ∀ᵐ ω ∂P,
            |partialSum (fun k ↦ X (k + 1)) (n + 1) ω| ≤
              |partialSum (fun k ↦ X (k + 1)) n ω| + |X (n + 1) ω| := by
        -- Pointwise, the triangle inequality controls the next partial sum.
        filter_upwards with ω
        rw [textbookPartialSum_succ]
        exact abs_add_le _ _
      have h_abs_eq :
          ∫ ω, |X (n + 1) ω| ∂P = ∫ ω, |X 1 ω| ∂P := by
        simpa [Real.norm_eq_abs] using (hX_ident n).norm.integral_eq
      have hupper_int :
          Integrable (fun ω ↦ |partialSum (fun k ↦ X (k + 1)) n ω| + |X (n + 1) ω|) P :=
        hSn_int.abs.add hXn_int.abs
      -- Integrate the pointwise triangle inequality and identify the common absolute expectation.
      calc
        ∫ ω, |partialSum (fun k ↦ X (k + 1)) (n + 1) ω| ∂P
            ≤ ∫ ω, (|partialSum (fun k ↦ X (k + 1)) n ω| + |X (n + 1) ω|) ∂P := by
                exact integral_mono_ae (integrable_textbookPartialSum P X hX_ident hX1_int (n + 1)).abs
                  hupper_int hpoint
        _ = (∫ ω, |partialSum (fun k ↦ X (k + 1)) n ω| ∂P) + ∫ ω, |X (n + 1) ω| ∂P := by
              rw [integral_add hSn_int.abs hXn_int.abs]
        _ = (∫ ω, |partialSum (fun k ↦ X (k + 1)) n ω| ∂P) + ∫ ω, |X 1 ω| ∂P := by
              rw [h_abs_eq]
        _ ≤ (n : ℝ) * ∫ ω, |X 1 ω| ∂P + ∫ ω, |X 1 ω| ∂P := by
              gcongr
        _ = ((n + 1 : ℕ) : ℝ) * ∫ ω, |X 1 ω| ∂P := by
              rw [Nat.cast_add, Nat.cast_one]
              ring

/-- Helper for Theorem 5.5: each deterministic textbook partial sum is independent of the atom
`{T = n}` when `T` is independent of the whole sequence. -/
theorem textbookPartialSum_indep_time_atom (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ)
    (X : ℕ → Ω → ℝ) (hTX_indep : T ⟂ᵢ[P] (fun ω ↦ fun n ↦ X (n + 1) ω)) (n : ℕ) :
    (fun ω ↦ partialSum (fun k ↦ X (k + 1)) n ω) ⟂ᵢ[P]
      (fun ω ↦ if T ω = n then (1 : ℝ) else 0) := by
  let seq : Ω → ℕ → ℝ := fun ω k ↦ X (k + 1) ω
  let ψ : (ℕ → ℝ) → ℝ := fun x ↦ ∑ i ∈ Finset.range n, x i
  let χ : ℕ → ℝ := fun k ↦ if k = n then 1 else 0
  have hψ_meas : Measurable ψ := by
    -- The partial-sum functional depends on finitely many measurable coordinates.
    refine Finset.measurable_sum (Finset.range n) ?_
    intro i hi
    exact measurable_pi_apply i
  have hχ_meas : Measurable χ := Measurable.of_discrete
  have hseq_eq : (fun ω ↦ ψ (seq ω)) = fun ω ↦ partialSum (fun k ↦ X (k + 1)) n ω := by
    -- The sequence functional is exactly the shifted partial sum.
    funext ω
    simp [seq, ψ, partialSum]
  have hatom_eq : (fun ω ↦ χ (T ω)) = (fun ω ↦ if T ω = n then (1 : ℝ) else 0) := by
    funext ω
    simp [χ]
  -- Compose the independence of `T` from the whole sequence with the finite partial-sum and atom
  -- functionals.
  have hmain : (fun ω ↦ ψ (seq ω)) ⟂ᵢ[P] fun ω ↦ χ (T ω) := by
    have hcomp := hTX_indep.symm.comp hψ_meas hχ_meas
    simpa [seq, Function.comp] using hcomp
  simpa [hseq_eq, hatom_eq] using hmain

/-- Helper for Theorem 5.5: collapsing the finite sum over the atoms `{t = n}` leaves only the
matching index when it lies in the truncation range. -/
theorem sum_range_mul_time_atom_eq_if_le (a : ℕ → ℝ) (N t : ℕ) :
    ∑ n ∈ Finset.range (N + 1), a n * (if t = n then (1 : ℝ) else 0) =
      if t ≤ N then a t else 0 := by
  -- Rewrite the atom factor into a Kronecker-delta sum and evaluate the unique surviving term.
  calc
    ∑ n ∈ Finset.range (N + 1), a n * (if t = n then (1 : ℝ) else 0)
        = ∑ n ∈ Finset.range (N + 1), if t = n then a n else 0 := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases h : t = n
            · simp [h]
            · simp [h]
    _ = if t ∈ Finset.range (N + 1) then a t else 0 := by
          simpa using Finset.sum_ite_eq (Finset.range (N + 1)) t a
    _ = if t ≤ N then a t else 0 := by
          simp [Finset.mem_range]

/-- Helper for Theorem 5.5: the atom indicator `{T = n}` is almost everywhere strongly
measurable once the real-valued time variable is integrable. -/
theorem time_atom_aestronglyMeasurable (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ)
    (hT_int : Integrable (fun ω ↦ (T ω : ℝ)) P) (n : ℕ) :
    AEStronglyMeasurable (fun ω ↦ if T ω = n then (1 : ℝ) else 0) P := by
  let χ : ℝ → ℝ := fun x ↦ if x = n then 1 else 0
  have hχ_meas : Measurable χ := by
    -- The atom indicator is measurable as an `if` over a singleton fiber in `ℝ`.
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (isClosed_eq continuous_id continuous_const).measurableSet
  have hχ_eq : (fun ω ↦ if T ω = n then (1 : ℝ) else 0) = χ ∘ fun ω ↦ (T ω : ℝ) := by
    funext ω
    simp [χ]
  rw [hχ_eq]
  exact (hχ_meas.comp_aemeasurable hT_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable

/-- Helper for Theorem 5.5: every atom indicator `{T = n}` is integrable because it is bounded by
the constant function `1`. -/
theorem time_atom_integrable (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ)
    (hT_int : Integrable (fun ω ↦ (T ω : ℝ)) P) (n : ℕ) :
    Integrable (fun ω ↦ if T ω = n then (1 : ℝ) else 0) P := by
  -- Compare the atom indicator with the integrable constant bound `1`.
  refine Integrable.mono' (integrable_const 1) (time_atom_aestronglyMeasurable P T hT_int n) ?_
  filter_upwards with ω
  by_cases h : T ω = n
  · simp [h]
  · simp [h]

/-- Helper for Theorem 5.5: the truncated stopped sum has expectation equal to the common
expectation of the increments times the truncated time variable. -/
theorem integral_stopped_sum_truncation_eq_expectation_mul_time_truncation (P : Measure Ω)
    [IsProbabilityMeasure P] (T : Ω → ℕ) (X : ℕ → Ω → ℝ)
    (hTX_indep : T ⟂ᵢ[P] (fun ω ↦ fun n ↦ X (n + 1) ω))
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hT_int : Integrable (fun ω ↦ (T ω : ℝ)) P) (hX1_int : Integrable (X 1) P) (N : ℕ) :
    ∫ ω, ∑ n ∈ Finset.range (N + 1),
        partialSum (fun k ↦ X (k + 1)) n ω * (if T ω = n then (1 : ℝ) else 0) ∂P =
      (∫ ω, X 1 ω ∂P) *
        ∫ ω, ∑ n ∈ Finset.range (N + 1), (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P := by
  have hterm_int :
      ∀ n ∈ Finset.range (N + 1),
        Integrable
          (fun ω ↦ partialSum (fun k ↦ X (k + 1)) n ω * (if T ω = n then (1 : ℝ) else 0)) P := by
    intro n hn
    -- Each finite partial sum is integrable, and so is the bounded time atom.
    exact ProbabilityTheory.IndepFun.integrable_mul
      (textbookPartialSum_indep_time_atom P T X hTX_indep n)
      (integrable_textbookPartialSum P X hX_ident hX1_int n)
      (time_atom_integrable P T hT_int n)
  have htime_term_int :
      ∀ n ∈ Finset.range (N + 1),
        Integrable (fun ω ↦ (n : ℝ) * (if T ω = n then (1 : ℝ) else 0)) P := by
    intro n hn
    exact (time_atom_integrable P T hT_int n).const_mul (n : ℝ)
  -- Expand the finite truncation, factor each fiber by independence, and regroup the common
  -- expectation `𝔼[X₁]`.
  rw [integral_finset_sum _ hterm_int]
  calc
    ∑ n ∈ Finset.range (N + 1),
        ∫ ω, partialSum (fun k ↦ X (k + 1)) n ω * (if T ω = n then (1 : ℝ) else 0) ∂P
        = ∑ n ∈ Finset.range (N + 1),
            ((∫ ω, partialSum (fun k ↦ X (k + 1)) n ω ∂P) *
              ∫ ω, (if T ω = n then (1 : ℝ) else 0) ∂P) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simpa using ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral
              (textbookPartialSum_indep_time_atom P T X hTX_indep n)
              (integrable_textbookPartialSum P X hX_ident hX1_int n).aestronglyMeasurable
              (time_atom_aestronglyMeasurable P T hT_int n)
    _ = ∑ n ∈ Finset.range (N + 1),
          (((n : ℝ) * ∫ ω, X 1 ω ∂P) *
            ∫ ω, (if T ω = n then (1 : ℝ) else 0) ∂P) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [integral_textbookPartialSum_eq_nat_mul_expectation P X hX_ident hX1_int n]
    _ = (∫ ω, X 1 ω ∂P) *
          ∑ n ∈ Finset.range (N + 1),
            ∫ ω, (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [MeasureTheory.integral_const_mul]
          ring
    _ = (∫ ω, X 1 ω ∂P) *
          ∫ ω, ∑ n ∈ Finset.range (N + 1),
            (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P := by
          rw [integral_finset_sum _ htime_term_int]

/-- Helper for Theorem 5.5: the absolute expectation of the truncated stopped sum is controlled by
the common absolute expectation of the increments times the truncated time variable. -/
theorem integral_abs_stopped_sum_truncation_le_abs_expectation_mul_time_truncation
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ) (X : ℕ → Ω → ℝ)
    (hTX_indep : T ⟂ᵢ[P] (fun ω ↦ fun n ↦ X (n + 1) ω))
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hT_int : Integrable (fun ω ↦ (T ω : ℝ)) P) (hX1_int : Integrable (X 1) P) (N : ℕ) :
    ∫ ω, ∑ n ∈ Finset.range (N + 1),
        |partialSum (fun k ↦ X (k + 1)) n ω| * (if T ω = n then (1 : ℝ) else 0) ∂P ≤
      (∫ ω, |X 1 ω| ∂P) *
        ∫ ω, ∑ n ∈ Finset.range (N + 1), (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P := by
  have hterm_int :
      ∀ n ∈ Finset.range (N + 1),
        Integrable
          (fun ω ↦ |partialSum (fun k ↦ X (k + 1)) n ω| * (if T ω = n then (1 : ℝ) else 0)) P := by
    intro n hn
    have habs_indep :
        (fun ω ↦ |partialSum (fun k ↦ X (k + 1)) n ω|) ⟂ᵢ[P]
          (fun ω ↦ if T ω = n then (1 : ℝ) else 0) := by
      simpa [Function.comp] using
        (textbookPartialSum_indep_time_atom P T X hTX_indep n).comp measurable_abs measurable_id
    exact ProbabilityTheory.IndepFun.integrable_mul habs_indep
      (integrable_textbookPartialSum P X hX_ident hX1_int n).abs
      (time_atom_integrable P T hT_int n)
  have htime_term_int :
      ∀ n ∈ Finset.range (N + 1),
        Integrable (fun ω ↦ (n : ℝ) * (if T ω = n then (1 : ℝ) else 0)) P := by
    intro n hn
    exact (time_atom_integrable P T hT_int n).const_mul (n : ℝ)
  -- Factor the absolute-value truncation on each fiber and insert the deterministic absolute
  -- expectation bound for the partial sums.
  rw [integral_finset_sum _ hterm_int]
  calc
    ∑ n ∈ Finset.range (N + 1),
        ∫ ω, |partialSum (fun k ↦ X (k + 1)) n ω| * (if T ω = n then (1 : ℝ) else 0) ∂P
        = ∑ n ∈ Finset.range (N + 1),
            ((∫ ω, |partialSum (fun k ↦ X (k + 1)) n ω| ∂P) *
              ∫ ω, (if T ω = n then (1 : ℝ) else 0) ∂P) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have habs_indep :
                (fun ω ↦ |partialSum (fun k ↦ X (k + 1)) n ω|) ⟂ᵢ[P]
                  (fun ω ↦ if T ω = n then (1 : ℝ) else 0) := by
              simpa [Function.comp] using
                (textbookPartialSum_indep_time_atom P T X hTX_indep n).comp
                  measurable_abs measurable_id
            simpa using ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral habs_indep
              (integrable_textbookPartialSum P X hX_ident hX1_int n).abs.aestronglyMeasurable
              (time_atom_aestronglyMeasurable P T hT_int n)
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          (((n : ℝ) * ∫ ω, |X 1 ω| ∂P) *
            ∫ ω, (if T ω = n then (1 : ℝ) else 0) ∂P) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hatom_nonneg :
              0 ≤ ∫ ω, (if T ω = n then (1 : ℝ) else 0) ∂P := by
            exact integral_nonneg fun ω ↦ by
              by_cases h : T ω = n
              · simp [h]
              · simp [h]
          exact mul_le_mul_of_nonneg_right
            (integral_abs_textbookPartialSum_le_nat_mul_integral_abs P X hX_ident hX1_int n)
            hatom_nonneg
    _ = (∫ ω, |X 1 ω| ∂P) *
          ∑ n ∈ Finset.range (N + 1),
            ∫ ω, (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [MeasureTheory.integral_const_mul]
          ring
    _ = (∫ ω, |X 1 ω| ∂P) *
          ∫ ω, ∑ n ∈ Finset.range (N + 1),
            (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P := by
          rw [integral_finset_sum _ htime_term_int]

-- Proof sketch: first show that the stopped value of the textbook partial-sum process is
-- integrable by conditioning on the fibers `{ω | T ω = n}` and using the integrability of `T`
-- together with the common integrability of the i.i.d. summands; then compute the integral on each
-- fiber and sum the resulting series.
/-- Theorem 5.5: Wald's identity for a nat-valued counting variable `T` independent of an
identically distributed sequence `X₁, X₂, …`; the stopped value of the textbook partial-sum
process at `T` is integrable and its expectation is the product of the expectations of `T` and
`X₁`. -/
theorem wald_identity (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ)
    (X : ℕ → Ω → ℝ) (hTX_indep : T ⟂ᵢ[P] (fun ω ↦ fun n ↦ X (n + 1) ω))
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hT_int : Integrable (fun ω ↦ (T ω : ℝ)) P) (hX1_int : Integrable (X 1) P) :
    Integrable (stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (T ω : WithTop ℕ))) P ∧
      ∫ ω, stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (T ω : WithTop ℕ)) ω ∂P =
        (∫ ω, (T ω : ℝ) ∂P) * ∫ ω, X 1 ω ∂P := by
  let Y : Ω → ℝ := stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (T ω : WithTop ℕ))
  let F : ℕ → Ω → ℝ := fun N ω ↦
    ∑ n ∈ Finset.range (N + 1),
      partialSum (fun k ↦ X (k + 1)) n ω * (if T ω = n then (1 : ℝ) else 0)
  let G : ℕ → Ω → ℝ := fun N ω ↦
    ∑ n ∈ Finset.range (N + 1),
      |partialSum (fun k ↦ X (k + 1)) n ω| * (if T ω = n then (1 : ℝ) else 0)
  let W : ℕ → Ω → ℝ := fun N ω ↦
    ∑ n ∈ Finset.range (N + 1), (n : ℝ) * (if T ω = n then (1 : ℝ) else 0)
  have hY_eq : Y = fun ω ↦ partialSum (fun k ↦ X (k + 1)) (T ω) ω := by
    funext ω
    change partialSum (fun k ↦ X (k + 1)) ((T ω : WithTop ℕ)).untopA ω =
      partialSum (fun k ↦ X (k + 1)) (T ω) ω
    rfl
  have hF_int : ∀ N, Integrable (F N) P := by
    intro N
    -- Each signed truncation is a finite sum of integrable fiber contributions.
    exact integrable_finset_sum _ fun n hn ↦
      ProbabilityTheory.IndepFun.integrable_mul
        (textbookPartialSum_indep_time_atom P T X hTX_indep n)
        (integrable_textbookPartialSum P X hX_ident hX1_int n)
        (time_atom_integrable P T hT_int n)
  have hG_int : ∀ N, Integrable (G N) P := by
    intro N
    -- Each absolute truncation is a finite sum of integrable nonnegative fiber contributions.
    exact integrable_finset_sum _ fun n hn ↦ by
      have habs_indep :
          (fun ω ↦ |partialSum (fun k ↦ X (k + 1)) n ω|) ⟂ᵢ[P]
            (fun ω ↦ if T ω = n then (1 : ℝ) else 0) := by
        simpa [Function.comp] using
          (textbookPartialSum_indep_time_atom P T X hTX_indep n).comp
            measurable_abs measurable_id
      exact ProbabilityTheory.IndepFun.integrable_mul habs_indep
        (integrable_textbookPartialSum P X hX_ident hX1_int n).abs
        (time_atom_integrable P T hT_int n)
  have hF_eq :
      ∀ N ω, F N ω = if T ω ≤ N then Y ω else 0 := by
    intro N ω
    -- Collapse the finite atom sum to the unique active fiber `{T = T ω}`.
    simpa [F, hY_eq] using
      (sum_range_mul_time_atom_eq_if_le
        (fun n ↦ partialSum (fun k ↦ X (k + 1)) n ω) N (T ω))
  have hG_eq :
      ∀ N ω, G N ω = if T ω ≤ N then |Y ω| else 0 := by
    intro N ω
    -- The absolute truncation is the cutoff version of `|S_T|`.
    simpa [G, hY_eq] using
      (sum_range_mul_time_atom_eq_if_le
        (fun n ↦ |partialSum (fun k ↦ X (k + 1)) n ω|) N (T ω))
  have hW_eq :
      ∀ N ω, W N ω = if T ω ≤ N then (T ω : ℝ) else 0 := by
    intro N ω
    -- The time truncation is the cutoff version of the counting variable itself.
    simpa [W] using (sum_range_mul_time_atom_eq_if_le (fun n ↦ (n : ℝ)) N (T ω))
  have hW_int : ∀ N, Integrable (W N) P := by
    intro N
    have hχ_meas : Measurable (fun x : ℝ ↦ if x ≤ N then x else 0) := by
      -- The truncation map on `ℝ` is measurable.
      refine Measurable.ite ?_ measurable_id measurable_const
      exact (isClosed_le continuous_id continuous_const).measurableSet
    have hW_aesm : AEStronglyMeasurable (W N) P := by
      have hcomp :
          AEStronglyMeasurable ((fun x : ℝ ↦ if x ≤ N then x else 0) ∘ fun ω ↦ (T ω : ℝ)) P :=
        (hχ_meas.comp_aemeasurable hT_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      have hcomp_eq :
          ((fun x : ℝ ↦ if x ≤ N then x else 0) ∘ fun ω ↦ (T ω : ℝ)) = W N := by
        funext ω
        simp [hW_eq N ω]
      simpa [hcomp_eq] using hcomp
    -- The cutoff time variable is dominated by the original integrable time variable.
    refine Integrable.mono' hT_int hW_aesm ?_
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hW_eq N ω, h]
    · simp [hW_eq N ω, h, Nat.cast_nonneg]
  have hF_tendsto :
      ∀ᵐ ω ∂P, Filter.Tendsto (fun N ↦ F N ω) Filter.atTop (nhds (Y ω)) := by
    -- Route correction: after rewriting the truncations as cutoff functions, the limit is
    -- eventually constant instead of a raw limit of fiber sums.
    filter_upwards with ω
    have hEq : (fun _ : ℕ ↦ Y ω) =ᶠ[Filter.atTop] fun N ↦ F N ω := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨T ω, ?_⟩
      intro N hN
      simp [hF_eq, hN]
    exact Filter.Tendsto.congr' hEq tendsto_const_nhds
  have hY_aesm : AEStronglyMeasurable Y P :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop (fun N ↦ (hF_int N).aestronglyMeasurable)
      hF_tendsto
  have hW_nonneg : ∀ N, 0 ≤ᶠ[ae P] W N := by
    intro N
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hW_eq N ω, h, Nat.cast_nonneg]
    · simp [hW_eq N ω, h]
  have hW_le_time : ∀ N, ∀ᵐ ω ∂P, W N ω ≤ (T ω : ℝ) := by
    intro N
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hW_eq N ω, h]
    · simp [hW_eq N ω, h, Nat.cast_nonneg]
  have hW_integral_le_time : ∀ N, ∫ ω, W N ω ∂P ≤ ∫ ω, (T ω : ℝ) ∂P := by
    intro N
    exact integral_mono_ae (hW_int N) hT_int (hW_le_time N)
  have habsX1_nonneg : 0 ≤ ∫ ω, |X 1 ω| ∂P := by
    exact integral_nonneg fun ω ↦ abs_nonneg _
  let C : ℝ := (∫ ω, |X 1 ω| ∂P) * ∫ ω, (T ω : ℝ) ∂P
  have hG_integral_bound : ∀ N, ∫ ω, G N ω ∂P ≤ C := by
    intro N
    -- Combine the truncation-level bound with the integrable domination of the truncated time.
    calc
      ∫ ω, G N ω ∂P
          ≤ (∫ ω, |X 1 ω| ∂P) * ∫ ω, W N ω ∂P := by
              simpa [G, W] using
                integral_abs_stopped_sum_truncation_le_abs_expectation_mul_time_truncation
                  P T X hTX_indep hX_ident hT_int hX1_int N
      _ ≤ (∫ ω, |X 1 ω| ∂P) * ∫ ω, (T ω : ℝ) ∂P := by
            exact mul_le_mul_of_nonneg_left (hW_integral_le_time N) habsX1_nonneg
  have hG_nonneg : ∀ N, 0 ≤ᶠ[ae P] G N := by
    intro N
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hG_eq N ω, h, abs_nonneg]
    · simp [hG_eq N ω, h]
  have hG_lintegral_tendsto :
      Filter.Tendsto
        (fun N ↦ ∫⁻ ω, ENNReal.ofReal (G N ω) ∂P) Filter.atTop
        (nhds (∫⁻ ω, ENNReal.ofReal |Y ω| ∂P)) := by
    -- The absolute truncations increase pointwise to `|S_T|`.
    refine MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
    · intro N
      simpa using (hG_int N).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    · filter_upwards with ω
      intro m n hmn
      by_cases hm : T ω ≤ m
      · have hn : T ω ≤ n := le_trans hm hmn
        simp [hG_eq, hm, hn]
      · by_cases hn : T ω ≤ n
        · simp [hG_eq, hm, hn]
        · simp [hG_eq, hm, hn]
    · filter_upwards with ω
      have hEq :
          (fun _ : ℕ ↦ ENNReal.ofReal |Y ω|) =ᶠ[Filter.atTop]
            fun N ↦ ENNReal.ofReal (G N ω) := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨T ω, ?_⟩
        intro N hN
        simp [hG_eq, hN]
      exact Filter.Tendsto.congr' hEq tendsto_const_nhds
  have hG_lintegral_bound :
      ∫⁻ ω, ENNReal.ofReal |Y ω| ∂P ≤ ENNReal.ofReal C := by
    refine le_of_tendsto' hG_lintegral_tendsto ?_
    intro N
    calc
      ∫⁻ ω, ENNReal.ofReal (G N ω) ∂P = ENNReal.ofReal (∫ ω, G N ω ∂P) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hG_int N) (hG_nonneg N)]
      _ ≤ ENNReal.ofReal C := by
        exact ENNReal.ofReal_le_ofReal (hG_integral_bound N)
  have habsY_hfi : HasFiniteIntegral (fun ω ↦ |Y ω|) P := by
    refine (MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω ↦ abs_nonneg _)).2 ?_
    exact lt_of_le_of_lt hG_lintegral_bound ENNReal.ofReal_lt_top
  have hY_hfi : HasFiniteIntegral Y P := by
    have hnorm_hfi : HasFiniteIntegral (fun ω ↦ ‖Y ω‖) P := by
      simpa [Real.norm_eq_abs] using habsY_hfi
    exact (MeasureTheory.hasFiniteIntegral_norm_iff Y).1 hnorm_hfi
  have hY_int : Integrable Y P := ⟨hY_aesm, hY_hfi⟩
  have hF_bound : ∀ N, ∀ᵐ ω ∂P, ‖F N ω‖ ≤ |Y ω| := by
    intro N
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hF_eq N ω, h, Real.norm_eq_abs]
    · simp [hF_eq N ω, h]
  have hF_integral_tendsto :
      Filter.Tendsto (fun N ↦ ∫ ω, F N ω ∂P) Filter.atTop (nhds (∫ ω, Y ω ∂P)) := by
    -- With `S_T` now known integrable, the signed truncations converge by dominated convergence.
    exact MeasureTheory.tendsto_integral_of_dominated_convergence (fun ω ↦ |Y ω|)
      (fun N ↦ (hF_int N).aestronglyMeasurable) hY_int.abs hF_bound hF_tendsto
  have hW_tendsto :
      ∀ᵐ ω ∂P, Filter.Tendsto (fun N ↦ W N ω) Filter.atTop (nhds ((T ω : ℝ))) := by
    filter_upwards with ω
    have hEq : (fun _ : ℕ ↦ (T ω : ℝ)) =ᶠ[Filter.atTop] fun N ↦ W N ω := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨T ω, ?_⟩
      intro N hN
      simp [hW_eq, hN]
    exact Filter.Tendsto.congr' hEq tendsto_const_nhds
  have hW_bound : ∀ N, ∀ᵐ ω ∂P, ‖W N ω‖ ≤ (T ω : ℝ) := by
    intro N
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hW_eq N ω, h]
    · simp [hW_eq N ω, h, Nat.cast_nonneg]
  have hW_integral_tendsto :
      Filter.Tendsto (fun N ↦ ∫ ω, W N ω ∂P) Filter.atTop
        (nhds (∫ ω, (T ω : ℝ) ∂P)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence (fun ω ↦ (T ω : ℝ))
      (fun N ↦ (hW_int N).aestronglyMeasurable) hT_int hW_bound hW_tendsto
  have htrunc_eq :
      (fun N ↦ ∫ ω, F N ω ∂P) =ᶠ[Filter.atTop]
        fun N ↦ (∫ ω, X 1 ω ∂P) * ∫ ω, W N ω ∂P := by
    exact Filter.Eventually.of_forall fun N ↦ by
      simpa [F, W] using
        integral_stopped_sum_truncation_eq_expectation_mul_time_truncation
          P T X hTX_indep hX_ident hT_int hX1_int N
  have hright_tendsto :
      Filter.Tendsto (fun N ↦ (∫ ω, X 1 ω ∂P) * ∫ ω, W N ω ∂P) Filter.atTop
        (nhds ((∫ ω, X 1 ω ∂P) * ∫ ω, (T ω : ℝ) ∂P)) := by
    exact Filter.Tendsto.const_mul (∫ ω, X 1 ω ∂P) hW_integral_tendsto
  have h_expectation :
      ∫ ω, Y ω ∂P = (∫ ω, X 1 ω ∂P) * ∫ ω, (T ω : ℝ) ∂P := by
    exact tendsto_nhds_unique (Filter.Tendsto.congr' htrunc_eq hF_integral_tendsto) hright_tendsto
  exact ⟨by simpa [Y] using hY_int, by simpa [Y, mul_comm] using h_expectation⟩

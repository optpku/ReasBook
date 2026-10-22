/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Corollary_6_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Exercise 6.1.4: the chapter's sequential `partialSum` agrees with the canonical
`Fin n`-indexed finite-sum owner API. -/
private lemma partialSum_eq_sum_univ (X : ℕ → Ω → ℝ) (n : ℕ) :
    partialSum X n = ∑ i : Fin n, X i := by
  -- Proof comment: rewrite the range sum defining `partialSum` as the corresponding `Fin n` sum.
  ext ω
  simpa [partialSum] using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) n).symm

/-- Helper for Exercise 6.1.4: almost-everywhere equality of the summands transfers to the
corresponding partial sums. -/
private lemma partialSum_ae_eq_of_forall_ae_eq
    (P : Measure Ω) {X Y : ℕ → Ω → ℝ} (hXY : ∀ n, X n =ᵐ[P] Y n) :
    ∀ n, partialSum X n =ᵐ[P] partialSum Y n := by
  intro n
  induction n with
  | zero =>
      exact Filter.Eventually.of_forall fun ω ↦ by simp [partialSum]
  | succ n ih =>
      -- Proof comment: compare the recursive prefix decomposition term by term.
      filter_upwards [ih, hXY n] with ω hprefix hterm
      rw [partialSum_apply, partialSum_apply] at hprefix
      simp [partialSum_apply, Finset.sum_range_succ, hprefix, hterm]

/-- Helper for Exercise 6.1.4: square integrability of every increment propagates to square
integrability of every finite partial sum. -/
private lemma partialSum_memLp_two_of_memLp_two
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX_memLp : ∀ n, MemLp (X n) 2 P) :
    ∀ n, MemLp (partialSum X n) 2 P := by
  intro n
  -- Proof comment: expand the partial sum as a finite sum and use stability of `MemLp` under
  -- finite addition.
  simpa [partialSum] using
    (memLp_finset_sum (Finset.range n) fun i _ ↦ hX_memLp i)

/-- Helper for Exercise 6.1.4: centered increments give centered finite partial sums. -/
private lemma partialSum_integral_zero_of_integral_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_memLp : ∀ n, MemLp (X n) 2 P) (hX_centered : ∀ n, P[X n] = 0) :
    ∀ n, P[partialSum X n] = 0 := by
  intro n
  -- Proof comment: integrate the finite-sum expression termwise and use the centeredness of each
  -- increment.
  change ∫ ω, ∑ i ∈ Finset.range n, X i ω ∂P = 0
  rw [integral_finset_sum]
  · exact Finset.sum_eq_zero fun i _ ↦ hX_centered i
  · intro i _
    exact (hX_memLp i).integrable (by norm_num)

/-- Helper for Exercise 6.1.4: pairwise uncorrelated square-integrable increments have additive
partial-sum variances. -/
private lemma partialSum_variance_eq_sum_of_pairwise_uncorrelated
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_uncorrelated : Pairwise fun i j ↦ cov[X i, X j; P] = 0) :
    ∀ n, Var[partialSum X n; P] = ∑ i ∈ Finset.range n, Var[X i; P] := by
  intro n
  let Y : Fin n → Ω → ℝ := fun i ↦ X i
  have hY_memLp : ∀ i, MemLp (Y i) 2 P := by
    intro i
    exact hX_memLp i
  have hY_uncorrelated : Pairwise fun i j ↦ cov[Y i, Y j; P] = 0 := by
    intro i j hij
    exact hX_uncorrelated (show (i : ℕ) ≠ j from fun h ↦ hij (Fin.ext h))
  -- Proof comment: pass to the canonical `Fin n` family and apply the finite variance-additivity
  -- theorem for pairwise uncorrelated variables.
  calc
    Var[partialSum X n; P] = Var[∑ i, Y i; P] := by
      rw [partialSum_eq_sum_univ X n]
    _ = ∑ i, Var[Y i; P] := by
      simpa using variance_sum_eq_sum_variance_of_pairwise_uncorrelated hY_memLp hY_uncorrelated
    _ = ∑ i ∈ Finset.range n, Var[X i; P] := by
      simpa [Y] using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ Var[X i; P]) n)

-- Proof sketch: the variances of the partial sums are the finite sums of the summable variance
-- series because the terms are independent and centered, so the partial sums form a Cauchy family
-- in `L²`. Use completeness of `L²` to obtain a square-integrable limit and then apply the
-- almost-sure convergence criterion from summable square-integrable tails.
/-- Exercise 6.1.4: If `X₁, X₂, …` is an independent sequence of centered square-integrable real
random variables with summable variances, then the partial sums converge almost surely to a
square-integrable random variable. In Lean's `0`-based indexing, the conclusion concerns the
canonical partial sums `partialSum X n = X₀ + ⋯ + Xₙ₋₁`. -/
theorem exists_memLp_two_ae_tendsto_partial_sums_of_iIndepFun_summable_variance
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (h_var_summable : Summable fun n ↦ Var[X n; P]) :
    ∃ Y : Ω → ℝ, MemLp Y 2 P ∧
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ partialSum X n ω) atTop (𝓝 (Y ω)) := by
  let Xm : ℕ → Ω → ℝ := fun n ↦ (hX_memLp n).aestronglyMeasurable.mk (X n)
  have hXm_ae : ∀ n, Xm n =ᵐ[P] X n := by
    intro n
    simpa [Xm] using ((hX_memLp n).aestronglyMeasurable.ae_eq_mk).symm
  have hXm_meas : ∀ n, Measurable (Xm n) := by
    intro n
    simpa [Xm] using (hX_memLp n).aestronglyMeasurable.measurable_mk
  have hXm_memLp : ∀ n, MemLp (Xm n) 2 P := by
    intro n
    exact (hX_memLp n).ae_eq (hXm_ae n).symm
  have hXm_centered : ∀ n, P[Xm n] = 0 := by
    intro n
    -- Proof comment: the measurable representative has the same integral as the original
    -- increment, hence remains centered.
    simpa [hX_centered n] using integral_congr_ae (hXm_ae n)
  have hXm_indep : iIndepFun Xm P := by
    -- Proof comment: independence is invariant under almost-everywhere replacement.
    exact hX_indep.congr fun n ↦ (hXm_ae n).symm
  have hXm_uncorrelated : Pairwise fun i j ↦ cov[Xm i, Xm j; P] = 0 := by
    intro i j hij
    exact (hXm_indep.indepFun hij).covariance_eq_zero (hXm_memLp i) (hXm_memLp j)
  have hXm_var : ∀ n, Var[Xm n; P] = Var[X n; P] := by
    intro n
    exact ProbabilityTheory.variance_congr (hXm_ae n)
  have hpartial_ae_eq : ∀ n, partialSum Xm n =ᵐ[P] partialSum X n :=
    partialSum_ae_eq_of_forall_ae_eq P hXm_ae
  have hpartial_memLp : ∀ n, MemLp (partialSum Xm n) 2 P :=
    partialSum_memLp_two_of_memLp_two P Xm hXm_memLp
  have hpartial_centered : ∀ n, P[partialSum Xm n] = 0 :=
    partialSum_integral_zero_of_integral_zero P Xm hXm_memLp hXm_centered
  have hpartial_var :
      ∀ n, Var[partialSum Xm n; P] = ∑ i ∈ Finset.range n, Var[X i; P] := by
    intro n
    rw [partialSum_variance_eq_sum_of_pairwise_uncorrelated P Xm hXm_memLp hXm_uncorrelated n]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact hXm_var i
  have hpartial_sq_le :
      ∀ n, ∫ ω, (partialSum Xm n ω) ^ 2 ∂P ≤ ∑' i, Var[X i; P] := by
    intro n
    -- Proof comment: because the partial sums are centered, their second moments are exactly
    -- their variances, and the finite variance sum is bounded by the full summable series.
    calc
      ∫ ω, (partialSum Xm n ω) ^ 2 ∂P = Var[partialSum Xm n; P] := by
        symm
        exact ProbabilityTheory.variance_of_integral_eq_zero
          (hpartial_memLp n).aemeasurable (hpartial_centered n)
      _ = ∑ i ∈ Finset.range n, Var[X i; P] := hpartial_var n
      _ ≤ ∑' i, Var[X i; P] := by
        exact h_var_summable.sum_le_tsum (Finset.range n) fun i _ ↦
          ProbabilityTheory.variance_nonneg (X i) P
  let C : NNReal := ⟨Real.sqrt (∑' i, Var[X i; P]), Real.sqrt_nonneg _⟩
  have hpartial_eLp_bdd :
      ∃ K : NNReal, ∀ n, eLpNorm (partialSum Xm n) (ENNReal.ofReal (2 : ℝ)) P ≤ K := by
    refine ⟨C, ?_⟩
    intro n
    -- Proof comment: package the second-moment estimate in the exact `L²` seminorm form required
    -- by the martingale convergence theorem.
    calc
      eLpNorm (partialSum Xm n) (ENNReal.ofReal (2 : ℝ)) P = eLpNorm (partialSum Xm n) 2 P := by
        simp
      _ ≤ ENNReal.ofReal (Real.sqrt (∑' i, Var[X i; P])) := by
        exact eLpNorm_two_le_of_integral_sq_le P (hpartial_memLp n) (hpartial_sq_le n)
      _ = C := by
        exact ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _)
  have hXm_int : ∀ n, Integrable (Xm n) P := by
    intro n
    exact (hXm_memLp n).integrable (by norm_num)
  have hmart :
      Martingale (partialSum Xm)
        (Filtration.natural (partialSum Xm)
          (fun n ↦ (partialSum_measurable Xm hXm_meas n).stronglyMeasurable)) P := by
    -- Proof comment: Example 10.6 identifies centered independent partial sums as a martingale
    -- for their natural filtration.
    simpa using independentCenteredPartialSums_martingale
      hXm_meas hXm_int hXm_centered hXm_indep
  obtain ⟨_, hY_memLp, hY_tendsto, _⟩ :=
    MeasureTheory.martingale_convergence_to_memLp_limitProcess_of_lp_bounded
      (X := partialSum Xm)
      (ℱ := Filtration.natural (partialSum Xm)
        (fun n ↦ (partialSum_measurable Xm hXm_meas n).stronglyMeasurable))
      (μ := P)
      hmart (by norm_num) hpartial_eLp_bdd
  refine ⟨Filtration.limitProcess
      (partialSum Xm)
      (Filtration.natural (partialSum Xm)
        (fun n ↦ (partialSum_measurable Xm hXm_meas n).stronglyMeasurable))
      P, ?_, ?_⟩
  · simpa using hY_memLp
  · have hpartial_ae_all : ∀ᵐ ω ∂P, ∀ n, partialSum Xm n ω = partialSum X n ω := by
      rw [ae_all_iff]
      exact hpartial_ae_eq
    filter_upwards [hY_tendsto, hpartial_ae_all] with ω hω hωeq
    have hseq_eq : (fun n ↦ partialSum Xm n ω) = fun n ↦ partialSum X n ω := by
      funext n
      exact hωeq n
    simpa [hseq_eq] using hω

/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Topology NNReal

section

/-- Helper for Lemma 5.31: the real correction term subtracted from `α` at step `n`. -/
private def perturbedDescentCorrection (α γ ε : ℕ → ℝ≥0) : ℕ → ℝ :=
  fun n ↦ (γ n : ℝ) * (α n : ℝ) + (ε n : ℝ)

/-- Helper for Lemma 5.31: the corrected real sequence obtained by subtracting the accumulated
perturbations from `α`. -/
private def correctedPerturbedDescent (α γ ε : ℕ → ℝ≥0) : ℕ → ℝ :=
  fun n ↦ (α n : ℝ) - (∑ k ∈ Finset.range n, perturbedDescentCorrection α γ ε k)

/-- Helper for Lemma 5.31: finite products of `1 + γ i` are controlled by the exponential of the
corresponding partial sum of `γ`. -/
private lemma prod_range_one_add_le_exp_sum {γ : ℕ → ℝ≥0} :
    ∀ n : ℕ, (∏ i ∈ Finset.range n, (1 + (γ i : ℝ))) ≤ Real.exp (∑ i ∈ Finset.range n, (γ i : ℝ))
  | 0 => by
      -- The empty product and empty sum give the normalized base case.
      simp
  | n + 1 => by
      -- Extend the finite product by one factor and compare the new factor with `exp (γ n)`.
      rw [Finset.prod_range_succ]
      have hexp_eq :
          Real.exp (∑ i ∈ Finset.range n, (γ i : ℝ)) * Real.exp (γ n : ℝ) =
            Real.exp (∑ i ∈ Finset.range (n + 1), (γ i : ℝ)) := by
        rw [← Real.exp_add]
        simp [Finset.sum_range_succ]
      calc
        (∏ i ∈ Finset.range n, (1 + (γ i : ℝ))) * (1 + (γ n : ℝ))
            ≤ Real.exp (∑ i ∈ Finset.range n, (γ i : ℝ)) * Real.exp (γ n : ℝ) := by
              exact mul_le_mul (prod_range_one_add_le_exp_sum n)
                (by simpa [add_comm] using (Real.add_one_le_exp (γ n : ℝ)))
                (by positivity) (Real.exp_nonneg _)
        _ = Real.exp (∑ i ∈ Finset.range (n + 1), (γ i : ℝ)) := by
              exact hexp_eq

/-- Helper for Lemma 5.31: the perturbed recursion yields a finite-horizon Gronwall bound for
the real coercion of `α`. -/
private lemma perturbed_descent_gronwall_bound
    {α β γ ε : ℕ → ℝ≥0}
    (hrec : ∀ n : ℕ, α (n + 1) + β n ≤ (1 + γ n) * α n + ε n) :
    ∀ n : ℕ, (α n : ℝ) ≤ (∏ i ∈ Finset.range n, (1 + (γ i : ℝ))) *
      ((α 0 : ℝ) + (∑ i ∈ Finset.range n, (ε i : ℝ)))
  | 0 => by
      -- At time `0`, the product is `1` and the perturbation sum is `0`.
      simp
  | n + 1 => by
      -- First drop the nonnegative `β n` term from the recursion.
      have hstep_nn : α (n + 1) ≤ (1 + γ n) * α n + ε n := by
        refine le_trans ?_ (hrec n)
        simp
      have hstep :
          (α (n + 1) : ℝ) ≤ (1 + (γ n : ℝ)) * (α n : ℝ) + (ε n : ℝ) := by
        exact_mod_cast hstep_nn
      have hprod_ge_one :
          1 ≤ (∏ i ∈ Finset.range (n + 1), (1 + (γ i : ℝ))) := by
        refine Finset.one_le_prod ?_
        intro i hi
        have hγi_nonneg : 0 ≤ (γ i : ℝ) := by positivity
        linarith
      have hmul :
          (1 + (γ n : ℝ)) * (α n : ℝ) ≤
            ((∏ i ∈ Finset.range n, (1 + (γ i : ℝ))) * (1 + (γ n : ℝ))) *
              ((α 0 : ℝ) + (∑ i ∈ Finset.range n, (ε i : ℝ))) := by
        have :=
          mul_le_mul_of_nonneg_left (perturbed_descent_gronwall_bound hrec n) (by positivity : 0 ≤ 1 + (γ n : ℝ))
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      have hε :
          (ε n : ℝ) ≤
            ((∏ i ∈ Finset.range n, (1 + (γ i : ℝ))) * (1 + (γ n : ℝ))) * (ε n : ℝ) := by
        have :=
          mul_le_mul_of_nonneg_right hprod_ge_one (by positivity : 0 ≤ (ε n : ℝ))
        simpa [Finset.prod_range_succ, mul_assoc, mul_left_comm, mul_comm] using this
      -- Absorb both pieces into the enlarged Gronwall factor and the enlarged perturbation sum.
      calc
        (α (n + 1) : ℝ) ≤ (1 + (γ n : ℝ)) * (α n : ℝ) + (ε n : ℝ) := hstep
        _ ≤
            ((∏ i ∈ Finset.range n, (1 + (γ i : ℝ))) * (1 + (γ n : ℝ))) *
                ((α 0 : ℝ) + (∑ i ∈ Finset.range n, (ε i : ℝ))) +
              (((∏ i ∈ Finset.range n, (1 + (γ i : ℝ))) * (1 + (γ n : ℝ))) * (ε n : ℝ)) := by
              exact add_le_add hmul hε
        _ =
            (∏ i ∈ Finset.range (n + 1), (1 + (γ i : ℝ))) *
              (((α 0 : ℝ) + (∑ i ∈ Finset.range n, (ε i : ℝ))) + (ε n : ℝ)) := by
              rw [Finset.prod_range_succ]
              ring
        _ =
            (∏ i ∈ Finset.range (n + 1), (1 + (γ i : ℝ))) *
              ((α 0 : ℝ) + (∑ i ∈ Finset.range (n + 1), (ε i : ℝ))) := by
              simp [Finset.sum_range_succ, add_assoc]

/-- Helper for Lemma 5.31: the summability of `γ` and `ε` gives a uniform real bound on the
coercion of `α`. -/
private lemma alpha_coe_bounded
    {α β γ ε : ℕ → ℝ≥0} (hγ : Summable γ) (hε : Summable ε)
    (hrec : ∀ n : ℕ, α (n + 1) + β n ≤ (1 + γ n) * α n + ε n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (α n : ℝ) ≤ C := by
  let C : ℝ := Real.exp (∑' n, (γ n : ℝ)) * ((α 0 : ℝ) + ∑' n, (ε n : ℝ))
  refine ⟨C, by positivity, ?_⟩
  have hγreal : Summable (fun n ↦ (γ n : ℝ)) := (NNReal.summable_coe).2 hγ
  have hεreal : Summable (fun n ↦ (ε n : ℝ)) := (NNReal.summable_coe).2 hε
  intro n
  -- Compare the finite Gronwall bound with the infinite exponential and infinite perturbation sum.
  have hprod_le :
      (∏ i ∈ Finset.range n, (1 + (γ i : ℝ))) ≤ Real.exp (∑' i, (γ i : ℝ)) := by
    calc
      (∏ i ∈ Finset.range n, (1 + (γ i : ℝ)))
          ≤ Real.exp (∑ i ∈ Finset.range n, (γ i : ℝ)) := prod_range_one_add_le_exp_sum n
      _ ≤ Real.exp (∑' i, (γ i : ℝ)) := by
            apply Real.exp_le_exp.mpr
            exact hγreal.sum_le_tsum _ (fun _ _ ↦ by positivity)
  have hsum_le :
      ((α 0 : ℝ) + (∑ i ∈ Finset.range n, (ε i : ℝ))) ≤ (α 0 : ℝ) + ∑' i, (ε i : ℝ) := by
    gcongr
    exact hεreal.sum_le_tsum _ (fun _ _ ↦ by positivity)
  calc
    (α n : ℝ) ≤ (∏ i ∈ Finset.range n, (1 + (γ i : ℝ))) * ((α 0 : ℝ) + (∑ i ∈ Finset.range n, (ε i : ℝ))) :=
      perturbed_descent_gronwall_bound hrec n
    _ ≤ Real.exp (∑' i, (γ i : ℝ)) * ((α 0 : ℝ) + ∑' i, (ε i : ℝ)) := by
          exact mul_le_mul hprod_le hsum_le (by positivity) (by positivity)
    _ = C := by
          rfl

/-- Helper for Lemma 5.31: the corrected sequence decreases by at least `β n` at each step. -/
private lemma corrected_descent_step
    {α β γ ε : ℕ → ℝ≥0}
    (hrec : ∀ n : ℕ, α (n + 1) + β n ≤ (1 + γ n) * α n + ε n) :
    ∀ n : ℕ,
      correctedPerturbedDescent α γ ε (n + 1) + (β n : ℝ) ≤ correctedPerturbedDescent α γ ε n := by
  intro n
  -- Expand the corrected sequence at consecutive indices and rewrite the recursion in `ℝ`.
  have hstep :
      (α (n + 1) : ℝ) + (β n : ℝ) ≤ (1 + (γ n : ℝ)) * (α n : ℝ) + (ε n : ℝ) := by
    exact_mod_cast hrec n
  dsimp [correctedPerturbedDescent, perturbedDescentCorrection]
  rw [Finset.sum_range_succ]
  nlinarith

/-- Helper for Lemma 5.31: summing the corrected descent inequality bounds the partial sums of
`β` by the drop of the corrected sequence. -/
private lemma corrected_descent_partial_sum_beta_le
    {α β γ ε : ℕ → ℝ≥0}
    (hrec : ∀ n : ℕ, α (n + 1) + β n ≤ (1 + γ n) * α n + ε n) :
    ∀ N : ℕ,
      ((∑ k ∈ Finset.range N, (β k : ℝ))) ≤
        correctedPerturbedDescent α γ ε 0 - correctedPerturbedDescent α γ ε N := by
  intro N
  induction N with
  | zero =>
      -- The empty partial sum matches the zero drop.
      simp [correctedPerturbedDescent]
  | succ N ih =>
      -- Add one more step and invoke the one-step corrected descent inequality.
      rw [Finset.sum_range_succ]
      have hstep := corrected_descent_step hrec N
      nlinarith

-- Proof sketch: introduce the corrected sequence
-- `δ n = α n - ∑ k < n, (γ k * α k + ε k)` ∈ `ℝ`, show from the one-step inequality that `δ`
-- is decreasing and bounded below, hence convergent; the summability of `γ` and `ε` then yields
-- convergence of `α`, and summing the descent inequality bounds the partial sums of `β`.
/-- Lemma 5.31: if nonnegative sequences `α` and `β` satisfy the perturbed descent recursion
`α (n + 1) + β n ≤ (1 + γ n) * α n + ε n` and the perturbation sequences `γ` and `ε` are
summable, then `α` converges in `ℝ≥0` and `β` is summable. -/
theorem tendsto_and_summable_of_summable_perturbed_descent
    {α β γ ε : ℕ → ℝ≥0} (hγ : Summable γ) (hε : Summable ε)
    (hrec : ∀ n : ℕ, α (n + 1) + β n ≤ (1 + γ n) * α n + ε n) :
    (∃ l : ℝ≥0, Tendsto α atTop (𝓝 l)) ∧ Summable β := by
  -- First get the textbook uniform bound needed to dominate the correction term `γ n * α n`.
  rcases alpha_coe_bounded hγ hε hrec with ⟨C, hC_nonneg, hα_le_C⟩
  have hγreal : Summable (fun n ↦ (γ n : ℝ)) := (NNReal.summable_coe).2 hγ
  have hεreal : Summable (fun n ↦ (ε n : ℝ)) := (NNReal.summable_coe).2 hε
  have hγα_summable : Summable (fun n ↦ (γ n : ℝ) * (α n : ℝ)) := by
    -- The product term is dominated by the fixed bound `C` times the summable sequence `γ`.
    refine Summable.of_nonneg_of_le
      (fun n ↦ by positivity)
      (fun n ↦ ?_)
      (hγreal.mul_left C)
    have :=
      mul_le_mul_of_nonneg_left (hα_le_C n) (by positivity : 0 ≤ (γ n : ℝ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hζ_summable : Summable (perturbedDescentCorrection α γ ε) := by
    -- The full correction term is the sum of the dominated `γ * α` part and `ε`.
    simpa [perturbedDescentCorrection] using hγα_summable.add hεreal
  have hδ_succ :
      ∀ n : ℕ, correctedPerturbedDescent α γ ε (n + 1) ≤ correctedPerturbedDescent α γ ε n := by
    intro n
    -- Dropping the nonnegative `β n` term from the corrected descent step gives monotonicity.
    have hstep := corrected_descent_step hrec n
    nlinarith
  have hδ_antitone : Antitone (correctedPerturbedDescent α γ ε) :=
    antitone_nat_of_succ_le hδ_succ
  have hδ_lower :
      ∀ n : ℕ,
        -(∑' k, perturbedDescentCorrection α γ ε k) ≤ correctedPerturbedDescent α γ ε n := by
    intro n
    -- The corrected sequence stays above the negative full correction sum because `α n ≥ 0`.
    have hpartial_le :
        ((∑ k ∈ Finset.range n, perturbedDescentCorrection α γ ε k)) ≤
          ∑' k, perturbedDescentCorrection α γ ε k := by
      exact hζ_summable.sum_le_tsum _ (fun _ _ ↦ by
        dsimp [perturbedDescentCorrection]
        positivity)
    dsimp [correctedPerturbedDescent]
    have hα_nonneg : 0 ≤ (α n : ℝ) := by positivity
    linarith
  have hδ_bddBelow : BddBelow (Set.range (correctedPerturbedDescent α γ ε)) := by
    -- The previous lower estimate gives a common lower bound for the entire corrected sequence.
    refine ⟨-(∑' k, perturbedDescentCorrection α γ ε k), ?_⟩
    rintro y ⟨n, rfl⟩
    exact hδ_lower n
  have hδ_tendsto :
      Tendsto (correctedPerturbedDescent α γ ε) atTop
        (𝓝 (⨅ n, correctedPerturbedDescent α γ ε n)) :=
    tendsto_atTop_ciInf hδ_antitone hδ_bddBelow
  have hsum_tendsto :
      Tendsto (fun n ↦ ∑ k ∈ Finset.range n, perturbedDescentCorrection α γ ε k) atTop
        (𝓝 (∑' k, perturbedDescentCorrection α γ ε k)) :=
    hζ_summable.hasSum.tendsto_sum_nat
  have hαreal_tendsto :
      Tendsto (fun n ↦ (α n : ℝ)) atTop
        (𝓝 ((⨅ n, correctedPerturbedDescent α γ ε n) +
          ∑' k, perturbedDescentCorrection α γ ε k)) := by
    -- Recover `α n` by adding back the convergent correction partial sums to `δ n`.
    convert hδ_tendsto.add hsum_tendsto using 1
    ext n
    simp [correctedPerturbedDescent]
  let lR : ℝ :=
    (⨅ n, correctedPerturbedDescent α γ ε n) + ∑' k, perturbedDescentCorrection α γ ε k
  have hlR_tendsto : Tendsto (fun n ↦ (α n : ℝ)) atTop (𝓝 lR) := by
    simpa [lR] using hαreal_tendsto
  rcases (NNReal.tendsto_coe' (m := α) (x := lR)).1 hlR_tendsto with ⟨hlR_nonneg, hα_tendsto⟩
  have hβ_partial :
      ∀ N : ℕ, (∑ k ∈ Finset.range N, (β k : ℝ)) ≤
        correctedPerturbedDescent α γ ε 0 - correctedPerturbedDescent α γ ε N :=
    corrected_descent_partial_sum_beta_le hrec
  have hβ_partial_bdd :
      ∀ N : ℕ, (∑ k ∈ Finset.range N, (β k : ℝ)) ≤
        correctedPerturbedDescent α γ ε 0 - ⨅ n, correctedPerturbedDescent α γ ε n := by
    intro N
    exact le_trans (hβ_partial N)
      (sub_le_sub_left (hδ_antitone.le_of_tendsto hδ_tendsto N) _)
  have hβreal_summable : Summable (fun n ↦ (β n : ℝ)) := by
    -- The corrected descent drop gives a uniform bound on all partial sums of `β`.
    refine summable_of_sum_range_le (fun n ↦ by positivity) hβ_partial_bdd
  have hβ_summable : Summable β := (NNReal.summable_coe).1 hβreal_summable
  exact ⟨⟨⟨lR, hlR_nonneg⟩, hα_tendsto⟩, hβ_summable⟩

end

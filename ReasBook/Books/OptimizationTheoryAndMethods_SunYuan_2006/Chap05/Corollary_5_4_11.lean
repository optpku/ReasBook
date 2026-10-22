/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_4_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_3
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open Filter

section Chapter05Corollary5411

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Operator" => Point →L[ℝ] Point

-- Domain sampling:
-- * primary domain: Jacobian-side quasi-Newton local convergence and superlinear rates.
-- * core/canonical owners inspected: `HasQuasiNewtonLocalConvergenceAssumptions` from
--   `Assumption_5_4_1`, `JacobianQuasiNewtonSmallStartConvergence` and
--   `JacobianQuasiNewtonIteration` from `Theorem_5_4_9`, and
--   `HasQSuperlinearConvergenceTo`.
-- * layer choice: this corollary is a source-facing bridge statement. The vanishing-subsequence
--   hypothesis is expressed through the reusable Chapter 5 owner `HasSubsequenceTendstoTo`
--   applied to the Jacobian-error norm sequence, while the ambient local-convergence
--   assumptions and small-start conclusion are expressed through the chapter owners above.

/-- Helper for Chapter05 Corollary 5.4.11: a linearly convergent sequence already converges to
its limit and has summable error norms. -/
lemma linearlyConvergesTo_tendsto_and_summableErrorNorm
    {x : ℕ → Point} {xStar : Point}
    (hlinear : LinearlyConvergesTo x xStar) :
    Tendsto x atTop (nhds xStar) ∧ Summable (fun k ↦ ‖x k - xStar‖) := by
  rcases hlinear with ⟨C, q, hC_nonneg, hq, hbound⟩
  have hq_nonneg : 0 ≤ q := le_of_lt hq.1
  have hgeomSummable : Summable (fun k : ℕ ↦ C * q ^ k) := by
    exact (summable_geometric_of_lt_one hq_nonneg hq.2).mul_left C
  have hgeomTendsto : Tendsto (fun k : ℕ ↦ C * q ^ k) atTop (nhds 0) := by
    -- The geometric majorant tends to zero because `0 ≤ q < 1`.
    have hpowTendsto : Tendsto (fun k : ℕ ↦ q ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq.2
    simpa using (tendsto_const_nhds.mul hpowTendsto)
  have herrTendsto : Tendsto (fun k ↦ ‖x k - xStar‖) atTop (nhds 0) := by
    -- Squeeze the error norms between `0` and the geometric majorant.
    exact
      squeeze_zero' (Eventually.of_forall fun k ↦ norm_nonneg _) (Eventually.of_forall hbound)
        hgeomTendsto
  constructor
  · -- Convergence in norm is exactly convergence to `xStar`.
    exact (tendsto_iff_norm_sub_tendsto_zero).2 herrTendsto
  · -- The same geometric majorant also makes the error norms summable.
    exact Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hbound hgeomSummable

/-- Helper for Chapter05 Corollary 5.4.11: a nonnegative sequence with additive one-step control
and summable forcing tends to `0` once some subsequence tends to `0`. -/
lemma tendsto_zero_of_subsequence_and_additiveControl
    {a v : ℕ → ℝ}
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (hv_nonneg : ∀ n, 0 ≤ v n)
    (hrec : ∀ n, a (n + 1) ≤ a n + v n)
    (hv_sum : Summable v)
    (hsub : HasSubsequenceTendstoTo a 0) :
    Tendsto a atTop (nhds 0) := by
  let b : ℕ → ℝ := fun n ↦ a n + ∑' k : ℕ, v (k + n)
  have htailTendsto : Tendsto (fun n ↦ ∑' k : ℕ, v (k + n)) atTop (nhds 0) := by
    -- Summable tails of a real series vanish.
    simpa using _root_.tendsto_sum_nat_add (f := v)
  have hb_nonneg : ∀ n, 0 ≤ b n := by
    intro n
    exact add_nonneg (ha_nonneg n) (tsum_nonneg fun k ↦ hv_nonneg (k + n))
  have hb_step : ∀ n, b (n + 1) ≤ b n := by
    intro n
    have hv_shift : Summable (fun k ↦ v (k + n)) := (summable_nat_add_iff n).2 hv_sum
    have hsplit :
        ∑' k : ℕ, v (k + n) = v n + ∑' k : ℕ, v (k + (n + 1)) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Summable.tsum_eq_zero_add hv_shift)
    -- Add the forcing tail to produce a decreasing corrected quantity.
    calc
      b (n + 1) = a (n + 1) + ∑' k : ℕ, v (k + (n + 1)) := rfl
      _ ≤ (a n + v n) + ∑' k : ℕ, v (k + (n + 1)) := by
            gcongr
            exact hrec n
      _ = a n + (v n + ∑' k : ℕ, v (k + (n + 1))) := by ring
      _ = b n := by
            dsimp [b]
            rw [hsplit]
  have hb_antitone : Antitone b := antitone_nat_of_succ_le hb_step
  rcases hsub with ⟨φ, hφ, hφ_tendsto⟩
  have hb_subseq_tendsto : Tendsto (b ∘ φ) atTop (nhds 0) := by
    have htail_subseq :
        Tendsto (fun n ↦ ∑' k : ℕ, v (k + φ n)) atTop (nhds 0) := by
      exact htailTendsto.comp hφ.tendsto_atTop
    -- Along the vanishing subsequence, the corrected quantity also tends to zero.
    change Tendsto (fun n ↦ a (φ n) + ∑' k : ℕ, v (k + φ n)) atTop (nhds 0)
    simpa using hφ_tendsto.add htail_subseq
  have hb_tendsto : Tendsto b atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases (Metric.tendsto_atTop.mp hb_subseq_tendsto) ε hε with ⟨N, hN⟩
    refine ⟨φ N, ?_⟩
    intro n hn
    have hle : φ N ≤ n := hn
    have hbound : b n ≤ b (φ N) := hb_antitone hle
    have hsmall : b (φ N) < ε := by
      simpa [Real.dist_eq, abs_of_nonneg (hb_nonneg (φ N))] using hN N le_rfl
    have hnonneg_n : 0 ≤ b n := hb_nonneg n
    have : |b n| < ε := by
      rw [abs_of_nonneg hnonneg_n]
      exact lt_of_le_of_lt hbound hsmall
    simpa [Real.dist_eq, abs_of_nonneg hnonneg_n] using this
  have habove : ∀ᶠ n in atTop, a n ≤ b n := by
    exact Eventually.of_forall fun n ↦ le_add_of_nonneg_right (tsum_nonneg fun k ↦ hv_nonneg _)
  -- The original sequence lies below the corrected decreasing sequence.
  exact squeeze_zero' (Eventually.of_forall ha_nonneg) habove hb_tendsto

/-- Helper for Chapter05 Corollary 5.4.11: a nonnegative sequence with `σ`-type one-step control
and summable coefficients tends to `0` once some subsequence tends to `0`. -/
lemma tendsto_zero_of_subsequence_and_sigmaControl
    {a u v : ℕ → ℝ}
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (hu_nonneg : ∀ n, 0 ≤ u n)
    (hv_nonneg : ∀ n, 0 ≤ v n)
    (hrec : ∀ n, a (n + 1) ≤ (1 + u n) * a n + v n)
    (hu_sum : Summable u)
    (hv_sum : Summable v)
    (hsub : HasSubsequenceTendstoTo a 0) :
    Tendsto a atTop (nhds 0) := by
  let p : ℕ → ℝ := fun n ↦ ∏ i ∈ Finset.range n, (1 + u i)
  let c : ℕ → ℝ := fun n ↦ a n / p n
  have hp_one_le : ∀ n, 1 ≤ p n := by
    intro n
    induction n with
    | zero =>
        simp [p]
    | succ n ih =>
        simp [p, Finset.prod_range_succ, ih]
        nlinarith [ih, hu_nonneg n]
  have hp_pos : ∀ n, 0 < p n := fun n ↦ lt_of_lt_of_le zero_lt_one (hp_one_le n)
  have hp_partial_exp : ∀ n, p n ≤ Real.exp (∑ i ∈ Finset.range n, u i) := by
    intro n
    induction n with
    | zero =>
        simp [p]
    | succ n ih =>
        simp [p, Finset.prod_range_succ, Finset.sum_range_succ, ih]
        have hu_exp : 1 + u n ≤ Real.exp (u n) := by
          simpa [add_comm] using Real.add_one_le_exp (u n)
        have hexp_nonneg : 0 ≤ Real.exp (∑ i ∈ Finset.range n, u i) := le_of_lt (Real.exp_pos _)
        have hone_nonneg : 0 ≤ 1 + u n := by
          linarith [hu_nonneg n]
        calc
          p n * (1 + u n) ≤ Real.exp (∑ i ∈ Finset.range n, u i) * Real.exp (u n) := by
            exact mul_le_mul ih hu_exp hone_nonneg hexp_nonneg
          _ = Real.exp (∑ i ∈ Finset.range n, u i + u n) := by
                rw [Real.exp_add]
  have hp_uniform : ∀ n, p n ≤ Real.exp (∑' i : ℕ, u i) := by
    intro n
    calc
      p n ≤ Real.exp (∑ i ∈ Finset.range n, u i) := hp_partial_exp n
      _ ≤ Real.exp (∑' i : ℕ, u i) := by
            refine Real.exp_le_exp.mpr ?_
            exact Summable.sum_le_tsum _ (fun i _ ↦ hu_nonneg i) hu_sum
  have hc_nonneg : ∀ n, 0 ≤ c n := by
    intro n
    exact div_nonneg (ha_nonneg n) (le_of_lt (hp_pos n))
  have hcrec : ∀ n, c (n + 1) ≤ c n + v n := by
    intro n
    have hpos_one_add : 0 < 1 + u n := by
      linarith [hu_nonneg n]
    have hden_pos : 0 < p n * (1 + u n) := mul_pos (hp_pos n) hpos_one_add
    have hdiv_rewrite :
        ((1 + u n) * a n + v n) / (p n * (1 + u n)) =
          c n + v n / (p n * (1 + u n)) := by
      dsimp [c]
      field_simp [(hp_pos n).ne', hpos_one_add.ne']
    -- Normalize by the partial product to reduce to the additive-control lemma.
    calc
      c (n + 1) = a (n + 1) / (p n * (1 + u n)) := by
            simp [c, p, Finset.prod_range_succ]
      _ ≤ ((1 + u n) * a n + v n) / (p n * (1 + u n)) := by
            exact div_le_div_of_nonneg_right (hrec n) (le_of_lt hden_pos)
      _ = c n + v n / (p n * (1 + u n)) := hdiv_rewrite
      _ ≤ c n + v n := by
            have hfrac : v n / (p n * (1 + u n)) ≤ v n := by
              have hden_one : 1 ≤ p n * (1 + u n) := by
                nlinarith [hp_one_le n, hu_nonneg n]
              exact div_le_self (hv_nonneg n) hden_one
            linarith
  have hc_sub : HasSubsequenceTendstoTo c 0 := by
    rcases hsub with ⟨φ, hφ, hφ_tendsto⟩
    refine ⟨φ, hφ, ?_⟩
    have hupper : ∀ᶠ n in atTop, c (φ n) ≤ a (φ n) := by
      exact Eventually.of_forall fun n ↦ div_le_self (ha_nonneg _) (hp_one_le _)
    exact squeeze_zero' (Eventually.of_forall fun n ↦ hc_nonneg (φ n)) hupper hφ_tendsto
  have hc_tendsto : Tendsto c atTop (nhds 0) := by
    exact
      tendsto_zero_of_subsequence_and_additiveControl hc_nonneg hv_nonneg hcrec hv_sum hc_sub
  have hmajor : Tendsto (fun n ↦ Real.exp (∑' i : ℕ, u i) * c n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hc_tendsto)
  have habove : ∀ᶠ n in atTop, a n ≤ Real.exp (∑' i : ℕ, u i) * c n := by
    refine Eventually.of_forall ?_
    intro n
    have hEq : a n = p n * c n := by
      dsimp [c]
      field_simp [(hp_pos n).ne']
    rw [hEq]
    exact mul_le_mul_of_nonneg_right (hp_uniform n) (hc_nonneg n)
  -- Undo the normalization using the uniform bound on the partial products.
  exact squeeze_zero' (Eventually.of_forall ha_nonneg) habove hmajor

/-- Helper for Chapter05 Corollary 5.4.11: the Jacobian-side secant-error ratio is bounded by the
operator-norm Jacobian approximation error. -/
lemma quasiNewtonSecantErrorRatio_le_jacobianErrorNorm
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    {x0 : Point} {B0 : Operator}
    (A : JacobianQuasiNewtonIteration D F domU U x0 B0) :
    ∀ k : ℕ,
      quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k ≤
        ‖A.B k - fderiv ℝ F hF.xStar‖ := by
  intro k
  by_cases hstep : A.x (k + 1) = A.x k
  · -- If the step vanishes, the secant quotient collapses to `0`.
    simp [quasiNewtonSecantErrorRatio_apply, hstep]
  · have hstepPos : 0 < ‖A.x (k + 1) - A.x k‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hstep)
    -- Otherwise the operator norm directly controls the secant defect.
    rw [quasiNewtonSecantErrorRatio_apply]
    exact (div_le_iff₀ hstepPos).2 <| by
      simpa [mul_comm] using (A.B k - fderiv ℝ F hF.xStar).le_opNorm (A.x (k + 1) - A.x k)

/-- Helper for Chapter05 Corollary 5.4.11: under the Theorem 5.4.9 update hypotheses, a
vanishing subsequence of Jacobian errors forces the full Jacobian-error norm sequence to tend to
`0`. -/
lemma jacobianErrorNorm_tendsto_zero_of_vanishingSubsequence
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)} {U : JacobianUpdateFunction Point}
    (h_update :
      (∃ γu : ℝ,
        SatisfiesAdditiveLocalUpdateBound U F hF.xStar (fderiv ℝ F hF.xStar) domU γu) ∨
      ∃ α1 α2,
        SatisfiesSigmaLocalUpdateBound U F hF.xStar (fderiv ℝ F hF.xStar) domU α1 α2)
    {x0 : Point} {B0 : Operator}
    (A : JacobianQuasiNewtonIteration D F domU U x0 B0)
    (hlinear : LinearlyConvergesTo A.x hF.xStar)
    (h_vanishing :
      HasSubsequenceTendstoTo (fun k ↦ ‖A.B k - fderiv ℝ F hF.xStar‖) 0) :
    Tendsto (fun k ↦ ‖A.B k - fderiv ℝ F hF.xStar‖) atTop (nhds 0) := by
  let e : ℕ → ℝ := fun k ↦ ‖A.x k - hF.xStar‖
  let σ : ℕ → ℝ := fun k ↦ quasiNewtonSigma F hF.xStar (A.x k) (A.B k)
  let a : ℕ → ℝ := fun k ↦ ‖A.B k - fderiv ℝ F hF.xStar‖
  rcases linearlyConvergesTo_tendsto_and_summableErrorNorm hlinear with ⟨_, he_sum⟩
  have hσ_nonneg : ∀ k, 0 ≤ σ k := by
    intro k
    dsimp [σ]
    rw [quasiNewtonSigma]
    exact le_trans (norm_nonneg _) (le_max_left _ _)
  have hσ_le : ∀ k, σ k ≤ e k + e (k + 1) := by
    intro k
    dsimp [σ, e]
    rw [A.step_eq k, quasiNewtonSigma]
    refine max_le_iff.mpr ?_
    constructor
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have he_shift_sum : Summable (fun k ↦ e (k + 1)) := (summable_nat_add_iff 1).2 he_sum
  have hσ_sum : Summable σ := by
    refine Summable.of_nonneg_of_le hσ_nonneg hσ_le ?_
    exact he_sum.add he_shift_sum
  rcases h_update with ⟨γu, hAdd⟩ | ⟨α1, α2, hSigma⟩
  · let γu0 : ℝ := max γu 0
    let v : ℕ → ℝ := fun k ↦ γu0 * σ k
    have ha_nonneg : ∀ k, 0 ≤ a k := by intro k; dsimp [a]; exact norm_nonneg _
    have hv_nonneg : ∀ k, 0 ≤ v k := by
      intro k
      dsimp [v, γu0]
      exact mul_nonneg (by simp) (hσ_nonneg k)
    have hv_sum : Summable v := by
      dsimp [v, γu0]
      exact hσ_sum.mul_left (max γu 0)
    have hrec : ∀ k, a (k + 1) ≤ a k + v k := by
      intro k
      have hraw :=
        hAdd.2 (A.x k) (A.B k) (A.B (k + 1)) (A.in_dom k) (A.matrices_invertible k) (A.update_mem k)
      have hsigma_sum :
          ‖quasiNewtonNextIterate F (A.x k) (A.B k) - hF.xStar‖ + ‖A.x k - hF.xStar‖ ≤ 2 * σ k := by
        have hcur : ‖A.x k - hF.xStar‖ ≤ σ k := by
          dsimp [σ]
          rw [quasiNewtonSigma]
          exact le_max_left _ _
        have hnext : ‖quasiNewtonNextIterate F (A.x k) (A.B k) - hF.xStar‖ ≤ σ k := by
          dsimp [σ]
          rw [quasiNewtonSigma]
          exact le_max_right _ _
        nlinarith [hcur, hnext, hσ_nonneg k]
      have hfactor :
          (γu / 2) *
              (‖quasiNewtonNextIterate F (A.x k) (A.B k) - hF.xStar‖ + ‖A.x k - hF.xStar‖) ≤
            γu0 * σ k := by
        have hs_nonneg :
            0 ≤
              ‖quasiNewtonNextIterate F (A.x k) (A.B k) - hF.xStar‖ + ‖A.x k - hF.xStar‖ := by
          positivity
        have hγhalf :
            γu / 2 ≤ γu0 / 2 := by
          dsimp [γu0]
          nlinarith [le_max_left γu 0]
        have hγu0_nonneg : 0 ≤ γu0 := by
          dsimp [γu0]
          simp
        calc
          (γu / 2) *
              (‖quasiNewtonNextIterate F (A.x k) (A.B k) - hF.xStar‖ + ‖A.x k - hF.xStar‖)
              ≤ (γu0 / 2) *
                  (‖quasiNewtonNextIterate F (A.x k) (A.B k) - hF.xStar‖ + ‖A.x k - hF.xStar‖) := by
                    exact mul_le_mul_of_nonneg_right hγhalf hs_nonneg
          _ ≤ (γu0 / 2) * (2 * σ k) := by
                exact mul_le_mul_of_nonneg_left hsigma_sum (by positivity)
          _ = γu0 * σ k := by ring
      -- Route correction: instead of restarting Theorem 5.4.9 with arbitrary rates, use the
      -- update recurrence plus summable `σ`-tails to show the Jacobian errors vanish.
      calc
        a (k + 1) ≤ a k +
            (γu / 2) *
              (‖quasiNewtonNextIterate F (A.x k) (A.B k) - hF.xStar‖ + ‖A.x k - hF.xStar‖) := by
              simpa [a] using hraw
        _ ≤ a k + v k := by
              simpa [v] using add_le_add_left hfactor (a k)
    simpa [a] using
      tendsto_zero_of_subsequence_and_additiveControl ha_nonneg hv_nonneg hrec hv_sum h_vanishing
  · let α10 : ℝ := max α1 0
    let α20 : ℝ := max α2 0
    let u : ℕ → ℝ := fun k ↦ α10 * σ k
    let v : ℕ → ℝ := fun k ↦ α20 * σ k
    have ha_nonneg : ∀ k, 0 ≤ a k := by intro k; dsimp [a]; exact norm_nonneg _
    have hu_nonneg : ∀ k, 0 ≤ u k := by
      intro k
      dsimp [u, α10]
      exact mul_nonneg (by simp) (hσ_nonneg k)
    have hv_nonneg : ∀ k, 0 ≤ v k := by
      intro k
      dsimp [v, α20]
      exact mul_nonneg (by simp) (hσ_nonneg k)
    have hu_sum : Summable u := by
      dsimp [u, α10]
      exact hσ_sum.mul_left (max α1 0)
    have hv_sum : Summable v := by
      dsimp [v, α20]
      exact hσ_sum.mul_left (max α2 0)
    have hrec : ∀ k, a (k + 1) ≤ (1 + u k) * a k + v k := by
      intro k
      have hraw :=
        hSigma.2 (A.x k) (A.B k) (A.B (k + 1)) (A.in_dom k) (A.matrices_invertible k)
          (A.update_mem k)
      have hsigma_nonneg : 0 ≤ σ k := hσ_nonneg k
      have ha_nonneg_k : 0 ≤ a k := ha_nonneg k
      have hcoeff :
          (1 + α1 * σ k) * a k + α2 * σ k ≤ (1 + α10 * σ k) * a k + α20 * σ k := by
        have hcoef_le : 1 + α1 * σ k ≤ 1 + α10 * σ k := by
          dsimp [α10]
          nlinarith [hsigma_nonneg, le_max_left α1 0]
        have hterm1 : (1 + α1 * σ k) * a k ≤ (1 + α10 * σ k) * a k := by
          exact mul_le_mul_of_nonneg_right hcoef_le ha_nonneg_k
        have hterm2 : α2 * σ k ≤ α20 * σ k := by
          dsimp [α20]
          nlinarith [hsigma_nonneg, le_max_left α2 0]
        exact add_le_add hterm1 hterm2
      -- Replace possibly negative coefficients by their nonnegative parts.
      calc
        a (k + 1) ≤ (1 + α1 * σ k) * a k + α2 * σ k := by
              simpa [a, σ] using hraw
        _ ≤ (1 + u k) * a k + v k := by
              dsimp [u, v]
              simpa [α10, α20] using hcoeff
    simpa [a] using
      tendsto_zero_of_subsequence_and_sigmaControl ha_nonneg hu_nonneg hv_nonneg hrec hu_sum
        hv_sum h_vanishing

namespace JacobianQuasiNewtonSmallStartConvergence

/-- Under the Jacobian-side small-start owner from Theorem 5.4.9, any run whose Jacobian
approximation errors admit a vanishing subsequence converges to `hF.xStar` `Q`-superlinearly. -/
theorem qSuperlinear_of_vanishingJacobianErrorSubsequence
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    {domU : Set (Point × Operator)}
    {U : JacobianUpdateFunction Point}
    (h_update :
      (∃ γu : ℝ,
        SatisfiesAdditiveLocalUpdateBound U F hF.xStar (fderiv ℝ F hF.xStar) domU γu) ∨
      ∃ α1 α2,
        SatisfiesSigmaLocalUpdateBound U F hF.xStar (fderiv ℝ F hF.xStar) domU α1 α2)
    {x0 : Point} {B0 : Operator}
    (hsmall :
      JacobianQuasiNewtonSmallStartConvergence D F domU U hF.xStar x0 B0)
    (A : JacobianQuasiNewtonIteration D F domU U x0 B0)
    (h_vanishing :
      HasSubsequenceTendstoTo (fun k ↦ ‖A.B k - fderiv ℝ F hF.xStar‖) 0) :
    HasQSuperlinearConvergenceTo A.x hF.xStar := by
  let DFstar : Operator := fderiv ℝ F hF.xStar
  have hlinear : LinearlyConvergesTo A.x hF.xStar := hsmall.linear A
  have hx_tendsto : Tendsto A.x atTop (nhds hF.xStar) :=
    (linearlyConvergesTo_tendsto_and_summableErrorNorm hlinear).1
  have hJacobian_tendsto :
      Tendsto (fun k ↦ ‖A.B k - DFstar‖) atTop (nhds 0) := by
    simpa [DFstar] using
      jacobianErrorNorm_tendsto_zero_of_vanishingSubsequence hF h_update A hlinear h_vanishing
  have hSecant_nonneg :
      ∀ᶠ k in atTop, 0 ≤ quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k := by
    exact Eventually.of_forall fun k ↦ by
      rw [quasiNewtonSecantErrorRatio_apply]
      exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hSecant_bound :
      ∀ᶠ k in atTop,
        quasiNewtonSecantErrorRatio F hF.xStar A.B A.x k ≤ ‖A.B k - DFstar‖ := by
    exact Eventually.of_forall (quasiNewtonSecantErrorRatio_le_jacobianErrorNorm hF A)
  have hSecant_tendsto :
      Tendsto (quasiNewtonSecantErrorRatio F hF.xStar A.B A.x) atTop (nhds 0) := by
    -- The secant ratio is squeezed by the Jacobian-error norm sequence.
    exact squeeze_zero' hSecant_nonneg hSecant_bound hJacobian_tendsto
  have hStep :
      ∀ k : ℕ, A.x (k + 1) = A.x k - (A.B k).inverse (F (A.x k)) := by
    intro k
    simpa [quasiNewtonNextIterate] using A.step_eq k
  -- Feed the secant-ratio limit into the canonical Chapter 5 superlinear criterion.
  exact
    (quasiNewton_superlinear_iff_secantErrorRatio_tendsto_zero F hF A.B A.x
      A.matrices_invertible hStep A.iterates_mem hx_tendsto).2 hSecant_tendsto

end JacobianQuasiNewtonSmallStartConvergence

/-- Chapter05 Corollary 5.4.11: under the assumptions and small-start regime of
Theorem 5.4.9, if some subsequence of the Jacobian approximation errors
`‖B k - fderiv ℝ F xStar‖` converges to `0`, then the quasi-Newton iterates converge to `xStar`
`Q`-superlinearly. -/
theorem jacobianQuasiNewton_qSuperlinearConvergence_of_vanishingJacobianErrorSubsequence
    {D : Set Point} {F : Point → Point}
    (hF : HasQuasiNewtonLocalConvergenceAssumptions D F)
    (domU : Set (Point × Operator))
    (U : JacobianUpdateFunction Point)
    (h_update :
      (∃ γu : ℝ,
        SatisfiesAdditiveLocalUpdateBound U F hF.xStar (fderiv ℝ F hF.xStar) domU γu) ∨
      ∃ α1 α2,
        SatisfiesSigmaLocalUpdateBound U F hF.xStar (fderiv ℝ F hF.xStar) domU α1 α2) :
    ∃ ε > 0, ∃ δ > 0, ∀ x0 B0,
      ‖x0 - hF.xStar‖ < ε →
      ‖B0 - fderiv ℝ F hF.xStar‖ < δ →
      JacobianQuasiNewtonSmallStartConvergence D F domU U hF.xStar x0 B0 ∧
        ∀ A : JacobianQuasiNewtonIteration D F domU U x0 B0,
          HasSubsequenceTendstoTo (fun k ↦ ‖A.B k - fderiv ℝ F hF.xStar‖) 0 →
            HasQSuperlinearConvergenceTo A.x hF.xStar := by
  rcases
      jacobianQuasiNewtonSmallStartConvergence_of_update_condition D F hF domU U h_update with
    ⟨ε, hε, δ, hδ, hsmall⟩
  refine ⟨ε, hε, δ, hδ, ?_⟩
  intro x0 B0 hx0 hB0
  refine ⟨hsmall x0 B0 hx0 hB0, ?_⟩
  intro A h_vanishing
  -- Reduce the corollary to the fixed small-start superlinear theorem above.
  exact
    JacobianQuasiNewtonSmallStartConvergence.qSuperlinear_of_vanishingJacobianErrorSubsequence
      hF h_update (hsmall x0 B0 hx0 hB0) A h_vanishing

end Chapter05Corollary5411

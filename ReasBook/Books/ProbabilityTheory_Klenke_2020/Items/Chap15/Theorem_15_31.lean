/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_30

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Topology

section

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- Helper for Theorem 15.31: the order-two Taylor polynomial of `charFun μ` at `0` is the
explicit quadratic polynomial in the first two moments. -/
lemma charFunTaylorTwoAtZero_eq (hμ : MemLp id 2 μ) (t : ℝ) :
    taylorWithinEval (charFun μ) 2 Set.univ 0 t =
      1
        + Complex.I * (t : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ)
        - (1 / 2 : ℂ) * (t : ℂ) ^ 2 * ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) := by
  -- Proof comment: expand mathlib's Taylor formula at `0` and collect the first three moments.
  calc
    taylorWithinEval (charFun μ) 2 Set.univ 0 t =
        ∑ k ∈ Finset.range (2 + 1), (k.factorial : ℂ)⁻¹ * (t * Complex.I) ^ k * (∫ x, x ^ k ∂μ) :=
          MeasureTheory.taylorWithinEval_charFun_zero (μ := μ) hμ t
    _ =
        1
          + Complex.I * (t : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ)
          - (1 / 2 : ℂ) * (t : ℂ) ^ 2 * ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ) := by
          simp [Finset.sum_range_succ]
          ring_nf
          norm_num [Complex.I_sq]

/-- Helper for Theorem 15.31: the scalar Taylor monomial in `h * x` matches the coefficient shape
used for the oscillatory moment expansion. -/
lemma oscillatoryTaylorTerm_eq (h x : ℝ) (k : ℕ) :
    ((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ) =
      (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) * (x : ℂ) ^ k := by
  -- Proof comment: commute the scalar factors once, then split the power across the product.
  calc
    ((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ) =
        (((h : ℂ) * (x : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ) := by
          simp [mul_assoc]
    _ = ((((Complex.I * (h : ℂ)) * (x : ℂ)) ^ k) / (k.factorial : ℂ)) := by
          congr 1
          ring
    _ = (((Complex.I * (h : ℂ)) ^ k) * (x : ℂ) ^ k) / (k.factorial : ℂ) := by
          rw [mul_pow]
    _ = (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) * (x : ℂ) ^ k := by
          field_simp

-- Proof sketch: pass from the probability law on `ℝ` to the corresponding complex moment-
-- generating function along the imaginary axis, differentiate under the integral sign using the
-- `n`th absolute-moment bound, and then transfer the resulting analyticity back to `charFun`.
/-- Overview for Theorem 15.31: let `X` be a real random variable with characteristic function `φ`.
The source-facing surface is organized as follows:

- item (i): `charFun_contDiff_of_memLp` and its derivative-formula companion
  `charFun_iteratedDeriv_of_memLp`;
- item (ii): `charFun_secondOrderExpansion_at_zero`;
- item (iii): `charFun_tendsto_partialSums_of_moment_growth` and its subordinate
  exponential-integrability corollary
  `charFun_tendsto_partialSums_of_integrable_exp_abs`.

The source proves ordered convergence of the `Finset.range n` partial sums in item (iii), not an
unconditional `HasSum`/`tsum` statement. For the owner theorem behind item (i), compare
`MeasureTheory.contDiff_charFun`. -/
theorem charFun_contDiff_of_memLp {n : ℕ} (hμ : MemLp id n μ) :
    ContDiff ℝ n (charFun μ) := by
  -- Proof comment: item (i) is exactly mathlib's owner theorem for characteristic functions.
  simpa using MeasureTheory.contDiff_charFun (μ := μ) hμ

-- Proof sketch: write the difference quotients as oscillatory integrals, dominate them by the
-- `k`th absolute moment using the remainder estimate from Lemma 15.30, and apply dominated
-- convergence for each `k ≤ n`.
/-- Derivative-formula companion for item (i): with a finite `n`th moment, the `n`th iterated
derivative of the characteristic function is the oscillatory moment integral. In mathlib this is
the canonical declaration `MeasureTheory.iteratedDeriv_charFun`. -/
theorem charFun_iteratedDeriv_of_memLp {n : ℕ} {t : ℝ} (hμ : MemLp id n μ) :
    iteratedDeriv n (charFun μ) t =
      Complex.I ^ n * ∫ x, x ^ n * Complex.exp (t * x * Complex.I) ∂μ := by
  -- Proof comment: item (i)'s derivative formula is the real-line specialization already in
  -- `MeasureTheory.iteratedDeriv_charFun`.
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (MeasureTheory.iteratedDeriv_charFun (μ := μ) (t := t) hμ)

/-- Helper for Theorem 15.31: the order-two Taylor quotient for `charFun μ` tends to `0` once the
Taylor polynomial is rewritten into the explicit quadratic moment expression. -/
lemma charFunSecondOrderRemainderTendsto (hμ : MemLp id 2 μ) :
    Filter.Tendsto
      (fun t : ℝ ↦
        ((t ^ 2)⁻¹ : ℝ) •
          (charFun μ t -
            (1
              + Complex.I * (t : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ)
              - (1 / 2 : ℂ) * (t : ℂ) ^ 2 * ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ))))
      (𝓝 0) (𝓝 0) := by
  -- Proof comment: apply Taylor's theorem in quotient form and rewrite the Taylor polynomial using
  -- the explicit second-order moment formula already established above.
  have hTaylor :
      Filter.Tendsto
        (fun t : ℝ ↦
          ((t ^ 2)⁻¹ : ℝ) •
            (charFun μ t - taylorWithinEval (charFun μ) 2 Set.univ 0 t))
        (𝓝 0) (𝓝 0) := by
    simpa only [nhdsWithin_univ, sub_zero] using
      (taylor_tendsto (f := charFun μ) (x₀ := 0) (n := 2) (s := Set.univ)
        convex_univ (Set.mem_univ 0) (MeasureTheory.contDiff_charFun (μ := μ) hμ).contDiffOn)
  refine hTaylor.congr' ?_
  filter_upwards with t
  rw [charFunTaylorTwoAtZero_eq (μ := μ) hμ t]

/-- Helper for Theorem 15.31: on the nonzero branch, multiplying the real Taylor quotient by
`(t : ℂ)^2` recovers the original complex remainder term. -/
lemma realInvSqSmul_mul_complexSq {t : ℝ} (ht : t ≠ 0) (z : ℂ) :
    (((t ^ 2)⁻¹ : ℝ) • z) * (t : ℂ) ^ 2 = z := by
  -- Proof comment: rewrite the real scalar action as complex multiplication, cast the inverse
  -- square into `ℂ`, and cancel the nonzero factor `(t : ℂ)^2`.
  have htz : (t : ℂ) ≠ 0 := by
    intro hzero
    apply ht
    exact_mod_cast hzero
  have hpow : (t : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 htz
  calc
    (((t ^ 2)⁻¹ : ℝ) • z) * (t : ℂ) ^ 2 =
        ((((t ^ 2)⁻¹ : ℝ) : ℂ) * z) * (t : ℂ) ^ 2 := by
          simp
    _ = ((((t ^ 2)⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ 2) * z := by
          ring
    _ = ((((t : ℂ) ^ 2)⁻¹ * (t : ℂ) ^ 2) : ℂ) * z := by
          rw [Complex.ofReal_inv, Complex.ofReal_pow]
    _ = (1 : ℂ) * z := by
          rw [inv_mul_cancel₀ hpow]
    _ = z := by
          simp

-- Proof sketch: specialize the derivative formula from item (i) to `k = 1, 2` at `t = 0`, then
-- apply the second-order Taylor expansion with remainder `o(t^2)` encoded by a function
-- `ε(t) → 0`.
/-- Theorem 15.31 (item (ii)): a finite second moment yields the quadratic expansion of the
characteristic function at `0` with a remainder `ε(t) t^2` and `ε(t) → 0`. -/
theorem charFun_secondOrderExpansion_at_zero (hμ : MemLp id 2 μ) :
    ∃ ε : ℝ → ℂ,
      Filter.Tendsto ε (𝓝 0) (𝓝 0) ∧
        ∀ t : ℝ,
          charFun μ t =
            1
              + Complex.I * (t : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ)
              - (1 / 2 : ℂ) * (t : ℂ) ^ 2 * ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ)
              + ε t * (t : ℂ) ^ 2 := by
  let Q : ℝ → ℂ := fun t ↦
    1
      + Complex.I * (t : ℂ) * ((∫ x, x ∂μ : ℝ) : ℂ)
      - (1 / 2 : ℂ) * (t : ℂ) ^ 2 * ((∫ x, x ^ 2 ∂μ : ℝ) : ℂ)
  let ε : ℝ → ℂ := fun t ↦ ((t ^ 2)⁻¹ : ℝ) • (charFun μ t - Q t)
  refine ⟨ε, ?_, ?_⟩
  · -- Proof comment: the direct Taylor quotient already gives the required remainder function.
    simpa [ε, Q] using charFunSecondOrderRemainderTendsto (μ := μ) hμ
  · intro t
    -- Route correction: the previous `isLittleO` packaging hid the same coercion issue. Keeping
    -- the quotient remainder explicit lets the nonzero branch close by one cancellation lemma.
    by_cases ht : t = 0
    · subst ht
      -- Proof comment: at `t = 0`, both the quadratic term and the remainder term vanish.
      have hCharZero : charFun μ 0 = (1 : ℂ) := by
        simp [MeasureTheory.charFun_zero]
      simp [ε, Q, hCharZero]
    · -- Proof comment: split off the explicit quadratic polynomial and rewrite the remaining
      -- difference using the nonzero cancellation bridge.
      have hsplit : charFun μ t = Q t + (charFun μ t - Q t) := by
        ring
      have hremainder : charFun μ t - Q t = ε t * (t : ℂ) ^ 2 := by
        simpa [ε] using
          (realInvSqSmul_mul_complexSq (t := t) (z := charFun μ t - Q t) ht).symm
      have hpointwise : charFun μ t = Q t + ε t * (t : ℂ) ^ 2 := by
        calc
          charFun μ t = Q t + (charFun μ t - Q t) := hsplit
          _ = Q t + ε t * (t : ℂ) ^ 2 := by rw [hremainder]
      simpa [Q] using hpointwise

/-- Helper for Theorem 15.31: the `n`th ordered oscillatory partial sum approximates
`charFun μ (t + h)` with an error controlled by the `n`th absolute moment. -/
lemma charFunPartialSums_normSub_le_growth (t h : ℝ) (n : ℕ)
    (h_moments : ∀ k : ℕ, Integrable (fun x : ℝ ↦ |x| ^ k) μ) :
    ‖charFun μ (t + h) -
        Finset.sum (Finset.range n) fun k ↦
          (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
            ∫ x, Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k ∂μ‖ ≤
      |h| ^ n * (∫ x, |x| ^ n ∂μ) / n.factorial := by
  have hExpIntegrable : Integrable (fun x : ℝ ↦ Complex.exp ((t + h) * x * Complex.I)) μ := by
    -- Proof comment: the oscillatory exponential has constant norm `1`, so it is integrable on
    -- a probability space.
    exact (integrable_const (1 : ℝ)).mono
      (by fun_prop)
      (Filter.Eventually.of_forall fun x => by
        simpa [mul_assoc] using (Complex.norm_exp_ofReal_mul_I ((t + h) * x)).le)
  have hMomentTermIntegrable (k : ℕ) :
      Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k) μ := by
    -- Proof comment: the oscillatory factor has norm `1`, so the moment term is dominated by
    -- `|x|^k`.
    refine Integrable.mono' (h_moments k) ?_ ?_
    · fun_prop
    · filter_upwards with x
      have hnormexp : ‖Complex.exp (t * x * Complex.I)‖ = 1 := by
        simpa [mul_assoc] using (Complex.norm_exp_ofReal_mul_I (t * x))
      calc
        ‖Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k‖ =
            ‖Complex.exp (t * x * Complex.I)‖ * ‖(x : ℂ) ^ k‖ := by
              rw [norm_mul]
        _ = 1 * |x| ^ k := by
              rw [hnormexp]
              simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |x| ^ k := by simp
  have hOscillatoryTermIntegrable (k : ℕ) :
      Integrable (fun x : ℝ ↦
        Complex.exp (t * x * Complex.I) *
          (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ))) μ := by
    -- Proof comment: rewrite the monomial into the coefficient shape used by the partial sum.
    refine
      (((hMomentTermIntegrable k).const_mul
        (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ))).congr ?_)
    filter_upwards with x
    calc
      (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
          (Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k) =
          Complex.exp (t * x * Complex.I) *
            ((((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) * (x : ℂ) ^ k) := by
              ring
      _ = Complex.exp (t * x * Complex.I) *
          (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)) := by
              rw [← oscillatoryTaylorTerm_eq (h := h) (x := x) (k := k)]
  have hPolyIntegrable :
      Integrable (fun x : ℝ ↦
        Complex.exp (t * x * Complex.I) *
          ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ))) μ := by
    -- Proof comment: each finite Taylor coefficient is integrable, hence so is the truncated sum.
    refine (integrable_finset_sum (Finset.range n) fun k hk ↦ hOscillatoryTermIntegrable k).congr ?_
    filter_upwards with x
    rw [Finset.mul_sum]
  have hExpSplitIntegrable :
      Integrable (fun x : ℝ ↦
        Complex.exp (t * x * Complex.I) * Complex.exp (h * x * Complex.I)) μ := by
    -- Proof comment: rewrite the `(t + h)` phase as a product of the `t` and `h` phases.
    refine hExpIntegrable.congr ?_
    filter_upwards with x
    have hphase : ((t : ℂ) + h) * x * Complex.I = t * x * Complex.I + h * x * Complex.I := by
      ring
    rw [hphase]
    exact Complex.exp_add (t * x * Complex.I) (h * x * Complex.I)
  have hMajorantIntegrable :
      Integrable (fun x : ℝ ↦ (|h| ^ n / n.factorial) * |x| ^ n) μ := by
    -- Proof comment: the moment assumption supplies the integrable majorant after scaling by the
    -- deterministic coefficient.
    exact (h_moments n).const_mul (|h| ^ n / n.factorial)
  have hPointwise :
      ∀ x : ℝ,
        ‖Complex.exp (t * x * Complex.I) *
            (Complex.exp (h * x * Complex.I) -
              ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)))‖ ≤
          (|h| ^ n / n.factorial) * |x| ^ n := by
    intro x
    have hnormexp : ‖Complex.exp (t * x * Complex.I)‖ = 1 := by
      simpa [mul_assoc] using (Complex.norm_exp_ofReal_mul_I (t * x))
    calc
      ‖Complex.exp (t * x * Complex.I) *
          (Complex.exp (h * x * Complex.I) -
            ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)))‖ =
          ‖Complex.exp (t * x * Complex.I)‖ *
            ‖Complex.exp (h * x * Complex.I) -
              ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ))‖ := by
              rw [norm_mul]
      _ = 1 *
            ‖Complex.exp (h * x * Complex.I) -
              ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ))‖ := by
            rw [hnormexp]
      _ ≤ 1 * ((|h| ^ n / n.factorial) * |x| ^ n) := by
            gcongr
            calc
              ‖Complex.exp (h * x * Complex.I) -
                  ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ))‖
                  ≤ |h * x| ^ n / n.factorial := by
                    simpa using norm_exp_mul_I_sub_taylor_sum_le (t := h * x) (n := n)
              _ = (|h| ^ n / n.factorial) * |x| ^ n := by
                    rw [abs_mul, mul_pow, div_eq_mul_inv]
                    ring
      _ = (|h| ^ n / n.factorial) * |x| ^ n := by
            simp
  have hRemainderIntegrable :
      Integrable (fun x : ℝ ↦
        Complex.exp (t * x * Complex.I) *
          (Complex.exp (h * x * Complex.I) -
            ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)))) μ := by
    -- Proof comment: the remainder is dominated by the integrable majorant from the textbook
    -- estimate.
    refine Integrable.mono' hMajorantIntegrable ?_ ?_
    · fun_prop
    · exact Filter.Eventually.of_forall hPointwise
  have hPartialIntegral :
      Finset.sum (Finset.range n) (fun k ↦
        (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
          ∫ x, Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k ∂μ) =
        ∫ x,
          Complex.exp (t * x * Complex.I) *
            ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)) ∂μ := by
    -- Proof comment: move the finite sum under the integral and normalize each monomial to the
    -- scalar Taylor remainder from Lemma 15.30.
    calc
      Finset.sum (Finset.range n) (fun k ↦
          (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
            ∫ x, Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k ∂μ) =
          Finset.sum (Finset.range n) fun k ↦
            ∫ x,
              (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
                (Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k) ∂μ := by
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            simpa [smul_eq_mul] using
              (integral_const_mul
                (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ))
                (f := fun x : ℝ ↦ Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k)).symm
      _ =
          Finset.sum (Finset.range n) fun k ↦
            ∫ x,
              Complex.exp (t * x * Complex.I) *
                (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)) ∂μ := by
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            congr 1
            ext x
            calc
              (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
                  (Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k) =
                  Complex.exp (t * x * Complex.I) *
                    ((((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) * (x : ℂ) ^ k) := by
                      ring
              _ = Complex.exp (t * x * Complex.I) *
                  (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)) := by
                    rw [← oscillatoryTaylorTerm_eq (h := h) (x := x) (k := k)]
      _ =
          ∫ x,
            ∑ k ∈ Finset.range n,
              Complex.exp (t * x * Complex.I) *
                (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)) ∂μ := by
            symm
            exact integral_finset_sum (Finset.range n) fun k hk ↦ hOscillatoryTermIntegrable k
      _ =
          ∫ x,
            Complex.exp (t * x * Complex.I) *
              ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)) ∂μ := by
            congr with x
            rw [Finset.mul_sum]
  have hCharIntegral :
      charFun μ (t + h) =
        ∫ x, Complex.exp (t * x * Complex.I) * Complex.exp (h * x * Complex.I) ∂μ := by
    -- Proof comment: split the phase `exp(i(t + h)x)` into the product `exp(itx) exp(ihx)`.
    rw [MeasureTheory.charFun_apply_real]
    congr with x
    have hphase :
        ((t + h : ℝ) : ℂ) * x * Complex.I = t * x * Complex.I + h * x * Complex.I := by
      push_cast
      ring
    rw [hphase]
    exact Complex.exp_add (t * x * Complex.I) (h * x * Complex.I)
  have hRemainderIntegral :
      charFun μ (t + h) -
          Finset.sum (Finset.range n) (fun k ↦
            (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
              ∫ x, Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k ∂μ) =
        ∫ x,
          Complex.exp (t * x * Complex.I) *
            (Complex.exp (h * x * Complex.I) -
              ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)))
          ∂μ := by
    -- Proof comment: subtract the truncated integral expansion from the split characteristic
    -- function and fold the difference back into one remainder integral.
    rw [hCharIntegral, hPartialIntegral, ← integral_sub hExpSplitIntegrable hPolyIntegrable]
    congr with x
    ring
  calc
    ‖charFun μ (t + h) -
        Finset.sum (Finset.range n) fun k ↦
          (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
            ∫ x, Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k ∂μ‖ =
        ‖∫ x,
            Complex.exp (t * x * Complex.I) *
              (Complex.exp (h * x * Complex.I) -
                ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)))
            ∂μ‖ := by
          rw [hRemainderIntegral]
    _ ≤
        ∫ x,
          ‖Complex.exp (t * x * Complex.I) *
            (Complex.exp (h * x * Complex.I) -
              ∑ k ∈ Finset.range n, (((((h * x : ℝ) : ℂ) * Complex.I) ^ k) / (k.factorial : ℂ)))‖ ∂μ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ x, (|h| ^ n / n.factorial) * |x| ^ n ∂μ := by
          exact integral_mono_ae hRemainderIntegrable.norm hMajorantIntegrable
            (Filter.Eventually.of_forall hPointwise)
    _ = |h| ^ n * (∫ x, |x| ^ n ∂μ) / n.factorial := by
          rw [integral_const_mul]
          ring

-- Proof sketch: compare `charFun μ (t + h)` with the `n`th partial sum via the remainder term
-- from Lemma 15.30, bound that remainder by `|h|^n E[|X|^n] / n!`, and let `n → ∞`.
/-- Item (iii): if the scaled absolute moments satisfy
`|h|^n E[|X|^n] / n! → 0`, then the ordered power-series partial sums in the increment `h`
converge to the characteristic function. -/
theorem charFun_tendsto_partialSums_of_moment_growth (t h : ℝ)
    (h_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ)
    (h_growth :
      Filter.Tendsto (fun n : ℕ ↦ |h| ^ n * (∫ x, |x| ^ n ∂μ) / n.factorial) Filter.atTop
        (𝓝 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦
        Finset.sum (Finset.range n) fun k ↦
          (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
            ∫ x, Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k ∂μ)
      Filter.atTop (𝓝 (charFun μ (t + h))) := by
  -- Proof comment: combine the integral remainder bound with the assumed decay of
  -- `|h|^n E[|X|^n] / n!`.
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) ?_ h_growth
  intro n
  simpa [norm_sub_rev] using
    charFunPartialSums_normSub_le_growth (μ := μ) t h n h_moments

/-- Helper for Theorem 15.31: exponential integrability of `exp |h x|` yields all absolute
moments and the decay `|h|^n E[|X|^n] / n! → 0`. -/
lemma integrableExpAbs_yieldsMomentsAndGrowth (h : ℝ) (hh : h ≠ 0)
    (h_exp : Integrable (fun x : ℝ ↦ Real.exp |h * x|) μ) :
    (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ) ∧
      Filter.Tendsto (fun n : ℕ ↦ |h| ^ n * (∫ x, |x| ^ n ∂μ) / n.factorial) Filter.atTop
        (𝓝 0) := by
  have hExpPos : Integrable (fun x : ℝ ↦ Real.exp (h * x)) μ := by
    -- Proof comment: `exp (h x)` is pointwise bounded by `exp |h x|`.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (le_abs_self (h * x))
  have hExpNeg : Integrable (fun x : ℝ ↦ Real.exp (-h * x)) μ := by
    -- Proof comment: the same majorant also controls the negative phase.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      simpa [abs_neg] using Real.exp_le_exp.mpr (le_abs_self (-h * x))
  have h_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ := by
    -- Proof comment: invoke mathlib's moment-existence theorem once both exponential sides are
    -- integrable.
    intro n
    simpa using
      (ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul
        (μ := μ) (X := id) hh hExpPos hExpNeg n)
  have hF_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ ∫ x, |h * x| ^ n / n.factorial ∂μ) Filter.atTop (𝓝 0) := by
    -- Proof comment: dominated convergence applies to `|h x|^n / n!`, dominated by `exp |h x|`.
    simpa using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        (μ := μ) (f := fun _ : ℝ ↦ (0 : ℝ)) (bound := fun x : ℝ ↦ Real.exp |h * x|)
        (F := fun n x ↦ |h * x| ^ n / n.factorial)
        (fun n ↦ by fun_prop) h_exp
        (fun n ↦ Filter.Eventually.of_forall fun x ↦ by
          rw [Real.norm_of_nonneg (by positivity)]
          simpa using Real.pow_div_factorial_le_exp (x := |h * x|) (by positivity) n)
        (Filter.Eventually.of_forall fun x ↦ by
          simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (|h * x| : ℝ))))
  refine ⟨h_moments, ?_⟩
  -- Proof comment: rewrite the dominated-convergence limit into the target moment-growth
  -- expression using `|h * x|^n = |h|^n |x|^n`.
  have hSeqEq :
      (fun n : ℕ ↦ ∫ x, (|h| * |x|) ^ n / n.factorial ∂μ) =
        fun n : ℕ ↦ |h| ^ n * (∫ x, |x| ^ n ∂μ) / n.factorial := by
    funext n
    calc
      ∫ x, (|h| * |x|) ^ n / n.factorial ∂μ = ∫ x, (|h| ^ n / n.factorial) * |x| ^ n ∂μ := by
        congr with x
        rw [mul_pow, div_eq_mul_inv]
        ring
      _ = |h| ^ n * (∫ x, |x| ^ n ∂μ) / n.factorial := by
        rw [integral_const_mul]
        ring
  simpa [hSeqEq] using hF_tendsto

-- Proof sketch: expand `exp (|h x|)` into its positive power series, use monotone convergence to
-- control the coefficients `|h|^n E[|X|^n] / n!`, verify the growth hypothesis from item (iii),
-- and then apply the preceding power-series theorem.
/-- Corollary to item (iii): if `E[e^{|hX|}] < ∞`, then the same ordered power-series partial
sums for `charFun μ (t + h)` converge. -/
theorem charFun_tendsto_partialSums_of_integrable_exp_abs (t h : ℝ)
    (h_exp : Integrable (fun x : ℝ ↦ Real.exp |h * x|) μ) :
    Filter.Tendsto
      (fun n : ℕ ↦
        Finset.sum (Finset.range n) fun k ↦
          (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
            ∫ x, Complex.exp (t * x * Complex.I) * (x : ℂ) ^ k ∂μ)
      Filter.atTop (𝓝 (charFun μ (t + h))) := by
  by_cases hh : h = 0
  · -- Proof comment: when `h = 0`, all higher-order coefficients vanish, so the partial sums are
    -- eventually constant and equal to `charFun μ t`.
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn
    rw [hh]
    rw [Finset.sum_eq_single 0]
    · simp [MeasureTheory.charFun_apply_real]
    · intro k hk hk0
      simp [hk0]
    · intro h0
      exact (h0 (Finset.mem_range.mpr hn_pos)).elim
  · -- Proof comment: in the nonzero branch, exponential integrability provides both the moments
    -- and the growth hypothesis needed for item (iii).
    obtain ⟨h_moments, h_growth⟩ :=
      integrableExpAbs_yieldsMomentsAndGrowth (μ := μ) h hh h_exp
    exact charFun_tendsto_partialSums_of_moment_growth (μ := μ) t h h_moments h_growth

end

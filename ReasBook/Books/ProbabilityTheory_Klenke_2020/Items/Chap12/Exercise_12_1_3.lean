/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

/-- The explicit equality-case family on `Fin n`: the `i`-th random variable is the indicator of
the event that the sampled state equals `i`. -/
def exchangeableCovarianceEqualityExample (n : ℕ) : Fin n → Fin n → ℝ :=
  fun i ω ↦ if ω = i then 1 else 0

private theorem two_le_ne_zero {n : ℕ} (h_n : 2 ≤ n) : n ≠ 0 := by
  omega

/-- The uniform probability law on the nonempty finite space `Fin n` used for the equality
example. -/
def exchangeableCovarianceEqualityExampleLaw (n : ℕ) (h_nz : n ≠ 0) :
    ProbabilityMeasure (Fin n) :=
  let _ : NeZero n := ⟨h_nz⟩
  ⟨(PMF.uniformOfFintype (Fin n)).toMeasure, inferInstance⟩

/-- Helper for Exercise 12.1.3: two injective `Fin m`-tuples in `Fin n` can be matched by a
permutation of `Fin n`. -/
private theorem existsPermApplyEqOfEmbedding {m n : ℕ} (u v : Fin m ↪ Fin n) :
    ∃ ρ : Equiv.Perm (Fin n), ∀ k, ρ (v k) = u k := by
  classical
  let e : Set.range v ≃ Set.range u :=
    { toFun := fun x ↦ ⟨u (v.invOfMemRange x), Set.mem_range_self _⟩
      invFun := fun x ↦ ⟨v (u.invOfMemRange x), Set.mem_range_self _⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        simp }
  -- Proof comment: extend the bijection between the two finite ranges to a permutation of the
  -- whole sample space.
  refine ⟨e.extendSubtype, ?_⟩
  intro k
  rw [Equiv.extendSubtype_apply_of_mem e (v k) (Set.mem_range_self k)]
  simp [e]

/-- Helper for Exercise 12.1.3: the uniform law on `Fin n` is invariant under permutations of the
sample space. -/
private theorem exchangeableCovarianceEqualityExampleLaw_map_perm
    (n : ℕ) (h_nz : n ≠ 0) (ρ : Equiv.Perm (Fin n)) :
    Measure.map ρ (exchangeableCovarianceEqualityExampleLaw n h_nz : Measure (Fin n)) =
      exchangeableCovarianceEqualityExampleLaw n h_nz := by
  let _ : NeZero n := ⟨h_nz⟩
  have hρ_pmf : (PMF.uniformOfFintype (Fin n)).map ρ = PMF.uniformOfFintype (Fin n) := by
    ext a
    rw [PMF.map_apply]
    refine (tsum_eq_single (ρ.symm a) ?_).trans ?_
    · intro b hb
      have hab : a ≠ ρ b := by
        intro h
        apply hb
        simpa using (congrArg ρ.symm h).symm
      simp [hab]
    · simp [PMF.uniformOfFintype_apply]
  -- Proof comment: convert the permutation invariance of the uniform PMF into the corresponding
  -- statement for the induced measure.
  calc
    Measure.map ρ ((PMF.uniformOfFintype (Fin n)).toMeasure) =
        ((PMF.uniformOfFintype (Fin n)).map ρ).toMeasure := by
          simpa using
            (PMF.toMeasure_map (p := PMF.uniformOfFintype (Fin n))
              (f := ρ) (hf := (Measurable.of_discrete : Measurable ρ)))
    _ = ((PMF.uniformOfFintype (Fin n)).toMeasure) := by
          simpa using congrArg PMF.toMeasure hρ_pmf

/-- Helper for Exercise 12.1.3: reindexing the one-hot family by a coordinate permutation agrees
with precomposing the sample point by the ambient permutation matching the tuple. -/
private theorem exchangeableIndicatorTuple_perm {m n : ℕ}
    (u : Fin m ↪ Fin n) (σ : Equiv.Perm (Fin m)) (ρ : Equiv.Perm (Fin n))
    (hρ : ∀ i, ρ (u (σ i)) = u i) :
    (fun ω i ↦ exchangeableCovarianceEqualityExample n (u i) (ρ ω)) =
      fun ω i ↦ exchangeableCovarianceEqualityExample n (u (σ i)) ω := by
  -- Proof comment: both tuples are indicators of the same singleton after transporting the sample
  -- point by `ρ`.
  funext ω i
  by_cases hω : ω = u (σ i)
  · simp [exchangeableCovarianceEqualityExample, hω, hρ i]
  · have hρω : ρ ω ≠ u i := by
      intro hEq
      apply hω
      apply ρ.injective
      rw [hEq, hρ i]
    simp [exchangeableCovarianceEqualityExample, hω, hρω]

-- Proof sketch: under the uniform law on `Fin n`, permuting the coordinate labels simply permutes
-- the atoms of the sample space, so the finite-dimensional laws of the indicator family are
-- unchanged.
/-- The indicator family on the uniform finite space is exchangeable. -/
theorem exchangeableCovarianceEqualityExample_isExchangeable (n : ℕ) (h_nz : n ≠ 0) :
    IsExchangeable (exchangeableCovarianceEqualityExample n)
      (exchangeableCovarianceEqualityExampleLaw n h_nz) := by
  intro m u σ
  -- Route correction: prove exchangeability from the defining permutation-invariance clause, so
  -- the indicator example only needs a sample-space permutation and not the stronger tuple
  -- criterion from `Remark_12_2`.
  obtain ⟨ρ, hρ⟩ := existsPermApplyEqOfEmbedding u (σ.toEmbedding.trans u)
  let μ : Measure (Fin n) := exchangeableCovarianceEqualityExampleLaw n h_nz
  have hρ_law : HasLaw ρ μ μ := by
    refine ⟨(Measurable.of_discrete : Measurable ρ).aemeasurable, ?_⟩
    simpa [μ] using exchangeableCovarianceEqualityExampleLaw_map_perm n h_nz ρ
  have hid_law : HasLaw (fun ω : Fin n ↦ ω) μ μ := by
    refine ⟨measurable_id.aemeasurable, ?_⟩
    simp
  have htuple_meas :
      Measurable
        (fun z : Fin n ↦ fun i : Fin m ↦ exchangeableCovarianceEqualityExample n (u i) z) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact Measurable.of_discrete
  have htuple :
      IdentDistrib
        (fun ω i ↦ exchangeableCovarianceEqualityExample n (u i) (ρ ω))
        (fun ω i ↦ exchangeableCovarianceEqualityExample n (u i) ω)
        μ μ := by
    -- Proof comment: first identify `ρ` with the identity in law under the uniform measure, then
    -- observe the tuple as a measurable function of the sample point.
    simpa [Function.comp] using (hρ_law.identDistrib hid_law).comp htuple_meas
  simpa [μ, exchangeableIndicatorTuple_perm u σ ρ hρ] using htuple

-- Proof sketch: the sample space `Fin n` is finite and the indicator variables take only the
-- values `0` and `1`, hence every coordinate belongs to `L²`.
/-- Every coordinate of the explicit equality example is square integrable. -/
theorem exchangeableCovarianceEqualityExample_memLp (n : ℕ) (h_nz : n ≠ 0) :
    ∀ i, MemLp (exchangeableCovarianceEqualityExample n i) 2
      (exchangeableCovarianceEqualityExampleLaw n h_nz) := by
  let _ : NeZero n := ⟨h_nz⟩
  intro i
  have hbound :
      ∀ᵐ ω ∂(exchangeableCovarianceEqualityExampleLaw n h_nz : Measure (Fin n)),
        exchangeableCovarianceEqualityExample n i ω ∈ Set.Icc (0 : ℝ) 1 := by
    -- Proof comment: each indicator coordinate is pointwise either `0` or `1`.
    filter_upwards with ω
    by_cases hω : ω = i
    · simp [exchangeableCovarianceEqualityExample, hω]
    · simp [exchangeableCovarianceEqualityExample, hω]
  exact memLp_of_bounded hbound
    ((Measurable.of_discrete :
      Measurable (exchangeableCovarianceEqualityExample n i)).aestronglyMeasurable)
    2

/-- Helper for Exercise 12.1.3: every indicator coordinate has expectation `1 / n` under the
uniform law on `Fin n`. -/
private theorem exchangeableCovarianceEqualityExample_integral (n : ℕ) (h_nz : n ≠ 0) (i : Fin n) :
    (exchangeableCovarianceEqualityExampleLaw n h_nz :
      Measure (Fin n))[exchangeableCovarianceEqualityExample n i] = (n : ℝ)⁻¹ := by
  let _ : NeZero n := ⟨h_nz⟩
  -- Proof comment: on the finite space `Fin n`, the integral is a finite weighted sum and only
  -- the atom `ω = i` contributes.
  change ∫ ω, exchangeableCovarianceEqualityExample n i ω
      ∂((PMF.uniformOfFintype (Fin n)).toMeasure) = (n : ℝ)⁻¹
  rw [PMF.integral_eq_sum]
  simp [exchangeableCovarianceEqualityExample, PMF.uniformOfFintype_apply, ENNReal.toReal_inv]

/-- Helper for Exercise 12.1.3: two distinct coordinates of the finite indicator family have
covariance `-1 / n^2`. -/
private theorem exchangeableCovarianceEqualityExample_covariance
    (n : ℕ) (h_nz : n ≠ 0) {i j : Fin n} (hij : i ≠ j) :
    cov[exchangeableCovarianceEqualityExample n i, exchangeableCovarianceEqualityExample n j;
      exchangeableCovarianceEqualityExampleLaw n h_nz] =
      -((1 : ℝ) / n ^ 2) := by
  have hMemI := exchangeableCovarianceEqualityExample_memLp n h_nz i
  have hMemJ := exchangeableCovarianceEqualityExample_memLp n h_nz j
  have hIntI := exchangeableCovarianceEqualityExample_integral n h_nz i
  have hIntJ := exchangeableCovarianceEqualityExample_integral n h_nz j
  have hMulZero :
      exchangeableCovarianceEqualityExample n i *
          exchangeableCovarianceEqualityExample n j = 0 := by
    -- Proof comment: distinct one-hot coordinates can never be simultaneously equal to `1`.
    funext ω
    by_cases hωi : ω = i
    · have hij' : ¬ i = j := hij
      simp [exchangeableCovarianceEqualityExample, hωi, hij']
    · simp [exchangeableCovarianceEqualityExample, hωi]
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast h_nz
  rw [covariance_eq_sub hMemI hMemJ, hMulZero, hIntI, hIntJ]
  simp
  field_simp [hnReal]

/-- Helper for Exercise 12.1.3: each indicator coordinate has variance `(n - 1) / n^2`. -/
private theorem exchangeableCovarianceEqualityExample_variance
    (n : ℕ) (h_n : 2 ≤ n) (i : Fin n) :
    Var[exchangeableCovarianceEqualityExample n i;
      exchangeableCovarianceEqualityExampleLaw n (two_le_ne_zero h_n)] =
      (n - 1 : ℝ) / n ^ 2 := by
  have h_memLp := exchangeableCovarianceEqualityExample_memLp n (two_le_ne_zero h_n) i
  have h_integral :=
    exchangeableCovarianceEqualityExample_integral n (two_le_ne_zero h_n) i
  have hsq :
      exchangeableCovarianceEqualityExample n i ^ 2 =
        exchangeableCovarianceEqualityExample n i := by
    -- Proof comment: indicators are idempotent because they only take the values `0` and `1`.
    funext ω
    by_cases hω : ω = i
    · simp [exchangeableCovarianceEqualityExample, hω]
    · simp [exchangeableCovarianceEqualityExample, hω]
  have hn_real : (n : ℝ) ≠ 0 := by
    exact_mod_cast two_le_ne_zero h_n
  -- Proof comment: rewrite the variance as `E[X^2] - E[X]^2` and substitute the indicator
  -- moments.
  rw [variance_eq_sub h_memLp, hsq, h_integral]
  field_simp [hn_real]

-- Proof sketch: under the uniform law each indicator has success probability `1 / n`, so its
-- variance is `((n - 1) / n^2)`, which is positive for `n ≥ 2`.
/-- Every coordinate of the explicit equality example has nonzero variance. -/
theorem exchangeableCovarianceEqualityExample_variance_ne_zero (n : ℕ) (h_n : 2 ≤ n) :
    ∀ i, Var[exchangeableCovarianceEqualityExample n i;
      exchangeableCovarianceEqualityExampleLaw n (two_le_ne_zero h_n)] ≠ 0 := by
  intro i
  rw [exchangeableCovarianceEqualityExample_variance n h_n i]
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) h_n
  have hn_sub_pos : 0 < (n - 1 : ℝ) := by
    have hn_one_lt : (1 : ℝ) < n := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) h_n
    linarith
  -- Proof comment: the closed-form variance is strictly positive once `n ≥ 2`.
  have hvar_pos : 0 < (n - 1 : ℝ) / n ^ 2 := by
    refine div_pos hn_sub_pos ?_
    positivity
  linarith

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Exercise 12.1.3: an exchangeable family has the same mixed-product law on any two
distinct coordinates. -/
private theorem exchangeableProduct_identDistrib_of_ne
    (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ)
    (h_exchangeable : IsExchangeable X μ) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    IdentDistrib (fun ω ↦ X a ω * X b ω) (fun ω ↦ X c ω * X d ω) μ μ := by
  let u : Fin 2 ↪ Fin n := Function.Embedding.embFinTwo hab
  let v : Fin 2 ↪ Fin n := Function.Embedding.embFinTwo hcd
  have htuple :
      IdentDistrib (fun ω i ↦ X (u i) ω) (fun ω i ↦ X (v i) ω) μ μ :=
    (isExchangeable_iff_identDistrib_of_pairwise_distinct X μ).mp h_exchangeable 2 u v
  have hmul : Measurable (fun z : Fin 2 → ℝ ↦ z 0 * z 1) := by
    exact (measurable_pi_apply 0).mul (measurable_pi_apply 1)
  -- Proof comment: project the common two-point tuple law through the multiplication observable.
  simpa [u, v, Function.comp, Function.Embedding.embFinTwo_apply_zero,
    Function.Embedding.embFinTwo_apply_one] using htuple.comp hmul

/-- Helper for Exercise 12.1.3: exchangeability identifies all off-diagonal covariances of a
finite family. -/
private theorem exchangeableCovariance_eq_of_ne
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    (h_exchangeable : IsExchangeable X μ) (h_memLp : ∀ k, MemLp (X k) 2 μ)
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    cov[X a, X b; μ] = cov[X c, X d; μ] := by
  have hprod_int :
      μ[X a * X b] = μ[X c * X d] := by
    -- Proof comment: the mixed moment is the expectation of the two-point product observable, so
    -- the product-law helper rewrites it directly.
    simpa [Pi.mul_apply] using
      (exchangeableProduct_identDistrib_of_ne (μ := μ) X h_exchangeable hab hcd).integral_eq
  have ha_int : μ[X a] = μ[X c] := by
    simpa using (h_exchangeable.identDistrib a c).integral_eq
  have hb_int : μ[X b] = μ[X d] := by
    simpa using (h_exchangeable.identDistrib b d).integral_eq
  -- Proof comment: after `covariance_eq_sub`, all three moments match by exchangeability.
  rw [covariance_eq_sub (h_memLp a) (h_memLp b), covariance_eq_sub (h_memLp c) (h_memLp d),
    hprod_int, ha_int, hb_int]

/-- Helper for Exercise 12.1.3: the variance of the full sum of an exchangeable family collapses
to one diagonal variance term and one off-diagonal covariance term. -/
private theorem exchangeableCovarianceSumFormula
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    {i j : Fin n} (hij : i ≠ j) (h_exchangeable : IsExchangeable X μ)
    (h_memLp : ∀ k, MemLp (X k) 2 μ) :
    Var[∑ k, X k; μ] =
      (n : ℝ) * Var[X i; μ] + ((n * (n - 1) : ℕ) : ℝ) * cov[X i, X j; μ] := by
  have h_two_le : 2 ≤ n := by
    omega
  have h_one_le : 1 ≤ n := by
    omega
  rw [variance_sum_eq_sum_variance_add_sum_covariance_off_diagonal h_memLp]
  have hdiag :
      ∑ k, Var[X k; μ] = (n : ℝ) * Var[X i; μ] := by
    -- Proof comment: every marginal has the same variance because every coordinate has the same
    -- one-dimensional law.
    calc
      ∑ k, Var[X k; μ] = ∑ k : Fin n, Var[X i; μ] := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          simpa using (h_exchangeable.identDistrib k i).variance_eq
      _ = (n : ℝ) * Var[X i; μ] := by
          simp
  have hoffdiag :
      ∑ k, ∑ l ∈ Finset.univ.erase k, cov[X k, X l; μ] =
        ((n * (n - 1) : ℕ) : ℝ) * cov[X i, X j; μ] := by
    -- Proof comment: each ordered off-diagonal pair contributes the same covariance, and there
    -- are exactly `n * (n - 1)` such pairs.
    calc
      ∑ k, ∑ l ∈ Finset.univ.erase k, cov[X k, X l; μ] =
          ∑ k, ∑ l ∈ Finset.univ.erase k, cov[X i, X j; μ] := by
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            refine Finset.sum_congr rfl fun l hl ↦ ?_
            have hkl : k ≠ l := by
              exact fun hEq ↦ (Finset.mem_erase.mp hl).1 hEq.symm
            exact exchangeableCovariance_eq_of_ne (μ := μ) (X := X) h_exchangeable h_memLp hkl hij
      _ = ∑ k : Fin n, ((n - 1 : ℕ) : ℝ) * cov[X i, X j; μ] := by
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            simp
      _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * cov[X i, X j; μ] := by
            simp [mul_assoc]
      _ = ((n * (n - 1) : ℕ) : ℝ) * cov[X i, X j; μ] := by
            rw [Nat.cast_mul]
  -- Proof comment: substitute the diagonal and off-diagonal collapses into Bienayme's formula.
  rw [hdiag, hoffdiag]

-- Proof sketch: apply nonnegativity of `Var[∑ i : Fin n, X i; μ]`, expand it by
-- `ProbabilityTheory.variance_sum`, and use exchangeability to identify every diagonal term with
-- `Var[X₁; μ]` and every off-diagonal term with `cov[X₁, X₂; μ]`.
/-- Exercise 12.1.3 (1): for an exchangeable square-integrable family `X₁, …, Xₙ`, the covariance
between two distinct coordinates is bounded below by `-(n - 1)⁻¹ Var[X₁]`. -/
theorem cov_ge_neg_inv_mul_var_of_exchangeable
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X : Fin n → Ω → ℝ)
    {i j : Fin n} (hij : i ≠ j) (h_exchangeable : IsExchangeable X μ)
    (h_memLp : ∀ k, MemLp (X k) 2 μ) :
    cov[X i, X j; μ] ≥ -((1 : ℝ) / (n - 1 : ℝ)) * Var[X i; μ] := by
  have h_two_le : 2 ≤ n := by
    omega
  have hvar_nonneg : 0 ≤ Var[∑ k, X k; μ] := variance_nonneg _ _
  rw [exchangeableCovarianceSumFormula (μ := μ) (X := X) hij h_exchangeable h_memLp] at hvar_nonneg
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) h_two_le
  have hn_sub_pos : 0 < (n - 1 : ℝ) := by
    have hn_one_lt : (1 : ℝ) < n := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) h_two_le
    linarith
  have h_one_le : 1 ≤ n := by
    omega
  have hlinear_scaled :
      0 ≤ (n : ℝ) * (Var[X i; μ] + (n - 1 : ℝ) * cov[X i, X j; μ]) := by
    calc
      0 ≤ (n : ℝ) * Var[X i; μ] + (((n * (n - 1) : ℕ) : ℝ)) * cov[X i, X j; μ] := hvar_nonneg
      _ = (n : ℝ) * (Var[X i; μ] + (n - 1 : ℝ) * cov[X i, X j; μ]) := by
            rw [Nat.cast_mul, Nat.cast_sub h_one_le]
            ring
  have hlinear : 0 ≤ Var[X i; μ] + (n - 1 : ℝ) * cov[X i, X j; μ] := by
    -- Proof comment: divide the variance-of-sum inequality by the positive factor `n`.
    nlinarith [hlinear_scaled, hn_pos]
  have hdiv : -Var[X i; μ] / (n - 1 : ℝ) ≤ cov[X i, X j; μ] := by
    -- Proof comment: rearrange the linear inequality and divide by the positive factor `n - 1`.
    refine (div_le_iff₀ hn_sub_pos).2 ?_
    linarith
  -- Proof comment: rewrite the lower bound into the textbook form.
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

-- Proof sketch: for the explicit indicator family on the uniform finite space, one has
-- `E[X₁ X₂] = 0`, `E[X₁] = 1 / n`, and `Var[X₁] = (n - 1) / n^2`, so the covariance equals
-- `-1 / n^2 = -(n - 1)⁻¹ Var[X₁]`.
/-- Exercise 12.1.3 (2): for `n ≥ 2`, the indicator family on the uniform sample space `Fin n`
provides a nontrivial exchangeable square-integrable example attaining equality in (12.6). -/
theorem exchangeable_indicator_example_attains_covariance_bound (n : ℕ) (h_n : 2 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    cov[exchangeableCovarianceEqualityExample n i,
        exchangeableCovarianceEqualityExample n j;
        exchangeableCovarianceEqualityExampleLaw n (two_le_ne_zero h_n)] =
      -((1 : ℝ) / (n - 1 : ℝ)) * Var[exchangeableCovarianceEqualityExample n i;
        exchangeableCovarianceEqualityExampleLaw n (two_le_ne_zero h_n)] := by
  rw [exchangeableCovarianceEqualityExample_covariance n (two_le_ne_zero h_n) hij,
    exchangeableCovarianceEqualityExample_variance n h_n i]
  have hn_sub_ne : (n - 1 : ℝ) ≠ 0 := by
    have hn_one_lt : (1 : ℝ) < n := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) h_n
    linarith
  have hn_real : (n : ℝ) ≠ 0 := by
    exact_mod_cast two_le_ne_zero h_n
  -- Proof comment: substitute the closed-form covariance and variance and simplify.
  field_simp [hn_real, hn_sub_ne]

end

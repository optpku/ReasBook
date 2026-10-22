/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The defining power series of the probability generating function of a discrete law on `ℕ`,
evaluated at a point of the unit interval. -/
noncomputable abbrev probabilityGeneratingSeries (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) : ℝ :=
  ∑' n : ℕ, (p n).toReal * (z : ℝ) ^ n

-- Proof sketch: each term in the defining series is nonnegative because both `(p n).toReal` and
-- `(z : ℝ)^n` are nonnegative on the unit interval, so `tsum_nonneg` applies.
/-- The probability generating series takes nonnegative values on the unit interval. -/
theorem probabilityGeneratingSeries_nonneg (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    0 ≤ probabilityGeneratingSeries p z := by
  -- Each summand is nonnegative, so the whole series is nonnegative termwise.
  refine tsum_nonneg ?_
  intro n
  exact mul_nonneg (ENNReal.toReal_nonneg) (pow_nonneg z.2.1 n)

-- Proof sketch: compare the defining series termwise with `∑' n, (p n).toReal` using `z ≤ 1`,
-- and then use that the masses of a `PMF` sum to `1`.
/-- The probability generating series is bounded above by `1` on the unit interval. -/
theorem probabilityGeneratingSeries_le_one (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingSeries p z ≤ 1 := by
  have hp_summable : Summable (fun n : ℕ ↦ (p n).toReal) := by
    simpa using ENNReal.summable_toReal p.tsum_coe_ne_top
  have hseries_summable : Summable (fun n : ℕ ↦ (p n).toReal * (z : ℝ) ^ n) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ ↦ (p n).toReal) ?_ ?_ hp_summable
    · intro n
      exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg z.2.1 n)
    · intro n
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ z.2.1 z.2.2)
  have hp_tsum : ∑' n : ℕ, (p n).toReal = 1 := by
    rw [← ENNReal.toReal_one, ← p.tsum_coe, ENNReal.tsum_toReal_eq]
    intro n
    exact p.apply_ne_top n
  -- The summand `(z : ℝ)^n` is bounded above by `1`, so the whole series is bounded by the
  -- total mass of the law.
  calc
    probabilityGeneratingSeries p z = ∑' n : ℕ, (p n).toReal * (z : ℝ) ^ n := rfl
    _ ≤ ∑' n : ℕ, (p n).toReal :=
      hseries_summable.tsum_le_tsum
        (fun n ↦ mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ z.2.1 z.2.2))
        hp_summable
    _ = 1 := hp_tsum

/-- The probability generating function of an `ℕ`-valued law, viewed as a map from `[0,1]` to
`[0,1]`. -/
noncomputable def probabilityGeneratingFunction (p : PMF ℕ) :
    Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
  fun z ↦
    ⟨probabilityGeneratingSeries p z,
      probabilityGeneratingSeries_nonneg p z,
      probabilityGeneratingSeries_le_one p z⟩

-- Proof sketch: unfold `probabilityGeneratingFunction` and `probabilityGeneratingSeries`; the
-- value is definitionally the stated series.
/-- The probability generating function evaluates to the defining power series of the law. -/
theorem probabilityGeneratingFunction_apply (p : PMF ℕ) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction p z : ℝ) =
      ∑' n : ℕ, (p n).toReal * (z : ℝ) ^ n := by
  -- Unfolding the subtype-valued definition gives the defining series immediately.
  rfl

-- Proof sketch: the pushforward of a probability measure along a measurable map is again a
-- probability measure.
/-- The pushforward law of a measurable `ℕ`-valued random variable under a probability measure is
again a probability measure. -/
theorem isProbabilityMeasure_map_of_measurable (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℕ) (hX : Measurable X) :
    IsProbabilityMeasure (P.map X) := by
  -- Pushforwards of probability measures remain probability measures.
  simpa using Measure.isProbabilityMeasure_map hX.aemeasurable

/-- The `PMF` associated to an `ℕ`-valued measurable random variable under a probability measure. -/
noncomputable def natRandomVariableLaw (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℕ) (hX : Measurable X) : PMF ℕ :=
  let _ : IsProbabilityMeasure (P.map X) := isProbabilityMeasure_map_of_measurable P X hX
  (P.map X).toPMF

-- Proof sketch: unfold `natRandomVariableLaw`; the associated measure is definitionally the
-- pushforward measure `P.map X`.
/-- The measure associated to `natRandomVariableLaw` is the pushforward law of the random
variable. -/
theorem natRandomVariableLaw_toMeasure (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℕ) (hX : Measurable X) :
    (natRandomVariableLaw P X hX).toMeasure = P.map X := by
  -- Unfold the `PMF` built from the pushforward law and simplify `toPMF.toMeasure`.
  unfold natRandomVariableLaw
  simp [Measure.toPMF_toMeasure]

/-- The `ℕ`-valued random sum obtained by adding the first `T ω` entries of the sequence
`X`. -/
noncomputable def natRandomSum (T : Ω → ℕ) (X : ℕ → Ω → ℕ) : Ω → ℕ :=
  fun ω ↦ Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω)

-- Proof sketch: unfold `natRandomSum`; the value is definitionally the finite sum over
-- `Finset.range (T ω)`.
/-- The random sum evaluates to the finite sum of the first `T ω` entries of `X`. -/
theorem natRandomSum_apply (T : Ω → ℕ) (X : ℕ → Ω → ℕ) (ω : Ω) :
    natRandomSum T X ω = Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω) := by
  -- This is just the defining equation of `natRandomSum`.
  rfl

/-- Helper for Theorem 3.8: finite sums of measurable `ℕ`-valued random variables are measurable.
-/
theorem measurable_sum_natFamily {n : ℕ} (X : Fin n → Ω → ℕ)
    (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω ↦ ∑ i : Fin n, X i ω) := by
  -- Finite sums preserve measurability.
  fun_prop

-- Proof sketch: for each `n`, the restriction of `natRandomSum T X` to the event `{ω | T ω = n}`
-- agrees with the measurable finite sum `ω ↦ ∑ i in Finset.range n, X i ω`; then glue these
-- countably many measurable pieces together using the measurability of `T`.
/-- A random sum with a measurable counting variable and measurable summands is measurable. -/
theorem measurable_natRandomSum (T : Ω → ℕ) (hT_meas : Measurable T) (X : ℕ → Ω → ℕ)
    (hX_meas : ∀ n, Measurable (X n)) :
    Measurable (natRandomSum T X) := by
  -- Since the codomain is countable, it suffices to show that every singleton fiber is
  -- measurable, and each fiber splits according to the value of `T`.
  refine measurable_to_countable' ?_
  intro k
  have h_preimage :
      (natRandomSum T X) ⁻¹' {k} =
        ⋃ n : ℕ, ({ω | T ω = n} ∩ {ω | ∑ i : Fin n, X i ω = k}) := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨T ω, ?_⟩
      constructor
      · simp
      · have hsum : ∑ i : Fin (T ω), X i ω = natRandomSum T X ω := by
          simpa [natRandomSum_apply] using
            (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) (T ω))
        exact hsum.trans hω
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hnT, hnk⟩
      have hnT' : T ω = n := by
        simpa using hnT
      have hnk' : ∑ i : Fin n, X i ω = k := by
        simpa using hnk
      have hsum_range :
          (∑ i : Fin n, X i ω) = Finset.sum (Finset.range n) (fun i ↦ X i ω) := by
        simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) n)
      have hnat : natRandomSum T X ω = Finset.sum (Finset.range n) (fun i ↦ X i ω) := by
        calc
          natRandomSum T X ω = Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω) := by
            rw [natRandomSum_apply]
          _ = Finset.sum (Finset.range n) (fun i ↦ X i ω) := by
            simpa [hnT']
      have hsum : ∑ i : Fin n, X i ω = natRandomSum T X ω := by
        exact hsum_range.trans hnat.symm
      exact hsum.symm.trans hnk'
  rw [h_preimage]
  refine MeasurableSet.iUnion ?_
  intro n
  have hsum_meas : Measurable (fun ω ↦ ∑ i : Fin n, X i ω) :=
    measurable_sum_natFamily (fun i : Fin n ↦ X i) (fun i ↦ hX_meas i)
  refine (hT_meas (measurableSet_singleton n)).inter ?_
  exact hsum_meas (measurableSet_singleton k)

/-- Helper for Theorem 3.8: the probability generating function of the law of a measurable
`ℕ`-valued random variable is the expectation of the power map `ω ↦ z ^ X ω`. -/
theorem probabilityGeneratingFunction_natRandomVariableLaw_eq_integral (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℕ) (hX : Measurable X) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction (natRandomVariableLaw P X hX) z : ℝ) =
      ∫ ω, (z : ℝ) ^ X ω ∂P := by
  let _ : IsProbabilityMeasure (P.map X) := isProbabilityMeasure_map_of_measurable P X hX
  have h_pow_meas : Measurable (fun n : ℕ ↦ (z : ℝ) ^ n) := by
    fun_prop
  have h_pow_integrable_map : Integrable (fun n : ℕ ↦ (z : ℝ) ^ n) (P.map X) := by
    -- The integrand is uniformly bounded by `1` on `[0, 1]`.
    refine Integrable.of_bound h_pow_meas.aestronglyMeasurable 1 ?_
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg z.2.1 n)]
    simpa using (pow_le_one₀ z.2.1 z.2.2 : (z : ℝ) ^ n ≤ 1)
  have h_pow_integrable_law :
      Integrable (fun n : ℕ ↦ (z : ℝ) ^ n) (natRandomVariableLaw P X hX).toMeasure := by
    simpa [natRandomVariableLaw_toMeasure P X hX] using h_pow_integrable_map
  -- Rewrite the pgf as an integral against the law of `X`, then push that integral back to `P`.
  calc
    (probabilityGeneratingFunction (natRandomVariableLaw P X hX) z : ℝ)
        = ∑' n : ℕ, ((natRandomVariableLaw P X hX) n).toReal * (z : ℝ) ^ n := by
            rw [probabilityGeneratingFunction_apply]
    _ = ∫ n, (z : ℝ) ^ n ∂(natRandomVariableLaw P X hX).toMeasure := by
          symm
          rw [PMF.integral_eq_tsum _ _ h_pow_integrable_law]
          simp [smul_eq_mul]
    _ = ∫ n, (z : ℝ) ^ n ∂(P.map X) := by
          rw [natRandomVariableLaw_toMeasure P X hX]
    _ = ∫ ω, (z : ℝ) ^ X ω ∂P := by
          rw [integral_map hX.aemeasurable h_pow_meas.aestronglyMeasurable]

/-- Helper for Theorem 3.8: the pgf of a finite partial sum of iid `ℕ`-valued random variables
is the corresponding power of the common pgf. -/
theorem integral_pow_partial_sum_eq_pow_common_pgf (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hX_meas : ∀ n, Measurable (X n)) (hX_indep : iIndepFun X P)
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P) (n : ℕ) (z : Set.Icc (0 : ℝ) 1) :
    ∫ ω, (z : ℝ) ^ ∑ i : Fin n, X i ω ∂P =
      ((probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z : ℝ)) ^ n := by
  let Xn : Fin n → Ω → ℕ := fun i ω ↦ X i ω
  have hXn_meas : ∀ i : Fin n, Measurable (Xn i) := by
    intro i
    exact hX_meas i
  have hXn_indep : iIndepFun Xn P := by
    simpa [Xn] using hX_indep.precomp (g := ((↑) : Fin n → ℕ)) Fin.val_injective
  have h_pow_indep : iIndepFun (fun i : Fin n ↦ fun ω ↦ (z : ℝ) ^ Xn i ω) P := by
    -- Independence is preserved under the coordinatewise power transform.
    simpa [Xn, Function.comp] using
      hXn_indep.comp (fun _ : Fin n ↦ fun m : ℕ ↦ (z : ℝ) ^ m) (fun _ ↦ by fun_prop)
  have h_pow_aestrong : ∀ i : Fin n, AEStronglyMeasurable (fun ω ↦ (z : ℝ) ^ Xn i ω) P := by
    intro i
    exact ((hXn_meas i).const_pow (z : ℝ)).aestronglyMeasurable
  have h_pow_sum_eq_prod :
      (fun ω ↦ (z : ℝ) ^ ∑ i : Fin n, Xn i ω) =
        fun ω ↦ ∏ i : Fin n, (z : ℝ) ^ Xn i ω := by
    -- The exponent of a finite sum turns into a finite product of powers.
    funext ω
    simpa [Xn] using
      (Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Fin n ↦ Xn i ω) (z : ℝ)).symm
  rw [h_pow_sum_eq_prod]
  calc
    ∫ ω, ∏ i : Fin n, (z : ℝ) ^ Xn i ω ∂P
        = ∏ i : Fin n, ∫ ω, (z : ℝ) ^ Xn i ω ∂P := by
            simpa using h_pow_indep.integral_fun_prod_eq_prod_integral h_pow_aestrong
    _ = ∏ i : Fin n, ∫ ω, (z : ℝ) ^ X 0 ω ∂P := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          simpa [Xn] using
            ((hX_ident i).comp (by fun_prop)).integral_eq
    _ = (∫ ω, (z : ℝ) ^ X 0 ω ∂P) ^ n := by
          simp
    _ = ((probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z : ℝ)) ^ n := by
          rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral P (X 0) (hX_meas 0) z]

/-- Helper for Theorem 3.8: on the fiber `{ω | T ω = n}`, the power of the random sum agrees with
the power of the fixed `n`-th partial sum. -/
theorem pow_natRandomSum_eq_partial_sum_on_counting_fiber
    (T : Ω → ℕ) (X : ℕ → Ω → ℕ) (z : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Set.EqOn (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω)
      (fun ω ↦ (z : ℝ) ^ ∑ i : Fin n, X i ω) {ω | T ω = n} := by
  intro ω hω
  -- On the fiber `T = n`, the random sum is definitionally the `n`-th finite partial sum.
  calc
    (z : ℝ) ^ natRandomSum T X ω =
        (z : ℝ) ^ Finset.sum (Finset.range (T ω)) (fun i ↦ X i ω) := by
      rw [natRandomSum_apply]
    _ = (z : ℝ) ^ Finset.sum (Finset.range n) (fun i ↦ X i ω) := by
      simpa using congrArg
        (fun m : ℕ ↦ (z : ℝ) ^ Finset.sum (Finset.range m) (fun i ↦ X i ω)) hω
    _ = (z : ℝ) ^ (∑ i : Fin n, X i ω) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) n]

/-- Helper for Theorem 3.8: the contribution of the fiber `{ω | T ω = n}` factors into the
probability of the fiber and the `n`-th power of the common pgf. -/
theorem setIntegral_pow_natRandomSum_fiber_eq_countingLaw_mul_common_pgf_pow
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ) (hT_meas : Measurable T)
    (X : ℕ → Ω → ℕ) (hX_meas : ∀ n, Measurable (X n))
    (hTX_indep : IndepFun T (fun ω ↦ fun n ↦ X n ω) P) (hX_indep : iIndepFun X P)
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P) (n : ℕ) (z : Set.Icc (0 : ℝ) 1) :
    ∫ ω in {ω | T ω = n}, (z : ℝ) ^ natRandomSum T X ω ∂P =
      ((natRandomVariableLaw P T hT_meas) n).toReal *
        ((probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z : ℝ)) ^ n := by
  let A : Set Ω := {ω | T ω = n}
  have hA_meas : MeasurableSet A := hT_meas (measurableSet_singleton n)
  have hseq_meas : Measurable (fun ω ↦ fun k ↦ X k ω) := by
    -- The whole sequence is measurable coordinatewise.
    exact measurable_pi_lambda _ hX_meas
  have hindicator_meas :
      Measurable (Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ))) := by
    -- The singleton indicator on `ℕ` is measurable.
    classical
    simpa using measurable_const.indicator (measurableSet_singleton n)
  have hpartial_sum_meas : Measurable (fun x : ℕ → ℕ ↦ ∑ i : Fin n, x i) := by
    -- The partial-sum functional depends on finitely many measurable coordinates.
    fun_prop
  have hpartial_pow_meas :
      Measurable (fun x : ℕ → ℕ ↦ (z : ℝ) ^ ∑ i : Fin n, x i) := by
    -- Composing the partial sum with the power map keeps measurability.
    exact hpartial_sum_meas.const_pow (z : ℝ)
  have hindicator_eq :
      Set.indicator A (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω) =
        fun ω ↦ Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) *
          ((z : ℝ) ^ ∑ i : Fin n, X i ω) := by
    funext ω
    by_cases hω : T ω = n
    · have hpow :
          (z : ℝ) ^ natRandomSum T X ω = (z : ℝ) ^ ∑ i : Fin n, X i ω :=
        (pow_natRandomSum_eq_partial_sum_on_counting_fiber T X z n) hω
      -- On the fiber the indicator is `1`, so only the partial-sum term remains.
      simp [A, hω, hpow]
    · -- Off the fiber both indicator terms vanish.
      simp [A, hω]
  have hT_factor :
      ∫ ω, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) ∂P =
        ((natRandomVariableLaw P T hT_meas) n).toReal := by
    -- Push the singleton indicator integral to the law of `T`.
    calc
      ∫ ω, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) ∂P
          = ∫ k, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) k ∂(P.map T) := by
              rw [← integral_map hT_meas.aemeasurable hindicator_meas.aestronglyMeasurable]
      _ = ∫ k in ({n} : Set ℕ), (1 : ℝ) ∂(P.map T) := by
            rw [integral_indicator (measurableSet_singleton n)]
      _ = ((natRandomVariableLaw P T hT_meas) n).toReal := by
            rw [setIntegral_one_eq_measureReal, Measure.real,
              ← PMF.toMeasure_apply_singleton (natRandomVariableLaw P T hT_meas) n
                (measurableSet_singleton n), natRandomVariableLaw_toMeasure P T hT_meas]
  have hX_factor :
      ∫ x, (z : ℝ) ^ ∑ i : Fin n, x i ∂(P.map (fun ω ↦ fun k ↦ X k ω)) =
        ((probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z : ℝ)) ^ n := by
    -- Push the partial-sum functional back to `P` and use the iid partial-sum formula.
    rw [integral_map hseq_meas.aemeasurable hpartial_pow_meas.aestronglyMeasurable]
    simpa using integral_pow_partial_sum_eq_pow_common_pgf P X hX_meas hX_indep hX_ident n z
  -- Rewrite the fiber integral as an indicator product, factor it by independence, and evaluate
  -- each factor separately.
  calc
    ∫ ω in {ω | T ω = n}, (z : ℝ) ^ natRandomSum T X ω ∂P
        = ∫ ω, Set.indicator A (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω) ω ∂P := by
            symm
            rw [integral_indicator hA_meas]
    _ = ∫ ω, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) *
          ((z : ℝ) ^ ∑ i : Fin n, X i ω) ∂P := by
            rw [hindicator_eq]
    _ = (∫ ω, Set.indicator ({n} : Set ℕ) (fun _ ↦ (1 : ℝ)) (T ω) ∂P) *
          ∫ ω, (z : ℝ) ^ ∑ i : Fin n, X i ω ∂P := by
            simpa using
              hTX_indep.integral_fun_comp_mul_comp hT_meas.aemeasurable hseq_meas.aemeasurable
                hindicator_meas.aestronglyMeasurable hpartial_pow_meas.aestronglyMeasurable
    _ = ((natRandomVariableLaw P T hT_meas) n).toReal *
          ∫ ω, (z : ℝ) ^ ∑ i : Fin n, X i ω ∂P := by
            rw [hT_factor]
    _ = ((natRandomVariableLaw P T hT_meas) n).toReal *
          ((probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z : ℝ)) ^ n := by
            rw [integral_pow_partial_sum_eq_pow_common_pgf P X hX_meas hX_indep hX_ident n z]

/-- Helper for Theorem 3.8: integrating `z ^ natRandomSum` over the partition `{ω | T ω = n}`
produces the scalar series indexed by the counting variable law. -/
theorem integral_pow_natRandomSum_eq_tsum_countingLaw_mul_common_pgf_pow
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ) (hT_meas : Measurable T)
    (X : ℕ → Ω → ℕ) (hX_meas : ∀ n, Measurable (X n))
    (hTX_indep : IndepFun T (fun ω ↦ fun n ↦ X n ω) P) (hX_indep : iIndepFun X P)
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P) (z : Set.Icc (0 : ℝ) 1) :
    ∫ ω, (z : ℝ) ^ natRandomSum T X ω ∂P =
      ∑' n : ℕ, ((natRandomVariableLaw P T hT_meas) n).toReal *
        ((probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z : ℝ)) ^ n := by
  let A : ℕ → Set Ω := fun n ↦ {ω | T ω = n}
  have hA_meas : ∀ n, MeasurableSet (A n) := by
    intro n
    exact hT_meas (measurableSet_singleton n)
  have hA_disjoint : Pairwise (fun m n ↦ Disjoint (A m) (A n)) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun ω hm hn ↦ ?_
    have hm' : T ω = m := by simpa [A] using hm
    have hn' : T ω = n := by simpa [A] using hn
    exact hmn (hm'.symm.trans hn')
  have hA_union : ⋃ n, A n = Set.univ := by
    ext ω
    simp [A]
  have hpow_integrable : Integrable (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω) P := by
    -- The integrand is measurable and bounded by `1` on the unit interval.
    refine Integrable.of_bound
      ((measurable_natRandomSum T hT_meas X hX_meas).const_pow (z : ℝ)).aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (pow_nonneg z.2.1 _)]
    exact pow_le_one₀ z.2.1 z.2.2
  have hpow_integrableOn :
      IntegrableOn (fun ω ↦ (z : ℝ) ^ natRandomSum T X ω) (⋃ n, A n) P := by
    simpa [hA_union] using hpow_integrable
  -- Decompose the integral along the measurable partition given by the values of `T`.
  calc
    ∫ ω, (z : ℝ) ^ natRandomSum T X ω ∂P
        = ∫ ω in ⋃ n, A n, (z : ℝ) ^ natRandomSum T X ω ∂P := by
            rw [hA_union, setIntegral_univ]
    _ = ∑' n, ∫ ω in A n, (z : ℝ) ^ natRandomSum T X ω ∂P := by
          rw [integral_iUnion hA_meas hA_disjoint hpow_integrableOn]
    _ = ∑' n : ℕ, ((natRandomVariableLaw P T hT_meas) n).toReal *
          ((probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z : ℝ)) ^ n := by
            refine tsum_congr fun n ↦ ?_
            simpa [A] using
              setIntegral_pow_natRandomSum_fiber_eq_countingLaw_mul_common_pgf_pow P T hT_meas
                X hX_meas hTX_indep hX_indep hX_ident n z

-- Proof sketch: condition on the value of `T`, use independence of `T` from the whole sequence
-- `X` to identify the law of `natRandomSum T X` as the mixture of the laws of the finite sums,
-- apply the finite-sum pgf product formula, and finally use identical distribution to replace each
-- factor by the common pgf of `X 0`.
/-- Theorem 3.8: If `T` is independent of the sequence `X`, and the `ℕ`-valued random variables
`X n` are independent and identically distributed, then the probability generating function of the
random sum `ω ↦ ∑ i < T ω, X i ω` is obtained by evaluating the probability generating function of
`T` at the common probability generating function of the summands. -/
theorem probabilityGeneratingFunction_natRandomSum_eq_comp_of_indepFun_of_iIndepFun_of_identDistrib
    (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ) (hT_meas : Measurable T)
    (X : ℕ → Ω → ℕ) (hX_meas : ∀ n, Measurable (X n))
    (hTX_indep : IndepFun T (fun ω ↦ fun n ↦ X n ω) P) (hX_indep : iIndepFun X P)
    (hX_ident : ∀ n, IdentDistrib (X n) (X 0) P P) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction
        (natRandomVariableLaw P (natRandomSum T X)
          (measurable_natRandomSum T hT_meas X hX_meas)) z : ℝ) =
      (probabilityGeneratingFunction (natRandomVariableLaw P T hT_meas)
        (probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z) : ℝ) :=
by
  -- Route correction: partition the integral over the fibers `{T = n}` instead of building a
  -- function-valued `tsum`; this matches the textbook conditioning argument directly.
  -- First rewrite the pgf of the random sum as a single expectation.
  calc
    (probabilityGeneratingFunction
        (natRandomVariableLaw P (natRandomSum T X)
          (measurable_natRandomSum T hT_meas X hX_meas)) z : ℝ)
        = ∫ ω, (z : ℝ) ^ natRandomSum T X ω ∂P := by
            rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral P (natRandomSum T X)
              (measurable_natRandomSum T hT_meas X hX_meas) z]
    _ = ∑' n : ℕ, ((natRandomVariableLaw P T hT_meas) n).toReal *
          ((probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z : ℝ)) ^ n := by
            rw [integral_pow_natRandomSum_eq_tsum_countingLaw_mul_common_pgf_pow P T hT_meas
              X hX_meas hTX_indep hX_indep hX_ident z]
    _ = (probabilityGeneratingFunction (natRandomVariableLaw P T hT_meas)
          (probabilityGeneratingFunction (natRandomVariableLaw P (X 0) (hX_meas 0)) z) : ℝ) := by
            symm
            rw [probabilityGeneratingFunction_apply]

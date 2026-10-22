/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_32

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- A real random variable satisfies the textbook finite absolute-moment root-growth limsup
hypothesis if it is measurable, all of its absolute moments are finite, and the normalized nth
roots of those absolute moments are bounded above along `atTop`. -/
def HasFiniteAbsoluteMomentRootLimsup (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) : Prop :=
  Measurable X ∧
    (∀ n : ℕ, Integrable (fun ω ↦ |X ω| ^ n) P) ∧
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n : ℕ ↦ ((n : ℝ)⁻¹) * Real.rpow (moment (fun ω ↦ |X ω|) n P) (1 / (n : ℝ)))

/-- Finite absolute-moment root-growth limsup is exactly measurability, finiteness of all absolute
moments, and boundedness of the normalized absolute moments. -/
@[simp] theorem hasFiniteAbsoluteMomentRootLimsup_iff (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → ℝ) :
    HasFiniteAbsoluteMomentRootLimsup P X ↔
      Measurable X ∧
        (∀ n : ℕ, Integrable (fun ω ↦ |X ω| ^ n) P) ∧
          Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
            (fun n : ℕ ↦ ((n : ℝ)⁻¹) * Real.rpow (moment (fun ω ↦ |X ω|) n P) (1 / (n : ℝ))) := by
  rfl

-- The source-facing finite absolute-moment root-growth limsup hypothesis implies the chapter's
-- canonical moment-determinacy predicate.
--
-- Proof sketch: first bridge the source-facing limsup hypothesis to exponential integrability of
-- `|X|`, then invoke the chapter's method-of-moments theorem for pushforward laws.
/-- Helper for Exercise 15.4.1: the limsup growth hypothesis should yield a positive exponential
moment for `|X|`. -/
lemma natMulPowDivFactorialSummable (Λ : ℝ) :
    Summable (fun m : ℕ ↦ (m : ℝ) * Λ ^ m / m.factorial) := by
  -- Reindex the derivative of the exponential series to obtain the extra `m` factor.
  have hpow : Summable (fun m : ℕ ↦ Λ ^ m / m.factorial) :=
    Real.summable_pow_div_factorial Λ
  have hbase : Summable (fun m : ℕ ↦ Λ * (Λ ^ m / m.factorial)) :=
    hpow.mul_left Λ
  have hterm : ∀ m : ℕ,
      ((m + 1 : ℕ) : ℝ) * Λ ^ (m + 1) / (m + 1).factorial
        = Λ * (Λ ^ m / m.factorial) := by
    intro m
    rw [Nat.factorial_succ, pow_succ]
    have hm : (((m + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have hm' : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    -- Cancel the common `(m + 1)` factor after expanding `(m + 1)!`.
    field_simp [hm, hm', hf]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hshift :
      Summable
        (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ) * Λ ^ (m + 1) / (m + 1).factorial) :=
    hbase.congr (fun m ↦ (hterm m).symm)
  -- Shift the summable tail back to the original indexing.
  exact
    (summable_nat_add_iff
      (f := fun m : ℕ ↦ (m : ℝ) * Λ ^ m / m.factorial) 1).1 hshift

/-- Helper for Exercise 15.4.1: Stirling's lower bound implies
`(n : ℝ)^n / n.factorial ≤ (Real.exp 1)^n` for every `n ≥ 1`. -/
lemma powDivFactorial_le_expNat {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ n / n.factorial ≤ (Real.exp 1) ^ n := by
  have hsqrt_ge_one : 1 ≤ Real.sqrt (2 * Real.pi * n : ℝ) := by
    rw [Real.one_le_sqrt]
    · have hpi : 1 < Real.pi := by
        nlinarith [Real.pi_gt_three]
      have hn' : (1 : ℝ) ≤ n := by
        exact_mod_cast hn
      nlinarith
  have hstirling : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / Real.exp 1) ^ n = 1 * ((n : ℝ) / Real.exp 1) ^ n := by ring
      _ ≤ Real.sqrt (2 * Real.pi * n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n := by
            gcongr
      _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  have hdiv : ((n : ℝ) / Real.exp 1) ^ n / n.factorial ≤ 1 := by
    have hstirling' : ((n : ℝ) / Real.exp 1) ^ n ≤ 1 * (n.factorial : ℝ) := by
      simpa using hstirling
    exact (div_le_iff₀ (show 0 < (n.factorial : ℝ) by positivity)).2 hstirling'
  calc
    (n : ℝ) ^ n / n.factorial
        = (Real.exp 1) ^ n * (((n : ℝ) ^ n / (Real.exp 1) ^ n) / n.factorial) := by
            have hexpn : (Real.exp 1) ^ n ≠ 0 := by positivity
            field_simp [hexpn]
    _ = (Real.exp 1) ^ n * ((((n : ℝ) / Real.exp 1) ^ n) / n.factorial) := by
          rw [div_pow]
    _ ≤ (Real.exp 1) ^ n * 1 := by
          gcongr
    _ = (Real.exp 1) ^ n := by ring

/-- Helper for Exercise 15.4.1: the limsup hypothesis eventually gives a linear bound on the
unnormalized moment roots. -/
lemma eventuallyMomentRootLe_mul_of_hasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : HasFiniteAbsoluteMomentRootLimsup P X) :
    ∃ C : ℝ,
      ∀ᶠ n in Filter.atTop,
        1 ≤ n ∧
          Real.rpow (moment (fun ω ↦ |X ω|) n P) (1 / (n : ℝ)) ≤ C * n := by
  rcases hX with ⟨-, -, hX_bdd⟩
  rcases hX_bdd with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  -- Combine the eventual boundedness from the source hypothesis with the eventual positivity of `n`.
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hC] with n hn hCn
  constructor
  · exact hn
  · have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hmul :=
      mul_le_mul_of_nonneg_left hCn (show 0 ≤ (n : ℝ) by positivity)
    simpa [mul_assoc, hn0, mul_comm, mul_left_comm] using hmul

/-- Helper for Exercise 15.4.1: absolute moments are nonnegative because the integrand `|X|^n`
is pointwise nonnegative. -/
lemma moment_abs_nonneg (P : Measure Ω) {X : Ω → ℝ} (n : ℕ) :
    0 ≤ moment (fun ω ↦ |X ω|) n P := by
  -- Proof comment: `moment` is an integral of the nonnegative function `ω ↦ |X ω|^n`.
  rw [moment]
  exact integral_nonneg_of_ae (ae_of_all _ fun ω ↦ pow_nonneg (abs_nonneg (X ω)) n)

/-- Helper for Exercise 15.4.1: a linear bound on the normalized root controls the exponential
series coefficient at order `n`. -/
lemma expMomentCoeffLe_expRate_of_rootBound {a D t : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hD : 0 ≤ D) (ht : 0 ≤ t) (hn : 1 ≤ n)
    (hroot : Real.rpow a (1 / (n : ℝ)) ≤ D * n) :
    t ^ n * a / n.factorial ≤ (t * D * Real.exp 1) ^ n := by
  have hn0 : n ≠ 0 := by omega
  have hfac_nonneg : 0 ≤ ((n.factorial : ℕ) : ℝ) := by positivity
  have hroot_nonneg : 0 ≤ Real.rpow a (1 / (n : ℝ)) := Real.rpow_nonneg ha _
  have hpow :
      (Real.rpow a (1 / (n : ℝ))) ^ n = a := by
    -- Proof comment: recover the original moment from its normalized `n`th root.
    simpa [one_div] using (Real.rpow_inv_natCast_pow ha hn0)
  have htd_nonneg : 0 ≤ t * D := mul_nonneg ht hD
  calc
    t ^ n * a / n.factorial
        = t ^ n * (Real.rpow a (1 / (n : ℝ))) ^ n / n.factorial := by
            conv_lhs => rw [← hpow]
    _ = (t * Real.rpow a (1 / (n : ℝ))) ^ n / n.factorial := by
          rw [← mul_pow]
    _ ≤ (t * (D * n)) ^ n / n.factorial := by
          refine div_le_div_of_nonneg_right ?_ hfac_nonneg
          exact
            pow_le_pow_left₀ (mul_nonneg ht hroot_nonneg)
              (mul_le_mul_of_nonneg_left hroot ht) n
    _ = (t * D) ^ n * ((n : ℝ) ^ n / n.factorial) := by
          have hmul : t * (D * (n : ℝ)) = (t * D) * n := by ring
          rw [hmul, mul_pow]
          ring
    _ ≤ (t * D) ^ n * (Real.exp 1) ^ n := by
          exact mul_le_mul_of_nonneg_left (powDivFactorial_le_expNat hn) (pow_nonneg htd_nonneg _)
    _ = ((t * D) * Real.exp 1) ^ n := by rw [← mul_pow]
    _ = (t * D * Real.exp 1) ^ n := by simp [mul_assoc]

/-- Helper for Exercise 15.4.1: the limsup hypothesis yields an eventual geometric bound on the
exponential-series coefficients with ratio `1 / 2`. -/
lemma existsPosEventualExpMomentCoeffLe_halfPow_of_hasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasFiniteAbsoluteMomentRootLimsup P X) :
    ∃ t : ℝ, 0 < t ∧
      ∀ᶠ n in Filter.atTop,
        t ^ n * moment (fun ω ↦ |X ω|) n P / n.factorial ≤ (1 / 2 : ℝ) ^ n := by
  rcases eventuallyMomentRootLe_mul_of_hasFiniteAbsoluteMomentRootLimsup P hX with ⟨C, hC⟩
  let D0 : ℝ := max C 1
  let t : ℝ := (2 * D0 * Real.exp 1)⁻¹
  have hD0_nonneg : 0 ≤ D0 := by
    dsimp [D0]
    positivity
  have hD0_ge_one : (1 : ℝ) ≤ D0 := by
    exact le_max_right C 1
  have hD0_pos : 0 < D0 := lt_of_lt_of_le zero_lt_one hD0_ge_one
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hexp_ne : Real.exp 1 ≠ 0 := by positivity
  have hRate : t * D0 * Real.exp 1 = (1 / 2 : ℝ) := by
    -- Proof comment: the explicit choice `t = (2 * D0 * exp 1)⁻¹` fixes the tail ratio at `1/2`.
    dsimp [t]
    field_simp [hD0_pos.ne', hexp_ne]
  refine ⟨t, ht_pos, ?_⟩
  filter_upwards [hC] with n hn
  rcases hn with ⟨hn1, hrootC⟩
  have hrootD0 : Real.rpow (moment (fun ω ↦ |X ω|) n P) (1 / (n : ℝ)) ≤ D0 * n := by
    -- Proof comment: replace the possibly nonpositive bound `C` by the canonical positive constant
    -- `D0 = max C 1`.
    calc
      Real.rpow (moment (fun ω ↦ |X ω|) n P) (1 / (n : ℝ)) ≤ C * n := hrootC
      _ ≤ D0 * n := by
            have hC_le_D0 : C ≤ D0 := le_max_left C 1
            nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  have hCoeff :=
    expMomentCoeffLe_expRate_of_rootBound
      (moment_abs_nonneg P n) hD0_nonneg ht_pos.le hn1 hrootD0
  simpa [hRate] using hCoeff

/-- Helper for Exercise 15.4.1: the geometric tail estimate packages into summability of the
exponential-series coefficients. -/
lemma existsPosSummableExpMomentSeriesOfHasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasFiniteAbsoluteMomentRootLimsup P X) :
    ∃ t : ℝ, 0 < t ∧
      Summable (fun n : ℕ ↦ t ^ n * moment (fun ω ↦ |X ω|) n P / n.factorial) := by
  rcases existsPosEventualExpMomentCoeffLe_halfPow_of_hasFiniteAbsoluteMomentRootLimsup P hX with
    ⟨t, ht, htail⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htail
  have hgeom : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) := by
    exact summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hgeomShift : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + N)) := by
    exact (_root_.summable_nat_add_iff N).2 hgeom
  have hcoeff_nonneg :
      ∀ n : ℕ, 0 ≤ t ^ n * moment (fun ω ↦ |X ω|) n P / n.factorial := by
    intro n
    exact div_nonneg (mul_nonneg (pow_nonneg ht.le _) (moment_abs_nonneg P n)) (by positivity)
  have htailSummable :
      Summable
        (fun n : ℕ ↦
          t ^ (n + N) * moment (fun ω ↦ |X ω|) (n + N) P / (n + N).factorial) := by
    -- Proof comment: compare the shifted tail directly against the geometric majorant `(1/2)^(n+N)`.
    refine Summable.of_nonneg_of_le (fun n ↦ hcoeff_nonneg (n + N)) ?_ hgeomShift
    intro n
    exact hN (n + N) (Nat.le_add_left N n)
  refine ⟨t, ht, ?_⟩
  -- Proof comment: summability of a shifted tail is equivalent to summability of the full series.
  exact (_root_.summable_nat_add_iff N).1 htailSummable

/-- Helper for Exercise 15.4.1: `Real.exp (t * |x|)` is the exponential power series written in
the coefficient shape used for absolute moments. -/
lemma exp_mul_abs_eq_tsum_scaledAbsPowers (t x : ℝ) :
    Real.exp (t * |x|) = ∑' n : ℕ, (t ^ n / n.factorial) * |x| ^ n := by
  have hExp :
      Real.exp (t * |x|) = ∑' n : ℕ, (t * |x|) ^ n / n.factorial := by
    simpa [Real.exp_eq_exp_ℝ] using
      congrArg (fun f : ℝ → ℝ => f (t * |x|))
        (NormedSpace.exp_eq_tsum_div : NormedSpace.exp = fun y : ℝ =>
          ∑' n : ℕ, y ^ n / n.factorial)
  refine hExp.trans ?_
  refine tsum_congr fun n ↦ ?_
  rw [mul_pow]
  ring

/-- Helper for Exercise 15.4.1: applying `ENNReal.ofReal` to the exponential series preserves the
same coefficient shape because every summand is nonnegative. -/
lemma ennreal_ofReal_exp_mul_abs_eq_tsum_scaledAbsPowers (t x : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (t * |x|)) =
      ∑' n : ℕ, ENNReal.ofReal ((t ^ n / n.factorial) * |x| ^ n) := by
  rw [exp_mul_abs_eq_tsum_scaledAbsPowers]
  have hsum : Summable (fun n : ℕ ↦ (t ^ n / n.factorial) * |x| ^ n) := by
    -- Proof comment: this is the ordinary exponential series evaluated at `t * |x|`.
    refine (Real.summable_pow_div_factorial (t * |x|)).congr ?_
    intro n
    rw [mul_pow]
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n ↦
      mul_nonneg
        (div_nonneg (pow_nonneg ht _) (by positivity))
        (pow_nonneg (abs_nonneg x) _))
    hsum]

/-- Helper for Exercise 15.4.1: integrating a scaled absolute power rewrites directly to the
corresponding scaled absolute moment. -/
lemma integral_scaledAbsPow_eq_scaledMoment
    (P : Measure Ω) {X : Ω → ℝ} (t : ℝ) (n : ℕ) :
    ∫ ω, (t ^ n / n.factorial) * |X ω| ^ n ∂P =
      t ^ n * moment (fun ω ↦ |X ω|) n P / n.factorial := by
  -- Proof comment: pull the scalar coefficient out of the integral, then unfold `moment`.
  rw [integral_const_mul, moment]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 15.4.1: the limsup growth hypothesis should yield a positive exponential
moment for `|X|`. -/
lemma existsPosIntegrableExpAbsOfHasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasFiniteAbsoluteMomentRootLimsup P X) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun ω ↦ Real.exp (t * |X ω|)) P := by
  -- Proof comment: first package the limsup hypothesis into a summable absolute-moment series.
  rcases existsPosSummableExpMomentSeriesOfHasFiniteAbsoluteMomentRootLimsup P hX with
    ⟨t, ht, hsum⟩
  have hterm_meas :
      ∀ n : ℕ, AEMeasurable (fun ω ↦ ENNReal.ofReal ((t ^ n / n.factorial) * |X ω| ^ n)) P := by
    intro n
    -- Proof comment: measurability comes from `X`, then `ENNReal.ofReal` preserves it.
    exact ((measurable_const.mul (hX.1.abs.pow_const n)).ennreal_ofReal).aemeasurable
  have hcoeff_nonneg :
      ∀ n : ℕ, 0 ≤ t ^ n * moment (fun ω ↦ |X ω|) n P / n.factorial := by
    intro n
    exact
      div_nonneg
        (mul_nonneg (pow_nonneg ht.le _) (moment_abs_nonneg P n))
        (by positivity)
  have hterm_lintegral :
      ∀ n : ℕ,
        ∫⁻ ω, ENNReal.ofReal ((t ^ n / n.factorial) * |X ω| ^ n) ∂P =
          ENNReal.ofReal (t ^ n * moment (fun ω ↦ |X ω|) n P / n.factorial) := by
    intro n
    have hterm_nonneg :
        0 ≤ᵐ[P] fun ω ↦ (t ^ n / n.factorial) * |X ω| ^ n := by
      filter_upwards with ω
      exact
        mul_nonneg
          (div_nonneg (pow_nonneg ht.le _) (by positivity))
          (pow_nonneg (abs_nonneg (X ω)) _)
    have hterm_int :
        Integrable (fun ω ↦ (t ^ n / n.factorial) * |X ω| ^ n) P :=
      (hX.2.1 n).const_mul (t ^ n / n.factorial)
    -- Proof comment: identify each nonnegative series term with its scaled absolute moment.
    calc
      ∫⁻ ω, ENNReal.ofReal ((t ^ n / n.factorial) * |X ω| ^ n) ∂P =
          ENNReal.ofReal (∫ ω, (t ^ n / n.factorial) * |X ω| ^ n ∂P) := by
            exact
              (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hterm_int
                hterm_nonneg).symm
      _ = ENNReal.ofReal
            (t ^ n * moment (fun ω ↦ |X ω|) n P / n.factorial) := by
            rw [integral_scaledAbsPow_eq_scaledMoment P t n]
  have hseries_lt_top :
      ∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal ((t ^ n / n.factorial) * |X ω| ^ n) ∂P < ⊤ := by
    -- Proof comment: exchange the lower integral and the nonnegative exponential series.
    calc
      ∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal ((t ^ n / n.factorial) * |X ω| ^ n) ∂P =
          ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal ((t ^ n / n.factorial) * |X ω| ^ n) ∂P := by
        rw [MeasureTheory.lintegral_tsum hterm_meas]
      _ = ∑' n : ℕ, ENNReal.ofReal
            (t ^ n * moment (fun ω ↦ |X ω|) n P / n.factorial) := by
          refine tsum_congr fun n ↦ hterm_lintegral n
      _ = ENNReal.ofReal
            (∑' n : ℕ, t ^ n * moment (fun ω ↦ |X ω|) n P / n.factorial) := by
          symm
          exact ENNReal.ofReal_tsum_of_nonneg hcoeff_nonneg hsum
      _ < ⊤ := by
          exact ENNReal.ofReal_lt_top
  have hseries_eq :
      (fun ω ↦ ENNReal.ofReal (Real.exp (t * |X ω|))) =
        fun ω ↦ ∑' n : ℕ, ENNReal.ofReal ((t ^ n / n.factorial) * |X ω| ^ n) := by
    funext ω
    simpa using ennreal_ofReal_exp_mul_abs_eq_tsum_scaledAbsPowers t (X ω) ht.le
  have hlintegral_lt_top :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * |X ω|)) ∂P < ⊤ := by
    -- Proof comment: rewrite the integrand using the exponential power-series identity.
    simpa [hseries_eq] using hseries_lt_top
  have hnonneg :
      0 ≤ᵐ[P] fun ω ↦ Real.exp (t * |X ω|) := by
    filter_upwards with ω
    exact (Real.exp_pos _).le
  have hmeas : AEStronglyMeasurable (fun ω ↦ Real.exp (t * |X ω|)) P := by
    -- Proof comment: strong measurability follows from measurability of `X`, then composition
    -- with the continuous exponential map.
    exact
      (Real.continuous_exp.measurable.comp (measurable_const.mul hX.1.abs)).aestronglyMeasurable
  exact
    ⟨t, ht,
      (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).1
        (ne_of_lt hlintegral_lt_top)⟩

theorem isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasFiniteAbsoluteMomentRootLimsup P X) :
    IsMomentDeterminate P X := by
  have hX_meas : Measurable X := hX.1
  -- Proof comment: once the auxiliary exponential-moment bridge is available, the owner-level
  -- method-of-moments theorem applies directly to the law of `X`.
  rcases existsPosIntegrableExpAbsOfHasFiniteAbsoluteMomentRootLimsup P hX with ⟨t, ht, h_exp⟩
  exact (method_of_moments_of_integrable_exp_abs_map P X hX_meas ht h_exp).2

/-- Helper for Exercise 15.4.1: under pointwise nonnegativity, absolute powers coincide with
ordinary powers. -/
lemma absPow_eq_pow_of_nonneg {Z : Ω → ℝ} (hZ_nonneg : ∀ ω, 0 ≤ Z ω) (n : ℕ) :
    (fun ω ↦ |Z ω| ^ n) = fun ω ↦ Z ω ^ n := by
  funext ω
  rw [abs_of_nonneg (hZ_nonneg ω)]

/-- Helper for Exercise 15.4.1: under pointwise nonnegativity, integrability of absolute powers is
the same as integrability of ordinary powers. -/
lemma integrable_absPow_iff_integrable_pow_of_nonneg
    {P : Measure Ω} {Z : Ω → ℝ} (hZ_nonneg : ∀ ω, 0 ≤ Z ω) (n : ℕ) :
    Integrable (fun ω ↦ |Z ω| ^ n) P ↔ Integrable (fun ω ↦ Z ω ^ n) P := by
  simpa [absPow_eq_pow_of_nonneg hZ_nonneg n]

/-- Helper for Exercise 15.4.1: under pointwise nonnegativity, absolute moments are the ordinary
moments. -/
lemma moment_abs_eq_moment_of_nonneg
    {P : Measure Ω} {Z : Ω → ℝ} (hZ_nonneg : ∀ ω, 0 ≤ Z ω) (n : ℕ) :
    moment (fun ω ↦ |Z ω|) n P = moment Z n P := by
  simp [moment, abs_of_nonneg, hZ_nonneg]

/-- Helper for Exercise 15.4.1: the normalized `X^m`-tilt preserves the law of `Y` because the
tilted moments of `Y` agree with the original ones. -/
lemma powTilt_map_eq_map_of_mixedMoments
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX_growth : HasFiniteAbsoluteMomentRootLimsup P X)
    (hY_det : IsMomentDeterminate P Y)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (h_mixedMoments :
      ∀ m n : ℕ, Integrable (fun ω ↦ X ω ^ m * Y ω ^ n) P ∧
        ∫ ω, X ω ^ m * Y ω ^ n ∂P = moment X m P * moment Y n P)
    (m : ℕ) (hm : moment X m P ≠ 0) :
    Measure.map Y
        ((ENNReal.ofReal (moment X m P))⁻¹ •
          P.withDensity (fun ω ↦ ENNReal.ofReal (X ω ^ m))) =
      Measure.map Y P := by
  set ν0 : Measure Ω := P.withDensity (fun ω ↦ ENNReal.ofReal (X ω ^ m)) with hν0def
  set νm : Measure Ω := (ENNReal.ofReal (moment X m P))⁻¹ • ν0 with hνmdef
  have hY_meas : Measurable Y := hY_det.1
  have hXpow_nonneg : ∀ ω, 0 ≤ X ω ^ m := by
    intro ω
    exact pow_nonneg (hX_nonneg ω) m
  have hXpow_integrable : Integrable (fun ω ↦ X ω ^ m) P := by
    rw [← integrable_absPow_iff_integrable_pow_of_nonneg hX_nonneg]
    exact hX_growth.2.1 m
  have hMoment_nonneg : 0 ≤ moment X m P := by
    rw [moment]
    exact integral_nonneg_of_ae (ae_of_all _ hXpow_nonneg)
  have hf_meas : Measurable (fun ω ↦ ENNReal.ofReal (X ω ^ m)) := by
    -- Proof comment: the tilt density is the measurable nonnegative power `X^m`.
    exact (hX_growth.1.pow_const m).ennreal_ofReal
  have hf_top : ∀ᵐ ω ∂P, ENNReal.ofReal (X ω ^ m) < ⊤ := by
    filter_upwards with ω
    simp
  have hν0_univ : ν0 Set.univ = ENNReal.ofReal (moment X m P) := by
    -- Proof comment: the total mass of the unnormalized tilt is the `m`th moment of `X`.
    rw [hν0def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hXpow_integrable
      (ae_of_all _ hXpow_nonneg)]
    simp [moment, hXpow_nonneg]
  have hMoment_ofReal_ne : ENNReal.ofReal (moment X m P) ≠ 0 := by
    intro h0
    apply hm
    exact le_antisymm (by simpa [ENNReal.ofReal_eq_zero] using h0) hMoment_nonneg
  letI : IsProbabilityMeasure νm := by
    constructor
    -- Proof comment: normalize the tilted mass by the inverse of `E[X^m]`.
    rw [hνmdef, Measure.smul_apply, hν0_univ]
    exact ENNReal.inv_mul_cancel hMoment_ofReal_ne ENNReal.ofReal_ne_top
  have hY_moments : ∀ n : ℕ, Integrable (fun ω ↦ |Y ω| ^ n) νm := by
    intro n
    have hYpow_integrable_ν0 : Integrable (fun ω ↦ Y ω ^ n) ν0 := by
      -- Proof comment: integrability under the tilted law is equivalent to integrability of
      -- `X^m * Y^n` under `P`, which is exactly the mixed-moment hypothesis.
      rw [hν0def, MeasureTheory.integrable_withDensity_iff hf_meas hf_top]
      simpa [ENNReal.toReal_ofReal, hXpow_nonneg, smul_eq_mul, mul_comm, mul_left_comm,
        mul_assoc] using (h_mixedMoments m n).1
    have hYpow_integrable_νm : Integrable (fun ω ↦ Y ω ^ n) νm := by
      simpa [hνmdef] using
        hYpow_integrable_ν0.smul_measure (ENNReal.inv_ne_top.2 hMoment_ofReal_ne)
    exact (integrable_absPow_iff_integrable_pow_of_nonneg hY_nonneg n).2 hYpow_integrable_νm
  have hMoments : ∀ n : ℕ, moment Y n νm = moment Y n P := by
    intro n
    -- Proof comment: compute the tilted moment, substitute mixed-moment factorization, and
    -- cancel the normalizing factor `E[X^m]`.
    rw [hνmdef, moment, MeasureTheory.integral_smul_measure, smul_eq_mul, hν0def,
      integral_withDensity_eq_integral_toReal_smul hf_meas hf_top]
    have hMixed :
        ∫ ω, (ENNReal.ofReal (X ω ^ m)).toReal • (Y ^ n) ω ∂P =
          moment X m P * moment Y n P := by
      simpa [ENNReal.toReal_ofReal, hXpow_nonneg, smul_eq_mul, mul_comm, mul_left_comm,
        mul_assoc] using (h_mixedMoments m n).2
    rw [hMixed]
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hMoment_nonneg]
    field_simp [hm]
  -- Proof comment: `Y` is moment determinate, so matching all tilted moments forces equality of
  -- the pushed-forward laws.
  have hmap : Measure.map Y P = Measure.map Y νm :=
    hY_det.map_eq νm Y hY_meas hY_moments (fun n ↦ (hMoments n).symm)
  simpa [hνmdef, hν0def] using hmap.symm

/-- Helper for Exercise 15.4.1: the unnormalized `X^m`-weighted mass of a measurable set is the
`ENNReal.ofReal` image of the corresponding set integral. -/
lemma withDensityApply_eq_ofReal_setIntegral_pow
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_growth : HasFiniteAbsoluteMomentRootLimsup P X)
    (hX_nonneg : ∀ ω, 0 ≤ X ω) (m : ℕ) {A : Set Ω} (hA : MeasurableSet A) :
    P.withDensity (fun ω ↦ ENNReal.ofReal (X ω ^ m)) A =
      ENNReal.ofReal (∫ ω in A, X ω ^ m ∂P) := by
  have hXpow_nonneg : ∀ ω, 0 ≤ X ω ^ m := by
    intro ω
    exact pow_nonneg (hX_nonneg ω) m
  have hXpow_integrable : Integrable (fun ω ↦ X ω ^ m) P := by
    rw [← integrable_absPow_iff_integrable_pow_of_nonneg hX_nonneg]
    exact hX_growth.2.1 m
  have hXpow_integrable_restrict : Integrable (fun ω ↦ X ω ^ m) (P.restrict A) :=
    hXpow_integrable.restrict
  have hXpow_nonneg_restrict : 0 ≤ᵐ[P.restrict A] fun ω ↦ X ω ^ m :=
    ae_restrict_of_ae (ae_of_all _ hXpow_nonneg)
  -- Proof comment: rewrite the weighted mass through `withDensity_apply`, then identify the
  -- resulting lower integral with the usual set integral of the nonnegative density.
  rw [MeasureTheory.withDensity_apply _ hA]
  simpa [Measure.restrict_apply, hA] using
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      hXpow_integrable_restrict hXpow_nonneg_restrict).symm

/-- Helper for Exercise 15.4.1: evaluating the normalized `X^m`-tilt on a measurable `Y`-event
gives back the original event mass. -/
lemma powTiltPreimage_eq_preimage_of_mixedMoments
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX_growth : HasFiniteAbsoluteMomentRootLimsup P X)
    (hY_det : IsMomentDeterminate P Y)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (h_mixedMoments :
      ∀ m n : ℕ, Integrable (fun ω ↦ X ω ^ m * Y ω ^ n) P ∧
        ∫ ω, X ω ^ m * Y ω ^ n ∂P = moment X m P * moment Y n P)
    (m : ℕ) (hm : moment X m P ≠ 0) {T : Set ℝ} (hT : MeasurableSet T) :
    ((ENNReal.ofReal (moment X m P))⁻¹ •
        P.withDensity (fun ω ↦ ENNReal.ofReal (X ω ^ m))) (Y ⁻¹' T) =
      P (Y ⁻¹' T) := by
  have hY_meas : Measurable Y := hY_det.1
  have hmap :=
    powTilt_map_eq_map_of_mixedMoments P X Y hX_growth hY_det hX_nonneg hY_nonneg
      h_mixedMoments m hm
  have hEval :
      ((ENNReal.ofReal (moment X m P))⁻¹ •
          P.withDensity (fun ω ↦ ENNReal.ofReal (X ω ^ m))) (Y ⁻¹' T) =
        P (Y ⁻¹' T) := by
    -- Proof comment: evaluate the equality of tilted pushforward laws on the measurable set `T`.
    simpa [Measure.map_apply_of_aemeasurable hY_meas.aemeasurable hT] using
      congrArg (fun μ : Measure ℝ => μ T) hmap
  -- Proof comment: evaluate the equality of tilted pushforward laws on the measurable set `T`.
  exact hEval

/-- Helper for Exercise 15.4.1: the nonzero `X^m`-tilt identity can be rewritten directly as an
`ENNReal` equality for the weighted mass of a measurable `Y`-event. -/
lemma weightedEventMassENNReal_eq_of_mixedMoments
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX_growth : HasFiniteAbsoluteMomentRootLimsup P X)
    (hY_det : IsMomentDeterminate P Y)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (h_mixedMoments :
      ∀ m n : ℕ, Integrable (fun ω ↦ X ω ^ m * Y ω ^ n) P ∧
        ∫ ω, X ω ^ m * Y ω ^ n ∂P = moment X m P * moment Y n P)
    (m : ℕ) (hm : moment X m P ≠ 0) {T : Set ℝ} (hT : MeasurableSet T) :
    ENNReal.ofReal (∫ ω in Y ⁻¹' T, X ω ^ m ∂P) =
      ENNReal.ofReal (moment X m P) * P (Y ⁻¹' T) := by
  have hWeighted :
      (ENNReal.ofReal (moment X m P))⁻¹ *
          ENNReal.ofReal (∫ ω in Y ⁻¹' T, X ω ^ m ∂P) =
        P (Y ⁻¹' T) := by
    -- Proof comment: rewrite the tilted event mass using the normalized tilt and then replace the
    -- `withDensity` term by the weighted set integral.
    simpa [Measure.smul_apply,
      withDensityApply_eq_ofReal_setIntegral_pow P hX_growth hX_nonneg m (hY_det.1 hT)] using
      powTiltPreimage_eq_preimage_of_mixedMoments P X Y hX_growth hY_det hX_nonneg hY_nonneg
        h_mixedMoments m hm hT
  have hMoment_nonneg : 0 ≤ moment X m P := by
    rw [moment]
    exact integral_nonneg_of_ae (ae_of_all _ fun ω ↦ pow_nonneg (hX_nonneg ω) m)
  have hMoment_ofReal_ne : ENNReal.ofReal (moment X m P) ≠ 0 := by
    intro h0
    apply hm
    exact le_antisymm (by simpa [ENNReal.ofReal_eq_zero] using h0) hMoment_nonneg
  -- Proof comment: multiply the normalized identity back by `E[X^m]` entirely inside `ENNReal`.
  calc
    ENNReal.ofReal (∫ ω in Y ⁻¹' T, X ω ^ m ∂P)
        = (ENNReal.ofReal (moment X m P) * (ENNReal.ofReal (moment X m P))⁻¹) *
            ENNReal.ofReal (∫ ω in Y ⁻¹' T, X ω ^ m ∂P) := by
              rw [ENNReal.mul_inv_cancel hMoment_ofReal_ne ENNReal.ofReal_ne_top, one_mul]
    _ = ENNReal.ofReal (moment X m P) *
          ((ENNReal.ofReal (moment X m P))⁻¹ *
            ENNReal.ofReal (∫ ω in Y ⁻¹' T, X ω ^ m ∂P)) := by
              rw [mul_assoc]
    _ = ENNReal.ofReal (moment X m P) * P (Y ⁻¹' T) := by rw [hWeighted]

/-- Helper for Exercise 15.4.1: evaluating the `X^m`-tilted law on a `Y`-event yields the textbook
weighted-event identity `E[X^m 1_{Y ∈ T}] = E[X^m] P[Y ∈ T]`. -/
lemma setIntegral_pow_preimage_eq_moment_mul_measure
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX_growth : HasFiniteAbsoluteMomentRootLimsup P X)
    (hY_det : IsMomentDeterminate P Y)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (h_mixedMoments :
      ∀ m n : ℕ, Integrable (fun ω ↦ X ω ^ m * Y ω ^ n) P ∧
        ∫ ω, X ω ^ m * Y ω ^ n ∂P = moment X m P * moment Y n P)
    (m : ℕ) {T : Set ℝ} (hT : MeasurableSet T) :
    ∫ ω in Y ⁻¹' T, X ω ^ m ∂P = moment X m P * (P (Y ⁻¹' T)).toReal := by
  have hYT_meas : MeasurableSet (Y ⁻¹' T) := hY_det.1 hT
  have hXpow_nonneg : ∀ ω, 0 ≤ X ω ^ m := by
    intro ω
    exact pow_nonneg (hX_nonneg ω) m
  have hIntegral_nonneg : 0 ≤ ∫ ω in Y ⁻¹' T, X ω ^ m ∂P := by
    -- Proof comment: the weighted set integral is nonnegative because `X^m` is pointwise
    -- nonnegative on the restricted event.
    exact integral_nonneg_of_ae (ae_of_all _ hXpow_nonneg)
  by_cases hm : moment X m P = 0
  · have hWeighted_zero :
        P.withDensity (fun ω ↦ ENNReal.ofReal (X ω ^ m)) (Y ⁻¹' T) = 0 := by
      -- Proof comment: when `E[X^m] = 0`, the full weighted mass is zero, hence every measurable
      -- `Y`-event has zero weighted mass by monotonicity.
      apply le_antisymm
      · calc
          P.withDensity (fun ω ↦ ENNReal.ofReal (X ω ^ m)) (Y ⁻¹' T)
              ≤ P.withDensity (fun ω ↦ ENNReal.ofReal (X ω ^ m)) Set.univ := by
                  exact measure_mono (by intro ω hω; simp)
          _ = 0 := by
                rw [withDensityApply_eq_ofReal_setIntegral_pow P hX_growth hX_nonneg m
                  MeasurableSet.univ]
                have hMoment_zero : ∫ ω, X ω ^ m ∂P = 0 := by
                  simpa [moment] using hm
                have hMoment_zero_univ : ∫ ω in Set.univ, X ω ^ m ∂P = 0 := by
                  simpa using hMoment_zero
                rw [hMoment_zero_univ]
                simp
      · exact bot_le
    have hIntegral_nonpos : ∫ ω in Y ⁻¹' T, X ω ^ m ∂P ≤ 0 := by
      rw [withDensityApply_eq_ofReal_setIntegral_pow P hX_growth hX_nonneg m hYT_meas]
        at hWeighted_zero
      simpa [ENNReal.ofReal_eq_zero] using hWeighted_zero
    have hIntegral_zero : ∫ ω in Y ⁻¹' T, X ω ^ m ∂P = 0 :=
      le_antisymm hIntegral_nonpos hIntegral_nonneg
    -- Proof comment: both sides are forced to zero in the vanishing-moment branch.
    simp [hm, hIntegral_zero]
  · have hIntegral_enn :=
      weightedEventMassENNReal_eq_of_mixedMoments P X Y hX_growth hY_det hX_nonneg hY_nonneg
        h_mixedMoments m hm hT
    have hMoment_nonneg : 0 ≤ moment X m P := by
      rw [moment]
      exact integral_nonneg_of_ae (ae_of_all _ hXpow_nonneg)
    -- Proof comment: after the nonzero branch is normalized in `ENNReal`, a single `toReal`
    -- conversion recovers the textbook real-valued weighted-event identity.
    calc
      ∫ ω in Y ⁻¹' T, X ω ^ m ∂P
          = ENNReal.toReal (ENNReal.ofReal (∫ ω in Y ⁻¹' T, X ω ^ m ∂P)) := by
              simp [hIntegral_nonneg]
      _ = ENNReal.toReal (ENNReal.ofReal (moment X m P) * P (Y ⁻¹' T)) := by
            exact congrArg ENNReal.toReal hIntegral_enn
      _ = moment X m P * (P (Y ⁻¹' T)).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hMoment_nonneg]

/-- Helper for Exercise 15.4.1: if all conditioned moments of `X` on a positive event `A`
agree with the original moments, then conditioning on `A` does not change the law of `X`. -/
lemma map_cond_eq_map_of_weightedMoments
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX_det : IsMomentDeterminate P X)
    (hX_moments : ∀ n : ℕ, Integrable (fun ω ↦ |X ω| ^ n) P)
    {A : Set Ω} (hA : MeasurableSet A) (hPA : P A ≠ 0)
    (hWeighted :
      ∀ n : ℕ, ∫ ω in A, X ω ^ n ∂P = moment X n P * (P A).toReal) :
    (P[|A]).map X = P.map X := by
  letI : IsProbabilityMeasure (P[|A]) := ProbabilityTheory.cond_isProbabilityMeasure hPA
  have hX_meas : Measurable X := hX_det.1
  have hmap : P.map X = (P[|A]).map X := by
    refine hX_det.map_eq (P[|A]) X hX_meas ?_ ?_
    · intro n
      -- Proof comment: the conditioned measure is a finite scalar multiple of `P.restrict A`, so
      -- absolute-moment integrability descends from `P`.
      have hRestrict : Integrable (fun ω ↦ |X ω| ^ n) (P.restrict A) := (hX_moments n).restrict
      simpa [ProbabilityTheory.cond] using
        hRestrict.smul_measure (by simpa using ENNReal.inv_ne_top.2 hPA)
    · intro n
      have hPA_toReal : (P A).toReal ≠ 0 :=
        ENNReal.toReal_ne_zero.2 ⟨hPA, measure_ne_top P A⟩
      -- Proof comment: rewrite the conditioned moment through `cond = (P A)⁻¹ • P.restrict A`,
      -- insert the weighted-moment hypothesis, and cancel the normalizing factor.
      have hCondMoment : moment X n (P[|A]) = moment X n P := by
        rw [moment, ProbabilityTheory.cond, MeasureTheory.integral_smul_measure, smul_eq_mul]
        change ((P A)⁻¹).toReal * ∫ ω in A, X ω ^ n ∂P = moment X n P
        rw [hWeighted n, ENNReal.toReal_inv]
        calc
          ((P A).toReal)⁻¹ * (moment X n P * (P A).toReal)
              = moment X n P * (((P A).toReal)⁻¹ * (P A).toReal) := by ring
          _ = moment X n P * 1 := by rw [inv_mul_cancel₀ hPA_toReal]
          _ = moment X n P := by ring
      exact hCondMoment.symm
  exact hmap.symm

/-- Helper for Exercise 15.4.1: conditioning on a measurable `Y`-event does not change the law of
`X`, because all conditioned moments of `X` agree with the original ones. -/
lemma map_condPreimage_eq_map_of_mixedMoments
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX_growth : HasFiniteAbsoluteMomentRootLimsup P X)
    (hY_growth : HasFiniteAbsoluteMomentRootLimsup P Y)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (h_mixedMoments :
      ∀ m n : ℕ, Integrable (fun ω ↦ X ω ^ m * Y ω ^ n) P ∧
        ∫ ω, X ω ^ m * Y ω ^ n ∂P = moment X m P * moment Y n P)
    {T : Set ℝ} (hT : MeasurableSet T) (hPT : P (Y ⁻¹' T) ≠ 0) :
    (P[|Y ⁻¹' T]).map X = P.map X := by
  let A : Set Ω := Y ⁻¹' T
  have hX_det : IsMomentDeterminate P X :=
    isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup P hX_growth
  have hY_det : IsMomentDeterminate P Y :=
    isMomentDeterminate_of_hasFiniteAbsoluteMomentRootLimsup P hY_growth
  -- Proof comment: the generic conditional-law helper reduces this step to the textbook weighted
  -- identity on `A = {ω | Y ω ∈ T}`.
  refine map_cond_eq_map_of_weightedMoments P X hX_det hX_growth.2.1 (hY_growth.1 hT) hPT ?_
  intro n
  simpa [A] using
    setIntegral_pow_preimage_eq_moment_mul_measure P X Y hX_growth hY_det hX_nonneg hY_nonneg
      h_mixedMoments n hT

-- Proof sketch: first pass from the source-facing limsup hypotheses to the canonical owner
-- predicate `IsMomentDeterminate`. For each Borel set `A`, use the factorization of mixed moments
-- together with nonnegativity to form the tilted measures with densities `X^m` and `Y^n`; then
-- moment determinacy shows
-- `E[X^m 1_A(Y)] = E[X^m] P[Y ∈ A]` for all `m`, then apply the same argument to the tilted
-- conditional laws of `X` given `Y ∈ A` to deduce factorization of all rectangle probabilities.
/-- Exercise 15.4.1: if nonnegative real random variables `X` and `Y` both satisfy the textbook
finite absolute-moment root-growth limsup hypothesis and all mixed moments factorize as
`E[X^m Y^n] = E[X^m] E[Y^n]`, with those mixed moments finite, then `X` and `Y` are independent. -/
theorem indepFun_of_mixed_moment_factorization_of_hasFiniteAbsoluteMomentRootLimsup
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX_growth : HasFiniteAbsoluteMomentRootLimsup P X)
    (hY_growth : HasFiniteAbsoluteMomentRootLimsup P Y)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (hY_nonneg : ∀ ω, 0 ≤ Y ω)
    (h_mixedMoments :
      ∀ m n : ℕ, Integrable (fun ω ↦ X ω ^ m * Y ω ^ n) P ∧
        ∫ ω, X ω ^ m * Y ω ^ n ∂P = moment X m P * moment Y n P) :
    IndepFun X Y P := by
  have hX_meas : Measurable X := hX_growth.1
  have hY_meas : Measurable Y := hY_growth.1
  -- Route correction: use measurable rectangles, then compare the one-dimensional laws after
  -- tilting by `X^m` and conditioning on events of the form `{Y ∈ A}`.
  rw [ProbabilityTheory.indepFun_iff_indepSet_preimage hX_meas hY_meas]
  intro S T hS hT
  by_cases hPT : P (Y ⁻¹' T) = 0
  · -- If `Y ∈ T` has zero probability, then every rectangle over that event has zero probability.
    have hsubset : X ⁻¹' S ∩ Y ⁻¹' T ⊆ Y ⁻¹' T := by
      intro ω hω
      exact hω.2
    have hInter : P (X ⁻¹' S ∩ Y ⁻¹' T) = 0 := measure_mono_null hsubset hPT
    rw [indepSet_iff_measure_inter_eq_mul (hX_meas hS) (hY_meas hT) P]
    rw [hInter, hPT]
    simp
  · let A : Set Ω := Y ⁻¹' T
    have hMap :
        (P[|A]).map X = P.map X :=
      map_condPreimage_eq_map_of_mixedMoments P X Y hX_growth hY_growth hX_nonneg
        hY_nonneg h_mixedMoments hT hPT
    have hEval : P[X ⁻¹' S | A] = P (X ⁻¹' S) := by
      simpa [A, Measure.map_apply_of_aemeasurable hX_meas.aemeasurable hS] using
        congrArg (fun μ : Measure ℝ => μ S) hMap
    have hMul := congrArg (fun x : ENNReal => x * P A) hEval
    rw [indepSet_iff_measure_inter_eq_mul (hX_meas hS) (hY_meas hT) P]
    simpa [A, ProbabilityTheory.cond_mul_eq_inter (hY_meas hT) (X ⁻¹' S) P,
      Set.inter_comm, Set.inter_left_comm, Set.inter_assoc, mul_assoc, mul_left_comm, mul_comm]
      using hMul

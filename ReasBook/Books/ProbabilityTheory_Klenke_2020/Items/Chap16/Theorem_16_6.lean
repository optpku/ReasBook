/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Exercise_16_1_2

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

section

local notation "E1" => EuclideanSpace ℝ (Fin 1)

/-- Helper for Theorem 16.6: the unique coordinate map `EuclideanSpace ℝ (Fin 1) → ℝ` is
measurable. -/
private theorem measurable_euclidean1ToReal :
    Measurable (euclidean1ToReal : E1 → ℝ) := by
  -- Proof comment: `euclidean1ToReal` is evaluation at the unique coordinate of `ℝ¹`.
  simpa [euclidean1ToReal] using
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 1 ↦ ℝ) (0 : Fin 1)).measurable

/-- Helper for Theorem 16.6: continuity at `0` on `ℝ` yields the one-dimensional
`PartiallyContinuousAtZero` condition after reading the unique coordinate of `ℝ¹`. -/
private theorem partiallyContinuousAtZero_comp_euclidean1ToReal
    {φ : ℝ → ℂ} (hφ0 : ContinuousAt φ 0) :
    PartiallyContinuousAtZero (fun x : E1 ↦ φ (euclidean1ToReal x)) := by
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  -- Proof comment: in dimension one the unique coordinate axis is the original real line.
  simpa [euclidean1ToReal, realToEuclidean1] using hφ0

/-- Helper for Theorem 16.6: pushing a one-dimensional Euclidean law forward along the unique
coordinate map recovers its characteristic function on `ℝ` by evaluating at `realToEuclidean1`. -/
private theorem charFun_map_euclidean1ToReal
    (μ : ProbabilityMeasure E1) (t : ℝ) :
    charFun
      (μ.map measurable_euclidean1ToReal.aemeasurable : Measure ℝ) t =
      charFun (μ : Measure E1) (realToEuclidean1 t) := by
  -- Proof comment: rewrite the pushforward characteristic function via `integral_map`,
  -- then identify the Euclidean inner product with the unique coordinate.
  change
    charFun (Measure.map euclidean1ToReal (μ : Measure E1)) t =
      charFun (μ : Measure E1) (realToEuclidean1 t)
  rw [MeasureTheory.charFun_apply_real, MeasureTheory.charFun_apply,
    MeasureTheory.integral_map
      measurable_euclidean1ToReal.aemeasurable (by fun_prop)]
  congr with x
  congr 1
  have hinner :
      inner ℝ x (realToEuclidean1 t) = t * euclidean1ToReal x := by
    simpa [euclidean1ToReal, realToEuclidean1] using
      (EuclideanSpace.inner_single_right (i := (0 : Fin 1)) t x)
  exact congrArg (fun z : ℂ ↦ z * Complex.I) (by exact_mod_cast hinner.symm)

/-- Helper for Theorem 16.6: scaling a probability-law intensity by a nonnegative real rate
turns the compound-Poisson characteristic function into the centered exponential form. -/
private theorem charFun_compoundPoissonMeasure_nonnegRateProbability
    (μ : ProbabilityMeasure ℝ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    charFun
      (compoundPoissonMeasure
        ((((Real.toNNReal a) : NNReal) • μ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ) t =
      Complex.exp ((a : ℂ) * (charFun (μ : Measure ℝ) t - 1)) := by
  have hintegrable :
      Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) (μ := (μ : Measure ℝ)) := by
    -- Proof comment: the Fourier kernel has constant norm `1`, so it is integrable against any
    -- probability law.
    refine Integrable.of_bound (by fun_prop) 1 ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      exact le_of_eq (by simpa using (Complex.norm_exp_ofReal_mul_I (t * x)))
  have hcentered :
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂(μ : Measure ℝ) =
        charFun (μ : Measure ℝ) t - 1 := by
    -- Proof comment: subtracting the constant `1` removes exactly the total mass of the
    -- probability law.
    rw [integral_sub hintegrable (integrable_const (1 : ℂ)), MeasureTheory.charFun_apply_real]
    simp
  rw [charFun_compoundPoissonMeasure]
  congr 1
  let c : ENNReal := (Real.toNNReal a : NNReal)
  change
    (∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂
      (((((Real.toNNReal a : NNReal) • μ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ))) =
        (a : ℂ) * (charFun (μ : Measure ℝ) t - 1)
  have hscaledMeasure :
      (((((Real.toNNReal a : NNReal) • μ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ)) =
        c • (μ : Measure ℝ) := by
    rfl
  rw [hscaledMeasure, integral_smul_measure, hcentered]
  change ((c.toReal : ℂ) * (charFun (μ : Measure ℝ) t - 1)) =
      (a : ℂ) * (charFun (μ : Measure ℝ) t - 1)
  simp [c, Real.toNNReal_of_nonneg ha]

/-- Helper for Theorem 16.6: for a natural rate `n`, the centered compound-Poisson exponential
attached to a characteristic function is again a characteristic function. -/
private theorem isCFP_natCompoundPoissonExponent
    {χ : ℝ → ℂ} (hχ : IsCFP χ) (n : ℕ) :
    IsCFP (fun t ↦ Complex.exp ((n : ℂ) * (χ t - 1))) := by
  rcases hχ with ⟨μ, hμ⟩
  refine ⟨compoundPoissonMeasure (((n : NNReal) • μ.toFiniteMeasure) : FiniteMeasure ℝ), ?_⟩
  funext t
  -- Proof comment: the specialized compound-Poisson law realizes the desired centered
  -- exponential characteristic function.
  simpa [hμ] using
    charFun_compoundPoissonMeasure_nonnegRateProbability (μ := μ) (a := n) (by positivity) t

/-- Helper for Theorem 16.6: after transporting the compound-Poisson approximants to `ℝ¹`, the
pointwise characteristic functions converge to the transported exponential limit. -/
private theorem tendsto_charFun_pushRealToEuclidean1_of_linearizedLimit
    {φs : ℕ → ℝ → ℂ} {ψ : ℝ → ℂ} {μs : ℕ → ProbabilityMeasure ℝ}
    (hμs :
      ∀ n : ℕ,
        charFun (μs n : Measure ℝ) =
          fun t ↦ Complex.exp (((n : ℂ) * (φs n t - 1))))
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (ψ t))) :
    ∀ x : E1,
      Tendsto (fun n ↦ charFun (pushRealToEuclidean1 (μs n) : Measure E1) x) atTop
        (𝓝 (Complex.exp (ψ (euclidean1ToReal x)))) := by
  intro x
  have hpoint :
      Tendsto
        (fun n : ℕ ↦ Complex.exp (((n : ℂ) * (φs n (euclidean1ToReal x) - 1))))
        atTop (𝓝 (Complex.exp (ψ (euclidean1ToReal x)))) := by
    -- Proof comment: the assumed linearized limit is stable under the continuous map `exp`.
    exact Complex.continuous_exp.continuousAt.tendsto.comp (hlin (euclidean1ToReal x))
  have hrewrite :
      (fun n ↦ charFun (pushRealToEuclidean1 (μs n) : Measure E1) x) =
        fun n : ℕ ↦ Complex.exp (((n : ℂ) * (φs n (euclidean1ToReal x) - 1))) := by
    funext n
    calc
      charFun (pushRealToEuclidean1 (μs n) : Measure E1) x
          = charFun (μs n : Measure ℝ) (euclidean1ToReal x) := by
              simpa using charFun_map_realToEuclidean1 (μ := μs n) x
      _ = Complex.exp (((n : ℂ) * (φs n (euclidean1ToReal x) - 1))) := by
            rw [hμs n]
  rw [hrewrite]
  exact hpoint

/-- Helper for Theorem 16.6: the linearized limit hypothesis produces a probability measure on
`ℝ¹` whose characteristic function is `x ↦ exp (ψ (euclidean1ToReal x))`. -/
private theorem existsEuclidean1ProbabilityMeasure_of_linearizedLimit
    {φs : ℕ → ℝ → ℂ} {ψ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (ψ t)))
    (hψ0 : ContinuousAt ψ 0) :
    ∃ Q : ProbabilityMeasure E1,
      ∀ x : E1, charFun (Q : Measure E1) x = Complex.exp (ψ (euclidean1ToReal x)) := by
  classical
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦
    Classical.choose (isCFP_natCompoundPoissonExponent (hχ := hφs n) n)
  have hμs :
      ∀ n : ℕ,
        charFun (μs n : Measure ℝ) =
          fun t ↦ Complex.exp (((n : ℂ) * (φs n t - 1))) := by
    intro n
    exact Classical.choose_spec (isCFP_natCompoundPoissonExponent (hχ := hφs n) n)
  let Ps : ℕ → ProbabilityMeasure E1 := fun n ↦ pushRealToEuclidean1 (μs n)
  have hchar :
      ∀ x : E1,
        Tendsto (fun n ↦ charFun (Ps n : Measure E1) x) atTop
          (𝓝 (Complex.exp (ψ (euclidean1ToReal x)))) :=
    tendsto_charFun_pushRealToEuclidean1_of_linearizedLimit hμs hlin
  have hψE0 :
      PartiallyContinuousAtZero (fun x : E1 ↦ Complex.exp (ψ (euclidean1ToReal x))) := by
    -- Proof comment: continuity at `0` survives composition with the continuous exponential map.
    refine
      (partiallyContinuousAtZero_comp_euclidean1ToReal
        (φ := fun t : ℝ ↦ Complex.exp (ψ t)) ?_)
    simpa using (Complex.continuous_exp.continuousAt.comp hψ0)
  rcases exists_probabilityMeasure_of_tendsto_charFun (d := 1) Ps hchar hψE0 with
    ⟨Q, hQchar, _⟩
  exact ⟨Q, hQchar⟩

/-- Helper for Theorem 16.6: if `n * (z n - 1)` converges in `ℂ`, then `z n ^ n` converges to
`exp` of the same limit. -/
private theorem pow_tendsto_exp_of_tendstoNatMulSubOne
    {z : ℕ → ℂ} {w : ℂ}
    (hz : Tendsto (fun n : ℕ ↦ (n : ℂ) * (z n - 1)) atTop (𝓝 w)) :
    Tendsto (fun n : ℕ ↦ z n ^ n) atTop (𝓝 (Complex.exp w)) := by
  -- Proof comment: rewrite `z n` as `1 + (z n - 1)` and apply the standard complex exponential
  -- asymptotic `(1 + g n)^n → exp w`.
  simpa using
    (Complex.tendsto_one_add_pow_exp_of_tendsto (g := fun n ↦ z n - 1) (t := w) hz)

/-- Helper for Theorem 16.6: the powered pointwise limit is itself a characteristic function. -/
private theorem cfpPowerLimit_limitIsCFP
    {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0) :
    IsCFP φ := by
  classical
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦ Classical.choose (hφs n)
  have hμs :
      ∀ n : ℕ, charFun (μs n : Measure ℝ) = φs n := by
    intro n
    exact Classical.choose_spec (hφs n)
  let νs : ℕ → ProbabilityMeasure ℝ := fun n ↦ μs n ^ n
  have hνs_apply :
      ∀ n : ℕ, ∀ t : ℝ, charFun (νs n : Measure ℝ) t = φs n t ^ n := by
    intro n t
    calc
      charFun (νs n : Measure ℝ) t = charFun (μs n : Measure ℝ) t ^ n := by
        simpa [νs] using
          congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow (μs n) n)
      _ = φs n t ^ n := by rw [hμs n]
  let Ps : ℕ → ProbabilityMeasure E1 := fun n ↦ pushRealToEuclidean1 (νs n)
  have hcharE1 :
      ∀ x : E1,
        Tendsto (fun n ↦ charFun (Ps n : Measure E1) x) atTop (𝓝 (φ (euclidean1ToReal x))) := by
    intro x
    have hcharReal := hpow (euclidean1ToReal x)
    have hrewrite :
        (fun n ↦ charFun (Ps n : Measure E1) x) =
          fun n : ℕ ↦ φs n (euclidean1ToReal x) ^ n := by
      funext n
      calc
        charFun (Ps n : Measure E1) x = charFun (νs n : Measure ℝ) (euclidean1ToReal x) := by
          simpa [Ps] using charFun_map_realToEuclidean1 (μ := νs n) x
        _ = φs n (euclidean1ToReal x) ^ n := by rw [hνs_apply n]
    rw [hrewrite]
    exact hcharReal
  have hφE0 :
      PartiallyContinuousAtZero (fun x : E1 ↦ φ (euclidean1ToReal x)) :=
    partiallyContinuousAtZero_comp_euclidean1ToReal hφ0
  rcases exists_probabilityMeasure_of_tendsto_charFun (d := 1) Ps hcharE1 hφE0 with
    ⟨Q, hQchar, _⟩
  refine ⟨Q.map measurable_euclidean1ToReal.aemeasurable, ?_⟩
  funext t
  -- Proof comment: read the unique coordinate of the limiting `ℝ¹` law to recover the real-line
  -- characteristic function `φ`.
  rw [charFun_map_euclidean1ToReal]
  simpa [realToEuclidean1, euclidean1ToReal] using hQchar (realToEuclidean1 t)

/-- Helper for Theorem 16.6: the powered characteristic functions converge uniformly on compact
sets. -/
private theorem cfpPowerLimit_tendstoUniformlyOnCompact
    {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0) :
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n s ↦ φs n s ^ n) φ atTop K := by
  classical
  let μs : ℕ → ProbabilityMeasure ℝ := fun n ↦ Classical.choose (hφs n)
  have hμs :
      ∀ n : ℕ, charFun (μs n : Measure ℝ) = φs n := by
    intro n
    exact Classical.choose_spec (hφs n)
  let νs : ℕ → ProbabilityMeasure ℝ := fun n ↦ μs n ^ n
  have hνs_apply :
      ∀ n : ℕ, ∀ t : ℝ, charFun (νs n : Measure ℝ) t = φs n t ^ n := by
    intro n t
    calc
      charFun (νs n : Measure ℝ) t = charFun (μs n : Measure ℝ) t ^ n := by
        simpa [νs] using
          congrArg (fun f : ℝ → ℂ ↦ f t) (ProbabilityMeasure.charFun_pow (μs n) n)
      _ = φs n t ^ n := by rw [hμs n]
  rcases cfpPowerLimit_limitIsCFP hφs hpow hφ0 with ⟨P, hPchar⟩
  have hνtendsto : Tendsto νs atTop (𝓝 P) := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 ?_
    intro t
    have hpowt := hpow t
    -- Proof comment: once the weak limit is identified by its characteristic function, Lévy's
    -- convergence criterion turns the powered pointwise limit into weak convergence.
    simpa [hνs_apply, hPchar] using hpowt
  intro K hK
  -- Proof comment: weak convergence of the powered witness laws upgrades their characteristic
  -- functions to compact-uniform convergence.
  simpa [hνs_apply, hPchar] using
    (charFun_tendstoUniformlyOn_of_tendstoReal (P := P) hνtendsto) K hK

/-- Helper for Theorem 16.6: near the origin, the powered-limit hypothesis yields a uniform bound
on the first-order modulus defect of the roots. -/
private theorem cfpPowerLimit_localModulusDefectBound
    {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0) :
    ∃ ε > 0, ∃ C > 0, ∀ n : ℕ+, ∀ s ∈ Set.Icc (-ε) ε,
      (n : ℝ) * (1 - ‖φs n s‖ ^ 2) ≤ C := by
  have hφone : φ 0 = 1 := by
    have hpow0 :
        Tendsto (fun n : ℕ ↦ (1 : ℂ)) atTop (𝓝 (φ 0)) := by
      refine Tendsto.congr' ?_ (hpow 0)
      exact Filter.Eventually.of_forall fun n ↦ by
        simp [zero_eq_one_of_isCFP (hφs n)]
    exact tendsto_nhds_unique hpow0 tendsto_const_nhds
  have hnear :
      {s : ℝ | φ s ∈ Metric.ball (φ 0) ((1 / 2 : ℝ))} ∈ 𝓝 (0 : ℝ) :=
    hφ0.tendsto.eventually (Metric.ball_mem_nhds (φ 0) (by norm_num))
  rcases Metric.mem_nhds_iff.mp hnear with ⟨δ, hδpos, hδsubset⟩
  let ε : ℝ := δ / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < δ := by
    dsimp [ε]
    linarith
  have hsmall :
      ∀ s ∈ Set.Icc (-ε) ε, (1 / 2 : ℝ) < ‖φ s‖ := by
    intro s hs
    have hsabs : |s| ≤ ε := by
      exact abs_le.mpr ⟨hs.1, hs.2⟩
    have hsball : s ∈ Metric.ball (0 : ℝ) δ := by
      change dist s 0 < δ
      simpa [Real.dist_eq] using lt_of_le_of_lt hsabs hεlt
    have hclose : ‖φ s - 1‖ < (1 / 2 : ℝ) := by
      have hsballφ : φ s ∈ Metric.ball (φ 0) ((1 / 2 : ℝ)) := hδsubset hsball
      simpa [Metric.mem_ball, dist_eq_norm, hφone] using hsballφ
    have hone_le : (1 : ℝ) ≤ ‖1 - φ s‖ + ‖φ s‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_add_le (1 - φ s) (φ s))
    have hclose' : ‖1 - φ s‖ < (1 / 2 : ℝ) := by
      simpa [norm_sub_rev] using hclose
    nlinarith
  have huni :=
    cfpPowerLimit_tendstoUniformlyOnCompact hφs hpow hφ0 (Set.Icc (-ε) ε) isCompact_Icc
  rw [Metric.tendstoUniformlyOn_iff] at huni
  have hcloseEventually :
      ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (-ε) ε,
        dist (φs n s ^ n) (φ s) < (1 / 4 : ℝ) := by
    simpa [ε, dist_comm] using huni (1 / 4) (by norm_num)
  rcases Filter.eventually_atTop.1 hcloseEventually with ⟨N, hN⟩
  let C : ℝ := max (N : ℝ) (-Real.log (1 / 16 : ℝ))
  have hCpos : 0 < C := by
    have hlogPos : 0 < -Real.log (1 / 16 : ℝ) := by
      exact neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
    exact lt_of_lt_of_le hlogPos (le_max_right _ _)
  refine ⟨ε, hεpos, C, hCpos, ?_⟩
  intro n s hs
  by_cases hlarge : N ≤ (n : ℕ)
  · have hclose := hN (n : ℕ) hlarge s hs
    have hnormSq_le_one : ‖φs n s‖ ^ 2 ≤ 1 := by
      have hnorm_le_one : ‖φs n s‖ ≤ 1 := norm_le_one_of_isCFP (hφs n) s
      have hnorm_nonneg : 0 ≤ ‖φs n s‖ := norm_nonneg _
      nlinarith [sq_nonneg (1 - ‖φs n s‖), hnorm_nonneg, hnorm_le_one]
    have hpowLower : (1 / 4 : ℝ) < ‖φs n s ^ (n : ℕ)‖ := by
      have hone_le :
          ‖φ s‖ ≤ ‖φ s - φs n s ^ (n : ℕ)‖ + ‖φs n s ^ (n : ℕ)‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (norm_add_le (φ s - φs n s ^ (n : ℕ)) (φs n s ^ (n : ℕ)))
      have hclose' : ‖φ s - φs n s ^ (n : ℕ)‖ < (1 / 4 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hclose
      have hφlower : (1 / 2 : ℝ) < ‖φ s‖ := hsmall s hs
      nlinarith
    have hpowSq_ge : (1 / 16 : ℝ) ≤ (‖φs n s‖ ^ 2) ^ (n : ℕ) := by
      have hsq : (1 / 16 : ℝ) < ‖φs n s ^ (n : ℕ)‖ ^ 2 := by
        nlinarith [hpowLower, sq_nonneg ‖φs n s ^ (n : ℕ)‖]
      calc
        (1 / 16 : ℝ) ≤ ‖φs n s ^ (n : ℕ)‖ ^ 2 := le_of_lt hsq
        _ = (‖φs n s‖ ^ 2) ^ (n : ℕ) := by
            calc
              ‖φs n s ^ (n : ℕ)‖ ^ 2 = (‖φs n s‖ ^ (n : ℕ)) ^ 2 := by rw [norm_pow]
              _ = ‖φs n s‖ ^ ((n : ℕ) * 2) := by rw [pow_mul]
              _ = ‖φs n s‖ ^ (2 * (n : ℕ)) := by rw [Nat.mul_comm]
              _ = (‖φs n s‖ ^ 2) ^ (n : ℕ) := by rw [pow_mul]
    -- Proof comment: on the small interval, compact-uniform convergence of the powered sequence
    -- forces the powered modulus away from `0`, which bounds the first-order defect.
    calc
      (n : ℝ) * (1 - ‖φs n s‖ ^ 2) ≤ -Real.log (1 / 16 : ℝ) := by
        exact natMulOneSub_le_negLog_of_pow_ge
          (by positivity) hnormSq_le_one (by norm_num) hpowSq_ge
      _ ≤ C := le_max_right _ _
  · have hnle : (n : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hlarge))
    have htriv :
        (n : ℝ) * (1 - ‖φs n s‖ ^ 2) ≤ (n : ℝ) := by
      have hnormSq_le_one : ‖φs n s‖ ^ 2 ≤ 1 := by
        have hnorm_le_one : ‖φs n s‖ ≤ 1 := norm_le_one_of_isCFP (hφs n) s
        have hnorm_nonneg : 0 ≤ ‖φs n s‖ := norm_nonneg _
        nlinarith [sq_nonneg (1 - ‖φs n s‖), hnorm_nonneg, hnorm_le_one]
      nlinarith
    calc
      (n : ℝ) * (1 - ‖φs n s‖ ^ 2) ≤ (n : ℝ) := htriv
      _ ≤ N := hnle
      _ ≤ C := le_max_left _ _

/-- Helper for Theorem 16.6: the powered pointwise limit never vanishes. -/
private theorem cfpPowerLimit_nonvanishing
    {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0) :
    ∀ t : ℝ, φ t ≠ 0 := by
  rcases cfpPowerLimit_localModulusDefectBound hφs hpow hφ0 with
    ⟨ε, hεpos, C, hCpos, hlocal⟩
  have hdyadic :
      ∀ k : ℕ, ∀ n : ℕ+, ∀ s ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε),
        (n : ℝ) * (1 - ‖φs n s‖ ^ 2) ≤ (4 ^ k : ℝ) * C := by
    intro k
    induction k with
    | zero =>
        intro n s hs
        simpa using hlocal n s (by simpa using hs)
    | succ k ih =>
        intro n s hs
        let u : ℝ := s / 2
        have hs_two : 2 * u = s := by
          dsimp [u]
          ring_nf
        have hpow2 : ((2 ^ (k + 1) : ℝ) * ε) = 2 * ((2 ^ k : ℝ) * ε) := by
          simp [pow_succ, mul_left_comm, mul_comm]
        have hu :
            u ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε) := by
          rw [hpow2] at hs
          constructor
          · have hsleft := hs.1
            dsimp [u]
            nlinarith
          · have hsright := hs.2
            dsimp [u]
            nlinarith
        have hdbl :
            1 - ‖φs n s‖ ^ 2 ≤ 4 * (1 - ‖φs n u‖ ^ 2) := by
          have hχ :=
            one_sub_re_isCFP_two_mul_le_four_mul (hχ := isCFP_mul_conj (hφs n)) u
          have hre_mul_conj (x : ℝ) :
              Complex.re (φs n x * star (φs n x)) = ‖φs n x‖ ^ 2 := by
            have hnormSq :
                φs n x * star (φs n x) = (Complex.normSq (φs n x) : ℂ) := by
              rw [mul_comm]
              simpa using (Complex.normSq_eq_conj_mul_self (z := φs n x)).symm
            rw [hnormSq, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
          -- Proof comment: apply the doubled-frequency defect inequality to the modulus-square
          -- characteristic function and rewrite it back to norms.
          have hχ' := hχ
          rw [hre_mul_conj, hre_mul_conj] at hχ'
          simpa [u, hs_two] using hχ'
        calc
          (n : ℝ) * (1 - ‖φs n s‖ ^ 2)
              ≤ (n : ℝ) * (4 * (1 - ‖φs n u‖ ^ 2)) := by
                  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
                  gcongr
          _ = 4 * ((n : ℝ) * (1 - ‖φs n u‖ ^ 2)) := by ring
          _ ≤ 4 * ((4 ^ k : ℝ) * C) := by
                have huBound := ih n u hu
                nlinarith
          _ = (4 ^ (k + 1) : ℝ) * C := by
                simp [pow_succ, mul_left_comm, mul_comm]
  intro t
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|t| / ε) (show (1 : ℝ) < 2 by norm_num)
  have htk : |t| ≤ (2 ^ k : ℝ) * ε := by
    have hk' : |t| / ε < (2 ^ k : ℝ) := by simpa using hk
    have := (div_lt_iff₀ hεpos).mp hk'
    exact le_of_lt (by simpa [mul_comm] using this)
  have htIcc : t ∈ Set.Icc (-((2 ^ k : ℝ) * ε)) ((2 ^ k : ℝ) * ε) := by
    simpa [abs_le] using htk
  have hbound_t :
      ∀ n : ℕ+, (n : ℝ) * (1 - ‖φs n t‖ ^ 2) ≤ (4 ^ k : ℝ) * C := by
    intro n
    exact hdyadic k n t htIcc
  obtain ⟨c, hcpos, hcEventually⟩ :=
    pNat_posLowerBound_of_natMulOneSub_le
      (C := (4 ^ k : ℝ) * C) hbound_t
  have hpowSqNat :
      Tendsto (fun n : ℕ ↦ ‖φs n t ^ n‖ ^ 2) atTop (𝓝 (‖φ t‖ ^ 2)) := by
    have hnorm : Tendsto (fun n : ℕ ↦ ‖φs n t ^ n‖) atTop (𝓝 ‖φ t‖) := (hpow t).norm
    simpa [pow_two] using hnorm.mul hnorm
  have hpowSq :
      Tendsto (fun n : ℕ+ ↦ ‖φs n t ^ (n : ℕ)‖ ^ 2) atTop (𝓝 (‖φ t‖ ^ 2)) := by
    simpa using hpowSqNat.comp tendsto_PNat_val_atTop_atTop
  have hpowEventually :
      ∀ᶠ n : ℕ+ in atTop, c ≤ ‖φs n t ^ (n : ℕ)‖ ^ 2 := by
    filter_upwards [hcEventually] with n hn
    have hpowSqEq :
        (‖φs n t‖ ^ 2) ^ (n : ℕ) = ‖φs n t ^ (n : ℕ)‖ ^ 2 := by
      calc
        (‖φs n t‖ ^ 2) ^ (n : ℕ) = ‖φs n t‖ ^ (2 * (n : ℕ)) := by rw [pow_mul]
        _ = ‖φs n t‖ ^ ((n : ℕ) * 2) := by rw [Nat.mul_comm]
        _ = (‖φs n t‖ ^ (n : ℕ)) ^ 2 := by rw [pow_mul]
        _ = ‖φs n t ^ (n : ℕ)‖ ^ 2 := by rw [norm_pow]
    simpa [hpowSqEq] using hn
  -- Proof comment: a positive eventual lower bound on the powered norms is incompatible with a
  -- zero limit, so the powered pointwise limit must stay away from `0`.
  exact fun hzero ↦ by
    have htoZero :
        Tendsto (fun n : ℕ+ ↦ ‖φs n t ^ (n : ℕ)‖ ^ 2) atTop (𝓝 0) := by
      simpa [hzero] using hpowSq
    have hsmallEventually :
        ∀ᶠ n : ℕ+ in atTop, ‖φs n t ^ (n : ℕ)‖ ^ 2 < c := by
      simpa [Metric.mem_ball, Real.dist_eq] using htoZero.eventually (Metric.ball_mem_nhds 0 hcpos)
    rcases (hpowEventually.and hsmallEventually).exists with ⟨n, hnle, hnlt⟩
    exact not_lt_of_ge hnle hnlt

/-- Helper for Theorem 16.6: on each compact segment `Set.uIcc 0 t`, the normalized powered
quotients `(φs n x)^n / φ x` converge uniformly to `1`. -/
private theorem segmentPowerQuotient_tendstoUniformlyOn_uIcc
    {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0)
    (hφne : ∀ t : ℝ, φ t ≠ 0) :
    ∀ t : ℝ,
      TendstoUniformlyOn
        (fun n x ↦ (φs n x ^ n) / φ x)
        (fun _ ↦ (1 : ℂ))
        atTop
        (Set.uIcc (0 : ℝ) t) := by
  intro t
  let A : Set ℝ := Set.uIcc (0 : ℝ) t
  have hACompact : IsCompact A := isCompact_uIcc
  have hφcfp : IsCFP φ := cfpPowerLimit_limitIsCFP hφs hpow hφ0
  have hφcont : Continuous φ := continuous_of_isCFP hφcfp
  have hnum :
      TendstoUniformlyOn (fun n x ↦ φs n x ^ n) φ atTop A :=
    cfpPowerLimit_tendstoUniformlyOnCompact hφs hpow hφ0 A hACompact
  have hnumLoc :
      TendstoLocallyUniformlyOn (fun n x ↦ φs n x ^ n) φ atTop A :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hACompact).2 hnum
  have hdenLoc :
      TendstoLocallyUniformlyOn (fun _ : ℕ => fun x : ℝ ↦ φ x) φ atTop A := by
    intro u hu x hx
    refine ⟨A, self_mem_nhdsWithin, ?_⟩
    exact Filter.Eventually.of_forall fun n y hy ↦ refl_mem_uniformity hu
  have hquotLoc :
      TendstoLocallyUniformlyOn
        (fun n x ↦ (φs n x ^ n) / φ x)
        (fun x ↦ φ x / φ x)
        atTop
        A :=
    hnumLoc.div₀ hdenLoc hφcont.continuousOn hφcont.continuousOn fun x hx ↦ hφne x
  -- Proof comment: after dividing by the nonvanishing limit on the compact segment, locally
  -- uniform convergence upgrades back to uniform convergence and the quotient simplifies to `1`.
  simpa [A, hφne] using
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hACompact).1 hquotLoc

/-- Helper for Theorem 16.6: on `Set.uIcc 0 t`, any continuous `n`th root of `exp ∘ H`
normalized at `0` is the divided exponential lift `exp (H / n)`. -/
private theorem segmentPowerRepresentationOn_uIcc
    {t : ℝ} {n : ℕ+} {χ : ℝ → ℂ} {H : C(Set.uIcc (0 : ℝ) t, ℂ)}
    (hχ : IsCFP χ)
    (hH0 : H ⟨0, by simp⟩ = 0)
    (hpow : ∀ x, Complex.exp (H x) = χ x ^ (n : ℕ)) :
    ∀ x : Set.uIcc (0 : ℝ) t, χ x = Complex.exp (H x / (n : ℂ)) := by
  intro x
  let A : Set ℝ := Set.uIcc (0 : ℝ) t
  letI : ContractibleSpace A := (convex_uIcc (0 : ℝ) t).contractibleSpace ⟨0, by simp⟩
  let T : Set ℂ := Set.range fun ζ : rootsOfUnity (n : ℕ) ℂ => ((ζ : Units ℂ) : ℂ)
  let q : A → ℂ := fun y ↦ χ y / Complex.exp (H y / (n : ℂ))
  have hqcont : Continuous q := by
    have hnum : Continuous fun y : A ↦ χ y := by
      simpa using (continuous_of_isCFP hχ).comp continuous_subtype_val
    have hden : Continuous fun y : A ↦ Complex.exp (H y / (n : ℂ)) := by
      simpa using Complex.continuous_exp.comp (H.continuous.div_const (n : ℂ))
    exact hnum.div hden fun y ↦ Complex.exp_ne_zero _
  have hqmaps : Set.MapsTo q (Set.univ : Set A) T := by
    intro y hy
    refine ⟨rootsOfUnity.mkOfPowEq (q y) ?_, ?_⟩
    · -- Proof comment: the quotient has `n`th power `1`, so it lands among the `n`th roots of
      -- unity.
      calc
        (q y) ^ (n : ℕ) =
            χ y ^ (n : ℕ) / (Complex.exp (H y / (n : ℂ))) ^ (n : ℕ) := by
              simp [q, div_pow]
        _ = Complex.exp (H y) / (Complex.exp (H y / (n : ℂ))) ^ (n : ℕ) := by
              rw [← hpow y]
        _ = Complex.exp (H y) / Complex.exp ((n : ℂ) * (H y / (n : ℂ))) := by
              rw [← Complex.exp_nat_mul]
        _ = Complex.exp (H y) / Complex.exp (H y) := by
              have hn0 : (n : ℂ) ≠ 0 := by
                exact_mod_cast (Nat.ne_of_gt n.pos)
              have hmul : (n : ℂ) * (H y / (n : ℂ)) = H y := by
                field_simp [hn0]
              rw [hmul]
        _ = 1 := by exact div_self (Complex.exp_ne_zero _)
    · simp [q]
  have hTdiscrete :
      IsDiscrete T := (Set.finite_range
        fun ζ : rootsOfUnity (n : ℕ) ℂ => ((ζ : Units ℂ) : ℂ)).isDiscrete
  have hconst : q x = q ⟨0, by simp [A]⟩ := by
    -- Proof comment: the interval subtype is contractible, hence preconnected, so a continuous
    -- map into the finite root-of-unity set is constant.
    exact isPreconnected_univ.constant_of_mapsTo hTdiscrete hqcont.continuousOn hqmaps
      (by simp) (by simp)
  have hqzero : q ⟨0, by simp [A]⟩ = 1 := by
    -- Proof comment: both the characteristic function and the divided exponential are normalized
    -- to `1` at the left endpoint.
    simp [q, hH0, zero_eq_one_of_isCFP hχ]
  have hqone : q x = 1 := hconst.trans hqzero
  have hden_ne : Complex.exp (H x / (n : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hmul :
      χ x = 1 * Complex.exp (H x / (n : ℂ)) := by
    exact (div_eq_iff hden_ne).mp (by simpa [q] using hqone)
  -- Proof comment: clearing the nonzero denominator recovers the root from the normalized lift.
  calc
    χ x = 1 * Complex.exp (H x / (n : ℂ)) := hmul
    _ = Complex.exp (H x / (n : ℂ)) := by simp

/-- Helper for Theorem 16.6: if `a n → w`, then the scaled exponential increments
`n * (exp (a n / n) - 1)` converge to `w`. -/
private theorem segmentPowerEndpointLog_tendstoOn_uIcc
    {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0)
    (hφne : ∀ t : ℝ, φ t ≠ 0)
    {Ψ : C(ℝ, ℂ)}
    (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = φ t) :
    ∀ t : ℝ,
      Tendsto (fun n : ℕ ↦ Ψ t + Complex.log ((φs n t ^ n) / φ t)) atTop (𝓝 (Ψ t)) ∧
        ∀ᶠ n : ℕ in atTop,
          0 < n ∧
            φs n t = Complex.exp ((Ψ t + Complex.log ((φs n t ^ n) / φ t)) / (n : ℂ)) := by
  intro t
  let A : Set ℝ := Set.uIcc (0 : ℝ) t
  have hφcfp : IsCFP φ := cfpPowerLimit_limitIsCFP hφs hpow hφ0
  have hφcont : Continuous φ := continuous_of_isCFP hφcfp
  have hφzero : φ 0 = 1 := zero_eq_one_of_isCFP hφcfp
  have hquot :
      TendstoUniformlyOn
        (fun n x ↦ (φs n x ^ n) / φ x)
        (fun _ ↦ (1 : ℂ))
        atTop
        A :=
    segmentPowerQuotient_tendstoUniformlyOn_uIcc hφs hpow hφ0 hφne t
  rw [Metric.tendstoUniformlyOn_iff] at hquot
  have hslitEventually :
      ∀ᶠ n : ℕ in atTop, ∀ x : A, (φs n x ^ n) / φ x ∈ Complex.slitPlane := by
    have honeClose :
        ∀ᶠ n : ℕ in atTop, ∀ x ∈ A, dist ((φs n x ^ n) / φ x) (1 : ℂ) < 1 := by
      simpa [dist_comm] using hquot 1 zero_lt_one
    filter_upwards [honeClose] with n hn x
    have hnorm : ‖(φs n x ^ n) / φ x - 1‖ < 1 := by
      simpa [dist_eq_norm] using hn x x.2
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      Complex.mem_slitPlane_of_norm_lt_one (z := (φs n x ^ n) / φ x - 1) hnorm
  have hquotEndpoint :
      Tendsto (fun n : ℕ ↦ (φs n t ^ n) / φ t) atTop (𝓝 (1 : ℂ)) := by
    have hraw :
        Tendsto (fun n : ℕ ↦ (φs n t ^ n) / φ t) atTop (𝓝 (φ t / φ t)) := by
      simpa using (hpow t).div tendsto_const_nhds (hφne t)
    simpa [hφne t] using hraw
  have hlogEndpoint :
      Tendsto (fun n : ℕ ↦ Complex.log ((φs n t ^ n) / φ t)) atTop (𝓝 0) := by
    simpa [Complex.log_one] using
      (Filter.Tendsto.clog hquotEndpoint (by simp : (1 : ℂ) ∈ Complex.slitPlane))
  have hendpoint :
      Tendsto (fun n : ℕ ↦ Ψ t + Complex.log ((φs n t ^ n) / φ t)) atTop (𝓝 (Ψ t)) := by
    -- Proof comment: the endpoint quotient tends to `1`, so its principal logarithm tends to `0`.
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ Ψ t) atTop (𝓝 (Ψ t))).add hlogEndpoint
  have hreprEventually :
      ∀ᶠ n : ℕ in atTop,
        0 < n ∧
          φs n t = Complex.exp ((Ψ t + Complex.log ((φs n t ^ n) / φ t)) / (n : ℂ)) := by
    filter_upwards [Filter.eventually_gt_atTop 0, hslitEventually] with n hnpos hslit
    let m : ℕ+ := ⟨n, hnpos⟩
    have hQcont : Continuous fun x : A ↦ (φs n x ^ n) / φ x := by
      have hnum : Continuous fun x : A ↦ φs n x ^ n := by
        simpa using ((continuous_of_isCFP (hφs n)).comp continuous_subtype_val).pow n
      have hden : Continuous fun x : A ↦ φ x := by
        simpa using hφcont.comp continuous_subtype_val
      exact hnum.div hden fun x ↦ hφne x
    let Q : C(A, ℂ) := ⟨fun x ↦ (φs n x ^ n) / φ x, hQcont⟩
    let L : C(A, ℂ) := ⟨fun x ↦ Complex.log (Q x), Q.continuous.clog hslit⟩
    let H : C(A, ℂ) := Ψ.restrict A + L
    have hH0 : H ⟨0, by simp [A]⟩ = 0 := by
      -- Proof comment: both the global lift and the quotient logarithm are normalized at the left
      -- endpoint of the interval.
      simp [H, L, Q, A, hΨ0, hφzero, zero_eq_one_of_isCFP (hφs n)]
    have hHexp : ∀ x, Complex.exp (H x) = φs n x ^ (m : ℕ) := by
      intro x
      have hQne : Q x ≠ 0 := Complex.slitPlane_ne_zero (hslit x)
      have hφx : φ x ≠ 0 := hφne x
      -- Proof comment: `H` adds the global logarithmic lift `Ψ` to the principal log of the
      -- quotient, so exponentiating `H` reconstructs the exact powered root datum.
      calc
        Complex.exp (H x) = Complex.exp (Ψ x + Complex.log (Q x)) := by
          simp [H, L]
        _ = Complex.exp (Ψ x) * Complex.exp (Complex.log (Q x)) := by
              rw [Complex.exp_add]
        _ = φ x * Q x := by
              rw [hΨexp x, Complex.exp_log hQne]
        _ = φ x * ((φs n x ^ n) / φ x) := by
              simp [Q]
        _ = φs n x ^ n := by
              field_simp [hφx]
        _ = φs n x ^ (m : ℕ) := by
              rfl
    have hrepr :=
      segmentPowerRepresentationOn_uIcc
        (t := t) (n := m) (χ := φs n) (H := H) (hχ := hφs n) hH0 hHexp ⟨t, by simp⟩
    refine ⟨hnpos, ?_⟩
    -- Proof comment: evaluate the interval root-recovery lemma at the right endpoint.
    simpa [A, H, L, Q, m] using hrepr
  exact ⟨hendpoint, hreprEventually⟩

/-- Helper for Theorem 16.6: if `a n → w`, then the scaled exponential increments
`n * (exp (a n / n) - 1)` converge to `w`. -/
private theorem natMul_expDivSubOne_tendsto
    {a : ℕ → ℂ} {w : ℂ}
    (ha : Tendsto a atTop (𝓝 w)) :
    Tendsto (fun n : ℕ ↦ (n : ℂ) * (Complex.exp (a n / (n : ℂ)) - 1)) atTop (𝓝 w) := by
  have hboundEventually : ∀ᶠ n : ℕ in atTop, ‖a n‖ ≤ ‖w‖ + 1 := by
    have hcloseEventually :
        ∀ᶠ n : ℕ in atTop, ‖a n - w‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using
        ha.eventually (Metric.ball_mem_nhds w zero_lt_one)
    filter_upwards [hcloseEventually] with n hn
    calc
      ‖a n‖ = ‖(a n - w) + w‖ := by ring_nf
      _ ≤ ‖a n - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + 1 := by nlinarith
  let N : ℕ := max 1 (Nat.ceil (‖w‖ + 1))
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖(n : ℂ) * (Complex.exp (a n / (n : ℂ)) - 1) - a n‖ ≤ (‖w‖ + 1) ^ 2 / n := by
    filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_gt_atTop 0, hboundEventually]
      with n hnN hn0 hna
    have hn0C : (n : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn0
    have hn0R : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn0
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast hn0
    have hwle : ‖w‖ + 1 ≤ n := by
      have hceil : ‖w‖ + 1 ≤ Nat.ceil (‖w‖ + 1) := Nat.le_ceil _
      have hceilN : (Nat.ceil (‖w‖ + 1) : ℝ) ≤ N := by
        exact_mod_cast le_max_right 1 (Nat.ceil (‖w‖ + 1))
      have hNn : (N : ℝ) ≤ n := by
        exact_mod_cast hnN
      exact le_trans hceil (le_trans hceilN hNn)
    have hnormDiv : ‖a n / (n : ℂ)‖ = ‖a n‖ / n := by
      rw [norm_div, Complex.norm_natCast]
    have hsmall : ‖a n / (n : ℂ)‖ ≤ 1 := by
      rw [hnormDiv]
      have hdiv :
          ‖a n‖ / (n : ℝ) ≤ (‖w‖ + 1) / n := by
        exact div_le_div_of_nonneg_right hna hnpos.le
      have hdiv' :
          (‖w‖ + 1) / (n : ℝ) ≤ (n : ℝ) / n := by
        exact div_le_div_of_nonneg_right hwle hnpos.le
      exact le_trans hdiv (by simpa [hn0R] using hdiv')
    have hrew :
        (n : ℂ) * (Complex.exp (a n / (n : ℂ)) - 1) - a n =
          (n : ℂ) * (Complex.exp (a n / (n : ℂ)) - 1 - a n / (n : ℂ)) := by
      field_simp [hn0C]
    have hstep :
        ‖(n : ℂ) * (Complex.exp (a n / (n : ℂ)) - 1) - a n‖ ≤ ‖a n‖ ^ 2 / n := by
      rw [hrew, norm_mul]
      calc
        ‖(n : ℂ)‖ * ‖Complex.exp (a n / (n : ℂ)) - 1 - a n / (n : ℂ)‖
            ≤ ‖(n : ℂ)‖ * ‖a n / (n : ℂ)‖ ^ 2 := by
              exact mul_le_mul_of_nonneg_left
                (Complex.norm_exp_sub_one_sub_id_le hsmall) (norm_nonneg _)
        _ = (n : ℝ) * (‖a n‖ / n) ^ 2 := by rw [Complex.norm_natCast, hnormDiv]
        _ = ‖a n‖ ^ 2 / n := by
              field_simp [hn0R]
    calc
      ‖(n : ℂ) * (Complex.exp (a n / (n : ℂ)) - 1) - a n‖ ≤ ‖a n‖ ^ 2 / n := hstep
      _ ≤ (‖w‖ + 1) ^ 2 / n := by
            have hsquare : ‖a n‖ ^ 2 ≤ (‖w‖ + 1) ^ 2 := by
              nlinarith [hna, norm_nonneg (a n)]
            exact div_le_div_of_nonneg_right hsquare hnpos.le
  have hzero :
      Tendsto (fun n : ℕ ↦ (‖w‖ + 1) ^ 2 / n) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (‖w‖ + 1) ^ 2) atTop
        (𝓝 ((‖w‖ + 1) ^ 2))).mul hinv
  have hdiff :
      Tendsto
        (fun n : ℕ ↦ ‖(n : ℂ) * (Complex.exp (a n / (n : ℂ)) - 1) - a n‖)
        atTop
        (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
      hbound hzero
  have hdiffZero :
      Tendsto
        (fun n : ℕ ↦ (n : ℂ) * (Complex.exp (a n / (n : ℂ)) - 1) - a n)
        atTop
        (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hdiff
  -- Proof comment: the exponential remainder is `o(1)` after scaling by `n`, so adding back the
  -- convergent main term `a n` gives the claimed limit.
  have hsum := hdiffZero.add ha
  simpa [zero_add] using hsum

/-- Helper for Theorem 16.6: once the powered limit is written as `exp ∘ Ψ`, the quotient-log
endpoint formula reduces the forward implication to the elementary exponential asymptotic. -/
private theorem linearizedLimit_of_powerLimit_and_continuousExpLift
    {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0)
    {Ψ : C(ℝ, ℂ)}
    (hΨ0 : Ψ 0 = 0)
    (hΨexp : ∀ t : ℝ, Complex.exp (Ψ t) = φ t) :
    ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (Ψ t)) := by
  have hφne : ∀ t : ℝ, φ t ≠ 0 := cfpPowerLimit_nonvanishing hφs hpow hφ0
  intro t
  rcases segmentPowerEndpointLog_tendstoOn_uIcc hφs hpow hφ0 hφne hΨ0 hΨexp t with
    ⟨ha, hreprEventually⟩
  have hscaled :
      Tendsto
        (fun n : ℕ ↦
          (n : ℂ) *
            (Complex.exp ((Ψ t + Complex.log ((φs n t ^ n) / φ t)) / (n : ℂ)) - 1))
        atTop
        (𝓝 (Ψ t)) :=
    natMul_expDivSubOne_tendsto ha
  have hEventuallyEq :
      ∀ᶠ n : ℕ in atTop,
        (n : ℂ) *
            (Complex.exp ((Ψ t + Complex.log ((φs n t ^ n) / φ t)) / (n : ℂ)) - 1) =
          (n : ℂ) * (φs n t - 1) := by
    filter_upwards [hreprEventually] with n hn
    rcases hn with ⟨_, hrepr⟩
    exact congrArg (fun z : ℂ ↦ (n : ℂ) * (z - 1)) hrepr.symm
  -- Proof comment: on the eventual tail where the exact endpoint representation holds, the
  -- sequence matches the exponential model handled by `natMul_expDivSubOne_tendsto`.
  exact Tendsto.congr' hEventuallyEq hscaled

/-- Theorem 16.6: for a sequence of CFPs on `ℝ`, existence of the powered pointwise limit
`φ t = lim_{n → ∞} φs n t ^ n` with `φ` continuous at `0` is equivalent to existence of the
linearized pointwise limit `ψ t = lim_{n → ∞} n (φs n t - 1)` with `ψ` continuous at `0`.
The companion theorems `cfp_power_limit_eq_cexp_linearized_limit` and
`cfp_power_limit_isCFP` record the source conclusion that, when both limits coexist,
`φ = exp ψ` and `φ` is again a characteristic function. -/
theorem cfp_power_limit_iff_linearized_limit
    {φs : ℕ → ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n)) :
    (∃ φ : ℝ → ℂ,
      (∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t))) ∧
        ContinuousAt φ 0) ↔
      ∃ ψ : ℝ → ℂ,
        (∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (ψ t))) ∧
          ContinuousAt ψ 0 := by
  constructor
  · rintro ⟨φ, hpow, hφ0⟩
    have hφcfp : IsCFP φ := cfpPowerLimit_limitIsCFP hφs hpow hφ0
    have hφcont : Continuous φ := continuous_of_isCFP hφcfp
    have hφzero : φ 0 = 1 := zero_eq_one_of_isCFP hφcfp
    have hφne : ∀ t : ℝ, φ t ≠ 0 := cfpPowerLimit_nonvanishing hφs hpow hφ0
    obtain ⟨Ψ, hΨ, _⟩ := existsUnique_continuousExpLift hφcont hφne hφzero
    rcases hΨ with ⟨hΨ0, hΨexp⟩
    refine ⟨fun t : ℝ ↦ Ψ t, ?_, ?_⟩
    · -- Route correction: the forward implication is now reduced to the last source-style step.
      -- The global powered limit has already been packaged as a zero-free CFP with logarithmic
      -- lift `Ψ`. The endpoint helper now absorbs the quotient-log path construction on
      -- `Set.uIcc 0 t`, so the closing step is the scalar asymptotic
      -- `n * (exp (a_n / n) - 1) → a_n`.
      exact linearizedLimit_of_powerLimit_and_continuousExpLift hφs hpow hφ0 hΨ0 hΨexp
    · -- Proof comment: the logarithmic lift is continuous, so its underlying function is
      -- continuous at `0`.
      simpa using Ψ.continuous.continuousAt
  · rintro ⟨ψ, hlin, hψ0⟩
    refine ⟨fun t : ℝ ↦ Complex.exp (ψ t), ?_, ?_⟩
    · intro t
      -- Proof comment: the scalar limit `(1 + g_n)^n → exp` upgrades the linearized hypothesis
      -- to the powered limit.
      exact pow_tendsto_exp_of_tendstoNatMulSubOne (z := fun n ↦ φs n t) (w := ψ t) (hlin t)
    · -- Proof comment: continuity at `0` is preserved by composition with `Complex.exp`.
      simpa using (Complex.continuous_exp.continuousAt.comp hψ0)

/-- Auxiliary theorem: when the powered and linearized limits coexist for the same CFP
sequence, the powered limit is `t ↦ exp (ψ t)`. -/
theorem cfp_power_limit_eq_cexp_linearized_limit
    {φs : ℕ → ℝ → ℂ} {φ ψ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0)
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (ψ t))) :
    φ = fun t : ℝ ↦ Complex.exp (ψ t) := by
  let _ := hφs
  let _ := hφ0
  funext t
  have hpowExp :
      Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (Complex.exp (ψ t))) :=
    pow_tendsto_exp_of_tendstoNatMulSubOne (z := fun n ↦ φs n t) (w := ψ t) (hlin t)
  -- Proof comment: the powered sequence has both limits, so uniqueness identifies them.
  exact tendsto_nhds_unique (hpow t) hpowExp

/-- Auxiliary theorem: under the linearized-limit hypothesis, the limit `t ↦ exp (ψ t)` is a
characteristic function on `ℝ`. -/
theorem cfp_linearized_limit_exponential_isCFP
    {φs : ℕ → ℝ → ℂ} {ψ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (ψ t)))
    (hψ0 : ContinuousAt ψ 0) :
    IsCFP (fun t : ℝ ↦ Complex.exp (ψ t)) := by
  rcases existsEuclidean1ProbabilityMeasure_of_linearizedLimit hφs hlin hψ0 with ⟨Q, hQchar⟩
  refine ⟨Q.map measurable_euclidean1ToReal.aemeasurable, ?_⟩
  funext t
  -- Proof comment: read the unique coordinate of the limiting law on `ℝ¹`.
  rw [charFun_map_euclidean1ToReal]
  simpa [realToEuclidean1, euclidean1ToReal] using hQchar (realToEuclidean1 t)

/-- Auxiliary theorem: if the powered and linearized limits coexist for the same CFP
sequence, then the powered limit `φ` is itself a characteristic function on `ℝ`. -/
theorem cfp_power_limit_isCFP
    {φs : ℕ → ℝ → ℂ} {φ ψ : ℝ → ℂ}
    (hφs : ∀ n : ℕ, IsCFP (φs n))
    (hpow : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ φs n t ^ n) atTop (𝓝 (φ t)))
    (hφ0 : ContinuousAt φ 0)
    (hlin : ∀ t : ℝ, Tendsto (fun n : ℕ ↦ (n : ℂ) * (φs n t - 1)) atTop (𝓝 (ψ t)))
    (hψ0 : ContinuousAt ψ 0) :
    IsCFP φ := by
  have hEq :
      φ = fun t : ℝ ↦ Complex.exp (ψ t) :=
    cfp_power_limit_eq_cexp_linearized_limit hφs hpow hφ0 hlin
  rw [hEq]
  -- Proof comment: the linearized-limit theorem already constructs the exponential limit as a
  -- characteristic function.
  exact cfp_linearized_limit_exponential_isCFP hφs hlin hψ0

end

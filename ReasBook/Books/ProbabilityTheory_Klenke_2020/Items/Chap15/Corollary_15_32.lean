/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_31

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

namespace MeasureTheory.Measure

/-- A law on `ℝ` has the textbook finite absolute-moment root-growth limit property if all of its
absolute moments are finite and the normalized nth roots of those absolute moments converge to a
finite real limit. -/
def HasFiniteAbsoluteMomentRootLimit (μ : Measure ℝ) : Prop :=
  (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ) ∧
    ∃ α : ℝ,
      Tendsto
        (fun n : ℕ ↦ ((n : ℝ)⁻¹) * Real.rpow (moment (fun x : ℝ ↦ |x|) n μ) (1 / (n : ℝ)))
        atTop (𝓝 α)

/-- Finite absolute-moment root-growth limit is exactly finiteness of all absolute moments together
with convergence of the normalized absolute-moment roots. -/
@[simp]
theorem hasFiniteAbsoluteMomentRootLimit_iff (μ : Measure ℝ) :
    Measure.HasFiniteAbsoluteMomentRootLimit μ ↔
      (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ) ∧
        ∃ α : ℝ,
          Tendsto
            (fun n : ℕ ↦
              ((n : ℝ)⁻¹) * Real.rpow (moment (fun x : ℝ ↦ |x|) n μ) (1 / (n : ℝ)))
            atTop (𝓝 α) := by
  rfl

/-- A law on `ℝ` is moment determinate if it is a probability measure, has genuine finite absolute
moments of every order, and every comparison probability law with the same finite moments is equal
to it. -/
def IsMomentDeterminate (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
    (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ) ∧
    ∀ ⦃ν : Measure ℝ⦄, IsProbabilityMeasure ν →
      (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν) →
      (∀ n : ℕ, moment id n μ = moment id n ν) →
      μ = ν

/-- Moment determinacy is exactly the conjunction of being a probability law, having all absolute
moments finite, and uniqueness among probability laws on `ℝ` with the same genuinely finite
moments. -/
@[simp]
theorem isMomentDeterminate_iff (μ : Measure ℝ) :
    Measure.IsMomentDeterminate μ ↔
      IsProbabilityMeasure μ ∧
        (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ) ∧
        ∀ ⦃ν : Measure ℝ⦄, IsProbabilityMeasure ν →
          (∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν) →
          (∀ n : ℕ, moment id n μ = moment id n ν) →
          μ = ν := by
  rfl

/-- A moment-determinate law has finite absolute moments of every order. -/
theorem IsMomentDeterminate.integrable_abs_pow {μ : Measure ℝ}
    (hμ : Measure.IsMomentDeterminate μ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n) μ :=
  hμ.2.1 n

/-- A moment-determinate law is equal to every probability law on `ℝ` with the same genuinely
finite moments. -/
theorem IsMomentDeterminate.eq_of_forall_moment_eq {μ ν : Measure ℝ}
    (hμ : Measure.IsMomentDeterminate μ) [IsProbabilityMeasure ν]
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_moments : ∀ n : ℕ, moment id n μ = moment id n ν) :
    μ = ν :=
  hμ.2.2 inferInstance hν_moments h_moments

end MeasureTheory.Measure

/-- A real random variable has the textbook finite absolute-moment root-growth limit property if
it is measurable and its law has the corresponding owner-level property. -/
def HasFiniteAbsoluteMomentRootLimit (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ Measure.HasFiniteAbsoluteMomentRootLimit (P.map X)

/-- The source-facing finite absolute-moment root-growth property is exactly measurability together
with the owner-level property of the pushforward law. -/
@[simp]
theorem hasFiniteAbsoluteMomentRootLimit_iff (P : Measure Ω) (X : Ω → ℝ) :
    HasFiniteAbsoluteMomentRootLimit P X ↔
      Measurable X ∧ Measure.HasFiniteAbsoluteMomentRootLimit (P.map X) := by
  rfl

/-- A real random variable is moment determinate if it is measurable and its law is moment
determinate. -/
def IsMomentDeterminate (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  Measurable X ∧ Measure.IsMomentDeterminate (P.map X)

/-- The source-facing moment-determinacy predicate is exactly measurability together with the
owner-level predicate on the pushforward law. -/
@[simp]
theorem isMomentDeterminate_iff (P : Measure Ω) (X : Ω → ℝ) :
    IsMomentDeterminate P X ↔ Measurable X ∧ Measure.IsMomentDeterminate (P.map X) := by
  rfl

private theorem integrable_abs_pow_map_iff (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X)
    (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n) (P.map X) ↔ Integrable (fun ω ↦ |X ω| ^ n) P := by
  simpa [Function.comp] using
    (integrable_map_measure
      (by
        fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ n) (P.map X))
      hX.aemeasurable)

private theorem moment_id_map_eq (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) (n : ℕ) :
    moment id n (P.map X) = moment X n P := by
  rw [moment, moment]
  simpa using
    (integral_map hX.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ x ^ n) (P.map X)))

/-- If `X` is moment determinate, then any other measurable real random variable with genuinely
finite absolute moments of every order and the same moments has the same law. -/
theorem IsMomentDeterminate.map_eq {P : Measure Ω} {X : Ω → ℝ} (hX_det : IsMomentDeterminate P X)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q] (Y : Ω' → ℝ)
    (hY : Measurable Y) (hY_moments : ∀ n : ℕ, Integrable (fun ω ↦ |Y ω| ^ n) Q)
    (h_moments : ∀ n : ℕ, moment X n P = moment Y n Q) :
    P.map X = Q.map Y := by
  rcases hX_det with ⟨hX, hPX_det⟩
  haveI : IsProbabilityMeasure (Q.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  exact hPX_det.eq_of_forall_moment_eq
    (fun n ↦ (integrable_abs_pow_map_iff Q hY n).2 (hY_moments n))
    (fun n ↦ by
      simpa [moment_id_map_eq P hX n, moment_id_map_eq Q hY n] using h_moments n)

/-- Helper for Corollary 15.32: even raw moments on `ℝ` agree with the corresponding even absolute
moments. -/
private theorem moment_even_eq_absMoment (η : Measure ℝ) (n : ℕ) :
    moment id (2 * n) η = moment (fun x : ℝ ↦ |x|) (2 * n) η := by
  -- Proof comment: the even power of a real number is unchanged by inserting an absolute value.
  rw [moment, moment]
  congr with x
  simpa [pow_mul] using congrArg (fun y : ℝ ↦ y ^ n) (sq_abs x)

/-- Helper for Corollary 15.32: scaled absolute-power integrals rewrite directly to scaled
absolute moments. -/
private theorem integral_scaledAbsPow_eq_scaledMoment
    (η : Measure ℝ) (t : ℝ) (n : ℕ) :
    ∫ x, (t ^ n / n.factorial) * |x| ^ n ∂η =
      t ^ n * moment (fun x : ℝ ↦ |x|) n η / n.factorial := by
  -- Proof comment: pull the deterministic scalar out of the integral and unfold `moment`.
  rw [integral_const_mul, moment]
  simp [Pi.pow_apply]
  ring

/-- Helper for Corollary 15.32: the complex-valued integral of `x^n` is the complex cast of the
`n`th raw moment. -/
private theorem complexIntegral_pow_eq_moment (η : Measure ℝ) (n : ℕ)
    (hη_moment : Integrable (fun x : ℝ ↦ |x| ^ n) η) :
    ∫ x, (x : ℂ) ^ n ∂η = (moment id n η : ℂ) := by
  -- Proof comment: cast the real power integral to `ℂ`; the integrability hypothesis supplies the
  -- real moment integral.
  have hpow : Integrable (fun x : ℝ ↦ x ^ n) η := by
    refine Integrable.mono' hη_moment ?_ ?_
    · fun_prop
    · filter_upwards with x
      simp [Real.norm_eq_abs, abs_pow]
  calc
    ∫ x, (x : ℂ) ^ n ∂η = ∫ x, ((x ^ n : ℝ) : ℂ) ∂η := by
      simp
    _ = (∫ x, x ^ n ∂η : ℝ) := by
      rw [integral_complex_ofReal]
    _ = (moment id n η : ℂ) := by
      rfl

/-- Helper for Corollary 15.32: exponential `|x|`-integrability at a positive rate makes the
characteristic function analytic on all of `ℝ`. -/
private theorem analyticOn_charFun_of_integrableExpAbs (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) (h_exp : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) μ) :
    AnalyticOn ℝ (charFun μ) Set.univ := by
  -- Route correction: compose the strip analyticity of `complexMGF id μ` with the linear map
  -- `x ↦ (x : ℂ) * I` instead of trying to transport analyticity along a separate restriction API.
  have ht_mem : t ∈ ProbabilityTheory.integrableExpSet id μ := by
    -- Proof comment: the positive phase `exp (t * x)` is pointwise dominated by `exp (t * |x|)`.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (le_abs_self x) ht.le
  have hneg_mem : -t ∈ ProbabilityTheory.integrableExpSet id μ := by
    -- Proof comment: the negative phase `exp (-t * x)` is also dominated by `exp (t * |x|)`.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      have hx : -x ≤ |x| := by simpa using (neg_le_abs x)
      have hmul := mul_le_mul_of_nonneg_left hx ht.le
      simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hzero_int : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
    -- Proof comment: convexity of the exponential-integrability interval puts the midpoint `0`
    -- strictly inside once both endpoints `-t` and `t` belong to it.
    have hstrip :
        Set.Ioo (-t) t ⊆ interior (ProbabilityTheory.integrableExpSet id μ) := by
      rw [isOpen_Ioo.subset_interior_iff]
      exact ProbabilityTheory.convex_integrableExpSet.Ioo_subset_of_mem_closure
        (subset_closure hneg_mem) (subset_closure ht_mem)
    exact hstrip <| by constructor <;> linarith
  intro s hs
  -- Proof comment: every imaginary-axis point has real part `0`, so the strip analyticity applies
  -- uniformly and we only need to compose with the analytic map `x ↦ (x : ℂ) * I`.
  have hz :
      (((s : ℂ) * Complex.I).re) ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
    simpa using hzero_int
  have hmgf :
      AnalyticAt ℂ (ProbabilityTheory.complexMGF id μ) ((s : ℂ) * Complex.I) :=
    ProbabilityTheory.analyticAt_complexMGF (X := id) (μ := μ) (z := (s : ℂ) * Complex.I) hz
  have haxis : AnalyticAt ℂ (fun z : ℂ ↦ z * Complex.I) s := by
    simpa using (analyticAt_id.mul analyticAt_const : AnalyticAt ℂ (fun z : ℂ ↦ z * Complex.I) s)
  have hcomp :
      AnalyticAt ℂ
        (ProbabilityTheory.complexMGF id μ ∘ fun z : ℂ ↦ z * Complex.I) s := by
    exact
      AnalyticAt.comp
        (g := ProbabilityTheory.complexMGF id μ)
        (f := fun z : ℂ ↦ z * Complex.I)
        hmgf haxis
  have hre :
      AnalyticAt ℝ
        (fun y : ℝ ↦ (ProbabilityTheory.complexMGF id μ ((y : ℂ) * Complex.I)).re) s := by
    simpa [Function.comp] using hcomp.re_ofReal
  have him :
      AnalyticAt ℝ
        (fun y : ℝ ↦ (ProbabilityTheory.complexMGF id μ ((y : ℂ) * Complex.I)).im) s := by
    simpa [Function.comp] using hcomp.im_ofReal
  have hpair :
      AnalyticAt ℝ
        (fun y : ℝ ↦
          ((ProbabilityTheory.complexMGF id μ ((y : ℂ) * Complex.I)).re,
            (ProbabilityTheory.complexMGF id μ ((y : ℂ) * Complex.I)).im)) s := by
    exact hre.prod him
  have hcompReal :
      AnalyticAt ℝ
        (ProbabilityTheory.complexMGF id μ ∘ fun y : ℝ ↦ (y : ℂ) * Complex.I) s := by
    simpa [Function.comp, Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using
      (Complex.equivRealProdCLM.symm.analyticAt _).comp hpair
  have hchar :
      (ProbabilityTheory.complexMGF id μ ∘ fun y : ℝ ↦ (y : ℂ) * Complex.I) = charFun μ := by
    funext y
    simpa [Function.comp] using (ProbabilityTheory.complexMGF_id_mul_I (μ := μ) y)
  simpa [hchar] using hcompReal

/-- Helper for Corollary 15.32: exponential `|x|`-integrability controls the hyperbolic cosine at
the same rate. -/
private theorem integrableCosh_of_integrableExpAbs
    (η : Measure ℝ) [IsProbabilityMeasure η] {t : ℝ} (ht : 0 < t)
    (h_exp : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) η) :
    Integrable (fun x : ℝ ↦ Real.cosh (t * x)) η := by
  have hpos : Integrable (fun x : ℝ ↦ Real.exp (t * x)) η := by
    -- Proof comment: the positive exponential phase is pointwise dominated by `exp (t * |x|)`.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self x) ht.le)
  have hneg : Integrable (fun x : ℝ ↦ Real.exp (-t * x)) η := by
    -- Proof comment: the reflected exponential phase is dominated in the same way.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      have hx : -x ≤ |x| := by simpa using (neg_le_abs x)
      have hmul := mul_le_mul_of_nonneg_left hx ht.le
      simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using Real.exp_le_exp.mpr hmul
  have hadd : Integrable (fun x : ℝ ↦ Real.exp (t * x) + Real.exp (-t * x)) η := hpos.add hneg
  -- Proof comment: rewrite `cosh` through its defining average of the two exponential phases.
  simpa [Real.cosh_eq] using hadd.div_const (2 : ℝ)

/-- Helper for Corollary 15.32: integrability of `cosh (t x)` controls the absolute exponential
phase at the same rate. -/
private theorem integrableExpAbs_of_integrableCosh
    (η : Measure ℝ) [IsProbabilityMeasure η] {t : ℝ}
    (ht : 0 ≤ t)
    (h_cosh : Integrable (fun x : ℝ ↦ Real.cosh (t * x)) η) :
    Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) η := by
  have htwo : Integrable (fun x : ℝ ↦ 2 * Real.cosh (t * x)) η := h_cosh.const_mul 2
  refine Integrable.mono' htwo ?_ ?_
  · fun_prop
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hexp := Real.exp_abs_le (t * x)
    have hcosh :
        Real.exp (t * x) + Real.exp (-(t * x)) = 2 * Real.cosh (t * x) := by
      rw [Real.cosh_eq]
      ring
    simpa [abs_mul, abs_of_nonneg ht, hcosh] using hexp

/-- Helper for Corollary 15.32: the even `cosh` partial sums are written directly in the
absolute-moment normal form. -/
private def coshEvenPartialSum (t : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range N) fun k ↦ (t ^ (2 * k) / (2 * k).factorial) * |x| ^ (2 * k)

/-- Helper for Corollary 15.32: matching even raw moments identifies every finite even `cosh`
partial sum under the two laws. -/
private theorem coshEvenPartialSum_integral_eq_of_sameMoments
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : ℝ)
    (hμ_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ)
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_moments : ∀ n : ℕ, moment id n μ = moment id n ν)
    (N : ℕ) :
    ∫ x, coshEvenPartialSum t N x ∂ν = ∫ x, coshEvenPartialSum t N x ∂μ := by
  -- Proof comment: rewrite each finite even-power coefficient as an absolute moment, then use the
  -- even raw-moment identities term by term.
  have hν_sum :
      ∫ x, coshEvenPartialSum t N x ∂ν =
        Finset.sum (Finset.range N) fun k ↦
          ∫ x, (t ^ (2 * k) / (2 * k).factorial) * |x| ^ (2 * k) ∂ν := by
    unfold coshEvenPartialSum
    exact
      integral_finset_sum _ fun k hk ↦
        (hν_moments (2 * k)).const_mul (t ^ (2 * k) / (2 * k).factorial)
  have hμ_sum :
      ∫ x, coshEvenPartialSum t N x ∂μ =
        Finset.sum (Finset.range N) fun k ↦
          ∫ x, (t ^ (2 * k) / (2 * k).factorial) * |x| ^ (2 * k) ∂μ := by
    unfold coshEvenPartialSum
    exact
      integral_finset_sum _ fun k hk ↦
        (hμ_moments (2 * k)).const_mul (t ^ (2 * k) / (2 * k).factorial)
  rw [hν_sum, hμ_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  calc
    ∫ x, (t ^ (2 * k) / (2 * k).factorial) * |x| ^ (2 * k) ∂ν =
        t ^ (2 * k) * moment (fun x : ℝ ↦ |x|) (2 * k) ν / (2 * k).factorial := by
          rw [integral_scaledAbsPow_eq_scaledMoment ν t (2 * k)]
    _ = t ^ (2 * k) * moment id (2 * k) ν / (2 * k).factorial := by
          rw [← moment_even_eq_absMoment ν k]
    _ = t ^ (2 * k) * moment id (2 * k) μ / (2 * k).factorial := by
          rw [(h_moments (2 * k)).symm]
    _ = t ^ (2 * k) * moment (fun x : ℝ ↦ |x|) (2 * k) μ / (2 * k).factorial := by
          rw [← moment_even_eq_absMoment μ k]
    _ = ∫ x, (t ^ (2 * k) / (2 * k).factorial) * |x| ^ (2 * k) ∂μ := by
          rw [integral_scaledAbsPow_eq_scaledMoment μ t (2 * k)]

/-- Helper for Corollary 15.32: equality of all moments transfers finiteness of the `cosh`
lower integral at a fixed positive rate. -/
private theorem lintegral_cosh_lt_top_of_sameMoments
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {t : ℝ} (ht : 0 < t)
    (h_exp : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) μ)
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_moments : ∀ n : ℕ, moment id n μ = moment id n ν) :
    ∫⁻ x, ENNReal.ofReal (Real.cosh (t * x)) ∂ν < ⊤ := by
  -- Route correction: keep the proof in the finite abs-power normal form and only pass to
  -- `lintegral` after the finite integral identities are established.
  have hμ_pos : Integrable (fun x : ℝ ↦ Real.exp (t * x)) μ := by
    -- Proof comment: the positive exponential phase is pointwise dominated by `exp (t * |x|)`.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self x) ht.le)
  have hμ_neg : Integrable (fun x : ℝ ↦ Real.exp (-t * x)) μ := by
    -- Proof comment: the reflected exponential phase is dominated in the same way.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      have hx : -x ≤ |x| := by simpa using (neg_le_abs x)
      have hmul := mul_le_mul_of_nonneg_left hx ht.le
      simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using Real.exp_le_exp.mpr hmul
  have hμ_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ := by
    -- Proof comment: the source exponential moment supplies all absolute moments of `μ`.
    intro n
    simpa using
      (ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul
        (μ := μ) (X := id) (t := t) ht.ne' hμ_pos hμ_neg n)
  have hμ_cosh : Integrable (fun x : ℝ ↦ Real.cosh (t * x)) μ :=
    integrableCosh_of_integrableExpAbs μ ht h_exp
  have hμ_cosh_nonneg :
      0 ≤ᵐ[μ] fun x : ℝ ↦ Real.cosh (t * x) := by
    filter_upwards with x
    positivity
  have hμ_cosh_lintegral :
      ∫⁻ x, ENNReal.ofReal (Real.cosh (t * x)) ∂μ < ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hμ_cosh hμ_cosh_nonneg]
    exact ENNReal.ofReal_lt_top
  have hpartial_meas :
      ∀ N : ℕ, AEMeasurable (fun x ↦ ENNReal.ofReal (coshEvenPartialSum t N x)) ν := by
    intro N
    refine (Measurable.ennreal_ofReal ?_).aemeasurable
    unfold coshEvenPartialSum
    fun_prop
  have hpartial_tendsto :
      ∀ x : ℝ, Tendsto (fun N : ℕ ↦ ENNReal.ofReal (coshEvenPartialSum t N x)) atTop
        (𝓝 (ENNReal.ofReal (Real.cosh (t * x)))) := by
    intro x
    have hsum :
        HasSum (fun k : ℕ ↦ (t * x) ^ (2 * k) / (2 * k).factorial) (Real.cosh (t * x)) :=
      Real.hasSum_cosh (t * x)
    have hpartial_eq :
        ∀ N : ℕ,
          coshEvenPartialSum t N x =
            Finset.sum (Finset.range N) fun k ↦ (t * x) ^ (2 * k) / (2 * k).factorial := by
      intro N
      unfold coshEvenPartialSum
      refine Finset.sum_congr rfl ?_
      intro k hk
      have habs : |x| ^ (2 * k) = x ^ (2 * k) := by
        simpa [pow_mul] using congrArg (fun y : ℝ ↦ y ^ k) (sq_abs x)
      have hfac : (((2 * k).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      rw [habs, mul_pow]
      field_simp [hfac]
    have hpartial_real :
        Tendsto
          (fun N : ℕ ↦
            Finset.sum (Finset.range N) fun k ↦ (t * x) ^ (2 * k) / (2 * k).factorial)
          atTop
          (𝓝 (Real.cosh (t * x))) :=
      hsum.tendsto_sum_nat
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    exact hpartial_real.congr' <| Filter.Eventually.of_forall fun N ↦ by rw [← hpartial_eq N]
  have hpartial_mono :
      ∀ᵐ x ∂ν, Monotone fun N : ℕ ↦ ENNReal.ofReal (coshEvenPartialSum t N x) := by
    filter_upwards with x
    intro N M hNM
    refine ENNReal.ofReal_le_ofReal ?_
    unfold coshEvenPartialSum
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hNM) ?_
    intro k hk hnot
    refine mul_nonneg ?_ ?_
    · exact div_nonneg (pow_nonneg ht.le _) (by positivity)
    · exact pow_nonneg (abs_nonneg x) _
  have hpartial_lintegral_tendsto :
      Tendsto (fun N : ℕ ↦ ∫⁻ x, ENNReal.ofReal (coshEvenPartialSum t N x) ∂ν) atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal (Real.cosh (t * x)) ∂ν)) := by
    refine MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
      hpartial_meas hpartial_mono ?_
    filter_upwards with x
    exact hpartial_tendsto x
  have hpartial_bound :
      ∀ N : ℕ,
        ∫⁻ x, ENNReal.ofReal (coshEvenPartialSum t N x) ∂ν ≤
          ∫⁻ x, ENNReal.ofReal (Real.cosh (t * x)) ∂μ := by
    intro N
    have hpartial_nonneg_ν :
        0 ≤ᵐ[ν] fun x : ℝ ↦ coshEvenPartialSum t N x := by
      filter_upwards with x
      unfold coshEvenPartialSum
      exact Finset.sum_nonneg fun k hk ↦
        mul_nonneg
          (div_nonneg (pow_nonneg ht.le _) (by positivity))
          (pow_nonneg (abs_nonneg x) _)
    have hpartial_nonneg_μ :
        0 ≤ᵐ[μ] fun x : ℝ ↦ coshEvenPartialSum t N x := by
      filter_upwards with x
      unfold coshEvenPartialSum
      exact Finset.sum_nonneg fun k hk ↦
        mul_nonneg
          (div_nonneg (pow_nonneg ht.le _) (by positivity))
          (pow_nonneg (abs_nonneg x) _)
    have hpartial_int_ν :
        Integrable (fun x : ℝ ↦ coshEvenPartialSum t N x) ν := by
      unfold coshEvenPartialSum
      refine integrable_finset_sum (Finset.range N) ?_
      intro k hk
      exact (hν_moments (2 * k)).const_mul (t ^ (2 * k) / (2 * k).factorial)
    have hpartial_int_μ :
        Integrable (fun x : ℝ ↦ coshEvenPartialSum t N x) μ := by
      unfold coshEvenPartialSum
      refine integrable_finset_sum (Finset.range N) ?_
      intro k hk
      exact (hμ_moments (2 * k)).const_mul (t ^ (2 * k) / (2 * k).factorial)
    have hle_pointwise :
        ∀ x : ℝ, coshEvenPartialSum t N x ≤ Real.cosh (t * x) := by
      intro x
      have hsum :
          HasSum (fun k : ℕ ↦ (t * x) ^ (2 * k) / (2 * k).factorial) (Real.cosh (t * x)) :=
        Real.hasSum_cosh (t * x)
      have hpartial_eq :
          coshEvenPartialSum t N x =
            Finset.sum (Finset.range N) fun k ↦ (t * x) ^ (2 * k) / (2 * k).factorial := by
        unfold coshEvenPartialSum
        refine Finset.sum_congr rfl ?_
        intro k hk
        have habs : |x| ^ (2 * k) = x ^ (2 * k) := by
          simpa [pow_mul] using congrArg (fun y : ℝ ↦ y ^ k) (sq_abs x)
        have hfac : (((2 * k).factorial : ℕ) : ℝ) ≠ 0 := by positivity
        rw [habs, mul_pow]
        field_simp [hfac]
      rw [hpartial_eq]
      calc
        Finset.sum (Finset.range N) (fun k ↦ (t * x) ^ (2 * k) / (2 * k).factorial) ≤
            ∑' k : ℕ, (t * x) ^ (2 * k) / (2 * k).factorial := by
              exact hsum.summable.sum_le_tsum _ fun k hk ↦ by
                refine div_nonneg ?_ (by positivity)
                rw [pow_mul]
                exact pow_nonneg (sq_nonneg (t * x)) k
        _ = Real.cosh (t * x) := by
              simpa using hsum.tsum_eq
    calc
      ∫⁻ x, ENNReal.ofReal (coshEvenPartialSum t N x) ∂ν =
          ENNReal.ofReal (∫ x, coshEvenPartialSum t N x ∂ν) := by
            exact
              (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpartial_int_ν
                hpartial_nonneg_ν).symm
      _ = ENNReal.ofReal (∫ x, coshEvenPartialSum t N x ∂μ) := by
            rw [coshEvenPartialSum_integral_eq_of_sameMoments
              μ ν t hμ_moments hν_moments h_moments N]
      _ = ∫⁻ x, ENNReal.ofReal (coshEvenPartialSum t N x) ∂μ := by
            exact
              MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpartial_int_μ
                hpartial_nonneg_μ
      _ ≤ ∫⁻ x, ENNReal.ofReal (Real.cosh (t * x)) ∂μ := by
            refine MeasureTheory.lintegral_mono fun x ↦ ?_
            exact ENNReal.ofReal_le_ofReal (hle_pointwise x)
  have hlimit_le :
      ∫⁻ x, ENNReal.ofReal (Real.cosh (t * x)) ∂ν ≤
        ∫⁻ x, ENNReal.ofReal (Real.cosh (t * x)) ∂μ := by
    exact le_of_tendsto hpartial_lintegral_tendsto (Eventually.of_forall hpartial_bound)
  exact lt_of_le_of_lt hlimit_le hμ_cosh_lintegral

/-- Helper for Corollary 15.32: a comparison probability law with the same raw moments as a law
with one exponential `|x|`-moment inherits a smaller exponential `|x|`-moment. -/
private theorem comparisonIntegrableExpAbs_of_sameMoments
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {t : ℝ} (ht : 0 < t)
    (h_exp : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) μ)
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_moments : ∀ n : ℕ, moment id n μ = moment id n ν) :
    ∃ s : ℝ, 0 < s ∧ Integrable (fun x : ℝ ↦ Real.exp (s * |x|)) ν := by
  -- Proof comment: first transfer finiteness of the `cosh` lower integral at the same rate, then
  -- convert that `cosh` integrability back to the absolute exponential phase.
  have h_cosh_lintegral :
      ∫⁻ x, ENNReal.ofReal (Real.cosh (t * x)) ∂ν < ⊤ :=
    lintegral_cosh_lt_top_of_sameMoments μ ν ht h_exp hν_moments h_moments
  have h_cosh_nonneg :
      0 ≤ᵐ[ν] fun x : ℝ ↦ Real.cosh (t * x) := by
    filter_upwards with x
    positivity
  have h_cosh_int : Integrable (fun x : ℝ ↦ Real.cosh (t * x)) ν := by
    exact
      (lintegral_ofReal_ne_top_iff_integrable
        (by fun_prop) h_cosh_nonneg).1 (ne_of_lt h_cosh_lintegral)
  exact ⟨t, ht, integrableExpAbs_of_integrableCosh ν ht.le h_cosh_int⟩

/-- Helper for Corollary 15.32: inside the interval `(-t,t)`, the owner-level exponential
integrability at rate `t` dominates the smaller absolute phase `exp |h x|`. -/
private theorem integrableExpAbs_of_mem_Ioo
    (η : Measure ℝ) [IsProbabilityMeasure η] {t h : ℝ} (ht : 0 < t)
    (hh : h ∈ Set.Ioo (-t) t)
    (h_exp : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) η) :
    Integrable (fun x : ℝ ↦ Real.exp |h * x|) η := by
  have ht_pos : Integrable (fun x : ℝ ↦ Real.exp (t * x)) η := by
    -- Proof comment: the positive phase is pointwise dominated by the absolute-value exponential.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self x) ht.le)
  have ht_neg : Integrable (fun x : ℝ ↦ Real.exp (-t * x)) η := by
    -- Proof comment: the negative phase is dominated in the same way, using `-x ≤ |x|`.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      have hx : -x ≤ |x| := by simpa using (neg_le_abs x)
      have hmul := mul_le_mul_of_nonneg_left hx ht.le
      simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using Real.exp_le_exp.mpr hmul
  have hh_abs : |h| ≤ |t| := by
    have hht : |h| < t := by
      rw [abs_lt]
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    simpa [abs_of_pos ht] using le_of_lt hht
  have hh_pos : Integrable (fun x : ℝ ↦ Real.exp (h * x)) η :=
    ProbabilityTheory.integrable_exp_mul_of_abs_le (μ := η) (X := id) ht_pos ht_neg hh_abs
  have hh_neg : Integrable (fun x : ℝ ↦ Real.exp (-h * x)) η := by
    refine ProbabilityTheory.integrable_exp_mul_of_abs_le (μ := η) (X := id) ht_pos ht_neg ?_
    simpa [abs_neg] using hh_abs
  -- Proof comment: combine the two one-sided phases to recover the absolute-value exponential.
  simpa [abs_mul] using
    (ProbabilityTheory.integrable_exp_abs_mul_abs (μ := η) (X := id) (t := h) hh_pos hh_neg)

/-- Helper for Corollary 15.32: these are the centered Taylor partial sums from Theorem 15.31 at
basepoint `0`, written for a fixed real increment `h`. -/
private def charFunMomentPartialSum (h : ℝ) (η : Measure ℝ) (n : ℕ) : ℂ :=
  Finset.sum (Finset.range n) fun k ↦
    (((Complex.I * (h : ℂ)) ^ k) / (k.factorial : ℂ)) *
      ∫ x, (x : ℂ) ^ k ∂η

/-- Helper for Corollary 15.32: if two probability laws have the same raw moments and both admit
an exponential `|x|`-moment at the same rate, then their characteristic functions agree on the
corresponding open interval around `0`. -/
private theorem charFun_eqOn_Ioo_of_sameMoments_and_integrableExpAbs
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {t : ℝ} (ht : 0 < t)
    (hμ_exp : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) μ)
    (hν_exp : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) ν)
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_moments : ∀ n : ℕ, moment id n μ = moment id n ν) :
    Set.EqOn (charFun μ) (charFun ν) (Set.Ioo (-t) t) := by
  intro h hh
  by_cases hh0 : h = 0
  · -- Proof comment: both characteristic functions take the value `1` at the origin.
    have hμ_zero : charFun μ 0 = 1 := by
      simpa using (MeasureTheory.charFun_zero μ)
    have hν_zero : charFun ν 0 = 1 := by
      simpa using (MeasureTheory.charFun_zero ν)
    simpa [hh0] using hμ_zero.trans hν_zero.symm
  have hμ_exp_h : Integrable (fun x : ℝ ↦ Real.exp |h * x|) μ :=
    integrableExpAbs_of_mem_Ioo μ ht hh hμ_exp
  have hν_exp_h : Integrable (fun x : ℝ ↦ Real.exp |h * x|) ν :=
    integrableExpAbs_of_mem_Ioo ν ht hh hν_exp
  have hμ_pos_h : Integrable (fun x : ℝ ↦ Real.exp (h * x)) μ := by
    -- Proof comment: `exp (h x)` is dominated by the absolute phase `exp |h x|`.
    refine Integrable.mono' hμ_exp_h ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (le_abs_self (h * x))
  have hμ_neg_h : Integrable (fun x : ℝ ↦ Real.exp (-h * x)) μ := by
    -- Proof comment: the same domination handles the reflected phase.
    refine Integrable.mono' hμ_exp_h ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      simpa [neg_mul] using Real.exp_le_exp.mpr (le_abs_self (-(h * x)))
  have hμ_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ := by
    -- Proof comment: one nontrivial local exponential moment gives all absolute moments of `μ`.
    intro n
    simpa using
      (ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul
        (μ := μ) (X := id) (t := h) hh0 hμ_pos_h hμ_neg_h n)
  have hpartial_eq : ∀ n : ℕ, charFunMomentPartialSum h μ n = charFunMomentPartialSum h ν n := by
    intro n
    -- Proof comment: at center `0`, each Taylor coefficient is exactly the corresponding raw
    -- moment, so the two finite partial sums match term by term.
    unfold charFunMomentPartialSum
    refine Finset.sum_congr rfl ?_
    intro k hk
    congr 1
    calc
      ∫ x, (x : ℂ) ^ k ∂μ = (moment id k μ : ℂ) := by
        exact complexIntegral_pow_eq_moment μ k (hμ_moments k)
      _ = (moment id k ν : ℂ) := by
        exact congrArg (fun r : ℝ ↦ (r : ℂ)) (h_moments k)
      _ = ∫ x, (x : ℂ) ^ k ∂ν := by
        symm
        exact complexIntegral_pow_eq_moment ν k (hν_moments k)
  have hμ_tend :
      Filter.Tendsto (charFunMomentPartialSum h μ) Filter.atTop (𝓝 (charFun μ h)) := by
    simpa [charFunMomentPartialSum] using
      (charFun_tendsto_partialSums_of_integrable_exp_abs (μ := μ) (t := 0) (h := h) hμ_exp_h)
  have hseq : charFunMomentPartialSum h μ = charFunMomentPartialSum h ν := by
    funext n
    exact hpartial_eq n
  have hν_tend :
      Filter.Tendsto (charFunMomentPartialSum h μ) Filter.atTop (𝓝 (charFun ν h)) := by
    simpa [hseq, charFunMomentPartialSum] using
      (charFun_tendsto_partialSums_of_integrable_exp_abs (μ := ν) (t := 0) (h := h) hν_exp_h)
  -- Proof comment: the shared Taylor partial sums have a unique limit in `ℂ`.
  exact tendsto_nhds_unique hμ_tend hν_tend

/-- Helper for Corollary 15.32: absolute moments are nonnegative because the integrand `|x|^n`
is pointwise nonnegative. -/
private theorem moment_abs_nonneg (μ : Measure ℝ) (n : ℕ) :
    0 ≤ moment (fun x : ℝ ↦ |x|) n μ := by
  -- Proof comment: unfold `moment` and integrate the nonnegative absolute-power function.
  rw [moment]
  exact integral_nonneg_of_ae (ae_of_all _ fun x ↦ pow_nonneg (abs_nonneg x) n)

/-- Helper for Corollary 15.32: the convergent normalized absolute-moment roots eventually satisfy
a linear bound in `n`. -/
private theorem eventuallyMomentRootLe_mul_of_hasFiniteAbsoluteMomentRootLimit
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Measure.HasFiniteAbsoluteMomentRootLimit μ) :
    ∃ D : ℝ,
      0 < D ∧
        ∀ᶠ n in Filter.atTop,
          1 ≤ n ∧
            Real.rpow (moment (fun x : ℝ ↦ |x|) n μ) (1 / (n : ℝ)) ≤ D * n := by
  rcases hμ.2 with ⟨α, hα⟩
  let D : ℝ := max (|α| + 1) 1
  let rootSeq : ℕ → ℝ := fun n ↦
    ((n : ℝ)⁻¹) * Real.rpow (moment (fun x : ℝ ↦ |x|) n μ) (1 / (n : ℝ))
  refine ⟨D, ?_, ?_⟩
  · -- Proof comment: the explicit choice `D = max (|α| + 1) 1` is strictly positive.
    dsimp [D]
    positivity
  · have hclose :
        ∀ᶠ n in Filter.atTop, |rootSeq n - α| < 1 := by
      simpa [rootSeq, Metric.ball, Real.dist_eq] using hα (Metric.ball_mem_nhds α zero_lt_one)
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hclose] with n hn hnear
    constructor
    · exact hn
    · have hnormalized :
          rootSeq n ≤ D := by
        have hα_le : α + 1 ≤ |α| + 1 := by
          nlinarith [le_abs_self α]
        have hUpper : rootSeq n ≤ α + 1 := by
          have hnear' := abs_lt.mp hnear
          nlinarith [hnear'.2]
        calc
          rootSeq n ≤ α + 1 := hUpper
          _ ≤ |α| + 1 := hα_le
          _ ≤ D := le_max_left _ _
      have hmul :=
        mul_le_mul_of_nonneg_left hnormalized (show 0 ≤ (n : ℝ) by positivity)
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      simpa [rootSeq, D, hn0, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Corollary 15.32: Stirling's lower bound implies
`(n : ℝ)^n / n.factorial ≤ (Real.exp 1)^n` for every `n ≥ 1`. -/
private theorem powDivFactorial_le_expNat {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ n / n.factorial ≤ (Real.exp 1) ^ n := by
  have hsqrt_ge_one : 1 ≤ Real.sqrt (2 * Real.pi * n : ℝ) := by
    refine Real.one_le_sqrt.mpr ?_
    have hpi : 1 < Real.pi := by
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

/-- Helper for Corollary 15.32: a linear bound on the absolute-moment root controls the
corresponding exponential-series coefficient. -/
private theorem expMomentCoeffLe_expRate_of_rootBound {a D t : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hD : 0 ≤ D) (ht : 0 ≤ t) (hn : 1 ≤ n)
    (hroot : Real.rpow a (1 / (n : ℝ)) ≤ D * n) :
    t ^ n * a / n.factorial ≤ (t * D * Real.exp 1) ^ n := by
  have hn0 : n ≠ 0 := by omega
  have hfac_nonneg : 0 ≤ ((n.factorial : ℕ) : ℝ) := by positivity
  have hroot_nonneg : 0 ≤ Real.rpow a (1 / (n : ℝ)) := Real.rpow_nonneg ha _
  have hpow : (Real.rpow a (1 / (n : ℝ))) ^ n = a := by
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

/-- Helper for Corollary 15.32: the root-limit hypothesis yields summability of the scaled
absolute-moment exponential series. -/
private theorem existsPosSummableScaledAbsMomentSeries_of_hasFiniteAbsoluteMomentRootLimit
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Measure.HasFiniteAbsoluteMomentRootLimit μ) :
    ∃ t : ℝ,
      0 < t ∧ Summable (fun n : ℕ ↦ t ^ n * moment (fun x : ℝ ↦ |x|) n μ / n.factorial) := by
  rcases eventuallyMomentRootLe_mul_of_hasFiniteAbsoluteMomentRootLimit μ hμ with
    ⟨D, hD_pos, hDtail⟩
  let t : ℝ := (2 * D * Real.exp 1)⁻¹
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have hRate : t * D * Real.exp 1 = (1 / 2 : ℝ) := by
    -- Proof comment: the explicit reciprocal choice fixes the geometric tail ratio at `1/2`.
    dsimp [t]
    have hExp : Real.exp 1 ≠ 0 := by positivity
    field_simp [hD_pos.ne', hExp]
  have hcoeff_nonneg :
      ∀ n : ℕ, 0 ≤ t ^ n * moment (fun x : ℝ ↦ |x|) n μ / n.factorial := by
    intro n
    exact
      div_nonneg
        (mul_nonneg (pow_nonneg ht_pos.le _) (moment_abs_nonneg μ n))
        (by positivity)
  have htail :
      ∀ᶠ n in Filter.atTop,
        t ^ n * moment (fun x : ℝ ↦ |x|) n μ / n.factorial ≤ (1 / 2 : ℝ) ^ n := by
    filter_upwards [hDtail] with n hn
    rcases hn with ⟨hn1, hroot⟩
    have hCoeff :=
      expMomentCoeffLe_expRate_of_rootBound
        (moment_abs_nonneg μ n) hD_pos.le ht_pos.le hn1 hroot
    simpa [hRate] using hCoeff
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htail
  have hgeom : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) := by
    exact summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hgeomShift : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + N)) := by
    exact (_root_.summable_nat_add_iff N).2 hgeom
  have htailSummable :
      Summable
        (fun n : ℕ ↦
          t ^ (n + N) * moment (fun x : ℝ ↦ |x|) (n + N) μ / (n + N).factorial) := by
    -- Proof comment: compare the shifted coefficient tail against the geometric majorant.
    refine Summable.of_nonneg_of_le (fun n ↦ hcoeff_nonneg (n + N)) ?_ hgeomShift
    intro n
    exact hN (n + N) (Nat.le_add_left N n)
  refine ⟨t, ht_pos, ?_⟩
  -- Proof comment: summability of a shifted tail is equivalent to summability of the full series.
  exact (_root_.summable_nat_add_iff N).1 htailSummable

/-- Helper for Corollary 15.32: the absolute exponential phase is its power series with scaled
absolute-power coefficients. -/
private theorem exp_mul_abs_eq_tsum_scaledAbsPowers (t x : ℝ) :
    Real.exp (t * |x|) = ∑' n : ℕ, (t ^ n / n.factorial) * |x| ^ n := by
  have hExp :
      Real.exp (t * |x|) = ∑' n : ℕ, (t * |x|) ^ n / n.factorial := by
    simpa [Real.exp_eq_exp_ℝ] using
      congrArg (fun f : ℝ → ℝ ↦ f (t * |x|))
        (NormedSpace.exp_eq_tsum_div :
          NormedSpace.exp = fun y : ℝ ↦ ∑' n : ℕ, y ^ n / n.factorial)
  refine hExp.trans ?_
  refine tsum_congr fun n ↦ ?_
  rw [mul_pow]
  ring

/-- Helper for Corollary 15.32: applying `ENNReal.ofReal` to the absolute exponential series keeps
the same coefficient shape because every term is nonnegative. -/
private theorem ennreal_ofReal_exp_mul_abs_eq_tsum_scaledAbsPowers (t x : ℝ) (ht : 0 ≤ t) :
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

/-- Helper for Corollary 15.32: the root-limit hypothesis should yield one positive exponential
absolute moment. -/
private theorem existsPosIntegrableExpAbs_of_hasFiniteAbsoluteMomentRootLimit
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Measure.HasFiniteAbsoluteMomentRootLimit μ) :
    ∃ t : ℝ, 0 < t ∧ Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) μ := by
  -- Proof comment: first show the coefficient series is summable, then integrate the nonnegative
  -- exponential power series term by term in `ENNReal`.
  rcases existsPosSummableScaledAbsMomentSeries_of_hasFiniteAbsoluteMomentRootLimit μ hμ with
    ⟨t, ht, hsum⟩
  have hterm_meas :
      ∀ n : ℕ, AEMeasurable (fun x ↦ ENNReal.ofReal ((t ^ n / n.factorial) * |x| ^ n)) μ := by
    intro n
    fun_prop
  have hcoeff_nonneg :
      ∀ n : ℕ, 0 ≤ t ^ n * moment (fun x : ℝ ↦ |x|) n μ / n.factorial := by
    intro n
    exact
      div_nonneg
        (mul_nonneg (pow_nonneg ht.le _) (moment_abs_nonneg μ n))
        (by positivity)
  have hterm_lintegral :
      ∀ n : ℕ,
        ∫⁻ x, ENNReal.ofReal ((t ^ n / n.factorial) * |x| ^ n) ∂μ =
          ENNReal.ofReal (t ^ n * moment (fun x : ℝ ↦ |x|) n μ / n.factorial) := by
    intro n
    have hterm_nonneg :
        0 ≤ᵐ[μ] fun x : ℝ ↦ (t ^ n / n.factorial) * |x| ^ n := by
      filter_upwards with x
      exact
        mul_nonneg
          (div_nonneg (pow_nonneg ht.le _) (by positivity))
          (pow_nonneg (abs_nonneg x) _)
    have hterm_int :
        Integrable (fun x : ℝ ↦ (t ^ n / n.factorial) * |x| ^ n) μ :=
      (hμ.1 n).const_mul (t ^ n / n.factorial)
    calc
      ∫⁻ x, ENNReal.ofReal ((t ^ n / n.factorial) * |x| ^ n) ∂μ =
          ENNReal.ofReal (∫ x, (t ^ n / n.factorial) * |x| ^ n ∂μ) := by
            exact
              (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hterm_int
                hterm_nonneg).symm
      _ = ENNReal.ofReal
            (t ^ n * moment (fun x : ℝ ↦ |x|) n μ / n.factorial) := by
            rw [integral_scaledAbsPow_eq_scaledMoment μ t n]
  have hseries_lt_top :
      ∫⁻ x, ∑' n : ℕ, ENNReal.ofReal ((t ^ n / n.factorial) * |x| ^ n) ∂μ < ⊤ := by
    calc
      ∫⁻ x, ∑' n : ℕ, ENNReal.ofReal ((t ^ n / n.factorial) * |x| ^ n) ∂μ =
          ∑' n : ℕ, ∫⁻ x, ENNReal.ofReal ((t ^ n / n.factorial) * |x| ^ n) ∂μ := by
        rw [MeasureTheory.lintegral_tsum hterm_meas]
      _ = ∑' n : ℕ, ENNReal.ofReal (t ^ n * moment (fun x : ℝ ↦ |x|) n μ / n.factorial) := by
        refine tsum_congr fun n ↦ hterm_lintegral n
      _ = ENNReal.ofReal
            (∑' n : ℕ, t ^ n * moment (fun x : ℝ ↦ |x|) n μ / n.factorial) := by
            symm
            exact ENNReal.ofReal_tsum_of_nonneg hcoeff_nonneg hsum
      _ < ⊤ := by
        exact ENNReal.ofReal_lt_top
  have hseries_eq :
      (fun x : ℝ ↦ ENNReal.ofReal (Real.exp (t * |x|))) =
        fun x ↦ ∑' n : ℕ, ENNReal.ofReal ((t ^ n / n.factorial) * |x| ^ n) := by
    funext x
    simpa using ennreal_ofReal_exp_mul_abs_eq_tsum_scaledAbsPowers t x ht.le
  have hlintegral_lt_top :
      ∫⁻ x, ENNReal.ofReal (Real.exp (t * |x|)) ∂μ < ⊤ := by
    simpa [hseries_eq] using hseries_lt_top
  have hnonneg :
      0 ≤ᵐ[μ] fun x : ℝ ↦ Real.exp (t * |x|) := by
    filter_upwards with x
    exact (Real.exp_pos _).le
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (t * |x|)) μ := by
    fun_prop
  exact
    ⟨t, ht,
      (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).1
        (ne_of_lt hlintegral_lt_top)⟩

/-- Exponential integrability of `|x|` under a probability law implies the method-of-moments
conclusion for that law. -/
-- Proof sketch: exponential integrability of `|x|` gives an open neighborhood of `0` inside the
-- owner interval `integrableExpSet id μ`, hence finite absolute moments of every order and the
-- required absolute-moment root-growth control. The main method-of-moments theorem then applies.
theorem method_of_moments_of_integrable_exp_abs (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) (h_exp : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) μ) :
    AnalyticOn ℝ (charFun μ) Set.univ ∧ Measure.IsMomentDeterminate μ := by
  -- Route correction: the analytic half is already stable via the complex-mgf strip. The remaining
  -- work is the comparison-law transfer of a smaller exponential `|x|`-moment.
  refine ⟨analyticOn_charFun_of_integrableExpAbs μ ht h_exp, ?_⟩
  have hμ_pos : Integrable (fun x : ℝ ↦ Real.exp (t * x)) μ := by
    -- Proof comment: the positive exponential phase is dominated by the absolute-value phase.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self x) ht.le)
  have hμ_neg : Integrable (fun x : ℝ ↦ Real.exp (-t * x)) μ := by
    -- Proof comment: the reflected phase is dominated in the same way.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      have hx : -x ≤ |x| := by simpa using (neg_le_abs x)
      have hmul := mul_le_mul_of_nonneg_left hx ht.le
      simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using Real.exp_le_exp.mpr hmul
  have hμ_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) μ := by
    -- Proof comment: one nontrivial exponential `|x|`-moment yields all absolute moments.
    intro n
    simpa using
      (ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul
        (μ := μ) (X := id) (t := t) ht.ne' hμ_pos hμ_neg n)
  refine ⟨inferInstance, hμ_moments, ?_⟩
  intro ν hν_prob hν_moments h_moments
  letI : IsProbabilityMeasure ν := hν_prob
  rcases
      comparisonIntegrableExpAbs_of_sameMoments μ ν ht h_exp hν_moments h_moments with
    ⟨s, hs, hν_exp_s⟩
  let r : ℝ := min t s
  have hr : 0 < r := lt_min ht hs
  have hμ_exp_r : Integrable (fun x : ℝ ↦ Real.exp (r * |x|)) μ := by
    -- Proof comment: shrink the original exponential rate from `t` to the common interval radius
    -- `r = min t s`.
    refine Integrable.mono' h_exp ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg x))
  have hν_exp_r : Integrable (fun x : ℝ ↦ Real.exp (r * |x|)) ν := by
    -- Proof comment: the transferred exponential moment also dominates all smaller rates.
    refine Integrable.mono' hν_exp_s ?_ ?_
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg x))
  have hchar_local :
      Set.EqOn (charFun μ) (charFun ν) (Set.Ioo (-r) r) :=
    charFun_eqOn_Ioo_of_sameMoments_and_integrableExpAbs
      μ ν hr hμ_exp_r hν_exp_r hν_moments h_moments
  have hμ_analyticNhd : AnalyticOnNhd ℝ (charFun μ) Set.univ := by
    exact
      (isOpen_univ.analyticOn_iff_analyticOnNhd).1
        (analyticOn_charFun_of_integrableExpAbs μ ht h_exp)
  have hν_analyticNhd : AnalyticOnNhd ℝ (charFun ν) Set.univ := by
    exact
      (isOpen_univ.analyticOn_iff_analyticOnNhd).1
        (analyticOn_charFun_of_integrableExpAbs ν hr hν_exp_r)
  have hfreq :
      ∃ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), charFun μ x = charFun ν x := by
    have hIoo : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), x ∈ Set.Ioo (-r) r :=
      mem_nhdsWithin_of_mem_nhds <| isOpen_Ioo.mem_nhds <| by constructor <;> linarith
    have hEq :
        ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), charFun μ x = charFun ν x := by
      filter_upwards [hIoo] with x hx
      exact hchar_local hx
    exact Filter.Eventually.frequently hEq
  have hchar_global : Set.EqOn (charFun μ) (charFun ν) Set.univ := by
    -- Proof comment: equality on a punctured neighborhood of the origin extends to all of `ℝ`
    -- because both characteristic functions are real-analytic everywhere.
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hμ_analyticNhd hν_analyticNhd
      isPreconnected_univ (z₀ := (0 : ℝ)) ?_ hfreq
    simp
  -- Proof comment: global equality of characteristic functions identifies the two probability
  -- measures.
  exact Measure.ext_of_charFun <| funext fun x ↦ by
    simpa using hchar_global (by simp : x ∈ Set.univ)

/-- Corollary 15.32: if a probability law on `ℝ` has finite absolute moments of every order and
the normalized nth roots of those absolute moments converge to a finite limit, then its
characteristic function is analytic on `ℝ` and the law is determined by its moments among
probability laws with genuinely finite absolute moments of every order. -/
-- Proof sketch: use the moment-growth hypothesis to obtain a nontrivial analytic neighborhood for
-- the complex moment-generating function, identify the characteristic function on the imaginary
-- axis, and then apply analytic continuation together with `Measure.ext_of_charFun` to recover the
-- law from its moments.
theorem method_of_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Measure.HasFiniteAbsoluteMomentRootLimit μ) :
    AnalyticOn ℝ (charFun μ) Set.univ ∧ Measure.IsMomentDeterminate μ := by
  -- Proof comment: once the root-limit hypothesis yields one positive exponential `|x|`-moment,
  -- the exponential-moment version of the theorem applies directly.
  rcases existsPosIntegrableExpAbs_of_hasFiniteAbsoluteMomentRootLimit μ hμ with ⟨t, ht, h_exp⟩
  exact method_of_moments_of_integrable_exp_abs μ ht h_exp

/-- Source-facing bridge for Corollary 15.32: if a real random variable has the root-growth
property, then its characteristic function is analytic on `ℝ` and its law is moment determinate. -/
theorem method_of_moments_map (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasFiniteAbsoluteMomentRootLimit P X) :
    AnalyticOn ℝ (charFun (P.map X)) Set.univ ∧ IsMomentDeterminate P X := by
  rcases hX with ⟨hX, hPX⟩
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  exact ⟨(method_of_moments (P.map X) hPX).1, hX, (method_of_moments (P.map X) hPX).2⟩

/-- Source-facing bridge: exponential integrability of `|X|` implies the method-of-moments
conclusion for the law of `X`. -/
theorem method_of_moments_of_integrable_exp_abs_map (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) {t : ℝ} (ht : 0 < t)
    (h_exp : Integrable (fun ω ↦ Real.exp (t * |X ω|)) P) :
    AnalyticOn ℝ (charFun (P.map X)) Set.univ ∧ IsMomentDeterminate P X := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have h_exp_map : Integrable (fun x : ℝ ↦ Real.exp (t * |x|)) (P.map X) := by
    simpa [Function.comp] using
      (integrable_map_measure
        (by
          fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (t * |x|)) (P.map X))
        hX.aemeasurable).2 h_exp
  exact
    ⟨(method_of_moments_of_integrable_exp_abs (P.map X) ht h_exp_map).1,
      hX,
      (method_of_moments_of_integrable_exp_abs (P.map X) ht h_exp_map).2⟩

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Theorem_23_17

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- Helper for Remark 23.18: the positive-parameter filter is nontrivial because right-sided
neighborhoods of `0` contain positive real numbers. -/
private instance positiveParameterFilter_neBot :
    NeBot (positiveParameterFilter : Filter PositiveParameter) := by
  -- Proof comment: `positiveParameterFilter` is the pullback of `𝓝[>] 0` along the subtype
  -- coercion, and that right-neighborhood filter is nontrivial.
  rw [positiveParameterFilter]
  exact (show NeBot (𝓝[>] (0 : ℝ)) from inferInstance).comap_of_range_mem (by
    simpa [PositiveParameter, Subtype.range_coe] using
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)))

/-- Helper for Remark 23.18: restricting to the tail `{x | M ≤ φ x}` is dominated by the full
Laplace functional for the shifted amplified potential `x ↦ α * φ x - (α - 1) * M`. -/
private theorem tailLaplaceFunctional_le_shiftedMoment
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (hφ : Measurable φ)
    {α : ℝ} (hα : 1 < α) (M : ℝ) (ε : PositiveParameter) :
    varadhanTailLaplaceFunctional μ φ M ε ≤
      varadhanLaplaceFunctional μ (fun x ↦ α * φ x - (α - 1) * M) ε := by
  have hTailSet : MeasurableSet {x | M ≤ φ x} := hφ measurableSet_Ici
  have hα1 : 0 < α - 1 := sub_pos.mpr hα
  -- Proof comment: rewrite the restricted integral as an indicator integral and dominate the
  -- integrand pointwise on and off the tail set.
  rw [varadhanTailLaplaceFunctional_def, varadhanLaplaceFunctional_def]
  rw [← lintegral_indicator hTailSet]
  refine lintegral_mono fun x ↦ ?_
  by_cases hx : M ≤ φ x
  · have hLinear : φ x ≤ α * φ x - (α - 1) * M := by
      nlinarith [hx, hα1]
    have hDiv : φ x / (ε : ℝ) ≤ (α * φ x - (α - 1) * M) / (ε : ℝ) := by
      exact (div_le_div_iff_of_pos_right ε.2).2 hLinear
    simp [hx, ENNReal.ofReal_le_ofReal, Real.exp_le_exp.mpr hDiv]
  · have hx' : ¬ x ∈ {x | M ≤ φ x} := hx
    simp [hx']

/-- Helper for Remark 23.18: subtracting a constant from the potential pulls out the exponential
factor `exp (-c / ε)` from the Laplace functional. -/
private theorem laplaceFunctional_sub_const_eq
    (μ : PositiveProbabilityFamily E) (ψ : E → ℝ) (c : ℝ) (ε : PositiveParameter) :
    varadhanLaplaceFunctional μ (fun x ↦ ψ x - c) ε =
      ENNReal.ofReal (Real.exp (-c / (ε : ℝ))) * varadhanLaplaceFunctional μ ψ ε := by
  have hε0 : (ε : ℝ) ≠ 0 := ne_of_gt ε.2
  have hPointwise :
      ∀ x : E,
        ENNReal.ofReal (Real.exp ((ψ x - c) / (ε : ℝ))) =
          ENNReal.ofReal (Real.exp (-c / (ε : ℝ))) *
            ENNReal.ofReal (Real.exp (ψ x / (ε : ℝ))) := by
    intro x
    have hSplit : (ψ x - c) / (ε : ℝ) = -c / (ε : ℝ) + ψ x / (ε : ℝ) := by
      field_simp [hε0]
      ring
    -- Proof comment: the exponential of the shifted exponent factors into the constant weight and
    -- the original Laplace integrand.
    rw [hSplit, Real.exp_add, ← ENNReal.ofReal_mul (by positivity)]
  -- Proof comment: after the pointwise factorization, move the constant factor outside the
  -- `lintegral`.
  calc
    varadhanLaplaceFunctional μ (fun x ↦ ψ x - c) ε
      = ∫⁻ x, ENNReal.ofReal (Real.exp (-c / (ε : ℝ))) *
          ENNReal.ofReal (Real.exp (ψ x / (ε : ℝ))) ∂(μ ε : Measure E) := by
            rw [varadhanLaplaceFunctional_def]
            refine lintegral_congr_ae ?_
            exact Filter.Eventually.of_forall hPointwise
    _ = ENNReal.ofReal (Real.exp (-c / (ε : ℝ))) *
          ∫⁻ x, ENNReal.ofReal (Real.exp (ψ x / (ε : ℝ))) ∂(μ ε : Measure E) := by
            rw [lintegral_const_mul' _ _ (by simp)]
    _ = ENNReal.ofReal (Real.exp (-c / (ε : ℝ))) * varadhanLaplaceFunctional μ ψ ε := by
          rw [varadhanLaplaceFunctional_def]

/-- Helper for Remark 23.18: the scaled logarithmic tail exponent is bounded by the affine shift
coming from the amplified moment exponent. -/
private theorem tailLaplaceExponent_le_affineMomentExponent
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (hφ : Measurable φ)
    {α : ℝ} (hα : 1 < α) (M : ℝ) (ε : PositiveParameter) :
    ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M ε) ≤
      (-((α - 1) * M) : EReal) +
        ((ε : ℝ) : EReal) *
          ENNReal.log (varadhanLaplaceFunctional μ (fun x ↦ α * φ x) ε) := by
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hTailLog :
      ENNReal.log (varadhanTailLaplaceFunctional μ φ M ε) ≤
        ENNReal.log
          (varadhanLaplaceFunctional μ (fun x ↦ α * φ x - (α - 1) * M) ε) := by
    exact ENNReal.log_le_log <|
      tailLaplaceFunctional_le_shiftedMoment
        (μ := μ) (φ := φ) hφ hα M ε
  have hMul :
      ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M ε) ≤
        ((ε : ℝ) : EReal) *
          ENNReal.log
            (varadhanLaplaceFunctional μ (fun x ↦ α * φ x - (α - 1) * M) ε) := by
    exact mul_le_mul_of_nonneg_left hTailLog hε
  have hcancel :
      (ε : ℝ) * (-((α - 1) * M) / (ε : ℝ)) = -((α - 1) * M) := by
    field_simp [show (ε : ℝ) ≠ 0 by exact ne_of_gt ε.2]
  have hFirstTerm :
      ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp (-((α - 1) * M) / (ε : ℝ)))) =
        (-((α - 1) * M) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), ← EReal.coe_mul, Real.log_exp]
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hcancel
  -- Proof comment: rewrite the shifted Laplace functional by separating the constant shift and
  -- then take logarithms.
  calc
    ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M ε)
      ≤ ((ε : ℝ) : EReal) *
          ENNReal.log
            (varadhanLaplaceFunctional μ (fun x ↦ α * φ x - (α - 1) * M) ε) := hMul
    _ = ((ε : ℝ) : EReal) *
          ENNReal.log
            (ENNReal.ofReal (Real.exp (-((α - 1) * M) / (ε : ℝ))) *
              varadhanLaplaceFunctional μ (fun x ↦ α * φ x) ε) := by
            rw [laplaceFunctional_sub_const_eq
              (μ := μ) (ψ := fun x ↦ α * φ x) ((α - 1) * M) ε]
    _ = ((ε : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal (Real.exp (-((α - 1) * M) / (ε : ℝ)))) +
            ((ε : ℝ) : EReal) *
              ENNReal.log (varadhanLaplaceFunctional μ (fun x ↦ α * φ x) ε) := by
            rw [ENNReal.log_mul_add, EReal.left_distrib_of_nonneg_of_ne_top hε (by simp)]
    _ = (-((α - 1) * M) : EReal) +
          ((ε : ℝ) : EReal) *
            ENNReal.log (varadhanLaplaceFunctional μ (fun x ↦ α * φ x) ε) := by
          rw [hFirstTerm]

/-- Helper for Remark 23.18: every extended real value below `⊤` admits a strictly larger real
upper bound. -/
private theorem exists_real_upper_bound_of_lt_top {x : EReal} (hx : x < ⊤) :
    ∃ C : ℝ, x < C := by
  by_cases hbot : x = ⊥
  · refine ⟨0, ?_⟩
    simp [hbot]
  · refine ⟨x.toReal + 1, ?_⟩
    have htop : x ≠ ⊤ := by
      intro htop
      simp [htop] at hx
    -- Proof comment: once `x` is neither `⊥` nor `⊤`, rewrite it as the coercion of `x.toReal`
    -- and add one.
    have hlt :
        ((x.toReal : ℝ) : EReal) < ((x.toReal + 1 : ℝ) : EReal) := by
      exact_mod_cast (by linarith : x.toReal < x.toReal + 1)
    simpa [EReal.coe_toReal htop hbot] using hlt

-- Mathlib recall: `Continuous.borel_measurable` supplies the inherited measurable bridge from
-- Theorem 23.17, but the standalone implication below only needs `Measurable φ` on its public
-- surface so that later proofs can treat the cutoffs `{x | M ≤ φ x}` measurably.
/-- Remark 23.18: if `φ` is measurable and there exists
`α > 1` such that
`limsup_{ε→0+} ε log ∫ exp (α φ / ε) dμ_ε < ∞`, then the tail condition
`inf_{M > 0} limsup_{ε→0+} ε log ∫ exp (φ / ε) 𝟙_{ {φ ≥ M} } dμ_ε = -∞` from Varadhan's lemma
holds. -/
theorem varadhan_tail_condition_of_moment_condition
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (hφ : Measurable φ)
    (hmoment :
      ∃ α > 1,
        Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log
              (varadhanLaplaceFunctional μ (fun x ↦ α * φ x) ε))
          positiveParameterFilter < ⊤) :
    sInf (Set.range fun M : {M : ℝ // 0 < M} ↦
      Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M.1 ε))
        positiveParameterFilter) = (⊥ : EReal) := by
  rcases hmoment with ⟨α, hα, hMomentTop⟩
  let momentExponent : PositiveParameter → EReal := fun ε ↦
    ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ (fun x ↦ α * φ x) ε)
  let B : EReal := Filter.limsup momentExponent positiveParameterFilter
  have hα1 : 0 < α - 1 := sub_pos.mpr hα
  have hTailLimsup :
      ∀ M : ℝ,
        Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M ε))
            positiveParameterFilter ≤
          (-((α - 1) * M) : EReal) + B := by
    intro M
    let c : EReal := ((-((α - 1) * M) : ℝ) : EReal)
    have hPointwise :
        ∀ ε : PositiveParameter,
          ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M ε) ≤
            c + momentExponent ε := by
      intro ε
      simpa [momentExponent, c] using
        tailLaplaceExponent_le_affineMomentExponent
          (μ := μ) (φ := φ) hφ hα M ε
    have hPointwiseLimsup :
        Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M ε))
            positiveParameterFilter ≤
          Filter.limsup
            (fun ε : PositiveParameter ↦ c + momentExponent ε)
            positiveParameterFilter := by
      exact Filter.limsup_le_limsup (Filter.Eventually.of_forall hPointwise)
    have hAddLimsup :
        Filter.limsup (fun ε : PositiveParameter ↦ c + momentExponent ε) positiveParameterFilter ≤
          c + B := by
      have hConstLimsupBot :
          Filter.limsup (fun _ : PositiveParameter ↦ c) positiveParameterFilter ≠ ⊥ := by
        simpa [Filter.limsup_const, c] using
          (EReal.coe_ne_bot (-((α - 1) * M)))
      have hConstLimsupTop :
          Filter.limsup (fun _ : PositiveParameter ↦ c) positiveParameterFilter ≠ ⊤ := by
        simpa [Filter.limsup_const, c] using
          (EReal.coe_ne_top (-((α - 1) * M)))
      simpa [B, Filter.limsup_const] using
        (EReal.limsup_add_le
          (u := fun _ : PositiveParameter ↦ c)
          (v := momentExponent) (f := positiveParameterFilter)
          (Or.inl hConstLimsupBot) (Or.inl hConstLimsupTop))
    simpa [c] using hPointwiseLimsup.trans hAddLimsup
  have hCup : ∃ C : ℝ, B < C := exists_real_upper_bound_of_lt_top (x := B) hMomentTop
  -- Proof comment: every real threshold is beaten by some positive cutoff `M`, because the
  -- affine upper bound `-((α - 1) * M) + B` tends to `-∞` as `M → ∞`.
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  rcases hCup with ⟨C, hBC⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (C - y) / (α - 1) < n := exists_nat_gt ((C - y) / (α - 1))
  let M : {M : ℝ // 0 < M} := ⟨n + 1, by positivity⟩
  have hMbound : (C - y) / (α - 1) < M.1 := by
    change (C - y) / (α - 1) < ((n : ℝ) + 1)
    exact lt_trans hn (by exact_mod_cast Nat.lt_succ_self n)
  have hAffine_lt : (-((α - 1) * M.1) : EReal) + C < y := by
    have hAffineReal : -((α - 1) * M.1) + C < y := by
      have hMul : C - y < (α - 1) * M.1 := by
        have hMul' : C - y < M.1 * (α - 1) := by
          exact (div_lt_iff₀ hα1).1 hMbound
        simpa [mul_comm] using hMul'
      linarith
    exact_mod_cast hAffineReal
  have hTailLt :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M.1 ε))
          positiveParameterFilter < y := by
    refine lt_of_le_of_lt (hTailLimsup M.1) ?_
    exact lt_trans (EReal.add_lt_add_left_coe hBC (-((α - 1) * M.1))) hAffine_lt
  exact lt_of_le_of_lt (sInf_le (Set.mem_range.mpr ⟨M, rfl⟩)) hTailLt

end ProbabilityTheory

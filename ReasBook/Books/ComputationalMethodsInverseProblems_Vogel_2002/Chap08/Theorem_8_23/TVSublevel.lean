/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Poincare
public section
noncomputable section
namespace VariationalRegularization
variable {d : ℕ}

private lemma lpToL1_norm_le_sublevel
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact (1 ≤ p)] [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    ‖lpToL1 f‖ ≤
      (domainMeasure Ω Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)).toReal * ‖f‖ := by
  -- Compare the `eLpNorm`s first; the `Lp` norm statement is just the corresponding `toReal`
  -- normalization.
  let fμ : (EuclideanSpace ℝ (Fin d)) →ₘ[domainMeasure Ω] ℝ := f
  let C : ENNReal :=
    domainMeasure Ω Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)
  have hLp1 : MeasureTheory.MemLp fμ 1 (domainMeasure Ω) := by
    exact MeasureTheory.Lp.mem_Lp_iff_memLp.mp <|
      MeasureTheory.Lp.antitone (E := ℝ) (μ := domainMeasure Ω)
        (show (1 : ENNReal) ≤ p from Fact.out) f.2
  have hcompare :
      MeasureTheory.eLpNorm fμ 1 (domainMeasure Ω) ≤
        MeasureTheory.eLpNorm fμ p (domainMeasure Ω) * C :=
    MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (show (1 : ENNReal) ≤ p from Fact.out) fμ.aestronglyMeasurable
  have hC_ne_top : C ≠ ⊤ := by
    have hp_inv_le_one : 1 / p.toReal ≤ 1 := by
      by_cases hp_top : p = ⊤
      · simp [hp_top]
      · have hp_one : 1 ≤ p.toReal := by
          simpa using ENNReal.toReal_mono hp_top (show (1 : ENNReal) ≤ p from Fact.out)
        simpa [one_div] using inv_le_one_of_one_le₀ hp_one
    have hC_nonneg : 0 ≤ 1 / (1 : ENNReal).toReal - 1 / p.toReal := by
      simpa using sub_nonneg.mpr hp_inv_le_one
    exact
      (ENNReal.rpow_lt_top_of_nonneg
        hC_nonneg
        (MeasureTheory.measure_ne_top (domainMeasure Ω) Set.univ)).ne
  have hcompareRealENN :
      ENNReal.toReal (MeasureTheory.eLpNorm fμ 1 (domainMeasure Ω)) ≤
        ENNReal.toReal (MeasureTheory.eLpNorm fμ p (domainMeasure Ω) * C) := by
    exact
      (ENNReal.toReal_le_toReal hLp1.2.ne
        (ENNReal.mul_ne_top f.2.ne hC_ne_top)).2 hcompare
  -- Rewrite both `Lp` norms to the same `eLpNorm` spelling and apply the real-valued inequality.
  have hcompareReal :
      ‖lpToL1 f‖ ≤ C.toReal * ‖f‖ := by
    rw [MeasureTheory.Lp.norm_def, MeasureTheory.Lp.norm_def, lpToL1_toAEEqFun]
    simpa [C, fμ, ENNReal.toReal_mul, mul_comm, mul_left_comm, mul_assoc] using hcompareRealENN
  simpa [C] using hcompareReal


/-- Helper for Theorem 8.23: an exact-objective upper bound controls the total-variation term. -/
lemma tvObjectiveSublevel_totalVariationBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    {B : EReal}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hObj :
      tvRegularizedLeastSquaresFunctional K g α f ≤ B) :
    (α : EReal) * totalVariation (lpToL1 f) ≤ B := by
  -- Drop the nonnegative residual term from the exact objective.
  have hres_nonneg :
      (0 : EReal) ≤ (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) := by
    exact_mod_cast (show 0 ≤ ‖K f - g‖ ^ 2 / 2 by positivity)
  have hpenalty_le :
      (α : EReal) * totalVariation (lpToL1 f) ≤
        (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) +
          (α : EReal) * totalVariation (lpToL1 f)) := by
    simpa [add_comm] using
      (le_add_of_nonneg_left hres_nonneg :
        (α : EReal) * totalVariation (lpToL1 f) ≤
          (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) +
            (α : EReal) * totalVariation (lpToL1 f))
  calc
    (α : EReal) * totalVariation (lpToL1 f)
        ≤ (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal) +
            (α : EReal) * totalVariation (lpToL1 f)) :=
      hpenalty_le
    _ = tvRegularizedLeastSquaresFunctional K g α f := by
      rw [tvRegularizedLeastSquaresFunctional_def]
    _ ≤ B := hObj

/-- Helper for Theorem 8.23: an exact-objective upper bound also controls the quadratic residual
term. -/
lemma tvObjectiveSublevel_residualBound
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    {B : EReal}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hObj :
      tvRegularizedLeastSquaresFunctional K g α f ≤ B) :
    (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) ≤ B := by
  have hpenalty_nonneg :
      (0 : EReal) ≤ (α : EReal) * totalVariation (lpToL1 f) := by
    have htv_nonneg : (0 : EReal) ≤ totalVariation (lpToL1 f) := by
      have hdiv_zero :
          ∀ x : EuclideanSpace ℝ (Fin d),
            admissibleDivergence (AdmissibleTestField.zero Ω) x = 0 := by
        intro x
        have hfd :
            fderiv ℝ (⇑(0 : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1)) x = 0 := by
          change fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin d) =>
            (0 : EuclideanSpace ℝ (Fin d))) x = 0
          simp
        rw [admissibleDivergence_def, AdmissibleTestField.zero_toTestFunction, hfd]
        simp
      rw [totalVariation_def]
      refine le_sSup ?_
      refine ⟨AdmissibleTestField.zero Ω, by
        change
          ((admissibleDivergencePairing
              (lpToL1 f) (AdmissibleTestField.zero Ω) : ℝ) : EReal) = 0
        rw [admissibleDivergencePairing_def]
        simp [hdiv_zero]⟩
    exact mul_nonneg (by exact_mod_cast le_of_lt hα)
      htv_nonneg
  -- Drop the nonnegative TV penalty to keep only the least-squares residual term.
  have hresidual_le :
      (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) ≤
        (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) +
          (α : EReal) * totalVariation (lpToL1 f) := by
    exact le_add_of_nonneg_right hpenalty_nonneg
  calc
    (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal))
        ≤ (((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) +
            (α : EReal) * totalVariation (lpToL1 f) :=
      hresidual_le
    _ = tvRegularizedLeastSquaresFunctional K g α f := by
      rw [tvRegularizedLeastSquaresFunctional_def]
    _ ≤ B := hObj


/-- Helper for Theorem 8.23: a finite exact-objective upper bound yields an unscaled total
variation bound. -/
lemma tvObjectiveSublevel_totalVariationBound_of_ltTop
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (B : EReal)
    (hB : B < ⊤)
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hObj :
      tvRegularizedLeastSquaresFunctional K g α f ≤ B) :
    totalVariation (lpToL1 f) ≤ (B / (α : EReal)).toReal := by
  -- First isolate the scaled TV term already controlled by the objective bound.
  have hscaled :
      (α : EReal) * totalVariation (lpToL1 f) ≤ B :=
    tvObjectiveSublevel_totalVariationBound K g α hObj
  have hαE_pos : (0 : EReal) < (α : EReal) := by
    exact_mod_cast hα
  have hαE_ne_top : (α : EReal) ≠ ⊤ :=
    EReal.coe_ne_top α
  have hdiv_ne_top : B / (α : EReal) ≠ ⊤ := by
    -- The quotient stays finite because both `B` and `α` are finite and `α > 0`.
    rw [EReal.div_eq_inv_mul]
    refine (EReal.mul_ne_top ((α : EReal)⁻¹) B).2 ?_
    constructor
    · exact Or.inl <| ne_bot_of_gt <| EReal.inv_pos_of_pos_ne_top hαE_pos hαE_ne_top
    constructor
    · exact Or.inl <| EReal.inv_nonneg_of_nonneg <| le_of_lt hαE_pos
    constructor
    · exact Or.inl <| (EReal.inv_lt_top (α : EReal)).ne
    · exact Or.inr <| ne_of_lt hB
  have htv_div :
      totalVariation (lpToL1 f) ≤ B / (α : EReal) := by
    -- Divide the scaled bound by the positive regularization parameter.
    exact (EReal.le_div_iff_mul_le hαE_pos hαE_ne_top).2 <| by
      simpa [mul_comm] using hscaled
  exact htv_div.trans <| EReal.le_coe_toReal hdiv_ne_top

/-- A mean-value Poincaré inequality controls the zero-mean part of a TV
sublevel. The residual and `K 1 ≠ 0` then control its scalar mean, yielding
an eventual `L¹` bound. Boundedness alone would fail on disconnected domains. -/
lemma eventualLpToL1Bound_of_eventually_tvSublevel
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h_poincare : HasLpTVPoincare Ω p)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (hα : 0 < α)
    (hK_one : K (MeasureTheory.Lp.const p (domainMeasure Ω) (1 : ℝ)) ≠ 0)
    (B : EReal)
    (hB : B < ⊤)
    (u : ℕ → MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (huB :
      ∀ᶠ n in Filter.atTop,
        tvRegularizedLeastSquaresFunctional K g α (u n) ≤
          B) :
    ∃ M : ℝ, ∀ᶠ n in Filter.atTop, ‖lpToL1 (u n)‖ ≤ M := by
  obtain ⟨CP, hCP, hP⟩ := h_poincare.centered_norm_le
  let one : MeasureTheory.Lp ℝ p (domainMeasure Ω) :=
    MeasureTheory.Lp.const p (domainMeasure Ω) (1 : ℝ)
  let V : ℝ := (B / (α : EReal)).toReal
  let P : ℝ := CP * V
  let D : ℝ := |B.toReal| + 1
  let Q : ℝ := P + ((D + ‖g‖ + ‖K‖ * P) / ‖K one‖) * ‖one‖
  let L : ℝ :=
    (domainMeasure Ω Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / p.toReal)).toReal
  refine ⟨L * Q, ?_⟩
  filter_upwards [huB] with n hn
  have htv : totalVariation (lpToL1 (u n)) ≤ (V : EReal) :=
    tvObjectiveSublevel_totalVariationBound_of_ltTop K g α hα B hB hn
  have hcenter : ‖u n - lpDomainMean (u n) • one‖ ≤ P := hP (u n) V htv
  have hresE : (((‖K (u n) - g‖ ^ 2 / 2 : ℝ) : EReal)) ≤ (B.toReal : EReal) :=
    (tvObjectiveSublevel_residualBound K g α hα hn).trans (EReal.le_coe_toReal hB.ne)
  have hresSq : ‖K (u n) - g‖ ^ 2 / 2 ≤ B.toReal := by exact_mod_cast hresE
  have hres : ‖K (u n) - g‖ ≤ D := by
    dsimp [D]
    nlinarith [sq_nonneg (‖K (u n) - g‖ - 1), le_abs_self B.toReal]
  have hKf : ‖K (u n)‖ ≤ D + ‖g‖ :=
    (norm_le_norm_sub_add (K (u n)) g).trans (add_le_add hres le_rfl)
  have hLp : ‖u n‖ ≤ Q := by
    apply (norm_le_of_centered_norm_le K one (u n) (lpDomainMean (u n)) P
      hK_one hcenter).trans
    dsimp [Q]
    gcongr
  exact (lpToL1_norm_le_sublevel (u n)).trans
    (mul_le_mul_of_nonneg_left hLp (ENNReal.toReal_nonneg))


end VariationalRegularization

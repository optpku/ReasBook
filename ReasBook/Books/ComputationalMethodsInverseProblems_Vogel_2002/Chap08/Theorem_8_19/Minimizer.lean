/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_18
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_19.Objective
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A1.ClosedConvex
public import Mathlib.MeasureTheory.Function.L2Space
public section
noncomputable section
open Filter
open scoped Topology
namespace VariationalRegularization
namespace TVMinimizer
variable {d : ℕ} {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
variable {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
variable [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]

lemma totalVariation_lowerSemicontinuous :
    LowerSemicontinuous (fun f : MeasureTheory.Lp ℝ p (domainMeasure Ω) ↦
      totalVariation (lpToL1 f)) := by
  have heq : (fun f : MeasureTheory.Lp ℝ p (domainMeasure Ω) ↦ totalVariation (lpToL1 f)) =
      fun f ↦ ⨆ v : AdmissibleTestField Ω,
        ((totalVariationPairingCLM v (lpToL1 f)) : EReal) := by
    funext f
    rw [totalVariation_def, sSup_range]
    simp only [totalVariationPairingCLM_apply]
  rw [heq]
  apply lowerSemicontinuous_iSup
  intro v
  simpa only [Function.comp_def, lpToL1CLM_apply] using
    (continuous_coe_real_ereal.comp
      ((totalVariationPairingCLM v).continuous.comp (lpToL1CLM (Ω := Ω) (p := p)).continuous)).lowerSemicontinuous

lemma objective_lowerSemicontinuous
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ] MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)) {α : ℝ} (hα : 0 < α) :
    LowerSemicontinuous (tvRegularizedLeastSquaresFunctional K g α) := by
  have hq : Continuous (fun f : MeasureTheory.Lp ℝ p (domainMeasure Ω) ↦
      ((‖K f - g‖ ^ 2 / 2 : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (((K.continuous.sub continuous_const).norm.pow 2).div_const 2)
  have hm : Continuous (fun t : EReal ↦ (α : EReal) * t) := by
    apply continuous_iff_continuousAt.2
    intro t
    have hαne : (α : EReal) ≠ 0 := by exact_mod_cast hα.ne'
    exact (EReal.continuousAt_mul (p := ((α : EReal), t))
      (Or.inl hαne) (Or.inl hαne)
      (Or.inl (EReal.coe_ne_bot α)) (Or.inl (EReal.coe_ne_top α))).comp
        (continuous_const.prodMk continuous_id).continuousAt
  have ht := hm.comp_lowerSemicontinuous
    (totalVariation_lowerSemicontinuous (Ω := Ω) (p := p))
    (fun _ _ h ↦ mul_le_mul_of_nonneg_left h (by exact_mod_cast hα.le))
  exact hq.lowerSemicontinuous.add' ht fun f ↦
    EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))

lemma objective_nonneg
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ] MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)) {α : ℝ} (hα : 0 ≤ α)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    0 ≤ tvRegularizedLeastSquaresFunctional K g α f := by
  rw [tvRegularizedLeastSquaresFunctional_def]
  exact add_nonneg (by positivity) (mul_nonneg (by exact_mod_cast hα) (lpTotalVariationNonneg _))

lemma tv_ne_top_of_objective_lt_top
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ] MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)) {α : ℝ} (hα : 0 < α)
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf : tvRegularizedLeastSquaresFunctional K g α f < ⊤) :
    totalVariation (lpToL1 f) ≠ ⊤ := by
  intro htv
  rw [tvRegularizedLeastSquaresFunctional_def, htv] at hf
  simp [EReal.coe_mul_top_of_pos hα] at hf

lemma tv_coe_toReal {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf : totalVariation (lpToL1 f) ≠ ⊤) :
    ((totalVariation (lpToL1 f)).toReal : EReal) = totalVariation (lpToL1 f) :=
  EReal.coe_toReal hf (ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe 0) (lpTotalVariationNonneg _)))

lemma objective_lt_top_of_tv_lt_top
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ] MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)) (α : ℝ)
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf : totalVariation (lpToL1 f) < ⊤) :
    tvRegularizedLeastSquaresFunctional K g α f < ⊤ := by
  rw [tvRegularizedLeastSquaresFunctional_def, ← tv_coe_toReal hf.ne,
    ← EReal.coe_mul, ← EReal.coe_add]
  exact EReal.coe_lt_top _

lemma midpoint_tv_le (x y : MeasureTheory.Lp ℝ p (domainMeasure Ω))
    (hx : totalVariation (lpToL1 x) ≠ ⊤) (hy : totalVariation (lpToL1 y) ≠ ⊤) :
    totalVariation (lpToL1 ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) ≤
      (((totalVariation (lpToL1 x)).toReal + (totalVariation (lpToL1 y)).toReal) / 2 : ℝ) := by
  rw [lpToL1_add, lpToL1_smul, lpToL1_smul]
  calc
    _ ≤ totalVariation ((1 / 2 : ℝ) • lpToL1 x) +
        totalVariation ((1 / 2 : ℝ) • lpToL1 y) := lpTotalVariationAddLe _ _
    _ ≤ ((‖(1 / 2 : ℝ)‖ : ℝ) : EReal) * totalVariation (lpToL1 x) +
        ((‖(1 / 2 : ℝ)‖ : ℝ) : EReal) * totalVariation (lpToL1 y) :=
      add_le_add (lpTotalVariationSmulLe _ _) (lpTotalVariationSmulLe _ _)
    _ = _ := by
      rw [← tv_coe_toReal hx, ← tv_coe_toReal hy]
      norm_num only [Real.norm_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      simp only [EReal.toReal_coe]
      norm_cast
      ring

omit [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)] in
lemma quadratic_midpoint (a b g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)) :
    ‖(1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b - g‖ ^ 2 / 2 =
      (‖a - g‖ ^ 2 / 2 + ‖b - g‖ ^ 2 / 2) / 2 - ‖a - b‖ ^ 2 / 8 := by
  have hmid : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b - g =
      (1 / 2 : ℝ) • ((a - g) + (b - g)) := by module
  rw [hmid, norm_smul]
  norm_num only [Real.norm_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  have h := parallelogram_law_with_norm ℝ (a - g) (b - g)
  have hsub : (a - g) - (b - g) = a - b := by abel
  rw [hsub] at h
  nlinarith

lemma minimizers_eq
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))) (hC : Convex ℝ C)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ] MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (hK : Function.Injective K) (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    {α : ℝ} (hα : 0 < α) {x y : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hx : x ∈ C) (hy : y ∈ C)
    (hminx : IsMinOn (tvRegularizedLeastSquaresFunctional K g α) C x)
    (hminy : IsMinOn (tvRegularizedLeastSquaresFunctional K g α) C y)
    (hfinite : tvRegularizedLeastSquaresFunctional K g α x < ⊤) : x = y := by
  have hval : tvRegularizedLeastSquaresFunctional K g α x =
      tvRegularizedLeastSquaresFunctional K g α y :=
    le_antisymm (hminx hy) (hminy hx)
  have hxtv := tv_ne_top_of_objective_lt_top K g hα hfinite
  have hytv := tv_ne_top_of_objective_lt_top K g hα (hval ▸ hfinite)
  let w := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hw : w ∈ C := hC hx hy (by norm_num) (by norm_num) (by norm_num)
  have htv := midpoint_tv_le x y hxtv hytv
  have hupper : tvRegularizedLeastSquaresFunctional K g α w ≤
      ((‖K w - g‖ ^ 2 / 2 + α *
        (((totalVariation (lpToL1 x)).toReal + (totalVariation (lpToL1 y)).toReal) / 2) : ℝ) : EReal) := by
    rw [tvRegularizedLeastSquaresFunctional_def, EReal.coe_add, EReal.coe_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left htv
      (show (0 : EReal) ≤ (α : EReal) by exact_mod_cast hα.le))
  have hmin := (hminx hw).trans hupper
  rw [tvRegularizedLeastSquaresFunctional_def, ← tv_coe_toReal hxtv,
    ← EReal.coe_mul, ← EReal.coe_add] at hmin
  simp only [EReal.toReal_coe] at hmin
  have hreal := EReal.coe_le_coe_iff.1 hmin
  have hvalreal : ‖K x - g‖ ^ 2 / 2 + α * (totalVariation (lpToL1 x)).toReal =
      ‖K y - g‖ ^ 2 / 2 + α * (totalVariation (lpToL1 y)).toReal := by
    rw [tvRegularizedLeastSquaresFunctional_def, tvRegularizedLeastSquaresFunctional_def,
      ← tv_coe_toReal hxtv, ← tv_coe_toReal hytv,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add] at hval
    simpa only [EReal.toReal_coe] using EReal.coe_injective hval
  have hquad := quadratic_midpoint (K x) (K y) g
  have hKw : K w = (1 / 2 : ℝ) • K x + (1 / 2 : ℝ) • K y := by simp [w]
  rw [hKw] at hreal
  have hzero : ‖K x - K y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖K x - K y‖]
  exact hK (sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 hzero)))

/-- The uniqueness part needs only convexity and a finite-TV feasible point;
compactness is used solely to obtain a minimizer. -/
theorem minimizers_eq_of_finiteTV_feasible
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))) (hC : Convex ℝ C)
    (hfinite : ∃ f ∈ C, totalVariation (lpToL1 f) < ⊤)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ] MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (hK : Function.Injective K) (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    {α : ℝ} (hα : 0 < α) {x y : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hx : x ∈ C) (hy : y ∈ C)
    (hminx : IsMinOn (tvRegularizedLeastSquaresFunctional K g α) C x)
    (hminy : IsMinOn (tvRegularizedLeastSquaresFunctional K g α) C y) : x = y := by
  obtain ⟨f₀, hf₀, htv₀⟩ := hfinite
  exact minimizers_eq C hC K hK g hα hx hy hminx hminy
    ((hminx hf₀).trans_lt (objective_lt_top_of_tv_lt_top K g α htv₀))

/-- A compact convex admissible set and a finite-TV feasible point suffice for
existence and uniqueness. Compactness is an explicit stronger constraint
hypothesis; no BV compact-embedding theorem is used by this version. -/
theorem existsUnique_on_compact
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))) (hC : IsCompact C)
    (hconv : Convex ℝ C)
    (hfinite : ∃ f ∈ C, totalVariation (lpToL1 f) < ⊤)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ] MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (hK : Function.Injective K) (g : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    {α : ℝ} (hα : 0 < α) :
    ∃! f, f ∈ C ∧ IsMinOn (tvRegularizedLeastSquaresFunctional K g α) C f := by
  obtain ⟨f₀, hf₀, htv₀⟩ := hfinite
  obtain ⟨f, hf, hmin⟩ :=
    ((objective_lowerSemicontinuous K g hα).lowerSemicontinuousOn C).exists_isMinOn ⟨f₀, hf₀⟩ hC
  have hfinite₀ : tvRegularizedLeastSquaresFunctional K g α f₀ < ⊤ :=
    objective_lt_top_of_tv_lt_top K g α htv₀
  have hfinitef := (hmin hf₀).trans_lt hfinite₀
  refine ⟨f, ⟨hf, hmin⟩, ?_⟩
  intro y hy
  exact (minimizers_eq C hconv K hK g hα hf hy.1 hmin hy.2 hfinitef).symm

end TVMinimizer
end VariationalRegularization

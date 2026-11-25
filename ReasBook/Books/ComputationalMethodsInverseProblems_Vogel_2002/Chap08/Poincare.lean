/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_19.Objective
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public section
noncomputable section
namespace VariationalRegularization

/-- The scalar average of an `Lᵖ` function, computed through its canonical
`L¹` representative. -/
@[expose] def lpDomainMean {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) : ℝ :=
  (∫ x, lpToL1 f x ∂domainMeasure Ω) / (domainMeasure Ω Set.univ).toReal

/-- The mean-value Poincaré inequality for the TV seminorm in `Lᵖ`.
It is an explicit domain regularity hypothesis, as available on connected
bounded Lipschitz domains below the BV critical exponent. Boundedness of an
arbitrary open domain alone is insufficient: TV vanishes on a separate
constant on each connected component. The extended-real formulation also
covers functions with infinite variation. -/
@[expose] def HasLpTVPoincare {d : ℕ}
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    (p : ENNReal) [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)] : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MeasureTheory.Lp ℝ p (domainMeasure Ω),
    ((‖f - lpDomainMean f • MeasureTheory.Lp.const p (domainMeasure Ω) (1 : ℝ)‖ : ℝ) : EReal) ≤
      (C : EReal) * totalVariation (lpToL1 f)

/-- A TV bound controls the part with zero average through Poincaré. -/
lemma HasLpTVPoincare.centered_norm_le {d : ℕ}
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (h : HasLpTVPoincare Ω p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) (V : ℝ),
      totalVariation (lpToL1 f) ≤ (V : EReal) →
        ‖f - lpDomainMean f • MeasureTheory.Lp.const p (domainMeasure Ω) (1 : ℝ)‖ ≤ C * V := by
  obtain ⟨C, hC, hP⟩ := h
  refine ⟨C, hC, ?_⟩
  intro f V hV
  have hmul := mul_le_mul_of_nonneg_left hV
    (show (0 : EReal) ≤ (C : EReal) by exact_mod_cast hC)
  have hbound := (hP f).trans hmul
  exact_mod_cast hbound

/-- A bounded zero-mean part and an operator that detects constants control
the whole function. This is the algebraic constant-mode estimate; it does
not assume a coercivity inequality. -/
lemma norm_le_of_centered_norm_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (K : X →L[ℝ] Y) (one f : X) (m P : ℝ)
    (hKone : K one ≠ 0) (hcenter : ‖f - m • one‖ ≤ P) :
    ‖f‖ ≤ P + ((‖K f‖ + ‖K‖ * P) / ‖K one‖) * ‖one‖ := by
  have hk : 0 < ‖K one‖ := norm_pos_iff.2 hKone
  have hKm : |m| * ‖K one‖ ≤ ‖K f‖ + ‖K‖ * P := by
    calc
      _ = ‖K (m • one)‖ := by rw [map_smul, norm_smul, Real.norm_eq_abs]
      _ = ‖K f - K (f - m • one)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖K f‖ + ‖K (f - m • one)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add_right ((K.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hcenter (norm_nonneg K))) _
  have hm : |m| ≤ (‖K f‖ + ‖K‖ * P) / ‖K one‖ := (le_div_iff₀ hk).2 hKm
  calc
    ‖f‖ = ‖(f - m • one) + m • one‖ := by congr 1; abel
    _ ≤ ‖f - m • one‖ + ‖m • one‖ := norm_add_le _ _
    _ = ‖f - m • one‖ + |m| * ‖one‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ _ := add_le_add hcenter (mul_le_mul_of_nonneg_right hm (norm_nonneg _))

end VariationalRegularization

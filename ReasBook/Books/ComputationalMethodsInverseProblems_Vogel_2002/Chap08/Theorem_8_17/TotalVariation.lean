/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15.TV
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_13

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}
variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

namespace BV

/-- The canonical total-variation seminorm on `BV(Ω)` is not strictly convex on a nontrivial
bounded-variation space: every nonzero `u` and the origin lie on a common ray where a seminorm is
affine. -/
theorem tvSeminorm_notStrictConvexOn [Nontrivial (BV Ω)] :
    ¬ StrictConvexOn ℝ Set.univ (tvSeminorm : BV Ω → ℝ) := by
  intro hstrict
  obtain ⟨u, hu⟩ := exists_ne (0 : BV Ω)
  have hlt :
      (1 / 2 : ℝ) * tvSeminorm u < (1 / 2 : ℝ) * tvSeminorm u := by
    simpa [one_div, map_smul_eq_mul] using
      hstrict.2
        (show u ∈ (Set.univ : Set (BV Ω)) by simp)
        (show (0 : BV Ω) ∈ Set.univ by simp)
        hu
        (show 0 < (1 / 2 : ℝ) by norm_num)
        (show 0 < (1 / 2 : ℝ) by norm_num)
        (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num)
  exact lt_irrefl _ hlt

end BV

namespace W11

/-- The Chapter 8 total-variation functional restricted from `L¹(Ω)` to the source-facing Sobolev
space `W¹,¹(Ω)` and converted to a real-valued quantity by `EReal.toReal`. -/
@[expose] def totalVariation (f : W¹,¹(Ω)) : ℝ :=
  (VariationalRegularization.totalVariation f.toL1).toReal

/-- The defining formula for the restricted Chapter 8 total-variation functional on `W¹,¹(Ω)`. -/
theorem totalVariation_def (f : W¹,¹(Ω)) :
    f.totalVariation = (VariationalRegularization.totalVariation f.toL1).toReal := by
  rfl

/-- Proposition 8.13 in reusable real-valued form on the source-facing Sobolev owner: the Chapter
8 total variation of the underlying `L¹(Ω)` function equals the weak-gradient norm integral. -/
theorem totalVariation_eq_integralNormWeakGradient (f : W¹,¹(Ω)) :
    f.totalVariation = f.integralNormWeakGradient := by
  simpa [totalVariation_def, W11.integralNormWeakGradient_def] using
    totalVariation_toReal_eq_integral_norm_of_weakGradient f

/-- On `W¹,¹(Ω)`, the restricted real-valued Chapter 8 total variation is absolutely homogeneous. -/
theorem totalVariation_smul (a : ℝ) (f : W¹,¹(Ω)) :
    (a • f).totalVariation = ‖a‖ * f.totalVariation := by
  rw [totalVariation_eq_integralNormWeakGradient (a • f),
    totalVariation_eq_integralNormWeakGradient f,
    W11.integralNormWeakGradient_def, W11.integralNormWeakGradient_def]
  rw [W11.smul_weakGradient]
  have hsmul :
      (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖(a • f.weakGradient) x‖) =ᵐ[domainMeasure Ω]
        fun x ↦ ‖a‖ * ‖f.weakGradient x‖ := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul a f.weakGradient] with x hx
    simp [hx, norm_smul]
  calc
    ∫ x, ‖(a • f.weakGradient) x‖ ∂domainMeasure Ω
        = ∫ x, ‖a‖ * ‖f.weakGradient x‖ ∂domainMeasure Ω :=
          MeasureTheory.integral_congr_ae hsmul
    _ = ‖a‖ * ∫ x, ‖f.weakGradient x‖ ∂domainMeasure Ω := by
          rw [MeasureTheory.integral_const_mul]

/-- The restricted real-valued Chapter 8 total variation vanishes at `0 ∈ W¹,¹(Ω)`. -/
@[simp] theorem totalVariation_zero :
    (0 : W¹,¹(Ω)).totalVariation = 0 := by
  rw [totalVariation_eq_integralNormWeakGradient (0 : W¹,¹(Ω)),
    W11.integralNormWeakGradient_def, W11.zero_weakGradient]
  have hzero :
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ‖(0 :
          MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω)) x‖) =ᵐ[domainMeasure Ω]
        0 := by
    filter_upwards
      [MeasureTheory.Lp.coeFn_zero
        (EuclideanSpace ℝ (Fin d)) (1 : ENNReal) (domainMeasure Ω)] with x hx
    simpa using hx
  calc
    ∫ x, ‖(0 : MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω)) x‖
        ∂domainMeasure Ω
        = ∫ x, (0 : ℝ) ∂domainMeasure Ω := MeasureTheory.integral_congr_ae hzero
    _ = 0 := by simp

/-- The restriction of the Chapter 8 total-variation functional to a nontrivial source-facing
Sobolev space `W¹,¹(Ω)` is not strictly convex: by Proposition 8.13 it is absolutely homogeneous
and therefore affine on every ray through `0`. -/
theorem totalVariation_notStrictConvexOn [Nontrivial (W¹,¹(Ω))] :
    ¬ StrictConvexOn ℝ Set.univ (W11.totalVariation : W¹,¹(Ω) → ℝ) := by
  intro hstrict
  obtain ⟨u, hu⟩ := exists_ne (0 : W¹,¹(Ω))
  have hmid :
      ((1 / 2 : ℝ) • u).totalVariation =
        (1 / 2 : ℝ) * u.totalVariation := by
    simpa using totalVariation_smul (1 / 2 : ℝ) u
  have hstrict_mid :
      ((1 / 2 : ℝ) • u).totalVariation <
        (1 / 2 : ℝ) * u.totalVariation +
          (1 / 2 : ℝ) * (0 : W¹,¹(Ω)).totalVariation := by
    simpa using
      hstrict.2
        (show u ∈ (Set.univ : Set (W¹,¹(Ω))) by simp)
        (show (0 : W¹,¹(Ω)) ∈ Set.univ by simp)
        hu
        (show 0 < (1 / 2 : ℝ) by norm_num)
        (show 0 < (1 / 2 : ℝ) by norm_num)
        (show (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 by norm_num)
  have hlt :
      (1 / 2 : ℝ) * u.totalVariation <
        (1 / 2 : ℝ) * u.totalVariation := by
    calc
      (1 / 2 : ℝ) * u.totalVariation
          = ((1 / 2 : ℝ) • u).totalVariation := hmid.symm
      _ < (1 / 2 : ℝ) * u.totalVariation +
            (1 / 2 : ℝ) * (0 : W¹,¹(Ω)).totalVariation := hstrict_mid
      _ = (1 / 2 : ℝ) * u.totalVariation := by simp
  exact lt_irrefl _ hlt

end W11

end VariationalRegularization

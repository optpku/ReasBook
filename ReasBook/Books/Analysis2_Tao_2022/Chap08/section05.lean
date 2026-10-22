/-
Authors: Zichen Wang, Wanli Ma, Min Cui, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open MeasureTheory

section Chap08
section Section05

/-- Helper for Theorem 8.6: absolute integrability of a real-valued function on `ℝ²`
implies its integrability. -/
lemma helperForTheorem_8_6_integrable_of_absIntegrable
    (f : ℝ × ℝ → ℝ)
    (hf_meas : AEMeasurable f (volume : Measure (ℝ × ℝ)))
    (hfin : Integrable (fun z : ℝ × ℝ => |f z|)) :
    Integrable f := by
  have hnorm : Integrable (fun z : ℝ × ℝ => ‖f z‖) := by
    simpa [Real.norm_eq_abs] using hfin
  exact (integrable_norm_iff hf_meas.aestronglyMeasurable).1 hnorm

/-- Helper for Theorem 8.6: integrability on `ℝ²` gives a.e. integrable sections
and integrability of the iterated-integral functions. -/
lemma helperForTheorem_8_6_sections_and_outer_integrable
    (f : ℝ × ℝ → ℝ)
    (hf_int : Integrable f) :
    (∀ᵐ x : ℝ ∂(volume : Measure ℝ), Integrable (fun y : ℝ => f (x, y))) ∧
    (∀ᵐ y : ℝ ∂(volume : Measure ℝ), Integrable (fun x : ℝ => f (x, y))) ∧
    Integrable (fun x : ℝ => ∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∧
    Integrable (fun y : ℝ => ∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) := by
  have hf_prod : Integrable f ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using hf_int
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hf_prod.prod_right_ae
  · simpa using hf_prod.prod_left_ae
  · simpa using hf_prod.integral_prod_left
  · simpa using hf_prod.integral_prod_right

/-- Helper for Theorem 8.6: Fubini equalities for an integrable real-valued function on `ℝ²`. -/
lemma helperForTheorem_8_6_fubini_equalities_for_f
    (f : ℝ × ℝ → ℝ)
    (hf_int : Integrable f) :
    (∫ z : ℝ × ℝ, f z ∂(volume : Measure (ℝ × ℝ))) =
      (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) ∧
    (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) =
      (∫ y : ℝ, (∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) := by
  have hf_prod : Integrable f ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using hf_int
  have h_prod_eq_xy :
      (∫ z : ℝ × ℝ, f z ∂(volume : Measure (ℝ × ℝ))) =
        (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using integral_prod f hf_prod
  have h_prod_eq_yx :
      (∫ z : ℝ × ℝ, f z ∂(volume : Measure (ℝ × ℝ))) =
        (∫ y : ℝ, (∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using integral_prod_symm f hf_prod
  have h_xy_eq_yx :
      (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) =
        (∫ y : ℝ, (∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) :=
    h_prod_eq_xy.symm.trans h_prod_eq_yx
  exact ⟨h_prod_eq_xy, h_xy_eq_yx⟩

/-- Helper for Theorem 8.6: Tonelli equalities for the absolute value `|f|` on `ℝ²`. -/
lemma helperForTheorem_8_6_tonelli_equalities_for_abs
    (f : ℝ × ℝ → ℝ)
    (hfin : Integrable (fun z : ℝ × ℝ => |f z|)) :
    (∫ x : ℝ, (∫ y : ℝ, |f (x, y)| ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) =
      (∫ z : ℝ × ℝ, |f z| ∂(volume : Measure (ℝ × ℝ))) ∧
    (∫ z : ℝ × ℝ, |f z| ∂(volume : Measure (ℝ × ℝ))) =
      (∫ y : ℝ, (∫ x : ℝ, |f (x, y)| ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) := by
  have habs_prod : Integrable (fun z : ℝ × ℝ => |f z|) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using hfin
  have h_prod_eq_xy_abs :
      (∫ z : ℝ × ℝ, |f z| ∂(volume : Measure (ℝ × ℝ))) =
        (∫ x : ℝ, (∫ y : ℝ, |f (x, y)| ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using integral_prod (fun z : ℝ × ℝ => |f z|) habs_prod
  have h_prod_eq_yx_abs :
      (∫ z : ℝ × ℝ, |f z| ∂(volume : Measure (ℝ × ℝ))) =
        (∫ y : ℝ, (∫ x : ℝ, |f (x, y)| ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) := by
    simpa [Measure.volume_eq_prod] using integral_prod_symm (fun z : ℝ × ℝ => |f z|) habs_prod
  exact ⟨h_prod_eq_xy_abs.symm, h_prod_eq_yx_abs⟩

/-- Theorem 8.6 (Fubini--Tonelli for absolutely integrable functions on `ℝ²`):
if `f : ℝ × ℝ → ℝ` is Lebesgue measurable and `∫ |f| < ∞` on `ℝ²`, then for almost every
`x` the section `y ↦ f (x, y)` is integrable, for almost every `y` the section `x ↦ f (x, y)`
is integrable, the iterated-integral functions are integrable, and both the Fubini equalities
for `f` and for `|f|` hold. -/
theorem fubini_tonelli_absolutely_integrable_R2
    (f : ℝ × ℝ → ℝ)
    (hf_meas : AEMeasurable f (volume : Measure (ℝ × ℝ)))
    (hfin : Integrable (fun z : ℝ × ℝ => |f z|)) :
    (∀ᵐ x : ℝ ∂(volume : Measure ℝ), Integrable (fun y : ℝ => f (x, y))) ∧
    (∀ᵐ y : ℝ ∂(volume : Measure ℝ), Integrable (fun x : ℝ => f (x, y))) ∧
    Integrable (fun x : ℝ => ∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∧
    Integrable (fun y : ℝ => ∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∧
    (∫ z : ℝ × ℝ, f z ∂(volume : Measure (ℝ × ℝ))) =
      (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) ∧
    (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) =
      (∫ y : ℝ, (∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) ∧
    (∫ x : ℝ, (∫ y : ℝ, |f (x, y)| ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) =
      (∫ z : ℝ × ℝ, |f z| ∂(volume : Measure (ℝ × ℝ))) ∧
    (∫ z : ℝ × ℝ, |f z| ∂(volume : Measure (ℝ × ℝ))) =
      (∫ y : ℝ, (∫ x : ℝ, |f (x, y)| ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) :=
by
  have hf_int : Integrable f :=
    helperForTheorem_8_6_integrable_of_absIntegrable f hf_meas hfin
  have h_sections :
      (∀ᵐ x : ℝ ∂(volume : Measure ℝ), Integrable (fun y : ℝ => f (x, y))) ∧
      (∀ᵐ y : ℝ ∂(volume : Measure ℝ), Integrable (fun x : ℝ => f (x, y))) ∧
      Integrable (fun x : ℝ => ∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∧
      Integrable (fun y : ℝ => ∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) :=
    helperForTheorem_8_6_sections_and_outer_integrable f hf_int
  have h_fubini :
      (∫ z : ℝ × ℝ, f z ∂(volume : Measure (ℝ × ℝ))) =
        (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) ∧
      (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) =
        (∫ y : ℝ, (∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) :=
    helperForTheorem_8_6_fubini_equalities_for_f f hf_int
  have h_tonelli_abs :
      (∫ x : ℝ, (∫ y : ℝ, |f (x, y)| ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) =
        (∫ z : ℝ × ℝ, |f z| ∂(volume : Measure (ℝ × ℝ))) ∧
      (∫ z : ℝ × ℝ, |f z| ∂(volume : Measure (ℝ × ℝ))) =
        (∫ y : ℝ, (∫ x : ℝ, |f (x, y)| ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) :=
    helperForTheorem_8_6_tonelli_equalities_for_abs f hfin
  rcases h_sections with ⟨h_sec_x, h_sec_y, h_int_x, h_int_y⟩
  rcases h_fubini with ⟨h_prod_eq_xy, h_xy_eq_yx⟩
  rcases h_tonelli_abs with ⟨h_abs_xy_eq_prod, h_abs_prod_eq_yx⟩
  exact ⟨h_sec_x, h_sec_y, h_int_x, h_int_y, h_prod_eq_xy, h_xy_eq_yx, h_abs_xy_eq_prod,
    h_abs_prod_eq_yx⟩

/-- Theorem 8.7 (Fubini's theorem): if `f : ℝ × ℝ → ℝ` is Lebesgue measurable and
`∫ |f| < ∞` on `ℝ²`, then (1) for almost every `x`, the section `y ↦ f (x, y)` is
absolutely integrable and `F x := ∫ y, f (x, y)` defines an `L¹` function of `x`;
(2) for almost every `y`, the section `x ↦ f (x, y)` is absolutely integrable and
`G y := ∫ x, f (x, y)` defines an `L¹` function of `y`; and (3) the two iterated
integrals agree with the integral over `ℝ²`. -/
theorem fubini_theorem_R2
    (f : ℝ × ℝ → ℝ)
    (hf_meas : AEMeasurable f (volume : Measure (ℝ × ℝ)))
    (hfin : Integrable (fun z : ℝ × ℝ => |f z|)) :
    (∀ᵐ x : ℝ ∂(volume : Measure ℝ), Integrable (fun y : ℝ => f (x, y))) ∧
    Integrable (fun x : ℝ => ∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∧
    (∀ᵐ y : ℝ ∂(volume : Measure ℝ), Integrable (fun x : ℝ => f (x, y))) ∧
    Integrable (fun y : ℝ => ∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∧
    (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) =
      (∫ z : ℝ × ℝ, f z ∂(volume : Measure (ℝ × ℝ))) ∧
    (∫ z : ℝ × ℝ, f z ∂(volume : Measure (ℝ × ℝ))) =
      (∫ y : ℝ, (∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) := by
  rcases fubini_tonelli_absolutely_integrable_R2 f hf_meas hfin with
    ⟨h_sec_x, h_sec_y, h_int_x, h_int_y, h_prod_eq_xy, h_xy_eq_yx, _, _⟩
  have h_xy_eq_prod :
      (∫ x : ℝ, (∫ y : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) =
        (∫ z : ℝ × ℝ, f z ∂(volume : Measure (ℝ × ℝ))) :=
    h_prod_eq_xy.symm
  have h_prod_eq_yx :
      (∫ z : ℝ × ℝ, f z ∂(volume : Measure (ℝ × ℝ))) =
        (∫ y : ℝ, (∫ x : ℝ, f (x, y) ∂(volume : Measure ℝ)) ∂(volume : Measure ℝ)) :=
    h_prod_eq_xy.trans h_xy_eq_yx
  exact ⟨h_sec_x, h_int_x, h_sec_y, h_int_y, h_xy_eq_prod, h_prod_eq_yx⟩

end Section05
end Chap08

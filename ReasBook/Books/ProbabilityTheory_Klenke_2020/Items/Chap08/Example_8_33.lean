/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: use independence to identify the joint law of `(X, X + Y)` with the composition
-- product of `P.map X` and the translation kernel `x ↦ Measure.dirac x ∗ P.map Y`, then apply
-- the a.e. uniqueness theorem `condDistrib_ae_eq_of_measure_eq_compProd`. The statement is given
-- in the canonical mathlib `=ᵐ[P.map X]` form.
/-- Example 8.33: If `X` and `Y` are independent real random variables, then for `P.map X`-almost
all `x : ℝ`, the regular conditional distribution of `X + Y` given `X = x` is the translated law
`Measure.dirac x ∗ P.map Y`. -/
theorem condDistrib_add_given_left_ae_eq_dirac_conv
    (P : Measure Ω) [IsFiniteMeasure P] {X Y : Ω → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (hXY : IndepFun X Y P) :
    condDistrib (X + Y) X P =ᵐ[P.map X] fun x ↦ Measure.dirac x ∗ P.map Y := by
  let ν : Measure ℝ := P.map X
  let η : Measure ℝ := P.map Y
  let κ : Kernel ℝ ℝ :=
    ((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ η).map fun z : ℝ × ℝ ↦ z.1 + z.2
  have hκ_apply : ∀ x : ℝ, κ x = Measure.dirac x ∗ η := by
    intro x
    change
      (((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ η).map fun z : ℝ × ℝ ↦ z.1 + z.2) x =
        Measure.dirac x ∗ η
    rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
    rw [Measure.dirac_prod, Measure.map_map (by fun_prop) measurable_prodMk_left]
    simpa [Function.comp_def] using (Measure.dirac_conv x η).symm
  have hXY_map : P.map (fun ω ↦ (X ω, Y ω)) = ν.prod η := by
    simpa [ν, η] using
      (indepFun_iff_map_prod_eq_prod_map_map hX hY).mp hXY
  have hmap :
      P.map (fun ω ↦ (X ω, (X + Y) ω)) =
        (ν.prod η).map (fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) := by
    rw [← hXY_map]
    change P.map ((fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) ∘ fun ω ↦ (X ω, Y ω)) =
      Measure.map (fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) (Measure.map (fun ω ↦ (X ω, Y ω)) P)
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hX.prodMk hY)]
  have hcomp :
      (ν.prod η).map (fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) = ν ⊗ₘ κ := by
    refine Measure.ext_prod ?_
    intro s t hs ht
    have hF_meas : Measurable (fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) := by fun_prop
    rw [Measure.map_apply (by fun_prop) (hs.prod ht), Measure.compProd_apply_prod hs ht]
    rw [Measure.prod_apply (hF_meas (hs.prod ht))]
    have hslice :
        (fun x : ℝ ↦
          η (Prod.mk x ⁻¹' ((fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) ⁻¹' (s ×ˢ t)))) =
        s.indicator (fun x ↦ κ x t) := by
      funext x
      by_cases hx : x ∈ s
      · have hpre :
            Prod.mk x ⁻¹' ((fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) ⁻¹' (s ×ˢ t)) =
              (fun y : ℝ ↦ x + y) ⁻¹' t := by
          ext y
          simp [hx]
        rw [hpre, Set.indicator_of_mem hx, hκ_apply x, Measure.dirac_conv,
          Measure.map_apply (by fun_prop) ht]
      · have hpre :
            Prod.mk x ⁻¹' ((fun z : ℝ × ℝ ↦ (z.1, z.1 + z.2)) ⁻¹' (s ×ˢ t)) = ∅ := by
          ext y
          simp [hx]
        simp [hpre, Set.indicator, hx]
    rw [hslice, lintegral_indicator hs]
  have hkernel :
      P.map (fun ω ↦ (X ω, (X + Y) ω)) = P.map X ⊗ₘ κ := by
    simpa [ν] using hmap.trans hcomp
  have hcond : condDistrib (X + Y) X P =ᵐ[P.map X] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) hkernel
  filter_upwards [hcond] with x hx
  rw [hx, hκ_apply]

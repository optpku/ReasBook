/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Definition_8_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {E : Type v} [mE : MeasurableSpace E] [StandardBorelSpace E]

-- Proof sketch: in the nonempty case, view `id : Ω → Ω` as a measurable map from `(Ω, mΩ)` to
-- `(Ω, m)` using `hm` and reuse the canonical owner construction `condDistrib Y id P`; if `Ω` is
-- empty, the theorem is witnessed internally by the zero kernel.
/-- Theorem 8.37: If `Y` takes values in a Borel space `E`, then given a sub-σ-algebra `m` of the
ambient σ-algebra there exists a regular conditional distribution of `Y` given `m`. -/
theorem exists_regular_conditional_distribution_borel_given
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {Y : Ω → E} (hY : Measurable[mΩ, mE] Y) :
    ∃ κ : Kernel[m, mE] Ω E, IsRegularCondDistrib P m Y κ := by
  by_cases hΩ : Nonempty Ω
  · letI : Nonempty Ω := hΩ
    letI : Nonempty E := ⟨Y (Classical.choice hΩ)⟩
    have hX : Measurable[mΩ, m] id := by
      rw [measurable_iff_comap_le, MeasurableSpace.comap_id]
      exact hm
    have hκ :
        @IsRegularCondDistrib Ω E mE mΩ P inferInstance (MeasurableSpace.comap id m) Y
          ((condDistrib Y id P).comap id (Measurable.of_comap_le le_rfl)) :=
      @ProbabilityTheory.isRegularCondDistrib_condDistrib Ω E mE mΩ Ω m inferInstance
        inferInstance P inferInstance Y hY id hX
    have hm_id : MeasurableSpace.comap id m = m := MeasurableSpace.comap_id
    let κ : Kernel[m, mE] Ω E := by
      exact hm_id ▸ ((condDistrib Y id P).comap id (Measurable.of_comap_le le_rfl))
    refine ⟨κ, ?_⟩
    subst κ
    convert hκ using 1 <;> simp [hm_id]
  · letI : IsEmpty Ω := not_nonempty_iff.mp hΩ
    refine ⟨0, ?_⟩
    refine
      { toIsMarkovKernel := inferInstance
        le_ambient := hm
        measurable_Y := hY
        ae_eq_conditionalProbability := ?_ }
    intro B hB
    exact Filter.EventuallyEq.of_eq <| funext fun ω ↦ False.elim (isEmptyElim ω)

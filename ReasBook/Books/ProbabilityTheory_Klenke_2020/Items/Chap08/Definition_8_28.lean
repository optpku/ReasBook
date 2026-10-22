/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v w

variable {Ω : Type u} {E : Type v} [mE : MeasurableSpace E]

namespace ProbabilityTheory

/-- Definition 8.28: A kernel `κ : Kernel[m, mE] Ω E` is a regular conditional
distribution of `Y` given the sub-σ-algebra `m` if it is a Markov kernel and, for every
measurable `B ⊆ E`, the section `ω ↦ κ ω B` agrees `P`-almost surely with the conditional
probability `P[Y ∈ B | m]`. This is equivalent to the integral identity (8.10) for all `A ∈ m`
and measurable `B`. -/
class IsRegularCondDistrib
    {mΩ : MeasurableSpace Ω} (P : @Measure Ω mΩ) [IsFiniteMeasure P] (m : MeasurableSpace Ω)
    (Y : Ω → E) (κ : @Kernel Ω E m mE) : Prop
    extends IsMarkovKernel κ where
  /-- The conditioning σ-algebra is a sub-σ-algebra of the ambient one. -/
  le_ambient : m ≤ mΩ
  /-- The conditioned variable is measurable. -/
  measurable_Y : @Measurable Ω E mΩ mE Y
  /-- For each measurable set `B`, the kernel section `ω ↦ κ ω B` realizes the conditional
  probability of the event `{Y ∈ B}` given `m`. -/
  ae_eq_conditionalProbability :
    ∀ ⦃B : Set E⦄, MeasurableSet B →
      (fun ω ↦ (κ ω).real B) =ᵐ[P] P⟦Y ⁻¹' B | m⟧

namespace IsRegularCondDistrib

variable [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω}
variable {Y : Ω → E} {κ : Kernel[m, mE] Ω E}

/-- A regular conditional distribution disintegrates the joint law of `(id, Y)` over the trimmed
base measure. This is the canonical bridge from the source-facing conditional-probability
definition to the owner abstraction `Measure.IsCondKernel`. -/
instance instIsCondKernel [hκ : IsRegularCondDistrib P m Y κ] :
    (@Measure.map Ω (Ω × E) mΩ (m.prod mE) (fun ω ↦ (ω, Y ω)) P).IsCondKernel κ where
  disintegrate := by
    have hm : m ≤ mΩ := hκ.le_ambient
    have hY : @Measurable Ω E mΩ mE Y := hκ.measurable_Y
    have h_id : Measurable[mΩ, m] (fun ω : Ω ↦ ω) := by
      change m ≤ mΩ
      exact hm
    have hfst :
        (@Measure.map Ω (Ω × E) mΩ (m.prod mE) (fun ω ↦ (ω, Y ω)) P).fst =
          P.trim hm := by
      ext s hs
      rw [Measure.fst_apply hs, Measure.map_apply (h_id.prodMk hY) (measurable_fst hs),
        ← Set.prod_univ, Set.mk_preimage_prod]
      rw [trim_measurableSet_eq hm hs]
      simp
    have hmap :
        @Measure.map Ω (Ω × E) mΩ (m.prod mE) (fun ω ↦ (ω, Y ω)) P =
          P.trim hm ⊗ₘ κ := by
      rw [Measure.ext_prod_iff]
      intro s t hs ht
      have hreal :
          (@Measure.map Ω (Ω × E) mΩ (m.prod mE) (fun ω ↦ (ω, Y ω)) P).real (s ×ˢ t) =
              (P.trim hm ⊗ₘ κ).real (s ×ˢ t) ↔
            @Measure.map Ω (Ω × E) mΩ (m.prod mE) (fun ω ↦ (ω, Y ω)) P (s ×ˢ t) =
              (P.trim hm ⊗ₘ κ) (s ×ˢ t) :=
        measureReal_eq_measureReal_iff (measure_lt_top _ _).ne (measure_lt_top _ _).ne
      rw [← hreal]
      rw [measureReal_def, Measure.map_apply (h_id.prodMk hY) (hs.prod ht),
        Set.mk_preimage_prod, Set.inter_comm, measureReal_def, Measure.compProd_apply_prod hs ht]
      rw [← integral_toReal (κ.measurable_coe ht).aemeasurable]
      swap
      · exact Filter.Eventually.of_forall fun ω ↦ measure_lt_top (κ ω) t
      have hκ_trim : (fun ω ↦ (κ ω).real t) =ᵐ[P.trim hm] P⟦Y ⁻¹' t | m⟧ := by
        exact (((κ.measurable_coe ht).ennreal_toReal.stronglyMeasurable).ae_eq_trim_iff hm
          stronglyMeasurable_condExp).2 (hκ.ae_eq_conditionalProbability ht)
      change (P (Y ⁻¹' t ∩ (fun a ↦ a) ⁻¹' s)).toReal = ∫ a in s, (κ a).real t ∂P.trim hm
      rw [integral_congr_ae (ae_restrict_of_ae hκ_trim),
        ← setIntegral_trim hm stronglyMeasurable_condExp hs,
        setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator (hY ht)) hs,
        setIntegral_indicator (hY ht), integral_const, measureReal_restrict_apply_univ,
        smul_eq_mul, mul_one]
      simp [measureReal_def, Set.inter_comm]
    rw [hfst]
    exact hmap.symm

end IsRegularCondDistrib

section CondDistrib

variable [mΩ : MeasurableSpace Ω]
variable {S : Type w} [mS : MeasurableSpace S] [StandardBorelSpace E] [Nonempty E]

/-- The canonical conditional distribution along `X` is a regular conditional distribution of `Y`
given the σ-algebra `σ(X) = mS.comap X`. -/
instance isRegularCondDistrib_condDistrib
    (P : Measure Ω) [IsFiniteMeasure P] {Y : Ω → E} (hY : Measurable Y)
    {X : Ω → S} (hX : Measurable X) :
    IsRegularCondDistrib P (mS.comap X) Y
      ((condDistrib Y X P).comap X (Measurable.of_comap_le le_rfl)) := by
  refine
    { toIsMarkovKernel := inferInstance
      le_ambient := hX.comap_le
      measurable_Y := hY
      ae_eq_conditionalProbability := ?_ }
  intro B hB
  simpa using (condDistrib_ae_eq_condExp hX hY hB :
    (fun ω ↦ (condDistrib Y X P (X ω)).real B) =ᵐ[P] P⟦Y ⁻¹' B | mS.comap X⟧)

end CondDistrib

end ProbabilityTheory

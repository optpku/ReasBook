/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Definition_8_28

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

-- Proof sketch: specialize the canonical `ProbabilityTheory.condDistrib` construction to `X = id`,
-- viewed as a measurable map from `(Ω, mΩ)` to `(Ω, m)` using `hm`.
/-- Theorem 8.29: A real-valued random variable admits a regular conditional distribution given a
sub-σ-algebra `m`. -/
theorem exists_regular_conditional_distribution_real_given
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {Y : Ω → ℝ} (hY : Measurable[mΩ] Y) :
    ∃ κ : Kernel[m] Ω ℝ, IsRegularCondDistrib P m Y κ := by
  have hX : Measurable[mΩ, m] id := by
    rw [measurable_iff_comap_le, MeasurableSpace.comap_id]
    exact hm
  have hκ :
      @IsRegularCondDistrib Ω ℝ inferInstance mΩ P inferInstance (MeasurableSpace.comap id m) Y
        ((condDistrib Y id P).comap id (Measurable.of_comap_le le_rfl)) :=
    @ProbabilityTheory.isRegularCondDistrib_condDistrib Ω ℝ inferInstance mΩ Ω m inferInstance
      inferInstance P inferInstance Y hY id hX
  have hm_id : MeasurableSpace.comap id m = m := MeasurableSpace.comap_id
  let κ : Kernel[m] Ω ℝ := by
    change @Kernel Ω ℝ m inferInstance
    exact hm_id ▸ ((condDistrib Y id P).comap id (Measurable.of_comap_le le_rfl))
  refine ⟨κ, ?_⟩
  subst κ
  convert hκ using 1 <;> simp [hm_id]

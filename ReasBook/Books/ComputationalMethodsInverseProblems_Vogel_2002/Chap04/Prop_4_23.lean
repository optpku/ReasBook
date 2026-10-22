/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_23.Transform

public section

noncomputable section

namespace ProbabilityTheory

universe u v w z

/-- Proposition 4.23. If `Z ω = g (X ω) (Y ω)` for a measurable `g`, then the conditional law of
`Z` given `X` is obtained by pushing forward the conditional law of `Y` given `X` through the
`X`-dependent map `y ↦ g (X ω) y`. -/
theorem condDistrib_mapWithInput
    {Ω : Type u} {α : Type v} {β : Type w} {γ : Type z}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace γ] [Nonempty γ]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {X : Ω → α} {Y : Ω → β} (hY : AEMeasurable Y μ)
    {g : α → β → γ} (hg : Measurable (Function.uncurry g)) :
    condDistrib (fun ω ↦ g (X ω) (Y ω)) X μ =ᵐ[μ.map X]
      Kernel.mapWithInput (condDistrib Y X μ) g := by
  by_cases hX : AEMeasurable X μ
  · -- Package the canonical conditional distribution as a `HasCondDistrib` witness.
    have hcond : HasCondDistrib Y X (condDistrib Y X μ) μ := by
      refine ⟨by fun_prop, ?_⟩
      simpa using (compProd_map_condDistrib (X := X) (Y := Y) (μ := μ) hY).symm
    -- Transport the conditional distribution through the measurable `X`-dependent map `g`.
    have hmap :
        HasCondDistrib (fun ω ↦ g (X ω) (Y ω)) X
          (Kernel.mapWithInput (condDistrib Y X μ) g) μ :=
      hcond.mapWithInput hg
    let κ : Kernel α γ := ((Kernel.id) ×ₖ condDistrib Y X μ).map (Function.uncurry g)
    have hκ : Kernel.mapWithInput (condDistrib Y X μ) g = κ := by
      ext x s hs
      rw [Kernel.mapWithInput_apply (κ := condDistrib Y X μ) (g := g) hg x]
      rw [show κ x s = (((Kernel.id) ×ₖ condDistrib Y X μ).map (Function.uncurry g)) x s by
        rfl]
      rw [Kernel.map_apply' _ hg x hs]
      rw [Kernel.id_prod_apply' (κ := condDistrib Y X μ) x (s := Function.uncurry g ⁻¹' s)
        (hs := hg hs)]
      rw [MeasureTheory.Measure.map_apply hg.of_uncurry_left hs]
      rfl
    -- The transformed random variable is a.e. measurable once both inputs are.
    have hgXY : AEMeasurable (fun ω ↦ g (X ω) (Y ω)) μ := by
      fun_prop
    -- Rewrite the `HasCondDistrib` witness to the explicit kernel used by `condDistrib`.
    have hκmap : μ.map (fun ω ↦ (X ω, g (X ω) (Y ω))) = μ.map X ⊗ₘ κ := by
      simpa [hκ] using hmap.map_eq
    -- Uniqueness of conditional distributions identifies that explicit kernel a.e.
    have hcondEq :
        condDistrib (fun ω ↦ g (X ω) (Y ω)) X μ =ᵐ[μ.map X] κ :=
      condDistrib_ae_eq_of_measure_eq_compProd (X := X) (Y := fun ω ↦ g (X ω) (Y ω))
        (μ := μ) hgXY hκmap
    simpa [hκ] using hcondEq
  · -- If `X` is not a.e. measurable, then `μ.map X = 0`, so the a.e. statement is trivial.
    simp [MeasureTheory.Measure.map_of_not_aemeasurable, hX, Filter.EventuallyEq]

end ProbabilityTheory

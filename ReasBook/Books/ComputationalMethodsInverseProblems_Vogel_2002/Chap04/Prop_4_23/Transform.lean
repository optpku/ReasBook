/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.CondDistrib

public section

noncomputable section

namespace ProbabilityTheory

namespace Kernel

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- The kernel obtained by pairing the input `x` with a `κ x`-sample and then applying the
`x`-dependent transform `fun (x, y) ↦ g x y`. -/
def mapWithInput (κ : Kernel α β) (g : α → β → γ) : Kernel α γ :=
  (Kernel.id ×ₖ κ).map (Function.uncurry g)

/-- Helper for Proposition 4.23: the `x`-dependent pushforward of an s-finite kernel is s-finite. -/
instance (κ : Kernel α β) [IsSFiniteKernel κ] (g : α → β → γ) :
    IsSFiniteKernel (mapWithInput κ g) := by
  dsimp [mapWithInput]
  infer_instance

/-- Pointwise, `Kernel.mapWithInput κ g x` is the pushforward of `κ x` by `g x`. -/
theorem mapWithInput_apply
    (κ : Kernel α β) [IsSFiniteKernel κ] {g : α → β → γ}
    (hg : Measurable (Function.uncurry g)) (x : α) :
    mapWithInput κ g x = (κ x).map (g x) := by
  -- Unfold the kernel transform and evaluate it on measurable sets.
  ext s hs
  rw [mapWithInput, Kernel.map_apply' _ hg x hs]
  rw [Kernel.id_prod_apply' (κ := κ) x (s := Function.uncurry g ⁻¹' s) (hs := hg hs)]
  rw [MeasureTheory.Measure.map_apply hg.of_uncurry_left hs]
  rfl

end Kernel

namespace HasCondDistrib

universe u v w z

variable {Ω : Type u} {α : Type v} {β : Type w} {γ : Type z}
variable [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.SFinite P]
variable {X : Ω → α} {Y : Ω → β} {κ : Kernel α β} [IsSFiniteKernel κ]

omit [MeasureTheory.SFinite P] [IsSFiniteKernel κ] in
/-- A finite kernel realizing the conditional distribution of `Y` given `X` agrees almost
everywhere with `condDistrib Y X P`. -/
theorem condDistrib_ae_eq [StandardBorelSpace β] [Nonempty β]
    [MeasureTheory.IsFiniteMeasure P] [IsFiniteKernel κ] (h : HasCondDistrib Y X κ P) :
    condDistrib Y X P =ᵐ[P.map X] κ :=
  condDistrib_ae_eq_of_measure_eq_compProd X h.aemeasurable_snd h.map_eq

/-- Transport a conditional distribution of `Y` given `X` through an `X`-dependent measurable
transform `g`. -/
theorem mapWithInput
    (h : HasCondDistrib Y X κ P) {g : α → β → γ}
    (hg : Measurable (Function.uncurry g)) :
    HasCondDistrib (fun ω ↦ g (X ω) (Y ω)) X (Kernel.mapWithInput κ g) P where
  map_eq := by
    let F : α × β → α × γ := fun z ↦ (z.1, g z.1 z.2)
    have hF : Measurable F := by
      fun_prop
    -- Rewrite the transformed pair as a pushforward of the original joint law.
    calc
      P.map (fun ω ↦ (X ω, g (X ω) (Y ω)))
          = (P.map (fun ω ↦ (X ω, Y ω))).map F := by
              rw [AEMeasurable.map_map_of_aemeasurable hF.aemeasurable h.aemeasurable]
              rfl
      _ = (P.map X ⊗ₘ κ).map F := by
            rw [h.map_eq]
      _ = P.map X ⊗ₘ Kernel.mapWithInput κ g := by
            ext s hs
            rw [MeasureTheory.Measure.map_apply hF hs]
            rw [MeasureTheory.Measure.compProd_apply (hF hs)]
            rw [MeasureTheory.Measure.compProd_apply hs]
            congr with x
            rw [Kernel.mapWithInput_apply (κ := κ) (g := g) hg x]
            rw [MeasureTheory.Measure.map_apply hg.of_uncurry_left (measurable_prodMk_left hs)]
            rfl

end HasCondDistrib

end ProbabilityTheory

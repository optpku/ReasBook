module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Constructions.SumProd

public section

open Filter
open scoped Topology

namespace Filter.EventuallyEq

/-!
Fixed-coordinate slices of a jointly eventual equality.  The two directions are
kept as separate declarations so callers can use the coordinate that is held
constant without rebuilding the product-filter map.
-/

/-- Infrastructure I.16a: an eventual equality of uncurried maps restricts to
the second-coordinate slice through a fixed first coordinate. -/
theorem uncurry_slice
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f g : α → β → γ} {a : α} {b : β}
    (h : Function.uncurry f =ᶠ[𝓝 (a, b)] Function.uncurry g) :
    f a =ᶠ[𝓝 b] g a := by
  have hslice : Tendsto (fun y : β ↦ (a, y)) (𝓝 b) (𝓝 (a, b)) := by
    exact (continuous_const.prodMk continuous_id).tendsto b
  have hcomp := h.comp_tendsto hslice
  have hleft : Function.uncurry f ∘ (fun y : β ↦ (a, y)) = f a := by
    funext y
    rfl
  have hright : Function.uncurry g ∘ (fun y : β ↦ (a, y)) = g a := by
    funext y
    rfl
  simpa only [hleft, hright] using hcomp

/-- Helper for Infrastructure I.16a: an eventual equality of uncurried maps
restricts to the first-coordinate slice through a fixed second coordinate. -/
theorem uncurry_slice_left
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f g : α → β → γ} {a : α} {b : β}
    (h : Function.uncurry f =ᶠ[𝓝 (a, b)] Function.uncurry g) :
    (fun x : α ↦ f x b) =ᶠ[𝓝 a] (fun x : α ↦ g x b) := by
  have hslice : Tendsto (fun x : α ↦ (x, b)) (𝓝 a) (𝓝 (a, b)) := by
    exact (continuous_id.prodMk continuous_const).tendsto a
  have hcomp := h.comp_tendsto hslice
  have hleft : Function.uncurry f ∘ (fun x : α ↦ (x, b)) = (fun x : α ↦ f x b) := by
    funext x
    rfl
  have hright : Function.uncurry g ∘ (fun x : α ↦ (x, b)) = (fun x : α ↦ g x b) := by
    funext x
    rfl
  simpa only [hleft, hright] using hcomp

end Filter.EventuallyEq

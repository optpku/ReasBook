import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic

/-- A subset of `ι → ℝ` is integral if it is the convex hull of its integer points. -/
def is_integral {ι : Type*} (P : Set (ι → ℝ)) : Prop :=
  P =
    convexHull ℝ
      (P ∩ Set.range (fun z : ι → ℤ ↦ Int.cast ∘ z))

/-- A subset of `ι → ℝ` is integral exactly when it equals the convex hull of its integer points. -/
theorem is_integral_iff {ι : Type*} {P : Set (ι → ℝ)} :
    is_integral P ↔
      P =
        convexHull ℝ
          (P ∩ Set.range (fun z : ι → ℤ ↦ Int.cast ∘ z)) :=
  Iff.rfl

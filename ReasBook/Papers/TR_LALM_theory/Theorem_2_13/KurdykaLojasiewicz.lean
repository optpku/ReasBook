/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Deriv

public section

open Filter Set Topology

namespace KurdykaLojasiewicz

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type v}

/-- A Kurdyka--Łojasiewicz desingularizer on `[0, η)` is nonnegative,
continuous at zero, `C¹` on `(0, η)`, concave, normalized at zero, and has
positive derivative on `(0, η)`. -/
def IsDesingularizer (η : ℝ) (φ : ℝ → ℝ) : Prop :=
  MapsTo φ (Ico 0 η) (Ici 0) ∧
    ContinuousWithinAt φ (Ico 0 η) 0 ∧
    φ 0 = 0 ∧
    ContDiffOn ℝ 1 φ (Ioo 0 η) ∧
    (∀ s ∈ Ioo 0 η, 0 < deriv φ s) ∧
    ConcaveOn ℝ (Ico 0 η) φ

/-- The defining conditions of a Kurdyka--Łojasiewicz desingularizer. -/
theorem isDesingularizer_iff (η : ℝ) (φ : ℝ → ℝ) :
    IsDesingularizer η φ ↔
      MapsTo φ (Ico 0 η) (Ici 0) ∧
        ContinuousWithinAt φ (Ico 0 η) 0 ∧
        φ 0 = 0 ∧
        ContDiffOn ℝ 1 φ (Ioo 0 η) ∧
        (∀ s ∈ Ioo 0 η, 0 < deriv φ s) ∧
        ConcaveOn ℝ (Ico 0 η) φ := Iff.rfl

/-- An energy has the Kurdyka--Łojasiewicz property at a point when a positive
energy window admits a concave desingularizer with positive derivative whose
gradient inequality holds locally above the energy of the point. -/
def HasAt (energy : H → ℝ) (xBar : H) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ φ : ℝ → ℝ,
    IsDesingularizer η φ ∧
      ∀ᶠ x in 𝓝 xBar,
        energy xBar < energy x → energy x < energy xBar + η →
          1 ≤ deriv φ (energy x - energy xBar) * ‖gradient energy x‖

/-- The Kurdyka--Łojasiewicz property exposes its energy window, desingularizer,
regularity conditions, and local gradient inequality. -/
theorem hasAt_iff (energy : H → ℝ) (xBar : H) :
    HasAt energy xBar ↔
      ∃ η : ℝ, 0 < η ∧ ∃ φ : ℝ → ℝ,
        IsDesingularizer η φ ∧
          ∀ᶠ x in 𝓝 xBar,
            energy xBar < energy x → energy x < energy xBar + η →
              1 ≤ deriv φ (energy x - energy xBar) * ‖gradient energy x‖ := Iff.rfl

/-- An energy has the Kurdyka--Łojasiewicz property at every cluster point of a
map along a filter. -/
def HasAtClusterPoints (energy : H → ℝ) (l : Filter ι) (u : ι → H) : Prop :=
  ∀ xBar, MapClusterPt xBar l u → HasAt energy xBar

/-- The cluster-point Kurdyka--Łojasiewicz hypothesis is pointwise `HasAt` at
every mapped cluster point. -/
theorem hasAtClusterPoints_iff (energy : H → ℝ) (l : Filter ι) (u : ι → H) :
    HasAtClusterPoints energy l u ↔
      ∀ xBar, MapClusterPt xBar l u → HasAt energy xBar := Iff.rfl

end KurdykaLojasiewicz

end

/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_6
import Mathlib.Analysis.Meromorphic.Order

open scoped ContDiff Manifold
open TopologicalSpace

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `MeromorphicAt`, `MeromorphicOn`, `meromorphicOrderAt`,
  `tendsto_cobounded_iff_meromorphicOrderAt_neg`.
- Verified locally: root-level planar meromorphic notions live in
  `Mathlib.Analysis.Meromorphic.*`, while open subsets of a complex `1`-manifold inherit the
  ambient `IsManifold` structure needed to make chartwise meromorphicity intrinsic.
- Owner choice: keep the textbook owner as a surface-level predicate on total maps `f : Y → ℂ`,
  but place it at the inherited complex-manifold layer rather than bare `ChartedSpace`; the pole
  criterion is stated with the natural local meromorphicity hypothesis at the point.
-/

namespace RiemannSurface

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- A complex-valued function on a complex `1`-manifold is meromorphic at a point when its
expression in a local chart at that point is meromorphic in the usual planar sense. -/
def MeromorphicAt [IsManifold (𝓘(ℂ)) ω M] (f : M → ℂ) (x : M) : Prop :=
  _root_.MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

/-- Meromorphicity at a point is exactly planar meromorphicity of the chosen coordinate
expression. -/
theorem meromorphicAt_iff_coord [IsManifold (𝓘(ℂ)) ω M] (f : M → ℂ) (x : M) :
    MeromorphicAt f x ↔
      _root_.MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
  Iff.rfl

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Definition 1.12: a function on an open subset of a Riemann surface is meromorphic when it is
meromorphic at each point of that open subset, using the inherited complex-manifold structure on
the open-subset carrier. This keeps the source's partial-holomorphic presentation in a canonical
total-function API on `Y : Opens X`, while requiring the ambient chart changes to be holomorphic. -/
def MeromorphicOn [IsManifold (𝓘(ℂ)) ω X] (Y : Opens X) (f : Y → ℂ) : Prop :=
  ∀ y : Y, MeromorphicAt f y

/-- Meromorphicity on an open subset is the pointwise meromorphic-at condition. -/
theorem meromorphicOn_iff_forall [IsManifold (𝓘(ℂ)) ω X] (Y : Opens X) (f : Y → ℂ) :
    MeromorphicOn Y f ↔ ∀ y : Y, MeromorphicAt f y :=
  Iff.rfl

/-- Meromorphicity on an open subset is equivalent to planar meromorphicity of the local
coordinate expression at every point. -/
theorem meromorphicOn_iff_chartwise [IsManifold (𝓘(ℂ)) ω X] (Y : Opens X) (f : Y → ℂ) :
    MeromorphicOn Y f ↔
      ∀ y : Y,
        _root_.MeromorphicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y) := by
  simp [MeromorphicOn, meromorphicAt_iff_coord]

namespace HolomorphicOn

/-- A holomorphic function on an open subset of a complex `1`-manifold, hence in particular of a
Riemann surface, is meromorphic there. -/
theorem meromorphicOn [IsManifold (𝓘(ℂ)) ω X] (Y : Opens X) {f : Y → ℂ} :
    HolomorphicOn Y f → MeromorphicOn Y f := sorry

end HolomorphicOn

/-- The set of meromorphic functions on an open subset of a Riemann surface. -/
def meromorphicFunctions [IsManifold (𝓘(ℂ)) ω X] (Y : Opens X) : Set (Y → ℂ) :=
  {f | MeromorphicOn Y f}

notation "𝓜(" Y ")" => meromorphicFunctions Y

/-- Membership in `𝓜(Y)` is equivalent to meromorphicity on `Y`. -/
theorem mem_meromorphicFunctions [IsManifold (𝓘(ℂ)) ω X] (Y : Opens X) (f : Y → ℂ) :
    f ∈ 𝓜(Y) ↔ MeromorphicOn Y f :=
  Iff.rfl

/-- A point of an open subset is a pole when the local meromorphic order of the coordinate
expression is negative. -/
def IsPoleAt [IsManifold (𝓘(ℂ)) ω X] {Y : Opens X} (f : Y → ℂ) (x : Y) : Prop :=
  meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) < 0

/-- At a meromorphic point, being a pole is equivalent to the norm of the local coordinate
expression tending to infinity along the punctured neighborhood. -/
theorem isPoleAt_iff_tendsto_norm_atTop
    [IsManifold (𝓘(ℂ)) ω X] {Y : Opens X} {f : Y → ℂ} {x : Y} (hf : MeromorphicAt f x) :
    IsPoleAt f x ↔
      Filter.Tendsto
        (fun z : ℂ ↦ ‖(f ∘ (chartAt ℂ x).symm) z‖)
        (nhdsWithin (chartAt ℂ x x) {chartAt ℂ x x}ᶜ)
        Filter.atTop := sorry

end RiemannSurface

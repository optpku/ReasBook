/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_6

open scoped Manifold
open TopologicalSpace

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: holomorphic functions form a complex algebra / chartwise holomorphicity.
- Verified locally: `HolomorphicOn`, `holomorphicFunctions`, `MDifferentiable.add`,
  `MDifferentiable.mul`, `mdifferentiable_const`, `mdifferentiable_of_mem_atlas`, and `atlas ℂ Y`.
- Owner choice: keep `HolomorphicOn` and `holomorphicFunctions` as the existing source-facing
  owners, add the canonical `Subalgebra ℂ (Y → ℂ)` companion for part (a), express part (b) on a
  covering family of induced atlas charts on `Y`, and state part (c) for arbitrary atlas charts on
  `X`.
-/

namespace RiemannSurface

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Remark 1.7 (1): the sum of two holomorphic functions on an open subset of a Riemann surface is
again holomorphic. -/
theorem holomorphicOn_add (Y : Opens X) {f g : Y → ℂ} (hf : HolomorphicOn Y f)
    (hg : HolomorphicOn Y g) :
    HolomorphicOn Y (f + g) := by
  simpa [HolomorphicOn] using hf.add hg

/-- Remark 1.7 (2): the product of two holomorphic functions on an open subset of a Riemann
surface is again holomorphic. -/
theorem holomorphicOn_mul (Y : Opens X) {f g : Y → ℂ} (hf : HolomorphicOn Y f)
    (hg : HolomorphicOn Y g) :
    HolomorphicOn Y (f * g) := by
  simpa [HolomorphicOn] using hf.mul hg

/-- Remark 1.7 (3): every constant complex-valued function on an open subset of a Riemann surface
is holomorphic. -/
theorem holomorphicOn_const (Y : Opens X) (c : ℂ) :
    HolomorphicOn Y (fun _ : Y ↦ c) := by
  simpa [HolomorphicOn] using
    (mdifferentiable_const : MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) (fun _ : Y ↦ c))

/-- Remark 1.7 (4): the holomorphic functions on an open subset of a Riemann surface form a
`ℂ`-subalgebra of the algebra of all complex-valued functions on that subset. -/
def holomorphicSubalgebra (Y : Opens X) : Subalgebra ℂ (Y → ℂ) where
  carrier := 𝓒(Y)
  zero_mem' := holomorphicOn_const Y 0
  add_mem' := holomorphicOn_add Y
  one_mem' := holomorphicOn_const Y 1
  mul_mem' := holomorphicOn_mul Y
  algebraMap_mem' c := holomorphicOn_const Y c

notation "𝒪(" Y ")" => holomorphicSubalgebra Y

/-- Membership in the holomorphic-function subalgebra is exactly holomorphicity. -/
theorem mem_holomorphicSubalgebra (Y : Opens X) (f : Y → ℂ) :
    f ∈ 𝒪(Y) ↔ HolomorphicOn Y f :=
  Iff.rfl

section

variable [RiemannSurface X]

/-- Remark 1.7 (5): to verify holomorphicity it suffices to check the coordinate expression on any
family of induced charts covering `Y`, rather than on every chart in the atlas. -/
theorem holomorphicOn_iff_chartwiseOnCover (Y : Opens X) (f : Y → ℂ)
    {S : Set (OpenPartialHomeomorph Y ℂ)} (hS : S ⊆ atlas ℂ Y)
    (hcover : ∀ y : Y, ∃ e ∈ S, y ∈ e.source) :
    HolomorphicOn Y f ↔
      ∀ e ∈ S, DifferentiableOn ℂ (f ∘ e.symm) e.target := sorry

/-- Remark 1.7 (6): every complex atlas chart on a Riemann surface is holomorphic when regarded as
a complex-valued function on its source; such a chart is also called a local coordinate or a
uniformizing parameter. -/
theorem atlasChart_holomorphicOn {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X) :
    HolomorphicOn (⟨e.source, e.open_source⟩ : Opens X) (fun x ↦ e x) := sorry

end

end RiemannSurface

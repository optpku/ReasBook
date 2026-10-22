/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_12

open scoped ContDiff Manifold
open TopologicalSpace

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`,
  `MeromorphicOn.add`, `MeromorphicOn.fun_mul`.
- Verified locally: this chapter already uses the surface-level owners
  `RiemannSurface.MeromorphicOn`, `RiemannSurface.IsPoleAt`, and `𝓜(Y)`.
- Owner choice: part (a) is stated as the canonical chartwise meromorphic normal form underlying a
  Laurent expansion at a pole; part (b) keeps `MeromorphicOn` as the source-facing owner and
  packages the induced algebra structure as a `Subalgebra ℂ (Y → ℂ)` whose carrier is exactly
  `𝓜(Y)`.
-/

namespace RiemannSurface

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Remark 1.13 (1): on an open subset of a complex `1`-manifold, hence in particular of a
Riemann surface, if `x` is a pole of a meromorphic function and the chosen local coordinate is
normalized by `z(x) = 0`, then the coordinate expression of the function has the usual
Laurent-type normal form near `x`. -/
theorem exists_coordLaurentNormalFormAtPole
    [IsManifold (𝓘(ℂ)) ω X]
    {Y : Opens X} {f : Y → ℂ} {x : Y} (hx : IsPoleAt f x) (hzero : chartAt ℂ x x = 0) :
    ∃ n : ℕ,
      0 < n ∧
      ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧
        (f ∘ (chartAt ℂ x).symm) =ᶠ[nhdsWithin 0 {0}ᶜ]
          fun z : ℂ ↦ z ^ (-(n : ℤ)) * g z := sorry

section

variable [IsManifold (𝓘(ℂ)) ω X]

namespace MeromorphicOn

/-- Constant complex-valued functions on `Y` are meromorphic. -/
theorem const (Y : Opens X) (c : ℂ) :
    MeromorphicOn Y (fun _ : Y ↦ c) := by
  intro y
  change _root_.MeromorphicAt (((fun _ : Y ↦ c) : Y → ℂ) ∘ (chartAt ℂ y).symm) (chartAt ℂ y y)
  fun_prop

/-- The sum of two meromorphic functions on `Y` is meromorphic. -/
theorem add {Y : Opens X} {f g : Y → ℂ} (hf : MeromorphicOn Y f) (hg : MeromorphicOn Y g) :
    MeromorphicOn Y (f + g) := by
  intro y
  change _root_.MeromorphicAt ((f + g) ∘ (chartAt ℂ y).symm) (chartAt ℂ y y)
  simpa [Function.comp, Pi.add_apply] using (hf y).add (hg y)

/-- The product of two meromorphic functions on `Y` is meromorphic. -/
theorem mul {Y : Opens X} {f g : Y → ℂ} (hf : MeromorphicOn Y f) (hg : MeromorphicOn Y g) :
    MeromorphicOn Y (f * g) := by
  intro y
  change _root_.MeromorphicAt ((f * g) ∘ (chartAt ℂ y).symm) (chartAt ℂ y y)
  simpa [Function.comp, Pi.mul_apply] using (hf y).mul (hg y)

end MeromorphicOn

/-- Remark 1.13 (2): the meromorphic functions on an open subset of a complex `1`-manifold, hence
in particular of a Riemann surface, form a natural `ℂ`-subalgebra of the algebra of all
complex-valued functions on that open subset. -/
def meromorphicSubalgebra (Y : Opens X) : Subalgebra ℂ (Y → ℂ) where
  carrier := 𝓜(Y)
  zero_mem' := by
    simpa [mem_meromorphicFunctions] using (MeromorphicOn.const Y (0 : ℂ))
  add_mem' := by
    intro f g hf hg
    simpa [mem_meromorphicFunctions] using
      (hf : MeromorphicOn Y f).add (hg : MeromorphicOn Y g)
  mul_mem' := by
    intro f g hf hg
    simpa [mem_meromorphicFunctions] using
      (hf : MeromorphicOn Y f).mul (hg : MeromorphicOn Y g)
  algebraMap_mem' c := by
    simpa [mem_meromorphicFunctions, Pi.algebraMap_apply] using (MeromorphicOn.const Y c)

/-- Membership in the meromorphic subalgebra is equivalent to meromorphicity. -/
theorem mem_meromorphicSubalgebra (Y : Opens X) (f : Y → ℂ) :
    f ∈ meromorphicSubalgebra Y ↔ MeromorphicOn Y f :=
  Iff.rfl

end

end RiemannSurface

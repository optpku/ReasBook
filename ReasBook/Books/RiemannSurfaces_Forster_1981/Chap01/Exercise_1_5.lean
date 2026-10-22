/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_9
import RiemannSurfaces_Forster_1981.Chap01.Example_1_5
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

open scoped MatrixGroups
open scoped Pointwise
open AddAction

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `UpperHalfPlane.coe_specialLinearGroup_apply`,
  `UpperHalfPlane.SLAction`.
- Verified locally: `PeriodPair`, `PeriodPair.lattice`, `Structomorph`,
  `RiemannSurface.Holomorphic`, `RiemannSurface.isomorphic`, and `orbitRel.Quotient`.
- Owner choice: attach the torus quotient directly to its period-pair owner as `L.Torus`, and
  attach the standard pair and torus for `τ : UpperHalfPlane` to that owner as
  `UpperHalfPlane.periodPair τ` and `X(τ)`. The modular transformation in part (c) is expressed by
  the canonical `SL(2, ℤ)` action on `UpperHalfPlane`.
-/

/-- Auxiliary linear independence for the standard torus periods `1` and `τ`. -/
private theorem oneAndTauLinearIndependent (τ : UpperHalfPlane) :
    LinearIndependent ℝ ![(1 : ℂ), (τ : ℂ)] := sorry

namespace UpperHalfPlane

/-- The standard period pair attached to `τ ∈ ℍ`, corresponding to the lattice
`ℤ + ℤ τ ⊂ ℂ`. -/
def periodPair (τ : UpperHalfPlane) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := oneAndTauLinearIndependent τ

/-- The first standard period attached to `τ ∈ ℍ` is `1`. -/
@[simp] theorem periodPair_omega1 (τ : UpperHalfPlane) :
    τ.periodPair.ω₁ = 1 :=
  rfl

/-- The second standard period attached to `τ ∈ ℍ` is `τ`. -/
@[simp] theorem periodPair_omega2 (τ : UpperHalfPlane) :
    τ.periodPair.ω₂ = τ :=
  rfl

end UpperHalfPlane

namespace PeriodPair

/-- The complex torus attached to a period pair `L`, realized as the quotient `ℂ / L.lattice`. -/
abbrev Torus (L : PeriodPair) :=
  orbitRel.Quotient L.lattice.toAddSubgroup ℂ

/-- Multiplication by `α` on `ℂ` descends to the quotient tori whenever it sends the lattice of
`L` into the lattice of `L'`. -/
def smulTorusMap (L L' : PeriodPair) (α : ℂ)
    (hα : α • (L.lattice : Set ℂ) ⊆ (L'.lattice : Set ℂ)) :
    L.Torus → L'.Torus :=
  Quotient.map' (fun z : ℂ ↦ α * z) fun z w hzw ↦ by
    rw [orbitRel_apply] at hzw ⊢
    rcases hzw with ⟨g, hg⟩
    have hαg : α * (g : ℂ) ∈ (L'.lattice : Set ℂ) := by
      apply hα
      refine ⟨(g : ℂ), g.2, ?_⟩
      simp [smul_eq_mul]
    refine ⟨⟨α * g, hαg⟩, ?_⟩
    have hg' : (g : ℂ) + w = z := by
      simpa [vadd_eq_add] using hg
    change α * (g : ℂ) + α * w = α * z
    rw [← hg']
    ring

/-- On quotient representatives, `smulTorusMap` is induced by multiplication by `α`. -/
@[simp] theorem smulTorusMap_mk (L L' : PeriodPair) (α : ℂ)
    (hα : α • (L.lattice : Set ℂ) ⊆ (L'.lattice : Set ℂ)) (z : ℂ) :
    L.smulTorusMap L' α hα (Quotient.mk'' z) = Quotient.mk'' (α * z) := by
  simp [smulTorusMap]

end PeriodPair

namespace UpperHalfPlane

/-- The standard complex torus attached to `τ ∈ ℍ`. -/
abbrev torus (τ : UpperHalfPlane) :=
  τ.periodPair.Torus

end UpperHalfPlane

notation "X(" τ ")" => UpperHalfPlane.torus τ

/-- Exercise 1.5 (1): if multiplication by `α` sends the lattice of `L` into the lattice of `L'`,
then the induced map between the associated complex tori is holomorphic. -/
theorem latticeMul_descendsToHolomorphicTorusMap (L L' : PeriodPair) (α : ℂ)
    (hα : α • (L.lattice : Set ℂ) ⊆ (L'.lattice : Set ℂ)) :
    RiemannSurface.Holomorphic (L.smulTorusMap L' α hα) := sorry

/-- Exercise 1.5 (1), source-facing existence form: the descended multiplication map on the torus is
represented by the canonical quotient map `PeriodPair.smulTorusMap`. -/
theorem latticeMul_descendsToHolomorphicTorusMap_exists (L L' : PeriodPair) (α : ℂ)
    (hα : α • (L.lattice : Set ℂ) ⊆ (L'.lattice : Set ℂ)) :
    ∃ f : L.Torus → L'.Torus,
      RiemannSurface.Holomorphic f ∧
        ∀ z : ℂ, f (Quotient.mk'' z) = Quotient.mk'' (α * z) := by
  refine ⟨L.smulTorusMap L' α hα, latticeMul_descendsToHolomorphicTorusMap L L' α hα,
    ?_⟩
  intro z
  simp

/-- Exercise 1.5 (2): the descended map attached to multiplication by `α` is biholomorphic exactly
when the scaled source lattice equals the target lattice. -/
theorem latticeMul_descendsToBiholomorph_iff (L L' : PeriodPair) (α : ℂ)
    :
    (∃ F : Structomorph biholomorphicGroupoid
        L.Torus
        L'.Torus,
      ∀ z : ℂ, F.toHomeomorph (Quotient.mk'' z) = Quotient.mk'' (α * z)) ↔
        α • (L.lattice : Set ℂ) = (L'.lattice : Set ℂ) := sorry

/-- Exercise 1.5 (3): every complex torus `ℂ / Γ` is isomorphic to a torus of the form
`ℂ / (ℤ + ℤ τ)` for some `τ` with positive imaginary part. -/
theorem torus_isomorphic_standardTorus (L : PeriodPair) :
    ∃ τ : UpperHalfPlane,
      RiemannSurface.isomorphic L.Torus X(τ) := sorry

/-- Exercise 1.5 (4): if `τ' = (aτ + b) / (cτ + d)` for a matrix
`((a, b), (c, d)) ∈ SL(2, ℤ)`, then the standard tori `X(τ)` and `X(τ')` are isomorphic; in the
canonical API this is `τ' = A • τ`. -/
theorem standardTorus_isomorphic_of_sl2z (τ : UpperHalfPlane) (A : SL(2, ℤ)) :
    RiemannSurface.isomorphic X(τ) X(A • τ) := sorry

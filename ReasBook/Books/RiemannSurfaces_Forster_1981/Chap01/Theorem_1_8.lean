/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_6
import Mathlib.Topology.Bornology.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

open scoped ContDiff Manifold
open TopologicalSpace

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `Complex.differentiableOn_update_limUnder_of_bddAbove`.
- Verified locally: `HolomorphicOn`, `Bornology.IsBounded`, and the punctured-open packaging once
  the necessary separation hypothesis is made explicit.
- Owner choice: keep the source-facing extension theorem on an open subset of a complex manifold,
  with a thin `puncturedOpen` companion matching the existing `HolomorphicOn : Opens X → _` API;
  this then specializes directly to the Riemann-surface setting used in the text.
-/

namespace RiemannSurface

section PuncturedOpen

variable {X : Type u} [TopologicalSpace X] [T1Space X]

/-- The punctured open subset `U \ {a}` of an open subset `U` of `X`. -/
def puncturedOpen (U : Opens X) (a : U) : Opens X :=
  ⟨(U : Set X) \ {a.1}, U.isOpen.sdiff isClosed_singleton⟩

/-- Membership in `puncturedOpen U a` means lying in `U` and being different from `a`. -/
theorem mem_puncturedOpen (U : Opens X) (a : U) {x : X} :
    x ∈ puncturedOpen U a ↔ x ∈ (U : Set X) ∧ x ≠ a.1 := by
  simp [puncturedOpen]

/-- The canonical inclusion from the punctured open subset into the ambient open subset. -/
def puncturedOpenInclusion (U : Opens X) (a : U) : puncturedOpen U a → U :=
  fun z ↦ ⟨z.1, z.2.1⟩

@[simp] theorem puncturedOpenInclusion_apply (U : Opens X) (a : U) (z : puncturedOpen U a) :
    puncturedOpenInclusion U a z = ⟨z.1, z.2.1⟩ :=
  rfl

end PuncturedOpen

section HolomorphicExtension

variable {X : Type u} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]

/-- `HolomorphicExtensionOn U a f ftilde` means that `ftilde` is holomorphic on `U` and extends
`f` across the puncture at `a`. -/
def HolomorphicExtensionOn (U : Opens X) (a : U) (f : puncturedOpen U a → ℂ) (ftilde : U → ℂ) :
    Prop :=
  HolomorphicOn U ftilde ∧ ftilde ∘ puncturedOpenInclusion U a = f

/-- A function is a holomorphic extension across the puncture exactly when it is holomorphic on the
ambient open set and agrees with the given punctured function away from the puncture. -/
theorem holomorphicExtensionOn_iff (U : Opens X) (a : U) (f : puncturedOpen U a → ℂ)
    (ftilde : U → ℂ) :
    HolomorphicExtensionOn U a f ftilde ↔
      HolomorphicOn U ftilde ∧ ftilde ∘ puncturedOpenInclusion U a = f :=
  Iff.rfl

/-- An extension across the puncture is holomorphic on the ambient open subset. -/
theorem HolomorphicExtensionOn.holomorphicOn {U : Opens X} {a : U}
    {f : puncturedOpen U a → ℂ} {ftilde : U → ℂ}
    (h : HolomorphicExtensionOn U a f ftilde) :
    HolomorphicOn U ftilde :=
  h.1

/-- An extension across the puncture agrees with the punctured function after restriction. -/
theorem HolomorphicExtensionOn.comp_puncturedOpenInclusion {U : Opens X} {a : U}
    {f : puncturedOpen U a → ℂ} {ftilde : U → ℂ}
    (h : HolomorphicExtensionOn U a f ftilde) :
    ftilde ∘ puncturedOpenInclusion U a = f :=
  h.2

/-- Pointwise form of the extension property. -/
theorem HolomorphicExtensionOn.apply_eq {U : Opens X} {a : U}
    {f : puncturedOpen U a → ℂ} {ftilde : U → ℂ}
    (h : HolomorphicExtensionOn U a f ftilde) (z : puncturedOpen U a) :
    ftilde (puncturedOpenInclusion U a z) = f z :=
  congrFun h.2 z

/-- `BoundedAtPuncture U a f` means that `f` is bounded along the punctured neighborhood filter of
`a` inside `U`. This is the canonical filter-level form of being bounded near the puncture. -/
def BoundedAtPuncture (U : Opens X) (a : U) (f : puncturedOpen U a → ℂ) : Prop :=
  Filter.BoundedAtFilter
    (Filter.comap (puncturedOpenInclusion U a) (nhdsWithin a ({a}ᶜ : Set U))) f

/-- Filter-level boundedness at the puncture is equivalent to boundedness on some punctured
neighborhood of `a` in the ambient space. -/
theorem boundedAtPuncture_iff (U : Opens X) (a : U) (f : puncturedOpen U a → ℂ) :
    BoundedAtPuncture U a f ↔
      ∃ V : Opens X, a.1 ∈ V ∧
        Bornology.IsBounded (f '' {z : puncturedOpen U a | z.1 ∈ (V : Set X)}) := sorry

end HolomorphicExtension

section LocalComplexManifold

variable {X : Type u} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Two holomorphic extensions across the same puncture agree. This is a local uniqueness
statement, so it only uses the ambient complex-manifold structure needed to speak about
holomorphicity on the open subset. -/
theorem HolomorphicExtensionOn.unique {U : Opens X} {a : U}
    {f : puncturedOpen U a → ℂ} {ftilde gtilde : U → ℂ}
    (hftilde : HolomorphicExtensionOn U a f ftilde)
    (hgtilde : HolomorphicExtensionOn U a f gtilde) :
    ftilde = gtilde := sorry

/-- Theorem 1.8: if a holomorphic function on the punctured open subset `U \ {a}` is bounded near
`a`, then it admits a unique holomorphic extension to `U`. The boundedness hypothesis is stated in
the canonical filter form `BoundedAtPuncture U a f`; the companion theorem
`boundedAtPuncture_iff` recovers the textbook neighborhood formulation. The Lean statement keeps
only the local complex-manifold assumptions actually used by the theorem, so it applies in
particular on any Riemann surface. -/
theorem riemannRemovableSingularities (U : Opens X) (a : U) (f : puncturedOpen U a → ℂ)
    (hf : HolomorphicOn (puncturedOpen U a) f) (hbounded : BoundedAtPuncture U a f) :
    ∃! ftilde : U → ℂ, HolomorphicExtensionOn U a f ftilde := sorry

/-- Theorem 1.8 (1): if a holomorphic function on the punctured open subset `U \ {a}` is bounded
in some neighborhood of `a`, then it extends to a holomorphic function on `U`. The neighborhood
need not be stated as contained in `U`, since the function is already only evaluated on
`puncturedOpen U a`. This is the source-facing neighborhood version of
`riemannRemovableSingularities`, stated on the same local complex-manifold hypotheses. -/
theorem riemannRemovableSingularitiesExists (U : Opens X) (a : U) (f : puncturedOpen U a → ℂ)
    (hf : HolomorphicOn (puncturedOpen U a) f)
    (hbounded : ∃ V : Opens X, a.1 ∈ V ∧
      Bornology.IsBounded (f '' {z : puncturedOpen U a | z.1 ∈ (V : Set X)})) :
    ∃ ftilde : U → ℂ, HolomorphicExtensionOn U a f ftilde := by
  rcases riemannRemovableSingularities U a f hf ((boundedAtPuncture_iff U a f).2 hbounded) with
    ⟨ftilde, hftilde, _⟩
  exact ⟨ftilde, hftilde⟩

/-- Theorem 1.8 (2): a holomorphic extension across the puncture is unique. -/
theorem riemannRemovableSingularitiesUnique (U : Opens X) (a : U) (f : puncturedOpen U a → ℂ)
    {ftilde gtilde : U → ℂ} (hftilde : HolomorphicExtensionOn U a f ftilde)
    (hgtilde : HolomorphicExtensionOn U a f gtilde) :
    ftilde = gtilde :=
  HolomorphicExtensionOn.unique hftilde hgtilde

end LocalComplexManifold

end RiemannSurface

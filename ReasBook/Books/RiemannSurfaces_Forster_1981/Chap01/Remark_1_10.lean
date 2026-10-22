/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_9
import RiemannSurfaces_Forster_1981.Chap01.Remark_1_7

open scoped Manifold
open TopologicalSpace

universe u v w

noncomputable section

/- Semantic recall:
- `lean_leansearch`: pullback algebra hom on sections/continuous functions, manifold
  differentiability composition.
- Verified locally: `RiemannSurface.Holomorphic`, `HolomorphicOn`, `𝒪`,
  `ContinuousMap.comp`, `Opens.comap`, `Opens.comap_comap`, `Subalgebra.comap`,
  `Subalgebra.val`, and `AlgHom.codRestrict`.
- Owner choice: keep the existing `Holomorphic` and `HolomorphicOn` predicates as the source-facing
  owners, represent holomorphic functions on `V` by `𝒪(V)`, and encode pullback by explicit
  precomposition on function algebras before restricting to holomorphic functions.
-/

namespace RiemannSurface

section

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
variable {Z : Type w} [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- Remark 1.10 (1): for maps into `ℂ`, holomorphicity as a map of Riemann surfaces is the same as
holomorphicity as a complex-valued function on the whole surface; this criterion already depends
only on the underlying complex-charted-space structure. -/
theorem holomorphic_iff_holomorphicOn_univ (f : X → ℂ) :
    Holomorphic f ↔ HolomorphicOn (⊤ : Opens X) (fun x : (⊤ : Opens X) ↦ f x) := sorry

/- Composition recall for Remark 1.10: holomorphic maps are closed under composition by
`RiemannSurface.holomorphic_comp`. -/
#check holomorphic_comp

end

section Pullback

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]
variable {Z : Type w} [TopologicalSpace Z]

/-- Precomposition with a continuous map pulls complex-valued functions on an open subset of the
target back to complex-valued functions on its open preimage, as a `ℂ`-algebra homomorphism. -/
def pullbackAlgHom (f : C(X, Y)) (V : Opens Y) :
    (V → ℂ) →ₐ[ℂ] (Opens.comap f V → ℂ) where
  toFun ψ := fun x ↦ ψ ⟨f x, x.2⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' c := by
    ext x
    rfl

/-- Pullback on ambient function algebras acts by composition. -/
theorem pullbackAlgHom_apply (f : C(X, Y)) (V : Opens Y) (ψ : V → ℂ)
    (x : Opens.comap f V) :
    pullbackAlgHom f V ψ x = ψ ⟨f x, x.2⟩ := rfl

/-- Pullback along a composite continuous map is the composite of the ambient pullback algebra
homomorphisms. -/
theorem pullbackAlgHom_comp (f : C(X, Y)) (g : C(Y, Z)) (W : Opens Z) :
    pullbackAlgHom (g.comp f) W =
      (pullbackAlgHom f (Opens.comap g W)).comp (pullbackAlgHom g W) := by
  ext ψ x
  rfl

end Pullback

section

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
variable {Z : Type w} [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- The continuous map underlying a holomorphic map of Riemann surfaces. -/
abbrev continuousMapOfHolomorphic (f : X → Y) (hf : Holomorphic f) : C(X, Y) where
  toFun := f
  continuous_toFun := holomorphic_continuous hf

/-- The bundled continuous map underlying a holomorphic map agrees pointwise with the original
function. -/
theorem continuousMapOfHolomorphic_apply (f : X → Y) (hf : Holomorphic f) (x : X) :
    continuousMapOfHolomorphic f hf x = f x := rfl

/-- Bundling a composite holomorphic map as a continuous map agrees with composing the bundled
continuous maps. -/
theorem continuousMapOfHolomorphic_comp (f : X → Y) (g : Y → Z)
    (hf : Holomorphic f) (hg : Holomorphic g) :
    continuousMapOfHolomorphic (g ∘ f) (holomorphic_comp hf hg) =
      (continuousMapOfHolomorphic g hg).comp (continuousMapOfHolomorphic f hf) := by
  ext x
  rfl

/-- Remark 1.10 (2): for a continuous map between complex-charted spaces, hence in particular
between Riemann surfaces, holomorphicity is equivalent to stability of the holomorphic-function
subalgebra under pullback on every open subset of the target. -/
theorem holomorphic_iff_holomorphicSubalgebra_le_comap (f : C(X, Y)) :
    Holomorphic (f : X → Y) ↔
      ∀ V : Opens Y, 𝒪(V) ≤ (𝒪(Opens.comap f V)).comap (pullbackAlgHom f V) := sorry

/-- Remark 1.10 (2): for a continuous map between complex-charted spaces, hence in particular
between Riemann surfaces, holomorphicity is equivalent to pullback preserving holomorphic
functions on every open subset of the target. -/
theorem holomorphic_iff_pullback_mem_holomorphicSubalgebra (f : C(X, Y)) :
    Holomorphic (f : X → Y) ↔
      ∀ V : Opens Y, ∀ ψ : V → ℂ,
        ψ ∈ 𝒪(V) →
          pullbackAlgHom f V ψ ∈ 𝒪(Opens.comap f V) := by
  constructor
  · intro hf V ψ hψ
    exact ((holomorphic_iff_holomorphicSubalgebra_le_comap f).1 hf V hψ : _)
  · intro h
    refine (holomorphic_iff_holomorphicSubalgebra_le_comap f).2 ?_
    intro V ψ hψ
    exact h V ψ hψ

/-- A holomorphic map between complex-charted spaces pulls holomorphic functions back to
holomorphic functions on open preimages. -/
theorem pullbackAlgHom_mem_holomorphicSubalgebra
    (f : C(X, Y)) (hf : Holomorphic (f : X → Y))
    (V : Opens Y) {ψ : V → ℂ} (hψ : ψ ∈ 𝒪(V)) :
    pullbackAlgHom f V ψ ∈ 𝒪(Opens.comap f V) :=
  (holomorphic_iff_pullback_mem_holomorphicSubalgebra f).1 hf V ψ hψ

/-- Remark 1.10 (3): a holomorphic map between complex-charted spaces, hence in particular between
Riemann surfaces, induces a pullback `ℂ`-algebra homomorphism on holomorphic functions over any
open subset of the target. -/
def holomorphicPullback (f : X → Y) (hf : Holomorphic f) (V : Opens Y) :
    𝒪(V) →ₐ[ℂ] 𝒪(Opens.comap (continuousMapOfHolomorphic f hf) V) :=
  (((pullbackAlgHom (continuousMapOfHolomorphic f hf) V).comp (Subalgebra.val _)).codRestrict
    (𝒪(Opens.comap (continuousMapOfHolomorphic f hf) V))
    fun ψ ↦
      pullbackAlgHom_mem_holomorphicSubalgebra (continuousMapOfHolomorphic f hf) hf V ψ.2)

/-- The induced pullback on holomorphic functions also acts by composition. -/
theorem holomorphicPullback_apply (f : X → Y) (hf : Holomorphic f) (V : Opens Y)
    (ψ : 𝒪(V)) (x : Opens.comap (continuousMapOfHolomorphic f hf) V) :
    ((holomorphicPullback f hf V ψ : 𝒪(Opens.comap (continuousMapOfHolomorphic f hf) V)) :
        Opens.comap (continuousMapOfHolomorphic f hf) V → ℂ) x =
      (ψ : V → ℂ) ⟨f x, x.2⟩ := rfl

/-- Remark 1.10 (4): for holomorphic maps between complex-charted spaces, hence in particular
between Riemann surfaces, pullback along a composite is the composite of the pullback
homomorphisms. -/
theorem holomorphicPullback_comp (f : X → Y) (g : Y → Z) (hf : Holomorphic f)
    (hg : Holomorphic g) (W : Opens Z) :
    holomorphicPullback (g ∘ f) (holomorphic_comp hf hg) W =
      (holomorphicPullback f hf (Opens.comap (continuousMapOfHolomorphic g hg) W)).comp
        (holomorphicPullback g hg W) := by
  ext ψ x
  rfl

end

end RiemannSurface

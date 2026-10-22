/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Pointwise
open Monoid

set_option autoImplicit false

section

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]

/-!
Primary domain: group actions and free products with amalgamation.

Layer triage:
- `source-facing`: two subgroup factors `G₁`, `G₂ ≤ G`, their common subgroup `G₁ ⊓ G₂`, two
  disjoint nonempty subsets `Ω₁`, `Ω₂ ⊆ Ω`, and the ping-pong hypotheses on their setwise images.
- `core/canonical`: `Subgroup` for the subgroup data, pointwise `SMul` on sets for the action
  hypotheses, `Subgroup.inclusion` for the two canonical maps from `G₁ ⊓ G₂`, `Subgroup.relIndex`
  for the relative-index clause, and `Monoid.PushoutI` together with `Monoid.PushoutI.lift` for
  the amalgamated free product and its canonical comparison map into `G`.
- `bridge/view`: the internal Bool-indexed pushout diagram built from those two canonical
  inclusions and the resulting comparison homomorphism from the canonical pushout into `G`;
  Proposition `3-12-5` itself should live on the resulting multiplicative equivalence.

Domain sampling:
1. `Subgroup` and `Subgroup.relIndex` are mathlib's owner abstractions for intersections,
   properness, and relative index.
2. `Subgroup.inclusion inf_le_left` and `Subgroup.inclusion inf_le_right` are the canonical maps
   from `G₁ ⊓ G₂` into `G₁` and `G₂`.
3. The pointwise action `g • Ω₁` on subsets is the canonical owner API for the source conditions
   `Ω₁ (G₁ - H) ⊆ Ω₂`, `Ω₂ (G₂ - H) ⊆ Ω₁`, and `Ωᵢ H ⊆ Ωᵢ`.
4. `Monoid.PushoutI` is the canonical owner abstraction for a free product with an amalgamated
   subgroup, and the source-facing two-factor specialization should therefore be a thin
   abbreviation `Subgroup.amalgamatedProduct G₁ G₂` with named left/right embeddings, not public
   `Bool` indexing.
5. `Monoid.PushoutI.lift`, `Monoid.PushoutI.lift_of`, and `Monoid.PushoutI.lift_base` are the
   canonical owner API for the comparison map from that amalgamated product into `G`.

Primitive vs. derived:
the primitive data are the two subgroups, their common intersection subgroup, the action on `Ω`,
and the setwise ping-pong hypotheses. The two canonical inclusions of `G₁ ⊓ G₂` into `G₁` and
`G₂`, the internal Bool-indexed pushout diagram, and the comparison map into `G` are derived
canonically from that subgroup data and should stay bridge code behind the public
`Subgroup.amalgamatedProduct` owner surface.
-/

namespace Subgroup

section

variable {G : Type u} [Group G]
variable (G₁ G₂ : Subgroup G)

local notation "H" => (G₁ ⊓ G₂ : Subgroup G)
local notation "φ" =>
  (fun b : Bool ↦
    @Bool.rec
      (fun b ↦ H →* Bool.rec G₁ G₂ b)
      (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion inf_le_right)
      b)

private local instance amalgamatedProductDiagramCodomainGroup (b : Bool) :
    Group (Bool.rec G₁ G₂ b) := by
  cases b <;> infer_instance

/-- The amalgamated free product of `G₁` and `G₂` over their intersection `G₁ ⊓ G₂`. -/
abbrev amalgamatedProduct : Type u :=
  Monoid.PushoutI φ

namespace amalgamatedProduct

/-- The canonical left embedding of `G₁` into `Subgroup.amalgamatedProduct G₁ G₂`. -/
abbrev left : G₁ →* Subgroup.amalgamatedProduct G₁ G₂ :=
  @Monoid.PushoutI.of Bool (fun b ↦ Bool.rec G₁ G₂ b) H _ _ φ false

/-- The canonical right embedding of `G₂` into `Subgroup.amalgamatedProduct G₁ G₂`. -/
abbrev right : G₂ →* Subgroup.amalgamatedProduct G₁ G₂ :=
  @Monoid.PushoutI.of Bool (fun b ↦ Bool.rec G₁ G₂ b) H _ _ φ true

end amalgamatedProduct

/-- The canonical comparison homomorphism from the amalgamated product of `G₁` and `G₂` over
their intersection into the ambient group `G`. -/
def amalgamatedProductComparison : Subgroup.amalgamatedProduct G₁ G₂ →* G :=
  Monoid.PushoutI.lift
    (fun b ↦ Bool.rec G₁.subtype G₂.subtype b)
    (Subgroup.subtype H)
    (fun b ↦ by cases b <;> rfl)

end

end Subgroup

variable (G₁ G₂ : Subgroup G)

local notation "H" => (G₁ ⊓ G₂ : Subgroup G)
local notation "φ" =>
  (fun b : Bool ↦
    @Bool.rec
      (fun b ↦ H →* Bool.rec G₁ G₂ b)
      (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion inf_le_right)
      b)

private local instance subgroupPairCodomainGroup (b : Bool) : Group (Bool.rec G₁ G₂ b) := by
  cases b <;> infer_instance

/-- The canonical comparison map from the pushout of the two canonical inclusions
`G₁ ⊓ G₂ ↪ G₁`, `G₁ ⊓ G₂ ↪ G₂` to the ambient group `G`. -/
@[simp] private theorem comparisonMap_left (g : G₁) :
    Subgroup.amalgamatedProductComparison G₁ G₂
      (Subgroup.amalgamatedProduct.left G₁ G₂ g) = g := by
  simp [Subgroup.amalgamatedProductComparison, Subgroup.amalgamatedProduct.left]

@[simp] private theorem comparisonMap_right (g : G₂) :
    Subgroup.amalgamatedProductComparison G₁ G₂
      (Subgroup.amalgamatedProduct.right G₁ G₂ g) = g := by
  simp [Subgroup.amalgamatedProductComparison, Subgroup.amalgamatedProduct.right]

variable
    (hgen : G₁ ⊔ G₂ = ⊤)
    (hproper₁ : (G₁ ⊓ G₂ : Subgroup G) < G₁)
    (hproper₂ : (G₁ ⊓ G₂ : Subgroup G) < G₂)
    (hnot_indexTwo :
      ¬ (((G₁ ⊓ G₂ : Subgroup G)).relIndex G₁ = 2 ∧
          ((G₁ ⊓ G₂ : Subgroup G)).relIndex G₂ = 2))
    (Ω₁ Ω₂ : Set Ω)
    (hΩ₁ : Ω₁.Nonempty)
    (hΩ₂ : Ω₂.Nonempty)
    (hdisj : Disjoint Ω₁ Ω₂)
    (h₁₂ : ∀ g : G₁, (g : G) ∉ (G₁ ⊓ G₂ : Subgroup G) → (g : G) • Ω₁ ⊆ Ω₂)
    (h₂₁ : ∀ g : G₂, (g : G) ∉ (G₁ ⊓ G₂ : Subgroup G) → (g : G) • Ω₂ ⊆ Ω₁)
    (hH₁ : ∀ h : (G₁ ⊓ G₂ : Subgroup G), (h : G) • Ω₁ ⊆ Ω₁)
    (hH₂ : ∀ h : (G₁ ⊓ G₂ : Subgroup G), (h : G) • Ω₂ ⊆ Ω₂)

-- Proof sketch: use the relative-index hypothesis to make one of the ping-pong transitions
-- strict, so that every nontrivial alternating reduced word moves one of the two distinguished
-- subsets away from itself. This gives injectivity of the canonical map
-- `comparisonMap G₁ G₂`; surjectivity follows from the generation hypothesis
-- `G₁ ⊔ G₂ = ⊤`.
include hgen hproper₁ hproper₂ hnot_indexTwo Ω₁ Ω₂ hΩ₁ hΩ₂ hdisj h₁₂ h₂₁ hH₁ hH₂ in
private theorem comparisonMap_bijective_of_twoSubsetPingPong :
    Function.Bijective (Subgroup.amalgamatedProductComparison G₁ G₂) := sorry

include hgen hproper₁ hproper₂ hnot_indexTwo Ω₁ Ω₂ hΩ₁ hΩ₂ hdisj h₁₂ h₂₁ hH₁ hH₂
/-- Proposition 3-12-5: if `G` is generated by subgroups `G₁` and `G₂`, their intersection is a
proper subgroup of each and is not of index `2` in both, and the action of `G` on `Ω` satisfies
the two-set ping-pong hypotheses on disjoint nonempty subsets `Ω₁` and `Ω₂`, then `G` is the
amalgamated free product of `G₁` and `G₂` over `G₁ ∩ G₂`. -/
noncomputable def amalgamatedFreeProductEquivOfTwoSubsetPingPong
    : Subgroup.amalgamatedProduct G₁ G₂ ≃* G :=
  MulEquiv.ofBijective
    (Subgroup.amalgamatedProductComparison G₁ G₂)
    (comparisonMap_bijective_of_twoSubsetPingPong
      G₁ G₂ hgen hproper₁ hproper₂ hnot_indexTwo Ω₁ Ω₂ hΩ₁ hΩ₂ hdisj h₁₂ h₂₁ hH₁ hH₂)

@[simp] theorem amalgamatedFreeProductEquivOfTwoSubsetPingPong_of_left
    (g : G₁) :
    amalgamatedFreeProductEquivOfTwoSubsetPingPong
        G₁ G₂ hgen hproper₁ hproper₂ hnot_indexTwo
        Ω₁ Ω₂ hΩ₁ hΩ₂ hdisj h₁₂ h₂₁ hH₁ hH₂
        (Subgroup.amalgamatedProduct.left G₁ G₂ g) = g := by
  simp [amalgamatedFreeProductEquivOfTwoSubsetPingPong, Subgroup.amalgamatedProductComparison]

@[simp] theorem amalgamatedFreeProductEquivOfTwoSubsetPingPong_of_right
    (g : G₂) :
    amalgamatedFreeProductEquivOfTwoSubsetPingPong
        G₁ G₂ hgen hproper₁ hproper₂ hnot_indexTwo
        Ω₁ Ω₂ hΩ₁ hΩ₂ hdisj h₁₂ h₂₁ hH₁ hH₂
        (Subgroup.amalgamatedProduct.right G₁ G₂ g) = g := by
  simp [amalgamatedFreeProductEquivOfTwoSubsetPingPong, Subgroup.amalgamatedProductComparison]

end

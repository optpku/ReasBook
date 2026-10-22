/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Pointwise
open HNNExtension

set_option autoImplicit false

section

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]
variable (G₀ : Subgroup G) (Hplus Hminus : Subgroup G₀) (φ : Hplus ≃* Hminus)
variable (f : G)
variable (Ωneg Ωzero Ωpos : Set Ω)

/-!
Primary domain: group actions and HNN extensions.

Layer triage:
- `source-facing`: a group `G` acting on `Ω`, a base subgroup `G₀ ≤ G`, two associated subgroups
  `Hplus`, `Hminus ≤ G₀`, a stable letter `f : G`, and a ping-pong partition
  `Ω = Ωneg ⊔ Ωzero ⊔ Ωpos`.
- `core/canonical`: mathlib's owner `HNNExtension G₀ Hplus Hminus φ` together with
  `HNNExtension.lift`, `HNNExtension.of`, and `HNNExtension.t`.
- `bridge/view`: the canonical homomorphism sending the base subgroup by inclusion into `G` and
  the stable letter to `f`. A concrete permutation-group realization is only the specialization of
  this action-theoretic statement to `G := Subgroup (Equiv.Perm Ω)`.

Domain sampling:
1. `[MulAction G Ω]` is the intrinsic owner of the ping-pong action data, as already used by
   nearby Chapter 3 ping-pong files.
2. `Subgroup G` is the canonical owner for the base group `G₀` and its associated subgroups.
3. The pointwise action `g • S` on subsets is the canonical owner API for the ping-pong movement
   hypotheses; it should replace `Equiv.Perm`-level `Set.MapsTo` bookkeeping.
4. `HNNExtension G₀ Hplus Hminus φ` with `HNNExtension.lift`, `HNNExtension.of`, and
   `HNNExtension.t` is mathlib's owner abstraction for the source HNN construction.

Primitive vs. derived:
- primitive public data: the action of `G` on `Ω`, the subgroup data `G₀`, `Hplus`, `Hminus`, the
  stable letter `f`, the conjugation hypothesis implementing `φ`, and the ping-pong subsets with
  their disjointness, nonemptiness, and set-action hypotheses;
- derived API: the canonical homomorphism from the HNN extension to `G`, its bijectivity under the
  ping-pong assumptions, and the resulting multiplicative equivalence.
-/

-- Conjugation by `f` yields the multiplicative relation required by `HNNExtension.lift`.
-- Proof sketch: start from the hypothesis
-- `φ a = f * a * f⁻¹` inside `G`, then multiply on the right by `f` and simplify.
private theorem relation_of_conjugation
    (hconj : ∀ a : Hplus, (φ a : G) = f * (a : G) * f⁻¹) :
    ∀ a : Hplus, f * (a : G) = (φ a : G) * f := by
  intro a
  calc
    f * (a : G) = (f * (a : G) * f⁻¹) * f := by
      simp [mul_assoc]
    _ = (φ a : G) * f := by
      rw [hconj a]

variable (hconj : ∀ a : Hplus, (φ a : G) = f * (a : G) * f⁻¹)

-- The canonical comparison map from the HNN extension onto `G`.
private def comparisonMap : HNNExtension G₀ Hplus Hminus φ →* G :=
  lift G₀.subtype f (relation_of_conjugation G₀ Hplus Hminus φ f hconj)

-- The ping-pong hypotheses force the canonical HNN-extension map onto `G` to be bijective.
-- Proof sketch: surjectivity follows from the generation hypothesis `closure (G₀ ∪ {f}) = ⊤`,
-- since the image already contains the base subgroup and the stable letter. Injectivity is the
-- ping-pong argument from the textbook, using the partition `Ωneg ⊔ Ωzero ⊔ Ωpos` and the
-- movement assumptions on `f`, `f⁻¹`, and on elements of `G₀ \ Hplus` and `G₀ \ Hminus`.
private theorem comparisonMap_bijective
    (hgen : Subgroup.closure ((G₀ : Set G) ∪ {f}) = ⊤)
    (hcover : Set.univ = Ωneg ∪ Ωzero ∪ Ωpos)
    (hdisj_neg_zero : Disjoint Ωneg Ωzero)
    (hdisj_neg_pos : Disjoint Ωneg Ωpos)
    (hdisj_zero_pos : Disjoint Ωzero Ωpos)
    (hΩneg_nonempty : Ωneg.Nonempty)
    (hΩzero_nonempty : Ωzero.Nonempty)
    (hΩpos_nonempty : Ωpos.Nonempty)
    (hf_pos : f • (Ωzero ∪ Ωpos) ⊆ Ωpos)
    (hf_neg : f⁻¹ • (Ωzero ∪ Ωneg) ⊆ Ωneg)
    (hmove_pos : ∀ g : G₀, g ∉ Hplus → (g : G) • Ωpos ⊆ Ωzero)
    (hmove_neg : ∀ g : G₀, g ∉ Hminus → (g : G) • Ωneg ⊆ Ωzero) :
    Function.Bijective (comparisonMap G₀ Hplus Hminus φ f hconj) := sorry

/-- Proposition 3-12-6: under the ping-pong hypotheses on the partition
`Ω = Ωneg ⊔ Ωzero ⊔ Ωpos`, the group `G` is canonically the HNN extension of `G₀` with
associated subgroups `Hplus`, `Hminus`, and stable letter `f` implementing `φ` by conjugation. -/
noncomputable def group_hnn_extension_equiv
    (hgen : Subgroup.closure ((G₀ : Set G) ∪ {f}) = ⊤)
    (hcover : Set.univ = Ωneg ∪ Ωzero ∪ Ωpos)
    (hdisj_neg_zero : Disjoint Ωneg Ωzero)
    (hdisj_neg_pos : Disjoint Ωneg Ωpos)
    (hdisj_zero_pos : Disjoint Ωzero Ωpos)
    (hΩneg_nonempty : Ωneg.Nonempty)
    (hΩzero_nonempty : Ωzero.Nonempty)
    (hΩpos_nonempty : Ωpos.Nonempty)
    (hf_pos : f • (Ωzero ∪ Ωpos) ⊆ Ωpos)
    (hf_neg : f⁻¹ • (Ωzero ∪ Ωneg) ⊆ Ωneg)
    (hmove_pos : ∀ g : G₀, g ∉ Hplus → (g : G) • Ωpos ⊆ Ωzero)
    (hmove_neg : ∀ g : G₀, g ∉ Hminus → (g : G) • Ωneg ⊆ Ωzero) :
    HNNExtension G₀ Hplus Hminus φ ≃* G :=
  MulEquiv.ofBijective
    (comparisonMap G₀ Hplus Hminus φ f hconj)
    (comparisonMap_bijective
      G₀ Hplus Hminus φ f Ωneg Ωzero Ωpos hconj
      hgen hcover hdisj_neg_zero hdisj_neg_pos hdisj_zero_pos
      hΩneg_nonempty hΩzero_nonempty hΩpos_nonempty hf_pos hf_neg hmove_pos hmove_neg)

/-- The canonical HNN-extension equivalence restricts to the inclusion of the base subgroup. -/
-- Proof sketch: unfold `group_hnn_extension_equiv`; its forward map is the canonical comparison
-- map built from `HNNExtension.lift`, so the claim is `HNNExtension.lift_of`.
@[simp] theorem group_hnn_extension_equiv_of
    (hgen : Subgroup.closure ((G₀ : Set G) ∪ {f}) = ⊤)
    (hcover : Set.univ = Ωneg ∪ Ωzero ∪ Ωpos)
    (hdisj_neg_zero : Disjoint Ωneg Ωzero)
    (hdisj_neg_pos : Disjoint Ωneg Ωpos)
    (hdisj_zero_pos : Disjoint Ωzero Ωpos)
    (hΩneg_nonempty : Ωneg.Nonempty)
    (hΩzero_nonempty : Ωzero.Nonempty)
    (hΩpos_nonempty : Ωpos.Nonempty)
    (hf_pos : f • (Ωzero ∪ Ωpos) ⊆ Ωpos)
    (hf_neg : f⁻¹ • (Ωzero ∪ Ωneg) ⊆ Ωneg)
    (hmove_pos : ∀ g : G₀, g ∉ Hplus → (g : G) • Ωpos ⊆ Ωzero)
    (hmove_neg : ∀ g : G₀, g ∉ Hminus → (g : G) • Ωneg ⊆ Ωzero)
    (g : G₀) :
    group_hnn_extension_equiv
        G₀ Hplus Hminus φ f Ωneg Ωzero Ωpos hconj
        hgen hcover hdisj_neg_zero hdisj_neg_pos hdisj_zero_pos
        hΩneg_nonempty hΩzero_nonempty hΩpos_nonempty hf_pos hf_neg hmove_pos hmove_neg
        (of g) =
      G₀.subtype g := by
  simp [group_hnn_extension_equiv, comparisonMap]

/-- The canonical HNN-extension equivalence sends the stable letter to `f`. -/
-- Proof sketch: unfold `group_hnn_extension_equiv`; its forward map is the canonical comparison
-- map built from `HNNExtension.lift`, so the claim is `HNNExtension.lift_t`.
@[simp] theorem group_hnn_extension_equiv_t
    (hgen : Subgroup.closure ((G₀ : Set G) ∪ {f}) = ⊤)
    (hcover : Set.univ = Ωneg ∪ Ωzero ∪ Ωpos)
    (hdisj_neg_zero : Disjoint Ωneg Ωzero)
    (hdisj_neg_pos : Disjoint Ωneg Ωpos)
    (hdisj_zero_pos : Disjoint Ωzero Ωpos)
    (hΩneg_nonempty : Ωneg.Nonempty)
    (hΩzero_nonempty : Ωzero.Nonempty)
    (hΩpos_nonempty : Ωpos.Nonempty)
    (hf_pos : f • (Ωzero ∪ Ωpos) ⊆ Ωpos)
    (hf_neg : f⁻¹ • (Ωzero ∪ Ωneg) ⊆ Ωneg)
    (hmove_pos : ∀ g : G₀, g ∉ Hplus → (g : G) • Ωpos ⊆ Ωzero)
    (hmove_neg : ∀ g : G₀, g ∉ Hminus → (g : G) • Ωneg ⊆ Ωzero) :
    group_hnn_extension_equiv
        G₀ Hplus Hminus φ f Ωneg Ωzero Ωpos hconj
        hgen hcover hdisj_neg_zero hdisj_neg_pos hdisj_zero_pos
        hΩneg_nonempty hΩzero_nonempty hΩpos_nonempty hf_pos hf_neg hmove_pos hmove_neg
        t =
      f := by
  simp [group_hnn_extension_equiv, comparisonMap]

end

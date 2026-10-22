/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

namespace MulAut

variable (F : Type u) [Group F]

/-- The action of an automorphism of `F` on the quotient by a characteristic subgroup. -/
def quotient (H : Subgroup F) [H.Characteristic] : MulAut F →* MulAut (F ⧸ H) where
  toFun σ :=
    QuotientGroup.congr H H σ (Subgroup.characteristic_iff_map_eq.mp inferInstance σ)
  map_one' := by
    ext ⟨x⟩
    rfl
  map_mul' σ τ := by
    ext ⟨x⟩
    rfl

/-- The natural homomorphism from automorphisms of `F` to automorphisms of its abelianization,
obtained by specializing the canonical quotient-action owner `MulAut.quotient` to the commutator
subgroup. -/
abbrev abelianization : MulAut F →* MulAut (Abelianization F) :=
  quotient F (commutator F)

/-- The subgroup of automorphisms acting trivially on the abelianization of `F`. -/
def IA : Subgroup (MulAut F) :=
  (abelianization F).ker

/-- The subgroup of inner automorphisms of `F`. -/
def innerAutomorphismSubgroup : Subgroup (MulAut F) :=
  (MulAut.conj : F →* MulAut F).range

/-- The subgroup of inner automorphisms is normal in the full automorphism group. -/
instance innerAutomorphismSubgroup_normal : (innerAutomorphismSubgroup F).Normal := by
  change ((MulAut.conj : F →* MulAut F).range).Normal
  refine ⟨?_⟩
  intro n hn σ
  rcases hn with ⟨a, rfl⟩
  exact ⟨σ a, by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  ⟩

end MulAut

macro "JA(" F:term ")" : term => `(MulAut.innerAutomorphismSubgroup $F)

section

variable {F : Type u} [Group F] [IsFreeGroup F] [Group.FG F]

/-- Proposition 1-4-5: for a finitely generated free group `F`, the natural map from `Aut(F)` to
the automorphism group of its abelianization is surjective. -/
-- Layer triage:
-- `source-facing`: the natural map from `MulAut F` to `MulAut (Abelianization F)`.
-- `core/canonical`: the quotient-action owner `MulAut.quotient F H`, whose specialization to
-- `H = commutator F` is definitionally the abelianization action; pointwise this is the induced
-- automorphism `σ.abelianizationCongr` on `Abelianization F`.
-- `bridge/view`: `MulAut.abelianization F` is just the source-facing abbreviation for that
-- specialization, while `MulAut.quotient F H` remains the broader owner for later
-- lower-central-series quotients. The textbook quotient `\overline{F}` is the canonical
-- abelianization `Abelianization F`, and `lowerCentralSeries_one` identifies it with the first
-- lower-central-series quotient.
-- Domain sampling:
-- 1. `MulAut.quotient F H` is the chapter owner action on quotients by characteristic subgroups.
-- 2. `MulEquiv.abelianizationCongr` in mathlib is the pointwise owner for the induced
--    automorphism on abelianizations.
-- 3. `QuotientGroup.congr` is the canonical equivalence induced on quotient groups by an
--    automorphism preserving the distinguished subgroup.
-- 4. `Subgroup.characteristic_iff_map_eq` is the owner criterion turning characteristicity into
--    the equality needed by `QuotientGroup.congr`.
-- 5. `lowerCentralSeries_one` identifies the first lower-central-series quotient with the
--    canonical abelianization.
-- 6. `[Group.FG F]` is the chapter's canonical finite-rank owner assumption for free groups.
-- Primitive vs. derived:
-- the primitive owner datum for the public action is the quotient owner `MulAut.quotient F H`;
-- its commutator specialization is the source-facing abbreviation `MulAut.abelianization F`,
-- used for kernel and surjectivity statements, while the subgroup of inner automorphisms is used
-- downstream through the owner declaration `MulAut.innerAutomorphismSubgroup F`. Pointwise the
-- action is still the canonical automorphism `σ.abelianizationCongr`. The textbook notation
-- `JA(F)` is rendered in later source-facing statements by this canonical inner-automorphism
-- owner rather than by a second subgroup declaration. The
-- representative quotient formulas are already supplied upstream by `QuotientGroup.congr_mk'`,
-- so this file keeps no parallel local wrapper lemmas for them.
-- Proof sketch: choose a finite free basis of `F` and identify `Abelianization F` with the free
-- abelian group on that basis. Elementary Nielsen automorphisms lift the standard generators of
-- the automorphism group of the free abelian group, so every automorphism of `Abelianization F`
-- comes from an automorphism of `F`.
theorem abelianization_surjective_of_fg :
    Function.Surjective (MulAut.abelianization F) := sorry

end

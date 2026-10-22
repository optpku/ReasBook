/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

-- Layer triage:
-- `source-facing`: a one-relator group on generators `X` with defining relator `r`, together with
-- the hypothesis that `X` has cardinality at least three.
-- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator owner,
-- `Cardinal.mk X` for the cardinality lower bound, `Subgroup G` for subgroup data, and quotient
-- groups `S ⧸ N`.
-- `bridge/view`: a chosen equivalence `PresentedGroup (Set.singleton r) ≃* G` transports
-- the owner-level `SQ`-universality statement to an arbitrary ambient group `G`.
-- Domain sampling:
-- 1. `PresentedGroup (Set.singleton r)` is the chapter's canonical owner for a group with
--    generators `X` and a single defining relator `r`.
-- 2. `Cardinal.mk X` is the universe-stable way to encode “at least three generators”.
-- 3. `Subgroup G` and `S ⧸ N` are the canonical mathlib owners for subgroups and quotient groups.
-- 4. Definition `2-1-1` uses `PresentedGroup R ≃* G` directly as presentation data, so a chosen
--    equivalence belongs at the bridge layer rather than as primitive owner data for this item.
-- Primitive vs. derived:
-- the primitive owner-level data are only the relator `r` and the lower bound on the cardinality
-- of the generator type; `SQ`-universality is the derived property of admitting every countable
-- group as a subquotient, and invariance under multiplicative equivalence supplies the separate
-- bridge theorem for arbitrary isomorphic ambient groups.

/-- A group is `SQ`-universal when every countable group embeds in a quotient of one of its
subgroups. -/
def IsSQUniversal (G : Type u) [Group G] : Prop :=
  ∀ {H : Type w} [Group H] [Countable H],
    ∃ (S : Subgroup G) (N : Subgroup S) (_ : N.Normal) (φ : H →* S ⧸ N),
      Function.Injective φ

namespace IsSQUniversal

/-- `SQ`-universality is invariant under multiplicative equivalence. -/
theorem of_mulEquiv {G : Type u} {G' : Type v} [Group G] [Group G'] (e : G ≃* G')
    (hG : IsSQUniversal.{u, w} G) : IsSQUniversal.{v, w} G' := by
  intro H _ _
  obtain ⟨S, N, hN, φ, hφ⟩ :
      ∃ (S : Subgroup G) (N : Subgroup S) (_ : N.Normal) (φ : H →* S ⧸ N),
        Function.Injective φ := hG
  let S' : Subgroup G' := S.map (e : G →* G')
  let N' : Subgroup S' := N.map (e.subgroupMap S : S →* S')
  let _ : N'.Normal := hN.map (e.subgroupMap S : S →* S') (e.subgroupMap S).surjective
  let eQ : S ⧸ N ≃* S' ⧸ N' := QuotientGroup.congr N N' (e.subgroupMap S) rfl
  exact ⟨S', N', inferInstance, eQ.toMonoidHom.comp φ, eQ.injective.comp hφ⟩

/-- `SQ`-universality is preserved and reflected by multiplicative equivalence. -/
theorem iff_mulEquiv {G : Type u} {G' : Type v} [Group G] [Group G'] (e : G ≃* G') :
    IsSQUniversal.{u, w} G ↔ IsSQUniversal.{v, w} G' :=
  ⟨of_mulEquiv e, of_mulEquiv e.symm⟩

end IsSQUniversal

section

variable {X : Type v} (r : FreeGroup X)

local notation "Q" => PresentedGroup (Set.singleton r)

-- Proof sketch: apply the classical Magnus--Lyndon theorem that a one-relator group with at least
-- three generators is `SQ`-universal directly to the canonical owner `Q`.
/-- Proposition 2-5-31: a one-relator group on at least three generators is `SQ`-universal. -/
theorem isSQUniversal_of_three_generator_one_relator_group (hX : 3 ≤ Cardinal.mk X) :
    IsSQUniversal Q := sorry

-- Proof sketch: transport Proposition `2-5-31` across the chosen presentation equivalence from
-- Definition `2-1-1`. The owner-level theorem stays canonical, and this lemma is only the bridge
-- to an arbitrary isomorphic ambient group.
/-- Transport form of Proposition 2-5-31 for a chosen one-relator presentation of an ambient
group. -/
theorem isSQUniversal_of_three_generator_one_relator_presentation
    {G : Type u} [Group G] (P : Q ≃* G) (hX : 3 ≤ Cardinal.mk X) :
    IsSQUniversal G := by
  exact IsSQUniversal.of_mulEquiv P
    (isSQUniversal_of_three_generator_one_relator_group r hX)

end

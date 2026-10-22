/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u v

-- Declarations for this item are recorded in this dedicated item file.

-- Primary domain: one-relator groups and subgroup structure under group laws.
-- Layer triage:
-- `source-facing`: a subgroup of a one-relator group satisfying a nontrivial law, together with
-- the torsion-free versus torsion dichotomy for the ambient one-relator group.
-- `core/canonical`: `PresentedGroup ({r} : Set (FreeGroup X))` for the one-relator owner,
-- `Subgroup` for the subgroup owner, `SatisfiesNontrivialLaw` for the intrinsic law hypothesis on
-- the subgroup type,
-- `IsMulTorsionFree` and `IsOfFinOrder` for the torsion split, `IsCyclic` for cyclicity, and
-- `DihedralGroup 0` for the infinite dihedral group. The exceptional Baumslag-Solitar branch is
-- source-facing through the named owner `BS(1, n)`.
-- `bridge/view`: a chosen presentation equivalence
-- `PresentedGroup ({r} : Set (FreeGroup X)) ≃* G` transports the canonical owner-level theorem to
-- an arbitrary ambient group `G`; the Baumslag-Solitar exceptional family is compared by
-- isomorphism with the named owner `BS(1, n)`.
-- Domain sampling:
-- 1. `PresentedGroup ({r} : Set (FreeGroup X))` is the chapter owner abstraction for one-relator
--    groups throughout nearby propositions `2-5-25`, `2-5-26`, and `2-5-29`.
-- 2. Definition `2-1-1` uses `PresentedGroup R ≃* G` directly as presentation data, so a chosen
--    equivalence is the right bridge layer, not the main owner-level statement.
-- 3. A law is intrinsically a property of a group, so the subgroup hypothesis is best expressed
--    on the subgroup type `H` itself rather than as extra structure on the ambient `Subgroup G`.
-- 4. Nearby Theorem `2-2-5` packages `BS(2, 3)` in the source-facing owner namespace
--    `BaumslagSolitar23`, so the standard family `BS(1, n)` should likewise be named at the owner
--    level rather than exposed only through a raw presentation expression.
-- 5. Nearby Proposition `2-5-25` already renders “locally cyclic” directly as
--    `∀ K : Subgroup H, K.FG → IsCyclic K`, so that owner-level form is reused here.
-- Primitive vs. derived:
-- the primitive public data are the relator `r`, the subgroup `H`, the law satisfied by `H`, and
-- the source-facing Baumslag-Solitar owner `BS(1, n)`; the locally cyclic, cyclic, and
-- infinite-dihedral alternatives are derived conclusions.

section

namespace BaumslagSolitarOne

/-- The relator `x⁻¹ y x y^{-n}` presenting the Baumslag-Solitar group `BS(1, n)`. -/
abbrev relator (n : ℤ) : FreeGroup (Fin 2) :=
  (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) *
    (FreeGroup.of (1 : Fin 2) ^ (-n))

/-- The Baumslag-Solitar group `BS(1, n)` presented by `⟨x, y | x⁻¹ y x = y^n⟩`. -/
abbrev Group (n : ℤ) : Type := PresentedGroup ({relator n} : Set (FreeGroup (Fin 2)))

end BaumslagSolitarOne

notation "BS(1," n ")" => BaumslagSolitarOne.Group n

/-- A group satisfies a nontrivial law when some nontrivial word in finitely many variables
vanishes under every evaluation into that group. -/
def SatisfiesNontrivialLaw (G : Type v) [Group G] : Prop :=
  ∃ n : ℕ, ∃ w : FreeGroup (Fin n),
    w ≠ 1 ∧ ∀ f : Fin n → G, FreeGroup.lift f w = 1

namespace SatisfiesNontrivialLaw

/-- A multiplicative equivalence preserves the property of satisfying a nontrivial law. -/
theorem iff_mulEquiv {G : Type v} [Group G] {G' : Type u} [Group G'] (e : G ≃* G') :
    SatisfiesNontrivialLaw G ↔ SatisfiesNontrivialLaw G' := by
  constructor
  · rintro ⟨n, w, hw, hlaw⟩
    refine ⟨n, w, hw, ?_⟩
    intro f
    have h := hlaw (fun i ↦ e.symm (f i))
    let e' : G →* G' := e.toMonoidHom
    have hcomp :
        e'.comp (FreeGroup.lift (fun i ↦ e.symm (f i))) = FreeGroup.lift f := by
      ext i
      simp [e']
    have hw' :
        e ((FreeGroup.lift (fun i ↦ e.symm (f i))) w) = FreeGroup.lift f w := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun g : FreeGroup (Fin n) →* G' ↦ g w) hcomp
    have h' : e ((FreeGroup.lift (fun i ↦ e.symm (f i))) w) = 1 := by
      simpa using congrArg e h
    exact hw'.symm.trans h'
  · rintro ⟨n, w, hw, hlaw⟩
    refine ⟨n, w, hw, ?_⟩
    intro f
    have h := hlaw (fun i ↦ e (f i))
    let e' : G' →* G := e.symm.toMonoidHom
    have hcomp :
        e'.comp (FreeGroup.lift (fun i ↦ e (f i))) = FreeGroup.lift f := by
      ext i
      simp [e']
    have hw' :
        e.symm ((FreeGroup.lift (fun i ↦ e (f i))) w) = FreeGroup.lift f w := by
      simpa [MonoidHom.comp_apply] using
        congrArg (fun g : FreeGroup (Fin n) →* G ↦ g w) hcomp
    have h' : e.symm ((FreeGroup.lift (fun i ↦ e (f i))) w) = 1 := by
      simpa using congrArg e.symm h
    exact hw'.symm.trans h'

/-- A solvable group satisfies a nontrivial law. -/
theorem of_isSolvable (G : Type*) [Group G] [IsSolvable G] :
    SatisfiesNontrivialLaw G := sorry

end SatisfiesNontrivialLaw

variable {X : Type u} (r : FreeGroup X)

local notation "Q" => PresentedGroup (Set.singleton r)

private abbrev subgroupComapMulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) (K : Subgroup B) : K.comap e.toMonoidHom ≃* K :=
  (MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm' e K)).trans
    (e.symm.subgroupMap K).symm

private theorem locallyCyclic_of_mulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) :
    (∀ K : Subgroup A, K.FG → IsCyclic K) →
      ∀ K : Subgroup B, K.FG → IsCyclic K := by
  intro h K hK
  let K' : Subgroup A := K.comap e.toMonoidHom
  let eK : K' ≃* K := subgroupComapMulEquiv e K
  have hK' : K'.FG := by
    have hKG : Group.FG K := (Group.fg_iff_subgroup_fg K).2 hK
    let f : K →* K' := eK.symm.toMonoidHom
    have hf : Function.Surjective f := eK.symm.surjective
    have hK'G : Group.FG K' := Group.fg_of_surjective hf
    exact (Group.fg_iff_subgroup_fg K').1 hK'G
  exact (MulEquiv.isCyclic eK).1 (h K' hK')

private theorem locallyCyclic_iff_mulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) :
    (∀ K : Subgroup A, K.FG → IsCyclic K) ↔
      ∀ K : Subgroup B, K.FG → IsCyclic K :=
  ⟨locallyCyclic_of_mulEquiv e, locallyCyclic_of_mulEquiv e.symm⟩

private theorem isMulTorsionFree_of_mulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) :
    IsMulTorsionFree A → IsMulTorsionFree B := by
  intro hA
  letI : IsMulTorsionFree A := hA
  exact Function.Injective.isMulTorsionFree e.symm.toMonoidHom e.symm.injective

private theorem isMulTorsionFree_iff_mulEquiv {A : Type u} [Group A] {B : Type v} [Group B]
    (e : A ≃* B) :
    IsMulTorsionFree A ↔ IsMulTorsionFree B :=
  ⟨isMulTorsionFree_of_mulEquiv e, isMulTorsionFree_of_mulEquiv e.symm⟩

private theorem exists_nontrivial_isOfFinOrder_of_mulEquiv
    {A : Type u} [Group A] {B : Type v} [Group B] (e : A ≃* B) :
    (∃ a : A, a ≠ 1 ∧ IsOfFinOrder a) →
      ∃ b : B, b ≠ 1 ∧ IsOfFinOrder b := by
  rintro ⟨a, ha, hfin⟩
  refine ⟨e a, ?_, e.toMonoidHom.isOfFinOrder hfin⟩
  · intro h
    apply ha
    exact e.injective (by simpa using h)

private theorem exists_nontrivial_isOfFinOrder_iff_mulEquiv
    {A : Type u} [Group A] {B : Type v} [Group B] (e : A ≃* B) :
    (∃ a : A, a ≠ 1 ∧ IsOfFinOrder a) ↔
      ∃ b : B, b ≠ 1 ∧ IsOfFinOrder b :=
  ⟨exists_nontrivial_isOfFinOrder_of_mulEquiv e,
    exists_nontrivial_isOfFinOrder_of_mulEquiv e.symm⟩

-- Proof sketch: combine the classical subgroup theorem for one-relator groups with law
-- hypotheses. In the torsion-free case, the theorem gives the locally cyclic alternative or a
-- Baumslag-Solitar presentation `BS(1, n)` for `H`. In the presence of a nontrivial finite-order
-- element of the ambient one-relator group, the corresponding classification reduces the
-- possibilities for `H` to cyclic or infinite dihedral.
/-- Proposition 2-5-24: if `H` is a subgroup of the one-relator group
`PresentedGroup ({r} : Set (FreeGroup X))` and `H` satisfies a nontrivial law, then the
torsion-free case forces `H` to be locally cyclic or of the form `⟨x, y | x⁻¹ y x = y^n⟩`, while
the presence of torsion in the ambient group forces `H` to be cyclic or infinite dihedral. -/
theorem subgroup_with_nontrivial_law_classification_in_one_relator_group
    (H : Subgroup Q)
    (hHlaw : SatisfiesNontrivialLaw H) :
    (IsMulTorsionFree Q →
      (∀ K : Subgroup H, K.FG → IsCyclic K) ∨
        ∃ n : ℤ, Nonempty (H ≃* BS(1, n))) ∧
    ((∃ g : Q, g ≠ 1 ∧ IsOfFinOrder g) →
      IsCyclic H ∨ Nonempty (H ≃* DihedralGroup 0)) := sorry

variable {G : Type v} [Group G]

-- Proof sketch: transport the owner-level statement across the chosen presentation equivalence
-- from Definition `2-1-1`. The law hypothesis, the torsion/torsion-free predicates, and the
-- exceptional isomorphism alternatives are invariant under multiplicative equivalence.
/-- Bridge form of Proposition 2-5-24 for an arbitrary ambient group given by a chosen one-relator
presentation. -/
theorem subgroup_with_nontrivial_law_classification_of_presentation
    (P : Q ≃* G) (H : Subgroup G)
    (hHlaw : SatisfiesNontrivialLaw H) :
    (IsMulTorsionFree G →
      (∀ K : Subgroup H, K.FG → IsCyclic K) ∨
        ∃ n : ℤ, Nonempty (H ≃* BS(1, n))) ∧
    ((∃ g : G, g ≠ 1 ∧ IsOfFinOrder g) →
      IsCyclic H ∨ Nonempty (H ≃* DihedralGroup 0)) := by
  let H' : Subgroup Q := H.comap P.toMonoidHom
  let eH : H' ≃* H := subgroupComapMulEquiv P H
  have hHlaw' : SatisfiesNontrivialLaw H' :=
    (SatisfiesNontrivialLaw.iff_mulEquiv eH).2 hHlaw
  have hQ :=
    subgroup_with_nontrivial_law_classification_in_one_relator_group r H' hHlaw'
  refine ⟨?_, ?_⟩
  · intro htf
    have htf' : IsMulTorsionFree Q := (isMulTorsionFree_iff_mulEquiv P).2 htf
    rcases hQ.1 htf' with hloc | ⟨n, hBS⟩
    · exact Or.inl ((locallyCyclic_iff_mulEquiv eH).1 hloc)
    · rcases hBS with ⟨eBS⟩
      exact Or.inr ⟨n, ⟨eH.symm.trans eBS⟩⟩
  · intro htors
    have htors' : ∃ g : Q, g ≠ 1 ∧ IsOfFinOrder g :=
      (exists_nontrivial_isOfFinOrder_iff_mulEquiv P).2 htors
    rcases hQ.2 htors' with hcyc | hD
    · exact Or.inl ((MulEquiv.isCyclic eH).1 hcyc)
    · rcases hD with ⟨eD⟩
      exact Or.inr ⟨eH.symm.trans eD⟩

end

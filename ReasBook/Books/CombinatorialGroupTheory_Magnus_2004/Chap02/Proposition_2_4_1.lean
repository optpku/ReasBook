/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_20
import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

namespace ReidemeisterSchreier

open FreeGroup
open GroupPresentation

-- Layer triage:
-- `source-facing`: a presentation `G = F / ⟪R⟫` with `F = FreeGroup X`, a subgroup `H ≤ G`, the
-- inverse-image subgroup `H̃ ≤ F`, a right transversal `T` for `H̃` satisfying the Schreier
-- initial-segment condition, the rewriting map `τ`, and the relators `τ(trt⁻¹)`.
-- `core/canonical`: `PresentedGroup R`, `PresentedGroup.mk R`, `Subgroup.comap`,
-- `Subgroup.RightTransversal`, the chapter-1 Schreier owner layer
-- `HasInitialSegments` / `schreierGenerator` / `schreierGeneratorSet`, and the chapter-2
-- presentation owner map `GroupPresentation.generatorImage`.
-- `bridge/view`: the textbook representative `\bar w` is the canonical right-coset selector
-- `T.2.toRightFun w`, while the textbook nontrivial Schreier generators are the chapter-1 owner
-- set `schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun`.
-- Domain sampling:
-- 1. `PresentedGroup R` and `PresentedGroup.mk R` are the owner quotient-presentation API.
-- 2. `Subgroup.comap` is the canonical inverse-image construction for `H̃`.
-- 3. `HasInitialSegments` is the project owner property for the Schreier prefix condition.
-- 4. `schreierGeneratorSet` is the project owner set of nontrivial Schreier generators.
-- Primitive vs. derived:
-- the primitive source data are the relator set `R`, the subgroup `H`, and the chosen right
-- transversal `T`; the subgroup `H̃`, the textbook condition `1 ∈ T`, the Schreier generator
-- alphabet, the rewriting map `τ`, and the induced relator set are all derived from that owner
-- data.

variable {X : Type u} [DecidableEq X] {R : Set (FreeGroup X)}

variable {H : Subgroup (PresentedGroup R)}
/-- The inverse-image subgroup `H̃ ≤ FreeGroup X` of `H ≤ PresentedGroup R` under the canonical
quotient map. This is the source-facing subgroup that appears in the Reidemeister-Schreier
construction. -/
def preimageSubgroup (H : Subgroup (PresentedGroup R)) : Subgroup (FreeGroup X) :=
  H.comap (PresentedGroup.mk R)

/-- The source-facing set of nontrivial Schreier generators attached to a right transversal of the
inverse-image subgroup `preimageSubgroup H`, viewed as elements of that subgroup. -/
abbrev schreierGenerators (T : (preimageSubgroup H).RightTransversal) : Set (preimageSubgroup H) :=
  { y | (y : FreeGroup X) ∈ schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun }

variable {T : (preimageSubgroup H).RightTransversal}

/-- The canonical image in `H` of a Schreier generator symbol, obtained by evaluating the
corresponding preimage-subgroup element in the ambient quotient `PresentedGroup R`. -/
abbrev schreierGeneratorImage (T : (preimageSubgroup H).RightTransversal) :
    ↥(schreierGenerators T) → H :=
  fun y ↦ ⟨PresentedGroup.mk R y.1, y.1.2⟩

private def signedLetter : X × Bool → FreeGroup X
  | (x, true) => FreeGroup.of x
  | (x, false) => (FreeGroup.of x)⁻¹

omit [DecidableEq X] in
private theorem schreierGenerator_mem_preimageSubgroup
    (T : (preimageSubgroup H).RightTransversal) (t : ↥(T : Set (FreeGroup X))) (x : X)
    (hγ : schreierGenerator T.2.toRightFun t x ≠ 1) :
    schreierGenerator T.2.toRightFun t x ∈ preimageSubgroup H := by
  have hclosure :
      Subgroup.closure (schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun) =
        preimageSubgroup H :=
    Subgroup.RightTransversal.closure_schreierGeneratorSet_eq
  simpa [hclosure] using
    (Subgroup.subset_closure ((mem_schreierGeneratorSet_iff).2 ⟨t, x, rfl, hγ⟩) :
      schreierGenerator T.2.toRightFun t x ∈
        Subgroup.closure (schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun))

private def schreierGeneratorOf (T : (preimageSubgroup H).RightTransversal)
    (t : ↥(T : Set (FreeGroup X))) (x : X)
    (hγ : schreierGenerator T.2.toRightFun t x ≠ 1) :
    schreierGenerators T :=
  ⟨⟨schreierGenerator T.2.toRightFun t x, schreierGenerator_mem_preimageSubgroup T t x hγ⟩,
    (mem_schreierGeneratorSet_iff).2 ⟨t, x, rfl, hγ⟩⟩

private def schreierSignedGenerator (T : (preimageSubgroup H).RightTransversal)
    (current : FreeGroup X) (y : X × Bool) :
    FreeGroup ↥(schreierGenerators T) :=
  let _ : DecidableEq (FreeGroup X) := Classical.decEq (FreeGroup X)
  match y.2 with
  | true =>
      let t := T.2.toRightFun current
      if hγ : schreierGenerator T.2.toRightFun t y.1 ≠ 1 then
        FreeGroup.of (schreierGeneratorOf T t y.1 hγ)
      else
        1
  | false =>
      let next := T.2.toRightFun (current * signedLetter y)
      if hγ : schreierGenerator T.2.toRightFun next y.1 ≠ 1 then
        (FreeGroup.of (schreierGeneratorOf T next y.1 hγ))⁻¹
      else
        1

private def schreierTauWordAux (T : (preimageSubgroup H).RightTransversal) (current : FreeGroup X) :
    List (X × Bool) → FreeGroup ↥(schreierGenerators T)
  | [] => 1
  | y :: ys =>
      schreierSignedGenerator T current y * schreierTauWordAux T (current * signedLetter y) ys

-- Proof sketch: check a single cancellation step `xx⁻¹ ↦ 1` in the input word. The two adjacent
-- Schreier letters introduced by that pair are inverse to each other, and the running coset
-- representative before and after the cancellation is the same, so the recursive products agree.
-- The Schreier rewriting of a word is invariant under one free-group reduction step.
omit [DecidableEq X] in
private lemma schreierTauWordAux_step_eq
    (T : (preimageSubgroup H).RightTransversal)
    (current : FreeGroup X) {L₁ L₂ : List (X × Bool)}
    (hred : FreeGroup.Red.Step L₁ L₂) :
    schreierTauWordAux T current L₁ = schreierTauWordAux T current L₂ := sorry

/-- The Schreier rewriting map `τ : FreeGroup X → FreeGroup X₁*` descended from the word-level
definition, where `X₁` is the owner Schreier generator set attached to the transversal `T`. -/
noncomputable def schreierTau (T : (preimageSubgroup H).RightTransversal) :
    FreeGroup X → FreeGroup ↥(schreierGenerators T) :=
  Quot.lift (fun L : List (X × Bool) ↦ schreierTauWordAux T 1 L)
    (fun _ _ h ↦ schreierTauWordAux_step_eq T 1 h)

/-- The relator set `R* = { τ(t r t⁻¹) | t ∈ T, r ∈ R }` in the Reidemeister-Schreier
presentation. -/
noncomputable def schreierRelators (T : (preimageSubgroup H).RightTransversal) :
    Set (FreeGroup ↥(schreierGenerators T)) :=
  {u | ∃ t : ↥(T : Set (FreeGroup X)), ∃ r : FreeGroup X, r ∈ R ∧
      schreierTau T ((t : FreeGroup X) * r * (t : FreeGroup X)⁻¹) = u}

-- Proof sketch: Proposition `1-3-7` organizes the nontrivial Schreier generators through the
-- owner set `schreierGeneratorSet`, while the quotient map `PresentedGroup.mk R` identifies the
-- subgroup `H̃ / ⟪R⟫` with `H`. The Reidemeister-Schreier kernel calculation then shows that the
-- rewritten relators `τ(trt⁻¹)` present exactly that quotient, with the defining-generator map
-- equal to the canonical Schreier-generator image map `schreierGeneratorImage T`.
/-- Proposition 2-4-1: if `H ≤ PresentedGroup R` and `T` is a right transversal of the
inverse-image subgroup `H̃ ≤ FreeGroup X` whose underlying set has initial segments, then `H`
admits the Reidemeister-Schreier presentation with generators the owner Schreier set
`schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun` and relators `τ(t r t⁻¹)`, and the
chosen defining-generator map is the canonical map from each Schreier-generator symbol to its
image in `H`. -/
theorem reidemeister_schreier_presentation_presentedGroup
    (hT : HasInitialSegments (T : Set (FreeGroup X))) :
    ∃ P : PresentedGroup (schreierRelators T) ≃* H,
      generatorImage P = schreierGeneratorImage T := sorry

section

variable {G : Type*} [Group G] (P : PresentedGroup R ≃* G) {K : Subgroup G}
variable {T : (preimageSubgroup (K.comap P.toMonoidHom)).RightTransversal}

/-- The presentation equivalence identifies the canonical owner subgroup `K.comap P.toMonoidHom`
of `PresentedGroup R` with the source-facing subgroup `K ≤ G`. -/
abbrev presentationSubgroupEquiv (K : Subgroup G) : K.comap P.toMonoidHom ≃* K :=
  (P.subgroupMap (K.comap P.toMonoidHom)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective P.surjective K))

/-- The canonical image in `K` of a Schreier generator symbol for the subgroup `K ≤ G`,
transported from the owner-side subgroup of `PresentedGroup R` along the chosen presentation `P`.
-/
abbrev schreierGeneratorImageOfPresentation (K : Subgroup G)
    (T : (preimageSubgroup (K.comap P.toMonoidHom)).RightTransversal) :
    ↥(schreierGenerators T) → K :=
  presentationSubgroupEquiv P K ∘ schreierGeneratorImage T

-- Proof sketch: apply the owner-level Reidemeister-Schreier presentation theorem to the canonical
-- subgroup `K.comap P.toMonoidHom ≤ PresentedGroup R`, then transport the resulting presentation
-- equivalence across the canonical subgroup equivalence `presentationSubgroupEquiv P K`.
/-- Proposition 2-4-1 in source-facing form: if `P : PresentedGroup R ≃* G` is a chosen
presentation of `G`, `K ≤ G`, and `T` is a right transversal of the corresponding inverse-image
subgroup `H̃ ≤ FreeGroup X` whose underlying set has initial segments, then `K` admits the
Reidemeister-Schreier presentation with generators the owner Schreier set
`schreierGeneratorSet (T : Set (FreeGroup X)) T.2.toRightFun` and relators `τ(t r t⁻¹)`, and the
chosen defining-generator map is the canonical map from each Schreier-generator symbol to its
image in `K`. -/
theorem reidemeister_schreier_presentation
    (hT : HasInitialSegments (T : Set (FreeGroup X))) :
    ∃ Q : PresentedGroup (schreierRelators T) ≃* K,
      generatorImage Q = schreierGeneratorImageOfPresentation P K T := by
  rcases reidemeister_schreier_presentation_presentedGroup hT with ⟨Q, hQ⟩
  refine ⟨Q.trans (presentationSubgroupEquiv P K), ?_⟩
  funext y
  simpa only [generatorImage, MulEquiv.trans_apply,
    schreierGeneratorImageOfPresentation, Function.comp_apply] using
    congrArg (presentationSubgroupEquiv P K) (congrFun hQ y)

end

end ReidemeisterSchreier

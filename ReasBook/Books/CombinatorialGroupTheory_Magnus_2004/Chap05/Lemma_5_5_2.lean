/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_5_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_5
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_5

universe u

set_option autoImplicit false

noncomputable section

open Quiver.Path

section

variable {X : Type u}

local instance lemma_5_5_2_decidableEq : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X

/-!
Primary domain: annular small-cancellation diagrams for conjugacy in relator quotients.

Layer triage:
- `source-facing`: two cyclically reduced words `u` and `z` in the free group `F` whose images in
  `G = F / N` are conjugate, together with the existence of a reduced annular `R`-diagram whose
  chosen outer and inner boundary components carry the cyclic words of `u` and `z⁻¹`,
  respectively.
- `core/canonical`: `FreeGroup X` is the owner for the ambient free group,
  `PresentedGroup.mk R` is the canonical quotient map into `G = F / N`,
  `GroupDiagram.AnnularRDiagram` from Lemma `5-5-1` is the chapter owner for annular
  `R`-diagrams,
  `GroupDiagram.IsReduced` is the owner predicate for reduced diagrams, and
  `CyclicWord X` is the chapter owner for cyclically reduced boundary words modulo rotation,
  while `GroupDiagram.pathLabelWord` is the source-facing boundary-word API attached to a chosen
  loop.
- `bridge/view`: `Loop` and `cyclicPath` give based representatives of the chosen outer and inner
  boundary cycles. The based boundary labels remain list words, but the public boundary
  conclusion is recorded through the owner `CyclicWord X` rather than only through raw equalities
  in `Cycle (X × Bool)`.

Domain sampling:
1. `GroupDiagram.IsReduced` from Definition `5-2-5` is the existing owner predicate for reduced
   diagrams.
2. `GroupDiagram.AnnularRDiagram` from Lemma `5-5-1` is the chapter owner for annular
   `R`-diagrams.
3. `PresentedGroup.mk R` from the presentation API is the canonical quotient map used throughout
   the chapter for passing from `FreeGroup X` to the relator quotient.
4. `CyclicWord X` from Definition `1-4-17` is the chapter owner for cyclically reduced boundary
   words modulo rotation.
5. `GroupDiagram.pathLabelWord` from Definition `5-1-5` is the owner boundary-word API for a
   chosen loop; the resulting cyclic boundary data should be exposed via `CyclicWord X`.

Primitive vs. derived:
- primitive public data: the annular `R`-diagram owner together with nonemptiness of regions and
  reducedness of the underlying labelled map;
- derived API: chosen loop representatives of the outer and inner boundary cycles whose read words
  determine the prescribed cyclic boundary words of `u` and `z⁻¹`, stated directly through
  `pathLabelWord` and the owner `CyclicWord X`.
-/

namespace GroupDiagram

private theorem isCyclicallyReduced_invRev {L : List (X × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.IsCyclicallyReduced (FreeGroup.invRev L) := by
  rcases h with ⟨hred, hcyc⟩
  refine ⟨?_, ?_⟩
  ·
    let R : (X × Bool) → (X × Bool) → Prop := fun a b ↦ a.1 = b.1 → a.2 = b.2
    let f : X × Bool → X × Bool := fun x ↦ (x.1, !x.2)
    unfold FreeGroup.IsReduced at hred ⊢
    have hreverse : List.IsChain R L.reverse := by
      rw [List.isChain_reverse]
      change List.IsChain (fun a b : X × Bool ↦ b.1 = a.1 → b.2 = a.2) L
      simpa [R, eq_comm] using hred
    have hmap : List.IsChain R (List.map f L.reverse) := by
      rw [List.isChain_map]
      change List.IsChain
        (fun a b : X × Bool ↦ (f a).1 = (f b).1 → (f a).2 = (f b).2) L.reverse
      simpa [f, R]
    simpa [FreeGroup.invRev, f, Function.comp_def] using hmap
  ·
    rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hab
    have ha' : L.head? = some (a₁, !a₂) := by
      simpa [FreeGroup.invRev] using ha
    have hb' : L.getLast? = some (b₁, !b₂) := by
      simpa [FreeGroup.invRev] using hb
    have h' := hcyc (b₁, !b₂) hb' (a₁, !a₂) ha' hab.symm
    simpa [eq_comm] using h'

-- Proof sketch: choose a minimal relator-conjugate expression witnessing that the images of `u`
-- and `z` are conjugate in `PresentedGroup R`, build the corresponding annular van Kampen
-- diagram, and remove the distinguished `z`-region from the minimal disc diagram. Minimality
-- gives reducedness, while the surviving outer and inner boundary loops read cyclically reduced
-- boundary words whose cyclic words are exactly those of `u` and `z⁻¹`, respectively. If there
-- were no regions left, the annulus would already witness that `u` and `z` are conjugate in the
-- free group, contradicting `h_not_conj`.
/-- Lemma 5-5-2: if `u` and `z` are cyclically reduced words of the free group `F = FreeGroup X`,
`u` and `z` are not conjugate in `F` although their images in `G = F / N` are conjugate, then
there exists a reduced annular
`R`-diagram with at least one region together with chosen outer and inner boundary loops whose
boundary labels realize the cyclic words of `u` and `z⁻¹`, respectively. -/
theorem exists_reduced_annularRDiagram_of_conjugate_in_relator_quotient
    (R : Set (FreeGroup X)) {u z : FreeGroup X}
    (hu_cyclic : FreeGroup.IsCyclicallyReduced u.toWord)
    (hz_cyclic : FreeGroup.IsCyclicallyReduced z.toWord)
    (h_not_conj : ¬ IsConj u z)
    (hconj_quotient : IsConj (PresentedGroup.mk R u) (PresentedGroup.mk R z)) :
    ∃ (M : AnnularRDiagram R) (outer inner : Loop M.source.skeleton)
      (houter : cyclicPath outer = M.outerBoundary)
      (hinner : cyclicPath inner = M.innerBoundary),
      Nonempty M.source.Face ∧
        M.IsReduced ∧
          ∃ houter_cyclic : FreeGroup.IsCyclicallyReduced (M.pathLabelWord basis outer.2),
            ∃ hinner_cyclic : FreeGroup.IsCyclicallyReduced (M.pathLabelWord basis inner.2),
              (⟨(M.pathLabelWord basis outer.2 : Cycle (X × Bool)), houter_cyclic⟩ :
                  CyclicWord X) = ⟨u.toWord, hu_cyclic⟩ ∧
                (⟨(M.pathLabelWord basis inner.2 : Cycle (X × Bool)), hinner_cyclic⟩ :
                    CyclicWord X) =
                  ⟨(z⁻¹).toWord,
                    by
                      simpa [FreeGroup.toWord_inv] using
                        isCyclicallyReduced_invRev hz_cyclic⟩ := sorry

end GroupDiagram

end

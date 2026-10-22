/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open Monoid
open Quiver

namespace OneComplex

namespace Subcomplex

variable {ι : Type w} {K : OneComplex.{u, v}}

-- Layer triage:
-- `source-facing`: an ambient `1`-complex `K`, a family of subcomplexes `K_λ`, a vertex-labelling
-- into an indexed free product, and the resulting notion of a binding tie.
-- `core/canonical`: `OneComplex`, `OneComplex.Subcomplex`, `OneComplex.Hom`,
-- `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `Quiver.Path (Quiver.Symmetrify _)`,
-- `CoprodI`, and `MonoidHom.range` are the owner abstractions for the ambient graph, the
-- subcomplexes, connectedness, ambient and
-- internal zigzag paths, and the target free product.
-- `bridge/view`: `Subcomplex.toOneComplex` and the canonical hom
-- `Subcomplex.iInterInclusion` convert the
-- source-facing subcomplex data to the canonical ambient/path owners.
--
-- Domain sampling:
-- 1. `OneComplex.Subcomplex` is the source-facing owner for the subcomplexes `K_λ`.
-- 2. `OneComplex.Hom` from Proposition `3-3-1` is the chapter owner for maps of carried
--    `1`-complexes, so the intersection inclusion should be phrased through that owner rather
--    than as a raw quiver prefunctor.
-- 3. `Quiver.IsStronglyConnected (Quiver.Symmetrify _)` is the canonical owner for connectedness
--    of a reversible `1`-skeleton.
-- 4. `Quiver.Path (Quiver.Symmetrify K)` is the canonical path owner specialized to
--    symmetrified `1`-complexes.
-- 5. `CoprodI`, `CoprodI.of`, and `MonoidHom.range` are the owner abstractions for
--    the indexed free product and its canonical factor subgroups.

variable {A : ι → Type x} [∀ i, Group (A i)]

/-- A zigzag path in a `1`-complex is a path in its symmetrified quiver. -/
abbrev ZigzagPath {C : OneComplex.{u, v}} (a b : C) : Type _ :=
  @Quiver.Path (Quiver.Symmetrify C) _ a b

/-- The label displacement between two endpoints in the ambient free product. -/
def endpointDisplacement (label : K → CoprodI A) (a b : K) : CoprodI A :=
  (label a)⁻¹ * label b

/-- The source-facing labelled free-product context for a family `K_λ`: each `K_λ` is connected,
and the endpoint displacement between any two of its vertices lies in the corresponding
free-product factor. -/
class IsFreeProductLabelledFamily (Ksub : ι → Subcomplex K) (label : K → CoprodI A) : Prop where
  /-- Each subcomplex `K_λ` is connected. -/
  connected (i : ι) :
    Quiver.IsStronglyConnected (Quiver.Symmetrify (Ksub i).toOneComplex)
  /-- The label displacement between vertices of `K_λ` lies in the `λ`-factor subgroup. -/
  endpointDisplacement_mem_factor
      (i : ι) (start finish : (Ksub i).toOneComplex) :
      endpointDisplacement label start.1 finish.1 ∈
        (CoprodI.of : A i →* CoprodI A).range

/-- A binding tie is a path lying in one `K_λ`, with trivial image in the ambient indexed free
product, whose endpoints lie in different connected components of `⋂ K_λ`. -/
structure BindingTie (Ksub : ι → Subcomplex K) (label : K → CoprodI A) where
  /-- The chosen index `λ` for the subcomplex containing the tie. -/
  index : ι
  /-- The initial vertex of the tie lies in the common intersection. -/
  start : (⋂ i, Ksub i).toOneComplex
  /-- The terminal vertex of the tie lies in the common intersection. -/
  finish : (⋂ i, Ksub i).toOneComplex
  /-- The endpoints of the tie belong to different components of the common intersection. -/
  separated : ¬ Nonempty (ZigzagPath start finish)
  /-- The underlying zigzag path of the tie lies in the chosen subcomplex `K_λ`. -/
  path : ZigzagPath
      ((iInterInclusion Ksub index).toVertex start)
      ((iInterInclusion Ksub index).toVertex finish)
  /-- The endpoint displacement of the tie is trivial in the ambient free product. -/
  displacement_eq_one : endpointDisplacement label start.1 finish.1 = 1

private theorem coprodI_eq_one_of_mem_two_factors {i j : ι} (hij : i ≠ j) {g : CoprodI A}
    (hi : g ∈ (CoprodI.of : A i →* CoprodI A).range)
    (hj : g ∈ (CoprodI.of : A j →* CoprodI A).range) : g = 1 := by
  classical
  rcases hi with ⟨a, rfl⟩
  rcases hj with ⟨b, hab⟩
  have hproj :
      CoprodI.lift (Pi.mulSingle i (MonoidHom.id (A i))) (CoprodI.of a : CoprodI A) =
        CoprodI.lift (Pi.mulSingle i (MonoidHom.id (A i))) (CoprodI.of b : CoprodI A) := by
    simpa using (congrArg (CoprodI.lift (Pi.mulSingle i (MonoidHom.id (A i)))) hab).symm
  have ha : a = 1 := by
    simpa [hij] using hproj
  simp [ha]

/-- Lemma 3-3-8: in the labelled free-product setting, if the common intersection `⋂ K_λ` is not
connected, then any two distinct factors produce a binding tie in the chosen `i`-factor.

The source-facing data are the family `K_λ`, the ambient vertex-labelling into the indexed free
product, and the standard free-product property that endpoint displacements inside `K_λ` land in
the `λ`-factor subgroup. The trivial-image condition is derived by comparing the same endpoint pair
through two distinct factors, rather than assumed as an extra bridge hypothesis. -/
-- Proof sketch: choose two vertices of `⋂ K_λ` lying in different components. Since `Kᵢ` and `Kⱼ`
-- are connected, there are paths between these vertices inside each of the two factors. The two
-- endpoint displacements coincide by definition, while the labelled free-product hypotheses force
-- that common displacement to lie in the `i`- and `j`-factors respectively. Distinct free-product
-- factors intersect trivially, so the common displacement is `1`; the path in `Kᵢ` is therefore a
-- binding tie.
theorem exists_bindingTie_of_intersection_not_connected
    (Ksub : ι → Subcomplex K) (label : K → CoprodI A)
    (hlabel : IsFreeProductLabelledFamily Ksub label)
    (i j : ι) (hij : i ≠ j)
    (hnot :
      ¬ Quiver.IsStronglyConnected (Quiver.Symmetrify ((⋂ i, Ksub i).toOneComplex))) :
    ∃ tie : BindingTie Ksub label, tie.index = i := by
  classical
  have hseparated :
      ∃ start finish : (⋂ i, Ksub i).toOneComplex, ¬ Nonempty (ZigzagPath start finish) := by
    by_contra hseparated
    apply hnot
    intro start finish
    by_contra hpath'
    exact hseparated ⟨start, finish, hpath'⟩
  rcases hseparated with ⟨start, finish, hseparated⟩
  let starti := (iInterInclusion Ksub i).toVertex start
  let finishi := (iInterInclusion Ksub i).toVertex finish
  let startj := (iInterInclusion Ksub j).toVertex start
  let finishj := (iInterInclusion Ksub j).toVertex finish
  have hpathi :
      Nonempty (ZigzagPath starti finishi) := by
    exact hlabel.connected i _ _
  rcases hpathi with ⟨pathi⟩
  have hfactori :
      endpointDisplacement label start.1 finish.1 ∈
        (CoprodI.of : A i →* CoprodI A).range := by
    simpa [starti, finishi] using hlabel.endpointDisplacement_mem_factor i starti finishi
  have hfactorj :
      endpointDisplacement label start.1 finish.1 ∈
        (CoprodI.of : A j →* CoprodI A).range := by
    simpa [startj, finishj] using hlabel.endpointDisplacement_mem_factor j startj finishj
  have himage :
      endpointDisplacement label start.1 finish.1 = 1 :=
    coprodI_eq_one_of_mem_two_factors hij hfactori hfactorj
  refine ⟨
    { index := i
      start := start
      finish := finish
      separated := hseparated
      path := pathi
      displacement_eq_one := himage },
    rfl⟩

end Subcomplex

end OneComplex

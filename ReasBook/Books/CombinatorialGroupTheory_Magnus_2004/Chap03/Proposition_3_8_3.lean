/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_7_6
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_8_1

universe u v w x

set_option autoImplicit false

noncomputable section

/-!
Primary domain: NEC groups and presentations with reflection cycles.

Layer triage:
- `source-facing`: a chosen finite presentation of an NEC group with finitely many ordinary
  generators `X`, reflection generators indexed by a disjoint union of cyclically ordered
  boundary blocks `J_j`, and relators of the three forms described in Proposition `3-8-3`.
- `core/canonical`: `PresentedGroup R` is the owner for the group defined by a specified relator
  set, `Finite X` is the canonical finite-generator owner for the ordinary generator type, and
  `IsStrictlyQuadraticSet` is the chapter owner for the final “each generator of `X` occurs
  exactly twice” condition on the auxiliary words `a_{jh}` and `s_k`.
- `bridge/view`: the helper definitions below turn the source formulas for the relators
  `x_{jh}²`, `t_{jh}^{m_{jh}}`, and `s_k^{m_k}` into a single canonical relator set for
  `PresentedGroup`.

Domain sampling:
1. `IsNECGroup` from Definition `3-8-1` is the owner predicate for the ambient NEC-group
   hypothesis.
2. `PresentedGroup R` from Chapter `2` is the canonical owner for a concrete presentation.
3. `IsStrictlyQuadraticSet` from Proposition `1-7-6` is the established chapter owner for the
   “exactly twice” incidence condition on a finite word system.

Primitive vs. derived:
- primitive public data: the finite ordinary generator type `X`, the boundary-component index
  type, the positive lengths `n_j`, the words `a_{jh}` and `s_k`, the multiplicities `m_{jh}` and
  `m_k`, and the presentation equivalence to `G`;
- derived API: the canonical sigma-type reflection index `J = ⨿_j J_j`, the relator set
  `R₀ ∪ R₁ ∪ R₂`, and the combined strict-quadratic auxiliary word system.
-/

/-- The cyclic successor on one boundary block `J_j`. -/
private def necBoundaryNext {B : Type w} (boundaryLength : B → ℕ+) (j : B) :
    Fin (boundaryLength j : ℕ) → Fin (boundaryLength j : ℕ)
  | h => Fin.ofNat (boundaryLength j : ℕ) (h.1 + 1)

/-- Regard a word on the ordinary generators `X` as a word on the enlarged alphabet
`X ⊕ J`. -/
private def necOrdinaryWordInclusion {X : Type v} {B : Type w} (boundaryLength : B → ℕ+) :
    FreeGroup X → FreeGroup (X ⊕ Σ j : B, Fin (boundaryLength j : ℕ)) :=
  FreeGroup.map Sum.inl

/-- The reflection generator corresponding to one index in the disjoint union `J = ⨿_j J_j`. -/
private def necReflectionGenerator {X : Type v} {B : Type w} (boundaryLength : B → ℕ+)
    (r : Σ j : B, Fin (boundaryLength j : ℕ)) :
    FreeGroup (X ⊕ Σ j : B, Fin (boundaryLength j : ℕ)) :=
  FreeGroup.of (.inr r)

/-- The textbook word `t_{jh} = x_{jh} a_{jh} x_{j,h+1} a_{jh}^{-1}` attached to one boundary
reflection. -/
private def necBoundaryElement {X : Type v} {B : Type w} (boundaryLength : B → ℕ+)
    (connectorWord : (j : B) → Fin (boundaryLength j : ℕ) → FreeGroup X)
    (j : B) (h : Fin (boundaryLength j : ℕ)) :
    FreeGroup (X ⊕ Σ j : B, Fin (boundaryLength j : ℕ)) :=
  necReflectionGenerator boundaryLength ⟨j, h⟩ *
    necOrdinaryWordInclusion boundaryLength (connectorWord j h) *
    necReflectionGenerator boundaryLength ⟨j, necBoundaryNext boundaryLength j h⟩ *
    (necOrdinaryWordInclusion boundaryLength (connectorWord j h))⁻¹

/-- The auxiliary word system formed by all words `a_{jh}` together with all words `s_k`. -/
def necOrdinaryWordSystem {X : Type v} {B : Type w} [Finite B] (boundaryLength : B → ℕ+)
    {K : Type x} [Finite K]
    (connectorWord : (j : B) → Fin (boundaryLength j : ℕ) → FreeGroup X)
    (interiorWord : K → FreeGroup X) : Finset (FreeGroup X) := by
  classical
  let _ : Fintype B := Fintype.ofFinite B
  let _ : Fintype K := Fintype.ofFinite K
  exact
    (Finset.univ.image fun r : Σ j : B, Fin (boundaryLength j : ℕ) ↦ connectorWord r.1 r.2) ∪
      Finset.univ.image interiorWord

/-- The relator set `R₀ ∪ R₁ ∪ R₂` of the NEC presentation determined by the given data. -/
def necRelatorSet {X : Type v} {B : Type w} (boundaryLength : B → ℕ+)
    {K : Type x}
    (connectorWord : (j : B) → Fin (boundaryLength j : ℕ) → FreeGroup X)
    (boundaryMultiplicity : (j : B) → Fin (boundaryLength j : ℕ) → ℕ+)
    (interiorWord : K → FreeGroup X)
    (interiorMultiplicity : K → ℕ+) :
    Set (FreeGroup (X ⊕ Σ j : B, Fin (boundaryLength j : ℕ))) :=
  Set.range (fun r : Σ j : B, Fin (boundaryLength j : ℕ) ↦
      necReflectionGenerator boundaryLength r ^ (2 : ℕ)) ∪
    Set.range (fun r : Σ j : B, Fin (boundaryLength j : ℕ) ↦
      necBoundaryElement boundaryLength connectorWord r.1 r.2 ^
        (boundaryMultiplicity r.1 r.2 : ℕ)) ∪
    Set.range (fun k : K ↦
      necOrdinaryWordInclusion boundaryLength (interiorWord k) ^ (interiorMultiplicity k : ℕ))

variable {G : Type u} [Group G]

-- Proof sketch: start from the planar simply connected `2`-complex with regular face action given
-- by the NEC-group structure. Choose representatives for the boundary cycles of the quotient
-- orbifold, record the edge-reflection generators `x_{jh}`, read the conjugating words `a_{jh}`
-- from connecting paths between consecutive reflections, and collect the remaining elliptic
-- relators as the words `s_k^{m_k}`. The resulting relator family presents `G`, and the planar
-- incidence argument shows that the combined auxiliary word system is strictly quadratic.
/-- Proposition 3-8-3: every NEC group admits a finite presentation
`G = (X ∪ J; R₀ ∪ R₁ ∪ R₂)` in
which `J` is a disjoint union of ordered blocks `J_j = (x_{j1}, …, x_{jn_j})`, `R₀` consists of
the involution relators `x_{jh}²`, `R₁` consists of the power relators
`t_{jh}^{m_{jh}} = (x_{jh} a_{jh} x_{j,h+1} a_{jh}^{-1})^{m_{jh}}`, `R₂` consists of the power
relators `s_k^{m_k}` on words in `X`, and the combined family of words `a_{jh}` and `s_k` is
strictly quadratic over `X`. -/
theorem exists_necPresentation_of_isNECGroup (hG : IsNECGroup G) :
    ∃ (X : Type v) (_ : Finite X)
      (BoundaryComponent : Type w) (_ : Finite BoundaryComponent)
      (boundaryLength : BoundaryComponent → ℕ+)
      (InteriorRelator : Type x) (_ : Finite InteriorRelator)
      (connectorWord : (j : BoundaryComponent) → Fin (boundaryLength j : ℕ) → FreeGroup X)
      (boundaryMultiplicity : (j : BoundaryComponent) → Fin (boundaryLength j : ℕ) → ℕ+)
      (interiorWord : InteriorRelator → FreeGroup X)
      (interiorMultiplicity : InteriorRelator → ℕ+)
      (e :
        PresentedGroup
            (necRelatorSet boundaryLength connectorWord boundaryMultiplicity interiorWord
              interiorMultiplicity) ≃* G),
      IsStrictlyQuadraticSet (necOrdinaryWordSystem boundaryLength connectorWord interiorWord) :=
  sorry

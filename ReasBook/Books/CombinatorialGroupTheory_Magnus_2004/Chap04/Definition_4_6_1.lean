/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

/-!
Primary domain: bipolar structures on groups.

Layer triage:
- `source-facing`: the two poles `E` and `E*`, admissible sector factorizations, and the bipolar
  decomposition of a group into the fixed subgroup piece and four sectors.
- `core/canonical`: the involution on poles is the standard `Star`/`InvolutiveStar` API, and
  disjointness of the sector family is recorded by mathlib's `Pairwise (Disjoint on ...)`.
- `bridge/view`: coercing a `BipolarStructure` to its sector family `Pole → Pole → Set G`, and the
  owner-side irreducibility predicate `B.IsIrreducible g`.

Domain sampling:
1. `Star` and `InvolutiveStar` are mathlib's owner abstractions for a type equipped with an
   involution.
2. `Pairwise (Disjoint on f)` is the canonical mathlib surface for a pairwise disjoint indexed
   family of sets.
3. `BipolarStructure` is the chapter-facing owner abstraction for Definition `4-6-1`.
4. `HasSectorFactorization` is the primitive source-facing predicate recording admissible products
   through a pole sequence, while `B.IsIrreducible g` is its canonical owner-side view.

Primitive vs. derived:
the primitive data are the subgroup piece `F`, the sector family `sector`, and the axioms they
satisfy. The old five-piece indexing wrapper was only bookkeeping for cover/disjointness, so the
owner now stores those axioms directly instead of exposing a second public piece-index type.
The primitive factorization predicate itself only depends on the multiplicative structure, so it is
stated at the weaker `Monoid` level and then reused inside the group-level owner.
In particular, the source nontriviality axiom `EE* ≠ ∅` belongs to the owner itself rather than to
an auxiliary later predicate, while irreducibility is derived from the primitive factorization
predicate and therefore belongs in the owner file rather than a later theorem file.
-/

/-- The two poles used to label the non-subgroup pieces of a bipolar structure. -/
inductive Pole where
  | E
  | EStar
  deriving DecidableEq, Repr, Fintype

namespace Pole

/-- The involution exchanging `E` and `E*`. -/
instance : Star Pole where
  star
    | .E => .EStar
    | .EStar => .E

/-- The pole involution is an involution. -/
instance : InvolutiveStar Pole where
  star_involutive
    | .E => rfl
    | .EStar => rfl

@[simp] theorem star_E : star E = EStar := rfl

@[simp] theorem star_EStar : star EStar = E := rfl

end Pole

open Function Pole

section

variable {G : Type u} [Monoid G]

/-- A length-`n` sector factorization of `g` is an ordered product `g = g₁ ⋯ gₙ`
together with a pole sequence `X₀, ..., Xₙ` such that each factor lies in `Xᵢ₋₁* Xᵢ`. -/
def HasSectorFactorization (sector : Pole → Pole → Set G) (g : G) (n : ℕ) : Prop :=
  ∃ factors : Fin n → G,
    ∃ poles : Fin (n + 1) → Pole,
      g = (List.ofFn factors).prod ∧
        ∀ i : Fin n, factors i ∈ sector (star (poles i.castSucc)) (poles i.succ)

end

/-- Definition 4-6-1: a bipolar structure on a group is a decomposition of the group
into the subgroup piece `F` and the four sectors `EE`, `EE*`, `E*E`, and `E*E*`,
satisfying the subgroup, nontriviality, right-translation, inverse, product, and boundedness
axioms from the text. -/
structure BipolarStructure (G : Type u) [Group G] where
  /-- The subgroup piece `F`. -/
  F : Subgroup G
  /-- The sector `XY` for `X,Y ∈ {E,E*}`. -/
  sector : Pole → Pole → Set G
  /-- The fixed subgroup piece together with the four sectors cover the whole group. -/
  pieces_cover :
    (F : Set G) ∪ ⋃ X : Pole, ⋃ Y : Pole, sector X Y = (Set.univ : Set G)
  /-- The fixed subgroup piece is disjoint from every sector. -/
  fixed_disjoint_sector (X Y : Pole) :
    Disjoint (F : Set G) (sector X Y)
  /-- Distinct sectors are pairwise disjoint. -/
  sector_pairwiseDisjoint :
    Pairwise (Disjoint on fun p : Pole × Pole ↦ sector p.1 p.2)
  /-- The mixed sector `EE*` is nonempty. -/
  eeStar_nonempty : (sector E EStar).Nonempty
  /-- Right multiplication by an element of `F` preserves each sector. -/
  sector_mul_mem {X Y : Pole} {g f : G} (hg : g ∈ sector X Y) (hf : f ∈ F) :
    g * f ∈ sector X Y
  /-- Inversion sends the sector `XY` to the sector `YX`. -/
  inv_mem_sector {X Y : Pole} {g : G} (hg : g ∈ sector X Y) :
    g⁻¹ ∈ sector Y X
  /-- Multiplying an `XY` element by a `Y*Z` element lands in `XZ`. -/
  mul_mem_sector {X Y Z : Pole} {g h : G} (hg : g ∈ sector X Y)
      (hh : h ∈ sector (star Y) Z) :
    g * h ∈ sector X Z
  /-- The lengths of admissible sector factorizations of a fixed group element are
  uniformly bounded. -/
  bounded_factorizations (g : G) :
    ∃ N : ℕ, ∀ n : ℕ, HasSectorFactorization sector g n → n ≤ N

namespace BipolarStructure

variable {G : Type u} [Group G]

/-- A bipolar structure is used via its sector family. -/
instance : CoeFun (BipolarStructure G) (fun _ ↦ Pole → Pole → Set G) where
  coe B := B.sector

/-- Every group element lies either in the fixed subgroup piece or in one of the four sectors. -/
theorem mem_fixed_or_mem_sector (B : BipolarStructure G) (g : G) :
    g ∈ B.F ∨ ∃ X Y : Pole, g ∈ B X Y := by
  have hg : g ∈ (B.F : Set G) ∪ ⋃ X : Pole, ⋃ Y : Pole, B X Y := by
    rw [B.pieces_cover]
    simp
  rcases hg with hgF | hgSectors
  · exact Or.inl hgF
  · rcases Set.mem_iUnion.1 hgSectors with ⟨X, hgX⟩
    rcases Set.mem_iUnion.1 hgX with ⟨Y, hgXY⟩
    exact Or.inr ⟨X, Y, hgXY⟩

/-- Distinct sectors are disjoint. -/
theorem sector_disjoint (B : BipolarStructure G) {X Y Z W : Pole}
    (h : (X, Y) ≠ (Z, W)) :
    Disjoint (B X Y) (B Z W) :=
  B.sector_pairwiseDisjoint h

/-- Inversion shows that the other mixed sector `E*E` is nonempty as well. -/
theorem eStarE_nonempty (B : BipolarStructure G) : (B EStar E).Nonempty := by
  rcases B.eeStar_nonempty with ⟨g, hg⟩
  exact ⟨g⁻¹, B.inv_mem_sector hg⟩

/-- The chapter-facing irreducibility predicate: `g` admits no admissible two-step sector
factorization. -/
def IsIrreducible (B : BipolarStructure G) (g : G) : Prop :=
  ¬ HasSectorFactorization B g 2

@[simp] theorem isIrreducible_iff (B : BipolarStructure G) (g : G) :
    B.IsIrreducible g ↔ ¬ HasSectorFactorization B g 2 := Iff.rfl

end BipolarStructure

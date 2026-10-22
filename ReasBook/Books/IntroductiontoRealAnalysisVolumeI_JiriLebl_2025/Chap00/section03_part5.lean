/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators

section Chap00
section Section03

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Definition 0.3.26: Sets `A` and `B` have the same cardinality when there exists a
bijection `f : A → B`. The cardinality `|A|` is the equivalence class of all sets with
the same cardinality as `A`. -/
def sameCardinality (A : Type u) (B : Type v) : Prop :=
  Nonempty (A ≃ B)

/-- The book's notion of equal cardinalities matches mathlib's equality of cardinals. -/
theorem sameCardinality_iff_cardinal_eq {A : Type u} {B : Type v} :
    sameCardinality A B ↔
      Cardinal.lift.{v, u} (Cardinal.mk A) = Cardinal.lift.{u, v} (Cardinal.mk B) := by
  simpa [sameCardinality] using (Cardinal.lift_mk_eq' (α := A) (β := B)).symm

/-- The cardinality class of a set `A` is the collection of all sets bijective to `A`. -/
def cardinalityClass (A : Type u) : Set (Type u) :=
  {B | sameCardinality A B}

/-- The book's cardinality `|A|` corresponds to the mathlib cardinal `Cardinal.mk A`. -/
abbrev cardinality (A : Type u) : Cardinal :=
  Cardinal.mk A

/-- Definition 0.3.27: A set has cardinality `n` when it is in bijection with
`{1, 2, …, n}` (or is empty when `n = 0`); such sets are called finite. A set is
infinite if it is not finite. -/
def elementCollectionCardEq (A : Set α) (n : ℕ) : Prop :=
  Nonempty ((Subtype A) ≃ Fin n)

/-- The book's notion of a finite set: it has the same cardinality as some `{1, …, n}`. -/
abbrev finiteElementCollection (A : Set α) : Prop :=
  ∃ n, elementCollectionCardEq (A := A) n

/-- The book's finite sets correspond to mathlib's `Set.Finite`. -/
theorem finiteElementCollection_iff_setFinite {A : Set α} :
    finiteElementCollection (A := A) ↔ Set.Finite A := by
  constructor
  · rintro ⟨n, ⟨e⟩⟩
    refine (Set.finite_def).2 ?_
    exact ⟨Fintype.ofEquiv (Fin n) e.symm⟩
  · intro h
    classical
    rcases (Set.finite_def).1 h with ⟨inst⟩
    let _ : Fintype (Subtype A) := inst
    rcases (Finite.exists_equiv_fin (Subtype A)) with ⟨n, ⟨e⟩⟩
    exact ⟨n, ⟨e⟩⟩

/-- The book's infinite sets are those that are not finite. -/
abbrev infiniteElementCollection (A : Set α) : Prop :=
  ¬ finiteElementCollection (A := A)

/-- The book's infinite sets correspond to mathlib's `Set.Infinite`. -/
theorem infiniteElementCollection_iff_setInfinite {A : Set α} :
    infiniteElementCollection (A := A) ↔ Set.Infinite A := by
  constructor
  · intro hInfColl
    change ¬ Set.Finite A
    intro hFinite
    exact hInfColl ((finiteElementCollection_iff_setFinite).2 hFinite)
  · intro hInfinite
    change ¬ Set.Finite A at hInfinite
    intro hFinColl
    exact hInfinite ((finiteElementCollection_iff_setFinite).1 hFinColl)

/-- Definition 0.3.28: We write `|A| ≤ |B|` if there is an injection from `A` to `B`;
`|A| = |B|` when the two have the same cardinality; `|A| < |B|` when `|A| ≤ |B|` but the
cardinalities are not equal. -/
def cardinalLe (A : Type u) (B : Type v) : Prop :=
  ∃ f : A → B, Function.Injective f

/-- The book's `|A| ≤ |B|` corresponds to the cardinal inequality of `Cardinal.mk`. -/
theorem cardinalLe_iff {A : Type u} {B : Type v} :
    cardinalLe A B ↔ Cardinal.lift.{v, u} (Cardinal.mk A) ≤ Cardinal.lift.{u, v} (Cardinal.mk B) :=
  by
  constructor
  · rintro ⟨f, hf⟩
    exact (Cardinal.lift_mk_le').2 ⟨⟨f, hf⟩⟩
  · intro h
    rcases (Cardinal.lift_mk_le').1 h with ⟨e⟩
    exact ⟨e, e.injective⟩

/-- The book's strict cardinal inequality `|A| < |B|` means `|A| ≤ |B|` but not equal. -/
def cardinalLt (A : Type u) (B : Type v) : Prop :=
  cardinalLe A B ∧ ¬ sameCardinality A B

/-- The book's `|A| < |B|` matches the strict inequality of cardinals. -/
theorem cardinalLt_iff {A : Type u} {B : Type v} :
    cardinalLt A B ↔ Cardinal.lift.{v, u} (Cardinal.mk A) < Cardinal.lift.{u, v} (Cardinal.mk B) :=
  by
  constructor
  · rintro ⟨hLe, hNe⟩
    have hLe' := (cardinalLe_iff (A := A) (B := B)).1 hLe
    have hNe' :
        Cardinal.lift.{v, u} (Cardinal.mk A) ≠
          Cardinal.lift.{u, v} (Cardinal.mk B) := by
      intro hEq
      apply hNe
      exact (sameCardinality_iff_cardinal_eq (A := A) (B := B)).2 hEq
    exact lt_of_le_of_ne hLe' hNe'
  · intro hLt
    have hLe' :
        Cardinal.lift.{v, u} (Cardinal.mk A) ≤
          Cardinal.lift.{u, v} (Cardinal.mk B) :=
      le_of_lt hLt
    have hNe' :
        Cardinal.lift.{v, u} (Cardinal.mk A) ≠
          Cardinal.lift.{u, v} (Cardinal.mk B) :=
      ne_of_lt hLt
    refine ⟨(cardinalLe_iff (A := A) (B := B)).2 hLe', ?_⟩
    intro hSame
    apply hNe'
    exact (sameCardinality_iff_cardinal_eq (A := A) (B := B)).1 hSame

/-- Definition 0.3.29: A set is countably infinite if its cardinality equals that of
the natural numbers; it is countable if it is finite or countably infinite; otherwise it
is uncountable. -/
def countablyInfiniteElementCollection (A : Set α) : Prop :=
  Nonempty ((Subtype A) ≃ ℕ)

theorem countablyInfiniteElementCollection_iff_cardinal_eq_nat {A : Set α} :
    countablyInfiniteElementCollection (A := A) ↔ Cardinal.mk (Subtype A) = Cardinal.aleph0 := by
  constructor
  · rintro ⟨e⟩
    have e' : Subtype A ≃ ULift.{u, 0} ℕ :=
      e.trans (Equiv.ulift.symm : ℕ ≃ ULift.{u, 0} ℕ)
    have h : Cardinal.mk (Subtype A) = Cardinal.mk (ULift.{u, 0} ℕ) := Cardinal.mk_congr e'
    exact h.trans (Cardinal.mk_uLift (α := ℕ))
  · intro h
    have h' : Cardinal.mk (Subtype A) = Cardinal.mk (ULift.{u, 0} ℕ) :=
      h.trans (Cardinal.mk_uLift (α := ℕ)).symm
    have h'' :
        Cardinal.lift (Cardinal.mk (Subtype A)) =
          Cardinal.lift (Cardinal.mk (ULift.{u, 0} ℕ)) := congrArg Cardinal.lift h'
    have hEquiv : Nonempty (Subtype A ≃ ULift.{u, 0} ℕ) :=
      (Cardinal.lift_mk_eq' (α := Subtype A) (β := ULift.{u, 0} ℕ)).1 h''
    rcases hEquiv with ⟨e⟩
    exact ⟨e.trans (Equiv.ulift : ULift.{u, 0} ℕ ≃ ℕ)⟩

def countableElementCollection (A : Set α) : Prop :=
  finiteElementCollection (A := A) ∨ countablyInfiniteElementCollection (A := A)

def uncountableElementCollection (A : Set α) : Prop :=
  ¬ countableElementCollection (A := A)

theorem countableElementCollection_iff_setCountable {A : Set α} :
    countableElementCollection (A := A) ↔ Set.Countable A := by
  constructor
  · intro h
    rcases h with h | h
    · exact (finiteElementCollection_iff_setFinite).1 h |>.countable
    · rcases h with ⟨e⟩
      have : Countable (Subtype A) := Countable.of_equiv ℕ e.symm
      exact (Set.countable_coe_iff).1 this
  · intro h
    by_cases hfinite : Set.Finite A
    · left
      exact (finiteElementCollection_iff_setFinite).2 hfinite
    · right
      have hcount : Countable (Subtype A) := (Set.countable_coe_iff).2 h
      have hInfSet : Set.Infinite A := by
        change ¬ Set.Finite A
        exact hfinite
      have hInf : Infinite (Subtype A) := (Set.infinite_coe_iff).2 hInfSet
      classical
      let _ : Countable (Subtype A) := hcount
      let _ : Infinite (Subtype A) := hInf
      exact (nonempty_equiv_of_countable (α := Subtype A) (β := ℕ))

theorem uncountableElementCollection_iff_not_setCountable {A : Set α} :
    uncountableElementCollection (A := A) ↔ ¬ Set.Countable A := by
  simp [uncountableElementCollection, countableElementCollection_iff_setCountable]

/-- Example 0.3.30: The set `E` of even natural numbers has the same cardinality as `ℕ`;
the bijection is given by `n ↦ 2n`. -/
def evenNaturals : Set ℕ := {n | Even n}

/-- The map `n ↦ 2n` is a bijection from `ℕ` onto the even naturals. -/
lemma evenNaturals_map_bijective :
    Function.Bijective
      (fun n : ℕ => (⟨2 * n, by
        change Even (2 * n)
        exact even_two_mul n⟩ : Subtype evenNaturals)) := by
  constructor
  · intro a b h
    have h' : 2 * a = 2 * b := by
      exact congrArg Subtype.val h
    exact Nat.mul_left_cancel (by decide : 0 < 2) h'
  · intro y
    rcases y with ⟨k, hk⟩
    rcases (even_iff_exists_two_mul.mp hk) with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    rfl

/-- An explicit equivalence between `ℕ` and the even naturals. -/
lemma equiv_nat_evenNaturals : Nonempty (ℕ ≃ Subtype evenNaturals) := by
  classical
  let f : ℕ → Subtype evenNaturals :=
    fun n =>
      ⟨2 * n, by
        change Even (2 * n)
        exact even_two_mul n⟩
  refine ⟨Equiv.ofBijective f ?_⟩
  simpa [f] using evenNaturals_map_bijective

/-- Example 0.3.30 (continued). -/
theorem evenNaturals_sameCardinality_nat :
    sameCardinality (Subtype evenNaturals) ℕ := by
  rcases equiv_nat_evenNaturals with ⟨e⟩
  exact ⟨e.symm⟩

/-- Example 0.3.31: The Cartesian product `ℕ × ℕ` is countably infinite, for example via
the diagonal enumeration `(1,1), (1,2), (2,1), (1,3), (2,2), (3,1), …`. -/
theorem natProd_countablyInfinite :
    countablyInfiniteElementCollection (A := (Set.univ : Set (ℕ × ℕ))) := by
  refine ⟨(Equiv.subtypeUnivEquiv (α := ℕ × ℕ) (p := (Set.univ : Set (ℕ × ℕ))) ?_).trans
    Nat.pairEquiv⟩
  intro x
  trivial

/-- ℚ is denumerable, so we can pick an explicit equivalence with ℕ. -/
lemma rat_equiv_nat : Nonempty (ℚ ≃ ℕ) := by
  classical
  exact ⟨Denumerable.eqv ℚ⟩

/-- Example 0.3.32: The set of rational numbers is countable (in fact countably
infinite), e.g., by enumerating positive fractions in a grid and then inserting `0`
and their negatives. -/
theorem rationals_countablyInfinite :
    countablyInfiniteElementCollection (A := (Set.univ : Set ℚ)) := by
  rcases rat_equiv_nat with ⟨e⟩
  refine ⟨(Equiv.subtypeUnivEquiv (α := ℚ) (p := (Set.univ : Set ℚ)) ?_).trans e⟩
  intro x
  trivial

/-- Definition 0.3.33: The power set `𝒫(A)` of a set `A` is the set of all subsets of
`A`. -/
abbrev powerSetElementCollection (A : Set α) : Set (Set α) :=
  𝒫 A

/-- The book's power set of `A` is mathlib's `𝒫 A`. -/
theorem powerSetElementCollection_eq (A : Set α) :
    powerSetElementCollection (A := A) = 𝒫 A := by
  rfl

/-- Membership in the power set means being a subset. -/
theorem mem_powerSetElementCollection {A : Set α} {B : Set α} :
    B ∈ powerSetElementCollection (A := A) ↔ B ⊆ A := by
  rfl

/-- Theorem 0.3.34 (Cantor). For any set `A`, the cardinality of `A` is strictly less
than the cardinality of its power set `𝒫 A`; in particular there is no surjection
from `A` onto `𝒫 A`. -/
theorem cantor_cardinal_lt (A : Type u) : Cardinal.mk A < Cardinal.mk (Set A) := by
  simpa [Cardinal.mk_set] using (Cardinal.cantor (Cardinal.mk A))

theorem no_surjection_to_powerSet (A : Type u) (f : A → Set A) :
    ¬ Function.Surjective f := by
  simpa using (Function.cantor_surjective f)

end Section03
end Chap00

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

/-- Definition 0.3.19: For a set `A`, a binary relation on `A` is a subset `R ⊆ A × A`
of ordered pairs where the relation is said to hold; we write `a R b` instead of
`(a, b) ∈ R`. -/
abbrev BinaryRelationOn (A : Set α) : Type _ :=
  Set (Subtype A × Subtype A)

/-- The book's binary relations on a set `A` correspond to mathlib relations on the
subtype of `A`. -/
def binaryRelationOn_equiv_relation (A : Set α) :
    BinaryRelationOn A ≃ (Subtype A → Subtype A → Prop) := by
  classical
  refine
    { toFun := fun R x y => (x, y) ∈ R
      invFun := fun r => {p | r p.1 p.2}
      left_inv := ?_
      right_inv := ?_ }
  · intro R; ext p; rfl
  · intro r; funext x y; rfl

/-- Example 0.3.20: On the finite set `A = {1,2,3}` the relation `<` corresponds to the
set of pairs `{(1,2), (1,3), (2,3)}`, so `1 < 2` holds but `3 < 1` does not. The relation
`=` is given by `{(1,1), (2,2), (3,3)}`. Any subset of `A × A` is a relation; for example
`† = {(1,2), (2,1), (2,3), (3,1)}` satisfies `1 † 2` and `3 † 1` but not `1 † 3`. -/
def finiteExampleSet : Set ℕ := {x | x = 1 ∨ x = 2 ∨ x = 3}

def exampleLtRelationPairs : Set (ℕ × ℕ) :=
  {p | p = (1, 2) ∨ p = (1, 3) ∨ p = (2, 3)}

def exampleEqRelationPairs : Set (ℕ × ℕ) :=
  {p | p = (1, 1) ∨ p = (2, 2) ∨ p = (3, 3)}

def daggerRelationPairs : Set (ℕ × ℕ) :=
  {p | p = (1, 2) ∨ p = (2, 1) ∨ p = (2, 3) ∨ p = (3, 1)}

theorem example_relation_membership :
    (1, 2) ∈ exampleLtRelationPairs ∧ (3, 1) ∉ exampleLtRelationPairs ∧
      (1, 1) ∈ exampleEqRelationPairs ∧ (3, 3) ∈ exampleEqRelationPairs ∧
        (1, 2) ∈ daggerRelationPairs ∧ (3, 1) ∈ daggerRelationPairs ∧
          (1, 3) ∉ daggerRelationPairs := by
  constructor
  · simp [exampleLtRelationPairs]
  constructor
  · simp [exampleLtRelationPairs]
  constructor
  · simp [exampleEqRelationPairs]
  constructor
  · simp [exampleEqRelationPairs]
  constructor
  · simp [daggerRelationPairs]
  constructor
  · simp [daggerRelationPairs]
  · simp [daggerRelationPairs]

/-- Definition 0.3.21: A relation `R` on a set `A` is (i) reflexive if `a R a` for all
`a ∈ A`; (ii) symmetric if `a R b` implies `b R a`; (iii) transitive if `a R b` and
`b R c` imply `a R c`. A relation that is reflexive, symmetric, and transitive is an
equivalence relation. -/
abbrev ReflexiveRelationOn (A : Set α) (R : Subtype A → Subtype A → Prop) : Prop :=
  Reflexive R

/-- The book's reflexive relation on `A` is mathlib's `Reflexive` predicate on the
underlying relation on `Subtype A`. -/
theorem reflexiveRelationOn_iff (A : Set α) (R : Subtype A → Subtype A → Prop) :
    ReflexiveRelationOn A R ↔ Reflexive R := by
  rfl

/-- The book's symmetric relation on `A` is mathlib's `Symmetric` predicate on the
underlying relation on `Subtype A`. -/
abbrev SymmetricRelationOn (A : Set α) (R : Subtype A → Subtype A → Prop) : Prop :=
  Symmetric R

theorem symmetricRelationOn_iff (A : Set α) (R : Subtype A → Subtype A → Prop) :
    SymmetricRelationOn A R ↔ Symmetric R := by
  rfl

/-- The book's transitive relation on `A` is mathlib's `Transitive` predicate on the
underlying relation on `Subtype A`. -/
abbrev TransitiveRelationOn (A : Set α) (R : Subtype A → Subtype A → Prop) : Prop :=
  Transitive R

theorem transitiveRelationOn_iff (A : Set α) (R : Subtype A → Subtype A → Prop) :
    TransitiveRelationOn A R ↔ Transitive R := by
  rfl

/-- The book's notion of equivalence relation collects reflexivity, symmetry, and
transitivity. -/
abbrev equivalenceRelationOn (A : Set α) (R : Subtype A → Subtype A → Prop) : Prop :=
  ReflexiveRelationOn A R ∧ SymmetricRelationOn A R ∧ TransitiveRelationOn A R

/-- The book's equivalence relations on `A` coincide with mathlib's `Equivalence`
structure for relations on `Subtype A`. -/
theorem equivalenceRelationOn_iff_equivalence (A : Set α)
    (R : Subtype A → Subtype A → Prop) :
    equivalenceRelationOn A R ↔ Equivalence R := by
  constructor
  · rintro ⟨hR, hS, hT⟩
    refine ⟨?_, ?_, ?_⟩
    · exact hR
    · intro x y hxy
      exact hS hxy
    · intro x y z hxy hyz
      exact hT hxy hyz
  · intro h
    constructor
    · exact h.refl
    · constructor
      · intro x y hxy
        exact h.symm hxy
      · intro x y z hxy hyz
        exact h.trans hxy hyz

/-- Example 0.3.22: On `A = {1,2,3}`, the usual `<` is transitive but neither reflexive
nor symmetric. The relation `≤` (restricted to `A`) given by
`{(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)}` is reflexive and transitive but not symmetric.
The relation `⋆` with pairs `{(1,1),(1,2),(2,1),(2,2),(3,3)}` is an equivalence relation. -/
def exampleRelationLtOnA : Subtype finiteExampleSet → Subtype finiteExampleSet → Prop :=
  fun x y => x.1 < y.1

def exampleRelationLeOnA : Subtype finiteExampleSet → Subtype finiteExampleSet → Prop :=
  fun x y => x.1 ≤ y.1

def exampleStarRelation (x y : Subtype finiteExampleSet) : Prop :=
  (x.1 ≤ 2 ∧ y.1 ≤ 2) ∨ (x.1 = 3 ∧ y.1 = 3)

/-- Any element of `finiteExampleSet` is at most `2` or equal to `3`. -/
lemma finiteExampleSet_le2_or_eq3 (x : Subtype finiteExampleSet) :
    x.1 ≤ 2 ∨ x.1 = 3 := by
  rcases x.property with hx | hx | hx
  · left; nlinarith [hx]
  · left; nlinarith [hx]
  · right; exact hx

theorem exampleRelationLt_properties :
    Transitive exampleRelationLtOnA ∧ ¬ Reflexive exampleRelationLtOnA ∧
      ¬ Symmetric exampleRelationLtOnA := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y z hxy hyz
    exact lt_trans hxy hyz
  · intro h
    have h1mem : finiteExampleSet 1 := by
      left; rfl
    have h1 := h ⟨1, h1mem⟩
    exact (lt_irrefl _ h1)
  · intro h
    have h1mem : finiteExampleSet 1 := by
      left; rfl
    have h2mem : finiteExampleSet 2 := by
      right; left; rfl
    have h12 :
        exampleRelationLtOnA ⟨1, h1mem⟩ ⟨2, h2mem⟩ := by
      simp [exampleRelationLtOnA]
    have h21 : (2 : ℕ) < 1 := h h12
    have : ¬ (2 : ℕ) < 1 := by decide
    exact this h21

theorem exampleRelationLe_properties :
    Reflexive exampleRelationLeOnA ∧ Transitive exampleRelationLeOnA ∧
      ¬ Symmetric exampleRelationLeOnA := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [exampleRelationLeOnA]
  · intro x y z hxy hyz
    exact le_trans hxy hyz
  · intro h
    have h1mem : finiteExampleSet 1 := by
      left; rfl
    have h2mem : finiteExampleSet 2 := by
      right; left; rfl
    have h12 :
        exampleRelationLeOnA ⟨1, h1mem⟩ ⟨2, h2mem⟩ := by
      simp [exampleRelationLeOnA]
    have h21 : (2 : ℕ) ≤ 1 := h h12
    have : ¬ (2 : ℕ) ≤ 1 := by decide
    exact this h21

theorem exampleStarRelation_equivalence : Equivalence exampleStarRelation := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rcases finiteExampleSet_le2_or_eq3 x with hx | hx
    · left; exact ⟨hx, hx⟩
    · right; exact ⟨hx, hx⟩
  · intro x y hxy
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · left; exact ⟨hy, hx⟩
    · right; exact ⟨hy, hx⟩
  · intro x y z hxy hyz
    rcases hxy with ⟨hx2, hy2⟩ | ⟨hx3, hy3⟩
    · rcases hyz with ⟨hy2', hz2⟩ | ⟨hy3', hz3⟩
      · left; exact ⟨hx2, hz2⟩
      · have : False := by
          have hnot : ¬ (3 : ℕ) ≤ 2 := by decide
          exact hnot (by simp [hy3'] at hy2)
        exact this.elim
    · rcases hyz with ⟨hy2', hz2⟩ | ⟨hy3', hz3⟩
      · have : False := by
          have hnot : ¬ (3 : ℕ) ≤ 2 := by decide
          exact hnot (by simp [hy3] at hy2')
        exact this.elim
      · right; exact ⟨hx3, hz3⟩

/-- Definition 0.3.23: For a set `A` with an equivalence relation `R` and an element
`a ∈ A`, the equivalence class of `a`, denoted `[a]`, is the set `{ x ∈ A | a R x }`. -/
def equivalenceClass (A : Set α) (R : Subtype A → Subtype A → Prop) (a : Subtype A) :
    Set (Subtype A) :=
  {x | R a x}

/-- The book's equivalence class agrees with the class coming from the `Setoid` built from
the equivalence relation `R` on `A`. -/
theorem equivalenceClass_eq_setoid_r (A : Set α) (R : Subtype A → Subtype A → Prop)
    (hR : Equivalence R) (a : Subtype A) :
    equivalenceClass A R a =
      {x : Subtype A | ({ r := R, iseqv := hR } : Setoid (Subtype A)).r a x} := by
  rfl

/-- Proposition 0.3.24: If `R` is an equivalence relation on `A`, then every `a ∈ A`
lies in exactly one equivalence class. Moreover, `a R b` if and only if `[a] = [b]`. -/
theorem equivalenceClass_unique (A : Set α) (R : Subtype A → Subtype A → Prop)
    (hR : Equivalence R) (a : Subtype A) :
    a ∈ equivalenceClass A R a ∧
      ∀ b : Subtype A,
        a ∈ equivalenceClass A R b → equivalenceClass A R b = equivalenceClass A R a := by
  constructor
  · exact hR.refl a
  · intro b hab
    apply Set.ext
    intro x
    constructor
    · intro hx
      have hba : R a b := hR.symm hab
      exact hR.trans hba hx
    · intro hx
      exact hR.trans hab hx

theorem related_iff_equivalenceClass_eq (A : Set α) (R : Subtype A → Subtype A → Prop)
    (hR : Equivalence R) (a b : Subtype A) :
    R a b ↔ equivalenceClass A R a = equivalenceClass A R b := by
  constructor
  · intro h
    apply Set.ext
    intro x
    constructor
    · intro hx
      have hba : R b a := hR.symm h
      exact hR.trans hba hx
    · intro hx
      exact hR.trans h hx
  · intro h
    have ha : a ∈ equivalenceClass A R a := hR.refl a
    have : a ∈ equivalenceClass A R b := by simpa [h] using ha
    exact hR.symm this

/-- Example 0.3.25: Rational numbers can be presented as equivalence classes of pairs
`(a, b)` with `a ∈ ℤ` and a positive `b ∈ ℕ` under the relation `(a, b) ∼ (c, d)` when
`a * d = b * c`. The class of `(a, b)` is typically written `a / b`. -/
def RatPair : Type :=
  {p : ℤ × ℕ // 0 < p.2}

def ratPairRel (p q : RatPair) : Prop :=
  p.1.1 * (q.1.2 : ℤ) = q.1.1 * (p.1.2 : ℤ)

/-- The relation used to define rationals as pairs is an equivalence relation. -/
theorem ratPairRel_equivalence : Equivalence ratPairRel := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    dsimp [ratPairRel]
  · intro p q h
    simpa [ratPairRel] using Eq.symm h
  · intro p q r h1 h2
    dsimp [ratPairRel] at h1 h2 ⊢
    have h1' := congrArg (fun t => t * (r.1.2 : ℤ)) h1
    have h2' := congrArg (fun t => t * (p.1.2 : ℤ)) h2
    have h2'' : q.1.1 * (p.1.2 : ℤ) * (r.1.2 : ℤ) =
        r.1.1 * (q.1.2 : ℤ) * (p.1.2 : ℤ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h2'
    have h : p.1.1 * (q.1.2 : ℤ) * (r.1.2 : ℤ) =
        r.1.1 * (q.1.2 : ℤ) * (p.1.2 : ℤ) := by
      calc
        p.1.1 * (q.1.2 : ℤ) * (r.1.2 : ℤ) =
            q.1.1 * (p.1.2 : ℤ) * (r.1.2 : ℤ) := h1'
        _ = r.1.1 * (q.1.2 : ℤ) * (p.1.2 : ℤ) := h2''
    have hq : (q.1.2 : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt q.2)
    exact mul_left_cancel₀ hq (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h)

/-- The setoid of rational-number representatives as pairs of an integer and a natural
number with positive denominator. -/
def ratPairSetoid : Setoid RatPair :=
  { r := ratPairRel
    iseqv := ratPairRel_equivalence }

/-- Rational numbers as the quotient of integer–natural pairs by the relation `(a, b) ∼ (c, d)`
when `a * d = b * c`. -/
abbrev rationalNumbersQuot : Type :=
  Quot ratPairSetoid

/-- Interpret a numerator–denominator pair as a rational number. -/
def ratPairToRat (p : RatPair) : ℚ :=
  (p.1.1 : ℚ) / (p.1.2 : ℚ)

/-- Cross-multiplication characterizes when two pairs represent the same rational. -/
lemma ratPairRel_iff_toRat_eq (p q : RatPair) :
    ratPairRel p q ↔ ratPairToRat p = ratPairToRat q := by
  constructor
  · intro h
    have hp : (p.1.2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt p.2)
    have hq : (q.1.2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt q.2)
    have h' : (p.1.1 : ℚ) * q.1.2 = (q.1.1 : ℚ) * p.1.2 := by
      exact_mod_cast h
    dsimp [ratPairToRat]
    field_simp [hp, hq]
    simpa [mul_comm] using h'
  · intro h
    have hp : (p.1.2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt p.2)
    have hq : (q.1.2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt q.2)
    dsimp [ratPairToRat] at h
    field_simp [hp, hq] at h
    norm_cast at h
    simpa [ratPairRel, mul_comm] using h

/-- The quotient of integer–natural pairs is equivalent to mathlib's rationals `ℚ`. -/
noncomputable def rationalNumbersQuot_equiv_rat : rationalNumbersQuot ≃ ℚ := by
  classical
  refine
    { toFun := Quot.lift ratPairToRat (fun p q h => (ratPairRel_iff_toRat_eq p q).1 h)
      invFun := fun q =>
        Quot.mk _ ⟨(q.num, q.den), by
          have h := Rat.den_pos q
          simpa using h⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    refine Quot.induction_on x ?_
    intro p
    apply Quot.sound
    have h :
        ratPairToRat
            ⟨((ratPairToRat p).num, (ratPairToRat p).den), by
              have h := Rat.den_pos (ratPairToRat p)
              simpa using h⟩ =
          ratPairToRat p := by
      simpa [ratPairToRat] using (Rat.num_div_den (ratPairToRat p))
    exact (ratPairRel_iff_toRat_eq _ _).2 h
  · intro q
    simp [ratPairToRat, Rat.num_div_den]

end Section03
end Chap00

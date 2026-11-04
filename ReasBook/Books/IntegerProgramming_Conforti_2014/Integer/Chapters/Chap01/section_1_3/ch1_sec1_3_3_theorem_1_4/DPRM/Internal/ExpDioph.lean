/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import Mathlib.NumberTheory.Dioph

/-!
# Exponential Diophantine relations

Issue #16, and the first piece of M4. This layer is **route-independent**: both the machine
route and the direct route arithmetise into exponential Diophantine relations, and #15's
spike must produce one, so it is a prerequisite for the route decision rather than a
consequence of it.

## Why ℕ-valued

`ExpTerm` is valued in `ℕ`, and `ExpDioph` is *equality of two ℕ-valued terms* under ℕ
witnesses. An `ℤ`-valued exponential term would leave `s ^ t` ill-specified when the
exponent evaluates negatively, and `Dioph.pow_dioph` supplies only the graph of **natural**
exponentiation. So there is no negation, and equations are `s = t` rather than `p = 0`.

The payoff is that the bridge to `Dioph` is a structural induction over combinators mathlib
already has. `DiophFn` is itself ℕ-valued, and every term constructor here is backed by a
`DiophFn`-valued lemma:

| constructor | mathlib |
|---|---|
| `var`, `const` | `Dioph.proj_dioph`, `Dioph.const_dioph` |
| `add`, `mul`, `pow` | `Dioph.add_dioph`, `Dioph.mul_dioph`, `Dioph.pow_dioph` |
| `div`, `mod` | `Dioph.div_dioph`, `Dioph.mod_dioph` |
| `sub` (truncated) | `Dioph.sub_dioph` |

`div` and `mod` are constructors for a concrete reason: base-`u` digit extraction (#33) needs
them at the `ExpDioph` level, and `ExpDioph.dioph` is one-directional, so a `Dioph`-level
lemma could not be pulled back. Relations that are *not* `DiophFn`-valued in mathlib —
`≤`, `<`, `∣` — appear instead as closure lemmas below.

`sub` is truncated subtraction, and it earns its place by making **conjunction** available.
Over `ℤ` a system of equations is combined by sum of squares (`Poly.sumsq`); over `ℕ` that is
unavailable, but

```
s₁ = t₁ ∧ s₂ = t₂  ↔  (s₁ ∸ t₁) + (t₁ ∸ s₁) + (s₂ ∸ t₂) + (t₂ ∸ s₂) = 0
```

does the same job, since a sum of naturals vanishes iff every summand does. Without it
`ExpDioph` could express only single equations, which is not enough for any real
arithmetisation — a packed machine run is a *system* whose constraints share witnesses.

## Universes

Everything here lives at `Type 0`. That is forced: `Dioph` itself is universe-polymorphic,
but mathlib states the entire `DiophFn` combinator API — `add_dioph`, `mul_dioph`,
`pow_dioph`, `div_dioph`, `mod_dioph`, `eq_dioph` — inside a section fixing
`variable {α : Type}`. No loss here, since every variable type in this project is `Fin n`,
but it is a real restriction on the API and worth generalising upstream some day.

This syntax stays internal to the DPRM core; it is not the DSL of #29, having no
fresh-variable discipline, no gadget calls and no extraction.
-/

@[expose] public section

namespace Hilbert10

variable {α β : Type}

/-- Syntax of exponential polynomials over `ℕ`. -/
inductive ExpTerm (α : Type) : Type
  | var : α → ExpTerm α
  | const : ℕ → ExpTerm α
  | add : ExpTerm α → ExpTerm α → ExpTerm α
  | mul : ExpTerm α → ExpTerm α → ExpTerm α
  | pow : ExpTerm α → ExpTerm α → ExpTerm α
  | div : ExpTerm α → ExpTerm α → ExpTerm α
  | mod : ExpTerm α → ExpTerm α → ExpTerm α
  | sub : ExpTerm α → ExpTerm α → ExpTerm α

namespace ExpTerm

/-- Value of an exponential term at an assignment. -/
def eval : ExpTerm α → (α → ℕ) → ℕ
  | var i, x => x i
  | const n, _ => n
  | add s t, x => s.eval x + t.eval x
  | mul s t, x => s.eval x * t.eval x
  | pow s t, x => s.eval x ^ t.eval x
  | div s t, x => s.eval x / t.eval x
  | mod s t, x => s.eval x % t.eval x
  | sub s t, x => s.eval x - t.eval x

/-- **The bridge.** Every exponential term denotes a Diophantine function.

One structural induction, each case a mathlib combinator; `pow` is where
`Pell.eq_pow_of_pell` enters, through `Dioph.pow_dioph`. -/
theorem diophFn (t : ExpTerm α) : Dioph.DiophFn fun x => t.eval x := by
  induction t with
  | var i => exact Dioph.proj_dioph i
  | const n => exact Dioph.const_dioph n
  | add s t hs ht => exact Dioph.add_dioph hs ht
  | mul s t hs ht => exact Dioph.mul_dioph hs ht
  | pow s t hs ht => exact Dioph.pow_dioph hs ht
  | div s t hs ht => exact Dioph.div_dioph hs ht
  | mod s t hs ht => exact Dioph.mod_dioph hs ht
  | sub s t hs ht => exact Dioph.sub_dioph hs ht

/-- Reindex the variables of a term. -/
def map (f : α → β) : ExpTerm α → ExpTerm β
  | var i => var (f i)
  | const n => const n
  | add s t => add (s.map f) (t.map f)
  | mul s t => mul (s.map f) (t.map f)
  | pow s t => pow (s.map f) (t.map f)
  | div s t => div (s.map f) (t.map f)
  | mod s t => mod (s.map f) (t.map f)
  | sub s t => sub (s.map f) (t.map f)

@[simp] theorem eval_map (f : α → β) (t : ExpTerm α) (x : β → ℕ) :
    (t.map f).eval x = t.eval (x ∘ f) := by
  induction t <;> simp_all [map, eval]

/-- Substitute a term for each variable. Unlike `map`, which only renames variables, this
replaces them by arbitrary terms — which is what an arithmetisation needs when a local
witness variable has to become a lookup into a coded sequence. -/
def subst (f : α → ExpTerm β) : ExpTerm α → ExpTerm β
  | var i => f i
  | const n => const n
  | add s t => add (s.subst f) (t.subst f)
  | mul s t => mul (s.subst f) (t.subst f)
  | pow s t => pow (s.subst f) (t.subst f)
  | div s t => div (s.subst f) (t.subst f)
  | mod s t => mod (s.subst f) (t.subst f)
  | sub s t => sub (s.subst f) (t.subst f)

@[simp] theorem eval_subst (f : α → ExpTerm β) (t : ExpTerm α) (v : β → ℕ) :
    (t.subst f).eval v = t.eval fun i => (f i).eval v := by
  induction t <;> simp_all [subst, eval]

end ExpTerm

/-- A set is exponential Diophantine when it is the projection of an equality between two
exponential terms. -/
def ExpDioph (S : Set (α → ℕ)) : Prop :=
  ∃ (β : Type) (s t : ExpTerm (α ⊕ β)),
    ∀ v, v ∈ S ↔ ∃ w : β → ℕ, s.eval (Sum.elim v w) = t.eval (Sum.elim v w)

namespace ExpDioph

/-- **Exponential Diophantine implies Diophantine.** The witnesses are projected away by
`Dioph.ex_dioph`, and the equation is `Dioph` by `Dioph.eq_dioph` applied to the two
`DiophFn`s from `ExpTerm.diophFn`. -/
theorem dioph {S : Set (α → ℕ)} (h : ExpDioph S) : Dioph S := by
  obtain ⟨β, s, t, hst⟩ := h
  have heq : Dioph {z : α ⊕ β → ℕ | s.eval z = t.eval z} :=
    Dioph.eq_dioph s.diophFn t.diophFn
  exact (Dioph.ex_dioph heq).ext fun v => (hst v).symm

/-- Two natural numbers are equal iff their two truncated differences both vanish. This is
the ℕ substitute for the sum-of-squares trick that combines a system of equations over `ℤ`. -/
theorem eq_iff_sub_add_sub {a b : ℕ} : a = b ↔ (a - b) + (b - a) = 0 := by omega

/-- `ExpDioph` is closed under conjunction, with the two witness blocks combined. This is
what makes a *system* of constraints expressible, which every arithmetisation needs. -/
theorem and {S T : Set (α → ℕ)} (hS : ExpDioph S) (hT : ExpDioph T) : ExpDioph (S ∩ T) := by
  obtain ⟨β, s₁, t₁, h₁⟩ := hS
  obtain ⟨γ, s₂, t₂, h₂⟩ := hT
  -- Reindex each equation into the combined witness block `β ⊕ γ`.
  let f₁ : α ⊕ β → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (fun b => Sum.inr (Sum.inl b))
  let f₂ : α ⊕ γ → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (fun c => Sum.inr (Sum.inr c))
  refine ⟨β ⊕ γ,
    .add (.add (.sub (s₁.map f₁) (t₁.map f₁)) (.sub (t₁.map f₁) (s₁.map f₁)))
      (.add (.sub (s₂.map f₂) (t₂.map f₂)) (.sub (t₂.map f₂) (s₂.map f₂))),
    .const 0, fun v => ?_⟩
  have key : ∀ (w : (β ⊕ γ) → ℕ),
      (Sum.elim v w ∘ f₁ = Sum.elim v (w ∘ Sum.inl)) ∧
        (Sum.elim v w ∘ f₂ = Sum.elim v (w ∘ Sum.inr)) := by
    intro w
    constructor <;> (funext z; cases z <;> rfl)
  constructor
  · rintro ⟨hv₁, hv₂⟩
    obtain ⟨w₁, hw₁⟩ := (h₁ v).mp hv₁
    obtain ⟨w₂, hw₂⟩ := (h₂ v).mp hv₂
    refine ⟨Sum.elim w₁ w₂, ?_⟩
    have e := key (Sum.elim w₁ w₂)
    simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2, Sum.elim_comp_inl, Sum.elim_comp_inr]
    omega
  · rintro ⟨w, hw⟩
    have e := key w
    simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2] at hw
    refine ⟨(h₁ v).mpr ⟨w ∘ Sum.inl, by omega⟩, (h₂ v).mpr ⟨w ∘ Sum.inr, by omega⟩⟩

/-- `ExpDioph` is closed under disjunction, via the *product* of the two symmetric equality
gaps: a product of naturals vanishes exactly when one factor does. Finite dispatch over a fixed
program's instruction list (#45) is repeated use of this, which is why it is worth having
alongside `and` rather than routing through complements. -/
theorem or {S T : Set (α → ℕ)} (hS : ExpDioph S) (hT : ExpDioph T) : ExpDioph (S ∪ T) := by
  obtain ⟨β, s₁, t₁, h₁⟩ := hS
  obtain ⟨γ, s₂, t₂, h₂⟩ := hT
  let f₁ : α ⊕ β → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (fun b => Sum.inr (Sum.inl b))
  let f₂ : α ⊕ γ → α ⊕ (β ⊕ γ) := Sum.elim Sum.inl (fun c => Sum.inr (Sum.inr c))
  refine ⟨β ⊕ γ,
    .mul (.add (.sub (s₁.map f₁) (t₁.map f₁)) (.sub (t₁.map f₁) (s₁.map f₁)))
      (.add (.sub (s₂.map f₂) (t₂.map f₂)) (.sub (t₂.map f₂) (s₂.map f₂))),
    .const 0, fun v => ?_⟩
  have key : ∀ (w : (β ⊕ γ) → ℕ),
      (Sum.elim v w ∘ f₁ = Sum.elim v (w ∘ Sum.inl)) ∧
        (Sum.elim v w ∘ f₂ = Sum.elim v (w ∘ Sum.inr)) := by
    intro w
    constructor <;> (funext z; cases z <;> rfl)
  constructor
  · rintro (hv | hv)
    · obtain ⟨w₁, hw₁⟩ := (h₁ v).mp hv
      refine ⟨Sum.elim w₁ (fun _ => 0), ?_⟩
      have e := key (Sum.elim w₁ (fun _ => 0))
      simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2, Sum.elim_comp_inl, Sum.elim_comp_inr]
      exact Nat.mul_eq_zero.mpr (Or.inl (by omega))
    · obtain ⟨w₂, hw₂⟩ := (h₂ v).mp hv
      refine ⟨Sum.elim (fun _ => 0) w₂, ?_⟩
      have e := key (Sum.elim (fun _ => 0) w₂)
      simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2, Sum.elim_comp_inl, Sum.elim_comp_inr]
      exact Nat.mul_eq_zero.mpr (Or.inr (by omega))
  · rintro ⟨w, hw⟩
    have e := key w
    simp only [ExpTerm.eval, ExpTerm.eval_map, e.1, e.2] at hw
    rcases Nat.mul_eq_zero.mp hw with h | h
    · exact Or.inl ((h₁ v).mpr ⟨w ∘ Sum.inl, by omega⟩)
    · exact Or.inr ((h₂ v).mpr ⟨w ∘ Sum.inr, by omega⟩)

/-- The empty relation. The base case of a finite disjunction. -/
theorem of_false : ExpDioph (∅ : Set (α → ℕ)) :=
  ⟨Empty, .const 0, .const 1, fun v => by simp [ExpTerm.eval]⟩

/-- `ExpDioph` respects extensional equality of relations. -/
theorem congr {S T : Set (α → ℕ)} (h : ExpDioph S) (hST : ∀ v, v ∈ S ↔ v ∈ T) :
    ExpDioph T := by
  obtain ⟨β, s, t, hst⟩ := h
  exact ⟨β, s, t, fun v => (hST v).symm.trans (hst v)⟩

/-- Reindexing the variables of an exponential Diophantine set. -/
theorem reindex {S : Set (α → ℕ)} (h : ExpDioph S) (f : α → β) :
    ExpDioph {v : β → ℕ | (v ∘ f) ∈ S} := by
  obtain ⟨γ, s, t, hst⟩ := h
  refine ⟨γ, s.map (Sum.map f id), t.map (Sum.map f id), fun v => ?_⟩
  have e : ∀ w : γ → ℕ,
      Sum.elim v w ∘ Sum.map f id = Sum.elim (v ∘ f) w := by
    intro w
    funext z
    cases z <;> rfl
  simp only [Set.mem_setOf_eq, ExpTerm.eval_map, e]
  exact hst (v ∘ f)

/-- Projecting away the last block of variables. Mirrors `Dioph.ex_dioph`; this is the
primary projection operation, not a variant of another lemma. -/
theorem ex {S : Set (α ⊕ β → ℕ)} (h : ExpDioph S) :
    ExpDioph {v : α → ℕ | ∃ w : β → ℕ, Sum.elim v w ∈ S} := by
  obtain ⟨γ, s, t, hst⟩ := h
  -- Combine the projected block with the existing witnesses.
  let f : (α ⊕ β) ⊕ γ → α ⊕ (β ⊕ γ) :=
    Sum.elim (Sum.elim Sum.inl (fun b => Sum.inr (Sum.inl b))) (fun c => Sum.inr (Sum.inr c))
  refine ⟨β ⊕ γ, s.map f, t.map f, fun v => ?_⟩
  have e : ∀ (w : β → ℕ) (u : γ → ℕ),
      Sum.elim v (Sum.elim w u) ∘ f = Sum.elim (Sum.elim v w) u := by
    intro w u
    funext z
    rcases z with (a | b) | c <;> rfl
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨u, hu⟩ := (hst (Sum.elim v w)).mp hw
    exact ⟨Sum.elim w u, by simpa only [ExpTerm.eval_map, e w u] using hu⟩
  · rintro ⟨wu, hwu⟩
    refine ⟨wu ∘ Sum.inl, (hst _).mpr ⟨wu ∘ Sum.inr, ?_⟩⟩
    have := hwu
    simp only [ExpTerm.eval_map] at this
    rwa [show Sum.elim v wu ∘ f
        = Sum.elim (Sum.elim v (wu ∘ Sum.inl)) (wu ∘ Sum.inr) by
      funext z; rcases z with (a | b) | c <;> rfl] at this

/-- `≤` between exponential terms, via a slack witness. -/
theorem of_le {s t : ExpTerm α} : ExpDioph {v | s.eval v ≤ t.eval v} := by
  refine ⟨Unit, .add (s.map Sum.inl) (.var (Sum.inr ())), t.map Sum.inl, fun v => ?_⟩
  simp only [Set.mem_setOf_eq, ExpTerm.eval, ExpTerm.eval_map, Sum.elim_comp_inl]
  constructor
  · intro h
    exact ⟨fun _ => t.eval v - s.eval v, by simp [Sum.elim_inr]; omega⟩
  · rintro ⟨w, hw⟩
    simp only [Sum.elim_inr] at hw
    omega

/-- `<` between exponential terms, via a slack witness. -/
theorem of_lt {s t : ExpTerm α} : ExpDioph {v | s.eval v < t.eval v} := by
  refine ⟨Unit, .add (.add (s.map Sum.inl) (.var (Sum.inr ()))) (.const 1),
    t.map Sum.inl, fun v => ?_⟩
  simp only [Set.mem_setOf_eq, ExpTerm.eval, ExpTerm.eval_map, Sum.elim_comp_inl]
  constructor
  · intro h
    exact ⟨fun _ => t.eval v - s.eval v - 1, by simp [Sum.elim_inr]; omega⟩
  · rintro ⟨w, hw⟩
    simp only [Sum.elim_inr] at hw
    omega

/-- Divisibility between exponential terms, via a cofactor witness. -/
theorem of_dvd {s t : ExpTerm α} : ExpDioph {v | s.eval v ∣ t.eval v} := by
  refine ⟨Unit, .mul (s.map Sum.inl) (.var (Sum.inr ())), t.map Sum.inl, fun v => ?_⟩
  simp only [Set.mem_setOf_eq, ExpTerm.eval, ExpTerm.eval_map, Sum.elim_comp_inl]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun _ => c, by simp [Sum.elim_inr, hc]⟩
  · rintro ⟨w, hw⟩
    simp only [Sum.elim_inr] at hw
    exact ⟨w (), hw.symm⟩

/-- Any equation between exponential terms with no witnesses is exponential Diophantine. -/
theorem of_eq {s t : ExpTerm α} : ExpDioph {v | s.eval v = t.eval v} := by
  refine ⟨PEmpty, s.map Sum.inl, t.map Sum.inl, fun v => ?_⟩
  simp only [Set.mem_setOf_eq, ExpTerm.eval_map]
  exact ⟨fun h => ⟨PEmpty.elim, by simpa using h⟩, fun ⟨_, hw⟩ => by simpa using hw⟩

/-- The trivial condition. Needed as the base case of a finite conjunction, and as the branch
a statically false side condition collapses to. -/
theorem of_true : ExpDioph (Set.univ : Set (α → ℕ)) :=
  (of_eq (s := (.const 0 : ExpTerm α)) (t := .const 0)).congr fun _ => by simp

/-- A conjunction indexed by a list. Distinct from `ex`, whose quantifier ranges over an input
of the problem: the length here is fixed when the condition is written down. -/
theorem list_and {ι : Type} {S : ι → Set (α → ℕ)} (h : ∀ i, ExpDioph (S i)) :
    ∀ l : List ι, ExpDioph {v | ∀ i ∈ l, v ∈ S i}
  | [] => of_true.congr fun _ => by simp
  | i :: l => (((h i).and (list_and h l)).congr fun v => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_cons]
      constructor
      · rintro ⟨hi, hl⟩ j (rfl | hj)
        · exact hi
        · exact hl j hj
      · intro hall
        exact ⟨hall i (Or.inl rfl), fun j hj => hall j (Or.inr hj)⟩)

/-- **A finite conjunction over a fixed index type.** The number of conjuncts is determined by
the problem, not by its input, so this adds no quantifier: it unfolds to nested `and`. -/
theorem fin_and {ι : Type} [Finite ι] {S : ι → Set (α → ℕ)} (h : ∀ i, ExpDioph (S i)) :
    ExpDioph {v | ∀ i, v ∈ S i} := by
  have : Fintype ι := Fintype.ofFinite ι
  exact (list_and h (Finset.univ : Finset ι).toList).congr fun v => by
    simp [Finset.mem_toList]

end ExpDioph

/-! ### Finite sums of terms

A coefficient-weighted sum over a fixed index type is a term, built by folding: again the
length is fixed when the term is written down. -/

namespace ExpTerm

/-- The sum of a finite family of terms. -/
noncomputable def sumTerm {ι : Type} [Fintype ι] (t : ι → ExpTerm α) : ExpTerm α :=
  (((Finset.univ : Finset ι).toList).map t).foldr ExpTerm.add (ExpTerm.const 0)

theorem eval_foldr_add (v : α → ℕ) :
    ∀ l : List (ExpTerm α),
      (l.foldr ExpTerm.add (ExpTerm.const 0)).eval v = (l.map (fun t => t.eval v)).sum
  | [] => rfl
  | t :: l => by
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, eval]
    rw [eval_foldr_add v l]

@[simp] theorem eval_sumTerm {ι : Type} [Fintype ι] (t : ι → ExpTerm α) (v : α → ℕ) :
    (sumTerm t).eval v = ∑ i, (t i).eval v := by
  rw [sumTerm, eval_foldr_add, List.map_map]
  exact Finset.sum_map_toList Finset.univ fun i => (t i).eval v

end ExpTerm

/-! ### Acceptance tests

Nested powers are the case a representation that does not really compose fails on, so the
layer is exercised on one before anything is built above it.
-/

/-- A nested power: `2 ^ (2 ^ x₀) = x₁` is exponential Diophantine, and hence Diophantine. -/
theorem expDioph_two_pow_two_pow {α : Type} (i j : α) :
    ExpDioph {v : α → ℕ | 2 ^ (2 ^ v i) = v j} :=
  ExpDioph.of_eq (s := .pow (.const 2) (.pow (.const 2) (.var i))) (t := .var j)

theorem dioph_two_pow_two_pow {α : Type} (i j : α) :
    Dioph {v : α → ℕ | 2 ^ (2 ^ v i) = v j} :=
  (expDioph_two_pow_two_pow i j).dioph

/-- A term mixing every constructor, to check the induction covers them together. -/
theorem dioph_mixed {α : Type} (i j : α) :
    Dioph {v : α → ℕ | (v i ^ v j + v i * v j) / (v j % 3 + 1) = v i} :=
  (ExpDioph.of_eq
    (s := .div (.add (.pow (.var i) (.var j)) (.mul (.var i) (.var j)))
      (.add (.mod (.var j) (.const 3)) (.const 1)))
    (t := .var i)).dioph

end Hilbert10

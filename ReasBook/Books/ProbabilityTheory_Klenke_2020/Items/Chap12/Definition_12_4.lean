/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-- Permuting the first `n` coordinates of a sequence by `ρ` and leaving the tail fixed. -/
def permutePrefix {E : Type u} (n : ℕ) (ρ : Equiv.Perm (Fin n)) (x : ℕ → E) : ℕ → E :=
  x ∘ ρ.extendDomain Fin.equivSubtype

/-- Definition 12.4 (1): A map on `n` coordinates is symmetric when it is invariant under every
permutation of its `n` input coordinates. -/
def IsSymmetricMap {E : Type u} {E' : Type v} {n : ℕ} (f : (Fin n → E) → E') : Prop :=
  ∀ ρ : Equiv.Perm (Fin n), ∀ x : Fin n → E, f (x ∘ ρ) = f x

/-- Definition 12.4 (2): A map on sequences is `n`-symmetric when permuting the first `n`
coordinates leaves its value unchanged. -/
def IsNSymmetricSequenceMap {E : Type u} {E' : Type v} (n : ℕ) (F : (ℕ → E) → E') : Prop :=
  ∀ ρ : Equiv.Perm (Fin n), ∀ x : ℕ → E, F (permutePrefix n ρ x) = F x

/-- Definition 12.4 (3): A map on sequences is symmetric when it is `n`-symmetric for every
`n : ℕ`. -/
def IsSymmetricSequenceMap {E : Type u} {E' : Type v} (F : (ℕ → E) → E') : Prop :=
  ∀ n : ℕ, IsNSymmetricSequenceMap n F

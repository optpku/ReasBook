/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

open FreeGroup

-- Layer triage:
-- `source-facing`: Conway's family of groups `F_n`, given by `n` generators with the cyclic
-- relators `x_i x_{i+1} = x_{i+2}`.
-- `core/canonical`: `PresentedGroup` is mathlib's owner abstraction for groups given by
-- generators and relators, and `ZMod n` is the clean cyclic indexing type for the generator
-- family.
-- `bridge/view`: the textbook list
-- `x₁ x₂ = x₃, ..., x_{n-1} x_n = x₁, x_n x₁ = x₂`
-- is encoded as the uniform cyclic relator family indexed by `i : ZMod n`.
-- Domain sampling:
-- 1. `PresentedGroup rels` is the canonical quotient attached to a relator set in the free group.
-- 2. `PresentedGroup.of` supplies the canonical generators in the quotient.
-- 3. `PresentedGroup.one_of_mem` is the owner lemma saying a listed relator becomes trivial in the
--    presented group.
-- Primitive vs. derived:
-- the primitive data are the cyclic relators in the free group; the group `F_n` is the derived
-- canonical quotient by those relators, so no auxiliary wrapper structure is introduced.

namespace Conway

/-- The canonical cyclic relator `x_i x_{i+1} x_{i+2}^{-1}` used in Conway's presentations. -/
def relator (n : ℕ+) (i : ZMod n) : FreeGroup (ZMod n) :=
  of i * of (i + 1) * (of (i + 2))⁻¹

/-- The relator set for Conway's balanced presentation on `n` cyclically indexed generators. -/
def relators (n : ℕ+) : Set (FreeGroup (ZMod n)) :=
  Set.range (relator n)

/-- Definition 2-2-6: Conway's group `F_n` is the group presented by cyclically indexed generators
`x_i` with relators `x_i x_{i+1} = x_{i+2}` for all `i : ZMod n`, which reproduces the textbook
list `x₁ x₂ = x₃, ..., x_{n-1} x_n = x₁, x_n x₁ = x₂`. -/
abbrev F (n : ℕ+) : Type :=
  PresentedGroup (relators n)

notation "F_" n:arg => Conway.F n

/-- Conway's defining relation holds between the canonical generators of `F_n`. -/
-- Proof sketch: `PresentedGroup.one_of_mem` makes the relator word
-- `x_i x_{i+1} x_{i+2}^{-1}` trivial in the quotient, and simplifying that quotient equation
-- recovers the textbook relation `x_i x_{i+1} = x_{i+2}`.
theorem generator_relation (n : ℕ+) (i : ZMod n) :
    (PresentedGroup.of i : F_ n) * PresentedGroup.of (i + 1) = PresentedGroup.of (i + 2) := by
  have h : PresentedGroup.mk (relators n) (relator n i) = (1 : F_ n) :=
    PresentedGroup.one_of_mem (Set.mem_range_self i)
  have h' : ((PresentedGroup.of i : F_ n) * PresentedGroup.of (i + 1)) *
      (PresentedGroup.of (i + 2))⁻¹ = 1 := by
    simpa [relator, PresentedGroup.of, mul_assoc] using h
  have h'' := congrArg (fun x : F_ n ↦ x * PresentedGroup.of (i + 2)) h'
  simpa [mul_assoc] using h''

end Conway

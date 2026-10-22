/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Definition_2_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open FreeGroup

-- Layer triage:
-- `source-facing`: the cyclically indexed presentation `F_{r,n}` with `n` generators and the
-- relators `x_i x_{i+1} ... x_{i+r-1} = x_{i+r}`.
-- `core/canonical`: `PresentedGroup` is mathlib's owner abstraction for a group given by
-- generators and relators, and `ZMod n` is the canonical cyclic index type.
-- `bridge/view`: the displayed cyclic list of relators is encoded uniformly by a relator family
-- indexed by `i : ZMod n`, using a list product for the left-hand side word.
-- Domain sampling:
-- 1. `PresentedGroup rels` is the canonical group attached to a relator set in `FreeGroup`.
-- 2. `PresentedGroup.mk` and `PresentedGroup.one_of_mem` express that listed relators become
--    trivial in the quotient.
-- 3. `Conway.F` from the previous item is the `r = 2` specialization of the same owner-side
--    presentation pattern, so the generalized file should bridge back to it explicitly.
-- Primitive vs. derived:
-- the primitive data are the cyclic relator words indexed by `r : ℕ`; positivity of `r` is not
-- part of the canonical construction, while the group `F_{r,n}` is the derived quotient by those
-- relators, so no auxiliary package around the presentation is introduced.

namespace Conway.Generalized

/-- The cyclic relator `x_i x_{i+1} ... x_{i+r-1} x_{i+r}^{-1}` used in the presentation of
`F_{r,n}`. -/
def relator (r : ℕ) (n : ℕ+) (i : ZMod n) : FreeGroup (ZMod n) :=
  ((List.range r).map fun j ↦ of (i + j)).prod * (of (i + r))⁻¹

/-- The relator set for the cyclic presentation of `F_{r,n}` on generators indexed by `ZMod n`. -/
def relators (r : ℕ) (n : ℕ+) : Set (FreeGroup (ZMod n)) :=
  Set.range (relator r n)

/-- Definition 2-2-7: `F_{r,n}` is the group presented by cyclically indexed generators `x_i`
with relators `x_i x_{i+1} ... x_{i+r-1} = x_{i+r}` for all `i` modulo `n`. -/
abbrev F (r : ℕ) (n : ℕ+) : Type :=
  PresentedGroup (relators r n)

notation "F_{" r "," n "}" => Conway.Generalized.F r n

/-- The defining relation of `F_{r,n}` holds between its canonical generators. -/
-- Proof sketch: `PresentedGroup.one_of_mem` makes the relator word
-- `x_i x_{i+1} ... x_{i+r-1} x_{i+r}^{-1}` trivial in the quotient; multiplying by `x_{i+r}` on
-- the right recovers the source-facing relation.
theorem generator_relation (r : ℕ) (n : ℕ+) (i : ZMod n) :
    ((List.range r).map fun j ↦ (PresentedGroup.of (i + j) : F_{r,n})).prod =
      PresentedGroup.of (i + r) := by
  have hrel : PresentedGroup.mk (relators r n) (relator r n i) = (1 : F_{r,n}) :=
    PresentedGroup.one_of_mem (Set.mem_range_self i)
  have h : ((List.range r).map fun j ↦ (PresentedGroup.of (i + j) : F_{r,n})).prod *
      (PresentedGroup.of (i + r) : F_{r,n})⁻¹ = 1 := by
    simpa [relator, PresentedGroup.of, map_list_prod] using hrel
  have h' := congrArg (fun x : F_{r,n} ↦ x * PresentedGroup.of (i + r)) h
  simpa [mul_assoc] using h'

/-- The generalized relator specializes to Conway's original relator when `r = 2`. -/
theorem relator_two (n : ℕ+) (i : ZMod n) :
    relator 2 n i = Conway.relator n i := by
  rw [relator, show List.range 2 = [0, 1] by rfl, Conway.relator]
  simp

/-- The generalized cyclic relator set specializes to Conway's original relator set when `r = 2`.
-/
theorem relators_two (n : ℕ+) :
    relators 2 n = Conway.relators n := by
  ext w
  constructor <;> rintro ⟨i, rfl⟩
  · exact ⟨i, (relator_two n i).symm⟩
  · exact ⟨i, relator_two n i⟩

/-- The generalized presentation `F_{r,n}` recovers Conway's `F_n` when `r = 2`. -/
theorem F_two (n : ℕ+) : F_{2,n} = F_ n := by
  simp [F, Conway.F, relators_two n]

end Conway.Generalized

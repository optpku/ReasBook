/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_15.Clutter
public import Mathlib.Order.Minimal

public section

namespace Clutter

universe u

variable {α : Type u}
variable [DecidableEq α]

/-- A transversal of `S` on the finite ground set `E` is a finite subset of `E` meeting every
member of `S`. -/
structure IsTransversal (E : Finset α) (S : Set (Finset α)) (t : Finset α) : Prop where
  /-- A transversal stays inside the ground set. -/
  subset_ground : t ⊆ E
  /-- A transversal meets every member of the family. -/
  hits : ∀ s ∈ S, (s ∩ t).Nonempty

/-- Build a transversal witness from its ground-set and incidence properties. -/
def IsTransversal.ofSubsetGroundAndHits
    {E : Finset α} {S : Set (Finset α)} {t : Finset α}
    (h_ground : t ⊆ E)
    (h_hits : ∀ s ∈ S, (s ∩ t).Nonempty) :
    IsTransversal E S t :=
  ⟨h_ground, h_hits⟩

/-- Unfolding specification for `IsTransversal`. -/
theorem isTransversal_iff
    {E : Finset α} {S : Set (Finset α)} {t : Finset α} :
    IsTransversal E S t ↔
      t ⊆ E ∧ ∀ s ∈ S, (s ∩ t).Nonempty := by
  constructor
  · intro h
    -- Unpack the structure fields into the explicit transversal conditions.
    exact ⟨h.subset_ground, h.hits⟩
  · rintro ⟨h_ground, h_hits⟩
    -- Repackage the explicit conditions into the structure witness.
    exact IsTransversal.ofSubsetGroundAndHits h_ground h_hits

/-- The blocker of a finite set family is the family of its inclusion-minimal transversals. -/
def blocker (E : Finset α) (S : Set (Finset α)) : Set (Finset α) :=
  {t | Minimal (fun u ↦ IsTransversal E S u) t}

/-- Membership in the blocker means being an inclusion-minimal transversal. -/
theorem mem_blocker_iff
    {E : Finset α} {S : Set (Finset α)} {t : Finset α} :
    t ∈ blocker E S ↔ Minimal (fun u ↦ IsTransversal E S u) t := by
  -- The blocker was defined exactly as the set of minimal transversals.
  rfl

/-- Helper for Definition 2.16: two blocker members cannot be properly nested, so the blocker
forms an antichain under inclusion. -/
theorem blockerAntichain
    (E : Finset α) (S : Set (Finset α)) :
    IsAntichain (· ⊆ ·) (blocker E S) := by
  intro s hs t ht hne hst
  -- Translate blocker membership into minimal-transversal data on both sides.
  let hs_min : Minimal (fun u ↦ IsTransversal E S u) s := mem_blocker_iff.mp hs
  let ht_min : Minimal (fun u ↦ IsTransversal E S u) t := mem_blocker_iff.mp ht
  -- Minimality upgrades the inclusion `s ⊆ t` to the reverse inclusion `t ⊆ s`.
  have hts : t ⊆ s := ht_min.le_of_le hs_min.prop hst
  -- Mutual inclusion forces equality, contradicting the distinctness hypothesis.
  exact hne (Finset.Subset.antisymm hst hts)

/-- The blocker of a finite set family is itself a clutter on the same ground set. -/
theorem blocker_isClutterOn
    (E : Finset α) (S : Set (Finset α)) :
    IsClutterOn E (blocker E S) := by
  -- Members of the blocker inherit ground-set containment from their transversal witness.
  refine IsClutterOn.ofSubsetGroundAndAntichain ?_ (blockerAntichain E S)
  intro t ht
  exact (mem_blocker_iff.mp ht).prop.subset_ground

end Clutter

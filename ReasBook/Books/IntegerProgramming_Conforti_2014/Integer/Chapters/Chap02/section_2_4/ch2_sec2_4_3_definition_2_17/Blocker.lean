module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_15
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_16.Blocker

public section

namespace SetTransversal

open Clutter

/-- A pair of finite families `(S, T)` on `Fin n` is a blocking pair when `S` is a clutter and
`T` is exactly the blocker of `S`. -/
structure IsBlockingPair
    {n : ℕ}
    (S T : Finset (Finset (Fin n))) : Prop where
  /-- The family `S` is a clutter. -/
  left_isClutter : IsClutter S
  /-- The members of `T` are exactly the members of the blocker of `S`. -/
  mem_iff :
    ∀ U : Finset (Fin n),
      U ∈ T ↔ U ∈ blocker Finset.univ (S : Set (Finset (Fin n)))

namespace IsBlockingPair

/-- Build a blocking-pair witness from the characterization of the members of `T`. -/
def ofMemIff
    {n : ℕ} {S T : Finset (Finset (Fin n))}
    (hS : IsClutter S)
    (h_mem :
      ∀ U : Finset (Fin n),
        U ∈ T ↔ U ∈ blocker Finset.univ (S : Set (Finset (Fin n)))) :
    IsBlockingPair S T :=
  ⟨hS, h_mem⟩

/-- The left-hand family in a blocking pair is a clutter on the ground set `Finset.univ`. -/
theorem left_isClutterOn
    {n : ℕ} {S T : Finset (Finset (Fin n))}
    (hST : IsBlockingPair S T) :
    IsClutterOn Finset.univ (S : Set (Finset (Fin n))) :=
  hST.left_isClutter.toIsClutterOn

/-- The family `T` in a blocking pair is the blocker of `S` as a set family. -/
theorem blocker_eq
    {n : ℕ} {S T : Finset (Finset (Fin n))}
    (hST : IsBlockingPair S T) :
    (T : Set (Finset (Fin n))) = blocker Finset.univ (S : Set (Finset (Fin n))) := by
  ext U
  exact hST.mem_iff U

/-- Every member of the right-hand side of a blocking pair is a minimal transversal of `S`. -/
theorem mem_iff_minimal
    {n : ℕ} {S T : Finset (Finset (Fin n))}
    (hST : IsBlockingPair S T)
    (U : Finset (Fin n)) :
    U ∈ T ↔
      Minimal
        (fun V ↦ IsTransversal Finset.univ (S : Set (Finset (Fin n))) V)
        U := by
  rw [hST.mem_iff, mem_blocker_iff]

/-- The right-hand family in a blocking pair is again a clutter on the ground set `Finset.univ`. -/
theorem right_isClutterOn
    {n : ℕ} {S T : Finset (Finset (Fin n))}
    (hST : IsBlockingPair S T) :
    IsClutterOn Finset.univ (T : Set (Finset (Fin n))) := by
  simpa [hST.blocker_eq] using
    (blocker_isClutterOn Finset.univ (S : Set (Finset (Fin n))))

/-- The right-hand family in a blocking pair is again a clutter. -/
theorem right_isClutter
    {n : ℕ} {S T : Finset (Finset (Fin n))}
    (hST : IsBlockingPair S T) :
    IsClutter T :=
  (isClutter_iff_isClutterOn_univ T).2 hST.right_isClutterOn

end IsBlockingPair

/-- Unfolding specification for `IsBlockingPair`. -/
theorem isBlockingPair_iff
    {n : ℕ} {S T : Finset (Finset (Fin n))} :
    IsBlockingPair S T ↔
      IsClutter S ∧
      ∀ U : Finset (Fin n),
        U ∈ T ↔ U ∈ blocker Finset.univ (S : Set (Finset (Fin n))) := by
  constructor
  · intro hST
    exact ⟨hST.left_isClutter, hST.mem_iff⟩
  · rintro ⟨hS, h_mem⟩
    exact IsBlockingPair.ofMemIff hS h_mem

/-- A pair `(S, T)` is blocking exactly when `S` is a clutter and the members of `T` are precisely
the inclusionwise minimal transversals of `S`. -/
theorem isBlockingPair_iff_forall_mem
    {n : ℕ}
    {S T : Finset (Finset (Fin n))} :
    IsBlockingPair S T ↔
      IsClutter S ∧
      ∀ U : Finset (Fin n),
        U ∈ T ↔
          Minimal
            (fun V ↦ IsTransversal Finset.univ (S : Set (Finset (Fin n))) V)
            U := by
  constructor
  · intro hST
    exact ⟨hST.left_isClutter, hST.mem_iff_minimal⟩
  · rintro ⟨hS, h_mem⟩
    exact IsBlockingPair.ofMemIff hS (fun U ↦ by
      rw [h_mem U, mem_blocker_iff])

end SetTransversal

/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_5.ch5_sec5_2_5_theorem_5_19

-- Domain-style sampling for this refine pass:
-- * core/canonical owner: `GomoryLexicographicCuttingPlaneMethod`
-- * nearby bridge patterns inspected: Exercise 5.12 and Exercise 5.14
-- * source-facing owner kept here: `MixedIntegerGomoryLexicographicCuttingPlaneMethod`
-- * bridge/view layer added here: `toGomoryLexicographicCuttingPlaneMethod`

section Exercise513

/-- A mixed-integer lexicographic cutting-plane run records the full tableau iterate
`(x̄₀, x̄₁, …, x̄ₙ, ȳ₁, …, ȳᵣ)`, but only the objective-plus-integer prefix
`(x̄₀, x̄₁, …, x̄ₙ)` enters the stopping rule and the lexicographic descent argument. -/
structure MixedIntegerGomoryLexicographicCuttingPlaneMethod (n r : ℕ) where
  prefixFeasibleRegion : Set (Fin (n + 1) → ℝ)
  bounded_prefixFeasibleRegion : Bornology.IsBounded prefixFeasibleRegion
  iterates : ℕ → Fin (n + 1 + r) → ℝ
  iterates_prefix_mem_prefixFeasibleRegion :
    ∀ t : ℕ, (fun h : Fin (n + 1) ↦ iterates t (h.castAdd r)) ∈ prefixFeasibleRegion
  selectedRow : ℕ → Option (Fin (n + 1))
  selectedRow_none_iff :
    ∀ t : ℕ, selectedRow t = none ↔
      ∀ h : Fin (n + 1), iterates t (h.castAdd r) ∈ Set.range (Int.cast : ℤ → ℝ)
  lexicographically_nonincreasing :
    ∀ t : ℕ,
      toLex (fun h : Fin (n + 1) ↦ iterates (t + 1) (h.castAdd r)) ≤
        toLex (fun h : Fin (n + 1) ↦ iterates t (h.castAdd r))
  selectedRow_spec :
    ∀ ⦃t : ℕ⦄ ⦃h : Fin (n + 1)⦄, selectedRow t = some h →
      (∀ i : Fin (n + 1), i < h → iterates t (i.castAdd r) ∈ Set.range (Int.cast : ℤ → ℝ)) ∧
        iterates t (h.castAdd r) ∉ Set.range (Int.cast : ℤ → ℝ)
  strict_progress_on_fractional_step :
    ∀ ⦃t : ℕ⦄ ⦃h : Fin (n + 1)⦄, selectedRow t = some h →
      toLex (fun i : Fin (n + 1) ↦ iterates (t + 1) (i.castAdd r)) <
        toLex (fun i : Fin (n + 1) ↦ iterates t (i.castAdd r))
  selectedRow_eventually_forces_floor :
    ∀ ⦃t : ℕ⦄ ⦃h : Fin (n + 1)⦄,
      selectedRow t = some h →
      ∀ {m : ℤ},
      iterates t (h.castAdd r) < (m : ℝ) + 1 →
      (∀ i : Fin (n + 1), i < h →
        ∃ z : ℤ, ∀ s ≥ t + 1, iterates s (i.castAdd r) = (z : ℝ)) →
      ∀ s ≥ t + 1, iterates s (h.castAdd r) ≤ (m : ℝ)

namespace MixedIntegerGomoryLexicographicCuttingPlaneMethod

/-- The objective-plus-integer prefix `(x̄₀, x̄₁, …, x̄ₙ)` tracked by the mixed-integer
lexicographic method. -/
def objectiveIntegerPrefix
    {n r : ℕ} (A : MixedIntegerGomoryLexicographicCuttingPlaneMethod n r) (t : ℕ) :
    Fin (n + 1) → ℝ :=
  fun h ↦ A.iterates t (h.castAdd r)

/-- The mixed-integer run stops at stage `t` when no fractional objective-or-integer row remains in
the tracked prefix. -/
def StopsAt
    {n r : ℕ} (A : MixedIntegerGomoryLexicographicCuttingPlaneMethod n r) (t : ℕ) : Prop :=
  A.selectedRow t = none

/-- A mixed-integer run stops exactly when its tracked objective-plus-integer prefix is integral
in every coordinate. -/
@[simp] theorem stopsAt_iff
    {n r : ℕ} (A : MixedIntegerGomoryLexicographicCuttingPlaneMethod n r) (t : ℕ) :
    A.StopsAt t ↔
      ∀ h : Fin (n + 1), A.objectiveIntegerPrefix t h ∈ Set.range (Int.cast : ℤ → ℝ) :=
  A.selectedRow_none_iff t

/-- Forgetting the continuous coordinates yields the canonical Chapter 5 lexicographic owner on the
objective-plus-integer prefix. -/
def toGomoryLexicographicCuttingPlaneMethod
    {n r : ℕ} (A : MixedIntegerGomoryLexicographicCuttingPlaneMethod n r)
    (relaxation : ℕ → Set (Fin n → ℝ))
    (iterates_mem_relaxation :
      ∀ t : ℕ, (fun j ↦ A.objectiveIntegerPrefix t j.succ) ∈ relaxation t)
    (cutColumns : ℕ → Finset (Fin n))
    (cutCoeff : ℕ → Fin n → ℚ)
    (cutRhs : ℕ → ℚ)
    (relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃h : Fin (n + 1)⦄, A.selectedRow t = some h →
        relaxation (t + 1) =
          relaxation t ∩ gomory_fractional_cut (cutColumns t) (cutCoeff t) (cutRhs t)) :
    GomoryLexicographicCuttingPlaneMethod n where
  feasibleRegion := A.prefixFeasibleRegion
  bounded_feasibleRegion := A.bounded_prefixFeasibleRegion
  relaxation := relaxation
  iterates := A.objectiveIntegerPrefix
  iterates_mem_feasibleRegion := A.iterates_prefix_mem_prefixFeasibleRegion
  iterates_mem_relaxation := iterates_mem_relaxation
  selectedRow := A.selectedRow
  selectedRow_none_iff := A.selectedRow_none_iff
  cutColumns := cutColumns
  cutCoeff := cutCoeff
  cutRhs := cutRhs
  relaxation_step := relaxation_step
  lexicographically_nonincreasing := A.lexicographically_nonincreasing
  selectedRow_spec := A.selectedRow_spec
  strict_progress_on_fractional_step := A.strict_progress_on_fractional_step
  selectedRow_eventually_forces_floor := A.selectedRow_eventually_forces_floor

@[simp] theorem toGomoryLexicographicCuttingPlaneMethod_iterates
    {n r : ℕ} (A : MixedIntegerGomoryLexicographicCuttingPlaneMethod n r)
    (relaxation : ℕ → Set (Fin n → ℝ))
    (iterates_mem_relaxation :
      ∀ t : ℕ, (fun j ↦ A.objectiveIntegerPrefix t j.succ) ∈ relaxation t)
    (cutColumns : ℕ → Finset (Fin n))
    (cutCoeff : ℕ → Fin n → ℚ)
    (cutRhs : ℕ → ℚ)
    (relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃h : Fin (n + 1)⦄, A.selectedRow t = some h →
        relaxation (t + 1) =
          relaxation t ∩ gomory_fractional_cut (cutColumns t) (cutCoeff t) (cutRhs t))
    (t : ℕ) :
    (A.toGomoryLexicographicCuttingPlaneMethod relaxation iterates_mem_relaxation
      cutColumns cutCoeff cutRhs relaxation_step).iterates t =
      A.objectiveIntegerPrefix t :=
  rfl

@[simp] theorem toGomoryLexicographicCuttingPlaneMethod_selectedRow
    {n r : ℕ} (A : MixedIntegerGomoryLexicographicCuttingPlaneMethod n r)
    (relaxation : ℕ → Set (Fin n → ℝ))
    (iterates_mem_relaxation :
      ∀ t : ℕ, (fun j ↦ A.objectiveIntegerPrefix t j.succ) ∈ relaxation t)
    (cutColumns : ℕ → Finset (Fin n))
    (cutCoeff : ℕ → Fin n → ℚ)
    (cutRhs : ℕ → ℚ)
    (relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃h : Fin (n + 1)⦄, A.selectedRow t = some h →
        relaxation (t + 1) =
          relaxation t ∩ gomory_fractional_cut (cutColumns t) (cutCoeff t) (cutRhs t))
    (t : ℕ) :
    (A.toGomoryLexicographicCuttingPlaneMethod relaxation iterates_mem_relaxation
      cutColumns cutCoeff cutRhs relaxation_step).selectedRow t =
      A.selectedRow t :=
  rfl

@[simp] theorem toGomoryLexicographicCuttingPlaneMethod_stopsAt_iff
    {n r : ℕ} (A : MixedIntegerGomoryLexicographicCuttingPlaneMethod n r)
    (relaxation : ℕ → Set (Fin n → ℝ))
    (iterates_mem_relaxation :
      ∀ t : ℕ, (fun j ↦ A.objectiveIntegerPrefix t j.succ) ∈ relaxation t)
    (cutColumns : ℕ → Finset (Fin n))
    (cutCoeff : ℕ → Fin n → ℚ)
    (cutRhs : ℕ → ℚ)
    (relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃h : Fin (n + 1)⦄, A.selectedRow t = some h →
        relaxation (t + 1) =
          relaxation t ∩ gomory_fractional_cut (cutColumns t) (cutCoeff t) (cutRhs t))
    (t : ℕ) :
    (A.toGomoryLexicographicCuttingPlaneMethod relaxation iterates_mem_relaxation
      cutColumns cutCoeff cutRhs relaxation_step).StopsAt t ↔
      A.StopsAt t :=
  Iff.rfl

end MixedIntegerGomoryLexicographicCuttingPlaneMethod

/-- Exercise 5.13. The mixed-integer lexicographic cutting-plane method terminates in finitely
many iterations whenever its tracked objective-plus-integer prefix is equipped with the auxiliary
relaxation, cut, and finiteness data needed to invoke the canonical Chapter 5 lexicographic
owner. -/
theorem mixed_integer_gomory_lexicographic_cutting_plane_method_terminates
    {n r : ℕ} (A : MixedIntegerGomoryLexicographicCuttingPlaneMethod n r)
    (relaxation : ℕ → Set (Fin n → ℝ))
    (iterates_mem_relaxation :
      ∀ t : ℕ, (fun j ↦ A.objectiveIntegerPrefix t j.succ) ∈ relaxation t)
    (cutColumns : ℕ → Finset (Fin n))
    (cutCoeff : ℕ → Fin n → ℚ)
    (cutRhs : ℕ → ℚ)
    (relaxation_step :
      ∀ ⦃t : ℕ⦄ ⦃h : Fin (n + 1)⦄, A.selectedRow t = some h →
        relaxation (t + 1) =
          relaxation t ∩ gomory_fractional_cut (cutColumns t) (cutCoeff t) (cutRhs t)) :
    ∃ T : ℕ, A.StopsAt T := by
  -- Route correction: reuse the canonical Chapter 5 termination theorem through the mixed-prefix
  -- bridge instead of replaying the stabilization argument in this file.
  obtain ⟨T, hT⟩ :=
    gomory_lexicographic_cutting_plane_method_terminates
      (A.toGomoryLexicographicCuttingPlaneMethod relaxation iterates_mem_relaxation
        cutColumns cutCoeff cutRhs relaxation_step)
  -- Rewrite the bridged stopping predicate back to the mixed owner.
  refine ⟨T, ?_⟩
  simpa using hT

end Exercise513

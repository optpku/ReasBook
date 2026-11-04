/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_3.ch9_sec9_3_proposition_9_13

open Set

section Proposition915

universe u

variable {α : Type u}

-- Semantic recall: mathlib's canonical orbit owner is `MulAction.orbit`, but Proposition 9.15
-- is phrased over the source orbit family `𝒪_a`, so this file keeps that family explicit instead
-- of identifying it with a stronger stabilizer-based orbit partition.

/-- `hasOrbitMeetingFixedZero orbitFamily node x` means that some orbit `O ∈ 𝒪_a` attached to
`node` meets the variables fixed to `0` at `node` and also contains a coordinate where the binary
solution `x` takes the value `1`. -/
def hasOrbitMeetingFixedZero
    (orbitFamily : Set (Set α))
    (node : EnumerationNode α)
    (x : α → Bool) : Prop :=
  ∃ O ∈ orbitFamily, (O ∩ node.fixedZero).Nonempty ∧ ∃ i ∈ O, x i = true

/-- Helper for Proposition 9.15: `x` is represented by an isomorphic solution contained in some
node lying to the left of `node`. -/
def hasLeftNodeIsomorphicSolution
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (node : EnumerationNode α)
    (x : α → Bool) : Prop :=
  ∃ nodeLeft, leftOf nodeLeft node ∧
    ∃ y ∈ nodeLeft.solutions, solutions_are_isomorphic Γ x y

/-- Helper for Proposition 9.15: the Chapter 9.3 orbital-fixing rule sends any feasible solution
meeting a fixed-zero orbit to the left-node witness used in the proposition. -/
def orbitalFixingWitnessesLeftNodeIsomorphicSolution
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (orbitFamily : Set (Set α))
    (node : EnumerationNode α) : Prop :=
  ∀ ⦃x O i⦄, x ∈ node.solutions → O ∈ orbitFamily →
    (O ∩ node.fixedZero).Nonempty → i ∈ O → x i = true →
      hasLeftNodeIsomorphicSolution Γ leftOf node x

/-- Proposition 9.15. Consider a node `N_a` of the enumeration tree. If `x̄` is a solution in
node `N_a` such that there exists an orbit `O ∈ 𝒪_a` satisfying `O ∩ F_a^0 ≠ ∅`, with an index
`i ∈ O` for which `x̄ i = 1`, then there exists a node `N_b` to the left of `N_a` containing a
solution isomorphic to `x̄`. In Lean, the ambient Chapter 9.3 orbital-fixing branch rule is made
explicit by `hOrbitalFixing`. -/
theorem left_node_contains_isomorphic_solution_of_orbit_meeting_fixed_zero
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (orbitFamily : Set (Set α))
    (node : EnumerationNode α)
    (hOrbitalFixing :
      orbitalFixingWitnessesLeftNodeIsomorphicSolution Γ leftOf orbitFamily node)
    (x : α → Bool)
    (hx : x ∈ node.solutions)
    (hOrbit : hasOrbitMeetingFixedZero orbitFamily node x) :
    hasLeftNodeIsomorphicSolution Γ leftOf node x := by
  -- Unpack the orbit witness into the exact arguments required by the orbital-fixing rule.
  rcases hOrbit with ⟨O, hO, hMeet, i, hi, hxi⟩
  -- The branch rule already returns the textbook left-node witness.
  exact hOrbitalFixing hx hO hMeet hi hxi

/-- Canonical Chapter 9.13 solution-set reformulation of Proposition 9.15 for the actual
enumeration-tree left-of relation and source orbit family `𝒪_a`, with the Chapter 9.3
orbital-fixing branch rule made explicit as `hOrbitalFixing`: if a feasible solution `x̄` at node
`N_a` has a `1` in some orbit `O ∈ 𝒪_a` that also meets `F_a^0`, then `x̄` already lies in the
left-isomorphic solution set of `N_a`. -/
theorem mem_left_isomorphic_solution_set_of_orbit_meeting_fixed_zero
    (Γ : Subgroup (Equiv.Perm α))
    (leftOf : EnumerationNode α → EnumerationNode α → Prop)
    (orbitFamily : Set (Set α))
    (node : EnumerationNode α)
    (hOrbitalFixing :
      orbitalFixingWitnessesLeftNodeIsomorphicSolution Γ leftOf orbitFamily node)
    (x : α → Bool)
    (hx : x ∈ node.solutions)
    (hOrbit : hasOrbitMeetingFixedZero orbitFamily node x) :
    x ∈ left_isomorphic_solution_set Γ leftOf node := by
  -- Route correction: first use Proposition 9.15's explicit existential witness, then package it.
  have hLeft :
      hasLeftNodeIsomorphicSolution Γ leftOf node x :=
    left_node_contains_isomorphic_solution_of_orbit_meeting_fixed_zero
      Γ leftOf orbitFamily node hOrbitalFixing x hx hOrbit
  -- Repackage the left-node witness as membership in the canonical left-isomorphic solution set.
  rcases hLeft with ⟨nodeLeft, hleft, y, hy, hiso⟩
  exact (mem_left_isomorphic_solution_set_iff Γ leftOf node x).2
    ⟨nodeLeft, hleft, y, hy, hiso⟩

end Proposition915

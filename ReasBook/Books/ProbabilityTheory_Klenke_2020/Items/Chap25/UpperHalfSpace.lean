/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open Topology
open scoped Topology

noncomputable section

namespace ProbabilityTheory

section HalfSpace

variable (n : ℕ)

local notation "State" => EuclideanSpace ℝ (Fin (n + 1))
local notation "Boundary" => EuclideanSpace ℝ (Fin n)

/-- The open upper half-space `ℝ^n × (0, ∞)` inside `ℝ^(n+1)`, with the last coordinate as the
vertical variable. -/
def upperHalfSpace : Set State :=
  {x | 0 < x (Fin.last n)}

/-- Membership in `upperHalfSpace n` is positivity of the last coordinate. -/
@[simp] theorem mem_upperHalfSpace_iff (x : State) :
    x ∈ upperHalfSpace n ↔ 0 < x (Fin.last n) :=
  Iff.rfl

/-- The boundary projection `ℝ^(n+1) → ℝ^n` forgetting the vertical coordinate. -/
def upperHalfSpaceBoundaryProjection (x : State) : Boundary :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦ x (Fin.castSucc i)

/-- Evaluating the boundary projection forgets the last coordinate. -/
theorem upperHalfSpaceBoundaryProjection_apply (x : State) (i : Fin n) :
    upperHalfSpaceBoundaryProjection n x i = x (Fin.castSucc i) := by
  simp [upperHalfSpaceBoundaryProjection]

attribute [simp] upperHalfSpaceBoundaryProjection_apply

/-- The frontier of the upper half-space consists exactly of points whose last coordinate
vanishes. -/
theorem mem_frontier_upperHalfSpace_iff (x : State) :
    x ∈ frontier (upperHalfSpace n) ↔ x (Fin.last n) = 0 := by
  let π : State →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last n)
  have hπ : Function.Surjective π := by
    intro r
    refine ⟨(EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm <|
      Fin.snoc (fun _ : Fin n ↦ (0 : ℝ)) r, ?_⟩
    simp [π]
  have hset : upperHalfSpace n = π ⁻¹' Set.Ioi (0 : ℝ) := by
    ext z
    simp [upperHalfSpace, π]
  have hfrontier :
      frontier (upperHalfSpace n) = {z : State | z (Fin.last n) = 0} := by
    calc
      frontier (upperHalfSpace n)
          = frontier (π ⁻¹' Set.Ioi (0 : ℝ)) := by rw [hset]
      _ = π ⁻¹' frontier (Set.Ioi (0 : ℝ)) := π.frontier_preimage hπ (Set.Ioi (0 : ℝ))
      _ = {z : State | z (Fin.last n) = 0} := by
            ext z
            simp [π]
  simp [hfrontier]

/-- The canonical identification `∂(ℝ^n × (0, ∞)) ≃ ℝ^n` forgetting the vertical coordinate. -/
noncomputable def upperHalfSpaceFrontierEquiv :
    frontier (upperHalfSpace n) ≃ Boundary where
  toFun x := (EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦ x.1 (Fin.castSucc i)
  invFun y :=
    ⟨(EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm <|
        Fin.snoc ((EuclideanSpace.equiv (Fin n) ℝ) y) 0, by
      rw [mem_frontier_upperHalfSpace_iff]
      simp⟩
  left_inv x := by
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp
    · simpa using
        ((mem_frontier_upperHalfSpace_iff n x.1).mp x.2).symm
  right_inv y := by
    ext i
    simp

end HalfSpace

end ProbabilityTheory

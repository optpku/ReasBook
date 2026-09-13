/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.Analysis.SetValuedOperator
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.DualPairing.Monotone

/-!
# Normal cones for continuous dual pairings

This module defines normal-cone operators and proves their domain, interior,
and monotonicity properties.
-/

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/-- The normal-cone set-valued operator determined by a dual pairing and a set. -/
def normalCone (P : DualPairing X Xstar) (C : Set X) : SetValuedOperator X Xstar :=
  fun x ↦ {xstar | x ∈ C ∧ ∀ y ∈ C, P.toLinearPairing (y - x) xstar ≤ 0}

/-- Membership in a normal-cone value is the defining variational inequality. -/
@[simp]
lemma mem_normalCone (P : DualPairing X Xstar) (C : Set X) (x : X) (xstar : Xstar) :
    xstar ∈ P.normalCone C x ↔
      x ∈ C ∧ ∀ y ∈ C, P.toLinearPairing (y - x) xstar ≤ 0 := by
  -- Unfolding the value exposes exactly the defining variational inequality.
  rfl

/-- The graph of a normal-cone set-valued operator. -/
def normalConeGraph (P : DualPairing X Xstar) (C : Set X) : SetRel X Xstar :=
  (P.normalCone C).graph

/-- Membership in the graph of a normal cone is the defining variational inequality. -/
@[simp]
lemma mem_graph_normalCone (P : DualPairing X Xstar) (C : Set X) (x : X)
    (xstar : Xstar) :
    (x, xstar) ∈ P.normalConeGraph C ↔
      x ∈ C ∧ ∀ y ∈ C, P.toLinearPairing (y - x) xstar ≤ 0 := by
  -- Graph membership reduces to membership in the corresponding operator value.
  simp [normalConeGraph, SetValuedOperator.mem_graph, mem_normalCone]

/-- The domain of a normal-cone set-valued operator. -/
def normalConeDom (P : DualPairing X Xstar) (C : Set X) : Set X :=
  (P.normalCone C).dom

/-- The domain of the normal-cone operator of a set is exactly that set. -/
@[simp]
theorem dom_normalCone (P : DualPairing X Xstar) (C : Set X) :
    P.normalConeDom C = C := by
  -- Compare the domain and the defining set pointwise.
  ext x
  constructor
  · intro hx
    -- Any value in the normal cone carries the base-point membership in `C`.
    exact (SetValuedOperator.mem_dom (P.normalCone C) x).1 hx |>.choose_spec |>.1
  · intro hx
    -- At a point of `C`, the zero dual vector satisfies every defining inequality.
    change x ∈ (P.normalCone C).dom
    rw [SetValuedOperator.mem_dom]
    refine ⟨0, hx, ?_⟩
    intro y hy
    simp [DualPairing.toLinearPairing_apply]

/-- Domain membership for a normal-cone operator reduces to membership in its set. -/
@[simp]
lemma mem_dom_normalCone (P : DualPairing X Xstar) (C : Set X) (x : X) :
    x ∈ P.normalConeDom C ↔ x ∈ C := by
  -- The set equality immediately gives its pointwise membership form.
  rw [dom_normalCone]

/-- A normal vector at an interior point induces the zero continuous functional for
`DualPairing.normalCone_eq_zero_of_mem_interior`. -/
private lemma toDual_eq_zero_of_mem_normalCone_of_mem_interior
    (P : DualPairing X Xstar) {C : Set X} {x : X} {xstar : Xstar}
    (hx : x ∈ interior C) (hxstar : xstar ∈ P.normalCone C x) : P.toDual xstar = 0 := by
  -- Fix a symmetric ball about the interior point that remains inside the set.
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  apply ContinuousLinearMap.ext
  intro y
  by_cases hy : y = 0
  · simp [hy]
  · -- Scale a nonzero direction so that both signed perturbations lie in the ball.
    let t : ℝ := ε / (2 * ‖y‖)
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have hty : ‖t • y‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      dsimp [t]
      field_simp
      nlinarith [norm_pos_iff.mpr hy]
    have hplus : x + t • y ∈ C := by
      apply hball
      simpa [dist_eq_norm] using hty
    have hminus : x - t • y ∈ C := by
      apply hball
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, norm_neg] using hty
    -- Test the normal inequality at both perturbations to bound the pairing both ways.
    have hnormal := (P.mem_normalCone C x xstar).1 hxstar
    have hplus_eval : t * P.toDual xstar y ≤ 0 := by
      simpa [P.toLinearPairing_apply, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc, map_add, map_smul, smul_eq_mul] using hnormal.2 (x + t • y) hplus
    have hminus_eval : -t * P.toDual xstar y ≤ 0 := by
      simpa [P.toLinearPairing_apply, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc, map_add, map_smul, smul_eq_mul] using hnormal.2 (x - t • y) hminus
    have hposval : 0 ≤ P.toDual xstar y := by
      nlinarith [hminus_eval]
    have hnegval : P.toDual xstar y ≤ 0 := by
      nlinarith [hplus_eval]
    exact le_antisymm hnegval hposval

/-- The normal cone of a set at an interior point is the singleton containing zero. -/
theorem normalCone_eq_zero_of_mem_interior (P : DualPairing X Xstar) {C : Set X} {x : X}
    (hx : x ∈ interior C) : P.normalCone C x = {0} := by
  -- Compare membership pointwise, using nondegeneracy for the nontrivial inclusion.
  ext xstar
  constructor
  · intro h
    have hzero := toDual_eq_zero_of_mem_normalCone_of_mem_interior P hx h
    apply P.injective_toDual
    simpa using hzero
  · intro h
    -- Zero satisfies every normal inequality once the base point is known to lie in `C`.
    have hxstar : xstar = 0 := by simpa using h
    subst hxstar
    apply (P.mem_normalCone C x 0).2
    constructor
    · exact interior_subset hx
    · intro y hy
      simp

/-- The graph of the normal-cone operator of any set is monotone. -/
theorem isMonotone_normalConeGraph (P : DualPairing X Xstar) (C : Set X) :
    P.IsMonotone (P.normalConeGraph C) := by
  -- Use the polar characterization and fix two arbitrary points of the graph.
  apply (DualPairing.isMonotone_iff_subset_polar P (P.normalConeGraph C)).2
  intro z hz
  rw [DualPairing.mem_monotonePolar]
  intro w hw
  rcases z with ⟨x, xstar⟩
  rcases w with ⟨y, ystar⟩
  have hz' := (P.mem_graph_normalCone C x xstar).1 hz
  have hw' := (P.mem_graph_normalCone C y ystar).1 hw
  -- Normalize the product difference before expanding the quadratic pairing.
  have hsub : (x, xstar) - (y, ystar) = (x - y, xstar - ystar) := by
    rfl
  rw [hsub, P.quadratic_apply]
  -- Cross-test each defining inequality at the other graph point, then add them.
  have hxy := hz'.2 y hw'.1
  have hyx := hw'.2 x hz'.1
  rw [P.toLinearPairing_apply] at hxy hyx
  simp only [map_sub]
  rw [sub_apply, sub_apply]
  simp only [map_sub] at hxy hyx
  linarith

end DualPairing

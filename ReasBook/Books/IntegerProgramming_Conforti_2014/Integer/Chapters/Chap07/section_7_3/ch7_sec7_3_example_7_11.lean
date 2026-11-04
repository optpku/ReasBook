/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9

open scoped BigOperators

section Example711

variable {m n : ℕ}

/-- The feasible-set constraints of the facility location formulation used in this section. -/
def facility_location_feasible
    (d : Fin m → ℝ) (u : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → Fin n → ℝ) : Prop :=
  (∀ i, ∑ j, y i j = d i) ∧
    (∀ j, ∑ i, y i j ≤ u j * x j) ∧
      (∀ i j, 0 ≤ y i j) ∧
        ∀ j, x j = 0 ∨ x j = 1

/-- A definitional expansion of `facility_location_feasible`. -/
theorem facility_location_feasible_iff
    (d : Fin m → ℝ) (u : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → Fin n → ℝ) :
    facility_location_feasible d u x y ↔
      (∀ i, ∑ j, y i j = d i) ∧
        (∀ j, ∑ i, y i j ≤ u j * x j) ∧
          (∀ i j, 0 ≤ y i j) ∧
            ∀ j, x j = 0 ∨ x j = 1 :=
  Iff.rfl

/-- The aggregated facility load `z_j = ∑_i y_{ij}` attached to a shipment matrix. -/
def facility_location_projection (y : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  ∑ i, y i

/-- The pointwise formula for `facility_location_projection`. -/
theorem facility_location_projection_apply
    (y : Fin m → Fin n → ℝ) (j : Fin n) :
    facility_location_projection y j = ∑ i, y i j := by
  simp [facility_location_projection]

/-- Example 7.11. If `(x,y)` is feasible for the facility location formulation and
`z_j = ∑_i y_{ij}`, then `(x,z)` belongs to the associated single-node flow set with
right-hand side `∑_i d_i`. -/
theorem example_7_11_facility_location_projection_single_node_flow
    (d : Fin m → ℝ) (u : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → Fin n → ℝ)
    (hfeas : facility_location_feasible d u x y) :
    (x, facility_location_projection y) ∈ single_node_flow_set u (∑ i, d i) := by
  rw [mem_single_node_flow_set_iff]
  rcases hfeas with ⟨hd, hu, hy_nonneg, hx_binary⟩
  refine ⟨hx_binary, ?_, ?_, ?_⟩
  · intro j
    simpa [facility_location_projection] using
      (Finset.sum_nonneg fun i _ ↦ hy_nonneg i j : 0 ≤ ∑ i, y i j)
  · calc
      ∑ j, facility_location_projection y j
        = ∑ j, ∑ i, y i j := by simp [facility_location_projection]
      _ = ∑ i, ∑ j, y i j := by rw [Finset.sum_comm]
      _ = ∑ i, d i := by simp [hd]
      _ ≤ ∑ i, d i := le_rfl
  · intro j
    simpa [facility_location_projection] using hu j

end Example711

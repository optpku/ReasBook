/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

noncomputable section

section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

-- Primary domain: nearest-point projections onto complete convex sets in real inner product
-- spaces.
-- Owner sampling:
-- * `exists_norm_eq_iInf_of_complete_convex` in mathlib supplies the primitive existence theorem.
-- * `norm_eq_iInf_iff_real_inner_le_zero` in mathlib is the canonical minimizer characterization.
-- * Chapter 1 already establishes uniqueness for this same minimizer notion, so the public owner
--   here keeps only the primitive data `X`, `X.Nonempty`, `IsComplete X`, and `Convex ℝ X`.
-- Membership and distance-minimizing properties are derived API.

/-- Chapter11 Definition 11.5-extra-1: the nearest-point projection map
`x ↦ P(x) = arg min {‖z - x‖ | z ∈ X}` on a nonempty complete convex set `X`. -/
def nearestPointProjection
    (X : Set F) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) :
    F → F :=
  fun x ↦
    Classical.choose <|
      exists_norm_eq_iInf_of_complete_convex hX_nonempty hX_complete hX_convex x

/-- The value `nearestPointProjection X hX_nonempty hX_complete hX_convex x` belongs to `X`. -/
@[simp] theorem nearestPointProjection_mem
    (X : Set F) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (x : F) :
    nearestPointProjection X hX_nonempty hX_complete hX_convex x ∈ X := by
  simpa [nearestPointProjection] using
    (Classical.choose_spec <|
      exists_norm_eq_iInf_of_complete_convex hX_nonempty hX_complete hX_convex x).1

/-- The value `nearestPointProjection X hX_nonempty hX_complete hX_convex x` attains the source
distance minimum over `X`. -/
theorem norm_sub_nearestPointProjection_eq_iInf
    (X : Set F) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (x : F) :
    ‖x - nearestPointProjection X hX_nonempty hX_complete hX_convex x‖ =
      ⨅ z : X, ‖x - z‖ := by
  simpa [nearestPointProjection] using
    (Classical.choose_spec <|
      exists_norm_eq_iInf_of_complete_convex hX_nonempty hX_complete hX_convex x).2

/-- Unfolding `nearestPointProjection X hX_nonempty hX_complete hX_convex x` gives a point of
`X` that attains the source distance minimum. -/
theorem nearestPointProjection_spec
    (X : Set F) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (x : F) :
    nearestPointProjection X hX_nonempty hX_complete hX_convex x ∈ X ∧
      ‖x - nearestPointProjection X hX_nonempty hX_complete hX_convex x‖ =
        ⨅ z : X, ‖x - z‖ := by
  exact ⟨
    nearestPointProjection_mem X hX_nonempty hX_complete hX_convex x,
    norm_sub_nearestPointProjection_eq_iInf X hX_nonempty hX_complete hX_convex x
  ⟩

/-- The nearest-point projection satisfies the canonical convex-set characterization:
for every `z ∈ X`, the displacement from `x` to its projection has nonpositive real inner product
with the displacement from the projection to `z`. -/
theorem real_inner_sub_nearestPointProjection_le_zero
    (X : Set F) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (x z : F) (hz : z ∈ X) :
    inner ℝ
        (x - nearestPointProjection X hX_nonempty hX_complete hX_convex x)
        (z - nearestPointProjection X hX_nonempty hX_complete hX_convex x) ≤ 0 := by
  exact
    (norm_eq_iInf_iff_real_inner_le_zero
      hX_convex
      (nearestPointProjection_mem X hX_nonempty hX_complete hX_convex x)).1
      (norm_sub_nearestPointProjection_eq_iInf X hX_nonempty hX_complete hX_convex x)
      z
      hz

/-- A point of `X` is fixed by the nearest-point projection onto `X`. -/
@[simp] theorem nearestPointProjection_eq_self
    (X : Set F) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) {x : F} (hx : x ∈ X) :
    nearestPointProjection X hX_nonempty hX_complete hX_convex x = x := by
  let projection := nearestPointProjection X hX_nonempty hX_complete hX_convex x
  have hinner_le :
      inner ℝ (x - projection) (x - projection) ≤ 0 := by
    simpa [projection] using
      real_inner_sub_nearestPointProjection_le_zero
        X hX_nonempty hX_complete hX_convex x x hx
  have hinner_nonneg :
      0 ≤ inner ℝ (x - projection) (x - projection) := by
    exact real_inner_self_nonneg
  have hsub_eq_zero : x - projection = 0 := by
    exact inner_self_eq_zero.mp <| le_antisymm hinner_le hinner_nonneg
  have hx_eq_projection : x = projection := sub_eq_zero.mp hsub_eq_zero
  exact hx_eq_projection.symm

/-- A point is fixed by the nearest-point projection onto `X` exactly when it belongs to `X`. -/
@[simp] theorem nearestPointProjection_eq_self_iff
    (X : Set F) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) {x : F} :
    nearestPointProjection X hX_nonempty hX_complete hX_convex x = x ↔ x ∈ X := by
  constructor
  · intro hx
    rw [← hx]
    exact nearestPointProjection_mem X hX_nonempty hX_complete hX_convex x
  · intro hx
    exact nearestPointProjection_eq_self X hX_nonempty hX_complete hX_convex hx

/-- The nearest-point projection depends only on the set `X`, not on the particular proof terms
used to witness nonemptiness, completeness, and convexity. -/
theorem nearestPointProjection_congr
    (X : Set F) (hX_nonempty : X.Nonempty) (hX_complete : IsComplete X)
    (hX_convex : Convex ℝ X) (hX_nonempty' : X.Nonempty) (hX_complete' : IsComplete X)
    (hX_convex' : Convex ℝ X) (x : F) :
    nearestPointProjection X hX_nonempty hX_complete hX_convex x =
      nearestPointProjection X hX_nonempty' hX_complete' hX_convex' x := by
  have hh_nonempty : hX_nonempty = hX_nonempty' := Subsingleton.elim _ _
  have hh_complete : hX_complete = hX_complete' := Subsingleton.elim _ _
  have hh_convex : hX_convex = hX_convex' := Subsingleton.elim _ _
  cases hh_nonempty
  cases hh_complete
  cases hh_convex
  rfl

#print axioms nearestPointProjection

end

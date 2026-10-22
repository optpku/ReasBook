/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_19.EuclideanQuadrant
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_6.Projection
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8.FeasibleSet

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}

/-- The nonnegative-orthant feasible set for `(9.16)` is nonempty. -/
theorem feasibleSet_nonempty (n : ℕ) :
    (feasibleSet n).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_feasibleSet]
  intro i
  exact le_rfl

/-- The nonnegative-orthant feasible set for `(9.16)` is closed and convex. -/
theorem closedConvex_feasibleSet (n : ℕ) :
    Set.ClosedConvex (feasibleSet n) := by
  have hset : feasibleSet n = {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} := by
    ext x
    rw [mem_feasibleSet]
    rfl
  rw [Set.closedConvex_iff]
  rw [hset]
  constructor
  · exact EuclideanQuadrant.isClosed_nonnegativeOrthant n
  · simpa using
      (EuclideanQuadrant.convex :
        Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i})

/-- The orthant projector for `(9.16)` is the Euclidean projection onto
`feasibleSet n`. -/
def projector (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  EuclideanProjection.proj (feasibleSet n) (feasibleSet_nonempty n)
    (closedConvex_feasibleSet n)

/-- The orthant projector maps every point into the feasible set of `(9.16)`. -/
theorem projector_mem_feasibleSet
    (n : ℕ) (f : EuclideanSpace ℝ (Fin n)) :
    projector n f ∈ feasibleSet n := by
  simpa [projector] using
    EuclideanProjection.proj_mem
      (feasibleSet n)
      (feasibleSet_nonempty n)
      (closedConvex_feasibleSet n)
      f

/-- The orthant projector is the reusable Euclidean projection onto `feasibleSet n`. -/
theorem projector_eq_proj
    (n : ℕ) (f : EuclideanSpace ℝ (Fin n)) :
    projector n f =
      EuclideanProjection.proj (feasibleSet n) (feasibleSet_nonempty n)
        (closedConvex_feasibleSet n) f := by
  rfl

/-- A feasible point of `(9.16)` is fixed by the orthant projector. -/
theorem projector_eq_self_of_mem
    (n : ℕ) {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ feasibleSet n) :
    projector n f = f := by
  simpa [projector] using
    EuclideanProjection.proj_eq_self_of_mem
      (feasibleSet n)
      (feasibleSet_nonempty n)
      (closedConvex_feasibleSet n)
      hf

end NonnegativeOrthant

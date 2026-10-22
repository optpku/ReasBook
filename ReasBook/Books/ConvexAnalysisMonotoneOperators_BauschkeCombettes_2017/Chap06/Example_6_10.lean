/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_4

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Helper for Example 6.10: a nonempty convex set symmetric about the origin contains `0`. -/
lemma zero_mem_of_nonempty_convex_eq_neg {C : Set E} (hC_nonempty : C.Nonempty)
    (hC_convex : Convex ℝ C) (hC_symmetric : C = -C) :
    (0 : E) ∈ C := by
  rcases hC_nonempty with ⟨y, hy⟩
  -- Symmetry turns a witness `y ∈ C` into the opposite point `-y ∈ C`.
  have hy_neg : -y ∈ C := by
    rw [hC_symmetric, Set.mem_neg]
    simpa using hy
  -- Convexity keeps the midpoint of `y` and `-y`, which is exactly the origin.
  have hmid : midpoint ℝ y (-y) ∈ C := hC_convex.midpoint_mem hy hy_neg
  simpa using hmid

omit [Module ℝ E] in
/-- Helper for Example 6.10: subtracting the singleton `{0}` leaves the set unchanged. -/
lemma sub_singleton_zero_eq_self {C : Set E} :
    C - ({(0 : E)} : Set E) = C := by
  ext x
  constructor
  · intro hx
    -- Any representation `x = u - v` with `v ∈ {0}` reduces to `x = u`.
    rcases Set.mem_sub.mp hx with ⟨u, hu, v, hv, huv⟩
    have hv0 : v = 0 := by
      simpa using hv
    have hux : u = x := by
      simpa [hv0] using huv
    simpa [← hux] using hu
  · intro hx
    -- Conversely, realize `x` as `x - 0`.
    exact Set.mem_sub.mpr ⟨x, hx, 0, by simp, by simp⟩

/-- Helper for Example 6.10: the cone hull of a convex set agrees with `Convex.toCone`. -/
lemma convexCone_hull_eq_toCone {C : Set E} (hC_convex : Convex ℝ C) :
    (ConvexCone.hull ℝ C : Set E) = ((hC_convex.toCone C : ConvexCone ℝ E) : Set E) := by
  simpa [ConvexCone.hull] using
    congrArg (fun S : ConvexCone ℝ E => (S : Set E)) hC_convex.toCone_eq_sInf.symm

/-- Helper for Example 6.10: symmetry upgrades the cone hull of a nonempty convex set to its
linear span. -/
lemma convexCone_hull_eq_span_of_eq_neg {C : Set E} (hC_nonempty : C.Nonempty)
    (hC_convex : Convex ℝ C) (hC_symmetric : C = -C) :
    (ConvexCone.hull ℝ C : Set E) = (Submodule.span ℝ C : Set E) := by
  -- First identify the hull with the canonical cone attached to `C`.
  rw [convexCone_hull_eq_toCone hC_convex]
  -- Proposition 6.4 then collapses that cone to the span under symmetry.
  simpa using (span_eq_cone_of_eq_neg hC_nonempty hC_convex hC_symmetric).symm

-- Proof sketch: apply the characterization of `ri` at the point `0`; for a symmetric convex set,
-- Proposition 6.4 identifies `cone C` with `span C`, and translating by `0` does not change `C`.
/-- Example 6.10 (1): if a nonempty convex set is symmetric with respect to the origin, then the
origin belongs to its relative interior. -/
theorem zero_mem_relativeInterior_of_eq_neg {C : Set E} (hC_nonempty : C.Nonempty)
    (hC_convex : Convex ℝ C) (hC_symmetric : C = -C) :
    (0 : E) ∈ {x ∈ C |
      (ConvexCone.hull ℝ (C - ({x} : Set E)) : Set E) =
        (Submodule.span ℝ (C - ({x} : Set E)) : Set E)} := by
  -- First place the origin in `C`, then normalize the translate `C - {0}` back to `C`.
  have h0 : (0 : E) ∈ C := zero_mem_of_nonempty_convex_eq_neg hC_nonempty hC_convex hC_symmetric
  have hsub : C - ({(0 : E)} : Set E) = C := sub_singleton_zero_eq_self
  refine ⟨h0, ?_⟩
  -- Proposition 6.4 gives `span C = cone C`; after rewriting by `hsub`, this is the target clause.
  calc
    (ConvexCone.hull ℝ (C - ({(0 : E)} : Set E)) : Set E)
        = (Submodule.span ℝ C : Set E) := by
          simpa [hsub] using convexCone_hull_eq_span_of_eq_neg hC_nonempty hC_convex hC_symmetric
    _ = (Submodule.span ℝ (C - ({(0 : E)} : Set E)) : Set E) := by
          simp [hsub]

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul ℝ E]

/-- Helper for Example 6.10: a closed span coincides with its topological closure. -/
lemma span_eq_topologicalClosure_of_isClosed {C : Set E}
    (hC_span_closed : IsClosed (((Submodule.span ℝ C : Submodule ℝ E) : Set E))) :
    (Submodule.span ℝ C : Set E) = ((Submodule.span ℝ C).topologicalClosure : Set E) := by
  -- Closed submodules are equal to their topological closure.
  have hclosure :
      (Submodule.span ℝ C).topologicalClosure = (Submodule.span ℝ C : Submodule ℝ E) :=
    IsClosed.submodule_topologicalClosure_eq hC_span_closed
  exact congrArg (fun S : Submodule ℝ E => (S : Set E)) hclosure.symm

-- Proof sketch: use the defining criterion for `sri` at `0`; symmetry and convexity again give
-- `cone C = span C` via Proposition 6.4, and the additional closedness assumption identifies this
-- span with its topological closure.
/-- Example 6.10 (2): if a nonempty convex set is symmetric with respect to the origin and its
linear span is closed, then the origin belongs to its strong relative interior. -/
theorem zero_mem_strongRelativeInterior_of_eq_neg_of_span_closed {C : Set E}
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) (hC_symmetric : C = -C)
    (hC_span_closed : IsClosed (((Submodule.span ℝ C : Submodule ℝ E) : Set E))) :
    (0 : E) ∈ {x ∈ C |
      (ConvexCone.hull ℝ (C - ({x} : Set E)) : Set E) =
        ((Submodule.span ℝ (C - ({x} : Set E))).topologicalClosure : Set E)} := by
  -- As in part (1), symmetry and convexity place the origin in `C` and trivialize the translate.
  have h0 : (0 : E) ∈ C := zero_mem_of_nonempty_convex_eq_neg hC_nonempty hC_convex hC_symmetric
  have hsub : C - ({(0 : E)} : Set E) = C := sub_singleton_zero_eq_self
  refine ⟨h0, ?_⟩
  -- Route correction: use Proposition 6.4 directly, then replace the span by its closure using
  -- the assumed closedness of `span C`.
  calc
    (ConvexCone.hull ℝ (C - ({(0 : E)} : Set E)) : Set E)
        = (Submodule.span ℝ C : Set E) := by
          simpa [hsub] using convexCone_hull_eq_span_of_eq_neg hC_nonempty hC_convex hC_symmetric
    _ = ((Submodule.span ℝ C).topologicalClosure : Set E) := by
          exact span_eq_topologicalClosure_of_isClosed hC_span_closed
    _ = ((Submodule.span ℝ (C - ({(0 : E)} : Set E))).topologicalClosure : Set E) := by
          simp [hsub]

end

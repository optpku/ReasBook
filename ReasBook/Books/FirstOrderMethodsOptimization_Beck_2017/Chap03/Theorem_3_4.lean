/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Theorem 3.4 is `source-facing` in the chapter real-valued convex-analysis API. The
`core/canonical` owner notions are Chapter 3's `subdifferential` and `strongDualSubdifferential`;
the declaration `subdifferentialAt` below is the stable real-valued specialization used
throughout the chapter, not a second owner abstraction. -/
/-- The real-valued subdifferential at `x`, viewed through the chapter's strong-dual bridge for
the extended-real-valued coercion of `f`. -/
abbrev subdifferentialAt (f : E → ℝ) (x : E) : Set (StrongDual ℝ E) :=
  strongDualSubdifferential (fun y ↦ (f y : EReal)) x

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: view `f` as the everywhere-finite extended-real-valued function
-- `y ↦ (f y : EReal)`. Its effective domain is all of `E`, so every `x` is an interior point.
-- The owner theorem `subdifferential_nonempty_at_interior_point` yields an algebraic dual
-- subgradient, and finite dimensionality upgrades that linear functional canonically to a
-- continuous one via `LinearMap.toContinuousLinearMap`; this is exactly a point of
-- `subdifferentialAt f x`.
/-- Theorem 3.4 in owner-set form: every real-valued convex function on `E` is subdifferentiable
at each point. -/
theorem subdifferentialAt_nonempty_of_convexOn {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x : E) :
    (subdifferentialAt f x).Nonempty := by
  have hconvex : is_convex_function (fun y ↦ (f y : EReal)) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro y hy
      simp
    · simpa [effective_domain] using hf
  have hx : x ∈ interior (effective_domain (fun y ↦ (f y : EReal))) := by
    simp [effective_domain]
  rcases
      subdifferential_nonempty_at_interior_point
        (fun y ↦ (f y : EReal)) x hconvex hx with
    ⟨g, hg⟩
  exact ⟨LinearMap.toContinuousLinearMap g, by simpa [subdifferentialAt] using hg⟩

end

section

open InnerProductSpace (toDualMap)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean/vector-side subdifferential at `x`, obtained by transporting the owner
`subdifferentialAt f x : Set (StrongDual ℝ E)` back to vectors using the Riesz map `toDualMap`.
This is a derived `bridge/view` API obtained by specializing `euclideanSubdifferential` to the
everywhere-finite coercion of `f`; `subdifferentialAt` remains the owner abstraction. -/
abbrev euclideanSubdifferentialAt (f : E → ℝ) (x : E) : Set E :=
  euclideanSubdifferential (fun y ↦ (f y : EReal)) x

/-- Membership in `euclideanSubdifferentialAt f x` is definitionally membership of the
corresponding functional `toDualMap ℝ E z` in `subdifferentialAt f x`. -/
@[simp] theorem mem_euclideanSubdifferentialAt_iff
    {f : E → ℝ} {x z : E} :
    z ∈ euclideanSubdifferentialAt f x ↔
      toDualMap ℝ E z ∈ subdifferentialAt f x :=
  mem_euclideanSubdifferential_iff

end

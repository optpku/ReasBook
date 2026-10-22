/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace Topology Laplacian

open scoped InnerProductSpace

/-- Definition 25.36: a real-valued function on `ℝ^d` solves the Dirichlet problem on `G` with
boundary value `f` if it is harmonic on `G`, extends continuously to `closure G`, and agrees with
`f` on `frontier G`. On an open set, this is equivalent to the textbook `C²` and `Δ u = 0`
formulation. -/
def SolvesDirichletProblem
    {d : ℕ} (G : Set (EuclideanSpace ℝ (Fin d))) (f : frontier G → ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  HarmonicContOnCl u G ∧ ∀ x : frontier G, u x = f x

namespace SolvesDirichletProblem

variable {d : ℕ} {G : Set (EuclideanSpace ℝ (Fin d))} {f : frontier G → ℝ}
  {u : EuclideanSpace ℝ (Fin d) → ℝ}

/-- A Dirichlet solution is harmonic on `G` and continuous on `closure G` in mathlib's canonical
owner API. -/
theorem harmonicContOnCl (hu : SolvesDirichletProblem G f u) :
    HarmonicContOnCl u G :=
  hu.1

/-- The solution matches the prescribed boundary datum on `frontier G`. -/
theorem boundary_eq (hu : SolvesDirichletProblem G f u) (x : frontier G) :
    u x = f x :=
  hu.2 x

/-- A Dirichlet solution is harmonic in a neighborhood of every point of `G`. -/
theorem harmonicOnNhd (hu : SolvesDirichletProblem G f u) :
    HarmonicOnNhd u G :=
  hu.harmonicContOnCl.harmonicOnNhd

/-- The solution extends continuously to `closure G`. -/
theorem continuousOn_closure (hu : SolvesDirichletProblem G f u) :
    ContinuousOn u (closure G) :=
  hu.harmonicContOnCl.continuousOn

/-- A Dirichlet solution is twice continuously differentiable on `G`. -/
theorem contDiffOn (hu : SolvesDirichletProblem G f u) :
    ContDiffOn ℝ 2 u G :=
  hu.harmonicOnNhd.contDiffOn

/-- A Dirichlet solution is harmonic on `G`, written as vanishing Laplacian. -/
theorem laplacian_eq_zero (hu : SolvesDirichletProblem G f u) :
    ∀ x ∈ G, Δ u x = 0 := by
  intro x hx
  exact (hu.harmonicOnNhd x hx).2.self_of_nhds

/-- On an open set, the canonical harmonic-owner formulation is equivalent to the textbook
`C²` plus `Δ u = 0` formulation. -/
theorem iff
    (hG : IsOpen G) :
    SolvesDirichletProblem G f u ↔
      ContinuousOn u (closure G) ∧
        ContDiffOn ℝ 2 u G ∧
        (∀ x ∈ G, Δ u x = 0) ∧
        ∀ x : frontier G, u x = f x := by
  constructor
  · intro hu
    exact ⟨hu.continuousOn_closure, hu.contDiffOn, hu.laplacian_eq_zero, hu.boundary_eq⟩
  · rintro ⟨hu_cont, hu_diff, hu_lap, hu_boundary⟩
    refine ⟨?_, hu_boundary⟩
    refine ⟨?_, hu_cont⟩
    intro x hx
    refine ⟨hu_diff.contDiffAt (hG.mem_nhds hx), ?_⟩
    filter_upwards [hG.mem_nhds hx] with y hy
    exact hu_lap y hy

end SolvesDirichletProblem

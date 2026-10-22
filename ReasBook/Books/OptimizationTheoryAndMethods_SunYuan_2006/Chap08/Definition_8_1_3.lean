/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped Topology

section ConstrainedLocalMinOn

variable {X : Type*} [TopologicalSpace X]
variable {α : Type*} [Preorder α]

-- Domain sampling:
-- * primary domain: constrained local extrema on subset neighborhoods in topological spaces
-- * source-facing owner: `IsConstrainedLocalMinOn`
-- * core/canonical owner: mathlib's `IsLocalMinOn`
-- * related declarations inspected:
--   `IsLocalMinOn`, `IsLocalMinOn.isLocalMin`, `nhdsWithin_insert`,
--   `ConstrainedOptimizationProblem.IsGlobalMinimizer`,
--   `IsStrictLocalMin` from `Chapter01/Definition_1_4_1`
-- * layer triage: source-facing owner adds feasibility to the topological neighborhood-filter
--   owner `IsLocalMinOn`,
--   with metric closed-ball formulations kept as bridge API below
-- * primitive data: feasibility together with the canonical local-minimum owner, and for the
--   strict notion eventual strict inequality on `𝓝[s \ {a}] a`
-- * derived API kept here: bridges to the canonical local-minimum owner and metric-ball
--   formulations

/- Core/canonical owner for local minima on a set. The source-facing constrained notion below adds
the feasibility clause that the textbook includes. -/
#check IsLocalMinOn

/-- Chapter08 Definition 8.1.3 (1): a constrained local minimizer on `s` is a feasible point `a`
that satisfies the canonical local-minimum owner `IsLocalMinOn f s a`. -/
def IsConstrainedLocalMinOn (f : X → α) (s : Set X) (a : X) : Prop :=
  a ∈ s ∧ IsLocalMinOn f s a

/-- Unfolding formula for `IsConstrainedLocalMinOn`. -/
theorem isConstrainedLocalMinOn_iff
    (f : X → α) (s : Set X) (a : X) :
    IsConstrainedLocalMinOn f s a ↔
      a ∈ s ∧ IsLocalMinOn f s a :=
  Iff.rfl

/-- A constrained local minimizer on `s` is feasible. -/
theorem IsConstrainedLocalMinOn.mem
    {f : X → α} {s : Set X} {a : X} (h : IsConstrainedLocalMinOn f s a) :
    a ∈ s :=
  h.1

/-- A constrained local minimizer on `s` satisfies the canonical local-minimum owner. -/
theorem IsConstrainedLocalMinOn.isLocalMinOn
    {f : X → α} {s : Set X} {a : X} (h : IsConstrainedLocalMinOn f s a) :
    IsLocalMinOn f s a :=
  h.2

/-- Chapter08 Definition 8.1.3 (2): a strict local minimizer on `s` is a feasible point `a`
whose value is strictly smaller than the value at every distinct nearby feasible point. -/
def IsStrictLocalMinOn (f : X → α) (s : Set X) (a : X) : Prop :=
  a ∈ s ∧ ∀ᶠ x in 𝓝[s \ {a}] a, f a < f x

/-- Unfolding formula for `IsStrictLocalMinOn`. -/
theorem isStrictLocalMinOn_iff
    (f : X → α) (s : Set X) (a : X) :
    IsStrictLocalMinOn f s a ↔
      a ∈ s ∧ ∀ᶠ x in 𝓝[s \ {a}] a, f a < f x :=
  Iff.rfl

/-- A strict local minimizer on `s` is feasible. -/
theorem IsStrictLocalMinOn.mem
    {f : X → α} {s : Set X} {a : X} (h : IsStrictLocalMinOn f s a) :
    a ∈ s :=
  h.1

/-- Near a strict local minimizer on `s`, every distinct feasible point has strictly larger
value. -/
theorem IsStrictLocalMinOn.eventually_lt
    {f : X → α} {s : Set X} {a : X} (h : IsStrictLocalMinOn f s a) :
    ∀ᶠ x in 𝓝[s \ {a}] a, f a < f x :=
  h.2

/-- A strict local minimizer on `s` is, in particular, a local minimizer on `s`. -/
theorem IsStrictLocalMinOn.isLocalMinOn
    {f : X → α} {s : Set X} {a : X} (h : IsStrictLocalMinOn f s a) :
    IsLocalMinOn f s a := by
  have hle : ∀ᶠ x in 𝓝[s \ {a}] a, f a ≤ f x :=
    h.eventually_lt.mono fun _ hx ↦ le_of_lt hx
  have hself : ∀ᶠ x in pure a, f a ≤ f x := by
    simp
  change {x | f a ≤ f x} ∈ 𝓝[s] a
  rw [← Set.insert_eq_of_mem h.mem, ← Set.insert_sdiff_singleton, nhdsWithin_insert]
  exact Filter.mem_sup.2 ⟨hself, hle⟩

/-- A strict local minimizer on `s` is, in particular, a constrained local minimizer on `s`. -/
theorem IsStrictLocalMinOn.isConstrainedLocalMinOn
    {f : X → α} {s : Set X} {a : X} (h : IsStrictLocalMinOn f s a) :
    IsConstrainedLocalMinOn f s a :=
  ⟨h.mem, h.isLocalMinOn⟩

end ConstrainedLocalMinOn

section Chapter08Definition813

variable {X : Type*} [PseudoMetricSpace X]
variable {α : Type*} [Preorder α]

/-- Closed-ball bridge for Chapter08 Definition 8.1.3 (1): a constrained local minimizer is a
feasible point whose value is no larger than that of every nearby feasible point. -/
theorem isConstrainedLocalMinOn_iff_exists_forall_mem_closedBall
    (f : X → α) (s : Set X) (a : X) :
    IsConstrainedLocalMinOn f s a ↔
      a ∈ s ∧
        ∃ δ > 0, ∀ x : X, x ∈ s ∩ Metric.closedBall a δ → f a ≤ f x := by
  constructor
  · rintro ⟨ha, h⟩
    change {x | f a ≤ f x} ∈ 𝓝[s] a at h
    rcases Metric.mem_nhdsWithin_iff.mp h with ⟨δ, hδ, hδball⟩
    refine ⟨ha, δ / 2, half_pos hδ, ?_⟩
    intro x hx
    apply hδball
    refine ⟨?_, hx.1⟩
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall] using hx.2) (half_lt_self hδ)
  · rintro ⟨ha, δ, hδ, hδclosed⟩
    refine ⟨ha, ?_⟩
    change {x | f a ≤ f x} ∈ 𝓝[s] a
    refine Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩
    intro x hx
    exact hδclosed x ⟨hx.2, Metric.mem_closedBall.2 (le_of_lt hx.1)⟩

/-- Closed-ball bridge for `IsStrictLocalMinOn`. -/
theorem isStrictLocalMinOn_iff_exists_forall_mem_closedBall
    (f : X → α) (s : Set X) (a : X) :
    IsStrictLocalMinOn f s a ↔
      a ∈ s ∧
        ∃ δ > 0,
          ∀ x : X, x ∈ s ∩ Metric.closedBall a δ → x ≠ a → f a < f x := by
  constructor
  · intro h
    refine ⟨h.mem, ?_⟩
    have hlt := h.eventually_lt
    change {x | f a < f x} ∈ 𝓝[s \ {a}] a at hlt
    rcases Metric.mem_nhdsWithin_iff.mp hlt with ⟨δ, hδ, hδball⟩
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    intro x hx hxa
    apply hδball
    refine ⟨?_, hx.1, by simpa using hxa⟩
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall] using hx.2) (half_lt_self hδ)
  · rintro ⟨ha, δ, hδ, hδclosed⟩
    refine ⟨ha, ?_⟩
    change {x | f a < f x} ∈ 𝓝[s \ {a}] a
    refine Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩
    intro x hx
    exact hδclosed x ⟨hx.2.1, Metric.mem_closedBall.2 (le_of_lt hx.1)⟩
      (by simpa using hx.2.2)

end Chapter08Definition813

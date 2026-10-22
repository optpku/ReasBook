/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Group.Basic

open scoped Topology

section StrictLocalMin

variable {X : Type*} [TopologicalSpace X]
variable {α : Type*} [Preorder α]

/-- A strict local minimizer is a point whose function value is strictly smaller than the value at
every distinct nearby point. -/
def IsStrictLocalMin (f : X → α) (xStar : X) : Prop :=
  ∀ᶠ x in nhdsWithin xStar {xStar}ᶜ, f xStar < f x

/-- Unfolding formula for `IsStrictLocalMin`. -/
theorem isStrictLocalMin_iff
    (f : X → α) (xStar : X) :
    IsStrictLocalMin f xStar ↔
      ∀ᶠ x in nhdsWithin xStar {xStar}ᶜ, f xStar < f x :=
  Iff.rfl

/-- A strict local minimizer is, in particular, a local minimizer. -/
theorem IsStrictLocalMin.isLocalMin
    {f : X → α} {xStar : X} (h : IsStrictLocalMin f xStar) :
    IsLocalMin f xStar := by
  have hpunctured : ∀ᶠ x in nhdsWithin xStar {xStar}ᶜ, f xStar ≤ f x :=
    h.mono fun _ hx ↦ le_of_lt hx
  have hself : ∀ᶠ x in pure xStar, f xStar ≤ f x := by
    simp
  rw [IsLocalMin, ← nhdsNE_sup_pure]
  exact Filter.mem_sup.2 ⟨hpunctured, hself⟩

end StrictLocalMin

section StrictLocalMinMetric

variable {X : Type*} [PseudoMetricSpace X]
variable {α : Type*} [Preorder α]

/-- Metric bridge for `IsStrictLocalMin`: in a pseudometric space, strict local minimality is
equivalent to the punctured-ball inequality from the source text. -/
theorem isStrictLocalMin_iff_exists_forall_mem_ball
    (f : X → α) (xStar : X) :
    IsStrictLocalMin f xStar ↔
      ∃ δ > 0, ∀ ⦃x : X⦄, x ∈ Metric.ball xStar δ → x ≠ xStar → f xStar < f x := by
  constructor
  · intro h
    change {x | f xStar < f x} ∈ nhdsWithin xStar {xStar}ᶜ at h
    rcases Metric.mem_nhdsWithin_iff.mp h with ⟨δ, hδ, hδball⟩
    refine ⟨δ, hδ, fun {x} hxball hne ↦ hδball ⟨hxball, by simpa using hne⟩⟩
  · rintro ⟨δ, hδ, hδball⟩
    change {x | f xStar < f x} ∈ nhdsWithin xStar {xStar}ᶜ
    refine Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩
    intro x hx
    exact hδball hx.1 (by simpa using hx.2)

end StrictLocalMinMetric

section Chapter01Definition141

variable {X : Type*} [SeminormedAddCommGroup X]
variable {α : Type*} [Preorder α]

-- Domain sampling:
-- * primary domain: local extrema in topological and normed-group spaces
-- * core/canonical owner: `IsMinFilter` specialized to neighborhood filters
-- * related canonical project/mathlib declarations inspected:
--   `IsMinFilter`, `IsLocalMin`, `nhdsNE_sup_pure`, `Metric.mem_nhdsWithin_iff`
-- * source-facing owner kept here: `IsStrictLocalMin`
-- * primitive data: eventual strict inequality on the punctured neighborhood filter `𝓝[≠] xStar`
-- * derived API kept here: metric-ball and norm-ball reformulations

/- Chapter01 Definition 1.4.1 (1): the canonical owner for a local minimizer is mathlib's
`IsLocalMin`. The norm-ball formula from the source is recorded below only as a normed-group bridge
theorem. -/
#check IsLocalMin

/-- Normed-group bridge for Definition 1.4.1 (1): `IsLocalMin` is equivalent to the
source's norm-ball inequality. -/
theorem isLocalMin_iff_exists_forall_norm_sub_lt
    (f : X → α) (xStar : X) :
    IsLocalMin f xStar ↔
      ∃ δ > 0, ∀ x : X, ‖x - xStar‖ < δ → f xStar ≤ f x := by
  constructor
  · intro h
    change {x | f xStar ≤ f x} ∈ nhds xStar at h
    rcases Metric.mem_nhds_iff.mp h with ⟨δ, hδ, hδball⟩
    refine ⟨δ, hδ, fun x hx ↦ hδball ?_⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  · rintro ⟨δ, hδ, hδnorm⟩
    change {x | f xStar ≤ f x} ∈ nhds xStar
    refine Metric.mem_nhds_iff.mpr ⟨δ, hδ, ?_⟩
    intro x hx
    exact hδnorm x (by simpa [Metric.mem_ball, dist_eq_norm] using hx)

/-- Normed-group bridge for Definition 1.4.1 (2): the canonical strict local-minimum owner is
exactly the source's punctured norm-ball inequality. -/
theorem isStrictLocalMin_iff_exists_forall_norm_sub_lt
    (f : X → α) (xStar : X) :
    IsStrictLocalMin f xStar ↔
      ∃ δ > 0, ∀ x : X, x ≠ xStar → ‖x - xStar‖ < δ → f xStar < f x := by
  rw [isStrictLocalMin_iff_exists_forall_mem_ball]
  constructor
  · rintro ⟨δ, hδ, hδball⟩
    refine ⟨δ, hδ, fun x hx hnorm ↦ hδball ?_ hx⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm
  · rintro ⟨δ, hδ, hδnorm⟩
    refine ⟨δ, hδ, ?_⟩
    intro x hxball hx
    exact hδnorm x hx (by simpa [Metric.mem_ball, dist_eq_norm] using hxball)

end Chapter01Definition141

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.PointwiseSupremumOn
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped WithTopConvexAnalysis

variable {ι : Type u} {X : Type v}

/- Theorem 3.1.8 lies in the chapter's `WithTop ℝ`-valued closed-convex pointwise-supremum
domain.

Sampled owner-style declarations in this domain:
- `pointwiseSupremumOn` and `pointwiseSupremumOn_apply` from `PointwiseSupremumOn`
- `dom` and `constrainedEpigraph` from `Definition_3_3`
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ConvexOn ℝ (dom f) (withTopRealPart f)` as the canonical convexity view behind
  `ClosedConvexOn`

Best owner abstraction:
- core/canonical owners reused from earlier chapter files:
  `pointwiseSupremumOn`, `dom`, and `ClosedConvexOn`
- bridge/view layer: the feasible-domain restriction
  `pointwiseSupremumOnEffectiveDomain Q Δ φ = Q ∩ dom (pointwiseSupremumOn Δ φ)`

Primitive data:
- the parameter subset `Δ : Set ι`
- the slice family `φ : X → ι → WithTop ℝ`
- the owner function `pointwiseSupremumOn Δ φ`

Derived API:
- `pointwiseSupremumOn_apply`
- `pointwiseSupremumOnEffectiveDomain`
- `mem_pointwiseSupremumOnEffectiveDomain_iff`
- `mem_pointwiseSupremumOnEffectiveDomain_iff_lt_top`
- `ClosedConvexOn.pointwise_sSup`

Source/core/bridge triage:
- source-facing: Theorem 3.1.8 itself, namely the closed-convexity theorem below
- core/canonical: `pointwiseSupremumOn`, `dom`, `ClosedConvexOn`
- bridge/view: `pointwiseSupremumOnEffectiveDomain`

This file reuses the generic owner `pointwiseSupremumOn`, and it does not keep a parallel
primitive notion of “finite-value domain”: that domain is derived canonically from the upstream
owner `dom` applied to `pointwiseSupremumOn Δ φ`, then intersected with the ambient feasible set
`Q`. -/

/-- The finite-value domain of the pointwise supremum over `Δ` inside `Q`, expressed through the
chapter owner `dom`. -/
abbrev pointwiseSupremumOnEffectiveDomain
    (Q : Set X) (Δ : Set ι) (φ : X → ι → WithTop ℝ) : Set X :=
  Q ∩ dom (pointwiseSupremumOn Δ φ)

/-- Membership in `pointwiseSupremumOnEffectiveDomain Q Δ φ` means lying in `Q` and in the
canonical effective domain of `pointwiseSupremumOn Δ φ`. -/
@[simp]
theorem mem_pointwiseSupremumOnEffectiveDomain_iff
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} :
    x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ ↔
      x ∈ Q ∧ x ∈ dom (pointwiseSupremumOn Δ φ) :=
  Iff.rfl

/-- Membership in `pointwiseSupremumOnEffectiveDomain Q Δ φ` can be read as a finiteness
condition on the pointwise supremum. -/
theorem mem_pointwiseSupremumOnEffectiveDomain_iff_lt_top
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} :
    x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ ↔
      x ∈ Q ∧ pointwiseSupremumOn Δ φ x < ⊤ := by
  rw [mem_pointwiseSupremumOnEffectiveDomain_iff, mem_withTopEffectiveDomain_iff]

section

variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

namespace ClosedConvexOn

omit [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] in
/-- Helper for Theorem 3.1.8: every admissible slice value lies below the pointwise supremum. -/
lemma slice_le_pointwiseSupremumOn
    {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} {y : ι}
    (hy : y ∈ Δ) :
    φ x y ≤ pointwiseSupremumOn Δ φ x := by
  -- The chosen slice contributes one element to the supremum-defining image set.
  rw [pointwiseSupremumOn_apply]
  refine le_csSup ?_ ?_
  · exact ⟨⊤, fun _ _ ↦ le_top⟩
  · exact ⟨y, hy, rfl⟩

omit [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] in
/-- Helper for Theorem 3.1.8: a uniform real upper bound on all admissible slices also bounds
the pointwise supremum. -/
lemma pointwiseSupremumOn_le_of_forall_le
    {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} {t : ℝ}
    (hΔ : Δ.Nonempty)
    (hupper : ∀ y ∈ Δ, φ x y ≤ t) :
    pointwiseSupremumOn Δ φ x ≤ t := by
  -- The supremum is below `t` because every element of its defining image set is below `t`.
  rw [pointwiseSupremumOn_apply]
  refine csSup_le ?_ ?_
  · rcases hΔ with ⟨y, hy⟩
    exact ⟨φ x y, ⟨y, hy, rfl⟩⟩
  · intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact hupper y hy

omit [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] in
/-- Helper for Theorem 3.1.8: the constrained epigraph over the finite-value domain of the
pointwise supremum is the intersection of the constrained epigraphs of the admissible slices. -/
lemma constrainedEpigraph_pointwiseSupremumOnEffectiveDomain_eq_iInter
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ}
    (hΔ : Δ.Nonempty) :
    constrainedEpigraph (pointwiseSupremumOnEffectiveDomain Q Δ φ) (pointwiseSupremumOn Δ φ) =
      ⋂ y : Δ, constrainedEpigraph Q (fun x ↦ φ x y) := by
  ext p
  constructor
  · intro hp
    rw [Set.mem_iInter]
    intro y
    rcases mem_constrainedEpigraph_iff.mp hp with ⟨hpEff, hpLe⟩
    rcases mem_pointwiseSupremumOnEffectiveDomain_iff.mp hpEff with ⟨hpQ, _⟩
    -- Every slice sits below the supremum, so the epigraph point belongs to each slice epigraph.
    refine mem_constrainedEpigraph_iff.mpr ?_
    exact ⟨hpQ, le_trans (slice_le_pointwiseSupremumOn (Δ := Δ) (φ := φ) y.2) hpLe⟩
  · intro hp
    rw [Set.mem_iInter] at hp
    rcases hΔ with ⟨y0, hy0⟩
    have hp0 : p ∈ constrainedEpigraph Q (fun x ↦ φ x y0) := hp ⟨y0, hy0⟩
    rcases mem_constrainedEpigraph_iff.mp hp0 with ⟨hpQ, _⟩
    have hslice_upper : ∀ y ∈ Δ, φ p.1 y ≤ p.2 := by
      intro y hy
      exact (mem_constrainedEpigraph_iff.mp (hp ⟨y, hy⟩)).2
    have hsup_le :
        pointwiseSupremumOn Δ φ p.1 ≤ p.2 :=
      pointwiseSupremumOn_le_of_forall_le (Δ := Δ) (φ := φ) (x := p.1) (t := p.2) ⟨y0, hy0⟩
        hslice_upper
    have hp2_lt_top : ((p.2 : ℝ) : WithTop ℝ) < ⊤ :=
      WithTop.coe_lt_top p.2
    have hsup_lt_top : pointwiseSupremumOn Δ φ p.1 < ⊤ :=
      lt_of_le_of_lt hsup_le hp2_lt_top
    have hpEff : p.1 ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ :=
      (mem_pointwiseSupremumOnEffectiveDomain_iff_lt_top).2 ⟨hpQ, hsup_lt_top⟩
    -- The uniform slice bound upgrades to a bound on the supremum, and the real height enforces
    -- finiteness of that supremum on the base point.
    exact mem_constrainedEpigraph_iff.mpr ⟨hpEff, hsup_le⟩

/-- Theorem 3.1.8: if every slice `x ↦ φ(x, y)` with `y ∈ Δ` is closed and convex on `Q`, then
the pointwise supremum `x ↦ sup_{y ∈ Δ} φ(x, y)` is closed and convex on the finite-value domain
`{x ∈ Q | sup_{y ∈ Δ} φ(x, y) < +∞}`. -/
-- Proof sketch: the constrained epigraph of `pointwiseSupremumOn Δ φ` over
-- `pointwiseSupremumOnEffectiveDomain Q Δ φ` is the intersection over `y ∈ Δ` of the constrained
-- epigraphs of the slices `x ↦ φ x y`. Intersections preserve closedness and convexity, and the
-- finiteness-on-domain clause is built into `pointwiseSupremumOnEffectiveDomain`.
theorem pointwise_sSup
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ}
    (hΔ : Δ.Nonempty)
    (hφ : ∀ y ∈ Δ, ClosedConvexOn Q (fun x ↦ φ x y)) :
    ClosedConvexOn (pointwiseSupremumOnEffectiveDomain Q Δ φ) (pointwiseSupremumOn Δ φ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    -- The effective-domain component of the target is already packaged in the definition.
    exact (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hx).2
  · -- Rewrite the constrained epigraph as a slice intersection and use closedness of each slice.
    rw [constrainedEpigraph_pointwiseSupremumOnEffectiveDomain_eq_iInter
      (Q := Q) (Δ := Δ) (φ := φ) hΔ]
    refine isClosed_iInter ?_
    intro y
    exact (hφ y y.2).isClosed_constrainedEpigraph
  · -- The same intersection identity preserves convexity as well.
    rw [constrainedEpigraph_pointwiseSupremumOnEffectiveDomain_eq_iInter
      (Q := Q) (Δ := Δ) (φ := φ) hΔ]
    refine convex_iInter ?_
    intro y
    exact (hφ y y.2).convex_constrainedEpigraph

end ClosedConvexOn

end

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators WithTopConvexAnalysis

universe u

variable {X : Type u} {ι : Type*} [Fintype ι]
  [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Proposition 3.1.2.1 lies in the chapter's closed-convex weighted pointwise-supremum domain.

Primary domain:
- weighted pointwise suprema of `WithTop ℝ`-valued functions on a real topological module.

Sampled owner-style declarations:
- `pointwiseSupremumOn` and `pointwiseSupremumOn_apply`
- `pointwiseSupremumOnEffectiveDomain`
- `ClosedConvexOn.pointwise_sSup`
- `ClosedConvexOn.nonneg_smul` and `ClosedConvexOn.add_inter`

Best owner abstraction:
- source-facing: this proposition, which bridges componentwise closed-convexity and nonnegative
  weights to the chapter owner theorem for pointwise suprema
- core/canonical: `pointwiseSupremumOn`, `pointwiseSupremumOnEffectiveDomain`, and
  `ClosedConvexOn.pointwise_sSup`
- bridge/view: the weighted slice family
  `fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x`

Primitive data:
- a weight set `Δ : Set (ι → ℝ)`
- a family `f : ι → X → WithTop ℝ`
- nonemptiness of `Δ`
- coordinatewise nonnegativity of the weights in `Δ`
- closed-convexity of each component `f i`

Derived API:
- the weighted-slice pointwise-supremum owner
  `pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)`
- the closed-convexity theorem below for that owner

This proposition is not recall-only: its mathematical content is the bridge from the componentwise
assumptions on the family `f i` and the coordinatewise nonnegative weight functions in `Δ` to
the slicewise hypothesis required by `ClosedConvexOn.pointwise_sSup`. The later file
`Proposition_3_9` therefore
reuses this theorem directly instead of keeping a second public copy of the same bridge. -/

-- Proof sketch: first prove each weighted slice is a closed convex function by finite induction on
-- the sum, using the nonnegative weighted-add rule at each step. Then identify the effective
-- epigraph of the pointwise supremum with the intersection of the slice effective epigraphs. The
-- closedness and convexity fields of `ClosedConvexFunction` then follow from intersection
-- stability.
/-- Helper for Proposition 3.1.2.1: the constant zero `WithTop ℝ`-valued function is closed and
convex. -/
lemma closedConvexFunction_zero : ClosedConvexFunction (fun _ : X ↦ (0 : WithTop ℝ)) := by
  -- The zero function is the coercion of a continuous convex real-valued function.
  simpa using
    (closedConvexFunction_coe_of_convexOn_continuous
      (f := fun _ : X ↦ (0 : ℝ))
      (convexOn_const (0 : ℝ) convex_univ)
      continuous_const)

/-- Helper for Proposition 3.1.2.1: every admissible nonnegative weighted slice is a closed convex
function. -/
lemma closedConvexFunction_weighted_slice
    {Δ : Set (ι → ℝ)} {f : ι → X → WithTop ℝ}
    (hΔ_nonneg : ∀ ⦃weights⦄, weights ∈ Δ → ∀ i, 0 ≤ weights i)
    (hf : ∀ i, ClosedConvexFunction (f i))
    {weights : ι → ℝ} (hs : weights ∈ Δ) :
    ClosedConvexFunction (fun x ↦ ∑ i, (weights i : WithTop ℝ) * f i x) := by
  classical
  -- Build the finite weighted sum by inserting one nonnegative weighted summand at a time.
  have hzero : ClosedConvexFunction
      (fun x ↦ ∑ i ∈ (∅ : Finset ι), (weights i : WithTop ℝ) * f i x) := by
    simpa using closedConvexFunction_zero (X := X)
  have hstep : ∀ a s, a ∉ s →
      ClosedConvexFunction (fun x ↦ ∑ i ∈ s, (weights i : WithTop ℝ) * f i x) →
      ClosedConvexFunction (fun x ↦ ∑ i ∈ insert a s, (weights i : WithTop ℝ) * f i x) := by
    intro a s ha hsCC
    -- The induction step is the nonnegative weighted-add rule with coefficient `1` on the tail.
    have hsum :=
      ClosedConvexFunction.nonneg_weighted_add (hf a) hsCC (hΔ_nonneg hs a) zero_le_one
    simpa [Finset.sum_insert, ha, smul_eq_mul, Pi.add_apply, one_smul] using hsum
  simpa using Finset.induction hzero hstep (Finset.univ : Finset ι)

/-- Helper for Proposition 3.1.2.1: each admissible weighted slice lies below the pointwise
supremum. -/
lemma weighted_slice_le_pointwiseSupremumOn
    {Δ : Set (ι → ℝ)} {f : ι → X → WithTop ℝ}
    {weights : ι → ℝ} (hs : weights ∈ Δ) (x : X) :
    (∑ i, (weights i : WithTop ℝ) * f i x) ≤
      pointwiseSupremumOn Δ (fun y weights ↦ ∑ i, (weights i : WithTop ℝ) * f i y) x := by
  -- The chosen slice is one member of the supremum-defining image set.
  rw [pointwiseSupremumOn_apply]
  refine le_csSup ?_ ?_
  · exact ⟨⊤, fun _ _ ↦ le_top⟩
  · exact ⟨weights, hs, rfl⟩

/-- Helper for Proposition 3.1.2.1: the effective epigraph of the weighted pointwise supremum is
the intersection of the slice effective epigraphs. -/
lemma effectiveEpigraph_pointwiseSupremumOn_nonneg_weighted_eq_iInter
    {Δ : Set (ι → ℝ)} {f : ι → X → WithTop ℝ}
    (hΔ_nonempty : Δ.Nonempty) :
    WithTopConvexAnalysis.effectiveEpigraph
        (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) =
      ⋂ weights : Δ,
        WithTopConvexAnalysis.effectiveEpigraph
          (fun x ↦ ∑ i, ((weights.1 i : ℝ) : WithTop ℝ) * f i x) := by
  ext p
  constructor
  · intro hp
    rw [Set.mem_iInter]
    intro weights
    rcases WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp hp with ⟨hpdom, hple⟩
    have hslicele := weighted_slice_le_pointwiseSupremumOn (f := f) weights.2 p.1
    have hslicedom : p.1 ∈ dom (fun x ↦ ∑ i, ((weights.1 i : ℝ) : WithTop ℝ) * f i x) := by
      rw [mem_withTopEffectiveDomain_iff]
      exact
        lt_of_le_of_lt (le_trans hslicele hple)
          (show (p.2 : WithTop ℝ) < ⊤ from WithTop.coe_lt_top p.2)
    exact WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr ⟨hslicedom, le_trans hslicele hple⟩
  · intro hp
    rw [Set.mem_iInter] at hp
    rcases hΔ_nonempty with ⟨weights0, hs0⟩
    refine WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr ?_
    constructor
    · rw [mem_withTopEffectiveDomain_iff, pointwiseSupremumOn_apply]
      refine lt_of_le_of_lt ?_ (show (p.2 : WithTop ℝ) < ⊤ from WithTop.coe_lt_top p.2)
      refine csSup_le ?_ ?_
      · exact ⟨_, ⟨weights0, hs0, rfl⟩⟩
      · intro z hz
        rcases hz with ⟨weights, hs, rfl⟩
        exact (WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp (hp ⟨weights, hs⟩)).2
    · rw [pointwiseSupremumOn_apply]
      refine csSup_le ?_ ?_
      · exact ⟨_, ⟨weights0, hs0, rfl⟩⟩
      · intro z hz
        rcases hz with ⟨weights, hs, rfl⟩
        exact (WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp (hp ⟨weights, hs⟩)).2

/-- Proposition 3.1.2.1: for a nonempty family of coordinatewise nonnegative finite weights, the
weighted pointwise supremum built from the finite sums `x ↦ ∑ i, weights i * f i x` of closed
convex functions is again a closed convex function. -/
theorem closedConvexFunction_pointwiseSupremumOn_nonneg_weighted
    {Δ : Set (ι → ℝ)} {f : ι → X → WithTop ℝ}
    (hΔ_nonempty : Δ.Nonempty)
    (hΔ_nonneg : ∀ ⦃weights⦄, weights ∈ Δ → ∀ i, 0 ≤ weights i)
    (hf : ∀ i, ClosedConvexFunction (f i)) :
    ClosedConvexFunction
      (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) := by
  refine ⟨subset_rfl, ?_, ?_⟩
  · -- The supremum effective epigraph is an intersection of closed slice effective epigraphs.
    rw [show constrainedEpigraph
        (dom (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)))
        (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) =
        WithTopConvexAnalysis.effectiveEpigraph
          (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) by
      rfl]
    rw [effectiveEpigraph_pointwiseSupremumOn_nonneg_weighted_eq_iInter
      (Δ := Δ) (f := f) hΔ_nonempty]
    refine isClosed_iInter ?_
    intro weights
    -- Each slice is closed because the slice itself is a closed convex function.
    have hslice :=
      closedConvexFunction_weighted_slice (Δ := Δ) (f := f) hΔ_nonneg hf weights.2
    simpa [WithTopConvexAnalysis.effectiveEpigraph] using hslice.isClosed_constrainedEpigraph
  · -- The same effective-epigraph intersection identity preserves convexity as well.
    rw [show constrainedEpigraph
        (dom (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)))
        (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) =
        WithTopConvexAnalysis.effectiveEpigraph
          (pointwiseSupremumOn Δ (fun x weights ↦ ∑ i, (weights i : WithTop ℝ) * f i x)) by
      rfl]
    rw [effectiveEpigraph_pointwiseSupremumOn_nonneg_weighted_eq_iInter
      (Δ := Δ) (f := f) hΔ_nonempty]
    refine convex_iInter ?_
    intro weights
    -- Each slice contributes a convex effective epigraph to the intersection.
    have hslice :=
      closedConvexFunction_weighted_slice (Δ := Δ) (f := f) hΔ_nonneg hf weights.2
    simpa [WithTopConvexAnalysis.effectiveEpigraph] using hslice.convex_constrainedEpigraph

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_28
import Mathlib.Topology.Algebra.SeparationQuotient.Section

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped Topology WithTopConvexAnalysis

universe u v

variable {ι : Type u}

/- Lemma 3.13 lies in the finite-family specialization of Chapter 3's pointwise-supremum and
active-subdifferential calculus for `WithTop ℝ`-valued convex functions.

Relevant owner-style declarations sampled before refinement:
- `pointwiseSupremumOn` in `PointwiseSupremumOn`
- `activePointwiseSupremumOnIndices` in `Lemma_3_1_14`
- `ClosedConvexOn.pointwise_sSup` in `Theorem_3_1_8`
- `subdifferential` in `Definition_3_1_5`

Best owner abstraction:
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`,
  `ClosedConvexOn.pointwise_sSup`, `dom`, `ClosedConvexFunction`, `subdifferential`

Primitive data:
- a finite index type `ι`
- a family `φ : X → ι → WithTop ℝ`

Derived API in this file:
- the finite-specialization bridge `pointwiseSupremumOn_univ_eq_sup'`
- the finite inequality and active-set bridges
- the closed-convex, interior-domain, and unconstrained active-subdifferential conclusions for
  the specialization `pointwiseSupremumOn (Set.univ : Set ι) φ`

Source/core/bridge triage:
- source-facing: Lemma 3.13 as the finite-family specialization of the chapter supremum calculus
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`,
  `ClosedConvexOn.pointwise_sSup`, `dom`, `ClosedConvexFunction`, `subdifferential`
- bridge/view: `pointwiseSupremumOn_univ_eq_sup'`, `pointwiseSupremumOn_univ_le_zero_iff`,
  `mem_activePointwiseSupremumOnIndices_univ_iff`

This file therefore does not introduce a second finite-maximum owner. It keeps only the finite
`Set.univ` specialization layer above the existing chapter owner `pointwiseSupremumOn`, and it
states the genuinely finite-specific domain/interior and unconstrained active-subdifferential
results directly on that owner surface.
-/

/-- Evaluating the Chapter 3 supremum owner on the finite set `Set.univ` reproduces the usual
nonempty finite supremum. -/
theorem pointwiseSupremumOn_univ_eq_sup'
    [Fintype ι] [Nonempty ι] {X : Type v} {φ : X → ι → WithTop ℝ} {x : X} :
    pointwiseSupremumOn (Set.univ : Set ι) φ x =
      Finset.univ.sup' Finset.univ_nonempty (φ x) := by
  simpa [pointwiseSupremumOn_apply, Set.image_univ] using
    (Finset.sup'_eq_csSup_image Finset.univ Finset.univ_nonempty (φ x)).symm

/-- The `Set.univ` specialization of `pointwiseSupremumOn` is nonpositive at `x` exactly when
every slice is nonpositive there. -/
theorem pointwiseSupremumOn_univ_le_zero_iff
    {X : Type v} {φ : X → ι → WithTop ℝ} {x : X} :
    pointwiseSupremumOn (Set.univ : Set ι) φ x ≤ 0 ↔ ∀ i : ι, φ x i ≤ 0 := by
  classical
  by_cases hι : Nonempty ι
  · let _ : Nonempty ι := hι
    simpa [pointwiseSupremumOn_apply, Set.image_univ, iSup] using
      (ciSup_le_iff
        (show BddAbove (Set.range (φ x)) from ⟨⊤, fun _ _ ↦ le_top⟩))
  · let _ : IsEmpty ι := not_nonempty_iff.mp hι
    rw [pointwiseSupremumOn_apply, Set.image_univ, Set.range_eq_empty]
    simp [sSup]

/-- For the finite specialization `Δ = Set.univ`, an index is active exactly when its slice
attains the pointwise supremum value. -/
@[simp] theorem mem_activePointwiseSupremumOnIndices_univ_iff
    {X : Type v} {φ : X → ι → WithTop ℝ} {x : X} {i : ι} :
    i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ↔
      φ x i = pointwiseSupremumOn (Set.univ : Set ι) φ x := by
  simpa using
    (mem_activePointwiseSupremumOnIndices_iff :
      i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ↔
        i ∈ (Set.univ : Set ι) ∧
          φ x i = pointwiseSupremumOn (Set.univ : Set ι) φ x)

section ClosedConvex

variable {X : Type v} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Helper for Lemma 3.13: if the index type is empty, the `Set.univ` pointwise supremum is the
constant zero function. -/
lemma pointwiseSupremumOn_univ_eq_zero_of_isEmpty
    [IsEmpty ι] {φ : X → ι → WithTop ℝ} :
    pointwiseSupremumOn (Set.univ : Set ι) φ = fun _ ↦ (0 : WithTop ℝ) := by
  funext x
  -- With no active indices, the supremum is over the empty image set.
  rw [pointwiseSupremumOn_apply, Set.image_univ, Set.range_eq_empty]
  simp [sSup]

/-- Helper for Lemma 3.13: the nonempty finite specialization of the pointwise supremum of closed
convex extended-real-valued functions is again a closed convex function. -/
-- Proof sketch: specialize the finite-family pointwise supremum to the chapter owner
-- `pointwiseSupremumOn (Set.univ : Set ι) φ`, then apply the usual epigraph-intersection argument
-- for finitely many closed convex slices.
theorem closedConvexFunction_pointwiseSupremumOn_univ
    [Finite ι] [Nonempty ι]
    {φ : X → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun x ↦ φ x i)) :
    ClosedConvexFunction (pointwiseSupremumOn (Set.univ : Set ι) φ) := by
  classical
  let f : X → WithTop ℝ := pointwiseSupremumOn (Set.univ : Set ι) φ
  have hEpigraph :
      constrainedEpigraph (dom f) f =
        ⋂ i : ι, constrainedEpigraph (dom (fun x ↦ φ x i)) (fun x ↦ φ x i) := by
    ext p
    constructor
    · intro hp
      rw [Set.mem_iInter]
      intro i
      rcases mem_constrainedEpigraph_iff.mp hp with ⟨hpDom, hpLe⟩
      refine mem_constrainedEpigraph_iff.mpr ?_
      constructor
      · change φ p.1 i < ⊤
        have hle : φ p.1 i ≤ f p.1 := by
          rw [show f p.1 = pointwiseSupremumOn (Set.univ : Set ι) φ p.1 by rfl,
            pointwiseSupremumOn_apply]
          exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ ⟨i, by simp, rfl⟩
        exact lt_of_le_of_lt hle hpDom
      · have hle : φ p.1 i ≤ f p.1 := by
          rw [show f p.1 = pointwiseSupremumOn (Set.univ : Set ι) φ p.1 by rfl,
            pointwiseSupremumOn_apply]
          exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ ⟨i, by simp, rfl⟩
        exact hle.trans hpLe
    · intro hp
      let i₀ : ι := Classical.choice ‹Nonempty ι›
      rw [Set.mem_iInter] at hp
      have hsSup_le : f p.1 ≤ p.2 := by
        rw [show f p.1 = pointwiseSupremumOn (Set.univ : Set ι) φ p.1 by rfl,
          pointwiseSupremumOn_apply]
        have himage_nonempty :
            ((fun y ↦ φ p.1 y) '' (Set.univ : Set ι)).Nonempty := by
          exact ⟨φ p.1 i₀, ⟨i₀, by simp, rfl⟩⟩
        exact csSup_le himage_nonempty fun _ hs ↦ by
          rcases hs with ⟨i, -, rfl⟩
          exact (mem_constrainedEpigraph_iff.mp (hp i)).2
      refine mem_constrainedEpigraph_iff.mpr ?_
      constructor
      · exact lt_of_le_of_lt hsSup_le (by simp)
      · exact hsSup_le
  refine ⟨subset_rfl, ?_, ?_⟩
  · rw [hEpigraph]
    exact isClosed_iInter fun i ↦ (hφ i).isClosed_constrainedEpigraph
  · rw [hEpigraph]
    exact convex_iInter fun i ↦ (hφ i).convex_constrainedEpigraph

end ClosedConvex

/-- Helper for Lemma 3.13: the interior of the effective domain of the nonempty finite
specialization of the pointwise supremum is the intersection of the interiors of the component
effective domains. -/
-- Proof sketch: rewrite the effective domain using `pointwiseSupremumOn_univ_eq_sup'` and
-- `Finset.sup'_lt_iff`, then apply the canonical finite-intersection identity
-- `interior_iInter_of_finite`.
theorem interior_dom_pointwiseSupremumOn_univ
    [Finite ι] [Nonempty ι] {X : Type v} [TopologicalSpace X] {φ : X → ι → WithTop ℝ} :
    interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ)) =
      ⋂ i : ι, interior (dom (fun x ↦ φ x i)) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have hdom :
      dom (pointwiseSupremumOn (Set.univ : Set ι) φ) = ⋂ i : ι, dom (fun x ↦ φ x i) := by
    ext x
    classical
    constructor
    · intro hx
      change pointwiseSupremumOn (Set.univ : Set ι) φ x < (⊤ : WithTop ℝ) at hx
      rw [pointwiseSupremumOn_univ_eq_sup'] at hx
      rw [Set.mem_iInter]
      have hlt :
          Finset.univ.sup' Finset.univ_nonempty (φ x) < (⊤ : WithTop ℝ) ↔
            ∀ i ∈ Finset.univ, φ x i < ⊤ := by
        simpa using
          (Finset.sup'_lt_iff :
            Finset.univ.sup' Finset.univ_nonempty (φ x) < (⊤ : WithTop ℝ) ↔
              ∀ i ∈ Finset.univ, φ x i < ⊤)
      intro i
      change φ x i < (⊤ : WithTop ℝ)
      exact hlt.mp hx i (by simp)
    · intro hx
      rw [Set.mem_iInter] at hx
      change pointwiseSupremumOn (Set.univ : Set ι) φ x < (⊤ : WithTop ℝ)
      rw [pointwiseSupremumOn_univ_eq_sup']
      have hlt :
          Finset.univ.sup' Finset.univ_nonempty (φ x) < (⊤ : WithTop ℝ) ↔
            ∀ i ∈ Finset.univ, φ x i < ⊤ := by
        simpa using
          (Finset.sup'_lt_iff :
            Finset.univ.sup' Finset.univ_nonempty (φ x) < (⊤ : WithTop ℝ) ↔
              ∀ i ∈ Finset.univ, φ x i < ⊤)
      exact hlt.mpr fun i hi ↦ hx i
  simpa [hdom] using
    (interior_iInter_of_finite (fun i : ι ↦ dom (fun x ↦ φ x i)))

section Subdifferential

variable {V : Type v} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Helper for Lemma 3.13: a closed convex function is constant on every
`SeparationQuotient` fiber. -/
lemma closedConvexFunction_eq_of_separationQuotient_eq
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x y : V}
    (hxy : SeparationQuotient.mk x = SeparationQuotient.mk y) :
    f x = f y := by
  have hInsep : Inseparable x y := (SeparationQuotient.mk_eq_mk).mp hxy
  by_cases hx : x ∈ dom f
  · have hy_le :
        f y ≤ (withTopRealPart f x : WithTop ℝ) := by
      have hx_epi :
          (x, withTopRealPart f x) ∈ constrainedEpigraph (dom f) f := by
        -- The base epigraph point over `x` is closedly transported along the inseparable fiber.
        exact ⟨hx, le_of_eq (coe_withTopRealPart hx).symm⟩
      have hprod :
          Inseparable (x, withTopRealPart f x) (y, withTopRealPart f x) :=
        hInsep.prod <| by
          rw [inseparable_iff_specializes_and]
          exact ⟨specializes_refl _, specializes_refl _⟩
      have hy_epi :
          (y, withTopRealPart f x) ∈ constrainedEpigraph (dom f) f :=
        (hprod.mem_closed_iff hf.isClosed_constrainedEpigraph).mp hx_epi
      exact hy_epi.2
    have hy : y ∈ dom f := lt_of_le_of_lt hy_le (by simp)
    have hx_le :
        f x ≤ (withTopRealPart f y : WithTop ℝ) := by
      have hy_epi :
          (y, withTopRealPart f y) ∈ constrainedEpigraph (dom f) f := by
        -- Repeat the same closed-epigraph transport in the reverse direction.
        exact ⟨hy, le_of_eq (coe_withTopRealPart hy).symm⟩
      have hprod :
          Inseparable (y, withTopRealPart f y) (x, withTopRealPart f y) :=
        hInsep.symm.prod <| by
          rw [inseparable_iff_specializes_and]
          exact ⟨specializes_refl _, specializes_refl _⟩
      have hx_epi :
          (x, withTopRealPart f y) ∈ constrainedEpigraph (dom f) f :=
        (hprod.mem_closed_iff hf.isClosed_constrainedEpigraph).mp hy_epi
      exact hx_epi.2
    have hxy_real : withTopRealPart f y ≤ withTopRealPart f x := by
      exact (withTopRealPart_le_iff hy).2 hy_le
    have hyx_real : withTopRealPart f x ≤ withTopRealPart f y := by
      exact (withTopRealPart_le_iff hx).2 hx_le
    have hreal : withTopRealPart f x = withTopRealPart f y :=
      le_antisymm hyx_real hxy_real
    rw [← coe_withTopRealPart hx, ← coe_withTopRealPart hy]
    exact congrArg (fun t : ℝ ↦ (t : WithTop ℝ)) hreal
  · have hfx_top : f x = ⊤ := by
      by_contra hfx_top
      exact hx (by
        rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top]
        exact hfx_top)
    have hfy_top : f y = ⊤ := by
      by_contra hfy_top
      have hy : y ∈ dom f := by
        rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top]
        exact hfy_top
      have hx_le :
          f x ≤ (withTopRealPart f y : WithTop ℝ) := by
        have hy_epi :
            (y, withTopRealPart f y) ∈ constrainedEpigraph (dom f) f := by
          exact ⟨hy, le_of_eq (coe_withTopRealPart hy).symm⟩
        have hprod :
            Inseparable (y, withTopRealPart f y) (x, withTopRealPart f y) :=
          hInsep.symm.prod <| by
            rw [inseparable_iff_specializes_and]
            exact ⟨specializes_refl _, specializes_refl _⟩
        have hx_epi :
            (x, withTopRealPart f y) ∈ constrainedEpigraph (dom f) f :=
          (hprod.mem_closed_iff hf.isClosed_constrainedEpigraph).mp hy_epi
        exact hx_epi.2
      exact hx (lt_of_le_of_lt hx_le (by simp))
    simp [hfx_top, hfy_top]

/-- Helper for Lemma 3.13: precomposing a closed convex function with a continuous linear map
preserves closed convexity. -/
lemma ClosedConvexFunction.compContinuousLinearMap
    {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) (A : W →L[ℝ] V) :
    ClosedConvexFunction (fun w ↦ f (A w)) := by
  -- Reuse the owner pullback theorem for closed convex functions along continuous affine maps.
  simpa [ClosedConvexFunction] using
    (ClosedConvexOn.comp_continuousAffineMap (S := dom f) (φ := f) hf A.toContinuousAffineMap)

/-- Helper for Lemma 3.13: adding a zero-norm vector does not change subdifferential membership.
-/
lemma memSubdifferential_iff_add_zeroNorm
    {f : V → WithTop ℝ} {x g k : V} (hk : ‖k‖ = 0) :
    g ∈ ∂ f(x) ↔ g + k ∈ ∂ f(x) := by
  rw [mem_subdifferential_iff, mem_subdifferential_iff]
  constructor
  · rintro ⟨hx, hminorant⟩
    refine ⟨hx, ?_⟩
    intro y hy
    have hinner_zero : inner ℝ k (y - x) = 0 := by
      apply norm_eq_zero.mp
      refine le_antisymm ?_ (norm_nonneg _)
      calc
        ‖inner ℝ k (y - x)‖ ≤ ‖k‖ * ‖y - x‖ := norm_inner_le_norm _ _
        _ = 0 := by simp [hk]
    -- A zero-norm direction contributes no affine term to the supporting inequality.
    simpa [inner_add_left, hinner_zero] using hminorant hy
  · rintro ⟨hx, hminorant⟩
    refine ⟨hx, ?_⟩
    intro y hy
    have hinner_zero : inner ℝ k (y - x) = 0 := by
      apply norm_eq_zero.mp
      refine le_antisymm ?_ (norm_nonneg _)
      calc
        ‖inner ℝ k (y - x)‖ ≤ ‖k‖ * ‖y - x‖ := norm_inner_le_norm _ _
        _ = 0 := by simp [hk]
    -- The same zero contribution lets us move back from `g + k` to `g`.
    simpa [inner_add_left, hinner_zero] using hminorant hy

/-- Helper for Lemma 3.13: a subgradient pushes forward to the quotient-lifted function. -/
lemma memSubdifferential_comp_outCLM_of_memSubdifferential
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x g : V}
    (hg : g ∈ ∂ f(x)) :
    SeparationQuotient.mk g ∈
      subdifferential
        (fun q : SeparationQuotient V ↦ f (SeparationQuotient.outCLM ℝ V q))
        (SeparationQuotient.mk x) := by
  rw [mem_subdifferential_iff] at hg ⊢
  rcases hg with ⟨hx, hminorant⟩
  refine ⟨?_, ?_⟩
  · -- The quotient base point has the same slice value as the original representative.
    have hx_eq :
        f (SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk x)) = f x :=
      closedConvexFunction_eq_of_separationQuotient_eq
        hf (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk x))
    simpa [hx_eq] using hx
  · intro q hq
    have hx_eq :
        f (SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk x)) = f x :=
      closedConvexFunction_eq_of_separationQuotient_eq
        hf (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk x))
    have hinner_real :
        inner ℝ (SeparationQuotient.mk g) (q - SeparationQuotient.mk x) =
          inner ℝ g (SeparationQuotient.outCLM ℝ V q - x) := by
      rw [← SeparationQuotient.mk_outCLM ℝ q, ← SeparationQuotient.mk_sub]
      simpa using
        (SeparationQuotient.inner_mk_mk g
          (SeparationQuotient.outCLM ℝ V q - x))
    have hinner :
        ((inner ℝ (SeparationQuotient.mk g) (q - SeparationQuotient.mk x) : ℝ) :
            WithTop ℝ) =
          (inner ℝ g (SeparationQuotient.outCLM ℝ V q - x) : WithTop ℝ) := by
      exact_mod_cast hinner_real
    -- Evaluate the original affine minorant at the chosen quotient representative.
    simpa [hx_eq, hinner] using hminorant hq

/-- Helper for Lemma 3.13: a quotient-lifted subgradient pulls back along `outCLM`. -/
lemma memSubdifferential_of_memSubdifferential_comp_outCLM
    {f : V → WithTop ℝ} (hf : ClosedConvexFunction f) {x : V}
    {g : SeparationQuotient V}
    (hg : g ∈
      subdifferential
        (fun q : SeparationQuotient V ↦ f (SeparationQuotient.outCLM ℝ V q))
        (SeparationQuotient.mk x)) :
    SeparationQuotient.outCLM ℝ V g ∈ ∂ f(x) := by
  rw [mem_subdifferential_iff] at hg ⊢
  rcases hg with ⟨hxq, hminorant⟩
  have hx_eq :
      f (SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk x)) = f x :=
    closedConvexFunction_eq_of_separationQuotient_eq
      hf (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk x))
  have hx : x ∈ dom f := by
    simpa [hx_eq] using hxq
  refine ⟨hx, ?_⟩
  intro y hy
  have hyq : SeparationQuotient.mk y ∈
      dom (fun q : SeparationQuotient V ↦ f (SeparationQuotient.outCLM ℝ V q)) := by
    have hy_eq :
        f (SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk y)) = f y :=
      closedConvexFunction_eq_of_separationQuotient_eq
        hf (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk y))
    simpa [hy_eq] using hy
  have hinner_real :
      inner ℝ g (SeparationQuotient.mk y - SeparationQuotient.mk x) =
        inner ℝ (SeparationQuotient.outCLM ℝ V g) (y - x) := by
    rw [← SeparationQuotient.mk_outCLM ℝ g, ← SeparationQuotient.mk_sub]
    simpa using
      (SeparationQuotient.inner_mk_mk
        (SeparationQuotient.outCLM ℝ V g) (y - x))
  have hinner :
      ((inner ℝ g (SeparationQuotient.mk y - SeparationQuotient.mk x) : ℝ) :
          WithTop ℝ) =
        (inner ℝ (SeparationQuotient.outCLM ℝ V g) (y - x) : WithTop ℝ) := by
    exact_mod_cast hinner_real
  have hy_eq :
      f (SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk y)) = f y :=
    closedConvexFunction_eq_of_separationQuotient_eq
      hf (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk y))
  -- Test the quotient inequality on the concrete point `mk y`.
  simpa [hx_eq, hy_eq, hinner] using
    (hminorant (y := SeparationQuotient.mk y) hyq)

/-- Helper for Lemma 3.13: quotienting a slice subdifferential gives exactly the subdifferential
of the quotient-lifted slice. -/
lemma sliceSubdifferentialImage_mk_eq_quotientLiftSubdifferential
    {φ : V → ι → WithTop ℝ} (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (i : ι) :
    SeparationQuotient.mk '' (∂ (fun y ↦ φ y i)(x) : Set V) =
      (subdifferential
        (fun q : SeparationQuotient V ↦ φ (SeparationQuotient.outCLM ℝ V q) i)
        (SeparationQuotient.mk x) : Set (SeparationQuotient V)) := by
  ext gbar
  constructor
  · rintro ⟨g, hg, rfl⟩
    -- Push the original slice subgradient forward through the quotient map.
    simpa using
      (memSubdifferential_comp_outCLM_of_memSubdifferential (hf := hφ i) hg)
  · intro hgbar
    refine ⟨SeparationQuotient.outCLM ℝ V gbar, ?_, ?_⟩
    · -- Pull the quotient slice subgradient back along the chosen section.
      exact memSubdifferential_of_memSubdifferential_comp_outCLM
        (hf := hφ i) (x := x) (g := gbar) hgbar
    · simpa using (SeparationQuotient.mk_outCLM ℝ gbar).symm

/-- Helper for Lemma 3.13: support values on the quotient image agree with the original support
values when the direction is projected by `SeparationQuotient.mk`. -/
lemma supportFunction_image_separationQuotient_eq
    {Q : Set V} {p : V} :
    supportFunction (SeparationQuotient.mk '' Q) (SeparationQuotient.mk p) =
      supportFunction Q p := by
  rw [supportFunction_apply, supportFunction_apply]
  have himage :
      ((fun q : SeparationQuotient V ↦
          (((inner ℝ q (SeparationQuotient.mk p) : ℝ)) : EReal)) ''
        (SeparationQuotient.mk '' Q)) =
        ((fun q : V ↦ (((inner ℝ q p : ℝ)) : EReal)) '' Q) := by
    ext a
    constructor
    · rintro ⟨qbar, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨q, hq, ?_⟩
      exact congrArg (fun r : ℝ ↦ (r : EReal))
        (SeparationQuotient.inner_mk_mk q p)
    · rintro ⟨q, hq, rfl⟩
      refine ⟨SeparationQuotient.mk q, ⟨q, hq, rfl⟩, ?_⟩
      exact congrArg (fun r : ℝ ↦ (r : EReal))
        (SeparationQuotient.inner_mk_mk q p).symm
  rw [himage]

/-- Helper for Lemma 3.13: the active subdifferential generator is stable under adding a
zero-norm vector. -/
lemma mem_activeSubdifferentialGenerator_add_zeroNorm
    {φ : V → ι → WithTop ℝ} {x g k : V}
    (hg :
      g ∈ {g | ∃ i : ι,
        i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
          g ∈ ∂ (fun y ↦ φ y i)(x)})
    (hk : ‖k‖ = 0) :
    g + k ∈ {g | ∃ i : ι,
      i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
        g ∈ ∂ (fun y ↦ φ y i)(x)} := by
  rcases hg with ⟨i, hi, hgi⟩
  refine ⟨i, hi, ?_⟩
  -- Zero-norm shifts preserve slice subdifferential membership at the same base point.
  exact (memSubdifferential_iff_add_zeroNorm
    (f := fun y ↦ φ y i) (x := x) (g := g) (k := k) hk).mp hgi

/-- Helper for Lemma 3.13: the convex hull of a zero-norm-saturated set is still stable under
adding a zero-norm vector. -/
lemma mem_convexHull_add_zeroNorm_of_saturated
    {Q : Set V}
    (hQ : ∀ ⦃g k : V⦄, g ∈ Q → ‖k‖ = 0 → g + k ∈ Q)
    {g k : V} (hg : g ∈ convexHull ℝ Q) (hk : ‖k‖ = 0) :
    g + k ∈ convexHull ℝ Q := by
  rcases (mem_convexHull_iff_exists_fintype.mp hg) with
    ⟨ι', _, w, z, hw₀, hw₁, hz, rfl⟩
  -- Translate every point in the convex combination by the same zero-norm vector.
  refine mem_convexHull_of_exists_fintype w (fun i ↦ z i + k) hw₀ hw₁ ?_ ?_
  · intro i
    exact hQ (hz i) hk
  · calc
      ∑ i, w i • (z i + k)
          = ∑ i, (w i • z i + w i • k) := by
              simp [smul_add]
      _ = (∑ i, w i • z i) + ∑ i, w i • k := by
            rw [Finset.sum_add_distrib]
      _ = (∑ i, w i • z i) + (∑ i, w i) • k := by
            rw [Finset.sum_smul]
      _ = (∑ i, w i • z i) + k := by simp [hw₁]

/-- Helper for Lemma 3.13: the separation-quotient projection is a proper map. -/
lemma isProperMap_separationQuotient_mk :
    IsProperMap (SeparationQuotient.mk : V → SeparationQuotient V) := by
  classical
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨SeparationQuotient.continuous_mk, SeparationQuotient.isClosedMap_mk, ?_⟩
  intro q
  refine isCompact_of_finite_subcover ?_
  intro ι U hU hcover
  rcases SeparationQuotient.surjective_mk q with ⟨x, rfl⟩
  have hx_cover :
      x ∈ ⋃ i, U i := by
    exact hcover (by simp)
  rcases Set.mem_iUnion.mp hx_cover with ⟨i, hxi⟩
  refine ⟨{i}, ?_⟩
  intro y hy
  have hxy :
      Inseparable y x := by
    apply (SeparationQuotient.mk_eq_mk).mp
    simpa using hy
  have hyi : y ∈ U i :=
    ((hxy.mem_open_iff (hU i)).2 hxi)
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨by simp, hyi⟩⟩

/-- Helper for Lemma 3.13: quotienting the seminormed ambient restores the normed slice
regularity package. -/
lemma sliceSubdifferentialRegularity_viaSeparationQuotient
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) (i : ι) :
    (∂ (fun y ↦ φ y i)(x)).Nonempty ∧
      IsCompact (∂ (fun y ↦ φ y i)(x) : Set V) := by
  let ψ : SeparationQuotient V → WithTop ℝ :=
    fun q ↦ φ (SeparationQuotient.outCLM ℝ V q) i
  have hψ : ClosedConvexFunction ψ := by
    -- Pull the slice to the quotient ambient, where the normed regularity API is available.
    simpa [ψ, Function.comp] using
      (hφ i).compContinuousLinearMap (SeparationQuotient.outCLM ℝ V)
  have hslice_int :
      x ∈ interior (dom (fun y ↦ φ y i)) :=
    by
      have hinterior :
          interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ)) =
            ⋂ j : ι, interior (dom (fun y ↦ φ y j)) :=
        interior_dom_pointwiseSupremumOn_univ
      rw [hinterior] at hx
      rw [Set.mem_iInter] at hx
      exact hx i
  have hxq_int : SeparationQuotient.mk x ∈ interior (dom ψ) := by
    let U : Set V := interior (dom (fun y ↦ φ y i))
    have hU_open : IsOpen U := isOpen_interior
    have hxU : x ∈ U := hslice_int
    have himage_mem : SeparationQuotient.mk x ∈ SeparationQuotient.mk '' U := by
      exact ⟨x, hxU, rfl⟩
    have himage_subset : SeparationQuotient.mk '' U ⊆ dom ψ := by
      intro q hq
      rcases hq with ⟨y, hyU, rfl⟩
      have hy : y ∈ dom (fun z ↦ φ z i) := interior_subset hyU
      have hy_eq :
          ψ (SeparationQuotient.mk y) = φ y i :=
        closedConvexFunction_eq_of_separationQuotient_eq
          (hφ i) (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk y))
      simpa [hy_eq]
        using hy
    -- The quotient image of an open slice neighborhood is open and still lies in the quotient
    -- effective domain.
    refine mem_interior_iff_mem_nhds.mpr ?_
    exact Filter.mem_of_superset
      (IsOpen.mem_nhds (SeparationQuotient.isOpenMap_mk U hU_open) himage_mem)
      himage_subset
  let Qψ : Set (SeparationQuotient V) :=
    subdifferential ψ (SeparationQuotient.mk x)
  have hq_regular :
      Qψ.Nonempty ∧ Bornology.IsBounded Qψ :=
    subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
      hψ.convexOn_withTopRealPart hxq_int
  have hq_closed :
      IsClosed Qψ := by
    let H : dom ψ → Set (SeparationQuotient V) := fun y ↦
      {g : SeparationQuotient V |
        withTopRealPart ψ (SeparationQuotient.mk x) +
            inner ℝ g (y.1 - SeparationQuotient.mk x) ≤
          withTopRealPart ψ y}
    have hclosedH : ∀ y : dom ψ, IsClosed (H y) := by
      intro y
      refine isClosed_le ?_ continuous_const
      have hcont :
          Continuous fun g : SeparationQuotient V ↦
            withTopRealPart ψ (SeparationQuotient.mk x) +
              inner ℝ g (y.1 - SeparationQuotient.mk x) := by
        exact continuous_const.add (continuous_id.inner continuous_const)
      simpa [H] using hcont
    have hrepr : Qψ = ⋂ y : dom ψ, H y := by
      ext g
      rw [mem_subdifferential_iff]
      constructor
      · rintro ⟨hxψ, hminorant⟩
        rw [Set.mem_iInter]
        intro y
        have hineq :
            ψ y.1 ≥ ψ (SeparationQuotient.mk x) +
              (inner ℝ g (y.1 - SeparationQuotient.mk x) : WithTop ℝ) :=
          hminorant y.2
        rw [← coe_withTopRealPart y.2, ← coe_withTopRealPart hxψ] at hineq
        exact_mod_cast hineq
      · intro hg
        refine ⟨interior_subset hxq_int, ?_⟩
        intro y hy
        have hineq :
            withTopRealPart ψ (SeparationQuotient.mk x) +
                inner ℝ g (y - SeparationQuotient.mk x) ≤
              withTopRealPart ψ y := by
          simpa [H] using (Set.mem_iInter.mp hg ⟨y, hy⟩)
        rw [← coe_withTopRealPart (interior_subset hxq_int), ← coe_withTopRealPart hy]
        exact_mod_cast hineq
    rw [hrepr]
    exact isClosed_iInter hclosedH
  have hq_compact :
      IsCompact Qψ :=
    Metric.isCompact_of_isClosed_isBounded hq_closed hq_regular.2
  have hpreimage :
      (∂ (fun y ↦ φ y i)(x) : Set V) =
        SeparationQuotient.mk ⁻¹' Qψ := by
    ext g
    constructor
    · intro hg
      -- Push each original slice subgradient to the quotient slice subdifferential.
      simpa [ψ, Qψ] using
        (memSubdifferential_comp_outCLM_of_memSubdifferential (hf := hφ i) hg)
    · intro hg
      have hrep :
          SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk g) ∈
            ∂ (fun y ↦ φ y i)(x) := by
        -- Pull the quotient slice subgradient back to the original ambient.
        exact memSubdifferential_of_memSubdifferential_comp_outCLM
          (hf := hφ i) (x := x) (g := SeparationQuotient.mk g)
          (by simpa [ψ, Qψ] using hg)
      have hzero :
          ‖g - SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk g)‖ = 0 := by
        have hInsep :
            Inseparable g (SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk g)) := by
          apply (SeparationQuotient.mk_eq_mk).mp
          simpa using (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk g)).symm
        rw [Metric.inseparable_iff, dist_eq_norm] at hInsep
        simpa [sub_eq_add_neg] using hInsep
      have hshift :
          SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk g) +
              (g - SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk g)) ∈
            ∂ (fun y ↦ φ y i)(x) :=
        (memSubdifferential_iff_add_zeroNorm
          (f := fun y ↦ φ y i) (x := x)
          (g := SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk g))
          (k := g - SeparationQuotient.outCLM ℝ V (SeparationQuotient.mk g))
          hzero).mp hrep
      simpa [sub_eq_add_neg, add_assoc] using hshift
  refine ⟨?_, ?_⟩
  · rcases hq_regular.1 with ⟨q, hq⟩
    -- A quotient slice subgradient produces one original slice subgradient by the section map.
    exact ⟨SeparationQuotient.outCLM ℝ V q,
      memSubdifferential_of_memSubdifferential_comp_outCLM
        (hf := hφ i) (x := x) (g := q) hq⟩
  · -- Properness of `mk` descends compactness of the quotient slice subdifferential.
    have hprecompact :
        IsCompact (SeparationQuotient.mk ⁻¹' Qψ) :=
      isProperMap_separationQuotient_mk.isCompact_preimage hq_compact
    simpa [hpreimage] using hprecompact

/-- Helper for Lemma 3.13: constraining the subgradient inequality to `dom f` does not change the
subdifferential. -/
lemma constrainedSubdifferential_dom_eq_subdifferential
    {f : V → WithTop ℝ} {x : V} :
    ∂[dom f] f(x) = ∂ f(x) := by
  ext g
  -- Both owners record the same affine minorant condition on the effective domain of `f`.
  rw [mem_constrainedSubdifferential_iff, mem_subdifferential_iff, IsSubgradientAt]
  constructor
  · rintro ⟨hx, -, hminorant⟩
    exact ⟨hx, hminorant⟩
  · rintro ⟨hx, hminorant⟩
    exact ⟨hx, hx, hminorant⟩

/-- Helper for Lemma 3.13: a whole-space subgradient restricts to any smaller feasible set inside
the effective domain. -/
lemma mem_constrainedSubdifferential_of_mem_subdifferential
    {Q : Set V} {f : V → WithTop ℝ} {x g : V}
    (hg : g ∈ ∂ f(x)) (hxQ : x ∈ Q) (hQ : Q ⊆ dom f) :
    g ∈ ∂[Q] f(x) := by
  -- Restrict the global affine minorant to the smaller feasible set `Q`.
  rcases (mem_subdifferential_iff.mp hg) with ⟨hxDom, hminorant⟩
  exact mem_constrainedSubdifferential_iff.mpr
    ⟨hxQ, hQ hxQ, fun y hyQ ↦ hminorant (hQ hyQ)⟩

/-- Helper for Lemma 3.13: an interior point of the finite `Set.univ` supremum domain lies in the
interior domain of every slice. -/
lemma mem_interior_dom_slice_of_mem_interior_dom_pointwiseSupremumOn_univ
    [Finite ι] [Nonempty ι] {φ : V → ι → WithTop ℝ} {x : V}
    (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) (i : ι) :
    x ∈ interior (dom (fun y ↦ φ y i)) := by
  -- Rewrite the common interior-domain statement and project to the `i`-th slice.
  have hinterior :
      interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ)) =
        ⋂ j : ι, interior (dom (fun y ↦ φ y j)) :=
    interior_dom_pointwiseSupremumOn_univ
  rw [hinterior] at hx
  rw [Set.mem_iInter] at hx
  exact hx i

/-- Helper for Lemma 3.13: at any finite base point, the whole-space subdifferential is closed in
the subgradient variable. -/
lemma isClosedSubdifferentialAt
    {f : V → WithTop ℝ} {x : V} (hx : x ∈ dom f) :
    IsClosed (∂ f(x) : Set V) := by
  let H : dom f → Set V := fun y ↦
    {g : V | withTopRealPart f x + inner ℝ g (y.1 - x) ≤ withTopRealPart f y}
  have hclosedH : ∀ y : dom f, IsClosed (H y) := by
    intro y
    refine isClosed_le ?_ continuous_const
    -- Each support inequality cuts out a closed affine half-space in the subgradient variable.
    have hcont : Continuous fun g : V ↦ withTopRealPart f x + inner ℝ g (y.1 - x) := by
      continuity
    simpa [H] using hcont
  have hrepr : (∂ f(x) : Set V) = ⋂ y : dom f, H y := by
    ext g
    rw [mem_subdifferential_iff]
    constructor
    · rintro ⟨hx', hminorant⟩
      rw [Set.mem_iInter]
      intro y
      have hineq :
          f y.1 ≥ f x + (inner ℝ g (y.1 - x) : WithTop ℝ) :=
        hminorant y.2
      rw [← coe_withTopRealPart y.2, ← coe_withTopRealPart hx] at hineq
      exact_mod_cast hineq
    · intro hg
      refine ⟨hx, ?_⟩
      intro y hy
      have hineq : withTopRealPart f x + inner ℝ g (y - x) ≤ withTopRealPart f y := by
        simpa [H] using (Set.mem_iInter.mp hg ⟨y, hy⟩)
      -- Move back from the finite real representative to the original `WithTop ℝ` values.
      rw [← coe_withTopRealPart hx, ← coe_withTopRealPart hy]
      exact_mod_cast hineq
  rw [hrepr]
  exact isClosed_iInter hclosedH

/-- Helper for Lemma 3.13: a nonempty finite `Set.univ` supremum always has at least one active
index at every base point. -/
lemma activePointwiseSupremumOnIndices_univ_nonempty
    [Finite ι] [Nonempty ι] {φ : V → ι → WithTop ℝ} (x : V) :
    (activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x).Nonempty := by
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Choose an index attaining the finite supremum value at `x`.
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (φ x)
  refine ⟨i, ?_⟩
  rw [mem_activePointwiseSupremumOnIndices_univ_iff, pointwiseSupremumOn_univ_eq_sup']
  exact hi.symm

/-- Helper for Lemma 3.13: a subgradient pairing is bounded above by any realized right secant
slope limit along the same direction. -/
lemma subgradientPairing_le_directionalSlopeLimit
    {f : V → WithTop ℝ} {x g p : V} {d : ℝ}
    (hg : g ∈ ∂ f(x))
    (hdom : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f)
    (hlim :
      Filter.Tendsto
        (fun α : ℝ ↦
          (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
        (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    inner ℝ g p ≤ d := by
  let q : ℝ → ℝ := fun α ↦
    (withTopRealPart f (x + α • p) - withTopRealPart f x) / α
  have hxdom : x ∈ dom f := (mem_subdifferential_iff.mp hg).1
  have hq_mem :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), q α ∈ Set.Ici (inner ℝ g p) := by
    -- Convert the affine minorant at `x + α • p` into a secant-quotient inequality.
    filter_upwards [hdom, self_mem_nhdsWithin] with α hαdom hαmem
    have hα : 0 < α := hαmem
    have hineq :
        f (x + α • p) ≥ f x + (inner ℝ g ((x + α • p) - x) : WithTop ℝ) :=
      (mem_subdifferential_iff.mp hg).2 hαdom
    rw [← coe_withTopRealPart hαdom, ← coe_withTopRealPart hxdom] at hineq
    have hreal :
        withTopRealPart f (x + α • p) ≥
          withTopRealPart f x + inner ℝ g ((x + α • p) - x) := by
      exact_mod_cast hineq
    have hinner :
        inner ℝ g ((x + α • p) - x) = α * inner ℝ g p := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (inner_smul_right g p α)
    rw [hinner] at hreal
    have hscaled :
        α * inner ℝ g p ≤ withTopRealPart f (x + α • p) - withTopRealPart f x := by
      linarith
    have hquot : inner ℝ g p ≤ q α := by
      exact (le_div_iff₀ hα).2 (by simpa [q, mul_comm] using hscaled)
    exact hquot
  have hd_mem : d ∈ Set.Ici (inner ℝ g p) :=
    IsClosed.mem_of_tendsto isClosed_Ici hlim hq_mem
  simpa using hd_mem

/-- Helper for Lemma 3.13: the convex hull of the active slice subdifferentials is contained in
the subdifferential of the finite `Set.univ` pointwise supremum. -/
lemma active_hull_subset_subdifferential_pointwiseSupremumOn_univ
    [Finite ι] [Nonempty ι] {φ : V → ι → WithTop ℝ}
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    convexHull ℝ
      {g | ∃ i : ι,
          i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
            g ∈ ∂ (fun y ↦ φ y i)(x)} ⊆
      ∂ (pointwiseSupremumOn (Set.univ : Set ι) φ)(x) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let f : V → WithTop ℝ := pointwiseSupremumOn (Set.univ : Set ι) φ
  have hxDom : x ∈ dom f := interior_subset hx
  have hxEff : x ∈ pointwiseSupremumOnEffectiveDomain (dom f) (Set.univ : Set ι) φ := by
    -- The owner effective domain over `dom f` is exactly `dom f` at the base point.
    exact ⟨hxDom, hxDom⟩
  have hpre :
      {g | ∃ i : ι,
          i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
            g ∈ ∂ (fun y ↦ φ y i)(x)} ⊆
        ⋃ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x,
          ∂[dom f] (fun y ↦ φ y i)(x) := by
    intro g hg
    rcases hg with ⟨i, hi, hgi⟩
    have hdom_subset : dom f ⊆ dom (fun y ↦ φ y i) := by
      intro y hy
      change φ y i < ⊤
      have hle : φ y i ≤ f y := by
        rw [show f y = pointwiseSupremumOn (Set.univ : Set ι) φ y by rfl, pointwiseSupremumOn_apply]
        exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ ⟨i, by simp, rfl⟩
      exact lt_of_le_of_lt hle hy
    have hgi' : g ∈ ∂[dom f] (fun y ↦ φ y i)(x) := by
      -- Each whole-space slice subgradient is valid on the smaller common domain.
      exact mem_constrainedSubdifferential_of_mem_subdifferential hgi hxDom hdom_subset
    change g ∈ ⋃ j ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x,
        ∂[dom f] (fun y ↦ φ y j)(x)
    refine Set.mem_iUnion.2 ?_
    exact ⟨i, Set.mem_iUnion.2 ⟨hi, hgi'⟩⟩
  have howner :
      convexHull ℝ
          (⋃ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x,
            ∂[dom f] (fun y ↦ φ y i)(x)) ⊆
        ∂ f(x) := by
    -- This is exactly the owner inclusion on the common feasible set `dom f`.
    have howner' :
        convexHull ℝ
            (⋃ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x,
              ∂[dom f] (fun y ↦ φ y i)(x)) ⊆
          ∂[pointwiseSupremumOnEffectiveDomain (dom f) (Set.univ : Set ι) φ]
            (pointwiseSupremumOn (Set.univ : Set ι) φ) (x) :=
      convexHull_activePointwiseSupremumOnSubdifferentials_subset hxEff
    simpa [f, pointwiseSupremumOnEffectiveDomain, constrainedSubdifferential_dom_eq_subdifferential]
      using
        howner'
  exact Set.Subset.trans (convexHull_mono hpre) howner

section NormedSliceRegularity

variable {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Helper for Lemma 3.13: on the normed owner layer, each slice subdifferential is nonempty and
bounded at a common interior point of the finite `Set.univ` supremum. -/
lemma sliceSubdifferentialRegularityOfMemInteriorDomPointwiseSupremumOnUnivOfNormed
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ W] {φ : W → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : W} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) (i : ι) :
    (∂ (fun y ↦ φ y i)(x)).Nonempty ∧
      Bornology.IsBounded (∂ (fun y ↦ φ y i)(x) : Set W) := by
  have hslice_int :
      x ∈ interior (dom (fun y ↦ φ y i)) :=
    mem_interior_dom_slice_of_mem_interior_dom_pointwiseSupremumOn_univ
      (φ := φ) hx i
  -- On the genuine normed owner layer, the standard interior-point regularity theorem applies
  -- directly to the chosen slice.
  exact
    subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
      (hφ i).convexOn_withTopRealPart hslice_int

/-- Helper for Lemma 3.13: on the normed owner layer, each slice subdifferential is compact at a
common interior point of the finite `Set.univ` supremum. -/
lemma sliceSubdifferentialIsCompactOfMemInteriorDomPointwiseSupremumOnUnivOfNormed
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ W] {φ : W → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : W} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) (i : ι) :
    IsCompact (∂ (fun y ↦ φ y i)(x) : Set W) := by
  have hslice_int :
      x ∈ interior (dom (fun y ↦ φ y i)) :=
    mem_interior_dom_slice_of_mem_interior_dom_pointwiseSupremumOn_univ
      (φ := φ) hx i
  have hslice_closed :
      IsClosed (∂ (fun y ↦ φ y i)(x) : Set W) :=
    isClosedSubdifferentialAt (f := fun y ↦ φ y i) (x := x) (interior_subset hslice_int)
  have hslice_bounded :
      Bornology.IsBounded (∂ (fun y ↦ φ y i)(x) : Set W) :=
    (sliceSubdifferentialRegularityOfMemInteriorDomPointwiseSupremumOnUnivOfNormed
      (hφ := hφ) hx i).2
  -- Finite-dimensional closed bounded subsets are compact, so the normed slice regularity package
  -- immediately upgrades to compactness.
  exact Metric.isCompact_of_isClosed_isBounded hslice_closed hslice_bounded

end NormedSliceRegularity

/-- Helper for Lemma 3.13: every slice has a nonempty subdifferential at an interior point of the
finite `Set.univ` pointwise supremum domain. -/
lemma sliceSubdifferential_nonempty_of_mem_interior_dom_pointwiseSupremumOn_univ
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) (i : ι) :
    (∂ (fun y ↦ φ y i)(x)).Nonempty := by
  -- Route correction: instead of forcing the normed owner theorem on `V`, move only the slice
  -- regularity step to `SeparationQuotient V` and pull one subgradient back along `outCLM`.
  exact (sliceSubdifferentialRegularity_viaSeparationQuotient
    (hφ := hφ) hx i).1

/-- Helper for Lemma 3.13: the active-slice generator set is nonempty at every interior base
point of the finite `Set.univ` pointwise supremum. -/
lemma activeSubdifferentialGenerator_nonempty
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    {g | ∃ i : ι,
        i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
          g ∈ ∂ (fun y ↦ φ y i)(x)}.Nonempty := by
  -- Choose an active index at `x`, then choose one slice subgradient at that same interior point.
  rcases activePointwiseSupremumOnIndices_univ_nonempty (φ := φ) x with ⟨i, hi⟩
  rcases
      sliceSubdifferential_nonempty_of_mem_interior_dom_pointwiseSupremumOn_univ
        (hφ := hφ) hx i with
    ⟨g, hg⟩
  exact ⟨g, ⟨i, hi, hg⟩⟩

/-- Helper for Lemma 3.13: the convex hull of the active-slice generator set is nonempty. -/
lemma activeSubdifferentialHull_nonempty
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    (convexHull ℝ
      {g | ∃ i : ι,
          i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
            g ∈ ∂ (fun y ↦ φ y i)(x)}).Nonempty := by
  -- Lift one active slice subgradient into the convex hull by the canonical hull inclusion.
  rcases activeSubdifferentialGenerator_nonempty (hφ := hφ) hx with ⟨g, hg⟩
  exact ⟨g, subset_convexHull ℝ _ hg⟩

/-- Helper for Lemma 3.13: the active-slice generator set is the union of the active slice
subdifferentials. -/
lemma activeSubdifferentialGenerator_eq_iUnion
    {φ : V → ι → WithTop ℝ} {x : V} :
    {g | ∃ i : ι,
        i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
          g ∈ ∂ (fun y ↦ φ y i)(x)} =
      ⋃ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x,
        (∂ (fun y ↦ φ y i)(x) : Set V) := by
  ext g
  constructor
  · rintro ⟨i, hi, hg⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hg⟩⟩
  · intro hg
    rcases Set.mem_iUnion.1 hg with ⟨i, hg⟩
    rcases Set.mem_iUnion.1 hg with ⟨hi, hgi⟩
    exact ⟨i, hi, hgi⟩

/-- Helper for Lemma 3.13: each slice subdifferential at the common interior base point is closed.
-/
lemma sliceSubdifferential_isClosed_of_mem_interior_dom_pointwiseSupremumOn_univ
    [Finite ι] [Nonempty ι] {φ : V → ι → WithTop ℝ}
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) (i : ι) :
    IsClosed (∂ (fun y ↦ φ y i)(x) : Set V) := by
  have hslice_int :
      x ∈ interior (dom (fun y ↦ φ y i)) :=
    mem_interior_dom_slice_of_mem_interior_dom_pointwiseSupremumOn_univ
      (φ := φ) hx i
  -- Project to the slice interior domain, then apply the owner closedness theorem.
  exact isClosedSubdifferentialAt (f := fun y ↦ φ y i) (x := x) (interior_subset hslice_int)

/-- Helper for Lemma 3.13: each slice subdifferential at a common interior point is compact. -/
lemma sliceSubdifferential_isCompact_of_mem_interior_dom_pointwiseSupremumOn_univ
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) (i : ι) :
    IsCompact (∂ (fun y ↦ φ y i)(x) : Set V) := by
  -- The same quotient package also returns compactness, now that the original slice is identified
  -- as the proper preimage of the compact quotient slice subdifferential.
  exact (sliceSubdifferentialRegularity_viaSeparationQuotient
    (hφ := hφ) hx i).2

/-- Helper for Lemma 3.13: the active-slice generator set is compact at every common interior
point. -/
lemma activeSubdifferentialGenerator_isCompact
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    IsCompact
      {g | ∃ i : ι,
          i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
            g ∈ ∂ (fun y ↦ φ y i)(x)} := by
  rw [activeSubdifferentialGenerator_eq_iUnion]
  -- Rewrite the generator set as a finite iterated union of compact slice subdifferentials.
  refine isCompact_iUnion fun i ↦ ?_
  refine isCompact_iUnion fun _ ↦ ?_
  exact sliceSubdifferential_isCompact_of_mem_interior_dom_pointwiseSupremumOn_univ hφ hx i

/-- Helper for Lemma 3.13: an index that is inactive at the base point has strictly smaller finite
value than the finite `Set.univ` supremum there. -/
lemma inactiveSlice_lt_pointwiseSupremumOn_univ_realPart_at_base
    [Finite ι] [Nonempty ι] {φ : V → ι → WithTop ℝ} {x : V} {i : ι}
    (hx : x ∈ dom (pointwiseSupremumOn (Set.univ : Set ι) φ))
    (hxi : x ∈ dom (fun y ↦ φ y i))
    (hi : i ∉ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x) :
    withTopRealPart (fun y ↦ φ y i) x <
      withTopRealPart (pointwiseSupremumOn (Set.univ : Set ι) φ) x := by
  let f : V → WithTop ℝ := pointwiseSupremumOn (Set.univ : Set ι) φ
  have hle : φ x i ≤ f x := by
    rw [show f x = pointwiseSupremumOn (Set.univ : Set ι) φ x by rfl, pointwiseSupremumOn_apply]
    exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ ⟨i, by simp, rfl⟩
  have hne : φ x i ≠ f x := by
    intro heq
    exact hi ((mem_activePointwiseSupremumOnIndices_univ_iff).2 heq)
  have hlt : φ x i < f x := lt_of_le_of_ne hle hne
  rw [← coe_withTopRealPart (f := fun y ↦ φ y i) hxi,
    ← coe_withTopRealPart (f := f) hx] at hlt
  exact_mod_cast hlt

/-- Helper for Lemma 3.13: the quotient lift of the finite `Set.univ` pointwise supremum keeps
the quotient base point inside the interior of the effective domain. -/
lemma quotientLiftPointwiseSupremumOnUniv_memInteriorDom
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    SeparationQuotient.mk x ∈
      interior
        (dom
          (fun q : SeparationQuotient V ↦
            pointwiseSupremumOn (Set.univ : Set ι) φ
              (SeparationQuotient.outCLM ℝ V q))) := by
  let f : V → WithTop ℝ := pointwiseSupremumOn (Set.univ : Set ι) φ
  let qf : SeparationQuotient V → WithTop ℝ :=
    fun q ↦ f (SeparationQuotient.outCLM ℝ V q)
  have hf : ClosedConvexFunction f :=
    closedConvexFunction_pointwiseSupremumOn_univ hφ
  let U : Set V := interior (dom f)
  have hU_open : IsOpen U := isOpen_interior
  have hxU : x ∈ U := hx
  have himage_mem : SeparationQuotient.mk x ∈ SeparationQuotient.mk '' U := by
    exact ⟨x, hxU, rfl⟩
  have himage_subset : SeparationQuotient.mk '' U ⊆ dom qf := by
    intro q hq
    rcases hq with ⟨y, hyU, rfl⟩
    have hy : y ∈ dom f := interior_subset hyU
    have hy_eq :
        qf (SeparationQuotient.mk y) = f y :=
      closedConvexFunction_eq_of_separationQuotient_eq
        hf (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk y))
    simpa [qf, hy_eq] using hy
  -- Push the open interior-domain neighborhood through the open quotient map.
  refine mem_interior_iff_mem_nhds.mpr ?_
  exact Filter.mem_of_superset
    (IsOpen.mem_nhds (SeparationQuotient.isOpenMap_mk U hU_open) himage_mem)
    himage_subset

/-- Helper for Lemma 3.13: on the quotient slice, the finite directional derivative equals the
support value of the pushed-forward original slice subdifferential. -/
lemma quotientSliceDirectionalDerivativeReal_eq_supportFunctionImageSubdifferential
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} {i : ι}
    (hxqi :
      SeparationQuotient.mk x ∈
        interior
          (dom
            (fun q : SeparationQuotient V ↦
              φ (SeparationQuotient.outCLM ℝ V q) i)))
    (p : SeparationQuotient V) :
    ((fun q : SeparationQuotient V ↦ φ (SeparationQuotient.outCLM ℝ V q) i)′[hxqi] p) =
      supportFunction
        (SeparationQuotient.mk '' (∂ (fun y ↦ φ y i)(x) : Set V)) p := by
  let ψ : SeparationQuotient V → WithTop ℝ :=
    fun q ↦ φ (SeparationQuotient.outCLM ℝ V q) i
  have hψ : ClosedConvexFunction ψ := by
    -- Pull the original slice along the quotient section to reach the normed owner layer.
    simpa [ψ, Function.comp] using
      (hφ i).compContinuousLinearMap (SeparationQuotient.outCLM ℝ V)
  have hmax :
      IsGreatest
        ((fun g : SeparationQuotient V ↦ inner ℝ g p) ''
          subdifferential ψ (SeparationQuotient.mk x))
        (ψ′[hxqi] p) :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
      hψ.convexOn_withTopRealPart hxqi p
  -- Rewrite the quotient slice subdifferential back to the quotient image of the original slice.
  rw [supportFunction_apply, sliceSubdifferentialImage_mk_eq_quotientLiftSubdifferential (hφ := hφ)]
  symm
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro a ha
    rcases ha with ⟨g, hg, rfl⟩
    exact
      (show (((inner ℝ g p : ℝ) : EReal) ≤ (((ψ′[hxqi] p : ℝ) : EReal))) from by
        exact_mod_cast (hmax.2 ⟨g, hg, rfl⟩))
  · exact le_sSup (by
      rcases hmax.1 with ⟨g, hg, hgp⟩
      exact ⟨g, hg, by simpa using congrArg (fun r : ℝ ↦ (r : EReal)) hgp⟩)

/-- Helper for Lemma 3.13: the quotient lift of the finite `Set.univ` pointwise supremum is a
closed convex function on the normed quotient ambient. -/
lemma quotientLiftPointwiseSupremumOnUniv_closedConvex
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i)) :
    ClosedConvexFunction
      (fun q : SeparationQuotient V ↦
        pointwiseSupremumOn (Set.univ : Set ι) φ (SeparationQuotient.outCLM ℝ V q)) := by
  -- Pull the original finite-supremum owner through the quotient section.
  simpa [Function.comp] using
    (closedConvexFunction_pointwiseSupremumOn_univ hφ).compContinuousLinearMap
      (SeparationQuotient.outCLM ℝ V)

/-- Helper for Lemma 3.13: the quotient active hull is nonempty. -/
lemma quotientActiveHull_nonempty
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    (convexHull ℝ
      (SeparationQuotient.mk ''
        {g | ∃ i : ι,
            i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
              g ∈ ∂ (fun y ↦ φ y i)(x)})).Nonempty := by
  rcases activeSubdifferentialGenerator_nonempty (hφ := hφ) hx with ⟨g, hg⟩
  -- One active slice subgradient enters the quotient hull through the canonical hull inclusion.
  exact ⟨SeparationQuotient.mk g, subset_convexHull ℝ _ ⟨g, hg, rfl⟩⟩

/-- Helper for Lemma 3.13: every active quotient slice support value is bounded by the support
function of the quotient active hull. -/
lemma quotientActiveSliceSupport_le_supportFunctionActiveHull
    {φ : V → ι → WithTop ℝ} {x : V} {i : ι}
    (hi : i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x)
    (p : SeparationQuotient V) :
    supportFunction (SeparationQuotient.mk '' (∂ (fun y ↦ φ y i)(x) : Set V)) p ≤
      supportFunction
        (convexHull ℝ
        (SeparationQuotient.mk ''
          {g | ∃ j : ι,
              j ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                g ∈ ∂ (fun y ↦ φ y j)(x)})) p := by
  rw [supportFunction_apply, supportFunction_convexHull_eq, supportFunction_apply]
  -- Each active slice image is already contained in the quotient active generator image.
  refine sSup_le ?_
  rintro _ ⟨gbar, ⟨g, hg, rfl⟩, rfl⟩
  exact le_sSup ⟨SeparationQuotient.mk g, ⟨g, ⟨i, hi, hg⟩, rfl⟩, rfl⟩

/-- Helper for Lemma 3.13: the quotient active hull is bounded because the active generator image
is compact, and convex hulls preserve boundedness. -/
lemma quotientActiveHull_isBounded
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    Bornology.IsBounded
      (convexHull ℝ
        (SeparationQuotient.mk ''
          {g | ∃ i : ι,
              i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                g ∈ ∂ (fun y ↦ φ y i)(x)})) := by
  have hcompact_image :
      IsCompact
        (SeparationQuotient.mk ''
          {g | ∃ i : ι,
              i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                g ∈ ∂ (fun y ↦ φ y i)(x)}) :=
    (activeSubdifferentialGenerator_isCompact (hφ := hφ) hx).image
      SeparationQuotient.continuous_mk
  have hbounded_image :
      Bornology.IsBounded
        (SeparationQuotient.mk ''
          {g | ∃ i : ι,
              i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                g ∈ ∂ (fun y ↦ φ y i)(x)}) :=
    hcompact_image.isBounded
  -- Replace the quotient active hull by its generator image and use boundedness preservation.
  exact (isBounded_convexHull (s :=
    SeparationQuotient.mk ''
      {g | ∃ i : ι,
          i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
            g ∈ ∂ (fun y ↦ φ y i)(x)})).2 hbounded_image

/-- Helper for Lemma 3.13: the quotient lift of each slice keeps the quotient base point inside
the slice interior domain. -/
lemma quotientLiftSlice_memInteriorDom
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) (i : ι) :
    SeparationQuotient.mk x ∈
      interior
        (dom
          (fun q : SeparationQuotient V ↦
            φ (SeparationQuotient.outCLM ℝ V q) i)) := by
  let ψ : SeparationQuotient V → WithTop ℝ :=
    fun q ↦ φ (SeparationQuotient.outCLM ℝ V q) i
  have hslice_int :
      x ∈ interior (dom (fun y ↦ φ y i)) :=
    mem_interior_dom_slice_of_mem_interior_dom_pointwiseSupremumOn_univ
      (φ := φ) hx i
  let U : Set V := interior (dom (fun y ↦ φ y i))
  have hU_open : IsOpen U := isOpen_interior
  have hxU : x ∈ U := hslice_int
  have himage_mem : SeparationQuotient.mk x ∈ SeparationQuotient.mk '' U := by
    exact ⟨x, hxU, rfl⟩
  have himage_subset : SeparationQuotient.mk '' U ⊆ dom ψ := by
    intro q hq
    rcases hq with ⟨y, hyU, rfl⟩
    have hy : y ∈ dom (fun z ↦ φ z i) := interior_subset hyU
    have hy_eq :
        ψ (SeparationQuotient.mk y) = φ y i :=
      closedConvexFunction_eq_of_separationQuotient_eq
        (hφ i) (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk y))
    simpa [ψ, hy_eq] using hy
  -- Push the slice interior neighborhood through the open quotient map.
  refine mem_interior_iff_mem_nhds.mpr ?_
  exact Filter.mem_of_superset
    (IsOpen.mem_nhds (SeparationQuotient.isOpenMap_mk U hU_open) himage_mem)
    himage_subset

/-- Helper for Lemma 3.13: the quotient active hull is closed. -/
lemma quotientActiveHull_isClosed
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    IsClosed
      (convexHull ℝ
        (SeparationQuotient.mk ''
          {g | ∃ i : ι,
              i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                g ∈ ∂ (fun y ↦ φ y i)(x)})) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let G : Set V :=
    {g | ∃ i : ι,
        i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
          g ∈ ∂ (fun y ↦ φ y i)(x)}
  let A : Finset ι :=
    Finset.univ.filter fun i ↦ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x
  let K : ι → Set (SeparationQuotient V) := fun i ↦
    SeparationQuotient.mk '' (∂ (fun y ↦ φ y i)(x) : Set V)
  let U : Finset ι → Set (SeparationQuotient V) := fun s ↦ ⋃ i ∈ (s : Set ι), K i
  have hK_nonempty : ∀ i : ι, (K i).Nonempty := by
    intro i
    rcases
        sliceSubdifferential_nonempty_of_mem_interior_dom_pointwiseSupremumOn_univ
          (hφ := hφ) hx i with
      ⟨g, hg⟩
    exact ⟨SeparationQuotient.mk g, ⟨g, hg, rfl⟩⟩
  have hK_compact : ∀ i : ι, IsCompact (K i) := by
    intro i
    -- Each quotient slice image is compact because the original slice subdifferential is compact.
    simpa [K] using
      (sliceSubdifferential_isCompact_of_mem_interior_dom_pointwiseSupremumOn_univ
        (hφ := hφ) hx i).image SeparationQuotient.continuous_mk
  have hK_convex : ∀ i : ι, Convex ℝ (K i) := by
    intro i
    have hsub_convex :
        Convex ℝ (∂ (fun y ↦ φ y i)(x) : Set V) := by
      -- Whole-space slice subdifferentials are the constrained owner over the effective domain.
      simpa [constrainedSubdifferential_dom_eq_subdifferential] using
        (convex_constrainedSubdifferential
          (Q := dom (fun y ↦ φ y i)) (f := fun y ↦ φ y i) (x := x))
    -- The quotient map is linear, so it preserves convexity of the slice image.
    simpa [K] using hsub_convex.linear_image (SeparationQuotient.mkCLM ℝ V).toLinearMap
  have hcompactU : ∀ s : Finset ι, IsCompact (convexHull ℝ (U s)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        -- The convex hull of the empty union is empty, hence compact.
        simp [U]
    | @insert i s hi hs =>
        have hU_insert : U (insert i s) = K i ∪ U s := by
          ext q
          simp [U]
        by_cases hUs : (U s).Nonempty
        · -- Repackage the finite active family by adjoining one compact convex slice at a time.
          rw [hU_insert, convexHull_union (hK_nonempty i) hUs,
            convexHull_eq_self.mpr (hK_convex i)]
          exact isCompact_convexJoin (hK_compact i) hs
        · have hUs_empty : U s = ∅ := Set.not_nonempty_iff_eq_empty.mp hUs
          -- If the tail union is empty, the hull is just the current compact convex slice image.
          rw [hU_insert, hUs_empty, union_empty, convexHull_eq_self.mpr (hK_convex i)]
          exact hK_compact i
  have himage_eq : SeparationQuotient.mk '' G = U A := by
    ext q
    constructor
    · rintro ⟨g, ⟨i, hi, hg⟩, rfl⟩
      refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ?_⟩
      refine ⟨?_, ⟨g, hg, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    · intro hq
      rcases Set.mem_iUnion.1 hq with ⟨i, hq⟩
      rcases Set.mem_iUnion.1 hq with ⟨hiA, hq⟩
      rcases hq with ⟨g, hg, rfl⟩
      have hiA' : i ∈ A := hiA
      exact ⟨g, ⟨i, (Finset.mem_filter.mp hiA').2, hg⟩, rfl⟩
  have hcompact :
      IsCompact
        (convexHull ℝ
          (SeparationQuotient.mk ''
            {g | ∃ i : ι,
                i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                  g ∈ ∂ (fun y ↦ φ y i)(x)})) := by
    -- Replace the quotient active generator by the finite union of compact convex slice images.
    rw [himage_eq]
    exact hcompactU A
  exact hcompact.isClosed

/-- Helper for Lemma 3.13: the quotient owner for the finite `Set.univ` pointwise supremum. -/
abbrev quotientPointwiseSupremumOnUnivLift
    {φ : V → ι → WithTop ℝ} :
    SeparationQuotient V → WithTop ℝ :=
  fun q ↦
    pointwiseSupremumOn (Set.univ : Set ι) φ
      (SeparationQuotient.outCLM ℝ V q)

/-- Helper for Lemma 3.13: the quotient owner of the `i`-th slice. -/
abbrev quotientSliceLift
    {φ : V → ι → WithTop ℝ} (i : ι) :
    SeparationQuotient V → WithTop ℝ :=
  fun q ↦ φ (SeparationQuotient.outCLM ℝ V q) i

/-- Helper for Lemma 3.13: quotient interior membership for the lifted finite supremum forces
quotient interior membership for each lifted slice at the same base point. -/
lemma quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    {x : V}
    (hxq :
      SeparationQuotient.mk x ∈
        interior
          (dom
            (fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q))))
    (i : ι) :
    SeparationQuotient.mk x ∈
      interior
        (dom
          (fun q : SeparationQuotient V ↦
            φ (SeparationQuotient.outCLM ℝ V q) i)) := by
  -- Specialize the finite-interior formula to the quotient-lifted family.
  simpa using
    (mem_interior_dom_slice_of_mem_interior_dom_pointwiseSupremumOn_univ
      (φ := fun q : SeparationQuotient V ↦
        fun j : ι ↦ φ (SeparationQuotient.outCLM ℝ V q) j) hxq i)

/-- Helper for Lemma 3.13: the finite `sup'` of quotient slice secants converges to the matching
finite `sup'` of quotient slice directional derivatives. -/
lemma tendsto_activeSupQuotientSliceSecant
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V}
    (hxq :
      SeparationQuotient.mk x ∈
        interior
          (dom
            (fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q))))
    (A : Finset ι) (hA_nonempty : A.Nonempty) (p : SeparationQuotient V) :
    Filter.Tendsto
      (fun α : ℝ ↦
        A.sup' hA_nonempty (fun i ↦
          (withTopRealPart
              (fun q : SeparationQuotient V ↦
                φ (SeparationQuotient.outCLM ℝ V q) i)
              (SeparationQuotient.mk x + α • p) -
            withTopRealPart
              (fun q : SeparationQuotient V ↦
                φ (SeparationQuotient.outCLM ℝ V q) i)
              (SeparationQuotient.mk x)) / α))
      (𝓝[>] (0 : ℝ))
      (𝓝
        (A.sup' hA_nonempty fun i ↦
          convexDirectionalDerivativeReal
            (quotientSliceLift (φ := φ) i)
            (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
              (φ := φ) (x := x) hxq i) p)) := by
  -- Each slice secant converges to its directional derivative, so the finite `sup'` does too.
  refine Filter.Tendsto.finset_sup'_nhds_apply hA_nonempty ?_
  intro i hi
  have hψi :
      ClosedConvexFunction
        (fun q : SeparationQuotient V ↦
          φ (SeparationQuotient.outCLM ℝ V q) i) := by
    -- Pull the original slice to the quotient owner before using the directional-derivative API.
    simpa [Function.comp] using
      (hφ i).compContinuousLinearMap (SeparationQuotient.outCLM ℝ V)
  -- The one-dimensional secant limit is already available on the quotient slice.
  simpa using
    tendsto_directionalSecantQuotient_of_mem_interior hψi.convexOn_withTopRealPart
      (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
        (φ := φ) (x := x) hxq i) p

/-- Helper for Lemma 3.13: the finite `sup'` of active quotient slice directional derivatives is
bounded by the support function of the quotient active hull. -/
lemma activeSupQuotientSliceDirectionalDerivative_le_supportFunctionActiveHull
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V}
    (A : Finset ι)
    (hA :
      ∀ i ∈ A,
        i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x)
    (hA_nonempty : A.Nonempty)
    (hxq :
      SeparationQuotient.mk x ∈
        interior
          (dom
            (fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q))))
    (p : SeparationQuotient V) :
    ((A.sup' hA_nonempty fun i ↦
        (convexDirectionalDerivativeReal
          (quotientSliceLift (φ := φ) i)
          (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
            (φ := φ) (x := x) hxq i) p : ℝ)) : EReal) ≤
      supportFunction
        (convexHull ℝ
        (SeparationQuotient.mk ''
          {g | ∃ i : ι,
              i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                g ∈ ∂ (fun y ↦ φ y i)(x)})) p := by
  -- Compare each active slice support value to the common quotient active hull, then take `sup'`.
  refine Finset.sup'_le (f := fun i ↦
    ((convexDirectionalDerivativeReal
        (quotientSliceLift (φ := φ) i)
        (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
          (φ := φ) (x := x) hxq i) p : ℝ) : EReal)) hA_nonempty ?_
  intro i hi
  calc
    ((convexDirectionalDerivativeReal
        (quotientSliceLift (φ := φ) i)
        (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
          (φ := φ) (x := x) hxq i) p : ℝ) : EReal)
        =
          supportFunction
            (SeparationQuotient.mk '' (∂ (fun y ↦ φ y i)(x) : Set V)) p := by
              simpa using
                quotientSliceDirectionalDerivativeReal_eq_supportFunctionImageSubdifferential
                  (hφ := hφ) (x := x) (i := i)
                  (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
                    (φ := φ) (x := x) hxq i) p
    _ ≤
        supportFunction
          (convexHull ℝ
            (SeparationQuotient.mk ''
              {g | ∃ j : ι,
                  j ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                    g ∈ ∂ (fun y ↦ φ y j)(x)})) p := by
              exact
                quotientActiveSliceSupport_le_supportFunctionActiveHull
                  (φ := φ) (x := x) (i := i) (hA i hi) p

/-- Helper for Lemma 3.13: near `0+`, the quotient secant quotient of the lifted supremum is
dominated by the finite `sup'` of the active quotient slice secants. -/
lemma quotientPointwiseSupremumSecant_le_activeSupSecant_eventually
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V}
    (A : Finset ι)
    (hA :
      ∀ i : ι, i ∈ A ↔ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x)
    (hA_nonempty : A.Nonempty)
    (hxq :
      SeparationQuotient.mk x ∈
        interior
          (dom
            (fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q))))
    (p : SeparationQuotient V) :
    ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
      (withTopRealPart
          (fun q : SeparationQuotient V ↦
            pointwiseSupremumOn (Set.univ : Set ι) φ
              (SeparationQuotient.outCLM ℝ V q))
          (SeparationQuotient.mk x + α • p) -
        withTopRealPart
          (fun q : SeparationQuotient V ↦
            pointwiseSupremumOn (Set.univ : Set ι) φ
              (SeparationQuotient.outCLM ℝ V q))
          (SeparationQuotient.mk x)) / α
        ≤
          A.sup' hA_nonempty (fun i ↦
            (withTopRealPart
                (fun q : SeparationQuotient V ↦
                  φ (SeparationQuotient.outCLM ℝ V q) i)
                (SeparationQuotient.mk x + α • p) -
              withTopRealPart
                (fun q : SeparationQuotient V ↦
                  φ (SeparationQuotient.outCLM ℝ V q) i)
                (SeparationQuotient.mk x)) / α) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let xq : SeparationQuotient V := SeparationQuotient.mk x
  let qf : SeparationQuotient V → WithTop ℝ := quotientPointwiseSupremumOnUnivLift (φ := φ)
  let ψ : ι → SeparationQuotient V → WithTop ℝ := fun i ↦ quotientSliceLift (φ := φ) i
  let line : ℝ → SeparationQuotient V := fun α ↦ xq + α • p
  have hA_nonempty_secant : A.Nonempty := hA_nonempty
  obtain ⟨j0, hj0A⟩ := hA_nonempty
  have hj0_active : j0 ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x := (hA j0).1 hj0A
  have hline_cont : Continuous line := by
    -- The affine ray in the quotient ambient is continuous in the step size.
    simpa [line] using
      ((continuous_const : Continuous fun _ : ℝ ↦ xq).add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ p)))
  have hqf_base_val :
      qf xq = pointwiseSupremumOn (Set.univ : Set ι) φ x := by
    -- The quotient owner agrees with the original finite supremum at the chosen base point.
    simpa [qf, xq, quotientPointwiseSupremumOnUnivLift] using
      (closedConvexFunction_eq_of_separationQuotient_eq
        (closedConvexFunction_pointwiseSupremumOn_univ hφ)
        (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk x)))
  have hslice_base_val (i : ι) :
      ψ i xq = φ x i := by
    -- Each quotient slice agrees with the original slice at the base point.
    simpa [ψ, xq, quotientSliceLift] using
      (closedConvexFunction_eq_of_separationQuotient_eq
        (hφ i) (SeparationQuotient.mk_outCLM ℝ (SeparationQuotient.mk x)))
  have hqf_base_real :
      withTopRealPart qf xq =
        withTopRealPart (pointwiseSupremumOn (Set.univ : Set ι) φ) x := by
    -- Read the quotient base value back on the original owner using fiber constancy.
    simpa [withTopRealPart] using congrArg WithTop.untop₀ hqf_base_val
  have hslice_base_real (i : ι) :
      withTopRealPart (ψ i) xq = withTopRealPart (fun y ↦ φ y i) x := by
    -- Each quotient slice takes the same value as the original slice at the chosen base point.
    simpa [withTopRealPart] using congrArg WithTop.untop₀ (hslice_base_val i)
  have hactive_base_real {i : ι}
      (hi : i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x) :
      withTopRealPart (ψ i) xq = withTopRealPart qf xq := by
    -- Active slices match the quotient supremum already at the base point.
    calc
      withTopRealPart (ψ i) xq = withTopRealPart (fun y ↦ φ y i) x := hslice_base_real i
      _ = withTopRealPart (pointwiseSupremumOn (Set.univ : Set ι) φ) x := by
          simpa [withTopRealPart] using
            congrArg WithTop.untop₀
              ((mem_activePointwiseSupremumOnIndices_univ_iff).1 hi)
      _ = withTopRealPart qf xq := hqf_base_real.symm
  have hx_dom :
      x ∈ dom (pointwiseSupremumOn (Set.univ : Set ι) φ) := by
    -- Interior membership on the quotient owner implies finiteness on the original owner at `x`.
    have hxq_dom : xq ∈ dom qf := interior_subset hxq
    simpa [hqf_base_val] using hxq_dom
  have hslice_dom_base (i : ι) : x ∈ dom (fun y ↦ φ y i) := by
    -- The quotient interior-domain transfer for slices gives original finiteness at the base.
    have hxqi :
        xq ∈ interior (dom (ψ i)) :=
      quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
        (φ := φ) (x := x) hxq i
    have hxqi_dom : xq ∈ dom (ψ i) := interior_subset hxqi
    simpa [hslice_base_val i] using hxqi_dom
  have hbranch_cont (i : ι) :
      ContinuousAt (fun α : ℝ ↦ withTopRealPart (ψ i) (line α)) 0 := by
    -- Each quotient slice is continuous at the base because the base point lies in the slice
    -- interior domain and the line map is continuous.
    have hxqi :
        xq ∈ interior (dom (ψ i)) :=
      quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
        (φ := φ) (x := x) hxq i
    have hψi : ClosedConvexFunction (ψ i) := by
      -- Pull the original closed convex slice through the quotient section.
      simpa [ψ, quotientSliceLift, Function.comp] using
        (hφ i).compContinuousLinearMap (SeparationQuotient.outCLM ℝ V)
    have hcont_q :
        ContinuousAt (withTopRealPart (ψ i)) xq :=
      -- Use the neighborhood form of continuity on the interior domain to avoid rewriting the
      -- goal into an extra `interior`.
      ContinuousOn.continuousAt
        hψi.convexOn_withTopRealPart.continuousOn_interior
        (isOpen_interior.mem_nhds hxqi)
    have hline_cont0 : ContinuousAt line 0 := by
      simpa [line] using hline_cont.continuousAt
    have hcont_q0 : ContinuousAt (withTopRealPart (ψ i)) (line 0) := by
      simpa [line] using hcont_q
    exact hcont_q0.comp hline_cont0
  let inactive : Finset ι := Finset.univ.filter fun i ↦ i ∉ A
  have hinactive_lt_j0 :
      ∀ᶠ α : ℝ in 𝓝 (0 : ℝ), ∀ i ∈ inactive,
        withTopRealPart (ψ i) (line α) < withTopRealPart (ψ j0) (line α) := by
    -- A strict inactive gap at the base persists along the line for sufficiently small steps.
    refine (inactive.eventually_all).2 ?_
    intro i hi
    have hi_notA : i ∉ A := (Finset.mem_filter.mp hi).2
    have hi_not_active :
        i ∉ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x := by
      intro hi_active
      exact hi_notA ((hA i).2 hi_active)
    have hbase_lt :
        withTopRealPart (ψ i) xq < withTopRealPart (ψ j0) xq := by
      calc
        withTopRealPart (ψ i) xq = withTopRealPart (fun y ↦ φ y i) x := hslice_base_real i
        _ < withTopRealPart (pointwiseSupremumOn (Set.univ : Set ι) φ) x := by
            exact inactiveSlice_lt_pointwiseSupremumOn_univ_realPart_at_base
              (φ := φ) (x := x) (i := i) hx_dom (hslice_dom_base i) hi_not_active
        _ = withTopRealPart qf xq := hqf_base_real.symm
        _ = withTopRealPart (ψ j0) xq := (hactive_base_real hj0_active).symm
    have hbase_lt_line :
        withTopRealPart (ψ i) (line 0) < withTopRealPart (ψ j0) (line 0) := by
      simpa [line] using hbase_lt
    exact (hbranch_cont i).eventually_lt (hbranch_cont j0) hbase_lt_line
  have hqf_dom_eventually :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), line α ∈ dom qf := by
    -- Interior membership gives a neighborhood where the quotient supremum stays finite.
    have hdom_nhds_raw :
        dom
            (fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q)) ∈
          𝓝 xq :=
      mem_interior_iff_mem_nhds.mp hxq
    have hdom_nhds_xq : dom qf ∈ 𝓝 xq := by
      -- Normalize the local abbreviation back to the canonical lifted owner before applying the
      -- neighborhood witness from `hxq`.
      change
        dom
            (fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q)) ∈
          𝓝 xq
      exact hdom_nhds_raw
    have hdom_nhds : dom qf ∈ 𝓝 (line 0) := by
      simpa [line] using hdom_nhds_xq
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (hline_cont.continuousAt.tendsto.eventually hdom_nhds)
  have hinactive_lt_j0_within :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), ∀ i ∈ inactive,
        withTopRealPart (ψ i) (line α) < withTopRealPart (ψ j0) (line α) := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hinactive_lt_j0
  -- Route correction: instead of pushing a raw `EReal` secant inequality through the full
  -- supremum, choose the maximizing branch for each nearby quotient point and prove it must be
  -- active because every inactive branch stays below the fixed active branch `j0`.
  filter_upwards [hqf_dom_eventually, hinactive_lt_j0_within, self_mem_nhdsWithin] with α hqf_dom
      hinactive hαmem
  have hα : 0 < α := hαmem
  have hqf_eq_sup :
      qf (line α) = Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ψ i (line α)) := by
    -- Rewrite the lifted finite supremum as an honest finite `sup'`.
    simpa [qf, ψ, quotientPointwiseSupremumOnUnivLift, quotientSliceLift] using
      (pointwiseSupremumOn_univ_eq_sup'
        (φ := fun q : SeparationQuotient V ↦
          fun i : ι ↦ φ (SeparationQuotient.outCLM ℝ V q) i)
        (x := line α))
  obtain ⟨k, hk_mem, hk_eq⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ ψ i (line α))
  have hslice_dom (i : ι) : line α ∈ dom (ψ i) := by
    -- Every slice is finite wherever the finite quotient supremum is finite.
    have hle : ψ i (line α) ≤ qf (line α) := by
      rw [hqf_eq_sup]
      exact Finset.le_sup' (fun j ↦ ψ j (line α)) (Finset.mem_univ i)
    exact lt_of_le_of_lt hle hqf_dom
  have hkA : k ∈ A := by
    by_contra hk_notA
    have hk_inactive : k ∈ inactive := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk_notA⟩
    have hk_lt_j0_real :
        withTopRealPart (ψ k) (line α) < withTopRealPart (ψ j0) (line α) :=
      hinactive k hk_inactive
    have hk_lt_j0 :
        ψ k (line α) < ψ j0 (line α) := by
      rw [← coe_withTopRealPart (f := ψ k) (hslice_dom k),
        ← coe_withTopRealPart (f := ψ j0) (hslice_dom j0)]
      exact_mod_cast hk_lt_j0_real
    have hj0_le_hk : ψ j0 (line α) ≤ ψ k (line α) := by
      rw [← hk_eq]
      exact Finset.le_sup' (fun i ↦ ψ i (line α)) (Finset.mem_univ j0)
    exact (not_lt_of_ge hj0_le_hk) hk_lt_j0
  have hk_active : k ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x := (hA k).1 hkA
  have hqf_real_eq :
      withTopRealPart qf (line α) = withTopRealPart (ψ k) (line α) := by
    -- The maximizing branch `k` realizes the quotient supremum at the current step.
    have hval_eq : qf (line α) = ψ k (line α) := by
      rw [hqf_eq_sup, hk_eq]
    simpa [withTopRealPart] using congrArg WithTop.untop₀ hval_eq
  have hbase_real_eq :
      withTopRealPart qf xq = withTopRealPart (ψ k) xq := by
    -- Active branches agree with the quotient supremum at the base point.
    exact (hactive_base_real hk_active).symm
  have hineq :
      (withTopRealPart qf (line α) - withTopRealPart qf xq) / α
        ≤
          A.sup' hA_nonempty_secant (fun i ↦
            (withTopRealPart (ψ i) (line α) - withTopRealPart (ψ i) xq) / α) := by
    -- Rewrite the left secant through the active maximizing branch and dominate it by the active
    -- finite `sup'`.
    calc
      (withTopRealPart qf (line α) - withTopRealPart qf xq) / α
          = (withTopRealPart (ψ k) (line α) - withTopRealPart (ψ k) xq) / α := by
              rw [hqf_real_eq, hbase_real_eq]
      _ ≤ A.sup' hA_nonempty_secant (fun i ↦
            (withTopRealPart (ψ i) (line α) - withTopRealPart (ψ i) xq) / α) := by
              exact Finset.le_sup' (f := fun i ↦
                (withTopRealPart (ψ i) (line α) - withTopRealPart (ψ i) xq) / α) hkA
  -- Expand the local abbreviations back to the theorem statement.
  simpa only [xq, qf, ψ, line] using hineq

lemma quotientDirectionalDerivativeReal_le_supportFunctionActiveHull
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i))
    {x : V}
    (hxq :
      SeparationQuotient.mk x ∈
        interior
          (dom
            (fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q))))
    (p : SeparationQuotient V) :
    ((fun q : SeparationQuotient V ↦
        pointwiseSupremumOn (Set.univ : Set ι) φ
          (SeparationQuotient.outCLM ℝ V q))′[hxq] p : EReal) ≤
      supportFunction
        (convexHull ℝ
        (SeparationQuotient.mk ''
          {g | ∃ i : ι,
              i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                g ∈ ∂ (fun y ↦ φ y i)(x)})) p := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let A : Finset ι :=
    Finset.univ.filter
      fun i ↦ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x
  have hA_nonempty : A.Nonempty := by
    -- Choose one active index to witness nonemptiness of the active finite family.
    rcases activePointwiseSupremumOnIndices_univ_nonempty (φ := φ) x with ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hA :
      ∀ i ∈ A, i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hA_iff :
      ∀ i : ι, i ∈ A ↔ i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x := by
    intro i
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have hqf :
      ClosedConvexFunction
        (fun q : SeparationQuotient V ↦
          pointwiseSupremumOn (Set.univ : Set ι) φ
            (SeparationQuotient.outCLM ℝ V q)) := by
    -- The quotient lift inherits closed convexity from the original finite supremum owner.
    simpa using quotientLiftPointwiseSupremumOnUniv_closedConvex (hφ := hφ)
  have hsecant_tendsto :
      Filter.Tendsto
        (fun α : ℝ ↦
          (withTopRealPart
              (fun q : SeparationQuotient V ↦
                pointwiseSupremumOn (Set.univ : Set ι) φ
                  (SeparationQuotient.outCLM ℝ V q))
              (SeparationQuotient.mk x + α • p) -
            withTopRealPart
              (fun q : SeparationQuotient V ↦
                pointwiseSupremumOn (Set.univ : Set ι) φ
                  (SeparationQuotient.outCLM ℝ V q))
              (SeparationQuotient.mk x)) / α)
        (𝓝[>] (0 : ℝ))
        (𝓝
          ((fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q))′[hxq] p)) := by
    -- The lifted supremum secants converge to the quotient directional derivative.
    simpa using
      tendsto_directionalSecantQuotient_of_mem_interior hqf.convexOn_withTopRealPart hxq p
  have hactive_tendsto :
      Filter.Tendsto
        (fun α : ℝ ↦
          A.sup' hA_nonempty (fun i ↦
            (withTopRealPart
                (fun q : SeparationQuotient V ↦
                  φ (SeparationQuotient.outCLM ℝ V q) i)
                (SeparationQuotient.mk x + α • p) -
              withTopRealPart
                (fun q : SeparationQuotient V ↦
                  φ (SeparationQuotient.outCLM ℝ V q) i)
                (SeparationQuotient.mk x)) / α))
        (𝓝[>] (0 : ℝ))
        (𝓝
          (A.sup' hA_nonempty fun i ↦
            convexDirectionalDerivativeReal
              (quotientSliceLift (φ := φ) i)
              (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
                (φ := φ) (x := x) hxq i) p)) := by
    -- The active finite `sup'` limit is delegated to the slice-wise secant convergence helper.
    exact tendsto_activeSupQuotientSliceSecant (hφ := hφ) (x := x) hxq A hA_nonempty p
  have hsecant_bound :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        (withTopRealPart
            (fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q))
            (SeparationQuotient.mk x + α • p) -
          withTopRealPart
            (fun q : SeparationQuotient V ↦
              pointwiseSupremumOn (Set.univ : Set ι) φ
                (SeparationQuotient.outCLM ℝ V q))
            (SeparationQuotient.mk x)) / α
          ≤
            A.sup' hA_nonempty (fun i ↦
              (withTopRealPart
                  (fun q : SeparationQuotient V ↦
                    φ (SeparationQuotient.outCLM ℝ V q) i)
                  (SeparationQuotient.mk x + α • p) -
                withTopRealPart
                  (fun q : SeparationQuotient V ↦
                    φ (SeparationQuotient.outCLM ℝ V q) i)
                  (SeparationQuotient.mk x)) / α) := by
    -- Route correction: the remaining structural step is now isolated in the dedicated helper.
    simpa using
      quotientPointwiseSupremumSecant_le_activeSupSecant_eventually
        (hφ := hφ) (x := x) A hA_iff hA_nonempty hxq p
  have hlimit_le :
      ((fun q : SeparationQuotient V ↦
          pointwiseSupremumOn (Set.univ : Set ι) φ
            (SeparationQuotient.outCLM ℝ V q))′[hxq] p)
        ≤
          A.sup' hA_nonempty (fun i ↦
            convexDirectionalDerivativeReal
              (quotientSliceLift (φ := φ) i)
              (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
                (φ := φ) (x := x) hxq i) p) := by
    -- Compare the two secant limits through the eventual active-branch majorization.
    exact le_of_tendsto_of_tendsto hsecant_tendsto hactive_tendsto hsecant_bound
  have hactive_le :
      ((A.sup' hA_nonempty fun i ↦
          convexDirectionalDerivativeReal
            (quotientSliceLift (φ := φ) i)
            (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
              (φ := φ) (x := x) hxq i) p) : EReal) ≤
        supportFunction
          (convexHull ℝ
            (SeparationQuotient.mk ''
              {g | ∃ i : ι,
                  i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                    g ∈ ∂ (fun y ↦ φ y i)(x)})) p := by
    -- The final support-function comparison is a finite `sup'` of the active slice bounds.
    exact
      activeSupQuotientSliceDirectionalDerivative_le_supportFunctionActiveHull
        (hφ := hφ) (x := x) A hA hA_nonempty hxq p
  have hlimit_le_ereal :
      (((fun q : SeparationQuotient V ↦
          pointwiseSupremumOn (Set.univ : Set ι) φ
            (SeparationQuotient.outCLM ℝ V q))′[hxq] p : ℝ) : EReal)
        ≤
          (A.sup' hA_nonempty fun i ↦
            ((convexDirectionalDerivativeReal
              (quotientSliceLift (φ := φ) i)
              (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
                (φ := φ) (x := x) hxq i) p : ℝ) : EReal)) := by
    have hlimit_le_ereal' :
        (((fun q : SeparationQuotient V ↦
            pointwiseSupremumOn (Set.univ : Set ι) φ
              (SeparationQuotient.outCLM ℝ V q))′[hxq] p : ℝ) : EReal)
          ≤
            (((A.sup' hA_nonempty fun i ↦
                convexDirectionalDerivativeReal
                  (quotientSliceLift (φ := φ) i)
                  (quotientSlice_memInteriorDom_of_quotientPointwiseSupremumInterior
                    (φ := φ) (x := x) hxq i) p : ℝ)) : EReal) := by
      exact_mod_cast hlimit_le
    simpa using hlimit_le_ereal'
  exact hlimit_le_ereal.trans hactive_le

/-- Helper for Lemma 3.13: once the quotient directional derivatives are bounded by the support
function of a closed convex set, every quotient subgradient lies in that set. -/
lemma quotientSubdifferential_subset_of_directionalDerivative_bound
    [FiniteDimensional ℝ (SeparationQuotient V)]
    [CompleteSpace (SeparationQuotient V)]
    {f : SeparationQuotient V → WithTop ℝ} (hf : ClosedConvexFunction f)
    {xq : SeparationQuotient V} (hxq : xq ∈ interior (dom f))
    {Q : Set (SeparationQuotient V)}
    (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (hbound : ∀ p : SeparationQuotient V, ((f′[hxq] p : ℝ) : EReal) ≤ supportFunction Q p) :
    ∂ f(xq) ⊆ Q := by
  intro g hg
  have hsingleton_subset : ({g} : Set (SeparationQuotient V)) ⊆ Q := by
    apply subset_of_supportFunction_le_on_domain ({g}) Q
      hQ_nonempty hQ_closed hQ_convex
    intro p hp
    have hpair :
        inner ℝ g p ≤ f′[hxq] p := by
      -- The quotient directional derivative dominates every quotient subgradient pairing.
      exact
        (convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
          hf.convexOn_withTopRealPart hxq p).2 ⟨g, hg, rfl⟩
    have hpair_le_Q : (((inner ℝ g p : ℝ) : EReal) ≤ supportFunction Q p) := by
      exact (show (((inner ℝ g p : ℝ) : EReal) ≤ (((f′[hxq] p : ℝ) : EReal))) from by
          exact_mod_cast hpair).trans (hbound p)
    -- Rewrite the singleton support function back to the single pairing.
    simpa [supportFunction_apply] using hpair_le_Q
  exact hsingleton_subset (by simp)

/-- Helper for Lemma 3.13: quotient convex-hull membership of the active generator pulls back to
the original ambient by zero-norm saturation. -/
lemma memConvexHull_activeGenerator_of_mk_memQuotientHull
    {φ : V → ι → WithTop ℝ} {x g : V}
    (hgbar :
      SeparationQuotient.mk g ∈
        convexHull ℝ
          (SeparationQuotient.mk ''
            {g | ∃ i : ι,
                i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                  g ∈ ∂ (fun y ↦ φ y i)(x)})) :
    g ∈
      convexHull ℝ
        {g | ∃ i : ι,
            i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
              g ∈ ∂ (fun y ↦ φ y i)(x)} := by
  let G : Set V :=
    {g | ∃ i : ι,
        i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
          g ∈ ∂ (fun y ↦ φ y i)(x)}
  have himage :
      SeparationQuotient.mk '' convexHull ℝ G =
        convexHull ℝ (SeparationQuotient.mk '' G) := by
    simpa [G] using
      (LinearMap.image_convexHull (SeparationQuotient.mkCLM ℝ V).toLinearMap G)
  have hg_image :
      SeparationQuotient.mk g ∈ SeparationQuotient.mk '' convexHull ℝ G := by
    rw [himage]
    exact hgbar
  change ∃ g' ∈ convexHull ℝ G, SeparationQuotient.mk g' = SeparationQuotient.mk g at hg_image
  rcases hg_image with ⟨g', hg', hg_eq⟩
  have hzero : ‖g - g'‖ = 0 := by
    have hInsep : Inseparable g g' := by
      apply (SeparationQuotient.mk_eq_mk).mp
      simpa [eq_comm] using hg_eq
    rw [Metric.inseparable_iff, dist_eq_norm] at hInsep
    simpa [sub_eq_add_neg] using hInsep
  have hshift :
      g' + (g - g') ∈ convexHull ℝ G :=
    mem_convexHull_add_zeroNorm_of_saturated
      (Q := G)
      (hQ := fun a b ha hb ↦
        mem_activeSubdifferentialGenerator_add_zeroNorm (φ := φ) ha hb)
      (g := g') (k := g - g') hg' hzero
  -- The zero-norm shift exactly recovers the original representative `g`.
  simpa [G, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hshift

/-- Helper for Lemma 3.13: the reverse inclusion reduces the active-slice formula to a single
 support-function/separation step. -/
lemma subdifferential_subset_convexHull_activeSubdifferentials_pointwiseSupremumOn_univ
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun x ↦ φ x i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    ∂ (pointwiseSupremumOn (Set.univ : Set ι) φ)(x) ⊆
      convexHull ℝ
        {g | ∃ i : ι,
            i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
              g ∈ ∂ (fun y ↦ φ y i)(x)} := by
  let G : Set V :=
    {g | ∃ i : ι,
        i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
          g ∈ ∂ (fun y ↦ φ y i)(x)}
  let qf : SeparationQuotient V → WithTop ℝ :=
    fun q ↦ pointwiseSupremumOn (Set.univ : Set ι) φ (SeparationQuotient.outCLM ℝ V q)
  let Q : Set (SeparationQuotient V) :=
    convexHull ℝ (SeparationQuotient.mk '' G)
  intro g hg
  have hf : ClosedConvexFunction (pointwiseSupremumOn (Set.univ : Set ι) φ) :=
    closedConvexFunction_pointwiseSupremumOn_univ hφ
  have hxq : SeparationQuotient.mk x ∈ interior (dom qf) := by
    -- Move the common interior-domain point to the quotient owner before applying Hilbert-space
    -- support comparison there.
    simpa [qf] using
      quotientLiftPointwiseSupremumOnUniv_memInteriorDom (hφ := hφ) hx
  have hgbar :
      SeparationQuotient.mk g ∈ subdifferential qf (SeparationQuotient.mk x) := by
    -- Push the original subgradient forward to the quotient-lifted supremum.
    simpa [qf] using
      (memSubdifferential_comp_outCLM_of_memSubdifferential (hf := hf) hg)
  have hQ_nonempty : Q.Nonempty :=
    quotientActiveHull_nonempty (hφ := hφ) hx
  have hQ_closed : IsClosed Q := by
    -- Route correction: the quotient target-set packaging is isolated in the dedicated helper.
    simpa [Q, G] using quotientActiveHull_isClosed (hφ := hφ) hx
  have hQ_convex : Convex ℝ Q := by
    -- The quotient active hull is a convex hull by definition.
    simpa [Q] using (convex_convexHull ℝ (SeparationQuotient.mk '' G))
  have hgbar_mem : SeparationQuotient.mk g ∈ Q := by
    have hqf : ClosedConvexFunction qf := by
      -- The quotient lift inherits closed convexity from the original finite supremum owner.
      simpa [qf] using quotientLiftPointwiseSupremumOnUniv_closedConvex (hφ := hφ)
    have hqsubset :
        subdifferential qf (SeparationQuotient.mk x) ⊆ Q := by
      -- The final quotient inclusion now depends only on the isolated directional-derivative
      -- bound and the closedness package for `Q`.
      refine quotientSubdifferential_subset_of_directionalDerivative_bound
        (f := qf) hqf hxq hQ_nonempty hQ_closed hQ_convex ?_
      intro p
      simpa [qf, Q, G] using
        quotientDirectionalDerivativeReal_le_supportFunctionActiveHull
          (hφ := hφ) (x := x) hxq p
    exact hqsubset hgbar
  -- Pull the quotient convex-hull membership back to the original ambient through zero-norm
  -- saturation of the active generator.
  exact memConvexHull_activeGenerator_of_mk_memQuotientHull (φ := φ) (x := x) (g := g) hgbar_mem

theorem subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun x ↦ φ x i))
    {x : V} (hx : x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set ι) φ))) :
    ∂ (pointwiseSupremumOn (Set.univ : Set ι) φ)(x) =
      convexHull ℝ
        {g | ∃ i : ι,
            i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
              g ∈ ∂ (fun y ↦ φ y i)(x)} := by
  -- The active-hull inclusion is already proved, so only the reverse inclusion remains.
  exact Set.Subset.antisymm
    (subdifferential_subset_convexHull_activeSubdifferentials_pointwiseSupremumOn_univ hφ hx)
    (active_hull_subset_subdifferential_pointwiseSupremumOn_univ hx)

/-- Lemma 3.13: for a nonempty finite family of closed convex `WithTop ℝ`-valued functions on a
finite-dimensional real inner-product space, the canonical owner
`f := pointwiseSupremumOn (Set.univ : Set ι) φ` is closed and convex, its effective-domain
interior is the intersection of the slice interiors, and at each interior point its
subdifferential is the convex hull of the subdifferentials of the active slices. Specializing
`V = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` statement. -/
theorem pointwiseSupremumOn_univ_closedConvex_interior_dom_subdifferential
    [Finite ι] [Nonempty ι] [FiniteDimensional ℝ V] {φ : V → ι → WithTop ℝ}
    (hφ : ∀ i, ClosedConvexFunction (fun y ↦ φ y i)) :
    let f : V → WithTop ℝ := pointwiseSupremumOn (Set.univ : Set ι) φ
    ClosedConvexFunction f ∧
      interior (dom f) = ⋂ i : ι, interior (dom (fun y ↦ φ y i)) ∧
      ∀ ⦃x : V⦄, x ∈ interior (dom f) →
        ∂ f(x) =
          convexHull ℝ
            {g | ∃ i : ι,
                i ∈ activePointwiseSupremumOnIndices (Set.univ : Set ι) φ x ∧
                  g ∈ ∂ (fun y ↦ φ y i)(x)} := by
  -- Unfold the local abbreviation and package the three finite-supremum conclusions.
  dsimp
  refine ⟨closedConvexFunction_pointwiseSupremumOn_univ hφ,
    interior_dom_pointwiseSupremumOn_univ, ?_⟩
  intro x hx
  -- The subdifferential clause is exactly the previous theorem specialized at `x`.
  exact subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials hφ hx

end Subdifferential

end

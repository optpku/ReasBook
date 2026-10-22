/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped WithTopConvexAnalysis

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

namespace ClosedConvexOn

/-- Helper for Theorem 3.1.2.6: a closed convex `WithTop ℝ`-valued function has closed
constrained real sublevel sets. -/
theorem isClosed_constrainedSublevelSet
    {Q : Set E} {f : E → WithTop ℝ} (hf : ClosedConvexOn Q f) (β : ℝ) :
    IsClosed (constrainedSublevelSet Q f β) := by
  -- The constrained sublevel set is the preimage of the constrained epigraph along the graph map
  -- `x ↦ (x, β)`.
  have hcont : Continuous fun x : E ↦ (x, β) :=
    by fun_prop
  simpa [constrainedSublevelSet, constrainedEpigraph] using
    hf.isClosed_constrainedEpigraph.preimage hcont

/-- Helper for Theorem 3.1.2.6: a closed convex `WithTop ℝ`-valued function has convex
constrained real sublevel sets. -/
theorem convex_constrainedSublevelSet
    {Q : Set E} {f : E → WithTop ℝ} (hf : ClosedConvexOn Q f) (β : ℝ) :
    Convex ℝ (constrainedSublevelSet Q f β) := by
  -- Convexity is inherited from the convexity of the feasible set and the convexity inequality
  -- for the finite real part.
  intro x hx y hy a b ha hb hab
  rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
  rcases mem_constrainedSublevelSet_iff.mp hy with ⟨hyQ, hyβ⟩
  have hzQ : a • x + b • y ∈ Q :=
    hf.convex hxQ hyQ ha hb hab
  have hxdom : x ∈ dom f :=
    hf.subset_withTopEffectiveDomain hxQ
  have hydom : y ∈ dom f :=
    hf.subset_withTopEffectiveDomain hyQ
  have hzdom : a • x + b • y ∈ dom f :=
    hf.subset_withTopEffectiveDomain hzQ
  have hconv :
      withTopRealPart f (a • x + b • y) ≤
        a * withTopRealPart f x + b * withTopRealPart f y :=
    hf.convexOn_withTopRealPart.2 hxQ hyQ ha hb hab
  have hxβ' : withTopRealPart f x ≤ β :=
    (withTopRealPart_le_iff hxdom).2 hxβ
  have hyβ' : withTopRealPart f y ≤ β :=
    (withTopRealPart_le_iff hydom).2 hyβ
  have hcomb :
      a * withTopRealPart f x + b * withTopRealPart f y ≤ a * β + b * β := by
    gcongr
  have hzβ' : withTopRealPart f (a • x + b • y) ≤ β := by
    calc
      withTopRealPart f (a • x + b • y)
          ≤ a * withTopRealPart f x + b * withTopRealPart f y := hconv
      _ ≤ a * β + b * β := hcomb
      _ = β := by
        calc
          a * β + b * β = (a + b) * β := by ring
          _ = β := by rw [hab, one_mul]
  exact mem_constrainedSublevelSet_iff.2
    ⟨hzQ, (withTopRealPart_le_iff hzdom).1 hzβ'⟩

/-- Helper for Theorem 3.1.2.6: the real-valued representative of a closed convex real lift is
lower semicontinuous on any closed feasible set. -/
theorem lowerSemicontinuousOn_real
    {Q : Set E} {f : E → ℝ} (hQ : IsClosed Q)
    (hf : ClosedConvexOn Q (fun x ↦ (f x : WithTop ℝ))) :
    LowerSemicontinuousOn f Q := by
  -- Rewrite the real epigraph as the chapter's constrained epigraph for the lifted function.
  rw [lowerSemicontinuousOn_iff_isClosed_epigraph hQ]
  have hEq :
      {p : E × ℝ | p.1 ∈ Q ∧ f p.1 ≤ p.2} =
        constrainedEpigraph Q (fun x ↦ (f x : WithTop ℝ)) := by
    ext p
    constructor
    · rintro ⟨hpQ, hp₂⟩
      exact mem_constrainedEpigraph_iff.2 ⟨hpQ, by exact_mod_cast hp₂⟩
    · rintro ⟨hpQ, hp₂⟩
      have hp₂' : ((f p.1 : ℝ) : WithTop ℝ) ≤ (p.2 : WithTop ℝ) := hp₂
      exact ⟨hpQ, by exact_mod_cast hp₂'⟩
  simpa [hEq] using hf.isClosed_constrainedEpigraph

/-- Helper for Theorem 3.1.2.6: the lifted closed-convex hypothesis recovers the ordinary
real-valued convexity of the underlying function. -/
theorem convexOn_real
    {Q : Set E} {f : E → ℝ}
    (hf : ClosedConvexOn Q (fun x ↦ (f x : WithTop ℝ))) :
    ConvexOn ℝ Q f := by
  -- For real lifts, the finite real part is just the original function.
  simpa [withTopRealPart] using hf.convexOn_withTopRealPart

end ClosedConvexOn

/-- Helper for Theorem 3.1.2.6: a continuous linear functional on `ℝ × ℝ` is determined by its
values on the two coordinate vectors. -/
theorem strongDual_apply_prod
    (f : StrongDual ℝ (ℝ × ℝ)) (u v : ℝ) :
    f (u, v) = u * f ((1 : ℝ), (0 : ℝ)) + v * f ((0 : ℝ), (1 : ℝ)) := by
  -- Expand `(u, v)` in the standard basis and use linearity.
  have hpair :
      (u, v) = u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  calc
    f (u, v) = f (u • ((1 : ℝ), (0 : ℝ)) + v • ((0 : ℝ), (1 : ℝ))) := by rw [hpair]
    _ = f (u • ((1 : ℝ), (0 : ℝ))) + f (v • ((0 : ℝ), (1 : ℝ))) := by rw [map_add]
    _ = u • f ((1 : ℝ), (0 : ℝ)) + v • f ((0 : ℝ), (1 : ℝ)) := by
      rw [map_smul, map_smul]
    _ = u * f ((1 : ℝ), (0 : ℝ)) + v * f ((0 : ℝ), (1 : ℝ)) := by
      simp [smul_eq_mul]

/- Theorem 3.1.2.6 lies in the chapter's two-function minimax-linearization domain on a proper
real normed space, with the textbook finite-dimensional `ℝⁿ` statement recovered by the canonical
bridge `FiniteDimensional.proper_real`.

Sampled owner-style declarations:
- `ClosedConvexOn` from `Definition_3_1_1_5`, the chapter owner for closed convexity on a
  feasible set
- `constrainedSublevelSet` from `Definition_3_3`, the owner real-sublevel-set construction on a
  feasible set
- `IsMinimaxLinearizationParameter` from `Definition_3_1_2_3`, the source-facing owner predicate
  for the minimax equality on two functions
- `StrongConvexOn.existsUnique_isMinOn_of_isClosed_lowerSemicontinuousOn` in `Theorem_3_45`, the
  nearby Chapter 3 proper-space owner theorem showing that bounded sublevel sets feed attainment
  through `ProperSpace` rather than through a frozen finite-dimensional hypothesis

Best owner abstraction:
- source-facing/core owner:
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`

Primitive data:
- a feasible set `Q : Set E`
- two real-valued objectives `f₁`, `f₂ : E → ℝ`
- closed convexity of their canonical `WithTop` lifts on `Q`
- boundedness of the constrained sublevel sets of the pointwise maximum
  `x ↦ max (f₁ x) (f₂ x)` on `Q`

Derived API:
- a parameter `lam : unitInterval`
- the owner conclusion
  `IsMinimaxLinearizationParameter (fun x : Q ↦ f₁ x) (fun x : Q ↦ f₂ x) lam`

Source/core/bridge triage:
- source-facing: this two-function bounded-sublevel-set minimax existence theorem
- core/canonical: `ClosedConvexOn`, `constrainedSublevelSet`, and
  `IsMinimaxLinearizationParameter`
- bridge/view: the coercion of real-valued objectives to `WithTop ℝ`, used only in the
  closed-convex and sublevel-set hypotheses

This file is therefore the owner theorem for the two-function case. The refinement keeps the
source semantics unchanged, reuses the existing chapter owners directly, and removes the
nonessential finite-dimensional proof-route specialization from the public surface. -/

/-- Theorem 3.1.2.6: if `f₁` and `f₂` are real-valued functions whose `WithTop` lifts are closed
and convex on a feasible set `Q`, and every constrained sublevel set of the pointwise maximum
`x ↦ max (f₁ x) (f₂ x)` on `Q` is bounded, then there exists some `λ* ∈ [0, 1]` for which the
minimum value of `x ↦ max (f₁ x) (f₂ x)` on `Q` equals the minimum value of the convex
combination `x ↦ λ* f₁ x + (1 - λ*) f₂ x`; in Lean this minimum equality is recorded by the owner
predicate `IsMinimaxLinearizationParameter` on the subtype `Q`. The textbook finite-dimensional
`ℝⁿ` statement is recovered by equipping `E = EuclideanSpace ℝ (Fin n)` with the canonical
`ProperSpace` instance. -/
-- Proof sketch: consider the auxiliary value function
-- `φ(λ) = inf_{x ∈ Q} (λ f₁(x) + (1 - λ) f₂(x))`. Closed convexity and bounded constrained
-- sublevel sets of the maximum objective are the source-facing hypotheses, while the proper-space
-- compactness bridge turns the closed bounded feasible sublevel slices needed in the chapter's
-- minimizer-existence argument into compact ones. The pointwise maximum of the two functions is
-- again closed and convex, and the textbook monotonicity argument for the minimizing selections
-- then shows that a maximizer `λ* ∈ [0, 1]` of `φ` gives the desired minimax equality.
theorem exists_minimax_parameter_of_bounded_constrainedSublevelSets
    {Q : Set E} {f₁ f₂ : E → ℝ}
    (hf₁ : ClosedConvexOn Q (fun x ↦ (f₁ x : WithTop ℝ)))
    (hf₂ : ClosedConvexOn Q (fun x ↦ (f₂ x : WithTop ℝ)))
    (hbounded :
    ∀ β : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet Q
            (fun x ↦ ((max (f₁ x) (f₂ x) : ℝ) : WithTop ℝ)) β)) :
    ∃ lam : unitInterval,
      IsMinimaxLinearizationParameter (fun x : Q ↦ f₁ x) (fun x : Q ↦ f₂ x) lam :=
  by
  rcases Q.eq_empty_or_nonempty with rfl | hQ_nonempty
  · -- On the empty feasible set, both infima are over an empty range and therefore agree.
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    let lam : unitInterval := ⟨0, hzero_mem⟩
    have hrange_max :
        Set.range (fun x : (∅ : Set E) ↦ ((max (f₁ x) (f₂ x) : ℝ) : EReal)) = ∅ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.property.elim
      · simp
    have hrange_line :
        Set.range
            (fun x : (∅ : Set E) ↦
              ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal)) = ∅ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact x.property.elim
      · simp
    refine ⟨lam, ?_⟩
    rw [isMinimaxLinearizationParameter_iff, hrange_max, hrange_line]
  · -- Route correction: the source's global `λ`-slice minimizer route is not valid under the
    -- actual hypotheses, so the proof works through a compact primal minimizer and a supporting
    -- functional on the convex upper image in `ℝ²`.
    let β₀ : ℝ := max (f₁ hQ_nonempty.some) (f₂ hQ_nonempty.some)
    let S : Set E :=
      constrainedSublevelSet Q
        (fun x ↦ ((max (f₁ x) (f₂ x) : ℝ) : WithTop ℝ)) β₀
    have hsome_memS : hQ_nonempty.some ∈ S := by
      -- The chosen reference point lies in the corresponding max-sublevel slice by definition.
      refine mem_constrainedSublevelSet_iff.2 ?_
      exact ⟨hQ_nonempty.some_mem, le_rfl⟩
    have hS_closed : IsClosed S := by
      -- The max-sublevel slice is the intersection of the two individual closed sublevel sets.
      have hEq :
          S =
            constrainedSublevelSet Q (fun x ↦ (f₁ x : WithTop ℝ)) β₀ ∩
              constrainedSublevelSet Q (fun x ↦ (f₂ x : WithTop ℝ)) β₀ := by
        ext x
        constructor
        · intro hx
          rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
          have hxβ' : max (f₁ x) (f₂ x) ≤ β₀ := by
            exact_mod_cast hxβ
          exact ⟨mem_constrainedSublevelSet_iff.2
              ⟨hxQ, by exact_mod_cast le_trans (le_max_left (f₁ x) (f₂ x)) hxβ'⟩,
            mem_constrainedSublevelSet_iff.2
              ⟨hxQ, by exact_mod_cast le_trans (le_max_right (f₁ x) (f₂ x)) hxβ'⟩⟩
        · intro hx
          rcases hx with ⟨hx₁, hx₂⟩
          rcases mem_constrainedSublevelSet_iff.mp hx₁ with ⟨hxQ, hx₁β⟩
          rcases mem_constrainedSublevelSet_iff.mp hx₂ with ⟨_, hx₂β⟩
          refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
          exact_mod_cast (max_le hx₁β hx₂β)
      rw [hEq]
      exact
        (hf₁.isClosed_constrainedSublevelSet β₀).inter
          (hf₂.isClosed_constrainedSublevelSet β₀)
    have hS_convex : Convex ℝ S := by
      -- The same max-sublevel identity reduces convexity to the two scalar sublevel slices.
      have hEq :
          S =
            constrainedSublevelSet Q (fun x ↦ (f₁ x : WithTop ℝ)) β₀ ∩
              constrainedSublevelSet Q (fun x ↦ (f₂ x : WithTop ℝ)) β₀ := by
        ext x
        constructor
        · intro hx
          rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hxβ⟩
          have hxβ' : max (f₁ x) (f₂ x) ≤ β₀ := by
            exact_mod_cast hxβ
          exact ⟨mem_constrainedSublevelSet_iff.2
              ⟨hxQ, by exact_mod_cast le_trans (le_max_left (f₁ x) (f₂ x)) hxβ'⟩,
            mem_constrainedSublevelSet_iff.2
              ⟨hxQ, by exact_mod_cast le_trans (le_max_right (f₁ x) (f₂ x)) hxβ'⟩⟩
        · intro hx
          rcases hx with ⟨hx₁, hx₂⟩
          rcases mem_constrainedSublevelSet_iff.mp hx₁ with ⟨hxQ, hx₁β⟩
          rcases mem_constrainedSublevelSet_iff.mp hx₂ with ⟨_, hx₂β⟩
          refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
          exact_mod_cast (max_le hx₁β hx₂β)
      rw [hEq]
      exact
        (hf₁.convex_constrainedSublevelSet β₀).inter
          (hf₂.convex_constrainedSublevelSet β₀)
    have hS_bounded : Bornology.IsBounded S := by
      simpa [S, β₀] using hbounded β₀
    have hS_compact : IsCompact S :=
      Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
    have hS_nonempty : S.Nonempty :=
      ⟨hQ_nonempty.some, hsome_memS⟩
    have hS_subset : S ⊆ Q := by
      intro x hx
      exact (mem_constrainedSublevelSet_iff.mp hx).1
    have hf₁S : ClosedConvexOn S (fun x ↦ (f₁ x : WithTop ℝ)) :=
      hf₁.restrict hS_closed hS_convex hS_subset
    have hf₂S : ClosedConvexOn S (fun x ↦ (f₂ x : WithTop ℝ)) :=
      hf₂.restrict hS_closed hS_convex hS_subset
    have hlsc₁S : LowerSemicontinuousOn f₁ S :=
      hf₁S.lowerSemicontinuousOn_real hS_closed
    have hlsc₂S : LowerSemicontinuousOn f₂ S :=
      hf₂S.lowerSemicontinuousOn_real hS_closed
    have hlscMaxS : LowerSemicontinuousOn (fun x ↦ max (f₁ x) (f₂ x)) S :=
      hlsc₁S.sup hlsc₂S
    obtain ⟨xStar, hxStarS, hxStarMinS⟩ :=
      hlscMaxS.exists_isMinOn hS_nonempty hS_compact
    have hxStarQ : xStar ∈ Q :=
      hS_subset hxStarS
    have hxStar_beta : max (f₁ xStar) (f₂ xStar) ≤ β₀ :=
      by
        exact_mod_cast (mem_constrainedSublevelSet_iff.mp hxStarS).2
    have hxStarMinQ : IsMinOn (fun x ↦ max (f₁ x) (f₂ x)) Q xStar := by
      -- Any feasible point either lies in the compact slice `S`, where `xStar` is minimizing, or
      -- has larger max-value than `β₀`, which still dominates the value at `xStar`.
      intro y hyQ
      by_cases hyS : y ∈ S
      · exact hxStarMinS hyS
      · have hy_not_le : ¬ max (f₁ y) (f₂ y) ≤ β₀ := by
          intro hyβ
          exact hyS (mem_constrainedSublevelSet_iff.2 ⟨hyQ, by exact_mod_cast hyβ⟩)
        have hyβ_lt : β₀ < max (f₁ y) (f₂ y) :=
          lt_of_not_ge hy_not_le
        exact (le_trans hxStar_beta hyβ_lt.le)
    let fStar : ℝ := max (f₁ xStar) (f₂ xStar)
    let U : Set (ℝ × ℝ) :=
      {p | ∃ x ∈ Q, f₁ x ≤ p.1 ∧ f₂ x ≤ p.2}
    have hconv₁ : ConvexOn ℝ Q f₁ :=
      hf₁.convexOn_real
    have hconv₂ : ConvexOn ℝ Q f₂ :=
      hf₂.convexOn_real
    have hU_convex : Convex ℝ U := by
      -- The upper image is stable under convex combinations because `Q` is convex and both
      -- coordinates obey the convexity inequality.
      intro p hp q hq a b ha hb hab
      rcases hp with ⟨x, hxQ, hx₁, hx₂⟩
      rcases hq with ⟨y, hyQ, hy₁, hy₂⟩
      refine ⟨a • x + b • y, hf₁.convex hxQ hyQ ha hb hab, ?_, ?_⟩
      · calc
          f₁ (a • x + b • y) ≤ a * f₁ x + b * f₁ y := hconv₁.2 hxQ hyQ ha hb hab
          _ ≤ a * p.1 + b * q.1 := by gcongr
      · calc
          f₂ (a • x + b • y) ≤ a * f₂ x + b * f₂ y := hconv₂.2 hxQ hyQ ha hb hab
          _ ≤ a * p.2 + b * q.2 := by gcongr
    have hdStar_memU : (fStar, fStar) ∈ U := by
      -- The primal minimizer provides the diagonal upper-image point.
      refine ⟨xStar, hxStarQ, le_max_left _ _, le_max_right _ _⟩
    have hU_int_nonempty : (interior U).Nonempty := by
      -- Any feasible point contributes an open upper-right quadrant contained in `U`.
      let p0 : ℝ × ℝ := (f₁ hQ_nonempty.some + 1, f₂ hQ_nonempty.some + 1)
      let V : Set (ℝ × ℝ) := Set.Ioi (f₁ hQ_nonempty.some) ×ˢ Set.Ioi (f₂ hQ_nonempty.some)
      have hp0_memV : p0 ∈ V := by
        simp [p0, V]
      have hV_open : IsOpen V :=
        isOpen_Ioi.prod isOpen_Ioi
      have hV_subset : V ⊆ U := by
        intro p hp
        rcases hp with ⟨hp₁, hp₂⟩
        exact ⟨hQ_nonempty.some, hQ_nonempty.some_mem, hp₁.le, hp₂.le⟩
      refine ⟨p0, mem_interior_iff_mem_nhds.2 ?_⟩
      exact Filter.mem_of_superset (hV_open.mem_nhds hp0_memV) hV_subset
    have hdStar_not_mem_interior : (fStar, fStar) ∉ interior U := by
      -- A neighborhood of `(fStar, fStar)` inside `U` would contain a strictly smaller diagonal
      -- point, contradicting the minimality of `xStar`.
      intro hdStar_int
      rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hdStar_int) with
        ⟨ε, hε, hεball⟩
      let pDown : ℝ × ℝ := (fStar - ε / 2, fStar - ε / 2)
      have hpDown_dist : dist pDown (fStar, fStar) < ε := by
        rw [dist_eq_norm, Prod.norm_def]
        simpa [pDown, abs_of_pos hε] using half_lt_self hε
      have hpDown_memU : pDown ∈ U :=
        interior_subset (hεball hpDown_dist)
      rcases hpDown_memU with ⟨x, hxQ, hx₁, hx₂⟩
      have hxlt : max (f₁ x) (f₂ x) < fStar := by
        apply lt_of_le_of_lt (max_le_iff.mpr ⟨hx₁, hx₂⟩)
        simp [pDown, hε]
      rw [isMinOn_iff] at hxStarMinQ
      exact (not_lt_of_ge (hxStarMinQ x hxQ)) hxlt
    obtain ⟨f, hf_ne, hf_support⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hU_convex hdStar_not_mem_interior
        hU_int_nonempty
    let g : StrongDual ℝ (ℝ × ℝ) := -f
    have hg_support : ∀ p ∈ U, g (fStar, fStar) ≤ g p := by
      -- Negating the separating functional turns the upper bound on `U` into the lower bound we
      -- need for convex combinations.
      intro p hp
      simpa [g] using neg_le_neg (hf_support p hp)
    let α : ℝ := g (1, 0)
    let β : ℝ := g (0, 1)
    have hα_nonneg : 0 ≤ α := by
      have hstep : (fStar + 1, fStar) ∈ U := by
        exact ⟨xStar, hxStarQ, by linarith [le_max_left (f₁ xStar) (f₂ xStar)], le_max_right _ _⟩
      have hineq := hg_support (fStar + 1, fStar) hstep
      rw [strongDual_apply_prod g fStar fStar, strongDual_apply_prod g (fStar + 1) fStar] at hineq
      have hineq' : fStar * α + fStar * β ≤ (fStar + 1) * α + fStar * β := by
        simpa [α, β, mul_comm, mul_left_comm, mul_assoc] using hineq
      linarith
    have hβ_nonneg : 0 ≤ β := by
      have hstep : (fStar, fStar + 1) ∈ U := by
        exact ⟨xStar, hxStarQ, le_max_left _ _, by linarith [le_max_right (f₁ xStar) (f₂ xStar)]⟩
      have hineq := hg_support (fStar, fStar + 1) hstep
      rw [strongDual_apply_prod g fStar fStar, strongDual_apply_prod g fStar (fStar + 1)] at hineq
      have hineq' : fStar * α + fStar * β ≤ fStar * α + (fStar + 1) * β := by
        simpa [α, β, mul_comm, mul_left_comm, mul_assoc] using hineq
      linarith
    have hαβ_pos : 0 < α + β := by
      have hαβ_nonneg : 0 ≤ α + β := add_nonneg hα_nonneg hβ_nonneg
      have hαβ_ne : α + β ≠ 0 := by
        intro hsum
        have hα_zero : α = 0 := by linarith
        have hβ_zero : β = 0 := by linarith
        have hg_zero : g = 0 := by
          apply ContinuousLinearMap.ext
          intro z
          rcases z with ⟨u, v⟩
          rw [strongDual_apply_prod]
          simp [α, β, hα_zero, hβ_zero]
        exact hf_ne (by simpa [g] using hg_zero)
      exact lt_of_le_of_ne hαβ_nonneg hαβ_ne.symm
    let lamReal : ℝ := α / (α + β)
    have hlam_nonneg : 0 ≤ lamReal := by
      dsimp [lamReal]
      exact div_nonneg hα_nonneg hαβ_pos.le
    have hlam_le_one : lamReal ≤ 1 := by
      dsimp [lamReal]
      exact (div_le_iff₀ hαβ_pos).2 (by linarith)
    have hlam_mem : lamReal ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hlam_nonneg, hlam_le_one⟩
    let lam : unitInterval := ⟨lamReal, hlam_mem⟩
    have hline_lower :
        ∀ x ∈ Q, fStar ≤ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) := by
      -- The supporting inequality on `U` yields a global lower bound for the normalized convex
      -- combination.
      intro x hxQ
      have hxU : (f₁ x, f₂ x) ∈ U := by
        exact ⟨x, hxQ, le_rfl, le_rfl⟩
      have hineq := hg_support (f₁ x, f₂ x) hxU
      have hineq' : fStar * α + fStar * β ≤ f₁ x * α + f₂ x * β := by
        rw [strongDual_apply_prod g fStar fStar, strongDual_apply_prod g (f₁ x) (f₂ x)] at hineq
        simpa [α, β, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
          hineq
      have hineq'' : (α + β) * fStar ≤ β * f₂ x + α * f₁ x := by
        nlinarith [hineq']
      have hmul :
          (α + β) * fStar ≤ (α + β) * AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) := by
        have hline_mul :
            (α + β) * AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) =
              β * f₂ x + α * f₁ x := by
          dsimp [lam, lamReal]
          rw [AffineMap.lineMap_apply_ring]
          have hβ_div :
              1 - α / (α + β) = β / (α + β) := by
            field_simp [show α + β ≠ 0 by linarith [hαβ_pos]]
            ring
          rw [hβ_div]
          field_simp [show α + β ≠ 0 by linarith [hαβ_pos]]
        calc
          (α + β) * fStar ≤ β * f₂ x + α * f₁ x := hineq''
          _ = (α + β) * AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) := hline_mul.symm
      nlinarith [hαβ_pos, hmul]
    have hline_xStar_le : AffineMap.lineMap (f₂ xStar) (f₁ xStar) (lam : ℝ) ≤ fStar := by
      -- At the primal minimizer, the convex combination cannot exceed the pointwise maximum.
      rw [AffineMap.lineMap_apply_ring]
      have h₁ :
          (1 - (lam : ℝ)) * f₂ xStar ≤ (1 - (lam : ℝ)) * fStar := by
        exact mul_le_mul_of_nonneg_left (le_max_right (f₁ xStar) (f₂ xStar))
          (sub_nonneg.mpr lam.2.2)
      have h₂ : (lam : ℝ) * f₁ xStar ≤ (lam : ℝ) * fStar := by
        exact mul_le_mul_of_nonneg_left (le_max_left (f₁ xStar) (f₂ xStar)) lam.2.1
      nlinarith [h₁, h₂]
    have hline_xStar_eq : AffineMap.lineMap (f₂ xStar) (f₁ xStar) (lam : ℝ) = fStar := by
      exact le_antisymm hline_xStar_le (hline_lower xStar hxStarQ)
    let xStarQ : Q := ⟨xStar, hxStarQ⟩
    have hmax_min_subtype :
        IsMinOn (fun x : Q ↦ max (f₁ x) (f₂ x)) Set.univ xStarQ := by
      -- Restrict the primal minimizer from `Q` to the subtype `Q`.
      rw [isMinOn_univ_iff]
      rw [isMinOn_iff] at hxStarMinQ
      intro x
      exact hxStarMinQ x x.property
    have hline_min_subtype :
        IsMinOn (fun x : Q ↦ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ)) Set.univ xStarQ := by
      -- The supporting inequality gives the lower bound everywhere, and the minimizer attains it.
      rw [isMinOn_univ_iff]
      intro x
      simpa [xStarQ, hline_xStar_eq] using hline_lower x x.property
    have hsInf_max :
        sInf (Set.range fun x : Q ↦ ((max (f₁ x) (f₂ x) : ℝ) : EReal)) = (fStar : EReal) := by
      -- The subtype minimizer rewrites the infimum of the max objective to the attained value.
      have hopt :
          (SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ max (f₁ x) (f₂ x))).optimalValue = (fStar : EReal) := by
        simpa [fStar] using
          (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
          (problem := SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ max (f₁ x) (f₂ x)))
          (x := xStarQ) (by simp) hmax_min_subtype)
      simpa [SetConstrainedMinimizationProblem.optimalValue] using hopt
    have hsInf_line :
        sInf (Set.range fun x : Q ↦
          ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal)) = (fStar : EReal) := by
      -- The same argument applies to the supported convex combination.
      have hopt :
          (SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ))).optimalValue =
              (((AffineMap.lineMap (f₂ xStarQ) (f₁ xStarQ) (lam : ℝ) : ℝ) : EReal)) := by
        simpa using
          (SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn
          (problem := SetConstrainedMinimizationProblem.unconstrained
            (fun x : Q ↦ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ)))
          (x := xStarQ) (by simp) hline_min_subtype)
      calc
        sInf (Set.range fun x : Q ↦
          ((AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ) : ℝ) : EReal))
            = (SetConstrainedMinimizationProblem.unconstrained
                (fun x : Q ↦ AffineMap.lineMap (f₂ x) (f₁ x) (lam : ℝ))).optimalValue := by
                  simp [SetConstrainedMinimizationProblem.optimalValue]
        _ = (((AffineMap.lineMap (f₂ xStarQ) (f₁ xStarQ) (lam : ℝ) : ℝ) : EReal)) := hopt
        _ = (fStar : EReal) := by exact_mod_cast hline_xStar_eq
    refine ⟨lam, ?_⟩
    -- Both infima equal the common attained value `fStar`.
    rw [isMinimaxLinearizationParameter_iff]
    exact hsInf_max.trans hsInf_line.symm

end

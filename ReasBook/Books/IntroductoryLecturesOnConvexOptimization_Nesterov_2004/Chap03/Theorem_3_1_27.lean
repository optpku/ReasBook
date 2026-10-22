/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_22
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.LinearEqualityFeasibleSet
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis
open scoped TangentCone
open scoped Topology
open scoped NormalCone
open scoped WithTopConvexAnalysis

universe u v

variable {E : Type u} {Λ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ] [FiniteDimensional ℝ Λ]

/- Theorem 3.1.27 lies in the chapter's equality-constrained extended-valued convex-optimality
domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on finite-dimensional real inner-product spaces
  with linear equality constraints.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite-value representative;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients;
- `normalCone`, the notation `N[Q] x`, and `mem_normalCone_iff` in `Definition_3_22`, the chapter
  owner API for textbook normal cones;
- `constrainedSublevelSet` in `Definition_3_3`, the chapter owner for constrained sublevel sets;
- `linearEqualityFeasibleSet` in `LinearEqualityFeasibleSet`, the chapter owner for the feasible
  set cut out by `x ∈ Q` and `A x = b`.

Best owner abstraction:
- the source-facing theorem stated directly on the chapter owners
  `ConvexOn ℝ (dom f) (withTopRealPart f)`,
  `Convex ℝ Q`,
  `∂ f(xStar)`, `N[Q] xStar`,
  `constrainedSublevelSet`, and `linearEqualityFeasibleSet`.

Primitive data:
- a convex feasible set `Q`;
- an extended-real-valued objective `f`;
- a linear map `A` and right-hand side `b`;
- a Slater point `xBar` with a feasible ball `Metric.ball xBar ε ⊆ Q`.

Derived API:
- the feasibility conclusion `A xStar = b`;
- an owner-level subgradient witness `gStar ∈ ∂ f(xStar)`;
- the owner-level normal-cone condition `gStar - A.adjoint yStar ∈ N[Q] xStar`;
- the quantitative Slater-radius bound on `‖A.adjoint yStar‖`.

Source/core/bridge triage:
- source-facing: the quantitative equality-constrained optimality theorem;
- core/canonical: `dom`, `withTopRealPart`, `∂`, `N[Q] xStar`,
  `constrainedSublevelSet`, and `linearEqualityFeasibleSet`;
- bridge/view: matrix / transpose and relative-subgradient reformulations in downstream files.

The previous version rebuilt local copies of the effective domain, finite real part, convexity
predicate, subgradient predicate, subdifferential, and constrained sublevel set, then repackaged
the resulting theorem witnesses in one-off wrapper declarations. Those notions are already owned
earlier in the chapter, so this refinement deletes that duplicate wheel layer and states the
theorem directly on the canonical chapter surface with the explicit feasibility, multiplier, and
variational-inequality data that appear in the source.
-/
-- Semantic recall note: `lean_leansearch` only surfaced generic Lagrange-multiplier calculus
-- theorems, so this item stays on the chapter's local convex-analysis owner API.

/-- Helper for Theorem 3.1.27: a feasible point satisfying the subgradient-multiplier normal-cone
certificate is optimal on the linear-equality feasible set. -/
lemma isMinOn_linearEqualityFeasibleSet_of_subgradient_multiplier_certificate
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {A : E →ₗ[ℝ] Λ} {b : Λ} {xStar : E}
    (hxStar : xStar ∈ linearEqualityFeasibleSet Q A b)
    {yStar : Λ} {gStar : E}
    (hgStar : gStar ∈ ∂ f(xStar))
    (hnormal : gStar - A.adjoint yStar ∈ N[Q] xStar) :
    IsMinOn (withTopRealPart f) (linearEqualityFeasibleSet Q A b) xStar := by
  rcases hxStar with ⟨hxStarQ, hxStarA⟩
  refine isMinOn_iff.mpr ?_
  intro x hx
  rcases hx with ⟨hxQ, hxA⟩
  have hxDom : x ∈ dom f := interior_subset (hQ_subset_interior hxQ)
  have hxStarDom : xStar ∈ dom f := (mem_subdifferential_iff.mp hgStar).mem_dom
  -- First convert the ambient subgradient inequality to the finite real-part surface.
  have hsupport :
      withTopRealPart f xStar + inner ℝ gStar (x - xStar) ≤ withTopRealPart f x := by
    have hsub := (mem_subdifferential_iff.mp hgStar).2 hxDom
    rw [← coe_withTopRealPart hxDom, ← coe_withTopRealPart hxStarDom] at hsub
    exact_mod_cast hsub
  -- Then the normal-cone inequality removes the multiplier contribution on `Q`.
  have hpair :
      inner ℝ (A.adjoint yStar) (x - xStar) ≤ inner ℝ gStar (x - xStar) := by
    have hnormal_x := (mem_normalCone_iff.mp hnormal) x hxQ
    rw [inner_sub_left] at hnormal_x
    linarith
  -- Finally, feasibility on both points kills the adjoint pairing exactly.
  have hbase :
      inner ℝ (A.adjoint yStar) (x - xStar) = 0 := by
    calc
      inner ℝ (A.adjoint yStar) (x - xStar)
          = inner ℝ yStar (A (x - xStar)) := by
              rw [A.adjoint_inner_left]
      _ = inner ℝ yStar (A x - A xStar) := by
            simp [map_sub]
      _ = 0 := by
            simp [hxA, hxStarA]
  have hsupport' : withTopRealPart f xStar ≤ withTopRealPart f x := by
    linarith
  exact hsupport'

/-- Helper for Theorem 3.1.27: on a set contained in `interior (dom f)`, constrained-subgradient
membership is exactly optimality of the tilted finite real part on `Q`. -/
lemma mem_constrainedSubdifferential_iff_isMinOn_tilted
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {xStar h : E} :
    h ∈ ∂[Q] f(xStar) ↔
      xStar ∈ Q ∧
        IsMinOn (fun x : E ↦ withTopRealPart f x + inner ℝ (-h) x) Q xStar := by
  constructor
  · intro hh
    rcases (mem_constrainedSubdifferential_iff.mp hh) with ⟨hxStarQ, hxStarDom, hminorant⟩
    refine ⟨hxStarQ, ?_⟩
    refine isMinOn_iff.mpr ?_
    intro y hyQ
    have hyDom : y ∈ dom f := interior_subset (hQ_subset_interior hyQ)
    -- Rewriting the constrained-subgradient inequality shows that the tilted objective is
    -- minimized at `xStar`.
    have hsub := hminorant hyQ
    rw [← coe_withTopRealPart hxStarDom, ← coe_withTopRealPart hyDom] at hsub
    have hsubReal :
        withTopRealPart f xStar + inner ℝ h (y - xStar) ≤ withTopRealPart f y := by
      exact_mod_cast hsub
    have htilt :
        withTopRealPart f xStar + inner ℝ (-h) xStar ≤
          withTopRealPart f y + inner ℝ (-h) y := by
      rw [inner_neg_left, inner_neg_left]
      have hpair : inner ℝ h (y - xStar) = inner ℝ h y - inner ℝ h xStar := by
        rw [inner_sub_right]
      linarith
    simpa using htilt
  · rintro ⟨hxStarQ, hmin⟩
    have hxStarDom : xStar ∈ dom f := interior_subset (hQ_subset_interior hxStarQ)
    refine mem_constrainedSubdifferential_iff.mpr ⟨hxStarQ, hxStarDom, ?_⟩
    intro y hyQ
    have hyDom : y ∈ dom f := interior_subset (hQ_subset_interior hyQ)
    -- Expanding the minimizing property of the tilt recovers the constrained-subgradient
    -- supporting inequality on `Q`.
    have htilt := isMinOn_iff.mp hmin y hyQ
    have hsubReal :
        withTopRealPart f xStar + inner ℝ h (y - xStar) ≤ withTopRealPart f y := by
      rw [inner_neg_left, inner_neg_left] at htilt
      have hpair : inner ℝ h (y - xStar) = inner ℝ h y - inner ℝ h xStar := by
        rw [inner_sub_right]
      linarith
    rw [← coe_withTopRealPart hxStarDom, ← coe_withTopRealPart hyDom]
    exact_mod_cast hsubReal

/-- Helper for Theorem 3.1.27: an ambient subgradient plus a normal-cone remainder induces the
corresponding constrained subgradient on `Q`. -/
lemma mem_constrainedSubdifferential_of_mem_subdifferential_sub_mem_normalCone
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {xStar h gStar : E} (hxStarQ : xStar ∈ Q)
    (hgStar : gStar ∈ ∂ f(xStar))
    (hnormal : gStar - h ∈ N[Q] xStar) :
    h ∈ ∂[Q] f(xStar) := by
  have hxStarDom : xStar ∈ dom f := (mem_subdifferential_iff.mp hgStar).mem_dom
  refine mem_constrainedSubdifferential_iff.mpr ⟨hxStarQ, hxStarDom, ?_⟩
  intro y hyQ
  have hyDom : y ∈ dom f := interior_subset (hQ_subset_interior hyQ)
  -- Combine the ambient subgradient inequality with the normal-cone bound to remove the excess
  -- term `gStar - h`.
  have hsub := (mem_subdifferential_iff.mp hgStar).2 hyDom
  rw [← coe_withTopRealPart hxStarDom, ← coe_withTopRealPart hyDom] at hsub
  have hsubReal :
      withTopRealPart f xStar + inner ℝ gStar (y - xStar) ≤ withTopRealPart f y := by
    exact_mod_cast hsub
  have hnormal_y := (mem_normalCone_iff.mp hnormal) y hyQ
  have hpair : inner ℝ h (y - xStar) ≤ inner ℝ gStar (y - xStar) := by
    rw [inner_sub_left] at hnormal_y
    linarith
  have htarget :
      withTopRealPart f xStar + inner ℝ h (y - xStar) ≤ withTopRealPart f y := by
    linarith
  rw [← coe_withTopRealPart hxStarDom, ← coe_withTopRealPart hyDom]
  exact_mod_cast htarget

/-- Helper for Theorem 3.1.27: a normal-cone certificate for the tilted real-valued objective
transports back to an ambient subgradient of `f`. -/
lemma existsSubgradientWithNormalConeRemainder_of_tiltedCertificate
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {xStar h : E} (hxStarQ : xStar ∈ Q)
    (htilt :
      ∃ p : E,
        p ∈
          ∂
            (fun z : E ↦
              ((withTopRealPart f z + inner ℝ (-h) z : ℝ) : WithTop ℝ))
            (xStar) ∧
          p ∈ N[Q] xStar) :
    ∃ gStar ∈ ∂ f(xStar), gStar - h ∈ N[Q] xStar := by
  rcases htilt with ⟨p, hpTilt, hpNormal⟩
  let gStar : E := p + h
  have hxStarDom : xStar ∈ dom f := interior_subset (hQ_subset_interior hxStarQ)
  have hgStar : gStar ∈ ∂ f(xStar) := by
    rw [mem_subdifferential_iff]
    refine ⟨hxStarDom, ?_⟩
    intro y hyDom
    have hpReal :=
      mem_subdifferential_coe_real_iff.mp hpTilt y
    have hinner :
        inner ℝ h (y - xStar) = inner ℝ h y - inner ℝ h xStar := by
      rw [inner_sub_right]
    -- Rearrange the tilted subgradient inequality back to the original objective.
    have hreal :
        withTopRealPart f xStar + inner ℝ (p + h) (y - xStar) ≤ withTopRealPart f y := by
      rw [inner_add_left, hinner]
      rw [inner_neg_left, inner_neg_left] at hpReal
      linarith
    rw [← coe_withTopRealPart hyDom, ← coe_withTopRealPart hxStarDom]
    exact_mod_cast hreal
  have hnormal : gStar - h ∈ N[Q] xStar := by
    simpa [gStar]
      using hpNormal
  exact ⟨gStar, hgStar, hnormal⟩

/-- Helper for Theorem 3.1.27: at an interior effective-domain point, the subdifferential of a
convex extended-valued objective is compact and convex. -/
lemma subdifferentialCompactConvex_of_convexOn_of_mem_interior
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {xStar : E} (hxStar : xStar ∈ interior (dom f)) :
    IsCompact (∂ f(xStar)) ∧ Convex ℝ (∂ f(xStar)) := by
  have hbounded :
      Bornology.IsBounded (∂ f(xStar)) :=
    (subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
      hf hxStar).2
  have hclosed : IsClosed (∂ f(xStar) : Set E) :=
    isClosedSubdifferentialAt (f := f) (x := xStar) (interior_subset hxStar)
  have hconv :
      Convex ℝ (∂ f(xStar)) := by
    -- Rewrite the ambient subdifferential as the constrained one on `dom f`, where convexity is
    -- already packaged.
    simpa [constrainedSubdifferential_dom_eq_subdifferential (f := f) (x := xStar)] using
      (convex_constrainedSubdifferential (Q := dom f) (f := f) (x := xStar))
  exact ⟨Metric.isCompact_of_isClosed_isBounded hclosed hbounded, hconv⟩

/-- Helper for Theorem 3.1.27: an interior-point subdifferential admits a closest point to the
normal cone, and the resulting closest pair satisfies the usual projection inequalities. -/
lemma existsClosestSubgradientNormalConePair_of_convexOn_of_mem_interior
    {Q : Set E} {f : E → WithTop ℝ} {xStar : E}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hxStar : xStar ∈ interior (dom f)) :
    ∃ g1Star ∈ ∂ f(xStar),
      ∃ g2Star ∈ N[Q] xStar,
        (∀ g1 ∈ ∂ f(xStar),
            inner ℝ (g2Star - g1Star) (g1 - g1Star) ≤ 0) ∧
          (∀ g2 ∈ N[Q] xStar,
            inner ℝ (g1Star - g2Star) (g2 - g2Star) ≤ 0) := by
  let S : Set E := ∂ f(xStar)
  let N : Set E := N[Q] xStar
  have hS_nonempty : S.Nonempty := by
    -- Interior points of a convex effective domain admit at least one ambient subgradient.
    simpa [S] using
      (subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
        hf hxStar).1
  have hS_compact : IsCompact S := by
    -- Compactness packages the closest-subgradient choice.
    simpa [S] using
      (subdifferentialCompactConvex_of_convexOn_of_mem_interior hf hxStar).1
  have hS_convex : Convex ℝ S := by
    simpa [S] using
      (subdifferentialCompactConvex_of_convexOn_of_mem_interior hf hxStar).2
  have hinf_cont : ContinuousOn (fun g : E ↦ Metric.infDist g N) S := by
    simpa [N] using (Metric.continuous_infDist_pt N).continuousOn
  rcases hS_compact.exists_isMinOn hS_nonempty hinf_cont with ⟨g1Star, hg1Star, hg1Min⟩
  have hzero_mem : (0 : E) ∈ N := by
    -- The normal cone is a cone, hence contains `0`.
    change (0 : E) ∈ N[Q] xStar
    rw [mem_normalCone_iff]
    intro x hx
    simp
  have hN_nonempty : N.Nonempty := ⟨0, hzero_mem⟩
  have hN_closed : IsClosed N := by
    simpa [N] using (N[Q] xStar : ProperCone ℝ E).isClosed
  have hN_convex : Convex ℝ N := by
    simpa [N] using (N[Q] xStar : ProperCone ℝ E).convex
  rcases exists_unique_projection_point_of_nonempty_closed_convex
      N hN_nonempty hN_closed hN_convex g1Star with ⟨g2Star, hprojN, _⟩
  have hprojS : IsProjectionPointOn S g2Star g1Star := by
    -- Minimizing the distance to `N[Q] xStar` over `S` turns `g1Star` into a projection point.
    refine (IsProjectionPointOn.iff_isMinOn).2 ?_
    refine ⟨hg1Star, ?_⟩
    rw [isMinOn_iff]
    intro g1 hg1
    have hdist_le : dist g2Star g1Star ≤ dist g2Star g1 := by
      calc
        dist g2Star g1Star = Metric.infDist g1Star N := by
          simpa [dist_comm] using hprojN.2
        _ ≤ Metric.infDist g1 N := (isMinOn_iff.mp hg1Min) g1 hg1
        _ ≤ dist g1 g2Star := Metric.infDist_le_dist_of_mem hprojN.1
        _ = dist g2Star g1 := by rw [dist_comm]
    simpa [dist_eq_norm, norm_sub_rev] using hdist_le
  refine ⟨g1Star, hg1Star, g2Star, hprojN.1, ?_, ?_⟩
  · intro g1 hg1
    -- The projection inequality on the compact subdifferential gives the first closest-pair
    -- variational inequality.
    have hineq : 0 ≤ inner ℝ (g1Star - g2Star) (g1 - g1Star) :=
      hprojS.inner_sub_nonneg hS_convex hg1
    simpa [sub_eq_add_neg, inner_add_left, inner_neg_left] using neg_nonpos.mpr hineq
  · intro g2 hg2
    -- The projection inequality on the normal cone gives the second closest-pair variational
    -- inequality.
    have hineq : 0 ≤ inner ℝ (g2Star - g1Star) (g2 - g2Star) :=
      hprojN.inner_sub_nonneg hN_convex hg2
    simpa [sub_eq_add_neg, inner_add_left, inner_neg_left] using neg_nonpos.mpr hineq

/-- Helper for Theorem 3.1.27: an extended-valued constrained minimizer has nonnegative convex
directional derivative along every feasible displacement. -/
lemma directionalDerivativeReal_nonneg_on_feasibleDisplacement_of_isMinOn_of_mem_interior
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {xStar : E} (hxStar : xStar ∈ Q)
    (hmin : IsMinOn (withTopRealPart f) Q xStar)
    {x : E} (hx : x ∈ Q) :
    0 ≤ convexDirectionalDerivativeReal f (hQ_subset_interior hxStar) (x - xStar) := by
  let hxInt : xStar ∈ interior (dom f) := hQ_subset_interior hxStar
  have hlt : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  have hquot_nonneg :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        0 ≤ (withTopRealPart f (xStar + α • (x - xStar)) - withTopRealPart f xStar) / α := by
    -- Along a feasible segment, every forward secant quotient is nonnegative because `xStar`
    -- minimizes the finite real part on `Q`.
    filter_upwards [self_mem_nhdsWithin, hlt] with α hαpos hαlt
    have hseg : xStar + α • (x - xStar) ∈ segment ℝ xStar x := by
      rw [segment_eq_image']
      exact ⟨α, ⟨le_of_lt hαpos, le_of_lt hαlt⟩, rfl⟩
    have hfeas : xStar + α • (x - xStar) ∈ Q := hQ_convex.segment_subset hxStar hx hseg
    have hmin_ineq :
        withTopRealPart f xStar ≤ withTopRealPart f (xStar + α • (x - xStar)) :=
      (isMinOn_iff.mp hmin) _ hfeas
    have hsub : 0 ≤ withTopRealPart f (xStar + α • (x - xStar)) - withTopRealPart f xStar := by
      linarith
    simpa using div_nonneg hsub hαpos.le
  have hzero : Filter.Tendsto (fun _ : ℝ ↦ 0) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds
  have hsecant :=
    tendsto_directionalSecantQuotient_of_mem_interior hf hxInt (x - xStar)
  -- Passing to the limit preserves the secant-quotient lower bound at `0`.
  exact le_of_tendsto_of_tendsto hzero hsecant hquot_nonneg

/-- Helper for Theorem 3.1.27: the same nonnegativity extends from feasible displacements to the
pointed cone hull generated by them. -/
lemma directionalDerivativeReal_nonneg_on_pointedConeHull_of_isMinOn_of_mem_interior
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {xStar : E} (hxStar : xStar ∈ Q)
    (hmin : IsMinOn (withTopRealPart f) Q xStar)
    {p : E} (hp : p ∈ PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E))) :
    0 ≤ convexDirectionalDerivativeReal f (hQ_subset_interior hxStar) p := by
  let hxInt : xStar ∈ interior (dom f) := hQ_subset_interior hxStar
  rcases exists_nonneg_smul_vsub_of_mem_pointedConeHull hQ_convex hxStar hp with
    ⟨r, hr, x, hx, rfl⟩
  have hdisp :
      0 ≤ convexDirectionalDerivativeReal f hxInt (x - xStar) :=
    directionalDerivativeReal_nonneg_on_feasibleDisplacement_of_isMinOn_of_mem_interior
      hQ_convex hf hQ_subset_interior hxStar hmin hx
  have hzero :
      convexDirectionalDerivativeReal f hxInt (0 : E) = 0 := by
    -- The zero direction has zero directional derivative by uniqueness against the constant slice.
    have howner :
        HasDirectionalDerivAt (withTopToEReal ∘ f) xStar (0 : E)
          (convexDirectionalDerivativeReal f hxInt (0 : E)) :=
      convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hxInt 0
    have hconst :
        HasDirectionalDerivAt (withTopToEReal ∘ f) xStar (0 : E) 0 :=
      HasDirectionalDerivAt.zero
        (f := withTopToEReal ∘ f)
        (x := xStar)
        (mem_dom_withTopToEReal_comp_of_mem_dom (interior_subset hxInt))
    exact HasDirectionalDerivAt.unique howner hconst
  have hscale :
      convexDirectionalDerivativeReal f hxInt (r • (x - xStar)) =
        r * convexDirectionalDerivativeReal f hxInt (x - xStar) := by
    -- Positive homogeneity transports the feasible-displacement estimate to the whole cone hull.
    by_cases hr0 : r = 0
    · subst hr0
      simp [hzero]
    · have hr_pos : 0 < r := lt_of_le_of_ne hr (by simpa [eq_comm] using hr0)
      rw [convexDirectionalDerivativeReal_apply, convexDirectionalDerivativeReal_apply]
      rw [convexDirectionalDerivative_smul
        (f := f)
        (hx := interior_subset hxInt) hr_pos (x - xStar)]
      simp [EReal.toReal_mul]
  rw [hscale]
  exact mul_nonneg hr hdisp

/-- Helper for Theorem 3.1.27: an extended-valued constrained minimizer has nonnegative convex
directional derivative on the whole tangent cone. -/
lemma directionalDerivativeReal_nonneg_on_tangentCone_of_isMinOn_of_mem_interior
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {xStar : E} (hxStar : xStar ∈ Q)
    (hmin : IsMinOn (withTopRealPart f) Q xStar)
    {p : E} (hp : p ∈ 𝒯[Q] xStar) :
    0 ≤ convexDirectionalDerivativeReal f (hQ_subset_interior hxStar) p := by
  let hxInt : xStar ∈ interior (dom f) := hQ_subset_interior hxStar
  let dderiv : E → ℝ := convexDirectionalDerivativeReal f hxInt
  let C : Set E := {q : E | 0 ≤ dderiv q}
  have hcont : Continuous dderiv := by
    -- The interior-point convex directional derivative is continuous on all directions.
    rw [← continuousOn_univ]
    simpa [dderiv] using
      (convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior
        (f := f) hf hxInt).continuousOn_interior
  have hclosed : IsClosed C := by
    simpa [C] using isClosed_Ici.preimage hcont
  have hsubset :
      (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E) ⊆ C := by
    -- The pointed cone hull is the dense generating cone of tangent directions.
    intro q hq
    exact directionalDerivativeReal_nonneg_on_pointedConeHull_of_isMinOn_of_mem_interior
      hQ_convex hf hQ_subset_interior hxStar hmin hq
  have hp' : p ∈ closure (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E) := by
    -- Lemma 3.1.18 identifies the tangent cone with the closure of the pointed feasible hull.
    rw [posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton Q hQ_convex xStar hxStar] at hp
    simpa using hp
  have hclosure :
      closure (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set E)) : Set E) ⊆ C := by
    exact hclosed.closure_subset_iff.2 hsubset
  exact hclosure hp'

/-- Helper for Theorem 3.1.27: for an interior-point convex objective, the subgradient-side
projection inequality forces a strictly negative directional derivative along the closest-pair
gap. -/
lemma closestPairDirectionalDerivative_lt_zero_of_convexOn_of_mem_interior
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {xStar g1Star g2Star : E}
    (hdisj : Disjoint (∂ f(xStar)) ({g2Star} : Set E))
    (hg1Star : g1Star ∈ ∂ f(xStar))
    (hproj :
      ∀ g1 ∈ ∂ f(xStar),
        inner ℝ (g2Star - g1Star) (g1 - g1Star) ≤ 0)
    (hzeroPair : inner ℝ g2Star (g2Star - g1Star) = 0)
    (hxStar : xStar ∈ interior (dom f)) :
    convexDirectionalDerivativeReal f hxStar (g2Star - g1Star) < 0 := by
  let pStar : E := g2Star - g1Star
  have hmax :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
      (f := f) hf hxStar pStar
  have hupper :
      ∀ g ∈ ∂ f(xStar), inner ℝ g pStar ≤ inner ℝ g1Star pStar := by
    intro g hg
    have hineq : inner ℝ g pStar - inner ℝ g1Star pStar ≤ 0 := by
      calc
        inner ℝ g pStar - inner ℝ g1Star pStar
            = inner ℝ pStar g - inner ℝ pStar g1Star := by
                rw [real_inner_comm g pStar, real_inner_comm g1Star pStar]
        _ = inner ℝ pStar (g - g1Star) := by
              rw [inner_sub_right]
        _ ≤ 0 := hproj g hg
    exact sub_nonpos.mp hineq
  have hmemImage :
      inner ℝ g1Star pStar ∈ (fun g : E ↦ inner ℝ g pStar) '' ∂ f(xStar) := by
    exact ⟨g1Star, hg1Star, rfl⟩
  have hle_max :
      inner ℝ g1Star pStar ≤ convexDirectionalDerivativeReal f hxStar pStar :=
    hmax.2 hmemImage
  have hge_max :
      convexDirectionalDerivativeReal f hxStar pStar ≤ inner ℝ g1Star pStar := by
    rcases hmax.1 with ⟨g, hg, hgEq⟩
    rw [← hgEq]
    exact hupper g hg
  have hvalue :
      convexDirectionalDerivativeReal f hxStar pStar = inner ℝ g1Star pStar := by
    exact le_antisymm hge_max hle_max
  have hg2_not_mem : g2Star ∉ ∂ f(xStar) := by
    rw [Set.disjoint_singleton_right] at hdisj
    exact hdisj
  have hneq : g1Star ≠ g2Star := by
    intro hEq
    apply hg2_not_mem
    simpa [hEq] using hg1Star
  have hp_nonzero : pStar ≠ 0 := sub_ne_zero.mpr hneq.symm
  have hp_norm_sq_pos : 0 < ‖pStar‖ ^ (2 : ℕ) := by
    positivity
  have hpair :
      inner ℝ g1Star pStar = -‖pStar‖ ^ (2 : ℕ) := by
    calc
      inner ℝ g1Star pStar = inner ℝ (g2Star - pStar) pStar := by
        simp [pStar, sub_eq_add_neg, add_left_comm]
      _ = inner ℝ g2Star pStar - inner ℝ pStar pStar := by
        rw [inner_sub_left]
      _ = -‖pStar‖ ^ (2 : ℕ) := by
        simp [pStar, hzeroPair]
  rw [hvalue, hpair]
  linarith

/-- Helper for Theorem 3.1.27: an interior constrained minimizer of an extended-valued convex
objective admits an ambient subgradient lying in the normal cone. -/
lemma existsSubgradientMemNormalCone_of_isMinOn_of_mem_interior
    {Q : Set E} (hQ_convex : Convex ℝ Q)
    {f : E → WithTop ℝ} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {xStar : E} (hxStar : xStar ∈ Q)
    (hmin : IsMinOn (withTopRealPart f) Q xStar) :
    ∃ gStar : E, gStar ∈ ∂ f(xStar) ∧ gStar ∈ N[Q] xStar := by
  let S : Set E := ∂ f(xStar)
  let hxInt : xStar ∈ interior (dom f) := hQ_subset_interior hxStar
  by_contra hno
  have hnone :
      ∀ g : E, g ∈ S → g ∉ N[Q] xStar := by
    intro g hgS hgN
    exact hno ⟨g, hgS, hgN⟩
  rcases existsClosestSubgradientNormalConePair_of_convexOn_of_mem_interior hf hxInt with
    ⟨g1Star, hg1Star, g2Star, hg2Star, hprojS, hprojN⟩
  have hg2_not_mem : g2Star ∉ S := by
    intro hg2S
    exact hno ⟨g2Star, hg2S, hg2Star⟩
  have hdisj_singleton : Disjoint S ({g2Star} : Set E) := by
    rw [Set.disjoint_singleton_right]
    exact hg2_not_mem
  have htan : g2Star - g1Star ∈ 𝒯[Q] xStar :=
    closest_pair_direction_mem_tangentCone hQ_convex hxStar hg2Star hprojN
  have hnonneg :
      0 ≤ convexDirectionalDerivativeReal f hxInt (g2Star - g1Star) :=
    directionalDerivativeReal_nonneg_on_tangentCone_of_isMinOn_of_mem_interior
      hQ_convex hf hQ_subset_interior hxStar hmin htan
  have hzeroPair :
      inner ℝ g2Star (g2Star - g1Star) = 0 :=
    normal_projection_gap_pairing_eq_zero hg2Star hprojN
  have hlt :
      convexDirectionalDerivativeReal f hxInt (g2Star - g1Star) < 0 :=
    closestPairDirectionalDerivative_lt_zero_of_convexOn_of_mem_interior
      hf hdisj_singleton hg1Star hprojS hzeroPair hxInt
  linarith

/-- Helper for Theorem 3.1.27: tilting by a finite linear functional does not change the
effective domain. -/
lemma dom_tiltedObjective_eq
    {f : E → WithTop ℝ} {h : E} :
    dom (fun z : E ↦ f z + (inner ℝ (-h) z : WithTop ℝ)) = dom f := by
  ext z
  rw [mem_withTopEffectiveDomain_iff, mem_withTopEffectiveDomain_iff]
  constructor
  · intro hz
    rw [WithTop.add_lt_top] at hz
    exact hz.1
  · intro hz
    rw [WithTop.add_lt_top]
    refine ⟨hz, ?_⟩
    simpa [inner_neg_left] using (WithTop.coe_lt_top (inner ℝ (-h) z))

/-- Helper for Theorem 3.1.27: on the effective domain, the tilted objective adds the linear term
to the finite real part. -/
lemma withTopRealPart_tiltedObjective_eq_of_mem_dom
    {f : E → WithTop ℝ} {h : E} {x : E}
    (hx : x ∈ dom f) :
    withTopRealPart (fun z : E ↦ f z + (inner ℝ (-h) z : WithTop ℝ)) x =
      withTopRealPart f x + inner ℝ (-h) x := by
  have hxTilt : x ∈ dom (fun z : E ↦ f z + (inner ℝ (-h) z : WithTop ℝ)) := by
    rw [dom_tiltedObjective_eq (f := f) (h := h)]
    exact hx
  apply WithTop.coe_injective
  rw [coe_withTopRealPart hxTilt, ← coe_withTopRealPart hx]
  simp

/-- Helper for Theorem 3.1.27: decompose a constrained subgradient into an ambient subgradient
plus a normal-cone remainder by passing to the tilted extended-valued objective. -/
lemma existsSubgradientWithNormalConeRemainderOfMemConstrainedSubdifferential
    {Q : Set E} {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hfQ : ConvexOn ℝ Q (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {xStar h : E} (hxStarQ : xStar ∈ Q)
    (hh : h ∈ ∂[Q] f(xStar)) :
    ∃ gStar ∈ ∂ f(xStar), gStar - h ∈ N[Q] xStar := by
  let fTilt : E → WithTop ℝ := fun z ↦ f z + (inner ℝ (-h) z : WithTop ℝ)
  have hlinear : ConvexOn ℝ Q (fun z : E ↦ inner ℝ (-h) z) := by
    let ℓ : E →ᵃ[ℝ] ℝ :=
      AffineMap.const ℝ E 0 + ((innerSL ℝ (-h)).toLinearMap).toAffineMap
    have hℓ : ConvexOn ℝ Set.univ (ℓ : E → ℝ) := by
      simpa [Function.comp, ℓ] using (convexOn_id convex_univ).comp_affineMap ℓ
    refine ⟨hfQ.1, ?_⟩
    intro z hz w hw a b ha hb hab
    simpa [ℓ, innerSL_apply_apply, add_assoc, add_left_comm, add_comm] using
      hℓ.2 (by simp) (by simp) ha hb hab
  have hlinearDom : ConvexOn ℝ (dom f) (fun z : E ↦ inner ℝ (-h) z) := by
    let ℓ : E →ᵃ[ℝ] ℝ :=
      AffineMap.const ℝ E 0 + ((innerSL ℝ (-h)).toLinearMap).toAffineMap
    have hℓ : ConvexOn ℝ Set.univ (ℓ : E → ℝ) := by
      simpa [Function.comp, ℓ] using (convexOn_id convex_univ).comp_affineMap ℓ
    refine ⟨hf.1, ?_⟩
    intro z hz w hw a b ha hb hab
    simpa [ℓ, innerSL_apply_apply, add_assoc, add_left_comm, add_comm] using
      hℓ.2 (by simp) (by simp) ha hb hab
  have hsumConv :
      ConvexOn ℝ (dom f) (withTopRealPart f + fun z : E ↦ inner ℝ (-h) z) :=
    hf.add hlinearDom
  have hdomTilt : dom fTilt = dom f := dom_tiltedObjective_eq (f := f) (h := h)
  have htiltConv : ConvexOn ℝ (dom fTilt) (withTopRealPart fTilt) := by
    refine ⟨?_, ?_⟩
    · simpa [hdomTilt] using hsumConv.1
    · intro x hx y hy a b ha hb hab
      have hxDom : x ∈ dom f := by
        rwa [hdomTilt] at hx
      have hyDom : y ∈ dom f := by
        rwa [hdomTilt] at hy
      have hxyDom : a • x + b • y ∈ dom f := hsumConv.1 hxDom hyDom ha hb hab
      rw [withTopRealPart_tiltedObjective_eq_of_mem_dom (f := f) (h := h) hxyDom,
        withTopRealPart_tiltedObjective_eq_of_mem_dom (f := f) (h := h) hxDom,
        withTopRealPart_tiltedObjective_eq_of_mem_dom (f := f) (h := h) hyDom]
      simpa [Pi.add_apply] using hsumConv.2 hxDom hyDom ha hb hab
  have hminTilt : IsMinOn (fun z : E ↦ withTopRealPart f z + inner ℝ (-h) z) Q xStar := by
    exact
      (mem_constrainedSubdifferential_iff_isMinOn_tilted
        (Q := Q) (f := f) hQ_subset_interior
        (xStar := xStar) (h := h)).mp hh |>.2
  have hQ_subset_interiorTilt : Q ⊆ interior (dom fTilt) := by
    intro x hxQ
    simpa [hdomTilt] using hQ_subset_interior hxQ
  have hminTiltTop : IsMinOn (withTopRealPart fTilt) Q xStar := by
    refine isMinOn_iff.mpr ?_
    intro x hxQ
    have hxDom : x ∈ dom f := interior_subset (hQ_subset_interior hxQ)
    have hxStarDom : xStar ∈ dom f := interior_subset (hQ_subset_interior hxStarQ)
    rw [withTopRealPart_tiltedObjective_eq_of_mem_dom (f := f) (h := h) hxStarDom,
      withTopRealPart_tiltedObjective_eq_of_mem_dom (f := f) (h := h) hxDom]
    exact (isMinOn_iff.mp hminTilt) x hxQ
  -- Route correction: instead of searching for a standalone real-valued tilted certificate, apply
  -- the interior-domain normal-cone criterion directly to the extended-valued tilt `fTilt`.
  rcases existsSubgradientMemNormalCone_of_isMinOn_of_mem_interior
      (Q := Q) hfQ.1 htiltConv hQ_subset_interiorTilt hxStarQ hminTiltTop with
    ⟨p, hpSub, hpNormal⟩
  have hpShift : p + h ∈ ∂ f(xStar) := by
    have hxStarDom : xStar ∈ dom f := interior_subset (hQ_subset_interior hxStarQ)
    rw [mem_subdifferential_iff] at hpSub ⊢
    rcases hpSub with ⟨hxTiltDom, hpSub⟩
    refine ⟨hxStarDom, ?_⟩
    intro y hyDom
    have hyTiltDom : y ∈ dom fTilt := by
      rwa [hdomTilt]
    have hpIneq := hpSub hyTiltDom
    rw [← coe_withTopRealPart hyTiltDom, ← coe_withTopRealPart hxTiltDom] at hpIneq
    have hpReal :
        withTopRealPart fTilt xStar + inner ℝ p (y - xStar) ≤ withTopRealPart fTilt y := by
      exact_mod_cast hpIneq
    rw [withTopRealPart_tiltedObjective_eq_of_mem_dom (f := f) (h := h) hxStarDom,
      withTopRealPart_tiltedObjective_eq_of_mem_dom (f := f) (h := h) hyDom] at hpReal
    rw [inner_neg_left, inner_neg_left] at hpReal
    have hinner : inner ℝ h (y - xStar) = inner ℝ h y - inner ℝ h xStar := by
      rw [inner_sub_right]
    have hreal :
        withTopRealPart f xStar + inner ℝ (p + h) (y - xStar) ≤ withTopRealPart f y := by
      rw [inner_add_left, hinner]
      linarith
    rw [← coe_withTopRealPart hyDom, ← coe_withTopRealPart hxStarDom]
    exact_mod_cast hreal
  refine ⟨p + h, hpShift, ?_⟩
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hpNormal

/-- Helper for Theorem 3.1.27: the Slater ball around `xBar` lets us top-extend `f` off `Q` and
recover a constrained subgradient at the center `xBar`. -/
lemma constrainedSubdifferentialNonemptyAtSlaterCenter
    {Q : Set E} {f : E → WithTop ℝ}
    (hfQ : ConvexOn ℝ Q (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {xBar : E} {ε : ℝ} (hε : 0 < ε) (hball : Metric.ball xBar ε ⊆ Q) :
    (∂[Q] f(xBar)).Nonempty := by
  classical
  let fQ : E → WithTop ℝ := fun y ↦ if y ∈ Q then f y else ⊤
  have hxBarQ : xBar ∈ Q := hball (Metric.mem_ball_self hε)
  have hdom_fQ : dom fQ = Q := by
    ext y
    constructor
    · intro hy
      by_cases hyQ : y ∈ Q
      · exact hyQ
      · simpa [fQ, hyQ] using hy
    · intro hyQ
      have hyDom : y ∈ dom f := interior_subset (hQ_subset_interior hyQ)
      simpa [fQ, hyQ] using hyDom
  have hconv_fQ : ConvexOn ℝ (dom fQ) (withTopRealPart fQ) := by
    rw [hdom_fQ]
    refine ⟨hfQ.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxyQ : a • x + b • y ∈ Q := hfQ.1 hx hy ha hb hab
    simpa [fQ, hx, hy, hxyQ] using hfQ.2 hx hy ha hb hab
  have hxBarInteriorQ : xBar ∈ interior Q := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)) hball
  have hxBarInterior_fQ : xBar ∈ interior (dom fQ) := by
    simpa [hdom_fQ] using hxBarInteriorQ
  rcases subdifferential_nonempty_of_convexOn_of_mem_interior hconv_fQ hxBarInterior_fQ with
    ⟨g, hg⟩
  have htopBridge :
      g ∈ ∂ (fun y ↦ if y ∈ Q then f y else ⊤)(xBar) ↔ g ∈ ∂[Q] f(xBar) := by
    rw [mem_subdifferential_iff, mem_constrainedSubdifferential_iff]
    constructor
    · rintro ⟨hxExt, hminorant⟩
      have hxBarDom : xBar ∈ dom f := interior_subset (hQ_subset_interior hxBarQ)
      refine ⟨hxBarQ, hxBarDom, ?_⟩
      intro y hyQ
      by_cases hyDom : y ∈ dom f
      · have hyExt : y ∈ dom (fun z ↦ if z ∈ Q then f z else ⊤) := by
          simpa [hyQ] using hyDom
        simpa [hyQ, hxBarQ] using hminorant hyExt
      · have hytop : f y = ⊤ := top_unique (le_of_not_gt hyDom)
        simp [hyQ, hxBarQ, hytop]
    · rintro ⟨hxBarQ', hxBarDom, hminorant⟩
      refine ⟨?_, ?_⟩
      · simpa [hxBarQ'] using hxBarDom
      · intro y hyExt
        have hyQ : y ∈ Q := by
          by_contra hyQ
          exfalso
          simpa [hyQ] using hyExt
        simpa [hyQ, hxBarQ'] using hminorant hyQ
  refine ⟨g, ?_⟩
  exact htopBridge.mp <| by simpa [fQ] using hg

/-- Helper for Theorem 3.1.27: bounded constrained sublevel sets and one constrained subgradient
at the Slater center produce a global lower bound for `withTopRealPart f` on `Q`. -/
lemma exists_lowerBound_on_Q_of_bounded_constrainedSublevels
    {Q : Set E} {f : E → WithTop ℝ}
    (hfQ : ConvexOn ℝ Q (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    (hlevel_bounded : ∀ α : ℝ, Bornology.IsBounded (constrainedSublevelSet Q f α))
    {xBar : E} {ε : ℝ} (hε : 0 < ε) (hball : Metric.ball xBar ε ⊆ Q) :
    ∃ m : ℝ, ∀ x : E, x ∈ Q → m ≤ withTopRealPart f x := by
  have hxBarQ : xBar ∈ Q := hball (Metric.mem_ball_self hε)
  rcases constrainedSubdifferentialNonemptyAtSlaterCenter
      hfQ hQ_subset_interior hε hball with
    ⟨gBar, hgBar⟩
  have hxBarDom : xBar ∈ dom f := interior_subset (hQ_subset_interior hxBarQ)
  let α0 : ℝ := withTopRealPart f xBar
  let S0 : Set E := constrainedSublevelSet Q f α0
  have hxBarS0 : xBar ∈ S0 := by
    refine mem_constrainedSublevelSet_iff.2 ⟨hxBarQ, ?_⟩
    change f xBar ≤ ((withTopRealPart f xBar : ℝ) : WithTop ℝ)
    rw [coe_withTopRealPart hxBarDom]
  have hS0_bounded : Bornology.IsBounded S0 := hlevel_bounded α0
  obtain ⟨R, hS0_subset⟩ := (Metric.isBounded_iff_subset_closedBall xBar).mp hS0_bounded
  have hR_nonneg : 0 ≤ R := by
    have hxBarClosed : xBar ∈ Metric.closedBall xBar R := hS0_subset hxBarS0
    simpa [Metric.mem_closedBall] using hxBarClosed
  refine ⟨α0 - ‖gBar‖ * R, ?_⟩
  intro x hxQ
  by_cases hxS0 : x ∈ S0
  · have hxDom : x ∈ dom f := interior_subset (hQ_subset_interior hxQ)
    have hxNorm : ‖x - xBar‖ ≤ R := by
      have hxClosed : x ∈ Metric.closedBall xBar R := hS0_subset hxS0
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxClosed
    -- On the reference sublevel set, the constrained subgradient gives an affine minorant.
    have hsupport :
        α0 + inner ℝ gBar (x - xBar) ≤ withTopRealPart f x := by
      simpa [α0] using
        withTopRealPart_le_of_mem_constrainedSubdifferential Q f hgBar hxQ hxDom
    have hinner_norm : ‖inner ℝ gBar (x - xBar)‖ ≤ ‖gBar‖ * ‖x - xBar‖ :=
      norm_inner_le_norm _ _
    have hinner_lower : -‖gBar‖ * R ≤ inner ℝ gBar (x - xBar) := by
      have hmul : ‖gBar‖ * ‖x - xBar‖ ≤ ‖gBar‖ * R :=
        mul_le_mul_of_nonneg_left hxNorm (norm_nonneg _)
      have habs : |inner ℝ gBar (x - xBar)| ≤ ‖gBar‖ * R := by
        exact le_trans (by simpa using hinner_norm) hmul
      simpa using (abs_le.mp habs).1
    linarith
  · -- Outside the reference sublevel set, the value is already strictly above `α0`.
    have houtside : α0 < withTopRealPart f x := by
      by_contra hnotlt
      have hxDom : x ∈ dom f := interior_subset (hQ_subset_interior hxQ)
      apply hxS0
      refine mem_constrainedSublevelSet_iff.2 ⟨hxQ, ?_⟩
      rw [← coe_withTopRealPart hxDom]
      exact_mod_cast (le_of_not_gt hnotlt)
    have hbase : α0 - ‖gBar‖ * R ≤ α0 := by
      nlinarith [norm_nonneg gBar, hR_nonneg]
    linarith

/-- Helper for Theorem 3.1.27: the equality-fiber affine value function is convex on its
finite-value domain. -/
lemma affineValueFunctionConvexOn
    {Q : Set E} {f : E → WithTop ℝ}
    (hfQ : ConvexOn ℝ Q (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {A : E →ₗ[ℝ] Λ}
    (hlower : ∃ m : ℝ, ∀ x : E, x ∈ Q → m ≤ withTopRealPart f x) :
    let ψ : Λ → EReal :=
      partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
        (withTopToEReal ∘ f ∘ Prod.snd)
    ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ) := by
  classical
  let S : Set (Λ × E) := {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
  let φQ : Λ × E → EReal := fun p ↦ withTopToEReal (if p.2 ∈ Q then f p.2 else ⊤)
  let ψ : Λ → EReal := partialInfProjection S (withTopToEReal ∘ f ∘ Prod.snd)
  let ψQ : Λ → EReal := partialInfProjection S φQ
  obtain ⟨m, hm⟩ := hlower
  have hS_convex : Convex ℝ S := by
    intro p hp q hq a b ha hb hab
    rcases mem_linearEqualityFeasibleSet_iff.mp hp with ⟨hpQ, hpA⟩
    rcases mem_linearEqualityFeasibleSet_iff.mp hq with ⟨hqQ, hqA⟩
    refine mem_linearEqualityFeasibleSet_iff.mpr ⟨hfQ.1 hpQ hqQ ha hb hab, ?_⟩
    -- The linear equality constraint is preserved by convex combinations.
    calc
      A ((a • p + b • q).2) = A (a • p.2 + b • q.2) := by simp
      _ = a • A p.2 + b • A q.2 := by simp
      _ = a • p.1 + b • q.1 := by rw [hpA, hqA]
      _ = (a • p + b • q).1 := by simp
  have hdomφQ : dom φQ = {p : Λ × E | p.2 ∈ Q} := by
    ext p
    constructor
    · intro hp
      by_cases hpQ : p.2 ∈ Q
      · exact hpQ
      · exfalso
        rw [mem_extendedRealEffectiveDomain_iff] at hp
        have htop : φQ p = ⊤ := by
          dsimp [φQ]
          rw [if_neg hpQ, withTopToEReal]
          rfl
        exact hp.1 htop
    · intro hpQ
      have hpQ' : p.2 ∈ Q := by simpa using hpQ
      have hpDom : p.2 ∈ dom f := interior_subset (hQ_subset_interior hpQ')
      have hpNeTop : f p.2 ≠ ⊤ := by
        rw [mem_withTopEffectiveDomain_iff] at hpDom
        exact ne_of_lt hpDom
      rw [mem_extendedRealEffectiveDomain_iff]
      constructor
      · dsimp [φQ]
        rw [if_pos hpQ']
        exact withTopToEReal_ne_top_of_mem_dom hpDom
      · dsimp [φQ]
        rw [if_pos hpQ']
        exact withTopToEReal_ne_bot_of_mem_dom hpDom
  have hφQ_real :
      ∀ p : Λ × E, p ∈ dom φQ → extendedRealRealPart φQ p = withTopRealPart f p.2 := by
    intro p hp
    have hpQ : p.2 ∈ Q := by simpa [hdomφQ] using hp
    have hpDom : p.2 ∈ dom f := interior_subset (hQ_subset_interior hpQ)
    apply EReal.coe_injective
    rw [coe_extendedRealRealPart hp]
    dsimp [φQ]
    rw [if_pos hpQ]
    simpa [withTopToEReal] using
      (congrArg withTopToEReal (coe_withTopRealPart hpDom)).symm
  have hφQ_convex : ConvexOn ℝ (dom φQ) (extendedRealRealPart φQ) := by
    refine ⟨?_, ?_⟩
    · rw [hdomφQ]
      intro p hp q hq a b ha hb hab
      simpa using hfQ.1 hp hq ha hb hab
    · intro p hp q hq a b ha hb hab
      have hpQ : p.2 ∈ Q := by simpa [hdomφQ] using hp
      have hqQ : q.2 ∈ Q := by simpa [hdomφQ] using hq
      have hpqDom : a • p + b • q ∈ dom φQ := by
        rw [hdomφQ]
        simpa using hfQ.1 hpQ hqQ ha hb hab
      rw [hφQ_real _ hpqDom, hφQ_real _ hp, hφQ_real _ hq]
      simpa using hfQ.2 hpQ hqQ ha hb hab
  have hψ_eq : ψQ = ψ := by
    funext u
    let T : Set (Λ × E) := {z : Λ × E | z ∈ S ∧ z.1 = u}
    have himage :
        φQ '' T = (withTopToEReal ∘ f ∘ Prod.snd) '' T := by
      ext a
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzQ : z.2 ∈ Q := (mem_linearEqualityFeasibleSet_iff.mp hz.1).1
        refine ⟨z, hz, ?_⟩
        simp [φQ, hzQ, Function.comp, withTopToEReal]
      · rintro ⟨z, hz, rfl⟩
        have hzQ : z.2 ∈ Q := (mem_linearEqualityFeasibleSet_iff.mp hz.1).1
        refine ⟨z, hz, ?_⟩
        simp [φQ, hzQ, Function.comp, withTopToEReal]
    -- The feasible fibers already force `z.2 ∈ Q`, so the top-extension leaves each fiber
    -- image unchanged.
    change sInf (φQ '' T) = sInf ((withTopToEReal ∘ f ∘ Prod.snd) '' T)
    simpa [T] using congrArg sInf himage
  have hQdom : S ⊆ dom φQ := by
    intro p hp
    rw [hdomφQ]
    exact (mem_linearEqualityFeasibleSet_iff.mp hp).1
  have hfinite :
      ∀ ⦃u : Λ⦄, (∃ x : E, (u, x) ∈ S) → u ∈ dom ψQ := by
    intro u hu
    rcases hu with ⟨x, hxS⟩
    have hxQ : x ∈ Q := (mem_linearEqualityFeasibleSet_iff.mp hxS).1
    have hxDom : x ∈ dom f := interior_subset (hQ_subset_interior hxQ)
    let T : Set EReal :=
      φQ '' {z : Λ × E | z ∈ S ∧ z.1 = u}
    have hT_nonempty : T.Nonempty := by
      refine ⟨φQ (u, x), ?_⟩
      refine ⟨(u, x), ?_, rfl⟩
      exact ⟨hxS, rfl⟩
    have hxValue : φQ (u, x) = ((withTopRealPart f x : ℝ) : EReal) := by
      simpa [φQ, hxQ, withTopToEReal] using
        (congrArg withTopToEReal (coe_withTopRealPart hxDom)).symm
    have hψQ_upper : ψQ u ≤ ((withTopRealPart f x : ℝ) : EReal) := by
      have hx_mem : φQ (u, x) ∈ T := by
        refine ⟨(u, x), ?_, rfl⟩
        exact ⟨hxS, rfl⟩
      have hupper : ψQ u ≤ φQ (u, x) := by
        simpa [ψQ, T, partialInfProjection_eq_sInf] using
          csInf_le ⟨⊥, by intro a ha; exact bot_le⟩ hx_mem
      simpa [hxValue] using hupper
    have hψQ_lower : ((m : ℝ) : EReal) ≤ ψQ u := by
      have hT_lower : ∀ a ∈ T, ((m : ℝ) : EReal) ≤ a := by
        intro a ha
        rcases ha with ⟨z, hz, rfl⟩
        have hzQ : z.2 ∈ Q := (mem_linearEqualityFeasibleSet_iff.mp hz.1).1
        have hzDom : z.2 ∈ dom f := interior_subset (hQ_subset_interior hzQ)
        have hzValue : φQ z = ((withTopRealPart f z.2 : ℝ) : EReal) := by
          simpa [φQ, hzQ, withTopToEReal] using
            (congrArg withTopToEReal (coe_withTopRealPart hzDom)).symm
        have hmz : m ≤ withTopRealPart f z.2 := hm z.2 hzQ
        have hmzE : ((m : ℝ) : EReal) ≤ ((withTopRealPart f z.2 : ℝ) : EReal) := by
          exact_mod_cast hmz
        simpa [hzValue] using hmzE
      simpa [ψQ, T, partialInfProjection_eq_sInf] using le_csInf hT_nonempty hT_lower
    rw [mem_extendedRealEffectiveDomain_iff]
    constructor
    · intro htop
      rw [htop] at hψQ_upper
      simp at hψQ_upper
    · intro hbot
      rw [hbot] at hψQ_lower
      simp at hψQ_lower
  -- Apply the generic partial-inf-projection convexity theorem to the top-extended objective and
  -- then rewrite back to the original affine value function.
  simpa [ψ, ψQ, hψ_eq] using
    (partialInfProjection_convexOn
      hS_convex hφQ_convex hQdom hfinite)

/-- Helper for Theorem 3.1.27: fiberwise optimality at `xStar` identifies the canonical affine
partial-infimal-projection value at `b` with the finite value `f xStar`. -/
lemma affineValueFunction_eq_of_linearEqualityFeasibleOptimality
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {A : E →ₗ[ℝ] Λ} {b : Λ} {xStar : E}
    (hxStarQ : xStar ∈ Q)
    (hfeasible : A xStar = b)
    (hmin : IsMinOn (withTopRealPart f) (linearEqualityFeasibleSet Q A b) xStar) :
    let ψ : Λ → EReal :=
      partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
        (withTopToEReal ∘ f ∘ Prod.snd)
    b ∈ dom ψ ∧ extendedRealRealPart ψ b = withTopRealPart f xStar := by
  let ψ : Λ → EReal :=
    partialInfProjection
      {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
      (withTopToEReal ∘ f ∘ Prod.snd)
  let S : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = b}
  have hxStarFeas : xStar ∈ linearEqualityFeasibleSet Q A b := by
    exact mem_linearEqualityFeasibleSet_iff.mpr ⟨hxStarQ, hfeasible⟩
  have hxStarDom : xStar ∈ dom f := interior_subset (hQ_subset_interior hxStarQ)
  have hxStarValue :
      ((withTopRealPart f xStar : ℝ) : EReal) = withTopToEReal (f xStar) := by
    simpa [withTopToEReal] using
      congrArg withTopToEReal (coe_withTopRealPart hxStarDom)
  -- The optimal fiber is nonempty because `(b, xStar)` is a feasible witness.
  have hS_nonempty : S.Nonempty := by
    refine ⟨withTopToEReal (f xStar), ?_⟩
    refine ⟨(b, xStar), ?_, rfl⟩
    exact ⟨hxStarFeas, rfl⟩
  -- Every feasible fiber value lies above the value attained at `xStar`.
  have hS_lower : ∀ t ∈ S, withTopToEReal (f xStar) ≤ t := by
    intro t ht
    rcases ht with ⟨z, hz, rfl⟩
    have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A b := by
      simpa [hz.2] using hz.1
    have hzQ : z.2 ∈ Q := (mem_linearEqualityFeasibleSet_iff.mp hzFeas).1
    have hzDom : z.2 ∈ dom f := interior_subset (hQ_subset_interior hzQ)
    have hzValue :
        ((withTopRealPart f z.2 : ℝ) : EReal) = withTopToEReal (f z.2) := by
      simpa [withTopToEReal] using
        congrArg withTopToEReal (coe_withTopRealPart hzDom)
    have hmin' : withTopRealPart f xStar ≤ withTopRealPart f z.2 := by
      exact isMinOn_iff.mp hmin z.2 hzFeas
    have hminEReal :
        ((withTopRealPart f xStar : ℝ) : EReal) ≤
          ((withTopRealPart f z.2 : ℝ) : EReal) := by
      exact_mod_cast hmin'
    calc
      withTopToEReal (f xStar) = ((withTopRealPart f xStar : ℝ) : EReal) := by
        rw [hxStarValue.symm]
      _ ≤ ((withTopRealPart f z.2 : ℝ) : EReal) := hminEReal
      _ = (withTopToEReal ∘ f ∘ Prod.snd) z := by
        simpa [Function.comp] using hzValue
  have hS_bddBelow : BddBelow S := ⟨withTopToEReal (f xStar), hS_lower⟩
  have hψ_upper : ψ b ≤ withTopToEReal (f xStar) := by
    have hxStarMem : withTopToEReal (f xStar) ∈ S := by
      refine ⟨(b, xStar), ?_, rfl⟩
      exact ⟨hxStarFeas, rfl⟩
    simpa [ψ, S, partialInfProjection_eq_sInf] using csInf_le hS_bddBelow hxStarMem
  have hψ_lower : withTopToEReal (f xStar) ≤ ψ b := by
    simpa [ψ, S, partialInfProjection_eq_sInf] using le_csInf hS_nonempty hS_lower
  have hψ :
      ψ b = ((withTopRealPart f xStar : ℝ) : EReal) := by
    calc
      ψ b = withTopToEReal (f xStar) := by exact le_antisymm hψ_upper hψ_lower
      _ = ((withTopRealPart f xStar : ℝ) : EReal) := by rw [← hxStarValue]
  have hbDom : b ∈ dom ψ := by
    rw [mem_extendedRealEffectiveDomain_iff, hψ]
    simp
  refine ⟨hbDom, ?_⟩
  -- Read the finite projected value back through the canonical real-part bridge.
  apply EReal.coe_injective
  rw [coe_extendedRealRealPart hbDom, hψ]

/-- Helper for Theorem 3.1.27: restricting affine-fiber values to the finite-value locus of `f`
does not change the canonical affine value function. -/
lemma affineValueFunction_eq_restrictedRealProjection
    {Q : Set E} {f : E → WithTop ℝ} {A : E →ₗ[ℝ] Λ} :
    partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
        (withTopToEReal ∘ f ∘ Prod.snd) =
      partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
        (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2) := by
  funext u
  let S : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = u}
  let T : Set EReal :=
    (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2) '' {z : Λ × E |
      (z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.2 ∈ dom f) ∧ z.1 = u}
  -- Finite feasible points contribute the same value on both fiber descriptions.
  have hTS : T ⊆ S := by
    intro a ha
    rcases ha with ⟨z, hz, rfl⟩
    refine ⟨z, ⟨hz.1.1, hz.2⟩, ?_⟩
    simpa [Function.comp, withTopToEReal] using
      (congrArg withTopToEReal (coe_withTopRealPart hz.1.2)).symm
  -- Outside `dom f`, the unrestricted fiber contributes only `⊤`, which does not affect `sInf`.
  have hSinsert : S ⊆ insert ⊤ T := by
    intro a ha
    rcases ha with ⟨z, hz, rfl⟩
    by_cases hzDom : z.2 ∈ dom f
    · right
      refine ⟨z, ⟨⟨hz.1, hzDom⟩, hz.2⟩, ?_⟩
      simpa [Function.comp, withTopToEReal] using
        congrArg withTopToEReal (coe_withTopRealPart hzDom)
    · left
      rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hzDom
      have hzTop : f z.2 = ⊤ := by
        simpa using hzDom
      change withTopToEReal (f z.2) = ⊤
      rw [hzTop, withTopToEReal]
      rfl
  rw [partialInfProjection_eq_sInf, partialInfProjection_eq_sInf]
  simpa [S, T] using
    (show sInf S = sInf T from
      le_antisymm (sInf_le_sInf hTS)
        (by simpa using (sInf_le_sInf hSinsert : sInf (insert ⊤ T) ≤ sInf S)))

/-- Helper for Theorem 3.1.27: every finite affine value-function point has a feasible witness
where `f` is finite. -/
lemma exists_feasiblePoint_of_mem_dom_affineValueFunction
    {Q : Set E} {f : E → WithTop ℝ} {A : E →ₗ[ℝ] Λ}
    {v : Λ}
    (hv :
      v ∈ dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))) :
    ∃ x : E, x ∈ linearEqualityFeasibleSet Q A v ∧ x ∈ dom f := by
  let Q' : Set (Λ × E) :=
    {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1 ∧ p.2 ∈ dom f}
  have hv' :
      v ∈ dom
        (partialInfProjection
          Q'
          (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2)) := by
    rw [affineValueFunction_eq_restrictedRealProjection] at hv
    exact hv
  -- If the restricted fiber were empty, the partial infimum would be `⊤`, contradicting `hv'`.
  by_contra hno
  have hempty :
      {z : Λ × E | z ∈ Q' ∧ z.1 = v} = ∅ := by
    ext z
    constructor
    · intro hz
      exfalso
      apply hno
      refine ⟨z.2, ?_, hz.1.2⟩
      simpa [hz.2] using hz.1.1
    · intro hz
      cases hz
  have htop :
      partialInfProjection
          Q'
          (Real.toEReal ∘ fun p : Λ × E ↦ withTopRealPart f p.2)
          v = ⊤ := by
    rw [partialInfProjection_eq_sInf, hempty]
    simp
  rw [mem_extendedRealEffectiveDomain_iff, htop] at hv'
  exact hv'.1 rfl

/-- Helper for Theorem 3.1.27: every finite affine value-function base point already lies in the
range of the constraint map. -/
lemma mem_range_of_mem_dom_affineValueFunction
    {Q : Set E} {f : E → WithTop ℝ} {A : E →ₗ[ℝ] Λ}
    {v : Λ}
    (hv :
      v ∈ dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))) :
    v ∈ A.range := by
  -- A finite projected value comes from an actual feasible witness `x` with `A x = v`.
  rcases exists_feasiblePoint_of_mem_dom_affineValueFunction hv with
    ⟨x, hx, -⟩
  exact ⟨x, (mem_linearEqualityFeasibleSet_iff.mp hx).2⟩

/-- Helper for Theorem 3.1.27: a finite affine-fiber value is bounded above by every feasible
fiber witness. -/
lemma extendedRealRealPart_affineValueFunction_le_of_feasible
    {Q : Set E} {f : E → WithTop ℝ} {A : E →ₗ[ℝ] Λ}
    {v : Λ} {x : E}
    (hv :
      v ∈ dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd)))
    (hx : x ∈ linearEqualityFeasibleSet Q A v)
    (hxDom : x ∈ dom f) :
    extendedRealRealPart
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd))
        v ≤
      withTopRealPart f x := by
  let ψ : Λ → EReal :=
    partialInfProjection
      {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
      (withTopToEReal ∘ f ∘ Prod.snd)
  let S : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = v}
  have hS_bddBelow : BddBelow S := ⟨⊥, by intro a ha; exact bot_le⟩
  have hx_mem : withTopToEReal (f x) ∈ S := by
    refine ⟨(v, x), ?_, rfl⟩
    exact ⟨hx, rfl⟩
  -- The feasible witness `x` bounds the fiber infimum from above.
  have hψ_upper : ψ v ≤ withTopToEReal (f x) := by
    simpa [ψ, S, partialInfProjection_eq_sInf] using csInf_le hS_bddBelow hx_mem
  have hxValue : ((withTopRealPart f x : ℝ) : EReal) = withTopToEReal (f x) := by
    simpa [withTopToEReal] using congrArg withTopToEReal (coe_withTopRealPart hxDom)
  have hE :
      ((extendedRealRealPart ψ v : ℝ) : EReal) ≤ ((withTopRealPart f x : ℝ) : EReal) := by
    calc
      ((extendedRealRealPart ψ v : ℝ) : EReal) = ψ v := by
        rw [coe_extendedRealRealPart hv]
      _ ≤ withTopToEReal (f x) := hψ_upper
      _ = ((withTopRealPart f x : ℝ) : EReal) := by
        rw [← hxValue]
  exact_mod_cast hE

/-- Helper for Theorem 3.1.27: once `withTopRealPart f` has a global lower bound on `Q`, every
point of `A '' Q` lies in the finite-value domain of the affine value function. -/
lemma affineValueFunction_finite_on_image_of_Q_of_lowerBound
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {A : E →ₗ[ℝ] Λ}
    (hlower : ∃ m : ℝ, ∀ z : E, z ∈ Q → m ≤ withTopRealPart f z) :
    ∀ x : E,
      x ∈ Q →
        A x ∈
          dom
            (partialInfProjection
              {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
              (withTopToEReal ∘ f ∘ Prod.snd)) := by
  intro x hxQ
  let ψ : Λ → EReal :=
    partialInfProjection
      {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
      (withTopToEReal ∘ f ∘ Prod.snd)
  obtain ⟨m, hm⟩ := hlower
  have hxDom : x ∈ dom f := interior_subset (hQ_subset_interior hxQ)
  let S : Set EReal :=
    (withTopToEReal ∘ f ∘ Prod.snd) '' {z : Λ × E |
      z.2 ∈ linearEqualityFeasibleSet Q A z.1 ∧ z.1 = A x}
  have hS_nonempty : S.Nonempty := by
    refine ⟨withTopToEReal (f x), ?_⟩
    refine ⟨(A x, x), ?_, rfl⟩
    exact ⟨mem_linearEqualityFeasibleSet_iff.mpr ⟨hxQ, rfl⟩, rfl⟩
  have hψ_upper : ψ (A x) ≤ ((withTopRealPart f x : ℝ) : EReal) := by
    have hx_mem : withTopToEReal (f x) ∈ S := by
      refine ⟨(A x, x), ?_, rfl⟩
      exact ⟨mem_linearEqualityFeasibleSet_iff.mpr ⟨hxQ, rfl⟩, rfl⟩
    have hupper : ψ (A x) ≤ withTopToEReal (f x) := by
      simpa [ψ, S, partialInfProjection_eq_sInf] using
        csInf_le ⟨⊥, by intro a ha; exact bot_le⟩ hx_mem
    have hxValue : withTopToEReal (f x) = ((withTopRealPart f x : ℝ) : EReal) := by
      simpa [withTopToEReal] using
        (congrArg withTopToEReal (coe_withTopRealPart hxDom)).symm
    simpa [hxValue] using hupper
  have hψ_lower : ((m : ℝ) : EReal) ≤ ψ (A x) := by
    have hS_lower : ∀ a ∈ S, ((m : ℝ) : EReal) ≤ a := by
      intro a ha
      rcases ha with ⟨z, hz, rfl⟩
      have hzFeas : z.2 ∈ linearEqualityFeasibleSet Q A (A x) := by
        simpa [hz.2] using hz.1
      have hzQ : z.2 ∈ Q := (mem_linearEqualityFeasibleSet_iff.mp hzFeas).1
      have hzDom : z.2 ∈ dom f := interior_subset (hQ_subset_interior hzQ)
      have hzValue : withTopToEReal (f z.2) = ((withTopRealPart f z.2 : ℝ) : EReal) := by
        simpa [withTopToEReal] using
          (congrArg withTopToEReal (coe_withTopRealPart hzDom)).symm
      have hmz : m ≤ withTopRealPart f z.2 := hm z.2 hzQ
      have hmzE : ((m : ℝ) : EReal) ≤ ((withTopRealPart f z.2 : ℝ) : EReal) := by
        exact_mod_cast hmz
      simpa [Function.comp, hzValue] using hmzE
    simpa [ψ, S, partialInfProjection_eq_sInf] using le_csInf hS_nonempty hS_lower
  rw [mem_extendedRealEffectiveDomain_iff]
  constructor
  · intro htop
    have htop' : ψ (A x) = ⊤ := by
      simpa [ψ] using htop
    rw [htop'] at hψ_upper
    simp at hψ_upper
  · intro hbot
    have hbot' : ψ (A x) = ⊥ := by
      simpa [ψ] using hbot
    rw [hbot'] at hψ_lower
    simp at hψ_lower

/-- Helper for Theorem 3.1.27: under the global lower bound on `Q`, the finite-value domain of the
affine value function is exactly `A '' Q`. -/
lemma affineValueFunctionDomain_eq_image
    {Q : Set E} {f : E → WithTop ℝ} {A : E →ₗ[ℝ] Λ}
    (hQ_subset_interior : Q ⊆ interior (dom f))
    (hlower : ∃ m : ℝ, ∀ z : E, z ∈ Q → m ≤ withTopRealPart f z) :
    dom
        (partialInfProjection
          {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
          (withTopToEReal ∘ f ∘ Prod.snd)) =
      A '' Q := by
  ext v
  constructor
  · intro hv
    rcases exists_feasiblePoint_of_mem_dom_affineValueFunction hv with
      ⟨x, hxFeas, -⟩
    refine ⟨x, (mem_linearEqualityFeasibleSet_iff.mp hxFeas).1, ?_⟩
    exact (mem_linearEqualityFeasibleSet_iff.mp hxFeas).2
  · rintro ⟨x, hxQ, rfl⟩
    exact affineValueFunction_finite_on_image_of_Q_of_lowerBound
      hQ_subset_interior hlower x hxQ

/-- Helper for Theorem 3.1.27: with `xStar ∈ Q` ambient, optimality for the equality-constrained
problem means satisfying the equality constraint and minimizing over the equality-feasible set. -/
def EqualityConstrainedOptimalPoint
    (Q : Set E) (f : E → WithTop ℝ) (A : E →ₗ[ℝ] Λ) (b : Λ) (xStar : E) : Prop :=
  A xStar = b ∧
    IsMinOn (withTopRealPart f) (linearEqualityFeasibleSet Q A b) xStar

/-- Helper for Theorem 3.1.27: expand `EqualityConstrainedOptimalPoint` to the equality constraint
and the minimizer condition on the feasible slice. -/
lemma equalityConstrainedOptimalPoint_iff
    {Q : Set E} {f : E → WithTop ℝ} {A : E →ₗ[ℝ] Λ} {b : Λ} {xStar : E} :
    EqualityConstrainedOptimalPoint Q f A b xStar ↔
      A xStar = b ∧
        IsMinOn (withTopRealPart f) (linearEqualityFeasibleSet Q A b) xStar :=
  Iff.rfl

/-- Helper for Theorem 3.1.27: the multiplier certificate records the equality constraint together
with the bounded adjoint norm and the variational inequality on `Q`. -/
def HasSubgradientMultiplierCertificateWithBound
    (Q : Set E) (f : E → WithTop ℝ) (A : E →ₗ[ℝ] Λ) (b : Λ)
    (xBar : E) (ε : ℝ) (xStar : E) : Prop :=
  A xStar = b ∧
    ∃ yStar ∈
      {y : Λ |
        ‖A.adjoint y‖ ≤
          (sSup (withTopRealPart f '' Metric.closedBall xBar (ε / 2)) -
              sInf (withTopRealPart f '' Q)) / (ε / 2)},
      ∃ gStar ∈ ∂ f(xStar),
        ∀ x ∈ Q, 0 ≤ inner ℝ (gStar - A.adjoint yStar) (x - xStar)

/-- Helper for Theorem 3.1.27: expand the bounded multiplier certificate into its equality,
multiplier, subgradient, and variational-inequality components. -/
lemma hasSubgradientMultiplierCertificateWithBound_iff
    {Q : Set E} {f : E → WithTop ℝ} {A : E →ₗ[ℝ] Λ} {b : Λ}
    {xBar : E} {ε : ℝ} {xStar : E} :
    HasSubgradientMultiplierCertificateWithBound Q f A b xBar ε xStar ↔
      A xStar = b ∧
        ∃ yStar ∈
          {y : Λ |
            ‖A.adjoint y‖ ≤
              (sSup (withTopRealPart f '' Metric.closedBall xBar (ε / 2)) -
                  sInf (withTopRealPart f '' Q)) / (ε / 2)},
          ∃ gStar ∈ ∂ f(xStar),
            ∀ x ∈ Q, 0 ≤ inner ℝ (gStar - A.adjoint yStar) (x - xStar) :=
  Iff.rfl

/-- Helper for Theorem 3.1.27: once the affine value function is known to be finite on `A '' Q`,
every relative affine-value subgradient pulls back to a constrained subgradient of `f`. -/
lemma adjoint_mem_constrainedSubdifferential_of_mem_affineValueSubgradient
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {A : E →ₗ[ℝ] Λ} {b : Λ} {xStar : E} {yStar : Λ}
    (hxStarQ : xStar ∈ Q)
    (hfeasible : A xStar = b)
    (hdomQ :
      ∀ x : E, x ∈ Q →
        A x ∈
          dom
            (partialInfProjection
              {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
              (withTopToEReal ∘ f ∘ Prod.snd)))
    (hy :
      yStar ∈
        ∂[dom
            (partialInfProjection
              {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
              (withTopToEReal ∘ f ∘ Prod.snd))]
          (extendedRealRealPart
            (partialInfProjection
              {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
              (withTopToEReal ∘ f ∘ Prod.snd)))
          (b))
    (hψb :
      extendedRealRealPart
          (partialInfProjection
            {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
            (withTopToEReal ∘ f ∘ Prod.snd))
          b =
        withTopRealPart f xStar) :
    A.adjoint yStar ∈ ∂[Q] f(xStar) := by
  let ψ : Λ → EReal :=
    partialInfProjection
      {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
      (withTopToEReal ∘ f ∘ Prod.snd)
  have hxStarDom : xStar ∈ dom f := interior_subset (hQ_subset_interior hxStarQ)
  rw [mem_subdifferentialWithin_iff] at hy
  rcases hy with ⟨hbDom, hsupport⟩
  refine mem_constrainedSubdifferential_iff.mpr ⟨hxStarQ, hxStarDom, ?_⟩
  intro x hxQ
  have hxDom : x ∈ dom f := interior_subset (hQ_subset_interior hxQ)
  have hAxDom : A x ∈ dom ψ := by
    simpa [ψ] using hdomQ x hxQ
  have hψx :
      extendedRealRealPart ψ (A x) ≤ withTopRealPart f x :=
    extendedRealRealPart_affineValueFunction_le_of_feasible
      hAxDom
      (mem_linearEqualityFeasibleSet_iff.mpr ⟨hxQ, rfl⟩) hxDom
  -- Compare the affine-value support inequality with the feasible witness on the fiber `A x`.
  have hsupport_x :
      extendedRealRealPart ψ b + inner ℝ yStar (A x - b) ≤ withTopRealPart f x := by
    exact le_trans (hsupport hAxDom) hψx
  have hpair :
      inner ℝ yStar (A x - b) = inner ℝ (A.adjoint yStar) (x - xStar) := by
    calc
      inner ℝ yStar (A x - b)
          = inner ℝ yStar (A x - A xStar) := by simpa [hfeasible]
      _ = inner ℝ yStar (A (x - xStar)) := by simp [map_sub]
      _ = inner ℝ (A.adjoint yStar) (x - xStar) := by
            rw [A.adjoint_inner_left]
  have hψb' : (ψ b).toReal = withTopRealPart f xStar := by
    simpa [ψ] using hψb
  have hsupport_x' :
      (ψ b).toReal + inner ℝ (A.adjoint yStar) (x - xStar) ≤ withTopRealPart f x := by
    simpa [extendedRealRealPart, hpair] using hsupport_x
  have hreal :
      withTopRealPart f xStar + inner ℝ (A.adjoint yStar) (x - xStar) ≤ withTopRealPart f x := by
    simpa [hψb'] using hsupport_x'
  -- Read the real inequality back on the source-facing `WithTop`-valued constrained-subgradient
  -- owner.
  rw [← coe_withTopRealPart hxDom, ← coe_withTopRealPart hxStarDom]
  exact_mod_cast hreal

/-- Helper for Theorem 3.1.27: the Slater ball around `xBar` gives an actual interior
neighborhood of `b` inside the affine-value domain when the ambient space is restricted to
`A.range`. -/
lemma slaterBase_mem_interior_affineValueDomainInRange
    {Q : Set E} {A : E →ₗ[ℝ] Λ} {b : Λ} {xBar : E} {ε : ℝ} {ψ : Λ → EReal}
    (hbar : A xBar = b) (hε : 0 < ε) (hball : Metric.ball xBar ε ⊆ Q)
    (hψdom : dom ψ = A '' Q) :
    (⟨b, by exact ⟨xBar, hbar⟩⟩ : A.range) ∈ interior {u : A.range | u.1 ∈ dom ψ} := by
  let u0 : A.range := ⟨b, ⟨xBar, hbar⟩⟩
  let U : Set A.range := A.rangeRestrict '' Metric.ball xBar ε
  -- Push the Slater ball through the surjective range-restricted map to get an open neighborhood
  -- of `u0` in `A.range`.
  have hu0U : u0 ∈ U := by
    refine ⟨xBar, Metric.mem_ball_self hε, ?_⟩
    ext
    simp [u0, hbar]
  have hUOpen : IsOpen U := by
    let hopen : IsOpenMap A.rangeRestrict :=
      LinearMap.isOpenMap_of_finiteDimensional A.rangeRestrict A.surjective_rangeRestrict
    exact hopen _ Metric.isOpen_ball
  -- Every point in that image comes from a Slater-ball point, hence from a point of `Q`.
  have hUSubset : U ⊆ {u : A.range | u.1 ∈ dom ψ} := by
    intro u hu
    rcases hu with ⟨x, hxBall, rfl⟩
    rw [hψdom]
    exact ⟨x, hball hxBall, rfl⟩
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hUOpen.mem_nhds hu0U) hUSubset

/-- Helper for Theorem 3.1.27: the affine value function has a relative subgradient at the Slater
base point `b` once the lower-bound package makes its finite-value domain equal to `A '' Q`. -/
lemma existsAffineValueSubgradientAtSlaterBase
    {Q : Set E} {f : E → WithTop ℝ}
    (hfQ : ConvexOn ℝ Q (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {A : E →ₗ[ℝ] Λ} {b : Λ} {xBar : E} {ε : ℝ}
    (hbar : A xBar = b) (hε : 0 < ε) (hball : Metric.ball xBar ε ⊆ Q)
    (hlower : ∃ m : ℝ, ∀ z : E, z ∈ Q → m ≤ withTopRealPart f z) :
    let ψ : Λ → EReal :=
      partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
        (withTopToEReal ∘ f ∘ Prod.snd)
    ∃ yStar : Λ, yStar ∈ ∂[dom ψ] (extendedRealRealPart ψ) (b) := by
  classical
  let ψ : Λ → EReal :=
    partialInfProjection
      {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
      (withTopToEReal ∘ f ∘ Prod.snd)
  have hψconv : ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ) := by
    simpa [ψ] using affineValueFunctionConvexOn hfQ hQ_subset_interior (A := A) hlower
  have hψdom : dom ψ = A '' Q := by
    simpa [ψ] using affineValueFunctionDomain_eq_image
      (A := A) (Q := Q) (f := f) hQ_subset_interior hlower
  let u0 : A.range := ⟨b, ⟨xBar, hbar⟩⟩
  let D : Set A.range := {u : A.range | u.1 ∈ dom ψ}
  let ψRangeTop : A.range → WithTop ℝ :=
    fun u ↦ if u ∈ D then ((extendedRealRealPart ψ u.1 : ℝ) : WithTop ℝ) else ⊤
  have hdomRangeTop : dom ψRangeTop = D := by
    ext u
    by_cases huD : u ∈ D
    · constructor
      · intro _
        exact huD
      · intro _
        dsimp [ψRangeTop]
        simp [huD]
    · constructor
      · intro hu
        dsimp [ψRangeTop] at hu
        simp [huD] at hu
      · intro hu
        exact (huD hu).elim
  have hψRangeTop_real :
      ∀ u : A.range, u ∈ dom ψRangeTop →
        withTopRealPart ψRangeTop u = extendedRealRealPart ψ u.1 := by
    intro u hu
    have huD : u ∈ D := by
      simpa [hdomRangeTop] using hu
    apply WithTop.coe_injective
    rw [coe_withTopRealPart hu]
    dsimp [ψRangeTop]
    simp [huD]
  have hconvRangeTop : ConvexOn ℝ (dom ψRangeTop) (withTopRealPart ψRangeTop) := by
    refine ⟨?_, ?_⟩
    · intro u hu v hv a b ha hb hab
      have huDom : u.1 ∈ dom ψ := by
        simpa [hdomRangeTop, D] using hu
      have hvDom : v.1 ∈ dom ψ := by
        simpa [hdomRangeTop, D] using hv
      have huvDom : (a • u + b • v).1 ∈ dom ψ := by
        simpa using hψconv.1 huDom hvDom ha hb hab
      simpa [hdomRangeTop, D] using huvDom
    · intro u hu v hv a b ha hb hab
      have huDom : u.1 ∈ dom ψ := by
        simpa [hdomRangeTop, D] using hu
      have hvDom : v.1 ∈ dom ψ := by
        simpa [hdomRangeTop, D] using hv
      have huvDom : (a • u + b • v).1 ∈ dom ψ := by
        simpa using hψconv.1 huDom hvDom ha hb hab
      have huv : a • u + b • v ∈ dom ψRangeTop := by
        simpa [hdomRangeTop, D] using huvDom
      rw [hψRangeTop_real _ huv, hψRangeTop_real _ hu, hψRangeTop_real _ hv]
      simpa using hψconv.2 huDom hvDom ha hb hab
  have hu0IntD : u0 ∈ interior D := by
    simpa [D] using
      slaterBase_mem_interior_affineValueDomainInRange hbar hε hball hψdom
  have hu0Int : u0 ∈ interior (dom ψRangeTop) := by
    simpa [hdomRangeTop] using hu0IntD
  -- Apply the interior-point subgradient theorem on the correct ambient space `A.range`.
  rcases subdifferential_nonempty_of_convexOn_of_mem_interior hconvRangeTop hu0Int with
    ⟨qStar, hqStar⟩
  let ψRange : A.range → ℝ := fun u ↦ extendedRealRealPart ψ u.1
  let φRange : A.range → WithTop ℝ :=
    fun u ↦ ((ψRange u : ℝ) : WithTop ℝ)
  have hqWithinTop :
      qStar ∈ ∂[D] φRange (u0) := by
    rw [subdifferential_topExtension_eq_constrainedSubdifferential
      (Q := D) (f := φRange) (x := u0)] at hqStar
    exact hqStar
  have hqWithin :
      qStar ∈ ∂[D] ψRange (u0) := by
    rcases mem_constrainedSubdifferential_iff.mp hqWithinTop with ⟨hu0Dom, -, hminorant⟩
    rw [mem_subdifferentialWithin_iff]
    refine ⟨hu0Dom, ?_⟩
    intro v hv
    have hcast :
        (((ψRange v : ℝ) : WithTop ℝ)) ≥
          (((ψRange u0 + inner ℝ qStar (v - u0) : ℝ) : WithTop ℝ)) := by
      simpa [φRange, ψRange] using hminorant hv
    exact_mod_cast hcast
  -- Finally transport the range-valued subgradient back to the ambient relative subgradient at
  -- `b`.
  refine ⟨qStar, ?_⟩
  rw [mem_subdifferentialWithin_iff]
  refine ⟨?_, ?_⟩
  · have hu0Dom := (mem_subdifferentialWithin_iff.mp hqWithin).1
    change ¬ ψ b = ⊤ ∧ ¬ ψ b = ⊥
    simpa [D, u0] using hu0Dom
  · intro v hv
    have hvRange : v ∈ A.range := by
      rw [hψdom] at hv
      rcases hv with ⟨x, hxQ, rfl⟩
      exact ⟨x, rfl⟩
    let vR : A.range := ⟨v, hvRange⟩
    have hvR : vR ∈ D := by
      simpa [D, vR]
    have hsupport := (mem_subdifferentialWithin_iff.mp hqWithin).2 hvR
    simpa [u0, vR, ψRange] using hsupport
/-- Helper for Theorem 3.1.27: an ambient subgradient together with the multiplier variational
inequality controls every affine fiber value by the base-space pairing `⟪yStar, v - u⟫`. -/
lemma affineFiberLowerBoundOfVariationalInequality
    {Q : Set E} {f : E → WithTop ℝ} {A : E →ₗ[ℝ] Λ}
    {u v : Λ} {xStar gStar x : E} {yStar : Λ}
    (hxStar : xStar ∈ linearEqualityFeasibleSet Q A u)
    (hgStar : gStar ∈ ∂ f(xStar))
    (hvar :
      ∀ z : E, z ∈ Q →
        0 ≤ inner ℝ (gStar - A.adjoint yStar) (z - xStar))
    (hx : x ∈ linearEqualityFeasibleSet Q A v)
    (hxDom : x ∈ dom f) :
    withTopRealPart f xStar + inner ℝ yStar (v - u) ≤ withTopRealPart f x := by
  have hxStarDom : xStar ∈ dom f := (mem_subdifferential_iff.mp hgStar).mem_dom
  rcases hxStar with ⟨hxStarQ, hxStarA⟩
  rcases hx with ⟨hxQ, hxA⟩
  -- First translate the ambient subgradient inequality to the finite real-part surface.
  have hsupport :
      withTopRealPart f xStar + inner ℝ gStar (x - xStar) ≤ withTopRealPart f x := by
    have hsub := (mem_subdifferential_iff.mp hgStar).2 hxDom
    rw [← coe_withTopRealPart hxDom, ← coe_withTopRealPart hxStarDom] at hsub
    exact_mod_cast hsub
  -- Then use the variational inequality on `Q` to replace `gStar` by `A.adjoint yStar`.
  have hnormal :
      inner ℝ (A.adjoint yStar) (x - xStar) ≤ inner ℝ gStar (x - xStar) := by
    have hvarx := hvar x hxQ
    rw [inner_sub_left] at hvarx
    linarith
  -- Finally, feasibility rewrites the adjoint pairing as the base-space displacement `v - u`.
  have hbase :
      inner ℝ yStar (v - u) = inner ℝ (A.adjoint yStar) (x - xStar) := by
    calc
      inner ℝ yStar (v - u)
          = inner ℝ yStar (A x - A xStar) := by simpa [hxA, hxStarA]
      _ = inner ℝ yStar (A (x - xStar)) := by simp [map_sub]
      _ = inner ℝ (A.adjoint yStar) (x - xStar) := by
            rw [A.adjoint_inner_left]
  have htarget :
      withTopRealPart f xStar + inner ℝ (A.adjoint yStar) (x - xStar) ≤ withTopRealPart f x := by
    linarith
  simpa [hbase] using htarget

/-- Helper for Theorem 3.1.27: once `A.adjoint yStar` is known to be a constrained subgradient at
`xStar`, any upper bound on the Slater ball and lower bound on `Q` yield the textbook adjoint-norm
estimate. -/
lemma adjointNormBoundOfConstrainedSubgradient
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_subset_interior : Q ⊆ interior (dom f))
    {A : E →ₗ[ℝ] Λ} {b : Λ} {xBar : E} {ε : ℝ}
    (hbar : A xBar = b) (hε : 0 < ε) (hball : Metric.ball xBar ε ⊆ Q)
    {M m : ℝ}
    (hUpper : ∀ x : E, x ∈ Metric.ball xBar ε → withTopRealPart f x ≤ M)
    (hLower : ∀ x : E, x ∈ Q → m ≤ withTopRealPart f x)
    {xStar : E} {yStar : Λ}
    (hxStar : xStar ∈ linearEqualityFeasibleSet Q A b)
    (hAdj : A.adjoint yStar ∈ ∂[Q] f(xStar)) :
    ‖A.adjoint yStar‖ ≤ (M - m) / ε := by
  rcases hxStar with ⟨hxStarQ, hxStarA⟩
  have hxBarBall : xBar ∈ Metric.ball xBar ε := Metric.mem_ball_self hε
  have hxBarQ : xBar ∈ Q := hball hxBarBall
  have hnum_nonneg : 0 ≤ M - m := by
    linarith [hUpper xBar hxBarBall, hLower xBar hxBarQ]
  by_cases hs : A.adjoint yStar = 0
  · have hrhs_nonneg :
        0 ≤ (M - m) / ε := by
      exact div_nonneg hnum_nonneg hε.le
    simpa [hs] using hrhs_nonneg
  · have hsNormPos : 0 < ‖A.adjoint yStar‖ := norm_pos_iff.mpr hs
    have hmul :
        ε * ‖A.adjoint yStar‖ ≤ M - m := by
      by_contra hmul
      have hlt :
          M - m < ε * ‖A.adjoint yStar‖ := by
        linarith
      let r : ℝ := ((M - m) / ‖A.adjoint yStar‖ + ε) / 2
      have hr_pos : 0 < r := by
        have hfrac_nonneg : 0 ≤ (M - m) / ‖A.adjoint yStar‖ := by
          exact div_nonneg hnum_nonneg hsNormPos.le
        dsimp [r]
        linarith
      have hr_lt_eps : r < ε := by
        have hdiv_lt : (M - m) / ‖A.adjoint yStar‖ < ε := by
          rw [div_lt_iff₀ hsNormPos]
          exact hlt
        dsimp [r]
        linarith
      have hr_mul :
          M - m < r * ‖A.adjoint yStar‖ := by
        have hdiv_lt_eps : (M - m) / ‖A.adjoint yStar‖ < ε := by
          rw [div_lt_iff₀ hsNormPos]
          exact hlt
        have hdiv_lt_r : (M - m) / ‖A.adjoint yStar‖ < r := by
          dsimp [r]
          nlinarith
        have hmul' :
            ((M - m) / ‖A.adjoint yStar‖) * ‖A.adjoint yStar‖ <
              r * ‖A.adjoint yStar‖ := by
          exact mul_lt_mul_of_pos_right hdiv_lt_r hsNormPos
        have hcancel : ((M - m) / ‖A.adjoint yStar‖) * ‖A.adjoint yStar‖ = M - m := by
          field_simp [hsNormPos.ne']
        rw [← hcancel]
        exact hmul'
      let dir : E := ‖A.adjoint yStar‖⁻¹ • A.adjoint yStar
      let z : E := xBar + r • dir
      have hz_sub : z - xBar = r • dir := by
        dsimp [z]
        abel
      have hzBall : z ∈ Metric.ball xBar ε := by
        rw [Metric.mem_ball, dist_eq_norm, hz_sub, norm_smul]
        have hdir_norm : ‖dir‖ = 1 := by
          change ‖‖A.adjoint yStar‖⁻¹ • A.adjoint yStar‖ = 1
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hsNormPos.le)]
          field_simp [hsNormPos.ne']
        simpa [hdir_norm, Real.norm_of_nonneg hr_pos.le] using hr_lt_eps
      have hzQ : z ∈ Q := hball hzBall
      have hzDom : z ∈ dom f := interior_subset (hQ_subset_interior hzQ)
      have hpairBase : inner ℝ (A.adjoint yStar) (xBar - xStar) = 0 := by
        calc
          inner ℝ (A.adjoint yStar) (xBar - xStar)
              = inner ℝ yStar (A (xBar - xStar)) := by
                  rw [A.adjoint_inner_left]
          _ = inner ℝ yStar (A xBar - A xStar) := by
                simp [map_sub]
          _ = 0 := by
                simp [hbar, hxStarA]
      have hpair :
          inner ℝ (A.adjoint yStar) (z - xStar) = r * ‖A.adjoint yStar‖ := by
        have hz_decomp : z - xStar = (z - xBar) + (xBar - xStar) := by
          abel
        calc
          inner ℝ (A.adjoint yStar) (z - xStar)
              = inner ℝ (A.adjoint yStar) ((z - xBar) + (xBar - xStar)) := by
                  rw [hz_decomp]
          _ = inner ℝ (A.adjoint yStar) (z - xBar) +
                inner ℝ (A.adjoint yStar) (xBar - xStar) := by
                  rw [inner_add_right]
          _ = inner ℝ (A.adjoint yStar) (z - xBar) := by
                rw [hpairBase, add_zero]
          _ = inner ℝ (A.adjoint yStar) (r • dir) := by
                rw [hz_sub]
          _ = r * (‖A.adjoint yStar‖⁻¹ * ‖A.adjoint yStar‖ ^ (2 : ℕ)) := by
                simp [dir, inner_smul_right, real_inner_self_eq_norm_sq, mul_assoc, mul_left_comm,
                  mul_comm]
          _ = r * ‖A.adjoint yStar‖ := by
                field_simp [hsNormPos.ne']
      -- Evaluate the constrained-subgradient support inequality on the radial Slater test point.
      have hsupport :
          withTopRealPart f xStar + r * ‖A.adjoint yStar‖ ≤ withTopRealPart f z := by
        have hsupport' :=
          withTopRealPart_le_of_mem_constrainedSubdifferential
            (Q := Q) (f := f) hAdj hzQ hzDom
        simpa [hpair] using hsupport'
      have hzUpper : withTopRealPart f z ≤ M := hUpper z hzBall
      have hxLower : m ≤ withTopRealPart f xStar := hLower xStar hxStarQ
      linarith
    exact (le_div_iff₀ hε).2 (by simpa [mul_comm] using hmul)

/-- Theorem 3.1.27. A point `xStar ∈ Q` is optimal for the equality-constrained problem exactly
when it satisfies the equality constraint and admits a subgradient-multiplier certificate whose
adjoint norm obeys the Slater-radius bound. -/
theorem isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound
    {Q : Set E} {f : E → WithTop ℝ}
    (hfQ : ConvexOn ℝ Q (withTopRealPart f))
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    (hlevel_bounded : ∀ α : ℝ, Bornology.IsBounded (constrainedSublevelSet Q f α))
    {A : E →ₗ[ℝ] Λ} {b : Λ} {xBar : E} {ε : ℝ}
    (hbar : A xBar = b) (hε : 0 < ε) (hball : Metric.ball xBar ε ⊆ Q) {xStar : E}
    (hxStarQ : xStar ∈ Q) :
    EqualityConstrainedOptimalPoint Q f A b xStar ↔
      HasSubgradientMultiplierCertificateWithBound Q f A b xBar ε xStar := by
  -- Route correction: `IsMinOn` here does not include `xStar ∈ linearEqualityFeasibleSet Q A b`.
  -- The source theorem is about feasible optimal points, so the public surface keeps the
  -- equality-feasibility clause bundled with the minimizer and certificate views.
  rw [equalityConstrainedOptimalPoint_iff, hasSubgradientMultiplierCertificateWithBound_iff]
  constructor
  · rintro ⟨hfeasible, hmin⟩
    let ψ : Λ → EReal :=
      partialInfProjection
        {p : Λ × E | p.2 ∈ linearEqualityFeasibleSet Q A p.1}
        (withTopToEReal ∘ f ∘ Prod.snd)
    -- First package the affine value-function data attached to the optimal fiber.
    have hlower :
        ∃ m : ℝ, ∀ z : E, z ∈ Q → m ≤ withTopRealPart f z :=
      exists_lowerBound_on_Q_of_bounded_constrainedSublevels
        hfQ hQ_subset_interior hlevel_bounded hε hball
    have hdomQ :
        ∀ x : E, x ∈ Q → A x ∈ dom ψ := by
      intro x hxQ
      simpa [ψ] using
        affineValueFunction_finite_on_image_of_Q_of_lowerBound
          hQ_subset_interior hlower x hxQ
    have hψconv : ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ) := by
      simpa [ψ] using affineValueFunctionConvexOn hfQ hQ_subset_interior hlower (A := A)
    have hψdom : dom ψ = A '' Q := by
      simpa [ψ] using affineValueFunctionDomain_eq_image
        (A := A) (Q := Q) (f := f) hQ_subset_interior hlower
    have hxBarQ : xBar ∈ Q := hball (Metric.mem_ball_self hε)
    have hbDom : b ∈ dom ψ := by
      rw [hψdom]
      exact ⟨xBar, hxBarQ, hbar⟩
    have hψb :
        extendedRealRealPart ψ b = withTopRealPart f xStar := by
      exact (by
        simpa [ψ] using
          (affineValueFunction_eq_of_linearEqualityFeasibleOptimality
            hQ_subset_interior hxStarQ hfeasible hmin).2)
    -- First obtain the affine-value subgradient at the Slater base point on the correct ambient
    -- space `A.range`, then pull it back to a constrained subgradient of `f`.
    have hyExists : ∃ yStar : Λ, yStar ∈ ∂[dom ψ] (extendedRealRealPart ψ) (b) := by
      simpa [ψ] using
        existsAffineValueSubgradientAtSlaterBase
          (Q := Q) (f := f) hfQ hQ_subset_interior
          (A := A) (b := b) (xBar := xBar) hbar hε hball hlower
    rcases hyExists with ⟨yStar, hy⟩
    have hAdj : A.adjoint yStar ∈ ∂[Q] f(xStar) := by
      exact adjoint_mem_constrainedSubdifferential_of_mem_affineValueSubgradient
        hQ_subset_interior hxStarQ hfeasible hdomQ hy hψb
    rcases existsSubgradientWithNormalConeRemainderOfMemConstrainedSubdifferential
        (Q := Q) (f := f) hf hfQ hQ_subset_interior hxStarQ hAdj with
      ⟨gStar, hgStar, hnormal⟩
    have hε_half : 0 < ε / 2 := by
      linarith
    have hball_half : Metric.ball xBar (ε / 2) ⊆ Q := by
      intro x hxBall
      exact hball (Metric.ball_subset_ball (by linarith) hxBall)
    have hclosedBall_half_subset : Metric.closedBall xBar (ε / 2) ⊆ Q := by
      intro x hxClosed
      have hxlt : dist x xBar < ε := by
        rw [Metric.mem_closedBall] at hxClosed
        linarith
      exact hball (by simpa [Metric.mem_ball, dist_comm] using hxlt)
    have hclosedBall_half_subset_interior :
        Metric.closedBall xBar (ε / 2) ⊆ interior (dom f) := by
      intro x hxClosed
      exact hQ_subset_interior (hclosedBall_half_subset hxClosed)
    have hImage_half_bddAbove :
        BddAbove (withTopRealPart f '' Metric.closedBall xBar (ε / 2)) := by
      refine IsCompact.bddAbove_image (isCompact_closedBall xBar (ε / 2)) ?_
      exact hf.continuousOn_interior.mono hclosedBall_half_subset_interior
    obtain ⟨mLower, hmLower⟩ := hlower
    have hImage_Q_bddBelow : BddBelow (withTopRealPart f '' Q) := by
      refine ⟨mLower, ?_⟩
      rintro _ ⟨x, hxQ, rfl⟩
      exact hmLower x hxQ
    have hyBound :
        yStar ∈
          {y : Λ |
            ‖A.adjoint y‖ ≤
              (sSup (withTopRealPart f '' Metric.closedBall xBar (ε / 2)) -
                  sInf (withTopRealPart f '' Q)) / (ε / 2)} := by
      -- Use the compact half-radius Slater ball so the `sSup` surface is a genuine finite upper
      -- bound on the image of `withTopRealPart f`.
      exact adjointNormBoundOfConstrainedSubgradient
        (Q := Q) (f := f) hQ_subset_interior
        (A := A) (b := b) (xBar := xBar) hbar hε_half hball_half
        (M := sSup (withTopRealPart f '' Metric.closedBall xBar (ε / 2)))
        (m := sInf (withTopRealPart f '' Q))
        (hUpper := by
          intro x hxBall
          have hxClosed : x ∈ Metric.closedBall xBar (ε / 2) := by
            rw [Metric.mem_closedBall]
            exact le_of_lt (by simpa [Metric.mem_ball] using hxBall)
          exact le_csSup hImage_half_bddAbove
            (show withTopRealPart f x ∈
                withTopRealPart f '' Metric.closedBall xBar (ε / 2) from
              ⟨x, hxClosed, rfl⟩))
        (hLower := by
          intro x hxQ
          exact csInf_le hImage_Q_bddBelow
            (show withTopRealPart f x ∈ withTopRealPart f '' Q from
              ⟨x, hxQ, rfl⟩))
        (hxStar := mem_linearEqualityFeasibleSet_iff.mpr ⟨hxStarQ, hfeasible⟩)
        (hAdj := hAdj)
    refine ⟨hfeasible, yStar, hyBound, gStar, hgStar, ?_⟩
    -- The decomposition helper already provides exactly the normal-cone pairing inequality on `Q`.
    exact mem_normalCone_iff.mp hnormal
  · rintro ⟨hfeasible, yStar, hyBound, gStar, hgStar, hvar⟩
    have hxStarFeasible : xStar ∈ linearEqualityFeasibleSet Q A b := by
      exact mem_linearEqualityFeasibleSet_iff.mpr ⟨hxStarQ, hfeasible⟩
    -- The certificate inequality is exactly the normal-cone condition for the multiplier defect.
    have hnormal : gStar - A.adjoint yStar ∈ N[Q] xStar := by
      rw [mem_normalCone_iff]
      intro x hxQ
      exact hvar x hxQ
    refine ⟨hfeasible, ?_⟩
    -- Apply the previously isolated normal-cone optimality criterion on the equality-feasible set.
    exact isMinOn_linearEqualityFeasibleSet_of_subgradient_multiplier_certificate
      hQ_subset_interior hxStarFeasible hgStar hnormal

end

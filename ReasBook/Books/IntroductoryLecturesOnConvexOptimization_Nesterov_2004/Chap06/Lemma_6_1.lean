/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Corollary_3_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

/- This item lies in the chapter's Fenchel-biconjugacy domain.

Primary domain:
- Fenchel duality for `ℝ ∪ {+∞}`-valued functions on real inner-product spaces.

Sampled owner-style declarations:
- `dom` and `withTopToEReal` from `Chap03/Definition_3_3`, the chapter owners for the
  finite-value domain and the canonical codomain bridge to `EReal`;
- `ClosedConvexFunction` from `Chap03/Definition_3_1_1_5`, the chapter owner for proper
  closed-convex `WithTop`-valued functions;
- `fenchelDual` with the notation `f⋆` from `Chap03/Definition_3_1_2_1`, the source-facing
  Fenchel-conjugate owner;
- `fenchelBidual` with the notation `f⋆⋆` from `Chap03/Theorem_3_1_5_2`, the canonical
  source-facing biconjugate owner.

Best owner abstraction:
- source-facing theorem: the Fenchel-Moreau `sSup` formula for a proper closed convex
  function on the canonical `EReal` surface;
- core/canonical owner: `fenchelBidual`;
- bridge/view: the explicit `sSup` formula obtained from `fenchelBidual` by the
  `dom (f⋆)`-restriction bridge under `hproper`;
- Euclidean `ℝⁿ` is only a specialization layer, already handled separately by chapter recall
  files such as `Theorem_3_20`.

Primitive data:
- `f : E → WithTop ℝ`;
- properness as `(dom f).Nonempty`;
- closed convexity as `ClosedConvexFunction f`.

Derived API:
- the owner-level equality `(f⋆⋆) x = withTopToEReal (f x)`;
- the source-facing supremum identity
  `withTopToEReal (f x) = sSup ((fun s ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆))`.

Source/core/bridge triage:
- source-facing: the displayed canonical supremum formula over `dom (f⋆)` for every `x`;
- core/canonical: `fenchelBidual`;
- bridge/view: the `dom (f⋆)`-restricted supremum bridge from `Theorem_3_1_5_2`, which supplies
  the companion `sSup` equality behind the displayed formula.

The previous file rebuilt local owners for the effective domain, closed-convexity, conjugate, and
biconjugate integrand. Those notions already live upstream on the canonical chapter surfaces
`dom`, `ClosedConvexFunction`, `f⋆`, and `f⋆⋆`, so this file keeps only the source-facing theorem
layer, with the labeled surface given by the global displayed supremum formula.

Verified local recall: `Chap03/Theorem_3_20` already records the chapter's Euclidean `ℝⁿ`
specialization, so the labeled theorem below stays on `EuclideanSpace ℝ (Fin n)`.
Semantic recall note: `lean_leansearch` timed out on the Fenchel-Moreau query in this environment,
so the repair follows the local chapter owners `fenchelBidual` and
`fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty`.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace ClosedConvexFunction

/-- Helper for Lemma 6 1: the effective epigraph of a closed convex `WithTop`-valued function is
closed. -/
lemma isClosed_effectiveEpigraph
    {f : E → WithTop ℝ} (hf : ClosedConvexFunction f) :
    IsClosed (WithTopConvexAnalysis.effectiveEpigraph f) := by
  -- The effective epigraph is the canonical constrained epigraph over `dom f`.
  simpa [WithTopConvexAnalysis.effectiveEpigraph] using hf.isClosed_constrainedEpigraph

/-- Helper for Lemma 6 1: the effective epigraph of a closed convex `WithTop`-valued function is
convex. -/
lemma convex_effectiveEpigraph
    {f : E → WithTop ℝ} (hf : ClosedConvexFunction f) :
    Convex ℝ (WithTopConvexAnalysis.effectiveEpigraph f) := by
  -- The effective epigraph is the canonical constrained epigraph over `dom f`.
  simpa [WithTopConvexAnalysis.effectiveEpigraph] using hf.convex_constrainedEpigraph

/-- Helper: every point of the effective epigraph of `f` satisfies the Fenchel
support halfspace inequality associated to `s`. -/
lemma fenchel_support_halfspace_contains_effectiveEpigraph
    {f : E → WithTop ℝ} (s : E) :
    WithTopConvexAnalysis.effectiveEpigraph f ⊆
      {p : E × ℝ | (inner ℝ s p.1 : EReal) - (f⋆) s ≤ p.2} := by
  intro p hp
  rcases WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp hp with ⟨hpdom, hp₂⟩
  have hsupport : (inner ℝ s p.1 : EReal) - withTopToEReal (f p.1) ≤ (f⋆) s :=
    fenchelDual_lower_bound_of_mem_dom hpdom
  have hsum : (inner ℝ s p.1 : EReal) ≤ (f⋆) s + withTopToEReal (f p.1) := by
    -- Rewrite the Fenchel lower bound into an additive upper bound on the support term.
    exact (EReal.sub_le_iff_le_add
      (.inl (withTopToEReal_ne_bot_of_mem_dom hpdom))
      (.inl (withTopToEReal_ne_top_of_mem_dom hpdom))).1 hsupport
  have hp₂' : withTopToEReal (f p.1) ≤ (p.2 : EReal) := by
    have hp₂real : withTopRealPart f p.1 ≤ p.2 :=
      (withTopRealPart_le_iff hpdom).2 hp₂
    rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom hpdom]
    exact_mod_cast hp₂real
  have hsum' : (inner ℝ s p.1 : EReal) ≤ (f⋆) s + p.2 := by
    -- Raise the finite epigraph height from `f p.1` to the chosen epigraph ordinate `p.2`.
    have hraise : (f⋆) s + withTopToEReal (f p.1) ≤ (f⋆) s + p.2 := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hp₂' ((f⋆) s)
    exact hsum.trans hraise
  -- Convert the additive bound back to the desired halfspace inequality.
  exact EReal.sub_le_of_le_add' hsum'

/-- Helper for Lemma 6 1: every finite epigraph basepoint `(x, withTopRealPart f x)` lies on the
frontier of `effectiveEpigraph f`. -/
lemma basepoint_mem_frontier_effectiveEpigraph
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ dom f) :
    (x, withTopRealPart f x) ∈ frontier (WithTopConvexAnalysis.effectiveEpigraph f) := by
  rw [frontier_eq_closure_inter_closure]
  constructor
  · -- The basepoint itself lies in the effective epigraph.
    exact subset_closure <|
      WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr
        ⟨hx, by
          simpa using le_of_eq (coe_withTopRealPart (f := f) hx).symm⟩
  · -- Lowering only the height coordinate leaves every neighborhood through the complement.
    refine Metric.mem_closure_iff.2 ?_
    intro ε hε
    refine ⟨(x, withTopRealPart f x - ε / 2), ?_, ?_⟩
    · intro hmem
      rcases WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp hmem with ⟨_, hle⟩
      have hlt : withTopRealPart f x - ε / 2 < withTopRealPart f x := by
        linarith
      rw [← coe_withTopRealPart hx] at hle
      have hle_real : withTopRealPart f x ≤ withTopRealPart f x - ε / 2 := by
        exact_mod_cast hle
      linarith
    · rw [Prod.dist_eq, dist_self, max_eq_right]
      · rw [Real.dist_eq]
        have hhalf_lt : ε / 2 < ε := by
          linarith
        simpa [abs_of_nonneg (by linarith : 0 ≤ ε / 2)] using hhalf_lt
      · exact dist_nonneg

/-- Helper: on a finite-dimensional real inner-product space, every interior point
of the effective domain already satisfies the Fenchel-Moreau equality. -/
theorem fenchelBidual_eq_of_mem_interior
    [FiniteDimensional ℝ E] {f : E → WithTop ℝ} (hf : ClosedConvexFunction f)
    {x : E} (hx : x ∈ interior (dom f)) :
    (f⋆⋆) x = withTopToEReal (f x) := by
  -- Interior effective-domain points admit a subgradient by the chapter's subgradient-existence
  -- theorem for finite-dimensional closed convex functions.
  have hsub : (∂ f(x)).Nonempty :=
    subdifferential_nonempty_of_convexOn_of_mem_interior hf.convexOn_withTopRealPart hx
  -- Once a subgradient exists at `x`, the existing bidual equality theorem closes the pointwise
  -- Fenchel-Moreau identity.
  exact fenchelBidual_eq_of_subdifferential_nonempty hsub

/-- Helper for Lemma 6 1: `effectiveEpigraph f` transported to the `WithLp 2` product owner used
by the separation theorems. -/
abbrev effectiveEpigraphProdL2
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → WithTop ℝ) :
    Set (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ⁻¹'
    WithTopConvexAnalysis.effectiveEpigraph f

/-- Helper for Lemma 6 1: a supporting nesterovHyperplane of the effective epigraph with negative height
component yields a genuine subgradient at the contact point. -/
lemma mem_subdifferential_of_supportingHyperplane_effectiveEpigraph
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    {z : EuclideanSpace ℝ (Fin n)} {normal : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)}
    {γ : ℝ} (hz : z ∈ dom f)
    (hcontact : WithLp.toLp 2 (z, withTopRealPart f z) ∈ nesterovHyperplane normal γ)
    (hsupport : IsSupportingHyperplane (effectiveEpigraphProdL2 f) normal γ)
    (hsnd : normal.snd < 0) :
    ((-normal.snd)⁻¹ • normal.fst) ∈ ∂ f(z) := by
  let a : ℝ := -normal.snd
  let s : EuclideanSpace ℝ (Fin n) := a⁻¹ • normal.fst
  have ha_pos : 0 < a := by
    -- The normalized height coefficient is positive because the supporting nesterovHyperplane points
    -- downward in the epigraph direction.
    dsimp [a]
    linarith
  have hs_eq : a • s = normal.fst := by
    -- Scaling the normalized spatial part by `a` recovers the original separator direction.
    dsimp [s]
    rw [smul_smul]
    have ha_inv : a * a⁻¹ = 1 := by
      field_simp [ha_pos.ne']
    rw [ha_inv, one_smul]
  have hcontact' : inner ℝ normal.fst z + normal.snd * withTopRealPart f z = γ := by
    -- Rewrite the contact point from the `WithLp` nesterovHyperplane owner into pair coordinates.
    have hraw : inner ℝ normal.fst z + inner ℝ normal.snd (withTopRealPart f z) = γ := by
      simpa [nesterovHyperplane, WithLp.prod_inner_apply] using hcontact
    rw [real_inner_scalar_eq_mul] at hraw
    exact hraw
  have hsupport' :
      ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ dom f →
        inner ℝ normal.fst y + normal.snd * withTopRealPart f y ≤ γ := by
    intro y hy
    -- Evaluate the supporting-halfspace inequality at the canonical finite epigraph point
    -- `(y, withTopRealPart f y)`.
    have hy_epi :
        WithLp.toLp 2 (y, withTopRealPart f y) ∈ effectiveEpigraphProdL2 f := by
      have hy_epi_raw :
          (y, withTopRealPart f y) ∈ WithTopConvexAnalysis.effectiveEpigraph f := by
        exact WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr
          ⟨hy, by
            simpa using le_of_eq (coe_withTopRealPart (f := f) hy).symm⟩
      simpa [effectiveEpigraphProdL2, Set.preimage] using hy_epi_raw
    exact supporting_hyperplane_component_inequality_prodL2 hsupport hy_epi
  rw [mem_subdifferential_iff]
  constructor
  · exact hz
  · intro y hy
    -- After normalizing the supporting inequality by `a`, the affine support inequality is
    -- exactly the subgradient condition.
    have hy_bound : inner ℝ normal.fst y - a * withTopRealPart f y ≤ γ := by
      have hy_raw := hsupport' hy
      dsimp [a] at hy_raw ⊢
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy_raw
    have hz_contact : inner ℝ normal.fst z - a * withTopRealPart f z = γ := by
      dsimp [a] at hcontact' ⊢
      linarith
    have hdiff :
        inner ℝ normal.fst (y - z) ≤ a * (withTopRealPart f y - withTopRealPart f z) := by
      have hdiff' :
          inner ℝ normal.fst y - inner ℝ normal.fst z ≤
            a * (withTopRealPart f y - withTopRealPart f z) := by
        linarith
      simpa [inner_sub_right] using hdiff'
    have hscaled :
        inner ℝ s (y - z) ≤ withTopRealPart f y - withTopRealPart f z := by
      have hmul :
          a⁻¹ * inner ℝ normal.fst (y - z) ≤
            a⁻¹ * (a * (withTopRealPart f y - withTopRealPart f z)) :=
        mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr ha_pos.le)
      have hdiv :
          a⁻¹ * inner ℝ normal.fst (y - z) ≤
            withTopRealPart f y - withTopRealPart f z := by
        simpa [ha_pos.ne', mul_assoc] using hmul
      simpa [s, real_inner_smul_left] using hdiv
    have hreal :
        withTopRealPart f z + inner ℝ s (y - z) ≤ withTopRealPart f y := by
      linarith
    have hwithTop :
        (((withTopRealPart f z + inner ℝ s (y - z) : ℝ) : WithTop ℝ) ≤
          (withTopRealPart f y : WithTop ℝ)) := by
      exact_mod_cast hreal
    -- Return from real coordinates to the original `WithTop`-valued subgradient inequality.
    rw [← coe_withTopRealPart (f := f) hy, ← coe_withTopRealPart (f := f) hz]
    simpa [a, s, WithTop.coe_add, inv_neg, real_inner_smul_left] using hwithTop

/-- Helper for Lemma 6 1: one primal domain point and a finite real upper bound on `(f⋆) s`
already certify that `s` lies in the effective domain of the Fenchel dual. -/
lemma mem_dom_fenchelDual_of_le_realBound
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    (hdom : (dom f).Nonempty) {s : EuclideanSpace ℝ (Fin n)} {bound : ℝ}
    (hdual_le : (f⋆) s ≤ (bound : EReal)) :
    s ∈ dom (f⋆) := by
  rcases hdom with ⟨y0, hy0⟩
  have hdual_ne_bot : (f⋆) s ≠ ⊥ :=
    fenchelDual_ne_bot_of_mem_dom (f := f) (s := s) hy0
  have hdual_ne_top : (f⋆) s ≠ ⊤ := by
    -- The finite real upper bound rules out the value `⊤`.
    exact ne_of_lt (lt_of_le_of_lt hdual_le (lt_top_iff_ne_top.mpr (EReal.coe_ne_top _)))
  -- Packaging the two finite-value facts places `s` in the effective domain of `f⋆`.
  exact (mem_extendedRealEffectiveDomain_iff).2 ⟨hdual_ne_top, hdual_ne_bot⟩

/-- Helper for Lemma 6 1: once the separator inequalities are written in pair coordinates, a
negative height coefficient can be normalized into a finite Fenchel-dual support witness. -/
lemma supportTerm_gt_of_componentBounds_effectiveEpigraph
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    (hdom : (dom f).Nonempty) {x : EuclideanSpace ℝ (Fin n)} {t γ : ℝ}
    {normal : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)}
    (hupper : ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ dom f →
      inner ℝ normal.fst y + normal.snd * withTopRealPart f y ≤ γ)
    (hstrict : γ < inner ℝ normal.fst x + normal.snd * t)
    (hsnd : normal.snd < 0) :
    ∃ s ∈ dom (f⋆), (t : EReal) < (inner ℝ s x : EReal) - (f⋆) s := by
  let a : ℝ := -normal.snd
  let s : EuclideanSpace ℝ (Fin n) := a⁻¹ • normal.fst
  have ha_pos : 0 < a := by
    -- The normalization denominator is the positive opposite of the separator height.
    dsimp [a]
    linarith
  have hs_eq : a • s = normal.fst := by
    -- Scaling the normalized vector `s` by `a` recovers the original spatial separator.
    dsimp [s]
    rw [smul_smul]
    have ha_inv : a * a⁻¹ = 1 := by
      field_simp [ha_pos.ne']
    rw [ha_inv, one_smul]
  have hupperScaled :
      ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ dom f →
        (inner ℝ s y : EReal) - withTopToEReal (f y) ≤ (γ / a : EReal) := by
    intro y hy
    have hupper' : inner ℝ normal.fst y - a * withTopRealPart f y ≤ γ := by
      -- Rewrite the separator bound so the negative height coefficient appears as `-a`.
      have hbase := hupper hy
      dsimp [a] at hbase ⊢
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbase
    have hscaledMul : a * (inner ℝ s y - withTopRealPart f y) ≤ γ := by
      -- Multiply the desired affine term by `a` to match the original separator normal.
      rw [mul_sub, ← real_inner_smul_left, hs_eq]
      exact hupper'
    have hscaled :
        inner ℝ s y - withTopRealPart f y ≤ γ / a := by
      -- Divide back by the positive scalar `a`.
      exact (le_div_iff₀ ha_pos).2 (by simpa [mul_comm] using hscaledMul)
    -- Move from the finite real coordinates back to the canonical `EReal` surface.
    have hscaledEReal :
        ((inner ℝ s y - withTopRealPart f y : ℝ) : EReal) ≤ (γ / a : EReal) := by
      rw [← EReal.coe_div]
      exact_mod_cast hscaled
    simpa [EReal.coe_sub, withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy] using
      hscaledEReal
  have hdual_le : (f⋆) s ≤ (γ / a : EReal) := by
    -- The normalized affine terms bound every contributor to the Fenchel-dual supremum.
    rw [fenchelDual_apply_eq_sSup_image_dom]
    refine sSup_le ?_
    rintro z ⟨y, hy, rfl⟩
    exact hupperScaled hy
  have hs_mem : s ∈ dom (f⋆) := by
    -- The finite dual upper bound makes the normalized vector a genuine dual point.
    exact mem_dom_fenchelDual_of_le_realBound (f := f) hdom hdual_le
  have hstrictMul : γ < a * (inner ℝ s x - t) := by
    -- Rewrite the strict separated-point inequality in the normalized coordinates.
    have hrewrite : a * (inner ℝ s x - t) = inner ℝ normal.fst x + normal.snd * t := by
      rw [mul_sub, ← real_inner_smul_left, hs_eq]
      dsimp [a]
      ring_nf
    simpa [hrewrite] using hstrict
  have hstrictReal : t < inner ℝ s x - γ / a := by
    -- Divide the strict inequality by the positive scalar `a`.
    have hdiv : γ / a < inner ℝ s x - t := by
      exact (div_lt_iff₀ ha_pos).2 (by simpa [mul_comm] using hstrictMul)
    linarith
  have hterm_le :
      ((inner ℝ s x - γ / a : ℝ) : EReal) ≤ (inner ℝ s x : EReal) - (f⋆) s := by
    -- Replacing the finite upper bound `γ / a` by `(f⋆) s` only increases the support term.
    have hs_mem' := mem_extendedRealEffectiveDomain_iff.mp hs_mem
    rw [EReal.le_sub_iff_add_le (.inl hs_mem'.2) (.inr (EReal.coe_ne_top _))]
    have hsum :
        ((inner ℝ s x - γ / a : ℝ) : EReal) + (f⋆) s ≤
          ((inner ℝ s x - γ / a : ℝ) : EReal) + (γ / a : EReal) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hdual_le ((inner ℝ s x - γ / a : ℝ) : EReal)
    have hcancel :
        ((inner ℝ s x - γ / a : ℝ) : EReal) + (γ / a : EReal) = (inner ℝ s x : EReal) := by
      rw [← EReal.coe_div, ← EReal.coe_add]
      ring_nf
    exact hsum.trans_eq hcancel
  have hterm_lt :
      (t : EReal) < (inner ℝ s x : EReal) - (f⋆) s := by
    have hstrictEReal : (t : EReal) < ((inner ℝ s x - γ / a : ℝ) : EReal) := by
      exact_mod_cast hstrictReal
    exact lt_of_lt_of_le hstrictEReal hterm_le
  exact ⟨s, hs_mem, hterm_lt⟩

/-- Helper for Lemma 6 1: a strict separator of the effective epigraph with negative height
component yields a genuine dual support term above the separated height. -/
lemma supportTerm_gt_of_strictSeparator_effectiveEpigraph
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    (hdom : (dom f).Nonempty) {x : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    {normal : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)} {γ : ℝ}
    (hsep : SeparatesPointFromWith
      (effectiveEpigraphProdL2 f) (WithLp.toLp 2 (x, t)) normal γ)
    (hstrict : γ < inner ℝ normal (WithLp.toLp 2 (x, t))) (hsnd : normal.snd < 0) :
    ∃ s ∈ dom (f⋆), (t : EReal) < (inner ℝ s x : EReal) - (f⋆) s := by
  let e : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × ℝ :=
    WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ
  have hupper :
      ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ dom f →
        inner ℝ normal.fst y + normal.snd * withTopRealPart f y ≤ γ := by
    intro y hy
    -- Route correction: rewrite the `WithLp` separator once into pair coordinates before doing
    -- any duality algebra.
    have hy_epi :
        WithLp.toLp 2 (y, withTopRealPart f y) ∈ effectiveEpigraphProdL2 f := by
      have hy_epi_raw :
          (y, withTopRealPart f y) ∈ WithTopConvexAnalysis.effectiveEpigraph f := by
        exact WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr
          ⟨hy, by
            simpa using le_of_eq (coe_withTopRealPart (f := f) hy).symm⟩
      simpa [effectiveEpigraphProdL2, e, Set.preimage] using hy_epi_raw
    have hle : inner ℝ normal (WithLp.toLp 2 (y, withTopRealPart f y)) ≤ γ :=
      hsep.le_offset hy_epi
    have hle' : inner ℝ normal.fst y + inner ℝ normal.snd (withTopRealPart f y) ≤ γ := by
      simpa [WithLp.prod_inner_apply] using hle
    rwa [real_inner_scalar_eq_mul] at hle'
  have hstrict' : γ < inner ℝ normal.fst x + normal.snd * t := by
    -- The separated point itself is rewritten into the same pair-coordinate spelling.
    have hstrict'raw : γ < inner ℝ normal (WithLp.toLp 2 (x, t)) := hstrict
    have hstrict'' : γ < inner ℝ normal.fst x + inner ℝ normal.snd t := by
      simpa [WithLp.prod_inner_apply] using hstrict'raw
    rwa [real_inner_scalar_eq_mul] at hstrict''
  exact supportTerm_gt_of_componentBounds_effectiveEpigraph
    (f := f) hdom hupper hstrict' hsnd

/-- Helper for Lemma 6 1: every real level strictly below the finite value `f x` is exceeded by
some dual support term at `x`. -/
lemma exists_supportTerm_gt_of_mem_dom_lt
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    (hf : ClosedConvexFunction f) (hdom : (dom f).Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ dom f) {r : ℝ}
    (hr : (r : EReal) < withTopToEReal (f x)) :
    ∃ s ∈ dom (f⋆), (r : EReal) < (inner ℝ s x : EReal) - (f⋆) s := by
  let e : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × ℝ :=
    WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ
  have hnot_epi : (x, r) ∉ WithTopConvexAnalysis.effectiveEpigraph f := by
    intro hmem
    rcases WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp hmem with ⟨_, hle⟩
    rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hx] at hr
    have hle' : withTopRealPart f x ≤ r := by
      rw [← coe_withTopRealPart (f := f) hx] at hle
      exact_mod_cast hle
    exact (not_le_of_gt (by simpa using hr)) hle'
  have hnot_prod : WithLp.toLp 2 (x, r) ∉ effectiveEpigraphProdL2 f := by
    intro hmem
    exact hnot_epi (by simpa [effectiveEpigraphProdL2, e, Set.preimage] using hmem)
  obtain ⟨normal, γ, hsep, hstrict⟩ :=
    exists_strictlySeparating_hyperplane_of_nonmem_closed_convex
      (effectiveEpigraphProdL2 f)
      (by
        simpa [effectiveEpigraphProdL2, e] using
          (isClosed_effectiveEpigraph hf).preimage e.continuous)
      (by
        simpa [effectiveEpigraphProdL2, e] using
          (convex_effectiveEpigraph hf).linear_preimage e.toLinearMap)
      hnot_prod
  have hx_epi :
      WithLp.toLp 2 (x, withTopRealPart f x) ∈ effectiveEpigraphProdL2 f := by
    have hx_epi_raw :
        (x, withTopRealPart f x) ∈ WithTopConvexAnalysis.effectiveEpigraph f := by
      exact WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr
        ⟨hx, by
          simpa using le_of_eq (coe_withTopRealPart (f := f) hx).symm⟩
    simpa [effectiveEpigraphProdL2, e, Set.preimage] using hx_epi_raw
  have hsnd_neg : normal.snd < 0 := by
    have hle_pair :
        inner ℝ normal.fst x + normal.snd * withTopRealPart f x ≤ γ := by
      have hle : inner ℝ normal (WithLp.toLp 2 (x, withTopRealPart f x)) ≤ γ :=
        hsep.le_offset hx_epi
      have hle' : inner ℝ normal.fst x + inner ℝ normal.snd (withTopRealPart f x) ≤ γ := by
        simpa [WithLp.prod_inner_apply] using hle
      rw [real_inner_scalar_eq_mul] at hle'
      exact hle'
    have hstrict_pair' :
        γ < inner ℝ normal.fst x + normal.snd * r := by
      have hstrict' : γ < inner ℝ normal (WithLp.toLp 2 (x, r)) := hstrict
      have hstrict'' : γ < inner ℝ normal.fst x + inner ℝ normal.snd r := by
        simpa [WithLp.prod_inner_apply] using hstrict'
      rwa [real_inner_scalar_eq_mul] at hstrict''
    have hr_real : r < withTopRealPart f x := by
      rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hx] at hr
      simpa using hr
    by_contra hsnd_nonneg
    have hsnd_nonneg' : 0 ≤ normal.snd := le_of_not_gt hsnd_nonneg
    by_cases hsnd_zero : normal.snd = 0
    · rw [hsnd_zero] at hle_pair hstrict_pair'
      linarith
    · have hsnd_pos' : 0 < normal.snd := by
        exact lt_of_le_of_ne hsnd_nonneg' (by simpa [eq_comm] using hsnd_zero)
      have hmul : normal.snd * r < normal.snd * withTopRealPart f x := by
        exact mul_lt_mul_of_pos_left hr_real hsnd_pos'
      linarith
  -- Apply the separator-to-support-term bridge with the now-proved negative height component.
  exact supportTerm_gt_of_strictSeparator_effectiveEpigraph
    (f := f) hdom hsep hstrict hsnd_neg

/-- Helper for Lemma 6 1: a finite real upper bound on `(f⋆) s` converts a real lower bound on
`inner s x - bound` into the corresponding strict Fenchel support inequality. -/
lemma lt_supportTerm_of_dual_le_realBound
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    {s x : EuclideanSpace ℝ (Fin n)} {bound r : ℝ}
    (hs_mem : s ∈ dom (f⋆)) (hdual_le : (f⋆) s ≤ (bound : EReal))
    (hstrictReal : r < inner ℝ s x - bound) :
    (r : EReal) < (inner ℝ s x : EReal) - (f⋆) s := by
  have hterm_le :
      ((inner ℝ s x - bound : ℝ) : EReal) ≤ (inner ℝ s x : EReal) - (f⋆) s := by
    -- Replacing `(f⋆) s` by the finite upper bound `bound` only decreases the support term.
    have hs_mem' := mem_extendedRealEffectiveDomain_iff.mp hs_mem
    rw [EReal.le_sub_iff_add_le (.inl hs_mem'.2) (.inr (EReal.coe_ne_top _))]
    have hsum :
        ((inner ℝ s x - bound : ℝ) : EReal) + (f⋆) s ≤
          ((inner ℝ s x - bound : ℝ) : EReal) + (bound : EReal) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hdual_le (((inner ℝ s x - bound : ℝ) : EReal))
    have hcancel :
        ((inner ℝ s x - bound : ℝ) : EReal) + (bound : EReal) = (inner ℝ s x : EReal) := by
      exact_mod_cast (sub_add_cancel (inner ℝ s x) bound)
    exact hsum.trans_eq hcancel
  have hstrictEReal : (r : EReal) < ((inner ℝ s x - bound : ℝ) : EReal) := by
    exact_mod_cast hstrictReal
  exact lt_of_lt_of_le hstrictEReal hterm_le

/-- Helper for Lemma 6 1: once a global affine lower support is available at `y0`, any point
outside `closure (dom f)` forces the Fenchel support terms at `x` to grow above every prescribed
real level. -/
lemma exists_supportTerm_gt_of_not_mem_closure_of_subgradient
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    {y0 x g : EuclideanSpace ℝ (Fin n)}
    (hf : ClosedConvexFunction f) (hy0 : y0 ∈ dom f) (hg : g ∈ ∂ f(y0))
    (hxclosure : x ∉ closure (dom f)) (r : ℝ) :
    ∃ s ∈ dom (f⋆), (r : EReal) < (inner ℝ s x : EReal) - (f⋆) s := by
  by_cases htriv : Subsingleton (EuclideanSpace ℝ (Fin n))
  · -- In the trivial space, `x = y0`, so `x` cannot lie outside `closure (dom f)`.
    have hxmem : x ∈ closure (dom f) := by
      simpa [Subsingleton.elim x y0] using subset_closure hy0
    exact (hxclosure hxmem).elim
  · letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := not_subsingleton_iff_nontrivial.mp htriv
    obtain ⟨normal, γ, hsep, hstrict⟩ :=
      exists_strictlySeparating_hyperplane_of_nonmem_closed_convex
        (closure (dom f)) isClosed_closure (hf.convexOn_withTopRealPart.1.closure) hxclosure
    let c : ℝ := inner ℝ g y0 - withTopRealPart f y0
    let base : ℝ := inner ℝ g x - c
    let δ : ℝ := inner ℝ normal x - γ
    have hδ_pos : 0 < δ := by
      -- The strict primal separator leaves a positive margin at `x`.
      dsimp [δ]
      linarith
    let scale : ℝ := max 0 ((r - base + 1) / δ)
    let s : EuclideanSpace ℝ (Fin n) := g + scale • normal
    let bound : ℝ := c + scale * γ
    have hscale_nonneg : 0 ≤ scale := by
      -- The scaling parameter is chosen nonnegative so the primal separator keeps its sign.
      dsimp [scale]
      exact le_max_left _ _
    have hsub : IsSubgradientAt f y0 g := mem_subdifferential_iff.mp hg
    have hupperReal :
        ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ dom f →
          inner ℝ s y - withTopRealPart f y ≤ bound := by
      intro y hy
      have hgReal :
          inner ℝ g y - withTopRealPart f y ≤ c := by
        -- Rewrite the subgradient inequality at `y0` as a global affine minorant bound.
        have hineq : f y ≥ f y0 + (inner ℝ g (y - y0) : WithTop ℝ) := hsub.2 hy
        rw [← coe_withTopRealPart (f := f) hy, ← coe_withTopRealPart (f := f) hy0] at hineq
        have hreal : withTopRealPart f y0 + inner ℝ g (y - y0) ≤ withTopRealPart f y := by
          exact_mod_cast hineq
        dsimp [c]
        have hinner : inner ℝ g y = inner ℝ g y0 + inner ℝ g (y - y0) := by
          calc
            inner ℝ g y = inner ℝ g (y0 + (y - y0)) := by simp
            _ = inner ℝ g y0 + inner ℝ g (y - y0) := by rw [inner_add_right]
        calc
          inner ℝ g y - withTopRealPart f y
              = inner ℝ g y0 + inner ℝ g (y - y0) - withTopRealPart f y := by rw [hinner]
          _ ≤ inner ℝ g y0 - withTopRealPart f y0 := by linarith
          _ = c := by simp [c]
      have hnormal : inner ℝ normal y ≤ γ := hsep.le_offset (subset_closure hy)
      have hscaled : scale * inner ℝ normal y ≤ scale * γ :=
        mul_le_mul_of_nonneg_left hnormal hscale_nonneg
      -- Add the affine minorant bound and the scaled primal separator bound.
      have hs_eq :
          inner ℝ s y - withTopRealPart f y =
            (inner ℝ g y - withTopRealPart f y) + scale * inner ℝ normal y := by
        dsimp [s]
        rw [show inner ℝ (g + scale • normal) y = inner ℝ g y + scale * inner ℝ normal y by
          rw [inner_add_left, real_inner_smul_left]]
        ring
      rw [hs_eq]
      linarith
    have hdual_le : (f⋆) s ≤ (bound : EReal) := by
      -- The affine minorant plus the primal separator gives a finite upper bound on `f⋆ s`.
      rw [fenchelDual_apply_eq_sSup_image_dom]
      refine sSup_le ?_
      rintro z ⟨y, hy, rfl⟩
      have hreal := hupperReal hy
      have hEReal :
          ((inner ℝ s y - withTopRealPart f y : ℝ) : EReal) ≤ (bound : EReal) := by
        exact_mod_cast hreal
      simpa [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy, EReal.coe_sub] using
        hEReal
    have hs_mem : s ∈ dom (f⋆) := by
      -- The affine upper bound keeps the perturbed support vector inside `dom (f⋆)`.
      exact mem_dom_fenchelDual_of_le_realBound (f := f) ⟨y0, hy0⟩ hdual_le
    have hscale_mul :
        r - base + 1 ≤ scale * δ := by
      -- The `max` choice guarantees a large enough multiple of the separation margin `δ`.
      have hquot_le : (r - base + 1) / δ ≤ scale := by
        dsimp [scale]
        exact le_max_right _ _
      have hmul :=
        mul_le_mul_of_nonneg_right hquot_le hδ_pos.le
      have hcancel : ((r - base + 1) / δ) * δ = r - base + 1 := by
        field_simp [hδ_pos.ne']
      rw [hcancel] at hmul
      exact hmul
    have hstrictReal : r < inner ℝ s x - bound := by
      -- The scaled separator margin dominates the prescribed real level.
      have hs_eq : inner ℝ s x - bound = base + scale * δ := by
        dsimp [s, bound, base, c, δ]
        rw [show inner ℝ (g + scale • normal) x = inner ℝ g x + scale * inner ℝ normal x by
          simp [inner_add_left, real_inner_smul_left]]
        ring
      rw [hs_eq]
      linarith [hscale_mul]
    have hterm_lt : (r : EReal) < (inner ℝ s x : EReal) - (f⋆) s :=
      lt_supportTerm_of_dual_le_realBound (f := f) hs_mem hdual_le hstrictReal
    exact ⟨s, hs_mem, hterm_lt⟩

/-- Helper for Lemma 6 1: if `(x, t)` is strictly separated from the effective epigraph and
`x` lies in `closure (dom f)`, then the separator must point downward in the height direction. -/
lemma snd_neg_of_strictSeparator_effectiveEpigraph_of_mem_closure
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    (hdom : (dom f).Nonempty) {x : EuclideanSpace ℝ (Fin n)} {t γ : ℝ}
    {normal : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)}
    (hxclosure : x ∈ closure (dom f))
    (hsep : SeparatesPointFromWith
      (effectiveEpigraphProdL2 f) (WithLp.toLp 2 (x, t)) normal γ)
    (hstrict : γ < inner ℝ normal (WithLp.toLp 2 (x, t))) :
    normal.snd < 0 := by
  rcases hdom with ⟨y0, hy0⟩
  have hsnd_nonpos : normal.snd ≤ 0 := by
    -- Testing the separator on arbitrarily high vertical points forbids a positive height
    -- coefficient.
    by_contra hsnd_pos
    have hsnd_pos : 0 < normal.snd := lt_of_not_ge hsnd_pos
    let τ : ℝ :=
      max (withTopRealPart f y0) ((γ - inner ℝ normal.fst y0 + 1) / normal.snd)
    have hτ_mem :
        WithLp.toLp 2 (y0, τ) ∈ effectiveEpigraphProdL2 f := by
      have hτ_mem_raw :
          (y0, τ) ∈ WithTopConvexAnalysis.effectiveEpigraph f := by
        refine WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr ?_
        refine ⟨hy0, ?_⟩
        rw [← coe_withTopRealPart (f := f) hy0]
        exact_mod_cast le_max_left (withTopRealPart f y0)
          ((γ - inner ℝ normal.fst y0 + 1) / normal.snd)
      simpa [effectiveEpigraphProdL2, Set.preimage] using hτ_mem_raw
    have hτ_upper : inner ℝ normal.fst y0 + normal.snd * τ ≤ γ := by
      have hτ_le : inner ℝ normal (WithLp.toLp 2 (y0, τ)) ≤ γ := hsep.le_offset hτ_mem
      have hτ_le' : inner ℝ normal.fst y0 + inner ℝ normal.snd τ ≤ γ := by
        simpa [WithLp.prod_inner_apply] using hτ_le
      rwa [real_inner_scalar_eq_mul] at hτ_le'
    have hτ_lower : γ + 1 ≤ inner ℝ normal.fst y0 + normal.snd * τ := by
      have hτ_large :
          (γ - inner ℝ normal.fst y0 + 1) ≤ normal.snd * τ := by
        have hτ_large' :
            ((γ - inner ℝ normal.fst y0 + 1) / normal.snd) ≤ τ :=
          le_max_right (withTopRealPart f y0)
            ((γ - inner ℝ normal.fst y0 + 1) / normal.snd)
        have hmul :
            γ - inner ℝ normal.fst y0 + 1 ≤ τ * normal.snd :=
          (div_le_iff₀ hsnd_pos).1 hτ_large'
        simpa [mul_comm] using hmul
      linarith
    linarith
  have hsnd_ne_zero : normal.snd ≠ 0 := by
    -- A vertical separator would already separate `x` from `closure (dom f)`, contradicting the
    -- closure hypothesis.
    intro hsnd_zero
    have hsubset :
        dom f ⊆ {y : EuclideanSpace ℝ (Fin n) | inner ℝ normal.fst y ≤ γ} := by
      intro y hy
      have hy_mem :
          WithLp.toLp 2 (y, withTopRealPart f y) ∈ effectiveEpigraphProdL2 f := by
        have hy_mem_raw :
            (y, withTopRealPart f y) ∈ WithTopConvexAnalysis.effectiveEpigraph f := by
          exact WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr
            ⟨hy, by
              simpa using le_of_eq (coe_withTopRealPart (f := f) hy).symm⟩
        simpa [effectiveEpigraphProdL2, Set.preimage] using hy_mem_raw
      have hy_le : inner ℝ normal (WithLp.toLp 2 (y, withTopRealPart f y)) ≤ γ :=
        hsep.le_offset hy_mem
      have hy_le' : inner ℝ normal.fst y + inner ℝ normal.snd (withTopRealPart f y) ≤ γ := by
        simpa [WithLp.prod_inner_apply] using hy_le
      rw [real_inner_scalar_eq_mul, hsnd_zero, zero_mul, add_zero] at hy_le'
      exact hy_le'
    have hclosed_halfspace :
        IsClosed {y : EuclideanSpace ℝ (Fin n) | inner ℝ normal.fst y ≤ γ} := by
      simpa using isClosed_le (continuous_const.inner continuous_id) continuous_const
    have hx_le : inner ℝ normal.fst x ≤ γ := by
      exact closure_minimal hsubset hclosed_halfspace hxclosure
    have hstrict' : γ < inner ℝ normal.fst x := by
      have hstrict'raw : γ < inner ℝ normal.fst x + inner ℝ normal.snd t := by
        have hstrict'' : γ < inner ℝ normal (WithLp.toLp 2 (x, t)) := hstrict
        simpa [WithLp.prod_inner_apply] using hstrict''
      rw [real_inner_scalar_eq_mul, hsnd_zero, zero_mul, add_zero] at hstrict'raw
      exact hstrict'raw
    linarith
  exact lt_of_le_of_ne hsnd_nonpos hsnd_ne_zero

/-- Helper for Lemma 6 1: strict separation of the effective epigraph at a closure-domain point
already yields the desired Fenchel support witness. -/
lemma exists_supportTerm_gt_of_mem_closure_not_mem_dom
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    (hf : ClosedConvexFunction f) (hdom : (dom f).Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hxclosure : x ∈ closure (dom f)) (hx : x ∉ dom f) (r : ℝ) :
    ∃ s ∈ dom (f⋆), (r : EReal) < (inner ℝ s x : EReal) - (f⋆) s := by
  let e : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × ℝ :=
    WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ
  have hnot_epi : (x, r) ∉ WithTopConvexAnalysis.effectiveEpigraph f := by
    intro hmem
    exact hx (WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp hmem).1
  have hnot_prod : WithLp.toLp 2 (x, r) ∉ effectiveEpigraphProdL2 f := by
    intro hmem
    exact hnot_epi (by simpa [effectiveEpigraphProdL2, e, Set.preimage] using hmem)
  obtain ⟨normal, γ, hsep, hstrict⟩ :=
    exists_strictlySeparating_hyperplane_of_nonmem_closed_convex
      (effectiveEpigraphProdL2 f)
      (by
        simpa [effectiveEpigraphProdL2, e] using
          (isClosed_effectiveEpigraph hf).preimage e.continuous)
      (by
        simpa [effectiveEpigraphProdL2, e] using
          (convex_effectiveEpigraph hf).linear_preimage e.toLinearMap)
      hnot_prod
  have hsnd_neg : normal.snd < 0 :=
    snd_neg_of_strictSeparator_effectiveEpigraph_of_mem_closure
      (f := f) hdom hxclosure hsep hstrict
  -- The existing separator-to-support bridge now closes the closure branch immediately.
  exact supportTerm_gt_of_strictSeparator_effectiveEpigraph
    (f := f) hdom hsep hstrict hsnd_neg

/-- Helper for Lemma 6 1: a finite Fenchel-dual point together with a strict separator of
`closure (dom f)` is enough to force support terms above every prescribed real level. -/
lemma exists_supportTerm_gt_of_not_mem_closure
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    (hf : ClosedConvexFunction f) (hdom : (dom f).Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hxclosure : x ∉ closure (dom f)) (r : ℝ) :
    ∃ s ∈ dom (f⋆), (r : EReal) < (inner ℝ s x : EReal) - (f⋆) s := by
  rcases hdom with ⟨y0, hy0⟩
  have hy0_strict :
      ((withTopRealPart f y0 - 1 : ℝ) : EReal) < withTopToEReal (f y0) := by
    rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy0]
    exact_mod_cast (show withTopRealPart f y0 - 1 < withTopRealPart f y0 by linarith)
  obtain ⟨s0, hs0, _⟩ :=
    exists_supportTerm_gt_of_mem_dom_lt (f := f) hf ⟨y0, hy0⟩ hy0 hy0_strict
  by_cases htriv : Subsingleton (EuclideanSpace ℝ (Fin n))
  · -- In the trivial space, `x = y0`, so `x` cannot lie outside `closure (dom f)`.
    have hxmem : x ∈ closure (dom f) := by
      simpa [Subsingleton.elim x y0] using subset_closure hy0
    exact (hxclosure hxmem).elim
  · letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := not_subsingleton_iff_nontrivial.mp htriv
    obtain ⟨normal, γ, hsep, hstrict⟩ :=
      exists_strictlySeparating_hyperplane_of_nonmem_closed_convex
        (closure (dom f)) isClosed_closure (hf.convexOn_withTopRealPart.1.closure) hxclosure
    let base : ℝ := inner ℝ s0 x - ((f⋆) s0).toReal
    let δ : ℝ := inner ℝ normal x - γ
    have hδ_pos : 0 < δ := by
      -- The strict primal separator leaves a positive margin at `x`.
      dsimp [δ]
      linarith
    let scale : ℝ := max 0 ((r - base + 1) / δ)
    let s : EuclideanSpace ℝ (Fin n) := s0 + scale • normal
    let bound : ℝ := ((f⋆) s0).toReal + scale * γ
    have hscale_nonneg : 0 ≤ scale := by
      -- The scaling parameter is chosen nonnegative so the primal separator keeps its sign.
      dsimp [scale]
      exact le_max_left _ _
    have hs0_mem := mem_extendedRealEffectiveDomain_iff.mp hs0
    have hupperReal :
        ∀ ⦃y : EuclideanSpace ℝ (Fin n)⦄, y ∈ dom f →
          inner ℝ s y - withTopRealPart f y ≤ bound := by
      intro y hy
      have hs0_upper : inner ℝ s0 y - withTopRealPart f y ≤ ((f⋆) s0).toReal := by
        -- Finite dual points provide a global affine upper bound on the support terms.
        have hfenchel :
            (inner ℝ s0 y : EReal) - withTopToEReal (f y) ≤ (f⋆) s0 :=
          fenchelDual_lower_bound_of_mem_dom (f := f) (s := s0) hy
        rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy] at hfenchel
        have hfenchel' :
            ((inner ℝ s0 y - withTopRealPart f y : ℝ) : EReal) ≤ (((f⋆) s0).toReal : EReal) := by
          rw [EReal.coe_toReal hs0_mem.1 hs0_mem.2]
          simpa [EReal.coe_sub] using hfenchel
        exact_mod_cast hfenchel'
      have hnormal : inner ℝ normal y ≤ γ := hsep.le_offset (subset_closure hy)
      have hscaled : scale * inner ℝ normal y ≤ scale * γ :=
        mul_le_mul_of_nonneg_left hnormal hscale_nonneg
      -- Add the finite dual bound and the scaled primal separator bound.
      have hs_eq :
          inner ℝ s y - withTopRealPart f y =
            (inner ℝ s0 y - withTopRealPart f y) + scale * inner ℝ normal y := by
        dsimp [s]
        rw [show inner ℝ (s0 + scale • normal) y = inner ℝ s0 y + scale * inner ℝ normal y by
          rw [inner_add_left, real_inner_smul_left]]
        ring
      rw [hs_eq]
      linarith
    have hdual_le : (f⋆) s ≤ (bound : EReal) := by
      -- The finite affine bound above every domain point controls the dual value of `s`.
      rw [fenchelDual_apply_eq_sSup_image_dom]
      refine sSup_le ?_
      rintro z ⟨y, hy, rfl⟩
      have hreal := hupperReal hy
      have hEReal :
          ((inner ℝ s y - withTopRealPart f y : ℝ) : EReal) ≤ (bound : EReal) := by
        exact_mod_cast hreal
      simpa [bound, withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hy, EReal.coe_sub]
        using hEReal
    have hs_mem : s ∈ dom (f⋆) := by
      -- The finite dual upper bound keeps the shifted support vector inside `dom (f⋆)`.
      exact mem_dom_fenchelDual_of_le_realBound (f := f) ⟨y0, hy0⟩ hdual_le
    have hscale_mul :
        r - base + 1 ≤ scale * δ := by
      -- The `max` choice guarantees a large enough multiple of the separation margin `δ`.
      have hquot_le : (r - base + 1) / δ ≤ scale := by
        dsimp [scale]
        exact le_max_right _ _
      have hmul :=
        mul_le_mul_of_nonneg_right hquot_le hδ_pos.le
      have hcancel : ((r - base + 1) / δ) * δ = r - base + 1 := by
        field_simp [hδ_pos.ne']
      rw [hcancel] at hmul
      exact hmul
    have hstrictReal : r < inner ℝ s x - bound := by
      -- The scaled separator margin dominates the prescribed real level.
      have hs_eq : inner ℝ s x - bound = base + scale * δ := by
        dsimp [s, bound, base, δ]
        rw [show inner ℝ (s0 + scale • normal) x = inner ℝ s0 x + scale * inner ℝ normal x by
          rw [inner_add_left, real_inner_smul_left]]
        ring
      rw [hs_eq]
      linarith [hscale_mul]
    have hterm_lt : (r : EReal) < (inner ℝ s x : EReal) - (f⋆) s :=
      lt_supportTerm_of_dual_le_realBound (f := f) hs_mem hdual_le hstrictReal
    exact ⟨s, hs_mem, hterm_lt⟩

/-- Helper for Lemma 6 1: every point outside `dom f` forces the Fenchel-bidual support supremum
above any prescribed real level. -/
lemma exists_supportTerm_gt_of_not_mem_dom
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ}
    (hf : ClosedConvexFunction f) (hdom : (dom f).Nonempty)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ dom f) (r : ℝ) :
    ∃ s ∈ dom (f⋆), (r : EReal) < (inner ℝ s x : EReal) - (f⋆) s := by
  by_cases hxclosure : x ∈ closure (dom f)
  · -- Route correction: the closure-side branch is now closed by strict separation of the
    -- effective epigraph itself, followed by the negative-height sign lemma above.
    exact exists_supportTerm_gt_of_mem_closure_not_mem_dom (f := f) hf hdom hxclosure hx r
  · -- Outside `closure (dom f)`, one finite dual point and the primal separator already suffice.
    exact exists_supportTerm_gt_of_not_mem_closure (f := f) hf hdom hxclosure r

/-- Helper: on `ℝⁿ`, a proper closed convex function agrees with its Fenchel
bidual. -/
-- Proof sketch: this is the Fenchel-Moreau theorem on the chapter owner surface `f⋆⋆`; the
-- nonempty-domain hypothesis is the source-facing properness assumption under which the bidual
-- recovers the original function.
theorem fenchelBidual_eq_of_dom_nonempty
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ} (hf : ClosedConvexFunction f)
    (hdom : (dom f).Nonempty) (x : EuclideanSpace ℝ (Fin n)) :
    (f⋆⋆) x = withTopToEReal (f x) := by
  -- Route correction: the interior-point theorem is too weak here; the remaining proof must split
  -- on `x ∈ dom f`, but the finite branch can be closed directly by separating points strictly
  -- below the graph rather than extracting an explicit subgradient first.
  by_cases hx : x ∈ dom f
  · let S : Set EReal :=
      ((fun s : EuclideanSpace ℝ (Fin n) ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆))
    have hupper : ∀ z ∈ S, z ≤ withTopToEReal (f x) := by
      intro z hz
      rcases hz with ⟨s, hs, rfl⟩
      have hsum : (inner ℝ s x : EReal) ≤ (f⋆) s + withTopToEReal (f x) := by
        have hlower := fenchelDual_lower_bound_of_mem_dom (f := f) (s := s) hx
        exact (EReal.sub_le_iff_le_add
          (.inl (withTopToEReal_ne_bot_of_mem_dom (f := f) hx))
          (.inl (withTopToEReal_ne_top_of_mem_dom (f := f) hx))).1 hlower
      exact EReal.sub_le_of_le_add' hsum
    have hdense :
        ∀ w : EReal, w < withTopToEReal (f x) → ∃ z ∈ S, w < z := by
      intro w hw
      obtain ⟨r, hwr, hrx⟩ := EReal.exists_between_coe_real hw
      obtain ⟨s, hs, hslt⟩ :=
        exists_supportTerm_gt_of_mem_dom_lt (f := f) hf hdom hx hrx
      exact ⟨(inner ℝ s x : EReal) - (f⋆) s, ⟨s, hs, rfl⟩, hwr.trans hslt⟩
    have hS : sSup S = withTopToEReal (f x) := by
      refine sSup_eq_of_forall_le_of_forall_lt_exists_gt hupper ?_
      intro w hw
      exact hdense w hw
    -- Rewrite the bidual as the source-facing support supremum and identify its supremum value.
    rw [fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty (f := f) hdom x]
    simpa [S] using hS
  · have hfx_top : f x = ⊤ := top_unique (not_lt.mp hx)
    -- Route correction: the remaining branch should use a dedicated outside-domain support
    -- witness rather than extending the old exterior-point separator normalization.
    rw [fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty (f := f) hdom x]
    rw [hfx_top, withTopToEReal]
    change sSup ((fun s : EuclideanSpace ℝ (Fin n) ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) =
      (⊤ : EReal)
    refine (EReal.eq_top_iff_forall_lt _).2 ?_
    intro r
    rcases exists_supportTerm_gt_of_not_mem_dom hf hdom hx r with ⟨s, hs, hlt⟩
    exact (lt_sSup_iff).2 ⟨(inner ℝ s x : EReal) - (f⋆) s, ⟨s, hs, rfl⟩, hlt⟩

/-- Lemma 6 1: on `ℝⁿ`, a proper closed convex function equals the supremum
of the affine terms `⟪s, x⟫ - f_*(s)` over `dom f_*` at every `x`, which is the
canonical `EReal` surface of the textbook max formula. -/
theorem fenchelMoreau_eq_sSup_inner_sub_fenchelDual
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → WithTop ℝ} (hf : ClosedConvexFunction f)
    (hdom : (dom f).Nonempty) (x : EuclideanSpace ℝ (Fin n)) :
    withTopToEReal (f x) =
      sSup ((fun s : EuclideanSpace ℝ (Fin n) ↦ (inner ℝ s x : EReal) - (f⋆) s) '' dom (f⋆)) := by
  -- Rewrite the source-facing supremum formula through the owner-level bidual equality.
  rw [← fenchelBidual_eq_of_dom_nonempty hf hdom x]
  rw [fenchelBidual_apply_eq_sSup_image_dom_of_dom_nonempty (f := f) hdom x]

end ClosedConvexFunction

end

/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part11
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part2

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Lemma 31.0.2 (Convex Set Separation: Attainability of Supremum for Condition (a)): if
`f, g : ℝ^n → ℝ ∪ {+∞}` are proper convex functions, `ri (dom f) ∩ ri (dom g)` is nonempty, and
`α = inf_x (f x - g x)` is a finite real number, then there exists `x* ∈ ℝ^n` such that
`g* (x*) - f* (x*) ≥ α`. -/
lemma fenchel_duality_attainability_of_supremum_for_condition_a {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)))
    (α : ℝ)
    (hα : functionInfimumEReal (fun x => f x - g x) = (α : EReal)) :
    ∃ xStar : Fin n → ℝ, fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  -- First convert the infimum hypothesis into the pointwise primal lower bound used by the
  -- textbook separation setup.
  have hPointwise :
      ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x :=
    helperForLemma_31_0_2_pointwiseLowerBoundFromInfimum f g α hα
  -- The relative-interior qualification is exactly the local condition needed to support the
  -- slice-gap function at the origin.
  have hZeroDomDiffRi :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f -
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :=
    helperForLemma_31_0_2_zero_mem_relativeInterior_domainDifference
      (hf := hf) (hg := hg) hri
  -- Route correction: instead of forcing an affine sandwich directly, it is enough to support the
  -- zero-balance slice gap at the origin and read the dual vector from that supporting affine map.
  exact
    helperForLemma_31_0_2_dualWitnessFromRiQualification
      (n := n) (f := f) (g := g) α hf hg hPointwise hZeroDomDiffRi

-- Proof sketch: this helper restricts `f - g` to the common effective domain by assigning `⊤`
-- outside that set, so later statements can refer to that restricted primal objective when
-- needed.
/-- The primal difference restricted to the common effective domain of `f` and `g`, taking the
value `⊤` outside that region so the global infimum matches the intended infimum over points
where both functions are effectively finite. -/
noncomputable def commonEffectiveDomainDifference {n : ℕ} (f g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun x =>
    if x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) g then
      f x - g x
    else
      (⊤ : EReal)

-- Proof sketch: apply the polyhedral version of the convex separation argument under the
-- qualification hypothesis `ri (dom f) ∩ dom g ≠ ∅`, then identify the separating functional
-- with a dual point `xStar` giving `g* xStar - f* xStar ≥ α`. In this `EReal`
-- formalization, the primal quantity is represented by `commonEffectiveDomainDifference f g`,
-- which agrees with `f - g` on the common effective domain and is `+∞` elsewhere; the
-- additional hypothesis `∀ x, g x ≠ ⊥` enforces the book's codomain `ℝ ∪ {+∞}`.
/-- Helper for Lemma 31.0.3: the guarded primal infimum still yields the textbook pointwise lower
bound at every point of the common effective domain. -/
lemma helperForLemma_31_0_3_pointwiseLowerBoundOnCommonEffectiveDomain {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) (α : ℝ)
    (hα : functionInfimumEReal (commonEffectiveDomainDifference f g) = (α : EReal))
    {x : Fin n → ℝ}
    (hx :
      x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    (α : EReal) ≤ f x - g x := by
  -- Rewrite the guarded infimum as the relevant pointwise value at this common-domain point.
  rw [← hα]
  have hInfLe :
      functionInfimumEReal (commonEffectiveDomainDifference f g) ≤
        commonEffectiveDomainDifference f g x := by
    simpa [functionInfimumEReal] using
      iInf_le (commonEffectiveDomainDifference f g) x
  -- On the common effective domain the guard is inactive, so the objective is exactly `f x - g x`.
  simpa [commonEffectiveDomainDifference, hx] using hInfLe

/-- Helper for Lemma 31.0.3: the polyhedral hypothesis plus a common-domain witness upgrades `g`
to a proper convex function on `ℝ^n`. -/
lemma helperForLemma_31_0_3_polyhedralFunctionIsProperOnUniv_of_domainWitness {n : ℕ}
    (g : (Fin n → ℝ) → EReal)
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg_ne_bot : ∀ x, g x ≠ (⊥ : EReal))
    (hdom : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
  -- Keep the convex part from the polyhedral definition and read properness from the domain.
  refine ⟨hg_poly.1, ?_, ?_⟩
  · -- A nonempty effective domain is equivalent to a nonempty epigraph.
    exact (nonempty_epigraph_iff_nonempty_effectiveDomain
      (Set.univ : Set (Fin n → ℝ)) g).2 hdom
  · -- The extra side condition rules out `-∞` everywhere on `ℝ^n`.
    intro x _hx
    exact hg_ne_bot x

/-- Helper for Lemma 31.0.3: rewrite the textbook witness `ri (dom f) ∩ dom g ≠ ∅` into the
mixed Euclidean-space `dom g ∩ ri (dom f)` witness used by the Chapter 20 polyhedral
qualification lemmas. -/
lemma helperForLemma_31_0_3_nonempty_preimageDomG_inter_riPreimageDomF {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    Set.Nonempty
      ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
        ∩
        euclideanRelativeInterior n
          (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))) := by
  rcases hri with ⟨x0, hx0riF, hx0domG⟩
  let x0E : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x0
  have hpreimageDomF :
      (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) =
        ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm ''
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    ext x
    constructor
    · intro hx
      exact ⟨x.ofLp, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [Set.mem_preimage]
  -- Keep the mixed witness in the exact Euclidean-space format expected by Chapter 20.
  refine ⟨x0E, ?_⟩
  constructor
  · -- The domain membership is unchanged when we pass through the coordinate equivalence.
    simpa [x0E, Set.mem_preimage]
      using hx0domG
  · -- Convert the `Fin`-coordinate relative-interior fact into the Euclidean-space version.
    have hx0riF_E :
        x0E ∈
          euclideanRelativeInterior n
            ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm ''
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      simpa [x0E] using
        (mem_euclideanRelativeInterior_fin_iff
          (n := n)
          (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
          (x := x0)).1 hx0riF
    simpa [hpreimageDomF] using hx0riF_E

/-- Helper for Lemma 31.0.3: once `g` is known to be proper, the polyhedral hypothesis upgrades
it to a closed convex function. -/
lemma helperForLemma_31_0_3_closedConvexFunction_of_polyhedralProper {n : ℕ}
    {g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    ClosedConvexFunction g := by
  -- A proper polyhedral convex function agrees with its closure, so the standard closure lemma
  -- immediately yields the closed-convex package used later by the mixed Chapter 20 bridge.
  have hcl : convexFunctionClosure g = g :=
    helperForTheorem_20_0_4_convexFunctionClosure_eq_self_of_polyhedral_proper
      (n := n) (g := g) hg_poly hg_proper
  simpa [hcl] using
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := g) hg_proper).1.1

/-- Helper for Lemma 31.0.3: the mixed `dom g ∩ ri(dom f)` witness already forces the Euclidean
relative interior of `dom g` to be nonempty, because the polyhedral left block satisfies the
Chapter 20 transfer principle. -/
lemma helperForLemma_31_0_3_nonempty_riPreimageDomG_of_polyhedralQualification {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hMixedWitness :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)))) :
    Set.Nonempty
      (euclideanRelativeInterior n
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))) := by
  -- Apply the Chapter 20 mixed `dom/ri` transfer with the polyhedral summand on the left.
  exact
    (helperForTheorem_20_0_4_nonempty_ri_inter_of_polyhedral_left_and_nonempty_dom_inter_ri_right
      (p := g) (q := f) hg_poly hg hf hMixedWitness).1

/-- Helper for Lemma 31.0.3: the same Chapter 20 transfer keeps the Euclidean relative interior
of `dom f` nonempty on the right block, so the remaining blocker is only the final separator
construction on the encoded lower/upper branches. -/
lemma helperForLemma_31_0_3_nonempty_riPreimageDomF_of_polyhedralQualification {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hMixedWitness :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)))) :
    Set.Nonempty
      (euclideanRelativeInterior n
        (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))) := by
  -- The same transfer simultaneously recovers nonempty relative interior on the right block.
  exact
    (helperForTheorem_20_0_4_nonempty_ri_inter_of_polyhedral_left_and_nonempty_dom_inter_ri_right
      (p := g) (q := f) hg_poly hg hf hMixedWitness).2

/-- Helper for Lemma 31.0.3: convert a Euclidean-space relative-interior witness for a preimage
effective domain back into the native `Fin`-coordinate relative-interior witness used in the
Section 31 statements. -/
lemma helperForLemma_31_0_3_nonempty_riFin_of_nonempty_riPreimage {n : ℕ}
    {h : (Fin n → ℝ) → EReal}
    (hriPreimage :
      Set.Nonempty
        (euclideanRelativeInterior n
          (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) h)))) :
    Set.Nonempty
      (euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h)) := by
  rcases hriPreimage with ⟨xE, hxE⟩
  let x : Fin n → ℝ := xE
  have hpreimage :
      (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) h)) =
        ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm ''
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) := by
    ext y
    constructor
    · intro hy
      exact ⟨y.ofLp, hy, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [Set.mem_preimage]
  have hxImage :
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x ∈
        euclideanRelativeInterior n
          ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm ''
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) := by
    simpa [x, hpreimage] using hxE
  refine ⟨x, ?_⟩
  exact
    (mem_euclideanRelativeInterior_fin_iff
      (n := n)
      (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) h)
      (x := x)).2
      (by simpa [x] using hxImage)

/-- Helper for Lemma 31.0.3: the qualification hypothesis directly supplies a point of
`effectiveDomain g`, so `g` has a nonempty effective domain before any polyhedral upgrades are
used. -/
lemma helperForLemma_31_0_3_nonempty_effectiveDomainG_of_qualification {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
  -- Read the `dom g` component directly from the textbook witness `ri (dom f) ∩ dom g ≠ ∅`.
  rcases hri with ⟨x, _hxriF, hxdomG⟩
  exact ⟨x, hxdomG⟩

/-- Helper for Lemma 31.0.3: the mixed Chapter 20 witness already contains one point where both
`f` and `g` are effectively finite. -/
lemma helperForLemma_31_0_3_exists_commonEffectiveDomainPoint {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hMixedWitness :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)))) :
    ∃ x0 : Fin n → ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
  -- Read the common-domain anchor directly from the Chapter 20 mixed `dom/ri` witness.
  rcases
      helperForTheorem_20_0_4_exists_common_effectiveDomain_point_of_nonempty_dom_left_inter_ri_right
        (p := g) (q := f) hMixedWitness with
    ⟨x0, hx0G, hx0F⟩
  exact ⟨x0, hx0F, hx0G⟩

/-- Helper for Lemma 31.0.3: the textbook lower bound on the common effective domain upgrades to
the shifted inequality `α + g x ≤ f x` at every point of `dom g`. -/
lemma helperForLemma_31_0_3_shiftedPointwiseBoundOnDomainG {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwiseOnCommon :
      ∀ x : Fin n → ℝ,
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          (α : EReal) ≤ f x - g x) :
    ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
      (α : EReal) + g x ≤ f x := by
  intro x hxG
  by_cases hxF : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  · -- On the common effective domain, undo the subtraction in the textbook inequality.
    have hLower : (α : EReal) ≤ f x - g x :=
      hPointwiseOnCommon x ⟨hxF, hxG⟩
    have hgx_ne_top : g x ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hxG
    have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
    exact
      (EReal.le_sub_iff_add_le (Or.inl hgx_ne_bot) (Or.inl hgx_ne_top)).1 hLower
  · -- Outside `dom f`, the upper side is `+∞`, so the shifted inequality is automatic.
    have hfx_top : f x = (⊤ : EReal) := by
      by_contra hfx_ne_top
      apply hxF
      rw [effectiveDomain_eq]
      exact ⟨by simp, lt_top_iff_ne_top.mpr hfx_ne_top⟩
    simpa [hfx_top]

/-- Helper for Lemma 31.0.3: the corrected packed lower lifted epigraph records the shifted
epigraph inequality `α + g x ≤ μ` in the `λ = -1` slice. -/
noncomputable def helperForLemma_31_0_3_shiftedLowerLiftedEpigraph {n : ℕ}
    (α : ℝ) (g : (Fin n → ℝ) → EReal) :
    Set (Fin (n + 2) → ℝ) :=
  {z | ∃ x : Fin n → ℝ, ∃ μ : ℝ,
      (α : EReal) + g x ≤ (μ : EReal) ∧
        z =
          prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x, -μ), (-1 : ℝ))}

/-- Helper for Lemma 31.0.3: the packed upper lifted epigraph records the usual epigraph
inequality `f x ≤ μ` in the `λ = 1` slice. -/
noncomputable def helperForLemma_31_0_3_upperLiftedEpigraph {n : ℕ}
    (f : (Fin n → ℝ) → EReal) :
    Set (Fin (n + 2) → ℝ) :=
  {z | ∃ x : Fin n → ℝ, ∃ μ : ℝ,
      f x ≤ (μ : EReal) ∧
        z =
          prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (x, μ), (1 : ℝ))}

/-- Helper for Lemma 31.0.3: every exact lower generator coming from a finite point of `g`
already lies in the corrected shifted lower lifted epigraph. -/
lemma helperForLemma_31_0_3_mem_shiftedLowerLiftedEpigraph_of_mem_effectiveDomain {n : ℕ}
    {g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {x : Fin n → ℝ}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    prodLinearEquiv_append_coord (n := n + 1)
        (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ)) ∈
      helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g := by
  let μ : ℝ := α + (g x).toReal
  have hgx_ne_top : g x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hx
  have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
  have hgx_eq : g x = (((g x).toReal : ℝ) : EReal) := by
    simpa using (EReal.coe_toReal (x := g x) hgx_ne_top hgx_ne_bot).symm
  have hμ_eq : ((μ : ℝ) : EReal) = (α : EReal) + g x := by
    have hsum : (α : EReal) + g x = ((α + (g x).toReal : ℝ) : EReal) := by
      rw [hgx_eq]
      simp [EReal.coe_add, add_comm, add_left_comm, add_assoc]
    simpa [μ] using hsum.symm
  -- Use the exact finite `μ = α + g x` slice to place the lower generator in the corrected set.
  refine ⟨x, μ, ?_, rfl⟩
  simpa [hμ_eq] using (le_rfl : (α : EReal) + g x ≤ (α : EReal) + g x)

/-- Helper for Lemma 31.0.3: a single finite point of `g` makes the corrected shifted lower
lifted epigraph nonempty. -/
lemma helperForLemma_31_0_3_shiftedLowerLiftedEpigraph_nonempty {n : ℕ}
    {g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hdom : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    (helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g).Nonempty := by
  rcases hdom with ⟨x, hx⟩
  -- Reuse the exact lower generator at the chosen finite point.
  refine ⟨prodLinearEquiv_append_coord (n := n + 1)
      (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ)), ?_⟩
  exact
    helperForLemma_31_0_3_mem_shiftedLowerLiftedEpigraph_of_mem_effectiveDomain
      (n := n) (g := g) α hg hx

/-- Helper for Lemma 31.0.3: translating a polyhedral convex set preserves polyhedrality by
shifting each defining half-space constant by the corresponding dot product. -/
lemma helperForLemma_31_0_3_polyhedralTranslate {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC : IsPolyhedralConvexSet n C) (v : Fin n → ℝ) :
    IsPolyhedralConvexSet n ((fun x : Fin n → ℝ => v + x) '' C) := by
  rcases hC with ⟨ι, hι, b, β, rfl⟩
  -- Rewrite the translated set by moving each half-space threshold by `⟪v, b i⟫`.
  refine ⟨ι, hι, b, fun i => β i + v ⬝ᵥ b i, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_iInter, closedHalfSpaceLE, Set.mem_setOf_eq] at hx ⊢
    intro i
    have hxi := hx i
    simpa [add_dotProduct, add_assoc, add_comm, add_left_comm] using
      add_le_add_right hxi (v ⬝ᵥ b i)
  · intro hy
    refine ⟨y - v, ?_, by simp⟩
    simp only [Set.mem_iInter, closedHalfSpaceLE, Set.mem_setOf_eq] at hy ⊢
    intro i
    have hyi := hy i
    have hyi' : (y - v) ⬝ᵥ b i + v ⬝ᵥ b i ≤ β i + v ⬝ᵥ b i := by
      simpa [sub_dotProduct, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hyi
    have hdot : (y - v) ⬝ᵥ b i + v ⬝ᵥ b i = y ⬝ᵥ b i := by
      rw [sub_dotProduct]
      linarith
    linarith [hyi']

/-- Helper for Lemma 31.0.3: after translating the packed epigraph point of height `μ - α`,
the sign flip and final `λ = -1` embedding recover the exact shifted lower generator at
height `μ`. -/
lemma helperForLemma_31_0_3_translatedPackedEpigraphPoint_eq_shiftedLowerPoint {n : ℕ}
    (α μ : ℝ) (x : Fin n → ℝ) :
    let vLast : Fin (n + 2) → ℝ := prodLinearEquiv_append_coord (n := n + 1) (0, (-1 : ℝ))
    let vα : Fin (n + 1) → ℝ := prodLinearEquiv_append_coord (n := n) (0, α)
    let Aneg : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) := (-1 : ℝ) • LinearMap.id
    let Aembed : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) :=
      (prodLinearEquiv_append_coord (n := n + 1)).toLinearMap.comp
        (LinearMap.inl ℝ (Fin (n + 1) → ℝ) ℝ)
    vLast + Aembed (Aneg (vα + prodLinearEquiv_append_coord (n := n) (x, μ - α))) =
      prodLinearEquiv_append_coord (n := n + 1)
        (prodLinearEquiv_append_coord (n := n) (-x, -μ), (-1 : ℝ)) := by
  dsimp
  -- Unpack the outer `λ`-coordinate and then the inner `(x, μ)` coordinates.
  apply_fun (prodLinearEquiv_append_coord (n := n + 1)).symm using
    (prodLinearEquiv_append_coord (n := n + 1)).symm.injective
  ext x'
  · simpa [sub_eq_add_neg, add_comm] using
      congrArg (fun z : Fin (n + 1) → ℝ => z x')
        (by
          apply_fun (prodLinearEquiv_append_coord (n := n)).symm using
            (prodLinearEquiv_append_coord (n := n)).symm.injective
          simp [sub_eq_add_neg, add_comm] : -(prodLinearEquiv_append_coord (n := n) (x, μ - α)) -
              prodLinearEquiv_append_coord (n := n) (0, α) =
            prodLinearEquiv_append_coord (n := n) (-x, -μ))
  · simp

/-- Helper for Lemma 31.0.3: the same translated-sign-flipped epigraph construction reads an
ordinary epigraph height `ν` back as the shifted lower height `α + ν`. -/
lemma helperForLemma_31_0_3_translatedPackedEpigraphPoint_eq_shiftedLowerPoint_of_epigraphHeight
    {n : ℕ} (α ν : ℝ) (x : Fin n → ℝ) :
    let vLast : Fin (n + 2) → ℝ := prodLinearEquiv_append_coord (n := n + 1) (0, (-1 : ℝ))
    let vα : Fin (n + 1) → ℝ := prodLinearEquiv_append_coord (n := n) (0, α)
    let Aneg : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) := (-1 : ℝ) • LinearMap.id
    let Aembed : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) :=
      (prodLinearEquiv_append_coord (n := n + 1)).toLinearMap.comp
        (LinearMap.inl ℝ (Fin (n + 1) → ℝ) ℝ)
    vLast + Aembed (Aneg (vα + prodLinearEquiv_append_coord (n := n) (x, ν))) =
      prodLinearEquiv_append_coord (n := n + 1)
        (prodLinearEquiv_append_coord (n := n) (-x, -(α + ν)), (-1 : ℝ)) := by
  dsimp
  -- This is the same coordinate computation with `ν` standing for the original epigraph height.
  apply_fun (prodLinearEquiv_append_coord (n := n + 1)).symm using
    (prodLinearEquiv_append_coord (n := n + 1)).symm.injective
  ext x'
  · simpa using
      congrArg (fun z : Fin (n + 1) → ℝ => z x')
        (by
          apply_fun (prodLinearEquiv_append_coord (n := n)).symm using
            (prodLinearEquiv_append_coord (n := n)).symm.injective
          simp
          ring : -(prodLinearEquiv_append_coord (n := n) (0, α)) +
              -(prodLinearEquiv_append_coord (n := n) (x, ν)) =
            prodLinearEquiv_append_coord (n := n) (-x, -(α + ν)))
  · simp

/-- Helper for Lemma 31.0.3: the corrected shifted lower lifted epigraph is polyhedral because it
is obtained from the packed epigraph of `g` by a vertical translation, a linear sign flip, and a
final affine embedding into the `λ = -1` slice. -/
lemma helperForLemma_31_0_3_shiftedLowerLiftedEpigraph_polyhedral {n : ℕ}
    (α : ℝ) {g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g) :
    IsPolyhedralConvexSet (n + 2) (helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g) := by
  let M0 : Set (Fin (n + 1) → ℝ) :=
    ((fun p => prodLinearEquiv_append_coord (n := n) p) '' epigraph (Set.univ : Set (Fin n → ℝ)) g)
  have hM0poly : IsPolyhedralConvexSet (n + 1) M0 := by
    -- Start from the packed epigraph characterization already included in `hg_poly`.
    simpa [M0, prodLinearEquiv_append_coord] using hg_poly.2
  let vα : Fin (n + 1) → ℝ := prodLinearEquiv_append_coord (n := n) (0, α)
  have hMαpoly : IsPolyhedralConvexSet (n + 1) ((fun z => vα + z) '' M0) :=
    helperForLemma_31_0_3_polyhedralTranslate hM0poly vα
  let Aneg : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) := (-1 : ℝ) • LinearMap.id
  have hMnegPoly : IsPolyhedralConvexSet (n + 1) (Aneg '' ((fun z => vα + z) '' M0)) := by
    -- After the vertical shift, flip all coordinates to match the lower-slice sign convention.
    exact (polyhedralConvexSet_image_preimage_linear (n + 1) (n + 1) Aneg).1 _ hMαpoly
  let Aembed : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) :=
    (prodLinearEquiv_append_coord (n := n + 1)).toLinearMap.comp
      (LinearMap.inl ℝ (Fin (n + 1) → ℝ) ℝ)
  have hMembedPoly :
      IsPolyhedralConvexSet (n + 2) (Aembed '' (Aneg '' ((fun z => vα + z) '' M0))) := by
    -- Embed the signed `(x, μ)` data into the ambient `(x, μ, λ)` coordinate space.
    exact (polyhedralConvexSet_image_preimage_linear (n + 1) (n + 2) Aembed).1 _ hMnegPoly
  let vLast : Fin (n + 2) → ℝ :=
    prodLinearEquiv_append_coord (n := n + 1) (0, (-1 : ℝ))
  have hLowerPoly :
      IsPolyhedralConvexSet (n + 2)
        ((fun z : Fin (n + 2) → ℝ => vLast + z) ''
          (Aembed '' (Aneg '' ((fun z => vα + z) '' M0)))) :=
    helperForLemma_31_0_3_polyhedralTranslate hMembedPoly vLast
  have hEq :
      helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g =
        ((fun z : Fin (n + 2) → ℝ => vLast + z) ''
          (Aembed '' (Aneg '' ((fun z => vα + z) '' M0)))) := by
    ext z
    constructor
    · rintro ⟨x, μ, hμ, rfl⟩
      -- Convert the shifted inequality into an ordinary epigraph point of `g`.
      have hμ' : g x + (α : EReal) ≤ (μ : EReal) := by
        simpa [add_comm] using hμ
      have hEpig : g x ≤ ((μ - α : ℝ) : EReal) :=
        (EReal.le_sub_iff_add_le (Or.inl (by simp)) (Or.inl (by simp))).2 hμ'
      have hPackedEq :
          vLast + Aembed (Aneg (vα + prodLinearEquiv_append_coord (n := n) (x, μ - α))) =
            prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (-x, -μ), (-1 : ℝ)) :=
        helperForLemma_31_0_3_translatedPackedEpigraphPoint_eq_shiftedLowerPoint
          (n := n) α μ x
      refine ⟨Aembed (Aneg (vα + prodLinearEquiv_append_coord (n := n) (x, μ - α))), ?_, hPackedEq⟩
      refine ⟨Aneg (vα + prodLinearEquiv_append_coord (n := n) (x, μ - α)), ?_, rfl⟩
      refine ⟨vα + prodLinearEquiv_append_coord (n := n) (x, μ - α), ?_, rfl⟩
      refine ⟨prodLinearEquiv_append_coord (n := n) (x, μ - α), ?_, rfl⟩
      exact ⟨(x, μ - α), (mem_epigraph_univ_iff (f := g)).2 hEpig, rfl⟩
    · intro hz
      rcases hz with ⟨w, hw, rfl⟩
      rcases hw with ⟨u, hu, rfl⟩
      rcases hu with ⟨y, hy, rfl⟩
      rcases hy with ⟨q, hq, rfl⟩
      rcases hq with ⟨p, hp, rfl⟩
      rcases p with ⟨x, ν⟩
      have hν : g x ≤ (ν : EReal) := (mem_epigraph_univ_iff (f := g)).1 hp
      have hPackedEq :
          vLast + Aembed (Aneg (vα + prodLinearEquiv_append_coord (n := n) (x, ν))) =
            prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (-x, -(α + ν)), (-1 : ℝ)) :=
        helperForLemma_31_0_3_translatedPackedEpigraphPoint_eq_shiftedLowerPoint_of_epigraphHeight
          (n := n) α ν x
      refine ⟨x, α + ν, ?_, hPackedEq⟩
      -- Recover the shifted lower inequality by adding `α` back to the original epigraph height.
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using
        add_le_add_left hν (α : EReal)
  simpa [hEq] using hLowerPoly

/-- Helper for Lemma 31.0.3: every epigraph point of `f` gives a corresponding packed upper
generator in the `λ = 1` slice. -/
lemma helperForLemma_31_0_3_mem_upperLiftedEpigraph {n : ℕ}
    {f : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {μ : ℝ}
    (hμ : f x ≤ (μ : EReal)) :
    prodLinearEquiv_append_coord (n := n + 1)
        (prodLinearEquiv_append_coord (n := n) (x, μ), (1 : ℝ)) ∈
      helperForLemma_31_0_3_upperLiftedEpigraph f := by
  -- This is just the packed form of an ordinary epigraph witness.
  exact ⟨x, μ, hμ, rfl⟩

/-- Helper for Lemma 31.0.3: properness of `f` supplies one packed upper epigraph point. -/
lemma helperForLemma_31_0_3_upperLiftedEpigraph_nonempty {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    (helperForLemma_31_0_3_upperLiftedEpigraph f).Nonempty := by
  rcases properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf with ⟨x0, μ0, hx0μ0⟩
  -- Pack the finite epigraph witness produced by properness.
  refine ⟨prodLinearEquiv_append_coord (n := n + 1)
      (prodLinearEquiv_append_coord (n := n) (x0, μ0), (1 : ℝ)), ?_⟩
  exact
    helperForLemma_31_0_3_mem_upperLiftedEpigraph
      (f := f) (x := x0) (μ := μ0) (by simpa [hx0μ0])

/-- Helper for Lemma 31.0.3: the packed upper lifted epigraph inherits convexity from the
ordinary epigraph of `f`. -/
lemma helperForLemma_31_0_3_upperLiftedEpigraph_convex {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    Convex ℝ (helperForLemma_31_0_3_upperLiftedEpigraph f) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  rcases hz₁ with ⟨x₁, μ₁, hμ₁, rfl⟩
  rcases hz₂ with ⟨x₂, μ₂, hμ₂, rfl⟩
  have hEpiConv :
      Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa using convex_epigraph_of_convexFunctionOn (f := f) (hf := hf.1)
  have hComboEpi :
      a • ((x₁, μ₁) : (Fin n → ℝ) × ℝ) + b • ((x₂, μ₂) : (Fin n → ℝ) × ℝ) ∈
        epigraph (Set.univ : Set (Fin n → ℝ)) f :=
    hEpiConv
      ((mem_epigraph_univ_iff (f := f)).2 hμ₁)
      ((mem_epigraph_univ_iff (f := f)).2 hμ₂)
      ha hb hab
  have hComboμ : f (a • x₁ + b • x₂) ≤ ((a * μ₁ + b * μ₂ : ℝ) : EReal) :=
    (mem_epigraph_univ_iff (f := f)).1 (by simpa using hComboEpi)
  have hInnerPair :
      a • (x₁, μ₁) + b • (x₂, μ₂) = (a • x₁ + b • x₂, a * μ₁ + b * μ₂) := by
    ext <;> simp
  have hInnerPacked :
      a • prodLinearEquiv_append_coord (n := n) (x₁, μ₁) +
          b • prodLinearEquiv_append_coord (n := n) (x₂, μ₂) =
        prodLinearEquiv_append_coord (n := n) (a • x₁ + b • x₂, a * μ₁ + b * μ₂) := by
    calc
      a • prodLinearEquiv_append_coord (n := n) (x₁, μ₁) +
          b • prodLinearEquiv_append_coord (n := n) (x₂, μ₂)
          =
        prodLinearEquiv_append_coord (n := n) (a • (x₁, μ₁) + b • (x₂, μ₂)) := by
          rw [← LinearEquiv.map_smul, ← LinearEquiv.map_smul, ← LinearEquiv.map_add]
      _ =
        prodLinearEquiv_append_coord (n := n) (a • x₁ + b • x₂, a * μ₁ + b * μ₂) := by
          rw [hInnerPair]
  have hOuterPair :
      a • (prodLinearEquiv_append_coord (n := n) (x₁, μ₁), (1 : ℝ)) +
          b • (prodLinearEquiv_append_coord (n := n) (x₂, μ₂), (1 : ℝ)) =
        (a • prodLinearEquiv_append_coord (n := n) (x₁, μ₁) +
            b • prodLinearEquiv_append_coord (n := n) (x₂, μ₂),
          (1 : ℝ)) := by
    ext <;> simp [hab]
  -- The packing map is linear on the epigraph coordinates, and `a + b = 1` keeps us in `λ = 1`.
  refine ⟨a • x₁ + b • x₂, a * μ₁ + b * μ₂, hComboμ, ?_⟩
  calc
    a •
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (x₁, μ₁), (1 : ℝ)) +
      b •
        prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (x₂, μ₂), (1 : ℝ))
        =
      prodLinearEquiv_append_coord (n := n + 1)
        (a • (prodLinearEquiv_append_coord (n := n) (x₁, μ₁), (1 : ℝ)) +
          b • (prodLinearEquiv_append_coord (n := n) (x₂, μ₂), (1 : ℝ))) := by
            rw [← LinearEquiv.map_smul, ← LinearEquiv.map_smul, ← LinearEquiv.map_add]
    _ =
      prodLinearEquiv_append_coord (n := n + 1)
        (a • prodLinearEquiv_append_coord (n := n) (x₁, μ₁) +
            b • prodLinearEquiv_append_coord (n := n) (x₂, μ₂),
          (1 : ℝ)) := by
            rw [hOuterPair]
    _ =
      prodLinearEquiv_append_coord (n := n + 1)
        (prodLinearEquiv_append_coord (n := n) (a • x₁ + b • x₂, a * μ₁ + b * μ₂),
          (1 : ℝ)) := by
            rw [hInnerPacked]

/-- Helper for Lemma 31.0.3: the corrected lower packed set misses the intrinsic interior of the
upper packed set because the two families live in the disjoint slices `λ = -1` and `λ = 1`. -/
lemma helperForLemma_31_0_3_lowerInterIntrinsicInteriorUpper_empty_of_lambdaSlices {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ) :
    helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g ∩
        intrinsicInterior ℝ (helperForLemma_31_0_3_upperLiftedEpigraph f) =
      (∅ : Set (Fin (n + 2) → ℝ)) := by
  ext z
  constructor
  · rintro ⟨hzLower, hzUpper⟩
    rcases hzLower with ⟨x, μ, _hμ, rfl⟩
    -- Any intrinsic-interior point of the upper packed set is still an upper packed point.
    have hzUpperMem :
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x, -μ), (-1 : ℝ)) ∈
          helperForLemma_31_0_3_upperLiftedEpigraph f :=
      intrinsicInterior_subset (𝕜 := ℝ) (s := helperForLemma_31_0_3_upperLiftedEpigraph f) hzUpper
    rcases hzUpperMem with ⟨x', μ', _hμ', hEq⟩
    -- Unpacking the last coordinate forces the impossible identity `-1 = 1`.
    apply_fun (prodLinearEquiv_append_coord (n := n + 1)).symm at hEq
    have hLast : (-1 : ℝ) = (1 : ℝ) := by
      simpa using congrArg (fun p : (Fin (n + 1) → ℝ) × ℝ => p.2) hEq
    linarith
  · intro hz
    exact hz.elim

/-- Helper for Lemma 31.0.3: Theorem 20.2 applied to the packed lower and upper sets yields raw
separator data `(β, c, b, t)` before any zero-level normalization. -/
lemma helperForLemma_31_0_3_orientedPackedSeparatorDataFromTheorem20 {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hdomG : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∃ β c : ℝ, ∃ b : Fin n → ℝ, ∃ t : ℝ,
      (∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + t * μ + c ≤ β) ∧
      (∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c) ∧
      ¬ helperForLemma_31_0_3_upperLiftedEpigraph f ⊆
          {z : Fin (n + 2) → ℝ |
            z ⬝ᵥ
                prodLinearEquiv_append_coord (n := n + 1)
                  (prodLinearEquiv_append_coord (n := n) (b, t), c) =
              β} := by
  have hLowerPoly :
      IsPolyhedralConvexSet (n + 2) (helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g) :=
    helperForLemma_31_0_3_shiftedLowerLiftedEpigraph_polyhedral
      (n := n) (g := g) α hg_poly
  have hLowerNonempty :
      (helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g).Nonempty :=
    helperForLemma_31_0_3_shiftedLowerLiftedEpigraph_nonempty
      (n := n) (g := g) α hg hdomG
  have hUpperNonempty :
      (helperForLemma_31_0_3_upperLiftedEpigraph f).Nonempty :=
    helperForLemma_31_0_3_upperLiftedEpigraph_nonempty (n := n) (f := f) hf
  have hUpperConvex :
      Convex ℝ (helperForLemma_31_0_3_upperLiftedEpigraph f) :=
    helperForLemma_31_0_3_upperLiftedEpigraph_convex (n := n) (f := f) hf
  have hEmpty :
      helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g ∩
          intrinsicInterior ℝ (helperForLemma_31_0_3_upperLiftedEpigraph f) =
        (∅ : Set (Fin (n + 2) → ℝ)) :=
    helperForLemma_31_0_3_lowerInterIntrinsicInteriorUpper_empty_of_lambdaSlices
      (n := n) (f := f) (g := g) α
  rcases
      (exists_hyperplaneSeparatesProperly_and_not_subset_right_iff_inter_intrinsicInterior_eq_empty_of_nonempty_convex_polyhedral_left
        (n + 2)
        (helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g)
        (helperForLemma_31_0_3_upperLiftedEpigraph f)
        hLowerNonempty hUpperNonempty hUpperConvex hLowerPoly).2 hEmpty with
    ⟨H, hHproper, hUpperNotSubsetH⟩
  rcases hyperplaneSeparatesProperly_oriented (n + 2) H
      (helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g)
      (helperForLemma_31_0_3_upperLiftedEpigraph f) hHproper with
    ⟨w, β, _hw0, hHdef, hLowerGe, hUpperLe, _hnotBoth⟩
  let q : (Fin (n + 1) → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n + 1)).symm w
  let p : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm q.1
  have hdotPacked :
      ∀ (lam : ℝ) (x : Fin n → ℝ) (μ : ℝ),
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
            w =
          x ⬝ᵥ p.1 + μ * p.2 + lam * q.2 := by
    intro lam x μ
    calc
      dotProduct
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
          w
          =
        dotProduct
            (prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
            (prodLinearEquiv_append_coord (n := n + 1) q) := by
              simp [q]
      _ =
        dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ)) q.1 + lam * q.2 := by
          simpa [q] using
            helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
              (n := n + 1)
              (p := (prodLinearEquiv_append_coord (n := n) (x, μ), lam))
              (q := q)
      _ = x ⬝ᵥ p.1 + μ * p.2 + lam * q.2 := by
          have hInner :
              dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ)) q.1 =
                x ⬝ᵥ p.1 + μ * p.2 := by
            calc
              dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ)) q.1 =
                  dotProduct (prodLinearEquiv_append_coord (n := n) (x, μ))
                    (prodLinearEquiv_append_coord (n := n) p) := by
                      simp [p]
              _ = x ⬝ᵥ p.1 + μ * p.2 := by
                    simpa [p] using
                      helperForText_19_0_9_dotProduct_prodLinearEquivAppendCoord
                        (n := n) (p := (x, μ)) (q := p)
          rw [hInner]
  refine ⟨β, q.2, p.1, p.2, ?_, ?_, ?_⟩
  · intro x μ hμ
    -- Evaluating the upper packed generator gives the raw upper affine inequality.
    have hz :
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (x, μ), (1 : ℝ)) ∈
          helperForLemma_31_0_3_upperLiftedEpigraph f :=
      helperForLemma_31_0_3_mem_upperLiftedEpigraph (f := f) (x := x) (μ := μ) hμ
    have hzLe : dotProduct
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (x, μ), (1 : ℝ)))
          w ≤ β :=
      hUpperLe _ hz
    rw [hdotPacked (1 : ℝ) x μ, one_mul, mul_comm μ p.2] at hzLe
    nlinarith [hzLe]
  · intro x hxG
    -- Evaluating the exact lower packed generator gives the raw lower affine inequality.
    have hz :
        prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ)) ∈
          helperForLemma_31_0_3_shiftedLowerLiftedEpigraph α g :=
      helperForLemma_31_0_3_mem_shiftedLowerLiftedEpigraph_of_mem_effectiveDomain
        (n := n) (g := g) α hg hxG
    have hzGe : β ≤
        dotProduct
          (prodLinearEquiv_append_coord (n := n + 1)
            (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ)))
          w :=
      hLowerGe _ hz
    rw [hdotPacked (-1 : ℝ) (-x) (-(α + (g x).toReal))] at hzGe
    rw [neg_dotProduct, neg_one_mul, mul_comm (-(α + (g x).toReal)) p.2] at hzGe
    simpa [sub_eq_add_neg] using hzGe
  · intro hSubset
    apply hUpperNotSubsetH
    intro z hzUpper
    have hzEq :
        z ⬝ᵥ
            prodLinearEquiv_append_coord (n := n + 1)
              (prodLinearEquiv_append_coord (n := n) (p.1, p.2), q.2) =
          β :=
      hSubset hzUpper
    have hzH : z ∈ H := by
      simpa [hHdef, q, p] using hzEq
    exact hzH

/-- Helper for Lemma 31.0.3: once the raw packed separator has strictly negative `t` and
nonpositive level `β`, it yields a common affine minorant of both `α + g` on `dom g`
and `f`. -/
lemma helperForLemma_31_0_3_affineMinorantOfPackedSeparatorWithLevel {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {β c : ℝ} {b : Fin n → ℝ} {t : ℝ}
    (ht : t < 0) (hβ : β ≤ 0)
    (hUpper :
      ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + t * μ + c ≤ β)
    (hLower :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c) :
    ∃ h : AffineMap ℝ (Fin n → ℝ) ℝ,
      (∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g,
        (h x : EReal) ≤ (α : EReal) + g x) ∧
        (∀ x : Fin n → ℝ, (h x : EReal) ≤ f x) := by
  let hAff : AffineMap ℝ (Fin n → ℝ) ℝ :=
    (((-1 / t : ℝ) • dotProductLinear n b).toAffineMap) -
      AffineMap.const ℝ (Fin n → ℝ) ((β + c) / t)
  have hAff_repr :
      ∀ x : Fin n → ℝ, hAff x = (-β - c - x ⬝ᵥ b) / t := by
    intro x
    simp [hAff, dotProductLinear, div_eq_mul_inv, sub_eq_add_neg]
    ring
  refine ⟨hAff, ?_, ?_⟩
  · intro x hxG
    -- Route correction: the raw level-`β` lower inequality normalizes to an affine minorant of
    -- `α + g`, not to an affine majorant, so this is the precise corrected statement.
    have hgx_ne_top : g x ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hxG
    have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
    let gx : ℝ := (g x).toReal
    let s : ℝ := α + gx
    have hgx_eq : g x = (gx : EReal) := by
      simpa [gx] using (EReal.coe_toReal (x := g x) hgx_ne_top hgx_ne_bot).symm
    have hs_eq : (α : EReal) + g x = (s : EReal) := by
      simp [s, hgx_eq, EReal.coe_add]
    have hLowerSlice : β ≤ -x ⬝ᵥ b + t * (-s) - c := by
      simpa [s, gx] using hLower (x := x) hxG
    have hLowerSlice' : β ≤ -x ⬝ᵥ b - t * s - c := by
      simpa [mul_comm, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using hLowerSlice
    have hNumerator : t * s ≤ -β - c - x ⬝ᵥ b := by
      have hStep0 :
          x ⬝ᵥ b + c + β ≤ x ⬝ᵥ b + c + (-x ⬝ᵥ b - t * s - c) :=
        add_le_add_right hLowerSlice' (x ⬝ᵥ b + c)
      have hStep' : β + x ⬝ᵥ b + c ≤ -(t * s) := by
        calc
          β + x ⬝ᵥ b + c = x ⬝ᵥ b + c + β := by ring
          _ ≤ x ⬝ᵥ b + c + (-x ⬝ᵥ b - t * s - c) := hStep0
          _ = x ⬝ᵥ b + (-x ⬝ᵥ b) - t * s := by ring
          _ = 0 - t * s := by simp
          _ = -(t * s) := by ring
      have hNeg : t * s ≤ -(β + x ⬝ᵥ b + c) := by
        simpa [neg_mul, mul_comm] using neg_le_neg hStep'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hNeg
    have hReal : hAff x ≤ s := by
      rw [hAff_repr x]
      exact (div_le_iff_of_neg ht).2 (by simpa [mul_comm] using hNumerator)
    have hCoe : (hAff x : EReal) ≤ ((s : ℝ) : EReal) := by
      exact_mod_cast hReal
    calc
      (hAff x : EReal) ≤ (s : EReal) := hCoe
      _ = (α : EReal) + g x := hs_eq.symm
  · intro x
    -- The upper normalization compares the level-`β` numerator with the old zero-level one using
    -- the sign fact `β ≤ 0`.
    by_cases hfx_top : f x = (⊤ : EReal)
    · simpa [hfx_top]
    · have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      let μ : ℝ := (f x).toReal
      have hμ_eq : f x = (μ : EReal) := by
        simpa [μ] using (EReal.coe_toReal (x := f x) hfx_top hfx_ne_bot).symm
      have hUpperSlice : x ⬝ᵥ b + t * μ + c ≤ β := by
        exact hUpper (x := x) (μ := μ) (by simpa [hμ_eq])
      have hUpperSlice' : x ⬝ᵥ b + μ * t + c ≤ β := by
        simpa [mul_comm, add_assoc, add_left_comm, add_comm] using hUpperSlice
      have hUpperNumerator : μ * t ≤ β - c - x ⬝ᵥ b := by
        nlinarith [hUpperSlice']
      have hUpperReal : (β - c - x ⬝ᵥ b) / t ≤ μ := by
        exact (div_le_iff_of_neg ht).2 hUpperNumerator
      have hCompareReal : hAff x ≤ (β - c - x ⬝ᵥ b) / t := by
        rw [hAff_repr x]
        exact (div_le_div_right_of_neg ht).2 (by linarith)
      have hReal : hAff x ≤ μ := le_trans hCompareReal hUpperReal
      have hCoe : (hAff x : EReal) ≤ (μ : EReal) := by
        exact_mod_cast hReal
      calc
        (hAff x : EReal) ≤ (μ : EReal) := hCoe
        _ = f x := hμ_eq.symm

/-- Helper for Lemma 31.0.3: the raw packed separator has nonpositive vertical coefficient
`t`; the strict-negativity upgrade requires an additional argument for the `t = 0` branch. -/
lemma helperForLemma_31_0_3_separatorSlopeStrictNeg {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (_hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
    {β c : ℝ} {b : Fin n → ℝ} {t : ℝ}
    (hUpper :
      ∀ {x : Fin n → ℝ} {μ : ℝ}, f x ≤ (μ : EReal) →
        x ⬝ᵥ b + t * μ + c ≤ β)
    (_hLower :
      ∀ {x : Fin n → ℝ}, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        β ≤ -x ⬝ᵥ b + t * (-(α + (g x).toReal)) - c)
    (_hUpperNotSubset :
      ¬ helperForLemma_31_0_3_upperLiftedEpigraph f ⊆
          {z : Fin (n + 2) → ℝ |
            z ⬝ᵥ
                prodLinearEquiv_append_coord (n := n + 1)
                  (prodLinearEquiv_append_coord (n := n) (b, t), c) =
              β}) :
    t ≤ 0 := by
  -- First rule out a positive slope by pushing one finite upper epigraph point to arbitrarily
  -- large heights.
  have htle : t ≤ 0 := by
    rcases properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf with ⟨x0, μ0, hx0μ0⟩
    have hμ0 : f x0 ≤ (μ0 : EReal) := by
      simpa [hx0μ0]
    by_contra htPos
    have htPos : 0 < t := lt_of_not_ge htPos
    let A : ℝ := |β - (x0 ⬝ᵥ b + t * μ0 + c)|
    let R : ℝ := A / t + 1
    have hRnonneg : 0 ≤ R := by
      have hDivNonneg : 0 ≤ A / t := by
        exact div_nonneg (by
          dsimp [A]
          exact abs_nonneg _) (le_of_lt htPos)
      dsimp [R]
      nlinarith
    have hμ0R : f x0 ≤ ((μ0 + R) : EReal) := by
      have hμle : (μ0 : ℝ) ≤ μ0 + R := by
        linarith
      exact le_trans hμ0 (by exact_mod_cast hμle)
    have hUpperR : x0 ⬝ᵥ b + t * (μ0 + R) + c ≤ β :=
      hUpper (x := x0) (μ := μ0 + R) hμ0R
    have hRle : t * R ≤ β - (x0 ⬝ᵥ b + t * μ0 + c) := by
      nlinarith [hUpperR]
    have hAbsBound : β - (x0 ⬝ᵥ b + t * μ0 + c) ≤ A := by
      simpa [A] using le_abs_self (β - (x0 ⬝ᵥ b + t * μ0 + c))
    have hAbsLt : A < t * R := by
      have hAbsNonneg : 0 ≤ A := by
        dsimp [A]
        exact abs_nonneg _
      have hEq : t * R = A + t := by
        dsimp [R]
        field_simp [htPos.ne']
      rw [hEq]
      nlinarith
    exact (not_le_of_gt hAbsLt) (le_trans hRle hAbsBound)
  -- Route correction: the earlier plan tried to force `t < 0` from the raw packed separator
  -- alone, but the present hypotheses only support the large-height argument ruling out `t > 0`.
  -- The unresolved structural branch is the exact `t = 0` case, which needs a different decoder.
  exact htle

/-- Helper for Lemma 31.0.3: a real affine functional viewed as an `EReal`-valued map is
polyhedral convex. -/
lemma helperForLemma_31_0_3_coeAffineFunctional_polyhedral {m : ℕ}
    (a : Fin m → ℝ) (δ : ℝ) :
    IsPolyhedralConvexFunction m
      (fun z : Fin m → ℝ => ((z ⬝ᵥ a - δ : ℝ) : EReal)) := by
  -- Package the affine functional as a one-piece max-affine-plus-indicator representation.
  refine
    ((polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := m)
      (f := fun z : Fin m → ℝ => ((z ⬝ᵥ a - δ : ℝ) : EReal))).2 ?_).1
  refine ⟨1, 1, fun _ => a, fun _ => δ, le_rfl, ?_⟩
  funext z
  simp [dotProduct, indicatorFunction]

/-- Helper for Lemma 31.0.3: the same affine functional is proper convex on all of `ℝ^m`. -/
lemma helperForLemma_31_0_3_coeAffineFunctional_proper {m : ℕ}
    (a : Fin m → ℝ) (δ : ℝ) :
    ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ))
      (fun z : Fin m → ℝ => ((z ⬝ᵥ a - δ : ℝ) : EReal)) := by
  have hAffine :
      AffineFunctionOn (Set.univ : Set (Fin m → ℝ))
        (fun z : Fin m → ℝ => ((z ⬝ᵥ a - δ : ℝ) : EReal)) := by
    simpa [dotProduct, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (affineFunctionOn_univ_inner_add_const (n := m) (a := a) (α := -δ))
  refine ⟨hAffine.2.1, ?_, ?_⟩
  · -- The graph point `(0, -δ)` lies on the epigraph with equality.
    refine ⟨((0 : Fin m → ℝ), -δ), ?_⟩
    exact
      (mem_epigraph_univ_iff
        (f := fun z : Fin m → ℝ => ((z ⬝ᵥ a - δ : ℝ) : EReal))).2
        (by simp [dotProduct])
  · -- Affine real-valued maps never take the value `-∞`.
    intro z hz
    exact (hAffine.1 z hz).1


end Section31
end Chap06

/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part4

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Lemma 31.0.3: after restricting `f` to `dom g` and tilting by `-z`, the shifted
pointwise bound `α + g ≤ f` yields a dual upper bound at the origin. -/
lemma helperForLemma_31_0_3_restrictedTiltedDualUpperBoundAtZero {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hShiftedOnDomainG :
      ∀ x : Fin n → ℝ, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        (α : EReal) + g x ≤ f x)
    (z : Fin n → ℝ) :
    fenchelConjugate n
        (fun x =>
          (f x + indicatorFunction (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) +
            (((x ⬝ᵥ (-z) : ℝ)) : EReal)) 0
      ≤ fenchelConjugate n g z - (α : EReal) := by
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  let gTilt : (Fin n → ℝ) → EReal :=
    fun x => (g x + (α : EReal)) + (((x ⬝ᵥ (-z) : ℝ)) : EReal)
  let fRestrTilt : (Fin n → ℝ) → EReal :=
    fun x => (f x + indicatorFunction domG x) + (((x ⬝ᵥ (-z) : ℝ)) : EReal)
  have hOrder : gTilt ≤ fRestrTilt := by
    intro x
    by_cases hxG : x ∈ domG
    · -- On `dom g`, the indicator vanishes, so the pointwise primal inequality survives the tilt.
      have hShifted := hShiftedOnDomainG x hxG
      simpa [gTilt, fRestrTilt, domG, indicatorFunction, hxG, add_assoc, add_left_comm,
        add_comm] using
        (add_le_add
          (le_rfl : (((x ⬝ᵥ (-z) : ℝ)) : EReal) ≤ (((x ⬝ᵥ (-z) : ℝ)) : EReal))
          hShifted)
    · -- Outside `dom g`, both tilted functions are `⊤`, so the order is trivial.
      have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
      have hgx_top : g x = (⊤ : EReal) := by
        by_contra hgx_ne_top
        apply hxG
        change x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
        rw [effectiveDomain_eq]
        exact ⟨by simp, (lt_top_iff_ne_top).2 hgx_ne_top⟩
      have hgTilt_top : gTilt x = (⊤ : EReal) := by
        have hga_top : g x + (α : EReal) = (⊤ : EReal) := by
          simpa [hgx_top] using
            (EReal.top_add_of_ne_bot (x := (α : EReal)) (EReal.coe_ne_bot α))
        simpa [gTilt, hga_top] using
          (EReal.top_add_of_ne_bot (x := (((x ⬝ᵥ (-z) : ℝ)) : EReal))
            (EReal.coe_ne_bot _))
      have hRestr_top : fRestrTilt x = (⊤ : EReal) := by
        have hind_top : f x + indicatorFunction domG x = (⊤ : EReal) := by
          simpa [domG, indicatorFunction, hxG] using
            (EReal.add_top_of_ne_bot (x := f x) hfx_ne_bot)
        simpa [fRestrTilt, hind_top] using
          (EReal.top_add_of_ne_bot (x := (((x ⬝ᵥ (-z) : ℝ)) : EReal))
            (EReal.coe_ne_bot _))
      simpa [hgTilt_top, hRestr_top] using (le_rfl : (⊤ : EReal) ≤ (⊤ : EReal))
  -- Antitonicity of Fenchel conjugation turns the tilted primal order into the desired dual bound.
  calc
    fenchelConjugate n fRestrTilt 0 ≤ fenchelConjugate n gTilt 0 :=
      (fenchelConjugate_antitone n) hOrder 0
    _ = fenchelConjugate n (fun x => g x + (α : EReal)) z := by
      simpa [gTilt, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        congrArg (fun h : (Fin n → ℝ) → EReal => h 0)
          (section16_fenchelConjugate_add_linear
            (h := fun x => g x + (α : EReal)) (-z))
    _ = fenchelConjugate n g z - (α : EReal) := by
      simpa using
        congrArg (fun h : (Fin n → ℝ) → EReal => h z)
          (section16_fenchelConjugate_add_const g α)

/-- Helper for Lemma 31.0.3: the effective domain of a polyhedral convex function is itself
polyhedral, so its indicator gives the left polyhedral block required by the Chapter 20 binary
exactness theorem. -/
lemma helperForLemma_31_0_3_indicatorEffectiveDomainOfPolyhedralG_isProperPolyhedral {n : ℕ}
    {g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    IsPolyhedralConvexFunction n
        (indicatorFunction (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (indicatorFunction (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) := by
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  have hg_nonbot : ∀ x : Fin n → ℝ, g x ≠ (⊥ : EReal) := by
    intro x
    exact hg.2.2 x (by simp)
  have hdomPoly : IsPolyhedralConvexSet n domG := by
    rcases
        (polyhedral_convex_function_iff_max_affine_plus_indicator n g).1
          ⟨hg_poly, hg_nonbot⟩ with
      ⟨k, m, b, β, _hk_le_m, hrepr⟩
    let C : Set (Fin n → ℝ) :=
      {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
    have hdomEq : domG = C := by
      ext x
      constructor
      · intro hx
        by_contra hxC
        have hgx_top : g x = (⊤ : EReal) := by
          have hind_top : indicatorFunction C x = (⊤ : EReal) := by
            simp [indicatorFunction, hxC]
          have hsup_ne_bot :
              ((sSup {r : ℝ |
                  ∃ i : Fin m, (i : ℕ) < k ∧
                    r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) ≠ (⊥ : EReal) :=
            EReal.coe_ne_bot _
          have hreprx := congrArg (fun h : (Fin n → ℝ) → EReal => h x) hrepr
          calc
            g x =
                ((sSup {r : ℝ |
                    ∃ i : Fin m, (i : ℕ) < k ∧
                      r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
                  indicatorFunction C x := hreprx
            _ = (⊤ : EReal) := by
                  simpa [hind_top] using
                    (EReal.add_top_of_ne_bot (x := ((sSup {r : ℝ |
                      ∃ i : Fin m, (i : ℕ) < k ∧
                        r = (∑ j, x j * b i j) - β i} : ℝ) : EReal))
                      hsup_ne_bot)
        exact
          (mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hx) hgx_top
      · intro hxC
        change x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
        rw [effectiveDomain_eq]
        constructor
        · simp
        · have hreprx := congrArg (fun h : (Fin n → ℝ) → EReal => h x) hrepr
          have hgx_eq :
              g x =
                ((sSup {r : ℝ |
                    ∃ i : Fin m, (i : ℕ) < k ∧
                      r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) := by
            simpa [C, indicatorFunction, hxC] using hreprx
          exact (lt_top_iff_ne_top).2 (by
            rw [hgx_eq]
            exact EReal.coe_ne_top _)
    have hCpoly : IsPolyhedralConvexSet n C := by
      refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces n C).2 ?_
      let b' : Fin m → Fin n → ℝ := fun i => if k ≤ (i : ℕ) then b i else 0
      let β' : Fin m → ℝ := fun i => if k ≤ (i : ℕ) then β i else 0
      refine ⟨m, b', β', ?_⟩
      ext y
      constructor
      · intro hy
        refine Set.mem_iInter.mpr ?_
        intro i
        by_cases hki : k ≤ (i : ℕ)
        · have hyi : (∑ j, y j * b i j) ≤ β i := hy i hki
          simpa [C, closedHalfSpaceLE, b', β', hki, dotProduct] using hyi
        · simp [C, closedHalfSpaceLE, b', β', hki, dotProduct]
      · intro hy i hki
        have hmem : y ∈ closedHalfSpaceLE n (b' i) (β' i) :=
          Set.mem_iInter.mp hy i
        simpa [C, closedHalfSpaceLE, b', β', hki, dotProduct] using hmem
    simpa [domG, hdomEq] using hCpoly
  have hdomConv : Convex ℝ domG :=
    helperForTheorem_19_1_polyhedral_isConvex n domG hdomPoly
  have hdomNe : Set.Nonempty domG :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain
      (Set.univ : Set (Fin n → ℝ)) g).1 hg.2.1
  constructor
  · -- The polyhedrality of the domain turns directly into a polyhedral indicator.
    simpa [domG] using
      helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet hdomPoly
  · -- The indicator is proper because `dom g` is convex and nonempty.
    simpa [domG] using
      section16_properConvexFunctionOn_indicatorFunction_univ hdomConv hdomNe

/-- Helper for Lemma 31.0.3: rewriting the tilted zero-dual estimate back to the ordinary
conjugate of `f + indicatorFunction (dom g)` gives the uniform restricted dual upper bound used
in the corrected Chapter 20 bridge. -/
lemma helperForLemma_31_0_3_restrictedConjugateUpperBound {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hShiftedOnDomainG :
      ∀ x : Fin n → ℝ,
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          (α : EReal) + g x ≤ f x) :
    ∀ z : Fin n → ℝ,
      fenchelConjugate n
          (fun x =>
            f x + indicatorFunction
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
        ≤ fenchelConjugate n g z - (α : EReal) := by
  intro z
  -- Move the dual point `z` to the origin so the existing tilted zero-dual estimate applies.
  calc
    fenchelConjugate n
        (fun x =>
          f x + indicatorFunction
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
      =
        fenchelConjugate n
          (fun x =>
            (f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) +
              (((x ⬝ᵥ (-z) : ℝ)) : EReal)) 0 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            (congrArg (fun h : (Fin n → ℝ) → EReal => h 0)
              (section16_fenchelConjugate_add_linear
                (h := fun x =>
                  f x + indicatorFunction
                    (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x)
                (-z))).symm
    _ ≤ fenchelConjugate n g z - (α : EReal) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        helperForLemma_31_0_3_restrictedTiltedDualUpperBoundAtZero
          (n := n) (f := f) (g := g) α hf hShiftedOnDomainG z

/-- Helper for Lemma 31.0.3: applying the mixed Chapter 20 exactness theorem to the pair
`(indicatorFunction (dom g), f)` yields a finite attained split for the restricted conjugate of
`f + indicatorFunction (dom g)`. -/
lemma helperForLemma_31_0_3_restrictedFiniteDualAttainedSplit {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∃ z y : Fin n → ℝ,
      fenchelConjugate n
          (fun x =>
            f x + indicatorFunction
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z ≠ (⊤ : EReal) ∧
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          =
            fenchelConjugate n
                (indicatorFunction
                  (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) (z - y) +
              fenchelConjugate n f y := by
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  have hIndicator :=
    helperForLemma_31_0_3_indicatorEffectiveDomainOfPolyhedralG_isProperPolyhedral
      (n := n) (g := g) hg_poly hg
  have hMixedWitnessBase :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' domG))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))) :=
    helperForLemma_31_0_3_nonempty_preimageDomG_inter_riPreimageDomF
      (n := n) (f := f) (g := g) hri
  have hMixedWitness :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (indicatorFunction domG)))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))) := by
    simpa [domG, effectiveDomain_indicatorFunction_eq] using hMixedWitnessBase
  have hRestrProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => indicatorFunction domG x + f x) :=
    helperForTheorem_20_1_binary_sum_proper_of_nonempty_dom_inter_ri
      (p := indicatorFunction domG) (q := f) hIndicator.2 hf hMixedWitness
  have hRestrStarProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fenchelConjugate n (fun x => indicatorFunction domG x + f x)) :=
    proper_fenchelConjugate_of_proper
      (n := n) (f := fun x => indicatorFunction domG x + f x) hRestrProper
  obtain ⟨z, r, hzFinite⟩ :=
    properConvexFunctionOn_exists_finite_point
      (n := n)
      (f := fenchelConjugate n (fun x => indicatorFunction domG x + f x))
      hRestrStarProper
  have hz_ne_top :
      fenchelConjugate n (fun x => indicatorFunction domG x + f x) z ≠ (⊤ : EReal) := by
    simpa [hzFinite] using EReal.coe_ne_top r
  let hBridge :=
    _root_.helperForTheorem_20_1_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_without_riInter
      (p := indicatorFunction domG) (q := f) hIndicator.1 hIndicator.2 hf hMixedWitness
  have hEqAt :
      fenchelConjugate n (fun x => indicatorFunction domG x + f x) z =
        infimalConvolution
          (fenchelConjugate n (indicatorFunction domG))
          (fenchelConjugate n f) z := by
    simpa using congrArg (fun h : (Fin n → ℝ) → EReal => h z) hBridge.1
  rcases hBridge.2 z with hTop | ⟨y, hy⟩
  · exact False.elim (hz_ne_top (hEqAt.trans hTop))
  · refine ⟨z, y, ?_, ?_⟩
    · simpa [add_comm] using hz_ne_top
    · simpa [add_comm] using hEqAt.trans hy

/-- Helper for Lemma 31.0.3: the same Chapter 20 binary exactness theorem applied to
`(indicatorFunction (dom g), g)` bounds `g⋆ z` by every candidate decomposition with the common
support-function term at `z - y`. -/
lemma helperForLemma_31_0_3_supportFunctionCandidateBoundForG {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∀ z y : Fin n → ℝ,
      fenchelConjugate n g z
        ≤ fenchelConjugate n
            (indicatorFunction
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) (z - y) +
          fenchelConjugate n g y := by
  intro z y
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  have hIndicator :=
    helperForLemma_31_0_3_indicatorEffectiveDomainOfPolyhedralG_isProperPolyhedral
      (n := n) (g := g) hg_poly hg
  have hMixedWitnessBase :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' domG))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' domG))) := by
    rcases
      helperForLemma_31_0_3_nonempty_riPreimageDomG_of_polyhedralQualification
        (n := n) (f := f) (g := g) hg_poly hg hf
        (helperForLemma_31_0_3_nonempty_preimageDomG_inter_riPreimageDomF
          (n := n) (f := f) (g := g) hri) with
      ⟨xE, hxE⟩
    have hxDomG :
        xE ∈ (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' domG)) := by
      exact
        intrinsicInterior_subset (𝕜 := ℝ)
          (s := (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' domG)))
          (by
            simpa [intrinsicInterior_eq_euclideanRelativeInterior
              (n := n)
              (C := (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' domG)))]
              using hxE)
    exact ⟨xE, hxDomG, hxE⟩
  have hMixedWitness :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) (indicatorFunction domG)))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))) := by
    simpa [domG, effectiveDomain_indicatorFunction_eq] using hMixedWitnessBase
  let hBridge :=
    _root_.helperForTheorem_20_1_mixed_two_block_exact_topOrAttained_of_polyLeft_domRi_without_riInter
      (p := indicatorFunction domG) (q := g) hIndicator.1 hIndicator.2 hg hMixedWitness
  have hIndicatorAdd_eq_g :
      (fun x => indicatorFunction domG x + g x) = g := by
    funext x
    by_cases hx : x ∈ domG
    · simp [domG, indicatorFunction, hx]
    · have hgx_top : g x = (⊤ : EReal) := by
        by_contra hgx_ne_top
        exact hx (by
          change x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
          rw [effectiveDomain_eq]
          exact ⟨by simp, (lt_top_iff_ne_top).2 hgx_ne_top⟩)
      have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
      simp [domG, indicatorFunction, hx, hgx_top, hgx_ne_bot]
  have hEqAt :
      fenchelConjugate n g z =
        infimalConvolution
          (fenchelConjugate n (indicatorFunction domG))
          (fenchelConjugate n g) z := by
    calc
      fenchelConjugate n g z =
          fenchelConjugate n (fun x => indicatorFunction domG x + g x) z := by
            rw [hIndicatorAdd_eq_g]
      _ =
          infimalConvolution
            (fenchelConjugate n (indicatorFunction domG))
            (fenchelConjugate n g) z := by
            simpa using congrArg (fun h : (Fin n → ℝ) → EReal => h z) hBridge.1
  have hCandidate :
      infimalConvolution
          (fenchelConjugate n (indicatorFunction domG))
          (fenchelConjugate n g) z
        ≤ fenchelConjugate n (indicatorFunction domG) (z - y) +
            fenchelConjugate n g y := by
    -- The split `z = (z - y) + y` is one admissible candidate in the defining infimum.
    rw [infimalConvolution]
    have hMem :
        fenchelConjugate n (indicatorFunction domG) (z - y) + fenchelConjugate n g y ∈
          {w : EReal |
            ∃ x1 x2 : Fin n → ℝ,
              x1 + x2 = z ∧
                w =
                  fenchelConjugate n (indicatorFunction domG) x1 +
                    fenchelConjugate n g x2} := by
      exact ⟨z - y, y, by simp, rfl⟩
    exact sInf_le hMem
  exact hEqAt.trans_le hCandidate

/-- Helper for Lemma 31.0.3: the restricted finite split and the matching candidate estimate for
`g⋆` share the same support-function term, so after ruling out the infinite branches that common
term can be cancelled to produce the desired dual gap witness. -/
lemma helperForLemma_31_0_3_dualGapWitnessFromRestrictedFiniteSplit {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
    (hShiftedOnDomainG :
      ∀ x : Fin n → ℝ,
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          (α : EReal) + g x ≤ f x) :
    ∃ y : Fin n → ℝ,
      fenchelConjugate n g y - fenchelConjugate n f y ≥ (α : EReal) := by
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  obtain ⟨z, y, hz_ne_top, hSplit⟩ :=
    helperForLemma_31_0_3_restrictedFiniteDualAttainedSplit
      (n := n) (f := f) (g := g) hg_poly hg hf hri
  have hUpper :=
    helperForLemma_31_0_3_restrictedConjugateUpperBound
      (n := n) (f := f) (g := g) α hf hShiftedOnDomainG z
  have hCandidate :=
    helperForLemma_31_0_3_supportFunctionCandidateBoundForG
      (n := n) (f := f) (g := g) hg_poly hg hf hri z y
  have hDomGne : Set.Nonempty domG :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain
      (Set.univ : Set (Fin n → ℝ)) g).1 hg.2.1
  have hFstarProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hGstarProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g) :=
    proper_fenchelConjugate_of_proper (n := n) (f := g) hg
  have hFy_ne_bot : fenchelConjugate n f y ≠ (⊥ : EReal) := hFstarProper.2.2 y (by simp)
  have hGy_ne_bot : fenchelConjugate n g y ≠ (⊥ : EReal) := hGstarProper.2.2 y (by simp)
  rw [section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := domG)] at hSplit hCandidate
  have hSupport_ne_bot : supportFunctionEReal domG (z - y) ≠ (⊥ : EReal) :=
    section13_supportFunctionEReal_ne_bot_of_nonempty hDomGne (z - y)
  have hSupport_ne_top : supportFunctionEReal domG (z - y) ≠ (⊤ : EReal) := by
    intro hSupport_top
    have hTopValue :
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          = (⊤ : EReal) := by
      calc
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          = supportFunctionEReal domG (z - y) + fenchelConjugate n f y := hSplit
        _ = (⊤ : EReal) := by
          simpa [hSupport_top] using EReal.top_add_of_ne_bot hFy_ne_bot
    exact hz_ne_top hTopValue
  have hFy_ne_top : fenchelConjugate n f y ≠ (⊤ : EReal) := by
    intro hFy_top
    have hTopValue :
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          = (⊤ : EReal) := by
      calc
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          = supportFunctionEReal domG (z - y) + fenchelConjugate n f y := hSplit
        _ = (⊤ : EReal) := by
          simpa [hFy_top] using EReal.add_top_of_ne_bot hSupport_ne_bot
    exact hz_ne_top hTopValue
  by_cases hGy_ne_top : fenchelConjugate n g y ≠ (⊤ : EReal)
  · have hCombined :
        supportFunctionEReal domG (z - y) + fenchelConjugate n f y
          ≤ (supportFunctionEReal domG (z - y) + fenchelConjugate n g y) - (α : EReal) := by
      calc
        supportFunctionEReal domG (z - y) + fenchelConjugate n f y
            =
              fenchelConjugate n
                (fun x =>
                  f x + indicatorFunction
                    (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z := hSplit.symm
        _ ≤ fenchelConjugate n g z - (α : EReal) := hUpper
        _ ≤ (supportFunctionEReal domG (z - y) + fenchelConjugate n g y) - (α : EReal) := by
            exact EReal.sub_le_sub hCandidate le_rfl
    have hAdd :
        (supportFunctionEReal domG (z - y) + fenchelConjugate n f y) + (α : EReal)
          ≤ supportFunctionEReal domG (z - y) + fenchelConjugate n g y := by
      exact
        (EReal.le_sub_iff_add_le
          (Or.inl (EReal.coe_ne_bot α))
          (Or.inl (EReal.coe_ne_top α))).1 hCombined
    have hSupport_coe :
        (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal) =
          supportFunctionEReal domG (z - y) :=
      EReal.coe_toReal hSupport_ne_top hSupport_ne_bot
    have hCancelSupport :
        fenchelConjugate n f y + (α : EReal) ≤ fenchelConjugate n g y := by
      have hTransport :=
        (section13_addRightOrderIso (supportFunctionEReal domG (z - y)).toReal).symm.monotone
          (by
            simpa [add_assoc, add_left_comm, add_comm] using hAdd)
      have hTransport' :
          fenchelConjugate n f y + (↑α + supportFunctionEReal domG (z - y)) -
              supportFunctionEReal domG (z - y)
            ≤
              fenchelConjugate n g y + supportFunctionEReal domG (z - y) -
                supportFunctionEReal domG (z - y) := by
        simpa [section13_addRightOrderIso, hSupport_coe] using hTransport
      have hLeftRewrite :
          fenchelConjugate n f y + (↑α + supportFunctionEReal domG (z - y)) -
              supportFunctionEReal domG (z - y) =
            fenchelConjugate n f y + (α : EReal) := by
        rw [← hSupport_coe]
        calc
          fenchelConjugate n f y + (↑α + (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal)) -
              (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal)
            =
              (fenchelConjugate n f y + (α : EReal)) +
                  (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal) -
                (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal) := by
                  simp [add_assoc, add_left_comm, add_comm]
          _ = fenchelConjugate n f y + (α : EReal) := by
                rw [EReal.add_sub_cancel_right]
      have hRightRewrite :
          fenchelConjugate n g y + supportFunctionEReal domG (z - y) -
              supportFunctionEReal domG (z - y) =
            fenchelConjugate n g y := by
        rw [← hSupport_coe, EReal.add_sub_cancel_right]
      exact hLeftRewrite ▸ hRightRewrite ▸ hTransport'
    have hGap :
        (α : EReal) ≤ fenchelConjugate n g y - fenchelConjugate n f y := by
      exact
        (EReal.le_sub_iff_add_le
          (Or.inr hGy_ne_bot)
          (Or.inr hGy_ne_top)).2
          (by simpa [add_assoc, add_left_comm, add_comm] using hCancelSupport)
    exact ⟨y, hGap⟩
  · have hGy_top : fenchelConjugate n g y = (⊤ : EReal) := by
      by_contra hGy_ne_top'
      exact hGy_ne_top hGy_ne_top'
    have hFy_coe :
        (((fenchelConjugate n f y).toReal : ℝ) : EReal) = fenchelConjugate n f y :=
      EReal.coe_toReal hFy_ne_top hFy_ne_bot
    refine ⟨y, ?_⟩
    calc
      (α : EReal) ≤ (⊤ : EReal) := by simp
      _ = fenchelConjugate n g y - fenchelConjugate n f y := by
        rw [hGy_top, ← hFy_coe]
        simpa using EReal.top_sub_coe ((fenchelConjugate n f y).toReal)

lemma helperForLemma_31_0_3_directDualWitnessFromMixedPolyhedralFenchelBridge {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
    (hPointwiseOnCommon :
      ∀ x : Fin n → ℝ,
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          (α : EReal) ≤ f x - g x) :
    ∃ xStar : Fin n → ℝ,
      fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  -- Route correction: the old decoder `t < 0 ∨ t = 0` is not faithful here, because the packed
  -- Theorem 20.2 separator may live entirely in the `lambda` direction with `t = 0`.
  have hMixedWitness :
      Set.Nonempty
        ((((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
          ∩
          euclideanRelativeInterior n
            (((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))) :=
    helperForLemma_31_0_3_nonempty_preimageDomG_inter_riPreimageDomF
      (n := n) (f := f) (g := g) hri
  have hShiftedOnDomainG :
      ∀ x : Fin n → ℝ, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        (α : EReal) + g x ≤ f x := by
    intro x hxG
    -- Promote the common-domain lower bound to the domain-of-`g` form needed by the Chapter 20
    -- infimal-convolution bridge.
    exact
      helperForLemma_31_0_3_shiftedPointwiseBoundOnDomainG
        (n := n) (f := f) (g := g) α hg hPointwiseOnCommon hxG
  let _ := hMixedWitness
  -- Route correction: the valid bridge works with the restricted function
  -- `f + indicatorFunction (dom g)`, whose attained split shares the same support term as the
  -- Chapter 20 candidate bound for `g⋆`.
  exact
    helperForLemma_31_0_3_dualGapWitnessFromRestrictedFiniteSplit
      (n := n) (f := f) (g := g) α hf hg_poly hg hri hShiftedOnDomainG

/-- Helper for Lemma 31.0.3: the mixed polyhedral qualification now passes through the valid
Chapter 20 attained infimal-convolution bridge, avoiding the invalid raw-separator `t = 0`
contradiction route. -/
lemma helperForLemma_31_0_3_dualWitnessFromPolyhedralQualification {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
    (hPointwiseOnCommon :
      ∀ x : Fin n → ℝ,
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          (α : EReal) ≤ f x - g x) :
    ∃ xStar : Fin n → ℝ,
      fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  -- Route correction: stop decoding the raw Theorem 20.2 separator here. The valid remaining
  -- route is the attained mixed-polyhedral Fenchel bridge from Chapter 20.
  exact
    helperForLemma_31_0_3_directDualWitnessFromMixedPolyhedralFenchelBridge
      (n := n) (f := f) (g := g) α hf hg_poly hg hri hPointwiseOnCommon

/-- Lemma 31.0.3 (Simplified Separation for Polyhedral Functions: `g` is polyhedral): if
`f : ℝ^n → ℝ ∪ {+∞}` is proper convex, `g : ℝ^n → ℝ ∪ {+∞}` is polyhedral convex, and
`g` never takes the value `-∞`, `ri (dom f) ∩ dom g` is nonempty, and any finite primal
value `α` comes from the book's expression `inf_x (f x - g x)`, then there is a dual
witness `x* ∈ ℝ^n` with
`g* (x*) - f* (x*) ≥ α`. In this `EReal` formalization, that primal infimum is
represented by `functionInfimumEReal (commonEffectiveDomainDifference f g)`, which
agrees with `f - g` on the common effective domain of `f` and `g`. -/
lemma fenchel_duality_attainability_of_supremum_for_polyhedral_g {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg_ne_bot : ∀ x, g x ≠ (⊥ : EReal))
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
    (α : ℝ)
    (hα : functionInfimumEReal (commonEffectiveDomainDifference f g) = (α : EReal)) :
    ∃ xStar : Fin n → ℝ,
      fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  have hdomG_nonempty : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :=
    helperForLemma_31_0_3_nonempty_effectiveDomainG_of_qualification
      (f := f) (g := g) hri
  rcases hri with ⟨x0, hx0riF, hx0domG⟩
  have hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    -- The common-domain witness supplies nonemptiness of `dom g`, which is the only missing
    -- ingredient for properness beyond the polyhedral/non-`⊥` hypotheses.
    exact
      helperForLemma_31_0_3_polyhedralFunctionIsProperOnUniv_of_domainWitness
        (g := g) hg_poly hg_ne_bot hdomG_nonempty
  have hPointwiseOnCommon :
      ∀ x : Fin n → ℝ,
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          (α : EReal) ≤ f x - g x := by
    intro x hx
    -- This is the restricted-infimum lower bound that the separator argument actually uses.
    exact
      helperForLemma_31_0_3_pointwiseLowerBoundOnCommonEffectiveDomain
        (f := f) (g := g) (α := α) hα hx
  -- Reduce the remaining work to the dedicated mixed polyhedral separator helper.
  exact
    helperForLemma_31_0_3_dualWitnessFromPolyhedralQualification
      (n := n) (f := f) (g := g) α hf hg_poly hg_proper
      ⟨x0, hx0riF, hx0domG⟩ hPointwiseOnCommon

-- Proof sketch: this is the book's primal objective `x ↦ f x - g x`, written as a separate
-- definition so later statements can refer directly to the unrestricted infimum appearing in the
-- text.
/-- The pointwise primal difference `x ↦ f x - g x` used in the book's formulation of the primal
infimum. -/
noncomputable def pointwisePrimalDifference {n : ℕ} (f g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun x => f x - g x

/-- A polyhedral convex function in the book's sense: a polyhedral-convex `EReal`-valued
function that never takes the value `⊥`, so it models a map `ℝ^n → ℝ ∪ {+∞}`. -/
def IsBookPolyhedralConvexFunction (n : ℕ) (f : (Fin n → ℝ) → EReal) : Prop :=
  IsPolyhedralConvexFunction n f ∧ ∀ x, f x ≠ (⊥ : EReal)

-- Proof sketch: specialize the polyhedral separation argument to the case where both functions
-- are polyhedral. Use the book's literal primal objective `x ↦ f x - g x`, represented here by
-- `pointwisePrimalDifference f g`, and then identify the separating functional with a dual point
-- `x*` satisfying the dual inequality `g* x* - f* x* ≥ α`.
/-- Helper for Lemma 31.0.4: a finite value of the unrestricted primal infimum forces at least
one point where both polyhedral functions are effectively finite. -/
lemma helperForLemma_31_0_4_exists_commonEffectiveDomainPoint_of_finitePrimalInfimum {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hf_ne_bot : ∀ x, f x ≠ (⊥ : EReal))
    (hg_ne_bot : ∀ x, g x ≠ (⊥ : EReal))
    (α : ℝ)
    (hα : functionInfimumEReal (pointwisePrimalDifference f g) = (α : EReal)) :
    ∃ x0 : Fin n → ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
  -- First read the infimum hypothesis as the global lower bound `α ≤ f x - g x`.
  have hPointwise :
      ∀ x : Fin n → ℝ, (α : EReal) ≤ pointwisePrimalDifference f g x :=
    helperForLemma_31_0_2_pointwiseLowerBoundFromInfimum f g α hα
  by_contra hNoCommon
  -- If `g x = ⊤` anywhere, then `f x - g x = ⊥`, contradicting the finite lower bound `α`.
  have hg_ne_top : ∀ x : Fin n → ℝ, g x ≠ (⊤ : EReal) := by
    intro x hgx_top
    have hLower := hPointwise x
    rw [pointwisePrimalDifference, hgx_top, EReal.sub_top] at hLower
    have hAlphaNotLeBot : ¬ ((α : EReal) ≤ (⊥ : EReal)) := by
      simp
    exact hAlphaNotLeBot hLower
  -- Therefore, under the negated common-domain hypothesis, `f` must be `⊤` everywhere.
  have hf_top : ∀ x : Fin n → ℝ, f x = (⊤ : EReal) := by
    intro x
    by_contra hfx_ne_top
    have hxF :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
      rw [effectiveDomain_eq]
      exact ⟨by simp, (lt_top_iff_ne_top).2 hfx_ne_top⟩
    have hxG :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
      rw [effectiveDomain_eq]
      exact ⟨by simp, (lt_top_iff_ne_top).2 (hg_ne_top x)⟩
    exact hNoCommon ⟨x, hxF, hxG⟩
  -- But then every primal value is `⊤`, so the infimum cannot equal the finite real `α`.
  have hAllTop : ∀ x : Fin n → ℝ, pointwisePrimalDifference f g x = (⊤ : EReal) := by
    intro x
    simpa [pointwisePrimalDifference, hf_top x] using EReal.top_sub (hg_ne_top x)
  have hInfTop : functionInfimumEReal (pointwisePrimalDifference f g) = (⊤ : EReal) := by
    rw [functionInfimumEReal, iInf_eq_top]
    intro x
    exact hAllTop x
  have hAlphaTop : (α : EReal) = (⊤ : EReal) := by
    simpa [hα] using hInfTop
  exact EReal.coe_ne_top α hAlphaTop

/-- Helper for Lemma 31.0.4: the Chapter 20 polyhedral-family attainment theorem gives a finite
attained split for the restricted conjugate of `f + indicatorFunction (dom g)`. -/
lemma helperForLemma_31_0_4_restrictedFiniteDualAttainedSplit_of_polyhedralPair {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hf_poly : IsPolyhedralConvexFunction n f)
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hdomCommon :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∃ z y : Fin n → ℝ,
      fenchelConjugate n
          (fun x =>
            f x + indicatorFunction
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z ≠ (⊤ : EReal) ∧
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          =
            fenchelConjugate n
                (indicatorFunction
                  (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) (z - y) +
              fenchelConjugate n f y := by
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  let fPair : Fin 2 → (Fin n → ℝ) → EReal := fun i => Fin.cases (indicatorFunction domG) (fun _ => f) i
  have hPairZero : fPair 0 = indicatorFunction domG := by
    funext x
    rfl
  have hPairOne : fPair 1 = f := by
    funext x
    rfl
  have hRestrictedSum :
      (fun x => ∑ i : Fin 2, fPair i x) = (fun x => indicatorFunction domG x + f x) := by
    funext x
    rw [Fin.sum_univ_two, hPairZero, hPairOne]
  have hIndicator :=
    helperForLemma_31_0_3_indicatorEffectiveDomainOfPolyhedralG_isProperPolyhedral
      (n := n) (g := g) hg_poly hg
  rcases hdomCommon with ⟨x0, hx0F, hx0G⟩
  have hpolyPair : ∀ i : Fin 2, IsPolyhedralConvexFunction n (fPair i) := by
    intro i
    fin_cases i
    · simpa [fPair] using hIndicator.1
    · simpa [fPair] using hf_poly
  have hproperPair :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fPair i) := by
    intro i
    fin_cases i
    · simpa [fPair] using hIndicator.2
    · simpa [fPair] using hf
  have hdomPair :
      Set.Nonempty
        (⋂ i : Fin 2, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fPair i)) := by
    refine ⟨x0, Set.mem_iInter.2 ?_⟩
    intro i
    fin_cases i
    · simpa [fPair, domG, effectiveDomain_indicatorFunction_eq] using hx0G
    · simpa [fPair] using hx0F
  have hsumExists : ∃ x : Fin n → ℝ, (∑ i : Fin 2, fPair i x) ≠ (⊤ : EReal) := by
    refine ⟨x0, ?_⟩
    have hfx0_ne_top :
        f x0 ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hx0F
    simpa [fPair, Fin.sum_univ_two, domG, indicatorFunction, hx0G, add_comm] using hfx0_ne_top
  have hRestrProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => ∑ i : Fin 2, fPair i x) :=
    properConvexFunctionOn_sum_of_exists_ne_top (f := fPair) hproperPair hsumExists
  have hRestrStarProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fenchelConjugate n (fun x => ∑ i : Fin 2, fPair i x)) :=
    proper_fenchelConjugate_of_proper
      (n := n) (f := fun x => ∑ i : Fin 2, fPair i x) hRestrProper
  -- Pick a dual point where the restricted conjugate is finite before applying attainment.
  obtain ⟨z, r, hzFinite⟩ :=
    properConvexFunctionOn_exists_finite_point
      (n := n) (f := fenchelConjugate n (fun x => ∑ i : Fin 2, fPair i x)) hRestrStarProper
  have hz_ne_top :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fPair i x) z ≠ (⊤ : EReal) := by
    intro hzTop
    rw [hzFinite] at hzTop
    exact EReal.coe_ne_top r hzTop
  have hEqAt :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fPair i x) z =
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fPair i)) z := by
    exact
      congrArg (fun h : (Fin n → ℝ) → EReal => h z)
        (fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
          (f := fPair) (hpoly := hpolyPair) (hproper := hproperPair) (hdom := hdomPair))
  obtain ⟨zFamily, hsumFamily, hvalueFamily⟩ :=
    infimalConvolutionFamily_fenchelConjugate_attained_of_polyhedral_of_nonempty_iInter_effectiveDomain
      (f := fPair) (hpoly := hpolyPair) (hproper := hproperPair) (hdom := hdomPair)
      (by decide) z
  let y : Fin n → ℝ := zFamily 1
  have hsumTwo : zFamily 0 + zFamily 1 = z := by
    simpa [Fin.sum_univ_two] using hsumFamily
  have hsplit : z - y = zFamily 0 := by
    apply (sub_eq_iff_eq_add).2
    simpa [y, add_comm, add_left_comm, add_assoc] using hsumTwo.symm
  have hAttained :
      infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fPair i)) z =
        fenchelConjugate n (indicatorFunction domG) (z - y) + fenchelConjugate n f y := by
    calc
      infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fPair i)) z =
          ∑ i : Fin 2, fenchelConjugate n (fPair i) (zFamily i) := hvalueFamily
      _ = fenchelConjugate n (indicatorFunction domG) (z - y) + fenchelConjugate n f y := by
          rw [Fin.sum_univ_two, hPairZero, hPairOne, hsplit]
  have hz_ne_top' :
      fenchelConjugate n (fun x => indicatorFunction domG x + f x) z ≠ (⊤ : EReal) := by
    simpa [hRestrictedSum] using hz_ne_top
  refine ⟨z, y, ?_, ?_⟩
  · simpa [domG, add_comm] using hz_ne_top'
  · calc
      fenchelConjugate n
          (fun x =>
            f x + indicatorFunction
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
        =
          fenchelConjugate n (fun x => indicatorFunction domG x + f x) z := by
            simp [domG, add_comm]
      _ =
          fenchelConjugate n (fun x => ∑ i : Fin 2, fPair i x) z := by
            rw [hRestrictedSum]
      _ = infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fPair i)) z := hEqAt
      _ =
          fenchelConjugate n
              (indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) (z - y) +
            fenchelConjugate n f y := by
              simpa [domG] using hAttained

/-- Helper for Lemma 31.0.4: the polyhedral-family exactness theorem applied to the pair
`(indicatorFunction (dom g), g)` bounds `g⋆ z` by every explicit split carrying the common
support-function term. -/
lemma helperForLemma_31_0_4_supportFunctionCandidateBoundForG_of_polyhedralPair {n : ℕ}
    {g : (Fin n → ℝ) → EReal}
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hdomG : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∀ z y : Fin n → ℝ,
      fenchelConjugate n g z
        ≤ fenchelConjugate n
            (indicatorFunction
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) (z - y) +
          fenchelConjugate n g y := by
  intro z y
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  let gPair : Fin 2 → (Fin n → ℝ) → EReal := fun i => Fin.cases (indicatorFunction domG) (fun _ => g) i
  have hPairZero : gPair 0 = indicatorFunction domG := by
    funext x
    rfl
  have hPairOne : gPair 1 = g := by
    funext x
    rfl
  have hIndicatorPlusG :
      (fun x => ∑ i : Fin 2, gPair i x) = (fun x => indicatorFunction domG x + g x) := by
    funext x
    rw [Fin.sum_univ_two, hPairZero, hPairOne]
  have hIndicator :=
    helperForLemma_31_0_3_indicatorEffectiveDomainOfPolyhedralG_isProperPolyhedral
      (n := n) (g := g) hg_poly hg
  have hpolyPair : ∀ i : Fin 2, IsPolyhedralConvexFunction n (gPair i) := by
    intro i
    fin_cases i
    · simpa [gPair] using hIndicator.1
    · simpa [gPair] using hg_poly
  have hproperPair :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (gPair i) := by
    intro i
    fin_cases i
    · simpa [gPair] using hIndicator.2
    · simpa [gPair] using hg
  have hdomPair :
      Set.Nonempty
        (⋂ i : Fin 2, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (gPair i)) := by
    rcases hdomG with ⟨x0, hx0G⟩
    refine ⟨x0, Set.mem_iInter.2 ?_⟩
    intro i
    fin_cases i
    · simpa [gPair, domG, effectiveDomain_indicatorFunction_eq] using hx0G
    · simpa [gPair] using hx0G
  have hIndicatorAdd_eq_g :
      (fun x => indicatorFunction domG x + g x) = g := by
    funext x
    by_cases hx : x ∈ domG
    · simp [domG, indicatorFunction, hx]
    · have hgx_top : g x = (⊤ : EReal) := by
        by_contra hgx_ne_top
        change x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g at hx
        exact hx (by
          rw [effectiveDomain_eq]
          exact ⟨by simp, (lt_top_iff_ne_top).2 hgx_ne_top⟩)
      have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
      simp [domG, indicatorFunction, hx, hgx_top, hgx_ne_bot]
  have hEqAt :
      fenchelConjugate n g z =
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (gPair i)) z := by
    calc
      fenchelConjugate n g z =
          fenchelConjugate n (fun x => indicatorFunction domG x + g x) z := by
            rw [hIndicatorAdd_eq_g]
      _ =
          fenchelConjugate n (fun x => ∑ i : Fin 2, gPair i x) z := by
            rw [hIndicatorPlusG]
      _ =
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (gPair i)) z := by
            exact
              congrArg (fun h : (Fin n → ℝ) → EReal => h z)
                (fenchelConjugate_sum_eq_infimalConvolutionFamily_of_polyhedral_of_nonempty_iInter_effectiveDomain
                  (f := gPair) (hpoly := hpolyPair) (hproper := hproperPair) (hdom := hdomPair))
  have hCandidate :
      infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (gPair i)) z
        ≤ fenchelConjugate n (indicatorFunction domG) (z - y) + fenchelConjugate n g y := by
    -- The explicit split `z = (z - y) + y` is one admissible candidate in the defining infimum.
    unfold infimalConvolutionFamily
    let zFamily : Fin 2 → Fin n → ℝ := fun i => Fin.cases (z - y) (fun _ => y) i
    have hZFamilyZero : zFamily 0 = z - y := by
      funext x
      rfl
    have hZFamilyOne : zFamily 1 = y := by
      funext x
      rfl
    have hzFamilySum : (∑ i : Fin 2, zFamily i) = z := by
      rw [Fin.sum_univ_two, hZFamilyZero, hZFamilyOne]
      simp
    refine sInf_le ?_
    refine ⟨zFamily, hzFamilySum, ?_⟩
    simpa [Fin.sum_univ_two, hPairZero, hPairOne, hZFamilyZero, hZFamilyOne, add_comm] using
      (rfl :
        fenchelConjugate n (indicatorFunction domG) (z - y) + fenchelConjugate n g y =
          fenchelConjugate n (indicatorFunction domG) (z - y) + fenchelConjugate n g y)
  exact hEqAt.trans_le (by simpa [domG] using hCandidate)

end Section31
end Chap06

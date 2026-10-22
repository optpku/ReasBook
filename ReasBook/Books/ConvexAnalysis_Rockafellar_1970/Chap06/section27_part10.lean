/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part9

section Chap06
section Section27

/-- Helper for Corollary 6.27.3: if `y` is a recession direction of `h`, the affine slope forced
by `haffine` must be zero on every feasible forward ray, so any finite feasible point on that ray
already minimizes the indicator extension along the whole affine line. -/
lemma helperForCorollary_6_27_3_lineMinimizer_of_forwardRecessionDirection
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (haffine : EveryRecessionDirectionIsAffineAlongRay h)
    (C : Set (Fin n → ℝ)) (hbounded : HasRealLowerBoundOn h C)
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (x y : Fin n → ℝ) {s0 : ℝ}
    (hyRec : IsRecessionDirection h y)
    (hs0C : x + s0 • y ∈ C) (hs0Top : h (x + s0 • y) < (⊤ : EReal))
    (hForwardC : ∀ t : ℝ, 0 ≤ t → x + (s0 + t) • y ∈ C) :
    ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
  rcases haffine y hyRec with ⟨a, ha⟩
  have hSlopeNonpos :
      a ≤ 0 :=
    helperForCorollary_6_27_3_affineSlope_nonpositive_of_recessionDirection
      (h := h) hproper hyRec hs0Top ha
  have hSlopeNonneg :
      0 ≤ a := by
    -- The feasible forward ray cannot drive the affine formula below the uniform lower bound.
    have hRayFromBase :
        ∀ t : ℝ, 0 ≤ t → (x + s0 • y) + t • y ∈ C := by
      intro t ht
      simpa [add_assoc, add_left_comm, add_comm, add_smul] using hForwardC t ht
    exact
      helperForCorollary_6_27_3_affineSlope_nonnegative_on_pointedFeasibleRay
        (h := h) hproper C hRayFromBase hs0Top ha hbounded
  have hSlopeZero : a = 0 := by linarith
  have hs0Dom : x + s0 • y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [effectiveDomain_eq] using hs0Top
  refine ⟨s0, ?_⟩
  apply le_antisymm
  · -- Compare the chosen finite feasible point to every scalar parameter on the same line.
    refine le_iInf ?_
    intro s
    by_cases hsC : x + s • y ∈ C
    · by_cases hsTop : h (x + s • y) = (⊤ : EReal)
      · have htriv : h (x + s0 • y) ≤ (⊤ : EReal) := le_top
        simpa [hg, indicatorFunction, hs0C, hsC, hsTop] using htriv
      · have hsDom : x + s • y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
          simpa [effectiveDomain_eq] using lt_top_iff_ne_top.mpr hsTop
        have hvalueEq : h (x + s • y) = h (x + s0 • y) := by
          by_cases hs_le : s ≤ s0
          · have hstep : 0 ≤ s0 - s := sub_nonneg.mpr hs_le
            have hrewrite : (x + s • y) + (s0 - s) • y = x + s0 • y := by
              ext i
              simp [smul_eq_mul]
              ring
            calc
              h (x + s • y) = h ((x + s • y) + (s0 - s) • y) := by
                rw [ha (x + s • y) hsDom (s0 - s) hstep, hSlopeZero]
                simp
              _ = h (x + s0 • y) := by rw [hrewrite]
          · have hs0_le : s0 ≤ s := le_of_not_ge hs_le
            have hstep : 0 ≤ s - s0 := sub_nonneg.mpr hs0_le
            have hrewrite : (x + s0 • y) + (s - s0) • y = x + s • y := by
              ext i
              simp [smul_eq_mul]
              ring
            calc
              h (x + s • y) = h ((x + s0 • y) + (s - s0) • y) := by rw [hrewrite]
              _ = h (x + s0 • y) := by
                rw [ha (x + s0 • y) hs0Dom (s - s0) hstep, hSlopeZero]
                simp
        have hle : h (x + s0 • y) ≤ h (x + s • y) := by
          rw [hvalueEq]
        simpa [hg, indicatorFunction, hs0C, hsC] using hle
    · have hsBot : h (x + s • y) ≠ (⊥ : EReal) := hproper.2.2 _ (by simp)
      -- Outside the feasible slice, the indicator contribution is `⊤`.
      simpa [hg, indicatorFunction, hs0C, hsC, hsBot] using
        (show h (x + s0 • y) ≤ (⊤ : EReal) from le_top)
  · -- The global line infimum is always below the value at the chosen feasible parameter.
    exact iInf_le (fun s : ℝ => g (x + s • y)) s0

/-- Helper for Corollary 6.27.3: the same zero-slope argument works on a feasible backward ray
when `-y` is a recession direction of `h`. -/
lemma helperForCorollary_6_27_3_lineMinimizer_of_backwardRecessionDirection
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (haffine : EveryRecessionDirectionIsAffineAlongRay h)
    (C : Set (Fin n → ℝ)) (hbounded : HasRealLowerBoundOn h C)
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (x y : Fin n → ℝ) {s0 : ℝ}
    (hyRec : IsRecessionDirection h (-y))
    (hs0C : x + s0 • y ∈ C) (hs0Top : h (x + s0 • y) < (⊤ : EReal))
    (hBackwardC : ∀ t : ℝ, 0 ≤ t → x + (s0 - t) • y ∈ C) :
    ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
  rcases haffine (-y) hyRec with ⟨a, ha⟩
  have hSlopeNonpos :
      a ≤ 0 :=
    helperForCorollary_6_27_3_affineSlope_nonpositive_of_recessionDirection
      (h := h) hproper hyRec hs0Top ha
  have hSlopeNonneg :
      0 ≤ a := by
    -- The bounded-below hypothesis also controls the backward feasible ray.
    have hRayFromBase :
        ∀ t : ℝ, 0 ≤ t → (x + s0 • y) + t • (-y) ∈ C := by
      intro t ht
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul] using hBackwardC t ht
    exact
      helperForCorollary_6_27_3_affineSlope_nonnegative_on_pointedFeasibleRay
        (h := h) hproper C hRayFromBase hs0Top ha hbounded
  have hSlopeZero : a = 0 := by linarith
  have hs0Dom : x + s0 • y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [effectiveDomain_eq] using hs0Top
  refine ⟨s0, ?_⟩
  apply le_antisymm
  · -- As in the forward case, every finite feasible point on the line has the same value.
    refine le_iInf ?_
    intro s
    by_cases hsC : x + s • y ∈ C
    · by_cases hsTop : h (x + s • y) = (⊤ : EReal)
      · have htriv : h (x + s0 • y) ≤ (⊤ : EReal) := le_top
        simpa [hg, indicatorFunction, hs0C, hsC, hsTop] using htriv
      · have hsDom : x + s • y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
          simpa [effectiveDomain_eq] using lt_top_iff_ne_top.mpr hsTop
        have hvalueEq : h (x + s • y) = h (x + s0 • y) := by
          by_cases hs_le : s ≤ s0
          · have hstep : 0 ≤ s0 - s := sub_nonneg.mpr hs_le
            have hrewrite : (x + s0 • y) + (s0 - s) • (-y) = x + s • y := by
              ext i
              simp [smul_eq_mul]
              ring
            calc
              h (x + s • y) = h ((x + s0 • y) + (s0 - s) • (-y)) := by rw [hrewrite]
              _ = h (x + s0 • y) := by
                rw [ha (x + s0 • y) hs0Dom (s0 - s) hstep, hSlopeZero]
                simp
          · have hs0_le : s0 ≤ s := le_of_not_ge hs_le
            have hstep : 0 ≤ s - s0 := sub_nonneg.mpr hs0_le
            have hrewrite : (x + s • y) + (s - s0) • (-y) = x + s0 • y := by
              ext i
              simp [smul_eq_mul]
              ring
            calc
              h (x + s • y) = h ((x + s • y) + (s - s0) • (-y)) := by
                rw [ha (x + s • y) hsDom (s - s0) hstep, hSlopeZero]
                simp
              _ = h (x + s0 • y) := by rw [hrewrite]
        have hle : h (x + s0 • y) ≤ h (x + s • y) := by
          rw [hvalueEq]
        simpa [hg, indicatorFunction, hs0C, hsC] using hle
    · have hsBot : h (x + s • y) ≠ (⊥ : EReal) := hproper.2.2 _ (by simp)
      -- Outside the feasible slice, the indicator again forces the value to `⊤`.
      simpa [hg, indicatorFunction, hs0C, hsC, hsBot] using
        (show h (x + s0 • y) ≤ (⊤ : EReal) from le_top)
  · -- The unrestricted line infimum is always below the value at the chosen parameter.
    exact iInf_le (fun s : ℝ => g (x + s • y)) s0

/-- Helper for Corollary 6.27.3: the scalar sublevel set of the line restriction
`s ↦ g (x + s • y)` is a closed convex subset of `ℝ`. -/
lemma helperForCorollary_6_27_3_scalarSublevel_closedConvex
    {n : ℕ} {g : (Fin n → ℝ) → EReal} (hgClosed : ClosedConvexFunction g)
    (x y : Fin n → ℝ) (α : ℝ) :
    let S : Set ℝ := {s : ℝ | g (x + s • y) ≤ (α : EReal)}
    IsClosed S ∧ Convex ℝ S := by
  let S : Set ℝ := {s : ℝ | g (x + s • y) ≤ (α : EReal)}
  have hSubClosed : IsClosed (sublevelSetEReal g α) := by
    exact (lowerSemicontinuous_iff_closed_sublevel (f := g)).1 hgClosed.2 α
  have hSubConvex : Convex ℝ (sublevelSetEReal g α) := by
    simpa [sublevelSetEReal] using
      (convexFunction_level_sets_convex (f := g) hgClosed.1 (α := (α : EReal))).2
  have hSclosed : IsClosed S := by
    let L : ℝ → Fin n → ℝ := fun s => x + s • y
    have hcont : Continuous L := by
      continuity
    -- The scalar sublevel is the continuous preimage of an ambient closed sublevel set.
    simpa [S, L, sublevelSetEReal] using hSubClosed.preimage hcont
  have hSconv : Convex ℝ S := by
    intro s hs t ht a b ha hb hab
    have hsSub : x + s • y ∈ sublevelSetEReal g α := by
      simpa [S, sublevelSetEReal] using hs
    have htSub : x + t • y ∈ sublevelSetEReal g α := by
      simpa [S, sublevelSetEReal] using ht
    have hcomb : a • (x + s • y) + b • (x + t • y) = x + (a • s + b • t) • y := by
      have hb' : b = 1 - a := by
        linarith
      subst b
      ext i
      simp [smul_eq_mul]
      ring
    have hmem :
        a • (x + s • y) + b • (x + t • y) ∈ sublevelSetEReal g α :=
      hSubConvex hsSub htSub ha hb hab
    -- Convexity of the ambient sublevel set descends to the scalar parameter set.
    change g (x + (a • s + b • t) • y) ≤ (α : EReal)
    rw [← hcomb]
    exact hmem
  exact ⟨hSclosed, hSconv⟩

/-- Helper for Corollary 6.27.3: a forward halfline on which the indicator extension
`g = h + δ_C` stays below a finite real level produces an ambient recession direction of `h`. -/
lemma helperForCorollary_6_27_3_sublevelHalfline_forces_ambientRecession
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (C : Set (Fin n → ℝ))
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (x y : Fin n → ℝ) (hy : y ≠ 0) (α : ℝ) {s0 : ℝ}
    (hHalfline :
      ∀ t : ℝ, 0 ≤ t → g (x + (s0 + t) • y) ≤ (α : EReal)) :
    IsRecessionDirection h y := by
  let _ := hy
  let S : Set (Fin n → ℝ) := sublevelSetEReal h α
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let SE : Set (EuclideanSpace ℝ (Fin n)) := e ⁻¹' S
  have hProperEReal :
      ProperConvexERealFunction (F := Fin n → ℝ) h :=
    helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
      (f := h) hproper
  have hSubClosed : IsClosed S := by
    exact (lowerSemicontinuous_iff_closed_sublevel (f := h)).1 hclosed.2 α
  have hSubConvex : Convex ℝ S := by
    simpa [S, sublevelSetEReal] using
      (convexFunction_level_sets_convex (f := h) hclosed.1 (α := (α : EReal))).2
  have hRayInSublevel :
      ∀ t : ℝ, 0 ≤ t → x + (s0 + t) • y ∈ S := by
    intro t ht
    have hzBot : h (x + (s0 + t) • y) ≠ (⊥ : EReal) := hproper.2.2 _ (by simp)
    have hzLe : g (x + (s0 + t) • y) ≤ (α : EReal) := hHalfline t ht
    have hzC : x + (s0 + t) • y ∈ C := by
      by_contra hzNotC
      have : False := by
        simpa [hg, indicatorFunction, hzNotC, hzBot] using hzLe
      exact this.elim
    -- A finite upper bound strips away the indicator term and yields a genuine sublevel point.
    have hzLe' : h (x + (s0 + t) • y) ≤ (α : EReal) := by
      simpa [hg, indicatorFunction, hzC] using hzLe
    simpa [S, sublevelSetEReal] using hzLe'
  have hx0S : x + s0 • y ∈ S := by
    simpa using hRayInSublevel 0 le_rfl
  have hSEne : SE.Nonempty := by
    refine ⟨e.symm (x + s0 • y), ?_⟩
    simpa [SE] using hx0S
  have hSEclosed : IsClosed SE := by
    -- Pull the ambient closed sublevel back to Euclidean space via the canonical equivalence.
    simpa [SE] using hSubClosed.preimage e.continuous
  have hSEconv : Convex ℝ SE := by
    intro u hu v hv a b ha hb hab
    have huS : e u ∈ S := by simpa [SE] using hu
    have hvS : e v ∈ S := by simpa [SE] using hv
    have hcomb : a • e u + b • e v ∈ S := hSubConvex huS hvS ha hb hab
    -- Convex combinations commute with the linear equivalence.
    simpa [SE, map_add, map_smul] using hcomb
  have hSEhalf :
      ∀ t : ℝ, 0 ≤ t → e.symm (x + s0 • y) + t • e.symm y ∈ SE := by
    intro t ht
    have hmem : x + (s0 + t) • y ∈ S := hRayInSublevel t ht
    -- The affine halfline in `Fin n → ℝ` is exactly the image of the Euclidean halfline.
    simpa [SE, map_add, map_smul, add_smul, smul_smul, add_assoc, add_left_comm, add_comm] using
      hmem
  have hRecSE : e.symm y ∈ Set.recessionCone SE :=
    halfline_mem_recessionCone (C := SE) hSEne hSEclosed hSEconv hSEhalf
  have hRecS' : e.toLinearEquiv (e.symm y) ∈ Set.recessionCone S :=
    (mem_recessionCone_preimage_linearEquiv_iff e.toLinearEquiv S (e.symm y)).1 hRecSE
  have hRecS : y ∈ Set.recessionCone S := by
    simpa [S] using hRecS'
  have hyRecE : y ∈ recessionConeEReal (F := Fin n → ℝ) h :=
    section14_recessionCone_sublevel_subset_recessionConeEReal
      (E := Fin n → ℝ) (f := h) hProperEReal hclosed.2 (α := α) ⟨x + s0 • y, hx0S⟩ hRecS
  -- Route correction: transport the whole sublevel set to Euclidean space, prove recession there,
  -- and map the conclusion back before invoking the Section 14 recession theorem.
  simpa [recessionConeEReal, IsRecessionDirection, recessionFunctionEReal,
    recessionFunction, erealDom, effectiveDomain_eq] using hyRecE

/-- Helper for Corollary 6.27.3: if the feasible scalar slice is a right ray and the line
restriction of `g = h + δ_C` still fails to attain its infimum, then a scalar sublevel contains a
forward halfline, forcing `y` to be an ambient recession direction of `h`. -/
lemma helperForCorollary_6_27_3_rightRay_nonattainment_forces_ambientRecession
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (C : Set (Fin n → ℝ))
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (hgClosed : ClosedConvexFunction g)
    (x y : Fin n → ℝ) (hy : y ≠ 0)
    (hFinite : ∃ s : ℝ, x + s • y ∈ C ∧ h (x + s • y) < (⊤ : EReal))
    (hSlice :
      let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
      T = Set.Ici (sInf T))
    (hNoMin : ¬ ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y)) :
    IsRecessionDirection h y := by
  rcases hFinite with ⟨s0, hs0C, hs0Top⟩
  let α : ℝ := (h (x + s0 • y)).toReal
  let S : Set ℝ := {s : ℝ | g (x + s • y) ≤ (α : EReal)}
  let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
  have hαeq : ((α : ℝ) : EReal) = h (x + s0 • y) := by
    have hbot : h (x + s0 • y) ≠ (⊥ : EReal) := hproper.2.2 _ (by simp)
    simpa [α] using EReal.coe_toReal (x := h (x + s0 • y)) hs0Top.ne hbot
  have hs0S : s0 ∈ S := by
    -- The finite feasible witness lies in the chosen scalar sublevel.
    change g (x + s0 • y) ≤ (α : EReal)
    have hs0Eq : g (x + s0 • y) = (α : EReal) := by
      calc
        g (x + s0 • y) = h (x + s0 • y) := by
          simp [hg, indicatorFunction, hs0C]
        _ = (α : EReal) := hαeq.symm
    exact le_of_eq hs0Eq
  have hSclosed : IsClosed S := by
    simpa [S] using
      (helperForCorollary_6_27_3_scalarSublevel_closedConvex
        (g := g) hgClosed x y α).1
  have hSconv : Convex ℝ S := by
    simpa [S] using
      (helperForCorollary_6_27_3_scalarSublevel_closedConvex
        (g := g) hgClosed x y α).2
  have hSliceT : T = Set.Ici (sInf T) := by
    simpa [T] using hSlice
  have hSsubsetT : S ⊆ T := by
    intro s hsS
    by_contra hsNotT
    have hsNotC : x + s • y ∉ C := by
      simpa [T] using hsNotT
    have hsBot : h (x + s • y) ≠ (⊥ : EReal) := hproper.2.2 _ (by simp)
    have hsLe : h (x + s • y) + indicatorFunction C (x + s • y) ≤ (α : EReal) := by
      simpa [S, hg] using hsS
    have hfalse : False := by
      simpa [indicatorFunction, hsNotC, hsBot] using hsLe
    exact hfalse.elim
  have hSbelow : BddBelow S := by
    refine ⟨sInf T, ?_⟩
    intro s hs
    have hsT : s ∈ T := hSsubsetT hs
    rw [hSliceT] at hsT
    exact hsT
  have hSne : S.Nonempty := ⟨s0, hs0S⟩
  have hSpre : IsPreconnected S := hSconv.isPreconnected
  have hNotAbove : ¬ BddAbove S := by
    intro hSabove
    have hSeq :
        S = Set.Icc (sInf S) (sSup S) :=
      eq_Icc_csInf_csSup_of_connected_bdd_closed
        ⟨hSne, hSpre⟩ hSbelow hSabove hSclosed
    let φ : ℝ → EReal := fun s => g (x + s • y)
    have hφlsc : LowerSemicontinuous φ := by
      let L : ℝ → Fin n → ℝ := fun s => x + s • y
      have hcont : Continuous L := by
        simpa [L] using (continuous_const.add (continuous_id.smul continuous_const))
      -- The line restriction of `g` remains lower semicontinuous.
      simpa [φ, L] using hgClosed.2.comp_continuous hcont
    obtain ⟨t, htIcc, htMin⟩ :=
      (hφlsc.lowerSemicontinuousOn (Set.Icc (sInf S) (sSup S))).exists_isMinOn
        ⟨s0, by
          show s0 ∈ Set.Icc (sInf S) (sSup S)
          exact hSeq ▸ hs0S⟩ isCompact_Icc
    have htS : t ∈ S := by
      exact hSeq.symm ▸ htIcc
    have htGlobal :
        ∀ s : ℝ, g (x + t • y) ≤ g (x + s • y) := by
      intro s
      by_cases hsS : s ∈ S
      · have hsIcc : s ∈ Set.Icc (sInf S) (sSup S) := by
          exact hSeq ▸ hsS
        exact (isMinOn_iff.mp htMin) s hsIcc
      · have htLeAlpha : g (x + t • y) ≤ (α : EReal) := htS
        have hAlphaLt : (α : EReal) < g (x + s • y) := by
          exact lt_of_not_ge hsS
        exact le_trans htLeAlpha (le_of_lt hAlphaLt)
    have htEq :
        g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
      apply le_antisymm
      · refine le_iInf ?_
        intro s
        exact htGlobal s
      · exact iInf_le (fun s : ℝ => g (x + s • y)) t
    exact hNoMin ⟨t, htEq⟩
  have hsInfMem : sInf S ∈ S := hSclosed.csInf_mem hSne hSbelow
  have hForwardHalfline : ∀ t : ℝ, 0 ≤ t → sInf S + t ∈ S := by
    intro t ht
    rcases eq_or_lt_of_le ht with rfl | ht'
    · simpa using hsInfMem
    · have hmem : sInf S + t ∈ Set.Ioi (sInf S) := by
        change sInf S < sInf S + t
        linarith
      exact (hSpre.Ioi_csInf_subset hSbelow hNotAbove) hmem
  -- The unbounded scalar sublevel now supplies a genuine ambient halfline in a real sublevel set.
  exact
    helperForCorollary_6_27_3_sublevelHalfline_forces_ambientRecession
      (h := h) hclosed hproper C hg x y hy α
      (s0 := sInf S) (by
        intro t ht
        simpa [S] using hForwardHalfline t ht)

lemma helperForCorollary_6_27_3_rightRayScalarSlice_attainment_of_not_recessionDirection
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (haffine : EveryRecessionDirectionIsAffineAlongRay h)
    (C : Set (Fin n → ℝ)) (hbounded : HasRealLowerBoundOn h C)
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (hgClosed : ClosedConvexFunction g)
    (x y : Fin n → ℝ) (hy : y ≠ 0)
    (hFinite : ∃ s : ℝ, x + s • y ∈ C ∧ h (x + s • y) < (⊤ : EReal))
    (hyNotRec : ¬ IsRecessionDirection h y)
    (hSlice :
      let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
      T = Set.Ici (sInf T)) :
    ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
  let _ := haffine
  let _ := hbounded
  by_contra hNoMin
  -- Route correction: instead of transferring a scalar recession direction directly to `h`,
  -- we extract a scalar sublevel halfline and lift it to an ambient recession contradiction.
  exact
    hyNotRec
      (helperForCorollary_6_27_3_rightRay_nonattainment_forces_ambientRecession
        (h := h) hclosed hproper C hg hgClosed x y hy hFinite hSlice hNoMin)

/-- Helper for Corollary 6.27.3: negating the scalar parameter only reparametrizes the same
ambient line, so the line infimum is unchanged. -/
lemma helperForCorollary_6_27_3_lineInfimum_negDirection_eq
    {n : ℕ} (g : (Fin n → ℝ) → EReal) (x y : Fin n → ℝ) :
    (⨅ s : ℝ, g (x + s • (-y))) = ⨅ s : ℝ, g (x + s • y) := by
  apply le_antisymm
  · -- Use the substitution `t = -s` to compare the reflected parametrization with the original.
    refine le_iInf ?_
    intro s
    have hparam : x + (-s) • (-y) = x + s • y := by
      ext i
      simp [smul_eq_mul]
    calc
      (⨅ t : ℝ, g (x + t • (-y))) ≤ g (x + (-s) • (-y)) := by
        exact iInf_le (fun t : ℝ => g (x + t • (-y))) (-s)
      _ = g (x + s • y) := by rw [hparam]
  · -- The reverse inequality is the same substitution in the opposite direction.
    refine le_iInf ?_
    intro s
    have hparam : x + (-s) • y = x + s • (-y) := by
      ext i
      simp [smul_eq_mul]
    calc
      (⨅ t : ℝ, g (x + t • y)) ≤ g (x + (-s) • y) := by
        exact iInf_le (fun t : ℝ => g (x + t • y)) (-s)
      _ = g (x + s • (-y)) := by rw [hparam]

/-- Helper for Corollary 6.27.3: the symmetric unresolved branch is the left ray `Iic`, where
one still has to descend the bounded-below line problem when `-y` is not an ambient recession
direction. -/
lemma helperForCorollary_6_27_3_leftRayScalarSlice_attainment_of_not_recessionDirection
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (haffine : EveryRecessionDirectionIsAffineAlongRay h)
    (C : Set (Fin n → ℝ)) (hbounded : HasRealLowerBoundOn h C)
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (hgClosed : ClosedConvexFunction g)
    (x y : Fin n → ℝ) (hy : y ≠ 0)
    (hFinite : ∃ s : ℝ, x + s • y ∈ C ∧ h (x + s • y) < (⊤ : EReal))
    (hyNotRec : ¬ IsRecessionDirection h (-y))
    (hSlice :
      let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
      T = Set.Iic (sSup T)) :
    ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
  rcases hFinite with ⟨s0, hs0C, hs0Top⟩
  have hnegY : -y ≠ 0 := by
    intro hneg
    exact hy (neg_eq_zero.mp hneg)
  have hFiniteNeg : ∃ s : ℝ, x + s • (-y) ∈ C ∧ h (x + s • (-y)) < (⊤ : EReal) := by
    refine ⟨-s0, ?_, ?_⟩
    · -- The same feasible point is obtained after flipping both the scalar and the direction.
      have hparam : x + (-s0) • (-y) = x + s0 • y := by
        ext i
        simp [smul_eq_mul]
      simpa [hparam] using hs0C
    · -- The finite-value witness is preserved by that same reparametrization.
      have hparam : x + (-s0) • (-y) = x + s0 • y := by
        ext i
        simp [smul_eq_mul]
      simpa [hparam] using hs0Top
  have hSliceNeg :
      let T : Set ℝ := {s : ℝ | x + s • (-y) ∈ C}
      T = Set.Ici (sInf T) := by
    let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
    let TNeg : Set ℝ := {s : ℝ | x + s • (-y) ∈ C}
    have hSliceT : T = Set.Iic (sSup T) := by
      simpa [T] using hSlice
    have hTNeg :
        TNeg = Set.Ici (-(sSup T)) := by
      ext s
      constructor
      · intro hs
        have hparam : x + s • (-y) = x + (-s) • y := by
          ext i
          simp [smul_eq_mul]
        have hnegMem : -s ∈ T := by
          simpa [T, TNeg, hparam] using hs
        have hnegLe : -s ≤ sSup T := by
          rw [hSliceT] at hnegMem
          exact hnegMem
        change -(sSup T) ≤ s
        linarith
      · intro hs
        have hnegLe : -s ≤ sSup T := by
          change -(sSup T) ≤ s at hs
          linarith
        have hnegMem : -s ∈ T := by
          rw [hSliceT]
          exact hnegLe
        have hparam : x + s • (-y) = x + (-s) • y := by
          ext i
          simp [smul_eq_mul]
        simpa [T, TNeg, hparam] using hnegMem
    -- The reflected left ray is exactly the right ray needed by the previous lemma.
    change TNeg = Set.Ici (sInf TNeg)
    rw [hTNeg, csInf_Ici]
  obtain ⟨tNeg, htNeg⟩ :=
    helperForCorollary_6_27_3_rightRayScalarSlice_attainment_of_not_recessionDirection
      (h := h) hclosed hproper haffine C hbounded hg hgClosed x (-y) hnegY hFiniteNeg hyNotRec
      hSliceNeg
  refine ⟨-tNeg, ?_⟩
  -- Route correction: the left-ray branch is the right-ray branch after the parameter flip
  -- `s ↦ -s`, so we transport the witness back to the original direction `y`.
  have hparam : x + (-tNeg) • y = x + tNeg • (-y) := by
    ext i
    simp [smul_eq_mul]
  calc
    g (x + (-tNeg) • y) = g (x + tNeg • (-y)) := by rw [hparam]
    _ = ⨅ s : ℝ, g (x + s • (-y)) := htNeg
    _ = ⨅ s : ℝ, g (x + s • y) :=
      helperForCorollary_6_27_3_lineInfimum_negDirection_eq g x y

/-- Helper for Corollary 6.27.3: if the feasible scalar slice is the whole line and the line
restriction of `g = h + δ_C` still has no minimizer, then some scalar sublevel is unbounded in at
least one direction, forcing either `y` or `-y` to be an ambient recession direction of `h`. -/
lemma helperForCorollary_6_27_3_fullLine_nonattainment_forces_oneAmbientRecession
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (C : Set (Fin n → ℝ))
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (hgClosed : ClosedConvexFunction g)
    (x y : Fin n → ℝ) (hy : y ≠ 0)
    (hFinite : ∃ s : ℝ, x + s • y ∈ C ∧ h (x + s • y) < (⊤ : EReal))
    (hNoMin : ¬ ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y)) :
    IsRecessionDirection h y ∨ IsRecessionDirection h (-y) := by
  rcases hFinite with ⟨s0, hs0C, hs0Top⟩
  let α : ℝ := (h (x + s0 • y)).toReal
  let S : Set ℝ := {s : ℝ | g (x + s • y) ≤ (α : EReal)}
  have hαeq : ((α : ℝ) : EReal) = h (x + s0 • y) := by
    have hbot : h (x + s0 • y) ≠ (⊥ : EReal) := hproper.2.2 _ (by simp)
    simpa [α] using EReal.coe_toReal (x := h (x + s0 • y)) hs0Top.ne hbot
  have hs0S : s0 ∈ S := by
    -- The finite feasible base point belongs to the chosen scalar sublevel.
    change g (x + s0 • y) ≤ (α : EReal)
    have hs0Eq : g (x + s0 • y) = (α : EReal) := by
      calc
        g (x + s0 • y) = h (x + s0 • y) := by
          simp [hg, indicatorFunction, hs0C]
        _ = (α : EReal) := hαeq.symm
    exact le_of_eq hs0Eq
  have hSclosed : IsClosed S := by
    simpa [S] using
      (helperForCorollary_6_27_3_scalarSublevel_closedConvex
        (g := g) hgClosed x y α).1
  have hSconv : Convex ℝ S := by
    simpa [S] using
      (helperForCorollary_6_27_3_scalarSublevel_closedConvex
        (g := g) hgClosed x y α).2
  have hSne : S.Nonempty := ⟨s0, hs0S⟩
  have hSpre : IsPreconnected S := hSconv.isPreconnected
  have hNoBoundedBoth : ¬ (BddBelow S ∧ BddAbove S) := by
    rintro ⟨hSbelow, hSabove⟩
    have hSeq :
        S = Set.Icc (sInf S) (sSup S) :=
      eq_Icc_csInf_csSup_of_connected_bdd_closed
        ⟨hSne, hSpre⟩ hSbelow hSabove hSclosed
    let φ : ℝ → EReal := fun s => g (x + s • y)
    have hφlsc : LowerSemicontinuous φ := by
      let L : ℝ → Fin n → ℝ := fun s => x + s • y
      have hcont : Continuous L := by
        simpa [L] using (continuous_const.add (continuous_id.smul continuous_const))
      -- Compact scalar minimization applies to the line restriction of `g`.
      simpa [φ, L] using hgClosed.2.comp_continuous hcont
    obtain ⟨t, htIcc, htMin⟩ :=
      (hφlsc.lowerSemicontinuousOn (Set.Icc (sInf S) (sSup S))).exists_isMinOn
        ⟨s0, by
          show s0 ∈ Set.Icc (sInf S) (sSup S)
          exact hSeq ▸ hs0S⟩ isCompact_Icc
    have htS : t ∈ S := by
      exact hSeq.symm ▸ htIcc
    have htGlobal :
        ∀ s : ℝ, g (x + t • y) ≤ g (x + s • y) := by
      intro s
      by_cases hsS : s ∈ S
      · have hsIcc : s ∈ Set.Icc (sInf S) (sSup S) := by
          exact hSeq ▸ hsS
        exact (isMinOn_iff.mp htMin) s hsIcc
      · have htLeAlpha : g (x + t • y) ≤ (α : EReal) := htS
        have hAlphaLt : (α : EReal) < g (x + s • y) := by
          exact lt_of_not_ge hsS
        exact le_trans htLeAlpha (le_of_lt hAlphaLt)
    have htEq :
        g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
      apply le_antisymm
      · refine le_iInf ?_
        intro s
        exact htGlobal s
      · exact iInf_le (fun s : ℝ => g (x + s • y)) t
    exact hNoMin ⟨t, htEq⟩
  by_cases hSabove : BddAbove S
  · by_cases hSbelow : BddBelow S
    · exact False.elim (hNoBoundedBoth ⟨hSbelow, hSabove⟩)
    · have hsSupMem : sSup S ∈ S := hSclosed.csSup_mem hSne hSabove
      have hBackwardHalfline : ∀ t : ℝ, 0 ≤ t → sSup S - t ∈ S := by
        intro t ht
        rcases eq_or_lt_of_le ht with rfl | ht'
        · simpa using hsSupMem
        · have hmem : sSup S - t ∈ Set.Iio (sSup S) := by
            change sSup S - t < sSup S
            linarith
          exact (hSpre.Iio_csSup_subset hSbelow hSabove) hmem
      have hnegY : -y ≠ 0 := by
        intro hneg
        exact hy (neg_eq_zero.mp hneg)
      -- Reparametrize the backward scalar halfline as a forward halfline in direction `-y`.
      exact Or.inr
        (helperForCorollary_6_27_3_sublevelHalfline_forces_ambientRecession
          (h := h) hclosed hproper C hg x (-y) hnegY α
          (s0 := -sSup S) (by
            intro t ht
            have htS : sSup S - t ∈ S := hBackwardHalfline t ht
            have htLe : g (x + (sSup S - t) • y) ≤ (α : EReal) := by
              simpa [S] using htS
            have hparam : x + (-sSup S + t) • (-y) = x + (sSup S - t) • y := by
              ext i
              simp [smul_eq_mul]
              ring
            rw [hparam]
            exact htLe))
  · by_cases hSbelow : BddBelow S
    · have hsInfMem : sInf S ∈ S := hSclosed.csInf_mem hSne hSbelow
      have hForwardHalfline : ∀ t : ℝ, 0 ≤ t → sInf S + t ∈ S := by
        intro t ht
        rcases eq_or_lt_of_le ht with rfl | ht'
        · simpa using hsInfMem
        · have hmem : sInf S + t ∈ Set.Ioi (sInf S) := by
            change sInf S < sInf S + t
            linarith
          exact (hSpre.Ioi_csInf_subset hSbelow hSabove) hmem
      exact Or.inl
        (helperForCorollary_6_27_3_sublevelHalfline_forces_ambientRecession
          (h := h) hclosed hproper C hg x y hy α
          (s0 := sInf S) (by
            intro t ht
            simpa [S] using hForwardHalfline t ht))
    · have hSuniv : S = Set.univ := hSpre.eq_univ_of_unbounded hSbelow hSabove
      -- If the scalar sublevel is all of `ℝ`, any forward ray already lies inside it.
      exact Or.inl
        (helperForCorollary_6_27_3_sublevelHalfline_forces_ambientRecession
          (h := h) hclosed hproper C hg x y hy α
          (s0 := 0) (by
            intro t ht
            have htS : t ∈ S := by
              rw [hSuniv]
              simp
            simpa [S] using htS))

lemma helperForCorollary_6_27_3_fullLineScalarSlice_attainment_of_no_recessionDirection
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (haffine : EveryRecessionDirectionIsAffineAlongRay h)
    (C : Set (Fin n → ℝ)) (hbounded : HasRealLowerBoundOn h C)
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (hgClosed : ClosedConvexFunction g)
    (x y : Fin n → ℝ) (hy : y ≠ 0)
    (hFinite : ∃ s : ℝ, x + s • y ∈ C ∧ h (x + s • y) < (⊤ : EReal))
    (hyNotRec : ¬ IsRecessionDirection h y)
    (hyNegNotRec : ¬ IsRecessionDirection h (-y))
    (hSlice :
      let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
      T = Set.univ) :
    ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
  let _ := haffine
  let _ := hbounded
  let _ := hSlice
  by_contra hNoMin
  have hRecOr :
      IsRecessionDirection h y ∨ IsRecessionDirection h (-y) :=
    helperForCorollary_6_27_3_fullLine_nonattainment_forces_oneAmbientRecession
      (h := h) hclosed hproper C hg hgClosed x y hy hFinite hNoMin
  -- Route correction: the unresolved full-line branch now reduces to which side the scalar
  -- sublevel escapes to; either escape yields an ambient recession contradiction.
  rcases hRecOr with hyRec | hyNegRec
  · exact hyNotRec hyRec
  · exact hyNegNotRec hyNegRec


end Section27
end Chap06

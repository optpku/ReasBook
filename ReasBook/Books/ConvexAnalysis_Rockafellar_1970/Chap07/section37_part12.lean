/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part17
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part11

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Corollary 37.6.2: when both arguments satisfy the constraints, the ambient lower
simple extension agrees with the original real-valued kernel on subtype points. -/
lemma helperForCorollary_37_6_2_lowerSimpleExtensionOfReal_agrees_on_subtypes
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (u : C) (v : D) :
    lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal)) u.1 v.1 =
      ((J u.1 v.1 : ℝ) : EReal) := by
  -- The subtype witnesses put the evaluation point inside `C × D`, so the extension collapses
  -- back to the original kernel value.
  exact helperForLemma33_0_3_lowerSimpleExtension_agrees u.2 v.2

/-- Helper for Corollary 37.6.2: for a real-valued kernel, the first effective domain of the
lower simple extension is exactly the first constraint set `C`. -/
lemma helperForCorollary_37_6_2_effectiveDomain1_lowerSimpleExtensionOfReal_eq
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) :
    effectiveDomain₁ (lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal))) = C := by
  ext u
  constructor
  · intro hu
    by_contra huC
    rcases hDne with ⟨v, hv⟩
    have hbot :
        lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal)) u v = ⊥ := by
      -- Once `u ∉ C`, the lower simple extension is identically `⊥` in the second variable.
      simp [lowerSimpleExtension, huC]
    have hgt : lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal)) u v > ⊥ := hu v
    rw [hbot] at hgt
    simp at hgt
  · intro hu v
    by_cases hv : v ∈ D
    · -- Inside `C × D`, the ambient extension reduces to the original real value, hence is
      -- automatically strictly above `⊥`.
      rw [helperForLemma33_0_3_lowerSimpleExtension_agrees hu hv]
      simp
    · simp [lowerSimpleExtension, hu, hv]

/-- Helper for Corollary 37.6.2: for a real-valued kernel, the second effective domain of the
lower simple extension is exactly the second constraint set `D`. -/
lemma helperForCorollary_37_6_2_effectiveDomain2_lowerSimpleExtensionOfReal_eq
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) :
    effectiveDomain₂ (lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal))) = D := by
  ext v
  constructor
  · intro hv
    by_contra hvD
    rcases hCne with ⟨u, hu⟩
    have hImpossible :
        ¬ ((⊤ : EReal) < (⊤ : EReal)) := by
      simp
    -- Evaluating at a witness in `C` forces the off-domain value `⊤`, contradicting membership in
    -- the second effective domain.
    exact hImpossible (by simpa [effectiveDomain₂, lowerSimpleExtension, hu, hvD] using hv u)
  · intro hv u
    by_cases hu : u ∈ C
    · -- On admissible points, the lower extension again reduces to the original real value.
      rw [helperForLemma33_0_3_lowerSimpleExtension_agrees hu hv]
      simp
    · simp [lowerSimpleExtension, hu]

/-- Helper for Corollary 37.6.2: the lower simple extension of a continuous finite
concave-convex kernel on `C × D` is a closed proper saddle-function on the ambient space. -/
lemma helperForCorollary_37_6_2_lowerSimpleExtensionOfReal_closed_proper
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hStrongClosures : Section34Text34_1_9StrongClosureQualification m n)
    (hClosedNoBot : ∀ L : SaddleFunction m n,
      IsClosedSaddleFunction L → HasNoBotValuesBifunction L)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (hJcont : ContinuousOn (fun p : (Fin m → ℝ) × (Fin n → ℝ) => J p.1 p.2) (C ×ˢ D))
    (hJcc : IsConcaveConvexOn C D (fun u v => ((J u v : ℝ) : EReal))) :
    IsClosedSaddleFunction (lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal))) ∧
      IsProperSaddleFunction (lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal))) := by
  let K1 : SaddleFunction m n := lowerSimpleExtensionOfReal C D J
  have hCor33 :=
    «Corollary33.3.3» (C := C) (D := D) (K := J)
      hCne hDne hCclosed hDclosed hCconv hDconv hJcont hJcc
  dsimp [K1, lowerSimpleExtensionOfReal] at hCor33
  rcases hCor33 with ⟨_hLowerClosedOld, F, hF, _hUniqueF⟩
  rcases hF with ⟨hFrock, hFnoBot, _hFgraphClosed, hFpair,
      _hFdual, _hFprimalFormula, _hFdualFormula, _hFdom, _hFadjDom⟩
  have hK1_firstClosed : IsConcaveClosedInFirst K1 := by
    unfold IsConcaveClosedInFirst
    funext u
    funext xStar
    by_cases hxStar : xStar ∈ D
    · simpa [K1] using
        (helperForCorollary33_3_3_onDualDomain_lowerSimpleExtension_firstClosure_eq
          (C := C) (D := D) (K := J) hCclosed hJcont hxStar u).symm
    · simpa [K1] using
        (helperForCorollary33_3_3_offDualDomain_lowerSimpleExtension_firstClosure_eq
          (C := C) (D := D) (K := J) hCclosed hxStar u).symm
  have hK1eq : K1 = convexBifunctionPairing F := by
    funext u
    funext xStar
    exact hFpair u xStar
  rcases
      (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hFrock hFnoBot with
    ⟨hK1shapeRaw, hK1secondClosedRaw, _hSectionFormula⟩
  have hK1shape : IsConcaveConvexOn Set.univ Set.univ K1 := by
    simpa [hK1eq] using hK1shapeRaw
  have hK1secondClosed : IsConvexClosedInSecond K1 := by
    simpa [hK1eq] using hK1secondClosedRaw
  have hLowerIdentity :
      convexClosureInSecond (concaveClosureInFirst K1) = K1 := by
    exact
      helperForLemma33_0_43_lowerClosedIdentity_of_firstConcaveClosed_and_secondConvexClosed
        (K := K1) hK1_firstClosed hK1secondClosed
  have hLowerClosedNew : IsLowerClosed K1 := by
    refine ⟨by simpa [IsConcaveConvex] using hK1shape, ?_⟩
    intro h
    calc
      K1 = partialClosure₂ (partialClosure₁ K1) := by
        simpa [partialClosure₁, partialClosure₂] using hLowerIdentity.symm
      _ = lowerClosureConcaveConvex K1 h := by
        symm
        exact (helperForText_34_0_1_mixedClosure_formulas K1 h).1
  have hClosed : IsClosedSaddleFunction K1 :=
    lowerClosed_saddleFunction_isClosed hLowerClosedNew hStrongClosures hClosedNoBot
  have hDom1 : effectiveDomain₁ K1 = C :=
    helperForCorollary_37_6_2_effectiveDomain1_lowerSimpleExtensionOfReal_eq hDne J
  have hDom2 : effectiveDomain₂ K1 = D :=
    helperForCorollary_37_6_2_effectiveDomain2_lowerSimpleExtensionOfReal_eq hCne J
  have hProper : IsProperSaddleFunction K1 := by
    rw [IsProperSaddleFunction, saddleEffectiveDomain, hDom1, hDom2]
    intro hEmpty
    rcases hCne with ⟨u, hu⟩
    rcases hDne with ⟨v, hv⟩
    have hMem : (u, v) ∈ C ×ˢ D := by simp [hu, hv]
    simpa [hEmpty] using hMem
  exact ⟨by simpa [K1, lowerSimpleExtensionOfReal] using hClosed,
    by simpa [K1, lowerSimpleExtensionOfReal] using hProper⟩

/-- Helper for Corollary 37.6.2: any global saddle point of the lower simple extension of `J`
must lie in `C × D`. -/
lemma helperForCorollary_37_6_2_mem_constraints_of_isSaddlePoint_lowerSimpleExtensionOfReal
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hS :
      IsSaddlePoint (C := (Fin m → ℝ)) (D := (Fin n → ℝ))
        (lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal))) u v) :
    u ∈ C ∧ v ∈ D := by
  rcases hCne with ⟨u0, hu0⟩
  rcases hDne with ⟨v0, hv0⟩
  rcases hS with ⟨hLeft, hRight⟩
  have hu : u ∈ C := by
    by_contra huC
    by_cases hv : v ∈ D
    · have hImpossible :
          ¬ (((J u0 v : ℝ) : EReal) ≤ (⊥ : EReal)) := by
        simp
      exact hImpossible (by simpa [lowerSimpleExtension, hu0, hv, huC] using hLeft u0)
    · have hImpossible : ¬ ((⊤ : EReal) ≤ (⊥ : EReal)) := by
        simp
      exact hImpossible (by simpa [lowerSimpleExtension, hu0, hv, huC] using hLeft u0)
  have hv : v ∈ D := by
    by_contra hvD
    have hImpossible :
        ¬ ((⊤ : EReal) ≤ (((J u v0 : ℝ) : EReal))) := by
      simp
    exact hImpossible (by simpa [lowerSimpleExtension, hu, hvD, hv0] using hRight v0)
  exact ⟨hu, hv⟩

/-- Corollary 37.6.2: a continuous finite concave-convex kernel on nonempty closed bounded
convex sets has a saddle point on `C × D`. -/
theorem corollary37_6_2_continuousFiniteConcaveConvexOn_closedBoundedConvex_hasSaddlePoint
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (hCbdd : Bornology.IsBounded C) (hDbdd : Bornology.IsBounded D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hStrongClosures : Section34Text34_1_9StrongClosureQualification m n)
    (hClosedNoBot : ∀ L : SaddleFunction m n,
      IsClosedSaddleFunction L → HasNoBotValuesBifunction L)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (hQ : Section37Theorem37_2Qualification
      (lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal))))
    (hRepresentative : ∀ hClosed : IsClosedSaddleFunction
      (lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal))),
      Section37ClosedRepresentativeQualification
        (lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal))) hClosed)
    (hJcont : ContinuousOn (fun p : (Fin m → ℝ) × (Fin n → ℝ) => J p.1 p.2) (C ×ˢ D))
    (hJcc : IsConcaveConvexOn C D (fun u v => ((J u v : ℝ) : EReal))) :
    ∃ u : C, ∃ v : D,
      IsSaddlePoint (C := C) (D := D) (fun u v => ((J u.1 v.1 : ℝ) : EReal)) u v := by
  -- Extend the constrained real kernel to the ambient spaces so Theorem 37.6 applies directly.
  let K : SaddleFunction m n :=
    lowerSimpleExtension C D (fun u v => ((J u v : ℝ) : EReal))
  have hKclosedProper :
      IsClosedSaddleFunction K ∧ IsProperSaddleFunction K :=
    helperForCorollary_37_6_2_lowerSimpleExtensionOfReal_closed_proper
      (m := m) (n := n)
      hCclosed hDclosed hCconv hDconv hCne hDne hStrongClosures hClosedNoBot J hJcont hJcc
  -- The effective domains of the ambient extension are exactly the original constraint sets.
  have hDom1 : effectiveDomain₁ K = C := by
    simpa [K] using
      helperForCorollary_37_6_2_effectiveDomain1_lowerSimpleExtensionOfReal_eq
        (m := m) (n := n) (C := C) (D := D) hDne J
  have hDom2 : effectiveDomain₂ K = D := by
    simpa [K] using
      helperForCorollary_37_6_2_effectiveDomain2_lowerSimpleExtensionOfReal_eq
        (m := m) (n := n) (C := C) (D := D) hCne J
  have hKb1 : Bornology.IsBounded (effectiveDomain₁ K) := by
    simpa [hDom1] using hCbdd
  have hKb2 : Bornology.IsBounded (effectiveDomain₂ K) := by
    simpa [hDom2] using hDbdd
  rcases
      helperForCorollary_37_6_2_bounded_effectiveDomains_yield_theorem37_6_hypotheses
        (K := K) (hKclosed := hKclosedProper.1) (hKproper := hKclosedProper.2)
        (by simpa [K] using hQ) hKb1 hKb2 with
    ⟨hNoCommonSecond, hNoCommonFirst⟩
  -- Apply the ambient saddle-point theorem after transferring boundedness to the effective
  -- domains of the extension.
  rcases
      section37_theorem37_6
        (K := K) (hKclosed := hKclosedProper.1) (hKproper := hKclosedProper.2)
        (by simpa [K] using hQ)
        (by simpa [K] using hRepresentative hKclosedProper.1)
        (hNoCommonSecond := hNoCommonSecond) (hNoCommonFirst := hNoCommonFirst) with
    ⟨u, v, hSaddle⟩
  -- Any saddle point of the lower simple extension must in fact lie in the original
  -- constraint sets.
  have huv :
      u ∈ C ∧ v ∈ D :=
    helperForCorollary_37_6_2_mem_constraints_of_isSaddlePoint_lowerSimpleExtensionOfReal
      (m := m) (n := n) (C := C) (D := D) hCne hDne J hSaddle
  refine ⟨⟨u, huv.1⟩, ⟨v, huv.2⟩, ?_⟩
  rcases hSaddle with ⟨hLeft, hRight⟩
  constructor
  · intro u'
    -- Restrict the ambient left inequality back to the subtype kernel by evaluating the lower
    -- extension on admissible points.
    calc
      ((J u'.1 v : ℝ) : EReal) = K u'.1 v := by
        symm
        simpa [K] using
          helperForCorollary_37_6_2_lowerSimpleExtensionOfReal_agrees_on_subtypes
            (m := m) (n := n) (C := C) (D := D) J u' ⟨v, huv.2⟩
      _ ≤ K u v := hLeft u'.1
      _ = ((J u v : ℝ) : EReal) := by
        simpa [K] using
          helperForCorollary_37_6_2_lowerSimpleExtensionOfReal_agrees_on_subtypes
            (m := m) (n := n) (C := C) (D := D) J ⟨u, huv.1⟩ ⟨v, huv.2⟩
  · intro v'
    -- The right inequality restricts in exactly the same way on admissible points.
    calc
      ((J u v : ℝ) : EReal) = K u v := by
        symm
        simpa [K] using
          helperForCorollary_37_6_2_lowerSimpleExtensionOfReal_agrees_on_subtypes
            (m := m) (n := n) (C := C) (D := D) J ⟨u, huv.1⟩ ⟨v, huv.2⟩
      _ ≤ K u v'.1 := hRight v'.1
      _ = ((J u v'.1 : ℝ) : EReal) := by
        simpa [K] using
          helperForCorollary_37_6_2_lowerSimpleExtensionOfReal_agrees_on_subtypes
            (m := m) (n := n) (C := C) (D := D) J ⟨u, huv.1⟩ v'

end Section37
end Chap07

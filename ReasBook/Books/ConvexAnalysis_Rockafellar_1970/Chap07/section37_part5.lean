/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part4

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Theorem 37.2: negating a concave section produces the convex slice needed for
the second support-function formula. -/
lemma helperForTheorem_37_2_negatedFirstSlice_on_intrinsicInterior
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {v : Fin n → ℝ}
    (hv : v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)) :
    IsProperClosedConvexFunctionWithDomain (fun u => -K u v) (effectiveDomain₁ K) := by
  have hKcc : IsConcaveConvex K := hKclosed.1.1
  have hSliceData :=
    closed_concaveConvex_iff_relativeInterior_slice_conditions
      K hKproper hKcc hGlobal hKclosed
  have hConcSlice :
      IsProperClosedConcaveFunctionWithDomain (fun u => K u v) (effectiveDomain₁ K) :=
    hSliceData.2.2.2.1 v hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The first-variable slice is concave, so its negation is convex on all of `ℝ^m`.
    intro u₁ u₂ hu₁ hu₂ a b ha hb hab hu12
    have hJensen :
        (a : EReal) * K u₁ v + (b : EReal) * K u₂ v ≤
          K (a • u₁ + b • u₂) v :=
      hConcSlice.1 hu₁ hu₂ ha hb hab hu12
    have hTerm1_ne_top : (a : EReal) * K u₁ v ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inl ?_, Or.inl (EReal.coe_ne_top a), ?_⟩
      · exact_mod_cast ha
      · by_cases hZero : a = 0
        · left
          simp [hZero]
        · right
          exact hConcSlice.2.2.1 u₁
    have hTerm2_ne_top : (b : EReal) * K u₂ v ≠ ⊤ := by
      rw [EReal.mul_ne_top]
      refine ⟨Or.inl (EReal.coe_ne_bot b), Or.inl ?_, Or.inl (EReal.coe_ne_top b), ?_⟩
      · exact_mod_cast hb
      · by_cases hZero : b = 0
        · left
          simp [hZero]
        · right
          exact hConcSlice.2.2.1 u₂
    have hNegJensen :
        -(K (a • u₁ + b • u₂) v) ≤
          -((a : EReal) * K u₁ v + (b : EReal) * K u₂ v) := by
      simpa using hJensen
    have hNegAdd :
        -((a : EReal) * K u₁ v + (b : EReal) * K u₂ v) =
          -((a : EReal) * K u₁ v) - ((b : EReal) * K u₂ v) :=
      EReal.neg_add (Or.inr hTerm2_ne_top) (Or.inl hTerm1_ne_top)
    calc
      -(K (a • u₁ + b • u₂) v)
          ≤ -((a : EReal) * K u₁ v + (b : EReal) * K u₂ v) := hNegJensen
      _ = (a : EReal) * (-K u₁ v) + (b : EReal) * (-K u₂ v) := by
            simpa [sub_eq_add_neg] using hNegAdd
  · -- Concave-closedness converts to convex-closedness after a pointwise sign flip.
    exact
      (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed).1
        hConcSlice.2.1
  · -- The original slice avoids `⊤`, so the negated slice avoids `⊥`.
    intro u
    simpa [EReal.neg_eq_bot_iff] using hConcSlice.2.2.1 u
  · -- Negating swaps the concave and convex effective-domain conventions.
    ext u
    simpa [convexFunctionEffectiveDomain, concaveFunctionEffectiveDomain,
      lt_top_iff_ne_top, bot_lt_iff_ne_bot, EReal.neg_eq_top_iff]
      using congrArg (fun s => u ∈ s) hConcSlice.2.2.2

/-- Helper for Theorem 37.2: a proper saddle-function has a point in its first effective
domain. -/
lemma helperForTheorem_37_2_firstDomain_nonempty
    (K : SaddleFunction m n)
    (hKproper : IsProperSaddleFunction K) :
    (effectiveDomain₁ K).Nonempty := by
  -- Project any witness from the saddle effective domain to the first coordinate.
  have hSaddleNonempty : (saddleEffectiveDomain K).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hKproper
  rcases hSaddleNonempty with ⟨⟨u, _v⟩, huv⟩
  exact ⟨u, (Set.mem_prod.mp huv).1⟩

/-- Helper for Theorem 37.2: a proper saddle-function has a point in its second effective
domain. -/
lemma helperForTheorem_37_2_secondDomain_nonempty
    (K : SaddleFunction m n)
    (hKproper : IsProperSaddleFunction K) :
    (effectiveDomain₂ K).Nonempty := by
  -- Project the same saddle-domain witness to the second coordinate.
  have hSaddleNonempty : (saddleEffectiveDomain K).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hKproper
  rcases hSaddleNonempty with ⟨⟨_u, v⟩, huv⟩
  exact ⟨v, (Set.mem_prod.mp huv).2⟩

/-- Helper for Theorem 37.2: every relative-interior slice `K(u, ·)` is proper as a convex
function on the full ambient space. -/
lemma helperForTheorem_37_2_convexSlice_properOn_univ
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (K u) := by
  have hSlice :=
    helperForTheorem_37_2_convexSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu
  have hDomain :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u) = effectiveDomain₂ K := by
    -- The closed-slice theorem identifies the unrestricted effective domain with `dom₂ K`.
    simpa [convexFunctionEffectiveDomain, effectiveDomain_eq] using hSlice.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · -- Jensen convexity on `univ` is exactly the convex-function structure needed here.
    exact helperForTheorem_37_2_convexFunctionOn_univ_of_IsERealConvexOn hSlice.1
  · -- Properness needs one finite point, which comes from any point of `dom₂ K`.
    exact
      (nonempty_epigraph_iff_nonempty_effectiveDomain
        (S := (Set.univ : Set (Fin n → ℝ))) (f := K u)).2
        (by simpa [hDomain] using
          helperForTheorem_37_2_secondDomain_nonempty (K := K) hKproper)
  · -- The slice theorem already gives the required no-`⊥` property.
    intro x hx
    exact hSlice.2.2.1 x

/-- Helper for Theorem 37.2: each interior slice-conjugate domain is nonempty. -/
lemma helperForTheorem_37_2_sliceConjugateDomain_nonempty
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)) :
    (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))).Nonempty := by
  have hProperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u)) :=
    proper_fenchelConjugate_of_proper (n := n) (f := K u)
      (helperForTheorem_37_2_convexSlice_properOn_univ
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu)
  -- Properness of the Fenchel conjugate is equivalent to nonempty effective domain plus no `⊥`.
  exact
    (nonempty_epigraph_iff_nonempty_effectiveDomain
      (S := (Set.univ : Set (Fin n → ℝ))) (f := fenchelConjugate n (K u))).1
      hProperStar.2.1

/-- Helper for Theorem 37.2: each interior slice-conjugate domain is convex. -/
lemma helperForTheorem_37_2_sliceConjugateDomain_convex
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)) :
    Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))) := by
  have hProperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u)) :=
    proper_fenchelConjugate_of_proper (n := n) (f := K u)
      (helperForTheorem_37_2_convexSlice_properOn_univ
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu)
  -- The effective domain of any convex function on `univ` is convex.
  exact effectiveDomain_convex (S := Set.univ) (f := fenchelConjugate n (K u)) hProperStar.1

/-- Helper for Theorem 37.2: every relative-interior first slice `u ↦ -K(u, v)` is proper as a
convex function on the full ambient space. -/
lemma helperForTheorem_37_2_negatedFirstSlice_properOn_univ
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {v : Fin n → ℝ}
    (hv : v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun u => -K u v) := by
  have hSlice :=
    helperForTheorem_37_2_negatedFirstSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hv
  have hDomain :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun u => -K u v) = effectiveDomain₁ K := by
    -- The negated first-slice helper already records the full domain description.
    simpa [convexFunctionEffectiveDomain, effectiveDomain_eq] using hSlice.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · -- The negated first slice is convex on all of `ℝ^m`.
    exact helperForTheorem_37_2_convexFunctionOn_univ_of_IsERealConvexOn hSlice.1
  · -- Properness again reduces to exhibiting one point in the effective domain.
    exact
      (nonempty_epigraph_iff_nonempty_effectiveDomain
        (S := (Set.univ : Set (Fin m → ℝ))) (f := fun u => -K u v)).2
        (by simpa [hDomain] using
          helperForTheorem_37_2_firstDomain_nonempty (K := K) hKproper)
  · -- The helper already proves the pointwise no-`⊥` condition.
    intro u hu
    exact hSlice.2.2.1 u

/-- Helper for Theorem 37.2: each sign-twisted first-slice conjugate domain is nonempty. -/
lemma helperForTheorem_37_2_negatedFirstSliceConjugateDomain_nonempty
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {v : Fin n → ℝ}
    (hv : v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)) :
    (effectiveDomain (Set.univ : Set (Fin m → ℝ))
      (fenchelConjugate m (fun u => -K u v))).Nonempty := by
  have hProperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ))
        (fenchelConjugate m (fun u => -K u v)) :=
    proper_fenchelConjugate_of_proper (n := m) (f := fun u => -K u v)
      (helperForTheorem_37_2_negatedFirstSlice_properOn_univ
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hv)
  -- The conjugate of a proper convex slice is proper, hence has nonempty effective domain.
  exact
    (nonempty_epigraph_iff_nonempty_effectiveDomain
      (S := (Set.univ : Set (Fin m → ℝ))) (f := fenchelConjugate m (fun u => -K u v))).1
      hProperStar.2.1

/-- Helper for Theorem 37.2: each sign-twisted first-slice conjugate domain is convex. -/
lemma helperForTheorem_37_2_negatedFirstSliceConjugateDomain_convex
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {v : Fin n → ℝ}
    (hv : v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)) :
    Convex ℝ
      (effectiveDomain (Set.univ : Set (Fin m → ℝ))
        (fenchelConjugate m (fun u => -K u v))) := by
  have hProperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ))
        (fenchelConjugate m (fun u => -K u v)) :=
    proper_fenchelConjugate_of_proper (n := m) (f := fun u => -K u v)
      (helperForTheorem_37_2_negatedFirstSlice_properOn_univ
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hv)
  -- Convexity of the effective domain is inherited from convexity of the conjugate itself.
  exact
    effectiveDomain_convex (S := Set.univ)
      (f := fenchelConjugate m (fun u => -K u v)) hProperStar.1

/-- Helper for Theorem 37.2: any point where the representative slice `F u` is finite already
lies in the common second effective domain of the upper Section 37 conjugate. -/
lemma helperForTheorem_37_2_representativeSliceDomain_subset_upperSecondDomain
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (K : SaddleFunction m n)
    (hK : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (hFStar :
      IsClosedConvexBifunction
        (bifunctionInverse (section34ConcaveBifunctionAdjoint F)))
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ} :
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u) ⊆
      effectiveDomain₂ (fun uStar x => theorem37ValueInfSup K uStar x) := by
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hSection34FStar := section34_theorem34_2 FStar hFStar
  have hOmegaKernel :
      convexBifunctionClosedKernel FStar ∈ omegaClassOfConvexBifunction FStar :=
    hSection34FStar.2.2
  have hKernelGenerated :
      convexBifunctionClosedKernel FStar ∈
        EquivalenceClassGeneratedByConvexBifunction ⟨FStar, hFStar⟩ := by
    have hEquivKernel :
        convexBifunctionClosedKernel FStar ∈
          {L | saddleEquivalent L (convexBifunctionClosedKernel FStar)} := by
      rw [← hSection34FStar.2.1]
      exact hOmegaKernel
    simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel] using
      hEquivKernel
  have hSection37 :=
    section37_theorem37_1 F hF K hK (convexBifunctionClosedKernel FStar) hFStar
      hKernelGenerated hGlobal
  intro x hx uStar
  have hxFinite : F u x < (⊤ : EReal) := by
    simpa [effectiveDomain_eq] using hx
  have hTermFinite : (((finDot uStar u : ℝ) : EReal) + F u x) < (⊤ : EReal) := by
    exact EReal.add_lt_top (by simp) (lt_top_iff_ne_top.mp hxFinite)
  have hLe :
      theorem37ValueInfSup K uStar x ≤ (((finDot uStar u : ℝ) : EReal) + F u x) := by
    rw [hSection37.1 uStar x, infPairing]
    simpa [bifunctionInverse] using
      (iInf_le (fun u' : Fin m → ℝ => (((finDot uStar u' : ℝ) : EReal) + F u' x)) u)
  -- Use the witness `u` inside the infimum formula for the upper conjugate.
  exact lt_of_le_of_lt hLe (by simpa [bifunctionInverse] using hTermFinite)

/-- Helper for Theorem 37.2: the first effective domain of the canonical Section 34 kernel is
just the ordinary finite-parameter domain of the underlying convex bifunction. -/
lemma helperForTheorem_37_2_firstKernelDomain_eq_convexBifunctionEffectiveDomain
    (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    effectiveDomain₁ (convexBifunctionClosedKernel G) = convexBifunctionEffectiveDomain G := by
  ext u
  constructor
  · intro hu
    -- Evaluate the universal no-`⊥` condition at the zero dual vector and rewrite that single
    -- pairing section using the Section 33 effective-domain formula.
    have hu0 :
        u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (fun u' => -convexBifunctionPairing G u' (0 : Fin n → ℝ)) := by
      rw [effectiveDomain_eq]
      constructor
      · simp
      have hPairNeBot : convexBifunctionPairing G u (0 : Fin n → ℝ) ≠ (⊥ : EReal) := by
        simpa [convexBifunctionClosedKernel] using
          (bot_lt_iff_ne_bot.mp (hu (0 : Fin n → ℝ)))
      exact lt_top_iff_ne_top.2 (show -convexBifunctionPairing G u (0 : Fin n → ℝ) ≠ (⊤ : EReal) by
        simpa using hPairNeBot)
    rw [_root_.helperForCorollary33_2_1_negConvexPairingSection_effectiveDomain_eq
      (F := G) (0 : Fin n → ℝ)] at hu0
    simpa [convexBifunctionEffectiveDomain] using hu0
  · intro hu xStar
    -- The Section 33 domain identity is independent of `xStar`, so the same finite witness for
    -- `G u` keeps every conjugate value away from `⊥`.
    have hx :
        u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (fun u' => -convexBifunctionPairing G u' xStar) := by
      rw [_root_.helperForCorollary33_2_1_negConvexPairingSection_effectiveDomain_eq
        (F := G) xStar]
      simpa [convexBifunctionEffectiveDomain] using hu
    have hxlt : -convexBifunctionPairing G u xStar < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hx
    exact bot_lt_iff_ne_bot.mpr (by
      simpa [convexBifunctionClosedKernel] using (lt_top_iff_ne_top.mp hxlt))

/-- Helper for Theorem 37.2: the second effective domain of the canonical Section 34 kernel is
the ordinary effective domain of the Section 34 adjoint bifunction. -/
lemma helperForTheorem_37_2_secondKernelDomain_eq_concaveAdjointEffectiveDomain
    (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hG : IsClosedConvexBifunction G)
    (hQ : Section34Theorem34_2Qualification G) :
    effectiveDomain₂ (convexBifunctionClosedKernel G) =
      concaveBifunctionEffectiveDomain (section34ConcaveBifunctionAdjoint G) := by
  have hKernelEq :
      convexBifunctionClosedKernel G = section34ConcaveBifunctionAdjointPairing G :=
    hQ.adjointPairing_eq
  ext xStar
  constructor
  · intro hx
    -- Again it is enough to evaluate the universal no-`⊤` condition at one parameter and then
    -- invoke the Section 33 effective-domain formula for the adjoint pairing section.
    have hx0 :
        xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x' =>
            concaveBifunctionPairing (section34ConcaveBifunctionAdjoint G) x'
              (0 : Fin m → ℝ)) := by
      rw [effectiveDomain_eq]
      constructor
      · simp
      have hPoint : section34ConcaveBifunctionAdjointPairing G (0 : Fin m → ℝ) xStar < (⊤ : EReal) := by
        rw [← hKernelEq]
        exact hx (0 : Fin m → ℝ)
      simpa [section34ConcaveBifunctionAdjointPairing, concaveBifunctionPairing] using hPoint
    rw [_root_.helperForCorollary33_2_1_concavePairingSection_effectiveDomain_eq
      (m := n) (n := m) (F := section34ConcaveBifunctionAdjoint G) (0 : Fin m → ℝ)] at hx0
    simpa [concaveBifunctionEffectiveDomain, bot_lt_iff_ne_bot] using hx0
  · intro hx uStar
    -- The right-hand side is independent of the frozen parameter `uStar`, so every pairing
    -- section stays finite at `xStar`.
    have hxu :
        xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x' =>
            concaveBifunctionPairing (section34ConcaveBifunctionAdjoint G) x' uStar) := by
      rw [_root_.helperForCorollary33_2_1_concavePairingSection_effectiveDomain_eq
        (m := n) (n := m) (F := section34ConcaveBifunctionAdjoint G) uStar]
      simpa [concaveBifunctionEffectiveDomain, bot_lt_iff_ne_bot] using hx
    have hPairFinite :
        concaveBifunctionPairing (section34ConcaveBifunctionAdjoint G) xStar uStar < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hxu
    have hPoint : section34ConcaveBifunctionAdjointPairing G uStar xStar < (⊤ : EReal) := by
      simpa [section34ConcaveBifunctionAdjointPairing, concaveBifunctionPairing] using hPairFinite
    rw [hKernelEq]
    exact hPoint

/-- Helper for Theorem 37.2: the recovered dual inverse has adjoint equal to the inverse of the
original representative. -/
lemma helperForTheorem_37_2_dualInverseAdjoint_eq_originalInverse
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (hFStar :
      IsClosedConvexBifunction
        (bifunctionInverse (section34ConcaveBifunctionAdjoint F)))
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    section34ConcaveBifunctionAdjoint
        (bifunctionInverse (section34ConcaveBifunctionAdjoint F)) =
      bifunctionInverse F := by
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hDoubleRecovery :
      bifunctionInverse (section34ConcaveBifunctionAdjoint FStar) = F := by
    let FDouble := bifunctionInverse (section34ConcaveBifunctionAdjoint FStar)
    have hFDouble : IsClosedConvexBifunction FDouble :=
      helperForCorollary_37_1_2_dualAdjointInverse_isClosedConvex
        (F := FStar) (hF := hFStar) hGlobal
    have hPairEq :
        ∀ u xStar,
          convexBifunctionPairing FDouble u xStar = convexBifunctionPairing F u xStar := by
      intro u xStar
      -- Identify the doubled transform with the one-variable convex closure of the original
      -- pairing section, then collapse that closure because the original section is already
      -- convex-closed.
      have hClosure :
          convexBifunctionPairing FDouble u xStar =
            functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar := by
        simpa [FStar, FDouble] using
          helperForCorollary_37_1_1_upperRecoveredKernel_eq_functionConvexClosure
            (F := F) (hF := hF) hGlobal (u := u) (xStar := xStar)
      have hCollapse :
          functionConvexClosure (fun y => convexBifunctionPairing F u y) xStar =
            convexBifunctionPairing F u xStar :=
        helperForCorollary_37_1_1_originalKernelSlice_functionConvexClosure_eq_self
          (F := F) (hF := hF) (u := u) (xStar := xStar)
      exact hClosure.trans hCollapse
    have hRecoverDouble :=
      (closedSaddleFunctions_imageClosedBifunctions_correspondence (m := m) (n := n)).1
        FDouble hFDouble
    have hRecoverF :=
      (closedSaddleFunctions_imageClosedBifunctions_correspondence (m := m) (n := n)).1
        F hF
    -- Equality of the pairing sections forces equality of the recovered convex bifunctions.
    ext u x
    have hSectionFun :
        (fun y => convexBifunctionPairing FDouble u y) =
          (fun y => convexBifunctionPairing F u y) := by
      funext y
      exact hPairEq u y
    have hConjEq :
        convexConjugate (fun y => convexBifunctionPairing FDouble u y) x =
          convexConjugate (fun y => convexBifunctionPairing F u y) x := by
      exact congrArg (fun g => convexConjugate g x) hSectionFun
    calc
      FDouble u x = convexConjugate (fun y => convexBifunctionPairing FDouble u y) x := by
        symm
        simpa using hRecoverDouble.2.2 u x
      _ = convexConjugate (fun y => convexBifunctionPairing F u y) x := hConjEq
      _ = F u x := by
        simpa using hRecoverF.2.2 u x
  funext x uStar
  -- Evaluate the doubled-transform identity at `(uStar, x)` and unfold the inverse.
  have hPoint : bifunctionInverse (section34ConcaveBifunctionAdjoint FStar) uStar x = F uStar x :=
    congrArg (fun H => H uStar x) hDoubleRecovery
  simpa [FStar, bifunctionInverse] using congrArg Neg.neg hPoint

/-- Helper for Theorem 37.2: precomposing a function with negation transports the effective
domain by the same negation map. -/
lemma helperForTheorem_37_2_negPrecompose_effectiveDomain
    (h : (Fin m → ℝ) → EReal) :
    effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fun uStar => h (-uStar)) =
      Neg.neg ⁻¹' effectiveDomain (Set.univ : Set (Fin m → ℝ)) h := by
  ext uStar
  simp [effectiveDomain_eq]

/-- Helper for Theorem 37.2: negating the underlying set transports the support function by
negating its argument. -/
lemma helperForTheorem_37_2_supportFunctionEReal_negPreimage
    {k : ℕ} (C : Set (Fin k → ℝ)) (z : Fin k → ℝ) :
    supportFunctionEReal (Neg.neg ⁻¹' C) z = supportFunctionEReal C (-z) := by
  -- Unfold both support functions and transport each witness by the involution `x ↦ -x`.
  unfold supportFunctionEReal
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    refine le_sSup ?_
    refine ⟨-x, hx, ?_⟩
    simp [dotProduct_neg]
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    refine le_sSup ?_
    refine ⟨-x, by simpa using hx, ?_⟩
    simp [dotProduct_neg]

/-- Helper for Theorem 37.2: support functions are monotone under inclusion of the underlying
sets. -/
lemma helperForTheorem_37_2_supportFunctionEReal_mono_of_subset
    {k : ℕ} {A B : Set (Fin k → ℝ)} (hAB : A ⊆ B) (y : Fin k → ℝ) :
    supportFunctionEReal A y ≤ supportFunctionEReal B y := by
  -- Unfold the two support functions and push every witness from `A` into `B`.
  unfold supportFunctionEReal
  refine sSup_le ?_
  rintro r ⟨x, hxA, rfl⟩
  exact le_sSup ⟨x, hAB hxA, rfl⟩

/-- Helper for Theorem 37.2: each interior slice-conjugate domain is contained in the common
second dual domain `D*`. -/
lemma helperForTheorem_37_2_sliceConjugateDomain_subset_commonSecondDomain
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (_hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)) :
    let DStar : Set (Fin n → ℝ) :=
      effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u)) ⊆ DStar := by
  dsimp
  -- Recover the closed convex representative whose `u`-slice is exactly `(K u)^*`.
  rcases helperForCorollary_37_1_2_closedProperRepresentative K hKclosed hKproper hGlobal with
    ⟨F, hF, _, hKGenerated⟩
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hFStarClosed : IsClosedConvexBifunction FStar :=
    helperForCorollary_37_1_2_dualAdjointInverse_isClosedConvex (F := F) (hF := hF) hGlobal
  have hQ : Section34Theorem34_2Qualification F := hGlobal.qualification F hF
  have hSection34F := section34_theorem34_2_qualified F hF hQ
  have hOmega : K ∈ omegaClassOfConvexBifunction F := by
    rw [hSection34F.2.1]
    simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel] using
      hKGenerated
  rcases hSection34F.2.2.2.2 K hOmega with
    ⟨_, _, hOriginalDomainEq, hRecoverConv, _, _⟩
  have hSliceEq : fenchelConjugate n (K u) = F u := by
    funext x
    simpa [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate] using
      (hRecoverConv u x).symm
  have hLowerKernel :
      (fun uStar x => theorem37ValueSupInf K uStar x) = convexBifunctionClosedKernel FStar := by
    funext uStar x
    simpa [FStar, convexBifunctionClosedKernel] using
      helperForCorollary_37_1_2_lowerConjugate_eq_dualLowerKernel
        (F := F) (hF := hF) (K := K) (hK := hKGenerated) (hFStar := hFStarClosed)
        hGlobal uStar x
  have hUpperSecondDomainEq :
      effectiveDomain₂ (fun uStar x => theorem37ValueInfSup K uStar x) =
        effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x) := by
    -- Corollary 37.1.2 already identifies the upper and lower second effective domains.
    simpa using
      (helperForTheorem_37_2_canonicalCommonEffectiveDomains
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal).2.2.2.2.2
  intro x hx
  -- The slice of the recovered representative already sits in the upper dual domain, and the
  -- upper and lower dual domains coincide by Corollary 37.1.2.
  have hxF : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u) := by
    simpa [hSliceEq] using hx
  have hxUpper :
      x ∈ effectiveDomain₂ (fun uStar x => theorem37ValueInfSup K uStar x) :=
    helperForTheorem_37_2_representativeSliceDomain_subset_upperSecondDomain
      (F := F) (hF := hF) (K := K) (hK := hKGenerated) (hFStar := hFStarClosed)
      hGlobal hxF
  simpa [hUpperSecondDomainEq] using hxUpper

/-- Helper for Theorem 37.2: every relative-interior second slice has a nonempty convex
Fenchel-domain. -/
lemma helperForTheorem_37_2_sliceConjugateDomain_convex_nonempty
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)) :
    Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))) ∧
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))).Nonempty := by
  -- Repackage the new granular convexity and nonemptiness helpers for the slice dual domains.
  exact
    ⟨helperForTheorem_37_2_sliceConjugateDomain_convex
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu,
      helperForTheorem_37_2_sliceConjugateDomain_nonempty
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu⟩

/-- Helper for Theorem 37.2: every relative-interior first slice, after the sign flip used in the
textbook formula, has a nonempty convex Fenchel-domain. -/
lemma helperForTheorem_37_2_negatedSliceConjugateDomain_convex_nonempty
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {v : Fin n → ℝ}
    (hv : v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)) :
    Convex ℝ
        (effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (fenchelConjugate m (fun u => -K u v))) ∧
      (effectiveDomain (Set.univ : Set (Fin m → ℝ))
        (fenchelConjugate m (fun u => -K u v))).Nonempty := by
  -- The sign-twisted first-slice family now has separate convexity and nonemptiness helpers.
  exact
    ⟨helperForTheorem_37_2_negatedFirstSliceConjugateDomain_convex
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hv,
      helperForTheorem_37_2_negatedFirstSliceConjugateDomain_nonempty
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hv⟩

/-- Helper for Theorem 37.2: every relative-interior second slice contributes a lower bound for
the support of `D*`. -/
lemma helperForTheorem_37_2_fixedSliceSup_le_secondDualSupport
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K))
    (w : Fin n → ℝ) :
    let D : Set (Fin n → ℝ) := effectiveDomain₂ K
    let DStar : Set (Fin n → ℝ) :=
      effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)
    (⨆ v : {v // v ∈ D}, K u (v.1 + w) - K u v.1) ≤
      supportFunctionEReal DStar w := by
  dsimp
  have hSlice :=
    helperForTheorem_37_2_convexSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu
  have hDomain :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u) = effectiveDomain₂ K := by
    -- The closed slice theorem already identifies the fixed-slice effective domain with `D`.
    simpa [convexFunctionEffectiveDomain, effectiveDomain_eq] using hSlice.2.2.2
  have hProperSlice : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (K u) :=
    helperForTheorem_37_2_convexSlice_properOn_univ
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu
  have hLscSlice : LowerSemicontinuous (K u) := by
    have hRawLsc : LowerSemicontinuous (functionConvexClosure (K u)) := by
      simpa [functionConvexClosure] using
        helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := K u)
    -- Closedness of the slice collapses the closure back to the original function.
    simpa [hSlice.2.1.symm] using hRawLsc
  have hClosedSlice : ClosedConvexFunction (K u) := by
    refine ⟨?_, hLscSlice⟩
    exact helperForTheorem_37_2_convexFunctionOn_univ_of_IsERealConvexOn hSlice.1
  have hSupportEq :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))) =
        recessionFunction (K u) := by
    exact
      section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction
        (n := n) (f := K u) hClosedSlice hProperSlice
  have hDualSubset :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u)) ⊆
        effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x) :=
    helperForTheorem_37_2_sliceConjugateDomain_subset_commonSecondDomain
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu
  have hSliceSupport :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))) w =
        recessionFunction (K u) w := by
    -- Evaluate the Chapter 13 identity at the present direction `w`.
    exact congrArg (fun g => g w) hSupportEq
  have hSupportMono :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))) w ≤
        supportFunctionEReal (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w := by
    -- Support functions are monotone, so the slice dual domain gives a lower bound for `D*`.
    exact
      helperForTheorem_37_2_supportFunctionEReal_mono_of_subset
        hDualSubset w
  have hSet :
      {r : EReal | ∃ v ∈ effectiveDomain₂ K, r = K u (v + w) - K u v} =
        Set.range (fun v : {v // v ∈ effectiveDomain₂ K} => K u (v.1 + w) - K u v.1) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨v.1, v.2, rfl⟩
  have hFormula :
      (⨆ v : {v // v ∈ effectiveDomain₂ K}, K u (v.1 + w) - K u v.1) =
        recessionFunction (K u) w := by
    -- Rewrite the Chapter 13 recession function as the explicit indexed supremum over `D`.
    calc
      ⨆ v : {v // v ∈ effectiveDomain₂ K}, K u (v.1 + w) - K u v.1
          = sSup (Set.range
              (fun v : {v // v ∈ effectiveDomain₂ K} => K u (v.1 + w) - K u v.1)) := by
                rw [sSup_range]
      _ = sSup {r : EReal | ∃ v ∈ effectiveDomain₂ K, r = K u (v + w) - K u v} := by
            rw [← hSet]
      _ = recessionFunction (K u) w := by
            simp [recessionFunction, hDomain]
  -- Compare the explicit slice formula with the support function of `D*` through the slice dual
  -- domain and support monotonicity.
  calc
    ⨆ v : {v // v ∈ effectiveDomain₂ K}, K u (v.1 + w) - K u v.1
        = recessionFunction (K u) w := hFormula
    _ = supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))) w := by
            exact hSliceSupport.symm
    _ ≤ supportFunctionEReal
          (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w := hSupportMono

/-- Helper for Theorem 37.2: the full relative-interior supremum is always bounded above by the
support of `D*`. -/
lemma helperForTheorem_37_2_iSupInteriorSlices_le_secondDualSupport
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (w : Fin n → ℝ) :
    iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
      iSup (fun v : {v // v ∈ effectiveDomain₂ K} => K u.1 (v.1 + w) - K u.1 v.1)) ≤
      supportFunctionEReal
        (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w := by
  -- Push the bound proved for each fixed slice through the outer supremum over `ri C`.
  refine iSup_le ?_
  intro u
  exact
    helperForTheorem_37_2_fixedSliceSup_le_secondDualSupport
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal u.2 w

/-- Helper for Theorem 37.2: for any closed convex representative `F` of `K`, the common second
dual domain `D*` is exactly the union of the effective domains of the slices `F u`. -/
lemma helperForTheorem_37_2_secondDualDomain_eq_iUnion_representativeSliceDomains
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (K : SaddleFunction m n)
    (hK : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x) =
      ⋃ u : Fin m → ℝ, effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u) := by
  let FStar := bifunctionInverse (section34ConcaveBifunctionAdjoint F)
  have hFStar : IsClosedConvexBifunction FStar :=
    helperForCorollary_37_1_2_dualAdjointInverse_isClosedConvex (F := F) (hF := hF) hGlobal
  have hLowerKernel :
      (fun uStar x => theorem37ValueSupInf K uStar x) = convexBifunctionClosedKernel FStar := by
    funext uStar x
    -- Corollary 37.1.2 rewrites the lower conjugate as the canonical dual kernel `⟪F_* u*, x⟫`.
    simpa [FStar, convexBifunctionClosedKernel] using
      helperForCorollary_37_1_2_lowerConjugate_eq_dualLowerKernel
        (F := F) (hF := hF) (K := K) (hK := hK) (hFStar := hFStar)
        hGlobal uStar x
  have hDomainEq :
      effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x) =
        concaveBifunctionEffectiveDomain (section34ConcaveBifunctionAdjoint FStar) := by
    -- The second effective domain of the dual kernel is the effective domain of its Section 34
    -- adjoint.
    rw [hLowerKernel]
    exact helperForTheorem_37_2_secondKernelDomain_eq_concaveAdjointEffectiveDomain
      (G := FStar) (hG := hFStar) (hGlobal.qualification FStar hFStar)
  have hAdjointEq :
      section34ConcaveBifunctionAdjoint FStar = bifunctionInverse F :=
    helperForTheorem_37_2_dualInverseAdjoint_eq_originalInverse
      (F := F) (hF := hF) (hFStar := hFStar) hGlobal
  rw [hDomainEq, hAdjointEq]
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u, hu⟩
    -- Unfold the inverse slice pointwise: `⊥ < -F u x` is the same as `F u x < ⊤`.
    refine Set.mem_iUnion.mpr ⟨u, ?_⟩
    simpa [effectiveDomain_eq, concaveBifunctionEffectiveDomain, bifunctionInverse,
      bot_lt_iff_ne_bot, lt_top_iff_ne_top, EReal.neg_eq_bot_iff] using hu
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨u, hu⟩
    -- Conversely, any finite value of the representative slice produces a witness in the
    -- concave-adjoint effective domain.
    refine ⟨u, ?_⟩
    simpa [effectiveDomain_eq, concaveBifunctionEffectiveDomain, bifunctionInverse,
      bot_lt_iff_ne_bot, lt_top_iff_ne_top, EReal.neg_eq_bot_iff] using hu

/-- Helper for Theorem 37.2: the support function of a union is the supremum of the support
functions of the members. -/
lemma helperForTheorem_37_2_supportFunctionEReal_iUnion
    (C : (Fin m → ℝ) → Set (Fin n → ℝ)) (w : Fin n → ℝ) :
    supportFunctionEReal (⋃ u : Fin m → ℝ, C u) w =
      iSup (fun u : Fin m → ℝ => supportFunctionEReal (C u) w) := by
  -- Unfold the support function and split the witness set according to which slice contains the
  -- maximizing point.
  unfold supportFunctionEReal
  apply le_antisymm
  · refine sSup_le ?_
    rintro r ⟨x, hx, rfl⟩
    rcases Set.mem_iUnion.mp hx with ⟨u, hxu⟩
    exact le_iSup_of_le u (le_sSup ⟨x, hxu, rfl⟩)
  · refine iSup_le ?_
    intro u
    refine sSup_le ?_
    rintro r ⟨x, hx, rfl⟩
    exact le_sSup ⟨x, Set.mem_iUnion.mpr ⟨u, hx⟩, rfl⟩

/-- Helper for Theorem 37.2: the support of `D*` is the supremum of the support functions of the
representative slice domains. -/
lemma helperForTheorem_37_2_secondDualSupport_eq_iSupRepresentativeSliceSupports
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (K : SaddleFunction m n)
    (hK : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (w : Fin n → ℝ) :
    supportFunctionEReal
        (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w =
      iSup (fun u : Fin m → ℝ =>
        supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u)) w) := by
  -- First rewrite `D*` as the union of the representative slice domains, then move the support
  -- function across that union.
  rw [helperForTheorem_37_2_secondDualDomain_eq_iUnion_representativeSliceDomains
    (F := F) (hF := hF) (K := K) (hK := hK) hGlobal]
  exact helperForTheorem_37_2_supportFunctionEReal_iUnion
    (C := fun u : Fin m → ℝ => effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u)) w

/-- Helper for Theorem 37.2: on relative-interior first slices, the support of the recovered
representative domain is exactly the textbook supremum over `v ∈ D`. -/
lemma helperForTheorem_37_2_representativeInteriorSliceSupport_eq_primalSliceSup
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsClosedConvexBifunction F)
    (K : SaddleFunction m n)
    (hK : K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K))
    (w : Fin n → ℝ) :
    supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u)) w =
      iSup (fun v : {v // v ∈ effectiveDomain₂ K} => K u (v.1 + w) - K u v.1) := by
  have hQ : Section34Theorem34_2Qualification F := hGlobal.qualification F hF
  have hSection34F := section34_theorem34_2_qualified F hF hQ
  have hOmega : K ∈ omegaClassOfConvexBifunction F := by
    -- Convert generated-class membership back into the canonical `Ω(F)` language of Theorem 34.2.
    rw [hSection34F.2.1]
    simpa [EquivalenceClassGeneratedByConvexBifunction, convexBifunctionClosedKernel] using hK
  rcases hSection34F.2.2.2.2 K hOmega with ⟨_, _, _, hRecoverConv, _, _⟩
  have hSliceEq : fenchelConjugate n (K u) = F u := by
    -- On every fixed first slice, the recovered representative is exactly the convex conjugate.
    funext x
    simpa [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate] using
      (hRecoverConv u x).symm
  have hSlice :=
    helperForTheorem_37_2_convexSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu
  have hDomain :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u) = effectiveDomain₂ K := by
    -- Theorem 34.3 identifies the effective domain of the interior slice with the common set `D`.
    simpa [convexFunctionEffectiveDomain, effectiveDomain_eq] using hSlice.2.2.2
  have hProperSlice : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (K u) :=
    helperForTheorem_37_2_convexSlice_properOn_univ
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu
  have hLscSlice : LowerSemicontinuous (K u) := by
    have hRawLsc : LowerSemicontinuous (functionConvexClosure (K u)) := by
      simpa [functionConvexClosure] using
        helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := K u)
    -- Closedness of the interior slice collapses the convex closure back to the original function.
    simpa [hSlice.2.1.symm] using hRawLsc
  have hClosedSlice : ClosedConvexFunction (K u) := by
    -- Package the interior slice as a closed convex function so Chapter 13 applies directly.
    refine ⟨?_, hLscSlice⟩
    exact helperForTheorem_37_2_convexFunctionOn_univ_of_IsERealConvexOn hSlice.1
  have hSupportEq :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))) w =
        recessionFunction (K u) w := by
    -- Evaluate the Chapter 13 support/recession identity at the present direction `w`.
    exact congrArg (fun g => g w)
      (section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction
        (n := n) (f := K u) hClosedSlice hProperSlice)
  have hSet :
      {r : EReal | ∃ v ∈ effectiveDomain₂ K, r = K u (v + w) - K u v} =
        Set.range (fun v : {v // v ∈ effectiveDomain₂ K} => K u (v.1 + w) - K u v.1) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨v.1, v.2, rfl⟩
  have hFormula :
      (⨆ v : {v // v ∈ effectiveDomain₂ K}, K u (v.1 + w) - K u v.1) =
        recessionFunction (K u) w := by
    -- Rewrite the recession function as the explicit supremum over the common domain `D`.
    calc
      (⨆ v : {v // v ∈ effectiveDomain₂ K}, K u (v.1 + w) - K u v.1)
          = sSup (Set.range
              (fun v : {v // v ∈ effectiveDomain₂ K} => K u (v.1 + w) - K u v.1)) := by
                rw [sSup_range]
      _ = sSup {r : EReal | ∃ v ∈ effectiveDomain₂ K, r = K u (v + w) - K u v} := by
            rw [← hSet]
      _ = recessionFunction (K u) w := by
            simp [recessionFunction, hDomain]
  -- Replace the representative slice by the Fenchel conjugate of `K u`, then invoke the Chapter
  -- 13 support formula and the explicit recession-function supremum.
  calc
    supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u)) w
        = supportFunctionEReal
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (K u))) w := by
              rw [hSliceEq]
    _ = recessionFunction (K u) w := hSupportEq
    _ = iSup (fun v : {v // v ∈ effectiveDomain₂ K} => K u (v.1 + w) - K u v.1) := by
          exact hFormula.symm

/-- Boundary-generation qualification for Theorem 37.2: after choosing any closed convex
representative of `K`, the support supremum over all first-coordinate slices is already generated
by slices whose first coordinate lies in the relative interior of the common primal domain. -/
def Section37SecondDualBoundaryGeneration (K : SaddleFunction m n) : Prop :=
  ∀ (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hF : IsClosedConvexBifunction F),
    K ∈ EquivalenceClassGeneratedByConvexBifunction ⟨F, hF⟩ →
      ∀ w : Fin n → ℝ,
        iSup (fun u : Fin m → ℝ =>
            supportFunctionEReal
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u)) w) =
          iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
            supportFunctionEReal
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u.1)) w)

/-- Helper for Theorem 37.2: under explicit boundary generation, the support function of the
second common dual domain is the supremum of the second-family recession expressions over the
relative interior of `C`. -/
lemma helperForTheorem_37_2_secondDualSupport_formula
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (hBoundary : Section37SecondDualBoundaryGeneration K)
    (w : Fin n → ℝ) :
    supportFunctionEReal
        (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w =
      iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
        iSup (fun v : {v // v ∈ effectiveDomain₂ K} => K u.1 (v.1 + w) - K u.1 v.1)) := by
  rcases
      helperForCorollary_37_1_2_closedProperRepresentative K hKclosed hKproper hGlobal with
    ⟨F, hF, _hFproper, hKGenerated⟩
  calc
    supportFunctionEReal
          (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w =
        iSup (fun u : Fin m → ℝ =>
          supportFunctionEReal
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u)) w) :=
      helperForTheorem_37_2_secondDualSupport_eq_iSupRepresentativeSliceSupports
        F hF K hKGenerated hGlobal w
    _ = iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
          supportFunctionEReal
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u.1)) w) :=
      hBoundary F hF hKGenerated w
    _ = iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
          iSup (fun v : {v // v ∈ effectiveDomain₂ K} =>
            K u.1 (v.1 + w) - K u.1 v.1)) := by
      apply iSup_congr
      intro u
      exact helperForTheorem_37_2_representativeInteriorSliceSupport_eq_primalSliceSup
        F hF K hKGenerated hKclosed hKproper hGlobal u.2 w


end Section37
end Chap07

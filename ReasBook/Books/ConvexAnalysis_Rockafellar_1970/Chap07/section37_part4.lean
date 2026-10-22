/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part3

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Theorem 37.2: Corollary 37.1.2 already packages a common pair of coordinate
effective domains for the two Section 37 conjugates. -/
lemma helperForTheorem_37_2_commonEffectiveDomains
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    ∃ CStar : Set (Fin m → ℝ), ∃ DStar : Set (Fin n → ℝ),
      CStar.Nonempty ∧
        DStar.Nonempty ∧
        Convex ℝ CStar ∧
        Convex ℝ DStar ∧
        effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x) = CStar ∧
        effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x) = DStar ∧
        effectiveDomain₁ (fun uStar x => theorem37ValueInfSup K uStar x) = CStar ∧
        effectiveDomain₂ (fun uStar x => theorem37ValueInfSup K uStar x) = DStar := by
  -- Reuse the common-domain package already proved for Corollary 37.1.2.
  rcases corollary37_1_2_lower_upper_conjugates_structure K hKclosed hKproper hGlobal with
    ⟨CStar, DStar, hCnonempty, hDnonempty, hCconvex, hDconvex,
      hLower1, hLower2, hUpper1, hUpper2, _, _, _⟩
  exact ⟨CStar, DStar, hCnonempty, hDnonempty, hCconvex, hDconvex,
    hLower1, hLower2, hUpper1, hUpper2⟩

/-- Helper for Theorem 37.2: the common effective domains can be chosen canonically as the two
coordinate effective domains of the lower Section 37 conjugate. -/
lemma helperForTheorem_37_2_canonicalCommonEffectiveDomains
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    let CStar : Set (Fin m → ℝ) := effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)
    let DStar : Set (Fin n → ℝ) := effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)
    CStar.Nonempty ∧
      DStar.Nonempty ∧
      Convex ℝ CStar ∧
      Convex ℝ DStar ∧
      effectiveDomain₁ (fun uStar x => theorem37ValueInfSup K uStar x) = CStar ∧
      effectiveDomain₂ (fun uStar x => theorem37ValueInfSup K uStar x) = DStar := by
  -- Specialize the abstract common-domain package to the canonical lower-conjugate domains.
  dsimp
  rcases helperForTheorem_37_2_commonEffectiveDomains (K := K) hKclosed hKproper hGlobal with
    ⟨CStar, DStar, hCnonempty, hDnonempty, hCconvex, hDconvex,
      hLower1, hLower2, hUpper1, hUpper2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hLower1] using hCnonempty
  · simpa [hLower2] using hDnonempty
  · simpa [hLower1] using hCconvex
  · simpa [hLower2] using hDconvex
  · exact hUpper1.trans hLower1.symm
  · exact hUpper2.trans hLower2.symm

/-- Helper for Theorem 37.2: Jensen convexity on `Set.univ` upgrades directly to convexity of the
epigraph, hence to `ConvexFunctionOn Set.univ`. -/
lemma helperForTheorem_37_2_convexFunctionOn_univ_of_IsERealConvexOn
    {k : ℕ} {f : (Fin k → ℝ) → EReal}
    (hf : IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) f) :
    ConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) f := by
  simpa [ConvexFunction] using
    (helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction (f := f) hf)

/-- Helper for Theorem 37.2: properness of the saddle function already forces both primal
effective coordinate domains to be nonempty. -/
lemma helperForTheorem_37_2_effectiveDomains_nonempty
    (K : SaddleFunction m n)
    (hKproper : IsProperSaddleFunction K) :
    (effectiveDomain₁ K).Nonempty ∧ (effectiveDomain₂ K).Nonempty := by
  have hDomainNonempty : (saddleEffectiveDomain K).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hKproper
  rcases hDomainNonempty with ⟨⟨u, v⟩, huv⟩
  constructor
  · -- Project the properness witness onto the first coordinate to land in `dom₁ K`.
    refine ⟨u, ?_⟩
    simpa [saddleEffectiveDomain] using (Set.mem_prod.mp huv).1
  · -- Project the same witness onto the second coordinate to land in `dom₂ K`.
    refine ⟨v, ?_⟩
    simpa [saddleEffectiveDomain] using (Set.mem_prod.mp huv).2

/-- Helper for Theorem 37.2: the original effective domains `C` and `D` of a closed proper
concave-convex saddle-function have nonempty relative interiors. -/
lemma helperForTheorem_37_2_intrinsicInterior_nonempty
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K) :
    let C : Set (Fin m → ℝ) := effectiveDomain₁ K
    let D : Set (Fin n → ℝ) := effectiveDomain₂ K
    (intrinsicInterior ℝ C).Nonempty ∧
      (intrinsicInterior ℝ D).Nonempty := by
  let C : Set (Fin m → ℝ) := effectiveDomain₁ K
  let D : Set (Fin n → ℝ) := effectiveDomain₂ K
  have hKcc : IsConcaveConvex K := hKclosed.1.1
  have hDomainsConvex := section34_text_34_1_6 (K := K) hKcc
  have hEffectiveDomainsNonempty :=
    helperForTheorem_37_2_effectiveDomains_nonempty (K := K) hKproper
  have hCnonempty : C.Nonempty := by
    -- Rewrite the packaged first-coordinate nonemptiness into the local name `C`.
    simpa [C] using hEffectiveDomainsNonempty.1
  have hDnonempty : D.Nonempty := by
    -- Rewrite the packaged second-coordinate nonemptiness into the local name `D`.
    simpa [D] using hEffectiveDomainsNonempty.2
  refine ⟨?_, ?_⟩
  · simpa [C] using (intrinsicInterior_nonempty (s := C) (by simpa [C] using hDomainsConvex.1)).2
      hCnonempty
  · simpa [D] using
      (intrinsicInterior_nonempty (s := D) (by simpa [D] using hDomainsConvex.2.1)).2 hDnonempty

/-- Helper for Theorem 37.2: every `u` in `ri C` yields a closed proper convex slice
`K(u, ·)` with effective domain exactly `D`. -/
lemma helperForTheorem_37_2_convexSlice_on_intrinsicInterior
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)) :
    IsProperClosedConvexFunctionWithDomain (K u) (effectiveDomain₂ K) := by
  have hKcc : IsConcaveConvex K := hKclosed.1.1
  have hSliceData :=
    closed_concaveConvex_iff_relativeInterior_slice_conditions
      K hKproper hKcc hGlobal hKclosed
  -- Apply the closed-slice characterization directly at the requested relative-interior point.
  exact hSliceData.1 u hu

/-- Helper for Theorem 37.2: once `u ∈ ri C`, the unrestricted effective domain of the convex
slice `K(u, ·)` is exactly the second coordinate domain `D`. -/
lemma helperForTheorem_37_2_convexSlice_effectiveDomain_eq
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u) = effectiveDomain₂ K := by
  have hSlice :=
    helperForTheorem_37_2_convexSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu
  -- The slice theorem already records the ambient-space effective domain description.
  simpa [convexFunctionEffectiveDomain, effectiveDomain_eq] using hSlice.2.2.2

/-- Helper for Theorem 37.2: every interior convex slice `K(u, ·)` has a finite point, so its
ambient-space effective domain is nonempty. -/
lemma helperForTheorem_37_2_convexSlice_effectiveDomain_nonempty
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {u : Fin m → ℝ}
    (hu : u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)) :
    (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u)).Nonempty := by
  have hDnonempty :
      (effectiveDomain₂ K).Nonempty :=
    helperForTheorem_37_2_effectiveDomains_nonempty (K := K) hKproper |>.2
  -- Rewrite the nonempty second-coordinate domain through the slice-domain identification.
  simpa [helperForTheorem_37_2_convexSlice_effectiveDomain_eq
    (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hu] using hDnonempty

end Section37
end Chap07

/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part18

section Chap07
section Section34

open Set

section SaddleAmbient

variable {m n : ℕ}

/-- A concave-convex saddle-function is an admissible extension of `J` from `C × D` when it
agrees with `J` on `C × D`, takes the upper-simple-extension value `⊤` on `C × Dᶜ`, and takes
the lower-simple-extension value `⊥` on `Cᶜ × D`. -/
def IsAdmissibleConcaveConvexExtension
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (L : SaddleFunction m n) : Prop :=
  IsConcaveConvex L ∧
    (∀ u ∈ C, ∀ v ∈ D, L u v = ((J u v : ℝ) : EReal)) ∧
    (∀ u ∈ C, ∀ v ∉ D, L u v = (⊤ : EReal)) ∧
    ∀ u ∉ C, ∀ v ∈ D, L u v = (⊥ : EReal)

/-- The class of all admissible concave-convex extensions of `J` from `C × D` to
`ℝ^m × ℝ^n`. -/
def admissibleConcaveConvexExtensionClass
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) : Set (SaddleFunction m n) :=
  {L | IsAdmissibleConcaveConvexExtension C D J L}

/-- An admissible extension lies pointwise above the lower simple extension. -/
lemma lowerSimpleExtension_le_of_isAdmissibleConcaveConvexExtension
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {L : SaddleFunction m n}
    (hL : IsAdmissibleConcaveConvexExtension C D J L) :
    let JE : SaddleFunction m n := fun u v => ((J u v : ℝ) : EReal)
    lowerSimpleExtension C D JE ≤ L := by
  intro JE u v
  rcases hL with ⟨_hcc, hOn, hTop, _hBot⟩
  by_cases hu : u ∈ C
  · by_cases hv : v ∈ D
    · simpa [JE, lowerSimpleExtension, hu, hv] using le_of_eq (hOn u hu v hv).symm
    · simpa [JE, lowerSimpleExtension, hu, hv] using le_of_eq (hTop u hu v hv).symm
  · simp [lowerSimpleExtension, hu]

/-- An admissible extension lies pointwise below the upper simple extension. -/
lemma le_upperSimpleExtension_of_isAdmissibleConcaveConvexExtension
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {L : SaddleFunction m n}
    (hL : IsAdmissibleConcaveConvexExtension C D J L) :
    let JE : SaddleFunction m n := fun u v => ((J u v : ℝ) : EReal)
    L ≤ upperSimpleExtension C D JE := by
  intro JE u v
  rcases hL with ⟨_hcc, hOn, _hTop, hBot⟩
  by_cases hv : v ∈ D
  · by_cases hu : u ∈ C
    · simpa [JE, upperSimpleExtension, hu, hv] using le_of_eq (hOn u hu v hv)
    · simpa [JE, upperSimpleExtension, hu, hv] using le_of_eq (hBot u hu v hv)
  · simp [upperSimpleExtension, hv]

/-- The admissible-extension side conditions are equivalent to lying between the lower and upper
simple extensions of the `EReal`-valued kernel associated to `J`. -/
lemma isAdmissibleConcaveConvexExtension_iff_interval
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    {L : SaddleFunction m n} :
    IsAdmissibleConcaveConvexExtension C D J L ↔
      let JE : SaddleFunction m n := fun u v => ((J u v : ℝ) : EReal)
      IsConcaveConvex L ∧
        lowerSimpleExtension C D JE ≤ L ∧
        L ≤ upperSimpleExtension C D JE := by
  constructor
  · intro hL
    refine ⟨hL.1, ?_, ?_⟩
    · exact lowerSimpleExtension_le_of_isAdmissibleConcaveConvexExtension hL
    · exact le_upperSimpleExtension_of_isAdmissibleConcaveConvexExtension hL
  · intro hL
    rcases hL with ⟨hcc, hLower, hUpper⟩
    refine ⟨hcc, ?_, ?_, ?_⟩
    · intro u hu v hv
      have hLe : ((J u v : ℝ) : EReal) ≤ L u v := by
        simpa [lowerSimpleExtension, hu, hv] using hLower u v
      have hGe : L u v ≤ ((J u v : ℝ) : EReal) := by
        simpa [upperSimpleExtension, hu, hv] using hUpper u v
      exact le_antisymm hGe hLe
    · intro u hu v hv
      have hTopLe : (⊤ : EReal) ≤ L u v := by
        simpa [lowerSimpleExtension, hu, hv] using hLower u v
      exact top_le_iff.mp hTopLe
    · intro u hu v hv
      have hLeBot : L u v ≤ (⊥ : EReal) := by
        simpa [upperSimpleExtension, hu, hv] using hUpper u v
      exact le_bot_iff.mp hLeBot

/-- The admissible-extension class is exactly the interval between the lower and upper simple
extensions inside the concave-convex functions. -/
lemma admissibleConcaveConvexExtensionClass_eq_interval
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) :
    let JE : SaddleFunction m n := fun u v => ((J u v : ℝ) : EReal)
    admissibleConcaveConvexExtensionClass C D J =
      {L | IsConcaveConvex L ∧
          lowerSimpleExtension C D JE ≤ L ∧
          L ≤ upperSimpleExtension C D JE} := by
  intro JE
  ext L
  change IsAdmissibleConcaveConvexExtension C D J L ↔
    (IsConcaveConvex L ∧
      lowerSimpleExtension C D JE ≤ L ∧
      L ≤ upperSimpleExtension C D JE)
  exact isAdmissibleConcaveConvexExtension_iff_interval

-- Proof sketch: rewrite the admissible class as the interval between the lower and upper simple
-- extensions, then keep only the part of Corollary 34.2.4 that survives the corrected Section 34
-- pipeline. In the present formalization, the full "closed equivalence class" package is too
-- strong: what is stable is that the lower simple extension is itself an admissible closed proper
-- representative, is the least admissible member, and every admissible member stays below the
-- upper simple extension.
/-- Corrected formal version of Corollary 34.2.4: if `C` and `D` are nonempty closed convex sets
and `J` is a finite continuous concave-convex function on `C × D`, then the lower simple
extension is an admissible closed proper representative of `J`; it is the least member of the
admissible interval class, and every admissible member is pointwise bounded above by the upper
simple extension. The stronger theorem-level packaging of the whole admissible class as a closed
concave-convex equivalence class is deferred. -/
theorem concaveConvexExtensionClass_is_proper_closed_saddle_equivalenceClass
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hStrongClosures : Section34Text34_1_9StrongClosureQualification m n)
    (hClosedNoBot :
      ∀ L : SaddleFunction m n, IsClosedSaddleFunction L → HasNoBotValuesBifunction L)
    (J : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (hJcont : ContinuousOn (fun p : (Fin m → ℝ) × (Fin n → ℝ) => J p.1 p.2) (C ×ˢ D))
    (hJcc : IsConcaveConvexOn C D (fun u v => ((J u v : ℝ) : EReal))) :
    let JE : SaddleFunction m n := fun u v => ((J u v : ℝ) : EReal)
    let Ω : Set (SaddleFunction m n) := admissibleConcaveConvexExtensionClass C D J
    lowerSimpleExtension C D JE ∈ Ω ∧
      (∀ L ∈ Ω, lowerSimpleExtension C D JE ≤ L) ∧
      (∀ L ∈ Ω, L ≤ upperSimpleExtension C D JE) ∧
      IsProperSaddleFunction (lowerSimpleExtension C D JE) ∧
      IsClosedSaddleFunction (lowerSimpleExtension C D JE) := by
  intro JE Ω
  let K1 : SaddleFunction m n := lowerSimpleExtensionOfReal C D J
  have hCor33 :=
    «Corollary33.3.3» (C := C) (D := D) (K := J)
      hCne hDne hCclosed hDclosed hCconv hDconv hJcont hJcc
  dsimp [K1, lowerSimpleExtensionOfReal, upperSimpleExtensionOfReal] at hCor33
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
  have hLowerClosed : IsClosedSaddleFunction K1 :=
    lowerClosed_saddleFunction_isClosed hLowerClosedNew hStrongClosures hClosedNoBot
  have hJfinite :
      ∀ u ∈ C, ∀ v ∈ D, (⊥ : EReal) < JE u v ∧ JE u v < (⊤ : EReal) := by
    intro u hu v hv
    simp [JE]
  have hLowerProper : IsProperSaddleFunction (lowerSimpleExtension C D JE) := by
    simpa [JE, K1, lowerSimpleExtensionOfReal, erealOfRealBifunction] using
      helperForText_34_1_7_lowerSimpleExtension_isProper
        (C := C) (D := D) hCne hDne JE hJfinite
  have hLowerCC : IsConcaveConvex (lowerSimpleExtension C D JE) := by
    simpa [JE, K1, lowerSimpleExtensionOfReal, erealOfRealBifunction, IsConcaveConvex] using
      hLowerClosedNew.1
  have hLowerLeUpper : lowerSimpleExtension C D JE ≤ upperSimpleExtension C D JE := by
    intro u v
    simpa [JE, lowerSimpleExtensionOfReal, upperSimpleExtensionOfReal, erealOfRealBifunction] using
      helperForCorollary33_3_3_lowerSimpleExtension_le_upperSimpleExtension
        (C := C) (D := D) (K := JE) u v
  have hLowerInOmega : lowerSimpleExtension C D JE ∈ Ω := by
    change IsAdmissibleConcaveConvexExtension C D J (lowerSimpleExtension C D JE)
    exact (isAdmissibleConcaveConvexExtension_iff_interval (C := C) (D := D)
      (J := J) (L := lowerSimpleExtension C D JE)).2
      ⟨hLowerCC, le_rfl, hLowerLeUpper⟩
  have hLowerLeast : ∀ L ∈ Ω, lowerSimpleExtension C D JE ≤ L := by
    intro L hL
    exact ((isAdmissibleConcaveConvexExtension_iff_interval (C := C) (D := D)
      (J := J) (L := L)).1 hL).2.1
  have hUpperBound : ∀ L ∈ Ω, L ≤ upperSimpleExtension C D JE := by
    intro L hL
    exact ((isAdmissibleConcaveConvexExtension_iff_interval (C := C) (D := D)
      (J := J) (L := L)).1 hL).2.2
  refine ⟨hLowerInOmega, hLowerLeast, hUpperBound, hLowerProper, ?_⟩
  simpa [JE, K1, lowerSimpleExtensionOfReal, erealOfRealBifunction] using hLowerClosed

end SaddleAmbient

end Section34
end Chap07

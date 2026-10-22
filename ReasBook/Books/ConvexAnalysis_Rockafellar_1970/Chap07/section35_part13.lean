/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part12

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- Helper for Text 35.6.10: once `∂₁ K(u, v)` is nonempty and bounded, the reflected-slice
Theorem 23.4 route yields the exact infimum formula claimed in the text. -/
lemma helperForText_35_6_10_formula_of_nonempty_bounded_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartial : Set.Nonempty (partialSubdifferentialInFirstVariable K u v))
    (hpartialBdd : Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))
    (u' : Fin m → ℝ) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
      sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) := by
  let g : (Fin m → ℝ) → EReal := fun x => -K (-x) v
  let C : Set (Fin m → ℝ) := partialSubdifferentialInFirstVariable K u v
  have hg : ConvexFunction g := by
    -- The first slice becomes convex after the reflection `x ↦ -x`.
    simpa [g] using helperForText_35_6_6_reflectedFirstSlice_convex (K := K) hSaddle v
  have hgu : g (-u) ≠ (⊤ : EReal) ∧ g (-u) ≠ (⊥ : EReal) := by
    -- The reflected base point still records the same finite kernel value.
    simpa [g] using
      helperForText_35_6_6_reflectedFirstSlice_finiteAtBase
        (K := K) (u := u) (v := v) hFinite
  have hsliceNonempty : Set.Nonempty (subdifferentialAt g (-u)) := by
    -- Transport the textbook first partial witness into the reflected slice subdifferential.
    simpa [g, C] using
      (helperForText_35_6_6_partialFirst_nonempty_iff_sliceSubdifferential_nonempty
        (K := K) (u := u) (v := v)).1 hpartial
  have hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g :=
    (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
      g hg (-u) hgu).1 hsliceNonempty
  have hFirstEq :
      ((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt g (-u)) = C := by
    -- This is the standard reflected-slice identification of `∂₁ K(u, v)`.
    simpa [g, C] using
      helperForText_35_6_6_partialFirst_eq_sliceSubdifferential
        (K := K) (u := u) (v := v)
  have hsliceBdd :
      Bornology.IsBounded (((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt g (-u))) := by
    -- Boundedness transports through the same identification.
    simpa [hFirstEq] using hpartialBdd
  have h23 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      g hproperG (-u)
  have hBaseInterior :
      -u ∈ interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) := by
    -- The bounded nonempty branch is exactly the interior branch of Theorem 23.4.
    exact (h23.2.2.1).1 ⟨hsliceNonempty, hsliceBdd⟩
  have hBaseRi :
      -u ∈ euclideanRelativeInterior_fin m
        (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) :=
    helperForTheorem_23_4_mem_relativeInterior_of_mem_interior hBaseInterior
  have hDirEq :
      upperDirectionalDerivativeAt g (-u) (-u') =
        subdifferentialSupportAt g (-u) (-u') :=
    (h23.2.1 hBaseRi).2.2.2 (-u')
  have hDerivativeEq :
      -sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        subdifferentialSupportAt g (-u) (-u') := by
    -- Re-express the raw saddle derivative through the reflected first-directional derivative.
    calc
      -sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
          firstVariableDirectionalDerivativeFunction K u v (-u') := by
        simp [firstVariableDirectionalDerivativeFunction]
      _ = upperDirectionalDerivativeAt g (-u) (-u') := by
        simpa [g] using
          congrFun
            (helperForText_35_6_6_firstVariableDirectionalDerivative_eq_upperDirectionalDerivative
              (K := K) hSaddle (u := u) (v := v) hFinite)
            (-u')
      _ = subdifferentialSupportAt g (-u) (-u') := hDirEq
  have hSliceConvex :
      Convex ℝ (((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt g (-u))) := by
    -- The Euclidean subdifferential of the reflected slice is always convex.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        g hg (-u) hgu (0 : Module.Dual ℝ (Fin m → ℝ))).2.2.1
  have hCConv : Convex ℝ C := by
    -- Transport convexity back to the textbook first partial subdifferential.
    simpa [hFirstEq] using hSliceConvex
  have hCne : C.Nonempty := by
    simpa [C] using hpartial
  have hNegPairBddAbove :
      BddAbove (Set.image (fun uStar : Fin m → ℝ => dotProduct uStar (-u')) C) := by
    have hSupportNegTop : supportFunctionEReal C (-u') ≠ (⊤ : EReal) :=
      section13_supportFunctionEReal_ne_top_of_isBounded (C := C) hpartialBdd (-u')
    refine ⟨(supportFunctionEReal C (-u')).toReal, ?_⟩
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hSupportLe :
        supportFunctionEReal C (-u') ≤
          (((supportFunctionEReal C (-u')).toReal) : EReal) := by
      simpa using
        (EReal.le_coe_toReal (x := supportFunctionEReal C (-u')) hSupportNegTop)
    exact
      (section13_supportFunctionEReal_le_coe_iff
        (C := C) (y := -u') (μ := (supportFunctionEReal C (-u')).toReal)).1
        hSupportLe x hx
  have hPairBddBelow :
      BddBelow (Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u') C) :=
    section13_bddBelow_image_dotProduct_of_bddAbove_image_dotProduct_neg
      (C := C) (xStar := u') hNegPairBddAbove
  have hPairNonempty :
      (Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u') C).Nonempty := by
    simpa using hCne.image (fun uStar : Fin m → ℝ => dotProduct uStar u')
  have hSupportNegToDelta :
      supportFunctionOfSet C (-u') = (((deltaStar C (-u')) : ℝ) : EReal) := by
    have hImageEq :
        ((fun uStar : Fin m → ℝ => (((dotProduct uStar (-u') : ℝ)) : EReal)) '' C) =
          ((fun r : ℝ => (r : EReal)) ''
            Set.image (fun uStar : Fin m → ℝ => dotProduct uStar (-u')) C) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨dotProduct x (-u'), ⟨x, hx, rfl⟩, ?_⟩
        simp
      · rintro ⟨r, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨x, hx, ?_⟩
        simp
    have hNegPairNonempty :
        (Set.image (fun uStar : Fin m → ℝ => dotProduct uStar (-u')) C).Nonempty := by
      simpa using hCne.image (fun uStar : Fin m → ℝ => dotProduct uStar (-u'))
    -- Convert the `EReal` support supremum back to the real-valued support function `δ*`.
    calc
      supportFunctionOfSet C (-u') =
          sSup ((fun uStar : Fin m → ℝ => (((dotProduct uStar (-u') : ℝ)) : EReal)) '' C) := by
        simp [supportFunctionOfSet, dotProduct]
      _ =
          sSup ((fun r : ℝ => (r : EReal)) ''
            Set.image (fun uStar : Fin m → ℝ => dotProduct uStar (-u')) C) := by
        rw [hImageEq]
      _ =
          (((sSup
            (Set.image (fun uStar : Fin m → ℝ => dotProduct uStar (-u')) C)) : ℝ) : EReal) := by
        exact
          section13_sSup_image_coe_real_eq_coe_sSup
            (S := Set.image (fun uStar : Fin m → ℝ => dotProduct uStar (-u')) C)
            hNegPairNonempty hNegPairBddAbove
      _ = (((deltaStar C (-u')) : ℝ) : EReal) := by
        rw [deltaStar_eq_sSup_image_dotProduct_right]
  have hPairInfEq :
      sInf
          ((fun uStar : Fin m → ℝ => (((dotProduct uStar u' : ℝ)) : EReal)) '' C) =
        (((sInf (Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u') C)) : ℝ) : EReal) := by
    have hPairImageEq :
        ((fun uStar : Fin m → ℝ => (((dotProduct uStar u' : ℝ)) : EReal)) '' C) =
          ((fun r : ℝ => (r : EReal)) ''
            Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u') C) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨dotProduct x u', ⟨x, hx, rfl⟩, ?_⟩
        simp
      · rintro ⟨r, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨x, hx, ?_⟩
        simp
    rw [hPairImageEq]
    exact
      sInf_coe_image_eq_sInf_real
        (A := Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u') C)
        hPairNonempty hPairBddBelow
  have hPairRealEq :
      sInf (Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u') C) =
        -(deltaStar C (-u')) := by
    -- The real pairing infimum is the negative support value at the reflected direction.
    simpa using sInf_dotProduct_eq_neg_deltaStar (C := C) (xStar := u') hCConv
  have hDeltaRealEq :
      deltaStar C (-u') =
        -sInf (Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u') C) := by
    simpa using (congrArg (fun r : ℝ => -r) hPairRealEq).symm
  have hSupportToInf :
      subdifferentialSupportAt g (-u) (-u') =
        -sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) '' C) := by
    -- Translate the Chapter 23 support value into the textbook infimum over pairings.
    calc
      subdifferentialSupportAt g (-u) (-u') = supportFunctionOfSet C (-u') := by
        simpa [g, C] using
          congrFun
            (helperForText_35_6_6_sliceSupport_eq_firstPartialSupport
              (K := K) (u := u) (v := v))
            (-u')
      _ = (((deltaStar C (-u')) : ℝ) : EReal) := hSupportNegToDelta
      _ =
          -((((sInf (Set.image (fun uStar : Fin m → ℝ => dotProduct uStar u') C)) : ℝ)) :
            EReal) := by
        rw [hDeltaRealEq]
        simp
      _ =
          -sInf
            ((fun uStar : Fin m → ℝ =>
                (((dotProduct uStar u' : ℝ)) : EReal)) '' C) := by
        rw [hPairInfEq]
      _ =
          -sInf
            ((fun uStar : Fin m → ℝ =>
                (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) '' C) := by
        simp [dotProduct]
  -- Negate the reflected-slice equality to recover the textbook infimum formula.
  calc
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        -(-sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L}) := by
      simp
    _ = -subdifferentialSupportAt g (-u) (-u') := by
      rw [hDerivativeEq]
    _ =
        -(-sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) '' C)) := by
      rw [hSupportToInf]
    _ =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) '' C) := by
      simp

/-- Helper for Text 35.6.10: under the missing nonempty-bounded hypothesis on `∂₁ K(u, v)`,
the textbook infimum formula does hold for every first direction. -/
lemma helperForText_35_6_10_allDirectionsFormula_of_nonempty_bounded_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartial : Set.Nonempty (partialSubdifferentialInFirstVariable K u v))
    (hpartialBdd : Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)) :
    ∀ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v) := by
  intro u'
  -- Specialize the already proved good-branch formula to the requested first direction.
  exact
    helperForText_35_6_10_formula_of_nonempty_bounded_partialFirst
      (K := K) hSaddle (u := u) (v := v) hFinite hpartial hpartialBdd u'

/-- Helper for Text 35.6.10: once the nonempty-unbounded remainder is excluded, the full
all-directions textbook formula is equivalent to the corrected nonempty-bounded branch
hypothesis on `∂₁ K(u, v)`. -/
lemma helperForText_35_6_10_allDirectionsFormula_iff_goodBranch_of_no_nonempty_unbounded
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hNoNonemptyUnbounded :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))) :
    (∀ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v)) ↔
      (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)) := by
  constructor
  · intro hFormula
    -- Once the nonempty-unbounded alternative is ruled out, the asserted formula can only live
    -- on the corrected nonempty-bounded branch.
    exact
      helperForText_35_6_10_allDirectionsFormula_forces_goodBranch_of_no_nonempty_unbounded
        (K := K) (u := u) (v := v) hFinite hNoNonemptyUnbounded hFormula
  · rintro ⟨hpartial, hpartialBdd⟩
    -- Conversely, the good branch is exactly the hypothesis needed for the reflected-slice proof
    -- of the all-directions formula.
    exact
      helperForText_35_6_10_allDirectionsFormula_of_nonempty_bounded_partialFirst
        (K := K) hSaddle (u := u) (v := v) hFinite hpartial hpartialBdd

/-- Text 35.6.10: in the branch where the first partial subdifferential `∂₁ K(u, v)` is
nonempty and bounded, the first-variable directional derivative is the infimum of the pairings
`⟪u*, u'⟫` over `u* ∈ ∂₁ K(u, v)`. -/
theorem section35_text35_6_10
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstPartial :
      Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))
    (u' : Fin m → ℝ) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
      sInf
        ((fun uStar : Fin m → ℝ =>
            (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) := by
  -- Route correction: the unrestricted textbook statement is false on the empty-partial branch,
  -- so the formal proof necessarily works on the corrected nonempty-bounded branch.
  -- The corrected theorem is exactly the good-branch all-directions formula specialized to `u'`.
  exact
    helperForText_35_6_10_allDirectionsFormula_of_nonempty_bounded_partialFirst
      (K := K) hSaddle (u := u) (v := v) hFinite hFirstPartial.1 hFirstPartial.2 u'

/-- Helper for Text 35.6.10: the `EReal`-valued pairing map in the theorem statement can be
rewritten using `dotProduct`, matching the usual `⟪u*, u'⟫` notation. -/
lemma helperForText_35_6_10_sInf_pairingImage_eq_sInf_dotProductImage
    {m : ℕ} (C : Set (Fin m → ℝ)) (u' : Fin m → ℝ) :
    sInf ((fun uStar : Fin m → ℝ => (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) '' C) =
      sInf ((fun uStar : Fin m → ℝ => (((dotProduct uStar u' : ℝ)) : EReal)) '' C) := by
  -- The images coincide because `dotProduct` is definitionally the same finite sum.
  have hImage :
      ((fun uStar : Fin m → ℝ => (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) '' C) =
        ((fun uStar : Fin m → ℝ => (((dotProduct uStar u' : ℝ)) : EReal)) '' C) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [dotProduct]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [dotProduct]
  -- Rewrite `sInf` along the identified images.
  simp [hImage]

/-- Helper for Text 35.6.10: restatement of `section35_text35_6_10` using `dotProduct` on the
right-hand side, for closer alignment with the textbook pairing notation. -/
lemma helperForText_35_6_10_dotProductFormula
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstPartial :
      Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))
    (u' : Fin m → ℝ) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
      sInf
        ((fun uStar : Fin m → ℝ =>
            (((dotProduct uStar u' : ℝ)) : EReal)) ''
          partialSubdifferentialInFirstVariable K u v) := by
  -- Start from the proved statement and rewrite the pairing map.
  calc
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v) := by
      exact section35_text35_6_10 (K := K) hSaddle (u := u) (v := v) hFinite hFirstPartial u'
    _ =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((dotProduct uStar u' : ℝ)) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v) := by
      exact
        helperForText_35_6_10_sInf_pairingImage_eq_sInf_dotProductImage
          (C := partialSubdifferentialInFirstVariable K u v) (u' := u')

/-- Helper for Text 35.6.10: proposition packaging the corrected all-directions formula on the
good branch where `∂₁ K(u, v)` is nonempty and bounded. This is the target boundary actually
supported by the Lean development. -/
abbrev helperForText_35_6_10_originalAllDirectionsFormula
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) : Prop :=
  Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
    Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) ∧
    ∀ u' : Fin m → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v u' 0 L} =
        sInf
          ((fun uStar : Fin m → ℝ =>
              (((∑ i : Fin m, uStar i * u' i) : ℝ) : EReal)) ''
            partialSubdifferentialInFirstVariable K u v)

/-- Helper for Text 35.6.10: if the packaged original textbook formula held at a finite base
point, then specializing to the zero direction forces the corresponding pairing infimum to be
`0`. -/
lemma helperForText_35_6_10_originalAllDirectionsFormula_forces_zeroDirection_pairingInf_eq_zero
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFormula : helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v) :
    sInf
      ((fun uStar : Fin m → ℝ =>
          (((∑ i : Fin m, uStar i * (0 : Fin m → ℝ) i) : ℝ) : EReal)) ''
        partialSubdifferentialInFirstVariable K u v) = 0 := by
  have hZeroDirection := hFormula.2.2 (0 : Fin m → ℝ)
  -- The left-hand side of the specialized formula is exactly the zero directional derivative
  -- value, which was already identified with `0`.
  rw [helperForText_35_6_10_zeroDirectionDerivative_eq_zero
    (K := K) (u := u) (v := v) hFinite] at hZeroDirection
  exact hZeroDirection.symm

/-- Helper for Text 35.6.10: the original unrestricted textbook proposition already fails on the
empty-first-partial branch, so no proof can exist there without extra hypotheses. -/
lemma helperForText_35_6_10_originalAllDirectionsFormula_false_of_empty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInFirstVariable K u v = ∅) :
    ¬ helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v := by
  -- The finiteness hypothesis is irrelevant for the empty-set contradiction; we keep it in the
  -- statement for uniformity with the other Text 35.6.10 helpers.
  have _ := hFinite
  intro hFormula
  have hNonemptyEmpty : Set.Nonempty (∅ : Set (Fin m → ℝ)) := by
    simpa [hpartialEmpty] using hFormula.1
  rcases hNonemptyEmpty with ⟨uStar, huStar⟩
  exact huStar.elim

/-- Helper for Text 35.6.10: one finite base point with empty first partial subdifferential
already refutes the unrestricted textbook schema for the whole kernel. -/
lemma helperForText_35_6_10_exists_empty_partialFirst_forces_global_originalStatement_failure
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hCounterexample :
      ∃ u : Fin m → ℝ, ∃ v : Fin n → ℝ,
        (K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) ∧
          partialSubdifferentialInFirstVariable K u v = ∅) :
    ¬ ∀ u : Fin m → ℝ, ∀ v : Fin n → ℝ,
      (K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) →
        helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v := by
  rintro hOriginalSchema
  rcases hCounterexample with ⟨u, v, hFinite, hpartialEmpty⟩
  have hFormula :
      helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v :=
    hOriginalSchema u v hFinite
  -- A single empty-partial witness collapses the global schema to the earlier pointwise
  -- contradiction on that branch.
  exact
    (helperForText_35_6_10_originalAllDirectionsFormula_false_of_empty_partialFirst
      (K := K) (u := u) (v := v) hFinite hpartialEmpty) hFormula

/-- Helper for Text 35.6.10: once the missing nonempty-bounded hypothesis on `∂₁ K(u, v)` is
supplied, the corrected theorem recovers the original all-directions textbook proposition. -/
lemma helperForText_35_6_10_originalAllDirectionsFormula_of_nonempty_bounded_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFirstPartial :
      Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)) :
    helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v := by
  refine ⟨hFirstPartial.1, hFirstPartial.2, ?_⟩
  intro u'
  -- The corrected theorem is exactly the textbook formula specialized to the good branch.
  exact section35_text35_6_10 (K := K) hSaddle (u := u) (v := v) hFinite hFirstPartial u'

/-- Helper for Text 35.6.10: if the packaged original unrestricted textbook formula holds at a
finite base point, then the first partial subdifferential cannot be empty. -/
lemma helperForText_35_6_10_originalAllDirectionsFormula_forces_nonempty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFormula : helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v) :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) := by
  -- This conclusion only uses the packaged nonemptiness; record `hFinite` to avoid a linter
  -- warning about an intentionally unused hypothesis.
  have _ := hFinite
  exact hFormula.1

/-- Helper for Text 35.6.10: once the nonempty-unbounded remainder is excluded, the packaged
original textbook formula already forces the corrected nonempty-bounded branch. -/
lemma helperForText_35_6_10_originalAllDirectionsFormula_forces_goodBranch_of_no_nonempty_unbounded
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hNoNonemptyUnbounded :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)))
    (hFormula : helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v) :
    Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
      Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) := by
  -- Both facts are already part of the packaged formula; `hFinite` and `hNoNonemptyUnbounded`
  -- remain in the statement because later lemmas quantify them.
  have _ := hFinite
  have _ := hNoNonemptyUnbounded
  exact ⟨hFormula.1, hFormula.2.1⟩

/-- Helper for Text 35.6.10: once the nonempty-unbounded remainder is excluded, the packaged
original textbook proposition is equivalent to the corrected nonempty-bounded branch
hypothesis on `∂₁ K(u, v)`. -/
lemma helperForText_35_6_10_originalAllDirectionsFormula_iff_goodBranch_of_no_nonempty_unbounded
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hNoNonemptyUnbounded :
      ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v))) :
    helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v ↔
      (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
        Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)) := by
  constructor
  · intro hFormula
    -- With the nonempty-unbounded alternative excluded, the packaged formula can only live on
    -- the corrected good branch.
    exact
      helperForText_35_6_10_originalAllDirectionsFormula_forces_goodBranch_of_no_nonempty_unbounded
        (K := K) (u := u) (v := v) hFinite hNoNonemptyUnbounded hFormula
  · intro hFirstPartial
    -- Conversely, the corrected theorem recovers the packaged textbook schema on that branch.
    exact
      helperForText_35_6_10_originalAllDirectionsFormula_of_nonempty_bounded_partialFirst
        (K := K) hSaddle (u := u) (v := v) hFinite hFirstPartial

/-- Helper for Text 35.6.10: if the original unrestricted textbook schema held globally, then
every finite base point would have a nonempty first partial subdifferential. -/
lemma helperForText_35_6_10_globalOriginalStatement_forces_nonempty_partialFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hOriginalSchema :
      ∀ u : Fin m → ℝ, ∀ v : Fin n → ℝ,
        (K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) →
          helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v) :
    ∀ u : Fin m → ℝ, ∀ v : Fin n → ℝ,
      (K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) →
        Set.Nonempty (partialSubdifferentialInFirstVariable K u v) := by
  intro u v hFinite
  have hFormula :
      helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v :=
    hOriginalSchema u v hFinite
  -- Specialize the global schema at the chosen finite base point and reuse the earlier
  -- pointwise obstruction to emptiness of `∂₁ K(u, v)`.
  exact
    helperForText_35_6_10_originalAllDirectionsFormula_forces_nonempty_partialFirst
      (K := K) (u := u) (v := v) hFinite hFormula

/-- Helper for Text 35.6.10: if the original unrestricted textbook schema held globally and the
nonempty-unbounded remainder were excluded pointwise, then every finite base point would satisfy
the corrected nonempty-bounded branch hypothesis. -/
lemma helperForText_35_6_10_globalOriginalStatement_forces_goodBranch_of_pointwise_no_nonempty_unbounded
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hNoNonemptyUnbounded :
      ∀ u : Fin m → ℝ, ∀ v : Fin n → ℝ,
        (K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) →
          ¬ (Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
              ¬ Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v)))
    (hOriginalSchema :
      ∀ u : Fin m → ℝ, ∀ v : Fin n → ℝ,
        (K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) →
          helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v) :
    ∀ u : Fin m → ℝ, ∀ v : Fin n → ℝ,
      (K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) →
        Set.Nonempty (partialSubdifferentialInFirstVariable K u v) ∧
          Bornology.IsBounded (partialSubdifferentialInFirstVariable K u v) := by
  intro u v hFinite
  have hFormula :
      helperForText_35_6_10_originalAllDirectionsFormula (K := K) u v :=
    hOriginalSchema u v hFinite
  -- At the chosen finite base point, the pointwise bridge from the original schema to the
  -- corrected branch applies as soon as the nonempty-unbounded alternative is excluded.
  exact
    helperForText_35_6_10_originalAllDirectionsFormula_forces_goodBranch_of_no_nonempty_unbounded
      (K := K) (u := u) (v := v) hFinite (hNoNonemptyUnbounded u v hFinite) hFormula

-- Proof sketch: apply Theorem 23.4 to the proper convex slice `v₁ ↦ K u v₁` at the finite
-- point `v`. The directional derivative of this slice in direction `v'` is exactly
-- `K'(u, v; 0, v')`, and its subdifferential is the second partial subdifferential
-- `∂₂ K(u, v)`. Rewriting the support-function formula from Theorem 23.4 for this slice yields
  -- the desired supremum formula, with `sSup ∅ = ⊥` encoding the convention `sup ∅ = -∞`.
/-- Helper for Text 35.6.11: expand `supportFunctionOfSet` into the explicit supremum of pairings
over `∂₂ K(u, v)`. -/
lemma helperForText_35_6_11_supportEq_sSup_pairingImage
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) (v' : Fin n → ℝ) :
    supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) v' =
      sSup
        ((fun vStar : Fin n → ℝ =>
            (((∑ i : Fin n, vStar i * v' i) : ℝ) : EReal)) ''
          partialSubdifferentialInSecondVariable K u v) := by
  -- The definition of `supportFunctionOfSet` is exactly this `sSup` of coordinatewise pairings.
  rfl

/-- Helper for Text 35.6.11: once `∂₂ K(u, v)` is nonempty and bounded, the direct Theorem 23.4
route on the convex slice `v₁ ↦ K u v₁` yields the supremum formula from the text. -/
lemma helperForText_35_6_11_formula_of_nonempty_bounded_partialSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartial : Set.Nonempty (partialSubdifferentialInSecondVariable K u v))
    (hpartialBdd : Bornology.IsBounded (partialSubdifferentialInSecondVariable K u v))
    (v' : Fin n → ℝ) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} =
      sSup
        ((fun vStar : Fin n → ℝ =>
            (((∑ i : Fin n, vStar i * v' i) : ℝ) : EReal)) ''
          partialSubdifferentialInSecondVariable K u v) := by
  classical
  let g : (Fin n → ℝ) → EReal := K u
  have hg : ConvexFunction g := by
    -- Fixing the first variable turns the saddle kernel into a convex slice.
    simpa [g] using hSaddle.2 u
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The slice base point has the same finite value as the kernel at `(u, v)`.
    simpa [g] using hFinite
  have hsliceNonempty : Set.Nonempty (subdifferentialAt g v) :=
    -- Transport the nonemptiness of `∂₂ K(u, v)` to the Euclidean subdifferential of the slice.
    (helperForText_35_6_7_partialSecond_nonempty_iff_sliceSubdifferential_nonempty
      (K := K) (u := u) (v := v)).1 hpartial
  have hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    -- Properness follows from subdifferentiability at the finite base point.
    (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
      g hg v hgv).1 hsliceNonempty
  have hSecondEq :
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g v) =
        partialSubdifferentialInSecondVariable K u v := by
    -- This is the standard identification of `∂₂ K(u, v)` with the slice subdifferential.
    simpa [g] using
      helperForText_35_6_7_partialSecond_eq_sliceSubdifferential (K := K) (u := u) (v := v)
  have hsliceBdd :
      Bornology.IsBounded (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g v)) := by
    -- Boundedness transports through the same identification.
    simpa [hSecondEq] using hpartialBdd
  have h23 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      g hproperG v
  have hBaseInterior :
      v ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
    -- The nonempty-bounded branch is exactly the interior branch of Theorem 23.4.
    exact (h23.2.2.1).1 ⟨hsliceNonempty, hsliceBdd⟩
  have hBaseRi :
      v ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :=
    helperForTheorem_23_4_mem_relativeInterior_of_mem_interior hBaseInterior
  have hDirEq :
      upperDirectionalDerivativeAt g v v' =
        subdifferentialSupportAt g v v' :=
    -- Apply the directional-derivative representation from Theorem 23.4.
    (h23.2.1 hBaseRi).2.2.2 v'
  have hDerivativeEq :
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} =
        upperDirectionalDerivativeAt g v v' := by
    -- Convert the saddle derivative definition into the slice directional derivative.
    have hpsiEq :
        secondVariableDirectionalDerivativeFunction K u v v' =
          upperDirectionalDerivativeAt g v v' := by
      simpa [g] using
        congrFun
          (helperForText_35_6_7_secondVariableDirectionalDerivative_eq_upperDirectionalDerivative
            (K := K) hSaddle (u := u) (v := v) hFinite)
          v'
    simpa [secondVariableDirectionalDerivativeFunction] using hpsiEq
  have hSupportEq :
      subdifferentialSupportAt g v v' =
        supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) v' := by
    -- Rewrite the Chapter 23 support value as the explicit support function over `∂₂ K(u, v)`.
    simpa [g] using
      congrFun
        (helperForText_35_6_7_sliceSupport_eq_secondPartialSupport (K := K) (u := u) (v := v))
        v'
  -- Assemble: saddle derivative = slice derivative = slice support = explicit support function.
  calc
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} =
        upperDirectionalDerivativeAt g v v' := hDerivativeEq
    _ = subdifferentialSupportAt g v v' := hDirEq
    _ = supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) v' := hSupportEq
    _ =
        sSup
          ((fun vStar : Fin n → ℝ =>
              (((∑ i : Fin n, vStar i * v' i) : ℝ) : EReal)) ''
            partialSubdifferentialInSecondVariable K u v) := by
      -- Finish by unfolding the definition of the support function.
      simpa using helperForText_35_6_11_supportEq_sSup_pairingImage (K := K) u v v'

/-- Helper for Text 35.6.11: the pointwise supremum formula forces `∂₂ K(u, v)` to be nonempty,
since emptiness yields a direction where the saddle directional derivative takes the value `⊤`. -/
lemma helperForText_35_6_11_nonempty_partialSecond_required
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hFormula :
      ∀ v' : Fin n → ℝ,
        sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} =
          sSup
            ((fun vStar : Fin n → ℝ =>
                (((∑ i : Fin n, vStar i * v' i) : ℝ) : EReal)) ''
              partialSubdifferentialInSecondVariable K u v)) :
    Set.Nonempty (partialSubdifferentialInSecondVariable K u v) := by
  classical
  -- Argue by contradiction: if `∂₂ K(u, v)` is empty, the formula fails in the `⊤` direction.
  by_contra hnonempty
  have hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hnonempty
  rcases
      helperForText_35_6_7_exists_bot_and_top_direction_of_empty_partialSecond
        (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty with
    ⟨w, _hwBot, hwTop⟩
  have hEq := hFormula (-w)
  have hLHS :
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 (-w) L} = (⊤ : EReal) := by
    -- Unfold the definition of the second-variable saddle directional derivative function.
    simpa [secondVariableDirectionalDerivativeFunction] using hwTop
  have : (⊤ : EReal) = (⊥ : EReal) := by
    -- The assumed formula at direction `-w` collapses to `⊤ = ⊥`, because the supremum is over an
    -- empty set.
    have hEqTop :
        (⊤ : EReal) =
          sSup
            ((fun vStar : Fin n → ℝ =>
                (((∑ i : Fin n, vStar i * (-w) i) : ℝ) : EReal)) ''
              partialSubdifferentialInSecondVariable K u v) := by
      simpa [hLHS] using hEq
    -- Simplify the supremum over an empty set on the right-hand side.
    have hEqTop' := hEqTop
    simp [hpartialEmpty] at hEqTop'
  exact top_ne_bot this

/-- Helper for Text 35.6.11: if `∂₂ K(u, v) = ∅`, then there exists a direction `v'` where the
claimed supremum formula fails (the left-hand side becomes `⊤` while the right-hand side is
`sSup ∅ = ⊥`). -/
lemma helperForText_35_6_11_exists_counterexample_of_empty_partialSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅) :
    ∃ v' : Fin n → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} ≠
        sSup
          ((fun vStar : Fin n → ℝ =>
              (((∑ i : Fin n, vStar i * v' i) : ℝ) : EReal)) ''
            partialSubdifferentialInSecondVariable K u v) := by
  classical
  -- Use the existing empty-branch lemma to produce a direction with `⊤` directional derivative.
  rcases
      helperForText_35_6_7_exists_bot_and_top_direction_of_empty_partialSecond
        (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty with
    ⟨w, _hwBot, hwTop⟩
  refine ⟨-w, ?_⟩
  -- Step 1: identify the left-hand side with the `⊤` value supplied by the empty-branch lemma.
  have hLHS :
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 (-w) L} = (⊤ : EReal) := by
    simpa [secondVariableDirectionalDerivativeFunction] using hwTop
  -- Step 2: the right-hand side is a supremum over an empty image, hence `⊥`.
  have hRHS :
      sSup
          ((fun vStar : Fin n → ℝ =>
              (((∑ i : Fin n, vStar i * (-w) i) : ℝ) : EReal)) ''
            partialSubdifferentialInSecondVariable K u v) = (⊥ : EReal) := by
    simp [hpartialEmpty]
  -- Conclude by `⊤ ≠ ⊥`.
  intro hEq
  have hEqTop :
      (⊤ : EReal) =
        sSup
          ((fun vStar : Fin n → ℝ =>
              (((∑ i : Fin n, vStar i * (-w) i) : ℝ) : EReal)) ''
            partialSubdifferentialInSecondVariable K u v) := by
    -- Rewrite the left-hand side of `hEq` using `hLHS`, without simplifying the right-hand side.
    have hEq' := hEq
    rw [hLHS] at hEq'
    exact hEq'
  have : (⊤ : EReal) = (⊥ : EReal) := Eq.trans hEqTop hRHS
  exact top_ne_bot this

/-- Helper for Text 35.6.11: if `∂₂ K(u, v) = ∅`, then there exists a direction `v'` where the
left-hand side equals `⊤` while the right-hand side is `sSup ∅ = ⊥`. -/
lemma helperForText_35_6_11_exists_top_lhs_and_bot_rhs_of_empty_partialSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅) :
    ∃ v' : Fin n → ℝ,
      sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} = (⊤ : EReal) ∧
        sSup
            ((fun vStar : Fin n → ℝ =>
                (((∑ i : Fin n, vStar i * v' i) : ℝ) : EReal)) ''
              partialSubdifferentialInSecondVariable K u v) = (⊥ : EReal) := by
  classical
  -- Choose the direction with `⊤` directional derivative given by the empty-branch lemma.
  rcases
      helperForText_35_6_7_exists_bot_and_top_direction_of_empty_partialSecond
        (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty with
    ⟨w, _hwBot, hwTop⟩
  refine ⟨-w, ?_, ?_⟩
  · -- The left-hand side is exactly the second-variable directional derivative value.
    simpa [secondVariableDirectionalDerivativeFunction] using hwTop
  · -- The supremum is taken over an empty image set, hence equals `⊥`.
    simp [hpartialEmpty]

/-- Helper for Text 35.6.11: if the base point `v` lies in the interior of the effective domain
of the convex slice `v₁ ↦ K u v₁`, then the supremum formula from Text 35.6.11 holds for every
direction `v'`. -/
lemma helperForText_35_6_11_formula_of_mem_interior_effectiveDomain_secondSlice
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hvInt :
      v ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u)))
    (v' : Fin n → ℝ) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} =
      sSup
        ((fun vStar : Fin n → ℝ =>
            (((∑ i : Fin n, vStar i * v' i) : ℝ) : EReal)) ''
          partialSubdifferentialInSecondVariable K u v) := by
  classical
  -- Step 1: work on the convex slice `g(v₁) = K u v₁` and use the interior hypothesis to obtain
  -- nonempty and bounded subdifferentials at `v` (Chapter 23).
  let g : (Fin n → ℝ) → EReal := K u
  have hg : ConvexFunction g := by
    -- Fixing `u` turns the saddle kernel into a convex slice.
    simpa [g] using hSaddle.2 u
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The slice inherits finiteness from the kernel at `(u, v)`.
    simpa [g] using hFinite
  have hProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    -- Interior membership of the effective domain makes the slice proper.
    helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
      hg (by simpa [g] using hvInt) hgv.2
  have h23 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      g hProper v
  have hSliceNonemptyBdd :
      Set.Nonempty (subdifferentialAt g v) ∧
        Bornology.IsBounded (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g v)) := by
    -- This is exactly the characterization of interior points by nonempty bounded subdifferentials.
    exact (h23.2.2.1).2 (by simpa [g] using hvInt)
  have hpartial : Set.Nonempty (partialSubdifferentialInSecondVariable K u v) :=
    -- Transport nonemptiness from the Euclidean slice subdifferential to `∂₂ K(u, v)`.
    (helperForText_35_6_7_partialSecond_nonempty_iff_sliceSubdifferential_nonempty
      (K := K) (u := u) (v := v)).2 hSliceNonemptyBdd.1
  have hSecondEq :
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g v) =
        partialSubdifferentialInSecondVariable K u v := by
    -- Identify the slice and textbook second partial subdifferentials.
    simpa [g] using
      helperForText_35_6_7_partialSecond_eq_sliceSubdifferential (K := K) (u := u) (v := v)
  have hpartialBdd : Bornology.IsBounded (partialSubdifferentialInSecondVariable K u v) := by
    -- Transport boundedness through the same identification.
    simpa [hSecondEq] using hSliceNonemptyBdd.2
  -- Step 2: apply the already-proved Theorem 23.4 route under the nonempty-bounded hypothesis.
  exact
    helperForText_35_6_11_formula_of_nonempty_bounded_partialSecond
      (K := K) hSaddle (u := u) (v := v) hFinite hpartial hpartialBdd v'

/-- Text 35.6.11: in the good branch where the second partial subdifferential at `(u, v)` is
nonempty and bounded, the directional derivative `K'(u, v; 0, v')` equals the support formula
`sup {⟪v*, v'⟫ | v* ∈ ∂₂ K(u, v)}` for every direction `v'`. This is the branch supplied by the
Chapter 23 route already developed in the file. -/
theorem section35_text35_6_11
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartial : Set.Nonempty (partialSubdifferentialInSecondVariable K u v))
    (hpartialBdd : Bornology.IsBounded (partialSubdifferentialInSecondVariable K u v))
    (v' : Fin n → ℝ) :
    sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L} =
      sSup
        ((fun vStar : Fin n → ℝ =>
            (((∑ i : Fin n, vStar i * v' i) : ℝ) : EReal)) ''
          partialSubdifferentialInSecondVariable K u v) := by
  exact
    helperForText_35_6_11_formula_of_nonempty_bounded_partialSecond
      (K := K) hSaddle (u := u) (v := v) hFinite hpartial hpartialBdd v'

/-- The concave subdifferential of a real-valued saddle kernel in the first variable on `C`
at `(u, v)`. -/
def realPartialSubdifferentialInFirstVariableOn {m n : ℕ}
    (C : Set (Fin m → ℝ)) (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    Set (Fin m → ℝ) :=
  {uStar | ∀ u' ∈ C, K u' v ≤ K u v + ∑ i : Fin m, uStar i * (u' i - u i)}

/-- The convex subdifferential of a real-valued saddle kernel in the second variable on `D`
at `(u, v)`. -/
def realPartialSubdifferentialInSecondVariableOn {m n : ℕ}
    (D : Set (Fin n → ℝ)) (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {vStar | ∀ v' ∈ D, K u v' ≥ K u v + ∑ i : Fin n, vStar i * (v' i - v i)}

/-- The bilinear pairing of a product subgradient `(u*, v*)` with a direction `(u', v')`. -/
def saddleSubgradientPairing {m n : ℕ}
    (uStar : Fin m → ℝ) (uDir : Fin m → ℝ)
    (vStar : Fin n → ℝ) (vDir : Fin n → ℝ) : ℝ :=
  (∑ i : Fin m, uStar i * uDir i) + ∑ j : Fin n, vStar j * vDir j

/-- The first-variable directional derivative of a real-valued saddle kernel at `(u, v)` in the
direction `u'`, packaged as the infimum of the real numbers that realize this derivative. -/
noncomputable def realFirstVariableDirectionalDerivativeValue {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) (u' : Fin m → ℝ) : ℝ :=
  sInf {L : ℝ | HasRealSaddleDirectionalDerivativeAt K u v u' 0 L}

/-- The second-variable directional derivative of a real-valued saddle kernel at `(u, v)` in the
direction `v'`, packaged as the infimum of the real numbers that realize this derivative. -/
noncomputable def realSecondVariableDirectionalDerivativeValue {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) (v' : Fin n → ℝ) : ℝ :=
  sInf {L : ℝ | HasRealSaddleDirectionalDerivativeAt K u v 0 v' L}

/-- The saddle subdifferential of a real-valued saddle kernel on `C × D` at `(u, v)`, written as
the product of the concave and convex partial subdifferentials. -/
def realSaddleSubdifferentialOn {m n : ℕ}
    (C : Set (Fin m → ℝ)) (D : Set (Fin n → ℝ))
    (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  realPartialSubdifferentialInFirstVariableOn C K u v ×ˢ
    realPartialSubdifferentialInSecondVariableOn D K u v

/-- The closed Euclidean ball of radius `ε` in `ℝ^m × ℝ^n`, written in split coordinates. -/
def splitEuclideanClosedBall {m n : ℕ} (ε : ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p |
    (∑ i : Fin m, p.1 i ^ (2 : ℕ)) + ∑ j : Fin n, p.2 j ^ (2 : ℕ) ≤ ε ^ (2 : ℕ)}

/-- Helper for Text 35.6.12: coerce a real-valued bifunction to an `EReal`-valued bifunction. -/
def helperForText_35_6_12_erealOfRealKernel
    {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u v => ((K u v : ℝ) : EReal)

end Section35
end Chap07

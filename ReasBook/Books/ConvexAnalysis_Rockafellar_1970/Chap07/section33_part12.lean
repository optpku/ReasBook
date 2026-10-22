/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part11

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- Helper for Lemma33.0.34: translating the primal variable by `u` extracts the constant
correction term `- ⟪u, vStar⟫` from the dual pairing. -/
lemma helperForLemma33_0_34_dotProduct_translation_split
    {m : ℕ}
    {u w vStar : Fin m → ℝ} :
    (((dotProduct (w - u) vStar : ℝ) : EReal)) =
      (((dotProduct w vStar : ℝ) : EReal)) - (((dotProduct u vStar : ℝ) : EReal)) := by
  -- The textbook subtraction identity is exactly the first-variable linearity of dot product.
  rw [sub_dotProduct, EReal.coe_sub]

/-- Helper for Lemma33.0.34: translating the first variable does not change the range of a
two-variable integrand, because the substitution `w = u + v` is bijective. -/
lemma helperForLemma33_0_34_translate_first_range_eq
    {m n : ℕ}
    (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) :
    Set.range (fun vy : (Fin m → ℝ) × (Fin n → ℝ) => G (u + vy.1) vy.2) =
      Set.range (fun wy : (Fin m → ℝ) × (Fin n → ℝ) => G wy.1 wy.2) := by
  -- One direction is immediate by renaming `w = u + v`.
  ext z
  constructor
  · intro hz
    rcases hz with ⟨⟨v, y⟩, rfl⟩
    exact ⟨(u + v, y), rfl⟩
  · intro hz
    -- The reverse direction uses the inverse substitution `v = w - u`.
    rcases hz with ⟨⟨w, y⟩, rfl⟩
    refine ⟨(w - u, y), ?_⟩
    simp

/-- Helper for Lemma33.0.34: after translating `w = u + v`, the translated-tilted adjoint
integrand is the original adjoint integrand for `F` at `xStar + yStar`, shifted by the
constant `- ⟪u, vStar⟫`. -/
lemma helperForLemma33_0_34_translatedTilted_integrand_rewrite
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u v vStar : Fin m → ℝ}
    {xStar yStar y : Fin n → ℝ} :
    ((F (u + v) y - ((dotProduct y xStar : ℝ) : EReal)) -
        ((dotProduct y yStar : ℝ) : EReal)) +
        (((dotProduct v vStar : ℝ) : EReal)) =
      (F (u + v) y - ((dotProduct y (xStar + yStar) : ℝ) : EReal) +
          (((dotProduct (u + v) vStar : ℝ) : EReal))) -
        (((dotProduct u vStar : ℝ) : EReal)) := by
  -- First combine the two `y`-tilt terms into the single tilt by `xStar + yStar`.
  rw [helperForLemma33_0_34_tilt_terms_combine
    (Fv := F (u + v) y) (y := y) (xStar := xStar) (yStar := yStar)]
  -- Next rewrite the translated dual pairing `⟪v, vStar⟫` using `w = u + v`.
  have hSplit :
      (((dotProduct v vStar : ℝ) : EReal)) =
        (((dotProduct (u + v) vStar : ℝ) : EReal)) -
          (((dotProduct u vStar : ℝ) : EReal)) := by
    simpa using
      (helperForLemma33_0_34_dotProduct_translation_split
        (u := u) (w := u + v) (vStar := vStar))
  rw [hSplit]
  -- Finally reassociate the finite correction term to match the later adjoint formula.
  simp [sub_eq_add_neg, add_assoc]

/-- Helper for Lemma33.0.34: the whole range defining the translated-tilted adjoint equals the
range for the untranslated integrand at `xStar + yStar`, shifted by the constant
`- ⟪u, vStar⟫`. -/
lemma helperForLemma33_0_34_translatedTilted_adjointRange_eq
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u vStar : Fin m → ℝ}
    {xStar yStar : Fin n → ℝ} :
    Set.range
        (fun vy : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((F (u + vy.1) vy.2 - ((dotProduct vy.2 xStar : ℝ) : EReal)) -
              ((dotProduct vy.2 yStar : ℝ) : EReal)) +
            (((dotProduct vy.1 vStar : ℝ) : EReal))) =
      Set.range
        (fun wy : (Fin m → ℝ) × (Fin n → ℝ) =>
          (F wy.1 wy.2 - ((dotProduct wy.2 (xStar + yStar) : ℝ) : EReal) +
              (((dotProduct wy.1 vStar : ℝ) : EReal))) -
            (((dotProduct u vStar : ℝ) : EReal))) := by
  let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
    fun w y =>
      (F w y - ((dotProduct y (xStar + yStar) : ℝ) : EReal) +
          (((dotProduct w vStar : ℝ) : EReal))) -
        (((dotProduct u vStar : ℝ) : EReal))
  -- First rewrite the translated-tilted integrand pointwise into the shifted untranslated one.
  have hPointwise :
      (fun vy : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((F (u + vy.1) vy.2 - ((dotProduct vy.2 xStar : ℝ) : EReal)) -
              ((dotProduct vy.2 yStar : ℝ) : EReal)) +
            (((dotProduct vy.1 vStar : ℝ) : EReal))) =
        fun vy : (Fin m → ℝ) × (Fin n → ℝ) => G (u + vy.1) vy.2 := by
    funext vy
    rcases vy with ⟨v, y⟩
    simpa [G] using
      (helperForLemma33_0_34_translatedTilted_integrand_rewrite
        (F := F) (u := u) (v := v) (vStar := vStar)
        (xStar := xStar) (yStar := yStar) (y := y))
  -- Next transport the range across the bijection `w = u + v`.
  calc
    Set.range
        (fun vy : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((F (u + vy.1) vy.2 - ((dotProduct vy.2 xStar : ℝ) : EReal)) -
              ((dotProduct vy.2 yStar : ℝ) : EReal)) +
            (((dotProduct vy.1 vStar : ℝ) : EReal))) =
        Set.range (fun vy : (Fin m → ℝ) × (Fin n → ℝ) => G (u + vy.1) vy.2) := by
          rw [hPointwise]
    _ = Set.range (fun wy : (Fin m → ℝ) × (Fin n → ℝ) => G wy.1 wy.2) := by
          exact helperForLemma33_0_34_translate_first_range_eq (G := G) (u := u)
    _ =
        Set.range
          (fun wy : (Fin m → ℝ) × (Fin n → ℝ) =>
            (F wy.1 wy.2 - ((dotProduct wy.2 (xStar + yStar) : ℝ) : EReal) +
                (((dotProduct wy.1 vStar : ℝ) : EReal))) -
              (((dotProduct u vStar : ℝ) : EReal))) := by
          simp [G]

/-- Helper for Lemma33.0.34: subtracting the constant `⟪u, vStar⟫` from the untranslated
adjoint integrand is exactly the image of its range under the affine map `z ↦ z - ⟪u,
vStar⟫`. -/
lemma helperForLemma33_0_34_untranslated_adjointRange_sub_eq_image
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u vStar : Fin m → ℝ}
    {xStar yStar : Fin n → ℝ} :
    Set.range
        (fun wy : (Fin m → ℝ) × (Fin n → ℝ) =>
          (F wy.1 wy.2 - ((dotProduct wy.2 (xStar + yStar) : ℝ) : EReal) +
              (((dotProduct wy.1 vStar : ℝ) : EReal))) -
            (((dotProduct u vStar : ℝ) : EReal))) =
      (fun z : EReal => z - (((dotProduct u vStar : ℝ) : EReal))) ''
        Set.range
          (fun wy : (Fin m → ℝ) × (Fin n → ℝ) =>
            F wy.1 wy.2 - ((dotProduct wy.2 (xStar + yStar) : ℝ) : EReal) +
              (((dotProduct wy.1 vStar : ℝ) : EReal))) := by
  ext z
  constructor
  · intro hz
    -- Repackage a point in the shifted range as the image of the corresponding unshifted value.
    rcases hz with ⟨wy, rfl⟩
    exact ⟨_, ⟨wy, rfl⟩, rfl⟩
  · intro hz
    -- Unpack an image point and reuse the same witness in the shifted range.
    rcases hz with ⟨w, ⟨wy, rfl⟩, rfl⟩
    exact ⟨wy, rfl⟩

/-- Helper for Lemma33.0.34: the translated-tilted adjoint range is the image of the
untranslated adjoint range under subtraction by the constant `⟪u, vStar⟫`. -/
lemma helperForLemma33_0_34_translatedTilted_adjointRange_eq_imageSub
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u vStar : Fin m → ℝ}
    {xStar yStar : Fin n → ℝ} :
    Set.range
        (fun vy : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((F (u + vy.1) vy.2 - ((dotProduct vy.2 xStar : ℝ) : EReal)) -
              ((dotProduct vy.2 yStar : ℝ) : EReal)) +
            (((dotProduct vy.1 vStar : ℝ) : EReal))) =
      (fun z : EReal => z - (((dotProduct u vStar : ℝ) : EReal))) ''
        Set.range
          (fun wy : (Fin m → ℝ) × (Fin n → ℝ) =>
            F wy.1 wy.2 - ((dotProduct wy.2 (xStar + yStar) : ℝ) : EReal) +
              (((dotProduct wy.1 vStar : ℝ) : EReal))) := by
  -- First use the existing change-of-variables lemma to expose the constant shift explicitly.
  calc
    Set.range
        (fun vy : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((F (u + vy.1) vy.2 - ((dotProduct vy.2 xStar : ℝ) : EReal)) -
              ((dotProduct vy.2 yStar : ℝ) : EReal)) +
            (((dotProduct vy.1 vStar : ℝ) : EReal))) =
      Set.range
        (fun wy : (Fin m → ℝ) × (Fin n → ℝ) =>
          (F wy.1 wy.2 - ((dotProduct wy.2 (xStar + yStar) : ℝ) : EReal) +
              (((dotProduct wy.1 vStar : ℝ) : EReal))) -
            (((dotProduct u vStar : ℝ) : EReal))) := by
          exact
            helperForLemma33_0_34_translatedTilted_adjointRange_eq
              (F := F) (u := u) (vStar := vStar) (xStar := xStar) (yStar := yStar)
    _ =
      (fun z : EReal => z - (((dotProduct u vStar : ℝ) : EReal))) ''
        Set.range
          (fun wy : (Fin m → ℝ) × (Fin n → ℝ) =>
            F wy.1 wy.2 - ((dotProduct wy.2 (xStar + yStar) : ℝ) : EReal) +
              (((dotProduct wy.1 vStar : ℝ) : EReal))) := by
          exact
            helperForLemma33_0_34_untranslated_adjointRange_sub_eq_image
              (F := F) (u := u) (vStar := vStar) (xStar := xStar) (yStar := yStar)

/-- Helper for Lemma33.0.34: after the `w = u + v` substitution, the infimum defining the
translated-tilted adjoint is the infimum for `F` at `xStar + yStar`, minus the constant
`⟪u, vStar⟫`. -/
lemma helperForLemma33_0_34_translatedTilted_adjointRange_sInf_eq
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u vStar : Fin m → ℝ}
    {xStar yStar : Fin n → ℝ} :
    sInf
      (Set.range
        (fun vy : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((F (u + vy.1) vy.2 - ((dotProduct vy.2 xStar : ℝ) : EReal)) -
              ((dotProduct vy.2 yStar : ℝ) : EReal)) +
            (((dotProduct vy.1 vStar : ℝ) : EReal)))) =
      sInf
        (Set.range
          (fun wy : (Fin m → ℝ) × (Fin n → ℝ) =>
            F wy.1 wy.2 - ((dotProduct wy.2 (xStar + yStar) : ℝ) : EReal) +
              (((dotProduct wy.1 vStar : ℝ) : EReal)))) -
        (((dotProduct u vStar : ℝ) : EReal)) := by
  -- Rewrite the translated-tilted range as the image of the untranslated range under the
  -- order isomorphism `z ↦ z - ⟪u, vStar⟫`.
  rw [helperForLemma33_0_34_translatedTilted_adjointRange_eq_imageSub
      (F := F) (u := u) (vStar := vStar) (xStar := xStar) (yStar := yStar)]
  let S : Set EReal :=
    Set.range
      (fun wy : (Fin m → ℝ) × (Fin n → ℝ) =>
        F wy.1 wy.2 - ((dotProduct wy.2 (xStar + yStar) : ℝ) : EReal) +
          (((dotProduct wy.1 vStar : ℝ) : EReal)))
  -- Transport `sInf` across addition by the real constant `-(⟪u, vStar⟫)` using the
  -- existing Chapter 6 order-isomorphism lemma.
  simpa [S, sub_eq_add_neg] using
    (helperForTheorem_6_29_3_sInf_image_add_right
      (c := -(dotProduct u vStar : ℝ)) (s := S))

/-- Helper for Lemma33.0.34: the textbook translated-and-tilted bifunction
`H(v, y) = F(u + v, y) - ⟪y, xStar⟫`, recorded locally in the dependency-closed file that
stages the adjoint calculation. -/
noncomputable abbrev helperForLemma33_0_34_translatedTiltedBifunction
    {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ)
    (xStar : Fin n → ℝ) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun v y => F (u + v) y - ((dotProduct y xStar : ℝ) : EReal)

/-- Helper for Lemma33.0.34: the raw two-variable infimum formula that later becomes
`genuineConvexBifunctionAdjoint` in the downstream file. -/
noncomputable abbrev helperForLemma33_0_34_rawGenuineAdjoint
    {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (xStar : Fin n → ℝ)
    (uStar : Fin m → ℝ) : EReal :=
  sInf <| Set.range fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
    (F ux.1 ux.2 - ((dotProduct ux.2 xStar : ℝ) : EReal)) +
      ((dotProduct ux.1 uStar : ℝ) : EReal)

/-- Helper for Lemma33.0.34: the raw adjoint of the textbook bifunction `H(v, y) =
F(u + v, y) - ⟪y, xStar⟫` is the raw adjoint of `F` at `xStar + yStar`, shifted by
`-⟪u, vStar⟫`. -/
lemma helperForLemma33_0_34_rawGenuineAdjoint_translatedTiltedBifunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u vStar : Fin m → ℝ}
    {xStar yStar : Fin n → ℝ} :
    helperForLemma33_0_34_rawGenuineAdjoint
        (helperForLemma33_0_34_translatedTiltedBifunction F u xStar) yStar vStar =
      helperForLemma33_0_34_rawGenuineAdjoint F (xStar + yStar) vStar -
        (((dotProduct u vStar : ℝ) : EReal)) := by
  -- Unfold the local textbook object `H` and the raw adjoint so the goal becomes exactly
  -- the already-proved `sInf` transport identity from the change of variables `w = u + v`.
  unfold helperForLemma33_0_34_rawGenuineAdjoint
    helperForLemma33_0_34_translatedTiltedBifunction
  -- The Section 33 helper chain already proves this raw adjoint formula verbatim.
  simpa using
    (helperForLemma33_0_34_translatedTilted_adjointRange_sInf_eq
      (F := F) (u := u) (vStar := vStar) (xStar := xStar) (yStar := yStar))

/-- Helper for Lemma33.0.34: after expanding the translated-tilted integrand explicitly, the
left-hand side of the downstream adjoint computation is already the raw adjoint formula proved
above. -/
lemma helperForLemma33_0_34_explicitTranslatedTiltedAdjoint_eq_rawTranslated
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u vStar : Fin m → ℝ}
    {xStar yStar : Fin n → ℝ} :
    sInf
        (Set.range
          (fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
            ((F (u + ux.1) ux.2 - ((dotProduct ux.2 xStar : ℝ) : EReal)) -
                ((dotProduct ux.2 yStar : ℝ) : EReal)) +
              (((dotProduct ux.1 vStar : ℝ) : EReal)))) =
      helperForLemma33_0_34_rawGenuineAdjoint
        (helperForLemma33_0_34_translatedTiltedBifunction F u xStar) yStar vStar := by
  -- Unfold the local textbook bifunction and the raw adjoint abbreviation until both sides
  -- are literally the same explicit `sInf` expression.
  unfold helperForLemma33_0_34_rawGenuineAdjoint
    helperForLemma33_0_34_translatedTiltedBifunction
  rfl

/-- Helper for Lemma33.0.34: after expanding the translated-tilted integrand explicitly, the
left-hand side of the downstream adjoint computation is already the raw adjoint formula proved
above. -/
lemma helperForLemma33_0_34_explicitTranslatedTiltedAdjoint_eq_rawShift
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u vStar : Fin m → ℝ}
    {xStar yStar : Fin n → ℝ} :
    sInf
        (Set.range
          (fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
            ((F (u + ux.1) ux.2 - ((dotProduct ux.2 xStar : ℝ) : EReal)) -
                ((dotProduct ux.2 yStar : ℝ) : EReal)) +
              (((dotProduct ux.1 vStar : ℝ) : EReal)))) =
      helperForLemma33_0_34_rawGenuineAdjoint F (xStar + yStar) vStar -
        (((dotProduct u vStar : ℝ) : EReal)) := by
  -- First identify the explicit left-hand side with the raw adjoint of the local textbook
  -- bifunction `H(v, y) = F(u + v, y) - ⟪y, xStar⟫`.
  rw [helperForLemma33_0_34_explicitTranslatedTiltedAdjoint_eq_rawTranslated
      (F := F) (u := u) (vStar := vStar) (xStar := xStar) (yStar := yStar)]
  -- Then apply the already-proved translated raw adjoint formula.
  exact
    helperForLemma33_0_34_rawGenuineAdjoint_translatedTiltedBifunction
      (F := F) (u := u) (vStar := vStar) (xStar := xStar) (yStar := yStar)

end Section33
end Chap07

/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part2

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 26.4: at each interior effective-domain point, the chosen interior
gradient is a genuine Euclidean subgradient of `f`. -/
lemma helperForTheorem_26_4_interiorGradientMap_mem_subdifferentialAt
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x)
    {x : Fin n → ℝ}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    dotProductEquiv ℝ (Fin n) (interiorGradientMap f hdiff x) ∈ subdifferentialAt f x := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  -- The interior gradient is exactly the unique Euclidean subgradient furnished by Theorem 25.1.
  have hcore :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      f hfConv x (ERealDifferentiableAt.finiteAt (hdiff x hx))).1 (hdiff x hx)
  simpa [interiorGradientMap, hx] using hcore.1

/-- Helper for Theorem 26.4: Fenchel-Young equality rewrites the value of `f*` at an interior
gradient as the standard subtraction formula. -/
lemma helperForTheorem_26_4_fenchelConjugate_eq_dotSub_at_interiorGradient
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x)
    {x : Fin n → ℝ}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    fenchelConjugate n f (interiorGradientMap f hdiff x) =
      (((dotProduct x (interiorGradientMap f hdiff x) : ℝ) : EReal) - f x) := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hSub :
      IsEuclideanSubgradientAt f x (interiorGradientMap f hdiff x) := by
    -- Repackage subdifferential membership in the Euclidean-subgradient form needed by Theorem 23.5.
    simpa [IsEuclideanSubgradientAt] using
      helperForTheorem_26_4_interiorGradientMap_mem_subdifferentialAt
        (hf := hf) (hdiff := hdiff) hx
  have hFY :
      FenchelYoungEqualityAt f x (interiorGradientMap f hdiff x) := by
    -- The Euclidean subgradient characterization produces the Fenchel-Young equality.
    exact
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        f hproper x (interiorGradientMap f hdiff x)).1.out 0 3).1 hSub
  -- Rewrite that equality in the subtraction form required by the Legendre package.
  exact
    helperForText_26_4_0_2_fenchelYoung_subtractionForm
      (F := f) (x := x) (xStar := interiorGradientMap f hdiff x) hproper hFY

/-- Helper for Theorem 26.4: the subtraction formula is constant on each fiber of the interior
gradient map. -/
lemma helperForTheorem_26_4_interiorGradient_fiber_well_defined
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x)
    {x₁ x₂ xStar : Fin n → ℝ}
    (hx₁ : x₁ ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hx₂ : x₂ ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hx₁Star : interiorGradientMap f hdiff x₁ = xStar)
    (hx₂Star : interiorGradientMap f hdiff x₂ = xStar) :
    (((dotProduct x₁ xStar : ℝ) : EReal) - f x₁) =
      (((dotProduct x₂ xStar : ℝ) : EReal) - f x₂) := by
  have hEq₁ :
      fenchelConjugate n f xStar =
        (((dotProduct x₁ xStar : ℝ) : EReal) - f x₁) := by
    -- Identify the first fiber value with `f* xStar`.
    simpa [hx₁Star] using
      helperForTheorem_26_4_fenchelConjugate_eq_dotSub_at_interiorGradient
        (hf := hf) (hdiff := hdiff) hx₁
  have hEq₂ :
      fenchelConjugate n f xStar =
        (((dotProduct x₂ xStar : ℝ) : EReal) - f x₂) := by
    -- The same identification holds for the second source point in the fiber.
    simpa [hx₂Star] using
      helperForTheorem_26_4_fenchelConjugate_eq_dotSub_at_interiorGradient
        (hf := hf) (hdiff := hdiff) hx₂
  -- Both source values coincide because they are equal to the same conjugate value.
  calc
    (((dotProduct x₁ xStar : ℝ) : EReal) - f x₁) = fenchelConjugate n f xStar := by
      exact hEq₁.symm
    _ = (((dotProduct x₂ xStar : ℝ) : EReal) - f x₂) := hEq₂

/-- Helper for Theorem 26.4: the image of the interior gradient map lies in the effective domain
of the Fenchel conjugate. -/
lemma helperForTheorem_26_4_gradientImage_subset_effectiveDomain_fenchelConjugate
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x) :
    interiorGradientMap f hdiff ''
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ⊆
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hfConv, hf_closed⟩
  have hRangeSubset :
      (dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialRange f ⊆
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    (relativeInterior_subset_preimage_subdifferentialRange_subset_effectiveDomain_fenchelConjugate
      (f := f) hclosed hproper).2
  intro xStar hxStar
  rcases hxStar with ⟨x, hx, rfl⟩
  -- Each gradient image point comes from an actual subgradient, hence lies in `dom f*`.
  apply hRangeSubset
  change dotProductEquiv ℝ (Fin n) (interiorGradientMap f hdiff x) ∈ subdifferentialRange f
  rw [helperForRemark_5_24_2_mem_subdifferentialRange_iff_exists]
  exact
    ⟨x,
      helperForTheorem_26_4_interiorGradientMap_mem_subdifferentialAt
        (hf := hf) (hdiff := hdiff) hx⟩

/-- Theorem 26.4: if `f` is a closed proper convex function, `C = int (dom f)` is nonempty, and
`f` is differentiable on `C`, then the Legendre conjugate of `(C, f)` is well-defined. More
precisely, with `D` the image of `C` under the interior gradient map of `f`, there exists a
Legendre-conjugate package on `C` whose target is `D`; moreover `D ⊆ dom f*`, and the package's
conjugate function agrees with `f*` on `D`. -/
theorem closedProperConvex_has_legendreConjugatePackageOn_interior_eq_fenchelConjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hC_nonempty :
      (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)).Nonempty)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x) :
    let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
      L.toFun = interiorGradientMap f hdiff ∧
      L.target = interiorGradientMap f hdiff '' C ∧
      Set.EqOn L.conjFun (fenchelConjugate n f) L.target ∧
      L.target ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
  let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  have _ : C.Nonempty := by
    simpa [C] using hC_nonempty
  change ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
      L.toFun = interiorGradientMap f hdiff ∧
      L.target = interiorGradientMap f hdiff '' C ∧
      Set.EqOn L.conjFun (fenchelConjugate n f) L.target ∧
      L.target ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)
  have hFiberWellDefined :
      ∀ ⦃x₁ x₂ xStar⦄,
        x₁ ∈ C →
        x₂ ∈ C →
        interiorGradientMap f hdiff x₁ = xStar →
        interiorGradientMap f hdiff x₂ = xStar →
        (((dotProduct x₁ xStar : ℝ) : EReal) - f x₁) =
          (((dotProduct x₂ xStar : ℝ) : EReal) - f x₂) := by
    intro x₁ x₂ xStar hx₁ hx₂ hx₁Star hx₂Star
    -- The fiber formula is inherited from the common `f*` value attached to the shared gradient.
    exact
      helperForTheorem_26_4_interiorGradient_fiber_well_defined
        (hf := hf) (hdiff := hdiff) hx₁ hx₂ hx₁Star hx₂Star
  have hValueEq :
      ∀ ⦃x⦄, x ∈ C →
        fenchelConjugate n f (interiorGradientMap f hdiff x) =
          (((dotProduct x (interiorGradientMap f hdiff x) : ℝ) : EReal) - f x) := by
    intro x hx
    -- On each source point, the package value is exactly the Fenchel-Young subtraction formula.
    exact
      helperForTheorem_26_4_fenchelConjugate_eq_dotSub_at_interiorGradient
        (hf := hf) (hdiff := hdiff) hx
  have hEqOn :
      Set.EqOn (fenchelConjugate n f) (fenchelConjugate n f) (interiorGradientMap f hdiff '' C) := by
    intro xStar hxStar
    rfl
  have hTargetSubset :
      interiorGradientMap f hdiff '' C ⊆
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
    -- Remark 5.24.2 places every gradient image point inside the effective domain of `f*`.
    simpa [C] using
      helperForTheorem_26_4_gradientImage_subset_effectiveDomain_fenchelConjugate
        (hf := hf) (hf_closed := hf_closed) (hdiff := hdiff)
  let L :
      LegendreConjugatePackageOn
        (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f :=
    { target := interiorGradientMap f hdiff '' C
      conjFun := fenchelConjugate n f
      toFun := interiorGradientMap f hdiff
      image_eq := rfl
      fiber_well_defined := hFiberWellDefined
      value_eq := hValueEq }
  -- Package the interior gradient map together with the conjugate function itself.
  refine ⟨L, rfl, rfl, ?_, ?_⟩
  · simpa [L] using hEqOn
  · simpa [L] using hTargetSubset

/-- An involutive Legendre-transform package is a bundled conjugacy package equipped with an
inverse map on the target set. -/
structure InvolutiveLegendreTransformationOn {X Y : Type*}
    (pair : X → Y → ℝ) (C : Set X) (f : X → EReal)
    extends LegendreConjugatePackageOn pair C f where
  invFun : Y → X
  left_inv : ∀ ⦃x⦄, x ∈ C → invFun (toFun x) = x
  inv_mem : ∀ ⦃xStar⦄, xStar ∈ target → invFun xStar ∈ C
  right_inv : ∀ ⦃xStar⦄, xStar ∈ target → toFun (invFun xStar) = xStar

/-- The standard Euclidean pairing on `ℝ^n`, used to specialize the generic Legendre data. -/
def euclideanPairing {n : ℕ} (x xStar : Fin n → ℝ) : ℝ :=
  dotProduct x xStar

/-- The Legendre-transform-type package associated to `f` is well-defined and involutory when the
effective domain of `∂ f` carries a bundled conjugacy package whose induced map `T` is exactly
the unique Euclidean representative of the subgradient at each point. -/
structure RealizesSubgradientOn {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (L : InvolutiveLegendreTransformationOn (euclideanPairing (n := n))
      (subdifferentialEffectiveDomain f) f) : Prop where
  convex : ConvexFunction f
  subgradient_mem :
    ∀ x ∈ subdifferentialEffectiveDomain f,
      dotProductEquiv ℝ (Fin n) (L.toFun x) ∈ subdifferentialAt f x
  subgradient_unique :
    ∀ ⦃x xStar⦄, x ∈ subdifferentialEffectiveDomain f →
      dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
        xStar = L.toFun x

/-- The Legendre-transform-type package associated to `f` is well-defined and involutory when
there exists a bundled conjugacy package on `dom ∂ f` whose chosen dual points are exactly the
unique Euclidean subgradients of `f`. -/
def LegendreWellDefinedInvolutory {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ∃ L : InvolutiveLegendreTransformationOn (euclideanPairing (n := n))
      (subdifferentialEffectiveDomain f) f,
    RealizesSubgradientOn f L

/-- Helper for Text 26.0.1: choose the unique Euclidean representative of the subgradient at
each point of `dom ∂ f`, and return `0` off that domain. -/
noncomputable def helperForText_26_0_1_selectedSubgradientVector {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (_hSVI : HasSingleValuedInjectiveSubdifferential f) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x =>
    if hx : x ∈ subdifferentialEffectiveDomain f then
      (dotProductEquiv ℝ (Fin n)).symm
        (Classical.choose
          ((helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty f x).1 hx))
    else
      0

/-- Helper for Text 26.0.1: on `dom ∂ f`, the selected Euclidean vector is a genuine
subgradient. -/
lemma helperForText_26_0_1_selectedSubgradient_mem {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hSVI : HasSingleValuedInjectiveSubdifferential f)
    {x : Fin n → ℝ} (hx : x ∈ subdifferentialEffectiveDomain f) :
    dotProductEquiv ℝ (Fin n)
        (helperForText_26_0_1_selectedSubgradientVector hSVI x) ∈
      subdifferentialAt f x := by
  -- On the effective domain, the selector was defined from a concrete subgradient witness.
  simpa [helperForText_26_0_1_selectedSubgradientVector, hx] using
    (Classical.choose_spec
      ((helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty f x).1 hx))

/-- Helper for Text 26.0.1: single-valuedness of `∂ f` identifies every Euclidean subgradient
with the selected one. -/
lemma helperForText_26_0_1_selectedSubgradient_unique {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hSVI : HasSingleValuedInjectiveSubdifferential f)
    {x xStar : Fin n → ℝ} (hx : x ∈ subdifferentialEffectiveDomain f)
    (hxStar :
      dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x) :
    xStar = helperForText_26_0_1_selectedSubgradientVector hSVI x := by
  -- The subdifferential at `x` is a subsingleton, so the two dual witnesses coincide.
  have hEqDual :
      dotProductEquiv ℝ (Fin n) xStar =
        dotProductEquiv ℝ (Fin n)
          (helperForText_26_0_1_selectedSubgradientVector hSVI x) :=
    hSVI.2.1 x hx hxStar (helperForText_26_0_1_selectedSubgradient_mem hSVI hx)
  -- Apply the Euclidean-dual equivalence to return to vector coordinates.
  exact (dotProductEquiv ℝ (Fin n)).injective hEqDual

/-- Helper for Text 26.0.1: injectivity of the subdifferential on `dom ∂ f` makes the selected
Euclidean subgradient map injective there as well. -/
lemma helperForText_26_0_1_selectedSubgradient_injectiveOnDomain {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hSVI : HasSingleValuedInjectiveSubdifferential f)
    {x y : Fin n → ℝ}
    (hx : x ∈ subdifferentialEffectiveDomain f)
    (hy : y ∈ subdifferentialEffectiveDomain f)
    (hxy :
      helperForText_26_0_1_selectedSubgradientVector hSVI x =
        helperForText_26_0_1_selectedSubgradientVector hSVI y) :
    x = y := by
  -- The common selected dual point belongs to both subdifferentials.
  have hxMem :
      dotProductEquiv ℝ (Fin n)
          (helperForText_26_0_1_selectedSubgradientVector hSVI x) ∈
        subdifferentialAt f x :=
    helperForText_26_0_1_selectedSubgradient_mem hSVI hx
  have hyMem :
      dotProductEquiv ℝ (Fin n)
          (helperForText_26_0_1_selectedSubgradientVector hSVI x) ∈
        subdifferentialAt f y := by
    simpa [hxy] using helperForText_26_0_1_selectedSubgradient_mem hSVI hy
  -- The injectivity clause of `HasSingleValuedInjectiveSubdifferential` now identifies `x` and `y`.
  exact hSVI.2.2 hx hy hxMem hyMem

-- Proof sketch: express the Legendre transformation through the conjugacy correspondence and
-- identify the well-defined involutory regime with single-valuedness and injectivity of `∂ f`.
/-- Text 26.0.1: for convex functions, the Legendre transformation is essentially well-defined
and involutory exactly in the regime where the subdifferential mapping is single-valued on its
effective domain and one-to-one there. -/
theorem legendreWellDefinedInvolutory_iff_hasSingleValuedInjectiveSubdifferential
    {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    LegendreWellDefinedInvolutory f ↔ HasSingleValuedInjectiveSubdifferential f := by
  constructor
  · intro hLegendre
    rcases hLegendre with ⟨L, hR⟩
    refine ⟨hR.convex, ?_, ?_⟩
    · intro x hx
      -- The realized Legendre map picks the unique Euclidean representative of `∂ f (x)`.
      intro g₁ hg₁ g₂ hg₂
      have hg₁Vec :
          (dotProductEquiv ℝ (Fin n)).symm g₁ = L.toFun x :=
        hR.subgradient_unique hx (by simpa using hg₁)
      have hg₂Vec :
          (dotProductEquiv ℝ (Fin n)).symm g₂ = L.toFun x :=
        hR.subgradient_unique hx (by simpa using hg₂)
      calc
        g₁ = dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm g₁) := by
          simp
        _ = dotProductEquiv ℝ (Fin n) (L.toFun x) := by rw [hg₁Vec]
        _ = dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm g₂) := by
          rw [hg₂Vec]
        _ = g₂ := by
          simp
    · intro x y g hx hy hgx hgy
      -- A common dual subgradient forces the Legendre images of `x` and `y` to agree.
      have hxVec :
          (dotProductEquiv ℝ (Fin n)).symm g = L.toFun x :=
        hR.subgradient_unique hx (by simpa using hgx)
      have hyVec :
          (dotProductEquiv ℝ (Fin n)).symm g = L.toFun y :=
        hR.subgradient_unique hy (by simpa using hgy)
      have hToFun : L.toFun x = L.toFun y := by
        rw [← hxVec, ← hyVec]
      -- Applying the inverse map on the target recovers the original primal points.
      calc
        x = L.invFun (L.toFun x) := by
          symm
          exact L.left_inv hx
        _ = L.invFun (L.toFun y) := by rw [hToFun]
        _ = y := by
          exact L.left_inv hy
  · intro hSVI
    let selected : (Fin n → ℝ) → (Fin n → ℝ) :=
      helperForText_26_0_1_selectedSubgradientVector hSVI
    let target : Set (Fin n → ℝ) := selected '' subdifferentialEffectiveDomain f
    let invFun : (Fin n → ℝ) → (Fin n → ℝ) :=
      fun xStar =>
        if hxStar : xStar ∈ target then
          Classical.choose hxStar
        else
          0
    let conjFun : (Fin n → ℝ) → EReal :=
      fun xStar =>
        if hxStar : xStar ∈ target then
          (((euclideanPairing (n := n) (invFun xStar) xStar : ℝ) : EReal) - f (invFun xStar))
        else
          0
    have hSelectedMem :
        ∀ ⦃x⦄, x ∈ subdifferentialEffectiveDomain f →
          dotProductEquiv ℝ (Fin n) (selected x) ∈ subdifferentialAt f x := by
      intro x hx
      -- The selected map reuses the dedicated subgradient witness on `dom ∂ f`.
      simpa [selected] using helperForText_26_0_1_selectedSubgradient_mem hSVI hx
    have hSelectedUnique :
        ∀ ⦃x xStar⦄, x ∈ subdifferentialEffectiveDomain f →
          dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
            xStar = selected x := by
      intro x xStar hx hxStar
      -- Single-valuedness of `∂ f` identifies any Euclidean witness with the chosen one.
      simpa [selected] using helperForText_26_0_1_selectedSubgradient_unique hSVI hx hxStar
    have hSelectedInjective :
        ∀ ⦃x y⦄, x ∈ subdifferentialEffectiveDomain f →
          y ∈ subdifferentialEffectiveDomain f →
            selected x = selected y →
              x = y := by
      intro x y hx hy hxy
      -- Injectivity of `∂ f` transfers directly to the chosen selector.
      simpa [selected] using
        helperForText_26_0_1_selectedSubgradient_injectiveOnDomain hSVI hx hy hxy
    have hTargetMem :
        ∀ ⦃x⦄, x ∈ subdifferentialEffectiveDomain f → selected x ∈ target := by
      intro x hx
      -- Every selected subgradient lies in the image set by construction.
      exact ⟨x, hx, rfl⟩
    have hLeftInv :
        ∀ ⦃x⦄, x ∈ subdifferentialEffectiveDomain f → invFun (selected x) = x := by
      intro x hx
      have hxTarget : selected x ∈ target := hTargetMem hx
      have hChosenMem : Classical.choose hxTarget ∈ subdifferentialEffectiveDomain f :=
        (Classical.choose_spec hxTarget).1
      have hChosenEq : selected (Classical.choose hxTarget) = selected x :=
        (Classical.choose_spec hxTarget).2
      -- The chosen preimage of `selected x` must be `x` because `selected` is injective on the domain.
      have hEq : Classical.choose hxTarget = x :=
        hSelectedInjective hChosenMem hx hChosenEq
      simpa [invFun, hxTarget] using hEq
    have hInvMem :
        ∀ ⦃xStar⦄, xStar ∈ target → invFun xStar ∈ subdifferentialEffectiveDomain f := by
      intro xStar hxStar
      -- On the target, `invFun` was defined by choosing a preimage from the domain.
      simpa [invFun, hxStar] using (Classical.choose_spec hxStar).1
    have hRightInv :
        ∀ ⦃xStar⦄, xStar ∈ target → selected (invFun xStar) = xStar := by
      intro xStar hxStar
      -- The chosen preimage carries exactly the defining image equality.
      simpa [invFun, hxStar] using (Classical.choose_spec hxStar).2
    have hFiberWellDefined :
        ∀ ⦃x₁ x₂ xStar⦄,
          x₁ ∈ subdifferentialEffectiveDomain f →
          x₂ ∈ subdifferentialEffectiveDomain f →
          selected x₁ = xStar →
          selected x₂ = xStar →
          (((euclideanPairing (n := n) x₁ xStar : ℝ) : EReal) - f x₁) =
            (((euclideanPairing (n := n) x₂ xStar : ℝ) : EReal) - f x₂) := by
      intro x₁ x₂ xStar hx₁ hx₂ hx₁Star hx₂Star
      -- Equal selected dual points force the primal points to agree, so the two values coincide.
      have hEq : x₁ = x₂ := hSelectedInjective hx₁ hx₂ (hx₁Star.trans hx₂Star.symm)
      subst hEq
      rfl
    have hValueEq :
        ∀ ⦃x⦄, x ∈ subdifferentialEffectiveDomain f →
          conjFun (selected x) =
            (((euclideanPairing (n := n) x (selected x) : ℝ) : EReal) - f x) := by
      intro x hx
      have hxTarget : selected x ∈ target := hTargetMem hx
      have hInvEq : invFun (selected x) = x := hLeftInv hx
      -- On image points, `conjFun` evaluates through the chosen inverse, which is `x`.
      simp [conjFun, hxTarget, hInvEq]
    let L :
        InvolutiveLegendreTransformationOn (euclideanPairing (n := n))
          (subdifferentialEffectiveDomain f) f :=
      { target := target
        conjFun := conjFun
        toFun := selected
        image_eq := rfl
        fiber_well_defined := hFiberWellDefined
        value_eq := hValueEq
        invFun := invFun
        left_inv := hLeftInv
        inv_mem := hInvMem
        right_inv := hRightInv }
    refine ⟨L, ?_⟩
    refine
      { convex := hSVI.1
        subgradient_mem := ?_
        subgradient_unique := ?_ }
    · intro x hx
      -- The packaged forward map is exactly the selected Euclidean subgradient.
      simpa [L, selected] using hSelectedMem hx
    · intro x xStar hx hxStar
      -- Uniqueness of the subdifferential determines the packaged Legendre image.
      simpa [L, selected] using hSelectedUnique hx hxStar

/-- Definition 26.1.1: a proper convex function `f` on `ℝ^n` is essentially smooth when, with
`C = int (dom f)`, one has (a) `C` nonempty, (b) `f` admits a unique Euclidean subgradient at
every point of `C`, encoded by a gradient map `grad`, and (c) for every sequence in `C`
converging to a boundary point of `C`, the norms `‖grad (xᵢ)‖` tend to `+∞`. For a smooth convex
function on all of `ℝ^n`, condition (c) is vacuous because then `C = univ`. -/
def IsEssentiallySmooth {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  let C := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
    C.Nonempty ∧
      ∃ grad : (Fin n → ℝ) → (Fin n → ℝ),
        (∀ x ∈ C, dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x) ∧
        (∀ ⦃x xStar⦄, x ∈ C →
          dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
            xStar = grad x) ∧
        ∀ (xSeq : ℕ → Fin n → ℝ) (x : Fin n → ℝ),
          (∀ i : ℕ, xSeq i ∈ C) →
          Filter.Tendsto xSeq Filter.atTop (nhds x) →
          x ∈ frontier C →
          Filter.Tendsto (fun i : ℕ => ‖grad (xSeq i)‖) Filter.atTop Filter.atTop

-- Proof sketch: combine the Chapter 25 characterization of differentiability by uniqueness of the
-- Euclidean subgradient with the Chapter 24 criterion that boundary and exterior points of a
-- closed proper convex function have empty subdifferential exactly off `int (dom f)`.
/-- Helper for Theorem 26.1: under global single-valuedness of `∂ f`, every interior point has a
canonically chosen Euclidean gradient vector, namely the gradient supplied by Theorem 25.1. -/
lemma helperForTheorem_26_1_interiorGradientData_of_singleValued
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hSV : IsSingleValuedMultivaluedMap (subdifferentialAt f)) :
    ∃ grad : (Fin n → ℝ) → (Fin n → ℝ),
      (∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x) ∧
      (∀ {x xStar}, x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
          xStar = grad x) := by
  let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hdiff :
      ∀ x ∈ C, ERealDifferentiableAt f x := by
    intro x hx
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      constructor
      · exact
          mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → ℝ))) (f := f) (interior_subset hx)
      · exact hproper.2.2 x (by simp)
    have h23_4 :=
      subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        f hproper x
    have hsubNonempty : Set.Nonempty (subdifferentialAt f x) :=
      ((h23_4.2.2.1).mpr hx).1
    rcases hsubNonempty with ⟨xStar, hxStar⟩
    have huniq :
        ∃! g : Fin n → ℝ, IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) g) := by
      refine ⟨(dotProductEquiv ℝ (Fin n)).symm xStar, ?_, ?_⟩
      · simpa using hxStar
      · intro g hg
        have hgMem : dotProductEquiv ℝ (Fin n) g ∈ subdifferentialAt f x := by
          simpa using hg
        have hEqDual :
            dotProductEquiv ℝ (Fin n) g = xStar :=
          hSV x hgMem hxStar
        have hEqDual' :
            dotProductEquiv ℝ (Fin n) g =
              dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
          simpa using hEqDual
        exact (dotProductEquiv ℝ (Fin n)).injective hEqDual'
    exact
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hfConv x hxFinite).2 huniq
  let grad : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun x =>
      if hx : x ∈ C then
        erealGradientAt (hdiff x hx)
      else
        0
  refine ⟨grad, ?_, ?_⟩
  · intro x hx
    -- On interior points, the chosen gradient is the unique Euclidean subgradient from Theorem 25.1.
    have hxC : x ∈ C := by
      simpa [C] using hx
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      constructor
      · exact
          mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → ℝ))) (f := f) (interior_subset hx)
      · exact hproper.2.2 x (by simp)
    have hcore :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hfConv x hxFinite).1 (hdiff x hxC)
    have hgradEq : grad x = erealGradientAt (hdiff x hxC) := by
      simp [grad, hxC]
    rw [hgradEq]
    exact hcore.1
  · intro x xStar hx hxStar
    -- Any competing interior Euclidean subgradient equals the chosen gradient by uniqueness.
    have hxC : x ∈ C := by
      simpa [C] using hx
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      constructor
      · exact
          mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → ℝ))) (f := f) (interior_subset hx)
      · exact hproper.2.2 x (by simp)
    have hcore :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hfConv x hxFinite).1 (hdiff x hxC)
    have hgradEq : grad x = erealGradientAt (hdiff x hxC) := by
      simp [grad, hxC]
    rw [hgradEq]
    exact hcore.2.2 xStar (by simpa using hxStar)

/-- Helper for Theorem 26.1: if `∂ f` is globally single-valued, then every point outside
`int (dom f)` has empty subdifferential. -/
lemma helperForTheorem_26_1_subdifferential_eq_empty_of_not_mem_interior_under_singleValued
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hSV : IsSingleValuedMultivaluedMap (subdifferentialAt f)) :
    ∀ x ∉ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
      subdifferentialAt f x = ∅ := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  intro x hxNotInt
  have h23_4 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      f hproper x
  by_contra hnonempty
  have hsubNonempty : Set.Nonempty (subdifferentialAt f x) :=
    Set.nonempty_iff_ne_empty.mpr hnonempty
  rcases hsubNonempty with ⟨xStar, hxStar⟩
  let g : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xStar
  have hpreimage_singleton :
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) = ({g} : Set (Fin n → ℝ)) := by
    ext v
    constructor
    · intro hv
      have hEqDual :
          dotProductEquiv ℝ (Fin n) v = xStar :=
        hSV x hv hxStar
      have hEqDual' : dotProductEquiv ℝ (Fin n) v = dotProductEquiv ℝ (Fin n) g := by
        simpa [g] using hEqDual
      have hEq : v = g := (dotProductEquiv ℝ (Fin n)).injective hEqDual'
      exact Set.mem_singleton_iff.mpr hEq
    · intro hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      simpa [g] using hxStar
  have hbounded :
      Bornology.IsBounded ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) := by
    simpa [hpreimage_singleton] using (Bornology.isBounded_singleton (x := g))
  exact hxNotInt ((h23_4.2.2.1).mp ⟨⟨xStar, hxStar⟩, hbounded⟩)

/-- Helper for Theorem 26.1: essential smoothness already packages the interior singleton fibers
of `∂ f` once one unpacks the chosen gradient field. -/
lemma helperForTheorem_26_1_singletonFiber_of_essentiallySmooth_on_interior
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hES : IsEssentiallySmooth f) :
    ∃ grad : (Fin n → ℝ) → (Fin n → ℝ),
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        subdifferentialAt f x = {dotProductEquiv ℝ (Fin n) (grad x)} := by
  rcases hES with ⟨_hproper, _hCne, grad, hgradMem, hgradUnique, _hblowup⟩
  refine ⟨grad, ?_⟩
  intro x hx
  -- The essential-smooth gradient is already the unique Euclidean subgradient on the interior.
  ext xStar
  constructor
  · intro hxStar
    have hEq : (dotProductEquiv ℝ (Fin n)).symm xStar = grad x := by
      exact hgradUnique hx (by simpa using hxStar)
    calc
      xStar = dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm xStar) := by
        simp
      _ = dotProductEquiv ℝ (Fin n) (grad x) := by rw [hEq]
  · intro hxStar
    rcases Set.mem_singleton_iff.mp hxStar with rfl
    exact hgradMem x hx

/-- Helper for Theorem 26.1: a nonnegative real sequence that does not tend to `+∞` admits a
strictly monotone bounded subsequence. -/
lemma helperForTheorem_26_1_exists_strictMono_boundedSubsequence_of_not_tendsto_atTop
    (a : ℕ → ℝ) (ha_nonneg : ∀ i : ℕ, 0 ≤ a i)
    (ha_not_tendsto : ¬ Filter.Tendsto a Filter.atTop Filter.atTop) :
    ∃ R ≥ 0, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, a (φ k) ≤ R := by
  -- Negating convergence to `atTop` gives one level that the sequence keeps revisiting below.
  rw [Filter.tendsto_atTop] at ha_not_tendsto
  rcases not_forall.mp ha_not_tendsto with ⟨R, hR⟩
  have hfreq : ∃ᶠ n : ℕ in Filter.atTop, a n < R := by
    simpa [Filter.Frequently, not_le] using hR
  rcases Filter.extraction_of_frequently_atTop hfreq with ⟨φ, hφ, hφlt⟩
  have hRnonneg : 0 ≤ R := by
    -- One extracted term lies both below `R` and above `0`, forcing `R` to be nonnegative.
    have h0le : 0 ≤ a (φ 0) := ha_nonneg (φ 0)
    have hlt : a (φ 0) < R := hφlt 0
    linarith
  refine ⟨R, hRnonneg, φ, hφ, ?_⟩
  intro k
  exact le_of_lt (hφlt k)

/-- Helper for Theorem 26.1: essential smoothness forbids finite gradient-limit vectors at a
frontier point of `int (dom f)`. -/
lemma helperForTheorem_26_1_gradientLimitVectors_eq_empty_of_essentiallySmooth_frontier
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hES : IsEssentiallySmooth f)
    {x : Fin n → ℝ}
    (hxFrontier :
      x ∈ frontier (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))) :
    gradientLimitVectorsAt f x = ∅ := by
  rcases hES with ⟨hproper, _hCne, grad, hgradMem, hgradUnique, hblowup⟩
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  ext g
  constructor
  · intro hg
    rcases hg with ⟨xSeq, hdiff, hxSeqTendsto, hgradTendsto⟩
    have hxSeqInt :
        ∀ i : ℕ, xSeq i ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      intro i
      -- Differentiability of a proper convex function forces the base point into `int (dom f)`.
      exact
        (convexFunction_proper_and_mem_interior_of_differentiableAt
          f hfConv (xSeq i) (hdiff i)).2
    have hgradEq :
        ∀ i : ℕ, erealGradientAt (hdiff i) = grad (xSeq i) := by
      intro i
      -- At each interior differentiability point, the essential-smooth gradient matches the true
      -- gradient because both are Euclidean subgradients.
      have hcore :=
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          f hfConv (xSeq i) (ERealDifferentiableAt.finiteAt (hdiff i))).1 (hdiff i)
      exact hgradUnique (hxSeqInt i) (by simpa using hcore.1)
    have hnormBlowup :
        Filter.Tendsto (fun i : ℕ => ‖erealGradientAt (hdiff i)‖)
          Filter.atTop Filter.atTop := by
      -- Rewrite Rockafellar's blow-up clause along the differentiability sequence.
      convert hblowup xSeq x hxSeqInt hxSeqTendsto hxFrontier using 1
      ext i
      rw [hgradEq i]
    have hnormTendsto :
        Filter.Tendsto (fun i : ℕ => ‖erealGradientAt (hdiff i)‖)
          Filter.atTop (nhds ‖g‖) := by
      -- Convergence of gradients forces convergence of their norms to the finite limit `‖g‖`.
      exact continuous_norm.continuousAt.tendsto.comp hgradTendsto
    have hEventuallyLarge :
        ∀ᶠ i : ℕ in Filter.atTop, ‖g‖ + 1 ≤ ‖erealGradientAt (hdiff i)‖ := by
      exact (Filter.tendsto_atTop.1 hnormBlowup) (‖g‖ + 1)
    have hEventuallySmall :
        ∀ᶠ i : ℕ in Filter.atTop, ‖erealGradientAt (hdiff i)‖ < ‖g‖ + 1 := by
      have hball :
          ∀ᶠ i : ℕ in Filter.atTop,
            ‖erealGradientAt (hdiff i)‖ ∈ Metric.ball ‖g‖ 1 := by
        exact hnormTendsto (Metric.ball_mem_nhds ‖g‖ zero_lt_one)
      filter_upwards [hball] with i hi
      have hdist : dist ‖erealGradientAt (hdiff i)‖ ‖g‖ < 1 := by
        simpa [Metric.mem_ball] using hi
      have habs : |‖erealGradientAt (hdiff i)‖ - ‖g‖| < 1 := by
        simpa [Real.dist_eq] using hdist
      have hupper : ‖erealGradientAt (hdiff i)‖ - ‖g‖ < 1 := (abs_lt.mp habs).2
      linarith
    have hEventuallyFalse : ∀ᶠ i : ℕ in Filter.atTop, False := by
      filter_upwards [hEventuallyLarge, hEventuallySmall] with i hiLarge hiSmall
      linarith
    have hbot : (Filter.atTop : Filter ℕ) = ⊥ :=
      (Filter.eventually_false_iff_eq_bot).1 hEventuallyFalse
    exact Filter.atTop_neBot.ne hbot
  · intro hg
    simp at hg

/-- Helper for Theorem 26.1: on a frontier domain point, Theorem 25.6 collapses the vectorized
subdifferential to `∅` once the boundary gradient-limit set is empty. -/
lemma helperForTheorem_26_1_boundarySubdifferential_eq_empty_of_essentiallySmooth_via_theorem25_6
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hES : IsEssentiallySmooth f)
    {x : Fin n → ℝ}
    (hxFrontier :
      x ∈ frontier (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)))
    (_hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :
    subdifferentialAt f x = ∅ := by
  have hES_data := hES
  rcases hES with ⟨_hproper, hCne, _grad, _hgradMem, _hgradUnique, _hblowup⟩
  have hgradLimitEmpty :
      gradientLimitVectorsAt f x = ∅ :=
    helperForTheorem_26_1_gradientLimitVectors_eq_empty_of_essentiallySmooth_frontier
      f hES_data hxFrontier
  have hpreimageEmpty :
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) = ∅ := by
    -- Theorem 25.6 reduces the boundary fiber to the gradient-limit term plus the normal cone.
    rw [closedProperConvex_subdifferential_preimage_eq_closure_convexHull_gradientLimitVectors_add_normalCone_preimage
      (f := f) hf hf_closed hCne x]
    rw [hgradLimitEmpty]
    simp
  ext xStar
  constructor
  · intro hxStar
    have hpre :
        (dotProductEquiv ℝ (Fin n)).symm xStar ∈
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) := by
      simpa using hxStar
    simpa [hpreimageEmpty] using hpre
  · intro hxStar
    simp at hxStar

/-- Helper for Theorem 26.1: the forward implication reduces to the boundary blow-up statement
once the interior gradient field and the exterior emptiness are known. -/
lemma helperForTheorem_26_1_boundaryGradientNormBlowup_of_singleValued
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hSV : IsSingleValuedMultivaluedMap (subdifferentialAt f))
    {grad : (Fin n → ℝ) → (Fin n → ℝ)}
    (hgradMem :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x)
    (_hgradUnique :
      ∀ {x xStar}, x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
          xStar = grad x) :
    ∀ (xSeq : ℕ → Fin n → ℝ) (x : Fin n → ℝ),
      (∀ i : ℕ, xSeq i ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) →
      Filter.Tendsto xSeq Filter.atTop (nhds x) →
      x ∈ frontier (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) →
      Filter.Tendsto (fun i : ℕ => ‖grad (xSeq i)‖) Filter.atTop Filter.atTop := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hfConv, hf_closed⟩
  intro xSeq x hxSeq hxSeqTendsto hxFrontier
  by_contra hNoBlowup
  have hnonneg : ∀ i : ℕ, 0 ≤ ‖grad (xSeq i)‖ := by
    intro i
    exact norm_nonneg (grad (xSeq i))
  rcases
      helperForTheorem_26_1_exists_strictMono_boundedSubsequence_of_not_tendsto_atTop
        (fun i : ℕ => ‖grad (xSeq i)‖) hnonneg hNoBlowup with
    ⟨R, _hRnonneg, φ, hφ, hφBound⟩
  have hsubseqMem :
      ∀ k : ℕ,
        grad (xSeq (φ k)) ∈ Metric.closedBall (0 : Fin n → ℝ) R := by
    intro k
    -- The bounded subsequence of gradients stays inside one compact closed ball.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hφBound k
  rcases (isCompact_closedBall (0 : Fin n → ℝ) R).tendsto_subseq hsubseqMem with
    ⟨g, _hgBall, ψ, hψ, hψTendsto⟩
  have hφψ : StrictMono (φ ∘ ψ) := hφ.comp hψ
  have hxCompTendsto :
      Filter.Tendsto (fun k : ℕ => xSeq ((φ ∘ ψ) k)) Filter.atTop (nhds x) := by
    -- Composing the original convergent primal sequence with strict-mono subsequences preserves
    -- convergence to the same boundary point.
    exact hxSeqTendsto.comp hφψ.tendsto_atTop
  have hsubMem :
      ∀ k : ℕ,
        dotProductEquiv ℝ (Fin n) (grad (xSeq ((φ ∘ ψ) k))) ∈
          subdifferentialAt f (xSeq ((φ ∘ ψ) k)) := by
    intro k
    exact hgradMem _ (hxSeq _)
  have hlimitMem :
      dotProductEquiv ℝ (Fin n) g ∈ subdifferentialAt f x := by
    -- The closed graph of `∂ f` transports the convergent gradient subsequence to a boundary
    -- subgradient at the limit point.
    exact
      (subdifferential_limit_mem_and_isClosed_graph (f := f) hclosed hproper).1
        (fun k : ℕ => xSeq ((φ ∘ ψ) k))
        (fun k : ℕ => grad (xSeq ((φ ∘ ψ) k)))
        hsubMem hxCompTendsto hψTendsto
  have hempty :
      subdifferentialAt f x = ∅ :=
    helperForTheorem_26_1_subdifferential_eq_empty_of_not_mem_interior_under_singleValued
      f hf hSV x (by simpa [interior_interior] using hxFrontier.2)
  simpa [hempty] using hlimitMem

/-- Helper for Theorem 26.1: essential smoothness gives the exterior-empty formula for `∂ f`; the
only nontrivial case is a boundary point of `int (dom f)`. -/
lemma helperForTheorem_26_1_subdifferential_eq_empty_of_not_mem_interior_of_essentiallySmooth
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hES : IsEssentiallySmooth f) :
    ∀ x ∉ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
      subdifferentialAt f x = ∅ := by
  have hES_data := hES
  rcases hES with ⟨hproper, hCne, _grad, _hgradMem, _hgradUnique, _hblowup⟩
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  intro x hxNotInt
  by_cases hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  · -- Route correction: rather than rebuilding the admissible-ray contradiction, use Theorem 25.6
    -- to reduce the boundary fiber to `cl (conv S(x))`, then show `S(x) = ∅` by the blow-up axiom.
    have hdomConv :
        Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hfConv
    have hxClosure : x ∈ closure C := by
      rw [hdomConv.closure_interior_eq_closure_of_nonempty_interior hCne]
      exact subset_closure hxDom
    have hxFrontier : x ∈ frontier C := by
      exact ⟨hxClosure, by simpa [C] using hxNotInt⟩
    exact
      helperForTheorem_26_1_boundarySubdifferential_eq_empty_of_essentiallySmooth_via_theorem25_6
        f hf hf_closed hES_data hxFrontier hxDom
  · -- Off the effective domain, Theorem 23.4 already forces the subdifferential to vanish.
    exact
      (subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        f hproper x).1 hxDom

/-- Theorem 26.1: for a closed proper convex function, the subdifferential mapping is
single-valued exactly when the function is essentially smooth. In that case there is a gradient
map `grad` on `int (dom f)` such that `∂ f(x)` is the singleton `{grad x}` on the interior of the
effective domain and `∂ f(x) = ∅` outside that interior. -/
theorem subdifferential_singleValued_iff_essentiallySmooth
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f) :
    (IsSingleValuedMultivaluedMap (subdifferentialAt f) ↔ IsEssentiallySmooth f) ∧
      (IsEssentiallySmooth f →
        ∃ grad : (Fin n → ℝ) → (Fin n → ℝ),
          (∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
            subdifferentialAt f x = {dotProductEquiv ℝ (Fin n) (grad x)}) ∧
          ∀ x ∉ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
            subdifferentialAt f x = ∅) := by
  -- First isolate the explicit singleton/empty fiber description supplied by essential smoothness.
  constructor
  · constructor
    · intro hSV
      have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
        helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
      have hfConv : ConvexFunction f := by
        simpa [ConvexFunction] using hproper.1
      rcases helperForTheorem_26_1_interiorGradientData_of_singleValued f hf hSV with
        ⟨grad, hgradMem, hgradUnique⟩
      refine ⟨hproper, ?_, ?_⟩
      · -- Start from a relative-interior point of `dom f`; the global emptiness lemma upgrades it to an interior point.
        rcases hf.1.2 with ⟨x0, hx0Finite⟩
        have hdomNonempty :
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f).Nonempty := by
          refine ⟨x0, ?_⟩
          rw [effectiveDomain_eq]
          simpa using lt_top_iff_ne_top.mpr hx0Finite
        have hdomConv :
            Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
          effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hfConv
        rcases
            helperForTheorem_21_1_riFin_nonempty_of_convex_nonempty
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hdomConv hdomNonempty with
          ⟨x, hxri⟩
        have hsubNonempty :
            Set.Nonempty (subdifferentialAt f x) :=
          (subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
            f hproper x).2.1 hxri |>.1
        by_contra hCempty
        have hempty :=
          helperForTheorem_26_1_subdifferential_eq_empty_of_not_mem_interior_under_singleValued
            f hf hSV x (by
              intro hxInt
              exact hCempty ⟨x, hxInt⟩)
        exact hsubNonempty.ne_empty (by simpa [hempty])
      · refine ⟨grad, hgradMem, ?_, ?_⟩
        · intro x xStar hx hxStar
          exact hgradUnique hx hxStar
        -- The only remaining ingredient in the forward implication is Rockafellar's boundary blow-up.
        exact
          helperForTheorem_26_1_boundaryGradientNormBlowup_of_singleValued
            f hf hf_closed hSV hgradMem hgradUnique
    · intro hES
      rcases helperForTheorem_26_1_singletonFiber_of_essentiallySmooth_on_interior f hES with
        ⟨grad, hsingleton⟩
      have hempty :=
        helperForTheorem_26_1_subdifferential_eq_empty_of_not_mem_interior_of_essentiallySmooth
          f hf hf_closed hES
      intro x
      by_cases hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
      · rw [hsingleton x hx]
        exact Set.subsingleton_singleton
      · rw [hempty x hx]
        exact Set.subsingleton_empty
  · intro hES
    rcases helperForTheorem_26_1_singletonFiber_of_essentiallySmooth_on_interior f hES with
      ⟨grad, hsingleton⟩
    refine ⟨grad, hsingleton, ?_⟩
    -- The only unresolved part is again the boundary/exterior emptiness formula.
    exact
      helperForTheorem_26_1_subdifferential_eq_empty_of_not_mem_interior_of_essentiallySmooth
        f hf hf_closed hES


end Section26
end Chap05

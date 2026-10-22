/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part10

section Chap05
section Section26

attribute [local instance] Classical.propDecidable
open scoped Topology ConvexAnalysis Pointwise

/-- Text 26.3.3.1: if `C` is a nonempty closed convex subset of `ℝ^n` and
`f(x) = inf { |x - y|^p | y ∈ C }` with `p > 1`, then `f` is a differentiable convex function on
`ℝ^n`, hence continuously differentiable. -/
theorem convexOn_differentiable_contDiffOne_infDist_rpow_of_nonempty_closed_convex
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {p : ℝ} (hp : 1 < p) :
    let f : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x => sInf ((fun y : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x y) p) '' C)
    ConvexOn ℝ Set.univ f ∧ Differentiable ℝ f ∧ ContDiff ℝ 1 f := by
  dsimp
  let f : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => sInf ((fun y : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x y) p) '' C)
  have hcore : ConvexOn ℝ Set.univ f ∧ Differentiable ℝ f := by
    -- First isolate the convexity/differentiability package coming from Corollary 26.3.2.
    simpa [f] using
      helperForText_26_3_3_1_convex_differentiable_core
        (C := C) hC_nonempty hC_closed hC_convex hp
  have hcontDiff : ContDiff ℝ 1 f := by
    -- Corollary 25.5.1 upgrades the already-obtained convex differentiable envelope to `C¹`.
    exact helperForText_26_3_3_1_contDiffOne_of_convex_differentiable hcore.1 hcore.2
  exact ⟨hcore.1, hcore.2, hcontDiff⟩

-- Proof sketch: a convex function that is differentiable on all of `ℝ^n` is essentially smooth,
-- because `int (dom f) = univ` and the boundary-growth clause is vacuous. The kernel positivity
-- condition on `recessionFunction f` rules out the obstruction in Corollary 16.2.1, so the range
-- of `A*` meets `ri (dom f*)`; Corollary 26.3.3 then yields essential smoothness of `A f`,
-- which here is exactly convexity together with differentiability at every point of `ℝ^m`.
/-- Helper for Text 26.3.3.2: package global differentiability into the proper, closed, and
essentially smooth hypotheses needed before invoking Corollary 26.3.3. -/
lemma helperForText_26_3_3_2_closedProper_and_essentiallySmooth_of_convex_and_everywhereDifferentiable
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hconv : ConvexFunction f)
    (hdiff : ∀ x : Fin n → ℝ, ERealDifferentiableAt f x) :
    ProperConvexERealFunction (F := (Fin n → ℝ)) f ∧
      LowerSemicontinuous f ∧
      IsEssentiallySmooth f := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    -- Everywhere differentiability makes `f` finite everywhere, so `f` is proper on `univ`.
    refine ⟨hconv, ?_, ?_⟩
    · apply (nonempty_epigraph_iff_nonempty_effectiveDomain (Set.univ : Set (Fin n → ℝ)) f).2
      refine ⟨0, ?_⟩
      rw [effectiveDomain_eq]
      exact ⟨by simp, lt_top_iff_ne_top.mpr (ERealDifferentiableAt.finiteAt (hdiff 0)).1⟩
    · intro x hx
      exact (ERealDifferentiableAt.finiteAt (hdiff x)).2
  have hproperEReal : ProperConvexERealFunction (F := (Fin n → ℝ)) f :=
    helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ f hproper
  have hdom : effectiveDomain (Set.univ : Set (Fin n → ℝ)) f = Set.univ := by
    -- Finiteness at every point forces the effective domain to be the whole space.
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      rw [effectiveDomain_eq]
      exact ⟨by simp, lt_top_iff_ne_top.mpr (ERealDifferentiableAt.finiteAt (hdiff x)).1⟩
  have hrealDiff : Differentiable ℝ (fun x => (f x).toReal) :=
    helperForText_26_3_3_1_realDifferentiable_of_ERealDifferentiable_everywhere
      (fun x => ERealDifferentiableAt.finiteAt (hdiff x)) hdiff
  have hclosed : LowerSemicontinuous f := by
    have hcontToReal : Continuous (fun x => (f x).toReal) := hrealDiff.continuous
    have hcontOn : ContinuousOn f Set.univ := by
      exact continuousOn_ereal_of_toReal (f := f) hcontToReal.continuousOn
        (fun x hx =>
          ⟨(ERealDifferentiableAt.finiteAt (hdiff x)).2,
            (ERealDifferentiableAt.finiteAt (hdiff x)).1⟩)
    have hcont : Continuous f := by
      simpa [continuousOn_univ] using hcontOn
    exact hcont.lowerSemicontinuous
  have hsingle : IsSingleValuedMultivaluedMap (subdifferentialAt f) := by
    -- Differentiability identifies a unique Euclidean subgradient at each point.
    intro x xStar₁ hx₁ xStar₂ hx₂
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := ERealDifferentiableAt.finiteAt (hdiff x)
    have huniq :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient f hconv x hxFinite).1
        (hdiff x)
    have hx₁' : (dotProductEquiv ℝ (Fin n)).symm xStar₁ = erealGradientAt (hdiff x) := by
      exact huniq.2.2 _ (by simpa using hx₁)
    have hx₂' : (dotProductEquiv ℝ (Fin n)).symm xStar₂ = erealGradientAt (hdiff x) := by
      exact huniq.2.2 _ (by simpa using hx₂)
    exact by
      simpa using congrArg (dotProductEquiv ℝ (Fin n)) (hx₁'.trans hx₂'.symm)
  exact ⟨hproperEReal, hclosed,
    ((subdifferential_singleValued_iff_essentiallySmooth (f := f) hproperEReal hclosed).1).1
      hsingle⟩

/-- Helper for Text 26.3.3.2: the kernel-positivity hypothesis removes the Corollary 16.2.1
obstruction, so the range of `A*` meets `ri (dom f*)`. -/
lemma helperForText_26_3_3_2_coordinateAdjoint_meets_relativeInterior_conjugateDomain
    {n m : ℕ} {f : (Fin n → ℝ) → EReal} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)}
    (hconv : ConvexFunction f)
    (hdiff : ∀ x : Fin n → ℝ, ERealDifferentiableAt f x)
    (hker :
      ∀ x : Fin n → ℝ, A x = 0 → x ≠ 0 → recessionFunction f x > (0 : EReal)) :
    ∃ yStar : Fin m → ℝ,
      coordinateAdjointLinearMap A yStar ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
  rcases
      helperForText_26_3_3_2_closedProper_and_essentiallySmooth_of_convex_and_everywhereDifferentiable
        hconv hdiff with
    ⟨hf, hf_closed, -⟩
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hconjProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hneBot : ∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal) := by
    intro x
    exact hf.1.1 x
  have hbiconj : fenchelConjugate n (fenchelConjugate n f) = f :=
    fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := f) hf_closed hconv hneBot
  have hnotBad :
      ¬ ∃ xStar : EuclideanSpace ℝ (Fin n),
          (LinearMap.adjoint
              (helperForTheorem_23_9_euclideanLinearLift (coordinateAdjointLinearMap A))) xStar =
            0 ∧
          recessionFunction (fenchelConjugate n (fenchelConjugate n f)) (xStar : Fin n → ℝ) ≤
            (0 : EReal) ∧
          recessionFunction (fenchelConjugate n (fenchelConjugate n f)) (-xStar : Fin n → ℝ) >
            (0 : EReal) := by
    intro hbad
    rcases hbad with ⟨xStarE, hAdjZero, hrecession_le, hrecession_pos⟩
    let xStar : Fin n → ℝ := (xStarE : Fin n → ℝ)
    have hA_zero : A xStar = 0 := by
      -- The Euclidean adjoint equation for `A*` rewrites back to the kernel condition for `A`.
      apply dotProduct_eq_zero
      intro y
      have hdotAdj :=
        section16_dotProduct_map_eq_dotProduct_adjoint
          (A := helperForTheorem_23_9_euclideanLinearLift (coordinateAdjointLinearMap A))
          (x := y) (yStar := xStar)
      have hAdjZero' :
          (((LinearMap.adjoint
                (helperForTheorem_23_9_euclideanLinearLift (coordinateAdjointLinearMap A)))
              xStarE) : Fin m → ℝ) = 0 := by
        simpa using hAdjZero
      have hdotAdjZero : dotProduct (coordinateAdjointLinearMap A y) xStar = 0 := by
        calc
          dotProduct (coordinateAdjointLinearMap A y) xStar =
              dotProduct y
                ((((LinearMap.adjoint
                    (helperForTheorem_23_9_euclideanLinearLift (coordinateAdjointLinearMap A)))
                  xStarE) : EuclideanSpace ℝ (Fin m)) : Fin m → ℝ) := by
                simpa [xStar, helperForTheorem_23_9_euclideanLinearLift] using hdotAdj
          _ = 0 := by simp [hAdjZero']
      calc
        dotProduct (A xStar) y = dotProduct xStar (coordinateAdjointLinearMap A y) := by
          exact helperForCorollary_26_3_3_dotProduct_coordinateAdjoint A xStar y
        _ = dotProduct (coordinateAdjointLinearMap A y) xStar := by rw [dotProduct_comm]
        _ = 0 := hdotAdjZero
    by_cases hxZero : xStar = 0
    · -- If the obstructing vector is `0`, Corollary 16.2.1 asks for the impossible `0 > 0`.
      have hrecession_le' : recessionFunction f 0 ≤ (0 : EReal) := by
        simpa [hbiconj, xStar, hxZero] using hrecession_le
      have hrecession_pos' : recessionFunction f 0 > (0 : EReal) := by
        simpa [hbiconj, xStar, hxZero] using hrecession_pos
      exact (not_lt_of_ge hrecession_le') hrecession_pos'
    · -- If the obstructing vector is nonzero, the textbook kernel-positivity hypothesis rules it out.
      have hxPos : recessionFunction f xStar > (0 : EReal) := hker xStar hA_zero hxZero
      have hrecession_le' : recessionFunction f xStar ≤ (0 : EReal) := by
        simpa [hbiconj, xStar] using hrecession_le
      exact (not_lt_of_ge hrecession_le') hxPos
  have hsec :=
    (section16_exists_image_mem_ri_effectiveDomain_iff_not_exists_adjoint_eq_zero_recession_ineq
      (A := helperForTheorem_23_9_euclideanLinearLift (coordinateAdjointLinearMap A))
      (g := fenchelConjugate n f) hconjProper).1 hnotBad
  rcases hsec with ⟨yStarE, hyStarE⟩
  -- Translate the Euclidean-space witness back to coordinate space.
  refine ⟨(yStarE : Fin m → ℝ), ?_⟩
  exact
    (mem_euclideanRelativeInterior_fin_iff
      (n := n)
      (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))
      (x := coordinateAdjointLinearMap A (yStarE : Fin m → ℝ))).2
    (by
      simpa [helperForTheorem_23_9_euclideanLinearLift,
        helperForTheorem_23_4_preimage_eq_symmImage] using hyStarE)

/-- Helper for Text 26.3.3.2: essential smoothness of the image plus surjectivity gives a finite
value on every fiber, so `A f` is finite everywhere. -/
lemma helperForText_26_3_3_2_finiteEverywhere_of_essentiallySmooth_imageUnderLinearMap
    {n m : ℕ} {f : (Fin n → ℝ) → EReal} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)}
    (hA : Function.Surjective A)
    (hdiff : ∀ x : Fin n → ℝ, ERealDifferentiableAt f x)
    (hSmooth : IsEssentiallySmooth (imageUnderLinearMap A f)) :
    ∀ y, imageUnderLinearMap A f y ≠ ⊤ ∧ imageUnderLinearMap A f y ≠ ⊥ := by
  rcases hSmooth with ⟨hproper, -, -, -, -, -⟩
  intro y
  constructor
  · rcases hA y with ⟨x, rfl⟩
    intro hyTop
    have hxle : imageUnderLinearMap A f (A x) ≤ f x := by
      -- The chosen preimage `x` gives one admissible value in the infimum defining `A f (A x)`.
      unfold imageUnderLinearMap
      exact csInf_le (by
          refine ⟨⊥, ?_⟩
          rintro z ⟨w, hw, rfl⟩
          exact bot_le)
        (by exact ⟨x, rfl, rfl⟩)
    have hxf : f x ≠ ⊤ := (ERealDifferentiableAt.finiteAt (hdiff x)).1
    exact hxf (top_unique (hyTop ▸ hxle))
  · -- Properness coming from essential smoothness rules out `-∞` everywhere.
    exact hproper.2.2 y (by simp)

/-- Helper for Text 26.3.3.2: once the effective domain is all of `ℝ^m`, essential smoothness is
exactly global convexity plus differentiability at every point. -/
lemma helperForText_26_3_3_2_convex_and_everywhereDifferentiable_of_essentiallySmooth_and_finiteEverywhere
    {m : ℕ} {g : (Fin m → ℝ) → EReal}
    (hsmooth : IsEssentiallySmooth g)
    (hfinite : ∀ y, g y ≠ ⊤ ∧ g y ≠ ⊥) :
    ConvexFunction g ∧ ∀ y, ERealDifferentiableAt g y := by
  rcases hsmooth with ⟨hproper, -, grad, hgradMem, hgradUnique, -⟩
  have hconv : ConvexFunction g := by
    simpa [ConvexFunction] using hproper.1
  have hdom : effectiveDomain (Set.univ : Set (Fin m → ℝ)) g = Set.univ := by
    -- The finite-everywhere hypothesis collapses the effective domain to `univ`.
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      rw [effectiveDomain_eq]
      exact ⟨by simp, lt_top_iff_ne_top.mpr (hfinite y).1⟩
  refine ⟨hconv, ?_⟩
  intro y
  have hyInterior : y ∈ interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) := by
    simp [hdom]
  -- With `int (dom g) = univ`, the unique subgradient data from essential smoothness is global.
  refine
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient g hconv y (hfinite y)).2
      ?_
  refine ⟨grad y, ?_, ?_⟩
  · simpa [hdom] using hgradMem y hyInterior
  · intro z hz
    exact hgradUnique hyInterior (by simpa using hz)

/-- Text 26.3.3.2: if `f` is a differentiable convex function on `ℝ^n` and
`A : ℝ^n → ℝ^m` is onto such that `A x = 0` and `x ≠ 0` imply `(f₀⁺)(x) > 0`, then the image
function `A f` is a differentiable convex function on `ℝ^m`. -/
theorem imageUnderLinearMap_convex_and_differentiable_of_positive_recession_on_kernel
    {n m : ℕ} (f : (Fin n → ℝ) → EReal) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hconv : ConvexFunction f)
    (hdiff : ∀ x : Fin n → ℝ, ERealDifferentiableAt f x)
    (hA : Function.Surjective A)
    (hker :
      ∀ x : Fin n → ℝ, A x = 0 → x ≠ 0 → recessionFunction f x > (0 : EReal)) :
    ConvexFunction (imageUnderLinearMap A f) ∧
      ∀ y : Fin m → ℝ, ERealDifferentiableAt (imageUnderLinearMap A f) y := by
  rcases
      helperForText_26_3_3_2_closedProper_and_essentiallySmooth_of_convex_and_everywhereDifferentiable
        hconv hdiff with
    ⟨hf, hf_closed, hf_smooth⟩
  have hri :=
    helperForText_26_3_3_2_coordinateAdjoint_meets_relativeInterior_conjugateDomain
      hconv hdiff hker
  have hImageSmooth : IsEssentiallySmooth (imageUnderLinearMap A f) :=
    essentiallySmooth_imageUnderLinearMap_of_surjective_and_adjoint_mem_relativeInterior_conjugateEffectiveDomain
      f A hf hf_closed hf_smooth hA hri
  have hImageFinite :=
    helperForText_26_3_3_2_finiteEverywhere_of_essentiallySmooth_imageUnderLinearMap
      hA hdiff hImageSmooth
  -- Corollary 26.3.3 gives essential smoothness of `A f`; full-domain finiteness turns that into
  -- the textbook conclusion of global convexity and differentiability.
  exact
    helperForText_26_3_3_2_convex_and_everywhereDifferentiable_of_essentiallySmooth_and_finiteEverywhere
      hImageSmooth hImageFinite

/-- The open positive quadrant in `ℝ²`, written in coordinates `(ξ₁, ξ₂)`. -/
def openPositiveQuadrantR2 : Set (Fin 2 → ℝ) :=
  {x | 0 < x 0 ∧ 0 < x 1}

/-- The non-negative `ξ₁`-axis in `ℝ²`, i.e. the points with `ξ₂ = 0` and `ξ₁ ≥ 0`. -/
def nonnegativeXi1AxisR2 : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ x 0 ∧ x 1 = 0}

/-- The convex function `f(ξ₁, ξ₂) = ξ₂^2 / (2 ξ₁) - 2 √ξ₂` on `ξ₁ > 0`, `ξ₂ ≥ 0`, extended by
`0` at the origin and by `+∞` elsewhere. -/
noncomputable def quadraticOverLinearMinusSqrtFunction : (Fin 2 → ℝ) → EReal :=
  fun x =>
    if 0 < x 0 ∧ 0 ≤ x 1 then
      (((x 1) ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ) : EReal)
    else if x = 0 then
      (0 : EReal)
    else
      ⊤

/-- Helper for Example 26.2.1: the effective domain is the open-right/nonnegative-upper region
plus the origin, and the function vanishes on the nonnegative `ξ₁`-axis. -/
lemma helperForExample_26_2_1_effectiveDomain_and_axisValues :
    effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction =
        {x | 0 < x 0 ∧ 0 ≤ x 1} ∪ ({0} : Set (Fin 2 → ℝ)) ∧
      Set.EqOn (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal)
        (fun _ : Fin 2 → ℝ => (0 : ℝ)) nonnegativeXi1AxisR2 := by
  constructor
  · -- Unfolding the piecewise definition leaves only the finite branches.
    ext x
    constructor
    · intro hx
      rw [effectiveDomain_eq] at hx
      rcases hx with ⟨_, hfinite⟩
      by_cases hbranch : 0 < x 0 ∧ 0 ≤ x 1
      · exact Or.inl hbranch
      · by_cases hx0 : x = 0
        · exact Or.inr hx0
        · simp [quadraticOverLinearMinusSqrtFunction, hbranch, hx0] at hfinite
    · intro hx
      rcases hx with hbranch | hx0
      · rcases hbranch with ⟨hx0, hx1⟩
        refine ⟨x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1), ?_⟩
        change Set.univ x ∧
          quadraticOverLinearMinusSqrtFunction x ≤
            (((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ) : EReal))
        constructor
        · exact Set.mem_univ x
        · simpa [quadraticOverLinearMinusSqrtFunction, hx0, hx1] using
            (le_rfl :
              ((((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ) : EReal))) ≤
                (((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ) : EReal)))
      · rcases hx0 with rfl
        refine ⟨0, ?_⟩
        change Set.univ (0 : Fin 2 → ℝ) ∧ quadraticOverLinearMinusSqrtFunction 0 ≤ (0 : EReal)
        constructor
        · exact Set.mem_univ 0
        · simp [quadraticOverLinearMinusSqrtFunction]
  · intro x hx
    rcases hx with ⟨hx0, hx1⟩
    by_cases hpos : 0 < x 0
    · have hbranch : 0 < x 0 ∧ 0 ≤ x 1 := by
        refine ⟨hpos, ?_⟩
        simp [hx1]
      -- Positive axis points lie in the first finite branch, where the formula reduces to `0`.
      simp [quadraticOverLinearMinusSqrtFunction, hbranch, hx1]
    · have hx0zero : x 0 = 0 := le_antisymm (not_lt.mp hpos) hx0
      have hxEqZero : x = 0 := by
        -- The nonpositive axis point in `dom f` is necessarily the origin.
        ext i
        fin_cases i <;> simp [hx0zero, hx1]
      -- At the origin we use the exceptional branch `f(0, 0) = 0`.
      simp [quadraticOverLinearMinusSqrtFunction, hxEqZero]

/-- Helper for Example 26.2.1: the constant zero restriction on the nonnegative `ξ₁`-axis gives a
direct witness that the function is not strictly convex on its whole effective domain. -/
lemma helperForExample_26_2_1_not_strictConvexOn_effectiveDomain :
    ¬ StrictConvexOn ℝ
      (effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction)
      (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal) := by
  intro hstrict
  have hx :
      (0 : Fin 2 → ℝ) ∈
        effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction := by
    -- The origin is the exceptional finite point in the definition.
    simp [effectiveDomain_eq, quadraticOverLinearMinusSqrtFunction]
  let y : Fin 2 → ℝ := ![1, 0]
  have hy :
      y ∈ effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction := by
    -- Positive `ξ₁` and zero `ξ₂` keep `y` in the first finite branch.
    simp [y, effectiveDomain_eq, quadraticOverLinearMinusSqrtFunction]
  have hxy : (0 : Fin 2 → ℝ) ≠ y := by
    intro hEq
    have hcoord := congrArg (fun z : Fin 2 → ℝ => z 0) hEq
    simp [y] at hcoord
  have hlt :=
    hstrict.2 hx hy hxy
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (by norm_num)
  -- Evaluating the strict convexity inequality on the axis midpoint reduces immediately to
  -- the contradiction `0 < 0`.
  norm_num [y, quadraticOverLinearMinusSqrtFunction] at hlt

/-- Helper for Example 26.2.1: on the open positive quadrant, the function is given by its
explicit real-valued branch. -/
lemma helperForExample_26_2_1_value_on_openQuadrant
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    quadraticOverLinearMinusSqrtFunction x =
      (((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ)) : EReal) := by
  rcases hx with ⟨hx0, hx1⟩
  have hbranch : 0 < x 0 ∧ 0 ≤ x 1 := ⟨hx0, le_of_lt hx1⟩
  -- On interior points we are entirely inside the first finite branch of the definition.
  simp [quadraticOverLinearMinusSqrtFunction, hbranch]

/-- Helper for Example 26.2.1: the textbook perturbation `x + (t^3, t^2)` of an axis point lands
in the open positive quadrant whenever `t > 0`. -/
lemma helperForExample_26_2_1_axisPerturbation_mem_openQuadrant
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegativeXi1AxisR2) {t : ℝ} (ht : 0 < t) :
    x + ![t ^ 3, t ^ 2] ∈ openPositiveQuadrantR2 := by
  rcases hx with ⟨hx0, hx1⟩
  constructor
  · -- The first coordinate picks up the strictly positive `t^3` term.
    have ht3 : 0 < t ^ 3 := by positivity
    simpa using add_pos_of_nonneg_of_pos hx0 ht3
  · have ht2 : 0 < t ^ 2 := by positivity
    -- The second coordinate becomes exactly `t^2`, so it is strictly positive.
    simp [hx1, ht2]

/-- Helper for Example 26.2.1: along the axis perturbation `x + (t^3, t^2)`, the function takes
the explicit textbook value `t^4 / (2 (ξ₁ + t^3)) - 2 t`. -/
lemma helperForExample_26_2_1_axisPerturbation_value
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegativeXi1AxisR2) {t : ℝ} (ht : 0 < t) :
    quadraticOverLinearMinusSqrtFunction (x + ![t ^ 3, t ^ 2]) =
      (((t ^ 4 / (2 * (x 0 + t ^ 3)) - 2 * t : ℝ)) : EReal) := by
  rcases hx with ⟨hx0, hx1⟩
  have hmem :
      x + ![t ^ 3, t ^ 2] ∈ openPositiveQuadrantR2 :=
    helperForExample_26_2_1_axisPerturbation_mem_openQuadrant ⟨hx0, hx1⟩ ht
  have ht_nonneg : 0 ≤ t := le_of_lt ht
  -- Rewrite through the interior branch, then simplify the perturbed coordinates explicitly.
  rw [helperForExample_26_2_1_value_on_openQuadrant hmem]
  have hreal :
      ((x + ![t ^ 3, t ^ 2]) 1 ^ 2 / (2 * (x + ![t ^ 3, t ^ 2]) 0) -
        2 * Real.sqrt ((x + ![t ^ 3, t ^ 2]) 1) : ℝ) =
      (t ^ 4 / (2 * (x 0 + t ^ 3)) - 2 * t : ℝ) := by
    calc
      (x + ![t ^ 3, t ^ 2]) 1 ^ 2 / (2 * (x + ![t ^ 3, t ^ 2]) 0) -
          2 * Real.sqrt ((x + ![t ^ 3, t ^ 2]) 1) =
        (t ^ 2) ^ 2 / (2 * (x 0 + t ^ 3)) - 2 * Real.sqrt (t ^ 2) := by
          simp [hx1]
      _ = (t ^ 2) ^ 2 / (2 * (x 0 + t ^ 3)) - 2 * t := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
      _ = t ^ 4 / (2 * (x 0 + t ^ 3)) - 2 * t := by
          ring_nf
  exact congrArg (fun r : ℝ => (r : EReal)) hreal

/-- Helper for Example 26.2.1: on the nonnegative `ξ₁`-axis, the original `EReal`-valued
function itself is identically zero. -/
lemma helperForExample_26_2_1_value_on_nonnegativeXi1Axis
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegativeXi1AxisR2) :
    quadraticOverLinearMinusSqrtFunction x = (0 : EReal) := by
  rcases hx with ⟨hx0, hx1⟩
  by_cases hpos : 0 < x 0
  · have hbranch : 0 < x 0 ∧ 0 ≤ x 1 := by
      refine ⟨hpos, ?_⟩
      simp [hx1]
    -- Positive axis points lie in the finite branch, where `ξ₂ = 0` collapses the value to `0`.
    simp [quadraticOverLinearMinusSqrtFunction, hbranch, hx1]
  · have hx0zero : x 0 = 0 := le_antisymm (not_lt.mp hpos) hx0
    have hxEqZero : x = 0 := by
      -- The only nonpositive point on the nonnegative axis is the origin.
      ext i
      fin_cases i <;> simp [hx0zero, hx1]
    -- At the origin the exceptional branch again gives value `0`.
    simp [quadraticOverLinearMinusSqrtFunction, hxEqZero]

end Section26
end Chap05

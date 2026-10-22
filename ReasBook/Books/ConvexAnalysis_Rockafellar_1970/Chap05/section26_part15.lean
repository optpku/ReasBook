/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part14

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- The convex function `f(ξ₁, ξ₂) = ξ₂^2 / (2 ξ₁) + ξ₂^2` on `ξ₁ > 0`, `ξ₂ ≥ 0`, extended by
`0` at the origin and by `+∞` elsewhere. -/
noncomputable def quadraticOverLinearPlusSquareFunction : (Fin 2 → ℝ) → EReal :=
  fun x =>
    if 0 < x 0 ∧ 0 ≤ x 1 then
      (((x 1) ^ 2 / (2 * x 0) + (x 1) ^ 2 : ℝ) : EReal)
    else if x = 0 then
      (0 : EReal)
    else
      ⊤

/-- Helper for Example 26.2.2: the effective domain is the open-right/nonnegative-upper region
plus the origin, and the function vanishes on the nonnegative `ξ₁`-axis. -/
lemma helperForExample_26_2_2_effectiveDomain_eq_and_axisValues :
    effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearPlusSquareFunction =
        {x | 0 < x 0 ∧ 0 ≤ x 1} ∪ ({0} : Set (Fin 2 → ℝ)) ∧
      Set.EqOn (fun x => (quadraticOverLinearPlusSquareFunction x).toReal)
        (fun _ : Fin 2 → ℝ => (0 : ℝ)) nonnegativeXi1AxisR2 := by
  constructor
  · -- Unfolding the piecewise definition leaves only the finite branch and the exceptional origin.
    ext x
    constructor
    · intro hx
      rw [effectiveDomain_eq] at hx
      rcases hx with ⟨_, hfinite⟩
      by_cases hbranch : 0 < x 0 ∧ 0 ≤ x 1
      · exact Or.inl hbranch
      · by_cases hx0 : x = 0
        · exact Or.inr hx0
        · simp [quadraticOverLinearPlusSquareFunction, hbranch, hx0] at hfinite
    · intro hx
      rcases hx with hbranch | hx0
      · rcases hbranch with ⟨hx0, hx1⟩
        refine ⟨x 1 ^ 2 / (2 * x 0) + x 1 ^ 2, ?_⟩
        constructor
        · exact Set.mem_univ x
        · simpa [quadraticOverLinearPlusSquareFunction, hx0, hx1] using
            (show
                ((((x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 : ℝ)) : EReal)) ≤
                  (((x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 : ℝ) : EReal))
              from le_rfl)
      · rcases hx0 with rfl
        refine ⟨0, ?_⟩
        constructor
        · exact Set.mem_univ 0
        · simp [quadraticOverLinearPlusSquareFunction]
  · intro x hx
    rcases hx with ⟨hx0, hx1⟩
    by_cases hpos : 0 < x 0
    · have hbranch : 0 < x 0 ∧ 0 ≤ x 1 := by
        refine ⟨hpos, ?_⟩
        simp [hx1]
      -- On positive axis points the real formula collapses to zero because `ξ₂ = 0`.
      simp [quadraticOverLinearPlusSquareFunction, hbranch, hx1]
    · have hx0zero : x 0 = 0 := le_antisymm (not_lt.mp hpos) hx0
      have hxEqZero : x = 0 := by
        -- The only nonpositive point on the nonnegative axis is the origin.
        ext i
        fin_cases i <;> simp [hx0zero, hx1]
      -- At the origin we use the exceptional branch `f(0, 0) = 0`.
      simp [quadraticOverLinearPlusSquareFunction, hxEqZero]

/-- Helper for Example 26.2.2: on the open positive quadrant, the piecewise function agrees with
its explicit real-valued branch. -/
lemma helperForExample_26_2_2_value_on_openQuadrant
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    quadraticOverLinearPlusSquareFunction x =
      (((x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 : ℝ)) : EReal) := by
  rcases hx with ⟨hx0, hx1⟩
  have hbranch : 0 < x 0 ∧ 0 ≤ x 1 := ⟨hx0, le_of_lt hx1⟩
  -- Inside the open quadrant the first finite branch is active.
  simp [quadraticOverLinearPlusSquareFunction, hbranch]

/-- Helper for Example 26.2.2: the original `EReal`-valued function is identically zero on the
nonnegative `ξ₁`-axis. -/
lemma helperForExample_26_2_2_value_on_nonnegativeXi1Axis
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegativeXi1AxisR2) :
    quadraticOverLinearPlusSquareFunction x = (0 : EReal) := by
  rcases hx with ⟨hx0, hx1⟩
  by_cases hpos : 0 < x 0
  · have hbranch : 0 < x 0 ∧ 0 ≤ x 1 := by
      refine ⟨hpos, ?_⟩
      simp [hx1]
    -- Positive axis points again lie in the first finite branch, where `ξ₂ = 0`.
    simp [quadraticOverLinearPlusSquareFunction, hbranch, hx1]
  · have hx0zero : x 0 = 0 := le_antisymm (not_lt.mp hpos) hx0
    have hxEqZero : x = 0 := by
      -- The only nonpositive point on the nonnegative axis is the origin.
      ext i
      fin_cases i <;> simp [hx0zero, hx1]
    -- At the origin the exceptional branch gives the value zero.
    simp [quadraticOverLinearPlusSquareFunction, hxEqZero]

/-- Helper for Example 26.2.2: the function is globally nonnegative, so the zero covector can
support it at every axis point where the value is zero. -/
lemma helperForExample_26_2_2_nonnegative
    (x : Fin 2 → ℝ) :
    (0 : EReal) ≤ quadraticOverLinearPlusSquareFunction x := by
  by_cases hbranch : 0 < x 0 ∧ 0 ≤ x 1
  · rcases hbranch with ⟨hx0, _hx1⟩
    have hbranch' : 0 < x 0 ∧ 0 ≤ x 1 := ⟨hx0, _hx1⟩
    have hquad : 0 ≤ x 1 ^ 2 / (2 * x 0) := by
      have hden : 0 < 2 * x 0 := by positivity
      exact div_nonneg (sq_nonneg _) hden.le
    have hsq : 0 ≤ x 1 ^ 2 := sq_nonneg _
    have hsum : 0 ≤ x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 := add_nonneg hquad hsq
    have hsumE :
        (0 : EReal) ≤ (((x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 : ℝ)) : EReal) := by
      exact_mod_cast hsum
    simpa [quadraticOverLinearPlusSquareFunction, hbranch'] using hsumE
  · by_cases hx0 : x = 0
    · simp [quadraticOverLinearPlusSquareFunction, hx0]
    · rw [quadraticOverLinearPlusSquareFunction, if_neg hbranch, if_neg hx0]
      simp

/-- Helper for Example 26.2.2: the ordinary interior of the explicit domain
`{ξ₁ > 0, ξ₂ ≥ 0} ∪ {0}` is the open positive quadrant. -/
lemma helperForExample_26_2_2_explicitDomain_interior_eq_openQuadrant :
    interior ({x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1} ∪ ({0} : Set (Fin 2 → ℝ))) =
      openPositiveQuadrantR2 := by
  let D : Set (Fin 2 → ℝ) := {x | 0 < x 0 ∧ 0 ≤ x 1} ∪ ({0} : Set (Fin 2 → ℝ))
  ext x
  constructor
  · intro hx
    let p0 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (i := (0 : Fin 2))
    let p1 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (i := (1 : Fin 2))
    have hsubset0 : D ⊆ {y : Fin 2 → ℝ | 0 ≤ y 0} := by
      intro y hy
      rcases hy with hy | rfl
      · exact le_of_lt hy.1
      · simp
    have hsubset1 : D ⊆ {y : Fin 2 → ℝ | 0 ≤ y 1} := by
      intro y hy
      rcases hy with hy | rfl
      · exact hy.2
      · simp
    have hx0 : x ∈ interior ({y : Fin 2 → ℝ | 0 ≤ y 0}) := interior_mono hsubset0 hx
    have hx1 : x ∈ interior ({y : Fin 2 → ℝ | 0 ≤ y 1}) := interior_mono hsubset1 hx
    have hsurj0 : Function.Surjective p0 := by
      intro r
      refine ⟨![r, 0], ?_⟩
      simp [p0]
    have hsurj1 : Function.Surjective p1 := by
      intro r
      refine ⟨![0, r], ?_⟩
      simp [p1]
    have hInt0 : interior ({y : Fin 2 → ℝ | 0 ≤ y 0}) = {y : Fin 2 → ℝ | 0 < y 0} := by
      simpa [p0] using
        (ContinuousLinearMap.interior_preimage (f := p0) hsurj0 (s := Set.Ici (0 : ℝ)))
    have hInt1 : interior ({y : Fin 2 → ℝ | 0 ≤ y 1}) = {y : Fin 2 → ℝ | 0 < y 1} := by
      simpa [p1] using
        (ContinuousLinearMap.interior_preimage (f := p1) hsurj1 (s := Set.Ici (0 : ℝ)))
    constructor
    · rw [hInt0] at hx0
      simpa using hx0
    · rw [hInt1] at hx1
      simpa using hx1
  · intro hx
    have hOpen : IsOpen openPositiveQuadrantR2 :=
      helperForExample_26_2_1_openQuadrant_isOpen
    have hSubset : openPositiveQuadrantR2 ⊆ D := by
      intro y hy
      exact Or.inl ⟨hy.1, le_of_lt hy.2⟩
    exact mem_interior_iff_mem_nhds.2
      (Filter.mem_of_superset (hOpen.mem_nhds hx) hSubset)

/-- Helper for Example 26.2.2: the explicit domain `{ξ₁ > 0, ξ₂ ≥ 0} ∪ {0}` has relative
interior equal to the open positive quadrant. -/
lemma helperForExample_26_2_2_explicitDomain_relativeInterior_eq_openQuadrant :
    euclideanRelativeInterior_fin 2
        ({x : Fin 2 → ℝ | 0 < x 0 ∧ 0 ≤ x 1} ∪ ({0} : Set (Fin 2 → ℝ))) =
      openPositiveQuadrantR2 := by
  let e := (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ))
  let D : Set (Fin 2 → ℝ) := {x | 0 < x 0 ∧ 0 ≤ x 1} ∪ ({0} : Set (Fin 2 → ℝ))
  let C : Set (EuclideanSpace ℝ (Fin 2)) := e.symm '' D
  have hIntD : interior D = openPositiveQuadrantR2 := by
    simpa [D] using helperForExample_26_2_2_explicitDomain_interior_eq_openQuadrant
  have hImageInterior : e.symm.toHomeomorph '' interior D = interior C := by
    -- Transport the explicit-domain interior across the coordinate homeomorphism.
    simpa [C] using (e.symm.toHomeomorph.image_interior (s := D))
  have hIntNe : (interior C).Nonempty := by
    have hbase : (![1, 1] : Fin 2 → ℝ) ∈ interior D := by
      rw [hIntD]
      simp [openPositiveQuadrantR2]
    refine ⟨e.symm ![1, 1], ?_⟩
    -- The point `(1, 1)` lies in the interior of the explicit domain.
    rw [← hImageInterior]
    exact ⟨![1, 1], hbase, rfl⟩
  have hAffTop : affineSpan ℝ C = ⊤ := by
    have hAffTopInt : affineSpan ℝ (interior C) = ⊤ :=
      isOpen_interior.affineSpan_eq_top hIntNe
    exact top_unique <| by
      simpa [hAffTopInt] using
        (affineSpan_mono Real interior_subset : affineSpan ℝ (interior C) ≤ affineSpan ℝ C)
  have hAff : (affineSpan Real C : Set (EuclideanSpace Real (Fin 2))) = Set.univ := by
    simp [hAffTop]
  have hri : euclideanRelativeInterior 2 C = interior C :=
    euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ 2 C hAff
  have hPreimageSet : e.symm.toHomeomorph ⁻¹' C = D := by
    ext x
    simp [C, D]
  have hPreimageInterior : e.symm.toHomeomorph ⁻¹' interior C = interior D := by
    -- Pulling interior back through the same homeomorphism recovers the original interior.
    rw [e.symm.toHomeomorph.preimage_interior (s := C)]
    rw [hPreimageSet]
  ext x
  -- Full dimensionality reduces relative interior to ordinary interior after transport.
  rw [mem_euclideanRelativeInterior_fin_iff]
  rw [hri]
  change x ∈ e.symm.toHomeomorph ⁻¹' interior C ↔ x ∈ openPositiveQuadrantR2
  rw [hPreimageInterior]
  rw [hIntD]

/-- Helper for Example 26.2.2: the relative interior of the effective domain is exactly the open
positive quadrant. -/
lemma helperForExample_26_2_2_relativeInterior_eq_openQuadrant :
    euclideanRelativeInterior_fin 2
        (effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearPlusSquareFunction) =
      openPositiveQuadrantR2 := by
  rcases helperForExample_26_2_2_effectiveDomain_eq_and_axisValues with ⟨hdom, _haxis⟩
  -- After rewriting the explicit domain, `simp` computes the transported relative interior.
  simpa [hdom] using helperForExample_26_2_2_explicitDomain_relativeInterior_eq_openQuadrant

/-- Helper for Example 26.2.2: positive weights strictly contract the square unless the
coordinates agree. -/
lemma helperForExample_26_2_2_weightedSquare_strict
    {u v a b : ℝ} (huv : u ≠ v) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (a * u + b * v) ^ 2 < a * u ^ 2 + b * v ^ 2 := by
  have hb' : b = 1 - a := by
    linarith
  rw [hb']
  have hdiff :
      a * u ^ 2 + (1 - a) * v ^ 2 - (a * u + (1 - a) * v) ^ 2 =
        a * (1 - a) * (u - v) ^ 2 := by
    ring_nf
  have hsq : 0 < (u - v) ^ 2 := by
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr huv)
  have hOneSub : 0 < 1 - a := by
    linarith
  have hpos : 0 < a * (1 - a) * (u - v) ^ 2 := by
    exact mul_pos (mul_pos ha hOneSub) hsq
  linarith

/-- Helper for Example 26.2.2: the same two-case argument as in Example 26.2.1 yields strict
convexity of the real branch on the open positive quadrant. -/
lemma helperForExample_26_2_2_strictConvexOn_openQuadrant :
    StrictConvexOn ℝ openPositiveQuadrantR2
      (fun x => (quadraticOverLinearPlusSquareFunction x).toReal) := by
  refine ⟨helperForExample_26_2_1_openQuadrant_isConvex, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let z : Fin 2 → ℝ := a • x + b • y
  have hz : z ∈ openPositiveQuadrantR2 :=
    helperForExample_26_2_1_openQuadrant_combo_mem hx hy ha hb hab
  have hxReal :
      (quadraticOverLinearPlusSquareFunction x).toReal =
        x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 := by
    -- On the open quadrant the `EReal` function agrees with its finite real branch.
    simpa using congrArg EReal.toReal
      (helperForExample_26_2_2_value_on_openQuadrant hx)
  have hyReal :
      (quadraticOverLinearPlusSquareFunction y).toReal =
        y 1 ^ 2 / (2 * y 0) + y 1 ^ 2 := by
    -- The same branch computation applies at the second endpoint.
    simpa using congrArg EReal.toReal
      (helperForExample_26_2_2_value_on_openQuadrant hy)
  have hzReal :
      (quadraticOverLinearPlusSquareFunction z).toReal =
        z 1 ^ 2 / (2 * z 0) + z 1 ^ 2 := by
    -- The convex combination stays in the open quadrant, so the midpoint uses the same branch.
    simpa using congrArg EReal.toReal
      (helperForExample_26_2_2_value_on_openQuadrant hz)
  by_cases hsecond : x 1 = y 1
  · have hfirst : x 0 ≠ y 0 := by
      intro h0
      apply hxy
      ext i
      fin_cases i
      · simpa using h0
      · simp [hsecond]
    have hz1 : z 1 = x 1 := by
      calc
        z 1 = a * x 1 + b * y 1 := by
          simp [z, smul_eq_mul]
        _ = a * x 1 + b * x 1 := by rw [hsecond]
        _ = (a + b) * x 1 := by ring
        _ = x 1 := by rw [hab]; ring
    have hquad :
        z 1 ^ 2 / (2 * z 0) <
          a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0)) := by
      rcases hx with ⟨hx0, hx1⟩
      rcases hy with ⟨hy0, _hy1⟩
      -- When the second coordinates agree, strictness comes from the `ξ₁`-dependence alone.
      simpa [z, hz1, hsecond, smul_eq_mul] using
        helperForExample_26_2_1_fixedSecondCoordinate_strictConvex_firstCoordinate
          hx0 hy0 hx1 hfirst ha hb hab
    change (quadraticOverLinearPlusSquareFunction z).toReal <
        a * (quadraticOverLinearPlusSquareFunction x).toReal +
          b * (quadraticOverLinearPlusSquareFunction y).toReal
    have hyReal' :
        (quadraticOverLinearPlusSquareFunction y).toReal =
          y 1 ^ 2 / (2 * y 0) + x 1 ^ 2 := by
      simpa [hsecond] using hyReal
    have hzReal' :
        (quadraticOverLinearPlusSquareFunction z).toReal =
          z 1 ^ 2 / (2 * z 0) + x 1 ^ 2 := by
      simpa [hz1] using hzReal
    rw [hxReal, hyReal', hzReal']
    have hright :
        a * (x 1 ^ 2 / (2 * x 0) + x 1 ^ 2) +
            b * (y 1 ^ 2 / (2 * y 0) + x 1 ^ 2) =
          (a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0))) + x 1 ^ 2 := by
      calc
        a * (x 1 ^ 2 / (2 * x 0) + x 1 ^ 2) +
            b * (y 1 ^ 2 / (2 * y 0) + x 1 ^ 2) =
          (a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0))) +
            (a + b) * x 1 ^ 2 := by
              ring
        _ =
          (a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0))) + x 1 ^ 2 := by
            rw [hab]
            ring
    rw [hright]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_lt_add_right hquad (x 1 ^ 2)
  · have hsq :
        z 1 ^ 2 < a * x 1 ^ 2 + b * y 1 ^ 2 := by
      -- When the second coordinates differ, the square term supplies the strict inequality.
      simpa [z, smul_eq_mul] using
        helperForExample_26_2_2_weightedSquare_strict hsecond ha hb hab
    have hquad :
        z 1 ^ 2 / (2 * z 0) ≤
          a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0)) :=
      helperForExample_26_2_1_quadraticOverLinear_real_convex_combo hx hy ha hb hab
    change (quadraticOverLinearPlusSquareFunction z).toReal <
        a * (quadraticOverLinearPlusSquareFunction x).toReal +
          b * (quadraticOverLinearPlusSquareFunction y).toReal
    rw [hxReal, hyReal, hzReal]
    linarith

/-- Helper for Example 26.2.2: every point on the nonnegative `ξ₁`-axis has the zero covector as
a subgradient, so the whole axis lies in `dom ∂ f`. -/
lemma helperForExample_26_2_2_axis_subset_subdifferentialEffectiveDomain :
    nonnegativeXi1AxisR2 ⊆ subdifferentialEffectiveDomain quadraticOverLinearPlusSquareFunction := by
  intro x hx
  have hxVal : quadraticOverLinearPlusSquareFunction x = (0 : EReal) :=
    helperForExample_26_2_2_value_on_nonnegativeXi1Axis hx
  have hzero :
      (0 : Module.Dual ℝ (Fin 2 → ℝ)) ∈
        subdifferentialAt quadraticOverLinearPlusSquareFunction x := by
    rw [mem_subdifferentialAt_iff]
    intro z
    -- Global nonnegativity rewrites exactly to the subgradient inequality with zero slope.
    simpa [IsSubgradientAt, hxVal] using helperForExample_26_2_2_nonnegative z
  have hnonempty :
      Set.Nonempty (subdifferentialAt quadraticOverLinearPlusSquareFunction x) := ⟨0, hzero⟩
  simpa [subdifferentialEffectiveDomain, Set.nonempty_iff_ne_empty] using hnonempty

/-- Helper for Example 26.2.2: the nonnegative `ξ₁`-axis is a convex set. -/
lemma helperForExample_26_2_2_nonnegativeXi1Axis_isConvex :
    Convex ℝ nonnegativeXi1AxisR2 := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  constructor
  · -- The first coordinate is a nonnegative convex combination of nonnegative numbers.
    have : 0 ≤ a * x 0 + b * y 0 := by
      exact add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
    simpa [smul_eq_mul] using this
  · -- The second coordinate stays zero because both endpoints already lie on the axis.
    simp [hx1, hy1, smul_eq_mul]

/-- Helper for Example 26.2.2: the axis lies in `dom ∂ f` but the function is constant there, so
it cannot be essentially strictly convex. -/
lemma helperForExample_26_2_2_not_essentiallyStrictlyConvex :
    ¬ IsEssentiallyStrictlyConvex quadraticOverLinearPlusSquareFunction := by
  intro hEss
  have hAxisSubset :
      nonnegativeXi1AxisR2 ⊆
        subdifferentialEffectiveDomain quadraticOverLinearPlusSquareFunction :=
    helperForExample_26_2_2_axis_subset_subdifferentialEffectiveDomain
  have hstrictAxis :
      StrictConvexOn ℝ nonnegativeXi1AxisR2
        (fun x => (quadraticOverLinearPlusSquareFunction x).toReal) :=
    hEss.2 hAxisSubset helperForExample_26_2_2_nonnegativeXi1Axis_isConvex
  have hx : (0 : Fin 2 → ℝ) ∈ nonnegativeXi1AxisR2 := by
    simp [nonnegativeXi1AxisR2]
  let y : Fin 2 → ℝ := ![1, 0]
  have hy : y ∈ nonnegativeXi1AxisR2 := by
    simp [y, nonnegativeXi1AxisR2]
  have hxy : (0 : Fin 2 → ℝ) ≠ y := by
    intro hEq
    have hcoord := congrArg (fun z : Fin 2 → ℝ => z 0) hEq
    simp [y] at hcoord
  have hlt :=
    hstrictAxis.2 hx hy hxy
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (by norm_num)
  -- Evaluating the strict-convexity inequality on two axis points reduces to `0 < 0`.
  norm_num [y, quadraticOverLinearPlusSquareFunction, nonnegativeXi1AxisR2] at hlt

-- Proof sketch: identify `ri (dom f)` with the open positive quadrant from the explicit formula,
-- use the positive-definite Hessian there to obtain strict convexity, note that every point on the
-- nonnegative `ξ₁`-axis still has a supporting subgradient while the restriction of `f` to that
-- axis is identically zero, and conclude that `f` cannot be essentially strictly convex.
/-- Example 26.2.2: the function
`f(ξ₁, ξ₂) = ξ₂^2 / (2 ξ₁) + ξ₂^2` for `ξ₁ > 0`, `ξ₂ ≥ 0`, with `f(0, 0) = 0` and `f = +∞`
otherwise, is strictly convex on `ri (dom f)`, and this relative interior is the open positive
quadrant of `ℝ²`; moreover, the nonnegative `ξ₁`-axis lies in `dom ∂ f`, `f` is constant there,
and therefore `f` is not essentially strictly convex. -/
theorem quadraticOverLinearPlusSquareFunction_strictConvexOn_relativeInterior_but_not_essentiallyStrictlyConvex :
    euclideanRelativeInterior_fin 2
        (effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearPlusSquareFunction) =
      openPositiveQuadrantR2 ∧
      StrictConvexOn ℝ openPositiveQuadrantR2
        (fun x => (quadraticOverLinearPlusSquareFunction x).toReal) ∧
      nonnegativeXi1AxisR2 ⊆ subdifferentialEffectiveDomain quadraticOverLinearPlusSquareFunction ∧
      Set.EqOn (fun x => (quadraticOverLinearPlusSquareFunction x).toReal)
        (fun _ : Fin 2 → ℝ => (0 : ℝ)) nonnegativeXi1AxisR2 ∧
      ¬ IsEssentiallyStrictlyConvex quadraticOverLinearPlusSquareFunction := by
  rcases helperForExample_26_2_2_effectiveDomain_eq_and_axisValues with ⟨_hdom, haxisEqOn⟩
  constructor
  · -- The explicit domain computation identifies the relative interior with the open quadrant.
    exact helperForExample_26_2_2_relativeInterior_eq_openQuadrant
  constructor
  · -- Strict convexity on that relative interior follows from the two-case Jensen argument.
    exact helperForExample_26_2_2_strictConvexOn_openQuadrant
  constructor
  · -- The zero covector shows the whole nonnegative axis lies in `dom ∂ f`.
    exact helperForExample_26_2_2_axis_subset_subdifferentialEffectiveDomain
  constructor
  · -- The axis restriction is constant because every axis value equals zero.
    exact haxisEqOn
  · -- Since the axis lies in `dom ∂ f`, this constant restriction rules out essential strictness.
    exact helperForExample_26_2_2_not_essentiallyStrictlyConvex

/-- The open upper half-plane in `ℝ²`, written in coordinates `(ξ₁, ξ₂)`. -/
def openUpperHalfPlaneR2 : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | 0 < x 1}

/-- The parabola `ξ₂* = - (ξ₁*)²` in `ℝ²`. -/
def negativeParabolaR2 : Set (EuclideanSpace ℝ (Fin 2)) :=
  {xStar | xStar 1 = - (xStar 0) ^ 2}

/-- The differentiable convex function `f(ξ₁, ξ₂) = ξ₁² / (4 ξ₂)` on the open upper half-plane. -/
noncomputable def upperHalfPlaneQuadraticOverLinearFunction (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 0 ^ 2 / (4 * x 1)

/-- Helper for Example 26.4.1.3: the open upper half-plane is an open convex subset of `ℝ²`. -/
lemma helperForExample_26_4_1_3_openUpperHalfPlane_isOpen_isConvex :
    IsOpen openUpperHalfPlaneR2 ∧ Convex ℝ openUpperHalfPlaneR2 := by
  constructor
  · -- The strict positivity condition on the second coordinate defines an open half-space.
    let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (Fin 2 → ℝ) := EuclideanSpace.equiv (Fin 2) ℝ
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 2) => (e x) 1) :=
      (continuous_apply 1).comp e.continuous
    simpa [openUpperHalfPlaneR2, e] using isOpen_lt continuous_const hcont
  · -- Convex combinations preserve strict positivity of the second coordinate.
    intro x hx y hy a b ha hb hab
    change 0 < (a • x + b • y) 1
    have hx' : 0 < x 1 := hx
    have hy' : 0 < y 1 := hy
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by
        linarith
      simpa [Pi.smul_apply, Pi.add_apply, ha0, hb1] using hy'
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hax : 0 < a * x 1 := mul_pos ha_pos hx'
      have hby : 0 ≤ b * y 1 := mul_nonneg hb hy'.le
      have : 0 < a * x 1 + b * y 1 := add_pos_of_pos_of_nonneg hax hby
      simpa [Pi.smul_apply, Pi.add_apply] using this

/-- Helper for Example 26.4.1.3: the quadratic-over-linear function is convex on the open upper
half-plane after the coordinate change `(ξ₁, ξ₂) ↦ (ξ₂, ξ₁ / √2)`. -/
lemma helperForExample_26_4_1_3_convexOn_openUpperHalfPlane :
    ConvexOn ℝ openUpperHalfPlaneR2 upperHalfPlaneQuadraticOverLinearFunction := by
  rw [convexOn_iff_forall_pos]
  refine ⟨helperForExample_26_4_1_3_openUpperHalfPlane_isOpen_isConvex.2, ?_⟩
  intro x hx y hy a b ha hb hab
  let τ : EuclideanSpace ℝ (Fin 2) → Fin 2 → ℝ := fun z => ![z 1, z 0 / Real.sqrt 2]
  have hnotbot :
      ∀ ξ ∈ (Set.univ : Set (Fin 2 → ℝ)), quadraticOverLinearEReal ξ ≠ ⊥ := by
    intro ξ _
    by_cases hξ : 0 < ξ 0
    · -- On the positive branch the function is finite.
      simp [quadraticOverLinearEReal, hξ]
    · by_cases hzero : ξ 0 = 0 ∧ ξ 1 = 0
      · -- At the origin the exceptional branch is still finite.
        simp [quadraticOverLinearEReal, hξ, hzero]
      · -- Outside those cases the value is `⊤`, never `⊥`.
        simp [quadraticOverLinearEReal, hξ, hzero]
  have hsegment :=
    (convexFunctionOn_iff_segment_inequality
      (C := (Set.univ : Set (Fin 2 → ℝ))) (f := quadraticOverLinearEReal)
      convex_univ hnotbot).1 convexFunctionOn_quadraticOverLinearEReal
  have hτx0 : 0 < τ x 0 := by
    simpa [τ] using hx
  have hτy0 : 0 < τ y 0 := by
    simpa [τ] using hy
  have hτz0 : 0 < (a • τ x + b • τ y) 0 := by
    have hx' : 0 < x 1 := hx
    have hy' : 0 < y 1 := hy
    have : 0 < a * x 1 + b * y 1 := add_pos (mul_pos ha hx') (mul_pos hb hy')
    simpa [τ, Pi.smul_apply, Pi.add_apply] using this
  have hb_lt_one : b < 1 := by
    linarith
  have hab' : 1 - b = a := by
    linarith
  have hsegmentE := hsegment (τ x) (by simp) (τ y) (by simp) b hb hb_lt_one
  rw [hab'] at hsegmentE
  have hτz0' : 0 < a * τ x 0 + b * τ y 0 := by
    simpa [Pi.smul_apply, Pi.add_apply] using hτz0
  have hrealE :
      ((((a • τ x + b • τ y) 1) ^ 2 / (2 * ((a • τ x + b • τ y) 0)) : ℝ) : EReal) ≤
        (((a * ((τ x 1) ^ 2 / (2 * τ x 0)) + b * ((τ y 1) ^ 2 / (2 * τ y 0)) : ℝ)) : EReal) := by
    -- On points with positive first coordinate, the extended-real inequality reduces to the real
    -- quadratic-over-linear inequality.
    simpa [quadraticOverLinearEReal, hτx0, hτy0, hτz0', smul_eq_mul] using hsegmentE
  have hreal :
      ((a • τ x + b • τ y) 1) ^ 2 / (2 * ((a • τ x + b • τ y) 0)) ≤
        a * ((τ x 1) ^ 2 / (2 * τ x 0)) + b * ((τ y 1) ^ 2 / (2 * τ y 0)) := by
    exact_mod_cast hrealE
  -- The coordinate change `τ (ξ₁, ξ₂) = (ξ₂, ξ₁ / √2)` turns the standard
  -- quadratic-over-linear formula into `ξ₁² / (4 ξ₂)`.
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
    positivity
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hleft :
      ((a • τ x + b • τ y) 1) ^ 2 / (2 * ((a • τ x + b • τ y) 0)) =
        upperHalfPlaneQuadraticOverLinearFunction (a • x + b • y) := by
    change
      ((a * (x 0 / Real.sqrt 2) + b * (y 0 / Real.sqrt 2)) ^ 2 / (2 * (a * x 1 + b * y 1))) =
        (a * x 0 + b * y 0) ^ 2 / (4 * (a * x 1 + b * y 1))
    have hden : a * x 1 + b * y 1 ≠ 0 := ne_of_gt hτz0'
    field_simp [hsqrt2_ne, hden]
    rw [hsqrt2_sq]
    ring
  have hxeq :
      (τ x 1) ^ 2 / (2 * τ x 0) = upperHalfPlaneQuadraticOverLinearFunction x := by
    change ((x 0 / Real.sqrt 2) ^ 2 / (2 * x 1)) = x 0 ^ 2 / (4 * x 1)
    have hden : x 1 ≠ 0 := ne_of_gt hx
    field_simp [hsqrt2_ne, hden]
    rw [hsqrt2_sq]
    ring
  have hyeq :
      (τ y 1) ^ 2 / (2 * τ y 0) = upperHalfPlaneQuadraticOverLinearFunction y := by
    change ((y 0 / Real.sqrt 2) ^ 2 / (2 * y 1)) = y 0 ^ 2 / (4 * y 1)
    have hden : y 1 ≠ 0 := ne_of_gt hy
    field_simp [hsqrt2_ne, hden]
    rw [hsqrt2_sq]
    ring
  have hleft' :
      (a * τ x 1 + b * τ y 1) ^ 2 / (2 * (a * τ x 0 + b * τ y 0)) =
        upperHalfPlaneQuadraticOverLinearFunction (a • x + b • y) := by
    simpa [Pi.smul_apply, Pi.add_apply] using hleft
  simpa [hleft', hxeq, hyeq] using hreal

/-- Helper for Example 26.4.1.3: the coordinate gradient of `ξ ↦ ξ₁² / (4 ξ₂)` is explicit. -/
lemma helperForExample_26_4_1_3_coordinateGradient_formula
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ openUpperHalfPlaneR2) :
    euclideanGradientAt (fun ξ : Fin 2 → ℝ => ξ 0 ^ 2 / (4 * ξ 1))
        ((EuclideanSpace.equiv (Fin 2) ℝ) x) =
      ![x 0 / (2 * x 1), -(x 0 ^ 2 / (4 * x 1 ^ 2))] := by
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (Fin 2 → ℝ) := EuclideanSpace.equiv (Fin 2) ℝ
  let g : (Fin 2 → ℝ) → ℝ := fun ξ => ξ 0 ^ 2 / (4 * ξ 1)
  have hx1 : 0 < x 1 := hx
  have hdiff : DifferentiableAt ℝ g (e x) := by
    -- The positive second coordinate keeps the denominator away from zero.
    fun_prop (disch := positivity)
  ext i
  fin_cases i
  · -- Along the first basis direction, only the numerator changes.
    change
      (fderiv ℝ g (e x)) (Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)) =
        x 0 / (2 * x 1)
    have hline_from_fderiv :
        HasDerivAt
          (fun t : ℝ =>
            g (e x + t • Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
          ((fderiv ℝ g (e x)) (Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ))) 0 := by
      simpa [HasLineDerivAt, e, g] using
        (hdiff.hasFDerivAt.hasLineDerivAt
          (Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
    have hline_explicit :
        HasDerivAt
          (fun t : ℝ =>
            g (e x + t • Pi.single (i := (0 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
          (x 0 / (2 * x 1)) 0 := by
      have hbase : HasDerivAt (fun t : ℝ => x 0 + t) 1 0 := by
        simpa using (hasDerivAt_id 0).const_add (x 0)
      have hpow : HasDerivAt (fun t : ℝ => (x 0 + t) ^ 2) (2 * x 0) 0 := by
        simpa [two_mul] using hbase.pow 2
      have hdiv : HasDerivAt (fun t : ℝ => (x 0 + t) ^ 2 / (4 * x 1)) ((2 * x 0) / (4 * x 1)) 0 := by
        exact hpow.div_const (4 * x 1)
      have hdiv' : HasDerivAt (fun t : ℝ => (x 0 + t) ^ 2 / (4 * x 1)) (x 0 / (2 * x 1)) 0 := by
        convert hdiv using 1
        field_simp [hx1.ne']
        ring
      simpa [g, e, Pi.add_apply, Pi.smul_apply] using hdiv'
    exact hline_from_fderiv.unique hline_explicit
  · -- Along the second basis direction, the denominator changes and contributes the negative term.
    change
      (fderiv ℝ g (e x)) (Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)) =
        -(x 0 ^ 2 / (4 * x 1 ^ 2))
    have hline_from_fderiv :
        HasDerivAt
          (fun t : ℝ =>
            g (e x + t • Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
          ((fderiv ℝ g (e x)) (Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ))) 0 := by
      simpa [HasLineDerivAt, e, g] using
        (hdiff.hasFDerivAt.hasLineDerivAt
          (Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
    have hline_explicit :
        HasDerivAt
          (fun t : ℝ =>
            g (e x + t • Pi.single (i := (1 : Fin 2)) (M := fun _ : Fin 2 => ℝ) (1 : ℝ)))
          (-(x 0 ^ 2 / (4 * x 1 ^ 2))) 0 := by
      have hnum : HasDerivAt (fun _t : ℝ => x 0 ^ 2) 0 0 := by
        simpa using (hasDerivAt_const (x := 0) (c := x 0 ^ 2))
      have hden_base : HasDerivAt (fun t : ℝ => x 1 + t) 1 0 := by
        simpa using (hasDerivAt_id 0).const_add (x 1)
      have hden : HasDerivAt (fun t : ℝ => 4 * (x 1 + t)) 4 0 := by
        simpa [mul_add, add_comm, add_left_comm, add_assoc] using hden_base.const_mul (4 : ℝ)
      have hquot : HasDerivAt (fun t : ℝ => x 0 ^ 2 / (4 * (x 1 + t)))
          ((0 * (4 * (x 1 + 0)) - x 0 ^ 2 * 4) / (4 * (x 1 + 0)) ^ 2) 0 := by
        simpa using hnum.div hden (by positivity)
      have hquot' : HasDerivAt (fun t : ℝ => x 0 ^ 2 / (4 * (x 1 + t)))
          (-(x 0 ^ 2 / (4 * x 1 ^ 2))) 0 := by
        convert hquot using 1
        field_simp [hx1.ne']
        ring
      simpa [g, e, Pi.add_apply, Pi.smul_apply] using hquot'
    exact hline_from_fderiv.unique hline_explicit

/-- Helper for Example 26.4.1.3: on the open upper half-plane, the gradient is
`(ξ₁ / (2 ξ₂), - ξ₁² / (4 ξ₂²))`. -/

lemma helperForExample_26_4_1_3_hasGradientAt_formula
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ openUpperHalfPlaneR2) :
    HasGradientAt upperHalfPlaneQuadraticOverLinearFunction
      ((EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm
        ![x 0 / (2 * x 1), -(x 0 ^ 2 / (4 * x 1 ^ 2))]) x := by
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (Fin 2 → ℝ) := EuclideanSpace.equiv (Fin 2) ℝ
  let fCoord : (Fin 2 → ℝ) → ℝ := fun ξ => ξ 0 ^ 2 / (4 * ξ 1)
  have hx1 : 0 < (e x) 1 := by
    simpa [e, openUpperHalfPlaneR2] using hx
  have hdiff : DifferentiableAt ℝ fCoord (e x) := by
    -- The positive second coordinate keeps the denominator away from zero.
    fun_prop (disch := positivity)
  have hfderiv :
      HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin 2) => fCoord (e z))
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2)))
          (e.symm (euclideanGradientAt fCoord (e x))))
        (e.symm (e x)) := by
    -- Transport the Fréchet derivative from coordinate space to Euclidean space.
    exact
      helperForText_26_4_0_2_sourceGradient_transport_fderiv_form
        (f := fCoord) (x := e x) hdiff
  have hgradAt :
      HasGradientAt
        (fun z : EuclideanSpace ℝ (Fin 2) => fCoord (e z))
        (e.symm (euclideanGradientAt fCoord (e x)))
        (e.symm (e x)) :=
    (hasGradientAt_iff_hasFDerivAt).2 hfderiv
  have hcoord :
      euclideanGradientAt fCoord (e x) =
        ![x 0 / (2 * x 1), -(x 0 ^ 2 / (4 * x 1 ^ 2))] := by
    simpa [e, fCoord] using helperForExample_26_4_1_3_coordinateGradient_formula x hx
  have hvec :
      e.symm (euclideanGradientAt fCoord (e x)) =
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm
          ![x 0 / (2 * x 1), -(x 0 ^ 2 / (4 * x 1 ^ 2))]) := by
    rw [hcoord]
  rw [hvec] at hgradAt
  -- Evaluating `euclideanGradientAt` on the two basis vectors gives the displayed formula.
  simpa [e, fCoord, upperHalfPlaneQuadraticOverLinearFunction] using hgradAt

/-- Helper for Example 26.4.1.3: the gradient image of the open upper half-plane is exactly the
negative parabola `ξ₂* = - (ξ₁*)²`. -/
lemma helperForExample_26_4_1_3_gradientImage_eq_negativeParabola :
    legendreGradientImage openUpperHalfPlaneR2 upperHalfPlaneQuadraticOverLinearFunction =
      negativeParabolaR2 := by
  ext xStar
  constructor
  · intro hxStar
    rcases hxStar with ⟨x, hx, rfl⟩
    have hgrad := (helperForExample_26_4_1_3_hasGradientAt_formula hx).gradient
    have hx1_ne : x 1 ≠ 0 := ne_of_gt hx
    have hsq :
        x 0 ^ 2 / (4 * x 1 ^ 2) = (x 0 / (2 * x 1)) ^ 2 := by
      field_simp [pow_two, hx1_ne]
      ring
    -- The explicit gradient coordinates satisfy the parabola equation identically.
    change (gradient upperHalfPlaneQuadraticOverLinearFunction x) 1 =
      -((gradient upperHalfPlaneQuadraticOverLinearFunction x) 0) ^ 2
    rw [hgrad]
    rw [hsq]
    simp
  · intro hxStar
    let x : EuclideanSpace ℝ (Fin 2) :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![2 * xStar 0, 1])
    have hx : x ∈ openUpperHalfPlaneR2 := by
      -- The witness lies in the upper half-plane because its second coordinate is `1`.
      simp [x, openUpperHalfPlaneR2]
    refine ⟨x, hx, ?_⟩
    have hgrad := (helperForExample_26_4_1_3_hasGradientAt_formula hx).gradient
    -- Evaluating the gradient at `(2 ξ₁*, 1)` recovers the prescribed parabola point.
    rw [hgrad]
    ext i <;> fin_cases i
    · simp [x]
    · have hxStar' : xStar 1 = - (xStar 0) ^ 2 := hxStar
      have hcalc : -((2 * xStar 0) ^ 2 / (4 * (1 : ℝ) ^ 2)) = -(xStar 0) ^ 2 := by
        ring
      simpa [x, hxStar'] using hcalc

/-- Helper for Example 26.4.1.3: the vertical sequence `(0, 1/(i+1))` stays in the upper
half-plane, converges to the boundary point `0`, and its gradient norm is constantly zero. -/
lemma helperForExample_26_4_1_3_boundarySequence_witness :
    ∃ xSeq : ℕ → EuclideanSpace ℝ (Fin 2),
      (∀ i : ℕ, xSeq i ∈ openUpperHalfPlaneR2) ∧
      Filter.Tendsto xSeq Filter.atTop (nhds (0 : EuclideanSpace ℝ (Fin 2))) ∧
      (0 : EuclideanSpace ℝ (Fin 2)) ∈ frontier openUpperHalfPlaneR2 ∧
      ¬ Filter.Tendsto
          (fun i : ℕ =>
            ‖gradient upperHalfPlaneQuadraticOverLinearFunction (xSeq i)‖)
          Filter.atTop Filter.atTop := by
  let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (Fin 2 → ℝ) := EuclideanSpace.equiv (Fin 2) ℝ
  let xSeq : ℕ → EuclideanSpace ℝ (Fin 2) :=
    fun i => (e.symm ![0, 1 / ((i : ℝ) + 1)])
  refine ⟨xSeq, ?_, ?_, ?_, ?_⟩
  · intro i
    -- Every term has positive second coordinate.
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    simpa [xSeq, e, openUpperHalfPlaneR2] using hi
  · have h0 :
        Filter.Tendsto (fun i : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds
    have h1 :
        Filter.Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1) : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcoords :
        Filter.Tendsto (fun i : ℕ => (![0, 1 / ((i : ℝ) + 1)] : Fin 2 → ℝ))
          Filter.atTop (nhds 0) := by
      -- Coordinatewise convergence gives convergence of the coordinate vector.
      rw [tendsto_pi_nhds]
      intro j
      fin_cases j
      · simpa using h0
      · simpa using h1
    simpa [xSeq, e] using e.symm.continuous.continuousAt.tendsto.comp hcoords
  · have hxSeq_tendsto :
        Filter.Tendsto xSeq Filter.atTop (nhds (0 : EuclideanSpace ℝ (Fin 2))) := by
      have h0 :
          Filter.Tendsto (fun i : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds
      have h1 :
          Filter.Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1) : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hcoords :
          Filter.Tendsto (fun i : ℕ => (![0, 1 / ((i : ℝ) + 1)] : Fin 2 → ℝ))
            Filter.atTop (nhds 0) := by
        rw [tendsto_pi_nhds]
        intro j
        fin_cases j
        · simpa using h0
        · simpa using h1
      simpa [xSeq, e] using e.symm.continuous.continuousAt.tendsto.comp hcoords
    have hclosure :
        (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure openUpperHalfPlaneR2 := by
      -- A limit of points in the set belongs to its closure.
      refine mem_closure_of_tendsto hxSeq_tendsto (Filter.Eventually.of_forall ?_)
      intro i
      have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      simpa [xSeq, e, openUpperHalfPlaneR2] using hi
    have hcompl :
        (0 : EuclideanSpace ℝ (Fin 2)) ∈ closure (openUpperHalfPlaneR2ᶜ) := by
      -- The origin already lies in the complement because its second coordinate is not positive.
      exact subset_closure (by simp [openUpperHalfPlaneR2])
    -- Being in the closures of both the set and its complement characterizes the frontier.
    rw [frontier_eq_closure_inter_closure]
    exact ⟨hclosure, hcompl⟩
  · have hxSeq_mem : ∀ i : ℕ, xSeq i ∈ openUpperHalfPlaneR2 := by
      intro i
      have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      simpa [xSeq, e, openUpperHalfPlaneR2] using hi
    have hgrad_zero :
        ∀ i : ℕ, gradient upperHalfPlaneQuadraticOverLinearFunction (xSeq i) = 0 := by
      intro i
      have hgrad := (helperForExample_26_4_1_3_hasGradientAt_formula (hxSeq_mem i)).gradient
      have hi_ne : (xSeq i) 1 ≠ 0 := ne_of_gt (hxSeq_mem i)
      rw [hgrad]
      ext j <;> fin_cases j
      · simp [xSeq, e]
      · simp [xSeq, e, hi_ne]
    -- Along the vertical sequence the gradient vanishes identically, so its norm cannot tend to
    -- `+∞`.
    simpa [hgrad_zero] using
      (Filter.not_tendsto_const_atTop (x := (0 : ℝ)) (l := Filter.atTop))

-- Proof sketch: compute the gradient explicitly as
-- `∇f(ξ₁, ξ₂) = (ξ₁ / (2 ξ₂), - ξ₁² / (4 ξ₂²))`, eliminate `(ξ₁, ξ₂)` to identify the image with
-- the parabola `ξ₂* = - (ξ₁*)²`, and exhibit the vertical sequence `(0, t)` with `t ↓ 0` to show
-- that the gradient norm does not blow up at the boundary point `0`, so condition (c) fails
-- there and the gradient-image domain is not convex.
/-- Example 26.4.1.3: for the differentiable convex function
`f(ξ₁, ξ₂) = ξ₁² / (4 ξ₂)` on the open upper half-plane `C ⊆ ℝ²`, the Legendre conjugate domain
`D = ∇ f(C)` is the parabola `P = {(ξ₁*, ξ₂*) | ξ₂* = - (ξ₁*)²}`; this parabola is not convex,
and condition (c) of essential smoothness fails at the origin. -/
theorem upperHalfPlaneQuadraticOverLinear_has_parabolic_gradientImage_and_boundaryBlowupFails :
    IsOpen openUpperHalfPlaneR2 ∧
      Convex ℝ openUpperHalfPlaneR2 ∧
      ConvexOn ℝ openUpperHalfPlaneR2 upperHalfPlaneQuadraticOverLinearFunction ∧
      DifferentiableOn ℝ upperHalfPlaneQuadraticOverLinearFunction openUpperHalfPlaneR2 ∧
      legendreGradientImage openUpperHalfPlaneR2 upperHalfPlaneQuadraticOverLinearFunction =
        negativeParabolaR2 ∧
      ¬ Convex ℝ negativeParabolaR2 ∧
      ∃ xSeq : ℕ → EuclideanSpace ℝ (Fin 2),
        (∀ i : ℕ, xSeq i ∈ openUpperHalfPlaneR2) ∧
        Filter.Tendsto xSeq Filter.atTop (nhds (0 : EuclideanSpace ℝ (Fin 2))) ∧
        (0 : EuclideanSpace ℝ (Fin 2)) ∈ frontier openUpperHalfPlaneR2 ∧
        ¬ Filter.Tendsto
            (fun i : ℕ =>
              ‖gradient upperHalfPlaneQuadraticOverLinearFunction (xSeq i)‖)
            Filter.atTop Filter.atTop := by
  rcases helperForExample_26_4_1_3_openUpperHalfPlane_isOpen_isConvex with ⟨hOpen, hConvex⟩
  refine ⟨hOpen, hConvex, helperForExample_26_4_1_3_convexOn_openUpperHalfPlane, ?_, ?_, ?_, ?_⟩
  · -- The explicit gradient formula gives differentiability at every point of the half-plane.
    intro x hx
    exact
      (helperForExample_26_4_1_3_hasGradientAt_formula hx).differentiableAt.differentiableWithinAt
  · -- The Legendre gradient image is the negative parabola.
    exact helperForExample_26_4_1_3_gradientImage_eq_negativeParabola
  · intro hconv
    let u : EuclideanSpace ℝ (Fin 2) := ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, -1])
    let v : EuclideanSpace ℝ (Fin 2) := ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![-1, -1])
    have hu : u ∈ negativeParabolaR2 := by
      simp [u, negativeParabolaR2]
    have hv : v ∈ negativeParabolaR2 := by
      simp [v, negativeParabolaR2]
    have hmid : ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) ∈ negativeParabolaR2 := by
      -- Convexity would force the midpoint of two parabola points to remain on the parabola.
      exact hconv hu hv (by positivity) (by positivity) (by norm_num)
    -- But the midpoint is `(0, -1)`, which violates the equation `ξ₂* = -(ξ₁*)²`.
    simp [u, v, negativeParabolaR2] at hmid
  · -- The explicit vertical sequence exhibits failure of the boundary blow-up condition.
    exact helperForExample_26_4_1_3_boundarySequence_witness

/-- A function is essentially smooth on `C` when it is proper and convex on `C`, has a unique
Euclidean subgradient at each point of `C`, and the norms of these subgradients blow up along
sequences in `C` converging to boundary points of `C`. -/
def IsEssentiallySmoothOn {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → EReal) : Prop :=
  ProperConvexFunctionOn C f ∧
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

/-- Definition 26.4.1.4: a convex function is of Legendre type on the pair `(C, f)` when
`C` is a nonempty open convex set, `f` is finite on `C`, the restriction of `f` to `C` is
strictly convex, and `f` is essentially smooth on `C`. Thus, by Corollary 26.3.1, a closed
proper convex function has one-to-one subdifferential exactly when its restriction to
`int (dom f)` is of Legendre type. -/
def IsLegendreTypeOn {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → EReal) : Prop :=
  C.Nonempty ∧
    IsOpen C ∧
      Convex ℝ C ∧
        (∀ x ∈ C, f x ≠ (⊤ : EReal)) ∧
          StrictConvexOn ℝ C (fun x => (f x).toReal) ∧
            IsEssentiallySmoothOn C f

/-- Helper for Proposition 26.4.1.5: if `C = int (dom f)` is nonempty, then it is open, convex,
and `f` is finite on `C`. -/
lemma helperForProposition_26_4_1_5_interiorDomain_openConvex_and_finite
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f) :
    let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    C.Nonempty → IsOpen C ∧ Convex ℝ C ∧ ∀ x ∈ C, f x ≠ (⊤ : EReal) := by
  intro C _hCne
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  -- The interior of the effective domain inherits openness and convexity from the domain itself.
  have hConvexDom :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    effectiveDomain_convex hproper.1
  refine ⟨isOpen_interior, hConvexDom.interior, ?_⟩
  intro x hx
  -- Interior points of the effective domain are automatically finite-valued.
  exact
    mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → ℝ))) (f := f) (interior_subset hx)

/-- Helper for Proposition 26.4.1.5: on `C = int (dom f)`, the ambient proper-convex package
restricts to a local `ProperConvexFunctionOn C f` package. -/
lemma helperForProposition_26_4_1_5_properConvexFunctionOn_interior
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f) :
    let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    C.Nonempty → ProperConvexFunctionOn C f := by
  intro C hCne
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hgeom :=
    helperForProposition_26_4_1_5_interiorDomain_openConvex_and_finite (f := f) hf hCne
  rcases hgeom with ⟨_hOpen, hConvex, _hFinite⟩
  have hconvOnUnivSeg :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), ∀ y ∈ (Set.univ : Set (Fin n → ℝ)), ∀ t : ℝ,
        0 < t → t < 1 →
          f ((1 - t) • x + t • y) ≤
            ((1 - t : ℝ) : EReal) * f x + ((t : ℝ) : EReal) * f y := by
    -- We reuse the global segment inequality on `univ`.
    refine
      (convexFunctionOn_iff_segment_inequality
        (C := (Set.univ : Set (Fin n → ℝ))) (f := f) convex_univ ?_).1 hproper.1
    intro x hx
    simpa using hproper.2.2 x hx
  have hconvOnC : ConvexFunctionOn C f := by
    -- Restrict the same segment inequality to the convex interior domain.
    refine
      (convexFunctionOn_iff_segment_inequality
        (C := C) (f := f) hConvex ?_).2 ?_
    · intro x hx
      simpa using hproper.2.2 x (by simp)
    · intro x hx y hy t ht0 ht1
      simpa using hconvOnUnivSeg x (by simp) y (by simp) t ht0 ht1
  refine ⟨hconvOnC, ?_, ?_⟩
  · rcases hCne with ⟨x, hx⟩
    rcases interior_subset hx with ⟨μ, hμ⟩
    -- A point of `C` provides a concrete epigraph point over `C`.
    exact ⟨(x, μ), ⟨hx, hμ.2⟩⟩
  · intro x hx
    -- Properness still rules out `⊥` on the restricted domain.
    simpa using hproper.2.2 x (by simp)

/-- Helper for Proposition 26.4.1.5: on `C = int (dom f)`, the local and global versions of
essential smoothness have the same gradient and boundary-blowup data. -/
lemma helperForProposition_26_4_1_5_essentiallySmoothOn_interior_iff_essentiallySmooth
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f) :
    let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    IsEssentiallySmoothOn C f ↔ IsEssentiallySmooth f := by
  intro C
  constructor
  · intro hSmoothOn
    rcases hSmoothOn with ⟨hproperC, grad, hmem, huniq, hblowup⟩
    have hCne : C.Nonempty := by
      rcases hproperC.2.1 with ⟨p, hp⟩
      exact ⟨p.1, hp.1⟩
    -- The only extra global field is properness on `univ`, supplied by `hf`.
    exact ⟨helperForTheorem_25_6_properConvexFunctionOn (f := f) hf, hCne, grad, hmem, huniq,
      hblowup⟩
  · intro hSmooth
    rcases hSmooth with ⟨_hproperUniv, hCne, grad, hmem, huniq, hblowup⟩
    -- Conversely, the global package restricts verbatim to `C`.
    exact
      ⟨helperForProposition_26_4_1_5_properConvexFunctionOn_interior (f := f) hf hCne, grad,
        hmem, huniq, hblowup⟩

/-- Helper for Proposition 26.4.1.5: on `C = int (dom f)`, Legendre type is exactly strict
convexity on `C` together with global essential smoothness. -/
lemma helperForProposition_26_4_1_5_isLegendreTypeOn_interior_iff_strictConvexOn_and_essentiallySmooth
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f) :
    let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    IsLegendreTypeOn C f ↔
      StrictConvexOn ℝ C (fun x => (f x).toReal) ∧ IsEssentiallySmooth f := by
  intro C
  constructor
  · intro hLegendre
    rcases hLegendre with ⟨_hCne, _hOpen, _hConvex, _hFinite, hStrict, hSmoothOn⟩
    -- Unpack the local Legendre record and replace local smoothness by the global predicate.
    exact
      ⟨hStrict,
        (helperForProposition_26_4_1_5_essentiallySmoothOn_interior_iff_essentiallySmooth
          (f := f) hf).1 hSmoothOn⟩
  · intro hData
    rcases hData with ⟨hStrict, hSmooth⟩
    have hSmoothGlobal : IsEssentiallySmooth f := hSmooth
    rcases hSmooth with ⟨_hproperUniv, hCne, _grad, _hmem, _huniq, _hblowup⟩
    have hgeom :=
      helperForProposition_26_4_1_5_interiorDomain_openConvex_and_finite (f := f) hf hCne
    rcases hgeom with ⟨hOpen, hConvex, hFinite⟩
    have hSmoothOn :
        IsEssentiallySmoothOn C f :=
      (helperForProposition_26_4_1_5_essentiallySmoothOn_interior_iff_essentiallySmooth
        (f := f) hf).2 hSmoothGlobal
    -- Repackage the geometric data and the smoothness bridge into the local Legendre record.
    exact ⟨hCne, hOpen, hConvex, hFinite, hStrict, hSmoothOn⟩

end Section26
end Chap05

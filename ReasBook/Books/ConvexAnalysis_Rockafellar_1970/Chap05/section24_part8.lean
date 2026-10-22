/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part7

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

/-- A finite profile value gives a domain point of the interval-integral primitive. -/


lemma helperForTheorem_5_24_4_mem_scalarEffectiveDomain_of_finite_profile
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
  have hxEval :
      oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint x) =
        (((∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := by
    rw [helperForTheorem_5_24_4_scalarPoint_primitive_eval]
    exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
      φ a x hmono ha hx
  have hxNotTop :
      oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint x) ≠ (⊤ : EReal) := by
    rw [hxEval]
    simp
  simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top, hxNotTop]

/-- The scalar effective domain of the interval-integral primitive is a convex interval. This is
the formal replacement for the interval `J` in the textbook proof of Theorem 5.24.4. -/
lemma helperForTheorem_5_24_4_scalarEffectiveDomain_convex_intervalIntegralPrimitive
    (φ : ℝ → EReal) (a : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    Convex ℝ (scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) := by
  intro x hx y hy α β hα hβ hsum
  let z : ℝ := α * x + β * y
  by_cases hxy : x ≤ y
  · have hmem : z ∈ Set.Icc x y := by
      constructor
      · have hαeq : α = 1 - β := by
          linarith
        dsimp [z]
        calc
          x ≤ x + β * (y - x) := by
            have : 0 ≤ β * (y - x) := mul_nonneg hβ (sub_nonneg.mpr hxy)
            linarith
          _ = α * x + β * y := by
              rw [hαeq]
              ring
      · have hβeq : β = 1 - α := by
          linarith
        dsimp [z]
        calc
          α * x + β * y = y - α * (y - x) := by
              rw [hβeq]
              ring
          _ ≤ y := by
              have : 0 ≤ α * (y - x) := mul_nonneg hα (sub_nonneg.mpr hxy)
              linarith
    by_cases hzLeft : z = x
    · simpa [z, hzLeft]
    by_cases hzRight : z = y
    · simpa [z, hzRight]
    have hzOpen : z ∈ Set.uIoo x y := by
      have hxz : x < z := lt_of_le_of_ne hmem.1 (Ne.symm hzLeft)
      have hzy : z < y := lt_of_le_of_ne hmem.2 hzRight
      simpa [z, Set.uIoo_of_le hxy] using (show z ∈ Set.Ioo x y from ⟨hxz, hzy⟩)
    have hzFinite :
        z ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
      helperForTheorem_5_24_4_finite_profile_on_open_interval_of_domain_points
        φ a x y z ha hx hy hzOpen
    exact
      helperForTheorem_5_24_4_mem_scalarEffectiveDomain_of_finite_profile
        φ a z hmono ha hzFinite
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hmem : z ∈ Set.Icc y x := by
      constructor
      · have hβeq : β = 1 - α := by
          linarith
        dsimp [z]
        calc
          y ≤ y + α * (x - y) := by
            have : 0 ≤ α * (x - y) := mul_nonneg hα (sub_nonneg.mpr hyx)
            linarith
          _ = α * x + β * y := by
              rw [hβeq]
              ring
      · have hαeq : α = 1 - β := by
          linarith
        dsimp [z]
        calc
          α * x + β * y = x - β * (x - y) := by
              rw [hαeq]
              ring
          _ ≤ x := by
              have : 0 ≤ β * (x - y) := mul_nonneg hβ (sub_nonneg.mpr hyx)
              linarith
    by_cases hzLeft : z = y
    · simpa [z, hzLeft]
    by_cases hzRight : z = x
    · simpa [z, hzRight]
    have hzOpen : z ∈ Set.uIoo x y := by
      have hyz : y < z := lt_of_le_of_ne hmem.1 (Ne.symm hzLeft)
      have hzx : z < x := lt_of_le_of_ne hmem.2 hzRight
      simpa [z, Set.uIoo_of_ge hyx] using (show z ∈ Set.Ioo y x from ⟨hyz, hzx⟩)
    have hzFinite :
        z ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
      helperForTheorem_5_24_4_finite_profile_on_open_interval_of_domain_points
        φ a x y z ha hx hy hzOpen
    exact
      helperForTheorem_5_24_4_mem_scalarEffectiveDomain_of_finite_profile
        φ a z hmono ha hzFinite

/-- On any scalar domain segment joining the base point `a` to another effective-domain point, the
interval-integral primitive is continuous. This is the anchored continuity statement needed for
the remaining closedness argument. -/
lemma helperForTheorem_5_24_4_primitiveValue_continuousOn_uIcc_of_mem_scalarEffectiveDomain
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    ContinuousOn (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.uIcc a x) := by
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a x hxDom with
    ⟨_, hInt⟩
  have hContIntReal :
      ContinuousOn (fun z : ℝ => ∫ t in a..z, (φ t).toReal) (Set.uIcc a x) :=
    intervalIntegral.continuousOn_primitive_interval' hInt (by simp)
  have hContInt :
      ContinuousOn (fun z : ℝ => (((∫ t in a..z, (φ t).toReal) : ℝ) : EReal)) (Set.uIcc a x) :=
    continuous_coe_real_ereal.comp_continuousOn hContIntReal
  have haDom : a ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) :=
    helperForTheorem_5_24_4_scalarBasePoint_mem_scalarEffectiveDomain φ a
  have hDomConv :
      Convex ℝ (scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :=
    helperForTheorem_5_24_4_scalarEffectiveDomain_convex_intervalIntegralPrimitive
      φ a hmono ha
  have hEq :
      Set.EqOn (oneDimensionalIntervalIntegralPrimitiveValue φ a)
        (fun z : ℝ => (((∫ t in a..z, (φ t).toReal) : ℝ) : EReal)) (Set.uIcc a x) := by
    intro z hz
    have hzDom :
        z ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
      by_cases hax : a ≤ x
      · exact hDomConv.ordConnected.out haDom hxDom (by simpa [Set.uIcc_of_le hax] using hz)
      · have hxa : x ≤ a := le_of_not_ge hax
        exact hDomConv.ordConnected.out hxDom haDom (by simpa [Set.uIcc_of_ge hxa] using hz)
    exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
      φ a z hzDom
  exact hContInt.congr hEq

/-- More generally, between any two scalar effective-domain points of the primitive, the primitive
is continuous on the whole unordered closed interval joining them. -/
lemma helperForTheorem_5_24_4_primitiveValue_continuousOn_uIcc_of_domain_points
    (φ : ℝ → EReal) (a x y : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    ContinuousOn (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.uIcc x y) := by
  have hIntXY :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume x y :=
    helperForTheorem_5_24_4_intervalIntegrable_toReal_of_domain_points φ a x y hxDom hyDom
  have hContIntReal :
      ContinuousOn (fun z : ℝ => ∫ t in x..z, (φ t).toReal) (Set.uIcc x y) :=
    intervalIntegral.continuousOn_primitive_interval' hIntXY (by simp)
  have hContInt :
      ContinuousOn
        (fun z : ℝ => (((∫ t in x..z, (φ t).toReal) : ℝ) : EReal))
        (Set.uIcc x y) :=
    continuous_coe_real_ereal.comp_continuousOn hContIntReal
  have hxNotTop :
      oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊤ : EReal) := by
    have hxLtTop :
        oneDimensionalIntervalIntegralPrimitiveValue φ a x < (⊤ : EReal) := by
      simpa [scalarEffectiveDomain, effectiveDomain_eq,
        helperForTheorem_5_24_4_scalarPoint_primitive_eval] using hxDom
    exact (lt_top_iff_ne_top).1 hxLtTop
  have hxNotBot :
      oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊥ : EReal) := by
    simpa [helperForTheorem_5_24_4_scalarPoint_primitive_eval] using
      helperForTheorem_5_24_4_primitive_ne_bot φ a (scalarPoint x)
  have hxCoe :
      (((oneDimensionalIntervalIntegralPrimitiveValue φ a x).toReal : ℝ) : EReal) =
        oneDimensionalIntervalIntegralPrimitiveValue φ a x :=
    EReal.coe_toReal hxNotTop hxNotBot
  have hContModel :
      ContinuousOn
        (fun z : ℝ =>
          (((∫ t in x..z, (φ t).toReal) +
              (oneDimensionalIntervalIntegralPrimitiveValue φ a x).toReal : ℝ) : EReal))
        (Set.uIcc x y) :=
    continuous_coe_real_ereal.comp_continuousOn
      (hContIntReal.add continuousOn_const)
  have hDomConv :
      Convex ℝ (scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :=
    helperForTheorem_5_24_4_scalarEffectiveDomain_convex_intervalIntegralPrimitive
      φ a hmono ha
  have hEq :
      Set.EqOn
        (oneDimensionalIntervalIntegralPrimitiveValue φ a)
        (fun z : ℝ =>
          (((∫ t in x..z, (φ t).toReal) +
              (oneDimensionalIntervalIntegralPrimitiveValue φ a x).toReal : ℝ) : EReal))
        (Set.uIcc x y) := by
    intro z hz
    have hzDom :
        z ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
      by_cases hxy : x ≤ y
      · exact hDomConv.ordConnected.out hxDom hyDom (by simpa [Set.uIcc_of_le hxy] using hz)
      · have hyx : y ≤ x := le_of_not_ge hxy
        exact hDomConv.ordConnected.out hyDom hxDom (by simpa [Set.uIcc_of_ge hyx] using hz)
    have hsub :
        oneDimensionalIntervalIntegralPrimitiveValue φ a z -
            (((oneDimensionalIntervalIntegralPrimitiveValue φ a x).toReal : ℝ) : EReal) =
          (((∫ t in x..z, (φ t).toReal) : ℝ) : EReal) := by
      simpa [hxCoe] using
        helperForTheorem_5_24_4_primitiveValue_sub_eq_integral_of_domain_points
          φ a x z hxDom hzDom
    calc
      oneDimensionalIntervalIntegralPrimitiveValue φ a z
          =
            (oneDimensionalIntervalIntegralPrimitiveValue φ a z -
                (((oneDimensionalIntervalIntegralPrimitiveValue φ a x).toReal : ℝ) : EReal)) +
              (((oneDimensionalIntervalIntegralPrimitiveValue φ a x).toReal : ℝ) : EReal) := by
            symm
            simpa using
              (EReal.sub_add_cancel
                (a := oneDimensionalIntervalIntegralPrimitiveValue φ a z)
                (b := (oneDimensionalIntervalIntegralPrimitiveValue φ a x).toReal))
      _ =
            (((∫ t in x..z, (φ t).toReal) +
                (oneDimensionalIntervalIntegralPrimitiveValue φ a x).toReal : ℝ) : EReal) := by
            norm_num [hsub, EReal.coe_add]
  exact hContModel.congr hEq

/-- If a scalar domain point is bracketed by domain points on both sides, the primitive is
continuous there. This packages the interior continuity needed later for the closedness proof. -/
lemma helperForTheorem_5_24_4_primitiveValue_continuousAt_of_domain_points_straddling
    (φ : ℝ → EReal) (a x y z : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hzDom : z ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyx : y < x) (hxz : x < z) :
    ContinuousAt (oneDimensionalIntervalIntegralPrimitiveValue φ a) x := by
  have hyz : y < z := lt_trans hyx hxz
  have hcont :
      ContinuousOn (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.uIcc y z) :=
    helperForTheorem_5_24_4_primitiveValue_continuousOn_uIcc_of_domain_points
      φ a y z hmono ha hyDom hzDom
  exact hcont.continuousAt (by
    simpa [Set.uIcc_of_lt hyz] using (Icc_mem_nhds hyx hxz : Set.Icc y z ∈ nhds x))

/-- At a scalar domain point with no domain points strictly to the right, continuity on a left
domain segment gives lower semicontinuity from the left. -/
lemma helperForTheorem_5_24_4_primitiveValue_lowerSemicontinuousWithinAt_left_of_rightEndpoint
    (φ : ℝ → EReal) (a x y : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyx : y < x) :
    LowerSemicontinuousWithinAt (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.Iic x) x := by
  have hyx_le : y ≤ x := hyx.le
  have hcont :
      ContinuousOn (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.uIcc y x) :=
    helperForTheorem_5_24_4_primitiveValue_continuousOn_uIcc_of_domain_points
      φ a y x hmono ha hyDom hxDom
  have hcontWithin :
      ContinuousWithinAt (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.uIcc y x) x :=
    hcont.continuousWithinAt (by simpa [Set.uIcc_of_le hyx_le] using
      (show x ∈ Set.Icc y x from ⟨hyx_le, le_rfl⟩))
  have hmem :
      Set.uIcc y x ∈ nhdsWithin x (Set.Iic x) := by
    simpa [Set.uIcc_of_le hyx_le] using
      (Icc_mem_nhdsLE hyx : Set.Icc y x ∈ nhdsWithin x (Set.Iic x))
  exact (hcontWithin.mono_of_mem_nhdsWithin hmem).lowerSemicontinuousWithinAt

/-- The right-sided analogue of the previous lemma. -/
lemma helperForTheorem_5_24_4_primitiveValue_lowerSemicontinuousWithinAt_right_of_leftEndpoint
    (φ : ℝ → EReal) (a x y : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hxy : x < y) :
    LowerSemicontinuousWithinAt (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.Ici x) x := by
  have hxy_le : x ≤ y := hxy.le
  have hcont :
      ContinuousOn (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.uIcc x y) :=
    helperForTheorem_5_24_4_primitiveValue_continuousOn_uIcc_of_domain_points
      φ a x y hmono ha hxDom hyDom
  have hcontWithin :
      ContinuousWithinAt (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.uIcc x y) x :=
    hcont.continuousWithinAt (by simpa [Set.uIcc_of_le hxy_le] using
      (show x ∈ Set.Icc x y from ⟨le_rfl, hxy_le⟩))
  have hmem :
      Set.uIcc x y ∈ nhdsWithin x (Set.Ici x) := by
    simpa [Set.uIcc_of_le hxy_le] using
      (Icc_mem_nhdsGE hxy : Set.Icc x y ∈ nhdsWithin x (Set.Ici x))
  exact (hcontWithin.mono_of_mem_nhdsWithin hmem).lowerSemicontinuousWithinAt

/-- Any point outside the scalar effective domain of the primitive must already lie strictly to
one side of the whole interval `J`; there are no interior gaps because the domain is convex and
contains the base point `a`. -/
lemma helperForTheorem_5_24_4_off_scalarEffectiveDomain_is_exterior
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxOff : x ∉ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    IsRightOfScalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) x ∨
      IsLeftOfScalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) x := by
  let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
  have haDom : a ∈ scalarEffectiveDomain f :=
    helperForTheorem_5_24_4_scalarBasePoint_mem_scalarEffectiveDomain φ a
  have hconv : Convex ℝ (scalarEffectiveDomain f) :=
    helperForTheorem_5_24_4_scalarEffectiveDomain_convex_intervalIntegralPrimitive φ a hmono ha
  by_cases hax : a ≤ x
  · left
    intro y hy
    by_contra hxy
    have hxy' : x ≤ y := le_of_not_gt hxy
    have hxDom : x ∈ scalarEffectiveDomain f :=
      hconv.ordConnected.out haDom hy ⟨hax, hxy'⟩
    exact hxOff hxDom
  · right
    intro y hy
    by_contra hyx
    have hyx' : y ≤ x := le_of_not_gt hyx
    have hxa : x ≤ a := le_of_not_ge hax
    have hxDom : x ∈ scalarEffectiveDomain f :=
      hconv.ordConnected.out hy haDom ⟨hyx', hxa⟩
    exact hxOff hxDom

/-- Outside the scalar effective domain, the primitive can only take the value `+∞`, since it
never takes the value `-∞`. -/
lemma helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain
    (φ : ℝ → EReal) (a x : ℝ)
    (hxOff : x ∉ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint x) = (⊤ : EReal) := by
  by_contra hxNotTop
  have hxLtTop :
      oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint x) < (⊤ : EReal) :=
    (lt_top_iff_ne_top).2 hxNotTop
  have hxEff :
      scalarPoint x ∈
        effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
          (oneDimensionalIntervalIntegralPrimitive φ a) := by
    simpa [effectiveDomain_eq] using
      (show scalarPoint x ∈
          {u | u ∈ (Set.univ : Set (Fin 1 → ℝ)) ∧
            oneDimensionalIntervalIntegralPrimitive φ a u < (⊤ : EReal)} from
        ⟨by simp, hxLtTop⟩)
  have hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
    simpa [scalarEffectiveDomain] using hxEff
  exact hxOff hxDom

/-- Every scalar effective-domain point of the primitive is a lower-semicontinuity point. The only
input beyond the interval-integral formulas is that outside the scalar domain the primitive equals
`⊤`, so missing one-sided domain points cause no lower-semicontinuity loss. -/
lemma helperForTheorem_5_24_4_primitiveValue_lowerSemicontinuousAt_of_mem_scalarEffectiveDomain
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    LowerSemicontinuousAt (oneDimensionalIntervalIntegralPrimitiveValue φ a) x := by
  let f := oneDimensionalIntervalIntegralPrimitiveValue φ a
  by_cases hLeft : ∃ y, y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) ∧ y < x
  · rcases hLeft with ⟨y, hyDom, hyx⟩
    by_cases hRight : ∃ z, z ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) ∧ x < z
    · rcases hRight with ⟨z, hzDom, hxz⟩
      exact
        (helperForTheorem_5_24_4_primitiveValue_continuousAt_of_domain_points_straddling
          φ a x y z hmono ha hyDom hxDom hzDom hyx hxz).lowerSemicontinuousAt
    · have hleft :
          LowerSemicontinuousWithinAt f (Set.Iic x) x :=
        helperForTheorem_5_24_4_primitiveValue_lowerSemicontinuousWithinAt_left_of_rightEndpoint
          φ a x y hmono ha hyDom hxDom hyx
      have hright :
          LowerSemicontinuousWithinAt f (Set.Ioi x) x := by
        intro b hb
        refine Filter.mem_of_superset self_mem_nhdsWithin ?_
        intro z hz
        have hzOff :
            z ∉ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
          intro hzDom
          exact hRight ⟨z, hzDom, hz⟩
        have hzTop : f z = (⊤ : EReal) := by
          simpa [f] using
            helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain φ a z hzOff
        simpa [f, hzTop] using hb.trans_le le_top
      intro b hb
      have hleftMem : {u : ℝ | b < f u} ∈ nhdsWithin x (Set.Iic x) := hleft b hb
      have hrightMem : {u : ℝ | b < f u} ∈ nhdsWithin x (Set.Ioi x) := hright b hb
      have hsup : {u : ℝ | b < f u} ∈ nhdsWithin x (Set.Iic x) ⊔ nhdsWithin x (Set.Ioi x) :=
        (Filter.mem_sup).2 ⟨hleftMem, hrightMem⟩
      have hEq :
          nhdsWithin x (Set.Iic x) ⊔ nhdsWithin x (Set.Ioi x) = nhds x := by
        simpa [nhdsWithin_univ] using
          (nhdsWithinLE_sup_nhdsWithinGT (s := (Set.univ : Set ℝ)) x)
      rw [hEq] at hsup
      exact hsup
  · by_cases hRight : ∃ z, z ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) ∧ x < z
    · rcases hRight with ⟨z, hzDom, hxz⟩
      have hright :
          LowerSemicontinuousWithinAt f (Set.Ici x) x :=
        helperForTheorem_5_24_4_primitiveValue_lowerSemicontinuousWithinAt_right_of_leftEndpoint
          φ a x z hmono ha hxDom hzDom hxz
      have hleft :
          LowerSemicontinuousWithinAt f (Set.Iio x) x := by
        intro b hb
        refine Filter.mem_of_superset self_mem_nhdsWithin ?_
        intro z hz
        have hzOff :
            z ∉ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
          intro hzDom
          exact hLeft ⟨z, hzDom, hz⟩
        have hzTop : f z = (⊤ : EReal) := by
          simpa [f] using
            helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain φ a z hzOff
        simpa [f, hzTop] using hb.trans_le le_top
      intro b hb
      have hleftMem : {u : ℝ | b < f u} ∈ nhdsWithin x (Set.Iio x) := hleft b hb
      have hrightMem : {u : ℝ | b < f u} ∈ nhdsWithin x (Set.Ici x) := hright b hb
      have hsup : {u : ℝ | b < f u} ∈ nhdsWithin x (Set.Iio x) ⊔ nhdsWithin x (Set.Ici x) :=
        (Filter.mem_sup).2 ⟨hleftMem, hrightMem⟩
      have hEq :
          nhdsWithin x (Set.Iio x) ⊔ nhdsWithin x (Set.Ici x) = nhds x := by
        simpa [nhdsWithin_univ] using
          (nhdsWithinLT_sup_nhdsWithinGE (s := (Set.univ : Set ℝ)) x)
      rw [hEq] at hsup
      exact hsup
    · intro b hb
      have hleftMem : {u : ℝ | b < f u} ∈ nhdsWithin x (Set.Iio x) := by
        refine Filter.mem_of_superset self_mem_nhdsWithin ?_
        intro z hz
        have hzOff :
            z ∉ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
          intro hzDom
          exact hLeft ⟨z, hzDom, hz⟩
        have hzTop : f z = (⊤ : EReal) := by
          simpa [f] using
            helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain φ a z hzOff
        simpa [f, hzTop] using hb.trans_le le_top
      have hrightMem : {u : ℝ | b < f u} ∈ nhdsWithin x (Set.Ioi x) := by
        refine Filter.mem_of_superset self_mem_nhdsWithin ?_
        intro z hz
        have hzOff :
            z ∉ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
          intro hzDom
          exact hRight ⟨z, hzDom, hz⟩
        have hzTop : f z = (⊤ : EReal) := by
          simpa [f] using
            helperForTheorem_5_24_4_primitive_eq_top_of_not_mem_scalarEffectiveDomain φ a z hzOff
        simpa [f, hzTop] using hb.trans_le le_top
      have hsup : {u : ℝ | b < f u} ∈ nhdsWithin x (Set.Iio x) ⊔ nhdsWithin x (Set.Ioi x) :=
        (Filter.mem_sup).2 ⟨hleftMem, hrightMem⟩
      have hEq :
          nhdsWithin x (Set.Iio x) ⊔ nhdsWithin x (Set.Ioi x) =
            nhdsWithin x (Set.univ \ ({x} : Set ℝ)) := by
        simpa [nhdsWithin_univ] using
          (nhdsWithinLT_sup_nhdsWithinGT (s := (Set.univ : Set ℝ)) x)
      rw [hEq] at hsup
      have hxMem : x ∈ {u : ℝ | b < f u} := hb
      have hpunct : {u : ℝ | b < f u} ∈ nhdsWithin x ({x}ᶜ) := by
        simpa [Set.diff_eq] using hsup
      have hnhds :
          insert x {u : ℝ | b < f u} ∈ nhds x :=
        (insert_mem_nhds_iff).2 hpunct
      simpa [Set.insert_eq_of_mem hxMem] using hnhds

/-- If the monotone profile takes the value `+∞` at a scalar domain point, then no larger scalar
point can remain in the primitive's effective domain. -/
lemma helperForTheorem_5_24_4_no_domain_point_to_right_of_top_profile
    (φ : ℝ → EReal) (a x y : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hxy : x < y) (hxTop : φ x = (⊤ : EReal)) :
    y ∉ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
  intro hyDom
  let z : ℝ := (x + y) / 2
  have hzIoo : z ∈ Set.Ioo x y := by
    dsimp [z]
    constructor <;> linarith
  have hzOpen : z ∈ Set.uIoo x y := by
    simpa [Set.uIoo_of_lt hxy] using hzIoo
  have hzFinite :
      z ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
    helperForTheorem_5_24_4_finite_profile_on_open_interval_of_domain_points
      φ a x y z ha hxDom hyDom hzOpen
  have hzTop : φ z = (⊤ : EReal) := by
    exact top_le_iff.mp (hxTop ▸ hmono (le_of_lt hzIoo.1))
  exact hzFinite.1 hzTop

/-- If the monotone profile takes the value `-∞` at a scalar domain point, then no smaller scalar
point can remain in the primitive's effective domain. -/
lemma helperForTheorem_5_24_4_no_domain_point_to_left_of_bot_profile
    (φ : ℝ → EReal) (a x y : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyx : y < x) (hxBot : φ x = (⊥ : EReal)) :
    y ∉ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
  intro hyDom
  let z : ℝ := (x + y) / 2
  have hzIoo : z ∈ Set.Ioo y x := by
    dsimp [z]
    constructor <;> linarith
  have hzOpen : z ∈ Set.uIoo y x := by
    simpa [Set.uIoo_of_lt hyx] using hzIoo
  have hzFinite :
      z ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
    helperForTheorem_5_24_4_finite_profile_on_open_interval_of_domain_points
      φ a y x z ha hyDom hxDom hzOpen
  have hzLeBot : φ z ≤ (⊥ : EReal) := by
    simpa [hxBot] using hmono (le_of_lt hzIoo.2)
  have hzBot : φ z = (⊥ : EReal) := le_bot_iff.mp hzLeBot
  exact hzFinite.2 hzBot

/-- On the scalar effective-domain interval `J`, the primitive satisfies the same convex
combination inequality as in the textbook proof, even when the endpoints lie on the boundary of
`J`. -/
lemma helperForTheorem_5_24_4_primitiveValue_convexCombo_of_domain_lt
    (φ : ℝ → EReal) (a x y θ : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxy : x < y)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let z := (1 - θ) * x + θ * y
    oneDimensionalIntervalIntegralPrimitiveValue φ a z ≤
      ((1 - θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a x +
        ((θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a y := by
  dsimp
  let z := (1 - θ) * x + θ * y
  by_cases hθx : θ = 0
  · subst hθx
    simp
  by_cases hθy : θ = 1
  · subst hθy
    have hz1 : ((1 - (1 : ℝ)) * x + (1 : ℝ) * y) = y := by
      ring
    have hzeroR : ((1 : ℝ) - 1) = 0 := by
      ring
    have hzero : (1 - ((1 : ℝ) : EReal)) = (0 : EReal) := by
      exact_mod_cast hzeroR
    rw [hz1, hzero]
    simp
  have hθlt : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθx)
  have hθgt : θ < 1 := lt_of_le_of_ne hθ1 hθy
  have hz_repr : z = x + θ * (y - x) := by
    dsimp [z]
    ring
  have hxz : x < z := by
    rw [hz_repr]
    nlinarith
  have hzy : z < y := by
    rw [hz_repr]
    nlinarith
  have hzOpen : z ∈ Set.uIoo x y := by
    simpa [z, Set.uIoo_of_lt hxy] using (show z ∈ Set.Ioo x y from ⟨hxz, hzy⟩)
  have hzFinite :
      z ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
    helperForTheorem_5_24_4_finite_profile_on_open_interval_of_domain_points
      φ a x y z ha hxDom hyDom hzOpen
  have hzDom :
      z ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) :=
    helperForTheorem_5_24_4_mem_scalarEffectiveDomain_of_finite_profile
      φ a z hmono ha hzFinite
  let Fx : ℝ := ∫ t in a..x, (φ t).toReal
  let Fy : ℝ := ∫ t in a..y, (φ t).toReal
  let Fz : ℝ := ∫ t in a..z, (φ t).toReal
  have hUpperE :
      (((∫ t in x..z, (φ t).toReal) : ℝ) : EReal) ≤
        ((((z - x) * (φ z).toReal : ℝ) : EReal)) :=
    helperForTheorem_5_24_4_integral_le_profile_mul_sub_of_domain_lt
      φ a x z hmono ha hxDom hzDom hzFinite hxz
  have hLowerE :
      ((((y - z) * (φ z).toReal : ℝ) : EReal)) ≤
        (((∫ t in z..y, (φ t).toReal) : ℝ) : EReal) :=
    helperForTheorem_5_24_4_profile_mul_sub_le_integral_of_domain_lt
      φ a z y hmono ha hzDom hyDom hzFinite hzy
  have hUpper :
      ∫ t in x..z, (φ t).toReal ≤ (z - x) * (φ z).toReal := by
    exact_mod_cast hUpperE
  have hLower :
      (y - z) * (φ z).toReal ≤ ∫ t in z..y, (φ t).toReal := by
    exact_mod_cast hLowerE
  have hzEq1 : z - x = θ * (y - x) := by
    dsimp [z]
    ring
  have hzEq2 : y - z = (1 - θ) * (y - x) := by
    dsimp [z]
    ring
  have hBalance : (1 - θ) * (z - x) = θ * (y - z) := by
    rw [hzEq1, hzEq2]
    ring
  have hWeighted :
      (1 - θ) * (∫ t in x..z, (φ t).toReal) ≤
        θ * (∫ t in z..y, (φ t).toReal) := by
    have h1 :
        (1 - θ) * (∫ t in x..z, (φ t).toReal) ≤
          (1 - θ) * ((z - x) * (φ z).toReal) :=
      mul_le_mul_of_nonneg_left hUpper (sub_nonneg.mpr hθ1)
    have h2 :
        θ * ((y - z) * (φ z).toReal) ≤
          θ * (∫ t in z..y, (φ t).toReal) :=
      mul_le_mul_of_nonneg_left hLower hθ0
    calc
      (1 - θ) * (∫ t in x..z, (φ t).toReal)
        ≤ (1 - θ) * ((z - x) * (φ z).toReal) := h1
      _ = ((1 - θ) * (z - x)) * (φ z).toReal := by ring
      _ = (θ * (y - z)) * (φ z).toReal := by rw [hBalance]
      _ = θ * ((y - z) * (φ z).toReal) := by ring
      _ ≤ θ * (∫ t in z..y, (φ t).toReal) := h2
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a z hzDom with
    ⟨_, hIntAz⟩
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a y hyDom with
    ⟨_, hIntAy⟩
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a x hxDom with
    ⟨_, hIntAx⟩
  have hSub1 : Fz - Fx = ∫ t in x..z, (φ t).toReal := by
    dsimp [Fx, Fz]
    exact intervalIntegral.integral_interval_sub_left hIntAz hIntAx
  have hSub2 : Fy - Fz = ∫ t in z..y, (φ t).toReal := by
    dsimp [Fy, Fz]
    exact intervalIntegral.integral_interval_sub_left hIntAy hIntAz
  have hReal :
      Fz ≤ (1 - θ) * Fx + θ * Fy := by
    have hWeighted' : (1 - θ) * (Fz - Fx) ≤ θ * (Fy - Fz) := by
      simpa [hSub1, hSub2] using hWeighted
    nlinarith
  have hFx :
      oneDimensionalIntervalIntegralPrimitiveValue φ a x = ((Fx : ℝ) : EReal) := by
    dsimp [Fx]
    exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
      φ a x hxDom
  have hFy :
      oneDimensionalIntervalIntegralPrimitiveValue φ a y = ((Fy : ℝ) : EReal) := by
    dsimp [Fy]
    exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
      φ a y hyDom
  have hFz :
      oneDimensionalIntervalIntegralPrimitiveValue φ a z = ((Fz : ℝ) : EReal) := by
    dsimp [Fz]
    exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
      φ a z hzDom
  rw [hFx, hFy, hFz]
  exact_mod_cast hReal

/-- The domain-endpoint convex-combination inequality also covers the degenerate case `x = y`. -/
lemma helperForTheorem_5_24_4_primitiveValue_convexCombo_of_domain_le
    (φ : ℝ → EReal) (a x y θ : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxy : x ≤ y)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let z := (1 - θ) * x + θ * y
    oneDimensionalIntervalIntegralPrimitiveValue φ a z ≤
      ((1 - θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a x +
        ((θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a y := by
  rcases lt_or_eq_of_le hxy with hxy' | rfl
  · simpa using
      helperForTheorem_5_24_4_primitiveValue_convexCombo_of_domain_lt
        φ a x y θ hmono ha hxy' hxDom hyDom hθ0 hθ1
  · dsimp
    let Fx : ℝ := ∫ t in a..x, (φ t).toReal
    have hFx :
        oneDimensionalIntervalIntegralPrimitiveValue φ a x = ((Fx : ℝ) : EReal) := by
      dsimp [Fx]
      exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
        φ a x hxDom
    have hReal :
        Fx ≤ (1 - θ) * Fx + θ * Fx := by
      have hEq : (1 - θ) * Fx + θ * Fx = Fx := by ring
      rw [hEq]
    have hzEq : ((1 - θ) * x + θ * x) = x := by ring
    calc
      oneDimensionalIntervalIntegralPrimitiveValue φ a ((1 - θ) * x + θ * x)
        = ((Fx : ℝ) : EReal) := by
            rw [hzEq, hFx]
      _ ≤ ((1 - θ : ℝ) : EReal) * ((Fx : ℝ) : EReal) +
            ((θ : ℝ) : EReal) * ((Fx : ℝ) : EReal) := by
              exact_mod_cast hReal
      _ = ((1 - θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a x +
            ((θ : ℝ) : EReal) * oneDimensionalIntervalIntegralPrimitiveValue φ a x := by
            rw [hFx]

/-- To the strict right of the primitive's domain, the monotone profile has already jumped to
`+∞`. -/
lemma helperForTheorem_5_24_4_profile_eq_top_of_rightOfPrimitiveDomain
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxRight : IsRightOfScalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) x) :
    φ x = (⊤ : EReal) := by
  have haDom :
      a ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
    have haEval :
        oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint a) =
          (((0 : ℝ) : EReal)) := by
      simpa using helperForTheorem_5_24_4_primitive_at_scalarBasePoint φ a
    have haNotTop :
        oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint a) ≠ (⊤ : EReal) := by
      rw [haEval]
      simp
    simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top, haNotTop]
  have hax : a < x := hxRight a haDom
  by_contra hxTop
  have hxBot : φ x ≠ (⊥ : EReal) := by
    intro hxBot
    exact ha.2 (le_bot_iff.mp (hxBot ▸ hmono hax.le))
  have hxFinite : x ∈ oneDimensionalPrimitiveFiniteValueSet φ := ⟨hxTop, hxBot⟩
  have hxDom :
      x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) :=
    helperForTheorem_5_24_4_mem_scalarEffectiveDomain_of_finite_profile
      φ a x hmono ha hxFinite
  exact (lt_irrefl x) (hxRight x hxDom)

/-- To the strict left of the primitive's domain, the monotone profile has already fallen to
`-∞`. -/
lemma helperForTheorem_5_24_4_profile_eq_bot_of_leftOfPrimitiveDomain
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxLeft : IsLeftOfScalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) x) :
    φ x = (⊥ : EReal) := by
  have haDom :
      a ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
    have haEval :
        oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint a) =
          (((0 : ℝ) : EReal)) := by
      simpa using helperForTheorem_5_24_4_primitive_at_scalarBasePoint φ a
    have haNotTop :
        oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint a) ≠ (⊤ : EReal) := by
      rw [haEval]
      simp
    simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top, haNotTop]
  have hxa : x < a := hxLeft a haDom
  by_contra hxBot
  have hxTop : φ x ≠ (⊤ : EReal) := by
    intro hxTop
    exact ha.1 (top_le_iff.mp (hxTop ▸ hmono hxa.le))
  have hxFinite : x ∈ oneDimensionalPrimitiveFiniteValueSet φ := ⟨hxTop, hxBot⟩
  have hxDom :
      x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) :=
    helperForTheorem_5_24_4_mem_scalarEffectiveDomain_of_finite_profile
      φ a x hmono ha hxFinite
  exact (lt_irrefl x) (hxLeft x hxDom)

/-- On the two scalar exterior regions, the derivative-band statement is already forced by the
definition of the derivative extensions together with the monotone profile's jump to `±∞`. -/
lemma helperForTheorem_5_24_4_scalarBand_on_primitive_exterior
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
    (IsRightOfScalarEffectiveDomain f x ∨ IsLeftOfScalarEffectiveDomain f x) →
      (leftDerivativeExtension f x ≤ φ x ∧ φ x ≤ rightDerivativeExtension f x) := by
  dsimp
  intro hxExterior
  rcases hxExterior with hxRight | hxLeft
  · have hxTop :
        φ x = (⊤ : EReal) :=
      helperForTheorem_5_24_4_profile_eq_top_of_rightOfPrimitiveDomain
        φ a x hmono ha hxRight
    constructor <;> simp [leftDerivativeExtension, rightDerivativeExtension, hxRight, hxTop]
  · have hxBot :
        φ x = (⊥ : EReal) :=
      helperForTheorem_5_24_4_profile_eq_bot_of_leftOfPrimitiveDomain
        φ a x hmono ha hxLeft
    have haDom :
        a ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
      have haEval :
          oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint a) =
            (((0 : ℝ) : EReal)) := by
        simpa using helperForTheorem_5_24_4_primitive_at_scalarBasePoint φ a
      have haNotTop :
          oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint a) ≠ (⊤ : EReal) := by
        rw [haEval]
        simp
      simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top, haNotTop]
    have hxNotRight :
        ¬ IsRightOfScalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) x := by
      intro hxRight
      exact (lt_irrefl a) (lt_trans (hxRight a haDom) (hxLeft a haDom))
    constructor <;> simp [leftDerivativeExtension, rightDerivativeExtension, hxLeft, hxNotRight, hxBot]

/-- Helper for Theorem 5.24.4: a monotone profile always lies between its left and right
one-sided limit profiles. -/
lemma helperForTheorem_5_24_4_monotone_profile_between_its_one_sided_limits
    (φ : ℝ → EReal) (hmono : Monotone φ) :
    ∀ x : ℝ, leftLimitProfile φ x ≤ φ x ∧ φ x ≤ rightLimitProfile φ x := by
  intro x
  constructor
  · -- Every strict-left value is at most `φ x`, so their supremum is also at most `φ x`.
    refine sSup_le ?_
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hmono (le_of_lt hz)
  · -- Every strict-right value is at least `φ x`, so their infimum still dominates `φ x`.
    refine le_sInf ?_
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hmono (le_of_lt hz)

/-- To prove the scalar derivative-band statement for the interval-integral primitive, it is
enough to prove it on the scalar effective domain `J`; the exterior cases are already handled by
the profile jumping to `±∞`. -/
lemma helperForTheorem_5_24_4_scalarBand_of_domain_band
    (φ : ℝ → EReal) (a : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    let f : (Fin 1 → ℝ) → EReal := oneDimensionalIntervalIntegralPrimitive φ a
    (∀ x ∈ scalarEffectiveDomain f,
        leftDerivativeExtension f x ≤ φ x ∧ φ x ≤ rightDerivativeExtension f x) →
      ∀ x : ℝ, leftDerivativeExtension f x ≤ φ x ∧ φ x ≤ rightDerivativeExtension f x := by
  dsimp
  intro hDomBand x
  by_cases hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)
  · exact hDomBand x hxDom
  · rcases
      helperForTheorem_5_24_4_off_scalarEffectiveDomain_is_exterior φ a x hmono ha hxDom with
      hxRight | hxLeft
    · exact
        helperForTheorem_5_24_4_scalarBand_on_primitive_exterior φ a x hmono ha (Or.inl hxRight)
    · exact
        helperForTheorem_5_24_4_scalarBand_on_primitive_exterior φ a x hmono ha (Or.inr hxLeft)


end Section24
end Chap05

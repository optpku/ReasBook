/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap06
section Section06

/-- A self-map `f : X → X` is a contraction if it is 1-Lipschitz. -/
def IsContraction {X : Type*} [MetricSpace X] (f : X → X) : Prop :=
  ∀ x y : X, dist (f x) (f y) ≤ dist x y

/-- A self-map `f : X → X` is a strict contraction if it has a contraction constant `c` with `0 < c < 1`. -/
def IsStrictContraction {X : Type*} [MetricSpace X] (f : X → X) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y

/-- A real number `c` is a contraction constant of `f` if `0 < c < 1` and `dist (f x) (f y) ≤ c * dist x y` for all `x,y`. -/
def IsContractionConstant {X : Type*} [MetricSpace X] (f : X → X) (c : ℝ) : Prop :=
  0 < c ∧ c < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y

/-- Definition 6.13 (Contraction and strict contraction):
(i) `f` is a contraction iff `dist (f x) (f y) ≤ dist x y` for all `x,y`.
(ii) `f` is a strict contraction iff there exists `c` with `0 < c < 1` such that
`dist (f x) (f y) ≤ c * dist x y` for all `x,y`; such a `c` is a contraction constant. -/
theorem definition_6_13
    {X : Type*} [MetricSpace X] (f : X → X) :
    (IsContraction f ↔ ∀ x y : X, dist (f x) (f y) ≤ dist x y) ∧
      (IsStrictContraction f ↔ ∃ c : ℝ, IsContractionConstant f c) := by
  constructor <;> rfl

/-- Proposition 6.13(1): if `f : [a,b] → [a,b]` is continuous on `[a,b]`,
differentiable on `(a,b)`, and `|f'| ≤ 1` on `(a,b)`, then
`|f(x) - f(y)| ≤ |x - y|` for all `x,y ∈ [a,b]`;
in particular, the induced self-map of `[a,b]` is a non-expanding contraction. -/
theorem deriv_bound_one_on_interval_implies_nonexpanding
    {a b : ℝ} (f : ℝ → ℝ)
    (hmaps : Set.MapsTo f (Set.Icc a b) (Set.Icc a b))
    (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, |deriv f x| ≤ (1 : ℝ)) :
    (∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ |x - y|) ∧
      IsContraction (Set.MapsTo.restrict f (Set.Icc a b) (Set.Icc a b) hmaps) := by
  have hdiffIcc : DifferentiableOn ℝ f (interior (Set.Icc a b)) := by
    simpa [interior_Icc] using hdiff
  have hderivBounds :
      ∀ x ∈ interior (Set.Icc a b), (-1 : ℝ) ≤ deriv f x ∧ deriv f x ≤ (1 : ℝ) := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo a b := by
      simpa [interior_Icc] using hx
    have hderivx : |deriv f x| ≤ (1 : ℝ) := hderiv x hxIoo
    simpa using (abs_le.mp hderivx)
  have hsub_le :
      ∀ {x y : ℝ}, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → f y - f x ≤ y - x := by
    intro x y hx hy hxy
    have hderivUpper : ∀ z ∈ interior (Set.Icc a b), deriv f z ≤ (1 : ℝ) := by
      intro z hz
      exact (hderivBounds z hz).2
    have hxy' :=
      Convex.image_sub_le_mul_sub_of_deriv_le (hD := convex_Icc a b)
        (f := f) (hf := hcont) (hf' := hdiffIcc) (C := 1) hderivUpper x hx y hy hxy
    simpa using hxy'
  have hneg_sub_le :
      ∀ {x y : ℝ}, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → -(y - x) ≤ f y - f x := by
    intro x y hx hy hxy
    have hderivLower : ∀ z ∈ interior (Set.Icc a b), (-1 : ℝ) ≤ deriv f z := by
      intro z hz
      exact (hderivBounds z hz).1
    have hxy' :=
      Convex.mul_sub_le_image_sub_of_le_deriv (hD := convex_Icc a b)
        (f := f) (hf := hcont) (hf' := hdiffIcc) (C := -1) hderivLower x hx y hy hxy
    simpa using hxy'
  have habs_of_le :
      ∀ {x y : ℝ}, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → |f x - f y| ≤ |x - y| := by
    intro x y hx hy hxy
    have hup : f y - f x ≤ y - x := hsub_le hx hy hxy
    have hlow : -(y - x) ≤ f y - f x := hneg_sub_le hx hy hxy
    have habs : |f y - f x| ≤ y - x := by
      exact (abs_le).2 ⟨hlow, hup⟩
    have hxy_nonpos : x - y ≤ 0 := sub_nonpos.mpr hxy
    have habs_xy : |x - y| = y - x := by
      calc
        |x - y| = -(x - y) := abs_of_nonpos hxy_nonpos
        _ = y - x := by ring
    calc
      |f x - f y| = |f y - f x| := by rw [abs_sub_comm]
      _ ≤ y - x := habs
      _ = |x - y| := habs_xy.symm
  have hnonexp :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ |x - y| := by
    intro x hx y hy
    by_cases hxy : x ≤ y
    · exact habs_of_le hx hy hxy
    · have hyx : y ≤ x := le_of_not_ge hxy
      have hyxBound : |f y - f x| ≤ |y - x| := habs_of_le hy hx hyx
      simpa [abs_sub_comm] using hyxBound
  constructor
  · exact hnonexp
  · intro x y
    simpa [Set.MapsTo.restrict, Real.dist_eq, abs_sub_comm] using
      hnonexp x x.property y y.property

/-- Proposition 6.14: Let `f : [a,b] → ℝ` be differentiable and assume
`|f x - f y| ≤ |x - y|` for all `x,y ∈ [a,b]`. Then the derivative of `f`
within `[a,b]` satisfies `|f'(x)| ≤ 1` for all `x ∈ [a,b]`. -/
theorem contraction_on_interval_implies_deriv_bound_one
    {a b : ℝ} (f : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ f (Set.Icc a b))
    (hcontract : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ |x - y|) :
    ∀ x ∈ Set.Icc a b, |derivWithin f (Set.Icc a b) x| ≤ (1 : ℝ) := by
  intro x hx
  by_cases hablt : a < b
  · have hslope_abs_le_one :
        ∀ y ∈ Set.Icc a b, y ≠ x → |slope f x y| ≤ (1 : ℝ) := by
      intro y hy hyx
      have hcontract' : |f y - f x| ≤ |y - x| := by
        simpa [abs_sub_comm] using hcontract x hx y hy
      have hxypos : 0 < |y - x| := by
        exact abs_pos.mpr (sub_ne_zero.mpr hyx)
      rw [slope_def_field, abs_div]
      exact (div_le_iff₀ hxypos).2 (by simpa [one_mul] using hcontract')
    have hderivWithin :
        HasDerivWithinAt f (derivWithin f (Set.Icc a b) x) (Set.Icc a b) x :=
      (hdiff x hx).hasDerivWithinAt
    have htendsto :
        Filter.Tendsto (slope f x) (nhdsWithin x (Set.Icc a b \ {x}))
          (nhds (derivWithin f (Set.Icc a b) x)) :=
      (hasDerivWithinAt_iff_tendsto_slope).1 hderivWithin
    have hself : Set.Icc a b \ {x} ∈ nhdsWithin x (Set.Icc a b \ {x}) :=
      self_mem_nhdsWithin
    have hEventually :
        ∀ᶠ y in nhdsWithin x (Set.Icc a b \ {x}), slope f x y ∈ Set.Icc (-1 : ℝ) 1 := by
      filter_upwards [hself] with y hy
      have hyx : y ≠ x := by
        simpa [Set.mem_singleton_iff] using hy.2
      have habs : |slope f x y| ≤ (1 : ℝ) := hslope_abs_le_one y hy.1 hyx
      exact (abs_le.mp habs)
    have hNeBot : (nhdsWithin x (Set.Icc a b \ {x})).NeBot := by
      by_cases hxb : x < b
      · have hIocNeBot : (nhdsWithin x (Set.Ioc x b)).NeBot := by
          rw [nhdsWithin_Ioc_eq_nhdsGT hxb]
          exact nhdsGT_neBot x
        have hsubset : Set.Ioc x b ⊆ Set.Icc a b \ {x} := by
          intro y hy
          refine ⟨?_, ?_⟩
          · refine ⟨?_, hy.2⟩
            exact le_trans hx.1 (le_of_lt hy.1)
          · have hyne : y ≠ x := ne_of_gt hy.1
            simp [Set.mem_singleton_iff, hyne]
        letI : (nhdsWithin x (Set.Ioc x b)).NeBot := hIocNeBot
        exact Filter.neBot_of_le (nhdsWithin_mono x hsubset)
      · have hxb_ge : b ≤ x := le_of_not_gt hxb
        have hxb_eq : x = b := le_antisymm hx.2 hxb_ge
        have hax : a < x := by simpa [hxb_eq] using hablt
        have hIcoNeBot : (nhdsWithin x (Set.Ico a x)).NeBot := by
          rw [nhdsWithin_Ico_eq_nhdsLT hax]
          exact nhdsLT_neBot x
        have hsubset : Set.Ico a x ⊆ Set.Icc a b \ {x} := by
          intro y hy
          refine ⟨?_, ?_⟩
          · refine ⟨hy.1, ?_⟩
            exact le_trans (le_of_lt hy.2) hx.2
          · simp [Set.mem_singleton_iff, hy.2.ne]
        letI : (nhdsWithin x (Set.Ico a x)).NeBot := hIcoNeBot
        exact Filter.neBot_of_le (nhdsWithin_mono x hsubset)
    letI : (nhdsWithin x (Set.Icc a b \ {x})).NeBot := hNeBot
    have hmem : derivWithin f (Set.Icc a b) x ∈ Set.Icc (-1 : ℝ) 1 :=
      IsClosed.mem_of_tendsto isClosed_Icc htendsto hEventually
    exact (abs_le).2 hmem
  · have hba : b ≤ a := le_of_not_gt hablt
    have hEqba : b = a := le_antisymm hba (le_trans hx.1 hx.2)
    have hxeq : x = a := le_antisymm (le_trans hx.2 hba) hx.1
    subst x
    have hderivzero : derivWithin f (Set.Icc a b) a = 0 := by
      rw [hEqba]
      have hnotacc : ¬AccPt a (Filter.principal (Set.Icc a a)) := by
        rw [accPt_principal_iff_nhdsWithin]
        simp
      exact derivWithin_zero_of_not_accPt hnotacc
    rw [hderivzero]
    norm_num

/-- Helper for Proposition 6.15: from a contraction witness with `0 ≤ c < 1`,
extract the nonnegativity and distance bound needed for Lipschitz control. -/
lemma helperForProposition_6_15_unpack_nonneg_bound
    {X : Type*} [MetricSpace X] (f : X → X)
    (hcontract : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y := by
  rcases hcontract with ⟨c, hc0, _hc1, hdist⟩
  exact ⟨c, hc0, hdist⟩

/-- Helper for Proposition 6.15: convert a real-valued contraction estimate with
`c ≥ 0` into an `NNReal`-valued `LipschitzWith` bound. -/
lemma helperForProposition_6_15_lipschitzWith_of_real_contraction_bound
    {X : Type*} [MetricSpace X] (f : X → X)
    (hbound : ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y) :
    ∃ K : NNReal, LipschitzWith K f := by
  rcases hbound with ⟨c, hc0, hdist⟩
  let K : NNReal := ⟨c, hc0⟩
  refine ⟨K, ?_⟩
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa [K] using hdist x y

/-- Helper for Proposition 6.15: any map with an `NNReal` Lipschitz bound is continuous. -/
lemma helperForProposition_6_15_continuous_of_exists_lipschitzWith
    {X : Type*} [MetricSpace X] (f : X → X)
    (hlip : ∃ K : NNReal, LipschitzWith K f) :
    Continuous f := by
  rcases hlip with ⟨K, hK⟩
  exact hK.continuous

/-- Proposition 6.15: If `f : X → X` on a metric space satisfies
`dist (f x) (f y) ≤ c * dist x y` for some `c ∈ [0,1)` and all `x,y`,
then `f` is Lipschitz and therefore continuous on `X`. -/
theorem contraction_has_lipschitz_and_continuous
    {X : Type*} [MetricSpace X] (f : X → X)
    (hcontract : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y) :
    (∃ K : NNReal, LipschitzWith K f) ∧ Continuous f := by
  have hbound :
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y :=
    helperForProposition_6_15_unpack_nonneg_bound f hcontract
  have hlip : ∃ K : NNReal, LipschitzWith K f :=
    helperForProposition_6_15_lipschitzWith_of_real_contraction_bound f hbound
  have hcont : Continuous f :=
    helperForProposition_6_15_continuous_of_exists_lipschitzWith f hlip
  exact ⟨hlip, hcont⟩

/-- Definition 6.14 (Fixed point): Let X be a set and let f : X → X be a map.
An element x ∈ X is a fixed point of f if f x = x. -/
def IsFixedPoint {X : Type*} (f : X → X) (x : X) : Prop :=
  f x = x

/-- Helper for Theorem 6.7: convert a real-valued contraction bound with
`0 ≤ c < 1` into `ContractingWith` with an `NNReal` constant. -/
lemma helperForTheorem_6_7_contractingWith_of_nonneg_constant
    {X : Type*} [MetricSpace X] (f : X → X)
    (hstrict : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y) :
    ∃ K : NNReal, ContractingWith K f := by
  rcases hstrict with ⟨c, hc0, hc1, hdist⟩
  let K : NNReal := ⟨c, hc0⟩
  refine ⟨K, ?_⟩
  refine ⟨?_, ?_⟩
  · change c < 1
    simpa [K] using hc1
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [K] using hdist x y

/-- Helper for Theorem 6.7: fixed points of a `ContractingWith` map are unique. -/
lemma helperForTheorem_6_7_fixedPoint_eq_of_contractingWith
    {X : Type*} [MetricSpace X] {f : X → X} {K : NNReal}
    (hfK : ContractingWith K f) {x y : X}
    (hx : IsFixedPoint f x) (hy : IsFixedPoint f y) :
    x = y := by
  apply hfK.fixedPoint_unique'
  · simpa [IsFixedPoint, Function.IsFixedPt] using hx
  · simpa [IsFixedPoint, Function.IsFixedPt] using hy

/-- Helper for Theorem 6.7: in a nonempty complete metric space, a
`ContractingWith` map has a unique fixed point. -/
lemma helperForTheorem_6_7_existsUnique_fixedPoint_of_contractingWith
    {X : Type*} [MetricSpace X] [Nonempty X] [CompleteSpace X]
    {f : X → X} {K : NNReal} (hfK : ContractingWith K f) :
    ∃! x : X, IsFixedPoint f x := by
  refine ⟨ContractingWith.fixedPoint f hfK, ?_, ?_⟩
  · simpa [IsFixedPoint, Function.IsFixedPt] using hfK.fixedPoint_isFixedPt
  · intro y hy
    have hy' : Function.IsFixedPt f y := by
      simpa [IsFixedPoint, Function.IsFixedPt] using hy
    exact hfK.fixedPoint_unique hy'

/-- Theorem 6.7 (Contraction mapping theorem): Let `(X,d)` be a metric space and
`f : X → X` satisfy `dist (f x) (f y) ≤ c * dist x y` for some `c ∈ [0,1)` and all
`x,y`. Then `f` has at most one fixed point. If, in addition, `X` is nonempty and
complete, then `f` has exactly one fixed point. -/
theorem contraction_mapping_theorem_6_7
    {X : Type*} [MetricSpace X] (f : X → X)
    (hstrict : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y) :
    (∀ x y : X, IsFixedPoint f x → IsFixedPoint f y → x = y) ∧
      (Nonempty X → CompleteSpace X → ∃! x : X, IsFixedPoint f x) := by
  rcases helperForTheorem_6_7_contractingWith_of_nonneg_constant f hstrict with ⟨K, hfK⟩
  constructor
  · intro x y hx hy
    exact helperForTheorem_6_7_fixedPoint_eq_of_contractingWith hfK hx hy
  · intro hN hC
    letI : Nonempty X := hN
    letI : CompleteSpace X := hC
    exact helperForTheorem_6_7_existsUnique_fixedPoint_of_contractingWith hfK

/-- Helper for Proposition 6.16: the `f`-centered triangle inequality and contraction
bound imply `dist x0 y0 ≤ ε + c * dist x0 y0`. -/
lemma helperForProposition_6_16_dist_le_eps_add_c_mul_dist
    {X : Type*} [MetricSpace X]
    (f g : X → X) (c : ℝ) (x0 y0 : X) (ε : ℝ)
    (hf : IsContractionConstant f c)
    (hx0 : IsFixedPoint f x0)
    (hy0 : IsFixedPoint g y0)
    (hclose : ∀ x : X, dist (f x) (g x) ≤ ε) :
    dist x0 y0 ≤ ε + c * dist x0 y0 := by
  have hcontraction : dist (f x0) (f y0) ≤ c * dist x0 y0 := hf.2.2 x0 y0
  have hclose_y0 : dist (f y0) (g y0) ≤ ε := hclose y0
  have hsum :
      dist (f x0) (f y0) + dist (f y0) (g y0) ≤ c * dist x0 y0 + ε :=
    add_le_add hcontraction hclose_y0
  have hfixed_rewrite : dist x0 y0 = dist (f x0) (g y0) := by
    calc
      dist x0 y0 = dist (f x0) y0 := by
        simpa [IsFixedPoint] using congrArg (fun z : X => dist z y0) hx0.symm
      _ = dist (f x0) (g y0) := by
        simpa [IsFixedPoint] using congrArg (fun z : X => dist (f x0) z) hy0.symm
  calc
    dist x0 y0 = dist (f x0) (g y0) := hfixed_rewrite
    _ ≤ dist (f x0) (f y0) + dist (f y0) (g y0) := dist_triangle (f x0) (f y0) (g y0)
    _ ≤ c * dist x0 y0 + ε := hsum
    _ = ε + c * dist x0 y0 := by ring

/-- Helper for Proposition 6.16: the `g`-centered triangle inequality and contraction
bound imply `dist x0 y0 ≤ ε + c' * dist x0 y0`. -/
lemma helperForProposition_6_16_dist_le_eps_add_cprime_mul_dist
    {X : Type*} [MetricSpace X]
    (f g : X → X) (c' : ℝ) (x0 y0 : X) (ε : ℝ)
    (hg : IsContractionConstant g c')
    (hx0 : IsFixedPoint f x0)
    (hy0 : IsFixedPoint g y0)
    (hclose : ∀ x : X, dist (f x) (g x) ≤ ε) :
    dist x0 y0 ≤ ε + c' * dist x0 y0 := by
  have hclose_x0 : dist (f x0) (g x0) ≤ ε := hclose x0
  have hcontraction : dist (g x0) (g y0) ≤ c' * dist x0 y0 := hg.2.2 x0 y0
  have hsum :
      dist (f x0) (g x0) + dist (g x0) (g y0) ≤ ε + c' * dist x0 y0 :=
    add_le_add hclose_x0 hcontraction
  have hfixed_rewrite : dist x0 y0 = dist (f x0) (g y0) := by
    calc
      dist x0 y0 = dist (f x0) y0 := by
        simpa [IsFixedPoint] using congrArg (fun z : X => dist z y0) hx0.symm
      _ = dist (f x0) (g y0) := by
        simpa [IsFixedPoint] using congrArg (fun z : X => dist (f x0) z) hy0.symm
  calc
    dist x0 y0 = dist (f x0) (g y0) := hfixed_rewrite
    _ ≤ dist (f x0) (g x0) + dist (g x0) (g y0) := dist_triangle (f x0) (g x0) (g y0)
    _ ≤ ε + c' * dist x0 y0 := hsum

/-- Helper for Proposition 6.16: from `d ≤ ε + a*d` with `a < 1`, one gets
`d ≤ ε / (1 - a)`. -/
lemma helperForProposition_6_16_le_div_one_sub_of_le_add_mul
    (d ε a : ℝ) (ha1 : a < 1) (hd : d ≤ ε + a * d) :
    d ≤ ε / (1 - a) := by
  have hpos : 0 < 1 - a := sub_pos.mpr ha1
  have hmul : d * (1 - a) ≤ ε := by
    nlinarith [hd]
  exact (le_div_iff₀ hpos).2 hmul

/-- Helper for Proposition 6.16: combine the `c`- and `c'`-division bounds into
the denominator `1 - min c c'` by a case split on `c ≤ c'`. -/
lemma helperForProposition_6_16_min_case_finish
    (d ε c c' : ℝ)
    (h1 : d ≤ ε / (1 - c))
    (h2 : d ≤ ε / (1 - c')) :
    d ≤ ε / (1 - min c c') := by
  by_cases hcc : c ≤ c'
  · simpa [min_eq_left hcc] using h1
  · have hc'c : c' ≤ c := le_of_not_ge hcc
    simpa [min_eq_right hc'c] using h2

/-- Proposition 6.16: Let `(X,d)` be a complete metric space, and let `f,g : X → X`
be strict contractions with contraction constants `c,c' ∈ (0,1)`, respectively.
If `x₀` and `y₀` are fixed points of `f` and `g`, and there exists `ε > 0` such that
`dist (f x) (g x) ≤ ε` for all `x`, then
`dist x₀ y₀ ≤ ε / (1 - min c c')`. -/
theorem fixed_point_distance_le_of_uniformly_close_strict_contractions
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (f g : X → X) (c c' : ℝ) (x0 y0 : X) (ε : ℝ)
    (hf : IsContractionConstant f c)
    (hg : IsContractionConstant g c')
    (hx0 : IsFixedPoint f x0)
    (hy0 : IsFixedPoint g y0)
    (hε : 0 < ε)
    (hclose : ∀ x : X, dist (f x) (g x) ≤ ε) :
    dist x0 y0 ≤ ε / (1 - min c c') := by
  have _ : 0 ≤ ε := le_of_lt hε
  have hdist_c :
      dist x0 y0 ≤ ε + c * dist x0 y0 :=
    helperForProposition_6_16_dist_le_eps_add_c_mul_dist f g c x0 y0 ε hf hx0 hy0 hclose
  have hdist_c' :
      dist x0 y0 ≤ ε + c' * dist x0 y0 :=
    helperForProposition_6_16_dist_le_eps_add_cprime_mul_dist f g c' x0 y0 ε hg hx0 hy0 hclose
  have hdiv_c :
      dist x0 y0 ≤ ε / (1 - c) :=
    helperForProposition_6_16_le_div_one_sub_of_le_add_mul
      (dist x0 y0) ε c hf.2.1 hdist_c
  have hdiv_c' :
      dist x0 y0 ≤ ε / (1 - c') :=
    helperForProposition_6_16_le_div_one_sub_of_le_add_mul
      (dist x0 y0) ε c' hg.2.1 hdist_c'
  exact helperForProposition_6_16_min_case_finish (dist x0 y0) ε c c' hdiv_c hdiv_c'

/-- Helper for Theorem 6.6: turn the real-valued contraction hypothesis into
`ContractingWith` with an `NNReal` constant. -/
lemma helperForTheorem_6_6_contractingWith_of_real_constant
    {X : Type*} [MetricSpace X] (f : X → X)
    (hcontract : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y) :
    ∃ K : NNReal, ContractingWith K f := by
  rcases hcontract with ⟨c, hc0, hc1, hdist⟩
  let K : NNReal := ⟨c, le_of_lt hc0⟩
  refine ⟨K, ?_⟩
  refine ⟨?_, ?_⟩
  · change c < 1
    simpa [K] using hc1
  · refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [K] using hdist x y

/-- Helper for Theorem 6.6: the local fixed-point predicate agrees with mathlib's
`IsFixedPt`. -/
lemma helperForTheorem_6_6_isFixedPoint_iff_isFixedPt
    {X : Type*} (f : X → X) (x : X) :
    IsFixedPoint f x ↔ Function.IsFixedPt f x := by
  rfl

/-- Helper for Theorem 6.6: uniqueness stated using
`ContractingWith.fixedPoint`. -/
lemma helperForTheorem_6_6_unique_at_mathlib_fixedPoint
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {f : X → X} {K : NNReal} (hfK : ContractingWith K f) :
    ∀ y : X, IsFixedPoint f y → y = ContractingWith.fixedPoint f hfK := by
  intro y hy
  apply hfK.fixedPoint_unique
  exact (helperForTheorem_6_6_isFixedPoint_iff_isFixedPt f y).1 hy

/-- Helper for Theorem 6.6: iterates `Nat.iterate f n x₀` converge to the
`ContractingWith.fixedPoint`. -/
lemma helperForTheorem_6_6_tendsto_nat_iterate_fixedPoint
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {f : X → X} {K : NNReal} (hfK : ContractingWith K f) :
    ∀ x0 : X,
      Filter.Tendsto (fun n : ℕ => Nat.iterate f n x0) Filter.atTop
        (nhds (ContractingWith.fixedPoint f hfK)) := by
  intro x0
  simpa using hfK.tendsto_iterate_fixedPoint x0

/-- Theorem 6.6 (Banach fixed-point theorem): If `X` is a nonempty complete metric
space and `f : X → X` is a contraction with constant `c` satisfying `0 < c < 1`, then
`f` has a unique fixed point `x*`; moreover, for every initial point `x₀`, the iterates
`x_{n+1} = f(x_n)` converge to `x*`. -/
theorem banach_fixed_point_theorem
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (f : X → X)
    (hcontract : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y) :
    ∃ xstar : X,
      IsFixedPoint f xstar ∧
        (∀ y : X, IsFixedPoint f y → y = xstar) ∧
          ∀ x0 : X,
            Filter.Tendsto (fun n : ℕ => Nat.iterate f n x0) Filter.atTop (nhds xstar) := by
  rcases helperForTheorem_6_6_contractingWith_of_real_constant f hcontract with ⟨K, hfK⟩
  refine ⟨ContractingWith.fixedPoint f hfK, ?_⟩
  refine ⟨?_, ?_⟩
  · exact
      (helperForTheorem_6_6_isFixedPoint_iff_isFixedPt f (ContractingWith.fixedPoint f hfK)).2
        hfK.fixedPoint_isFixedPt
  · refine ⟨?_, ?_⟩
    · exact helperForTheorem_6_6_unique_at_mathlib_fixedPoint hfK
    · exact helperForTheorem_6_6_tendsto_nat_iterate_fixedPoint hfK

end Section06
end Chap06

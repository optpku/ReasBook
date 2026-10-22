/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part5

section Chap05
section Section23

/-- Corollary 23.4.1: If `f` is a finite convex function on `ℝⁿ`, then at every point `x` the
subdifferential `∂f(x)` is a nonempty bounded closed convex set, the directional derivative
function `y ↦ f'(x; y)` is finite, positively homogeneous, and convex, and for each direction `y`
the value `f'(x; y)` is attained as the maximum pairing `⟨x⋆, y⟩` over `x⋆ ∈ ∂f(x)`. -/
theorem finite_convex_subdifferential_nonempty_bounded_closed_convex_and_directionalDerivative_max
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f)
    (hfinite : ∀ z : Fin n → ℝ, f z ≠ (⊤ : EReal) ∧ f z ≠ (⊥ : EReal)) (x : Fin n → ℝ) :
    Set.Nonempty (subdifferentialAt f x) ∧
      Bornology.IsBounded ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ∧
      IsClosed ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ∧
      Convex ℝ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x) ∧
      PositivelyHomogeneous (upperDirectionalDerivativeAt f x) ∧
      (∀ y : Fin n → ℝ,
        upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) ∧
          upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal)) ∧
      ∀ y : Fin n → ℝ,
        ∃ xStar ∈ subdifferentialAt f x,
          upperDirectionalDerivativeAt f x y = ((xStar y : ℝ) : EReal) ∧
            ∀ zStar ∈ subdifferentialAt f x, zStar y ≤ xStar y := by
  let C : Set (Fin n → ℝ) := ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)
  have hconvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [ConvexFunction] using hf
  have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    refine ⟨(f x).toReal, ?_⟩
    exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := x) (μ := (f x).toReal)
      (by simp) (by rw [EReal.coe_toReal (hfinite x).1 (hfinite x).2])
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    refine (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
      (S := (Set.univ : Set (Fin n → ℝ))) (f := f)).2 ?_
    refine ⟨hconvOn, ⟨x, hxDom⟩, ?_⟩
    intro z hz
    exact ⟨(hfinite z).2, (hfinite z).1⟩
  have hdom_univ : effectiveDomain (Set.univ : Set (Fin n → ℝ)) f = Set.univ := by
    ext z
    constructor
    · intro hz
      simp
    · intro hz
      refine ⟨(f z).toReal, ?_⟩
      exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := z) (μ := (f z).toReal)
        (by simp) (by rw [EReal.coe_toReal (hfinite z).1 (hfinite z).2])
  have hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [hdom_univ]
  have h23_4 :=
    subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
      f hproper x
  have hsub_bdd :
      Set.Nonempty (subdifferentialAt f x) ∧ Bornology.IsBounded C := by
    simpa [C] using (h23_4.2.2.1).2 hxInt
  have hsub : Set.Nonempty (subdifferentialAt f x) := hsub_bdd.1
  have hCbd : Bornology.IsBounded C := hsub_bdd.2
  have hxri :
      x ∈ euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    helperForTheorem_23_4_mem_relativeInterior_of_mem_interior (n := n)
      (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hxInt
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := hfinite x
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hxFinite with
    ⟨_hmono, hpos, _hconvD, _hzero, _hsymm⟩
  have h23_2 :=
    subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      f hf x hxFinite (0 : Module.Dual ℝ (Fin n → ℝ))
  have hCclosed : IsClosed C := by
    simpa [C] using h23_2.2.1
  have hCconv : Convex ℝ C := by
    simpa [C] using h23_2.2.2.1
  have hDirProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x) :=
    (h23_4.2.1 hxri).2.1
  have hDirFinite :
      ∀ y : Fin n → ℝ,
        upperDirectionalDerivativeAt f x y ≠ (⊤ : EReal) ∧
          upperDirectionalDerivativeAt f x y ≠ (⊥ : EReal) :=
    h23_4.2.2.2 hxInt
  have hDirEq :
      ∀ y : Fin n → ℝ,
        upperDirectionalDerivativeAt f x y = subdifferentialSupportAt f x y :=
    (h23_4.2.1 hxri).2.2.2
  have hsupportEq :
      ∀ y : Fin n → ℝ, upperDirectionalDerivativeAt f x y = supportFunctionEReal C y := by
    intro y
    calc
      upperDirectionalDerivativeAt f x y = subdifferentialSupportAt f x y := hDirEq y
      _ = supportFunctionEReal C y := by
        symm
        exact helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x y
  have hCnonempty : C.Nonempty := by
    rcases hsub with ⟨g, hg⟩
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm g, ?_⟩
    simpa [C] using hg
  have hCcompact : IsCompact C := (Metric.isCompact_iff_isClosed_bounded).2 ⟨hCclosed, hCbd⟩
  refine ⟨hsub, hCbd, hCclosed, hCconv, hDirProper, hpos, hDirFinite, ?_⟩
  intro y
  have hcont :
      ContinuousOn (fun z : Fin n → ℝ => dotProduct z y) C := by
    have hcont' : Continuous (fun z : Fin n → ℝ => dotProduct z y) := by
      simpa using
        (continuous_id.dotProduct (continuous_const : Continuous fun _ : Fin n → ℝ => y))
    exact hcont'.continuousOn
  obtain ⟨v0, hv0C, hv0max⟩ := hCcompact.exists_isMaxOn hCnonempty hcont
  have hsupp_v0_eq : supportFunctionEReal C y = ((dotProduct v0 y : ℝ) : EReal) := by
    apply le_antisymm
    · exact
        (section13_supportFunctionEReal_le_coe_iff C y (dotProduct v0 y)).2
          (fun z hz => (isMaxOn_iff.mp hv0max) z hz)
    · exact le_sSup ⟨v0, hv0C, rfl⟩
  refine ⟨dotProductEquiv ℝ (Fin n) v0, ?_, ?_, ?_⟩
  · simpa [C] using hv0C
  · calc
      upperDirectionalDerivativeAt f x y = supportFunctionEReal C y := hsupportEq y
      _ = ((dotProduct v0 y : ℝ) : EReal) := hsupp_v0_eq
      _ = (((dotProductEquiv ℝ (Fin n) v0) y : ℝ) : EReal) := by simp [dotProduct_comm]
  · intro zStar hzStar
    have hzC : (dotProductEquiv ℝ (Fin n)).symm zStar ∈ C := by
      simpa [C] using hzStar
    have hzEval :
        ((dotProductEquiv ℝ (Fin n)) ((dotProductEquiv ℝ (Fin n)).symm zStar)) y = zStar y :=
      congrArg (fun g : Module.Dual ℝ (Fin n → ℝ) => g y)
        ((dotProductEquiv ℝ (Fin n)).apply_symm_apply zStar)
    have hzDot :
        zStar y = dotProduct ((dotProductEquiv ℝ (Fin n)).symm zStar) y := by
      change zStar y = ((dotProductEquiv ℝ (Fin n)) ((dotProductEquiv ℝ (Fin n)).symm zStar)) y
      symm
      exact congrArg (fun g : Module.Dual ℝ (Fin n → ℝ) => g y)
        ((dotProductEquiv ℝ (Fin n)).apply_symm_apply zStar)
    have hmaxEval :
        dotProduct ((dotProductEquiv ℝ (Fin n)).symm zStar) y ≤ dotProduct v0 y := by
      simpa [dotProduct_comm] using
        (isMaxOn_iff.mp hv0max) ((dotProductEquiv ℝ (Fin n)).symm zStar) hzC
    calc
      zStar y = dotProduct ((dotProductEquiv ℝ (Fin n)).symm zStar) y := hzDot
      _ ≤ dotProduct v0 y := hmaxEval
      _ = ((dotProductEquiv ℝ (Fin n)) v0) y := by simp [dotProduct_comm]

/-- Helper for Theorem 23.6: identify the vectorized approximate subdifferential with the
Fenchel-conjugate sublevel set from Proposition 23.6.1. -/
lemma helperForTheorem_23_6_approximateSubdifferential_preimage_eq_conjugateSublevel
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : NNReal) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' approximateSubdifferentialAt f x ε) =
      {v : Fin n → ℝ | fenchelConjugate n (translatedDifferenceFunctionAt f x) v ≤
        ((ε : ℝ) : EReal)} := by
  rcases
      approximateSubdifferential_iff_translatedDifferenceConjugate_le_and_basic_properties
        (f := f) hf x hx with
    ⟨_htrans, happ, _hclosed, _hconv, _hmono, _hInter⟩
  -- Read the approximate subdifferential membership criterion pointwise and extensionalize it.
  ext v
  exact happ ε v

/-- Helper for Theorem 23.6: rewrite the approximate-support value as the support function of the
corresponding Fenchel-conjugate sublevel set. -/
lemma helperForTheorem_23_6_approximateSupport_eq_supportFunction_conjugateSublevel
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x y : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : NNReal) :
    approximateSubdifferentialSupportAt f x ε y =
      supportFunctionEReal
        {v : Fin n → ℝ | fenchelConjugate n (translatedDifferenceFunctionAt f x) v ≤
          ((ε : ℝ) : EReal)} y := by
  -- Unfold the support value and replace the set by the conjugate-sublevel description.
  rw [approximateSubdifferentialSupportAt,
    helperForTheorem_23_6_approximateSubdifferential_preimage_eq_conjugateSublevel
      (f := f) hf x hx ε]

/-- Helper for Theorem 23.6: shifting the closed translated-difference function by a real
constant subtracts that constant from its Fenchel conjugate. -/
lemma helperForTheorem_23_6_shiftedTranslatedClosure_fenchelConjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (ε : ℝ) :
    fenchelConjugate n
        (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal)) =
      fun v =>
        fenchelConjugate n (translatedDifferenceFunctionAt f x) v - ((ε : ℝ) : EReal) := by
  -- Rewrite the conjugate of the shifted closure using the add-constant rule.
  rw [section16_fenchelConjugate_add_const]
  -- The Fenchel conjugate is unchanged by passing to the convex closure.
  simp [fenchelConjugate_eq_of_convexFunctionClosure]

/-- Helper for Theorem 23.6: the translated-difference function vanishes at the origin whenever
`f x` is finite. -/
lemma helperForTheorem_23_6_translatedDifference_zero
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    translatedDifferenceFunctionAt f x 0 = 0 := by
  -- Evaluate the translated difference at the zero direction and cancel the finite value `f x`.
  simp [translatedDifferenceFunctionAt, EReal.sub_self hx.1 hx.2]

/-- Helper for Theorem 23.6: properness of `f` rules out the value `⊥` for every translated
difference. -/
lemma helperForTheorem_23_6_translatedDifference_ne_bot
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (z : Fin n → ℝ) :
    translatedDifferenceFunctionAt f x z ≠ (⊥ : EReal) := by
  -- Properness gives `f (x + z) ≠ ⊥`, and subtracting the finite value `f x` preserves that.
  have hxz : f (x + z) ≠ (⊥ : EReal) :=
    hproper.2.2 (x + z) (by simp)
  simp [translatedDifferenceFunctionAt, sub_eq_add_neg, hxz, hx.1]

/-- Helper for Theorem 23.6: the translated-difference function inherits proper convexity from
`f` by combining input translation with subtraction of the finite value `f x`. -/
lemma helperForTheorem_23_6_translatedDifference_properConvex
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (translatedDifferenceFunctionAt f x) := by
  let β : ℝ := (f x).toReal
  have hβ : ((β : ℝ) : EReal) = f x := by
    -- Finiteness at `x` lets us replace the `EReal` value by a real constant.
    simp [β, EReal.coe_toReal, hx.1, hx.2]
  have htranslate :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun z => f (z - (-x))) :=
    properConvexFunctionOn_translate (n := n) (a := -x) hproper
  have hconst :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun _ : Fin n → ℝ => (((-β : ℝ)) : EReal)) :=
    properConvexFunctionOn_const (n := n) (-β)
  have hrepr :
      translatedDifferenceFunctionAt f x =
        fun z => f (z - (-x)) + (((-β : ℝ)) : EReal) := by
    -- Rewrite the translated difference as a translate of `f` plus a finite constant.
    funext z
    simp [translatedDifferenceFunctionAt, hβ, sub_eq_add_neg, add_comm]
  refine ⟨?_, ?_, ?_⟩
  · -- Convexity is stable under addition of the finite constant function.
    rw [hrepr]
    exact convexFunctionOn_add_of_proper (n := n) htranslate hconst
  · -- The origin remains a finite epigraph point after the normalization by `f x`.
    refine ⟨(0, 0), ?_⟩
    constructor
    · exact Set.mem_univ 0
    · simp [helperForTheorem_23_6_translatedDifference_zero (f := f) x hx]
  · -- The finite constant shift cannot create a `⊥` value.
    intro z _
    exact helperForTheorem_23_6_translatedDifference_ne_bot (f := f) hproper x hx z

/-- Helper for Theorem 23.6: if `f` is closed, then the translated-difference function is also
closed. -/
lemma helperForTheorem_23_6_translatedDifference_closed
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ClosedConvexFunction (translatedDifferenceFunctionAt f x) := by
  let g : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt f x
  let β : ℝ := (f x).toReal
  have hβ : ((β : ℝ) : EReal) = f x := by
    simp [β, EReal.coe_toReal, hx.1, hx.2]
  have hg_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    helperForTheorem_23_6_translatedDifference_properConvex (f := f) hproper x hx
  have hg_lsc : LowerSemicontinuous g := by
    rw [lowerSemicontinuous_iff_closed_sublevel]
    intro α
    have hsub :
        {z : Fin n → ℝ | g z ≤ (α : EReal)} =
          (fun z : Fin n → ℝ => z + x) ⁻¹'
            {z : Fin n → ℝ | f z ≤ (((α + β : ℝ)) : EReal)} := by
      ext z
      constructor
      · intro hz
        have hz' :
            f (z + x) - ((β : ℝ) : EReal) ≤ (α : EReal) := by
          simpa [g, translatedDifferenceFunctionAt, hβ, add_comm, add_left_comm, add_assoc] using
            hz
        have hz'' :
            f (z + x) ≤ (α : EReal) + ((β : ℝ) : EReal) :=
          (EReal.sub_le_iff_le_add (Or.inl (by simp)) (Or.inl (by simp))).1 hz'
        simpa [Set.mem_preimage, add_comm, add_left_comm, add_assoc] using hz''
      · intro hz
        have hz' :
            f (z + x) ≤ (α : EReal) + ((β : ℝ) : EReal) := by
          simpa [Set.mem_preimage, add_comm, add_left_comm, add_assoc] using hz
        have hz'' :
            f (z + x) - ((β : ℝ) : EReal) ≤ (α : EReal) :=
          (EReal.sub_le_iff_le_add (Or.inl (by simp)) (Or.inl (by simp))).2 hz'
        simpa [g, translatedDifferenceFunctionAt, hβ, add_comm, add_left_comm, add_assoc] using
          hz''
    rw [hsub]
    have hclosed_sub :
        IsClosed {z : Fin n → ℝ | f z ≤ (((α + β : ℝ)) : EReal)} :=
      (lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hclosed.2 (α + β)
    exact hclosed_sub.preimage (continuous_id.add continuous_const)
  exact ⟨hg_proper.1, hg_lsc⟩

/-- Helper for Theorem 23.6: the shifted closed translated-difference function is the proper
closed convex input needed for the dual half of Theorem 13.5. -/
lemma helperForTheorem_23_6_shiftedTranslatedClosure_closedProper
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : ℝ) (hε : 0 < ε) :
    ClosedConvexFunction
        (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal)) := by
  let g : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt f x
  let gε : (Fin n → ℝ) → EReal := fun z => convexFunctionClosure g z + ((ε : ℝ) : EReal)
  have _hε : 0 < ε := hε
  have hgProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    helperForTheorem_23_6_translatedDifference_properConvex (f := f) hproper x hx
  have hclosure :
      ClosedConvexFunction (convexFunctionClosure g) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure g) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := g) hgProper).1
  have hconst :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun _ : Fin n → ℝ => ((ε : ℝ) : EReal)) :=
    properConvexFunctionOn_const (n := n) ε
  -- Route correction: the remaining gap is not mere closure transport.
  -- The local transport facts below are enough to reduce the blocker to the missing
  -- dependency-closed bridge identified by Agent C: a nonpositive-origin analogue of
  -- Theorem 9.7 for the positively homogeneous hull.
  have hgε_closed : ClosedConvexFunction gε := by
    refine ⟨?_, ?_⟩
    · -- Convexity survives the addition of the constant real function.
      change ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gε
      simpa [gε] using convexFunctionOn_add_of_proper (n := n) hclosure.2 hconst
    · -- Closed sublevel sets shift by the same real constant.
      rw [lowerSemicontinuous_iff_closed_sublevel]
      intro α
      have hsub :
          {z : Fin n → ℝ | gε z ≤ (α : EReal)} =
            {z : Fin n → ℝ | convexFunctionClosure g z ≤ (((α - ε : ℝ)) : EReal)} := by
        ext z
        simpa [gε, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (EReal.le_sub_iff_add_le (a := convexFunctionClosure g z)
            (b := ((ε : ℝ) : EReal)) (c := (α : EReal))
            (Or.inr (by simp)) (Or.inr (by simp))).symm
      rw [hsub]
      exact
        (lowerSemicontinuous_iff_closed_sublevel (f := convexFunctionClosure g)).1
          hclosure.1.2 (α - ε)
  have hgε_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gε := by
    refine ⟨?_, ?_, ?_⟩
    · -- The same sum-of-proper-convex-functions argument gives convexity.
      change ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gε
      simpa [gε] using convexFunctionOn_add_of_proper (n := n) hclosure.2 hconst
    · -- Any epigraph witness for `convexFunctionClosure g` shifts vertically by `ε`.
      rcases hclosure.2.2.1 with ⟨⟨z, μ⟩, hzμ⟩
      refine ⟨(z, μ + ε), ?_⟩
      constructor
      · exact Set.mem_univ z
      · have hzμ' : convexFunctionClosure g z ≤ (μ : EReal) := hzμ.2
        have hshift := add_le_add_left hzμ' (((ε : ℝ) : EReal))
        simpa [gε, add_comm, add_left_comm, add_assoc] using hshift
    · -- Adding a finite constant does not create a `⊥` value.
      intro z _
      have hz : convexFunctionClosure g z ≠ (⊥ : EReal) := hclosure.2.2.2 z (by simp)
      let a : EReal := convexFunctionClosure g z
      cases hval : a <;> simp [gε, a, hval] at hz ⊢
  exact ⟨hgε_closed, hgε_proper⟩

/-- Helper for Theorem 23.6: the shifted closed translated-difference function is bounded above
by `ε` at the origin, because the original translated difference vanishes there and convex closure
can only decrease values. -/
lemma helperForTheorem_23_6_shiftedTranslatedClosure_value_at_zero_le
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : ℝ) :
    (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal))
        0 ≤ ((ε : ℝ) : EReal) := by
  -- Start from the universal bound `cl g ≤ g` and specialize it at the origin.
  have hclosure_le :
      convexFunctionClosure (translatedDifferenceFunctionAt f x) 0 ≤ (0 : EReal) := by
    simpa [helperForTheorem_23_6_translatedDifference_zero (f := f) x hx] using
      (convexFunctionClosure_le_self (f := translatedDifferenceFunctionAt f x)) 0
  -- Adding the same real constant preserves the order and gives the desired endpoint bound.
  simpa [add_comm, zero_add] using add_le_add_right hclosure_le (((ε : ℝ) : EReal))

/-- Helper for Theorem 23.6: for every positive `ε`, the origin stays in the effective domain of
the shifted closed translated-difference function. -/
lemma helperForTheorem_23_6_shiftedTranslatedClosure_zero_mem_effectiveDomain
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (ε : ℝ) (hε : 0 < ε) :
    (0 : Fin n → ℝ) ∈
      effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal)) := by
  let gε : (Fin n → ℝ) → EReal :=
    fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal)
  have hgε_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gε :=
    (helperForTheorem_23_6_shiftedTranslatedClosure_closedProper
      (f := f) hproper x hx ε hε).2
  have hgε_le :
      gε 0 ≤ ((ε : ℝ) : EReal) := by
    -- Reuse the origin estimate in the normalized `gε` notation.
    simpa [gε] using
      helperForTheorem_23_6_shiftedTranslatedClosure_value_at_zero_le (f := f) x hx ε
  have hgε_ne_top : gε 0 ≠ (⊤ : EReal) := by
    -- Any value bounded above by the real number `ε` must avoid `⊤`.
    intro htop
    have : (⊤ : EReal) ≤ ((ε : ℝ) : EReal) := by
      rw [htop] at hgε_le
      exact hgε_le
    exact EReal.coe_ne_top ε (top_le_iff.mp this)
  -- Membership in the effective domain on `univ` is exactly finiteness from above.
  rw [effectiveDomain_eq]
  refine ⟨by simp, (lt_top_iff_ne_top).2 hgε_ne_top⟩

/-- Helper for Theorem 23.6: for positive `ε`, the approximate-support value is the closed
positively homogeneous hull of the shifted translated-difference closure. -/
lemma helperForTheorem_23_6_support_eq_clConv_posHom_shiftedTranslatedClosure
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : ℝ) (hε : 0 < ε) :
    approximateSubdifferentialSupportAt f x ε.toNNReal y =
      clConv n
        (positivelyHomogeneousConvexFunctionGenerated
          (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal))) y := by
  let gε : (Fin n → ℝ) → EReal :=
    fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal)
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hsupport0 :
      approximateSubdifferentialSupportAt f x ε.toNNReal y =
        supportFunctionEReal
          {v : Fin n → ℝ | fenchelConjugate n (translatedDifferenceFunctionAt f x) v ≤
            (((ε.toNNReal : NNReal) : ℝ) : EReal)} y :=
    helperForTheorem_23_6_approximateSupport_eq_supportFunction_conjugateSublevel
      (f := f) hf x y hx ε.toNNReal
  have hsupport :
      approximateSubdifferentialSupportAt f x ε.toNNReal y =
        supportFunctionEReal
          {v : Fin n → ℝ | fenchelConjugate n (translatedDifferenceFunctionAt f x) v ≤
            ((ε : ℝ) : EReal)} y := by
    simpa [Real.toNNReal_of_nonneg (le_of_lt hε)] using hsupport0
  have hset :
      {v : Fin n → ℝ | fenchelConjugate n (translatedDifferenceFunctionAt f x) v ≤
          ((ε : ℝ) : EReal)} =
        {v : Fin n → ℝ | fenchelConjugate n gε v ≤ (0 : EReal)} := by
    -- Replace the `≤ ε` sublevel set by the `≤ 0` sublevel set of the shifted closure.
    ext v
    simp [gε, helperForTheorem_23_6_shiftedTranslatedClosure_fenchelConjugate, EReal.sub_nonpos]
  have hgε :
      ClosedConvexFunction gε ∧ ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gε :=
    helperForTheorem_23_6_shiftedTranslatedClosure_closedProper
      (f := f) hproper x hx ε hε
  have hdual :
      clConv n (positivelyHomogeneousConvexFunctionGenerated gε) =
        supportFunctionEReal {xStar : Fin n → ℝ | fenchelConjugate n gε xStar ≤ (0 : EReal)} :=
    (supportFunctionEReal_setOf_le_zero_eq_clConv_posHomGenerated_fenchelConjugate_and_dual
      (n := n) (f := gε) hgε.1 hgε.2).2
  -- Route correction: isolate the Fenchel-sublevel rewrite before any right-scalar-multiple work.
  calc
    approximateSubdifferentialSupportAt f x ε.toNNReal y =
        supportFunctionEReal
          {xStar : Fin n → ℝ | fenchelConjugate n gε xStar ≤ (0 : EReal)} y := by
            rw [hsupport, hset]
    _ = clConv n (positivelyHomogeneousConvexFunctionGenerated gε) y := by
            simpa using congrArg (fun h => h y) hdual.symm
    _ =
        clConv n
          (positivelyHomogeneousConvexFunctionGenerated
            (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z +
              ((ε : ℝ) : EReal))) y := by
            rfl

/-- Helper for Theorem 23.6: the recession cone of the shifted translated-closure epigraph is
the epigraph of its recession function. -/
lemma helperForTheorem_23_6_shiftedTranslatedClosure_recession_eq_recessionFunction
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : ℝ) (hε : 0 < ε) :
    Set.recessionCone
        (epigraph (Set.univ : Set (Fin n → ℝ))
          (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z +
            ((ε : ℝ) : EReal))) =
      epigraph (Set.univ : Set (Fin n → ℝ))
        (recessionFunction
          (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z +
            ((ε : ℝ) : EReal))) := by
  let gε : (Fin n → ℝ) → EReal :=
    fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal)
  have hgε :
      ClosedConvexFunction gε ∧ ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gε :=
    helperForTheorem_23_6_shiftedTranslatedClosure_closedProper
      (f := f) hproper x hx ε hε
  let g : Fin 1 → (Fin n → ℝ) → EReal := fun _ => gε
  have hconv_epi :
      ∀ i : Fin 1, Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) (g i)) := by
    intro i
    -- The epigraph of each copy of `gε` is convex because `gε` is proper convex.
    simpa [g, ConvexFunction] using
      (convex_epigraph_of_convexFunctionOn (f := gε) hgε.2.1)
  have hproper_family :
      ∀ i : Fin 1, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g i) := by
    intro i
    -- The one-point family inherits properness from `gε`.
    simpa [g] using hgε.2
  have hk :
      ∀ (i : Fin 1) (y : Fin n → ℝ),
        recessionFunction gε y =
          sSup {r : EReal | ∃ z : Fin n → ℝ, r = g i (z + y) - g i z} := by
    intro i y
    -- Route correction: use the unrestricted recession-function formula directly, so the only
    -- remaining global blocker is the Chapter 9 bridge that removes the recession branch.
    simpa [g] using (section16_recessionFunction_eq_sSup_unrestricted (f := gε) y)
  -- Apply the general epigraph recession theorem to the constant one-element family.
  simpa [g, gε] using
    (recessionCone_epigraph_eq_epigraph_k
      (f := g) (k := recessionFunction gε) hconv_epi hproper_family hk (i := 0))

/-- Helper for Theorem 23.6: once the shifted translated-closure input comes with a recession
description and a strictly positive value at the origin, Theorem 9.7 rewrites the approximate
support value as the infimum of the corresponding right-scalar multiples together with the
recession branch. -/
lemma helperForTheorem_23_6_approximateSupport_eq_infimum_rightScalarMultiple_of_origin_pos
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : ℝ) (hε : 0 < ε)
    (g0_plus : (Fin n → ℝ) → EReal)
    (hrec :
      Set.recessionCone
          (epigraph (Set.univ : Set (Fin n → ℝ))
            (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z +
              ((ε : ℝ) : EReal))) =
        epigraph (Set.univ : Set (Fin n → ℝ)) g0_plus)
    (hOriginPos :
      (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z +
        ((ε : ℝ) : EReal)) 0 > (0 : EReal)) :
    approximateSubdifferentialSupportAt f x ε.toNNReal y =
      sInf
        (Set.insert (g0_plus y)
          {z : EReal | ∃ lam : ℝ, 0 < lam ∧
            z =
              rightScalarMultiple
                (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z +
                  ((ε : ℝ) : EReal))
                lam y}) := by
  let gε : (Fin n → ℝ) → EReal :=
    fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal)
  have hgε :
      ClosedConvexFunction gε ∧ ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gε :=
    helperForTheorem_23_6_shiftedTranslatedClosure_closedProper
      (f := f) hproper x hx ε hε
  have hk :=
    closure_posHomogeneousGenerated_infimum_rightScalarMultiple
      (n := n) (f := gε) (f0_plus := g0_plus) hgε.1 hgε.2 hOriginPos (by simpa [gε] using hrec)
  let k : (Fin n → ℝ) → EReal := positivelyHomogeneousConvexFunctionGenerated gε
  have hkConv : ConvexFunction k := by
    -- The generated positively homogeneous hull is convex because Theorem 9.7 gives it as proper.
    simpa [ConvexFunction, k] using hk.1.1
  have hkClConv :
      clConv n k = convexFunctionClosure k := by
    -- Route correction: isolate the `clConv = convexFunctionClosure` conversion before rewriting
    -- with the Chapter 9 infimum formula, so the remaining blocker is only the recession input.
    calc
      clConv n k = fenchelConjugate n (fenchelConjugate n k) := by
        symm
        simpa [k] using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := k))
      _ = convexFunctionClosure k := by
        simpa [k] using
          (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
            (n := n) (f := k) hkConv)
  -- First rewrite the approximate support as the closed positively homogeneous hull, then
  -- replace that hull by the Chapter 9 right-scalar-multiple infimum formula.
  calc
    approximateSubdifferentialSupportAt f x ε.toNNReal y = clConv n k y := by
      simpa [gε, k] using
        helperForTheorem_23_6_support_eq_clConv_posHom_shiftedTranslatedClosure
          (f := f) hproper x y hx ε hε
    _ = convexFunctionClosure k y := by
      simpa using congrArg (fun h : (Fin n → ℝ) → EReal => h y) hkClConv
    _ =
        sInf
          (Set.insert (g0_plus y)
            {z : EReal | ∃ lam : ℝ, 0 < lam ∧ z = rightScalarMultiple gε lam y}) := by
      simpa [gε, k] using hk.2.1 y

/-- Helper for Theorem 23.6: when the shifted translated-closure is positive at the origin, the
approximate-support value is the Chapter 9 infimum formula with the recession branch specialized
to the recession function of that shifted input. -/
lemma helperForTheorem_23_6_approximateSupport_eq_infimum_rightScalarMultiple_recessionFunction_of_origin_pos
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : ℝ) (hε : 0 < ε)
    (hOriginPos :
      (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z +
        ((ε : ℝ) : EReal)) 0 > (0 : EReal)) :
    approximateSubdifferentialSupportAt f x ε.toNNReal y =
      sInf
        (Set.insert
          (recessionFunction
            (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z +
              ((ε : ℝ) : EReal)) y)
          {z : EReal | ∃ lam : ℝ, 0 < lam ∧
            z =
              rightScalarMultiple
                (fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z +
                  ((ε : ℝ) : EReal))
                lam y}) := by
  let gε : (Fin n → ℝ) → EReal :=
    fun z => convexFunctionClosure (translatedDifferenceFunctionAt f x) z + ((ε : ℝ) : EReal)
  have hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) gε) =
        epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction gε) :=
    helperForTheorem_23_6_shiftedTranslatedClosure_recession_eq_recessionFunction
      (f := f) hproper x hx ε hε
  -- Specialize the previously proved Chapter 9 reduction to the concrete recession function.
  simpa [gε] using
    (helperForTheorem_23_6_approximateSupport_eq_infimum_rightScalarMultiple_of_origin_pos
      (f := f) hproper x y hx ε hε (g0_plus := recessionFunction gε) hrec hOriginPos)

/-- Helper for Theorem 23.6: if `f` is closed, then the approximate-support value is exactly the
positive-scaling infimum from the textbook proof. -/
lemma helperForTheorem_23_6_approximateSupport_eq_infimum_rightScalarMultiple_of_closed
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : ℝ) (hε : 0 < ε) :
    approximateSubdifferentialSupportAt f x ε.toNNReal y =
      sInf
        {z : EReal | ∃ lam : ℝ, 0 < lam ∧
          z =
            rightScalarMultiple
              (fun z => translatedDifferenceFunctionAt f x z + ((ε : ℝ) : EReal))
              lam y} := by
  let g : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt f x
  let gε : (Fin n → ℝ) → EReal := fun z => g z + ((ε : ℝ) : EReal)
  have hclg : convexFunctionClosure g = g := by
    exact
      convexFunctionClosure_eq_of_closedConvexFunction
        (f := g)
        (helperForTheorem_23_6_translatedDifference_closed
          (f := f) hclosed hproper x hx)
        (fun z => helperForTheorem_23_6_translatedDifference_ne_bot
          (f := f) hproper x hx z)
  have hgε :
      ClosedConvexFunction gε ∧ ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gε := by
    simpa [g, gε, hclg] using
      (helperForTheorem_23_6_shiftedTranslatedClosure_closedProper
        (f := f) hproper x hx ε hε)
  have hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) gε) =
        epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction gε) := by
    simpa [g, gε, hclg] using
      (helperForTheorem_23_6_shiftedTranslatedClosure_recession_eq_recessionFunction
        (f := f) hproper x hx ε hε)
  have hdom0 :
      (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) gε := by
    simpa [g, gε, hclg] using
      (helperForTheorem_23_6_shiftedTranslatedClosure_zero_mem_effectiveDomain
        (f := f) hproper x hx ε hε)
  have hOriginPos : gε 0 > (0 : EReal) := by
    simp [gε, g, helperForTheorem_23_6_translatedDifference_zero (f := f) x hx, hε]
  let k : (Fin n → ℝ) → EReal := positivelyHomogeneousConvexFunctionGenerated gε
  have hk :=
    closure_posHomogeneousGenerated_infimum_rightScalarMultiple
      (n := n) (f := gε) (f0_plus := recessionFunction gε) hgε.1 hgε.2 hOriginPos hrec
  have hkclosed : ClosedConvexFunction k := (hk.2.2.2 hdom0).1
  have hkClConv : clConv n k = k :=
    clConv_eq_of_closedProperConvex (n := n) (f := k)
      (hf_closed := hkclosed.2) (hf_proper := hk.1)
  calc
    approximateSubdifferentialSupportAt f x ε.toNNReal y = clConv n k y := by
      simpa [g, gε, hclg, k] using
        (helperForTheorem_23_6_support_eq_clConv_posHom_shiftedTranslatedClosure
          (f := f) hproper x y hx ε hε)
    _ = k y := by
      simpa using congrArg (fun h : (Fin n → ℝ) → EReal => h y) hkClConv
    _ =
        sInf
          {z : EReal | ∃ lam : ℝ, 0 < lam ∧ z = rightScalarMultiple gε lam y} := by
      simpa [k, gε] using (hk.2.2.2 hdom0).2 y
    _ =
        sInf
          {z : EReal | ∃ lam : ℝ, 0 < lam ∧
            z =
              rightScalarMultiple
                (fun z => translatedDifferenceFunctionAt f x z + ((ε : ℝ) : EReal))
                lam y} := by
      rfl

/-- Helper for Theorem 23.6: in the closed case, every approximate-support value already
dominates the directional derivative itself. -/
lemma helperForTheorem_23_6_upperDirectionalDerivative_le_approximateSupport_of_closed
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : ℝ) (hε : 0 < ε) :
    upperDirectionalDerivativeAt f x y ≤
      approximateSubdifferentialSupportAt f x ε.toNNReal y := by
  let g : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt f x
  let gε : (Fin n → ℝ) → EReal := fun z => g z + ((ε : ℝ) : EReal)
  let S : Set EReal :=
    {z : EReal | ∃ lam : ℝ, 0 < lam ∧ z = rightScalarMultiple gε lam y}
  have happ :
      approximateSubdifferentialSupportAt f x ε.toNNReal y = sInf S := by
    simpa [S, g, gε] using
      (helperForTheorem_23_6_approximateSupport_eq_infimum_rightScalarMultiple_of_closed
        (f := f) hclosed hproper x y hx ε hε)
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨hdirData, _hpos, _hconv, _hzero, _hsymm⟩
  have hQbdd :
      BddBelow ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t) :=
    ⟨⊥, by intro z hz; simp⟩
  have hdirEq :
      upperDirectionalDerivativeAt f x y =
        sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t) :=
    helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x y (hdirData y).1
  have hS_nonempty : S.Nonempty := by
    refine ⟨rightScalarMultiple gε 1 y, ?_⟩
    exact ⟨1, by norm_num, rfl⟩
  have hgConv : ConvexFunction g := by
    simpa [g, ConvexFunction] using
      (helperForTheorem_23_6_translatedDifference_properConvex (f := f) hproper x hx).1
  have hgεConv : ConvexFunction gε := by
    have hclg : convexFunctionClosure g = g := by
      exact
        convexFunctionClosure_eq_of_closedConvexFunction
          (f := g)
          (helperForTheorem_23_6_translatedDifference_closed
            (f := f) hclosed hproper x hx)
          (fun z => helperForTheorem_23_6_translatedDifference_ne_bot
            (f := f) hproper x hx z)
    simpa [g, gε, hclg, ConvexFunction] using
      (helperForTheorem_23_6_shiftedTranslatedClosure_closedProper
        (f := f) hproper x hx ε hε).2.1
  have hupper_le_elem : ∀ z ∈ S, upperDirectionalDerivativeAt f x y ≤ z := by
    intro z hz
    rcases hz with ⟨lam, hLam, rfl⟩
    have hq_le :
        upperDirectionalDerivativeAt f x y ≤ directionalDifferenceQuotientAt f x y (lam⁻¹) := by
      rw [hdirEq]
      exact csInf_le hQbdd ⟨lam⁻¹, inv_pos.mpr hLam, rfl⟩
    have htE : (0 : EReal) ≤ (lam : EReal) := by
      exact_mod_cast le_of_lt hLam
    have hpoint : g (lam⁻¹ • y) ≤ gε (lam⁻¹ • y) := by
      simpa [gε] using
        (le_add_of_nonneg_right
          (show (0 : EReal) ≤ ((ε : ℝ) : EReal) by exact_mod_cast le_of_lt hε) :
            g (lam⁻¹ • y) ≤ g (lam⁻¹ • y) + ((ε : ℝ) : EReal))
    have hmul :
        ((lam : ℝ) : EReal) * g (lam⁻¹ • y) ≤
          ((lam : ℝ) : EReal) * gε (lam⁻¹ • y) :=
      mul_le_mul_of_nonneg_left hpoint htE
    have hq_to_right :
        directionalDifferenceQuotientAt f x y (lam⁻¹) ≤ rightScalarMultiple gε lam y := by
      calc
        directionalDifferenceQuotientAt f x y (lam⁻¹) =
            ((lam : ℝ) : EReal) * g (lam⁻¹ • y) := by
              change g (lam⁻¹ • y) / ((lam⁻¹ : ℝ) : EReal) =
                ((lam : ℝ) : EReal) * g (lam⁻¹ • y)
              rw [div_eq_mul_inv]
              have hInv : (((lam⁻¹ : ℝ) : EReal)⁻¹) = ((lam : ℝ) : EReal) := by
                calc
                  (((lam⁻¹ : ℝ) : EReal)⁻¹) = ((((lam⁻¹ : ℝ)⁻¹) : ℝ) : EReal) := by
                    simpa using (EReal.coe_inv (x := (lam⁻¹ : ℝ))).symm
                  _ = ((lam : ℝ) : EReal) := by simp
              rw [hInv]
              simp [mul_comm]
        _ ≤ ((lam : ℝ) : EReal) * gε (lam⁻¹ • y) := hmul
        _ = rightScalarMultiple gε lam y := by
              simpa [gε] using
                (rightScalarMultiple_pos_rewrite (f := gε) (hf := hgεConv) (hlam := hLam)
                  (x := y)).symm
    exact le_trans hq_le hq_to_right
  have hdir_le_sInf : upperDirectionalDerivativeAt f x y ≤ sInf S :=
    le_csInf hS_nonempty hupper_le_elem
  rw [happ]
  exact hdir_le_sInf

/-- Helper for Theorem 23.6: support functions are monotone under inclusion of the underlying
sets. -/
lemma helperForTheorem_23_6_supportFunctionEReal_mono_of_subset
    {n : ℕ} {A B : Set (Fin n → ℝ)} (hAB : A ⊆ B) (y : Fin n → ℝ) :
    supportFunctionEReal A y ≤ supportFunctionEReal B y := by
  -- Unfold both support functions and push each witness from `A` into `B`.
  unfold supportFunctionEReal
  refine sSup_le ?_
  rintro z ⟨x, hxA, rfl⟩
  exact le_sSup ⟨x, hAB hxA, rfl⟩

/-- Helper for Theorem 23.6: every approximate-support value dominates the closed directional
derivative because `∂f(x) = ∂₀ f(x) ⊆ ∂_ε f(x)`. -/
lemma helperForTheorem_23_6_closureDirectionalDerivative_le_approximateSupport
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) (ε : NNReal) :
    convexFunctionClosure (upperDirectionalDerivativeAt f x) y ≤
      approximateSubdifferentialSupportAt f x ε y := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  rcases
      approximateSubdifferential_iff_translatedDifferenceConjugate_le_and_basic_properties
        (f := f) hf x hx with
    ⟨_htrans, _happ, _hclosed, _hconv, hmono, _hInter⟩
  have hsubset :
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' approximateSubdifferentialAt f x ε) := by
    intro v hv
    have hvSub : dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f x := by
      simpa using hv
    have hvApprox0 :
        dotProductEquiv ℝ (Fin n) v ∈ approximateSubdifferentialAt f x 0 :=
      (helperForProposition_23_6_1_approximateSubdifferential_zero_eq_subdifferential
        (f := f) hf x hx v).2 hvSub
    have hvApproxε :
        dotProductEquiv ℝ (Fin n) v ∈ approximateSubdifferentialAt f x ε :=
      (hmono 0 ε (by simp)) hvApprox0
    -- Transport the monotone inclusion back through the Euclidean-dual equivalence.
    simpa using hvApproxε
  have hsupport :
      subdifferentialSupportAt f x y ≤ approximateSubdifferentialSupportAt f x ε y := by
    -- Compare the exact and approximate support functions on their vectorized dual sets.
    rw [← helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x y]
    unfold approximateSubdifferentialSupportAt
    exact helperForTheorem_23_6_supportFunctionEReal_mono_of_subset hsubset y
  have hclosure :
      convexFunctionClosure (upperDirectionalDerivativeAt f x) = subdifferentialSupportAt f x := by
    -- Theorem 23.2 identifies the closed directional derivative with the exact support value.
    simpa using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hf x hx (0 : Module.Dual ℝ (Fin n → ℝ))).2.2.2
  -- Replace the closed derivative by the exact support before enlarging to `∂_ε f(x)`.
  simpa [hclosure] using hsupport

/-- Helper for Theorem 23.6: any strict real lower bound below the closed directional derivative
already lies below every approximate-support value, so it automatically yields the eventual lower
neighborhood statement on `ε ↓ 0`. -/
lemma helperForTheorem_23_6_eventually_gt_of_real_lt_closureDirectionalDerivative
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) {μ : ℝ}
    (hμ : ((μ : ℝ) : EReal) < convexFunctionClosure (upperDirectionalDerivativeAt f x) y) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ((μ : ℝ) : EReal) < approximateSubdifferentialSupportAt f x ε.toNNReal y := by
  -- The closure-level lower bound from Theorem 23.2 already holds pointwise for every `ε`.
  refine Filter.Eventually.of_forall ?_
  intro ε
  exact lt_of_lt_of_le hμ
    (helperForTheorem_23_6_closureDirectionalDerivative_le_approximateSupport
      (f := f) hproper x y hx ε.toNNReal)

/-- Helper for Theorem 23.6: Fenchel's inequality gives the local one-sided upper bound
`δ^*(y | ∂_ε f(x)) ≤ ([f(x + ty) - f(x)] + ε) / t` for every `t > 0`. -/
lemma helperForTheorem_23_6_approximateSupport_le_regularizedDifferenceQuotient
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (ε : NNReal) {t : ℝ} (ht : 0 < t) :
    approximateSubdifferentialSupportAt f x ε y ≤
      (translatedDifferenceFunctionAt f x (t • y) + ((ε : ℝ) : EReal)) / (t : EReal) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hgProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (translatedDifferenceFunctionAt f x) :=
    helperForTheorem_23_6_translatedDifference_properConvex (f := f) hproper x hx
  have hsupport :
      approximateSubdifferentialSupportAt f x ε y =
        supportFunctionEReal
          {v : Fin n → ℝ | fenchelConjugate n (translatedDifferenceFunctionAt f x) v ≤
            ((ε : ℝ) : EReal)} y :=
    helperForTheorem_23_6_approximateSupport_eq_supportFunction_conjugateSublevel
      (f := f) hf x y hx ε
  have ht_nonneg_ereal : (0 : EReal) ≤ (t : EReal) := by
    exact_mod_cast le_of_lt ht
  have ht_ne_zero_ereal : (t : EReal) ≠ 0 := by
    exact_mod_cast ht.ne'
  -- Unfold the support function and bound each admissible dual vector with Fenchel's inequality.
  rw [hsupport]
  unfold supportFunctionEReal
  refine sSup_le ?_
  intro z hz
  rcases hz with ⟨v, hv, rfl⟩
  have hfenchel :
      ((dotProduct (t • y) v : ℝ) : EReal) ≤
        translatedDifferenceFunctionAt f x (t • y) +
          fenchelConjugate n (translatedDifferenceFunctionAt f x) v :=
    fenchel_inequality n (translatedDifferenceFunctionAt f x) hgProper (t • y) v
  have hsum :
      ((dotProduct (t • y) v : ℝ) : EReal) ≤
        translatedDifferenceFunctionAt f x (t • y) + ((ε : ℝ) : EReal) := by
    exact le_trans hfenchel
      (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hv (translatedDifferenceFunctionAt f x (t • y)))
  have hdiv :=
    (EReal.monotone_div_right_of_nonneg (b := (t : EReal)) ht_nonneg_ereal) hsum
  have hscale :
      (((dotProduct (t • y) v : ℝ) : EReal) / (t : EReal)) = ((dotProduct v y : ℝ) : EReal) := by
    have hdiv_eq :=
      (EReal.div_eq_iff (a := ((dotProduct v y : ℝ) : EReal)) (b := (t : EReal))
        (c := ((dotProduct (t • y) v : ℝ) : EReal)) (by simp) (by simp) ht_ne_zero_ereal)
    refine hdiv_eq.2 ?_
    simp [dotProduct_comm, mul_comm]
  -- Dividing by the positive step length gives the regularized difference-quotient bound.
  calc
    ((dotProduct v y : ℝ) : EReal) =
        (((dotProduct (t • y) v : ℝ) : EReal) / (t : EReal)) := hscale.symm
    _ ≤
        (translatedDifferenceFunctionAt f x (t • y) + ((ε : ℝ) : EReal)) / (t : EReal) := hdiv

/-- Helper for Theorem 23.6: every strict real upper bound on the directional derivative
eventually dominates the approximate-support values. -/
lemma helperForTheorem_23_6_eventually_lt_of_upperDirectionalDerivative_lt_real
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) {μ : ℝ}
    (hμ : upperDirectionalDerivativeAt f x y < ((μ : ℝ) : EReal)) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      approximateSubdifferentialSupportAt f x ε.toNNReal y < ((μ : ℝ) : EReal) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
  have hnebotWithin : (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))).NeBot := by
    have hclosure : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
      simp [closure_Ioi]
    exact (mem_closure_iff_nhdsWithin_neBot).1 hclosure
  have hqEventually :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        directionalDifferenceQuotientAt f x y t < ((μ : ℝ) : EReal) :=
    (tendsto_order.1 (hdir y).2.1).2 μ hμ
  have hposEventually :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), 0 < t := by
    simpa using
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
  rcases (hqEventually.and hposEventually).exists with ⟨t, hqtμ, ht⟩
  obtain ⟨β, hqtβ, hβμ⟩ := EReal.exists_between_coe_real hqtμ
  have hvalueβ :
      f (x + t • y) ≤ (((f x).toReal + t * β : ℝ) : EReal) :=
    helperForTheorem_23_1_valueBound_of_differenceQuotient_le_real
      (f := f) (x := x) (y := y) (t := t) hx ht (μ := β) (le_of_lt hqtβ)
  have hxtBot : f (x + t • y) ≠ (⊥ : EReal) :=
    hproper.2.2 (x + t • y) (by simp)
  have hxtTop : f (x + t • y) ≠ (⊤ : EReal) := by
    intro htop
    rw [htop] at hvalueβ
    exact (not_top_le_coe _ hvalueβ).elim
  have hvalueβReal : (f (x + t • y)).toReal ≤ (f x).toReal + t * β := by
    have hvalueβ' :
        (((f (x + t • y)).toReal : ℝ) : EReal) ≤
          (((f x).toReal + t * β : ℝ) : EReal) := by
      simpa [EReal.coe_toReal hxtTop hxtBot] using hvalueβ
    exact_mod_cast hvalueβ'
  have hβμReal : β < μ := by
    exact_mod_cast hβμ
  have hδ : 0 < t * (μ - β) := by
    exact mul_pos ht (sub_pos.mpr hβμReal)
  have hεTendsto :
      Filter.Tendsto (fun ε : ℝ => ε)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ)) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hsmallEventually :
      ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ε < t * (μ - β) :=
    (tendsto_order.1 hεTendsto).2 (t * (μ - β)) hδ
  filter_upwards [hsmallEventually, self_mem_nhdsWithin] with ε hεδ hεpos
  have happ_le0 :
      approximateSubdifferentialSupportAt f x ε.toNNReal y ≤
        (translatedDifferenceFunctionAt f x (t • y) + (((ε.toNNReal : NNReal) : ℝ) : EReal)) /
          (t : EReal) :=
    helperForTheorem_23_6_approximateSupport_le_regularizedDifferenceQuotient
      (f := f) hproper x y hx ε.toNNReal ht
  have happ_le :
      approximateSubdifferentialSupportAt f x ε.toNNReal y ≤
        (translatedDifferenceFunctionAt f x (t • y) + ((ε : ℝ) : EReal)) / (t : EReal) := by
    simpa [Real.toNNReal_of_nonneg (le_of_lt hεpos)] using happ_le0
  have hexpr :
      (translatedDifferenceFunctionAt f x (t • y) + ((ε : ℝ) : EReal)) / (t : EReal) =
        ((((f (x + t • y)).toReal - (f x).toReal + ε) / t : ℝ) : EReal) := by
    simp [translatedDifferenceFunctionAt, EReal.coe_div, EReal.coe_sub,
      EReal.coe_toReal hxtTop hxtBot, EReal.coe_toReal hx.1 hx.2]
  have hquotReal :
      ((f (x + t • y)).toReal - (f x).toReal + ε) / t < μ := by
    have hnum_lt : (f (x + t • y)).toReal - (f x).toReal + ε < μ * t := by
      nlinarith
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp [htne] at hnum_lt ⊢
    nlinarith
  have hexpr_lt :
      (translatedDifferenceFunctionAt f x (t • y) + ((ε : ℝ) : EReal)) / (t : EReal) <
        ((μ : ℝ) : EReal) := by
    rw [hexpr]
    exact_mod_cast hquotReal
  -- Combine the eventual real upper control with the pointwise Fenchel estimate.
  exact lt_of_le_of_lt happ_le hexpr_lt

/-- Helper for Theorem 23.6: every strict real lower bound below the directional derivative is
eventually dominated by all approximate-support values in the closed case. -/
lemma helperForTheorem_23_6_eventually_gt_of_real_lt_upperDirectionalDerivative_of_closed
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) {μ : ℝ}
    (hμ : ((μ : ℝ) : EReal) < upperDirectionalDerivativeAt f x y) :
    ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      ((μ : ℝ) : EReal) < approximateSubdifferentialSupportAt f x ε.toNNReal y := by
  -- The closed-case lower estimate is pointwise on `Ioi 0`, so the filter statement follows
  -- directly from eventual membership in that right-neighborhood.
  filter_upwards [self_mem_nhdsWithin] with ε hε
  -- Compare the chosen real lower bound with the pointwise lower support estimate.
  exact lt_of_lt_of_le hμ
    (helperForTheorem_23_6_upperDirectionalDerivative_le_approximateSupport_of_closed
      (f := f) hclosed hproper x y hx ε hε)

/-- Theorem 23.6: If `f` is a closed proper convex function and `x` is a point where `f` is finite, then for
every direction `y` the directional derivative `f'(x; y)` is the right-hand limit, as
`ε ↓ 0`, of the support values `δ^*(y | ∂_ε f(x))` of the approximate subdifferentials. -/
theorem directionalDerivative_eq_tendsto_approximateSubdifferentialSupport {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x y : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    Filter.Tendsto
      (fun ε : ℝ => approximateSubdifferentialSupportAt f x ε.toNNReal y)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (upperDirectionalDerivativeAt f x y)) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hUpperNeighborhood :
      ∀ μ : ℝ, upperDirectionalDerivativeAt f x y < ((μ : ℝ) : EReal) →
        ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          approximateSubdifferentialSupportAt f x ε.toNNReal y < ((μ : ℝ) : EReal) := by
    intro μ hμ
    exact
      helperForTheorem_23_6_eventually_lt_of_upperDirectionalDerivative_lt_real
        (f := f) hproper x y hx hμ
  have hLowerNeighborhoodReal :
      ∀ μ : ℝ, ((μ : ℝ) : EReal) < upperDirectionalDerivativeAt f x y →
        ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
          ((μ : ℝ) : EReal) < approximateSubdifferentialSupportAt f x ε.toNNReal y := by
    intro μ hμ
    -- Package the closed-case pointwise lower bound into the neighborhood form used by
    -- `tendsto_order`.
    exact
      helperForTheorem_23_6_eventually_gt_of_real_lt_upperDirectionalDerivative_of_closed
        (f := f) hclosed hproper x y hx hμ
  -- Reduce convergence in `EReal` to lower and upper eventual inequalities around the limit.
  refine (tendsto_order.2 ?_)
  constructor
  · intro a ha
    obtain ⟨μ, haμ, hμ⟩ := EReal.exists_between_coe_real ha
    filter_upwards [hLowerNeighborhoodReal μ hμ] with ε hε
    exact lt_trans haμ hε
  · intro a ha
    obtain ⟨μ, hμ, hμa⟩ := EReal.exists_between_coe_real ha
    filter_upwards [hUpperNeighborhood μ hμ] with ε hε
    exact lt_trans hε hμa


end Section23
end Chap05

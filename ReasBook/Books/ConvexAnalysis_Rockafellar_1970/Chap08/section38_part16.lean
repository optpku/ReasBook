/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part21
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section13_part6

section Chap08
section Section38

/-- Definition 38.5.2: For a (proper) convex function `f` and a (proper) concave function `g` on
`ℝ^n`, define

`α = sup_{x ∈ dom f} (g*(x) - f(x))` and `β = inf_{y ∈ dom g} (f*(y) - g(y))`,

where `f*` is `convexConjugateInner f` and `g*` is `concaveConjugateInner g` (both using the
Euclidean inner product on `Fin n → ℝ`). If `α = β`, their common value is called the inner product
`⟨f, g⟩`; otherwise `⟨f, g⟩` is undefined. This remains well-defined even when `f` or `g` is
improper. -/
noncomputable def fenchelInnerProduct {n : Nat} (f g : (Fin n → ℝ) → EReal) : Option EReal :=
  let α : EReal := ⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f}, concaveConjugateInner g x.1 - f x.1
  let β : EReal := ⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g}, convexConjugateInner f y.1 - g y.1
  letI : DecidableEq EReal := Classical.decEq _
  if α = β then some α else none

-- Proof sketch: Apply Fenchel duality (Corollary 13.3.1 in the text) under either relative-
-- interior qualification, together with the indicated closedness assumption, to obtain equality
-- of the primal and dual extremal values `α` and `β` from Definition 38.5.2; then
-- `fenchelInnerProduct f g` is defined. The bounded-domain criterion is a standard sufficient
-- condition implying such qualification.
/-- Proposition 38.5.3: For a proper convex `f` and a proper concave `g` on `ℝ^n`, the inner product
`⟨f, g⟩` (modeled by `fenchelInnerProduct f g`) exists in particular under either condition:

1. `g` is closed and `ri (dom f) ∩ ri (dom g*) ≠ ∅`;
2. `f` is closed and `ri (dom g) ∩ ri (dom f*) ≠ ∅`.

A simple sufficient condition is that `f` and `g` are closed and either `dom f` or `dom g` is
bounded.

Here `ri` is `intrinsicInterior`, `dom f` is `erealDom f`, `dom g` is `erealDomBot g`,
`f*` is `convexConjugateInner f`, and `g*` is `concaveConjugateInner g`. -/
lemma convexConjugateInner_eq_fenchelConjugate {n : Nat}
    (f : (Fin n → ℝ) → EReal) (y : Fin n → ℝ) :
    convexConjugateInner f y = fenchelConjugate n f y := by
  unfold convexConjugateInner
  rw [fenchelConjugate_eq_iSup]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    have hx : (((x.1 ⬝ᵥ y : ℝ) : EReal) - f x.1) ≤
        ⨆ z : Fin n → ℝ, (((z ⬝ᵥ y : ℝ) : EReal) - f z) :=
      le_iSup (fun z : Fin n → ℝ => (((z ⬝ᵥ y : ℝ) : EReal) - f z)) x.1
    have hx' :
        (∑ i : Fin n, (((x.1 i) * (y i) : ℝ) : EReal)) - f x.1 ≤
          ⨆ z : Fin n → ℝ, (((z ⬝ᵥ y : ℝ) : EReal) - f z) := by
      simpa [dotProduct, ← ereal_sum_coe] using hx
    simpa [dotProduct] using hx'
  · refine iSup_le ?_
    intro x
    by_cases hx : x ∈ erealDom f
    · have hx' : (((x ⬝ᵥ y : ℝ) : EReal) - f x) ≤
          ⨆ z : {z : Fin n → ℝ // z ∈ erealDom f},
            ((Finset.univ.sum (fun i : Fin n => z.1 i * y i)) : EReal) - f z.1 := by
        refine le_iSup_of_le ⟨x, hx⟩ ?_
        have : (((x ⬝ᵥ y : ℝ) : EReal) - f x) ≤ (((x ⬝ᵥ y : ℝ) : EReal) - f x) := le_rfl
        simpa [dotProduct, ← ereal_sum_coe] using this
      simpa [dotProduct] using hx'
    · have hx_top : f x = ⊤ := by
        simpa [erealDom, lt_top_iff_ne_top] using hx
      simp [dotProduct, hx_top]

lemma concaveConjugateInner_eq_concaveFenchelConjugate {n : Nat}
    (g : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) :
    concaveConjugateInner g x = concaveFenchelConjugate g x := by
  rw [helperForLemma_31_0_11_concaveFenchelConjugate_eq_iInf]
  unfold concaveConjugateInner
  apply le_antisymm
  · refine le_iInf ?_
    intro y
    by_cases hy : y ∈ erealDomBot g
    · have hy' :
          (⨅ z : {z : Fin n → ℝ // z ∈ erealDomBot g},
            ((Finset.univ.sum (fun i : Fin n => x i * z.1 i)) : EReal) - g z.1) ≤
          (((y ⬝ᵥ x : ℝ) : EReal) - g y) := by
        refine iInf_le_of_le ⟨y, hy⟩ ?_
        have : (((y ⬝ᵥ x : ℝ) : EReal) - g y) ≤ (((y ⬝ᵥ x : ℝ) : EReal) - g y) := le_rfl
        simpa [dotProduct, dotProduct_comm, ← ereal_sum_coe, mul_comm] using this
      simpa [dotProduct, dotProduct_comm, ← ereal_sum_coe, mul_comm] using hy'
    · have hy_bot : g y = ⊥ := by
        simpa [erealDomBot, bot_lt_iff_ne_bot] using hy
      simp [dotProduct, hy_bot]
  · refine le_iInf ?_
    intro y
    have hy' :
        (⨅ v : Fin n → ℝ, (((v ⬝ᵥ x : ℝ) : EReal) - g v)) ≤
          (((y.1 ⬝ᵥ x : ℝ) : EReal) - g y.1) :=
      iInf_le (fun v : Fin n → ℝ => (((v ⬝ᵥ x : ℝ) : EReal) - g v)) y.1
    have hy'' :
        (⨅ v : Fin n → ℝ, (((v ⬝ᵥ x : ℝ) : EReal) - g v)) ≤
          (∑ i : Fin n, (((x i) * (y.1 i) : ℝ) : EReal)) - g y.1 := by
      simpa [dotProduct, dotProduct_comm, ← ereal_sum_coe, mul_comm] using hy'
    simpa [dotProduct] using hy''

lemma properConcaveFunctionOn_univ_of_isProperNeg_and_isERealConvexNeg {n : Nat}
    {g : (Fin n → ℝ) → EReal}
    (hg_concave : IsERealConvex (fun y => -g y))
    (hg_proper : IsProperEReal (fun y => -g y)) :
    ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
  simpa [ProperConcaveFunctionOn] using
    (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      (fun y => -g y) hg_proper hg_concave)

lemma erealDom_convexConjugateInner_eq_effectiveDomain_fenchelConjugate {n : Nat}
    (f : (Fin n → ℝ) → EReal) :
    erealDom (convexConjugateInner f) =
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
  ext x
  simp [erealDom, effectiveDomain_eq, convexConjugateInner_eq_fenchelConjugate]

lemma erealDomBot_concaveConjugateInner_eq_concaveConjugateEffectiveDomain {n : Nat}
    (g : (Fin n → ℝ) → EReal) :
    erealDomBot (concaveConjugateInner g) = concaveConjugateEffectiveDomain g := by
  ext x
  simp [erealDomBot, concaveConjugateEffectiveDomain, effectiveDomain_eq,
    concaveConjugateInner_eq_concaveFenchelConjugate, bot_lt_iff_ne_bot,
    lt_top_iff_ne_top, EReal.neg_eq_top_iff]

lemma helperForFenchelInnerProduct_alpha_eq_neg_primalInf {n : Nat}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f}, g x.1 - f x.1) =
      -fenchelPrimalInfimum f g := by
  have hCommon :=
    helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
      (n := n) f g hf hg
  have hObj :
      ∀ x : Fin n → ℝ, g x - f x = -(f x - g x) := by
    intro x
    have hf_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
    have hg_ne_top : g x ≠ (⊤ : EReal) := by
      intro htop
      have hneg_ne_bot : -(g x) ≠ (⊥ : EReal) := hg.2.2 x (by simp)
      exact hneg_ne_bot (by simpa [htop])
    have hNegSub :
        -(f x - g x) = g x - f x := by
      calc
        -(f x - g x) = -(f x) + g x := by
          exact
            EReal.neg_sub (x := f x) (y := g x)
              (h1 := Or.inl hf_ne_bot) (h2 := Or.inr hg_ne_top)
        _ = g x - f x := by
          simp [sub_eq_add_neg, add_comm]
    exact hNegSub.symm
  have hReindex :
      (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f}, g x.1 - f x.1) =
        ⨆ x : Fin n → ℝ, g x - f x := by
    apply le_antisymm
    · refine iSup_le ?_
      intro x
      exact le_iSup (fun z : Fin n → ℝ => g z - f z) x.1
    · refine iSup_le ?_
      intro x
      by_cases hx : x ∈ erealDom f
      · exact le_iSup_of_le ⟨x, hx⟩ le_rfl
      · have hx_top : f x = (⊤ : EReal) := by
          simpa [erealDom, lt_top_iff_ne_top] using hx
        simp [hx_top]
  calc
    (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f}, g x.1 - f x.1)
        = ⨆ x : Fin n → ℝ, g x - f x := hReindex
    _ = ⨆ x : Fin n → ℝ, -(f x - g x) := by
          congr with x
          exact hObj x
    _ = -(⨅ x : Fin n → ℝ, f x - g x) := by
          simpa using (ereal_iSup_neg_eq_neg_iInf (g := fun x : Fin n → ℝ => f x - g x))
    _ = -fenchelPrimalInfimum f g := by
          simp [fenchelPrimalInfimum, functionInfimumEReal, hCommon]

lemma helperForFenchelInnerProduct_beta_eq_primalInf {n : Nat}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g}, f y.1 - g y.1) =
      fenchelPrimalInfimum f g := by
  have hCommon :=
    helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
      (n := n) f g hf hg
  have hSubtype_le_all :
      (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g}, f y.1 - g y.1) ≤
        ⨅ y : Fin n → ℝ, f y - g y := by
    refine le_iInf ?_
    intro y
    by_cases hy : y ∈ erealDomBot g
    · exact iInf_le (fun z : {z : (Fin n → ℝ) // z ∈ erealDomBot g} => f z.1 - g z.1) ⟨y, hy⟩
    · have hy_bot : g y = (⊥ : EReal) := by
        simpa [erealDomBot, bot_lt_iff_ne_bot] using hy
      have hf_ne_bot : f y ≠ (⊥ : EReal) := hf.2.2 y (by simp)
      simp [hy_bot, hf_ne_bot]
  have hAll_le_subtype :
      (⨅ y : Fin n → ℝ, f y - g y) ≤
        (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g}, f y.1 - g y.1) := by
    refine le_iInf ?_
    intro y
    exact iInf_le (fun z : Fin n → ℝ => f z - g z) y.1
  calc
    (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g}, f y.1 - g y.1)
        = ⨅ y : Fin n → ℝ, f y - g y := by
            exact le_antisymm hSubtype_le_all hAll_le_subtype
    _ = fenchelPrimalInfimum f g := by
          simp [fenchelPrimalInfimum, functionInfimumEReal, hCommon]

lemma closedConvexFunction_of_isProperEReal_and_isERealConvex_and_lsc {n : Nat}
    (f : (Fin n → ℝ) → EReal)
    (hf_proper : IsProperEReal f)
    (hf_convex : IsERealConvex f)
    (hf_lsc : LowerSemicontinuous f) :
    ClosedConvexFunction f := by
  let hf_proper_on :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      f hf_proper hf_convex
  exact (properConvexFunction_closed_iff_lowerSemicontinuous hf_proper_on).2 hf_lsc

lemma closedConcaveFunction_of_isProperNeg_and_isERealConvexNeg_and_lsc {n : Nat}
    (g : (Fin n → ℝ) → EReal)
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y))
    (hg_lsc : LowerSemicontinuous (fun y => -g y)) :
    ClosedConcaveFunction g := by
  simpa [ClosedConcaveFunction] using
    (closedConvexFunction_of_isProperEReal_and_isERealConvex_and_lsc
      (f := fun y => -g y) hg_proper hg_concave hg_lsc)

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 400000

/-- Proposition 38.5.3: For a proper convex `f` and a proper concave `g` on `ℝ^n`, the inner product
`⟨f, g⟩` (modeled by `fenchelInnerProduct f g`) exists in particular under either condition:

1. `g` is closed and `ri (dom f) ∩ ri (dom g*) ≠ ∅`;
2. `f` is closed and `ri (dom g) ∩ ri (dom f*) ≠ ∅`.

A simple sufficient condition is that `f` and `g` are closed and either `dom f` or `dom g` is
bounded.

Here `ri` is `intrinsicInterior`, `dom f` is `erealDom f`, `dom g` is `erealDomBot g`,
`f*` is `convexConjugateInner f`, and `g*` is `concaveConjugateInner g`. -/
theorem fenchelInnerProduct_exists_of_closed_ri_or_bounded_domain {n : Nat}
    {f g : (Fin n → ℝ) → EReal}
    (hf_convex : IsERealConvex f)
    (hg_concave : IsERealConvex (fun y => -g y))
    (hf_proper : IsProperEReal f)
    (hg_proper : IsProperEReal (fun y => -g y))
    (hcond :
      (LowerSemicontinuous (fun y => -g y) ∧
          (intrinsicInterior ℝ (erealDom f) ∩
              intrinsicInterior ℝ (erealDomBot (concaveConjugateInner g))).Nonempty) ∨
        (LowerSemicontinuous f ∧
          (intrinsicInterior ℝ (erealDomBot g) ∩
              intrinsicInterior ℝ (erealDom (convexConjugateInner f))).Nonempty) ∨
        (LowerSemicontinuous f ∧ LowerSemicontinuous (fun y => -g y) ∧
          (Bornology.IsBounded (erealDom f) ∨ Bornology.IsBounded (erealDomBot g)))) :
    ∃ c : EReal, fenchelInnerProduct f g = some c := by
  classical
  have hf_proper_on : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      f hf_proper hf_convex
  have hg_proper_on : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    simpa [ProperConcaveFunctionOn] using
      (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        (fun y => -g y) hg_proper hg_concave)
  have hf_star_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper_on
  have hcaseA :
      LowerSemicontinuous (fun y => -g y) →
      (intrinsicInterior ℝ (erealDom f) ∩
          intrinsicInterior ℝ (erealDomBot (concaveConjugateInner g))).Nonempty →
      ∃ c : EReal, fenchelInnerProduct f g = some c := by
    intro hg_lsc hri
    let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
    have hg_closed : ClosedConcaveFunction g :=
      closedConcaveFunction_of_isProperNeg_and_isERealConvexNeg_and_lsc
        (g := g) hg_proper hg_concave hg_lsc
    have hg_star_proper : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
      simpa [gStar] using
        helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
          (n := n) (g := g) hg_proper_on
    have hA : FenchelConditionA (n := n) f gStar := by
      rcases hri with ⟨x, hxF, hxGStar⟩
      refine ⟨x, ?_, ?_⟩
      · rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
            (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)]
        simpa [erealDom, effectiveDomain_eq] using hxF
      · rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
            (n := n) (C := concaveEffectiveDomain gStar)]
        simpa [gStar, concaveEffectiveDomain, concaveConjugateEffectiveDomain, effectiveDomain_eq,
          erealDomBot_concaveConjugateInner_eq_concaveConjugateEffectiveDomain] using hxGStar
    have hFenchelA :
        fenchelPrimalInfimum f gStar = fenchelDualSupremum (n := n) f gStar :=
      (helperForTheorem_31_1_conditionA_concaveDuality_core
        (n := n) f gStar hf_proper_on hg_star_proper hA).1
    have hg_biconj_fun : concaveFenchelConjugate gStar = g := by
      funext x
      simpa [gStar] using
        helperForTheorem_31_1_concave_biconjugate_eq_of_closedConcave
          (n := n) (g := g) hg_closed hg_proper_on x
    have hAlphaCore :
        (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
          concaveConjugateInner g x.1 - f x.1) =
          -fenchelPrimalInfimum f gStar := by
      simpa [gStar, concaveConjugateInner_eq_concaveFenchelConjugate] using
        helperForFenchelInnerProduct_alpha_eq_neg_primalInf
          (n := n) f gStar hf_proper_on hg_star_proper
    have hBetaCore :
        (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g},
          convexConjugateInner f y.1 - g y.1) =
          fenchelPrimalInfimum (fenchelConjugate n f) g := by
      simpa [convexConjugateInner_eq_fenchelConjugate] using
        helperForFenchelInnerProduct_beta_eq_primalInf
          (n := n) (fenchelConjugate n f) g hf_star_proper hg_proper_on
    have hDualToBeta :
        -fenchelDualSupremum (n := n) f gStar = fenchelPrimalInfimum (fenchelConjugate n f) g := by
      have hDual :=
        helperForTheorem_31_1_dual_eq_neg_primal_of_conjugate_pair
          (n := n) f gStar hf_proper_on hg_star_proper
      have hNegDual := congrArg (fun t : EReal => -t) hDual
      simpa [gStar, hg_biconj_fun] using hNegDual
    have hNegFenchelA := congrArg (fun t : EReal => -t) hFenchelA
    have hAlphaBeta :
        -fenchelPrimalInfimum f gStar = fenchelPrimalInfimum (fenchelConjugate n f) g := by
      calc
        -fenchelPrimalInfimum f gStar = -fenchelDualSupremum (n := n) f gStar := by
          simpa using hNegFenchelA
        _ = fenchelPrimalInfimum (fenchelConjugate n f) g := hDualToBeta
    refine ⟨fenchelPrimalInfimum (fenchelConjugate n f) g, ?_⟩
    unfold fenchelInnerProduct
    have hAlpha :
        (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
          concaveConjugateInner g x.1 - f x.1) =
          fenchelPrimalInfimum (fenchelConjugate n f) g :=
      hAlphaCore.trans hAlphaBeta
    simp [hAlpha, hBetaCore]
  have hcaseB :
      LowerSemicontinuous f →
      (intrinsicInterior ℝ (erealDomBot g) ∩
          intrinsicInterior ℝ (erealDom (convexConjugateInner f))).Nonempty →
      ∃ c : EReal, fenchelInnerProduct f g = some c := by
    intro hf_lsc hri
    let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
    let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
    have hf_closed : ClosedConvexFunction f :=
      closedConvexFunction_of_isProperEReal_and_isERealConvex_and_lsc
        (f := f) hf_proper hf_convex hf_lsc
    have hg_star_proper : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
      simpa [gStar] using
        helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
          (n := n) (g := g) hg_proper_on
    have hA : FenchelConditionA (n := n) fStar g := by
      rcases hri with ⟨x, hxG, hxFStar⟩
      refine ⟨x, ?_, ?_⟩
      · rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
            (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))]
        simpa [fStar, erealDom_convexConjugateInner_eq_effectiveDomain_fenchelConjugate] using hxFStar
      · rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
            (n := n) (C := concaveEffectiveDomain g)]
        simpa [concaveEffectiveDomain, erealDomBot, effectiveDomain_eq,
          bot_lt_iff_ne_bot, lt_top_iff_ne_top, EReal.neg_eq_top_iff] using hxG
    have hFenchelA :
        fenchelPrimalInfimum fStar g = fenchelDualSupremum (n := n) fStar g :=
      (helperForTheorem_31_1_conditionA_concaveDuality_core
        (n := n) fStar g hf_star_proper hg_proper_on hA).1
    have hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal) := by
      intro x
      exact hf_proper_on.2.2 x (by simp)
    have hf_biconj : fenchelConjugate n fStar = f :=
      fenchelConjugate_biconjugate_eq_of_closedConvex
        (n := n) (f := f)
        (hf_closed := hf_closed.2) (hf_convex := hf_closed.1) (hf_ne_bot := hf_ne_bot)
    have hDualToAlpha :
        fenchelDualSupremum (n := n) fStar g = -fenchelPrimalInfimum f gStar := by
      simpa [fStar, gStar, hf_biconj] using
        helperForTheorem_31_1_dual_eq_neg_primal_of_conjugate_pair
          (n := n) fStar g hf_star_proper hg_proper_on
    have hAlphaCore :
        (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
          concaveConjugateInner g x.1 - f x.1) =
          -fenchelPrimalInfimum f gStar := by
      simpa [gStar, concaveConjugateInner_eq_concaveFenchelConjugate] using
        helperForFenchelInnerProduct_alpha_eq_neg_primalInf
          (n := n) f gStar hf_proper_on hg_star_proper
    have hBetaCore :
        (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g},
          convexConjugateInner f y.1 - g y.1) =
          fenchelPrimalInfimum fStar g := by
      simpa [fStar, convexConjugateInner_eq_fenchelConjugate] using
        helperForFenchelInnerProduct_beta_eq_primalInf
          (n := n) fStar g hf_star_proper hg_proper_on
    have hAlphaBeta :
        -fenchelPrimalInfimum f gStar = fenchelPrimalInfimum fStar g := by
      calc
        -fenchelPrimalInfimum f gStar = fenchelDualSupremum (n := n) fStar g := by
          simpa using hDualToAlpha.symm
        _ = fenchelPrimalInfimum fStar g := hFenchelA.symm
    refine ⟨fenchelPrimalInfimum fStar g, ?_⟩
    unfold fenchelInnerProduct
    have hAlpha :
        (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
          concaveConjugateInner g x.1 - f x.1) =
          fenchelPrimalInfimum fStar g :=
      hAlphaCore.trans hAlphaBeta
    simp [hAlpha, hBetaCore]
  rcases hcond with hA | hrest
  · exact hcaseA hA.1 hA.2
  · rcases hrest with hB | hbounded
    · exact hcaseB hB.1 hB.2
    · rcases hbounded with ⟨hf_lsc, hg_lsc, hboundedfg⟩
      cases hboundedfg with
      | inl hboundedF =>
          have hf_closed : ClosedConvexFunction f :=
            closedConvexFunction_of_isProperEReal_and_isERealConvex_and_lsc
              (f := f) hf_proper hf_convex hf_lsc
          have hcofinite : CoFiniteConvexFunction f := by
            apply coFiniteConvexFunction_of_isBounded_effectiveDomain (n := n) (f := f)
              hf_closed hf_proper_on
            simpa [erealDom, effectiveDomain_eq] using hboundedF
          have hstarDom :=
            (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite (n := n) (f := f) hf_closed).2 hcofinite
          let hNeg : (Fin n → ℝ) → EReal := fun y => -g y
          have hNegProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) hNeg := by
            simpa [hNeg, ProperConcaveFunctionOn] using hg_proper_on
          rcases (helperForTheorem_31_5_relativeInteriorWitnesses (n := n) hNeg hNegProper).1 with
            ⟨x0, hx0riG⟩
          have hx0riG' : x0 ∈ intrinsicInterior ℝ (erealDomBot g) := by
            rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
              (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) hNeg)] at hx0riG
            simpa [hNeg, erealDomBot, effectiveDomain_eq,
              bot_lt_iff_ne_bot, lt_top_iff_ne_top, EReal.neg_eq_top_iff] using hx0riG
          have hx0riFStarE :
              x0 ∈ euclideanRelativeInterior_fin n
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
            rw [hstarDom.1]
            exact helperForTheorem_31_5_mem_euclideanRelativeInterior_univ (n := n) x0
          have hx0riFStar : x0 ∈ intrinsicInterior ℝ (erealDom (convexConjugateInner f)) := by
            rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
              (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))] at hx0riFStarE
            simpa [erealDom_convexConjugateInner_eq_effectiveDomain_fenchelConjugate] using hx0riFStarE
          exact hcaseB hf_lsc ⟨x0, hx0riG', hx0riFStar⟩
      | inr hboundedG =>
          let hNeg : (Fin n → ℝ) → EReal := fun y => -g y
          have hNegClosed : ClosedConvexFunction hNeg :=
            closedConvexFunction_of_isProperEReal_and_isERealConvex_and_lsc
              (f := hNeg) hg_proper hg_concave hg_lsc
          have hNegProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) hNeg := by
            simpa [hNeg, ProperConcaveFunctionOn] using hg_proper_on
          have hcofiniteNeg : CoFiniteConvexFunction hNeg := by
            apply coFiniteConvexFunction_of_isBounded_effectiveDomain (n := n) (f := hNeg)
              hNegClosed hNegProper
            simpa [hNeg, erealDomBot, effectiveDomain_eq, bot_lt_iff_ne_bot,
              lt_top_iff_ne_top, EReal.neg_eq_top_iff] using hboundedG
          have hstarDomNeg :=
            (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite (n := n) (f := hNeg) hNegClosed).2
              hcofiniteNeg
          rcases (helperForTheorem_31_5_relativeInteriorWitnesses (n := n) f hf_proper_on).1 with
            ⟨x0, hx0riF⟩
          have hx0riF' : x0 ∈ intrinsicInterior ℝ (erealDom f) := by
            rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
              (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)] at hx0riF
            simpa [erealDom, effectiveDomain_eq] using hx0riF
          have hx0domGStarE : x0 ∈ euclideanRelativeInterior_fin n (Set.univ : Set (Fin n → ℝ)) := by
            exact helperForTheorem_31_5_mem_euclideanRelativeInterior_univ (n := n) x0
          have hx0riGStar : x0 ∈ intrinsicInterior ℝ (erealDomBot (concaveConjugateInner g)) := by
            have hdomGStar : erealDomBot (concaveConjugateInner g) = Set.univ := by
              ext x
              have hxDom : (-x) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n hNeg) := by
                simpa [hstarDomNeg.1]
              simpa [hNeg, erealDomBot, effectiveDomain_eq,
                concaveConjugateInner_eq_concaveFenchelConjugate, concaveFenchelConjugate,
                bot_lt_iff_ne_bot, lt_top_iff_ne_top, EReal.neg_eq_top_iff] using hxDom
            rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
              (n := n) (C := (Set.univ : Set (Fin n → ℝ)))] at hx0domGStarE
            simpa [hdomGStar] using hx0domGStarE
          exact hcaseA hg_lsc ⟨x0, hx0riF', hx0riGStar⟩

/-- The convex indicator of a point `a ∈ ℝ^n`: the function `f(x) = δ(x | a)` which is `0` at
`x = a` and `+∞` otherwise. -/
noncomputable def convexIndicatorPoint {n : Nat} (a : Fin n → ℝ) : (Fin n → ℝ) → EReal :=
  fun x =>
    letI : DecidableEq (Fin n → ℝ) := Classical.decEq _
    if x = a then 0 else ⊤

/-- The concave indicator of a point `b ∈ ℝ^n`: the function `g(y) = -δ(y | b)` which is `0` at
`y = b` and `-∞` otherwise. -/
noncomputable def concaveIndicatorPoint {n : Nat} (b : Fin n → ℝ) : (Fin n → ℝ) → EReal :=
  fun y =>
    letI : DecidableEq (Fin n → ℝ) := Classical.decEq _
    if y = b then 0 else ⊥

-- Proof sketch: Compute `f*` and `g*` explicitly for point indicators: the conjugate of `δ(·|a)`
-- is the linear form `y ↦ ⟨a, y⟩`, and the concave conjugate of `-δ(·|b)` is `x ↦ ⟨x, b⟩`.
-- Substituting into Definition 38.5.2 makes both extremal values `α` and `β` equal to `⟨a, b⟩`,
-- so `fenchelInnerProduct f g = some ⟨a, b⟩`.
lemma erealDomBot_concaveIndicatorPoint {n : Nat} (xStar : Fin n → ℝ) :
    erealDomBot (concaveIndicatorPoint xStar) = {xStar} := by
  ext y
  by_cases hy : y = xStar
  · simp [erealDomBot, concaveIndicatorPoint, hy]
  · simp [erealDomBot, concaveIndicatorPoint, hy]

lemma concaveIndicatorPoint_domBot_subsingleton {n : Nat} (xStar : Fin n → ℝ) :
    Subsingleton {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint xStar)} := by
  refine ⟨?_⟩
  intro y1 y2
  apply Subtype.ext
  have hy1 : y1.1 = xStar := by
    have : y1.1 ∈ erealDomBot (concaveIndicatorPoint xStar) := y1.2
    simpa [erealDomBot_concaveIndicatorPoint] using this
  have hy2 : y2.1 = xStar := by
    have : y2.1 ∈ erealDomBot (concaveIndicatorPoint xStar) := y2.2
    simpa [erealDomBot_concaveIndicatorPoint] using this
  simpa [hy1, hy2]

lemma concaveConjugateInner_concaveIndicatorPoint {n : Nat}
    (x xStar : Fin n → ℝ) :
    concaveConjugateInner (concaveIndicatorPoint xStar) x =
      ((Finset.univ.sum (fun i : Fin n => x i * xStar i)) : EReal) := by
  classical
  unfold concaveConjugateInner
  let y0 : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint xStar)} :=
    ⟨xStar, by simpa [erealDomBot_concaveIndicatorPoint]⟩
  letI := concaveIndicatorPoint_domBot_subsingleton xStar
  have hconst :
      (fun y : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint xStar)} =>
        ((Finset.univ.sum (fun i : Fin n => x i * y.1 i)) : EReal) - concaveIndicatorPoint xStar y.1) =
      fun _ => ((Finset.univ.sum (fun i : Fin n => x i * xStar i)) : EReal) := by
    funext y
    have hy : y = y0 := Subsingleton.elim _ _
    rw [hy]
    simp [y0, concaveIndicatorPoint]
  rw [hconst]
  simpa using (ciInf_subsingleton y0
    (fun _ : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint xStar)} =>
      ((Finset.univ.sum (fun i : Fin n => x i * xStar i)) : EReal)))

lemma erealDom_convexIndicatorPoint {n : Nat} (a : Fin n → ℝ) :
    erealDom (convexIndicatorPoint a) = {a} := by
  ext x
  by_cases hx : x = a
  · simp [erealDom, convexIndicatorPoint, hx]
  · simp [erealDom, convexIndicatorPoint, hx]

lemma convexIndicatorPoint_dom_subsingleton {n : Nat} (a : Fin n → ℝ) :
    Subsingleton {x : Fin n → ℝ // x ∈ erealDom (convexIndicatorPoint a)} := by
  refine ⟨?_⟩
  intro x1 x2
  apply Subtype.ext
  have hx1 : x1.1 = a := by
    have : x1.1 ∈ erealDom (convexIndicatorPoint a) := x1.2
    simpa [erealDom_convexIndicatorPoint] using this
  have hx2 : x2.1 = a := by
    have : x2.1 ∈ erealDom (convexIndicatorPoint a) := x2.2
    simpa [erealDom_convexIndicatorPoint] using this
  simpa [hx1, hx2]

lemma convexConjugateInner_convexIndicatorPoint {n : Nat}
    (a y : Fin n → ℝ) :
    convexConjugateInner (convexIndicatorPoint a) y =
      ((Finset.univ.sum (fun i : Fin n => a i * y i)) : EReal) := by
  classical
  unfold convexConjugateInner
  let x0 : {x : Fin n → ℝ // x ∈ erealDom (convexIndicatorPoint a)} :=
    ⟨a, by simpa [erealDom_convexIndicatorPoint]⟩
  letI := convexIndicatorPoint_dom_subsingleton a
  have hconst :
      (fun x : {x : Fin n → ℝ // x ∈ erealDom (convexIndicatorPoint a)} =>
        ((Finset.univ.sum (fun i : Fin n => x.1 i * y i)) : EReal) - convexIndicatorPoint a x.1) =
      fun _ => ((Finset.univ.sum (fun i : Fin n => a i * y i)) : EReal) := by
    funext x
    have hx : x = x0 := Subsingleton.elim _ _
    rw [hx]
    simp [x0, convexIndicatorPoint]
  rw [hconst]
  simpa using (ciSup_subsingleton x0
    (fun _ : {x : Fin n → ℝ // x ∈ erealDom (convexIndicatorPoint a)} =>
      ((Finset.univ.sum (fun i : Fin n => a i * y i)) : EReal)))

/-- Proposition 38.5.4: Let `f(x) = δ(x | a)` be the convex indicator of the point `a ∈ ℝ^n`, and
let `g(y) = -δ(y | b)` be the concave indicator of the point `b ∈ ℝ^n`. Then

`⟨f, g⟩ = ⟨a, b⟩`,

the ordinary Euclidean inner product (here expressed as `∑ i, a i * b i`). -/
theorem fenchelInnerProduct_convexIndicatorPoint_concaveIndicatorPoint {n : Nat}
    (a b : Fin n → ℝ) :
    fenchelInnerProduct (convexIndicatorPoint a) (concaveIndicatorPoint b) =
      some ((Finset.univ.sum (fun i : Fin n => a i * b i)) : EReal) := by
  classical
  unfold fenchelInnerProduct
  let y0 : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint b)} :=
    ⟨b, by simpa [erealDomBot_concaveIndicatorPoint]⟩
  have hα :
      (⨆ x : {x : Fin n → ℝ // x ∈ erealDom (convexIndicatorPoint a)},
        concaveConjugateInner (concaveIndicatorPoint b) x.1 - convexIndicatorPoint a x.1) =
      ((Finset.univ.sum (fun i : Fin n => a i * b i)) : EReal) := by
    calc
      (⨆ x : {x : Fin n → ℝ // x ∈ erealDom (convexIndicatorPoint a)},
          concaveConjugateInner (concaveIndicatorPoint b) x.1 - convexIndicatorPoint a x.1) =
          convexConjugateInner (convexIndicatorPoint a) b := by
            unfold convexConjugateInner
            simp [concaveConjugateInner_concaveIndicatorPoint]
      _ = ((Finset.univ.sum (fun i : Fin n => a i * b i)) : EReal) := by
            simpa using convexConjugateInner_convexIndicatorPoint a b
  have hβ :
      (⨅ y : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint b)},
        convexConjugateInner (convexIndicatorPoint a) y.1 - concaveIndicatorPoint b y.1) =
      ((Finset.univ.sum (fun i : Fin n => a i * b i)) : EReal) := by
    letI := concaveIndicatorPoint_domBot_subsingleton b
    calc
      (⨅ y : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint b)},
          convexConjugateInner (convexIndicatorPoint a) y.1 - concaveIndicatorPoint b y.1) =
          convexConjugateInner (convexIndicatorPoint a) y0.1 - concaveIndicatorPoint b y0.1 := by
            simpa using
              (ciInf_subsingleton y0
                (fun y : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint b)} =>
                  convexConjugateInner (convexIndicatorPoint a) y.1 - concaveIndicatorPoint b y.1))
      _ = ((Finset.univ.sum (fun i : Fin n => a i * b i)) : EReal) := by
          simp [y0, concaveIndicatorPoint, convexConjugateInner_convexIndicatorPoint]
  simp [hα, hβ]

-- Proof sketch: For `g(y) = -δ(y|x*)` (modeled by `concaveIndicatorPoint xStar`), its concave
-- conjugate is the linear form `x ↦ ⟨x, xStar⟩`, so the `α` and `β` extremal values in
-- Definition 38.5.2 both reduce to the convex conjugate `f*(xStar) = convexConjugateInner f xStar`.
/-- Proposition 38.5.5: The inner product notation `⟨f, g⟩` (Definition 38.5.2) agrees with the
notation `⟨f, x*⟩` for the conjugate `f*(x*)` from §33, in the sense that

`⟨f, g⟩ = ⟨f, x*⟩`

when `g(y) = -δ(y | x*)`. In Lean we model `g` as `concaveIndicatorPoint xStar` and `⟨f, x*⟩` as
`convexConjugateInner f xStar`, so the claim is `fenchelInnerProduct f g = some (f*(x*))`. -/
theorem fenchelInnerProduct_concaveIndicatorPoint_eq_convexConjugateInner {n : Nat}
    (f : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    fenchelInnerProduct f (concaveIndicatorPoint xStar) = some (convexConjugateInner f xStar) := by
  classical
  unfold fenchelInnerProduct
  let y0 : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint xStar)} :=
    ⟨xStar, by simpa [erealDomBot_concaveIndicatorPoint]⟩
  have hα :
      (⨆ x : {x : Fin n → ℝ // x ∈ erealDom f},
        concaveConjugateInner (concaveIndicatorPoint xStar) x.1 - f x.1) =
      convexConjugateInner f xStar := by
    unfold convexConjugateInner
    simp [concaveConjugateInner_concaveIndicatorPoint]
  have hβ :
      (⨅ y : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint xStar)},
        convexConjugateInner f y.1 - concaveIndicatorPoint xStar y.1) =
      convexConjugateInner f xStar := by
    letI := concaveIndicatorPoint_domBot_subsingleton xStar
    calc
      (⨅ y : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint xStar)},
          convexConjugateInner f y.1 - concaveIndicatorPoint xStar y.1) =
          convexConjugateInner f y0.1 - concaveIndicatorPoint xStar y0.1 := by
            simpa using
              (ciInf_subsingleton y0
                (fun y : {y : Fin n → ℝ // y ∈ erealDomBot (concaveIndicatorPoint xStar)} =>
                  convexConjugateInner f y.1 - concaveIndicatorPoint xStar y.1))
      _ = convexConjugateInner f xStar := by
          simp [y0, concaveIndicatorPoint]
  simp [hα, hβ]

end Section38
end Chap08

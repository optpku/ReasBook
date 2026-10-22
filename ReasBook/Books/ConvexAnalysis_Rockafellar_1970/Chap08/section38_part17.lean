/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part16

section Chap08
section Section38

-- Proof sketch: The extremal expressions defining `α` and `β` in Definition 38.5.2 are meaningful
-- for arbitrary `EReal`-valued functions (even if improper) because they are built from `iSup`/`iInf`
-- over effective domains and use `EReal`'s totalized arithmetic. Under the present repository
-- semantics, the textbook restricted-extrema formulas remain valid in the proper branch, but the
-- unconditional improper analogue of Proposition 38.5.3 is false; see the explicit `⊤/⊥`
-- counterexample below.
/-- Proposition 38.5.6: In the present formalization, the textbook restricted-extrema formulas

`⟨f, g⟩ = sup { g*(x) - f(x) | x ∈ dom g* ∩ dom f } = inf { f*(y) - g(y) | y ∈ dom f* ∩ dom g }`

remain valid once `f` and `-g` are proper. The naive extension of the existence clause from
Proposition 38.5.3 to arbitrary improper `EReal`-valued functions is refuted below. -/
theorem fenchelInnerProduct_exists_of_closed_ri_or_bounded_domain_improper {n : Nat}
    {f g : (Fin n → ℝ) → EReal} :
    ∀ {c : EReal},
      IsProperEReal f →
        IsProperEReal (fun y => -g y) →
          fenchelInnerProduct f g = some c →
            c =
                (⨆ x :
                    {x : (Fin n → ℝ) //
                      x ∈ erealDom f ∧ x ∈ erealDomBot (concaveConjugateInner g)},
                  concaveConjugateInner g x.1 - f x.1) ∧
              c =
                (⨅ y :
                    {y : (Fin n → ℝ) //
                      y ∈ erealDomBot g ∧ y ∈ erealDom (convexConjugateInner f)},
                  convexConjugateInner f y.1 - g y.1) := by
  intro c hf_proper hg_proper hc
  unfold fenchelInnerProduct at hc
  dsimp at hc
  split_ifs at hc with hEq
  · injection hc with hcEq
    subst hcEq
    constructor
    · trans (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
        concaveConjugateInner g x.1 - f x.1)
      · rfl
      · refine le_antisymm ?_ ?_
        · refine iSup_le ?_
          intro x
          by_cases hxStar : x.1 ∈ erealDomBot (concaveConjugateInner g)
          · exact le_iSup_of_le ⟨x.1, ⟨x.2, hxStar⟩⟩ le_rfl
          · have hbot : concaveConjugateInner g x.1 = (⊥ : EReal) := by
              simpa [erealDomBot, bot_lt_iff_ne_bot] using hxStar
            have hfx_ne_bot : f x.1 ≠ (⊥ : EReal) := hf_proper.1 x.1
            have hterm : concaveConjugateInner g x.1 - f x.1 = (⊥ : EReal) := by
              simpa [hbot] using (EReal.bot_sub hfx_ne_bot)
            rw [hterm]
            exact bot_le
        · refine iSup_le ?_
          intro x
          exact le_iSup_of_le ⟨x.1, x.2.1⟩ le_rfl
    · trans (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g},
        convexConjugateInner f y.1 - g y.1)
      · exact hEq
      · refine le_antisymm ?_ ?_
        · refine le_iInf ?_
          intro y
          exact iInf_le (fun z : {z : Fin n → ℝ // z ∈ erealDomBot g} =>
            convexConjugateInner f z.1 - g z.1) ⟨y.1, y.2.1⟩
        · refine le_iInf ?_
          intro y
          by_cases hyStar : y.1 ∈ erealDom (convexConjugateInner f)
          · exact iInf_le
              (fun z :
                {z : (Fin n → ℝ) //
                  z ∈ erealDomBot g ∧ z ∈ erealDom (convexConjugateInner f)} =>
                convexConjugateInner f z.1 - g z.1) ⟨y.1, ⟨y.2, hyStar⟩⟩
          · have htop : convexConjugateInner f y.1 = (⊤ : EReal) := by
              have hnotlt : ¬ convexConjugateInner f y.1 < (⊤ : EReal) := by
                simpa [erealDom] using hyStar
              exact (top_le_iff).1 ((not_lt).1 hnotlt)
            have hgy_ne_top : g y.1 ≠ (⊤ : EReal) := by
              intro hgy_top
              have hneg_ne_bot : -g y.1 ≠ (⊥ : EReal) := hg_proper.1 y.1
              exact hneg_ne_bot (by simpa [hgy_top])
            have hterm : convexConjugateInner f y.1 - g y.1 = (⊤ : EReal) := by
              simpa [htop] using (EReal.top_sub hgy_ne_top)
            rw [hterm]
            exact le_top

lemma fenchelInnerProduct_alpha_restrict_commonDom_of_proper {n : Nat}
    {f g : (Fin n → ℝ) → EReal}
    (hf_proper : IsProperEReal f) :
    (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
      concaveConjugateInner g x.1 - f x.1) =
      (⨆ x :
          {x : (Fin n → ℝ) //
            x ∈ erealDom f ∧ x ∈ erealDomBot (concaveConjugateInner g)},
        concaveConjugateInner g x.1 - f x.1) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro x
    by_cases hxStar : x.1 ∈ erealDomBot (concaveConjugateInner g)
    · exact le_iSup_of_le ⟨x.1, ⟨x.2, hxStar⟩⟩ le_rfl
    · have hbot : concaveConjugateInner g x.1 = (⊥ : EReal) := by
        simpa [erealDomBot, bot_lt_iff_ne_bot] using hxStar
      have hfx_ne_bot : f x.1 ≠ (⊥ : EReal) := hf_proper.1 x.1
      have hterm : concaveConjugateInner g x.1 - f x.1 = (⊥ : EReal) := by
        simpa [hbot] using (EReal.bot_sub hfx_ne_bot)
      rw [hterm]
      exact bot_le
  · refine iSup_le ?_
    intro x
    exact le_iSup_of_le ⟨x.1, x.2.1⟩ le_rfl

lemma fenchelInnerProduct_beta_restrict_commonDom_of_proper {n : Nat}
    {f g : (Fin n → ℝ) → EReal}
    (hg_proper : IsProperEReal (fun y => -g y)) :
    (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g},
      convexConjugateInner f y.1 - g y.1) =
      (⨅ y :
          {y : (Fin n → ℝ) //
            y ∈ erealDomBot g ∧ y ∈ erealDom (convexConjugateInner f)},
        convexConjugateInner f y.1 - g y.1) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro y
    exact iInf_le (fun z : {z : Fin n → ℝ // z ∈ erealDomBot g} =>
      convexConjugateInner f z.1 - g z.1) ⟨y.1, y.2.1⟩
  · refine le_iInf ?_
    intro y
    by_cases hyStar : y.1 ∈ erealDom (convexConjugateInner f)
    · exact iInf_le
        (fun z :
          {z : (Fin n → ℝ) //
            z ∈ erealDomBot g ∧ z ∈ erealDom (convexConjugateInner f)} =>
          convexConjugateInner f z.1 - g z.1) ⟨y.1, ⟨y.2, hyStar⟩⟩
    · have htop : convexConjugateInner f y.1 = (⊤ : EReal) := by
        have hnotlt : ¬ convexConjugateInner f y.1 < (⊤ : EReal) := by
          simpa [erealDom] using hyStar
        exact (top_le_iff).1 ((not_lt).1 hnotlt)
      have hgy_ne_top : g y.1 ≠ (⊤ : EReal) := by
        intro hgy_top
        have hneg_ne_bot : -g y.1 ≠ (⊥ : EReal) := hg_proper.1 y.1
        exact hneg_ne_bot (by simpa [hgy_top])
      have hterm : convexConjugateInner f y.1 - g y.1 = (⊤ : EReal) := by
        simpa [htop] using (EReal.top_sub hgy_ne_top)
      rw [hterm]
      exact le_top

lemma fenchelInnerProduct_textbook_extrema_of_proper {n : Nat}
    {f g : (Fin n → ℝ) → EReal}
    (hf_proper : IsProperEReal f)
    (hg_proper : IsProperEReal (fun y => -g y)) :
    ∀ {c : EReal},
      fenchelInnerProduct f g = some c →
        c =
            (⨆ x :
                {x : (Fin n → ℝ) //
                  x ∈ erealDom f ∧ x ∈ erealDomBot (concaveConjugateInner g)},
              concaveConjugateInner g x.1 - f x.1) ∧
          c =
            (⨅ y :
                {y : (Fin n → ℝ) //
                  y ∈ erealDomBot g ∧ y ∈ erealDom (convexConjugateInner f)},
              convexConjugateInner f y.1 - g y.1) := by
  intro c hc
  unfold fenchelInnerProduct at hc
  dsimp at hc
  split_ifs at hc with hEq
  injection hc with hcEq
  subst hcEq
  constructor
  · trans (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
      concaveConjugateInner g x.1 - f x.1)
    · rfl
    · exact fenchelInnerProduct_alpha_restrict_commonDom_of_proper hf_proper
  · trans (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g},
      convexConjugateInner f y.1 - g y.1)
    · exact hEq
    · exact fenchelInnerProduct_beta_restrict_commonDom_of_proper hg_proper

lemma helperForProposition_38_5_6_improper_textbook_formula_counterexample
    : fenchelInnerProduct (fun _ : Fin 1 → ℝ => (⊥ : EReal)) (fun _ : Fin 1 → ℝ => (⊤ : EReal)) = some (⊥ : EReal) ∧
      (⨅ y :
          {y : (Fin 1 → ℝ) //
            y ∈ erealDomBot (fun _ : Fin 1 → ℝ => (⊤ : EReal)) ∧
              y ∈ erealDom (convexConjugateInner (fun _ : Fin 1 → ℝ => (⊥ : EReal)))},
        convexConjugateInner (fun _ : Fin 1 → ℝ => (⊥ : EReal)) y.1 - (⊤ : EReal)) = (⊤ : EReal) := by
  constructor
  · simp [fenchelInnerProduct, concaveConjugateInner, convexConjugateInner, erealDom, erealDomBot]
  · let S := {y : (Fin 1 → ℝ) //
      y ∈ erealDomBot (fun _ : Fin 1 → ℝ => (⊤ : EReal)) ∧
        y ∈ erealDom (convexConjugateInner (fun _ : Fin 1 → ℝ => (⊥ : EReal)))}
    have htop : ∀ y : Fin 1 → ℝ,
        convexConjugateInner (fun _ : Fin 1 → ℝ => (⊥ : EReal)) y = (⊤ : EReal) := by
      intro y
      unfold convexConjugateInner
      refine top_le_iff.mp ?_
      refine le_iSup_of_le ⟨0, by simp [erealDom]⟩ ?_
      simp
    haveI : IsEmpty S := by
      refine ⟨?_⟩
      intro y
      have : y.1 ∉ erealDom (convexConjugateInner (fun _ : Fin 1 → ℝ => (⊥ : EReal))) := by
        simpa [erealDom, htop y.1]
      exact this y.2.2
    simp [S]

lemma helperForProposition_38_5_6_improper_existence_counterexample :
    let f : (Fin 1 → ℝ) → EReal := fun _ => (⊤ : EReal)
    let g : (Fin 1 → ℝ) → EReal := fun _ => (⊥ : EReal)
    IsERealConvex f ∧
      IsERealConvex (fun y => -g y) ∧
      ((LowerSemicontinuous (fun y => -g y) ∧
          (intrinsicInterior ℝ (erealDom f) ∩
              intrinsicInterior ℝ (erealDomBot (concaveConjugateInner g))).Nonempty) ∨
        (LowerSemicontinuous f ∧
          (intrinsicInterior ℝ (erealDomBot g) ∩
              intrinsicInterior ℝ (erealDom (convexConjugateInner f))).Nonempty) ∨
        (LowerSemicontinuous f ∧ LowerSemicontinuous (fun y => -g y) ∧
          (Bornology.IsBounded (erealDom f) ∨ Bornology.IsBounded (erealDomBot g)))) ∧
      fenchelInnerProduct f g = none := by
  dsimp
  refine ⟨?_, ?_, Or.inr (Or.inr ?_), ?_⟩
  · simpa [IsERealConvex, helperForTheorem_38_1_epigraph_eq_univ] using
      (convexFunctionOn_const_top (C := (Set.univ : Set (Fin 1 → ℝ))))
  · simpa [IsERealConvex, helperForTheorem_38_1_epigraph_eq_univ] using
      (convexFunctionOn_const_top (C := (Set.univ : Set (Fin 1 → ℝ))))
  · refine ⟨?_, ?_, Or.inl ?_⟩
    · simpa using
        (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : Fin 1 → ℝ => (⊤ : EReal)))
    · simpa using
        (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : Fin 1 → ℝ => (⊤ : EReal)))
    · simpa [erealDom] using (Bornology.isBounded_empty : Bornology.IsBounded (∅ : Set (Fin 1 → ℝ)))
  · unfold fenchelInnerProduct
    have hα :
        (⨆ x : {x : Fin 1 → ℝ // x ∈ erealDom (fun _ : Fin 1 → ℝ => (⊤ : EReal))},
          concaveConjugateInner (fun _ : Fin 1 → ℝ => (⊥ : EReal)) x.1 - (⊤ : EReal)) = (⊥ : EReal) := by
      haveI : IsEmpty {x : Fin 1 → ℝ // x ∈ erealDom (fun _ : Fin 1 → ℝ => (⊤ : EReal))} := by
        refine ⟨?_⟩
        intro x
        have : x.1 ∉ erealDom (fun _ : Fin 1 → ℝ => (⊤ : EReal)) := by
          simp [erealDom]
        exact this x.2
      simp
    have hβ :
        (⨅ y : {y : Fin 1 → ℝ // y ∈ erealDomBot (fun _ : Fin 1 → ℝ => (⊥ : EReal))},
          convexConjugateInner (fun _ : Fin 1 → ℝ => (⊤ : EReal)) y.1 - (⊥ : EReal)) = (⊤ : EReal) := by
      haveI : IsEmpty {y : Fin 1 → ℝ // y ∈ erealDomBot (fun _ : Fin 1 → ℝ => (⊥ : EReal))} := by
        refine ⟨?_⟩
        intro y
        have : y.1 ∉ erealDomBot (fun _ : Fin 1 → ℝ => (⊥ : EReal)) := by
          simp [erealDomBot]
        exact this y.2
      simp
    simp [hβ]

lemma helperForProposition_38_5_6_improper_existence_not_universally_valid :
    ¬ (∀ {n : Nat} {f g : (Fin n → ℝ) → EReal}
          (_hf_convex : IsERealConvex f)
          (_hg_concave : IsERealConvex (fun y => -g y))
          (_hcond :
            (LowerSemicontinuous (fun y => -g y) ∧
                (intrinsicInterior ℝ (erealDom f) ∩
                    intrinsicInterior ℝ (erealDomBot (concaveConjugateInner g))).Nonempty) ∨
              (LowerSemicontinuous f ∧
                (intrinsicInterior ℝ (erealDomBot g) ∩
                    intrinsicInterior ℝ (erealDom (convexConjugateInner f))).Nonempty) ∨
              (LowerSemicontinuous f ∧ LowerSemicontinuous (fun y => -g y) ∧
                (Bornology.IsBounded (erealDom f) ∨ Bornology.IsBounded (erealDomBot g)))),
          ∃ c : EReal, fenchelInnerProduct f g = some c) := by
  intro hUniversal
  rcases helperForProposition_38_5_6_improper_existence_counterexample with ⟨hf, hg, hcond, hnone⟩
  rcases hUniversal (n := 1) (f := fun _ : Fin 1 → ℝ => (⊤ : EReal))
      (g := fun _ : Fin 1 → ℝ => (⊥ : EReal)) hf hg hcond with ⟨c, hc⟩
  rw [hnone] at hc
  cases hc


/-- The book-style closure of a concave `EReal`-valued function `g`, defined as `- cl(-g)` where
`cl` is `erealFunctionClosure`. -/
noncomputable def erealConcaveClosure {X : Type*} [TopologicalSpace X] (g : X → EReal) : X → EReal :=
  fun x => -erealFunctionClosure (fun y => -g y) x

-- Proof sketch: Use the extremal characterization of `⟨f, g⟩` from Definition 38.5.2 and the
-- involutive conjugacy properties (for convex/concave functions) to relate the primal/dual values
-- for `(f*, g*)`, yielding `⟨f*, g*⟩ = -⟨f, g⟩`. For the "Moreover" part, replace `f` by `cl f` and
-- `g` by `cl g` (closure in the convex/concave sense), and use that conjugates are invariant under
-- closure, so the defining extremal values (hence the inner product when it exists) are unchanged.
lemma helperForLemma_38_6_fStar_properConvexFunctionOn {n : Nat}
    {f : (Fin n → ℝ) → EReal}
    (hf_proper : IsProperEReal f)
    (hf_convex : IsERealConvex f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexConjugateInner f) := by
  have hf_proper_on : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      f hf_proper hf_convex
  have hstar : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper_on
  have hEq : convexConjugateInner f = fenchelConjugate n f := by
    funext y
    exact convexConjugateInner_eq_fenchelConjugate f y
  refine ⟨?_, ?_, ?_⟩
  · simpa [hEq] using hstar.1
  · simpa [hEq] using hstar.2.1
  · intro x hx
    simpa [hEq] using hstar.2.2 x hx

lemma helperForLemma_38_6_gStar_properConcaveFunctionOn {n : Nat}
    {g : (Fin n → ℝ) → EReal}
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y)) :
    ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) (concaveConjugateInner g) := by
  let A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (ContinuousLinearEquiv.neg ℝ : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)).toLinearEquiv
  have hneg_proper_on : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun y => -g y) :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      (fun y => -g y) hg_proper hg_concave
  have hstar : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fenchelConjugate n (fun y => -g y)) :=
    proper_fenchelConjugate_of_proper (n := n) (f := fun y => -g y) hneg_proper_on
  have hprecomp : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun y => fenchelConjugate n (fun z => -g z) (A y)) :=
    properConvexFunctionOn_precomp_linearEquiv (n := n) A hstar
  unfold ProperConcaveFunctionOn
  simpa [A, concaveConjugateInner_eq_concaveFenchelConjugate, concaveFenchelConjugate]
    using hprecomp

lemma helperForLemma_38_6_fStar_closedConvexFunction {n : Nat}
    {f : (Fin n → ℝ) → EReal} :
    ClosedConvexFunction (convexConjugateInner f) := by
  have hclosed : LowerSemicontinuous (fenchelConjugate n f) ∧ ConvexFunction (fenchelConjugate n f) :=
    fenchelConjugate_closedConvex (n := n) (f := f)
  have hEq : convexConjugateInner f = fenchelConjugate n f := by
    funext y
    exact convexConjugateInner_eq_fenchelConjugate f y
  refine ⟨?_, ?_⟩
  · simpa [hEq] using hclosed.2
  · simpa [hEq] using hclosed.1

lemma helperForLemma_38_6_gStar_closedConcaveFunction {n : Nat}
    {g : (Fin n → ℝ) → EReal} :
    ClosedConcaveFunction (concaveConjugateInner g) := by
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    (ContinuousLinearEquiv.neg ℝ : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)).toLinearMap
  have hclosed : ClosedConvexFunction (fenchelConjugate n (fun y => -g y)) := by
    have h := fenchelConjugate_closedConvex (n := n) (f := fun y => -g y)
    exact ⟨h.2, h.1⟩
  have hprecomp : ClosedConvexFunction (fun y => fenchelConjugate n (fun z => -g z) (A y)) :=
    closedConvexFunction_precomp_linearMap (A := A) hclosed
  unfold ClosedConcaveFunction
  simpa [A, concaveConjugateInner_eq_concaveFenchelConjugate, concaveFenchelConjugate]
    using hprecomp

lemma helperForLemma_38_6_isProperEReal_of_properConvexFunctionOn_univ {n : Nat}
    {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsProperEReal f := by
  refine ⟨?_, ?_⟩
  · intro x
    exact hf.2.2 x (by simp)
  · rcases (nonempty_epigraph_iff_nonempty_effectiveDomain (Set.univ : Set (Fin n → ℝ)) f).1 hf.2.1 with
      ⟨x, hx⟩
    exact ⟨x, mem_effectiveDomain_imp_ne_top hx⟩

lemma helperForLemma_38_6_isProperNeg_of_properConcaveFunctionOn_univ {n : Nat}
    {g : (Fin n → ℝ) → EReal}
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    IsProperEReal (fun y => -g y) := by
  simpa [ProperConcaveFunctionOn] using
    helperForLemma_38_6_isProperEReal_of_properConvexFunctionOn_univ
      (f := fun y => -g y) hg

lemma helperForLemma_38_6_primal_with_gStar_eq_neg_value {n : Nat}
    {f g : (Fin n → ℝ) → EReal}
    (hf_proper : IsProperEReal f)
    (hg_proper : IsProperEReal (fun y => -g y))
    (hf_convex : IsERealConvex f)
    (hg_concave : IsERealConvex (fun y => -g y)) :
    ∀ {c : EReal},
      fenchelInnerProduct f g = some c →
        fenchelPrimalInfimum f (concaveConjugateInner g) = -c := by
  intro c hc
  have hf_proper_on : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      f hf_proper hf_convex
  have hgStar_proper_on : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) (concaveConjugateInner g) :=
    helperForLemma_38_6_gStar_properConcaveFunctionOn hg_proper hg_concave
  have hAlphaText :=
    (fenchelInnerProduct_textbook_extrema_of_proper (f := f) (g := g)
      hf_proper hg_proper hc).1
  have hAlphaDom :
      c = (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
        concaveConjugateInner g x.1 - f x.1) := by
    simpa [fenchelInnerProduct_alpha_restrict_commonDom_of_proper
      (f := f) (g := g) hf_proper] using hAlphaText
  have hAlphaCore :
      (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom f},
        concaveConjugateInner g x.1 - f x.1) =
          -fenchelPrimalInfimum f (concaveConjugateInner g) := by
    simpa using
      (helperForFenchelInnerProduct_alpha_eq_neg_primalInf
        (n := n) f (concaveConjugateInner g) hf_proper_on hgStar_proper_on)
  have hneg : c = -fenchelPrimalInfimum f (concaveConjugateInner g) :=
    hAlphaDom.trans hAlphaCore
  have h := congrArg Neg.neg hneg
  simpa using h.symm

lemma helperForLemma_38_6_primal_with_fStar_eq_value {n : Nat}
    {f g : (Fin n → ℝ) → EReal}
    (hf_proper : IsProperEReal f)
    (hg_proper : IsProperEReal (fun y => -g y))
    (hf_convex : IsERealConvex f)
    (hg_concave : IsERealConvex (fun y => -g y)) :
    ∀ {c : EReal},
      fenchelInnerProduct f g = some c →
        fenchelPrimalInfimum (convexConjugateInner f) g = c := by
  intro c hc
  have hg_proper_on : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    simpa [ProperConcaveFunctionOn] using
      (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        (fun y => -g y) hg_proper hg_concave)
  have hfStar_proper_on : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexConjugateInner f) :=
    helperForLemma_38_6_fStar_properConvexFunctionOn hf_proper hf_convex
  have hBetaText :=
    (fenchelInnerProduct_textbook_extrema_of_proper (f := f) (g := g)
      hf_proper hg_proper hc).2
  have hBetaDom :
      c = (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g},
        convexConjugateInner f y.1 - g y.1) := by
    simpa [fenchelInnerProduct_beta_restrict_commonDom_of_proper
      (f := f) (g := g) hg_proper] using hBetaText
  have hBetaCore :
      (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot g},
        convexConjugateInner f y.1 - g y.1) =
          fenchelPrimalInfimum (convexConjugateInner f) g := by
    simpa using
      (helperForFenchelInnerProduct_beta_eq_primalInf
        (n := n) (convexConjugateInner f) g hfStar_proper_on hg_proper_on)
  exact (hBetaDom.trans hBetaCore).symm

lemma helperForLemma_38_6_convexConjugateInner_convexFunctionClosure_eq {n : Nat}
    (f : (Fin n → ℝ) → EReal) :
    convexConjugateInner (convexFunctionClosure f) = convexConjugateInner f := by
  funext x
  simp [convexConjugateInner_eq_fenchelConjugate,
    section16_fenchelConjugate_convexFunctionClosure_eq]

lemma helperForLemma_38_6_convexConjugateInner_biconjugate_eq_convexFunctionClosure {n : Nat}
    {f : (Fin n → ℝ) → EReal}
    (hf_convex : IsERealConvex f) :
    convexConjugateInner (convexConjugateInner f) = convexFunctionClosure f := by
  have hConvFun : ConvexFunction f := by
    simpa [IsERealConvex, ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ] using
      hf_convex
  have hInnerEq : convexConjugateInner f = fenchelConjugate n f := by
    funext y
    exact convexConjugateInner_eq_fenchelConjugate f y
  funext x
  calc
    convexConjugateInner (convexConjugateInner f) x
        = fenchelConjugate n (convexConjugateInner f) x := by
            exact convexConjugateInner_eq_fenchelConjugate (convexConjugateInner f) x
    _ = fenchelConjugate n (fenchelConjugate n f) x := by rw [hInnerEq]
    _ = convexFunctionClosure f x := by
          exact congrFun
            (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (n := n)
              (f := f) hConvFun)
            x

lemma helperForLemma_38_6_concaveConjugateInner_biconjugate_eq_concaveClosure {n : Nat}
    {g : (Fin n → ℝ) → EReal}
    (hg_concave : IsERealConvex (fun y => -g y)) :
    concaveConjugateInner (concaveConjugateInner g) = concaveClosure g := by
  have hConcFun : ConcaveFunction g := by
    simpa [ConcaveFunction, IsERealConvex, ConvexFunctionOn,
      helperForTheorem_38_1_epigraph_eq_univ] using hg_concave
  have hInnerEq : concaveConjugateInner g = concaveConjugate g := by
    funext y
    calc
      concaveConjugateInner g y = concaveFenchelConjugate g y := by
        exact concaveConjugateInner_eq_concaveFenchelConjugate g y
      _ = concaveConjugate g y := by
        simpa [concaveFenchelConjugate] using
          (helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
            (g := g) (xStar := y)).symm
  funext x
  calc
    concaveConjugateInner (concaveConjugateInner g) x
        = concaveFenchelConjugate (concaveConjugateInner g) x := by
            exact concaveConjugateInner_eq_concaveFenchelConjugate (concaveConjugateInner g) x
    _ = concaveConjugate (concaveConjugateInner g) x := by
          simpa [concaveFenchelConjugate] using
            (helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
              (g := concaveConjugateInner g) (xStar := x)).symm
    _ = concaveConjugate (concaveConjugate g) x := by rw [hInnerEq]
    _ = concaveClosure g x := by
          exact congrFun (concaveConjugate_biconjugate_eq_concaveClosure (g := g) hConcFun) x

lemma helperForLemma_38_6_concaveClosure_eq_biconjugate {n : Nat}
    {g : (Fin n → ℝ) → EReal}
    (hg_concave : IsERealConvex (fun y => -g y)) :
    concaveClosure g = concaveFenchelConjugate (concaveFenchelConjugate g) := by
  have hInnerEq : concaveConjugateInner g = concaveFenchelConjugate g := by
    funext y
    exact concaveConjugateInner_eq_concaveFenchelConjugate g y
  funext x
  calc
    concaveClosure g x = concaveConjugateInner (concaveConjugateInner g) x := by
      simpa using congrFun
        (helperForLemma_38_6_concaveConjugateInner_biconjugate_eq_concaveClosure
          (g := g) hg_concave).symm
        x
    _ = concaveFenchelConjugate (concaveConjugateInner g) x := by
      exact concaveConjugateInner_eq_concaveFenchelConjugate (concaveConjugateInner g) x
    _ = concaveFenchelConjugate (concaveFenchelConjugate g) x := by rw [hInnerEq]

lemma helperForLemma_38_6_concaveClosure_properConcaveFunctionOn {n : Nat}
    {g : (Fin n → ℝ) → EReal}
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y)) :
    ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) (concaveClosure g) := by
  let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
  have hg0_proper : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    simpa [ProperConcaveFunctionOn] using
      (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        (fun y => -g y) hg_proper hg_concave)
  have hgStar_proper : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
    simpa [gStar] using
      helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
        (n := n) (g := g) hg0_proper
  have hclosure : concaveClosure g = concaveFenchelConjugate gStar := by
    simpa [gStar] using
      helperForLemma_38_6_concaveClosure_eq_biconjugate (g := g) hg_concave
  simpa [hclosure, gStar] using
    helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
      (n := n) (g := gStar) hgStar_proper

lemma helperForLemma_38_6_concaveConjugateInner_concaveClosure_eq {n : Nat}
    {g : (Fin n → ℝ) → EReal}
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y)) :
    concaveConjugateInner (concaveClosure g) = concaveConjugateInner g := by
  let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
  have hg0_proper : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    simpa [ProperConcaveFunctionOn] using
      (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        (fun y => -g y) hg_proper hg_concave)
  have hgStar_proper : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
    simpa [gStar] using
      helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
        (n := n) (g := g) hg0_proper
  have hStarEq : gStar = concaveConjugateInner g := by
    funext x
    simpa [gStar] using
      (concaveConjugateInner_eq_concaveFenchelConjugate g x).symm
  have hgStar_closed : ClosedConcaveFunction gStar := by
    simpa [hStarEq] using
      (helperForLemma_38_6_gStar_closedConcaveFunction (g := g))
  have hclosure : concaveClosure g = concaveFenchelConjugate gStar := by
    simpa [gStar] using
      helperForLemma_38_6_concaveClosure_eq_biconjugate (g := g) hg_concave
  funext x
  calc
    concaveConjugateInner (concaveClosure g) x
        = concaveFenchelConjugate (concaveClosure g) x := by
            exact concaveConjugateInner_eq_concaveFenchelConjugate (concaveClosure g) x
    _ = concaveFenchelConjugate (concaveFenchelConjugate gStar) x := by
          simp [hclosure]
    _ = gStar x := by
          simpa using
            helperForTheorem_31_1_concave_biconjugate_eq_of_closedConcave
              (n := n) (g := gStar) hgStar_closed hgStar_proper x
    _ = concaveConjugateInner g x := by
          simpa [gStar] using
            (concaveConjugateInner_eq_concaveFenchelConjugate g x).symm

lemma helperForLemma_38_6_convexClosure_properConvexFunctionOn {n : Nat}
    {f : (Fin n → ℝ) → EReal}
    (hf_proper : IsProperEReal f)
    (hf_convex : IsERealConvex f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure f) := by
  have hf_proper_on : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      f hf_proper hf_convex
  exact (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
    (f := f) hf_proper_on).1.2

lemma helperForLemma_38_6_fStar_isProperEReal {n : Nat}
    {f : (Fin n → ℝ) → EReal}
    (hf_proper : IsProperEReal f)
    (hf_convex : IsERealConvex f) :
    IsProperEReal (convexConjugateInner f) := by
  exact helperForLemma_38_6_isProperEReal_of_properConvexFunctionOn_univ
    (helperForLemma_38_6_fStar_properConvexFunctionOn hf_proper hf_convex)

lemma helperForLemma_38_6_gStar_isProperNeg {n : Nat}
    {g : (Fin n → ℝ) → EReal}
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y)) :
    IsProperEReal (fun y => -(concaveConjugateInner g y)) := by
  exact helperForLemma_38_6_isProperNeg_of_properConcaveFunctionOn_univ
    (helperForLemma_38_6_gStar_properConcaveFunctionOn hg_proper hg_concave)

lemma helperForLemma_38_6_convexClosure_isProperEReal {n : Nat}
    {f : (Fin n → ℝ) → EReal}
    (hf_proper : IsProperEReal f)
    (hf_convex : IsERealConvex f) :
    IsProperEReal (convexFunctionClosure f) := by
  exact helperForLemma_38_6_isProperEReal_of_properConvexFunctionOn_univ
    (helperForLemma_38_6_convexClosure_properConvexFunctionOn hf_proper hf_convex)

lemma helperForLemma_38_6_concaveClosure_isProperNeg {n : Nat}
    {g : (Fin n → ℝ) → EReal}
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y)) :
    IsProperEReal (fun y => -(concaveClosure g y)) := by
  exact helperForLemma_38_6_isProperNeg_of_properConcaveFunctionOn_univ
    (helperForLemma_38_6_concaveClosure_properConcaveFunctionOn hg_proper hg_concave)

/-- Lemma 38.6: Let `f` be a proper convex function on `ℝ^n`, and let `g` be a proper concave
function on `ℝ^n`. If `⟨f, g⟩` exists, then `⟨f^*, g^*⟩` exists and `⟨f^*, g^*⟩ = -⟨f, g⟩`.
Moreover, then `⟨cl f, cl g⟩` exists and coincides with `⟨f, g⟩`.

In Lean, `⟨f, g⟩` is modeled by `fenchelInnerProduct f g : Option EReal`, `f^*` by
`convexConjugateInner f`, `g^*` by `concaveConjugateInner g`, `cl f` by
`convexFunctionClosure f`, and `cl g` by `concaveClosure g`. Downstream uses in Section 38.7 are
all in this proper branch. -/
lemma fenchelInnerProduct_conjugates_eq_neg_and_closure {n : Nat}
    (f g : (Fin n → ℝ) → EReal)
    (hf_proper : IsProperEReal f)
    (hg_proper : IsProperEReal (fun y => -g y))
    (hf_convex : IsERealConvex f)
    (hg_concave : IsERealConvex (fun y => -g y)) :
    ∀ {c : EReal},
      fenchelInnerProduct f g = some c →
        fenchelInnerProduct (convexConjugateInner f) (concaveConjugateInner g) = some (-c) ∧
          fenchelInnerProduct (convexFunctionClosure f) (concaveClosure g) = some c := by
  intro c hc
  let fStar := convexConjugateInner f
  let gStar := concaveConjugateInner g
  let fCl := convexFunctionClosure f
  let gCl := concaveClosure g
  have hfPC : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      f hf_proper hf_convex
  have hgPC : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    simpa [ProperConcaveFunctionOn] using
      (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        (fun y => -g y) hg_proper hg_concave)
  have hfStarPC : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar := by
    simpa [fStar] using
      helperForLemma_38_6_fStar_properConvexFunctionOn hf_proper hf_convex
  have hgStarPC : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
    simpa [gStar] using
      helperForLemma_38_6_gStar_properConcaveFunctionOn hg_proper hg_concave
  have hfClPC : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fCl := by
    simpa [fCl] using
      helperForLemma_38_6_convexClosure_properConvexFunctionOn hf_proper hf_convex
  have hgClPC : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gCl := by
    simpa [gCl] using
      helperForLemma_38_6_concaveClosure_properConcaveFunctionOn hg_proper hg_concave
  have hfStarStar : convexConjugateInner fStar = fCl := by
    simpa [fStar, fCl] using
      helperForLemma_38_6_convexConjugateInner_biconjugate_eq_convexFunctionClosure hf_convex
  have hgStarStar : concaveConjugateInner gStar = gCl := by
    simpa [gStar, gCl] using
      helperForLemma_38_6_concaveConjugateInner_biconjugate_eq_concaveClosure hg_concave
  have hfClStar : convexConjugateInner fCl = fStar := by
    simpa [fCl, fStar] using
      helperForLemma_38_6_convexConjugateInner_convexFunctionClosure_eq f
  have hgClStar : concaveConjugateInner gCl = gStar := by
    simpa [gCl, gStar] using
      helperForLemma_38_6_concaveConjugateInner_concaveClosure_eq hg_proper hg_concave
  have hfStarFenchel : fenchelConjugate n fStar = fCl := by
    calc
      fenchelConjugate n fStar = convexConjugateInner fStar := by
        funext x
        exact (convexConjugateInner_eq_fenchelConjugate fStar x).symm
      _ = fCl := hfStarStar
  have hfFenchel : fenchelConjugate n f = fStar := by
    funext x
    exact (convexConjugateInner_eq_fenchelConjugate f x).symm
  have hgStarFenchel : concaveFenchelConjugate gStar = gCl := by
    calc
      concaveFenchelConjugate gStar = concaveConjugateInner gStar := by
        funext x
        exact (concaveConjugateInner_eq_concaveFenchelConjugate gStar x).symm
      _ = gCl := hgStarStar
  have hgFenchel : concaveFenchelConjugate g = gStar := by
    funext x
    exact (concaveConjugateInner_eq_concaveFenchelConjugate g x).symm
  have hP_f_gStar : fenchelPrimalInfimum f gStar = -c := by
    simpa [gStar] using
      helperForLemma_38_6_primal_with_gStar_eq_neg_value
        hf_proper hg_proper hf_convex hg_concave hc
  have hP_fStar_g : fenchelPrimalInfimum fStar g = c := by
    simpa [fStar] using
      helperForLemma_38_6_primal_with_fStar_eq_value
        hf_proper hg_proper hf_convex hg_concave hc
  have hP_fCl_gStar_le :
      fenchelPrimalInfimum fCl gStar ≤ fenchelPrimalInfimum f gStar := by
    have hCommonCl :=
      helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
        (n := n) fCl gStar hfClPC hgStarPC
    have hCommon :=
      helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
        (n := n) f gStar hfPC hgStarPC
    simp only [fenchelPrimalInfimum, functionInfimumEReal, hCommonCl, hCommon]
    exact iInf_mono (fun x => EReal.sub_le_sub ((convexFunctionClosure_le_self f) x) le_rfl)
  have hP_fStar_gCl_le :
      fenchelPrimalInfimum fStar gCl ≤ fenchelPrimalInfimum fStar g := by
    have hCommonCl :=
      helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
        (n := n) fStar gCl hfStarPC hgClPC
    have hCommon :=
      helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
        (n := n) fStar g hfStarPC hgPC
    simp only [fenchelPrimalInfimum, functionInfimumEReal, hCommonCl, hCommon]
    exact iInf_mono (fun x =>
      EReal.sub_le_sub le_rfl (helperForCorollary_6_30_3_self_le_concaveClosure g x))
  have hP_fCl_gStar_ge : -c ≤ fenchelPrimalInfimum fCl gStar := by
    have hWeak := helperForTheorem_31_1_primal_ge_dual fStar g hfStarPC hgPC
    have hDual :=
      helperForTheorem_31_1_dual_eq_neg_primal_of_conjugate_pair fStar g hfStarPC hgPC
    have hneg : -fenchelPrimalInfimum fCl gStar ≤ c := by
      calc
        -fenchelPrimalInfimum fCl gStar = fenchelDualSupremum (n := n) fStar g := by
          simpa [hfStarFenchel, hgFenchel] using hDual.symm
        _ ≤ fenchelPrimalInfimum fStar g := hWeak
        _ = c := hP_fStar_g
    rw [← EReal.neg_le_neg_iff]
    simpa using hneg
  have hP_fStar_gCl_neg_eq : -fenchelPrimalInfimum fStar gCl = -c := by
    have hWeak := helperForTheorem_31_1_primal_ge_dual f gStar hfPC hgStarPC
    have hDual :=
      helperForTheorem_31_1_dual_eq_neg_primal_of_conjugate_pair f gStar hfPC hgStarPC
    have hUpper : -fenchelPrimalInfimum fStar gCl ≤ -c := by
      calc
        -fenchelPrimalInfimum fStar gCl = fenchelDualSupremum (n := n) f gStar := by
          simpa [hfFenchel, hgStarFenchel] using hDual.symm
        _ ≤ fenchelPrimalInfimum f gStar := hWeak
        _ = -c := hP_f_gStar
    have hLower : -c ≤ -fenchelPrimalInfimum fStar gCl := by
      apply EReal.neg_le_neg_iff.mpr
      exact hP_fStar_gCl_le.trans_eq hP_fStar_g
    exact le_antisymm hUpper hLower
  have hP_fCl_gStar_eq : fenchelPrimalInfimum fCl gStar = -c := by
    exact le_antisymm (hP_fCl_gStar_le.trans_eq hP_f_gStar) hP_fCl_gStar_ge
  have hfStarStarPC :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (convexConjugateInner fStar) := by
    rw [hfStarStar]
    exact hfClPC
  have hgStarStarPC :
      ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ))
        (concaveConjugateInner gStar) := by
    rw [hgStarStar]
    exact hgClPC
  have hAlphaStar :
      (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom fStar},
        concaveConjugateInner gStar x.1 - fStar x.1) = -c := by
    calc
      _ = -fenchelPrimalInfimum fStar (concaveConjugateInner gStar) :=
        helperForFenchelInnerProduct_alpha_eq_neg_primalInf
          fStar (concaveConjugateInner gStar) hfStarPC hgStarStarPC
      _ = -fenchelPrimalInfimum fStar gCl := by rw [hgStarStar]
      _ = -c := hP_fStar_gCl_neg_eq
  have hBetaStar :
      (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot gStar},
        convexConjugateInner fStar y.1 - gStar y.1) = -c := by
    calc
      _ = fenchelPrimalInfimum (convexConjugateInner fStar) gStar :=
        helperForFenchelInnerProduct_beta_eq_primalInf
          (convexConjugateInner fStar) gStar hfStarStarPC hgStarPC
      _ = fenchelPrimalInfimum fCl gStar := by rw [hfStarStar]
      _ = -c := hP_fCl_gStar_eq
  have hAlphaCl :
      (⨆ x : {x : (Fin n → ℝ) // x ∈ erealDom fCl},
        concaveConjugateInner gCl x.1 - fCl x.1) = c := by
    rw [hgClStar]
    calc
      _ = -fenchelPrimalInfimum fCl gStar :=
        helperForFenchelInnerProduct_alpha_eq_neg_primalInf fCl gStar hfClPC hgStarPC
      _ = c := by rw [hP_fCl_gStar_eq]; simp
  have hBetaCl :
      (⨅ y : {y : (Fin n → ℝ) // y ∈ erealDomBot gCl},
        convexConjugateInner fCl y.1 - gCl y.1) = c := by
    rw [hfClStar]
    calc
      _ = fenchelPrimalInfimum fStar gCl :=
        helperForFenchelInnerProduct_beta_eq_primalInf fStar gCl hfStarPC hgClPC
      _ = c := by
        have := congrArg Neg.neg hP_fStar_gCl_neg_eq
        simpa using this
  constructor
  · change fenchelInnerProduct fStar gStar = some (-c)
    unfold fenchelInnerProduct
    rw [hAlphaStar, hBetaStar]
    simp
  · change fenchelInnerProduct fCl gCl = some c
    unfold fenchelInnerProduct
    rw [hAlphaCl, hBetaCl]
    simp

lemma intrinsicInterior_erealDomBot_concaveClosure_eq {n : Nat}
    (g : (Fin n → ℝ) → EReal)
    (hg_proper : IsProperEReal (fun x => -g x))
    (hg_concave : IsERealConvex (fun x => -g x)) :
    intrinsicInterior ℝ (erealDomBot (concaveClosure g)) =
      intrinsicInterior ℝ (erealDomBot g) := by
  let negG : (Fin n → ℝ) → EReal := fun x => -g x
  have hnegPC : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) negG :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      negG hg_proper hg_concave
  have hriE :=
    (convexFunctionClosure_effectiveDomain_subset_relativeBoundary_and_same_closure_ri_dim
      hnegPC).2.2.2.1
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hpre (C : Set (Fin n → ℝ)) :
      e.symm '' C = (fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [e] using hx
    · intro hy
      refine ⟨e y, ?_, by simp⟩
      simpa [e] using hy
  have hriRaw :
      euclideanRelativeInterior n
          (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (convexFunctionClosure negG)) =
        euclideanRelativeInterior n
          (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) negG) := by
    rw [hpre, hpre]
    simpa [e, negG] using hriE
  have hriFin :
      euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure negG)) =
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) negG) := by
    unfold euclideanRelativeInterior_fin
    simpa [e] using congrArg (fun C => e '' C) hriRaw
  rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior,
    helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] at hriFin
  have hconv : ConvexFunction negG := by
    simpa [negG, IsERealConvex, ConvexFunctionOn,
      helperForTheorem_38_1_epigraph_eq_univ] using hg_concave
  have hclEq : convexClosure negG = convexFunctionClosure negG := by
    calc
      convexClosure negG = clConv n negG :=
        helperForTheorem_6_30_3_convexClosure_eq_clConv negG hconv
      _ = fenchelConjugate n (fenchelConjugate n negG) := by
        symm
        exact fenchelConjugate_biconjugate_eq_clConv (n := n) (f := negG)
      _ = convexFunctionClosure negG :=
        section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
          (n := n) (f := negG) hconv
  have hnegIff (a : EReal) : (⊥ : EReal) < -a ↔ a < (⊤ : EReal) := by
    simp [bot_lt_iff_ne_bot]
  have hdomCl :
      erealDomBot (concaveClosure g) =
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure negG) := by
    ext x
    simp only [erealDomBot, Set.mem_setOf_eq, effectiveDomain_eq, Set.mem_univ, true_and,
      concaveClosure_eq_neg_convexClosure_neg, hnegIff]
    change convexClosure negG x < (⊤ : EReal) ↔ convexFunctionClosure negG x < ⊤
    rw [hclEq]
  have hdom :
      erealDomBot g = effectiveDomain (Set.univ : Set (Fin n → ℝ)) negG := by
    ext x
    simp only [erealDomBot, Set.mem_setOf_eq, effectiveDomain_eq, Set.mem_univ, true_and]
    simpa [negG] using hnegIff (-g x)
  rw [hdomCl, hdom]
  exact hriFin

/-- Relative-interior qualification for `h` and `g` makes the Fenchel inner product of `h`
with the concave conjugate of `g` exist; no closedness assumption on `g` is needed. -/
lemma fenchelInnerProduct_with_concaveConjugate_exists_of_ri
    {n : Nat} (h g : (Fin n → ℝ) → EReal)
    (hh_proper : IsProperEReal h) (hh_convex : IsERealConvex h)
    (hg_proper : IsProperEReal (fun x => -g x))
    (hg_concave : IsERealConvex (fun x => -g x))
    (hri :
      (intrinsicInterior ℝ (erealDom h) ∩
        intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    ∃ c : EReal, fenchelInnerProduct h (concaveConjugateInner g) = some c := by
  let gStar := concaveConjugateInner g
  have hgStarPC : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
    simpa [gStar] using
      helperForLemma_38_6_gStar_properConcaveFunctionOn hg_proper hg_concave
  have hgStarProper : IsProperEReal (fun x => -gStar x) :=
    helperForLemma_38_6_isProperNeg_of_properConcaveFunctionOn_univ hgStarPC
  have hgStarClosed : ClosedConcaveFunction gStar := by
    simpa [gStar] using (helperForLemma_38_6_gStar_closedConcaveFunction (g := g))
  have hgStarConcave : IsERealConvex (fun x => -gStar x) := by
    simpa [ClosedConcaveFunction, IsERealConvex, ConvexFunction, ConvexFunctionOn,
      helperForTheorem_38_1_epigraph_eq_univ] using hgStarClosed.1
  have hbiconj : concaveConjugateInner gStar = concaveClosure g := by
    simpa [gStar] using
      helperForLemma_38_6_concaveConjugateInner_biconjugate_eq_concaveClosure
        (g := g) hg_concave
  have hriClosure :=
    intrinsicInterior_erealDomBot_concaveClosure_eq g hg_proper hg_concave
  have hriStar :
      (intrinsicInterior ℝ (erealDom h) ∩
        intrinsicInterior ℝ (erealDomBot (concaveConjugateInner gStar))).Nonempty := by
    rw [hbiconj, hriClosure]
    exact hri
  exact fenchelInnerProduct_exists_of_closed_ri_or_bounded_domain
    (f := h) (g := gStar) hh_convex hgStarConcave hh_proper hgStarProper
    (Or.inl ⟨hgStarClosed.2, hriStar⟩)

/-- Lemma 38.6, current proper branch: let `f` be a proper convex function on `ℝ^n`, and let `g` be a proper concave
function on `ℝ^n`. If `⟨f, g⟩` exists, then `⟨f^*, g^*⟩` exists and `⟨f^*, g^*⟩ = -⟨f, g⟩`.
Moreover, then `⟨cl f, cl g⟩` exists and coincides with `⟨f, g⟩`.

In Lean, `⟨f, g⟩` is modeled by `fenchelInnerProduct f g : Option EReal`, `f^*` by
`convexConjugateInner f`, `g^*` by `concaveConjugateInner g`, `cl f` by
`convexFunctionClosure f`, and `cl g` by `concaveClosure g`. Downstream uses in Section 38.7 are
all in this proper branch.  The original lemma also discusses improper convex/concave functions;
that additional case split is not claimed by this proper-branch declaration. -/


lemma helperForTheorem_38_7_hqual_to_fin_relativeInteriors
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (hqual :
      ∃ u : Fin m → ℝ,
        u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
          (intrinsicInterior ℝ (erealDom (fun x : Fin n → ℝ => F u x)) ∩
              intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    ∃ u : Fin m → ℝ, ∃ x : Fin n → ℝ,
      u ∈ euclideanRelativeInterior_fin m (erealDom f) ∩
          euclideanRelativeInterior_fin m (bifunctionDom F) ∧
        x ∈ euclideanRelativeInterior_fin n (erealDom (fun y : Fin n → ℝ => F u y)) ∩
          euclideanRelativeInterior_fin n (erealDomBot g) := by
  rcases hqual with ⟨u, hu, x, hxF, hxg⟩
  refine ⟨u, x, ?_, ?_⟩
  · simpa only [
      helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] using hu
  · simpa only [
      helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] using
        And.intro hxF hxg

/-- The Euclidean packed graph domain has the expected fixed-u fibers and projection.
This is the set-theoretic bridge needed before applying Theorems 6.6 and 6.8. -/
lemma helperForTheorem_38_7_packedGraphDomain_fiber_projection
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    let eMN := EuclideanSpace.equiv (ι := Fin (m + n)) (𝕜 := ℝ)
    let eM := EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
    let eN := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
    let C : Set (EuclideanSpace ℝ (Fin (m + n))) :=
      eMN.symm ''
        {z : Fin (m + n) → ℝ |
          F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j)) < ⊤}
    let append :
        EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin (m + n)) :=
      fun u x => eMN.symm (Fin.append (eM u) (eN x))
    let Cu : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin n)) :=
      fun u => {x | append u x ∈ C}
    let D : Set (EuclideanSpace ℝ (Fin m)) := {u | (Cu u).Nonempty}
    (∀ u : Fin m → ℝ, Cu (eM.symm u) = eN.symm '' erealDom (F u)) ∧
      D = eM.symm '' bifunctionDom F := by
  classical
  intro eMN eM eN C append Cu D
  constructor
  · intro u
    ext x
    constructor
    · intro hx
      refine ⟨eN x, ?_, by simp [eN]⟩
      simpa [Cu, append, C, eMN, eM, eN, erealDom] using hx
    · rintro ⟨x, hx, rfl⟩
      simpa [Cu, append, C, eMN, eM, eN, erealDom] using hx
  · ext u
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨eM u, ?_, by simp [eM]⟩
      refine ⟨eN x, ?_⟩
      have hx' : F (eM u) (eN x) < ⊤ := by
        simpa [Cu, append, C, eMN, eM, eN] using hx
      exact ne_of_lt hx'
    · rintro ⟨u, hu, rfl⟩
      rcases hu with ⟨x, hx⟩
      refine ⟨eN.symm x, ?_⟩
      simpa [Cu, append, C, eMN, eM, eN, lt_top_iff_ne_top] using hx

/-- Intersecting the packed graph projection with the transported domain of `f` is exactly the
transport of the common base domain. -/
lemma helperForTheorem_38_7_mem_imageDom_iff_exists_sum_lt_top
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (x : Fin n → ℝ) :
    x ∈ erealDom (bifunctionImageRaw F f) ↔
      ∃ u : Fin m → ℝ, f u + F u x < (⊤ : EReal) := by
  simp only [erealDom, bifunctionImageRaw, Set.mem_setOf_eq, iInf_lt_top]

/-- The `x`-projection of the packed effective domain of `(u,x) ↦ f u + F u x` is the
Euclidean transport of the effective domain of `bifunctionImageRaw F f`. -/
lemma helperForTheorem_38_7_packedSumDomain_xProjection
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) :
    let eMN := EuclideanSpace.equiv (ι := Fin (m + n)) (𝕜 := ℝ)
    let eM := EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
    let eN := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
    let C : Set (EuclideanSpace ℝ (Fin (m + n))) :=
      eMN.symm ''
        {z : Fin (m + n) → ℝ |
          f (fun i => z (Fin.castAdd n i)) +
              F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j)) < ⊤}
    let append :
        EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin (m + n)) :=
      fun u x => eMN.symm (Fin.append (eM u) (eN x))
    let projX : Set (EuclideanSpace ℝ (Fin n)) :=
      {x | ∃ u : EuclideanSpace ℝ (Fin m), append u x ∈ C}
    projX = eN.symm '' erealDom (bifunctionImageRaw F f) := by
  classical
  intro eMN eM eN C append projX
  ext x
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨eN x, ?_, by simp [eN]⟩
    rw [helperForTheorem_38_7_mem_imageDom_iff_exists_sum_lt_top]
    refine ⟨eM u, ?_⟩
    simpa [append, C, eMN, eM, eN] using hu
  · rintro ⟨x0, hx0, rfl⟩
    rw [helperForTheorem_38_7_mem_imageDom_iff_exists_sum_lt_top] at hx0
    rcases hx0 with ⟨u0, hu0⟩
    refine ⟨eM.symm u0, ?_⟩
    simpa [append, C, eMN, eM, eN] using hu0

/-- The graph-domain part of the qualification lifts to the relative interior of the packed
graph domain.  This isolates the Theorem 6.8 step needed before intersecting with the lifted
domain of `f`. -/
lemma helperForTheorem_38_7_graphQualification_lifts_to_packedRi
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hqual :
      ∃ u : Fin m → ℝ,
        u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
          (intrinsicInterior ℝ (erealDom (fun x : Fin n → ℝ => F u x)) ∩
              intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    let eMN := EuclideanSpace.equiv (ι := Fin (m + n)) (𝕜 := ℝ)
    let eM := EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
    let eN := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
    let C : Set (EuclideanSpace ℝ (Fin (m + n))) :=
      eMN.symm ''
        {z : Fin (m + n) → ℝ |
          F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j)) < ⊤}
    ∃ u : Fin m → ℝ, ∃ x : Fin n → ℝ,
      eMN.symm (Fin.append u x) ∈ euclideanRelativeInterior (m + n) C ∧
        u ∈ euclideanRelativeInterior_fin m (erealDom f) ∧
        x ∈ euclideanRelativeInterior_fin n (erealDomBot g) := by
  classical
  intro eMN eM eN C
  rcases helperForTheorem_38_7_hqual_to_fin_relativeInteriors F f g hqual with
    ⟨u, x, hu, hx⟩
  let graphg : (Fin (m + n) → ℝ) → EReal :=
    fun z => F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
  let pairMap : (Fin (m + n) → ℝ) →ₗ[ℝ]
      (Fin m → ℝ) × (Fin n → ℝ) :=
    (projXLinearMap (n := m) (m := n)).prod (projLamLinearMap (n := m) (m := n))
  have hgraph_convex : IsERealConvex graphg := by
    simpa [graphg, pairMap, projXLinearMap, projLamLinearMap] using
      helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := pairMap) (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2)
        hF_convex
  have hgraph_proper : IsProperEReal graphg := by
    constructor
    · intro z
      simpa [graphg] using hF_proper.1
        ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))
    · rcases hF_proper.2 with ⟨p, hp⟩
      refine ⟨Fin.append p.1 p.2, ?_⟩
      simpa [graphg]
  have hgraph_pc :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) graphg :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      graphg hgraph_proper hgraph_convex
  have hraw_conv : Convex ℝ {z : Fin (m + n) → ℝ | graphg z < ⊤} := by
    have heq :
        {z : Fin (m + n) → ℝ | graphg z < ⊤} =
          effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ)) graphg := by
      ext z
      simp [effectiveDomain_eq, lt_top_iff_ne_top]
    rw [heq]
    exact effectiveDomain_convex hgraph_pc.1
  have hCconv : Convex ℝ C := by
    simpa [C, graphg] using hraw_conv.linear_image eMN.symm.toLinearMap
  let append :
      EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℝ (Fin (m + n)) :=
    fun u x => eMN.symm (Fin.append (eM u) (eN x))
  let Cu : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun u => {x | append u x ∈ C}
  let D : Set (EuclideanSpace ℝ (Fin m)) := {u | (Cu u).Nonempty}
  have hfiber_projection := helperForTheorem_38_7_packedGraphDomain_fiber_projection F
  have hCu : Cu (eM.symm u) = eN.symm '' erealDom (F u) := by
    simpa [append, Cu, D, C, eMN, eM, eN] using hfiber_projection.1 u
  have hD : D = eM.symm '' bifunctionDom F := by
    simpa [append, Cu, D, C, eMN, eM, eN] using hfiber_projection.2
  have huE : eM.symm u ∈ euclideanRelativeInterior m D := by
    rw [hD]
    exact (mem_euclideanRelativeInterior_fin_iff
      (n := m) (C := bifunctionDom F) (x := u)).1 hu.2
  have hxE : eN.symm x ∈ euclideanRelativeInterior n (Cu (eM.symm u)) := by
    rw [hCu]
    exact (mem_euclideanRelativeInterior_fin_iff
      (n := n) (C := erealDom (F u)) (x := x)).1 hx.1
  have hsection :=
    euclideanRelativeInterior_mem_iff_relativeInterior_section
      (m := m) (p := n) C hCconv (eM.symm u) (eN.symm x)
  refine ⟨u, x, ?_, hu.1, hx.2⟩
  exact hsection.2 ⟨huE, hxE⟩

/-- The same qualification point lies in the relative interior of the intersection of the packed
graph domain and the cylinder over `dom f`. -/
lemma helperForTheorem_38_7_qualification_lifts_to_packedDomainIntersectionRi
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hqual :
      ∃ u : Fin m → ℝ,
        u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
          (intrinsicInterior ℝ (erealDom (fun x : Fin n → ℝ => F u x)) ∩
              intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    let eMN := EuclideanSpace.equiv (ι := Fin (m + n)) (𝕜 := ℝ)
    let Cgraph : Set (EuclideanSpace ℝ (Fin (m + n))) :=
      eMN.symm ''
        {z : Fin (m + n) → ℝ |
          F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j)) < ⊤}
    let Cliftf : Set (EuclideanSpace ℝ (Fin (m + n))) :=
      eMN.symm '' {z : Fin (m + n) → ℝ | f (fun i => z (Fin.castAdd n i)) < ⊤}
    ∃ u : Fin m → ℝ, ∃ x : Fin n → ℝ,
      eMN.symm (Fin.append u x) ∈
        euclideanRelativeInterior (m + n) (Cgraph ∩ Cliftf) ∧
      x ∈ euclideanRelativeInterior_fin n (erealDomBot g) := by
  classical
  intro eMN Cgraph Cliftf
  rcases helperForTheorem_38_7_graphQualification_lifts_to_packedRi
      F f g hF_proper hF_convex hqual with ⟨u, x, hzGraph, huF, hxg⟩
  let eM := EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let Cf : Set (EuclideanSpace ℝ (Fin m)) := eM.symm '' erealDom f
  let A : EuclideanSpace ℝ (Fin (m + n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    eM.symm.toLinearMap.comp
      ((projXLinearMap (n := m) (m := n)).comp eMN.toLinearMap)
  have hf_pc : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      f hf_proper hf_convex
  have hdomf_conv : Convex ℝ (erealDom f) := by
    have heq : erealDom f = effectiveDomain (Set.univ : Set (Fin m → ℝ)) f := by
      ext y
      simp [erealDom, effectiveDomain_eq, lt_top_iff_ne_top]
    rw [heq]
    exact effectiveDomain_convex hf_pc.1
  have hCfconv : Convex ℝ Cf := by
    exact hdomf_conv.linear_image eM.symm.toLinearMap
  have huE : eM.symm u ∈ euclideanRelativeInterior m Cf := by
    exact (mem_euclideanRelativeInterior_fin_iff
      (n := m) (C := erealDom f) (x := u)).1 huF
  have hAz : A (eMN.symm (Fin.append u x)) = eM.symm u := by
    simp [A, eM, eMN, projXLinearMap]
  have hpre_nonempty :
      (A ⁻¹' euclideanRelativeInterior m Cf).Nonempty := by
    exact ⟨eMN.symm (Fin.append u x), by simpa [hAz] using huE⟩
  have hpre := euclideanRelativeInterior_preimage_linearMap_eq_and_closure_preimage
    (n := m + n) (m := m) A Cf hCfconv hpre_nonempty
  have hzPre : eMN.symm (Fin.append u x) ∈
      euclideanRelativeInterior (m + n) (A ⁻¹' Cf) := by
    rw [hpre.1]
    simpa [hAz] using huE
  have hClift : Cliftf = A ⁻¹' Cf := by
    ext z
    constructor
    · rintro ⟨z0, hz0, rfl⟩
      refine ⟨fun i => z0 (Fin.castAdd n i), ?_, ?_⟩
      · simpa [erealDom] using hz0
      · simp [A, Cf, eM, eMN, projXLinearMap]
    · rintro ⟨u0, hu0, hAu⟩
      refine ⟨eMN z, ?_, by simp [eMN]⟩
      have huEq : u0 = fun i => (eMN z) (Fin.castAdd n i) := by
        apply eM.symm.injective
        simpa [A, eM, eMN, projXLinearMap] using hAu
      simpa [erealDom, huEq] using hu0
  have hzLift : eMN.symm (Fin.append u x) ∈
      euclideanRelativeInterior (m + n) Cliftf := by
    rw [hClift]
    exact hzPre
  have hCliftconv : Convex ℝ Cliftf := by
    rw [hClift]
    exact hCfconv.linear_preimage A
  have hCgraphconv : Convex ℝ Cgraph := by
    let graphg : (Fin (m + n) → ℝ) → EReal :=
      fun z => F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
    let pairMap : (Fin (m + n) → ℝ) →ₗ[ℝ]
        (Fin m → ℝ) × (Fin n → ℝ) :=
      (projXLinearMap (n := m) (m := n)).prod (projLamLinearMap (n := m) (m := n))
    have hgconv : IsERealConvex graphg := by
      simpa [graphg, pairMap, projXLinearMap, projLamLinearMap] using
        helperForTheorem_38_4_isERealConvex_precomp_linearMap (A := pairMap) hF_convex
    have hgproper : IsProperEReal graphg := by
      constructor
      · intro z
        simpa [graphg] using hF_proper.1
          ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))
      · rcases hF_proper.2 with ⟨p, hp⟩
        exact ⟨Fin.append p.1 p.2, by simpa [graphg]⟩
    have hgpc :=
      helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        graphg hgproper hgconv
    have hraw : Convex ℝ {z : Fin (m + n) → ℝ | graphg z < ⊤} := by
      have heq : {z : Fin (m + n) → ℝ | graphg z < ⊤} =
          effectiveDomain Set.univ graphg := by
        ext z
        simp [effectiveDomain_eq, lt_top_iff_ne_top]
      rw [heq]
      exact effectiveDomain_convex hgpc.1
    simpa [Cgraph, graphg] using hraw.linear_image eMN.symm.toLinearMap
  let family : Fin 2 → Set (EuclideanSpace ℝ (Fin (m + n))) :=
    fun i => if i = 0 then Cgraph else Cliftf
  have hzGraph' : eMN.symm (Fin.append u x) ∈
      euclideanRelativeInterior (m + n) Cgraph := by
    simpa [Cgraph, eMN] using hzGraph
  have hfamilyConv : ∀ i, Convex ℝ (family i) := by
    intro i
    fin_cases i
    · simpa [family] using hCgraphconv
    · simpa [family] using hCliftconv
  have hfamilyRi : (⋂ i, euclideanRelativeInterior (m + n) (family i)).Nonempty := by
    refine ⟨eMN.symm (Fin.append u x), ?_⟩
    rw [iInter_fin_two_eq_inter]
    exact ⟨by simpa [family] using hzGraph', by simpa [family] using hzLift⟩
  have hriEq := euclideanRelativeInterior_iInter_eq_iInter_relativeInterior_of_finite
    (m + n) family hfamilyConv hfamilyRi
  refine ⟨u, x, ?_, hxg⟩
  have hzI : eMN.symm (Fin.append u x) ∈
      ⋂ i, euclideanRelativeInterior (m + n) (family i) := by
    rw [iInter_fin_two_eq_inter]
    exact ⟨by simpa [family] using hzGraph', by simpa [family] using hzLift⟩
  have hInter : (⋂ i, family i) = Cgraph ∩ Cliftf := by
    simpa [family] using iInter_fin_two_eq_inter family
  rw [← hInter, hriEq]
  exact hzI

/-- The full relative-interior consequence of the §38.7 qualification: the same `x` furnished
by the qualified slice belongs to both `ri (dom (Ff))` and `ri (domBot g)`. -/
lemma helperForTheorem_38_7_qualification_implies_imageDom_inter_domBot_ri_nonempty
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hqual :
      ∃ u : Fin m → ℝ,
        u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
          (intrinsicInterior ℝ (erealDom (fun x : Fin n → ℝ => F u x)) ∩
              intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    (intrinsicInterior ℝ (erealDom (bifunctionImageRaw F f)) ∩
      intrinsicInterior ℝ (erealDomBot g)).Nonempty := by
  classical
  let eMN := EuclideanSpace.equiv (ι := Fin (m + n)) (𝕜 := ℝ)
  let eN := EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let Cgraph : Set (EuclideanSpace ℝ (Fin (m + n))) :=
    eMN.symm ''
      {z : Fin (m + n) → ℝ |
        F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j)) < ⊤}
  let Cliftf : Set (EuclideanSpace ℝ (Fin (m + n))) :=
    eMN.symm '' {z : Fin (m + n) → ℝ | f (fun i => z (Fin.castAdd n i)) < ⊤}
  let Csum : Set (EuclideanSpace ℝ (Fin (m + n))) :=
    eMN.symm ''
      {z : Fin (m + n) → ℝ |
        f (fun i => z (Fin.castAdd n i)) +
          F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j)) < ⊤}
  rcases helperForTheorem_38_7_qualification_lifts_to_packedDomainIntersectionRi
      F f g hF_proper hF_convex hf_proper hf_convex hqual with
    ⟨u, x, hzInter, hxg⟩
  have hAddDom : ∀ (u0 : Fin m → ℝ) (x0 : Fin n → ℝ),
      f u0 + F u0 x0 < ⊤ ↔ f u0 < ⊤ ∧ F u0 x0 < ⊤ := by
    intro u0 x0
    constructor
    · intro h
      constructor
      · rw [lt_top_iff_ne_top]
        intro hfTop
        rw [hfTop] at h
        simpa [hF_proper.1 (u0, x0)] using h
      · rw [lt_top_iff_ne_top]
        intro hFTop
        rw [hFTop] at h
        simpa [hf_proper.1 u0] using h
    · rintro ⟨hfTop, hFTop⟩
      exact EReal.add_lt_top (ne_of_lt hfTop) (ne_of_lt hFTop)
  have hDomains : Cgraph ∩ Cliftf = Csum := by
    ext z
    simp only [Cgraph, Cliftf, Csum, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨zg, hzg, hzgEq⟩, ⟨zf, hzf, hzfEq⟩⟩
      have hEq : zg = zf := by
        apply eMN.symm.injective
        exact hzgEq.trans hzfEq.symm
      subst zf
      refine ⟨zg, ?_, hzgEq⟩
      exact (hAddDom _ _).2 ⟨hzf, hzg⟩
    · rintro ⟨z0, hz0, rfl⟩
      have hzParts := (hAddDom
        (fun i => z0 (Fin.castAdd n i)) (fun j => z0 (Fin.natAdd m j))).1 hz0
      exact ⟨⟨z0, hzParts.2, rfl⟩, ⟨z0, hzParts.1, rfl⟩⟩
  have hzSum : eMN.symm (Fin.append u x) ∈
      euclideanRelativeInterior (m + n) Csum := by
    rw [← hDomains]
    simpa [Cgraph, Cliftf, eMN] using hzInter
  let liftedf : (Fin (m + n) → ℝ) → EReal :=
    fun z => f (fun i => z (Fin.castAdd n i))
  let liftedF : (Fin (m + n) → ℝ) → EReal :=
    fun z => F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
  let firstMap : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    projXLinearMap (n := m) (m := n)
  let pairMap : (Fin (m + n) → ℝ) →ₗ[ℝ]
      (Fin m → ℝ) × (Fin n → ℝ) :=
    firstMap.prod (projLamLinearMap (n := m) (m := n))
  have hlfProper : IsProperEReal liftedf := by
    constructor
    · intro z
      exact hf_proper.1 _
    · rcases hf_proper.2 with ⟨u0, hu0⟩
      exact ⟨Fin.append u0 (0 : Fin n → ℝ), by simpa [liftedf]⟩
  have hlFProper : IsProperEReal liftedF := by
    constructor
    · intro z
      simpa [liftedF] using hF_proper.1
        ((fun i => z (Fin.castAdd n i)), (fun j => z (Fin.natAdd m j)))
    · rcases hF_proper.2 with ⟨p, hp⟩
      exact ⟨Fin.append p.1 p.2, by simpa [liftedF]⟩
  have hlfConvex : IsERealConvex liftedf := by
    simpa [liftedf, firstMap, projXLinearMap] using
      helperForTheorem_38_4_isERealConvex_precomp_linearMap (A := firstMap) hf_convex
  have hlFConvex : IsERealConvex liftedF := by
    simpa [liftedF, pairMap, firstMap, projXLinearMap, projLamLinearMap] using
      helperForTheorem_38_4_isERealConvex_precomp_linearMap (A := pairMap) hF_convex
  have hlfPC :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      liftedf hlfProper hlfConvex
  have hlFPC :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      liftedF hlFProper hlFConvex
  have hsumPC : ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
      (fun z => liftedf z + liftedF z) :=
    convexFunctionOn_add_of_proper hlfPC hlFPC
  have hCsumConv : Convex ℝ Csum := by
    have hraw : Convex ℝ
        (effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
          (fun z => liftedf z + liftedF z)) := effectiveDomain_convex hsumPC
    have heq : Csum = eMN.symm ''
        effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
          (fun z => liftedf z + liftedF z) := by
      ext z
      simp [Csum, effectiveDomain_eq, liftedf, liftedF, lt_top_iff_ne_top]
    rw [heq]
    exact hraw.linear_image eMN.symm.toLinearMap
  let P : EuclideanSpace ℝ (Fin (m + n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    eN.symm.toLinearMap.comp
      ((projLamLinearMap (n := m) (m := n)).comp eMN.toLinearMap)
  have hPz : P (eMN.symm (Fin.append u x)) = eN.symm x := by
    simp [P, eN, eMN, projLamLinearMap]
  have hprojRi :=
    (euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset
      (n := m + n) (m := n) Csum hCsumConv P).1
  have hxProj : eN.symm x ∈ euclideanRelativeInterior n (P '' Csum) := by
    rw [hprojRi]
    exact ⟨eMN.symm (Fin.append u x), hzSum, hPz⟩
  have hprojEq : P '' Csum = eN.symm '' erealDom (bifunctionImageRaw F f) := by
    ext y
    constructor
    · rintro ⟨z, ⟨z0, hz0, hzEq⟩, rfl⟩
      have hzEq' : z = eMN.symm z0 := hzEq.symm
      subst z
      refine ⟨(fun j => z0 (Fin.natAdd m j)), ?_, ?_⟩
      · rw [helperForTheorem_38_7_mem_imageDom_iff_exists_sum_lt_top]
        exact ⟨(fun i => z0 (Fin.castAdd n i)), hz0⟩
      · simp [P, eMN, eN, projLamLinearMap]
    · rintro ⟨x0, hx0, rfl⟩
      rw [helperForTheorem_38_7_mem_imageDom_iff_exists_sum_lt_top] at hx0
      rcases hx0 with ⟨u0, hu0⟩
      refine ⟨eMN.symm (Fin.append u0 x0), ?_, ?_⟩
      · exact ⟨Fin.append u0 x0, by simpa, rfl⟩
      · simp [P, eMN, eN, projLamLinearMap]
  have hxImageFin : x ∈ euclideanRelativeInterior_fin n
      (erealDom (bifunctionImageRaw F f)) := by
    apply (mem_euclideanRelativeInterior_fin_iff
      (n := n) (C := erealDom (bifunctionImageRaw F f)) (x := x)).2
    rw [← hprojEq]
    exact hxProj
  refine ⟨x, ?_, ?_⟩
  · simpa only [
      helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] using hxImageFin
  · simpa only [
      helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] using hxg


/-- The qualification in Theorem 38.7 supplies a concrete point in the effective domain of the
image `Ff`.  Indeed its slice-relative-interior witness gives finite-above values of both `f u`
and `F u x`, and the defining infimum of `Ff` is bounded above by their sum.  The properness
hypotheses are retained in the interface used by Theorem 38.7, although the qualification itself
already gives the required upper finiteness. -/
lemma helperForTheorem_38_7_image_erealDom_nonempty
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (_hF_proper : IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (_hf_proper : IsProperEReal f)
    (hqual :
      ∃ u : (Fin m → ℝ),
        u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
          (intrinsicInterior ℝ (erealDom (fun x : (Fin n → ℝ) => F u x)) ∩
              intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    (erealDom (bifunctionImageRaw F f)).Nonempty := by
  rcases hqual with ⟨u, hu, x, hxF, hxg⟩
  have huf_dom : u ∈ erealDom f :=
    intrinsicInterior_subset (𝕜 := ℝ) (s := erealDom f) hu.1
  have huf_lt_top : f u < (⊤ : EReal) := by
    simpa [erealDom] using huf_dom
  have hFx_dom : x ∈ erealDom (fun y : Fin n → ℝ => F u y) :=
    intrinsicInterior_subset (𝕜 := ℝ)
      (s := erealDom (fun y : Fin n → ℝ => F u y)) hxF
  have hFx_lt_top : F u x < (⊤ : EReal) := by
    simpa [erealDom] using hFx_dom
  have hsum_lt_top : f u + F u x < (⊤ : EReal) :=
    EReal.add_lt_top (ne_of_lt huf_lt_top) (ne_of_lt hFx_lt_top)
  refine ⟨x, ?_⟩
  rw [erealDom]
  exact lt_of_le_of_lt (iInf_le (fun v : Fin m → ℝ => f v + F v x) u) hsum_lt_top

/-- Theorem 38.7's slice qualification contains the common relative-interior qualification used
by Theorem 38.4.  Together with Theorem 38.4's unconditional first conclusion this also packages
the convexity of the image `Ff` for the later Lemma 38.6 application. -/
lemma helperForTheorem_38_7_image_convex_and_base_hri
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hqual :
      ∃ u : (Fin m → ℝ),
        u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
          (intrinsicInterior ℝ (erealDom (fun x : (Fin n → ℝ) => F u x)) ∩
              intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    (intrinsicInterior ℝ (erealDom f) ∩
        intrinsicInterior ℝ (bifunctionDom F)).Nonempty ∧
      IsERealConvex (bifunctionImageRaw F f) := by
  rcases hqual with ⟨u, hu, hx⟩
  refine ⟨⟨u, hu⟩, ?_⟩
  exact (theorem38_4_image_convex_and_conjugate
    F f hF_proper hF_convex hf_proper hf_convex).1

/-- A proper convex function agrees with its closure on the intrinsic relative interior of its
effective domain, in `Fin` coordinates. -/
lemma helperForTheorem_38_7_convexFunctionClosure_eq_on_intrinsicInterior
    {n : Nat} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) {x : Fin n → ℝ}
    (hx : x ∈ intrinsicInterior ℝ
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    convexFunctionClosure f x = f x := by
  have hxFin : x ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hx
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  have hpre :
      ((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) =
        e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    ext y
    constructor
    · intro hy; exact ⟨e y, hy, by simp [e]⟩
    · rintro ⟨z, hz, rfl⟩; simpa [e] using hz
  have hxE : e.symm x ∈ euclideanRelativeInterior n
      ((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    have := (mem_euclideanRelativeInterior_fin_iff
      (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) (x := x)).1 hxFin
    simpa [e, hpre] using this
  simpa [e] using
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri hf).2
      (e.symm x) hxE

set_option synthInstance.maxHeartbeats 100000 in
/-- In the improper image branch, the common relative-interior point forces both extrema in
the Fenchel inner product with `g*` to equal `+∞`. -/
lemma helperForTheorem_38_7_improper_innerProduct_with_concaveConjugate_eq_top
    {n : Nat} (h g : (Fin n → ℝ) → EReal)
    (hh_convex : IsERealConvex h) (hh_notProper : ¬ IsProperEReal h)
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y))
    (hri : (intrinsicInterior ℝ (erealDom h) ∩
      intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    fenchelInnerProduct h (concaveConjugateInner g) = some (⊤ : EReal) := by
  let gStar := concaveConjugateInner g
  have hhConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [ConvexFunctionOn, IsERealConvex, helperForTheorem_38_1_epigraph_eq_univ] using hh_convex
  have hhNotPC : ¬ ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    intro hh
    exact hh_notProper (helperForLemma_38_6_isProperEReal_of_properConvexFunctionOn_univ hh)
  have hhImproper : ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h :=
    ⟨hhConvOn, hhNotPC⟩
  rcases hri with ⟨x, hxh, hxg⟩
  have hxhEff : x ∈ intrinsicInterior ℝ
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) := by
    simpa [erealDom, effectiveDomain_eq] using hxh
  have hxbot : h x = (⊥ : EReal) :=
    improperConvexFunctionOn_eq_bot_on_intrinsicInterior_fin hhImproper hxhEff
  let negG : (Fin n → ℝ) → EReal := fun y => -g y
  have hnegPC : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) negG :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      negG hg_proper hg_concave
  have hdomNeg : erealDomBot g =
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) negG := by
    ext z
    simp only [erealDomBot, Set.mem_setOf_eq, effectiveDomain_eq, Set.mem_univ, true_and,
      negG, bot_lt_iff_ne_bot, lt_top_iff_ne_top]
    constructor
    · intro hz hnegTop; exact hz ((EReal.neg_eq_top_iff).1 hnegTop)
    · intro hz hbot; exact hz ((EReal.neg_eq_top_iff).2 hbot)
  have hxgEff : x ∈ intrinsicInterior ℝ
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) negG) := by
    rw [← hdomNeg]; exact hxg
  have hclNeg :=
    helperForTheorem_38_7_convexFunctionClosure_eq_on_intrinsicInterior hnegPC hxgEff
  have hnegConv : ConvexFunction negG := by
    simpa [negG, IsERealConvex, ConvexFunctionOn,
      helperForTheorem_38_1_epigraph_eq_univ] using hg_concave
  have hconvClosureEq : convexClosure negG = convexFunctionClosure negG := by
    calc
      convexClosure negG = clConv n negG :=
        helperForTheorem_6_30_3_convexClosure_eq_clConv negG hnegConv
      _ = fenchelConjugate n (fenchelConjugate n negG) := by
        symm; exact fenchelConjugate_biconjugate_eq_clConv (n := n) (f := negG)
      _ = convexFunctionClosure negG :=
        section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
          (n := n) (f := negG) hnegConv
  have hgClosureX : concaveClosure g x = g x := by
    rw [concaveClosure_eq_neg_convexClosure_neg, show (fun z => -g z) = negG from rfl,
      hconvClosureEq]
    change -convexFunctionClosure negG x = g x
    rw [hclNeg]
    simp [negG]
  have hbiconj : concaveConjugateInner gStar = concaveClosure g := by
    simpa [gStar] using
      helperForLemma_38_6_concaveConjugateInner_biconjugate_eq_concaveClosure
        (g := g) hg_concave
  have hstarstar_ne_bot : concaveConjugateInner gStar x ≠ (⊥ : EReal) := by
    rw [hbiconj, hgClosureX]
    exact ne_of_gt (intrinsicInterior_subset (s := erealDomBot g) hxg)
  have hhStar : convexConjugateInner h = fun _ => (⊤ : EReal) := by
    funext y
    unfold convexConjugateInner
    apply top_le_iff.mp
    let xs : {z : Fin n → ℝ // z ∈ erealDom h} := ⟨x, by simp [erealDom, hxbot]⟩
    refine le_iSup_of_le xs ?_
    change (⊤ : EReal) ≤ (∑ i : Fin n, (((x i) * (y i) : ℝ) : EReal)) - h x
    rw [hxbot]
    have hs : (∑ i : Fin n, (((x i) * (y i) : ℝ) : EReal)) ≠ (⊥ : EReal) := by
      exact sum_ne_bot_of_ne_bot (s := Finset.univ)
        (f := fun i : Fin n => (((x i) * (y i) : ℝ) : EReal))
        (fun i _ => EReal.coe_ne_bot _)
    exact top_le_iff.mpr (EReal.sub_bot hs)
  have hgStarProper : IsProperEReal (fun y => -gStar y) :=
    helperForLemma_38_6_gStar_isProperNeg hg_proper hg_concave
  have hAlpha : (⨆ z : {z : Fin n → ℝ // z ∈ erealDom h},
      concaveConjugateInner gStar z.1 - h z.1) = (⊤ : EReal) := by
    apply top_le_iff.mp
    refine le_iSup_of_le ⟨x, by simp [erealDom, hxbot]⟩ ?_
    simpa [hxbot] using EReal.sub_bot hstarstar_ne_bot
  have hBeta : (⨅ y : {y : Fin n → ℝ // y ∈ erealDomBot gStar},
      convexConjugateInner h y.1 - gStar y.1) = (⊤ : EReal) := by
    rw [hhStar]
    refine top_unique (le_iInf ?_)
    intro y
    have hy : gStar y.1 ≠ (⊤ : EReal) := by
      intro hy; exact hgStarProper.1 y.1 (by simpa [hy])
    simpa using EReal.top_sub hy
  unfold fenchelInnerProduct
  rw [hAlpha, hBeta]
  simp

/-- The first Fenchel inner product in Theorem 38.7 exists in both the proper and improper
image branches. -/
lemma helperForTheorem_38_7_image_innerProduct_exists
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hg_proper : IsProperEReal (fun y => -g y)) (hg_concave : IsERealConvex (fun y => -g y))
    (hqual : ∃ u : Fin m → ℝ,
      u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
        (intrinsicInterior ℝ (erealDom (fun x : Fin n → ℝ => F u x)) ∩
          intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    ∃ c : EReal, fenchelInnerProduct (bifunctionImageRaw F f) (concaveConjugateInner g) = some c := by
  let h := bifunctionImageRaw F f
  have hhConvex := (helperForTheorem_38_7_image_convex_and_base_hri
    F f g hF_proper hF_convex hf_proper hf_convex hqual).2
  have hriImage :=
    helperForTheorem_38_7_qualification_implies_imageDom_inter_domBot_ri_nonempty
      F f g hF_proper hF_convex hf_proper hf_convex hqual
  by_cases hhProper : IsProperEReal h
  · exact fenchelInnerProduct_with_concaveConjugate_exists_of_ri
      h g hhProper hhConvex hg_proper hg_concave hriImage
  · exact ⟨⊤, helperForTheorem_38_7_improper_innerProduct_with_concaveConjugate_eq_top
      h g hhConvex hhProper hg_proper hg_concave hriImage⟩

/-- The Euclidean inner product on `Fin n → ℝ` used throughout §38 (as `∑ i, x i * y i`). -/
def euclideanInner (n : Nat) (x y : Fin n → ℝ) : ℝ :=
  Finset.univ.sum (fun i : Fin n => x i * y i)

/-- The adjoint `F^*` of a bifunction `F : ℝ^m → ℝ^n → EReal`, using the Euclidean identification
of a finite-dimensional space with its dual:
`F^* x* u* = inf_{u,x} (F u x - ⟨x, x*⟩ + ⟨u, u*⟩)`. -/
noncomputable def bifunctionAdjointInner {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar uStar =>
    ⨅ (u : Fin m → ℝ) (x : Fin n → ℝ),
      F u x + (-((euclideanInner n x xStar : ℝ) : EReal)) +
        ((euclideanInner m u uStar : ℝ) : EReal)

/-- The "concave image" of a function `g` under a bifunction `K : ℝ^n → ℝ^m → EReal`, defined by
`(Kg)(u) = sup_x (g x + K x u)` (modeled by `iSup`). This is the natural `sup`-analogue of
`bifunctionImageRaw` for concave transforms such as `F_*`. -/
lemma bifunctionAdjointInner_eq_adjointOfConvexBifunction {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hF : ConvexBifunction F) :
    bifunctionAdjointInner F = adjointOfConvexBifunction ⟨F, hF⟩ := by
  funext xStar uStar
  rw [bifunctionAdjointInner, adjointOfConvexBifunction, sInf_range]
  rw [show (⨅ p : (Fin m → ℝ) × (Fin n → ℝ),
      F p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
        (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) =
      ⨅ (u : Fin m → ℝ) (x : Fin n → ℝ),
        F u x - (((x ⬝ᵥ xStar : ℝ) : EReal)) +
          (((u ⬝ᵥ uStar : ℝ) : EReal)) by
        simp only [iInf_prod]]
  simp [euclideanInner, dotProduct, sub_eq_add_neg]

/-- The concave image of `g` under a bifunction `K`, using pointwise suprema. -/
noncomputable def bifunctionImageSupRaw {m n : Nat}
    (K : (Fin n → ℝ) → (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → EReal :=
  fun u => ⨆ x : (Fin n → ℝ), g x + K x u

lemma bifunctionInverseBookAdjoint_eq_neg_bifunctionAdjointInner {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hF : ConvexBifunction F) :
    bifunctionInverseBookAdjoint F =
      fun uStar xStar => -bifunctionAdjointInner F xStar uStar := by
  funext uStar xStar
  have hAdj :=
    adjointOfConvexBifunction_eq_neg_fenchelConjugate_graphFunction
      (⟨F, hF⟩ : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
      xStar uStar
  rw [bifunctionInverseBookAdjoint]
  rw [bifunctionAdjointInner_eq_adjointOfConvexBifunction F hF, hAdj]
  simp

/-- Negating a supremal bifunction image turns it into the infimal image of the
pointwise-negated data when the two summands never take `⊤`. -/
lemma neg_bifunctionImageSupRaw_eq_bifunctionImageRaw_neg
    {m n : Nat} (K : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (q : (Fin n → ℝ) → EReal)
    (hqTop : ∀ x, q x ≠ (⊤ : EReal))
    (hKTop : ∀ x u, K x u ≠ (⊤ : EReal)) :
    (fun u => -bifunctionImageSupRaw K q u) =
      bifunctionImageRaw (fun x u => -K x u) (fun x => -q x) := by
  funext u
  unfold bifunctionImageSupRaw bifunctionImageRaw
  have hnegSup :
      -(⨆ x, q x + K x u) = ⨅ x, -(q x + K x u) := by
    have h := congrArg Neg.neg
      (ereal_iSup_neg_eq_neg_iInf (g := fun x => -(q x + K x u)))
    simpa only [neg_neg] using h
  rw [hnegSup]
  refine iInf_congr ?_
  intro x
  exact EReal.neg_add (x := q x) (y := K x u)
    (Or.inr (hKTop x u)) (Or.inl (hqTop x))

/-- A proper concave conjugate never takes the value `⊤`. -/
lemma concaveConjugateInner_ne_top
    {n : Nat} {g : (Fin n → ℝ) → EReal}
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y)) :
    ∀ y, concaveConjugateInner g y ≠ (⊤ : EReal) := by
  have hproper : IsProperEReal (fun y => -(concaveConjugateInner g y)) :=
    helperForLemma_38_6_gStar_isProperNeg hg_proper hg_concave
  intro y hy
  have hbot := hproper.1 y
  apply hbot
  simp [hy]

/-- The product-coordinate properness and convexity hypotheses used in Theorem 38.7
give the Chapter 6 packaged notion of a proper convex bifunction. -/
lemma properConvexBifunction_of_product_hypotheses
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2)) :
    ProperConvexBifunction F := by
  let pairMap :
      (Fin (m + n) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { toFun := fun z =>
        (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
      map_add' := by intro z w; ext i <;> simp
      map_smul' := by intro a z; ext i <;> simp }
  have hPackedConvex : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [pairMap, bifunctionGraphFunction] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := pairMap)
        (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2) hF_convex)
  have hF30 : ConvexBifunction F := by
    simpa [ConvexBifunction, ConvexFunction, IsERealConvex, ConvexFunctionOn,
      helperForTheorem_38_1_epigraph_eq_univ] using hPackedConvex
  have hPackedProper : IsProperEReal (bifunctionGraphFunction F) := by
    constructor
    · intro z
      exact hF_proper.1
        (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
    · rcases hF_proper.2 with ⟨p, hp⟩
      exact ⟨Fin.append p.1 p.2, by simpa [bifunctionGraphFunction]⟩
  have hPackedProperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (bifunctionGraphFunction F) :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      (bifunctionGraphFunction F) hPackedProper hPackedConvex
  exact ⟨hF30,
    helperForText_26_4_0_2_properConvexERealFunction_of_properConvexFunctionOn
      hPackedProperOn⟩

/-- The adjoint of a proper convex bifunction never takes the value `⊤`. -/
lemma bifunctionAdjointInner_ne_top
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2)) :
    ∀ x u, bifunctionAdjointInner F x u ≠ (⊤ : EReal) := by
  have hProperF : ProperConvexBifunction F :=
    properConvexBifunction_of_product_hypotheses F hF_proper hF_convex
  have hF30 : ConvexBifunction F := hProperF.1
  have hProperAdj :
      ProperConcaveBifunction
        (adjointOfConvexBifunction ⟨F, hF30⟩) :=
    ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality F).1
      hF30).2.1.mpr hProperF
  intro x u htop
  have hnebot := hProperAdj.2.1.1 (Fin.append x u)
  have htop' : adjointOfConvexBifunction ⟨F, hF30⟩ x u = (⊤ : EReal) := by
    rw [← bifunctionAdjointInner_eq_adjointOfConvexBifunction F hF30]
    exact htop
  apply hnebot
  simp only [bifunctionGraphFunction, Fin.append_left, Fin.append_right, htop', EReal.neg_top]

/-- The negative of the adjoint supremal image is the infimal image under the
Chapter 38.4 inverse-book adjoint, with the concave conjugate negated. -/
lemma neg_adjointImageSup_eq_inverseBookImage_neg_concaveConjugate
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y)) :
    (fun u => -bifunctionImageSupRaw (bifunctionAdjointInner F)
      (concaveConjugateInner g) u) =
      bifunctionImageRaw (fun x u => bifunctionInverseBookAdjoint F u x)
        (fun x => -concaveConjugateInner g x) := by
  rw [neg_bifunctionImageSupRaw_eq_bifunctionImageRaw_neg
    (bifunctionAdjointInner F) (concaveConjugateInner g)
    (concaveConjugateInner_ne_top hg_proper hg_concave)
    (bifunctionAdjointInner_ne_top F hF_proper hF_convex)]
  have hF30 : ConvexBifunction F :=
    (properConvexBifunction_of_product_hypotheses F hF_proper hF_convex).1
  rw [bifunctionInverseBookAdjoint_eq_neg_bifunctionAdjointInner F hF30]

/-- The qualified adjoint image of a proper concave conjugate is everywhere below `⊤`.
A common relative-interior point supplies a finite affine upper bound uniform in the dual
variable over which the supremum is taken. -/
lemma adjointImageSup_concaveConjugate_ne_top
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hg_proper : IsProperEReal (fun y => -g y))
    (hqual : ∃ u : (Fin m → ℝ),
      (intrinsicInterior ℝ (erealDom (fun x : (Fin n → ℝ) => F u x)) ∩
        intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    ∀ uStar, bifunctionImageSupRaw (bifunctionAdjointInner F)
      (concaveConjugateInner g) uStar ≠ (⊤ : EReal) := by
  rcases hqual with ⟨u₀, x₀, hxF, hxg⟩
  have hF_top : F u₀ x₀ ≠ (⊤ : EReal) := by
    exact (lt_top_iff_ne_top.mp
      ((intrinsicInterior_subset (s := erealDom (fun x : Fin n → ℝ => F u₀ x))) hxF))
  have hF_bot : F u₀ x₀ ≠ (⊥ : EReal) := hF_proper.1 (u₀, x₀)
  have hg_bot : g x₀ ≠ (⊥ : EReal) := by
    exact (bot_lt_iff_ne_bot.mp
      ((intrinsicInterior_subset (s := erealDomBot g)) hxg))
  have hg_top : g x₀ ≠ (⊤ : EReal) := by
    intro htop
    exact hg_proper.1 x₀ (by simp [htop])
  intro uStar
  have hle :
      bifunctionImageSupRaw (bifunctionAdjointInner F)
          (concaveConjugateInner g) uStar ≤
        (((F u₀ x₀).toReal - (g x₀).toReal +
          euclideanInner m u₀ uStar : ℝ) : EReal) := by
    unfold bifunctionImageSupRaw
    refine iSup_le ?_
    intro xStar
    have hq : concaveConjugateInner g xStar ≤
        ((euclideanInner n x₀ xStar : ℝ) : EReal) - g x₀ := by
      unfold concaveConjugateInner
      exact iInf_le_of_le ⟨x₀, intrinsicInterior_subset hxg⟩ (by
        simp [euclideanInner, dotProduct, dotProduct_comm, ← ereal_sum_coe, mul_comm])
    have hK : bifunctionAdjointInner F xStar uStar ≤
        F u₀ x₀ + (-((euclideanInner n x₀ xStar : ℝ) : EReal)) +
          ((euclideanInner m u₀ uStar : ℝ) : EReal) := by
      unfold bifunctionAdjointInner
      exact iInf_le_of_le u₀ (iInf_le _ x₀)
    calc
      concaveConjugateInner g xStar + bifunctionAdjointInner F xStar uStar ≤
          (((euclideanInner n x₀ xStar : ℝ) : EReal) - g x₀) +
            (F u₀ x₀ + (-((euclideanInner n x₀ xStar : ℝ) : EReal)) +
              ((euclideanInner m u₀ uStar : ℝ) : EReal)) := add_le_add hq hK
      _ = (((F u₀ x₀).toReal - (g x₀).toReal +
          euclideanInner m u₀ uStar : ℝ) : EReal) := by
        rw [← EReal.coe_toReal hF_top hF_bot, ← EReal.coe_toReal hg_top hg_bot]
        simp only [sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_add]
        congr 1
        norm_num
        ring
  exact ne_of_lt (lt_of_le_of_lt hle (EReal.coe_lt_top _))

lemma helperForTheorem_38_7_sub_iSup_eq_iInf_sub {α : Type*} (a : EReal) (q : α → EReal)
    (haBot : a ≠ (⊥ : EReal)) (hSupTop : (⨆ i, q i) ≠ (⊤ : EReal))
    (hqTop : ∀ i, q i ≠ (⊤ : EReal)) :
    a - (⨆ i, q i) = ⨅ i, a - q i := by
  cases ha : a with
  | bot => exact (haBot ha).elim
  | top =>
      rw [EReal.top_sub hSupTop]
      symm
      exact top_unique (le_iInf (fun i => by simpa using EReal.top_sub (hqTop i)))
  | coe r =>
      rw [sub_eq_add_neg]
      have hneg : -(⨆ i, q i) = ⨅ i, -q i := by
        have h := congrArg Neg.neg (ereal_iSup_neg_eq_neg_iInf (g := fun i => -q i))
        simpa only [neg_neg] using h
      rw [hneg]
      simpa [ha, sub_eq_add_neg] using
        (helperForTheorem_6_30_15_real_add_iInf (c := r) (f := fun i => -q i))

lemma helperForTheorem_38_7_sub_iInf_eq_iSup_sub {α : Type*} (a : EReal) (q : α → EReal)
    (haTop : a ≠ (⊤ : EReal)) (hqBot : ∀ i, q i ≠ (⊥ : EReal)) :
    a - (⨅ i, q i) = ⨆ i, a - q i := by
  cases ha : a with
  | top => exact (haTop ha).elim
  | bot =>
      rw [EReal.bot_sub]
      symm
      exact bot_unique (iSup_le (fun i => by simpa using EReal.bot_sub (q i)))
  | coe r =>
      rw [sub_eq_add_neg]
      have hneg : -(⨅ i, q i) = ⨆ i, -q i := by
        exact helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg q
      rw [hneg]
      simpa [ha, sub_eq_add_neg] using
        (helperForTheorem_6_30_15_real_add_iSup (c := r) (f := fun i => -q i))

lemma helperForTheorem_38_7_iInf_domBot_eq_iInf {α : Type*} (a q : α → EReal)
    (haBot : ∀ i, a i ≠ (⊥ : EReal)) :
    (⨅ i : {i : α // i ∈ erealDomBot q}, a i.1 - q i.1) =
      ⨅ i : α, a i - q i := by
  apply le_antisymm
  · refine le_iInf ?_
    intro i
    by_cases hi : i ∈ erealDomBot q
    · exact iInf_le_of_le ⟨i, hi⟩ le_rfl
    · have hbot : q i = (⊥ : EReal) := by
        simpa [erealDomBot, bot_lt_iff_ne_bot] using hi
      rw [hbot, EReal.sub_bot (haBot i)]
      exact le_top
  · refine le_iInf ?_
    intro i
    exact iInf_le (fun j : α => a j - q j) i.1

lemma helperForTheorem_38_7_iSup_domBot_eq_iSup {α : Type*} (a q : α → EReal)
    (haTop : ∀ i, a i ≠ (⊤ : EReal)) :
    (⨆ i : {i : α // i ∈ erealDomBot q}, q i.1 + a i.1) =
      ⨆ i : α, q i + a i := by
  apply le_antisymm
  · refine iSup_le ?_
    intro i
    exact le_iSup (fun j : α => q j + a j) i.1
  · refine iSup_le ?_
    intro i
    by_cases hi : i ∈ erealDomBot q
    · exact le_iSup_of_le ⟨i, hi⟩ le_rfl
    · have hbot : q i = (⊥ : EReal) := by
        simpa [erealDomBot, bot_lt_iff_ne_bot] using hi
      rw [hbot]
      simpa [haTop i]

lemma helperForTheorem_38_7_inverseImageClosure_le_concaveConjugate_adjointImage
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y))
    (hqual : ∃ u : (Fin m → ℝ),
      (intrinsicInterior ℝ (erealDom (fun x : (Fin n → ℝ) => F u x)) ∩
        intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    ∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
      concaveClosure g x - F u x ≤
        concaveConjugateInner
          (bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g)) u := by
  intro u x
  have hgClTop : concaveClosure g x ≠ (⊤ : EReal) := by
    intro htop
    exact (helperForLemma_38_6_concaveClosure_isProperNeg hg_proper hg_concave).1 x
      (by simp [htop])
  by_cases hgClBot : concaveClosure g x = (⊥ : EReal)
  · rw [hgClBot, EReal.bot_sub]
    exact bot_le
  by_cases hFTop : F u x = (⊤ : EReal)
  · rw [hFTop]
    simpa using EReal.sub_top hgClTop
  have hFBot : F u x ≠ (⊥ : EReal) := hF_proper.1 (u, x)
  have hQTop : ∀ uStar,
      bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g) uStar ≠
        (⊤ : EReal) :=
    adjointImageSup_concaveConjugate_ne_top F g hF_proper hg_proper hqual
  have hbiconj : concaveConjugateInner (concaveConjugateInner g) = concaveClosure g :=
    helperForLemma_38_6_concaveConjugateInner_biconjugate_eq_concaveClosure
      (g := g) hg_concave
  unfold concaveConjugateInner
  refine le_iInf ?_
  intro uStar
  have hQBot :
      bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g) uStar.1 ≠
        (⊥ : EReal) := by
    simpa [erealDomBot, bot_lt_iff_ne_bot] using uStar.2
  lift bifunctionImageSupRaw (bifunctionAdjointInner F)
      (concaveConjugateInner g) uStar.1 to ℝ using ⟨hQTop uStar.1, hQBot⟩ with q hq
  lift F u x to ℝ using ⟨hFTop, hFBot⟩ with a ha
  lift concaveClosure g x to ℝ using ⟨hgClTop, hgClBot⟩ with b hb
  have hQle :
      bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g) uStar.1 ≤
        F u x + ((euclideanInner m u uStar.1 : ℝ) : EReal) - concaveClosure g x := by
    unfold bifunctionImageSupRaw
    refine iSup_le ?_
    intro xStar
    by_cases hgStarBot : concaveConjugateInner g xStar = (⊥ : EReal)
    · rw [hgStarBot]
      have hadjTop := bifunctionAdjointInner_ne_top F hF_proper hF_convex xStar uStar.1
      simp [hadjTop]
    have hgStarTop := concaveConjugateInner_ne_top hg_proper hg_concave xStar
    lift concaveConjugateInner g xStar to ℝ using ⟨hgStarTop, hgStarBot⟩ with s hs
    have hadjLe : bifunctionAdjointInner F xStar uStar.1 ≤
        F u x + (-((euclideanInner n x xStar : ℝ) : EReal)) +
          ((euclideanInner m u uStar.1 : ℝ) : EReal) := by
      unfold bifunctionAdjointInner
      exact iInf_le_of_le u (iInf_le _ x)
    have hclLe : concaveClosure g x ≤
        ((euclideanInner n x xStar : ℝ) : EReal) - concaveConjugateInner g xStar := by
      rw [← congrFun hbiconj x]
      unfold concaveConjugateInner
      exact iInf_le_of_le ⟨xStar, by
        change (⊥ : EReal) < concaveConjugateInner g xStar
        rw [← hs]
        simp⟩ (by
        simp [euclideanInner, dotProduct, dotProduct_comm, ← ereal_sum_coe, mul_comm])
    rw [← ha] at hadjLe ⊢
    rw [← hb] at hclLe ⊢
    rw [← hs] at hclLe
    cases hadj : bifunctionAdjointInner F xStar uStar.1 with
    | top =>
        exact (bifunctionAdjointInner_ne_top F hF_proper hF_convex xStar uStar.1 hadj).elim
    | bot => simp
    | coe t =>
        rw [hadj] at hadjLe
        have hadjLeR : t ≤ a - euclideanInner n x xStar + euclideanInner m u uStar.1 := by
          exact_mod_cast hadjLe
        have hclLeR : b ≤ euclideanInner n x xStar - s := by
          exact_mod_cast hclLe
        norm_num at ⊢
        exact_mod_cast (by linarith [hadjLeR, hclLeR])
  have hq' := hq
  unfold concaveConjugateInner at hq'
  rw [← hq']
  rw [← ha, ← hb] at hQle
  rw [← hq] at hQle
  have hQleR : q ≤ a + euclideanInner m u uStar.1 - b := by
    exact_mod_cast hQle
  have hreal : b - a ≤ euclideanInner m u uStar.1 - q := by
    linarith [hQleR]
  have hcast : ((b - a : ℝ) : EReal) ≤
      ((euclideanInner m u uStar.1 - q : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa [euclideanInner, ← ereal_sum_coe] using hcast

lemma helperForTheorem_38_7_sub_add_assoc (a b c : EReal) (haTop : a ≠ (⊤ : EReal))
    (hbTop : b ≠ (⊤ : EReal)) (hbBot : b ≠ (⊥ : EReal))
    (hcBot : c ≠ (⊥ : EReal)) :
    a - (b + c) = (a - c) - b := by
  cases ha : a with
  | top => exact (haTop ha).elim
  | bot => simp
  | coe r =>
      cases hb : b with
      | top => exact (hbTop hb).elim
      | bot => exact (hbBot hb).elim
      | coe s =>
          cases hc : c with
          | bot => exact (hcBot hc).elim
          | top => simp
          | coe t =>
              norm_num [sub_eq_add_neg]
              exact_mod_cast (by ring : r - (s + t) = (r - t) - s)

lemma helperForTheorem_38_7_alpha_image_le_adjoint
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f)
    (hg_proper : IsProperEReal (fun y => -g y))
    (hg_concave : IsERealConvex (fun y => -g y))
    (hqual : ∃ u : (Fin m → ℝ),
      (intrinsicInterior ℝ (erealDom (fun x : (Fin n → ℝ) => F u x)) ∩
        intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    (⨆ x : {x : Fin n → ℝ // x ∈ erealDom (bifunctionImageRaw F f)},
        concaveConjugateInner (concaveConjugateInner g) x.1 -
          bifunctionImageRaw F f x.1) ≤
      ⨆ u : {u : Fin m → ℝ // u ∈ erealDom f},
        concaveConjugateInner
            (bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g)) u.1 -
          f u.1 := by
  have hbiconj : concaveConjugateInner (concaveConjugateInner g) = concaveClosure g :=
    helperForLemma_38_6_concaveConjugateInner_biconjugate_eq_concaveClosure
      (g := g) hg_concave
  refine iSup_le ?_
  intro x
  rw [congrFun hbiconj x.1]
  unfold bifunctionImageRaw
  rw [helperForTheorem_38_7_sub_iInf_eq_iSup_sub
    (concaveClosure g x.1) (fun u => f u + F u x.1)
    (by
      intro htop
      exact (helperForLemma_38_6_concaveClosure_isProperNeg hg_proper hg_concave).1 x.1
        (by simp [htop]))
    (fun u => (EReal.add_ne_bot_iff).2 ⟨hf_proper.1 u, hF_proper.1 (u, x.1)⟩)]
  refine iSup_le ?_
  intro u
  by_cases hfuTop : f u = (⊤ : EReal)
  · have hsumTop : f u + F u x.1 = (⊤ : EReal) := by
      rw [hfuTop]
      exact EReal.top_add_of_ne_bot (hF_proper.1 (u, x.1))
    rw [hsumTop]
    have hgClTop : concaveClosure g x.1 ≠ (⊤ : EReal) := by
      intro htop
      exact (helperForLemma_38_6_concaveClosure_isProperNeg hg_proper hg_concave).1 x.1
        (by simp [htop])
    simpa using EReal.sub_top hgClTop
  · have huDom : u ∈ erealDom f := by simpa [erealDom, lt_top_iff_ne_top]
    refine le_trans ?_ (le_iSup (fun v : {v : Fin m → ℝ // v ∈ erealDom f} =>
      concaveConjugateInner
          (bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g)) v.1 -
        f v.1) ⟨u, huDom⟩)
    rw [helperForTheorem_38_7_sub_add_assoc
      (concaveClosure g x.1) (f u) (F u x.1)
      (by
        intro htop
        exact (helperForLemma_38_6_concaveClosure_isProperNeg hg_proper hg_concave).1 x.1
          (by simp [htop]))
      hfuTop (hf_proper.1 u) (hF_proper.1 (u, x.1))]
    exact EReal.sub_le_sub
      (helperForTheorem_38_7_inverseImageClosure_le_concaveConjugate_adjointImage
        F g hF_proper hF_convex hg_proper hg_concave hqual u x.1) le_rfl

lemma helperForTheorem_38_7_fenchel_alpha_le_beta
    {n : Nat} (f q : (Fin n → ℝ) → EReal)
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hqTop : ∀ y, q y ≠ (⊤ : EReal)) :
    (⨆ x : {x : Fin n → ℝ // x ∈ erealDom f},
        concaveConjugateInner q x.1 - f x.1) ≤
      ⨅ y : {y : Fin n → ℝ // y ∈ erealDomBot q},
        convexConjugateInner f y.1 - q y.1 := by
  refine iSup_le ?_
  intro x
  refine le_iInf ?_
  intro y
  have hfxTop : f x.1 ≠ (⊤ : EReal) := by
    simpa [erealDom, lt_top_iff_ne_top] using x.2
  have hfxBot : f x.1 ≠ (⊥ : EReal) := hf_proper.1 x.1
  have hqyBot : q y.1 ≠ (⊥ : EReal) := by
    simpa [erealDomBot, bot_lt_iff_ne_bot] using y.2
  have hqyTop : q y.1 ≠ (⊤ : EReal) := hqTop y.1
  lift f x.1 to ℝ using ⟨hfxTop, hfxBot⟩ with a ha
  lift q y.1 to ℝ using ⟨hqyTop, hqyBot⟩ with b hb
  have hqStarLe : concaveConjugateInner q x.1 ≤
      ((euclideanInner n x.1 y.1 : ℝ) : EReal) - q y.1 := by
    unfold concaveConjugateInner euclideanInner
    exact iInf_le_of_le y (by
      simp_rw [← EReal.coe_mul]
      rw [ereal_sum_coe])
  have hfStarGe : ((euclideanInner n x.1 y.1 : ℝ) : EReal) - f x.1 ≤
      convexConjugateInner f y.1 := by
    unfold convexConjugateInner euclideanInner
    exact le_iSup_of_le x (by
      simp_rw [← EReal.coe_mul]
      rw [ereal_sum_coe])
  have hqStarTop : concaveConjugateInner q x.1 ≠ (⊤ : EReal) := by
    intro htop
    rw [htop, ← hb] at hqStarLe
    have : ((euclideanInner n x.1 y.1 - b : ℝ) : EReal) = (⊤ : EReal) :=
      top_unique hqStarLe
    exact EReal.coe_ne_top _ this
  have hfStarBot : convexConjugateInner f y.1 ≠ (⊥ : EReal) :=
    (helperForLemma_38_6_fStar_isProperEReal hf_proper hf_convex).1 y.1
  cases hqStar : concaveConjugateInner q x.1 with
  | top => exact (hqStarTop hqStar).elim
  | bot => simp
  | coe c =>
      cases hfStar : convexConjugateInner f y.1 with
      | bot => exact (hfStarBot hfStar).elim
      | top =>
          simpa using EReal.top_sub (EReal.coe_ne_top b)
      | coe d =>
          rw [hqStar] at hqStarLe
          rw [← hb] at hqStarLe
          rw [hfStar, ← ha] at hfStarGe
          have hqStarLeR : c ≤ euclideanInner n x.1 y.1 - b := by
            exact_mod_cast hqStarLe
          have hfStarGeR : euclideanInner n x.1 y.1 - a ≤ d := by
            exact_mod_cast hfStarGe
          have hreal : c - a ≤ d - b := by linarith [hqStarLeR, hfStarGeR]
          exact_mod_cast hreal

lemma helperForTheorem_38_7_beta_transport
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hg_proper : IsProperEReal (fun y => -g y)) (hg_concave : IsERealConvex (fun y => -g y))
    (hqual : ∃ u : (Fin m → ℝ),
      u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
        (intrinsicInterior ℝ (erealDom (fun x : (Fin n → ℝ) => F u x)) ∩
          intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    let H := bifunctionImageRaw F f
    let gStar := concaveConjugateInner g
    let Q := bifunctionImageSupRaw (bifunctionAdjointInner F) gStar
    (⨅ xStar : {xStar : Fin n → ℝ // xStar ∈ erealDomBot gStar},
        convexConjugateInner H xStar.1 - gStar xStar.1) =
      ⨅ uStar : {uStar : Fin m → ℝ // uStar ∈ erealDomBot Q},
        convexConjugateInner f uStar.1 - Q uStar.1 := by
  dsimp only
  let H := bifunctionImageRaw F f
  let gStar := concaveConjugateInner g
  let Q := bifunctionImageSupRaw (bifunctionAdjointInner F) gStar
  have hbaseRi :
      (intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F)).Nonempty := by
    rcases hqual with ⟨u, hu, _⟩
    exact ⟨u, hu⟩
  have hconj := (theorem38_4_image_convex_and_conjugate F f hF_proper hF_convex
    hf_proper hf_convex).2 hbaseRi
  have hF30 : ConvexBifunction F :=
    (properConvexBifunction_of_product_hypotheses F hF_proper hF_convex).1
  have hbook := bifunctionInverseBookAdjoint_eq_neg_bifunctionAdjointInner F hF30
  have hfStarBot : ∀ uStar, convexConjugateInner f uStar ≠ (⊥ : EReal) := by
    intro uStar
    exact (helperForLemma_38_6_fStar_isProperEReal hf_proper hf_convex).1 uStar
  have hgStarTop : ∀ xStar, gStar xStar ≠ (⊤ : EReal) := by
    exact concaveConjugateInner_ne_top hg_proper hg_concave
  have hAdjTop : ∀ xStar uStar, bifunctionAdjointInner F xStar uStar ≠ (⊤ : EReal) :=
    bifunctionAdjointInner_ne_top F hF_proper hF_convex
  have hQTop : ∀ uStar, Q uStar ≠ (⊤ : EReal) := by
    apply adjointImageSup_concaveConjugate_ne_top F g hF_proper hg_proper
    rcases hqual with ⟨u, _, hx⟩
    exact ⟨u, hx⟩
  have hHStarBot : ∀ xStar, convexConjugateInner H xStar ≠ (⊥ : EReal) := by
    intro xStar
    rw [convexConjugateInner_eq_fenchelConjugate, hconj.1]
    rcases hconj.2 xStar with ⟨uStar, huStar⟩
    rw [huStar]
    rw [congrFun (congrFun hbook uStar) xStar]
    exact (EReal.add_ne_bot_iff).2
      ⟨by simpa [convexConjugateInner_eq_fenchelConjugate] using hfStarBot uStar,
        by simpa using hAdjTop xStar uStar⟩
  rw [helperForTheorem_38_7_iInf_domBot_eq_iInf _ _ hHStarBot]
  rw [helperForTheorem_38_7_iInf_domBot_eq_iInf _ _ hfStarBot]
  simp only [H, Q, gStar]
  have hleftPoint : ∀ xStar : Fin n → ℝ,
      convexConjugateInner (bifunctionImageRaw F f) xStar - concaveConjugateInner g xStar =
        ⨅ uStar : Fin m → ℝ,
          convexConjugateInner f uStar -
            (concaveConjugateInner g xStar + bifunctionAdjointInner F xStar uStar) := by
    intro xStar
    cases hgx : concaveConjugateInner g xStar with
    | top => exact (hgStarTop xStar hgx).elim
    | bot =>
        rw [EReal.sub_bot (hHStarBot xStar)]
        symm
        exact top_unique (le_iInf (fun uStar => by
          have hadj := hAdjTop xStar uStar
          have hsum : (⊥ : EReal) + bifunctionAdjointInner F xStar uStar = ⊥ := by
            simpa [hadj]
          rw [hsum, EReal.sub_bot (hfStarBot uStar)]))
    | coe r =>
        rw [convexConjugateInner_eq_fenchelConjugate, hconj.1]
        unfold bifunctionImageRaw
        rw [show
          (⨅ uStar : Fin m → ℝ,
              fenchelConjugate m f uStar + bifunctionInverseBookAdjoint F uStar xStar) =
            ⨅ uStar : Fin m → ℝ,
              convexConjugateInner f uStar + -bifunctionAdjointInner F xStar uStar by
            refine iInf_congr ?_
            intro uStar
            rw [convexConjugateInner_eq_fenchelConjugate,
              congrFun (congrFun hbook uStar) xStar]]
        calc
          (⨅ uStar : Fin m → ℝ,
              convexConjugateInner f uStar + -bifunctionAdjointInner F xStar uStar) -
                (r : EReal) =
              (-(r : EReal)) +
                (⨅ uStar : Fin m → ℝ,
                  convexConjugateInner f uStar + -bifunctionAdjointInner F xStar uStar) := by
                    simp [sub_eq_add_neg, add_comm]
          _ = ⨅ uStar : Fin m → ℝ,
                (-(r : EReal)) +
                  (convexConjugateInner f uStar +
                    -bifunctionAdjointInner F xStar uStar) := by
                  simpa using
                    (helperForTheorem_6_30_15_real_add_iInf
                      (c := -r)
                      (f := fun uStar : Fin m → ℝ =>
                        convexConjugateInner f uStar +
                          -bifunctionAdjointInner F xStar uStar))
          _ = ⨅ uStar : Fin m → ℝ,
                convexConjugateInner f uStar -
                  ((r : EReal) + bifunctionAdjointInner F xStar uStar) := by
                  refine iInf_congr ?_
                  intro uStar
                  have hfbot := hfStarBot uStar
                  have hatop := hAdjTop xStar uStar
                  cases hfu : convexConjugateInner f uStar with
                  | bot => exact (hfbot hfu).elim
                  | top =>
                      cases hau : bifunctionAdjointInner F xStar uStar with
                      | top => exact (hatop hau).elim
                      | bot => simp
                      | coe s =>
                          rw [EReal.top_sub (EReal.add_ne_top (EReal.coe_ne_top r)
                            (EReal.coe_ne_top s))]
                          simp
                  | coe t =>
                      cases hau : bifunctionAdjointInner F xStar uStar with
                      | top => exact (hatop hau).elim
                      | bot => simp
                      | coe s =>
                          norm_num [sub_eq_add_neg]
                          exact_mod_cast (by ring : -r + (t + -s) = t + -(r + s))
  have hrightPoint : ∀ uStar : Fin m → ℝ,
      convexConjugateInner f uStar -
          bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g) uStar =
        ⨅ xStar : Fin n → ℝ,
          convexConjugateInner f uStar -
            (concaveConjugateInner g xStar + bifunctionAdjointInner F xStar uStar) := by
    intro uStar
    exact helperForTheorem_38_7_sub_iSup_eq_iInf_sub
      (convexConjugateInner f uStar)
      (fun xStar => concaveConjugateInner g xStar +
        bifunctionAdjointInner F xStar uStar)
      (hfStarBot uStar) (hQTop uStar)
      (fun xStar => EReal.add_ne_top (hgStarTop xStar) (hAdjTop xStar uStar))
  simp_rw [hleftPoint, hrightPoint]
  exact iInf_comm

lemma helperForTheorem_38_7_first_fenchel_transport
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hg_proper : IsProperEReal (fun y => -g y)) (hg_concave : IsERealConvex (fun y => -g y))
    (hqual : ∃ u : (Fin m → ℝ),
      u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
        (intrinsicInterior ℝ (erealDom (fun x : (Fin n → ℝ) => F u x)) ∩
          intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    ∃ c : EReal,
      fenchelInnerProduct (bifunctionImageRaw F f) (concaveConjugateInner g) = some c ∧
        fenchelInnerProduct f
          (bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g)) = some c := by
  rcases helperForTheorem_38_7_image_innerProduct_exists
    F f g hF_proper hF_convex hf_proper hf_convex hg_proper hg_concave hqual with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  let alpha1 : EReal :=
    ⨆ x : {x : Fin n → ℝ // x ∈ erealDom (bifunctionImageRaw F f)},
      concaveConjugateInner (concaveConjugateInner g) x.1 - bifunctionImageRaw F f x.1
  let beta1 : EReal :=
    ⨅ xStar : {xStar : Fin n → ℝ // xStar ∈ erealDomBot (concaveConjugateInner g)},
      convexConjugateInner (bifunctionImageRaw F f) xStar.1 - concaveConjugateInner g xStar.1
  let Q := bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g)
  let alpha2 : EReal :=
    ⨆ u : {u : Fin m → ℝ // u ∈ erealDom f}, concaveConjugateInner Q u.1 - f u.1
  let beta2 : EReal :=
    ⨅ uStar : {uStar : Fin m → ℝ // uStar ∈ erealDomBot Q},
      convexConjugateInner f uStar.1 - Q uStar.1
  have hEq1 : alpha1 = beta1 := by
    unfold fenchelInnerProduct at hc
    dsimp only at hc
    split_ifs at hc with hEq
    simpa [alpha1, beta1] using hEq
  have hcAlpha : alpha1 = c := by
    have hform : fenchelInnerProduct (bifunctionImageRaw F f) (concaveConjugateInner g) =
        some alpha1 := by
      unfold fenchelInnerProduct
      dsimp only
      have hEqRaw :
          (⨆ x : {x : Fin n → ℝ // x ∈ erealDom (bifunctionImageRaw F f)},
            concaveConjugateInner (concaveConjugateInner g) x.1 - bifunctionImageRaw F f x.1) =
            (⨅ y : {y : Fin n → ℝ // y ∈ erealDomBot (concaveConjugateInner g)},
              convexConjugateInner (bifunctionImageRaw F f) y.1 - concaveConjugateInner g y.1) := by
        simpa [alpha1, beta1] using hEq1
      rw [if_pos hEqRaw]
    exact Option.some.inj (hform.symm.trans hc)
  have hBeta : beta1 = beta2 := by
    simpa [beta1, beta2, Q] using
      (helperForTheorem_38_7_beta_transport F f g hF_proper hF_convex hf_proper hf_convex
        hg_proper hg_concave hqual)
  have hAlphaLe : alpha1 ≤ alpha2 := by
    apply helperForTheorem_38_7_alpha_image_le_adjoint F f g hF_proper hF_convex hf_proper
      hg_proper hg_concave
    rcases hqual with ⟨u, _, hx⟩
    exact ⟨u, hx⟩
  have hQTop : ∀ uStar, Q uStar ≠ (⊤ : EReal) := by
    apply adjointImageSup_concaveConjugate_ne_top F g hF_proper hg_proper
    rcases hqual with ⟨u, _, hx⟩
    exact ⟨u, hx⟩
  have hWeak : alpha2 ≤ beta2 := by
    simpa [alpha2, beta2] using helperForTheorem_38_7_fenchel_alpha_le_beta f Q hf_proper hf_convex hQTop
  have hEq2 : alpha2 = beta2 := by
    apply le_antisymm hWeak
    rw [← hBeta, ← hEq1]
    exact hAlphaLe
  unfold fenchelInnerProduct
  dsimp only
  rw [show
    (⨆ u : {u : Fin m → ℝ // u ∈ erealDom f}, concaveConjugateInner Q u.1 - f u.1) =
      (⨅ uStar : {uStar : Fin m → ℝ // uStar ∈ erealDomBot Q},
        convexConjugateInner f uStar.1 - Q uStar.1) by simpa [alpha2, beta2] using hEq2]
  rw [show
    (⨅ uStar : {uStar : Fin m → ℝ // uStar ∈ erealDomBot Q},
      convexConjugateInner f uStar.1 - Q uStar.1) = c by
        change beta2 = c
        rw [← hBeta, ← hEq1, hcAlpha]]
  simp

/-- Under the primal relative-interior qualification, the conjugate of the infimal image is the
image of the convex conjugate under the inverse Euclidean adjoint. -/
lemma helperForTheorem_38_7_image_conjugate_eq_inverseAdjointImage
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hri :
      (intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F)).Nonempty) :
    convexConjugateInner (bifunctionImageRaw F f) =
      bifunctionImageRaw (bifunctionInverse (bifunctionAdjointInner F))
        (convexConjugateInner f) := by
  have h38 := (theorem38_4_image_convex_and_conjugate
    F f hF_proper hF_convex hf_proper hf_convex).2 hri
  have hleft : convexConjugateInner (bifunctionImageRaw F f) =
      fenchelConjugate n (bifunctionImageRaw F f) := by
    funext x
    exact convexConjugateInner_eq_fenchelConjugate _ _
  rw [hleft, h38.1]
  have hfStar : convexConjugateInner f = fenchelConjugate m f := by
    funext u
    exact convexConjugateInner_eq_fenchelConjugate _ _
  rw [hfStar]
  have hF30 : ConvexBifunction F :=
    (properConvexBifunction_of_product_hypotheses F hF_proper hF_convex).1
  rw [bifunctionInverseBookAdjoint_eq_neg_bifunctionAdjointInner F hF30]
  rfl

-- Proof sketch: This is the bifunctional "adjointness" identity for Fenchel inner products.
-- Combine the qualification hypothesis (a relative-interior condition ensuring existence of the
-- relevant extremal values) with the conjugacy formula for images (Theorem 38.4), the duality
-- results from Chapter 6 (Theorems 6.5, 6.6, 6.8), and the conjugate-symmetry lemma (Lemma 38.6),
-- rewriting each term in the chain using `bifunctionAdjointInner` for `F^*` and `bifunctionInverse`
-- for `F_*` and `F^*_*`.
/-- Theorem 38.7: Let `F` be a proper convex bifunction from `ℝ^m` to `ℝ^n`. Let `f` be a proper
convex function on `ℝ^m`, and let `g` be a proper concave function on `ℝ^n`. Assume there exists
at least one `u ∈ ri (dom f) ∩ ri (dom F)` such that `ri (dom (F u))` meets `ri (dom g)`. Then the
Fenchel inner products in the text all exist and satisfy

`⟨Ff, g^*⟩ = ⟨f, F^* g^*⟩ = -⟨f^*, F_* g⟩ = -⟨F^*_* f^*, g⟩`.

In Lean, we model `⟨·,·⟩` by `fenchelInnerProduct : Option EReal`, `f^*` by `convexConjugateInner`,
`g^*` by `concaveConjugateInner`, `Ff` by `bifunctionImageRaw F f`, `F^*` by
`bifunctionAdjointInner F`, `F_*` by `bifunctionInverse F`, and `F^*_*` by
`bifunctionInverse (bifunctionAdjointInner F)`.

The four-value chain additionally records the regularity needed by the biconjugation steps:
`Ff` is proper; `g` equals its concave biconjugate; the adjoint image `F^* g^*` is proper and
concave; and its concave conjugate is exactly `F_* g`.  The first adjacent equality itself needs
only the relative-interior qualification and is provided separately above. -/
theorem theorem38_7_fenchelInnerProduct_image_adjoint_inverse
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (f : (Fin m → ℝ) → EReal)
    (g : (Fin n → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hg_proper : IsProperEReal (fun y => -g y)) (hg_concave : IsERealConvex (fun y => -g y))
    (hqual :
      ∃ u : (Fin m → ℝ),
        u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
          (intrinsicInterior ℝ (erealDom (fun x : (Fin n → ℝ) => F u x)) ∩
              intrinsicInterior ℝ (erealDomBot g)).Nonempty)
    (hImage_proper : IsProperEReal (bifunctionImageRaw F f))
    (hg_biconj : concaveConjugateInner (concaveConjugateInner g) = g)
    (hQ_proper : IsProperEReal (fun u =>
      -bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g) u))
    (hQ_concave : IsERealConvex (fun u =>
      -bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g) u))
    (hQ_conj :
      concaveConjugateInner
          (bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g)) =
        bifunctionImageSupRaw (bifunctionInverse F) g) :
    ∃ c : EReal,
      fenchelInnerProduct (bifunctionImageRaw F f) (concaveConjugateInner g) = some c ∧
        fenchelInnerProduct f
            (bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g)) =
          some c ∧
        fenchelInnerProduct (convexConjugateInner f) (bifunctionImageSupRaw (bifunctionInverse F) g) =
          some (-c) ∧
        fenchelInnerProduct
            (bifunctionImageRaw (bifunctionInverse (bifunctionAdjointInner F)) (convexConjugateInner f))
            g =
          some (-c) := by
  rcases helperForTheorem_38_7_first_fenchel_transport
      F f g hF_proper hF_convex hf_proper hf_convex hg_proper hg_concave hqual with
    ⟨c, hleft, hright⟩
  let Q := bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveConjugateInner g)
  have hthirdRaw := (fenchelInnerProduct_conjugates_eq_neg_and_closure
    f Q hf_proper hQ_proper hf_convex hQ_concave hright).1
  have hthird : fenchelInnerProduct (convexConjugateInner f)
      (bifunctionImageSupRaw (bifunctionInverse F) g) = some (-c) := by
    simpa only [Q, hQ_conj] using hthirdRaw
  have hriBase :
      (intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F)).Nonempty := by
    rcases hqual with ⟨u, hu, _⟩
    exact ⟨u, hu⟩
  have hImageConvex : IsERealConvex (bifunctionImageRaw F f) :=
    (theorem38_4_image_convex_and_conjugate
      F f hF_proper hF_convex hf_proper hf_convex).1
  have hgStarProper : IsProperEReal (fun x => -concaveConjugateInner g x) :=
    helperForLemma_38_6_gStar_isProperNeg hg_proper hg_concave
  have hgStarConcave : IsERealConvex (fun x => -concaveConjugateInner g x) := by
    have hp := helperForLemma_38_6_gStar_properConcaveFunctionOn hg_proper hg_concave
    simpa [ProperConcaveFunctionOn, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hp.1
  have hfourthRaw := (fenchelInnerProduct_conjugates_eq_neg_and_closure
    (bifunctionImageRaw F f) (concaveConjugateInner g)
    hImage_proper hgStarProper hImageConvex hgStarConcave hleft).1
  have hImageConj := helperForTheorem_38_7_image_conjugate_eq_inverseAdjointImage
    F f hF_proper hF_convex hf_proper hf_convex hriBase
  have hfourth : fenchelInnerProduct
      (bifunctionImageRaw (bifunctionInverse (bifunctionAdjointInner F))
        (convexConjugateInner f)) g = some (-c) := by
    rw [← hImageConj, ← hg_biconj]
    exact hfourthRaw
  exact ⟨c, hleft, hright, hthird, hfourth⟩

lemma linearPairing_isProperEReal_neg_and_isERealConvex {n : Nat}
    (xStar : Fin n → ℝ) :
    IsProperEReal (fun y : Fin n → ℝ => -(((y ⬝ᵥ xStar : ℝ)) : EReal)) ∧
      IsERealConvex (fun y : Fin n → ℝ => -(((y ⬝ᵥ xStar : ℝ)) : EReal)) := by
  constructor
  · constructor
    · intro y
      simp
    · exact ⟨0, by simp⟩
  · intro p hp q hq a b ha hb hab
    change (-(((a • p.1 + b • q.1) ⬝ᵥ xStar : ℝ) : EReal)) ≤
      ((a • p.2 + b • q.2 : ℝ) : EReal)
    have hp' : -((p.1 ⬝ᵥ xStar : ℝ)) ≤ p.2 := by
      change (-(((p.1 ⬝ᵥ xStar : ℝ)) : EReal)) ≤ (p.2 : EReal) at hp
      exact_mod_cast hp
    have hq' : -((q.1 ⬝ᵥ xStar : ℝ)) ≤ q.2 := by
      change (-(((q.1 ⬝ᵥ xStar : ℝ)) : EReal)) ≤ (q.2 : EReal) at hq
      exact_mod_cast hq
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct]
    push_cast
    norm_cast
    dsimp only [smul_eq_mul]
    linarith [mul_le_mul_of_nonneg_left hp' ha,
      mul_le_mul_of_nonneg_left hq' hb]

/-- A finite Euclidean linear pairing has full lower effective domain. -/
lemma erealDomBot_linearPairing_eq_univ {n : Nat} (xStar : Fin n → ℝ) :
    erealDomBot (fun y : Fin n → ℝ => (((y ⬝ᵥ xStar : ℝ)) : EReal)) = Set.univ := by
  ext y
  simp [erealDomBot]

/-- The concave conjugate of evaluation against `xStar` is the concave point indicator at
`xStar`. -/
lemma concaveConjugateInner_linearPairing_eq_indicator {n : Nat} (xStar : Fin n → ℝ) :
    concaveConjugateInner (fun y : Fin n → ℝ => (((y ⬝ᵥ xStar : ℝ)) : EReal)) =
      concaveIndicatorPoint xStar := by
  funext x
  by_cases h : x = xStar
  · subst x
    rw [concaveIndicatorPoint, if_pos rfl]
    unfold concaveConjugateInner
    apply le_antisymm
    · exact iInf_le_of_le ⟨0, by simp [erealDomBot]⟩ (by simp)
    · refine le_iInf ?_
      intro y
      simp_rw [← EReal.coe_mul]
      rw [← section16_coe_finset_sum]
      rw [show (∑ i, xStar i * y.1 i) = y.1 ⬝ᵥ xStar by
        simpa [dotProduct] using dotProduct_comm xStar y.1]
      simp
  · rw [concaveIndicatorPoint]
    simp only [h, if_false]
    unfold concaveConjugateInner
    rw [iInf_eq_bot]
    intro b hb
    let d : Fin n → ℝ := xStar - x
    have hdne : d ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hd : 0 < d ⬝ᵥ d := dotProduct_self_pos_of_ne_zero hdne
    by_cases hbtop : b = ⊤
    · refine ⟨⟨0, by simp [erealDomBot]⟩, ?_⟩
      simp [hbtop]
    let t : ℝ := (-b.toReal + 1) / (d ⬝ᵥ d)
    have ht : -(t * (d ⬝ᵥ d)) < b.toReal := by
      dsimp [t]
      field_simp
      linarith
    refine ⟨⟨t • d, ?_⟩, ?_⟩
    · simp [erealDomBot]
    · have hval : (((x ⬝ᵥ (t • d) : ℝ) : EReal) -
          (((t • d) ⬝ᵥ xStar : ℝ) : EReal)) < b := by
        rw [← EReal.coe_sub]
        rw [← EReal.coe_toReal hbtop (ne_of_gt hb)]
        rw [EReal.coe_lt_coe_iff]
        dsimp [d]
        rw [dotProduct_smul, smul_dotProduct]
        have hdot : (x ⬝ᵥ (xStar - x)) - ((xStar - x) ⬝ᵥ xStar) =
            -((xStar - x) ⬝ᵥ (xStar - x)) := by
          simp only [dotProduct_sub, sub_dotProduct]
          rw [dotProduct_comm x xStar]
          ring
        simp only [smul_eq_mul]
        rw [← mul_sub, hdot]
        rw [mul_neg]
        exact ht
      have hcoeDot :
          (∑ i, (x i : EReal) * ((t • d) i : EReal)) =
            (((x ⬝ᵥ (t • d) : ℝ)) : EReal) := by
        simp_rw [← EReal.coe_mul]
        rw [← section16_coe_finset_sum]
        rfl
      rw [hcoeDot]
      exact hval

/-- Applying a concave point indicator through an adjoint supremal image selects the indicated
adjoint slice. -/
lemma bifunctionImageSupRaw_adjoint_indicator_eq {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    bifunctionImageSupRaw (bifunctionAdjointInner F) (concaveIndicatorPoint xStar) =
      bifunctionAdjointInner F xStar := by
  funext uStar
  unfold bifunctionImageSupRaw
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    by_cases hx : x = xStar
    · subst x
      simp [concaveIndicatorPoint]
    · simp [concaveIndicatorPoint, hx]
  · exact le_iSup_of_le xStar (by simp [concaveIndicatorPoint])



-- Proof sketch: Specialize Theorem 38.7 to the concave indicator `g = concaveIndicatorPoint xStar`,
-- use the Chapter 6 existence results under `ri (dom f) ∩ ri (dom F) ≠ ∅` to obtain existence of
-- the relevant inner products for every `xStar`, and then identify
-- `⟨Ff, xStar⟩` with `fenchelInnerProduct (bifunctionImageRaw F f) (concaveIndicatorPoint xStar)`
-- and `⟨f, F^* xStar⟩` with `fenchelInnerProduct f (bifunctionAdjointInner F xStar)`.
/-- Corollary 38.7.1: Let `F` be a proper convex bifunction from `ℝ^m` to `ℝ^n`, and let `f` be a
proper convex function on `ℝ^m` such that `ri (dom f)` meets `ri (dom F)`. Then for every
`xStar : ℝ^n`, the inner product `⟨f, F^* xStar⟩` exists, and

`⟨Ff, xStar⟩ = ⟨f, F^* xStar⟩`.

In Lean, `⟨Ff, xStar⟩` is modeled by
`fenchelInnerProduct (bifunctionImageRaw F f) (concaveIndicatorPoint xStar)`,
while `⟨f, F^* xStar⟩` is modeled by
`fenchelInnerProduct f (bifunctionAdjointInner F xStar)`. -/
theorem fenchelInnerProduct_image_point_eq_adjoint_point
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (f : (Fin m → ℝ) → EReal)
    (hF_proper : IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hF_convex : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2))
    (hf_proper : IsProperEReal f) (hf_convex : IsERealConvex f)
    (hri :
      (intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F)).Nonempty) :
    ∀ xStar : Fin n → ℝ, ∃ c : EReal,
      fenchelInnerProduct (bifunctionImageRaw F f) (concaveIndicatorPoint xStar) = some c ∧
        fenchelInnerProduct f (bifunctionAdjointInner F xStar) = some c :=
  by
    intro xStar
    let gLinear : (Fin n → ℝ) → EReal :=
      fun y => (((y ⬝ᵥ xStar : ℝ)) : EReal)
    have hg := linearPairing_isProperEReal_neg_and_isERealConvex xStar
    have hqual :
        ∃ u : Fin m → ℝ,
          u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
            (intrinsicInterior ℝ (erealDom (fun x : Fin n → ℝ => F u x)) ∩
                intrinsicInterior ℝ (erealDomBot gLinear)).Nonempty := by
      rcases hri with ⟨u, huf, huF⟩
      refine ⟨u, ⟨huf, huF⟩, ?_⟩
      have hslice : IsERealConvex (F u) := by
        intro p hp q hq a b ha hb hab
        have hp' : ((u, p.1), p.2) ∈ ERealEpigraph
            (fun z : (Fin m → ℝ) × (Fin n → ℝ) => F z.1 z.2) := by
          simpa [ERealEpigraph] using hp
        have hq' : ((u, q.1), q.2) ∈ ERealEpigraph
            (fun z : (Fin m → ℝ) × (Fin n → ℝ) => F z.1 z.2) := by
          simpa [ERealEpigraph] using hq
        have h := hF_convex hp' hq' ha hb hab
        have hu : a • u + b • u = u := by
          rw [← add_smul, hab, one_smul]
        simpa [ERealEpigraph, Prod.smul_mk, Prod.mk_add_mk, hu] using h
      have hsliceConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F u) := by
        simpa [ConvexFunctionOn, IsERealConvex,
          helperForTheorem_38_1_epigraph_eq_univ] using hslice
      have hdomConv : Convex ℝ (erealDom (F u)) := by
        simpa [erealDom, effectiveDomain_eq] using
          (effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ)))
            (f := F u) hsliceConvOn)
      have huDom : u ∈ bifunctionDom F :=
        intrinsicInterior_subset (s := bifunctionDom F) huF
      rcases huDom with ⟨x, hx⟩
      have hdomNe : (erealDom (F u)).Nonempty :=
        ⟨x, lt_top_iff_ne_top.2 hx⟩
      rcases Set.Nonempty.intrinsicInterior hdomConv hdomNe with ⟨x0, hx0⟩
      refine ⟨x0, hx0, ?_⟩
      rw [erealDomBot_linearPairing_eq_univ xStar]
      rw [← helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
      exact helperForTheorem_31_5_mem_euclideanRelativeInterior_univ x0
    rcases helperForTheorem_38_7_first_fenchel_transport
        F f gLinear hF_proper hF_convex hf_proper hf_convex hg.1 hg.2 hqual with
      ⟨c, hleft, hright⟩
    refine ⟨c, ?_, ?_⟩
    · simpa [gLinear, concaveConjugateInner_linearPairing_eq_indicator] using hleft
    · simpa [gLinear, concaveConjugateInner_linearPairing_eq_indicator,
        bifunctionImageSupRaw_adjoint_indicator_eq] using hright

/-- A point indicator is a proper convex function. -/
lemma convexIndicatorPoint_isProperEReal_and_isERealConvex {n : Nat} (u : Fin n → ℝ) :
    IsProperEReal (convexIndicatorPoint u) ∧ IsERealConvex (convexIndicatorPoint u) := by
  constructor
  · constructor
    · intro v
      by_cases hv : v = u <;> simp [convexIndicatorPoint, hv]
    · exact ⟨u, by simp [convexIndicatorPoint]⟩
  · have hconv : Convex ℝ ({u} : Set (Fin n → ℝ)) := convex_singleton u
    have hfun : ConvexFunction (indicatorFunction ({u} : Set (Fin n → ℝ))) :=
      convexFunction_indicator_of_convex hconv
    simpa [convexIndicatorPoint, indicatorFunction, IsERealConvex, ConvexFunction,
      ConvexFunctionOn, helperForTheorem_38_1_epigraph_eq_univ] using hfun

/-- Infimally imaging a point indicator selects the corresponding bifunction slice. -/
lemma bifunctionImageRaw_convexIndicatorPoint_eq_slice {m n : Nat}
    (F : FiberwiseProperConvexBifunction m n) (u : Fin m → ℝ) :
    bifunctionImageRaw F.toFun (convexIndicatorPoint u) = F.toFun u := by
  funext x
  unfold bifunctionImageRaw
  apply le_antisymm
  · exact iInf_le_of_le u (by simp [convexIndicatorPoint])
  · refine le_iInf ?_
    intro v
    by_cases hv : v = u
    · subst v
      simp [convexIndicatorPoint]
    · rw [convexIndicatorPoint, if_neg hv]
      rw [EReal.top_add_of_ne_bot (F.proper.1 v x)]
      exact le_top

-- Proof sketch: Apply Corollary 38.7.1 twice. First, view `Fu` as a convex function on `ℝ^n` and
-- apply Corollary 38.7.1 to the bifunction `G` to get `⟨GFu, y*⟩ = ⟨Fu, G^* y*⟩` (existence
-- included) under the hypothesis `ri (dom F_*) ∩ ri (dom G) ≠ ∅`. Second, apply Corollary 38.7.1
-- to the bifunction `F` with `f = δ(·|u)` to identify `Fu` as the image `Ff` and obtain
-- `⟨Fu, G^* y*⟩ = ⟨u, F^* (G^* y*)⟩`, where `F^* (G^* y*)` is the concave image
-- `bifunctionImageSupRaw (bifunctionAdjointInner F) (bifunctionAdjointInner G y*)`.
/-- Corollary 38.7.2: Let `F` be a proper convex bifunction from `ℝ^m` to `ℝ^n`, and let `G` be a
proper convex bifunction from `ℝ^n` to `ℝ^p`. Assume that `ri (dom F_*)` and `ri (dom G)` have a
point in common. Then, for each `u ∈ ri (dom (G ⊙ F))`, the inner product `⟨F u, G^* y*⟩` exists
for every `y* ∈ ℝ^p` and one has the chain

`⟨(G ⊙ F) u, y*⟩ = ⟨F u, G^* y*⟩ = ⟨u, F^* (G^* y*)⟩`.

In Lean:
- `G ⊙ F` is `bifunctionCompose G F`;
- `F_*` is `bifunctionInverse F.toFun`;
- `ri` is modeled by `intrinsicInterior`;
- `G^*` and `F^*` are modeled by `bifunctionAdjointInner`;
- the point pairings `⟨h, y*⟩` and `⟨u, k⟩` are represented using `fenchelInnerProduct` with the
  point indicators `concaveIndicatorPoint yStar` and `convexIndicatorPoint u`.

The fiberwise structure alone does not encode the joint convexity used by the book.  Accordingly,
the Lean statement records joint proper-convex hypotheses for `F` and `G`, properness and the
slice relative-interior qualification for `F u`, and a proper concave preconjugate of `G^* y*`
which satisfies the qualification needed for the second adjoint transport. -/
theorem fenchelInnerProduct_compose_point_eq_adjoint_chain
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (_hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
            intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (hF_proper : IsProperEReal
      (fun z : (Fin m → ℝ) × (Fin n → ℝ) => F.toFun z.1 z.2))
    (hF_convex : IsERealConvex
      (fun z : (Fin m → ℝ) × (Fin n → ℝ) => F.toFun z.1 z.2))
    (hG_proper : IsProperEReal
      (fun z : (Fin n → ℝ) × (Fin p → ℝ) => G.toFun z.1 z.2))
    (hG_convex : IsERealConvex
      (fun z : (Fin n → ℝ) × (Fin p → ℝ) => G.toFun z.1 z.2)) :
    ∀ {u : Fin m → ℝ},
      u ∈ intrinsicInterior ℝ (bifunctionDom (bifunctionCompose G F)) →
      IsProperEReal (F.toFun u) →
      (intrinsicInterior ℝ (erealDom (F.toFun u)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty →
      ∀ yStar : Fin p → ℝ,
        (∃ gY : (Fin n → ℝ) → EReal,
          IsProperEReal (fun x => -gY x) ∧
          IsERealConvex (fun x => -gY x) ∧
          concaveConjugateInner gY = bifunctionAdjointInner G.toFun yStar ∧
          ∃ v : Fin m → ℝ,
            v ∈ intrinsicInterior ℝ (erealDom (convexIndicatorPoint u)) ∩
              intrinsicInterior ℝ (bifunctionDom F.toFun) ∧
            (intrinsicInterior ℝ (erealDom (fun x : Fin n → ℝ => F.toFun v x)) ∩
              intrinsicInterior ℝ (erealDomBot gY)).Nonempty) →
        ∃ c : EReal,
          fenchelInnerProduct (fun y : Fin p → ℝ => bifunctionCompose G F u y)
              (concaveIndicatorPoint yStar) = some c ∧
            fenchelInnerProduct (fun x : Fin n → ℝ => F.toFun u x)
                (bifunctionAdjointInner G.toFun yStar) = some c ∧
            fenchelInnerProduct (convexIndicatorPoint u)
                (bifunctionImageSupRaw (bifunctionAdjointInner F.toFun)
                  (bifunctionAdjointInner G.toFun yStar)) = some c :=
  by
    intro u _hu hFu_proper hriGu yStar hpre
    rcases fenchelInnerProduct_image_point_eq_adjoint_point
        G.toFun (F.toFun u) hG_proper hG_convex hFu_proper (F.convex u) hriGu yStar with
      ⟨c, hcompose, hmiddle⟩
    rcases hpre with ⟨gY, hgY_proper, hgY_concave, hgY_conj, hqual⟩
    have hIndicator := convexIndicatorPoint_isProperEReal_and_isERealConvex u
    rcases helperForTheorem_38_7_first_fenchel_transport
        F.toFun (convexIndicatorPoint u) gY hF_proper hF_convex
        hIndicator.1 hIndicator.2 hgY_proper hgY_concave hqual with
      ⟨d, hmiddle', hlast⟩
    have hmiddleEq :
        fenchelInnerProduct (F.toFun u) (bifunctionAdjointInner G.toFun yStar) = some d := by
      simpa only [bifunctionImageRaw_convexIndicatorPoint_eq_slice F u, hgY_conj] using hmiddle'
    have hlastEq : fenchelInnerProduct (convexIndicatorPoint u)
        (bifunctionImageSupRaw (bifunctionAdjointInner F.toFun)
          (bifunctionAdjointInner G.toFun yStar)) = some d := by
      simpa only [hgY_conj] using hlast
    have hcd : c = d := Option.some.inj (hmiddle.symm.trans hmiddleEq)
    subst d
    refine ⟨c, ?_, hmiddle, hlastEq⟩
    simpa only [bifunctionImageRaw, bifunctionCompose] using hcompose

/-- A predicate asserting that the epigraph of an `EReal`-valued function contains a non-vertical
half-line: there exist a base point `p ∈ epi f` and a direction `d` whose `X`-component is
nonzero, such that `p + t • d ∈ epi f` for every `t ≥ 0`. -/
def ERealEpigraphHasNonverticalHalfLine
    {X : Type*} [AddCommGroup X] [Module ℝ X] (f : X → EReal) : Prop :=
  ∃ (p d : X × ℝ),
    p ∈ ERealEpigraph f ∧ d.1 ≠ (0 : X) ∧ ∀ t : ℝ, 0 ≤ t → p + t • d ∈ ERealEpigraph f

/-- A book-style co-finiteness predicate for an `EReal`-valued function: `f` is co-finite if its
epigraph is closed, `f` is proper (never `-∞` and not identically `+∞`), and `epi f` contains no
non-vertical half-lines. -/
def CoFiniteERealFunction
    {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X] (f : X → EReal) : Prop :=
  IsClosed (ERealEpigraph f) ∧ IsProperEReal f ∧ ¬ ERealEpigraphHasNonverticalHalfLine f

/-- A real upper bound on the one-step recession supremum controls every nonnegative point on
the corresponding ray. The proof identifies the recession function with the support function of
`dom f⋆` (Theorem 13.3) and uses positive homogeneity of support functions. -/
lemma helperForCoFiniteERealFunction_recessionRayBound {n : Nat}
    (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (y : Fin n → ℝ) (a : ℝ)
    (hyBound :
      sSup
          {r : EReal |
            ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f,
              r = f (x + y) - f x} ≤ (a : EReal)) :
    ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f,
      ∀ t : ℝ, 0 ≤ t → f (x + t • y) ≤ f x + ((t * a : ℝ) : EReal) := by
  intro x hx t ht
  by_cases ht0 : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let C : Set (Fin n → ℝ) :=
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)
  have hstarProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hCne : C.Nonempty := by
    exact section13_effectiveDomain_nonempty_of_proper hstarProper
  have hCconv : Convex ℝ C := by
    have hstarConv : ConvexFunction (fenchelConjugate n f) :=
      (fenchelConjugate_closedConvex (n := n) (f := f)).2
    have hstarConvOn :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      simpa [ConvexFunction] using hstarConv
    exact effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ)))
      (f := fenchelConjugate n f) hstarConvOn
  have hsupportPos : PositivelyHomogeneous (supportFunctionEReal C) :=
    ((exists_supportFunctionEReal_iff_closedProperConvex_posHom
      (supportFunctionEReal C)).1 ⟨C, hCne, hCconv, rfl⟩).2.2
  have hrec : supportFunctionEReal C = recessionFunction f := by
    exact supportFunctionEReal_effectiveDomain_fenchelConjugate_eq_recession
      f hproper hclosed (recessionFunction f) (fun _ => rfl)
  have hyRec : recessionFunction f y ≤ (a : EReal) := by
    simpa [recessionFunction] using hyBound
  have htyRec : recessionFunction f (t • y) ≤ ((t * a : ℝ) : EReal) := by
    calc
      recessionFunction f (t • y) = supportFunctionEReal C (t • y) := by rw [← hrec]
      _ = (t : EReal) * supportFunctionEReal C y := hsupportPos y t htpos
      _ ≤ (t : EReal) * (a : EReal) :=
        mul_le_mul_of_nonneg_left (by simpa [hrec] using hyRec) (by exact_mod_cast ht)
      _ = ((t * a : ℝ) : EReal) := by rw [EReal.coe_mul]
  have hdiff : f (x + t • y) - f x ≤ recessionFunction f (t • y) := by
    unfold recessionFunction
    exact le_sSup ⟨x, hx, rfl⟩
  have hsub : f (x + t • y) - f x ≤ ((t * a : ℝ) : EReal) := hdiff.trans htyRec
  simpa [add_comm] using
    ((EReal.sub_le_iff_le_add
      (Or.inr (EReal.coe_ne_top (t * a)))
      (Or.inr (EReal.coe_ne_bot (t * a)))).1 hsub)

/-- For a closed proper convex function whose epigraph has no non-vertical half-line, the
recession supremum is `+∞` in every nonzero direction. -/
lemma helperForCoFiniteERealFunction_recessionSup_eq_top_of_noNonverticalHalfLine {n : Nat}
    (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hnoLine : ¬ ERealEpigraphHasNonverticalHalfLine f) :
    ∀ y : Fin n → ℝ, y ≠ 0 →
      sSup
          {r : EReal |
            ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f,
              r = f (x + y) - f x} =
        (⊤ : EReal) := by
  intro y hy
  let q : EReal :=
    sSup
      {r : EReal |
        ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f,
          r = f (x + y) - f x}
  by_contra hqTop
  let a : ℝ := q.toReal
  have hqLe : q ≤ (a : EReal) := EReal.le_coe_toReal hqTop
  rcases section13_effectiveDomain_nonempty_of_proper hproper with ⟨x, hx⟩
  have hfxTop : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hx
  have hfxBot : f x ≠ (⊥ : EReal) := hproper.2.2 x (Set.mem_univ x)
  let b : ℝ := (f x).toReal
  have hfb : (b : EReal) = f x := EReal.coe_toReal hfxTop hfxBot
  apply hnoLine
  refine ⟨(x, b), (y, a), ?_, hy, ?_⟩
  · change f x ≤ (b : EReal)
    exact le_of_eq hfb.symm
  · intro t ht
    change f (x + t • y) ≤ ((b + t * a : ℝ) : EReal)
    have h := helperForCoFiniteERealFunction_recessionRayBound f hclosed hproper y a
      (by simpa [q] using hqLe) x hx t ht
    rw [← hfb] at h
    simpa [EReal.coe_add] using h

/-- The epigraph half-line definition of co-finiteness used in Section 38 implies the Chapter 13
recession-function definition for closed proper convex functions. -/
lemma helperForCoFiniteERealFunction_to_coFiniteConvexFunction {n : Nat}
    (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hcofinite : CoFiniteERealFunction f) :
    CoFiniteConvexFunction f := by
  refine ⟨hclosed, hproper, ?_⟩
  exact helperForCoFiniteERealFunction_recessionSup_eq_top_of_noNonverticalHalfLine
    f hclosed hproper hcofinite.2.2

/-- The Chapter 13 recession-function formulation of co-finiteness implies the equivalent
epigraph formulation used in Section 38. -/
lemma helperForCoFiniteConvexFunction_to_coFiniteERealFunction {n : Nat}
    (f : (Fin n → ℝ) → EReal) (h : CoFiniteConvexFunction f) :
    CoFiniteERealFunction f := by
  rcases h with ⟨hclosed, hproper, hrec⟩
  have hproperE : IsProperEReal f :=
    helperForLemma_38_6_isProperEReal_of_properConvexFunctionOn_univ hproper
  have hEpiClosed : IsClosed (ERealEpigraph f) := by
    have hclosedSub : ∀ α : ℝ, IsClosed {x | f x ≤ (α : EReal)} :=
      (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).1.mp hclosed.2
    have hclosedEpi :
        IsClosed (epigraph (Set.univ : Set (Fin n → ℝ)) f) :=
      (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).2.mp hclosedSub
    have heq : ERealEpigraph f = epigraph (Set.univ : Set (Fin n → ℝ)) f := by
      ext p
      constructor
      · intro hp
        exact ⟨Set.mem_univ p.1, hp⟩
      · intro hp
        exact hp.2
    rw [heq]
    exact hclosedEpi
  have hEpiConvex : Convex ℝ (ERealEpigraph f) := by
    have hconvE : IsERealConvex f := by
      simpa [ConvexFunction, ConvexFunctionOn, IsERealConvex,
        helperForTheorem_38_1_epigraph_eq_univ] using hclosed.1
    exact hconvE
  refine ⟨hEpiClosed, hproperE, ?_⟩
  intro hline
  rcases hline with ⟨p, d, hp, hd, hray⟩
  let e : ((Fin n → ℝ) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (prodLinearEquiv_append (n := n)).toContinuousLinearEquiv
  let C : Set (EuclideanSpace ℝ (Fin (n + 1))) := e '' ERealEpigraph f
  have hCne : C.Nonempty := ⟨e p, ⟨p, hp, rfl⟩⟩
  have hCclosed : IsClosed C := by
    exact e.isClosed_image.mpr hEpiClosed
  have hCconv : Convex ℝ C := by
    exact hEpiConvex.linear_image e.toLinearMap
  have hRayC : ∀ t : ℝ, 0 ≤ t → e p + t • e d ∈ C := by
    intro t ht
    refine ⟨p + t • d, hray t ht, ?_⟩
    simp [e]
  have hdrec : e d ∈ Set.recessionCone C :=
    halfline_mem_recessionCone hCne hCclosed hCconv hRayC
  have hsupLe :
      sSup
          {r : EReal |
            ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f,
              r = f (x + d.1) - f x} ≤ (d.2 : EReal) := by
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hfxTop : f x ≠ (⊤ : EReal) := mem_effectiveDomain_imp_ne_top hx
    have hfxBot : f x ≠ (⊥ : EReal) := hproper.2.2 x (Set.mem_univ x)
    let b : ℝ := (f x).toReal
    have hfb : (b : EReal) = f x := EReal.coe_toReal hfxTop hfxBot
    have hxb : (x, b) ∈ ERealEpigraph f := by
      change f x ≤ (b : EReal)
      exact le_of_eq hfb.symm
    have hbaseC : e (x, b) ∈ C := ⟨(x, b), hxb, rfl⟩
    have hstepC : e (x, b) + (1 : ℝ) • e d ∈ C :=
      hdrec hbaseC (by norm_num)
    have hstepEpi : (x, b) + (1 : ℝ) • d ∈ ERealEpigraph f := by
      rcases hstepC with ⟨q, hq, hqeq⟩
      have hqe : q = (x, b) + (1 : ℝ) • d := by
        apply e.injective
        simpa using hqeq
      simpa [hqe] using hq
    have hineq : f (x + d.1) ≤ ((b + d.2 : ℝ) : EReal) := by
      simpa [ERealEpigraph, Prod.smul_mk, Prod.mk_add_mk] using hstepEpi
    rw [← hfb]
    exact
      (EReal.sub_le_iff_le_add
        (Or.inl (EReal.coe_ne_bot b))
        (Or.inl (EReal.coe_ne_top b))).2 (by
          simpa [EReal.coe_add, add_comm] using hineq)
  have htop := hrec d.1 hd
  rw [htop] at hsupLe
  exact (not_top_le_coe d.2) hsupLe

/-- A closed proper convex function which is co-finite in the Section 38 sense has a Fenchel
conjugate finite on the whole Euclidean space. -/
lemma helperForCoFiniteERealFunction_fenchelConjugate_effectiveDomain_eq_univ {n : Nat}
    (f : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hcofinite : CoFiniteERealFunction f) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) = Set.univ := by
  have hold : CoFiniteConvexFunction f :=
    helperForCoFiniteERealFunction_to_coFiniteConvexFunction f hclosed hproper hcofinite
  exact (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite f hclosed).2 hold |>.1

/-- The recession function of a co-finite convex function has the recession-cone,
positive-homogeneity, and properness properties needed by Corollary 9.2.2. -/
lemma helperForCoFiniteConvexFunction_recession_package {n : Nat}
    (f : (Fin n → ℝ) → EReal) (hf : CoFiniteConvexFunction f) :
    Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) f) =
        epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f) ∧
      PositivelyHomogeneous (recessionFunction f) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (recessionFunction f) := by
  have hdomStar :=
    (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite f hf.1).2 hf
  have hCne :
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)).Nonempty := by
    rw [hdomStar.1]
    exact Set.univ_nonempty
  have hCconv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
    have hstarConv : ConvexFunction (fenchelConjugate n f) :=
      (fenchelConjugate_closedConvex (n := n) (f := f)).2
    exact effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ)))
      (f := fenchelConjugate n f) (by simpa [ConvexFunction] using hstarConv)
  have hsupp := section13_supportFunctionEReal_closedProperConvex_posHom
    (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) hCne hCconv
  have hsuppEq :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) =
        recessionFunction f := by
    exact supportFunctionEReal_effectiveDomain_fenchelConjugate_eq_recession
      f hf.2.1 hf.1 (recessionFunction f) (fun _ => rfl)
  have hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) f) =
        epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f) := by
    let fam : Fin 1 → (Fin n → ℝ) → EReal := fun _ => f
    have hconv : ∀ i : Fin 1,
        Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) (fam i)) := by
      intro i
      simpa [fam] using convex_epigraph_of_convexFunctionOn hf.2.1.1
    have hproper : ∀ i : Fin 1,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fam i) := by
      intro i
      simpa [fam] using hf.2.1
    have hk : ∀ (i : Fin 1) (y : Fin n → ℝ),
        recessionFunction f y =
          sSup {r : EReal | ∃ x, r = fam i (x + y) - fam i x} := by
      intro i y
      simpa [fam] using section16_recessionFunction_eq_sSup_unrestricted (f := f) y
    simpa [fam] using
      (recessionCone_epigraph_eq_epigraph_k (f := fam) (k := recessionFunction f)
        hconv hproper hk (0 : Fin 1))
  refine ⟨hrec, ?_, ?_⟩
  · simpa [hsuppEq] using hsupp.2.2
  · simpa [hsuppEq] using hsupp.2.1

/-- The infimal convolution of two co-finite convex functions is co-finite. -/
lemma coFiniteConvexFunction_infimalConvolution {n : Nat}
    (f g : (Fin n → ℝ) → EReal)
    (hf : CoFiniteConvexFunction f) (hg : CoFiniteConvexFunction g) :
    CoFiniteConvexFunction (infimalConvolution f g) := by
  have hfrec := helperForCoFiniteConvexFunction_recession_package f hf
  have hgrec := helperForCoFiniteConvexFunction_recession_package g hg
  have hpos : ∀ z : Fin n → ℝ, z ≠ 0 →
      recessionFunction f z + recessionFunction g (-z) > (0 : EReal) := by
    intro z hz
    have hfTop : recessionFunction f z = (⊤ : EReal) := by
      simpa [recessionFunction] using hf.2.2 z hz
    rw [hfTop]
    rw [EReal.top_add_of_ne_bot]
    · exact EReal.coe_lt_top 0
    · exact hgrec.2.2.2.2 (-z) (by simp)
  have hmain := infimalConvolution_closed_proper_convex_recession
    hf.1 hg.1 hf.2.1 hg.2.1 hpos hfrec.1 hgrec.1
    hfrec.2.1 hgrec.2.1 hfrec.2.2 hgrec.2.2
  have hclosed := hmain.1
  have hfstar := (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite f hf.1).2 hf
  have hgstar := (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite g hg.1).2 hg
  let fam : Fin 2 → (Fin n → ℝ) → EReal := fun i => if i = 0 then f else g
  have hfam : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fam i) := by
    intro i
    fin_cases i <;> simp [fam, hf.2.1, hg.2.1]
  have hInf : infimalConvolution f g = infimalConvolutionFamily fam := by
    simpa [fam] using infimalConvolution_eq_infimalConvolutionFamily_two f g
  have hconj : fenchelConjugate n (infimalConvolution f g) =
      fun xStar => fenchelConjugate n f xStar + fenchelConjugate n g xStar := by
    rw [hInf, section16_fenchelConjugate_infimalConvolutionFamily fam hfam]
    funext xStar
    simp [fam, Fin.sum_univ_two]
  apply (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite
    (infimalConvolution f g) hclosed).1
  constructor
  · ext xStar
    simp only [effectiveDomain_eq, Set.mem_setOf_eq, Set.mem_univ, true_and, iff_true]
    rw [hconj]
    apply EReal.add_lt_top
    · rw [← lt_top_iff_ne_top]
      simpa [effectiveDomain_eq] using Set.ext_iff.mp hfstar.1 xStar
    · rw [← lt_top_iff_ne_top]
      simpa [effectiveDomain_eq] using Set.ext_iff.mp hgstar.1 xStar
  · intro xStar
    rw [hconj]
    exact (EReal.add_ne_bot_iff).2 ⟨hfstar.2 xStar, hgstar.2 xStar⟩

/-- Definition 38.7.1: A convex (or concave) bifunction `F : ℝ^m → ℝ^n` is *co-finite* if, for every
`u ∈ ℝ^m`, the slice `x ↦ F u x` is a co-finite convex function (closed, proper, and with no
non-vertical half-lines in its epigraph).  Convexity and concavity here are joint graph-function
conditions, as in the book, rather than merely fiberwise conditions. -/
def CoFiniteBifunction {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  (ConvexBifunction F ∧ ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u)) ∨
    (ConcaveBifunction F ∧
      ∀ u : Fin m → ℝ, CoFiniteERealFunction (fun x => -F u x))

/-- Every slice of a jointly convex co-finite bifunction has a Fenchel conjugate with full
effective domain. -/
lemma helperForCoFiniteBifunction_slice_fenchelConjugate_effectiveDomain_eq_univ {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF_cofinite : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u)) :
    ∀ u : Fin m → ℝ,
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (F u)) = Set.univ := by
  intro u
  have hGraph : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hF_joint
  have hsliceConvE : IsERealConvex (F u) := by
    intro p hp q hq a b ha hb hab
    have hp' :
        (Fin.append u p.1, p.2) ∈ ERealEpigraph (bifunctionGraphFunction F) := by
      simpa [ERealEpigraph, bifunctionGraphFunction] using hp
    have hq' :
        (Fin.append u q.1, q.2) ∈ ERealEpigraph (bifunctionGraphFunction F) := by
      simpa [ERealEpigraph, bifunctionGraphFunction] using hq
    have h := hGraph hp' hq' ha hb hab
    have happend :
        a • Fin.append u p.1 + b • Fin.append u q.1 =
          Fin.append u (a • p.1 + b • q.1) := by
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Pi.smul_apply, Pi.add_apply, Fin.append, Fin.addCases_left, smul_eq_mul]
        rw [← add_mul, hab, one_mul]
      · intro j
        simp only [Pi.smul_apply, Pi.add_apply, Fin.append, Fin.addCases_right, smul_eq_mul]
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, happend] at h
    simpa [ERealEpigraph, bifunctionGraphFunction, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul] using h
  have hsliceProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F u) :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      (F u) (hF_cofinite u).2.1 hsliceConvE
  have hsliceConv : ConvexFunction (F u) := by
    simpa [ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hsliceConvE
  have hclosedEpi :
      IsClosed (epigraph (Set.univ : Set (Fin n → ℝ)) (F u)) := by
    have heq : ERealEpigraph (F u) = epigraph (Set.univ : Set (Fin n → ℝ)) (F u) := by
      ext p
      constructor
      · intro hp
        exact ⟨Set.mem_univ p.1, hp⟩
      · intro hp
        exact hp.2
    rw [← heq]
    exact (hF_cofinite u).1
  have hsliceLsc : LowerSemicontinuous (F u) := by
    have hclosedSub : ∀ α : ℝ, IsClosed {x | F u x ≤ (α : EReal)} :=
      (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := F u)).2.mpr hclosedEpi
    exact (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := F u)).1.mpr hclosedSub
  exact helperForCoFiniteERealFunction_fenchelConjugate_effectiveDomain_eq_univ
    (F u) ⟨hsliceConv, hsliceLsc⟩ hsliceProper (hF_cofinite u)

lemma convexBifunction_convexIndicatorBifunction {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ConvexBifunction (convexIndicatorBifunction A) := by
  have hconv :
      IsERealConvex
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          convexIndicatorBifunction A p.1 p.2) := by
    rw [IsERealConvex, ERealEpigraph]
    intro p hp q hq a b ha hb hab
    have hpGraph : p.1.2 = A p.1.1 := by
      by_contra hne
      simp [convexIndicatorBifunction, hne] at hp
    have hqGraph : q.1.2 = A q.1.1 := by
      by_contra hne
      simp [convexIndicatorBifunction, hne] at hq
    have hpHeight : 0 ≤ p.2 := by
      simpa [convexIndicatorBifunction, hpGraph] using hp
    have hqHeight : 0 ≤ q.2 := by
      simpa [convexIndicatorBifunction, hqGraph] using hq
    have hgraph :
        a • p.1.2 + b • q.1.2 = A (a • p.1.1 + b • q.1.1) := by
      rw [hpGraph, hqGraph, map_add, map_smul, map_smul]
    have hheightR : 0 ≤ a * p.2 + b * q.2 := by nlinarith
    have hheight :
        (0 : EReal) ≤ (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) := by
      exact_mod_cast hheightR
    simpa [Prod.smul_mk, Prod.mk_add_mk, convexIndicatorBifunction, hgraph,
      smul_eq_mul] using hheight
  let pairMap :
      (Fin (m + n) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { toFun := fun z =>
        (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
      map_add' := by intro z w; ext i <;> simp
      map_smul' := by intro c z; ext i <;> simp }
  have hgraph : IsERealConvex (bifunctionGraphFunction (convexIndicatorBifunction A)) := by
    simpa [pairMap, bifunctionGraphFunction] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := pairMap)
        (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          convexIndicatorBifunction A p.1 p.2) hconv)
  simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
    helperForTheorem_38_1_epigraph_eq_univ] using hgraph

lemma coFiniteERealFunction_convexIndicatorPoint {n : Nat} (a : Fin n → ℝ) :
    CoFiniteERealFunction (convexIndicatorPoint a) := by
  have hepi :
      ERealEpigraph (convexIndicatorPoint a) =
        ({a} : Set (Fin n → ℝ)) ×ˢ Set.Ici (0 : ℝ) := by
    ext p
    by_cases hp : p.1 = a
    · simp [ERealEpigraph, convexIndicatorPoint, hp]
    · simp [ERealEpigraph, convexIndicatorPoint, hp]
  refine ⟨?_, ?_, ?_⟩
  · rw [hepi]
    exact isClosed_singleton.prod isClosed_Ici
  · constructor
    · intro x
      by_cases hx : x = a <;> simp [convexIndicatorPoint, hx]
    · exact ⟨a, by simp [convexIndicatorPoint]⟩
  · rintro ⟨p, d, hp, hd, hall⟩
    have hpEq : p.1 = a := by
      by_contra hne
      simp [ERealEpigraph, convexIndicatorPoint, hne] at hp
    have h1 := hall 1 zero_le_one
    have h1Eq : (p + (1 : ℝ) • d).1 = a := by
      by_contra hne
      have hne' : p.1 + d.1 ≠ a := by simpa [Prod.smul_mk] using hne
      have hbad : convexIndicatorPoint a (p.1 + d.1) ≤ ((p.2 + d.2 : ℝ) : EReal) := by
        simpa [Prod.smul_mk] using h1
      simp [convexIndicatorPoint, hne'] at hbad
      exact EReal.coe_ne_top _ hbad
    apply hd
    have : p.1 + d.1 = a := by
      simpa [Prod.smul_mk] using h1Eq
    rw [hpEq] at this
    have hz := congrArg (fun z => z - a) this
    simpa using hz

lemma coFiniteERealFunction_convexIndicatorBifunction_slice {m n : Nat}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (u : Fin m → ℝ) :
    CoFiniteERealFunction (convexIndicatorBifunction A u) := by
  have heq : convexIndicatorBifunction A u = convexIndicatorPoint (A u) := by
    funext x
    by_cases hx : x = A u <;> simp [convexIndicatorBifunction, convexIndicatorPoint, hx]
  rw [heq]
  exact coFiniteERealFunction_convexIndicatorPoint (A u)

lemma coFiniteERealFunction_positive_rescale {n : Nat}
    (f : (Fin n → ℝ) → EReal) (hf : CoFiniteERealFunction f)
    (lam : {r : ℝ // 0 < r}) :
    CoFiniteERealFunction
      (fun x => ((lam.1 : ℝ) : EReal) * f (lam.1⁻¹ • x)) := by
  have hlamE : (0 : EReal) < ((lam.1 : ℝ) : EReal) := by exact_mod_cast lam.2
  have hlamTop : ((lam.1 : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hlamBot : ((lam.1 : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hlamNonneg : (0 : EReal) ≤ ((lam.1 : ℝ) : EReal) := le_of_lt hlamE
  let T : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) :=
    fun p => (lam.1⁻¹ • p.1, lam.1⁻¹ * p.2)
  have hmem (p : (Fin n → ℝ) × ℝ) :
      p ∈ ERealEpigraph (fun x => ((lam.1 : ℝ) : EReal) * f (lam.1⁻¹ • x)) ↔
        T p ∈ ERealEpigraph f := by
    change ((lam.1 : ℝ) : EReal) * f (lam.1⁻¹ • p.1) ≤ (p.2 : EReal) ↔
      f (lam.1⁻¹ • p.1) ≤ ((lam.1⁻¹ * p.2 : ℝ) : EReal)
    rw [EReal.coe_mul, EReal.coe_inv, ← EReal.div_eq_inv_mul]
    rw [EReal.le_div_iff_mul_le hlamE hlamTop]
    simp [mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · have hT : Continuous T := by
      exact ((continuous_const_smul (lam.1⁻¹ : ℝ)).comp continuous_fst).prodMk
        (continuous_const.mul continuous_snd)
    have hepi :
        ERealEpigraph (fun x => ((lam.1 : ℝ) : EReal) * f (lam.1⁻¹ • x)) =
          T ⁻¹' ERealEpigraph f := by
      ext p
      exact hmem p
    rw [hepi]
    exact hf.1.preimage hT
  · constructor
    · intro x
      rw [EReal.mul_ne_bot]
      exact ⟨Or.inl hlamBot, Or.inr (hf.2.1.1 _), Or.inl hlamTop, Or.inl hlamNonneg⟩
    · rcases hf.2.1.2 with ⟨x, hx⟩
      refine ⟨lam.1 • x, ?_⟩
      have hinv : lam.1⁻¹ • (lam.1 • x) = x := by
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt lam.2), one_smul]
      change ((lam.1 : ℝ) : EReal) * f (lam.1⁻¹ • (lam.1 • x)) ≠ ⊤
      rw [hinv, EReal.mul_ne_top]
      exact ⟨Or.inl hlamBot, Or.inl hlamNonneg, Or.inl hlamTop, Or.inr hx⟩
  · intro hline
    apply hf.2.2
    rcases hline with ⟨p, d, hp, hd, hall⟩
    refine ⟨T p, T d, (hmem p).mp hp, ?_, ?_⟩
    · dsimp [T]
      intro hz
      apply hd
      have hscale := congrArg (fun z => lam.1 • z) hz
      have hor : lam.1 = 0 ∨ d.1 = 0 := by
        simpa [smul_smul] using hscale
      exact hor.resolve_left (ne_of_gt lam.2)
    · intro t ht
      have hscaled := (hmem (p + t • d)).mp (hall t ht)
      have hTadd : T (p + t • d) = T p + t • T d := by
        apply Prod.ext
        · dsimp [T]
          ext i
          simp [smul_eq_mul]
          ring
        · dsimp [T]
          change lam.1⁻¹ * (p.2 + t * d.2) =
            lam.1⁻¹ * p.2 + t * (lam.1⁻¹ * d.2)
          ring
      rw [← hTadd]
      exact hscaled

lemma convexBifunction_positive_rescale {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hF : ConvexBifunction F)
    (lam : {r : ℝ // 0 < r}) :
    ConvexBifunction (fun u x => ((lam.1 : ℝ) : EReal) * F u (lam.1⁻¹ • x)) := by
  let appendMap :
      ((Fin m → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] (Fin (m + n) → ℝ) :=
    { toFun := fun p => Fin.append p.1 p.2
      map_add' := by
        intro p q
        ext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;>
          simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Fin.append_left,
            Fin.append_right]
      map_smul' := by
        intro c p
        ext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;>
          simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Fin.append_left,
            Fin.append_right, RingHom.id_apply] }
  have hgraph : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hF
  have hpair : IsERealConvex (fun p : (Fin m → ℝ) × (Fin n → ℝ) => F p.1 p.2) := by
    simpa [appendMap, bifunctionGraphFunction] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := appendMap) (g := bifunctionGraphFunction F) hgraph)
  have hscaled :
      IsERealConvex
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((lam.1 : ℝ) : EReal) * F p.1 (lam.1⁻¹ • p.2)) := by
    rw [IsERealConvex, ERealEpigraph]
    rw [IsERealConvex] at hpair
    intro p hp q hq a b ha hb hab
    have hlamE : (0 : EReal) < ((lam.1 : ℝ) : EReal) := by exact_mod_cast lam.2
    have hlamTop : ((lam.1 : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    have hpPre :
        ((p.1.1, lam.1⁻¹ • p.1.2), lam.1⁻¹ * p.2) ∈
          ERealEpigraph (fun z : (Fin m → ℝ) × (Fin n → ℝ) => F z.1 z.2) := by
      change F p.1.1 (lam.1⁻¹ • p.1.2) ≤ ((lam.1⁻¹ * p.2 : ℝ) : EReal)
      rw [EReal.coe_mul, EReal.coe_inv, ← EReal.div_eq_inv_mul]
      rw [EReal.le_div_iff_mul_le hlamE hlamTop]
      simpa [mul_comm] using hp
    have hqPre :
        ((q.1.1, lam.1⁻¹ • q.1.2), lam.1⁻¹ * q.2) ∈
          ERealEpigraph (fun z : (Fin m → ℝ) × (Fin n → ℝ) => F z.1 z.2) := by
      change F q.1.1 (lam.1⁻¹ • q.1.2) ≤ ((lam.1⁻¹ * q.2 : ℝ) : EReal)
      rw [EReal.coe_mul, EReal.coe_inv, ← EReal.div_eq_inv_mul]
      rw [EReal.le_div_iff_mul_le hlamE hlamTop]
      simpa [mul_comm] using hq
    have hcombo := hpair hpPre hqPre ha hb hab
    have hinput :
        a • (p.1.1, lam.1⁻¹ • p.1.2) + b • (q.1.1, lam.1⁻¹ • q.1.2) =
          (a • p.1.1 + b • q.1.1, lam.1⁻¹ • (a • p.1.2 + b • q.1.2)) := by
      apply Prod.ext
      · rfl
      · ext i
        simp [smul_eq_mul]
        ring
    have hcombo' :
        F (a • p.1.1 + b • q.1.1)
            (lam.1⁻¹ • (a • p.1.2 + b • q.1.2)) ≤
          ((a * (lam.1⁻¹ * p.2) + b * (lam.1⁻¹ * q.2) : ℝ) : EReal) := by
      have hcombo0 :
          F (a • (p.1.1, lam.1⁻¹ • p.1.2) + b • (q.1.1, lam.1⁻¹ • q.1.2)).1
              (a • (p.1.1, lam.1⁻¹ • p.1.2) + b • (q.1.1, lam.1⁻¹ • q.1.2)).2 ≤
            ((a * (lam.1⁻¹ * p.2) + b * (lam.1⁻¹ * q.2) : ℝ) : EReal) := by
        simpa [ERealEpigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hcombo
      rw [hinput] at hcombo0
      exact hcombo0
    have hmul := mul_le_mul_of_nonneg_left hcombo' (le_of_lt hlamE)
    have hreal :
        lam.1 * (a * (lam.1⁻¹ * p.2) + b * (lam.1⁻¹ * q.2)) =
          a * p.2 + b * q.2 := by
      field_simp [ne_of_gt lam.2]
    have hereal :
        ((lam.1 : ℝ) : EReal) *
            ((a * (lam.1⁻¹ * p.2) + b * (lam.1⁻¹ * q.2) : ℝ) : EReal) =
          ((a * p.2 + b * q.2 : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [ERealEpigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using
      hmul.trans_eq hereal
  let pairMap :
      (Fin (m + n) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { toFun := fun z =>
        (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
      map_add' := by intro z w; ext i <;> simp
      map_smul' := by intro c z; ext i <;> simp }
  have hout :
      IsERealConvex
        (bifunctionGraphFunction
          (fun u x => ((lam.1 : ℝ) : EReal) * F u (lam.1⁻¹ • x))) := by
    simpa [pairMap, bifunctionGraphFunction] using
      (helperForTheorem_38_4_isERealConvex_precomp_linearMap
        (A := pairMap)
        (g := fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          ((lam.1 : ℝ) : EReal) * F p.1 (lam.1⁻¹ • p.2)) hscaled)
  simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
    helperForTheorem_38_1_epigraph_eq_univ] using hout

/-- The Euclidean-version of the bracket `⟨F u, x*⟩` for a bifunction `F : ℝ^m → ℝ^n → EReal`:
the convex-conjugate value `sup_x (⟨x, x*⟩ - F u x)`. -/
noncomputable def bifunctionLeftPairingInner {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) (xStar : Fin n → ℝ) : EReal :=
  convexConjugateInner (F u) xStar

/-- The adjoint of a convex bifunction is the concave conjugate, in its first variable, of the
left-pairing function. -/
lemma bifunctionAdjointInner_eq_concaveConjugateInner_leftPairing {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (hF : ConvexBifunction F)
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    bifunctionAdjointInner F xStar uStar =
      concaveConjugateInner
        (fun u => bifunctionLeftPairingInner F u xStar) uStar := by
  rw [bifunctionAdjointInner_eq_adjointOfConvexBifunction F hF]
  rw [← textbookBifunctionAdjoint_eq_adjointOfConvexBifunction F hF]
  rw [textbookBifunctionAdjoint_eq_concaveConjugate_pairing]
  rw [concaveConjugateInner_eq_concaveFenchelConjugate]
  simp_rw [bifunctionLeftPairingInner, convexConjugateInner_eq_fenchelConjugate]
  rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
  rw [helperForLemma_31_0_11_concaveFenchelConjugate_eq_iInf]
  simp [sub_eq_add_neg]

/-- For a jointly convex bifunction with co-finite primal slices, every fixed-dual
left-pairing section is closed concave and never takes the value `+∞`. -/
lemma helperForCoFiniteBifunction_leftPairing_closedConcave_and_ne_top {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF_cofinite : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u))
    (xStar : Fin n → ℝ) :
    let phi : (Fin m → ℝ) → EReal :=
      fun u => bifunctionLeftPairingInner F u xStar
    ClosedConcaveFunction phi ∧ ∀ u, phi u ≠ (⊤ : EReal) := by
  have hGraph : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hF_joint
  have hSliceConv : ∀ u : Fin m → ℝ, IsERealConvex (F u) := by
    intro u p hp q hq a b ha hb hab
    have hp' :
        (Fin.append u p.1, p.2) ∈ ERealEpigraph (bifunctionGraphFunction F) := by
      simpa [ERealEpigraph, bifunctionGraphFunction] using hp
    have hq' :
        (Fin.append u q.1, q.2) ∈ ERealEpigraph (bifunctionGraphFunction F) := by
      simpa [ERealEpigraph, bifunctionGraphFunction] using hq
    have h := hGraph hp' hq' ha hb hab
    have happend :
        a • Fin.append u p.1 + b • Fin.append u q.1 =
          Fin.append u (a • p.1 + b • q.1) := by
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Pi.smul_apply, Pi.add_apply, Fin.append, Fin.addCases_left, smul_eq_mul]
        rw [← add_mul, hab, one_mul]
      · intro j
        simp only [Pi.smul_apply, Pi.add_apply, Fin.append, Fin.addCases_right, smul_eq_mul]
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, happend] at h
    simpa [ERealEpigraph, bifunctionGraphFunction, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul] using h
  let Fpacked : FiberwiseProperConvexBifunction m n :=
    { toFun := F
      proper := by
        constructor
        · intro u x
          exact (hF_cofinite u).2.1.1 x
        · rcases (hF_cofinite (0 : Fin m → ℝ)).2.1.2 with ⟨x, hx⟩
          exact ⟨0, x, hx⟩
      convex := hSliceConv }
  have hNegConvex : ConvexFunction
      (fun u : Fin m → ℝ => -fenchelConjugate n (F u) xStar) := by
    simpa [Fpacked] using neg_fenchelConjugate_slice_convexFunction Fpacked hF_joint xStar
  have hPhiNoTop : ∀ u : Fin m → ℝ,
      fenchelConjugate n (F u) xStar ≠ (⊤ : EReal) := by
    intro u
    have hdom :=
      helperForCoFiniteBifunction_slice_fenchelConjugate_effectiveDomain_eq_univ
        F hF_joint hF_cofinite u
    exact mem_effectiveDomain_imp_ne_top (by rw [hdom]; simp)
  have hPhiNoBot : ∀ u : Fin m → ℝ,
      fenchelConjugate n (F u) xStar ≠ (⊥ : EReal) := by
    intro u
    rcases (hF_cofinite u).2.1.2 with ⟨x, hx⟩
    exact helperForTheorem33_1_convexConjugate_ne_bot_of_point
      (f := F u) (x₀ := x) hx xStar
  have hNegFinite : ∀ u : Fin m → ℝ,
      (fun v => -fenchelConjugate n (F v) xStar) u ≠ ⊤ ∧
        (fun v => -fenchelConjugate n (F v) xStar) u ≠ ⊥ := by
    intro u
    constructor
    · simpa using hPhiNoBot u
    · simpa using hPhiNoTop u
  have hNegClosed : ClosedConvexFunction
      (fun u : Fin m → ℝ => -fenchelConjugate n (F u) xStar) :=
    (section13_closedProper_of_convex_finite hNegConvex hNegFinite).1
  have hPairEq : (fun u : Fin m → ℝ => bifunctionLeftPairingInner F u xStar) =
      fun u : Fin m → ℝ => fenchelConjugate n (F u) xStar := by
    funext u
    exact convexConjugateInner_eq_fenchelConjugate (F u) xStar
  refine ⟨?_, ?_⟩
  · rw [hPairEq]
    exact hNegClosed
  · intro u
    rw [hPairEq]
    exact hPhiNoTop u

/-- Negating a concave conjugate gives the Fenchel conjugate of the negated primal
function, precomposed with reflection in the dual variable. -/
lemma section38_neg_concaveConjugate_eq_fenchelConjugate_neg_precomp_neg
    {n : Nat} (phi : (Fin n → ℝ) → EReal) :
    (fun y : Fin n → ℝ => -concaveConjugate phi y) =
      fun y : Fin n → ℝ => fenchelConjugate n (fun x => -phi x) (-y) := by
  exact helperForTheorem_6_30_3_neg_concaveConjugate_eq_fenchel_precomp_neg phi

/-- The Fenchel conjugate of the negative concave conjugate is the reflected Fenchel
biconjugate of the negative primal function. -/
lemma section38_fenchelConjugate_neg_concaveConjugate_eq_reflected_biconjugate
    {n : Nat} (phi : (Fin n → ℝ) → EReal) :
    fenchelConjugate n (fun y : Fin n → ℝ => -concaveConjugate phi y) =
      fun x : Fin n → ℝ =>
        fenchelConjugate n (fenchelConjugate n (fun z => -phi z)) (-x) := by
  rw [section38_neg_concaveConjugate_eq_fenchelConjugate_neg_precomp_neg]
  exact helperForTheorem_21_4_fenchelConjugate_precomp_neg
    (n := n) (g := fenchelConjugate n (fun z => -phi z))

/-- For a closed concave function with no `+∞` values, the reflected biconjugate in the
preceding identity reduces to the reflected negative primal function. -/
lemma section38_fenchelConjugate_neg_concaveConjugate_eq_neg_reflect_of_closed
    {n : Nat} (phi : (Fin n → ℝ) → EReal)
    (hphi : ClosedConcaveFunction phi)
    (hphi_ne_top : ∀ x, phi x ≠ (⊤ : EReal)) :
    fenchelConjugate n (fun y : Fin n → ℝ => -concaveConjugate phi y) =
      fun x : Fin n → ℝ => -phi (-x) := by
  rw [section38_fenchelConjugate_neg_concaveConjugate_eq_reflected_biconjugate]
  have hbiconj :
      fenchelConjugate n (fenchelConjugate n (fun z => -phi z)) =
        fun z => -phi z := by
    exact fenchelConjugate_biconjugate_eq_of_closedConvex n (fun z => -phi z)
      hphi.2 hphi.1 (by
        intro z
        simpa using hphi_ne_top z)
  rw [hbiconj]

/-- The domain-restricted conjugate used in §38 agrees with the unrestricted Chapter 6
concave conjugate. -/
lemma section38_concaveConjugateInner_eq_concaveConjugate
    {n : Nat} (phi : (Fin n → ℝ) → EReal) :
    concaveConjugateInner phi = concaveConjugate phi := by
  funext y
  calc
    concaveConjugateInner phi y = concaveFenchelConjugate phi y := by
      exact concaveConjugateInner_eq_concaveFenchelConjugate phi y
    _ = concaveConjugate phi y := by
      simpa [concaveFenchelConjugate] using
        (helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
          (g := phi) (xStar := y)).symm

/-- For a fixed dual point `xStar`, the Fenchel conjugate of the negative adjoint slice is
the reflected biconjugate of the negative left-pairing slice. -/
lemma section38_fenchelConjugate_neg_adjointSlice_eq_reflected_biconjugate
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : ConvexBifunction F) (xStar : Fin n → ℝ) :
    fenchelConjugate m
        (fun uStar : Fin m → ℝ => -bifunctionAdjointInner F xStar uStar) =
      fun u : Fin m → ℝ =>
        fenchelConjugate m
          (fenchelConjugate m (fun z => -bifunctionLeftPairingInner F z xStar)) (-u) := by
  let phi : (Fin m → ℝ) → EReal := fun u => bifunctionLeftPairingInner F u xStar
  have hadj :
      (fun uStar => bifunctionAdjointInner F xStar uStar) =
        concaveConjugateInner phi := by
    funext uStar
    exact bifunctionAdjointInner_eq_concaveConjugateInner_leftPairing
      F hF xStar uStar
  have hneg :
      (fun uStar => -bifunctionAdjointInner F xStar uStar) =
        (fun uStar => -concaveConjugate phi uStar) := by
    funext uStar
    rw [congrFun hadj uStar, section38_concaveConjugateInner_eq_concaveConjugate]
  rw [hneg]
  exact section38_fenchelConjugate_neg_concaveConjugate_eq_reflected_biconjugate phi

/-- Every fixed first-variable slice of the negative adjoint of a jointly convex co-finite
bifunction is co-finite. -/
lemma helperForCoFiniteBifunction_neg_adjointSlice_coFiniteERealFunction {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF_cofinite : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u))
    (xStar : Fin n → ℝ) :
    CoFiniteERealFunction
      (fun uStar : Fin m → ℝ => -bifunctionAdjointInner F xStar uStar) := by
  let phi : (Fin m → ℝ) → EReal :=
    fun u => bifunctionLeftPairingInner F u xStar
  let q : (Fin m → ℝ) → EReal :=
    fun uStar => -bifunctionAdjointInner F xStar uStar
  have hphi :=
    helperForCoFiniteBifunction_leftPairing_closedConcave_and_ne_top
      F hF_joint hF_cofinite xStar
  have hphiClosed : ClosedConcaveFunction phi := hphi.1
  have hphiNoTop : ∀ u, phi u ≠ (⊤ : EReal) := hphi.2
  have hphiNoBot : ∀ u, phi u ≠ (⊥ : EReal) := by
    intro u
    rcases (hF_cofinite u).2.1.2 with ⟨x, hx⟩
    have h := helperForTheorem33_1_convexConjugate_ne_bot_of_point
      (f := F u) (x₀ := x) hx xStar
    simpa [phi, bifunctionLeftPairingInner,
      convexConjugateInner_eq_fenchelConjugate] using h
  have hqEq : q = fun y : Fin m → ℝ =>
      fenchelConjugate m (fun x => -phi x) (-y) := by
    have hadj :
        (fun uStar => bifunctionAdjointInner F xStar uStar) =
          concaveConjugateInner phi := by
      funext uStar
      exact bifunctionAdjointInner_eq_concaveConjugateInner_leftPairing
        F hF_joint xStar uStar
    calc
      q = fun y => -concaveConjugate phi y := by
        funext y
        simp only [q]
        rw [congrFun hadj y, section38_concaveConjugateInner_eq_concaveConjugate]
      _ = fun y => fenchelConjugate m (fun x => -phi x) (-y) :=
        section38_neg_concaveConjugate_eq_fenchelConjugate_neg_precomp_neg phi
  have hqClosed : ClosedConvexFunction q := by
    let A : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
      (ContinuousLinearEquiv.neg ℝ : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)).toLinearMap
    have hstar : ClosedConvexFunction (fenchelConjugate m (fun x => -phi x)) := by
      have h := fenchelConjugate_closedConvex (n := m) (f := fun x => -phi x)
      exact ⟨h.2, h.1⟩
    have hpre := closedConvexFunction_precomp_linearMap (A := A) hstar
    rw [hqEq]
    simpa [A] using hpre
  have hqStarEq : fenchelConjugate m q = fun u => -phi (-u) := by
    rw [hqEq]
    have hpre := helperForTheorem_21_4_fenchelConjugate_precomp_neg
      (n := m) (g := fenchelConjugate m (fun z => -phi z))
    rw [hpre]
    have hbiconj :
        fenchelConjugate m (fenchelConjugate m (fun z => -phi z)) =
          fun z => -phi z := by
      exact fenchelConjugate_biconjugate_eq_of_closedConvex m (fun z => -phi z)
        hphiClosed.2 hphiClosed.1 (by
          intro z
          simpa using hphiNoTop z)
    rw [hbiconj]
  have hdom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fenchelConjugate m q) = Set.univ := by
    ext u
    rw [hqStarEq]
    simp only [effectiveDomain_eq, Set.mem_setOf_eq, Set.mem_univ, true_and, iff_true]
    refine (lt_top_iff_ne_top).2 ?_
    intro htop
    exact hphiNoBot (-u) (EReal.neg_eq_top_iff.mp htop)
  have hstarNoBot : ∀ u, fenchelConjugate m q u ≠ (⊥ : EReal) := by
    intro u
    rw [hqStarEq]
    simpa using hphiNoTop (-u)
  have hold : CoFiniteConvexFunction q :=
    (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite q hqClosed).1
      ⟨hdom, hstarNoBot⟩
  simpa [q] using helperForCoFiniteConvexFunction_to_coFiniteERealFunction q hold

/-- The Euclidean-version of the bracket `⟨u, G x*⟩` for a bifunction on dual variables
`G : (ℝ^n) → (ℝ^m) → EReal`: the concave-conjugate value
`inf_{u*} (⟨u, u*⟩ - G x* u*)`. -/
noncomputable def bifunctionRightPairingInner {m n : Nat}
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal) (xStar : Fin n → ℝ) (u : Fin m → ℝ) : EReal :=
  concaveConjugateInner (G xStar) u

/-- A jointly convex bifunction with co-finite primal slices has a co-finite adjoint, and the
left and right Fenchel pairings agree. -/
lemma helperForCoFiniteBifunction_adjoint_and_pairing {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF_cofinite : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u)) :
    CoFiniteBifunction (bifunctionAdjointInner F) ∧
      ∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
        bifunctionLeftPairingInner F u xStar =
          bifunctionRightPairingInner (bifunctionAdjointInner F) xStar u := by
  constructor
  · right
    constructor
    · rw [bifunctionAdjointInner_eq_adjointOfConvexBifunction F hF_joint]
      exact (adjointOfConvexBifunction_closedConcave ⟨F, hF_joint⟩).1
    · intro xStar
      exact helperForCoFiniteBifunction_neg_adjointSlice_coFiniteERealFunction
        F hF_joint hF_cofinite xStar
  · intro u xStar
    let phi : (Fin m → ℝ) → EReal :=
      fun v => bifunctionLeftPairingInner F v xStar
    have hphi :=
      helperForCoFiniteBifunction_leftPairing_closedConcave_and_ne_top
        F hF_joint hF_cofinite xStar
    have hphiNoBot : ∀ v, phi v ≠ (⊥ : EReal) := by
      intro v
      rcases (hF_cofinite v).2.1.2 with ⟨x, hx⟩
      have h := helperForTheorem33_1_convexConjugate_ne_bot_of_point
        (f := F v) (x₀ := x) hx xStar
      simpa [phi, bifunctionLeftPairingInner,
        convexConjugateInner_eq_fenchelConjugate] using h
    have hnegFinite : ∀ v,
        (fun z => -phi z) v ≠ (⊤ : EReal) ∧
          (fun z => -phi z) v ≠ (⊥ : EReal) := by
      intro v
      constructor
      · intro hv
        exact hphiNoBot v (EReal.neg_eq_top_iff.mp hv)
      · intro hv
        exact hphi.2 v (EReal.neg_eq_bot_iff.mp hv)
    have hphiProper : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) phi := by
      exact (section13_closedProper_of_convex_finite hphi.1.1 hnegFinite).2
    have hdouble : concaveConjugateInner (concaveConjugateInner phi) = phi := by
      have hbiconj := helperForTheorem_31_1_concave_biconjugate_eq_of_closedConcave
        phi hphi.1 hphiProper
      funext v
      calc
        concaveConjugateInner (concaveConjugateInner phi) v =
            concaveFenchelConjugate (concaveConjugateInner phi) v :=
          concaveConjugateInner_eq_concaveFenchelConjugate _ _
        _ = concaveFenchelConjugate (concaveFenchelConjugate phi) v := by
          congr 1
          funext w
          exact concaveConjugateInner_eq_concaveFenchelConjugate phi w
        _ = phi v := hbiconj v
    have hadj :
        (fun uStar => bifunctionAdjointInner F xStar uStar) =
          concaveConjugateInner phi := by
      funext uStar
      exact bifunctionAdjointInner_eq_concaveConjugateInner_leftPairing
        F hF_joint xStar uStar
    change phi u = concaveConjugateInner
      (fun uStar => bifunctionAdjointInner F xStar uStar) u
    rw [hadj, hdouble]

/-- A jointly convex bifunction with co-finite primal slices has full primal domain, and its
adjoint has full `-∞`-effective domain. -/
lemma helperForCoFiniteBifunction_dom_and_adjointDom_eq_univ {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF_cofinite : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u)) :
    bifunctionDom F = (Set.univ : Set (Fin m → ℝ)) ∧
      bifunctionDomBot (bifunctionAdjointInner F) =
        (Set.univ : Set (Fin n → ℝ)) := by
  constructor
  · ext u
    simp only [bifunctionDom, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (hF_cofinite u).2.1.2
  · ext xStar
    simp only [bifunctionDomBot, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hq := helperForCoFiniteBifunction_neg_adjointSlice_coFiniteERealFunction
      F hF_joint hF_cofinite xStar
    rcases hq.2.1.2 with ⟨uStar, huStar⟩
    refine ⟨uStar, ?_⟩
    intro hbot
    apply huStar
    simp [hbot]

/-- For a closed convex bifunction, full primal domain together with full `-∞`-effective
domain of the adjoint implies co-finiteness in the convex orientation. -/
lemma helperForClosedConvexBifunction_coFinite_of_dom_and_adjointDom_eq_univ {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_closed : ClosedConvexBifunction F)
    (hdomF : bifunctionDom F = (Set.univ : Set (Fin m → ℝ)))
    (hdomAdj : bifunctionDomBot (bifunctionAdjointInner F) =
      (Set.univ : Set (Fin n → ℝ))) :
    ConvexBifunction F ∧ ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u) := by
  refine ⟨hF_closed.1, ?_⟩
  intro u
  have hGraph : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hF_closed.1
  have hsliceConvE : IsERealConvex (F u) := by
    intro p hp q hq a b ha hb hab
    have hp' :
        (Fin.append u p.1, p.2) ∈ ERealEpigraph (bifunctionGraphFunction F) := by
      simpa [ERealEpigraph, bifunctionGraphFunction] using hp
    have hq' :
        (Fin.append u q.1, q.2) ∈ ERealEpigraph (bifunctionGraphFunction F) := by
      simpa [ERealEpigraph, bifunctionGraphFunction] using hq
    have h := hGraph hp' hq' ha hb hab
    have happend :
        a • Fin.append u p.1 + b • Fin.append u q.1 =
          Fin.append u (a • p.1 + b • q.1) := by
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Pi.smul_apply, Pi.add_apply, Fin.append, Fin.addCases_left, smul_eq_mul]
        rw [← add_mul, hab, one_mul]
      · intro j
        simp only [Pi.smul_apply, Pi.add_apply, Fin.append, Fin.addCases_right, smul_eq_mul]
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, happend] at h
    simpa [ERealEpigraph, bifunctionGraphFunction, Prod.smul_mk, Prod.mk_add_mk,
      smul_eq_mul] using h
  have hsliceConv : ConvexFunction (F u) := by
    simpa [ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hsliceConvE
  have hsliceLsc : LowerSemicontinuous (F u) := by
    let freeze : (Fin n → ℝ) → (Fin (m + n) → ℝ) := fun x => Fin.append u x
    have hfreeze : Continuous freeze := by
      simpa [freeze] using
        (Fin.continuous_append m n).comp (continuous_const.prodMk continuous_id)
    have hcomp := hF_closed.2.2.comp_continuous hfreeze
    simpa [freeze, bifunctionGraphFunction] using hcomp
  have hsliceClosed : ClosedConvexFunction (F u) := ⟨hsliceConv, hsliceLsc⟩
  have huDom : u ∈ bifunctionDom F := by
    rw [hdomF]
    trivial
  rcases huDom with ⟨x₀, hx₀⟩
  have hstarNoBot : ∀ xStar : Fin n → ℝ,
      fenchelConjugate n (F u) xStar ≠ (⊥ : EReal) := by
    intro xStar
    exact helperForTheorem33_1_convexConjugate_ne_bot_of_point
      (f := F u) (x₀ := x₀) hx₀ xStar
  have hstarNoTop : ∀ xStar : Fin n → ℝ,
      fenchelConjugate n (F u) xStar ≠ (⊤ : EReal) := by
    intro xStar
    have hxAdjDom : xStar ∈ bifunctionDomBot (bifunctionAdjointInner F) := by
      rw [hdomAdj]
      trivial
    rcases hxAdjDom with ⟨uStar, huStar⟩
    let phi : (Fin m → ℝ) → EReal :=
      fun v => bifunctionLeftPairingInner F v xStar
    have hadj : bifunctionAdjointInner F xStar uStar =
        concaveConjugateInner phi uStar :=
      bifunctionAdjointInner_eq_concaveConjugateInner_leftPairing
        F hF_closed.1 xStar uStar
    have hconjNeBot : concaveConjugate phi uStar ≠ (⊥ : EReal) := by
      rw [← section38_concaveConjugateInner_eq_concaveConjugate phi]
      rw [← hadj]
      exact huStar
    have hphiNoTop : ∀ v, phi v ≠ (⊤ : EReal) := by
      intro v hv
      apply hconjNeBot
      apply bot_unique
      rw [helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
      refine le_trans (iInf_le _ v) ?_
      simp [hv]
    have huPhi := hphiNoTop u
    simpa [phi, bifunctionLeftPairingInner,
      convexConjugateInner_eq_fenchelConjugate] using huPhi
  have hdomStar :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (F u)) =
        Set.univ := by
    ext xStar
    simp only [effectiveDomain_eq, Set.mem_setOf_eq, Set.mem_univ, true_and, iff_true]
    exact (lt_top_iff_ne_top).2 (hstarNoTop xStar)
  have hold : CoFiniteConvexFunction (F u) :=
    (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite (F u) hsliceClosed).1
      ⟨hdomStar, hstarNoBot⟩
  exact helperForCoFiniteConvexFunction_to_coFiniteERealFunction (F u) hold

-- Proof sketch: For the first part, apply the one-variable co-finiteness duality theorem for each
-- slice `x ↦ F u x` to show the corresponding adjoint slice is co-finite and to identify the
-- left/right pairings via the definition of `bifunctionAdjointInner`. For the "Moreover" part,
-- use the domain characterization of co-finite closed convex functions and apply it to slices of
-- `F` and to slices of the adjoint.
/-- Proposition 38.7.2: If `F` is a co-finite convex bifunction from `ℝ^m` to `ℝ^n`, then its
adjoint `F^*` (modeled by `bifunctionAdjointInner F`) is co-finite and satisfies

`⟨F u, x*⟩ = ⟨u, F^* x*⟩` for all `u : ℝ^m` and `x* : ℝ^n`,

where the brackets are modeled by `bifunctionLeftPairingInner` and
`bifunctionRightPairingInner`. Moreover, a closed convex bifunction `F` is co-finite if and only
if `dom F = ℝ^m` and `dom F^* = ℝ^n`, where `dom F` is `bifunctionDom F` and `dom F^*` is modeled
by `bifunctionDomBot (bifunctionAdjointInner F)`. -/
theorem coFiniteBifunction_adjointInner_and_dom_iff {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    ((ConvexBifunction F ∧ ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u)) →
        CoFiniteBifunction (bifunctionAdjointInner F) ∧
          (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
            bifunctionLeftPairingInner F u xStar =
              bifunctionRightPairingInner (bifunctionAdjointInner F) xStar u)) ∧
      (ClosedConvexBifunction F →
        ((ConvexBifunction F ∧ ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u)) ↔
          bifunctionDom F = (Set.univ : Set (Fin m → ℝ)) ∧
            bifunctionDomBot (bifunctionAdjointInner F) = (Set.univ : Set (Fin n → ℝ)))) := by
  constructor
  · rintro ⟨hF_joint, hF_cofinite⟩
    exact helperForCoFiniteBifunction_adjoint_and_pairing F hF_joint hF_cofinite
  · intro hF_closed
    constructor
    · rintro ⟨hF_joint, hF_cofinite⟩
      exact helperForCoFiniteBifunction_dom_and_adjointDom_eq_univ
        F hF_joint hF_cofinite
    · rintro ⟨hdomF, hdomAdj⟩
      exact helperForClosedConvexBifunction_coFinite_of_dom_and_adjointDom_eq_univ
        F hF_closed hdomF hdomAdj

/-- The adjoint identity for the infimal convolution of two jointly convex bifunctions with
co-finite slices.  Co-finiteness makes both parameter domains equal to the whole space, which
supplies the relative-interior qualification in Theorem 38.2. -/
lemma helperForCoFiniteBifunction_infimalConvolution_adjointInner_eq {m n : Nat}
    (F₁ F₂ : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF₁ : ConvexBifunction F₁ ∧ ∀ u : Fin m → ℝ, CoFiniteERealFunction (F₁ u))
    (hF₂ : ConvexBifunction F₂ ∧ ∀ u : Fin m → ℝ, CoFiniteERealFunction (F₂ u)) :
    bifunctionAdjointInner (bifunctionInfimalConvolutionInSecond F₁ F₂) =
      concaveBifunctionInfimalConvolutionInSecond
        (bifunctionAdjointInner F₁) (bifunctionAdjointInner F₂) := by
  have hproper₁ : ProperConvexBifunction F₁ := by
    refine ⟨hF₁.1, ?_⟩
    have hp : IsProperEReal (bifunctionGraphFunction F₁) := by
      constructor
      · intro z
        exact (hF₁.2 (fun i => z (Fin.castAdd n i))).2.1.1
          (fun j => z (Fin.natAdd m j))
      · rcases (hF₁.2 (0 : Fin m → ℝ)).2.1.2 with ⟨x, hx⟩
        exact ⟨Fin.append 0 x, by simpa [bifunctionGraphFunction] using hx⟩
    have hc : IsERealConvex (bifunctionGraphFunction F₁) := by
      simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
        helperForTheorem_38_1_epigraph_eq_univ] using hF₁.1
    exact helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ _
      (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        _ hp hc)
  have hproper₂ : ProperConvexBifunction F₂ := by
    refine ⟨hF₂.1, ?_⟩
    have hp : IsProperEReal (bifunctionGraphFunction F₂) := by
      constructor
      · intro z
        exact (hF₂.2 (fun i => z (Fin.castAdd n i))).2.1.1
          (fun j => z (Fin.natAdd m j))
      · rcases (hF₂.2 (0 : Fin m → ℝ)).2.1.2 with ⟨x, hx⟩
        exact ⟨Fin.append 0 x, by simpa [bifunctionGraphFunction] using hx⟩
    have hc : IsERealConvex (bifunctionGraphFunction F₂) := by
      simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
        helperForTheorem_38_1_epigraph_eq_univ] using hF₂.1
    exact helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ _
      (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        _ hp hc)
  obtain ⟨P₁, hP₁⟩ := fiberwiseProperConvex_of_properConvexBifunction F₁ hproper₁
  obtain ⟨P₂, hP₂⟩ := fiberwiseProperConvex_of_properConvexBifunction F₂ hproper₂
  have hdom₁ : bifunctionDom P₁.toFun = (Set.univ : Set (Fin m → ℝ)) := by
    simpa [hP₁] using
      (helperForCoFiniteBifunction_dom_and_adjointDom_eq_univ F₁ hF₁.1 hF₁.2).1
  have hdom₂ : bifunctionDom P₂.toFun = (Set.univ : Set (Fin m → ℝ)) := by
    simpa [hP₂] using
      (helperForCoFiniteBifunction_dom_and_adjointDom_eq_univ F₂ hF₂.1 hF₂.2).1
  have hri :
      (intrinsicInterior ℝ (bifunctionDom P₁.toFun) ∩
        intrinsicInterior ℝ (bifunctionDom P₂.toFun)).Nonempty := by
    rw [hdom₁, hdom₂]
    have hzeroInterior :
        (0 : Fin m → ℝ) ∈ interior (Set.univ : Set (Fin m → ℝ)) := by
      simpa [interior_univ]
    have hzeroII :
        (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ (Set.univ : Set (Fin m → ℝ)) :=
      (interior_subset_intrinsicInterior (s := (Set.univ : Set (Fin m → ℝ))))
        hzeroInterior
    exact ⟨0, hzeroII, hzeroII⟩
  have h38 :=
    bifunctionAdjoint_infimalConvolution_eq_infimalConvolution_adjoint
      P₁ P₂ (by simpa [hP₁] using hF₁.1) (by simpa [hP₂] using hF₂.1) hri
  have hInf : bifunctionInfimalConvolution P₁ P₂ =
      bifunctionInfimalConvolutionInSecond F₁ F₂ := by
    funext u x
    simp [bifunctionInfimalConvolution, bifunctionInfimalConvolutionInSecond, hP₁, hP₂]
  rw [hInf] at h38
  have hconvInf : ConvexBifunction (bifunctionInfimalConvolutionInSecond F₁ F₂) :=
    bifunctionInfimalConvolutionInSecond_convexBifunction F₁ F₂ hproper₁ hproper₂
  rw [textbookBifunctionAdjoint_eq_adjointOfConvexBifunction
    (bifunctionInfimalConvolutionInSecond F₁ F₂) hconvInf] at h38
  rw [← bifunctionAdjointInner_eq_adjointOfConvexBifunction
    (bifunctionInfimalConvolutionInSecond F₁ F₂) hconvInf] at h38
  rw [hP₁, hP₂] at h38
  rw [textbookBifunctionAdjoint_eq_adjointOfConvexBifunction F₁ hF₁.1,
    textbookBifunctionAdjoint_eq_adjointOfConvexBifunction F₂ hF₂.1] at h38
  rw [← bifunctionAdjointInner_eq_adjointOfConvexBifunction F₁ hF₁.1,
    ← bifunctionAdjointInner_eq_adjointOfConvexBifunction F₂ hF₂.1] at h38
  exact h38

-- Proof sketch: Co-finiteness of each slice is preserved under one-variable infimal convolution,
-- so `u ↦ (F₁ □ F₂) u` is co-finite slice-wise. For the conjugacy identity, apply the bifunction
-- infimal-convolution duality (Theorem 38.2) under the qualification implied by co-finiteness,
-- and rewrite conjugates using `bifunctionAdjointInner` and infimal convolution using
-- `bifunctionInfimalConvolutionInSecond`.
/-- Result after Corollary 38.7.2: If `F₁` and `F₂` are co-finite convex bifunctions from `ℝ^m` to `ℝ^n`,
then their infimal convolution `F₁ □ F₂` is also co-finite and satisfies

`(F₁ □ F₂)^* = F₁^* □ F₂^*`.

In Lean, we model `F₁ □ F₂` as `bifunctionInfimalConvolutionInSecond F₁ F₂` and the conjugate
`F^*` as `bifunctionAdjointInner F`.  The convolution on the adjoint side uses the book's
concave extended-real convention. -/
theorem coFiniteBifunction_infimalConvolutionInSecond_adjointInner {m n : Nat}
    (F₁ F₂ : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF₁ : ConvexBifunction F₁ ∧ ∀ u : Fin m → ℝ, CoFiniteERealFunction (F₁ u))
    (hF₂ : ConvexBifunction F₂ ∧ ∀ u : Fin m → ℝ, CoFiniteERealFunction (F₂ u)) :
    CoFiniteBifunction (bifunctionInfimalConvolutionInSecond F₁ F₂) ∧
      bifunctionAdjointInner (bifunctionInfimalConvolutionInSecond F₁ F₂) =
        concaveBifunctionInfimalConvolutionInSecond
          (bifunctionAdjointInner F₁) (bifunctionAdjointInner F₂) :=
  by
    have hproper₁ : ProperConvexBifunction F₁ := by
      refine ⟨hF₁.1, ?_⟩
      have hp : IsProperEReal (bifunctionGraphFunction F₁) := by
        constructor
        · intro z
          exact (hF₁.2 (fun i => z (Fin.castAdd n i))).2.1.1
            (fun j => z (Fin.natAdd m j))
        · rcases (hF₁.2 (0 : Fin m → ℝ)).2.1.2 with ⟨x, hx⟩
          exact ⟨Fin.append 0 x, by simpa [bifunctionGraphFunction] using hx⟩
      have hc : IsERealConvex (bifunctionGraphFunction F₁) := by
        simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
          helperForTheorem_38_1_epigraph_eq_univ] using hF₁.1
      exact helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ _
        (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
          _ hp hc)
    have hproper₂ : ProperConvexBifunction F₂ := by
      refine ⟨hF₂.1, ?_⟩
      have hp : IsProperEReal (bifunctionGraphFunction F₂) := by
        constructor
        · intro z
          exact (hF₂.2 (fun i => z (Fin.castAdd n i))).2.1.1
            (fun j => z (Fin.natAdd m j))
        · rcases (hF₂.2 (0 : Fin m → ℝ)).2.1.2 with ⟨x, hx⟩
          exact ⟨Fin.append 0 x, by simpa [bifunctionGraphFunction] using hx⟩
      have hc : IsERealConvex (bifunctionGraphFunction F₂) := by
        simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
          helperForTheorem_38_1_epigraph_eq_univ] using hF₂.1
      exact helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ _
        (helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
          _ hp hc)
    obtain ⟨P₁, hP₁⟩ := fiberwiseProperConvex_of_properConvexBifunction F₁ hproper₁
    obtain ⟨P₂, hP₂⟩ := fiberwiseProperConvex_of_properConvexBifunction F₂ hproper₂
    have hsliceOld₁ : ∀ u : Fin m → ℝ, CoFiniteConvexFunction (F₁ u) := by
      intro u
      have hcE : IsERealConvex (F₁ u) := by
        simpa [hP₁] using P₁.convex u
      have hc : ConvexFunction (F₁ u) := by
        simpa [ConvexFunction, ConvexFunctionOn, IsERealConvex,
          helperForTheorem_38_1_epigraph_eq_univ] using hcE
      have hp : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F₁ u) :=
        helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
          (F₁ u) (hF₁.2 u).2.1 hcE
      have hepi : IsClosed (epigraph (Set.univ : Set (Fin n → ℝ)) (F₁ u)) := by
        have heq : ERealEpigraph (F₁ u) =
            epigraph (Set.univ : Set (Fin n → ℝ)) (F₁ u) := by
          ext p
          constructor
          · intro hp'
            exact ⟨Set.mem_univ p.1, hp'⟩
          · intro hp'
            exact hp'.2
        rw [← heq]
        exact (hF₁.2 u).1
      have hlsc : LowerSemicontinuous (F₁ u) :=
        (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := F₁ u)).1.mpr
          ((lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := F₁ u)).2.mpr hepi)
      exact helperForCoFiniteERealFunction_to_coFiniteConvexFunction
        (F₁ u) ⟨hc, hlsc⟩ hp (hF₁.2 u)
    have hsliceOld₂ : ∀ u : Fin m → ℝ, CoFiniteConvexFunction (F₂ u) := by
      intro u
      have hcE : IsERealConvex (F₂ u) := by
        simpa [hP₂] using P₂.convex u
      have hc : ConvexFunction (F₂ u) := by
        simpa [ConvexFunction, ConvexFunctionOn, IsERealConvex,
          helperForTheorem_38_1_epigraph_eq_univ] using hcE
      have hp : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F₂ u) :=
        helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
          (F₂ u) (hF₂.2 u).2.1 hcE
      have hepi : IsClosed (epigraph (Set.univ : Set (Fin n → ℝ)) (F₂ u)) := by
        have heq : ERealEpigraph (F₂ u) =
            epigraph (Set.univ : Set (Fin n → ℝ)) (F₂ u) := by
          ext p
          constructor
          · intro hp'
            exact ⟨Set.mem_univ p.1, hp'⟩
          · intro hp'
            exact hp'.2
        rw [← heq]
        exact (hF₂.2 u).1
      have hlsc : LowerSemicontinuous (F₂ u) :=
        (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := F₂ u)).1.mpr
          ((lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := F₂ u)).2.mpr hepi)
      exact helperForCoFiniteERealFunction_to_coFiniteConvexFunction
        (F₂ u) ⟨hc, hlsc⟩ hp (hF₂.2 u)
    refine ⟨?_, helperForCoFiniteBifunction_infimalConvolution_adjointInner_eq
      F₁ F₂ hF₁ hF₂⟩
    left
    refine ⟨bifunctionInfimalConvolutionInSecond_convexBifunction
      F₁ F₂ hproper₁ hproper₂, ?_⟩
    intro u
    have hold := coFiniteConvexFunction_infimalConvolution
      (F₁ u) (F₂ u) (hsliceOld₁ u) (hsliceOld₂ u)
    have hnew := helperForCoFiniteConvexFunction_to_coFiniteERealFunction
      (infimalConvolution (F₁ u) (F₂ u)) hold
    have heq :
        bifunctionInfimalConvolutionInSecond F₁ F₂ u =
          infimalConvolution (F₁ u) (F₂ u) := by
      funext x
      rw [infimalConvolution_eq_iInf_second]
      simp only [bifunctionInfimalConvolutionInSecond]
      apply iInf_congr
      intro z
      rw [add_comm]
    simpa [heq] using hnew
-- Proof sketch: For each `u`, apply stability of co-finiteness of one-variable convex functions
-- under the positive rescaling `x ↦ lam.1⁻¹ • x` and scaling of function values by `lam.1`, which
-- is exactly the slice operation defining `bifunctionScalarMultiple`. Combine this slice-wise
-- result with `isFiberwiseConvexBifunction_scalarMultiple` to produce the convex branch of
-- `CoFiniteBifunction`.
/-- Proposition 38.7.4: If `F` is a co-finite convex bifunction from `ℝ^m` to `ℝ^n`, then for any
`λ > 0`, the scalar multiple `Fλ` (Definition 38.2.2, modeled by `bifunctionScalarMultiple`) is
also co-finite (Definition 38.7.1, modeled by `CoFiniteBifunction`). -/
theorem coFiniteBifunction_scalarMultiple {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u))
    (lam : {r : ℝ // 0 < r}) :
    CoFiniteBifunction
      (fun u x => ((lam.1 : ℝ) : EReal) * F u (lam.1⁻¹ • x)) :=
  by
    left
    exact ⟨convexBifunction_positive_rescale F hF_joint lam,
      fun u => coFiniteERealFunction_positive_rescale (F u) (hF u) lam⟩

lemma bifunctionEffectiveDomain_eq_bifunctionDom {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    bifunctionEffectiveDomain F = bifunctionDom F := by
  ext u
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, lt_top_iff_ne_top.mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, lt_top_iff_ne_top.mpr hx⟩

/-- Joint convexity and co-finite slices imply properness of the graph function. -/
lemma properConvexBifunction_of_joint_cofinite {m n : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u)) :
    ProperConvexBifunction F := by
  have hp : IsProperEReal (bifunctionGraphFunction F) := by
    constructor
    · intro z
      exact (hF (fun i => z (Fin.castAdd n i))).2.1.1
        (fun j => z (Fin.natAdd m j))
    · rcases (hF 0).2.1.2 with ⟨x, hx⟩
      refine ⟨Fin.append 0 x, ?_⟩
      change F (fun i => Fin.append 0 x (Fin.castAdd n i))
          (fun j => Fin.append 0 x (Fin.natAdd m j)) ≠ ⊤
      have hleft : (fun i => Fin.append (0 : Fin m → ℝ) x (Fin.castAdd n i)) = 0 := by
        ext i
        simp
      have hright : (fun j => Fin.append (0 : Fin m → ℝ) x (Fin.natAdd m j)) = x := by
        ext j
        simp
      rw [hleft, hright]
      exact hx
  have hc : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hF_joint
  have hpc :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      (bifunctionGraphFunction F) hp hc
  exact ⟨hF_joint,
    helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
      (f := bifunctionGraphFunction F) hpc⟩

private lemma coFiniteSlice_closed {n : Nat} (f : (Fin n → ℝ) → EReal)
    (hconv : IsERealConvex f) (hcof : CoFiniteERealFunction f) :
    ClosedConvexFunction f := by
  have hc : ConvexFunction f := by
    simpa [ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hconv
  have hepi : IsClosed (epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    have heq : ERealEpigraph f = epigraph (Set.univ : Set (Fin n → ℝ)) f := by
      ext p
      constructor
      · intro hp
        exact ⟨Set.mem_univ p.1, hp⟩
      · intro hp
        exact hp.2
    rw [← heq]
    exact hcof.1
  have hlsc : LowerSemicontinuous f :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).1.mpr
      ((lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := f)).2.mpr hepi)
  exact ⟨hc, hlsc⟩

/-- A jointly convex bifunction with co-finite slices is globally closed convex. -/
lemma closedConvexBifunction_of_coFiniteSlices
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : ConvexBifunction F)
    (hcof : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u)) :
    ClosedConvexBifunction F := by
  have hgraphProper : IsProperEReal (bifunctionGraphFunction F) := by
    constructor
    · intro z
      exact (hcof (fun i => z (Fin.castAdd n i))).2.1.1
        (fun j => z (Fin.natAdd m j))
    · rcases (hcof (0 : Fin m → ℝ)).2.1.2 with ⟨x, hx⟩
      exact ⟨Fin.append 0 x, by simpa [bifunctionGraphFunction] using hx⟩
  have hgraphConvE : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hF
  have hgraphPC : ProperConvexFunctionOn
      (Set.univ : Set (Fin (m + n) → ℝ)) (bifunctionGraphFunction F) :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      (bifunctionGraphFunction F) hgraphProper hgraphConvE
  have hproper : ProperConvexBifunction F := ⟨hF,
    helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
      (bifunctionGraphFunction F) hgraphPC⟩
  obtain ⟨P, hP⟩ := fiberwiseProperConvex_of_properConvexBifunction F hproper
  have hgraphJensen : ConvexERealFunction (bifunctionGraphFunction F) :=
    (helperForText_26_4_0_2_properConvexERealFunction_of_properConvexFunctionOn hgraphPC).2
  have hFold : IsConvexBifunction F := by
    intro p q a b ha hb hab
    have happ :
        a • Fin.append p.1 p.2 + b • Fin.append q.1 q.2 =
          Fin.append (a • p.1 + b • q.1) (a • p.2 + b • q.2) := by
      ext i
      cases i using Fin.addCases with
      | left i => simp
      | right i => simp
    have hj := hgraphJensen
      (x := Fin.append p.1 p.2) (y := Fin.append q.1 q.2) ha hb hab
    simpa [graphFunction, bifunctionGraphFunction, Prod.smul_mk, Prod.mk_add_mk,
      happ] using hj
  let BF : BundledConvexBifunction m n := ⟨F, hFold⟩
  have hdom : bifunctionEffectiveDomain BF.1 =
      (Set.univ : Set (Fin m → ℝ)) := by
    rw [bifunctionEffectiveDomain_eq_bifunctionDom]
    simpa [BF] using
      (helperForCoFiniteBifunction_dom_and_adjointDom_eq_univ F hF hcof).1
  have hsliceClosed : ∀ u : Fin m → ℝ, ClosedConvexFunction (F u) := by
    intro u
    exact coFiniteSlice_closed (F u) (by simpa [hP] using P.convex u) (hcof u)
  let coord : (Fin (m + n) → ℝ) → EReal :=
    helperForTheorem_6_29_4_coordinateGraphFunction BF
  have hcoordProper : IsProperEReal coord := by
    simpa [coord, BF, helperForTheorem_6_29_4_coordinateGraphFunction,
      bifunctionGraphFunction] using hgraphProper
  have hcoordConv : ConvexFunction coord := by
    simpa [coord] using helperForTheorem_6_29_4_coordinateGraphFunction_convex BF
  have hcoordConvE : IsERealConvex coord := by
    simpa [ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hcoordConv
  have hcoordPC : ProperConvexFunctionOn
      (Set.univ : Set (Fin (m + n) → ℝ)) coord :=
    helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
      coord hcoordProper hcoordConvE
  have hclosureEq : convexFunctionClosure coord = coord := by
    funext z
    let u : Fin m → ℝ := fun i => z (Fin.castAdd n i)
    let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
    have hz : Fin.append u x = z := by
      ext i
      cases i using Fin.addCases with
      | left i => simp [u]
      | right i => simp [x]
    have hu : u ∈ euclideanRelativeInterior_fin m
        (bifunctionEffectiveDomain BF.1) := by
      rw [hdom,
        helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
      exact (interior_subset_intrinsicInterior
        (s := (Set.univ : Set (Fin m → ℝ)))) (by simp)
    have hsection :=
      (theorem_29_4_convex_bifunction_closure_section_and_domain BF).1 u hu
    have hsliceEq : convexFunctionClosure (F u) = F u :=
      convexFunctionClosure_eq_of_closedConvexFunction (hsliceClosed u)
        (hcof u).2.1.1
    rw [hsliceEq] at hsection
    have hxEq := congrFun hsection x
    simpa [coord, helperForTheorem_6_29_4_define_section29_bifunctionClosure,
      helperForTheorem_6_29_4_coordinateGraphFunction, BF, hz] using hxEq
  have hclosureClosed : ClosedConvexFunction (convexFunctionClosure coord) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := coord) hcoordPC).1.1
  have hcoordClosed : ClosedConvexFunction coord := by
    simpa [hclosureEq] using hclosureClosed
  refine ⟨hF, ?_⟩
  simpa [coord, BF, helperForTheorem_6_29_4_coordinateGraphFunction,
    bifunctionGraphFunction] using hcoordClosed

set_option synthInstance.maxHeartbeats 80000 in
/-- The adjoint of a co-finite composition is the supremal composition of the adjoints. -/
lemma cofinite_compose_adjoint_identity {m n p : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u))
    (G : (Fin n → ℝ) → (Fin p → ℝ) → EReal)
    (hG_joint : ConvexBifunction G)
    (hG : ∀ x : Fin n → ℝ, CoFiniteERealFunction (G x)) :
    bifunctionAdjointInner (bifunctionComposeInfGeneric G F) =
      bifunctionComposeSup (bifunctionAdjointInner F) (bifunctionAdjointInner G) := by
  have hFproper0 := properConvexBifunction_of_joint_cofinite F hF_joint hF
  have hGproper0 := properConvexBifunction_of_joint_cofinite G hG_joint hG
  obtain ⟨Fpkg, hFpkg⟩ := fiberwiseProperConvex_of_properConvexBifunction F hFproper0
  obtain ⟨Gpkg, hGpkg⟩ := fiberwiseProperConvex_of_properConvexBifunction G hGproper0
  subst F
  subst G
  have hFproper : ProperConvexBifunction Fpkg.toFun := hFproper0
  have hGproper : ProperConvexBifunction Gpkg.toFun := hGproper0
  have hdomG : bifunctionDom Gpkg.toFun = (Set.univ : Set (Fin n → ℝ)) :=
    (helperForCoFiniteBifunction_dom_and_adjointDom_eq_univ
      Gpkg.toFun hG_joint hG).1
  let D := effectiveDomain (Set.univ : Set (Fin (m + n) → ℝ))
    (bifunctionGraphFunction Fpkg.toFun)
  have hDconv : Convex ℝ D := by
    exact effectiveDomain_convex (S := (Set.univ : Set (Fin (m + n) → ℝ)))
      (f := bifunctionGraphFunction Fpkg.toFun) (by simpa [ConvexFunction] using hF_joint)
  have hsetEq : bifunctionDomBot (bifunctionInverse Fpkg.toFun) =
      projLamLinearMap '' D := by
    rw [helperForCorollary_38_5_1_bifunctionDomBot_inverse_eq_exists_ne_top]
    ext x
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨Fin.append u x, ?_, ?_⟩
      · simpa [D, effectiveDomain_eq, bifunctionGraphFunction] using
          (lt_top_iff_ne_top.2 hu)
      · simp [projLamLinearMap]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨projXLinearMap z, ?_⟩
      have hz' :
          Fpkg.toFun (fun i => z (Fin.castAdd n i))
              (fun j => z (Fin.natAdd m j)) < ⊤ := by
        simpa [D, effectiveDomain_eq, bifunctionGraphFunction] using hz
      simpa [D, effectiveDomain_eq, bifunctionGraphFunction,
        projXLinearMap, projLamLinearMap] using (lt_top_iff_ne_top.1 hz')
  have hSconv : Convex ℝ (bifunctionDomBot (bifunctionInverse Fpkg.toFun)) := by
    rw [hsetEq]
    exact hDconv.linear_image projLamLinearMap
  have hSne : (bifunctionDomBot (bifunctionInverse Fpkg.toFun)).Nonempty := by
    rcases (hF 0).2.1.2 with ⟨x, hx⟩
    rw [helperForCorollary_38_5_1_bifunctionDomBot_inverse_eq_exists_ne_top]
    exact ⟨x, 0, hx⟩
  rcases Set.Nonempty.intrinsicInterior hSconv hSne with ⟨x0, hx0⟩
  have hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse Fpkg.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom Gpkg.toFun)).Nonempty := by
    have hxUniv : x0 ∈ intrinsicInterior ℝ
        (Set.univ : Set (Fin n → ℝ)) := by
      rw [← helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
      exact helperForTheorem_31_5_mem_euclideanRelativeInterior_univ x0
    refine ⟨x0, hx0, ?_⟩
    rw [hdomG]
    exact hxUniv
  have hComposeConvex : ConvexBifunction (bifunctionCompose Gpkg Fpkg) :=
    (theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
      Fpkg Gpkg hFproper hGproper).1
  have hComposeConvexRaw :
      ConvexBifunction (bifunctionComposeInfGeneric Gpkg.toFun Fpkg.toFun) := by
    simpa [bifunctionComposeInfGeneric, bifunctionCompose] using hComposeConvex
  have hpack :=
    helperForCorollary_38_5_1_packagedComposeSup_eq_packagedAdjointCompose_of_theorem_hri
      Fpkg Gpkg hFproper hGproper hComposeConvex hri
  rw [bifunctionAdjointInner_eq_adjointOfConvexBifunction
    (bifunctionComposeInfGeneric Gpkg.toFun Fpkg.toFun) hComposeConvexRaw]
  rw [bifunctionAdjointInner_eq_adjointOfConvexBifunction Fpkg.toFun hF_joint]
  rw [bifunctionAdjointInner_eq_adjointOfConvexBifunction Gpkg.toFun hG_joint]
  exact hpack.symm

/-- The first-variable domain of a proper convex bifunction is nonempty and convex. -/
lemma properConvexBifunction_dom_convex_nonempty {n p : Nat}
    (H : (Fin n → ℝ) → (Fin p → ℝ) → EReal)
    (hH : ProperConvexBifunction H) :
    Convex ℝ (bifunctionDom H) ∧ (bifunctionDom H).Nonempty := by
  let D := effectiveDomain (Set.univ : Set (Fin (n + p) → ℝ))
    (bifunctionGraphFunction H)
  have hDconv : Convex ℝ D := by
    exact effectiveDomain_convex (S := (Set.univ : Set (Fin (n + p) → ℝ)))
      (f := bifunctionGraphFunction H) (by simpa [ConvexFunction] using hH.1)
  let proj : (Fin (n + p) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun z i => z (Fin.castAdd p i)
      map_add' := by intro z w; ext i; simp
      map_smul' := by intro c z; ext i; simp }
  have hDomEq : bifunctionDom H = proj '' D := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Fin.append x y, ?_, ?_⟩
      · simpa [D, effectiveDomain_eq, bifunctionGraphFunction] using
          (lt_top_iff_ne_top.2 hy)
      · ext i
        simp [proj]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(fun j => z (Fin.natAdd n j)), ?_⟩
      have hz' : H (fun i => z (Fin.castAdd p i))
          (fun j => z (Fin.natAdd n j)) < ⊤ := by
        simpa [D, effectiveDomain_eq, bifunctionGraphFunction] using hz
      exact (lt_top_iff_ne_top.1 hz')
  constructor
  · rw [hDomEq]
    exact hDconv.linear_image proj
  · rcases hH.2.1.2 with ⟨z, hz⟩
    refine ⟨(fun i => z (Fin.castAdd p i)), ?_⟩
    refine ⟨(fun j => z (Fin.natAdd n j)), ?_⟩
    simpa [bifunctionGraphFunction] using hz

/-- Build the Corollary 38.5.1 qualification entirely in finite Euclidean
packaged coordinates. -/
lemma cofinite_packaged_hri {m n p : Nat}
    (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hFproper : ProperConvexBifunction F.toFun)
    (hGproper : ProperConvexBifunction G.toFun)
    (hGclosed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hFadjDom : bifunctionDomBot (bifunctionAdjointInner F.toFun) = Set.univ) :
    (intrinsicInterior ℝ
          (bifunctionDomBot
            (adjointOfConvexBifunction ⟨F.toFun, hFproper.1⟩)) ∩
      intrinsicInterior ℝ
          (bifunctionDom
            (bifunctionInverse
              (adjointOfConvexBifunction ⟨G.toFun, hGproper.1⟩)))).Nonempty := by
  have hLeftEq :
      bifunctionDomBot (adjointOfConvexBifunction ⟨F.toFun, hFproper.1⟩) =
        (Set.univ : Set (Fin n → ℝ)) := by
    rw [← bifunctionAdjointInner_eq_adjointOfConvexBifunction F.toFun hFproper.1]
    exact hFadjDom
  have hAdjG := helperForCorollary_38_5_1_packagedAdjoint_closedProperConcave
    G hGproper hGclosed
  obtain ⟨H, hHeq, hHproper⟩ :=
    helperForCorollary_38_5_1_packagedAdjointInverse_fiberwiseProperConvex
      (adjointOfConvexBifunction ⟨G.toFun, hGproper.1⟩) hAdjG.1 hAdjG.2
  have hHdom := properConvexBifunction_dom_convex_nonempty H.toFun hHproper
  have hRightConv : Convex ℝ
      (bifunctionDom
        (bifunctionInverse (adjointOfConvexBifunction ⟨G.toFun, hGproper.1⟩))) := by
    rw [← hHeq]
    exact hHdom.1
  have hRightNe :
      (bifunctionDom
        (bifunctionInverse
          (adjointOfConvexBifunction ⟨G.toFun, hGproper.1⟩))).Nonempty := by
    rw [← hHeq]
    exact hHdom.2
  rcases Set.Nonempty.intrinsicInterior hRightConv hRightNe with ⟨x, hx⟩
  refine ⟨x, ?_, hx⟩
  rw [hLeftEq]
  exact interior_subset_intrinsicInterior (s := (Set.univ : Set (Fin n → ℝ)))
    (by simp [interior_univ])

/-- Recover product lower semicontinuity from a packaged Euclidean
qualification, without forming an intrinsic-interior statement on the current dual. -/
lemma reversedDual_closedness_of_packaged_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hFproper : ProperConvexBifunction F.toFun)
    (hGproper : ProperConvexBifunction G.toFun)
    (hFclosed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hGclosed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ
            (bifunctionDomBot
              (adjointOfConvexBifunction ⟨F.toFun, hFproper.1⟩)) ∩
          intrinsicInterior ℝ
            (bifunctionDom
              (bifunctionInverse
                (adjointOfConvexBifunction ⟨G.toFun, hGproper.1⟩)))).Nonempty) :
    IsProductLowerSemicontinuousBifunction (bifunctionCompose G F) := by
  rcases
      helperForCorollary_38_5_1_reversedDual_theorem38_5_application
        (F := F) (G := G) (hF_properConvex := hFproper)
        (hG_properConvex := hGproper) (hF_closed := hFclosed)
        (hG_closed := hGclosed) hri with
    ⟨FdualInv, GdualInv, hFdualInv_eq, hFdualInv_proper, hGdualInv_eq,
      hGdualInv_proper, hReversedEq, _hReversedAttainment⟩
  have hReversedConvex :
      ConvexBifunction (bifunctionCompose GdualInv FdualInv) :=
    (theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
      (F := FdualInv) (G := GdualInv) hFdualInv_proper hGdualInv_proper).1
  have hFBiadjEq : biadjointOfConvexBifunction ⟨F.toFun, hFproper.1⟩ = F.toFun :=
    (helperForCorollary_38_5_1_closedProper_biadjoint_rewrites
      (F := F) (G := G) (hF_properConvex := hFproper)
      (hG_properConvex := hGproper) (hF_closed := hFclosed)
      (hG_closed := hGclosed)).1
  have hGBiadjEq : biadjointOfConvexBifunction ⟨G.toFun, hGproper.1⟩ = G.toFun :=
    (helperForCorollary_38_5_1_closedProper_biadjoint_rewrites
      (F := F) (G := G) (hF_properConvex := hFproper)
      (hG_properConvex := hGproper) (hF_closed := hFclosed)
      (hG_closed := hGclosed)).2
  have hPackagedAdjointEq :
      adjointOfConvexBifunction ⟨bifunctionCompose GdualInv FdualInv, hReversedConvex⟩ =
        bifunctionInverse (bifunctionCompose G F) := by
    funext y u
    calc
      adjointOfConvexBifunction
          ⟨bifunctionCompose GdualInv FdualInv, hReversedConvex⟩ y u =
        bifunctionAdjoint (bifunctionCompose GdualInv FdualInv)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) := by
            exact congrFun (congrFun
              (helperForCorollary_38_5_1_vectorizedAdjoint_eq_packagedAdjoint_of_convex
                (F := bifunctionCompose GdualInv FdualInv) hReversedConvex) y) u
      _ = bifunctionComposeSupGeneric (bifunctionAdjoint FdualInv.toFun)
          (bifunctionAdjoint GdualInv.toFun)
          (dotProductEquiv ℝ (Fin p) (-y))
          (dotProductEquiv ℝ (Fin m) (-u)) := by rw [hReversedEq]
      _ = - bifunctionCompose G F u y := by
            exact
              helperForCorollary_38_5_1_reversedDual_output_rewrite_at_primalPair
                (F := F) (G := G) (hF_properConvex := hFproper)
                (hG_properConvex := hGproper) (hFdualInv_eq := hFdualInv_eq)
                (hFdualInv_proper := hFdualInv_proper)
                (hGdualInv_eq := hGdualInv_eq)
                (hGdualInv_proper := hGdualInv_proper)
                (hFBiadjEq := hFBiadjEq) (hGBiadjEq := hGBiadjEq) u y
      _ = bifunctionInverse (bifunctionCompose G F) y u := by rfl
  have hClosedPackaged :
      ClosedConcaveBifunction
        (adjointOfConvexBifunction
          ⟨bifunctionCompose GdualInv FdualInv, hReversedConvex⟩) :=
    ((adjoint_bifunction_closure_properness_biconjugation_and_polyhedrality
      (F := bifunctionCompose GdualInv FdualInv)).1 hReversedConvex).1
  have hClosedInverseCompose :
      ClosedConcaveBifunction (bifunctionInverse (bifunctionCompose G F)) := by
    simpa [hPackagedAdjointEq] using hClosedPackaged
  have hInvInvCompose :
      bifunctionInverse (bifunctionInverse (bifunctionCompose G F)) =
        bifunctionCompose G F := by
    funext u y
    simp [bifunctionInverse]
  rw [← hInvInvCompose]
  exact helperForCorollary_38_5_1_inverse_closedConcave_is_productLowerSemicontinuous
    (K := bifunctionInverse (bifunctionCompose G F)) hClosedInverseCompose

/-- The packaged qualification supplies closedness of a co-finite composition. -/
lemma cofinite_compose_closed_packaged_route {m n p : Nat}
    (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (hFproper : ProperConvexBifunction F.toFun)
    (hGproper : ProperConvexBifunction G.toFun)
    (hFclosed : IsProductLowerSemicontinuousBifunction F.toFun)
    (hGclosed : IsProductLowerSemicontinuousBifunction G.toFun)
    (hFadjDom : bifunctionDomBot (bifunctionAdjointInner F.toFun) = Set.univ) :
    IsProductLowerSemicontinuousBifunction (bifunctionCompose G F) := by
  exact reversedDual_closedness_of_packaged_hri F G hFproper hGproper hFclosed hGclosed
    (cofinite_packaged_hri F G hFproper hGproper hGclosed hFadjDom)

set_option maxHeartbeats 2000000 in
/-- The current dual domain of the inverse packaged adjoint is nonempty and convex. -/
lemma packagedAdjointInverse_currentDom_convex_nonempty {n p : Nat}
    (Gpkg : FiberwiseProperConvexBifunction n p)
    (hGproper : ProperConvexBifunction Gpkg.toFun)
    (hGclosed : IsProductLowerSemicontinuousBifunction Gpkg.toFun) :
    Convex ℝ (bifunctionDom (bifunctionInverse (bifunctionAdjoint Gpkg.toFun))) ∧
      (bifunctionDom (bifunctionInverse (bifunctionAdjoint Gpkg.toFun))).Nonempty := by
  have hAdjG := helperForCorollary_38_5_1_packagedAdjoint_closedProperConcave
    Gpkg hGproper hGclosed
  obtain ⟨Hpkg, hHeq, hHproper⟩ :=
    helperForCorollary_38_5_1_packagedAdjointInverse_fiberwiseProperConvex
      (adjointOfConvexBifunction ⟨Gpkg.toFun, hGproper.1⟩) hAdjG.1 hAdjG.2
  have hPkg := properConvexBifunction_dom_convex_nonempty Hpkg.toFun hHproper
  let signed : (Fin n → ℝ) →ₗ[ℝ] Module.Dual ℝ (Fin n → ℝ) :=
    { toFun := fun x => dotProductEquiv ℝ (Fin n) (-x)
      map_add' := by intro x y; simp [add_comm]
      map_smul' := by intro c x; simp }
  let Scur := bifunctionDom (bifunctionInverse (bifunctionAdjoint Gpkg.toFun))
  have hCurrentEq : Scur = signed '' bifunctionDom Hpkg.toFun := by
    rw [hHeq]
    rw [helperForCorollary_38_5_1_vectorizedAdjointInverse_dom_preimage
      (G := Gpkg) (hG_properConvex := hGproper)]
    ext xStar
    constructor
    · intro hx
      refine ⟨-((dotProductEquiv ℝ (Fin n)).symm xStar), ?_, ?_⟩
      · simpa [signed, Scur, dotProductEquiv_apply_apply] using hx
      · simp [signed, dotProductEquiv_apply_apply]
    · rintro ⟨x, hx, rfl⟩
      simpa [signed, Scur, dotProductEquiv_apply_apply] using hx
  constructor
  · change Convex ℝ Scur
    rw [hCurrentEq]
    exact hPkg.1.linear_image signed
  · change Scur.Nonempty
    rw [hCurrentEq]
    exact hPkg.2.image signed

/-- A nonempty convex set meets the intrinsic interior of the whole finite-dimensional space. -/
lemma intrinsicInterior_univ_inter_nonempty_of_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S : Set E) (hconv : Convex ℝ S) (hne : S.Nonempty) :
    (intrinsicInterior ℝ (Set.univ : Set E) ∩ intrinsicInterior ℝ S).Nonempty := by
  rcases Set.Nonempty.intrinsicInterior hconv hne with ⟨x, hx⟩
  refine ⟨x, ?_, hx⟩
  exact interior_subset_intrinsicInterior (s := (Set.univ : Set E)) (by simp [interior_univ])

/-- Full Euclidean adjoint domain transports to the current dual-coordinate domain. -/
lemma cofinite_adjoint_current_domBot_eq_univ {m n : Nat}
    (Fpkg : FiberwiseProperConvexBifunction m n)
    (hFproper : ProperConvexBifunction Fpkg.toFun)
    (hFadjDom : bifunctionDomBot (bifunctionAdjointInner Fpkg.toFun) = Set.univ) :
    bifunctionDomBot (bifunctionAdjoint Fpkg.toFun) = Set.univ := by
  have hLeftPkg : ∀ xStar : Fin n → ℝ,
      xStar ∈ bifunctionDomBot
        (adjointOfConvexBifunction ⟨Fpkg.toFun, hFproper.1⟩) := by
    intro xStar
    rw [← bifunctionAdjointInner_eq_adjointOfConvexBifunction Fpkg.toFun hFproper.1]
    rw [hFadjDom]
    trivial
  have hLeftFull :=
    helperForCorollary_38_5_1_full_currentDual_leftDomain_of_full_packagedDomain
      Fpkg hFproper hLeftPkg
  ext x
  constructor
  · simp
  · intro _
    exact hLeftFull x

set_option maxHeartbeats 1000000 in
/-- Co-finite compositions are closed convex before applying the domain characterization. -/
lemma cofinite_compose_closed {m n p : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u))
    (G : (Fin n → ℝ) → (Fin p → ℝ) → EReal)
    (hG_joint : ConvexBifunction G)
    (hG : ∀ x : Fin n → ℝ, CoFiniteERealFunction (G x)) :
    ClosedConvexBifunction (bifunctionComposeInfGeneric G F) := by
  have hFproper := properConvexBifunction_of_joint_cofinite F hF_joint hF
  have hGproper := properConvexBifunction_of_joint_cofinite G hG_joint hG
  obtain ⟨Fpkg, hFpkg⟩ := fiberwiseProperConvex_of_properConvexBifunction F hFproper
  obtain ⟨Gpkg, hGpkg⟩ := fiberwiseProperConvex_of_properConvexBifunction G hGproper
  subst F
  subst G
  have hFclosed0 := closedConvexBifunction_of_coFiniteSlices Fpkg.toFun hF_joint hF
  have hGclosed0 := closedConvexBifunction_of_coFiniteSlices Gpkg.toFun hG_joint hG
  have hFclosed : IsProductLowerSemicontinuousBifunction Fpkg.toFun := by
    have hcomp := hFclosed0.2.2.comp_continuous
      (show Continuous (fun q : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append q.1 q.2) by
        simpa using (Fin.continuous_append m n).comp (continuous_fst.prodMk continuous_snd))
    simpa [IsProductLowerSemicontinuousBifunction, bifunctionGraphFunction] using hcomp
  have hGclosed : IsProductLowerSemicontinuousBifunction Gpkg.toFun := by
    have hcomp := hGclosed0.2.2.comp_continuous
      (show Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) => Fin.append q.1 q.2) by
        simpa using (Fin.continuous_append n p).comp (continuous_fst.prodMk continuous_snd))
    simpa [IsProductLowerSemicontinuousBifunction, bifunctionGraphFunction] using hcomp
  have hFadjDom :=
    (helperForCoFiniteBifunction_dom_and_adjointDom_eq_univ Fpkg.toFun hF_joint hF).2
  have hComposeLsc := cofinite_compose_closed_packaged_route
    Fpkg Gpkg hFproper hGproper hFclosed hGclosed hFadjDom
  have hconv : ConvexBifunction (bifunctionCompose Gpkg Fpkg) :=
    (theorem38_5_compose_convex_and_adjoint_eq_composeSup_adjoint
      Fpkg Gpkg hFproper hGproper).1
  refine ⟨?_, ?_⟩
  · simpa [bifunctionComposeInfGeneric, bifunctionCompose] using hconv
  · have hlscGraph : LowerSemicontinuous
        (bifunctionGraphFunction
          (bifunctionComposeInfGeneric Gpkg.toFun Fpkg.toFun)) := by
      have hcomp := hComposeLsc.comp_continuous
        (show Continuous (fun z : Fin (m + p) → ℝ =>
            ((fun i => z (Fin.castAdd p i)), (fun j => z (Fin.natAdd m j)))) by
          fun_prop)
      simpa [IsProductLowerSemicontinuousBifunction, bifunctionGraphFunction,
        bifunctionComposeInfGeneric, bifunctionCompose] using hcomp
    exact ⟨by simpa [bifunctionComposeInfGeneric, bifunctionCompose] using hconv,
      hlscGraph⟩

-- Proof sketch: Use the slice-wise characterization of co-finiteness from Proposition 38.7.2 to
-- deduce `dom F = ℝ^m` and `dom (F^*) = ℝ^n` (and similarly for `G`), which supplies the
-- qualification needed for the composition conjugacy theorem from §38.5. Apply the composition
-- conjugacy identity (specializing Theorem 38.5 to Euclidean duality via `bifunctionAdjointInner`)
-- to obtain `(GF)^* = F^* G^*`, and use stability of co-finiteness under multiplication to show
-- the slices of `GF` are co-finite.
/-- Proposition 38.7.5: If `F` is a co-finite convex bifunction from `ℝ^m` to `ℝ^n` and `G` is a
co-finite convex bifunction from `ℝ^n` to `ℝ^p`, then the product `GF` is a co-finite convex
bifunction from `ℝ^m` to `ℝ^p` and satisfies `(GF)^* = F^* G^*`.

In Lean, the product `GF` is modeled by `bifunctionComposeInfGeneric G.1 F.1`, the adjoint `F^*`
by `bifunctionAdjointInner F.1`, and the product `F^* G^*` by
`bifunctionComposeSup (bifunctionAdjointInner F.1) (bifunctionAdjointInner G.1)`. -/
theorem coFiniteBifunction_composeInfGeneric_adjointInner {m n p : Nat}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF_joint : ConvexBifunction F)
    (hF : ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u))
    (G : (Fin n → ℝ) → (Fin p → ℝ) → EReal)
    (hG_joint : ConvexBifunction G)
    (hG : ∀ x : Fin n → ℝ, CoFiniteERealFunction (G x)) :
    (ConvexBifunction (bifunctionComposeInfGeneric G F) ∧
        ∀ u : Fin m → ℝ, CoFiniteERealFunction (bifunctionComposeInfGeneric G F u)) ∧
      bifunctionAdjointInner (bifunctionComposeInfGeneric G F) =
        bifunctionComposeSup (bifunctionAdjointInner F) (bifunctionAdjointInner G) :=
  by
    have hclosed := cofinite_compose_closed F hF_joint hF G hG_joint hG
    have hadj := cofinite_compose_adjoint_identity F hF_joint hF G hG_joint hG
    have hdom : bifunctionDom (bifunctionComposeInfGeneric G F) = Set.univ := by
      ext u
      simp only [bifunctionDom, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rcases (hF u).2.1.2 with ⟨x, hx⟩
      rcases (hG x).2.1.2 with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      apply (lt_top_iff_ne_top.1 ?_)
      refine lt_of_le_of_lt (iInf_le (fun z => F u z + G z y) x) ?_
      exact EReal.add_lt_top hx hy
    have hdomAdj :
        bifunctionDomBot (bifunctionAdjointInner (bifunctionComposeInfGeneric G F)) =
          Set.univ := by
      rw [hadj]
      ext yStar
      simp only [bifunctionDomBot, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have hGneg := helperForCoFiniteBifunction_neg_adjointSlice_coFiniteERealFunction
        G hG_joint hG yStar
      rcases hGneg.2.1.2 with ⟨xStar, hxStar⟩
      have hxStar' : bifunctionAdjointInner G yStar xStar ≠ ⊥ := by
        simpa using hxStar
      have hFneg := helperForCoFiniteBifunction_neg_adjointSlice_coFiniteERealFunction
        F hF_joint hF xStar
      rcases hFneg.2.1.2 with ⟨uStar, huStar⟩
      have huStar' : bifunctionAdjointInner F xStar uStar ≠ ⊥ := by
        simpa using huStar
      refine ⟨uStar, ?_⟩
      have hterm :
          bifunctionAdjointInner F xStar uStar +
              bifunctionAdjointInner G yStar xStar ≠ ⊥ :=
        (EReal.add_ne_bot_iff).2 ⟨huStar', hxStar'⟩
      have hle :
          bifunctionAdjointInner F xStar uStar +
              bifunctionAdjointInner G yStar xStar ≤
            bifunctionComposeSup (bifunctionAdjointInner F)
              (bifunctionAdjointInner G) yStar uStar := by
        simpa [bifunctionComposeSup, add_comm] using
          (le_iSup (fun z =>
            bifunctionAdjointInner F z uStar + bifunctionAdjointInner G yStar z) xStar)
      intro hbot
      apply hterm
      exact le_antisymm (by simpa [hbot] using hle) bot_le
    refine ⟨?_, hadj⟩
    exact helperForClosedConvexBifunction_coFinite_of_dom_and_adjointDom_eq_univ
      (bifunctionComposeInfGeneric G F) hclosed hdom hdomAdj

/-- A jointly convex bifunction in the Chapter 6 graph-function sense. -/
abbrev JointConvexBifunction (m n : Nat) : Type :=
  {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}

/-- A bundled co-finite jointly convex bifunction from `ℝ^n` to itself. -/
abbrev CoFiniteFiberwiseConvexBifunction (n : Nat) : Type :=
  {F : JointConvexBifunction n n // ∀ u : Fin n → ℝ, CoFiniteERealFunction (F.1 u)}

lemma isFiberwiseConvexBifunction_of_convexBifunction {m n : Nat}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : ConvexBifunction F) : IsFiberwiseConvexBifunction F := by
  intro u
  have hGraph : IsERealConvex (bifunctionGraphFunction F) := by
    simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
      helperForTheorem_38_1_epigraph_eq_univ] using hF
  intro p hp q hq a b ha hb hab
  have hp' :
      (Fin.append u p.1, p.2) ∈ ERealEpigraph (bifunctionGraphFunction F) := by
    simpa [ERealEpigraph, bifunctionGraphFunction] using hp
  have hq' :
      (Fin.append u q.1, q.2) ∈ ERealEpigraph (bifunctionGraphFunction F) := by
    simpa [ERealEpigraph, bifunctionGraphFunction] using hq
  have h := hGraph hp' hq' ha hb hab
  have happend :
      a • Fin.append u p.1 + b • Fin.append u q.1 =
        Fin.append u (a • p.1 + b • q.1) := by
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [Pi.smul_apply, Pi.add_apply, Fin.append, Fin.addCases_left, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
    · intro j
      simp only [Pi.smul_apply, Pi.add_apply, Fin.append, Fin.addCases_right, smul_eq_mul]
  rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, happend] at h
  simpa [ERealEpigraph, bifunctionGraphFunction, Prod.smul_mk, Prod.mk_add_mk,
    smul_eq_mul] using h

def fiberwiseProperConvexBifunction_of_coFiniteFiberwiseConvexBifunction {n : Nat}
    (F : CoFiniteFiberwiseConvexBifunction n) : FiberwiseProperConvexBifunction n n := by
  refine ⟨F.1.1, ?_, isFiberwiseConvexBifunction_of_convexBifunction F.1.2⟩
  constructor
  · intro u x
    exact (F.2 u).2.1.1 x
  · rcases (F.2 0).2.1.2 with ⟨x, hx⟩
    exact ⟨0, x, hx⟩

-- Proof sketch: Apply Proposition 38.7.5 specialized to `m = n = p` and extract the convexity and
-- slice-wise co-finiteness conclusions for the product `GF`.
/-- Closure of co-finite convex bifunctions under multiplication `GF`, modeled by
`bifunctionComposeInfGeneric`. -/
lemma coFiniteFiberwiseConvexBifunction_composeInfGeneric {n : Nat}
    (F G : CoFiniteFiberwiseConvexBifunction n) :
    ConvexBifunction (bifunctionComposeInfGeneric G.1.1 F.1.1) ∧
      ∀ u : Fin n → ℝ, CoFiniteERealFunction (bifunctionComposeInfGeneric G.1.1 F.1.1 u) := by
  exact
    (coFiniteBifunction_composeInfGeneric_adjointInner
      F.1.1 F.1.2 F.2 G.1.1 G.1.2 G.2).1

/-- Multiplication on `CoFiniteFiberwiseConvexBifunction n`, given by infimum-based composition `GF`. -/
noncomputable def CoFiniteFiberwiseConvexBifunction.mul {n : Nat}
    (G F : CoFiniteFiberwiseConvexBifunction n) : CoFiniteFiberwiseConvexBifunction n :=
  let h := coFiniteFiberwiseConvexBifunction_composeInfGeneric (F := F) (G := G)
  ⟨⟨bifunctionComposeInfGeneric G.1.1 F.1.1, h.1⟩, h.2⟩

/-- The multiplication operation on `CoFiniteFiberwiseConvexBifunction n`. -/
noncomputable instance (n : Nat) : Mul (CoFiniteFiberwiseConvexBifunction n) :=
  ⟨fun G F => CoFiniteFiberwiseConvexBifunction.mul (n := n) G F⟩

-- Proof sketch: Reduce to the associativity statement for infimum-based composition from
-- Proposition 38.5.1, using that co-finiteness supplies the properness qualifications required for
-- associativity of the generic infimum formula.
/-- Associativity of multiplication on co-finite convex bifunctions. -/
lemma coFiniteFiberwiseConvexBifunction_mul_assoc (n : Nat)
    (F G H : CoFiniteFiberwiseConvexBifunction n) :
    F * G * H = F * (G * H) := by
  let Fpkg := fiberwiseProperConvexBifunction_of_coFiniteFiberwiseConvexBifunction F
  let Gpkg := fiberwiseProperConvexBifunction_of_coFiniteFiberwiseConvexBifunction G
  let Hpkg := fiberwiseProperConvexBifunction_of_coFiniteFiberwiseConvexBifunction H
  have hGHcofinite :
      ConvexBifunction (bifunctionComposeInfGeneric G.1.1 H.1.1) ∧
        ∀ u : Fin n → ℝ, CoFiniteERealFunction (bifunctionComposeInfGeneric G.1.1 H.1.1 u) :=
    coFiniteFiberwiseConvexBifunction_composeInfGeneric (F := H) (G := G)
  have hFGcofinite :
      ConvexBifunction (bifunctionComposeInfGeneric F.1.1 G.1.1) ∧
        ∀ u : Fin n → ℝ, CoFiniteERealFunction (bifunctionComposeInfGeneric F.1.1 G.1.1 u) :=
    coFiniteFiberwiseConvexBifunction_composeInfGeneric (F := G) (G := F)
  have hGHproper :
      IsProperEReal (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        bifunctionComposeInfGeneric G.1.1 H.1.1 z.1 z.2) := by
    constructor
    · intro p
      exact (hGHcofinite.2 p.1).2.1.1 p.2
    · rcases (hGHcofinite.2 0).2.1.2 with ⟨x, hx⟩
      exact ⟨(0, x), hx⟩
  have hFGproper :
      IsProperEReal (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        bifunctionComposeInfGeneric F.1.1 G.1.1 z.1 z.2) := by
    constructor
    · intro p
      exact (hFGcofinite.2 p.1).2.1.1 p.2
    · rcases (hFGcofinite.2 0).2.1.2 with ⟨x, hx⟩
      exact ⟨(0, x), hx⟩
  have hFproper : ProperConvexBifunction Fpkg.toFun := by
    have hp : IsProperEReal (bifunctionGraphFunction F.1.1) := by
      constructor
      · intro z
        exact (F.2 (fun i => z (Fin.castAdd n i))).2.1.1
          (fun j => z (Fin.natAdd n j))
      · rcases (F.2 0).2.1.2 with ⟨x, hx⟩
        refine ⟨Fin.append 0 x, ?_⟩
        change F.1.1 (fun i => Fin.append 0 x (Fin.castAdd n i))
            (fun j => Fin.append 0 x (Fin.natAdd n j)) ≠ ⊤
        have hleft : (fun i => Fin.append (0 : Fin n → ℝ) x (Fin.castAdd n i)) = 0 :=
          funext (Fin.append_left 0 x)
        have hright : (fun j => Fin.append (0 : Fin n → ℝ) x (Fin.natAdd n j)) = x :=
          funext (Fin.append_right 0 x)
        rw [hleft, hright]
        exact hx
    have hc : IsERealConvex (bifunctionGraphFunction F.1.1) := by
      simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
        helperForTheorem_38_1_epigraph_eq_univ] using F.1.2
    have hpc :=
      helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        (bifunctionGraphFunction F.1.1) hp hc
    have hraw : ProperConvexBifunction F.1.1 :=
      ⟨F.1.2,
        helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
          (f := bifunctionGraphFunction F.1.1) hpc⟩
    simpa [Fpkg, fiberwiseProperConvexBifunction_of_coFiniteFiberwiseConvexBifunction] using hraw
  have hGproper : ProperConvexBifunction Gpkg.toFun := by
    have hp : IsProperEReal (bifunctionGraphFunction G.1.1) := by
      constructor
      · intro z
        exact (G.2 (fun i => z (Fin.castAdd n i))).2.1.1
          (fun j => z (Fin.natAdd n j))
      · rcases (G.2 0).2.1.2 with ⟨x, hx⟩
        refine ⟨Fin.append 0 x, ?_⟩
        change G.1.1 (fun i => Fin.append 0 x (Fin.castAdd n i))
            (fun j => Fin.append 0 x (Fin.natAdd n j)) ≠ ⊤
        have hleft : (fun i => Fin.append (0 : Fin n → ℝ) x (Fin.castAdd n i)) = 0 :=
          funext (Fin.append_left 0 x)
        have hright : (fun j => Fin.append (0 : Fin n → ℝ) x (Fin.natAdd n j)) = x :=
          funext (Fin.append_right 0 x)
        rw [hleft, hright]
        exact hx
    have hc : IsERealConvex (bifunctionGraphFunction G.1.1) := by
      simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
        helperForTheorem_38_1_epigraph_eq_univ] using G.1.2
    have hpc :=
      helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        (bifunctionGraphFunction G.1.1) hp hc
    have hraw : ProperConvexBifunction G.1.1 :=
      ⟨G.1.2,
        helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
          (f := bifunctionGraphFunction G.1.1) hpc⟩
    simpa [Gpkg, fiberwiseProperConvexBifunction_of_coFiniteFiberwiseConvexBifunction] using hraw
  have hHproper : ProperConvexBifunction Hpkg.toFun := by
    have hp : IsProperEReal (bifunctionGraphFunction H.1.1) := by
      constructor
      · intro z
        exact (H.2 (fun i => z (Fin.castAdd n i))).2.1.1
          (fun j => z (Fin.natAdd n j))
      · rcases (H.2 0).2.1.2 with ⟨x, hx⟩
        refine ⟨Fin.append 0 x, ?_⟩
        change H.1.1 (fun i => Fin.append 0 x (Fin.castAdd n i))
            (fun j => Fin.append 0 x (Fin.natAdd n j)) ≠ ⊤
        have hleft : (fun i => Fin.append (0 : Fin n → ℝ) x (Fin.castAdd n i)) = 0 :=
          funext (Fin.append_left 0 x)
        have hright : (fun j => Fin.append (0 : Fin n → ℝ) x (Fin.natAdd n j)) = x :=
          funext (Fin.append_right 0 x)
        rw [hleft, hright]
        exact hx
    have hc : IsERealConvex (bifunctionGraphFunction H.1.1) := by
      simpa [ConvexBifunction, ConvexFunction, ConvexFunctionOn, IsERealConvex,
        helperForTheorem_38_1_epigraph_eq_univ] using H.1.2
    have hpc :=
      helperForTheorem_38_4_properConvexFunctionOn_univ_of_isProperEReal_and_isERealConvex
        (bifunctionGraphFunction H.1.1) hp hc
    have hraw : ProperConvexBifunction H.1.1 :=
      ⟨H.1.2,
        helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
          (f := bifunctionGraphFunction H.1.1) hpc⟩
    simpa [Hpkg, fiberwiseProperConvexBifunction_of_coFiniteFiberwiseConvexBifunction] using hraw
  have hassoc :=
    (bifunctionComposeInfGeneric_assoc_and_identityIndicator n).1
      (F := Hpkg) (G := Gpkg) (H := Fpkg)
      hHproper hGproper hFproper hGHproper hFGproper
  apply Subtype.ext
  apply Subtype.ext
  simpa [Mul.mul, CoFiniteFiberwiseConvexBifunction.mul, Fpkg, Gpkg, Hpkg]
    using hassoc.symm

/-- A semigroup structure on co-finite convex bifunctions from `ℝ^n` to itself, with multiplication
given by infimum-based composition. -/
noncomputable instance coFiniteFiberwiseConvexBifunction_semigroup (n : Nat) :
    Semigroup (CoFiniteFiberwiseConvexBifunction n) where
  mul := (· * ·)
  mul_assoc := coFiniteFiberwiseConvexBifunction_mul_assoc (n := n)

-- Proof sketch: Associativity is `coFiniteFiberwiseConvexBifunction_mul_assoc`. Non-commutativity is
-- witnessed by two explicit co-finite convex bifunctions whose products differ (e.g. coming from
-- non-commuting linear maps).
/-- Proposition 38.7.6: in dimension at least two, the co-finite convex bifunctions from `ℝ^n`
to itself form a non-commutative semigroup under multiplication.  The explicit dimension
hypothesis is required by the book's witness using non-commuting linear maps; at `n = 0` the
unqualified non-commutativity statement is false. -/
theorem coFiniteFiberwiseConvexBifunction_mul_assoc_and_not_comm (n : Nat) (hn : 2 ≤ n) :
    (∀ F G H : CoFiniteFiberwiseConvexBifunction n, (F * G) * H = F * (G * H)) ∧
      (∃ F G : CoFiniteFiberwiseConvexBifunction n, F * G ≠ G * F) :=
  by
    constructor
    · exact coFiniteFiberwiseConvexBifunction_mul_assoc n
    · let i0 : Fin n := ⟨0, by omega⟩
      let i1 : Fin n := ⟨1, by omega⟩
      have hi01 : i0 ≠ i1 := by
        intro h
        have hval : (0 : Nat) = 1 := by
          simpa [i0, i1] using congrArg Fin.val h
        omega
      let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
        { toFun := fun x i => if i = i0 then x i1 else 0
          map_add' := by
            intro x y
            funext i
            by_cases hi : i = i0 <;> simp [hi]
          map_smul' := by
            intro c x
            funext i
            by_cases hi : i = i0 <;> simp [hi] }
      let B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
        { toFun := fun x i => if i = i1 then x i0 else 0
          map_add' := by
            intro x y
            funext i
            by_cases hi : i = i1 <;> simp [hi]
          map_smul' := by
            intro c x
            funext i
            by_cases hi : i = i1 <;> simp [hi] }
      let FA : CoFiniteFiberwiseConvexBifunction n :=
        ⟨⟨convexIndicatorBifunction A,
            convexBifunction_convexIndicatorBifunction A⟩,
          coFiniteERealFunction_convexIndicatorBifunction_slice A⟩
      let FB : CoFiniteFiberwiseConvexBifunction n :=
        ⟨⟨convexIndicatorBifunction B,
            convexBifunction_convexIndicatorBifunction B⟩,
          coFiniteERealFunction_convexIndicatorBifunction_slice B⟩
      let v : Fin n → ℝ := fun i => if i = i0 then 1 else 0
      have hcomp : (A.comp B) v ≠ (B.comp A) v := by
        intro h
        have hv := congrFun h i0
        simp [A, B, v, i0, i1, hi01] at hv
      refine ⟨FA, FB, ?_⟩
      intro hcomm
      have hfun := congrArg (fun K : CoFiniteFiberwiseConvexBifunction n => K.1.1) hcomm
      have hAB :
          (FA * FB).1.1 = convexIndicatorBifunction (A.comp B) := by
        simpa [FA, FB, Mul.mul, CoFiniteFiberwiseConvexBifunction.mul,
          bifunctionComposeInfGeneric, bifunctionCompose] using
          (bifunctionCompose_convexIndicatorBifunction_eq_convexIndicatorBifunction_comp
            (A := B) (B := A))
      have hBA :
          (FB * FA).1.1 = convexIndicatorBifunction (B.comp A) := by
        simpa [FA, FB, Mul.mul, CoFiniteFiberwiseConvexBifunction.mul,
          bifunctionComposeInfGeneric, bifunctionCompose] using
          (bifunctionCompose_convexIndicatorBifunction_eq_convexIndicatorBifunction_comp
            (A := A) (B := B))
      have hind :
          convexIndicatorBifunction (A.comp B) =
            convexIndicatorBifunction (B.comp A) := by
        rw [← hAB, ← hBA]
        exact hfun
      have hv := congrFun (congrFun hind v) ((A.comp B) v)
      simp [convexIndicatorBifunction] at hv
      exact hcomp hv

-- Proof sketch: Co-finiteness supplies the qualification hypotheses needed to apply the general
-- Fenchel inner-product adjointness theorem (Theorem 38.7) to the triple `(F, f, g)`, with `g^*`
-- viewed as an arbitrary co-finite concave function. Identify `Ff` with `bifunctionImageRaw F f`
-- and `F^* g^*` with `bifunctionImageSupRaw (bifunctionAdjointInner F) gStar`.
/-- Proposition 38.7.7: For a co-finite convex bifunction `F`, a co-finite convex function `f` on
`ℝ^m`, and a co-finite concave function `g^*` on `ℝ^n`, the Fenchel inner product satisfies the
adjointness identity

`⟨Ff, g^*⟩ = ⟨f, F^* g^*⟩`.

In Lean, `⟨·,·⟩` is `fenchelInnerProduct : Option EReal`, `Ff` is `bifunctionImageRaw F f`, and
`F^* g^*` is the concave image `bifunctionImageSupRaw (bifunctionAdjointInner F) gStar`.
The fiberwise co-finite data are supplemented by the joint proper-convex hypotheses on `F` and
an explicit proper concave preconjugate `g` of `gStar` satisfying the relative-interior
qualification required by the adjoint transport. -/
theorem fenchelInnerProduct_image_eq_adjointImageSup_of_coFinite
    {m n : Nat} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (f : (Fin m → ℝ) → EReal) (gStar : (Fin n → ℝ) → EReal)
    (hF : IsFiberwiseConvexBifunction F ∧ ∀ u : Fin m → ℝ, CoFiniteERealFunction (F u))
    (hf_convex : IsERealConvex f) (hf_cofinite : CoFiniteERealFunction f)
    (hg_concave : IsERealConvex (fun y => -gStar y))
    (hg_cofinite : CoFiniteERealFunction (fun y => -gStar y))
    (hF_proper : IsProperEReal
      (fun z : (Fin m → ℝ) × (Fin n → ℝ) => F z.1 z.2))
    (hF_convex : IsERealConvex
      (fun z : (Fin m → ℝ) × (Fin n → ℝ) => F z.1 z.2))
    (hregular : ∃ g : (Fin n → ℝ) → EReal,
      IsProperEReal (fun y => -g y) ∧
      IsERealConvex (fun y => -g y) ∧
      concaveConjugateInner g = gStar ∧
      ∃ u : Fin m → ℝ,
        u ∈ intrinsicInterior ℝ (erealDom f) ∩ intrinsicInterior ℝ (bifunctionDom F) ∧
          (intrinsicInterior ℝ (erealDom (fun x : Fin n → ℝ => F u x)) ∩
            intrinsicInterior ℝ (erealDomBot g)).Nonempty) :
    ∃ c : EReal,
      fenchelInnerProduct (bifunctionImageRaw F f) gStar = some c ∧
        fenchelInnerProduct f (bifunctionImageSupRaw (bifunctionAdjointInner F) gStar) = some c :=
  by
    rcases hregular with ⟨g, hg_proper, hg_convex, hg_conj, hqual⟩
    have hf_proper : IsProperEReal f := hf_cofinite.2.1
    rcases helperForTheorem_38_7_first_fenchel_transport
        F f g hF_proper hF_convex hf_proper hf_convex hg_proper hg_convex hqual with
      ⟨c, hleft, hright⟩
    refine ⟨c, ?_, ?_⟩
    · simpa only [hg_conj] using hleft
    · simpa only [hg_conj] using hright

end Section38
end Chap08

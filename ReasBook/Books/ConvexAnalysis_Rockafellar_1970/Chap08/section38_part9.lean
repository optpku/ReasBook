/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part12

open scoped Pointwise

section Chap08
section Section38

attribute [local instance] instTopologicalSpace_moduleDual_weak_part3

-- `helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective`,
-- `helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective_convexOn`, and
-- `helperForTheorem_38_5_composeSupGeneric_eq_fenchelDualSupremum`
-- are provided upstream in `section38_part7`.

/-- Helper for Theorem 38.5: the graph function of the corrected second-shift reduced objective
is exactly its packed `Fin (n + n)` representative. -/
lemma helperForTheorem_38_5_graphSecondShift_eq_packed
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    bifunctionGraphFunction (helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar) =
      helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective F G yStar uStar := by
  -- Both sides read the first `n` coordinates as `z` and the last `n` coordinates as `x`.
  funext zx
  simp [bifunctionGraphFunction, helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective,
    projXLinearMap, projLamLinearMap]

/-- Helper for Theorem 38.5: the corrected second-shift reduced objective is convex in the
Chapter 30 graph-function sense. -/
lemma helperForTheorem_38_5_secondShiftMiddleReducedObjective_convexBifunction
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    ConvexBifunction
      (helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar) := by
  have hGraphConv :
      ConvexFunctionOn (Set.univ : Set (Fin (n + n) → ℝ))
        (bifunctionGraphFunction
          (helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar)) := by
    -- Route correction: only graph convexity survives the repaired `⊥/⊤` semantics.
    rw [helperForTheorem_38_5_graphSecondShift_eq_packed]
    exact
      helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective_convexOn
        (F := F) (G := G) (yStar := yStar) (uStar := uStar)
        hF_properConvex hG_properConvex
  -- Repackage the `Set.univ` convexity statement as the global Chapter 30 predicate.
  simpa [ConvexBifunction, ConvexFunction] using hGraphConv

/-- Helper for Theorem 38.5: the guarded value function is the infimum of the packed second-shift
objective over the fibers of the projection onto the `z`-coordinates. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuardedValue_eq_infFiber
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    (fun z : Fin n → ℝ =>
      sInf
        {r : EReal |
          ∃ zx : Fin (n + n) → ℝ,
            projXLinearMap (n := n) (m := n) zx = z ∧
              r =
                helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective
                  F G yStar uStar zx}) =
      helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar := by
  funext z
  have hSet :
      {r : EReal |
          ∃ zx : Fin (n + n) → ℝ,
            projXLinearMap (n := n) (m := n) zx = z ∧
              r =
                helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective
                  F G yStar uStar zx} =
        Set.range
          (helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
            F G yStar uStar z) := by
    ext r
    constructor
    · rintro ⟨zx, hzx, rfl⟩
      refine ⟨projLamLinearMap (n := n) (m := n) zx, ?_⟩
      have hGraphEq :=
        congrFun
          (helperForTheorem_38_5_graphSecondShift_eq_packed
            (F := F) (G := G) (yStar := yStar) (uStar := uStar)) zx
      have hzx' : (fun i : Fin n => zx (Fin.castAdd n i)) = z := by
        ext i
        exact congrArg (fun f : Fin n → ℝ => f i) hzx
      have hPackedAsSecond :
          helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective F G yStar uStar zx =
            helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar z
              (projLamLinearMap (n := n) (m := n) zx) := by
        simpa [bifunctionGraphFunction, projLamLinearMap, hzx'] using hGraphEq.symm
      calc
        helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar z
            (projLamLinearMap (n := n) (m := n) zx) =
          helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar z
            (projLamLinearMap (n := n) (m := n) zx) := by
              symm
              exact
                helperForTheorem_38_5_secondShiftMiddleReducedObjective_eq_textbookSecondShiftGuardedPerturbationRaw
                  (F := F) (G := G) (yStar := yStar) (uStar := uStar)
                  (z := z) (x := projLamLinearMap (n := n) (m := n) zx)
        _ =
          helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective F G yStar uStar zx :=
            hPackedAsSecond.symm
    · rintro ⟨x, rfl⟩
      refine ⟨Fin.append z x, ?_, ?_⟩
      · simp [projXLinearMap]
      · have hGraphEq :=
          congrFun
            (helperForTheorem_38_5_graphSecondShift_eq_packed
              (F := F) (G := G) (yStar := yStar) (uStar := uStar))
            (Fin.append z x)
        have hAppendX : (fun i : Fin n => Fin.append z x (Fin.castAdd n i)) = z := by
          ext i
          simp
        have hAppendLam : (fun j : Fin n => Fin.append z x (j.addNat n)) = x := by
          ext j
          simpa using (Fin.append_right (u := z) (v := x) (i := j))
        have hSecondAsPacked :
            helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar z x =
              helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective F G yStar uStar
                (Fin.append z x) := by
          simpa [bifunctionGraphFunction, hAppendX, hAppendLam] using hGraphEq
        calc
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar z x =
              helperForTheorem_38_5_secondShiftMiddleReducedObjective F G yStar uStar z x := by
                symm
                exact
                  helperForTheorem_38_5_secondShiftMiddleReducedObjective_eq_textbookSecondShiftGuardedPerturbationRaw
                    (F := F) (G := G) (yStar := yStar) (uStar := uStar) (z := z) (x := x)
          _ =
              helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective F G yStar uStar
                (Fin.append z x) := hSecondAsPacked
  -- Replace the infimum set by the explicit range over `x`.
  rw [helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction, functionInfimumEReal]
  rw [← sInf_range]
  exact congrArg sInf hSet

/-- Helper for Theorem 38.5: the guarded translated value function is convex in the shift
parameter `z`. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction_convex
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun) :
    ConvexFunction
      (helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar) := by
  let packed : (Fin (n + n) → ℝ) → EReal :=
    helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective F G yStar uStar
  let A : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    projXLinearMap (n := n) (m := n)
  have hPackedConv :
      ConvexFunctionOn (Set.univ : Set (Fin (n + n) → ℝ)) packed :=
    helperForTheorem_38_5_packedSecondShiftMiddleReducedObjective_convexOn
      (F := F) (G := G) (yStar := yStar) (uStar := uStar)
      hF_properConvex hG_properConvex
  have hFiberConv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun z : Fin n → ℝ =>
          sInf {r : EReal | ∃ zx : Fin (n + n) → ℝ, A zx = z ∧ r = packed zx}) := by
    simpa [A, packed] using
      (convexFunctionOn_inf_fiber_linearMap (A := A) packed hPackedConv)
  -- The fiber-infimum description is exactly the textbook guarded value function.
  simpa [A, packed, ConvexFunction,
    helperForTheorem_38_5_textbookSecondShiftGuardedValue_eq_infFiber
      (F := F) (G := G) (yStar := yStar) (uStar := uStar)] using hFiberConv

/-- Helper for Theorem 38.5: the effective domain of the guarded value function is exactly the
Minkowski difference `dom G - dom F_*`. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuardedValue_effectiveDomain_eq_domainDifference
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar) =
      bifunctionDom G.toFun - bifunctionDomBot (bifunctionInverse F.toFun) := by
  ext z
  constructor
  · intro hz
    rw [effectiveDomain_eq] at hz
    have hzlt :
        helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar z <
          (⊤ : EReal) :=
      hz.2
    rw [helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction, functionInfimumEReal] at hzlt
    have hzlt' :
        sInf
            (Set.range
              (helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
                F G yStar uStar z)) <
          (⊤ : EReal) := by
      simpa [sInf_range] using hzlt
    have hRangeNonempty :
        (Set.range
          (helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
            F G yStar uStar z)).Nonempty := by
      exact ⟨_, ⟨0, rfl⟩⟩
    rcases exists_lt_of_csInf_lt
        (s := Set.range
          (helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw
            F G yStar uStar z))
        hRangeNonempty hzlt' with
      ⟨r, hr, hrlt⟩
    rcases hr with ⟨x, rfl⟩
    have hRaw_ne_top :
        helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar z x ≠
          (⊤ : EReal) :=
      lt_top_iff_ne_top.mp hrlt
    by_cases hguard :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
          (x + z) ∈
            concaveEffectiveDomain
              (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
    · have hxF : x ∈ bifunctionDomBot (bifunctionInverse F.toFun) := by
        simpa [helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain] using hguard.1
      have hxzG : x + z ∈ bifunctionDom G.toFun := by
        simpa [helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using
          hguard.2
      refine ⟨x + z, hxzG, x, hxF, ?_⟩
      ext i
      simp
    · have htop :
        helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar z x =
          (⊤ : EReal) := by
        simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hguard]
      exact (hRaw_ne_top htop).elim
  · rintro ⟨y, hyG, x, hxF, rfl⟩
    rw [effectiveDomain_eq]
    refine ⟨by simp, ?_⟩
    have hguard :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
          (x + (y - x)) ∈
            concaveEffectiveDomain
              (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
      constructor
      · simpa [helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain] using hxF
      · simpa [helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using hyG
    have hfx_ne_top :
        helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top
        (S := (Set.univ : Set (Fin n → ℝ)))
        (f := helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) hguard.1
    have hnegGy_ne_top :
        -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) (x + (y - x))) ≠
          (⊤ : EReal) := by
      have hdom :
          x + (y - x) ∈ (Set.univ : Set (Fin n → ℝ)) ∧
            -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) (x + (y - x))) <
              (⊤ : EReal) := by
        simpa [concaveEffectiveDomain, effectiveDomain_eq] using hguard.2
      exact lt_top_iff_ne_top.mp hdom.2
    have hxy : x + (y - x) = y := by
      ext i
      simp
    have hguard' :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
          y ∈ concaveEffectiveDomain
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
      simpa [hxy] using hguard
    have hRaw_ne_top :
        helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar (y - x) x ≠
          (⊤ : EReal) := by
      simpa [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hguard', hxy,
        sub_eq_add_neg] using
        (EReal.add_ne_top hfx_ne_top hnegGy_ne_top)
    have hLe :
        helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar (y - x) ≤
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar (y - x) x := by
      rw [helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction, functionInfimumEReal]
      exact iInf_le _ x
    exact lt_of_le_of_lt hLe (lt_top_iff_ne_top.mpr hRaw_ne_top)

/-- Helper for Theorem 38.5: the finite branch can be rephrased at the corrected second-shift
value because both the legacy surrogate and the corrected perturbation recover the same primal
infimum at the origin. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuardedValueAtZero_finite_of_legacyFiniteAtZero
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hp0_finite :
      IsFiniteEReal
        (helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0)) :
    IsFiniteEReal
      (helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0) := by
  rw [helperForTheorem_38_5_textbookSecondShiftGuardedValueAtZero_eq_fenchelPrimalInfimum
    (F := F) (G := G) (yStar := yStar) (uStar := uStar)]
  simpa [helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction, fenchelPrimalInfimum,
    functionInfimumEReal] using hp0_finite

/-- Helper for Theorem 38.5: the qualification hypothesis and finiteness at the origin produce a
supporting vector for the guarded value function at `z = 0`. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuarded_supportingVector_of_legacyFiniteAtZero_and_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hF_properConvex : ProperConvexBifunction F.toFun)
    (hG_properConvex : ProperConvexBifunction G.toFun)
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    (hp0_finite :
      IsFiniteEReal
        (helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0)) :
    ∃ zStar : Fin n → ℝ,
      ∀ z : Fin n → ℝ,
        helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar z +
            (((dotProduct zStar z : ℝ) : EReal)) ≥
          helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0 := by
  let p : (Fin n → ℝ) → EReal :=
    helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar
  let domF : Set (Fin n → ℝ) := bifunctionDomBot (bifunctionInverse F.toFun)
  let domG : Set (Fin n → ℝ) := bifunctionDom G.toFun
  have hpConv : ConvexFunction p := by
    -- The value function is the fiber infimum of the packed convex objective.
    simpa [p] using
      helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction_convex
        (F := F) (G := G) (yStar := yStar) (uStar := uStar)
        hF_properConvex hG_properConvex
  have hpFinite :
      p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) := by
    simpa [p] using
      helperForTheorem_38_5_textbookSecondShiftGuardedValueAtZero_finite_of_legacyFiniteAtZero
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) hp0_finite
  have hDom :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) p = domG - domF := by
    simpa [p, domF, domG] using
      helperForTheorem_38_5_textbookSecondShiftGuardedValue_effectiveDomain_eq_domainDifference
        (F := F) (G := G) (yStar := yStar) (uStar := uStar)
  have hConvF : Convex ℝ domF := by
    have hconv :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) :=
      helperForTheorem_38_5_textbookPrimalMiddleFunction_convexOn
        (F := F) (uStar := -uStar) hF_properConvex
    simpa [domF, helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain] using
      effectiveDomain_convex
        (S := (Set.univ : Set (Fin n → ℝ)))
        (f := helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) hconv
  have hConvG : Convex ℝ domG := by
    have hconv :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (fun x : Fin n → ℝ => -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x)) :=
      helperForTheorem_38_5_neg_textbookDualMiddleFunction_negDual_convexOn
        (G := G) (yStar := yStar) hG_properConvex
    have hconvDom :
        Convex ℝ
          (concaveEffectiveDomain (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))) := by
      simpa [concaveEffectiveDomain] using
        effectiveDomain_convex
          (S := (Set.univ : Set (Fin n → ℝ)))
          (f := fun x : Fin n → ℝ =>
            -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x))
          hconv
    simpa [domG, helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using
      hconvDom
  rcases hri with ⟨x0, hx0F_intr, hx0G_intr⟩
  have hx0G_intr' : x0 ∈ intrinsicInterior ℝ domG := by
    simpa only [domG] using hx0G_intr
  have hx0F_intr' : x0 ∈ intrinsicInterior ℝ domF := by
    simpa only [domF] using hx0F_intr
  have hzero_intr :
      (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ (domG - domF) := by
    -- The common relative-interior point witnesses that `0` lies in the translated domain.
    have hsubEq :
        intrinsicInterior ℝ (domG - domF) =
          intrinsicInterior ℝ domG - intrinsicInterior ℝ domF :=
      intrinsicInterior_sub_eq (n := n) (C₁ := domG) (C₂ := domF) hConvG hConvF
    rw [hsubEq]
    change (0 : Fin n → ℝ) ∈
      Set.image2 (fun a b : Fin n → ℝ => a - b)
        (intrinsicInterior ℝ domG) (intrinsicInterior ℝ domF)
    exact ⟨x0, hx0G_intr', x0, hx0F_intr', sub_self x0⟩
  have hzero_ri :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) p) := by
    rw [hDom]
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
    exact hzero_intr
  have hSub : Set.Nonempty (subdifferentialAt p 0) := by
    by_contra hEmpty
    have h23 :=
      (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
        p hpConv 0 hpFinite).2 hEmpty
    rcases convex_directionalDerivative_monotone_exists_and_sublinear p hpConv 0 hpFinite with
      ⟨_hdir, _hpos, _hconv, hzero, _hsymm⟩
    have hbot :
        upperDirectionalDerivativeAt p 0 (0 : Fin n → ℝ) = (⊥ : EReal) := by
      simpa using (h23.2 0 hzero_ri).1
    have hzeroBot : ((0 : ℝ) : EReal) = (⊥ : EReal) := by
      exact hzero.symm.trans hbot
    exact EReal.coe_ne_bot 0 hzeroBot
  rcases hSub with ⟨g, hg⟩
  let v : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g
  have hv : v ∈ euclideanSubdifferentialAt p 0 := by
    simpa [v, euclideanSubdifferentialAt] using hg
  refine ⟨-v, ?_⟩
  -- Convert the subgradient at `0` into the textbook supporting inequality.
  exact
    (helperForTheorem_6_29_1_neg_mem_euclideanSubdifferentialAt_zero_iff_supporting_inequality
      p (-v)).1 (by simpa using hv)

/-- Helper for Theorem 38.5: a supporting vector for the guarded value function already gives the
Fenchel dual lower bound needed in the finite branch. -/
lemma helperForTheorem_38_5_textbookSecondShiftGuarded_dualObjectiveLowerBound_of_supportingVector
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty)
    {zStar : Fin n → ℝ}
    (hSupport :
      ∀ z : Fin n → ℝ,
        helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar z +
            (((dotProduct zStar z : ℝ) : EReal)) ≥
          helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0) :
    helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar 0 ≤
      fenchelDualObjective
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
        zStar := by
  let pVal : (Fin n → ℝ) → EReal :=
    helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar
  let f : (Fin n → ℝ) → EReal := helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)
  let g : (Fin n → ℝ) → EReal := helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)
  let BX : (Fin n → ℝ) → EReal :=
    fun x => f x - (((dotProduct zStar x : ℝ) : EReal))
  let AY : (Fin n → ℝ) → EReal :=
    fun y => (((dotProduct zStar y : ℝ) : EReal) - g y)
  let XF : Set (Fin n → ℝ) := bifunctionDomBot (bifunctionInverse F.toFun)
  let YG : Set (Fin n → ℝ) := bifunctionDom G.toFun
  have hBX_top : ∀ {x : Fin n → ℝ}, x ∉ XF → BX x = (⊤ : EReal) := by
    intro x hx
    have hxF : x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
      simpa [f, XF, helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain] using hx
    have hAllTopF : ∀ u : Fin m → ℝ, F.toFun u x = (⊤ : EReal) := by
      intro u
      by_contra hu
      apply hxF
      rw [effectiveDomain_eq]
      refine ⟨by simp, ?_⟩
      have hTerm_ne_top :
          (-((uStar u : ℝ) : EReal)) + F.toFun u x ≠ (⊤ : EReal) := by
        exact EReal.add_ne_top (EReal.coe_ne_top _) hu
      have hle :
          f x ≤ (-((uStar u : ℝ) : EReal)) + F.toFun u x := by
        simpa [f, helperForTheorem_38_5_textbookPrimalMiddleFunction] using
          (iInf_le (fun u' : Fin m → ℝ => (-((uStar u' : ℝ) : EReal)) + F.toFun u' x) u)
      exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hTerm_ne_top)
    have hfx_top : f x = (⊤ : EReal) := by
      change (⨅ u : Fin m → ℝ, (-((uStar u : ℝ) : EReal)) + F.toFun u x) = (⊤ : EReal)
      apply le_antisymm le_top
      refine le_iInf ?_
      intro u
      have hTerm :
          (-((uStar u : ℝ) : EReal)) + F.toFun u x = (⊤ : EReal) := by
        simpa [hAllTopF u] using EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)
      rw [hTerm]
    simp [BX, hfx_top, sub_eq_add_neg]
  have hAY_top : ∀ {y : Fin n → ℝ}, y ∉ YG → AY y = (⊤ : EReal) := by
    intro y hy
    have hyG : y ∉ concaveEffectiveDomain g := by
      simpa [g, YG, helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using hy
    have hneg_top : -(g y) = (⊤ : EReal) := by
      by_contra hneg
      apply hyG
      rw [concaveEffectiveDomain, effectiveDomain_eq]
      exact ⟨by simp, lt_top_iff_ne_top.mpr hneg⟩
    have hgy_bot : g y = (⊥ : EReal) := by
      simpa using congrArg Neg.neg hneg_top
    simp [AY, hgy_bot, sub_eq_add_neg]
  have hProdLe :
      pVal 0 ≤
        (⨅ q : {x : Fin n → ℝ // x ∈ XF} × {y : Fin n → ℝ // y ∈ YG},
          BX q.1.1 + AY q.2.1) := by
    refine le_iInf ?_
    intro q
    have hValueLe :
        helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar
            (q.2.1 - q.1.1) ≤
          helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar
            (q.2.1 - q.1.1) q.1.1 := by
      rw [helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction, functionInfimumEReal]
      exact iInf_le _ q.1.1
    have hguard :
        q.1.1 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
          (q.1.1 + (q.2.1 - q.1.1)) ∈
            concaveEffectiveDomain
              (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
      constructor
      · simpa [helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain] using q.1.2
      · simpa [helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using q.2.2
    have hxy : q.1.1 + (q.2.1 - q.1.1) = q.2.1 := by
      ext i
      simp
    have hguard' :
        q.1.1 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∧
          q.2.1 ∈ concaveEffectiveDomain
              (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
      simpa [hxy] using hguard
    have hRawEq :
        helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw F G yStar uStar
            (q.2.1 - q.1.1) q.1.1 =
          helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) q.1.1 -
            helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) q.2.1 := by
      simp [helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw, hguard', hxy]
    have hShifted :
        pVal 0 ≤
          helperForTheorem_38_5_textbookSecondShiftGuardedValueFunction F G yStar uStar
              (q.2.1 - q.1.1) +
            (((dotProduct zStar (q.2.1 - q.1.1) : ℝ) : EReal)) := by
      simpa [pVal, ge_iff_le] using hSupport (q.2.1 - q.1.1)
    have hPointwise :
        pVal 0 ≤
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) q.1.1 -
              helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) q.2.1) +
            (((dotProduct zStar (q.2.1 - q.1.1) : ℝ) : EReal)) := by
      exact le_trans hShifted <| by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_right (hValueLe.trans_eq hRawEq)
            ((((dotProduct zStar (q.2.1 - q.1.1) : ℝ) : EReal)))
    simpa [BX, AY, sub_eq_add_neg, dotProduct_sub, add_assoc, add_left_comm, add_comm] using
      hPointwise
  rcases hri with ⟨x0, hx0F, hx0G⟩
  have hx0F_mem : x0 ∈ XF := by
    exact intrinsicInterior_subset (𝕜 := ℝ) (s := XF) hx0F
  have hx0G_mem : x0 ∈ YG := by
    exact intrinsicInterior_subset (𝕜 := ℝ) (s := YG) hx0G
  letI : Nonempty {x : Fin n → ℝ // x ∈ XF} := ⟨⟨x0, hx0F_mem⟩⟩
  letI : Nonempty {y : Fin n → ℝ // y ∈ YG} := ⟨⟨x0, hx0G_mem⟩⟩
  have hBX_finite : ∃ x : {x : Fin n → ℝ // x ∈ XF}, BX x.1 < (⊤ : EReal) := by
    refine ⟨⟨x0, hx0F_mem⟩, ?_⟩
    have hx0eff : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
      simpa [f, XF, helperForTheorem_38_5_textbookPrimalMiddleFunction_effectiveDomain] using hx0F_mem
    rw [effectiveDomain_eq] at hx0eff
    have hfx_ne_top : f x0 ≠ (⊤ : EReal) := ne_of_lt hx0eff.2
    exact lt_top_iff_ne_top.mpr <| by
      simpa [BX, sub_eq_add_neg] using
        EReal.add_ne_top hfx_ne_top (EReal.coe_ne_top _)
  have hAY_finite : ∃ y : {y : Fin n → ℝ // y ∈ YG}, AY y.1 < (⊤ : EReal) := by
    refine ⟨⟨x0, hx0G_mem⟩, ?_⟩
    have hx0eff : x0 ∈ concaveEffectiveDomain g := by
      simpa [g, YG, helperForTheorem_38_5_textbookDualMiddleFunction_concaveEffectiveDomain] using hx0G_mem
    rw [concaveEffectiveDomain, effectiveDomain_eq] at hx0eff
    have hneg_ne_top : -(g x0) ≠ (⊤ : EReal) := ne_of_lt hx0eff.2
    exact lt_top_iff_ne_top.mpr <| by
      simpa [AY, sub_eq_add_neg] using
        EReal.add_ne_top (EReal.coe_ne_top _) hneg_ne_top
  have hSplitSubtype :
      (⨅ q : {x : Fin n → ℝ // x ∈ XF} × {y : Fin n → ℝ // y ∈ YG},
          BX q.1.1 + AY q.2.1) =
        (⨅ x : {x : Fin n → ℝ // x ∈ XF}, BX x.1) +
          (⨅ y : {y : Fin n → ℝ // y ∈ YG}, AY y.1) := by
    simpa using
      helperForTheorem_6_30_22_twoFactor_iInf_eq_iInf_add_iInf
        (F := fun x : {x : Fin n → ℝ // x ∈ XF} => BX x.1)
        (G := fun y : {y : Fin n → ℝ // y ∈ YG} => AY y.1)
        hBX_finite hAY_finite
  have hRestrictBX :
      (⨅ x : {x : Fin n → ℝ // x ∈ XF}, BX x.1) = ⨅ x : Fin n → ℝ, BX x := by
    apply le_antisymm
    · refine le_iInf ?_
      intro x
      by_cases hx : x ∈ XF
      · exact iInf_le (fun x' : {x : Fin n → ℝ // x ∈ XF} => BX x'.1) ⟨x, hx⟩
      · rw [hBX_top (x := x) hx]
        exact le_top
    · refine le_iInf ?_
      intro x
      exact iInf_le BX x.1
  have hRestrictAY :
      (⨅ y : {y : Fin n → ℝ // y ∈ YG}, AY y.1) = ⨅ y : Fin n → ℝ, AY y := by
    apply le_antisymm
    · refine le_iInf ?_
      intro y
      by_cases hy : y ∈ YG
      · exact iInf_le (fun y' : {y : Fin n → ℝ // y ∈ YG} => AY y'.1) ⟨y, hy⟩
      · rw [hAY_top (y := y) hy]
        exact le_top
    · refine le_iInf ?_
      intro y
      exact iInf_le AY y.1
  calc
    pVal 0 ≤
      (⨅ q : {x : Fin n → ℝ // x ∈ XF} × {y : Fin n → ℝ // y ∈ YG},
          BX q.1.1 + AY q.2.1) := hProdLe
    _ = (⨅ x : {x : Fin n → ℝ // x ∈ XF}, BX x.1) +
          (⨅ y : {y : Fin n → ℝ // y ∈ YG}, AY y.1) := hSplitSubtype
    _ = (⨅ x : Fin n → ℝ, BX x) + (⨅ y : Fin n → ℝ, AY y) := by
          rw [hRestrictBX, hRestrictAY]
    _ = fenchelDualObjective f g zStar := by
          rw [fenchelDualObjective,
            helperForLemma_31_0_11_concaveFenchelConjugate_eq_iInf]
          simp [BX, AY, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            dotProduct_comm, helperForLemma_31_0_11_neg_fenchelConjugate_eq_iInf]

/-- Helper for Theorem 38.5: at `z = 0`, the legacy common-shift surrogate still agrees with the
Fenchel primal infimum of the middle-function pair. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_eq_fenchelPrimalInfimum
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 =
      fenchelPrimalInfimum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
  simp [helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction, fenchelPrimalInfimum,
    functionInfimumEReal]

/-- Helper for Theorem 38.5: under the qualification hypothesis, the legacy common-shift surrogate
at `0` cannot be `⊤`, because condition `(a)` supplies a common-domain point where the guarded
primal objective is an actual extended-real difference. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_ne_top_of_hri
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hri :
      (intrinsicInterior ℝ (bifunctionDomBot (bifunctionInverse F.toFun)) ∩
        intrinsicInterior ℝ (bifunctionDom G.toFun)).Nonempty) :
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 ≠
      (⊤ : EReal) := by
  have hFenchelA :
      FenchelConditionA (n := n)
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
    exact
      helperForTheorem_38_5_hri_implies_fenchelConditionA
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) hri
  rcases hFenchelA with ⟨x0, hx0riF, hx0riG⟩
  have hx0F :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))) hx0riF
  have hx0G :
      x0 ∈ concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) :=
    helperForTheorem_21_1_riFin_subset_C (n := n)
      (concaveEffectiveDomain
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))) hx0riG
  have hx0Common :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) ∩
        concaveEffectiveDomain
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) :=
    ⟨hx0F, hx0G⟩
  have hfx0_ne_top :
      helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → ℝ)))
      (f := helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar)) hx0F
  have hgx0_ne_bot :
      helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0 ≠ (⊥ : EReal) := by
    intro hgx0_bot
    have hx0G' :
        x0 ∈ (Set.univ : Set (Fin n → ℝ)) ∧
          (-(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0)) < (⊤ : EReal) := by
      simpa [concaveEffectiveDomain, effectiveDomain_eq] using hx0G
    have : -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0) = (⊤ : EReal) := by
      simpa [hgx0_bot] using
        (show -(helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0) =
            (-(⊥ : EReal)) from rfl)
    exact (lt_top_iff_ne_top).1 hx0G'.2 (by simpa [this])
  have hSample_ne_top :
      commonBookEffectiveDomainDifference
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          x0 ≠ (⊤ : EReal) := by
    rw [commonBookEffectiveDomainDifference, if_pos hx0Common]
    cases hfx0 : helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar) x0 with
    | top =>
        exact (hfx0_ne_top hfx0).elim
    | bot =>
        cases hgx0 : helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0 with
        | bot =>
            exact (hgx0_ne_bot hgx0).elim
        | top =>
            simp
        | coe s =>
            simp
    | coe r =>
        cases hgx0 : helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar) x0 with
        | bot =>
            exact (hgx0_ne_bot hgx0).elim
        | top =>
            simp
        | coe s =>
            simpa [hfx0, hgx0, EReal.coe_sub] using (EReal.coe_ne_top (r - s))
  have hLeSample_raw :
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 ≤
        commonBookEffectiveDomainDifference
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          (x0 + 0) := by
    rw [helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction, functionInfimumEReal]
    exact
      iInf_le
        (fun x : Fin n → ℝ =>
          commonBookEffectiveDomainDifference
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
            (x + 0))
        x0
  have hLeSample :
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 ≤
        commonBookEffectiveDomainDifference
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          x0 := by
    simpa using hLeSample_raw
  intro hp0_top
  have hTopLeSample :
      (⊤ : EReal) ≤
        commonBookEffectiveDomainDifference
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          x0 := by
    simpa [hp0_top] using hLeSample
  exact hSample_ne_top ((top_le_iff.mp hTopLeSample))

/-- Helper for Theorem 38.5: the current theorem-local strong-duality target phrased through the
legacy common-shift surrogate at `0`. The corrected second-shift value function above is the
object that matches the original Chapter 31 perturbation route. -/
abbrev helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) : Prop :=
  helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 =
    fenchelDualSupremum
      (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
      (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) ∧
    ∃ xStarVec : Fin n → ℝ,
      fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
        fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          xStarVec

/-- Helper for Theorem 38.5: the raw Section 29 perturbation family attached to the legacy
common-shift surrogate. It is useful for the current finite-branch scaffold, but the corrected
original-text perturbation is `helperForTheorem_38_5_textbookSecondShiftGuardedPerturbationRaw`.
-/
noncomputable def helperForTheorem_38_5_textbookGuardedTranslatedPerturbationRaw
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    (Fin n → ℝ) → (Fin n → ℝ) → EReal :=
  fun z x =>
    commonBookEffectiveDomainDifference
      (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
      (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
      (x + z)

/-- Helper for Theorem 38.5: the translated value function is the perturbation infimum of the raw
guarded translated family. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceValue_eq_rawPerturbation_apply
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (z : Fin n → ℝ) :
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar z =
      functionInfimumEReal
        (helperForTheorem_38_5_textbookGuardedTranslatedPerturbationRaw
          F G yStar uStar z) := by
  simp [helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction,
    helperForTheorem_38_5_textbookGuardedTranslatedPerturbationRaw, functionInfimumEReal]

/-- Helper for Theorem 38.5: because the guard is applied after the common translation `x ↦ x + z`,
the translated value function is actually constant in `z`. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceValue_eq_at_zero
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (z : Fin n → ℝ) :
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar z =
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 := by
  let h :
      (Fin n → ℝ) → EReal :=
    commonBookEffectiveDomainDifference
      (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
      (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
  have hShift :
      (⨅ x : Fin n → ℝ, h (x + z)) = ⨅ x : Fin n → ℝ, h x := by
    let e : (Fin n → ℝ) ≃ (Fin n → ℝ) :=
      { toFun := fun x => x + z
        invFun := fun x => x - z
        left_inv := by
          intro x
          ext i
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        right_inv := by
          intro x
          ext i
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] }
    calc
      (⨅ x : Fin n → ℝ, h (x + z)) = ⨅ x : Fin n → ℝ, h (e x) := by
        simp [e]
      _ = ⨅ x : Fin n → ℝ, h x := by
        exact Equiv.iInf_congr e (fun x => rfl)
  calc
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar z =
      (⨅ x : Fin n → ℝ, h (x + z)) := by
        simp [helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction, h,
          functionInfimumEReal]
    _ = ⨅ x : Fin n → ℝ, h x := hShift
    _ = helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 := by
        simp [helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction, h,
          functionInfimumEReal]

/-- Helper for Theorem 38.5: the translated value function equals the primal infimum at every
shift, not only at `0`. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceValue_eq_fenchelPrimalInfimum
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (z : Fin n → ℝ) :
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar z =
      fenchelPrimalInfimum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
  calc
    helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar z =
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 := by
        exact
          helperForTheorem_38_5_textbookTranslatedDifferenceValue_eq_at_zero
            (F := F) (G := G) (yStar := yStar) (uStar := uStar) (z := z)
    _ =
      fenchelPrimalInfimum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
          exact
            helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_eq_fenchelPrimalInfimum
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)

/-- Helper for Theorem 38.5: if the translated value at `0` is finite, then the whole translated
value function is finite because it is constant. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceValue_finite_everywhere_of_finiteAtZero
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hp0_finite :
      IsFiniteEReal
        (helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0)) :
    ∀ z : Fin n → ℝ,
      IsFiniteEReal
        (helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar z) := by
  intro z
  rw [helperForTheorem_38_5_textbookTranslatedDifferenceValue_eq_at_zero
    (F := F) (G := G) (yStar := yStar) (uStar := uStar) (z := z)]
  exact hp0_finite

/-- Helper for Theorem 38.5: the translated-value formulation at `0` is equivalent to the
middle-pair strong-duality formulation. -/
lemma helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality_iff_specialPairStrongDuality
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ)) :
    helperForTheorem_38_5_textbookTranslatedDifferenceStrongDuality F G yStar uStar ↔
      helperForTheorem_38_5_textbookSpecialPairStrongDuality F G yStar uStar := by
  constructor
  · rintro ⟨hEq, hAtt⟩
    refine ⟨?_, hAtt⟩
    calc
      fenchelPrimalInfimum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
        helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 := by
          symm
          exact
            helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_eq_fenchelPrimalInfimum
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)
      _ = fenchelDualSupremum
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := hEq
  · rintro ⟨hEq, hAtt⟩
    refine ⟨?_, hAtt⟩
    calc
      helperForTheorem_38_5_textbookTranslatedDifferenceValueFunction F G yStar uStar 0 =
        fenchelPrimalInfimum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
          exact
            helperForTheorem_38_5_textbookTranslatedDifferenceValueAtZero_eq_fenchelPrimalInfimum
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)
      _ = fenchelDualSupremum
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := hEq

/-- Helper for Theorem 38.5: a maximizing middle dual vector for the textbook dual objective
produces the `Module.Dual` witness required by the bifunction statement. -/
lemma helperForTheorem_38_5_moduleDualWitness_of_textbookSpecialPairDualAttainer
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    {xStarVec : Fin n → ℝ}
    (hAtt :
      fenchelDualSupremum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) =
        fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          xStarVec) :
    ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
      bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
          yStar uStar =
        (bifunctionAdjoint G.toFun) yStar xStar + (bifunctionAdjoint F.toFun) xStar uStar := by
  refine ⟨dotProductEquiv ℝ (Fin n) (-xStarVec), ?_⟩
  calc
    bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
        yStar uStar =
      fenchelDualSupremum
        (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
        (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
          exact
            helperForTheorem_38_5_composeSupGeneric_eq_fenchelDualSupremum
              (F := F) (G := G) (yStar := yStar) (uStar := uStar)
    _ = fenchelDualObjective
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar))
          xStarVec := hAtt
    _ = (bifunctionAdjoint G.toFun) yStar (dotProductEquiv ℝ (Fin n) (-xStarVec)) +
          (bifunctionAdjoint F.toFun) (dotProductEquiv ℝ (Fin n) (-xStarVec)) uStar := by
          rw [helperForTheorem_38_5_adjoint_secondFactor_eq_concaveFenchelConjugate_textbookDual,
            helperForTheorem_38_5_adjoint_firstFactor_eq_neg_fenchelConjugate_textbookPrimal]
          simp [fenchelDualObjective, sub_eq_add_neg]

/-- Helper for Theorem 38.5: once the textbook middle-function pair satisfies pointwise strong
duality and dual attainment, the displayed bifunction dual identity and the `Module.Dual`
attainment clause follow immediately. -/
lemma helperForTheorem_38_5_pointwiseConclusion_of_textbookSpecialPairStrongDuality
    {m n p : Nat} (F : FiberwiseProperConvexBifunction m n)
    (G : FiberwiseProperConvexBifunction n p)
    (yStar : Module.Dual ℝ (Fin p → ℝ))
    (uStar : Module.Dual ℝ (Fin m → ℝ))
    (hStrong : helperForTheorem_38_5_textbookSpecialPairStrongDuality F G yStar uStar) :
    bifunctionAdjoint (bifunctionCompose G F) yStar uStar =
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
          yStar uStar ∧
      ∃ xStar : Module.Dual ℝ (Fin n → ℝ),
        bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
            yStar uStar =
          (bifunctionAdjoint G.toFun) yStar xStar + (bifunctionAdjoint F.toFun) xStar uStar := by
  rcases hStrong with ⟨hEqMiddle, hAttMiddle⟩
  constructor
  · calc
      bifunctionAdjoint (bifunctionCompose G F) yStar uStar =
        fenchelPrimalInfimum
          (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
          (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := by
            exact
              helperForTheorem_38_5_adjoint_compose_eq_fenchelPrimalInfimum
                (F := F) (G := G) (yStar := yStar) (uStar := uStar)
      _ = fenchelDualSupremum
            (helperForTheorem_38_5_textbookPrimalMiddleFunction F (-uStar))
            (helperForTheorem_38_5_textbookDualMiddleFunction G (-yStar)) := hEqMiddle
      _ = bifunctionComposeSupGeneric (bifunctionAdjoint F.toFun) (bifunctionAdjoint G.toFun)
            yStar uStar := by
              symm
              exact
                helperForTheorem_38_5_composeSupGeneric_eq_fenchelDualSupremum
                  (F := F) (G := G) (yStar := yStar) (uStar := uStar)
  · rcases hAttMiddle with ⟨xStarVec, hxStarVec⟩
    exact
      helperForTheorem_38_5_moduleDualWitness_of_textbookSpecialPairDualAttainer
        (F := F) (G := G) (yStar := yStar) (uStar := uStar) hxStarVec


end Section38
end Chap08

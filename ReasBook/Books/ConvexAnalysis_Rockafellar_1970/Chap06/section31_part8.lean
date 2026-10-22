/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part7

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

lemma helperForTheorem_31_1_conditionB_concaveDuality_core {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hB : FenchelConditionB (n := n) f g) :
    fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
      ∃ x : Fin n → ℝ, fenchelPrimalInfimum f g = commonBookEffectiveDomainDifference f g x := by
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
  rcases hB with ⟨hfClosed, hgClosed, hRiStar⟩
  have hfStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar := by
    simpa [fStar] using proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hgStar :
      ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
    simpa [gStar] using
      helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
        (n := n) (g := g) hg
  -- Build condition (a) for the conjugate pair from condition (b) for the original pair.
  have hAStar : FenchelConditionA (n := n) fStar gStar := by
    rcases hRiStar with ⟨xStar, hxRiDomGStar, hxRiDomFStar⟩
    refine ⟨xStar, ?_, ?_⟩
    · simpa [fStar] using hxRiDomFStar
    · simpa [gStar, concaveEffectiveDomain, concaveConjugateEffectiveDomain] using hxRiDomGStar
  have hPairCore :
      fenchelPrimalInfimum fStar gStar = fenchelDualSupremum (n := n) fStar gStar ∧
        ∃ x : Fin n → ℝ, fenchelDualSupremum (n := n) fStar gStar = fenchelDualObjective (n := n) fStar gStar x :=
    helperForTheorem_31_1_conditionA_concaveDuality_core (n := n) fStar gStar hfStar hgStar hAStar
  exact
    helperForTheorem_31_1_translate_conjugatePair_duality_to_original
      (n := n) f g hf hg hfClosed hgClosed hPairCore.1 hPairCore.2

/-- Helper for Theorem 31.1: finish strong duality and dual attainment from a conjugate-of-sum
bridge at `0` and an attained decomposition of the corresponding infimal convolution, in the
ordered-pair convention `(h, f)` where `h = -g`. -/
lemma helperForTheorem_31_1_finishFromInfConv_hf {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hConjSum0 :
        fenchelConjugate n (fun x => f x + (-(g x))) 0 =
          infimalConvolution (fenchelConjugate n (fun x => -(g x))) (fenchelConjugate n f) 0)
    (hAttained0 :
        ∃ xStar : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n (fun x => -(g x))) (fenchelConjugate n f) 0 =
            fenchelConjugate n (fun x => -(g x)) (-xStar) + fenchelConjugate n f xStar) :
    fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
      ∃ xStar : Fin n → ℝ,
        fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar := by
  classical
  -- Introduce `h := -g`, so the guarded primal objective is pointwise `f + h`.
  let h : (Fin n → ℝ) → EReal := fun x => -(g x)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [ProperConcaveFunctionOn, h] using hg

  -- Step 1: rewrite the primal infimum as `- (f + h)⋆(0)`.
  have hCommonEq : commonBookEffectiveDomainDifference f g = fun x => f x + h x := by
    funext x
    by_cases hx :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g
    · -- On the common effective domain, `f - g = f + (-g)`.
      simp [commonBookEffectiveDomainDifference, hx, h, sub_eq_add_neg, add_assoc]
    · -- Outside the common domain, at least one term is `⊤`, hence the sum is `⊤` as well.
      have hxOr :
          x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∨
            x ∉ concaveEffectiveDomain g := by
        have : ¬ (x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
            x ∈ concaveEffectiveDomain g) := by
          simpa [Set.mem_inter_iff] using hx
        exact not_and_or.mp this
      cases hxOr with
      | inl hxNotDomF =>
          have hfTop : f x = (⊤ : EReal) :=
            not_mem_effectiveDomain_univ_imp_eq_top (f := f) hxNotDomF
          have hxUniv : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
            simp
          have hhNeBot : h x ≠ (⊥ : EReal) := hh.2.2 x hxUniv
          have hSumTop : f x + h x = (⊤ : EReal) := by
            simpa [hfTop] using (EReal.top_add_of_ne_bot hhNeBot)
          simp [commonBookEffectiveDomainDifference, hx, hSumTop]
      | inr hxNotDomG =>
          have hxNotDomH :
              x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
            simpa [concaveEffectiveDomain, h] using hxNotDomG
          have hhTop : h x = (⊤ : EReal) :=
            not_mem_effectiveDomain_univ_imp_eq_top (f := h) hxNotDomH
          have hxUniv : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
            simp
          have hfNeBot : f x ≠ (⊥ : EReal) := hf.2.2 x hxUniv
          have hSumTop : f x + h x = (⊤ : EReal) := by
            simpa [hhTop] using (EReal.add_top_of_ne_bot hfNeBot)
          simp [commonBookEffectiveDomainDifference, hx, hSumTop]
  have hPrimal_as_negConj0 :
      fenchelPrimalInfimum f g =
        -fenchelConjugate n (fun x => f x + h x) 0 := by
    -- Replace the guarded primal objective by the pointwise sum `f + h`.
    have :
        fenchelPrimalInfimum f g =
          functionInfimumEReal (fun x => f x + h x) := by
      simp [fenchelPrimalInfimum, hCommonEq]
    -- Convert the infimum into a conjugate-at-zero identity.
    have h0 :=
      fenchelConjugate_zero_eq_neg_iInf (n := n) (f := fun x => f x + h x)
    have h0' : -fenchelConjugate n (fun x => f x + h x) 0 =
        functionInfimumEReal (fun x => f x + h x) := by
      have := congrArg (fun a : EReal => -a) h0
      simpa [functionInfimumEReal] using this
    simpa [this] using h0'.symm

  -- Step 2: rewrite the dual supremum as `- (h⋆ □ f⋆)(0)`.
  have hInfConv0_eq_iInf :
      infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 =
        ⨅ xStar : Fin n → ℝ, fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar := by
    -- Unfold and eliminate `x1` from the constraint `x1 + x2 = 0`.
    unfold infimalConvolution
    have hset :
        {z : EReal |
            ∃ x1 x2 : Fin n → ℝ, x1 + x2 = (0 : Fin n → ℝ) ∧
              z = fenchelConjugate n h x1 + fenchelConjugate n f x2} =
          Set.range (fun xStar : Fin n → ℝ =>
            fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
      ext z
      constructor
      · rintro ⟨x1, x2, hsum, rfl⟩
        have hx1 : x1 = -x2 :=
          eq_neg_of_add_eq_zero_left hsum
        refine ⟨x2, ?_⟩
        simp [hx1, add_comm, add_left_comm, add_assoc]
      · rintro ⟨xStar, rfl⟩
        refine ⟨-xStar, xStar, ?_, rfl⟩
        simp
    simp [hset]
    rfl
  have hDual_as_negInfConv0 :
      fenchelDualSupremum (n := n) f g =
        -infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
    -- First rewrite the dual objective in terms of `h`.
    have hDualObj :
        (fun xStar : Fin n → ℝ => fenchelDualObjective (n := n) f g xStar) =
          (fun xStar : Fin n → ℝ =>
            -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar)) := by
      funext xStar
      -- Prepare the `≠ ⊥` hypotheses needed for `EReal.neg_add`.
      have hHstarProper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n h) :=
        proper_fenchelConjugate_of_proper (n := n) (f := h) hh
      have hFstarProper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
        proper_fenchelConjugate_of_proper (n := n) (f := f) hf
      have hxUnivNeg : (-xStar) ∈ (Set.univ : Set (Fin n → ℝ)) := by
        simp
      have hxUniv : xStar ∈ (Set.univ : Set (Fin n → ℝ)) := by
        simp
      have hA_ne_bot : fenchelConjugate n h (-xStar) ≠ (⊥ : EReal) :=
        hHstarProper.2.2 (-xStar) hxUnivNeg
      have hB_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
        hFstarProper.2.2 xStar hxUniv
      have hneg :
          (-fenchelConjugate n h (-xStar)) - fenchelConjugate n f xStar =
            -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
        simpa using
          (EReal.neg_add (x := fenchelConjugate n h (-xStar))
            (y := fenchelConjugate n f xStar)
            (h1 := Or.inl hA_ne_bot) (h2 := Or.inr hB_ne_bot)).symm
      simpa [fenchelDualObjective, concaveFenchelConjugate, h] using hneg
    -- Convert `sup (-a)` into `- inf a`.
    have hSupNeg :
        (⨆ xStar : Fin n → ℝ,
            -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar)) =
          - (⨅ xStar : Fin n → ℝ,
              fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
      simpa using (ereal_iSup_neg_eq_neg_iInf
        (g := fun xStar : Fin n → ℝ =>
          fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar))
    have hInfRewrite :
        (⨅ xStar : Fin n → ℝ, fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) =
          infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
      simpa [hInfConv0_eq_iInf] using rfl
    simp [fenchelDualSupremum, hDualObj, hSupNeg, hInfRewrite]

  -- Step 3: `hConjSum0` identifies both values as `- (f + h)⋆(0)`.
  have hEq : fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g := by
    have hConjSum0' :
        fenchelConjugate n (fun x => f x + h x) 0 =
          infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
      simpa [h] using hConjSum0
    have hNegConjSum0' :
        -fenchelConjugate n (fun x => f x + h x) 0 =
          -infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
      simpa using congrArg (fun t : EReal => -t) hConjSum0'
    calc
      fenchelPrimalInfimum f g
          = -fenchelConjugate n (fun x => f x + h x) 0 := hPrimal_as_negConj0
      _ = -infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
            simpa using hNegConjSum0'
      _ = fenchelDualSupremum (n := n) f g := by
            simpa [hDual_as_negInfConv0]

  -- Step 4: use the attained infimal-convolution decomposition to extract a dual maximizer.
  rcases hAttained0 with ⟨xStar, hValue⟩
  have hObj :
      fenchelDualObjective (n := n) f g xStar =
        -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
    -- Same `EReal.neg_add` rewrite as in the dual-value computation above.
    have hHstarProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n h) :=
      proper_fenchelConjugate_of_proper (n := n) (f := h) hh
    have hFstarProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
      proper_fenchelConjugate_of_proper (n := n) (f := f) hf
    have hxUnivNeg : (-xStar) ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hxUniv : xStar ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hA_ne_bot : fenchelConjugate n h (-xStar) ≠ (⊥ : EReal) :=
      hHstarProper.2.2 (-xStar) hxUnivNeg
    have hB_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
      hFstarProper.2.2 xStar hxUniv
    have hneg :
        (-fenchelConjugate n h (-xStar)) - fenchelConjugate n f xStar =
          -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
      simpa using
        (EReal.neg_add (x := fenchelConjugate n h (-xStar))
          (y := fenchelConjugate n f xStar)
          (h1 := Or.inl hA_ne_bot) (h2 := Or.inr hB_ne_bot)).symm
    simpa [fenchelDualObjective, concaveFenchelConjugate, h] using hneg
  have hDualAttained :
      fenchelDualSupremum (n := n) f g =
        fenchelDualObjective (n := n) f g xStar := by
    calc
      fenchelDualSupremum (n := n) f g
          = -infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := hDual_as_negInfConv0
      _ = -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
            simpa [hValue]
      _ = fenchelDualObjective (n := n) f g xStar := by
            simpa [hObj]

  refine And.intro hEq ?_
  exact ⟨xStar, hDualAttained⟩

/-- Helper for Theorem 31.1: finish strong duality and dual attainment from a conjugate-of-sum
bridge at `0` and an attained decomposition of the corresponding infimal convolution, in the
ordered-pair convention `(f, h)` where `h = -g` (this is the polyhedral-`f` branch). -/
lemma helperForTheorem_31_1_finishFromInfConv_fh {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hConjSum0 :
        fenchelConjugate n (fun x => f x + (-(g x))) 0 =
          infimalConvolution (fenchelConjugate n f) (fenchelConjugate n (fun x => -(g x))) 0)
    (hAttained0 :
        ∃ u : Fin n → ℝ,
          infimalConvolution (fenchelConjugate n f) (fenchelConjugate n (fun x => -(g x))) 0 =
            fenchelConjugate n f (-u) + fenchelConjugate n (fun x => -(g x)) u) :
    fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
      ∃ xStar : Fin n → ℝ,
        fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar := by
  classical
  -- Introduce `h := -g`, so again `f - g = f + h` on the common effective domain.
  let h : (Fin n → ℝ) → EReal := fun x => -(g x)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [ProperConcaveFunctionOn, h] using hg

  -- Step 1: same primal rewrite as in the `(h, f)` convention.
  have hCommonEq : commonBookEffectiveDomainDifference f g = fun x => f x + h x := by
    funext x
    by_cases hx :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g
    · simp [commonBookEffectiveDomainDifference, hx, h, sub_eq_add_neg, add_assoc]
    ·
      have hxOr :
          x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∨
            x ∉ concaveEffectiveDomain g := by
        have : ¬ (x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
            x ∈ concaveEffectiveDomain g) := by
          simpa [Set.mem_inter_iff] using hx
        exact not_and_or.mp this
      cases hxOr with
      | inl hxNotDomF =>
          have hfTop : f x = (⊤ : EReal) :=
            not_mem_effectiveDomain_univ_imp_eq_top (f := f) hxNotDomF
          have hxUniv : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
            simp
          have hhNeBot : h x ≠ (⊥ : EReal) := hh.2.2 x hxUniv
          have hSumTop : f x + h x = (⊤ : EReal) := by
            simpa [hfTop] using (EReal.top_add_of_ne_bot hhNeBot)
          simp [commonBookEffectiveDomainDifference, hx, hSumTop]
      | inr hxNotDomG =>
          have hxNotDomH :
              x ∉ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
            simpa [concaveEffectiveDomain, h] using hxNotDomG
          have hhTop : h x = (⊤ : EReal) :=
            not_mem_effectiveDomain_univ_imp_eq_top (f := h) hxNotDomH
          have hxUniv : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
            simp
          have hfNeBot : f x ≠ (⊥ : EReal) := hf.2.2 x hxUniv
          have hSumTop : f x + h x = (⊤ : EReal) := by
            simpa [hhTop] using (EReal.add_top_of_ne_bot hfNeBot)
          simp [commonBookEffectiveDomainDifference, hx, hSumTop]
  have hPrimal_as_negConj0 :
      fenchelPrimalInfimum f g =
        -fenchelConjugate n (fun x => f x + h x) 0 := by
    have :
        fenchelPrimalInfimum f g =
          functionInfimumEReal (fun x => f x + h x) := by
      simp [fenchelPrimalInfimum, hCommonEq]
    have h0 :=
      fenchelConjugate_zero_eq_neg_iInf (n := n) (f := fun x => f x + h x)
    have h0' : -fenchelConjugate n (fun x => f x + h x) 0 =
        functionInfimumEReal (fun x => f x + h x) := by
      have := congrArg (fun a : EReal => -a) h0
      simpa [functionInfimumEReal] using this
    simpa [this] using h0'.symm

  -- Step 2: identify the dual value as `-(f⋆ □ h⋆)(0)` by reparameterizing `xStar ↦ -xStar`.
  have hInfConv0_eq_iInf :
      infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 =
        ⨅ u : Fin n → ℝ, fenchelConjugate n f (-u) + fenchelConjugate n h u := by
    unfold infimalConvolution
    have hset :
        {z : EReal |
            ∃ x1 x2 : Fin n → ℝ, x1 + x2 = (0 : Fin n → ℝ) ∧
              z = fenchelConjugate n f x1 + fenchelConjugate n h x2} =
          Set.range (fun u : Fin n → ℝ =>
            fenchelConjugate n f (-u) + fenchelConjugate n h u) := by
      ext z
      constructor
      · rintro ⟨x1, x2, hsum, rfl⟩
        have hx1 : x1 = -x2 :=
          eq_neg_of_add_eq_zero_left hsum
        refine ⟨x2, ?_⟩
        simp [hx1, add_comm, add_left_comm, add_assoc]
      · rintro ⟨u, rfl⟩
        refine ⟨-u, u, ?_, rfl⟩
        simp
    simp [hset]
    rfl

  have hDual_as_negInfConv0 :
      fenchelDualSupremum (n := n) f g =
        -infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 := by
    -- Rewrite the dual objective as in the core proof, then change variables `xStar ↦ -xStar`.
    have hDualObj :
        (fun xStar : Fin n → ℝ => fenchelDualObjective (n := n) f g xStar) =
          (fun xStar : Fin n → ℝ =>
            -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar)) := by
      funext xStar
      have hHstarProper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n h) :=
        proper_fenchelConjugate_of_proper (n := n) (f := h) hh
      have hFstarProper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
        proper_fenchelConjugate_of_proper (n := n) (f := f) hf
      have hxUnivNeg : (-xStar) ∈ (Set.univ : Set (Fin n → ℝ)) := by
        simp
      have hxUniv : xStar ∈ (Set.univ : Set (Fin n → ℝ)) := by
        simp
      have hA_ne_bot : fenchelConjugate n h (-xStar) ≠ (⊥ : EReal) :=
        hHstarProper.2.2 (-xStar) hxUnivNeg
      have hB_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
        hFstarProper.2.2 xStar hxUniv
      have hneg :
          (-fenchelConjugate n h (-xStar)) - fenchelConjugate n f xStar =
            -(fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar) := by
        simpa using
          (EReal.neg_add (x := fenchelConjugate n h (-xStar))
            (y := fenchelConjugate n f xStar)
            (h1 := Or.inl hA_ne_bot) (h2 := Or.inr hB_ne_bot)).symm
      simpa [fenchelDualObjective, concaveFenchelConjugate, h] using hneg
    -- Route correction: for the polyhedral-`f` branch we reparameterize `xStar ↦ -xStar`
    -- so that the `iInf` matches the swapped infimal-convolution order `(f⋆, h⋆)`.
    have hReparam :
        (⨆ xStar : Fin n → ℝ, fenchelDualObjective (n := n) f g xStar) =
          (⨆ u : Fin n → ℝ, fenchelDualObjective (n := n) f g (-u)) := by
      refine le_antisymm ?_ ?_
      · refine iSup_le ?_
        intro xStar
        have hLe : fenchelDualObjective (n := n) f g xStar ≤
            (⨆ u : Fin n → ℝ, fenchelDualObjective (n := n) f g (-u)) := by
          -- Choose `u := -xStar`.
          simpa using
            (le_iSup (fun u : Fin n → ℝ => fenchelDualObjective (n := n) f g (-u)) (-xStar))
        simpa using hLe
      · refine iSup_le ?_
        intro u
        have hLe : fenchelDualObjective (n := n) f g (-u) ≤
            (⨆ xStar : Fin n → ℝ, fenchelDualObjective (n := n) f g xStar) := by
          simpa using (le_iSup (fun xStar : Fin n → ℝ => fenchelDualObjective (n := n) f g xStar) (-u))
        simpa using hLe
    -- Now rewrite `dualObj (-u)` into `-(f⋆ (-u) + h⋆ u)` and convert `sup (-a)` into `-inf a`.
    have hDualObjNeg :
        (fun u : Fin n → ℝ => fenchelDualObjective (n := n) f g (-u)) =
          (fun u : Fin n → ℝ => -(fenchelConjugate n f (-u) + fenchelConjugate n h u)) := by
      funext u
      -- Expand via `hDualObj` and commute the addends.
      have : fenchelDualObjective (n := n) f g (-u) =
          -(fenchelConjugate n h u + fenchelConjugate n f (-u)) := by
        simpa [hDualObj] using (congrArg (fun t => t (-u)) hDualObj)
      -- Commute `h⋆ u + f⋆ (-u)` into `f⋆ (-u) + h⋆ u`.
      simpa [add_comm, add_left_comm, add_assoc] using this
    have hSupNeg :
        (⨆ u : Fin n → ℝ, -(fenchelConjugate n f (-u) + fenchelConjugate n h u)) =
          - (⨅ u : Fin n → ℝ, fenchelConjugate n f (-u) + fenchelConjugate n h u) := by
      simpa using (ereal_iSup_neg_eq_neg_iInf
        (g := fun u : Fin n → ℝ =>
          fenchelConjugate n f (-u) + fenchelConjugate n h u))
    have hInfRewrite :
        (⨅ u : Fin n → ℝ, fenchelConjugate n f (-u) + fenchelConjugate n h u) =
          infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 := by
      simpa [hInfConv0_eq_iInf] using rfl
    -- Put everything together.
    simp [fenchelDualSupremum, hReparam, hDualObjNeg, hSupNeg, hInfRewrite]

  -- Step 3: the bridge at `0` yields equality of primal and dual values.
  have hEq : fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g := by
    have hConjSum0' :
        fenchelConjugate n (fun x => f x + h x) 0 =
          infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 := by
      simpa [h] using hConjSum0
    have hNegConjSum0' :
        -fenchelConjugate n (fun x => f x + h x) 0 =
          -infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 := by
      simpa using congrArg (fun t : EReal => -t) hConjSum0'
    calc
      fenchelPrimalInfimum f g
          = -fenchelConjugate n (fun x => f x + h x) 0 := hPrimal_as_negConj0
      _ = -infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 := by
            -- `hConjSum0` already matches the `(f, h)` order.
            simpa using hNegConjSum0'
      _ = fenchelDualSupremum (n := n) f g := by
            simpa [hDual_as_negInfConv0]

  -- Step 4: extract a maximizing dual variable from the attained infimal convolution at `0`.
  rcases hAttained0 with ⟨u, hValue⟩
  let xStar : Fin n → ℝ := -u
  have hObj_at_xStar :
      fenchelDualObjective (n := n) f g xStar =
        -(fenchelConjugate n f (-u) + fenchelConjugate n h u) := by
    -- This is the reparameterized objective `dualObj (-u)` expressed as `-(f⋆ (-u) + h⋆ u)`.
    have hHstarProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n h) :=
      proper_fenchelConjugate_of_proper (n := n) (f := h) hh
    have hFstarProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
      proper_fenchelConjugate_of_proper (n := n) (f := f) hf
    have hxUnivNeg : u ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hxUniv : (-u) ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hA_ne_bot : fenchelConjugate n h u ≠ (⊥ : EReal) :=
      hHstarProper.2.2 u hxUnivNeg
    have hB_ne_bot : fenchelConjugate n f (-u) ≠ (⊥ : EReal) :=
      hFstarProper.2.2 (-u) hxUniv
    have hneg :
        (-fenchelConjugate n h u) - fenchelConjugate n f (-u) =
          -(fenchelConjugate n h u + fenchelConjugate n f (-u)) := by
      simpa using
        (EReal.neg_add (x := fenchelConjugate n h u)
          (y := fenchelConjugate n f (-u))
          (h1 := Or.inl hA_ne_bot) (h2 := Or.inr hB_ne_bot)).symm
    have hObjNeg :
        fenchelDualObjective (n := n) f g (-u) =
          -(fenchelConjugate n f (-u) + fenchelConjugate n h u) := by
      -- Expand `dualObj (-u) = g⋆(-u) - f⋆(-u)` and use `g⋆(-u) = -h⋆(u)`.
      have : fenchelDualObjective (n := n) f g (-u) =
          -(fenchelConjugate n h u + fenchelConjugate n f (-u)) := by
        simpa [fenchelDualObjective, concaveFenchelConjugate, h] using hneg
      simpa [add_comm, add_left_comm, add_assoc] using this
    simpa [xStar] using hObjNeg
  have hDualAttained :
      fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar := by
    calc
      fenchelDualSupremum (n := n) f g
          = -infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 := hDual_as_negInfConv0
      _ = -(fenchelConjugate n f (-u) + fenchelConjugate n h u) := by
            simpa [hValue]
      _ = fenchelDualObjective (n := n) f g xStar := by
            simpa [hObj_at_xStar]

  refine And.intro hEq ?_
  exact ⟨xStar, hDualAttained⟩

/-- Helper for Theorem 31.1: polyhedral-`g` variant of qualification (a), proved by specializing
Theorem 20.1 with `k = 1` to the ordered pair `(h, f)` where `h = -g`. -/
lemma helperForTheorem_31_1_polyA_polyG_k1_core {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hgPoly : IsBookPolyhedralConcaveFunction n g)
    (hA_polyG : FenchelConditionAWithPolyhedralG (n := n) f g) :
    fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
      ∃ xStar : Fin n → ℝ,
        fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar := by
  classical
  -- Set `h := -g` so the sum `h + f` matches the book primal objective.
  let h : (Fin n → ℝ) → EReal := fun x => -(g x)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [ProperConcaveFunctionOn, h] using hg
  rcases hgPoly with ⟨hPoly, _h_ne_bot⟩
  have hPoly' : IsPolyhedralConvexFunction n h := by
    simpa [h] using hPoly

  -- Use the family `(h, f)` with `k = 1`: index `0` is polyhedral and uses `dom`, index `1` uses `ri(dom)`.
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => if i = 0 then h else f
  have hk : (1 : ℕ) ≤ 2 := by
    decide
  have hmPos : (0 : ℕ) < 2 := by
    decide
  have hpolyTwo :
      ∀ i : Fin 2, i.1 < 1 → IsPolyhedralConvexFunction n (fTwo i) := by
    intro i hi
    fin_cases i
    · simpa [fTwo] using hPoly'
    · have : ¬ (1 < 1) := Nat.lt_irrefl 1
      exact False.elim (this hi)
  have hproperTwo :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hh
    · simpa [fTwo] using hf

  -- Build the nonempty qualification set from `ri(dom f) ∩ dom g ≠ ∅`.
  rcases hA_polyG with ⟨x0, hx0riF, hx0DomG⟩
  have hx0DomH :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [concaveEffectiveDomain, h] using hx0DomG
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  let y0 : EuclideanSpace ℝ (Fin n) := e.symm x0
  have hPreimage_eq_image (C : Set (Fin n → ℝ)) :
      ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' C) = e.symm '' C := by
    ext y
    constructor
    · intro hy
      refine ⟨e y, hy, ?_⟩
      simp [e]
    · rintro ⟨x, hxC, rfl⟩
      simpa [e] using hxC
  have hdomRiTwo :
      Set.Nonempty
        ((⋂ i : {i : Fin 2 // i.1 < 1},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))
          ∩
          (⋂ i : {i : Fin 2 // 1 ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))) := by
    refine ⟨y0, ?_⟩
    refine And.intro ?_ ?_
    · -- Dom-block: only index `0`, i.e. membership in `dom h`.
      refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, hi⟩
      fin_cases i
      · -- `(y0 : Fin n → ℝ) = x0`.
        have hy0 : (y0 : Fin n → ℝ) = x0 := by
          simp [y0, e]
        -- Use the dom witness from the hypothesis.
        simpa [fTwo, hy0] using hx0DomH
      · have : ¬ (1 < 1) := Nat.lt_irrefl 1
        exact False.elim (this hi)
    · -- Ri-block: only index `1`, i.e. relative interior of `dom f`.
      refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, hi⟩
      fin_cases i
      · -- Contradiction: `1 ≤ 0` is impossible.
        exact False.elim ((Nat.not_succ_le_zero 0) hi)
      · have hy0ri :
            y0 ∈ euclideanRelativeInterior n
              (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
          have := (mem_euclideanRelativeInterior_fin_iff
            (n := n)
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
            (x := x0)).1 hx0riF
          simpa [y0, e] using this
        simpa [hPreimage_eq_image, fTwo] using hy0ri

  -- Apply Theorem 20.1, then extract the needed bridge at `0` plus an attained decomposition.
  obtain ⟨hConjEq, hAttained⟩ :=
    fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_dom_first_poly_iInter_ri_rest_and_attained
      (f := fTwo) (k := 1) (hk := hk) (hmPos := hmPos) hpolyTwo hproperTwo hdomRiTwo
  have hConjEq0 :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) 0 =
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 := by
    simpa using congrArg (fun F => F 0) hConjEq
  have hInfConvFamilyEq :
      infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) := by
    have hConjTwo :
        (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
          (fun i : Fin 2 =>
            if i = 0 then fenchelConjugate n h else fenchelConjugate n f) := by
      funext i
      fin_cases i
      · simp [fTwo]
      · simp [fTwo]
    simpa [hConjTwo] using
      (infimalConvolution_eq_infimalConvolutionFamily_two
        (f := fenchelConjugate n h) (g := fenchelConjugate n f)).symm
  have hConjEq0' :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) 0 =
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
    simpa [hInfConvFamilyEq] using hConjEq0
  have hSumRewrite :
      (fun x => ∑ i : Fin 2, fTwo i x) = fun x => h x + f x := by
    funext x
    simp [fTwo, Fin.sum_univ_two]
  have hConjSum0 :
      fenchelConjugate n (fun x => f x + (-(g x))) 0 =
        infimalConvolution (fenchelConjugate n (fun x => -(g x))) (fenchelConjugate n f) 0 := by
    -- Transport `hConjEq0'` through the `∑`-rewrite, then commute `h + f` into `f + h`.
    have hConjSum0_hf :
        fenchelConjugate n (fun x => h x + f x) 0 =
          infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
      simpa [hSumRewrite] using hConjEq0'
    have hSwap : (fun x => f x + h x) = fun x => h x + f x := by
      funext x
      simp [add_comm]
    simpa [h, hSwap] using hConjSum0_hf

  -- Extract an attained decomposition of the binary infimal convolution at `0`.
  have hAtt0 := hAttained (0 : Fin n → ℝ)
  rcases hAtt0 with ⟨xStarFam, hsum0, hval⟩
  have hsum0' : xStarFam 0 + xStarFam 1 = (0 : Fin n → ℝ) := by
    simpa [Fin.sum_univ_two] using hsum0
  have hx0 : xStarFam 0 = -xStarFam 1 :=
    eq_neg_of_add_eq_zero_left hsum0'
  let xStar : Fin n → ℝ := xStarFam 1
  have hInfConv0_value :
      infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 =
        fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar := by
    have hval' :
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 =
          fenchelConjugate n h (xStarFam 0) + fenchelConjugate n f (xStarFam 1) := by
      simpa [fTwo, Fin.sum_univ_two] using hval
    have hInf0 :
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 =
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 := by
      simpa [hInfConvFamilyEq] using rfl
    have : fenchelConjugate n h (xStarFam 0) + fenchelConjugate n f (xStarFam 1) =
        fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar := by
      simp [xStar, hx0]
    exact hInf0.trans (hval'.trans this)

  -- Finish using the shared bookkeeping lemma.
  refine
    helperForTheorem_31_1_finishFromInfConv_hf (n := n) f g hf hg hConjSum0 ?_
  exact ⟨xStar, hInfConv0_value⟩

/-- Helper for Theorem 31.1: polyhedral-`f` variant of qualification (a), proved by specializing
Theorem 20.1 with `k = 1` to the ordered pair `(f, h)` where `h = -g`. -/
lemma helperForTheorem_31_1_polyA_polyF_k1_core {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hfPoly : IsBookPolyhedralConvexFunction n f)
    (hA_polyF : FenchelConditionAWithPolyhedralF (n := n) f g) :
    fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
      ∃ xStar : Fin n → ℝ,
        fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar := by
  classical
  let h : (Fin n → ℝ) → EReal := fun x => -(g x)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [ProperConcaveFunctionOn, h] using hg
  rcases hfPoly with ⟨fPoly, _f_ne_bot⟩

  -- Use the family `(f, h)` with `k = 1`: index `0` is polyhedral and uses `dom`, index `1` uses `ri(dom)`.
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => if i = 0 then f else h
  have hk : (1 : ℕ) ≤ 2 := by
    decide
  have hmPos : (0 : ℕ) < 2 := by
    decide
  have hpolyTwo :
      ∀ i : Fin 2, i.1 < 1 → IsPolyhedralConvexFunction n (fTwo i) := by
    intro i hi
    fin_cases i
    · simpa [fTwo] using fPoly
    · have : ¬ (1 < 1) := Nat.lt_irrefl 1
      exact False.elim (this hi)
  have hproperTwo :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hf
    · simpa [fTwo] using hh

  -- Qualification witness: `x0 ∈ dom f` and `x0 ∈ ri(dom g)`.
  rcases hA_polyF with ⟨x0, hx0DomF, hx0riG⟩
  have hx0riH :
      x0 ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) := by
    simpa [concaveEffectiveDomain, h] using hx0riG
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  let y0 : EuclideanSpace ℝ (Fin n) := e.symm x0
  have hPreimage_eq_image (C : Set (Fin n → ℝ)) :
      ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' C) = e.symm '' C := by
    ext y
    constructor
    · intro hy
      refine ⟨e y, hy, ?_⟩
      simp [e]
    · rintro ⟨x, hxC, rfl⟩
      simpa [e] using hxC
  have hdomRiTwo :
      Set.Nonempty
        ((⋂ i : {i : Fin 2 // i.1 < 1},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))
          ∩
          (⋂ i : {i : Fin 2 // 1 ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))) := by
    refine ⟨y0, ?_⟩
    refine And.intro ?_ ?_
    · -- Dom-block: only index `0`, i.e. membership in `dom f`.
      refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, hi⟩
      fin_cases i
      · have hy0 : (y0 : Fin n → ℝ) = x0 := by
          simp [y0, e]
        simpa [fTwo, hy0] using hx0DomF
      · have : ¬ (1 < 1) := Nat.lt_irrefl 1
        exact False.elim (this hi)
    · -- Ri-block: only index `1`, i.e. relative interior of `dom h`.
      refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, hi⟩
      fin_cases i
      · exact False.elim ((Nat.not_succ_le_zero 0) hi)
      · have hy0ri :
            y0 ∈ euclideanRelativeInterior n
              (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) h) := by
          have := (mem_euclideanRelativeInterior_fin_iff
            (n := n)
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) h)
            (x := x0)).1 hx0riH
          simpa [y0, e] using this
        simpa [hPreimage_eq_image, fTwo] using hy0ri

  -- Apply Theorem 20.1 and extract the bridge at `0` plus attainment.
  obtain ⟨hConjEq, hAttained⟩ :=
    fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_dom_first_poly_iInter_ri_rest_and_attained
      (f := fTwo) (k := 1) (hk := hk) (hmPos := hmPos) hpolyTwo hproperTwo hdomRiTwo
  have hConjEq0 :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) 0 =
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 := by
    simpa using congrArg (fun F => F 0) hConjEq
  have hInfConvFamilyEq :
      infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
        infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) := by
    have hConjTwo :
        (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
          (fun i : Fin 2 =>
            if i = 0 then fenchelConjugate n f else fenchelConjugate n h) := by
      funext i
      fin_cases i
      · simp [fTwo]
      · simp [fTwo]
    simpa [hConjTwo] using
      (infimalConvolution_eq_infimalConvolutionFamily_two
        (f := fenchelConjugate n f) (g := fenchelConjugate n h)).symm
  have hConjEq0' :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) 0 =
        infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 := by
    simpa [hInfConvFamilyEq] using hConjEq0
  have hSumRewrite :
      (fun x => ∑ i : Fin 2, fTwo i x) = fun x => f x + h x := by
    funext x
    simp [fTwo, Fin.sum_univ_two]
  have hConjSum0 :
      fenchelConjugate n (fun x => f x + (-(g x))) 0 =
        infimalConvolution (fenchelConjugate n f) (fenchelConjugate n (fun x => -(g x))) 0 := by
    simpa [h, hSumRewrite] using hConjEq0'

  -- Attainment for the binary infimal convolution at `0`.
  have hAtt0 := hAttained (0 : Fin n → ℝ)
  rcases hAtt0 with ⟨xStarFam, hsum0, hval⟩
  have hsum0' : xStarFam 0 + xStarFam 1 = (0 : Fin n → ℝ) := by
    simpa [Fin.sum_univ_two] using hsum0
  have hx0 : xStarFam 0 = -xStarFam 1 :=
    eq_neg_of_add_eq_zero_left hsum0'
  let u : Fin n → ℝ := xStarFam 1
  have hInfConv0_value :
      infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 =
        fenchelConjugate n f (-u) + fenchelConjugate n h u := by
    have hval' :
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 =
          fenchelConjugate n f (xStarFam 0) + fenchelConjugate n h (xStarFam 1) := by
      simpa [fTwo, Fin.sum_univ_two] using hval
    have hInf0 :
        infimalConvolution (fenchelConjugate n f) (fenchelConjugate n h) 0 =
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 := by
      simpa [hInfConvFamilyEq] using rfl
    have : fenchelConjugate n f (xStarFam 0) + fenchelConjugate n h (xStarFam 1) =
        fenchelConjugate n f (-u) + fenchelConjugate n h u := by
      simp [u, hx0]
    exact hInf0.trans (hval'.trans this)

  refine
    helperForTheorem_31_1_finishFromInfConv_fh (n := n) f g hf hg hConjSum0 ?_
  exact ⟨u, hInfConv0_value⟩

/-- Helper for Theorem 31.1: polyhedral-pair variant of qualification (a), proved by specializing
Theorem 20.1 with `k = 2` to the ordered pair `(h, f)` where `h = -g` (so no relative-interior
hypothesis is needed). -/
lemma helperForTheorem_31_1_polyA_pair_k2_core {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hfPoly : IsBookPolyhedralConvexFunction n f)
    (hgPoly : IsBookPolyhedralConcaveFunction n g)
    (hA_pair : FenchelConditionAForPolyhedralPair (n := n) f g) :
    fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
      ∃ xStar : Fin n → ℝ,
        fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar := by
  classical
  let h : (Fin n → ℝ) → EReal := fun x => -(g x)
  have hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [ProperConcaveFunctionOn, h] using hg
  rcases hfPoly with ⟨fPoly, _f_ne_bot⟩
  rcases hgPoly with ⟨hPoly, _h_ne_bot⟩
  have hPoly' : IsPolyhedralConvexFunction n h := by
    simpa [h] using hPoly

  -- Use the family `(h, f)` with `k = 2`, i.e. both indices are in the dom-block.
  let fTwo : Fin 2 → (Fin n → ℝ) → EReal := fun i => if i = 0 then h else f
  have hk : (2 : ℕ) ≤ 2 := by
    decide
  have hmPos : (0 : ℕ) < 2 := by
    decide
  have hpolyTwo :
      ∀ i : Fin 2, i.1 < 2 → IsPolyhedralConvexFunction n (fTwo i) := by
    intro i _hi
    fin_cases i
    · simpa [fTwo] using hPoly'
    · simpa [fTwo] using fPoly
  have hproperTwo :
      ∀ i : Fin 2, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fTwo i) := by
    intro i
    fin_cases i
    · simpa [fTwo] using hh
    · simpa [fTwo] using hf

  -- Qualification witness: `x0 ∈ dom f` and `x0 ∈ dom g` gives nonemptiness of the dom-block.
  rcases hA_pair with ⟨x0, hx0DomF, hx0DomG⟩
  have hx0DomH :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
    simpa [concaveEffectiveDomain, h] using hx0DomG
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  let y0 : EuclideanSpace ℝ (Fin n) := e.symm x0
  have hdomRiTwo :
      Set.Nonempty
        ((⋂ i : {i : Fin 2 // i.1 < 2},
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))
          ∩
          (⋂ i : {i : Fin 2 // 2 ≤ i.1},
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fTwo i)))) := by
    refine ⟨y0, ?_⟩
    refine And.intro ?_ ?_
    · -- Dom-block: both indices, use the two dom witnesses.
      refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, _hi⟩
      fin_cases i
      · have hy0 : (y0 : Fin n → ℝ) = x0 := by
          simp [y0, e]
        simpa [fTwo, hy0] using hx0DomH
      · have hy0 : (y0 : Fin n → ℝ) = x0 := by
          simp [y0, e]
        simpa [fTwo, hy0] using hx0DomF
    · -- Ri-block is empty for `k = 2`; membership is trivial by contradiction.
      refine Set.mem_iInter.2 ?_
      intro i
      rcases i with ⟨i, hi⟩
      have : ¬ (2 ≤ i.1) :=
        Nat.not_le_of_gt i.2
      exact False.elim (this hi)

  obtain ⟨hConjEq, hAttained⟩ :=
    fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_dom_first_poly_iInter_ri_rest_and_attained
      (f := fTwo) (k := 2) (hk := hk) (hmPos := hmPos) hpolyTwo hproperTwo hdomRiTwo
  have hConjEq0 :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) 0 =
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 := by
    simpa using congrArg (fun F => F 0) hConjEq
  have hInfConvFamilyEq :
      infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) := by
    have hConjTwo :
        (fun i : Fin 2 => fenchelConjugate n (fTwo i)) =
          (fun i : Fin 2 =>
            if i = 0 then fenchelConjugate n h else fenchelConjugate n f) := by
      funext i
      fin_cases i
      · simp [fTwo]
      · simp [fTwo]
    simpa [hConjTwo] using
      (infimalConvolution_eq_infimalConvolutionFamily_two
        (f := fenchelConjugate n h) (g := fenchelConjugate n f)).symm
  have hConjEq0' :
      fenchelConjugate n (fun x => ∑ i : Fin 2, fTwo i x) 0 =
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
    simpa [hInfConvFamilyEq] using hConjEq0
  have hSumRewrite :
      (fun x => ∑ i : Fin 2, fTwo i x) = fun x => h x + f x := by
    funext x
    simp [fTwo, Fin.sum_univ_two]
  have hConjSum0 :
      fenchelConjugate n (fun x => f x + (-(g x))) 0 =
        infimalConvolution (fenchelConjugate n (fun x => -(g x))) (fenchelConjugate n f) 0 := by
    have hConjSum0_hf :
        fenchelConjugate n (fun x => h x + f x) 0 =
          infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 := by
      simpa [hSumRewrite] using hConjEq0'
    have hSwap : (fun x => f x + h x) = fun x => h x + f x := by
      funext x
      simp [add_comm]
    simpa [h, hSwap] using hConjSum0_hf

  have hAtt0 := hAttained (0 : Fin n → ℝ)
  rcases hAtt0 with ⟨xStarFam, hsum0, hval⟩
  have hsum0' : xStarFam 0 + xStarFam 1 = (0 : Fin n → ℝ) := by
    simpa [Fin.sum_univ_two] using hsum0
  have hx0 : xStarFam 0 = -xStarFam 1 :=
    eq_neg_of_add_eq_zero_left hsum0'
  let xStar : Fin n → ℝ := xStarFam 1
  have hInfConv0_value :
      infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 =
        fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar := by
    have hval' :
        infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 =
          fenchelConjugate n h (xStarFam 0) + fenchelConjugate n f (xStarFam 1) := by
      simpa [fTwo, Fin.sum_univ_two] using hval
    have hInf0 :
        infimalConvolution (fenchelConjugate n h) (fenchelConjugate n f) 0 =
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (fTwo i)) 0 := by
      simpa [hInfConvFamilyEq] using rfl
    have : fenchelConjugate n h (xStarFam 0) + fenchelConjugate n f (xStarFam 1) =
        fenchelConjugate n h (-xStar) + fenchelConjugate n f xStar := by
      simp [xStar, hx0]
    exact hInf0.trans (hval'.trans this)

  refine
    helperForTheorem_31_1_finishFromInfConv_hf (n := n) f g hf hg hConjSum0 ?_
  exact ⟨xStar, hInfConv0_value⟩

/-- Helper for Theorem 31.1: the polyhedral variants of qualification (a) still imply strong
duality and dual attainment, by specializing Theorem 20.1 with `k = 1` or `k = 2`. -/
lemma helperForTheorem_31_1_conditionA_polyhedralVariants_concaveDuality_core {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    (IsBookPolyhedralConcaveFunction n g ∧ FenchelConditionAWithPolyhedralG (n := n) f g →
        fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
          ∃ xStar : Fin n → ℝ,
            fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar) ∧
    (IsBookPolyhedralConvexFunction n f ∧ FenchelConditionAWithPolyhedralF (n := n) f g →
        fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
          ∃ xStar : Fin n → ℝ,
            fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar) ∧
    (IsBookPolyhedralConvexFunction n f ∧ IsBookPolyhedralConcaveFunction n g ∧
        FenchelConditionAForPolyhedralPair (n := n) f g →
        fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
          ∃ xStar : Fin n → ℝ,
            fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar) := by
  -- Each branch is proved by a dedicated specialization of Theorem 20.1, isolating the `k = 1`
  -- / `k = 2` bookkeeping from the main theorem proof.
  refine And.intro ?_ (And.intro ?_ ?_)
  · rintro ⟨hgPoly, hA_polyG⟩
    exact
      helperForTheorem_31_1_polyA_polyG_k1_core (n := n) f g hf hg hgPoly hA_polyG
  · rintro ⟨hfPoly, hA_polyF⟩
    exact
      helperForTheorem_31_1_polyA_polyF_k1_core (n := n) f g hf hg hfPoly hA_polyF
  · rintro ⟨hfPoly, hgPoly, hA_pair⟩
    exact
      helperForTheorem_31_1_polyA_pair_k2_core (n := n) f g hf hg hfPoly hgPoly hA_pair


end Section31
end Chap06

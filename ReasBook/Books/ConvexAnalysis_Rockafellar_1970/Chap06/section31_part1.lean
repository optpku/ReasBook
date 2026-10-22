/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section12_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part18

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

--  This file is generated as the section 31 scaffold. The detailed statements in
--  `data/Books.ConvexAnalysis_Rockafellar_1970/section31.json` are not yet reconstructed into
--  fully formal Lean theorems in this workspace.

-- Proof sketch: apply Fenchel's inequality twice, once to `f` and once to `g`, to get
-- `g⋆ xStar - f⋆ xStar ≤ f x - g x` for every primal-dual pair `(x, xStar)`. Then take the
-- supremum over `xStar` on the left and the infimum over `x` on the right.
/-- Helper for Lemma 31.0.1: the constant-zero function `f ≡ 0` used in the one-dimensional
counterexample. -/
noncomputable def helperForLemma_31_0_1_counterexampleF : (Fin 1 → ℝ) → EReal :=
  fun _ => 0

/-- Helper for Lemma 31.0.1: the step function `g(0) = 0`, `g(x) = 1` for `x ≠ 0` used in the
one-dimensional counterexample. -/
noncomputable def helperForLemma_31_0_1_counterexampleG : (Fin 1 → ℝ) → EReal :=
  fun x => if x 0 = 0 then 0 else 1

/-- Helper for Lemma 31.0.1: the counterexample function `f ≡ 0` is proper. -/
lemma helperForLemma_31_0_1_counterexampleF_proper :
    ProperERealFunction helperForLemma_31_0_1_counterexampleF := by
  constructor
  · intro x
    -- The constant-zero function never takes the value `⊥`.
    simp [helperForLemma_31_0_1_counterexampleF]
  · -- The same point also witnesses that `f` is finite somewhere.
    refine ⟨0, ?_⟩
    simp [helperForLemma_31_0_1_counterexampleF]

/-- Helper for Lemma 31.0.1: the step-function counterexample `g` is proper. -/
lemma helperForLemma_31_0_1_counterexampleG_proper :
    ProperERealFunction helperForLemma_31_0_1_counterexampleG := by
  constructor
  · intro x
    -- Each value of `g` is either `0` or `1`, so `g` never hits `⊥`.
    by_cases hx : x 0 = 0
    · simp [helperForLemma_31_0_1_counterexampleG, hx]
    · simp [helperForLemma_31_0_1_counterexampleG, hx]
      simpa using (EReal.coe_ne_bot (1 : ℝ))
  · -- Evaluating at the origin shows that `g` is finite somewhere.
    refine ⟨0, ?_⟩
    simp [helperForLemma_31_0_1_counterexampleG]

/-- Helper for Lemma 31.0.1: for the counterexample pair, the primal infimum is at most `-1`. -/
lemma helperForLemma_31_0_1_counterexamplePrimal_le_neg_one :
    functionInfimumEReal
        (fun x =>
          helperForLemma_31_0_1_counterexampleF x -
            helperForLemma_31_0_1_counterexampleG x) ≤
      (-1 : EReal) := by
  -- Evaluating the infimum at the point `x = 1` already gives the value `-1`.
  have h :=
    iInf_le
      (fun x : Fin 1 → ℝ =>
        helperForLemma_31_0_1_counterexampleF x -
          helperForLemma_31_0_1_counterexampleG x)
      (fun _ => (1 : ℝ))
  simpa [functionInfimumEReal, helperForLemma_31_0_1_counterexampleF,
    helperForLemma_31_0_1_counterexampleG] using h

/-- Helper for Lemma 31.0.1: every primal objective value of the counterexample pair is bounded
below by `-1`. -/
lemma helperForLemma_31_0_1_counterexamplePrimal_pointwise_ge_neg_one
    (x : Fin 1 → ℝ) :
    (-1 : EReal) ≤
      helperForLemma_31_0_1_counterexampleF x -
        helperForLemma_31_0_1_counterexampleG x := by
  -- The counterexample objective is `0` at the origin and `-1` elsewhere.
  by_cases hx : x 0 = 0
  · simp [helperForLemma_31_0_1_counterexampleF, helperForLemma_31_0_1_counterexampleG, hx]
  · simp [helperForLemma_31_0_1_counterexampleF, helperForLemma_31_0_1_counterexampleG, hx]

/-- Helper for Lemma 31.0.1: for the counterexample pair, the primal infimum is exactly `-1`. -/
lemma helperForLemma_31_0_1_counterexamplePrimal_eq_neg_one :
    functionInfimumEReal
        (fun x =>
          helperForLemma_31_0_1_counterexampleF x -
            helperForLemma_31_0_1_counterexampleG x) =
      (-1 : EReal) := by
  apply le_antisymm
  · -- The point `x = 1` already realizes the value `-1`.
    exact helperForLemma_31_0_1_counterexamplePrimal_le_neg_one
  · -- No value of the primal objective can fall below `-1`.
    refine le_iInf ?_
    intro x
    exact helperForLemma_31_0_1_counterexamplePrimal_pointwise_ge_neg_one x

/-- Helper for Lemma 31.0.1: the conjugate of the constant-zero counterexample at `x⋆ = 0`
vanishes. -/
lemma helperForLemma_31_0_1_counterexampleF_conjugate_zero :
    fenchelConjugate 1 helperForLemma_31_0_1_counterexampleF 0 = 0 := by
  -- At `x⋆ = 0`, every affine term is identically zero.
  unfold fenchelConjugate helperForLemma_31_0_1_counterexampleF
  simp

/-- Helper for Lemma 31.0.1: the conjugate of the step-function counterexample at `x⋆ = 0`
also vanishes. -/
lemma helperForLemma_31_0_1_counterexampleG_conjugate_zero :
    fenchelConjugate 1 helperForLemma_31_0_1_counterexampleG 0 = 0 := by
  apply le_antisymm
  · -- Every term in the defining supremum is either `0` or `-1`.
    unfold fenchelConjugate helperForLemma_31_0_1_counterexampleG
    refine sSup_le_iff.2 ?_
    rintro y ⟨x, rfl⟩
    by_cases hx : x 0 = 0
    · simp [hx]
    · simp [hx]
  · -- The origin contributes the value `0`, so the supremum is at least `0`.
    unfold fenchelConjugate helperForLemma_31_0_1_counterexampleG
    refine le_sSup ?_
    refine ⟨0, ?_⟩
    simp

/-- Helper for Lemma 31.0.1: the dual supremum for the counterexample pair is at least `0`. -/
lemma helperForLemma_31_0_1_counterexampleDual_ge_zero :
    (0 : EReal) ≤
      ⨆ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_1_counterexampleG xStar -
          fenchelConjugate 1 helperForLemma_31_0_1_counterexampleF xStar := by
  -- Evaluating the dual objective at `x⋆ = 0` already gives the lower bound `0`.
  have h0 :
      (0 : EReal) ≤
        fenchelConjugate 1 helperForLemma_31_0_1_counterexampleG 0 -
          fenchelConjugate 1 helperForLemma_31_0_1_counterexampleF 0 := by
    simp [helperForLemma_31_0_1_counterexampleG_conjugate_zero,
      helperForLemma_31_0_1_counterexampleF_conjugate_zero]
  exact le_trans h0
    (le_iSup
      (fun xStar : Fin 1 → ℝ =>
        fenchelConjugate 1 helperForLemma_31_0_1_counterexampleG xStar -
          fenchelConjugate 1 helperForLemma_31_0_1_counterexampleF xStar)
      0)

/-- Helper for Lemma 31.0.1: the counterexample primal value is strictly smaller than the
advertised dual bound. -/
lemma helperForLemma_31_0_1_counterexamplePrimal_lt_dualSupremum :
    functionInfimumEReal
        (fun x =>
          helperForLemma_31_0_1_counterexampleF x -
            helperForLemma_31_0_1_counterexampleG x) <
      ⨆ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_1_counterexampleG xStar -
          fenchelConjugate 1 helperForLemma_31_0_1_counterexampleF xStar := by
  -- Identify the primal infimum explicitly, then compare it with the dual lower bound `0`.
  calc
    functionInfimumEReal
        (fun x =>
          helperForLemma_31_0_1_counterexampleF x -
            helperForLemma_31_0_1_counterexampleG x)
        = (-1 : EReal) := helperForLemma_31_0_1_counterexamplePrimal_eq_neg_one
    _ < (0 : EReal) := by
      norm_num
    _ ≤
        ⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_1_counterexampleG xStar -
            fenchelConjugate 1 helperForLemma_31_0_1_counterexampleF xStar :=
      helperForLemma_31_0_1_counterexampleDual_ge_zero

/-- Helper for Lemma 31.0.1: the one-dimensional counterexample contradicts the advertised
lower bound under mere properness assumptions. -/
lemma helperForLemma_31_0_1_counterexampleRefutesClaim :
    ¬
      (functionInfimumEReal
          (fun x =>
            helperForLemma_31_0_1_counterexampleF x -
              helperForLemma_31_0_1_counterexampleG x) ≥
        ⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_1_counterexampleG xStar -
            fenchelConjugate 1 helperForLemma_31_0_1_counterexampleF xStar) := by
  intro hLowerBound
  -- The strengthened strict counterexample leaves no room for the advertised non-strict bound.
  exact
    (not_le_of_gt helperForLemma_31_0_1_counterexamplePrimal_lt_dualSupremum) hLowerBound

/-- Helper for Lemma 31.0.1: there exist proper one-dimensional functions for which the claimed
Fenchel lower bound fails. -/
lemma helperForLemma_31_0_1_existsProperCounterexample :
    ∃ f g : (Fin 1 → ℝ) → EReal,
      ProperERealFunction f ∧
      ProperERealFunction g ∧
      ¬
        (functionInfimumEReal (fun x => f x - g x) ≥
          ⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 g xStar - fenchelConjugate 1 f xStar) := by
  -- Package the explicit counterexample so later repair work can cite a single existential fact.
  refine ⟨helperForLemma_31_0_1_counterexampleF, helperForLemma_31_0_1_counterexampleG,
    helperForLemma_31_0_1_counterexampleF_proper, helperForLemma_31_0_1_counterexampleG_proper,
    ?_⟩
  -- The previously proved refutation applies verbatim to these witnesses.
  simpa using helperForLemma_31_0_1_counterexampleRefutesClaim

/-- Helper for Lemma 31.0.1: the current theorem header is already false in dimension `1`, so no
proof can exist under mere properness assumptions. -/
lemma helperForLemma_31_0_1_currentHeaderFalseInDimensionOne :
    ¬
      (∀ f g : (Fin 1 → ℝ) → EReal, ProperERealFunction f → ProperERealFunction g →
        functionInfimumEReal (fun x => f x - g x) ≥
          ⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 g xStar - fenchelConjugate 1 f xStar) := by
  intro hUniversal
  -- Apply the universal claim to the explicit counterexample witnesses.
  have hCounterexampleIneq :
      functionInfimumEReal
          (fun x =>
            helperForLemma_31_0_1_counterexampleF x -
              helperForLemma_31_0_1_counterexampleG x) ≥
        ⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_1_counterexampleG xStar -
            fenchelConjugate 1 helperForLemma_31_0_1_counterexampleF xStar :=
    hUniversal
      helperForLemma_31_0_1_counterexampleF
      helperForLemma_31_0_1_counterexampleG
      helperForLemma_31_0_1_counterexampleF_proper
      helperForLemma_31_0_1_counterexampleG_proper
  -- The previously formalized refutation rules out exactly this specialized inequality.
  exact helperForLemma_31_0_1_counterexampleRefutesClaim hCounterexampleIneq

/-- Helper for Lemma 31.0.1: the full polymorphic theorem header has no witness under mere
properness assumptions, because its dimension-`1` specialization is already false. -/
lemma helperForLemma_31_0_1_polymorphicHeaderFalseUnderMereProperness :
    ¬
      (∀ {n : ℕ} (f g : (Fin n → ℝ) → EReal), ProperERealFunction f → ProperERealFunction g →
        functionInfimumEReal (fun x => f x - g x) ≥
          ⨆ xStar : Fin n → ℝ, fenchelConjugate n g xStar - fenchelConjugate n f xStar) := by
  intro hUniversal
  -- Specialize the polymorphic claim to the already formalized one-dimensional counterexample.
  have hCounterexampleIneq :
      functionInfimumEReal
          (fun x =>
            helperForLemma_31_0_1_counterexampleF x -
              helperForLemma_31_0_1_counterexampleG x) ≥
        ⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_1_counterexampleG xStar -
            fenchelConjugate 1 helperForLemma_31_0_1_counterexampleF xStar :=
    hUniversal (n := 1)
      helperForLemma_31_0_1_counterexampleF
      helperForLemma_31_0_1_counterexampleG
      helperForLemma_31_0_1_counterexampleF_proper
      helperForLemma_31_0_1_counterexampleG_proper
  -- The strict primal-dual gap for these witnesses contradicts that specialized inequality.
  exact helperForLemma_31_0_1_counterexampleRefutesClaim hCounterexampleIneq

/-- Helper for Lemma 31.0.1: membership in the common effective domain forces `f x` and `g x`
to be finite on the appropriate sides needed for the `EReal` rearrangements. -/
lemma helperForLemma_31_0_1_finiteValuesOnCommonEffectiveDomain {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun z => -(g z)))
    {x : Fin n → ℝ}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun z => -(g z))) :
    f x ≠ (⊤ : EReal) ∧ g x ≠ (⊤ : EReal) ∧ g x ≠ (⊥ : EReal) := by
  have _hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  -- Extract the `⊤`-exclusion for `f` from the effective-domain hypothesis.
  have hfx_ne_top : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hx.1
  -- Properness of `-g` rules out `-g x = ⊥`, hence `g x ≠ ⊤`.
  have hgx_ne_top : g x ≠ (⊤ : EReal) := by
    have hneg_ne_bot : -(g x) ≠ (⊥ : EReal) := hg.2.2 x (by simp)
    simpa using hneg_ne_bot
  -- Membership in the effective domain of `-g` rules out `-g x = ⊤`, hence `g x ≠ ⊥`.
  have hgx_ne_bot : g x ≠ (⊥ : EReal) := by
    have hneg_ne_top : -(g x) ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top
        (S := (Set.univ : Set (Fin n → ℝ))) (f := fun z => -(g z)) hx.2
    simpa using hneg_ne_top
  exact ⟨hfx_ne_top, hgx_ne_top, hgx_ne_bot⟩

/-- Helper for Lemma 31.0.1: applying Fenchel's inequality to `-g` at `-xStar` yields the
textbook rearrangement `g x - (-g)⋆(-xStar) ≤ ⟪x, xStar⟫`. -/
lemma helperForLemma_31_0_1_negFenchel_rearrangedToDualBound {n : ℕ}
    {g : (Fin n → ℝ) → EReal}
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun z => -(g z)))
    {x xStar : Fin n → ℝ}
    (hgx_ne_top : g x ≠ (⊤ : EReal))
    (hgx_ne_bot : g x ≠ (⊥ : EReal)) :
    g x - fenchelConjugate n (fun z => -(g z)) (-xStar) ≤
      (((dotProduct x xStar : ℝ) : EReal)) := by
  -- Apply Fenchel's inequality to the convex function `-g` with dual vector `-xStar`.
  have hFenchelNeg :
      (((dotProduct x (-xStar) : ℝ) : EReal)) ≤
        -(g x) + fenchelConjugate n (fun z => -(g z)) (-xStar) :=
    fenchel_inequality n (fun z => -(g z)) hg x (-xStar)
  -- Translate finiteness of `g x` into the side conditions needed for `EReal` subtraction.
  have hnegG_ne_bot : -(g x) ≠ (⊥ : EReal) := by
    simpa using hgx_ne_top
  have hnegG_ne_top : -(g x) ≠ (⊤ : EReal) := by
    simpa using hgx_ne_bot
  -- Rewrite the Fenchel inequality so the dot product appears on the right.
  have hMinusDot_le_negG_sub_negConj :
      -((((dotProduct x xStar : ℝ) : EReal))) ≤
        -(g x) - (-(fenchelConjugate n (fun z => -(g z)) (-xStar))) := by
    simpa [sub_eq_add_neg, dotProduct_neg, neg_dotProduct, add_assoc, add_left_comm, add_comm]
      using hFenchelNeg
  have hMinusDot_add_negConj_le_negG :
      -((((dotProduct x xStar : ℝ) : EReal))) +
          (-(fenchelConjugate n (fun z => -(g z)) (-xStar))) ≤
        -(g x) :=
    (EReal.le_sub_iff_add_le (Or.inr hnegG_ne_bot) (Or.inr hnegG_ne_top)).1
      hMinusDot_le_negG_sub_negConj
  -- Negating the inequality recovers the desired upper bound for `g x`.
  have hg_le_dot_add_conj :
      g x ≤
        (((dotProduct x xStar : ℝ) : EReal)) +
          fenchelConjugate n (fun z => -(g z)) (-xStar) := by
    have hnegated :
        -(-(g x)) ≤
          -( -((((dotProduct x xStar : ℝ) : EReal))) +
            (-(fenchelConjugate n (fun z => -(g z)) (-xStar)))) :=
      EReal.neg_le_neg_iff.2 hMinusDot_add_negConj_le_negG
    have hrewrite :
        -( -((((dotProduct x xStar : ℝ) : EReal))) +
            (-(fenchelConjugate n (fun z => -(g z)) (-xStar)))) =
          (((dotProduct x xStar : ℝ) : EReal)) +
            fenchelConjugate n (fun z => -(g z)) (-xStar) := by
      calc
        -( -((((dotProduct x xStar : ℝ) : EReal))) +
            (-(fenchelConjugate n (fun z => -(g z)) (-xStar)))) =
            -(-((((dotProduct x xStar : ℝ) : EReal)))) -
              (-(fenchelConjugate n (fun z => -(g z)) (-xStar))) := by
                exact EReal.neg_add (Or.inl (by simp)) (Or.inl (by simp))
        _ = (((dotProduct x xStar : ℝ) : EReal)) +
              fenchelConjugate n (fun z => -(g z)) (-xStar) := by
                simp [sub_eq_add_neg]
    simpa [hrewrite] using hnegated
  exact
    (EReal.sub_le_iff_le_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _))).2
      hg_le_dot_add_conj

/-- Helper for Lemma 31.0.1: Fenchel's inequality for `f` and `-g` gives the pointwise dual
lower bound on the common effective domain. -/
lemma helperForLemma_31_0_1_dualTerm_le_primalDifference_onCommonEffectiveDomain {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun z => -(g z)))
    {x xStar : Fin n → ℝ}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun z => -(g z))) :
    (-(fenchelConjugate n (fun z => -(g z)) (-xStar))) - fenchelConjugate n f xStar ≤
      f x - g x := by
  -- First collect the finiteness information needed for the `EReal` subtraction identities.
  rcases helperForLemma_31_0_1_finiteValuesOnCommonEffectiveDomain hf hg hx with
    ⟨hfx_ne_top, hgx_ne_top, hgx_ne_bot⟩
  have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  have hfStar_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hfStar_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) := hfStar_proper.2.2 xStar (by simp)
  -- Fenchel's inequality for `f` is the first half of the textbook estimate.
  have hFenchelF :
      (((dotProduct x xStar : ℝ) : EReal)) ≤ f x + fenchelConjugate n f xStar :=
    fenchel_inequality n f hf x xStar
  have hDotSub_le_fx :
      (((dotProduct x xStar : ℝ) : EReal)) - fenchelConjugate n f xStar ≤ f x := by
    exact
      (EReal.sub_le_iff_le_add (Or.inl hfStar_ne_bot) (Or.inr hfx_ne_bot)).2 hFenchelF
  -- A dedicated helper packages the `-g` Fenchel step into the textbook pointwise estimate.
  have hgSub_le_dot :
      g x - fenchelConjugate n (fun z => -(g z)) (-xStar) ≤
        (((dotProduct x xStar : ℝ) : EReal)) :=
    helperForLemma_31_0_1_negFenchel_rearrangedToDualBound
      (hg := hg) (x := x) (xStar := xStar) hgx_ne_top hgx_ne_bot
  -- Subtract `f^*(xStar)` and then move `g x` to the right to reach the desired form.
  have hSubtractConjugate :
      (g x - fenchelConjugate n (fun z => -(g z)) (-xStar)) - fenchelConjugate n f xStar ≤
        (((dotProduct x xStar : ℝ) : EReal)) - fenchelConjugate n f xStar :=
    by
      have hadd :=
        add_le_add_right hgSub_le_dot (-(fenchelConjugate n f xStar))
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
  have hAdd_le_fx :
      (g x - fenchelConjugate n (fun z => -(g z)) (-xStar)) - fenchelConjugate n f xStar ≤
        f x :=
    le_trans hSubtractConjugate hDotSub_le_fx
  exact
    (EReal.le_sub_iff_add_le (Or.inl hgx_ne_bot) (Or.inl hgx_ne_top)).2
      (by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hAdd_le_fx)

/-- Helper for Lemma 31.0.1: the pointwise dual lower bound extends to the guarded primal
objective by taking the out-of-domain branch to be `⊤`. -/
lemma helperForLemma_31_0_1_dualTerm_le_guardedPrimalObjective {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun z => -(g z)))
    (x xStar : Fin n → ℝ) :
    (-(fenchelConjugate n (fun z => -(g z)) (-xStar))) - fenchelConjugate n f xStar ≤
      if x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun z => -(g z)) then
        f x - g x
      else
        (⊤ : EReal) := by
  -- Split on the guard exactly as in the textbook passage from a pointwise inequality to an
  -- unrestricted infimum with `⊤` outside the common effective domain.
  by_cases hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun z => -(g z))
  · simpa [hx] using
      helperForLemma_31_0_1_dualTerm_le_primalDifference_onCommonEffectiveDomain
        (hf := hf) (hg := hg) (x := x) (xStar := xStar) hx
  · simp [hx]

/-- Lemma 31.0.1 (Lower Bound from Fenchel's Inequality): if `f : ℝ^n → ℝ ∪ {+∞}` is proper
convex and `g : ℝ^n → ℝ ∪ {-∞}` is proper concave, then the primal infimum of `f - g`
dominates the dual supremum of `g⋆ - f⋆`. In this early-file formulation, `g⋆` is written
directly as the concave conjugate `xStar ↦ -( (-g)⋆(-xStar) )`, and the primal infimum is taken
over the common effective domain of `f` and `g`. -/
lemma fenchel_duality_lower_bound_from_fenchel_inequality {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => -(g x))) :
    functionInfimumEReal
        (fun x =>
          if x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => -(g x)) then
            f x - g x
          else
            (⊤ : EReal)) ≥
      ⨆ xStar : Fin n → ℝ,
        (-(fenchelConjugate n (fun x => -(g x)) (-xStar))) - fenchelConjugate n f xStar := by
  -- Route correction: the earlier properness-only header was false; the repaired statement is
  -- proved by the textbook two-step Fenchel-inequality argument for `(f, -g)`.
  -- Rewrite the target as a comparison between a supremum and an infimum.
  rw [ge_iff_le, functionInfimumEReal]
  -- It suffices to dominate each guarded primal value by every dual objective value.
  refine le_iInf ?_
  intro x
  refine iSup_le ?_
  intro xStar
  -- The guarded helper is exactly the pointwise estimate needed for the `iSup`/`iInf` finish.
  exact helperForLemma_31_0_1_dualTerm_le_guardedPrimalObjective
    (hf := hf) (hg := hg) x xStar

-- Proof sketch: apply the convex-set separation theorem to the epigraphs encoding `f` and `g`,
-- using the nonempty intersection of the relative interiors of their effective domains to obtain
-- a separating vector `x*`; then identify the separator inequality with
-- `g* x* - f* x* ≥ α`.
/-- Helper for Lemma 31.0.2: the infimum identity `inf_x (f x - g x) = α` yields the textbook
pointwise lower bound `α ≤ f x - g x` at every primal point. -/
lemma helperForLemma_31_0_2_pointwiseLowerBoundFromInfimum {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) (α : ℝ)
    (hα : functionInfimumEReal (fun x => f x - g x) = (α : EReal))
    (x : Fin n → ℝ) :
    (α : EReal) ≤ f x - g x := by
  -- Rewrite the infimum as the pointwise `iInf`; then `iInf_le` gives the desired bound.
  rw [← hα]
  simpa [functionInfimumEReal] using iInf_le (fun y : Fin n → ℝ => f y - g y) x

/-- Helper for Lemma 31.0.2: the difference of the two effective domains is convex, so it is a
valid carrier for the separator's horizontal projection. -/
lemma helperForLemma_31_0_2_convexDomainDifference {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    Convex ℝ
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f -
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
  let domF : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  have hdomF_conv : Convex ℝ domF :=
    effectiveDomain_convex (S := Set.univ) (f := f) hf.1
  have hdomG_conv : Convex ℝ domG :=
    effectiveDomain_convex (S := Set.univ) (f := g) hg.1
  -- Minkowski subtraction preserves convexity because it is addition with the negated set.
  simpa [domF, domG, set_sub_eq_add_neg] using hdomF_conv.add hdomG_conv.neg

/-- Helper for Lemma 31.0.2: a common relative-interior point of `dom f` and `dom g` gives the
origin in the relative interior of the Minkowski difference `dom f - dom g`. -/
lemma helperForLemma_31_0_2_zero_mem_relativeInterior_domainDifference {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
          euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))) :
    (0 : Fin n → ℝ) ∈
      euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f -
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) := by
  let domF : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  have hdomF_conv : Convex ℝ domF :=
    effectiveDomain_convex (S := Set.univ) (f := f) hf.1
  have hdomG_conv : Convex ℝ domG :=
    effectiveDomain_convex (S := Set.univ) (f := g) hg.1
  rcases hri with ⟨x, hxF_ri, hxG_ri⟩
  -- Move the two relative-interior hypotheses to intrinsic interior so the Chapter 11
  -- subtraction lemma applies directly.
  have hxF_intr : x ∈ intrinsicInterior ℝ domF := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] at hxF_ri
    exact hxF_ri
  have hxG_intr : x ∈ intrinsicInterior ℝ domG := by
    rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior] at hxG_ri
    exact hxG_ri
  have hzero_intr :
      (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ domF - intrinsicInterior ℝ domG := by
    -- The same relative-interior point witnesses `0 = x - x` in the difference.
    change (0 : Fin n → ℝ) ∈
      Set.image2 (fun a b : Fin n → ℝ => a - b) (intrinsicInterior ℝ domF)
        (intrinsicInterior ℝ domG)
    exact ⟨x, hxF_intr, x, hxG_intr, sub_self x⟩
  have hsub_intr :
      intrinsicInterior ℝ (domF - domG) =
        intrinsicInterior ℝ domF - intrinsicInterior ℝ domG :=
    intrinsicInterior_sub_eq (n := n) (C₁ := domF) (C₂ := domG) hdomF_conv hdomG_conv
  have hzero_intr_diff :
      (0 : Fin n → ℝ) ∈ intrinsicInterior ℝ (domF - domG) := by
    rw [hsub_intr]
    exact hzero_intr
  -- Translate back to the `euclideanRelativeInterior_fin` presentation used in this file.
  rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior]
  exact hzero_intr_diff

/-- Helper for Lemma 31.0.2: the shifted hypograph of `g + α`, after flipping the vertical
coordinate, is closed up to its convex-cone hull in `ℝ^n × ℝ`. This is the corrected lower
cone that should be separated from the homogenized epigraph cone of `f`. -/
noncomputable def helperForLemma_31_0_2_shiftedHypographCone {n : ℕ}
    (α : ℝ) (g : (Fin n → ℝ) → EReal) :
    Set ((Fin n → ℝ) × ℝ) :=
  (ConvexCone.hull ℝ
    {p : (Fin n → ℝ) × ℝ | ((-p.2 : ℝ) : EReal) ≤ (α : EReal) + g p.1} :
      Set ((Fin n → ℝ) × ℝ))

/-- Helper for Lemma 31.0.2: every point of the sign-flipped shifted hypograph already lies in
its convex-cone hull. -/
lemma helperForLemma_31_0_2_mem_shiftedHypographCone_of_le {n : ℕ}
    (α : ℝ) {g : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {μ : ℝ}
    (hμ : (μ : EReal) ≤ (α : EReal) + g x) :
    (x, -μ) ∈ helperForLemma_31_0_2_shiftedHypographCone α g := by
  -- Start from the actual shifted hypograph point and insert it into the cone hull.
  have hbase :
      (x, -μ) ∈ {p : (Fin n → ℝ) × ℝ | ((-p.2 : ℝ) : EReal) ≤ (α : EReal) + g p.1} := by
    simpa using hμ
  exact
    (ConvexCone.subset_hull
      (s := {p : (Fin n → ℝ) × ℝ | ((-p.2 : ℝ) : EReal) ≤ (α : EReal) + g p.1}) hbase)

/-- Helper for Lemma 31.0.2: the corrected shifted hypograph cone is convex. -/
lemma helperForLemma_31_0_2_convex_shiftedHypographCone {n : ℕ}
    (α : ℝ) (g : (Fin n → ℝ) → EReal) :
    Convex ℝ (helperForLemma_31_0_2_shiftedHypographCone α g) := by
  -- The carrier of a convex cone is convex.
  simpa [helperForLemma_31_0_2_shiftedHypographCone] using
    (ConvexCone.convex (C := ConvexCone.hull ℝ
      {p : (Fin n → ℝ) × ℝ | ((-p.2 : ℝ) : EReal) ≤ (α : EReal) + g p.1}))

/-- Helper for Lemma 31.0.2: the corrected shifted hypograph cone is stable under positive
scaling. -/
lemma helperForLemma_31_0_2_smul_mem_shiftedHypographCone {n : ℕ}
    (α : ℝ) (g : (Fin n → ℝ) → EReal) {t : ℝ} (ht : 0 < t)
    {p : (Fin n → ℝ) × ℝ}
    (hp : p ∈ helperForLemma_31_0_2_shiftedHypographCone α g) :
    t • p ∈ helperForLemma_31_0_2_shiftedHypographCone α g := by
  -- Positive scaling is built into the convex-cone hull.
  simpa [helperForLemma_31_0_2_shiftedHypographCone] using
    (ConvexCone.smul_mem
      (C := ConvexCone.hull ℝ
        {p : (Fin n → ℝ) × ℝ | ((-p.2 : ℝ) : EReal) ≤ (α : EReal) + g p.1})
      ht hp)

/-- Helper for Lemma 31.0.2: the lifted balance generators package the upper epigraph points of
`f` together with the exact sign-flipped lower slices coming from finite points of `g + α`. -/
noncomputable def helperForLemma_31_0_2_liftedBalanceGeneratorSet {n : ℕ}
    (α : ℝ) (f g : (Fin n → ℝ) → EReal) :
    Set (ℝ × (Fin n → ℝ) × ℝ) :=
  {z : ℝ × (Fin n → ℝ) × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} ∪
    {z : ℝ × (Fin n → ℝ) × ℝ |
      ∃ x, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g ∧
        z = (-1, -x, -(α + (g x).toReal))}

/-- Helper for Lemma 31.0.2: every admissible upper epigraph generator belongs to the lifted
balance generator set. -/
lemma helperForLemma_31_0_2_mem_liftedBalanceGeneratorSet_upper {n : ℕ}
    (α : ℝ) {f g : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {μ : ℝ}
    (hμ : f x ≤ (μ : EReal)) :
    (1, x, μ) ∈ helperForLemma_31_0_2_liftedBalanceGeneratorSet α f g := by
  -- Insert the upper generator directly into the left summand of the defining union.
  exact Or.inl ⟨x, μ, rfl, hμ⟩

/-- Helper for Lemma 31.0.2: every admissible lower generator belongs to the lifted balance
generator set. -/
lemma helperForLemma_31_0_2_mem_liftedBalanceGeneratorSet_lower {n : ℕ}
    (α : ℝ) {f g : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    (-1, -x, -(α + (g x).toReal)) ∈ helperForLemma_31_0_2_liftedBalanceGeneratorSet α f g := by
  -- Insert the exact lower slice coming from the finite value of `g x`.
  exact Or.inr ⟨x, hx, rfl⟩

/-- Helper for Lemma 31.0.2: the lifted balance generator set is nonempty because a proper convex
function has a finite epigraph point. -/
lemma helperForLemma_31_0_2_liftedBalanceGeneratorSet_nonempty {n : ℕ}
    (α : ℝ) {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    (helperForLemma_31_0_2_liftedBalanceGeneratorSet α f g).Nonempty := by
  -- Use a finite point of `f` to produce one upper generator.
  rcases properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf with ⟨x0, r0, hr0⟩
  refine ⟨(1, x0, r0), ?_⟩
  exact
    helperForLemma_31_0_2_mem_liftedBalanceGeneratorSet_upper
      (α := α) (f := f) (g := g) (x := x0) (μ := r0) (by simpa [hr0])

/-- Helper for Lemma 31.0.2: on the effective domain of `g`, the primal lower bound
`α ≤ f - g` rewrites to the more geometric inequality `α + g ≤ f`. -/
lemma helperForLemma_31_0_2_shiftedPointwiseBoundOnEffectiveDomain {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x)
    {x : Fin n → ℝ}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    (α : EReal) + g x ≤ f x := by
  -- Finite-domain membership for `g` supplies the side conditions for undoing the subtraction.
  have hgx_ne_top : g x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hx
  have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
  exact
    (EReal.le_sub_iff_add_le (Or.inl hgx_ne_bot) (Or.inl hgx_ne_top)).1
      (hPointwise x)

/-- Helper for Lemma 31.0.2: the relative-interior hypothesis on `dom f - dom g` yields one
common primal point where both `f` and `g` are finite. -/
lemma helperForLemma_31_0_2_commonFinitePoint_of_zero_mem_domainDifference {n : ℕ}
    {f g : (Fin n → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hZeroDomDiffRi :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f -
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∃ x0 : Fin n → ℝ, ∃ rF rG : ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g ∧
          f x0 = (rF : EReal) ∧
            g x0 = (rG : EReal) := by
  let domF : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  have hzero_mem : (0 : Fin n → ℝ) ∈ domF - domG := by
    -- A relative-interior point of the domain difference already belongs to that difference.
    exact
      helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin
        (by simpa [domF, domG] using hZeroDomDiffRi)
  rcases hzero_mem with ⟨xF, hxF, xG, hxG, hFG⟩
  have hxEq : xF = xG := sub_eq_zero.mp hFG
  have hxG' : xF ∈ domG := by
    simpa [hxEq] using hxG
  have hfx_ne_top : f xF ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxF
  have hfx_ne_bot : f xF ≠ (⊥ : EReal) := hf.2.2 xF (by simp)
  have hgx_ne_top : g xF ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hxG'
  have hgx_ne_bot : g xF ≠ (⊥ : EReal) := hg.2.2 xF (by simp)
  refine ⟨xF, (f xF).toReal, (g xF).toReal, hxF, hxG', ?_, ?_⟩
  · -- Record the exact finite value of `f` at the anchor point.
    simpa using (EReal.coe_toReal (x := f xF) hfx_ne_top hfx_ne_bot).symm
  · -- Record the exact finite value of `g` at the same anchor point.
    simpa using (EReal.coe_toReal (x := g xF) hgx_ne_top hgx_ne_bot).symm

/-- Helper for Lemma 31.0.2: at a common effective-domain point, the shifted primal bound
`α + g ≤ f` becomes the real-coordinate inequality `α + g(x).toReal ≤ f(x).toReal`. -/
lemma helperForLemma_31_0_2_shiftedRealBoundOnCommonEffectiveDomain {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x)
    {x : Fin n → ℝ}
    (hxF : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (hxG : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    α + (g x).toReal ≤ (f x).toReal := by
  -- First rewrite the extended-real lower bound into the geometric form `α + g x ≤ f x`.
  have hShifted :
      (α : EReal) + g x ≤ f x :=
    helperForLemma_31_0_2_shiftedPointwiseBoundOnEffectiveDomain
      (f := f) (g := g) α hg hPointwise hxG
  have hfx_ne_top : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxF
  have hfx_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x (by simp)
  have hgx_ne_top : g x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := g) hxG
  have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
  have hShiftedReal :
      (((α + (g x).toReal : ℝ) : EReal)) ≤ (((f x).toReal : ℝ) : EReal) := by
    -- Replace both finite function values by their exact real representatives.
    simpa [EReal.coe_add, EReal.coe_toReal (x := f x) hfx_ne_top hfx_ne_bot,
      EReal.coe_toReal (x := g x) hgx_ne_top hgx_ne_bot] using hShifted
  exact (EReal.coe_le_coe_iff).1 hShiftedReal

/-- Helper for Lemma 31.0.2: the relative-interior qualification yields one common finite anchor
point together with the real inequality `α + g(x₀).toReal ≤ f(x₀).toReal` needed by the direct
separation route. -/
lemma helperForLemma_31_0_2_commonFinitePoint_with_shiftedRealBound {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x)
    (hZeroDomDiffRi :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f -
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∃ x0 : Fin n → ℝ, ∃ rF rG : ℝ,
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
        x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g ∧
          f x0 = (rF : EReal) ∧
            g x0 = (rG : EReal) ∧
              α + rG ≤ rF := by
  rcases
      helperForLemma_31_0_2_commonFinitePoint_of_zero_mem_domainDifference
        (f := f) (g := g) hf hg hZeroDomDiffRi with
    ⟨x0, rF, rG, hxF, hxG, hfx, hgx⟩
  have hReal :
      α + (g x0).toReal ≤ (f x0).toReal :=
    helperForLemma_31_0_2_shiftedRealBoundOnCommonEffectiveDomain
      (f := f) (g := g) α hf hg hPointwise hxF hxG
  have hAnchorBound : α + rG ≤ rF := by
    -- Rewrite the real inequality using the recorded exact finite values at the anchor point.
    simpa [hfx, hgx] using hReal
  exact ⟨x0, rF, rG, hxF, hxG, hfx, hgx, hAnchorBound⟩

/-- Helper for Lemma 31.0.2: the zero-balance slice gap records the infimum of the translated
primal difference over pairs `(u, v)` with horizontal defect `u - v = z`, while sending
inadmissible pairs to `⊤`. -/
noncomputable def helperForLemma_31_0_2_zeroBalanceSliceGap {n : ℕ}
    (α : ℝ) (f g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun z =>
    ⨅ uv : (Fin n → ℝ) × (Fin n → ℝ),
      if _hEq : uv.1 - uv.2 = z then
        if _hDom :
            uv.1 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
              uv.2 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g then
          f uv.1 - ((α : EReal) + g uv.2)
        else
          (⊤ : EReal)
      else
        (⊤ : EReal)

/-- Helper for Lemma 31.0.2: on a common finite point, the pointwise primal bound `α ≤ f - g`
rewrites as nonnegativity of the translated gap `f - (α + g)`. -/
lemma helperForLemma_31_0_2_nonnegative_translatedGap_on_commonEffectiveDomain {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x)
    {x : Fin n → ℝ}
    (hxF : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (hxG : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    (0 : EReal) ≤ f x - ((α : EReal) + g x) := by
  -- The geometric lower slice `α + g x ≤ f x` is exactly the inequality needed to make the
  -- translated gap nonnegative at a common effective-domain point.
  have hShifted :
      (α : EReal) + g x ≤ f x :=
    helperForLemma_31_0_2_shiftedPointwiseBoundOnEffectiveDomain
      (f := f) (g := g) α hg hPointwise hxG
  have hfx_ne_top : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hxF
  have hgx_ne_bot : g x ≠ (⊥ : EReal) := hg.2.2 x (by simp)
  have hShifted_ne_bot : (α : EReal) + g x ≠ (⊥ : EReal) :=
    add_ne_bot_of_notbot (by simp) hgx_ne_bot
  exact
    (EReal.le_sub_iff_add_le
      (Or.inl hShifted_ne_bot)
      (Or.inr hfx_ne_top)).2
      (by simpa)

/-- Helper for Lemma 31.0.2: the translated zero-balance slice function is already nonnegative at
the exact slice `z = 0`, because every admissible pair there lies on the diagonal `u = v`. -/
lemma helperForLemma_31_0_2_zeroBalanceSliceGap_nonnegative_at_zero {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x) :
    (0 : EReal) ≤ helperForLemma_31_0_2_zeroBalanceSliceGap α f g 0 := by
  -- Unfold the infimum: out-of-slice or out-of-domain pairs contribute `⊤`, and on the zero
  -- slice the previous diagonal-gap lemma gives the desired nonnegativity.
  rw [helperForLemma_31_0_2_zeroBalanceSliceGap]
  refine le_iInf ?_
  intro uv
  by_cases hEq : uv.1 - uv.2 = (0 : Fin n → ℝ)
  · by_cases hDom :
        uv.1 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∧
          uv.2 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
    · have huv : uv.1 = uv.2 := sub_eq_zero.mp hEq
      have hDomG : uv.1 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g := by
        simpa [huv] using hDom.2
      have hNonneg :
          (0 : EReal) ≤ f uv.1 - ((α : EReal) + g uv.2) := by
        -- Along the zero slice, `u = v`, so the translated-gap estimate applies on the diagonal.
        simpa [huv] using
          helperForLemma_31_0_2_nonnegative_translatedGap_on_commonEffectiveDomain
            (f := f) (g := g) α hg hPointwise hDom.1 hDomG
      simpa [hEq, hDom] using hNonneg
    · simp [hEq, hDom]
  · simp [hEq]

/-- Helper for Lemma 31.0.2: any admissible pair on the defect-`z` slice gives an explicit
upper bound for the slice infimum. -/
lemma helperForLemma_31_0_2_zeroBalanceSliceGap_le_of_admissiblePair {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    {z u v : Fin n → ℝ}
    (hEq : u - v = z)
    (huF : u ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    (hvG : v ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    helperForLemma_31_0_2_zeroBalanceSliceGap α f g z ≤
      f u - ((α : EReal) + g v) := by
  -- Route correction: the midpoint-based lower bound proposed in the previous plan is false for
  -- convex-convex pairs in general; the infimum is only immediately controlled from above by an
  -- admissible slice witness.
  rw [helperForLemma_31_0_2_zeroBalanceSliceGap]
  refine iInf_le_of_le (u, v) ?_
  simp [hEq, huF, hvG]

/-- Helper for Lemma 31.0.2: the relative-interior anchor data gives a real upper bound for the
zero-balance slice at `z = 0`. -/
lemma helperForLemma_31_0_2_zeroBalanceSliceGap_boundedAboveAtZero {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x)
    (hZeroDomDiffRi :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f -
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∃ r : ℝ, helperForLemma_31_0_2_zeroBalanceSliceGap α f g 0 ≤ (r : EReal) := by
  rcases
      helperForLemma_31_0_2_commonFinitePoint_with_shiftedRealBound
        (f := f) (g := g) α hf hg hPointwise hZeroDomDiffRi with
    ⟨x0, rF, rG, hxF, hxG, hfx, hgx, _hAnchorBound⟩
  refine ⟨rF - (α + rG), ?_⟩
  -- Evaluate the zero-balance infimum at the diagonal anchor pair `(x₀, x₀)`.
  have hDiag :
      helperForLemma_31_0_2_zeroBalanceSliceGap α f g 0 ≤
        f x0 - ((α : EReal) + g x0) :=
    helperForLemma_31_0_2_zeroBalanceSliceGap_le_of_admissiblePair
      (α := α) (z := (0 : Fin n → ℝ)) (u := x0) (v := x0)
      (by simp) hxF hxG
  -- Rewrite the finite anchor values into real coordinates to get an explicit real upper bound.
  rw [show (((rF - (α + rG) : ℝ) : EReal)) =
      (rF : EReal) - ((α + rG : ℝ) : EReal) by simp]
  simpa [hfx, hgx, EReal.coe_add] using hDiag

/-- Helper for Lemma 31.0.2: the zero-balance slice has an actual finite real value at the
origin once the diagonal nonnegativity is combined with the common finite anchor. -/
lemma helperForLemma_31_0_2_zeroBalanceSliceGap_finiteAtZero {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x)
    (hZeroDomDiffRi :
      (0 : Fin n → ℝ) ∈
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f -
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g)) :
    ∃ r : ℝ, helperForLemma_31_0_2_zeroBalanceSliceGap α f g 0 = (r : EReal) := by
  let ψ : EReal := helperForLemma_31_0_2_zeroBalanceSliceGap α f g 0
  have hNonneg : (0 : EReal) ≤ ψ := by
    -- The diagonal slice is always nonnegative because `α + g ≤ f` on `dom g`.
    simpa [ψ] using
      helperForLemma_31_0_2_zeroBalanceSliceGap_nonnegative_at_zero
        (f := f) (g := g) α hg hPointwise
  rcases
      helperForLemma_31_0_2_zeroBalanceSliceGap_boundedAboveAtZero
        (f := f) (g := g) α hf hg hPointwise hZeroDomDiffRi with
    ⟨r, hUpper⟩
  have hne_top : ψ ≠ (⊤ : EReal) := by
    intro hTop
    have hUpperTop := hUpper
    simp [ψ, hTop] at hUpperTop
  have hne_bot : ψ ≠ (⊥ : EReal) := by
    intro hBot
    have hNonnegBot := hNonneg
    simp [ψ, hBot] at hNonnegBot
  -- Finite upper and lower bounds identify the zero slice with a real number.
  refine ⟨ψ.toReal, ?_⟩
  simpa [ψ] using (EReal.coe_toReal (x := ψ) hne_top hne_bot).symm

/-- Helper for Lemma 31.0.2: pack the lifted balance generators into `Fin (n + 2)` coordinates,
placing the primal vector first, the vertical coordinate second-to-last, and the balance
coordinate last. -/
noncomputable def helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet {n : ℕ}
    (α : ℝ) (f g : (Fin n → ℝ) → EReal) :
    Set (Fin (n + 2) → ℝ) :=
  (fun z : ℝ × (Fin n → ℝ) × ℝ =>
    prodLinearEquiv_append_coord (n := n + 1)
      (prodLinearEquiv_append_coord (n := n) (z.2.1, z.2.2), z.1)) ''
    helperForLemma_31_0_2_liftedBalanceGeneratorSet α f g

/-- Helper for Lemma 31.0.2: in the encoded coordinates, the forbidden point is the negative
vertical direction with zero primal and balance components. -/
noncomputable def helperForLemma_31_0_2_encodedNegativeVerticalPoint {n : ℕ} :
    Fin (n + 2) → ℝ :=
  prodLinearEquiv_append_coord (n := n + 1)
    (prodLinearEquiv_append_coord (n := n) (0, (-1 : ℝ)), (0 : ℝ))

/-- Helper for Lemma 31.0.2: every admissible upper generator remains visible after packing the
lifted balance generators into `Fin (n + 2)` coordinates. -/
lemma helperForLemma_31_0_2_mem_encodedLiftedBalanceGeneratorSet_upper {n : ℕ}
    (α : ℝ) {f g : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {μ : ℝ}
    (hμ : f x ≤ (μ : EReal)) :
    prodLinearEquiv_append_coord (n := n + 1)
        (prodLinearEquiv_append_coord (n := n) (x, μ), (1 : ℝ)) ∈
      helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet α f g := by
  -- Encode the already-available upper generator witness into the packed coordinates.
  refine ⟨(1, x, μ), ?_, rfl⟩
  exact
    helperForLemma_31_0_2_mem_liftedBalanceGeneratorSet_upper
      (α := α) (f := f) (g := g) (x := x) (μ := μ) hμ

/-- Helper for Lemma 31.0.2: every admissible lower generator remains visible after packing the
lifted balance generators into `Fin (n + 2)` coordinates. -/
lemma helperForLemma_31_0_2_mem_encodedLiftedBalanceGeneratorSet_lower {n : ℕ}
    (α : ℝ) {f g : (Fin n → ℝ) → EReal} {x : Fin n → ℝ}
    (hx : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) :
    prodLinearEquiv_append_coord (n := n + 1)
        (prodLinearEquiv_append_coord (n := n) (-x, -(α + (g x).toReal)), (-1 : ℝ)) ∈
      helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet α f g := by
  -- Encode the repaired exact lower generator coming from the finite value of `g x`.
  refine ⟨(-1, -x, -(α + (g x).toReal)), ?_, rfl⟩
  exact
    helperForLemma_31_0_2_mem_liftedBalanceGeneratorSet_lower
      (α := α) (f := f) (g := g) (x := x) hx

/-- Helper for Lemma 31.0.2: decoding a packed encoded generator recovers an actual lifted
balance generator in the original `(λ, x, μ)` coordinates. -/
lemma helperForLemma_31_0_2_decoded_mem_liftedBalanceGeneratorSet_of_mem_encoded {n : ℕ}
    (α : ℝ) {f g : (Fin n → ℝ) → EReal} {y : Fin (n + 2) → ℝ}
    (hy : y ∈ helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet α f g) :
    let q := (prodLinearEquiv_append_coord (n := n + 1)).symm y
    let p := (prodLinearEquiv_append_coord (n := n)).symm q.1
    (q.2, p.1, p.2) ∈ helperForLemma_31_0_2_liftedBalanceGeneratorSet α f g := by
  -- Unpack the image witness and then cancel the two coordinate-packing equivalences.
  rcases hy with ⟨z, hz, rfl⟩
  simp at hz ⊢
  simpa using hz

/-- Helper for Lemma 31.0.2: the forbidden packed negative vertical vector is genuinely nonzero,
so conic-combination extraction does not collapse to the origin case. -/
lemma helperForLemma_31_0_2_encodedNegativeVerticalPoint_ne_zero {n : ℕ} :
    helperForLemma_31_0_2_encodedNegativeVerticalPoint (n := n) ≠ (0 : Fin (n + 2) → ℝ) := by
  intro hZero
  -- Decode the outer packing first, then decode the inner `(x, μ)` packing.
  have hOuter :
      prodLinearEquiv_append_coord (n := n) (0, (-1 : ℝ)) = (0 : Fin (n + 1) → ℝ) := by
    simpa [helperForLemma_31_0_2_encodedNegativeVerticalPoint] using
      congrArg ((prodLinearEquiv_append_coord (n := n + 1)).symm) hZero
  have hInner : ((0 : Fin n → ℝ), (-1 : ℝ)) = (0 : (Fin n → ℝ) × ℝ) := by
    simpa using congrArg ((prodLinearEquiv_append_coord (n := n)).symm) hOuter
  have hMinusOne : (-1 : ℝ) = 0 := by
    simpa using congrArg Prod.snd hInner
  norm_num at hMinusOne

/-- Helper for Lemma 31.0.2: a nonzero point of the encoded cone hull admits a finite
nonnegative linear-combination witness over encoded generators. -/
lemma helperForLemma_31_0_2_exists_nonnegLinearCombination_of_mem_encodedHull {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {y : Fin (n + 2) → ℝ}
    (hy : y ∈
      (ConvexCone.hull ℝ
        (helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet α f g) :
          Set (Fin (n + 2) → ℝ))) :
    ∃ k : ℕ, k ≤ n + 2 ∧
      ∃ v : Fin k → Fin (n + 2) → ℝ, ∃ c : Fin k → ℝ,
        (∀ i, v i ∈ helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet α f g) ∧
          (∀ i, 0 ≤ c i) ∧
            y = ∑ i, c i • v i := by
  let T : Set (Fin (n + 2) → ℝ) := helperForLemma_31_0_2_encodedLiftedBalanceGeneratorSet α f g
  have hTne : T.Nonempty :=
    by
      -- A proper point of `f` gives an upper generator, hence an encoded generator as well.
      rcases properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf with
        ⟨x0, r0, hr0⟩
      refine ⟨prodLinearEquiv_append_coord (n := n + 1)
          (prodLinearEquiv_append_coord (n := n) (x0, r0), (1 : ℝ)), ?_⟩
      exact
        helperForLemma_31_0_2_mem_encodedLiftedBalanceGeneratorSet_upper
          (α := α) (f := f) (g := g) (x := x0) (μ := r0) (by simpa [hr0])
  have hyCone : y ∈ convexConeGenerated (n + 2) T := by
    -- Membership in the raw cone hull is exactly the nonzero branch of `convexConeGenerated`.
    change y ∈ Set.insert (0 : Fin (n + 2) → ℝ) ((ConvexCone.hull ℝ T : ConvexCone ℝ _) : Set _)
    exact (Set.mem_insert_iff).2 (Or.inr (by simpa [T] using hy))
  rcases
      mem_convexConeGenerated_imp_exists_nonnegLinearCombination_le
        (n := n + 2) (T := T) hTne hyCone with
    ⟨k, hk, v, c, hv, hc, hEq⟩
  exact ⟨k, hk, v, c, hv, hc, hEq⟩


end Section31
end Chap06

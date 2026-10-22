/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part7

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart8 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

variable {m n : ℕ}


/-- Helper for Text 34.1.4: every constant kernel is fixed by the first partial closure. -/
lemma helperForText_34_1_4_partialClosure₁_constantKernel
    (c : ℝ) :
    partialClosure₁ (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) =
      (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) := by
  funext u v
  apply le_antisymm
  · -- Evaluate the outer infimum at radius `1`; the inner supremum of a constant section is
    -- still the same constant.
    have hε : (0 : ℝ) < 1 := by
      norm_num
    calc
      concaveClosureInFirst (fun _ _ => ((c : ℝ) : EReal)) u v
          ≤ ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < (1 : ℝ)}), ((c : ℝ) : EReal) :=
            iInf_le
              (fun ε : {ε : ℝ // 0 < ε} =>
                ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), ((c : ℝ) : EReal))
              ⟨1, hε⟩
      _ = ((c : ℝ) : EReal) := by
          apply le_antisymm
          · refine iSup_le ?_
            intro w
            exact le_rfl
          · exact
              le_iSup (fun w : {w : Fin m → ℝ // ‖w - u‖ < (1 : ℝ)} => ((c : ℝ) : EReal))
                ⟨u, by simpa using hε⟩
  · -- Conversely, every inner supremum contains the center point `u`, so the infimum stays
    -- above the constant value.
    refine le_iInf ?_
    intro ε
    refine le_iSup (fun w : {w : Fin m → ℝ // ‖w - u‖ < ε.1} => ((c : ℝ) : EReal))
      ⟨u, ?_⟩
    simpa using ε.2

/-- Helper for Text 34.1.4: every constant kernel is fixed by the second partial closure. -/
lemma helperForText_34_1_4_partialClosure₂_constantKernel
    (c : ℝ) :
    partialClosure₂ (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) =
      (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) := by
  funext u v
  apply le_antisymm
  · -- Each inner infimum is bounded above by the center point `v`.
    refine iSup_le ?_
    intro ε
    refine iInf_le (fun w : {w : Fin n → ℝ // ‖w - v‖ < ε.1} => ((c : ℝ) : EReal))
      ⟨v, ?_⟩
    simpa using ε.2
  · -- Evaluating the outer supremum at radius `1` gives back the same constant value.
    have hε : (0 : ℝ) < 1 := by
      norm_num
    calc
      ((c : ℝ) : EReal)
          ≤ ⨅ (w : {w : Fin n → ℝ // ‖w - v‖ < (1 : ℝ)}), ((c : ℝ) : EReal) := by
            simp
      _ ≤ convexClosureInSecond (fun _ _ => ((c : ℝ) : EReal)) u v := by
            exact
              le_iSup
                (fun ε : {ε : ℝ // 0 < ε} =>
                  ⨅ (w : {w : Fin n → ℝ // ‖w - v‖ < ε.1}), ((c : ℝ) : EReal))
                ⟨1, hε⟩

/-- Helper for Text 34.1.4: a constant kernel is concave-convex. -/
lemma helperForText_34_1_4_constantKernel_isConcaveConvex
    (c : ℝ) :
    IsConcaveConvex
      (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) := by
  unfold IsConcaveConvex IsConcaveConvexOn IsERealConcaveOn IsERealConvexOn
  constructor
  · intro v hv x y hx hy a b ha hb hab hxy
    change ((a : EReal) * ((c : ℝ) : EReal) + (b : EReal) * ((c : ℝ) : EReal)) ≤
      ((c : ℝ) : EReal)
    -- Rewrite the weighted endpoint sum back to the constant value `c`.
    have hmulA :
        (a : EReal) * ((c : ℝ) : EReal) = ((a * c : ℝ) : EReal) := by
      simpa using (EReal.coe_mul a c).symm
    have hmulB :
        (b : EReal) * ((c : ℝ) : EReal) = ((b * c : ℝ) : EReal) := by
      simpa using (EReal.coe_mul b c).symm
    rw [hmulA, hmulB]
    have hadd :
        ((a * c : ℝ) : EReal) + ((b * c : ℝ) : EReal) =
          (((a * c) + (b * c) : ℝ) : EReal) := by
      simpa using (EReal.coe_add (a * c) (b * c)).symm
    rw [hadd]
    have hConst : a * c + b * c = c := by
      calc
        a * c + b * c = (a + b) * c := by ring
        _ = c := by rw [hab, one_mul]
    rw [hConst]
  · intro u hu x y hx hy a b ha hb hab hxy
    change ((c : ℝ) : EReal) ≤
      ((a : EReal) * ((c : ℝ) : EReal) + (b : EReal) * ((c : ℝ) : EReal))
    -- The same rewrite proves the convex inequality in the second variable.
    have hmulA :
        (a : EReal) * ((c : ℝ) : EReal) = ((a * c : ℝ) : EReal) := by
      simpa using (EReal.coe_mul a c).symm
    have hmulB :
        (b : EReal) * ((c : ℝ) : EReal) = ((b * c : ℝ) : EReal) := by
      simpa using (EReal.coe_mul b c).symm
    rw [hmulA, hmulB]
    have hadd :
        ((a * c : ℝ) : EReal) + ((b * c : ℝ) : EReal) =
          (((a * c) + (b * c) : ℝ) : EReal) := by
      simpa using (EReal.coe_add (a * c) (b * c)).symm
    rw [hadd]
    have hConst : a * c + b * c = c := by
      calc
        a * c + b * c = (a + b) * c := by ring
        _ = c := by rw [hab, one_mul]
    rw [hConst]

/-- Helper for Text 34.1.4: a constant kernel is upper closed in the Section 33 saddle sense. -/
lemma helperForText_34_1_4_constantKernel_isUpperClosedSaddleFunction
    (c : ℝ) :
    IsUpperClosedSaddleFunction
      (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) := by
  have hOrient :
      IsConcaveConvex
        (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) :=
    helperForText_34_1_4_constantKernel_isConcaveConvex (m := m) (n := n) c
  have hFirstFixed :
      partialClosure₁ (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) =
        (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) :=
    helperForText_34_1_4_partialClosure₁_constantKernel (m := m) (n := n) c
  have hSecondFixed :
      partialClosure₂ (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) =
        (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) :=
    helperForText_34_1_4_partialClosure₂_constantKernel (m := m) (n := n) c
  left
  constructor
  · -- The orientation is the constant-kernel concave-convexity proved just above.
    exact hOrient
  · -- Because both one-variable closures fix the constant kernel, so does their composition.
    calc
      partialClosure₁ (partialClosure₂ (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)))
          = partialClosure₁ (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) := by
            rw [hSecondFixed]
      _ = (fun (_ : Fin m → ℝ) (_ : Fin n → ℝ) => ((c : ℝ) : EReal)) := hFirstFixed

/-- Helper for Text 34.1.4: a closed convex bifunction with no `⊥` values is already
Rockafellar convex. -/
lemma helperForText_34_1_4_rockafellarConvex_of_closedConvexBifunction
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F) :
    IsRockafellarConvexBifunction F := by
  have hGraphConvex : IsGraphConvexBifunction F := by
    have hGraphConvexFunction : ConvexFunction (graphFunctionOfBifunction F) := by
      simpa [ClosedConvexBifunction, ConvexBifunction, bifunctionGraphFunction,
        graphFunctionOfBifunction] using hClosed.1
    have hGraphNoBot :
        ∀ z : Fin (m + n) → ℝ, graphFunctionOfBifunction F z ≠ (⊥ : EReal) := by
      intro z
      simpa [graphFunctionOfBifunction] using
        hNoBot (fun i : Fin m => z (Fin.castAdd n i))
          (fun j : Fin n => z (Fin.natAdd m j))
    exact
      helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ
        (f := graphFunctionOfBifunction F) hGraphConvexFunction hGraphNoBot
  exact helperForLemma33_0_22_graphConvex_gives_rockafellarConvex hGraphConvex

/-- Helper for Text 34.1.4: the constant zero kernel satisfies the corrected Corollary 33.3.1,
so it has a canonical Section 33 witness. -/
lemma helperForText_34_1_4_zeroKernel_hasCanonicalWitness
    (hRealization : Section34CanonicalClosureRealizationQualification 1 1) :
    ∃ F : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
      IsRockafellarConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        ClosedConvexBifunction F ∧
        (fun (_ : Fin 1 → ℝ) (_ : Fin 1 → ℝ) => ((0 : ℝ) : EReal)) =
          convexBifunctionPairing F ∧
        partialClosure₁ (fun (_ : Fin 1 → ℝ) (_ : Fin 1 → ℝ) => ((0 : ℝ) : EReal)) =
          helperForText_34_0_1_convexAdjointPairingKernel F := by
  let L : SaddleFunction 1 1 := fun _ _ => ((0 : ℝ) : EReal)
  have hLOrient : IsConcaveConvex L := by
    simpa [L] using
      (helperForText_34_1_4_constantKernel_isConcaveConvex (m := 1) (n := 1) (c := 0))
  have hLFirstFixed : partialClosure₁ L = L := by
    simpa [L] using
      (helperForText_34_1_4_partialClosure₁_constantKernel (m := 1) (n := 1) (c := 0))
  have hLSecondFixed : partialClosure₂ L = L := by
    simpa [L] using
      (helperForText_34_1_4_partialClosure₂_constantKernel (m := 1) (n := 1) (c := 0))
  have hLNoTopBot : HasNoTopOrBotValuesBifunction L := by
    constructor
    · intro u x hBot
      norm_num [L] at hBot
    · intro u x hTop
      norm_num [L] at hTop
  have hLowerFixed : lowerClosureConcaveConvex L hLOrient = L := by
    rw [(helperForText_34_0_1_mixedClosure_formulas L hLOrient).1,
      hLFirstFixed, hLSecondFixed]
  have hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex L hLOrient) := by
    simpa [hLowerFixed] using hLNoTopBot
  rcases
      helperForText_34_1_4_closedConvexWitness_exists_for_canonicalUpperPartner
        L hLOrient hLNoTopBot.1 hLowerNoTopBot hRealization with
    ⟨F, hClosed, hNoBot, hLowerRep, hUpperRep⟩
  have hRock : IsRockafellarConvexBifunction F :=
    helperForText_34_1_4_rockafellarConvex_of_closedConvexBifunction hClosed hNoBot
  refine ⟨F, hRock, hNoBot, hClosed, ?_, ?_⟩
  · change L = convexBifunctionPairing F
    exact hLowerFixed.symm.trans hLowerRep
  · change partialClosure₁ L = helperForText_34_0_1_convexAdjointPairingKernel F
    rw [← hLowerFixed]
    exact hUpperRep
  where
    L : SaddleFunction 1 1 := fun _ _ => ((0 : ℝ) : EReal)

/-- Helper for Text 34.1.4: the abstract upper-partner minimality statement requested in the
previous replans is false without an additional witness hypothesis. A constant `-1` kernel is
upper closed and lies below the fully fixed constant `0` kernel, but the two kernels are not
equal. -/
lemma helperForText_34_1_4_upperPartnerMinimality_withoutWitness_false :
    ∃ L U : SaddleFunction 1 1,
      partialClosure₁ L = L ∧
      partialClosure₂ L = L ∧
      IsUpperClosedSaddleFunction U ∧
      U ≤ L ∧
      U ≠ partialClosure₁ L := by
  let L : SaddleFunction 1 1 := fun _ _ => ((0 : ℝ) : EReal)
  let U : SaddleFunction 1 1 := fun _ _ => (((-1 : ℝ)) : EReal)
  have hLFirstFixed : partialClosure₁ L = L := by
    simpa [L] using
      (helperForText_34_1_4_partialClosure₁_constantKernel (m := 1) (n := 1) (c := 0))
  have hLSecondFixed : partialClosure₂ L = L := by
    simpa [L] using
      (helperForText_34_1_4_partialClosure₂_constantKernel (m := 1) (n := 1) (c := 0))
  have hUUpperClosed : IsUpperClosedSaddleFunction U := by
    -- The abstract counterexample uses the constant `-1` kernel as the strict upper-closed
    -- minorant.
    simpa [U] using
      (helperForText_34_1_4_constantKernel_isUpperClosedSaddleFunction
        (m := 1) (n := 1) (c := -1))
  have hULeL : U ≤ L := by
    -- Pointwise, `-1 ≤ 0`.
    intro u v
    norm_num [L, U]
  have hUne : U ≠ partialClosure₁ L := by
    intro hEq
    -- Evaluating the alleged equality at the origin exposes the contradiction `-1 = 0`.
    rw [hLFirstFixed] at hEq
    have hPoint := congrArg (fun F => F 0 0) hEq
    norm_num [L, U] at hPoint
  exact ⟨L, U, hLFirstFixed, hLSecondFixed, hUUpperClosed, hULeL, hUne⟩

/-- Helper for Text 34.1.4: even a canonical Section 33 witness for a fully fixed lower
representative does not, by itself, exclude an unrelated strict upper-closed minorant.

This formal counterexample explains why the remaining blocker must mention the actual mixed
upper closure `overline(K)`, not just abstract witness data for `underline(K)`. -/
lemma helperForText_34_1_4_canonicalWitness_doesNotExclude_strictUpperClosedMinorant
    (hRealization : Section34CanonicalClosureRealizationQualification 1 1) :
    ∃ L U : SaddleFunction 1 1,
      (∃ F : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
        IsRockafellarConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          ClosedConvexBifunction F ∧
          L = convexBifunctionPairing F ∧
          partialClosure₁ L = helperForText_34_0_1_convexAdjointPairingKernel F) ∧
      partialClosure₁ L = L ∧
      partialClosure₂ L = L ∧
      IsUpperClosedSaddleFunction U ∧
      U ≤ L ∧
      U ≠ L := by
  let L : SaddleFunction 1 1 := fun _ _ => ((0 : ℝ) : EReal)
  let U : SaddleFunction 1 1 := fun _ _ => (((-1 : ℝ)) : EReal)
  have hWitness :
      ∃ F : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
        IsRockafellarConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          ClosedConvexBifunction F ∧
          L = convexBifunctionPairing F ∧
          partialClosure₁ L = helperForText_34_0_1_convexAdjointPairingKernel F := by
    simpa [L] using helperForText_34_1_4_zeroKernel_hasCanonicalWitness hRealization
  have hLFirstFixed : partialClosure₁ L = L := by
    simpa [L] using
      (helperForText_34_1_4_partialClosure₁_constantKernel (m := 1) (n := 1) (c := 0))
  have hLSecondFixed : partialClosure₂ L = L := by
    simpa [L] using
      (helperForText_34_1_4_partialClosure₂_constantKernel (m := 1) (n := 1) (c := 0))
  have hUUpperClosed : IsUpperClosedSaddleFunction U := by
    simpa [U] using
      (helperForText_34_1_4_constantKernel_isUpperClosedSaddleFunction
        (m := 1) (n := 1) (c := -1))
  have hULeL : U ≤ L := by
    intro u v
    norm_num [L, U]
  have hUne : U ≠ L := by
    intro hEq
    have hPoint := congrArg (fun K => K 0 0) hEq
    norm_num [L, U] at hPoint
  exact ⟨L, U, hWitness, hLFirstFixed, hLSecondFixed, hUUpperClosed, hULeL, hUne⟩

end SaddleAmbient

end Section34
end Chap07

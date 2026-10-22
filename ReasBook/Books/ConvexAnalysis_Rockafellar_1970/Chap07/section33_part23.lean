/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part22

section Chap07
section Section33

attribute [local instance] Classical.propDecidable

/-- Helper for Corollary33.3.2: simultaneous concave-convex and convex-concave structure
forces the second-variable convex closure to fix the kernel.

This is the symmetric one-step closure fact used to collapse the `Or.inr` branch in
Corollary33.3.2. -/
lemma helperForCorollary33_3_2_simultaneousOrientations_fix_convexClosureInSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hVC : IsConvexConcaveOn Set.univ Set.univ K) :
    convexClosureInSecond K = K := by
  -- Step 1: reduce the kernel-level fixed-point statement to lower semicontinuity of each
  -- frozen second-variable section.
  apply
    helperForCorollary33_3_2_convexClosureInSecond_eq_self_of_sectionLowerSemicontinuous
      (K := K)
  intro u
  have hConvSection :
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) :=
    hK.2 u (by simp)
  have hConcSection :
      IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) (fun xStar => K u xStar) :=
    hVC.2 u (by simp)
  -- Step 2: the same simultaneous-orientation classification gives lower semicontinuity for
  -- the frozen second-variable section.
  exact
    (helperForCorollary33_3_2_upperLowerSemicontinuous_of_simultaneousConvexConcave
      (g := fun xStar => K u xStar) hConcSection hConvSection).2

/-- Helper for Corollary33.3.2: under the concave-convex hypothesis, the lower-closed
predicate reduces to the aligned identity `cl₂ (cl₁ K) = K`. -/
lemma helperForCorollary33_3_2_lowerClosed_concaveConvex_extract_lowerComposition
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn Set.univ Set.univ K)
    (hLower : IsLowerClosedSaddleFunction K) :
    convexClosureInSecond (concaveClosureInFirst K) = K := by
  -- Step 1: unfold the reducible lower-closed predicate and split on its two textbook
  -- orientation branches.
  dsimp [IsLowerClosedSaddleFunction, saddleClosednessPredicates] at hLower
  rcases hLower with hLowerCC | hLowerVC
  · -- Step 2: on the concave-convex branch, the aligned lower composition is part of the
    -- hypothesis already.
    exact hLowerCC.2
  · rcases hLowerVC with ⟨hVC, _hLowerSwap⟩
    -- Route correction: instead of converting the swapped lower identity directly, first use
    -- the simultaneous-orientation fixed-point lemmas to collapse the aligned composition.
    calc
      convexClosureInSecond (concaveClosureInFirst K)
          = convexClosureInSecond K := by
              rw
                [helperForCorollary33_3_2_simultaneousOrientations_fix_concaveClosureInFirst
                  (K := K) hK hVC]
      _ = K := by
            exact
              helperForCorollary33_3_2_simultaneousOrientations_fix_convexClosureInSecond
                (K := K) hK hVC

/-- Helper for Corollary33.3.2: under simultaneous concave-convex and convex-concave
orientations, the first-variable convex closure is already exact. -/
lemma helperForCorollary33_3_2_simultaneousOrientations_fix_convexClosureInFirst
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hCC : IsConcaveConvexOn Set.univ Set.univ K)
    (hVC : IsConvexConcaveOn Set.univ Set.univ K) :
    convexClosureInFirst K = K := by
  let Ks : (Fin n → ℝ) → (Fin m → ℝ) → EReal := fun v u => K u v
  have hKsCC :
      IsConcaveConvexOn (Set.univ : Set (Fin n → ℝ)) (Set.univ : Set (Fin m → ℝ)) Ks := by
    simpa [Ks] using
      helperForCorollary33_1_1_swap_preserves_convexConcave (K := K) hVC
  have hKsVC :
      IsConvexConcaveOn (Set.univ : Set (Fin n → ℝ)) (Set.univ : Set (Fin m → ℝ)) Ks := by
    constructor
    · intro u hu
      simpa [Ks] using hCC.2 u hu
    · intro v hv
      simpa [Ks] using hCC.1 v hv
  have hFixKs : convexClosureInSecond Ks = Ks :=
    helperForCorollary33_3_2_simultaneousOrientations_fix_convexClosureInSecond
      (K := Ks) hKsCC hKsVC
  funext u v
  have hPoint := congrArg (fun F => F v u) hFixKs
  simpa [Ks, convexClosureInSecond, convexClosureInFirst] using hPoint

/-- Helper for Corollary33.3.2: under simultaneous concave-convex and convex-concave
orientations, the second-variable concave closure is already exact. -/
lemma helperForCorollary33_3_2_simultaneousOrientations_fix_concaveClosureInSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hCC : IsConcaveConvexOn Set.univ Set.univ K)
    (hVC : IsConvexConcaveOn Set.univ Set.univ K) :
    concaveClosureInSecond K = K := by
  let Ks : (Fin n → ℝ) → (Fin m → ℝ) → EReal := fun v u => K u v
  have hKsCC :
      IsConcaveConvexOn (Set.univ : Set (Fin n → ℝ)) (Set.univ : Set (Fin m → ℝ)) Ks := by
    simpa [Ks] using
      helperForCorollary33_1_1_swap_preserves_convexConcave (K := K) hVC
  have hKsVC :
      IsConvexConcaveOn (Set.univ : Set (Fin n → ℝ)) (Set.univ : Set (Fin m → ℝ)) Ks := by
    constructor
    · intro u hu
      simpa [Ks] using hCC.2 u hu
    · intro v hv
      simpa [Ks] using hCC.1 v hv
  have hFixKs : concaveClosureInFirst Ks = Ks :=
    helperForCorollary33_3_2_simultaneousOrientations_fix_concaveClosureInFirst
      (K := Ks) hKsCC hKsVC
  funext u v
  have hPoint := congrArg (fun F => F v u) hFixKs
  simpa [Ks, concaveClosureInFirst, concaveClosureInSecond] using hPoint

/-- Helper for Corollary33.3.2: under the convex-concave hypothesis, the upper-closed
predicate reduces to the aligned identity `cl₂^c (cl₁^v K) = K`. -/
lemma helperForCorollary33_3_2_upperClosed_convexConcave_extract_upperComposition
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConvexConcaveOn Set.univ Set.univ K)
    (hUpper : IsUpperClosedSaddleFunction K) :
    concaveClosureInSecond (convexClosureInFirst K) = K := by
  dsimp [IsUpperClosedSaddleFunction, saddleClosednessPredicates] at hUpper
  rcases hUpper with hUpperCC | hUpperVC
  · rcases hUpperCC with ⟨hCC, _hUpperComp⟩
    calc
      concaveClosureInSecond (convexClosureInFirst K)
          = concaveClosureInSecond K := by
              rw
                [helperForCorollary33_3_2_simultaneousOrientations_fix_convexClosureInFirst
                  (K := K) hCC hK]
      _ = K := by
            exact
              helperForCorollary33_3_2_simultaneousOrientations_fix_concaveClosureInSecond
                (K := K) hCC hK
  · exact hUpperVC.2

lemma helperForCorollary33_3_2_upperClosed_concaveConvex_extract_upperComposition
    {m n : ℕ}
    {Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hKbar : IsConcaveConvexOn Set.univ Set.univ Kbar)
    (hUpper : IsUpperClosedSaddleFunction Kbar) :
    concaveClosureInFirst (convexClosureInSecond Kbar) = Kbar := by
  -- Step 1: unfold the reducible upper-closed predicate and split on its two textbook
  -- orientation branches.
  dsimp [IsUpperClosedSaddleFunction, saddleClosednessPredicates] at hUpper
  rcases hUpper with hUpperCC | hUpperVC
  · -- Step 2: on the concave-convex branch, the aligned upper composition is already present.
    exact hUpperCC.2
  · rcases hUpperVC with ⟨hVC, _hUpperSwap⟩
    -- Route correction: rewrite through the same one-step fixed-point lemmas instead of
    -- converting the swapped upper identity in one jump.
    calc
      concaveClosureInFirst (convexClosureInSecond Kbar)
          = concaveClosureInFirst Kbar := by
              rw
                [helperForCorollary33_3_2_simultaneousOrientations_fix_convexClosureInSecond
                  (K := Kbar) hKbar hVC]
      _ = Kbar := by
            exact
              helperForCorollary33_3_2_simultaneousOrientations_fix_concaveClosureInFirst
                (K := Kbar) hKbar hVC

theorem lowerClosed_concaveConvex_upperClosed_concaveConvex_closure_correspondence :
    ∀ {m n : ℕ},
      (∀ (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
          IsConcaveConvexOn Set.univ Set.univ K →
            HasNoBotValuesBifunction K →
            IsLowerClosedSaddleFunction K →
              ∃! Kbar,
                IsConcaveConvexOn Set.univ Set.univ Kbar ∧
                  IsUpperClosedSaddleFunction Kbar ∧
                    Kbar = concaveClosureInFirst K ∧
                      convexClosureInSecond Kbar = K) ∧
        ∀ (Kbar : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
          IsConcaveConvexOn Set.univ Set.univ Kbar →
            HasNoBotValuesBifunction Kbar →
            IsUpperClosedSaddleFunction Kbar →
              ∃! K,
                IsConcaveConvexOn Set.univ Set.univ K ∧
                  IsLowerClosedSaddleFunction K ∧
                    Kbar = concaveClosureInFirst K ∧
                      convexClosureInSecond Kbar = K :=
  fun {m n} => by
    constructor
    · intro K hK hNoBot hLower
      -- Step 1: choose the textbook upper partner `Kbar := cl₁ K` and record the closure
      -- data supplied by Corollary 33.1.1.
      let Kbar := concaveClosureInFirst K
      have hClosures :=
        helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
          (K := K) hK hNoBot
      have hLowerComp :
          convexClosureInSecond (concaveClosureInFirst K) = K :=
        helperForCorollary33_3_2_lowerClosed_concaveConvex_extract_lowerComposition
          (K := K) hK hLower
      have hWitnessClosed :
          IsUpperClosedSaddleFunction Kbar :=
        (helperForCorollary33_3_1_coordinatewise_closure_pair_implies_closedness_and_order
          (K := K) (Kbar := Kbar) hK hClosures.1 ⟨rfl, hLowerComp⟩).2.1
      refine ⟨Kbar, ?_, ?_⟩
      · -- Step 2: the chosen `cl₁ K` is concave-convex, upper closed, and satisfies the
        -- two displayed closure identities by construction.
        exact ⟨hClosures.1, hWitnessClosed, rfl, hLowerComp⟩
      · intro Kbar' hKbar'
        -- Step 3: uniqueness is just the stored equality `Kbar' = cl₁ K`.
        exact hKbar'.2.2.1
    · intro Kbar hKbar hNoBot hUpper
      -- Step 1: choose the textbook lower partner `K := cl₂ Kbar` and record the closure
      -- data supplied by Corollary 33.1.1.
      let K := convexClosureInSecond Kbar
      have hClosures :=
        helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
          (K := Kbar) hKbar hNoBot
      have hUpperComp :
          concaveClosureInFirst (convexClosureInSecond Kbar) = Kbar :=
        helperForCorollary33_3_2_upperClosed_concaveConvex_extract_upperComposition
          (Kbar := Kbar) hKbar hUpper
      have hWitnessClosed :
          IsLowerClosedSaddleFunction K :=
        (helperForCorollary33_3_1_coordinatewise_closure_pair_implies_closedness_and_order
          (K := K) (Kbar := Kbar) hClosures.2.1 hKbar ⟨hUpperComp.symm, rfl⟩).1
      refine ⟨K, ?_, ?_⟩
      · -- Step 2: the chosen `cl₂ Kbar` is concave-convex, lower closed, and satisfies the
        -- two displayed closure identities by construction.
        exact ⟨hClosures.2.1, hWitnessClosed, hUpperComp.symm, rfl⟩
      · intro K' hK'
        -- Step 3: uniqueness is just the stored equality `cl₂ Kbar = K'`.
        exact hK'.2.2.2.symm

/-- Negating a concave section produces a convex one as soon as the original section avoids
`⊤`. This is the one-variable sign transport needed for the corrected reverse bridge. -/
lemma helperForCorollary33_3_2_concaveNegation_isConvex_of_noTop
    {k : ℕ} {f : (Fin k → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin k → ℝ)) f)
    (hNoTop : ∀ x, f x ≠ ⊤) :
    IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) (fun x => -f x) := by
  intro x y hx hy a b ha hb hab hxy
  have hJensen :
      (a : EReal) * f x + (b : EReal) * f y ≤ f (a • x + b • y) :=
    hConc (x := x) (y := y) hx hy ha hb hab hxy
  have hTerm1_ne_top : (a : EReal) * f x ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot a), Or.inl ?_, Or.inl (EReal.coe_ne_top a), ?_⟩
    · exact_mod_cast ha
    · by_cases hZero : a = 0
      · left
        simp [hZero]
      · right
        exact hNoTop x
  have hTerm2_ne_top : (b : EReal) * f y ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot b), Or.inl ?_, Or.inl (EReal.coe_ne_top b), ?_⟩
    · exact_mod_cast hb
    · by_cases hZero : b = 0
      · left
        simp [hZero]
      · right
        exact hNoTop y
  have hNegJensen :
      -f (a • x + b • y) ≤ -((a : EReal) * f x + (b : EReal) * f y) := by
    simpa using hJensen
  have hNegWeighted :
      -((a : EReal) * f x + (b : EReal) * f y) =
        (a : EReal) * (-f x) + (b : EReal) * (-f y) := by
    have hNegAdd :=
      EReal.neg_add (x := (a : EReal) * f x) (y := (b : EReal) * f y)
        (Or.inr hTerm2_ne_top) (Or.inl hTerm1_ne_top)
    simpa [sub_eq_add_neg, mul_neg, neg_mul, add_comm] using hNegAdd
  calc
    -f (a • x + b • y) ≤ -((a : EReal) * f x + (b : EReal) * f y) := hNegJensen
    _ = (a : EReal) * (-f x) + (b : EReal) * (-f y) := hNegWeighted

/-- Negating the first-variable concave closure converts it into the corresponding first-variable
convex closure. -/
lemma helperForCorollary33_3_2_neg_concaveClosureInFirst_eq_convexClosureInFirst
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    concaveClosureInFirst (fun u x => -K u x) = fun u x => -convexClosureInFirst K u x := by
  funext u x
  unfold concaveClosureInFirst convexClosureInFirst
  have hTmp :=
    helperForLemma33_0_5_negatedTwoLayerClosureIdentity
      (fun (ε : {ε : ℝ // 0 < ε})
        (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}) => K w.1 x)
  simpa using (congrArg Neg.neg hTmp).symm

/-- Negating the second-variable convex closure converts it into the corresponding
second-variable concave closure. -/
lemma helperForCorollary33_3_2_neg_convexClosureInSecond_eq_concaveClosureInSecond
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    convexClosureInSecond (fun u x => -K u x) = fun u x => -concaveClosureInSecond K u x := by
  funext u x
  unfold convexClosureInSecond concaveClosureInSecond
  simpa using
    helperForLemma33_0_5_negatedTwoLayerClosureIdentity
      (fun (ε : {ε : ℝ // 0 < ε})
        (w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}) => -K u w.1)

/-- After sign reversal, an upper-closed convex-concave kernel becomes a lower-closed
concave-convex kernel. -/
lemma helperForCorollary33_3_2_negated_upperClosedConvexConcave_isLowerClosed
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConvexConcaveOn Set.univ Set.univ K)
    (hUpper : IsUpperClosedSaddleFunction K)
    (hNoTop : HasNoTopValuesBifunction K) :
    IsLowerClosedSaddleFunction (fun u x => -K u x) := by
  have hNegCC :
      IsConcaveConvexOn Set.univ Set.univ (fun u x => -K u x) := by
    constructor
    · intro x hx
      exact helperForLemma33_0_5_convexNegation_isConcave (hK.1 x hx)
    · intro u hu
      exact
        helperForCorollary33_3_2_concaveNegation_isConvex_of_noTop
          (hK.2 u hu) (fun x => hNoTop u x)
  have hUpperComp : concaveClosureInSecond (convexClosureInFirst K) = K :=
    helperForCorollary33_3_2_upperClosed_convexConcave_extract_upperComposition
      (K := K) hK hUpper
  dsimp [IsLowerClosedSaddleFunction, saddleClosednessPredicates]
  refine Or.inl ⟨hNegCC, ?_⟩
  calc
    convexClosureInSecond (concaveClosureInFirst (fun u x => -K u x))
        = convexClosureInSecond (fun u x => -convexClosureInFirst K u x) := by
            rw [helperForCorollary33_3_2_neg_concaveClosureInFirst_eq_convexClosureInFirst
              (K := K)]
    _ = (fun u x => -concaveClosureInSecond (convexClosureInFirst K) u x) := by
          rw [helperForCorollary33_3_2_neg_convexClosureInSecond_eq_concaveClosureInSecond
            (K := convexClosureInFirst K)]
    _ = (fun u x => -K u x) := by
          funext u x
          exact congrArg Neg.neg (congrArg (fun H => H u x) hUpperComp)

theorem finiteContinuous_concaveConvex_simpleExtensions_yield_closed_convex_bifunction :
    ∀ {m n : ℕ}
      {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
      {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ},
      C.Nonempty →
        D.Nonempty →
          IsClosed C →
            IsClosed D →
              Convex ℝ C →
                Convex ℝ D →
                  ContinuousOn (fun p => K p.1 p.2) (C.prod D) →
                    IsConcaveConvexOn C D (erealOfRealBifunction K) →
                      have K1 := lowerSimpleExtensionOfReal C D K
                      have K2 := upperSimpleExtensionOfReal C D K
                      IsLowerClosedSaddleFunction K1 ∧
                        ∃! F,
                          IsRockafellarConvexBifunction F ∧
                            HasNoBotValuesBifunction F ∧
                              IsFunctionConvexClosed (graphFunctionOfBifunction F) ∧
                                (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
                                  K1 u xStar = convexBifunctionPairing F u xStar) ∧
                                  (∀ (u : Fin m → ℝ) (xStar : Fin n → ℝ),
                                    K2 u xStar = genuineConvexBifunctionAdjointPairing F u xStar) ∧
                                    (∀ (u : Fin m → ℝ) (x : Fin n → ℝ),
                                      F u x =
                                        if _ : u ∈ C then
                                          sSup (Set.range fun xStar : D => ↑(x ⬝ᵥ ↑xStar - K u ↑xStar))
                                        else ⊤) ∧
                                      (∀ (xStar : Fin n → ℝ) (uStar : Fin m → ℝ),
                                        genuineConvexBifunctionAdjoint F xStar uStar =
                                          if _ : xStar ∈ D then
                                            sInf (Set.range fun u : C => ↑(↑u ⬝ᵥ uStar - K (↑u) xStar))
                                          else ⊥) ∧
                                        convexBifunctionParameterDomain F = C ∧
                                          {xStar | ∃ uStar,
                                              genuineConvexBifunctionAdjoint F xStar uStar ≠ ⊥} = D :=
  fun {_} {_} {_} {_} {_} hC_nonempty hD_nonempty hC_closed hD_closed hC_convex hD_convex
      hK_cont hK_concaveConvex =>
    «Corollary33.3.3» hC_nonempty hD_nonempty hC_closed hD_closed hC_convex hD_convex
      hK_cont hK_concaveConvex

end Section33
end Chap07

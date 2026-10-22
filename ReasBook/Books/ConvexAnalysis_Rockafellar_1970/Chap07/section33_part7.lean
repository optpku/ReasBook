/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section19_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part6

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- Helper for Corollary33.1.1: swapping the variables turns a convex-concave kernel into a
concave-convex kernel. -/
lemma helperForCorollary33_1_1_swap_preserves_convexConcave
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K) :
    IsConcaveConvexOn (Set.univ : Set (Fin n → ℝ)) (Set.univ : Set (Fin m → ℝ))
      (fun v u => K u v) := by
  rcases hK with ⟨hConvInFirst, hConcInSecond⟩
  constructor
  · -- Concavity in the swapped first variable is the original second-variable concavity.
    intro u hu
    simpa using hConcInSecond u hu
  · -- Convexity in the swapped second variable is the original first-variable convexity.
    intro v hv
    simpa using hConvInFirst v hv

/-- Helper for Corollary33.1.1: swapping the variables turns a concave-convex kernel into a
convex-concave kernel. -/
lemma helperForCorollary33_1_1_swap_preserves_concaveConvex
    {m n : ℕ} {K : (Fin n → ℝ) → (Fin m → ℝ) → EReal}
    (hK : IsConcaveConvexOn (Set.univ : Set (Fin n → ℝ)) (Set.univ : Set (Fin m → ℝ)) K) :
    IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
      (fun u v => K v u) := by
  rcases hK with ⟨hConcInFirst, hConvInSecond⟩
  constructor
  · -- Convexity in the unswapped first variable is the original second-variable convexity.
    intro v hv
    simpa using hConvInSecond v hv
  · -- Concavity in the unswapped second variable is the original first-variable concavity.
    intro u hu
    simpa using hConcInFirst u hu

/-- Helper for Corollary33.1.1: a swapped kernel that is convex-closed in the second
variable becomes convex-closed in the first variable after unswapping. -/
lemma helperForCorollary33_1_1_swap_convexClosedInSecond_to_convexClosedInFirst
    {m n : ℕ} {K : (Fin n → ℝ) → (Fin m → ℝ) → EReal}
    (hK : IsConvexClosedInSecond K) :
    IsConvexClosedInFirst (fun u v => K v u) := by
  unfold IsConvexClosedInSecond at hK
  change (fun u v => K v u) = convexClosureInFirst (fun u v => K v u)
  -- Evaluate the fixed-point identity of the swapped kernel at the transposed point.
  funext u
  funext v
  have hPoint := congrArg (fun F => F v u) hK
  simpa [convexClosureInSecond, convexClosureInFirst] using hPoint

/-- Helper for Corollary33.1.1: a swapped kernel that is concave-closed in the first
variable becomes concave-closed in the second variable after unswapping. -/
lemma helperForCorollary33_1_1_swap_concaveClosedInFirst_to_concaveClosedInSecond
    {m n : ℕ} {K : (Fin n → ℝ) → (Fin m → ℝ) → EReal}
    (hK : IsConcaveClosedInFirst K) :
    IsConcaveClosedInSecond (fun u v => K v u) := by
  unfold IsConcaveClosedInFirst at hK
  change (fun u v => K v u) = concaveClosureInSecond (fun u v => K v u)
  -- Evaluate the fixed-point identity of the swapped kernel at the transposed point.
  funext u
  funext v
  have hPoint := congrArg (fun F => F v u) hK
  simpa [concaveClosureInFirst, concaveClosureInSecond] using hPoint

/-- Corollary33.1.1 in the book's epi/hypograph semantics: coordinatewise closures preserve
both saddle orientations and are fixed points of the corresponding closure operators. -/
theorem coordinatewise_closures_preserve_saddle_orientations
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    (IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
      IsEpigraphHypographConcaveConvex (concaveClosureInFirst K) ∧
        IsEpigraphHypographConcaveConvex (convexClosureInSecond K) ∧
        IsConcaveClosedInFirst (concaveClosureInFirst K) ∧
        IsConvexClosedInSecond (convexClosureInSecond K)) ∧
      (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
        IsEpigraphHypographConvexConcave (convexClosureInFirst K) ∧
          IsEpigraphHypographConvexConcave (concaveClosureInSecond K) ∧
          IsConvexClosedInFirst (convexClosureInFirst K) ∧
          IsConcaveClosedInSecond (concaveClosureInSecond K)) := by
  constructor
  · intro hK
    exact helperForCorollary33_1_1_concaveConvex_coordinatewise_closures (K := K) hK
  · intro hK
    let Ks : (Fin n → ℝ) → (Fin m → ℝ) → EReal := fun v u => K u v
    have hKs :
        IsConcaveConvexOn (Set.univ : Set (Fin n → ℝ)) (Set.univ : Set (Fin m → ℝ)) Ks := by
      exact helperForCorollary33_1_1_swap_preserves_convexConcave (K := K) hK
    rcases helperForCorollary33_1_1_concaveConvex_coordinatewise_closures (K := Ks) hKs with
      ⟨hKsConcave, hKsConvex, hKsConcaveClosed, hKsConvexClosed⟩
    have hSwapConcave :
        concaveClosureInFirst Ks = fun v u => concaveClosureInSecond K u v := by
      funext v
      funext u
      exact (helperForCorollary33_1_1_swap_coordinatewise_closure_identities
        (K := K) (u := u) (v := v)).1
    have hSwapConvex :
        convexClosureInSecond Ks = fun v u => convexClosureInFirst K u v := by
      funext v
      funext u
      exact (helperForCorollary33_1_1_swap_coordinatewise_closure_identities
        (K := K) (u := u) (v := v)).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [IsEpigraphHypographConvexConcave, Ks, hSwapConvex] using hKsConvex
    · simpa [IsEpigraphHypographConvexConcave, Ks, hSwapConcave] using hKsConcave
    · simpa [Ks, hSwapConvex] using
        helperForCorollary33_1_1_swap_convexClosedInSecond_to_convexClosedInFirst
          (K := convexClosureInSecond Ks) hKsConvexClosed
    · simpa [Ks, hSwapConcave] using
        helperForCorollary33_1_1_swap_concaveClosedInFirst_to_concaveClosedInSecond
          (K := concaveClosureInFirst Ks) hKsConcaveClosed

/-- Strong Jensen form of Corollary33.1.1 under the explicit convention that `K` never takes
`⊥`. -/
theorem coordinatewise_closures_preserve_saddle_orientations_of_noBot
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hNoBot : ∀ u v, K u v ≠ (⊥ : EReal)) :
    (IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
          (concaveClosureInFirst K) ∧
        IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
          (convexClosureInSecond K) ∧
        IsConcaveClosedInFirst (concaveClosureInFirst K) ∧
        IsConvexClosedInSecond (convexClosureInSecond K)) ∧
      (IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
        IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
            (convexClosureInFirst K) ∧
          IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
            (concaveClosureInSecond K) ∧
          IsConvexClosedInFirst (convexClosureInFirst K) ∧
          IsConcaveClosedInSecond (concaveClosureInSecond K)) := by
  constructor
  · intro hK
    -- The concave-convex branch is exactly the packaged closure statement proved above.
    exact helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
      (K := K) hK hNoBot
  · intro hK
    let Ks : (Fin n → ℝ) → (Fin m → ℝ) → EReal := fun v u => K u v
    have hKs :
        IsConcaveConvexOn (Set.univ : Set (Fin n → ℝ)) (Set.univ : Set (Fin m → ℝ)) Ks := by
      -- Swap the variables so the convex-concave kernel fits the first half of the corollary.
      exact helperForCorollary33_1_1_swap_preserves_convexConcave (K := K) hK
    rcases helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
        (K := Ks) hKs (fun v u => hNoBot u v) with
      ⟨hKsConcave, hKsConvex, hKsConcaveClosed, hKsConvexClosed⟩
    have hSwapConcave :
        concaveClosureInFirst Ks = fun v u => concaveClosureInSecond K u v := by
      -- The swapped first-variable concave closure is the original second-variable
      -- concave closure.
      funext v
      funext u
      exact (helperForCorollary33_1_1_swap_coordinatewise_closure_identities
        (K := K) (u := u) (v := v)).1
    have hSwapConvex :
        convexClosureInSecond Ks = fun v u => convexClosureInFirst K u v := by
      -- The swapped second-variable convex closure is the original first-variable
      -- convex closure.
      funext v
      funext u
      exact (helperForCorollary33_1_1_swap_coordinatewise_closure_identities
        (K := K) (u := u) (v := v)).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Unswap the swapped convex closure to obtain first-variable convex closure of `K`.
      simpa [Ks, hSwapConvex] using
        helperForCorollary33_1_1_swap_preserves_concaveConvex
          (K := convexClosureInSecond Ks) hKsConvex
    · -- Unswap the swapped concave closure to obtain second-variable concave closure of `K`.
      simpa [Ks, hSwapConcave] using
        helperForCorollary33_1_1_swap_preserves_concaveConvex
          (K := concaveClosureInFirst Ks) hKsConcave
    · -- The swapped convex closedness is exactly first-variable convex closedness after
      -- restoring the original argument order.
      simpa [Ks, hSwapConvex] using
        helperForCorollary33_1_1_swap_convexClosedInSecond_to_convexClosedInFirst
          (K := convexClosureInSecond Ks) hKsConvexClosed
    · -- The swapped concave closedness is exactly second-variable concave closedness after
      -- restoring the original argument order.
      simpa [Ks, hSwapConcave] using
        helperForCorollary33_1_1_swap_concaveClosedInFirst_to_concaveClosedInSecond
          (K := concaveClosureInFirst Ks) hKsConcaveClosed

/-- Helper for the concave side of Theorem33.1: negating a concave `EReal` section that avoids
`⊤` produces a convex section. This is the exact sign-transport used to dualize the convex-side
Rockafellar package. -/
lemma helperForCorollary33_1_2_concaveNegation_isConvex_of_noTop
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

/-- Helper for the concave side of Theorem33.1: the convex pairing of the negated bifunction is
exactly the negative of the original concave pairing, with the expected sign flip in the dual
variable. -/
lemma helperForCorollary33_1_2_convexPairing_negated_eq_neg_concavePairing
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    convexBifunctionPairing (fun u' x => -F u' x) u xStar =
      -concaveBifunctionPairing F u (-xStar) := by
  have h :=
    helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
      (g := F u) (xStar := -xStar)
  calc
    convexBifunctionPairing (fun u' x => -F u' x) u xStar
        = fenchelConjugate n (fun x => -(F u x)) xStar := by
            rfl
    _ = -concaveConjugate (F u) (-xStar) := by
          simpa using (congrArg Neg.neg h).symm
    _ = -concaveBifunctionPairing F u (-xStar) := by
          rfl

/-- Helper for the concave side of Theorem33.1: negating a Rockafellar concave bifunction that
avoids `⊤` yields the corresponding Rockafellar convex bifunction that avoids `⊥`. -/
lemma helperForCorollary33_1_2_negatedConcaveBifunction_isRockafellarConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConcaveBifunction F)
    (hNoTop : HasNoTopValuesBifunction F) :
    let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => -F u x
    IsRockafellarConvexBifunction G ∧ HasNoBotValuesBifunction G := by
  rcases hRock with ⟨hConcSections, hPairConvex⟩
  let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => -F u x
  have hSectionConvex : IsRockafellarSectionwiseConvexBifunction G := by
    intro u
    exact
      helperForCorollary33_1_2_concaveNegation_isConvex_of_noTop
        (hConc := hConcSections u) (hNoTop := fun x => hNoTop u x)
  have hPairConcave : HasConcaveParameterConvexPairing G := by
    intro xStar
    have hConv :
        IsERealConvexOn (Set.univ : Set (Fin m → ℝ))
          (fun u => concaveBifunctionPairing F u (-xStar)) :=
      hPairConvex (-xStar)
    have hNegConc :=
      helperForLemma33_0_5_convexNegation_isConcave (C := Set.univ) (f := fun u => concaveBifunctionPairing F u (-xStar)) hConv
    simpa [G, helperForCorollary33_1_2_convexPairing_negated_eq_neg_concavePairing] using hNegConc
  have hNoBot : HasNoBotValuesBifunction G := by
    intro u x
    simpa [G] using hNoTop u x
  exact ⟨⟨hSectionConvex, hPairConcave⟩, hNoBot⟩

/-- Precomposing with the involution `x ↦ -x` preserves convexity on the whole space. -/
lemma helperForCorollary33_1_2_precomp_neg_isERealConvexOn
    {k : ℕ} {f : (Fin k → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) f) :
    IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) (fun x => f (-x)) := by
  intro x y hx hy a b ha hb hab hxy
  simpa [smul_neg, neg_add_rev, add_comm, add_left_comm, add_assoc] using
    hConv (x := -x) (y := -y) (by simp) (by simp) ha hb hab (by simp)

/-- The constant `⊤` function is concave on `ℝ^k`. -/
lemma helperForCorollary33_1_2_constTop_isERealConcaveOn
    {k : ℕ} :
    IsERealConcaveOn (Set.univ : Set (Fin k → ℝ)) (fun _ => (⊤ : EReal)) := by
  intro x y hx hy a b ha hb hab hxy
  simp

/-- The Section 33 one-variable concave closure is the negative of the convex closure of the
negated function. -/
lemma helperForCorollary33_1_2_functionConcaveClosure_eq_neg_functionConvexClosure_neg
    {k : ℕ}
    {g : (Fin k → ℝ) → EReal} :
    functionConcaveClosure g = fun x => -functionConvexClosure (fun y => -g y) x := by
  funext x
  have hNeg :
      -functionConcaveClosure g x = functionConvexClosure (fun y => -g y) x := by
    unfold functionConcaveClosure functionConvexClosure
    change EReal.negOrderIso
        (⨅ (ε : {ε : ℝ // 0 < ε}),
          ⨆ (w : {w : Fin k → ℝ // ‖w - x‖ < ε.1}), g w.1) =
        ⨆ (ε : {ε : ℝ // 0 < ε}),
          ⨅ (w : {w : Fin k → ℝ // ‖w - x‖ < ε.1}), -g w.1
    rw [EReal.negOrderIso.map_iInf]
    congr
    funext ε
    rw [EReal.negOrderIso.map_iSup]
    rfl
  simpa using congrArg Neg.neg hNeg

/-- The constant `⊤` function is fixed by the one-variable concave closure. -/
lemma helperForCorollary33_1_2_constTop_isFunctionConcaveClosed
    {k : ℕ} :
    IsFunctionConcaveClosed (fun _ : Fin k → ℝ => (⊤ : EReal)) := by
  unfold IsFunctionConcaveClosed
  funext x
  symm
  calc
    functionConcaveClosure (fun _ : Fin k → ℝ => (⊤ : EReal)) x
        = -functionConvexClosure (fun _ : Fin k → ℝ => (⊥ : EReal)) x := by
            exact
              congrArg (fun h => h x)
                (helperForCorollary33_1_2_functionConcaveClosure_eq_neg_functionConvexClosure_neg
                  (g := fun _ : Fin k → ℝ => (⊤ : EReal)))
    _ = -(⊥ : EReal) := by
          have hNegLsc : LowerSemicontinuous (fun _ : Fin k → ℝ => (⊥ : EReal)) := by
            simpa using (continuous_const.lowerSemicontinuous :
              LowerSemicontinuous (fun _ : Fin k → ℝ => (⊥ : EReal)))
          have hNegClosed :
              (fun _ : Fin k → ℝ => (⊥ : EReal)) =
                functionConvexClosure (fun _ : Fin k → ℝ => (⊥ : EReal)) :=
            helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegLsc
          have hPoint :
              functionConvexClosure (fun _ : Fin k → ℝ => (⊥ : EReal)) x = (⊥ : EReal) :=
            congrArg (fun h => h x) hNegClosed.symm
          rw [hPoint]
    _ = (⊤ : EReal) := by simp

/-- Upper semicontinuous sections are already fixed by the one-variable Section 33 concave
closure. -/
lemma helperForCorollary33_1_2_functionConcaveClosure_eq_self_of_upperSemicontinuous
    {k : ℕ}
    {g : (Fin k → ℝ) → EReal}
    (hUpper : UpperSemicontinuous g) :
    functionConcaveClosure g = g := by
  have hNegLsc : LowerSemicontinuous (fun x => -g x) :=
    (helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg
      (g := g)).1 hUpper
  have hNegClosed :
      (fun x => -g x) = functionConvexClosure (fun y => -g y) :=
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegLsc
  funext x
  have hPoint :
      functionConvexClosure (fun y => -g y) x = -g x :=
    congrArg (fun h => h x) hNegClosed.symm
  calc
    functionConcaveClosure g x
        = -functionConvexClosure (fun y => -g y) x := by
            exact
              congrArg (fun h => h x)
                (helperForCorollary33_1_2_functionConcaveClosure_eq_neg_functionConvexClosure_neg
                  (g := g))
    _ = -(-g x) := by rw [hPoint]
    _ = g x := by simp

/-- If a section has one point different from `⊥`, then its concave conjugate is concave. -/
lemma helperForCorollary33_1_2_concaveConjugate_isERealConcaveOn_of_point
    {k : ℕ} {g : (Fin k → ℝ) → EReal} {x₀ : Fin k → ℝ}
    (hx₀_ne_bot : g x₀ ≠ ⊥) :
    IsERealConcaveOn (Set.univ : Set (Fin k → ℝ)) (concaveConjugate g) := by
  have hConv :
      IsERealConvexOn (Set.univ : Set (Fin k → ℝ))
        (fun x => convexConjugate (fun y => -g y) (-x)) := by
    have hBase :
        IsERealConvexOn (Set.univ : Set (Fin k → ℝ))
          (convexConjugate (fun y => -g y)) := by
      simpa [convexConjugate] using
        helperForTheorem33_1_convexConjugate_isERealConvexOn_of_point
          (f := fun y => -g y) (x₀ := x₀) (by simpa using hx₀_ne_bot)
    exact helperForCorollary33_1_2_precomp_neg_isERealConvexOn hBase
  have hConc :
      IsERealConcaveOn (Set.univ : Set (Fin k → ℝ))
        (fun x => -convexConjugate (fun y => -g y) (-x)) :=
    helperForLemma33_0_5_convexNegation_isConcave (C := Set.univ)
      (f := fun x => convexConjugate (fun y => -g y) (-x)) hConv
  have hEq :
      (fun x => -convexConjugate (fun y => -g y) (-x)) = concaveConjugate g := by
    funext x
    simpa [convexConjugate] using
      (helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
        (g := g) (xStar := x)).symm
  simpa [hEq] using hConc

/-- The concave conjugate is concave, with the exceptional all-`⊥` branch collapsing to the
constant `⊤` function. -/
lemma helperForCorollary33_1_2_concaveConjugate_isERealConcaveOn
    {k : ℕ} {g : (Fin k → ℝ) → EReal} :
    IsERealConcaveOn (Set.univ : Set (Fin k → ℝ)) (concaveConjugate g) := by
  by_cases hAllBot : ∀ x : Fin k → ℝ, g x = ⊥
  · have hTop : concaveConjugate g = fun _ : Fin k → ℝ => (⊤ : EReal) := by
      funext xStar
      rw [concaveConjugate, sInf_range]
      apply le_antisymm
      · exact le_top
      · refine le_iInf ?_
        intro x
        simp [hAllBot x]
    simpa [hTop] using helperForCorollary33_1_2_constTop_isERealConcaveOn (k := k)
  · rcases not_forall.mp hAllBot with ⟨x₀, hx₀⟩
    exact
      helperForCorollary33_1_2_concaveConjugate_isERealConcaveOn_of_point
        (g := g) (x₀ := x₀) hx₀

/-- If a section has one point different from `⊥`, then its concave conjugate is already fixed
by the one-variable Section 33 concave closure. -/
lemma helperForCorollary33_1_2_concaveConjugate_isFunctionConcaveClosed_of_point
    {k : ℕ} {g : (Fin k → ℝ) → EReal} {x₀ : Fin k → ℝ}
    (hx₀_ne_bot : g x₀ ≠ ⊥) :
    IsFunctionConcaveClosed (concaveConjugate g) := by
  have hClosed :
      IsFunctionConvexClosed (convexConjugate (fun y => -g y)) := by
    simpa [convexConjugate] using
      helperForTheorem33_1_convexConjugate_isFunctionConvexClosed_of_point
        (f := fun y => -g y) (x₀ := x₀) (by simpa using hx₀_ne_bot)
  have hLscClosure :
      LowerSemicontinuous
        (functionConvexClosure (convexConjugate (fun y => -g y))) :=
    helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
      (f := convexConjugate (fun y => -g y))
  have hLsc :
      LowerSemicontinuous (convexConjugate (fun y => -g y)) := by
    rw [← hClosed] at hLscClosure
    exact hLscClosure
  have hLscPre :
      LowerSemicontinuous (fun x => convexConjugate (fun y => -g y) (-x)) :=
    hLsc.comp_continuous continuous_neg
  have hNegEq :
      (fun x => -concaveConjugate g x) =
        fun x => convexConjugate (fun y => -g y) (-x) := by
    simpa [convexConjugate] using
      helperForTheorem_6_30_3_neg_concaveConjugate_eq_fenchel_precomp_neg (g := g)
  have hUpper : UpperSemicontinuous (concaveConjugate g) := by
    rw [helperForTheorem_6_30_2_upperSemicontinuous_iff_lowerSemicontinuous_neg]
    rw [hNegEq]
    exact hLscPre
  unfold IsFunctionConcaveClosed
  symm
  exact
    helperForCorollary33_1_2_functionConcaveClosure_eq_self_of_upperSemicontinuous
      (g := concaveConjugate g) hUpper

/-- The concave conjugate is always fixed by the one-variable Section 33 concave closure; the
only exceptional branch is the constant `⊤` one when the primal section is identically `⊥`. -/
lemma helperForCorollary33_1_2_concaveConjugate_isFunctionConcaveClosed
    {k : ℕ} {g : (Fin k → ℝ) → EReal} :
    IsFunctionConcaveClosed (concaveConjugate g) := by
  by_cases hAllBot : ∀ x : Fin k → ℝ, g x = ⊥
  · have hTop : concaveConjugate g = fun _ : Fin k → ℝ => (⊤ : EReal) := by
      funext xStar
      rw [concaveConjugate, sInf_range]
      apply le_antisymm
      · exact le_top
      · refine le_iInf ?_
        intro x
        simp [hAllBot x]
    simpa [hTop] using
      helperForCorollary33_1_2_constTop_isFunctionConcaveClosed (k := k)
  · rcases not_forall.mp hAllBot with ⟨x₀, hx₀⟩
    exact
      helperForCorollary33_1_2_concaveConjugate_isFunctionConcaveClosed_of_point
        (g := g) (x₀ := x₀) hx₀

/-- For a concave section with no `⊤` values, the Section 33 concave biconjugate identity is
exactly the one-variable concave closure formula. -/
lemma helperForCorollary33_1_2_biconjugate_eq_functionConcaveClosure_of_concave
    {k : ℕ} {g : (Fin k → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin k → ℝ)) g)
    (hNoTop : ∀ x, g x ≠ ⊤) :
    ∀ x, concaveConjugate (concaveConjugate g) x = functionConcaveClosure g x := by
  have hConcFun : ConcaveFunction g := by
    unfold ConcaveFunction
    exact
      helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction
        (helperForCorollary33_1_2_concaveNegation_isConvex_of_noTop
          (hConc := hConc) (hNoTop := hNoTop))
  have hClosureEq : functionConcaveClosure g = concaveClosure g := by
    funext x
    have hConvClosureEq :
        functionConvexClosure (fun y => -g y) = convexFunctionClosure (fun y => -g y) :=
      helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
        (f := fun y => -g y) (by
          intro y
          simpa [EReal.neg_eq_bot_iff] using hNoTop y)
    calc
      functionConcaveClosure g x = -functionConvexClosure (fun y => -g y) x := by
        exact
          congrArg (fun h => h x)
            (helperForCorollary33_1_2_functionConcaveClosure_eq_neg_functionConvexClosure_neg
              (g := g))
      _ = -convexFunctionClosure (fun y => -g y) x := by
            rw [congrArg (fun h => h x) hConvClosureEq]
      _ = concaveClosure g x := by rfl
  intro x
  simpa [hClosureEq] using
    congrArg (fun h => h x)
      (concaveConjugate_biconjugate_eq_concaveClosure (g := g) hConcFun)

-- Proof sketch: argue exactly as in Theorem33.1, but with the concave conjugate replacing
-- the convex conjugate, with convexity/concavity reversed in the two variables, and with
-- the one-sided `EReal` hypotheses adjusted to the concave convention.
/-- The dual saddle-function correspondence for concave bifunctions and convex-concave kernels. -/
theorem concaveBifunction_pairing_correspondence
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConcaveBifunction F →
      HasNoTopValuesBifunction F →
        IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
            (concaveBifunctionPairing F) ∧
          IsConcaveClosedInSecond (concaveBifunctionPairing F) ∧
          ∀ u x,
            functionConcaveClosure (F u) x =
              concaveConjugate (concaveBifunctionPairing F u) x) ∧
    (∀ K : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
      HasNoTopOrBotValuesBifunction K →
        let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
          fun u x => concaveConjugate (K u) x
        IsRockafellarConcaveBifunction F ∧
          (∀ u, IsFunctionConcaveClosed (F u)) ∧
          ∀ u xStar,
            concaveBifunctionPairing F u xStar =
              concaveClosureInSecond K u xStar) := by
  constructor
  · intro F hRock hNoTop
    rcases hRock with ⟨hConcSections, hPairConvex⟩
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro xStar hxStar
        exact hPairConvex xStar
      · intro u hu
        simpa [concaveBifunctionPairing, bifunctionPairingNotation] using
          helperForCorollary33_1_2_concaveConjugate_isERealConcaveOn (g := F u)
    · unfold IsConcaveClosedInSecond
      funext u
      simpa [concaveBifunctionPairing, bifunctionPairingNotation] using
        helperForCorollary33_1_2_concaveConjugate_isFunctionConcaveClosed (g := F u)
    · intro u x
      symm
      simpa [concaveBifunctionPairing, bifunctionPairingNotation] using
        helperForCorollary33_1_2_biconjugate_eq_functionConcaveClosure_of_concave
          (g := F u) (hConc := hConcSections u) (hNoTop := fun y => hNoTop u y) x
  · intro K hK hNoTopBot
    simp
    have hPairEq :
        ∀ u xStar,
          concaveBifunctionPairing (fun u x => concaveConjugate (K u) x) u xStar =
            concaveClosureInSecond K u xStar := by
      intro u xStar
      simpa [concaveBifunctionPairing, bifunctionPairingNotation,
        concaveClosureInSecond, functionConcaveClosure] using
        helperForCorollary33_1_2_biconjugate_eq_functionConcaveClosure_of_concave
          (g := K u) (hConc := hK.2 u (by simp)) (hNoTop := fun y => hNoTopBot.2 u y) xStar
    rcases (coordinatewise_closures_preserve_saddle_orientations_of_noBot
        (m := m) (n := n) (K := K) hNoTopBot.1).2 hK with
      ⟨_, hShapeSecond, _, _⟩
    refine ⟨?_, ?_, hPairEq⟩
    · refine ⟨?_, ?_⟩
      · intro u
        simpa using
          helperForCorollary33_1_2_concaveConjugate_isERealConcaveOn (g := K u)
      · intro xStar
        have hConvSlice :
            IsERealConvexOn (Set.univ : Set (Fin m → ℝ))
              (fun u => concaveClosureInSecond K u xStar) :=
          hShapeSecond.1 xStar (by simp)
        have hPairEqFun :
            (fun u => concaveBifunctionPairing (fun u x => concaveConjugate (K u) x) u xStar) =
              fun u => concaveClosureInSecond K u xStar := by
          funext u
          exact hPairEq u xStar
        simpa [hPairEqFun] using hConvSlice
    · intro u
      simpa using
        helperForCorollary33_1_2_concaveConjugate_isFunctionConcaveClosed (g := K u)

/-- Definition33.0.17: An image-closed bifunction is a convex bifunction whose every section
`F u` is convex-closed, or a concave bifunction whose every section `F u` is
concave-closed. In particular, a closed bifunction is image-closed. -/
def IsImageClosedBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  (IsRockafellarSectionwiseConvexBifunction F ∧ ∀ u, IsFunctionConvexClosed (F u)) ∨
    (IsConcaveBifunction F ∧ ∀ u, IsFunctionConcaveClosed (F u))

/-- An image-closed convex bifunction is a Rockafellar convex bifunction whose sections
are convex-closed and which takes values in `ℝ ∪ {+∞}` (modeled by excluding `⊥`). -/
def IsImageClosedConvexBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsRockafellarConvexBifunction F ∧
    HasNoBotValuesBifunction F ∧
    ∀ u, IsFunctionConvexClosed (F u)

/-- A convex-closed concave-convex kernel is a concave-convex bifunction that is
convex-closed in the second variable and takes values in `ℝ ∪ {+∞}` (hence has no `⊥`
values). -/
def IsConvexClosedConcaveConvexKernel {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
    IsConvexClosedInSecond K ∧
    HasNoBotValuesBifunction K

/-- An image-closed concave bifunction is a Rockafellar concave bifunction whose sections
are concave-closed and which takes values in `ℝ ∪ {-∞}` (modeled by excluding `⊤`). -/
def IsImageClosedConcaveBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsRockafellarConcaveBifunction F ∧
    HasNoTopValuesBifunction F ∧
    ∀ u, IsFunctionConcaveClosed (F u)

/-- A concave-closed convex-concave kernel is a convex-concave bifunction that is
concave-closed in the second variable and takes values in `ℝ ∪ {-∞}` (hence has no `⊤`
values). -/
def IsConcaveClosedConvexConcaveKernel {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
    IsConcaveClosedInSecond K ∧
    HasNoTopValuesBifunction K

/-- Helper for Lemma33.0.18: a convex-closed section agrees pointwise with its convex
closure. -/
lemma helperForLemma33_0_18_functionConvexClosure_eq_self
    {n : ℕ} {f : (Fin n → ℝ) → EReal} (h : IsFunctionConvexClosed f) :
    ∀ x, functionConvexClosure f x = f x := by
  intro x
  -- Unfold the fixed-point identity and evaluate it at the chosen point.
  unfold IsFunctionConvexClosed at h
  have hSymm : functionConvexClosure f = f := h.symm
  exact congrArg (fun g => g x) hSymm

/-- Helper for Lemma33.0.18: a kernel convex-closed in the second variable agrees pointwise
with its second-variable convex closure. -/
lemma helperForLemma33_0_18_convexClosureInSecond_eq_self
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (h : IsConvexClosedInSecond K) :
    ∀ u xStar, convexClosureInSecond K u xStar = K u xStar := by
  intro u xStar
  -- Unfold the fixed-point identity and evaluate it at the chosen pair `(u, xStar)`.
  unfold IsConvexClosedInSecond at h
  have hSymm : convexClosureInSecond K = K := h.symm
  exact congrArg (fun G => G u xStar) hSymm

-- Proof sketch: combine the two directions of `convexBifunction_pairing_correspondence`.
-- For an image-closed convex bifunction, the sectionwise closedness hypothesis identifies
-- `functionConvexClosure (F u)` with `F u`, so the forward direction gives the exact
-- reconstruction formula from the pairing. Conversely, if `K` is concave-convex and
-- convex-closed in the second variable, Theorem33.1 reconstructs `F` by partial convex
-- conjugation and the closure hypothesis turns `convexClosureInSecond K` back into `K`.
/-- Lemma33.0.18: On the convex side of Definition33.0.17, Theorem33.1 yields a one-to-one
correspondence between image-closed Rockafellar convex bifunctions and concave-convex
kernels that are convex-closed in the second variable. -/
theorem convexImageClosedBifunction_pairing_correspondence
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
      (∀ u, IsFunctionConvexClosed (F u)) →
      HasNoBotValuesBifunction F →
        IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
            (convexBifunctionPairing F) ∧
          IsConvexClosedInSecond (convexBifunctionPairing F) ∧
          ∀ u x,
            F u x = convexConjugate (convexBifunctionPairing F u) x) ∧
      (∀ K : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
        IsConvexClosedInSecond K →
        HasNoTopOrBotValuesBifunction K →
          let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
            fun u x => convexConjugate (K u) x
          IsRockafellarConvexBifunction F ∧
            (∀ u, IsFunctionConvexClosed (F u)) ∧
            ∀ u xStar,
              convexBifunctionPairing F u xStar = K u xStar) := by
  constructor
  · intro F hRock hSectionClosed hNoBot
    -- Apply the forward direction of Theorem33.1, which reconstructs `F u` from the pairing
    -- up to the sectionwise convex closure.
    have hForward :=
      (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hRock hNoBot
    refine ⟨hForward.1, hForward.2.1, ?_⟩
    intro u x
    -- Use image-closedness of each section to identify `functionConvexClosure (F u)` with
    -- `F u`, then chain equalities.
    have hClosurePoint :
        functionConvexClosure (F u) x = F u x :=
      helperForLemma33_0_18_functionConvexClosure_eq_self (f := F u) (hSectionClosed u) x
    exact hClosurePoint.symm.trans (hForward.2.2 u x)
  · intro K hConcConv hClosed hNoTopBot
    -- Reduce the `let F := ...` binder in the goal so we can work with the explicit
    -- reconstructed bifunction `F u x = (K u)^*(x)`.
    simp
    -- Apply the reverse direction of Theorem33.1, which identifies the pairing with
    -- `convexClosureInSecond K`.
    have hReverse :=
      (convexBifunction_pairing_correspondence (m := m) (n := n)).2 K hConcConv hNoTopBot
    have hReverse' :
        IsRockafellarConvexBifunction (fun u x => convexConjugate (K u) x) ∧
          (∀ u, IsFunctionConvexClosed (fun x => convexConjugate (K u) x)) ∧
          ∀ u xStar,
            convexBifunctionPairing (fun u x => convexConjugate (K u) x) u xStar =
              convexClosureInSecond K u xStar := by
      -- `simp` eliminates the `let`-binder present in Theorem33.1's reverse direction.
      simpa using hReverse
    refine ⟨hReverse'.1, hReverse'.2.1, ?_⟩
    intro u xStar
    -- Finally, use convex-closedness of `K` in the second variable to remove the closure.
    have hClosurePoint :
        convexClosureInSecond K u xStar = K u xStar :=
      helperForLemma33_0_18_convexClosureInSecond_eq_self (K := K) hClosed u xStar
    exact (hReverse'.2.2 u xStar).trans hClosurePoint

-- Proof sketch: package the four classes appearing in the corollary using the local
-- image-closed and coordinatewise-closed predicates. The forward directions send a
-- bifunction to its conjugate pairing and use the branchwise closedness to identify the
-- biconjugate with the original sections. The reverse directions reconstruct a bifunction
-- from a kernel by partial conjugation and then use the closure hypothesis on the kernel
-- to recover the original pairing.
/-- Helper for Lemma33.0.18: a concave-closed section agrees pointwise with its concave
closure. -/
lemma helperForLemma33_0_18_functionConcaveClosure_eq_self
    {n : ℕ} {f : (Fin n → ℝ) → EReal} (h : IsFunctionConcaveClosed f) :
    ∀ x, functionConcaveClosure f x = f x := by
  intro x
  unfold IsFunctionConcaveClosed at h
  have hSymm : functionConcaveClosure f = f := h.symm
  exact congrArg (fun g => g x) hSymm

/-- Helper for Lemma33.0.18: a kernel concave-closed in the second variable agrees pointwise
with its second-variable concave closure. -/
lemma helperForLemma33_0_18_concaveClosureInSecond_eq_self
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (h : IsConcaveClosedInSecond K) :
    ∀ u xStar, concaveClosureInSecond K u xStar = K u xStar := by
  intro u xStar
  unfold IsConcaveClosedInSecond at h
  have hSymm : concaveClosureInSecond K = K := h.symm
  exact congrArg (fun G => G u xStar) hSymm

-- Proof sketch: this is the concave analogue of
-- `convexImageClosedBifunction_pairing_correspondence`, using the freshly proved
-- `concaveBifunction_pairing_correspondence` and then removing the second-variable concave
-- closure with the kernel closedness hypothesis.
/-- Lemma33.0.18, concave side: image-closed Rockafellar concave bifunctions correspond to
convex-concave kernels that are concave-closed in the second variable. -/
theorem concaveImageClosedBifunction_pairing_correspondence
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConcaveBifunction F →
      (∀ u, IsFunctionConcaveClosed (F u)) →
      HasNoTopValuesBifunction F →
        IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
            (concaveBifunctionPairing F) ∧
          IsConcaveClosedInSecond (concaveBifunctionPairing F) ∧
          ∀ u x,
            F u x = concaveConjugate (concaveBifunctionPairing F u) x) ∧
      (∀ K : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
        IsConcaveClosedInSecond K →
        HasNoTopOrBotValuesBifunction K →
          let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
            fun u x => concaveConjugate (K u) x
          IsRockafellarConcaveBifunction F ∧
            (∀ u, IsFunctionConcaveClosed (F u)) ∧
            ∀ u xStar,
              concaveBifunctionPairing F u xStar = K u xStar) := by
  constructor
  · intro F hRock hSectionClosed hNoTop
    have hForward :=
      (concaveBifunction_pairing_correspondence (m := m) (n := n)).1 F hRock hNoTop
    refine ⟨hForward.1, hForward.2.1, ?_⟩
    intro u x
    have hClosurePoint :
        functionConcaveClosure (F u) x = F u x :=
      helperForLemma33_0_18_functionConcaveClosure_eq_self (f := F u) (hSectionClosed u) x
    exact hClosurePoint.symm.trans (hForward.2.2 u x)
  · intro K hConvConc hClosed hNoTopBot
    simp
    have hReverse :
        IsRockafellarConcaveBifunction (fun u x => concaveConjugate (K u) x) ∧
          (∀ u, IsFunctionConcaveClosed (fun x => concaveConjugate (K u) x)) ∧
          ∀ u xStar,
            concaveBifunctionPairing (fun u x => concaveConjugate (K u) x) u xStar = K u xStar := by
      have hPairEq :
          ∀ u xStar,
            concaveBifunctionPairing (fun u x => concaveConjugate (K u) x) u xStar =
              concaveClosureInSecond K u xStar := by
        intro u xStar
        simpa [concaveBifunctionPairing, bifunctionPairingNotation,
          concaveClosureInSecond, functionConcaveClosure] using
          helperForCorollary33_1_2_biconjugate_eq_functionConcaveClosure_of_concave
            (g := K u) (hConc := hConvConc.2 u (by simp)) (hNoTop := fun y => hNoTopBot.2 u y) xStar
      rcases (coordinatewise_closures_preserve_saddle_orientations_of_noBot
          (m := m) (n := n) (K := K) hNoTopBot.1).2 hConvConc with
        ⟨_, hShapeSecond, _, _⟩
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro u
          simpa using
            helperForCorollary33_1_2_concaveConjugate_isERealConcaveOn (g := K u)
        · intro xStar
          have hConvSlice :
              IsERealConvexOn (Set.univ : Set (Fin m → ℝ))
                (fun u => concaveClosureInSecond K u xStar) :=
            hShapeSecond.1 xStar (by simp)
          have hPairEqFun :
              (fun u => concaveBifunctionPairing (fun u x => concaveConjugate (K u) x) u xStar) =
                fun u => concaveClosureInSecond K u xStar := by
            funext u
            exact hPairEq u xStar
          simpa [hPairEqFun] using hConvSlice
      · intro u
        simpa using
          helperForCorollary33_1_2_concaveConjugate_isFunctionConcaveClosed (g := K u)
      · intro u xStar
        exact (hPairEq u xStar).trans
          (helperForLemma33_0_18_concaveClosureInSecond_eq_self (K := K) hClosed u xStar)
    simpa using hReverse

/-- Corollary33.1.2: The relations `K(u, x^*) = ⟪F u, x^*⟫` and `F u = K(u, ·)^*`
express a one-to-one correspondence between convex-closed concave-convex kernels `K`
on `ℝ^m × ℝ^n` and image-closed convex bifunctions `F : ℝ^m → (ℝ^n → EReal)`.
Similarly, the concave pairing gives a one-to-one correspondence between
concave-closed convex-concave kernels and image-closed concave bifunctions.
Here the image-closed and closed-kernel classes are interpreted in the local
extended-real formalization, including the one-sided admissibility hypotheses
excluding `⊥` on the convex side and excluding `⊤` on the concave side. -/
theorem closedSaddleFunctions_imageClosedBifunctions_correspondence
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsImageClosedConvexBifunction F →
        IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
            (convexBifunctionPairing F) ∧
          IsConvexClosedInSecond (convexBifunctionPairing F) ∧
          ∀ u x,
            convexConjugate (convexBifunctionPairing F u) x = F u x) ∧
      (∀ K : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
        IsConvexClosedInSecond K →
        HasNoTopOrBotValuesBifunction K →
          let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
            fun u x => convexConjugate (K u) x
          IsImageClosedConvexBifunction F ∧
            (∀ u x,
              F u x = convexConjugate (K u) x) ∧
            ∀ u xStar,
              convexBifunctionPairing F u xStar = K u xStar) ∧
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsImageClosedConcaveBifunction F →
        IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
            (concaveBifunctionPairing F) ∧
          IsConcaveClosedInSecond (concaveBifunctionPairing F) ∧
          ∀ u x,
            concaveConjugate (concaveBifunctionPairing F u) x = F u x) ∧
      (∀ K : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
        IsConcaveClosedInSecond K →
        HasNoTopOrBotValuesBifunction K →
          let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
            fun u x => concaveConjugate (K u) x
          IsImageClosedConcaveBifunction F ∧
            (∀ u x,
              F u x = concaveConjugate (K u) x) ∧
            ∀ u xStar,
              concaveBifunctionPairing F u xStar = K u xStar) := by
  constructor
  · intro F hImageClosed
    rcases hImageClosed with ⟨hRock, hNoBot, hSectionClosed⟩
    rcases
        (convexImageClosedBifunction_pairing_correspondence (m := m) (n := n)).1
          F hRock hSectionClosed hNoBot with
      ⟨hShape, hClosed, hRecover⟩
    refine ⟨hShape, hClosed, ?_⟩
    intro u x
    exact (hRecover u x).symm
  · constructor
    · intro K hConcConv hClosed hNoTopBot
      rcases
          (convexImageClosedBifunction_pairing_correspondence (m := m) (n := n)).2
            K hConcConv hClosed hNoTopBot with
        ⟨hRock, hSectionClosed, hPairing⟩
      have hNoBotF :
          HasNoBotValuesBifunction (fun u x => convexConjugate (K u) x) := by
        intro u x
        exact
          helperForTheorem33_1_convexConjugate_ne_bot_of_point
            (f := K u) (x₀ := x) (hNoTopBot.2 u x) x
      refine ⟨⟨hRock, hNoBotF, hSectionClosed⟩, ?_, hPairing⟩
      intro u x
      rfl
    · constructor
      · intro F hImageClosed
        rcases hImageClosed with ⟨hRock, hNoTop, hSectionClosed⟩
        rcases
            (concaveImageClosedBifunction_pairing_correspondence (m := m) (n := n)).1
              F hRock hSectionClosed hNoTop with
          ⟨hShape, hClosed, hRecover⟩
        refine ⟨hShape, hClosed, ?_⟩
        intro u x
        exact (hRecover u x).symm
      · intro K hConvConc hClosed hNoTopBot
        rcases
            (concaveImageClosedBifunction_pairing_correspondence (m := m) (n := n)).2
              K hConvConc hClosed hNoTopBot with
          ⟨hRock, hSectionClosed, hPairing⟩
        have hNoTopF :
            HasNoTopValuesBifunction (fun u x => concaveConjugate (K u) x) := by
          intro u x
          have hNoBotConj :
              convexConjugate (fun y => -K u y) (-x) ≠ (⊥ : EReal) := by
            exact
              helperForTheorem33_1_convexConjugate_ne_bot_of_point
                (f := fun y => -K u y) (x₀ := x) (by simpa using hNoTopBot.1 u x) (-x)
          have hEq :
              concaveConjugate (K u) x = -convexConjugate (fun y => -K u y) (-x) := by
            simpa [convexConjugate] using
              helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
                (g := K u) (xStar := x)
          simpa [hEq] using hNoBotConj
        refine ⟨⟨hRock, hNoTopF, hSectionClosed⟩, ?_, hPairing⟩
        intro u x
        rfl

/-!
Helpers for `Corollary33.1.3` (polyhedral sections, polyhedrality under affine shear,
and reconstruction from the pairing).
-/

/-- Helper for Corollary33.1.3: dot products split over `Fin.append`. -/
lemma helperForCorollary33_1_3_dotProduct_append
    {m k : ℕ} (u : Fin m → ℝ) (v : Fin k → ℝ) (b : Fin (m + k) → ℝ) :
    dotProduct (Fin.append u v) b =
      dotProduct u (fun i => b (Fin.castAdd k i)) +
        dotProduct v (fun j => b (Fin.natAdd m j)) := by
  classical
  -- Split the dot product sum into the first `m` and last `k` coordinate blocks.
  simp [dotProduct, Fin.sum_univ_add, Fin.append, Fin.addCases, add_assoc, add_left_comm, add_comm,
    mul_add, add_mul]

/-- Helper for Corollary33.1.3: the `castSucc` coordinates of the packed epigraph embedding
recover the base point. -/
lemma helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_castSucc
    {n : ℕ} (x : Fin n → ℝ) (μ : ℝ) (j : Fin n) :
    (prodLinearEquiv_append (n := n) (x, μ)).ofLp (Fin.castSucc j) = x j := by
  -- This is the `castSucc` coordinate lemma from Theorem 19.2, rewritten to use `.ofLp`.
  simpa using
    (helperForTheorem_19_2_prodLinearEquivAppendCoord_castSucc (x0 := x) (μ0 := μ) (j0 := j)).symm

/-- Helper for Corollary33.1.3: the last coordinate of the packed epigraph embedding is the
appended scalar. -/
lemma helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_last
    {n : ℕ} (x : Fin n → ℝ) (μ : ℝ) :
    (prodLinearEquiv_append (n := n) (x, μ)).ofLp (Fin.last n) = μ := by
  -- This is the `last` coordinate lemma from Theorem 19.2, rewritten to use `.ofLp`.
  simpa using
    (helperForTheorem_19_2_prodLinearEquivAppendCoord_last (x0 := x) (μ0 := μ)).symm

/-- Helper for Corollary33.1.3: appending a fixed parameter block commutes with the packed
epigraph embedding (viewed in coordinates via `.ofLp`). -/
lemma helperForCorollary33_1_3_append_prodLinearEquivAppend_ofLp
    {m n : ℕ} (u : Fin m → ℝ) (x : Fin n → ℝ) (μ : ℝ) :
    Fin.append u ((prodLinearEquiv_append (n := n) (x, μ)).ofLp) =
      (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp := by
  funext i
  by_cases hi : i.1 < m
  · -- First block: reduce to a `castSucc` coordinate and use `Fin.append_left`.
    let i' : Fin m := ⟨i.1, hi⟩
    have hiCast : Fin.castAdd (n + 1) i' = i := by
      ext
      simp [i']
    rw [← hiCast]
    have hIndex :
        (Fin.castAdd (n + 1) i' : Fin (m + n + 1)) =
          Fin.castSucc (Fin.castAdd n i') := by
      ext
      simp
    -- Evaluate both sides by reducing to the shared value `u i'`.
    have hLeft :
        Fin.append u ((prodLinearEquiv_append (n := n) (x, μ)).ofLp)
            (Fin.castAdd (n + 1) i') = u i' := by
      simp [Fin.append]
    have hRight :
        (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp
            (Fin.castAdd (n + 1) i') = u i' := by
      -- Convert the `castAdd` index to a `castSucc` index and apply the coordinate lemma.
      rw [hIndex]
      have hCast :=
        helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_castSucc
          (x := Fin.append u x) (μ := μ) (j := Fin.castAdd n i')
      -- The recovered base coordinate is in the `u` block.
      simpa [Fin.append] using hCast.trans (by simp [Fin.append])
    exact hLeft.trans hRight.symm
  · -- Second block: reduce to a `natAdd` index and split into `castSucc`/`last`.
    have hge : m ≤ i.1 := Nat.le_of_not_gt hi
    let j : Fin (n + 1) := ⟨i.1 - m, by
      have hlt : i.1 < m + (n + 1) := i.2
      omega⟩
    have hjNatAdd : Fin.natAdd m j = i := by
      ext
      simp [j]
      omega
    rw [← hjNatAdd]
    by_cases hjLast : j = Fin.last n
    · -- Last coordinate: both sides evaluate to `μ`.
      -- Rewrite to the canonical last index without eliminating the dependent `hjNatAdd`.
      have hj : j = Fin.last n := hjLast
      have hIndexLast :
          (Fin.natAdd m (Fin.last n) : Fin (m + (n + 1))) = Fin.last (m + n) := by
        ext
        simp
      -- Reduce both sides to `μ` using the `last` coordinate lemma.
      have hSmall :
          (prodLinearEquiv_append (n := n) (x, μ)).ofLp (Fin.last n) = μ :=
        helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_last (x := x) (μ := μ)
      have hBig :
          (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp (Fin.last (m + n)) = μ :=
        helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_last (x := Fin.append u x) (μ := μ)
      -- `Fin.append` drops to the right block at a `natAdd` index. We compute both sides
      -- explicitly to avoid `simp` loops.
      calc
        Fin.append u ((prodLinearEquiv_append (n := n) (x, μ)).ofLp)
            (Fin.natAdd m j)
            = (prodLinearEquiv_append (n := n) (x, μ)).ofLp (Fin.last n) := by
              -- Right-block lookup of `Fin.append`.
              -- First rewrite `j` to the canonical `Fin.last` index.
              have :
                  Fin.append u ((prodLinearEquiv_append (n := n) (x, μ)).ofLp) (Fin.natAdd m j) =
                    Fin.append u ((prodLinearEquiv_append (n := n) (x, μ)).ofLp)
                      (Fin.natAdd m (Fin.last n)) := by
                    simpa [hj]
              -- Then use `Fin.append_right`.
              refine this.trans ?_
              simpa using
                (Fin.append_right (u := u)
                  (v := (prodLinearEquiv_append (n := n) (x, μ)).ofLp) (i := Fin.last n))
        _ = μ := hSmall
        _ = (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp (Fin.natAdd m j) := by
              -- Show the right side also equals `μ` (then take symmetry).
              have hVal :
                  (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp (Fin.natAdd m j) =
                    μ := by
                  calc
                    (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp (Fin.natAdd m j)
                        =
                        (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp
                          (Fin.natAdd m (Fin.last n)) := by
                            simpa [hj]
                    _ =
                        (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp
                          (Fin.last (m + n)) := by
                            simpa [hIndexLast]
                    _ = μ := hBig
              exact hVal.symm
    · -- Cast-succ coordinate: use `Fin.eq_castSucc_of_ne_last`.
      rcases Fin.eq_castSucc_of_ne_last (n := n) (x := j) hjLast with ⟨j0, hj0⟩
      -- Rewrite `j` so the coordinate lemmas apply at `castSucc`.
      rw [← hj0]
      have hIndexCastSucc :
          (Fin.natAdd m (Fin.castSucc j0) : Fin (m + (n + 1))) =
            Fin.castSucc (Fin.natAdd m j0) := by
        ext
        simp
      -- Left side: drop to the right block, then use the `castSucc` coordinate lemma.
      have hSmall :
          (prodLinearEquiv_append (n := n) (x, μ)).ofLp (Fin.castSucc j0) = x j0 :=
        helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_castSucc (x := x) (μ := μ) (j := j0)
      -- Right side: convert the index to `castSucc` and use the coordinate lemma in the big space.
      have hBig :
          (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp
              (Fin.castSucc (Fin.natAdd m j0)) =
            (Fin.append u x) (Fin.natAdd m j0) :=
        helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_castSucc
          (x := Fin.append u x) (μ := μ) (j := Fin.natAdd m j0)
      -- Finish by computing both sides explicitly to avoid `simp` recursion.
      calc
        Fin.append u ((prodLinearEquiv_append (n := n) (x, μ)).ofLp)
            (Fin.natAdd m (Fin.castSucc j0))
            = (prodLinearEquiv_append (n := n) (x, μ)).ofLp (Fin.castSucc j0) := by
              simpa using
                (Fin.append_right (u := u)
                  (v := (prodLinearEquiv_append (n := n) (x, μ)).ofLp) (i := Fin.castSucc j0))
        _ = x j0 := hSmall
        _ = (Fin.append u x) (Fin.natAdd m j0) := by
              -- `Fin.append` on the right block reduces to `x`.
              simpa using
                (Fin.append_right (u := u) (v := x) (i := j0)).symm
        _ = (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp
              (Fin.castSucc (Fin.natAdd m j0)) := by
              exact hBig.symm
        _ = (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp
              (Fin.natAdd m (Fin.castSucc j0)) := by
              -- Rewrite the index using `hIndexCastSucc` without triggering `simp` loops.
              simpa using
                congrArg
                  (fun t =>
                    (prodLinearEquiv_append (n := m + n) (Fin.append u x, μ)).ofLp t)
                  hIndexCastSucc.symm

end Section33
end Chap07

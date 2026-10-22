/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part5

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Theorem 37.2: a concave `EReal` section becomes convex after negation once the
original section is known to avoid `⊤`. -/
lemma helperForTheorem_37_2_concaveNegation_isConvex_of_noTop
    {k : ℕ} {f : (Fin k → ℝ) → EReal}
    (hConc : IsERealConcaveOn (Set.univ : Set (Fin k → ℝ)) f)
    (hNoTop : ∀ x, f x ≠ ⊤) :
    IsERealConvexOn (Set.univ : Set (Fin k → ℝ)) (fun x => -f x) := by
  intro x y hx hy a b ha hb hab hxy
  -- Negate the Jensen inequality for `f` after first ruling out the `⊤` branches that would
  -- break `EReal.neg_add`.
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
    -- With the `⊤` branches removed, negation distributes across the weighted sum exactly.
    have hNegAdd :=
      EReal.neg_add (x := (a : EReal) * f x) (y := (b : EReal) * f y)
        (Or.inr hTerm2_ne_top) (Or.inl hTerm1_ne_top)
    simpa [sub_eq_add_neg, mul_neg, neg_mul, add_comm] using hNegAdd
  calc
    -f (a • x + b • y) ≤ -((a : EReal) * f x + (b : EReal) * f y) := hNegJensen
    _ = (a : EReal) * (-f x) + (b : EReal) * (-f y) := hNegWeighted

/-- Helper for Corollary 37.2.1: the raw outside-domain inverse model `u ↦ -K(u,v)` need not be
globally convex, so the remaining inverse-slice branch cannot be closed by a blanket negation
transport. -/
lemma helperForCorollary_37_2_1_not_convex_of_bot_top_top_sample
    {f : (Fin 1 → ℝ) → EReal}
    {x y z : Fin 1 → ℝ}
    (hx : f x = (⊥ : EReal))
    (hy : f y = (⊤ : EReal))
    (hz : f z = (⊤ : EReal))
    (hzCombo : ((1 / 3 : ℝ) • x + (2 / 3 : ℝ) • y) = z) :
    ¬ IsERealConvexOn (Set.univ : Set (Fin 1 → ℝ)) f := by
  intro hConv
  have hIneq :=
    hConv (x := x) (y := y) (by simp) (by simp)
      (a := (1 / 3 : ℝ)) (b := (2 / 3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by simp)
  -- This sample chooses one `⊥` endpoint and one `⊤` endpoint whose convex combination still
  -- lands in the `⊤` region, forcing the impossible inequality `⊤ ≤ ⊥`.
  rw [hzCombo, hz, hx, hy] at hIneq
  have hMulBot : (((1 / 3 : ℝ) : EReal) * (⊥ : EReal)) = (⊥ : EReal) := by
    exact EReal.coe_mul_bot_of_pos (by norm_num)
  have hMulTop : (((2 / 3 : ℝ) : EReal) * (⊤ : EReal)) = (⊤ : EReal) := by
    exact EReal.coe_mul_top_of_pos (by norm_num)
  have hEq : (((1 / 3 : ℝ) : EReal) * (⊥ : EReal) + (⊤ : EReal)) = (⊤ : EReal) := by
    simpa [hMulTop] using hIneq
  have hEqBot : (((1 / 3 : ℝ) : EReal) * (⊥ : EReal) + (⊤ : EReal)) = (⊥ : EReal) := by
    calc
      (((1 / 3 : ℝ) : EReal) * (⊥ : EReal) + (⊤ : EReal))
          = (⊥ : EReal) + (⊤ : EReal) := by rw [hMulBot]
      _ = (⊥ : EReal) := by simp
  have hTopEqBot : (⊤ : EReal) = (⊥ : EReal) := by
    calc
      (⊤ : EReal) = (((1 / 3 : ℝ) : EReal) * (⊥ : EReal) + (⊤ : EReal)) := hEq.symm
      _ = (⊥ : EReal) := hEqBot
  have hContra : False := by
    simp at hTopEqBot
  exact hContra

/-- Helper for Corollary 37.2.1: the raw outside-domain inverse model `u ↦ -K(u,v)` need not be
globally convex, so the remaining inverse-slice branch cannot be closed by a blanket negation
transport. -/
lemma helperForCorollary_37_2_1_halfspace_bot_top_not_convex :
    ¬ IsERealConvexOn (Set.univ : Set (Fin 1 → ℝ))
      (fun u : Fin 1 → ℝ => if 0 ≤ u 0 then (⊥ : EReal) else (⊤ : EReal)) := by
  let f : (Fin 1 → ℝ) → EReal := fun u => if 0 ≤ u 0 then (⊥ : EReal) else (⊤ : EReal)
  let x : Fin 1 → ℝ := ![1]
  let y : Fin 1 → ℝ := ![-3]
  let z : Fin 1 → ℝ := ![-5 / 3]
  have hxVal : f x = (⊥ : EReal) := by
    simp [f, x]
  have hyVal : f y = (⊤ : EReal) := by
    simp [f, y]
  have hzVal : f z = (⊤ : EReal) := by
    norm_num [f, z]
  have hz : ((1 / 3 : ℝ) • x + (2 / 3 : ℝ) • y) = z := by
    ext i
    fin_cases i
    norm_num [x, y, z]
  -- The explicit halfspace model is a concrete instance of the generic `⊥/⊤/⊤` obstruction.
  exact helperForCorollary_37_2_1_not_convex_of_bot_top_top_sample
    (f := f) (x := x) (y := y) (z := z) hxVal hyVal hzVal hz

/-- Explicit regularity data for Theorem 37.2.  The no-`⊤` field is exactly what makes the
swap-negation a concave-convex saddle function.  The two Section 34 and boundary-generation
fields support the second-dual formula for `K` and, separately, for its inverse. -/
structure Section37Theorem37_2Qualification (K : SaddleFunction m n) : Prop where
  noTop : HasNoTopValuesBifunction K
  primalGlobal : Section34Theorem34_2GlobalQualification m n
  primalBoundary : Section37SecondDualBoundaryGeneration K
  inverseGlobal : Section34Theorem34_2GlobalQualification n m
  inverseBoundary : Section37SecondDualBoundaryGeneration (bifunctionInverse K)

/-- Helper for Theorem 37.2: swapping variables and negating preserves the concave-convex
orientation when the original saddle function avoids `⊤`. -/
lemma helperForTheorem_37_2_inverseConcaveConvex
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (_hKproper : IsProperSaddleFunction K)
    (hKNoTop : HasNoTopValuesBifunction K) :
    IsConcaveConvex (bifunctionInverse K) := by
  have hKOrient : IsConcaveConvex K := hKclosed.1.1
  constructor
  · intro u _hu
    simpa [bifunctionInverse] using
      (helperForLemma33_0_5_convexNegation_isConcave
        (hKOrient.2 u (by simp)))
  · intro x _hx
    simpa [bifunctionInverse] using
      (helperForCorollary33_1_2_concaveNegation_isConvex_of_noTop
        (hKOrient.1 x (by simp)) (fun u => hKNoTop u x))

/-- Helper for Theorem 37.2: the first partial closure of the inverse saddle-function is the
inverse of the second partial closure of the original saddle-function. -/
lemma helperForTheorem_37_2_inversePartialClosureFirst_eq_inversePartialClosureSecond
    (K : SaddleFunction m n) :
    partialClosure₁ (bifunctionInverse K) = bifunctionInverse (partialClosure₂ K) := by
  funext x u
  -- Expand both partial closures and commute negation with the indexed infimum/supremum.
  unfold partialClosure₁ partialClosure₂ concaveClosureInFirst convexClosureInSecond bifunctionInverse
  calc
    (⨅ ε : {ε : ℝ // 0 < ε},
        ⨆ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, -K u w.1)
        = (⨅ ε : {ε : ℝ // 0 < ε},
            -(⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, K u w.1)) := by
              refine iInf_congr ?_
              intro ε
              simpa [eq_comm] using
                (helperForLemma33_0_5_neg_iInf_neg_eq_iSup
                  (f := fun w : {w : Fin n → ℝ // ‖w - x‖ < ε.1} => -K u w.1))
    _ = -(⨆ ε : {ε : ℝ // 0 < ε},
            ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, K u w.1) := by
          -- The outer indexed infimum behaves the same way after another negation commute.
          simpa [eq_comm] using
            (helperForLemma33_0_5_neg_iSup_neg_eq_iInf
              (f := fun ε : {ε : ℝ // 0 < ε} =>
                -(⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, K u w.1))).symm

/-- Helper for Theorem 37.2: the second partial closure of the inverse saddle-function is the
inverse of the first partial closure of the original saddle-function. -/
lemma helperForTheorem_37_2_inversePartialClosureSecond_eq_inversePartialClosureFirst
    (K : SaddleFunction m n) :
    partialClosure₂ (bifunctionInverse K) = bifunctionInverse (partialClosure₁ K) := by
  funext x u
  -- The second partial closure of the inverse is the negated first partial closure of `K`.
  unfold partialClosure₁ partialClosure₂ convexClosureInSecond concaveClosureInFirst bifunctionInverse
  calc
    (⨆ ε : {ε : ℝ // 0 < ε},
        ⨅ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, -K w.1 x)
        = (⨆ ε : {ε : ℝ // 0 < ε},
            -(⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x)) := by
              refine iSup_congr ?_
              intro ε
              simpa [eq_comm] using
                (helperForLemma33_0_5_neg_iSup_neg_eq_iInf
                  (f := fun w : {w : Fin m → ℝ // ‖w - u‖ < ε.1} => -K w.1 x)).symm
    _ = -(⨅ ε : {ε : ℝ // 0 < ε},
            ⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x) := by
          -- Negation also exchanges the outer indexed supremum and infimum.
          simpa [eq_comm] using
            (helperForLemma33_0_5_neg_iInf_neg_eq_iSup
              (f := fun ε : {ε : ℝ // 0 < ε} =>
                -(⨆ w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}, K w.1 x)))

/-- Helper for Theorem 37.2: closedness is preserved by the inverse saddle transform. -/
lemma helperForTheorem_37_2_inverseClosed
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hKNoTop : HasNoTopValuesBifunction K) :
    IsClosedSaddleFunction (bifunctionInverse K) := by
  have hKclosed' := hKclosed
  rcases hKclosed with ⟨hFirstClosed, hSecondClosed⟩
  have hInverseOrient : IsConcaveConvex (bifunctionInverse K) :=
    helperForTheorem_37_2_inverseConcaveConvex (K := K) hKclosed' hKproper hKNoTop
  have hInverseNoBot : HasNoBotValuesBifunction (bifunctionInverse K) := by
    intro x u
    simpa [bifunctionInverse, EReal.neg_eq_bot_iff] using hKNoTop u x
  have hInverseClosureData :=
    helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
      (K := bifunctionInverse K) (by simpa [IsConcaveConvex] using hInverseOrient)
      hInverseNoBot
  constructor
  · rcases hSecondClosed with ⟨hKcc, hCl2cc, hFirstEq, hSecondEq⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The inverse of the original saddle-function keeps the concave-convex orientation.
      exact hInverseOrient
    · -- The first inverse closure remains concave-convex by the coordinatewise-closure theorem.
      simpa [IsConcaveConvex, partialClosure₁] using hInverseClosureData.1
    · -- One application of `cl₁` already fixes the first inverse closure.
      exact
        (helperForText_34_0_1_partialClosure₁_idempotent
          (K := bifunctionInverse K) hInverseOrient).symm
    · -- The mixed fixed-point identity for `K ∼ cl₂ K` transports to the second partial closure
      -- of the inverse.
      calc
        partialClosure₂ (bifunctionInverse K)
            = bifunctionInverse (partialClosure₁ K) :=
              helperForTheorem_37_2_inversePartialClosureSecond_eq_inversePartialClosureFirst
                (K := K)
        _ = bifunctionInverse (partialClosure₁ (partialClosure₂ K)) := by
              rw [hFirstEq]
        _ = partialClosure₂ (bifunctionInverse (partialClosure₂ K)) := by
              symm
              exact
                helperForTheorem_37_2_inversePartialClosureSecond_eq_inversePartialClosureFirst
                  (K := partialClosure₂ K)
        _ = partialClosure₂ (partialClosure₁ (bifunctionInverse K)) := by
              rw [helperForTheorem_37_2_inversePartialClosureFirst_eq_inversePartialClosureSecond]
  · rcases hFirstClosed with ⟨hKcc, hCl1cc, hFirstEq, hSecondEq⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- The inverse keeps the original orientation on the first representative as well.
      exact hInverseOrient
    · -- The second inverse closure remains concave-convex by the coordinatewise-closure theorem.
      simpa [IsConcaveConvex, partialClosure₂] using hInverseClosureData.2.1
    · -- Transport the mixed fixed-point identity from `K ∼ cl₁ K` to the first closure of the
      -- inverse second representative.
      calc
        partialClosure₁ (bifunctionInverse K)
            = bifunctionInverse (partialClosure₂ K) :=
              helperForTheorem_37_2_inversePartialClosureFirst_eq_inversePartialClosureSecond
                (K := K)
        _ = bifunctionInverse (partialClosure₂ (partialClosure₁ K)) := by
              rw [hSecondEq]
        _ = partialClosure₁ (bifunctionInverse (partialClosure₁ K)) := by
              symm
              exact
                helperForTheorem_37_2_inversePartialClosureFirst_eq_inversePartialClosureSecond
                  (K := partialClosure₁ K)
        _ = partialClosure₁ (partialClosure₂ (bifunctionInverse K)) := by
              rw [helperForTheorem_37_2_inversePartialClosureSecond_eq_inversePartialClosureFirst]
    · -- One application of `cl₂` already fixes the second inverse closure.
      exact
        (helperForText_34_0_1_partialClosure₂_idempotent
          (K := bifunctionInverse K) hInverseOrient).symm

/-- Helper for Theorem 37.2: saddle-equivalence is stable under the inverse saddle transform. -/
lemma helperForTheorem_37_2_inverseSaddleEquivalent
    {K L : SaddleFunction m n}
    (hKL : saddleEquivalent K L)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hKNoTop : HasNoTopValuesBifunction K)
    (hLclosed : IsClosedSaddleFunction L)
    (hLproper : IsProperSaddleFunction L)
    (hLNoTop : HasNoTopValuesBifunction L) :
    saddleEquivalent (bifunctionInverse K) (bifunctionInverse L) := by
  rcases hKL with ⟨hK, hL, hFirst, hSecond⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Swap-negation preserves the concave-convex orientation on the left representative.
    let _ := hK
    exact helperForTheorem_37_2_inverseConcaveConvex (K := K) hKclosed hKproper hKNoTop
  · -- The same orientation transport applies on the right representative.
    let _ := hL
    exact helperForTheorem_37_2_inverseConcaveConvex (K := L) hLclosed hLproper hLNoTop
  · -- Equality of original second partial closures becomes equality of inverse first ones.
    rw [helperForTheorem_37_2_inversePartialClosureFirst_eq_inversePartialClosureSecond,
      helperForTheorem_37_2_inversePartialClosureFirst_eq_inversePartialClosureSecond, hSecond]
  · -- Equality of original first partial closures becomes equality of inverse second ones.
    rw [helperForTheorem_37_2_inversePartialClosureSecond_eq_inversePartialClosureFirst,
      helperForTheorem_37_2_inversePartialClosureSecond_eq_inversePartialClosureFirst, hFirst]

/-- Helper for Theorem 37.2: in the inverse saddle function, the first effective domain is
exactly the second effective domain of the original saddle function. -/
lemma helperForTheorem_37_2_inverseFirstDomain_eq_originalSecondDomain
    (K : SaddleFunction m n) :
    effectiveDomain₁ (bifunctionInverse K) = effectiveDomain₂ K := by
  ext x
  constructor
  · intro hx u
    -- Rewriting the inverse turns the first-domain no-`⊥` condition into the original
    -- second-domain no-`⊤` condition.
    simpa [effectiveDomain₁, effectiveDomain₂, bifunctionInverse, bot_lt_iff_ne_bot,
      lt_top_iff_ne_top, EReal.neg_eq_bot_iff] using hx u
  · intro hx u
    -- The converse implication is the same pointwise sign rewrite read backwards.
    simpa [effectiveDomain₁, effectiveDomain₂, bifunctionInverse, bot_lt_iff_ne_bot,
      lt_top_iff_ne_top, EReal.neg_eq_bot_iff] using hx u

/-- Helper for Theorem 37.2: in the inverse saddle function, the second effective domain is
exactly the first effective domain of the original saddle function. -/
lemma helperForTheorem_37_2_inverseSecondDomain_eq_originalFirstDomain
    (K : SaddleFunction m n) :
    effectiveDomain₂ (bifunctionInverse K) = effectiveDomain₁ K := by
  ext u
  constructor
  · intro hu x
    -- Swapping the arguments and negating exchanges the inverse second-domain condition with the
    -- original first-domain condition.
    simpa [effectiveDomain₁, effectiveDomain₂, bifunctionInverse, bot_lt_iff_ne_bot,
      lt_top_iff_ne_top, EReal.neg_eq_top_iff] using hu x
  · intro hu x
    -- The same equivalence proves the reverse inclusion.
    simpa [effectiveDomain₁, effectiveDomain₂, bifunctionInverse, bot_lt_iff_ne_bot,
      lt_top_iff_ne_top, EReal.neg_eq_top_iff] using hu x

/-- Helper for Theorem 37.2: properness is preserved when passing to the inverse saddle
function. -/
lemma helperForTheorem_37_2_inverseProper
    (K : SaddleFunction m n)
    (hKproper : IsProperSaddleFunction K) :
    IsProperSaddleFunction (bifunctionInverse K) := by
  rcases Set.nonempty_iff_ne_empty.mpr hKproper with ⟨⟨u, v⟩, huv⟩
  refine Set.nonempty_iff_ne_empty.mp ?_
  refine ⟨⟨v, u⟩, ?_⟩
  -- A witness in `dom K = dom₁ K × dom₂ K` becomes a swapped witness in
  -- `dom (K_*) = dom₂ K × dom₁ K`.
  have hvInv : v ∈ effectiveDomain₁ (bifunctionInverse K) := by
    simpa [helperForTheorem_37_2_inverseFirstDomain_eq_originalSecondDomain] using
      (Set.mem_prod.mp huv).2
  have huInv : u ∈ effectiveDomain₂ (bifunctionInverse K) := by
    simpa [helperForTheorem_37_2_inverseSecondDomain_eq_originalFirstDomain] using
      (Set.mem_prod.mp huv).1
  exact Set.mem_prod.mpr ⟨hvInv, huInv⟩

/-- Helper for Theorem 37.2: the lower Section 37 conjugate of the inverse saddle-function is the
negative of the upper Section 37 conjugate of `K` after negating both dual variables. -/
lemma helperForTheorem_37_2_inverseLowerConjugate_pointwiseRewrite
    (K : SaddleFunction m n)
    (uStar : Fin n → ℝ)
    (x : Fin m → ℝ) :
    theorem37ValueSupInf (bifunctionInverse K) uStar x =
      -theorem37ValueInfSup K (-x) (-uStar) := by
  -- Rewrite the inverse maximin value into the two-layer negation identity before comparing it
  -- with the original minimax value at the sign-twisted pair `(-x, -uStar)`.
  unfold theorem37ValueSupInf theorem37ValueInfSup bifunctionInverse
  calc
    (⨆ v : Fin m → ℝ,
        ⨅ u : Fin n → ℝ,
          (((finDot u uStar + finDot x v : ℝ) : EReal) - -K v u))
        =
          (⨆ v : Fin m → ℝ,
            ⨅ u : Fin n → ℝ,
              (((finDot u uStar + finDot x v : ℝ) : EReal) + K v u)) := by
            refine iSup_congr ?_
            intro v
            refine iInf_congr ?_
            intro u
            simp [sub_eq_add_neg]
    _ =
          -(⨅ v : Fin m → ℝ,
              ⨆ u : Fin n → ℝ,
                -((((finDot u uStar + finDot x v : ℝ) : EReal) + K v u))) := by
            simpa using
              (helperForLemma33_0_5_negatedTwoLayerClosureIdentity
                (F := fun v : Fin m → ℝ => fun u : Fin n → ℝ =>
                  (((finDot u uStar + finDot x v : ℝ) : EReal) + K v u)))
    _ = -(⨅ v : Fin m → ℝ,
            ⨆ u : Fin n → ℝ,
              (((finDot v (-x) + finDot (-uStar) u : ℝ) : EReal) - K v u)) := by
          refine congrArg Neg.neg ?_
          refine iInf_congr ?_
          intro v
          refine iSup_congr ?_
          intro u
          -- Identify the affine coefficient after negating both dual variables.
          have hDot :
              (finDot v (-x) + finDot (-uStar) u : ℝ) =
                -(finDot u uStar + finDot x v) := by
            simp [helperForProposition_36_4_6_finDot_eq_dotProduct, dotProduct_comm, add_comm]
          have hsumTop : ((finDot x v : EReal) + (finDot u uStar : EReal)) ≠ ⊤ := by
            exact
              (EReal.add_ne_top_iff_ne_top₂ (x := (finDot x v : EReal))
                (y := (finDot u uStar : EReal)) (by simp) (by simp)).2 ⟨by simp, by simp⟩
          have hsumBot : ((finDot x v : EReal) + (finDot u uStar : EReal)) ≠ ⊥ := by
            simp
          have hNegAdd :=
            EReal.neg_add (x := K v u)
              (y := ((finDot x v : EReal) + (finDot u uStar : EReal)))
              (Or.inr hsumTop) (Or.inr hsumBot)
          have hSumNeg :=
            EReal.neg_add (x := (finDot x v : EReal)) (y := (finDot u uStar : EReal))
              (Or.inr (by simp)) (Or.inr (by simp))
          -- Split the outer negation across the bifunction term and the finite affine sum.
          simpa [sub_eq_add_neg, hDot, add_comm, add_left_comm, add_assoc] using
            (show -(K v u + ((finDot x v : EReal) + (finDot u uStar : EReal))) =
              -K v u + (-((finDot x v : EReal)) + -((finDot u uStar : EReal))) by
              calc
                -(K v u + ((finDot x v : EReal) + (finDot u uStar : EReal)))
                    = -K v u - ((finDot x v : EReal) + (finDot u uStar : EReal)) := hNegAdd
                _ = -K v u + (-((finDot x v : EReal)) + -((finDot u uStar : EReal))) := by
                      simp [sub_eq_add_neg, hSumNeg])
    _ = -theorem37ValueInfSup K (-x) (-uStar) := by
          rfl

/-- Helper for Theorem 37.2: the slice supremum appearing in the second-variable formula for the
inverse saddle function is exactly the negative of the first-variable `iInf` expression from the
textbook formula for `K`. -/
lemma helperForTheorem_37_2_inverseSliceSup_eq_negatedFirstDualInf
    (K : SaddleFunction m n)
    (z : Fin m → ℝ) :
    iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₁ (bifunctionInverse K))} =>
      iSup (fun u : {u // u ∈ effectiveDomain₂ (bifunctionInverse K)} =>
        bifunctionInverse K v.1 (u.1 + z) - bifunctionInverse K v.1 u.1)) =
      -iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
        iInf (fun u : {u // u ∈ effectiveDomain₁ K} =>
          K (u.1 + z) v.1 - K u.1 v.1)) := by
  -- Replace the inverse-domain index sets by the original ones before commuting negation through
  -- the two displayed suprema.
  rw [helperForTheorem_37_2_inverseFirstDomain_eq_originalSecondDomain,
    helperForTheorem_37_2_inverseSecondDomain_eq_originalFirstDomain]
  let V : Type := {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)}
  let U : Type := {u // u ∈ effectiveDomain₁ K}
  change iSup (fun v : V =>
      iSup (fun u : U => bifunctionInverse K v.1 (u.1 + z) - bifunctionInverse K v.1 u.1)) =
    -iInf (fun v : V =>
      iInf (fun u : U => K (u.1 + z) v.1 - K u.1 v.1))
  calc
    iSup (fun v : V =>
      iSup (fun u : U =>
        bifunctionInverse K v.1 (u.1 + z) - bifunctionInverse K v.1 u.1)) =
        iSup (fun v : V =>
          iSup (fun u : U =>
            -(K (u.1 + z) v.1 - K u.1 v.1))) := by
          refine iSup_congr ?_
          intro v
          refine iSup_congr ?_
          intro u
          -- Expanding the inverse turns each slice increment into the negative of the original
          -- first-variable increment.
          have hvDom : v.1 ∈ effectiveDomain₂ K :=
            intrinsicInterior_subset (𝕜 := ℝ) (s := effectiveDomain₂ K) v.2
          have huBot : K u.1 v.1 ≠ ⊥ := by
            simpa [bot_lt_iff_ne_bot] using u.2 v.1
          have huvTop : K (u.1 + z) v.1 ≠ ⊤ := by
            simpa [lt_top_iff_ne_top] using hvDom (u.1 + z)
          have hNegSub :
              -(K (u.1 + z) v.1 - K u.1 v.1) =
                -K (u.1 + z) v.1 + K u.1 v.1 :=
            EReal.neg_sub (x := K (u.1 + z) v.1) (y := K u.1 v.1)
              (Or.inr huBot) (Or.inl huvTop)
          calc
            bifunctionInverse K v.1 (u.1 + z) - bifunctionInverse K v.1 u.1
                = -K (u.1 + z) v.1 + K u.1 v.1 := by
                    simp [bifunctionInverse, sub_eq_add_neg, add_comm]
            _ = -(K (u.1 + z) v.1 - K u.1 v.1) := by
                  simpa [sub_eq_add_neg, add_comm] using hNegSub.symm
    _ =
        iSup (fun v : V =>
          -iInf (fun u : U =>
            K (u.1 + z) v.1 - K u.1 v.1)) := by
          refine iSup_congr ?_
          intro v
          -- For each fixed interior `v`, negation turns the `u`-supremum into the displayed
          -- `u`-infimum.
          simpa [eq_comm] using
            (helperForLemma33_0_5_neg_iInf_neg_eq_iSup
              (f := fun u : {u // u ∈ effectiveDomain₁ K} =>
                -(K (u.1 + z) v.1 - K u.1 v.1)))
    _ =
        -iInf (fun v : V =>
          iInf (fun u : U =>
            K (u.1 + z) v.1 - K u.1 v.1)) := by
          -- Applying the same negation transport to the outer supremum finishes the inverse slice
          -- rewrite.
          simpa [eq_comm] using
            (helperForLemma33_0_5_neg_iInf_neg_eq_iSup (f := fun v : V =>
              -(iInf (fun u : U => K (u.1 + z) v.1 - K u.1 v.1))))

/-- Helper for Theorem 37.2: the common dual second domain of the inverse saddle-function is
the negated preimage of the common dual first domain of the original saddle-function. -/
lemma helperForTheorem_37_2_inverseSecondDualDomain_eq_originalFirstDualDomain
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    effectiveDomain₂ (fun uStar x => theorem37ValueSupInf (bifunctionInverse K) uStar x) =
      Neg.neg ⁻¹' effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x) := by
  -- Compare the inverse common dual second domain with the original upper-conjugate first
  -- domain, then replace the latter by the canonical common first domain from Corollary 37.1.2.
  have hCanonical :=
    helperForTheorem_37_2_canonicalCommonEffectiveDomains
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal
  have hFirstDomainEq :
      effectiveDomain₁ (fun uStar x => theorem37ValueInfSup K uStar x) =
        effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x) :=
    hCanonical.2.2.2.2.1
  ext x
  constructor
  · intro hx
    have hxUpper :
        -x ∈ effectiveDomain₁ (fun uStar x => theorem37ValueInfSup K uStar x) := by
      intro uStar
      -- Evaluate the inverse-domain condition at `-uStar` and rewrite the inverse value.
      have hPoint := hx (-uStar)
      simpa [effectiveDomain₂, effectiveDomain₁,
        helperForTheorem_37_2_inverseLowerConjugate_pointwiseRewrite,
        lt_top_iff_ne_top, bot_lt_iff_ne_bot] using hPoint
    have hxLower :
        -x ∈ effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x) := by
      simpa [hFirstDomainEq] using hxUpper
    simpa using hxLower
  · intro hx
    have hxLower :
        -x ∈ effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x) := by
      simpa using hx
    have hxUpper :
        -x ∈ effectiveDomain₁ (fun uStar x => theorem37ValueInfSup K uStar x) := by
      simpa [hFirstDomainEq] using hxLower
    intro uStar
    -- Rewrite the original upper-conjugate first-domain condition back to the inverse value.
    have hPoint := hxUpper (-uStar)
    simpa [effectiveDomain₂, effectiveDomain₁,
      helperForTheorem_37_2_inverseLowerConjugate_pointwiseRewrite,
      lt_top_iff_ne_top, bot_lt_iff_ne_bot] using hPoint

/-- Helper for Theorem 37.2: the inverse-domain transport proves the textbook sign-correct first
dual support formula with argument `-z`. -/
lemma helperForTheorem_37_2_firstDualSupport_formula_signCorrected
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (z : Fin m → ℝ) :
    -supportFunctionEReal
        (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (-z) =
      iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
        iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1)) := by
  have hInverseClosed : IsClosedSaddleFunction (bifunctionInverse K) :=
    helperForTheorem_37_2_inverseClosed (K := K) hKclosed hKproper hQ.noTop
  have hInverseProper : IsProperSaddleFunction (bifunctionInverse K) :=
    helperForTheorem_37_2_inverseProper (K := K) hKproper
  have hInverseSupport :
      supportFunctionEReal
          (effectiveDomain₂
            (fun uStar x => theorem37ValueSupInf (bifunctionInverse K) uStar x)) z =
        iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₁ (bifunctionInverse K))} =>
          iSup (fun u : {u // u ∈ effectiveDomain₂ (bifunctionInverse K)} =>
            bifunctionInverse K v.1 (u.1 + z) - bifunctionInverse K v.1 u.1)) :=
    helperForTheorem_37_2_secondDualSupport_formula
      (K := bifunctionInverse K) (hKclosed := hInverseClosed) (hKproper := hInverseProper)
      hQ.inverseGlobal hQ.inverseBoundary z
  have hInverseDomain :
      effectiveDomain₂ (fun uStar x => theorem37ValueSupInf (bifunctionInverse K) uStar x) =
        Neg.neg ⁻¹' effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x) :=
    helperForTheorem_37_2_inverseSecondDualDomain_eq_originalFirstDualDomain
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ.primalGlobal
  have hInverseSlices :
      iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₁ (bifunctionInverse K))} =>
        iSup (fun u : {u // u ∈ effectiveDomain₂ (bifunctionInverse K)} =>
          bifunctionInverse K v.1 (u.1 + z) - bifunctionInverse K v.1 u.1)) =
        -iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
          iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1)) :=
    helperForTheorem_37_2_inverseSliceSup_eq_negatedFirstDualInf (K := K) z
  have hSupportRewrite :
      supportFunctionEReal
          (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (-z) =
        -iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
          iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1)) := by
    calc
      supportFunctionEReal
          (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (-z) =
        supportFunctionEReal
          (Neg.neg ⁻¹' effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) z := by
            -- The inverse-domain computation shifts the support argument from `z` to `-z`.
            symm
            simpa using
              (helperForTheorem_37_2_supportFunctionEReal_negPreimage
                (C := effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (z := z))
      _ =
        supportFunctionEReal
          (effectiveDomain₂
            (fun uStar x => theorem37ValueSupInf (bifunctionInverse K) uStar x)) z := by
              -- Replace the sign-twisted preimage by the inverse common dual domain.
              rw [hInverseDomain]
      _ =
        iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₁ (bifunctionInverse K))} =>
          iSup (fun u : {u // u ∈ effectiveDomain₂ (bifunctionInverse K)} =>
            bifunctionInverse K v.1 (u.1 + z) - bifunctionInverse K v.1 u.1)) :=
              hInverseSupport
      _ =
        -iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
          iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1)) :=
              hInverseSlices
  -- Negating the sign-correct identity recovers the textbook left-hand side exactly.
  simpa using congrArg Neg.neg hSupportRewrite

/-- Helper for Theorem 37.2: for each `v ∈ ri D`, the support of the Fenchel-domain of the
negated first slice is exactly its recession function. -/
lemma helperForTheorem_37_2_negatedFirstInteriorSliceSupport_eq_recession
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    {v : Fin n → ℝ}
    (hv : v ∈ intrinsicInterior ℝ (effectiveDomain₂ K))
    (z : Fin m → ℝ) :
    supportFunctionEReal
        (effectiveDomain (Set.univ : Set (Fin m → ℝ))
          (fenchelConjugate m (fun u => -K u v))) z =
      recessionFunction (fun u => -K u v) z := by
  have hSlice :=
    helperForTheorem_37_2_negatedFirstSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hv
  have hProperSlice :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun u => -K u v) :=
    helperForTheorem_37_2_negatedFirstSlice_properOn_univ
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hv
  have hLscSlice : LowerSemicontinuous (fun u => -K u v) := by
    have hRawLsc : LowerSemicontinuous (functionConvexClosure (fun u => -K u v)) := by
      -- The raw convex closure is always lower semicontinuous.
      simpa [functionConvexClosure] using
        helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
          (f := fun u => -K u v)
    -- Closedness of the slice collapses the convex closure back to the slice itself.
    simpa [hSlice.2.1.symm] using hRawLsc
  have hClosedSlice : ClosedConvexFunction (fun u => -K u v) := by
    -- Package the negated first slice as a closed convex function so Chapter 13 applies directly.
    refine ⟨?_, hLscSlice⟩
    exact helperForTheorem_37_2_convexFunctionOn_univ_of_IsERealConvexOn hSlice.1
  -- Evaluate the Chapter 13 support/recession identity at the present direction `z`.
  exact congrArg (fun g => g z)
    (section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction
      (n := m) (f := fun u => -K u v) hClosedSlice hProperSlice)

/-- Helper for Theorem 37.2: for each `v ∈ ri D`, the first-family infimum is the negative of
the recession function of the convex slice `-K(·, v)`. -/
lemma helperForTheorem_37_2_firstSliceInf_eq_neg_recessionFunction_preTheorem
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)})
    (z : Fin m → ℝ) :
    iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1) =
      -recessionFunction (fun u => -K u v.1) z := by
  let g : (Fin m → ℝ) → EReal := fun u => -K u v.1
  have hSlice :=
    helperForTheorem_37_2_negatedFirstSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal v.2
  have hDomain :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) g = effectiveDomain₁ K := by
    -- The negated first slice has the original first effective domain as its finite locus.
    simpa [g, convexFunctionEffectiveDomain, effectiveDomain_eq] using hSlice.2.2.2
  have hNegatedSup :
      iSup (fun u : {u // u ∈ effectiveDomain₁ K} =>
        -(K (u.1 + z) v.1 - K u.1 v.1)) =
      recessionFunction g z := by
    have hSet :
        {r : EReal | ∃ u ∈ effectiveDomain₁ K, r = g (u + z) - g u} =
          Set.range (fun u : {u // u ∈ effectiveDomain₁ K} => g (u.1 + z) - g u.1) := by
      -- Rewrite the recession supremum as a subtype-indexed range over `dom₁ K`.
      ext r
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨u, hu⟩, rfl⟩
      · rintro ⟨u, rfl⟩
        exact ⟨u.1, u.2, rfl⟩
    have hvDom : v.1 ∈ effectiveDomain₂ K :=
      intrinsicInterior_subset (𝕜 := ℝ) (s := effectiveDomain₂ K) v.2
    have hPointwise :
        (fun u : {u // u ∈ effectiveDomain₁ K} => -(K (u.1 + z) v.1 - K u.1 v.1)) =
          fun u : {u // u ∈ effectiveDomain₁ K} => g (u.1 + z) - g u.1 := by
      -- Each increment of the negated slice is the negation of the original first-family increment.
      funext u
      have huBot : K u.1 v.1 ≠ ⊥ := by
        simpa [bot_lt_iff_ne_bot] using u.2 v.1
      have huzTop : K (u.1 + z) v.1 ≠ ⊤ := by
        simpa [lt_top_iff_ne_top] using hvDom (u.1 + z)
      have hNegSub :
          -(K (u.1 + z) v.1 - K u.1 v.1) =
            -K (u.1 + z) v.1 + K u.1 v.1 :=
        EReal.neg_sub (x := K (u.1 + z) v.1) (y := K u.1 v.1)
          (Or.inr huBot) (Or.inl huzTop)
      calc
        -(K (u.1 + z) v.1 - K u.1 v.1)
            = -K (u.1 + z) v.1 + K u.1 v.1 := hNegSub
        _ = g (u.1 + z) - g u.1 := by
              simp [g, sub_eq_add_neg, add_comm]
    -- After the pointwise rewrite, the resulting supremum is exactly the recession function.
    calc
      iSup (fun u : {u // u ∈ effectiveDomain₁ K} => -(K (u.1 + z) v.1 - K u.1 v.1))
          = iSup (fun u : {u // u ∈ effectiveDomain₁ K} => g (u.1 + z) - g u.1) := by
              rw [hPointwise]
      _ = sSup (Set.range (fun u : {u // u ∈ effectiveDomain₁ K} => g (u.1 + z) - g u.1)) := by
            rw [sSup_range]
      _ = sSup {r : EReal | ∃ u ∈ effectiveDomain₁ K, r = g (u + z) - g u} := by
            rw [← hSet]
      _ = recessionFunction g z := by
            simp [recessionFunction, hDomain]
  have hNegComm :
      iSup (fun u : {u // u ∈ effectiveDomain₁ K} =>
        -(K (u.1 + z) v.1 - K u.1 v.1)) =
      -iInf (fun u : {u // u ∈ effectiveDomain₁ K} =>
        K (u.1 + z) v.1 - K u.1 v.1) := by
    -- Commute negation across the indexed infimum before invoking the pointwise rewrite above.
    simpa using
      (helperForLemma33_0_5_neg_iInf_neg_eq_iSup
        (f := fun u : {u // u ∈ effectiveDomain₁ K} =>
          -(K (u.1 + z) v.1 - K u.1 v.1))).symm
  -- Negate the commuted identity to recover the original `iInf` on the left.
  have hInfComm :
      iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1) =
        -iSup (fun u : {u // u ∈ effectiveDomain₁ K} =>
          -(K (u.1 + z) v.1 - K u.1 v.1)) := by
    have hNeg := congrArg Neg.neg hNegComm
    simpa using hNeg.symm
  calc
    iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1) =
      -iSup (fun u : {u // u ∈ effectiveDomain₁ K} =>
        -(K (u.1 + z) v.1 - K u.1 v.1)) := hInfComm
    _ = -recessionFunction g z := by rw [hNegatedSup]

/-- Helper for Theorem 37.2: this compatibility wrapper records the sign-correct first dual
support formula with support argument `-z`. -/
lemma helperForTheorem_37_2_firstDualSupport_formula
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (z : Fin m → ℝ) :
    -supportFunctionEReal
        (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (-z) =
      iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
        iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1)) := by
  -- Reuse the proved sign-correct formula rather than duplicating the same support rewrite under
  -- a second helper name.
  exact
    helperForTheorem_37_2_firstDualSupport_formula_signCorrected
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ z
theorem section37_theorem37_2
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K) :
    let C : Set (Fin m → ℝ) := effectiveDomain₁ K
    let D : Set (Fin n → ℝ) := effectiveDomain₂ K
    let CStar : Set (Fin m → ℝ) :=
      effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)
    let DStar : Set (Fin n → ℝ) :=
      effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)
    ∀ w z,
      (supportFunctionEReal DStar w =
        iSup (fun u : {u // u ∈ intrinsicInterior ℝ C} =>
          iSup (fun v : {v // v ∈ D} => K u.1 (v.1 + w) - K u.1 v.1))) ∧
      (-supportFunctionEReal CStar (-z) =
        iInf (fun v : {v // v ∈ intrinsicInterior ℝ D} =>
          iInf (fun u : {u // u ∈ C} => K (u.1 + z) v.1 - K u.1 v.1))) := by
  change
    ∀ w z,
      (supportFunctionEReal (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w =
        iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
          iSup (fun v : {v // v ∈ effectiveDomain₂ K} => K u.1 (v.1 + w) - K u.1 v.1))) ∧
      (-supportFunctionEReal (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (-z) =
        iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
          iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1)))
  intro w z
  constructor
  · exact
      helperForTheorem_37_2_secondDualSupport_formula
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
        hQ.primalGlobal hQ.primalBoundary w
  · exact
      -- The first-domain formula is sign-correct with argument `-z`.
      helperForTheorem_37_2_firstDualSupport_formula_signCorrected
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ z

/-- Helper for Corollary 37.2.1: every second-family increment from Theorem 37.2 vanishes at
the zero recession direction. -/
lemma helperForCorollary_37_2_1_secondFamilyIncrementAtZero
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)})
    (v : {v // v ∈ effectiveDomain₂ K}) :
    K u.1 (v.1 + (0 : Fin n → ℝ)) - K u.1 v.1 = 0 := by
  have hSlice :=
    helperForTheorem_37_2_convexSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal u.2
  have hvTop : K u.1 v.1 ≠ ⊤ := by
    -- The slice-domain identification turns membership in `dom₂ K` into finiteness of `K(u, v)`.
    have hvDomain : v.1 ∈ convexFunctionEffectiveDomain (K u.1) := by
      rw [hSlice.2.2.2]
      exact v.2
    simpa [convexFunctionEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top] using hvDomain
  have hvBot : K u.1 v.1 ≠ ⊥ := hSlice.2.2.1 v.1
  -- At zero direction the displayed difference is exactly `K(u, v) - K(u, v)`.
  simpa using (EReal.sub_self hvTop hvBot)

/-- Helper for Corollary 37.2.1: every first-family increment from Theorem 37.2 vanishes at
the zero recession direction. -/
lemma helperForCorollary_37_2_1_firstFamilyIncrementAtZero
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)})
    (u : {u // u ∈ effectiveDomain₁ K}) :
    K (u.1 + (0 : Fin m → ℝ)) v.1 - K u.1 v.1 = 0 := by
  have hSlice :=
    helperForTheorem_37_2_negatedFirstSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal v.2
  have huTop : K u.1 v.1 ≠ ⊤ := by
    -- The negated first slice has no `⊥`, so the original slice value avoids `⊤`.
    simpa [EReal.neg_eq_bot_iff] using hSlice.2.2.1 u.1
  have huBot : K u.1 v.1 ≠ ⊥ := by
    -- Membership in `dom₁ K` is the same as finiteness of the negated first slice at `u`.
    have huDomain : u.1 ∈ convexFunctionEffectiveDomain (fun u => -K u v.1) := by
      rw [hSlice.2.2.2]
      exact u.2
    simpa [convexFunctionEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top,
      EReal.neg_eq_top_iff] using huDomain
  -- Again the zero-direction increment is just `K(u, v) - K(u, v)`.
  simpa using (EReal.sub_self huTop huBot)

/-- Helper for Corollary 37.2.1: the second-family recession expression from Theorem 37.2
specializes to `0` at the zero direction. -/
lemma helperForCorollary_37_2_1_secondFamilySupAtZero
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
      iSup (fun v : {v // v ∈ effectiveDomain₂ K} =>
        K u.1 (v.1 + (0 : Fin n → ℝ)) - K u.1 v.1)) = 0 := by
  rcases (helperForTheorem_37_2_intrinsicInterior_nonempty
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper)).1 with ⟨u0, hu0⟩
  rcases helperForTheorem_37_2_secondDomain_nonempty (K := K) hKproper with ⟨v0, hv0⟩
  have hPoint :
      ∀ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
        ∀ v : {v // v ∈ effectiveDomain₂ K},
          K u.1 (v.1 + (0 : Fin n → ℝ)) - K u.1 v.1 = 0 := by
    intro u v
    -- The pointwise zero-increment lemma makes the nested supremum constant.
    exact helperForCorollary_37_2_1_secondFamilyIncrementAtZero
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal u v
  refine le_antisymm ?_ ?_
  · -- Every term in the nested supremum is already `0`, so the whole supremum is at most `0`.
    refine iSup_le ?_
    intro u
    refine iSup_le ?_
    intro v
    simpa using (hPoint u v).le
  · -- The witness pair coming from properness shows that the same nested supremum is at least `0`.
    exact
      le_iSup_of_le ⟨u0, hu0⟩ <|
        le_iSup_of_le ⟨v0, hv0⟩ <|
          by simpa using (hPoint ⟨u0, hu0⟩ ⟨v0, hv0⟩).ge

/-- Helper for Corollary 37.2.1: the first-family recession expression from Theorem 37.2
specializes to `0` at the zero direction. -/
lemma helperForCorollary_37_2_1_firstFamilyInfAtZero
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n) :
    iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
      iInf (fun u : {u // u ∈ effectiveDomain₁ K} =>
        K (u.1 + (0 : Fin m → ℝ)) v.1 - K u.1 v.1)) = 0 := by
  rcases (helperForTheorem_37_2_intrinsicInterior_nonempty
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper)).2 with ⟨v0, hv0⟩
  rcases helperForTheorem_37_2_firstDomain_nonempty (K := K) hKproper with ⟨u0, hu0⟩
  have hPoint :
      ∀ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
        ∀ u : {u // u ∈ effectiveDomain₁ K},
          K (u.1 + (0 : Fin m → ℝ)) v.1 - K u.1 v.1 = 0 := by
    intro v u
    -- The first-family expression is likewise pointwise zero at direction `0`.
    exact helperForCorollary_37_2_1_firstFamilyIncrementAtZero
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal v u
  refine le_antisymm ?_ ?_
  · -- The witness pair again forces the nested infimum to be at most `0`.
    exact
      iInf_le_of_le ⟨v0, hv0⟩ <|
        iInf_le_of_le ⟨u0, hu0⟩ <|
          by simpa using (hPoint ⟨v0, hv0⟩ ⟨u0, hu0⟩).le
  · -- Since each term is `0`, the infimum cannot drop below `0`.
    refine le_iInf ?_
    intro v
    refine le_iInf ?_
    intro u
    simpa using (hPoint v u).ge

/-- Helper for Corollary 37.2.1: for each `u ∈ ri C`, the second-family slice supremum from
Theorem 37.2 is exactly the recession function of `K(u, ·)`. -/
lemma helperForCorollary_37_2_1_secondSliceSup_eq_recessionFunction
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)})
    (w : Fin n → ℝ) :
    iSup (fun v : {v // v ∈ effectiveDomain₂ K} => K u.1 (v.1 + w) - K u.1 v.1) =
      recessionFunction (K u.1) w := by
  have hSlice :=
    helperForTheorem_37_2_convexSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal u.2
  have hDomain :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u.1) = effectiveDomain₂ K := by
    -- The interior-slice theorem identifies the unrestricted slice domain with the common set `D`.
    simpa [convexFunctionEffectiveDomain, effectiveDomain_eq] using hSlice.2.2.2
  have hSet :
      {r : EReal | ∃ v ∈ effectiveDomain₂ K, r = K u.1 (v + w) - K u.1 v} =
        Set.range (fun v : {v // v ∈ effectiveDomain₂ K} => K u.1 (v.1 + w) - K u.1 v.1) := by
    -- Repackage the domain-restricted supremum as a subtype-indexed range.
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨v.1, v.2, rfl⟩
  -- Unfold the recession function and rewrite its defining `sSup` over the common slice domain.
  calc
    iSup (fun v : {v // v ∈ effectiveDomain₂ K} => K u.1 (v.1 + w) - K u.1 v.1)
        = sSup (Set.range
            (fun v : {v // v ∈ effectiveDomain₂ K} => K u.1 (v.1 + w) - K u.1 v.1)) := by
              rw [sSup_range]
    _ = sSup {r : EReal | ∃ v ∈ effectiveDomain₂ K, r = K u.1 (v + w) - K u.1 v} := by
          rw [← hSet]
    _ = recessionFunction (K u.1) w := by
          simp [recessionFunction, hDomain]

/-- Helper for Corollary 37.2.1: the support function of `D*` is the supremum of the recession
functions of the primal slices `K(u, ·)` over `u ∈ ri C`. -/
lemma helperForCorollary_37_2_1_secondSupport_eq_iSup_sliceRecession
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (w : Fin n → ℝ) :
    supportFunctionEReal
        (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w =
      iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
        recessionFunction (K u.1) w) := by
  -- Rewrite the existing second-dual support identity slice-by-slice in recession-function form.
  calc
    supportFunctionEReal
        (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w =
      iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
        iSup (fun v : {v // v ∈ effectiveDomain₂ K} => K u.1 (v.1 + w) - K u.1 v.1)) :=
          helperForTheorem_37_2_secondDualSupport_formula
            (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
            hQ.primalGlobal hQ.primalBoundary w
    _ =
      iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
        recessionFunction (K u.1) w) := by
          refine iSup_congr ?_
          intro u
          exact helperForCorollary_37_2_1_secondSliceSup_eq_recessionFunction
            (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ.primalGlobal u w

/-- Helper for Corollary 37.2.1: for each `v ∈ ri D`, the first-family infimum from Theorem 37.2
is the negative of the recession function of the convex slice `-K(·, v)`. -/
lemma helperForCorollary_37_2_1_firstSliceInf_eq_neg_recessionFunction
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)})
    (z : Fin m → ℝ) :
    iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1) =
      -recessionFunction (fun u => -K u v.1) z := by
  -- Reuse the theorem-level pointwise slice rewrite that will also feed the main support formula.
  exact helperForTheorem_37_2_firstSliceInf_eq_neg_recessionFunction_preTheorem
    (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal v z

/-- Helper for Corollary 37.2.1: the sign-correct first support identity rewrites `support C* (-z)`
as the supremum of the recession functions of the convex slices `-K(·, v)` over `v ∈ ri D`. -/
lemma helperForCorollary_37_2_1_firstSupport_negArg_eq_iSup_negatedFirstSliceRecession
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (z : Fin m → ℝ) :
    supportFunctionEReal
        (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (-z) =
      iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
        recessionFunction (fun u => -K u v.1) z) := by
  -- Route correction: the available first-dual support identity is the sign-correct one with
  -- support argument `-z`, so the corollary uses that formula directly and removes the sign only
  -- when quantifying over directions in the final theorem.
  calc
    supportFunctionEReal
        (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (-z) =
      -(-supportFunctionEReal
        (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (-z)) := by
          simp
    _ =
      -iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
        iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1)) := by
          rw [helperForTheorem_37_2_firstDualSupport_formula_signCorrected
            (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ z]
    _ =
      -iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
        -recessionFunction (fun u => -K u v.1) z) := by
          have hFamily :
              (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
                iInf (fun u : {u // u ∈ effectiveDomain₁ K} => K (u.1 + z) v.1 - K u.1 v.1)) =
                (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
                  -recessionFunction (fun u => -K u v.1) z) := by
            -- Rewrite the inner `iInf` for each fixed `v` using the slice recession helper.
            funext v
            exact helperForCorollary_37_2_1_firstSliceInf_eq_neg_recessionFunction
              (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ.primalGlobal v z
          rw [hFamily]
    _ =
      iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
        recessionFunction (fun u => -K u v.1) z) := by
          have hNegIInf :
              -iInf (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
                -recessionFunction (fun u => -K u v.1) z) =
                iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
                  recessionFunction (fun u => -K u v.1) z) := by
            let V : Type := {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)}
            -- Commute the outer negation across the `v`-infimum.
            change -iInf (fun v : V => -recessionFunction (fun u => -K u v.1) z) =
              iSup (fun v : V => recessionFunction (fun u => -K u v.1) z)
            exact
              (helperForLemma33_0_5_neg_iInf_neg_eq_iSup
                (f := fun v : V => recessionFunction (fun u => -K u v.1) z))
          exact hNegIInf

/-- Helper for Corollary 37.2.1: positivity of an indexed supremum is equivalent to the existence
of a positive slice. -/
lemma helperForCorollary_37_2_1_iSup_gt_zero_iff_exists_slice_gt_zero
    {ι : Type*} (a : ι → EReal) :
    iSup a > (0 : EReal) ↔ ∃ i, a i > (0 : EReal) := by
  -- The complete-lattice `lt_iSup_iff` principle turns support positivity into a slice witness.
  constructor
  · intro hSup
    rcases (lt_iSup_iff).1 hSup with ⟨i, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact lt_of_lt_of_le hi (le_iSup_of_le i le_rfl)

/-- Corollary 37.2.1: the origin lies in the interior of `D*` exactly when the convex slices
`K(u, ·)` for `u ∈ ri C` have no common recession direction, and similarly for `C*` and the
convex slices `-K(·, v)` for `v ∈ ri D`. -/
theorem corollary37_2_1_origin_interior_iff_no_common_recession_direction
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K) :
    let C : Set (Fin m → ℝ) := effectiveDomain₁ K
    let D : Set (Fin n → ℝ) := effectiveDomain₂ K
    let CStar : Set (Fin m → ℝ) :=
      effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)
    let DStar : Set (Fin n → ℝ) :=
      effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)
    ((0 : Fin n → ℝ) ∈ interior DStar ↔
      ∀ w : Fin n → ℝ, w ≠ 0 →
        ∃ u : {u // u ∈ intrinsicInterior ℝ C}, ¬ IsRecessionDirection (K u.1) w) ∧
    ((0 : Fin m → ℝ) ∈ interior CStar ↔
      ∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ D},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) := by
  dsimp
  rcases helperForTheorem_37_2_canonicalCommonEffectiveDomains
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ.primalGlobal with
    ⟨hCStarNonempty, hDStarNonempty, hCStarConvex, hDStarConvex, _hUpperC, _hUpperD⟩
  have hDInterior :
      ((0 : Fin n → ℝ) ∈
          interior (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x))) ↔
        ∀ w : Fin n → ℝ, w ≠ 0 →
          supportFunctionEReal
            (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w >
              (0 : EReal) := by
    -- The Chapter 13 criterion reduces `0 ∈ int D*` to strict positivity of the support function.
    exact
      section13_zero_mem_interior_iff_forall_supportFunctionEReal_pos
        (C := effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x))
        hDStarConvex hDStarNonempty
  have hCInterior :
      ((0 : Fin m → ℝ) ∈
          interior (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x))) ↔
        ∀ z : Fin m → ℝ, z ≠ 0 →
          supportFunctionEReal
            (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) z >
              (0 : EReal) := by
    -- The same support characterization applies to `C*`.
    exact
      section13_zero_mem_interior_iff_forall_supportFunctionEReal_pos
        (C := effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x))
        hCStarConvex hCStarNonempty
  constructor
  · constructor
    · intro hOrigin w hw
      -- Support positivity for `D*` yields a slice with strictly positive recession value.
      have hSupportPos :
          supportFunctionEReal
              (effectiveDomain₂ (fun uStar x => theorem37ValueSupInf K uStar x)) w >
            (0 : EReal) :=
        (hDInterior.1 hOrigin) w hw
      have hRecSupPos :
          iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
            recessionFunction (K u.1) w) > (0 : EReal) := by
        rw [helperForCorollary_37_2_1_secondSupport_eq_iSup_sliceRecession
          (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ w] at hSupportPos
        exact hSupportPos
      rcases
          (helperForCorollary_37_2_1_iSup_gt_zero_iff_exists_slice_gt_zero
            (a := fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
              recessionFunction (K u.1) w)).1 hRecSupPos with
        ⟨u, huPos⟩
      refine ⟨u, ?_⟩
      -- Positive recession value is exactly failure of the recession-direction inequality.
      intro huRec
      exact huPos.not_ge (by simpa [IsRecessionDirection] using huRec)
    · intro hNoCommon
      -- A witness slice with positive recession value gives support positivity for every nonzero direction.
      refine hDInterior.2 ?_
      intro w hw
      rcases hNoCommon w hw with ⟨u, huNotRec⟩
      have huPos : recessionFunction (K u.1) w > (0 : EReal) := by
        exact lt_of_not_ge (by simpa [IsRecessionDirection] using huNotRec)
      have hRecSupPos :
          iSup (fun u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} =>
            recessionFunction (K u.1) w) > (0 : EReal) :=
        lt_of_lt_of_le huPos (le_iSup_of_le u le_rfl)
      rw [helperForCorollary_37_2_1_secondSupport_eq_iSup_sliceRecession
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ w]
      exact hRecSupPos
  · constructor
    · intro hOrigin z hz
      -- Use the sign-correct support identity at `-z`, then extract a positive negated first slice.
      have hSupportPos :
          supportFunctionEReal
              (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) (-z) >
            (0 : EReal) :=
        (hCInterior.1 hOrigin) (-z) (by simpa using hz)
      have hRecSupPos :
          iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
            recessionFunction (fun u => -K u v.1) z) > (0 : EReal) := by
        rw [helperForCorollary_37_2_1_firstSupport_negArg_eq_iSup_negatedFirstSliceRecession
          (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ z] at hSupportPos
        exact hSupportPos
      rcases
          (helperForCorollary_37_2_1_iSup_gt_zero_iff_exists_slice_gt_zero
            (a := fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
              recessionFunction (fun u => -K u v.1) z)).1 hRecSupPos with
        ⟨v, hvPos⟩
      refine ⟨v, ?_⟩
      -- Again, strict positivity is exactly the negation of the recession-direction condition.
      intro hvRec
      exact hvPos.not_ge (by simpa [IsRecessionDirection] using hvRec)
    · intro hNoCommon
      -- Rewrite support positivity for an arbitrary nonzero `y` using the witness provided for `z = -y`.
      refine hCInterior.2 ?_
      intro y hy
      rcases hNoCommon (-y) (by simpa using hy) with ⟨v, hvNotRec⟩
      have hvPos : recessionFunction (fun u => -K u v.1) (-y) > (0 : EReal) := by
        exact lt_of_not_ge (by simpa [IsRecessionDirection] using hvNotRec)
      have hRecSupPos :
          iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
            recessionFunction (fun u => -K u v.1) (-y)) > (0 : EReal) :=
        lt_of_lt_of_le hvPos (le_iSup_of_le v le_rfl)
      have hSupportEq :
          supportFunctionEReal
              (effectiveDomain₁ (fun uStar x => theorem37ValueSupInf K uStar x)) y =
            iSup (fun v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} =>
              recessionFunction (fun u => -K u v.1) (-y)) := by
        have hSupportEqNegNeg :=
          helperForCorollary_37_2_1_firstSupport_negArg_eq_iSup_negatedFirstSliceRecession
            (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ (-y)
        simpa only [neg_neg] using hSupportEqNegNeg
      rw [hSupportEq]
      exact hRecSupPos

end Section37
end Chap07

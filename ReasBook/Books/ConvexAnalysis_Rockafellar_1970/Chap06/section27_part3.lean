/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part2

section Chap06
section Section27

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 6.27.1: the shifted-level support identity in part (h) is still waiting on
the constant-shift conjugate formula to be packaged for `sublevelSetEReal`. -/
-- TODO: define the shifted function `gα x = f x - α`, prove `sublevelSetEReal f α = {x | gα x ≤ 0}`
-- and `gα* = f* + α`, then invoke the Chapter 13 zero-sublevel support theorem.
lemma helperForTheorem_6_27_1_shiftedLevel_support_formula {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ α : ℝ,
      supportFunctionEReal (sublevelSetEReal f α) =
        clConv n
          (positivelyHomogeneousConvexFunctionGenerated
            (fun y : Fin n → ℝ => fenchelConjugate n f y + (α : EReal))) := by
  intro α
  let gα : (Fin n → ℝ) → EReal := fun x => f x - (α : EReal)
  have hconst :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun _ : Fin n → ℝ => ((-α : ℝ) : EReal)) :=
    properConvexFunctionOn_const (n := n) (-α)
  have hgα_closed : ClosedConvexFunction gα := by
    refine ⟨?_, ?_⟩
    · -- Convexity is preserved by subtracting the fixed real constant `α`.
      change ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gα
      simpa [gα, sub_eq_add_neg] using convexFunctionOn_add_of_proper (n := n) hproper hconst
    · -- Lower semicontinuity is preserved by adding the finite constant `-α`.
      have hcont_add :
          ∀ x,
            ContinuousAt
              (fun p : EReal × EReal => p.1 + p.2)
              (f x, ((-α : ℝ) : EReal)) := by
        intro x
        have hnotbot_f : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
        exact EReal.continuousAt_add (h := Or.inr (EReal.coe_ne_bot _)) (h' := Or.inl hnotbot_f)
      have hgα_lsc : LowerSemicontinuous gα := by
        have :
            LowerSemicontinuous (fun x : Fin n → ℝ => f x + (((-α : ℝ) : EReal))) :=
          LowerSemicontinuous.add' hclosed.2 lowerSemicontinuous_const hcont_add
        simpa [gα, sub_eq_add_neg] using this
      exact hgα_lsc
  have hgα_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gα := by
    refine ⟨?_, ?_, ?_⟩
    · -- The same sum-of-proper-convex-functions argument gives proper convexity.
      change ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) gα
      simpa [gα, sub_eq_add_neg] using convexFunctionOn_add_of_proper (n := n) hproper hconst
    · -- Any epigraph witness for `f` shifts vertically by `-α`.
      rcases hproper.2.1 with ⟨⟨x, μ⟩, hxμ⟩
      refine ⟨(x, μ - α), ?_⟩
      constructor
      · exact Set.mem_univ x
      · have hxμ' : f x ≤ (μ : EReal) := hxμ.2
        have hshift := add_le_add_right hxμ' (((-α : ℝ) : EReal))
        simpa [gα, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hshift
    · -- Subtracting a finite real constant cannot create the value `⊥`.
      intro x _hx
      have hx : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
      have : f x + (((-α : ℝ) : EReal)) ≠ (⊥ : EReal) :=
        add_ne_bot_of_notbot hx (EReal.coe_ne_bot _)
      simpa [gα, sub_eq_add_neg] using this
  have hset :
      sublevelSetEReal f α = {x : Fin n → ℝ | gα x ≤ (0 : EReal)} := by
    -- Recenter the `α`-sublevel of `f` as the zero-sublevel of the shifted function `gα`.
    ext x
    simpa [sublevelSetEReal, gα] using
      (EReal.sub_nonpos : f x - (α : EReal) ≤ (0 : EReal) ↔ f x ≤ (α : EReal)).symm
  have hconj :
      fenchelConjugate n gα =
        fun y : Fin n → ℝ => fenchelConjugate n f y + (α : EReal) := by
    -- The conjugate of `f - α` is `f* + α`.
    simpa [gα, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (section16_fenchelConjugate_add_const (h := f) (-α))
  have hsupport :
      supportFunctionEReal {x : Fin n → ℝ | gα x ≤ (0 : EReal)} =
        clConv n (positivelyHomogeneousConvexFunctionGenerated (fenchelConjugate n gα)) :=
    (supportFunctionEReal_setOf_le_zero_eq_clConv_posHomGenerated_fenchelConjugate_and_dual
      (n := n) (f := gα) hgα_closed hgα_proper).1
  -- Apply Theorem 13.5 to the shifted function and then rewrite its conjugate explicitly.
  rw [hset]
  simpa [hconj] using hsupport

/-- Helper for Theorem 6.27.1: after subtracting the finite infimum, the shifted level-set support
is exactly the approximate-support term from Theorem 23.6 for `f*` at the origin. -/
lemma helperForTheorem_6_27_1_sublevel_support_eq_approximateSupport_conjugate_zero {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hInfFinite : IsFiniteEReal (functionInfimumEReal f))
    (β : ℝ) (hβ : 0 < β) (y : Fin n → ℝ) :
    supportFunctionEReal (sublevelSetEReal f ((functionInfimumEReal f).toReal + β)) y =
      approximateSubdifferentialSupportAt (fenchelConjugate n f) 0 β.toNNReal y := by
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  have hA := helperForTheorem_6_27_1_conjugateAtZero_eq_neg_functionInfimumEReal f
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hconvStar : ConvexFunction fStar := by
    simpa [fStar, ConvexFunction] using hproperStar.1
  have hLower : HasRealLowerBound f :=
    (helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot f).2 hInfFinite.2
  have h0Dom :
      (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar :=
    hA.2.1 hLower
  have h0Finite : fStar 0 ≠ (⊤ : EReal) ∧ fStar 0 ≠ (⊥ : EReal) := by
    constructor
    · rw [effectiveDomain_eq] at h0Dom
      exact lt_top_iff_ne_top.mp h0Dom.2
    · exact hproperStar.2.2 0 (by simp)
  have hInf_coe :
      (((functionInfimumEReal f).toReal : ℝ) : EReal) = functionInfimumEReal f := by
    simpa using (EReal.coe_toReal (x := functionInfimumEReal f) hInfFinite.1 hInfFinite.2)
  have hβ_real : (β.toNNReal : ℝ) = β := by
    simpa [Real.toNNReal] using (max_eq_left (le_of_lt hβ))
  have hβ_coe : (((β.toNNReal : ℝ)) : EReal) = ((β : ℝ) : EReal) := by
    simp [hβ_real]
  have hconj0 : fStar 0 = -functionInfimumEReal f := by
    have := congrArg Neg.neg hA.1
    simpa [fStar] using this.symm
  have hf_ne_bot : ∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal) := by
    intro x
    exact hproper.2.2 x (by simp)
  have hbiconj : fenchelConjugate n fStar = f := by
    simpa [fStar] using
      fenchelConjugate_biconjugate_eq_of_closedConvex
        (n := n) (f := f) hclosed.2 hclosed.1 hf_ne_bot
  have hTrans :
      ∀ v : Fin n → ℝ,
        fenchelConjugate n (translatedDifferenceFunctionAt fStar 0) v =
          f v - functionInfimumEReal f := by
    intro v
    -- At `x = 0`, the affine correction term in the translated-difference conjugate disappears.
    calc
      fenchelConjugate n (translatedDifferenceFunctionAt fStar 0) v
          = fenchelConjugate n fStar v + fStar 0 -
              ((dotProduct (0 : Fin n → ℝ) v : ℝ) : EReal) := by
              simpa [fStar] using
                helperForProposition_23_6_1_translatedDifference_fenchelConjugate
                  (f := fStar) (x := (0 : Fin n → ℝ)) h0Finite v
      _ = f v + fStar 0 := by simp [hbiconj]
      _ = f v - functionInfimumEReal f := by simp [hconj0, sub_eq_add_neg, add_assoc]
  have hSet :
      {v : Fin n → ℝ |
          fenchelConjugate n (translatedDifferenceFunctionAt fStar 0) v ≤
            (((β.toNNReal : ℝ)) : EReal)} =
        sublevelSetEReal f ((functionInfimumEReal f).toReal + β) := by
    ext v
    constructor
    · intro hv
      have hv' : f v - functionInfimumEReal f ≤ (((β.toNNReal : ℝ)) : EReal) := by
        simpa [hTrans v] using hv
      have hv'' :
          f v ≤ functionInfimumEReal f + ((((β.toNNReal : ℝ)) : EReal)) := by
        have :
            f v ≤ (((β.toNNReal : ℝ)) : EReal) + functionInfimumEReal f :=
          (EReal.sub_le_iff_le_add
            (a := f v) (b := functionInfimumEReal f)
            (c := (((β.toNNReal : ℝ)) : EReal))
            (Or.inl hInfFinite.2) (Or.inr (by simp))).1 hv'
        simpa [add_comm, add_left_comm, add_assoc] using this
      simpa [sublevelSetEReal, hInf_coe, hβ_real, hβ_coe, add_assoc, add_left_comm,
        add_comm] using hv''
    · intro hv
      have hv' :
          f v ≤ functionInfimumEReal f + ((((β.toNNReal : ℝ)) : EReal)) := by
        simpa [sublevelSetEReal, hInf_coe, hβ_real, hβ_coe, add_assoc, add_left_comm,
          add_comm] using hv
      have hv'' : f v - functionInfimumEReal f ≤ (((β.toNNReal : ℝ)) : EReal) := by
        have hv''' :
            f v ≤ (((β.toNNReal : ℝ)) : EReal) + functionInfimumEReal f := by
          simpa [add_comm, add_left_comm, add_assoc] using hv'
        exact
          (EReal.sub_le_iff_le_add
            (a := f v) (b := functionInfimumEReal f)
            (c := (((β.toNNReal : ℝ)) : EReal))
            (Or.inl hInfFinite.2) (Or.inr (by simp))).2 hv'''
      simpa [hTrans v] using hv''
  -- Replace the conjugate sublevel in Theorem 23.6 by the shifted primal level set.
  calc
    supportFunctionEReal (sublevelSetEReal f ((functionInfimumEReal f).toReal + β)) y
        =
          supportFunctionEReal
            {v : Fin n → ℝ |
              fenchelConjugate n (translatedDifferenceFunctionAt fStar 0) v ≤
                (((β.toNNReal : ℝ)) : EReal)} y := by
              rw [hSet]
    _ = approximateSubdifferentialSupportAt fStar 0 β.toNNReal y := by
          symm
          exact
            helperForTheorem_23_6_approximateSupport_eq_supportFunction_conjugateSublevel
              (f := fStar) hconvStar 0 y h0Finite β.toNNReal

/-- Helper for Theorem 6.27.1: recenter the level parameter around `inf f` and apply Theorem 23.6
to the conjugate at `0` to obtain the support-function limit from part (i). -/
lemma helperForTheorem_6_27_1_support_limit_to_directionalDerivative {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    closedProperConvexMinimumPartI f := by
  intro hInfFinite y
  let infReal : ℝ := (functionInfimumEReal f).toReal
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  have hA := helperForTheorem_6_27_1_conjugateAtZero_eq_neg_functionInfimumEReal f
  have hclosedStar : ClosedConvexFunction fStar := by
    have h := fenchelConjugate_closedConvex (n := n) (f := f)
    exact ⟨h.2, h.1⟩
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hLower : HasRealLowerBound f :=
    (helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot f).2 hInfFinite.2
  have h0Dom :
      (0 : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar :=
    hA.2.1 hLower
  have h0Finite : fStar 0 ≠ (⊤ : EReal) ∧ fStar 0 ≠ (⊥ : EReal) := by
    constructor
    · rw [effectiveDomain_eq] at h0Dom
      exact lt_top_iff_ne_top.mp h0Dom.2
    · exact hproperStar.2.2 0 (by simp)
  have hApprox :
      Filter.Tendsto
        (fun β : ℝ => approximateSubdifferentialSupportAt fStar 0 β.toNNReal y)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (upperDirectionalDerivativeAt fStar 0 y)) :=
    directionalDerivative_eq_tendsto_approximateSubdifferentialSupport
      fStar hclosedStar hproperStar 0 y h0Finite
  have hShift :
      Filter.Tendsto (fun α : ℝ => α - infReal)
        (nhdsWithin infReal (Set.Ioi infReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
    -- Recenter the right-neighborhood of `inf f` to the right-neighborhood of `0`.
    have hcont : ContinuousWithinAt (fun α : ℝ => α - infReal) (Set.Ioi infReal) infReal :=
      ((continuous_id.sub continuous_const).continuousAt).continuousWithinAt
    have hshift' :
        Filter.Tendsto (fun α : ℝ => α - infReal)
          (nhdsWithin infReal (Set.Ioi infReal))
          (nhdsWithin (infReal - infReal) (Set.Ioi (0 : ℝ))) :=
      hcont.tendsto_nhdsWithin (by
        intro α hα
        simpa [infReal, sub_pos] using hα)
    simpa using hshift'
  have hApproxShifted :
      Filter.Tendsto
        (fun α : ℝ => approximateSubdifferentialSupportAt fStar 0 (α - infReal).toNNReal y)
        (nhdsWithin infReal (Set.Ioi infReal))
        (nhds (upperDirectionalDerivativeAt fStar 0 y)) :=
    hApprox.comp hShift
  have hEventuallyEq :
      ∀ᶠ α : ℝ in nhdsWithin infReal (Set.Ioi infReal),
        supportFunctionEReal (sublevelSetEReal f α) y =
          approximateSubdifferentialSupportAt fStar 0 (α - infReal).toNNReal y := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hβ : 0 < α - infReal := sub_pos.2 hα
    -- For `α > inf f`, write `α = inf f + β` and invoke the Chapter 23 support rewrite.
    simpa [infReal, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      helperForTheorem_6_27_1_sublevel_support_eq_approximateSupport_conjugate_zero
        (f := f) hclosed hproper hInfFinite (β := α - infReal) (hβ := hβ) (y := y)
  -- Replace the approximate-support function by the actual level-set support values.
  have hEventuallyEq_symm :
      ∀ᶠ α : ℝ in nhdsWithin infReal (Set.Ioi infReal),
        approximateSubdifferentialSupportAt fStar 0 (α - infReal).toNNReal y =
          supportFunctionEReal (sublevelSetEReal f α) y := by
    filter_upwards [hEventuallyEq] with α hα
    exact hα.symm
  simpa [fStar] using hApproxShifted.congr' hEventuallyEq_symm

/-- Theorem 6.27.1: for any closed proper convex function `f`, parts (a) through (i) describe the
minimum value, minimum set, attainment, boundedness, uniqueness, recession behavior, level-set
support functions, and limiting support-function formula in terms of the Fenchel conjugate `f*`.
-/
theorem closedProperConvexFunction_minimum_characterizations {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    closedProperConvexMinimumPartA f ∧
      closedProperConvexMinimumPartB f ∧
      closedProperConvexMinimumPartC f ∧
      closedProperConvexMinimumPartD f ∧
      closedProperConvexMinimumPartE f ∧
      closedProperConvexMinimumPartF f ∧
      closedProperConvexMinimumPartG f ∧
      closedProperConvexMinimumPartH f ∧
      closedProperConvexMinimumPartI f := by
  have hA :
      closedProperConvexMinimumPartA f :=
    helperForTheorem_6_27_1_conjugateAtZero_eq_neg_functionInfimumEReal f
  have hMinEq :
      minimumSetEReal f = euclideanSubdifferentialAt (fenchelConjugate n f) 0 :=
    helperForTheorem_6_27_1_minimumSet_eq_euclideanSubdifferentialAt_conjugate_zero
      f hclosed hproper
  have hZeroFiberNonempty :
      (0 : Fin n → ℝ) ∈
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) →
        (euclideanSubdifferentialAt (fenchelConjugate n f) 0).Nonempty :=
    helperForTheorem_6_27_1_zeroFiber_nonempty_of_mem_relativeInterior
      (fenchelConjugate n f) (proper_fenchelConjugate_of_proper (n := n) (f := f) hproper)
  have hB : closedProperConvexMinimumPartB f := by
    refine ⟨hMinEq, ?_, ?_, ?_⟩
    · -- The nonemptiness clause is immediate from the set equality already established.
      simpa [hMinEq]
    · -- Relative-interior subdifferentiability is the Chapter 24 bridge at the origin.
      intro hri
      exact hZeroFiberNonempty hri
    · -- Route correction: the remaining recession/relative-interior equivalence is isolated.
      exact
        helperForTheorem_6_27_1_relativeInterior_iff_everyRecessionDirectionIsConstant
          f hclosed hproper
  have hC :
      closedProperConvexMinimumPartC f :=
    helperForTheorem_6_27_1_finite_unattained_iff_conjugate_zero_finite_and_bot_directional
      f hclosed hproper
  have hD : closedProperConvexMinimumPartD f := by
    refine ⟨?_, ?_⟩
    · -- The first half of part (d) is exactly Theorem 23.4 for the conjugate fiber at `0`.
      exact
        helperForTheorem_6_27_1_minimumSet_nonempty_bounded_iff_zero_mem_interior_dom_conjugate
          f hclosed hproper
    · -- Route correction: the no-recession-directions equivalence is the remaining Chapter 14 step.
      exact
        helperForTheorem_6_27_1_zero_mem_interior_iff_hasNoRecessionDirections
          f hclosed hproper
  have hE :
      closedProperConvexMinimumPartE f :=
    helperForTheorem_6_27_1_singleton_minimumSet_iff_differentiableAt_conjugate_zero
      f hclosed hproper
  have hF :
      closedProperConvexMinimumPartF f :=
    helperForTheorem_6_27_1_recessionCone_and_polar_bridges f hclosed hproper
  have hG :
      closedProperConvexMinimumPartG f :=
    helperForTheorem_6_27_1_closure_domainCriteria_and_strict_decreasing_ray
      f hclosed hproper
  have hH : closedProperConvexMinimumPartH f := by
    refine ⟨?_, ?_⟩
    · -- Route correction: the shifted-level support identity still needs the dedicated shift lemma.
      exact helperForTheorem_6_27_1_shiftedLevel_support_formula f hclosed hproper
    · -- The minimum-set support identity already follows from Theorem 23.2 at the origin of `f*`.
      exact
        helperForTheorem_6_27_1_support_minimumSet_eq_closure_directionalDerivative
          f hclosed hproper
  have hI :
      closedProperConvexMinimumPartI f :=
    helperForTheorem_6_27_1_support_limit_to_directionalDerivative f hclosed hproper
  exact ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩

-- Proof sketch: apply the bounded-attainment criterion from Theorem 6.27.1(d) under the
-- hypothesis that `f` has no recession directions to obtain a nonempty bounded minimum set, then
-- combine the earlier convexity and closedness results for minimum sets. The `ε`-`δ` statement
-- follows from the standard contradiction argument: otherwise one could choose near-minimizers
-- staying a fixed positive distance away from the bounded closed minimum set, and extract a limit
-- point contradicting minimality.
/-- Theorem 6.27.2: if `f` is a closed proper convex function with no direction of recession, then
its infimum is finite and attained, the minimum set is a nonempty closed bounded convex set, and
for every `ε > 0` there exists `δ > 0` such that every `x` with
`f x ≤ inf f + δ` lies within distance `ε` of some minimizer of `f`. -/
theorem closedProperConvexFunction_near_minimizer_of_noRecessionDirections {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hnoRecession : HasNoRecessionDirections f) :
    IsFiniteEReal (functionInfimumEReal f) ∧
      (minimumSetEReal f).Nonempty ∧
      IsClosed (minimumSetEReal f) ∧
      Bornology.IsBounded (minimumSetEReal f) ∧
      Convex ℝ (minimumSetEReal f) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x : Fin n → ℝ,
            f x ≤ functionInfimumEReal f + (δ : EReal) →
              ∃ z : Fin n → ℝ, z ∈ minimumSetEReal f ∧ ‖z - x‖ < ε := by
  let infReal : ℝ := (functionInfimumEReal f).toReal
  rcases closedProperConvexFunction_minimum_characterizations f hclosed hproper with
    ⟨_hA, _hB, _hC, hD, _hE, hF, _hG, _hH, _hI⟩
  -- Part (d) turns the no-recession hypothesis into a nonempty bounded minimum set.
  have hInterior :
      (0 : Fin n → ℝ) ∈
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) :=
    hD.2.2 hnoRecession
  have hMinNonemptyBounded :
      (minimumSetEReal f).Nonempty ∧ Bornology.IsBounded (minimumSetEReal f) :=
    hD.1.2 hInterior
  rcases hMinNonemptyBounded with ⟨hMinNonempty, hMinBounded⟩
  rcases hMinNonempty with ⟨x0, hx0⟩
  have hMinNonempty : (minimumSetEReal f).Nonempty := ⟨x0, hx0⟩
  -- A minimizing point forces the infimum to avoid both `±∞`.
  have hInf_ne_bot : functionInfimumEReal f ≠ (⊥ : EReal) := by
    rw [minimumSetEReal] at hx0
    have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := hproper.2.2 x0 (by simp)
    intro hbot
    exact hx0_ne_bot (hx0.trans hbot)
  have hInf_ne_top : functionInfimumEReal f ≠ (⊤ : EReal) := by
    rcases hproper.2.1 with ⟨⟨x1, μ1⟩, hx1μ1⟩
    have hInf_le : functionInfimumEReal f ≤ f x1 := by
      simpa [functionInfimumEReal] using (iInf_le (fun y => f y) x1)
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hInf_le (lt_of_le_of_lt hx1μ1.2 (by simp)))
  have hInfFinite : IsFiniteEReal (functionInfimumEReal f) := ⟨hInf_ne_top, hInf_ne_bot⟩
  have hInf_coe :
      (((functionInfimumEReal f).toReal : ℝ) : EReal) = functionInfimumEReal f := by
    simpa using (EReal.coe_toReal (x := functionInfimumEReal f) hInf_ne_top hInf_ne_bot)
  have hMinEq :
      minimumSetEReal f = sublevelSetEReal f (functionInfimumEReal f).toReal :=
    helperForTheorem_6_27_1_minimumSet_eq_realSublevel_at_infimum_of_attainment
      (f := f) hproper hMinNonempty
  -- Rewrite the minimum set as the attained infimum sublevel to recover closedness and convexity.
  have hMinClosed : IsClosed (minimumSetEReal f) := by
    rw [hMinEq]
    exact (lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hclosed.2 infReal
  have hMinConvex : Convex ℝ (minimumSetEReal f) := by
    rw [hMinEq]
    simpa [sublevelSetEReal] using
      (convexFunction_level_sets_convex (f := f) hclosed.1
        (α := (((functionInfimumEReal f).toReal : ℝ) : EReal))).2
  -- The reference sublevel `inf f + 1` shares the recession cone of the minimum set, hence is
  -- bounded as well.
  have hRefNonempty : (sublevelSetEReal f (infReal + 1)).Nonempty := by
    refine ⟨x0, ?_⟩
    rw [minimumSetEReal] at hx0
    rw [sublevelSetEReal]
    calc
      f x0 = functionInfimumEReal f := hx0
      _ = (((functionInfimumEReal f).toReal : ℝ) : EReal) := hInf_coe.symm
      _ ≤ (((functionInfimumEReal f).toReal + 1 : ℝ) : EReal) := by
        exact_mod_cast (show (functionInfimumEReal f).toReal ≤ (functionInfimumEReal f).toReal + 1 by
          linarith)
  have hRefClosed : IsClosed (sublevelSetEReal f (infReal + 1)) :=
    (lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hclosed.2 (infReal + 1)
  have hRefConvex : Convex ℝ (sublevelSetEReal f (infReal + 1)) := by
    simpa [sublevelSetEReal] using
      (convexFunction_level_sets_convex (f := f) hclosed.1
        (α := ((infReal + 1 : ℝ) : EReal))).2
  have hRefRec :
      (minimumSetEReal f).recessionCone =
        (sublevelSetEReal f (infReal + 1)).recessionCone :=
    hF.2.1 hMinNonempty (infReal + 1) hRefNonempty
  have hMinRecZero : (minimumSetEReal f).recessionCone = ({0} : Set (Fin n → ℝ)) := by
    exact
      (helperForText_21_3_3_bounded_iff_recessionCone_eq_singleton_zero_fin
        (S := minimumSetEReal f)
        hMinNonempty hMinClosed hMinConvex).1 hMinBounded
  have hRefRecZero :
      (sublevelSetEReal f (infReal + 1)).recessionCone = ({0} : Set (Fin n → ℝ)) := by
    rw [← hRefRec, hMinRecZero]
  have hRefBounded_set : Bornology.IsBounded (sublevelSetEReal f (infReal + 1)) :=
    (helperForText_21_3_3_bounded_iff_recessionCone_eq_singleton_zero_fin
      (S := sublevelSetEReal f (infReal + 1))
      hRefNonempty hRefClosed hRefConvex).2
      (show Set.recessionCone (sublevelSetEReal f (infReal + 1)) = ({0} : Set (Fin n → ℝ)) by
        simpa using hRefRecZero)
  have hRefBounded : Bornology.IsBounded (sublevelSetEReal f (infReal + 1)) := hRefBounded_set
  refine ⟨hInfFinite, hMinNonempty, hMinClosed, hMinBounded, hMinConvex, ?_⟩
  intro ε hε
  by_contra hεδ
  -- Route correction: instead of constructing the contradiction directly in the whole space,
  -- work inside the bounded reference sublevel `inf f + 1` and extract a convergent subsequence.
  have hbad :
      ∀ δ : ℝ, 0 < δ →
        ∃ x : Fin n → ℝ,
          f x ≤ functionInfimumEReal f + (δ : EReal) ∧
            ∀ z : Fin n → ℝ, z ∈ minimumSetEReal f → ε ≤ ‖z - x‖ := by
    intro δ hδ
    by_cases hgood :
        ∀ x : Fin n → ℝ,
          f x ≤ functionInfimumEReal f + (δ : EReal) →
            ∃ z : Fin n → ℝ, z ∈ minimumSetEReal f ∧ ‖z - x‖ < ε
    · exact False.elim (hεδ ⟨δ, hδ, hgood⟩)
    · push_neg at hgood
      rcases hgood with ⟨x, hx, hxfar⟩
      refine ⟨x, hx, ?_⟩
      intro z hz
      exact hxfar z hz
  choose xSeq hxSeqNear hxSeqFar using
    fun k : ℕ => hbad ((1 : ℝ) / ((k : ℝ) + 1)) (by
      have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      exact one_div_pos.mpr hpos)
  -- Every bad point lies in the fixed bounded reference sublevel because `1 / (k + 1) ≤ 1`.
  have hSeqMemRef : ∀ k : ℕ, xSeq k ∈ sublevelSetEReal f (infReal + 1) := by
    intro k
    have hfrac_le : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
      have hle_nat : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have hle : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        exact_mod_cast hle_nat
      simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hle)
    have hfrac_le_ereal : (((1 : ℝ) / ((k : ℝ) + 1) : ℝ) : EReal) ≤ (1 : EReal) := by
      exact_mod_cast hfrac_le
    have hxBound : f (xSeq k) ≤ functionInfimumEReal f + (1 : EReal) := by
      exact le_trans (hxSeqNear k) (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hfrac_le_ereal (functionInfimumEReal f))
    simpa [sublevelSetEReal, infReal, hInf_coe, add_assoc, add_left_comm, add_comm] using hxBound
  have hSeqRangeBounded : Bornology.IsBounded (Set.range xSeq) :=
    hRefBounded.subset (by
      intro y hy
      rcases hy with ⟨k, rfl⟩
      exact hSeqMemRef k)
  rcases hSeqRangeBounded.exists_pos_norm_le with ⟨R, hRpos, hR⟩
  have hSeqMemBall : ∀ k : ℕ, xSeq k ∈ Metric.closedBall (0 : Fin n → ℝ) R := by
    intro k
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR (xSeq k) ⟨k, rfl⟩
  rcases (isCompact_closedBall (0 : Fin n → ℝ) R).tendsto_subseq hSeqMemBall with
    ⟨x, _hxBall, φ, hφmono, hφtend⟩
  have hφ_ge : ∀ k : ℕ, k ≤ φ k := by
    intro k
    induction k with
    | zero =>
        exact Nat.zero_le _
    | succ k hk =>
        exact
          le_trans (Nat.succ_le_succ hk)
            (Nat.succ_le_of_lt (hφmono (Nat.lt_succ_self k)))
  have hLevelClosed :
      ∀ α : ℝ, IsClosed (sublevelSetEReal f α) := by
    intro α
    exact (lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hclosed.2 α
  have hxRef : x ∈ sublevelSetEReal f (infReal + 1) :=
    hRefClosed.mem_of_tendsto hφtend (Filter.Eventually.of_forall fun k => hSeqMemRef (φ k))
  -- The limit belongs to every tighter sublevel `inf f + 1 / (m + 1)`, hence attains the infimum.
  have hxLevel :
      ∀ m : ℕ, x ∈ sublevelSetEReal f (infReal + (1 : ℝ) / ((m : ℝ) + 1)) := by
    intro m
    have hEventuallyMem :
        ∀ᶠ k : ℕ in Filter.atTop,
          xSeq (φ k) ∈ sublevelSetEReal f (infReal + (1 : ℝ) / ((m : ℝ) + 1)) := by
      filter_upwards [Filter.eventually_ge_atTop m] with k hk
      have hkφ : m ≤ φ k := le_trans hk (hφ_ge k)
      have hfrac_le :
          (1 : ℝ) / ((φ k : ℝ) + 1) ≤ (1 : ℝ) / ((m : ℝ) + 1) := by
        have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have hle : (m : ℝ) + 1 ≤ (φ k : ℝ) + 1 := by
          have hle' : (m : ℝ) ≤ (φ k : ℝ) := by
            exact_mod_cast hkφ
          linarith
        simpa using (one_div_le_one_div_of_le hpos hle)
      have hfrac_le_ereal :
          ((((1 : ℝ) / ((φ k : ℝ) + 1)) : ℝ) : EReal) ≤
            ((((1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : EReal) := by
        exact_mod_cast hfrac_le
      have hxBound :
          f (xSeq (φ k)) ≤
            functionInfimumEReal f + ((((1 : ℝ) / ((m : ℝ) + 1)) : ℝ) : EReal) := by
        exact le_trans (hxSeqNear (φ k)) (by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hfrac_le_ereal (functionInfimumEReal f))
      simpa [sublevelSetEReal, infReal, hInf_coe, add_assoc, add_left_comm, add_comm] using hxBound
    exact (hLevelClosed _).mem_of_tendsto hφtend hEventuallyMem
  have hInf_le_fx : functionInfimumEReal f ≤ f x := by
    simpa [functionInfimumEReal] using (iInf_le (fun y => f y) x)
  have hfx_ne_bot : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
  have hfx_ne_top : f x ≠ (⊤ : EReal) := by
    rw [sublevelSetEReal] at hxRef
    have htop : (((infReal + 1 : ℝ)) : EReal) < (⊤ : EReal) := by
      exact lt_top_iff_ne_top.mpr (EReal.coe_ne_top _)
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hxRef htop)
  have hfx_coe : (((f x).toReal : ℝ) : EReal) = f x := by
    simpa using (EReal.coe_toReal (x := f x) hfx_ne_top hfx_ne_bot)
  have hInfReal_le : infReal ≤ (f x).toReal := by
    have hcast :
        (((functionInfimumEReal f).toReal : ℝ) : EReal) ≤ (((f x).toReal : ℝ) : EReal) := by
      simpa [hInf_coe, hfx_coe] using hInf_le_fx
    exact_mod_cast hcast
  have hfxReal_le : (f x).toReal ≤ infReal := by
    by_contra hgt
    have hgap : 0 < ((f x).toReal - infReal) / 2 := by
      linarith
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hgap
    have hxLevelm : x ∈ sublevelSetEReal f (infReal + (1 : ℝ) / ((m : ℝ) + 1)) := hxLevel m
    rw [sublevelSetEReal] at hxLevelm
    have hupperE :
        (((f x).toReal : ℝ) : EReal) ≤
          (((infReal + (1 : ℝ) / ((m : ℝ) + 1) : ℝ)) : EReal) := by
      simpa [hfx_coe] using hxLevelm
    have hupper :
        (f x).toReal ≤ infReal + (1 : ℝ) / ((m : ℝ) + 1) := by
      exact_mod_cast hupperE
    linarith
  have hfx_eq_inf : f x = functionInfimumEReal f := by
    calc
      f x = (((f x).toReal : ℝ) : EReal) := hfx_coe.symm
      _ = ((infReal : ℝ) : EReal) := by
        have : (f x).toReal = infReal := by linarith
        simp [this]
      _ = functionInfimumEReal f := hInf_coe
  have hxMin : x ∈ minimumSetEReal f := by
    simpa [minimumSetEReal] using hfx_eq_inf
  -- The bad subsequence stays at least `ε` away from every minimizer, but its limit is itself a
  -- minimizer, so the distance-to-limit tends to `0` and contradicts the uniform lower bound.
  have hFarSub : ∀ k : ℕ, ε ≤ dist (xSeq (φ k)) x := by
    intro k
    simpa [dist_eq_norm, norm_sub_rev] using hxSeqFar (φ k) x hxMin
  have hDistTend :
      Filter.Tendsto (fun k : ℕ => dist (xSeq (φ k)) x) Filter.atTop (nhds 0) := by
    simpa using
      hφtend.dist
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x))
  have hε_le_zero : ε ≤ 0 := by
    exact
      le_of_tendsto_of_tendsto tendsto_const_nhds hDistTend
        (Filter.Eventually.of_forall hFarSub)
  exact (not_le_of_gt hε) hε_le_zero

end Section27
end Chap06

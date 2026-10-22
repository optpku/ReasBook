/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part12

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

-- Proof sketch: treat this as a separate convex/convex translated-value statement rather than as
-- part of the earlier convex/concave perturbation setup. Use the ordinary convex Fenchel
-- conjugates `f⋆` and `g⋆`, identify `sup_{xStar} (g⋆ xStar - f⋆ xStar)` with the dual value
-- attached to the translated function `p(u) = inf_x (f x - g (x + u))`, then use closedness of
-- `f` and `g`, together with the book-level codomain restriction `∀ x, g x ≠ -∞`, and the
-- stated domain qualification to relate that value to
-- `liminf_{u → 0} p(u)`, bound the liminf by `p(0)`, and evaluate `p(0)` as
-- `inf_x (f x - g x)`.
/-- Helper for Lemma 31.0.12: every neighborhood of `0` sees the value `p(0)`, so the liminf of
the translated value function is bounded above by its value at `0`. -/
lemma helperForLemma_31_0_12_liminf_translatedDifferenceValueFunction_le_at_zero {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) :
    Filter.liminf (translatedDifferenceValueFunction (n := n) f g) (𝓝 (0 : Fin n → ℝ)) ≤
      translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) := by
  -- The point `u = 0` is frequently seen along `pure 0`, and `pure 0 ≤ 𝓝 0` lifts that witness
  -- to the neighborhood filter.
  have hfreqPure :
      ∃ᶠ u in pure (0 : Fin n → ℝ),
        translatedDifferenceValueFunction (n := n) f g u ≤
          translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) := by
    simp [Filter.Frequently]
  have hfreqNhds :
      ∃ᶠ u in 𝓝 (0 : Fin n → ℝ),
        translatedDifferenceValueFunction (n := n) f g u ≤
          translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) :=
    hfreqPure.filter_mono (pure_le_nhds (0 : Fin n → ℝ))
  -- A frequently occurring upper bound controls the liminf in the complete lattice `EReal`.
  exact Filter.liminf_le_of_frequently_le' hfreqNhds

/-- Helper for Lemma 31.0.12: evaluating the translated value function at `0` removes the
translation and recovers the primal infimum `inf_x (f x - g x)`. -/
lemma helperForLemma_31_0_12_translatedDifferenceValueFunction_at_zero_eq_functionInfimum
    {n : ℕ} (f g : (Fin n → ℝ) → EReal) :
    translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) =
      functionInfimumEReal (fun x => f x - g x) := by
  -- Setting `u = 0` in `p(u) = inf_x (f x - g (x + u))` leaves the original difference.
  simp [translatedDifferenceValueFunction, functionInfimumEReal]

/-- Helper for Lemma 31.0.12: bundle the valid tail relations in the textbook chain, namely
`liminf_{u → 0} p(u) ≤ p(0)` and `p(0) = inf_x (f x - g x)`. -/
lemma helperForLemma_31_0_12_liminf_tail_relations {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) :
    Filter.liminf (translatedDifferenceValueFunction (n := n) f g) (𝓝 (0 : Fin n → ℝ)) ≤
        translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) ∧
      translatedDifferenceValueFunction (n := n) f g (0 : Fin n → ℝ) =
        functionInfimumEReal (fun x => f x - g x) := by
  -- Reuse the two already established one-step facts and package them into one conjunction.
  constructor
  · -- The liminf upper bound comes from seeing the constant value `p(0)` arbitrarily close to `0`.
    exact helperForLemma_31_0_12_liminf_translatedDifferenceValueFunction_le_at_zero f g
  · -- Evaluating at `u = 0` removes the translation from the primal value function.
    exact helperForLemma_31_0_12_translatedDifferenceValueFunction_at_zero_eq_functionInfimum f g

/-- Helper for Lemma 31.0.12: in the one-dimensional quadratic counterexample, the translated
difference integrand has no real lower bound for any translation parameter `u`. -/
lemma helperForLemma_31_0_12_counterexampleQuadraticHasNoRealLowerBound
    (u : Fin 1 → ℝ) :
    ¬ HasRealLowerBound
      (fun x : Fin 1 → ℝ =>
        (0 : EReal) - ((((x + u) 0)^2 : ℝ) : EReal)) := by
  intro hLower
  rcases hLower with ⟨m, hm⟩
  let x : Fin 1 → ℝ := fun _ => |m| + 1 - u 0
  have hx_le := hm x
  have hx_eval :
      (fun y : Fin 1 → ℝ => (0 : EReal) - ((((y + u) 0)^2 : ℝ) : EReal)) x =
        (((-((|m| + 1)^2)) : ℝ) : EReal) := by
    -- Choose the test point so the translated coordinate equals `|m| + 1`.
    simp [x, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hx_eval] at hx_le
  have hx_real : m ≤ -((|m| + 1)^2) := by
    -- For this finite value, the extended-real inequality is the same real inequality.
    exact_mod_cast hx_le
  have habs : |m| < (|m| + 1)^2 := by
    -- The square of `|m| + 1` strictly dominates `|m|`.
    nlinarith [abs_nonneg m]
  have hnegabs : -|m| ≤ m := by
    -- Every real number lies above its negative absolute value.
    exact neg_abs_le m
  have hlt : -((|m| + 1)^2) < m := by
    -- Hence the chosen point falls strictly below the purported lower bound.
    nlinarith
  exact (not_le_of_gt hlt) hx_real

/-- Helper for Lemma 31.0.12: the one-dimensional quadratic counterexample forces the translated
value function to be `⊥` at every translation parameter. -/
lemma helperForLemma_31_0_12_counterexampleTranslatedDifferenceValueFunction_eq_bot
    (u : Fin 1 → ℝ) :
    translatedDifferenceValueFunction (n := 1)
      (fun _ => (0 : EReal))
      (fun x => (((x 0)^2 : ℝ) : EReal)) u = ⊥ := by
  -- Rewrite the translated value as an infimum and use the absence of any real lower bound.
  by_contra hne
  exact helperForLemma_31_0_12_counterexampleQuadraticHasNoRealLowerBound u <|
    (helperForTheorem_6_27_1_hasRealLowerBound_iff_functionInfimum_ne_bot _).2 <|
      by simpa [translatedDifferenceValueFunction, functionInfimumEReal] using hne

/-- Helper for Lemma 31.0.12: the same quadratic counterexample makes the liminf side of the
displayed equality equal to `⊥`. -/
lemma helperForLemma_31_0_12_counterexampleLiminf_eq_bot :
    Filter.liminf
        (translatedDifferenceValueFunction (n := 1)
          (fun _ => (0 : EReal))
          (fun x => (((x 0)^2 : ℝ) : EReal)))
        (𝓝 (0 : Fin 1 → ℝ)) = ⊥ := by
  have hfun :
      translatedDifferenceValueFunction (n := 1)
        (fun _ => (0 : EReal))
        (fun x => (((x 0)^2 : ℝ) : EReal)) =
      fun _ : Fin 1 → ℝ => (⊥ : EReal) := by
    -- The preceding pointwise computation shows that this translated value function is constant.
    funext u
    exact helperForLemma_31_0_12_counterexampleTranslatedDifferenceValueFunction_eq_bot u
  -- The liminf of a constant `⊥`-valued function is `⊥`.
  rw [hfun]
  simp

/-- Helper for Lemma 31.0.12: the same quadratic counterexample also makes the value at `0` and
the corresponding primal infimum equal to `⊥`. -/
lemma helperForLemma_31_0_12_counterexample_tailChain_eq_bot :
    translatedDifferenceValueFunction (n := 1)
        (fun _ => (0 : EReal))
        (fun x => (((x 0)^2 : ℝ) : EReal))
        (0 : Fin 1 → ℝ) = (⊥ : EReal) ∧
      functionInfimumEReal
        (fun x : Fin 1 → ℝ =>
          (0 : EReal) - ((((x 0)^2 : ℝ) : EReal))) = (⊥ : EReal) := by
  constructor
  · -- The pointwise counterexample computation already gives the value-function side at `u = 0`.
    exact helperForLemma_31_0_12_counterexampleTranslatedDifferenceValueFunction_eq_bot 0
  · -- Evaluating the translated value at `0` rewrites it back to the primal infimum.
    calc
      functionInfimumEReal
          (fun x : Fin 1 → ℝ =>
            (0 : EReal) - ((((x 0)^2 : ℝ) : EReal))) =
          translatedDifferenceValueFunction (n := 1)
            (fun _ => (0 : EReal))
            (fun x => (((x 0)^2 : ℝ) : EReal))
            (0 : Fin 1 → ℝ) := by
        symm
        exact
          helperForLemma_31_0_12_translatedDifferenceValueFunction_at_zero_eq_functionInfimum
            (n := 1) (fun _ => (0 : EReal)) (fun x => (((x 0)^2 : ℝ) : EReal))
      _ = (⊥ : EReal) :=
        helperForLemma_31_0_12_counterexampleTranslatedDifferenceValueFunction_eq_bot 0

/-- Helper for Lemma 31.0.12: the constant-zero counterexample function is proper closed convex
on `ℝ^1`, so the left-hand obstruction is not caused by missing hypotheses on `f`. -/
lemma helperForLemma_31_0_12_counterexampleZeroFunction_closed_and_proper :
    ClosedConvexFunction (fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
  -- The zero model is a finite constant function, so properness is immediate.
  have hProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
    simpa using properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))
  -- Closedness is just lower semicontinuity of the same constant map.
  have hClosed :
      ClosedConvexFunction (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
    exact
      (properConvexFunction_closed_iff_lowerSemicontinuous hProper).2
        (by
          simpa using
            (lowerSemicontinuous_const :
              LowerSemicontinuous (fun _ : Fin 1 → ℝ => (0 : EReal))))
  exact ⟨hClosed, hProper⟩

/-- Helper for Lemma 31.0.12: the quadratic counterexample function is proper closed convex on
`ℝ^1`, hence in particular lower semicontinuous as required for `g`. -/
lemma helperForLemma_31_0_12_counterexampleSquareFunction_closed_and_proper :
    ClosedConvexFunction (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) := by
  have hConvexReal :
      ConvexOn ℝ (Set.univ : Set (Fin 1 → ℝ)) (fun x : Fin 1 → ℝ => (x 0) ^ 2) := by
    -- Pull back convexity of `t ↦ t^2` along the sole coordinate projection.
    simpa using
      (convexOn_comp_proj (s := Set.univ) (f := fun t : ℝ => t ^ 2)
        (by
          simpa using
            (Even.convexOn_pow (𝕜 := ℝ) (n := 2) (hn := by decide))))
  let fEuclidean : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => (x 0) ^ 2
  let toFunctionLin : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] (Fin 1 → ℝ) :=
    (WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := Fin 1 → ℝ)).toLinearMap
  have hConvexEuclidean :
      ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin 1))) fEuclidean := by
    -- Section 10 packages the coercion from real convexity to the `EReal`-valued closed/proper
    -- statements used in this chapter.
    have hConvexEuclidean' :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (Fin 1 → ℝ)))
        (f := fun x : Fin 1 → ℝ => (x 0) ^ 2) hConvexReal toFunctionLin
    simpa [fEuclidean, toFunctionLin, WithLp.coe_linearEquiv] using hConvexEuclidean'
  have hProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) := by
    -- Lift the finite convex quadratic to an `EReal`-valued proper convex function.
    simpa [fEuclidean] using
      (Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn
        (n := 1) (f := fEuclidean) hConvexEuclidean)
  have hClosed :
      ClosedConvexFunction (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) := by
    -- The same Section 10 package gives lower semicontinuity, hence closedness.
    simpa [fEuclidean] using
      (Section10.closedConvexFunction_coe_comp_toLp_of_convexOn
        (n := 1) (f := fEuclidean) hConvexEuclidean)
  exact ⟨hClosed, hProper⟩

/-- Helper for Lemma 31.0.12: the explicit zero/quadratic counterexample satisfies all local
hypotheses of the target theorem, so it can be reused uniformly when specializing the false
header. -/
lemma helperForLemma_31_0_12_counterexample_satisfiesTargetHypotheses :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
      ClosedConvexFunction (fun _ : Fin 1 → ℝ => (0 : EReal)) ∧
      ClosedERealFunction (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) ∧
      (∀ x : Fin 1 → ℝ, (fun y : Fin 1 → ℝ => (((y 0)^2 : ℝ) : EReal)) x ≠ (⊥ : EReal)) ∧
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fun _ : Fin 1 → ℝ => (0 : EReal)) ∩
          effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
            (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))) := by
  rcases helperForLemma_31_0_12_counterexampleZeroFunction_closed_and_proper with
    ⟨hZeroClosed, hZeroProper⟩
  rcases helperForLemma_31_0_12_counterexampleSquareFunction_closed_and_proper with
    ⟨hSquareClosed, _hSquareProper⟩
  have hSquareNeBot :
      ∀ x : Fin 1 → ℝ, (fun y : Fin 1 → ℝ => (((y 0)^2 : ℝ) : EReal)) x ≠ (⊥ : EReal) := by
    -- The quadratic model only takes real values, so it never reaches `⊥`.
    intro x
    exact EReal.coe_ne_bot ((x 0)^2)
  have hDom :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fun _ : Fin 1 → ℝ => (0 : EReal)) ∩
          effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
            (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal))) := by
    -- Both counterexample functions are finite at the origin, so the primal domains intersect.
    refine ⟨0, ?_, ?_⟩
    · rw [effectiveDomain_eq]
      simp
    · rw [effectiveDomain_eq]
      constructor
      · simp
      · have hQuadraticAtOriginNeTop :
            ((((0 : Fin 1 → ℝ) 0)^2 : ℝ) : EReal) ≠ (⊤ : EReal) := by
          simp
        exact lt_top_iff_ne_top.mpr hQuadraticAtOriginNeTop
  -- Package the ready-made hypotheses in the order used by the specialization lemmas below.
  exact ⟨hZeroProper, hZeroClosed, hSquareClosed.2, hSquareNeBot, hDom⟩

/-- Helper for Lemma 31.0.12: the quadratic counterexample's Fenchel conjugate vanishes at the
origin because the quadratic itself is nonnegative and attains the value `0` at `x = 0`. -/
lemma helperForLemma_31_0_12_counterexampleSquareFunction_fenchelConjugate_at_zero :
    fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) 0 = (0 : EReal) := by
  -- The quadratic model is pointwise nonnegative.
  have hSquareNonneg :
      ∀ x : Fin 1 → ℝ, (0 : EReal) ≤ (((x 0)^2 : ℝ) : EReal) := by
    intro x
    exact_mod_cast sq_nonneg (x 0)
  -- At the origin the quadratic value is exactly `0`.
  have hSquareZero :
      (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) 0 = (0 : EReal) := by
    simp
  -- Squeeze the infimum of the quadratic between `0` and the sampled value at the origin.
  have hInfLower :
      (0 : EReal) ≤ iInf (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) := by
    refine le_iInf ?_
    intro x
    exact hSquareNonneg x
  have hInfUpper :
      iInf (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) ≤ (0 : EReal) := by
    -- Re-express the sampled value at `x = 0` as `0^2 = 0`.
    change iInf (fun x : Fin 1 → ℝ => ((x 0 : EReal)^2)) ≤ (0 : EReal)
    have hEval :
        iInf (fun x : Fin 1 → ℝ => ((x 0 : EReal)^2)) ≤ ((0 : EReal)^2) :=
      iInf_le (fun x : Fin 1 → ℝ => ((x 0 : EReal)^2)) (0 : Fin 1 → ℝ)
    simpa using hEval
  have hInfEq :
      iInf (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) = (0 : EReal) :=
    le_antisymm hInfUpper hInfLower
  -- Evaluate `f⋆ 0` as `- inf_x f x` and plug in the computed infimum.
  have hConjZero :
      fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) 0 =
        - iInf (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) := by
    simpa [EReal.coe_pow] using
      (fenchelConjugate_zero_eq_neg_iInf
        (n := 1) (f := fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)))
  calc
    fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) 0 =
        - iInf (fun x : Fin 1 → ℝ => (((x 0)^2 : ℝ) : EReal)) := hConjZero
    _ = (0 : EReal) := by simpa [hInfEq]


end Section31
end Chap06

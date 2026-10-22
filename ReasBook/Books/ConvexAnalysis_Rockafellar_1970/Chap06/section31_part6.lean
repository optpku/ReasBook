/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part5

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Lemma 31.0.4: the finite restricted split and the matching candidate estimate for
`g⋆` share the same support-function term, so the Section 13 cancellation argument yields the
desired dual witness. -/
lemma helperForLemma_31_0_4_dualGapWitnessFromRestrictedFiniteSplit {n : ℕ}
    {f g : (Fin n → ℝ) → EReal} (α : ℝ)
    (hf_poly : IsPolyhedralConvexFunction n f)
    (hg_poly : IsPolyhedralConvexFunction n g)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hdomCommon :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) g))
    (hPointwise : ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x) :
    ∃ y : Fin n → ℝ,
      fenchelConjugate n g y - fenchelConjugate n f y ≥ (α : EReal) := by
  let domG : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) g
  have hPointwiseOnCommon :
      ∀ x : Fin n → ℝ,
        x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
          (α : EReal) ≤ f x - g x := by
    intro x _hx
    exact hPointwise x
  have hShiftedOnDomainG :
      ∀ x : Fin n → ℝ, x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) g →
        (α : EReal) + g x ≤ f x := by
    intro x hxG
    exact
      helperForLemma_31_0_3_shiftedPointwiseBoundOnDomainG
        (n := n) (f := f) (g := g) α hg hPointwiseOnCommon hxG
  obtain ⟨z, y, hz_ne_top, hSplit⟩ :=
    helperForLemma_31_0_4_restrictedFiniteDualAttainedSplit_of_polyhedralPair
      (n := n) (f := f) (g := g) hf_poly hg_poly hf hg hdomCommon
  have hUpper :=
    helperForLemma_31_0_3_restrictedConjugateUpperBound
      (n := n) (f := f) (g := g) α hf hShiftedOnDomainG z
  have hDomGne : Set.Nonempty domG := by
    rcases hdomCommon with ⟨x0, _hx0F, hx0G⟩
    exact ⟨x0, hx0G⟩
  have hCandidate :=
    helperForLemma_31_0_4_supportFunctionCandidateBoundForG_of_polyhedralPair
      (n := n) (g := g) hg_poly hg hDomGne z y
  have hFstarProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf
  have hGstarProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g) :=
    proper_fenchelConjugate_of_proper (n := n) (f := g) hg
  have hFy_ne_bot : fenchelConjugate n f y ≠ (⊥ : EReal) := hFstarProper.2.2 y (by simp)
  have hGy_ne_bot : fenchelConjugate n g y ≠ (⊥ : EReal) := hGstarProper.2.2 y (by simp)
  rw [section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := domG)] at hSplit hCandidate
  have hSupport_ne_bot : supportFunctionEReal domG (z - y) ≠ (⊥ : EReal) :=
    section13_supportFunctionEReal_ne_bot_of_nonempty hDomGne (z - y)
  have hSupport_ne_top : supportFunctionEReal domG (z - y) ≠ (⊤ : EReal) := by
    intro hSupport_top
    have hTopValue :
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          = (⊤ : EReal) := by
      calc
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          = supportFunctionEReal domG (z - y) + fenchelConjugate n f y := hSplit
        _ = (⊤ : EReal) := by
          simpa [hSupport_top] using EReal.top_add_of_ne_bot hFy_ne_bot
    exact hz_ne_top hTopValue
  have hFy_ne_top : fenchelConjugate n f y ≠ (⊤ : EReal) := by
    intro hFy_top
    have hTopValue :
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          = (⊤ : EReal) := by
      calc
        fenchelConjugate n
            (fun x =>
              f x + indicatorFunction
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z
          = supportFunctionEReal domG (z - y) + fenchelConjugate n f y := hSplit
        _ = (⊤ : EReal) := by
          simpa [hFy_top] using EReal.add_top_of_ne_bot hSupport_ne_bot
    exact hz_ne_top hTopValue
  by_cases hGy_ne_top : fenchelConjugate n g y ≠ (⊤ : EReal)
  · -- The finite support term can now be cancelled from both sides exactly as in Lemma 31.0.3.
    have hCombined :
        supportFunctionEReal domG (z - y) + fenchelConjugate n f y
          ≤ (supportFunctionEReal domG (z - y) + fenchelConjugate n g y) - (α : EReal) := by
      calc
        supportFunctionEReal domG (z - y) + fenchelConjugate n f y
            =
              fenchelConjugate n
                (fun x =>
                  f x + indicatorFunction
                    (effectiveDomain (Set.univ : Set (Fin n → ℝ)) g) x) z := hSplit.symm
        _ ≤ fenchelConjugate n g z - (α : EReal) := hUpper
        _ ≤ (supportFunctionEReal domG (z - y) + fenchelConjugate n g y) - (α : EReal) := by
            exact EReal.sub_le_sub hCandidate le_rfl
    have hAdd :
        (supportFunctionEReal domG (z - y) + fenchelConjugate n f y) + (α : EReal)
          ≤ supportFunctionEReal domG (z - y) + fenchelConjugate n g y := by
      exact
        (EReal.le_sub_iff_add_le
          (Or.inl (EReal.coe_ne_bot α))
          (Or.inl (EReal.coe_ne_top α))).1 hCombined
    have hSupport_coe :
        (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal) =
          supportFunctionEReal domG (z - y) :=
      EReal.coe_toReal hSupport_ne_top hSupport_ne_bot
    have hCancelSupport :
        fenchelConjugate n f y + (α : EReal) ≤ fenchelConjugate n g y := by
      have hTransport :=
        (section13_addRightOrderIso (supportFunctionEReal domG (z - y)).toReal).symm.monotone
          (by
            simpa [add_assoc, add_left_comm, add_comm] using hAdd)
      have hTransport' :
          fenchelConjugate n f y + (↑α + supportFunctionEReal domG (z - y)) -
              supportFunctionEReal domG (z - y)
            ≤
              fenchelConjugate n g y + supportFunctionEReal domG (z - y) -
                supportFunctionEReal domG (z - y) := by
        simpa [section13_addRightOrderIso, hSupport_coe] using hTransport
      have hLeftRewrite :
          fenchelConjugate n f y + (↑α + supportFunctionEReal domG (z - y)) -
              supportFunctionEReal domG (z - y) =
            fenchelConjugate n f y + (α : EReal) := by
        rw [← hSupport_coe]
        calc
          fenchelConjugate n f y + (↑α + (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal)) -
              (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal)
            =
              (fenchelConjugate n f y + (α : EReal)) +
                  (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal) -
                (((supportFunctionEReal domG (z - y)).toReal : ℝ) : EReal) := by
                  simp [add_assoc, add_left_comm, add_comm]
          _ = fenchelConjugate n f y + (α : EReal) := by
                rw [EReal.add_sub_cancel_right]
      have hRightRewrite :
          fenchelConjugate n g y + supportFunctionEReal domG (z - y) -
              supportFunctionEReal domG (z - y) =
            fenchelConjugate n g y := by
        rw [← hSupport_coe, EReal.add_sub_cancel_right]
      exact hLeftRewrite ▸ hRightRewrite ▸ hTransport'
    have hGap :
        (α : EReal) ≤ fenchelConjugate n g y - fenchelConjugate n f y := by
      exact
        (EReal.le_sub_iff_add_le
          (Or.inr hGy_ne_bot)
          (Or.inr hGy_ne_top)).2
          (by simpa [add_assoc, add_left_comm, add_comm] using hCancelSupport)
    exact ⟨y, hGap⟩
  · -- If `g⋆ y = ⊤`, the dual gap is automatically infinite.
    have hGy_top : fenchelConjugate n g y = (⊤ : EReal) := by
      by_contra hGy_ne_top'
      exact hGy_ne_top hGy_ne_top'
    have hFy_coe :
        (((fenchelConjugate n f y).toReal : ℝ) : EReal) = fenchelConjugate n f y :=
      EReal.coe_toReal hFy_ne_top hFy_ne_bot
    refine ⟨y, ?_⟩
    calc
      (α : EReal) ≤ (⊤ : EReal) := by simp
      _ = fenchelConjugate n g y - fenchelConjugate n f y := by
        rw [hGy_top, ← hFy_coe]
        simpa using EReal.top_sub_coe ((fenchelConjugate n f y).toReal)

/-- Lemma 31.0.4 (Case of Bivariate Polyhedral Functions): if
`f, g : ℝ^n → ℝ ∪ {+∞}` are polyhedral convex functions and
`α = inf_x (f x - g x)` is a finite real number, then there exists `x* ∈ ℝ^n` such that
`g* (x*) - f* (x*) ≥ α`. In this `EReal` formalization, the primal value is represented by
`functionInfimumEReal (pointwisePrimalDifference f g) = α`, and the book's codomain
`ℝ ∪ {+∞}` is encoded by `IsBookPolyhedralConvexFunction`. -/
lemma fenchel_duality_attainability_of_supremum_for_polyhedral_pair {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf_poly : IsBookPolyhedralConvexFunction n f)
    (hg_poly : IsBookPolyhedralConvexFunction n g)
    (α : ℝ)
    (hα : functionInfimumEReal (pointwisePrimalDifference f g) = (α : EReal)) :
    ∃ xStar : Fin n → ℝ,
      fenchelConjugate n g xStar - fenchelConjugate n f xStar ≥ (α : EReal) := by
  rcases hf_poly with ⟨hf_poly_conv, hf_ne_bot⟩
  rcases hg_poly with ⟨hg_poly_conv, hg_ne_bot⟩
  -- The finite primal infimum first yields a common effective-domain point for the two functions.
  rcases
      helperForLemma_31_0_4_exists_commonEffectiveDomainPoint_of_finitePrimalInfimum
        (n := n) (f := f) (g := g) hf_ne_bot hg_ne_bot α hα with
    ⟨x0, hx0F, hx0G⟩
  have hf :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForLemma_31_0_3_polyhedralFunctionIsProperOnUniv_of_domainWitness
      (n := n) (g := f) hf_poly_conv hf_ne_bot ⟨x0, hx0F⟩
  have hg :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    helperForLemma_31_0_3_polyhedralFunctionIsProperOnUniv_of_domainWitness
      (n := n) (g := g) hg_poly_conv hg_ne_bot ⟨x0, hx0G⟩
  have hPointwise :
      ∀ x : Fin n → ℝ, (α : EReal) ≤ f x - g x :=
    helperForLemma_31_0_2_pointwiseLowerBoundFromInfimum f g α hα
  -- Route correction: the valid Chapter 20 bridge here is the direct polyhedral-family
  -- exactness for `(indicatorFunction (dom g), f)` and `(indicatorFunction (dom g), g)`,
  -- not the stronger mixed `ri (dom f) ∩ dom g` route from Lemma 31.0.3.
  exact
    helperForLemma_31_0_4_dualGapWitnessFromRestrictedFiniteSplit
      (n := n) (f := f) (g := g) α hf_poly_conv hg_poly_conv hf hg
      ⟨x0, hx0F, hx0G⟩ hPointwise

-- Proof sketch: use the closed proper convex hypotheses to identify each function with its
-- biconjugate, then compare the dual supremum with the primal infimum for `g - f`. As elsewhere
-- in this file, the primal side is represented by `commonEffectiveDomainDifference g f` so the
-- Lean statement matches the book's `g - f` on the common effective domain without introducing
-- the artifact `⊤ - ⊤ = ⊥`.
/-- Helper for Lemma 31.0.5: the counterexample's `g` is the everywhere-zero function on
`ℝ^1`. -/
def helperForLemma_31_0_5_counterexampleZeroFunction : (Fin 1 → ℝ) → EReal :=
  fun _ => (0 : EReal)

/-- Helper for Lemma 31.0.5: the counterexample's `f` is the quadratic function
`x ↦ (x 0)^2`. -/
def helperForLemma_31_0_5_counterexampleSquareFunction : (Fin 1 → ℝ) → EReal :=
  fun x => (((x 0) ^ 2 : ℝ) : EReal)

/-- Helper for Lemma 31.0.5: for the one-dimensional counterexample candidate `g = 0`,
`f x = (x 0)^2`, the guarded primal objective agrees everywhere with the pointwise value
`-(x 0)^2`. -/
lemma helperForLemma_31_0_5_counterexample_commonDifference_eq_negSquare
    (x : Fin 1 → ℝ) :
    commonEffectiveDomainDifference
        helperForLemma_31_0_5_counterexampleZeroFunction
        helperForLemma_31_0_5_counterexampleSquareFunction x =
      -((((x 0) ^ 2 : ℝ) : EReal)) := by
  -- Both model functions are finite everywhere, so the common-domain guard is inactive.
  have hZeroMem :
      x ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleZeroFunction := by
    rw [effectiveDomain_eq]
    simp [helperForLemma_31_0_5_counterexampleZeroFunction]
  have hSquareMem :
      x ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleSquareFunction := by
    rw [effectiveDomain_eq]
    constructor
    · simp
    · refine lt_top_iff_ne_top.mpr ?_
      change (((x 0 : ℝ) : EReal) ^ 2) ≠ (⊤ : EReal)
      rw [← EReal.coe_pow]
      exact EReal.coe_ne_top ((x 0) ^ 2)
  have hMem :
      x ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
            helperForLemma_31_0_5_counterexampleZeroFunction ∩
          effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
            helperForLemma_31_0_5_counterexampleSquareFunction :=
    ⟨hZeroMem, hSquareMem⟩
  -- After opening the guard, the value is exactly `0 - (x 0)^2`.
  rw [commonEffectiveDomainDifference, if_pos hMem]
  simp [helperForLemma_31_0_5_counterexampleZeroFunction,
    helperForLemma_31_0_5_counterexampleSquareFunction]

/-- Helper for Lemma 31.0.5: the same one-dimensional counterexample makes the guarded primal
infimum lie below every sampled value `-t^2`. -/
lemma helperForLemma_31_0_5_counterexample_primalInfimum_le_negSquare
    (t : ℝ) :
    functionInfimumEReal
        (commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleZeroFunction
          helperForLemma_31_0_5_counterexampleSquareFunction) ≤
      -(((t ^ 2 : ℝ) : EReal)) := by
  -- Evaluating the infimum at the constant vector `x 0 = t` gives the required upper bound.
  have hInfLe :
      functionInfimumEReal
          (commonEffectiveDomainDifference
            helperForLemma_31_0_5_counterexampleZeroFunction
            helperForLemma_31_0_5_counterexampleSquareFunction) ≤
        commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleZeroFunction
          helperForLemma_31_0_5_counterexampleSquareFunction
          (fun _ : Fin 1 => t) := by
    simpa [functionInfimumEReal] using
      iInf_le
        (commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleZeroFunction
          helperForLemma_31_0_5_counterexampleSquareFunction)
        (fun _ : Fin 1 => t)
  -- The previous helper computes that sampled value explicitly.
  simpa [helperForLemma_31_0_5_counterexample_commonDifference_eq_negSquare] using hInfLe

/-- Helper for Lemma 31.0.5: the same one-dimensional counterexample forces the guarded primal
infimum to be `⊥`. -/
lemma helperForLemma_31_0_5_counterexample_primalInfimum_eq_bot :
    functionInfimumEReal
        (commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleZeroFunction
          helperForLemma_31_0_5_counterexampleSquareFunction) =
      (⊥ : EReal) := by
  -- It is enough to show that the infimum lies below every real threshold.
  apply ereal_eq_bot_of_le_all_coe
  intro μ
  by_cases hμ : 0 ≤ μ
  · -- The sample `t = 0` already gives the value `0`, which is below every nonnegative `μ`.
    have hInfLeZero :=
      helperForLemma_31_0_5_counterexample_primalInfimum_le_negSquare (t := 0)
    have hZeroLeMu : (0 : EReal) ≤ (μ : EReal) := by
      exact_mod_cast hμ
    exact le_trans (by simpa using hInfLeZero) hZeroLeMu
  · -- For negative `μ`, the sample `t = sqrt (-μ)` makes the sampled value equal to `μ`.
    have hInfLeSqrt :=
      helperForLemma_31_0_5_counterexample_primalInfimum_le_negSquare
        (t := Real.sqrt (-μ))
    have hμneg : μ < 0 := lt_of_not_ge hμ
    have hNegNonneg : 0 ≤ -μ := by
      linarith
    have hSqrtValueLe :
        (-((((Real.sqrt (-μ)) ^ 2 : ℝ) : EReal)) : EReal) ≤ (μ : EReal) := by
      have hRealLe : -((Real.sqrt (-μ)) ^ 2 : ℝ) ≤ μ := by
        rw [Real.sq_sqrt hNegNonneg]
        linarith
      exact_mod_cast hRealLe
    exact le_trans hInfLeSqrt hSqrtValueLe

/-- Helper for Lemma 31.0.5: the Fenchel conjugate of the quadratic counterexample at the origin
is `0`. This follows from the identity `f⋆ 0 = - inf_x f x` and the observation that the
quadratic function is pointwise nonnegative and vanishes at the origin. -/
lemma helperForLemma_31_0_5_counterexampleSquareFunction_fenchelConjugate_at_zero :
    fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction 0 = (0 : EReal) := by
  -- The quadratic model function is pointwise nonnegative.
  have hSquareNonneg :
      ∀ x : Fin 1 → ℝ, (0 : EReal) ≤ helperForLemma_31_0_5_counterexampleSquareFunction x := by
    intro x
    change (0 : EReal) ≤ ((((x 0) ^ 2 : ℝ) : EReal))
    exact_mod_cast sq_nonneg (x 0)
  -- At the origin the quadratic value is exactly `0`.
  have hSquareZero :
      helperForLemma_31_0_5_counterexampleSquareFunction 0 = (0 : EReal) := by
    simp [helperForLemma_31_0_5_counterexampleSquareFunction]
  -- `inf_x f x` is squeezed between `0` (from pointwise nonnegativity) and the sampled value `f 0`.
  have hInfLower :
      (0 : EReal) ≤
        iInf (fun x : Fin 1 → ℝ => helperForLemma_31_0_5_counterexampleSquareFunction x) := by
    refine le_iInf ?_
    intro x
    exact hSquareNonneg x
  have hInfUpper :
      iInf (fun x : Fin 1 → ℝ => helperForLemma_31_0_5_counterexampleSquareFunction x) ≤
        (0 : EReal) := by
    simpa [hSquareZero] using
      (iInf_le
        (fun x : Fin 1 → ℝ => helperForLemma_31_0_5_counterexampleSquareFunction x)
        (0 : Fin 1 → ℝ))
  have hInfEq :
      iInf (fun x : Fin 1 → ℝ => helperForLemma_31_0_5_counterexampleSquareFunction x) =
        (0 : EReal) :=
    le_antisymm hInfUpper hInfLower
  -- Evaluate the conjugate at `0` as `- inf_x f x`.
  simpa [hInfEq] using
    (fenchelConjugate_zero_eq_neg_iInf
      (n := 1) (f := helperForLemma_31_0_5_counterexampleSquareFunction))

/-- Helper for Lemma 31.0.5: for the same one-dimensional counterexample, the dual supremum is
`0`. The zero function has conjugate `δ_{ {0} }`, so every nonzero dual point contributes `⊥`,
while the origin contributes `0` because the quadratic conjugate is nonnegative and vanishes at
`0`. -/
lemma helperForLemma_31_0_5_counterexample_dualSup_eq_zero :
    (⨆ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStar -
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar) =
      (0 : EReal) := by
  let dualGap : (Fin 1 → ℝ) → EReal := fun xStar =>
    fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStar -
      fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar
  have hSquareConjZero :
      fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction 0 = (0 : EReal) := by
    -- The extracted helper isolates the `xStar = 0` conjugate evaluation used in the supremum.
    exact helperForLemma_31_0_5_counterexampleSquareFunction_fenchelConjugate_at_zero
  have hZeroConj :
      fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction =
        indicatorFunction ({0} : Set (Fin 1 → ℝ)) := by
    -- The conjugate of the constant zero function is the singleton indicator at the origin.
    simpa [helperForLemma_31_0_5_counterexampleZeroFunction] using
      (section16_fenchelConjugate_const_zero (n := 1))
  have hZeroConjAtZero :
      fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction 0 = (0 : EReal) := by
    -- The singleton indicator vanishes at the origin.
    simpa [indicatorFunction] using congrArg (fun h => h 0) hZeroConj
  have hDualGapAtZero : dualGap 0 = (0 : EReal) := by
    -- The origin is the maximizing dual point with value `0`.
    simp [dualGap, hSquareConjZero, hZeroConjAtZero]
  apply le_antisymm
  · refine iSup_le ?_
    intro xStar
    by_cases hxStar : xStar = 0
    · -- At the origin the dual gap is exactly zero.
      simp [hxStar, hSquareConjZero, hZeroConjAtZero]
    · have hZeroConjAway :
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar =
            (⊤ : EReal) := by
        -- Away from the origin, the singleton indicator equals `⊤`.
        simpa [indicatorFunction, hxStar] using congrArg (fun h => h xStar) hZeroConj
      -- Subtracting `⊤` collapses the dual gap to `⊥`, hence it is certainly at most `0`.
      simp [hZeroConjAway]
  · -- The origin term already gives the lower bound `0 ≤ sup dualGap`.
    rw [← hDualGapAtZero]
    exact le_iSup dualGap 0

/-- Helper for Lemma 31.0.5: the explicit quadratic/zero counterexample pair directly refutes the
equality conclusion in dimension one. -/
lemma helperForLemma_31_0_5_counterexample_conclusion_fails :
    (⨆ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStar -
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar) ≠
      functionInfimumEReal
        (commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleZeroFunction
          helperForLemma_31_0_5_counterexampleSquareFunction) := by
  -- Rewrite both sides using the already-computed exact values for this counterexample.
  intro hEq
  have hZeroEqBot : (0 : EReal) = (⊥ : EReal) := by
    -- The forced equality collapses to `0 = ⊥`.
    simpa [helperForLemma_31_0_5_counterexample_dualSup_eq_zero,
      helperForLemma_31_0_5_counterexample_primalInfimum_eq_bot] using hEq
  -- But `0` is not `⊥` in `EReal`.
  have hZeroNeBot : (0 : EReal) ≠ (⊥ : EReal) := by
    -- `simp` discharges the fact that a real coercion cannot be bottom.
    simp
  exact hZeroNeBot hZeroEqBot

/-- Helper for Lemma 31.0.5: for the swapped ordering `f = 0`, `g x = (x 0)^2`, the guarded
primal objective `g - f` agrees everywhere with the pointwise square. -/
lemma helperForLemma_31_0_5_swappedCounterexample_commonDifference_eq_square
    (x : Fin 1 → ℝ) :
    commonEffectiveDomainDifference
        helperForLemma_31_0_5_counterexampleSquareFunction
        helperForLemma_31_0_5_counterexampleZeroFunction x =
      (((x 0) ^ 2 : ℝ) : EReal) := by
  -- Both model functions are finite everywhere, so the common-domain guard is inactive.
  have hSquareMem :
      x ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleSquareFunction := by
    rw [effectiveDomain_eq]
    constructor
    · simp
    · refine lt_top_iff_ne_top.mpr ?_
      change (((x 0 : ℝ) : EReal) ^ 2) ≠ (⊤ : EReal)
      rw [← EReal.coe_pow]
      exact EReal.coe_ne_top ((x 0) ^ 2)
  have hZeroMem :
      x ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleZeroFunction := by
    rw [effectiveDomain_eq]
    simp [helperForLemma_31_0_5_counterexampleZeroFunction]
  have hMem :
      x ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
            helperForLemma_31_0_5_counterexampleSquareFunction ∩
          effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
            helperForLemma_31_0_5_counterexampleZeroFunction :=
    ⟨hSquareMem, hZeroMem⟩
  -- After opening the guard, the value is exactly `(x 0)^2 - 0`.
  rw [commonEffectiveDomainDifference, if_pos hMem]
  simp [helperForLemma_31_0_5_counterexampleZeroFunction,
    helperForLemma_31_0_5_counterexampleSquareFunction]

/-- Helper for Lemma 31.0.5: the swapped ordering `f = 0`, `g x = (x 0)^2` has guarded primal
infimum `0`. -/
lemma helperForLemma_31_0_5_swappedCounterexample_primalInfimum_eq_zero :
    functionInfimumEReal
        (commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleSquareFunction
          helperForLemma_31_0_5_counterexampleZeroFunction) =
      (0 : EReal) := by
  -- Bound the infimum above by sampling at the origin and below using pointwise nonnegativity.
  apply le_antisymm
  · have hInfLe :
        functionInfimumEReal
            (commonEffectiveDomainDifference
              helperForLemma_31_0_5_counterexampleSquareFunction
              helperForLemma_31_0_5_counterexampleZeroFunction) ≤
          commonEffectiveDomainDifference
            helperForLemma_31_0_5_counterexampleSquareFunction
            helperForLemma_31_0_5_counterexampleZeroFunction 0 := by
      simpa [functionInfimumEReal] using
        iInf_le
          (commonEffectiveDomainDifference
            helperForLemma_31_0_5_counterexampleSquareFunction
            helperForLemma_31_0_5_counterexampleZeroFunction)
          (0 : Fin 1 → ℝ)
    -- The sampled value is `0^2 = 0`.
    simpa [helperForLemma_31_0_5_swappedCounterexample_commonDifference_eq_square] using hInfLe
  · -- Every sampled value is a square, hence nonnegative.
    refine le_iInf ?_
    intro x
    have hSquareNonneg : (0 : EReal) ≤ (((x 0) ^ 2 : ℝ) : EReal) := by
      exact_mod_cast sq_nonneg (x 0)
    simpa [helperForLemma_31_0_5_swappedCounterexample_commonDifference_eq_square] using hSquareNonneg

/-- Helper for Lemma 31.0.5: the Fenchel conjugate of the quadratic model function at the dual
point `x⋆ = 1` is bounded above by `1`, hence it is not `⊤`. -/
lemma helperForLemma_31_0_5_counterexampleSquareFunction_fenchelConjugate_le_one_at_one :
    fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction
        (fun _ : Fin 1 => (1 : ℝ)) ≤
      (1 : EReal) := by
  -- Use the characterization of `f⋆ b ≤ μ` as a pointwise affine bound `⟪x,b⟫ - μ ≤ f x`.
  refine
    (fenchelConjugate_le_coe_iff_affine_le (n := 1)
        (f := helperForLemma_31_0_5_counterexampleSquareFunction)
        (b := (fun _ : Fin 1 => (1 : ℝ))) (μ := 1)).2 ?_
  intro x
  -- Reduce the dot product `⟪x,1⟫` to the single coordinate `x 0` and apply the inequality
  -- `t - 1 ≤ t^2`.
  have hReal : x ⬝ᵥ (fun _ : Fin 1 => (1 : ℝ)) - 1 ≤ (x 0) ^ 2 := by
    have hCoord : (x 0 : ℝ) - 1 ≤ (x 0) ^ 2 := by
      nlinarith
    simpa [dotProduct] using hCoord
  have hEReal :
      ((x ⬝ᵥ (fun _ : Fin 1 => (1 : ℝ)) - 1 : ℝ) : EReal) ≤
        (((x 0) ^ 2 : ℝ) : EReal) := by
    exact_mod_cast hReal
  simpa [helperForLemma_31_0_5_counterexampleSquareFunction] using hEReal

/-- Helper for Lemma 31.0.5: swapping the quadratic/zero pair shows the dual supremum can be
`⊤` even when the guarded primal infimum is finite, so guarding only against `⊥` is not enough
to make the theorem true. -/
lemma helperForLemma_31_0_5_swappedCounterexample_dualSup_eq_top :
    (⨆ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar -
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStar) =
      (⊤ : EReal) := by
  -- Exhibit an explicit dual point where the objective already equals `⊤`.
  let xStarOne : Fin 1 → ℝ := fun _ => 1
  have hxStarOne : xStarOne ≠ 0 := by
    intro hx
    have hx0 := congrArg (fun f : Fin 1 → ℝ => f 0) hx
    simp [xStarOne] at hx0
  have hZeroConj :
      fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction =
        indicatorFunction ({0} : Set (Fin 1 → ℝ)) := by
    -- The conjugate of the constant zero function is the singleton indicator at the origin.
    simpa [helperForLemma_31_0_5_counterexampleZeroFunction] using
      (section16_fenchelConjugate_const_zero (n := 1))
  have hZeroConjAtOne :
      fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStarOne =
        (⊤ : EReal) := by
    -- The singleton indicator is `⊤` away from the origin.
    simpa [indicatorFunction, hxStarOne] using congrArg (fun h => h xStarOne) hZeroConj
  have hSquareConjNeTop :
      fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStarOne ≠
        (⊤ : EReal) := by
    have hBound :
        fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStarOne ≤
          (1 : EReal) := by
      simpa [xStarOne] using
        helperForLemma_31_0_5_counterexampleSquareFunction_fenchelConjugate_le_one_at_one
    intro hTop
    have hTopLe : (⊤ : EReal) ≤ (1 : EReal) := by
      simpa [hTop] using hBound
    exact (not_top_le_coe 1) hTopLe
  have hTermTop :
      fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStarOne -
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStarOne =
        (⊤ : EReal) := by
    -- Once the left term is `⊤`, subtracting any non-top value stays at `⊤`.
    rw [hZeroConjAtOne]
    simpa using (EReal.top_sub hSquareConjNeTop)
  -- The `xStarOne` term already attains `⊤`, hence the supremum is `⊤`.
  refine le_antisymm le_top ?_
  have hLe :
      fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStarOne -
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStarOne ≤
        (⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar -
            fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStar) :=
    le_iSup
      (fun xStar : Fin 1 → ℝ =>
        fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar -
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStar)
      xStarOne
  simpa [hTermTop] using hLe

/-- Helper for Lemma 31.0.5: the swapped counterexample separates the dual supremum `⊤` from the
guarded primal infimum `0`. -/
lemma helperForLemma_31_0_5_swappedCounterexample_dualSup_ne_primalInfimum :
    (⨆ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar -
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStar) ≠
      functionInfimumEReal
        (commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleSquareFunction
          helperForLemma_31_0_5_counterexampleZeroFunction) := by
  -- Rewrite both sides using the explicit swapped evaluations `⊤` and `0`.
  rw [helperForLemma_31_0_5_swappedCounterexample_dualSup_eq_top,
    helperForLemma_31_0_5_swappedCounterexample_primalInfimum_eq_zero]
  simp

/-- Helper for Lemma 31.0.5: the one-dimensional counterexample already separates the dual
supremum from the guarded primal infimum, so the unrestricted Chapter 31 equality cannot hold as
stated. -/
lemma helperForLemma_31_0_5_counterexample_dualSup_ne_primalInfimum :
    (⨆ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStar -
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar) ≠
      functionInfimumEReal
        (commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleZeroFunction
          helperForLemma_31_0_5_counterexampleSquareFunction) := by
  -- The previously computed counterexample values reduce the obstruction to `0 ≠ ⊥`.
  rw [helperForLemma_31_0_5_counterexample_dualSup_eq_zero,
    helperForLemma_31_0_5_counterexample_primalInfimum_eq_bot]
  simp

/-- Helper for Lemma 31.0.5: in the same one-dimensional counterexample, the guarded primal
infimum is strictly smaller than the dual supremum (`⊥ < 0`). -/
lemma helperForLemma_31_0_5_counterexample_primalInfimum_lt_dualSup :
    functionInfimumEReal
        (commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleZeroFunction
          helperForLemma_31_0_5_counterexampleSquareFunction) <
      (⨆ xStar : Fin 1 → ℝ,
        fenchelConjugate 1 helperForLemma_31_0_5_counterexampleSquareFunction xStar -
          fenchelConjugate 1 helperForLemma_31_0_5_counterexampleZeroFunction xStar) := by
  -- Rewrite both sides using the explicit counterexample evaluations.
  rw [helperForLemma_31_0_5_counterexample_primalInfimum_eq_bot,
    helperForLemma_31_0_5_counterexample_dualSup_eq_zero]
  -- The strict inequality is just `⊥ < (0 : EReal)`.
  simpa using (EReal.bot_lt_coe (0 : ℝ))

/-- Helper for Lemma 31.0.5: the counterexample zero function is closed convex and proper on
`ℝ^1`, so it really satisfies the target theorem's hypotheses. -/
lemma helperForLemma_31_0_5_counterexampleZeroFunction_closed_and_proper :
    ClosedConvexFunction helperForLemma_31_0_5_counterexampleZeroFunction ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleZeroFunction := by
  -- The zero model is just a finite constant function, so properness is immediate.
  have hProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleZeroFunction := by
    simpa [helperForLemma_31_0_5_counterexampleZeroFunction] using
      (properConvexFunctionOn_const (n := 1) 0)
  -- Closedness then reduces to lower semicontinuity of a constant map.
  have hClosed :
      ClosedConvexFunction helperForLemma_31_0_5_counterexampleZeroFunction := by
    exact
      (properConvexFunction_closed_iff_lowerSemicontinuous hProper).2
        (by
          simpa [helperForLemma_31_0_5_counterexampleZeroFunction] using
            (lowerSemicontinuous_const :
              LowerSemicontinuous (fun _ : Fin 1 → ℝ => (0 : EReal))))
  exact ⟨hClosed, hProper⟩

/-- Helper for Lemma 31.0.5: the quadratic counterexample function is also closed convex and
proper on `ℝ^1`, so the Chapter 31 obstruction is not caused by missing regularity hypotheses on
the example itself. -/
lemma helperForLemma_31_0_5_counterexampleSquareFunction_closed_and_proper :
    ClosedConvexFunction helperForLemma_31_0_5_counterexampleSquareFunction ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleSquareFunction := by
  have hConvexReal :
      ConvexOn ℝ (Set.univ : Set (Fin 1 → ℝ)) (fun x : Fin 1 → ℝ => (x 0) ^ 2) := by
    -- Pull back scalar convexity of `t ↦ t^2` along the sole coordinate projection.
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
    -- Section 10 works on the Euclidean-space presentation of `ℝ^1`, so transport the convexity.
    have hConvexEuclidean' :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (Fin 1 → ℝ)))
        (f := fun x : Fin 1 → ℝ => (x 0) ^ 2) hConvexReal toFunctionLin
    simpa [fEuclidean, toFunctionLin, WithLp.coe_linearEquiv] using hConvexEuclidean'
  have hProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleSquareFunction := by
    -- The standard `EReal` lift of a finite convex function on all of `ℝ^1` is proper.
    simpa [helperForLemma_31_0_5_counterexampleSquareFunction, fEuclidean] using
      (Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn
        (n := 1) (f := fEuclidean) hConvexEuclidean)
  have hClosed :
      ClosedConvexFunction helperForLemma_31_0_5_counterexampleSquareFunction := by
    -- The same lift is lower semicontinuous, hence closed convex.
    simpa [helperForLemma_31_0_5_counterexampleSquareFunction, fEuclidean] using
      (Section10.closedConvexFunction_coe_comp_toLp_of_convexOn
        (n := 1) (f := fEuclidean) hConvexEuclidean)
  exact ⟨hClosed, hProper⟩

/-- Helper for Lemma 31.0.5: the standard one-dimensional counterexample satisfies all four
closed/proper assumptions appearing in the target theorem. -/
lemma helperForLemma_31_0_5_counterexample_satisfies_target_hypotheses :
    ClosedConvexFunction helperForLemma_31_0_5_counterexampleSquareFunction ∧
      ClosedConvexFunction helperForLemma_31_0_5_counterexampleZeroFunction ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleSquareFunction ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleZeroFunction := by
  -- Bundle the two separate regularity checks so the remaining blocker is purely the false
  -- conclusion of the target theorem.
  rcases helperForLemma_31_0_5_counterexampleSquareFunction_closed_and_proper with
    ⟨hSquareClosed, hSquareProper⟩
  rcases helperForLemma_31_0_5_counterexampleZeroFunction_closed_and_proper with
    ⟨hZeroClosed, hZeroProper⟩
  exact ⟨hSquareClosed, hZeroClosed, hSquareProper, hZeroProper⟩

/-- Helper for Lemma 31.0.5: the swapped counterexample pair `f = 0`, `g x = (x 0)^2` also
satisfies all four closed/proper hypotheses appearing in the target theorem. This isolates the
fact that the second obstruction is not caused by dropping assumptions, but by the mismatch
between the dual expression and the guarded primal infimum in this `EReal` encoding. -/
lemma helperForLemma_31_0_5_swappedCounterexample_satisfies_target_hypotheses :
    ClosedConvexFunction helperForLemma_31_0_5_counterexampleZeroFunction ∧
      ClosedConvexFunction helperForLemma_31_0_5_counterexampleSquareFunction ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleZeroFunction ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        helperForLemma_31_0_5_counterexampleSquareFunction := by
  -- Reuse the individual closed-and-proper facts and then bundle them in the order needed for the
  -- swapped witness.
  rcases helperForLemma_31_0_5_counterexampleZeroFunction_closed_and_proper with
    ⟨hZeroClosed, hZeroProper⟩
  rcases helperForLemma_31_0_5_counterexampleSquareFunction_closed_and_proper with
    ⟨hSquareClosed, hSquareProper⟩
  exact ⟨hZeroClosed, hSquareClosed, hZeroProper, hSquareProper⟩

/-- Helper for Lemma 31.0.5: swapping the quadratic/zero pair yields a counterexample with a
finite primal value `0` but an infinite dual value `⊤`. In particular, adding a guard like
`functionInfimumEReal (commonEffectiveDomainDifference g f) ≠ ⊥` is still insufficient to make
the lemma statement true. -/
lemma helperForLemma_31_0_5_existsDimensionOneCounterexampleWithFinitePrimalValue :
    ∃ (f g : (Fin 1 → ℝ) → EReal),
      ClosedConvexFunction f ∧
      ClosedConvexFunction g ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g ∧
      (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
        (⊤ : EReal) ∧
      functionInfimumEReal (commonEffectiveDomainDifference g f) = (0 : EReal) := by
  -- Use the swapped pair `f = 0`, `g x = (x 0)^2`; both are already known to be closed and proper.
  rcases helperForLemma_31_0_5_counterexampleZeroFunction_closed_and_proper with
    ⟨hf_closed, hf_proper⟩
  rcases helperForLemma_31_0_5_counterexampleSquareFunction_closed_and_proper with
    ⟨hg_closed, hg_proper⟩
  refine ⟨helperForLemma_31_0_5_counterexampleZeroFunction,
    helperForLemma_31_0_5_counterexampleSquareFunction,
    hf_closed, hg_closed, hf_proper, hg_proper, ?_, ?_⟩
  · -- The dual side is exactly `⊤` for this swapped pair.
    exact helperForLemma_31_0_5_swappedCounterexample_dualSup_eq_top
  · -- The guarded primal infimum is the finite value `0`.
    exact helperForLemma_31_0_5_swappedCounterexample_primalInfimum_eq_zero

/-- Helper for Lemma 31.0.5: the same one-dimensional witness already packages the exact failure
mode of the theorem header, namely dual value `0` and primal value `⊥` under all target
hypotheses. -/
lemma helperForLemma_31_0_5_existsDimensionOneCounterexampleWithExactValues :
    ∃ (f g : (Fin 1 → ℝ) → EReal),
      ClosedConvexFunction f ∧
      ClosedConvexFunction g ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g ∧
      (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
        (0 : EReal) ∧
      functionInfimumEReal (commonEffectiveDomainDifference g f) = (⊥ : EReal) := by
  -- Package the explicit quadratic/zero pair together with both already-computed objective values.
  rcases helperForLemma_31_0_5_counterexample_satisfies_target_hypotheses with
    ⟨hSquareClosed, hZeroClosed, hSquareProper, hZeroProper⟩
  refine ⟨helperForLemma_31_0_5_counterexampleSquareFunction,
    helperForLemma_31_0_5_counterexampleZeroFunction,
    hSquareClosed, hZeroClosed, hSquareProper, hZeroProper, ?_, ?_⟩
  · -- The dual side is exactly the finite value `0`.
    exact helperForLemma_31_0_5_counterexample_dualSup_eq_zero
  · -- The guarded primal side is exactly `⊥`.
    exact helperForLemma_31_0_5_counterexample_primalInfimum_eq_bot

/-- Helper for Lemma 31.0.5: there already exists a closed/proper convex counterexample in
`ℝ^1`, so the unrestricted theorem header is false before any further local proof search begins.
-/
lemma helperForLemma_31_0_5_existsDimensionOneCounterexample :
    ∃ (f g : (Fin 1 → ℝ) → EReal),
      ClosedConvexFunction f ∧
      ClosedConvexFunction g ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g ∧
      (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) ≠
        functionInfimumEReal (commonEffectiveDomainDifference g f) := by
  -- The stronger exact-value package isolates the obstruction as finite dual value versus
  -- bottom primal value.
  rcases helperForLemma_31_0_5_existsDimensionOneCounterexampleWithExactValues with
    ⟨f, g, hf_closed, hg_closed, hf_proper, hg_proper, hDual, hPrimal⟩
  refine ⟨f, g, hf_closed, hg_closed, hf_proper, hg_proper, ?_⟩
  -- Rewriting the candidate equality by the exact values reduces it to `0 ≠ ⊥`.
  rw [hDual, hPrimal]
  simp

/-- Helper for Lemma 31.0.5: even the dimension-one specialization of the unrestricted
closed/proper convex Fenchel equality is false, so the current theorem header cannot be repaired
by a local proof change alone. -/
lemma helperForLemma_31_0_5_targetSchemaFailsInDimensionOne :
    ¬ ∀ (f g : (Fin 1 → ℝ) → EReal),
        ClosedConvexFunction f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g →
        (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
          functionInfimumEReal (commonEffectiveDomainDifference g f) := by
  intro hFenchel
  -- Extract the explicit witness that already falsifies the dimension-one schema.
  rcases helperForLemma_31_0_5_existsDimensionOneCounterexample with
    ⟨f, g, hf_closed, hg_closed, hf_proper, hg_proper, hCounterexample⟩
  -- Any universal theorem would force equality for that witness, contradicting the packaged
  -- counterexample.
  exact hCounterexample (hFenchel f g hf_closed hg_closed hf_proper hg_proper)

/-- Helper for Lemma 31.0.5: any attempted proof of the unrestricted all-dimensions theorem
schema immediately specializes to the explicit one-dimensional counterexample, so such a proof
term implies `False`. -/
lemma helperForLemma_31_0_5_targetHeaderSpecializesToZeroEqBot
    (hFenchel :
      ∀ {n : ℕ} (f g : (Fin n → ℝ) → EReal),
        ClosedConvexFunction f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g →
        (⨆ xStar : Fin n → ℝ, fenchelConjugate n f xStar - fenchelConjugate n g xStar) =
          functionInfimumEReal (commonEffectiveDomainDifference g f)) :
    (0 : EReal) = (⊥ : EReal) := by
  -- Route correction: specialize the claimed theorem directly to the explicit quadratic/zero
  -- witness, now packaged together with its exact dual and primal values, so the contradiction
  -- appears as the concrete absurd identity `0 = ⊥`.
  rcases helperForLemma_31_0_5_existsDimensionOneCounterexampleWithExactValues with
    ⟨f, g, hf_closed, hg_closed, hf_proper, hg_proper, hDual, hPrimal⟩
  have hSpecialized :
      (⨆ xStar : Fin 1 → ℝ,
          fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
        functionInfimumEReal (commonEffectiveDomainDifference g f) := by
    -- The theorem schema forces equality for the already-formalized witness.
    exact hFenchel (n := 1) f g hf_closed hg_closed hf_proper hg_proper
  -- The packaged exact values collapse that forced equality to `0 = ⊥`.
  calc
    (0 : EReal) = (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) :=
      hDual.symm
    _ = functionInfimumEReal (commonEffectiveDomainDifference g f) := hSpecialized
    _ = (⊥ : EReal) := hPrimal

/-- Helper for Lemma 31.0.5: any attempted proof of the unrestricted all-dimensions theorem
schema immediately specializes to the explicit one-dimensional counterexample, so such a proof
term implies `False`. -/
lemma helperForLemma_31_0_5_targetHeaderImpliesFalse
    (hFenchel :
      ∀ {n : ℕ} (f g : (Fin n → ℝ) → EReal),
        ClosedConvexFunction f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g →
        (⨆ xStar : Fin n → ℝ, fenchelConjugate n f xStar - fenchelConjugate n g xStar) =
          functionInfimumEReal (commonEffectiveDomainDifference g f)) :
    False := by
  -- The sharper specialization helper already reduces the alleged theorem to the absurd equation
  -- `0 = ⊥`.
  have hZeroEqBot :
      (0 : EReal) = (⊥ : EReal) :=
    helperForLemma_31_0_5_targetHeaderSpecializesToZeroEqBot hFenchel
  -- That equality is impossible in `EReal`, so the theorem schema implies `False`.
  have hZeroNeBot : (0 : EReal) ≠ (⊥ : EReal) := by
    simp
  exact hZeroNeBot hZeroEqBot

/-- Helper for Lemma 31.0.5: the real value `0` in `EReal` is not `⊥`, so any derived identity
`(0 : EReal) = ⊥` is contradictory. -/
lemma helperForLemma_31_0_5_zero_ne_bot : (0 : EReal) ≠ (⊥ : EReal) := by
  -- `simp` reduces the claim to the fact that a real coercion is never bottom.
  simp

/-- Helper for Lemma 31.0.5: a real lower bound forces the infimum of an `EReal`-valued function
to be different from `⊥`. -/
lemma helperForLemma_31_0_5_infimum_ne_bot_of_hasRealLowerBound {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hBound : HasRealLowerBound f) :
    functionInfimumEReal f ≠ (⊥ : EReal) := by
  -- Extract a real lower bound `m` and push it through the `iInf` defining the infimum.
  rcases hBound with ⟨m, hm⟩
  have hm_le_inf : (m : EReal) ≤ functionInfimumEReal f := by
    -- `functionInfimumEReal` is an `iInf`, so it dominates every uniform lower bound.
    simpa [functionInfimumEReal] using (le_iInf hm)
  intro hInf_bot
  -- If the infimum were `⊥`, then the real coercion `m` would also have to be `⊥`, contradiction.
  have hm_le_bot : (m : EReal) ≤ (⊥ : EReal) := by
    simpa [hInf_bot] using hm_le_inf
  exact (EReal.coe_ne_bot m) (le_antisymm hm_le_bot bot_le)

/-- Helper for Lemma 31.0.5: the guarded primal objective in the one-dimensional counterexample
cannot admit a real lower bound, since its global infimum is `⊥`. -/
lemma helperForLemma_31_0_5_counterexample_noRealLowerBound :
    ¬ HasRealLowerBound
      (commonEffectiveDomainDifference
        helperForLemma_31_0_5_counterexampleZeroFunction
        helperForLemma_31_0_5_counterexampleSquareFunction) := by
  intro hBound
  -- A real lower bound would force the infimum to be different from `⊥`.
  have hInf_ne_bot :
      functionInfimumEReal
          (commonEffectiveDomainDifference
            helperForLemma_31_0_5_counterexampleZeroFunction
            helperForLemma_31_0_5_counterexampleSquareFunction) ≠ (⊥ : EReal) :=
    helperForLemma_31_0_5_infimum_ne_bot_of_hasRealLowerBound
      (f :=
        commonEffectiveDomainDifference
          helperForLemma_31_0_5_counterexampleZeroFunction
          helperForLemma_31_0_5_counterexampleSquareFunction) hBound
  -- But the infimum was computed explicitly as `⊥` earlier.
  exact hInf_ne_bot helperForLemma_31_0_5_counterexample_primalInfimum_eq_bot

/-- Helper for Lemma 31.0.5: the unrestricted Fenchel-duality schema already fails as a
dimension-polymorphic theorem statement, because its `n = 1` specialization is refuted by the
explicit counterexample above. -/
lemma helperForLemma_31_0_5_targetSchemaFails :
    ¬ ∀ {n : ℕ} (f g : (Fin n → ℝ) → EReal),
        ClosedConvexFunction f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g →
        (⨆ xStar : Fin n → ℝ, fenchelConjugate n f xStar - fenchelConjugate n g xStar) =
          functionInfimumEReal (commonEffectiveDomainDifference g f) := by
  intro hFenchel
  -- The stronger contradiction helper packages the one-dimensional specialization as `False`.
  exact helperForLemma_31_0_5_targetHeaderImpliesFalse hFenchel

/-- Helper for Lemma 31.0.5: even guarding the equality by assuming the primal infimum is not
`⊥` does not fix the statement in this `EReal` encoding. The swapped quadratic/zero pair has
finite primal infimum `0` but dual supremum `⊤`. -/
lemma helperForLemma_31_0_5_targetSchemaFailsEvenIfPrimalInfimumNeBot :
    ¬ ∀ (f g : (Fin 1 → ℝ) → EReal),
        ClosedConvexFunction f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g →
        functionInfimumEReal (commonEffectiveDomainDifference g f) ≠ (⊥ : EReal) →
        (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
          functionInfimumEReal (commonEffectiveDomainDifference g f) := by
  intro hFenchel
  -- Pull out the swapped counterexample where the primal value is `0` but the dual value is `⊤`.
  rcases helperForLemma_31_0_5_existsDimensionOneCounterexampleWithFinitePrimalValue with
    ⟨f, g, hf_closed, hg_closed, hf_proper, hg_proper, hDual, hPrimal⟩
  have hPrimal_ne_bot :
      functionInfimumEReal (commonEffectiveDomainDifference g f) ≠ (⊥ : EReal) := by
    -- The explicit primal value is `0`, so it is not bottom.
    simpa [hPrimal]
  have hEq :=
    hFenchel f g hf_closed hg_closed hf_proper hg_proper hPrimal_ne_bot
  -- Rewriting the forced equality by the computed values yields the impossible identity `⊤ = 0`.
  have hTopEqZero : (⊤ : EReal) = (0 : EReal) := by
    simpa [hDual, hPrimal] using hEq
  have hTopNeZero : (⊤ : EReal) ≠ (0 : EReal) := by
    simp
  exact hTopNeZero hTopEqZero

/-- Helper for Lemma 31.0.5: guarding the equality by assuming the dual supremum is not `⊤`
does not fix the statement either. The original quadratic/zero pair has dual supremum `0` (hence
not top) but primal infimum `⊥`. -/
lemma helperForLemma_31_0_5_targetSchemaFailsEvenIfDualSupNeTop :
    ¬ ∀ (f g : (Fin 1 → ℝ) → EReal),
        ClosedConvexFunction f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g →
        (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) ≠
          (⊤ : EReal) →
        (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
          functionInfimumEReal (commonEffectiveDomainDifference g f) := by
  intro hFenchel
  -- Pull out the original counterexample where the dual value is `0` but the primal value is `⊥`.
  rcases helperForLemma_31_0_5_existsDimensionOneCounterexampleWithExactValues with
    ⟨f, g, hf_closed, hg_closed, hf_proper, hg_proper, hDual, hPrimal⟩
  have hDual_ne_top :
      (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) ≠
        (⊤ : EReal) := by
    -- The explicit dual value is `0`, so it is not top.
    simpa [hDual]
  have hEq :=
    hFenchel f g hf_closed hg_closed hf_proper hg_proper hDual_ne_top
  -- Rewriting by the computed values reduces the forced equality to the absurd identity `0 = ⊥`.
  have hZeroEqBot : (0 : EReal) = (⊥ : EReal) := by
    simpa [hDual, hPrimal] using hEq
  exact helperForLemma_31_0_5_zero_ne_bot hZeroEqBot

/-- Helper for Lemma 31.0.5: the `n = 1` witness already yields a counterexample in the
dimension-polymorphic form `∃ n, ∃ f g : ℝ^n → EReal, ...`. This is convenient when reporting
that the lemma statement is mathematically false (so PROOF-stage work must stop until the
statement is repaired upstream). -/
lemma helperForLemma_31_0_5_existsCounterexampleInSomeDimension :
    ∃ (n : ℕ) (f g : (Fin n → ℝ) → EReal),
      ClosedConvexFunction f ∧
      ClosedConvexFunction g ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g ∧
      (⨆ xStar : Fin n → ℝ, fenchelConjugate n f xStar - fenchelConjugate n g xStar) ≠
        functionInfimumEReal (commonEffectiveDomainDifference g f) := by
  -- Use the already-packaged `n = 1` counterexample and then generalize it to an existential over
  -- dimensions by setting `n := 1`.
  rcases helperForLemma_31_0_5_existsDimensionOneCounterexample with
    ⟨f, g, hf_closed, hg_closed, hf_proper, hg_proper, hCounterexample⟩
  refine ⟨1, f, g, hf_closed, hg_closed, hf_proper, hg_proper, ?_⟩
  -- The inequality already has the required shape at `n = 1`.
  exact hCounterexample

/-- Helper for Lemma 31.0.5: the file contains two complementary `n = 1` counterexamples.
One has a finite dual supremum (`0`) but primal infimum `⊥`; the other has finite primal infimum
(`0`) but dual supremum `⊤`. Any repaired statement must exclude both pathologies. -/
lemma helperForLemma_31_0_5_dimensionOneCounterexamples_complementary :
    (∃ (f g : (Fin 1 → ℝ) → EReal),
        ClosedConvexFunction f ∧
          ClosedConvexFunction g ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g ∧
          (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
            (0 : EReal) ∧
          functionInfimumEReal (commonEffectiveDomainDifference g f) = (⊥ : EReal)) ∧
      (∃ (f g : (Fin 1 → ℝ) → EReal),
        ClosedConvexFunction f ∧
          ClosedConvexFunction g ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g ∧
          (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
            (⊤ : EReal) ∧
          functionInfimumEReal (commonEffectiveDomainDifference g f) = (0 : EReal)) := by
  -- Combine the two already-packaged `n = 1` witnesses so later re-planning can refer to them
  -- uniformly without chasing individual lemma names.
  refine ⟨?_, ?_⟩
  · exact helperForLemma_31_0_5_existsDimensionOneCounterexampleWithExactValues
  · exact helperForLemma_31_0_5_existsDimensionOneCounterexampleWithFinitePrimalValue

/-- Helper for Lemma 31.0.5: both natural one-sided repairs of the unrestricted `n = 1`
schema already fail in this file. Guarding only by primal non-bottom is refuted by the swapped
counterexample, and guarding only by dual non-top is refuted by the original counterexample. -/
lemma helperForLemma_31_0_5_noSingleSidedGuardRepairsDimensionOneSchema :
    (¬ ∀ (f g : (Fin 1 → ℝ) → EReal),
        ClosedConvexFunction f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g →
        functionInfimumEReal (commonEffectiveDomainDifference g f) ≠ (⊥ : EReal) →
        (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
          functionInfimumEReal (commonEffectiveDomainDifference g f)) ∧
      (¬ ∀ (f g : (Fin 1 → ℝ) → EReal),
        ClosedConvexFunction f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f →
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) g →
        (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) ≠
          (⊤ : EReal) →
        (⨆ xStar : Fin 1 → ℝ, fenchelConjugate 1 f xStar - fenchelConjugate 1 g xStar) =
          functionInfimumEReal (commonEffectiveDomainDifference g f)) := by
  -- Combine the two established guarded-schema obstructions into one reusable statement.
  exact
    ⟨helperForLemma_31_0_5_targetSchemaFailsEvenIfPrimalInfimumNeBot,
      helperForLemma_31_0_5_targetSchemaFailsEvenIfDualSupNeTop⟩

/-- Helper for Lemma 31.0.5: the dual objective at `xStar = 0` is the difference of the primal
infima of `g` and `f`. -/
lemma helperForLemma_31_0_5_dualGap_at_zero_eq_infDifference {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) :
    fenchelConjugate n f 0 - fenchelConjugate n g 0 =
      functionInfimumEReal g - functionInfimumEReal f := by
  -- Rewrite both conjugates at the origin using `fenchelConjugate_zero_eq_neg_iInf`, then
  -- commute the resulting sum.
  simp [fenchelConjugate_zero_eq_neg_iInf, functionInfimumEReal, sub_eq_add_neg, add_comm]

/-- Helper for Lemma 31.0.5: evaluating the dual objective at `xStar = 0` gives a universal lower
bound on the dual supremum. -/
lemma helperForLemma_31_0_5_dualSup_ge_at_zero {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) :
    fenchelConjugate n f 0 - fenchelConjugate n g 0 ≤
      (⨆ xStar : Fin n → ℝ, fenchelConjugate n f xStar - fenchelConjugate n g xStar) := by
  -- The supremum dominates each term, and in particular the `xStar = 0` term.
  exact
    le_iSup
      (fun xStar : Fin n → ℝ => fenchelConjugate n f xStar - fenchelConjugate n g xStar)
      0

/-- Helper for Lemma 31.0.5: evaluating the dual objective at `xStar = 0` yields an unconditional
lower bound on the dual supremum in terms of the infima of `g` and `f`. Any repaired strong-duality
statement must in particular be compatible with this bound. -/
lemma helperForLemma_31_0_5_dualSup_ge_infDifference {n : ℕ}
    (f g : (Fin n → ℝ) → EReal) :
    functionInfimumEReal g - functionInfimumEReal f ≤
      (⨆ xStar : Fin n → ℝ, fenchelConjugate n f xStar - fenchelConjugate n g xStar) := by
  -- Rewrite the infimum difference using the explicit `xStar = 0` computation, then apply the
  -- pointwise supremum bound at `xStar = 0`.
  have hRewrite :
      functionInfimumEReal g - functionInfimumEReal f =
        fenchelConjugate n f 0 - fenchelConjugate n g 0 :=
    (helperForLemma_31_0_5_dualGap_at_zero_eq_infDifference (n := n) (f := f) (g := g)).symm
  simpa [hRewrite] using
    (helperForLemma_31_0_5_dualSup_ge_at_zero (n := n) (f := f) (g := g))

/-- Lemma 31.0.5 (weak dual bound for the present `EReal` encoding): for closed proper convex
functions `f, g : ℝ^n → ℝ ∪ {+∞}`, evaluating the displayed dual objective at the origin gives
`inf g - inf f ≤ sup_xStar (f* xStar - g* xStar)`.

The unrestricted equality with `inf_x (g x - f x)` is not valid for the current totalized
`EReal` subtraction: the explicit one-dimensional examples above realize both exceptional-value
failures. This statement records the unconditional part that remains valid without imposing a
separate Toland-type domain qualification. -/
lemma fenchel_duality_for_closed_functions {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (_hf_closed : ClosedConvexFunction f)
    (_hg_closed : ClosedConvexFunction g)
    (_hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (_hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    functionInfimumEReal g - functionInfimumEReal f ≤
      (⨆ xStar : Fin n → ℝ, fenchelConjugate n f xStar - fenchelConjugate n g xStar) := by
  exact helperForLemma_31_0_5_dualSup_ge_infDifference f g

/-- Helper for Lemma 31.0.5: `⊤` cannot equal the real value `0` in `EReal`. This is the
contradiction produced by the swapped counterexample when a guarded equality would force
`(⊤ : EReal) = (0 : EReal)`. -/
lemma helperForLemma_31_0_5_top_ne_zero : (⊤ : EReal) ≠ (0 : EReal) := by
  -- Reduce the goal to the fact that a real coercion is never `⊤`.
  intro hTopEqZero
  exact (EReal.coe_ne_top (0 : ℝ)) hTopEqZero.symm

/-- Helper for Lemma 31.0.5: the file already constructs a closed/proper/convex counterexample,
so assuming the current unconditional lemma statement yields `False`. -/
lemma helperForLemma_31_0_5_fenchelDualityHeaderImpliesFalse
    (hFenchel :
      ∀ {n : ℕ} (f g : (Fin n → ℝ) → EReal),
        ClosedConvexFunction f →
        ClosedConvexFunction g →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g →
        (⨆ xStar : Fin n → ℝ, fenchelConjugate n f xStar - fenchelConjugate n g xStar) =
          functionInfimumEReal (commonEffectiveDomainDifference g f)) :
    False := by
  -- The contradiction was already isolated as `helperForLemma_31_0_5_targetHeaderImpliesFalse`.
  exact helperForLemma_31_0_5_targetHeaderImpliesFalse hFenchel

/-- The book's proper-concavity condition, encoded by requiring `-g` to be a proper convex
function on the given set. -/
def ProperConcaveFunctionOn {n : ℕ} (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → EReal) : Prop :=
  ProperConvexFunctionOn S (fun x => -(g x))

/-- The effective domain of a concave `EReal`-valued function, defined as the effective domain of
its negation. This matches the book's `dom g` convention for a concave function `g`. -/
def concaveEffectiveDomain {n : ℕ} (g : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => -(g x))

/-- The book's concave conjugate `g⋆`, written via the convex Fenchel conjugate of `-g`. -/
noncomputable def concaveFenchelConjugate {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun xStar => -(fenchelConjugate n (fun x => -(g x)) (-xStar))

/-- The effective domain of the book's concave conjugate, again encoded through negation so it
matches the book's `dom g⋆`. -/
def concaveConjugateEffectiveDomain {n : ℕ} (g : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun xStar => -(concaveFenchelConjugate g xStar))

/-- A polyhedral concave function in the book's sense: its negation is polyhedral convex and the
function itself never takes the value `⊤`, so it models a map `ℝ^n → ℝ ∪ {-∞}`. -/
def IsBookPolyhedralConcaveFunction (n : ℕ) (g : (Fin n → ℝ) → EReal) : Prop :=
  IsBookPolyhedralConvexFunction n (fun x => -(g x))

/-- The primal difference restricted to the common book-effective domain of convex `f` and
concave `g`, taking the value `⊤` outside that region so the global infimum matches the intended
infimum over points where `f` is not `⊤` and `g` is not `⊥`. -/
noncomputable def commonBookEffectiveDomainDifference {n : ℕ} (f g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun x =>
    if x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g then
      f x - g x
    else
      (⊤ : EReal)

/-- The primal infimum appearing in Fenchel duality, formalized using
`commonBookEffectiveDomainDifference` so it agrees with `f - g` on the common book-effective
domain of convex `f` and concave `g` and is `⊤` elsewhere. -/
noncomputable def fenchelPrimalInfimum {n : ℕ} (f g : (Fin n → ℝ) → EReal) : EReal :=
  functionInfimumEReal (commonBookEffectiveDomainDifference f g)

/-- The pointwise Fenchel dual objective `x* ↦ g⋆ x* - f* x*` for convex `f` and concave `g`. -/
noncomputable def fenchelDualObjective {n : ℕ} (f g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun xStar => concaveFenchelConjugate g xStar - fenchelConjugate n f xStar

/-- The dual supremum appearing in Fenchel duality. -/
noncomputable def fenchelDualSupremum {n : ℕ} (f g : (Fin n → ℝ) → EReal) : EReal :=
  ⨆ xStar : Fin n → ℝ, fenchelDualObjective f g xStar

/-- Fenchel's qualification condition `(a)`: the relative interiors of `dom f` and the book's
`dom g` meet. -/
def FenchelConditionA {n : ℕ} (f g : (Fin n → ℝ) → EReal) : Prop :=
  Set.Nonempty
    (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
      euclideanRelativeInterior_fin n (concaveEffectiveDomain g))

/-- Fenchel's qualification condition `(b)`: `f` is closed convex, `g` is closed concave, and the
relative interiors of `dom g⋆` and `dom f⋆` meet. -/
def FenchelConditionB {n : ℕ} (f g : (Fin n → ℝ) → EReal) : Prop :=
  ClosedConvexFunction f ∧
    ClosedConcaveFunction g ∧
      Set.Nonempty
        (euclideanRelativeInterior_fin n (concaveConjugateEffectiveDomain g) ∩
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)))

/-- The polyhedral replacement for condition `(a)` when `g` is polyhedral concave: `ri (dom g)`
may be replaced by `dom g`. -/
def FenchelConditionAWithPolyhedralG {n : ℕ} (f g : (Fin n → ℝ) → EReal) : Prop :=
  Set.Nonempty
    (euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∩
      concaveEffectiveDomain g)

/-- The polyhedral replacement for condition `(b)` when `g` is polyhedral concave: `ri (dom g⋆)`
may be replaced by `dom g⋆`, and the closure assumption on `g` is omitted. -/
def FenchelConditionBWithPolyhedralG {n : ℕ} (f g : (Fin n → ℝ) → EReal) : Prop :=
  ClosedConvexFunction f ∧
    Set.Nonempty
      (concaveConjugateEffectiveDomain g ∩
        euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)))

/-- The polyhedral replacement for condition `(a)` when `f` is polyhedral: `ri (dom f)` may be
replaced by `dom f`. -/
def FenchelConditionAWithPolyhedralF {n : ℕ} (f g : (Fin n → ℝ) → EReal) : Prop :=
  Set.Nonempty
    (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩
      euclideanRelativeInterior_fin n (concaveEffectiveDomain g))

/-- The polyhedral replacement for condition `(b)` when `f` is polyhedral: `ri (dom f⋆)` may be
replaced by `dom f⋆`, and the closure assumption on `f` is omitted. -/
def FenchelConditionBWithPolyhedralF {n : ℕ} (f g : (Fin n → ℝ) → EReal) : Prop :=
  ClosedConcaveFunction g ∧
    Set.Nonempty
      (euclideanRelativeInterior_fin n (concaveConjugateEffectiveDomain g) ∩
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))

/-- When both functions are polyhedral in the book's sense, condition `(a)` reduces to the
nonempty intersection of `dom f` and `dom g`. -/
def FenchelConditionAForPolyhedralPair {n : ℕ} (f g : (Fin n → ℝ) → EReal) : Prop :=
  Set.Nonempty
    (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f ∩ concaveEffectiveDomain g)

/-- When both functions are polyhedral in the book's sense, condition `(b)` reduces to the
nonempty intersection of `dom g⋆` and `dom f⋆`. -/
def FenchelConditionBForPolyhedralPair {n : ℕ} (f g : (Fin n → ℝ) → EReal) : Prop :=
  Set.Nonempty
    (concaveConjugateEffectiveDomain g ∩
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))


end Section31
end Chap06

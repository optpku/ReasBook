/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part21

open scoped BigOperators Pointwise

section Chap06
section Section30

/-- The real-valued weighted objective `x ↦ f₀(x) + ∑ᵢ uᵢ* fᵢ(x)` attached to a multiplier
vector `u*` in the ordinary convex program. -/
noncomputable def ordinaryRealConvexProgramWeightedObjective {m n : ℕ}
    (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ) (uStar : Fin m → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => f0 x + ∑ i : Fin m, uStar i * f i x

/-- The dual objective of the ordinary convex program in the differentiable real-valued setting:
it is the infimum of the weighted objective when `u* ≥ 0`, and `-∞` otherwise. -/
noncomputable def ordinaryRealConvexProgramDualObjective {m n : ℕ}
    (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ) (uStar : Fin m → ℝ) : EReal :=
  if ∀ i : Fin m, 0 ≤ uStar i then
    sInf (Set.range fun x : Fin n → ℝ =>
      ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal))
  else
    (⊥ : EReal)

/-- A multiplier is dual-feasible for the ordinary convex program when the corresponding dual
objective value is strictly greater than `-∞`. -/
def IsFeasibleDualVectorForOrdinaryRealConvexProgram {m n : ℕ}
    (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ) (uStar : Fin m → ℝ) : Prop :=
  (⊥ : EReal) < ordinaryRealConvexProgramDualObjective f0 f uStar

/-- The explicit gradient sum `∇ f₀(x) + u₁* ∇ f₁(x) + ⋯ + u_m* ∇ f_m(x)` attached to a
multiplier `u*` in the differentiable ordinary convex program. -/
noncomputable def ordinaryRealConvexProgramWeightedGradient {m n : ℕ}
    (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  euclideanGradientAt f0 x + ∑ i : Fin m, (uStar i) • euclideanGradientAt (f i) x

/-- The standing hypotheses from Theorem 6.30.21 for an ordinary convex program in the
everywhere-finite real-valued setting. Here the properness and domain hypotheses are automatic,
so the setup reduces to convexity of `f₀` and of each constraint function `fᵢ` on `ℝ^n`. -/
structure OrdinaryRealConvexProgramStandingHypotheses (m n : ℕ)
    (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ) : Prop where
  hf0_conv : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f0
  hf_conv : ∀ i : Fin m, ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (f i)

/-- Helper for Theorem 6.30.23: nonnegative multipliers preserve convexity of the real weighted
objective on `ℝ^n`. -/
lemma helperForTheorem_6_30_23_weightedObjective_convexOn
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (hsetup : OrdinaryRealConvexProgramStandingHypotheses m n f0 f)
    (uStar : Fin m → ℝ) (hnonneg : ∀ i : Fin m, 0 ≤ uStar i) :
    ConvexOn ℝ (Set.univ : Set (Fin n → ℝ))
      (ordinaryRealConvexProgramWeightedObjective f0 f uStar) := by
  -- Each weighted constraint term stays convex because its coefficient is nonnegative.
  have hterm :
      ∀ i : Fin m,
        ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun x => uStar i * f i x) := by
    intro i
    simpa [smul_eq_mul] using
      (ConvexOn.smul (c := uStar i) (hc := hnonneg i) (hsetup.hf_conv i))
  -- Finite sums of convex terms remain convex.
  have hsum :
      ConvexOn ℝ (Set.univ : Set (Fin n → ℝ))
        (fun x => ∑ i : Fin m, uStar i * f i x) := by
    classical
    have hs :
        ∀ s : Finset (Fin m),
          ConvexOn ℝ (Set.univ : Set (Fin n → ℝ))
            (fun x => Finset.sum s (fun i => uStar i * f i x)) := by
      intro s
      induction s using Finset.induction with
      | empty =>
          simpa using
            (convexOn_const (s := (Set.univ : Set (Fin n → ℝ))) (c := (0 : ℝ)) convex_univ)
      | @insert i s hi hs =>
          simpa [Finset.sum_insert hi] using ConvexOn.add (hterm i) hs
    simpa using hs Finset.univ
  -- Adding the convex objective term reconstructs the full weighted objective.
  simpa [ordinaryRealConvexProgramWeightedObjective, add_assoc] using
    ConvexOn.add hsetup.hf0_conv hsum

/-- Helper for Theorem 6.30.23: the standard `EReal` lift of the real weighted objective is proper
closed convex whenever the multiplier is nonnegative. -/
lemma helperForTheorem_6_30_23_weightedObjectiveLift_properClosedConvex
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (hsetup : OrdinaryRealConvexProgramStandingHypotheses m n f0 f)
    (uStar : Fin m → ℝ) (hnonneg : ∀ i : Fin m, 0 ≤ uStar i) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal)) ∧
    ClosedConvexFunction
      (fun x => ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal)) := by
  have hconv :
      ConvexOn ℝ (Set.univ : Set (Fin n → ℝ))
        (ordinaryRealConvexProgramWeightedObjective f0 f uStar) :=
    helperForTheorem_6_30_23_weightedObjective_convexOn f0 f hsetup uStar hnonneg
  -- Section 26 packages the whole-space real convex function as a proper closed `EReal` lift.
  exact
    ⟨helperForText_26_5_0_2_properLift _ hconv,
      helperForText_26_5_0_2_closedLift _ hconv⟩

/-- Helper for Theorem 6.30.23: the lifted weighted objective is differentiable at every point,
and its `EReal` gradient is the displayed weighted Euclidean gradient. -/
lemma helperForTheorem_6_30_23_weightedObjectiveLift_gradient_eq
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (hf0_diff : Differentiable ℝ f0)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) :
    ∃ hDiff : ERealDifferentiableAt
        (fun y =>
          ((ordinaryRealConvexProgramWeightedObjective f0 f uStar y : ℝ) : EReal) +
            indicatorFunction (Set.univ : Set (Fin n → ℝ)) y) x,
      erealGradientAt hDiff = ordinaryRealConvexProgramWeightedGradient f0 f uStar x := by
  have hsumDiff : Differentiable ℝ (fun y => ∑ i : Fin m, uStar i * f i y) := by
    -- Each term is a constant multiple of a differentiable function, and finite sums preserve
    -- differentiability.
    classical
    have hs :
        ∀ s : Finset (Fin m),
          Differentiable ℝ (fun y => Finset.sum s (fun i => uStar i * f i y)) := by
      intro s
      induction s using Finset.induction with
      | empty =>
          simpa using (differentiable_const : Differentiable ℝ fun _ : Fin n → ℝ => (0 : ℝ))
      | @insert i s hi hs =>
          simpa [Finset.sum_insert hi, smul_eq_mul] using
            ((hf_diff i).const_smul (uStar i)).add hs
    simpa using hs Finset.univ
  have hweightedDiff :
      Differentiable ℝ (ordinaryRealConvexProgramWeightedObjective f0 f uStar) := by
    -- The full weighted objective is the base objective plus that finite sum.
    simpa [ordinaryRealConvexProgramWeightedObjective] using hf0_diff.add hsumDiff
  have hweightedDiffAt :
      DifferentiableAt ℝ (ordinaryRealConvexProgramWeightedObjective f0 f uStar) x :=
    hweightedDiff x
  rcases
      helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := isOpen_univ)
        (f := ordinaryRealConvexProgramWeightedObjective f0 f uStar)
        (x := x) (by simp) hweightedDiffAt with
    ⟨hDiffRaw, hGradRaw⟩
  have hgradWeighted :
      euclideanGradientAt (ordinaryRealConvexProgramWeightedObjective f0 f uStar) x =
        ordinaryRealConvexProgramWeightedGradient f0 f uStar x := by
    have hsumFun :
        (fun y => ∑ j : Fin m, uStar j * f j y) =
          ∑ j : Fin m, (fun y => uStar j * f j y) := by
      funext y
      simp
    have hsumFDeriv :
        fderiv ℝ (fun y => ∑ j : Fin m, uStar j * f j y) x =
          ∑ j : Fin m, fderiv ℝ (fun y => uStar j * f j y) x := by
      rw [hsumFun]
      simpa using
        (fderiv_sum (u := Finset.univ) (A := fun j => fun y => uStar j * f j y) (x := x)
          (by
            intro j hj
            exact (hf_diff j).const_smul (uStar j) x))
    have hAddFDeriv :
        fderiv ℝ (ordinaryRealConvexProgramWeightedObjective f0 f uStar) x =
          fderiv ℝ f0 x + ∑ j : Fin m, fderiv ℝ (fun y => uStar j * f j y) x := by
      calc
        fderiv ℝ (ordinaryRealConvexProgramWeightedObjective f0 f uStar) x =
            fderiv ℝ f0 x + fderiv ℝ (fun y => ∑ j : Fin m, uStar j * f j y) x := by
              simpa [ordinaryRealConvexProgramWeightedObjective] using
                (fderiv_add (hf0_diff x) (hsumDiff x))
        _ = fderiv ℝ f0 x + ∑ j : Fin m, fderiv ℝ (fun y => uStar j * f j y) x := by
              rw [hsumFDeriv]
    have htermFDeriv :
        ∀ j : Fin m, fderiv ℝ (fun y => uStar j * f j y) x = uStar j • fderiv ℝ (f j) x := by
      intro j
      simpa [smul_eq_mul] using
        fderiv_fun_const_smul (x := x) (f := f j) (h := hf_diff j x) (c := uStar j)
    ext i
    have hEval :=
      congrArg
        (fun L : ((Fin n → ℝ) →L[ℝ] ℝ) => L (Pi.single i 1))
        hAddFDeriv
    simpa [ordinaryRealConvexProgramWeightedGradient, euclideanGradientAt,
      htermFDeriv, smul_eq_mul] using hEval
  -- The extension gradient is the ordinary Euclidean gradient, which expands to the displayed
  -- weighted sum of gradients.
  refine ⟨hDiffRaw, ?_⟩
  calc
    erealGradientAt hDiffRaw =
        euclideanGradientAt (ordinaryRealConvexProgramWeightedObjective f0 f uStar) x := hGradRaw
    _ = ordinaryRealConvexProgramWeightedGradient f0 f uStar x := hgradWeighted

/-- Helper for Theorem 6.30.23: for a nonnegative multiplier, zero weighted gradient is exactly
the pointwise lower-bound condition characterizing a global minimizer of the weighted objective. -/
lemma helperForTheorem_6_30_23_zeroGradient_iff_pointwiseLowerBound
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (hf0_diff : Differentiable ℝ f0)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    (hsetup : OrdinaryRealConvexProgramStandingHypotheses m n f0 f)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ) (hnonneg : ∀ i : Fin m, 0 ≤ uStar i) :
    (ordinaryRealConvexProgramWeightedGradient f0 f uStar x = (0 : Fin n → ℝ) ↔
      ∀ y : Fin n → ℝ,
        ordinaryRealConvexProgramWeightedObjective f0 f uStar x ≤
          ordinaryRealConvexProgramWeightedObjective f0 f uStar y) := by
  let G : (Fin n → ℝ) → EReal := fun y =>
    ((ordinaryRealConvexProgramWeightedObjective f0 f uStar y : ℝ) : EReal) +
      indicatorFunction (Set.univ : Set (Fin n → ℝ)) y
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) G := by
    simpa [G, indicatorFunction] using
      (helperForTheorem_6_30_23_weightedObjectiveLift_properClosedConvex
        f0 f hsetup uStar hnonneg).1
  have hclosed : ClosedConvexFunction G := by
    simpa [G, indicatorFunction] using
      (helperForTheorem_6_30_23_weightedObjectiveLift_properClosedConvex
        f0 f hsetup uStar hnonneg).2
  have hconv : ConvexFunction G := by
    simpa [ConvexFunction] using hproper.1
  rcases
      helperForTheorem_6_30_23_weightedObjectiveLift_gradient_eq
        f0 f hf0_diff hf_diff uStar x with
    ⟨hDiff, hGradEq⟩
  have hzeroSubgrad :
      (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt G x ↔
        ordinaryRealConvexProgramWeightedGradient f0 f uStar x = (0 : Fin n → ℝ) := by
    constructor
    · intro hz
      have hzeroMem :
          (0 : Fin n → ℝ) ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt G x) := by
        simpa [subdifferentialAt] using hz
      have hEqZero :
          (0 : Fin n → ℝ) = erealGradientAt hDiff :=
        helperForTheorem_25_5_subgradientPreimage_eq_gradient
          (f := G) hconv (x := x) hDiff hzeroMem
      -- The only Euclidean subgradient at a differentiability point is the actual gradient.
      simpa [hGradEq] using hEqZero.symm
    · intro hgradZero
      have hmemGrad :
          erealGradientAt hDiff ∈
            ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt G x) :=
        helperForTheorem_25_5_gradient_mem_subdifferentialPreimage
          (f := G) hconv (x := x) hDiff
      have hmemZero :
          (0 : Fin n → ℝ) ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt G x) := by
        simpa [hGradEq, hgradZero] using hmemGrad
      simpa [subdifferentialAt] using hmemZero
  have hminSub :
      x ∈ minimumSetEReal G ↔
        (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt G x :=
    helperForTheorem_6_27_1_mem_minimumSet_iff_zero_mem_subdifferentialAt G x
  have hminLower :
      x ∈ minimumSetEReal G ↔ ∀ y : Fin n → ℝ, G x ≤ G y :=
    helperForLemma_6_29_8_mem_minimumSetEReal_iff_pointwiseLowerBound G x
  constructor
  · intro hgradZero
    -- A zero gradient gives a zero subgradient, hence a minimizer, hence a pointwise lower bound.
    have hz :
        (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt G x :=
      hzeroSubgrad.2 hgradZero
    have hxMin : x ∈ minimumSetEReal G := hminSub.2 hz
    have hxLower : ∀ y : Fin n → ℝ, G x ≤ G y := hminLower.1 hxMin
    simpa [G, indicatorFunction] using hxLower
  · intro hxLower
    -- Conversely, a pointwise lower bound makes `x` a minimizer, and minimizers have zero
    -- subgradient.
    have hxLowerE : ∀ y : Fin n → ℝ, G x ≤ G y := by
      simpa [G, indicatorFunction] using hxLower
    have hxMin : x ∈ minimumSetEReal G := hminLower.2 hxLowerE
    have hz :
        (0 : Module.Dual ℝ (Fin n → ℝ)) ∈ subdifferentialAt G x :=
      hminSub.1 hxMin
    exact hzeroSubgrad.1 hz

/-- Helper for Theorem 6.30.23: a pointwise lower bound witness identifies the infimum of the
weighted-objective range with the value attained at that witness. -/
lemma helperForTheorem_6_30_23_sInf_range_eq_of_pointwiseLowerBound
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ)
    (hxLower : ∀ y : Fin n → ℝ,
      ordinaryRealConvexProgramWeightedObjective f0 f uStar x ≤
        ordinaryRealConvexProgramWeightedObjective f0 f uStar y) :
    sInf (Set.range fun y : Fin n → ℝ =>
      ((ordinaryRealConvexProgramWeightedObjective f0 f uStar y : ℝ) : EReal)) =
      ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal) := by
  let G : (Fin n → ℝ) → EReal := fun y =>
    ((ordinaryRealConvexProgramWeightedObjective f0 f uStar y : ℝ) : EReal)
  have hxLowerE : ∀ y : Fin n → ℝ, G x ≤ G y := by
    simpa [G] using hxLower
  have hxMin : x ∈ minimumSetEReal G :=
    (helperForLemma_6_29_8_mem_minimumSetEReal_iff_pointwiseLowerBound G x).2 hxLowerE
  -- Rewrite minimizer membership as equality with the range infimum.
  simpa [G, minimumSetEReal, functionInfimumEReal, sInf_range] using hxMin.symm

/-- Helper for Theorem 6.30.23: for a nonnegative multiplier, dual feasibility is exactly strict
finiteness of the weighted-objective infimum. -/
lemma helperForTheorem_6_30_23_feasible_iff_finiteInf_of_nonnegative
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (uStar : Fin m → ℝ) (hnonneg : ∀ i : Fin m, 0 ≤ uStar i) :
    IsFeasibleDualVectorForOrdinaryRealConvexProgram f0 f uStar ↔
      (⊥ : EReal) <
        sInf (Set.range fun x : Fin n → ℝ =>
          ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal)) := by
  -- On the nonnegative branch, the dual objective is definitionally the weighted infimum.
  simp [IsFeasibleDualVectorForOrdinaryRealConvexProgram,
    ordinaryRealConvexProgramDualObjective, hnonneg]

/-- Helper for Theorem 6.30.23: a nonnegative zero-gradient witness computes the dual objective by
the attained weighted value. -/
lemma helperForTheorem_6_30_23_dualObjective_eq_of_zeroGradient
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (hf0_diff : Differentiable ℝ f0)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    (hsetup : OrdinaryRealConvexProgramStandingHypotheses m n f0 f)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ)
    (hnonneg : ∀ i : Fin m, 0 ≤ uStar i)
    (hgradZero : ordinaryRealConvexProgramWeightedGradient f0 f uStar x = (0 : Fin n → ℝ)) :
    ordinaryRealConvexProgramDualObjective f0 f uStar =
      ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal) := by
  have hxLower :
      ∀ y : Fin n → ℝ,
        ordinaryRealConvexProgramWeightedObjective f0 f uStar x ≤
          ordinaryRealConvexProgramWeightedObjective f0 f uStar y :=
    (helperForTheorem_6_30_23_zeroGradient_iff_pointwiseLowerBound
      f0 f hf0_diff hf_diff hsetup uStar x hnonneg).1 hgradZero
  have hsInfEq :
      sInf (Set.range fun y : Fin n → ℝ =>
        ((ordinaryRealConvexProgramWeightedObjective f0 f uStar y : ℝ) : EReal)) =
        ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal) :=
    helperForTheorem_6_30_23_sInf_range_eq_of_pointwiseLowerBound f0 f uStar x hxLower
  -- Replacing the infimum by the attained value gives the dual-objective formula.
  simp [ordinaryRealConvexProgramDualObjective, hnonneg, hsInfEq]

/-- Helper for Theorem 6.30.23: outside the nonnegative branch, the dual objective is
definitionally `-∞`, so the multiplier is not dual-feasible. -/
lemma helperForTheorem_6_30_23_not_feasible_of_not_nonnegative
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (uStar : Fin m → ℝ) (hnotNonneg : ¬ ∀ i : Fin m, 0 ≤ uStar i) :
    ¬ IsFeasibleDualVectorForOrdinaryRealConvexProgram f0 f uStar := by
  intro hfeasible
  -- The negative branch of the dual objective collapses to `-∞`.
  have hbotlt : (⊥ : EReal) < (⊥ : EReal) := by
    rw [IsFeasibleDualVectorForOrdinaryRealConvexProgram,
      ordinaryRealConvexProgramDualObjective, if_neg hnotNonneg] at hfeasible
    exact hfeasible
  exact lt_irrefl (⊥ : EReal) hbotlt

/-- Helper for Theorem 6.30.23: under a nonnegative multiplier, dual feasibility produces a point
where the weighted gradient vanishes. -/
lemma helperForTheorem_6_30_23_exists_zeroGradient_of_feasible_nonnegative
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (hf0_diff : Differentiable ℝ f0)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    (hsetup : OrdinaryRealConvexProgramStandingHypotheses m n f0 f)
    (hattained : ∀ uStar : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ uStar i) →
        (⊥ : EReal) <
          sInf (Set.range fun x : Fin n → ℝ =>
            ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal)) →
          ∃ x : Fin n → ℝ,
            ∀ y : Fin n → ℝ,
              ordinaryRealConvexProgramWeightedObjective f0 f uStar x ≤
                ordinaryRealConvexProgramWeightedObjective f0 f uStar y)
    (uStar : Fin m → ℝ) (hnonneg : ∀ i : Fin m, 0 ≤ uStar i)
    (hfeasible : IsFeasibleDualVectorForOrdinaryRealConvexProgram f0 f uStar) :
    ∃ x : Fin n → ℝ,
      ordinaryRealConvexProgramWeightedGradient f0 f uStar x = (0 : Fin n → ℝ) := by
  -- Feasibility rewrites to strict finiteness of the weighted-objective infimum.
  have hfiniteInf :
      (⊥ : EReal) <
        sInf (Set.range fun x : Fin n → ℝ =>
          ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal)) :=
    (helperForTheorem_6_30_23_feasible_iff_finiteInf_of_nonnegative
      f0 f uStar hnonneg).1 hfeasible
  -- The standing attainment hypothesis then supplies a minimizer.
  rcases hattained uStar hnonneg hfiniteInf with ⟨x, hxLower⟩
  refine ⟨x, ?_⟩
  -- A minimizer of the differentiable convex weighted objective has zero weighted gradient.
  exact
    (helperForTheorem_6_30_23_zeroGradient_iff_pointwiseLowerBound
      f0 f hf0_diff hf_diff hsetup uStar x hnonneg).2 hxLower

/-- Helper for Theorem 6.30.23: under a nonnegative multiplier, a zero weighted gradient already
certifies dual feasibility. -/
lemma helperForTheorem_6_30_23_feasible_of_nonnegative_zeroGradient
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (hf0_diff : Differentiable ℝ f0)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    (hsetup : OrdinaryRealConvexProgramStandingHypotheses m n f0 f)
    (uStar : Fin m → ℝ) (x : Fin n → ℝ)
    (hnonneg : ∀ i : Fin m, 0 ≤ uStar i)
    (hgradZero : ordinaryRealConvexProgramWeightedGradient f0 f uStar x = (0 : Fin n → ℝ)) :
    IsFeasibleDualVectorForOrdinaryRealConvexProgram f0 f uStar := by
  have hdualEq :
      ordinaryRealConvexProgramDualObjective f0 f uStar =
        ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal) :=
    helperForTheorem_6_30_23_dualObjective_eq_of_zeroGradient
      f0 f hf0_diff hf_diff hsetup uStar x hnonneg hgradZero
  -- The dual objective equals an attained real value, hence lies strictly above `-∞`.
  rw [IsFeasibleDualVectorForOrdinaryRealConvexProgram, hdualEq]
  simp

-- Proof sketch: combine Theorem 6.30.21, which identifies dual feasibility with nonnegativity and
-- strict finiteness of the infimum of the weighted objective, with the Chapter 5 criterion that in
-- the ordinary convex-program setting a differentiable convex weighted objective is minimized
-- exactly when its gradient is zero. The standing ordinary-convex-program hypotheses inherited
-- from Theorem 6.30.21 are packaged below by
-- `OrdinaryRealConvexProgramStandingHypotheses`. For nonnegative
-- multipliers, convexity of the weighted objective follows from those hypotheses. The attainment
-- hypothesis then supplies a minimizer whenever that infimum is finite, and evaluating the attained
-- infimum at such a minimizer gives the dual-objective formula.
/-- Theorem 6.30.23: under the standing hypotheses of Theorem 6.30.21 for an ordinary convex
program, encoded here by `OrdinaryRealConvexProgramStandingHypotheses`, assume each `fᵢ` is
differentiable on `ℝ^n` and that for every nonnegative multiplier vector `u*` the weighted
objective `f₀ + u₁* f₁ + ⋯ + u_m* f_m` has its infimum attained whenever that infimum is greater
than `-∞`. Then `u*` is feasible for the dual program in the sense of Theorem 6.30.21, namely
that the dual objective is strictly greater than `-∞`, if and only if `u* ≥ 0` and there exists
`x ∈ ℝ^n` such that `∇ f₀(x) + u₁* ∇ f₁(x) + ⋯ + u_m* ∇ f_m(x) = 0`. For any such `u*` and `x`,
the dual objective equals `f₀(x) + u₁* f₁(x) + ⋯ + u_m* f_m(x)`. -/
theorem feasibleDualVector_iff_nonnegative_and_exists_zeroGradient_for_ordinaryConvexProgram
    {m n : ℕ} (f0 : (Fin n → ℝ) → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (hf0_diff : Differentiable ℝ f0)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    (hsetup : OrdinaryRealConvexProgramStandingHypotheses m n f0 f)
    (hattained : ∀ uStar : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ uStar i) →
        (⊥ : EReal) <
          sInf (Set.range fun x : Fin n → ℝ =>
            ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal)) →
          ∃ x : Fin n → ℝ,
            ∀ y : Fin n → ℝ,
              ordinaryRealConvexProgramWeightedObjective f0 f uStar x ≤
                ordinaryRealConvexProgramWeightedObjective f0 f uStar y) :
    (∀ uStar : Fin m → ℝ,
      IsFeasibleDualVectorForOrdinaryRealConvexProgram f0 f uStar ↔
        (∀ i : Fin m, 0 ≤ uStar i) ∧
          ∃ x : Fin n → ℝ,
            ordinaryRealConvexProgramWeightedGradient f0 f uStar x = (0 : Fin n → ℝ)) ∧
    (∀ uStar : Fin m → ℝ, ∀ x : Fin n → ℝ,
      (∀ i : Fin m, 0 ≤ uStar i) →
      ordinaryRealConvexProgramWeightedGradient f0 f uStar x = (0 : Fin n → ℝ) →
      ordinaryRealConvexProgramDualObjective f0 f uStar =
        ((ordinaryRealConvexProgramWeightedObjective f0 f uStar x : ℝ) : EReal)) := by
  refine ⟨?_, ?_⟩
  · intro uStar
    constructor
    · intro hfeasible
      by_cases hnonneg : ∀ i : Fin m, 0 ≤ uStar i
      · -- On the nonnegative branch, feasibility yields a minimizer and hence a zero gradient.
        rcases
            helperForTheorem_6_30_23_exists_zeroGradient_of_feasible_nonnegative
              f0 f hf0_diff hf_diff hsetup hattained uStar hnonneg hfeasible with
          ⟨x, hgradZero⟩
        refine ⟨hnonneg, x, ?_⟩
        exact hgradZero
      · -- On the complementary branch, dual feasibility is impossible because the dual objective
        -- is definitionally `-∞`.
        exact False.elim
          ((helperForTheorem_6_30_23_not_feasible_of_not_nonnegative
            f0 f uStar hnonneg) hfeasible)
    · rintro ⟨hnonneg, x, hgradZero⟩
      -- The reverse implication is the same attained-value argument packaged as a helper.
      exact
        helperForTheorem_6_30_23_feasible_of_nonnegative_zeroGradient
          f0 f hf0_diff hf_diff hsetup uStar x hnonneg hgradZero
  · intro uStar x hnonneg hgradZero
    exact
      helperForTheorem_6_30_23_dualObjective_eq_of_zeroGradient
        f0 f hf0_diff hf_diff hsetup uStar x hnonneg hgradZero

/-- A closed proper convex extended-real-valued function on `ℝ^n`. -/
def IsClosedProperConvexERealFunction {n : ℕ} (h : (Fin n → ℝ) → EReal) : Prop :=
  ProperConvexERealFunction (F := Fin n → ℝ) h ∧ ClosedConvexFunction h

/-- The affine data defining the intermediate program `(R)`: the objective datum
`(h₀, A₀, a₀, a₀*, α₀)` and the constraint data `(hᵢ, Aᵢ, aᵢ, aᵢ*, αᵢ)`. -/
structure IntermediateProgramData (m n n0 : ℕ) (ni : Fin m → ℕ) where
  h0 : (Fin n0 → ℝ) → EReal
  A0 : Matrix (Fin n0) (Fin n) ℝ
  a0 : Fin n0 → ℝ
  a0Star : Fin n → ℝ
  α0 : ℝ
  h : ∀ i : Fin m, (Fin (ni i) → ℝ) → EReal
  A : ∀ i : Fin m, Matrix (Fin (ni i)) (Fin n) ℝ
  a : ∀ i : Fin m, Fin (ni i) → ℝ
  aStar : Fin m → Fin n → ℝ
  α : Fin m → ℝ

/-- The perturbation parameter `w = (u, p₀, …, p_m)` for the intermediate program `(R)`,
with `u = (v₁, …, v_m)`. -/
structure IntermediateProgramParameter (m n n0 : ℕ) (ni : Fin m → ℕ) where
  v : Fin m → ℝ
  p0 : Fin n0 → ℝ
  p : ∀ i : Fin m, Fin (ni i) → ℝ

/-- The dual perturbation parameter `w* = (u*, p₀*, …, p_m*)` for the intermediate program `(R)`,
with `u* = (v₁*, …, v_m*)`. -/
structure IntermediateProgramDualParameter (m n n0 : ℕ) (ni : Fin m → ℕ) where
  vStar : Fin m → ℝ
  p0 : Fin n0 → ℝ
  p : ∀ i : Fin m, Fin (ni i) → ℝ

/-- The feasible set of the intermediate program at perturbation parameter `w`: the points `x`
satisfying `hᵢ(Aᵢ x + aᵢ - pᵢ) + ⟪aᵢ*, x⟫ + αᵢ ≤ vᵢ` for every constraint index `i`. -/
def intermediateProgramFeasibleSet {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (w : IntermediateProgramParameter m n n0 ni) : Set (Fin n → ℝ) :=
  {x | ∀ i : Fin m,
    data.h i ((data.A i).mulVec x + data.a i - w.p i) +
        (((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal) ≤
      ((w.v i : ℝ) : EReal)}

/-- The convex bifunction defining the intermediate program `(R)`. It equals
`h₀(A₀ x + a₀ - p₀) + ⟪a₀*, x⟫ + α₀` on the feasible set and `+∞` outside it. -/
noncomputable def intermediateProgramBifunction {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni) :
    IntermediateProgramParameter m n n0 ni → (Fin n → ℝ) → EReal :=
  fun w x =>
    data.h0 (data.A0.mulVec x + data.a0 - w.p0) +
      (((data.a0Star ⬝ᵥ x : ℝ) + data.α0 : ℝ) : EReal) +
      indicatorFunction (intermediateProgramFeasibleSet data w) x

/-- The canonical pairing `⟪w, w*⟫` between an intermediate-program perturbation parameter and
its dual parameter. -/
def intermediateProgramDualPairing {m n n0 : ℕ} {ni : Fin m → ℕ}
    (w : IntermediateProgramParameter m n n0 ni)
    (wStar : IntermediateProgramDualParameter m n n0 ni) : ℝ :=
  (w.v ⬝ᵥ wStar.vStar : ℝ) + (w.p0 ⬝ᵥ wStar.p0 : ℝ) +
    ∑ i : Fin m, (w.p i ⬝ᵥ wStar.p i : ℝ)

/-- The adjoint value `(H_{x*}^*)(w*)` of the intermediate-program bifunction, defined by the
usual infimum formula for a convex bifunction. -/
noncomputable def adjointOfIntermediateProgram {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni) :
    (Fin n → ℝ) → IntermediateProgramDualParameter m n n0 ni → EReal :=
  fun xStar wStar =>
    sInf (Set.range fun q : IntermediateProgramParameter m n n0 ni × (Fin n → ℝ) =>
      intermediateProgramBifunction data q.1 q.2 -
        (((q.2 ⬝ᵥ xStar : ℝ) : EReal)) +
        (((intermediateProgramDualPairing q.1 wStar : ℝ) : EReal)))

/-- The feasibility conditions in the explicit adjoint formula for the intermediate program:
`u* ≥ 0` and `a₀* + ∑ᵢ vᵢ* aᵢ* + A₀* p₀* + ∑ᵢ Aᵢ* pᵢ* = x*`. -/
def intermediateProgramDualFeasible {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni) (xStar : Fin n → ℝ)
    (wStar : IntermediateProgramDualParameter m n n0 ni) : Prop :=
  (∀ i : Fin m, 0 ≤ wStar.vStar i) ∧
    data.a0Star + ∑ i : Fin m, (wStar.vStar i) • data.aStar i +
        (data.A0.transpose.mulVec wStar.p0) +
        ∑ i : Fin m, (data.A i).transpose.mulVec (wStar.p i) = xStar

/-- The explicit dual objective in Theorem 6.30.24. For the book term
`(hᵢ^* vᵢ^*)(pᵢ^*)`, Lean uses the Fenchel conjugate of the scaled function
`y ↦ (vᵢ^* : EReal) * hᵢ(y)`. -/
noncomputable def intermediateProgramDualObjective {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (wStar : IntermediateProgramDualParameter m n n0 ni) : EReal :=
  (((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal) -
      fenchelConjugate n0 data.h0 wStar.p0) +
    ∑ i : Fin m,
      ((((data.α i * wStar.vStar i : ℝ) : EReal) +
            ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
        fenchelConjugate (ni i)
          (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
          (wStar.p i))

/-- The value of the dual program `(R*)`, expressed as the supremum of the explicit dual
objective over the feasible dual parameters. -/
noncomputable def dualProgramValueOfIntermediateProgram {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni) : EReal :=
  sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
    intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
      v = intermediateProgramDualObjective data wStar}

/-- Helper for Theorem 6.30.24: the displayed dual-program value identity is exactly the
definition of `dualProgramValueOfIntermediateProgram`. -/
lemma helperForTheorem_6_30_24_dualProgramValue_eq_explicitSup
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni) :
    dualProgramValueOfIntermediateProgram data =
      sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
        intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
          v = intermediateProgramDualObjective data wStar} := by
  -- This is the defining `sSup` expression for the dual value of the intermediate program.
  rfl

/-- Helper for Theorem 6.30.24: the perturbation parameter obtained from a primal point `x` and
domain witnesses `y₀`, `yᵢ` by solving the affine relations `A₀ x + a₀ - p₀ = y₀` and
`Aᵢ x + aᵢ - pᵢ = yᵢ`. -/
noncomputable def helperForTheorem_6_30_24_parameterFromWitnesses
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (x : Fin n → ℝ) (y0 : Fin n0 → ℝ) (y : ∀ i : Fin m, Fin (ni i) → ℝ) :
    IntermediateProgramParameter m n n0 ni :=
  { v := fun i =>
      (data.h i (y i) +
          ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal))).toReal
    p0 := data.A0.mulVec x + data.a0 - y0
    p := fun i => (data.A i).mulVec x + data.a i - y i }

/-- Helper for Theorem 6.30.24: if each constraint function is finite at a chosen witness point
`yᵢ`, then the perturbation parameter obtained by setting `pᵢ = Aᵢ x + aᵢ - yᵢ` and
`vᵢ = hᵢ(yᵢ) + ⟪aᵢ*, x⟫ + αᵢ` makes `x` feasible for the intermediate program. -/
lemma helperForTheorem_6_30_24_parameterFromWitnesses_feasiblePoint
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (x : Fin n → ℝ) (y0 : Fin n0 → ℝ) (y : ∀ i : Fin m, Fin (ni i) → ℝ)
    (hy : ∀ i : Fin m, data.h i (y i) ≠ (⊤ : EReal)) :
    x ∈ intermediateProgramFeasibleSet data
      (helperForTheorem_6_30_24_parameterFromWitnesses data x y0 y) := by
  -- Replacing each `pᵢ` by `Aᵢ x + aᵢ - yᵢ` turns the constraint expression back into `hᵢ(yᵢ)`,
  -- and the chosen `vᵢ` is exactly its real upper bound.
  simp [intermediateProgramFeasibleSet]
  intro i
  have hArg :
      (data.A i).mulVec x + data.a i -
          (helperForTheorem_6_30_24_parameterFromWitnesses data x y0 y).p i = y i := by
    ext j
    simp [helperForTheorem_6_30_24_parameterFromWitnesses, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  have hterm_ne_top :
      data.h i (y i) + ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal)) ≠ (⊤ : EReal) :=
    EReal.add_ne_top (hy i) (EReal.coe_ne_top _)
  -- The right-hand side is the `toReal` of that finite value, so `le_coe_toReal` yields the
  -- desired constraint inequality.
  rw [hArg]
  simpa [helperForTheorem_6_30_24_parameterFromWitnesses] using
    (EReal.le_coe_toReal
      (x := data.h i (y i) + ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal)))
      hterm_ne_top)

/-- Helper for Theorem 6.30.24: the one-dimensional constant-zero datum used to witness that the
current feasible-branch sign is wrong. -/
def helperForTheorem_6_30_24_wrongSignWitnessData :
    IntermediateProgramData 0 1 1 (fun i => Fin.elim0 i) :=
  { h0 := fun _ : Fin 1 → ℝ => (0 : EReal)
    A0 := 0
    a0 := 0
    a0Star := 0
    α0 := 0
    h := fun i => Fin.elim0 i
    A := fun i => Fin.elim0 i
    a := fun i => Fin.elim0 i
    aStar := fun i => Fin.elim0 i
    α := fun i => Fin.elim0 i }

/-- Helper for Theorem 6.30.24: the dual parameter paired with the canonical wrong-sign witness
datum. -/
def helperForTheorem_6_30_24_wrongSignWitnessDualParameter :
    IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i) :=
  { vStar := fun i => Fin.elim0 i
    p0 := fun _ : Fin 1 => (1 : ℝ)
    p := fun i => Fin.elim0 i }

/-- Helper for Theorem 6.30.24: the counterexample datum uses the constant-zero function, so its
objective term is closed proper convex. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_h0_closedProperConvex :
    IsClosedProperConvexERealFunction
      helperForTheorem_6_30_24_wrongSignWitnessData.h0 := by
  have hproper0 :
      ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
        (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
    -- The zero function is proper convex on the whole space.
    simpa using properConvexFunctionOn_const (n := 1) (c := (0 : ℝ))
  have hclosed0 :
      ClosedConvexFunction (fun _ : Fin 1 → ℝ => (0 : EReal)) := by
    -- Lower semicontinuity of a constant function gives closedness.
    exact
      (properConvexFunction_closed_iff_lowerSemicontinuous hproper0).2
        lowerSemicontinuous_const
  -- Unfolding the witness datum recovers exactly that zero function.
  simpa [helperForTheorem_6_30_24_wrongSignWitnessData] using
    (show IsClosedProperConvexERealFunction (fun _ : Fin 1 → ℝ => (0 : EReal)) from
      ⟨helperForLemma_26_2_properConvexERealFunction hproper0, hclosed0⟩)

/-- Helper for Theorem 6.30.24: there are no indexed constraint functions in the canonical
wrong-sign witness. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_h_closedProperConvex :
    ∀ i : Fin 0,
      IsClosedProperConvexERealFunction
        (helperForTheorem_6_30_24_wrongSignWitnessData.h i) := by
  -- The index type is empty, so every constraint claim is vacuous.
  intro i
  exact Fin.elim0 i

/-- Helper for Theorem 6.30.24: the canonical wrong-sign witness satisfies the explicit dual
feasibility conditions. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_feasible :
    intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
      (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter := by
  -- With no inequality coordinates and zero balance data, feasibility reduces to `0 = 0`.
  simp [intermediateProgramDualFeasible, helperForTheorem_6_30_24_wrongSignWitnessData,
    helperForTheorem_6_30_24_wrongSignWitnessDualParameter]

/-- Helper for Theorem 6.30.24: at the canonical witness, the explicit dual objective evaluates
to `-∞`. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_dualObjective_eq_bot :
    intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
      helperForTheorem_6_30_24_wrongSignWitnessDualParameter = (⊥ : EReal) := by
  have hOneNeZero :
      (fun _ : Fin 1 => (1 : ℝ)) ≠ (0 : Fin 1 → ℝ) := by
    -- The unique coordinate is `1`, so this covector is not zero.
    intro hone
    have hcoord := congrFun hone 0
    norm_num at hcoord
  -- The conjugate of the constant-zero function is the indicator of `{0}`.
  rw [intermediateProgramDualObjective]
  simp_rw [helperForTheorem_6_30_24_wrongSignWitnessData,
    helperForTheorem_6_30_24_wrongSignWitnessDualParameter]
  rw [section16_fenchelConjugate_const_zero]
  have hIndicator :
      indicatorFunction ({0} : Set (Fin 1 → ℝ)) (fun _ : Fin 1 => (1 : ℝ)) = (⊤ : EReal) := by
    -- Evaluating the indicator away from `0` yields `⊤`.
    simp [indicatorFunction, hOneNeZero]
  -- Every remaining finite term is zero, so the `⊤` contribution forces the total to `⊥`.
  simp [hIndicator]

/-- Helper for Theorem 6.30.24: negating the canonical witness objective flips `-∞` to `+∞`. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_negDualObjective_eq_top :
    -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
        helperForTheorem_6_30_24_wrongSignWitnessDualParameter = (⊤ : EReal) := by
  -- The already computed objective value is `⊥`, and `-⊥ = ⊤`.
  rw [helperForTheorem_6_30_24_wrongSignWitness_dualObjective_eq_bot]
  simp

/-- Helper for Theorem 6.30.24: the adjoint at the canonical witness is `-∞`, because the
defining infimum contains an unbounded affine ray. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_adjoint_eq_bot :
    adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
      (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter = (⊥ : EReal) := by
  -- To show the adjoint is `⊥`, it suffices to make the defining infimum arbitrarily small.
  rw [adjointOfIntermediateProgram, EReal.eq_bot_iff_forall_lt]
  intro y
  have hle :
      sInf (Set.range fun q :
          IntermediateProgramParameter 0 1 1 (fun i => Fin.elim0 i) × (Fin 1 → ℝ) =>
        intermediateProgramBifunction helperForTheorem_6_30_24_wrongSignWitnessData q.1 q.2 -
          (((q.2 ⬝ᵥ (0 : Fin 1 → ℝ) : ℝ) : EReal)) +
          (((intermediateProgramDualPairing q.1
              helperForTheorem_6_30_24_wrongSignWitnessDualParameter : ℝ) : EReal))) ≤
        (((y - 1 : ℝ) : EReal)) := by
    refine sInf_le ?_
    let w : IntermediateProgramParameter 0 1 1 (fun i => Fin.elim0 i) :=
      { v := fun i => Fin.elim0 i
        p0 := fun _ : Fin 1 => y - 1
        p := fun i => Fin.elim0 i }
    -- Choosing the zero primal vector and translating the `p₀` coordinate realizes the affine ray.
    refine ⟨(w, (0 : Fin 1 → ℝ)), ?_⟩
    simp [intermediateProgramBifunction, intermediateProgramFeasibleSet, indicatorFunction,
      intermediateProgramDualPairing, helperForTheorem_6_30_24_wrongSignWitnessData,
      helperForTheorem_6_30_24_wrongSignWitnessDualParameter, w, dotProduct]
  have hlt : (((y - 1 : ℝ) : EReal)) < ((y : ℝ) : EReal) := by
    -- The real inequality `y - 1 < y` transfers directly to `EReal`.
    exact_mod_cast (show y - 1 < y by linarith)
  exact lt_of_le_of_lt hle hlt

/-- Helper for Theorem 6.30.24: at the canonical witness, the adjoint agrees with the
positive-sign explicit dual objective. This is the sign that survives the direct computation. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_adjoint_eq_dualObjective :
    adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
        (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
      intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
        helperForTheorem_6_30_24_wrongSignWitnessDualParameter := by
  -- Both quantities evaluate to `⊥` at the named witness, so the positive-sign formula matches
  -- the concrete computation.
  rw [helperForTheorem_6_30_24_wrongSignWitness_adjoint_eq_bot,
    helperForTheorem_6_30_24_wrongSignWitness_dualObjective_eq_bot]

/-- Helper for Theorem 6.30.24: the canonical witness directly refutes the negative-sign feasible
branch of the current theorem statement. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_adjoint_ne_negDualObjective :
    adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
        (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter ≠
      -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
        helperForTheorem_6_30_24_wrongSignWitnessDualParameter := by
  -- The adjoint is `⊥`, while the negated dual objective is `⊤`.
  rw [helperForTheorem_6_30_24_wrongSignWitness_adjoint_eq_bot,
    helperForTheorem_6_30_24_wrongSignWitness_negDualObjective_eq_top]
  exact (bot_ne_top : (⊥ : EReal) ≠ (⊤ : EReal))

/-- Helper for Theorem 6.30.24: the named witness is dual-feasible, satisfies the corrected
positive-sign equality, and still refutes the current negative-sign equality. This packages the
exact sign comparison obstructing the theorem header. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_signComparison :
    intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
        (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter ∧
      adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
          (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
        intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
          helperForTheorem_6_30_24_wrongSignWitnessDualParameter ∧
      adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
          (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter ≠
        -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
          helperForTheorem_6_30_24_wrongSignWitnessDualParameter := by
  refine ⟨helperForTheorem_6_30_24_wrongSignWitness_feasible, ?_, ?_⟩
  · -- The direct computation already yields the corrected positive-sign equality.
    exact helperForTheorem_6_30_24_wrongSignWitness_adjoint_eq_dualObjective
  · -- The same witness computation still rules out the current negative-sign branch.
    exact helperForTheorem_6_30_24_wrongSignWitness_adjoint_ne_negDualObjective

/-- Helper for Theorem 6.30.24: the current feasible-branch sign already fails for a
one-dimensional constant-zero datum with no inequality constraints. -/
lemma helperForTheorem_6_30_24_exists_feasible_wrongSignWitness :
    ∃ (data : IntermediateProgramData 0 1 1 (fun i => Fin.elim0 i))
      (wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i)),
      IsClosedProperConvexERealFunction data.h0 ∧
      (∀ i : Fin 0, IsClosedProperConvexERealFunction (data.h i)) ∧
      intermediateProgramDualFeasible data (0 : Fin 1 → ℝ) wStar ∧
      adjointOfIntermediateProgram data (0 : Fin 1 → ℝ) wStar ≠
        -intermediateProgramDualObjective data wStar := by
  rcases helperForTheorem_6_30_24_wrongSignWitness_signComparison with
    ⟨hFeasible, _hCorrectedSign, hWrongSign⟩
  -- Reuse the named witness so later replans can cite the exact counterexample components.
  refine ⟨helperForTheorem_6_30_24_wrongSignWitnessData,
    helperForTheorem_6_30_24_wrongSignWitnessDualParameter, ?_, ?_, ?_, ?_⟩
  · exact helperForTheorem_6_30_24_wrongSignWitness_h0_closedProperConvex
  · exact helperForTheorem_6_30_24_wrongSignWitness_h_closedProperConvex
  · -- The packaged witness comparison records the explicit feasibility calculation.
    exact hFeasible
  · -- The same package keeps the computed negative-sign contradiction available.
    exact hWrongSign

/-- Helper for Theorem 6.30.24: at the named wrong-sign witness, even the feasible branch alone
of the current theorem body already contradicts the explicit adjoint and dual-objective
computations. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_feasibleBranch_false :
    ¬ (intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
          (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
        adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
          -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
            helperForTheorem_6_30_24_wrongSignWitnessDualParameter) := by
  intro hFeasibleBranch
  rcases helperForTheorem_6_30_24_wrongSignWitness_signComparison with
    ⟨hFeasible, _hCorrectedSign, hWrongSign⟩
  -- Feeding the named feasible witness into the current branch forces the impossible wrong-sign
  -- equality.
  have hForcedEquality :
      adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
          (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
        -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
          helperForTheorem_6_30_24_wrongSignWitnessDualParameter :=
    hFeasibleBranch hFeasible
  -- The packaged sign comparison closes the contradiction immediately.
  exact hWrongSign hForcedEquality

/-- Helper for Theorem 6.30.24: the theorem's branchwise adjoint formula already fails at the
named wrong-sign witness, even before adjoining the dual-program-value clause. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_branchFormulas_false :
    ¬ (∀ xStar : Fin 1 → ℝ,
          ∀ wStar : IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
            (intermediateProgramDualFeasible
                helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
              adjointOfIntermediateProgram
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar =
                -intermediateProgramDualObjective
                    helperForTheorem_6_30_24_wrongSignWitnessData wStar) ∧
            (¬ intermediateProgramDualFeasible
                helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar →
              adjointOfIntermediateProgram
                  helperForTheorem_6_30_24_wrongSignWitnessData xStar wStar = (⊥ : EReal))) := by
  intro hBranchFormulas
  -- Specializing the claimed branch formulas to the explicit feasible witness forces the wrong
  -- negative-sign equality.
  have hForcedEquality :
      adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
          (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
        -intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
          helperForTheorem_6_30_24_wrongSignWitnessDualParameter :=
    (hBranchFormulas (0 : Fin 1 → ℝ)
      helperForTheorem_6_30_24_wrongSignWitnessDualParameter).1
        helperForTheorem_6_30_24_wrongSignWitness_feasible
  -- The direct witness computation already shows that this equality is impossible.
  exact
    helperForTheorem_6_30_24_wrongSignWitness_adjoint_ne_negDualObjective
      hForcedEquality

/-- Helper for Theorem 6.30.24: at the named witness point, the corrected positive-sign feasible
branch and the unchanged infeasible branch both agree with the direct adjoint computation. This
isolates the error to the negative sign in the current theorem header. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_correctedBranchPair :
    (intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
          (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
        adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
          intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
            helperForTheorem_6_30_24_wrongSignWitnessDualParameter) ∧
      (¬ intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
        adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter = (⊥ : EReal)) := by
  constructor
  · intro _hFeasible
    -- The repaired feasible branch is exactly the positive-sign equality computed earlier.
    exact helperForTheorem_6_30_24_wrongSignWitness_adjoint_eq_dualObjective
  · intro _hInfeasible
    -- The adjoint stays `⊥` at this witness regardless of whether feasibility is assumed.
    exact helperForTheorem_6_30_24_wrongSignWitness_adjoint_eq_bot

/-- Helper for Theorem 6.30.24: at the named witness point, the corrected specialized theorem
conclusion already holds. This packages the repaired branch pair together with the unchanged
dual-program-value clause. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusion :
    (((intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
          adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
              (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
            intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
              helperForTheorem_6_30_24_wrongSignWitnessDualParameter) ∧
        (¬ intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
              (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
          adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
              (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
            (⊥ : EReal))) ∧
      dualProgramValueOfIntermediateProgram
          helperForTheorem_6_30_24_wrongSignWitnessData =
        sSup {v : EReal | ∃ wStar :
          IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
            intermediateProgramDualFeasible
                helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
              v = intermediateProgramDualObjective
                helperForTheorem_6_30_24_wrongSignWitnessData wStar}) := by
  refine ⟨?_, ?_⟩
  · -- The repaired branch pair was computed explicitly at the named witness.
    exact helperForTheorem_6_30_24_wrongSignWitness_correctedBranchPair
  · -- The dual-program-value clause is unchanged and still definitionally exact.
    exact
      helperForTheorem_6_30_24_dualProgramValue_eq_explicitSup
        helperForTheorem_6_30_24_wrongSignWitnessData

/-- Helper for Theorem 6.30.24: the corrected theorem body specialized to the named witness. This
abbreviation isolates the positive-sign repair route in a reusable proposition. -/
abbrev helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusionProp : Prop :=
  (((intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
          (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
        adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
          intermediateProgramDualObjective helperForTheorem_6_30_24_wrongSignWitnessData
            helperForTheorem_6_30_24_wrongSignWitnessDualParameter) ∧
      (¬ intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
        adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
          (⊥ : EReal))) ∧
    dualProgramValueOfIntermediateProgram
        helperForTheorem_6_30_24_wrongSignWitnessData =
      sSup {v : EReal | ∃ wStar :
        IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
          intermediateProgramDualFeasible
              helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
            v = intermediateProgramDualObjective
              helperForTheorem_6_30_24_wrongSignWitnessData wStar})

/-- Helper for Theorem 6.30.24: the current theorem body specialized to the named witness. This
abbreviation isolates the negative-sign branch that the witness computation refutes. -/
abbrev helperForTheorem_6_30_24_wrongSignWitness_currentSpecializedConclusionProp : Prop :=
  ((((intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
            (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
          adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
              (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
            -intermediateProgramDualObjective
                helperForTheorem_6_30_24_wrongSignWitnessData
                helperForTheorem_6_30_24_wrongSignWitnessDualParameter) ∧
        (¬ intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
              (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
          adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
              (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
            (⊥ : EReal))) ∧
      dualProgramValueOfIntermediateProgram
          helperForTheorem_6_30_24_wrongSignWitnessData =
        sSup {v : EReal | ∃ wStar :
          IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
            intermediateProgramDualFeasible
                helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
              v = intermediateProgramDualObjective
                helperForTheorem_6_30_24_wrongSignWitnessData wStar}))

/-- Helper for Theorem 6.30.24: even after adjoining the unchanged dual-program-value clause, the
current negative-sign specialized conclusion at the named witness is still impossible. This shows
that the obstruction is already present before any global quantifiers are considered. -/
lemma helperForTheorem_6_30_24_wrongSignWitness_currentSpecializedConclusion_false :
    ¬ ((((intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
              (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
            adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
                (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
              -intermediateProgramDualObjective
                  helperForTheorem_6_30_24_wrongSignWitnessData
                  helperForTheorem_6_30_24_wrongSignWitnessDualParameter) ∧
          (¬ intermediateProgramDualFeasible helperForTheorem_6_30_24_wrongSignWitnessData
                (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter →
            adjointOfIntermediateProgram helperForTheorem_6_30_24_wrongSignWitnessData
                (0 : Fin 1 → ℝ) helperForTheorem_6_30_24_wrongSignWitnessDualParameter =
              (⊥ : EReal))) ∧
        dualProgramValueOfIntermediateProgram
            helperForTheorem_6_30_24_wrongSignWitnessData =
          sSup {v : EReal | ∃ wStar :
            IntermediateProgramDualParameter 0 1 1 (fun i => Fin.elim0 i),
              intermediateProgramDualFeasible
                  helperForTheorem_6_30_24_wrongSignWitnessData (0 : Fin 1 → ℝ) wStar ∧
                v = intermediateProgramDualObjective
                  helperForTheorem_6_30_24_wrongSignWitnessData wStar})) := by
  intro hCurrentSpecialized
  -- The first component is exactly the wrong-sign feasible branch already refuted above.
  exact
    helperForTheorem_6_30_24_wrongSignWitness_feasibleBranch_false
      hCurrentSpecialized.1.1


end Section30
end Chap06

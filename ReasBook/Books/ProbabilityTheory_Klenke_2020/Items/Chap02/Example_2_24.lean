/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u v

variable {Ω : Type u} {ι : Type v} [Fintype ι] [Nonempty ι]

/-- The pointwise maximum of a finite nonempty family of real-valued random variables. -/
noncomputable def sampleMaximum (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ X i ω)

/-- The pointwise minimum of a finite nonempty family of real-valued random variables. -/
noncomputable def sampleMinimum (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ Finset.univ.inf' Finset.univ_nonempty (fun i ↦ X i ω)

section

variable [MeasurableSpace Ω] (P : Measure Ω) (X : ι → Ω → ℝ) (θ : ι → ℝ)

/-- Helper for Example 2.24: `maxCoord` is the coordinatewise maximum on `ι → ℝ`. -/
private noncomputable def maxCoord : (ι → ℝ) → ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ fun y : ι → ℝ ↦ y i

/-- Helper for Example 2.24: `minCoord` is the coordinatewise minimum on `ι → ℝ`. -/
private noncomputable def minCoord : (ι → ℝ) → ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i ↦ fun y : ι → ℝ ↦ y i

/-- Helper for Example 2.24: the joint law of a finite independent family is the finite product of
its marginal laws. -/
private theorem iIndepFun_hasLaw_pi {μ : ι → Measure ℝ} [IsProbabilityMeasure P]
    [∀ i, IsProbabilityMeasure (μ i)] (h_indep : iIndepFun X P)
    (h_law : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω i ↦ X i ω) (Measure.pi μ) P := by
  -- Proof comment: independence identifies the joint pushforward with the product of the marginal
  -- pushforwards, and the marginal law hypotheses replace those pushforwards by `μ i`.
  refine ⟨aemeasurable_pi_lambda _ fun i ↦ (h_law i).aemeasurable, ?_⟩
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (h_law i).aemeasurable).1 h_indep]
  congr 1
  funext i
  exact (h_law i).map_eq

/-- Helper for Example 2.24: the event that the coordinatewise maximum is at most `x` is the lower
orthant `Set.univ.pi (fun _ ↦ Set.Iic x)`. -/
private theorem sampleMaximum_preimage_Iic (x : ℝ) :
    (maxCoord (ι := ι)) ⁻¹' Set.Iic x =
      (Set.univ : Set ι).pi (fun _ ↦ Set.Iic x) := by
  -- Proof comment: unfold the maximum and rewrite the order condition with
  -- `Finset.sup'_le_iff`.
  ext y
  simp [maxCoord, Finset.sup'_le_iff, Pi.le_def]

/-- Helper for Example 2.24: the event that the coordinatewise minimum is strictly larger than `x`
is the upper orthant `Set.univ.pi (fun _ ↦ Set.Ioi x)`. -/
private theorem sampleMinimum_preimage_Ioi (x : ℝ) :
    (minCoord (ι := ι)) ⁻¹' Set.Ioi x =
      (Set.univ : Set ι).pi (fun _ ↦ Set.Ioi x) := by
  -- Proof comment: unfold the minimum and rewrite the order condition with
  -- `Finset.lt_inf'_iff`.
  ext y
  simp [minCoord, Finset.lt_inf'_iff]

/-- Helper for Example 2.24: the exponential survival function above `x` is
`if 0 ≤ x then exp (-(r * x)) else 1`. -/
private theorem expMeasure_real_Ioi {r x : ℝ} (hr : 0 < r) :
    (expMeasure r).real (Set.Ioi x) = if 0 ≤ x then Real.exp (-(r * x)) else 1 := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  by_cases hx : 0 ≤ x
  · -- Proof comment: on the nonnegative branch, compute the tail as the complement of the cdf.
    have hIic :
        (expMeasure r).real (Set.Iic x) = 1 - Real.exp (-(r * x)) := by
      rw [← cdf_eq_real (μ := expMeasure r) x, cdf_expMeasure_eq hr x, if_pos hx]
    calc
      (expMeasure r).real (Set.Ioi x) = 1 - (expMeasure r).real (Set.Iic x) := by
        simpa using
          (MeasureTheory.probReal_compl_eq_one_sub (μ := expMeasure r) (s := Set.Iic x)
            measurableSet_Iic)
      _ = Real.exp (-(r * x)) := by rw [hIic]; ring
      _ = if 0 ≤ x then Real.exp (-(r * x)) else 1 := by simp [hx]
  · -- Proof comment: on the negative branch, the interval `Set.Ioi x` is all of `ℝ`, so the
    -- cdf vanishes and the tail is therefore `1`.
    have hx' : x < 0 := lt_of_not_ge hx
    have hIic :
        (expMeasure r).real (Set.Iic x) = 0 := by
      rw [← cdf_eq_real (μ := expMeasure r) x, cdf_expMeasure_eq hr x, if_neg hx]
    calc
      (expMeasure r).real (Set.Ioi x) = 1 - (expMeasure r).real (Set.Iic x) := by
        simpa using
          (MeasureTheory.probReal_compl_eq_one_sub (μ := expMeasure r) (s := Set.Iic x)
            measurableSet_Iic)
      _ = 1 := by rw [hIic]; ring
      _ = if 0 ≤ x then Real.exp (-(r * x)) else 1 := by simp [hx]

-- Proof sketch: identify the event `{sampleMaximum X ≤ x}` with the intersection of the events
-- `{X i ≤ x}`, use independence to factor its probability into a product, and identify each
-- marginal factor with the corresponding exponential cdf.
/-- The cumulative distribution function of the maximum of a finite independent family of
exponential random variables with positive rates `θ i` is the product of the marginal exponential
cumulative distribution functions. -/
theorem cdf_sampleMaximum_eq_prod_exp
    (h_indep : iIndepFun X P) (h_exp : ∀ i, HasLaw (X i) (expMeasure (θ i)) P)
    (hθ : ∀ i, 0 < θ i)
    (x : ℝ) :
    cdf (P.map (sampleMaximum X)) x = ∏ i, cdf (expMeasure (θ i)) x := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  letI : IsProbabilityMeasure (expMeasure (θ i0)) := isProbabilityMeasure_expMeasure (hθ i0)
  letI : IsProbabilityMeasure P := (h_exp i0).isProbabilityMeasure
  letI : ∀ i, IsProbabilityMeasure (expMeasure (θ i)) :=
    fun i ↦ isProbabilityMeasure_expMeasure (hθ i)
  have hVec :
      HasLaw (fun ω i ↦ X i ω) (Measure.pi fun i ↦ expMeasure (θ i)) P :=
    iIndepFun_hasLaw_pi (P := P) (X := X) h_indep h_exp
  have hMaxCoordMeas :
      Measurable (maxCoord (ι := ι)) := by
    -- Proof comment: the maximum on a finite product is a measurable finite supremum of
    -- coordinate projections.
    simpa [maxCoord] using
      (Finset.measurable_sup' (α := ℝ) Finset.univ_nonempty fun i _ ↦
        (measurable_pi_apply i : Measurable fun y : ι → ℝ ↦ y i))
  letI : IsProbabilityMeasure ((Measure.pi fun i ↦ expMeasure (θ i)).map (maxCoord (ι := ι))) :=
    Measure.isProbabilityMeasure_map hMaxCoordMeas.aemeasurable
  have hMaxCoordLaw :
      HasLaw (maxCoord (ι := ι))
        ((Measure.pi fun i ↦ expMeasure (θ i)).map (maxCoord (ι := ι)))
        (Measure.pi fun i ↦ expMeasure (θ i)) := by
    refine ⟨hMaxCoordMeas.aemeasurable, rfl⟩
  have hMaxLaw :
      HasLaw (sampleMaximum X) ((Measure.pi fun i ↦ expMeasure (θ i)).map (maxCoord (ι := ι)))
        P := by
    -- Proof comment: transport the maximum from `Ω` to the canonical maximum on the product law.
    have hComp : (maxCoord (ι := ι)) ∘ (fun ω i ↦ X i ω) = sampleMaximum X := by
      funext ω
      simp [maxCoord, sampleMaximum, Function.comp]
    exact (HasLaw.comp hMaxCoordLaw hVec).congr (Filter.EventuallyEq.of_eq hComp.symm)
  calc
    cdf (P.map (sampleMaximum X)) x =
        cdf ((Measure.pi fun i ↦ expMeasure (θ i)).map (maxCoord (ι := ι))) x := by
      rw [hMaxLaw.map_eq]
    _ = (((Measure.pi fun i ↦ expMeasure (θ i)).map (maxCoord (ι := ι))) (Set.Iic x)).toReal := by
      rw [cdf_eq_real, Measure.real_def]
    _ = ((Measure.pi fun i ↦ expMeasure (θ i))
          ((Set.univ : Set ι).pi fun _ ↦ Set.Iic x)).toReal := by
      rw [Measure.map_apply hMaxCoordMeas measurableSet_Iic]
      rw [sampleMaximum_preimage_Iic (ι := ι) x]
    _ = (∏ i, expMeasure (θ i) (Set.Iic x)).toReal := by
      rw [Measure.pi_pi]
    _ = ∏ i, (expMeasure (θ i) (Set.Iic x)).toReal := by
      rw [ENNReal.toReal_prod]
    _ = ∏ i, cdf (expMeasure (θ i)) x := by
      refine Finset.prod_congr rfl ?_
      intro i _
      -- Proof comment: each coordinate factor is exactly the exponential cdf.
      symm
      rw [cdf_eq_real, Measure.real_def]

-- Proof sketch: rewrite `{sampleMinimum X ≤ x}` as the complement of the event that every
-- coordinate is larger than `x`, use independence to multiply the exponential survival
-- probabilities, and identify the resulting expression with the cdf of the exponential law of
-- rate `∑ i, θ i`.
/-- The cumulative distribution function of the minimum of a finite independent family of
exponential random variables with positive rates `θ i` agrees with the exponential cdf of rate
`∑ i, θ i`. -/
theorem cdf_sampleMinimum_eq_exp
    (h_indep : iIndepFun X P) (h_exp : ∀ i, HasLaw (X i) (expMeasure (θ i)) P)
    (hθ : ∀ i, 0 < θ i)
    (x : ℝ) :
    cdf (P.map (sampleMinimum X)) x = cdf (expMeasure (∑ i, θ i)) x := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  letI : IsProbabilityMeasure (expMeasure (θ i0)) := isProbabilityMeasure_expMeasure (hθ i0)
  letI : IsProbabilityMeasure P := (h_exp i0).isProbabilityMeasure
  letI : ∀ i, IsProbabilityMeasure (expMeasure (θ i)) :=
    fun i ↦ isProbabilityMeasure_expMeasure (hθ i)
  have hSumθ : 0 < ∑ i, θ i := by
    -- Proof comment: one positive summand already forces the full finite sum to be positive.
    calc
      0 < θ i0 := hθ i0
      _ ≤ ∑ i, θ i := by
        exact Finset.single_le_sum (fun j _ ↦ le_of_lt (hθ j)) (Finset.mem_univ i0)
  letI : IsProbabilityMeasure (expMeasure (∑ i, θ i)) := isProbabilityMeasure_expMeasure hSumθ
  have hVec :
      HasLaw (fun ω i ↦ X i ω) (Measure.pi fun i ↦ expMeasure (θ i)) P :=
    iIndepFun_hasLaw_pi (P := P) (X := X) h_indep h_exp
  have hMinCoordMeas :
      Measurable (minCoord (ι := ι)) := by
    -- Proof comment: the minimum is the supremum in `OrderDual ℝ`, so the same finite-supremum
    -- measurability lemma applies after dualizing the order.
    simpa [minCoord] using
      (Finset.measurable_sup' (α := OrderDual ℝ) Finset.univ_nonempty fun i _ ↦
        (measurable_pi_apply i : Measurable fun y : ι → ℝ ↦ y i))
  letI : IsProbabilityMeasure ((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι))) :=
    Measure.isProbabilityMeasure_map hMinCoordMeas.aemeasurable
  have hMinCoordLaw :
      HasLaw (minCoord (ι := ι))
        ((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι)))
        (Measure.pi fun i ↦ expMeasure (θ i)) := by
    refine ⟨hMinCoordMeas.aemeasurable, rfl⟩
  have hMinLaw :
      HasLaw (sampleMinimum X)
        ((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι)))
        P := by
    -- Proof comment: transport the minimum from `Ω` to the canonical minimum on the product law.
    have hComp : (minCoord (ι := ι)) ∘ (fun ω i ↦ X i ω) = sampleMinimum X := by
      funext ω
      simp [minCoord, sampleMinimum, Function.comp]
    exact (HasLaw.comp hMinCoordLaw hVec).congr (Filter.EventuallyEq.of_eq hComp.symm)
  have hTail :
      (((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι))).real (Set.Ioi x)) =
        ∏ i, if 0 ≤ x then Real.exp (-(θ i * x)) else 1 := by
    calc
      (((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι))).real (Set.Ioi x)) =
          ((((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι))) (Set.Ioi x))).toReal := by
        rw [Measure.real_def]
      _ = ((Measure.pi fun i ↦ expMeasure (θ i))
            ((Set.univ : Set ι).pi fun _ ↦ Set.Ioi x)).toReal := by
        rw [Measure.map_apply hMinCoordMeas measurableSet_Ioi]
        rw [sampleMinimum_preimage_Ioi (ι := ι) x]
      _ = (∏ i, expMeasure (θ i) (Set.Ioi x)).toReal := by
        rw [Measure.pi_pi]
      _ = ∏ i, (expMeasure (θ i) (Set.Ioi x)).toReal := by
        rw [ENNReal.toReal_prod]
      _ = ∏ i, if 0 ≤ x then Real.exp (-(θ i * x)) else 1 := by
        refine Finset.prod_congr rfl ?_
        intro i _
        -- Proof comment: each coordinate tail is the one-dimensional exponential survival
        -- function.
        simpa [Measure.real_def] using expMeasure_real_Ioi (x := x) (hθ i)
  have hTailExp :
      (∏ i, if 0 ≤ x then Real.exp (-(θ i * x)) else 1) =
        if 0 ≤ x then Real.exp (-((∑ i, θ i) * x)) else 1 := by
    by_cases hx : 0 ≤ x
    · -- Proof comment: on `x ≥ 0`, multiply exponential tails and collapse the exponent sum.
      suffices
          hExp : ∏ i, Real.exp (-(θ i * x)) =
            Real.exp (-((∑ i, θ i) * x)) by
        simpa only [hx, Finset.prod_ite_irrel, Finset.prod_const_one] using hExp
      rw [← Real.exp_sum]
      congr 1
      calc
        ∑ i, -(θ i * x) = ∑ i, (-θ i) * x := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
        _ = (∑ i, -θ i) * x := by rw [Finset.sum_mul]
        _ = -(∑ i, θ i) * x := by rw [Finset.sum_neg_distrib]
        _ = -((∑ i, θ i) * x) := by
          ring
    · -- Proof comment: on `x < 0`, every tail event is all of `ℝ`, so each factor is `1`.
      simp [hx]
  calc
    cdf (P.map (sampleMinimum X)) x =
        cdf ((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι))) x := by
      rw [hMinLaw.map_eq]
    _ = (((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι))).real (Set.Iic x)) := by
      rw [cdf_eq_real]
    _ = 1 - (((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι))).real (Set.Ioi x)) := by
      simpa using
        (MeasureTheory.probReal_compl_eq_one_sub
          (μ := ((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι))))
          (s := Set.Ioi x) measurableSet_Ioi)
    _ = 1 - ∏ i, if 0 ≤ x then Real.exp (-(θ i * x)) else 1 := by rw [hTail]
    _ = cdf (expMeasure (∑ i, θ i)) x := by
      rw [hTailExp]
      by_cases hx : 0 ≤ x
      · rw [if_pos hx, cdf_expMeasure_eq hSumθ x, if_pos hx]
      · rw [if_neg hx, cdf_expMeasure_eq hSumθ x, if_neg hx]
        simp

-- Proof sketch: a probability law on `ℝ` is determined by its cdf, so the previous cdf identity
-- identifies the law of `sampleMinimum X` with `expMeasure (∑ i, θ i)`.
/-- Example 2.24: The minimum of a finite independent family of exponentially distributed real
random variables with rates `θ i` is exponentially distributed with rate `∑ i, θ i`. -/
theorem sampleMinimum_hasLaw_expMeasure_sum
    (h_indep : iIndepFun X P) (h_exp : ∀ i, HasLaw (X i) (expMeasure (θ i)) P)
    (hθ : ∀ i, 0 < θ i) :
    HasLaw (sampleMinimum X) (expMeasure (∑ i, θ i)) P := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  letI : IsProbabilityMeasure (expMeasure (θ i0)) := isProbabilityMeasure_expMeasure (hθ i0)
  letI : IsProbabilityMeasure P := (h_exp i0).isProbabilityMeasure
  have hSumθ : 0 < ∑ i, θ i := by
    -- Proof comment: the finite sum of strictly positive rates is again strictly positive.
    calc
      0 < θ i0 := hθ i0
      _ ≤ ∑ i, θ i := by
        exact Finset.single_le_sum (fun j _ ↦ le_of_lt (hθ j)) (Finset.mem_univ i0)
  letI : IsProbabilityMeasure (expMeasure (∑ i, θ i)) := isProbabilityMeasure_expMeasure hSumθ
  letI : ∀ i, IsProbabilityMeasure (expMeasure (θ i)) :=
    fun i ↦ isProbabilityMeasure_expMeasure (hθ i)
  have hVec :
      HasLaw (fun ω i ↦ X i ω) (Measure.pi fun i ↦ expMeasure (θ i)) P :=
    iIndepFun_hasLaw_pi (P := P) (X := X) h_indep h_exp
  have hMinCoordMeas : Measurable (minCoord (ι := ι)) := by
    -- Proof comment: the product minimum is measurable after dualizing the order.
    simpa [minCoord] using
      (Finset.measurable_sup' (α := OrderDual ℝ) Finset.univ_nonempty fun i _ ↦
        (measurable_pi_apply i : Measurable fun y : ι → ℝ ↦ y i))
  have hMinCoordLaw :
      HasLaw (minCoord (ι := ι))
        ((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι)))
        (Measure.pi fun i ↦ expMeasure (θ i)) := by
    refine ⟨hMinCoordMeas.aemeasurable, rfl⟩
  have hMinLaw :
      HasLaw (sampleMinimum X)
        ((Measure.pi fun i ↦ expMeasure (θ i)).map (minCoord (ι := ι)))
        P := by
    -- Proof comment: re-express `sampleMinimum X` as the canonical minimum composed with the joint
    -- sample vector.
    have hComp : (minCoord (ι := ι)) ∘ (fun ω i ↦ X i ω) = sampleMinimum X := by
      funext ω
      simp [minCoord, sampleMinimum, Function.comp]
    exact (HasLaw.comp hMinCoordLaw hVec).congr (Filter.EventuallyEq.of_eq hComp.symm)
  letI : IsProbabilityMeasure (P.map (sampleMinimum X)) :=
    Measure.isProbabilityMeasure_map hMinLaw.aemeasurable
  refine ⟨hMinLaw.aemeasurable, ?_⟩
  -- Proof comment: the previous cdf identity determines the pushed-forward measure uniquely.
  apply MeasureTheory.Measure.eq_of_cdf
  ext x
  exact cdf_sampleMinimum_eq_exp (P := P) (X := X) (θ := θ) h_indep h_exp hθ x

end

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_24

open MeasureTheory ProbabilityTheory Set

namespace MeasureTheory

/-- The Dirac probability measure at `0` is invariant under negation. -/
instance diracProba_zero_isNegInvariant :
    Measure.IsNegInvariant (((diracProba (0 : ℝ)) : ProbabilityMeasure ℝ) : Measure ℝ) := by
  refine ⟨?_⟩
  -- Proof comment: pushing the Dirac mass at `0` forward along negation leaves it unchanged.
  simp [Measure.neg, MeasureTheory.diracProba]

end MeasureTheory

/-- The function `t ↦ exp (-|r t|^α)` appearing in the symmetric stable-law corollary. -/
noncomputable def symmetricStableCharFun (α r : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-(|r * t| ^ α : ℝ))

-- Proof sketch: unfold `symmetricStableCharFun`; this is exactly its defining formula.
/-- The defining formula for `symmetricStableCharFun`. -/
theorem symmetricStableCharFun_apply (α r t : ℝ) :
    symmetricStableCharFun α r t = Complex.exp (-(|r * t| ^ α : ℝ)) := by
  -- Proof comment: this is just the defining equation of `symmetricStableCharFun`.
  rfl

/-- Helper for Corollary 15.25: `symmetricStableCharFun α r` is even in the frequency variable. -/
lemma symmetricStableCharFun_neg (α r t : ℝ) :
    symmetricStableCharFun α r (-t) = symmetricStableCharFun α r t := by
  -- Proof comment: the kernel depends on `t` only through `|r * t|`.
  rw [symmetricStableCharFun_apply, symmetricStableCharFun_apply]
  congr 1
  rw [mul_neg, abs_neg]

/-- Helper for Corollary 15.25: a probability measure with characteristic function
`symmetricStableCharFun α r` is invariant under negation. -/
lemma isNegInvariant_of_charFun_eq_symmetricStableCharFun
    (μ : ProbabilityMeasure ℝ) {α r : ℝ}
    (hμ : ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t) :
    ((μ : Measure ℝ)).IsNegInvariant := by
  refine ⟨?_⟩
  have hμnegFinite : IsFiniteMeasure ((μ : Measure ℝ)).neg := by
    simpa [Measure.neg] using
      (inferInstance : IsFiniteMeasure (Measure.map (fun x : ℝ ↦ -x) (μ : Measure ℝ)))
  letI : IsFiniteMeasure ((μ : Measure ℝ)).neg := hμnegFinite
  -- Proof comment: characteristic functions determine finite measures, so compare `μ.neg` and `μ`
  -- through their transforms.
  apply Measure.ext_of_charFun
  funext t
  calc
    charFun ((μ : Measure ℝ)).neg t
        = charFun (μ : Measure ℝ) ((-1 : ℝ) * t) := by
            simpa [Measure.neg] using
              (MeasureTheory.charFun_map_mul (μ := (μ : Measure ℝ)) (-1) t)
    _ = charFun μ (-t) := by simp
    _ = symmetricStableCharFun α r (-t) := hμ (-t)
    _ = symmetricStableCharFun α r t := symmetricStableCharFun_neg α r t
    _ = charFun μ t := by simpa using (hμ t).symm

/-- Helper for Corollary 15.25: on `Set.Ici 0`, the symmetric stable kernel satisfies the convexity
hypothesis in Theorem 15.24. -/
lemma convexOn_symmetricStableKernel
    (α r : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    ConvexOn ℝ (Set.Ici 0) (fun t : ℝ ↦ Real.exp (-(|r * t| ^ α))) := by
  have hα_nonneg : 0 ≤ α := le_of_lt hα₀
  let c : ℝ := |r| ^ α
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact Real.rpow_nonneg (abs_nonneg r) α
  have hconcavePow : ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ ↦ t ^ α) :=
    Real.concaveOn_rpow hα_nonneg hα₁
  have hconcaveScaled : ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ ↦ c * (t ^ α)) := by
    -- Proof comment: scaling a concave nonnegative-ray power by the nonnegative constant `|r|^α`
    -- preserves concavity.
    simpa [smul_eq_mul] using hconcavePow.smul hc_nonneg
  have hconvInnerNormalized : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ ↦ -(c * (t ^ α))) := by
    -- Proof comment: negating a concave function turns it into a convex one.
    exact neg_convexOn_iff.mpr hconcaveScaled
  have hconvInner : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ ↦ -(|r * t| ^ α)) := by
    refine hconvInnerNormalized.congr ?_
    intro t ht
    have ht0 : 0 ≤ t := ht
    -- Proof comment: on `[0, ∞)`, the absolute value simplifies and the kernel normalizes to a
    -- scalar multiple of `t ^ α`.
    calc
      -(c * (t ^ α)) = -(((|r|) * t) ^ α) := by
        dsimp [c]
        rw [Real.mul_rpow (abs_nonneg r) ht0]
      _ = -(|r * t| ^ α) := by
        rw [abs_mul, abs_of_nonneg ht0]
  have hinner_cont : ContinuousOn (fun t : ℝ ↦ -(|r * t| ^ α)) (Set.Ici 0) := by
    -- Proof comment: the inner exponent is continuous on the nonnegative ray.
    refine (((continuous_const.mul continuous_id).abs.rpow_const ?_).neg).continuousOn
    intro t
    exact Or.inr hα_nonneg
  have hconvImage : Convex ℝ ((fun t : ℝ ↦ -(|r * t| ^ α)) '' Set.Ici 0) := by
    rw [Real.convex_iff_isPreconnected]
    refine isPreconnected_Ici.image _ ?_
    intro x hx
    exact hinner_cont x hx
  have hconvExp : ConvexOn ℝ ((fun t : ℝ ↦ -(|r * t| ^ α)) '' Set.Ici 0) Real.exp := by
    refine convexOn_exp.subset (subset_univ _) hconvImage
  have hmonoExp : MonotoneOn Real.exp ((fun t : ℝ ↦ -(|r * t| ^ α)) '' Set.Ici 0) :=
    Real.exp_monotone.monotoneOn _
  -- Proof comment: `exp` is convex and increasing on `(-∞, 0]`, so composing it with the convex
  -- inner exponent preserves convexity.
  simpa [Function.comp] using hconvExp.comp hconvInner hmonoExp

-- Proof sketch: apply Theorem 15.24 to the function `t ↦ exp (-|r t|^α)`, using the positivity
-- condition `0 < α ≤ 1` to obtain a probability measure with this characteristic function; then
-- use the evenness of the function to deduce the owner symmetry property
-- `Measure.IsNegInvariant`.
/-- Corollary 15.25: for every `α ∈ (0,1]` and `r ∈ ℝ`, the function
`t ↦ exp (-|r t|^α)` is the characteristic function of a symmetric probability measure on `ℝ`. -/
theorem exists_symmetricProbabilityMeasure_charFun_eq_symmetricStableCharFun
    (α r : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    ∃ μ : ProbabilityMeasure ℝ, ((μ : Measure ℝ)).IsNegInvariant ∧
      ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t := by
  let f : ℝ → ℝ := fun t ↦ Real.exp (-(|r * t| ^ α))
  have hα_nonneg : 0 ≤ α := le_of_lt hα₀
  have hf_cont : Continuous f := by
    -- Proof comment: the kernel is built from continuous multiplication, absolute value, `rpow`,
    -- and the real exponential.
    refine Real.continuous_exp.comp ?_
    refine ((continuous_const.mul continuous_id).abs.rpow_const ?_).neg
    intro t
    exact Or.inr hα_nonneg
  have hf_even : Function.Even f := by
    intro t
    -- Proof comment: the real kernel is even because the absolute value absorbs the sign change.
    simp [f, abs_neg]
  have hf_zero : f 0 = 1 := by
    -- Proof comment: the exponent vanishes at `0`.
    simp [f, Real.zero_rpow hα₀.ne']
  have hf_unit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    refine ⟨Real.exp_pos _ |>.le, ?_⟩
    have hexp_nonpos : -(|r * x| ^ α : ℝ) ≤ 0 := by
      exact neg_nonpos.mpr (Real.rpow_nonneg (abs_nonneg (r * x)) α)
    simpa [f] using (Real.exp_le_one_iff.mpr hexp_nonpos)
  have hf_convex : ConvexOn ℝ (Set.Ici 0) f := convexOn_symmetricStableKernel α r hα₀ hα₁
  rcases exists_probabilityMeasure_charFun_eq_of_continuous_even_convexOn_unitInterval
      f hf_cont hf_even hf_zero hf_unit hf_convex with ⟨μ, hμchar⟩
  have hμstable : ∀ t : ℝ, charFun μ t = symmetricStableCharFun α r t := by
    intro t
    -- Proof comment: the Polya kernel matches the target complex formula by `Complex.ofReal_exp`.
    calc
      charFun μ t = (f t : ℂ) := hμchar t
      _ = Complex.exp (-(|r * t| ^ α : ℝ)) := by
            simp [f, Complex.ofReal_exp]
      _ = symmetricStableCharFun α r t := by
            rw [symmetricStableCharFun_apply]
  refine ⟨μ, ?_, hμstable⟩
  -- Proof comment: the even characteristic function forces negation invariance of the law.
  exact isNegInvariant_of_charFun_eq_symmetricStableCharFun μ hμstable

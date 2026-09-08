module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import Mathlib.Analysis.Asymptotics.Lemmas

public section

open Filter
open scoped BigOperators Topology

namespace Asymptotics.IsUniformRemainderOn

universe u v w

/-- Uniform remainder estimates of the same order are closed under pointwise addition. -/
theorem add {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R S : Θ → ℝ → E} {s : Set Θ} {C D q : ℝ}
    (hR : IsUniformRemainderOn R s C q) (hS : IsUniformRemainderOn S s D q) :
    IsUniformRemainderOn (fun θ ε ↦ R θ ε + S θ ε) s (C + D) q := by
  -- Transport both estimates to the common product filter and use the fixed-gauge sum rule.
  refine (isBigOWith_iff (fun θ ε ↦ R θ ε + S θ ε) s (C + D) q).mp ?_
  exact ((isBigOWith_iff R s C q).mpr hR).add ((isBigOWith_iff S s D q).mpr hS)

/-- Uniform remainder estimates of the same order are closed under pointwise subtraction. -/
theorem sub {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R S : Θ → ℝ → E} {s : Set Θ} {C D q : ℝ}
    (hR : IsUniformRemainderOn R s C q) (hS : IsUniformRemainderOn S s D q) :
    IsUniformRemainderOn (fun θ ε ↦ R θ ε - S θ ε) s (C + D) q := by
  -- Transport both estimates to the common product filter and use the fixed-gauge difference rule.
  refine (isBigOWith_iff (fun θ ε ↦ R θ ε - S θ ε) s (C + D) q).mp ?_
  exact ((isBigOWith_iff R s C q).mpr hR).sub ((isBigOWith_iff S s D q).mpr hS)

/-- Multiplication by a fixed scalar scales a uniform remainder coefficient by its norm. -/
theorem const_smul {Θ : Type u} {𝕜 : Type v} {E : Type w} [SeminormedRing 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {R : Θ → ℝ → E} {s : Set Θ}
    {C q : ℝ} (a : 𝕜) (hR : IsUniformRemainderOn R s C q) :
    IsUniformRemainderOn (fun θ ε ↦ a • R θ ε) s (‖a‖ * C) q := by
  -- The fixed-scalar asymptotic rule preserves the gauge and scales its coefficient.
  refine (isBigOWith_iff (fun θ ε ↦ a • R θ ε) s (‖a‖ * C) q).mp ?_
  exact ((isBigOWith_iff R s C q).mpr hR).const_smul_left a

/-- Pointwise scalar multiplication adds the orders and multiplies the coefficients of
uniform remainder estimates. -/
theorem smul {Θ : Type u} {𝕜 : Type v} {E : Type w} [SeminormedRing 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {a : Θ → ℝ → 𝕜}
    {R : Θ → ℝ → E} {s : Set Θ} {C D p q : ℝ}
    (ha : IsUniformRemainderOn a s C p) (hR : IsUniformRemainderOn R s D q)
    (_hC : 0 ≤ C) (_hD : 0 ≤ D) (hp : 0 ≤ p) (_hq : 0 ≤ q) :
    IsUniformRemainderOn (fun θ ε ↦ a θ ε • R θ ε) s (C * D) (p + q) := by
  -- Multiply the filter estimates, then identify the product gauge with the summed exponent.
  refine (isBigOWith_iff (fun θ ε ↦ a θ ε • R θ ε) s (C * D) (p + q)).mp ?_
  have h := ((isBigOWith_iff a s C p).mpr ha).smul ((isBigOWith_iff R s D q).mpr hR)
  exact h.congr_right fun z ↦
    (Real.rpow_add_of_nonneg (abs_nonneg z.2) hp _hq).symm

/-- Pointwise multiplication adds the orders and multiplies the coefficients of uniform
remainder estimates. -/
theorem mul {Θ : Type u} {A : Type v} [SeminormedRing A] {R S : Θ → ℝ → A}
    {s : Set Θ} {C D p q : ℝ}
    (hR : IsUniformRemainderOn R s C p) (hS : IsUniformRemainderOn S s D q)
    (_hC : 0 ≤ C) (_hD : 0 ≤ D) (hp : 0 ≤ p) (_hq : 0 ≤ q) :
    IsUniformRemainderOn (fun θ ε ↦ R θ ε * S θ ε) s (C * D) (p + q) := by
  -- Multiply the filter estimates, then identify the product gauge with the summed exponent.
  refine (isBigOWith_iff (fun θ ε ↦ R θ ε * S θ ε) s (C * D) (p + q)).mp ?_
  have h := ((isBigOWith_iff R s C p).mpr hR).mul ((isBigOWith_iff S s D q).mpr hS)
  exact h.congr_right fun z ↦
    (Real.rpow_add_of_nonneg (abs_nonneg z.2) hp _hq).symm

/-- Taking norms preserves the coefficient and order of a uniform remainder estimate. -/
theorem norm {Θ : Type u} {E : Type v} [SeminormedAddCommGroup E]
    {R : Θ → ℝ → E} {s : Set Θ} {C q : ℝ} (hR : IsUniformRemainderOn R s C q) :
    IsUniformRemainderOn (fun θ ε ↦ ‖R θ ε‖) s C q := by
  -- The asymptotic norm-left equivalence leaves coefficient and gauge unchanged.
  refine (isBigOWith_iff (fun θ ε ↦ ‖R θ ε‖) s C q).mp ?_
  exact ((isBigOWith_iff R s C q).mpr hR).norm_left

/-- A finite pointwise product in a seminormed ring whose norm fixes one has the product
coefficient and sum order of its factors. -/
theorem finsetProd {Θ : Type u} {ι : Type v} {A : Type w} [SeminormedCommRing A]
    [NormOneClass A]
    (u : Finset ι) {R : ι → Θ → ℝ → A} {s : Set Θ} {C q : ι → ℝ}
    (hR : ∀ i ∈ u, IsUniformRemainderOn (R i) s (C i) (q i))
    (hC : ∀ i ∈ u, 0 ≤ C i) (hq : ∀ i ∈ u, 0 ≤ q i) :
    IsUniformRemainderOn (fun θ ε ↦ ∏ i ∈ u, R i θ ε) s
      (∏ i ∈ u, C i) (∑ i ∈ u, q i) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      -- The empty product is the constant one, bounded by the order-zero gauge.
      refine (isBigOWith_iff (fun θ ε ↦ ∏ i ∈ ∅, R i θ ε) s
        (∏ i ∈ ∅, C i) (∑ i ∈ ∅, q i)).mp ?_
      refine IsBigOWith.of_bound (Filter.Eventually.of_forall fun z ↦ ?_)
      simp only [Finset.prod_empty, Finset.sum_empty, norm_one, Real.rpow_zero, one_mul, le_refl]
  | @insert i u hi ih =>
      have huR : IsUniformRemainderOn (fun θ ε ↦ ∏ j ∈ u, R j θ ε) s
          (∏ j ∈ u, C j) (∑ j ∈ u, q j) :=
        ih (fun j hj ↦ hR j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hC j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hq j (Finset.mem_insert_of_mem hj))
      -- Insert the new factor using the binary product theorem and its accumulated side conditions.
      have hprod := mul (hR i (Finset.mem_insert_self i u)) huR
        (hC i (Finset.mem_insert_self i u))
        (Finset.prod_nonneg fun j hj ↦ hC j (Finset.mem_insert_of_mem hj))
        (hq i (Finset.mem_insert_self i u))
        (Finset.sum_nonneg fun j hj ↦ hq j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.prod_insert hi, Finset.sum_insert hi] using hprod

/-- Division by a factor with a uniform eventual positive norm lower bound preserves a
uniform remainder estimate. -/
theorem div {Θ : Type u} {𝕜 : Type v} [NormedDivisionRing 𝕜]
    {R D : Θ → ℝ → 𝕜} {s : Set Θ} {C q m : ℝ}
    (hR : IsUniformRemainderOn R s C q) (hm : 0 < m)
    (hD : ∀ᶠ z in principal s ×ˢ 𝓝 0, m ≤ ‖D z.1 z.2‖) :
    IsUniformRemainderOn (fun θ ε ↦ R θ ε / D θ ε) s (C / m) q := by
  -- Move to the product filter so the numerator and denominator bounds can be intersected.
  refine (isBigOWith_iff (fun θ ε ↦ R θ ε / D θ ε) s (C / m) q).mp ?_
  have hR' := (isBigOWith_iff R s C q).mpr hR
  refine IsBigOWith.of_bound ?_
  filter_upwards [hR'.bound, hD] with z hzR hzD
  have hzR' : ‖R z.1 z.2‖ ≤ C * |z.2| ^ q := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg z.2) q)] using hzR
  have hDpos : 0 < ‖D z.1 z.2‖ := hm.trans_le hzD
  have hnum : 0 ≤ C * |z.2| ^ q := (norm_nonneg _).trans hzR'
  calc
    ‖R z.1 z.2 / D z.1 z.2‖ = ‖R z.1 z.2‖ / ‖D z.1 z.2‖ := norm_div _ _
    _ ≤ (C * |z.2| ^ q) / ‖D z.1 z.2‖ :=
      div_le_div_of_nonneg_right hzR' (norm_nonneg _)
    _ ≤ (C * |z.2| ^ q) / m := div_le_div_of_nonneg_left hnum hm hzD
    _ = (C / m) * |z.2| ^ q := (div_mul_eq_mul_div C m (|z.2| ^ q)).symm
    _ = (C / m) * ‖|z.2| ^ q‖ := congrArg (fun t : ℝ ↦ (C / m) * t)
      (Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg z.2) q)).symm

end Asymptotics.IsUniformRemainderOn

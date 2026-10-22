/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Data.PNat.Notation
public import TR_LALM_theory.Assumption_3_1.Oracle

public section

open MeasureTheory
open scoped NNReal

namespace SPIDER

universe u v

variable {n : ℕ} {Ξ : Type u} [MeasurableSpace Ξ]
variable {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {region : Set (EuclideanSpace ℝ (Fin n))}
variable {Ω : Type v}

/-- Radial projection of a Euclidean vector onto the closed ball of radius `G`. -/
@[expose] noncomputable def clip (G : ℝ≥0) (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  if ‖z‖ ≤ G then z else (G / ‖z‖) • z

/-- Clipping fixes every vector already in the closed ball of radius `G`. -/
theorem clip_eq_self (G : ℝ≥0) (z : EuclideanSpace ℝ (Fin n))
    (hz : ‖z‖ ≤ G) :
    clip G z = z := by
  simp only [clip, if_pos hz]

/-- The norm of a clipped vector is at most the clipping radius. -/
theorem norm_clip_le (G : ℝ≥0) (z : EuclideanSpace ℝ (Fin n)) :
    ‖clip G z‖ ≤ G := by
  by_cases hz : ‖z‖ ≤ (G : ℝ)
  · rw [clip_eq_self G z hz]
    exact hz
  · have hnormPositive : 0 < ‖z‖ := by
      exact lt_of_le_of_lt G.coe_nonneg (lt_of_not_ge hz)
    have hratioNonnegative : 0 ≤ (G : ℝ) / ‖z‖ := by
      positivity
    rw [clip, if_neg hz, norm_smul, Real.norm_of_nonneg hratioNonnegative,
      div_mul_cancel₀ (G : ℝ) hnormPositive.ne']

/-- Clipping cannot increase distance from a vector in the clipping ball. -/
theorem norm_clip_sub_le (G : ℝ≥0) (z g : EuclideanSpace ℝ (Fin n))
    (hg : ‖g‖ ≤ G) :
    ‖clip G z - g‖ ≤ ‖z - g‖ := by
  by_cases hz : ‖z‖ ≤ (G : ℝ)
  · rw [clip_eq_self G z hz]
  · have hnormPositive : 0 < ‖z‖ := by
      exact lt_of_le_of_lt G.coe_nonneg (lt_of_not_ge hz)
    have hratioNonnegative : 0 ≤ (G : ℝ) / ‖z‖ := by
      positivity
    have hratioLeOne : (G : ℝ) / ‖z‖ ≤ 1 := by
      exact (div_le_one hnormPositive).2 (le_of_not_ge hz)
    have hscale : (G : ℝ) / ‖z‖ * ‖z‖ = G := by
      exact div_mul_cancel₀ (G : ℝ) hnormPositive.ne'
    have hinner : inner ℝ z g ≤ ‖z‖ * (G : ℝ) := by
      exact (real_inner_le_norm z g).trans
        (mul_le_mul_of_nonneg_left hg (norm_nonneg z))
    have hfactorNonnegative : 0 ≤ 1 - (G : ℝ) / ‖z‖ := sub_nonneg.mpr hratioLeOne
    have hbracketNonnegative :
        0 ≤ (1 + (G : ℝ) / ‖z‖) * ‖z‖ ^ 2 - 2 * inner ℝ z g := by
      nlinarith [sq_nonneg ‖z‖]
    have hproductNonnegative := mul_nonneg hfactorNonnegative hbracketNonnegative
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [clip, if_neg hz, norm_sub_sq_real, norm_sub_sq_real, norm_smul,
      Real.norm_of_nonneg hratioNonnegative, real_inner_smul_left]
    nlinarith

/-- The recursive SPIDER raw gradient estimate, using a fresh batch at refresh
indices and same-sample gradient differences at all other indices. -/
@[expose] noncomputable def rawEstimate
    (oracle : EqualityConstrained.StochasticOracle f region ν)
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → ℕ → Ω → Ξ) (Q B b : ℕ+) :
    ℕ → Ω → EuclideanSpace ℝ (Fin n)
  | 0, ω =>
      (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
        oracle.sampleGradient (point 0 ω) (sample 0 i ω)
  | k + 1, ω =>
      if (k + 1) % Q = 0 then
        (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
          oracle.sampleGradient (point (k + 1) ω) (sample (k + 1) i ω)
      else
        rawEstimate oracle point sample Q B b k ω +
          (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
            (oracle.sampleGradient (point (k + 1) ω) (sample (k + 1) i ω) -
              oracle.sampleGradient (point k ω) (sample (k + 1) i ω))

/-- At a refresh index, the raw estimate is the average of the fresh `B`-sample
batch. -/
theorem rawEstimate_of_refresh
    (oracle : EqualityConstrained.StochasticOracle f region ν)
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → ℕ → Ω → Ξ) (Q B b : ℕ+) (k : ℕ) (ω : Ω)
    (hk : k % Q = 0) :
    rawEstimate oracle point sample Q B b k ω =
      (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
        oracle.sampleGradient (point k ω) (sample k i ω) := by
  cases k with
  | zero => rfl
  | succ k => simp only [rawEstimate, hk, if_pos]

/-- At a nonrefresh positive index, the raw estimate adds the average of
same-sample gradient differences to the preceding estimate. -/
theorem rawEstimate_of_update
    (oracle : EqualityConstrained.StochasticOracle f region ν)
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → ℕ → Ω → Ξ) (Q B b : ℕ+) (k : ℕ) (ω : Ω)
    (hk : (k + 1) % Q ≠ 0) :
    rawEstimate oracle point sample Q B b (k + 1) ω =
      rawEstimate oracle point sample Q B b k ω +
        (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
          (oracle.sampleGradient (point (k + 1) ω) (sample (k + 1) i ω) -
            oracle.sampleGradient (point k ω) (sample (k + 1) i ω)) := by
  simp [rawEstimate, hk]

/-- The projected SPIDER gradient estimate obtained by clipping the raw estimate. -/
@[expose] noncomputable def estimate (G : ℝ≥0)
    (oracle : EqualityConstrained.StochasticOracle f region ν)
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → ℕ → Ω → Ξ) (Q B b : ℕ+)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  clip G (rawEstimate oracle point sample Q B b k ω)

/-- The projected estimate is clipping applied to the recursive raw estimate. -/
theorem estimate_apply (G : ℝ≥0)
    (oracle : EqualityConstrained.StochasticOracle f region ν)
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → ℕ → Ω → Ξ) (Q B b : ℕ+)
    (k : ℕ) (ω : Ω) :
    estimate G oracle point sample Q B b k ω =
      clip G (rawEstimate oracle point sample Q B b k ω) := rfl

/-- The projected SPIDER gradient error relative to the deterministic objective. -/
@[expose] noncomputable def error (G : ℝ≥0)
    (oracle : EqualityConstrained.StochasticOracle f region ν)
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → ℕ → Ω → Ξ) (Q B b : ℕ+)
    (k : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  estimate G oracle point sample Q B b k ω - gradient f (point k ω)

/-- The SPIDER error is the projected estimate minus the deterministic gradient. -/
theorem error_apply (G : ℝ≥0)
    (oracle : EqualityConstrained.StochasticOracle f region ν)
    (point : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (sample : ℕ → ℕ → Ω → Ξ) (Q B b : ℕ+)
    (k : ℕ) (ω : Ω) :
    error G oracle point sample Q B b k ω =
      estimate G oracle point sample Q B b k ω - gradient f (point k ω) := rfl

end SPIDER

end

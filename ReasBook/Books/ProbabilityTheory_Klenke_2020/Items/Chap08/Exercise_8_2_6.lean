/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω}

-- Proof sketch: for each rational `q`, apply `condExp_nonneg` to `(X + q • Y)^2`, then expand
-- the conditional expectation with `condExp_add` and `condExp_smul`. This yields a pointwise
-- nonnegative quadratic polynomial in `q`; extend it to all real `t` by density of `ℚ` and bound
-- the discriminant.
/-- Exercise 8.2.6: for square-integrable real random variables `X` and `Y`, the conditional
Cauchy--Schwarz inequality states that the square of the conditional expectation of `XY` is bounded
almost surely by the product of the conditional expectations of `X²` and `Y²`. -/
theorem condExp_mul_sq_ae_le_condExp_sq_mul_condExp_sq {ℱ : MeasurableSpace Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    P[X * Y | ℱ] ^ 2 ≤ᵐ[P] P[X ^ 2 | ℱ] * P[Y ^ 2 | ℱ] := by
  by_cases hℱ : ℱ ≤ mΩ
  · let A : Ω → ℝ := P[X ^ 2 | ℱ]
    let B : Ω → ℝ := P[X * Y | ℱ]
    let C : Ω → ℝ := P[Y ^ 2 | ℱ]
    have hXY_int : Integrable (X * Y) P := memLp_one_iff_integrable.1 <| hY.mul hX
    have hquad_rat (q : ℚ) : 0 ≤ᵐ[P] (q : ℝ) ^ 2 • C + (2 * (q : ℝ)) • B + A := by
      have hnonneg : 0 ≤ᵐ[P] P[(X + (q : ℝ) • Y) ^ 2 | ℱ] :=
        condExp_nonneg <| .of_forall fun _ ↦ sq_nonneg _
      refine hnonneg.trans_eq ?_
      calc
        P[(X + (q : ℝ) • Y) ^ 2 | ℱ]
            =ᵐ[P] P[X ^ 2 + (2 * (q : ℝ)) • (X * Y) + (q : ℝ) ^ 2 • (Y ^ 2) | ℱ] := by
              refine condExp_congr_ae <| .of_forall fun ω ↦ ?_
              change (X ω + (q : ℝ) * Y ω) ^ 2 =
                X ω ^ 2 + (2 * (q : ℝ)) * (X ω * Y ω) + (q : ℝ) ^ 2 * Y ω ^ 2
              ring
        _ =ᵐ[P] P[X ^ 2 | ℱ] + P[(2 * (q : ℝ)) • (X * Y) + (q : ℝ) ^ 2 • (Y ^ 2) | ℱ] := by
              simpa [A, add_assoc] using
                condExp_add hX.integrable_sq
                  ((hXY_int.const_mul _).add (hY.integrable_sq.const_mul _)) ℱ
        _ =ᵐ[P] P[X ^ 2 | ℱ] + (P[(2 * (q : ℝ)) • (X * Y) | ℱ] + P[(q : ℝ) ^ 2 • (Y ^ 2) | ℱ]) := by
              filter_upwards [condExp_add (hXY_int.const_mul _) (hY.integrable_sq.const_mul _) ℱ]
                with ω hω
              simpa using hω
        _ =ᵐ[P] A + ((2 * (q : ℝ)) • B + (q : ℝ) ^ 2 • C) := by
              filter_upwards [condExp_smul (2 * (q : ℝ)) (X * Y) ℱ,
                condExp_smul ((q : ℝ) ^ 2) (Y ^ 2) ℱ] with ω hω₁ hω₂
              simp [A, B, C, hω₁, hω₂]
        _ =ᵐ[P] (q : ℝ) ^ 2 • C + (2 * (q : ℝ)) • B + A := by
              refine .of_forall fun ω ↦ ?_
              simp [add_left_comm, add_comm]
    have hquad : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ ((q : ℝ) ^ 2 • C + (2 * (q : ℝ)) • B + A) ω :=
      ae_all_iff.2 hquad_rat
    filter_upwards [hquad] with ω hω
    have hreal : ∀ t : ℝ, 0 ≤ C ω * (t * t) + (2 * B ω) * t + A ω := by
      intro t
      refine Rat.denseRange_cast.induction_on t ?_ fun q ↦ ?_
      · have hcont : Continuous fun x : ℝ ↦ C ω * (x * x) + (2 * B ω) * x + A ω := by
          continuity
        exact isClosed_le continuous_const hcont
      · simpa [Pi.smul_apply, pow_two, mul_assoc, mul_left_comm, mul_comm] using hω q
    have hdisc : discrim (C ω) (2 * B ω) (A ω) ≤ 0 := discrim_le_zero hreal
    rw [discrim, sq] at hdisc
    have hpoint : B ω ^ 2 ≤ A ω * C ω := by
      nlinarith
    simpa [A, B, C, mul_comm] using hpoint
  · exact Filter.Eventually.of_forall fun _ ↦ by
      simp [condExp_of_not_le hℱ]

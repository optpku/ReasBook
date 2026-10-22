/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- Helper for Exercise 17.5.2: the modified Bessel function `I₀`, introduced through its
standard power series. -/
def modifiedBesselI0 (t : ℝ) : ℝ :=
  ∑' k, (t / 2) ^ (2 * k) / ((Nat.factorial k : ℝ) ^ (2 : ℕ))

scoped[ProbabilityTheory] notation "I₀" => modifiedBesselI0

/-- Helper for Exercise 17.5.2: the defining power-series expansion of `I₀`. -/
theorem modifiedBesselI0_eq_tsum (t : ℝ) :
    I₀ t =
      ∑' k, (t / 2) ^ (2 * k) / ((Nat.factorial k : ℝ) ^ (2 : ℕ)) := rfl

/- Exercise 17.5.2 is `source-facing`: it records the asymptotic of the first-coordinate return
probability for the continuous-time Poissonized simple random walk on `ℤ^D`.

Domain-style sampling for this item:
- `poissonConvolutionSemigroup` from Example 17.7 shows the chapter's continuous-time owner style:
  a source-facing time-indexed law family, with event probabilities derived from that owner.
- `modifiedBesselI0` from Exercise 17.5.5, used here through the pointwise notation `I₀`, is the
  source-facing owner declaration for the special-function side of the formula.

Primitive data versus derived API:
- the primitive data here is the one-dimensional law of the first coordinate at time `t`,
  realized canonically as the difference of two independent Poisson variables of rate `t / (2D)`;
- the zero-return probability `P₀[Y_t¹ = 0]` is derived from that law;
- the Bessel expression is a bridge theorem identifying the source-facing probability with the
  canonical special-function formula, not a second owner declaration. -/

private def poissonizedSimpleRandomWalkFirstCoordinatePMF
    (D : ℕ) [NeZero D] (t : ℝ≥0) : PMF ℤ :=
  (poissonPMF (t / (2 * (D : ℝ≥0)))).bind fun n ↦
    (poissonPMF (t / (2 * (D : ℝ≥0)))).map fun m : ℕ ↦ (n : ℤ) - m

/-- The law of the first coordinate `Y_t¹` of the continuous-time Poissonized simple random walk on
`ℤ^D` started at `0`, represented as the difference of two independent Poisson variables of rate
`t / (2D)`. -/
def poissonizedSimpleRandomWalkFirstCoordinateLaw
    (D : ℕ) [NeZero D] (t : ℝ≥0) : ProbabilityMeasure ℤ :=
  ⟨(poissonizedSimpleRandomWalkFirstCoordinatePMF D t).toMeasure, inferInstance⟩

/-- The source-facing return probability `P₀[Y_t¹ = 0]` for the first coordinate of the
continuous-time Poissonized simple random walk on `ℤ^D`. -/
def poissonizedSimpleRandomWalkFirstCoordinateZeroProbability
    (D : ℕ) [NeZero D] (t : ℝ≥0) : ℝ :=
  (poissonizedSimpleRandomWalkFirstCoordinateLaw D t : Measure ℤ).real ({0} : Set ℤ)

/-- Helper for Exercise 17.5.2: the zero event for `(n : ℤ) - m` is exactly the diagonal
condition `m = n`. -/
private lemma zero_eq_natCastSub_iff {m n : ℕ} :
    (0 : ℤ) = (n : ℤ) - m ↔ m = n := by
  constructor
  · intro h
    have hsub : (n : ℤ) - m = 0 := by simpa using h.symm
    have hcast : (n : ℤ) = m := sub_eq_zero.mp hsub
    exact (Int.ofNat.inj hcast).symm
  · intro h
    subst h
    simp

/-- Helper for Exercise 17.5.2: after mapping a Poisson law by `m ↦ (n : ℤ) - m`, the mass at
`0` comes only from the diagonal term `m = n`. -/
private lemma poissonDifferenceMap_zero_apply (lam : ℝ≥0) (n : ℕ) :
    (poissonPMF lam).map (fun m : ℕ ↦ (n : ℤ) - m) 0 = poissonPMF lam n := by
  -- Proof comment: `PMF.map_apply` rewrites the pushed-forward mass as a sum over the fiber of `0`.
  rw [PMF.map_apply]
  -- Proof comment: `0 = (n : ℤ) - m` forces `m = n`, so the fiber is the singleton `{n}`.
  refine (tsum_eq_single n ?_).trans ?_
  · intro m hm
    by_cases hzero : 0 = (n : ℤ) - m
    · exact (hm (zero_eq_natCastSub_iff.mp hzero)).elim
    · simp [hzero]
  · simp

/-- Helper for Exercise 17.5.2: the zero mass of the difference of two independent Poisson laws
is the diagonal Poisson square series. -/
private lemma poissonDifferenceZeroMass_eq_series (lam : ℝ≥0) :
    ((((poissonPMF lam).bind fun n ↦ (poissonPMF lam).map fun m : ℕ ↦ (n : ℤ) - m) 0).toReal) =
      ∑' n : ℕ, poissonPMFReal lam n * poissonPMFReal lam n := by
  -- Proof comment: expand the outer `bind` at `0` and rewrite each inner mass by the diagonal map
  -- identity from `poissonDifferenceMap_zero_apply`.
  rw [PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun n => ?_
    rw [poissonDifferenceMap_zero_apply, ENNReal.toReal_mul]
    have hMass : ((poissonPMF lam) n).toReal = poissonPMFReal lam n := by
      rw [← poissonPMFReal_ofReal_eq_poissonPMF, ENNReal.toReal_ofReal poissonPMFReal_nonneg]
    simp [hMass]
  · intro n
    exact ENNReal.mul_ne_top ((poissonPMF lam).apply_ne_top n)
      (((poissonPMF lam).map fun m : ℕ ↦ (n : ℤ) - m).apply_ne_top 0)

/-- Helper for Exercise 17.5.2: the diagonal square series of a Poisson law is exactly the
modified-Bessel expression with argument `2 * λ`. -/
private lemma poissonSquareSeries_eq_exp_mul_modifiedBesselI0 (lam : ℝ≥0) :
    (∑' n : ℕ, poissonPMFReal lam n * poissonPMFReal lam n) =
      Real.exp (-((2 : ℝ) * lam)) * I₀ ((2 : ℝ) * lam) := by
  -- Proof comment: unfold `I₀`, pull out the common exponential factor, and then compare the
  -- coefficients termwise with the square of the Poisson mass.
  rw [modifiedBesselI0_eq_tsum]
  have hExp : Real.exp (-↑lam) * Real.exp (-↑lam) = Real.exp (-((2 : ℝ) * lam)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hHalf : (((2 : ℝ) * lam : ℝ) / 2) = (lam : ℝ) := by ring
  calc
    ∑' n : ℕ, poissonPMFReal lam n * poissonPMFReal lam n
      = ∑' n : ℕ,
          Real.exp (-((2 : ℝ) * lam)) *
            (((((2 : ℝ) * lam : ℝ) / 2) ^ (2 * n)) / ((Nat.factorial n : ℝ) ^ (2 : ℕ))) := by
              refine tsum_congr fun n => ?_
              unfold poissonPMFReal
              rw [hHalf, ← hExp]
              ring_nf
    _ = Real.exp (-((2 : ℝ) * lam)) *
          ∑' n : ℕ,
            ((((2 : ℝ) * lam : ℝ) / 2) ^ (2 * n)) / ((Nat.factorial n : ℝ) ^ (2 : ℕ)) := by
              rw [← tsum_mul_left]

-- Proof sketch: write `Y_t¹` as the difference of two independent Poisson processes of rate
-- `(2D)⁻¹ t`, expand the mass at `0` by conditioning on the common value of the two Poisson
-- counts, and recognize the resulting power series as `I₀(t / D)`.
/-- The first-coordinate return probability is the modified-Bessel expression from `(17.21)`. -/
theorem poissonizedSimpleRandomWalkFirstCoordinateZeroProbability_eq_bessel
    (D : ℕ) [NeZero D] (t : ℝ≥0) :
    poissonizedSimpleRandomWalkFirstCoordinateZeroProbability D t =
      Real.exp (-((t : ℝ) / D)) * I₀ ((t : ℝ) / D) := by
  -- Proof comment: identify the singleton return mass with the diagonal Poisson square series and
  -- then recognize that series as the modified-Bessel power series at argument `t / D`.
  have hZeroMass :
      poissonizedSimpleRandomWalkFirstCoordinateZeroProbability D t =
        (((poissonizedSimpleRandomWalkFirstCoordinatePMF D t) 0).toReal) := by
    rw [poissonizedSimpleRandomWalkFirstCoordinateZeroProbability,
      poissonizedSimpleRandomWalkFirstCoordinateLaw, Measure.real_def]
    simpa using congrArg ENNReal.toReal
      (PMF.toMeasure_apply_singleton (poissonizedSimpleRandomWalkFirstCoordinatePMF D t) 0
        (measurableSet_singleton 0))
  rw [hZeroMass]
  let lam : ℝ≥0 := t / (2 * (D : ℝ≥0))
  have hSeries := poissonDifferenceZeroMass_eq_series (lam := lam)
  have hBessel := poissonSquareSeries_eq_exp_mul_modifiedBesselI0 (lam := lam)
  have hTwoLam : ((2 : ℝ) * lam : ℝ) = (t : ℝ) / D := by
    have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne D)
    change 2 * ((t : ℝ) / (2 * D)) = (t : ℝ) / D
    field_simp [hD]
  calc
    ((((poissonPMF lam).bind fun n ↦ (poissonPMF lam).map fun m : ℕ ↦ (n : ℤ) - m) 0).toReal)
      = ∑' n : ℕ, poissonPMFReal lam n * poissonPMFReal lam n := hSeries
    _ = Real.exp (-((2 : ℝ) * lam)) * I₀ ((2 : ℝ) * lam) := hBessel
    _ = Real.exp (-((t : ℝ) / D)) * I₀ ((t : ℝ) / D) := by rw [hTwoLam]

/-- Helper for Exercise 17.5.2: the normalized central-binomial term has the exact Wallis-product
representation used to read off its limit. -/
private lemma centralBinomialReturnProbability_sq_eq_wallis (n : ℕ) :
    (((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ^ 2) =
      1 / ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n) : ℝ) := by
  -- Proof comment: rewrite the central binomial coefficient through factorials and then compare
  -- the resulting expression with the closed factorial formula for `Real.Wallis.W n`.
  have hChoose :
      (Nat.choose (2 * n) n : ℝ) =
        (Nat.factorial (2 * n) : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) := by
    have hFact : ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by
      positivity
    apply (eq_div_iff hFact).2
    have hChooseNat :
        ((n + n).choose n : ℝ) * (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) =
          (Nat.factorial (n + n) : ℝ) := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n n
    ring_nf at hChooseNat ⊢
    simpa [two_mul] using hChooseNat
  have hPow :
      ((4 : ℝ) ^ n) ^ (2 : ℕ) = (2 : ℝ) ^ (4 * n) := by
    calc
      ((4 : ℝ) ^ n) ^ (2 : ℕ) = (4 : ℝ) ^ (n * 2) := by rw [pow_mul]
      _ = (4 : ℝ) ^ (2 * n) := by congr 1; ring
      _ = ((4 : ℝ) ^ (2 : ℕ)) ^ n := by rw [pow_mul]
      _ = (2 : ℝ) ^ (4 * n) := by norm_num [pow_mul]
  rw [pow_two, hChoose, Real.Wallis.W_eq_factorial_ratio]
  -- Proof comment: all remaining factors are explicit nonzero real numbers, so `field_simp`
  -- reduces the identity to a polynomial normalization.
  field_simp
  rw [← hPow]
  have hNat : (((2 * n + 1 : ℕ) : ℝ)) = 2 * (n : ℝ) + 1 := by
    norm_num
  rw [hNat]
  simp [mul_comm]

/-- Helper for Exercise 17.5.2: the normalized central-binomial coefficients converge to the
one-dimensional local-limit constant `1 / √π`. -/
private lemma centralBinomialReturnProbability_tendsto :
    Tendsto
      (fun n : ℕ ↦
        (n : ℝ) ^ ((1 : ℝ) / 2) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n))
      atTop
      (nhds (1 / Real.sqrt Real.pi)) := by
  -- Proof comment: first identify the square of the normalized term with the Wallis-product
  -- expression `n / ((2n + 1) W_n)`, whose limit is `1 / π`.
  let a : ℕ → ℝ := fun n ↦
    (n : ℝ) ^ ((1 : ℝ) / 2) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
  have hsqEq :
      ∀ n : ℕ, (a n) ^ (2 : ℕ) = (n : ℝ) / ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)) := by
    intro n
    dsimp [a]
    rw [mul_pow]
    rw [show (((n : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ)) = (n : ℝ) by
      rw [← Real.sqrt_eq_rpow]
      simp [Real.sq_sqrt (Nat.cast_nonneg n)]]
    rw [centralBinomialReturnProbability_sq_eq_wallis]
    ring
  have hsqWallis :
      Tendsto
        (fun n : ℕ ↦ (n : ℝ) / ((((2 * n + 1 : ℕ) : ℝ) * Real.Wallis.W n)))
        atTop
        (nhds (1 / Real.pi)) := by
    have hWallisInv :
        Tendsto (fun n : ℕ ↦ (Real.Wallis.W n)⁻¹) atTop (nhds ((Real.pi / 2)⁻¹)) := by
      exact Real.Wallis.tendsto_W_nhds_pi_div_two.inv₀ (by positivity)
    have hRatio :
        Tendsto (fun n : ℕ ↦ (n : ℝ) / (2 * (n : ℝ) + 1)) atTop (nhds (1 / 2)) := by
      simpa using Stirling.tendsto_self_div_two_mul_self_add_one
    convert hRatio.mul hWallisInv using 1
    · ext n
      field_simp [ne_of_gt (Real.Wallis.W_pos n)]
      congr 1
      simpa [mul_comm]
    · field_simp [Real.pi_ne_zero]
  have hsq :
      Tendsto (fun n : ℕ ↦ (a n) ^ (2 : ℕ)) atTop (nhds (1 / Real.pi)) := by
    simpa [hsqEq] using hsqWallis
  have hnonneg : ∀ n : ℕ, 0 ≤ a n := by
    intro n
    dsimp [a]
    refine mul_nonneg ?_ ?_
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · refine div_nonneg ?_ ?_
      · positivity
      · positivity
  -- Proof comment: since every term is nonnegative, the original sequence is the square root of
  -- its squared sequence, so continuity of `Real.sqrt` transfers the limit.
  have hsqrt :
      Tendsto (fun n : ℕ ↦ Real.sqrt ((a n) ^ (2 : ℕ))) atTop (nhds (Real.sqrt (1 / Real.pi))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hsqrtEq : (fun n : ℕ ↦ Real.sqrt ((a n) ^ (2 : ℕ))) = a := by
    funext n
    rw [show (a n) ^ (2 : ℕ) = (a n) ^ 2 by norm_num]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hnonneg n)]
  have hsqrtPi : Real.sqrt (1 / Real.pi) = 1 / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (by positivity)]
    simp
  rw [hsqrtEq] at hsqrt
  simpa [a, hsqrtPi] using hsqrt

/-- Helper for Exercise 17.5.2: Poisson masses satisfy the standard first-moment shift identity.
-/
private lemma poissonPMFReal_succ_mul (μ : ℝ≥0) (n : ℕ) :
    poissonPMFReal μ (n + 1) * (n + 1 : ℝ) = (μ : ℝ) * poissonPMFReal μ n := by
  -- Proof comment: rewrite the `(n + 1)`-st Poisson mass by separating one power of `μ`
  -- and one factorial factor.
  rw [poissonPMFReal, poissonPMFReal, pow_succ, Nat.factorial_succ]
  have hfac : ((n.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hfac]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

/-- Helper for Exercise 17.5.2: the two-step Poisson shift gives the factorial second-moment
identity at the level of coefficients. -/
private lemma poissonPMFReal_twoStep_mul (μ : ℝ≥0) (n : ℕ) :
    poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ)) =
      (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n := by
  -- Proof comment: apply the one-step identity twice and regroup the scalar factors.
  have htmp := poissonPMFReal_succ_mul μ (n + 1)
  have hsucc :
      poissonPMFReal μ (n + 2) * (n + 2 : ℝ) = (μ : ℝ) * poissonPMFReal μ (n + 1) := by
    norm_num [Nat.succ_eq_add_one, add_assoc] at htmp ⊢
    exact htmp
  calc
    poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ))
      = (poissonPMFReal μ (n + 2) * (n + 2 : ℝ)) * (n + 1 : ℝ) := by ring
    _ = ((μ : ℝ) * poissonPMFReal μ (n + 1)) * (n + 1 : ℝ) := by rw [hsucc]
    _ = (μ : ℝ) * (poissonPMFReal μ (n + 1) * (n + 1 : ℝ)) := by ring
    _ = (μ : ℝ) * ((μ : ℝ) * poissonPMFReal μ n) := by
          rw [poissonPMFReal_succ_mul μ n]
    _ = (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n := by ring

/-- Helper for Exercise 17.5.2: the Poisson first-moment series is summable after shifting it to
the mass series with the one-step recursion. -/
private lemma summablePoissonFirstMoment (μ : ℝ≥0) :
    Summable (fun n : ℕ ↦ poissonPMFReal μ n * (n : ℝ)) := by
  -- Proof comment: the shifted first-moment series agrees termwise with `(μ : ℝ)` times the
  -- summable Poisson mass series.
  have hshift :
      Summable (fun n : ℕ ↦ poissonPMFReal μ (n + 1) * ((n + 1 : ℕ) : ℝ)) := by
    have hbase : Summable (fun n : ℕ ↦ (μ : ℝ) * poissonPMFReal μ n) :=
      (poissonPMFRealSum μ).summable.mul_left (μ : ℝ)
    refine hbase.congr ?_
    intro n
    simpa using (poissonPMFReal_succ_mul μ n).symm
  exact (summable_nat_add_iff 1).mp <| by
    simpa [Nat.succ_eq_add_one] using hshift

/-- Helper for Exercise 17.5.2: the two-step Poisson recursion directly identifies the shifted
factorial second-moment series with `μ²` times the Poisson mass series. -/
private lemma hasSumPoissonShiftedFactorialSecondMoment (μ : ℝ≥0) :
    HasSum
      (fun n : ℕ ↦ poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ)))
      ((μ : ℝ) ^ (2 : ℕ)) := by
  -- Proof comment: the shifted series is exactly `μ²` times the mass series termwise.
  have hbase :
      HasSum (fun n : ℕ ↦ (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n) ((μ : ℝ) ^ (2 : ℕ)) := by
    simpa using (poissonPMFRealSum μ).mul_left ((μ : ℝ) ^ (2 : ℕ))
  simpa [poissonPMFReal_twoStep_mul, Nat.succ_eq_add_one, add_assoc] using hbase

/-- Helper for Exercise 17.5.2: the factorial second-moment series is summable after shifting by
two indices and using the stable shifted `HasSum` normal form. -/
private lemma summablePoissonFactorialSecondMoment (μ : ℝ≥0) :
    Summable (fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) := by
  -- Proof comment: the shifted tail is summable because it already has a `HasSum`; shifting back
  -- by two indices recovers the original factorial-moment series.
  have hshifted :
      Summable (fun n : ℕ ↦ poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ))) :=
    (hasSumPoissonShiftedFactorialSecondMoment μ).summable
  have htail :
      Summable
        (fun n : ℕ ↦
          poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))) := by
    refine hshifted.congr ?_
    intro n
    have hrewrite :
        (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) = (n + 2 : ℝ) * (n + 1 : ℝ) := by
      have hcast2 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by
        norm_num [Nat.cast_add]
      rw [hcast2]
      ring
    rw [hrewrite]
  exact (_root_.summable_nat_add_iff
      (f := fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) 2).mp <| by
    simpa [Nat.succ_eq_add_one, add_assoc] using htail

/-- Helper for Exercise 17.5.2: the Poisson first moment equals the rate parameter. -/
private lemma poissonFirstMoment_eq (μ : ℝ≥0) :
    ∑' n : ℕ, poissonPMFReal μ n * (n : ℝ) = (μ : ℝ) := by
  -- Proof comment: peel off the zero term and rewrite the remaining tail by the one-step
  -- coefficient identity.
  have hs : Summable (fun n : ℕ ↦ poissonPMFReal μ n * (n : ℝ)) :=
    summablePoissonFirstMoment μ
  rw [← hs.sum_add_tsum_nat_add 1]
  simp
  calc
    ∑' n : ℕ, poissonPMFReal μ (n + 1) * ((n : ℝ) + 1)
      = ∑' n : ℕ, (μ : ℝ) * poissonPMFReal μ n := by
          refine tsum_congr fun n ↦ ?_
          simpa using poissonPMFReal_succ_mul μ n
    _ = (μ : ℝ) * ∑' n : ℕ, poissonPMFReal μ n := by
          rw [tsum_mul_left]
    _ = (μ : ℝ) := by
          rw [(poissonPMFRealSum μ).tsum_eq]
          ring

/-- Helper for Exercise 17.5.2: the Poisson factorial second moment equals `μ²`. -/
private lemma poissonFactorialSecondMoment_eq (μ : ℝ≥0) :
    ∑' n : ℕ, poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1)) = (μ : ℝ) ^ (2 : ℕ) := by
  -- Proof comment: the first two terms vanish, and the remaining tail is exactly the shifted
  -- `HasSum` from `hasSumPoissonShiftedFactorialSecondMoment`.
  have hs : Summable (fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) :=
    summablePoissonFactorialSecondMoment μ
  have htail :
      ∑' n : ℕ, poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) =
        (μ : ℝ) ^ (2 : ℕ) := by
    calc
      ∑' n : ℕ, poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))
        = ∑' n : ℕ, poissonPMFReal μ (n + 2) * ((n + 2 : ℝ) * (n + 1 : ℝ)) := by
            refine tsum_congr fun n ↦ ?_
            have hrewrite :
                (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) = (n + 2 : ℝ) * (n + 1 : ℝ) := by
              have hcast2 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by
                norm_num [Nat.cast_add]
              rw [hcast2]
              ring
            rw [hrewrite]
      _ = (μ : ℝ) ^ (2 : ℕ) := (hasSumPoissonShiftedFactorialSecondMoment μ).tsum_eq
  calc
    ∑' n : ℕ, poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))
      = (∑ i ∈ Finset.range 2, poissonPMFReal μ i * ((i : ℝ) * ((i : ℝ) - 1))) +
          ∑' n : ℕ, poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) := by
            simpa using (hs.sum_add_tsum_nat_add 2).symm
    _ = ∑' n : ℕ, poissonPMFReal μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) := by
          norm_num [Finset.sum_range_succ, Nat.cast_add]
    _ = (μ : ℝ) ^ (2 : ℕ) := htail

/-- Helper for Exercise 17.5.2: the centered Poisson square series is summable. -/
private lemma summablePoissonCenteredSecondMoment (μ : ℝ≥0) :
    Summable (fun n : ℕ ↦ (((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n) := by
  -- Proof comment: rewrite the centered square into factorial-second-moment, first-moment, and
  -- mass pieces, then sum those three already-controlled series.
  have hFactorial :
      Summable (fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) :=
    summablePoissonFactorialSecondMoment μ
  have hFirst :
      Summable (fun n : ℕ ↦ ((1 : ℝ) - 2 * (μ : ℝ)) * (poissonPMFReal μ n * (n : ℝ))) :=
    (summablePoissonFirstMoment μ).mul_left ((1 : ℝ) - 2 * (μ : ℝ))
  have hMass :
      Summable (fun n : ℕ ↦ (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n) :=
    (poissonPMFRealSum μ).summable.mul_left ((μ : ℝ) ^ (2 : ℕ))
  refine (hFactorial.add (hFirst.add hMass)).congr ?_
  intro n
  ring

/-- Helper for Exercise 17.5.2: the centered second moment of a Poisson law equals its rate. -/
private lemma poissonCenteredSecondMoment_eq (μ : ℝ≥0) :
    ∑' n : ℕ, (((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n = (μ : ℝ) := by
  -- Proof comment: after the additive decomposition of the centered square, each infinite sum is
  -- one of the three Poisson moment identities already proved.
  have hFactorial :
      Summable (fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))) :=
    summablePoissonFactorialSecondMoment μ
  have hFirst :
      Summable (fun n : ℕ ↦ ((1 : ℝ) - 2 * (μ : ℝ)) * (poissonPMFReal μ n * (n : ℝ))) :=
    (summablePoissonFirstMoment μ).mul_left ((1 : ℝ) - 2 * (μ : ℝ))
  have hMass :
      Summable (fun n : ℕ ↦ (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n) :=
    (poissonPMFRealSum μ).summable.mul_left ((μ : ℝ) ^ (2 : ℕ))
  let a : ℕ → ℝ := fun n : ℕ ↦ poissonPMFReal μ n * ((n : ℝ) * ((n : ℝ) - 1))
  let b : ℕ → ℝ := fun n : ℕ ↦ ((1 : ℝ) - 2 * (μ : ℝ)) * (poissonPMFReal μ n * (n : ℝ))
  let c : ℕ → ℝ := fun n : ℕ ↦ (μ : ℝ) ^ (2 : ℕ) * poissonPMFReal μ n
  calc
    ∑' n : ℕ, (((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n
      = ∑' n : ℕ, (a n + (b n + c n)) := by
              refine tsum_congr fun n ↦ ?_
              dsimp [a, b, c]
              ring
    _ = (∑' n : ℕ, a n) + ∑' n : ℕ, (b n + c n) := by
              exact hFactorial.tsum_add (hFirst.add hMass)
    _ = (∑' n : ℕ, a n) + ((∑' n : ℕ, b n) + ∑' n : ℕ, c n) := by
              rw [hFirst.tsum_add hMass]
    _ = (μ : ℝ) := by
          dsimp [a, b, c]
          rw [poissonFactorialSecondMoment_eq, tsum_mul_left, poissonFirstMoment_eq, tsum_mul_left,
            (poissonPMFRealSum μ).tsum_eq]
          ring

/-- Helper for Exercise 17.5.2: the Poisson relative-window tail is controlled by the centered
second moment via a direct Chebyshev-type comparison of series terms. -/
private lemma poissonRelativeWindowTail_le (δ : ℝ) (μ : ℝ≥0)
    (hδ : 0 < δ) (hμ : 0 < (μ : ℝ)) :
    ∑' n : ℕ, (if δ * (μ : ℝ) ≤ |(n : ℝ) - μ| then poissonPMFReal μ n else 0) ≤
      1 / (δ ^ (2 : ℕ) * (μ : ℝ)) := by
  -- Proof comment: compare the indicator tail termwise with the centered-square series divided by
  -- `δ² μ²`, then evaluate that dominating series with the centered-moment identity.
  let tail : ℕ → ℝ := fun n : ℕ ↦
    if δ * (μ : ℝ) ≤ |(n : ℝ) - μ| then poissonPMFReal μ n else 0
  let bound : ℕ → ℝ := fun n : ℕ ↦
    ((((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n) / (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ))
  have hden : 0 < δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ) := by
    positivity
  have hTailNonneg : ∀ n : ℕ, 0 ≤ tail n := by
    intro n
    by_cases h : δ * (μ : ℝ) ≤ |(n : ℝ) - μ|
    · simp [tail, h, poissonPMFReal_nonneg]
    · simp [tail, h]
  have hTailLeMass : ∀ n : ℕ, tail n ≤ poissonPMFReal μ n := by
    intro n
    by_cases h : δ * (μ : ℝ) ≤ |(n : ℝ) - μ|
    · simp [tail, h]
    · simp [tail, h, poissonPMFReal_nonneg]
  have hTailSummable : Summable tail :=
    Summable.of_nonneg_of_le hTailNonneg hTailLeMass (poissonPMFRealSum μ).summable
  have hBoundSummable : Summable bound := by
    simpa [bound] using
      (summablePoissonCenteredSecondMoment μ).div_const (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ))
  have hTailLeBound : ∀ n : ℕ, tail n ≤ bound n := by
    intro n
    by_cases h : δ * (μ : ℝ) ≤ |(n : ℝ) - μ|
    · have habs : |δ * (μ : ℝ)| ≤ |(n : ℝ) - μ| := by
        have hleft : |δ * (μ : ℝ)| = δ * (μ : ℝ) := by
          rw [abs_of_nonneg]
          positivity
        rw [hleft]
        exact h
      have hsq' : (δ * (μ : ℝ)) ^ (2 : ℕ) ≤ ((n : ℝ) - μ) ^ (2 : ℕ) := by
        exact (sq_le_sq).2 habs
      have hsq :
          δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ) ≤ ((n : ℝ) - μ) ^ (2 : ℕ) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq'
      have hscale : 1 ≤ (((n : ℝ) - μ) ^ (2 : ℕ)) / (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ)) := by
        rw [one_le_div hden]
        exact hsq
      have hMassNonneg : 0 ≤ poissonPMFReal μ n := poissonPMFReal_nonneg
      simp [tail, bound, h]
      calc
        poissonPMFReal μ n
          = 1 * poissonPMFReal μ n := by ring
        _ ≤ ((((n : ℝ) - μ) ^ (2 : ℕ)) / (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ))) *
            poissonPMFReal μ n := by
              exact mul_le_mul_of_nonneg_right hscale hMassNonneg
        _ = ((((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n) /
              (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ)) := by
              rw [div_eq_mul_inv]
              ring_nf
    · have hBoundNonneg : 0 ≤ bound n := by
        exact div_nonneg (mul_nonneg (sq_nonneg _) poissonPMFReal_nonneg) hden.le
      simpa [tail, h] using hBoundNonneg
  calc
    ∑' n : ℕ, (if δ * (μ : ℝ) ≤ |(n : ℝ) - μ| then poissonPMFReal μ n else 0)
      = ∑' n : ℕ, tail n := by rfl
    _ ≤ ∑' n : ℕ, bound n := by
          exact Summable.tsum_le_tsum hTailLeBound hTailSummable hBoundSummable
    _ = (∑' n : ℕ, (((n : ℝ) - μ) ^ (2 : ℕ)) * poissonPMFReal μ n) /
          (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ)) := by
            rw [tsum_div_const]
    _ = (μ : ℝ) / (δ ^ (2 : ℕ) * (μ : ℝ) ^ (2 : ℕ)) := by
          rw [poissonCenteredSecondMoment_eq]
    _ = 1 / (δ ^ (2 : ℕ) * (μ : ℝ)) := by
          field_simp [pow_two, hδ.ne', hμ.ne']

/-- Helper for Exercise 17.5.2: squaring a Poisson mass at rate `λ` rewrites it as an even
Poisson mass at rate `2 λ` times the central-binomial factor. -/
private lemma poissonSquareTerm_eq_evenPoissonCentralBinomial
    (lam : ℝ≥0) (n : ℕ) :
    poissonPMFReal lam n * poissonPMFReal lam n =
      poissonPMFReal (2 * lam) (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
  -- Proof comment: separate the common exponential factor and then rewrite the remaining
  -- factorial ratio through the central binomial coefficient.
  have hExp : Real.exp (-↑lam) * Real.exp (-↑lam) = Real.exp (-((2 : ℝ) * lam)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hChoose' :
      (Nat.choose (2 * n) n : ℝ) =
        (Nat.factorial (2 * n) : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) := by
    have hFact : ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) ≠ 0 := by positivity
    apply (eq_div_iff hFact).2
    have hChooseNat :
        ((n + n).choose n : ℝ) * (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) =
          (Nat.factorial (n + n) : ℝ) := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n n
    ring_nf at hChooseNat ⊢
    simpa [two_mul] using hChooseNat
  have hPowMul :
      (((2 : ℝ) * lam : ℝ) ^ (2 * n)) = (4 : ℝ) ^ n * (lam : ℝ) ^ (2 * n) := by
    rw [mul_pow]
    have hTwoPow : (2 : ℝ) ^ (2 * n) = (4 : ℝ) ^ n := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, pow_mul]
    rw [hTwoPow]
  have hPowSplit :
      (lam : ℝ) ^ (2 * n) = (lam : ℝ) ^ n * (lam : ℝ) ^ n := by
    rw [← pow_add]
    congr 1
    ring
  have hPowMul' :
      ((↑(2 * lam) : ℝ) ^ (2 * n)) = (4 : ℝ) ^ n * (lam : ℝ) ^ (2 * n) := by
    simpa [NNReal.coe_mul] using hPowMul
  have hExp' : Real.exp (-↑(2 * lam)) = Real.exp (-↑lam) * Real.exp (-↑lam) := by
    simpa [NNReal.coe_mul] using hExp.symm
  unfold poissonPMFReal
  rw [hChoose', hPowMul', hPowSplit, hExp']
  field_simp

/-- Helper for Exercise 17.5.2: the first-coordinate return probability is an even-Poisson
average of the normalized central-binomial coefficients. -/
private lemma
    poissonizedSimpleRandomWalkFirstCoordinateZeroProbability_eq_evenPoissonCentralBinomialSeries
    (D : ℕ) [NeZero D] (t : ℝ≥0) :
    poissonizedSimpleRandomWalkFirstCoordinateZeroProbability D t =
      ∑' n : ℕ,
        poissonPMFReal (t / (D : ℝ≥0)) (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
  -- Proof comment: rewrite the return probability as the diagonal square series and then replace
  -- each squared Poisson coefficient by the even-rate central-binomial term.
  have hZeroMass :
      poissonizedSimpleRandomWalkFirstCoordinateZeroProbability D t =
        (((poissonizedSimpleRandomWalkFirstCoordinatePMF D t) 0).toReal) := by
    rw [poissonizedSimpleRandomWalkFirstCoordinateZeroProbability,
      poissonizedSimpleRandomWalkFirstCoordinateLaw, Measure.real_def]
    simpa using congrArg ENNReal.toReal
      (PMF.toMeasure_apply_singleton (poissonizedSimpleRandomWalkFirstCoordinatePMF D t) 0
        (measurableSet_singleton 0))
  rw [hZeroMass]
  let lam : ℝ≥0 := t / (2 * (D : ℝ≥0))
  have hSeries := poissonDifferenceZeroMass_eq_series (lam := lam)
  have hRate : 2 * lam = t / (D : ℝ≥0) := by
    apply NNReal.coe_injective
    have hD : (D : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne D)
    change 2 * ((t : ℝ) / (2 * D)) = (t : ℝ) / D
    field_simp [hD]
  calc
    ((((poissonPMF lam).bind fun n ↦ (poissonPMF lam).map fun m : ℕ ↦ (n : ℤ) - m) 0).toReal)
      = ∑' n : ℕ, poissonPMFReal lam n * poissonPMFReal lam n := hSeries
    _ = ∑' n : ℕ,
          poissonPMFReal (2 * lam) (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
            refine tsum_congr fun n => ?_
            exact poissonSquareTerm_eq_evenPoissonCentralBinomial lam n
    _ = ∑' n : ℕ,
          poissonPMFReal (t / (D : ℝ≥0)) (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
            simp [hRate]

/-- Helper for Exercise 17.5.2: the even Poisson mass at rate `μ` has the closed form
`exp (-μ) cosh μ`. -/
private lemma poissonEvenMass_eq_exp_mul_cosh (μ : ℝ≥0) :
    (∑' n : ℕ, poissonPMFReal μ (2 * n)) = Real.exp (-↑μ) * Real.cosh μ := by
  -- Proof comment: factor out the common exponential term and recognize the remaining even power
  -- series as the standard series of `cosh`.
  calc
    (∑' n : ℕ, poissonPMFReal μ (2 * n))
      = ∑' n : ℕ, Real.exp (-↑μ) * ((μ : ℝ) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) := by
          refine tsum_congr fun n => ?_
          rw [poissonPMFReal]
          ring
    _ = Real.exp (-↑μ) * ∑' n : ℕ, (μ : ℝ) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) := by
          rw [tsum_mul_left]
    _ = Real.exp (-↑μ) * Real.cosh μ := by
          rw [Real.cosh_eq_tsum]

/-- Helper for Exercise 17.5.2: the even Poisson mass converges to `1 / 2` as the rate tends to
infinity. -/
private lemma poissonEvenMass_tendsto_half :
    Tendsto (fun μ : ℝ≥0 ↦ ∑' n : ℕ, poissonPMFReal μ (2 * n)) atTop (nhds (1 / 2 : ℝ)) := by
  -- Proof comment: the exact formula `exp (-μ) * cosh μ` reduces the problem to the decay of the
  -- correction term `exp (-2μ)`.
  have hRewrite :
      (fun μ : ℝ≥0 ↦ ∑' n : ℕ, poissonPMFReal μ (2 * n)) =
        fun μ : ℝ≥0 ↦ (1 + Real.exp (-((2 : ℝ) * μ))) / 2 := by
    funext μ
    rw [poissonEvenMass_eq_exp_mul_cosh, Real.cosh_eq]
    have hExpCancel : Real.exp (-↑μ) * Real.exp ↑μ = 1 := by
      rw [← Real.exp_add]
      simp
    have hExpDouble : Real.exp (-↑μ) * Real.exp (-↑μ) = Real.exp (-((2 : ℝ) * μ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (-↑μ) * ((Real.exp ↑μ + Real.exp (-↑μ)) / 2)
        = (Real.exp (-↑μ) * Real.exp ↑μ + Real.exp (-↑μ) * Real.exp (-↑μ)) / 2 := by ring
      _ = (1 + Real.exp (-((2 : ℝ) * μ))) / 2 := by rw [hExpCancel, hExpDouble]
  rw [hRewrite]
  have hExp :
      Tendsto (fun μ : ℝ≥0 ↦ Real.exp (-((2 : ℝ) * μ))) atTop (nhds 0) := by
    have hMul : Tendsto (fun μ : ℝ≥0 ↦ (2 : ℝ) * μ) atTop atTop := by
      exact ((NNReal.tendsto_coe_atTop).2 tendsto_id).const_mul_atTop (by positivity)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hMul
  have hSum : Tendsto (fun μ : ℝ≥0 ↦ (1 : ℝ) + Real.exp (-((2 : ℝ) * μ))) atTop (nhds 1) := by
    simpa using (show Tendsto (fun μ : ℝ≥0 ↦ (1 : ℝ)) atTop (nhds (1 : ℝ)) from tendsto_const_nhds).add hExp
  convert hSum.const_mul (1 / 2 : ℝ) using 1
  · ext μ
    ring
  · ring

/-- Helper for Exercise 17.5.2: the normalized central-binomial factor is bounded by `1`. -/
private lemma centralBinomialReturnProbability_le_one (n : ℕ) :
    ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ≤ 1 := by
  -- Proof comment: `Nat.centralBinom_le_four_pow` is exactly the required numerator bound.
  have hnum : ((Nat.choose (2 * n) n : ℝ)) ≤ (4 : ℝ) ^ n := by
    exact_mod_cast Nat.centralBinom_le_four_pow n
  have hnum' : ((Nat.choose (2 * n) n : ℝ)) ≤ 1 * (4 : ℝ) ^ n := by
    simpa using hnum
  exact (div_le_iff₀ (by positivity)).2 hnum'

/-- Helper for Exercise 17.5.2: a relative window around `μ` forces `n` into the deterministic
interval `[(1 - δ) μ / 2, (1 + δ) μ / 2]`. -/
private lemma centralWindowIndexBounds {δ μ : ℝ} {n : ℕ}
    (_hδ : 0 < δ) (_hδ' : δ < 1) (_hμ : 0 < μ)
    (hwin : |(2 * n : ℝ) - μ| ≤ δ * μ) :
    ((1 - δ) * μ) / 2 ≤ n ∧ (n : ℝ) ≤ ((1 + δ) * μ) / 2 := by
  -- Proof comment: expand the absolute-value inequality into its two linear sides and solve.
  have hleft : -(δ * μ) ≤ (2 * n : ℝ) - μ := (abs_le.mp hwin).1
  have hright : (2 * n : ℝ) - μ ≤ δ * μ := (abs_le.mp hwin).2
  constructor <;> linarith

/-- Helper for Exercise 17.5.2: the even Poisson mass inside the relative window
`|(2 n) - μ| ≤ δ μ`. -/
private def evenCentralWindowMass (δ : ℝ) (μ : ℝ≥0) : ℝ :=
  ∑' n : ℕ, if |(2 * n : ℝ) - μ| ≤ δ * μ then poissonPMFReal μ (2 * n) else 0

/-- Helper for Exercise 17.5.2: the full Poisson mass outside the relative window
`|n - μ| < δ μ`. -/
private def poissonRelativeTailMass (δ : ℝ) (μ : ℝ≥0) : ℝ :=
  ∑' n : ℕ, if δ * μ ≤ |(n : ℝ) - μ| then poissonPMFReal μ n else 0

/-- Helper for Exercise 17.5.2: the full Poisson relative-window tail tends to `0`. -/
private lemma poissonRelativeTailMass_tendsto_zero (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (poissonRelativeTailMass δ) atTop (nhds 0) := by
  -- Proof comment: every tail mass is nonnegative, and for large `μ` the Chebyshev estimate
  -- bounds it by `1 / (δ² μ)`, which tends to `0`.
  have hNonneg : ∀ μ : ℝ≥0, 0 ≤ poissonRelativeTailMass δ μ := by
    intro μ
    unfold poissonRelativeTailMass
    exact tsum_nonneg fun n ↦ by
      split_ifs <;> simp [poissonPMFReal_nonneg]
  have hUpper :
      ∀ᶠ μ : ℝ≥0 in atTop, poissonRelativeTailMass δ μ ≤ 1 / (δ ^ (2 : ℕ) * (μ : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with μ hμ
    have hμ' : 0 < (μ : ℝ) := by exact_mod_cast hμ
    simpa [poissonRelativeTailMass] using poissonRelativeWindowTail_le δ μ hδ hμ'
  have hInv :
      Tendsto (fun μ : ℝ≥0 ↦ 1 / (δ ^ (2 : ℕ) * (μ : ℝ))) atTop (nhds 0) := by
    have hcoe : Tendsto (fun μ : ℝ≥0 ↦ (μ : ℝ)) atTop atTop :=
      (NNReal.tendsto_coe_atTop).2 tendsto_id
    have hinv : Tendsto (fun μ : ℝ≥0 ↦ ((μ : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hcoe
    have hconst :
        Tendsto
          (fun μ : ℝ≥0 ↦ (δ ^ (2 : ℕ))⁻¹ * ((μ : ℝ))⁻¹)
          atTop
          (nhds ((δ ^ (2 : ℕ))⁻¹ * 0)) :=
      tendsto_const_nhds.mul hinv
    convert hconst using 1
    · ext μ
      field_simp [hδ.ne']
    · simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hInv
    (Eventually.of_forall fun μ ↦ hNonneg μ) hUpper

/-- Helper for Exercise 17.5.2: once `μ` is large, every index in the relative window is above
any prescribed threshold. -/
private lemma centralWindowEventuallyLargeIndex (δ : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hδ' : δ < 1) :
    ∀ᶠ μ : ℝ≥0 in atTop, ∀ n : ℕ, |(2 * n : ℝ) - μ| ≤ δ * μ → N ≤ n := by
  let B : ℝ := max 1 (((2 : ℝ) * N) / (1 - δ))
  let Bnn : ℝ≥0 := ⟨B, by
    dsimp [B]
    positivity⟩
  filter_upwards [eventually_ge_atTop Bnn] with μ hμ n hwin
  have hOneSub : 0 < 1 - δ := by linarith
  have hμB : B ≤ (μ : ℝ) := by exact_mod_cast hμ
  have hμ' : 0 < (μ : ℝ) := by
    have hOne : (1 : ℝ) ≤ (μ : ℝ) := le_trans (le_max_left _ _) hμB
    linarith
  have hLarge : (((2 : ℝ) * N) / (1 - δ)) ≤ (μ : ℝ) := le_trans (le_max_right _ _) hμB
  have hIndexLower := (centralWindowIndexBounds hδ hδ' hμ' hwin).1
  have hNreal : (N : ℝ) ≤ (n : ℝ) := by
    have hScaled : (2 : ℝ) * N ≤ (1 - δ) * (μ : ℝ) := by
      have hTmp := hLarge
      field_simp [hOneSub.ne'] at hTmp
      linarith
    linarith
  exact_mod_cast hNreal

/-- Helper for Exercise 17.5.2: on the relative window, the ratio `sqrt μ / sqrt n` is trapped
between the deterministic endpoints coming from the window geometry. -/
private lemma centralWindowSqrtRatioBounds {δ : ℝ} {μ : ℝ≥0} {n : ℕ}
    (hδ : 0 < δ) (hδ' : δ < 1) (hμ : 0 < (μ : ℝ)) (hn : 0 < n)
    (hwin : |(2 * n : ℝ) - μ| ≤ δ * μ) :
    Real.sqrt (2 / (1 + δ)) ≤ Real.sqrt μ / Real.sqrt n ∧
      Real.sqrt μ / Real.sqrt n ≤ Real.sqrt (2 / (1 - δ)) := by
  -- Proof comment: the window inequality gives deterministic bounds on `n`, hence on `μ / n`;
  -- taking square roots transports those bounds to `sqrt μ / sqrt n`.
  have hBounds := centralWindowIndexBounds hδ hδ' hμ hwin
  have hUpperIndex : (n : ℝ) ≤ ((1 + δ) * (μ : ℝ)) / 2 := hBounds.2
  have hLowerIndex : ((1 - δ) * (μ : ℝ)) / 2 ≤ (n : ℝ) := hBounds.1
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hOneAdd : 0 < 1 + δ := by linarith
  have hOneSub : 0 < 1 - δ := by linarith
  have hLowerRatio : 2 / (1 + δ) ≤ (μ : ℝ) / n := by
    field_simp [hOneAdd.ne', hn'.ne']
    linarith
  have hUpperRatio : (μ : ℝ) / n ≤ 2 / (1 - δ) := by
    field_simp [hOneSub.ne', hn'.ne']
    linarith
  constructor
  · rw [← Real.sqrt_div (le_of_lt hμ) (n : ℝ)]
    exact Real.sqrt_le_sqrt hLowerRatio
  · rw [← Real.sqrt_div (le_of_lt hμ) (n : ℝ)]
    exact Real.sqrt_le_sqrt hUpperRatio

/-- Helper for Exercise 17.5.2: the one-dimensional central-binomial asymptotic can be converted
to a uniform two-sided threshold statement. -/
private lemma centralBinomialReturnProbability_eventuallyBounds (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N,
      1 / Real.sqrt Real.pi - η ≤
          Real.sqrt n * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ∧
        Real.sqrt n * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ≤
          1 / Real.sqrt Real.pi + η := by
  -- Proof comment: translate convergence to `1 / √π` into an eventual metric band of radius `η`.
  rcases Metric.tendsto_atTop.1 centralBinomialReturnProbability_tendsto η hη with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hDist := hN n hn
  have hsqrt : (n : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt n := by
    simpa using (Real.sqrt_eq_rpow (n : ℝ)).symm
  rw [hsqrt] at hDist
  rw [Real.dist_eq, abs_lt] at hDist
  constructor <;> linarith

/-- Helper for Exercise 17.5.2: the scaled central-binomial factor is uniformly trapped on every
fixed relative Poisson window once `μ` is large enough. -/
private lemma centralWindowScaledBounds (δ η : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1) (hη : 0 < η) :
    ∀ᶠ μ : ℝ≥0 in atTop, ∀ n : ℕ, |(2 * n : ℝ) - μ| ≤ δ * μ →
      Real.sqrt (2 / (1 + δ)) * (1 / Real.sqrt Real.pi - η) ≤
          Real.sqrt μ * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ∧
        Real.sqrt μ * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) ≤
          Real.sqrt (2 / (1 - δ)) * (1 / Real.sqrt Real.pi + η) := by
  -- Proof comment: extract a threshold in `n` from the central-binomial limit, then use the
  -- window geometry to guarantee every window index lies beyond that threshold.
  rcases centralBinomialReturnProbability_eventuallyBounds η hη with ⟨N, hN⟩
  have hLargeIndex := centralWindowEventuallyLargeIndex δ (max N 1) hδ hδ'
  filter_upwards [hLargeIndex, eventually_ge_atTop (1 : ℝ≥0)] with μ hμ hμge n hwin
  let c : ℝ := (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n
  have hnGe : max N 1 ≤ n := hμ n hwin
  have hn : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 1) (le_trans (Nat.le_max_right _ _) hnGe)
  have hCore := hN n (le_trans (Nat.le_max_left _ _) hnGe)
  have hμpos : 0 < (μ : ℝ) := by
    have hμge' : (1 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμge
    linarith
  have hRatio := centralWindowSqrtRatioBounds hδ hδ' hμpos hn hwin
  rcases hCore with ⟨hCoreLower, hCoreUpper⟩
  rcases hRatio with ⟨hRatioLower, hRatioUpper⟩
  have hCNonneg : 0 ≤ c := by
    refine div_nonneg ?_ ?_
    · positivity
    · positivity
  have hCoreNonneg : 0 ≤ Real.sqrt n * c := mul_nonneg (Real.sqrt_nonneg _) hCNonneg
  have hRatioNonneg : 0 ≤ Real.sqrt μ / Real.sqrt n := by
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hSplit :
      Real.sqrt μ * c = (Real.sqrt μ / Real.sqrt n) * (Real.sqrt n * c) := by
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := by
      exact Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)
    field_simp [hsqrt_ne]
  constructor
  · -- Proof comment: if the lower central-binomial band is negative, the claim is automatic;
    -- otherwise multiply the lower ratio bound by the lower central-binomial band.
    by_cases hLowerConst : 0 ≤ 1 / Real.sqrt Real.pi - η
    · rw [hSplit]
      exact mul_le_mul hRatioLower hCoreLower hLowerConst hRatioNonneg
    · have hLeftNonpos :
        Real.sqrt (2 / (1 + δ)) * (1 / Real.sqrt Real.pi - η) ≤ 0 := by
        have hSqrtNonneg : 0 ≤ Real.sqrt (2 / (1 + δ)) := Real.sqrt_nonneg _
        nlinarith
      have hRightNonneg : 0 ≤ Real.sqrt μ * c := mul_nonneg (Real.sqrt_nonneg _) hCNonneg
      exact le_trans hLeftNonpos hRightNonneg
  · -- Proof comment: the upper band uses only nonnegative factors, so monotonicity of
    -- multiplication applies directly after splitting off `sqrt μ / sqrt n`.
    rw [hSplit]
    exact mul_le_mul hRatioUpper hCoreUpper hCoreNonneg (by positivity)

/-- Helper for Exercise 17.5.2: the full even Poisson mass is controlled by the window mass plus
the full relative tail mass. -/
private lemma evenMass_le_windowMass_add_tailMass (δ : ℝ) (μ : ℝ≥0) :
    (∑' n : ℕ, poissonPMFReal μ (2 * n)) ≤ evenCentralWindowMass δ μ + poissonRelativeTailMass δ μ := by
  -- Proof comment: each even summand either lies inside the window or contributes to the full
  -- Poisson tail at the same even index; summing gives the comparison.
  let window : ℕ → ℝ := fun n ↦
    if |(2 * n : ℝ) - μ| ≤ δ * μ then poissonPMFReal μ (2 * n) else 0
  let tail : ℕ → ℝ := fun n ↦
    if δ * μ ≤ |(n : ℝ) - μ| then poissonPMFReal μ n else 0
  have hEvenSummable : Summable (fun n : ℕ ↦ poissonPMFReal μ (2 * n)) := by
    refine Summable.comp_injective (poissonPMFRealSum μ).summable ?_
    intro a b hab
    omega
  have hWindowSummable : Summable window := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ by
        by_cases h : |(2 * n : ℝ) - μ| ≤ δ * μ
        · simp [window, h, poissonPMFReal_nonneg]
        · simp [window, h])
      (fun n ↦ by
        by_cases h : |(2 * n : ℝ) - μ| ≤ δ * μ
        · simp [window, h]
        · simp [window, h, poissonPMFReal_nonneg])
      hEvenSummable
  have hTailSummable : Summable tail := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ by
        by_cases h : δ * μ ≤ |(n : ℝ) - μ|
        · simp [tail, h, poissonPMFReal_nonneg]
        · simp [tail, h])
      (fun n ↦ by
        by_cases h : δ * μ ≤ |(n : ℝ) - μ|
        · simp [tail, h]
        · simp [tail, h, poissonPMFReal_nonneg])
      (poissonPMFRealSum μ).summable
  have hTailEvenSummable : Summable (fun n : ℕ ↦ tail (2 * n)) :=
    Summable.comp_injective hTailSummable (by
      intro a b hab
      omega)
  have hPointwise : ∀ n : ℕ, poissonPMFReal μ (2 * n) ≤ window n + tail (2 * n) := by
    intro n
    by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
    · have hTailNonneg : 0 ≤ tail (2 * n) := by
        unfold tail
        split_ifs <;> simp [poissonPMFReal_nonneg]
      simp [window, hwin]
      linarith
    · have htail : δ * μ ≤ |(2 * n : ℝ) - μ| := (lt_of_not_ge hwin).le
      simp [window, tail, hwin, htail]
  calc
    (∑' n : ℕ, poissonPMFReal μ (2 * n))
      ≤ ∑' n : ℕ, (window n + tail (2 * n)) := by
          exact Summable.tsum_le_tsum hPointwise hEvenSummable (hWindowSummable.add hTailEvenSummable)
    _ = (∑' n : ℕ, window n) + ∑' n : ℕ, tail (2 * n) := by
          rw [(hWindowSummable.tsum_add hTailEvenSummable)]
    _ ≤ (∑' n : ℕ, window n) + ∑' n : ℕ, tail n := by
          have hTailComp :
              ∑' n : ℕ, tail (2 * n) ≤ ∑' n : ℕ, tail n := by
            simpa [Function.comp] using
              (tsum_comp_le_tsum_of_inj (f := tail) hTailSummable
                (fun a ↦ by
                  unfold tail
                  split_ifs <;> simp [poissonPMFReal_nonneg])
                (show Function.Injective (fun a : ℕ ↦ 2 * a) by
                  intro a b hab
                  have hEq : a + a = b + b := by simpa [two_mul] using hab
                  omega))
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hTailComp (∑' n : ℕ, window n)
    _ = evenCentralWindowMass δ μ + poissonRelativeTailMass δ μ := by
          simp [evenCentralWindowMass, poissonRelativeTailMass, window, tail]

/-- Helper for Exercise 17.5.2: the even Poisson mass inside the central relative window still
converges to `1 / 2`. -/
private lemma poissonEvenCentralWindowMass_tendsto_half (δ : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1) :
    Tendsto (evenCentralWindowMass δ) atTop (nhds (1 / 2 : ℝ)) := by
  -- Proof comment: the window mass sits below the full even mass and above it up to the vanishing
  -- full Poisson tail outside the relative window.
  let evenMass : ℝ≥0 → ℝ := fun μ ↦ ∑' n : ℕ, poissonPMFReal μ (2 * n)
  have hEven : Tendsto evenMass atTop (nhds (1 / 2 : ℝ)) := poissonEvenMass_tendsto_half
  have hTail : Tendsto (poissonRelativeTailMass δ) atTop (nhds 0) :=
    poissonRelativeTailMass_tendsto_zero δ hδ
  have hLower :
      ∀ μ : ℝ≥0, evenMass μ - poissonRelativeTailMass δ μ ≤ evenCentralWindowMass δ μ := by
    intro μ
    have hCompare := evenMass_le_windowMass_add_tailMass δ μ
    linarith
  have hUpper :
      ∀ μ : ℝ≥0, evenCentralWindowMass δ μ ≤ evenMass μ := by
    intro μ
    let window : ℕ → ℝ := fun n ↦
      if |(2 * n : ℝ) - μ| ≤ δ * μ then poissonPMFReal μ (2 * n) else 0
    have hEvenSummable : Summable (fun n : ℕ ↦ poissonPMFReal μ (2 * n)) := by
      refine Summable.comp_injective (poissonPMFRealSum μ).summable ?_
      intro a b hab
      omega
    have hWindowSummable : Summable window := by
      refine Summable.of_nonneg_of_le
        (fun n ↦ by
          by_cases h : |(2 * n : ℝ) - μ| ≤ δ * μ
          · simp [window, h, poissonPMFReal_nonneg]
          · simp [window, h])
        (fun n ↦ by
          by_cases h : |(2 * n : ℝ) - μ| ≤ δ * μ
          · simp [window, h]
          · simp [window, h, poissonPMFReal_nonneg])
        hEvenSummable
    simpa [evenMass, evenCentralWindowMass, window] using
      (Summable.tsum_le_tsum
        (fun n ↦ by
          by_cases h : |(2 * n : ℝ) - μ| ≤ δ * μ
          · simp [window, h]
          · simp [window, h, poissonPMFReal_nonneg])
        hWindowSummable
        hEvenSummable)
  have hLowerTendsto :
      Tendsto (fun μ : ℝ≥0 ↦ evenMass μ - poissonRelativeTailMass δ μ) atTop (nhds (1 / 2 : ℝ)) := by
    simpa using hEven.sub hTail
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLowerTendsto hEven hLower hUpper

/-- Helper for Exercise 17.5.2: the even-Poisson central-binomial series is summable because the
central-binomial factor is bounded by `1`. -/
private lemma summableEvenPoissonCentralBinomialSeries (μ : ℝ≥0) :
    Summable
      (fun n : ℕ ↦
        poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)) := by
  -- Proof comment: dominate the weighted even series by the even Poisson mass series using the
  -- deterministic bound `centralBinomialReturnProbability_le_one`.
  have hEven : Summable (fun n : ℕ ↦ poissonPMFReal μ (2 * n)) := by
    refine Summable.comp_injective (poissonPMFRealSum μ).summable ?_
    intro a b hab
    omega
  refine Summable.of_nonneg_of_le
    (fun n ↦ by
      refine mul_nonneg poissonPMFReal_nonneg ?_
      refine div_nonneg ?_ ?_
      · positivity
      · positivity)
    (fun n ↦ by
      have hCoeff := centralBinomialReturnProbability_le_one n
      have hMassNonneg : 0 ≤ poissonPMFReal μ (2 * n) := poissonPMFReal_nonneg
      calc
        poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
          ≤ poissonPMFReal μ (2 * n) * 1 := by
              exact mul_le_mul_of_nonneg_left hCoeff hMassNonneg
        _ = poissonPMFReal μ (2 * n) := by ring)
    hEven

/-- Helper for Exercise 17.5.2: after summing over the central relative window, the scaled
contribution is trapped between the deterministic window constants times the window mass. -/
private lemma scaledCentralWindowContribution_bounds (δ η : ℝ)
    (hδ : 0 < δ) (hδ' : δ < 1) (hη : 0 < η) :
    ∀ᶠ μ : ℝ≥0 in atTop,
      (Real.sqrt (2 / (1 + δ)) * (1 / Real.sqrt Real.pi - η) * evenCentralWindowMass δ μ
        ≤
          Real.sqrt μ *
            (∑' n : ℕ,
              if |(2 * n : ℝ) - μ| ≤ δ * μ then
                poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
              else 0)) ∧
      (Real.sqrt μ *
            (∑' n : ℕ,
            if |(2 * n : ℝ) - μ| ≤ δ * μ then
              poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
            else 0
            ) ≤ Real.sqrt (2 / (1 - δ)) * (1 / Real.sqrt Real.pi + η) * evenCentralWindowMass δ μ) := by
  -- Proof comment: sum the eventual pointwise window bounds from
  -- `centralWindowScaledBounds` against the nonnegative Poisson weights and rewrite both series
  -- via `evenCentralWindowMass`.
  filter_upwards [centralWindowScaledBounds δ η hδ hδ' hη] with μ hμ
  let windowMass : ℕ → ℝ := fun n ↦
    if |(2 * n : ℝ) - μ| ≤ δ * μ then poissonPMFReal μ (2 * n) else 0
  let windowContribution : ℕ → ℝ := fun n ↦
    if |(2 * n : ℝ) - μ| ≤ δ * μ then
      poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
    else 0
  let lowerConst : ℝ := Real.sqrt (2 / (1 + δ)) * (1 / Real.sqrt Real.pi - η)
  let upperConst : ℝ := Real.sqrt (2 / (1 - δ)) * (1 / Real.sqrt Real.pi + η)
  have hEvenSummable : Summable (fun n : ℕ ↦ poissonPMFReal μ (2 * n)) := by
    refine Summable.comp_injective (poissonPMFRealSum μ).summable ?_
    intro a b hab
    omega
  have hMassSummable : Summable windowMass := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · simp [windowMass, hwin, poissonPMFReal_nonneg]
        · simp [windowMass, hwin])
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · simp [windowMass, hwin]
        · simp [windowMass, hwin, poissonPMFReal_nonneg])
      hEvenSummable
  have hContributionSummable : Summable windowContribution := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · have hCoeffNonneg :
            0 ≤ ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
              refine div_nonneg ?_ ?_
              · positivity
              · positivity
          simp [windowContribution, hwin, mul_nonneg poissonPMFReal_nonneg hCoeffNonneg]
        · simp [windowContribution, hwin])
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · simpa [windowContribution, hwin] using
            le_rfl
              (poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n))
        · have hTermNonneg :
            0 ≤ poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
              refine mul_nonneg poissonPMFReal_nonneg ?_
              refine div_nonneg ?_ ?_
              · positivity
              · positivity
          simpa [windowContribution, hwin] using hTermNonneg)
      (summableEvenPoissonCentralBinomialSeries μ)
  have hLowerPointwise :
      ∀ n : ℕ, lowerConst * windowMass n ≤ Real.sqrt μ * windowContribution n := by
    intro n
    by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
    · rcases hμ n hwin with ⟨hLower, _⟩
      have hMassNonneg : 0 ≤ poissonPMFReal μ (2 * n) := poissonPMFReal_nonneg
      have hwin' : |(n : ℝ) * 2 - μ| ≤ δ * μ := by
        simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hwin
      have hsqrtDiv : Real.sqrt (2 / (1 + δ)) = Real.sqrt 2 / Real.sqrt (1 + δ) := by
        rw [Real.sqrt_div (by positivity)]
      have hMul := mul_le_mul_of_nonneg_right hLower hMassNonneg
      rw [hsqrtDiv] at hMul
      simpa [windowMass, windowContribution, lowerConst, hwin', mul_assoc, mul_comm,
        mul_left_comm] using hMul
    · simp [windowMass, windowContribution, lowerConst, hwin]
  have hUpperPointwise :
      ∀ n : ℕ, Real.sqrt μ * windowContribution n ≤ upperConst * windowMass n := by
    intro n
    by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
    · rcases hμ n hwin with ⟨_, hUpper⟩
      have hMassNonneg : 0 ≤ poissonPMFReal μ (2 * n) := poissonPMFReal_nonneg
      have hwin' : |(n : ℝ) * 2 - μ| ≤ δ * μ := by
        simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hwin
      have hsqrtDiv : Real.sqrt (2 / (1 - δ)) = Real.sqrt 2 / Real.sqrt (1 - δ) := by
        rw [Real.sqrt_div (by positivity)]
      have hMul := mul_le_mul_of_nonneg_right hUpper hMassNonneg
      rw [hsqrtDiv] at hMul
      simpa [windowMass, windowContribution, upperConst, hwin', mul_assoc, mul_comm,
        mul_left_comm] using hMul
    · simp [windowMass, windowContribution, upperConst, hwin]
  constructor
  · calc
      lowerConst * evenCentralWindowMass δ μ
        = lowerConst * ∑' n : ℕ, windowMass n := by
            simp [evenCentralWindowMass, windowMass, lowerConst]
      _ = ∑' n : ℕ, lowerConst * windowMass n := by
            rw [← tsum_mul_left]
      _ ≤ ∑' n : ℕ, Real.sqrt μ * windowContribution n := by
            exact Summable.tsum_le_tsum hLowerPointwise
              (hMassSummable.mul_left lowerConst)
              (hContributionSummable.mul_left _)
      _ = Real.sqrt μ * ∑' n : ℕ, windowContribution n := by
            rw [tsum_mul_left]
      _ =
          Real.sqrt μ *
            (∑' n : ℕ,
              if |(2 * n : ℝ) - μ| ≤ δ * μ then
                poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
              else 0) := by
                simp [windowContribution]
  · calc
      Real.sqrt μ *
          (∑' n : ℕ,
            if |(2 * n : ℝ) - μ| ≤ δ * μ then
              poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
            else 0)
        = ∑' n : ℕ, Real.sqrt μ * windowContribution n := by
            rw [tsum_mul_left]
      _ ≤ ∑' n : ℕ, upperConst * windowMass n := by
            exact Summable.tsum_le_tsum hUpperPointwise
              (hContributionSummable.mul_left _)
              (hMassSummable.mul_left upperConst)
      _ = upperConst * ∑' n : ℕ, windowMass n := by
            rw [tsum_mul_left]
      _ = upperConst * evenCentralWindowMass δ μ := by
            simp [evenCentralWindowMass, windowMass, upperConst]

/-- Helper for Exercise 17.5.2: the scaled contribution outside the central window is bounded by
the explicit Poisson tail estimate `1 / (δ² √μ)`. -/
private lemma scaledComplementContribution_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ μ : ℝ≥0 in atTop,
      (Real.sqrt μ *
          (∑' n : ℕ,
            if |(2 * n : ℝ) - μ| ≤ δ * μ then
              0
            else
              poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
          ) ≤ 1 / (δ ^ (2 : ℕ) * Real.sqrt μ)) := by
  -- Proof comment: dominate the off-window even series by the full Poisson relative tail, then
  -- use the Chebyshev tail estimate together with the identity
  -- `sqrt μ / (δ² μ) = 1 / (δ² sqrt μ)`.
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with μ hμ
  let complementTerm : ℕ → ℝ := fun n ↦
    if |(2 * n : ℝ) - μ| ≤ δ * μ then
      0
    else
      poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
  let tail : ℕ → ℝ := fun n ↦
    if δ * μ ≤ |(n : ℝ) - μ| then poissonPMFReal μ n else 0
  have hμ' : 0 < (μ : ℝ) := by
    exact_mod_cast hμ
  have hComplementSummable : Summable complementTerm := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · simp [complementTerm, hwin]
        · have hCoeffNonneg :
            0 ≤ ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
              refine div_nonneg ?_ ?_
              · positivity
              · positivity
          simp [complementTerm, hwin, mul_nonneg poissonPMFReal_nonneg hCoeffNonneg])
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · have hTermNonneg :
            0 ≤ poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
              refine mul_nonneg poissonPMFReal_nonneg ?_
              refine div_nonneg ?_ ?_
              · positivity
              · positivity
          simpa [complementTerm, hwin] using hTermNonneg
        · simpa [complementTerm, hwin] using
            le_rfl (poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)))
      (summableEvenPoissonCentralBinomialSeries μ)
  have hTailSummable : Summable tail := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ by
        by_cases htail : δ * μ ≤ |(n : ℝ) - μ|
        · simp [tail, htail, poissonPMFReal_nonneg]
        · simp [tail, htail])
      (fun n ↦ by
        by_cases htail : δ * μ ≤ |(n : ℝ) - μ|
        · simp [tail, htail]
        · simp [tail, htail, poissonPMFReal_nonneg])
      (poissonPMFRealSum μ).summable
  have hTailEvenSummable : Summable (fun n : ℕ ↦ tail (2 * n)) :=
    Summable.comp_injective hTailSummable (by
      intro a b hab
      omega)
  have hPointwise : ∀ n : ℕ, complementTerm n ≤ tail (2 * n) := by
    intro n
    by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
    · have hTailNonneg : 0 ≤ tail (2 * n) := by
        unfold tail
        split_ifs <;> simp [poissonPMFReal_nonneg]
      simpa [complementTerm, hwin] using hTailNonneg
    · have htail : δ * μ ≤ |(2 * n : ℝ) - μ| := (lt_of_not_ge hwin).le
      have hMassNonneg : 0 ≤ poissonPMFReal μ (2 * n) := poissonPMFReal_nonneg
      calc
        complementTerm n
          = poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
              simp [complementTerm, hwin]
        _ ≤ poissonPMFReal μ (2 * n) * 1 := by
              exact mul_le_mul_of_nonneg_left
                (centralBinomialReturnProbability_le_one n) hMassNonneg
        _ = tail (2 * n) := by
              simp [tail, htail]
  have hSeriesLe :
      ∑' n : ℕ, complementTerm n ≤ poissonRelativeTailMass δ μ := by
    calc
      ∑' n : ℕ, complementTerm n ≤ ∑' n : ℕ, tail (2 * n) := by
            exact Summable.tsum_le_tsum hPointwise hComplementSummable hTailEvenSummable
      _ ≤ ∑' n : ℕ, tail n := by
            simpa [Function.comp] using
              (tsum_comp_le_tsum_of_inj (f := tail) hTailSummable
                (fun a ↦ by
                  unfold tail
                  split_ifs <;> simp [poissonPMFReal_nonneg])
                (show Function.Injective (fun a : ℕ ↦ 2 * a) by
                  intro a b hab
                  have hEq : a + a = b + b := by simpa [two_mul] using hab
                  omega))
      _ = poissonRelativeTailMass δ μ := by
            simp [poissonRelativeTailMass, tail]
  have hTailBound :
      poissonRelativeTailMass δ μ ≤ 1 / (δ ^ (2 : ℕ) * (μ : ℝ)) := by
    simpa [poissonRelativeTailMass] using poissonRelativeWindowTail_le δ μ hδ hμ'
  have hSqrtNe : Real.sqrt (μ : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 hμ'
  have hSqrtSq : Real.sqrt (μ : ℝ) * Real.sqrt (μ : ℝ) = (μ : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (μ : ℝ) by positivity)]
  calc
    Real.sqrt μ *
        (∑' n : ℕ,
          if |(2 * n : ℝ) - μ| ≤ δ * μ then
            0
          else
            poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n))
      = Real.sqrt μ * ∑' n : ℕ, complementTerm n := by
          simp [complementTerm]
    _ ≤ Real.sqrt μ * poissonRelativeTailMass δ μ := by
          exact mul_le_mul_of_nonneg_left hSeriesLe (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt μ * (1 / (δ ^ (2 : ℕ) * (μ : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hTailBound (Real.sqrt_nonneg _)
    _ = Real.sqrt μ / (δ ^ (2 : ℕ) * (μ : ℝ)) := by ring
    _ = 1 / (δ ^ (2 : ℕ) * Real.sqrt μ) := by
          have hInvSqrt : Real.sqrt μ / (μ : ℝ) = 1 / Real.sqrt μ := by
            -- Proof comment: replace `μ` by `√μ * √μ` and cancel one square-root factor.
            have hμeq : (μ : ℝ) = Real.sqrt (μ : ℝ) * Real.sqrt (μ : ℝ) := by
              simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ (μ : ℝ) by positivity)).symm
            rw [hμeq]
            field_simp [hSqrtNe]
            simp [Real.sqrt_sq_eq_abs, Real.sqrt_nonneg]
          have hEq :
              Real.sqrt μ / (δ ^ (2 : ℕ) * (μ : ℝ)) =
                (1 / (δ ^ (2 : ℕ))) * (Real.sqrt μ / (μ : ℝ)) := by
            field_simp [pow_two, hδ.ne']
          rw [hEq, hInvSqrt]
          field_simp [pow_two, hδ.ne', hSqrtNe]

/-- Helper for Exercise 17.5.2: the explicit complement bound `1 / (δ² √μ)` tends to `0`
as `μ → ∞`. -/
private lemma scaledComplementBound_tendsto_zero (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun μ : ℝ≥0 ↦ 1 / (δ ^ (2 : ℕ) * Real.sqrt μ)) atTop (nhds 0) := by
  -- Proof comment: `√μ → ∞`, so its reciprocal tends to `0`, and the fixed factor `δ⁻²`
  -- does not change the limit.
  have hcoe : Tendsto (fun μ : ℝ≥0 ↦ (μ : ℝ)) atTop atTop :=
    (NNReal.tendsto_coe_atTop).2 tendsto_id
  have hsqrt : Tendsto (fun μ : ℝ≥0 ↦ Real.sqrt μ) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcoe
  have hinv : Tendsto (fun μ : ℝ≥0 ↦ (Real.sqrt μ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hScaled :
      Tendsto
        (fun μ : ℝ≥0 ↦ (δ ^ (2 : ℕ))⁻¹ * (Real.sqrt μ)⁻¹)
        atTop
        (nhds ((δ ^ (2 : ℕ))⁻¹ * 0)) :=
    tendsto_const_nhds.mul hinv
  convert hScaled using 1
  · ext μ
    field_simp [hδ.ne']
  · simp

/-- Helper for Exercise 17.5.2: the scaled even-Poisson central-binomial series whose limit gives
the return-probability asymptotic. -/
private def scaledEvenPoissonCentralBinomialSeries (μ : ℝ≥0) : ℝ :=
  Real.sqrt μ *
    (∑' n : ℕ,
      poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n))

/-- Helper for Exercise 17.5.2: the scaled even-Poisson central-binomial series is nonnegative
termwise. -/
private lemma scaledEvenPoissonCentralBinomialSeries_nonneg (μ : ℝ≥0) :
    0 ≤ scaledEvenPoissonCentralBinomialSeries μ := by
  -- Proof comment: every coefficient in the defining series is nonnegative, and the prefactor
  -- `√μ` is nonnegative as well.
  dsimp [scaledEvenPoissonCentralBinomialSeries]
  refine mul_nonneg (Real.sqrt_nonneg _) ?_
  exact tsum_nonneg fun n ↦ by
    refine mul_nonneg poissonPMFReal_nonneg ?_
    refine div_nonneg ?_ ?_
    · positivity
    · positivity

/-- Helper for Exercise 17.5.2: the full even-Poisson central-binomial series splits into its
central-window and complement contributions. -/
private lemma scaledEvenPoissonCentralBinomialSeries_split (δ : ℝ) (μ : ℝ≥0) :
    scaledEvenPoissonCentralBinomialSeries μ
      =
        Real.sqrt μ *
            (∑' n : ℕ,
              if |(2 * n : ℝ) - μ| ≤ δ * μ then
                poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
              else 0) +
          Real.sqrt μ *
            (∑' n : ℕ,
              if |(2 * n : ℝ) - μ| ≤ δ * μ then
                0
              else
                poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)) := by
  -- Proof comment: each summand is the sum of its inside-window and outside-window pieces, and
  -- both pieces are summable by domination with the full even series.
  let centralTerm : ℕ → ℝ := fun n ↦
    if |(2 * n : ℝ) - μ| ≤ δ * μ then
      poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
    else 0
  let complementTerm : ℕ → ℝ := fun n ↦
    if |(2 * n : ℝ) - μ| ≤ δ * μ then
      0
    else
      poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
  have hCentralSummable : Summable centralTerm := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · have hCoeffNonneg :
            0 ≤ ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
              refine div_nonneg ?_ ?_
              · positivity
              · positivity
          simp [centralTerm, hwin, mul_nonneg poissonPMFReal_nonneg hCoeffNonneg]
        · simp [centralTerm, hwin])
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · simpa [centralTerm, hwin] using
            le_rfl (poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n))
        · have hCoeffNonneg :
            0 ≤ poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
              refine mul_nonneg poissonPMFReal_nonneg ?_
              refine div_nonneg ?_ ?_
              · positivity
              · positivity
          simpa [centralTerm, hwin] using hCoeffNonneg)
      (summableEvenPoissonCentralBinomialSeries μ)
  have hComplementSummable : Summable complementTerm := by
    refine Summable.of_nonneg_of_le
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · simp [complementTerm, hwin]
        · have hCoeffNonneg :
            0 ≤ ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
              refine div_nonneg ?_ ?_
              · positivity
              · positivity
          simp [complementTerm, hwin, mul_nonneg poissonPMFReal_nonneg hCoeffNonneg]
      )
      (fun n ↦ by
        by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
        · have hCoeffNonneg :
            0 ≤ poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
              refine mul_nonneg poissonPMFReal_nonneg ?_
              refine div_nonneg ?_ ?_
              · positivity
              · positivity
          simpa [complementTerm, hwin] using hCoeffNonneg
        · simpa [complementTerm, hwin] using
            le_rfl (poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)))
      (summableEvenPoissonCentralBinomialSeries μ)
  calc
    scaledEvenPoissonCentralBinomialSeries μ
      = Real.sqrt μ *
          (∑' n : ℕ,
            poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)) := by
          rfl
    _ = Real.sqrt μ * ∑' n : ℕ, (centralTerm n + complementTerm n) := by
          congr 1
          refine tsum_congr fun n ↦ ?_
          by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
          · simp [centralTerm, complementTerm, hwin]
          · simp [centralTerm, complementTerm, hwin]
    _ = Real.sqrt μ * ((∑' n : ℕ, centralTerm n) + ∑' n : ℕ, complementTerm n) := by
          rw [hCentralSummable.tsum_add hComplementSummable]
    _ =
        Real.sqrt μ *
            (∑' n : ℕ,
              if |(2 * n : ℝ) - μ| ≤ δ * μ then
                poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)
              else 0) +
          Real.sqrt μ *
            (∑' n : ℕ,
              if |(2 * n : ℝ) - μ| ≤ δ * μ then
                0
              else
                poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)) := by
          simp [centralTerm, complementTerm, mul_add]

/-- Helper for Exercise 17.5.2: the scaled complement contribution is nonnegative. -/
private lemma scaledComplementContribution_nonneg (δ : ℝ) (μ : ℝ≥0) :
    0 ≤
      Real.sqrt μ *
        (∑' n : ℕ,
          if |(2 * n : ℝ) - μ| ≤ δ * μ then
            0
          else
            poissonPMFReal μ (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)) := by
  -- Proof comment: the off-window series is termwise nonnegative, so multiplying it by `√μ`
  -- preserves nonnegativity.
  refine mul_nonneg (Real.sqrt_nonneg _) ?_
  exact tsum_nonneg fun n ↦ by
    by_cases hwin : |(2 * n : ℝ) - μ| ≤ δ * μ
    · simp [hwin]
    · have hCoeffNonneg :
        0 ≤ ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n) := by
          refine div_nonneg ?_ ?_
          · positivity
          · positivity
      simpa [hwin] using mul_nonneg poissonPMFReal_nonneg hCoeffNonneg

/-- Helper for Exercise 17.5.2: the reciprocal window-width sequence used to squeeze the scaled
series. -/
private def asymptoticWindowWidth (k : ℕ) : ℝ :=
  1 / ((k : ℝ) + 2)

/-- Helper for Exercise 17.5.2: the lower squeezing constants for the scaled series. -/
private def scaledEvenPoissonLowerApprox (k : ℕ) : ℝ :=
  Real.sqrt (2 / (1 + asymptoticWindowWidth k)) *
    (1 / Real.sqrt Real.pi - asymptoticWindowWidth k) * (1 / 2 : ℝ)

/-- Helper for Exercise 17.5.2: the upper squeezing constants for the scaled series. -/
private def scaledEvenPoissonUpperApprox (k : ℕ) : ℝ :=
  Real.sqrt (2 / (1 - asymptoticWindowWidth k)) *
    (1 / Real.sqrt Real.pi + asymptoticWindowWidth k) * (1 / 2 : ℝ)

/-- Helper for Exercise 17.5.2: the reciprocal window-width sequence is positive. -/
private lemma asymptoticWindowWidth_pos (k : ℕ) :
    0 < asymptoticWindowWidth k := by
  -- Proof comment: the denominator is at least `2`, so its reciprocal is positive.
  dsimp [asymptoticWindowWidth]
  positivity

/-- Helper for Exercise 17.5.2: the reciprocal window-width sequence is bounded above by `1`. -/
private lemma asymptoticWindowWidth_lt_one (k : ℕ) :
    asymptoticWindowWidth k < 1 := by
  -- Proof comment: the denominator is strictly larger than `1`, so its reciprocal is below `1`.
  have hKtwo : (1 : ℝ) < (k : ℝ) + 2 := by
    have hKnonneg : (0 : ℝ) ≤ k := by positivity
    nlinarith
  dsimp [asymptoticWindowWidth]
  simpa [one_div] using inv_lt_one_of_one_lt₀ hKtwo

/-- Helper for Exercise 17.5.2: the reciprocal window-width sequence tends to `0`. -/
private lemma asymptoticWindowWidth_tendsto_zero :
    Tendsto asymptoticWindowWidth atTop (nhds 0) := by
  -- Proof comment: `1 / (k + 2)` is a shifted reciprocal sequence.
  convert ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 2))
    using 1
  ext k
  simp [asymptoticWindowWidth, one_div]

/-- Helper for Exercise 17.5.2: the lower squeezing constants converge to the target limit. -/
private lemma scaledEvenPoissonLowerApprox_tendsto :
    Tendsto scaledEvenPoissonLowerApprox atTop
      (nhds ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ))) := by
  -- Proof comment: compose the reciprocal window-width limit with the continuous lower-bound
  -- formula in the window parameter.
  let lowerFun : ℝ → ℝ := fun x ↦
    Real.sqrt (2 / (1 + x)) * (1 / Real.sqrt Real.pi - x) * (1 / 2 : ℝ)
  have hLowerFunTendsto :
      Tendsto lowerFun (nhds 0)
        (nhds ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ))) := by
    have hRatio : ContinuousAt (fun x : ℝ ↦ 2 / (1 + x)) 0 := by
      exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)
    have hSqrt : ContinuousAt (fun x : ℝ ↦ Real.sqrt (2 / (1 + x))) 0 :=
      Real.continuous_sqrt.continuousAt.comp hRatio
    have hLinear : ContinuousAt (fun x : ℝ ↦ 1 / Real.sqrt Real.pi - x) 0 :=
      continuousAt_const.sub continuousAt_id
    have hConst : ContinuousAt (fun _ : ℝ ↦ (1 / 2 : ℝ)) 0 := continuousAt_const
    have h0 : lowerFun 0 = ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ)) := by
      simp [lowerFun]
    simpa [lowerFun, h0] using ((hSqrt.mul hLinear).mul hConst).tendsto
  convert (hLowerFunTendsto.comp asymptoticWindowWidth_tendsto_zero) using 1

/-- Helper for Exercise 17.5.2: the upper squeezing constants converge to the target limit. -/
private lemma scaledEvenPoissonUpperApprox_tendsto :
    Tendsto scaledEvenPoissonUpperApprox atTop
      (nhds ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ))) := by
  -- Proof comment: the upper-bound formula is continuous at `0`, so the same reciprocal
  -- window-width sequence transports its limit to the target constant.
  let upperFun : ℝ → ℝ := fun x ↦
    Real.sqrt (2 / (1 - x)) * (1 / Real.sqrt Real.pi + x) * (1 / 2 : ℝ)
  have hUpperFunTendsto :
      Tendsto upperFun (nhds 0)
        (nhds ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ))) := by
    have hRatio : ContinuousAt (fun x : ℝ ↦ 2 / (1 - x)) 0 := by
      exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    have hSqrt : ContinuousAt (fun x : ℝ ↦ Real.sqrt (2 / (1 - x))) 0 :=
      Real.continuous_sqrt.continuousAt.comp hRatio
    have hLinear : ContinuousAt (fun x : ℝ ↦ 1 / Real.sqrt Real.pi + x) 0 :=
      continuousAt_const.add continuousAt_id
    have hConst : ContinuousAt (fun _ : ℝ ↦ (1 / 2 : ℝ)) 0 := continuousAt_const
    have h0 : upperFun 0 = ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ)) := by
      simp [upperFun]
    simpa [upperFun, h0] using ((hSqrt.mul hLinear).mul hConst).tendsto
  convert (hUpperFunTendsto.comp asymptoticWindowWidth_tendsto_zero) using 1

/-- Helper for Exercise 17.5.2: every strict lower target is eventually dominated by the scaled
even-Poisson central-binomial series. -/
private lemma scaledEvenPoissonCentralBinomialSeries_eventuallyGt {a : ℝ}
    (ha : a < ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ))) :
    ∀ᶠ μ : ℝ≥0 in atTop, a < scaledEvenPoissonCentralBinomialSeries μ := by
  -- Proof comment: pick one reciprocal window-width for which the lower approximation already
  -- exceeds `a`, and then compare the full series to its central-window contribution.
  by_cases haNeg : a < 0
  · exact Filter.Eventually.of_forall fun μ ↦
      lt_of_lt_of_le haNeg (scaledEvenPoissonCentralBinomialSeries_nonneg μ)
  · rcases
      Filter.eventually_atTop.1 ((tendsto_order.1 scaledEvenPoissonLowerApprox_tendsto).1 a ha)
        with ⟨K, hK⟩
    let δ : ℝ := asymptoticWindowWidth K
    let lowerConst : ℝ := Real.sqrt (2 / (1 + δ)) * (1 / Real.sqrt Real.pi - δ)
    have hδ : 0 < δ := asymptoticWindowWidth_pos K
    have hδ' : δ < 1 := asymptoticWindowWidth_lt_one K
    have haLower : a < lowerConst * (1 / 2 : ℝ) := by
      simpa [δ, lowerConst, scaledEvenPoissonLowerApprox, asymptoticWindowWidth] using hK K le_rfl
    have hWindowTendsto :
        Tendsto (fun μ : ℝ≥0 ↦ lowerConst * evenCentralWindowMass δ μ) atTop
          (nhds (lowerConst * (1 / 2 : ℝ))) := by
      simpa [lowerConst] using
        (poissonEvenCentralWindowMass_tendsto_half δ hδ hδ').const_mul lowerConst
    have hWindowEventually :
        ∀ᶠ μ : ℝ≥0 in atTop, a < lowerConst * evenCentralWindowMass δ μ := by
      exact (tendsto_order.1 hWindowTendsto).1 a haLower
    have hLowerBound :
        ∀ᶠ μ : ℝ≥0 in atTop, lowerConst * evenCentralWindowMass δ μ ≤
          scaledEvenPoissonCentralBinomialSeries μ := by
      filter_upwards [scaledCentralWindowContribution_bounds δ δ hδ hδ' hδ] with μ hCentral
      have hCompNonneg := scaledComplementContribution_nonneg δ μ
      rw [scaledEvenPoissonCentralBinomialSeries_split δ μ]
      linarith [hCentral.1, hCompNonneg]
    exact (hWindowEventually.and hLowerBound).mono fun μ hμ ↦ lt_of_lt_of_le hμ.1 hμ.2

/-- Helper for Exercise 17.5.2: every strict upper target eventually dominates the scaled
even-Poisson central-binomial series. -/
private lemma scaledEvenPoissonCentralBinomialSeries_eventuallyLt {b : ℝ}
    (hb : ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ)) < b) :
    ∀ᶠ μ : ℝ≥0 in atTop, scaledEvenPoissonCentralBinomialSeries μ < b := by
  -- Proof comment: pick one reciprocal window-width for which the upper approximation already
  -- lies below `b`, and then add the explicit complement bound.
  rcases
    Filter.eventually_atTop.1 ((tendsto_order.1 scaledEvenPoissonUpperApprox_tendsto).2 b hb)
      with ⟨K, hK⟩
  let δ : ℝ := asymptoticWindowWidth K
  let upperConst : ℝ := Real.sqrt (2 / (1 - δ)) * (1 / Real.sqrt Real.pi + δ)
  have hδ : 0 < δ := asymptoticWindowWidth_pos K
  have hδ' : δ < 1 := asymptoticWindowWidth_lt_one K
  have hbUpper : upperConst * (1 / 2 : ℝ) < b := by
    simpa [δ, upperConst, scaledEvenPoissonUpperApprox, asymptoticWindowWidth] using hK K le_rfl
  have hUpperTendsto :
      Tendsto
        (fun μ : ℝ≥0 ↦
          upperConst * evenCentralWindowMass δ μ + 1 / (δ ^ (2 : ℕ) * Real.sqrt μ))
        atTop
        (nhds (upperConst * (1 / 2 : ℝ))) := by
    simpa [upperConst] using
      ((poissonEvenCentralWindowMass_tendsto_half δ hδ hδ').const_mul upperConst).add
        (scaledComplementBound_tendsto_zero δ hδ)
  have hUpperEventually :
      ∀ᶠ μ : ℝ≥0 in atTop,
        upperConst * evenCentralWindowMass δ μ + 1 / (δ ^ (2 : ℕ) * Real.sqrt μ) < b := by
    exact (tendsto_order.1 hUpperTendsto).2 b hbUpper
  have hUpperBound :
      ∀ᶠ μ : ℝ≥0 in atTop,
        scaledEvenPoissonCentralBinomialSeries μ ≤
          upperConst * evenCentralWindowMass δ μ + 1 / (δ ^ (2 : ℕ) * Real.sqrt μ) := by
    filter_upwards [scaledCentralWindowContribution_bounds δ δ hδ hδ' hδ,
      scaledComplementContribution_le δ hδ] with μ hCentral hComp
    rw [scaledEvenPoissonCentralBinomialSeries_split δ μ]
    linarith [hCentral.2, hComp]
  exact (hUpperEventually.and hUpperBound).mono fun μ hμ ↦ lt_of_le_of_lt hμ.2 hμ.1

/-- Helper for Exercise 17.5.2: the natural `μ`-scaled even-Poisson central-binomial series
converges to `1 / √(2π)`. -/
private lemma scaledEvenPoissonCentralBinomialSeries_tendsto :
    Tendsto scaledEvenPoissonCentralBinomialSeries
      atTop
      (nhds ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ))) := by
  -- Proof comment: the lower and upper eventual estimates are isolated in dedicated helper
  -- lemmas, so `tendsto_order` closes the squeeze without re-elaborating the whole window split.
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact scaledEvenPoissonCentralBinomialSeries_eventuallyGt ha
  · intro b hb
    exact scaledEvenPoissonCentralBinomialSeries_eventuallyLt hb

-- Proof sketch: write the first coordinate as the difference of two independent Poisson
-- processes of rate `(2D)⁻¹`, rewrite the probability by
-- `poissonizedSimpleRandomWalkFirstCoordinateZeroProbability_eq_bessel`, and then apply the
-- standard large-argument asymptotic `I₀(s) ~ exp s / sqrt (2π s)` with `s = t / D`.
/-- Exercise 17.5.2: for the continuous-time Poissonized simple random walk on `ℤ^D` started at
`0`, the first-coordinate return probability
`P₀[Y_t¹ = 0] = exp (-t / D) * I₀(t / D)` satisfies
`P₀[Y_t¹ = 0] ~ (2π / D)^(-1 / 2) t^(-1 / 2)`, formalized here in equivalent limit form. -/
theorem poissonizedSimpleRandomWalkFirstCoordinateZeroProbability_asymptotic
    (D : ℕ) [NeZero D] :
    Tendsto
      (fun t : ℝ≥0 ↦
        (t : ℝ) ^ ((1 : ℝ) / 2) *
          poissonizedSimpleRandomWalkFirstCoordinateZeroProbability D t)
      atTop
      (nhds ((2 * Real.pi / D) ^ (-(1 : ℝ) / 2))) := by
  -- Proof comment: rewrite the return probability through the even-Poisson central-binomial
  -- series, compose the scaled-series limit with `t ↦ t / D`, and simplify the deterministic
  -- scaling factor.
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hMapReal :
      Tendsto (fun t : ℝ≥0 ↦ ((t / (D : ℝ≥0) : ℝ))) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((NNReal.tendsto_coe_atTop).2 tendsto_id).const_mul_atTop (show 0 < ((D : ℝ) : ℝ)⁻¹ by
        positivity))
  have hMap : Tendsto (fun t : ℝ≥0 ↦ t / (D : ℝ≥0)) atTop atTop :=
    (NNReal.tendsto_coe_atTop).1 hMapReal
  have hScaled :
      Tendsto (fun t : ℝ≥0 ↦ scaledEvenPoissonCentralBinomialSeries (t / (D : ℝ≥0))) atTop
        (nhds ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ))) :=
    scaledEvenPoissonCentralBinomialSeries_tendsto.comp hMap
  have hScaleConst :
      Tendsto
        (fun t : ℝ≥0 ↦
          Real.sqrt (D : ℝ) * scaledEvenPoissonCentralBinomialSeries (t / (D : ℝ≥0)))
        atTop
        (nhds (Real.sqrt (D : ℝ) * ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ)))) := by
    exact hScaled.const_mul (Real.sqrt (D : ℝ))
  have hRewrite :
      (fun t : ℝ≥0 ↦
        (t : ℝ) ^ ((1 : ℝ) / 2) *
          poissonizedSimpleRandomWalkFirstCoordinateZeroProbability D t) =
        fun t : ℝ≥0 ↦
          Real.sqrt (D : ℝ) * scaledEvenPoissonCentralBinomialSeries (t / (D : ℝ≥0)) := by
    funext t
    have hsqrt : (t : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt t := by
      simpa using (Real.sqrt_eq_rpow (t : ℝ)).symm
    have hSplit :
        Real.sqrt (t : ℝ) = Real.sqrt (D : ℝ) * Real.sqrt ((t / (D : ℝ≥0) : ℝ)) := by
      -- Proof comment: rewrite `t` as `D * (t / D)` and then take square roots multiplicatively.
      have hFactor : (t : ℝ) = (((D : ℝ≥0) : ℝ)) * ((t / (D : ℝ≥0) : ℝ)) := by
        have hDne : (((D : ℝ≥0) : ℝ)) ≠ 0 := by
          exact_mod_cast (NeZero.ne D)
        field_simp [hDne]
      calc
        Real.sqrt (t : ℝ)
          = Real.sqrt ((((D : ℝ≥0) : ℝ)) * ((t / (D : ℝ≥0) : ℝ))) := by
              nth_rw 1 [hFactor]
        _ = Real.sqrt ((((D : ℝ≥0) : ℝ))) * Real.sqrt ((t / (D : ℝ≥0) : ℝ)) := by
              rw [Real.sqrt_mul (show 0 ≤ ((((D : ℝ≥0) : ℝ)) : ℝ) by positivity)]
        _ = Real.sqrt (D : ℝ) * Real.sqrt ((t / (D : ℝ≥0) : ℝ)) := by norm_num
    rw [poissonizedSimpleRandomWalkFirstCoordinateZeroProbability_eq_evenPoissonCentralBinomialSeries,
      hsqrt]
    calc
      Real.sqrt (t : ℝ) *
          (∑' n : ℕ,
            poissonPMFReal (t / (D : ℝ≥0)) (2 * n) * ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n))
        = (Real.sqrt (D : ℝ) * Real.sqrt ((t / (D : ℝ≥0) : ℝ))) *
            (∑' n : ℕ,
              poissonPMFReal (t / (D : ℝ≥0)) (2 * n) *
                ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n)) := by rw [hSplit]
      _ = Real.sqrt (D : ℝ) *
            (Real.sqrt ((t / (D : ℝ≥0) : ℝ)) *
              (∑' n : ℕ,
                poissonPMFReal (t / (D : ℝ≥0)) (2 * n) *
                  ((Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n))) := by ring
      _ = Real.sqrt (D : ℝ) * scaledEvenPoissonCentralBinomialSeries (t / (D : ℝ≥0)) := by
            simp [scaledEvenPoissonCentralBinomialSeries]
  have hConst :
      Real.sqrt (D : ℝ) * ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ)) =
        (2 * Real.pi / D) ^ (-(1 : ℝ) / 2) := by
    have hSqrtMul : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
      simpa using (Real.sqrt_mul (show 0 ≤ (2 : ℝ) by positivity) Real.pi)
    have hEq1 :
        Real.sqrt (D : ℝ) * ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ)) =
          Real.sqrt (D : ℝ) / Real.sqrt (2 * Real.pi) := by
      have hSqrtTwoSq : (Real.sqrt (2 : ℝ)) ^ (2 : ℕ) = 2 := by
        simpa using (Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity))
      rw [hSqrtMul]
      field_simp [Real.sqrt_ne_zero'.2 hDpos, Real.sqrt_ne_zero'.2 (by positivity : 0 < (2 : ℝ)),
        Real.sqrt_ne_zero'.2 Real.pi_pos]
      simpa using hSqrtTwoSq
    have hDiv :
        Real.sqrt (2 * Real.pi / D) = Real.sqrt (2 * Real.pi) / Real.sqrt (D : ℝ) := by
      simpa using
        (Real.sqrt_div (show 0 ≤ (2 * Real.pi : ℝ) by positivity) (show 0 ≤ (D : ℝ) by positivity))
    have hEq2 :
        Real.sqrt (D : ℝ) / Real.sqrt (2 * Real.pi) = 1 / Real.sqrt (2 * Real.pi / D) := by
      rw [hDiv]
      field_simp [Real.sqrt_ne_zero'.2 hDpos,
        Real.sqrt_ne_zero'.2 (by positivity : 0 < (2 * Real.pi : ℝ))]
    have hNonneg : 0 ≤ 2 * Real.pi / D := by positivity
    have hEq3 : 1 / Real.sqrt (2 * Real.pi / D) = (2 * Real.pi / D) ^ (-(1 : ℝ) / 2) := by
      calc
        1 / Real.sqrt (2 * Real.pi / D) = (Real.sqrt (2 * Real.pi / D))⁻¹ := by rw [one_div]
        _ = ((2 * Real.pi / D) ^ (1 / (2 : ℝ)))⁻¹ := by rw [Real.sqrt_eq_rpow]
        _ = (2 * Real.pi / D) ^ (-(1 / (2 : ℝ))) := by
              symm
              exact Real.rpow_neg hNonneg (1 / (2 : ℝ))
        _ = (2 * Real.pi / D) ^ (-(1 : ℝ) / 2) := by
              congr 1
              ring
    exact hEq1.trans (hEq2.trans hEq3)
  have hFinal :
      Tendsto
        (fun t : ℝ≥0 ↦
          (t : ℝ) ^ ((1 : ℝ) / 2) *
            poissonizedSimpleRandomWalkFirstCoordinateZeroProbability D t)
        atTop
        (nhds (Real.sqrt (D : ℝ) * ((Real.sqrt 2 * (1 / Real.sqrt Real.pi)) * (1 / 2 : ℝ)))) := by
    convert hScaleConst using 1
  simpa only [← hConst] using hFinal

end ProbabilityTheory

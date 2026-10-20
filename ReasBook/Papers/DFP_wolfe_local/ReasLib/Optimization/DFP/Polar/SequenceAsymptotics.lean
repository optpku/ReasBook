module

public import ReasLib.Optimization.DFP.Polar.ActualObjective
public import ReasLib.Optimization.DFP.Polar.WolfeRatios
public import ReasLib.Topology.Sequences.Interleave
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

noncomputable section

open Filter
open scoped Topology BigOperators Asymptotics Matrix

namespace DFP.Polar.SequenceAsymptotics

/-- Helper for sec:known-results: the source physical displacement. -/
def step (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  p.point (k + 1) - p.point k

/-- Helper for sec:known-results: the original displacement formula. -/
theorem step_def (p : Parameters) (k : ℕ) :
    step p k = p.point (k + 1) - p.point k := by
  rfl

/-- Helper for sec:known-results: consecutive norms of the prescribed gradients. -/
def gradientRatio (p : Parameters) (k : ℕ) : ℝ :=
  ‖p.gradient (k + 1)‖ / ‖p.gradient k‖

/-- Helper for sec:known-results: the exact original gradient-norm quotient. -/
theorem gradientRatio_def (p : Parameters) (k : ℕ) :
    gradientRatio p k = ‖p.gradient (k + 1)‖ / ‖p.gradient k‖ := by
  rfl

/-- Helper for sec:known-results: the prescribed squared scales form a divergent
p-series, for every starting index, including its harmless totalization at zero. -/
theorem scaleSquare_not_summable (p : Parameters) :
    ¬ Summable (fun j ↦ p.scale j ^ 2) := by
  intro hsum
  have hshift : Summable (fun j : ℕ ↦
      ((j + p.startIndex : ℕ) : ℝ) ^ (-(2 : ℝ) / 3)) := by
    apply hsum.congr
    intro j
    rw [ScaleTails.scale_pow]
    simp only [Nat.cast_ofNat, Nat.add_comm]
  have hbase : Summable (fun j : ℕ ↦ (j : ℝ) ^ (-(2 : ℝ) / 3)) :=
    (summable_nat_add_iff p.startIndex).mp hshift
  have hexponent : -(2 : ℝ) / 3 < -1 := Real.summable_nat_rpow.mp hbase
  norm_num at hexponent

/-- Helper for sec:known-results: a positive quadratic lower bound on the actual
even step norms forces divergence of the full total step length. -/
theorem stepNorm_not_summable_of_lower (p : Parameters) {lower : ℝ}
    (hlower : 0 < lower)
    (hbound : ∀ k, lower * p.scale (k / 2) ^ 2 ≤ ‖step p k‖) :
    ¬ Summable (fun k ↦ ‖step p k‖) := by
  intro hsum
  have hinjective : Function.Injective (fun j : ℕ ↦ 2 * j) := by
    intro a b h
    dsimp only at h
    omega
  have heven := hsum.comp_injective hinjective
  have hcomparison (j : ℕ) : p.scale j ^ 2 ≤ lower⁻¹ * ‖step p (2 * j)‖ := by
    have hhalf : 2 * j / 2 = j := by omega
    have h := hbound (2 * j)
    rw [hhalf] at h
    calc
      p.scale j ^ 2 = lower⁻¹ * (lower * p.scale j ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hlower.ne', one_mul]
      _ ≤ lower⁻¹ * ‖step p (2 * j)‖ :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hlower.le)
  have hscaled := heven.mul_left lower⁻¹
  exact scaleSquare_not_summable p
    (Summable.of_nonneg_of_le (fun j ↦ sq_nonneg (p.scale j)) hcomparison hscaled)

/-- Helper for sec:known-results: the actual source steps have uniformly
comparable squared scales, and their nonnegative partial lengths tend to infinity.
All comparison constants precede every subsequently larger starting index. -/
theorem polarStepLengthDivergence :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ lower > 0, ∃ upper > 0, ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        let p := Parameters.of j₀ νStar
        (∀ k, lower * p.scale (k / 2) ^ 2 ≤ ‖step p k‖ ∧
          ‖step p k‖ ≤ upper * p.scale (k / 2) ^ 2) ∧
        ¬ Summable (fun k ↦ ‖step p k‖) ∧
          Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ‖step p k‖) atTop atTop := by
  obtain ⟨η, hη, hgeometry⟩ := PointGeometry.polarPointGeometry
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨_, _, _, _, _, _, _, lower, hlower, upper, hupper, _, _, J, hJ, hall⟩ :=
    hgeometry νStar hnear
  refine ⟨lower, hlower, upper, hupper, J, hJ, ?_⟩
  intro j₀ hj₀
  let p := Parameters.of j₀ νStar
  have hbounds : ∀ k, lower * p.scale (k / 2) ^ 2 ≤ ‖step p k‖ ∧
      ‖step p k‖ ≤ upper * p.scale (k / 2) ^ 2 := by
    simpa only [step_def] using (hall j₀ hj₀).2.step
  have hlowerBound (k : ℕ) := (hbounds k).1
  have hdiverge := stepNorm_not_summable_of_lower p hlower hlowerBound
  exact ⟨hbounds, hdiverge,
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k ↦ norm_nonneg (step p k))).mp
      hdiverge⟩

/-- Helper for sec:known-results: a positive absolute curvature quotient rules
out an exact accepted endpoint directional derivative. -/
theorem endpoint_ne_zero_of_curvatureRatio_pos (p : Parameters) (k : ℕ)
    (h : 0 < WolfeRatios.curvatureRatio p k) : WolfeRatios.endSlope p k ≠ 0 := by
  intro hz
  rw [WolfeRatios.curvatureRatio_def, hz, abs_zero, zero_div] at h
  exact (lt_irrefl 0) h

/-- Helper for sec:known-results: positivity of the source limiting curvature
ratios makes every accepted endpoint directional derivative nonzero after one
uniform natural starting-index threshold. -/
theorem polarAcceptedEndpointNonzero :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J, ∀ k,
        WolfeRatios.endSlope (Parameters.of j₀ νStar) k ≠ 0 := by
  obtain ⟨η, hη, hasymptotics⟩ := WolfeRatios.polarWolfeAsymptotics
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, C, hC, J₀, hJ₀, herror⟩ := hasymptotics νStar hnear
  let q := min (WolfeRatios.curvatureLimit νStar 0) (WolfeRatios.curvatureLimit νStar 1)
  have hq : 0 < q := lt_min (WolfeRatios.curvatureLimit_pos νStar hparameter 0)
    (WolfeRatios.curvatureLimit_pos νStar hparameter 1)
  have hqle (i : Fin 2) : q ≤ WolfeRatios.curvatureLimit νStar i := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hcutoff : 0 < q / (2 * C) := by positivity
  have htwoC : 0 < 2 * C := by positivity
  obtain ⟨J₁, _, hsmall⟩ := Continuation.existsStartThreshold _ hcutoff
  refine ⟨max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀ k
  let p := Parameters.of j₀ νStar
  have hj₀old : J₀ ≤ j₀ := (le_max_left _ _).trans hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ₀.trans_le hj₀old
  have htzero : p.scale 0 < q / (2 * C) :=
    hsmall νStar j₀ ((le_max_right _ _).trans hj₀)
  have hphase (j : ℕ) (i : Fin 2) :
      0 < WolfeRatios.curvatureRatio p (2 * j + (i : ℕ)) := by
    have hbound := (abs_le.mp (herror j₀ hj₀old j i).2.2).1
    have hscale := ScaleTails.scale_antitone p hstart (Nat.zero_le j)
    have hscaled := mul_le_mul_of_nonneg_left hscale hC.le
    have hcut : C * p.scale j < q / 2 := by
      nlinarith [(lt_div_iff₀ htwoC).mp htzero]
    have hlim := hqle i
    linarith
  apply endpoint_ne_zero_of_curvatureRatio_pos p k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simpa only [Nat.add_zero, Fin.val_zero] using hphase j 0
  · simpa only [Fin.val_one] using hphase j 1

/-- Helper for sec:known-results: dividing a cubic difference expansion by a
denominator within linear distance of one preserves its fourth-order error. -/
theorem quotientCubicError {a b t q E R : ℝ} (hb : 1 / 2 ≤ b) (ht : 0 ≤ t)
    (hnum : |a - b - q * t ^ 3| ≤ E * t ^ 4)
    (hden : |b - 1| ≤ R * t) :
    |a / b - 1 - q * t ^ 3| ≤ 2 * (E + |q| * R) * t ^ 4 := by
  have hbpos : 0 < b := by linarith
  have hidentity : a / b - 1 - q * t ^ 3 =
      ((a - b - q * t ^ 3) - q * t ^ 3 * (b - 1)) / b := by
    field_simp [hbpos.ne']
    ring
  have hterm : |q * t ^ 3 * (b - 1)| ≤ |q| * R * t ^ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht 3)]
    calc
      |q| * t ^ 3 * |b - 1| ≤ |q| * t ^ 3 * (R * t) :=
        mul_le_mul_of_nonneg_left hden (mul_nonneg (abs_nonneg _) (pow_nonneg ht 3))
      _ = |q| * R * t ^ 4 := by ring
  have htotal : |(a - b - q * t ^ 3) - q * t ^ 3 * (b - 1)| ≤
      (E + |q| * R) * t ^ 4 := by
    have htriangle := abs_sub (a - b - q * t ^ 3) (q * t ^ 3 * (b - 1))
    linarith
  have hnonnegative : 0 ≤ (E + |q| * R) * t ^ 4 := (abs_nonneg _).trans htotal
  rw [hidentity, abs_div, abs_of_pos hbpos]
  apply (div_le_iff₀ hbpos).mpr
  have hscaled := mul_le_mul_of_nonneg_left hb hnonnegative
  nlinarith

/-- Helper for sec:known-results: the accepted original radius expansion gives
a linear bound for its distance from one. -/
theorem radiusLinear_error {p : Parameters} {D : Fin 2 → ℝ} {K c B : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B) (hstart : 0 < p.startIndex)
    (hK : 0 ≤ K) (k : ℕ) :
    |p.radius k - 1| ≤ (3 * (D 0 + D 1) + K) * p.scale (k / 2) := by
  have ht := ScaleTails.scale_nonneg p (k / 2)
  have htone := ScaleTails.scale_le_one p hstart (k / 2)
  have hpower : p.scale (k / 2) ^ 2 ≤ p.scale (k / 2) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hpower hK
  have herror := (abs_le.mp (hr.expansion k)).2
  rw [abs_of_nonneg (sub_nonneg.mpr (hr.above_one k).le)]
  nlinarith

/-- Helper for sec:known-results: the cubic prescribed affine corrections and
the radius expansion give a uniform linear gradient-norm error. -/
theorem gradientNormLinear_error {p : Parameters} {D : Fin 2 → ℝ} {K c B A E : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B)
    (hc : ActualObjective.CoefficientEstimates p A E) (hstart : 0 < p.startIndex)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (k : ℕ) :
    |‖p.gradient k‖ - 1| ≤
      (3 * (D 0 + D 1) + K + A) * p.scale (k / 2) := by
  have hnorm : |‖p.gradient k‖ - p.radius k| ≤ A * p.scale (k / 2) ^ 3 := by
    have hreverse := abs_norm_sub_norm_le (p.gradient k) (p.point k)
    rw [PhysicalRealization.point_norm p k (zero_lt_one.trans (hr.above_one k)).le] at hreverse
    have hcoefficient : ‖p.gradient k - p.point k‖ ≤ A * p.scale (k / 2) ^ 3 := by
      simpa only [InterpolationSum.polarCoefficient_apply] using hc.norm_le k
    exact hreverse.trans hcoefficient
  have ht := ScaleTails.scale_nonneg p (k / 2)
  have htone := ScaleTails.scale_le_one p hstart (k / 2)
  have hpower : p.scale (k / 2) ^ 3 ≤ p.scale (k / 2) := by
    have hexponents : (1 : ℕ) ≤ 3 := by norm_num
    simpa only [pow_one] using pow_le_pow_of_le_one ht htone hexponents
  have hscaled := mul_le_mul_of_nonneg_left hpower hA
  have hradius := radiusLinear_error hr hstart hK k
  have htriangle := abs_sub_le ‖p.gradient k‖ (p.radius k) 1
  nlinarith

/-- Helper for sec:known-results: an even prescribed gradient has exactly its
original even radius as norm. -/
theorem gradient_norm_even (p : Parameters) (j : ℕ) (hr : 0 ≤ p.radius (2 * j)) :
    ‖p.gradient (2 * j)‖ = p.radius (2 * j) := by
  rw [PhysicalRealization.gradient_norm p _ hr, Parameters.zeta_even, one_mul]

/-- Helper for sec:known-results: the odd gradient norm plus its exact radial
correction norm equals the original odd radius. -/
theorem gradient_norm_odd_add_coefficient (p : Parameters) (j : ℕ)
    (hL : 0 ≤ p.feedbackRate) (hr : 0 ≤ p.radius (2 * j + 1)) :
    ‖p.gradient (2 * j + 1)‖ + ‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ =
      p.radius (2 * j + 1) := by
  rw [PhysicalRealization.gradient_norm p _ hr,
    ActualObjective.norm_polarCoefficient_odd p j hL hr, ActualObjective.zeta_odd_eq_exp]
  ring

/-- Helper for sec:known-results: the original radial decrements bound the
absolute difference between consecutive radii at the quartic scale. -/
theorem radiusStep_abs {p : Parameters} {D : Fin 2 → ℝ} {K c B : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B) (k : ℕ) :
    |p.radius (k + 1) - p.radius k| ≤ B * p.scale (k / 2) ^ 4 := by
  have hdecrease := (hr.strictAnti (Nat.lt_succ_self k)).le
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hdecrease)]
  exact (hr.drop k).2

/-- Helper for sec:known-results: cubic feedback and quartic radial drops give
the opposite cubic gradient-norm differences in the two original phases. -/
theorem gradientNormDifference_errors {p : Parameters} {D : Fin 2 → ℝ} {K c B A E : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B)
    (hc : ActualObjective.CoefficientEstimates p A E) (hL : 0 ≤ p.feedbackRate) (j : ℕ) :
    |‖p.gradient (2 * j + 1)‖ - ‖p.gradient (2 * j)‖ + p.feedbackRate * p.scale j ^ 3| ≤
        (B + E) * p.scale j ^ 4 ∧
      |‖p.gradient (2 * j + 2)‖ - ‖p.gradient (2 * j + 1)‖ -
          p.feedbackRate * p.scale j ^ 3| ≤ (B + E) * p.scale j ^ 4 := by
  have hhalfEven : 2 * j / 2 = j := by omega
  have hhalfOdd : (2 * j + 1) / 2 = j := by omega
  have hnext : 2 * j + 2 = 2 * (j + 1) := by omega
  have hnextOdd : 2 * j + 1 + 1 = 2 * j + 2 := by omega
  have hdropEven := radiusStep_abs hr (2 * j)
  have hdropOdd := radiusStep_abs hr (2 * j + 1)
  rw [hhalfEven] at hdropEven
  rw [hhalfOdd, hnextOdd] at hdropOdd
  have heven := gradient_norm_even p j (zero_lt_one.trans (hr.above_one _)).le
  have hodd := gradient_norm_odd_add_coefficient p j hL
    (zero_lt_one.trans (hr.above_one _)).le
  have hevenNext : ‖p.gradient (2 * j + 2)‖ = p.radius (2 * j + 2) := by
    rw [hnext]
    exact gradient_norm_even p (j + 1) (zero_lt_one.trans (hr.above_one _)).le
  have hcoefficient := hc.odd_error j
  have hevenIdentity :
      ‖p.gradient (2 * j + 1)‖ - ‖p.gradient (2 * j)‖ + p.feedbackRate * p.scale j ^ 3 =
      (p.radius (2 * j + 1) - p.radius (2 * j)) -
        (‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ - p.feedbackRate * p.scale j ^ 3) := by
    linarith
  have hoddIdentity :
      ‖p.gradient (2 * j + 2)‖ - ‖p.gradient (2 * j + 1)‖ - p.feedbackRate * p.scale j ^ 3 =
      (p.radius (2 * j + 2) - p.radius (2 * j + 1)) +
        (‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ - p.feedbackRate * p.scale j ^ 3) := by
    linarith
  constructor
  · rw [hevenIdentity]
    have htriangle := abs_sub (p.radius (2 * j + 1) - p.radius (2 * j))
      (‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ - p.feedbackRate * p.scale j ^ 3)
    nlinarith
  · rw [hoddIdentity]
    have htriangle := abs_add_le (p.radius (2 * j + 2) - p.radius (2 * j + 1))
      (‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ - p.feedbackRate * p.scale j ^ 3)
    nlinarith

/-- Helper for sec:known-results: the proved cubic differences and linear
gradient-norm bound imply both source ratio expansions with one constant. -/
theorem gradientRatio_errors {p : Parameters} {D : Fin 2 → ℝ} {K c B A E : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B)
    (hc : ActualObjective.CoefficientEstimates p A E) (hstart : 0 < p.startIndex)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hL : 0 ≤ p.feedbackRate)
    (hR : 0 ≤ 3 * (D 0 + D 1) + K + A)
    (hsmall : (3 * (D 0 + D 1) + K + A) * p.scale 0 ≤ 1 / 2) (j : ℕ) :
    |gradientRatio p (2 * j) - 1 + p.feedbackRate * p.scale j ^ 3| ≤
        2 * (B + E + p.feedbackRate * (3 * (D 0 + D 1) + K + A)) * p.scale j ^ 4 ∧
      |gradientRatio p (2 * j + 1) - 1 - p.feedbackRate * p.scale j ^ 3| ≤
        2 * (B + E + p.feedbackRate * (3 * (D 0 + D 1) + K + A)) * p.scale j ^ 4 := by
  have hden (k : ℕ) : 1 / 2 ≤ ‖p.gradient k‖ := by
    have hlinear := gradientNormLinear_error hr hc hstart hK hA k
    have hscaled := mul_le_mul_of_nonneg_left
      (ScaleTails.scale_antitone p hstart (Nat.zero_le (k / 2))) hR
    have hbound := (abs_le.mp hlinear).1
    linarith
  have hhalfEven : 2 * j / 2 = j := by omega
  have hhalfOdd : (2 * j + 1) / 2 = j := by omega
  have hnext : 2 * j + 1 + 1 = 2 * j + 2 := by omega
  have hdenEven := gradientNormLinear_error hr hc hstart hK hA (2 * j)
  have hdenOdd := gradientNormLinear_error hr hc hstart hK hA (2 * j + 1)
  rw [hhalfEven] at hdenEven
  rw [hhalfOdd] at hdenOdd
  have hdifference := gradientNormDifference_errors hr hc hL j
  have hnumEven : |‖p.gradient (2 * j + 1)‖ - ‖p.gradient (2 * j)‖ -
      (-p.feedbackRate) * p.scale j ^ 3| ≤ (B + E) * p.scale j ^ 4 := by
    simpa only [neg_mul, sub_neg_eq_add] using hdifference.1
  have heven := quotientCubicError (hden (2 * j)) (ScaleTails.scale_nonneg p j)
    hnumEven hdenEven
  have hodd := quotientCubicError (hden (2 * j + 1)) (ScaleTails.scale_nonneg p j)
    hdifference.2 hdenOdd
  constructor
  · simpa only [gradientRatio_def, neg_mul, sub_neg_eq_add, abs_neg,
      abs_of_nonneg hL] using heven
  · simpa only [gradientRatio_def, hnext, abs_of_nonneg hL] using hodd

/-- Helper for sec:known-results: infinitely late strict odd-to-even increases
exclude eventual nonincrease of a real sequence. -/
theorem not_eventually_nonincreasing_of_odd_increases (u : ℕ → ℝ)
    (hphase : ∀ᶠ j in atTop, u (2 * j + 1) < u (2 * j + 2)) :
    ¬ ∀ᶠ k in atTop, u (k + 1) ≤ u k := by
  intro hmonotone
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmonotone
  obtain ⟨M, hM⟩ := eventually_atTop.mp hphase
  let j := max N M
  have hj : M ≤ j := le_max_right _ _
  have hk : N ≤ 2 * j + 1 := by
    have hNj : N ≤ j := le_max_left _ _
    omega
  have hnext : 2 * j + 1 + 1 = 2 * j + 2 := by omega
  have hbad := hN (2 * j + 1) hk
  rw [hnext] at hbad
  exact (not_lt_of_ge hbad) (hM j hj)

/-- Helper for sec:known-results: infinitely late strict even-to-odd decreases
exclude eventual nondecrease of a real sequence. -/
theorem not_eventually_nondecreasing_of_even_decreases (u : ℕ → ℝ)
    (hphase : ∀ᶠ j in atTop, u (2 * j + 1) < u (2 * j)) :
    ¬ ∀ᶠ k in atTop, u k ≤ u (k + 1) := by
  intro hmonotone
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmonotone
  obtain ⟨M, hM⟩ := eventually_atTop.mp hphase
  let j := max N M
  have hj : M ≤ j := le_max_right _ _
  have hk : N ≤ 2 * j := by
    have hNj : N ≤ j := le_max_left _ _
    omega
  exact (not_lt_of_ge (hN (2 * j) hk)) (hM j hj)

/-- Helper for sec:known-results: positive cubic leading terms dominate the
uniform fourth-order ratio errors, forcing strict decreases and increases. -/
theorem gradientPhaseSigns_of_errors (p : Parameters) (hstart : 0 < p.startIndex)
    {C : ℝ} (hC : 0 ≤ C) (hL : 0 < p.feedbackRate)
    (hpositive : ∀ k, 0 < ‖p.gradient k‖)
    (hsmall : C * p.scale 0 ≤ p.feedbackRate / 2)
    (herror : ∀ j,
      |gradientRatio p (2 * j) - 1 + p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4 ∧
      |gradientRatio p (2 * j + 1) - 1 - p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4) :
    ∀ j, ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j)‖ ∧
      ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j + 2)‖ := by
  intro j
  have ht := ScaleTails.scale_pos p hstart j
  have hscaled := mul_le_mul_of_nonneg_left
    (ScaleTails.scale_antitone p hstart (Nat.zero_le j)) hC
  have hsmallj : C * p.scale j ≤ p.feedbackRate / 2 := hscaled.trans hsmall
  have hpower : C * p.scale j ^ 4 ≤ (p.feedbackRate / 2) * p.scale j ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hsmallj (pow_nonneg ht.le 3)
    nlinarith
  have hleading : 0 < p.feedbackRate * p.scale j ^ 3 := mul_pos hL (pow_pos ht 3)
  have hevenRatio : gradientRatio p (2 * j) < 1 := by
    have h := (abs_le.mp (herror j).1).2
    linarith
  have hoddRatio : 1 < gradientRatio p (2 * j + 1) := by
    have h := (abs_le.mp (herror j).2).1
    linarith
  rw [gradientRatio_def] at hevenRatio hoddRatio
  have hnext : 2 * j + 1 + 1 = 2 * j + 2 := by omega
  rw [hnext] at hoddRatio
  exact ⟨(div_lt_one (hpositive (2 * j))).mp hevenRatio,
    (one_lt_div (hpositive (2 * j + 1))).mp hoddRatio⟩

/-- Helper for sec:known-results (gradient-norm component): the original polar gradients
have the source opposite cubic ratio expansions with one uniform fourth-order
constant. After a single starting-index threshold, every even phase decreases
the gradient norm and every odd phase increases it; neither eventual direction
of monotonicity is possible. Constants precede every later choice of `j₀`. -/
theorem polarGradientNormOscillation :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ C > 0, ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        let p := Parameters.of j₀ νStar
        0 < p.feedbackRate ∧
        (∀ j,
          |gradientRatio p (2 * j) - 1 + p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4 ∧
          |gradientRatio p (2 * j + 1) - 1 - p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4) ∧
        (∀ j, ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j)‖ ∧
          ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j + 2)‖) ∧
        (¬ ∀ᶠ k in atTop, ‖p.gradient (k + 1)‖ ≤ ‖p.gradient k‖) ∧
        (¬ ∀ᶠ k in atTop, ‖p.gradient k‖ ≤ ‖p.gradient (k + 1)‖) := by
  obtain ⟨η, hη, hactual⟩ := ActualObjective.actualCoefficientEstimates
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, A, hA, E, hE, K, hK, c, _, B, hB, J₀, hJ₀, hall⟩ :=
    hactual νStar hnear
  let D := RadiusExpansions.radiusCoefficient νStar
  let L := 4 * baseAngle / (9 * νStar)
  let R := 3 * (D 0 + D 1) + K + A
  let C := 2 * (B + E + L * R)
  have hD := RadiusExpansions.radiusCoefficients_pos νStar hparameter
  have hDzero := hD.1
  have hDone := hD.2
  have ha := ActualObjective.baseAngle_pos
  have hν : 0 < νStar := ha.trans hnear.1
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hR : 0 < R := by
    dsimp only [R, D]
    positivity
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hcutoff : 0 < min ((1 / 2) / R) ((L / 2) / C) := by positivity
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold _ hcutoff
  refine ⟨C, hC, max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  let p := Parameters.of j₀ νStar
  have hj₀old : J₀ ≤ j₀ := (le_max_left _ _).trans hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ₀.trans_le hj₀old
  obtain ⟨hradius, hcoefficient, hfeedback⟩ := hall j₀ hj₀old
  have hpL : p.feedbackRate = L := by
    rw [Parameters.feedbackRate_def, Parameters.of_cycleParameter]
  have hsmallZero : p.scale 0 < min ((1 / 2) / R) ((L / 2) / C) :=
    hscale νStar j₀ ((le_max_right _ _).trans hj₀)
  have hsmallR : R * p.scale 0 ≤ 1 / 2 := by
    have h := (lt_div_iff₀ hR).mp (hsmallZero.trans_le (min_le_left _ _))
    nlinarith
  have hsmallC : C * p.scale 0 ≤ p.feedbackRate / 2 := by
    rw [hpL]
    have h := (lt_div_iff₀ hC).mp (hsmallZero.trans_le (min_le_right _ _))
    nlinarith
  have herrors : ∀ j,
      |gradientRatio p (2 * j) - 1 + p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4 ∧
      |gradientRatio p (2 * j + 1) - 1 - p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4 := by
    intro j
    have h := gradientRatio_errors hradius hcoefficient hstart hK.le hA.le hfeedback.le
      hR.le hsmallR j
    simpa only [p, C, R, D, L, Parameters.feedbackRate_def,
      Parameters.of_cycleParameter] using h
  have hpositive (k : ℕ) : 0 < ‖p.gradient k‖ := by
    rw [PhysicalRealization.gradient_norm p k (zero_lt_one.trans (hradius.above_one k)).le]
    exact mul_pos (PhysicalRealization.zeta_pos p k) (zero_lt_one.trans (hradius.above_one k))
  have hsigns := gradientPhaseSigns_of_errors p hstart hC.le hfeedback hpositive hsmallC herrors
  have hodd : ∀ᶠ j in atTop, ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j + 2)‖ :=
    Eventually.of_forall (fun j ↦ (hsigns j).2)
  have heven : ∀ᶠ j in atTop, ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j)‖ :=
    Eventually.of_forall (fun j ↦ (hsigns j).1)
  exact ⟨hfeedback, herrors, hsigns,
    not_eventually_nonincreasing_of_odd_increases (fun k ↦ ‖p.gradient k‖) hodd,
    not_eventually_nondecreasing_of_even_decreases (fun k ↦ ‖p.gradient k‖) heven⟩

/-- Helper for sec:known-results and eq:planar-scalar-definition: the original
gradient secant, independent of the interpolated objective's presentation. -/
def secant (p : Parameters) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  p.gradient (k + 1) - p.gradient k

/-- Helper for sec:known-results: evaluation of the actual gradient difference. -/
theorem secant_def (p : Parameters) (k : ℕ) :
    secant p k = p.gradient (k + 1) - p.gradient k := by
  rfl

/-- Helper for sec:known-results and eq:planar-scalar-definition: the physical
secant pairing `s_kᵀ y_k` of the original prescribed sequences. -/
def secantPairing (p : Parameters) (k : ℕ) : ℝ := inner ℝ (step p k) (secant p k)

/-- Helper for sec:known-results: the exact source numerator of the Xu scalar. -/
theorem secantPairing_def (p : Parameters) (k : ℕ) :
    secantPairing p k = inner ℝ (step p k) (secant p k) := by
  rfl

/-- Helper for sec:known-results: precisely Xu's original scalar, with the
actual prescribed positive step length in its denominator. -/
def xuScalar (p : Parameters) (k : ℕ) : ℝ :=
  secantPairing p k / PhysicalRealization.prescribedStepLength p k

/-- Helper for sec:known-results: evaluation of the original Xu scalar. -/
theorem xuScalar_def (p : Parameters) (k : ℕ) :
    xuScalar p k = secantPairing p k / PhysicalRealization.prescribedStepLength p k := by
  rfl

/-- Helper for eq:planar-scalar-definition and sec:known-results: the exact
normalized physical secant curvature of the prescribed polar trajectory. -/
def curvature (p : Parameters) (k : ℕ) : ℝ := secantPairing p k / ‖step p k‖ ^ 2

/-- Helper for eq:planar-scalar-definition and sec:known-results: the source
formula for `κ_k`. -/
theorem curvature_def (p : Parameters) (k : ℕ) :
    curvature p k = secantPairing p k / ‖step p k‖ ^ 2 := by
  rfl

/-- Helper for eq:planar-scalar-definition and sec:known-results: the ORIGINAL
coefficient `λ_k=κ_(k−1) det H_k` for `k≥1`; subtraction only totalizes zero. -/
def freeCoefficient (p : Parameters) (k : ℕ) : ℝ :=
  curvature p (k - 1) * (p.inverseHessian k).det

/-- Helper for eq:planar-scalar-definition and sec:known-results: evaluation
retains the original matrix `H_k` and previous source curvature index. -/
theorem freeCoefficient_def (p : Parameters) (k : ℕ) :
    freeCoefficient p k = curvature p (k - 1) * (p.inverseHessian k).det := by
  rfl

/-- Helper for sec:known-results: the actual normalized input to each phase,
using the computed original odd stage and the original cycle scale. -/
def phaseState (p : Parameters) (j : ℕ) (i : Fin 2) : ℝ × ℝ × ℝ :=
  StageFeasibility.cycleInput p.feedbackRate p.kStar i (p.scale j) (p.normalizedEvenState j)

/-- Helper for sec:known-results: the public normalized phase-input formula. -/
theorem phaseState_def (p : Parameters) (j : ℕ) (i : Fin 2) :
    phaseState p j i = StageFeasibility.cycleInput p.feedbackRate p.kStar i
      (p.scale j) (p.normalizedEvenState j) := by
  rfl

/-- Helper for sec:known-results: phase normalization is exactly the original
matrix coordinate map, in both prescribed phases. -/
theorem phaseState_eq_coordinates (p : Parameters) (hstart : 0 < p.startIndex)
    (j : ℕ) (i : Fin 2) :
    phaseState p j i = Normalized.coordinates (p.scale j) (p.matrix (2 * j + (i : ℕ))) := by
  fin_cases i
  · simpa only [phaseState_def, Fin.zero_eta, Fin.isValue, Fin.val_zero, Nat.add_zero,
      StageFeasibility.cycleInput_zero, Parameters.matrix_even] using
      StageFeasibility.normalizedEvenState_eq_coordinates p j
  · simpa only [phaseState_def, Fin.mk_one, Fin.isValue, Fin.val_one,
      Parameters.matrix_odd] using StageFeasibility.cycleInput_one_evenMatrix p j hstart

/-- Helper for sec:known-results: the true off-diagonal coordinate of the
normalized phase matrix retains its squared-scale factor. -/
theorem phaseState_offDiagonal (p : Parameters) (hstart : 0 < p.startIndex)
    (j : ℕ) (i : Fin 2) :
    (phaseState p j i).2.1 = p.scale j ^ 2 * p.matrix (2 * j + (i : ℕ)) 0 1 := by
  rw [phaseState_eq_coordinates p hstart j i, Normalized.coordinates_apply]

/-- Helper for sec:known-results: the exact normalized phase determinant is
the quartic scale times the original physical local-matrix determinant. -/
theorem phaseState_det (p : Parameters) (hstart : 0 < p.startIndex)
    (j : ℕ) (i : Fin 2) (hZ : (p.matrix (2 * j + (i : ℕ))).IsHermitian) :
    (StageFeasibility.stateMatrix (phaseState p j i)).det =
      p.scale j ^ 4 * (p.matrix (2 * j + (i : ℕ))).det := by
  have hsym : p.matrix (2 * j + (i : ℕ)) 1 0 = p.matrix (2 * j + (i : ℕ)) 0 1 := by
    simpa only [star_trivial] using hZ.apply 0 1
  rw [StageFeasibility.stateMatrix_det, phaseState_eq_coordinates p hstart j i,
    Normalized.coordinates_apply, Matrix.det_fin_two, hsym]
  ring

/-- Helper for sec:known-results: the source unreduced real rotation has
determinant exactly one. -/
theorem rotation_det (θ : ℝ) : (rotationMatrix θ).det = 1 := by
  rw [rotationMatrix_def, Matrix.det_fin_two]
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, neg_mul, sub_neg_eq_add, ← pow_two] using Real.cos_sq_add_sin_sq θ

/-- Helper for sec:known-results: the source inverse-Hessian determinant is
the reciprocal of the original local-matrix determinant. -/
theorem inverseHessian_det (p : Parameters) (k : ℕ) :
    (p.inverseHessian k).det = ((p.matrix k).det)⁻¹ := by
  rw [Parameters.inverseHessian_def, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, rotation_det, Matrix.det_nonsing_inv, Ring.inverse_eq_inv,
    one_mul, mul_one]

/-- Helper for sec:known-results: the source determinant identity keeps the
actual quartic scale and the actual normalized phase determinant. -/
theorem inverseHessian_det_phase (p : Parameters) (hstart : 0 < p.startIndex)
    (j : ℕ) (i : Fin 2) (hZ : (p.matrix (2 * j + (i : ℕ))).IsHermitian) :
    (p.inverseHessian (2 * j + (i : ℕ))).det =
      p.scale j ^ 4 / (StageFeasibility.stateMatrix (phaseState p j i)).det := by
  rw [inverseHessian_det, phaseState_det p hstart j i hZ, div_mul_eq_div_div,
    div_self (pow_ne_zero 4 (ScaleTails.scale_pos p hstart j).ne'), one_div]

/-- Helper for sec:known-results: the source rational two-cycle parameter
above the base angle makes the limiting Xu jump strictly larger than four. -/
theorem xuJumpLimit_gt_four (ν : ℝ) (hparameter : ν ∈ TwoCycle.parameterSet)
    (hν : baseAngle < ν) : 4 < 2 * cycleW ν / cycleZ ν := by
  have ha := ActualObjective.baseAngle_pos
  have hνpos : 0 < ν := ha.trans hν
  have hden : 0 < 2 * ν - baseAngle := by linarith
  have hthree : (0 : ℝ) < 3 := by norm_num
  have hZ := (TwoCycle.cycleFamily_mapsTo_positive hparameter).2.1
  have hidentity : cycleW ν - 2 * cycleZ ν =
      3 * ν * (ν - baseAngle) / (2 * ν - baseAngle) := by
    rw [cycleW_def, cycleZ_def]
    field_simp [hden.ne']
    ring
  have hgap : 0 < cycleW ν - 2 * cycleZ ν := by
    rw [hidentity]
    exact div_pos (mul_pos (mul_pos hthree hνpos)
      (sub_pos.mpr hν)) hden
  apply (lt_div_iff₀ hZ).mpr
  linarith

/-- Helper for sec:known-results: the actual reference state for each of the
two source phases, keeping both source limiting matrices unchanged. -/
def cycleState (K : ℝ) (i : Fin 2) : ℝ × ℝ × ℝ :=
  (![TwoCycle.evenState K, TwoCycle.oddState K] : Fin 2 → ℝ × ℝ × ℝ) i

/-- Helper for sec:known-results: the even source limiting state. -/
theorem cycleState_even (K : ℝ) : cycleState K 0 = TwoCycle.evenState K := by
  rfl

/-- Helper for sec:known-results: the odd source limiting state. -/
theorem cycleState_odd (K : ℝ) : cycleState K 1 = TwoCycle.oddState K := by
  rfl

/-- Helper for sec:known-results: both unchanged source limiting phase
matrices have determinant precisely `K`. -/
theorem cycleState_det (K : ℝ) (hK : K ∈ TwoCycle.normalizationSet) (i : Fin 2) :
    (StageFeasibility.stateMatrix (cycleState K i)).det = K := by
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, cycleState_even, StageFeasibility.stateMatrix_def]
      using TwoCycle.evenState_det K hK
  · simpa only [Fin.mk_one, Fin.isValue, cycleState_odd, StageFeasibility.stateMatrix_def]
      using TwoCycle.oddState_det K hK

/-- Helper for sec:known-results: both genuine limiting source phases are
regular, with positive leading and off-diagonal coordinates. -/
theorem cycleState_regular (K : ℝ) (hK : K ∈ TwoCycle.normalizationSet) (i : Fin 2) :
    StageFeasibility.regularState (cycleState K i) := by
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, cycleState_even] using
      StageFeasibility.regularState_evenState K hK
  · simpa only [Fin.mk_one, Fin.isValue, cycleState_odd] using
      StageFeasibility.regularState_oddState K hK

/-- Helper for sec:known-results: at zero scale the actual cycle input is
exactly the corresponding original source cycle state. -/
theorem cycleInput_zeroScale (L K : ℝ) (hK : K ∈ TwoCycle.normalizationSet) (i : Fin 2) :
    StageFeasibility.cycleInput L K i 0 (TwoCycle.evenState K) = cycleState K i := by
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, StageFeasibility.cycleInput_zero, cycleState_even]
  · simpa only [Fin.mk_one, Fin.isValue, StageFeasibility.cycleInput_one, cycleState_odd] using
      StageFeasibility.firstStage_zero_evenState L K K hK

/-- Helper for sec:known-results: convergence of the actual even normalized
state transports through the genuine computed stage to both source phase states. -/
theorem phaseState_tendsto (p : Parameters) (hK : p.kStar ∈ TwoCycle.normalizationSet)
    (hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar)))
    (i : Fin 2) : Tendsto (fun j ↦ phaseState p j i) atTop (𝓝 (cycleState p.kStar i)) := by
  have hregular := (StageFeasibility.regularState_def _).mp
    (StageFeasibility.regularState_evenState p.kStar hK)
  have hinput := (ScaleTails.scale_tendsto_zero p).prodMk_nhds hstate
  have hcontinuous := StageFeasibility.cycleInput_continuousAt p.feedbackRate p.kStar i
    (TwoCycle.evenState p.kStar) hregular.1.ne' hregular.2.1.ne'
  have hlimit := hcontinuous.tendsto.comp hinput
  simpa only [Function.comp_def, phaseState_def, cycleInput_zeroScale _ _ hK i] using hlimit

/-- Helper for sec:known-results: the accepted normalized cycle secants are
precisely the original actual physical `σ_k` in both phases. -/
theorem cycleSecant_prescribed (p : Parameters) (hstart : 0 < p.startIndex)
    (j : ℕ) (i : Fin 2) :
    StageFeasibility.cycleSecant p.feedbackRate p.kStar i (p.scale j)
      (p.normalizedEvenState j) = p.sigma (2 * j + (i : ℕ)) := by
  fin_cases i
  · simpa only [Fin.zero_eta, Fin.isValue, Fin.val_zero, Nat.add_zero] using
      StageFeasibility.cycleSecant_even_prescribed p j hstart
  · simpa only [Fin.mk_one, Fin.isValue, Fin.val_one] using
      StageFeasibility.cycleSecant_odd_prescribed p j hstart

/-- Helper for sec:known-results and eq:planar-scalar-definition: actual
normalized secant scalars tend to one by continuity at the source two-cycle. -/
theorem sigma_phase_tendsto_one (p : Parameters) (hstart : 0 < p.startIndex)
    (hK : p.kStar ∈ TwoCycle.normalizationSet)
    (hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar)))
    (i : Fin 2) : Tendsto (fun j ↦ p.sigma (2 * j + (i : ℕ))) atTop (𝓝 1) := by
  have hregular := (StageFeasibility.regularState_def _).mp
    (StageFeasibility.regularState_evenState p.kStar hK)
  have hnextC : (Normalized.leadingStage (Normalized.limitAngle 0)
      (TwoCycle.evenState p.kStar)).2.1 ≠ 0 := by
    rw [Normalized.limitAngle_zero, TwoCycle.evenToOdd p.kStar hK]
    exact ((StageFeasibility.regularState_def _).mp
      (StageFeasibility.regularState_oddState p.kStar hK)).2.1.ne'
  have hcontinuous := StageFeasibility.cycleSecant_continuousAt p.feedbackRate p.kStar i
    (TwoCycle.evenState p.kStar) hregular.1.ne' hregular.2.1.ne' hnextC
  have hlimit := hcontinuous.tendsto.comp ((ScaleTails.scale_tendsto_zero p).prodMk_nhds hstate)
  simpa only [Function.comp_def, cycleSecant_prescribed p hstart,
    StageFeasibility.cycleSecant_at_zero] using hlimit

/-- Helper for sec:known-results and eq:planar-scalar-definition: the original
physical slopes tend to zero, because their actual normalized phase slopes
have finite limits and retain the squared scale factor. -/
theorem omega_phase_tendsto_zero (p : Parameters) (hstart : 0 < p.startIndex)
    (hK : p.kStar ∈ TwoCycle.normalizationSet)
    (hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar)))
    (i : Fin 2) : Tendsto (fun j ↦ p.omega (2 * j + (i : ℕ))) atTop (𝓝 0) := by
  have hphase := phaseState_tendsto p hK hstate i
  have hC : (cycleState p.kStar i).2.1 ≠ 0 :=
    ((StageFeasibility.regularState_def _).mp (cycleState_regular p.kStar hK i)).2.1.ne'
  have hslope : Tendsto (fun j ↦ Normalized.slope (phaseState p j i)) atTop
      (𝓝 (Normalized.slope (cycleState p.kStar i))) := by
    simpa only [Normalized.slope_def, Pi.div_def] using
      hphase.snd_nhds.snd_nhds.div hphase.snd_nhds.fst_nhds hC
  have hproduct := ((ScaleTails.scale_tendsto_zero p).pow 2).mul hslope
  have htwo : (2 : ℕ) ≠ 0 := by norm_num
  simpa only [Function.comp_def, zero_pow htwo, zero_mul,
    RadiusExpansions.omega_prescribed p _ hstart i,
    RadiusExpansions.cycleSlope_def, phaseState_def] using hproduct

/-- Helper for sec:known-results: actual normalized determinants tend to the
source value `KStar`, through the continuous determinant polynomial. -/
theorem phaseState_det_tendsto (p : Parameters) (hK : p.kStar ∈ TwoCycle.normalizationSet)
    (hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar)))
    (i : Fin 2) :
    Tendsto (fun j ↦ (StageFeasibility.stateMatrix (phaseState p j i)).det)
      atTop (𝓝 p.kStar) := by
  have hcontinuous : Continuous (fun x : ℝ × ℝ × ℝ ↦
      (StageFeasibility.stateMatrix x).det) := by
    simp_rw [StageFeasibility.stateMatrix_det]
    fun_prop
  have hlimit := hcontinuous.continuousAt.tendsto.comp (phaseState_tendsto p hK hstate i)
  simpa only [Function.comp_def, cycleState_det _ hK i] using hlimit

/-- Helper for sec:known-results: the actual prescribed trajectory has both
source normalized phase limits, secant limit one, slope limit zero, and normalized
determinant limit `KStar`. The neighborhood and threshold come from the accepted
genuine continuation theorem, rather than assumptions about the target limits. -/
theorem polarNormalizedPhaseLimits :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        let p := Parameters.of j₀ νStar
        ∀ i : Fin 2,
          Tendsto (fun j ↦ phaseState p j i) atTop (𝓝 (cycleState (cycleK νStar) i)) ∧
          Tendsto (fun j ↦ p.sigma (2 * j + (i : ℕ))) atTop (𝓝 1) ∧
          Tendsto (fun j ↦ p.omega (2 * j + (i : ℕ))) atTop (𝓝 0) ∧
          Tendsto (fun j ↦ (StageFeasibility.stateMatrix (phaseState p j i)).det)
            atTop (𝓝 (cycleK νStar)) := by
  obtain ⟨η₀, hη₀, hactual⟩ := Continuation.polarLimits
  have ha := ActualObjective.baseAngle_pos
  have hquarter : 0 < baseAngle / 4 := by positivity
  refine ⟨min η₀ (baseAngle / 4), lt_min hη₀ hquarter, ?_⟩
  intro νStar hnear
  have hnear₀ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₀) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hparameter : νStar ∈ TwoCycle.parameterSet := by
    rw [TwoCycle.parameterSet_def]
    have hupper := hnear.2.trans_le (add_le_add le_rfl (min_le_right η₀ (baseAngle / 4)))
    constructor
    · linarith [hnear.1]
    · linarith
  obtain ⟨J, hJ, hlimits⟩ := hactual νStar hnear₀
  refine ⟨hparameter, J, hJ, ?_⟩
  intro j₀ hj₀
  dsimp only
  let p := Parameters.of j₀ νStar
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ.trans_le hj₀
  have hpK : p.kStar = cycleK νStar := by
    rw [Parameters.kStar_def, Parameters.of_cycleParameter]
  have hK : p.kStar ∈ TwoCycle.normalizationSet := by
    rw [hpK]
    exact TwoCycle.cycleK_bijOn_parameterSet.mapsTo hparameter
  have hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar)) := by
    simpa only [hpK] using (hlimits j₀ hj₀).2.2
  intro i
  have hphase := phaseState_tendsto p hK hstate i
  have hdet := phaseState_det_tendsto p hK hstate i
  rw [hpK] at hphase hdet
  exact ⟨hphase, sigma_phase_tendsto_one p hstart hK hstate i,
    omega_phase_tendsto_zero p hstart hK hstate i, hdet⟩

/-- Helper for sec:known-results and eq:planar-scalar-definition: the exact
source physical pairing factors through the original local scalar `σ_k`. -/
theorem secantPairing_eq (p : Parameters) (hstart : 0 < p.startIndex) (k : ℕ)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) (hW : p.radiusRatio k ≠ 0) :
    secantPairing p k = (p.radius (k + 1) * Real.sin (p.angleIncrement k)) ^ 2 * p.sigma k := by
  rw [secantPairing_def, step_def, secant_def, WolfeRatios.inner_eq_dot]
  simpa only [PhysicalRealization.chord_def, PhysicalRealization.secant_def] using
    PhysicalRealization.prescribed_secant_pairing p k hstart hr hW

/-- Helper for sec:known-results and eq:planar-scalar-definition: the source
common chord factor gives the exact squared step norm with `1+ω_k²`. -/
theorem step_norm_sq (p : Parameters) (k : ℕ)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) (hW : p.radiusRatio k ≠ 0) :
    ‖step p k‖ ^ 2 = (p.radius (k + 1) * Real.sin (p.angleIncrement k)) ^ 2 *
      (1 + p.omega k ^ 2) := by
  have hcoordinates : WithLp.ofLp (step p k) = rotationMatrix (p.angle k) *ᵥ
      ((p.radius (k + 1) * Real.sin (p.angleIncrement k)) • p.stepV k) := by
    rw [step_def, Parameters.point_def, Parameters.point_def,
      PhysicalRealization.angle_succ, Parameters.stepV_def]
    exact PhysicalRealization.chord_eq _ _ _ _ _ (PhysicalRealization.radius_balance p k hr hW)
  have hnorm : ‖step p k‖ =
      ‖(WithLp.toLp 2 ((p.radius (k + 1) * Real.sin (p.angleIncrement k)) • p.stepV k) :
        EuclideanSpace ℝ (Fin 2))‖ := by
    have h := congrArg (fun v : Fin 2 → ℝ ↦
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖) hcoordinates
    simpa only [WithLp.toLp_ofLp,
      Matrix.norm_toLp_mulVec_eq_of_mem_orthogonalGroup _
        (PhysicalRealization.rotation_orthogonal (p.angle k))] using h
  rw [hnorm, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Parameters.stepV_def, stepVOf_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← Parameters.omega_def]
  ring

/-- Helper for eq:planar-scalar-definition and sec:known-results: the actual
polar normalized secant curvature is exactly `σ_k/(1+ω_k²)`. -/
theorem curvature_eq_sigma_div (p : Parameters) (hstart : 0 < p.startIndex) (k : ℕ)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) (hW : p.radiusRatio k ≠ 0)
    (hradius : 0 < p.radius (k + 1)) :
    curvature p k = p.sigma k / (1 + p.omega k ^ 2) := by
  have hfactor : (p.radius (k + 1) * Real.sin (p.angleIncrement k)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero hradius.ne'
      (PhysicalRealization.angleIncrement_sin_pos p hstart k).ne')
  rw [curvature_def, secantPairing_eq p hstart k hr hW, step_norm_sq p k hr hW]
  exact mul_div_mul_left _ _ hfactor

/-- Helper for sec:known-results: exact cancellation of the source step
length in Xu's scalar retains the original radii, local secant and matrix entries. -/
theorem xuScalar_eq (p : Parameters) (hstart : 0 < p.startIndex) (k : ℕ)
    (hZ : (p.matrix k).PosDef) (hC : 0 < p.matrix k 0 1) (hW : 0 < p.radiusRatio k)
    (hr : p.radius (k + 1) = p.radius k / p.radiusRatio k) :
    xuScalar p k = p.zeta k * p.radius k * p.radius (k + 1) * Real.sin (p.angleIncrement k) *
      p.sigma k * p.matrix k 0 1 / (p.matrix k).det := by
  have hsin := (PhysicalRealization.angleIncrement_sin_pos p hstart k).ne'
  have hζ := (PhysicalRealization.zeta_pos p k).ne'
  have hbalance := PhysicalRealization.radius_balance p k hr hW.ne'
  rw [← Parameters.radiusRatio_def] at hbalance
  rw [xuScalar_def, secantPairing_eq p hstart k hr hW.ne',
    PhysicalRealization.prescribedStepLength_def, ← hbalance]
  field_simp [hZ.det_pos.ne', hC.ne', hW.ne', hsin, hζ]

/-- Helper for sec:known-results: dividing Xu's exact physical scalar by
the quartic scale gives its source normalized phase expression. -/
theorem xuScalar_phase_normalization (p : Parameters) (hstart : 0 < p.startIndex)
    (j : ℕ) (i : Fin 2) (hZ : (p.matrix (2 * j + (i : ℕ))).PosDef)
    (hC : 0 < p.matrix (2 * j + (i : ℕ)) 0 1)
    (hW : 0 < p.radiusRatio (2 * j + (i : ℕ)))
    (hr : p.radius (2 * j + (i : ℕ) + 1) =
      p.radius (2 * j + (i : ℕ)) / p.radiusRatio (2 * j + (i : ℕ))) :
    xuScalar p (2 * j + (i : ℕ)) / p.scale j ^ 4 =
      p.zeta (2 * j + (i : ℕ)) * p.radius (2 * j + (i : ℕ)) *
        p.radius (2 * j + (i : ℕ) + 1) * Normalized.sinFactor i (p.scale j) *
        p.sigma (2 * j + (i : ℕ)) *
          ((phaseState p j i).2.1 / (StageFeasibility.stateMatrix (phaseState p j i)).det) := by
  rw [xuScalar_eq p hstart _ hZ hC hW hr, phaseState_offDiagonal p hstart j i,
    phaseState_det p hstart j i hZ.isHermitian, ← Normalized.stageAngle_scale p i j hstart,
    WolfeRatios.sin_stageAngle_eq i (p.scale j) (ScaleTails.scale_pos p hstart j)]
  field_simp [(ScaleTails.scale_pos p hstart j).ne', hZ.det_pos.ne']

/-- Helper for sec:known-results: each fixed source phase and its successor
visit arbitrarily large indices of the original full sequence. -/
theorem phaseIndices_tendsto (r : ℕ) : Tendsto (fun j : ℕ ↦ 2 * j + r) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_ge_atTop N] with j hj
  omega

/-- Helper for sec:known-results: genuine even-state convergence makes the
exact cubic feedback multipliers tend to one on the full original sequence. -/
theorem zeta_tendsto_one (p : Parameters) (hK : p.kStar ∈ TwoCycle.normalizationSet)
    (hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar))) :
    Tendsto p.zeta atTop (𝓝 1) := by
  have hregular := (StageFeasibility.regularState_def _).mp
    (StageFeasibility.regularState_evenState p.kStar hK)
  have hcontinuous := (WolfeRatios.feedback_analyticAt p.feedbackRate p.kStar
    (TwoCycle.evenState p.kStar) hregular.1.ne').continuousAt
  have hzero : Normalized.feedback p.feedbackRate p.kStar 0 (TwoCycle.evenState p.kStar) = 1 := by
    rw [Normalized.feedback_def]
    norm_num
  have hodd : Tendsto (fun j ↦ p.zeta (2 * j + 1)) atTop (𝓝 1) := by
    have h := hcontinuous.tendsto.comp ((ScaleTails.scale_tendsto_zero p).prodMk_nhds hstate)
    simpa only [Function.comp_def, WolfeRatios.feedback_prescribed, hzero] using h
  have heven : Tendsto (fun j ↦ p.zeta (2 * j)) atTop (𝓝 1) := by
    simpa only [Parameters.zeta_even] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  exact tendsto_of_tendsto_even_odd heven hodd

/-- Helper for sec:known-results: the source limiting normalization is
positive whenever it belongs to the accepted two-cycle branch. -/
theorem normalization_pos {K : ℝ} (hK : K ∈ TwoCycle.normalizationSet) : 0 < K := by
  have h := (TwoCycle.evenState_mapsTo_positive hK).1
  simpa only [Set.mem_Ioi, TwoCycle.evenState_firstDiagonal] using h

/-- Helper for sec:known-results: the original normalized off-diagonal
entries divided by the source determinant are exactly `wStar` and `zStar`. -/
theorem cycleState_offDiagonal_div (ν : ℝ) (hν : ν ∈ TwoCycle.parameterSet) (i : Fin 2) :
    (cycleState (cycleK ν) i).2.1 / cycleK ν =
      (![cycleW ν, cycleZ ν] : Fin 2 → ℝ) i := by
  have hK : 0 < cycleK ν := by
    simpa only [Set.mem_Ioi] using (TwoCycle.cycleFamily_mapsTo_positive hν).1
  have hinverse := TwoCycle.inverseParameter_invOn.1 hν
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, cycleState_even, TwoCycle.evenState_apply,
      hinverse, Matrix.cons_val_zero]
    field_simp [hK.ne']
  · simp only [Fin.mk_one, Fin.isValue, cycleState_odd, TwoCycle.oddState_apply,
      hinverse, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp [hK.ne']

/-- Helper for sec:known-results and eq:planar-scalar-definition: the exact
physical source curvatures tend to one on the full original index sequence. -/
theorem curvature_tendsto_one {p : Parameters} {D : Fin 2 → ℝ} {K c B : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B) (hstart : 0 < p.startIndex)
    (hK : p.kStar ∈ TwoCycle.normalizationSet)
    (hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar))) :
    Tendsto (curvature p) atTop (𝓝 1) := by
  have hidentity (k : ℕ) : curvature p k = p.sigma k / (1 + p.omega k ^ 2) :=
    curvature_eq_sigma_div p hstart k (hr.recurrence k)
      (zero_lt_one.trans (hr.factor_above_one k)).ne'
      (zero_lt_one.trans (hr.above_one (k + 1)))
  have htwo : (2 : ℕ) ≠ 0 := by norm_num
  have hphase (i : Fin 2) : Tendsto (fun j ↦ curvature p (2 * j + (i : ℕ))) atTop (𝓝 1) := by
    have homega := omega_phase_tendsto_zero p hstart hK hstate i
    have hden : Tendsto (fun j ↦ 1 + p.omega (2 * j + (i : ℕ)) ^ 2) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add
        (homega.pow 2)
      simpa only [zero_pow htwo, add_zero] using h
    have h := (sigma_phase_tendsto_one p hstart hK hstate i).div hden one_ne_zero
    simpa only [hidentity, Pi.div_def, div_one] using h
  apply tendsto_of_tendsto_even_odd
  · simpa only [Fin.val_zero, Nat.add_zero] using hphase 0
  · simpa only [Fin.val_one] using hphase 1

/-- Helper for sec:known-results: the exact normalized determinant formula
and genuine normalized phase limits give the leading physical determinant order. -/
theorem inverseHessian_det_normalized_tendsto (p : Parameters) (hstart : 0 < p.startIndex)
    (hK : p.kStar ∈ TwoCycle.normalizationSet)
    (hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar)))
    (hZ : ∀ k, (p.matrix k).PosDef) :
    Tendsto (fun k ↦ (p.inverseHessian k).det / p.scale (k / 2) ^ 4)
      atTop (𝓝 (1 / p.kStar)) := by
  have hKne := (normalization_pos hK).ne'
  have hnormalized (j : ℕ) (i : Fin 2) :
      (p.inverseHessian (2 * j + (i : ℕ))).det / p.scale j ^ 4 =
        1 / (StageFeasibility.stateMatrix (phaseState p j i)).det := by
    have hmatrix := hZ (2 * j + (i : ℕ))
    rw [inverseHessian_det_phase p hstart j i hmatrix.isHermitian,
      phaseState_det p hstart j i hmatrix.isHermitian]
    field_simp [(ScaleTails.scale_pos p hstart j).ne', hmatrix.det_pos.ne']
  have hphase (i : Fin 2) :
      Tendsto (fun j ↦ (p.inverseHessian (2 * j + (i : ℕ))).det / p.scale j ^ 4)
        atTop (𝓝 (1 / p.kStar)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).div
      (phaseState_det_tendsto p hK hstate i) hKne
    simpa only [hnormalized, Pi.div_def] using h
  have hhalfEven (j : ℕ) : 2 * j / 2 = j := by omega
  have hhalfOdd (j : ℕ) : (2 * j + 1) / 2 = j := by omega
  apply tendsto_of_tendsto_even_odd
  · simpa only [Fin.val_zero, Nat.add_zero, hhalfEven] using hphase 0
  · simpa only [Fin.val_one, hhalfOdd] using hphase 1

/-- Helper for sec:known-results and eq:planar-scalar-definition: the ORIGINAL
coefficient with previous curvature and current matrix has the same quartic
leading order, including its harmless totalization at index zero. -/
theorem freeCoefficient_normalized_tendsto {p : Parameters} {D : Fin 2 → ℝ} {K c B : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B) (hstart : 0 < p.startIndex)
    (hK : p.kStar ∈ TwoCycle.normalizationSet)
    (hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar)))
    (hZ : ∀ k, (p.matrix k).PosDef) :
    Tendsto (fun k ↦ freeCoefficient p k / p.scale (k / 2) ^ 4)
      atTop (𝓝 (1 / p.kStar)) := by
  have hcurvature := curvature_tendsto_one hr hstart hK hstate
  have hshift : Tendsto (fun k ↦ curvature p (k + 1 - 1)) atTop (𝓝 1) := by
    simpa only [Nat.add_sub_cancel] using hcurvature
  have hprevious : Tendsto (fun k ↦ curvature p (k - 1)) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat 1).mp hshift
  have hproduct := hprevious.mul (inverseHessian_det_normalized_tendsto p hstart hK hstate hZ)
  simpa only [freeCoefficient_def, mul_div_assoc, one_mul] using hproduct

/-- Helper for sec:known-results: a normalized positive-scale limit with a
nonzero leading coefficient is precisely the source asymptotic equivalence. -/
theorem equivalent_of_normalized_limit {f t : ℕ → ℝ} {C : ℝ}
    (ht : ∀ n, 0 < t n) (hC : C ≠ 0)
    (hlimit : Tendsto (fun n ↦ f n / t n) atTop (𝓝 C)) :
    f ~[atTop] (fun n ↦ C * t n) := by
  have hnonzero : ∀ᶠ n in atTop, C * t n ≠ 0 :=
    Eventually.of_forall (fun n ↦ mul_ne_zero hC (ht n).ne')
  apply (Asymptotics.isEquivalent_iff_tendsto_one hnonzero).mpr
  have hquotient (n : ℕ) : f n / (C * t n) = (f n / t n) / C := by
    rw [div_div, mul_comm]
  simpa only [Pi.div_def, hquotient, div_self hC] using hlimit.div_const C

/-- Helper for sec:known-results: the proved uniform fourth-order inequalities
are precisely both source big-O ratio expansions, with the SAME chosen constant. -/
theorem gradientRatio_isBigOWith (p : Parameters) (C : ℝ)
    (herror : ∀ j,
      |gradientRatio p (2 * j) - 1 + p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4 ∧
      |gradientRatio p (2 * j + 1) - 1 - p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4) :
    Asymptotics.IsBigOWith C atTop
      (fun j ↦ gradientRatio p (2 * j) - (1 - p.feedbackRate * p.scale j ^ 3))
      (fun j ↦ p.scale j ^ 4) ∧
    Asymptotics.IsBigOWith C atTop
      (fun j ↦ gradientRatio p (2 * j + 1) - (1 + p.feedbackRate * p.scale j ^ 3))
      (fun j ↦ p.scale j ^ 4) := by
  constructor
  · apply Asymptotics.IsBigOWith.of_bound
    filter_upwards with j
    have hidentity : gradientRatio p (2 * j) - (1 - p.feedbackRate * p.scale j ^ 3) =
        gradientRatio p (2 * j) - 1 + p.feedbackRate * p.scale j ^ 3 := by ring
    simpa only [hidentity, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (ScaleTails.scale_nonneg p j) 4)] using (herror j).1
  · apply Asymptotics.IsBigOWith.of_bound
    filter_upwards with j
    have hidentity : gradientRatio p (2 * j + 1) - (1 + p.feedbackRate * p.scale j ^ 3) =
        gradientRatio p (2 * j + 1) - 1 - p.feedbackRate * p.scale j ^ 3 := by ring
    simpa only [hidentity, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (ScaleTails.scale_nonneg p j) 4)] using (herror j).2

/-- Helper for sec:known-results: the exact source leading Xu coefficient
selects the even value `2awStar` and the odd value `azStar`. -/
def xuLeadingCoefficient (ν : ℝ) (i : Fin 2) : ℝ :=
  Normalized.limitAngle i * (![cycleW ν, cycleZ ν] : Fin 2 → ℝ) i

/-- Helper for sec:known-results: the source phase coefficient formula. -/
theorem xuLeadingCoefficient_def (ν : ℝ) (i : Fin 2) :
    xuLeadingCoefficient ν i = Normalized.limitAngle i *
      (![cycleW ν, cycleZ ν] : Fin 2 → ℝ) i := by
  rfl

/-- Helper for sec:known-results: the even source leading coefficient is exactly `2awStar`. -/
theorem xuLeadingCoefficient_even (ν : ℝ) :
    xuLeadingCoefficient ν 0 = 2 * baseAngle * cycleW ν := by
  rw [xuLeadingCoefficient_def, Normalized.limitAngle_zero]
  rfl

/-- Helper for sec:known-results: the odd source leading coefficient is exactly `azStar`. -/
theorem xuLeadingCoefficient_odd (ν : ℝ) : xuLeadingCoefficient ν 1 = baseAngle * cycleZ ν := by
  rw [xuLeadingCoefficient_def, Normalized.limitAngle_one]
  rfl

/-- Helper for sec:known-results: exact physical normalization and the
genuine normalized-state limit give Xu's scalar leading coefficient in either phase. -/
theorem xuScalar_phase_tendsto {p : Parameters} {D : Fin 2 → ℝ} {K c B : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B) (hstart : 0 < p.startIndex)
    (hK : p.kStar ∈ TwoCycle.normalizationSet)
    (hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar)))
    (hfeasible : ∀ k, (p.matrix k).PosDef ∧ 0 < p.matrix k 0 1 ∧
      0 < p.sigma k ∧ 0 < p.radiusRatio k) (i : Fin 2) :
    Tendsto (fun j ↦ xuScalar p (2 * j + (i : ℕ)) / p.scale j ^ 4) atTop
      (𝓝 (Normalized.limitAngle i * ((cycleState p.kStar i).2.1 / p.kStar))) := by
  have hphase := phaseState_tendsto p hK hstate i
  have hζ := (zeta_tendsto_one p hK hstate).comp (phaseIndices_tendsto (i : ℕ))
  have hradius := hr.tendsto_one.comp (phaseIndices_tendsto (i : ℕ))
  have hradiusNext : Tendsto (fun j ↦ p.radius (2 * j + (i : ℕ) + 1)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Nat.add_assoc] using
      hr.tendsto_one.comp (phaseIndices_tendsto ((i : ℕ) + 1))
  have hsin := (Normalized.sinFactor_analyticAt i).continuousAt.tendsto.comp
    (ScaleTails.scale_tendsto_zero p)
  have hσ := sigma_phase_tendsto_one p hstart hK hstate i
  have hratio := hphase.snd_nhds.fst_nhds.div (phaseState_det_tendsto p hK hstate i)
    (normalization_pos hK).ne'
  have hproduct := ((((hζ.mul hradius).mul hradiusNext).mul hsin).mul hσ).mul hratio
  have hnormalized (j : ℕ) := xuScalar_phase_normalization p hstart j i
    (hfeasible _).1 (hfeasible _).2.1 (hfeasible _).2.2.2 (hr.recurrence _)
  simpa only [hnormalized, Pi.div_def, Function.comp_def, WolfeRatios.sinFactor_zero,
    one_mul, mul_one] using hproduct


/-- Helper for sec:known-results: the actual source step length and physical
secant pairing make Xu's scalar positive at every index. -/
theorem xuScalar_pos {p : Parameters} {D : Fin 2 → ℝ} {K c B : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B) (hstart : 0 < p.startIndex)
    (hfeasible : ∀ k, (p.matrix k).PosDef ∧ 0 < p.matrix k 0 1 ∧
      0 < p.sigma k ∧ 0 < p.radiusRatio k) (k : ℕ) : 0 < xuScalar p k := by
  have hσ := (hfeasible k).2.2.1
  have hW := (hfeasible k).2.2.2
  have hpair : 0 < secantPairing p k := by
    rw [secantPairing_eq p hstart k (hr.recurrence k) hW.ne']
    exact mul_pos (sq_pos_of_pos (mul_pos (zero_lt_one.trans (hr.above_one (k + 1)))
      (PhysicalRealization.angleIncrement_sin_pos p hstart k))) hσ
  rw [xuScalar_def]
  exact div_pos hpair (PhysicalRealization.prescribedStepLength_pos p k hstart
    (hfeasible k).1 (hfeasible k).2.1 hW)

/-- Helper for sec:known-results: consecutive quartic scales have ratio one
in the limit, using the exact analytic scale continuation. -/
theorem scaleQuarticQuotient_tendsto_one (p : Parameters) (hstart : 0 < p.startIndex) :
    Tendsto (fun j ↦ p.scale (j + 1) ^ 4 / p.scale j ^ 4) atTop (𝓝 1) := by
  have hzero : Normalized.rescaleFactor 0 = 1 := by
    rw [Normalized.rescaleFactor_def, Normalized.unitRoot_def]
    norm_num
  have hidentity (j : ℕ) : p.scale (j + 1) ^ 4 / p.scale j ^ 4 =
      Normalized.rescaleFactor (p.scale j) ^ 2 := by
    rw [Normalized.rescaleFactor_eq_div_sq _ (ScaleTails.scale_pos p hstart j),
      Normalized.nextScale_scale p j hstart, ← div_pow]
    ring
  have h := ((Normalized.rescaleFactor_analyticAt.continuousAt.tendsto.comp
    (ScaleTails.scale_tendsto_zero p)).pow 2)
  simpa only [hidentity, Function.comp_def, hzero, one_pow] using h

/-- Helper for sec:known-results: the ratio of the NEXT even Xu scalar to
the current odd scalar follows from their exact normalized phase limits and
the original next-scale ratio. -/
theorem xuScalar_jump_tendsto (p : Parameters) (hstart : 0 < p.startIndex) {A B : ℝ}
    (hB : B ≠ 0) (hodd : ∀ j, xuScalar p (2 * j + 1) ≠ 0)
    (hevenLimit : Tendsto (fun j ↦ xuScalar p (2 * j) / p.scale j ^ 4) atTop (𝓝 A))
    (hoddLimit : Tendsto (fun j ↦ xuScalar p (2 * j + 1) / p.scale j ^ 4) atTop (𝓝 B)) :
    Tendsto (fun j ↦ xuScalar p (2 * j + 2) / xuScalar p (2 * j + 1))
      atTop (𝓝 (A / B)) := by
  have hshift := hevenLimit.comp (tendsto_add_atTop_nat 1)
  have hquotient := hshift.div hoddLimit hB
  have hproduct := hquotient.mul (scaleQuarticQuotient_tendsto_one p hstart)
  have hidentity (j : ℕ) : xuScalar p (2 * j + 2) / xuScalar p (2 * j + 1) =
      ((xuScalar p (2 * (j + 1)) / p.scale (j + 1) ^ 4) /
        (xuScalar p (2 * j + 1) / p.scale j ^ 4)) *
          (p.scale (j + 1) ^ 4 / p.scale j ^ 4) := by
    have hindex : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [hindex]
    field_simp [(ScaleTails.scale_pos p hstart j).ne',
      (ScaleTails.scale_pos p hstart (j + 1)).ne', hodd j]
  simpa only [hidentity, Pi.div_def, Function.comp_def, mul_one] using hproduct

/-- Helper for sec:known-results: an asymptotic Xu jump larger than one
forces infinitely late strict increases, excluding eventual decrease. -/
theorem xuScalar_not_eventually_nonincreasing (p : Parameters) {Q : ℝ} (hQ : 1 < Q)
    (hpositive : ∀ k, 0 < xuScalar p k)
    (hlimit : Tendsto (fun j ↦ xuScalar p (2 * j + 2) / xuScalar p (2 * j + 1))
      atTop (𝓝 Q)) :
    ¬ ∀ᶠ k in atTop, xuScalar p (k + 1) ≤ xuScalar p k := by
  have hlarge := hlimit.eventually (eventually_gt_nhds hQ)
  have hphase : ∀ᶠ j in atTop, xuScalar p (2 * j + 1) < xuScalar p (2 * j + 2) := by
    filter_upwards [hlarge] with j hj
    exact (one_lt_div (hpositive (2 * j + 1))).mp hj
  exact not_eventually_nonincreasing_of_odd_increases (xuScalar p) hphase

/-- Helper for sec:known-results and eq:planar-scalar-definition: the actual
prescribed source family has the original secant-curvature limit one, both Xu
leading coefficients and its jump larger than four, and the exact quartic
determinant and ORIGINAL free-coefficient asymptotic equivalents. All trajectory
feasibility and limits are discharged by genuine continuation and radius products. -/
theorem polarScalarAsymptotics :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        let p := Parameters.of j₀ νStar
        (∀ k, curvature p k = p.sigma k / (1 + p.omega k ^ 2)) ∧
        Tendsto (curvature p) atTop (𝓝 1) ∧
        ((fun k ↦ (p.inverseHessian k).det) ~[atTop]
          (fun k ↦ p.scale (k / 2) ^ 4 / p.kStar)) ∧
        (freeCoefficient p ~[atTop] (fun k ↦ p.scale (k / 2) ^ 4 / p.kStar)) ∧
        (∀ i : Fin 2,
          Tendsto (fun j ↦ xuScalar p (2 * j + (i : ℕ)) / p.scale j ^ 4)
            atTop (𝓝 (xuLeadingCoefficient νStar i)) ∧
          ((fun j ↦ xuScalar p (2 * j + (i : ℕ))) ~[atTop]
            (fun j ↦ xuLeadingCoefficient νStar i * p.scale j ^ 4))) ∧
        Tendsto (fun j ↦ xuScalar p (2 * j + 2) / xuScalar p (2 * j + 1))
          atTop (𝓝 (2 * cycleW νStar / cycleZ νStar)) ∧
        4 < 2 * cycleW νStar / cycleZ νStar ∧
        (¬ ∀ᶠ k in atTop, xuScalar p (k + 1) ≤ xuScalar p k) := by
  obtain ⟨ηn, hηn, hnormalized⟩ := Continuation.polarLimits
  obtain ⟨ηc, hηc, hcontinued⟩ := Continuation.polarContinuation
  obtain ⟨ηr, hηr, hradii⟩ := RadiusProducts.polarRadiusProducts
  refine ⟨min ηn (min ηc ηr), lt_min hηn (lt_min hηc hηr), ?_⟩
  intro νStar hnear
  have hnearN : νStar ∈ Set.Ioo baseAngle (baseAngle + ηn) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hηcle : min ηn (min ηc ηr) ≤ ηc := (min_le_right _ _).trans (min_le_left _ _)
  have hηrle : min ηn (min ηc ηr) ≤ ηr := (min_le_right _ _).trans (min_le_right _ _)
  have hnearC : νStar ∈ Set.Ioo baseAngle (baseAngle + ηc) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl hηcle)⟩
  have hnearR : νStar ∈ Set.Ioo baseAngle (baseAngle + ηr) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl hηrle)⟩
  obtain ⟨Jn, hJn, hnorm⟩ := hnormalized νStar hnearN
  obtain ⟨hparameter, _, _, _, _, Jc, _, hcont⟩ := hcontinued νStar hnearC
  obtain ⟨_, K, _, c, _, B, _, Jr, _, hradiusAll⟩ := hradii νStar hnearR
  refine ⟨hparameter, max Jn (max Jc Jr), hJn.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  dsimp only
  let p := Parameters.of j₀ νStar
  have hjN : Jn ≤ j₀ := (le_max_left _ _).trans hj₀
  have hjC : Jc ≤ j₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hj₀
  have hjR : Jr ≤ j₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJn.trans_le hjN
  have hpK : p.kStar = cycleK νStar := by
    rw [Parameters.kStar_def, Parameters.of_cycleParameter]
  have hK : p.kStar ∈ TwoCycle.normalizationSet := by
    rw [hpK]
    exact TwoCycle.cycleK_bijOn_parameterSet.mapsTo hparameter
  have hstate : Tendsto p.normalizedEvenState atTop (𝓝 (TwoCycle.evenState p.kStar)) := by
    simpa only [hpK] using (hnorm j₀ hjN).2.2
  have hradius : RadiusProducts.RadiusEstimates p
      (RadiusExpansions.radiusCoefficient νStar) K c B := hradiusAll j₀ hjR
  have hfeasible : ∀ k, (p.matrix k).PosDef ∧ 0 < p.matrix k 0 1 ∧
      0 < p.sigma k ∧ 0 < p.radiusRatio k := (hcont j₀ hjC).2
  have hZ (k : ℕ) : (p.matrix k).PosDef := (hfeasible k).1
  have hcurvatureIdentity (k : ℕ) : curvature p k = p.sigma k / (1 + p.omega k ^ 2) :=
    curvature_eq_sigma_div p hstart k (hradius.recurrence k) (hfeasible k).2.2.2.ne'
      (zero_lt_one.trans (hradius.above_one (k + 1)))
  have hcurvature := curvature_tendsto_one hradius hstart hK hstate
  have hdetNormalized := inverseHessian_det_normalized_tendsto p hstart hK hstate hZ
  have hfreeNormalized := freeCoefficient_normalized_tendsto hradius hstart hK hstate hZ
  have hscalePositive (k : ℕ) : 0 < p.scale (k / 2) ^ 4 :=
    pow_pos (ScaleTails.scale_pos p hstart (k / 2)) 4
  have hcoefficientPositive : 0 < 1 / p.kStar := one_div_pos.mpr (normalization_pos hK)
  have hdetEquivalent : (fun k ↦ (p.inverseHessian k).det) ~[atTop]
      (fun k ↦ p.scale (k / 2) ^ 4 / p.kStar) := by
    have h := equivalent_of_normalized_limit hscalePositive hcoefficientPositive.ne' hdetNormalized
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h
  have hfreeEquivalent : freeCoefficient p ~[atTop]
      (fun k ↦ p.scale (k / 2) ^ 4 / p.kStar) := by
    have h := equivalent_of_normalized_limit hscalePositive hcoefficientPositive.ne' hfreeNormalized
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h
  have hXuNormalized (i : Fin 2) :
      Tendsto (fun j ↦ xuScalar p (2 * j + (i : ℕ)) / p.scale j ^ 4)
        atTop (𝓝 (xuLeadingCoefficient νStar i)) := by
    have h := xuScalar_phase_tendsto hradius hstart hK hstate hfeasible i
    rw [hpK, cycleState_offDiagonal_div νStar hparameter i] at h
    simpa only [xuLeadingCoefficient_def] using h
  have hWstar : 0 < cycleW νStar := by
    simpa only [Set.mem_Ioi] using (TwoCycle.cycleFamily_mapsTo_positive hparameter).2.2
  have hZstar : 0 < cycleZ νStar := by
    simpa only [Set.mem_Ioi] using (TwoCycle.cycleFamily_mapsTo_positive hparameter).2.1
  have ha := ActualObjective.baseAngle_pos
  have hLeadingPositive (i : Fin 2) : 0 < xuLeadingCoefficient νStar i := by
    fin_cases i
    · have h : 0 < 2 * baseAngle * cycleW νStar := by positivity
      simpa only [Fin.zero_eta, Fin.isValue, xuLeadingCoefficient_even] using h
    · have h : 0 < baseAngle * cycleZ νStar := mul_pos ha hZstar
      simpa only [Fin.mk_one, Fin.isValue, xuLeadingCoefficient_odd] using h
  have hXuEquivalent (i : Fin 2) : (fun j ↦ xuScalar p (2 * j + (i : ℕ))) ~[atTop]
      (fun j ↦ xuLeadingCoefficient νStar i * p.scale j ^ 4) := by
    have hpositive (j : ℕ) : 0 < p.scale j ^ 4 := pow_pos (ScaleTails.scale_pos p hstart j) 4
    exact equivalent_of_normalized_limit hpositive (hLeadingPositive i).ne' (hXuNormalized i)
  have hEven : Tendsto (fun j ↦ xuScalar p (2 * j) / p.scale j ^ 4) atTop
      (𝓝 (2 * baseAngle * cycleW νStar)) := by
    simpa only [Fin.val_zero, Nat.add_zero, xuLeadingCoefficient_even] using hXuNormalized 0
  have hOdd : Tendsto (fun j ↦ xuScalar p (2 * j + 1) / p.scale j ^ 4) atTop
      (𝓝 (baseAngle * cycleZ νStar)) := by
    simpa only [Fin.val_one, xuLeadingCoefficient_odd] using hXuNormalized 1
  have hXuPositive (k : ℕ) : 0 < xuScalar p k := xuScalar_pos hradius hstart hfeasible k
  have hXuOddNe (j : ℕ) : xuScalar p (2 * j + 1) ≠ 0 := (hXuPositive _).ne'
  have hOddLeading : baseAngle * cycleZ νStar ≠ 0 := (mul_pos ha hZstar).ne'
  have hJump := xuScalar_jump_tendsto p hstart hOddLeading hXuOddNe hEven hOdd
  have hquotient : (2 * baseAngle * cycleW νStar) / (baseAngle * cycleZ νStar) =
      2 * cycleW νStar / cycleZ νStar := by
    field_simp [ha.ne', hZstar.ne']
  rw [hquotient] at hJump
  have hJumpLarge := xuJumpLimit_gt_four νStar hparameter hnear.1
  have honeFour : (1 : ℝ) < 4 := by norm_num
  have hnotMonotone := xuScalar_not_eventually_nonincreasing p (honeFour.trans hJumpLarge)
    hXuPositive hJump
  exact ⟨hcurvatureIdentity, hcurvature, hdetEquivalent, hfreeEquivalent,
    fun i ↦ ⟨hXuNormalized i, hXuEquivalent i⟩, hJump, hJumpLarge, hnotMonotone⟩

/-- sec:known-results and the polar degeneration order following
lem:planar-degeneration (v21): the actual original polar trajectory has opposite
cubic gradient-norm ratio expansions with a uniform fourth-order constant,
infinitely many increases and decreases, quadratic step norms and infinite total
length, and nonzero accepted endpoint derivatives. Xu's original scalar has the
source leading coefficients `2awStar` and `azStar`, and its next-even/odd ratio
tends to `2wStar/zStar>4`, excluding eventual decrease. The exact source curvature
is `σ/(1+ω²)` and tends to one; both `det H_k` and the ORIGINAL
`λ_k=κ_(k−1)det H_k` are asymptotically `t_(k/2)^4/KStar`.

One parameter neighborhood and one natural threshold apply to ALL these
conclusions simultaneously. Every quantitative constant is chosen before every
later `j₀`; no trajectory convergence or target estimate is a hypothesis. -/
theorem polarSequenceAsymptotics :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ C > 0, ∃ lower > 0, ∃ upper > 0,
        ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        let p := Parameters.of j₀ νStar
        0 < p.feedbackRate ∧
        (∀ j,
          |gradientRatio p (2 * j) - 1 + p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4 ∧
          |gradientRatio p (2 * j + 1) - 1 - p.feedbackRate * p.scale j ^ 3| ≤ C * p.scale j ^ 4) ∧
        (Asymptotics.IsBigOWith C atTop
          (fun j ↦ gradientRatio p (2 * j) - (1 - p.feedbackRate * p.scale j ^ 3))
          (fun j ↦ p.scale j ^ 4) ∧
         Asymptotics.IsBigOWith C atTop
          (fun j ↦ gradientRatio p (2 * j + 1) - (1 + p.feedbackRate * p.scale j ^ 3))
          (fun j ↦ p.scale j ^ 4)) ∧
        (∀ j, ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j)‖ ∧
          ‖p.gradient (2 * j + 1)‖ < ‖p.gradient (2 * j + 2)‖) ∧
        (¬ ∀ᶠ k in atTop, ‖p.gradient (k + 1)‖ ≤ ‖p.gradient k‖) ∧
        (¬ ∀ᶠ k in atTop, ‖p.gradient k‖ ≤ ‖p.gradient (k + 1)‖) ∧
        (∀ k, lower * p.scale (k / 2) ^ 2 ≤ ‖step p k‖ ∧
          ‖step p k‖ ≤ upper * p.scale (k / 2) ^ 2) ∧
        (¬ Summable (fun k ↦ ‖step p k‖) ∧
          Tendsto (fun n ↦ ∑ k ∈ Finset.range n, ‖step p k‖) atTop atTop) ∧
        (∀ k, WolfeRatios.endSlope p k ≠ 0) ∧
        (∀ k, curvature p k = p.sigma k / (1 + p.omega k ^ 2)) ∧
        Tendsto (curvature p) atTop (𝓝 1) ∧
        ((fun k ↦ (p.inverseHessian k).det) ~[atTop]
          (fun k ↦ p.scale (k / 2) ^ 4 / p.kStar)) ∧
        (freeCoefficient p ~[atTop] (fun k ↦ p.scale (k / 2) ^ 4 / p.kStar)) ∧
        ((fun j ↦ xuScalar p (2 * j)) ~[atTop]
          (fun j ↦ (2 * baseAngle * cycleW νStar) * p.scale j ^ 4)) ∧
        ((fun j ↦ xuScalar p (2 * j + 1)) ~[atTop]
          (fun j ↦ (baseAngle * cycleZ νStar) * p.scale j ^ 4)) ∧
        Tendsto (fun j ↦ xuScalar p (2 * j + 2) / xuScalar p (2 * j + 1))
          atTop (𝓝 (2 * cycleW νStar / cycleZ νStar)) ∧
        4 < 2 * cycleW νStar / cycleZ νStar ∧
        (¬ ∀ᶠ k in atTop, xuScalar p (k + 1) ≤ xuScalar p k) := by
  obtain ⟨ηg, hηg, hgradients⟩ := polarGradientNormOscillation
  obtain ⟨ηs, hηs, hsteps⟩ := polarStepLengthDivergence
  obtain ⟨ηe, hηe, hendpoints⟩ := polarAcceptedEndpointNonzero
  obtain ⟨ηx, hηx, hscalars⟩ := polarScalarAsymptotics
  refine ⟨min ηg (min ηs (min ηe ηx)), lt_min hηg (lt_min hηs (lt_min hηe hηx)), ?_⟩
  intro νStar hnear
  have hηsLe : min ηg (min ηs (min ηe ηx)) ≤ ηs :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηeLe : min ηg (min ηs (min ηe ηx)) ≤ ηe :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηxLe : min ηg (min ηs (min ηe ηx)) ≤ ηx :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnearG : νStar ∈ Set.Ioo baseAngle (baseAngle + ηg) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hnearS : νStar ∈ Set.Ioo baseAngle (baseAngle + ηs) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl hηsLe)⟩
  have hnearE : νStar ∈ Set.Ioo baseAngle (baseAngle + ηe) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl hηeLe)⟩
  have hnearX : νStar ∈ Set.Ioo baseAngle (baseAngle + ηx) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl hηxLe)⟩
  obtain ⟨C, hC, Jg, hJg, hgradientAll⟩ := hgradients νStar hnearG
  obtain ⟨lower, hlower, upper, hupper, Js, _, hstepAll⟩ := hsteps νStar hnearS
  obtain ⟨Je, _, hendpointAll⟩ := hendpoints νStar hnearE
  obtain ⟨hparameter, Jx, _, hscalarAll⟩ := hscalars νStar hnearX
  refine ⟨hparameter, C, hC, lower, hlower, upper, hupper,
    max Jg (max Js (max Je Jx)), hJg.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  dsimp only
  let p := Parameters.of j₀ νStar
  have hjG : Jg ≤ j₀ := (le_max_left _ _).trans hj₀
  have hjS : Js ≤ j₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hj₀
  have hjE : Je ≤ j₀ :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hj₀
  have hjX : Jx ≤ j₀ :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hj₀
  obtain ⟨hL, hratioErrors, hsigns, hnotDown, hnotUp⟩ := hgradientAll j₀ hjG
  obtain ⟨hstepBounds, hnotSummable, hsumDiverges⟩ := hstepAll j₀ hjS
  obtain ⟨hcurvatureIdentity, hcurvatureLimit, hdet, hfree, hXu, hJump, hJumpLarge, hXuNot⟩ :=
    hscalarAll j₀ hjX
  have hbigO := gradientRatio_isBigOWith p C hratioErrors
  have hEvenXu : (fun j ↦ xuScalar p (2 * j)) ~[atTop]
      (fun j ↦ (2 * baseAngle * cycleW νStar) * p.scale j ^ 4) := by
    simpa only [Fin.val_zero, Nat.add_zero, xuLeadingCoefficient_even] using (hXu 0).2
  have hOddXu : (fun j ↦ xuScalar p (2 * j + 1)) ~[atTop]
      (fun j ↦ (baseAngle * cycleZ νStar) * p.scale j ^ 4) := by
    simpa only [Fin.val_one, xuLeadingCoefficient_odd] using (hXu 1).2
  exact ⟨hL, hratioErrors, hbigO, hsigns, hnotDown, hnotUp, hstepBounds,
    ⟨hnotSummable, hsumDiverges⟩, hendpointAll j₀ hjE,
    hcurvatureIdentity, hcurvatureLimit, hdet, hfree, hEvenXu, hOddXu,
    hJump, hJumpLarge, hXuNot⟩

/-- Helper for sec:known-results and the source degeneration order: adjacent
physical step products are uniformly comparable to the current quartic scale. -/
theorem stepProduct_bounds (p : Parameters) (hstart : 0 < p.startIndex)
    {lower upper : ℝ} (hlower : 0 < lower) (hupper : 0 < upper)
    (hsteps : ∀ k, lower * p.scale (k / 2) ^ 2 ≤ ‖step p k‖ ∧
      ‖step p k‖ ≤ upper * p.scale (k / 2) ^ 2) (k : ℕ) (hk : 1 ≤ k) :
    lower ^ 2 * p.scale (k / 2) ^ 4 ≤ ‖step p (k - 1)‖ * ‖step p k‖ ∧
      ‖step p (k - 1)‖ * ‖step p k‖ ≤ 4 * upper ^ 2 * p.scale (k / 2) ^ 4 := by
  have hindex : (k - 1) / 2 ≤ k / 2 := Nat.div_le_div_right (Nat.sub_le k 1)
  have hscale := ScaleTails.scale_antitone p hstart hindex
  have hscaleSq := pow_le_pow_left₀ (ScaleTails.scale_nonneg p (k / 2)) hscale 2
  have hindices : p.startIndex + k / 2 ≤ 8 * (p.startIndex + (k - 1) / 2) := by omega
  have hhalf := AngularGeometry.scale_lower_of_index_le_eight p hstart ((k - 1) / 2)
    (k / 2) hindices
  have hhalfNonnegative : 0 ≤ (1 / 2 : ℝ) * p.scale ((k - 1) / 2) := by
    have hconstant : (0 : ℝ) ≤ 1 / 2 := by norm_num
    exact mul_nonneg hconstant (ScaleTails.scale_nonneg p _)
  have hhalfSq := pow_le_pow_left₀ hhalfNonnegative hhalf 2
  have hpreviousSq : p.scale ((k - 1) / 2) ^ 2 ≤ 4 * p.scale (k / 2) ^ 2 := by
    nlinarith
  have hpreviousLower : lower * p.scale (k / 2) ^ 2 ≤ ‖step p (k - 1)‖ :=
    (mul_le_mul_of_nonneg_left hscaleSq hlower.le).trans (hsteps (k - 1)).1
  have hpreviousUpper : ‖step p (k - 1)‖ ≤ (4 * upper) * p.scale (k / 2) ^ 2 := by
    have h := (hsteps (k - 1)).2.trans (mul_le_mul_of_nonneg_left hpreviousSq hupper.le)
    nlinarith
  have hproductLower := mul_le_mul hpreviousLower (hsteps k).1
    (mul_nonneg hlower.le (sq_nonneg _)) (norm_nonneg _)
  have hupperNonnegative : 0 ≤ (4 * upper) * p.scale (k / 2) ^ 2 := by positivity
  have hproductUpper := mul_le_mul hpreviousUpper (hsteps k).2 (norm_nonneg _) hupperNonnegative
  constructor
  · nlinarith
  · nlinarith

/-- Helper for sec:known-results and the source degeneration order: a
positive asymptotic equivalent gives eventual explicit factor-two bounds. -/
theorem eventual_factor_bounds_of_equivalent {f g : ℕ → ℝ}
    (hg : ∀ k, 0 < g k) (h : f ~[atTop] g) :
    ∀ᶠ k in atTop, g k / 2 ≤ f k ∧ f k ≤ 2 * g k := by
  have hnonzero : ∀ᶠ k in atTop, g k ≠ 0 := Eventually.of_forall (fun k ↦ (hg k).ne')
  have hlimit := (Asymptotics.isEquivalent_iff_tendsto_one hnonzero).mp h
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hlower := hlimit.eventually (eventually_gt_nhds hhalf)
  have hupper := hlimit.eventually (eventually_lt_nhds htwo)
  filter_upwards [hlower, hupper] with k hkLower hkUpper
  have hlower' : (1 / 2 : ℝ) * g k < f k := (lt_div_iff₀ (hg k)).mp hkLower
  have hupper' : f k < 2 * g k := (div_lt_iff₀ (hg k)).mp hkUpper
  constructor
  · linarith
  · exact hupper'.le

/-- Helper for sec:known-results and the source degeneration order: the
original coefficient is bounded above and below by fixed positive multiples
of consecutive physical step products. -/
theorem freeCoefficient_stepProduct_bounds (p : Parameters) (hstart : 0 < p.startIndex)
    (hK : 0 < p.kStar) {lower upper : ℝ} (hlower : 0 < lower) (hupper : 0 < upper)
    (hsteps : ∀ k, lower * p.scale (k / 2) ^ 2 ≤ ‖step p k‖ ∧
      ‖step p k‖ ≤ upper * p.scale (k / 2) ^ 2)
    (hfree : freeCoefficient p ~[atTop] (fun k ↦ p.scale (k / 2) ^ 4 / p.kStar)) :
    ∀ᶠ k in atTop,
      (1 / (8 * upper ^ 2 * p.kStar)) * (‖step p (k - 1)‖ * ‖step p k‖) ≤ freeCoefficient p k ∧
      freeCoefficient p k ≤ (2 / (lower ^ 2 * p.kStar)) *
        (‖step p (k - 1)‖ * ‖step p k‖) := by
  have hpositive (k : ℕ) : 0 < p.scale (k / 2) ^ 4 / p.kStar :=
    div_pos (pow_pos (ScaleTails.scale_pos p hstart _) 4) hK
  have hbounds := eventual_factor_bounds_of_equivalent hpositive hfree
  have ha : 0 ≤ 1 / (8 * upper ^ 2 * p.kStar) := by positivity
  have hb : 0 ≤ 2 / (lower ^ 2 * p.kStar) := by positivity
  filter_upwards [hbounds, eventually_ge_atTop 1] with k hk hkOne
  have hproduct := stepProduct_bounds p hstart hlower hupper hsteps k hkOne
  constructor
  · calc
      (1 / (8 * upper ^ 2 * p.kStar)) * (‖step p (k - 1)‖ * ‖step p k‖) ≤
          (1 / (8 * upper ^ 2 * p.kStar)) * (4 * upper ^ 2 * p.scale (k / 2) ^ 4) :=
        mul_le_mul_of_nonneg_left hproduct.2 ha
      _ = (p.scale (k / 2) ^ 4 / p.kStar) / 2 := by
        field_simp [hK.ne', hupper.ne']
        ring
      _ ≤ freeCoefficient p k := hk.1
  · calc
      freeCoefficient p k ≤ 2 * (p.scale (k / 2) ^ 4 / p.kStar) := hk.2
      _ = (2 / (lower ^ 2 * p.kStar)) * (lower ^ 2 * p.scale (k / 2) ^ 4) := by
        field_simp [hK.ne', hlower.ne']
      _ ≤ (2 / (lower ^ 2 * p.kStar)) * (‖step p (k - 1)‖ * ‖step p k‖) :=
        mul_le_mul_of_nonneg_left hproduct.1 hb

/-- Helper for sec:known-results and the source degeneration order after
lem:planar-degeneration: on the actual original polar family, `λ_k` has the
same order as the product of consecutive step norms, with both positive
comparison constants chosen before every later starting index. -/
theorem polarFreeCoefficientStepOrder :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ a > 0, ∃ b > 0, ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        let p := Parameters.of j₀ νStar
        ∀ᶠ k in atTop,
          a * (‖step p (k - 1)‖ * ‖step p k‖) ≤ freeCoefficient p k ∧
          freeCoefficient p k ≤ b * (‖step p (k - 1)‖ * ‖step p k‖) := by
  obtain ⟨ηx, hηx, hscalars⟩ := polarScalarAsymptotics
  obtain ⟨ηs, hηs, hsteps⟩ := polarStepLengthDivergence
  refine ⟨min ηx ηs, lt_min hηx hηs, ?_⟩
  intro νStar hnear
  have hnearX : νStar ∈ Set.Ioo baseAngle (baseAngle + ηx) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hnearS : νStar ∈ Set.Ioo baseAngle (baseAngle + ηs) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_right _ _))⟩
  obtain ⟨hparameter, Jx, hJx, hscalarAll⟩ := hscalars νStar hnearX
  obtain ⟨lower, hlower, upper, hupper, Js, _, hstepAll⟩ := hsteps νStar hnearS
  have hK : 0 < cycleK νStar := by
    simpa only [Set.mem_Ioi] using (TwoCycle.cycleFamily_mapsTo_positive hparameter).1
  have ha : 0 < 1 / (8 * upper ^ 2 * cycleK νStar) := by positivity
  have hb : 0 < 2 / (lower ^ 2 * cycleK νStar) := by positivity
  refine ⟨1 / (8 * upper ^ 2 * cycleK νStar), ha, 2 / (lower ^ 2 * cycleK νStar), hb,
    max Jx Js, hJx.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  dsimp only
  let p := Parameters.of j₀ νStar
  have hjX : Jx ≤ j₀ := (le_max_left _ _).trans hj₀
  have hjS : Js ≤ j₀ := (le_max_right _ _).trans hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJx.trans_le hjX
  have hpK : p.kStar = cycleK νStar := by
    rw [Parameters.kStar_def, Parameters.of_cycleParameter]
  have hKp : 0 < p.kStar := by
    rw [hpK]
    exact hK
  obtain ⟨_, _, _, hfree, _, _, _, _⟩ := hscalarAll j₀ hjX
  have h := freeCoefficient_stepProduct_bounds p hstart hKp hlower hupper
    (hstepAll j₀ hjS).1 hfree
  simpa only [hpK] using h

end DFP.Polar.SequenceAsymptotics

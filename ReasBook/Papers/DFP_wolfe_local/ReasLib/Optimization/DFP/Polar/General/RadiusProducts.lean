module

public import ReasLib.Optimization.DFP.Polar.General.Geometry
public import ReasLib.Optimization.DFP.Polar.General.Realization
public import ReasLib.Optimization.DFP.Polar.General.Continuation
public import ReasLib.Optimization.DFP.Polar.General.RadiusBounds

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Polar.General.RadiusProducts

/-- Helper for eq:polar-orders: the source principal radial-excess coefficient. -/
def principalCoefficient (β D0 D1 : ℝ) : ℝ := ((1 + β) / (1 - β)) * (D0 + D1)

/-- Helper for eq:polar-orders: the exact principal radial-excess coefficient formula. -/
theorem principalCoefficient_def (β D0 D1 : ℝ) :
    principalCoefficient β D0 D1 = ((1 + β) / (1 - β)) * (D0 + D1) := by
  rfl

/-- Helper for lem:polar-geometry: uniform source radius conclusions derived
from the paired product, including the principal term and the scalar envelopes. -/
structure RadiusEnvelope (β : ℝ) (j0 : ℕ) (r : ℕ → ℝ)
    (D0 D1 B K c U : ℝ) : Prop where
  /-- Helper for eq:polar-radii: all source radii exceed one. -/
  above_one : ∀ k, 1 < r k
  /-- Helper for lem:polar-geometry: all source radii have one uniform upper bound. -/
  upper : ∀ k, r k ≤ B
  /-- Helper for eq:polar-radii: the source radii strictly decrease. -/
  strictAnti : StrictAnti r
  /-- Helper for eq:polar-radii: the same radii tend to their prescribed unit limit. -/
  tendsto_one : Tendsto r atTop (𝓝 1)
  /-- Helper for eq:polar-orders: both phases share the exact source principal coefficient. -/
  expansion : ∀ k,
    |r k - 1 - principalCoefficient β D0 D1 * scale β j0 (k / 2) ^ (1 - β)| ≤
      K * scale β j0 (k / 2) ^ (2 * (1 - β))
  /-- Helper for lem:polar-interpolation: radial excess dominates the slow source power. -/
  excess_lower : ∀ k,
    (principalCoefficient β D0 D1 / 2) * scale β j0 (k / 2) ^ (1 - β) ≤ r k - 1
  /-- Helper for eq:polar-orders: radial decrements have the quadratic source lower bound. -/
  drop_lower : ∀ k, c * scale β j0 (k / 2) ^ 2 ≤ r k - r (k + 1)
  /-- Helper for eq:polar-orders: radial decrements have the quadratic source upper bound. -/
  drop_upper : ∀ k, r k - r (k + 1) ≤ U * scale β j0 (k / 2) ^ 2

/-- Helper for lem:polar-geometry: positive two-phase factor expansions imply
uniform logarithmic errors and summability of the actual cycle logarithms. -/
theorem cycleLog_bounds {β D0 D1 C : ℝ} (hβ : 0 < β) (hβone : β < 1)
    {j0 : ℕ} (hstart : 0 < j0) (hC : 0 ≤ C) {u v : ℕ → ℝ}
    (hu : ∀ j, 1 < u j) (hv : ∀ j, 1 < v j)
    (herror : ∀ j,
      |u j - 1 - D0 * scale β j0 j ^ 2| ≤ C * scale β j0 j ^ (3 - β) ∧
      |v j - 1 - D1 * scale β j0 j ^ 2| ≤ C * scale β j0 j ^ (3 - β)) :
    (∀ j, |Real.log (u j * v j) - (D0 + D1) * scale β j0 j ^ 2| ≤
      ((C + (D0 + C) ^ 2) + (C + (D1 + C) ^ 2)) * scale β j0 j ^ (3 - β)) ∧
      Summable (fun j ↦ Real.log (u j * v j)) := by
  have hlog (j : ℕ) :
      |Real.log (u j * v j) - (D0 + D1) * scale β j0 j ^ 2| ≤
        ((C + (D0 + C) ^ 2) + (C + (D1 + C) ^ 2)) * scale β j0 j ^ (3 - β) := by
    exact Geometry.cycleLog_error (zero_lt_one.trans (hu j)) (zero_lt_one.trans (hv j))
      (Geometry.logFactor_power_error hβ hβone (scale_pos β hstart j)
        (scale_le_one hβ hstart j) hC (hu j).le (herror j).1)
      (Geometry.logFactor_power_error hβ hβone (scale_pos β hstart j)
        (scale_le_one hβ hstart j) hC (hv j).le (herror j).2)
  exact ⟨hlog, Geometry.summableLog_of_powerError hβ hβone j0 hlog⟩

/-- Helper for lem:polar-geometry: a reciprocal threshold absorbs a fixed
nonnegative scale into a unit upper bound. -/
private theorem mul_le_one_of_small {a s : ℝ} (hs : 0 ≤ s) (ha : 0 < a + 1)
    (hsmall : s < 1 / (a + 1)) : a * s ≤ 1 := by
  have hscaled := (lt_div_iff₀ ha).mp hsmall
  nlinarith only [hscaled, hs]

/-- Helper for lem:polar-geometry: a quadratic radial expansion at a scale
between zero and one gives a uniform upper bound. -/
private theorem radius_upper_of_linear_error {R s L K : ℝ}
    (hs : 0 ≤ s) (hsone : s ≤ 1) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (herror : |R - 1 - L * s| ≤ K * s ^ 2) : R ≤ 2 + L + K := by
  have hsq : s ^ 2 ≤ 1 := by
    nlinarith only [hs, hsone]
  have hlinear := mul_le_mul_of_nonneg_left hsone hL
  have hquadratic := mul_le_mul_of_nonneg_left hsq hK
  have herr := (abs_le.mp herror).2
  nlinarith only [herr, hlinear, hquadratic]

/-- Helper for lem:polar-geometry: the radius-error coefficient is absorbed
by half the principal coefficient at one uniform slow-scale threshold. -/
private theorem mul_le_half_of_small {K L s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hsmall : s < L / (2 * (K + 1))) : K * s ≤ L / 2 := by
  have hden : 0 < 2 * (K + 1) := by
    positivity
  have hscaled := (lt_div_iff₀ hden).mp hsmall
  nlinarith only [hscaled, hs]

/-- Helper for lem:polar-interpolation: a small quadratic radius error leaves
at least half of the principal radial excess. -/
private theorem radius_excess_of_linear_error {R s L K : ℝ}
    (hs : 0 ≤ s) (hsmall : K * s ≤ L / 2)
    (herror : |R - 1 - L * s| ≤ K * s ^ 2) : (L / 2) * s ≤ R - 1 := by
  have hproduct := mul_le_mul_of_nonneg_right hsmall hs
  have herr := (abs_le.mp herror).1
  nlinarith only [herr, hproduct]

/-- Helper for lem:polar-geometry: source paired-factor errors and positive
quadratic defects give the complete uniform radius envelope, with all constants
chosen before the starting index and the factor sequences. -/
theorem exists_pairedRadiusEnvelope {β D0 D1 C : ℝ}
    (hβ : 0 < β) (hβone : β < 1) (hD0 : 0 < D0) (hD1 : 0 < D1) (hC : 0 ≤ C) :
    ∃ B > 0, ∃ K > 0, ∃ c > 0, ∃ U > 0, ∃ δ > 0,
      ∀ j0 : ℕ, 0 < j0 → scale β j0 0 ^ (1 - β) < δ →
      ∀ u v : ℕ → ℝ, (∀ j, 1 < u j) → (∀ j, 1 < v j) →
      (∀ j, |u j - 1 - D0 * scale β j0 j ^ 2| ≤ C * scale β j0 j ^ (3 - β) ∧
        |v j - 1 - D1 * scale β j0 j ^ 2| ≤ C * scale β j0 j ^ (3 - β)) →
      (∀ j, (D0 / 2) * scale β j0 j ^ 2 ≤ u j - 1 ∧
        u j - 1 ≤ (D0 + C) * scale β j0 j ^ 2 ∧
        (D1 / 2) * scale β j0 j ^ 2 ≤ v j - 1 ∧
        v j - 1 ≤ (D1 + C) * scale β j0 j ^ 2) →
      Summable (fun j ↦ Real.log (u j * v j)) ∧
        RadiusEnvelope β j0 (Geometry.pairedRadius u v) D0 D1 B K c U := by
  let D := D0 + D1
  let Clog := (C + (D0 + C) ^ 2) + (C + (D1 + C) ^ 2)
  let L := principalCoefficient β D0 D1
  let E := D + Clog * (((1 + β) / (2 * (1 - β))) + 1)
  let Ke := (L + E) ^ 2 + E
  let B := 2 + L + Ke
  let K := Ke + B * (D0 + C) + 1
  let c := min D0 D1 / 2
  let U := B * (max D0 D1 + C)
  let δ := min (1 / (L + E + 1)) (L / (2 * (K + 1)))
  have hD : 0 < D := add_pos hD0 hD1
  have hClog : 0 ≤ Clog := by
    positivity
  have hL : 0 < L := by
    dsimp only [L]
    rw [principalCoefficient_def]
    exact mul_pos (div_pos (add_pos zero_lt_one hβ) (sub_pos.mpr hβone)) hD
  have hE : 0 < E := by
    dsimp only [E]
    have hratio : 0 ≤ (1 + β) / (2 * (1 - β)) := by
      positivity
    positivity
  have hKe : 0 < Ke := by
    positivity
  have hB : 0 < B := by
    positivity
  have hK : 0 < K := by
    positivity
  have hc : 0 < c := div_pos (lt_min hD0 hD1) zero_lt_two
  have hU : 0 < U := mul_pos hB (add_pos_of_pos_of_nonneg
    (hD0.trans_le (le_max_left D0 D1)) hC)
  have hδ : 0 < δ := by
    positivity
  refine ⟨B, hB, K, hK, c, hc, U, hU, δ, hδ, ?_⟩
  intro j0 hstart hsmall u v hu hv herror hdefect
  obtain ⟨hlogError, hlog⟩ := cycleLog_bounds hβ hβone hstart hC hu hv herror
  have hsmallLog : (L + E) * scale β j0 0 ^ (1 - β) ≤ 1 := by
    have hsmall' := hsmall.trans_le (min_le_left _ _)
    have hden : 0 < L + E + 1 := by
      positivity
    exact mul_le_one_of_small (Real.rpow_nonneg (scale_nonneg β j0 0) (1 - β)) hden hsmall'
  have hevenError (j : ℕ) :
      |Geometry.pairedRadius u v (2 * j) - 1 - L * scale β j0 j ^ (1 - β)| ≤
        Ke * scale β j0 j ^ (2 * (1 - β)) := by
    rw [Geometry.pairedRadius_even]
    exact Geometry.tailProduct_power_error hβ hβone hstart
      (fun j ↦ mul_pos (zero_lt_one.trans (hu j)) (zero_lt_one.trans (hv j)))
      hD.le hClog hlogError hsmallLog j
  have hslowNonneg (j : ℕ) : 0 ≤ scale β j0 j ^ (1 - β) :=
    Real.rpow_nonneg (scale_nonneg β j0 j) _
  have hslowOne (j : ℕ) : scale β j0 j ^ (1 - β) ≤ 1 :=
    Real.rpow_le_one (scale_nonneg β j0 j) (scale_le_one hβ hstart j)
      (sub_pos.mpr hβone).le
  have hslowSq (j : ℕ) : (scale β j0 j ^ (1 - β)) ^ 2 =
      scale β j0 j ^ (2 * (1 - β)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (scale_nonneg β j0 j)]
    congr 1
    ring
  have hanti := Geometry.pairedRadius_strictAnti hu hv hlog
  have hrOne := Geometry.pairedRadius_gt_one hu hv hlog
  have hevenUpper (j : ℕ) : Geometry.pairedRadius u v (2 * j) ≤ B := by
    have herr := hevenError j
    rw [← hslowSq j] at herr
    exact radius_upper_of_linear_error (hslowNonneg j) (hslowOne j) hL.le hKe.le herr
  have hrUpper (k : ℕ) : Geometry.pairedRadius u v k ≤ B := by
    have hindex : 2 * (k / 2) ≤ k := by
      omega
    exact (hanti.antitone hindex).trans (hevenUpper (k / 2))
  have hKKe : Ke ≤ K := by
    dsimp only [K]
    exact (le_add_of_nonneg_right (mul_nonneg hB.le (add_nonneg hD0.le hC))).trans
      (le_add_of_nonneg_right zero_le_one)
  have hKOdd : Ke + B * (D0 + C) ≤ K := by
    dsimp only [K]
    exact le_add_of_nonneg_right zero_le_one
  have hexpansion (k : ℕ) :
      |Geometry.pairedRadius u v k - 1 - L * scale β j0 (k / 2) ^ (1 - β)| ≤
        K * scale β j0 (k / 2) ^ (2 * (1 - β)) := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have hindex : 2 * j / 2 = j := by
        omega
      rw [hindex]
      exact (hevenError j).trans (mul_le_mul_of_nonneg_right hKKe
        (Real.rpow_nonneg (scale_nonneg β j0 j) _))
    · have hindex : (2 * j + 1) / 2 = j := by
        omega
      rw [hindex, Geometry.pairedRadius_odd]
      have hR : 0 ≤ DFP.Polar.RadiusProducts.tailProduct (fun n ↦ u n * v n) j := by
        rw [← Geometry.pairedRadius_even]
        exact (zero_lt_one.trans (hrOne (2 * j))).le
      have hRupper : DFP.Polar.RadiusProducts.tailProduct (fun n ↦ u n * v n) j ≤ B := by
        rw [← Geometry.pairedRadius_even]
        exact hevenUpper j
      have heven : |DFP.Polar.RadiusProducts.tailProduct (fun n ↦ u n * v n) j -
          1 - L * scale β j0 j ^ (1 - β)| ≤ Ke * scale β j0 j ^ (2 * (1 - β)) := by
        simpa only [Geometry.pairedRadius_even] using hevenError j
      have hodd := Geometry.quotientRadius_power_error hβ (scale_pos β hstart j)
        (scale_le_one hβ hstart j) (add_nonneg hD0.le hC) hR hRupper (hu j).le
        heven (hdefect j).2.1
      exact hodd.trans (mul_le_mul_of_nonneg_right hKOdd
        (Real.rpow_nonneg (scale_nonneg β j0 j) _))
  have hexcess (k : ℕ) :
      (L / 2) * scale β j0 (k / 2) ^ (1 - β) ≤ Geometry.pairedRadius u v k - 1 := by
    have hmonotone := Real.rpow_le_rpow (scale_nonneg β j0 (k / 2))
      (scale_antitone hβ hstart (Nat.zero_le (k / 2))) (sub_pos.mpr hβone).le
    have hsmall' := hsmall.trans_le (min_le_right _ _)
    have hsmallAtZero := mul_le_half_of_small hK.le (hslowNonneg 0) hsmall'
    have hKsmall : K * scale β j0 (k / 2) ^ (1 - β) ≤ L / 2 := by
      exact (mul_le_mul_of_nonneg_left hmonotone hK.le).trans hsmallAtZero
    have herr := hexpansion k
    rw [← hslowSq (k / 2)] at herr
    exact radius_excess_of_linear_error (hslowNonneg (k / 2)) hKsmall herr
  have hfactorBounds (k : ℕ) :
      c * scale β j0 (k / 2) ^ 2 ≤ DFP.twoStepSequence u v k - 1 ∧
      DFP.twoStepSequence u v k - 1 ≤ (max D0 D1 + C) * scale β j0 (k / 2) ^ 2 := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · have hindex : 2 * j / 2 = j := by
        omega
      rw [DFP.twoStepSequence_even, hindex]
      constructor
      · apply (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (min_le_left D0 D1) zero_le_two) (sq_nonneg _)).trans (hdefect j).1
      · exact (hdefect j).2.1.trans (mul_le_mul_of_nonneg_right
          (add_le_add (le_max_left D0 D1) (le_refl C)) (sq_nonneg _))
    · have hindex : (2 * j + 1) / 2 = j := by
        omega
      rw [DFP.twoStepSequence_odd, hindex]
      constructor
      · apply (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (min_le_right D0 D1) zero_le_two) (sq_nonneg _)).trans (hdefect j).2.2.1
      · exact (hdefect j).2.2.2.trans (mul_le_mul_of_nonneg_right
          (add_le_add (le_max_right D0 D1) (le_refl C)) (sq_nonneg _))
  have hdrop (k : ℕ) := Geometry.radius_drop_bounds_of_factor_bounds
    (hrOne (k + 1)).le (hrUpper (k + 1)) hc.le (hfactorBounds k).1 (hfactorBounds k).2
    (Geometry.pairedRadius_recurrence (fun j ↦ zero_lt_one.trans (hu j))
      (fun j ↦ zero_lt_one.trans (hv j)) hlog k)
  exact ⟨hlog, hrOne, hrUpper, hanti, Geometry.pairedRadius_tendsto_one hu hv hlog,
    hexpansion, hexcess, fun k ↦ (hdrop k).1, fun k ↦ (hdrop k).2⟩

/-- Helper for lem:polar-geometry: the source factor estimates from the actual
slow and fast tubes give the paired-product radius envelope uniformly before
the starting index is chosen. -/
theorem radiusEnvelopeOfActualTube (p : Parameters) (hβ : 0 < p.beta)
    (hβone : p.beta < 1) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ B > 0, ∃ K > 0, ∃ c > 0, ∃ U > 0, ∃ δ > 0,
      ∀ j0 : ℕ, 0 < j0 → scale p.beta j0 0 ^ (1 - p.beta) < δ →
      (∀ j, |((p.withStartIndex j0).normalizedEvenState j).1 - p.gammaStar| ≤
        M * scale p.beta j0 j ^ (1 - p.beta)) →
      (∀ j, FastContraction.fixedNorm p.ell p.z
        (DFP.Polar.FastContraction.fastCoordinates ((p.withStartIndex j0).normalizedEvenState j) -
          FastContraction.evenFastReference p ((p.withStartIndex j0).normalizedEvenState j).1) ≤
        N * scale p.beta j0 j ^ (1 + p.beta)) →
      (∀ k, 1 < (p.withStartIndex j0).radiusRatio k) ∧
      Summable (fun j ↦ Real.log ((p.withStartIndex j0).radiusRatio (2 * j) *
        (p.withStartIndex j0).radiusRatio (2 * j + 1))) ∧
      RadiusEnvelope p.beta j0 (p.withStartIndex j0).radius
        (RadiusBounds.radiusLimitCoefficient p 0) (RadiusBounds.radiusLimitCoefficient p 1)
        B K c U := by
  obtain ⟨C1, hC1, δ1, hδ1, herror⟩ :=
    RadiusBounds.radiusBoundsOfActualTube p hβ hβone hM hN
  obtain ⟨C2, hC2, δ2, hδ2, hfactor⟩ :=
    RadiusBounds.factorBoundsOfActualTube p hβ hβone hM hN
  let C := max C1 C2
  have hC : 0 ≤ C := hC1.le.trans (le_max_left C1 C2)
  obtain ⟨B, hB, K, hK, c, hc, U, hU, δr, hδr, hpaired⟩ :=
    exists_pairedRadiusEnvelope hβ hβone
      (RadiusBounds.radiusLimitCoefficient_pos p hβ 0)
      (RadiusBounds.radiusLimitCoefficient_pos p hβ 1) hC
  refine ⟨B, hB, K, hK, c, hc, U, hU,
    min δ1 (min δ2 δr), lt_min hδ1 (lt_min hδ2 hδr), ?_⟩
  intro j0 hstart hsmall hslow hfast
  have hsmall1 := hsmall.trans_le (min_le_left δ1 (min δ2 δr))
  have hsmall2 := hsmall.trans_le ((min_le_right δ1 (min δ2 δr)).trans (min_le_left δ2 δr))
  have hsmallr := hsmall.trans_le ((min_le_right δ1 (min δ2 δr)).trans (min_le_right δ2 δr))
  have hsourceError := herror j0 hstart hsmall1 hslow hfast
  have hsourceFactor := hfactor j0 hstart hsmall2 hslow hfast
  let q := p.withStartIndex j0
  let u : ℕ → ℝ := fun j ↦ q.radiusRatio (2 * j)
  let v : ℕ → ℝ := fun j ↦ q.radiusRatio (2 * j + 1)
  have hu (j : ℕ) : 1 < u j := by
    exact (hsourceFactor j 0).1
  have hv (j : ℕ) : 1 < v j := by
    exact (hsourceFactor j 1).1
  have herr (j : ℕ) :
      |u j - 1 - RadiusBounds.radiusLimitCoefficient p 0 * scale p.beta j0 j ^ 2| ≤
          C * scale p.beta j0 j ^ (3 - p.beta) ∧
      |v j - 1 - RadiusBounds.radiusLimitCoefficient p 1 * scale p.beta j0 j ^ 2| ≤
          C * scale p.beta j0 j ^ (3 - p.beta) := by
    have hscaled := mul_le_mul_of_nonneg_right (le_max_left C1 C2)
      (Real.rpow_nonneg (scale_nonneg p.beta j0 j) (3 - p.beta))
    exact ⟨(hsourceError j 0).trans hscaled, (hsourceError j 1).trans hscaled⟩
  have hdefect (j : ℕ) :
      (RadiusBounds.radiusLimitCoefficient p 0 / 2) * scale p.beta j0 j ^ 2 ≤ u j - 1 ∧
      u j - 1 ≤ (RadiusBounds.radiusLimitCoefficient p 0 + C) * scale p.beta j0 j ^ 2 ∧
      (RadiusBounds.radiusLimitCoefficient p 1 / 2) * scale p.beta j0 j ^ 2 ≤ v j - 1 ∧
      v j - 1 ≤ (RadiusBounds.radiusLimitCoefficient p 1 + C) * scale p.beta j0 j ^ 2 := by
    have he := hsourceFactor j 0
    have ho := hsourceFactor j 1
    refine ⟨he.2.1, ?_, ho.2.1, ?_⟩
    · exact he.2.2.trans (mul_le_mul_of_nonneg_right
        (add_le_add (le_refl _) (le_max_right C1 C2)) (sq_nonneg _))
    · exact ho.2.2.trans (mul_le_mul_of_nonneg_right
        (add_le_add (le_refl _) (le_max_right C1 C2)) (sq_nonneg _))
  obtain ⟨hlog, henvelope⟩ := hpaired j0 hstart hsmallr u v hu hv herr hdefect
  have hallFactors (k : ℕ) : 1 < q.radiusRatio k := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · exact hu j
    · exact hv j
  have hradius : q.radius = Geometry.pairedRadius u v := q.radius_def
  exact ⟨hallFactors, hlog, hradius ▸ henvelope⟩

/-- Helper for lem:polar-geometry: the actual continuation, raw feasibility,
factor positivity, logarithm summability and radius envelope for one starting index. -/
structure SourceRadialData (p : Parameters) (j0 : ℕ) (N M B K c U : ℝ) : Prop where
  /-- Helper for lem:polar-continuation: the actual source trajectory satisfies the proved tube. -/
  trajectory : Continuation.TrajectoryBounds p j0 N M
  /-- Helper for lem:polar-continuation: every actual raw stage is feasible. -/
  feasible : ∀ k, Continuation.RawFeasible (p.withStartIndex j0) k
  /-- Helper for eq:polar-radii: every actual source factor exceeds one. -/
  factors : ∀ k, 1 < (p.withStartIndex j0).radiusRatio k
  /-- Helper for eq:polar-radii: the actual cycle logarithms are summable. -/
  logarithms : Summable (fun j ↦ Real.log ((p.withStartIndex j0).radiusRatio (2 * j) *
    (p.withStartIndex j0).radiusRatio (2 * j + 1)))
  /-- Helper for lem:polar-geometry: the actual radii obey all source scalar envelopes. -/
  radii : RadiusEnvelope p.beta j0 (p.withStartIndex j0).radius
    (RadiusBounds.radiusLimitCoefficient p 0) (RadiusBounds.radiusLimitCoefficient p 1)
    B K c U

/-- Helper for lem:polar-geometry: the constructed normalized source
trajectory generates paired-product radii with the manuscript's principal
radial coefficient and uniform excess and decrement bounds at every cycle. -/
theorem existsSourceRadialData (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1) :
    ∃ N > 0, ∃ M > 0, ∃ B > 0, ∃ K > 0, ∃ c > 0, ∃ U > 0,
      ∃ J : ℕ, 0 < J ∧ ∀ j0 : ℕ, J ≤ j0 → SourceRadialData p j0 N M B K c U := by
  obtain ⟨N, hN, M, hM, J0, hJ0, hcontinuation⟩ := Continuation.existsContinuation p hβ hβone
  obtain ⟨B, hB, K, hK, c, hc, U, hU, δ, hδ, hradius⟩ :=
    radiusEnvelopeOfActualTube p hβ hβone hM.le hN.le
  have hd := slowExponent_pos hβ hβone
  have hslowLimit : Tendsto (fun j0 : ℕ ↦ scale p.beta j0 0 ^ (1 - p.beta))
      atTop (𝓝 0) := by
    simpa only [scale_rpow_one_sub, Nat.add_zero, Function.comp_def] using
      (tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop
  obtain ⟨J1, hJ1⟩ := eventually_atTop.mp (hslowLimit.eventually (Iio_mem_nhds hδ))
  refine ⟨N, hN, M, hM, B, hB, K, hK, c, hc, U, hU,
    max J0 J1, hJ0.trans_le (le_max_left _ _), ?_⟩
  intro j0 hj0
  have hj00 : J0 ≤ j0 := (le_max_left _ _).trans hj0
  have hj01 : J1 ≤ j0 := (le_max_right _ _).trans hj0
  have hstart : 0 < j0 := hJ0.trans_le hj00
  obtain ⟨htube, hfeasible⟩ := hcontinuation j0 hj00
  have hslow (j : ℕ) :
      |((p.withStartIndex j0).normalizedEvenState j).1 - p.gammaStar| ≤
        M * scale p.beta j0 j ^ (1 - p.beta) := by
    simpa only [Continuation.slowError_def, Continuation.stateAt_def] using htube.slow_bound j
  have hfast (j : ℕ) : FastContraction.fixedNorm p.ell p.z
      (DFP.Polar.FastContraction.fastCoordinates ((p.withStartIndex j0).normalizedEvenState j) -
        FastContraction.evenFastReference p ((p.withStartIndex j0).normalizedEvenState j).1) ≤
      N * scale p.beta j0 j ^ (1 + p.beta) := by
    simpa only [Continuation.fastSize_def, Continuation.fastError_def, Continuation.stateAt_def,
      scale_rpow_one_add hβ, div_eq_mul_inv] using htube.fast_bound j
  obtain ⟨hfactors, hlog, henvelope⟩ := hradius j0 hstart (hJ1 j0 hj01) hslow hfast
  exact ⟨htube, hfeasible, hfactors, hlog, henvelope⟩

end DFP.Polar.General.RadiusProducts

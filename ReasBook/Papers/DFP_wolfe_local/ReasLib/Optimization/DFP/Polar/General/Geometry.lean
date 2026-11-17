module

public import ReasLib.Optimization.DFP.Polar.General.Scale
public import ReasLib.Optimization.DFP.Polar.General.InterpolationBounds
public import ReasLib.Optimization.DFP.Polar.PointGeometry

/-!
# Geometry of general power-law polar data

These estimates keep the scalar factor, angle, and coefficient hypotheses
separate from the matrix recurrence. Radial tail products are controlled by
their logarithms. Angular separation controls nearby points and accumulated
radial decrease controls returns after arbitrary numbers of turns.
-/

public section

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace DFP.Polar.General.Geometry

/-- Helper for lem:polar-geometry: the generalized scale tail equals the sum
of the corresponding powers of the actual scale sequence. This reusable
adapter exposes the defining sum across the scale module boundary. -/
theorem scaleTail_eq_tsum (β q : ℝ) (j0 j : ℕ) :
    scaleTail β q j0 j = ∑' n : ℕ, scale β j0 (j + n) ^ q := by
  rw [scaleTail_eq_rpowSum]
  apply tsum_congr
  intro n
  rw [scale_rpow]
  simp only [Nat.add_left_comm, Nat.add_comm]

/-- Helper for eq:polar-radii: a summable principal sequence and a summable
pointwise logarithmic error imply summability of the logarithms themselves.
This is a reusable scalar tail-product estimate. -/
theorem summableLog_of_error {w u v : ℕ → ℝ} {D C : ℝ}
    (hu : Summable u) (hv : Summable v)
    (herror : ∀ j, |Real.log (w j) - D * u j| ≤ C * v j) :
    Summable (fun j ↦ Real.log (w j)) := by
  have herr : Summable (fun j ↦ Real.log (w j) - D * u j) := by
    apply (hv.mul_left C).of_norm_bounded
    intro j
    simpa only [Real.norm_eq_abs] using herror j
  simpa only [sub_add_cancel] using herr.add (hu.mul_left D)

/-- Helper for eq:polar-radii: summing a pointwise logarithmic error controls
the logarithmic tail by the corresponding error tail.
This is a reusable scalar tail-product estimate. -/
theorem logTail_error {w u v : ℕ → ℝ} {D C : ℝ}
    (hu : Summable u) (hv : Summable v)
    (herror : ∀ j, |Real.log (w j) - D * u j| ≤ C * v j) (j : ℕ) :
    |RadiusProducts.logTail w j - D * ∑' n : ℕ, u (j + n)| ≤
      C * ∑' n : ℕ, v (j + n) := by
  have huTail : Summable (fun n ↦ u (j + n)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff j).mpr hu
  have hvTail : Summable (fun n ↦ v (j + n)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff j).mpr hv
  have hid : RadiusProducts.logTail w j - D * ∑' n : ℕ, u (j + n) =
      ∑' n : ℕ, (Real.log (w (j + n)) - D * u (j + n)) := by
    rw [RadiusProducts.logTail_def,
      (RadiusProducts.summableLogTail (summableLog_of_error hu hv herror) j).tsum_sub
        (huTail.mul_left D), tsum_mul_left]
  rw [hid]
  have hnorm (n : ℕ) : ‖Real.log (w (j + n)) - D * u (j + n)‖ ≤ C * v (j + n) := by
    simpa only [Real.norm_eq_abs] using herror (j + n)
  simpa only [Real.norm_eq_abs, tsum_mul_left] using
    tsum_of_norm_bounded (hvTail.mul_left C).hasSum hnorm

/-- Helper for lem:polar-geometry and eq:polar-radii: the source logarithmic
factor expansion has summable principal and error terms for `0 < β < 1`.
This is a reusable general-power radius-product estimate. -/
theorem summableLog_of_powerError {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    (j0 : ℕ) {w : ℕ → ℝ} {D C : ℝ}
    (herror : ∀ j, |Real.log (w j) - D * scale β j0 j ^ 2| ≤
      C * scale β j0 j ^ (3 - β)) : Summable (fun j ↦ Real.log (w j)) := by
  have hq : 1 + β < 3 - β := by
    linarith
  exact summableLog_of_error (summable_scale_sq hβ hβone j0)
    (summable_scale_rpow hβ hq j0) herror

/-- Helper for lem:polar-geometry and eq:polar-orders: logarithmic cycle
factors with leading term `D τ²` and error `C τ^(3-β)` have the source radial
tail coefficient `(1+β)D/(1-β)` and an error of order `τ^(2(1-β))`.
All constants are independent of the positive starting index.
This is a reusable general-power radius-product estimate. -/
theorem logTail_power_error {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    {j0 : ℕ} (hstart : 0 < j0) {w : ℕ → ℝ} {D C : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C)
    (herror : ∀ j, |Real.log (w j) - D * scale β j0 j ^ 2| ≤
      C * scale β j0 j ^ (3 - β)) (j : ℕ) :
    |RadiusProducts.logTail w j - ((1 + β) / (1 - β)) * D *
      scale β j0 j ^ (1 - β)| ≤
      (D + C * (((1 + β) / (2 * (1 - β))) + 1)) *
        scale β j0 j ^ (2 * (1 - β)) := by
  have hq : 1 + β < 3 - β := by
    linarith
  have htail := logTail_error (summable_scale_sq hβ hβone j0)
    (summable_scale_rpow hβ hq j0) herror j
  have hquadratic := scaleSqTail_error hβ hβone hstart j
  have hremainder := radialRemainderTail_le hβ hβone hstart j
  have hexponents : 2 * (1 - β) ≤ (2 : ℝ) := by
    linarith
  have hpower : scale β j0 j ^ 2 ≤ scale β j0 j ^ (2 * (1 - β)) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge
      (scale_pos β hstart j) (scale_le_one hβ hstart j) hexponents
  have hmain : |D * (scaleTail β 2 j0 j -
      ((1 + β) / (1 - β)) * scale β j0 j ^ (1 - β))| ≤
      D * scale β j0 j ^ (2 * (1 - β)) := by
    rw [abs_mul, abs_of_nonneg hD, abs_of_nonneg hquadratic.1]
    exact mul_le_mul_of_nonneg_left (hquadratic.2.trans hpower) hD
  have htailBound : |RadiusProducts.logTail w j - D * scaleTail β 2 j0 j| ≤
      C * (((1 + β) / (2 * (1 - β))) + 1) *
        scale β j0 j ^ (2 * (1 - β)) := by
    have htailPowers : |RadiusProducts.logTail w j - D * scaleTail β 2 j0 j| ≤
        C * scaleTail β (3 - β) j0 j := by
      simpa only [scaleTail_eq_tsum, Real.rpow_two] using htail
    apply htailPowers.trans
    exact (mul_le_mul_of_nonneg_left hremainder hC).trans_eq (mul_assoc _ _ _).symm
  calc
    |RadiusProducts.logTail w j - ((1 + β) / (1 - β)) * D *
        scale β j0 j ^ (1 - β)| =
        |(RadiusProducts.logTail w j - D * scaleTail β 2 j0 j) +
          D * (scaleTail β 2 j0 j -
            ((1 + β) / (1 - β)) * scale β j0 j ^ (1 - β))| := by
      ring_nf
    _ ≤ |RadiusProducts.logTail w j - D * scaleTail β 2 j0 j| +
        |D * (scaleTail β 2 j0 j -
          ((1 + β) / (1 - β)) * scale β j0 j ^ (1 - β))| := abs_add_le _ _
    _ ≤ C * (((1 + β) / (2 * (1 - β))) + 1) *
          scale β j0 j ^ (2 * (1 - β)) +
        D * scale β j0 j ^ (2 * (1 - β)) := add_le_add htailBound hmain
    _ = (D + C * (((1 + β) / (2 * (1 - β))) + 1)) *
        scale β j0 j ^ (2 * (1 - β)) := by
      ring

/-- Helper for eq:polar-W-expansion: the source scalar factor expansion gives
positive quadratic lower and upper factor defects once the higher-order error
is small relative to its principal coefficient.
This is a reusable general-power scalar estimate. -/
theorem factor_sub_one_bounds {β τ w D C : ℝ} (hβone : β < 1)
    (hτ : 0 < τ) (hτone : τ ≤ 1) (hC : 0 ≤ C)
    (hsmall : C * τ ^ (1 - β) ≤ D / 2)
    (herror : |w - 1 - D * τ ^ 2| ≤ C * τ ^ (3 - β)) :
    (D / 2) * τ ^ 2 ≤ w - 1 ∧ w - 1 ≤ (D + C) * τ ^ 2 := by
  have hexponent : 3 - β = (2 : ℝ) + (1 - β) := by
    ring
  have hpower : τ ^ (3 - β) = τ ^ 2 * τ ^ (1 - β) := by
    rw [hexponent, Real.rpow_add hτ, Real.rpow_two]
  have hslowOne := Real.rpow_le_one hτ.le hτone (sub_pos.mpr hβone).le
  have hsmallPower := mul_le_mul_of_nonneg_right hsmall (sq_nonneg τ)
  have herrorPower := mul_le_mul_of_nonneg_left hslowOne hC
  have habs := abs_le.mp herror
  rw [hpower] at habs
  constructor
  · nlinarith
  · nlinarith

/-- Helper for eq:polar-radii: a source factor expansion with error
`C τ^(3-β)` has the same logarithmic principal term and a uniform error of
that order. This reusable estimate derives the logarithmic input from the
original scalar recurrence factor rather than assuming a logarithm expansion. -/
theorem logFactor_power_error {β τ w D C : ℝ} (hβ : 0 < β) (hβone : β < 1)
    (hτ : 0 < τ) (hτone : τ ≤ 1) (hC : 0 ≤ C) (hw : 1 ≤ w)
    (herror : |w - 1 - D * τ ^ 2| ≤ C * τ ^ (3 - β)) :
    |Real.log w - D * τ ^ 2| ≤ (C + (D + C) ^ 2) * τ ^ (3 - β) := by
  have hfirstExponents : (2 : ℝ) ≤ 3 - β := by
    linarith
  have hfirstPower : τ ^ (3 - β) ≤ τ ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_ge hτ hτone hfirstExponents
  have hupper : w - 1 ≤ (D + C) * τ ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hfirstPower hC
    linarith [(abs_le.mp herror).2]
  have hsquare := pow_le_pow_left₀ (sub_nonneg.mpr hw) hupper 2
  have hsecondExponents : 3 - β ≤ (4 : ℝ) := by
    linarith
  have hsecondPower : τ ^ 4 ≤ τ ^ (3 - β) := by
    rw [← Real.rpow_natCast τ 4]
    exact Real.rpow_le_rpow_of_exponent_ge hτ hτone hsecondExponents
  have hquadratic : (w - 1) ^ 2 ≤ (D + C) ^ 2 * τ ^ (3 - β) := by
    calc
      (w - 1) ^ 2 ≤ ((D + C) * τ ^ 2) ^ 2 := hsquare
      _ = (D + C) ^ 2 * τ ^ 4 := by
        ring
      _ ≤ (D + C) ^ 2 * τ ^ (3 - β) :=
        mul_le_mul_of_nonneg_left hsecondPower (sq_nonneg _)
  calc
    |Real.log w - D * τ ^ 2| =
        |(Real.log w - (w - 1)) + (w - 1 - D * τ ^ 2)| := by
      ring_nf
    _ ≤ |Real.log w - (w - 1)| + |w - 1 - D * τ ^ 2| := abs_add_le _ _
    _ ≤ (w - 1) ^ 2 + C * τ ^ (3 - β) :=
      add_le_add (RadiusProducts.abs_log_sub_linear_le_sq hw) herror
    _ ≤ (C + (D + C) ^ 2) * τ ^ (3 - β) := by
      linarith

/-- Helper for eq:polar-radii: the logarithm of the product of the two cycle
factors has the sum of their quadratic coefficients and the sum of their
logarithmic error bounds. This reusable identity retains both source phases. -/
theorem cycleLog_error {u v τ q D₀ D₁ C₀ C₁ : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hfirst : |Real.log u - D₀ * τ ^ 2| ≤ C₀ * τ ^ q)
    (hsecond : |Real.log v - D₁ * τ ^ 2| ≤ C₁ * τ ^ q) :
    |Real.log (u * v) - (D₀ + D₁) * τ ^ 2| ≤ (C₀ + C₁) * τ ^ q := by
  rw [Real.log_mul hu.ne' hv.ne']
  calc
    |Real.log u + Real.log v - (D₀ + D₁) * τ ^ 2| =
        |(Real.log u - D₀ * τ ^ 2) + (Real.log v - D₁ * τ ^ 2)| := by
      ring_nf
    _ ≤ |Real.log u - D₀ * τ ^ 2| + |Real.log v - D₁ * τ ^ 2| := abs_add_le _ _
    _ ≤ C₀ * τ ^ q + C₁ * τ ^ q := add_le_add hfirst hsecond
    _ = (C₀ + C₁) * τ ^ q := by
      ring

/-- Helper for lem:polar-geometry: exponentiating a small logarithmic
linear expansion preserves its principal term with a quadratic error.
This is a reusable scalar exponential estimate. -/
theorem exp_linear_error {z t L K : ℝ} (ht : 0 ≤ t) (htone : t ≤ 1)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (herror : |z - L * t| ≤ K * t ^ 2) (hsmall : (L + K) * t ≤ 1) :
    |Real.exp z - 1 - L * t| ≤ ((L + K) ^ 2 + K) * t ^ 2 := by
  have hsquare : t ^ 2 ≤ t := by
    nlinarith
  have hbound : |z| ≤ (L + K) * t := by
    calc
      |z| = |(z - L * t) + L * t| := by
        ring_nf
      _ ≤ |z - L * t| + |L * t| := abs_add_le _ _
      _ ≤ K * t ^ 2 + L * t := by
        rw [abs_of_nonneg (mul_nonneg hL ht)]
        exact add_le_add herror le_rfl
      _ ≤ (L + K) * t := by
        have hscaled := mul_le_mul_of_nonneg_left hsquare hK
        nlinarith
  have hexp := Real.abs_exp_sub_one_sub_id_le (hbound.trans hsmall)
  have hzSquare : z ^ 2 ≤ (L + K) ^ 2 * t ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg z) hbound 2
    simpa only [sq_abs, mul_pow] using h
  calc
    |Real.exp z - 1 - L * t| = |(Real.exp z - 1 - z) + (z - L * t)| := by
      ring_nf
    _ ≤ |Real.exp z - 1 - z| + |z - L * t| := abs_add_le _ _
    _ ≤ z ^ 2 + K * t ^ 2 := add_le_add hexp herror
    _ ≤ ((L + K) ^ 2 + K) * t ^ 2 := by
      linarith

/-- Helper for lem:polar-geometry and eq:polar-orders: the general radial
tail product has the source expansion with principal coefficient
`(1+β)D/(1-β)` and error of order `τ^(2(1-β))`. The smallness threshold and
error constant are uniform in the starting index and in the factor sequence.
This is a reusable general-power radius-product theorem. -/
theorem tailProduct_power_error {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    {j0 : ℕ} (hstart : 0 < j0) {w : ℕ → ℝ} {D C : ℝ}
    (hw : ∀ j, 0 < w j) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (herror : ∀ j, |Real.log (w j) - D * scale β j0 j ^ 2| ≤
      C * scale β j0 j ^ (3 - β))
    (hsmall : (((1 + β) / (1 - β)) * D +
        (D + C * (((1 + β) / (2 * (1 - β))) + 1))) * scale β j0 0 ^ (1 - β) ≤ 1)
    (j : ℕ) :
    |RadiusProducts.tailProduct w j - 1 - ((1 + β) / (1 - β)) * D *
      scale β j0 j ^ (1 - β)| ≤
      (((((1 + β) / (1 - β)) * D +
        (D + C * (((1 + β) / (2 * (1 - β))) + 1))) ^ 2) +
        (D + C * (((1 + β) / (2 * (1 - β))) + 1))) *
          scale β j0 j ^ (2 * (1 - β)) := by
  have hslow : 0 < 1 - β := sub_pos.mpr hβone
  have ht := scale_pos β hstart j
  have hL : 0 ≤ ((1 + β) / (1 - β)) * D := by
    positivity
  have hK : 0 ≤ D + C * (((1 + β) / (2 * (1 - β))) + 1) := by
    positivity
  have hsquare : (scale β j0 j ^ (1 - β)) ^ 2 =
      scale β j0 j ^ (2 * (1 - β)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hlog : |RadiusProducts.logTail w j - ((1 + β) / (1 - β)) * D *
      scale β j0 j ^ (1 - β)| ≤
      (D + C * (((1 + β) / (2 * (1 - β))) + 1)) *
        (scale β j0 j ^ (1 - β)) ^ 2 := by
    rw [hsquare]
    exact logTail_power_error hβ hβone hstart hD hC herror j
  have hscale := Real.rpow_le_rpow ht.le (scale_antitone hβ hstart (Nat.zero_le j)) hslow.le
  have hsmallAt := (mul_le_mul_of_nonneg_left hscale (add_nonneg hL hK)).trans hsmall
  have hexp := exp_linear_error (Real.rpow_nonneg ht.le _)
    (Real.rpow_le_one ht.le (scale_le_one hβ hstart j) hslow.le) hL hK hlog hsmallAt
  rw [← RadiusProducts.tailProduct_eq_exp hw (summableLog_of_powerError hβ hβone j0 herror)]
    at hexp
  simpa only [hsquare] using hexp

/-- Helper for eq:polar-radii: dividing the paired tail product by its first
factor leaves the second factor times the next paired tail product. This
reusable identity gives the source odd-radius recurrence without expanding
an infinite product. -/
theorem tailProduct_div_firstFactor {u v : ℕ → ℝ}
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hlog : Summable (fun j ↦ Real.log (u j * v j))) (j : ℕ) :
    RadiusProducts.tailProduct (fun n ↦ u n * v n) j / u j =
      v j * RadiusProducts.tailProduct (fun n ↦ u n * v n) (j + 1) := by
  have hpositive (j : ℕ) : 0 < u j * v j := mul_pos (hu j) (hv j)
  rw [RadiusProducts.tailProduct_shift hpositive hlog j]
  field_simp [(hu j).ne']

/-- Helper for eq:polar-radii: the source two-phase radii constructed from
the paired factor tail product, with the odd radius obtained by dividing by
the first factor. This reusable construction is independent of any parameter
structure or matrix recurrence. -/
def pairedRadius (u v : ℕ → ℝ) : ℕ → ℝ :=
  DFP.twoStepSequence (RadiusProducts.tailProduct (fun n ↦ u n * v n))
    (fun j ↦ RadiusProducts.tailProduct (fun n ↦ u n * v n) j / u j)

/-- Helper for eq:polar-radii: the exact interleaving formula for the general
paired-factor radius. This is the reusable construction interface. -/
theorem pairedRadius_def (u v : ℕ → ℝ) :
    pairedRadius u v =
      DFP.twoStepSequence (RadiusProducts.tailProduct (fun n ↦ u n * v n))
        (fun j ↦ RadiusProducts.tailProduct (fun n ↦ u n * v n) j / u j) := by
  rfl

/-- Helper for eq:polar-radii: each even paired-factor radius is precisely
the original paired tail product. This is the reusable even-phase interface. -/
theorem pairedRadius_even (u v : ℕ → ℝ) (j : ℕ) :
    pairedRadius u v (2 * j) = RadiusProducts.tailProduct (fun n ↦ u n * v n) j := by
  rw [pairedRadius_def, DFP.twoStepSequence_even]

/-- Helper for eq:polar-radii: each odd paired-factor radius is the even
tail product divided by the first factor. This is the reusable odd-phase
interface. -/
theorem pairedRadius_odd (u v : ℕ → ℝ) (j : ℕ) :
    pairedRadius u v (2 * j + 1) =
      RadiusProducts.tailProduct (fun n ↦ u n * v n) j / u j := by
  rw [pairedRadius_def, DFP.twoStepSequence_odd]

/-- Helper for eq:polar-radii: the odd paired-factor radius is the second
factor times the next even tail. This is a reusable finite recurrence for the
infinite-product construction. -/
theorem pairedRadius_odd_eq_mul {u v : ℕ → ℝ}
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hlog : Summable (fun j ↦ Real.log (u j * v j))) (j : ℕ) :
    pairedRadius u v (2 * j + 1) =
      v j * RadiusProducts.tailProduct (fun n ↦ u n * v n) (j + 1) := by
  rw [pairedRadius_odd, tailProduct_div_firstFactor hu hv hlog j]

/-- Helper for eq:polar-radii: the full paired-factor radius satisfies the
source radial multiplicative recurrence at both phases.
This is a reusable finite interface for the tail-product construction. -/
theorem pairedRadius_recurrence {u v : ℕ → ℝ}
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hlog : Summable (fun j ↦ Real.log (u j * v j))) (k : ℕ) :
    pairedRadius u v k = DFP.twoStepSequence u v k * pairedRadius u v (k + 1) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [pairedRadius_even, pairedRadius_odd, DFP.twoStepSequence_even]
    field_simp [(hu j).ne']
  · have hindex : 2 * j + 1 + 1 = 2 * (j + 1) := by
      omega
    rw [hindex, pairedRadius_odd_eq_mul hu hv hlog, pairedRadius_even,
      DFP.twoStepSequence_odd]

/-- Helper for eq:polar-radii: paired factors strictly above one give every
source radius strictly above one. This is reusable positivity for the general
tail-product radius construction. -/
theorem pairedRadius_gt_one {u v : ℕ → ℝ}
    (hu : ∀ j, 1 < u j) (hv : ∀ j, 1 < v j)
    (hlog : Summable (fun j ↦ Real.log (u j * v j))) (k : ℕ) :
    1 < pairedRadius u v k := by
  have huPos (j : ℕ) : 0 < u j := zero_lt_one.trans (hu j)
  have hvPos (j : ℕ) : 0 < v j := zero_lt_one.trans (hv j)
  have hcycle (j : ℕ) : 1 < u j * v j := by
    exact (hu j).trans (lt_mul_of_one_lt_right (huPos j) (hv j))
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [pairedRadius_even]
    exact RadiusProducts.tailProduct_gt_one hcycle hlog j
  · rw [pairedRadius_odd_eq_mul huPos hvPos hlog]
    have htail := RadiusProducts.tailProduct_gt_one hcycle hlog (j + 1)
    exact htail.trans (lt_mul_of_one_lt_left (zero_lt_one.trans htail) (hv j))

/-- Helper for eq:polar-radii: factors strictly above one make the complete
paired-factor radius sequence strictly decreasing.
This is reusable monotonicity for the general tail-product construction. -/
theorem pairedRadius_strictAnti {u v : ℕ → ℝ}
    (hu : ∀ j, 1 < u j) (hv : ∀ j, 1 < v j)
    (hlog : Summable (fun j ↦ Real.log (u j * v j))) : StrictAnti (pairedRadius u v) := by
  have huPos (j : ℕ) : 0 < u j := zero_lt_one.trans (hu j)
  have hvPos (j : ℕ) : 0 < v j := zero_lt_one.trans (hv j)
  have hfactor (k : ℕ) : 1 < DFP.twoStepSequence u v k := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · simpa only [DFP.twoStepSequence_even] using hu j
    · simpa only [DFP.twoStepSequence_odd] using hv j
  apply strictAnti_nat_of_succ_lt
  intro k
  rw [pairedRadius_recurrence huPos hvPos hlog k]
  exact lt_mul_of_one_lt_left (zero_lt_one.trans (pairedRadius_gt_one hu hv hlog (k + 1)))
    (hfactor k)

/-- Helper for eq:polar-radii and lem:polar-geometry: every radius of the
paired-factor construction tends to one. Odd radii are squeezed below their
own even tail and above one; no radial convergence premise is assumed.
This is a reusable convergence theorem for the general radius construction. -/
theorem pairedRadius_tendsto_one {u v : ℕ → ℝ}
    (hu : ∀ j, 1 < u j) (hv : ∀ j, 1 < v j)
    (hlog : Summable (fun j ↦ Real.log (u j * v j))) :
    Tendsto (pairedRadius u v) atTop (𝓝 1) := by
  have hpositive (j : ℕ) : 0 < u j * v j :=
    mul_pos (zero_lt_one.trans (hu j)) (zero_lt_one.trans (hv j))
  have heven := (RadiusProducts.tailProduct_tendsto_one hpositive hlog).comp
    AngularGeometry.halfIndex_tendsto
  have hupper (k : ℕ) : pairedRadius u v k ≤
      RadiusProducts.tailProduct (fun n ↦ u n * v n) (k / 2) := by
    have hindex : 2 * (k / 2) ≤ k := by
      omega
    simpa only [pairedRadius_even] using (pairedRadius_strictAnti hu hv hlog).antitone hindex
  have hdiff : Tendsto (fun k ↦ pairedRadius u v k - 1) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro k
      exact sub_nonneg.mpr (pairedRadius_gt_one hu hv hlog k).le
    · intro k
      exact sub_le_sub_right (hupper k) 1
    · simpa only [Function.comp_def, sub_self] using heven.sub_const 1
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const 1

/-- Helper for eq:polar-orders: dividing a nonnegative bounded radius by a
factor at least one changes a linear radial expansion by at most the factor
defect times the radius bound. This reusable scalar estimate controls the odd
phase from the even phase without changing the principal coefficient. -/
theorem divisorRadius_linear_error {R w t L K B C : ℝ}
    (hR : 0 ≤ R) (hRupper : R ≤ B) (hw : 1 ≤ w)
    (herror : |R - 1 - L * t| ≤ K * t ^ 2) (hdefect : w - 1 ≤ C * t ^ 2) :
    |R / w - 1 - L * t| ≤ (K + B * C) * t ^ 2 := by
  have hwpos : 0 < w := zero_lt_one.trans_le hw
  have hB : 0 ≤ B := hR.trans hRupper
  have hdefectNonneg : 0 ≤ w - 1 := sub_nonneg.mpr hw
  have hidentity : R / w - R = -(R * (w - 1) / w) := by
    field_simp
    ring
  have hbound : |R / w - R| ≤ B * C * t ^ 2 := by
    calc
      |R / w - R| = R * (w - 1) / w := by
        rw [hidentity, abs_neg, abs_div,
          abs_of_nonneg (mul_nonneg hR hdefectNonneg), abs_of_pos hwpos]
      _ ≤ R * (w - 1) := div_le_self (mul_nonneg hR hdefectNonneg) hw
      _ ≤ B * (w - 1) := mul_le_mul_of_nonneg_right hRupper hdefectNonneg
      _ ≤ B * (C * t ^ 2) := mul_le_mul_of_nonneg_left hdefect hB
      _ = B * C * t ^ 2 := by
        ring
  calc
    |R / w - 1 - L * t| = |(R / w - R) + (R - 1 - L * t)| := by
      ring_nf
    _ ≤ |R / w - R| + |R - 1 - L * t| := abs_add_le _ _
    _ ≤ B * C * t ^ 2 + K * t ^ 2 := add_le_add hbound herror
    _ = (K + B * C) * t ^ 2 := by
      ring

/-- Helper for lem:polar-geometry and eq:polar-orders: a quadratic source
factor defect perturbs the even-radius power expansion only at the allowed
error order `τ^(2(1-β))`. Thus the same principal radial coefficient holds
for the odd radius obtained by dividing by that factor.
This is a reusable general-power radius estimate. -/
theorem quotientRadius_power_error {β τ R w L K B C : ℝ}
    (hβ : 0 < β) (hτ : 0 < τ) (hτone : τ ≤ 1) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hRupper : R ≤ B) (hw : 1 ≤ w)
    (herror : |R - 1 - L * τ ^ (1 - β)| ≤ K * τ ^ (2 * (1 - β)))
    (hdefect : w - 1 ≤ C * τ ^ 2) :
    |R / w - 1 - L * τ ^ (1 - β)| ≤ (K + B * C) * τ ^ (2 * (1 - β)) := by
  have hexponents : 2 * (1 - β) ≤ (2 : ℝ) := by
    linarith
  have hpower : τ ^ 2 ≤ τ ^ (2 * (1 - β)) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_ge hτ hτone hexponents
  have hsquare : (τ ^ (1 - β)) ^ 2 = τ ^ (2 * (1 - β)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hτ.le]
    congr 1
    ring
  have hfactor : w - 1 ≤ C * (τ ^ (1 - β)) ^ 2 := by
    rw [hsquare]
    exact hdefect.trans (mul_le_mul_of_nonneg_left hpower hC)
  have hlinear : |R - 1 - L * τ ^ (1 - β)| ≤ K * (τ ^ (1 - β)) ^ 2 := by
    rwa [hsquare]
  have h := divisorRadius_linear_error hR hRupper hw hlinear hfactor
  simpa only [hsquare] using h

/-- Helper for eq:polar-orders: scalar factor defects comparable to `τ²`,
together with the exact radial recurrence and uniform radius bounds, give
two-sided radial decrements at the same scale.
This is a reusable scalar recurrence estimate. -/
theorem radius_drop_bounds_of_factor_bounds {R S w τ c C B : ℝ}
    (hS : 1 ≤ S) (hSupper : S ≤ B) (hc : 0 ≤ c)
    (hlower : c * τ ^ 2 ≤ w - 1) (hupper : w - 1 ≤ C * τ ^ 2)
    (hrecurrence : R = w * S) :
    c * τ ^ 2 ≤ R - S ∧ R - S ≤ B * C * τ ^ 2 := by
  have hdefect : 0 ≤ w - 1 := (mul_nonneg hc (sq_nonneg τ)).trans hlower
  have hB : 0 ≤ B := zero_le_one.trans (hS.trans hSupper)
  have hradial : R - S = S * (w - 1) := by
    rw [hrecurrence]
    ring
  rw [hradial]
  constructor
  · exact hlower.trans (le_mul_of_one_le_left hdefect hS)
  · calc
      S * (w - 1) ≤ B * (w - 1) := mul_le_mul_of_nonneg_right hSupper hdefect
      _ ≤ B * (C * τ ^ 2) := mul_le_mul_of_nonneg_left hupper hB
      _ = B * C * τ ^ 2 := by
        ring

/-- Helper for lem:polar-geometry: polar points with freely prescribed scalar
radii and unreduced real angles. This reusable construction is independent of
the matrix recurrence and of any parameter structure. -/
def point (r θ : ℕ → ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  r k • polarUnit (θ k)

/-- Helper for lem:polar-geometry: the scalar-times-unit-direction formula for
the general polar point. This is the reusable point construction interface. -/
theorem point_def (r θ : ℕ → ℝ) (k : ℕ) :
    point r θ k = r k • polarUnit (θ k) := by
  rfl

/-- Helper for lem:polar-geometry: nonnegative polar radii are the Euclidean
point norms. This is a reusable radial-distance bridge. -/
theorem point_norm {r θ : ℕ → ℝ} (k : ℕ) (hr : 0 ≤ r k) : ‖point r θ k‖ = r k := by
  rw [point_def, norm_smul, PointGeometry.polarUnit_norm, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_one]

/-- Helper for lem:polar-geometry: radial displacement is bounded above by
the Euclidean point distance. This is a reusable radial-distance bridge. -/
theorem radius_sub_le_point_distance {r θ : ℕ → ℝ} (k m : ℕ)
    (hk : 0 ≤ r k) (hm : 0 ≤ r m) : r k - r m ≤ ‖point r θ m - point r θ k‖ := by
  have h := norm_sub_norm_le (point r θ k) (point r θ m)
  rwa [point_norm k hk, point_norm m hm, norm_sub_rev] at h

/-- Helper for lem:polar-geometry: the inverse source scale is no larger
than its positive cycle index. This is reusable support for the near-return
window size and holds for every `β > 0`. -/
theorem inv_scale_le_index {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    (scale β j0 j)⁻¹ ≤ ((j0 + j : ℕ) : ℝ) := by
  have hindex : (0 : ℝ) < ((j0 + j : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.add_pos_left hstart j)
  have hscale := (sq_le_sq₀ (inv_nonneg.mpr hindex.le) (scale_nonneg β j0 j)).mp
    (inv_sq_le_scale_sq hβ hstart j)
  simpa only [inv_inv] using
    (inv_le_inv₀ (scale_pos β hstart j) (inv_pos.mpr hindex)).mpr hscale

/-- Helper for lem:polar-geometry: doubling a positive cycle index decreases
the source scale by at most a factor of two. This reusable comparison is
uniform in the starting index and every `β > 0`. -/
theorem scale_lower_of_index_le_two {β : ℝ} (hβ : 0 < β) {j0 : ℕ}
    (hstart : 0 < j0) (i j : ℕ) (hindices : j0 + j ≤ 2 * (j0 + i)) :
    (1 / 2 : ℝ) * scale β j0 i ≤ scale β j0 j := by
  have hden : 0 < 1 + β := by
    positivity
  have hexponentLower : (-1 : ℝ) ≤ -1 / (1 + β) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hexponentNonpos : -1 / (1 + β) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr zero_le_one) hden.le
  have htwoNonneg : (0 : ℝ) ≤ 2 := by
    norm_num
  have honeTwo : (1 : ℝ) ≤ 2 := by
    norm_num
  have hfactor : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-1 / (1 + β)) := by
    simpa only [Real.rpow_neg_one, one_div] using
      Real.rpow_le_rpow_of_exponent_le honeTwo hexponentLower
  have hrealIndices : ((j0 + j : ℕ) : ℝ) ≤ 2 * ((j0 + i : ℕ) : ℝ) := by
    exact_mod_cast hindices
  rw [scale_def, scale_def]
  calc
    (1 / 2 : ℝ) * ((j0 + i : ℕ) : ℝ) ^ (-1 / (1 + β)) ≤
        (2 : ℝ) ^ (-1 / (1 + β)) * ((j0 + i : ℕ) : ℝ) ^ (-1 / (1 + β)) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = (2 * ((j0 + i : ℕ) : ℝ)) ^ (-1 / (1 + β)) :=
      (Real.mul_rpow htwoNonneg (Nat.cast_nonneg _)).symm
    _ ≤ ((j0 + j : ℕ) : ℝ) ^ (-1 / (1 + β)) :=
      Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr (Nat.add_pos_left hstart j))
        hrealIndices hexponentNonpos

/-- Helper for lem:polar-geometry: the source near-return window contains
`⌊η / τ⌋₊` steps at the initial point scale. This reusable window depends only
on the generalized source scale and a fixed angular cutoff. -/
def nearWindow (β : ℝ) (j0 : ℕ) (η : ℝ) (k : ℕ) : ℕ :=
  ⌊η / scale β j0 (k / 2)⌋₊

/-- Helper for lem:polar-geometry: the explicit floor formula for the
general near-return window. This is its reusable construction interface. -/
theorem nearWindow_def (β : ℝ) (j0 : ℕ) (η : ℝ) (k : ℕ) :
    nearWindow β j0 η k = ⌊η / scale β j0 (k / 2)⌋₊ := by
  rfl

/-- Helper for lem:polar-geometry: a near-return window spans at most `η`
in units of its initial scale. This is reusable floor-window support. -/
theorem nearWindow_mul_scale_le {β : ℝ} {j0 : ℕ} (hstart : 0 < j0)
    {η : ℝ} (hη : 0 ≤ η) (k : ℕ) :
    (nearWindow β j0 η k : ℝ) * scale β j0 (k / 2) ≤ η := by
  have ht := scale_pos β hstart (k / 2)
  have hfloor := Nat.floor_le (div_nonneg hη ht.le)
  rw [← nearWindow_def] at hfloor
  exact (mul_le_mul_of_nonneg_right hfloor ht.le).trans_eq (div_mul_cancel₀ η ht.ne')

/-- Helper for lem:polar-geometry: with `η ≤ 1`, the near-return window has
at most as many steps as the current cycle index. This reusable bound controls
the change of scale throughout the window. -/
theorem nearWindow_le_index {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0)
    {η : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1) (k : ℕ) :
    nearWindow β j0 η k ≤ j0 + k / 2 := by
  have ht := scale_pos β hstart (k / 2)
  have hfloor := Nat.floor_le (div_nonneg hη ht.le)
  have hquotient : η / scale β j0 (k / 2) ≤ (scale β j0 (k / 2))⁻¹ := by
    simpa only [one_div] using div_le_div_of_nonneg_right hηone ht.le
  have hreal : (nearWindow β j0 η k : ℝ) ≤ ((j0 + k / 2 : ℕ) : ℝ) := by
    rw [nearWindow_def]
    exact hfloor.trans (hquotient.trans (inv_scale_le_index hβ hstart (k / 2)))
  exact_mod_cast hreal

/-- Helper for lem:polar-geometry: once the initial scale is at most `η/2`,
the source floor window retains at least half its defining length.
This is reusable floor-window support. -/
theorem nearWindow_mul_scale_lower {β : ℝ} (hβ : 0 < β) {j0 : ℕ}
    (hstart : 0 < j0) {η : ℝ} (hsmall : scale β j0 0 ≤ η / 2) (k : ℕ) :
    η / 2 ≤ (nearWindow β j0 η k : ℝ) * scale β j0 (k / 2) := by
  have ht := scale_pos β hstart (k / 2)
  have htsmall := (scale_antitone hβ hstart (Nat.zero_le (k / 2))).trans hsmall
  have hfloor := Nat.lt_floor_add_one (η / scale β j0 (k / 2))
  rw [← nearWindow_def] at hfloor
  have hmul := mul_lt_mul_of_pos_right hfloor ht
  rw [div_mul_cancel₀ η ht.ne'] at hmul
  nlinarith

/-- Helper for lem:polar-geometry: all source scales in a near-return window
lie between one half and one times the initial scale. This reusable estimate
depends only on `β > 0`, the positive starting index, and `0 ≤ η ≤ 1`. -/
theorem scale_nearWindow_bounds {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0)
    {η : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1) (k l : ℕ)
    (hkl : k ≤ l) (hl : l ≤ k + nearWindow β j0 η k) :
    (1 / 2 : ℝ) * scale β j0 (k / 2) ≤ scale β j0 (l / 2) ∧
      scale β j0 (l / 2) ≤ scale β j0 (k / 2) := by
  have hwindow := nearWindow_le_index hβ hstart hη hηone k
  have hindices : j0 + l / 2 ≤ 2 * (j0 + k / 2) := by
    omega
  exact ⟨scale_lower_of_index_le_two hβ hstart (k / 2) (l / 2) hindices,
    scale_antitone hβ hstart (Nat.div_le_div_right hkl)⟩

/-- Helper for lem:polar-geometry: scalar angular increments comparable to
the source scales give two-sided angular displacement estimates inside each
near-return window. This reusable estimate follows by summing increments. -/
theorem nearWindow_angle_bounds {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0)
    {η a b : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {θ : ℕ → ℝ}
    (hlower : ∀ k, a * scale β j0 (k / 2) ≤ θ (k + 1) - θ k)
    (hupper : ∀ k, θ (k + 1) - θ k ≤ b * scale β j0 (k / 2))
    (k m : ℕ) (hkm : k ≤ m) (hwindow : m - k ≤ nearWindow β j0 η k) :
    (a / 2) * ((m - k : ℕ) : ℝ) * scale β j0 (k / 2) ≤ θ m - θ k ∧
      θ m - θ k ≤ b * ((m - k : ℕ) : ℝ) * scale β j0 (k / 2) := by
  have hlocal (l : ℕ) (hl : l ∈ Finset.Ico k m) :
      (a / 2) * scale β j0 (k / 2) ≤ θ (l + 1) - θ l ∧
        θ (l + 1) - θ l ≤ b * scale β j0 (k / 2) := by
    have hlBounds := Finset.mem_Ico.mp hl
    have hlWindow : l ≤ k + nearWindow β j0 η k := by
      omega
    have hscales := scale_nearWindow_bounds hβ hstart hη hηone k l hlBounds.1 hlWindow
    constructor
    · have hscaled := mul_le_mul_of_nonneg_left hscales.1 ha
      nlinarith [hlower l]
    · exact (hupper l).trans (mul_le_mul_of_nonneg_left hscales.2 hb)
  have hsumLower := Finset.sum_le_sum (fun l hl ↦ (hlocal l hl).1)
  have hsumUpper := Finset.sum_le_sum (fun l hl ↦ (hlocal l hl).2)
  rw [Finset.sum_Ico_sub θ hkm] at hsumLower hsumUpper
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico] at hsumLower hsumUpper
  constructor
  · nlinarith [hsumLower]
  · nlinarith [hsumUpper]

/-- Helper for eq:polar-separation: within a near-return window, the exact
polar chord is bounded below by the number of steps times the source scale.
This reusable bound assumes only scalar radius and angular-increment bounds. -/
theorem near_point_separation {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0)
    {η a b : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hspan : b * η ≤ Real.pi) {r θ : ℕ → ℝ} (hr : ∀ k, 1 ≤ r k)
    (hlower : ∀ k, a * scale β j0 (k / 2) ≤ θ (k + 1) - θ k)
    (hupper : ∀ k, θ (k + 1) - θ k ≤ b * scale β j0 (k / 2))
    (k m : ℕ) (hkm : k < m) (hwindow : m - k ≤ nearWindow β j0 η k) :
    (a / Real.pi) * ((m - k : ℕ) : ℝ) * scale β j0 (k / 2) ≤
      ‖point r θ m - point r θ k‖ := by
  have hangle := nearWindow_angle_bounds hβ hstart hη hηone ha hb hlower hupper
    k m hkm.le hwindow
  have hcount : ((m - k : ℕ) : ℝ) * scale β j0 (k / 2) ≤ η := by
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hwindow)
      (scale_nonneg β j0 (k / 2))).trans (nearWindow_mul_scale_le hstart hη k)
  have hangleNonneg : 0 ≤ θ m - θ k := by
    have hnonneg : 0 ≤ (a / 2) * ((m - k : ℕ) : ℝ) * scale β j0 (k / 2) :=
      mul_nonneg (mul_nonneg (div_nonneg ha zero_le_two) (Nat.cast_nonneg _))
        (scale_nonneg β j0 (k / 2))
    exact hnonneg.trans hangle.1
  have hangleSpan : θ m - θ k ≤ Real.pi := by
    have hscaled := mul_le_mul_of_nonneg_left hcount hb
    nlinarith [hangle.2]
  have hchord := PointGeometry.polarChord_angle_lower (r m) (r k) (θ m) (θ k)
    (hr m) (hr k) hangleNonneg hangleSpan
  have hcoefficient : 0 ≤ 2 / Real.pi := (div_pos zero_lt_two Real.pi_pos).le
  calc
    (a / Real.pi) * ((m - k : ℕ) : ℝ) * scale β j0 (k / 2) =
        (2 / Real.pi) * ((a / 2) * ((m - k : ℕ) : ℝ) * scale β j0 (k / 2)) := by
      ring
    _ ≤ (2 / Real.pi) * (θ m - θ k) :=
      mul_le_mul_of_nonneg_left hangle.1 hcoefficient
    _ ≤ ‖point r θ m - point r θ k‖ := by
      rw [point_def, point_def]
      exact hchord

/-- Helper for lem:polar-geometry: nonnegative lower bounds for radial
decrements make the radii antitone. This is reusable scalar recurrence support. -/
theorem antitone_of_drop_lower {r t : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hdrop : ∀ k, c * t k ^ 2 ≤ r k - r (k + 1)) : Antitone r := by
  apply antitone_nat_of_succ_le
  intro k
  have hnonneg := mul_nonneg hc (sq_nonneg (t k))
  linarith [hdrop k]

/-- Helper for lem:polar-geometry: finite radial decrements telescope to the
radial displacement over the same interval. This reusable identity does not
assume any radial recurrence or monotonicity. -/
theorem sum_radius_drop_Ico (r : ℕ → ℝ) (k m : ℕ) (hkm : k ≤ m) :
    (∑ l ∈ Finset.Ico k m, (r l - r (l + 1))) = r k - r m := by
  have h := Finset.sum_Ico_sub r hkm
  rw [Finset.sum_sub_distrib] at h ⊢
  linarith

/-- Helper for eq:polar-separation: once the later point lies beyond the
near-return window, the accumulated radial decrease inside that window gives
a distance of at least `(c η/8) τ`. This reusable estimate is independent of
the angular difference and therefore controls arbitrarily many turns. -/
theorem far_point_separation {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0)
    {η c : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1) (hc : 0 ≤ c)
    (hsmall : scale β j0 0 ≤ η / 2) {r θ : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    (hdrop : ∀ k, c * scale β j0 (k / 2) ^ 2 ≤ r k - r (k + 1))
    (k m : ℕ) (hwindow : k + nearWindow β j0 η k ≤ m) :
    (c * η / 8) * scale β j0 (k / 2) ≤ ‖point r θ m - point r θ k‖ := by
  have hlocal (l : ℕ) (hl : l ∈ Finset.Ico k (k + nearWindow β j0 η k)) :
      (c / 4) * scale β j0 (k / 2) ^ 2 ≤ r l - r (l + 1) := by
    have hlBounds := Finset.mem_Ico.mp hl
    have hscales := scale_nearWindow_bounds hβ hstart hη hηone k l
      hlBounds.1 hlBounds.2.le
    have hhalfNonneg : 0 ≤ (1 / 2 : ℝ) * scale β j0 (k / 2) :=
      mul_nonneg (div_nonneg zero_le_one zero_le_two) (scale_nonneg β j0 (k / 2))
    have hsquare := pow_le_pow_left₀ hhalfNonneg hscales.1 2
    have hscaled := mul_le_mul_of_nonneg_left hsquare hc
    nlinarith [hdrop l]
  have hsum := Finset.sum_le_sum hlocal
  rw [sum_radius_drop_Ico r k (k + nearWindow β j0 η k) (Nat.le_add_right _ _)] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico, Nat.add_sub_cancel_left] at hsum
  have hfloor := nearWindow_mul_scale_lower hβ hstart hsmall k
  have hfour : (0 : ℝ) ≤ 4 := by
    norm_num
  have hscaled := mul_le_mul_of_nonneg_right hfloor
    (mul_nonneg (div_nonneg hc hfour)
      (scale_nonneg β j0 (k / 2)))
  have hfirst : (c * η / 8) * scale β j0 (k / 2) ≤
      r k - r (k + nearWindow β j0 η k) := by
    nlinarith [hscaled]
  have hanti := antitone_of_drop_lower hc hdrop
  have hradial : r k - r (k + nearWindow β j0 η k) ≤ r k - r m := by
    linarith [hanti hwindow]
  exact hfirst.trans (hradial.trans (radius_sub_le_point_distance k m (hr k) (hr m)))

/-- Helper for eq:polar-separation: the near/far window decomposition gives
a uniform separation from the initial source scale for every ordered pair of
distinct points. The hypotheses concern only scalar angular increments and
radial decrements; no point-pair separation is assumed.
This is a reusable general-power polar geometry theorem. -/
theorem ordered_point_separation_of_scalar_bounds
    {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0)
    {η a b c : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hspan : b * η ≤ Real.pi)
    (hsmall : scale β j0 0 ≤ η / 2) {r θ : ℕ → ℝ} (hr : ∀ k, 1 ≤ r k)
    (hlower : ∀ k, a * scale β j0 (k / 2) ≤ θ (k + 1) - θ k)
    (hupper : ∀ k, θ (k + 1) - θ k ≤ b * scale β j0 (k / 2))
    (hdrop : ∀ k, c * scale β j0 (k / 2) ^ 2 ≤ r k - r (k + 1))
    (k m : ℕ) (hkm : k < m) :
    min (a / Real.pi) (c * η / 8) * scale β j0 (k / 2) ≤
      ‖point r θ m - point r θ k‖ := by
  by_cases hnear : m - k ≤ nearWindow β j0 η k
  · have hbound := near_point_separation hβ hstart hη hηone ha hb hspan hr
      hlower hupper k m hkm hnear
    have hcount : (1 : ℝ) ≤ ((m - k : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.sub_pos_of_lt hkm)
    have hcoefficient : 0 ≤ (a / Real.pi) * scale β j0 (k / 2) :=
      mul_nonneg (div_nonneg ha Real.pi_pos.le) (scale_nonneg β j0 (k / 2))
    have hcountBound := mul_le_mul_of_nonneg_left hcount hcoefficient
    have hmin := mul_le_mul_of_nonneg_right
      (min_le_left (a / Real.pi) (c * η / 8)) (scale_nonneg β j0 (k / 2))
    calc
      min (a / Real.pi) (c * η / 8) * scale β j0 (k / 2) ≤
          (a / Real.pi) * scale β j0 (k / 2) := hmin
      _ ≤ (a / Real.pi) * ((m - k : ℕ) : ℝ) * scale β j0 (k / 2) := by
        nlinarith [hcountBound]
      _ ≤ ‖point r θ m - point r θ k‖ := hbound
  · have hwindow : k + nearWindow β j0 η k ≤ m := by
      omega
    have hfar := far_point_separation (θ := θ) hβ hstart hη hηone hc hsmall
      (fun k ↦ zero_le_one.trans (hr k)) hdrop k m hwindow
    have hmin := mul_le_mul_of_nonneg_right
      (min_le_right (a / Real.pi) (c * η / 8)) (scale_nonneg β j0 (k / 2))
    exact hmin.trans hfar

/-- Helper for eq:polar-separation: interchanging the two ordered indices
gives the source maximum of scales for every pair of distinct general polar
points, including near returns after any number of turns.
This is a reusable general-power polar geometry theorem. -/
theorem point_separation_of_scalar_bounds
    {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0)
    {η a b c : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hspan : b * η ≤ Real.pi)
    (hsmall : scale β j0 0 ≤ η / 2) {r θ : ℕ → ℝ} (hr : ∀ k, 1 ≤ r k)
    (hlower : ∀ k, a * scale β j0 (k / 2) ≤ θ (k + 1) - θ k)
    (hupper : ∀ k, θ (k + 1) - θ k ≤ b * scale β j0 (k / 2))
    (hdrop : ∀ k, c * scale β j0 (k / 2) ^ 2 ≤ r k - r (k + 1))
    (k m : ℕ) (hne : k ≠ m) :
    min (a / Real.pi) (c * η / 8) *
        max (scale β j0 (k / 2)) (scale β j0 (m / 2)) ≤
      ‖point r θ m - point r θ k‖ := by
  rcases lt_or_gt_of_ne hne with hkm | hmk
  · have hcycle : k / 2 ≤ m / 2 := Nat.div_le_div_right hkm.le
    have hscales := scale_antitone hβ hstart hcycle
    rw [max_eq_left hscales]
    exact ordered_point_separation_of_scalar_bounds hβ hstart hη hηone ha hb hc
      hspan hsmall hr hlower hupper hdrop k m hkm
  · have hcycle : m / 2 ≤ k / 2 := Nat.div_le_div_right hmk.le
    have hscales := scale_antitone hβ hstart hcycle
    rw [max_eq_right hscales, norm_sub_rev]
    exact ordered_point_separation_of_scalar_bounds hβ hstart hη hηone ha hb hc
      hspan hsmall hr hlower hupper hdrop m k hmk

/-- Helper for eq:polar-separation: positive scalar angular and radial
coefficients give one positive separation constant valid uniformly in every
admissible starting index and every polar trajectory satisfying the scalar
bounds. This is the reusable uniform form of the full near/far separation
theorem. -/
theorem exists_uniform_point_separation {β η a b c : ℝ}
    (hβ : 0 < β) (hη : 0 < η) (hηone : η ≤ 1) (ha : 0 < a) (hb : 0 ≤ b)
    (hc : 0 < c) (hspan : b * η ≤ Real.pi) :
    ∃ s : ℝ, 0 < s ∧ ∀ j0 : ℕ, 0 < j0 → scale β j0 0 ≤ η / 2 →
      ∀ r θ : ℕ → ℝ, (∀ k, 1 ≤ r k) →
      (∀ k, a * scale β j0 (k / 2) ≤ θ (k + 1) - θ k) →
      (∀ k, θ (k + 1) - θ k ≤ b * scale β j0 (k / 2)) →
      (∀ k, c * scale β j0 (k / 2) ^ 2 ≤ r k - r (k + 1)) →
      ∀ k m : ℕ, k ≠ m → s * max (scale β j0 (k / 2)) (scale β j0 (m / 2)) ≤
        ‖point r θ m - point r θ k‖ := by
  have height : (0 : ℝ) < 8 := by
    norm_num
  have hpositive : 0 < min (a / Real.pi) (c * η / 8) :=
    lt_min (div_pos ha Real.pi_pos) (div_pos (mul_pos hc hη) height)
  refine ⟨min (a / Real.pi) (c * η / 8), hpositive, ?_⟩
  intro j0 hstart hsmall r θ hr hlower hupper hdrop k m hkm
  exact point_separation_of_scalar_bounds hβ hstart hη.le hηone ha.le hb hc.le
    hspan hsmall hr hlower hupper hdrop k m hkm

/-- Helper for lem:polar-geometry and eq:polar-angles: positive angular
increments comparable from below to the general source scales make the
unreduced angle sequence strictly increasing. This is reusable angular support. -/
theorem angle_strictMono_of_increment_lower
    {β : ℝ} {j0 : ℕ} (hstart : 0 < j0) {a : ℝ} (ha : 0 < a) {θ : ℕ → ℝ}
    (hlower : ∀ k, a * scale β j0 (k / 2) ≤ θ (k + 1) - θ k) : StrictMono θ := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hpositive := mul_pos ha (scale_pos β hstart (k / 2))
  linarith [hlower k]

/-- Helper for lem:polar-geometry and eq:polar-angles: a positive lower
angular-increment bound by the general source scales forces the unreduced
angles to tend to infinity. This reusable result uses the divergent source
scale series and does not assume any winding or cluster conclusion. -/
theorem angle_tendsto_atTop_of_increment_lower
    {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0) {a : ℝ} (ha : 0 < a)
    {θ : ℕ → ℝ}
    (hlower : ∀ k, a * scale β j0 (k / 2) ≤ θ (k + 1) - θ k) :
    Tendsto θ atTop atTop := by
  have hbound (n : ℕ) : θ 0 + a * ∑ k ∈ Finset.range n, scale β j0 k ≤ θ n := by
    have hlocal (k : ℕ) (_hk : k ∈ Finset.Ico 0 n) :
        a * scale β j0 k ≤ θ (k + 1) - θ k := by
      have hscale := scale_antitone hβ hstart (Nat.div_le_self k 2)
      exact (mul_le_mul_of_nonneg_left hscale ha.le).trans (hlower k)
    have hsum := Finset.sum_le_sum hlocal
    rw [Finset.sum_Ico_sub θ (Nat.zero_le n), Nat.Ico_zero_eq_range,
      ← Finset.mul_sum] at hsum
    linarith
  have hscale := (tendsto_sum_scale_atTop hβ j0).const_mul_atTop ha
  have hlimit : Tendsto (fun n ↦ θ 0 + a * ∑ k ∈ Finset.range n, scale β j0 k)
      atTop atTop := tendsto_atTop_add_const_left atTop (θ 0) hscale
  exact tendsto_atTop_mono hbound hlimit

/-- Helper for lem:polar-geometry and eq:polar-angles: nonnegative angular
increments bounded above by the general source scales tend to zero.
This is reusable support for first-crossing overshoot limits. -/
theorem angleIncrement_tendsto_zero_of_bounds
    {β : ℝ} (hβ : 0 < β) (j0 : ℕ) {b : ℝ} {θ : ℕ → ℝ}
    (hnonneg : ∀ k, 0 ≤ θ (k + 1) - θ k)
    (hupper : ∀ k, θ (k + 1) - θ k ≤ b * scale β j0 (k / 2)) :
    Tendsto (fun k ↦ θ (k + 1) - θ k) atTop (𝓝 0) := by
  have hscale : Tendsto (fun k ↦ b * scale β j0 (k / 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((scale_tendsto_zero hβ j0).comp AngularGeometry.halfIndex_tendsto).const_mul b
  exact squeeze_zero hnonneg hupper hscale

/-- Helper for lem:polar-geometry: first crossings of successive full turns
give a subsequence of general polar points converging to any prescribed unit
direction once the radii tend to one and angular steps tend to zero.
This reusable theorem retains the source's unreduced-angle argument. -/
theorem exists_point_subsequence_to_polarUnit {r θ : ℕ → ℝ}
    (hradius : Tendsto r atTop (𝓝 1)) (hmono : StrictMono θ)
    (hangle : Tendsto θ atTop atTop)
    (hstep : Tendsto (fun k ↦ θ (k + 1) - θ k) atTop (𝓝 0)) (φ : ℝ) :
    ∃ j : ℕ → ℕ, StrictMono j ∧ Tendsto (point r θ ∘ j) atTop (𝓝 (polarUnit φ)) := by
  have hperiod : 0 < 2 * Real.pi := by
    positivity
  obtain ⟨N, hstrict, _, herror⟩ := AngularGeometry.exists_periodic_firstCrossings
    hmono hangle hstep (2 * Real.pi) hperiod φ
  let j : ℕ → ℕ := fun n ↦ AngularGeometry.firstCrossing θ hangle
    (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi))
  have hangleLimit : Tendsto
      (fun n ↦ φ + (θ (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi))))
      atTop (𝓝 φ) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  have hnormalize (n : ℕ) : polarUnit (θ (j n)) =
      polarUnit (φ + (θ (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))) := by
    have hangleIdentity : θ (j n) =
        (φ + (θ (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))) +
          ((N + n : ℕ) : ℝ) * (2 * Real.pi) := by
      ring
    calc
      polarUnit (θ (j n)) = polarUnit
          ((φ + (θ (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))) +
            ((N + n : ℕ) : ℝ) * (2 * Real.pi)) := congrArg polarUnit hangleIdentity
      _ = polarUnit (φ + (θ (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))) :=
        AngularGeometry.polarUnit_add_natPeriod _ (N + n)
  have hpolar : Tendsto (fun n ↦ polarUnit (θ (j n))) atTop (𝓝 (polarUnit φ)) := by
    simpa only [Function.comp_def, hnormalize] using
      (AngularGeometry.continuous_polarUnit.tendsto φ).comp hangleLimit
  have hpoint := (hradius.comp hstrict.tendsto_atTop).smul hpolar
  refine ⟨j, hstrict, ?_⟩
  simpa only [Function.comp_def, point_def, one_smul] using hpoint

/-- Helper for lem:polar-geometry: general polar points with radii tending to
one and unbounded increasing angles with vanishing steps have exactly the
unit circle as their cluster set. This reusable theorem proves both inclusion
directions and constructs each circle point by first crossings. -/
theorem point_cluster_iff {r θ : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k)
    (hradius : Tendsto r atTop (𝓝 1)) (hmono : StrictMono θ)
    (hangle : Tendsto θ atTop atTop)
    (hstep : Tendsto (fun k ↦ θ (k + 1) - θ k) atTop (𝓝 0))
    (x : EuclideanSpace ℝ (Fin 2)) : MapClusterPt x atTop (point r θ) ↔ ‖x‖ = 1 := by
  constructor
  · intro hx
    obtain ⟨j, hstrict, hlimit⟩ := hx.tendsto_subseq
    have hnorm := hlimit.norm
    have hunit : Tendsto (fun n ↦ ‖point r θ (j n)‖) atTop (𝓝 1) := by
      simpa only [Function.comp_def, point_norm _ (hr _)] using
        hradius.comp hstrict.tendsto_atTop
    exact tendsto_nhds_unique hnorm hunit
  · intro hx
    obtain ⟨φ, hφ⟩ := PointGeometry.exists_polarUnit_of_norm_eq_one x hx
    obtain ⟨j, hstrict, hlimit⟩ := exists_point_subsequence_to_polarUnit
      hradius hmono hangle hstep φ
    rw [hφ] at hlimit
    exact MapClusterPt.of_comp hstrict.tendsto_atTop hlimit.mapClusterPt

/-- Helper for lem:polar-geometry: scalar source-scale angular bounds and
radii tending to one suffice for the full circle cluster set. Unbounded angle
growth, strict monotonicity, and vanishing increments are conclusions.
This is a reusable general-power polar cluster theorem. -/
theorem point_cluster_iff_of_scalar_bounds
    {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0) {a b : ℝ} (ha : 0 < a)
    {r θ : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (hradius : Tendsto r atTop (𝓝 1))
    (hlower : ∀ k, a * scale β j0 (k / 2) ≤ θ (k + 1) - θ k)
    (hupper : ∀ k, θ (k + 1) - θ k ≤ b * scale β j0 (k / 2))
    (x : EuclideanSpace ℝ (Fin 2)) : MapClusterPt x atTop (point r θ) ↔ ‖x‖ = 1 := by
  have hmono := angle_strictMono_of_increment_lower hstart ha hlower
  have hangle := angle_tendsto_atTop_of_increment_lower hβ hstart ha hlower
  have hnonneg (k : ℕ) : 0 ≤ θ (k + 1) - θ k := by
    exact (mul_nonneg ha.le (scale_nonneg β j0 (k / 2))).trans (hlower k)
  exact point_cluster_iff hr hradius hmono hangle
    (angleIncrement_tendsto_zero_of_bounds hβ j0 hnonneg hupper) x

/-- Helper for eq:polar-orders: bounded radii, angular increments at most
`b τ`, and radial drops at most `C τ²` give the source upper step bound
`(C + B b) τ`. This reusable estimate uses the polar chord upper bound. -/
theorem point_step_upper_of_scalar_bounds
    {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0)
    {B b C : ℝ} (hC : 0 ≤ C) {r θ : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) (hrUpper : ∀ k, r k ≤ B)
    (hangle : ∀ k, 0 ≤ θ (k + 1) - θ k)
    (hangleUpper : ∀ k, θ (k + 1) - θ k ≤ b * scale β j0 (k / 2))
    (hdrop : ∀ k, 0 ≤ r k - r (k + 1))
    (hdropUpper : ∀ k, r k - r (k + 1) ≤ C * scale β j0 (k / 2) ^ 2)
    (k : ℕ) : ‖point r θ (k + 1) - point r θ k‖ ≤
      (C + B * b) * scale β j0 (k / 2) := by
  have hchord := PointGeometry.polarChord_upper (r (k + 1)) (r k)
    (θ (k + 1)) (θ k) (hr k)
  have hradial : r (k + 1) - r k ≤ 0 := by
    linarith [hdrop k]
  rw [abs_of_nonpos hradial, abs_of_nonneg (hangle k)] at hchord
  have hpower : scale β j0 (k / 2) ^ 2 ≤ scale β j0 (k / 2) := by
    have ht := scale_nonneg β j0 (k / 2)
    have htone := scale_le_one hβ hstart (k / 2)
    nlinarith
  have hradialUpper := (hdropUpper k).trans (mul_le_mul_of_nonneg_left hpower hC)
  have hangularUpper : r k * (θ (k + 1) - θ k) ≤
      B * (b * scale β j0 (k / 2)) := by
    have hfirst := mul_le_mul_of_nonneg_right (hrUpper k) (hangle k)
    have hB : 0 ≤ B := (hr k).trans (hrUpper k)
    exact hfirst.trans (mul_le_mul_of_nonneg_left (hangleUpper k) hB)
  rw [point_def, point_def]
  nlinarith [hchord]

/-- Helper for eq:polar-support-radii: a uniform separation at the maximum
of two nonnegative scales gives disjoint open balls at radii `κ` times those
scales whenever `2κ` is at most the separation constant.
This is a reusable metric interpolation-support estimate. -/
theorem supportBalls_disjoint_of_separation
    {X : Type*} [MetricSpace X] {c : ℕ → X} {t : ℕ → ℝ} (ht : ∀ k, 0 ≤ t k)
    {κ s : ℝ} (hκ : 0 ≤ κ) (hsmall : 2 * κ ≤ s)
    (hsep : ∀ k m, k ≠ m → s * max (t k) (t m) ≤ dist (c k) (c m)) :
    Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (c k) (κ * t k)) := by
  intro k _ m _ hkm
  apply Metric.ball_disjoint_ball
  have hmax : 0 ≤ max (t k) (t m) := (ht k).trans (le_max_left _ _)
  calc
    κ * t k + κ * t m ≤ κ * max (t k) (t m) + κ * max (t k) (t m) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hκ)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hκ)
    _ = (2 * κ) * max (t k) (t m) := by
      ring
    _ ≤ s * max (t k) (t m) := mul_le_mul_of_nonneg_right hsmall hmax
    _ ≤ dist (c k) (c m) := hsep k m hkm

/-- Helper for lem:polar-interpolation and eq:polar-support-radii: coefficients
bounded by `A τ^(1+β)` at support radii `κ τ` have coefficient-to-radius ratio
tending to zero when `τ → 0` and `β > 0`.
This is reusable support for the actual correction-sum regularity proof. -/
theorem coefficient_div_radius_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] {a : ℕ → E} {t : ℕ → ℝ}
    (ht : ∀ k, 0 < t k) (hlimit : Tendsto t atTop (𝓝 0))
    {κ A β : ℝ} (hκ : 0 < κ) (hβ : 0 < β)
    (hcoefficient : ∀ k, ‖a k‖ ≤ A * t k ^ (1 + β)) :
    Tendsto (fun k ↦ ‖a k‖ / (κ * t k)) atTop (𝓝 0) := by
  have hbound (k : ℕ) : ‖a k‖ / (κ * t k) ≤ (A / κ) * t k ^ β :=
    InterpolationBounds.coefficient_div_radius_le hκ (ht k) rfl (hcoefficient k)
  have hpower : Tendsto (fun k ↦ (A / κ) * t k ^ β) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hlimit.rpow_const_nhds_zero hβ).const_mul (A / κ)
  exact squeeze_zero
    (fun k ↦ div_nonneg (norm_nonneg _) (mul_pos hκ (ht k)).le) hbound hpower

/-- Helper for lem:polar-interpolation and eq:polar-support-radii: the source
radial lower bound at scale `τ^(1-β)` places every support ball of radius
`κ τ` outside the closed unit disk once `2κ τ₀^β ≤ L`.
This is reusable support for the radial margin in the gluing proof. -/
theorem radius_margin_of_power_lower
    {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0) {κ L : ℝ} (hκ : 0 ≤ κ)
    {r : ℕ → ℝ} (hsmall : 2 * κ * scale β j0 0 ^ β ≤ L)
    (hlower : ∀ k, L * scale β j0 (k / 2) ^ (1 - β) ≤ r k - 1) (k : ℕ) :
    1 + 2 * (κ * scale β j0 (k / 2)) ≤ r k := by
  have ht := scale_pos β hstart (k / 2)
  have hpower := Real.rpow_le_rpow ht.le
    (scale_antitone hβ hstart (Nat.zero_le (k / 2))) hβ.le
  have hscale : 2 * κ * scale β j0 (k / 2) ^ β ≤ L :=
    (mul_le_mul_of_nonneg_left hpower (mul_nonneg zero_le_two hκ)).trans hsmall
  have hsplit : scale β j0 (k / 2) ^ (1 - β) * scale β j0 (k / 2) ^ β =
      scale β j0 (k / 2) := by
    rw [← Real.rpow_add ht, sub_add_cancel, Real.rpow_one]
  have hscaled := mul_le_mul_of_nonneg_right hscale
    (Real.rpow_nonneg ht.le (1 - β))
  have hmargin : 2 * (κ * scale β j0 (k / 2)) ≤
      L * scale β j0 (k / 2) ^ (1 - β) := by
    calc
      2 * (κ * scale β j0 (k / 2)) =
          2 * (κ * (scale β j0 (k / 2) ^ (1 - β) * scale β j0 (k / 2) ^ β)) :=
        congrArg (fun t : ℝ ↦ 2 * (κ * t)) hsplit.symm
      _ = (2 * κ * scale β j0 (k / 2) ^ β) * scale β j0 (k / 2) ^ (1 - β) := by
        ring
      _ ≤ L * scale β j0 (k / 2) ^ (1 - β) := hscaled
  linarith [hlower k]

/-- Helper for lem:polar-interpolation: scalar angular and radial-decrement
bounds imply disjoint supports, while the radial power lower bound and
coefficient power upper bound imply the support margin and vanishing Hessian
envelope. Together with radial convergence these conclusions supply the
actual correction-sum geometry certificate, without assuming disjointness or
coefficient-to-radius decay. This is a reusable assembly theorem for the
generalized source trajectory. -/
theorem interpolationGeometry_of_scalar_bounds
    {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0)
    {η a b c κ L A : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hκ : 0 < κ)
    (hspan : b * η ≤ Real.pi) (hsmall : scale β j0 0 ≤ η / 2)
    (hκsep : 2 * κ ≤ min (a / Real.pi) (c * η / 8))
    (hκmargin : 2 * κ * scale β j0 0 ^ β ≤ L)
    {r θ : ℕ → ℝ} (hr : ∀ k, 1 ≤ r k) (hradius : Tendsto r atTop (𝓝 1))
    (hlower : ∀ k, a * scale β j0 (k / 2) ≤ θ (k + 1) - θ k)
    (hupper : ∀ k, θ (k + 1) - θ k ≤ b * scale β j0 (k / 2))
    (hdrop : ∀ k, c * scale β j0 (k / 2) ^ 2 ≤ r k - r (k + 1))
    (hradial : ∀ k, L * scale β j0 (k / 2) ^ (1 - β) ≤ r k - 1)
    {coefficient : ℕ → EuclideanSpace ℝ (Fin 2)}
    (hcoefficient : ∀ k, ‖coefficient k‖ ≤ A * scale β j0 (k / 2) ^ (1 + β)) :
    InterpolationSum.Geometry (point r θ) (fun k ↦ κ * scale β j0 (k / 2)) coefficient := by
  have hsep (k m : ℕ) (hkm : k ≠ m) :
      min (a / Real.pi) (c * η / 8) *
        max (scale β j0 (k / 2)) (scale β j0 (m / 2)) ≤
        dist (point r θ k) (point r θ m) := by
    rw [dist_eq_norm, norm_sub_rev]
    exact point_separation_of_scalar_bounds hβ hstart hη hηone ha hb hc hspan hsmall
      hr hlower hupper hdrop k m hkm
  constructor
  · intro k
    exact mul_pos hκ (scale_pos β hstart (k / 2))
  · exact supportBalls_disjoint_of_separation
      (fun k ↦ scale_nonneg β j0 (k / 2)) hκ.le hκsep hsep
  · simpa only [point_norm _ (zero_le_one.trans (hr _))] using hradius
  · intro k
    rw [point_norm k (zero_le_one.trans (hr k))]
    exact radius_margin_of_power_lower hβ hstart hκ.le hκmargin hradial k
  · exact coefficient_div_radius_tendsto_zero (fun k ↦ scale_pos β hstart (k / 2))
      ((scale_tendsto_zero hβ j0).comp AngularGeometry.halfIndex_tendsto)
      hκ hβ hcoefficient

end DFP.Polar.General.Geometry

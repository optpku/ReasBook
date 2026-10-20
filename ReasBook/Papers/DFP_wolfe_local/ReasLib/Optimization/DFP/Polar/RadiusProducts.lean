module

public import ReasLib.Optimization.DFP.Polar.Realization
public import ReasLib.Optimization.DFP.Polar.ScaleTails
public import ReasLib.Optimization.DFP.Polar.Continuation
public import ReasLib.Optimization.DFP.Polar.RadiusExpansions
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Order

public section

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace DFP.Polar.RadiusProducts

/-- Helper for eq:polar-radii: the tail product of a scalar factor sequence. -/
def tailProduct (w : ℕ → ℝ) (j : ℕ) : ℝ := ∏' n : ℕ, w (j + n)

/-- Helper for eq:polar-radii: the defining tail-product formula. -/
theorem tailProduct_def (w : ℕ → ℝ) (j : ℕ) :
    tailProduct w j = ∏' n : ℕ, w (j + n) := by
  rfl

/-- Helper for eq:polar-radii: the logarithmic tail of positive scalar factors. -/
def logTail (w : ℕ → ℝ) (j : ℕ) : ℝ := ∑' n : ℕ, Real.log (w (j + n))

/-- Helper for eq:polar-radii: the defining logarithmic-tail formula. -/
theorem logTail_def (w : ℕ → ℝ) (j : ℕ) :
    logTail w j = ∑' n : ℕ, Real.log (w (j + n)) := by
  rfl

/-- Helper for eq:polar-radii: summability of logarithms persists in every tail. -/
theorem summableLogTail {w : ℕ → ℝ} (hlog : Summable (fun n ↦ Real.log (w n)))
    (j : ℕ) : Summable (fun n ↦ Real.log (w (j + n))) := by
  simpa only [Nat.add_comm] using (summable_nat_add_iff j).2 hlog

/-- Helper for eq:polar-radii: summable logarithms give the original positive product,
with its exact exponential representation. -/
theorem tailProduct_eq_exp {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (hlog : Summable (fun n ↦ Real.log (w n))) (j : ℕ) :
    tailProduct w j = Real.exp (logTail w j) := by
  rw [tailProduct_def, logTail_def]
  exact (Real.rexp_tsum_eq_tprod (fun n ↦ hw (j + n)) (summableLogTail hlog j)).symm

/-- Helper for eq:polar-radii: every positive tail with summable logarithms is multipliable. -/
theorem multipliableTail {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (hlog : Summable (fun n ↦ Real.log (w n))) (j : ℕ) :
    Multipliable (fun n ↦ w (j + n)) := by
  exact Real.multipliable_of_summable_log (fun n ↦ hw (j + n)) (summableLogTail hlog j)

/-- Helper for eq:polar-radii: a positive logarithmic tail gives a positive radius. -/
theorem tailProduct_pos {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (hlog : Summable (fun n ↦ Real.log (w n))) (j : ℕ) :
    0 < tailProduct w j := by
  rw [tailProduct_eq_exp hw hlog]
  exact Real.exp_pos _

/-- Helper for eq:polar-radii: removing the first term shifts the logarithmic tail exactly. -/
theorem logTail_shift {w : ℕ → ℝ} (hlog : Summable (fun n ↦ Real.log (w n)))
    (j : ℕ) : logTail w j = Real.log (w j) + logTail w (j + 1) := by
  rw [logTail_def, logTail_def, (summableLogTail hlog j).tsum_eq_zero_add]
  simp only [Nat.add_zero, Nat.add_left_comm, Nat.add_comm]

/-- Helper for eq:polar-radii: the exact shifted tail-product recurrence follows
by exponentiating the shifted sum of logarithms. -/
theorem tailProduct_shift {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (hlog : Summable (fun n ↦ Real.log (w n))) (j : ℕ) :
    tailProduct w j = w j * tailProduct w (j + 1) := by
  rw [tailProduct_eq_exp hw hlog, logTail_shift hlog, Real.exp_add,
    Real.exp_log (hw j), tailProduct_eq_exp hw hlog]

/-- Helper for eq:polar-radii: the logarithmic tails tend to zero. -/
theorem logTail_tendsto_zero (w : ℕ → ℝ) :
    Tendsto (logTail w) atTop (𝓝 0) := by
  rw [funext (logTail_def w)]
  simpa only [Nat.add_comm] using
    tendsto_sum_nat_add (fun n ↦ Real.log (w n))

/-- Helper for eq:polar-radii: positive tail products tend to one through their logarithms. -/
theorem tailProduct_tendsto_one {w : ℕ → ℝ} (hw : ∀ n, 0 < w n)
    (hlog : Summable (fun n ↦ Real.log (w n))) :
    Tendsto (tailProduct w) atTop (𝓝 1) := by
  have hlimit := Real.continuous_exp.continuousAt.tendsto.comp (logTail_tendsto_zero w)
  simpa only [Function.comp_def, Real.exp_zero, ← tailProduct_eq_exp hw hlog] using hlimit

/-- Helper for eq:polar-radii: factors strictly above one give radii strictly above one. -/
theorem tailProduct_gt_one {w : ℕ → ℝ} (hw : ∀ n, 1 < w n)
    (hlog : Summable (fun n ↦ Real.log (w n))) (j : ℕ) :
    1 < tailProduct w j := by
  have hpositive : ∀ n, 0 < w n := fun n ↦ zero_lt_one.trans (hw n)
  have htail : 0 < logTail w j := by
    rw [logTail_def]
    apply (summableLogTail hlog j).tsum_pos
    · intro n
      exact (Real.log_pos (hw (j + n))).le
    · exact Real.log_pos (hw (j + 0))
  rw [tailProduct_eq_exp hpositive hlog, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr htail

/-- Helper for eq:polar-radii: factors strictly above one make the tail products
strictly decrease. -/
theorem tailProduct_strictAnti {w : ℕ → ℝ} (hw : ∀ n, 1 < w n)
    (hlog : Summable (fun n ↦ Real.log (w n))) : StrictAnti (tailProduct w) := by
  have hpositive : ∀ n, 0 < w n := fun n ↦ zero_lt_one.trans (hw n)
  apply strictAnti_nat_of_succ_lt
  intro j
  rw [tailProduct_shift hpositive hlog j]
  exact lt_mul_of_one_lt_left (tailProduct_pos hpositive hlog (j + 1)) (hw j)

/-- Helper for eq:polar-radii: the logarithm differs from its linear term by at most
the squared displacement, for every factor at least one. -/
theorem abs_log_sub_linear_le_sq {w : ℝ} (hw : 1 ≤ w) :
    |Real.log w - (w - 1)| ≤ (w - 1) ^ 2 := by
  have hpos : 0 < w := zero_lt_one.trans_le hw
  have hcub : 0 ≤ (w - 1) ^ 3 := pow_nonneg (sub_nonneg.mpr hw) 3
  have hquot : (w - 1) - (w - 1) ^ 2 ≤ (w - 1) / w := by
    apply (le_div_iff₀ hpos).2
    nlinarith
  have hid : (w - 1) / w = 1 - w⁻¹ := by
    field_simp
  have hlower := hquot.trans (hid ▸ Real.one_sub_inv_le_log_of_pos hpos)
  have hupper := Real.log_le_sub_one_of_pos hpos
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

/-- Helper for eq:polar-radii: the actual pair of prescribed radius factors in one cycle. -/
def cycleFactor (p : Parameters) (j : ℕ) : ℝ :=
  p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1)

/-- Helper for eq:polar-radii: the paired factor retains both original phases. -/
theorem cycleFactor_def (p : Parameters) (j : ℕ) :
    cycleFactor p j = p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1) := by
  rfl

/-- Helper for eq:polar-radii: the existing even radius is exactly the paired-factor
tail product. -/
theorem evenRadius_eq_tailProduct (p : Parameters) (j : ℕ) :
    p.evenRadius j = tailProduct (cycleFactor p) j := by
  rw [Parameters.evenRadius_def, tailProduct_def]
  simp only [cycleFactor_def]

/-- Helper for eq:polar-radii: a fifth-order remainder gives uniform fourth-order
upper and lower bounds after the scale is sufficiently small. -/
theorem factor_sub_one_bounds {w t D C : ℝ} (ht : 0 ≤ t) (htone : t ≤ 1)
    (hC : 0 ≤ C) (hsmall : C * t ≤ D / 2)
    (herror : |w - 1 - D * t ^ 4| ≤ C * t ^ 5) :
    D / 2 * t ^ 4 ≤ w - 1 ∧ w - 1 ≤ (D + C) * t ^ 4 := by
  have hexponents : (4 : ℕ) ≤ 5 := by norm_num
  have hpowers : t ^ 5 ≤ t ^ 4 := pow_le_pow_of_le_one ht htone hexponents
  have hsmallPower := mul_le_mul_of_nonneg_right hsmall (pow_nonneg ht 4)
  have herrorPower := mul_le_mul_of_nonneg_left hpowers hC
  have habs := abs_le.mp herror
  constructor
  · nlinarith
  · linarith

/-- Helper for eq:polar-radii: the exact logarithm of a factor has the same quartic
coefficient, with an explicit uniform fifth-order remainder. -/
theorem logFactor_error {w t D C : ℝ} (ht : 0 ≤ t) (htone : t ≤ 1)
    (hC : 0 ≤ C) (hw : 1 ≤ w)
    (herror : |w - 1 - D * t ^ 4| ≤ C * t ^ 5) :
    |Real.log w - D * t ^ 4| ≤ (C + (D + C) ^ 2) * t ^ 5 := by
  have hexponents : (4 : ℕ) ≤ 5 := by norm_num
  have hpowers : t ^ 5 ≤ t ^ 4 := pow_le_pow_of_le_one ht htone hexponents
  have hupper : w - 1 ≤ (D + C) * t ^ 4 := by
    have habs := (abs_le.mp herror).2
    have hmul := mul_le_mul_of_nonneg_left hpowers hC
    linarith
  have hsquare : (w - 1) ^ 2 ≤ ((D + C) * t ^ 4) ^ 2 := by
    exact pow_le_pow_left₀ (sub_nonneg.mpr hw) hupper 2
  have heighthExponent : (5 : ℕ) ≤ 8 := by norm_num
  have heighth : t ^ 8 ≤ t ^ 5 := pow_le_pow_of_le_one ht htone heighthExponent
  have hquadratic : (w - 1) ^ 2 ≤ (D + C) ^ 2 * t ^ 5 := by
    calc
      (w - 1) ^ 2 ≤ ((D + C) * t ^ 4) ^ 2 := hsquare
      _ = (D + C) ^ 2 * t ^ 8 := by ring
      _ ≤ (D + C) ^ 2 * t ^ 5 :=
        mul_le_mul_of_nonneg_left heighth (sq_nonneg _)
  calc
    |Real.log w - D * t ^ 4| =
        |(Real.log w - (w - 1)) + (w - 1 - D * t ^ 4)| := by ring_nf
    _ ≤ |Real.log w - (w - 1)| + |w - 1 - D * t ^ 4| := abs_add_le _ _
    _ ≤ (w - 1) ^ 2 + C * t ^ 5 := add_le_add (abs_log_sub_linear_le_sq hw) herror
    _ ≤ (C + (D + C) ^ 2) * t ^ 5 := by linarith

/-- Helper for eq:polar-radii: a quartic logarithmic expansion along the actual
prescribed scale proves summability of the logarithms. -/
theorem summableLog_of_error (p : Parameters) {w : ℕ → ℝ} {D C : ℝ}
    (herror : ∀ j, |Real.log (w j) - D * p.scale j ^ 4| ≤ C * p.scale j ^ 5) :
    Summable (fun j ↦ Real.log (w j)) := by
  have herr : Summable (fun j ↦ Real.log (w j) - D * p.scale j ^ 4) := by
    apply ((ScaleTails.summable_scale_five p).mul_left C).of_norm_bounded
    intro j
    simpa only [Real.norm_eq_abs] using herror j
  have hsum := herr.add ((ScaleTails.summable_scale_four p).mul_left D)
  simpa only [sub_add_cancel] using hsum

/-- Helper for eq:polar-radii: summing the logarithmic remainder gives exactly a
constant times the prescribed quintic scale tail. -/
theorem logTail_quartic_error (p : Parameters) {w : ℕ → ℝ} {D C : ℝ}
    (herror : ∀ j, |Real.log (w j) - D * p.scale j ^ 4| ≤ C * p.scale j ^ 5)
    (j : ℕ) :
    |logTail w j - D * ScaleTails.powerTail p 4 j| ≤
      C * ScaleTails.powerTail p 5 j := by
  have hfour : Summable (fun n ↦ p.scale (j + n) ^ 4) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff j).2 (ScaleTails.summable_scale_four p)
  have hfive : Summable (fun n ↦ p.scale (j + n) ^ 5) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff j).2 (ScaleTails.summable_scale_five p)
  have hid : logTail w j - D * ScaleTails.powerTail p 4 j =
      ∑' n : ℕ, (Real.log (w (j + n)) - D * p.scale (j + n) ^ 4) := by
    rw [logTail_def, ScaleTails.powerTail_def,
      (summableLogTail (summableLog_of_error p herror) j).tsum_sub (hfour.mul_left D),
      tsum_mul_left]
  rw [hid]
  have hnorm : ∀ n : ℕ, ‖Real.log (w (j + n)) - D * p.scale (j + n) ^ 4‖ ≤
      C * p.scale (j + n) ^ 5 := by
    intro n
    simpa only [Real.norm_eq_abs] using herror (j + n)
  have hsum := tsum_of_norm_bounded (hfive.mul_left C).hasSum
    hnorm
  simpa only [Real.norm_eq_abs, tsum_mul_left, ← ScaleTails.powerTail_def] using hsum

/-- Helper for lem:polar-geometry: the source integral comparisons turn the quartic
logarithmic expansion into a uniform linear tail expansion. -/
theorem logTail_linear_error (p : Parameters) (hstart : 0 < p.startIndex)
    {w : ℕ → ℝ} {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (herror : ∀ j, |Real.log (w j) - D * p.scale j ^ 4| ≤ C * p.scale j ^ 5)
    (j : ℕ) :
    |logTail w j - 3 * D * p.scale j| ≤ (D + (5 / 2) * C) * p.scale j ^ 2 := by
  have hfour := ScaleTails.quarticTail_error p hstart j
  have hfive := ScaleTails.quinticTail_le p hstart j
  have hexponents : (2 : ℕ) ≤ 4 := by norm_num
  have hpowers : p.scale j ^ 4 ≤ p.scale j ^ 2 :=
    pow_le_pow_of_le_one (ScaleTails.scale_nonneg p j)
      (ScaleTails.scale_le_one p hstart j) hexponents
  have hmain : |D * (ScaleTails.powerTail p 4 j - 3 * p.scale j)| ≤
      D * p.scale j ^ 2 := by
    rw [abs_mul, abs_of_nonneg hD, abs_of_nonneg hfour.1]
    exact mul_le_mul_of_nonneg_left (hfour.2.trans hpowers) hD
  calc
    |logTail w j - 3 * D * p.scale j| =
        |(logTail w j - D * ScaleTails.powerTail p 4 j) +
          D * (ScaleTails.powerTail p 4 j - 3 * p.scale j)| := by ring_nf
    _ ≤ |logTail w j - D * ScaleTails.powerTail p 4 j| +
        |D * (ScaleTails.powerTail p 4 j - 3 * p.scale j)| := abs_add_le _ _
    _ ≤ C * ScaleTails.powerTail p 5 j + D * p.scale j ^ 2 :=
      add_le_add (logTail_quartic_error p herror j) hmain
    _ ≤ (D + (5 / 2) * C) * p.scale j ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hfive hC
      nlinarith

/-- Helper for lem:polar-geometry: a uniform bound for the logarithmic radius in terms
of the actual prescribed scale. -/
theorem abs_logTail_le_scale (p : Parameters) (hstart : 0 < p.startIndex)
    {w : ℕ → ℝ} {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (herror : ∀ j, |Real.log (w j) - D * p.scale j ^ 4| ≤ C * p.scale j ^ 5)
    (j : ℕ) : |logTail w j| ≤ (4 * D + (5 / 2) * C) * p.scale j := by
  have hbound := logTail_linear_error p hstart hD hC herror j
  have ht := ScaleTails.scale_nonneg p j
  have hexponents : (1 : ℕ) ≤ 2 := by norm_num
  have hpowers : p.scale j ^ 2 ≤ p.scale j := by
    simpa only [pow_one] using pow_le_pow_of_le_one ht
      (ScaleTails.scale_le_one p hstart j) hexponents
  have hconstant : 0 ≤ D + (5 / 2) * C := by positivity
  have hmain : 0 ≤ 3 * D * p.scale j := by positivity
  calc
    |logTail w j| = |(logTail w j - 3 * D * p.scale j) + 3 * D * p.scale j| := by
      rw [sub_add_cancel]
    _ ≤ |logTail w j - 3 * D * p.scale j| + |3 * D * p.scale j| := abs_add_le _ _
    _ ≤ (D + (5 / 2) * C) * p.scale j ^ 2 + 3 * D * p.scale j := by
      rw [abs_of_nonneg hmain]
      exact add_le_add hbound le_rfl
    _ ≤ (4 * D + (5 / 2) * C) * p.scale j := by
      have hmul := mul_le_mul_of_nonneg_left hpowers hconstant
      linarith

/-- Helper for lem:polar-geometry: a single smallness condition at the starting scale
puts every logarithmic tail in the unit interval in absolute value. -/
theorem abs_logTail_le_one (p : Parameters) (hstart : 0 < p.startIndex)
    {w : ℕ → ℝ} {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (herror : ∀ j, |Real.log (w j) - D * p.scale j ^ 4| ≤ C * p.scale j ^ 5)
    (hsmall : (4 * D + (5 / 2) * C) * p.scale 0 ≤ 1) (j : ℕ) :
    |logTail w j| ≤ 1 := by
  have hconstant : 0 ≤ 4 * D + (5 / 2) * C := by positivity
  calc
    |logTail w j| ≤ (4 * D + (5 / 2) * C) * p.scale j :=
      abs_logTail_le_scale p hstart hD hC herror j
    _ ≤ (4 * D + (5 / 2) * C) * p.scale 0 :=
      mul_le_mul_of_nonneg_left
        (ScaleTails.scale_antitone p hstart (Nat.zero_le j)) hconstant
    _ ≤ 1 := hsmall

/-- Helper for lem:polar-geometry: exponentiating the source logarithmic expansion
gives the radius expansion, with a constant independent of the starting index. -/
theorem tailProduct_linear_error (p : Parameters) (hstart : 0 < p.startIndex)
    {w : ℕ → ℝ} {D C : ℝ} (hw : ∀ j, 0 < w j) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (herror : ∀ j, |Real.log (w j) - D * p.scale j ^ 4| ≤ C * p.scale j ^ 5)
    (hsmall : (4 * D + (5 / 2) * C) * p.scale 0 ≤ 1) (j : ℕ) :
    |tailProduct w j - 1 - 3 * D * p.scale j| ≤
      ((4 * D + (5 / 2) * C) ^ 2 + D + (5 / 2) * C) * p.scale j ^ 2 := by
  have hbound := abs_logTail_le_scale p hstart hD hC herror j
  have hexp := Real.abs_exp_sub_one_sub_id_le
    (abs_logTail_le_one p hstart hD hC herror hsmall j)
  have hsquare := pow_le_pow_left₀ (abs_nonneg (logTail w j)) hbound 2
  have hsquare' : logTail w j ^ 2 ≤
      (4 * D + (5 / 2) * C) ^ 2 * p.scale j ^ 2 := by
    simpa only [sq_abs, mul_pow] using hsquare
  rw [tailProduct_eq_exp hw (summableLog_of_error p herror)]
  calc
    |Real.exp (logTail w j) - 1 - 3 * D * p.scale j| =
        |(Real.exp (logTail w j) - 1 - logTail w j) +
          (logTail w j - 3 * D * p.scale j)| := by ring_nf
    _ ≤ |Real.exp (logTail w j) - 1 - logTail w j| +
        |logTail w j - 3 * D * p.scale j| := abs_add_le _ _
    _ ≤ logTail w j ^ 2 + (D + (5 / 2) * C) * p.scale j ^ 2 :=
      add_le_add hexp (logTail_linear_error p hstart hD hC herror j)
    _ ≤ ((4 * D + (5 / 2) * C) ^ 2 + D + (5 / 2) * C) * p.scale j ^ 2 := by
      linarith

/-- Helper for lem:polar-geometry: small logarithmic tails give one universal radius bound. -/
theorem tailProduct_le_exp_one (p : Parameters) (hstart : 0 < p.startIndex)
    {w : ℕ → ℝ} {D C : ℝ} (hw : ∀ j, 0 < w j) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (herror : ∀ j, |Real.log (w j) - D * p.scale j ^ 4| ≤ C * p.scale j ^ 5)
    (hsmall : (4 * D + (5 / 2) * C) * p.scale 0 ≤ 1) (j : ℕ) :
    tailProduct w j ≤ Real.exp 1 := by
  rw [tailProduct_eq_exp hw (summableLog_of_error p herror)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans
    (abs_logTail_le_one p hstart hD hC herror hsmall j))

/-- Helper for eq:polar-radii: a named interface for the two original positive
phase coefficients and their uniform scale estimates. These are scalar hypotheses
to be discharged by the actual source radius expansion. -/
structure FactorBounds (p : Parameters) (D : Fin 2 → ℝ) (C : ℝ) : Prop where
  /-- Helper for eq:polar-radii: both source phase coefficients are positive. -/
  coefficient_pos : ∀ i, 0 < D i
  /-- Helper for eq:polar-radii: the common remainder constant is nonnegative. -/
  error_nonneg : 0 ≤ C
  /-- Helper for eq:polar-radii: the exact source fifth-order phase remainder. -/
  expansion : ∀ j (i : Fin 2),
    |p.radiusRatio (2 * j + (i : ℕ)) - 1 - D i * p.scale j ^ 4| ≤ C * p.scale j ^ 5
  /-- Helper for eq:polar-radii: the source quartic term controls the radial decrease below. -/
  lower : ∀ j (i : Fin 2),
    D i / 2 * p.scale j ^ 4 ≤ p.radiusRatio (2 * j + (i : ℕ)) - 1
  /-- Helper for eq:polar-radii: the source quartic term controls the radial decrease above. -/
  upper : ∀ j (i : Fin 2),
    p.radiusRatio (2 * j + (i : ℕ)) - 1 ≤ (D i + C) * p.scale j ^ 4

/-- Helper for eq:polar-radii: the named factor interface follows from the original
fifth-order expansion by reducing the starting scale. -/
theorem factorBounds_of_expansion (p : Parameters) (hstart : 0 < p.startIndex)
    {D : Fin 2 → ℝ} {C : ℝ} (hD : ∀ i, 0 < D i) (hC : 0 ≤ C)
    (herror : ∀ j (i : Fin 2),
      |p.radiusRatio (2 * j + (i : ℕ)) - 1 - D i * p.scale j ^ 4| ≤ C * p.scale j ^ 5)
    (hsmall : ∀ i, C * p.scale 0 ≤ D i / 2) : FactorBounds p D C := by
  have hbounds : ∀ j (i : Fin 2),
      D i / 2 * p.scale j ^ 4 ≤ p.radiusRatio (2 * j + (i : ℕ)) - 1 ∧
      p.radiusRatio (2 * j + (i : ℕ)) - 1 ≤ (D i + C) * p.scale j ^ 4 := by
    intro j i
    have hsmallj : C * p.scale j ≤ D i / 2 :=
      (mul_le_mul_of_nonneg_left
        (ScaleTails.scale_antitone p hstart (Nat.zero_le j)) hC).trans (hsmall i)
    exact factor_sub_one_bounds (ScaleTails.scale_nonneg p j)
      (ScaleTails.scale_le_one p hstart j) hC hsmallj (herror j i)
  exact ⟨hD, hC, herror, fun j i ↦ (hbounds j i).1, fun j i ↦ (hbounds j i).2⟩

/-- Helper for eq:polar-radii: the explicit fifth-order logarithmic remainder constant
for the product of the two source phases. -/
def cycleLogConstant (D : Fin 2 → ℝ) (C : ℝ) : ℝ :=
  2 * C + (D 0 + C) ^ 2 + (D 1 + C) ^ 2

/-- Helper for eq:polar-radii: the formula for the paired logarithmic remainder constant. -/
theorem cycleLogConstant_def (D : Fin 2 → ℝ) (C : ℝ) :
    cycleLogConstant D C = 2 * C + (D 0 + C) ^ 2 + (D 1 + C) ^ 2 := by
  rfl

/-- Helper for eq:polar-radii: the paired logarithmic remainder constant is nonnegative. -/
theorem cycleLogConstant_nonneg (D : Fin 2 → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ cycleLogConstant D C := by
  rw [cycleLogConstant_def]
  positivity

/-- Helper for eq:polar-radii: every original phase factor exceeds one. -/
theorem FactorBounds.factor_gt_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) (i : Fin 2) :
    1 < p.radiusRatio (2 * j + (i : ℕ)) := by
  have ht := ScaleTails.scale_pos p hstart j
  have hD := h.coefficient_pos i
  have hterm : 0 < D i / 2 * p.scale j ^ 4 := by positivity
  linarith [h.lower j i]

/-- Helper for eq:polar-radii: both phases together form a factor strictly above one. -/
theorem FactorBounds.cycleFactor_gt_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    1 < cycleFactor p j := by
  have hE : 1 < p.radiusRatio (2 * j) := by
    simpa only [Fin.val_zero, Nat.add_zero] using h.factor_gt_one hstart j 0
  have hO : 1 < p.radiusRatio (2 * j + 1) := h.factor_gt_one hstart j 1
  rw [cycleFactor_def]
  exact hO.trans (lt_mul_of_one_lt_left (zero_lt_one.trans hO) hE)

/-- Helper for eq:polar-radii: the source paired factors have quartic logarithmic
coefficient `D₀ + D₁` and a uniform fifth-order remainder. -/
theorem FactorBounds.cycleLog_error {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    |Real.log (cycleFactor p j) - (D 0 + D 1) * p.scale j ^ 4| ≤
      cycleLogConstant D C * p.scale j ^ 5 := by
  have hE : 1 < p.radiusRatio (2 * j) := by
    simpa only [Fin.val_zero, Nat.add_zero] using h.factor_gt_one hstart j 0
  have hO : 1 < p.radiusRatio (2 * j + 1) := h.factor_gt_one hstart j 1
  have herrorE : |p.radiusRatio (2 * j) - 1 - D 0 * p.scale j ^ 4| ≤
      C * p.scale j ^ 5 := by
    simpa only [Fin.val_zero, Nat.add_zero] using h.expansion j 0
  have hlogE := logFactor_error (ScaleTails.scale_nonneg p j)
    (ScaleTails.scale_le_one p hstart j) h.error_nonneg hE.le herrorE
  have hlogO := logFactor_error (ScaleTails.scale_nonneg p j)
    (ScaleTails.scale_le_one p hstart j) h.error_nonneg hO.le (h.expansion j 1)
  rw [cycleFactor_def, Real.log_mul (ne_of_gt (zero_lt_one.trans hE))
    (ne_of_gt (zero_lt_one.trans hO)), cycleLogConstant_def]
  calc
    |Real.log (p.radiusRatio (2 * j)) + Real.log (p.radiusRatio (2 * j + 1)) -
        (D 0 + D 1) * p.scale j ^ 4| =
        |(Real.log (p.radiusRatio (2 * j)) - D 0 * p.scale j ^ 4) +
          (Real.log (p.radiusRatio (2 * j + 1)) - D 1 * p.scale j ^ 4)| := by ring_nf
    _ ≤ |Real.log (p.radiusRatio (2 * j)) - D 0 * p.scale j ^ 4| +
        |Real.log (p.radiusRatio (2 * j + 1)) - D 1 * p.scale j ^ 4| := abs_add_le _ _
    _ ≤ (2 * C + (D 0 + C) ^ 2 + (D 1 + C) ^ 2) * p.scale j ^ 5 := by
      linarith

/-- Helper for eq:polar-radii: the logarithms of the actual paired factors are summable. -/
theorem FactorBounds.summable_cycleLog {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) :
    Summable (fun j ↦ Real.log (cycleFactor p j)) := by
  exact summableLog_of_error p (h.cycleLog_error hstart)

/-- Helper for eq:polar-radii: every original paired-factor tail is multipliable. -/
theorem FactorBounds.multipliable_cycleTail {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    Multipliable (fun n ↦ p.radiusRatio (2 * (j + n)) *
      p.radiusRatio (2 * (j + n) + 1)) := by
  have hpositive : ∀ n, 0 < cycleFactor p n :=
    fun n ↦ zero_lt_one.trans (h.cycleFactor_gt_one hstart n)
  simpa only [cycleFactor_def] using multipliableTail hpositive
    (h.summable_cycleLog hstart) j

/-- Helper for eq:polar-radii: the original even radius is the exponential of the
sum of the paired logarithms, as in the source proof. -/
theorem FactorBounds.evenRadius_eq_exp {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    p.evenRadius j = Real.exp (logTail (cycleFactor p) j) := by
  rw [evenRadius_eq_tailProduct]
  exact tailProduct_eq_exp
    (fun n ↦ zero_lt_one.trans (h.cycleFactor_gt_one hstart n))
    (h.summable_cycleLog hstart) j

/-- Helper for eq:polar-radii: taking logarithms of the original product gives
exactly the summable logarithmic tail. -/
theorem FactorBounds.log_evenRadius {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    Real.log (p.evenRadius j) = logTail (cycleFactor p) j := by
  rw [h.evenRadius_eq_exp hstart, Real.log_exp]

/-- Helper for eq:polar-radii: the exact original tail product satisfies its
shift recurrence without replacing the radii by abstract witnesses. -/
theorem FactorBounds.evenRadius_shift {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    p.evenRadius j = p.radiusRatio (2 * j) * p.radiusRatio (2 * j + 1) *
      p.evenRadius (j + 1) := by
  rw [evenRadius_eq_tailProduct, evenRadius_eq_tailProduct]
  exact tailProduct_shift
    (fun n ↦ zero_lt_one.trans (h.cycleFactor_gt_one hstart n))
    (h.summable_cycleLog hstart) j

/-- Helper for eq:polar-radii: the odd quotient equals the remaining second-phase
factor times the next original even tail product. -/
theorem FactorBounds.oddRadius_eq_mul {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    p.oddRadius j = p.radiusRatio (2 * j + 1) * p.evenRadius (j + 1) := by
  have hE : 1 < p.radiusRatio (2 * j) := by
    simpa only [Fin.val_zero, Nat.add_zero] using h.factor_gt_one hstart j 0
  have hne : p.radiusRatio (2 * j) ≠ 0 := ne_of_gt (zero_lt_one.trans hE)
  rw [Parameters.oddRadius_def, h.evenRadius_shift hstart j]
  apply (div_eq_iff hne).2
  ring

/-- Helper for eq:polar-radii: every original even radius is strictly above one. -/
theorem FactorBounds.evenRadius_gt_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    1 < p.evenRadius j := by
  rw [evenRadius_eq_tailProduct]
  exact tailProduct_gt_one (h.cycleFactor_gt_one hstart) (h.summable_cycleLog hstart) j

/-- Helper for eq:polar-radii: every original odd radius is strictly above one. -/
theorem FactorBounds.oddRadius_gt_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    1 < p.oddRadius j := by
  have hO : 1 < p.radiusRatio (2 * j + 1) := h.factor_gt_one hstart j 1
  have hr := h.evenRadius_gt_one hstart (j + 1)
  rw [h.oddRadius_eq_mul hstart]
  exact hr.trans (lt_mul_of_one_lt_left (zero_lt_one.trans hr) hO)

/-- Helper for eq:polar-radii: the full original radius sequence is strictly above one. -/
theorem FactorBounds.radius_gt_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (k : ℕ) : 1 < p.radius k := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [Parameters.radius_even]
    exact h.evenRadius_gt_one hstart j
  · rw [Parameters.radius_odd]
    exact h.oddRadius_gt_one hstart j

/-- Helper for eq:polar-radii: every original radius factor exceeds one at an arbitrary index. -/
theorem FactorBounds.radiusRatio_gt_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (k : ℕ) :
    1 < p.radiusRatio k := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simpa only [Fin.val_zero, Nat.add_zero] using h.factor_gt_one hstart j 0
  · exact h.factor_gt_one hstart j 1

/-- Helper for eq:polar-radii: the full radius sequence satisfies the exact source
multiplicative recurrence at both phases. -/
theorem FactorBounds.radius_eq_factor_mul_succ {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (k : ℕ) :
    p.radius k = p.radiusRatio k * p.radius (k + 1) := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [Parameters.radius_even, Parameters.radius_odd, h.oddRadius_eq_mul hstart,
      h.evenRadius_shift hstart j]
    ring
  · have hindex : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    rw [hindex, Parameters.radius_odd, Parameters.radius_even, h.oddRadius_eq_mul hstart]

/-- Helper for eq:polar-radii: the exact quotient recurrence `r_(k+1) = r_k / W_k`. -/
theorem FactorBounds.radius_succ {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (k : ℕ) :
    p.radius (k + 1) = p.radius k / p.radiusRatio k := by
  apply (eq_div_iff (ne_of_gt (zero_lt_one.trans (h.radiusRatio_gt_one hstart k)))).2
  rw [h.radius_eq_factor_mul_succ hstart k]
  ring

/-- Helper for eq:polar-radii: the full original radius sequence strictly decreases. -/
theorem FactorBounds.radius_strictAnti {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) : StrictAnti p.radius := by
  apply strictAnti_nat_of_succ_lt
  intro k
  rw [h.radius_eq_factor_mul_succ hstart k]
  exact lt_mul_of_one_lt_left (zero_lt_one.trans (h.radius_gt_one hstart (k + 1)))
    (h.radiusRatio_gt_one hstart k)

/-- Helper for eq:polar-radii: even radii tend to one by convergence of their logarithmic tails. -/
theorem FactorBounds.evenRadius_tendsto_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) :
    Tendsto p.evenRadius atTop (𝓝 1) := by
  rw [funext (evenRadius_eq_tailProduct p)]
  exact tailProduct_tendsto_one
    (fun n ↦ zero_lt_one.trans (h.cycleFactor_gt_one hstart n)) (h.summable_cycleLog hstart)

/-- Helper for lem:polar-geometry: every radius is at most the even radius of its own cycle. -/
theorem FactorBounds.radius_le_evenRadius {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (k : ℕ) :
    p.radius k ≤ p.evenRadius (k / 2) := by
  have hindex : 2 * (k / 2) ≤ k := by omega
  simpa only [Parameters.radius_even] using (h.radius_strictAnti hstart).antitone hindex

/-- Helper for eq:polar-radii: all original radii tend to one; the odd terms are
squeezed between the adjacent even tails. -/
theorem FactorBounds.radius_tendsto_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) :
    Tendsto p.radius atTop (𝓝 1) := by
  have htwo : (2 : ℕ) ≠ 0 := by norm_num
  have heven := (h.evenRadius_tendsto_one hstart).comp (Nat.tendsto_div_const_atTop htwo)
  have hdiff : Tendsto (fun k ↦ p.radius k - 1) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro k
      exact sub_nonneg.mpr (h.radius_gt_one hstart k).le
    · intro k
      exact sub_le_sub_right (h.radius_le_evenRadius hstart k) 1
    · simpa only [Function.comp_def, sub_self] using heven.sub_const 1
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const 1

/-- Helper for lem:polar-geometry: the uniform logarithmic radius-size constant. -/
def radiusLogScaleConstant (D : Fin 2 → ℝ) (C : ℝ) : ℝ :=
  4 * (D 0 + D 1) + (5 / 2) * cycleLogConstant D C

/-- Helper for lem:polar-geometry: the formula for the logarithmic size constant. -/
theorem radiusLogScaleConstant_def (D : Fin 2 → ℝ) (C : ℝ) :
    radiusLogScaleConstant D C = 4 * (D 0 + D 1) + (5 / 2) * cycleLogConstant D C := by
  rfl

/-- Helper for lem:polar-geometry: a common error constant for even and odd radii. -/
def radiusExpansionConstant (D : Fin 2 → ℝ) (C : ℝ) : ℝ :=
  radiusLogScaleConstant D C ^ 2 + (D 0 + D 1) + (5 / 2) * cycleLogConstant D C +
    Real.exp 1 * (D 0 + C)

/-- Helper for lem:polar-geometry: the formula for the common radius error constant. -/
theorem radiusExpansionConstant_def (D : Fin 2 → ℝ) (C : ℝ) :
    radiusExpansionConstant D C = radiusLogScaleConstant D C ^ 2 +
      (D 0 + D 1) + (5 / 2) * cycleLogConstant D C + Real.exp 1 * (D 0 + C) := by
  rfl

/-- Helper for lem:polar-geometry: the source logarithm calculation gives the leading
coefficient `3 (D₀ + D₁)` for the original even radius. -/
theorem FactorBounds.log_evenRadius_error {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (j : ℕ) :
    |Real.log (p.evenRadius j) - 3 * (D 0 + D 1) * p.scale j| ≤
      (D 0 + D 1 + (5 / 2) * cycleLogConstant D C) * p.scale j ^ 2 := by
  rw [h.log_evenRadius hstart]
  exact logTail_linear_error p hstart (add_nonneg (h.coefficient_pos 0).le
    (h.coefficient_pos 1).le) (cycleLogConstant_nonneg D h.error_nonneg)
    (h.cycleLog_error hstart) j

/-- Helper for lem:polar-geometry: a small starting scale gives a universal upper
bound for every original even radius. -/
theorem FactorBounds.evenRadius_le_exp_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (j : ℕ) :
    p.evenRadius j ≤ Real.exp 1 := by
  rw [evenRadius_eq_tailProduct]
  exact tailProduct_le_exp_one p hstart
    (fun n ↦ zero_lt_one.trans (h.cycleFactor_gt_one hstart n))
    (add_nonneg (h.coefficient_pos 0).le (h.coefficient_pos 1).le)
    (cycleLogConstant_nonneg D h.error_nonneg) (h.cycleLog_error hstart) hsmall j

/-- Helper for lem:polar-geometry: all original even and odd radii have the same
universal upper bound. -/
theorem FactorBounds.radius_le_exp_one {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (k : ℕ) :
    p.radius k ≤ Real.exp 1 := by
  exact (h.radius_le_evenRadius hstart k).trans (h.evenRadius_le_exp_one hstart hsmall _)

/-- Helper for lem:polar-geometry: the exact multiplicative recurrence expresses the
radial decrement through the original factor defect. -/
theorem FactorBounds.radius_drop_eq {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex) (k : ℕ) :
    p.radius k - p.radius (k + 1) = p.radius (k + 1) * (p.radiusRatio k - 1) := by
  rw [h.radius_eq_factor_mul_succ hstart k]
  ring

/-- Helper for lem:polar-geometry: the one-step radial decrease has the source quartic
size in either original phase, uniformly in the starting index. -/
theorem FactorBounds.radius_phase_drop_bounds {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (j : ℕ) (i : Fin 2) :
    D i / 2 * p.scale j ^ 4 ≤
        p.radius (2 * j + (i : ℕ)) - p.radius (2 * j + (i : ℕ) + 1) ∧
      p.radius (2 * j + (i : ℕ)) - p.radius (2 * j + (i : ℕ) + 1) ≤
        Real.exp 1 * (D i + C) * p.scale j ^ 4 := by
  have hdefect : 0 ≤ p.radiusRatio (2 * j + (i : ℕ)) - 1 :=
    sub_nonneg.mpr (h.factor_gt_one hstart j i).le
  have hrLower : 1 ≤ p.radius (2 * j + (i : ℕ) + 1) :=
    (h.radius_gt_one hstart _).le
  have hrUpper := h.radius_le_exp_one hstart hsmall (2 * j + (i : ℕ) + 1)
  rw [h.radius_drop_eq hstart]
  constructor
  · calc
      D i / 2 * p.scale j ^ 4 ≤ p.radiusRatio (2 * j + (i : ℕ)) - 1 := h.lower j i
      _ ≤ p.radius (2 * j + (i : ℕ) + 1) *
          (p.radiusRatio (2 * j + (i : ℕ)) - 1) := le_mul_of_one_le_left hdefect hrLower
  · calc
      p.radius (2 * j + (i : ℕ) + 1) * (p.radiusRatio (2 * j + (i : ℕ)) - 1) ≤
          Real.exp 1 * (p.radiusRatio (2 * j + (i : ℕ)) - 1) :=
        mul_le_mul_of_nonneg_right hrUpper hdefect
      _ ≤ Real.exp 1 * ((D i + C) * p.scale j ^ 4) :=
        mul_le_mul_of_nonneg_left (h.upper j i) (Real.exp_pos 1).le
      _ = Real.exp 1 * (D i + C) * p.scale j ^ 4 := by ring

/-- Helper for lem:polar-geometry: the source even radius has its uniform first-order
expansion with an explicit second-order error. -/
theorem FactorBounds.evenRadius_error {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (j : ℕ) :
    |p.evenRadius j - 1 - 3 * (D 0 + D 1) * p.scale j| ≤
      (radiusLogScaleConstant D C ^ 2 + D 0 + D 1 + (5 / 2) * cycleLogConstant D C) *
        p.scale j ^ 2 := by
  rw [evenRadius_eq_tailProduct]
  have hbound := tailProduct_linear_error p hstart
    (fun n ↦ zero_lt_one.trans (h.cycleFactor_gt_one hstart n))
    (add_nonneg (h.coefficient_pos 0).le (h.coefficient_pos 1).le)
    (cycleLogConstant_nonneg D h.error_nonneg) (h.cycleLog_error hstart) hsmall j
  simpa only [radiusLogScaleConstant_def, add_assoc] using hbound

/-- Helper for lem:polar-geometry: the difference between the original odd radius and
its even radius is at most a constant times the fourth power of the same scale. -/
theorem FactorBounds.evenRadius_sub_oddRadius_bounds
    {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (j : ℕ) :
    0 ≤ p.evenRadius j - p.oddRadius j ∧
      p.evenRadius j - p.oddRadius j ≤ Real.exp 1 * (D 0 + C) * p.scale j ^ 4 := by
  have hdrop := h.radius_phase_drop_bounds hstart hsmall j 0
  have hnonneg : 0 ≤ D 0 / 2 * p.scale j ^ 4 := by
    have hD := h.coefficient_pos 0
    positivity
  simpa only [Fin.val_zero, Nat.add_zero, Parameters.radius_even, Parameters.radius_odd] using
    And.intro (hnonneg.trans hdrop.1) hdrop.2

/-- Helper for lem:polar-geometry: even and odd radii share the exact source leading
coefficient and one common uniform second-order error constant. -/
theorem FactorBounds.radius_error {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (k : ℕ) :
    |p.radius k - 1 - 3 * (D 0 + D 1) * p.scale (k / 2)| ≤
      radiusExpansionConstant D C * p.scale (k / 2) ^ 2 := by
  have hD := h.coefficient_pos 0
  have hC := h.error_nonneg
  have hextra : 0 ≤ Real.exp 1 * (D 0 + C) := by positivity
  have htwo : (2 : ℕ) ≤ 4 := by norm_num
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · simp only [Nat.mul_div_cancel_left _ zero_lt_two, Parameters.radius_even]
    have hbound := h.evenRadius_error hstart hsmall j
    rw [radiusExpansionConstant_def]
    nlinarith [mul_nonneg hextra (sq_nonneg (p.scale j))]
  · have hquot : (2 * j + 1) / 2 = j := by omega
    rw [hquot, Parameters.radius_odd]
    have hbound := h.evenRadius_error hstart hsmall j
    have hdiff := h.evenRadius_sub_oddRadius_bounds hstart hsmall j
    have hpowers : p.scale j ^ 4 ≤ p.scale j ^ 2 :=
      pow_le_pow_of_le_one (ScaleTails.scale_nonneg p j)
        (ScaleTails.scale_le_one p hstart j) htwo
    calc
      |p.oddRadius j - 1 - 3 * (D 0 + D 1) * p.scale j| =
          |(p.evenRadius j - 1 - 3 * (D 0 + D 1) * p.scale j) -
            (p.evenRadius j - p.oddRadius j)| := by ring_nf
      _ ≤ |p.evenRadius j - 1 - 3 * (D 0 + D 1) * p.scale j| +
          |p.evenRadius j - p.oddRadius j| := abs_sub _ _
      _ ≤ (radiusLogScaleConstant D C ^ 2 + D 0 + D 1 +
          (5 / 2) * cycleLogConstant D C) * p.scale j ^ 2 +
            Real.exp 1 * (D 0 + C) * p.scale j ^ 4 := by
        rw [abs_of_nonneg hdiff.1]
        exact add_le_add hbound hdiff.2
      _ ≤ radiusExpansionConstant D C * p.scale j ^ 2 := by
        rw [radiusExpansionConstant_def]
        have hmul := mul_le_mul_of_nonneg_left hpowers hextra
        nlinarith

/-- Helper for lem:polar-geometry: a two-phase coefficient lies between the minimum
and maximum of its two values. -/
theorem phaseCoefficient_bounds (D : Fin 2 → ℝ) (i : Fin 2) :
    min (D 0) (D 1) ≤ D i ∧ D i ≤ max (D 0) (D 1) := by
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨⟨min_le_left _ _, le_max_left _ _⟩, ⟨min_le_right _ _, le_max_right _ _⟩⟩

/-- Helper for lem:polar-geometry: one pair of positive constants controls every
one-step radial decrement, independent of parity and starting index. -/
theorem FactorBounds.radius_drop_bounds {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (k : ℕ) :
    (min (D 0) (D 1) / 2) * p.scale (k / 2) ^ 4 ≤ p.radius k - p.radius (k + 1) ∧
      p.radius k - p.radius (k + 1) ≤
        (Real.exp 1 * (max (D 0) (D 1) + C)) * p.scale (k / 2) ^ 4 := by
  have hphase : k % 2 < 2 := Nat.mod_lt k zero_lt_two
  let i : Fin 2 := ⟨k % 2, hphase⟩
  have hindex : 2 * (k / 2) + (i : ℕ) = k := by
    dsimp only [i]
    omega
  have hstage := h.radius_phase_drop_bounds hstart hsmall (k / 2) i
  rw [hindex] at hstage
  have hcoeff := phaseCoefficient_bounds D i
  have hpower := pow_nonneg (ScaleTails.scale_nonneg p (k / 2)) 4
  constructor
  · exact (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hcoeff.1 zero_le_two) hpower).trans hstage.1
  · exact hstage.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hcoeff.2 le_rfl) (Real.exp_pos 1).le) hpower)

/-- Helper for lem:polar-geometry: the logarithmic scale constant is strictly positive
when the two source coefficients are positive. -/
theorem radiusLogScaleConstant_pos {D : Fin 2 → ℝ} {C : ℝ}
    (hD : ∀ i, 0 < D i) (hC : 0 ≤ C) : 0 < radiusLogScaleConstant D C := by
  have hE := hD 0
  have hO := hD 1
  have hlog := cycleLogConstant_nonneg D hC
  rw [radiusLogScaleConstant_def]
  positivity

/-- Helper for lem:polar-geometry: the common radius error constant is strictly positive
when the two source coefficients are positive. -/
theorem radiusExpansionConstant_pos {D : Fin 2 → ℝ} {C : ℝ}
    (hD : ∀ i, 0 < D i) (hC : 0 ≤ C) : 0 < radiusExpansionConstant D C := by
  have hE := hD 0
  have hO := hD 1
  have hlog := cycleLogConstant_nonneg D hC
  rw [radiusExpansionConstant_def]
  positivity

/-- Helper for eq:polar-radii and lem:polar-geometry: the radius conclusions proved
from the logarithmic source argument, with quantitative constants preceding the data.
This interface states conclusions, rather than assuming any product convergence. -/
structure RadiusEstimates (p : Parameters) (D : Fin 2 → ℝ) (K c B : ℝ) : Prop where
  /-- Helper for eq:polar-radii: all prescribed positive paired tails converge. -/
  multipliable : ∀ j, Multipliable (fun n ↦ p.radiusRatio (2 * (j + n)) *
    p.radiusRatio (2 * (j + n) + 1))
  /-- Helper for eq:polar-radii: each original factor is strictly above one. -/
  factor_above_one : ∀ k, 1 < p.radiusRatio k
  /-- Helper for eq:polar-radii: the logarithm of the exact original even radius. -/
  log_evenRadius : ∀ j, Real.log (p.evenRadius j) = logTail (cycleFactor p) j
  /-- Helper for eq:polar-radii: the original even tail-product shift. -/
  even_shift : ∀ j, p.evenRadius j = p.radiusRatio (2 * j) *
    p.radiusRatio (2 * j + 1) * p.evenRadius (j + 1)
  /-- Helper for eq:polar-radii: all original even and odd radii exceed one. -/
  above_one : ∀ k, 1 < p.radius k
  /-- Helper for eq:polar-radii: the full original radius sequence strictly decreases. -/
  strictAnti : StrictAnti p.radius
  /-- Helper for eq:polar-radii: the original radii tend to one. -/
  tendsto_one : Tendsto p.radius atTop (𝓝 1)
  /-- Helper for eq:polar-radii: the exact physical quotient recurrence. -/
  recurrence : ∀ k, p.radius (k + 1) = p.radius k / p.radiusRatio k
  /-- Helper for lem:polar-geometry: a universal upper radius bound. -/
  upper : ∀ k, p.radius k ≤ Real.exp 1
  /-- Helper for lem:polar-geometry: both phases have the source linear radial expansion. -/
  expansion : ∀ k, |p.radius k - 1 - 3 * (D 0 + D 1) * p.scale (k / 2)| ≤
    K * p.scale (k / 2) ^ 2
  /-- Helper for lem:polar-geometry: the source uniform quartic radial decrement. -/
  drop : ∀ k, c * p.scale (k / 2) ^ 4 ≤ p.radius k - p.radius (k + 1) ∧
    p.radius k - p.radius (k + 1) ≤ B * p.scale (k / 2) ^ 4

/-- Helper for eq:polar-radii and lem:polar-geometry: the exact original products
satisfy all radius conclusions once the scalar phase estimates are discharged. -/
theorem radiusEstimatesOfFactorBounds {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) :
    RadiusEstimates p D (radiusExpansionConstant D C) (min (D 0) (D 1) / 2)
      (Real.exp 1 * (max (D 0) (D 1) + C)) := by
  exact ⟨h.multipliable_cycleTail hstart, h.radiusRatio_gt_one hstart,
    h.log_evenRadius hstart, h.evenRadius_shift hstart,
    h.radius_gt_one hstart, h.radius_strictAnti hstart, h.radius_tendsto_one hstart,
    h.radius_succ hstart, h.radius_le_exp_one hstart hsmall, h.radius_error hstart hsmall,
    h.radius_drop_bounds hstart hsmall⟩

/-- Helper for lem:polar-geometry: the even radius differs from one by at most a
uniform multiple of the prescribed scale. -/
theorem FactorBounds.evenRadius_sub_one_le {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (j : ℕ) :
    p.evenRadius j - 1 ≤ 2 * radiusLogScaleConstant D C * p.scale j := by
  have hD : 0 ≤ D 0 + D 1 := add_nonneg (h.coefficient_pos 0).le (h.coefficient_pos 1).le
  have hlogC := cycleLogConstant_nonneg D h.error_nonneg
  have hlogBound := abs_logTail_le_scale p hstart hD hlogC (h.cycleLog_error hstart) j
  have hexp := Real.abs_exp_sub_one_le
    (abs_logTail_le_one p hstart hD hlogC (h.cycleLog_error hstart) hsmall j)
  rw [h.evenRadius_eq_exp hstart]
  calc
    Real.exp (logTail (cycleFactor p) j) - 1 ≤
        |Real.exp (logTail (cycleFactor p) j) - 1| := le_abs_self _
    _ ≤ 2 * |logTail (cycleFactor p) j| := hexp
    _ ≤ 2 * radiusLogScaleConstant D C * p.scale j := by
      rw [radiusLogScaleConstant_def]
      linarith

/-- Helper for lem:polar-geometry: each actual phase decrement has its exact source
quartic leading coefficient and a uniform fifth-order error. -/
theorem FactorBounds.radius_phase_drop_error {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (j : ℕ) (i : Fin 2) :
    |p.radius (2 * j + (i : ℕ)) - p.radius (2 * j + (i : ℕ) + 1) -
        D i * p.scale j ^ 4| ≤
      (C + 2 * radiusLogScaleConstant D C * (D i + C)) * p.scale j ^ 5 := by
  have hindex : 2 * j ≤ 2 * j + (i : ℕ) + 1 := by omega
  have hnext : p.radius (2 * j + (i : ℕ) + 1) ≤ p.evenRadius j := by
    simpa only [Parameters.radius_even] using (h.radius_strictAnti hstart).antitone hindex
  have hnextSmall : p.radius (2 * j + (i : ℕ) + 1) - 1 ≤
      2 * radiusLogScaleConstant D C * p.scale j :=
    (sub_le_sub_right hnext 1).trans (h.evenRadius_sub_one_le hstart hsmall j)
  have hnextNonneg : 0 ≤ p.radius (2 * j + (i : ℕ) + 1) - 1 :=
    sub_nonneg.mpr (h.radius_gt_one hstart _).le
  have hdefect : 0 ≤ p.radiusRatio (2 * j + (i : ℕ)) - 1 :=
    sub_nonneg.mpr (h.factor_gt_one hstart j i).le
  have hC := h.error_nonneg
  have ht := ScaleTails.scale_nonneg p j
  have hprod := mul_le_mul hnextSmall (h.upper j i) hdefect
    (mul_nonneg (mul_nonneg zero_le_two (radiusLogScaleConstant_pos h.coefficient_pos hC).le) ht)
  rw [h.radius_drop_eq hstart]
  calc
    |p.radius (2 * j + (i : ℕ) + 1) * (p.radiusRatio (2 * j + (i : ℕ)) - 1) -
        D i * p.scale j ^ 4| =
        |(p.radius (2 * j + (i : ℕ) + 1) - 1) *
          (p.radiusRatio (2 * j + (i : ℕ)) - 1) +
            (p.radiusRatio (2 * j + (i : ℕ)) - 1 - D i * p.scale j ^ 4)| := by ring_nf
    _ ≤ |(p.radius (2 * j + (i : ℕ) + 1) - 1) *
          (p.radiusRatio (2 * j + (i : ℕ)) - 1)| +
        |p.radiusRatio (2 * j + (i : ℕ)) - 1 - D i * p.scale j ^ 4| := abs_add_le _ _
    _ ≤ (2 * radiusLogScaleConstant D C * p.scale j) *
        ((D i + C) * p.scale j ^ 4) + C * p.scale j ^ 5 := by
      rw [abs_of_nonneg (mul_nonneg hnextNonneg hdefect)]
      exact add_le_add hprod (h.expansion j i)
    _ = (C + 2 * radiusLogScaleConstant D C * (D i + C)) * p.scale j ^ 5 := by ring

/-- Helper for lem:polar-geometry: a uniform fifth-order error constant for the total
radial decrement over one original even-odd cycle. -/
def cycleDropConstant (D : Fin 2 → ℝ) (C : ℝ) : ℝ :=
  2 * C + 2 * radiusLogScaleConstant D C * (D 0 + D 1 + 2 * C)

/-- Helper for lem:polar-geometry: the formula for the cycle-decrement error constant. -/
theorem cycleDropConstant_def (D : Fin 2 → ℝ) (C : ℝ) :
    cycleDropConstant D C =
      2 * C + 2 * radiusLogScaleConstant D C * (D 0 + D 1 + 2 * C) := by
  rfl

/-- Helper for lem:polar-geometry: the exact original even-to-even radial decrement
has the source paired coefficient and a uniform fifth-order error. -/
theorem FactorBounds.evenRadius_drop_error {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hstart : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1) (j : ℕ) :
    |p.evenRadius j - p.evenRadius (j + 1) - (D 0 + D 1) * p.scale j ^ 4| ≤
      cycleDropConstant D C * p.scale j ^ 5 := by
  have hE := h.radius_phase_drop_error hstart hsmall j 0
  have hO := h.radius_phase_drop_error hstart hsmall j 1
  have hnext : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  simp only [Fin.val_zero, Fin.val_one, Nat.add_zero, Parameters.radius_even,
    Parameters.radius_odd] at hE hO
  rw [hnext, Parameters.radius_even] at hO
  calc
    |p.evenRadius j - p.evenRadius (j + 1) - (D 0 + D 1) * p.scale j ^ 4| =
        |(p.evenRadius j - p.oddRadius j - D 0 * p.scale j ^ 4) +
          (p.oddRadius j - p.evenRadius (j + 1) - D 1 * p.scale j ^ 4)| := by ring_nf
    _ ≤ |p.evenRadius j - p.oddRadius j - D 0 * p.scale j ^ 4| +
        |p.oddRadius j - p.evenRadius (j + 1) - D 1 * p.scale j ^ 4| := abs_add_le _ _
    _ ≤ cycleDropConstant D C * p.scale j ^ 5 := by
      rw [cycleDropConstant_def]
      linarith

/-- Helper for lem:polar-geometry: summing a controlled decrement over a finite interval
gives the endpoint difference with the summed error. -/
theorem sum_decrement_error {r u v : ℕ → ℝ} {D C : ℝ}
    (herror : ∀ j, |r j - r (j + 1) - D * u j| ≤ C * v j)
    {A B : ℕ} (hAB : A ≤ B) :
    |r A - r B - D * ∑ j ∈ Finset.Ico A B, u j| ≤
      C * ∑ j ∈ Finset.Ico A B, v j := by
  have htel : (∑ j ∈ Finset.Ico A B, (r j - r (j + 1))) = r A - r B := by
    have h := Finset.sum_Ico_sub r hAB
    rw [Finset.sum_sub_distrib] at h ⊢
    linarith
  calc
    |r A - r B - D * ∑ j ∈ Finset.Ico A B, u j| =
        |∑ j ∈ Finset.Ico A B, (r j - r (j + 1) - D * u j)| := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htel]
    _ ≤ ∑ j ∈ Finset.Ico A B, |r j - r (j + 1) - D * u j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Ico A B, C * v j :=
      Finset.sum_le_sum (fun j _ ↦ herror j)
    _ = C * ∑ j ∈ Finset.Ico A B, v j := (Finset.mul_sum _ _ _).symm

/-- Helper for eq:polar-radii: the accepted actual W expansion discharges the scalar
phase interface uniformly for every larger starting index. The two smallness thresholds
are chosen only after the source coefficients and common W error constant. -/
theorem actualFactorBounds :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ C > 0, ∃ J : ℕ, 0 < J ∧
        ∀ j₀ ≥ J, let p := Parameters.of j₀ νStar
          FactorBounds p (RadiusExpansions.radiusCoefficient νStar) C ∧
            radiusLogScaleConstant (RadiusExpansions.radiusCoefficient νStar) C * p.scale 0 ≤
              1 := by
  obtain ⟨η, hη, hactual⟩ := RadiusExpansions.actualSlopeAndRadiusEstimates
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, C, hC, J₀, hJ₀, hphase⟩ := hactual νStar hnear
  let D := RadiusExpansions.radiusCoefficient νStar
  have hD : ∀ i, 0 < D i := RadiusExpansions.radiusCoefficient_pos νStar hparameter
  let d := min (D 0) (D 1)
  have hd : 0 < d := lt_min (hD 0) (hD 1)
  have hdle : ∀ i : Fin 2, d ≤ D i := fun i ↦ (phaseCoefficient_bounds D i).1
  let H := radiusLogScaleConstant D C
  have hH : 0 < H := radiusLogScaleConstant_pos hD hC.le
  have hcutoff : 0 < min (d / (2 * C)) (1 / H) := by positivity
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold _ hcutoff
  refine ⟨hparameter, C, hC, max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  let p := Parameters.of j₀ νStar
  have hj₀old : J₀ ≤ j₀ := (le_max_left J₀ J₁).trans hj₀
  have hj₀scale : J₁ ≤ j₀ := (le_max_right J₀ J₁).trans hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ₀.trans_le hj₀old
  have hzero : p.scale 0 < min (d / (2 * C)) (1 / H) := hscale νStar j₀ hj₀scale
  have hzeroC : p.scale 0 < d / (2 * C) := hzero.trans_le (min_le_left _ _)
  have hzeroH : p.scale 0 < 1 / H := hzero.trans_le (min_le_right _ _)
  have htwoC : 0 < 2 * C := by positivity
  have hsmallC : ∀ i, C * p.scale 0 ≤ D i / 2 := by
    intro i
    nlinarith [(lt_div_iff₀ htwoC).mp hzeroC, hdle i]
  have hsmallH : H * p.scale 0 ≤ 1 := by
    nlinarith [(lt_div_iff₀ hH).mp hzeroH]
  have herror : ∀ j (i : Fin 2),
      |p.radiusRatio (2 * j + (i : ℕ)) - 1 - D i * p.scale j ^ 4| ≤
        C * p.scale j ^ 5 := by
    intro j i
    exact (hphase j₀ hj₀old j i).2.2
  exact ⟨factorBounds_of_expansion p hstart hD hC.le herror hsmallC, hsmallH⟩

/-- eq:polar-radii and eq:polar-orders (radial component): the prescribed original
tail products converge, exceed one, strictly decrease to one, satisfy the exact quotient
recurrence, and have the source first-order expansion and quartic radial decrease.
All quantitative constants are chosen before every subsequent starting index. -/
theorem polarRadiusProducts :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ K > 0, ∃ c > 0, ∃ B > 0,
        ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
          RadiusEstimates (Parameters.of j₀ νStar)
            (RadiusExpansions.radiusCoefficient νStar) K c B := by
  obtain ⟨η, hη, hbounds⟩ := actualFactorBounds
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, C, hC, J, hJ, hactual⟩ := hbounds νStar hnear
  let D := RadiusExpansions.radiusCoefficient νStar
  have hD : ∀ i, 0 < D i := RadiusExpansions.radiusCoefficient_pos νStar hparameter
  have hK := radiusExpansionConstant_pos hD hC.le
  have hc : 0 < min (D 0) (D 1) / 2 := half_pos (lt_min (hD 0) (hD 1))
  have hmax : 0 < max (D 0) (D 1) := (hD 0).trans_le (le_max_left _ _)
  have hB : 0 < Real.exp 1 * (max (D 0) (D 1) + C) := by positivity
  refine ⟨hparameter, radiusExpansionConstant D C, hK, min (D 0) (D 1) / 2, hc,
    Real.exp 1 * (max (D 0) (D 1) + C), hB, J, hJ, ?_⟩
  intro j₀ hj₀
  have hstart : 0 < (Parameters.of j₀ νStar).startIndex := by
    simpa only [Parameters.of_startIndex] using hJ.trans_le hj₀
  exact radiusEstimatesOfFactorBounds (hactual j₀ hj₀).1 hstart (hactual j₀ hj₀).2

/-- Helper for lem:polar-geometry: the actual prescribed scale at the source cubic
cycle endpoint is exactly `N⁻¹`. -/
theorem scale_cubic (p : Parameters) (N : ℕ) (hstart : p.startIndex ≤ N ^ 3) :
    p.scale (N ^ 3 - p.startIndex) = (N : ℝ)⁻¹ := by
  rw [Parameters.scale_def, Nat.add_sub_of_le hstart, ScaleTails.cubic_rpow_neg_third]

/-- Helper for lem:polar-geometry: the quintic error summed over one complete turn
is at most `4 N⁻³`, uniformly in the original starting index. -/
theorem quinticFullTurn_le (p : Parameters) (hpositive : 0 < p.startIndex) (N : ℕ)
    (hN : 0 < N) (hstart : p.startIndex ≤ N ^ 3) :
    (∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex) ((N + 1) ^ 3 - p.startIndex),
      p.scale j ^ 5) ≤ 4 * (N : ℝ) ^ (-3 : ℤ) := by
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : 0 ≤ (N : ℝ)⁻¹ := (inv_pos.mpr hNreal).le
  have hqone : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNge
  have hexponents : (2 : ℕ) ≤ 4 := by norm_num
  have hqfour : ((N : ℝ)⁻¹) ^ 4 ≤ ((N : ℝ)⁻¹) ^ 2 :=
    pow_le_pow_of_le_one hq hqone hexponents
  have hden : (N : ℝ) * N ≤ (N : ℝ) * (N + 1) := by nlinarith
  have hprincipal : 3 / ((N : ℝ) * (N + 1)) ≤ 3 * ((N : ℝ)⁻¹) ^ 2 := by
    calc
      3 / ((N : ℝ) * (N + 1)) ≤ 3 / ((N : ℝ) * N) :=
        div_le_div_of_nonneg_left zero_le_three (mul_pos hNreal hNreal) hden
      _ = 3 * ((N : ℝ)⁻¹) ^ 2 := by
        simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
  have hquartic := (abs_le.mp (ScaleTails.quarticFullTurn_abs_error p N hN hstart)).2
  simp only [zpow_neg, zpow_ofNat, ← inv_pow] at hquartic
  have hfour : (∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex)
      ((N + 1) ^ 3 - p.startIndex), p.scale j ^ 4) ≤ 4 * ((N : ℝ)⁻¹) ^ 2 := by
    linarith
  have hpointwise : ∀ j ∈ Finset.Ico (N ^ 3 - p.startIndex)
      ((N + 1) ^ 3 - p.startIndex), p.scale j ^ 5 ≤ (N : ℝ)⁻¹ * p.scale j ^ 4 := by
    intro j hj
    have hscale : p.scale j ≤ (N : ℝ)⁻¹ := by
      rw [← scale_cubic p N hstart]
      exact ScaleTails.scale_antitone p hpositive (Finset.mem_Ico.mp hj).1
    calc
      p.scale j ^ 5 = p.scale j * p.scale j ^ 4 := by ring
      _ ≤ (N : ℝ)⁻¹ * p.scale j ^ 4 :=
        mul_le_mul_of_nonneg_right hscale (pow_nonneg (ScaleTails.scale_nonneg p j) 4)
  calc
    (∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex) ((N + 1) ^ 3 - p.startIndex),
        p.scale j ^ 5) ≤
        ∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex) ((N + 1) ^ 3 - p.startIndex),
          (N : ℝ)⁻¹ * p.scale j ^ 4 := Finset.sum_le_sum hpointwise
    _ = (N : ℝ)⁻¹ * ∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex)
        ((N + 1) ^ 3 - p.startIndex), p.scale j ^ 4 := (Finset.mul_sum _ _ _).symm
    _ ≤ (N : ℝ)⁻¹ * (4 * ((N : ℝ)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hfour hq
    _ = 4 * (N : ℝ) ^ (-3 : ℤ) := by
      simp only [zpow_neg, zpow_ofNat, ← inv_pow]
      ring

/-- Helper for lem:polar-geometry: the cycle-decrement remainder constant is nonnegative. -/
theorem cycleDropConstant_nonneg {D : Fin 2 → ℝ} {C : ℝ}
    (hD : ∀ i, 0 < D i) (hC : 0 ≤ C) : 0 ≤ cycleDropConstant D C := by
  have hE := hD 0
  have hO := hD 1
  have hH := radiusLogScaleConstant_pos hD hC
  rw [cycleDropConstant_def]
  positivity

/-- Helper for lem:polar-geometry: summing the original radial decrements over a
complete cubic turn yields the source leading coefficient with uniform `O(N⁻³)` error. -/
theorem FactorBounds.fullTurn_error {p : Parameters} {D : Fin 2 → ℝ} {C : ℝ}
    (h : FactorBounds p D C) (hpositive : 0 < p.startIndex)
    (hsmall : radiusLogScaleConstant D C * p.scale 0 ≤ 1)
    (N : ℕ) (hN : 0 < N) (hstart : p.startIndex ≤ N ^ 3) :
    |p.evenRadius (N ^ 3 - p.startIndex) -
        p.evenRadius ((N + 1) ^ 3 - p.startIndex) -
          3 * (D 0 + D 1) / ((N : ℝ) * (N + 1))| ≤
      (D 0 + D 1 + 4 * cycleDropConstant D C) * (N : ℝ) ^ (-3 : ℤ) := by
  have hAB : N ^ 3 - p.startIndex ≤ (N + 1) ^ 3 - p.startIndex :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_left (Nat.le_succ N) 3) p.startIndex
  have hsegment := sum_decrement_error (h.evenRadius_drop_error hpositive hsmall) hAB
  have hscalar := ScaleTails.quarticFullTurn_abs_error p N hN hstart
  have hDsum : 0 ≤ D 0 + D 1 := add_nonneg (h.coefficient_pos 0).le (h.coefficient_pos 1).le
  have hdropC := cycleDropConstant_nonneg h.coefficient_pos h.error_nonneg
  have hquintic := mul_le_mul_of_nonneg_left
    (quinticFullTurn_le p hpositive N hN hstart) hdropC
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexponents : (3 : ℕ) ≤ 4 := by norm_num
  have hpowers : (N : ℝ) ^ (-4 : ℤ) ≤ (N : ℝ) ^ (-3 : ℤ) := by
    simp only [zpow_neg]
    exact inv_pow_le_inv_pow_of_le hNge hexponents
  have hscalarMul : |(D 0 + D 1) * ((∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex)
      ((N + 1) ^ 3 - p.startIndex), p.scale j ^ 4) -
        3 / ((N : ℝ) * (N + 1)))| ≤ (D 0 + D 1) * (N : ℝ) ^ (-4 : ℤ) := by
    rw [abs_mul, abs_of_nonneg hDsum]
    exact mul_le_mul_of_nonneg_left hscalar hDsum
  calc
    |p.evenRadius (N ^ 3 - p.startIndex) -
        p.evenRadius ((N + 1) ^ 3 - p.startIndex) -
          3 * (D 0 + D 1) / ((N : ℝ) * (N + 1))| =
        |(p.evenRadius (N ^ 3 - p.startIndex) -
          p.evenRadius ((N + 1) ^ 3 - p.startIndex) - (D 0 + D 1) *
            ∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex) ((N + 1) ^ 3 - p.startIndex),
              p.scale j ^ 4) + (D 0 + D 1) *
                ((∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex)
                  ((N + 1) ^ 3 - p.startIndex), p.scale j ^ 4) -
                    3 / ((N : ℝ) * (N + 1)))| := by ring_nf
    _ ≤ |p.evenRadius (N ^ 3 - p.startIndex) -
          p.evenRadius ((N + 1) ^ 3 - p.startIndex) - (D 0 + D 1) *
            ∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex) ((N + 1) ^ 3 - p.startIndex),
              p.scale j ^ 4| +
        |(D 0 + D 1) * ((∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex)
          ((N + 1) ^ 3 - p.startIndex), p.scale j ^ 4) -
            3 / ((N : ℝ) * (N + 1)))| := abs_add_le _ _
    _ ≤ cycleDropConstant D C * (∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex)
          ((N + 1) ^ 3 - p.startIndex), p.scale j ^ 5) +
        (D 0 + D 1) * (N : ℝ) ^ (-4 : ℤ) := add_le_add hsegment hscalarMul
    _ ≤ (D 0 + D 1 + 4 * cycleDropConstant D C) * (N : ℝ) ^ (-3 : ℤ) := by
      have hmul := mul_le_mul_of_nonneg_left hpowers hDsum
      nlinarith

/-- Helper for lem:polar-geometry: the complete-turn source radial asymptotic holds
for the actual original radius products with one error constant before every `j₀`. -/
theorem polarRadiusFullTurn :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ K > 0, ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J, ∀ N : ℕ, 0 < N → j₀ ≤ N ^ 3 →
        let p := Parameters.of j₀ νStar
        |p.evenRadius (N ^ 3 - j₀) - p.evenRadius ((N + 1) ^ 3 - j₀) -
            3 * (RadiusExpansions.radiusCoefficient νStar 0 +
              RadiusExpansions.radiusCoefficient νStar 1) / ((N : ℝ) * (N + 1))| ≤
          K * (N : ℝ) ^ (-3 : ℤ) := by
  obtain ⟨η, hη, hbounds⟩ := actualFactorBounds
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, C, hC, J, hJ, hactual⟩ := hbounds νStar hnear
  let D := RadiusExpansions.radiusCoefficient νStar
  have hD : ∀ i, 0 < D i := RadiusExpansions.radiusCoefficient_pos νStar hparameter
  have hdrop := cycleDropConstant_nonneg hD hC.le
  have hK : 0 < D 0 + D 1 + 4 * cycleDropConstant D C := by
    have hE := hD 0
    have hO := hD 1
    positivity
  refine ⟨D 0 + D 1 + 4 * cycleDropConstant D C, hK, J, hJ, ?_⟩
  intro j₀ hj₀ N hN hstart
  have hpositive : 0 < (Parameters.of j₀ νStar).startIndex := by
    simpa only [Parameters.of_startIndex] using hJ.trans_le hj₀
  have hstart' : (Parameters.of j₀ νStar).startIndex ≤ N ^ 3 := by
    simpa only [Parameters.of_startIndex] using hstart
  simpa only [Parameters.of_startIndex] using
    (hactual j₀ hj₀).1.fullTurn_error hpositive (hactual j₀ hj₀).2 N hN hstart'

end DFP.Polar.RadiusProducts

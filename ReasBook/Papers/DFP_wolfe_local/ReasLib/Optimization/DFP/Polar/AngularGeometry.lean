module

public import ReasLib.Optimization.DFP.Polar.ScaleTails
public import ReasLib.Optimization.DFP.Polar.Normalized.Recurrence
public import Mathlib.Topology.Sequences

public section

noncomputable section

open Set Filter
open scoped Topology Asymptotics

namespace DFP.Polar.AngularGeometry

/-- Helper for lem:polar-geometry and eq:polar-angles: the fixed source
angle `a = 2π/9` is positive. -/
theorem baseAngle_pos : 0 < baseAngle := by
  rw [baseAngle_def]
  positivity

/-- Helper for lem:polar-geometry and eq:polar-angles: cubing the named
positive root recovers the prescribed cubic scale factor. -/
theorem unitRoot_cube {t : ℝ} (ht : 0 ≤ t) :
    Normalized.unitRoot t ^ 3 = 1 + t ^ 3 := by
  have hbase : 0 < 1 + t ^ 3 := by
    positivity
  rw [Normalized.unitRoot_def, ← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have hexponent : (3 : ℝ) * (Real.log (1 + t ^ 3) / 3) = Real.log (1 + t ^ 3) := by
    ring
  rw [hexponent, Real.exp_log hbase]

/-- Helper for lem:polar-geometry and eq:polar-angles: on scales in `[0,1]`
the positive cubic root lies between one and two. -/
theorem unitRoot_bounds {t : ℝ} (ht : 0 ≤ t) (htone : t ≤ 1) :
    1 ≤ Normalized.unitRoot t ∧ Normalized.unitRoot t ≤ 2 := by
  have hroot : 0 ≤ Normalized.unitRoot t := by
    rw [Normalized.unitRoot_def]
    exact (Real.exp_pos _).le
  have hcube := unitRoot_cube ht
  have htCube : t ^ 3 ≤ 1 := pow_le_one₀ ht htone
  have hthree : (3 : ℕ) ≠ 0 := by
    norm_num
  constructor
  · apply (pow_le_pow_iff_left₀ zero_le_one hroot hthree).mp
    norm_num only [one_pow]
    linarith [pow_nonneg ht 3]
  · apply (pow_le_pow_iff_left₀ hroot (zero_le_two : (0 : ℝ) ≤ 2) hthree).mp
    norm_num
    linarith

/-- Helper for lem:polar-geometry and eq:polar-angles: the canceled angular
factor has uniform positive bounds on the full prescribed scale range. -/
theorem angleFactor_bounds {t : ℝ} (ht : 0 ≤ t) (htone : t ≤ 1) :
    9 * baseAngle / 7 ≤ Normalized.angleFactor t ∧
      Normalized.angleFactor t ≤ 3 * baseAngle := by
  have hroot := unitRoot_bounds ht htone
  have hdenomLower : 3 ≤ Normalized.unitRoot t ^ 2 + Normalized.unitRoot t + 1 := by
    nlinarith [sq_nonneg (Normalized.unitRoot t - 1)]
  have hdenomUpper : Normalized.unitRoot t ^ 2 + Normalized.unitRoot t + 1 ≤ 7 := by
    have hsquare := pow_le_pow_left₀ (zero_le_one.trans hroot.1) hroot.2 2
    nlinarith
  have hdenomPos : 0 < Normalized.unitRoot t ^ 2 + Normalized.unitRoot t + 1 := by
    linarith
  have ha := baseAngle_pos
  have hnum : 0 ≤ 9 * baseAngle := by
    positivity
  have hthree : (0 : ℝ) < 3 := by
    norm_num
  rw [Normalized.angleFactor_def]
  constructor
  · exact div_le_div_of_nonneg_left hnum hdenomPos hdenomUpper
  · have hupper := div_le_div_of_nonneg_left hnum hthree hdenomLower
    linarith

/-- Helper for lem:polar-geometry and eq:polar-angles: the two stage weights
lie between one third and two thirds. -/
theorem stageWeight_bounds (i : Fin 2) :
    (1 / 3 : ℝ) ≤ Normalized.stageWeight i ∧ Normalized.stageWeight i ≤ 2 / 3 := by
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · rw [Normalized.stageWeight_zero]
    norm_num
  · rw [Normalized.stageWeight_one]
    norm_num

/-- Helper for lem:polar-geometry and eq:polar-angles: the normalized stage
factor is uniformly between `3a/7` and `2a` for scales in `[0,1]`. -/
theorem stageAngleFactor_bounds (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (htone : t ≤ 1) :
    3 * baseAngle / 7 ≤ Normalized.stageAngleFactor i t ∧
      Normalized.stageAngleFactor i t ≤ 2 * baseAngle := by
  have ha := baseAngle_pos
  have hweight := stageWeight_bounds i
  have hfactor := angleFactor_bounds ht htone
  have hweightNonneg : 0 ≤ Normalized.stageWeight i := by
    linarith
  have hfactorNonneg : 0 ≤ Normalized.angleFactor t := by
    have hconstant : 0 < 9 * baseAngle / 7 := by
      positivity
    linarith
  have hlowerNonneg : 0 ≤ 9 * baseAngle / 7 := by
    positivity
  rw [Normalized.stageAngleFactor_def]
  constructor
  · calc
      3 * baseAngle / 7 = (1 / 3) * (9 * baseAngle / 7) := by ring
      _ ≤ Normalized.stageWeight i * (9 * baseAngle / 7) :=
        mul_le_mul_of_nonneg_right hweight.1 hlowerNonneg
      _ ≤ Normalized.stageWeight i * Normalized.angleFactor t :=
        mul_le_mul_of_nonneg_left hfactor.1 hweightNonneg
  · calc
      Normalized.stageWeight i * Normalized.angleFactor t ≤ (2 / 3) * Normalized.angleFactor t :=
        mul_le_mul_of_nonneg_right hweight.2 hfactorNonneg
      _ ≤ (2 / 3) * (3 * baseAngle) := by
        linarith [hfactor.2]
      _ = 2 * baseAngle := by ring

/-- Helper for lem:polar-geometry and eq:polar-angles: normalized stage
angles have uniform quadratic bounds with positive source constants. -/
theorem stageAngle_bounds (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) (htone : t ≤ 1) :
    (3 * baseAngle / 7) * t ^ 2 ≤ Normalized.stageAngle i t ∧
      Normalized.stageAngle i t ≤ (2 * baseAngle) * t ^ 2 := by
  have hfactor := stageAngleFactor_bounds i ht htone
  rw [Normalized.stageAngle_def]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hfactor.1 (sq_nonneg t)]
  · nlinarith [mul_le_mul_of_nonneg_left hfactor.2 (sq_nonneg t)]

/-- eq:polar-angles (uniform increment component). Every prescribed real
angular increment is between `3a/7` and `2a` times the current squared scale,
with constants independent of the positive starting index. -/
theorem angleIncrement_bounds (p : Parameters) (hstart : 0 < p.startIndex) (k : ℕ) :
    (3 * baseAngle / 7) * p.scale (k / 2) ^ 2 ≤ p.angleIncrement k ∧
      p.angleIncrement k ≤ (2 * baseAngle) * p.scale (k / 2) ^ 2 := by
  have hphase : k % 2 < 2 := Nat.mod_lt k zero_lt_two
  let i : Fin 2 := ⟨k % 2, hphase⟩
  have hindex : 2 * (k / 2) + (i : ℕ) = k := by
    dsimp only [i]
    omega
  have hstage := Normalized.stageAngle_scale p i (k / 2) hstart
  rw [hindex] at hstage
  rw [← hstage]
  exact stageAngle_bounds i (ScaleTails.scale_nonneg p _) (ScaleTails.scale_le_one p hstart _)

/-- Helper for lem:polar-geometry and eq:polar-angles: the actual two
angular phases inherit the source quadratic expansion with fifth-order error. -/
theorem angleIncrement_stage_expansion (p : Parameters) (hstart : 0 < p.startIndex)
    (i : Fin 2) :
    (fun j ↦ p.angleIncrement (2 * j + (i : ℕ)) - Normalized.limitAngle i * p.scale j ^ 2)
      =O[atTop] (fun j ↦ p.scale j ^ 5) := by
  have hsource := (Normalized.stageAngle_expansion i).comp_tendsto
    (ScaleTails.scale_tendsto_zero p)
  have hvalue (j : ℕ) : Normalized.stageAngle i (p.scale j) =
      p.angleIncrement (2 * j + (i : ℕ)) := Normalized.stageAngle_scale p i j hstart
  simpa only [Function.comp_def, hvalue] using hsource

/-- Helper for lem:polar-geometry and eq:polar-angles: the even angular
increments have leading coefficient `2a` and fifth-order scale error. -/
theorem angleIncrement_even_expansion (p : Parameters) (hstart : 0 < p.startIndex) :
    (fun j ↦ p.angleIncrement (2 * j) - (2 * baseAngle) * p.scale j ^ 2)
      =O[atTop] (fun j ↦ p.scale j ^ 5) := by
  simpa only [Fin.val_zero, Nat.add_zero, Normalized.limitAngle_zero] using
    angleIncrement_stage_expansion p hstart 0

/-- Helper for lem:polar-geometry and eq:polar-angles: the odd angular
increments have leading coefficient `a` and fifth-order scale error. -/
theorem angleIncrement_odd_expansion (p : Parameters) (hstart : 0 < p.startIndex) :
    (fun j ↦ p.angleIncrement (2 * j + 1) - baseAngle * p.scale j ^ 2)
      =O[atTop] (fun j ↦ p.scale j ^ 5) := by
  simpa only [Fin.val_one, Normalized.limitAngle_one] using
    angleIncrement_stage_expansion p hstart 1

/-- Helper for lem:polar-geometry and eq:polar-angles: all prescribed
angular increments are strictly positive for positive starting index. -/
theorem angleIncrement_pos (p : Parameters) (hstart : 0 < p.startIndex) (k : ℕ) :
    0 < p.angleIncrement k := by
  have ha := baseAngle_pos
  have hlower : 0 < (3 * baseAngle / 7) * p.scale (k / 2) ^ 2 := by
    have hcoefficient : 0 < 3 * baseAngle / 7 := by
      positivity
    exact mul_pos hcoefficient (sq_pos_of_pos (ScaleTails.scale_pos p hstart _))
  exact hlower.trans_le (angleIncrement_bounds p hstart k).1

/-- Helper for lem:polar-geometry and eq:polar-angles: the full prescribed
unreduced real angle sequence is strictly increasing. -/
theorem angle_strictMono (p : Parameters) (hstart : 0 < p.startIndex) : StrictMono p.angle := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hpositive := angleIncrement_pos p hstart k
  rw [Parameters.angleIncrement_def] at hpositive
  linarith

/-- Helper for lem:polar-geometry and eq:polar-angles: the cycle index
`floor(k/2)` tends to infinity along the full point index. -/
theorem halfIndex_tendsto : Tendsto (fun k : ℕ ↦ k / 2) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (2 * N)] with k hk
  omega

/-- Helper for lem:polar-geometry and eq:polar-angles: the actual prescribed
even real angles tend to positive infinity. -/
theorem evenAngle_tendsto_atTop (p : Parameters) : Tendsto p.evenAngle atTop atTop := by
  have hindex : Tendsto (fun j : ℕ ↦ ((p.startIndex + j : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, add_comm] using
      tendsto_atTop_add_const_right atTop (p.startIndex : ℝ) tendsto_natCast_atTop_atTop
  have hexponent : (0 : ℝ) < 1 / 3 := by
    norm_num
  have hcoefficient : 0 < 2 * Real.pi := by
    positivity
  rw [funext (Parameters.evenAngle_def p)]
  exact ((tendsto_rpow_atTop hexponent).comp hindex).const_mul_atTop hcoefficient

/-- Helper for lem:polar-geometry and eq:polar-angles: the full prescribed
real angle sequence diverges to positive infinity. -/
theorem angle_tendsto_atTop (p : Parameters) (hstart : 0 < p.startIndex) :
    Tendsto p.angle atTop atTop := by
  have hlower (k : ℕ) : p.evenAngle (k / 2) ≤ p.angle k := by
    rw [← Parameters.angle_even]
    have hindex : 2 * (k / 2) ≤ k := by
      omega
    exact (angle_strictMono p hstart).monotone hindex
  exact tendsto_atTop_mono hlower ((evenAngle_tendsto_atTop p).comp halfIndex_tendsto)

/-- Helper for lem:polar-geometry and eq:polar-angles: the positive prescribed
angular increments tend to zero along the full point sequence. -/
theorem angleIncrement_tendsto_zero (p : Parameters) (hstart : 0 < p.startIndex) :
    Tendsto p.angleIncrement atTop (𝓝 0) := by
  have hscale : Tendsto (fun k : ℕ ↦ p.scale (k / 2) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, zero_pow two_ne_zero] using
      ((ScaleTails.scale_tendsto_zero p).comp halfIndex_tendsto).pow 2
  have hupper : Tendsto (fun k : ℕ ↦ (2 * baseAngle) * p.scale (k / 2) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hscale.const_mul (2 * baseAngle)
  exact squeeze_zero (fun k ↦ (angleIncrement_pos p hstart k).le)
    (fun k ↦ (angleIncrement_bounds p hstart k).2) hupper

/-- Helper for lem:polar-geometry and eq:polar-angles: taking the real cubic
root of a natural cubic endpoint gives the endpoint itself. -/
theorem cubic_rpow_third (N : ℕ) :
    ((N ^ 3 : ℕ) : ℝ) ^ ((1 : ℝ) / 3) = (N : ℝ) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

/-- Helper for lem:polar-geometry and eq:polar-angles: the actual even angle
at cycle `N³-startIndex` is the unreduced value `2πN`. -/
theorem evenAngle_cubic (p : Parameters) (N : ℕ) (hstart : p.startIndex ≤ N ^ 3) :
    p.evenAngle (N ^ 3 - p.startIndex) = 2 * Real.pi * N := by
  rw [Parameters.evenAngle_def, Nat.add_sub_of_le hstart, cubic_rpow_third]

/-- Helper for lem:polar-geometry and eq:polar-angles: consecutive cubic
endpoints differ by exactly one full real turn, without reducing either angle. -/
theorem evenAngle_fullTurn (p : Parameters) (N : ℕ) (hstart : p.startIndex ≤ N ^ 3) :
    p.evenAngle ((N + 1) ^ 3 - p.startIndex) -
      p.evenAngle (N ^ 3 - p.startIndex) = 2 * Real.pi := by
  have hnext : p.startIndex ≤ (N + 1) ^ 3 :=
    hstart.trans (Nat.pow_le_pow_left (Nat.le_succ N) 3)
  rw [evenAngle_cubic p (N + 1) hnext, evenAngle_cubic p N hstart, Nat.cast_add, Nat.cast_one]
  ring

/-- Helper for lem:polar-geometry and eq:polar-angles: adding an integer
number of full turns preserves the polar unit vector while angles remain real. -/
theorem polarUnit_add_natPeriod (θ : ℝ) (N : ℕ) :
    polarUnit (θ + N * (2 * Real.pi)) = polarUnit θ := by
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  constructor
  · simp only [polarUnit_apply_zero, Real.cos_add_nat_mul_two_pi]
  · simp only [polarUnit_apply_one, Real.sin_add_nat_mul_two_pi]

/-- Helper for lem:polar-geometry and eq:polar-angles: the actual even
angles at cubic endpoints give precisely the same polar direction. -/
theorem polarUnit_evenAngle_cubic (p : Parameters) (N : ℕ)
    (hstart : p.startIndex ≤ N ^ 3) :
    polarUnit (p.evenAngle (N ^ 3 - p.startIndex)) = polarUnit 0 := by
  rw [evenAngle_cubic p N hstart]
  have hangle : 2 * Real.pi * N = 0 + N * (2 * Real.pi) := by
    ring
  rw [hangle]
  exact polarUnit_add_natPeriod 0 N

/-- Helper for lem:polar-geometry and eq:polar-angles: an unbounded real
sequence reaches every prescribed real level. -/
theorem exists_level_crossing {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (b : ℝ) :
    ∃ k, b ≤ a k := by
  obtain ⟨k, hk⟩ := tendsto_atTop_atTop.mp ha b
  exact ⟨k, hk k le_rfl⟩

/-- Helper for lem:polar-geometry and eq:polar-angles: the first index at
which an unbounded real sequence crosses a real level. -/
def firstCrossing (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (b : ℝ) : ℕ :=
  Nat.find (exists_level_crossing ha b)

/-- Helper for lem:polar-geometry and eq:polar-angles: a first-crossing
index reaches its level. -/
theorem firstCrossing_spec (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (b : ℝ) :
    b ≤ a (firstCrossing a ha b) := by
  exact Nat.find_spec (exists_level_crossing ha b)

/-- Helper for lem:polar-geometry and eq:polar-angles: every earlier index
is strictly below the level defining a first crossing. -/
theorem firstCrossing_before (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (b : ℝ)
    {k : ℕ} (hk : k < firstCrossing a ha b) : a k < b := by
  exact lt_of_not_ge (Nat.find_min (exists_level_crossing ha b) hk)

/-- Helper for lem:polar-geometry and eq:polar-angles: a level above the
value at a fixed index has its first crossing after that index. -/
theorem firstCrossing_after {a : ℕ → ℝ} (hmono : Monotone a)
    (ha : Tendsto a atTop atTop) {b : ℝ} {K : ℕ} (hb : a K < b) :
    K < firstCrossing a ha b := by
  by_contra hnot
  have hle := hmono (Nat.le_of_not_gt hnot)
  have hcross := firstCrossing_spec a ha b
  linarith

/-- Helper for lem:polar-geometry and eq:polar-angles: the nonnegative
overshoot of a positive first crossing is at most its preceding step. -/
theorem firstCrossing_overshoot_bounds (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (b : ℝ) (hpositive : 0 < firstCrossing a ha b) :
    0 ≤ a (firstCrossing a ha b) - b ∧
      a (firstCrossing a ha b) - b ≤
        a (firstCrossing a ha b) - a (firstCrossing a ha b - 1) := by
  have hcross := firstCrossing_spec a ha b
  have hpred : firstCrossing a ha b - 1 < firstCrossing a ha b := by
    omega
  have hbefore := firstCrossing_before a ha b hpred
  constructor
  · linarith
  · linarith

/-- Helper for lem:polar-geometry and eq:polar-angles: first crossings of
levels separated by a positive period are strictly increasing once the levels
lie beyond an index where all steps are smaller than that period. -/
theorem firstCrossings_strictMono {a b : ℕ → ℝ} {P : ℝ} {K : ℕ}
    (hmono : Monotone a) (ha : Tendsto a atTop atTop) (hP : 0 < P)
    (hgap : ∀ n, b (n + 1) - b n = P)
    (hsmall : ∀ k, K ≤ k → a (k + 1) - a k < P)
    (hafter : ∀ n, a K < b n) :
    StrictMono (fun n ↦ firstCrossing a ha (b n)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_contra hnot
  have hle : firstCrossing a ha (b (n + 1)) ≤ firstCrossing a ha (b n) :=
    Nat.le_of_not_gt hnot
  rcases hle.lt_or_eq with hlt | heq
  · have hbefore := firstCrossing_before a ha (b n) hlt
    have hcross := firstCrossing_spec a ha (b (n + 1))
    linarith [hgap n]
  · have hafterIndex := firstCrossing_after hmono ha (hafter n)
    have hpositive : 0 < firstCrossing a ha (b n) :=
      lt_of_le_of_lt (Nat.zero_le K) hafterIndex
    have hpred : firstCrossing a ha (b n) - 1 < firstCrossing a ha (b n) := by
      omega
    have hbefore := firstCrossing_before a ha (b n) hpred
    have hcross := firstCrossing_spec a ha (b (n + 1))
    have hKpred : K ≤ firstCrossing a ha (b n) - 1 := by
      omega
    have hstep := hsmall (firstCrossing a ha (b n) - 1) hKpred
    have hsucc : firstCrossing a ha (b n) - 1 + 1 = firstCrossing a ha (b n) := by
      omega
    rw [hsucc] at hstep
    rw [heq] at hcross
    linarith [hgap n]

/-- Helper for lem:polar-geometry and eq:polar-angles: overshoots along
strictly increasing positive first crossings tend to zero when the original
steps tend to zero. -/
theorem firstCrossing_overshoot_tendsto {a b : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    (hstrict : StrictMono (fun n ↦ firstCrossing a ha (b n)))
    (hpositive : ∀ n, 0 < firstCrossing a ha (b n))
    (hstep : Tendsto (fun k ↦ a (k + 1) - a k) atTop (𝓝 0)) :
    Tendsto (fun n ↦ a (firstCrossing a ha (b n)) - b n) atTop (𝓝 0) := by
  have hpred : Tendsto (fun n ↦ firstCrossing a ha (b n) - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hstrict.tendsto_atTop
  have hnormalize (n : ℕ) : firstCrossing a ha (b n) - 1 + 1 = firstCrossing a ha (b n) :=
    Nat.sub_add_cancel (hpositive n)
  have hpredStep : Tendsto
      (fun n ↦ a (firstCrossing a ha (b n)) - a (firstCrossing a ha (b n) - 1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, hnormalize] using hstep.comp hpred
  exact squeeze_zero
    (fun n ↦ (firstCrossing_overshoot_bounds a ha (b n) (hpositive n)).1)
    (fun n ↦ (firstCrossing_overshoot_bounds a ha (b n) (hpositive n)).2) hpredStep

/-- Helper for lem:polar-geometry and eq:polar-angles: periodic levels admit
strictly increasing FIRST crossings with vanishing overshoot, after one fixed
level offset. The construction selects the smallest crossing index of every level. -/
theorem exists_periodic_firstCrossings {a : ℕ → ℝ} (hmono : StrictMono a)
    (ha : Tendsto a atTop atTop) (hstep : Tendsto (fun k ↦ a (k + 1) - a k) atTop (𝓝 0))
    (P : ℝ) (hP : 0 < P) (φ : ℝ) :
    ∃ N : ℕ,
      StrictMono (fun n ↦ firstCrossing a ha (φ + ((N + n : ℕ) : ℝ) * P)) ∧
      (∀ n, a 0 < φ + ((N + n : ℕ) : ℝ) * P) ∧
      Tendsto (fun n ↦ a (firstCrossing a ha (φ + ((N + n : ℕ) : ℝ) * P)) -
        (φ + ((N + n : ℕ) : ℝ) * P)) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hstep.eventually_lt_const hP)
  obtain ⟨N, hN⟩ := exists_nat_gt ((a K - φ) / P)
  have hlevel : a K < φ + (N : ℝ) * P := by
    have hscaled := (div_lt_iff₀ hP).mp hN
    linarith
  have hafter (n : ℕ) : a K < φ + ((N + n : ℕ) : ℝ) * P := by
    have hcast : (N : ℝ) ≤ ((N + n : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right N n
    have hscaled := mul_le_mul_of_nonneg_right hcast hP.le
    linarith
  have hgap (n : ℕ) : (φ + ((N + (n + 1) : ℕ) : ℝ) * P) -
      (φ + ((N + n : ℕ) : ℝ) * P) = P := by
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hstrict := firstCrossings_strictMono hmono.monotone ha hP hgap hK hafter
  have hpositive (n : ℕ) : 0 < firstCrossing a ha (φ + ((N + n : ℕ) : ℝ) * P) :=
    lt_of_le_of_lt (Nat.zero_le K) (firstCrossing_after hmono.monotone ha (hafter n))
  refine ⟨N, hstrict, ?_, firstCrossing_overshoot_tendsto ha hstrict hpositive hstep⟩
  intro n
  exact (hmono.monotone (Nat.zero_le K)).trans_lt (hafter n)

/-- Helper for lem:polar-geometry and eq:polar-angles: the polar unit-vector
map is continuous as a map of an unreduced real angle. -/
theorem continuous_polarUnit : Continuous polarUnit := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro i
  revert i
  rw [Fin.forall_fin_two]
  constructor
  · simpa only [Function.comp_apply, polarUnit_apply_zero] using Real.continuous_cos
  · simpa only [Function.comp_apply, polarUnit_apply_one] using Real.continuous_sin

/-- lem:polar-geometry (angular first-crossing component). For every real
angle φ, the actual unreduced angle sequence has strictly increasing first
crossings of φ+2π(N+n). Their overshoots tend to zero and their polar unit
vectors tend to `polarUnit φ`. No radial assumption is used. -/
theorem exists_directional_firstCrossings (p : Parameters) (hstart : 0 < p.startIndex) (φ : ℝ) :
    ∃ N : ℕ, ∃ j : ℕ → ℕ,
      StrictMono j ∧ Tendsto j atTop atTop ∧
      (∀ n, p.angle 0 < φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)) ∧
      (∀ n, φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi) ≤ p.angle (j n)) ∧
      (∀ n k, k < j n → p.angle k < φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)) ∧
      Tendsto (fun n ↦ p.angle (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ polarUnit (p.angle (j n))) atTop (𝓝 (polarUnit φ)) := by
  have ha := angle_tendsto_atTop p hstart
  have hstep : Tendsto (fun k ↦ p.angle (k + 1) - p.angle k) atTop (𝓝 0) := by
    rw [← funext (Parameters.angleIncrement_def p)]
    exact angleIncrement_tendsto_zero p hstart
  have hperiod : 0 < 2 * Real.pi := by
    positivity
  obtain ⟨N, hstrict, hlevel, herror⟩ := exists_periodic_firstCrossings
    (angle_strictMono p hstart) ha hstep (2 * Real.pi) hperiod φ
  let j : ℕ → ℕ := fun n ↦ firstCrossing p.angle ha (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi))
  have hcross (n : ℕ) : φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi) ≤ p.angle (j n) :=
    firstCrossing_spec p.angle ha _
  have hbefore (n k : ℕ) (hk : k < j n) :
      p.angle k < φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi) :=
    firstCrossing_before p.angle ha _ hk
  have hangleLimit : Tendsto
      (fun n ↦ φ + (p.angle (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi))))
      atTop (𝓝 φ) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  have hnormalize (n : ℕ) : polarUnit (p.angle (j n)) =
      polarUnit (φ + (p.angle (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))) := by
    have hangle : p.angle (j n) =
        (φ + (p.angle (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))) +
          ((N + n : ℕ) : ℝ) * (2 * Real.pi) := by
      ring
    calc
      polarUnit (p.angle (j n)) = polarUnit
          ((φ + (p.angle (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))) +
            ((N + n : ℕ) : ℝ) * (2 * Real.pi)) := congrArg polarUnit hangle
      _ = polarUnit (φ + (p.angle (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))) :=
        polarUnit_add_natPeriod _ (N + n)
  have hpolar : Tendsto (fun n ↦ polarUnit (p.angle (j n))) atTop (𝓝 (polarUnit φ)) := by
    simpa only [Function.comp_def, hnormalize] using
      (continuous_polarUnit.tendsto φ).comp hangleLimit
  exact ⟨N, j, hstrict, hstrict.tendsto_atTop, hlevel, hcross, hbefore, herror, hpolar⟩

/-- Helper for lem:polar-geometry and eq:polar-chord: the squared chord norm
in polar coordinates separates into the two explicit real coordinate squares. -/
theorem polar_chord_coordinates (r s θ φ : ℝ) :
    ‖r • polarUnit θ - s • polarUnit φ‖ ^ 2 =
      (r * Real.cos θ - s * Real.cos φ) ^ 2 +
        (r * Real.sin θ - s * Real.sin φ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    polarUnit_apply_zero, polarUnit_apply_one]

/-- eq:polar-chord. The source chord identity holds for arbitrary real
radii and unreduced real angles; no radial orbit estimates are assumed. -/
theorem polar_chord_sq (r s θ φ : ℝ) :
    ‖r • polarUnit θ - s • polarUnit φ‖ ^ 2 =
      (r - s) ^ 2 + 4 * r * s * Real.sin ((θ - φ) / 2) ^ 2 := by
  have hhalf := Real.sin_sq_eq_half_sub ((θ - φ) / 2)
  have hdouble : 2 * ((θ - φ) / 2) = θ - φ := by
    ring
  rw [hdouble, Real.cos_sub] at hhalf
  rw [polar_chord_coordinates]
  have hθ := congrArg (fun z : ℝ ↦ r ^ 2 * z) (Real.sin_sq_add_cos_sq θ)
  have hφ := congrArg (fun z : ℝ ↦ s ^ 2 * z) (Real.sin_sq_add_cos_sq φ)
  have hhalfScaled := congrArg (fun z : ℝ ↦ 4 * r * s * z) hhalf
  nlinarith

/-- Helper for lem:polar-geometry and eq:polar-angles: an inverse squared
scale is at most its positive integer scale index. -/
theorem scale_inv_sq_le_index (p : Parameters) (hstart : 0 < p.startIndex) (j : ℕ) :
    p.scale j ^ (-2 : ℤ) ≤ ((p.startIndex + j : ℕ) : ℝ) := by
  have hbase : (1 : ℝ) ≤ ((p.startIndex + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.add_pos_left hstart j)
  rw [Parameters.scale_def, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  have hexponent : (-(1 : ℝ) / 3) * ((-2 : ℤ) : ℝ) = (2 / 3 : ℝ) := by
    norm_num
  have horder : (2 / 3 : ℝ) ≤ 1 := by
    norm_num
  rw [hexponent]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase horder

/-- Helper for lem:polar-geometry and eq:polar-angles: scales whose integer
indices differ by a factor at most eight are comparable by a factor of two. -/
theorem scale_lower_of_index_le_eight (p : Parameters) (hstart : 0 < p.startIndex)
    (i j : ℕ) (hindices : p.startIndex + j ≤ 8 * (p.startIndex + i)) :
    (1 / 2) * p.scale i ≤ p.scale j := by
  have hpositive : (0 : ℝ) < ((p.startIndex + j : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.add_pos_left hstart j)
  have hreal : ((p.startIndex + j : ℕ) : ℝ) ≤ 8 * ((p.startIndex + i : ℕ) : ℝ) := by
    exact_mod_cast hindices
  have hnegative : (-(1 : ℝ) / 3) ≤ 0 := by
    norm_num
  have hbound := Real.rpow_le_rpow_of_nonpos hpositive hreal hnegative
  have hEight : (8 : ℝ) ^ (-(1 : ℝ) / 3) = 1 / 2 := by
    simpa only [Nat.reducePow, Nat.cast_ofNat, one_div] using ScaleTails.cubic_rpow_neg_third 2
  have hEightNonneg : (0 : ℝ) ≤ 8 := by
    norm_num
  rw [Real.mul_rpow hEightNonneg (Nat.cast_nonneg _), hEight] at hbound
  simpa only [Parameters.scale_def] using hbound

/-- Helper for lem:polar-geometry and eq:polar-angles: the source near-window
length with the fixed sufficiently small choice `η = 1/4`. -/
def nearWindow (p : Parameters) (k : ℕ) : ℕ :=
  ⌊(1 / 4 : ℝ) * p.scale (k / 2) ^ (-2 : ℤ)⌋₊

/-- Helper for lem:polar-geometry and eq:polar-angles: the exact floor formula
for the selected angular near-window. -/
theorem nearWindow_def (p : Parameters) (k : ℕ) :
    nearWindow p k = ⌊(1 / 4 : ℝ) * p.scale (k / 2) ^ (-2 : ℤ)⌋₊ := by
  rfl

/-- Helper for lem:polar-geometry and eq:polar-angles: the selected near-window
length is at most the initial integer scale index. -/
theorem nearWindow_le_index (p : Parameters) (hstart : 0 < p.startIndex) (k : ℕ) :
    nearWindow p k ≤ p.startIndex + k / 2 := by
  rw [nearWindow_def]
  apply Nat.floor_le_of_le
  have hbound := scale_inv_sq_le_index p hstart (k / 2)
  have hnonneg : 0 ≤ p.scale (k / 2) ^ (-2 : ℤ) :=
    zpow_nonneg (ScaleTails.scale_nonneg p _) _
  linarith

/-- Helper for lem:polar-geometry and eq:polar-angles: multiplying the
near-window length by the squared initial scale gives at most `η = 1/4`. -/
theorem nearWindow_mul_scale_sq_le (p : Parameters) (hstart : 0 < p.startIndex) (k : ℕ) :
    (nearWindow p k : ℝ) * p.scale (k / 2) ^ 2 ≤ (1 / 4 : ℝ) := by
  have ht := ScaleTails.scale_pos p hstart (k / 2)
  have hnonneg : 0 ≤ (1 / 4 : ℝ) * p.scale (k / 2) ^ (-2 : ℤ) := by
    positivity
  have hfloor := Nat.floor_le hnonneg
  have hbound := mul_le_mul_of_nonneg_right hfloor (sq_nonneg (p.scale (k / 2)))
  have hcancel : ((1 / 4 : ℝ) * p.scale (k / 2) ^ (-2 : ℤ)) *
      p.scale (k / 2) ^ 2 = 1 / 4 := by
    field_simp [ht.ne']
  rw [hcancel] at hbound
  exact hbound

/-- Helper for lem:polar-geometry and eq:polar-angles: throughout the source
near-window the actual squared scales are between one quarter and one times
the initial squared scale. -/
theorem scale_sq_nearWindow_bounds (p : Parameters) (hstart : 0 < p.startIndex)
    (k m l : ℕ) (hkm : k ≤ m) (hwindow : m - k ≤ nearWindow p k)
    (hkl : k ≤ l) (hlm : l ≤ m) :
    (1 / 4) * p.scale (k / 2) ^ 2 ≤ p.scale (l / 2) ^ 2 ∧
      p.scale (l / 2) ^ 2 ≤ p.scale (k / 2) ^ 2 := by
  have hlength := hwindow.trans (nearWindow_le_index p hstart k)
  have hindices : p.startIndex + l / 2 ≤ 8 * (p.startIndex + k / 2) := by
    omega
  have hlower := scale_lower_of_index_le_eight p hstart (k / 2) (l / 2) hindices
  have hcycle : k / 2 ≤ l / 2 := Nat.div_le_div_right hkl
  have hupper := ScaleTails.scale_antitone p hstart hcycle
  have hhalf : 0 ≤ (1 / 2 : ℝ) * p.scale (k / 2) := by
    have hhalfNonneg : (0 : ℝ) ≤ 1 / 2 := by
      norm_num
    exact mul_nonneg hhalfNonneg (ScaleTails.scale_nonneg p _)
  have hlowerSq := pow_le_pow_left₀ hhalf hlower 2
  have hupperSq := pow_le_pow_left₀ (ScaleTails.scale_nonneg p _) hupper 2
  constructor
  · nlinarith
  · exact hupperSq

/-- Helper for lem:polar-geometry and eq:polar-angles: actual angular
increments telescope on every finite point-index interval. -/
theorem sum_angleIncrement_Ico (p : Parameters) (k m : ℕ) (hkm : k ≤ m) :
    (∑ i ∈ Finset.Ico k m, p.angleIncrement i) = p.angle m - p.angle k := by
  simp_rw [Parameters.angleIncrement_def]
  exact Finset.sum_Ico_sub p.angle hkm

/-- Helper for lem:polar-geometry and eq:polar-angles: the source near-window
has two-sided angular separation proportional to `(m-k)t²`, with uniform
constants and angular span at most π. The fixed cutoff is `η = 1/4`. -/
theorem nearWindow_angle_bounds (p : Parameters) (hstart : 0 < p.startIndex)
    (k m : ℕ) (hkm : k < m) (hwindow : m - k ≤ nearWindow p k) :
    (3 * baseAngle / 28) * (m - k : ℕ) * p.scale (k / 2) ^ 2 ≤ p.angle m - p.angle k ∧
      p.angle m - p.angle k ≤ (2 * baseAngle) * (m - k : ℕ) * p.scale (k / 2) ^ 2 ∧
      (2 * baseAngle) * (m - k : ℕ) * p.scale (k / 2) ^ 2 ≤ Real.pi := by
  have ha := baseAngle_pos
  have hlocal (i : ℕ) (hi : i ∈ Finset.Ico k m) :
      (3 * baseAngle / 28) * p.scale (k / 2) ^ 2 ≤ p.angleIncrement i ∧
        p.angleIncrement i ≤ (2 * baseAngle) * p.scale (k / 2) ^ 2 := by
    have hiBounds := Finset.mem_Ico.mp hi
    have hscales := scale_sq_nearWindow_bounds p hstart k m i hkm.le hwindow
      hiBounds.1 hiBounds.2.le
    have hincrement := angleIncrement_bounds p hstart i
    have hcoefficientLower : 0 ≤ 3 * baseAngle / 7 := by
      positivity
    have hcoefficientUpper : 0 ≤ 2 * baseAngle := by
      positivity
    have hlower := mul_le_mul_of_nonneg_left hscales.1 hcoefficientLower
    have hupper := mul_le_mul_of_nonneg_left hscales.2 hcoefficientUpper
    constructor
    · nlinarith [hincrement.1]
    · exact hincrement.2.trans hupper
  have hsumLower := Finset.sum_le_sum (fun i hi ↦ (hlocal i hi).1)
  have hsumUpper := Finset.sum_le_sum (fun i hi ↦ (hlocal i hi).2)
  rw [sum_angleIncrement_Ico p k m hkm.le] at hsumLower hsumUpper
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico] at hsumLower hsumUpper
  have hcount : ((m - k : ℕ) : ℝ) * p.scale (k / 2) ^ 2 ≤ 1 / 4 := by
    have hcast : ((m - k : ℕ) : ℝ) ≤ nearWindow p k := Nat.cast_le.mpr hwindow
    exact (mul_le_mul_of_nonneg_right hcast (sq_nonneg _)).trans
      (nearWindow_mul_scale_sq_le p hstart k)
  have hspan : (2 * baseAngle) * (m - k : ℕ) * p.scale (k / 2) ^ 2 ≤ Real.pi := by
    have hcoefficient : 0 ≤ 2 * baseAngle := by
      positivity
    have hbound := mul_le_mul_of_nonneg_left hcount hcoefficient
    rw [baseAngle_def] at hbound ⊢
    nlinarith [Real.pi_pos]
  refine ⟨?_, ?_, hspan⟩
  · nlinarith [hsumLower]
  · nlinarith [hsumUpper]

end DFP.Polar.AngularGeometry

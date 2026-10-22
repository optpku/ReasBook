/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_34
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_9

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {Ω : Type u} [MeasurableSpace Ω]

/- Layering for Theorem 19.33:
- `source-facing`: the one-dimensional random environment `W` on `ℤ`, its local ratios
  `ρ(x) = (1 - W.rightJumpProb x) / W.rightJumpProb x`, the textbook series `R_w^-`, `R_w^+`, and
  the drift-to-`±∞` / oscillation conclusions.
- `core/canonical`: the Chapter 19 conductance owner `effectiveResistanceToInfinity`.
- `bridge/view`: a reversible nearest-neighbor conductance family derived from the ratio products,
  used only to connect the RWRE series to the Chapter 19 electrical-network API. -/

/-- The local Solomon ratio `ρ(x) = q(x) / p(x)` of the environment `W`, where
`p(x) = W.rightJumpProb x` and `q(x) = 1 - p(x)`. -/
def randomEnvironmentRatio (W : RandomEnvironment) (x : ℤ) : ℝ≥0∞ :=
  ((1 : ℝ≥0∞) - W.rightJumpProb x) / W.rightJumpProb x

scoped[ProbabilityTheory] notation "ρ[" W "](" x ")" => randomEnvironmentRatio W x

/-- The `n`-th rightward multiplicative term in Solomon's series `R_w^+`, namely
`∏_{k=0}^n ρ(k)`. -/
def randomEnvironmentRightSeriesTerm (W : RandomEnvironment) (n : ℕ) : ℝ≥0∞ :=
  Finset.prod (Finset.range (n + 1)) fun k ↦ ρ[W](k)

/-- The `n`-th leftward multiplicative term in Solomon's series `R_w^-`, namely
`∏_{k=-n}^{-1} ρ(k)⁻¹`, with the convention that the empty product for `n = 0` is `1`. -/
def randomEnvironmentLeftSeriesTerm (W : RandomEnvironment) (n : ℕ) : ℝ≥0∞ :=
  Finset.prod (Finset.range n) fun k ↦ (ρ[W](-((k : ℤ) + 1)))⁻¹

/-- The textbook right-hand Solomon series `R_w^+ = ∑_{n ≥ 0} ∏_{k=0}^n ρ(k)`. -/
def randomEnvironmentRightSeries (W : RandomEnvironment) : ℝ≥0∞ :=
  ∑' n : ℕ, randomEnvironmentRightSeriesTerm W n

scoped[ProbabilityTheory] notation "R⁺[" W "]" => randomEnvironmentRightSeries W

/-- The textbook left-hand Solomon series
`R_w^- = ∑_{n ≥ 0} ∏_{k=-n}^{-1} ρ(k)⁻¹`, where the `n = 0` term is the empty product `1`. -/
def randomEnvironmentLeftSeries (W : RandomEnvironment) : ℝ≥0∞ :=
  ∑' n : ℕ, randomEnvironmentLeftSeriesTerm W n

scoped[ProbabilityTheory] notation "R⁻[" W "]" => randomEnvironmentLeftSeries W

/-- Expanding `R_w^+` gives the textbook series `∑_{n ≥ 0} ∏_{k=0}^n ρ(k)`. -/
@[simp]
theorem randomEnvironmentRightSeries_def (W : RandomEnvironment) :
    R⁺[W] = ∑' n : ℕ, randomEnvironmentRightSeriesTerm W n := rfl

/-- Expanding `R_w^-` gives the textbook series
`∑_{n ≥ 0} ∏_{k=-n}^{-1} ρ(k)⁻¹`, with empty `n = 0` term equal to `1`. -/
@[simp]
theorem randomEnvironmentLeftSeries_def (W : RandomEnvironment) :
    R⁻[W] = ∑' n : ℕ, randomEnvironmentLeftSeriesTerm W n := rfl

/-- Solomon's directional series ratio `toward / (away + toward)`, interpreted with the textbook
convention `∞ / ∞ = 1` in the asymmetric transience regime where `toward = ∞` and `away < ∞`. -/
def solomonDirectionalSeriesRatio (toward away : ℝ≥0∞) : ℝ≥0∞ :=
  if toward = ∞ then 1 else toward / (away + toward)

/-- When the series in the chosen direction is finite, Solomon's directional ratio is the usual
`ℝ≥0∞` quotient. -/
theorem solomonDirectionalSeriesRatio_eq_div {toward away : ℝ≥0∞} (htoward : toward < ∞) :
    solomonDirectionalSeriesRatio toward away = toward / (away + toward) := by
  simp [solomonDirectionalSeriesRatio, htoward.ne]

/-- When the series in the chosen direction is infinite, Solomon's source convention makes the
directional ratio equal to `1`. -/
@[simp]
theorem solomonDirectionalSeriesRatio_eq_one {toward away : ℝ≥0∞} (htoward : toward = ∞) :
    solomonDirectionalSeriesRatio toward away = 1 := by
  simp [solomonDirectionalSeriesRatio, htoward]

/-- Helper for Theorem 19.33: the finite left Solomon prefix sum up to `N` packages the repeated
`Finset.range (N + 1)` surface into one stable owner. -/
private def randomEnvironmentLeftPrefixSum (W : RandomEnvironment) (N : ℕ) : ℝ≥0∞ :=
  Finset.sum (Finset.range (N + 1)) (fun i ↦ randomEnvironmentLeftSeriesTerm W i)

/-- Helper for Theorem 19.33: the finite right Solomon prefix sum up to `N` packages the repeated
`Finset.range (N + 1)` surface into one stable owner. -/
private def randomEnvironmentRightPrefixSum (W : RandomEnvironment) (N : ℕ) : ℝ≥0∞ :=
  Finset.sum (Finset.range (N + 1)) (fun i ↦ randomEnvironmentRightSeriesTerm W i)

/-- Helper for Theorem 19.33: the finite symmetric-corridor left-exit ratio uses the right prefix
sum over the total prefix resistance. -/
private def randomEnvironmentLeftExitPrefixRatio (W : RandomEnvironment) (N : ℕ) : ℝ :=
  (randomEnvironmentRightPrefixSum W N).toReal /
    ((randomEnvironmentLeftPrefixSum W N).toReal + (randomEnvironmentRightPrefixSum W N).toReal)

/-- Helper for Theorem 19.33: the finite symmetric-corridor right-exit ratio uses the left prefix
sum over the total prefix resistance. -/
private def randomEnvironmentRightExitPrefixRatio (W : RandomEnvironment) (N : ℕ) : ℝ :=
  (randomEnvironmentLeftPrefixSum W N).toReal /
    ((randomEnvironmentLeftPrefixSum W N).toReal + (randomEnvironmentRightPrefixSum W N).toReal)

/-- The reversible edge conductance attached to the edge `{x, x + 1}` of the environment `W`.
For `x ≥ 0` it is the reciprocal of the prefix product `∏_{k=0}^x ρ(k)`, while for `x < 0` it is
the reciprocal of `∏_{k=x+1}^{-1} ρ(k)⁻¹`. This is a bridge object, not the main RWRE owner. -/
def randomEnvironmentEdgeConductance (W : RandomEnvironment) (x : ℤ) : ℝ≥0∞ :=
  if 0 ≤ x then
    (randomEnvironmentRightSeriesTerm W x.toNat)⁻¹
  else
    (randomEnvironmentLeftSeriesTerm W (Int.natAbs (x + 1)))⁻¹

/-- The nearest-neighbor conductance family on `ℤ` derived from the environment `W`: the edge
`{x, x + 1}` carries the conductance `randomEnvironmentEdgeConductance W x`. This is the
conductance-network bridge used to access the Chapter 19 owner API. -/
def randomEnvironmentConductance (W : RandomEnvironment) : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦
    if y = x + 1 then
      randomEnvironmentEdgeConductance W x
    else if y = x - 1 then
      randomEnvironmentEdgeConductance W (x - 1)
    else
      0

/-- Evaluating the environment-derived conductance family gives the two adjacent edge weights. -/
@[simp]
theorem randomEnvironmentConductance_apply (W : RandomEnvironment) (x y : ℤ) :
    randomEnvironmentConductance W x y =
      if y = x + 1 then
        randomEnvironmentEdgeConductance W x
      else if y = x - 1 then
        randomEnvironmentEdgeConductance W (x - 1)
      else
        0 := rfl

-- Route correction: this file now reuses the canonical Chapter 19
-- `effectiveResistanceToInfinity` owner from `Items.Chap19.Theorem_19_25`. The only local bridge
-- API that remains necessary is the normalized conductance-kernel adapter.

/-- Helper for Theorem 19.33: the normalized transition matrix attached to a conductance family is
`C(x,y) / conductance C x`. This local adapter replaces the broken owner import surface without
changing the proof route. -/
def conductanceTransitionMatrix {E : Type*} (C : E → E → ℝ≥0∞) (x y : E) : ℝ≥0∞ :=
  C x y / conductance C x

/-- Helper for Theorem 19.33: evaluating the localized conductance transition matrix just unfolds
its defining quotient. -/
@[simp]
theorem conductanceTransitionMatrix_apply {E : Type*}
    (C : E → E → ℝ≥0∞) (x y : E) :
    conductanceTransitionMatrix C x y = C x y / conductance C x := rfl

section Bridge

variable {W : RandomEnvironment}

/-- Helper for Theorem 19.33: the rightward Solomon product gains the new factor `ρ[W](n + 1)`
when the truncation is extended by one step. -/
theorem randomEnvironmentRightSeriesTerm_succ (W : RandomEnvironment) (n : ℕ) :
    randomEnvironmentRightSeriesTerm W (n + 1) =
      randomEnvironmentRightSeriesTerm W n * ρ[W](n + 1) := by
  -- Peel off the last factor in the finite product.
  simpa [randomEnvironmentRightSeriesTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Finset.prod_range_succ (fun k : ℕ ↦ ρ[W](k)) (n + 1))

/-- Helper for Theorem 19.33: the leftward Solomon product gains the new inverse factor
`(ρ[W](-((n : ℤ) + 1)))⁻¹` when the truncation is extended by one step. -/
theorem randomEnvironmentLeftSeriesTerm_succ (W : RandomEnvironment) (n : ℕ) :
    randomEnvironmentLeftSeriesTerm W (n + 1) =
      randomEnvironmentLeftSeriesTerm W n * (ρ[W](-((n : ℤ) + 1)))⁻¹ := by
  -- Peel off the newest negative-index factor in the finite product.
  simpa [randomEnvironmentLeftSeriesTerm] using
    (Finset.prod_range_succ (fun k : ℕ ↦ (ρ[W](-((k : ℤ) + 1)))⁻¹) n)

/-- Helper for Theorem 19.33: ellipticity makes every local Solomon ratio strictly positive. -/
theorem randomEnvironmentRatio_pos (hW : W.IsElliptic) (x : ℤ) :
    0 < ρ[W](x) := by
  -- Both the numerator and denominator in `ρ(x) = q(x) / p(x)` are strictly positive.
  have hnum : 0 < ((1 : ℝ≥0∞) - W.rightJumpProb x) := by
    exact_mod_cast (tsub_pos_iff_lt.2 (hW.lt_one x))
  exact (ENNReal.div_pos_iff).2 ⟨hnum.ne', by simp⟩

/-- Helper for Theorem 19.33: ellipticity keeps each local Solomon ratio finite. -/
theorem randomEnvironmentRatio_ne_top (hW : W.IsElliptic) (x : ℤ) :
    ρ[W](x) ≠ ∞ := by
  -- The numerator is finite and the denominator is strictly positive.
  have hnum : ((1 : ℝ≥0∞) - W.rightJumpProb x) ≠ ∞ := by
    exact ENNReal.sub_ne_top (by simp)
  exact ENNReal.div_ne_top hnum (by exact_mod_cast (hW.pos x).ne')

/-- Helper for Theorem 19.33: on the negative ray, the bridge edge conductance is exactly the
inverse of the corresponding leftward Solomon product. -/
@[simp]
theorem randomEnvironmentEdgeConductance_negSucc (W : RandomEnvironment) (n : ℕ) :
    randomEnvironmentEdgeConductance W (Int.negSucc n) =
      (randomEnvironmentLeftSeriesTerm W n)⁻¹ := by
  -- Proof comment: `Int.negSucc n + 1 = -n`, so the negative-ray branch of the definition uses
  -- precisely the left-series truncation indexed by `n`.
  have hnatAbs : Int.natAbs (Int.negSucc n + 1) = n := by
    have hneg : (Int.negSucc n : ℤ) + 1 = -((n : ℤ)) := by simp
    rw [hneg]
    simp
  rw [randomEnvironmentEdgeConductance, if_neg (by simp)]
  rw [hnatAbs]

/-- Helper for Theorem 19.33: every rightward Solomon prefix product is strictly positive in an
elliptic environment. -/
theorem randomEnvironmentRightSeriesTerm_pos (hW : W.IsElliptic) (n : ℕ) :
    0 < randomEnvironmentRightSeriesTerm W n := by
  induction n with
  | zero =>
      -- Proof comment: the zeroth prefix product is just the positive ratio `ρ[W](0)`.
      simpa [randomEnvironmentRightSeriesTerm] using randomEnvironmentRatio_pos hW (0 : ℤ)
  | succ n ih =>
      -- Proof comment: extend the prefix product by one new positive factor.
      rw [randomEnvironmentRightSeriesTerm_succ]
      exact ENNReal.mul_pos (ne_of_gt ih) (ne_of_gt (randomEnvironmentRatio_pos hW (n + 1)))

/-- Helper for Theorem 19.33: every rightward Solomon prefix product is finite in an elliptic
environment. -/
theorem randomEnvironmentRightSeriesTerm_ne_top (hW : W.IsElliptic) (n : ℕ) :
    randomEnvironmentRightSeriesTerm W n ≠ ∞ := by
  induction n with
  | zero =>
      -- Proof comment: the zeroth prefix product is the finite ratio `ρ[W](0)`.
      simpa [randomEnvironmentRightSeriesTerm] using randomEnvironmentRatio_ne_top hW (0 : ℤ)
  | succ n ih =>
      -- Proof comment: multiplying two finite ENNReal factors stays finite.
      rw [randomEnvironmentRightSeriesTerm_succ]
      exact ENNReal.mul_ne_top ih (randomEnvironmentRatio_ne_top hW (n + 1))

/-- Helper for Theorem 19.33: every leftward Solomon prefix product is strictly positive in an
elliptic environment. -/
theorem randomEnvironmentLeftSeriesTerm_pos (hW : W.IsElliptic) (n : ℕ) :
    0 < randomEnvironmentLeftSeriesTerm W n := by
  induction n with
  | zero =>
      -- Proof comment: the empty leftward product is `1`.
      simp [randomEnvironmentLeftSeriesTerm]
  | succ n ih =>
      -- Proof comment: extend the prefix by one inverse ratio, which is positive because the
      -- ratio is finite.
      rw [randomEnvironmentLeftSeriesTerm_succ]
      exact ENNReal.mul_pos (ne_of_gt ih)
        (ne_of_gt ((ENNReal.inv_pos).2 (randomEnvironmentRatio_ne_top hW (-((n : ℤ) + 1)))))

/-- Helper for Theorem 19.33: every leftward Solomon prefix product is finite in an elliptic
environment. -/
theorem randomEnvironmentLeftSeriesTerm_ne_top (hW : W.IsElliptic) (n : ℕ) :
    randomEnvironmentLeftSeriesTerm W n ≠ ∞ := by
  induction n with
  | zero =>
      -- Proof comment: the empty leftward product is finite.
      simp [randomEnvironmentLeftSeriesTerm]
  | succ n ih =>
      -- Proof comment: the extra inverse ratio is finite because the ratio is nonzero.
      rw [randomEnvironmentLeftSeriesTerm_succ]
      exact ENNReal.mul_ne_top ih
        ((ENNReal.inv_ne_top).2 (ne_of_gt (randomEnvironmentRatio_pos hW (-((n : ℤ) + 1)))))

/-- Helper for Theorem 19.33: ellipticity makes every bridge edge conductance strictly positive. -/
theorem randomEnvironmentEdgeConductance_pos (hW : W.IsElliptic) (x : ℤ) :
    0 < randomEnvironmentEdgeConductance W x := by
  by_cases hx : 0 ≤ x
  · -- Proof comment: on the nonnegative ray, the conductance is the inverse of a finite
    -- right-series prefix product.
    rw [randomEnvironmentEdgeConductance, if_pos hx]
    exact (ENNReal.inv_pos).2 (randomEnvironmentRightSeriesTerm_ne_top hW x.toNat)
  · -- Proof comment: on the negative ray, first rewrite `x` as `Int.negSucc n` and then use the
    -- finite left-series normal form.
    have hx' : x < 0 := lt_of_not_ge hx
    rcases Int.eq_negSucc_of_lt_zero hx' with ⟨n, rfl⟩
    rw [randomEnvironmentEdgeConductance_negSucc]
    exact (ENNReal.inv_pos).2 (randomEnvironmentLeftSeriesTerm_ne_top hW n)

/-- Helper for Theorem 19.33: ellipticity keeps every bridge edge conductance finite. -/
theorem randomEnvironmentEdgeConductance_ne_top (hW : W.IsElliptic) (x : ℤ) :
    randomEnvironmentEdgeConductance W x ≠ ∞ := by
  by_cases hx : 0 ≤ x
  · -- Proof comment: on the nonnegative ray, finiteness of the inverse is equivalent to
    -- nonvanishing of the underlying right-series prefix product.
    rw [randomEnvironmentEdgeConductance, if_pos hx]
    exact (ENNReal.inv_ne_top).2 (ne_of_gt (randomEnvironmentRightSeriesTerm_pos hW x.toNat))
  · -- Proof comment: on the negative ray, the same argument uses the left-series normal form.
    have hx' : x < 0 := lt_of_not_ge hx
    rcases Int.eq_negSucc_of_lt_zero hx' with ⟨n, rfl⟩
    rw [randomEnvironmentEdgeConductance_negSucc]
    exact (ENNReal.inv_ne_top).2 (ne_of_gt (randomEnvironmentLeftSeriesTerm_pos hW n))

/-- Helper for Theorem 19.33: the bridge row weight at `x` is the sum of the two adjacent edge
conductances. -/
theorem randomEnvironmentConductance_vertexWeight (W : RandomEnvironment) (x : ℤ) :
    conductance (randomEnvironmentConductance W) x =
      randomEnvironmentEdgeConductance W (x - 1) + randomEnvironmentEdgeConductance W x := by
  classical
  -- The row of `x` is supported exactly on the two neighbors `x ± 1`.
  have hsupport :
      ∀ y ∉ ({x + 1, x - 1} : Finset ℤ), randomEnvironmentConductance W x y = 0 := by
    intro y hy
    have hy_right : y ≠ x + 1 := by
      intro hy'
      exact hy (by simp [hy'])
    have hy_left : y ≠ x - 1 := by
      intro hy'
      exact hy (by simp [hy'])
    simp [randomEnvironmentConductance, hy_right, hy_left]
  rw [conductance, tsum_eq_sum hsupport]
  have hneq : x + 1 ≠ x - 1 := by
    omega
  have hneq' : x - 1 ≠ x + 1 := by
    omega
  simp [randomEnvironmentConductance, hneq, hneq', add_comm]

/-- Helper for Theorem 19.33: neighboring bridge edge conductances differ by the local Solomon
ratio `ρ[W](x)`. -/
theorem randomEnvironmentEdgeConductance_ratio
    (hW : W.IsElliptic) (x : ℤ) :
    randomEnvironmentEdgeConductance W (x - 1) =
      ρ[W](x) * randomEnvironmentEdgeConductance W x := by
  by_cases hx0 : x = 0
  · -- Proof comment: at the origin, the left edge has conductance `1`, while the right edge is
    -- `ρ[W](0)⁻¹`, so the ratio identity is exactly `ρ * ρ⁻¹ = 1`.
    subst hx0
    have hratio_ne_zero : ρ[W]((0 : ℤ)) ≠ 0 := ne_of_gt (randomEnvironmentRatio_pos hW 0)
    have hratio_ne_top : ρ[W]((0 : ℤ)) ≠ ∞ := randomEnvironmentRatio_ne_top hW 0
    rw [show (0 : ℤ) - 1 = Int.negSucc 0 by decide, randomEnvironmentEdgeConductance_negSucc,
      randomEnvironmentEdgeConductance, if_pos le_rfl]
    simpa [randomEnvironmentLeftSeriesTerm, randomEnvironmentRightSeriesTerm] using
      (ENNReal.mul_inv_cancel hratio_ne_zero hratio_ne_top).symm
  · by_cases hxpos : 0 < x
    · -- Proof comment: on the positive ray, rewrite `x = n + 1`, expand the successor product,
      -- and cancel the new ratio factor.
      obtain ⟨n, rfl⟩ := Int.eq_succ_of_zero_lt hxpos
      have hterm_ne_zero : randomEnvironmentRightSeriesTerm W n ≠ 0 :=
        ne_of_gt (randomEnvironmentRightSeriesTerm_pos hW n)
      have hterm_ne_top : randomEnvironmentRightSeriesTerm W n ≠ ∞ :=
        randomEnvironmentRightSeriesTerm_ne_top hW n
      have hratio_ne_zero : ρ[W]((n : ℤ) + 1) ≠ 0 :=
        ne_of_gt (randomEnvironmentRatio_pos hW ((n : ℤ) + 1))
      have hratio_ne_top : ρ[W]((n : ℤ) + 1) ≠ ∞ :=
        randomEnvironmentRatio_ne_top hW ((n : ℤ) + 1)
      have hxminus : ((n : ℤ) + 1) - 1 = n := by omega
      rw [hxminus, randomEnvironmentEdgeConductance,
        if_pos (show 0 ≤ (n : ℤ) by exact_mod_cast Nat.zero_le n)]
      rw [randomEnvironmentEdgeConductance, if_pos (show 0 ≤ (n : ℤ) + 1 by positivity)]
      calc
        (randomEnvironmentRightSeriesTerm W n)⁻¹
            = (randomEnvironmentRightSeriesTerm W n)⁻¹ *
                (ρ[W]((n : ℤ) + 1) * ρ[W]((n : ℤ) + 1)⁻¹) := by
                  rw [ENNReal.mul_inv_cancel hratio_ne_zero hratio_ne_top, mul_one]
        _ = ρ[W]((n : ℤ) + 1) *
              ((randomEnvironmentRightSeriesTerm W n)⁻¹ * ρ[W]((n : ℤ) + 1)⁻¹) := by
                ac_rfl
        _ = ρ[W]((n : ℤ) + 1) *
              (randomEnvironmentRightSeriesTerm W (n + 1))⁻¹ := by
                rw [randomEnvironmentRightSeriesTerm_succ,
                  ENNReal.mul_inv (Or.inl hterm_ne_zero) (Or.inl hterm_ne_top)]
    · -- Proof comment: on the negative ray, rewrite `x = Int.negSucc n`, expand the left-series
      -- successor, and invert the added inverse-ratio factor.
      have hxneg : x < 0 := lt_of_not_ge (by omega)
      rcases Int.eq_negSucc_of_lt_zero hxneg with ⟨n, rfl⟩
      have hleft_ne_zero : randomEnvironmentLeftSeriesTerm W n ≠ 0 :=
        ne_of_gt (randomEnvironmentLeftSeriesTerm_pos hW n)
      have hleft_ne_top : randomEnvironmentLeftSeriesTerm W n ≠ ∞ :=
        randomEnvironmentLeftSeriesTerm_ne_top hW n
      rw [show (Int.negSucc n : ℤ) - 1 = Int.negSucc (n + 1) by rfl,
        randomEnvironmentEdgeConductance_negSucc, randomEnvironmentEdgeConductance_negSucc]
      calc
        (randomEnvironmentLeftSeriesTerm W (n + 1))⁻¹
            = ((randomEnvironmentLeftSeriesTerm W n) *
                (ρ[W](Int.negSucc n))⁻¹)⁻¹ := by
                  rw [randomEnvironmentLeftSeriesTerm_succ]
                  have hindex : (-((n : ℤ) + 1) : ℤ) = Int.negSucc n := by omega
                  rw [hindex]
        _ = (randomEnvironmentLeftSeriesTerm W n)⁻¹ *
              ((ρ[W](Int.negSucc n))⁻¹)⁻¹ := by
                rw [ENNReal.mul_inv (Or.inl hleft_ne_zero) (Or.inl hleft_ne_top)]
        _ = (randomEnvironmentLeftSeriesTerm W n)⁻¹ * ρ[W](Int.negSucc n) := by
              simp
        _ = ρ[W](Int.negSucc n) * (randomEnvironmentLeftSeriesTerm W n)⁻¹ := by
              ac_rfl

/-- Helper for Theorem 19.33: multiplying the local Solomon ratio by the right-jump probability
recovers the left-jump probability `1 - W.rightJumpProb x`. -/
theorem randomEnvironmentRatio_mul_rightJumpProb
    (hW : W.IsElliptic) (x : ℤ) :
    ρ[W](x) * W.rightJumpProb x = (1 : ℝ≥0∞) - W.rightJumpProb x := by
  -- Cancel the positive denominator in the definition of `ρ(x)`.
  rw [randomEnvironmentRatio]
  exact ENNReal.div_mul_cancel (by exact_mod_cast (hW.pos x).ne') (by simp)

-- Proof sketch: the ratio recursion defining `randomEnvironmentEdgeConductance` gives
-- `randomEnvironmentEdgeConductance W (x - 1) /
--   randomEnvironmentEdgeConductance W x = ρ[W](x)`. Rewriting this as
-- `q(x) / p(x)` shows that row-normalizing the bridge conductances reproduces the source-facing
-- owner matrix `randomEnvironmentTransitionMatrix W`.
/-- For an environment with positive left- and right-jump probabilities, the Chapter 19
conductance walk associated to `randomEnvironmentConductance W` has transition matrix equal to the
source-facing RWRE owner `randomEnvironmentTransitionMatrix W`. -/
theorem randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix
    (hW : W.IsElliptic)
    (x y : ℤ) :
    randomEnvironmentTransitionMatrix W x y =
      conductanceTransitionMatrix (randomEnvironmentConductance W) x y := by
  have hden_pos : 0 < conductance (randomEnvironmentConductance W) x := by
    -- Proof comment: the row weight contains the positive right edge conductance at `x`.
    rw [randomEnvironmentConductance_vertexWeight]
    exact lt_of_lt_of_le (randomEnvironmentEdgeConductance_pos hW x)
      (le_add_of_nonneg_left (zero_le _))
  have hden_ne_zero : conductance (randomEnvironmentConductance W) x ≠ 0 := ne_of_gt hden_pos
  have hden_ne_top : conductance (randomEnvironmentConductance W) x ≠ ∞ := by
    -- Proof comment: both adjacent bridge edge conductances are finite, so their sum is finite.
    rw [randomEnvironmentConductance_vertexWeight]
    exact (ENNReal.add_ne_top).2 ⟨randomEnvironmentEdgeConductance_ne_top hW (x - 1),
      randomEnvironmentEdgeConductance_ne_top hW x⟩
  by_cases hy_right : y = x + 1
  · subst hy_right
    have hprob : (W.rightJumpProb x : ℝ≥0∞) ≤ 1 := by
      exact_mod_cast W.rightJumpProb_le_one x
    have hsum : ((1 : ℝ≥0∞) - W.rightJumpProb x) + W.rightJumpProb x = 1 := by
      simpa [add_comm] using (add_tsub_cancel_of_le hprob : W.rightJumpProb x + ((1 : ℝ≥0∞) - W.rightJumpProb x) = 1)
    have hmul :
        conductance (randomEnvironmentConductance W) x * W.rightJumpProb x =
          randomEnvironmentEdgeConductance W x := by
      calc
        conductance (randomEnvironmentConductance W) x * W.rightJumpProb x
            = (randomEnvironmentEdgeConductance W (x - 1) +
                randomEnvironmentEdgeConductance W x) * W.rightJumpProb x := by
                  rw [randomEnvironmentConductance_vertexWeight]
        _ = randomEnvironmentEdgeConductance W (x - 1) * W.rightJumpProb x +
              randomEnvironmentEdgeConductance W x * W.rightJumpProb x := by
                rw [add_mul]
        _ = (ρ[W](x) * randomEnvironmentEdgeConductance W x) * W.rightJumpProb x +
              randomEnvironmentEdgeConductance W x * W.rightJumpProb x := by
                rw [randomEnvironmentEdgeConductance_ratio hW x]
        _ = (ρ[W](x) * W.rightJumpProb x) * randomEnvironmentEdgeConductance W x +
              W.rightJumpProb x * randomEnvironmentEdgeConductance W x := by
                ac_rfl
        _ = ((1 : ℝ≥0∞) - W.rightJumpProb x) * randomEnvironmentEdgeConductance W x +
              W.rightJumpProb x * randomEnvironmentEdgeConductance W x := by
                rw [randomEnvironmentRatio_mul_rightJumpProb hW x]
        _ = (((1 : ℝ≥0∞) - W.rightJumpProb x) + W.rightJumpProb x) *
              randomEnvironmentEdgeConductance W x := by
                rw [add_mul]
        _ = randomEnvironmentEdgeConductance W x := by
              rw [hsum, one_mul]
    rw [randomEnvironmentTransitionMatrix_right, conductanceTransitionMatrix_apply,
      randomEnvironmentConductance, if_pos rfl]
    have hdiv :
        randomEnvironmentEdgeConductance W x /
            conductance (randomEnvironmentConductance W) x =
          W.rightJumpProb x / 1 := by
      exact
        (ENNReal.div_eq_div_iff
          (by simp) (by simp) hden_ne_zero hden_ne_top).2
          (by simpa [one_mul] using hmul.symm)
    simpa using hdiv.symm
  · by_cases hy_left : y = x - 1
    · subst hy_left
      have hprob : (W.rightJumpProb x : ℝ≥0∞) ≤ 1 := by
        exact_mod_cast W.rightJumpProb_le_one x
      have hsum : ((1 : ℝ≥0∞) - W.rightJumpProb x) + W.rightJumpProb x = 1 := by
        simpa [add_comm] using (add_tsub_cancel_of_le hprob : W.rightJumpProb x + ((1 : ℝ≥0∞) - W.rightJumpProb x) = 1)
      have hmulRight :
          conductance (randomEnvironmentConductance W) x * W.rightJumpProb x =
            randomEnvironmentEdgeConductance W x := by
        calc
          conductance (randomEnvironmentConductance W) x * W.rightJumpProb x
              = (randomEnvironmentEdgeConductance W (x - 1) +
                  randomEnvironmentEdgeConductance W x) * W.rightJumpProb x := by
                    rw [randomEnvironmentConductance_vertexWeight]
          _ = randomEnvironmentEdgeConductance W (x - 1) * W.rightJumpProb x +
                randomEnvironmentEdgeConductance W x * W.rightJumpProb x := by
                  rw [add_mul]
          _ = (ρ[W](x) * randomEnvironmentEdgeConductance W x) * W.rightJumpProb x +
                randomEnvironmentEdgeConductance W x * W.rightJumpProb x := by
                  rw [randomEnvironmentEdgeConductance_ratio hW x]
          _ = (ρ[W](x) * W.rightJumpProb x) * randomEnvironmentEdgeConductance W x +
                W.rightJumpProb x * randomEnvironmentEdgeConductance W x := by
                  ac_rfl
          _ = ((1 : ℝ≥0∞) - W.rightJumpProb x) * randomEnvironmentEdgeConductance W x +
                W.rightJumpProb x * randomEnvironmentEdgeConductance W x := by
                  rw [randomEnvironmentRatio_mul_rightJumpProb hW x]
          _ = (((1 : ℝ≥0∞) - W.rightJumpProb x) + W.rightJumpProb x) *
                randomEnvironmentEdgeConductance W x := by
                  rw [add_mul]
          _ = randomEnvironmentEdgeConductance W x := by
                rw [hsum, one_mul]
      have hmul :
          conductance (randomEnvironmentConductance W) x *
              ((1 : ℝ≥0∞) - W.rightJumpProb x) =
            randomEnvironmentEdgeConductance W (x - 1) := by
        calc
          conductance (randomEnvironmentConductance W) x *
              ((1 : ℝ≥0∞) - W.rightJumpProb x)
              = conductance (randomEnvironmentConductance W) x *
                  (ρ[W](x) * W.rightJumpProb x) := by
                    rw [randomEnvironmentRatio_mul_rightJumpProb hW x]
          _ = ρ[W](x) * (conductance (randomEnvironmentConductance W) x * W.rightJumpProb x) := by
                ac_rfl
          _ = ρ[W](x) * randomEnvironmentEdgeConductance W x := by rw [hmulRight]
          _ = randomEnvironmentEdgeConductance W (x - 1) := by
                rw [randomEnvironmentEdgeConductance_ratio hW x]
      rw [randomEnvironmentTransitionMatrix_left, conductanceTransitionMatrix_apply,
        randomEnvironmentConductance, if_neg hy_right]
      have hdiv :
          randomEnvironmentEdgeConductance W (x - 1) /
              conductance (randomEnvironmentConductance W) x =
            ((1 : ℝ≥0∞) - W.rightJumpProb x) / 1 := by
        exact
          (ENNReal.div_eq_div_iff
            (by simp) (by simp) hden_ne_zero hden_ne_top).2
            (by simpa [one_mul] using hmul.symm)
      simpa using hdiv.symm
    · -- Proof comment: away from the two neighbors `x ± 1`, both kernels assign zero mass.
      simp [randomEnvironmentTransitionMatrix, conductanceTransitionMatrix_apply,
        randomEnvironmentConductance, hy_right, hy_left]

/-- Helper for Theorem 19.33: the bridge conductance family is symmetric because each unoriented
nearest-neighbor edge `{x, x + 1}` carries the same weight from both incident vertices. -/
theorem randomEnvironmentConductance_symmetric (W : RandomEnvironment) (x y : ℤ) :
    randomEnvironmentConductance W x y = randomEnvironmentConductance W y x := by
  by_cases hy_right : y = x + 1
  · -- Proof comment: if `y = x + 1`, the reverse edge is the left-neighbor branch at `y`.
    have hyx_right : x ≠ y + 1 := by
      omega
    have hyx_left : x = y - 1 := by
      omega
    rw [randomEnvironmentConductance, if_pos hy_right]
    rw [randomEnvironmentConductance, if_neg hyx_right, if_pos hyx_left]
    simpa [hy_right]
  · by_cases hy_left : y = x - 1
    · -- Proof comment: if `y = x - 1`, the reverse edge is the right-neighbor branch at `y`.
      have hyx_right : x = y + 1 := by
        omega
      rw [randomEnvironmentConductance, if_neg hy_right, if_pos hy_left]
      rw [randomEnvironmentConductance, if_pos hyx_right]
      simpa [hy_left]
    · -- Proof comment: away from nearest neighbors, both directed edge weights vanish.
      have hyx_right : x ≠ y + 1 := by
        intro hyx_right
        exact hy_left (by omega)
      have hyx_left : x ≠ y - 1 := by
        intro hyx_left
        exact hy_right (by omega)
      rw [randomEnvironmentConductance, if_neg hy_right, if_neg hy_left]
      rw [randomEnvironmentConductance, if_neg hyx_right, if_neg hyx_left]

/-- Helper for Theorem 19.33: every row weight of the bridge conductance network is positive in an
elliptic environment. -/
theorem randomEnvironmentConductance_vertexWeight_pos
    (hW : W.IsElliptic) (x : ℤ) :
    0 < conductance (randomEnvironmentConductance W) x := by
  -- Proof comment: the row weight is the sum of the two positive adjacent edge conductances.
  rw [randomEnvironmentConductance_vertexWeight]
  exact lt_of_lt_of_le (randomEnvironmentEdgeConductance_pos hW x)
    (le_add_of_nonneg_left (zero_le _))

/-- Helper for Theorem 19.33: every row weight of the bridge conductance network is finite in an
elliptic environment. -/
theorem randomEnvironmentConductance_vertexWeight_lt_top
    (hW : W.IsElliptic) (x : ℤ) :
    conductance (randomEnvironmentConductance W) x < ∞ := by
  -- Proof comment: each row is the sum of two finite adjacent edge conductances.
  rw [randomEnvironmentConductance_vertexWeight]
  rw [lt_top_iff_ne_top]
  exact (ENNReal.add_ne_top).2
    ⟨randomEnvironmentEdgeConductance_ne_top hW (x - 1),
      randomEnvironmentEdgeConductance_ne_top hW x⟩

/-- Helper for Theorem 19.33: after normalizing the symmetric bridge conductances rowwise, one
recovers a random walk with weights in the sense of Definition 19.11. -/
theorem randomEnvironmentConductance_isRandomWalkWithWeights
    (hW : W.IsElliptic) :
    IsRandomWalkWithWeights
      (conductanceTransitionMatrix (randomEnvironmentConductance W))
      (randomEnvironmentConductance W) where
  -- Proof comment: stochasticity comes from the already identified RWRE transition matrix, while
  -- symmetry and the normalization formula are built into the bridge conductance family.
  isStochastic := by
    have hEq :
        conductanceTransitionMatrix (randomEnvironmentConductance W) =
          randomEnvironmentTransitionMatrix W := by
      funext x y
      symm
      exact randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix hW x y
    simpa [hEq] using randomEnvironmentTransitionMatrix_isStochastic W
  symmetric := randomEnvironmentConductance_symmetric W
  transition_eq := conductanceTransitionMatrix_apply (randomEnvironmentConductance W)

/-- Helper for Theorem 19.33: composing a positive first-step singleton mass with a positive
`n`-step singleton mass yields a positive `(n + 1)`-step singleton mass. -/
private theorem rwreKernel_singleton_pos_succ {x y z : ℤ} {n : ℕ}
    (hxy : 0 <
      ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) x) ({y} : Set ℤ))
    (hyz : 0 <
      (discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) y ({z} : Set ℤ)) :
    0 <
      ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ (n + 1)) x) ({z} : Set ℤ) := by
  let κ := discreteMatrixKernel (randomEnvironmentTransitionMatrix W)
  have hmeas : Measurable fun w : ℤ ↦ κ w ({z} : Set ℤ) :=
    Kernel.measurable_coe κ (MeasurableSet.singleton z)
  have hySupport : y ∈ Function.support fun w : ℤ ↦ κ w ({z} : Set ℤ) := by
    change (κ y) ({z} : Set ℤ) ≠ 0
    exact ne_of_gt hyz
  have hsupportPos :
      0 < ((κ ^ n) x) (Function.support fun w : ℤ ↦ κ w ({z} : Set ℤ)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the composition integral is positive because the support of the `n`-step
  -- mass contains the intermediate state `y` with positive first-step mass.
  rw [Kernel.pow_succ_apply_eq_lintegral κ n x (measurableSet_singleton z)]
  rw [MeasureTheory.lintegral_pos_iff_support hmeas]
  exact hsupportPos

/-- Under the canonical RWRE realization owner from Definition 19.34, ellipticity lets one
transport the realization to the Chapter 19 conductance-walk bridge. -/
theorem isMarkovProcessRealization_randomEnvironmentConductance
    {P : ℤ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℤ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (hW : W.IsElliptic) :
    IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel (conductanceTransitionMatrix (randomEnvironmentConductance W)) ^ n)
      P X := by
  have htransition :
      randomEnvironmentTransitionMatrix W =
        conductanceTransitionMatrix (randomEnvironmentConductance W) := by
    funext x y
    exact randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix hW x y
  simpa [htransition] using
    (inferInstance :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X)

/-- Helper for Theorem 19.33: following `n` successive right jumps from `x` has strictly positive
`n`-step mass in an elliptic random environment. -/
theorem randomEnvironmentRightPathMass_pos
    (hW : W.IsElliptic) (x : ℤ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) x)
          ({x + n} : Set ℤ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity, so it charges the starting point
      -- with mass `1`.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℤ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) x)
              ({x + n} : Set ℤ) := ih x
      have hlast :
          0 < (discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) (x + n)
              ({x + (n + 1)} : Set ℤ) := by
            have hendpoint : x + ((n : ℤ) + 1) = (x + n) + 1 := by omega
            rw [rwreKernel_apply_singleton, hendpoint, randomEnvironmentTransitionMatrix_right]
            exact_mod_cast hW.pos (x + n)
      exact rwreKernel_singleton_pos_succ hrest hlast

/-- Helper for Theorem 19.33: following `n` successive left jumps from `x` has strictly positive
`n`-step mass in an elliptic random environment. -/
theorem randomEnvironmentLeftPathMass_pos
    (hW : W.IsElliptic) (x : ℤ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) x)
          ({x - n} : Set ℤ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel again charges the starting point with mass `1`.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℤ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) x)
              ({x - n} : Set ℤ) := ih x
      have hleftprob : 0 < ((1 : ℝ≥0) - W.rightJumpProb (x - n) : ℝ≥0) := by
        exact tsub_pos_iff_lt.2 (hW.lt_one (x - n))
      have hlast :
          0 < (discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) (x - n)
              ({x - (n + 1)} : Set ℤ) := by
            have hendpoint : x - ((n : ℤ) + 1) = (x - n) - 1 := by omega
            rw [rwreKernel_apply_singleton, hendpoint, randomEnvironmentTransitionMatrix_left]
            simpa [ENNReal.coe_sub] using hleftprob
      exact rwreKernel_singleton_pos_succ hrest hlast

/-- Helper for Theorem 19.33: the elliptic RWRE kernel on `ℤ` is irreducible because every
target can be reached by a monotone path of right or left jumps with strictly positive mass. -/
theorem randomEnvironmentKernel_isIrreducible
    (hW : W.IsElliptic) :
    Kernel.IsIrreducible (Measure.count : Measure ℤ)
      (discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) := by
  refine ⟨?_⟩
  intro A hA hcount x
  have hA_nonempty : A.Nonempty := by
    by_contra hA_empty
    simp [Set.not_nonempty_iff_eq_empty.mp hA_empty] at hcount
  rcases hA_nonempty with ⟨y, hyA⟩
  by_cases hxy : x ≤ y
  · let n : ℕ := Int.toNat (y - x)
    have hn : (n : ℤ) = y - x := by
      dsimp [n]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hxy)
    have hy : y = x + n := by
      omega
    refine ⟨n, ?_⟩
    have hsingleton :
        0 <
          ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) x)
            ({y} : Set ℤ) := by
      simpa [hy] using randomEnvironmentRightPathMass_pos hW x n
    exact lt_of_lt_of_le hsingleton (measure_mono (Set.singleton_subset_iff.mpr hyA))
  · let n : ℕ := Int.toNat (x - y)
    have hn : (n : ℤ) = x - y := by
      dsimp [n]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hxy)))
    have hy : y = x - n := by
      omega
    refine ⟨n, ?_⟩
    have hsingleton :
        0 <
          ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) x)
            ({y} : Set ℤ) := by
      simpa [hy] using randomEnvironmentLeftPathMass_pos hW x n
    exact lt_of_lt_of_le hsingleton (measure_mono (Set.singleton_subset_iff.mpr hyA))

/-- Helper for Theorem 19.33: the environment-derived conductance walk on `ℤ` is irreducible,
because its transition matrix agrees with the elliptic RWRE kernel. -/
theorem randomEnvironmentConductance_irreducible
    (hW : W.IsElliptic) :
    Kernel.IsIrreducible (Measure.count : Measure ℤ)
      (discreteMatrixKernel
        (conductanceTransitionMatrix (randomEnvironmentConductance W))) := by
  -- Proof comment: transport the monotone-path irreducibility of the RWRE kernel through the
  -- already proved equality of the two transition matrices.
  have htransition :
      randomEnvironmentTransitionMatrix W =
        conductanceTransitionMatrix (randomEnvironmentConductance W) := by
    funext x y
    exact randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix hW x y
  simpa [htransition] using randomEnvironmentKernel_isIrreducible hW

/-- Helper for Theorem 19.33: ellipticity gives a strictly positive Chapter 17 ever-hit
probability from `0` to every integer, because each target is reached by an explicit monotone
nearest-neighbor path. -/
theorem randomEnvironmentEverHitsProbability_pos_from_zero
    {P : ℤ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℤ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (hW : W.IsElliptic) (k : ℤ) :
    0 < (F[P, X]) 0 k := by
  let κ := discreteMatrixKernel (randomEnvironmentTransitionMatrix W)
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hhitEvent :
      0 <
        (P 0 : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = k} := by
    by_cases hk0 : k = 0
    · -- Proof comment: a right jump followed by a left jump returns to `0` at time `2`.
      subst hk0
      have hmassStep :
          0 < ((κ ^ 1) 0) ({1} : Set ℤ) := by
        simpa [κ, pow_one] using randomEnvironmentRightPathMass_pos (W := W) hW 0 1
      have hbackStep :
          0 < κ 1 ({0} : Set ℤ) := by
        rw [rwreKernel_apply_singleton]
        have hleftprob : 0 < ((1 : ℝ≥0) - W.rightJumpProb 1 : ℝ≥0) := by
          exact tsub_pos_iff_lt.2 (hW.lt_one 1)
        simpa [randomEnvironmentTransitionMatrix] using hleftprob
      have hmass :
          0 < ((κ ^ 2) 0) ({0} : Set ℤ) := by
        simpa [pow_succ, pow_one, κ] using rwreKernel_singleton_pos_succ hmassStep hbackStep
      have hstep :
          0 < (P 0 : Measure Ω) {ω | X 2 ω = 0} := by
        have hpreimage : {ω | X 2 ω = 0} = X 2 ⁻¹' ({0} : Set ℤ) := by
          ext ω
          simp
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process 2) (measurableSet_singleton 0)]
        rw [hReal.transition_eq 0 2]
        simpa [κ] using hmass
      have hsubset :
          {ω | X 2 ω = 0} ⊆ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0} := by
        intro ω hω
        exact ⟨2, by decide, hω⟩
      exact lt_of_lt_of_le hstep (measure_mono hsubset)
    · by_cases hk_nonneg : 0 ≤ k
      · -- Proof comment: for `k > 0`, the monotone rightward path from `0` to `k` has positive
        -- mass and lies inside the positive-time hit event.
        let n : ℕ := Int.toNat k
        have hn : (n : ℤ) = k := by
          dsimp [n]
          exact Int.toNat_of_nonneg hk_nonneg
        have hn_pos : 0 < n := by
          apply Nat.pos_iff_ne_zero.mpr
          intro hn_zero
          have : k = 0 := by simpa [n, hn_zero] using hn.symm
          exact hk0 this
        have hmass :
            0 < ((κ ^ n) 0) ({k} : Set ℤ) := by
          simpa [κ, hn] using randomEnvironmentRightPathMass_pos (W := W) hW 0 n
        have hstep :
            0 < (P 0 : Measure Ω) {ω | X n ω = k} := by
          have hpreimage : {ω | X n ω = k} = X n ⁻¹' ({k} : Set ℤ) := by
            ext ω
            simp
          rw [hpreimage]
          rw [← Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton k)]
          rw [hReal.transition_eq 0 n]
          simpa [κ] using hmass
        have hsubset :
            {ω | X n ω = k} ⊆ {ω | ∃ m : ℕ, 0 < m ∧ X m ω = k} := by
          intro ω hω
          exact ⟨n, hn_pos, hω⟩
        exact lt_of_lt_of_le hstep (measure_mono hsubset)
      · -- Proof comment: for `k < 0`, the monotone leftward path from `0` to `k` gives the same
        -- positive-time hit event inclusion.
        let n : ℕ := Int.toNat (-k)
        have hk_neg : k < 0 := lt_of_not_ge hk_nonneg
        have hk_nonneg' : 0 ≤ -k := by omega
        have hn : (n : ℤ) = -k := by
          dsimp [n]
          exact Int.toNat_of_nonneg hk_nonneg'
        have hk_repr : k = -((n : ℤ)) := by
          omega
        have hn_pos : 0 < n := by
          apply Nat.pos_iff_ne_zero.mpr
          intro hn_zero
          have : -k = 0 := by simpa [n, hn_zero] using hn.symm
          omega
        have hmass :
            0 < ((κ ^ n) 0) ({k} : Set ℤ) := by
          simpa [κ, hk_repr] using randomEnvironmentLeftPathMass_pos (W := W) hW 0 n
        have hstep :
            0 < (P 0 : Measure Ω) {ω | X n ω = k} := by
          have hpreimage : {ω | X n ω = k} = X n ⁻¹' ({k} : Set ℤ) := by
            ext ω
            simp
          rw [hpreimage]
          rw [← Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton k)]
          rw [hReal.transition_eq 0 n]
          simpa [κ] using hmass
        have hsubset :
            {ω | X n ω = k} ⊆ {ω | ∃ m : ℕ, 0 < m ∧ X m ω = k} := by
          intro ω hω
          exact ⟨n, hn_pos, hω⟩
        exact lt_of_lt_of_le hstep (measure_mono hsubset)
  have hhit_ne_top :
      (P 0 : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = k} ≠ ⊤ := by
    have hle_univ :
        (P 0 : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = k} ≤
          (P 0 : Measure Ω) Set.univ := by
      exact measure_mono (by intro ω hω; simp)
    have hle : (P 0 : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = k} ≤ 1 := by
      simpa using hle_univ
    exact ne_of_lt (lt_of_le_of_lt hle (by simp))
  -- Proof comment: `F[P, X] 0 k` is the real probability of the positive-time hit event.
  rw [everHitsProbability_def]
  exact ENNReal.toReal_pos hhitEvent.ne' hhit_ne_top

/-- Helper for Theorem 19.33: ellipticity gives a strictly positive Chapter 17 ever-hit
probability between any two integers, because an explicit monotone nearest-neighbor path connects
the starting point to the target. -/
theorem randomEnvironmentEverHitsProbability_pos
    {P : ℤ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℤ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (hW : W.IsElliptic) (x y : ℤ) :
    0 < (F[P, X]) x y := by
  let κ := discreteMatrixKernel (randomEnvironmentTransitionMatrix W)
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hhitEvent :
      0 <
        (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y} := by
    by_cases hxy : x = y
    · -- Proof comment: if the target is the start state, a one-step excursion to the right and a
      -- one-step return to the left yield a positive-time return event.
      subst y
      have hmassStep :
          0 < ((κ ^ 1) x) ({x + 1} : Set ℤ) := by
        simpa [κ, pow_one] using randomEnvironmentRightPathMass_pos (W := W) hW x 1
      have hbackStep :
          0 < κ (x + 1) ({x} : Set ℤ) := by
        simpa [κ] using randomEnvironmentLeftPathMass_pos (W := W) hW (x + 1) 1
      have hmass :
          0 < ((κ ^ 2) x) ({x} : Set ℤ) := by
        simpa [pow_succ, pow_one, κ] using rwreKernel_singleton_pos_succ hmassStep hbackStep
      have hstep :
          0 < (P x : Measure Ω) {ω | X 2 ω = x} := by
        have hpreimage : {ω | X 2 ω = x} = X 2 ⁻¹' ({x} : Set ℤ) := by
          ext ω
          simp
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process 2) (measurableSet_singleton x)]
        rw [hReal.transition_eq x 2]
        simpa [κ] using hmass
      have hsubset :
          {ω | X 2 ω = x} ⊆ {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} := by
        intro ω hω
        exact ⟨2, by decide, hω⟩
      exact lt_of_lt_of_le hstep (measure_mono hsubset)
    · by_cases hxy_order : x ≤ y
      · -- Proof comment: when `y` lies to the right of `x`, the monotone rightward path from
        -- `x` to `y` has positive mass and sits inside the positive-time hit event.
        let n : ℕ := Int.toNat (y - x)
        have hn : (n : ℤ) = y - x := by
          dsimp [n]
          exact Int.toNat_of_nonneg (sub_nonneg.mpr hxy_order)
        have hy : y = x + n := by
          omega
        have hn_pos : 0 < n := by
          apply Nat.pos_iff_ne_zero.mpr
          intro hn_zero
          have : y = x := by
            omega
          exact hxy this.symm
        have hmass :
            0 < ((κ ^ n) x) ({y} : Set ℤ) := by
          simpa [κ, hy] using randomEnvironmentRightPathMass_pos (W := W) hW x n
        have hstep :
            0 < (P x : Measure Ω) {ω | X n ω = y} := by
          have hpreimage : {ω | X n ω = y} = X n ⁻¹' ({y} : Set ℤ) := by
            ext ω
            simp
          rw [hpreimage]
          rw [← Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton y)]
          rw [hReal.transition_eq x n]
          simpa [κ] using hmass
        have hsubset :
            {ω | X n ω = y} ⊆ {ω | ∃ m : ℕ, 0 < m ∧ X m ω = y} := by
          intro ω hω
          exact ⟨n, hn_pos, hω⟩
        exact lt_of_lt_of_le hstep (measure_mono hsubset)
      · -- Proof comment: when `y` lies to the left of `x`, the monotone leftward path plays the
        -- same role.
        let n : ℕ := Int.toNat (x - y)
        have hxy_lt : y < x := lt_of_not_ge hxy_order
        have hn : (n : ℤ) = x - y := by
          dsimp [n]
          exact Int.toNat_of_nonneg (sub_nonneg.mpr (le_of_lt hxy_lt))
        have hy : y = x - n := by
          omega
        have hn_pos : 0 < n := by
          apply Nat.pos_iff_ne_zero.mpr
          intro hn_zero
          have : y = x := by
            omega
          exact hxy this.symm
        have hmass :
            0 < ((κ ^ n) x) ({y} : Set ℤ) := by
          simpa [κ, hy] using randomEnvironmentLeftPathMass_pos (W := W) hW x n
        have hstep :
            0 < (P x : Measure Ω) {ω | X n ω = y} := by
          have hpreimage : {ω | X n ω = y} = X n ⁻¹' ({y} : Set ℤ) := by
            ext ω
            simp
          rw [hpreimage]
          rw [← Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton y)]
          rw [hReal.transition_eq x n]
          simpa [κ] using hmass
        have hsubset :
            {ω | X n ω = y} ⊆ {ω | ∃ m : ℕ, 0 < m ∧ X m ω = y} := by
          intro ω hω
          exact ⟨n, hn_pos, hω⟩
        exact lt_of_lt_of_le hstep (measure_mono hsubset)
  have hhit_ne_top :
      (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y} ≠ ⊤ := by
    have hle_univ :
        (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y} ≤
          (P x : Measure Ω) Set.univ := by
      exact measure_mono (by intro ω hω; simp)
    have hle : (P x : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = y} ≤ 1 := by
      simpa using hle_univ
    exact ne_of_lt (lt_of_le_of_lt hle (by simp))
  -- Proof comment: convert the positive probability of the hit event back to the Chapter 17
  -- ever-hit probability.
  rw [everHitsProbability_def]
  exact ENNReal.toReal_pos hhitEvent.ne' hhit_ne_top

end Bridge

section RWRERealization

variable (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]

/-- Helper for Theorem 19.33: under `P x`, the realized chain starts from `x` with probability
one. -/
private theorem initialState_prob_eq_one_local
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] (x : E) :
    (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hInit := congrArg (fun ν : Measure E ↦ ν ({x} : Set E)) (hReal.initial_eq x)
  -- Proof comment: evaluate the deterministic initial law `dirac x` on the singleton `{x}`.
  simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using hInit

/-- Helper for Theorem 19.33: under `P x`, the realized chain starts at the deterministic state
`x` almost surely. -/
private theorem initialState_ae_eq_start_local
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] (x : E) :
    ∀ᵐ ω ∂(P x : Measure Ω), X 0 ω = x := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hMeas : MeasurableSet {ω | X 0 ω = x} := by
    rw [show {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) by
      ext ω
      simp]
    exact hReal.measurable_process 0 (MeasurableSet.singleton x)
  -- Proof comment: the realization owner identifies the initial law with `dirac x`, so the
  -- time-`0` coordinate is almost surely pinned to `x`.
  exact (mem_ae_iff_prob_eq_one hMeas).2 <| by
    rw [show {ω | X 0 ω = x} = X 0 ⁻¹' ({x} : Set E) by
      ext ω
      simp]
    rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton x)]
    rw [hReal.initial_eq x]
    simp

/-- Helper for Theorem 19.33: if the realized trajectory starts outside `A`, then the first hit
searched from time `0` agrees with the first hit searched from time `1`. -/
private theorem hittingAfter_zero_eq_one_of_not_mem_initial_local
    {E : Type*} [MeasurableSpace E] {X : ℕ → Ω → E} {A : Set E} {ω : Ω}
    (h0 : X 0 ω ∉ A) :
    hittingAfter X A 0 ω = hittingAfter X A 1 ω := by
  -- Proof comment: monotonicity gives one inequality immediately, and `h0` rules out a time-`0`
  -- hit for the converse direction.
  refine le_antisymm (hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)) ?_
  by_cases htop : hittingAfter X A 0 ω = ⊤
  · have hle :
        hittingAfter X A 0 ω ≤ hittingAfter X A 1 ω :=
      hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)
    simpa [htop] using hle
  · lift hittingAfter X A 0 ω to ℕ using htop with n hn
    have hn_ne_top : hittingAfter X A 0 ω ≠ ⊤ := by
      rw [← hn]
      simp
    have hidx : (hittingAfter X A 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hmem : X n ω ∈ A := by
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hn_ne_top
    have hn_pos : 1 ≤ n := by
      by_contra hn_pos
      have hn_zero : n = 0 := by omega
      exact h0 (hn_zero ▸ hmem)
    -- Proof comment: once the first finite hit occurs at some `n ≥ 1`, the search from time `1`
    -- also stops by time `n`.
    simpa [hn] using
      hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω) hn_pos hmem

/-- Helper for Theorem 19.33: away from a two-point boundary, the positive-time boundary-hit event
is exactly the first-hit event defining `F_A`. -/
private theorem boundaryHitDistribution_eq_F_A_of_not_mem_boundary
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {a b x : E} (hx : x ∉ ({a, b} : Set E)) :
    ((P x : Measure Ω)
      {ω | hittingAfter X ({a, b} : Set E) 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({a, b} : Set E) 1) ω = b}).toReal =
      F_A P X ({a} : Set E) x b := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hboundary : ({a, b} : Set E) = insert b ({a} : Set E) := by
    ext y
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_left_comm, or_comm]
  have hEventAE :
      {ω | hittingAfter X ({a, b} : Set E) 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({a, b} : Set E) 1) ω = b} =ᵐ[μ]
        {ω | hittingAfter X (insert b ({a} : Set E)) 0 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert b ({a} : Set E)) 0) ω = b} := by
    have hstart : ∀ᵐ ω ∂μ, X 0 ω = x :=
      initialState_ae_eq_start_local (p := p) (P := P) (X := X) x
    filter_upwards [hstart] with ω hω
    have hx0 : X 0 ω ∉ ({a, b} : Set E) := by
      simpa [hω] using hx
    have hτeq :
        hittingAfter X ({a, b} : Set E) 0 ω =
          hittingAfter X ({a, b} : Set E) 1 ω :=
      hittingAfter_zero_eq_one_of_not_mem_initial_local hx0
    have hτeq' :
        hittingAfter X (insert b ({a} : Set E)) 0 ω =
          hittingAfter X (insert b ({a} : Set E)) 1 ω := by
      simpa [hboundary] using hτeq
    have hleft :
        ({ω | hittingAfter X ({a, b} : Set E) 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X ({a, b} : Set E) 1) ω = b} : Set Ω) ω ↔
          ({ω | hittingAfter X (insert b ({a} : Set E)) 1 ω < ⊤ ∧
              stoppedValue X (hittingAfter X (insert b ({a} : Set E)) 1) ω = b} :
            Set Ω) ω := by
      simpa [hboundary]
    have hright :
        ({ω | hittingAfter X (insert b ({a} : Set E)) 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert b ({a} : Set E)) 1) ω = b} :
          Set Ω) ω ↔
          ({ω | hittingAfter X (insert b ({a} : Set E)) 0 ω < ⊤ ∧
              stoppedValue X (hittingAfter X (insert b ({a} : Set E)) 0) ω = b} :
            Set Ω) ω := by
      have hstopEq :
          stoppedValue X (hittingAfter X (insert b ({a} : Set E)) 0) ω =
            stoppedValue X (hittingAfter X (insert b ({a} : Set E)) 1) ω := by
        rw [stoppedValue, hτeq']
        rfl
      constructor
      · rintro ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq'] using hfin
        · exact hstopEq.trans hstop
      · rintro ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq'] using hfin
        · exact hstopEq.symm.trans hstop
    -- Proof comment: away from the boundary, the positive-time event is the same as the
    -- time-`0` first-hit event defining `F_A`.
    exact propext (hleft.trans hright)
  rw [measure_congr hEventAE]
  suffices
      (μ
        {ω | hittingAfter X (insert b ({a} : Set E)) 0 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert b ({a} : Set E)) 0) ω = b}).toReal =
        F_A P X ({a} : Set E) x b by
    simpa [hboundary] using this
  rfl

/-- Helper for Theorem 19.33: the future path after time `k` is the Nat-shifted trajectory
`n ↦ Y (n + k)`. -/
private def shiftedFuturePath {E Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω']
    (Y : ℕ → Ω' → E) (k : ℕ) : Ω' → ℕ → E :=
  fun ω n ↦ Y (n + k) ω

/-- Helper for Theorem 19.33: if each time coordinate of `Y` is measurable, then the Nat-shifted
future-path map is measurable. -/
private theorem measurable_shiftedFuturePath {E Ω' : Type*} [MeasurableSpace E]
    [MeasurableSpace Ω'] (Y : ℕ → Ω' → E) (hY : ∀ n : ℕ, Measurable (Y n)) (k : ℕ) :
    Measurable (shiftedFuturePath Y k) := by
  refine measurable_pi_lambda _ fun n ↦ ?_
  simpa [shiftedFuturePath] using hY (n + k)

/-- Helper for Theorem 19.33: the finite history up to time `k` is packaged as a map into
`Fin (k + 1) → E`. -/
private def localPastPath {E Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω']
    (Y : ℕ → Ω' → E) (k : ℕ) : Ω' → Fin (k + 1) → E :=
  fun ω i ↦ Y i ω

/-- Helper for Theorem 19.33: the finite history map is measurable once each coordinate of `Y`
is measurable. -/
private theorem measurable_localPastPath {E Ω' : Type*} [MeasurableSpace E]
    [MeasurableSpace Ω'] (Y : ℕ → Ω' → E) (hY : ∀ n : ℕ, Measurable (Y n)) (k : ℕ) :
    Measurable (localPastPath Y k) := by
  -- Proof comment: each history coordinate is just the measurable slice `Y i`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [localPastPath] using hY i

/-- Helper for Theorem 19.33: the history filtration up to time `k` is the pullback
σ-algebra of the finite-history map `localPastPath X k`. -/
private theorem generatedFiltrationSpace_eq_localPastPath_comap
    {E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E) (k : ℕ) :
    generatedFiltrationSpace X k = MeasurableSpace.comap (localPastPath X k) inferInstance := by
  have hleft :
      MeasurableSpace.comap (localPastPath X k) inferInstance ≤ generatedFiltrationSpace X k := by
    have hPastMeas :
        Measurable[generatedFiltrationSpace X k] (fun ω ↦ fun i : Fin (k + 1) ↦ X i ω) := by
      -- Proof comment: every coordinate of the finite history already belongs to the generated
      -- history filtration up to time `k`.
      rw [@measurable_pi_iff]
      intro i
      refine Measurable.of_comap_le ?_
      exact
        le_iSup_of_le i <|
          le_iSup_of_le (show (i : ℕ) ≤ k from Nat.le_of_lt_succ i.2) le_rfl
    exact hPastMeas.comap_le
  have hright :
      generatedFiltrationSpace X k ≤ MeasurableSpace.comap (localPastPath X k) inferInstance := by
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (k + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap (localPastPath X k) inferInstance]
          (fun ω ↦ localPastPath X k ω i) := by
      exact (measurable_pi_apply i).comp (comap_measurable (localPastPath X k))
    simpa [localPastPath, i] using hCoord.comap_le
  exact le_antisymm hright hleft

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 19.33: every path measure is the projective limit of its finite
restriction marginals. -/
private theorem pathMeasure_isProjectiveLimit_restrictions_local
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (ν : Measure (ℕ → E)) :
    MeasureTheory.IsProjectiveLimit ν (fun J : Finset ℕ ↦ ν.map J.restrict) := by
  -- Proof comment: the finite restriction marginals are definitionally the projective-limit
  -- family of a path measure.
  intro J
  rfl

/-- Helper for Theorem 19.33: reindexing the ordered tuple attached to `J.orderEmbOfFin`
recovers the ordinary finite restriction map on path space. -/
private theorem piCongrLeft_orderEmbOfFin_eq_restrict_local
    {E : Type*} [MeasurableSpace E] (J : Finset ℕ) (y : ℕ → E) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i)) = J.restrict y := by
  -- Proof comment: the order isomorphism `Fin J.card ≃ J` identifies the sorted tuple with the
  -- usual restriction of a path to the finite index set `J`.
  dsimp
  ext j
  have hindex :
      J.orderEmbOfFin rfl ((J.orderIsoOfFin rfl).symm j) = j.1 := by
    exact congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply j)
  change
    ((Equiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
        (fun i ↦ y (J.orderEmbOfFin rfl i)) j) =
      J.restrict y j
  rw [Equiv.piCongrLeft_apply]
  simp [hindex]

/-- Helper for Theorem 19.33: the ordered finite future coordinates after time `k`. -/
private def shiftedFuturePathCoordinates
    {E Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω']
    {n : ℕ} (Y : ℕ → Ω' → E) (k : ℕ) (t : Fin n → ℕ) :
    Ω' → Fin n → E :=
  fun ω i ↦ Y (t i + k) ω

/-- Helper for Theorem 19.33: finite ordered coordinates of the shifted future path are
measurable. -/
private theorem measurable_shiftedFuturePathCoordinates
    {E Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω']
    {n : ℕ} (Y : ℕ → Ω' → E) (hY : ∀ n : ℕ, Measurable (Y n)) (k : ℕ) (t : Fin n → ℕ) :
    Measurable (shiftedFuturePathCoordinates Y k t) := by
  -- Proof comment: each tuple coordinate is the measurable slice `Y (t i + k)`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [shiftedFuturePathCoordinates, Nat.add_comm] using hY (t i + k)

/-- Helper for Theorem 19.33: reindexing the ordered shifted coordinates by `J.orderEmbOfFin`
matches the usual finite restriction event. -/
private theorem shiftedFuturePathIndicator_eq_restrictIndicator
    {E Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω']
    (Y : ℕ → Ω' → E) (k : ℕ) (J : Finset ℕ) {A : Set (J → E)} :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    let A' : Set (Fin J.card → E) :=
      (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
    (fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
        (shiftedFuturePathCoordinates Y k t ω)) =
      fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
        (J.restrict (shiftedFuturePath Y k ω)) := by
  dsimp
  funext ω
  have hEq :
      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
          (shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω) =
        J.restrict (shiftedFuturePath Y k ω) := by
    calc
      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
          (shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω)
          =
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
              (fun i ↦ shiftedFuturePath Y k ω (J.orderEmbOfFin rfl i)) := by
                rfl
      _ = J.restrict (shiftedFuturePath Y k ω) := by
            simpa using
              piCongrLeft_orderEmbOfFin_eq_restrict_local
                (J := J) (y := shiftedFuturePath Y k ω)
  have hmem :
      shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω ∈
          ((fun z ↦
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹'
            A) ↔
        J.restrict (shiftedFuturePath Y k ω) ∈ A := by
    simpa using show
      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
          (shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω) ∈ A ↔
        J.restrict (shiftedFuturePath Y k ω) ∈ A from by rw [hEq]
  by_cases hω : J.restrict (shiftedFuturePath Y k ω) ∈ A
  · have hω' :
        shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω ∈
          ((fun z ↦
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹'
            A) :=
      hmem.mpr hω
    simp [hω, hω']
  · have hω' :
        shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω ∉
          ((fun z ↦
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹'
            A) := by
        intro hω'
        exact hω (hmem.mp hω')
    simp [hω, hω']

/-- Helper for Theorem 19.33: evaluating a path measure on a finite-restriction preimage is the
same as evaluating its restricted pushforward. -/
private theorem kernelReal_restrictPreimage_eq_mapRestrictReal
    {E : Type*} [MeasurableSpace E] (ν : Measure (ℕ → E)) (J : Finset ℕ)
    {A : Set (J → E)} (hA : MeasurableSet A) :
    ν.real (J.restrict ⁻¹' A) = ((ν.map J.restrict).real A) := by
  -- Proof comment: this is the standard `map_measureReal_apply` rewrite for the measurable
  -- restriction map `J.restrict`.
  simpa using
    (MeasureTheory.map_measureReal_apply (μ := ν) (f := J.restrict)
      (Finset.measurable_restrict J) hA).symm

/-- Helper for Theorem 19.33: integrating the ordered-tuple indicator of a finite restriction
event against a path measure recovers the corresponding restricted pushforward mass. -/
private theorem orderedTupleIndicatorIntegral_eq_mapRestrictReal
    {E : Type*} [MeasurableSpace E] (ν : Measure (ℕ → E)) (J : Finset ℕ)
    {A : Set (J → E)} (hA : MeasurableSet A) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    let A' : Set (Fin J.card → E) :=
      (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
    (∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i)) ∂ν) =
      ((ν.map J.restrict).real A) := by
  dsimp
  -- Proof comment: rewrite the ordered tuple event as the ordinary restriction preimage and then
  -- use the standard `integral_indicator_one` / `map_measureReal_apply` identities.
  calc
    ∫ y, Set.indicator ((fun z ↦
          (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A)
          (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (fun i ↦ y (J.orderEmbOfFin rfl i)) ∂ν
        =
          ∫ y, Set.indicator (J.restrict ⁻¹' A) (fun _ : ℕ → E ↦ (1 : ℝ)) y ∂ν := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
            have hEq := piCongrLeft_orderEmbOfFin_eq_restrict_local (J := J) (y := y)
            have hmem :
                (fun i ↦ y (J.orderEmbOfFin rfl i)) ∈
                    ((fun z ↦
                      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E)
                        ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) ↔
                  y ∈ J.restrict ⁻¹' A := by
              simpa using show
                (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
                    (fun i ↦ y (J.orderEmbOfFin rfl i)) ∈ A ↔
                  J.restrict y ∈ A from by rw [hEq]
            by_cases hy : y ∈ J.restrict ⁻¹' A
            · have hy' :
                (fun i ↦ y (J.orderEmbOfFin rfl i)) ∈
                  ((fun z ↦
                    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E)
                      ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) := hmem.mpr hy
              simp [hy, hy']
            · have hy' :
                (fun i ↦ y (J.orderEmbOfFin rfl i)) ∉
                  ((fun z ↦
                    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E)
                      ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) := by
                  intro hy'
                  exact hy (hmem.mp hy')
              simp [hy, hy']
    _ = ν.real (J.restrict ⁻¹' A) := by
          simpa using
            (MeasureTheory.integral_indicator_one (μ := ν)
              (s := J.restrict ⁻¹' A)
              ((Finset.measurable_restrict J) hA))
    _ = ((ν.map J.restrict).real A) := by
          simpa using kernelReal_restrictPreimage_eq_mapRestrictReal (ν := ν) (J := J) hA

/-- Helper for Theorem 19.33: transport the Chapter 17 ordered-coordinate conditional-
expectation formula back to the discrete-time `ℕ` indexing used here. -/
private theorem orderedFutureCoordinateCondExp_of_markovProcessNat
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {m : ℕ} (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (f : (Fin m → E) → ℝ)
    (hf_meas : Measurable f) (hf_bdd : Bornology.IsBounded (Set.range f))
    (t : Fin m → ℕ) (ht : Monotone t) :
    ((P x : Measure Ω)[fun ω ↦ f (shiftedFuturePathCoordinates X k t ω) |
        generatedFiltrationSpace X k]) =ᵐ[(P x : Measure Ω)]
      fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X k ω) := by
  let Iℕ : AddSubmonoid NNReal := {
    carrier := {r | ∃ n : ℕ, ((n : ℕ) : NNReal) = r}
    zero_mem' := by
      exact ⟨0, by simp⟩
    add_mem' := by
      intro a b ha hb
      rcases ha with ⟨m, hm⟩
      rcases hb with ⟨n, hn⟩
      refine ⟨m + n, ?_⟩
      simpa [hm, hn] }
  let natTime : ℕ → Iℕ := fun n ↦
    ⟨n, by
      exact ⟨n, rfl⟩⟩
  let natIndex : Iℕ → ℕ := fun s ↦
    Classical.choose (show ∃ n : ℕ, ((n : ℕ) : NNReal) = s.1 from s.2)
  let Xnat : Iℕ → Ω → E := fun s ω ↦ X (natIndex s) ω
  let reindexPath : (ℕ → E) → Iℕ → E := fun y s ↦ y (natIndex s)
  let κnat : Kernel E (Iℕ → E) := κ.map reindexPath
  let tnat : Fin m → Iℕ := fun i ↦ natTime (t i)
  have hnatIndex_spec : ∀ s : Iℕ, ((natIndex s : ℕ) : NNReal) = s.1 := by
    intro s
    exact Classical.choose_spec (show ∃ n : ℕ, ((n : ℕ) : NNReal) = s.1 from s.2)
  have hnatIndex_natTime : ∀ n : ℕ, natIndex (natTime n) = n := by
    intro n
    have hcast : (((natIndex (natTime n) : ℕ) : ℕ) : NNReal) = n := by
      simpa [natTime] using hnatIndex_spec (natTime n)
    exact_mod_cast hcast
  have hnatTime_natIndex : ∀ s : Iℕ, natTime (natIndex s) = s := by
    intro s
    apply Subtype.ext
    exact hnatIndex_spec s
  have hnatIndex_add : ∀ s u : Iℕ, natIndex (s + u) = natIndex s + natIndex u := by
    intro s u
    have hcast :
        (((natIndex (s + u) : ℕ) : ℕ) : NNReal) =
          ((natIndex s + natIndex u : ℕ) : NNReal) := by
      calc
        (((natIndex (s + u) : ℕ) : ℕ) : NNReal) = (s + u).1 := hnatIndex_spec (s + u)
        _ = s.1 + u.1 := rfl
        _ = (((natIndex s : ℕ) : ℕ) : NNReal) + (((natIndex u : ℕ) : ℕ) : NNReal) := by
              rw [hnatIndex_spec s, hnatIndex_spec u]
        _ = ((natIndex s + natIndex u : ℕ) : NNReal) := by simp
    exact_mod_cast hcast
  have hnatTime_le_iff : ∀ {n l : ℕ}, natTime n ≤ natTime l ↔ n ≤ l := by
    intro n l
    change ((n : NNReal) ≤ (l : NNReal)) ↔ n ≤ l
    norm_num
  have hsub : ∀ ⦃s u : Iℕ⦄, s ≤ u → u.1 - s.1 ∈ Iℕ := by
    intro s u hsu
    change ∃ n : ℕ, ((n : ℕ) : NNReal) = u.1 - s.1
    refine ⟨natIndex u - natIndex s, ?_⟩
    have hle : natIndex s ≤ natIndex u := by
      have : natTime (natIndex s) ≤ natTime (natIndex u) := by
        simpa [hnatTime_natIndex] using hsu
      exact hnatTime_le_iff.mp this
    calc
      (((natIndex u - natIndex s : ℕ) : ℕ) : NNReal)
          = ((natIndex u : ℕ) : NNReal) - ((natIndex s : ℕ) : NNReal) := by
              simpa [Nat.cast_sub hle]
      _ = u.1 - s.1 := by rw [hnatIndex_spec u, hnatIndex_spec s]
  have hreindex_meas : Measurable reindexPath := by
    -- Proof comment: the transported path reindexing is coordinatewise evaluation at the chosen
    -- natural representative of each submonoid time.
    refine measurable_pi_lambda _ fun s ↦ ?_
    exact measurable_pi_apply (natIndex s)
  have hpathMap_meas : Measurable (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) := by
    -- Proof comment: the original trajectory map is measurable because each coordinate of `X`
    -- is measurable.
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using hX_meas n
  have hgenerated :
      ∀ n : ℕ, generatedFiltrationSpace Xnat (natTime n) = generatedFiltrationSpace X n := by
    intro n
    rw [generatedFiltrationSpace, generatedFiltrationSpace]
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun s hs ↦ ?_
      have hs' : natIndex s ≤ n := by
        have : natTime (natIndex s) ≤ natTime n := by
          simpa [hnatTime_natIndex] using hs
        exact hnatTime_le_iff.mp this
      have hcomap :
          MeasurableSpace.comap (X (natIndex s)) inferInstance ≤ generatedFiltrationSpace X n := by
        exact le_iSup_of_le (natIndex s) <| le_iSup_of_le hs' le_rfl
      simpa [Xnat] using hcomap
    · refine iSup₂_le fun r hr ↦ ?_
      have hr' : natTime r ≤ natTime n := hnatTime_le_iff.mpr hr
      have hcomap :
          MeasurableSpace.comap (Xnat (natTime r)) inferInstance ≤
            generatedFiltrationSpace Xnat (natTime n) := by
        exact le_iSup_of_le (natTime r) <| le_iSup_of_le hr' le_rfl
      simpa [Xnat, hnatIndex_natTime] using hcomap
  have hgenerated' :
      ∀ s : Iℕ, generatedFiltrationSpace Xnat s = generatedFiltrationSpace X (natIndex s) := by
    intro s
    calc
      generatedFiltrationSpace Xnat s
          = generatedFiltrationSpace Xnat (natTime (natIndex s)) := by
              rw [hnatTime_natIndex s]
      _ = generatedFiltrationSpace X (natIndex s) := hgenerated (natIndex s)
  have htransition : ∀ s : Iℕ, transitionKernel κnat s = transitionKernel κ (natIndex s) := by
    intro s
    ext y A hA
    rw [transitionKernel_apply, transitionKernel_apply]
    have hrow : κnat y = (κ y).map reindexPath := by
      simpa [κnat] using Kernel.map_apply κ hreindex_meas y
    rw [hrow]
    rw [Measure.map_map (μ := κ y) (f := reindexPath) (g := fun z : Iℕ → E ↦ z s)
      (measurable_pi_apply s) hreindex_meas]
    rfl
  letI : IsTimeHomogeneousMarkovProcess Xnat P κnat := by
    refine
      { measurable_process := fun s ↦ by simpa [Xnat] using hX_meas (natIndex s)
        initial_state := ?_
        path_law := ?_
        markov_property := ?_ }
    · intro y
      have hzero : natIndex (0 : Iℕ) = 0 := by
        have : (0 : Iℕ) = natTime 0 := by
          apply Subtype.ext
          simp [natTime]
        simpa [this] using hnatIndex_natTime 0
      simpa [Xnat, hzero] using hX0 y
    · intro y
      calc
        κnat y = ((κ y).map reindexPath) := by
              simpa [κnat] using Kernel.map_apply κ hreindex_meas y
        _ = (((P y : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω)).map reindexPath) := by
              rw [hpath y]
        _ = (P y : Measure Ω).map (fun ω : Ω ↦ fun s : Iℕ ↦ Xnat s ω) := by
              rw [Measure.map_map hreindex_meas hpathMap_meas]
              rfl
    · intro y A hA s u
      have hsum : Xnat (u + s) ⁻¹' A = X (natIndex u + natIndex s) ⁻¹' A := by
        ext ω
        simp [Xnat, hnatIndex_add]
      have hright :
          (fun ω ↦ ((transitionKernel κnat u) (Xnat s ω)).real A) =
            fun ω ↦ ((transitionKernel κ (natIndex u)) (X (natIndex s) ω)).real A := by
        funext ω
        rw [htransition u]
      -- Proof comment: after identifying the transported time indices and history sigma-algebras,
      -- the Markov property is exactly the original `ℕ`-indexed owner field.
      simpa [hsum, hgenerated' s, hright] using
        (hMarkov.markov_property y hA (natIndex s) (natIndex u))
  have hordered :
      HasOrderedFutureCoordinateConditionalExpectationFormula Xnat P κnat :=
    hasOrderedFutureCoordinateConditionalExpectationFormula_of_isTimeHomogeneousMarkovProcess
      Xnat P κnat hsub
  have htnat : Monotone tnat := by
    intro i j hij
    exact hnatTime_le_iff.mpr (ht hij)
  have horderedNat :
      (P x : Measure Ω)[fun ω ↦ f (futurePathCoordinates Xnat (natTime k) tnat ω) |
          generatedFiltrationSpace Xnat (natTime k)] =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ∫ y, f (fun i ↦ y (tnat i)) ∂κnat (Xnat (natTime k) ω) := by
    -- Proof comment: this is the Chapter 17 ordered-coordinate formula on the transported
    -- natural-number submonoid.
    have hk_nonneg : 0 ≤ natTime k := by
      show (0 : NNReal) ≤ ((natTime k : Iℕ) : NNReal)
      exact zero_le _
    simpa using hordered hf_meas hf_bdd (t := tnat) htnat (natTime k) x hk_nonneg
  have hleft :
      (fun ω ↦ f (futurePathCoordinates Xnat (natTime k) tnat ω)) =
        fun ω ↦ f (shiftedFuturePathCoordinates X k t ω) := by
    -- Proof comment: after transport, the Chapter 17 future coordinates become the local
    -- shifted-coordinate tuple `ω ↦ (X (k + t i) ω)_i`.
    funext ω
    congr 1
    funext i
    simp [futurePathCoordinates, shiftedFuturePathCoordinates, Xnat, tnat, natTime,
      hnatIndex_add, hnatIndex_natTime, add_comm]
  have hright :
      (fun ω ↦ ∫ y, f (fun i ↦ y (tnat i)) ∂κnat (Xnat (natTime k) ω)) =
        fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X k ω) := by
    -- Proof comment: the transported path-kernel row is just the original row seen through the
    -- index reparameterization `natIndex`.
    funext ω
    have htuple_meas :
        Measurable (fun y : Iℕ → E ↦ f (fun i ↦ y (tnat i))) := by
      refine hf_meas.comp ?_
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_pi_apply (tnat i)
    have hrow : κnat (Xnat (natTime k) ω) = (κ (X k ω)).map reindexPath := by
      rw [show Xnat (natTime k) ω = X k ω by simp [Xnat, hnatIndex_natTime]]
      simpa [κnat] using Kernel.map_apply κ hreindex_meas (X k ω)
    rw [hrow]
    rw [MeasureTheory.integral_map hreindex_meas.aemeasurable htuple_meas.aestronglyMeasurable]
    congr 1
    funext y
    congr 1
    funext i
    simp [reindexPath, tnat, hnatIndex_natTime]
  calc
    (P x : Measure Ω)[fun ω ↦ f (shiftedFuturePathCoordinates X k t ω) |
        generatedFiltrationSpace X k]
        =ᵐ[(P x : Measure Ω)]
          (P x : Measure Ω)[fun ω ↦ f (futurePathCoordinates Xnat (natTime k) tnat ω) |
            generatedFiltrationSpace Xnat (natTime k)] := by
              rw [hgenerated k]
              exact MeasureTheory.condExp_congr_ae (Filter.EventuallyEq.of_eq hleft.symm)
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ y, f (fun i ↦ y (tnat i)) ∂κnat (Xnat (natTime k) ω) :=
      horderedNat
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X k ω) :=
      Filter.EventuallyEq.of_eq hright

/-- Helper for Theorem 19.33: evaluating a composed kernel against a restricted pushforward is
the same as integrating the row masses over the source event. -/
private theorem kernelCompRestrictMapRealEqSetIntegral
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (κ : Kernel E F) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → E} (hY : Measurable Y)
    {B : Set Ω} (_hB : MeasurableSet B) {A : Set F} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
  let ν : Measure E := ((μ.restrict B).map Y)
  have hkernel_int :
      Integrable (fun y : E ↦ (κ y).real A) ν := by
    simpa [ν] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
        (μ := ν) (κ := κ) hA)
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun y : E ↦ (κ y).real A :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hcomp_real :
      ((κ ∘ₘ ν).real A) = ∫ y, (κ y).real A ∂ν := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
      (ProbabilityTheory.Kernel.aemeasurable _)]
    have hlintegral :
        ∫⁻ y, κ y A ∂ν = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
      calc
        ∫⁻ y, κ y A ∂ν = ∫⁻ y, ENNReal.ofReal ((κ y).real A) ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
        _ = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
    rw [hlintegral, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae hkernel_nonneg
  have hmap_real :
      ∫ y, (κ y).real A ∂ν = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
    change ∫ y, (κ y).real A ∂((μ.restrict B).map Y) = ∫ ω, (κ (Y ω)).real A ∂(μ.restrict B)
    rw [MeasureTheory.integral_map hY.aemeasurable hkernel_int.aestronglyMeasurable]
  calc
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ y, (κ y).real A ∂ν := by
      simpa [ν] using hcomp_real
    _ = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
      simpa [ν] using hmap_real

/-- Helper for Theorem 19.33: Theorem 17.9 gives the conditional law of every finite shifted
future restriction on history events. -/
private theorem shiftedFuturePathRestrictionIndicator_condExp
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {κ : Kernel E (ℕ → E)}
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    ((P x : Measure Ω)[fun ω ↦ Set.indicator A (fun _ ↦ (1 : ℝ))
        (J.restrict (shiftedFuturePath X k ω)) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ (((κ (X k ω)).map J.restrict).real A) := by
  let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
  let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
  let A' : Set (Fin J.card → E) :=
    (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
  have hA'_meas : MeasurableSet A' := by
    exact hA.preimage ((MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e).measurable)
  have hIndicator_meas :
      Measurable (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ)) := by
    -- Proof comment: the finite-coordinate event indicator is measurable on the ordered tuple
    -- space.
    exact Measurable.indicator measurable_const hA'_meas
  have hIndicator_bdd :
      Bornology.IsBounded (Set.range (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ))) := by
    -- Proof comment: the indicator takes only the values `0` and `1`.
    simpa [A'] using isBounded_range_indicator_one A'
  have hFiniteIndicator :
      (P x : Measure Ω)[fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (shiftedFuturePathCoordinates X k t ω) | generatedFiltrationSpace X k] =ᵐ[
            (P x : Measure Ω)] fun ω ↦
              ∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i))
                ∂κ (X k ω) := by
    -- Proof comment: transport the Chapter 17 ordered-coordinate formula through the natural
    -- numbers viewed as an additive submonoid of `NNReal`.
    exact
      orderedFutureCoordinateCondExp_of_markovProcessNat
        (X := X) (P := P) (κ := κ) (hX_meas := hX_meas) (hX0 := hX0) (hpath := hpath)
        x k (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ))
        hIndicator_meas hIndicator_bdd t
        (by simpa [t] using (J.orderEmbOfFin rfl).monotone)
  have hleft_fun :
      (fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (shiftedFuturePathCoordinates X k t ω)) =
        fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
          (J.restrict (shiftedFuturePath X k ω)) := by
    -- Proof comment: the ordered tuple event is exactly the same finite restriction event after
    -- reindexing by the order isomorphism of `J`.
    simpa [e, t, A'] using
      shiftedFuturePathIndicator_eq_restrictIndicator (Y := X) (k := k) (J := J) (A := A)
  have hFiniteIndicator' :
      (P x : Measure Ω)[fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
          (J.restrict (shiftedFuturePath X k ω)) | generatedFiltrationSpace X k] =ᵐ[
            (P x : Measure Ω)] fun ω ↦
              ∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i))
                ∂κ (X k ω) := by
    simpa [hleft_fun] using hFiniteIndicator
  filter_upwards [hFiniteIndicator'] with ω hω
  have hright :
      (∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i)) ∂κ (X k ω)) =
        (((κ (X k ω)).map J.restrict).real A) := by
    -- Proof comment: the auxiliary integral is exactly the restricted path-kernel mass by the
    -- finite-restriction integral helper.
    simpa [e, t, A'] using
      orderedTupleIndicatorIntegral_eq_mapRestrictReal (ν := κ (X k ω)) (J := J) hA
  simpa [hright] using hω

/-- Helper for Theorem 19.33: on each history event, the shifted future-path law agrees with the
path kernel mixed against the present-state law. -/
private theorem restrictedShiftedFuturePathLaw_eq_mixedPathLaw_on_history
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {κ : Kernel E (ℕ → E)}
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X k] B) :
    let μ : Measure Ω := (P x : Measure Ω)
    let νB : Measure (ℕ → E) := (μ.restrict B).map (shiftedFuturePath X k)
    let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X k))
    νB = ρB := by
  let μ : Measure Ω := (P x : Measure Ω)
  let νB : Measure (ℕ → E) := (μ.restrict B).map (shiftedFuturePath X k)
  let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X k))
  have hgenerated_le : generatedFiltrationSpace X k ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_localPastPath_comap X k]
    exact (measurable_localPastPath X hX_meas k).comap_le
  have hPathMap_meas : Measurable (fun ω ↦ fun m : ℕ ↦ X m ω) := by
    refine measurable_pi_lambda _ fun m ↦ ?_
    simpa using hX_meas m
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  have hB_ambient : MeasurableSet B := hgenerated_le B hB
  have hJ :
      ∀ J : Finset ℕ, νB.map J.restrict = ρB.map J.restrict := by
    intro J
    let κJ : Kernel E (J → E) := κ.map J.restrict
    letI : IsMarkovKernel κJ := by
      let hmeasRestrict : Measurable (J.restrict : (ℕ → E) → J → E) :=
        Finset.measurable_restrict J
      refine ⟨fun y : E ↦ ?_⟩
      have hrow : κJ y = (κ y).map J.restrict := by
        simpa [κJ] using Kernel.map_apply κ hmeasRestrict y
      rw [hrow]
      simpa using Measure.isProbabilityMeasure_map (μ := κ y) hmeasRestrict.aemeasurable
    refine Measure.ext fun A hA ↦ ?_
    let futureEvent : Set Ω := (fun ω ↦ J.restrict (shiftedFuturePath X k ω)) ⁻¹' A
    have hfuture_meas : MeasurableSet futureEvent := by
      simpa [futureEvent] using
        ((Finset.measurable_restrict J).comp (measurable_shiftedFuturePath X hX_meas k)) hA
    have hIndicatorInt :
        Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hfuture_meas
    have hmarkov :
        μ⟦futureEvent | generatedFiltrationSpace X k⟧ =ᵐ[μ]
          fun ω ↦ (((κ (X k ω)).map J.restrict).real A) := by
      -- Proof comment: the finite-restriction conditional-law formula gives the event mass on
      -- each history event.
      simpa [futureEvent] using
        shiftedFuturePathRestrictionIndicator_condExp
          (hX_meas := hX_meas) (hX0 := hX0) (hpath := hpath) x k J hA
    have hleft_real :
        (((νB.map J.restrict).real A)) = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
      have hmass :
          μ.real (B ∩ futureEvent) =
            ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
        calc
          μ.real (B ∩ futureEvent)
              = ∫ ω in B, (μ⟦futureEvent | generatedFiltrationSpace X k⟧) ω ∂μ := by
                  rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hB,
                    ← MeasureTheory.integral_indicator hB_ambient]
                  simpa [futureEvent, Set.indicator_indicator, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                    (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                      (hB_ambient.inter hfuture_meas)).symm
          _ = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
                exact MeasureTheory.integral_congr_ae hmarkov.restrict
      have hmapJ :
          νB.map J.restrict = (μ.restrict B).map (fun ω ↦ J.restrict (shiftedFuturePath X k ω)) := by
        dsimp [νB]
        rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict J).aemeasurable]
        · rfl
        · exact (measurable_shiftedFuturePath X hX_meas k).aemeasurable
      calc
        (((νB.map J.restrict).real A))
            = ((((μ.restrict B).map (fun ω ↦ J.restrict (shiftedFuturePath X k ω))).real A)) := by
                rw [hmapJ]
        _ = (μ.restrict B).real futureEvent := by
              simpa [futureEvent] using
                (MeasureTheory.map_measureReal_apply
                  (μ := (μ.restrict B)) (f := fun ω ↦ J.restrict (shiftedFuturePath X k ω))
                  ((Finset.measurable_restrict J).comp (measurable_shiftedFuturePath X hX_meas k))
                  hA)
        _ = μ.real (futureEvent ∩ B) := by
              simpa [futureEvent] using
                (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := B) (t := futureEvent)
                  hfuture_meas)
        _ = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
              simpa [Set.inter_comm] using hmass
    have hright_real :
        (((ρB.map J.restrict).real A)) = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
      let κJ : Kernel E (J → E) := κ.map J.restrict
      have hmap :
          ρB.map J.restrict = κJ ∘ₘ ((μ.restrict B).map (X k)) := by
        dsimp [ρB, κJ]
        simpa using Measure.map_comp (((μ.restrict B).map (X k))) κ (Finset.measurable_restrict J)
      haveI : IsMarkovKernel κJ := by
        let hmeasRestrict : Measurable (J.restrict : (ℕ → E) → J → E) :=
          Finset.measurable_restrict J
        refine ⟨fun y : E ↦ ?_⟩
        have hrow : κJ y = (κ y).map J.restrict := by
          simpa [κJ] using Kernel.map_apply κ hmeasRestrict y
        rw [hrow]
        simpa using Measure.isProbabilityMeasure_map (μ := κ y) hmeasRestrict.aemeasurable
      rw [hmap]
      calc
        ((κJ ∘ₘ ((μ.restrict B).map (X k))).real A)
            = ∫ ω in B, (κJ (X k ω)).real A ∂μ := by
                simpa [κJ] using
                  (kernelCompRestrictMapRealEqSetIntegral
                    (κ := κ.map J.restrict) (μ := μ) (Y := X k) (hY := hX_meas k)
                    (B := B) hB_ambient (A := A) hA)
        _ = ∫ ω in B, (((κ (X k ω)).map J.restrict).real A) ∂μ := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              have hrow : κJ (X k ω) = (κ (X k ω)).map J.restrict := by
                simpa [κJ] using Kernel.map_apply κ (Finset.measurable_restrict J) (X k ω)
              exact congrArg (fun ν : Measure (J → E) ↦ ν.real A) hrow
    have hleft_ne_top : (νB.map J.restrict) A ≠ ⊤ := by
      simpa using measure_lt_top (νB.map J.restrict) A
    have hright_ne_top : (ρB.map J.restrict) A ≠ ⊤ := by
      simpa using measure_lt_top (ρB.map J.restrict) A
    exact
      (MeasureTheory.measureReal_eq_measureReal_iff
        (μ := νB.map J.restrict) (ν := ρB.map J.restrict)
        (s := A) (t := A) hleft_ne_top hright_ne_top).mp
        (hleft_real.trans hright_real.symm)
  letI : Nonempty E := ⟨x⟩
  have hν :
      MeasureTheory.IsProjectiveLimit νB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    simpa [νB] using pathMeasure_isProjectiveLimit_restrictions_local νB
  have hρ :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ ρB.map J.restrict) := by
    simpa [ρB] using pathMeasure_isProjectiveLimit_restrictions_local ρB
  have hρ' :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    intro J
    exact (hJ J).symm
  haveI : ∀ J : Finset ℕ, IsFiniteMeasure (νB.map J.restrict) := fun _ ↦ inferInstance
  -- Proof comment: equality of all finite restrictions identifies the full path measures by
  -- projective-limit uniqueness.
  exact MeasureTheory.IsProjectiveLimit.unique hν hρ'

/-- Helper for Theorem 19.33: bounded measurable shifted-future-path functionals satisfy the
standard discrete-time conditional-expectation formula along `generatedFiltrationSpace X k`. -/
private theorem futurePathCondExp_shiftedNat
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {κ : Kernel E (ℕ → E)}
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (g : (ℕ → E) → ℝ) (hg_meas : Measurable g)
    (hg_bdd : Bornology.IsBounded (Set.range g)) :
    ((P x : Measure Ω)[fun ω ↦ g (shiftedFuturePath X k ω) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hPathMap_meas : Measurable (fun ω ↦ fun m : ℕ ↦ X m ω) := by
    refine measurable_pi_lambda _ fun m ↦ ?_
    simpa using hX_meas m
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  have hgenerated_le : generatedFiltrationSpace X k ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_localPastPath_comap X k]
    exact (measurable_localPastPath X hX_meas k).comap_le
  have hfuture_meas : Measurable (shiftedFuturePath X k) :=
    measurable_shiftedFuturePath X hX_meas k
  have hg_int :
      Integrable (fun ω ↦ g (shiftedFuturePath X k ω)) μ := by
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
    -- Proof comment: bounded measurable path observables are integrable under the start law.
    refine Integrable.of_bound (hg_meas.comp hfuture_meas).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨shiftedFuturePath X k ω, rfl⟩
  have hXk_generated : Measurable[generatedFiltrationSpace X k] (X k) := by
    -- Proof comment: the present state is the last coordinate of the finite history map.
    rw [generatedFiltrationSpace_eq_localPastPath_comap X k]
    have hCoord :
        Measurable[MeasurableSpace.comap (localPastPath X k) inferInstance]
          (fun ω ↦ localPastPath X k ω (Fin.last k)) := by
      exact (measurable_pi_apply (Fin.last k)).comp (comap_measurable (localPastPath X k))
    simpa [localPastPath] using hCoord
  have hKernelIntegral_meas :
      Measurable fun z : E ↦ ∫ y, g y ∂κ z := by
    -- Proof comment: integrating a measurable real-valued path functional against the kernel is
    -- measurable in the starting state.
    exact
      (hg_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : E ↦ ∫ y, g y ∂κ z).measurable
  have hKernelIntegral_meas_generated :
      Measurable[generatedFiltrationSpace X k] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    -- Proof comment: compose the measurable kernel integral with the history-measurable present
    -- state.
    exact hKernelIntegral_meas.comp hXk_generated
  have hKernelIntegral_meas_ambient :
      Measurable fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    exact hKernelIntegral_meas.comp (hX_meas k)
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
  have hCondExp :=
    MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hg_int
      (fun s hs hμs ↦ by
        -- Proof comment: the kernel-integral candidate is bounded on every finite history event.
        refine IntegrableOn.of_bound hμs hKernelIntegral_meas_ambient.aestronglyMeasurable C ?_
        refine Filter.Eventually.of_forall fun ω ↦ ?_
        have hbound_row :
            ‖∫ y, g y ∂κ (X k ω)‖ ≤ C := by
          have hgC : ∀ᵐ y ∂κ (X k ω), ‖g y‖ ≤ C := by
            exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
          simpa using
            (MeasureTheory.norm_integral_le_of_norm_le_const (μ := κ (X k ω)) hgC)
        exact hbound_row)
      (fun s hs _hμs ↦ by
        -- Proof comment: on each history event, identify the restricted future-path law with the
        -- mixed path-kernel law and then integrate `g` against that common path measure.
        let νB : Measure (ℕ → E) := (μ.restrict s).map (shiftedFuturePath X k)
        let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict s).map (X k))
        have hs_history : MeasurableSet[generatedFiltrationSpace X k] s := hs
        have hlaw : νB = ρB := by
          simpa [μ, νB, ρB] using
            restrictedShiftedFuturePathLaw_eq_mixedPathLaw_on_history
              (hX_meas := hX_meas) (hX0 := hX0) (hpath := hpath) x k hs_history
        haveI : IsFiniteMeasure νB := by
          dsimp [νB]
          infer_instance
        have hg_νB_int : Integrable g νB := by
          refine Integrable.of_bound hg_meas.aestronglyMeasurable C ?_
          exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
        have hg_ρB_int : Integrable g ρB := by
          rw [← hlaw]
          exact hg_νB_int
        have hleft :
            ∫ ω in s, g (shiftedFuturePath X k ω) ∂μ = ∫ y, g y ∂νB := by
          change ∫ ω, g (shiftedFuturePath X k ω) ∂(μ.restrict s) = ∫ y, g y ∂νB
          rw [show νB = (μ.restrict s).map (shiftedFuturePath X k) by rfl]
          exact
            (MeasureTheory.integral_map hfuture_meas.aemeasurable
              hg_meas.aestronglyMeasurable).symm
        have hright :
            ∫ y, g y ∂ρB = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
          let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict s).map (X k))
          have hcomp :
              (κ ∘ₖ κ₀) () = ρB := by
            simp [κ₀, ρB]
          calc
            ∫ y, g y ∂ρB = ∫ y, g y ∂((κ ∘ₖ κ₀) ()) := by rw [← hcomp]
            _ = ∫ z, ∫ y, g y ∂κ z ∂κ₀ () := by
                  simpa using
                    (ProbabilityTheory.Kernel.integral_comp (η := κ) (κ := κ₀) (a := ())
                      hg_ρB_int)
            _ = ∫ z, ∫ y, g y ∂κ z ∂((μ.restrict s).map (X k)) := by
                  simp [κ₀]
            _ = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_map (hX_meas k).aemeasurable
                      hKernelIntegral_meas.aestronglyMeasurable)
        exact (hleft.trans (hlaw ▸ hright)).symm)
      hKernelIntegral_meas_generated.aestronglyMeasurable
  exact hCondExp.symm

/-- Helper for Theorem 19.33: integrating a real observable of the realized state `X n` under the
start law `P x` agrees with the `n`-step transition row. -/
private theorem localMarkovRealization_integral_comp_transition_eq
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {g : E → ℝ} (x : E) (n : ℕ) :
    ∫ ω, g (X n ω) ∂(P x : Measure Ω) =
      ∫ z, g z ∂((discreteMatrixKernel p ^ n) x) := by
  let hReal :
      IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X := inferInstance
  have hXn : Measurable (X n) := hReal.measurable_process n
  -- Proof comment: rewrite the time-`n` marginal through the realization field `transition_eq`.
  rw [← hReal.transition_eq x n, integral_map]
  · exact hXn.aemeasurable
  · exact (Measurable.of_discrete : Measurable g).aestronglyMeasurable

/-- Helper for Theorem 19.33: the canonical path-law kernel of a realization started from `x`
is the push-forward of `P x` along the full path map. This is the path-space owner used for the
restart/harmonicity bridge, not new mathematical surface API. -/
private def realizationPathKernel
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} :
    Kernel E (ℕ → E) :=
  Kernel.ofFunOfCountable fun x ↦
    (P x : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω)

/-- Helper for Theorem 19.33: each row of the local path-law kernel is the pushforward of the
start law along the full realized trajectory. -/
@[simp] private theorem realizationPathKernel_apply
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    (x : E) :
    realizationPathKernel (P := P) (X := X) x =
      (P x : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) := rfl

/-- Helper for Theorem 19.33: the time-`n` marginal of the local path-law kernel is the original
`n`-step transition row. -/
private theorem realizationPathKernel_transition
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) (n : ℕ) :
    transitionKernel (realizationPathKernel (P := P) (X := X)) n x =
      (discreteMatrixKernel p ^ n) x := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  -- Proof comment: read the time-`n` coordinate of the pushed-forward path law and then use the
  -- realization field `transition_eq`.
  rw [transitionKernel_apply]
  change
    Measure.map (fun ξ : ℕ → E ↦ ξ n)
      ((P x : Measure Ω).map (fun ω : Ω ↦ fun m : ℕ ↦ X m ω)) =
        (discreteMatrixKernel p ^ n) x
  rw [Measure.map_map]
  · simpa using hReal.transition_eq x n
  · exact measurable_pi_apply n
  · refine measurable_pi_lambda _ fun m ↦ ?_
    exact hReal.measurable_process m

/-- Helper for Theorem 19.33: the local path-law kernel turns the realization into a
time-homogeneous Markov process on path space. -/
private theorem realizationPathKernel_isTimeHomogeneousMarkovProcess
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsTimeHomogeneousMarkovProcess X P (realizationPathKernel (P := P) (X := X)) := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  refine
    { measurable_process := hReal.measurable_process
      initial_state := ?_
      path_law := ?_
      markov_property := ?_ }
  · intro x
    -- Proof comment: the initial state is already pinned by the realization owner.
    exact initialState_prob_eq_one_local (p := p) (P := P) (X := X) x
  · intro x
    rfl
  · intro x A hA s t
    -- Proof comment: rewrite the path-kernel transition back to the original realization
    -- transition kernel before applying the existing Markov property.
    refine (hReal.markov_property x hA s t).trans ?_
    filter_upwards with ω
    rw [realizationPathKernel_transition (p := p) (P := P) (X := X) (x := X s ω) t]

/-- Helper for Theorem 19.33: finite prefix avoidance of a boundary set is measurable on path
space. -/
private theorem avoidBeforePathEvent_measurable
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (B : Set E) :
    ∀ n : ℕ, MeasurableSet {ξ : ℕ → E | ∀ m < n, ξ m ∉ B}
  | 0 => by
      simp
  | n + 1 => by
      have hEq :
          {ξ : ℕ → E | ∀ m < n + 1, ξ m ∉ B} =
            {ξ : ℕ → E | ∀ m < n, ξ m ∉ B} ∩ {ξ : ℕ → E | ξ n ∉ B} := by
        ext ξ
        constructor
        · intro hξ
          refine ⟨?_, ?_⟩
          · intro m hm
            exact hξ m (Nat.lt_succ_of_lt hm)
          · exact hξ n (Nat.lt_succ_self n)
        · intro hξ m hm
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
          · exact hξ.1 m hm
          · exact hξ.2
      -- Proof comment: split the length-`n + 1` avoidance condition into the previous prefix and
      -- the single coordinate constraint at time `n`.
      rw [hEq]
      refine (avoidBeforePathEvent_measurable B n).inter ?_
      change MeasurableSet (((fun ξ : ℕ → E ↦ ξ n) ⁻¹' Bᶜ))
      exact
        (measurable_pi_apply n)
          (by simpa using (MeasurableSet.of_discrete : MeasurableSet B))

/-- Helper for Theorem 19.33: on path space, hitting `insert b A` first at the distinguished
state `b` means reaching `b` after avoiding the whole boundary beforehand. -/
private def firstHitPathEvent
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (A : Set E) (b : E) : Set (ℕ → E) :=
  {ξ | ∃ n : ℕ, ξ n = b ∧ ∀ m < n, ξ m ∉ insert b A}

/-- Helper for Theorem 19.33: the path-space first-hit event for `b` before `A` is measurable. -/
private theorem firstHitPathEvent_measurable
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (A : Set E) (b : E) :
    MeasurableSet (firstHitPathEvent A b) := by
  have hEq :
      firstHitPathEvent A b =
        ⋃ n : ℕ,
          ({ξ : ℕ → E | ξ n = b} ∩ {ξ : ℕ → E | ∀ m < n, ξ m ∉ insert b A}) := by
    ext ξ
    simp [firstHitPathEvent]
  rw [hEq]
  refine MeasurableSet.iUnion fun n ↦ ?_
  refine
    (show MeasurableSet {ξ : ℕ → E | ξ n = b} from by
      change MeasurableSet (((fun ξ : ℕ → E ↦ ξ n) ⁻¹' ({b} : Set E)))
      exact (measurable_pi_apply n) (MeasurableSet.singleton b)).inter ?_
  exact avoidBeforePathEvent_measurable (insert b A) n

/-- Helper for Theorem 19.33: the first-hit event at `b` is equivalent to an explicit witness
time where the path first reaches `b` while avoiding the whole boundary earlier. -/
private theorem firstHitEvent_iff_exists
    {E Ω' : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableSpace Ω']
    (u : ℕ → Ω' → E) (A : Set E) (b : E) (ω : Ω') :
    (hittingAfter u (insert b A) 0 ω < ⊤ ∧
        stoppedValue u (hittingAfter u (insert b A) 0) ω = b) ↔
      ∃ n : ℕ, u n ω = b ∧ ∀ m < n, u m ω ∉ insert b A := by
  let s : Set E := insert b A
  constructor
  · rintro ⟨hfin, hstop⟩
    have hne_top : hittingAfter u s 0 ω ≠ ⊤ := ne_of_lt hfin
    lift hittingAfter u s 0 ω to ℕ using hne_top with n hn
    have hidx : (hittingAfter u s 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hnb : u n ω = b := by
      -- Proof comment: after naming the finite hitting time, the stopped value is exactly the
      -- coordinate `u n ω`, and the event says that value equals `b`.
      change stoppedValue u (hittingAfter u s 0) ω = b at hstop
      rw [stoppedValue, hidx] at hstop
      exact hstop
    refine ⟨n, hnb, ?_⟩
    intro m hm
    have hm_lt_hit : (m : ℕ∞) < hittingAfter u s 0 ω := by
      have hm_top : (m : ℕ∞) < (n : ℕ∞) := by
        simpa using hm
      rw [← hn]
      exact hm_top
    -- Proof comment: every strictly earlier time stays outside the full boundary `insert b A`.
    exact
      notMem_of_lt_hittingAfter (u := u) (s := s) (n := 0) (ω := ω) (k := m) hm_lt_hit
        (by simp)
  · rintro ⟨n, hnb, havoid⟩
    have hhit_le_n :
        hittingAfter u s 0 ω ≤ n :=
      hittingAfter_le_of_mem (u := u) (s := s) (n := 0) (i := n) (ω := ω) (by simp) <| by
        simp [s, hnb]
    have hne_top : hittingAfter u s 0 ω ≠ ⊤ := by
      intro htop
      simpa [htop] using hhit_le_n
    lift hittingAfter u s 0 ω to ℕ using hne_top with t ht
    have hidx : (hittingAfter u s 0 ω).untopA = t := by
      rw [← ht, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have htn : t ≤ n := by
      simpa using hhit_le_n
    have hne_top0 : hittingAfter u s 0 ω ≠ ⊤ := by
      intro htop
      have ht_top : (t : ℕ∞) = ⊤ := ht.trans htop
      simpa using ht_top
    have ht_mem : u t ω ∈ s := by
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := u) (s := s) (n := 0) (ω := ω) hne_top0
    have hnot_lt : ¬ t < n := by
      intro hlt
      exact (havoid t hlt) ht_mem
    have htn_eq : t = n := le_antisymm htn (not_lt.mp hnot_lt)
    have hltop : hittingAfter u s 0 ω < ⊤ := lt_top_iff_ne_top.mpr hne_top0
    refine ⟨hltop, ?_⟩
    -- Proof comment: the first boundary hit cannot occur before the witness time `n`, so the
    -- stopped value is exactly the prescribed state `b`.
    rw [stoppedValue, hidx, htn_eq]
    exact hnb

/-- Helper for Theorem 19.33: evaluating the realized path on the path-space first-hit event
recovers the original `F_A` first-hit event. -/
private theorem path_mem_firstHitPathEvent_iff
    {E Ω' : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableSpace Ω']
    (u : ℕ → Ω' → E) (A : Set E) (b : E) (ω : Ω') :
    (fun n : ℕ ↦ u n ω) ∈ firstHitPathEvent A b ↔
      (hittingAfter u (insert b A) 0 ω < ⊤ ∧
        stoppedValue u (hittingAfter u (insert b A) 0) ω = b) := by
  simpa [firstHitPathEvent, Set.mem_setOf_eq] using
    (firstHitEvent_iff_exists u A b ω).symm

/-- Helper for Theorem 19.33: if the start state already lies outside `insert b A`, then the
first-hit event from time `0` is exactly the first-hit path event of the shifted future path. -/
private theorem futurePath_mem_firstHitPathEvent_iff
    {E Ω' : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableSpace Ω']
    (u : ℕ → Ω' → E) (A : Set E) (b : E) {ω : Ω'}
    (hstart : u 0 ω ∉ insert b A) :
    shiftedFuturePath u 1 ω ∈ firstHitPathEvent A b ↔
      (hittingAfter u (insert b A) 0 ω < ⊤ ∧
        stoppedValue u (hittingAfter u (insert b A) 0) ω = b) := by
  rw [show
      (hittingAfter u (insert b A) 0 ω < ⊤ ∧
        stoppedValue u (hittingAfter u (insert b A) 0) ω = b) ↔
      ∃ n : ℕ, u n ω = b ∧ ∀ m < n, u m ω ∉ insert b A from
        firstHitEvent_iff_exists u A b ω]
  constructor
  · rintro ⟨n, hnb, havoid⟩
    refine ⟨n + 1, ?_, ?_⟩
    · simpa [shiftedFuturePath, Nat.add_comm] using hnb
    · intro m hm
      cases m with
      | zero =>
          simpa using hstart
      | succ m =>
          have hm_lt : m < n := by
            simpa using hm
          simpa [shiftedFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using havoid m hm_lt
  · rintro ⟨n, hnb, havoid⟩
    have hn_ne_zero : n ≠ 0 := by
      intro hn0
      exact hstart <| by simpa [hn0] using Or.inl hnb
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne_zero
    refine ⟨k, ?_, ?_⟩
    · simpa [shiftedFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnb
    · intro m hm
      have hm' : m + 1 < k + 1 := Nat.succ_lt_succ hm
      simpa [shiftedFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using havoid (m + 1) hm'

/-- Helper for Theorem 19.33: under the start law `P y`, the shifted future-path hit indicator
averages against the one-step kernel through the local path-law kernel. -/
private theorem futurePathHit_real_eq_pathKernelAverage
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (B : Set (ℕ → E)) (hB : MeasurableSet B) (y : E) :
    (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B) =
      ∫ z, (realizationPathKernel (P := P) (X := X) z).real B
        ∂((discreteMatrixKernel p) y) := by
  let μ : Measure Ω := (P y : Measure Ω)
  let futureIndicator : Ω → ℝ := fun ω ↦ Set.indicator B (fun _ ↦ (1 : ℝ)) (shiftedFuturePath X 1 ω)
  let rowMass : E → ℝ := fun z ↦
    (realizationPathKernel (P := P) (X := X) z).real B
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hfuture_meas : Measurable futureIndicator := by
    -- Proof comment: compose the measurable path-event indicator with the measurable one-step
    -- shifted future-path map.
    exact (Measurable.indicator measurable_const hB).comp <|
      measurable_shiftedFuturePath X hReal.measurable_process 1
  have hfuture_int : Integrable futureIndicator μ := by
    -- Proof comment: the future-path indicator takes only the values `0` and `1`.
    refine Integrable.of_bound hfuture_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : shiftedFuturePath X 1 ω ∈ B
      · simp [futureIndicator, hω]
      · simp [futureIndicator, hω]
  letI : IsTimeHomogeneousMarkovProcess X P
      (realizationPathKernel (P := P) (X := X)) :=
    realizationPathKernel_isTimeHomogeneousMarkovProcess (p := p) (P := P) (X := X)
  have hgenerated_le :
      generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_localPastPath_comap X 1]
    exact (measurable_localPastPath X hReal.measurable_process 1).comap_le
  have hcondAE :
      MeasureTheory.condExp (m := generatedFiltrationSpace X 1) μ futureIndicator =ᵐ[μ]
        fun ω ↦ rowMass (X 1 ω) := by
    let g : (ℕ → E) → ℝ := fun ξ ↦ Set.indicator B (fun _ ↦ (1 : ℝ)) ξ
    have hg_meas : Measurable g := by
      -- Proof comment: `g` is the measurable indicator of the path event `B`.
      exact Measurable.indicator measurable_const hB
    have hg_bdd : Bornology.IsBounded (Set.range g) := by
      -- Proof comment: an indicator only takes the values `0` and `1`.
      simpa [g] using isBounded_range_indicator_one B
    have hAE :=
      futurePathCondExp_shiftedNat
        (κ := realizationPathKernel (P := P) (X := X))
        (hX_meas := hReal.measurable_process)
        (hX0 := fun z ↦ by
          have hInit := congrArg (fun ν : Measure E ↦ ν ({z} : Set E)) (hReal.initial_eq z)
          simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton z)] using
            hInit)
        (hpath := fun z ↦ realizationPathKernel_apply (P := P) (X := X) z)
        y 1 g hg_meas hg_bdd
    -- Proof comment: specialize the future-path conditional expectation to the indicator of `B`.
    filter_upwards [hAE] with ω hω
    simpa [g, futureIndicator, rowMass, shiftedFuturePath, MeasureTheory.integral_indicator_one, hB]
      using hω
  have hfutureIntegral :
      ∫ ω, futureIndicator ω ∂μ = ∫ ω, rowMass (X 1 ω) ∂μ := by
    -- Proof comment: integrate the conditional-expectation identity over the ambient start law.
    calc
      ∫ ω, futureIndicator ω ∂μ
          = ∫ ω,
              MeasureTheory.condExp (m := generatedFiltrationSpace X 1) μ futureIndicator ω
              ∂μ := by
                symm
                exact integral_condExp hgenerated_le
      _ = ∫ ω, rowMass (X 1 ω) ∂μ := by
            exact integral_congr_ae hcondAE
  have htransitionIntegral :
      ∫ ω, rowMass (X 1 ω) ∂μ = ∫ z, rowMass z ∂((discreteMatrixKernel p) y) := by
    -- Proof comment: the time-`1` marginal of the realization is the one-step transition row.
    calc
      ∫ ω, rowMass (X 1 ω) ∂μ = ∫ z, rowMass z ∂((P y : Measure Ω).map (X 1)) := by
            simpa [μ] using
              (MeasureTheory.integral_map
                (μ := (P y : Measure Ω))
                (φ := X 1)
                (f := rowMass)
                (hReal.measurable_process 1).aemeasurable
                (Measurable.of_discrete.aestronglyMeasurable)).symm
      _ = ∫ z, rowMass z ∂((discreteMatrixKernel p ^ 1) y) := by
            rw [hReal.transition_eq y 1]
      _ = ∫ z, rowMass z ∂((discreteMatrixKernel p) y) := by
            simp
  -- Proof comment: rewrite the shifted-path mass as an indicator integral, then pass it through
  -- the conditional-expectation bridge and the time-`1` marginal identity.
  calc
    (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B)
        = ∫ ω, futureIndicator ω ∂μ := by
            symm
            simpa [μ, futureIndicator] using
              (MeasureTheory.integral_indicator_one
                (μ := μ)
                (s := (shiftedFuturePath X 1) ⁻¹' B)
                ((measurable_shiftedFuturePath X hReal.measurable_process 1) hB))
    _ = ∫ ω, rowMass (X 1 ω) ∂μ := hfutureIntegral
    _ = ∫ z, rowMass z ∂((discreteMatrixKernel p) y) := htransitionIntegral

/-- Helper for Theorem 19.33: every path-kernel row mass of the first-hit path event is exactly
the corresponding first-hit probability `F_A`. -/
private theorem realizationPathKernel_real_firstHitPathEvent_eq_F_A
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) (b z : E) :
    (realizationPathKernel (P := P) (X := X) z).real (firstHitPathEvent A b) =
      F_A P X A z b := by
  let path : Ω → ℕ → E := fun ω n ↦ X n ω
  have hpath_meas : Measurable path := by
    -- Proof comment: the full realized path map is measurable coordinatewise.
    refine measurable_pi_lambda _ fun n ↦ ?_
    let hReal :
        IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
    exact hReal.measurable_process n
  have hpreimage :
      path ⁻¹' firstHitPathEvent A b =
        {ω |
          hittingAfter X (insert b A) 0 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert b A) 0) ω = b} := by
    ext ω
    -- Proof comment: pulling the path-space event back along the realized path recovers the
    -- source-side first-hit event at time `0`.
    simpa [path] using (path_mem_firstHitPathEvent_iff X A b ω)
  calc
    (realizationPathKernel (P := P) (X := X) z).real (firstHitPathEvent A b)
        = (((P z : Measure Ω).map path).real (firstHitPathEvent A b)) := by
            rfl
    _ = (P z : Measure Ω).real (path ⁻¹' firstHitPathEvent A b) := by
          simpa using
            (MeasureTheory.map_measureReal_apply hpath_meas
              (firstHitPathEvent_measurable A b))
    _ = (P z : Measure Ω).real
          {ω | hittingAfter X (insert b A) 0 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert b A) 0) ω = b} := by
          rw [hpreimage]
    _ = F_A P X A z b := by
          rfl

/-- Helper for Theorem 19.33: away from the boundary `insert b A`, the first-hit probability
surface `z ↦ F_A P X A z b` is the one-step average of its future values. -/
private theorem F_A_average_eq_outside_insert_boundary
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {A : Set E} {b y : E} (hy : y ∉ insert b A) :
    F_A P X A y b =
      ∫ z, F_A P X A z b ∂((discreteMatrixKernel p) y) := by
  let μ : Measure Ω := (P y : Measure Ω)
  let B : Set (ℕ → E) := firstHitPathEvent A b
  have hB : MeasurableSet B := firstHitPathEvent_measurable A b
  have hEventAE :
      {ω | hittingAfter X (insert b A) 0 ω < ⊤ ∧
          stoppedValue X (hittingAfter X (insert b A) 0) ω = b} =ᵐ[μ]
        ((shiftedFuturePath X 1) ⁻¹' B) := by
    have hstart : ∀ᵐ ω ∂μ, X 0 ω = y :=
      initialState_ae_eq_start_local (p := p) (P := P) (X := X) y
    filter_upwards [hstart] with ω hω
    have hstart_out : X 0 ω ∉ insert b A := by
      simpa [hω] using hy
    -- Proof comment: away from the boundary, the time-`0` first-hit event is the one-step
    -- future-path first-hit event.
    exact propext <| (futurePath_mem_firstHitPathEvent_iff (u := X) A b hstart_out).symm
  calc
    F_A P X A y b
        = μ.real ((shiftedFuturePath X 1) ⁻¹' B) := by
            calc
              F_A P X A y b
                  = μ.real
                      {ω |
                        hittingAfter X (insert b A) 0 ω < ⊤ ∧
                          stoppedValue X (hittingAfter X (insert b A) 0) ω = b} := by
                            rfl
              _ = μ.real ((shiftedFuturePath X 1) ⁻¹' B) := by
                    exact MeasureTheory.measureReal_congr hEventAE
    _ = ∫ z, (realizationPathKernel (P := P) (X := X) z).real B
          ∂((discreteMatrixKernel p) y) := by
            simpa [μ] using
              futurePathHit_real_eq_pathKernelAverage (p := p) (P := P) (X := X) B hB y
    _ = ∫ z, F_A P X A z b ∂((discreteMatrixKernel p) y) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
          change
            (realizationPathKernel (P := P) (X := X) z).real (firstHitPathEvent A b) =
              F_A P X A z b
          exact realizationPathKernel_real_firstHitPathEvent_eq_F_A
            (p := p) (P := P) (X := X) A b z

/-- Helper for Theorem 19.33: on the boundary `insert b A`, the first-hit surface `F_A` already
has the boundary datum `1` at `b` and `0` on `A`. -/
private theorem F_A_eq_boundaryDatum_on_insert_boundary
    {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {A : Set E} {b x : E} (hx : x ∈ insert b A) :
    F_A P X A x b = if x = b then (1 : ℝ) else 0 := by
  by_cases hxb : x = b
  · subst hxb
    let μ : Measure Ω := (P x : Measure Ω)
    let S : Set Ω := {ω | X 0 ω = x}
    have hStart : μ S = 1 := by
      have hS_meas : MeasurableSet S := by
        let hReal :
            IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
          inferInstance
        simpa [S, Set.preimage] using hReal.measurable_process 0 (measurableSet_singleton x)
      exact (mem_ae_iff_prob_eq_one hS_meas).1 <| by
        simpa [S] using (initialState_ae_eq_start_local (p := p) (P := P) (X := X) x)
    have hSubset :
        S ⊆ {ω | hittingAfter X (insert x A) 0 ω < ⊤ ∧
          stoppedValue X (hittingAfter X (insert x A) 0) ω = x} := by
      intro ω hω
      have hτ0 : hittingAfter X (insert x A) 0 ω = 0 := by
        refine le_antisymm ?_ (le_hittingAfter (u := X) (s := insert x A) (n := 0) ω)
        have hmem : X 0 ω ∈ insert x A := by
          left
          simpa [S] using hω
        exact hittingAfter_le_of_mem (u := X) (s := insert x A) (n := 0) (ω := ω) (by simp) hmem
      have hstop :
          stoppedValue X (hittingAfter X (insert x A) 0) ω = X 0 ω := by
        simp [stoppedValue, hτ0]
      constructor
      · simpa [hτ0]
      · simpa [hτ0] using hstop.trans hω
    have hEvent :
        μ {ω | hittingAfter X (insert x A) 0 ω < ⊤ ∧
          stoppedValue X (hittingAfter X (insert x A) 0) ω = x} = 1 := by
      refine le_antisymm ?_ ?_
      · calc
          μ {ω | hittingAfter X (insert x A) 0 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert x A) 0) ω = x} ≤ μ Set.univ := by
              exact measure_mono (by intro ω hω; simp)
          _ = 1 := by simp [μ]
      · calc
          1 = μ S := hStart.symm
          _ ≤ μ {ω | hittingAfter X (insert x A) 0 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert x A) 0) ω = x} := measure_mono hSubset
    -- Proof comment: starting at `b` forces the first boundary hit to occur immediately at `b`.
    simpa [F_A, Measure.real_def, μ] using congrArg ENNReal.toReal hEvent
  · have hxA : x ∈ A := by
      rcases hx with rfl | hxA
      · exact False.elim (hxb rfl)
      · exact hxA
    let μ : Measure Ω := (P x : Measure Ω)
    let S : Set Ω := {ω | X 0 ω = x}
    have hSubset :
        {ω | hittingAfter X (insert b A) 0 ω < ⊤ ∧
          stoppedValue X (hittingAfter X (insert b A) 0) ω = b} ⊆ Sᶜ := by
      intro ω hω
      simp only [Set.mem_compl_iff, S]
      intro hSω
      have hτ0 : hittingAfter X (insert b A) 0 ω = 0 := by
        refine le_antisymm ?_ (le_hittingAfter (u := X) (s := insert b A) (n := 0) ω)
        have hmem : X 0 ω ∈ insert b A := by
          rw [hSω]
          exact Or.inr hxA
        exact hittingAfter_le_of_mem (u := X) (s := insert b A) (n := 0) (ω := ω) (by simp) hmem
      have hstop :
          stoppedValue X (hittingAfter X (insert b A) 0) ω = x := by
        calc
          stoppedValue X (hittingAfter X (insert b A) 0) ω = X 0 ω := by
            simp [stoppedValue, hτ0]
          _ = x := hSω
      exact hxb (hstop.symm.trans hω.2)
    have hS_meas : MeasurableSet S := by
      let hReal :
          IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
        inferInstance
      simpa [S, Set.preimage] using hReal.measurable_process 0 (measurableSet_singleton x)
    have hStart : μ S = 1 := by
      exact (mem_ae_iff_prob_eq_one hS_meas).1 <| by
        simpa [S] using (initialState_ae_eq_start_local (p := p) (P := P) (X := X) x)
    have hSComplZero : μ Sᶜ = 0 := by
      rw [measure_compl hS_meas (by rw [hStart]; simp), hStart]
      norm_num
    have hEventZero :
        μ {ω | hittingAfter X (insert b A) 0 ω < ⊤ ∧
          stoppedValue X (hittingAfter X (insert b A) 0) ω = b} = 0 := by
      exact measure_mono_null hSubset hSComplZero
    -- Proof comment: starting from `x ∈ A` with `x ≠ b`, the boundary is already hit at time
    -- `0` at the wrong point, so the first-hit event at `b` is null.
    simpa [F_A, Measure.real_def, μ, hxb] using congrArg ENNReal.toReal hEventZero

/-- Helper for Theorem 19.33: the first-hit probability surface `F_A(·, b)` solves the Dirichlet
problem on the boundary `insert b A` with datum `1` at `b` and `0` on `A`. -/
private theorem F_A_solvesDirichletProblem_of_insert_boundary
    {E : Type*} [Countable E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (A : Set E) (b : E) :
    SolvesDirichletProblem (discreteMatrixKernel p) (insert b A)
      (fun z ↦ if z = b then (1 : ℝ) else 0)
      (fun z ↦ F_A P X A z b) := by
  rw [solvesDirichletProblem_iff]
  constructor
  · intro z hz
    refine ⟨?_, ?_⟩
    · -- Proof comment: the first-hit probability surface is bounded by `1`, hence integrable
      -- against every stochastic row.
      let hReal :
          IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
      have hrow :
          (discreteMatrixKernel p) z = (P z : Measure Ω).map (X 1) := by
        simpa using (hReal.transition_eq z 1).symm
      haveI : IsFiniteMeasure ((discreteMatrixKernel p) z) := by
        rw [hrow]
        infer_instance
      refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1 ?_
      exact Filter.Eventually.of_forall fun w ↦ by
        have hnonneg : 0 ≤ F_A P X A w b := by
          rw [F_A]
          exact ENNReal.toReal_nonneg
        have hle :
            F_A P X A w b ≤ 1 := by
          rw [F_A]
          exact MeasureTheory.measureReal_le_one
            (μ := (P w : Measure Ω))
            (s := {ω | hittingAfter X (insert b A) 0 ω < ⊤ ∧
              stoppedValue X (hittingAfter X (insert b A) 0) ω = b})
        simpa [Real.norm_of_nonneg hnonneg] using hle
    · -- Proof comment: outside the boundary, `F_A` is already the one-step average of its future
      -- values by the path-space restart lemma proved above.
      simpa using
        F_A_average_eq_outside_insert_boundary
          (P := P) (X := X) (p := p) (A := A) (b := b) hz
  · intro z hz
    -- Proof comment: on the boundary, `F_A` matches the prescribed datum by construction.
    simpa using
      F_A_eq_boundaryDatum_on_insert_boundary
        (P := P) (X := X) (p := p) (A := A) (b := b) (x := z) hz

/-- Helper for Theorem 19.33: the cofinite two-ray boundary used to approximate infinity from the
origin. -/
private def randomEnvironmentTwoRayBoundary (N : ℕ) : Set ℤ :=
  Set.Iic (-((N + 1 : ℕ) : ℤ)) ∪ Set.Ici (((N + 1 : ℕ) : ℤ))

/-- Helper for Theorem 19.33: the two-ray boundaries shrink monotonically as the cutoff grows. -/
private theorem randomEnvironmentTwoRayBoundary_antitone :
    Antitone randomEnvironmentTwoRayBoundary := by
  intro M N hMN x hx
  rcases hx with hx | hx
  · -- Proof comment: the left boundary moves further left when the cutoff increases.
    left
    have hbound : (-((N + 1 : ℕ) : ℤ)) ≤ -((M + 1 : ℕ) : ℤ) := by
      omega
    exact le_trans hx hbound
  · -- Proof comment: the right boundary moves further right when the cutoff increases.
    right
    have hbound : (((M + 1 : ℕ) : ℤ)) ≤ ((N + 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.succ_le_succ hMN
    exact le_trans hbound hx

/-- Helper for Theorem 19.33: each two-ray boundary has finite complement. -/
private theorem randomEnvironmentTwoRayBoundary_compl_finite (N : ℕ) :
    (randomEnvironmentTwoRayBoundary N)ᶜ.Finite := by
  -- Proof comment: outside the two rays, only the finite interval
  -- `(-(N + 1), N + 1)` remains.
  have hcompl :
      (randomEnvironmentTwoRayBoundary N)ᶜ =
        Set.Ioo (-((N + 1 : ℕ) : ℤ)) (((N + 1 : ℕ) : ℤ)) := by
    ext x
    simp [randomEnvironmentTwoRayBoundary]
  rw [hcompl]
  simpa using
    (Set.finite_Ioo (-((N + 1 : ℕ) : ℤ)) (((N + 1 : ℕ) : ℤ)))

/-- Helper for Theorem 19.33: the base point `0` lies outside every two-ray boundary. -/
private theorem zero_not_mem_randomEnvironmentTwoRayBoundary (N : ℕ) :
    (0 : ℤ) ∉ randomEnvironmentTwoRayBoundary N := by
  -- Proof comment: the boundary starts at `±(N + 1)`, so it never contains `0`.
  simp [randomEnvironmentTwoRayBoundary]
  omega

/-- Helper for Theorem 19.33: the cofinite two-ray boundaries decrease to the empty set. -/
private theorem randomEnvironmentTwoRayBoundary_decreasesTo_empty :
    Set.DecreasesTo randomEnvironmentTwoRayBoundary (∅ : Set ℤ) := by
  refine ⟨randomEnvironmentTwoRayBoundary_antitone, ?_⟩
  ext x
  constructor
  · intro hx
    -- Proof comment: choosing the cutoff `N = |x|` traps `x` strictly inside the interval
    -- `(-(|x| + 1), |x| + 1)`, so `x` cannot lie in every two-ray boundary.
    have hxAbs : x ∈ randomEnvironmentTwoRayBoundary (Int.natAbs x) :=
      Set.mem_iInter.mp hx (Int.natAbs x)
    simp [randomEnvironmentTwoRayBoundary] at hxAbs
    rcases hxAbs with hxAbs | hxAbs
    · have hlower : -((Int.natAbs x : ℤ)) ≤ x := by
        simpa [Int.natCast_natAbs] using (neg_abs_le x)
      have hxAbs' : x + (Int.natAbs x : ℤ) ≤ -1 := by
        simpa [Int.natCast_natAbs] using hxAbs
      omega
    · have hupper : x ≤ (Int.natAbs x : ℤ) := by
        simpa [Int.natCast_natAbs] using (le_abs_self x)
      have hxAbs' : (Int.natAbs x : ℤ) + 1 ≤ x := by
        simpa [Int.natCast_natAbs] using hxAbs
      omega
  · intro hx
    simp at hx

/-- Helper for Theorem 19.33: the electrical route rewrites effective conductance to infinity as
the `iInf` of the finite-boundary conductances over the symmetric two-ray exhaustion. -/
private theorem randomEnvironment_effectiveConductanceToInfinity_eq_iInf_escapeToTwoRayBoundary
    (hW : W.IsElliptic) :
    effectiveConductanceToInfinity (randomEnvironmentConductance W) P X 0 =
      conductance (randomEnvironmentConductance W) 0 *
        ⨅ N : ℕ, escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N) := by
  have hlimit_eff :
      Tendsto
          (fun N ↦
            conductance (randomEnvironmentConductance W) 0 *
              escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N))
          atTop
          (nhds (effectiveConductanceToInfinity (randomEnvironmentConductance W) P X 0)) := by
    -- Proof comment: Lemma 19.24 applies directly to the cofinite two-ray exhaustion.
    exact
      effectiveConductanceToInfinity_tendsto_of_decreasing_finite_complement
        (C := randomEnvironmentConductance W) (P := P) (X := X) (x₁ := 0)
        randomEnvironmentTwoRayBoundary_decreasesTo_empty
        randomEnvironmentTwoRayBoundary_compl_finite
        zero_not_mem_randomEnvironmentTwoRayBoundary
        (randomEnvironmentConductance_vertexWeight_lt_top (W := W) hW 0)
  have hanti :
      Antitone (fun N ↦ escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N)) := by
    intro m n hmn
    exact escapeToSetProbability_mono P X 0 (randomEnvironmentTwoRayBoundary_antitone hmn)
  have hlimit_iInf :
      Tendsto
          (fun N ↦
            conductance (randomEnvironmentConductance W) 0 *
              escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N))
          atTop
          (nhds
            (conductance (randomEnvironmentConductance W) 0 *
              ⨅ N : ℕ, escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N))) := by
    -- Proof comment: the escape probabilities decrease with the boundary, so their finite-
    -- boundary conductances converge to the corresponding `iInf`.
    exact
      ENNReal.Tendsto.const_mul
        (tendsto_atTop_iInf hanti)
        (Or.inr (randomEnvironmentConductance_vertexWeight_lt_top (W := W) hW 0).ne)
  -- Proof comment: both descriptions are limits of the same monotone two-ray exhaustion.
  exact tendsto_nhds_unique hlimit_eff hlimit_iInf

/-- Helper for Theorem 19.33: a nonrecurrent state is transient because its return probability is
strictly smaller than `1`. -/
private theorem randomEnvironment_isTransientState_of_not_isRecurrentState
    {x : ℤ} (hx : ¬ IsRecurrentState P X x) :
    IsTransientState P X x := by
  have hxx_le_one : (F[P, X]) x x ≤ 1 := by
    rw [everHitsProbability_def]
    exact measureReal_le_one
  -- Proof comment: the return probability is always at most `1`, so failure of recurrence forces
  -- strict inequality.
  rw [IsTransientState]
  by_contra hnot_transient
  have hxx_ge_one : 1 ≤ (F[P, X]) x x := le_of_not_gt hnot_transient
  have hxx_eq_one : (F[P, X]) x x = 1 := le_antisymm hxx_le_one hxx_ge_one
  exact hx <| by simpa [IsRecurrentState] using hxx_eq_one

/-- Helper for Theorem 19.33: in the elliptic RWRE on `ℤ`, recurrence of one state forces
recurrence of every state, and failure at `0` forces transience everywhere. -/
private theorem randomEnvironment_recurrent_or_allStatesTransient
    (hW : W.IsElliptic) :
    IsRecurrentMarkovChain P X ∨ ∀ k : ℤ, IsTransientState P X k := by
  by_cases hrec0 : IsRecurrentState P X 0
  · left
    intro k
    -- Proof comment: recurrence at `0` propagates to every other state through the positive
    -- communication probabilities supplied by the monotone-path helper.
    exact
      isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
        (κ := fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n)
        (P := P) (X := X) hrec0
        (randomEnvironmentEverHitsProbability_pos (W := W) (P := P) (X := X) hW 0 k)
  · right
    intro k
    -- Proof comment: if some `k` were recurrent, the same positive communication helper would
    -- transport that recurrence back to `0`, contradicting the nonrecurrent branch assumption.
    apply randomEnvironment_isTransientState_of_not_isRecurrentState (P := P) (X := X)
    intro hk
    exact hrec0 <|
      isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
        (κ := fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n)
        (P := P) (X := X) hk
        (randomEnvironmentEverHitsProbability_pos (W := W) (P := P) (X := X) hW k 0)

/-- Helper for Theorem 19.33: if at least one Solomon series is finite, then the parallel
resistance expression `((R_w^-)⁻¹ + (R_w^+)⁻¹)⁻¹` is finite. -/
private theorem randomEnvironment_parallelResistance_lt_top_of_oneSeries_lt_top
    (hW : W.IsElliptic) (hfinite : R⁻[W] < ∞ ∨ R⁺[W] < ∞) :
    ((R⁻[W])⁻¹ + (R⁺[W])⁻¹)⁻¹ < ∞ := by
  rcases hfinite with hleft | hright
  · -- Proof comment: a finite left series makes its reciprocal strictly positive, so the sum of
    -- reciprocal branch conductances is positive and its inverse is finite.
    have hsum_pos : 0 < (R⁻[W])⁻¹ + (R⁺[W])⁻¹ := by
      exact lt_of_lt_of_le ((ENNReal.inv_pos).2 hleft.ne)
        (le_add_of_nonneg_right (zero_le _))
    rw [lt_top_iff_ne_top]
    exact (ENNReal.inv_ne_top).2 (ne_of_gt hsum_pos)
  · -- Proof comment: the same argument applies when the right series is the finite branch.
    have hsum_pos : 0 < (R⁻[W])⁻¹ + (R⁺[W])⁻¹ := by
      exact lt_of_lt_of_le ((ENNReal.inv_pos).2 hright.ne)
        (le_add_of_nonneg_left (zero_le _))
    rw [lt_top_iff_ne_top]
    exact (ENNReal.inv_ne_top).2 (ne_of_gt hsum_pos)

/-- Helper for Theorem 19.33: a nearest-neighbor integer path started at `1` that avoids `0` at
all positive times stays strictly positive forever. -/
private theorem integerPath_pos_of_startOne_and_no_zero
    (Y : ℕ → ℤ) (hstart : Y 0 = 1)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1)
    (hnozero : ∀ n : ℕ, 0 < n → Y n ≠ 0) :
    ∀ n : ℕ, 0 < Y n := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial state is fixed to `1`.
      simpa [hstart]
  | succ n ih =>
      -- Proof comment: a positive nearest-neighbor step can only cross to the nonpositive side
      -- through `0`, which is excluded by the no-hit hypothesis.
      rcases hstep n with hright | hleft
      · omega
      · have hnonzero : Y (n + 1) ≠ 0 := hnozero (n + 1) (Nat.succ_pos _)
        omega

/-- Helper for Theorem 19.33: a nearest-neighbor integer path started at `-1` that avoids `0` at
all positive times stays strictly negative forever. -/
private theorem integerPath_neg_of_startNegOne_and_no_zero
    (Y : ℕ → ℤ) (hstart : Y 0 = -1)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1)
    (hnozero : ∀ n : ℕ, 0 < n → Y n ≠ 0) :
    ∀ n : ℕ, Y n < 0 := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial state is fixed to `-1`.
      simpa [hstart]
  | succ n ih =>
      -- Proof comment: a negative nearest-neighbor step can only cross to the nonnegative side
      -- through `0`, which is excluded by the no-hit hypothesis.
      rcases hstep n with hright | hleft
      · have hnonzero : Y (n + 1) ≠ 0 := hnozero (n + 1) (Nat.succ_pos _)
        omega
      · omega

/-- Helper for Theorem 19.33: under the RWRE realization, every increment is almost surely one of
the two nearest-neighbor steps `+1` or `-1`. -/
theorem randomEnvironmentWalk_ae_nearestNeighbor
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (x : ℤ) :
    ∀ᵐ ω ∂(P x : Measure Ω),
      ∀ n : ℕ, X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω = X n ω - 1 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  rw [ae_all_iff]
  intro n
  let bad : Set Ω := {ω | ¬ (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω = X n ω - 1)}
  let badFiber : ℤ → ℤ → Set Ω := fun y z ↦
    if z = y + 1 ∨ z = y - 1 then
      ∅
    else
      {ω | X n ω = y ∧ X (n + 1) ω = z}
  have hbad_union :
      bad = ⋃ y : ℤ, ⋃ z : ℤ, badFiber y z := by
    ext ω
    constructor
    · intro hω
      refine Set.mem_iUnion.2 ⟨X n ω, ?_⟩
      refine Set.mem_iUnion.2 ⟨X (n + 1) ω, ?_⟩
      have hnot_adj :
          ¬ (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω = X n ω - 1) := hω
      simp [badFiber, hnot_adj, hω]
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨y, hy⟩
      rcases Set.mem_iUnion.1 hy with ⟨z, hz⟩
      by_cases hadj : z = y + 1 ∨ z = y - 1
      · simp [badFiber, hadj] at hz
      · have hz' : X n ω = y ∧ X (n + 1) ω = z := by
            simpa [badFiber, hadj] using hz
        have hyz_right : z ≠ y + 1 := by
          intro hEq
          exact hadj (Or.inl hEq)
        have hyz_left : z ≠ y - 1 := by
          intro hEq
          exact hadj (Or.inr hEq)
        simp [bad, hz'.1, hz'.2, hyz_right, hyz_left]
  have hbad_meas : MeasurableSet bad := by
    rw [hbad_union]
    refine MeasurableSet.iUnion fun y ↦ ?_
    refine MeasurableSet.iUnion fun z ↦ ?_
    by_cases hadj : z = y + 1 ∨ z = y - 1
    · simp [badFiber, hadj]
    · have hXn :
          MeasurableSet {ω | X n ω = y} := by
        simpa [Set.preimage] using
          hReal.measurable_process n (MeasurableSet.singleton y)
      have hXsucc :
          MeasurableSet {ω | X (n + 1) ω = z} := by
        simpa [Set.preimage] using
          hReal.measurable_process (n + 1) (MeasurableSet.singleton z)
      have hpairMeas :
          MeasurableSet {ω | X n ω = y ∧ X (n + 1) ω = z} := by
        have hpairEq :
            {ω | X n ω = y ∧ X (n + 1) ω = z} =
              ({ω | X n ω = y} ∩ {ω | X (n + 1) ω = z}) := by
          ext ω
          simp
        rw [hpairEq]
        exact hXn.inter hXsucc
      simpa [badFiber, hadj] using hpairMeas
  have hbad_zero :
      (P x : Measure Ω) bad = 0 := by
    rw [hbad_union]
    have hbad_le_zero :
        (P x : Measure Ω) (⋃ y : ℤ, ⋃ z : ℤ, badFiber y z) ≤ 0 := by
      calc
      (P x : Measure Ω) (⋃ y : ℤ, ⋃ z : ℤ, badFiber y z)
          ≤ ∑' y : ℤ, (P x : Measure Ω) (⋃ z : ℤ, badFiber y z) := by
            simpa using
              (measure_iUnion_le (μ := (P x : Measure Ω))
                (s := fun y : ℤ ↦ ⋃ z : ℤ, badFiber y z))
      _ ≤ ∑' y : ℤ, ∑' z : ℤ, (P x : Measure Ω) (badFiber y z) := by
            refine ENNReal.tsum_le_tsum ?_
            intro y
            simpa using
              (measure_iUnion_le (μ := (P x : Measure Ω))
                (s := fun z : ℤ ↦ badFiber y z))
      _ = ∑' y : ℤ, ∑' z : ℤ, 0 := by
            refine tsum_congr ?_
            intro y
            refine tsum_congr ?_
            intro z
            by_cases hadj : z = y + 1 ∨ z = y - 1
            · simp [badFiber, hadj]
            · have hpair :
                (P x : Measure Ω) {ω | X n ω = y ∧ X (n + 1) ω = z} =
                  randomEnvironmentTransitionMatrix W y z *
                    (P x : Measure Ω) (X n ⁻¹' ({y} : Set ℤ)) := by
                  simpa using randomWalkInRandomEnvironment_transition
                    (W := W) (P := P) (X := X) x n y z
              have hmatrix : randomEnvironmentTransitionMatrix W y z = 0 := by
                have hyz_right : z ≠ y + 1 := by
                  intro hEq
                  exact hadj (Or.inl hEq)
                have hyz_left : z ≠ y - 1 := by
                  intro hEq
                  exact hadj (Or.inr hEq)
                simp [randomEnvironmentTransitionMatrix, hyz_right, hyz_left]
              simp [badFiber, hadj, hpair, hmatrix]
      _ = 0 := by simp
    exact le_antisymm hbad_le_zero bot_le
  have hbad_ae : badᶜ ∈ ae (P x : Measure Ω) := compl_mem_ae_iff.2 hbad_zero
  classical
  filter_upwards [hbad_ae] with ω hω
  have hω' :
      ¬¬ (X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω = X n ω - 1) := by
    simpa [bad] using hω
  exact not_not.mp hω'

/-- Helper for Theorem 19.33: from the start state `1`, avoiding `0` at all positive times forces
the RWRE path to stay on the positive half-line almost surely. -/
theorem randomEnvironmentWalk_ae_pos_of_startOne_and_no_hit_zero
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X] :
    ∀ᵐ ω ∂(P 1 : Measure Ω),
      (∀ n : ℕ, 0 < n → X n ω ≠ 0) → ∀ n : ℕ, 0 < X n ω := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hstart :
      ∀ᵐ ω ∂(P 1 : Measure Ω), X 0 ω = 1 := by
    refine (mem_ae_iff_prob_eq_one ?_).2 ?_
    · simpa [Set.preimage] using
        hReal.measurable_process 0 (MeasurableSet.singleton 1)
    · simpa using randomWalkInRandomEnvironment_start (W := W) (P := P) (X := X) (x := 1)
  have hstep := randomEnvironmentWalk_ae_nearestNeighbor (W := W) (P := P) (X := X) (x := 1)
  filter_upwards [hstart, hstep] with ω hstartω hstepω hnozero
  exact integerPath_pos_of_startOne_and_no_zero (fun n ↦ X n ω) hstartω hstepω hnozero

/-- Helper for Theorem 19.33: from the start state `-1`, avoiding `0` at all positive times
forces the RWRE path to stay on the negative half-line almost surely. -/
theorem randomEnvironmentWalk_ae_neg_of_startNegOne_and_no_hit_zero
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X] :
    ∀ᵐ ω ∂(P (-1) : Measure Ω),
      (∀ n : ℕ, 0 < n → X n ω ≠ 0) → ∀ n : ℕ, X n ω < 0 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hstart :
      ∀ᵐ ω ∂(P (-1) : Measure Ω), X 0 ω = -1 := by
    refine (mem_ae_iff_prob_eq_one ?_).2 ?_
    · simpa [Set.preimage] using
        hReal.measurable_process 0 (MeasurableSet.singleton (-1))
    · simpa using randomWalkInRandomEnvironment_start (W := W) (P := P) (X := X) (x := (-1))
  have hstep := randomEnvironmentWalk_ae_nearestNeighbor (W := W) (P := P) (X := X) (x := (-1))
  filter_upwards [hstart, hstep] with ω hstartω hstepω hnozero
  exact integerPath_neg_of_startNegOne_and_no_zero (fun n ↦ X n ω) hstartω hstepω hnozero

/-- Helper for Theorem 19.33: after transporting the RWRE realization to the conductance walk,
the Chapter 19 escape-probability formula rewrites effective conductance as the row conductance at
`0` times the no-return probability from `0`. -/
private theorem randomEnvironment_effectiveConductanceToInfinity_eq_conductance_mul_escapeProbability
    (hW : W.IsElliptic) :
    effectiveConductanceToInfinity (randomEnvironmentConductance W) P X 0 =
      conductance (randomEnvironmentConductance W) 0 * escapeProbability P X 0 := by
  letI :
      IsRandomWalkWithWeights
        (conductanceTransitionMatrix (randomEnvironmentConductance W))
        (randomEnvironmentConductance W) :=
    randomEnvironmentConductance_isRandomWalkWithWeights (W := W) hW
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (conductanceTransitionMatrix (randomEnvironmentConductance W)) ^ n) P X :=
    isMarkovProcessRealization_randomEnvironmentConductance
      (W := W) (P := P) (X := X) hW
  have hescape :
      escapeProbability P X 0 =
        (conductance (randomEnvironmentConductance W) 0)⁻¹ *
          effectiveConductanceToInfinity (randomEnvironmentConductance W) P X 0 :=
    escapeProbability_eq_conductance_inv_mul_effectiveConductanceToInfinity
      (p := conductanceTransitionMatrix (randomEnvironmentConductance W))
      (C := randomEnvironmentConductance W) (P := P) (X := X) (x₁ := 0)
  have hcond_ne_zero : conductance (randomEnvironmentConductance W) 0 ≠ 0 :=
    ne_of_gt (randomEnvironmentConductance_vertexWeight_pos (W := W) hW 0)
  have hcond_ne_top : conductance (randomEnvironmentConductance W) 0 ≠ ∞ :=
    (randomEnvironmentConductance_vertexWeight_lt_top (W := W) hW 0).ne
  -- Proof comment: cancel the finite nonzero row conductance from the owner escape identity.
  calc
    effectiveConductanceToInfinity (randomEnvironmentConductance W) P X 0 =
        (conductance (randomEnvironmentConductance W) 0 *
            (conductance (randomEnvironmentConductance W) 0)⁻¹) *
          effectiveConductanceToInfinity (randomEnvironmentConductance W) P X 0 := by
          rw [ENNReal.mul_inv_cancel hcond_ne_zero hcond_ne_top, one_mul]
    _ = conductance (randomEnvironmentConductance W) 0 *
          ((conductance (randomEnvironmentConductance W) 0)⁻¹ *
            effectiveConductanceToInfinity (randomEnvironmentConductance W) P X 0) := by
          rw [mul_assoc]
    _ = conductance (randomEnvironmentConductance W) 0 * escapeProbability P X 0 := by
          rw [hescape]

/-- Helper for Theorem 19.33: the Chapter 19 escape probability at `0` is the measure of the
positive-time no-return event. -/
private theorem randomEnvironment_escapeProbability_eq_prob_no_return_zero
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X] :
    escapeProbability P X 0 =
      (P 0 : Measure Ω) {ω | ∀ n : ℕ, 0 < n → X n ω ≠ 0} := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  -- Proof comment: this is exactly Definition 19.23 specialized to the RWRE realization at `0`.
  exact escapeProbability_eq_prob_no_return P X 0 (fun n ↦ hReal.measurable_process n)

/-- Helper for Theorem 19.33: under `P 0`, the no-return event splits almost surely according to
whether the first step from `0` is to `1` or to `-1`. -/
private theorem randomEnvironment_noReturnAtZero_ae_eq_firstStepSlices
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X] :
    {ω | ∀ n : ℕ, 0 < n → X n ω ≠ 0} =ᵐ[(P 0 : Measure Ω)]
      ((({ω | X 1 ω = 1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0} : Set Ω) ∪
        {ω | X 1 ω = -1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0}) : Set Ω) := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hstart :
      ∀ᵐ ω ∂(P 0 : Measure Ω), X 0 ω = 0 := by
    refine (mem_ae_iff_prob_eq_one ?_).2 ?_
    · simpa [Set.preimage] using
        hReal.measurable_process 0 (MeasurableSet.singleton 0)
    · simpa using randomWalkInRandomEnvironment_start (W := W) (P := P) (X := X) (x := 0)
  have hstep := randomEnvironmentWalk_ae_nearestNeighbor (W := W) (P := P) (X := X) (x := 0)
  filter_upwards [hstart, hstep] with ω hstartω hstepω
  apply propext
  change
    ((∀ n : ℕ, 0 < n → X n ω ≠ 0) ↔
      ((X 1 ω = 1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0) ∨
        (X 1 ω = -1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0)))
  constructor
  · intro hω
    have hfirst : X 1 ω = 1 ∨ X 1 ω = -1 := by
      simpa [hstartω] using hstepω 0
    rcases hfirst with hfirst | hfirst
    · left
      constructor
      · exact hfirst
      · intro n hn
        exact hω n (lt_trans (by decide : 0 < 1) hn)
    · right
      constructor
      · exact hfirst
      · intro n hn
        exact hω n (lt_trans (by decide : 0 < 1) hn)
  · intro hω n hn
    rcases hω with hω | hω
    · by_cases hEq : n = 1
      · subst hEq
        simpa [hω.1]
      · have hgt : 1 < n := by omega
        exact hω.2 n hgt
    · by_cases hEq : n = 1
      · subst hEq
        simpa [hω.1]
      · have hgt : 1 < n := by omega
        exact hω.2 n hgt

/-- Helper for Theorem 19.33: rewriting the escape probability through the no-return event and
then splitting by the first step isolates the two half-line continuation probabilities. -/
private theorem randomEnvironment_escapeProbability_eq_firstStepSliceMeasure
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X] :
    escapeProbability P X 0 =
      (P 0 : Measure Ω)
        ((({ω | X 1 ω = 1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0} : Set Ω) ∪
          {ω | X 1 ω = -1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0}) : Set Ω) := by
  rw [randomEnvironment_escapeProbability_eq_prob_no_return_zero (W := W) (P := P) (X := X)]
  -- Proof comment: the only pathwise alternatives after a no-return start from `0` are the two
  -- nearest-neighbor first-step slices.
  exact measure_congr <|
    randomEnvironment_noReturnAtZero_ae_eq_firstStepSlices (W := W) (P := P) (X := X)

/-- Helper for Theorem 19.33: for any cutoff `k`, the future event that the RWRE path never hits
`0` after time `k` is measurable. -/
private theorem randomEnvironment_measurableSet_forall_gt_ne_zero
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (k : ℕ) :
    MeasurableSet {ω | ∀ n : ℕ, k < n → X n ω ≠ 0} := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hHit_eq :
      ({ω | ∃ n : ℕ, k < n ∧ X n ω = 0} : Set Ω) =
        ⋃ n : ℕ, {ω | k < n ∧ X n ω = 0} := by
    ext ω
    simp
  have hHit_meas :
      MeasurableSet ({ω | ∃ n : ℕ, k < n ∧ X n ω = 0} : Set Ω) := by
    rw [hHit_eq]
    refine MeasurableSet.iUnion fun n ↦ ?_
    by_cases hkn : k < n
    · have hEvent_eq :
          ({ω | k < n ∧ X n ω = 0} : Set Ω) = X n ⁻¹' ({0} : Set ℤ) := by
        ext ω
        simp [hkn]
      -- Proof comment: once `n` is beyond the cutoff, the slice is a singleton preimage.
      rw [hEvent_eq]
      simpa [Set.preimage] using
        hReal.measurable_process n (MeasurableSet.singleton (0 : ℤ))
    · have hEvent_eq : ({ω | k < n ∧ X n ω = 0} : Set Ω) = ∅ := by
        ext ω
        simp [hkn]
      -- Proof comment: before the cutoff, the strict-inequality guard makes the slice empty.
      rw [hEvent_eq]
      simp
  have hNoHit_eq :
      ({ω | ∀ n : ℕ, k < n → X n ω ≠ 0} : Set Ω) =
        ({ω | ∃ n : ℕ, k < n ∧ X n ω = 0} : Set Ω)ᶜ := by
    ext ω
    simp
  -- Proof comment: the no-hit event is the complement of the countable union of positive-time
  -- zero-hit slices.
  rw [hNoHit_eq]
  exact hHit_meas.compl

/-- Helper for Theorem 19.33: if a history event up to time `n` pins the current state to `y`,
then intersecting it with a measurable next-step target factors through the one-step RWRE kernel,
first in real event masses. -/
private theorem randomEnvironment_measure_inter_prefix_step_mem_eq_mulReal
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    {x y : ℤ} {A : Set Ω} {n : ℕ} {s : Set ℤ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (hs : MeasurableSet s) :
    (P x : Measure Ω).real {ω | ω ∈ A ∧ X (n + 1) ω ∈ s} =
      (discreteMatrixKernel (randomEnvironmentTransitionMatrix W) y s).toReal *
        (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  let B : Set Ω := X (n + 1) ⁻¹' s
  have hXn_measF : Measurable[generatedFiltrationSpace X n] (X n) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl
  have hA_meas_ambient : MeasurableSet A := by
    exact (generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n) _ hA_meas
  have hB_meas : MeasurableSet B := by
    simpa [B] using hReal.measurable_process (n + 1) hs
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦
          ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) (X n ω)).real s := by
    -- Proof comment: specialize the time-homogeneous Markov property to the one-step measurable
    -- target `s`.
    simpa [μ, B, pow_one, add_comm] using hReal.markov_property x (A := s) hs n 1
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the one-step Markov identity over the history event `A`, then use
  -- that `A` already freezes the present state to `y`.
  calc
    μ.real {ω | ω ∈ A ∧ X (n + 1) ω ∈ s}
        = ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂μ := by
            have hInterEq :
                A ∩ B = {ω | ω ∈ A ∧ X (n + 1) ω ∈ s} := by
              ext ω
              simp [B]
            rw [setIntegral_condExp
              (generatedFiltrationSpace_le_ambient (X := X) hReal.measurable_process n)
              hIndicatorIntegrable hA_meas, ← integral_indicator hA_meas_ambient]
            symm
            rw [← hInterEq]
            simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
              Set.inter_comm, smul_eq_mul] using
              integral_indicator_const (1 : ℝ) (hA_meas_ambient.inter hB_meas)
    _ = ∫ ω in A,
          ((discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) (X n ω)).real s ∂μ := by
          exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, (discreteMatrixKernel (randomEnvironmentTransitionMatrix W) y s).toReal ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict hA_meas_ambient] with ω hω
          have hωy : X n ω = y := hA_sub hω
          rw [hωy]
          simp [Measure.real_def]
    _ = (discreteMatrixKernel (randomEnvironmentTransitionMatrix W) y s).toReal * μ.real A := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Theorem 19.33: if a history event up to time `n` pins the current state to `y`,
then intersecting it with a measurable next-step target factors through the one-step RWRE kernel,
now in `ℝ≥0∞`. -/
private theorem randomEnvironment_measure_inter_prefix_step_mem_eq_mul
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    {x y : ℤ} {A : Set Ω} {n : ℕ} {s : Set ℤ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (hs : MeasurableSet s) :
    (P x : Measure Ω) {ω | ω ∈ A ∧ X (n + 1) ω ∈ s} =
      (discreteMatrixKernel (randomEnvironmentTransitionMatrix W) y s) *
        (P x : Measure Ω) A := by
  have hreal :
      (P x : Measure Ω).real {ω | ω ∈ A ∧ X (n + 1) ω ∈ s} =
        (discreteMatrixKernel (randomEnvironmentTransitionMatrix W) y s).toReal *
          (P x : Measure Ω).real A :=
    randomEnvironment_measure_inter_prefix_step_mem_eq_mulReal
      (W := W) (P := P) (X := X) hA_meas hA_sub hs
  have hleft_ne_top :
      (P x : Measure Ω) {ω | ω ∈ A ∧ X (n + 1) ω ∈ s} ≠ ⊤ :=
    measure_ne_top _ _
  have hkernel_ne_top :
      discreteMatrixKernel (randomEnvironmentTransitionMatrix W) y s ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt prob_le_one ENNReal.one_lt_top)
  have hright_ne_top :
      (discreteMatrixKernel (randomEnvironmentTransitionMatrix W) y s) *
          (P x : Measure Ω) A ≠ ⊤ := by
    exact ENNReal.mul_ne_top hkernel_ne_top (measure_ne_top _ _)
  exact (ENNReal.toReal_eq_toReal_iff' hleft_ne_top hright_ne_top).mp <| by
    simpa [Measure.real_def, ENNReal.toReal_mul, hkernel_ne_top, measure_ne_top _ _] using hreal

/-- Helper for Theorem 19.33: the singleton-target version of the deterministic-time restart
bridge factors the next-step state event through the one-step RWRE transition mass. -/
private theorem randomEnvironment_measure_inter_prefix_step_eq_mul
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    {x y z : ℤ} {A : Set Ω} {n : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + 1) ω = z}) =
      randomEnvironmentTransitionMatrix W y z * (P x : Measure Ω) A := by
  have hmem :
      (P x : Measure Ω) {ω | ω ∈ A ∧ X (n + 1) ω ∈ ({z} : Set ℤ)} =
        (discreteMatrixKernel (randomEnvironmentTransitionMatrix W) y ({z} : Set ℤ)) *
          (P x : Measure Ω) A :=
    randomEnvironment_measure_inter_prefix_step_mem_eq_mul
      (W := W) (P := P) (X := X) hA_meas hA_sub (MeasurableSet.singleton z)
  -- Proof comment: specialize the measurable-target bridge to the singleton target `{z}`.
  rw [rwreKernel_apply_singleton] at hmem
  simpa [Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using hmem

/-- Helper for Theorem 19.33: the Chapter 19 escape probability at `0` is the sum of the two
first-step no-return slice measures. -/
private theorem randomEnvironment_escapeProbability_eq_firstStepSliceMeasure_add
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X] :
    escapeProbability P X 0 =
      (P 0 : Measure Ω) ({ω | X 1 ω = 1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0} : Set Ω) +
        (P 0 : Measure Ω) ({ω | X 1 ω = -1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0} : Set Ω) := by
  let A : Set Ω := {ω | X 1 ω = 1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0}
  let B : Set Ω := {ω | X 1 ω = -1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0}
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hB_meas : MeasurableSet B := by
    have hStep_meas : MeasurableSet {ω | X 1 ω = -1} := by
      simpa [Set.preimage] using
        hReal.measurable_process 1 (MeasurableSet.singleton (-1 : ℤ))
    have hFuture_meas : MeasurableSet {ω | ∀ n : ℕ, 1 < n → X n ω ≠ 0} :=
      randomEnvironment_measurableSet_forall_gt_ne_zero (W := W) (P := P) (X := X) 1
    -- Proof comment: each slice is the intersection of a deterministic time-`1` singleton event
    -- with the measurable future no-hit-zero tail.
    exact hStep_meas.inter hFuture_meas
  have hdisj : Disjoint A B := by
    refine Set.disjoint_left.2 ?_
    intro ω hωA hωB
    have hA' : X 1 ω = 1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0 := by
      simpa [A] using hωA
    have hB' : X 1 ω = -1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0 := by
      simpa [B] using hωB
    omega
  -- Proof comment: the two no-return slices are disjoint because the first step cannot be both
  -- `1` and `-1`, so the union measure splits additively.
  rw [randomEnvironment_escapeProbability_eq_firstStepSliceMeasure (W := W) (P := P) (X := X)]
  simpa [A, B] using
    (measure_union hdisj hB_meas :
      (P 0 : Measure Ω) (A ∪ B) = (P 0 : Measure Ω) A + (P 0 : Measure Ω) B)

/-- Helper for Theorem 19.33: the right first-step no-return slice is exactly the time-`1`
state event `X 1 = 1` intersected with the first-return escape event from `0`. -/
private theorem randomEnvironment_rightFirstStepSlice_eq_inter_firstReturnEscape
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X] :
    ({ω | X 1 ω = 1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0} : Set Ω) =
      ({ω | X 1 ω = 1} ∩ {ω | (τ_[X, (0 : ℤ)]^1) ω = ⊤} : Set Ω) := by
  ext ω
  constructor
  · rintro ⟨hstep, htail⟩
    refine ⟨hstep, ?_⟩
    by_contra hescape
    have hlt :
        MeasureTheory.hittingAfter X ({0} : Set ℤ) 1 ω < ⊤ := by
      simpa [iteratedEntranceTime_one] using lt_top_iff_ne_top.2 hescape
    rcases (hittingAfter_singleton_lt_top_iff X (0 : ℤ) ω).1 hlt with ⟨m, hmpos, hmzero⟩
    by_cases hm : m = 1
    · subst hm
      simpa [hstep] using hmzero
    · have hgt : 1 < m := by omega
      exact htail m hgt hmzero
  · rintro ⟨hstep, hescape⟩
    refine ⟨hstep, ?_⟩
    intro n hn hzero
    have hlt :
        MeasureTheory.hittingAfter X ({0} : Set ℤ) 1 ω < ⊤ :=
      (hittingAfter_singleton_lt_top_iff X (0 : ℤ) ω).2 ⟨n, by omega, hzero⟩
    have hne : (τ_[X, (0 : ℤ)]^1) ω ≠ ⊤ := by
      simpa [iteratedEntranceTime_one] using hlt.ne
    exact hne hescape

/-- Helper for Theorem 19.33: the left first-step no-return slice is exactly the time-`1`
state event `X 1 = -1` intersected with the first-return escape event from `0`. -/
private theorem randomEnvironment_leftFirstStepSlice_eq_inter_firstReturnEscape
    (W : RandomEnvironment)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X] :
    ({ω | X 1 ω = -1 ∧ ∀ n : ℕ, 1 < n → X n ω ≠ 0} : Set Ω) =
      ({ω | X 1 ω = -1} ∩ {ω | (τ_[X, (0 : ℤ)]^1) ω = ⊤} : Set Ω) := by
  ext ω
  constructor
  · rintro ⟨hstep, htail⟩
    refine ⟨hstep, ?_⟩
    by_contra hescape
    have hlt :
        MeasureTheory.hittingAfter X ({0} : Set ℤ) 1 ω < ⊤ := by
      simpa [iteratedEntranceTime_one] using lt_top_iff_ne_top.2 hescape
    rcases (hittingAfter_singleton_lt_top_iff X (0 : ℤ) ω).1 hlt with ⟨m, hmpos, hmzero⟩
    by_cases hm : m = 1
    · subst hm
      simpa [hstep] using hmzero
    · have hgt : 1 < m := by omega
      exact htail m hgt hmzero
  · rintro ⟨hstep, hescape⟩
    refine ⟨hstep, ?_⟩
    intro n hn hzero
    have hlt :
        MeasureTheory.hittingAfter X ({0} : Set ℤ) 1 ω < ⊤ :=
      (hittingAfter_singleton_lt_top_iff X (0 : ℤ) ω).2 ⟨n, by omega, hzero⟩
    have hne : (τ_[X, (0 : ℤ)]^1) ω ≠ ⊤ := by
      simpa [iteratedEntranceTime_one] using hlt.ne
    exact hne hescape

/-- Helper for Theorem 19.33: a harmonic RWRE profile has the same conductance-weighted current
across the two edges adjacent to any interior vertex. -/
private theorem randomEnvironment_harmonicCurrent_eq
    (hW : W.IsElliptic) {u : ℤ → ℝ} {x : ℤ}
    (hu :
      u x = ∫ y, u y ∂ (discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) x) :
    (randomEnvironmentEdgeConductance W (x - 1)).toReal * (u x - u (x - 1)) =
      (randomEnvironmentEdgeConductance W x).toReal * (u (x + 1) - u x) := by
  let p : ℤ → ℤ → ℝ≥0∞ := randomEnvironmentTransitionMatrix W
  let f : ℤ → ℝ := fun y ↦ (p x y).toReal * u y
  have hpair_finite : ({x - 1, x + 1} : Set ℤ).Finite := by
    simpa [Set.insert_eq_of_mem] using (Set.finite_singleton (x - 1)).insert (x + 1)
  have hnorm_support :
      Function.support (fun y : ℤ ↦ (p x y).toReal * ‖u y‖) ⊆ ({x - 1, x + 1} : Set ℤ) := by
    intro y hy
    by_cases hyLeft : y = x - 1
    · simpa [hyLeft]
    · by_cases hyRight : y = x + 1
      · simpa [hyRight]
      · have hpy : p x y = 0 := by
          simp [p, randomEnvironmentTransitionMatrix, hyLeft, hyRight]
        have : (p x y).toReal * ‖u y‖ = 0 := by simp [hpy]
        exact False.elim (hy <| by simpa [this])
  have hnorm :
      Summable (fun y : ℤ ↦ (p x y).toReal * ‖u y‖) :=
    summable_of_hasFiniteSupport (hpair_finite.subset hnorm_support)
  have hsupport : ∀ y ∉ ({x - 1, x + 1} : Finset ℤ), f y = 0 := by
    intro y hy
    have hyLeft : y ≠ x - 1 := by
      intro h
      exact hy (by simp [h])
    have hyRight : y ≠ x + 1 := by
      intro h
      exact hy (by simp [h])
    simp [f, p, randomEnvironmentTransitionMatrix, hyLeft, hyRight]
  have hu_tsum : u x = ∑' y : ℤ, f y := by
    -- Proof comment: rewrite the harmonicity hypothesis as the explicit two-neighbor row series.
    simpa [f] using
      (hu.trans <|
        integral_discreteMatrixKernel_eq_tsum p
          (randomEnvironmentTransitionMatrix_isStochastic W) u x hnorm)
  have hneq : x - 1 ≠ x + 1 := by
    omega
  have hneq' : x + 1 ≠ x - 1 := by
    omega
  have hsplit :
      ∑' y : ℤ, f y = f (x - 1) + f (x + 1) := by
    rw [tsum_eq_sum hsupport]
    simp [f, hneq, hneq']
  have hrow_ne_zero :
      conductance (randomEnvironmentConductance W) x ≠ 0 :=
    ne_of_gt (randomEnvironmentConductance_vertexWeight_pos (W := W) hW x)
  have hrow_ne_top :
      conductance (randomEnvironmentConductance W) x ≠ ∞ :=
    (randomEnvironmentConductance_vertexWeight_lt_top (W := W) hW x).ne
  have hrow_toReal_ne_zero :
      (conductance (randomEnvironmentConductance W) x).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hrow_ne_zero, hrow_ne_top⟩
  have hleftWeight :
      (p x (x - 1)).toReal =
        (randomEnvironmentEdgeConductance W (x - 1)).toReal /
          (conductance (randomEnvironmentConductance W) x).toReal := by
    simpa [p, conductanceTransitionMatrix_apply, randomEnvironmentConductance,
      randomEnvironmentConductance_vertexWeight, randomEnvironmentTransitionMatrix_left,
      ENNReal.toReal_div, hrow_ne_zero, hrow_ne_top, hneq] using
      congrArg ENNReal.toReal
        (randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix hW x (x - 1))
  have hrightWeight :
      (p x (x + 1)).toReal =
        (randomEnvironmentEdgeConductance W x).toReal /
          (conductance (randomEnvironmentConductance W) x).toReal := by
    simpa [p, conductanceTransitionMatrix_apply, randomEnvironmentConductance,
      randomEnvironmentConductance_vertexWeight, randomEnvironmentTransitionMatrix_right,
      ENNReal.toReal_div, hrow_ne_zero, hrow_ne_top, hneq'] using
      congrArg ENNReal.toReal
        (randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix hW x (x + 1))
  have hrow_toReal :
      (conductance (randomEnvironmentConductance W) x).toReal =
        (randomEnvironmentEdgeConductance W (x - 1)).toReal +
          (randomEnvironmentEdgeConductance W x).toReal := by
    rw [randomEnvironmentConductance_vertexWeight,
      ENNReal.toReal_add (randomEnvironmentEdgeConductance_ne_top hW (x - 1))
        (randomEnvironmentEdgeConductance_ne_top hW x)]
  have haverage :
      u x =
        ((randomEnvironmentEdgeConductance W (x - 1)).toReal /
            (conductance (randomEnvironmentConductance W) x).toReal) * u (x - 1) +
          ((randomEnvironmentEdgeConductance W x).toReal /
            (conductance (randomEnvironmentConductance W) x).toReal) * u (x + 1) := by
    calc
      u x = ∑' y : ℤ, f y := hu_tsum
      _ = f (x - 1) + f (x + 1) := hsplit
      _ =
          ((randomEnvironmentEdgeConductance W (x - 1)).toReal /
              (conductance (randomEnvironmentConductance W) x).toReal) * u (x - 1) +
            ((randomEnvironmentEdgeConductance W x).toReal /
              (conductance (randomEnvironmentConductance W) x).toReal) * u (x + 1) := by
            simp [f, hleftWeight, hrightWeight]
  have hweighted :
      (conductance (randomEnvironmentConductance W) x).toReal * u x =
        (randomEnvironmentEdgeConductance W (x - 1)).toReal * u (x - 1) +
          (randomEnvironmentEdgeConductance W x).toReal * u (x + 1) := by
    -- Proof comment: clear the common row denominator in the two-neighbor average.
    rw [haverage]
    field_simp [hrow_toReal_ne_zero]
  have hweighted' :
      ((randomEnvironmentEdgeConductance W (x - 1)).toReal +
          (randomEnvironmentEdgeConductance W x).toReal) * u x =
        (randomEnvironmentEdgeConductance W (x - 1)).toReal * u (x - 1) +
          (randomEnvironmentEdgeConductance W x).toReal * u (x + 1) := by
    simpa [hrow_toReal] using hweighted
  -- Proof comment: rearranging the weighted-average identity yields the conserved current across
  -- the two edges adjacent to `x`.
  linarith

/-- Helper for Theorem 19.33: prefix sums of successive drops telescope to the endpoint
difference. -/
private theorem randomEnvironment_prefixDrops_telescope (u : ℕ → ℝ) (k : ℕ) :
    Finset.sum (Finset.range k) (fun i ↦ (u (i + 1) - u i)) = u k - u 0 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Proof comment: split off the last edge drop and telescope the earlier prefix inductively.
      rw [Finset.sum_range_succ, ih]
      ring

/-- Helper for Theorem 19.33: once the RWRE profile is harmonic at every positive interior vertex
of a finite corridor, the conductance-weighted edge current is constant along that corridor. -/
private theorem harmonicCurrentConstOnNatSegment
    (hW : W.IsElliptic) {u : ℤ → ℝ} {N : ℕ}
    (hharm :
      ∀ i : ℕ, i < N →
        u ((i + 1 : ℕ) : ℤ) =
          ∫ y, u y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W))
            ((i + 1 : ℕ) : ℤ))) :
    ∀ i : ℕ, i ≤ N →
      (randomEnvironmentEdgeConductance W (i : ℤ)).toReal *
          (u ((i + 1 : ℕ) : ℤ) - u (i : ℤ)) =
        (randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0) := by
  intro i hi
  induction i with
  | zero =>
      -- Proof comment: the base current is already the reference current.
      simp
  | succ i ih =>
      have hi_lt : i < N := Nat.lt_of_succ_le hi
      have hstep :=
        randomEnvironment_harmonicCurrent_eq
          (W := W) hW (u := u) (x := ((i + 1 : ℕ) : ℤ)) (hharm i hi_lt)
      have hxPrev : (((i + 1 : ℕ) : ℤ) - 1) = (i : ℤ) := by
        omega
      have hxNext : (((i + 1 : ℕ) : ℤ) + 1) = ((i + 2 : ℕ) : ℤ) := by
        omega
      calc
        (randomEnvironmentEdgeConductance W ((i + 1 : ℕ) : ℤ)).toReal *
            (u ((i + 2 : ℕ) : ℤ) - u ((i + 1 : ℕ) : ℤ))
            =
          (randomEnvironmentEdgeConductance W (i : ℤ)).toReal *
            (u ((i + 1 : ℕ) : ℤ) - u (i : ℤ)) := by
              simpa [hxPrev, hxNext] using hstep.symm
        _ =
          (randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0) :=
            ih (Nat.le_of_lt hi_lt)

/-- Helper for Theorem 19.33: on the reflected negative corridor, harmonicity again forces a
constant conductance-weighted current after reindexing by `ℕ`. -/
private theorem harmonicCurrentStep_negSucc
    (hW : W.IsElliptic) {u : ℤ → ℝ} {i : ℕ}
    (hu :
      u (-((i + 1 : ℕ) : ℤ)) =
        ∫ y, u y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W))
          (-((i + 1 : ℕ) : ℤ)))) :
    (randomEnvironmentEdgeConductance W (Int.negSucc (i + 1))).toReal *
        (u (-((i + 2 : ℕ) : ℤ)) - u (-((i + 1 : ℕ) : ℤ))) =
      (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal *
        (u (-((i + 1 : ℕ) : ℤ)) - u (-((i : ℕ) : ℤ))) := by
  have hstep :=
    randomEnvironment_harmonicCurrent_eq
      (W := W) hW (u := u) (x := -((i + 1 : ℕ) : ℤ)) hu
  have hx : (-((i + 1 : ℕ) : ℤ) : ℤ) = Int.negSucc i := by
    omega
  have hxPrev : ((-((i + 1 : ℕ) : ℤ) : ℤ) - 1) = Int.negSucc (i + 1) := by
    omega
  have hxNext : ((-((i + 1 : ℕ) : ℤ) : ℤ) + 1) = -((i : ℕ) : ℤ) := by
    omega
  have hxPrevNorm : (-1 + -((i : ℕ) : ℤ) - 1 : ℤ) = Int.negSucc (i + 1) := by
    omega
  have hxNorm : (-1 + -((i : ℕ) : ℤ) : ℤ) = Int.negSucc i := by
    omega
  have hxNegTwo : (-2 + -((i : ℕ) : ℤ) : ℤ) = Int.negSucc (i + 1) := by
    omega
  have hxSuccNegSucc : (Int.negSucc i : ℤ) + 1 = -((i : ℕ) : ℤ) := by
    simp
  have hnormalized :
      (randomEnvironmentEdgeConductance W (Int.negSucc (i + 1))).toReal *
          (u (-((i + 1 : ℕ) : ℤ)) - u (-((i + 2 : ℕ) : ℤ))) =
        (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal *
          (u (-((i : ℕ) : ℤ)) - u (-((i + 1 : ℕ) : ℤ))) := by
    -- Proof comment: rewrite the harmonic current identity into the stable `Int.negSucc`
    -- indexing before changing the drop orientation.
    simpa [hx, hxPrev, hxNext, hxPrevNorm, hxNorm, hxNegTwo, hxSuccNegSucc,
      randomEnvironmentEdgeConductance_negSucc]
      using hstep
  -- Proof comment: both sides change sign when the edge drops are written in corridor order.
  linarith

/-- Helper for Theorem 19.33: on the reflected negative corridor, harmonicity again forces a
constant conductance-weighted current after reindexing by `ℕ`. -/
private theorem harmonicCurrentConstOnNegSuccSegment
    (hW : W.IsElliptic) {u : ℤ → ℝ} {N : ℕ}
    (hharm :
      ∀ i : ℕ, i < N →
        u (-((i + 1 : ℕ) : ℤ)) =
          ∫ y, u y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W))
            (-((i + 1 : ℕ) : ℤ)))) :
    ∀ i : ℕ, i ≤ N →
      (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal *
          (u (-((i + 1 : ℕ) : ℤ)) - u (-((i : ℕ) : ℤ))) =
        (randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0) := by
  intro i hi
  induction i with
  | zero =>
      -- Proof comment: the first reflected edge is already the reference current.
      simp
  | succ i ih =>
      have hi_lt : i < N := Nat.lt_of_succ_le hi
      have hstep :=
        harmonicCurrentStep_negSucc
          (W := W) hW (u := u) (i := i) (hharm i hi_lt)
      calc
        (randomEnvironmentEdgeConductance W (Int.negSucc (i + 1))).toReal *
            (u (-((i + 2 : ℕ) : ℤ)) - u (-((i + 1 : ℕ) : ℤ)))
            =
          (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal *
            (u (-((i + 1 : ℕ) : ℤ)) - u (-((i : ℕ) : ℤ))) := hstep
        _ =
          (randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0) :=
            ih (Nat.le_of_lt hi_lt)

/-- Helper for Theorem 19.33: a constant finite-segment current integrates to the endpoint
difference times the reciprocal-weight sum. -/
private theorem boundaryDifference_eq_current_mul_prefixSum
    {c u : ℕ → ℝ} {N : ℕ} {J : ℝ}
    (hc : ∀ i : ℕ, i ≤ N → c i ≠ 0)
    (hcurrent : ∀ i : ℕ, i ≤ N → c i * (u (i + 1) - u i) = J) :
    u (N + 1) - u 0 =
      J * Finset.sum (Finset.range (N + 1)) (fun i ↦ (c i)⁻¹) := by
  calc
    u (N + 1) - u 0
        = Finset.sum (Finset.range (N + 1)) (fun i ↦ (u (i + 1) - u i)) := by
            symm
            exact randomEnvironment_prefixDrops_telescope u (N + 1)
    _ = Finset.sum (Finset.range (N + 1)) (fun i ↦ J * (c i)⁻¹) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi_le : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hci : c i ≠ 0 := hc i hi_le
          apply mul_right_cancel₀ hci
          calc
            (u (i + 1) - u i) * c i = c i * (u (i + 1) - u i) := by ring
            _ = J := hcurrent i hi_le
            _ = (J * (c i)⁻¹) * c i := by
                  field_simp [hci]
    _ = J * Finset.sum (Finset.range (N + 1)) (fun i ↦ (c i)⁻¹) := by
          rw [Finset.mul_sum]

/-- Helper for Theorem 19.33: the reciprocal real conductances on the positive ray are exactly
the real-valued right Solomon prefix terms. -/
private theorem rightEdgeConductanceInverseSum_eq_rightPrefixSum_toReal
    (hW : W.IsElliptic) (N : ℕ) :
    Finset.sum (Finset.range (N + 1))
        (fun i ↦ ((randomEnvironmentEdgeConductance W (i : ℤ)).toReal)⁻¹) =
      (randomEnvironmentRightPrefixSum W N).toReal := by
  -- Proof comment: on the nonnegative ray the bridge conductance is the inverse prefix product,
  -- so taking the reciprocal after `toReal` recovers the Solomon term itself.
  rw [randomEnvironmentRightPrefixSum, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_nonneg : (0 : ℤ) ≤ (i : ℤ) := by
      exact_mod_cast Nat.zero_le i
    rw [randomEnvironmentEdgeConductance, if_pos hi_nonneg]
    simpa using congrArg Inv.inv
      (ENNReal.toReal_inv (randomEnvironmentRightSeriesTerm W i))
  · intro i hi
    exact randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i

/-- Helper for Theorem 19.33: the reciprocal real conductances on the reflected negative ray are
exactly the real-valued left Solomon prefix terms. -/
private theorem leftEdgeConductanceInverseSum_eq_leftPrefixSum_toReal
    (hW : W.IsElliptic) (N : ℕ) :
    Finset.sum (Finset.range (N + 1))
        (fun i ↦ ((randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal)⁻¹) =
      (randomEnvironmentLeftPrefixSum W N).toReal := by
  -- Proof comment: the `Int.negSucc` normal form exposes the reflected left prefix owner
  -- directly, so the same reciprocal-to-term rewrite works on the negative ray.
  rw [randomEnvironmentLeftPrefixSum, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    rw [randomEnvironmentEdgeConductance_negSucc]
    simpa using congrArg Inv.inv
      (ENNReal.toReal_inv (randomEnvironmentLeftSeriesTerm W i))
  · intro i hi
    exact randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i

/-- Helper for Theorem 19.33: on the positive branch with boundary `{0, N + 1}`, the boundary
current through the first edge is the reciprocal of the positive Solomon prefix-resistance sum. -/
private theorem rightBoundaryFA_mul_edge_eq_rightPrefixInv
    (hW : W.IsElliptic) (N : ℕ) :
    (randomEnvironmentEdgeConductance W 0).toReal *
        F_A P X ({0} : Set ℤ) 1 (((N + 1 : ℕ) : ℤ)) =
      (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
  -- Route correction: the corridor theorem now uses the local conserved-current and telescoping
  -- API directly, instead of reopening the ENNReal normalization inside the final scalar step.
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let u : ℤ → ℝ := fun z ↦ F_A P X ({0} : Set ℤ) z right
  have hharm :
      ∀ i : ℕ, i < N →
        u ((i + 1 : ℕ) : ℤ) =
          ∫ y, u y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W))
            ((i + 1 : ℕ) : ℤ)) := by
    intro i hi
    apply F_A_average_eq_outside_insert_boundary
      (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
      (A := ({0} : Set ℤ)) (b := right)
    simp [right]
    omega
  have hcurrent :=
    harmonicCurrentConstOnNatSegment (W := W) hW (u := u) (N := N) hharm
  have hconductance_ne :
      ∀ i : ℕ, i ≤ N →
        (randomEnvironmentEdgeConductance W (i : ℤ)).toReal ≠ 0 := by
    intro i hi
    exact (ENNReal.toReal_pos
      (randomEnvironmentEdgeConductance_pos (W := W) hW (i : ℤ)).ne'
      (randomEnvironmentEdgeConductance_ne_top (W := W) hW (i : ℤ))).ne'
  have htelescoped :=
    boundaryDifference_eq_current_mul_prefixSum
      (c := fun i ↦ (randomEnvironmentEdgeConductance W (i : ℤ)).toReal)
      (u := fun i ↦ u (i : ℤ))
      (N := N)
      (J := (randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0))
      hconductance_ne
      (fun i hi ↦ by simpa using hcurrent i hi)
  have hzero :
      u 0 = 0 := by
    have hmem : (0 : ℤ) ∈ insert right ({0} : Set ℤ) := by simp
    have hneq : (0 : ℤ) ≠ right := by
      simp [right]
      omega
    simpa [u, hneq] using
      (F_A_eq_boundaryDatum_on_insert_boundary
        (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
        (A := ({0} : Set ℤ)) (b := right) (x := (0 : ℤ)) hmem)
  have hright :
      u right = 1 := by
    have hmem : right ∈ insert right ({0} : Set ℤ) := by simp
    simpa [u] using
      (F_A_eq_boundaryDatum_on_insert_boundary
        (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
        (A := ({0} : Set ℤ)) (b := right) (x := right) hmem)
  have hs_pos : 0 < (randomEnvironmentRightPrefixSum W N).toReal := by
    have hterm0 :
        0 < (randomEnvironmentRightSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentRightSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentRightSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentRightSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentRightSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i
  have hs_ne : (randomEnvironmentRightPrefixSum W N).toReal ≠ 0 := hs_pos.ne'
  have htelescoped' :
      u right - u 0 =
        ((randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal := by
    rw [rightEdgeConductanceInverseSum_eq_rightPrefixSum_toReal (W := W) hW N] at htelescoped
    simpa [right] using htelescoped
  have hprod :
      ((randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal = 1 := by
    have hmain : 1 =
        ((randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal := by
      simpa [hzero, hright] using htelescoped'
    exact hmain.symm
  have hcurrentValue :
      (randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0) =
        (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
    apply mul_right_cancel₀ hs_ne
    calc
      ((randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal = 1 := hprod
      _ =
          (randomEnvironmentRightPrefixSum W N).toReal⁻¹ *
            (randomEnvironmentRightPrefixSum W N).toReal := by
            field_simp [hs_ne]
  have hdrop : u 1 - u 0 = u 1 := by
    rw [hzero, sub_zero]
  have hcurrentValue' :
      (randomEnvironmentEdgeConductance W 0).toReal * u 1 =
        (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
    rw [← hdrop]
    exact hcurrentValue
  -- Proof comment: the right endpoint contributes the boundary value `1`, while the left
  -- endpoint contributes `0`, so the conserved current is exactly the reciprocal prefix sum.
  simpa [right, u] using hcurrentValue'

/-- Helper for Theorem 19.33: on the negative branch with boundary `{-(N + 1), 0}`, the boundary
current through the first left edge is the reciprocal of the reflected Solomon prefix-resistance
sum. -/
private theorem leftBoundaryFA_mul_edge_eq_leftPrefixInv
    (hW : W.IsElliptic) (N : ℕ) :
    (randomEnvironmentEdgeConductance W (-1)).toReal *
        F_A P X ({0} : Set ℤ) (-1) (-((N + 1 : ℕ) : ℤ)) =
      (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let u : ℤ → ℝ := fun z ↦ F_A P X ({0} : Set ℤ) z left
  have hharm :
      ∀ i : ℕ, i < N →
        u (-((i + 1 : ℕ) : ℤ)) =
          ∫ y, u y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W))
            (-((i + 1 : ℕ) : ℤ))) := by
    intro i hi
    apply F_A_average_eq_outside_insert_boundary
      (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
      (A := ({0} : Set ℤ)) (b := left)
    simp [left]
    omega
  have hcurrent :=
    harmonicCurrentConstOnNegSuccSegment (W := W) hW (u := u) (N := N) hharm
  have hconductance_ne :
      ∀ i : ℕ, i ≤ N →
        (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal ≠ 0 := by
    intro i hi
    exact (ENNReal.toReal_pos
      (randomEnvironmentEdgeConductance_pos (W := W) hW (Int.negSucc i)).ne'
      (randomEnvironmentEdgeConductance_ne_top (W := W) hW (Int.negSucc i))).ne'
  have htelescoped :=
    boundaryDifference_eq_current_mul_prefixSum
      (c := fun i ↦ (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal)
      (u := fun i ↦ u (-((i : ℕ) : ℤ)))
      (N := N)
      (J := (randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0))
      hconductance_ne
      (fun i hi ↦ by simpa using hcurrent i hi)
  have hzero :
      u 0 = 0 := by
    have hmem : (0 : ℤ) ∈ insert left ({0} : Set ℤ) := by simp
    have hneq : (0 : ℤ) ≠ left := by
      simp [left]
      omega
    simpa [u, hneq] using
      (F_A_eq_boundaryDatum_on_insert_boundary
        (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
        (A := ({0} : Set ℤ)) (b := left) (x := (0 : ℤ)) hmem)
  have hleft :
      u left = 1 := by
    have hmem : left ∈ insert left ({0} : Set ℤ) := by simp
    simpa [u] using
      (F_A_eq_boundaryDatum_on_insert_boundary
        (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
        (A := ({0} : Set ℤ)) (b := left) (x := left) hmem)
  have hs_pos : 0 < (randomEnvironmentLeftPrefixSum W N).toReal := by
    have hterm0 :
        0 < (randomEnvironmentLeftSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentLeftSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentLeftSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentLeftSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i
  have hs_ne : (randomEnvironmentLeftPrefixSum W N).toReal ≠ 0 := hs_pos.ne'
  have htelescoped' :
      u left - u 0 =
        ((randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal := by
    rw [leftEdgeConductanceInverseSum_eq_leftPrefixSum_toReal (W := W) hW N] at htelescoped
    simpa [left] using htelescoped
  have hprod :
      ((randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal = 1 := by
    have hmain : 1 =
        ((randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal := by
      simpa [hzero, hleft] using htelescoped'
    exact hmain.symm
  have hcurrentValue :
      (randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0) =
        (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ := by
    apply mul_right_cancel₀ hs_ne
    calc
      ((randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal = 1 := hprod
      _ =
          (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ *
            (randomEnvironmentLeftPrefixSum W N).toReal := by
            field_simp [hs_ne]
  have hdrop : u (-1) - u 0 = u (-1) := by
    rw [hzero, sub_zero]
  have hcurrentValue' :
      (randomEnvironmentEdgeConductance W (-1)).toReal * u (-1) =
        (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ := by
    rw [← hdrop]
    exact hcurrentValue
  -- Proof comment: the reflected corridor has the same telescoping shape, now with the boundary
  -- value `1` at the left endpoint.
  simpa [left, u] using hcurrentValue'

/-- Helper for Theorem 19.33: on the right half of the symmetric corridor
`[-(N + 1), N + 1]`, the conductance-weighted drop across the first right edge is the value at
`0` divided by the right Solomon prefix-resistance sum. -/
private theorem twoRayCorridorRightFlux_eq_u0_mul_rightPrefixInv
    (hW : W.IsElliptic) (N : ℕ) :
    let left : ℤ := -((N + 1 : ℕ) : ℤ)
    let right : ℤ := ((N + 1 : ℕ) : ℤ)
    let u : ℤ → ℝ := fun z ↦ F_A P X ({right} : Set ℤ) z left
    (randomEnvironmentEdgeConductance W 0).toReal * (u 0 - u 1) =
      u 0 *
        (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let u : ℤ → ℝ := fun z ↦ F_A P X ({right} : Set ℤ) z left
  have hharm :
      ∀ i : ℕ, i < N →
        u ((i + 1 : ℕ) : ℤ) =
          ∫ y, u y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W))
            ((i + 1 : ℕ) : ℤ)) := by
    intro i hi
    apply F_A_average_eq_outside_insert_boundary
      (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
      (A := ({right} : Set ℤ)) (b := left)
    simp [left, right]
    omega
  have hcurrent :=
    harmonicCurrentConstOnNatSegment (W := W) hW (u := u) (N := N) hharm
  have hconductance_ne :
      ∀ i : ℕ, i ≤ N →
        (randomEnvironmentEdgeConductance W (i : ℤ)).toReal ≠ 0 := by
    intro i hi
    exact (ENNReal.toReal_pos
      (randomEnvironmentEdgeConductance_pos (W := W) hW (i : ℤ)).ne'
      (randomEnvironmentEdgeConductance_ne_top (W := W) hW (i : ℤ))).ne'
  have htelescoped :=
    boundaryDifference_eq_current_mul_prefixSum
      (c := fun i ↦ (randomEnvironmentEdgeConductance W (i : ℤ)).toReal)
      (u := fun i ↦ u (i : ℤ))
      (N := N)
      (J := (randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0))
      hconductance_ne
      (fun i hi ↦ by simpa using hcurrent i hi)
  have hright :
      u right = 0 := by
    have hmem : right ∈ insert left ({right} : Set ℤ) := by simp
    have hneq : right ≠ left := by
      simp [left, right]
      omega
    simpa [u, hneq] using
      (F_A_eq_boundaryDatum_on_insert_boundary
        (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
        (A := ({right} : Set ℤ)) (b := left) (x := right) hmem)
  have hs_pos : 0 < (randomEnvironmentRightPrefixSum W N).toReal := by
    have hterm0 :
        0 < (randomEnvironmentRightSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentRightSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentRightSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentRightSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentRightSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i
  have hs_ne : (randomEnvironmentRightPrefixSum W N).toReal ≠ 0 := hs_pos.ne'
  have htelescoped' :
      u right - u 0 =
        ((randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal := by
    rw [rightEdgeConductanceInverseSum_eq_rightPrefixSum_toReal (W := W) hW N] at htelescoped
    simpa [right] using htelescoped
  have hprod :
      ((randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal = -u 0 := by
    have hmain : -u 0 =
        ((randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal := by
      simpa [hright] using htelescoped'
    exact hmain.symm
  have hcurrentValue :
      (randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0) =
        -u 0 * (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
    apply mul_right_cancel₀ hs_ne
    calc
      ((randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal = -u 0 := hprod
      _ =
          (-u 0 * (randomEnvironmentRightPrefixSum W N).toReal⁻¹) *
            (randomEnvironmentRightPrefixSum W N).toReal := by
            field_simp [hs_ne]
  -- Proof comment: the right boundary now carries the value `0`, so the telescoped difference
  -- is `-u 0`; flipping the edge orientation produces the flux formula used at the origin.
  calc
    (randomEnvironmentEdgeConductance W 0).toReal * (u 0 - u 1)
        = -((randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0)) := by ring
    _ = -(-u 0 * (randomEnvironmentRightPrefixSum W N).toReal⁻¹) := by rw [hcurrentValue]
    _ = u 0 * (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by ring

/-- Helper for Theorem 19.33: on the left half of the symmetric corridor
`[-(N + 1), N + 1]`, the conductance-weighted drop across the first left edge is
`1 - u(0)` divided by the left Solomon prefix-resistance sum. -/
private theorem twoRayCorridorLeftFlux_eq_oneSubU0_mul_leftPrefixInv
    (hW : W.IsElliptic) (N : ℕ) :
    let left : ℤ := -((N + 1 : ℕ) : ℤ)
    let right : ℤ := ((N + 1 : ℕ) : ℤ)
    let u : ℤ → ℝ := fun z ↦ F_A P X ({right} : Set ℤ) z left
    (randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0) =
      (1 - u 0) *
        (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let u : ℤ → ℝ := fun z ↦ F_A P X ({right} : Set ℤ) z left
  have hharm :
      ∀ i : ℕ, i < N →
        u (-((i + 1 : ℕ) : ℤ)) =
          ∫ y, u y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W))
            (-((i + 1 : ℕ) : ℤ))) := by
    intro i hi
    apply F_A_average_eq_outside_insert_boundary
      (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
      (A := ({right} : Set ℤ)) (b := left)
    simp [left, right]
    omega
  have hcurrent :=
    harmonicCurrentConstOnNegSuccSegment (W := W) hW (u := u) (N := N) hharm
  have hconductance_ne :
      ∀ i : ℕ, i ≤ N →
        (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal ≠ 0 := by
    intro i hi
    exact (ENNReal.toReal_pos
      (randomEnvironmentEdgeConductance_pos (W := W) hW (Int.negSucc i)).ne'
      (randomEnvironmentEdgeConductance_ne_top (W := W) hW (Int.negSucc i))).ne'
  have htelescoped :=
    boundaryDifference_eq_current_mul_prefixSum
      (c := fun i ↦ (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal)
      (u := fun i ↦ u (-((i : ℕ) : ℤ)))
      (N := N)
      (J := (randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0))
      hconductance_ne
      (fun i hi ↦ by simpa using hcurrent i hi)
  have hleft :
      u left = 1 := by
    have hmem : left ∈ insert left ({right} : Set ℤ) := by simp
    simpa [u] using
      (F_A_eq_boundaryDatum_on_insert_boundary
        (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
        (A := ({right} : Set ℤ)) (b := left) (x := left) hmem)
  have hs_pos : 0 < (randomEnvironmentLeftPrefixSum W N).toReal := by
    have hterm0 :
        0 < (randomEnvironmentLeftSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentLeftSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentLeftSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentLeftSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i
  have hs_ne : (randomEnvironmentLeftPrefixSum W N).toReal ≠ 0 := hs_pos.ne'
  have htelescoped' :
      u left - u 0 =
        ((randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal := by
    rw [leftEdgeConductanceInverseSum_eq_leftPrefixSum_toReal (W := W) hW N] at htelescoped
    simpa [left] using htelescoped
  have hprod :
      ((randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal = 1 - u 0 := by
    have hmain : 1 - u 0 =
        ((randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal := by
      simpa [hleft] using htelescoped'
    exact hmain.symm
  have hcurrentValue :
      (randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0) =
        (1 - u 0) * (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ := by
    apply mul_right_cancel₀ hs_ne
    calc
      ((randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal = 1 - u 0 := hprod
      _ =
          ((1 - u 0) * (randomEnvironmentLeftPrefixSum W N).toReal⁻¹) *
            (randomEnvironmentLeftPrefixSum W N).toReal := by
            field_simp [hs_ne]
  -- Proof comment: the left endpoint contributes the boundary value `1`, so the reflected
  -- telescoping identity directly gives the `1 - u 0` flux factor.
  simpa [left, right, u] using hcurrentValue

/-- Helper for Theorem 19.33: the symmetric finite-corridor left-exit probability at `0` is the
right prefix resistance divided by the total left-plus-right prefix resistance. -/
private theorem twoRayLeftExitProbability_eq_prefixRatio
    (hW : W.IsElliptic) (N : ℕ) :
    let left : ℤ := -((N + 1 : ℕ) : ℤ)
    let right : ℤ := ((N + 1 : ℕ) : ℤ)
    F_A P X ({right} : Set ℤ) 0 left = randomEnvironmentLeftExitPrefixRatio W N := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let u : ℤ → ℝ := fun z ↦ F_A P X ({right} : Set ℤ) z left
  let leftSum : ℝ≥0∞ := randomEnvironmentLeftPrefixSum W N
  let rightSum : ℝ≥0∞ := randomEnvironmentRightPrefixSum W N
  have hx : (0 : ℤ) ∉ insert left ({right} : Set ℤ) := by
    simp [left, right]
    omega
  have hharm :
      u 0 = ∫ y, u y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) 0) :=
    F_A_average_eq_outside_insert_boundary
      (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
      (A := ({right} : Set ℤ)) (b := left) hx
  have hcurrent :
      (randomEnvironmentEdgeConductance W (-1)).toReal * (u 0 - u (-1)) =
        (randomEnvironmentEdgeConductance W 0).toReal * (u 1 - u 0) :=
    randomEnvironment_harmonicCurrent_eq
      (W := W) hW (u := u) (x := 0) hharm
  have hbalance :
      (randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0) =
        (randomEnvironmentEdgeConductance W 0).toReal * (u 0 - u 1) := by
    linarith
  have hleftFlux :
      (randomEnvironmentEdgeConductance W (-1)).toReal * (u (-1) - u 0) =
        (1 - u 0) * (leftSum.toReal)⁻¹ := by
    simpa [left, right, u, leftSum] using
      twoRayCorridorLeftFlux_eq_oneSubU0_mul_leftPrefixInv
        (W := W) (P := P) (X := X) hW N
  have hrightFlux :
      (randomEnvironmentEdgeConductance W 0).toReal * (u 0 - u 1) =
        u 0 * (rightSum.toReal)⁻¹ := by
    simpa [left, right, u, rightSum] using
      twoRayCorridorRightFlux_eq_u0_mul_rightPrefixInv
        (W := W) (P := P) (X := X) hW N
  have hleftSum_pos : 0 < leftSum.toReal := by
    have hterm0 :
        0 < (randomEnvironmentLeftSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentLeftSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentLeftSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentLeftSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i
  have hrightSum_pos : 0 < rightSum.toReal := by
    have hterm0 :
        0 < (randomEnvironmentRightSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentRightSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentRightSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentRightSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentRightSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i
  have hleftSum_ne : leftSum.toReal ≠ 0 := hleftSum_pos.ne'
  have hrightSum_ne : rightSum.toReal ≠ 0 := hrightSum_pos.ne'
  have hsum_ne : leftSum.toReal + rightSum.toReal ≠ 0 := (add_pos hleftSum_pos hrightSum_pos).ne'
  have hratio :
      (1 - u 0) / leftSum.toReal = u 0 / rightSum.toReal := by
    calc
      (1 - u 0) / leftSum.toReal
          = (1 - u 0) * (leftSum.toReal)⁻¹ := by rw [div_eq_mul_inv]
      _ = u 0 * (rightSum.toReal)⁻¹ := by rw [← hleftFlux, hbalance, hrightFlux]
      _ = u 0 / rightSum.toReal := by rw [div_eq_mul_inv]
  have hcross :
      (1 - u 0) * rightSum.toReal = u 0 * leftSum.toReal := by
    have hratio' := hratio
    field_simp [hleftSum_ne, hrightSum_ne] at hratio'
    linarith
  have hfinal :
      u 0 = rightSum.toReal / (leftSum.toReal + rightSum.toReal) := by
    apply (eq_div_iff hsum_ne).2
    linarith
  -- Proof comment: the origin current balance turns the two half-corridor flux formulas into one
  -- scalar equation, whose solution is the finite Solomon prefix ratio.
  simpa [left, right, u, leftSum, rightSum, randomEnvironmentLeftExitPrefixRatio] using hfinal

/-- Helper for Theorem 19.33: on the symmetric corridor `[-(N + 1), N + 1]`, the right-exit
probability is the complement of the left-exit probability. -/
private theorem twoRayCorridorRightFlux_eq_rightBoundaryGap_mul_rightPrefixInv
    (hW : W.IsElliptic) (N : ℕ) :
    let left : ℤ := -((N + 1 : ℕ) : ℤ)
    let right : ℤ := ((N + 1 : ℕ) : ℤ)
    let v : ℤ → ℝ := fun z ↦ F_A P X ({left} : Set ℤ) z right
    (randomEnvironmentEdgeConductance W 0).toReal * (v 1 - v 0) =
      (1 - v 0) * (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let v : ℤ → ℝ := fun z ↦ F_A P X ({left} : Set ℤ) z right
  have hharm :
      ∀ i : ℕ, i < N →
        v ((i + 1 : ℕ) : ℤ) =
          ∫ y, v y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W))
            ((i + 1 : ℕ) : ℤ)) := by
    intro i hi
    apply F_A_average_eq_outside_insert_boundary
      (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
      (A := ({left} : Set ℤ)) (b := right)
    simp [left, right]
    omega
  have hcurrent :=
    harmonicCurrentConstOnNatSegment (W := W) hW (u := v) (N := N) hharm
  have hconductance_ne :
      ∀ i : ℕ, i ≤ N →
        (randomEnvironmentEdgeConductance W (i : ℤ)).toReal ≠ 0 := by
    intro i hi
    exact (ENNReal.toReal_pos
      (randomEnvironmentEdgeConductance_pos (W := W) hW (i : ℤ)).ne'
      (randomEnvironmentEdgeConductance_ne_top (W := W) hW (i : ℤ))).ne'
  have htelescoped :=
    boundaryDifference_eq_current_mul_prefixSum
      (c := fun i ↦ (randomEnvironmentEdgeConductance W (i : ℤ)).toReal)
      (u := fun i ↦ v (i : ℤ))
      (N := N)
      (J := (randomEnvironmentEdgeConductance W 0).toReal * (v 1 - v 0))
      hconductance_ne
      (fun i hi ↦ by simpa using hcurrent i hi)
  have hright :
      v right = 1 := by
    have hmem : right ∈ insert right ({left} : Set ℤ) := by simp
    simpa [v] using
      (F_A_eq_boundaryDatum_on_insert_boundary
        (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
        (A := ({left} : Set ℤ)) (b := right) (x := right) hmem)
  have hs_pos : 0 < (randomEnvironmentRightPrefixSum W N).toReal := by
    have hterm0 :
        0 < (randomEnvironmentRightSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentRightSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentRightSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentRightSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentRightSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i
  have hs_ne : (randomEnvironmentRightPrefixSum W N).toReal ≠ 0 := hs_pos.ne'
  have htelescoped' :
      v right - v 0 =
        ((randomEnvironmentEdgeConductance W 0).toReal * (v 1 - v 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal := by
    rw [rightEdgeConductanceInverseSum_eq_rightPrefixSum_toReal (W := W) hW N] at htelescoped
    simpa [right] using htelescoped
  have hprod :
      ((randomEnvironmentEdgeConductance W 0).toReal * (v 1 - v 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal = 1 - v 0 := by
    have hmain : 1 - v 0 =
        ((randomEnvironmentEdgeConductance W 0).toReal * (v 1 - v 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal := by
      simpa [hright] using htelescoped'
    exact hmain.symm
  have hcurrentValue :
      (randomEnvironmentEdgeConductance W 0).toReal * (v 1 - v 0) =
        (1 - v 0) * (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
    apply mul_right_cancel₀ hs_ne
    calc
      ((randomEnvironmentEdgeConductance W 0).toReal * (v 1 - v 0)) *
          (randomEnvironmentRightPrefixSum W N).toReal = 1 - v 0 := hprod
      _ =
          ((1 - v 0) * (randomEnvironmentRightPrefixSum W N).toReal⁻¹) *
            (randomEnvironmentRightPrefixSum W N).toReal := by
            field_simp [hs_ne]
  -- Proof comment: the right endpoint carries boundary value `1`, so the telescoped corridor
  -- current records the right-boundary gap `1 - v(0)`.
  simpa [left, right, v] using hcurrentValue

/-- Helper for Theorem 19.33: on the left half of the symmetric corridor for the right-exit
profile, the conductance-weighted drop across the first left edge is `v(0)` divided by the left
Solomon prefix-resistance sum. -/
private theorem twoRayCorridorLeftFlux_eq_leftBoundaryGap_mul_leftPrefixInv
    (hW : W.IsElliptic) (N : ℕ) :
    let left : ℤ := -((N + 1 : ℕ) : ℤ)
    let right : ℤ := ((N + 1 : ℕ) : ℤ)
    let v : ℤ → ℝ := fun z ↦ F_A P X ({left} : Set ℤ) z right
    (randomEnvironmentEdgeConductance W (-1)).toReal * (v 0 - v (-1)) =
      v 0 * (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let v : ℤ → ℝ := fun z ↦ F_A P X ({left} : Set ℤ) z right
  have hharm :
      ∀ i : ℕ, i < N →
        v (-((i + 1 : ℕ) : ℤ)) =
          ∫ y, v y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W))
            (-((i + 1 : ℕ) : ℤ))) := by
    intro i hi
    apply F_A_average_eq_outside_insert_boundary
      (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
      (A := ({left} : Set ℤ)) (b := right)
    simp [left, right]
    omega
  have hcurrent :=
    harmonicCurrentConstOnNegSuccSegment (W := W) hW (u := v) (N := N) hharm
  have hconductance_ne :
      ∀ i : ℕ, i ≤ N →
        (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal ≠ 0 := by
    intro i hi
    exact (ENNReal.toReal_pos
      (randomEnvironmentEdgeConductance_pos (W := W) hW (Int.negSucc i)).ne'
      (randomEnvironmentEdgeConductance_ne_top (W := W) hW (Int.negSucc i))).ne'
  have htelescoped :=
    boundaryDifference_eq_current_mul_prefixSum
      (c := fun i ↦ (randomEnvironmentEdgeConductance W (Int.negSucc i)).toReal)
      (u := fun i ↦ v (-((i : ℕ) : ℤ)))
      (N := N)
      (J := (randomEnvironmentEdgeConductance W (-1)).toReal * (v (-1) - v 0))
      hconductance_ne
      (fun i hi ↦ by simpa using hcurrent i hi)
  have hleft :
      v left = 0 := by
    have hmem : left ∈ insert right ({left} : Set ℤ) := by simp
    have hneq : left ≠ right := by
      simp [left, right]
      omega
    simpa [v, hneq] using
      (F_A_eq_boundaryDatum_on_insert_boundary
        (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
        (A := ({left} : Set ℤ)) (b := right) (x := left) hmem)
  have hs_pos : 0 < (randomEnvironmentLeftPrefixSum W N).toReal := by
    have hterm0 :
        0 < (randomEnvironmentLeftSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentLeftSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentLeftSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentLeftSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i
  have hs_ne : (randomEnvironmentLeftPrefixSum W N).toReal ≠ 0 := hs_pos.ne'
  have htelescoped' :
      v left - v 0 =
        ((randomEnvironmentEdgeConductance W (-1)).toReal * (v (-1) - v 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal := by
    rw [leftEdgeConductanceInverseSum_eq_leftPrefixSum_toReal (W := W) hW N] at htelescoped
    simpa [left] using htelescoped
  have hprod :
      ((randomEnvironmentEdgeConductance W (-1)).toReal * (v (-1) - v 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal = -v 0 := by
    have hmain : -v 0 =
        ((randomEnvironmentEdgeConductance W (-1)).toReal * (v (-1) - v 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal := by
      simpa [hleft] using htelescoped'
    exact hmain.symm
  have hcurrentValue :
      (randomEnvironmentEdgeConductance W (-1)).toReal * (v (-1) - v 0) =
        -v 0 * (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ := by
    apply mul_right_cancel₀ hs_ne
    calc
      ((randomEnvironmentEdgeConductance W (-1)).toReal * (v (-1) - v 0)) *
          (randomEnvironmentLeftPrefixSum W N).toReal = -v 0 := hprod
      _ =
          (-v 0 * (randomEnvironmentLeftPrefixSum W N).toReal⁻¹) *
            (randomEnvironmentLeftPrefixSum W N).toReal := by
            field_simp [hs_ne]
  -- Proof comment: the left endpoint now carries boundary value `0`, so flipping the edge
  -- orientation converts the telescoped identity into the left-boundary gap formula.
  calc
    (randomEnvironmentEdgeConductance W (-1)).toReal * (v 0 - v (-1))
        = -((randomEnvironmentEdgeConductance W (-1)).toReal * (v (-1) - v 0)) := by ring
    _ = -(-v 0 * (randomEnvironmentLeftPrefixSum W N).toReal⁻¹) := by rw [hcurrentValue]
    _ = v 0 * (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ := by ring

/-- Helper for Theorem 19.33: the symmetric finite-corridor right-exit probability at `0` is the
left prefix resistance divided by the total left-plus-right prefix resistance, proved directly
from the conserved-current identities. -/
private theorem twoRayRightExitProbability_eq_prefixRatioByCurrents
    (hW : W.IsElliptic) (N : ℕ) :
    let left : ℤ := -((N + 1 : ℕ) : ℤ)
    let right : ℤ := ((N + 1 : ℕ) : ℤ)
    F_A P X ({left} : Set ℤ) 0 right = randomEnvironmentRightExitPrefixRatio W N := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let v : ℤ → ℝ := fun z ↦ F_A P X ({left} : Set ℤ) z right
  let leftSum : ℝ≥0∞ := randomEnvironmentLeftPrefixSum W N
  let rightSum : ℝ≥0∞ := randomEnvironmentRightPrefixSum W N
  have hx : (0 : ℤ) ∉ insert right ({left} : Set ℤ) := by
    simp [left, right]
    omega
  have hharm :
      v 0 = ∫ y, v y ∂((discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) 0) :=
    F_A_average_eq_outside_insert_boundary
      (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
      (A := ({left} : Set ℤ)) (b := right) hx
  have hcurrent :
      (randomEnvironmentEdgeConductance W (-1)).toReal * (v 0 - v (-1)) =
        (randomEnvironmentEdgeConductance W 0).toReal * (v 1 - v 0) :=
    randomEnvironment_harmonicCurrent_eq
      (W := W) hW (u := v) (x := 0) hharm
  have hleftFlux :
      (randomEnvironmentEdgeConductance W (-1)).toReal * (v 0 - v (-1)) =
        v 0 * (leftSum.toReal)⁻¹ := by
    simpa [left, right, v, leftSum] using
      twoRayCorridorLeftFlux_eq_leftBoundaryGap_mul_leftPrefixInv
        (W := W) (P := P) (X := X) hW N
  have hrightFlux :
      (randomEnvironmentEdgeConductance W 0).toReal * (v 1 - v 0) =
        (1 - v 0) * (rightSum.toReal)⁻¹ := by
    simpa [left, right, v, rightSum] using
      twoRayCorridorRightFlux_eq_rightBoundaryGap_mul_rightPrefixInv
        (W := W) (P := P) (X := X) hW N
  have hleftSum_pos : 0 < leftSum.toReal := by
    have hterm0 :
        0 < (randomEnvironmentLeftSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentLeftSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentLeftSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentLeftSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i
  have hrightSum_pos : 0 < rightSum.toReal := by
    have hterm0 :
        0 < (randomEnvironmentRightSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentRightSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentRightSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentRightSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentRightSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i
  have hleftSum_ne : leftSum.toReal ≠ 0 := hleftSum_pos.ne'
  have hrightSum_ne : rightSum.toReal ≠ 0 := hrightSum_pos.ne'
  have hsum_ne : leftSum.toReal + rightSum.toReal ≠ 0 := (add_pos hleftSum_pos hrightSum_pos).ne'
  have hratio :
      v 0 / leftSum.toReal = (1 - v 0) / rightSum.toReal := by
    calc
      v 0 / leftSum.toReal = v 0 * (leftSum.toReal)⁻¹ := by rw [div_eq_mul_inv]
      _ = (1 - v 0) * (rightSum.toReal)⁻¹ := by rw [← hleftFlux, hcurrent, hrightFlux]
      _ = (1 - v 0) / rightSum.toReal := by rw [div_eq_mul_inv]
  have hcross :
      v 0 * rightSum.toReal = (1 - v 0) * leftSum.toReal := by
    have hratio' := hratio
    field_simp [hleftSum_ne, hrightSum_ne] at hratio'
    linarith
  have hfinal :
      v 0 = leftSum.toReal / (leftSum.toReal + rightSum.toReal) := by
    apply (eq_div_iff hsum_ne).2
    linarith
  -- Proof comment: the origin current balance now identifies the right-exit value with the left
  -- prefix resistance divided by the total corridor resistance.
  simpa [left, right, v, leftSum, rightSum, randomEnvironmentRightExitPrefixRatio] using hfinal

/-- Helper for Theorem 19.33: on the symmetric corridor `[-(N + 1), N + 1]`, the right-exit
probability is the complement of the left-exit probability. -/
private theorem twoRayRightExit_eq_one_sub_leftExit
    (hW : W.IsElliptic) (N : ℕ) :
    let left : ℤ := -((N + 1 : ℕ) : ℤ)
    let right : ℤ := ((N + 1 : ℕ) : ℤ)
    F_A P X ({left} : Set ℤ) 0 right =
      1 - F_A P X ({right} : Set ℤ) 0 left := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  have hrightRatio :
      F_A P X ({left} : Set ℤ) 0 right = randomEnvironmentRightExitPrefixRatio W N := by
    simpa [left, right] using
      twoRayRightExitProbability_eq_prefixRatioByCurrents
        (W := W) (P := P) (X := X) hW N
  have hleftRatio :
      F_A P X ({right} : Set ℤ) 0 left = randomEnvironmentLeftExitPrefixRatio W N := by
    simpa [left, right] using
      twoRayLeftExitProbability_eq_prefixRatio
        (W := W) (P := P) (X := X) hW N
  have hratioComp :
      randomEnvironmentRightExitPrefixRatio W N =
        1 - randomEnvironmentLeftExitPrefixRatio W N := by
    have hleftSum_pos : 0 < (randomEnvironmentLeftPrefixSum W N).toReal := by
      have hterm0 :
          0 < (randomEnvironmentLeftSeriesTerm W 0).toReal := by
        exact ENNReal.toReal_pos
          (randomEnvironmentLeftSeriesTerm_pos (W := W) hW 0).ne'
          (randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW 0)
      have hmem : 0 ∈ Finset.range (N + 1) := by simp
      have hsum_pos :
          0 < Finset.sum (Finset.range (N + 1))
            (fun i ↦ (randomEnvironmentLeftSeriesTerm W i).toReal) := by
        exact lt_of_lt_of_le hterm0
          (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
      change 0 <
        (Finset.sum (Finset.range (N + 1))
          (fun i ↦ randomEnvironmentLeftSeriesTerm W i)).toReal
      rw [ENNReal.toReal_sum]
      · exact hsum_pos
      · intro i hi
        exact randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i
    have hrightSum_pos : 0 < (randomEnvironmentRightPrefixSum W N).toReal := by
      have hterm0 :
          0 < (randomEnvironmentRightSeriesTerm W 0).toReal := by
        exact ENNReal.toReal_pos
          (randomEnvironmentRightSeriesTerm_pos (W := W) hW 0).ne'
          (randomEnvironmentRightSeriesTerm_ne_top (W := W) hW 0)
      have hmem : 0 ∈ Finset.range (N + 1) := by simp
      have hsum_pos :
          0 < Finset.sum (Finset.range (N + 1))
            (fun i ↦ (randomEnvironmentRightSeriesTerm W i).toReal) := by
        exact lt_of_lt_of_le hterm0
          (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
      change 0 <
        (Finset.sum (Finset.range (N + 1))
          (fun i ↦ randomEnvironmentRightSeriesTerm W i)).toReal
      rw [ENNReal.toReal_sum]
      · exact hsum_pos
      · intro i hi
        exact randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i
    have hsum_ne :
        (randomEnvironmentLeftPrefixSum W N).toReal +
            (randomEnvironmentRightPrefixSum W N).toReal ≠ 0 :=
      (add_pos hleftSum_pos hrightSum_pos).ne'
    rw [randomEnvironmentRightExitPrefixRatio, randomEnvironmentLeftExitPrefixRatio]
    field_simp [hsum_ne]
    ring
  -- Proof comment: both finite-corridor exit values are already identified with complementary
  -- prefix ratios, so the pathwise complement identity reduces to scalar denominator algebra.
  calc
    F_A P X ({left} : Set ℤ) 0 right
        = randomEnvironmentRightExitPrefixRatio W N := hrightRatio
    _ = 1 - randomEnvironmentLeftExitPrefixRatio W N := hratioComp
    _ = 1 - F_A P X ({right} : Set ℤ) 0 left := by rw [hleftRatio]

/-- Helper for Theorem 19.33: the symmetric finite-corridor right-exit probability at `0` is the
left prefix resistance divided by the total left-plus-right prefix resistance. -/
private theorem twoRayRightExitProbability_eq_prefixRatio
    (hW : W.IsElliptic) (N : ℕ) :
    let left : ℤ := -((N + 1 : ℕ) : ℤ)
    let right : ℤ := ((N + 1 : ℕ) : ℤ)
    F_A P X ({left} : Set ℤ) 0 right = randomEnvironmentRightExitPrefixRatio W N := by
  simpa using
    twoRayRightExitProbability_eq_prefixRatioByCurrents
      (W := W) (P := P) (X := X) hW N

/-- Helper for Theorem 19.33: a nearest-neighbor path started at `1` cannot first hit a negative
wall before it first hits `0`. -/
private theorem integerPath_not_mem_firstHitPathEvent_left_of_startOne
    (Y : ℕ → ℤ) (left : ℤ) (hleft : left < 0) (hstart : Y 0 = 1)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1) :
    (fun n : ℕ ↦ Y n) ∉ firstHitPathEvent ({0} : Set ℤ) left := by
  intro hmem
  rcases hmem with ⟨n, hnleft, havoid⟩
  have hn_eq_left : Y n = left := by simpa using hnleft
  let S : Set ℕ := {m : ℕ | m ≤ n ∧ Y m ≤ 0}
  have hS_nonempty : S.Nonempty := ⟨n, le_rfl, by omega⟩
  let m : ℕ := Nat.find hS_nonempty
  have hm_spec : m ≤ n ∧ Y m ≤ 0 := Nat.find_spec hS_nonempty
  have hm_le_n : m ≤ n := hm_spec.1
  have hm_nonpos : Y m ≤ 0 := hm_spec.2
  have hm_pos : 0 < m := by
    by_contra hm_not_pos
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm_not_pos
    have : Y m = 1 := by simpa [m, hm_zero] using hstart
    omega
  have hm_pred_lt : m - 1 < m := Nat.pred_lt (Nat.ne_of_gt hm_pos)
  have hm_pred_not_nonpos : ¬ Y (m - 1) ≤ 0 := by
    intro hm_pred_nonpos
    have hm_pred_mem : m - 1 ∈ S := by
      exact ⟨le_trans (Nat.sub_le _ _) hm_le_n, hm_pred_nonpos⟩
    have hmin : m ≤ m - 1 := Nat.find_min' hS_nonempty hm_pred_mem
    exact Nat.not_lt_of_ge hmin hm_pred_lt
  have hm_pred_pos : 0 < Y (m - 1) := by
    omega
  have hm_succ : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  rcases hstep (m - 1) with hm_right | hm_left
  · rw [hm_succ] at hm_right
    omega
  · rw [hm_succ] at hm_left
    by_cases hmn : m = n
    · have hm_eq_left : Y m = left := by simpa [hmn] using hn_eq_left
      omega
    · have hm_lt_n : m < n := lt_of_le_of_ne hm_le_n hmn
      have hm_not_mem : Y m ∉ ({left, 0} : Set ℤ) := by
        simpa [or_comm, or_left_comm] using havoid m hm_lt_n
      have hm_ne_zero : Y m ≠ 0 := by
        intro hm_zero
        exact hm_not_mem <| by simp [hm_zero]
      omega

/-- Helper for Theorem 19.33: a nearest-neighbor path started at `-1` cannot first hit a positive
wall before it first hits `0`. -/
private theorem integerPath_not_mem_firstHitPathEvent_right_of_startNegOne
    (Y : ℕ → ℤ) (right : ℤ) (hright : 0 < right) (hstart : Y 0 = -1)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1) :
    (fun n : ℕ ↦ Y n) ∉ firstHitPathEvent ({0} : Set ℤ) right := by
  intro hmem
  rcases hmem with ⟨n, hnright, havoid⟩
  have hn_eq_right : Y n = right := by simpa using hnright
  let S : Set ℕ := {m : ℕ | m ≤ n ∧ 0 ≤ Y m}
  have hS_nonempty : S.Nonempty := ⟨n, le_rfl, by omega⟩
  let m : ℕ := Nat.find hS_nonempty
  have hm_spec : m ≤ n ∧ 0 ≤ Y m := Nat.find_spec hS_nonempty
  have hm_le_n : m ≤ n := hm_spec.1
  have hm_nonneg : 0 ≤ Y m := hm_spec.2
  have hm_pos : 0 < m := by
    by_contra hm_not_pos
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm_not_pos
    have : Y m = -1 := by simpa [m, hm_zero] using hstart
    omega
  have hm_pred_lt : m - 1 < m := Nat.pred_lt (Nat.ne_of_gt hm_pos)
  have hm_pred_not_nonneg : ¬ 0 ≤ Y (m - 1) := by
    intro hm_pred_nonneg
    have hm_pred_mem : m - 1 ∈ S := by
      exact ⟨le_trans (Nat.sub_le _ _) hm_le_n, hm_pred_nonneg⟩
    have hmin : m ≤ m - 1 := Nat.find_min' hS_nonempty hm_pred_mem
    exact Nat.not_lt_of_ge hmin hm_pred_lt
  have hm_pred_neg : Y (m - 1) < 0 := by
    omega
  have hm_succ : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
  rcases hstep (m - 1) with hm_right | hm_left
  · rw [hm_succ] at hm_right
    by_cases hmn : m = n
    · have hm_eq_right : Y m = right := by simpa [hmn] using hn_eq_right
      omega
    · have hm_lt_n : m < n := lt_of_le_of_ne hm_le_n hmn
      have hm_not_mem : Y m ∉ ({right, 0} : Set ℤ) := by
        simpa [or_comm, or_left_comm] using havoid m hm_lt_n
      have hm_ne_zero : Y m ≠ 0 := by
        intro hm_zero
        exact hm_not_mem <| by simp [hm_zero]
      omega
  · rw [hm_succ] at hm_left
    omega

/-- Helper for Theorem 19.33: escaping from `0` to the two-ray boundary before returning to `0`
is exactly the shifted future-path event of first hitting one of the two corridor walls. -/
private theorem integerPath_escapeToTwoRayBoundary_iff_shiftedFutureWallHitUnion
    (Y : ℕ → ℤ) (N : ℕ) (hstart : Y 0 = 0)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1) :
    (∃ n : ℕ, 0 < n ∧ Y n ∈ randomEnvironmentTwoRayBoundary N ∧
      ∀ m : ℕ, 0 < m → m ≤ n → Y m ≠ 0) ↔
      (fun n : ℕ ↦ Y (n + 1)) ∈ firstHitPathEvent ({0} : Set ℤ) (((N + 1 : ℕ) : ℤ)) ∪
        firstHitPathEvent ({0} : Set ℤ) (-((N + 1 : ℕ) : ℤ)) := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  constructor
  · rintro ⟨n, hn_pos, hn_boundary, hnozero⟩
    have hcases : Y n ≤ left ∨ right ≤ Y n := by
      simpa [randomEnvironmentTwoRayBoundary, left, right] using hn_boundary
    rcases hcases with hleft_hit | hright_hit
    · let S : Set ℕ := {k : ℕ | 0 < k ∧ Y k ≤ left}
      have hS_nonempty : S.Nonempty := ⟨n, hn_pos, hleft_hit⟩
      let k : ℕ := Nat.find hS_nonempty
      have hk_spec : 0 < k ∧ Y k ≤ left := Nat.find_spec hS_nonempty
      have hk_pos : 0 < k := hk_spec.1
      have hk_le_left : Y k ≤ left := hk_spec.2
      have hk_le_n : k ≤ n := Nat.find_min' hS_nonempty ⟨hn_pos, hleft_hit⟩
      have hk_pred_gt : left < Y (k - 1) := by
        by_cases hk_one : k = 1
        · rw [hk_one, hstart]
          omega
        · have hk_pred_pos : 0 < k - 1 := by omega
          have hk_pred_not_le : ¬ Y (k - 1) ≤ left := by
            intro hk_pred_le
            have hmin : k ≤ k - 1 := Nat.find_min' hS_nonempty ⟨hk_pred_pos, hk_pred_le⟩
            omega
          exact lt_of_not_ge hk_pred_not_le
      have hk_succ : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk_pos)
      have hk_eq_left : Y k = left := by
        rcases hstep (k - 1) with hk_right | hk_left
        · rw [hk_succ] at hk_right
          omega
        · rw [hk_succ] at hk_left
          omega
      right
      refine ⟨k - 1, ?_, ?_⟩
      · simpa [hk_succ, left] using hk_eq_left
      · intro m hm
        have hm_pos : 0 < m + 1 := Nat.succ_pos _
        have hm_lt_k : m + 1 < k := by omega
        have hm_ne_zero : Y (m + 1) ≠ 0 := hnozero (m + 1) hm_pos (le_trans hm_lt_k.le hk_le_n)
        have hm_gt_left : left < Y (m + 1) := by
          by_contra hm_not_gt
          have hm_le_left : Y (m + 1) ≤ left := le_of_not_gt hm_not_gt
          have hmin : k ≤ m + 1 := Nat.find_min' hS_nonempty ⟨hm_pos, hm_le_left⟩
          exact Nat.not_lt_of_ge hmin hm_lt_k
        have hm_not_mem : Y (m + 1) ∉ ({left, 0} : Set ℤ) := by
          simp [hm_gt_left.ne', hm_ne_zero]
        simpa [left, or_comm, or_left_comm] using hm_not_mem
    · let S : Set ℕ := {k : ℕ | 0 < k ∧ right ≤ Y k}
      have hS_nonempty : S.Nonempty := ⟨n, hn_pos, hright_hit⟩
      let k : ℕ := Nat.find hS_nonempty
      have hk_spec : 0 < k ∧ right ≤ Y k := Nat.find_spec hS_nonempty
      have hk_pos : 0 < k := hk_spec.1
      have hk_right_le : right ≤ Y k := hk_spec.2
      have hk_le_n : k ≤ n := Nat.find_min' hS_nonempty ⟨hn_pos, hright_hit⟩
      have hk_pred_lt : Y (k - 1) < right := by
        by_cases hk_one : k = 1
        · rw [hk_one, hstart]
          omega
        · have hk_pred_pos : 0 < k - 1 := by omega
          have hk_pred_not_ge : ¬ right ≤ Y (k - 1) := by
            intro hk_pred_ge
            have hmin : k ≤ k - 1 := Nat.find_min' hS_nonempty ⟨hk_pred_pos, hk_pred_ge⟩
            omega
          exact lt_of_not_ge hk_pred_not_ge
      have hk_succ : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk_pos)
      have hk_eq_right : Y k = right := by
        rcases hstep (k - 1) with hk_right | hk_left
        · rw [hk_succ] at hk_right
          omega
        · rw [hk_succ] at hk_left
          omega
      left
      refine ⟨k - 1, ?_, ?_⟩
      · simpa [hk_succ, right] using hk_eq_right
      · intro m hm
        have hm_pos : 0 < m + 1 := Nat.succ_pos _
        have hm_lt_k : m + 1 < k := by omega
        have hm_ne_zero : Y (m + 1) ≠ 0 := hnozero (m + 1) hm_pos (le_trans hm_lt_k.le hk_le_n)
        have hm_lt_right : Y (m + 1) < right := by
          by_contra hm_not_lt
          have hm_ge_right : right ≤ Y (m + 1) := le_of_not_gt hm_not_lt
          have hmin : k ≤ m + 1 := Nat.find_min' hS_nonempty ⟨hm_pos, hm_ge_right⟩
          exact Nat.not_lt_of_ge hmin hm_lt_k
        have hm_not_mem : Y (m + 1) ∉ ({right, 0} : Set ℤ) := by
          simp [hm_lt_right.ne, hm_ne_zero]
        simpa [right, or_comm, or_left_comm] using hm_not_mem
  · intro hhit
    rcases hhit with hright_hit | hleft_hit
    · rcases hright_hit with ⟨k, hk_right, hk_avoid⟩
      refine ⟨k + 1, Nat.succ_pos _, ?_, ?_⟩
      · have hk_mem : Y (k + 1) ∈ randomEnvironmentTwoRayBoundary N := by
          change Y (k + 1) ∈ Set.Iic left ∪ Set.Ici right
          right
          have hk_eq_right : Y (k + 1) = right := by
            simpa [right] using hk_right
          have hk_gt_cutoff : (N : ℤ) < Y (k + 1) := by
            rw [hk_eq_right]
            omega
          simpa [right] using hk_gt_cutoff
        exact hk_mem
      · intro m hm_pos hm_le
        by_cases hm_eq : m = k + 1
        · subst hm_eq
          have hright_ne_zero : right ≠ 0 := by omega
          intro hm_zero
          exact hright_ne_zero (hk_right.symm.trans hm_zero)
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
          have hj_lt : j < k := by omega
          have hj_not_mem : Y (j + 1) ∉ ({right, 0} : Set ℤ) := by
            simpa [right, or_comm, or_left_comm] using hk_avoid j hj_lt
          intro hm_zero
          exact hj_not_mem <| by simp [hm_zero]
    · rcases hleft_hit with ⟨k, hk_left, hk_avoid⟩
      refine ⟨k + 1, Nat.succ_pos _, ?_, ?_⟩
      · have hk_mem : Y (k + 1) ∈ randomEnvironmentTwoRayBoundary N := by
          change Y (k + 1) ∈ Set.Iic left ∪ Set.Ici right
          left
          simpa [left] using hk_left.le
        exact hk_mem
      · intro m hm_pos hm_le
        by_cases hm_eq : m = k + 1
        · subst hm_eq
          have hleft_ne_zero : left ≠ 0 := by omega
          intro hm_zero
          exact hleft_ne_zero (hk_left.symm.trans hm_zero)
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
          have hj_lt : j < k := by omega
          have hj_not_mem : Y (j + 1) ∉ ({left, 0} : Set ℤ) := by
            simpa [left, or_comm, or_left_comm] using hk_avoid j hj_lt
          intro hm_zero
          exact hj_not_mem <| by simp [hm_zero]

/-- Helper for Theorem 19.33: under the path law started from `1`, the left-wall first-hit path
event has zero mass because the walk must cross `0` before reaching the negative wall. -/
private theorem realizationPathKernel_leftWall_real_eq_zero_from_startOne
    (W : RandomEnvironment) [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (N : ℕ) :
    (realizationPathKernel (P := P) (X := X) (1 : ℤ)).real
        (firstHitPathEvent ({0} : Set ℤ) (-((N + 1 : ℕ) : ℤ))) = 0 := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let μ : Measure Ω := (P 1 : Measure Ω)
  let path : Ω → ℕ → ℤ := fun ω n ↦ X n ω
  have hpath_meas : Measurable path := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    let hReal :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
      inferInstance
    exact hReal.measurable_process n
  have hbad_ae : ∀ᵐ ω ∂μ, ω ∈ (path ⁻¹'
      firstHitPathEvent ({0} : Set ℤ) left)ᶜ := by
    filter_upwards [initialState_ae_eq_start_local
      (p := randomEnvironmentTransitionMatrix W) (P := P) (X := X) (1 : ℤ),
      randomEnvironmentWalk_ae_nearestNeighbor (W := W) (P := P) (X := X) (1 : ℤ)] with
      ω hstart hstep
    simp [path]
    exact integerPath_not_mem_firstHitPathEvent_left_of_startOne
      (Y := fun n ↦ X n ω) left (by omega) hstart hstep
  have hpreimage_zero :
      μ (path ⁻¹' firstHitPathEvent ({0} : Set ℤ) left) = 0 := by
    simpa [ae_iff] using hbad_ae
  calc
    (realizationPathKernel (P := P) (X := X) (1 : ℤ)).real
        (firstHitPathEvent ({0} : Set ℤ) left)
        = (μ (path ⁻¹' firstHitPathEvent ({0} : Set ℤ) left)).toReal := by
            change (((μ.map path) (firstHitPathEvent ({0} : Set ℤ) left)).toReal) = _
            rw [Measure.map_apply hpath_meas
              (firstHitPathEvent_measurable ({0} : Set ℤ) left)]
    _ = 0 := by rw [hpreimage_zero]; simp

/-- Helper for Theorem 19.33: under the path law started from `-1`, the right-wall first-hit
path event has zero mass because the walk must cross `0` before reaching the positive wall. -/
private theorem realizationPathKernel_rightWall_real_eq_zero_from_startNegOne
    (W : RandomEnvironment) [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (N : ℕ) :
    (realizationPathKernel (P := P) (X := X) (-1 : ℤ)).real
        (firstHitPathEvent ({0} : Set ℤ) (((N + 1 : ℕ) : ℤ))) = 0 := by
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let μ : Measure Ω := (P (-1) : Measure Ω)
  let path : Ω → ℕ → ℤ := fun ω n ↦ X n ω
  have hpath_meas : Measurable path := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    let hReal :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
      inferInstance
    exact hReal.measurable_process n
  have hbad_ae : ∀ᵐ ω ∂μ, ω ∈ (path ⁻¹'
      firstHitPathEvent ({0} : Set ℤ) right)ᶜ := by
    filter_upwards [initialState_ae_eq_start_local
      (p := randomEnvironmentTransitionMatrix W) (P := P) (X := X) (-1 : ℤ),
      randomEnvironmentWalk_ae_nearestNeighbor (W := W) (P := P) (X := X) (-1 : ℤ)] with
      ω hstart hstep
    simp [path]
    exact integerPath_not_mem_firstHitPathEvent_right_of_startNegOne
      (Y := fun n ↦ X n ω) right (by omega) hstart hstep
  have hpreimage_zero :
      μ (path ⁻¹' firstHitPathEvent ({0} : Set ℤ) right) = 0 := by
    simpa [ae_iff] using hbad_ae
  calc
    (realizationPathKernel (P := P) (X := X) (-1 : ℤ)).real
        (firstHitPathEvent ({0} : Set ℤ) right)
        = (μ (path ⁻¹' firstHitPathEvent ({0} : Set ℤ) right)).toReal := by
            change (((μ.map path) (firstHitPathEvent ({0} : Set ℤ) right)).toReal) = _
            rw [Measure.map_apply hpath_meas
              (firstHitPathEvent_measurable ({0} : Set ℤ) right)]
    _ = 0 := by rw [hpreimage_zero]; simp

/-- Helper for Theorem 19.33: multiplying the finite two-ray escape probability by the row
conductance at `0` gives the sum of the reciprocal left and right Solomon prefix resistances. -/
private theorem twoRayBoundaryConductance_mul_escape_eq_prefixInvSum
    (hW : W.IsElliptic) (N : ℕ) :
    conductance (randomEnvironmentConductance W) 0 *
        escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N) =
      (randomEnvironmentLeftPrefixSum W N)⁻¹ + (randomEnvironmentRightPrefixSum W N)⁻¹ := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let Bright : Set (ℕ → ℤ) := firstHitPathEvent ({0} : Set ℤ) right
  let Bleft : Set (ℕ → ℤ) := firstHitPathEvent ({0} : Set ℤ) left
  let Bwall : Set (ℕ → ℤ) := Bright ∪ Bleft
  let rowMass : ℤ → ℝ := fun z ↦
    (realizationPathKernel (P := P) (X := X) z).real Bwall
  let p : ℤ → ℤ → ℝ≥0∞ := randomEnvironmentTransitionMatrix W
  have hwall_meas : MeasurableSet Bwall := by
    exact (firstHitPathEvent_measurable ({0} : Set ℤ) right).union
      (firstHitPathEvent_measurable ({0} : Set ℤ) left)
  have hescape_ae :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω ∈ randomEnvironmentTwoRayBoundary N ∧
          ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ 0} =ᵐ[(P 0 : Measure Ω)]
        ((shiftedFuturePath X 1) ⁻¹' Bwall) := by
    filter_upwards [initialState_ae_eq_start_local
      (p := randomEnvironmentTransitionMatrix W) (P := P) (X := X) (0 : ℤ),
      randomEnvironmentWalk_ae_nearestNeighbor (W := W) (P := P) (X := X) (0 : ℤ)] with
      ω hstart hstep
    exact propext <| by
      change
        (∃ n : ℕ, 0 < n ∧ X n ω ∈ randomEnvironmentTwoRayBoundary N ∧
          ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ 0) ↔
          ω ∈ (shiftedFuturePath X 1 ⁻¹' Bright ∪ shiftedFuturePath X 1 ⁻¹' Bleft)
      simpa [Bright, Bleft, right, left, shiftedFuturePath, Set.mem_preimage, Set.mem_union] using
        (integerPath_escapeToTwoRayBoundary_iff_shiftedFutureWallHitUnion
          (Y := fun n ↦ X n ω) (N := N) hstart hstep)
  have hescape_real :
      (escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N)).toReal =
        ∫ z, rowMass z ∂((discreteMatrixKernel p) 0) := by
    calc
      (escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N)).toReal
          = (P 0 : Measure Ω).real
              {ω | ∃ n : ℕ, 0 < n ∧ X n ω ∈ randomEnvironmentTwoRayBoundary N ∧
                  ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ 0} := by
                rw [escapeToSetProbability_def, Measure.real_def]
      _ = (P 0 : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' Bwall) := by
            exact MeasureTheory.measureReal_congr hescape_ae
      _ = ∫ z, (realizationPathKernel (P := P) (X := X) z).real Bwall
            ∂((discreteMatrixKernel p) 0) := by
              simpa [rowMass, p] using
                futurePathHit_real_eq_pathKernelAverage
                  (p := p) (P := P) (X := X) Bwall hwall_meas (0 : ℤ)
  have hrowMass_one :
      rowMass 1 = F_A P X ({0} : Set ℤ) 1 right := by
    let κ : Measure (ℕ → ℤ) := realizationPathKernel (P := P) (X := X) (1 : ℤ)
    have hBleft_zero_real :
        κ.real Bleft = 0 := by
      simpa [κ, Bleft, left] using
        realizationPathKernel_leftWall_real_eq_zero_from_startOne
          (W := W) (P := P) (X := X) N
    have hBleft_zero :
        κ Bleft = 0 := by
      have hκ_ne_top : κ Bleft ≠ ∞ := by
        change
          ((P 1 : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω)) Bleft ≠ ∞
        exact measure_ne_top _ _
      rcases (ENNReal.toReal_eq_zero_iff (κ Bleft)).mp
          (by simpa [Measure.real_def] using hBleft_zero_real) with hzero | htop
      · exact hzero
      · exact False.elim <| hκ_ne_top htop
    have hUnion :
        κ Bwall = κ Bright := by
      refine le_antisymm ?_ (measure_mono (by intro ξ hξ; exact Or.inl hξ))
      calc
        κ Bwall ≤ κ Bright + κ Bleft := measure_union_le _ _
        _ = κ Bright := by simp [hBleft_zero]
    calc
      rowMass 1 = (κ Bwall).toReal := by rfl
      _ = (κ Bright).toReal := by rw [hUnion]
      _ = F_A P X ({0} : Set ℤ) 1 right := by
            simpa [κ, Measure.real_def] using
              realizationPathKernel_real_firstHitPathEvent_eq_F_A
                (p := p) (P := P) (X := X) ({0} : Set ℤ) right (1 : ℤ)
  have hrowMass_negOne :
      rowMass (-1) = F_A P X ({0} : Set ℤ) (-1) left := by
    let κ : Measure (ℕ → ℤ) := realizationPathKernel (P := P) (X := X) (-1 : ℤ)
    have hBright_zero_real :
        κ.real Bright = 0 := by
      simpa [κ, Bright, right] using
        realizationPathKernel_rightWall_real_eq_zero_from_startNegOne
          (W := W) (P := P) (X := X) N
    have hBright_zero :
        κ Bright = 0 := by
      have hκ_ne_top : κ Bright ≠ ∞ := by
        change
          ((P (-1) : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω)) Bright ≠ ∞
        exact measure_ne_top _ _
      rcases (ENNReal.toReal_eq_zero_iff (κ Bright)).mp
          (by simpa [Measure.real_def] using hBright_zero_real) with hzero | htop
      · exact hzero
      · exact False.elim <| hκ_ne_top htop
    have hUnion :
        κ Bwall = κ Bleft := by
      refine le_antisymm ?_ (measure_mono (by intro ξ hξ; exact Or.inr hξ))
      calc
        κ Bwall ≤ κ Bright + κ Bleft := measure_union_le _ _
        _ = κ Bleft := by simp [hBright_zero]
    calc
      rowMass (-1) = (κ Bwall).toReal := by rfl
      _ = (κ Bleft).toReal := by rw [hUnion]
      _ = F_A P X ({0} : Set ℤ) (-1) left := by
            simpa [κ, Measure.real_def] using
              realizationPathKernel_real_firstHitPathEvent_eq_F_A
                (p := p) (P := P) (X := X) ({0} : Set ℤ) left (-1 : ℤ)
  have hrow_integral :
      ∫ z, rowMass z ∂((discreteMatrixKernel p) 0) =
        (p 0 1).toReal * rowMass 1 + (p 0 (-1)).toReal * rowMass (-1) := by
    have hnorm_support :
        Function.support (fun z : ℤ ↦ (p 0 z).toReal * ‖rowMass z‖) ⊆ ({-1, 1} : Set ℤ) := by
      intro z hz
      by_cases hz_one : z = 1
      · simp [hz_one]
      · by_cases hz_negOne : z = -1
        · simp [hz_negOne]
        · have hpz : p 0 z = 0 := by
            simp [p, randomEnvironmentTransitionMatrix, hz_one, hz_negOne]
          have : (p 0 z).toReal * ‖rowMass z‖ = 0 := by simp [hpz]
          exact False.elim (hz <| by simpa [this])
    have hnorm :
        Summable (fun z : ℤ ↦ (p 0 z).toReal * ‖rowMass z‖) :=
      summable_of_hasFiniteSupport ((Set.finite_singleton (1 : ℤ)).insert (-1) |>.subset
        (by simpa [Set.pair_comm] using hnorm_support))
    have hsupport :
        ∀ z ∉ ({-1, 1} : Finset ℤ), (p 0 z).toReal * rowMass z = 0 := by
      intro z hz
      have hz_one : z ≠ 1 := by intro hz'; exact hz (by simp [hz'])
      have hz_negOne : z ≠ -1 := by intro hz'; exact hz (by simp [hz'])
      simp [p, randomEnvironmentTransitionMatrix, hz_one, hz_negOne]
    calc
      ∫ z, rowMass z ∂((discreteMatrixKernel p) 0)
          = ∑' z : ℤ, (p 0 z).toReal * rowMass z := by
              exact integral_discreteMatrixKernel_eq_tsum p
                (randomEnvironmentTransitionMatrix_isStochastic W) rowMass (0 : ℤ) hnorm
      _ = (p 0 (-1)).toReal * rowMass (-1) + (p 0 1).toReal * rowMass 1 := by
            rw [tsum_eq_sum hsupport]
            simp [p]
      _ = (p 0 1).toReal * rowMass 1 + (p 0 (-1)).toReal * rowMass (-1) := by ring
  have hrow_conductance_real :
      (conductance (randomEnvironmentConductance W) 0).toReal *
          (escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N)).toReal =
        (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ +
          (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
    have hcond_ne_zero :
        conductance (randomEnvironmentConductance W) 0 ≠ 0 :=
      ne_of_gt (randomEnvironmentConductance_vertexWeight_pos (W := W) hW 0)
    have hcond_ne_top :
        conductance (randomEnvironmentConductance W) 0 ≠ ∞ :=
      (randomEnvironmentConductance_vertexWeight_lt_top (W := W) hW 0).ne
    have hcond_toReal_ne_zero :
        (conductance (randomEnvironmentConductance W) 0).toReal ≠ 0 := by
      exact ENNReal.toReal_ne_zero.mpr ⟨hcond_ne_zero, hcond_ne_top⟩
    have hrightWeight :
        (p 0 1).toReal =
          (randomEnvironmentEdgeConductance W 0).toReal /
            (conductance (randomEnvironmentConductance W) 0).toReal := by
      simpa [p, conductanceTransitionMatrix_apply, ENNReal.toReal_div, hcond_ne_zero,
        hcond_ne_top] using
        congrArg ENNReal.toReal
          (randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix
            (W := W) hW 0 1)
    have hleftWeight :
        (p 0 (-1)).toReal =
          (randomEnvironmentEdgeConductance W (-1)).toReal /
            (conductance (randomEnvironmentConductance W) 0).toReal := by
      simpa [p, conductanceTransitionMatrix_apply, ENNReal.toReal_div, hcond_ne_zero,
        hcond_ne_top] using
        congrArg ENNReal.toReal
          (randomEnvironmentTransitionMatrix_eq_conductanceTransitionMatrix
            (W := W) hW 0 (-1))
    have hmulRight :
        (conductance (randomEnvironmentConductance W) 0).toReal * (p 0 1).toReal =
          (randomEnvironmentEdgeConductance W 0).toReal := by
      rw [hrightWeight]
      field_simp [hcond_toReal_ne_zero]
    have hmulLeft :
        (conductance (randomEnvironmentConductance W) 0).toReal * (p 0 (-1)).toReal =
          (randomEnvironmentEdgeConductance W (-1)).toReal := by
      rw [hleftWeight]
      field_simp [hcond_toReal_ne_zero]
    calc
      (conductance (randomEnvironmentConductance W) 0).toReal *
          (escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N)).toReal
          = (conductance (randomEnvironmentConductance W) 0).toReal *
              ∫ z, rowMass z ∂((discreteMatrixKernel p) 0) := by rw [hescape_real]
      _ =
          (conductance (randomEnvironmentConductance W) 0).toReal *
              ((p 0 1).toReal * rowMass 1 + (p 0 (-1)).toReal * rowMass (-1)) := by
                rw [hrow_integral]
      _ =
          (conductance (randomEnvironmentConductance W) 0).toReal * (p 0 1).toReal * rowMass 1 +
            (conductance (randomEnvironmentConductance W) 0).toReal *
              (p 0 (-1)).toReal * rowMass (-1) := by ring
      _ =
          (randomEnvironmentEdgeConductance W 0).toReal * rowMass 1 +
            (randomEnvironmentEdgeConductance W (-1)).toReal * rowMass (-1) := by
              rw [hmulRight, hmulLeft]
      _ =
          (randomEnvironmentEdgeConductance W 0).toReal *
              F_A P X ({0} : Set ℤ) 1 right +
            (randomEnvironmentEdgeConductance W (-1)).toReal *
              F_A P X ({0} : Set ℤ) (-1) left := by
              rw [hrowMass_one, hrowMass_negOne]
      _ =
          (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ +
            (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
              rw [rightBoundaryFA_mul_edge_eq_rightPrefixInv (W := W) (P := P) (X := X) hW N,
                leftBoundaryFA_mul_edge_eq_leftPrefixInv (W := W) (P := P) (X := X) hW N,
                add_comm]
  have hleftPrefix_pos : 0 < (randomEnvironmentLeftPrefixSum W N).toReal := by
    have hterm0 :
        0 < (randomEnvironmentLeftSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentLeftSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentLeftSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentLeftSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i
  have hrightPrefix_pos : 0 < (randomEnvironmentRightPrefixSum W N).toReal := by
    have hterm0 :
        0 < (randomEnvironmentRightSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentRightSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentRightSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentRightSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentRightSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i
  have hleftInv_ne_top : (randomEnvironmentLeftPrefixSum W N)⁻¹ ≠ ∞ := by
    exact ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.toReal_pos_iff.mp hleftPrefix_pos).1)
  have hrightInv_ne_top : (randomEnvironmentRightPrefixSum W N)⁻¹ ≠ ∞ := by
    exact ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.toReal_pos_iff.mp hrightPrefix_pos).1)
  have hright_sum_ne_top :
      (randomEnvironmentLeftPrefixSum W N)⁻¹ + (randomEnvironmentRightPrefixSum W N)⁻¹ ≠ ∞ := by
    exact (ENNReal.add_ne_top).2 ⟨hleftInv_ne_top, hrightInv_ne_top⟩
  have hprod_ne_top :
      conductance (randomEnvironmentConductance W) 0 *
        escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (randomEnvironmentConductance_vertexWeight_lt_top (W := W) hW 0).ne
      (measure_ne_top _ _)
  exact (ENNReal.toReal_eq_toReal_iff' hprod_ne_top hright_sum_ne_top).mp <| by
    rw [ENNReal.toReal_add hleftInv_ne_top hrightInv_ne_top,
      ENNReal.toReal_inv, ENNReal.toReal_inv]
    simpa [ENNReal.toReal_mul,
      (randomEnvironmentConductance_vertexWeight_lt_top (W := W) hW 0).ne,
      measure_ne_top _ _] using hrow_conductance_real

/-- Helper for Theorem 19.33: the right Solomon series is the supremum of its finite prefix
sums. -/
private theorem randomEnvironment_rightSeries_eq_iSup_prefix (W : RandomEnvironment) :
    R⁺[W] = ⨆ N : ℕ, Finset.sum (Finset.range N) (fun i ↦ randomEnvironmentRightSeriesTerm W i) := by
  rw [randomEnvironmentRightSeries_def]
  exact ENNReal.tsum_eq_iSup_nat

/-- Helper for Theorem 19.33: the left Solomon series is the supremum of its finite prefix
sums. -/
private theorem randomEnvironment_leftSeries_eq_iSup_prefix (W : RandomEnvironment) :
    R⁻[W] = ⨆ N : ℕ, Finset.sum (Finset.range N) (fun i ↦ randomEnvironmentLeftSeriesTerm W i) := by
  rw [randomEnvironmentLeftSeries_def]
  exact ENNReal.tsum_eq_iSup_nat

/-- Helper for Theorem 19.33: the right Solomon series is also the supremum of the shifted
prefix sums `∑_{i < N + 1}` used by the finite-boundary formulas. -/
private theorem randomEnvironment_rightSeries_eq_iSup_prefixSucc (W : RandomEnvironment) :
    R⁺[W] = ⨆ N : ℕ, randomEnvironmentRightPrefixSum W N := by
  -- Proof comment: this is just the same `ℕ`-indexed supremum formula as before, rewritten in
  -- the stable `N + 1` prefix-sum owner used by the corridor identities.
  rw [randomEnvironmentRightSeries_def]
  simpa [randomEnvironmentRightPrefixSum] using
    (ENNReal.tsum_eq_iSup_nat'
      (f := randomEnvironmentRightSeriesTerm W)
      (N := fun n ↦ n + 1)
      (by simpa using tendsto_add_atTop_nat 1))

/-- Helper for Theorem 19.33: the left Solomon series is also the supremum of the shifted prefix
sums `∑_{i < N + 1}` used by the finite-boundary formulas. -/
private theorem randomEnvironment_leftSeries_eq_iSup_prefixSucc (W : RandomEnvironment) :
    R⁻[W] = ⨆ N : ℕ, randomEnvironmentLeftPrefixSum W N := by
  -- Proof comment: rewrite the textbook left series by the same shifted finite prefixes that
  -- appear in the two-ray exit-ratio formulas.
  rw [randomEnvironmentLeftSeries_def]
  simpa [randomEnvironmentLeftPrefixSum] using
    (ENNReal.tsum_eq_iSup_nat'
      (f := randomEnvironmentLeftSeriesTerm W)
      (N := fun n ↦ n + 1)
      (by simpa using tendsto_add_atTop_nat 1))

-- Proof sketch: the two rays `(-∞, 0]` and `[0, ∞)` form parallel branches of the bridge
-- conductance network `randomEnvironmentConductance W`. Their branch resistances are exactly the
-- source-facing Solomon series `R_w^-` and `R_w^+`, so the Chapter 19 effective resistance is the
-- reciprocal of the sum of the branch conductances.
/-- Via the environment-to-conductance bridge, the Chapter 19 effective resistance from `0` to
infinity is the parallel combination of the source series `R_w^-` and `R_w^+` for an elliptic
environment, stated directly under the canonical RWRE owner from Definition 19.34. -/
theorem randomEnvironment_effectiveResistanceToInfinity_eq_parallel
    (hW : W.IsElliptic) :
    effectiveResistanceToInfinity (randomEnvironmentConductance W) P X 0 =
      ((R⁻[W])⁻¹ + (R⁺[W])⁻¹)⁻¹ := by
  -- Route correction: the earlier first-step slice decomposition isolated the right events, but
  -- it still needed a future-event restart theorem. The source-aligned route now has the missing
  -- event/F_A adapter available, so the remaining task is only the finite path-network transport.
  rw [effectiveResistanceToInfinity,
    randomEnvironment_effectiveConductanceToInfinity_eq_iInf_escapeToTwoRayBoundary
      (W := W) (P := P) (X := X) hW]
  -- Proof comment: the remaining task is now purely finite-dimensional. For each cutoff `N`, one
  -- must compute the escape-to-two-ray term on `[-(N + 1), N + 1]` as the parallel sum of the
  -- left and right path conductances, then pass from the partial sums to `R⁻[W]` and `R⁺[W]`.
  -- Route correction: the local current lemma `randomEnvironment_harmonicCurrent_eq` now replaces
  -- the earlier uniqueness-based profile search, so the remaining blocker is only the telescoping
  -- and first-step packaging of the one-sided and symmetric `F_A` surfaces.
  -- TODO: prove the finite-boundary identity
  -- `conductance ... 0 * escapeToSetProbability ... (randomEnvironmentTwoRayBoundary N)
  --    = (∑ i in Finset.range (N + 1), randomEnvironmentLeftSeriesTerm W i)⁻¹
  --      + (∑ i in Finset.range (N + 1), randomEnvironmentRightSeriesTerm W i)⁻¹`
  -- by telescoping the constant-current relation, and then identify the resulting `iInf`
  -- with `(R⁻[W])⁻¹ + (R⁺[W])⁻¹` using the new prefix-`iSup` lemmas above.
  have hcond_ne_zero :
      conductance (randomEnvironmentConductance W) 0 ≠ 0 :=
    ne_of_gt (randomEnvironmentConductance_vertexWeight_pos (W := W) hW 0)
  have hcond_ne_top :
      conductance (randomEnvironmentConductance W) 0 ≠ ∞ :=
    (randomEnvironmentConductance_vertexWeight_lt_top (W := W) hW 0).ne
  rw [ENNReal.mul_iInf_of_ne hcond_ne_zero hcond_ne_top]
  have hboundary :
      (⨅ N : ℕ,
          conductance (randomEnvironmentConductance W) 0 *
            escapeToSetProbability P X 0 (randomEnvironmentTwoRayBoundary N))
        =
      ⨅ N : ℕ,
        (randomEnvironmentLeftPrefixSum W N)⁻¹ + (randomEnvironmentRightPrefixSum W N)⁻¹ := by
    refine iInf_congr ?_
    intro N
    simpa using
      twoRayBoundaryConductance_mul_escape_eq_prefixInvSum
        (W := W) (P := P) (X := X) hW N
  rw [hboundary]
  have hleftPrefix_mono : Monotone (fun N : ℕ ↦ randomEnvironmentLeftPrefixSum W N) := by
    intro M N hMN
    exact Finset.sum_le_sum_of_subset
      (Finset.range_subset_range.2 (Nat.succ_le_succ hMN))
  have hrightPrefix_mono : Monotone (fun N : ℕ ↦ randomEnvironmentRightPrefixSum W N) := by
    intro M N hMN
    exact Finset.sum_le_sum_of_subset
      (Finset.range_subset_range.2 (Nat.succ_le_succ hMN))
  have hsum_iInf :
      (⨅ N : ℕ, (randomEnvironmentLeftPrefixSum W N)⁻¹) +
          (⨅ N : ℕ, (randomEnvironmentRightPrefixSum W N)⁻¹)
        =
      ⨅ N : ℕ, (randomEnvironmentLeftPrefixSum W N)⁻¹ +
          (randomEnvironmentRightPrefixSum W N)⁻¹ := by
    exact ENNReal.iInf_add_iInf fun i j ↦ by
      refine ⟨max i j, ?_⟩
      exact add_le_add
        (ENNReal.inv_le_inv' (hleftPrefix_mono (le_max_left i j)))
        (ENNReal.inv_le_inv' (hrightPrefix_mono (le_max_right i j)))
  rw [← hsum_iInf, ← ENNReal.inv_iSup (fun N : ℕ ↦ randomEnvironmentLeftPrefixSum W N),
    ← ENNReal.inv_iSup (fun N : ℕ ↦ randomEnvironmentRightPrefixSum W N),
    randomEnvironment_leftSeries_eq_iSup_prefixSucc,
    randomEnvironment_rightSeries_eq_iSup_prefixSucc]

/-- Helper for Theorem 19.33: after transporting the RWRE realization to the conductance walk,
the Chapter 19 effective-conductance criterion characterizes recurrence of the state `0`. -/
theorem randomEnvironmentStateZeroRecurrent_iff_effectiveConductanceToInfinity_eq_zero
    (hW : W.IsElliptic) :
    IsRecurrentState P X 0 ↔
      effectiveConductanceToInfinity (randomEnvironmentConductance W) P X 0 = 0 := by
  letI :
      IsRandomWalkWithWeights
        (conductanceTransitionMatrix (randomEnvironmentConductance W))
        (randomEnvironmentConductance W) :=
    randomEnvironmentConductance_isRandomWalkWithWeights (W := W) hW
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (conductanceTransitionMatrix (randomEnvironmentConductance W)) ^ n) P X :=
    isMarkovProcessRealization_randomEnvironmentConductance
      (W := W) (P := P) (X := X) hW
  -- Proof comment: the generic Chapter 19 recurrence criterion applies directly once the
  -- environment walk is rewritten as the normalized conductance walk built above.
  exact
    isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero
      (p := conductanceTransitionMatrix (randomEnvironmentConductance W))
      (C := randomEnvironmentConductance W) (P := P) (X := X) (x₁ := 0)

/-- Helper for Theorem 19.33: recurrence of the state `0` is equivalently infinite effective
resistance in the environment-derived conductance network. -/
theorem randomEnvironmentStateZeroRecurrent_iff_effectiveResistanceToInfinity_eq_top
    (hW : W.IsElliptic) :
    IsRecurrentState P X 0 ↔
      effectiveResistanceToInfinity (randomEnvironmentConductance W) P X 0 = ∞ := by
  -- Proof comment: combine the local recurrence/effective-conductance criterion with the owner
  -- equivalence between zero effective conductance and infinite effective resistance.
  rw [randomEnvironmentStateZeroRecurrent_iff_effectiveConductanceToInfinity_eq_zero
    (W := W) (P := P) (X := X) hW]
  exact
    effectiveConductanceToInfinity_eq_zero_iff_effectiveResistanceToInfinity_eq_top
      (C := randomEnvironmentConductance W) (P := P) (X := X) (x₁ := 0)

/-- Helper for Theorem 19.33: if at least one Solomon series is finite, then irreducibility and
the finite parallel-resistance expression force every state to be transient. -/
private theorem randomEnvironment_allStatesTransient_of_oneSeries_finite
    (hW : W.IsElliptic) (hfinite : R⁻[W] < ∞ ∨ R⁺[W] < ∞) :
    ∀ k : ℤ, IsTransientState P X k := by
  rcases randomEnvironment_recurrent_or_allStatesTransient (W := W) (P := P) (X := X) hW with
    hrec | htrans
  · -- Proof comment: if the chain were recurrent, state `0` would have infinite effective
    -- resistance, contradicting the already-stated parallel formula together with one finite
    -- branch series.
    have hres_lt_top :
        effectiveResistanceToInfinity (randomEnvironmentConductance W) P X 0 < ∞ := by
      rw [randomEnvironment_effectiveResistanceToInfinity_eq_parallel (W := W) (P := P) (X := X) hW]
      exact randomEnvironment_parallelResistance_lt_top_of_oneSeries_lt_top
        (W := W) hW hfinite
    have hrec0 : IsRecurrentState P X 0 := hrec 0
    have hres_top :
        effectiveResistanceToInfinity (randomEnvironmentConductance W) P X 0 = ∞ :=
      (randomEnvironmentStateZeroRecurrent_iff_effectiveResistanceToInfinity_eq_top
        (W := W) (P := P) (X := X) hW).1 hrec0
    exact False.elim ((ne_of_lt hres_lt_top) hres_top)
  · exact htrans

/-- Helper for Theorem 19.33: if both Solomon series diverge, then the bridge resistance formula
specializes to infinite effective resistance at `0`. -/
private theorem randomEnvironment_effectiveResistanceToInfinity_eq_top_of_bothSeries_eq_top
    (hW : W.IsElliptic) (hleft : R⁻[W] = ∞) (hright : R⁺[W] = ∞) :
    effectiveResistanceToInfinity (randomEnvironmentConductance W) P X 0 = ∞ := by
  -- Proof comment: substitute the divergent series values into the parallel-resistance formula.
  rw [randomEnvironment_effectiveResistanceToInfinity_eq_parallel (W := W) (P := P) (X := X) hW,
    hleft, hright]
  simp

/-- Helper for Theorem 19.33: if the RWRE is recurrent at the origin, then every integer is hit
almost surely from `0`. -/
theorem randomEnvironmentHitsEveryInteger_of_recurrent
    (hW : W.IsElliptic) (hrec : IsRecurrentMarkovChain P X) (k : ℤ) :
    (F[P, X]) 0 k = 1 := by
  -- Proof comment: `hrec` already gives recurrence of the base state `0`, and Theorem 17.35
  -- upgrades the explicit positive communication probability from `0` to `k` to probability one.
  have hrec0 : IsRecurrentState P X 0 := hrec 0
  have hhitPos : 0 < (F[P, X]) 0 k :=
    randomEnvironmentEverHitsProbability_pos_from_zero
      (W := W) (P := P) (X := X) hW k
  exact
    everHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n)
      (P := P) (X := X) hrec0 hhitPos

/-- Helper for Theorem 19.33: irreducibility upgrades recurrence of the origin to recurrence of
the whole elliptic RWRE on `ℤ`. -/
private theorem randomEnvironment_recurrent_of_recurrentZero
    (hW : W.IsElliptic) (hrec0 : IsRecurrentState P X 0) :
    IsRecurrentMarkovChain P X := by
  intro k
  -- Proof comment: Theorem 17.35 transports recurrence from `0` to any state that is hit from
  -- `0` with positive probability, and the monotone-path helper provides that positivity.
  exact
    isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
      (κ := fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n)
      (P := P) (X := X) hrec0
      (randomEnvironmentEverHitsProbability_pos_from_zero
        (W := W) (P := P) (X := X) hW k)


/-- Helper for Theorem 19.33: the positive-time hit event of a fixed state is measurable. -/
private theorem measurableSet_exists_pos_eq
    (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (x : ℤ) :
    MeasurableSet {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  classical
  let A : ℕ → Set Ω := fun n ↦ if 0 < n then X n ⁻¹' ({x} : Set ℤ) else ∅
  have hA :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x} = ⋃ n : ℕ, A n := by
    ext ω
    simp [A]
  rw [hA]
  refine MeasurableSet.iUnion ?_
  intro n
  by_cases hn : 0 < n
  · simpa [A, hn] using
      (hReal.measurable_process n) (MeasurableSet.singleton x)
  · simp [A, hn]

/-- Helper for Theorem 19.33: if the Chapter 17 ever-hit probability of `x` from `0` is `1`,
then the walk hits `x` at a positive time almost surely. -/
private theorem ae_exists_pos_eq_of_everHitsProbability_eq_one
    (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (x : ℤ) (hhit : (F[P, X]) 0 x = 1) :
    ∀ᵐ ω ∂(P 0 : Measure Ω), ∃ n : ℕ, 0 < n ∧ X n ω = x := by
  -- Proof comment: rewrite `F[P, X]` as the probability of the positive-time hit event and then
  -- convert probability one into an almost-sure statement.
  let E : Set Ω := {ω | ∃ n : ℕ, 0 < n ∧ X n ω = x}
  have hE_meas : MeasurableSet E := measurableSet_exists_pos_eq W P X x
  apply (mem_ae_iff_prob_eq_one hE_meas).2
  exact ENNReal.toReal_eq_one_iff _ |>.mp <|
    by simpa [E, everHitsProbability_def, Measure.real_def] using hhit

/-- Helper for Theorem 19.33: if every integer has Chapter 17 ever-hit probability `1` from `0`,
then almost every path hits every positive and negative integer at some positive time. -/
private theorem ae_hitsEveryInteger_of_forall_everHitsProbability_eq_one
    (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (hhit : ∀ k : ℤ, (F[P, X]) 0 k = 1) :
    ∀ᵐ ω ∂(P 0 : Measure Ω),
      (∀ m : ℕ, ∃ n : ℕ, X n ω = -((m : ℤ))) ∧
        ∀ m : ℕ, ∃ n : ℕ, X n ω = m := by
  -- Proof comment: upgrade the one-state almost-sure hit statement to all integers by taking the
  -- countable intersection over `ℕ` on the positive and negative sides separately.
  have hneg :
      ∀ᵐ ω ∂(P 0 : Measure Ω), ∀ m : ℕ, ∃ n : ℕ, 0 < n ∧ X n ω = -((m : ℤ)) := by
    rw [ae_all_iff]
    intro m
    exact ae_exists_pos_eq_of_everHitsProbability_eq_one W P X (-((m : ℤ))) (hhit (-((m : ℤ))))
  have hpos :
      ∀ᵐ ω ∂(P 0 : Measure Ω), ∀ m : ℕ, ∃ n : ℕ, 0 < n ∧ X n ω = m := by
    rw [ae_all_iff]
    intro m
    exact ae_exists_pos_eq_of_everHitsProbability_eq_one W P X m (hhit m)
  filter_upwards [hneg, hpos] with ω hnegω hposω
  constructor
  · intro m
    rcases hnegω m with ⟨n, -, hn⟩
    exact ⟨n, hn⟩
  · intro m
    rcases hposω m with ⟨n, -, hn⟩
    exact ⟨n, hn⟩

/-- Helper for Theorem 19.33: in an elliptic recurrent RWRE on `ℤ`, almost every path hits every
integer. -/
theorem randomEnvironmentHitsEveryInteger_ae_of_recurrent
    (hW : W.IsElliptic) (hrec : IsRecurrentMarkovChain P X) :
    ∀ᵐ ω ∂(P 0 : Measure Ω),
      (∀ m : ℕ, ∃ n : ℕ, X n ω = -((m : ℤ))) ∧
        ∀ m : ℕ, ∃ n : ℕ, X n ω = m := by
  -- Proof comment: the recurrent bridge proved above turns every integer into a hit-probability
  -- one state, and the countable-intersection helper packages these pointwise statements.
  refine ae_hitsEveryInteger_of_forall_everHitsProbability_eq_one W P X ?_
  intro k
  exact randomEnvironmentHitsEveryInteger_of_recurrent W P X hW hrec k

/-- Helper for Theorem 19.33: in an elliptic environment, the two-sided divergent Solomon regime
should imply almost-sure hits of every integer. This packages the exact AE event consumed by the
oscillation endgame. -/
theorem randomEnvironmentHitsEveryInteger_ae_of_bothSeries_eq_top
    (hW : W.IsElliptic) (hleft : R⁻[W] = ∞) (hright : R⁺[W] = ∞) :
    ∀ᵐ ω ∂(P 0 : Measure Ω),
      (∀ m : ℕ, ∃ n : ℕ, X n ω = -((m : ℤ))) ∧
        ∀ m : ℕ, ∃ n : ℕ, X n ω = m := by
  -- Route correction: after importing the canonical Chapter 19 owner for
  -- `effectiveResistanceToInfinity`, the only remaining bridge is to specialize the recurrence
  -- criterion `isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero` to the RWRE
  -- conductance walk constructed above.
  have hresTop :
      effectiveResistanceToInfinity (randomEnvironmentConductance W) P X 0 = ∞ :=
    randomEnvironment_effectiveResistanceToInfinity_eq_top_of_bothSeries_eq_top
      (W := W) (P := P) (X := X) hW hleft hright
  have hrec0 : IsRecurrentState P X 0 := by
    -- Proof comment: the new local wrapper packages the conductance-walk transport and the
    -- Chapter 19 recurrence criterion into the exact RWRE statement needed here.
    exact
      (randomEnvironmentStateZeroRecurrent_iff_effectiveResistanceToInfinity_eq_top
        (W := W) (P := P) (X := X) hW).2 hresTop
  have hrec : IsRecurrentMarkovChain P X :=
    randomEnvironment_recurrent_of_recurrentZero (W := W) (P := P) (X := X) hW hrec0
  -- Proof comment: once recurrence is recovered, the previously established AE hitting theorem
  -- applies verbatim.
  exact randomEnvironmentHitsEveryInteger_ae_of_recurrent W P X hW hrec

/-- Helper for Theorem 19.33: if a deterministic integer-valued path hits every nonnegative level,
then it crosses every integer threshold infinitely often on the positive side. -/
private theorem integerPath_frequently_ge_of_hitsEveryNat
    (Y : ℕ → ℤ) (hpos : ∀ m : ℕ, ∃ n : ℕ, Y n = m) (M : ℤ) :
    ∃ᶠ n in atTop, M ≤ Y n := by
  rw [Nat.frequently_atTop_iff_infinite]
  let offset : ℕ := Int.natAbs M
  let pick : ℕ → ℕ := fun t ↦ Classical.choose (hpos (offset + t))
  have hpick : ∀ t : ℕ, Y (pick t) = ((offset + t : ℕ) : ℤ) := by
    intro t
    exact Classical.choose_spec (hpos (offset + t))
  have hinj : Function.Injective pick := by
    intro a b hab
    have hEq : (((offset + a : ℕ) : ℤ)) = (((offset + b : ℕ) : ℤ)) := by
      rw [← hpick a, hab, hpick b]
    omega
  have hsubset : Set.range pick ⊆ {n : ℕ | M ≤ Y n} := by
    intro n hn
    rcases hn with ⟨t, rfl⟩
    change M ≤ Y (pick t)
    rw [hpick t]
    have hMle : M ≤ ((offset : ℕ) : ℤ) := by
      by_cases hM : 0 ≤ M
      · simpa [offset, Int.ofNat_natAbs_of_nonneg hM] using hM
      · exact le_trans (le_of_not_ge hM) (by simp [offset])
    exact le_trans hMle (by exact_mod_cast Nat.le_add_right offset t)
  exact Set.Infinite.mono hsubset (Set.infinite_range_of_injective hinj)

/-- Helper for Theorem 19.33: if a deterministic integer-valued path hits every negative level,
then it crosses every integer threshold infinitely often on the negative side. -/
private theorem integerPath_frequently_le_of_hitsEveryNeg
    (Y : ℕ → ℤ) (hneg : ∀ m : ℕ, ∃ n : ℕ, Y n = -((m : ℤ))) (M : ℤ) :
    ∃ᶠ n in atTop, Y n ≤ M := by
  rw [Nat.frequently_atTop_iff_infinite]
  let offset : ℕ := Int.natAbs M
  let pick : ℕ → ℕ := fun t ↦ Classical.choose (hneg (offset + t))
  have hpick : ∀ t : ℕ, Y (pick t) = -(((offset + t : ℕ) : ℤ)) := by
    intro t
    exact Classical.choose_spec (hneg (offset + t))
  have hinj : Function.Injective pick := by
    intro a b hab
    have hEq : -((((offset + a : ℕ) : ℤ))) = -((((offset + b : ℕ) : ℤ))) := by
      rw [← hpick a, hab, hpick b]
    omega
  have hsubset : Set.range pick ⊆ {n : ℕ | Y n ≤ M} := by
    intro n hn
    rcases hn with ⟨t, rfl⟩
    change Y (pick t) ≤ M
    rw [hpick t]
    have hbase : -(((offset : ℕ) : ℤ)) ≤ M := by
      by_cases hM : 0 ≤ M
      · exact le_trans (by simp [offset]) hM
      · have hMle : M ≤ 0 := le_of_not_ge hM
        simpa [offset, Int.ofNat_natAbs_of_nonpos hMle] using le_rfl
    have hmono : -((((offset + t : ℕ) : ℤ))) ≤ -(((offset : ℕ) : ℤ)) := by
      omega
    exact le_trans hmono hbase
  exact Set.Infinite.mono hsubset (Set.infinite_range_of_injective hinj)

/-- Helper for Theorem 19.33: if a deterministic path visits every positive and negative integer,
then its `EReal` liminf and limsup are `⊥` and `⊤`. -/
theorem integerPath_liminf_eq_bot_and_limsup_eq_top_of_hitsEveryInteger
    (Y : ℕ → ℤ)
    (hneg : ∀ m : ℕ, ∃ n : ℕ, Y n = -((m : ℤ)))
    (hpos : ∀ m : ℕ, ∃ n : ℕ, Y n = m) :
    liminf (fun n ↦ (((Y n : ℤ) : ℝ) : EReal)) atTop = ⊥ ∧
      limsup (fun n ↦ (((Y n : ℤ) : ℝ) : EReal)) atTop = ⊤ := by
  constructor
  · -- Proof comment: every real threshold lies above some integer level that the path visits
    -- infinitely often on the negative side, forcing the liminf down to `⊥`.
    rw [EReal.eq_bot_iff_forall_lt]
    intro N
    let M : ℤ := Int.floor N - 1
    have hfreq :
        ∃ᶠ n in atTop,
          ((((Y n : ℤ) : ℝ) : EReal)) ≤ ((((M : ℤ) : ℝ) : EReal)) := by
      refine (integerPath_frequently_le_of_hitsEveryNeg Y hneg M).mono ?_
      intro n hn
      exact_mod_cast hn
    have hM_le :
        liminf (fun n ↦ (((Y n : ℤ) : ℝ) : EReal)) atTop ≤
          ((((M : ℤ) : ℝ) : EReal)) :=
      (liminf_le_iff').2 fun y hy ↦ hfreq.mono fun n hn ↦ le_trans hn hy.le
    have hMN : ((((M : ℤ) : ℝ) : EReal)) < N := by
      have hMN_real : (M : ℝ) < N := by
        have hfloor : (Int.floor N : ℝ) ≤ N := by
          exact_mod_cast Int.floor_le N
        calc
          (M : ℝ) = (Int.floor N : ℝ) - 1 := by
            dsimp [M]
            norm_num
          _ < Int.floor N := by linarith
          _ ≤ N := hfloor
      exact_mod_cast hMN_real
    exact lt_of_le_of_lt hM_le hMN
  · -- Proof comment: every real threshold lies below some integer level that the path visits
    -- infinitely often on the positive side, forcing the limsup up to `⊤`.
    rw [EReal.eq_top_iff_forall_lt]
    intro N
    rcases exists_nat_gt N with ⟨m, hm⟩
    have hfreq :
        ∃ᶠ n in atTop,
          ((((m + 1 : ℕ) : ℝ) : EReal)) ≤ ((((Y n : ℤ) : ℝ) : EReal)) := by
      refine (integerPath_frequently_ge_of_hitsEveryNat Y hpos (m + 1)).mono ?_
      intro n hn
      exact_mod_cast hn
    have hlim :
        ((((m + 1 : ℕ) : ℝ) : EReal)) ≤
          limsup (fun n ↦ (((Y n : ℤ) : ℝ) : EReal)) atTop :=
      le_limsup_of_frequently_le hfreq
    have hm_succ : (m : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self m
    have hN' : N < ((m + 1 : ℕ) : ℝ) := by
      exact lt_trans hm hm_succ
    exact lt_of_lt_of_le (by exact_mod_cast hN') hlim

/-- Helper for Theorem 19.33: once a nearest-neighbor integer path has reached a negative state
after its last visit to `0`, every later step stays on the negative side. -/
private theorem integerPath_neg_of_no_zero_after
    (Y : ℕ → ℤ)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1)
    {N : ℕ} (hN : Y N < 0) (hnozero : ∀ n : ℕ, N ≤ n → Y n ≠ 0) :
    ∀ n : ℕ, N ≤ n → Y n < 0 := by
  intro n hn
  induction' hn with n hn ih
  · -- Proof comment: the sign at the anchor time `N` is already negative.
    simpa using hN
  · have hpred : Y n < 0 := ih
    rcases hstep n with hright | hleft
    · -- Proof comment: a right jump from a negative state lands in `(-∞, 0]`; excluding `0`
      -- forces the new position to remain negative.
      have hnonzero : Y (n + 1) ≠ 0 := hnozero (n + 1) (le_trans hn (Nat.le_succ n))
      have hle : Y (n + 1) ≤ 0 := by
        rw [hright]
        omega
      exact lt_of_le_of_ne hle (by simpa [eq_comm] using hnonzero)
    · -- Proof comment: a left jump preserves negativity outright.
      calc
        Y (n + 1) = Y n - 1 := hleft
        _ < 0 := by omega

/-- Helper for Theorem 19.33: once a nearest-neighbor integer path has reached a positive state
after its last visit to `0`, every later step stays on the positive side. -/
private theorem integerPath_pos_of_no_zero_after
    (Y : ℕ → ℤ)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1)
    {N : ℕ} (hN : 0 < Y N) (hnozero : ∀ n : ℕ, N ≤ n → Y n ≠ 0) :
    ∀ n : ℕ, N ≤ n → 0 < Y n := by
  intro n hn
  induction' hn with n hn ih
  · -- Proof comment: the sign at the anchor time `N` is already positive.
    simpa using hN
  · have hpred : 0 < Y n := ih
    rcases hstep n with hright | hleft
    · -- Proof comment: a right jump from a positive state stays positive.
      calc
        0 < Y n + 1 := by omega
        _ = Y (n + 1) := by omega
    · -- Proof comment: a left jump from a positive state lands in `[0, ∞)`; excluding `0`
      -- keeps it strictly positive.
      have hnonzero : Y (n + 1) ≠ 0 := hnozero (n + 1) (le_trans hn (Nat.le_succ n))
      have hge : 0 ≤ Y (n + 1) := by
        rw [hleft]
        omega
      exact lt_of_le_of_ne hge (by simpa using hnonzero.symm)

/-- Helper for Theorem 19.33: if each state of an integer-valued path is visited only finitely
often, then the set of times spent in any fixed positive band is finite. -/
private theorem integerPath_smallPositiveValues_finite
    (Y : ℕ → ℤ) (hfinite : ∀ z : ℤ, Set.Finite {n : ℕ | Y n = z}) (b : ℤ) :
    Set.Finite {n : ℕ | 0 < Y n ∧ Y n < b} := by
  classical
  by_cases hb : b ≤ 1
  · have hsubset : {n : ℕ | 0 < Y n ∧ Y n < b} ⊆ (∅ : Set ℕ) := by
      intro n hn
      rcases hn with ⟨hpos, hlt⟩
      have : False := by omega
      simpa using this
    -- Proof comment: when `b ≤ 1`, there are no positive integers strictly below `b`.
    exact Set.Finite.subset (by simpa using (Set.finite_empty : (∅ : Set ℕ).Finite)) hsubset
  · let s : Finset ℤ := Finset.Icc 1 (b - 1)
    have hs : {n : ℕ | 0 < Y n ∧ Y n < b} ⊆ ⋃ z ∈ s, {n : ℕ | Y n = z} := by
      intro n hn
      rcases hn with ⟨hpos, hlt⟩
      have h1 : (1 : ℤ) ≤ Y n := by omega
      have h2 : Y n ≤ b - 1 := by omega
      have hyn : Y n ∈ s := by
        simp [s, h1, h2]
      exact Set.mem_iUnion.2 ⟨Y n, Set.mem_iUnion.2 ⟨hyn, by simp⟩⟩
    -- Proof comment: only the finitely many states in `{1, ..., b - 1}` can occur in this band.
    refine Set.Finite.subset ?_ hs
    refine (s.finite_toSet).biUnion ?_
    intro z hz
    simpa using hfinite z

/-- Helper for Theorem 19.33: if each state of an integer-valued path is visited only finitely
often, then the set of times spent in any fixed negative band is finite. -/
private theorem integerPath_negativeBand_finite
    (Y : ℕ → ℤ) (hfinite : ∀ z : ℤ, Set.Finite {n : ℕ | Y n = z}) (b : ℤ) :
    Set.Finite {n : ℕ | b < Y n ∧ Y n < 0} := by
  classical
  by_cases hb : 0 ≤ b
  · have hsubset : {n : ℕ | b < Y n ∧ Y n < 0} ⊆ (∅ : Set ℕ) := by
      intro n hn
      rcases hn with ⟨hgt, hneg⟩
      have : False := by omega
      simpa using this
    -- Proof comment: when `b ≥ 0`, no negative integer lies strictly above `b`.
    exact Set.Finite.subset (by simpa using (Set.finite_empty : (∅ : Set ℕ).Finite)) hsubset
  · let s : Finset ℤ := Finset.Icc (b + 1) (-1)
    have hs : {n : ℕ | b < Y n ∧ Y n < 0} ⊆ ⋃ z ∈ s, {n : ℕ | Y n = z} := by
      intro n hn
      rcases hn with ⟨hgt, hneg⟩
      have h1 : b + 1 ≤ Y n := by omega
      have h2 : Y n ≤ -1 := by omega
      have hyn : Y n ∈ s := by
        simp [s, h1, h2]
      exact Set.mem_iUnion.2 ⟨Y n, Set.mem_iUnion.2 ⟨hyn, by simp⟩⟩
    -- Proof comment: only the finitely many states in `{b + 1, ..., -1}` can occur here.
    refine Set.Finite.subset ?_ hs
    refine (s.finite_toSet).biUnion ?_
    intro z hz
    simpa using hfinite z

/-- Helper for Theorem 19.33: a nearest-neighbor integer path that visits every state only
finitely often must eventually keep one sign, and then it is forced to tend to `-∞` or `+∞`. -/
theorem integerPath_tendsto_atBot_or_atTop_of_finiteVisits
    (Y : ℕ → ℤ)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1)
    (hfinite : ∀ z : ℤ, Set.Finite {n : ℕ | Y n = z}) :
    Tendsto Y atTop atBot ∨ Tendsto Y atTop atTop := by
  have hnozero_eventually : ∀ᶠ n in atTop, Y n ≠ 0 := by
    have hnotFreq : ¬ ∃ᶠ n in atTop, Y n = 0 := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact (hfinite 0).not_infinite
    rw [not_frequently] at hnotFreq
    simpa using hnotFreq
  rcases (eventually_atTop.1 hnozero_eventually) with ⟨N, hNtail⟩
  have hNnonzero : Y N ≠ 0 := hNtail N (le_rfl)
  by_cases hNpos : 0 < Y N
  · right
    have hpos : ∀ n : ℕ, N ≤ n → 0 < Y n :=
      integerPath_pos_of_no_zero_after Y hstep hNpos (fun n hn ↦ hNtail n hn)
    refine tendsto_atTop.2 ?_
    intro b
    by_cases hb : b ≤ 0
    · -- Proof comment: for nonpositive thresholds, eventual positivity is already enough.
      refine (eventually_ge_atTop N).mono ?_
      intro n hn
      exact le_trans hb (le_of_lt (hpos n hn))
    · have hfiniteSmall : Set.Finite {n : ℕ | 0 < Y n ∧ Y n < b} :=
        integerPath_smallPositiveValues_finite Y hfinite b
      have havoid : ∀ᶠ n in atTop, n ∉ {n : ℕ | 0 < Y n ∧ Y n < b} := by
        simpa [Nat.cofinite_eq_atTop] using hfiniteSmall.eventually_cofinite_notMem
      -- Proof comment: after the last visit to the finite positive band `{1, ..., b - 1}`, the
      -- path stays above that band forever.
      filter_upwards [havoid, eventually_ge_atTop N] with n hsmall hn
      have hposn : 0 < Y n := hpos n hn
      by_contra hlt
      exact hsmall ⟨hposn, lt_of_not_ge hlt⟩
  · left
    have hNneg : Y N < 0 := by omega
    have hneg : ∀ n : ℕ, N ≤ n → Y n < 0 :=
      integerPath_neg_of_no_zero_after Y hstep hNneg (fun n hn ↦ hNtail n hn)
    refine tendsto_atBot.2 ?_
    intro b
    have hfiniteBand : Set.Finite {n : ℕ | b < Y n ∧ Y n < 0} :=
      integerPath_negativeBand_finite Y hfinite b
    have havoid : ∀ᶠ n in atTop, n ∉ {n : ℕ | b < Y n ∧ Y n < 0} := by
      simpa [Nat.cofinite_eq_atTop] using hfiniteBand.eventually_cofinite_notMem
    -- Proof comment: once the path has left the finite negative band `(b, 0)`, it can never
    -- come back without revisiting one of those finitely many states.
    filter_upwards [havoid, eventually_ge_atTop N] with n hband hn
    have hnegn : Y n < 0 := hneg n hn
    by_contra hgt
    exact hband ⟨lt_of_not_ge hgt, hnegn⟩

/-- Helper for Theorem 19.33: if the `(k + 1)`st entrance time into `x` is finite, then the `k`th
entrance time is already finite. -/
private theorem iteratedEntranceTime_finite_of_succ_finite
    {E : Type*} (Y : ℕ → Ω → E) (x : E) (ω : Ω) (k : ℕ+)
    (hfin : (τ_[Y, x]^(k + 1)) ω < ⊤) :
    (τ_[Y, x]^k) ω < ⊤ := by
  by_contra hk
  have hktop : (τ_[Y, x]^k) ω = ⊤ := top_unique (le_of_not_gt hk)
  have hempty :
      ((fun n : ℕ ↦ (n : ℕ∞)) '' {n : ℕ | (τ_[Y, x]^k) ω < n ∧ Y n ω = x}) = ∅ := by
    ext a
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp [hktop] at hn
    · simp
  -- Proof comment: if the previous entrance time is already `⊤`, the successor search set is
  -- empty, so the successor entrance time cannot be finite.
  rw [iteratedEntranceTime_succ, hempty] at hfin
  simpa using hfin

/-- Helper for Theorem 19.33: once some iterated entrance time into `x` is `⊤`, only finitely many
times can satisfy `Y n = x`. -/
private theorem finiteVisits_of_iteratedEntranceTime_eq_top
    {E : Type*} (Y : ℕ → Ω → E) (x : E) (ω : Ω) (k : ℕ+)
    (hk : (τ_[Y, x]^k) ω = ⊤) :
    Set.Finite {n : ℕ | Y n ω = x} := by
  induction k using PNat.recOn generalizing ω with
  | one =>
      have hNoPosHit : ∀ n : ℕ, 0 < n → Y n ω ≠ x := by
        intro n hn hnx
        have hhit : hittingAfter Y ({x} : Set E) 1 ω < ⊤ :=
          (hittingAfter_singleton_lt_top_iff Y x ω).2 ⟨n, hn, hnx⟩
        have : (τ_[Y, x]^1) ω < ⊤ := by simpa [iteratedEntranceTime_one] using hhit
        exact (ne_of_lt this) hk |> False.elim
      let S : Set ℕ := {n : ℕ | Y n ω = x}
      have hsubset : S ⊆ ({0} : Set ℕ) := by
        intro n hn
        by_cases hzero : n = 0
        · simpa [S, hzero]
        · exfalso
          exact hNoPosHit n (Nat.pos_of_ne_zero hzero) (by simpa [S] using hn)
      -- Proof comment: if the first entrance time is `⊤`, then only the time-`0` visit can remain.
      exact Set.Finite.subset (by simpa using (Set.finite_singleton 0)) hsubset
  | succ k ih =>
      by_cases hkprev : (τ_[Y, x]^k) ω = ⊤
      · -- Proof comment: if the earlier entrance time is already `⊤`, the induction hypothesis
        -- already bounds all visits.
        exact ih ω hkprev
      · let N : ℕ := ENat.toNat ((τ_[Y, x]^k) ω)
        have hTailEmpty :
            {n : ℕ | (τ_[Y, x]^k) ω < n ∧ Y n ω = x} = ∅ := by
          ext n
          constructor
          · intro hn
            have hlt :
                (τ_[Y, x]^(k + 1)) ω < ⊤ := by
              rw [iteratedEntranceTime_succ]
              exact lt_of_le_of_lt (sInf_le ⟨n, hn, rfl⟩) (by simp)
            exact False.elim ((ne_of_lt hlt) hk)
          · simp
        have hsubset : {n : ℕ | Y n ω = x} ⊆ Set.Iic N := by
          intro n hn
          by_cases hle : n ≤ N
          · exact hle
          · have hNlt : N < n := lt_of_not_ge hle
            have hτlt : (τ_[Y, x]^k) ω < n := by
              have hNlt' : ((N : ℕ) : ℕ∞) < n := by
                exact_mod_cast hNlt
              simpa [N, ENat.coe_toNat hkprev] using hNlt'
            have : n ∈ ({n : ℕ | (τ_[Y, x]^k) ω < n ∧ Y n ω = x} : Set ℕ) := ⟨hτlt, hn⟩
            simpa [hTailEmpty] using this
        -- Proof comment: if the `(k + 1)`st entrance never occurs, every hit lies before the
        -- finite time `τ_x^k`.
        exact Set.Finite.subset (by simpa using (Set.finite_Iic N)) hsubset

/-- Helper for Theorem 19.33: under `P 0`, a transient state `y` is visited only finitely many
times almost surely. -/
private theorem randomEnvironmentFiniteVisits_ae_of_transientState
    {κ : ℕ → Kernel ℤ ℤ}
    [IsMarkovProcessRealization κ P X]
    (y : ℤ) (hy : IsTransientState P X y) :
    ∀ᵐ ω ∂(P 0 : Measure Ω), Set.Finite {n : ℕ | X n ω = y} := by
  let entranceIndex : ℕ → ℕ+ := fun n ↦ ⟨n + 1, Nat.succ_pos n⟩
  let A : ℕ → Set Ω := fun n ↦ {ω | (τ_[X, y]^(entranceIndex n)) ω < ⊤}
  let All : Set Ω := ⋂ n : ℕ, A n
  have hA_anti : Antitone A := by
    intro m n hmn
    induction hmn with
    | refl =>
        intro ω hω
        exact hω
    | @step n hmn ih =>
        intro ω hω
        have hprev :
            (τ_[X, y]^(entranceIndex n)) ω < ⊤ :=
          iteratedEntranceTime_finite_of_succ_finite X y ω (entranceIndex n) hω
        exact ih hprev
  have hA_formula :
      ∀ n : ℕ,
        (P 0 : Measure Ω) (A n) =
          ENNReal.ofReal ((F[P, X]) 0 y * (F[P, X]) y y ^ n) := by
    intro n
    have hreal :
        (P 0 : Measure Ω).real (A n) =
          (F[P, X]) 0 y * (F[P, X]) y y ^ (entranceIndex n).natPred := by
      simpa [A, entranceIndex] using
        (iteratedEntranceTime_finite_probability_eq_everHitsProbability_mul_selfPow
          (κ := κ)
          (P := P) (X := X) 0 y (entranceIndex n))
    -- Proof comment: the public iterated-entrance formula packages each `n`th entrance event as
    -- one factor of the transient return probability.
    calc
      (P 0 : Measure Ω) (A n) = ENNReal.ofReal ((P 0 : Measure Ω).real (A n)) := by
        rw [Measure.real_def, ENNReal.ofReal_toReal]
        exact measure_ne_top _ _
      _ = ENNReal.ofReal ((F[P, X]) 0 y * (F[P, X]) y y ^ n) := by
        simpa [entranceIndex] using congrArg ENNReal.ofReal hreal
  have htail_tendsto :
      Tendsto (fun n ↦ (P 0 : Measure Ω) (A n)) atTop (nhds 0) := by
    have hy_nonneg : 0 ≤ (F[P, X]) y y := measureReal_nonneg
    have hy_pow :
        Tendsto (fun n : ℕ ↦ (F[P, X]) y y ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hy_nonneg hy
    have hprod :
        Tendsto (fun n : ℕ ↦ (F[P, X]) 0 y * (F[P, X]) y y ^ n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hy_pow)
    have hofReal :
        Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((F[P, X]) 0 y * (F[P, X]) y y ^ n))
          atTop (nhds 0) :=
      by simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hprod
    have hA_eq :
        (fun n ↦ (P 0 : Measure Ω) (A n)) =
          fun n ↦ ENNReal.ofReal ((F[P, X]) 0 y * (F[P, X]) y y ^ n) := by
      funext n
      exact hA_formula n
    simpa [hA_eq] using hofReal
  have hAll_le : ∀ n : ℕ, (P 0 : Measure Ω) All ≤ (P 0 : Measure Ω) (A n) := by
    intro n
    exact measure_mono (by
      intro ω hω
      exact Set.mem_iInter.1 hω n)
  have hAll_zero_le : (P 0 : Measure Ω) All ≤ 0 := by
    -- Proof comment: the infinite-entrance event sits inside every geometric tail event `A n`,
    -- and those tail masses tend to `0`.
    exact le_of_tendsto_of_tendsto'
      tendsto_const_nhds htail_tendsto hAll_le
  have hAll_zero : (P 0 : Measure Ω) All = 0 := le_antisymm hAll_zero_le bot_le
  have hAll_ae : Allᶜ ∈ ae (P 0 : Measure Ω) := compl_mem_ae_iff.2 hAll_zero
  filter_upwards [hAll_ae] with ω hω
  have hstop : ∃ n : ℕ, (τ_[X, y]^(entranceIndex n)) ω = ⊤ := by
    simpa [All, A, entranceIndex, lt_top_iff_ne_top] using hω
  rcases hstop with ⟨n, hn⟩
  exact finiteVisits_of_iteratedEntranceTime_eq_top X y ω (entranceIndex n) hn

/-- Helper for Theorem 19.33: if every state is transient, then almost every realized RWRE path
visits each state only finitely many times. -/
private theorem randomEnvironmentFiniteVisits_ae_of_allStatesTransient
    {κ : ℕ → Kernel ℤ ℤ}
    [IsMarkovProcessRealization κ P X]
    (hall : ∀ k : ℤ, IsTransientState P X k) :
    ∀ᵐ ω ∂(P 0 : Measure Ω), ∀ k : ℤ, Set.Finite {n : ℕ | X n ω = k} := by
  -- Proof comment: apply the single-state transient finite-visits bridge countably many times.
  rw [ae_all_iff]
  intro k
  exact randomEnvironmentFiniteVisits_ae_of_transientState
    (κ := κ) (P := P) (X := X) k (hall k)

/-- Helper for Theorem 19.33: if at least one Solomon series is finite, then almost every RWRE
path eventually chooses one direction and tends to `-∞` or `+∞`. -/
private theorem randomEnvironmentEventuallyDirectional_ae_of_oneSeries_finite
    (hW : W.IsElliptic) (hfinite : R⁻[W] < ∞ ∨ R⁺[W] < ∞) :
    ∀ᵐ ω ∂(P 0 : Measure Ω),
      Tendsto (fun n ↦ X n ω) atTop atBot ∨ Tendsto (fun n ↦ X n ω) atTop atTop := by
  have htrans : ∀ k : ℤ, IsTransientState P X k :=
    randomEnvironment_allStatesTransient_of_oneSeries_finite (W := W) (P := P) (X := X) hW hfinite
  have hfiniteVisits :
      ∀ᵐ ω ∂(P 0 : Measure Ω), ∀ k : ℤ, Set.Finite {n : ℕ | X n ω = k} :=
    randomEnvironmentFiniteVisits_ae_of_allStatesTransient
      (κ := fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n)
      (P := P) (X := X) htrans
  have hstep :
      ∀ᵐ ω ∂(P 0 : Measure Ω),
        ∀ n : ℕ, X (n + 1) ω = X n ω + 1 ∨ X (n + 1) ω = X n ω - 1 :=
    randomEnvironmentWalk_ae_nearestNeighbor (P := P) (X := X) W 0
  filter_upwards [hfiniteVisits, hstep] with ω hfiniteω hstepω
  -- Proof comment: once every state is visited only finitely often, the deterministic
  -- nearest-neighbor endgame forces one of the two directional limits.
  exact integerPath_tendsto_atBot_or_atTop_of_finiteVisits
    (Y := fun n ↦ X n ω) hstepω hfiniteω

/-- Helper for Theorem 19.33: the left Solomon series is strictly positive because its zeroth
term is the empty product `1`. -/
private theorem randomEnvironmentLeftSeries_pos (W : RandomEnvironment) :
    0 < R⁻[W] := by
  rw [randomEnvironmentLeftSeries_def]
  exact lt_of_lt_of_le (by simp [randomEnvironmentLeftSeriesTerm]) (ENNReal.le_tsum 0)

/-- Helper for Theorem 19.33: ellipticity makes the right Solomon series strictly positive because
its zeroth term is the positive local ratio `ρ[W](0)`. -/
private theorem randomEnvironmentRightSeries_pos
    (hW : W.IsElliptic) :
    0 < R⁺[W] := by
  rw [randomEnvironmentRightSeries_def]
  exact lt_of_lt_of_le
    (randomEnvironmentRightSeriesTerm_pos (W := W) hW 0)
    (ENNReal.le_tsum 0)

/-- Helper for Theorem 19.33: once both branch series are positive and at least one is finite, the
two Solomon directional ratios are complementary. -/
private theorem solomonDirectionalSeriesRatio_compl
    {toward away : ℝ≥0∞}
    (htoward_pos : 0 < toward) (haway_pos : 0 < away)
    (hfinite : toward < ∞ ∨ away < ∞) :
    1 - solomonDirectionalSeriesRatio toward away =
      solomonDirectionalSeriesRatio away toward := by
  rcases hfinite with htoward_fin | haway_fin
  · by_cases haway_top : away = ∞
    · -- Proof comment: if the opposite branch is infinite while the current branch is finite,
      -- then the current directional ratio is `0` and the opposite one is `1`.
      rw [solomonDirectionalSeriesRatio_eq_one haway_top,
        solomonDirectionalSeriesRatio_eq_div htoward_fin]
      simp [haway_top]
    · -- Proof comment: when both branch series are finite, the two quotients sum to `1`.
      have haway_fin : away < ∞ := lt_top_iff_ne_top.mpr haway_top
      have hsum_ne_top : toward + away ≠ ∞ :=
        (ENNReal.add_ne_top).2 ⟨htoward_fin.ne, haway_fin.ne⟩
      have hsum_ne_zero : toward + away ≠ 0 := by
        exact ne_of_gt (lt_of_lt_of_le htoward_pos (le_add_of_nonneg_right (zero_le away)))
      have hsum_ne_top' : away + toward ≠ ∞ := by
        simpa [add_comm] using hsum_ne_top
      have hsum_ne_zero' : away + toward ≠ 0 := by
        simpa [add_comm] using hsum_ne_zero
      rw [solomonDirectionalSeriesRatio_eq_div htoward_fin,
        solomonDirectionalSeriesRatio_eq_div haway_fin]
      refine ENNReal.sub_eq_of_eq_add (ENNReal.div_ne_top htoward_fin.ne hsum_ne_zero') ?_
      rw [add_comm toward away, ← ENNReal.add_div]
      simpa [hsum_ne_zero', hsum_ne_top'] using
        (ENNReal.div_self hsum_ne_zero' hsum_ne_top').symm
  · by_cases htoward_top : toward = ∞
    · -- Proof comment: this is the symmetric one-infinite-branch case.
      rw [solomonDirectionalSeriesRatio_eq_one htoward_top,
        solomonDirectionalSeriesRatio_eq_div haway_fin]
      simp [htoward_top]
    · -- Proof comment: the genuinely finite case is symmetric in the two branches.
      have htoward_fin : toward < ∞ := lt_top_iff_ne_top.mpr htoward_top
      have hsum_ne_top : away + toward ≠ ∞ :=
        (ENNReal.add_ne_top).2 ⟨haway_fin.ne, htoward_fin.ne⟩
      have hsum_ne_zero : away + toward ≠ 0 := by
        exact ne_of_gt (lt_of_lt_of_le haway_pos (le_add_of_nonneg_right (zero_le toward)))
      rw [solomonDirectionalSeriesRatio_eq_div htoward_fin,
        solomonDirectionalSeriesRatio_eq_div haway_fin]
      refine ENNReal.sub_eq_of_eq_add (ENNReal.div_ne_top htoward_fin.ne hsum_ne_zero) ?_
      rw [add_comm toward away, ← ENNReal.add_div]
      simpa [hsum_ne_zero, hsum_ne_top] using
        (ENNReal.div_self hsum_ne_zero hsum_ne_top).symm

/-- Helper for Theorem 19.33: a path on `ℤ` that tends to `-∞` is globally bounded above. This
is the deterministic compactness substitute needed before comparing the `-∞` event with fixed
two-ray exit events. -/
private theorem integerPath_bddAbove_of_tendsto_atBot
    (Y : ℕ → ℤ) (hbot : Tendsto Y atTop atBot) :
    ∃ M : ℤ, ∀ n : ℕ, Y n < M := by
  rcases (tendsto_atTop_atBot.1 hbot) 0 with ⟨N, hN⟩
  let S : ℕ := Finset.sum (Finset.range N) fun i ↦ Int.natAbs (Y i) + 1
  refine ⟨((S : ℕ) : ℤ) + 1, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · -- Proof comment: after the tail index, the path is already below `0`, hence below the
    -- positive bound `S + 1`.
    have htail : Y n ≤ 0 := hN n hn
    have hpos : (0 : ℤ) < ((S : ℕ) : ℤ) + 1 := by
      positivity
    exact lt_of_le_of_lt htail hpos
  · -- Proof comment: on the finite prefix, the crude sum of absolute values dominates every
    -- visited state.
    have hn' : n < N := lt_of_not_ge hn
    have hprefix :
        (Int.natAbs (Y n) + 1 : ℕ) ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (f := fun i ↦ Int.natAbs (Y i) + 1)
        (fun i hi ↦ Nat.zero_le _)
        (Finset.mem_range.mpr hn')
    have hnatAbs : Y n < (((Int.natAbs (Y n) + 1 : ℕ) : ℤ)) := by
      by_cases hnonneg : 0 ≤ Y n
      · have hcast : (((Int.natAbs (Y n) : ℕ) : ℤ)) = Y n := by
          exact_mod_cast (Int.natAbs_of_nonneg hnonneg)
        rw [show (((Int.natAbs (Y n) + 1 : ℕ) : ℤ)) = (((Int.natAbs (Y n) : ℕ) : ℤ)) + 1 by norm_num,
          hcast]
        omega
      · have hneg : Y n < 0 := lt_of_not_ge hnonneg
        have hcast : (((Int.natAbs (Y n) : ℕ) : ℤ)) = -Y n := by
          simpa using (Int.ofNat_natAbs_of_nonpos (le_of_lt hneg))
        rw [show (((Int.natAbs (Y n) + 1 : ℕ) : ℤ)) = (((Int.natAbs (Y n) : ℕ) : ℤ)) + 1 by norm_num,
          hcast]
        omega
    calc
      Y n < (((Int.natAbs (Y n) + 1 : ℕ) : ℤ)) := hnatAbs
      _ ≤ (S : ℤ) := by
            exact_mod_cast hprefix
      _ < ((S : ℕ) : ℤ) + 1 := by
            omega

/-- Helper for Theorem 19.33: a path on `ℤ` that tends to `+∞` is globally bounded below. This
is the positive-direction companion to `integerPath_bddAbove_of_tendsto_atBot`. -/
private theorem integerPath_bddBelow_of_tendsto_atTop
    (Y : ℕ → ℤ) (htop : Tendsto Y atTop atTop) :
    ∃ M : ℤ, ∀ n : ℕ, M < Y n := by
  have htail1 : ∀ᶠ n in atTop, (1 : ℤ) ≤ Y n := (tendsto_atTop.1 htop) 1
  rcases Filter.eventually_atTop.1 htail1 with ⟨N, hN⟩
  let S : ℕ := Finset.sum (Finset.range N) fun i ↦ Int.natAbs (Y i) + 1
  refine ⟨-(((S : ℕ) : ℤ) + 1), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · -- Proof comment: after the tail index, the path is already above `0`, hence above the
    -- negative bound `-(S + 1)`.
    have htail : (0 : ℤ) < Y n := by
      have htail' : (1 : ℤ) ≤ Y n := hN n hn
      omega
    have hneg : -(((S : ℕ) : ℤ) + 1) < (0 : ℤ) := by
      omega
    exact lt_trans hneg htail
  · -- Proof comment: on the finite prefix, the same absolute-value sum bounds the path from
    -- below.
    have hn' : n < N := lt_of_not_ge hn
    have hprefix :
        (Int.natAbs (Y n) + 1 : ℕ) ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum
        (f := fun i ↦ Int.natAbs (Y i) + 1)
        (fun i hi ↦ Nat.zero_le _)
        (Finset.mem_range.mpr hn')
    have hnatAbs : -(((Int.natAbs (Y n) : ℕ) : ℤ)) ≤ Y n := by
      by_cases hnonneg : 0 ≤ Y n
      · have hcast : (((Int.natAbs (Y n) : ℕ) : ℤ)) = Y n := by
          exact_mod_cast (Int.natAbs_of_nonneg hnonneg)
        rw [hcast]
        omega
      · have hneg : Y n < 0 := lt_of_not_ge hnonneg
        have hcast : (((Int.natAbs (Y n) : ℕ) : ℤ)) = -Y n := by
          simpa using (Int.ofNat_natAbs_of_nonpos (le_of_lt hneg))
        rw [hcast]
        omega
    have hprefixZ : (((Int.natAbs (Y n) + 1 : ℕ) : ℤ)) ≤ (S : ℤ) := by
      exact_mod_cast hprefix
    have hsum_lt : -(((S : ℕ) : ℤ) + 1) < -(((Int.natAbs (Y n) : ℕ) : ℤ)) := by
      omega
    exact lt_of_lt_of_le hsum_lt hnatAbs

/-- Helper for Theorem 19.33: a nearest-neighbor integer path started at `0`, bounded above by
`N`, and visiting each state only finitely often must hit the left boundary value
`-((N + 1 : ℕ) : ℤ)` at some positive time. -/
private theorem integerPath_hitsLeftBoundary_of_bddAbove_and_finiteVisits
    (Y : ℕ → ℤ) (N : ℕ) (hstart : Y 0 = 0)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1)
    (hbounded : ∀ n : ℕ, Y n < ((N + 1 : ℕ) : ℤ))
    (hfinite : ∀ z : ℤ, Set.Finite {n : ℕ | Y n = z}) :
    ∃ n : ℕ, 0 < n ∧ Y n = -((N + 1 : ℕ) : ℤ) := by
  let boundary : ℤ := -((N + 1 : ℕ) : ℤ)
  have hdir :
      Tendsto Y atTop atBot ∨ Tendsto Y atTop atTop :=
    integerPath_tendsto_atBot_or_atTop_of_finiteVisits Y hstep hfinite
  have hnot_top : ¬ Tendsto Y atTop atTop := by
    intro htop
    rcases Filter.eventually_atTop.1 ((tendsto_atTop.1 htop) (((N + 1 : ℕ) : ℤ))) with
      ⟨M, hM⟩
    exact not_le_of_gt (hbounded M) (hM M le_rfl)
  have hbot : Tendsto Y atTop atBot := by
    rcases hdir with hbot | htop
    · exact hbot
    · exact False.elim (hnot_top htop)
  rcases (tendsto_atTop_atBot.1 hbot) boundary with ⟨M, hM⟩
  have hS_nonempty : {n : ℕ | 0 < n ∧ Y n ≤ boundary}.Nonempty := by
    refine ⟨max M 1, ?_⟩
    constructor
    · exact lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_right M 1)
    · exact hM (max M 1) (Nat.le_max_left M 1)
  let n : ℕ := Nat.find hS_nonempty
  have hn_spec : 0 < n ∧ Y n ≤ boundary := Nat.find_spec hS_nonempty
  have hn_pos : 0 < n := hn_spec.1
  have hn_le : Y n ≤ boundary := hn_spec.2
  have hprev_gt : boundary < Y (n - 1) := by
    by_cases h_one : n = 1
    · simpa [h_one, boundary, hstart] using (show -((N + 1 : ℕ) : ℤ) < 0 by omega)
    · have hn_gt_one : 1 < n := by omega
      have hpred_pos : 0 < n - 1 := by omega
      have hpred_not_le : ¬ Y (n - 1) ≤ boundary := by
        intro hpred_le
        have hmin : n ≤ n - 1 := Nat.find_min' hS_nonempty ⟨hpred_pos, hpred_le⟩
        omega
      exact lt_of_not_ge hpred_not_le
  have hpred_succ : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)
  rcases hstep (n - 1) with hright | hleft
  · rw [hpred_succ] at hright
    have : boundary < Y n := by
      omega
    exact ⟨n, hn_pos, le_antisymm hn_le this.le⟩
  · rw [hpred_succ] at hleft
    have : Y n = boundary := by
      omega
    exact ⟨n, hn_pos, this⟩

/-- Helper for Theorem 19.33: a nearest-neighbor integer path started at `0`, bounded below by
`-(N + 1)`, and visiting each state only finitely often must hit the right boundary value
`((N + 1 : ℕ) : ℤ)` at some positive time. -/
private theorem integerPath_hitsRightBoundary_of_bddBelow_and_finiteVisits
    (Y : ℕ → ℤ) (N : ℕ) (hstart : Y 0 = 0)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1)
    (hbounded : ∀ n : ℕ, -((N + 1 : ℕ) : ℤ) < Y n)
    (hfinite : ∀ z : ℤ, Set.Finite {n : ℕ | Y n = z}) :
    ∃ n : ℕ, 0 < n ∧ Y n = ((N + 1 : ℕ) : ℤ) := by
  let boundary : ℤ := ((N + 1 : ℕ) : ℤ)
  have hdir :
      Tendsto Y atTop atBot ∨ Tendsto Y atTop atTop :=
    integerPath_tendsto_atBot_or_atTop_of_finiteVisits Y hstep hfinite
  have hnot_bot : ¬ Tendsto Y atTop atBot := by
    intro hbot
    rcases (tendsto_atTop_atBot.1 hbot) (-((N + 1 : ℕ) : ℤ)) with ⟨M, hM⟩
    exact not_lt_of_ge (hM M le_rfl) (hbounded M)
  have htop : Tendsto Y atTop atTop := by
    rcases hdir with hbot | htop
    · exact False.elim (hnot_bot hbot)
    · exact htop
  rcases Filter.eventually_atTop.1 ((tendsto_atTop.1 htop) boundary) with ⟨M, hM⟩
  have hS_nonempty : {n : ℕ | 0 < n ∧ boundary ≤ Y n}.Nonempty := by
    refine ⟨max M 1, ?_⟩
    constructor
    · exact lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_right M 1)
    · exact hM (max M 1) (Nat.le_max_left M 1)
  let n : ℕ := Nat.find hS_nonempty
  have hn_spec : 0 < n ∧ boundary ≤ Y n := Nat.find_spec hS_nonempty
  have hn_pos : 0 < n := hn_spec.1
  have hn_ge : boundary ≤ Y n := hn_spec.2
  have hprev_lt : Y (n - 1) < boundary := by
    by_cases h_one : n = 1
    · have hpos : (0 : ℤ) < ((N + 1 : ℕ) : ℤ) := by
        exact_mod_cast Nat.succ_pos N
      simpa [h_one, boundary, hstart] using hpos
    · have hn_gt_one : 1 < n := by omega
      have hpred_pos : 0 < n - 1 := by omega
      have hpred_not_ge : ¬ boundary ≤ Y (n - 1) := by
        intro hpred_ge
        have hmin : n ≤ n - 1 := Nat.find_min' hS_nonempty ⟨hpred_pos, hpred_ge⟩
        omega
      exact lt_of_not_ge hpred_not_ge
  have hpred_succ : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)
  rcases hstep (n - 1) with hright | hleft
  · rw [hpred_succ] at hright
    have : Y n = boundary := by
      omega
    exact ⟨n, hn_pos, this⟩
  · rw [hpred_succ] at hleft
    have : Y n < boundary := by
      omega
    exact False.elim (not_lt_of_ge hn_ge this)

/-- Helper for Theorem 19.33: if a nearest-neighbor integer path started at `0` stays strictly
below `N + 1` and tends to `-∞`, then its first exit from the symmetric corridor
`[-(N + 1), N + 1]` occurs at the left boundary. -/
private theorem integerPath_hitsLeftBoundary_before_right_of_bddAbove_and_tendsto_atBot
    (Y : ℕ → ℤ) (N : ℕ) (hstart : Y 0 = 0)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1)
    (hbounded : ∀ n : ℕ, Y n < ((N + 1 : ℕ) : ℤ))
    (hbot : Tendsto Y atTop atBot) :
    ∃ n : ℕ, Y n = -((N + 1 : ℕ) : ℤ) ∧
      ∀ m < n, Y m ∉ ({-((N + 1 : ℕ) : ℤ), ((N + 1 : ℕ) : ℤ)} : Set ℤ) := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  have hS_nonempty : {n : ℕ | 0 < n ∧ Y n ≤ left}.Nonempty := by
    rcases (tendsto_atTop_atBot.1 hbot) left with ⟨M, hM⟩
    refine ⟨max M 1, ?_⟩
    constructor
    · exact lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_right M 1)
    · exact hM (max M 1) (Nat.le_max_left M 1)
  let n : ℕ := Nat.find hS_nonempty
  have hn_spec : 0 < n ∧ Y n ≤ left := Nat.find_spec hS_nonempty
  have hn_pos : 0 < n := hn_spec.1
  have hn_le : Y n ≤ left := hn_spec.2
  have hprev_gt : left < Y (n - 1) := by
    by_cases h_one : n = 1
    · have hleft_lt_zero : left < 0 := by
        simp [left]
        omega
      simpa [h_one, left, hstart] using hleft_lt_zero
    · have hpred_pos : 0 < n - 1 := by omega
      have hpred_not_le : ¬ Y (n - 1) ≤ left := by
        intro hpred_le
        have hmin : n ≤ n - 1 := Nat.find_min' hS_nonempty ⟨hpred_pos, hpred_le⟩
        omega
      exact lt_of_not_ge hpred_not_le
  have hpred_succ : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)
  rcases hstep (n - 1) with hright | hleft
  · rw [hpred_succ] at hright
    have : left < Y n := by omega
    exact False.elim (not_lt_of_ge hn_le this)
  · rw [hpred_succ] at hleft
    have hn_eq : Y n = left := by omega
    refine ⟨n, by simpa [left] using hn_eq, ?_⟩
    intro m hm
    have hm_ne_left : Y m ≠ left := by
      intro hm_left
      by_cases hm_zero : m = 0
      · have hleft_ne_zero : left ≠ 0 := by
          simp [left]
          omega
        exact hleft_ne_zero <| hm_left.symm.trans (by simpa [hm_zero] using hstart)
      · have hm_pos : 0 < m := Nat.pos_iff_ne_zero.mpr hm_zero
        have hmin : n ≤ m := Nat.find_min' hS_nonempty ⟨hm_pos, by simpa [hm_left]⟩
        exact (not_le_of_gt hm) hmin
    have hm_ne_right : Y m ≠ ((N + 1 : ℕ) : ℤ) := by
      intro hm_right
      have := hbounded m
      omega
    intro hm_mem
    simp [left] at hm_mem
    rcases hm_mem with hm_left | hm_right
    · exact hm_ne_left <| by simpa [left] using hm_left
    · exact hm_ne_right hm_right

/-- Helper for Theorem 19.33: if a nearest-neighbor integer path started at `0` stays strictly
above `-(N + 1)` and tends to `+∞`, then its first exit from the symmetric corridor
`[-(N + 1), N + 1]` occurs at the right boundary. -/
private theorem integerPath_hitsRightBoundary_before_left_of_bddBelow_and_tendsto_atTop
    (Y : ℕ → ℤ) (N : ℕ) (hstart : Y 0 = 0)
    (hstep : ∀ n : ℕ, Y (n + 1) = Y n + 1 ∨ Y (n + 1) = Y n - 1)
    (hbounded : ∀ n : ℕ, -((N + 1 : ℕ) : ℤ) < Y n)
    (htop : Tendsto Y atTop atTop) :
    ∃ n : ℕ, Y n = ((N + 1 : ℕ) : ℤ) ∧
      ∀ m < n, Y m ∉ ({-((N + 1 : ℕ) : ℤ), ((N + 1 : ℕ) : ℤ)} : Set ℤ) := by
  let Z : ℕ → ℤ := fun n ↦ -Y n
  have hZstart : Z 0 = 0 := by simpa [Z, hstart]
  have hZstep : ∀ n : ℕ, Z (n + 1) = Z n + 1 ∨ Z (n + 1) = Z n - 1 := by
    intro n
    rcases hstep n with hright | hleft
    · right
      simp [Z]
      omega
    · left
      simp [Z]
      omega
  have hZbounded : ∀ n : ℕ, Z n < ((N + 1 : ℕ) : ℤ) := by
    intro n
    have h := hbounded n
    simp [Z] at *
    omega
  have hZbot : Tendsto Z atTop atBot :=
    tendsto_neg_atTop_atBot.comp htop
  rcases integerPath_hitsLeftBoundary_before_right_of_bddAbove_and_tendsto_atBot
      (Y := Z) (N := N) hZstart hZstep hZbounded hZbot with ⟨n, hn, havoid⟩
  refine ⟨n, ?_, ?_⟩
  · simp [Z] at hn
    omega
  · intro m hm
    have hm' := havoid m hm
    intro hm_mem
    apply hm'
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, Z] at hm_mem ⊢
    rcases hm_mem with hm_left | hm_right
    · right
      omega
    · left
      omega

/-- Helper for Theorem 19.33: the deterministic corridor witness above packages directly into the
Chapter 19 first-hit event at the left wall. -/
private theorem integerPath_leftBoundaryHitEvent_of_bddAbove_and_tendsto_atBot
    {Ω' : Type*} [MeasurableSpace Ω']
    (u : ℕ → Ω' → ℤ) (N : ℕ) {ω : Ω'}
    (hstart : u 0 ω = 0)
    (hstep : ∀ n : ℕ, u (n + 1) ω = u n ω + 1 ∨ u (n + 1) ω = u n ω - 1)
    (hbounded : ∀ n : ℕ, u n ω < ((N + 1 : ℕ) : ℤ))
    (hbot : Tendsto (fun n ↦ u n ω) atTop atBot) :
    hittingAfter u ({-((N + 1 : ℕ) : ℤ), ((N + 1 : ℕ) : ℤ)} : Set ℤ) 0 ω < ⊤ ∧
      stoppedValue u (hittingAfter u ({-((N + 1 : ℕ) : ℤ), ((N + 1 : ℕ) : ℤ)} : Set ℤ) 0) ω =
        -((N + 1 : ℕ) : ℤ) := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  rcases integerPath_hitsLeftBoundary_before_right_of_bddAbove_and_tendsto_atBot
      (Y := fun n ↦ u n ω) (N := N) hstart hstep hbounded hbot with ⟨n, hn, havoid⟩
  have hfirst :
      ∃ n : ℕ, u n ω = left ∧ ∀ m < n, u m ω ∉ insert left ({right} : Set ℤ) := by
    refine ⟨n, by simpa [left] using hn, ?_⟩
    intro m hm
    simpa [left, right, or_comm, or_left_comm] using havoid m hm
  -- Proof comment: the earliest left-wall witness is exactly the owner-side first-hit event.
  simpa [left, right, or_comm, or_left_comm] using
    (firstHitEvent_iff_exists u ({right} : Set ℤ) left ω).2 hfirst

/-- Helper for Theorem 19.33: the positive-direction corridor witness packages into the
corresponding first-hit event at the right wall. -/
private theorem integerPath_rightBoundaryHitEvent_of_bddBelow_and_tendsto_atTop
    {Ω' : Type*} [MeasurableSpace Ω']
    (u : ℕ → Ω' → ℤ) (N : ℕ) {ω : Ω'}
    (hstart : u 0 ω = 0)
    (hstep : ∀ n : ℕ, u (n + 1) ω = u n ω + 1 ∨ u (n + 1) ω = u n ω - 1)
    (hbounded : ∀ n : ℕ, -((N + 1 : ℕ) : ℤ) < u n ω)
    (htop : Tendsto (fun n ↦ u n ω) atTop atTop) :
    hittingAfter u ({-((N + 1 : ℕ) : ℤ), ((N + 1 : ℕ) : ℤ)} : Set ℤ) 0 ω < ⊤ ∧
      stoppedValue u (hittingAfter u ({-((N + 1 : ℕ) : ℤ), ((N + 1 : ℕ) : ℤ)} : Set ℤ) 0) ω =
        ((N + 1 : ℕ) : ℤ) := by
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  rcases integerPath_hitsRightBoundary_before_left_of_bddBelow_and_tendsto_atTop
      (Y := fun n ↦ u n ω) (N := N) hstart hstep hbounded htop with ⟨n, hn, havoid⟩
  have hfirst :
      ∃ n : ℕ, u n ω = right ∧ ∀ m < n, u m ω ∉ insert right ({left} : Set ℤ) := by
    refine ⟨n, by simpa [right] using hn, ?_⟩
    intro m hm
    simpa [left, right, or_comm, or_left_comm] using havoid m hm
  -- Proof comment: the reflected corridor witness is exactly the right-wall first-hit event.
  have hmain :
      hittingAfter u ({right, left} : Set ℤ) 0 ω < ⊤ ∧
        stoppedValue u (hittingAfter u ({right, left} : Set ℤ) 0) ω = right := by
    simpa [left, right, or_comm, or_left_comm] using
      (firstHitEvent_iff_exists u ({left} : Set ℤ) right ω).2 hfirst
  have hpair : ({right, left} : Set ℤ) = ({left, right} : Set ℤ) := by
    ext z
    simp [or_comm]
  rw [hpair] at hmain
  exact hmain

/-- Helper for Theorem 19.33: the event `Xₙ → -∞` is the union of its fixed upper-bound slices.
This is the source-proof reduction from the directional event to corridor cutoffs. -/
private theorem tendstoAtBot_set_eq_iUnion_uniformUpperSlices
    (X : ℕ → Ω → ℤ) :
    {ω | Tendsto (fun n ↦ X n ω) atTop atBot} =
      ⋃ N : ℕ, {ω | Tendsto (fun n ↦ X n ω) atTop atBot ∧
        ∀ n : ℕ, X n ω < ((N + 1 : ℕ) : ℤ)} := by
  ext ω
  constructor
  · intro hω
    rcases integerPath_bddAbove_of_tendsto_atBot (Y := fun n ↦ X n ω) hω with ⟨M, hM⟩
    rcases exists_nat_gt M with ⟨N, hN⟩
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    constructor
    · exact hω
    · intro n
      have hN' : M < ((N + 1 : ℕ) : ℤ) := by
        have hsucc : (N : ℤ) < ((N + 1 : ℕ) : ℤ) := by
          exact_mod_cast Nat.lt_succ_self N
        exact lt_trans hN hsucc
      exact lt_trans (hM n) hN'
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨N, hN⟩
    exact hN.1

/-- Helper for Theorem 19.33: the event `Xₙ → +∞` is the union of its fixed lower-bound slices.
This is the positive-direction companion to the upper-slice decomposition above. -/
private theorem tendstoAtTop_set_eq_iUnion_uniformLowerSlices
    (X : ℕ → Ω → ℤ) :
    {ω | Tendsto (fun n ↦ X n ω) atTop atTop} =
      ⋃ N : ℕ, {ω | Tendsto (fun n ↦ X n ω) atTop atTop ∧
        ∀ n : ℕ, -((N + 1 : ℕ) : ℤ) < X n ω} := by
  ext ω
  constructor
  · intro hω
    rcases integerPath_bddBelow_of_tendsto_atTop (Y := fun n ↦ X n ω) hω with ⟨M, hM⟩
    rcases exists_nat_gt (-M) with ⟨N, hN⟩
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    constructor
    · exact hω
    · intro n
      have hN' : -((N + 1 : ℕ) : ℤ) < M := by
        have hN'' : (-M : ℤ) < ((N + 1 : ℕ) : ℤ) := by
          have hsucc : (N : ℤ) < ((N + 1 : ℕ) : ℤ) := by
            exact_mod_cast Nat.lt_succ_self N
          exact lt_trans hN hsucc
        omega
      exact lt_trans hN' (hM n)
  · intro hω
    rcases Set.mem_iUnion.1 hω with ⟨N, hN⟩
    exact hN.1

/-- Helper for Theorem 19.33: each fixed upper-bound slice of the `-∞` event is dominated by the
left exit probability from the symmetric corridor `[-(N + 1), N + 1]`. -/
private theorem tendstoAtBot_uniformUpperSlice_real_le_leftBoundaryF_A
    (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (N : ℕ) :
    ((P 0 : Measure Ω)
      {ω | Tendsto (fun n ↦ X n ω) atTop atBot ∧
          ∀ n : ℕ, X n ω < ((N + 1 : ℕ) : ℤ)}).toReal ≤
      F_A P X ({((N + 1 : ℕ) : ℤ)} : Set ℤ) 0 (-((N + 1 : ℕ) : ℤ)) := by
  let μ : Measure Ω := (P 0 : Measure Ω)
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let E : Set Ω := {ω | Tendsto (fun n ↦ X n ω) atTop atBot ∧
    ∀ n : ℕ, X n ω < right}
  let B : Set Ω := {ω | hittingAfter X ({right, left} : Set ℤ) 1 ω < ⊤ ∧
    stoppedValue X (hittingAfter X ({right, left} : Set ℤ) 1) ω = left}
  have hsubset : E ≤ᵐ[μ] B := by
    filter_upwards [initialState_ae_eq_start_local (p := randomEnvironmentTransitionMatrix W)
      (P := P) (X := X) 0, randomEnvironmentWalk_ae_nearestNeighbor (P := P) (X := X) W 0] with
      ω hstart hstep
    intro hω
    have hboundary0 :
        hittingAfter X ({left, right} : Set ℤ) 0 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({left, right} : Set ℤ) 0) ω = left :=
      integerPath_leftBoundaryHitEvent_of_bddAbove_and_tendsto_atBot
        (u := X) (N := N) hstart hstep hω.2 hω.1
    have hboundary0' :
        hittingAfter X ({right, left} : Set ℤ) 0 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({right, left} : Set ℤ) 0) ω = left := by
      have hpair : ({right, left} : Set ℤ) = ({left, right} : Set ℤ) := by
        ext z
        simp [or_comm]
      rw [hpair]
      exact hboundary0
    have h0_not_mem : X 0 ω ∉ ({right, left} : Set ℤ) := by
      simp [hstart, left, right]
      omega
    have hτ :
        hittingAfter X ({right, left} : Set ℤ) 0 ω =
          hittingAfter X ({right, left} : Set ℤ) 1 ω :=
      hittingAfter_zero_eq_one_of_not_mem_initial_local (X := X) (A := ({right, left} : Set ℤ))
        h0_not_mem
    have hstop :
        stoppedValue X (hittingAfter X ({right, left} : Set ℤ) 0) ω =
          stoppedValue X (hittingAfter X ({right, left} : Set ℤ) 1) ω := by
      simp [stoppedValue, hτ]
    -- Proof comment: once the path stays below the right wall and tends to `-∞`, the deterministic
    -- corridor lemma forces a left-wall hit before any right-wall hit.
    refine ⟨?_, ?_⟩
    · simpa [B, hτ] using hboundary0'.1
    · rw [← hstop]
      exact hboundary0'.2
  have hμ_le : μ E ≤ μ B := measure_mono_ae hsubset
  have hreal_le : (μ E).toReal ≤ (μ B).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ B) hμ_le
  have hx0 : (0 : ℤ) ∉ ({right, left} : Set ℤ) := by
    simp [left, right]
    omega
  calc
    ((P 0 : Measure Ω) {ω | Tendsto (fun n ↦ X n ω) atTop atBot ∧
        ∀ n : ℕ, X n ω < ((N + 1 : ℕ) : ℤ)}).toReal
        = (μ E).toReal := by rfl
    _ ≤ (μ B).toReal := hreal_le
    _ = F_A P X ({right} : Set ℤ) 0 left := by
          simpa [μ, B, left, right] using
            boundaryHitDistribution_eq_F_A_of_not_mem_boundary
              (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
              (a := right) (b := left) (x := 0) hx0

/-- Helper for Theorem 19.33: each fixed lower-bound slice of the `+∞` event is dominated by the
right exit probability from the symmetric corridor `[-(N + 1), N + 1]`. -/
private theorem tendstoAtTop_uniformLowerSlice_real_le_rightBoundaryF_A
    (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]
    (N : ℕ) :
    ((P 0 : Measure Ω)
      {ω | Tendsto (fun n ↦ X n ω) atTop atTop ∧
          ∀ n : ℕ, -((N + 1 : ℕ) : ℤ) < X n ω}).toReal ≤
      F_A P X ({-((N + 1 : ℕ) : ℤ)} : Set ℤ) 0 (((N + 1 : ℕ) : ℤ)) := by
  let μ : Measure Ω := (P 0 : Measure Ω)
  let left : ℤ := -((N + 1 : ℕ) : ℤ)
  let right : ℤ := ((N + 1 : ℕ) : ℤ)
  let E : Set Ω := {ω | Tendsto (fun n ↦ X n ω) atTop atTop ∧
    ∀ n : ℕ, left < X n ω}
  let B : Set Ω := {ω | hittingAfter X ({left, right} : Set ℤ) 1 ω < ⊤ ∧
    stoppedValue X (hittingAfter X ({left, right} : Set ℤ) 1) ω = right}
  have hsubset : E ≤ᵐ[μ] B := by
    filter_upwards [initialState_ae_eq_start_local (p := randomEnvironmentTransitionMatrix W)
      (P := P) (X := X) 0, randomEnvironmentWalk_ae_nearestNeighbor (P := P) (X := X) W 0] with
      ω hstart hstep
    intro hω
    have hboundary0 :
        hittingAfter X ({left, right} : Set ℤ) 0 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({left, right} : Set ℤ) 0) ω = right :=
      integerPath_rightBoundaryHitEvent_of_bddBelow_and_tendsto_atTop
        (u := X) (N := N) hstart hstep hω.2 hω.1
    have h0_not_mem : X 0 ω ∉ ({left, right} : Set ℤ) := by
      simp [hstart, left, right]
      omega
    have hτ :
        hittingAfter X ({left, right} : Set ℤ) 0 ω =
          hittingAfter X ({left, right} : Set ℤ) 1 ω :=
      hittingAfter_zero_eq_one_of_not_mem_initial_local (X := X) (A := ({left, right} : Set ℤ))
        h0_not_mem
    have hstop :
        stoppedValue X (hittingAfter X ({left, right} : Set ℤ) 0) ω =
          stoppedValue X (hittingAfter X ({left, right} : Set ℤ) 1) ω := by
      simp [stoppedValue, hτ]
    -- Proof comment: the positive-direction slice forces the first corridor exit to occur at the
    -- right wall before the path can ever hit the left wall.
    refine ⟨?_, ?_⟩
    · simpa [B, hτ] using hboundary0.1
    · rw [← hstop]
      exact hboundary0.2
  have hμ_le : μ E ≤ μ B := measure_mono_ae hsubset
  have hreal_le : (μ E).toReal ≤ (μ B).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ B) hμ_le
  have hx0 : (0 : ℤ) ∉ ({left, right} : Set ℤ) := by
    simp [left, right]
    omega
  calc
    ((P 0 : Measure Ω) {ω | Tendsto (fun n ↦ X n ω) atTop atTop ∧
        ∀ n : ℕ, -((N + 1 : ℕ) : ℤ) < X n ω}).toReal
        = (μ E).toReal := by rfl
    _ ≤ (μ B).toReal := hreal_le
    _ = F_A P X ({left} : Set ℤ) 0 right := by
          simpa [μ, B, left, right] using
            boundaryHitDistribution_eq_F_A_of_not_mem_boundary
              (P := P) (X := X) (p := randomEnvironmentTransitionMatrix W)
              (a := left) (b := right) (x := 0) hx0

/-- Helper for Theorem 19.33: every finite left Solomon prefix sum stays finite in an elliptic
environment because each summand is finite. -/
private theorem randomEnvironmentLeftPrefixSum_ne_top
    (hW : W.IsElliptic) (N : ℕ) :
    randomEnvironmentLeftPrefixSum W N ≠ ∞ := by
  -- Proof comment: a finite `ENNReal` sum is finite once each term is finite.
  exact ENNReal.sum_ne_top.2 fun i hi ↦
    randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i

/-- Helper for Theorem 19.33: every finite right Solomon prefix sum stays finite in an elliptic
environment because each summand is finite. -/
private theorem randomEnvironmentRightPrefixSum_ne_top
    (hW : W.IsElliptic) (N : ℕ) :
    randomEnvironmentRightPrefixSum W N ≠ ∞ := by
  -- Proof comment: finiteness of the right-series terms propagates to every finite prefix sum.
  exact ENNReal.sum_ne_top.2 fun i hi ↦
    randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i

/-- Helper for Theorem 19.33: the left Solomon prefix sum is strictly positive because the zeroth
term is the positive empty product `1`. -/
private theorem randomEnvironmentLeftPrefixSum_pos
    (hW : W.IsElliptic) (N : ℕ) :
    0 < randomEnvironmentLeftPrefixSum W N := by
  have hterm0 :
      0 < randomEnvironmentLeftSeriesTerm W 0 := by
    exact randomEnvironmentLeftSeriesTerm_pos (W := W) hW 0
  have hzero_mem : 0 ∈ Finset.range (N + 1) := by
    simp
  -- Proof comment: the positive zeroth term appears in every corridor prefix.
  exact lt_of_lt_of_le hterm0 <|
    Finset.single_le_sum (fun i hi ↦ by exact zero_le _) hzero_mem

/-- Helper for Theorem 19.33: the right Solomon prefix sum is strictly positive because the zeroth
term is the positive ratio `ρ[W](0)`. -/
private theorem randomEnvironmentRightPrefixSum_pos
    (hW : W.IsElliptic) (N : ℕ) :
    0 < randomEnvironmentRightPrefixSum W N := by
  have hterm0 :
      0 < randomEnvironmentRightSeriesTerm W 0 := by
    exact randomEnvironmentRightSeriesTerm_pos (W := W) hW 0
  have hzero_mem : 0 ∈ Finset.range (N + 1) := by
    simp
  -- Proof comment: every shifted right prefix includes the positive first Solomon factor.
  exact lt_of_lt_of_le hterm0 <|
    Finset.single_le_sum (fun i hi ↦ by exact zero_le _) hzero_mem

/-- Helper for Theorem 19.33: the shifted finite left Solomon prefixes converge to the full left
series `R_w^-`. -/
private theorem randomEnvironmentLeftPrefixSum_tendsto
    (W : RandomEnvironment) :
    Tendsto (fun N : ℕ ↦ randomEnvironmentLeftPrefixSum W N) atTop (nhds R⁻[W]) := by
  -- Proof comment: `randomEnvironmentLeftPrefixSum W N` is exactly the `(N + 1)`st partial sum
  -- of the defining `tsum` for `R_w^-`.
  simpa [randomEnvironmentLeftSeries_def, randomEnvironmentLeftPrefixSum] using
    (ENNReal.tendsto_nat_tsum (randomEnvironmentLeftSeriesTerm W)).comp
      (tendsto_add_atTop_nat 1)

/-- Helper for Theorem 19.33: the shifted finite right Solomon prefixes converge to the full right
series `R_w^+`. -/
private theorem randomEnvironmentRightPrefixSum_tendsto
    (W : RandomEnvironment) :
    Tendsto (fun N : ℕ ↦ randomEnvironmentRightPrefixSum W N) atTop (nhds R⁺[W]) := by
  -- Proof comment: the right prefix owner is the same shifted partial-sum surface for `R_w^+`.
  simpa [randomEnvironmentRightSeries_def, randomEnvironmentRightPrefixSum] using
    (ENNReal.tendsto_nat_tsum (randomEnvironmentRightSeriesTerm W)).comp
      (tendsto_add_atTop_nat 1)

/-- Helper for Theorem 19.33: finite `ℝ≥0∞` values that diverge to `∞` have real parts that
diverge to `+∞`. -/
private theorem ennrealToReal_tendsto_atTop_of_tendsto_top
    {f : ℕ → ℝ≥0∞} (hfinite : ∀ n : ℕ, f n ≠ ∞)
    (htop : Tendsto f atTop (nhds ∞)) :
    Tendsto (fun n : ℕ ↦ (f n).toReal) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro r
  have hEventually : ∀ᶠ n : ℕ in atTop, ((⌈r⌉₊ : ℕ) : ℝ≥0∞) < f n :=
    (ENNReal.tendsto_nhds_top_iff_nat.1 htop) ⌈r⌉₊
  filter_upwards [hEventually] with n hn
  have hceil_le : r ≤ (⌈r⌉₊ : ℝ) := by
    exact Nat.le_ceil r
  have htoReal_ge : (⌈r⌉₊ : ℝ) ≤ (f n).toReal := by
    simpa using ENNReal.toReal_mono (hfinite n) (le_of_lt hn)
  exact le_trans hceil_le htoReal_ge

/-- Helper for Theorem 19.33: when both Solomon series are finite, the finite symmetric-corridor
prefix ratios converge to the limiting Solomon ratio. -/
private theorem twoRayPrefixRatio_tendsto_of_bothFinite
    (hW : W.IsElliptic) (hleft : R⁻[W] < ∞) (hright : R⁺[W] < ∞) :
    Tendsto (fun N : ℕ ↦ randomEnvironmentLeftExitPrefixRatio W N) atTop
      (nhds (R⁺[W].toReal / (R⁻[W].toReal + R⁺[W].toReal))) := by
  have hleftReal :
      Tendsto (fun N : ℕ ↦ (randomEnvironmentLeftPrefixSum W N).toReal) atTop
        (nhds R⁻[W].toReal) := by
    -- Proof comment: finite left prefixes converge in `ℝ≥0∞`, so continuity of `toReal` at the
    -- finite limit transports that convergence to `ℝ`.
    exact (ENNReal.tendsto_toReal hleft.ne).comp
      (randomEnvironmentLeftPrefixSum_tendsto (W := W))
  have hrightReal :
      Tendsto (fun N : ℕ ↦ (randomEnvironmentRightPrefixSum W N).toReal) atTop
        (nhds R⁺[W].toReal) := by
    -- Proof comment: the same continuity argument applies to the right prefix sums.
    exact (ENNReal.tendsto_toReal hright.ne).comp
      (randomEnvironmentRightPrefixSum_tendsto (W := W))
  have hleft_pos : 0 < R⁻[W].toReal := by
    exact ENNReal.toReal_pos ((randomEnvironmentLeftSeries_pos (W := W)).ne') hleft.ne
  have hright_pos : 0 < R⁺[W].toReal := by
    exact ENNReal.toReal_pos ((randomEnvironmentRightSeries_pos (W := W) hW).ne') hright.ne
  have hsum_ne : R⁻[W].toReal + R⁺[W].toReal ≠ 0 := by
    exact (add_pos hleft_pos hright_pos).ne'
  have hden :
      Tendsto
        (fun N : ℕ ↦
          (randomEnvironmentLeftPrefixSum W N).toReal +
            (randomEnvironmentRightPrefixSum W N).toReal)
        atTop
        (nhds (R⁻[W].toReal + R⁺[W].toReal)) :=
    hleftReal.add hrightReal
  -- Proof comment: once both finite prefix sums converge, the ratio owner is a continuous real
  -- quotient because the limiting total resistance is strictly positive.
  simpa [randomEnvironmentLeftExitPrefixRatio] using
    hrightReal.div hden hsum_ne

/-- Helper for Theorem 19.33: the finite left/right corridor exit ratios are complementary,
because both use the same total prefix resistance in the denominator. -/
private theorem randomEnvironmentRightExitPrefixRatio_eq_one_sub_leftExitPrefixRatio
    (hW : W.IsElliptic) (N : ℕ) :
    randomEnvironmentRightExitPrefixRatio W N =
      1 - randomEnvironmentLeftExitPrefixRatio W N := by
  let leftSum : ℝ≥0∞ := randomEnvironmentLeftPrefixSum W N
  let rightSum : ℝ≥0∞ := randomEnvironmentRightPrefixSum W N
  have hleftSum_pos : 0 < leftSum.toReal := by
    have hterm0 : 0 < (randomEnvironmentLeftSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        ((randomEnvironmentLeftSeriesTerm_pos (W := W) hW 0).ne')
        (randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentLeftSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentLeftSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentLeftSeriesTerm_ne_top (W := W) hW i
  have hrightSum_pos : 0 < rightSum.toReal := by
    have hterm0 : 0 < (randomEnvironmentRightSeriesTerm W 0).toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentRightSeriesTerm_pos (W := W) hW 0).ne'
        (randomEnvironmentRightSeriesTerm_ne_top (W := W) hW 0)
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 1))
          (fun i ↦ (randomEnvironmentRightSeriesTerm W i).toReal) := by
      exact lt_of_lt_of_le hterm0
        (Finset.single_le_sum (fun j _ ↦ ENNReal.toReal_nonneg) hmem)
    change 0 <
      (Finset.sum (Finset.range (N + 1))
        (fun i ↦ randomEnvironmentRightSeriesTerm W i)).toReal
    rw [ENNReal.toReal_sum]
    · exact hsum_pos
    · intro i hi
      exact randomEnvironmentRightSeriesTerm_ne_top (W := W) hW i
  have hsum_ne : leftSum.toReal + rightSum.toReal ≠ 0 := (add_pos hleftSum_pos hrightSum_pos).ne'
  -- Proof comment: the two finite exit ratios add to `1` because they share the same positive
  -- denominator and their numerators sum to the full prefix resistance.
  rw [eq_sub_iff_add_eq, randomEnvironmentRightExitPrefixRatio, randomEnvironmentLeftExitPrefixRatio]
  calc
    leftSum.toReal / (leftSum.toReal + rightSum.toReal) +
        rightSum.toReal / (leftSum.toReal + rightSum.toReal)
        = (leftSum.toReal + rightSum.toReal) / (leftSum.toReal + rightSum.toReal) := by
            rw [add_div]
    _ = 1 := by rw [div_self hsum_ne]

/-- Helper for Theorem 19.33: when both Solomon series are finite, the complementary finite
symmetric-corridor prefix ratios converge to the left Solomon ratio. -/
private theorem leftPrefixRatio_tendsto_of_bothFinite
    (hW : W.IsElliptic) (hleft : R⁻[W] < ∞) (hright : R⁺[W] < ∞) :
    Tendsto (fun N : ℕ ↦ randomEnvironmentRightExitPrefixRatio W N) atTop
      (nhds (R⁻[W].toReal / (R⁻[W].toReal + R⁺[W].toReal))) := by
  have hratio :
      (fun N : ℕ ↦ randomEnvironmentRightExitPrefixRatio W N) =
        fun N ↦ 1 - randomEnvironmentLeftExitPrefixRatio W N := by
    funext N
    exact randomEnvironmentRightExitPrefixRatio_eq_one_sub_leftExitPrefixRatio
      (W := W) hW N
  let leftSeries : ℝ≥0∞ := R⁻[W]
  let rightSeries : ℝ≥0∞ := R⁺[W]
  have hleft_pos : 0 < leftSeries.toReal := by
    exact ENNReal.toReal_pos ((randomEnvironmentLeftSeries_pos (W := W)).ne') hleft.ne
  have hright_pos : 0 < rightSeries.toReal := by
    exact ENNReal.toReal_pos ((randomEnvironmentRightSeries_pos (W := W) hW).ne') hright.ne
  have hsum_ne : leftSeries.toReal + rightSeries.toReal ≠ 0 := (add_pos hleft_pos hright_pos).ne'
  have htarget :
      1 - (rightSeries.toReal / (leftSeries.toReal + rightSeries.toReal)) =
        leftSeries.toReal / (leftSeries.toReal + rightSeries.toReal) := by
    apply (sub_eq_iff_eq_add).2
    calc
      1 = (leftSeries.toReal + rightSeries.toReal) / (leftSeries.toReal + rightSeries.toReal) := by
            rw [div_self hsum_ne]
      _ = leftSeries.toReal / (leftSeries.toReal + rightSeries.toReal) +
            rightSeries.toReal / (leftSeries.toReal + rightSeries.toReal) := by
              rw [add_div]
  rw [hratio]
  -- Proof comment: the right-exit ratios are the complements of the left-exit ratios, so the
  -- limit follows from the left-ratio theorem by subtracting from the constant sequence `1`.
  have hconst :
      Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds (1 : ℝ)) := tendsto_const_nhds
  have hsub :
      Tendsto (fun N : ℕ ↦ 1 - randomEnvironmentLeftExitPrefixRatio W N) atTop
        (nhds (1 - rightSeries.toReal / (leftSeries.toReal + rightSeries.toReal))) :=
    hconst.sub (twoRayPrefixRatio_tendsto_of_bothFinite (W := W) hW hleft hright)
  have htarget_nhds :
      nhds (1 - rightSeries.toReal / (leftSeries.toReal + rightSeries.toReal)) =
        nhds (leftSeries.toReal / (leftSeries.toReal + rightSeries.toReal)) := by
    rw [htarget]
  simpa [leftSeries, rightSeries] using (htarget_nhds ▸ hsub)

/-- Helper for Theorem 19.33: if the left Solomon series diverges while the right one is finite,
then the finite right-prefix ratios tend to `0`. -/
private theorem rightPrefixRatio_tendsto_zero_of_leftSeries_eq_top
    (hW : W.IsElliptic) (hright : R⁺[W] < ∞) (hleft : R⁻[W] = ∞) :
    Tendsto (fun N : ℕ ↦ randomEnvironmentLeftExitPrefixRatio W N) atTop (nhds (0 : ℝ)) := by
  have hleftPrefixTop :
      Tendsto (fun N : ℕ ↦ randomEnvironmentLeftPrefixSum W N) atTop (nhds ∞) := by
    have hbase := randomEnvironmentLeftPrefixSum_tendsto (W := W)
    have hseries : R⁻[W] = ∞ := hleft
    rw [show R⁻[W] = ∞ by exact hseries] at hbase
    exact hbase
  have hleftToRealTop :
      Tendsto (fun N : ℕ ↦ (randomEnvironmentLeftPrefixSum W N).toReal) atTop atTop := by
    -- Proof comment: divergent finite left prefixes force their real parts to diverge.
    exact ennrealToReal_tendsto_atTop_of_tendsto_top
      (fun N ↦ randomEnvironmentLeftPrefixSum_ne_top (W := W) hW N)
      hleftPrefixTop
  have hInv :
      Tendsto (fun N : ℕ ↦ (randomEnvironmentLeftPrefixSum W N).toReal⁻¹) atTop (nhds 0) :=
    hleftToRealTop.inv_tendsto_atTop
  have hUpper :
      Tendsto
        (fun N : ℕ ↦ R⁺[W].toReal * (randomEnvironmentLeftPrefixSum W N).toReal⁻¹)
        atTop
        (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hInv)
  apply squeeze_zero
  · intro N
    unfold randomEnvironmentLeftExitPrefixRatio
    positivity
  · intro N
    let leftSum : ℝ≥0∞ := randomEnvironmentLeftPrefixSum W N
    let rightSum : ℝ≥0∞ := randomEnvironmentRightPrefixSum W N
    have hleftPos : 0 < leftSum.toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentLeftPrefixSum_pos (W := W) hW N).ne'
        (randomEnvironmentLeftPrefixSum_ne_top (W := W) hW N)
    have hrightLe : rightSum ≤ R⁺[W] := by
      rw [randomEnvironment_rightSeries_eq_iSup_prefixSucc]
      exact le_iSup (fun n : ℕ ↦ randomEnvironmentRightPrefixSum W n) N
    have hrightRealLe : rightSum.toReal ≤ R⁺[W].toReal := by
      exact ENNReal.toReal_mono hright.ne hrightLe
    have hleftLeDenom : leftSum.toReal ≤ leftSum.toReal + rightSum.toReal := by
      exact le_add_of_nonneg_right ENNReal.toReal_nonneg
    have hInvLe :
        (leftSum.toReal + rightSum.toReal)⁻¹ ≤ (leftSum.toReal)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hleftPos hleftLeDenom
    calc
      randomEnvironmentLeftExitPrefixRatio W N
          = rightSum.toReal / (leftSum.toReal + rightSum.toReal) := by
              simp [randomEnvironmentLeftExitPrefixRatio, leftSum, rightSum]
      _ = rightSum.toReal * (leftSum.toReal + rightSum.toReal)⁻¹ := by
            rw [div_eq_mul_inv]
      _ ≤ rightSum.toReal * (leftSum.toReal)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hInvLe ENNReal.toReal_nonneg
      _ ≤ R⁺[W].toReal * (leftSum.toReal)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hrightRealLe
              (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ = R⁺[W].toReal * (randomEnvironmentLeftPrefixSum W N).toReal⁻¹ := by
            simp [leftSum]
  · simpa using hUpper

/-- Helper for Theorem 19.33: if the right Solomon series diverges while the left one is finite,
then the finite left-prefix ratios tend to `0`. -/
private theorem leftPrefixRatio_tendsto_zero_of_rightSeries_eq_top
    (hW : W.IsElliptic) (hleft : R⁻[W] < ∞) (hright : R⁺[W] = ∞) :
    Tendsto (fun N : ℕ ↦ randomEnvironmentRightExitPrefixRatio W N) atTop (nhds (0 : ℝ)) := by
  have hrightPrefixTop :
      Tendsto (fun N : ℕ ↦ randomEnvironmentRightPrefixSum W N) atTop (nhds ∞) := by
    have hbase := randomEnvironmentRightPrefixSum_tendsto (W := W)
    have hseries : R⁺[W] = ∞ := hright
    rw [show R⁺[W] = ∞ by exact hseries] at hbase
    exact hbase
  have hrightToRealTop :
      Tendsto (fun N : ℕ ↦ (randomEnvironmentRightPrefixSum W N).toReal) atTop atTop := by
    -- Proof comment: divergent finite right prefixes force their real parts to diverge.
    exact ennrealToReal_tendsto_atTop_of_tendsto_top
      (fun N ↦ randomEnvironmentRightPrefixSum_ne_top (W := W) hW N)
      hrightPrefixTop
  have hInv :
      Tendsto (fun N : ℕ ↦ (randomEnvironmentRightPrefixSum W N).toReal⁻¹) atTop (nhds 0) :=
    hrightToRealTop.inv_tendsto_atTop
  have hUpper :
      Tendsto
        (fun N : ℕ ↦ R⁻[W].toReal * (randomEnvironmentRightPrefixSum W N).toReal⁻¹)
        atTop
        (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hInv)
  apply squeeze_zero
  · intro N
    unfold randomEnvironmentRightExitPrefixRatio
    positivity
  · intro N
    let leftSum : ℝ≥0∞ := randomEnvironmentLeftPrefixSum W N
    let rightSum : ℝ≥0∞ := randomEnvironmentRightPrefixSum W N
    have hrightPos : 0 < rightSum.toReal := by
      exact ENNReal.toReal_pos
        (randomEnvironmentRightPrefixSum_pos (W := W) hW N).ne'
        (randomEnvironmentRightPrefixSum_ne_top (W := W) hW N)
    have hleftLe : leftSum ≤ R⁻[W] := by
      rw [randomEnvironment_leftSeries_eq_iSup_prefixSucc]
      exact le_iSup (fun n : ℕ ↦ randomEnvironmentLeftPrefixSum W n) N
    have hleftRealLe : leftSum.toReal ≤ R⁻[W].toReal := by
      exact ENNReal.toReal_mono hleft.ne hleftLe
    have hrightLeDenom : rightSum.toReal ≤ leftSum.toReal + rightSum.toReal := by
      exact le_add_of_nonneg_left ENNReal.toReal_nonneg
    have hInvLe :
        (leftSum.toReal + rightSum.toReal)⁻¹ ≤ (rightSum.toReal)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hrightPos hrightLeDenom
    calc
      randomEnvironmentRightExitPrefixRatio W N
          = leftSum.toReal / (leftSum.toReal + rightSum.toReal) := by
              simp [randomEnvironmentRightExitPrefixRatio, leftSum, rightSum]
      _ = leftSum.toReal * (leftSum.toReal + rightSum.toReal)⁻¹ := by
            rw [div_eq_mul_inv]
      _ ≤ leftSum.toReal * (rightSum.toReal)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hInvLe ENNReal.toReal_nonneg
      _ ≤ R⁻[W].toReal * (rightSum.toReal)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hleftRealLe
              (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ = R⁻[W].toReal * (randomEnvironmentRightPrefixSum W N).toReal⁻¹ := by
            simp [rightSum]
  · simpa using hUpper

section DirectionalEscape

-- Proof sketch: approximate the two-point boundary `{−N, N}` and use the finite-interval exit
-- formula for a one-dimensional RWRE. Passing to the limit yields Solomon's textbook ratio
-- `R_w^+ / (R_w^- + R_w^+)`, interpreted with Solomon's convention `∞ / ∞ = 1`.
/-- Theorem 19.33 (1): for an elliptic environment, if `R_w^- < ∞` or `R_w^+ < ∞`, then the
probability that the walk started from `0` tends to `-∞` is
`R_w^+ / (R_w^- + R_w^+)`, with Solomon's convention `∞ / ∞ = 1`. -/
theorem randomEnvironmentWalk_prob_tendsToNegInfinity
    (hW : W.IsElliptic)
    (hfinite : R⁻[W] < ∞ ∨ R⁺[W] < ∞) :
    (P 0 : Measure Ω) {ω | Tendsto (fun n ↦ X n ω) atTop atBot} =
      solomonDirectionalSeriesRatio R⁺[W] R⁻[W] := by
  let μ : Measure Ω := (P 0 : Measure Ω)
  let A : Set Ω := {ω | Tendsto (fun n ↦ X n ω) atTop atBot}
  let B : Set Ω := {ω | Tendsto (fun n ↦ X n ω) atTop atTop}
  let ASlice : ℕ → Set Ω := fun N ↦
    {ω | Tendsto (fun n ↦ X n ω) atTop atBot ∧
      ∀ n : ℕ, X n ω < ((N + 1 : ℕ) : ℤ)}
  let BSlice : ℕ → Set Ω := fun N ↦
    {ω | Tendsto (fun n ↦ X n ω) atTop atTop ∧
      ∀ n : ℕ, -((N + 1 : ℕ) : ℤ) < X n ω}
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hA_meas : MeasurableSet A := by
    simpa [A] using measurableSet_tendsto atBot (fun n ↦ hReal.measurable_process n)
  have hB_meas : MeasurableSet B := by
    simpa [B] using measurableSet_tendsto atTop (fun n ↦ hReal.measurable_process n)
  have hA_union : A = ⋃ N : ℕ, ASlice N := by
    simpa [A, ASlice] using tendstoAtBot_set_eq_iUnion_uniformUpperSlices X
  have hB_union : B = ⋃ N : ℕ, BSlice N := by
    simpa [B, BSlice] using tendstoAtTop_set_eq_iUnion_uniformLowerSlices X
  have hASlice_mono : Monotone ASlice := by
    intro m n hmn ω hω
    constructor
    · exact hω.1
    · intro k
      exact lt_of_lt_of_le (hω.2 k) (by
        exact_mod_cast Nat.succ_le_succ hmn)
  have hBSlice_mono : Monotone BSlice := by
    intro m n hmn ω hω
    constructor
    · exact hω.1
    · intro k
      have hbound : -((n + 1 : ℕ) : ℤ) ≤ -((m + 1 : ℕ) : ℤ) := by
        omega
      exact lt_of_le_of_lt hbound (hω.2 k)
  have hA_tendsto_enn :
      Tendsto (fun N : ℕ ↦ μ (ASlice N)) atTop (nhds (μ A)) := by
    simpa [μ, hA_union] using (tendsto_measure_iUnion_atTop (μ := μ) hASlice_mono)
  have hB_tendsto_enn :
      Tendsto (fun N : ℕ ↦ μ (BSlice N)) atTop (nhds (μ B)) := by
    simpa [μ, hB_union] using (tendsto_measure_iUnion_atTop (μ := μ) hBSlice_mono)
  have hA_tendsto :
      Tendsto (fun N : ℕ ↦ (μ (ASlice N)).toReal) atTop (nhds (μ A).toReal) := by
    rw [← ENNReal.tendsto_toReal_iff
      (fun N ↦ measure_ne_top μ (ASlice N))
      (measure_ne_top μ A)] at hA_tendsto_enn
    simpa [Measure.real_def] using hA_tendsto_enn
  have hB_tendsto :
      Tendsto (fun N : ℕ ↦ (μ (BSlice N)).toReal) atTop (nhds (μ B).toReal) := by
    rw [← ENNReal.tendsto_toReal_iff
      (fun N ↦ measure_ne_top μ (BSlice N))
      (measure_ne_top μ B)] at hB_tendsto_enn
    simpa [Measure.real_def] using hB_tendsto_enn
  have hASlice_le :
      ∀ N : ℕ, (μ (ASlice N)).toReal ≤ randomEnvironmentLeftExitPrefixRatio W N := by
    intro N
    calc
      (μ (ASlice N)).toReal
          ≤ F_A P X ({((N + 1 : ℕ) : ℤ)} : Set ℤ) 0 (-((N + 1 : ℕ) : ℤ)) := by
              simpa [μ, ASlice] using
                tendstoAtBot_uniformUpperSlice_real_le_leftBoundaryF_A
                  (W := W) (P := P) (X := X) N
      _ = randomEnvironmentLeftExitPrefixRatio W N := by
            simpa using
              twoRayLeftExitProbability_eq_prefixRatio
                (W := W) (P := P) (X := X) hW N
  have hBSlice_le :
      ∀ N : ℕ, (μ (BSlice N)).toReal ≤ randomEnvironmentRightExitPrefixRatio W N := by
    intro N
    calc
      (μ (BSlice N)).toReal
          ≤ F_A P X ({-((N + 1 : ℕ) : ℤ)} : Set ℤ) 0 (((N + 1 : ℕ) : ℤ)) := by
              simpa [μ, BSlice] using
                tendstoAtTop_uniformLowerSlice_real_le_rightBoundaryF_A
                  (W := W) (P := P) (X := X) N
      _ = randomEnvironmentRightExitPrefixRatio W N := by
            simpa using
              twoRayRightExitProbability_eq_prefixRatio
                (W := W) (P := P) (X := X) hW N
  have hdich :
      ∀ᵐ ω ∂μ, ω ∈ A ∪ B := by
    filter_upwards [randomEnvironmentEventuallyDirectional_ae_of_oneSeries_finite
      (W := W) (P := P) (X := X) hW hfinite] with ω hω
    simpa [A, B] using hω
  have hA_ae_compl : A =ᵐ[μ] Bᶜ := by
    filter_upwards [hdich] with ω hω
    apply propext
    constructor
    · intro hA hB
      exact (hA.not_tendsto disjoint_atBot_atTop) hB
    · intro hB
      rcases hω with hω | hω
      · exact hω
      · exact False.elim (hB hω)
  by_cases hleft_top : R⁻[W] = ∞
  · by_cases hright_top : R⁺[W] = ∞
    · exfalso
      rcases hfinite with hleft | hright
      · exact hleft.ne hleft_top
      · exact hright.ne hright_top
    · have hright_fin : R⁺[W] < ∞ := lt_top_iff_ne_top.2 hright_top
      have hA_zero_real :
          (μ A).toReal = 0 := by
        have hupper :
            Tendsto (fun N : ℕ ↦ randomEnvironmentLeftExitPrefixRatio W N) atTop (nhds (0 : ℝ)) :=
          rightPrefixRatio_tendsto_zero_of_leftSeries_eq_top (W := W) hW hright_fin hleft_top
        have hA_le_zero :
            (μ A).toReal ≤ 0 := by
          exact le_of_tendsto_of_tendsto' hA_tendsto hupper hASlice_le
        exact le_antisymm hA_le_zero ENNReal.toReal_nonneg
      have hA_zero : μ A = 0 := by
        by_contra hA_nonzero
        have hA_pos : 0 < (μ A).toReal := by
          exact ENNReal.toReal_pos hA_nonzero (measure_ne_top μ A)
        rw [hA_zero_real] at hA_pos
        exact lt_irrefl _ hA_pos
      rw [solomonDirectionalSeriesRatio_eq_div hright_fin, hleft_top, top_add]
      simpa [μ, A, hA_zero, hright_fin.ne]
  · have hleft_fin : R⁻[W] < ∞ := lt_top_iff_ne_top.2 hleft_top
    by_cases hright_top : R⁺[W] = ∞
    · have hB_zero_real :
          (μ B).toReal = 0 := by
        have hupper :
            Tendsto (fun N : ℕ ↦ randomEnvironmentRightExitPrefixRatio W N) atTop (nhds (0 : ℝ)) :=
          leftPrefixRatio_tendsto_zero_of_rightSeries_eq_top (W := W) hW hleft_fin hright_top
        have hB_le_zero :
            (μ B).toReal ≤ 0 := by
          exact le_of_tendsto_of_tendsto' hB_tendsto hupper hBSlice_le
        exact le_antisymm hB_le_zero ENNReal.toReal_nonneg
      have hB_zero : μ B = 0 := by
        by_contra hB_nonzero
        have hB_pos : 0 < (μ B).toReal := by
          exact ENNReal.toReal_pos hB_nonzero (measure_ne_top μ B)
        rw [hB_zero_real] at hB_pos
        exact lt_irrefl _ hB_pos
      have hμA : μ A = 1 := by
        calc
          μ A = μ Bᶜ := by simpa using measure_congr hA_ae_compl
          _ = 1 - μ B := by
                exact MeasureTheory.prob_compl_eq_one_sub (μ := μ) (s := B) hB_meas
          _ = 1 := by simp [hB_zero]
      rw [solomonDirectionalSeriesRatio_eq_one hright_top]
      simpa [μ, A] using hμA
    · have hright_fin : R⁺[W] < ∞ := lt_top_iff_ne_top.2 hright_top
      have hA_upper :
          Tendsto
            (fun N : ℕ ↦ randomEnvironmentLeftExitPrefixRatio W N)
            atTop
            (nhds
              (R⁺[W].toReal / (R⁻[W].toReal + R⁺[W].toReal))) :=
        twoRayPrefixRatio_tendsto_of_bothFinite (W := W) hW hleft_fin hright_fin
      have hB_upper :
          Tendsto
            (fun N : ℕ ↦ randomEnvironmentRightExitPrefixRatio W N)
            atTop
            (nhds
              (R⁻[W].toReal / (R⁻[W].toReal + R⁺[W].toReal))) :=
        leftPrefixRatio_tendsto_of_bothFinite (W := W) hW hleft_fin hright_fin
      have hA_real_le :
          (μ A).toReal ≤ R⁺[W].toReal / (R⁻[W].toReal + R⁺[W].toReal) :=
        le_of_tendsto_of_tendsto' hA_tendsto hA_upper hASlice_le
      have hB_real_le :
          (μ B).toReal ≤ R⁻[W].toReal / (R⁻[W].toReal + R⁺[W].toReal) :=
        le_of_tendsto_of_tendsto' hB_tendsto hB_upper hBSlice_le
      have hA_real_compl :
          (μ A).toReal = 1 - (μ B).toReal := by
        calc
          (μ A).toReal = (μ Bᶜ).toReal := by
            simpa using congrArg ENNReal.toReal (measure_congr hA_ae_compl)
          _ = (1 - μ B).toReal := by
            rw [MeasureTheory.prob_compl_eq_one_sub (μ := μ) (s := B) hB_meas]
          _ = 1 - (μ B).toReal := by
            have hμB_le_one : μ B ≤ 1 := by
              simpa [μ] using (show μ B ≤ μ Set.univ from measure_mono (by intro ω hω; simp))
            simpa using ENNReal.toReal_sub_of_le hμB_le_one (by simp : (1 : ℝ≥0∞) ≠ ∞)
      have hA_real_ge :
          R⁺[W].toReal / (R⁻[W].toReal + R⁺[W].toReal) ≤ (μ A).toReal := by
        have hcompl :
            1 -
              (R⁻[W].toReal / (R⁻[W].toReal + R⁺[W].toReal)) =
                R⁺[W].toReal / (R⁻[W].toReal + R⁺[W].toReal) := by
          have hsum_ne :
              R⁻[W].toReal + R⁺[W].toReal ≠ 0 := by
            exact (add_pos
              (ENNReal.toReal_pos ((randomEnvironmentLeftSeries_pos (W := W)).ne') hleft_fin.ne)
              (ENNReal.toReal_pos ((randomEnvironmentRightSeries_pos (W := W) hW).ne')
                hright_fin.ne)).ne'
          field_simp [hsum_ne]
          ring
        rw [hA_real_compl]
        linarith
      have hA_real :
          (μ A).toReal = R⁺[W].toReal / (R⁻[W].toReal + R⁺[W].toReal) :=
        le_antisymm hA_real_le hA_real_ge
      have hsum_pos : 0 < R⁻[W].toReal + R⁺[W].toReal := by
        exact add_pos
          (ENNReal.toReal_pos ((randomEnvironmentLeftSeries_pos (W := W)).ne') hleft_fin.ne)
          (ENNReal.toReal_pos ((randomEnvironmentRightSeries_pos (W := W) hW).ne') hright_fin.ne)
      have hsum_ne_zero : R⁻[W] + R⁺[W] ≠ 0 := by
        intro hsum
        have hsum_real : (R⁻[W] + R⁺[W]).toReal = 0 := by
          simpa using congrArg ENNReal.toReal hsum
        have hsum_toReal :
            (R⁻[W] + R⁺[W]).toReal = R⁻[W].toReal + R⁺[W].toReal := by
          rw [ENNReal.toReal_add hleft_fin.ne hright_fin.ne]
        have hsum_real_pos : 0 < (R⁻[W] + R⁺[W]).toReal := by
          rw [hsum_toReal]
          exact hsum_pos
        rw [hsum_real] at hsum_real_pos
        exact lt_irrefl _ hsum_real_pos
      have htarget_ne_top :
          solomonDirectionalSeriesRatio R⁺[W] R⁻[W] ≠ ∞ := by
        rw [solomonDirectionalSeriesRatio_eq_div hright_fin]
        exact ENNReal.div_ne_top hright_fin.ne hsum_ne_zero
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) htarget_ne_top).mp
      rw [solomonDirectionalSeriesRatio_eq_div hright_fin]
      have hsum_ne_top : R⁻[W] + R⁺[W] ≠ ∞ := by
        exact (ENNReal.add_ne_top).2 ⟨hleft_fin.ne, hright_fin.ne⟩
      have hA_real' :
          (μ A).toReal = R⁺[W].toReal / (R⁻[W] + R⁺[W]).toReal := by
        rw [ENNReal.toReal_add hleft_fin.ne hright_fin.ne]
        exact hA_real
      simpa [μ, A, Measure.real_def, ENNReal.toReal_div, hright_fin.ne, hsum_ne_zero, hsum_ne_top]
        using hA_real'

-- Proof sketch: the same finite-interval computation, now for exiting at `+N`, gives Solomon's
-- complementary ratio `R_w^- / (R_w^- + R_w^+)`, again with the convention `∞ / ∞ = 1`.
/-- Theorem 19.33 (2): for an elliptic environment, if `R_w^- < ∞` or `R_w^+ < ∞`, then the
probability that the walk started from `0` tends to `+∞` is
`R_w^- / (R_w^- + R_w^+)`, with Solomon's convention `∞ / ∞ = 1`. -/
theorem randomEnvironmentWalk_prob_tendsToPosInfinity
    (hW : W.IsElliptic)
    (hfinite : R⁻[W] < ∞ ∨ R⁺[W] < ∞) :
    (P 0 : Measure Ω) {ω | Tendsto (fun n ↦ X n ω) atTop atTop} =
      solomonDirectionalSeriesRatio R⁻[W] R⁺[W] := by
  let A : Set Ω := {ω | Tendsto (fun n ↦ X n ω) atTop atBot}
  let B : Set Ω := {ω | Tendsto (fun n ↦ X n ω) atTop atTop}
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X :=
    inferInstance
  have hA_meas : MeasurableSet A := by
    -- Proof comment: convergence to `-∞` is measurable because each coordinate map `ω ↦ X n ω`
    -- is measurable and `atBot` is a measurable target filter on the discrete state space `ℤ`.
    simpa [A] using measurableSet_tendsto atBot (fun n ↦ hReal.measurable_process n)
  have hdich :
      ∀ᵐ ω ∂(P 0 : Measure Ω), ω ∈ A ∪ B := by
    filter_upwards [randomEnvironmentEventuallyDirectional_ae_of_oneSeries_finite
      (W := W) (P := P) (X := X) hW hfinite] with ω hω
    simpa [A, B] using hω
  have hB_ae : B =ᵐ[(P 0 : Measure Ω)] Aᶜ := by
    filter_upwards [hdich] with ω hω
    apply propext
    constructor
    · intro hB hA
      exact (hA.not_tendsto disjoint_atBot_atTop) hB
    · intro hA
      rcases hω with hω | hω
      · exact False.elim (hA hω)
      · exact hω
  -- Proof comment: the transient dichotomy from the finite-visits endgame identifies the `+∞`
  -- event with the complement of the `-∞` event, so only the algebra of Solomon's two ratios
  -- remains once the negative-direction theorem is substituted.
  change (P 0 : Measure Ω) B = solomonDirectionalSeriesRatio R⁻[W] R⁺[W]
  calc
    (P 0 : Measure Ω) B = (P 0 : Measure Ω) Aᶜ := by
      simpa using measure_congr hB_ae
    _ = 1 - (P 0 : Measure Ω) A := by
      rw [measure_compl hA_meas (measure_ne_top _ _), measure_univ]
    _ = 1 - solomonDirectionalSeriesRatio R⁺[W] R⁻[W] := by
      rw [randomEnvironmentWalk_prob_tendsToNegInfinity
        (W := W) (P := P) (X := X) hW hfinite]
    _ = solomonDirectionalSeriesRatio R⁻[W] R⁺[W] := by
      exact solomonDirectionalSeriesRatio_compl
        (htoward_pos := randomEnvironmentRightSeries_pos (W := W) hW)
        (haway_pos := randomEnvironmentLeftSeries_pos (W := W))
        (hfinite := hfinite.elim Or.inr Or.inl)

end DirectionalEscape

section Oscillation

-- Proof sketch: in an elliptic environment, when both Solomon series diverge, the one-dimensional
-- RWRE is recurrent. A recurrent nearest-neighbor walk on `ℤ` visits arbitrarily negative states
-- infinitely often, so its pathwise `liminf` is `-∞`.
/-- Theorem 19.33 (3): for an elliptic environment, if `R_w^- = ∞` and `R_w^+ = ∞`, then
`liminf X_n = -∞` almost surely. -/
theorem randomEnvironmentWalk_ae_hasLiminfEqNegInfinity
    (hW : W.IsElliptic) (hleft : R⁻[W] = ∞) (hright : R⁺[W] = ∞) :
    ∀ᵐ ω ∂(P 0 : Measure Ω), liminf (fun n ↦ (((X n ω : ℤ) : ℝ) : EReal)) atTop = ⊥ := by
  -- Route correction: the deterministic `EReal` endgame is now isolated. The remaining blocker is
  -- the probabilistic bridge from `hleft`, `hright` to almost-sure hits of every integer.
  have hhitAll :
      ∀ᵐ ω ∂(P 0 : Measure Ω),
        (∀ m : ℕ, ∃ n : ℕ, X n ω = -((m : ℤ))) ∧
          ∀ m : ℕ, ∃ n : ℕ, X n ω = m :=
    randomEnvironmentHitsEveryInteger_ae_of_bothSeries_eq_top W P X hW hleft hright
  filter_upwards [hhitAll] with ω hω
  exact
    (integerPath_liminf_eq_bot_and_limsup_eq_top_of_hitsEveryInteger
      (fun n ↦ X n ω) hω.1 hω.2).1

-- Proof sketch: in the same elliptic recurrent regime, the walk also visits arbitrarily large
-- positive states infinitely often, hence `limsup X_n = +∞`.
/-- Theorem 19.33 (4): for an elliptic environment, if `R_w^- = ∞` and `R_w^+ = ∞`, then
`limsup X_n = +∞` almost surely. -/
theorem randomEnvironmentWalk_ae_hasLimsupEqPosInfinity
    (hW : W.IsElliptic) (hleft : R⁻[W] = ∞) (hright : R⁺[W] = ∞) :
    ∀ᵐ ω ∂(P 0 : Measure Ω), limsup (fun n ↦ (((X n ω : ℤ) : ℝ) : EReal)) atTop = ⊤ := by
  -- Route correction: after isolating the deterministic helper, the positive-side theorem has the
  -- same single blocker as the liminf statement: produce a.s. hits of all integer levels.
  have hhitAll :
      ∀ᵐ ω ∂(P 0 : Measure Ω),
        (∀ m : ℕ, ∃ n : ℕ, X n ω = -((m : ℤ))) ∧
          ∀ m : ℕ, ∃ n : ℕ, X n ω = m :=
    randomEnvironmentHitsEveryInteger_ae_of_bothSeries_eq_top W P X hW hleft hright
  filter_upwards [hhitAll] with ω hω
  exact
    (integerPath_liminf_eq_bot_and_limsup_eq_top_of_hitsEveryInteger
      (fun n ↦ X n ω) hω.1 hω.2).2

end Oscillation

end RWRERealization

end ProbabilityTheory

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics
public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.Specialization
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngleDrift
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

open Filter
open scoped Asymptotics BigOperators Topology

namespace DFP.TwoPhaseOrbit

/-- Helper for `slowCurveOneTurnAmplitudeDropAsymptotic`: consecutive forward
differences telescope over a natural-number interval. -/
private theorem sum_Ico_forwardDifference (u : ℕ → ℝ) {j ℓ : ℕ} (hjℓ : j ≤ ℓ) :
    ∑ t ∈ Finset.Ico j ℓ, (u t - u (t + 1)) = u j - u ℓ := by
  rw [Finset.sum_Ico_eq_sub _ hjℓ, Finset.sum_range_sub', Finset.sum_range_sub']
  ring

/-- Helper for `slowCurveOneTurnAmplitudeDropAsymptotic`: a one-turn angle
window has fourth-power scale mass `(2 * Real.pi / 3) * ε j ^ 2` up to a
cubic error when scale decrements and angle increments have their expected
fourth-order bounds. -/
private theorem fourthPowerSum_error_le_of_oneTurn
    {ε φ : ℕ → ℝ} {j ℓ : ℕ} {D Cφ : ℝ}
    (hD : 0 ≤ D) (hCφ : 0 ≤ Cφ) (hεpos : ∀ t, 0 < ε t)
    (hεanti : Antitone ε) (hjℓ : j ≤ ℓ) (hεjOne : ε j ≤ 1)
    (hangleSmall : Cφ * ε j ^ 2 ≤ 1)
    (hscale : ∀ t ∈ Finset.Ico j ℓ, ε t - ε (t + 1) ≤ D * ε t ^ 4)
    (hangle : ∀ t ∈ Finset.Ico j ℓ,
      |φ (t + 1) - φ t + 3 * ε t ^ 2| ≤ Cφ * ε t ^ 4)
    (hturn : |φ j - φ ℓ - 2 * Real.pi| < ε j ^ 2 / 4) :
    (|(∑ t ∈ Finset.Ico j ℓ, ε t ^ 4) -
          (2 * Real.pi / 3) * ε j ^ 2| ≤
        (50 * D + 1 / 12 + 5 * Cφ / 3) * ε j ^ 3) ∧
      (∑ t ∈ Finset.Ico j ℓ, ε t ^ 4) ≤ 5 * ε j ^ 2 := by
  let S₂ : ℝ := ∑ t ∈ Finset.Ico j ℓ, ε t ^ 2
  let S₄ : ℝ := ∑ t ∈ Finset.Ico j ℓ, ε t ^ 4
  change
    |S₄ - (2 * Real.pi / 3) * ε j ^ 2| ≤
        (50 * D + 1 / 12 + 5 * Cφ / 3) * ε j ^ 3 ∧
      S₄ ≤ 5 * ε j ^ 2
  have hεjPos : 0 < ε j := hεpos j
  have hεjNonneg : 0 ≤ ε j := hεjPos.le
  have hεjSqLeOne : ε j ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hεjNonneg hεjOne 2
  have hS₂Nonneg : 0 ≤ S₂ := by
    dsimp only [S₂]
    exact Finset.sum_nonneg fun t _ ↦ sq_nonneg (ε t)
  have hS₄Nonneg : 0 ≤ S₄ := by
    dsimp only [S₄]
    exact Finset.sum_nonneg fun t _ ↦ pow_nonneg (hεpos t).le 4
  have hscaleLe (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) : ε t ≤ ε j :=
    hεanti (Finset.mem_Ico.mp ht).1
  have hfourthLe (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) :
      ε t ^ 4 ≤ ε j ^ 2 * ε t ^ 2 := by
    have hsquare : ε t ^ 2 ≤ ε j ^ 2 :=
      pow_le_pow_left₀ (hεpos t).le (hscaleLe t ht) 2
    calc
      ε t ^ 4 = ε t ^ 2 * ε t ^ 2 := by ring
      _ ≤ ε j ^ 2 * ε t ^ 2 :=
        mul_le_mul_of_nonneg_right hsquare (sq_nonneg (ε t))
  have hS₄Le : S₄ ≤ ε j ^ 2 * S₂ := by
    calc
      S₄ ≤ ∑ t ∈ Finset.Ico j ℓ, ε j ^ 2 * ε t ^ 2 :=
        Finset.sum_le_sum fun t ht ↦ hfourthLe t ht
      _ = ε j ^ 2 * S₂ := by
        dsimp only [S₂]
        rw [Finset.mul_sum]
  have hangleIdentity :
      φ j - φ ℓ - 3 * S₂ =
        ∑ t ∈ Finset.Ico j ℓ, ((φ t - φ (t + 1)) - 3 * ε t ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    dsimp only [S₂]
    rw [sum_Ico_forwardDifference φ hjℓ]
  have hangleError : |φ j - φ ℓ - 3 * S₂| ≤ Cφ * S₄ := by
    rw [hangleIdentity]
    calc
      |∑ t ∈ Finset.Ico j ℓ, ((φ t - φ (t + 1)) - 3 * ε t ^ 2)| ≤
          ∑ t ∈ Finset.Ico j ℓ, |(φ t - φ (t + 1)) - 3 * ε t ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t ∈ Finset.Ico j ℓ,
          |φ (t + 1) - φ t + 3 * ε t ^ 2| := by
        apply Finset.sum_congr rfl
        intro t ht
        have hterm :
            (φ t - φ (t + 1)) - 3 * ε t ^ 2 =
              -(φ (t + 1) - φ t + 3 * ε t ^ 2) := by
          ring
        rw [hterm, abs_neg]
      _ ≤ ∑ t ∈ Finset.Ico j ℓ, Cφ * ε t ^ 4 :=
        Finset.sum_le_sum fun t ht ↦ hangle t ht
      _ = Cφ * S₄ := by
        dsimp only [S₄]
        rw [Finset.mul_sum]
  have hthreeErrorIdentity :
      3 * S₂ - 2 * Real.pi =
        (φ j - φ ℓ - 2 * Real.pi) - (φ j - φ ℓ - 3 * S₂) := by
    ring
  have hthreeError :
      |3 * S₂ - 2 * Real.pi| ≤ ε j ^ 2 / 4 + Cφ * S₄ := by
    rw [hthreeErrorIdentity]
    exact (abs_sub _ _).trans (add_le_add hturn.le hangleError)
  have hcoefficientS₂ : Cφ * ε j ^ 2 * S₂ ≤ S₂ := by
    calc
      Cφ * ε j ^ 2 * S₂ ≤ 1 * S₂ :=
        mul_le_mul_of_nonneg_right hangleSmall hS₂Nonneg
      _ = S₂ := one_mul S₂
  have hS₂Le : S₂ ≤ 5 := by
    have hupper :
        3 * S₂ - 2 * Real.pi ≤ ε j ^ 2 / 4 + Cφ * ε j ^ 2 * S₂ := by
      calc
        3 * S₂ - 2 * Real.pi ≤ |3 * S₂ - 2 * Real.pi| := le_abs_self _
        _ ≤ ε j ^ 2 / 4 + Cφ * S₄ := hthreeError
        _ ≤ ε j ^ 2 / 4 + Cφ * (ε j ^ 2 * S₂) :=
          add_le_add_right (mul_le_mul_of_nonneg_left hS₄Le hCφ) _
        _ = ε j ^ 2 / 4 + Cφ * ε j ^ 2 * S₂ := by ring
    nlinarith [Real.pi_le_four]
  have hangleMassError :
      |S₂ - 2 * Real.pi / 3| ≤ (1 / 12 + 5 * Cφ / 3) * ε j ^ 2 := by
    have hthirdNonneg : (0 : ℝ) ≤ 1 / 3 := by norm_num
    have hnormalized :
        |S₂ - 2 * Real.pi / 3| = (1 / 3 : ℝ) * |3 * S₂ - 2 * Real.pi| := by
      have hidentity : S₂ - 2 * Real.pi / 3 =
          (1 / 3 : ℝ) * (3 * S₂ - 2 * Real.pi) := by
        ring
      rw [hidentity, abs_mul]
      norm_num
    rw [hnormalized]
    calc
      (1 / 3 : ℝ) * |3 * S₂ - 2 * Real.pi| ≤
          (1 / 3 : ℝ) * (ε j ^ 2 / 4 + Cφ * S₄) :=
        mul_le_mul_of_nonneg_left hthreeError hthirdNonneg
      _ ≤ (1 / 3 : ℝ) * (ε j ^ 2 / 4 + Cφ * (ε j ^ 2 * S₂)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add_right (mul_le_mul_of_nonneg_left hS₄Le hCφ) _)
          hthirdNonneg
      _ ≤ (1 / 12 + 5 * Cφ / 3) * ε j ^ 2 := by
        have hscaled : Cφ * (ε j ^ 2 * S₂) ≤ Cφ * (ε j ^ 2 * 5) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hS₂Le (sq_nonneg (ε j))) hCφ
        nlinarith
  have hscaleWindow (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) :
      ε j - ε t ≤ 5 * D * ε j ^ 2 := by
    have hjt : j ≤ t := (Finset.mem_Ico.mp ht).1
    have hsubset : Finset.Ico j t ⊆ Finset.Ico j ℓ := by
      intro s hs
      have hsBounds := Finset.mem_Ico.mp hs
      exact Finset.mem_Ico.mpr ⟨hsBounds.1, hsBounds.2.trans (Finset.mem_Ico.mp ht).2⟩
    calc
      ε j - ε t = ∑ s ∈ Finset.Ico j t, (ε s - ε (s + 1)) := by
        rw [sum_Ico_forwardDifference ε hjt]
      _ ≤ ∑ s ∈ Finset.Ico j t, D * ε s ^ 4 :=
        Finset.sum_le_sum fun s hs ↦ hscale s (hsubset hs)
      _ ≤ ∑ s ∈ Finset.Ico j ℓ, D * ε s ^ 4 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro s hs hnot
        exact mul_nonneg hD (pow_nonneg (hεpos s).le 4)
      _ = D * S₄ := by
        dsimp only [S₄]
        rw [Finset.mul_sum]
      _ ≤ D * (ε j ^ 2 * S₂) := mul_le_mul_of_nonneg_left hS₄Le hD
      _ ≤ 5 * D * ε j ^ 2 := by
        have hscaled : D * (ε j ^ 2 * S₂) ≤ D * (ε j ^ 2 * 5) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hS₂Le (sq_nonneg (ε j))) hD
        nlinarith
  have hsquareWindow (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) :
      ε j ^ 2 - ε t ^ 2 ≤ 10 * D * ε j ^ 3 := by
    have htle : ε t ≤ ε j := hscaleLe t ht
    have hsumLe : ε j + ε t ≤ 2 * ε j := by linarith
    have hdiffNonneg : 0 ≤ ε j - ε t := sub_nonneg.mpr htle
    have hsumNonneg : 0 ≤ ε j + ε t := add_nonneg hεjNonneg (hεpos t).le
    have hfiveNonneg : (0 : ℝ) ≤ 5 := by norm_num
    calc
      ε j ^ 2 - ε t ^ 2 = (ε j - ε t) * (ε j + ε t) := by ring
      _ ≤ (5 * D * ε j ^ 2) * (2 * ε j) :=
        mul_le_mul (hscaleWindow t ht) hsumLe hsumNonneg
          (mul_nonneg (mul_nonneg hfiveNonneg hD) (sq_nonneg (ε j)))
      _ = 10 * D * ε j ^ 3 := by ring
  have hS₄Difference : ε j ^ 2 * S₂ - S₄ ≤ 50 * D * ε j ^ 3 := by
    have hsumIdentity :
        ε j ^ 2 * S₂ - S₄ =
          ∑ t ∈ Finset.Ico j ℓ, ε t ^ 2 * (ε j ^ 2 - ε t ^ 2) := by
      dsimp only [S₂, S₄]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    rw [hsumIdentity]
    calc
      ∑ t ∈ Finset.Ico j ℓ, ε t ^ 2 * (ε j ^ 2 - ε t ^ 2) ≤
          ∑ t ∈ Finset.Ico j ℓ, ε t ^ 2 * (10 * D * ε j ^ 3) :=
        Finset.sum_le_sum fun t ht ↦
          mul_le_mul_of_nonneg_left (hsquareWindow t ht) (sq_nonneg (ε t))
      _ = (10 * D * ε j ^ 3) * S₂ := by
        dsimp only [S₂]
        rw [← Finset.sum_mul]
        ring
      _ ≤ 50 * D * ε j ^ 3 := by
        have hfactorNonneg : 0 ≤ 10 * D * ε j ^ 3 := by positivity
        nlinarith
  have hS₄Centered : |S₄ - ε j ^ 2 * S₂| ≤ 50 * D * ε j ^ 3 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hS₄Le)]
    nlinarith [hS₄Difference]
  have hcenterIdentity :
      S₄ - (2 * Real.pi / 3) * ε j ^ 2 =
        (S₄ - ε j ^ 2 * S₂) +
          ε j ^ 2 * (S₂ - 2 * Real.pi / 3) := by
    ring
  constructor
  · rw [hcenterIdentity]
    calc
      |(S₄ - ε j ^ 2 * S₂) + ε j ^ 2 * (S₂ - 2 * Real.pi / 3)| ≤
          |S₄ - ε j ^ 2 * S₂| + |ε j ^ 2 * (S₂ - 2 * Real.pi / 3)| :=
        abs_add_le _ _
      _ ≤ 50 * D * ε j ^ 3 +
          ε j ^ 2 * ((1 / 12 + 5 * Cφ / 3) * ε j ^ 2) := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (ε j))]
        exact add_le_add hS₄Centered
          (mul_le_mul_of_nonneg_left hangleMassError (sq_nonneg (ε j)))
      _ ≤ (50 * D + 1 / 12 + 5 * Cφ / 3) * ε j ^ 3 := by
        have hcoefficientNonneg : 0 ≤ 1 / 12 + 5 * Cφ / 3 := by positivity
        have hfourLeThree : ε j ^ 4 ≤ ε j ^ 3 := by
          calc
            ε j ^ 4 = ε j ^ 3 * ε j := by ring
            _ ≤ ε j ^ 3 * 1 :=
              mul_le_mul_of_nonneg_left hεjOne (pow_nonneg hεjNonneg 3)
            _ = ε j ^ 3 := mul_one _
        nlinarith
  · calc
      S₄ ≤ ε j ^ 2 * S₂ := hS₄Le
      _ ≤ ε j ^ 2 * 5 :=
        mul_le_mul_of_nonneg_left hS₂Le (sq_nonneg (ε j))
      _ = 5 * ε j ^ 2 := by ring

/-- Helper for the clean one-turn theorem: summing a uniformly fifth-order
amplitude-ratio remainder across a window whose fourth-power scale mass is
`O(ε j ^ 2)` gives a cubic error in the amplitude drop. -/
private theorem amplitudeDrop_error_le_of_fourthPowerSum
    {ε a : ℕ → ℝ} {j ℓ : ℕ} {A M : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hεpos : ∀ t, 0 < ε t)
    (hεanti : Antitone ε) (haPos : ∀ t, 0 < a t) (haLe : ∀ t, a t ≤ M)
    (hjℓ : j ≤ ℓ) (hεjOne : ε j ≤ 1)
    (hfourthMass : (∑ t ∈ Finset.Ico j ℓ, ε t ^ 4) ≤ 5 * ε j ^ 2)
    (hratio : ∀ t ∈ Finset.Ico j ℓ,
      |a (t + 1) / a t - (1 - (13 / 2 : ℝ) * ε t ^ 4)| ≤ A * ε t ^ 5) :
    |a j - a ℓ -
        (13 / 2 : ℝ) * a j * (∑ t ∈ Finset.Ico j ℓ, ε t ^ 4)| ≤
      (5 * (5 * (13 / 2 : ℝ) * (M * ((13 / 2 : ℝ) + A)) + M * A)) *
        ε j ^ 3 := by
  let c : ℝ := 13 / 2
  let B : ℝ := M * (c + A)
  have hc : 0 ≤ c := by
    dsimp only [c]
    norm_num
  have hB : 0 ≤ B := mul_nonneg hM (add_nonneg hc hA)
  have hεjPos : 0 < ε j := hεpos j
  have hεjNonneg : 0 ≤ ε j := hεjPos.le
  have hscaleLe (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) : ε t ≤ ε j :=
    hεanti (Finset.mem_Ico.mp ht).1
  have hfifthLeFourth (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) :
      ε t ^ 5 ≤ ε t ^ 4 := by
    have htOne : ε t ≤ 1 := (hscaleLe t ht).trans hεjOne
    calc
      ε t ^ 5 = ε t ^ 4 * ε t := by ring
      _ ≤ ε t ^ 4 * 1 :=
        mul_le_mul_of_nonneg_left htOne (pow_nonneg (hεpos t).le 4)
      _ = ε t ^ 4 := mul_one _
  have hfifthLeScaledFourth (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) :
      ε t ^ 5 ≤ ε j * ε t ^ 4 := by
    calc
      ε t ^ 5 = ε t * ε t ^ 4 := by ring
      _ ≤ ε j * ε t ^ 4 :=
        mul_le_mul_of_nonneg_right (hscaleLe t ht) (pow_nonneg (hεpos t).le 4)
  have hdropIdentity (t : ℕ) :
      a t - a (t + 1) =
        a t * (c * ε t ^ 4 -
          (a (t + 1) / a t - (1 - c * ε t ^ 4))) := by
    field_simp [ne_of_gt (haPos t)]
    ring
  have hdropAbs (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) :
      |a t - a (t + 1)| ≤ B * ε t ^ 4 := by
    have hratioPoint :
        |a (t + 1) / a t - (1 - c * ε t ^ 4)| ≤ A * ε t ^ 5 := by
      simpa only [c] using hratio t ht
    have haNonneg : 0 ≤ a t := (haPos t).le
    have hleadingNonneg : 0 ≤ c * ε t ^ 4 :=
      mul_nonneg hc (pow_nonneg (hεpos t).le 4)
    have habsSub :
        |c * ε t ^ 4 - (a (t + 1) / a t - (1 - c * ε t ^ 4))| ≤
          c * ε t ^ 4 + |a (t + 1) / a t - (1 - c * ε t ^ 4)| := by
      calc
        |c * ε t ^ 4 - (a (t + 1) / a t - (1 - c * ε t ^ 4))| ≤
            |c * ε t ^ 4| + |a (t + 1) / a t - (1 - c * ε t ^ 4)| :=
          abs_sub _ _
        _ = c * ε t ^ 4 + |a (t + 1) / a t - (1 - c * ε t ^ 4)| := by
          rw [abs_of_nonneg hleadingNonneg]
    rw [hdropIdentity]
    calc
      |a t * (c * ε t ^ 4 -
          (a (t + 1) / a t - (1 - c * ε t ^ 4)))| =
          a t * |c * ε t ^ 4 -
            (a (t + 1) / a t - (1 - c * ε t ^ 4))| := by
        rw [abs_mul, abs_of_nonneg haNonneg]
      _ ≤ a t * (c * ε t ^ 4 +
          |a (t + 1) / a t - (1 - c * ε t ^ 4)|) :=
        mul_le_mul_of_nonneg_left habsSub haNonneg
      _ ≤ a t * (c * ε t ^ 4 + A * ε t ^ 5) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hratioPoint _) haNonneg
      _ ≤ M * (c * ε t ^ 4 + A * ε t ^ 5) := by
        exact mul_le_mul_of_nonneg_right (haLe t)
          (add_nonneg (mul_nonneg hc (pow_nonneg (hεpos t).le 4))
            (mul_nonneg hA (pow_nonneg (hεpos t).le 5)))
      _ ≤ M * (c * ε t ^ 4 + A * ε t ^ 4) :=
        mul_le_mul_of_nonneg_left
          (add_le_add_right (mul_le_mul_of_nonneg_left (hfifthLeFourth t ht) hA) _)
          hM
      _ = B * ε t ^ 4 := by
        dsimp only [B]
        ring
  have hamplitudeWindow (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) :
      |a t - a j| ≤ 5 * B * ε j ^ 2 := by
    have hjt : j ≤ t := (Finset.mem_Ico.mp ht).1
    have hsubset : Finset.Ico j t ⊆ Finset.Ico j ℓ := by
      intro s hs
      have hsBounds := Finset.mem_Ico.mp hs
      exact Finset.mem_Ico.mpr ⟨hsBounds.1, hsBounds.2.trans (Finset.mem_Ico.mp ht).2⟩
    have htelescope : a j - a t = ∑ s ∈ Finset.Ico j t, (a s - a (s + 1)) := by
      rw [sum_Ico_forwardDifference a hjt]
    rw [abs_sub_comm, htelescope]
    calc
      |∑ s ∈ Finset.Ico j t, (a s - a (s + 1))| ≤
          ∑ s ∈ Finset.Ico j t, |a s - a (s + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ Finset.Ico j t, B * ε s ^ 4 :=
        Finset.sum_le_sum fun s hs ↦ hdropAbs s (hsubset hs)
      _ ≤ ∑ s ∈ Finset.Ico j ℓ, B * ε s ^ 4 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro s hs hnot
        exact mul_nonneg hB (pow_nonneg (hεpos s).le 4)
      _ = B * (∑ s ∈ Finset.Ico j ℓ, ε s ^ 4) := by rw [Finset.mul_sum]
      _ ≤ B * (5 * ε j ^ 2) := mul_le_mul_of_nonneg_left hfourthMass hB
      _ = 5 * B * ε j ^ 2 := by ring
  have hεjSqLe : ε j ^ 2 ≤ ε j := by
    calc
      ε j ^ 2 = ε j * ε j := by ring
      _ ≤ ε j * 1 := mul_le_mul_of_nonneg_left hεjOne hεjNonneg
      _ = ε j := mul_one _
  have htermError (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) :
      |(a t - a (t + 1)) - c * a j * ε t ^ 4| ≤
        (5 * c * B + M * A) * ε j * ε t ^ 4 := by
    let r : ℝ := a (t + 1) / a t - (1 - c * ε t ^ 4)
    have hr : |r| ≤ A * ε t ^ 5 := by
      dsimp only [r]
      simpa only [c] using hratio t ht
    have hidentity :
        (a t - a (t + 1)) - c * a j * ε t ^ 4 =
          c * (a t - a j) * ε t ^ 4 - a t * r := by
      rw [hdropIdentity]
      dsimp only [r]
      ring
    rw [hidentity]
    calc
      |c * (a t - a j) * ε t ^ 4 - a t * r| ≤
          |c * (a t - a j) * ε t ^ 4| + |a t * r| := abs_sub _ _
      _ = c * |a t - a j| * ε t ^ 4 + a t * |r| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc,
          abs_of_nonneg (pow_nonneg (hεpos t).le 4), abs_of_pos (haPos t)]
      _ ≤ c * (5 * B * ε j ^ 2) * ε t ^ 4 + M * (A * ε t ^ 5) :=
        add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hamplitudeWindow t ht) hc)
            (pow_nonneg (hεpos t).le 4))
          (mul_le_mul (haLe t) hr (abs_nonneg r) hM)
      _ ≤ c * (5 * B * ε j) * ε t ^ 4 +
          M * (A * (ε j * ε t ^ 4)) := by
        apply add_le_add
        · have hwindowScale :
              5 * B * ε j ^ 2 ≤ 5 * B * ε j :=
            mul_le_mul_of_nonneg_left hεjSqLe
              (mul_nonneg (by norm_num) hB)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hwindowScale hc)
            (pow_nonneg (hεpos t).le 4)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hfifthLeScaledFourth t ht) hA) hM
      _ = (5 * c * B + M * A) * ε j * ε t ^ 4 := by ring
  have hsumIdentity :
      a j - a ℓ - c * a j * (∑ t ∈ Finset.Ico j ℓ, ε t ^ 4) =
        ∑ t ∈ Finset.Ico j ℓ,
          ((a t - a (t + 1)) - c * a j * ε t ^ 4) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [sum_Ico_forwardDifference a hjℓ]
  rw [hsumIdentity]
  calc
    |∑ t ∈ Finset.Ico j ℓ,
        ((a t - a (t + 1)) - c * a j * ε t ^ 4)| ≤
        ∑ t ∈ Finset.Ico j ℓ,
          |(a t - a (t + 1)) - c * a j * ε t ^ 4| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.Ico j ℓ,
        (5 * c * B + M * A) * ε j * ε t ^ 4 :=
      Finset.sum_le_sum fun t ht ↦ htermError t ht
    _ = ((5 * c * B + M * A) * ε j) *
        (∑ t ∈ Finset.Ico j ℓ, ε t ^ 4) := by
      rw [Finset.mul_sum]
    _ ≤ ((5 * c * B + M * A) * ε j) * (5 * ε j ^ 2) := by
      have hcoefficientNonneg : 0 ≤ (5 * c * B + M * A) * ε j := by positivity
      exact mul_le_mul_of_nonneg_left hfourthMass hcoefficientNonneg
    _ = (5 * (5 * (13 / 2 : ℝ) * (M * ((13 / 2 : ℝ) + A)) + M * A)) *
        ε j ^ 3 := by
      dsimp only [c, B]
      ring

/-- Helper for `slowCurveOneTurnAmplitudeDropAsymptotic`: positive monotone
scales with fourth-order decrement and angle laws, together with a uniformly
fifth-order amplitude-ratio law, have the claimed amplitude drop on every
cofinal one-turn window. -/
private theorem amplitudeDrop_isEquivalent_of_oneTurnBounds
    {ε a φ : ℕ → ℝ} {j ℓ : ℕ → ℕ} {D Cφ A m M : ℝ}
    (hD : 0 ≤ D) (hCφ : 0 ≤ Cφ) (hA : 0 ≤ A) (hm : 0 < m) (hM : 0 ≤ M)
    (hεpos : ∀ t, 0 < ε t) (hεanti : Antitone ε)
    (hεzero : Tendsto ε atTop (𝓝 0))
    (haPos : ∀ t, 0 < a t) (haLower : ∀ t, m ≤ a t) (haLe : ∀ t, a t ≤ M)
    (hscale : ∀ t, ε t - ε (t + 1) ≤ D * ε t ^ 4)
    (hangle : ∀ t, |φ (t + 1) - φ t + 3 * ε t ^ 2| ≤ Cφ * ε t ^ 4)
    (hratio : ∀ t,
      |a (t + 1) / a t - (1 - (13 / 2 : ℝ) * ε t ^ 4)| ≤ A * ε t ^ 5)
    (hj : Tendsto j atTop atTop) (hjℓ : ∀ᶠ n in atTop, j n < ℓ n)
    (hturn : ∀ᶠ n in atTop,
      |φ (j n) - φ (ℓ n) - 2 * Real.pi| < ε (j n) ^ 2 / 4) :
    (fun n ↦ a (j n) - a (ℓ n)) ~[atTop]
      (fun n ↦ (13 * Real.pi / 3) * a (j n) * ε (j n) ^ 2) := by
  let Q₄ : ℝ := 50 * D + 1 / 12 + 5 * Cφ / 3
  let Qₐ : ℝ :=
    5 * (5 * (13 / 2 : ℝ) * (M * ((13 / 2 : ℝ) + A)) + M * A)
  let Q : ℝ := Qₐ + (13 / 2 : ℝ) * M * Q₄
  let K : ℝ := 13 * Real.pi / 3
  have hQ₄ : 0 ≤ Q₄ := by
    dsimp only [Q₄]
    positivity
  have hQₐ : 0 ≤ Qₐ := by
    dsimp only [Qₐ]
    positivity
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hKm : 0 < K * m := mul_pos hK hm
  have hεjZero : Tendsto (fun n ↦ ε (j n)) atTop (𝓝 0) := hεzero.comp hj
  have honePos : (0 : ℝ) < 1 := by norm_num
  have hεjOne : ∀ᶠ n in atTop, ε (j n) ≤ 1 := by
    have hevent : ∀ᶠ n in atTop, ε (j n) < 1 :=
      hεjZero.eventually (Iio_mem_nhds honePos)
    exact hevent.mono fun n hn ↦ hn.le
  have hangleCoefficientZero :
      Tendsto (fun n ↦ Cφ * ε (j n) ^ 2) atTop (𝓝 0) := by
    have hconstant : Tendsto (fun _ : ℕ ↦ Cφ) atTop (𝓝 Cφ) := tendsto_const_nhds
    simpa using hconstant.mul (hεjZero.pow 2)
  have hangleSmall : ∀ᶠ n in atTop, Cφ * ε (j n) ^ 2 ≤ 1 := by
    have hevent : ∀ᶠ n in atTop, Cφ * ε (j n) ^ 2 < 1 :=
      hangleCoefficientZero.eventually (Iio_mem_nhds honePos)
    exact hevent.mono fun n hn ↦ hn.le
  have hpointError : ∀ᶠ n in atTop,
      |(a (j n) - a (ℓ n)) - K * a (j n) * ε (j n) ^ 2| ≤
        Q * ε (j n) ^ 3 := by
    filter_upwards [hjℓ, hturn, hεjOne, hangleSmall] with n hnOrder hnTurn hnOne hnSmall
    have hnLe : j n ≤ ℓ n := hnOrder.le
    have hfourth := fourthPowerSum_error_le_of_oneTurn
      hD hCφ hεpos hεanti hnLe hnOne hnSmall
      (fun t ht ↦ hscale t) (fun t ht ↦ hangle t) hnTurn
    have hamp := amplitudeDrop_error_le_of_fourthPowerSum
      hA hM hεpos hεanti haPos haLe hnLe hnOne hfourth.2
      (fun t ht ↦ hratio t)
    have hdecomposition :
        (a (j n) - a (ℓ n)) - K * a (j n) * ε (j n) ^ 2 =
          ((a (j n) - a (ℓ n)) -
            (13 / 2 : ℝ) * a (j n) *
              (∑ t ∈ Finset.Ico (j n) (ℓ n), ε t ^ 4)) +
            (13 / 2 : ℝ) * a (j n) *
              ((∑ t ∈ Finset.Ico (j n) (ℓ n), ε t ^ 4) -
                (2 * Real.pi / 3) * ε (j n) ^ 2) := by
      dsimp only [K]
      ring
    rw [hdecomposition]
    calc
      |((a (j n) - a (ℓ n)) -
          (13 / 2 : ℝ) * a (j n) *
            (∑ t ∈ Finset.Ico (j n) (ℓ n), ε t ^ 4)) +
          (13 / 2 : ℝ) * a (j n) *
            ((∑ t ∈ Finset.Ico (j n) (ℓ n), ε t ^ 4) -
              (2 * Real.pi / 3) * ε (j n) ^ 2)| ≤
          |(a (j n) - a (ℓ n)) -
            (13 / 2 : ℝ) * a (j n) *
              (∑ t ∈ Finset.Ico (j n) (ℓ n), ε t ^ 4)| +
            |(13 / 2 : ℝ) * a (j n) *
              ((∑ t ∈ Finset.Ico (j n) (ℓ n), ε t ^ 4) -
                (2 * Real.pi / 3) * ε (j n) ^ 2)| := abs_add_le _ _
      _ ≤ Qₐ * ε (j n) ^ 3 +
          (13 / 2 : ℝ) * M * (Q₄ * ε (j n) ^ 3) := by
        have haNonneg : 0 ≤ a (j n) := (haPos (j n)).le
        have hthirteenHalfNonneg : (0 : ℝ) ≤ 13 / 2 := by norm_num
        have hsecond :
            |(13 / 2 : ℝ) * a (j n) *
              ((∑ t ∈ Finset.Ico (j n) (ℓ n), ε t ^ 4) -
                (2 * Real.pi / 3) * ε (j n) ^ 2)| ≤
              (13 / 2 : ℝ) * M * (Q₄ * ε (j n) ^ 3) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hthirteenHalfNonneg,
            abs_of_nonneg haNonneg]
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (haLe (j n)) hthirteenHalfNonneg)
            hfourth.1 (abs_nonneg _)
            (mul_nonneg hthirteenHalfNonneg hM)
        exact add_le_add hamp hsecond
      _ = Q * ε (j n) ^ 3 := by
        dsimp only [Q]
        ring
  let C : ℝ := Q / (K * m)
  have hC : 0 ≤ C := div_nonneg hQ hKm.le
  have hratioError : ∀ᶠ n in atTop,
      |(a (j n) - a (ℓ n)) /
          (K * a (j n) * ε (j n) ^ 2) - 1| ≤ C * ε (j n) := by
    filter_upwards [hpointError] with n hnError
    have hεPos : 0 < ε (j n) := hεpos (j n)
    have hdenPos : 0 < K * a (j n) * ε (j n) ^ 2 :=
      mul_pos (mul_pos hK (haPos (j n))) (pow_pos hεPos 2)
    have hdenLower :
        K * m * ε (j n) ^ 2 ≤ K * a (j n) * ε (j n) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (haLower (j n)) hK.le) (sq_nonneg (ε (j n)))
    have hratioIdentity :
        (a (j n) - a (ℓ n)) /
            (K * a (j n) * ε (j n) ^ 2) - 1 =
          ((a (j n) - a (ℓ n)) - K * a (j n) * ε (j n) ^ 2) /
            (K * a (j n) * ε (j n) ^ 2) := by
      exact div_sub_one (ne_of_gt hdenPos)
    rw [hratioIdentity, abs_div, abs_of_pos hdenPos]
    apply (div_le_iff₀ hdenPos).2
    calc
      |(a (j n) - a (ℓ n)) - K * a (j n) * ε (j n) ^ 2| ≤
          Q * ε (j n) ^ 3 := hnError
      _ = (C * ε (j n)) * (K * m * ε (j n) ^ 2) := by
        dsimp only [C]
        field_simp [ne_of_gt hKm]
      _ ≤ (C * ε (j n)) * (K * a (j n) * ε (j n) ^ 2) :=
        mul_le_mul_of_nonneg_left hdenLower (mul_nonneg hC hεPos.le)
  have hboundZero : Tendsto (fun n ↦ C * ε (j n)) atTop (𝓝 0) := by
    have hconstant : Tendsto (fun _ : ℕ ↦ C) atTop (𝓝 C) := tendsto_const_nhds
    simpa only [mul_zero] using hconstant.mul hεjZero
  have hratioDistZero : Tendsto
      (fun n ↦ dist
        ((a (j n) - a (ℓ n)) / (K * a (j n) * ε (j n) ^ 2)) 1)
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ dist_nonneg
    · filter_upwards [hratioError] with n hn
      simpa only [Real.dist_eq, sub_zero] using hn
    · exact hboundZero
  have hratioTendsto : Tendsto
      (fun n ↦ (a (j n) - a (ℓ n)) / (K * a (j n) * ε (j n) ^ 2))
      atTop (𝓝 1) := tendsto_iff_dist_tendsto_zero.mpr hratioDistZero
  simpa only [K] using Asymptotics.isEquivalent_of_tendsto_one hratioTendsto

/-- Along a sufficiently small invariant slow-curve orbit, the amplitude drop
between cofinal iterates separated by one full frame turn is asymptotic to
`13 * Real.pi / 3` times the amplitude at the first iterate and the square of
its scale. -/
theorem slowCurveOneTurnAmplitudeDropAsymptotic (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ j ℓ : ℕ → ℕ, Tendsto j atTop atTop →
        (∀ᶠ n in atTop, j n < ℓ n) →
        (∀ᶠ n in atTop,
          |orbit.frameAngle (j n) - orbit.frameAngle (ℓ n) - 2 * Real.pi| <
            (orbit.state (j n)).ε ^ 2 / 4) →
        (fun n ↦
          (orbit.state (j n)).amplitude - (orbit.state (ℓ n)).amplitude) ~[atTop]
        (fun n ↦
          (13 * Real.pi / 3) * (orbit.state (j n)).amplitude *
              (orbit.state (j n)).ε ^ 2) := by
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηNext, hηNext, hNext⟩ :=
    DFP.TwoLeg.slowCurveNextPosLt p h h_pJet h_hJet
  obtain ⟨ηRec, hηRec, Cε, hCε, hRec⟩ :=
    DFP.TwoLeg.slowGraphSignedRecurrenceBound p h h_pJet h_hJet
  obtain ⟨ηScale, hηScale, hScale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  obtain ⟨ηFrame, hηFrame, Cφ, hCφ, hFrame⟩ :=
    slowCurveFrameRotation p h h_invariant h_pJet h_hJet
  obtain ⟨ηAmp, hηAmp, Gmin, hGmin, Gmax, hGminMax, hAmpBounds⟩ :=
    slowCurveAmplitudeUniformBounds p h h_invariant h_pJet h_hJet
  have hAmplitudeExpansion :
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).amplitudeRatio -
          (1 - (13 / 2) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    let graph := DFP.TwoLeg.SlowGraph.ofAsymptotics p h h_pJet h_hJet
    simpa only [graph, DFP.TwoLeg.SlowGraph.path_apply,
      DFP.TwoLeg.SlowGraph.ofAsymptotics_shape,
      DFP.TwoLeg.SlowGraph.ofAsymptotics_high] using
      graph.amplitudeRatio_sub_quartic_isBigO
  obtain ⟨A, hA, δA, hδA, hAmplitudeLocal⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_pos_natPow_bound_of_isBigO
      hAmplitudeExpansion
  let εbar : ℝ := min ηGraph
    (min ηNext
      (min (ηRec / 2)
        (min ηScale
          (min ηFrame
            (min ηAmp (min (δA / 2) 1))))))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    have honePos : (0 : ℝ) < 1 := by norm_num
    exact lt_min hηGraph.1
      (lt_min hηNext
        (lt_min (half_pos hηRec)
          (lt_min hηScale
            (lt_min hηFrame.1
              (lt_min hηAmp.1 (lt_min (half_pos hδA) honePos))))))
  have hbarGraph : εbar ≤ ηGraph := by
    dsimp only [εbar]
    exact min_le_left _ _
  have hbarNext : εbar ≤ ηNext := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hbarRecHalf : εbar ≤ ηRec / 2 := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hbarScale : εbar ≤ ηScale := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbarFrame : εbar ≤ ηFrame := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hbarAmp : εbar ≤ ηAmp := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hbarDeltaHalf : εbar ≤ δA / 2 := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans (min_le_left _ _))))))
  have hbarOne : εbar ≤ 1 := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans (min_le_right _ _))))))
  refine ⟨εbar, hεbarPos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro j ℓ hj hjℓ hturn
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  let ε : ℕ → ℝ := fun t ↦ (orbit.state t).ε
  let a : ℕ → ℝ := fun t ↦ (orbit.state t).amplitude
  let φ : ℕ → ℝ := fun t ↦ orbit.frameAngle t
  let D : ℝ := (3 / 2 : ℝ) + 5 / 4 + Cε
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans hbarGraph⟩
  have hε₀Next : ε₀ ∈ Set.Ioc 0 ηNext :=
    ⟨hε₀.1, hε₀.2.trans hbarNext⟩
  have hε₀Scale : ε₀ ∈ Set.Ioc 0 ηScale :=
    ⟨hε₀.1, hε₀.2.trans hbarScale⟩
  have hε₀Frame : ε₀ ∈ Set.Ioc 0 ηFrame :=
    ⟨hε₀.1, hε₀.2.trans hbarFrame⟩
  have hε₀Amp : ε₀ ∈ Set.Ioc 0 ηAmp :=
    ⟨hε₀.1, hε₀.2.trans hbarAmp⟩
  have hεbarRec : εbar ∈ Set.Ioc 0 ηRec := by
    constructor
    · exact hεbarPos
    · exact hbarRecHalf.trans (half_le_self hηRec.le)
  have hεeq (t : ℕ) :
      ε t = (DFP.TwoLeg.stateMap^[t] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ t
    have hcoordinates' :
        (orbit.state t).coordinates =
          DFP.TwoLeg.stateMap^[t] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hcoordinates
    dsimp only [ε]
    have hfirst := congrArg Prod.fst hcoordinates'
    rw [State.coordinates_def] at hfirst
    exact hfirst
  have hforward (t : ℕ) := hGraph ε₀ hε₀Graph t
  have hεpos (t : ℕ) : 0 < ε t := by
    rw [hεeq t]
    exact hforward t |>.2.1
  have hεleInitial (t : ℕ) : ε t ≤ ε₀ := by
    rw [hεeq t]
    exact hforward t |>.2.2
  have hεleBar (t : ℕ) : ε t ≤ εbar :=
    (hεleInitial t).trans hε₀.2
  have hgraphCoordinates (t : ℕ) :
      (orbit.state t).coordinates = (ε t, p (ε t), h (ε t)) := by
    have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ t
    calc
      (orbit.state t).coordinates =
          DFP.TwoLeg.stateMap^[t] (ε₀, p ε₀, h ε₀) := by
        simpa only [orbit] using hcoordinates
      _ = ((DFP.TwoLeg.stateMap^[t] (ε₀, p ε₀, h ε₀)).1,
          p (DFP.TwoLeg.stateMap^[t] (ε₀, p ε₀, h ε₀)).1,
          h (DFP.TwoLeg.stateMap^[t] (ε₀, p ε₀, h ε₀)).1) := hforward t |>.1
      _ = (ε t, p (ε t), h (ε t)) := by rw [hεeq t]
  have hscaleStep (t : ℕ) :
      ε (t + 1) = DFP.TwoLeg.signedEpsilon (ε t) (p (ε t)) (h (ε t)) := by
    have hiterate := Function.iterate_succ_apply'
      DFP.TwoLeg.stateMap t (ε₀, p ε₀, h ε₀)
    have hgraph := hforward t |>.1
    rw [hεeq (t + 1), hiterate, hgraph, ← hεeq t]
    simp only [DFP.TwoLeg.stateMap, DFP.TwoLeg.signedEpsilon]
  have hεstepLt (t : ℕ) : ε (t + 1) < ε t := by
    have htNext : ε t ∈ Set.Ioc 0 ηNext :=
      ⟨hεpos t, (hεleBar t).trans hbarNext⟩
    rw [hscaleStep t]
    exact (hNext (ε t) htNext).2
  have hεanti : Antitone ε :=
    antitone_nat_of_succ_le fun t ↦ (hεstepLt t).le
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    have hNineHalfPos : (0 : ℝ) < 9 / 2 := by norm_num
    have hbase : Tendsto (fun t : ℕ ↦ (9 / 2 : ℝ) * (t : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hNineHalfPos
    have hreference : Tendsto
        (fun t : ℕ ↦ ((9 / 2 : ℝ) * (t : ℝ)) ^ (-(1 : ℝ) / 3))
        atTop (𝓝 0) := by
      have hOneThirdPos : (0 : ℝ) < 1 / 3 := by norm_num
      have hpower := (tendsto_rpow_neg_atTop hOneThirdPos).comp hbase
      convert hpower using 1
      funext t
      dsimp only [Function.comp_apply]
      congr 1
      ring
    have hstateZero : Tendsto
        (fun t : ℕ ↦ (DFP.TwoLeg.stateMap^[t] (ε₀, p ε₀, h ε₀)).1)
        atTop (𝓝 0) :=
      (hScale ε₀ hε₀Scale).symm.tendsto_nhds hreference
    exact hstateZero.congr' (Eventually.of_forall fun t ↦ (hεeq t).symm)
  have hresidual (t : ℕ) :
      |ε (t + 1) - ε t + (3 / 2 : ℝ) * ε t ^ 4 -
          (5 / 4 : ℝ) * ε t ^ 5| ≤ Cε * ε t ^ 6 := by
    have hpoint := hRec εbar hεbarRec (ε t) ⟨hεpos t, hεleBar t⟩
    rw [hscaleStep t]
    exact hpoint
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hscaleDecrement (t : ℕ) : ε t - ε (t + 1) ≤ D * ε t ^ 4 := by
    have hbound := (abs_le.mp (hresidual t)).1
    have hεOne : ε t ≤ 1 := (hεleBar t).trans hbarOne
    have hsixthLe : ε t ^ 6 ≤ ε t ^ 4 := by
      have hεSquareOne : ε t ^ 2 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ (hεpos t).le hεOne 2
      calc
        ε t ^ 6 = ε t ^ 4 * ε t ^ 2 := by ring
        _ ≤ ε t ^ 4 * 1 :=
          mul_le_mul_of_nonneg_left hεSquareOne (pow_nonneg (hεpos t).le 4)
        _ = ε t ^ 4 := mul_one _
    have hCscaled := mul_le_mul_of_nonneg_left hsixthLe hCε.le
    have hraw :
        ε t - ε (t + 1) ≤
          (3 / 2 : ℝ) * ε t ^ 4 - (5 / 4 : ℝ) * ε t ^ 5 + Cε * ε t ^ 6 := by
      linarith
    dsimp only [D]
    calc
      ε t - ε (t + 1) ≤
          (3 / 2 : ℝ) * ε t ^ 4 - (5 / 4 : ℝ) * ε t ^ 5 + Cε * ε t ^ 6 := hraw
      _ ≤ (3 / 2 : ℝ) * ε t ^ 4 + Cε * ε t ^ 6 := by
        have hfiveFourNonneg : 0 ≤ (5 / 4 : ℝ) := by norm_num
        have hfifthNonneg : 0 ≤ (5 / 4 : ℝ) * ε t ^ 5 :=
          mul_nonneg hfiveFourNonneg (pow_nonneg (hεpos t).le 5)
        linarith
      _ ≤ (3 / 2 : ℝ) * ε t ^ 4 + Cε * ε t ^ 4 :=
        add_le_add_right hCscaled _
      _ ≤ ((3 / 2 : ℝ) + 5 / 4 + Cε) * ε t ^ 4 := by
        have hfourthNonneg : 0 ≤ ε t ^ 4 := pow_nonneg (hεpos t).le 4
        nlinarith
  have hframeBound (t : ℕ) :
      |φ (t + 1) - φ t + 3 * ε t ^ 2| ≤ Cφ * ε t ^ 4 := by
    simpa only [φ, ε, orbit] using hFrame ε₀ hε₀Frame t
  have hbarDelta : εbar < δA :=
    hbarDeltaHalf.trans_lt (half_lt_self hδA)
  have hamplitudeRemainder (t : ℕ) :
      |(DFP.TwoLeg.observableMap (ε t, p (ε t), h (ε t))).amplitudeRatio -
          (1 - (13 / 2 : ℝ) * ε t ^ 4)| ≤ A * ε t ^ 5 := by
    have hεDelta : |ε t| < δA := by
      rw [abs_of_pos (hεpos t)]
      exact (hεleBar t).trans_lt hbarDelta
    have hpoint := hAmplitudeLocal (ε t) hεDelta
    simpa only [Real.norm_eq_abs, abs_of_pos (hεpos t)] using hpoint
  obtain ⟨Glim, hGlim, hGlimTendsto, hAmplitudeBounds⟩ :=
    hAmpBounds ε₀ hε₀Amp
  have hGmaxNonneg : 0 ≤ Gmax := hGmin.le.trans hGminMax
  have haLower (t : ℕ) : Gmin ≤ a t := by
    exact hAmplitudeBounds t |>.1
  have haLe (t : ℕ) : a t ≤ Gmax := by
    exact hAmplitudeBounds t |>.2
  have haPos (t : ℕ) : 0 < a t := hGmin.trans_le (haLower t)
  have hratioBound (t : ℕ) :
      |a (t + 1) / a t - (1 - (13 / 2 : ℝ) * ε t ^ 4)| ≤ A * ε t ^ 5 := by
    have hsuccessor := DFP.TwoPhaseOrbit.ofSlowCurve_succ p h ε₀ t
    have hstateRatio := State.nextAmplitudeRatio (orbit.state t) (ne_of_gt (haPos t))
    calc
      |a (t + 1) / a t - (1 - (13 / 2 : ℝ) * ε t ^ 4)| =
          |(orbit.state t).next.amplitude / (orbit.state t).amplitude -
            (1 - (13 / 2 : ℝ) * ε t ^ 4)| := by
        rw [← hsuccessor]
      _ = |(DFP.TwoLeg.observableMap (ε t, p (ε t), h (ε t))).amplitudeRatio -
            (1 - (13 / 2 : ℝ) * ε t ^ 4)| := by
        rw [hstateRatio, hgraphCoordinates t]
      _ ≤ A * ε t ^ 5 := hamplitudeRemainder t
  have hmain := amplitudeDrop_isEquivalent_of_oneTurnBounds
    hD hCφ.le hA.le hGmin hGmaxNonneg hεpos hεanti hεzero
    haPos haLower haLe hscaleDecrement hframeBound hratioBound hj hjℓ hturn
  simpa only [a, ε, φ, orbit] using hmain

end DFP.TwoPhaseOrbit

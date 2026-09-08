module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

public section

namespace DFP.TwoPhaseOrbit

/-!
# Positive angular-gap adapters

These scalar lemmas isolate the final arithmetic step in the consecutive endpoint
angle argument.  They are deliberately independent of the orbit construction: a
clean endpoint-angle remainder modulus and a cubic polar-gradient correction can
instantiate them without unfolding either construction.
-/

/-- Helper for Lemma 4.11: a cubic correction is quadratic-small when its scale is
bounded by a fixed radius and its coefficient is bounded by the quadratic modulus. -/
theorem cubicCorrectionBound
    (e η ρ K c : ℝ)
    (hη : e ≤ η) (hK : 0 ≤ K)
    (hKη : K * η ≤ ρ)
    (hc : |c| ≤ K * e ^ 3) :
    |c| ≤ ρ * e ^ 2 := by
  have hKe : K * e ≤ K * η :=
    mul_le_mul_of_nonneg_left hη hK
  have he2 : 0 ≤ e ^ 2 := sq_nonneg e
  calc
    |c| ≤ K * e ^ 3 := hc
    _ = (K * e) * e ^ 2 := by ring
    _ ≤ (K * η) * e ^ 2 :=
      mul_le_mul_of_nonneg_right hKe he2
    _ ≤ ρ * e ^ 2 :=
      mul_le_mul_of_nonneg_right hKη he2

/-- Helper for Lemma 4.11: two quadratic error bounds around a signed leading
term give matching lower and upper bounds for the corrected gap. -/
theorem quadraticGapBounds
    (lead e ρ a c : ℝ)
    (hrem : |a + lead * e ^ 2| ≤ ρ * e ^ 2)
    (hc : |c| ≤ ρ * e ^ 2) :
    (lead - 2 * ρ) * e ^ 2 ≤ -a + c ∧
      -a + c ≤ (lead + 2 * ρ) * e ^ 2 := by
  have hrem' := abs_le.mp hrem
  have hc' := abs_le.mp hc
  constructor
  · nlinarith [hrem'.2, hc'.1]
  · nlinarith [hrem'.1, hc'.2]

/-- Helper for Lemma 4.11: combine a clean quadratic remainder with a cubic
polar-gradient correction into a two-sided gap estimate. -/
theorem quadraticGapBoundsFromCubic
    (lead e η ρ K a c : ℝ)
    (hη : e ≤ η) (hK : 0 ≤ K)
    (hKη : K * η ≤ ρ)
    (hrem : |a + lead * e ^ 2| ≤ ρ * e ^ 2)
    (hc : |c| ≤ K * e ^ 3) :
    (lead - 2 * ρ) * e ^ 2 ≤ -a + c ∧
      -a + c ≤ (lead + 2 * ρ) * e ^ 2 := by
  have hcQuadratic := cubicCorrectionBound e η ρ K c hη hK hKη hc
  exact quadraticGapBounds lead e ρ a c hrem hcQuadratic

/-- Helper for Lemma 4.11: the first-phase leading coefficient `2` yields a
positive corrected gap whenever the common quadratic error modulus is below `1`. -/
theorem firstPhaseGapLowerBound
    (e η ρ K a c : ℝ)
    (he : 0 < e) (hη : e ≤ η) (hK : 0 ≤ K)
    (hKη : K * η ≤ ρ) (hρ : ρ < 1)
    (hrem : |a + 2 * e ^ 2| ≤ ρ * e ^ 2)
    (hc : |c| ≤ K * e ^ 3) :
    (2 - 2 * ρ) * e ^ 2 ≤ -a + c ∧ 0 < -a + c := by
  have hbounds := quadraticGapBoundsFromCubic 2 e η ρ K a c
    hη hK hKη hrem hc
  have hcoef : 0 < 2 - 2 * ρ := by
    linarith
  have hpositive : 0 < (2 - 2 * ρ) * e ^ 2 :=
    mul_pos hcoef (sq_pos_of_pos he)
  exact ⟨hbounds.1, hpositive.trans_le hbounds.1⟩

/-- Helper for Lemma 4.11: the second-phase leading coefficient `1` yields a
positive corrected gap whenever the common quadratic error modulus is below `1/2`. -/
theorem secondPhaseGapLowerBound
    (e η ρ K a c : ℝ)
    (he : 0 < e) (hη : e ≤ η) (hK : 0 ≤ K)
    (hKη : K * η ≤ ρ) (hρ : ρ < 1 / 2)
    (hrem : |a + e ^ 2| ≤ ρ * e ^ 2)
    (hc : |c| ≤ K * e ^ 3) :
    (1 - 2 * ρ) * e ^ 2 ≤ -a + c ∧ 0 < -a + c := by
  have hrem' : |a + 1 * e ^ 2| ≤ ρ * e ^ 2 := by
    simpa only [one_mul] using hrem
  have hbounds := quadraticGapBoundsFromCubic 1 e η ρ K a c
    hη hK hKη hrem' hc
  have hcoef : 0 < 1 - 2 * ρ := by
    linarith
  have hpositive : 0 < (1 - 2 * ρ) * e ^ 2 :=
    mul_pos hcoef (sq_pos_of_pos he)
  exact ⟨hbounds.1, hpositive.trans_le hbounds.1⟩

end DFP.TwoPhaseOrbit

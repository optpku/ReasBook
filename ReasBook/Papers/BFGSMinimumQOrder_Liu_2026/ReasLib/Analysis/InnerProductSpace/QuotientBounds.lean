module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quotient bounds in real inner product spaces

The estimate below combines Cauchy--Schwarz with scale-dependent upper and
lower bounds.  It is independent of the source of the vectors and scalar
quantity.
-/

public section

/-- A cubic vector bound, a quadratic-scale step bound, and a fourth-order
positive denominator bound control the corresponding inner-product quotient
linearly in the scale. -/
theorem abs_inner_div_le_scale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (correction s : E) (ε r q Kcorrection CStep cQ : ℝ)
    (hε : 0 < ε) (hKcorrection : 0 < Kcorrection)
    (hCStep : 0 < CStep) (hcQ : 0 < cQ)
    (hr : r = ε ^ 2)
    (hcorrection : ‖correction‖ ≤ Kcorrection * ε ^ 3)
    (hstep : ‖s‖ ≤ CStep * r)
    (hq : cQ * r ^ 2 ≤ q) :
    |inner ℝ correction s / q| ≤
      (Kcorrection * CStep / cQ) * ε := by
  have hcorrectionNonneg : 0 ≤ Kcorrection * ε ^ 3 :=
    mul_nonneg hKcorrection.le (pow_nonneg hε.le 3)
  have hnum : |inner ℝ correction s| ≤
      Kcorrection * CStep * ε ^ 5 := by
    calc
      |inner ℝ correction s| ≤ ‖correction‖ * ‖s‖ :=
        abs_real_inner_le_norm correction s
      _ ≤ (Kcorrection * ε ^ 3) * (CStep * r) :=
        mul_le_mul hcorrection hstep (norm_nonneg s) hcorrectionNonneg
      _ = Kcorrection * CStep * ε ^ 5 := by rw [hr]; ring
  have hqLower : cQ * ε ^ 4 ≤ q := by
    calc
      cQ * ε ^ 4 = cQ * r ^ 2 := by rw [hr]; ring
      _ ≤ q := hq
  have hqPos : 0 < q := by
    have hLowerPos : 0 < cQ * ε ^ 4 := mul_pos hcQ (pow_pos hε 4)
    exact hLowerPos.trans_le hqLower
  rw [abs_div, abs_of_pos hqPos, div_le_iff₀ hqPos]
  calc
    |inner ℝ correction s| ≤ Kcorrection * CStep * ε ^ 5 := hnum
    _ = (Kcorrection * CStep / cQ) * ε * (cQ * ε ^ 4) := by
      field_simp
    _ ≤ (Kcorrection * CStep / cQ) * ε * q :=
      mul_le_mul_of_nonneg_left hqLower
        (mul_nonneg
          (div_nonneg (mul_nonneg hKcorrection.le hCStep.le) hcQ.le) hε.le)

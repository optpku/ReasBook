module

public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

public section

namespace Metric

/-- A lower bound for the gap between two approximate radii is bounded by the
distance between the points together with the two radius errors. -/
theorem radiusGap_le_dist_add_errors
    {E : Type*} [SeminormedAddCommGroup E]
    (x y center : E) (radiusX radiusY errorX errorY gap : ℝ)
    (hx : |‖x - center‖ - radiusX| ≤ errorX)
    (hy : |‖y - center‖ - radiusY| ≤ errorY)
    (hgap : gap ≤ radiusX - radiusY) :
    gap ≤ dist x y + errorX + errorY := by
  have hxLower := (abs_le.mp hx).1
  have hyUpper := (abs_le.mp hy).2
  have hnorm : |‖x - center‖ - ‖y - center‖| ≤ dist x y := by
    calc
      |‖x - center‖ - ‖y - center‖| ≤
          ‖(x - center) - (y - center)‖ := abs_norm_sub_norm_le _ _
      _ = ‖x - y‖ := by
        congr 1
        abel
      _ = dist x y := by rw [dist_eq_norm]
  linarith [le_abs_self (‖x - center‖ - ‖y - center‖)]

end Metric

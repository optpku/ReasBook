module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_2_definition_1_33

public section

namespace PureIntegerSlope
namespace Problem

/-- Helper for `ch1_sec1_4_2_proposition_1_14`: `boundaryPoint` is the coordinatewise real lift
of `boundaryLatticePoint`. -/
lemma boundaryPoint_eq_realLift_boundaryLatticePoint
    (E : Problem) :
    E.boundaryPoint =
      ((E.boundaryLatticePoint.1 : ℝ), (E.boundaryLatticePoint.2 : ℝ)) := by
  -- Unfold the distinguished endpoint to expose the coordinatewise real lift.
  rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_proposition_1_14.lean.
Proposition 1.14. In the Definition 1.33 setting, the endpoint of the
positive-slope boundary segment of `convexHull ℝ (PureIntegerSlope.realLatticeSet E.a₁ E.a₂ E.u)`
emanating from the origin is `((E.k * E.xStar.1 : ℝ), (E.k * E.xStar.2 : ℝ))`. -/
theorem positiveSlopeEndpoint_eq
    (E : Problem) :
    E.boundaryPoint =
      ((E.k * E.xStar.1 : ℝ), (E.k * E.xStar.2 : ℝ)) := by
  -- First rewrite the endpoint as the real lift of the lattice boundary point.
  rw [boundaryPoint_eq_realLift_boundaryLatticePoint]
  -- Then unfold the lattice endpoint and normalize each casted integer product.
  simp only [boundaryLatticePoint, Int.cast_mul]

end Problem
end PureIntegerSlope

end

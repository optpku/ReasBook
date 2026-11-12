/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_4.ch1_sec1_4_2_definition_1_33.Problem

public section

/- Definition 1.33. The two-dimensional pure-integer slope-maximization setup is formalized by
the explicit standing context `PureIntegerSlope.Problem`, together with the source-facing sets
`PureIntegerSlope.polyhedron` and `PureIntegerSlope.realLatticeSet` and the derived boundary data
`PureIntegerSlope.Problem.boundaryLatticePoint` and
`PureIntegerSlope.Problem.positiveSlopeEndpoint`. -/
#check PureIntegerSlope.Problem
#check PureIntegerSlope.polyhedron
#check PureIntegerSlope.realLatticeSet
#check PureIntegerSlope.Problem.boundaryLatticePoint
#check PureIntegerSlope.Problem.positiveSlopeEndpoint

end

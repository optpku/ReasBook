/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_17.TotalVariation

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}
variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

namespace BV

/-- Helper for Theorem 8.17: the source-facing total-variation functional `BV.totalVariation` is
convex on the whole bounded-variation space `BV(Ω)`. -/
theorem totalVariation_convexOn :
    ConvexOn ℝ Set.univ (BV.totalVariation : BV Ω → ℝ) := by
  exact (BV.tvSeminorm.convexOn : ConvexOn ℝ Set.univ (BV.tvSeminorm : BV Ω → ℝ)).congr
    (by
      intro u _
      exact BV.tvSeminorm_apply u)

/-- Helper for Theorem 8.17: the source-facing total-variation functional `BV.totalVariation` is
not strictly convex on a nontrivial bounded-variation space `BV(Ω)`. -/
theorem totalVariation_notStrictConvexOn [Nontrivial (BV Ω)] :
    ¬ StrictConvexOn ℝ Set.univ (BV.totalVariation : BV Ω → ℝ) := by
  intro hstrict
  exact (BV.tvSeminorm_notStrictConvexOn :
      ¬ StrictConvexOn ℝ Set.univ (BV.tvSeminorm : BV Ω → ℝ)) <|
    hstrict.congr (by
      intro u _
      exact (BV.tvSeminorm_apply u).symm)

end BV

/-- Theorem 8.17 (1). The total-variation functional on `BV(Ω)`, formalized by
`BV.totalVariation`, is convex on the whole space `BV(Ω)`. -/
theorem bvTotalVariationConvexOn :
    ConvexOn ℝ Set.univ (BV.totalVariation : BV Ω → ℝ) := by
  exact BV.totalVariation_convexOn

/-- Theorem 8.17 (2). The total-variation functional on `BV(Ω)`, formalized by
`BV.totalVariation`, is not strictly convex on the whole space `BV(Ω)`. -/
theorem bvTotalVariationNotStrictConvexOn [Nontrivial (BV Ω)] :
    ¬ StrictConvexOn ℝ Set.univ (BV.totalVariation : BV Ω → ℝ) := by
  exact BV.totalVariation_notStrictConvexOn

/-- Theorem 8.17 (3). On a nontrivial source-facing Sobolev space `W¹,¹(Ω)`, the restriction of
the Chapter 8 total-variation functional is not strictly convex: by Proposition 8.13 it is
absolutely homogeneous and therefore affine on every ray through `0`. -/
theorem w11TotalVariationNotStrictConvexOn [Nontrivial (W¹,¹(Ω))] :
    ¬ StrictConvexOn ℝ Set.univ (W11.totalVariation : W¹,¹(Ω) → ℝ) := by
  exact W11.totalVariation_notStrictConvexOn

/-
Verified anchors for Theorem 8.17 and its companion API.
-/
#check BV.totalVariation_convexOn

#check BV.totalVariation_notStrictConvexOn

#check VariationalRegularization.bvTotalVariationConvexOn

#check VariationalRegularization.bvTotalVariationNotStrictConvexOn

#check W11.integralNormWeakGradient

#check W11.totalVariation

#check W11.totalVariation_def

#check W11.totalVariation_eq_integralNormWeakGradient

#check W11.totalVariation_smul

#check W11.totalVariation_zero

#check W11.totalVariation_notStrictConvexOn

#check VariationalRegularization.w11TotalVariationNotStrictConvexOn

#check totalVariation_toReal_eq_integral_norm_of_weakGradient

end VariationalRegularization

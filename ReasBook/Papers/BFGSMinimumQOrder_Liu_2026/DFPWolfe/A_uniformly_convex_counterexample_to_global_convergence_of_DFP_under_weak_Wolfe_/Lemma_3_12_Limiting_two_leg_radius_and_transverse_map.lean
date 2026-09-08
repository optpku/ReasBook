module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map

public section

/- Lemma 3.12 (Limiting two-leg radius and transverse map) (1): at `ε = 0`,
the removable two-leg radius factor has the stated rational value. -/
#check (DFP.TwoLeg.radiusFactor_zero :
  ∀ (p h : ℝ), 0 < p → 0 < h →
    DFP.TwoLeg.radiusFactor 0 p h =
      9 * h * p * (p + 1) / (2 * (9 * h * p + (p + 1) ^ 2)))

/- Lemma 3.12 (Limiting two-leg radius and transverse map) (2): at `ε = 0`,
the transverse coordinates of the extended two-leg map have the stated values. -/
#check (DFP.TwoLeg.stateMap_zero_transverse :
  ∀ (p h : ℝ), 0 < p → 0 < h →
    (DFP.TwoLeg.extendedMap (0, p, h)).2 =
      (4 * (9 * h * p + (p + 1) ^ 2) ^ 2 / (81 * h * p * (p + 1) ^ 2), 1))

/- Lemma 3.12 (Limiting two-leg radius and transverse map) (3): at `(p, h) = (2, 1)`,
the radius factor is one. -/
#check (DFP.TwoLeg.radiusFactor_base : DFP.TwoLeg.radiusFactor 0 2 1 = 1)

/- Lemma 3.12 (Limiting two-leg radius and transverse map) (4): the extended map
fixes `(0, 2, 1)`. -/
#check (DFP.TwoLeg.stateMap_base :
  DFP.TwoLeg.extendedMap ((0, 2, 1) : ℝ × ℝ × ℝ) = (0, 2, 1))

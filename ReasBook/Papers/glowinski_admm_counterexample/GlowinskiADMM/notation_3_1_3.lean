module

public import glowinski_admm_counterexample.GlowinskiADMM.notation_3_1_3_Normalization

@[expose] public section

/-
Notation 3.1.3: the reduced KKT normalization, scaled recurrence, generated graph
normals, and support bounds are exposed by the following canonical declarations.
-/
#check ERealConvex.centerAt
#check ERealConvex.reflectedCenterAt
#check ADMM.Scaled.residual
#check ADMM.Scaled.firstNormal
#check ADMM.Scaled.secondNormal
#check ADMM.Scaled.firstMargin
#check ADMM.Scaled.secondMargin
#check ADMM.KKTNormalization.firstObjective
#check ADMM.KKTNormalization.secondObjective
#check ADMM.KKTNormalization.q
#check ADMM.KKTNormalization.eta
#check ADMM.KKTNormalization.w
#check ADMM.KKTNormalization.firstObjective_zero
#check ADMM.KKTNormalization.secondObjective_zero
#check ADMM.KKTNormalization.firstObjective_nonneg
#check ADMM.KKTNormalization.secondObjective_nonneg
#check ADMM.KKTNormalization.firstObjective_isClosedProperConvex
#check ADMM.KKTNormalization.secondObjective_isClosedProperConvex
#check ADMM.KKTNormalization.firstProx
#check ADMM.KKTNormalization.secondProx
#check ADMM.KKTNormalization.w_succ
#check ADMM.KKTNormalization.firstNormal_subgradient
#check ADMM.KKTNormalization.secondNormal_subgradient
#check ADMM.KKTNormalization.firstMargin_bounds
#check ADMM.KKTNormalization.secondMargin_bounds
#check ADMM.KKTNormalization.isTrajectory

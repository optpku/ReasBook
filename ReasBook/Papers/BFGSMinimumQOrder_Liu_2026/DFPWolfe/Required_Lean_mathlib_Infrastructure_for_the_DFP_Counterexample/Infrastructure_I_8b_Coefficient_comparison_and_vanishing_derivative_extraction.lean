module

public import ReasLib.Analysis.Calculus.ContDiff.Taylor
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.CoefficientComparison

/- Infrastructure I.8b (Coefficient comparison and vanishing-derivative extraction) (1) -/
#check FiniteTaylorJet.scalarCoeff_eq_of_eval_sub_isLittleO

/- Infrastructure I.8b (Coefficient comparison and vanishing-derivative extraction) (2) -/
#check ContDiffAt.taylor_isLittleO_of_iteratedDeriv_eq_zero

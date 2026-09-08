module

public import ReasLib.Algebra.GroupWithZero.PowerCancellation
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.LinearAlgebra.Matrix.Defs

/- Infrastructure I.10 (Exact cancellation of analytic powers) (1): the quotient
of analytic residual factors is analytic wherever the denominator is nonzero. -/
#check AnalyticAt.div

/- Infrastructure I.10 (Exact cancellation of analytic powers) (2): canceling
the exact common power gives the original scalar quotient away from zero. -/
#check (Function.div_eq_div_of_eq_pow_mul :
  ∀ (a : ℕ) (N D Nres Dres : ℝ → ℝ),
    (∀ ε, N ε = ε ^ a * Nres ε) → (∀ ε, D ε = ε ^ a * Dres ε) →
      ∀ {ε : ℝ}, ε ≠ 0 → Nres ε / Dres ε = N ε / D ε)

/- Infrastructure I.10 (Exact cancellation of analytic powers) (3): the
canceled scalar quotient has the explicit residual-factor value at zero. -/
#check Pi.div_apply

/- Infrastructure I.10 (Exact cancellation of analytic powers) (4): division
by a shared nonvanishing analytic residual denominator is analytic componentwise. -/
#check AnalyticAt.div

/- Infrastructure I.10 (Exact cancellation of analytic powers) (4, bundled): finite
families of componentwise analytic functions assemble into an analytic vector. -/
#check AnalyticAt.pi

/- Infrastructure I.10 (Exact cancellation of analytic powers) (4, characterization):
analyticity of a finite vector-valued function is equivalent to componentwise analyticity. -/
#check analyticAt_pi_iff

/- Infrastructure I.10 (Exact cancellation of analytic powers) (5): exact
common powers cancel componentwise from a vector numerator away from zero. -/
#check Function.div_eq_div_of_eq_pow_mul

/- Infrastructure I.10 (Exact cancellation of analytic powers) (6): the
canceled vector quotient has the entrywise residual-factor value at zero. -/
#check Pi.div_apply

/- Infrastructure I.10 (Exact cancellation of analytic powers) (7): division
by a shared nonvanishing analytic residual denominator is analytic entrywise. -/
#check AnalyticAt.div

/- Infrastructure I.10 (Exact cancellation of analytic powers) (7, bundled): iterated
finite families of entrywise analytic functions assemble into an analytic matrix. -/
#check AnalyticAt.pi

/- Infrastructure I.10 (Exact cancellation of analytic powers) (7, characterization):
analyticity of a finite matrix-valued function is equivalent to entrywise analyticity. -/
#check analyticAt_pi_iff

/- Infrastructure I.10 (Exact cancellation of analytic powers) (8): exact
common powers cancel entrywise from a matrix numerator away from zero. -/
#check Function.div_eq_div_of_eq_pow_mul

/- Infrastructure I.10 (Exact cancellation of analytic powers) (9): the
canceled matrix quotient has the entrywise residual-factor value at zero. -/
#check Pi.div_apply

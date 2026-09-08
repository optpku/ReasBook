module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.ResidualUniformAdapter

public section

open scoped BigOperators

universe u v

namespace LocalCutoff.GraphTransform

/-- Infrastructure I.16a: a principal branch estimate and a finite budget for
all non-principal branches give a norm estimate for their total residual. -/
theorem residual_norm_le_of_principal_and_nonDistinguished
    {ι : Type u} {E : Type v} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E]
    (distinguished : ι) (principal : E) (branches : ι → E)
    (δ ε : ℝ)
    (hprincipal : ‖principal‖ ≤ ε / 2)
    (hbranch : ∀ i, i ≠ distinguished → ‖branches i‖ ≤ δ)
    (hbudget : ((Fintype.card ι : ℝ) - 1) * δ ≤ ε / 2) :
    ‖principal + ∑ i, if i = distinguished then 0 else branches i‖ ≤ ε := by
  have hsum :
      ‖∑ i, if i = distinguished then 0 else branches i‖ ≤ ε / 2 :=
    norm_sum_if_eq_zero_le branches distinguished δ (ε / 2) hbranch hbudget
  calc
    ‖principal + ∑ i, if i = distinguished then 0 else branches i‖ ≤
        ‖principal‖ + ‖∑ i, if i = distinguished then 0 else branches i‖ :=
      norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hprincipal hsum
    _ = ε := by ring

/-- Infrastructure I.16a: a compact-uniform branch budget can be consumed
pointwise after a common radius has been chosen. -/
theorem residual_norm_le_of_uniform_nonDistinguished
    {ι : Type u} {Θ : Type v} {E : Type*}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    (distinguished : ι) (K : Set Θ) (principal : Θ → E)
    (branches : ι → Θ → ℝ → E) (δ ε : ℝ)
    (hprincipal : ∀ u ∈ K, ‖principal u‖ ≤ ε / 2)
    (hbranch : ∀ i, i ≠ distinguished → ∀ u ∈ K, ∀ t : ℝ,
      ‖branches i u t‖ ≤ δ)
    (hbudget : ((Fintype.card ι : ℝ) - 1) * δ ≤ ε / 2) :
    ∀ u ∈ K, ∀ t : ℝ,
      ‖principal u + ∑ i, if i = distinguished then 0 else branches i u t‖ ≤ ε := by
  intro u hu t
  exact residual_norm_le_of_principal_and_nonDistinguished distinguished
    (principal u) (fun i ↦ branches i u t) δ ε (hprincipal u hu)
    (fun i hi ↦ hbranch i hi u hu t) hbudget

end LocalCutoff.GraphTransform

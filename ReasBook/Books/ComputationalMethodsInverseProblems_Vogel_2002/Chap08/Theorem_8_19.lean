/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A1.ClosedConvex
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_19.Objective

public section

noncomputable section

/-!
Theorem 8.19.

This item states the source-facing existence-and-uniqueness claim for the
fixed Chapter 8 functional `(8.73)`. To avoid replacing the source object by a
provisional helper owner, the theorem writes the objective by its defining
formula instead of exporting a claim over an arbitrary or guessed surrogate
functional.
-/

namespace VariationalRegularization

variable {d : ℕ}

/-- thm_8_19. Theorem 8.19. Let `1 ≤ p < d / (d - 1)`, let `C` be a nonempty
closed convex subset of `L^p(Ω)`, and let `K : L^p(Ω) → L²(Ω)` be an injective
continuous linear map. Then, for each fixed datum `datum ∈ L²(Ω)` and
regularization parameter `α > 0`, the Chapter 8 functional `(8.73)` admits a
unique constrained minimizer on `C`. -/
theorem existsUnique_constrainedMinimizer_objective_8_73
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (hp_lt : p < ((d : ENNReal) / ((d - 1 : ℕ) : ENNReal)))
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (hC_nonempty : C.Nonempty)
    (hC : Set.ClosedConvex C)
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (hK_injective : Function.Injective K)
    (datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ) (hα : 0 < α) :
    ∃! fStar : MeasureTheory.Lp ℝ p (domainMeasure Ω),
      fStar ∈ C ∧
        IsMinOn
          (fun f : MeasureTheory.Lp ℝ p (domainMeasure Ω) ↦
            ((‖K f - datum‖ ^ 2 / 2 : ℝ) : EReal) +
              (α : EReal) * totalVariation (lpToL1 f))
          C fStar := sorry

end VariationalRegularization

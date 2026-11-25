/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A1.ClosedConvex
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_19.Minimizer

public section

noncomputable section

/-!
Theorem 8.19.

This file proves a compact-constraint version for the Chapter 8 functional
`(8.73)`. The admissible set must contain a finite-TV point: without this
condition the objective can be infinite everywhere, so uniqueness is false.

Compactness of the admissible set is an explicit stronger hypothesis than
the source's closed-convex constraint. Recovering the general source theorem
requires the BV compact-embedding and coercivity results; this version does
not claim to have established those results.
-/

namespace VariationalRegularization

variable {d : ℕ}

/-- thm_8_19. Compact-constraint version of Theorem 8.19. A compact convex
admissible set containing a finite-TV point has a unique constrained minimizer
of `(8.73)` when `K` is injective and `α > 0`. Under this stronger constraint
hypothesis no restriction on `p` beyond `1 ≤ p` is needed. -/
theorem existsUnique_constrainedMinimizer_objective_8_73
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (hC_compact : IsCompact C)
    (hC_convex : Convex ℝ C)
    (hC_finiteTV : ∃ f ∈ C, totalVariation (lpToL1 f) < ⊤)
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
          C fStar := by
  have hobj : tvRegularizedLeastSquaresFunctional K datum α =
      (fun f : MeasureTheory.Lp ℝ p (domainMeasure Ω) ↦
        ((‖K f - datum‖ ^ 2 / 2 : ℝ) : EReal) +
          (α : EReal) * totalVariation (lpToL1 f)) :=
    funext (tvRegularizedLeastSquaresFunctional_def K datum α)
  rw [← hobj]
  exact TVMinimizer.existsUnique_on_compact C hC_compact hC_convex hC_finiteTV
    K hK_injective datum hα

end VariationalRegularization

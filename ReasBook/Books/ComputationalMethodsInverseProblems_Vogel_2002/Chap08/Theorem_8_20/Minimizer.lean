/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_19.Objective

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- A constrained minimizer of the Chapter 8 TV-regularized least-squares
functional `tvRegularizedLeastSquaresFunctional K datum α` on `C`. -/
def IsTvRegularizedMinimizer
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) : Prop :=
  f ∈ C ∧ IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C f

namespace IsTvRegularizedMinimizer

/-- Construct a constrained TV-regularized minimizer from admissibility and
minimality on the constraint set. -/
theorem ofMemAndIsMinOn
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf_mem : f ∈ C)
    (hf_isMinOn : IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C f) :
    IsTvRegularizedMinimizer C K datum α f :=
  ⟨hf_mem, hf_isMinOn⟩

/-- A constrained TV-regularized minimizer is admissible. -/
theorem mem
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf : IsTvRegularizedMinimizer C K datum α f) :
    f ∈ C :=
  hf.1

/-- A constrained TV-regularized minimizer minimizes the Chapter 8 objective on
the constraint set. -/
theorem isMinOn
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hf : IsTvRegularizedMinimizer C K datum α f) :
    IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C f :=
  hf.2

end IsTvRegularizedMinimizer

/-- The defining characterization of `IsTvRegularizedMinimizer`. -/
theorem isTvRegularizedMinimizer_iff
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (f : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    IsTvRegularizedMinimizer C K datum α f ↔
      f ∈ C ∧ IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C f :=
  Iff.rfl

/-- A uniquely determined constrained minimizer of the Chapter 8
TV-regularized least-squares functional on `C`. -/
def IsUniqueTvRegularizedMinimizer
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (fStar : MeasureTheory.Lp ℝ p (domainMeasure Ω)) : Prop :=
  IsTvRegularizedMinimizer C K datum α fStar ∧
    ∀ f : MeasureTheory.Lp ℝ p (domainMeasure Ω),
      IsTvRegularizedMinimizer C K datum α f → f = fStar

namespace IsUniqueTvRegularizedMinimizer

/-- Construct a unique TV-regularized minimizer from a minimizer and the
corresponding uniqueness statement. -/
theorem ofIsTvRegularizedMinimizer
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {fStar : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hfStar : IsTvRegularizedMinimizer C K datum α fStar)
    (hunique :
      ∀ f : MeasureTheory.Lp ℝ p (domainMeasure Ω),
        IsTvRegularizedMinimizer C K datum α f → f = fStar) :
    IsUniqueTvRegularizedMinimizer C K datum α fStar :=
  ⟨hfStar, hunique⟩

/-- A unique TV-regularized minimizer is in particular a TV-regularized
minimizer. -/
theorem minimizer
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {fStar : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hfStar : IsUniqueTvRegularizedMinimizer C K datum α fStar) :
    IsTvRegularizedMinimizer C K datum α fStar :=
  hfStar.1

/-- A unique TV-regularized minimizer is admissible. -/
theorem mem
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {fStar : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hfStar : IsUniqueTvRegularizedMinimizer C K datum α fStar) :
    fStar ∈ C :=
  hfStar.1.1

/-- A unique TV-regularized minimizer minimizes the Chapter 8 objective on the
constraint set. -/
theorem isMinOn
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {fStar : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hfStar : IsUniqueTvRegularizedMinimizer C K datum α fStar) :
    IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C fStar :=
  hfStar.1.2

/-- Any constrained TV-regularized minimizer agrees with the unique one. -/
theorem eq
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    {C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω))}
    {K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω)}
    {α : ℝ}
    {fStar f : MeasureTheory.Lp ℝ p (domainMeasure Ω)}
    (hfStar : IsUniqueTvRegularizedMinimizer C K datum α fStar)
    (hf : IsTvRegularizedMinimizer C K datum α f) :
    f = fStar :=
  hfStar.2 f hf

end IsUniqueTvRegularizedMinimizer

/-- The defining characterization of `IsUniqueTvRegularizedMinimizer`. -/
theorem isUniqueTvRegularizedMinimizer_iff
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {p : ENNReal} [Fact ((1 : ENNReal) ≤ p)]
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (C : Set (MeasureTheory.Lp ℝ p (domainMeasure Ω)))
    (K : MeasureTheory.Lp ℝ p (domainMeasure Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (datum : MeasureTheory.Lp ℝ 2 (domainMeasure Ω))
    (α : ℝ)
    (fStar : MeasureTheory.Lp ℝ p (domainMeasure Ω)) :
    IsUniqueTvRegularizedMinimizer C K datum α fStar ↔
      (fStar ∈ C ∧ IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C fStar) ∧
        ∀ f : MeasureTheory.Lp ℝ p (domainMeasure Ω),
          f ∈ C →
            IsMinOn (tvRegularizedLeastSquaresFunctional K datum α) C f →
              f = fStar := by
  constructor
  · intro hfStar
    refine ⟨hfStar.1, ?_⟩
    intro f hf_mem hf_isMinOn
    exact hfStar.2 f ⟨hf_mem, hf_isMinOn⟩
  · rintro ⟨hfStar, hunique⟩
    refine ⟨hfStar, ?_⟩
    intro f hf
    exact hunique f hf.1 hf.2

end VariationalRegularization

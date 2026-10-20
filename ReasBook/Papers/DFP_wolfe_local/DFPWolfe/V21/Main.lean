module

public import ReasLib.Optimization.DFP.Polar.OrthogonalExtension
public import ReasLib.Optimization.DFP.GlobalConvergence
public import ReasLib.Optimization.DFP.LevelSetGlobalConvergence

public section

open DFP.Polar

namespace DFPWolfe.V21

/-- thm:main. For every `n≥2`, `0<c₁<2/3`, `2/3≤c₂<1`, and `0<ε<1`, the
original v21 polar construction gives a canonical matrix-valued inverse DFP iteration
with positive step lengths and strong Wolfe at every index. The standard certificate
contains its C² objective and the fixed global Hessian bounds `I/2` and `3I/2`.

`CounterexampleProperties` records gradient-norm limit exactly one, operator distance
of the Hessian from identity at most ε, global half-Hölder Hessian continuity, `f(0)=0`
and the unique origin minimizer. It also records failure of every β-Hölder Hessian bound
on the original initial level set for `β∈(1/2,1]`, and the exact unit-circle cluster set
under `planeEmbedding`. This is a linear isometric embedding of the source plane;
`planeEmbedding_range_finrank` proves its range has dimension exactly two.

The source identities retain the concrete original polar objective, points, step
lengths, gradients, and inverse Hessians, followed by the source orthogonal extension. -/
theorem main (n : ℕ) (hn : 2 ≤ n) (c₁ c₂ ε : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1)
    (hε : ε ∈ Set.Ioo 0 1) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂,
      OrthogonalExtension.CounterexampleProperties ε w
          (OrthogonalExtension.planeEmbedding n hn) ∧
        ∃ νStar > baseAngle, ∃ κ > 0, ∃ j₀ : ℕ, 0 < j₀ ∧
          ∃ c : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
            PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ c ∧
              OrthogonalExtension.FinExtensionIdentity n hn c w := by
  exact OrthogonalExtension.polarCounterexample n hn c₁ c₂ ε hc₁ hc₁lim hc₂lim hc₂ hε.1

/-- Helper for thm:main and eq:open-question: the new v21 polar witness disproves
global weak-Wolfe convergence for every pair in the source parameter range. The
convergence predicate quantifies over ordinary admissible inverse DFP iterations. -/
theorem not_globalWeakWolfeConvergenceAt (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ¬ DFP.GlobalWeakWolfeConvergenceAt c₁ c₂ := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  have hbounds : (1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨w, _, _⟩ := main 2 le_rfl c₁ c₂ (1 / 2) hc₁ hc₁lim hc₂lim hc₂ hhalf
  exact DFP.not_globalWeakWolfeConvergenceAt_of_counterexample
    w.toWolfeCounterexample le_rfl hhalf.1 hbounds

/-- Helper for thm:main and eq:open-question: the same new polar construction
disproves the initial-level-set formulation of ordinary weak-Wolfe DFP convergence,
with the source Wolfe parameter range unchanged. -/
theorem not_levelSetGlobalWeakWolfeConvergenceAt (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ¬ DFP.LevelSetGlobalWeakWolfeConvergenceAt c₁ c₂ := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  have hbounds : (1 / 2 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨w, _, _⟩ := main 2 le_rfl c₁ c₂ (1 / 2) hc₁ hc₁lim hc₂lim hc₂ hhalf
  exact DFP.not_levelSetGlobalWeakWolfeConvergenceAt_of_counterexample
    w.toWolfeCounterexample le_rfl hhalf.1 hbounds

end DFPWolfe.V21

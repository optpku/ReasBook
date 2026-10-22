/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_33

open Filter ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- Theorem 24.32: this file restores the missing label-associated entry in the original target
file by re-exposing the dependency-closed size-biased symmetric Dirichlet convergence theorem that
feeds the Poisson--Dirichlet limit argument. -/
theorem tendsto_orderedSymmetricDirichletLaw_poissonDirichletLimit
    (θ : ℝ) (hθ : 0 < θ) :
    Tendsto
      (fun n ↦ finiteSizeBiasedDirichletProbabilityMeasure θ hθ n)
      atTop
      (nhds (gemProbabilityMeasure θ hθ)) := by
  -- Proof comment: the Chapter 24 owner theorem already proves the convergence of the explicit
  -- size-biased symmetric Dirichlet laws to `GEM_θ`, so the local repair is just a labeled
  -- re-export of that dependency-closed result.
  simpa using sizeBiasedSymmetricDirichletLaw_tendsto_gemMeasure θ hθ

end ProbabilityTheory

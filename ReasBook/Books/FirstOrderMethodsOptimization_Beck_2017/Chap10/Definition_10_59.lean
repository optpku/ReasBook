/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 10.59 is `source-facing`: it fixes the standing assumptions for the constrained
problem `min {h(x) | x ∈ C}` used in the S-FISTA subsection. The relevant mathlib owners are the
standard predicates `C.Nonempty`, `IsClosed C`, `Convex ℝ C`, `ConvexOn ℝ Set.univ h`, and
`LipschitzWith ℓh h`. Following the project pattern for problem data in Chapter 10, the clean
public interface is therefore a small `Prop`-valued class on the objective, the feasible set, and
the given Lipschitz constant, rather than a new packaged optimization object. -/

/-- Definition 10.59: the constrained problem `min {h(x) | x ∈ C}` has a nonempty closed convex
feasible set `C`, and its objective `h : E → ℝ` is globally convex and `ℓ_h`-Lipschitz. -/
class IsConvexLipschitzConstrainedMinimizationProblem
    (h : E → ℝ) (C : Set E) (ℓh : NNReal) : Prop where
  constraint_nonempty : C.Nonempty
  constraint_closed : IsClosed C
  constraint_convex : Convex ℝ C
  objective_convex : ConvexOn ℝ Set.univ h
  objective_lipschitz : LipschitzWith ℓh h

/-- A constrained convex Lipschitz minimization problem canonically makes the real-valued
objective proper after coercion to `EReal`. -/
theorem IsConvexLipschitzConstrainedMinimizationProblem.objective_toEReal_proper
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    IsProperExtendedRealFunction h.toEReal := by
  rcases hproblem.constraint_nonempty with ⟨x, hx⟩
  let _ : Nonempty E := ⟨x⟩
  simpa using Function.toEReal_isProper h

/-- A constrained convex Lipschitz minimization problem makes the real-valued objective
lower semicontinuous after coercion to `EReal`. -/
theorem IsConvexLipschitzConstrainedMinimizationProblem.objective_toEReal_lowerSemicontinuous
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    LowerSemicontinuous h.toEReal :=
  Function.toEReal_lowerSemicontinuous_of_lipschitz hproblem.objective_lipschitz

/-- A constrained convex Lipschitz minimization problem makes the real-valued objective convex
after coercion to `EReal`. -/
theorem IsConvexLipschitzConstrainedMinimizationProblem.objective_toEReal_convex
    {h : E → ℝ} {C : Set E} {ℓh : NNReal}
    (hproblem : IsConvexLipschitzConstrainedMinimizationProblem h C ℓh) :
    is_convex_function h.toEReal :=
  Function.toEReal_isConvexFunction hproblem.objective_convex

end

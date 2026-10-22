/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped ConstrainedArgmin WithTopConvexAnalysis

/- Algorithm 3.9 lies in the chapter's Kelley cutting-plane domain for real-valued constrained
minimization on a real inner-product space.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the owner constrained problem
  carrying the feasible set `Q` and objective `f`;
* `IsSubgradientAt` and `subdifferential` in `Definition_3_1_5`, where the former is the
  primitive owner notion and the latter is the derived set-valued API, here specialized to the
  real objective by the coercion `fun x ↦ (problem x : WithTop ℝ)`;
* `nonsmoothModel` in `Lemma_3_3_2`, the chapter owner for the Kelley model
  `\hat f_k(X; ·) = max_{0 ≤ i ≤ k} {f(x_i) + ⟪g_i, · - x_i⟫}`;
* `constrainedArgmin` in `Chap01/Definition_1_3_3`, the canonical owner argmin set for a
  feasible-set minimization problem.

Best owner abstraction:
* a fixed constrained problem `problem : SetConstrainedMinimizationProblem E`;
* the primitive subgradient predicate `IsSubgradientAt (fun x ↦ (problem x : WithTop ℝ))`;
* the Kelley model family `nonsmoothModel problem xSeq g`;
* the canonical Kelley-step owner
  `argmin[problem.feasibleSet] (nonsmoothModel problem xSeq g k)`.

Source/core/bridge triage:
* source-facing: `KelleyMethod problem`;
* core/canonical: the owner subgradient predicate
  `IsSubgradientAt (fun x ↦ (problem x : WithTop ℝ)) x_k g_k` and the owner Kelley-step argmin
  set `argmin[problem.feasibleSet] (nonsmoothModel problem xSeq g k)`;
* bridge/view: the subdifferential-membership and minimizing-step theorems in the namespace
  below.

Primitive data:
* the iterate sequence `x₀, x₁, x₂, ...`;
* the chosen sampled vectors `g_k`;
* the initial feasibility;
* the pointwise subgradient specification;
* the Kelley-step argmin specification.

Derived API:
* the subdifferential membership statement
  `subgradient k ∈ subdifferential (fun x ↦ (problem x : WithTop ℝ)) (iterates k)`;
* the Kelley model `nonsmoothModel problem xSeq g k`;
* iterate feasibility.
-/

/-- Algorithm 3.9: for a constrained problem `min_{x ∈ Q} f(x)`, Kelley's method is given by an
initial feasible point `x₀`, a sampled subgradient sequence `g_k ∈ ∂f(x_k)`, and an iterate
sequence whose successor `x_{k+1}` minimizes the canonical Kelley model
`\hat f_k(X; ·) = nonsmoothModel f x g k` over the feasible set `Q`. -/
structure KelleyMethod (problem : SetConstrainedMinimizationProblem E) where
  /-- The iterate sequence `x₀, x₁, x₂, ...`. -/
  iterates : ℕ → E
  /-- The chosen sampled vector `g_k`. -/
  subgradient : ℕ → E
  /-- The initialization chooses a feasible point `x₀ ∈ Q`. -/
  x0_mem : iterates 0 ∈ problem.feasibleSet
  /-- Each sampled vector is a genuine subgradient of the owner objective at the current iterate.
  -/
  subgradient_spec (k : ℕ) :
    IsSubgradientAt (fun x ↦ (problem x : WithTop ℝ)) (iterates k) (subgradient k)
  /-- Each new iterate `x_{k+1}` belongs to the argmin set of the current Kelley model on `Q`. -/
  nextIterate_mem_argmin (k : ℕ) :
    iterates (k + 1) ∈
      argmin[problem.feasibleSet] (nonsmoothModel problem iterates subgradient k)

namespace KelleyMethod

variable {problem : SetConstrainedMinimizationProblem E}

/-- A Kelley method can be used as its underlying iterate sequence. -/
instance : CoeFun (KelleyMethod problem) (fun _ ↦ ℕ → E) where
  coe method := method.iterates

/-- The sampled vector at stage `k` is a genuine subgradient of the owner objective at `x_k`. -/
theorem subgradient_isSubgradientAt
    (method : KelleyMethod problem) (k : ℕ) :
    IsSubgradientAt (fun x ↦ (problem x : WithTop ℝ)) (method k) (method.subgradient k) := by
  exact method.subgradient_spec k

/-- The sampled vector at stage `k` belongs to the owner subdifferential at `x_k`. -/
theorem subgradient_mem_subdifferential
    (method : KelleyMethod problem) (k : ℕ) :
    method.subgradient k ∈ ∂ (fun x ↦ (problem x : WithTop ℝ))((method k)) := by
  exact mem_subdifferential_iff.mpr (method.subgradient_isSubgradientAt k)

/-- Each successor iterate belongs to the argmin set of the current Kelley model on `Q`. -/
theorem iterates_succ_mem_argmin
    (method : KelleyMethod problem) (k : ℕ) :
    method (k + 1) ∈
      argmin[problem.feasibleSet] (nonsmoothModel problem method method.subgradient k) := by
  exact method.nextIterate_mem_argmin k

/-- Each successor iterate is feasible and minimizes the current Kelley model over the feasible
set. -/
theorem iterates_succ_mem_and_isMinOn
    (method : KelleyMethod problem) (k : ℕ) :
    method (k + 1) ∈ problem.feasibleSet ∧
      IsMinOn
        (nonsmoothModel problem method method.subgradient k)
        problem.feasibleSet
        (method (k + 1)) := by
  exact mem_constrainedArgmin_iff.mp (method.iterates_succ_mem_argmin k)

/-- Every iterate produced by a Kelley method lies in the feasible set. -/
-- Proof sketch: use the field `x0_mem` for the base case and
-- `iterates_succ_mem_and_isMinOn` for the successor step.
theorem iterates_mem
    (method : KelleyMethod problem) (k : ℕ) :
    method k ∈ problem.feasibleSet := by
  induction k with
  | zero =>
      simpa using method.x0_mem
  | succ k _ =>
      exact (method.iterates_succ_mem_and_isMinOn k).1

end KelleyMethod

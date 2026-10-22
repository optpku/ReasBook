/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_51
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_52
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_53

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section Ambient

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

attribute [local instance] Classical.decPred

/-
Primary domain: cutting-plane schemes for constrained convex minimization with a separation
oracle.

Relevant owner-style declarations sampled before refinement:
- `ConvexMinimizationWithSeparationOracle` in `Definition_3_51` for the ambient constrained
  problem together with its separation oracle;
- `SeparatesByCuttingVector` and `cuttingHalfspace` in `Definition_3_51` for the owner-side strict
  affine cut and its retained closed half-space;
- `ConvexMinimizationSeparationOracle.subgradient_spec` in `Definition_3_51` for feasible query
  points;
- `ConvexMinimizationSeparationOracle.separating_spec` in `Definition_3_51` for infeasible query
  points;
- `StrictlySeparatesPointFromWith` in `Definition_3_1_4_1` for the underlying point/set strict
  separation geometry.

Source/core/bridge triage:
- source-facing: `GeneralCuttingPlaneScheme`;
- core/canonical: `ConvexMinimizationWithSeparationOracle E`;
- bridge/view: the source-facing localization/query data carried by `GeneralCuttingPlaneScheme`.

Owner abstractions:
- the chapter owner object `ConvexMinimizationWithSeparationOracle`;
- its query-to-vector oracle field `problem.oracle.oracle`;
- the retained cut `cuttingHalfspace y g` from `Definition_3_51`.

Primitive data:
- the localization sets `Eₖ` and query points `yₖ`.

Derived API:
- the cutting vectors `gₖ = problem.oracle (yₖ)`;
- the feasible/infeasible case split inherited from the owner oracle;
- the imported strict-separation and retained-half-space API from `Definition_3_51`;
- the coercion from a scheme to its query sequence.

Selected-feasible bridge data derived from the same owner:
- the canonical selected feasible subsequence `feasibleSubsequence problem.feasibleSet scheme`;
- the selected feasible counter `Nat.count (fun j ↦ scheme j ∈ problem.feasibleSet)`;
- the selected-stage localization containment theorem below.

Accordingly, this file keeps the source-facing localization/query data of Algorithm 3.6, derives
its cutting vectors from the owner separation oracle and reuses the owner-side retained cut
`cuttingHalfspace`. -/

/-- Algorithm 3.6: a general cutting-plane scheme for minimizing `f` over `Q` consists of bounded
initial localization data `E₀ ⊇ Q`, a query sequence `yₖ ∈ Eₖ`, the cutting vectors returned by
the owner separation oracle at those query points, and successor localization sets `Eₖ₊₁`
containing the retained slice `{x ∈ Eₖ | ⟪gₖ, yₖ - x⟫ ≥ 0}`. On feasible queries the owner oracle
returns a subgradient of `f`; on infeasible queries it returns a strict separating vector. -/
structure GeneralCuttingPlaneScheme (problem : ConvexMinimizationWithSeparationOracle E) where
  /-- The localization sets `E₀, E₁, E₂, ...`. -/
  localizer : ℕ → Set E
  /-- The query points `y₀, y₁, y₂, ...`. -/
  queryPoint : ℕ → E
  /-- The initial localization set `E₀` is bounded. -/
  initial_bounded : Bornology.IsBounded (localizer 0)
  /-- The feasible set `Q` is contained in the initial localization set `E₀`. -/
  feasibleSet_subset_initial : problem.feasibleSet ⊆ localizer 0
  /-- Each query point `yₖ` is chosen from the current localization set `Eₖ`. -/
  query_mem (k : ℕ) : queryPoint k ∈ localizer k
  /-- The next localization set contains the half-space slice of the current localization set cut
  out by the current cutting vector at the current query point. -/
  next_localizer_contains (k : ℕ) :
    localizer k ∩ cuttingHalfspace (queryPoint k) (problem.oracle (queryPoint k)) ⊆
      localizer (k + 1)

namespace GeneralCuttingPlaneScheme

/-
The declarations below all live over a fixed ambient constrained problem with separation oracle.
-/
variable {problem : ConvexMinimizationWithSeparationOracle E}

attribute [local instance] Classical.decPred

instance : CoeFun (GeneralCuttingPlaneScheme problem) (fun _ ↦ ℕ → E) where
  coe scheme := scheme.queryPoint

-- Proof sketch: unfold the coercion from a scheme to its query sequence.
@[simp] theorem coe_apply
    (scheme : GeneralCuttingPlaneScheme problem) (k : ℕ) :
    scheme k = scheme.queryPoint k :=
  rfl

/-- The cutting vector at step `k` is the owner oracle value at the current query point. -/
def cuttingVector (scheme : GeneralCuttingPlaneScheme problem) (k : ℕ) : E :=
  problem.oracle (scheme k)

/-- The canonical localization sets generated by a scheme's query points and owner-oracle cutting
vectors stay inside the scheme's chosen localizers. -/
-- Proof sketch: induct on `k`; the base case is the initial feasible-set inclusion, and the step
-- uses the recursive definition of `localizationSets` together with `next_localizer_contains`.
theorem localizationSets_subset_localizer
    (scheme : GeneralCuttingPlaneScheme problem) (k : ℕ) :
    localizationSets problem.feasibleSet scheme scheme.cuttingVector k ⊆ scheme.localizer k :=
  by
    induction k with
    | zero =>
        simpa using scheme.feasibleSet_subset_initial
    | succ k hk =>
        intro x hx
        rw [localizationSets_succ] at hx
        exact scheme.next_localizer_contains k
          ⟨hk hx.1, by simpa [GeneralCuttingPlaneScheme.cuttingVector] using hx.2⟩

/-- Along the canonical selected feasible subsequence of a cutting-plane scheme, the retained
localization stage at the selected-feasible counter `i(k)` stays inside the raw stage-`k`
localizer. -/
theorem selectedLocalizationSets_subset_localizer
    (scheme : GeneralCuttingPlaneScheme problem) (k : ℕ) :
    localizationSets
        problem.feasibleSet
        (feasibleSubsequence problem.feasibleSet scheme)
        (problem.oracle ∘ feasibleSubsequence problem.feasibleSet scheme)
        (Nat.count (fun j ↦ scheme j ∈ problem.feasibleSet) k) ⊆
      scheme.localizer k := by
  classical
  let X : ℕ → E := feasibleSubsequence problem.feasibleSet scheme
  let S : ℕ → Set E := localizationSets problem.feasibleSet X (problem.oracle ∘ X)
  let i : ℕ → ℕ := Nat.count (fun j ↦ scheme j ∈ problem.feasibleSet)
  change S (i k) ⊆ scheme.localizer k
  have hsubsetQ : ∀ j : ℕ, S j ⊆ problem.feasibleSet := by
    intro j
    induction j with
    | zero =>
        simp [S, localizationSets_zero]
    | succ j hj =>
        intro x hx
        have hx' :
            x ∈ S j ∩ cuttingHalfspace (X j) ((problem.oracle ∘ X) j) := by
          simpa [S, localizationSets_succ] using hx
        exact hj hx'.1
  induction k with
  | zero =>
      simpa [S, i, localizationSets_zero] using scheme.feasibleSet_subset_initial
  | succ k hk =>
      by_cases hyk : scheme k ∈ problem.feasibleSet
      · have hi :
            i (k + 1) = i k + 1 := by
          simpa [i] using
            (Nat.count_succ_eq_succ_count hyk :
              Nat.count (fun j ↦ scheme j ∈ problem.feasibleSet) (k + 1) =
                Nat.count (fun j ↦ scheme j ∈ problem.feasibleSet) k + 1)
        intro x hx
        rw [hi] at hx
        have hx' :
            x ∈ S (i k) ∩ cuttingHalfspace (X (i k)) ((problem.oracle ∘ X) (i k)) := by
          simpa [S, localizationSets_succ] using hx
        have hxLocalizer : x ∈ scheme.localizer k := hk hx'.1
        have hX : X (i k) = scheme k := by
          simpa [X, i] using
            (feasibleSubsequence_count_eq_self_of_feasible problem.feasibleSet scheme hyk)
        have hxCut : x ∈ cuttingHalfspace (scheme k) (problem.oracle (scheme k)) := by
          simpa [hX] using hx'.2
        exact scheme.next_localizer_contains k ⟨hxLocalizer, hxCut⟩
      · have hi :
            i (k + 1) = i k := by
          simpa [i] using
            (Nat.count_succ_eq_count hyk :
              Nat.count (fun j ↦ scheme j ∈ problem.feasibleSet) (k + 1) =
                Nat.count (fun j ↦ scheme j ∈ problem.feasibleSet) k)
        have hQcut :
            problem.feasibleSet ⊆ cuttingHalfspace (scheme k) (problem.oracle (scheme k)) :=
          (problem.oracle.separating_spec hyk).subset_cuttingHalfspace
        intro x hx
        rw [hi] at hx
        have hxLocalizer : x ∈ scheme.localizer k := hk hx
        have hxQ : x ∈ problem.feasibleSet := hsubsetQ (i k) hx
        exact scheme.next_localizer_contains k ⟨hxLocalizer, hQcut hxQ⟩

end GeneralCuttingPlaneScheme

end Ambient

end

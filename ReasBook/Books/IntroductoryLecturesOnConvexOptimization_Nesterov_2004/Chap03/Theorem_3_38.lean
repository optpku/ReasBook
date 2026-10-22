/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_31
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators WithTopConvexAnalysis

universe u v w

/- Theorem 3.38 lies in the chapter's max-type active-subgradient saddle domain.

Sampled owner-style declarations:
- `pointwiseSupremumOn` in `Chap03/Theorem_3_1_8` and
  `activePointwiseSupremumOnIndices` in `Chap03/Lemma_3_1_14`, the chapter owners for the
  faithful upper envelope and active parameters;
- `subdifferentialWithin` and the source-facing notation `∂[P] f(x)` in `Chap03/Theorem_3_44`,
  the chapter owner surface for relative subgradients;
- `IsSaddlePointOn` in `Mathlib/Order/SaddlePoint`, the canonical saddle-point owner on
  `P × S`;
- `minimax_eq_of_activeSubgradientRepresentation_at_minimizer` in `Chap03/Theorem_3_1_31`, the
  stronger barycentric minimax theorem from which the present source-facing result is a more
  general abstract-parameter variant.

Best owner abstraction:
- source-facing: existence of a saddle parameter produced from an active-subgradient
  representation;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `∂[P] f(x)`,
  together with `IsSaddlePointOn`;
- bridge/view: the raw aggregation hypothesis
  `∃ uBar ∈ S, ∀ x ∈ P, ∑ i, λ i * Ψ x (u i) ≤ Ψ x uBar`, which keeps the source's abstract
  parameter `uBar : U` instead of imposing additive structure on `U`.

Primitive data:
- the feasible primal set `P` and parameter set `S`;
- the kernel `Ψ`;
- the minimizing primal point `xStar` and its active-slice subgradient representation.

Derived API:
- the real-valued objective `f` together with its faithful upper-envelope bridge on `P`;
- the owner active set `activePointwiseSupremumOnIndices S (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar`;
- the canonical saddle predicate `IsSaddlePointOn P S Ψ xStar`.

The previous version duplicated the subgradient owner locally and treated the real-valued upper
envelope as a primitive owner. This refinement deletes the duplicate wheel, reuses the faithful
`WithTop ℝ` upper-envelope owner through an explicit real-valued bridge `f`, removes the one-off
saddle and aggregation wrappers, and phrases the source-facing result directly on the chapter
owner API. The active-family surface also lives at the canonical finite-index layer
`ι : Type*` with `[Fintype ι]`, not the over-concrete display model `Fin k`. -/

variable {E : Type u} {U : Type v} {ι : Type w}

variable [Fintype ι]

variable [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Theorem 3.38: if `f : E → ℝ` is a real-valued objective on `P` whose `WithTop ℝ` lift agrees
with the faithful upper-envelope owner
`pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ))`, if `xStar` minimizes `f` on `P`, if a
relative subgradient `gStar ∈ ∂[P] f(xStar)` annihilates every feasible
displacement `x - xStar`, and if `gStar` is a simplex-weighted combination of relative
subgradients `g i ∈ ∂[P] (fun x ↦ Ψ x (u i)) (xStar)` of active slices
`x ↦ Ψ(x, u i)` at `xStar` whose weighted slice values can be
aggregated by one parameter `uBar ∈ S`, then that aggregated parameter is a saddle point of `Ψ`
on `P × S` with first coordinate `xStar`; equivalently, it realizes the same lower-envelope value
as the primal optimum at `xStar`. -/
-- Proof sketch: use the representation
-- `gStar = ∑ i, weights.weights i • g i` and the orthogonality assumption to rewrite
-- `f xStar` as a weighted sum of the pairings `⟪g i, x - xStar⟫`. Apply the
-- relative subgradient inequality for each active slice `Ψ(·, u i)` and use activity at `xStar`
-- to get `f xStar ≤ ∑ i, weights.weights i * Ψ x (u i)` for every `x ∈ P`.
-- The aggregation hypothesis upgrades this to `f xStar ≤ Ψ x uBar` on `P`,
-- so `f xStar` is a lower bound for the image of `x ↦ Ψ x uBar` on `P`. The
-- faithful upper-envelope bridge gives `Ψ xStar uBar ≤ f xStar`, and for
-- every `u ∈ S` we also have `Ψ xStar u ≤ f xStar`. Combining these two
-- bounds yields `Ψ xStar u ≤ Ψ x uBar` for all `x ∈ P` and `u ∈ S`, i.e. the canonical saddle
-- relation `IsSaddlePointOn P S Ψ xStar uBar`.
theorem exists_saddle_parameter_of_active_subgradient_representation
    {P : Set E} {S : Set U} {Ψ : E → U → ℝ} {f : E → ℝ}
    {xStar gStar : E}
    (hf_eq :
      ∀ ⦃x : E⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hxStar_min : IsMinOn f P xStar)
    (hgStar_mem : gStar ∈ ∂[P] f(xStar))
    (horth : ∀ ⦃x : E⦄, x ∈ P → inner ℝ gStar (x - xStar) = 0)
    (weights : StdSimplex ℝ ι)
    (u : ι → U) (g : ι → E)
    (hu_active :
      ∀ i : ι,
        u i ∈ activePointwiseSupremumOnIndices S
          (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar)
    (hg_mem :
      ∀ i : ι, g i ∈ ∂[P] ((fun x ↦ Ψ x (u i)) : E → ℝ) (xStar))
    (hgStar_repr : gStar = ∑ i, weights.weights i • g i)
    (haggregate :
      ∃ uBar ∈ S,
        ∀ ⦃x : E⦄, x ∈ P →
          ∑ i, weights.weights i * Ψ x (u i) ≤ Ψ x uBar) :
    ∃ uBar ∈ S, IsSaddlePointOn P S Ψ xStar uBar := by
  -- The feasible membership of `xStar` comes from the relative-subgradient hypothesis.
  rw [mem_subdifferentialWithin_iff] at hgStar_mem
  rcases hgStar_mem with ⟨hxStar, -⟩
  rcases haggregate with ⟨uBar, huBar, huBar_dom⟩
  have hsum : ∑ i, weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  -- Active indices lie in `S` and realize the objective value at `xStar`.
  have hactive_value : ∀ i : ι, u i ∈ S ∧ Ψ xStar (u i) = f xStar := by
    intro i
    rcases (mem_activePointwiseSupremumOnIndices_iff.mp (hu_active i)) with ⟨huS, huEq⟩
    refine ⟨huS, ?_⟩
    apply WithTop.coe_injective
    calc
      (Ψ xStar (u i) : WithTop ℝ)
          = pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar := huEq
      _ = (f xStar : WithTop ℝ) := by
        symm
        exact hf_eq hxStar
  -- Every slice at `xStar` lies below the upper-envelope value `f xStar`.
  have hslice_le : ∀ ⦃y : U⦄, y ∈ S → Ψ xStar y ≤ f xStar := by
    intro y hy
    have hySup :
        (Ψ xStar y : WithTop ℝ) ≤
          pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar := by
      rw [pointwiseSupremumOn_apply]
      refine le_csSup ?_ ?_
      · exact ⟨⊤, fun _ _ ↦ le_top⟩
      · exact ⟨y, hy, rfl⟩
    have hySup' : (Ψ xStar y : WithTop ℝ) ≤ (f xStar : WithTop ℝ) := by
      simpa [hf_eq hxStar] using hySup
    exact_mod_cast hySup'
  refine ⟨uBar, huBar, ?_⟩
  intro x hx y hy
  -- Sum the active-slice subgradient inequalities with the simplex weights.
  have hweighted_gap :
      ∑ i, weights.weights i * inner ℝ (g i) (x - xStar) ≤
        ∑ i, weights.weights i * (Ψ x (u i) - Ψ xStar (u i)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hsubgrad_i :
        inner ℝ (g i) (x - xStar) ≤ Ψ x (u i) - Ψ xStar (u i) := by
      rcases (mem_subdifferentialWithin_iff.mp (hg_mem i)) with ⟨-, hminorant⟩
      have hminorant_x := hminorant hx
      linarith
    exact mul_le_mul_of_nonneg_left hsubgrad_i (weights.nonneg i)
  have horth_sum :
      ∑ i, weights.weights i * inner ℝ (g i) (x - xStar) = 0 := by
    have hrepr :
        inner ℝ gStar (x - xStar) =
          ∑ i, weights.weights i * inner ℝ (g i) (x - xStar) := by
      calc
        inner ℝ gStar (x - xStar)
            = inner ℝ (∑ i, weights.weights i • g i) (x - xStar) := by
                rw [hgStar_repr]
        _ = ∑ i, inner ℝ (weights.weights i • g i) (x - xStar) := by
          rw [sum_inner]
        _ = ∑ i, weights.weights i * inner ℝ (g i) (x - xStar) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using
            (inner_smul_left_eq_smul (x := g i) (y := x - xStar) (r := weights.weights i))
    rw [← hrepr, horth hx]
  have hgap_nonneg :
      0 ≤ ∑ i, weights.weights i * (Ψ x (u i) - Ψ xStar (u i)) := by
    simpa [horth_sum] using hweighted_gap
  have hactive_sum :
      ∑ i, weights.weights i * Ψ xStar (u i) = f xStar := by
    calc
      ∑ i, weights.weights i * Ψ xStar (u i)
          = ∑ i, weights.weights i * f xStar := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [(hactive_value i).2]
      _ = (∑ i, weights.weights i) * f xStar := by
        rw [Finset.sum_mul]
      _ = f xStar := by
        rw [hsum, one_mul]
  have hobjective_le_weighted :
      f xStar ≤ ∑ i, weights.weights i * Ψ x (u i) := by
    have hrewrite :
        ∑ i, weights.weights i * (Ψ x (u i) - Ψ xStar (u i)) =
          ∑ i, weights.weights i * Ψ x (u i) - f xStar := by
      calc
        ∑ i, weights.weights i * (Ψ x (u i) - Ψ xStar (u i))
            = ∑ i, (weights.weights i * Ψ x (u i) - weights.weights i * Ψ xStar (u i)) := by
                simp_rw [mul_sub]
        _ = (∑ i, weights.weights i * Ψ x (u i)) -
              ∑ i, weights.weights i * Ψ xStar (u i) := by
                rw [Finset.sum_sub_distrib]
        _ = ∑ i, weights.weights i * Ψ x (u i) - f xStar := by
          rw [hactive_sum]
    rw [hrewrite] at hgap_nonneg
    linarith
  -- The aggregation witness upgrades the weighted lower bound to a single parameter `uBar`.
  have hobjective_le_uBar : f xStar ≤ Ψ x uBar := by
    exact le_trans hobjective_le_weighted (huBar_dom hx)
  -- Sandwich both sides through `f xStar` to obtain the saddle inequality.
  exact le_trans (hslice_le hy) hobjective_le_uBar

end

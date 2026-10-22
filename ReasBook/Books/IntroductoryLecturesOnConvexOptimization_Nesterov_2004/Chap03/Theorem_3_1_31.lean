/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

local notation:max "∂[" Q "] " f:arg "(" x:arg ")" => subdifferentialWithin Q f x

universe u v w

/- Theorem 3.1.31 lies in the chapter's minimax / active-subgradient domain.

Mandatory domain-style sampling before refinement:
- `pointwiseSupremumOn` in `Chap03/Theorem_3_1_8`, the chapter owner for subset-indexed upper
  envelopes on the `WithTop ℝ` side;
- `activePointwiseSupremumOnIndices` in `Chap03/Lemma_3_1_14`, the canonical active-set owner for
  pointwise suprema;
- the source-facing notation `∂[P] f(x)`, together with the bridge
  `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Chap03/Theorem_3_44`, the
  chapter owner surface for real-valued relative subgradients;
- mathlib `IsMinOn` and `StdSimplex`, the canonical owners for minimizers on a set and simplex
  weights.

Best owner abstraction:
- source-facing: the minimax equality theorem below;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `IsMinOn`,
  `∂[P] f(x)`, and `StdSimplex`;
- bridge/view: the real-valued objective `f` on `P`, together with its equality to the
  `WithTop ℝ` owner `pointwiseSupremumOn`.

Primitive data:
- the primal set `P`, parameter set `S`, and kernel `Ψ`;
- the real-valued primal objective `f`;
- the minimizing primal point `xStar`;
- the active slice parameters `u i` and their relative subgradients `g i`;
- the simplex weights and their barycenter in the parameter space.

Derived API:
- the faithful `WithTop ℝ` upper-envelope owner `pointwiseSupremumOn`;
- the faithful active-set owner `activePointwiseSupremumOnIndices`;
- the minimax theorem phrased on the canonical `IsMinOn` / `∂[P] f(x)` owners, with
  real-valued lower slices exposed only under explicit bounded-below hypotheses.

Source/core/bridge triage:
- source-facing: `minimax_eq_of_activeSubgradientRepresentation_at_minimizer`;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `IsMinOn`,
  `∂[P] f(x)`, `StdSimplex`;
- bridge/view: the objective bridge
  `(f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x`.

The previous version installed new real-valued public owners
`sectionSupremumOn` / `sectionInfimumOn` by unconditional `Real.sSup` / `Real.sInf`. That loses
the mathematical semantics on empty or unbounded slices. This refinement therefore deletes those
duplicate owners, reuses the faithful chapter owner `pointwiseSupremumOn` on the upper side,
reuses `activePointwiseSupremumOnIndices` for activity, and exposes real-valued lower slices only
through theorem hypotheses that guarantee the relevant slice infima are genuine. -/

section Minimax

variable {X : Type u} {U : Type v} {ι : Type w}

variable [Fintype ι]

variable [SeminormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [AddCommGroup U] [Module ℝ U]

-- Proof sketch: use the constrained subgradient inequality for `gStar` together with the
-- optimality relation `⟪gStar, x - xStar⟫ = 0` on `P`. Rewrite `gStar` as the simplex-weighted sum
-- of the active section subgradients `g i`, combine their section inequalities, and use the
-- barycenter inequality
-- `∑ i, weights.weights i * Ψ(x, u i) ≤ Ψ(x, (Finset.univ).centerMass weights.weights u)` to show
-- that `f xStar ≤ sInf ((fun x ↦ Ψ x uBar) '' P)` for the barycenter parameter
-- `uBar = (Finset.univ).centerMass weights.weights u`. The faithful upper-owner bridge and weak
-- duality then yield the minimax equality `(3.1.78)`.
/-- Theorem 3.1.31: let `f : X → ℝ` be a real-valued objective on `P` whose `WithTop ℝ` lift
agrees with the faithful upper-envelope owner
`pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ))` on `P`. If `xStar` minimizes `f` on `P`,
if some relative subgradient `gStar ∈ ∂_P f(xStar)` satisfying the first-order optimality
relation `⟪gStar, x - xStar⟫ = 0` on `P` admits a simplex representation by active section
subgradients `g i ∈ ∂_P (Ψ(·, u_i))(xStar)`, and if the real lower slices
`x ↦ Ψ(x, u)` are exposed only under bounded-below hypotheses on `P`, then the minimax relation
`(3.1.78)` holds:
`min_{x ∈ P} f(x) = max_{u ∈ S} inf_{x ∈ P} Ψ(x, u)`. -/
theorem minimax_eq_of_activeSubgradientRepresentation_at_minimizer
    {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {f : X → ℝ}
    {xStar gStar : X}
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hxStar_min : IsMinOn f P xStar)
    (hgStar_mem : gStar ∈ ∂[P] f(xStar))
    (horth : ∀ ⦃x : X⦄, x ∈ P → inner ℝ gStar (x - xStar) = 0)
    (weights : StdSimplex ℝ ι)
    (u : ι → U) (g : ι → X)
    (hu_active :
      ∀ i : ι,
        u i ∈ activePointwiseSupremumOnIndices S
          (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar)
    (hg_mem :
      ∀ i : ι, g i ∈ ∂[P] (fun x ↦ Ψ x (u i)) (xStar))
    (hgStar_repr : gStar = ∑ i, weights.weights i • g i)
    (hΨ_bddBelow :
      ∀ ⦃u : U⦄, u ∈ S → BddBelow ((fun x ↦ Ψ x u) '' P))
    (hu_bar_mem :
      (Finset.univ).centerMass weights.weights u ∈ S)
    (hbar_domination :
      ∀ ⦃x : X⦄, x ∈ P →
        (∑ i, weights.weights i * Ψ x (u i)) ≤
          Ψ x ((Finset.univ).centerMass weights.weights u)) :
    sInf (f '' P) =
      sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := by
  -- The constrained-subgradient hypothesis provides the feasibility of the minimizer candidate.
  rw [mem_subdifferentialWithin_iff] at hgStar_mem
  rcases hgStar_mem with ⟨hxStar, -⟩
  have hweights_total : ∑ i, weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  let uBar : U := (Finset.univ).centerMass weights.weights u
  have hsInf_f : sInf (f '' P) = f xStar := by
    exact (hxStar_min.isGLB hxStar).csInf_eq ⟨f xStar, ⟨xStar, hxStar, rfl⟩⟩
  -- Active slices lie in `S` and realize the upper-envelope value at `xStar`.
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
  -- Every feasible slice value at `xStar` lies below the objective value `f xStar`.
  have hslice_le_objective : ∀ ⦃u0 : U⦄, u0 ∈ S → Ψ xStar u0 ≤ f xStar := by
    intro u0 hu0
    have hu0_sup :
        (Ψ xStar u0 : WithTop ℝ) ≤
          pointwiseSupremumOn S (fun x u ↦ (Ψ x u : WithTop ℝ)) xStar := by
      rw [pointwiseSupremumOn_apply]
      refine le_csSup ?_ ?_
      · exact ⟨⊤, fun _ _ ↦ le_top⟩
      · exact ⟨u0, hu0, rfl⟩
    have hu0_sup' : (Ψ xStar u0 : WithTop ℝ) ≤ (f xStar : WithTop ℝ) := by
      simpa [hf_eq hxStar] using hu0_sup
    exact_mod_cast hu0_sup'
  -- Summing the active-slice subgradient inequalities gives a weighted lower bound on the
  -- objective value at every feasible `x`.
  have hobjective_le_barycenter_slice : ∀ ⦃x : X⦄, x ∈ P → f xStar ≤ Ψ x uBar := by
    intro x hx
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
          rw [hweights_total, one_mul]
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
    exact le_trans hobjective_le_weighted (hbar_domination hx)
  -- The barycenter slice has infimum above the optimal objective value.
  have hobjective_le_slice_inf_at_barycenter :
      f xStar ≤ sInf ((fun x ↦ Ψ x uBar) '' P) := by
    refine le_csInf ?_ ?_
    · exact ⟨Ψ xStar uBar, ⟨xStar, hxStar, rfl⟩⟩
    · rintro b ⟨x, hx, rfl⟩
      exact hobjective_le_barycenter_slice hx
  -- Weak duality bounds every lower slice infimum from above by the primal minimum value.
  have hslice_inf_le_objective : ∀ ⦃u0 : U⦄, u0 ∈ S → sInf ((fun x ↦ Ψ x u0) '' P) ≤ f xStar := by
    intro u0 hu0
    exact (csInf_le (hΨ_bddBelow hu0) ⟨xStar, hxStar, rfl⟩).trans (hslice_le_objective hu0)
  have hdual_image_nonempty :
      ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S).Nonempty := by
    exact ⟨sInf ((fun x ↦ Ψ x uBar) '' P), ⟨uBar, hu_bar_mem, rfl⟩⟩
  have hdual_image_bddAbove :
      BddAbove ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := by
    refine ⟨f xStar, ?_⟩
    rintro y ⟨u0, hu0, rfl⟩
    exact hslice_inf_le_objective hu0
  have hobjective_le_dual :
      f xStar ≤ sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := by
    have huBar_lower :
        f xStar ≤ sInf ((fun x ↦ Ψ x uBar) '' P) := hobjective_le_slice_inf_at_barycenter
    exact le_trans huBar_lower (le_csSup hdual_image_bddAbove ⟨uBar, hu_bar_mem, rfl⟩)
  have hdual_le_objective :
      sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) ≤ f xStar := by
    refine csSup_le hdual_image_nonempty ?_
    rintro y ⟨u0, hu0, rfl⟩
    exact hslice_inf_le_objective hu0
  -- Both the primal infimum and the dual supremum are now sandwiched by `f xStar`.
  rw [hsInf_f]
  exact le_antisymm hobjective_le_dual hdual_le_objective

end Minimax

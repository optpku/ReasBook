/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18

-- Declarations for this item will be appended below by the statement pipeline.

open scoped StrongConvexSmooth

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type v} [Fintype ι] [Nonempty ι] {μ L : ℝ}

/- Definition 2.38 lies in the chapter's smooth minimax optimization domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem E` in `Chap01/Definition_1_3_3`, the canonical owner of an
  ambient feasible set together with a real-valued objective;
* `maxTypeObjective` in `Lemma_2_18`, which canonically forms the finite maximum attached to a
  component family;
* `maxTypeAffineApproximation` in `Lemma_2_18`, which canonically forms the affine max-type model
  at a base point;
* `IsStrongConvexSmoothObjective μ L` in `Definition_2_17`, the owner predicate for each
  component function.

Best owner abstraction:
* `SetConstrainedMinimizationProblem E` for the ambient feasible-set/objective pair.

Primitive data:
* the nonempty finite component family `components : ι → E → ℝ` together with
  `components_mem : ∀ i, components i ∈ 𝓢[μ, L]¹¹`;
* the nonempty closed convex feasible set `feasibleSet`.

Derived API:
* the max-type objective `objective`;
* the affine max-type approximation `affineApproximation`;
* the owner bridge `toSetConstrainedMinimizationProblem`;
* the coercion to the ambient objective function.
* existence and uniqueness of a feasible minimizer.

Source/core/bridge triage:
* source-facing: `SmoothMinimaxProblem`;
* core/canonical: `SetConstrainedMinimizationProblem`, `maxTypeObjective`,
  `maxTypeAffineApproximation`;
* bridge/view: `toSetConstrainedMinimizationProblem`. -/

/-- Definition 2.38: a smooth minimax problem with parameters `μ` and `L` consists of a nonempty
closed convex feasible set `Q ⊆ E` on a real Hilbert space together with finitely many component
functions `fᵢ ∈ 𝓢^{1,1}_{μ,L}(E)` indexed by a nonempty finite type `ι`; its objective is the
max-type function `x ↦ max_i fᵢ(x)`, so the problem is `min_{x ∈ Q} max_i fᵢ(x)`. The textbook
`ℝⁿ`/`Fin m` presentation is the specialization `E = EuclideanSpace ℝ (Fin n)` and
`ι = Fin m`. -/
structure SmoothMinimaxProblem
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (ι : Type v) [Fintype ι] [Nonempty ι] (μ L : ℝ) where
  /-- The closed convex feasible set `Q ⊆ E`. -/
  feasibleSet : Set E
  /-- The feasible set is nonempty. -/
  feasible_nonempty : feasibleSet.Nonempty
  /-- The feasible set is closed. -/
  feasible_closed : IsClosed feasibleSet
  /-- The feasible set is convex. -/
  feasible_convex : Convex ℝ feasibleSet
  /-- The component functions whose pointwise maximum defines the minimax objective. -/
  components : ι → E → ℝ
  /-- Each component belongs to the smooth strongly convex class `𝓢^{1,1}_{μ,L}(E)`. -/
  components_mem : ∀ i : ι, components i ∈ 𝓢[μ, L]¹¹

namespace SmoothMinimaxProblem

/-- The objective of a smooth minimax problem is the canonical max-type objective of its
component family. -/
abbrev objective (problem : SmoothMinimaxProblem E ι μ L) : E → ℝ :=
  maxTypeObjective problem.components

/-- The affine max-type approximation of a smooth minimax problem at the base point `xBar`. -/
abbrev affineApproximation (problem : SmoothMinimaxProblem E ι μ L) (xBar : E) : E → ℝ :=
  maxTypeAffineApproximation problem.components xBar

/-- The Chapter 1 owner abstraction attached to a smooth minimax problem. -/
def toSetConstrainedMinimizationProblem
    (problem : SmoothMinimaxProblem E ι μ L) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := problem.feasibleSet
  objective := problem.objective

/-- The owner bridge preserves the textbook feasible set `Q`. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : SmoothMinimaxProblem E ι μ L) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge evaluates to the max-type objective of the component family. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : SmoothMinimaxProblem E ι μ L) (x : E) :
    problem.toSetConstrainedMinimizationProblem x = problem.objective x :=
  rfl

/-- A smooth minimax problem can be used as its objective function. -/
instance : CoeFun (SmoothMinimaxProblem E ι μ L) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a smooth minimax problem returns its max-type objective value. -/
@[simp] theorem coe_apply (problem : SmoothMinimaxProblem E ι μ L) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- Helper for Definition 2.38: the max-type objective of the component family is strongly convex
on the whole ambient space with the common modulus `μ`. -/
lemma objective_strongConvexOn_univ (problem : SmoothMinimaxProblem E ι μ L) :
    StrongConvexOn Set.univ μ problem.objective := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- Each component is `μ`-strongly convex, and the finite maximum preserves the same estimate.
  rw [objective, maxTypeObjective_apply, Finset.sup'_le_iff]
  intro i hi
  have hcomponent : IsStrongConvexSmoothObjective μ L (problem.components i) :=
    mem_S11_iff.mp (problem.components_mem i)
  have hstrong :=
    hcomponent.strongConvexOn.2 (x := x) (y := y) (by simp) (by simp) ha hb hab
  have hstrong' :
      problem.components i (a • x + b • y) ≤
        a * problem.components i x + b * problem.components i y -
          a * b * ((μ / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
    simpa [smul_eq_mul] using hstrong
  have hxmax : problem.components i x ≤ problem.objective x := by
    rw [objective, maxTypeObjective_apply]
    exact Finset.le_sup' (fun j : ι ↦ problem.components j x) (by simp)
  have hymax : problem.components i y ≤ problem.objective y := by
    rw [objective, maxTypeObjective_apply]
    exact Finset.le_sup' (fun j : ι ↦ problem.components j y) (by simp)
  calc
    problem.components i (a • x + b • y)
        ≤ a * problem.components i x + b * problem.components i y -
            a * b * ((μ / 2) * ‖x - y‖ ^ (2 : ℕ)) := hstrong'
    _ ≤ a * problem.objective x + b * problem.objective y -
          a * b * ((μ / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
            gcongr
    _ = a • problem.objective x + b • problem.objective y -
          a * b * ((μ / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
            simp [smul_eq_mul]

/-- Helper for Definition 2.38: the max-type objective is continuous because it is a finite
maximum of `C¹` component functions. -/
lemma objective_continuous (problem : SmoothMinimaxProblem E ι μ L) :
    Continuous problem.objective := by
  classical
  -- Continuity of the finite maximum follows from continuity of each smooth component.
  have hcont :
      Continuous
        (fun x : E ↦
          Finset.univ.sup' Finset.univ_nonempty (fun i : ι ↦ problem.components i x)) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty fun i _ ↦
      (mem_S11_iff.mp (problem.components_mem i)).contDiff.continuous
  simpa [objective, maxTypeObjective_apply] using hcont

/-- Helper for Definition 2.38: a linear term plus the quadratic `μ/2 * ‖u‖²` is bounded below
by the completed-square constant `-‖g‖² / (2 μ)`. -/
lemma inner_add_quadratic_lower_bound
    (μ : ℝ) (hμ : 0 < μ) (g u : E) :
    -(‖g‖ ^ (2 : ℕ)) / (2 * μ) ≤
      inner ℝ g u + (μ / 2) * ‖u‖ ^ (2 : ℕ) := by
  have hnorm : -(‖g‖ * ‖u‖) ≤ inner ℝ g u := by
    -- Cauchy-Schwarz bounds the linear term from below by `-‖g‖ ‖u‖`.
    have hnorm' : -inner ℝ g u ≤ ‖g‖ * ‖u‖ := by
      simpa [inner_neg_left] using (real_inner_le_norm (-g) u)
    linarith
  calc
    -(‖g‖ ^ (2 : ℕ)) / (2 * μ) ≤ -(‖g‖ * ‖u‖) + (μ / 2) * ‖u‖ ^ (2 : ℕ) := by
      -- This is the scalar completed-square inequality `(μ‖u‖ - ‖g‖)^2 ≥ 0`.
      have hsq : 0 ≤ (μ * ‖u‖ - ‖g‖) ^ (2 : ℕ) := sq_nonneg (μ * ‖u‖ - ‖g‖)
      have hμ2 : 0 < 2 * μ := by positivity
      refine (div_le_iff₀ hμ2).2 ?_
      nlinarith
    _ ≤ inner ℝ g u + (μ / 2) * ‖u‖ ^ (2 : ℕ) := by
      gcongr

/-- Helper for Definition 2.38: the feasible objective values are bounded below by evaluating one
component at one feasible base point and completing the square in the tangent inequality. -/
lemma objective_image_bddBelow (problem : SmoothMinimaxProblem E ι μ L) :
    BddBelow (problem.objective '' problem.feasibleSet) := by
  classical
  rcases problem.feasible_nonempty with ⟨x0, hx0⟩
  let i0 : ι := Classical.choice inferInstance
  have hcomponent : IsStrongConvexSmoothObjective μ L (problem.components i0) :=
    mem_S11_iff.mp (problem.components_mem i0)
  have hμ : 0 < μ := hcomponent.mu_pos
  -- A single component lower-bounds the max objective, and its tangent model has a uniform lower
  -- bound after completing the square.
  set g0 : E := gradient (problem.components i0) x0
  let c : ℝ :=
    problem.components i0 x0 - ‖g0‖ ^ (2 : ℕ) / (2 * μ)
  refine ⟨c, ?_⟩
  rintro _ ⟨x, hxQ, rfl⟩
  have hobj_ge : problem.components i0 x ≤ problem.objective x := by
    rw [objective, maxTypeObjective_apply]
    exact Finset.le_sup' (fun j : ι ↦ problem.components j x) (by simp)
  have htan :
      problem.components i0 x ≥
        problem.components i0 x0 +
          inner ℝ g0 (x - x0) +
          (μ / 2) * ‖x - x0‖ ^ (2 : ℕ) :=
    by simpa [g0] using hcomponent.lower_tangent_quadratic x0 x
  have hquad :
      -(‖g0‖ ^ (2 : ℕ)) / (2 * μ) ≤
        inner ℝ g0 (x - x0) +
          (μ / 2) * ‖x - x0‖ ^ (2 : ℕ) :=
    inner_add_quadratic_lower_bound μ hμ _ _
  have hcomp_lower : c ≤ problem.components i0 x := by
    dsimp [c]
    have hraw' :
        problem.components i0 x0 - ‖g0‖ ^ (2 : ℕ) / (2 * μ) ≤
          problem.components i0 x0 +
            inner ℝ g0 (x - x0) +
            (μ / 2) * ‖x - x0‖ ^ (2 : ℕ) := by
      have hsum := add_le_add_left hquad (problem.components i0 x0)
      convert hsum using 1 <;> ring
    exact le_trans hraw' htan
  exact le_trans hcomp_lower hobj_ge

/-- Helper for Definition 2.38: midpoint strong convexity turns two approximate minimizers into a
quantitative distance estimate, which is the Cauchy-sequence core of the existence proof. -/
lemma strongConvexOn_distance_sq_le_of_upper_bounds
    {f : E → ℝ} {Q : Set E} {μ α ε₁ ε₂ : ℝ}
    (hstrong : StrongConvexOn Q μ f)
    {x₁ x₂ : E} (hx₁ : x₁ ∈ Q) (hx₂ : x₂ ∈ Q)
    (hα : α ≤ f ((1 / 2 : ℝ) • x₁ + (1 / 2 : ℝ) • x₂))
    (hx₁_le : f x₁ ≤ α + ε₁) (hx₂_le : f x₂ ≤ α + ε₂) :
    (μ / 8) * ‖x₁ - x₂‖ ^ (2 : ℕ) ≤ (ε₁ + ε₂) / 2 := by
  -- Apply strong convexity at the midpoint and compare both endpoint values with `α`.
  have hmid :
      f ((1 / 2 : ℝ) • x₁ + (1 / 2 : ℝ) • x₂) ≤
        (1 / 2 : ℝ) * f x₁ + (1 / 2 : ℝ) * f x₂ -
          (1 / 2 : ℝ) * (1 / 2 : ℝ) * ((μ / 2) * ‖x₁ - x₂‖ ^ (2 : ℕ)) := by
    simpa using hstrong.2 hx₁ hx₂ (by norm_num) (by norm_num) (by norm_num)
  nlinarith

/-- Helper for Definition 2.38: on a nonempty closed set in a complete real Hilbert space, a
continuous strongly convex function with bounded-below image attains its minimum. -/
lemma exists_isMinOn_of_isClosed_of_complete_of_bddBelow
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hQ_closed : IsClosed Q) (hQ_nonempty : Q.Nonempty)
    (hf_cont : ContinuousOn f Q)
    (hstrong : StrongConvexOn Q μ f) (hμ : 0 < μ)
    (hbdd : BddBelow (f '' Q)) :
    ∃ x : E, x ∈ Q ∧ IsMinOn f Q x := by
  let α : ℝ := sInf (f '' Q)
  have himage_nonempty : (f '' Q).Nonempty := by
    rcases hQ_nonempty with ⟨x, hxQ⟩
    exact ⟨f x, ⟨x, hxQ, rfl⟩⟩
  have hsInf_le : ∀ x ∈ Q, α ≤ f x := by
    intro x hxQ
    exact csInf_le hbdd ⟨x, hxQ, rfl⟩
  have happrox :
      ∀ n : ℕ, ∃ x : E, x ∈ Q ∧ f x < α + 1 / ((n : ℝ) + 1) := by
    intro n
    -- Choose a feasible point whose value is within `1 / (n + 1)` of the infimum `α`.
    have hlt : α < α + 1 / ((n : ℝ) + 1) := by
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    rcases exists_lt_of_csInf_lt himage_nonempty hlt with ⟨y, hy, hylt⟩
    rcases hy with ⟨x, hxQ, rfl⟩
    exact ⟨x, hxQ, hylt⟩
  choose xSeq hxSeq_mem hxSeq_lt using happrox
  have hxSeq_cauchy : CauchySeq xSeq := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have htarget : 0 < (μ / 8) * ε ^ (2 : ℕ) := by
      positivity
    rcases exists_nat_one_div_lt htarget with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hm_div :
        1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      positivity
      exact_mod_cast Nat.succ_le_succ hm
    have hn_div :
        1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      positivity
      exact_mod_cast Nat.succ_le_succ hn
    have hmid_mem :
        ((1 / 2 : ℝ) • xSeq m + (1 / 2 : ℝ) • xSeq n) ∈ Q :=
      hstrong.1 (hxSeq_mem m) (hxSeq_mem n) (by norm_num) (by norm_num) (by norm_num)
    have hdist_sq :
        (μ / 8) * ‖xSeq m - xSeq n‖ ^ (2 : ℕ) ≤
          (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) / 2 :=
      strongConvexOn_distance_sq_le_of_upper_bounds hstrong (hxSeq_mem m) (hxSeq_mem n)
        (hsInf_le _ hmid_mem) (le_of_lt (hxSeq_lt m)) (le_of_lt (hxSeq_lt n))
    have hdist_sq' : ‖xSeq m - xSeq n‖ ^ (2 : ℕ) < ε ^ (2 : ℕ) := by
      have hsmall :
          (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) / 2 <
            (μ / 8) * ε ^ (2 : ℕ) := by
        have hsum :
            (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) / 2 ≤ 1 / ((N : ℝ) + 1) := by
          nlinarith
        exact lt_of_le_of_lt hsum hN
      have hμ8 : 0 < μ / 8 := by positivity
      nlinarith
    have hdist_lt : ‖xSeq m - xSeq n‖ < ε := by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_pos hε] using (sq_lt_sq).mp hdist_sq'
    simpa [dist_eq_norm] using hdist_lt
  obtain ⟨xStar, hxStarQ, hxSeq_tendsto⟩ :=
    cauchySeq_tendsto_of_isComplete hQ_closed.isComplete hxSeq_mem hxSeq_cauchy
  have hxSeq_tendsto_within :
      Filter.Tendsto xSeq Filter.atTop (nhdsWithin xStar Q) :=
    (tendsto_nhdsWithin_iff.2 ⟨hxSeq_tendsto, Filter.Eventually.of_forall hxSeq_mem⟩)
  have hvalues_tendsto :
      Filter.Tendsto (fun n ↦ f (xSeq n)) Filter.atTop (nhds (f xStar)) := by
    -- Continuity on `Q` transfers the convergence of the feasible minimizing sequence.
    have hf_within :
        Filter.Tendsto f (nhdsWithin xStar Q) (nhdsWithin (f xStar) Set.univ) := by
      exact (hf_cont xStar hxStarQ).tendsto_nhdsWithin (by
        intro x hx
        exact Set.mem_univ _)
    have hf_plain : Filter.Tendsto f (nhdsWithin xStar Q) (nhds (f xStar)) := by
      simpa [nhdsWithin_univ] using hf_within
    exact hf_plain.comp hxSeq_tendsto_within
  have hupper_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ α + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds α) := by
    have hfrac_tendsto :
        Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have hsucc :
          Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) Filter.atTop Filter.atTop := by
        exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa [one_div] using tendsto_inv_atTop_zero.comp hsucc
    simpa using hfrac_tendsto.const_add α
  have hvalues_tendsto_alpha :
      Filter.Tendsto (fun n ↦ f (xSeq n)) Filter.atTop (nhds α) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper_tendsto
      (fun n ↦ hsInf_le (xSeq n) (hxSeq_mem n))
      (fun n ↦ le_of_lt (hxSeq_lt n))
  have hxStar_value : f xStar = α :=
    tendsto_nhds_unique hvalues_tendsto hvalues_tendsto_alpha
  refine ⟨xStar, hxStarQ, ?_⟩
  -- Once the objective value equals the infimum `α`, the feasible point is a minimizer.
  rw [isMinOn_iff]
  intro y hyQ
  rw [hxStar_value]
  exact hsInf_le y hyQ

-- Proof sketch: the component hypotheses make the max-type objective `problem.objective`
-- `μ`-strongly convex, so on the nonempty closed feasible set `problem.feasibleSet` the canonical
-- strong-convexity minimizer theorem yields existence and uniqueness.
/-- A smooth minimax problem has a unique feasible minimizer. -/
theorem existsUnique_isMinOn (problem : SmoothMinimaxProblem E ι μ L) :
    ∃! x : E, x ∈ problem.feasibleSet ∧ IsMinOn problem problem.feasibleSet x := by
  have hstrong_univ := objective_strongConvexOn_univ problem
  have hstrong :
      StrongConvexOn problem.feasibleSet μ problem.objective := by
    -- Restrict the whole-space strong convexity estimate to the closed convex feasible set.
    rw [strongConvexOn_iff_convex] at hstrong_univ ⊢
    exact hstrong_univ.subset (by simp) problem.feasible_convex
  have hμ :
      0 < μ := (mem_S11_iff.mp (problem.components_mem (Classical.choice inferInstance))).mu_pos
  obtain ⟨xStar, hxStarQ, hxStarMin⟩ :=
    exists_isMinOn_of_isClosed_of_complete_of_bddBelow
      problem.feasible_closed problem.feasible_nonempty
      (objective_continuous problem).continuousOn
      hstrong hμ (objective_image_bddBelow problem)
  refine ⟨xStar, ?_, ?_⟩
  · simpa [coe_apply] using ⟨hxStarQ, hxStarMin⟩
  · intro y hy
    exact
      (hstrong.strictConvexOn hμ).eq_of_isMinOn
        (by simpa [coe_apply] using hy.2)
        (by simpa [coe_apply] using hxStarMin)
        hy.1 hxStarQ

/- A global minimizer of a smooth minimax problem is expressed directly by the canonical predicate
`IsMinOn problem problem.feasibleSet x`. No additional wrapper declaration is needed. -/

end SmoothMinimaxProblem

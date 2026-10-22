/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_68
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_65
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_62
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped LevelMethodNotation
open scoped NonsmoothModelNotation

/- Definition 3.69 lies in the chapter's level-method / sampled max-affine model domain.

Sampled owner declarations:
- `nonsmoothModel` and `nonsmoothModel_apply` in `Definition_3_65`
- `constrainedEpigraph` in `Definition_3_3`
- `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Definition_3_62`
- `levelMethodHistoryFromApproximateValues` in `Proposition_3_50`
- `LevelMethodHistory.levelValue` in `Lemma_3_3_1`
- `constrainedSublevelSet` in `Definition_3_3`, recalled in `Definition_3_68`
- `IsProjectionPointOn.isMinOn` in `Definition_2_33`

Best owner abstraction:
- the level-method history
  `levelMethodHistoryFromApproximateValues hatf f xSeq`
- the source-facing polyhedron presentation `Q = innerLePolyhedron a b` when the textbook LP/QP
  reformulations are written with explicit affine inequalities

Primitive data:
- the feasible set `Q`
- a finite polyhedron presentation `a`, `b` of `Q` for the LP/QP reformulations
- the objective `f`
- the sample sequence `xSeq`
- the sampled slopes `g`
- the owner model family `fun k ↦ f̂[xSeq; f; g](k)`

Derived API:
- the textbook level value `ℓ_k(α)` as `ℓ[history](α, k)`
- the level set `𝓛_k(α)` as `𝓛[Q, (fun j ↦ f̂[xSeq; f; g](j)), history](α, k)`
- the owner-to-source bridge theorems identifying `constrainedEpigraph` and `𝓛_k(α)` with the
  explicit LP/QP affine-inequality regions obtained from the evaluation bridge for
  `f̂[xSeq; f; g](k)`,
  `mem_innerLePolyhedron_iff`, `constrainedEpigraph`, and `IsProjectionPointOn`

Source/core/bridge triage:
- source-facing: the linear-program and quadratic-program reformulations in Definition 3.69
- core/canonical: `nonsmoothModel`, `levelMethodHistoryFromApproximateValues`,
  `constrainedEpigraph`,
  `constrainedSublevelSet`, `LevelMethodHistory.levelValue`, and `IsProjectionPointOn`
- bridge/view: the explicit sampled-affine inequalities and the epigraph presentation of the
  owner model

Accordingly, this file keeps only the source-facing reformulation theorems. It does not add
parallel public `Set` owners for the explicit LP/QP feasible regions: the canonical owners remain
`constrainedEpigraph` and `constrainedSublevelSet`, and the finite affine-inequality
descriptions are exposed only through bridge theorems.
-/

section

variable (Q : Set E) (f : E → ℝ) (xSeq g : ℕ → E) (hatf : ℕ → ℝ)
variable
  (hhat :
    ∀ k : ℕ,
      ((hatf k : ℝ) : EReal) =
        (levelMethodApproximateProblem Q (fun j ↦ f̂[xSeq; f; g](j)) k).optimalValue)

local notation "model" => fun j ↦ f̂[xSeq; f; g](j)
local notation "history" => (levelMethodHistoryFromApproximateValues hatf f xSeq : LevelMethodHistory)

section PolyhedralPresentation

variable {m : ℕ} (a : Fin m → E) (b : Fin m → ℝ) (hQ : Q = innerLePolyhedron a b)

/-- The owner epigraph of the sampled max-affine model is exactly the textbook linear-program
feasible region with variables `(x, t)` once `Q` is presented as `innerLePolyhedron a b`. -/
-- Proof sketch: rewrite `x ∈ Q` using `hQ` and `mem_innerLePolyhedron_iff`, unfold
-- `constrainedEpigraph`, rewrite `f̂[xSeq; f; g](k) xt.1` using `nonsmoothModel_apply`,
-- and use that a finite maximum is bounded above by `xt.2` exactly when each indexed affine
-- minorant is.
theorem constrainedEpigraph_eq_linearProgramRegion
    (hQ : Q = innerLePolyhedron a b) (k : ℕ) :
    constrainedEpigraph Q (fun x ↦ (model k x : WithTop ℝ)) =
      {xt : E × ℝ |
        (∀ j : Fin m, inner ℝ (a j) xt.1 ≤ b j) ∧
          ∀ i : Fin (k + 1),
            f (xSeq i) + inner ℝ (g i) (xt.1 - xSeq i) ≤ xt.2} := by
  ext xt
  constructor
  · intro hxt
    rcases mem_constrainedEpigraph_iff.mp hxt with ⟨hxQ, hmodel⟩
    refine ⟨?_, ?_⟩
    · -- Rewrite membership in `Q` through the chosen polyhedral presentation.
      simpa [hQ] using hxQ
    · -- Expand the sampled max-affine model into its finite supremum presentation.
      have hmodel_eq :
          model k xt.1 =
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 1) ↦
                f (xSeq i) + inner ℝ (g i) (xt.1 - xSeq i)) := by
        simpa using nonsmoothModel_apply f xSeq g k xt.1
      have hmodel' : model k xt.1 ≤ xt.2 := by
        exact_mod_cast hmodel
      rw [hmodel_eq, Finset.sup'_le_iff] at hmodel'
      intro i
      simpa using hmodel' i (by simp)
  · rintro ⟨hxQ, hminorants⟩
    refine mem_constrainedEpigraph_iff.2 ⟨?_, ?_⟩
    · -- Convert the explicit affine inequalities back to membership in `Q`.
      simpa [hQ] using hxQ
    · -- Reassemble the model inequality from the coordinatewise affine bounds.
      have hmodel_eq :
          model k xt.1 =
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 1) ↦
                f (xSeq i) + inner ℝ (g i) (xt.1 - xSeq i)) := by
        simpa using nonsmoothModel_apply f xSeq g k xt.1
      have hmodel' : model k xt.1 ≤ xt.2 := by
        rw [hmodel_eq, Finset.sup'_le_iff]
        intro i hi
        simpa using hminorants i
      exact_mod_cast hmodel'

/-- The owner level set is exactly the textbook quadratic-program feasible region cut out by the
sampled affine-minorant constraints at the level value `ℓ_k(α)` once `Q` is presented as the
polyhedron `innerLePolyhedron a b`. -/
-- Proof sketch: rewrite `x ∈ Q` using `hQ` and `mem_innerLePolyhedron_iff`, unfold
-- `constrainedSublevelSet`, rewrite `f̂[xSeq; f; g](k) x` using `nonsmoothModel_apply`,
-- and use that a finite maximum is bounded above by `ℓ[history](α, k)` exactly when each
-- indexed term is.
theorem constrainedSublevelSet_eq_quadraticProgramRegion
    (hQ : Q = innerLePolyhedron a b) (α : ℝ) (k : ℕ) :
    𝓛[Q, model, history](α, k) =
      {x : E |
        (∀ j : Fin m, inner ℝ (a j) x ≤ b j) ∧
          ∀ i : Fin (k + 1),
            f (xSeq i) + inner ℝ (g i) (x - xSeq i) ≤
              ℓ[history](α, k)} := by
  ext x
  constructor
  · intro hx
    rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxQ, hmodel⟩
    refine ⟨?_, ?_⟩
    · -- Rewrite membership in `Q` through the fixed polyhedral presentation.
      simpa [hQ] using hxQ
    · -- Expand the sampled max-affine model and read the supremum inequality pointwise.
      have hmodel_eq :
          model k x =
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 1) ↦
                f (xSeq i) + inner ℝ (g i) (x - xSeq i)) := by
        simpa using nonsmoothModel_apply f xSeq g k x
      have hmodel' : model k x ≤ ℓ[history](α, k) := by
        exact_mod_cast hmodel
      rw [hmodel_eq, Finset.sup'_le_iff] at hmodel'
      intro i
      simpa using hmodel' i (by simp)
  · rintro ⟨hxQ, hminorants⟩
    refine mem_constrainedSublevelSet_iff.2 ⟨?_, ?_⟩
    · -- Convert the explicit half-space inequalities back into `x ∈ Q`.
      simpa [hQ] using hxQ
    · -- The coordinatewise affine bounds imply the finite-max model bound.
      have hmodel_eq :
          model k x =
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (k + 1) ↦
                f (xSeq i) + inner ℝ (g i) (x - xSeq i)) := by
        simpa using nonsmoothModel_apply f xSeq g k x
      have hmodel' : model k x ≤ ℓ[history](α, k) := by
        rw [hmodel_eq, Finset.sup'_le_iff]
        intro i hi
        simpa using hminorants i
      exact_mod_cast hmodel'

/-- Helper for Definition 3.69: a real-valued constrained minimization problem with nonempty
feasible set and a lower bound on its feasible objective image has owner optimal value equal to
the coercion of the corresponding real infimum. -/
theorem real_problem_optimalValue_eq_coe_sInf
    {X : Type u} (problem : SetConstrainedMinimizationProblem X)
    (hfeasible : problem.feasibleSet.Nonempty)
    (hbounded : BddBelow (problem '' problem.feasibleSet)) :
    problem.optimalValue = (((sInf (problem '' problem.feasibleSet) : ℝ)) : EReal) := by
  -- Rewrite the owner optimal value as the `EReal` infimum of the feasible objective image.
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  have hsReal :
      IsGLB (problem '' problem.feasibleSet) (sInf (problem '' problem.feasibleSet)) :=
    Real.isGLB_sInf (hfeasible.image fun x ↦ problem x) hbounded
  have hs :
      IsGLB (((↑) : ℝ → EReal) '' (problem '' problem.feasibleSet))
        (((sInf (problem '' problem.feasibleSet) : ℝ)) : EReal) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact_mod_cast hsReal.1 hy
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          rintro rfl
          rcases hfeasible with ⟨x, hx⟩
          have hz_le : (⊤ : EReal) ≤ (problem x : EReal) := by
            exact hz ⟨problem x, ⟨x, hx, rfl⟩, rfl⟩
          simp at hz_le
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : r ≤ sInf (problem '' problem.feasibleSet) := by
          refine le_csInf (hfeasible.image fun x ↦ problem x) ?_
          intro y hy
          exact_mod_cast hz ⟨y, hy, rfl⟩
        exact_mod_cast hr
  have hsNonempty :
      (((↑) : ℝ → EReal) '' (problem '' problem.feasibleSet)).Nonempty := by
    rcases hfeasible with ⟨x, hx⟩
    exact ⟨problem x, ⟨problem x, ⟨x, hx, rfl⟩, rfl⟩⟩
  simpa [Set.image_image] using hs.csInf_eq hsNonempty

/-- Helper for Definition 3.69: minimizing the epigraph height over the constrained epigraph of
the sampled max-affine model gives the same owner optimal value as minimizing the model directly
on `Q`. -/
theorem epigraph_linear_program_optimalValue_eq_approximateProblem
    (k : ℕ) :
    (SetConstrainedMinimizationProblem.mk
      (constrainedEpigraph Q (fun x ↦ (model k x : WithTop ℝ))) Prod.snd).optimalValue =
      (levelMethodApproximateProblem Q model k).optimalValue := by
  let epigraphProblem : SetConstrainedMinimizationProblem (E × ℝ) :=
    .mk (constrainedEpigraph Q (fun x ↦ (model k x : WithTop ℝ))) Prod.snd
  let approximateProblem : SetConstrainedMinimizationProblem E :=
    levelMethodApproximateProblem Q model k
  apply le_antisymm
  · -- Lift each feasible point of the direct problem to the epigraph at height `model k x`.
    rw [approximateProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨x, hxQ, rfl⟩
    have hfeasible :
        (x, model k x) ∈ epigraphProblem.feasibleSet := by
      change (x, model k x) ∈ constrainedEpigraph Q (fun y ↦ (model k y : WithTop ℝ))
      exact mem_constrainedEpigraph_iff.2 ⟨hxQ, le_rfl⟩
    simpa [epigraphProblem] using epigraphProblem.optimalValue_le_of_mem_feasibleSet hfeasible
  · -- Project any epigraph-feasible pair back to `Q` and compare `model k x ≤ t`.
    rw [epigraphProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨xt, hxt, rfl⟩
    change xt ∈ constrainedEpigraph Q (fun y ↦ (model k y : WithTop ℝ)) at hxt
    rcases mem_constrainedEpigraph_iff.mp hxt with ⟨hxQ, hmodel⟩
    have happrox :
        approximateProblem.optimalValue ≤ (approximateProblem xt.1 : EReal) :=
      approximateProblem.optimalValue_le_of_mem_feasibleSet hxQ
    have hmodel' : ((model k xt.1 : ℝ) : EReal) ≤ (xt.2 : EReal) := by
      exact_mod_cast hmodel
    calc
      approximateProblem.optimalValue ≤ (approximateProblem xt.1 : EReal) := happrox
      _ = ((model k xt.1 : ℝ) : EReal) := by rfl
      _ ≤ (xt.2 : EReal) := hmodel'

/-- Helper for Definition 3.69: squaring preserves a distance minimizer because norms are
nonnegative. -/
theorem norm_sq_isMinOn_of_norm_isMinOn
    {S : Set E} {x₀ p : E}
    (hmin : IsMinOn (fun x ↦ ‖x - x₀‖) S p) :
    IsMinOn (fun x ↦ ‖x - x₀‖ ^ (2 : ℕ)) S p := by
  -- Reduce to the pointwise minimizing inequality and square both nonnegative sides.
  rw [isMinOn_iff] at hmin ⊢
  intro y hy
  have hle : ‖p - x₀‖ ≤ ‖y - x₀‖ := hmin y hy
  nlinarith [hle, norm_nonneg (p - x₀), norm_nonneg (y - x₀)]

/-- Definition 3.69 (1): when the model is the finite maximum of the sampled affine minorants,
and `Q` is presented as the polyhedron `innerLePolyhedron a b`, the minimal model value
`\hat f_k^* = history.approximateOptimalValue k` is the optimal value of the linear program
minimizing `t` subject to the polyhedron inequalities and the sampled affine inequalities. -/
-- Proof sketch: by definition, `history.approximateOptimalValue k` is the infimum of
-- `f̂[xSeq; f; g](k)` over `Q`. Rewrite the owner epigraph by
-- `constrainedEpigraph_eq_linearProgramRegion` to obtain the explicit finite
-- affine-inequality feasible region of the textbook linear program.
theorem nonsmoothModelOptimalValue_eq_linearProgramValue
    (hhat :
      ∀ k : ℕ,
        ((hatf k : ℝ) : EReal) =
          (levelMethodApproximateProblem Q (fun j ↦ f̂[xSeq; f; g](j)) k).optimalValue)
    (hQ : Q = innerLePolyhedron a b)
    (k : ℕ) :
    fhat(history, k) =
      sInf
        (Prod.snd ''
          {xt : E × ℝ |
            (∀ j : Fin m, inner ℝ (a j) xt.1 ≤ b j) ∧
              ∀ i : Fin (k + 1),
                f (xSeq i) + inner ℝ (g i) (xt.1 - xSeq i) ≤ xt.2}) := by
  let epigraphProblem : SetConstrainedMinimizationProblem (E × ℝ) :=
    .mk (constrainedEpigraph Q (fun x ↦ (model k x : WithTop ℝ))) Prod.snd
  let linearProgramRegion : Set (E × ℝ) :=
    {xt : E × ℝ |
      (∀ j : Fin m, inner ℝ (a j) xt.1 ≤ b j) ∧
        ∀ i : Fin (k + 1),
          f (xSeq i) + inner ℝ (g i) (xt.1 - xSeq i) ≤ xt.2}
  -- Identify the textbook lower value with the canonical epigraph owner optimal value.
  have hhistory_opt :
      (((fhat(history, k) : ℝ) : EReal) = epigraphProblem.optimalValue) := by
    calc
      (((fhat(history, k) : ℝ) : EReal) =
          (levelMethodApproximateProblem Q model k).optimalValue) := by
        simpa using
          levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
            Q model hatf f xSeq hhat k
      _ = epigraphProblem.optimalValue := by
        symm
        simpa [epigraphProblem] using
          epigraph_linear_program_optimalValue_eq_approximateProblem
            (Q := Q) (f := f) (xSeq := xSeq) (g := g) k
  have hregion :
      epigraphProblem.feasibleSet = linearProgramRegion := by
    simpa [epigraphProblem, linearProgramRegion] using
      constrainedEpigraph_eq_linearProgramRegion
        (Q := Q) (f := f) (xSeq := xSeq) (g := g) (a := a) (b := b) hQ k
  -- A real-valued optimal value forces the explicit LP region to be nonempty.
  have hfeasible : epigraphProblem.feasibleSet.Nonempty := by
    by_contra hEmpty
    have hEmpty' : epigraphProblem.feasibleSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
    have htop : epigraphProblem.optimalValue = (⊤ : EReal) := by
      rw [epigraphProblem.optimalValue_eq_sInf_image, hEmpty']
      simp
    exact (EReal.coe_ne_top (fhat(history, k))) (hhistory_opt.trans htop)
  -- The same real optimal value provides a lower bound on every feasible LP objective value.
  have hbounded : BddBelow (epigraphProblem '' epigraphProblem.feasibleSet) := by
    refine ⟨fhat(history, k), ?_⟩
    rintro _ ⟨xt, hxt, rfl⟩
    have hle : (((fhat(history, k) : ℝ) : EReal) ≤ (epigraphProblem xt : EReal)) := by
      calc
        (((fhat(history, k) : ℝ) : EReal) = epigraphProblem.optimalValue) := hhistory_opt
        _ ≤ (epigraphProblem xt : EReal) :=
          epigraphProblem.optimalValue_le_of_mem_feasibleSet hxt
    simpa [epigraphProblem] using hle
  -- Convert the owner `EReal` optimal value into the real infimum over the explicit LP region.
  have himage :
      epigraphProblem '' epigraphProblem.feasibleSet = Prod.snd '' linearProgramRegion := by
    rw [hregion]
  have hsInf_eq :
      (((fhat(history, k) : ℝ) : EReal) =
        (((sInf (Prod.snd '' linearProgramRegion) : ℝ)) : EReal)) := by
    calc
      (((fhat(history, k) : ℝ) : EReal) = epigraphProblem.optimalValue) := hhistory_opt
      _ = (((sInf (epigraphProblem '' epigraphProblem.feasibleSet) : ℝ)) : EReal) :=
        real_problem_optimalValue_eq_coe_sInf epigraphProblem hfeasible hbounded
      _ = (((sInf (Prod.snd '' linearProgramRegion) : ℝ)) : EReal) := by
        rw [himage]
  exact_mod_cast hsInf_eq

/-- Definition 3.69 (2): if the next iterate is obtained by projecting `x_k` onto the level set
`𝓛_k(α)` and `Q` is presented as the polyhedron `innerLePolyhedron a b`, then `x_{k+1}` minimizes
the
quadratic objective `‖x - x_k‖^2` over the feasible points satisfying the polyhedron inequalities
and the sampled affine-minorant constraints. -/
-- Proof sketch: apply the owner bridge `IsProjectionPointOn.isMinOn` to obtain that
-- `x_{k+1}` minimizes `y ↦ ‖y - x_k‖` on the owner level set
-- `constrainedSublevelSet Q (fun x ↦ (model k x : WithTop ℝ)) (ℓ[history](α, k))`. Then
-- rewrite that set by `constrainedSublevelSet_eq_quadraticProgramRegion`;
-- since norms are nonnegative,
-- squaring preserves the order.
theorem projectionStep_isMinOn_nonsmoothModelQuadraticProgram
    (hQ : Q = innerLePolyhedron a b)
    (α : ℝ) (k : ℕ)
    (hproj :
      IsProjectionPointOn
        (𝓛[Q, model, history](α, k))
        (xSeq k) (xSeq (k + 1))) :
    IsMinOn (fun x ↦ ‖x - xSeq k‖ ^ (2 : ℕ))
      {x : E |
        (∀ j : Fin m, inner ℝ (a j) x ≤ b j) ∧
          ∀ i : Fin (k + 1),
            f (xSeq i) + inner ℝ (g i) (x - xSeq i) ≤
              ℓ[history](α, k)}
      (xSeq (k + 1)) := by
  -- First read the projection hypothesis as distance minimization on the owner level set.
  have hmin_norm :
      IsMinOn (fun x ↦ ‖x - xSeq k‖) (𝓛[Q, model, history](α, k)) (xSeq (k + 1)) :=
    hproj.isMinOn
  have hregion :
      𝓛[Q, model, history](α, k) =
        {x : E |
          (∀ j : Fin m, inner ℝ (a j) x ≤ b j) ∧
            ∀ i : Fin (k + 1),
              f (xSeq i) + inner ℝ (g i) (x - xSeq i) ≤
                ℓ[history](α, k)} := by
    simpa using
      constrainedSublevelSet_eq_quadraticProgramRegion
        (Q := Q) (f := f) (xSeq := xSeq) (g := g) (hatf := hatf)
        (a := a) (b := b) (hQ := hQ) (α := α) (k := k)
  have hmin_region :
      IsMinOn (fun x ↦ ‖x - xSeq k‖)
        {x : E |
          (∀ j : Fin m, inner ℝ (a j) x ≤ b j) ∧
            ∀ i : Fin (k + 1),
              f (xSeq i) + inner ℝ (g i) (x - xSeq i) ≤
                ℓ[history](α, k)}
        (xSeq (k + 1)) := by
    -- Rewrite the owner feasible set into the explicit quadratic-program region.
    simpa [hregion] using
      (show
          IsMinOn (fun x ↦ ‖x - xSeq k‖)
            (𝓛[Q, model, history](α, k))
            (xSeq (k + 1)) from
          hmin_norm)
  -- Match the textbook squared objective using the monotonicity of squaring on `ℝ≥0`.
  exact norm_sq_isMinOn_of_norm_isMinOn hmin_region

end PolyhedralPresentation

end

end

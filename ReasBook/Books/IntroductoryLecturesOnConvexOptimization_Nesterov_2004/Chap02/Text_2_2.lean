/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvex

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Text 2.2: restricting a whole-space `𝓛^1[γ]` owner statement to a convex feasible
set preserves strong convexity with the same modulus. -/
lemma strongConvexOnWith_restrict_univ
    {Q : Set E} {f : E → ℝ} {γ : ℝ}
    (hf : StrongConvexOnWith (normSeminorm ℝ E) γ Set.univ f)
    (hQ_convex : Convex ℝ Q) :
    StrongConvexOnWith (normSeminorm ℝ E) γ Q f := by
  refine ⟨hQ_convex, hf.2.1, ?_⟩
  intro x hx y hy a b ha hb hab
  exact hf.2.2 (by simp) (by simp) ha hb hab

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*}

/-- Helper for Text 2.2: each quadratically regularized component linearization belongs to the
whole-space class `𝓛^1[γ]`. -/
lemma regularized_component_mem_L1
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    ∀ i : ι,
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt (fi i) xBar) γ xBar ∈ 𝓛^1[γ] :=
    by
  intro i
  -- Each component is an affine model plus the centered quadratic penalty.
  change
    StrongConvexOnWith (normSeminorm ℝ E) γ Set.univ
      (quadraticallyRegularizedObjective (firstOrderTaylorModelAt (fi i) xBar) γ xBar)
  rw [strongConvexOnWith_normSeminorm_iff]
  refine ⟨hγ, ?_⟩
  have hsum :
      firstOrderTaylorModelAt (fi i) xBar +
          quadraticallyRegularizedObjective (fun _ : E ↦ 0) γ xBar =
        quadraticallyRegularizedObjective (firstOrderTaylorModelAt (fi i) xBar) γ xBar := by
    -- This identifies the regularized affine model as the sum of its affine and quadratic parts.
    ext x
    simp [quadraticallyRegularizedObjective_apply]
  rw [← hsum]
  -- Strong convexity comes from adding the convex affine model to the strongly convex quadratic.
  exact
    (quadraticallyRegularizedObjective_zero_strongConvexOn xBar γ).add_convexOn
      (firstOrderTaylorModelAt_convexOn Set.univ convex_univ (fi i) xBar)

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Helper for Text 2.2: the regularized max-type model attached to the affine max approximation
at `xBar`. -/
abbrev regularizedAffineMaxModel
    (fi : ι → E → ℝ) (γ : ℝ) :
    E → E → ℝ :=
  fun xBar ↦ quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar

/-- Helper for Text 2.2: the regularized affine max model is `γ`-strongly convex on the ambient
space. -/
lemma regularized_affine_max_strongConvexOn_univ
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) :
    StrongConvexOn (Set.univ : Set E) γ
      (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) := by
  have hsum :
      maxTypeAffineApproximation fi xBar +
          quadraticallyRegularizedObjective (fun _ : E ↦ 0) γ xBar =
        quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar := by
    -- This puts the max-type model into the same affine-plus-quadratic form as the source proof.
    ext x
    simp [quadraticallyRegularizedObjective_apply]
  rw [← hsum]
  -- The affine max part is convex, and the quadratic part contributes the strong convexity
  -- modulus `γ`.
  exact
    (quadraticallyRegularizedObjective_zero_strongConvexOn xBar γ).add_convexOn
      (maxTypeAffineApproximation_convexOn Set.univ convex_univ fi xBar)

/-- Helper for Text 2.2: the regularized affine max model belongs to `𝓛^1[γ]`. -/
lemma regularized_affine_max_mem_L1
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar ∈ 𝓛^1[γ] := by
  change
    StrongConvexOnWith (normSeminorm ℝ E) γ Set.univ
      (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
  rw [strongConvexOnWith_normSeminorm_iff]
  exact ⟨hγ, regularized_affine_max_strongConvexOn_univ fi xBar γ⟩

/-- Helper for Text 2.2: a first-order Taylor model at a fixed base point is continuous. -/
lemma firstOrderTaylorModelAt_continuous
    (f : E → ℝ) (xBar : E) :
    Continuous (firstOrderTaylorModelAt f xBar) := by
  -- The model is a constant plus a continuous linear functional in `x`.
  simpa [firstOrderTaylorModelAt_apply] using
    continuous_const.add
      ((innerSL ℝ (∇ f xBar)).continuous.comp (continuous_id.sub continuous_const))

/-- Helper for Text 2.2: the affine max approximation is continuous as a finite maximum of
continuous affine models. -/
lemma maxTypeAffineApproximation_continuous
    (fi : ι → E → ℝ) (xBar : E) :
    Continuous (maxTypeAffineApproximation fi xBar) := by
  classical
  -- Continuity of the finite maximum follows componentwise from the affine Taylor models.
  have hcont :
      Continuous
        (fun x ↦
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : ι ↦ firstOrderTaylorModelAt (fi i) xBar x)) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty
      (fun i _ ↦ firstOrderTaylorModelAt_continuous (fi i) xBar)
  simpa [maxTypeAffineApproximation] using hcont

/-- Helper for Text 2.2: the regularized affine max model is continuous. -/
lemma regularized_affine_max_continuous
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) :
    Continuous (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) :=
    by
  -- Add continuity of the affine max part to continuity of the quadratic penalty.
  simpa [quadraticallyRegularizedObjective_apply] using
    (maxTypeAffineApproximation_continuous fi xBar).add
      (continuous_const.mul (((continuous_id.sub continuous_const).norm).pow (2 : ℕ)))

/-- Helper for Text 2.2: the constrained regularized affine max subproblem has a unique minimizer
on a nonempty closed convex feasible set. -/
lemma existsUnique_isMinOn_regularized_affine_max
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    ∃! xPlus : E,
      xPlus ∈ Q ∧
        IsMinOn
          (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
          Q
          xPlus := by
  have hL1_univ :
      quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar ∈ 𝓛^1[γ] :=
    regularized_affine_max_mem_L1 fi xBar γ hγ
  have hL1_Q :
      StrongConvexOnWith (normSeminorm ℝ E) γ Q
        (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) :=
    strongConvexOnWith_restrict_univ hL1_univ hQ_convex
  -- Route correction: the earlier single-objective whole-space route is replaced by the actual
  -- constrained max-type model, then the owner existence theorem is applied on `Q`.
  exact
    hL1_Q.existsUnique_isMinOn_of_isClosed
      (regularized_affine_max_continuous fi xBar γ).continuousOn
      hQ_nonempty
      hQ_closed

/-- Helper for Text 2.2: the owner gradient-mapping set of the regularized affine max model has a
unique element. -/
lemma gradientMappingSet_singleton_of_existsUnique_isMinOn
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    ∃! xPlus : E, xPlus ∈ gradientMappingSet Q (regularizedAffineMaxModel fi γ) xBar := by
  -- Rewrite feasible minimizers of the regularized model as membership in `gradientMappingSet`.
  simpa [regularizedAffineMaxModel, mem_gradientMappingSet_iff] using
    existsUnique_isMinOn_regularized_affine_max Q hQ_nonempty hQ_closed hQ_convex fi xBar γ hγ

/-- Text 2.2: for a nonempty closed convex set `Q` and `γ > 0`, the quadratically regularized
max of the affine component linearizations at `xBar` has components in `𝓛^1[γ]` and a unique
feasible minimizer. Equivalently, the owner set `X_f(xBar; γ)` from Definition 2.41 is a
singleton, so the associated gradient mapping is well defined. -/
theorem regularizedAffineMax_gradientMapping_wellDefined
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) (hγ : 0 < γ) :
    (∀ i : ι,
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt (fi i) xBar) γ xBar ∈ 𝓛^1[γ]) ∧
      ∃! xPlus : E, xPlus ∈ gradientMappingSet Q (regularizedAffineMaxModel fi γ) xBar := by
  -- First record the componentwise `𝓛^1[γ]` property from the affine-plus-quadratic structure.
  refine ⟨regularized_component_mem_L1 fi xBar γ hγ, ?_⟩
  -- Then convert the unique constrained minimizer into the singleton owner gradient-mapping set.
  exact
    gradientMappingSet_singleton_of_existsUnique_isMinOn
      Q hQ_nonempty hQ_closed hQ_convex fi xBar γ hγ

end

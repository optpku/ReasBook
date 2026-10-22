/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/-
Theorem 9.8 is a `source-facing` constrained specialization of the Chapter 9 owner theorem
`existsUnique_composite_minimizer_mem_domains`. Its primitive mathematical data are the feasible
set `C`, the dual linear perturbation `a`, the Bregman potential hypothesis on `ω`, and the
intrinsic-interior qualification needed by Lemma 9.7. The source-facing constrained minimization
statement is kept as the main theorem, while the Chapter 3 owner `constrained_problem_objective`
and the Chapter 10 constrained/global minimizer bridge supply the canonical global-objective API
for downstream reuse.
-/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E} {ω : E → EReal} {σ : ℝ}

variable [FiniteDimensional ℝ E]

/-- Helper for Theorem 9.8: the lifted linear functional `x ↦ ((a x : ℝ) : EReal)` is convex. -/
private theorem mirrorDescentLinearObjective_isConvexFunction
    (a : StrongDual ℝ E) :
    is_convex_function (fun x ↦ ((a x : ℝ) : EReal)) := by
  -- A continuous linear functional is affine, hence convex on all of `E`.
  have hlinearConvex : ConvexOn ℝ Set.univ (fun x : E ↦ a x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β hα hβ hαβ
    refine le_of_eq ?_
    simp [smul_eq_mul, map_add]
  exact Function.toEReal_isConvexFunction hlinearConvex

/-- Helper for Theorem 9.8: the constrained linear owner objective has effective domain `C`
because the lifted linear term is finite everywhere. -/
private theorem mirrorDescentLinearObjective_effectiveDomain
    (a : StrongDual ℝ E) :
    effective_domain (constrained_problem_objective (fun x ↦ ((a x : ℝ) : EReal)) C) = C := by
  -- Rewrite the constrained objective domain and simplify the finite linear term.
  rw [effective_domain_constrained_problem_objective]
  ext x
  simp [effective_domain]

/-- Helper for Theorem 9.8: the constrained linear owner objective is lower semicontinuous on `E`
when `C` is closed. -/
private theorem constrainedLinearObjective_lowerSemicontinuous
    (a : StrongDual ℝ E) (hC_closed : IsClosed C) :
    LowerSemicontinuous (constrained_problem_objective (fun x ↦ ((a x : ℝ) : EReal)) C) := by
  -- The lifted linear part is continuous, hence lower semicontinuous.
  have hlinear_closed :
      LowerSemicontinuous (fun x ↦ ((a x : ℝ) : EReal)) :=
    Function.toEReal_lowerSemicontinuous_of_continuous a.continuous
  -- The feasible-set indicator is lower semicontinuous exactly when `C` is closed.
  have hindicator_closed : LowerSemicontinuous (δ_ C) :=
    (extendedIndicator_lowerSemicontinuous_iff_isClosed C).2 hC_closed
  have hindicator_ne_bot : ∀ x : E, (δ_ C) x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ C <;> simp [extendedIndicator, hx]
  have hsum_closed :
      LowerSemicontinuous ((fun x ↦ ((a x : ℝ) : EReal)) + δ_ C) := by
    -- Addition is continuous because the linear term is always finite and the indicator never
    -- takes the value `-∞`.
    refine hlinear_closed.add' hindicator_closed ?_
    intro x
    exact EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))
  -- Rewrite the constrained objective into the canonical `f + δ_C` owner form.
  rw [constrained_problem_objective_eq_add_extendedIndicator
    (fun x ↦ ((a x : ℝ) : EReal)) C (fun _ _ ↦ by simp)]
  simpa [Pi.add_apply] using hsum_closed

/-- Helper for Theorem 9.8: at a feasible point, minimizing the Chapter 9 owner objective
`constrained_problem_objective (fun z ↦ ((a z : ℝ) : EReal)) C + ω` on `Set.univ`
is equivalent to minimizing `x ↦ ((a x : ℝ) : EReal) + ω x` on `C`. -/
private theorem isMinOn_constrainedLinearObjective_add_potential_univ_iff
    (a : StrongDual ℝ E) (hω : IsBregmanPotentialOn ω C σ) {x : E} (hx : x ∈ C) :
    IsMinOn
        (fun y ↦ constrained_problem_objective (fun z ↦ ((a z : ℝ) : EReal)) C y + ω y)
        Set.univ x ↔
      IsMinOn (fun y ↦ ((a y : ℝ) : EReal) + ω y) C x := by
  constructor
  · intro hmin
    rw [isMinOn_iff]
    intro y hy
    -- On feasible points the owner objective and the source-facing objective agree pointwise.
    simpa [constrained_problem_objective_of_mem (fun z ↦ ((a z : ℝ) : EReal)) hx,
      constrained_problem_objective_of_mem (fun z ↦ ((a z : ℝ) : EReal)) hy] using
      (isMinOn_univ_iff.mp hmin) y
  · intro hmin
    rw [isMinOn_univ_iff]
    intro y
    by_cases hy : y ∈ C
    · -- Feasible comparison points reduce to the constrained minimizer inequality.
      simpa [constrained_problem_objective_of_mem (fun z ↦ ((a z : ℝ) : EReal)) hx,
        constrained_problem_objective_of_mem (fun z ↦ ((a z : ℝ) : EReal)) hy] using
        (isMinOn_iff.mp hmin) y hy
    · -- Outside `C` the constrained owner objective is `⊤`, so the inequality is automatic.
      have hy_top :
          constrained_problem_objective (fun z ↦ ((a z : ℝ) : EReal)) C y + ω y = ⊤ := by
        rw [constrained_problem_objective_of_not_mem (fun z ↦ ((a z : ℝ) : EReal)) hy]
        simpa using EReal.top_add_of_ne_bot (hω.toIsProperExtendedRealFunction.ne_bot y)
      calc
        constrained_problem_objective (fun z ↦ ((a z : ℝ) : EReal)) C x + ω x ≤ ⊤ := le_top
        _ = constrained_problem_objective (fun z ↦ ((a z : ℝ) : EReal)) C y + ω y :=
          hy_top.symm

-- Proof sketch: apply Lemma 9.7 to the Chapter 3 constrained objective
-- `constrained_problem_objective (fun x ↦ ((a x : ℝ) : EReal) + ω x) C`, then rewrite its
-- effective domain with `effective_domain_constrained_problem_objective`. The minimizer
-- hypothesis itself supplies the nonempty-domain witness for the constrained objective, so this
-- reusable companion needs only the convexity and Bregman-potential data.
/-- Helper for Theorem 9.8: under the relative-interior qualification needed by Lemma 9.7, a
feasible constrained minimizer of the mirror-descent objective lies in `C ∩ dom(∂ ω)`. -/
theorem mirror_descent_problem_minimizer_mem_domains
    (a : StrongDual ℝ E) (hC_convex : Convex ℝ C) (hω : IsBregmanPotentialOn ω C σ)
    (hqual :
      (intrinsicInterior ℝ C ∩ intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    {xStar : E} (hxC : xStar ∈ C)
    (hxStar : IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + ω x) C xStar) :
    xStar ∈ C ∩ subdifferential_domain ω := by
  let ψ : E → EReal := constrained_problem_objective (fun x ↦ ((a x : ℝ) : EReal)) C
  have hψ_eff : effective_domain ψ = C := by
    simpa [ψ] using mirrorDescentLinearObjective_effectiveDomain (C := C) a
  have hωψ : IsBregmanPotentialOn ω (effective_domain ψ) σ := by
    simpa [hψ_eff] using hω
  have hψ_proper : IsProperExtendedRealFunction ψ := by
    refine ⟨?_, ?_⟩
    · intro x
      dsimp [ψ]
      by_cases hx : x ∈ C <;> simp [constrained_problem_objective, hx]
    · -- The feasible minimizer point supplies the nonempty effective-domain witness.
      refine ⟨xStar, ?_⟩
      simpa [hψ_eff] using hxC
  have hψ_convex : is_convex_function ψ := by
    -- Convexity comes from the finite linear functional and the convex feasible set.
    simpa [ψ] using
      is_convex_function_constrained_problem_objective
        (mirrorDescentLinearObjective_isConvexFunction (E := E) a) hC_convex
  have hxStar_univ : IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar := by
    -- Rewrite the constrained minimizer into the owner global-objective form.
    exact
      (isMinOn_constrainedLinearObjective_add_potential_univ_iff
        (C := C) (ω := ω) (σ := σ) a hω hxC).mpr hxStar
  -- Apply Lemma 9.7 to the constrained linear owner objective.
  simpa [hψ_eff] using
    composite_minimizer_mem_domains hωψ hψ_proper hψ_convex
      (by simpa [hψ_eff] using hqual) hxStar_univ

/-- Helper for Theorem 9.8: the constrained linear owner objective is proper as soon as `C` is
nonempty. -/
private theorem mirrorDescentConstrainedLinearObjective_isProper
    (a : StrongDual ℝ E) (hC_nonempty : C.Nonempty) :
    IsProperExtendedRealFunction
      (constrained_problem_objective (fun x ↦ ((a x : ℝ) : EReal)) C) := by
  constructor
  · -- The constrained linear objective never takes the value `-∞`.
    intro x
    by_cases hx : x ∈ C <;> simp [constrained_problem_objective, hx]
  · -- A feasible point witnesses nonemptiness of the effective domain.
    rcases hC_nonempty with ⟨x0, hx0⟩
    have hψ_eff :
        effective_domain
            (constrained_problem_objective (fun x ↦ ((a x : ℝ) : EReal)) C) = C := by
      simpa using mirrorDescentLinearObjective_effectiveDomain (C := C) a
    refine ⟨x0, ?_⟩
    simpa [hψ_eff] using hx0

/-- Helper for Theorem 9.8: a feasible point of `C` is automatically in the effective domain of
the mirror-descent objective `x ↦ ((a x : ℝ) : EReal) + ω x`. -/
private theorem mirrorDescentObjective_effectiveDomain_nonempty
    (a : StrongDual ℝ E) (hC_nonempty : C.Nonempty) (hω : IsBregmanPotentialOn ω C σ) :
    (C ∩ effective_domain (fun x ↦ ((a x : ℝ) : EReal) + ω x)).Nonempty := by
  rcases hC_nonempty with ⟨x0, hx0⟩
  have hx0ω : x0 ∈ effective_domain ω := hω.subset_effective_domain hx0
  refine ⟨x0, hx0, ?_⟩
  -- The linear term is finite everywhere, so finiteness is inherited from `ω`.
  rw [mem_effective_domain] at hx0ω ⊢
  exact EReal.add_lt_top (EReal.coe_ne_top (a x0)) hx0ω.ne

/-- Helper for Theorem 9.8: global minimizers of the canonical constrained objective are exactly
the feasible minimizers of the source-facing mirror-descent objective. -/
private theorem isMinOn_mirrorDescentConstrainedProblemObjective_iff
    (a : StrongDual ℝ E)
    (hC_dom : (C ∩ effective_domain (fun y ↦ ((a y : ℝ) : EReal) + ω y)).Nonempty)
    {x : E} :
    IsMinOn (constrained_problem_objective (fun y ↦ ((a y : ℝ) : EReal) + ω y) C)
        Set.univ x ↔
      x ∈ C ∧ IsMinOn (fun y ↦ ((a y : ℝ) : EReal) + ω y) C x := by
  -- Rewrite through the Chapter 10 solution-set bridge for `constrained_problem_objective`.
  rw [← mem_unconstrained_problem_solutions_iff]
  rw [unconstrained_problem_solutions_constrained_problem_objective_eq
    (fun y ↦ ((a y : ℝ) : EReal) + ω y) C hC_dom]
  rw [mem_constrained_problem_solutions_iff]

/-- Companion to Theorem 9.8: any minimizer of the constrained mirror-descent objective lies in
the feasible set `C`. -/
theorem mirror_descent_problem_minimizer_mem_feasible_set
    (a : StrongDual ℝ E) (hC_convex : Convex ℝ C) (hω : IsBregmanPotentialOn ω C σ)
    (hqual :
      (intrinsicInterior ℝ C ∩ intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    {xStar : E} (hxC : xStar ∈ C)
    (hxStar : IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + ω x) C xStar) :
    xStar ∈ C :=
  (mirror_descent_problem_minimizer_mem_domains a hC_convex hω hqual hxC hxStar).1

/-- Companion to Theorem 9.8: any minimizer of the constrained mirror-descent objective lies in
`dom(∂ ω)`. -/
theorem mirror_descent_problem_minimizer_mem_subdifferential_domain
    (a : StrongDual ℝ E) (hC_convex : Convex ℝ C) (hω : IsBregmanPotentialOn ω C σ)
    (hqual :
      (intrinsicInterior ℝ C ∩ intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    {xStar : E} (hxC : xStar ∈ C)
    (hxStar : IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + ω x) C xStar) :
    xStar ∈ subdifferential_domain ω :=
  (mirror_descent_problem_minimizer_mem_domains a hC_convex hω hqual hxC hxStar).2

-- Proof sketch: apply Lemma 9.7 to
-- the Chapter 3 constrained objective attached to `x ↦ ((a x : ℝ) : EReal) + ω x`; equivalently,
-- this is `((a · : ℝ) : EReal) + δ_C` added to `ω`. The feasible set hypotheses make the
-- constrained objective proper, closed, and convex, and the relative-interior qualification lets
-- Lemma 9.7 upgrade the minimizer into `dom(∂ ω)`. The constrained/global minimizer bridge then
-- rewrites that result back to minimization over `C`.
/-- Theorem 9.8: if `C` is nonempty, closed, and convex, `ω` is a Bregman potential on `C`, and
`intrinsicInterior ℝ C ∩ intrinsicInterior ℝ (effective_domain ω)` is nonempty, then for every
dual vector `a`, the constrained problem `min_{x ∈ C} {⟨a, x⟩ + ω(x)}` has a unique minimizer,
and that minimizer lies in `C ∩ dom(∂ ω)`. -/
theorem existsUnique_mirror_descent_problem_minimizer_mem_domains
    (a : StrongDual ℝ E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hω : IsBregmanPotentialOn ω C σ)
    (hqual :
      (intrinsicInterior ℝ C ∩ intrinsicInterior ℝ (effective_domain ω)).Nonempty) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + ω x) C xStar ∧
        xStar ∈ C ∩ subdifferential_domain ω := by
  let ψ : E → EReal := constrained_problem_objective (fun x ↦ ((a x : ℝ) : EReal)) C
  have hψ_eff : effective_domain ψ = C := by
    simpa [ψ] using mirrorDescentLinearObjective_effectiveDomain (C := C) a
  have hωψ : IsBregmanPotentialOn ω (effective_domain ψ) σ := by
    -- Transport the Bregman-potential hypothesis across the identified effective domain.
    simpa [hψ_eff] using hω
  have hψ_proper : IsProperExtendedRealFunction ψ := by
    -- Properness is the only new owner side condition for Lemma 9.7.
    simpa [ψ] using mirrorDescentConstrainedLinearObjective_isProper (C := C) a hC_nonempty
  have hψ_closed : LowerSemicontinuous ψ := by
    -- Closedness comes from lower semicontinuity of the constrained linear objective.
    simpa [ψ] using constrainedLinearObjective_lowerSemicontinuous (C := C) a hC_closed
  have hψ_convex : is_convex_function ψ := by
    -- Convexity is inherited from the linear functional and the convex feasible set.
    simpa [ψ] using
      is_convex_function_constrained_problem_objective
        (mirrorDescentLinearObjective_isConvexFunction (E := E) a) hC_convex
  rcases existsUnique_composite_minimizer_mem_domains hωψ hψ_proper hψ_closed hψ_convex
      (by simpa [hψ_eff] using hqual) with
    ⟨xStar, hxStar, huniq⟩
  refine ⟨xStar, ?_, ?_⟩
  · have hxStarC : xStar ∈ C := by
      simpa [hψ_eff] using hxStar.2.1
    -- Rewrite the owner minimizer back to the textbook constrained minimizer statement.
    refine ⟨?_, ?_⟩
    · exact
        (isMinOn_constrainedLinearObjective_add_potential_univ_iff
          (C := C) (ω := ω) (σ := σ) a hω hxStarC).mp hxStar.1
    · simpa [hψ_eff] using hxStar.2
  · intro y hy
    have hy_univ :
        IsMinOn (fun x ↦ ψ x + ω x) Set.univ y := by
      -- Push any competing constrained minimizer back to the owner problem.
      exact
        (isMinOn_constrainedLinearObjective_add_potential_univ_iff
          (C := C) (ω := ω) (σ := σ) a hω hy.2.1).mpr hy.1
    apply huniq
    exact ⟨hy_univ, by simpa [hψ_eff] using hy.2⟩

-- Proof sketch: use the Chapter 10 owner-level constrained/global minimizer bridge for
-- `constrained_problem_objective` at the mirror-descent objective
-- `x ↦ ((a x : ℝ) : EReal) + ω x`.
/-- Companion to Theorem 9.8: the same unique minimizer globally minimizes the canonical
Chapter 3 constrained objective associated to `x ↦ ((a x : ℝ) : EReal) + ω x`. -/
theorem existsUnique_mirror_descent_constrained_problem_objective_minimizer_mem_domains
    (a : StrongDual ℝ E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hω : IsBregmanPotentialOn ω C σ)
    (hqual :
      (intrinsicInterior ℝ C ∩ intrinsicInterior ℝ (effective_domain ω)).Nonempty) :
    ∃! xStar : E,
      IsMinOn (constrained_problem_objective (fun x ↦ ((a x : ℝ) : EReal) + ω x) C)
          Set.univ xStar ∧
        xStar ∈ C ∩ subdifferential_domain ω := by
  let f : E → EReal := fun x ↦ ((a x : ℝ) : EReal) + ω x
  have hC_dom : (C ∩ effective_domain f).Nonempty := by
    -- A feasible point of `C` is automatically feasible for the mirror-descent objective.
    simpa [f] using mirrorDescentObjective_effectiveDomain_nonempty
      (C := C) (ω := ω) (σ := σ) a hC_nonempty hω
  rcases existsUnique_mirror_descent_problem_minimizer_mem_domains
      (C := C) (ω := ω) (σ := σ) a hC_nonempty hC_closed hC_convex hω hqual with
    ⟨xStar, hxStar, huniq⟩
  refine ⟨xStar, ?_, ?_⟩
  · -- Transport the source-facing minimizer to the owner constrained objective.
    refine ⟨?_, hxStar.2⟩
    exact
      (isMinOn_mirrorDescentConstrainedProblemObjective_iff
        (C := C) (ω := ω) a hC_dom).mpr ⟨hxStar.2.1, hxStar.1⟩
  · intro y hy
    have hy_source :
        y ∈ C ∧ IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + ω x) C y := by
      -- Pull any owner minimizer back to the source-facing constrained problem.
      exact
        (isMinOn_mirrorDescentConstrainedProblemObjective_iff
          (C := C) (ω := ω) a hC_dom).mp hy.1
    apply huniq
    exact ⟨hy_source.2, hy.2⟩

end

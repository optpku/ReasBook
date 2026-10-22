/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u v

variable {X : Type u} {U : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
variable [TopologicalSpace U] [AddCommMonoid U] [Module ℝ U]

/-- Helper for Lemma 3.22: a real-valued objective whose `WithTop` lift is closed and convex on a
nonempty feasible set, and whose constrained sublevel sets are all bounded, attains a feasible
minimum on that set. -/
-- Proof sketch: choose one feasible reference point and minimize the objective on its constrained
-- sublevel slice. That slice is nonempty, closed, and bounded, hence compact in the proper space.
-- Lower semicontinuity on the slice gives a minimizer there, and any feasible point outside the
-- slice has larger objective value than the slice threshold.
lemma exists_isMinOn_of_closedConvexOn_bounded_sublevels
    {Q : Set X} (hQ_nonempty : Q.Nonempty) {f : X → ℝ}
    (hf : ClosedConvexOn Q (fun x ↦ (f x : WithTop ℝ)))
    (hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet Q (fun x ↦ (f x : WithTop ℝ)) α)) :
    ∃ x ∈ Q, IsMinOn f Q x := by
  let β₀ : ℝ := f hQ_nonempty.some
  let S : Set X := constrainedSublevelSet Q (fun x ↦ (f x : WithTop ℝ)) β₀
  have hsome_memS : hQ_nonempty.some ∈ S := by
    -- The reference feasible point lies in its own constrained sublevel slice.
    refine mem_constrainedSublevelSet_iff.2 ?_
    exact ⟨hQ_nonempty.some_mem, le_rfl⟩
  have hS_subset : S ⊆ Q := by
    -- Membership in the constrained sublevel set already records feasibility.
    intro x hx
    exact (mem_constrainedSublevelSet_iff.mp hx).1
  have hS_closed : IsClosed S := by
    -- Closed convexity of the lifted objective gives closedness of every constrained sublevel set.
    simpa [S, β₀] using hf.isClosed_constrainedSublevelSet β₀
  have hS_convex : Convex ℝ S := by
    -- The same lifted owner also provides convexity of the slice.
    simpa [S, β₀] using hf.convex_constrainedSublevelSet β₀
  have hS_bounded : Bornology.IsBounded S := by
    -- The bounded-sublevel hypothesis applies directly at the reference value `β₀`.
    simpa [S, β₀] using hbounded β₀
  have hS_compact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  have hS_nonempty : S.Nonempty := ⟨hQ_nonempty.some, hsome_memS⟩
  have hfS : ClosedConvexOn S (fun x ↦ (f x : WithTop ℝ)) :=
    hf.restrict hS_closed hS_convex hS_subset
  have hlscS : LowerSemicontinuousOn f S :=
    hfS.lowerSemicontinuousOn_real hS_closed
  obtain ⟨x, hxS, hxMinS⟩ := hlscS.exists_isMinOn hS_nonempty hS_compact
  have hxQ : x ∈ Q := hS_subset hxS
  have hxβ : f x ≤ β₀ := by
    exact_mod_cast (mem_constrainedSublevelSet_iff.mp hxS).2
  have hxMinQ : IsMinOn f Q x := by
    -- Points inside `S` are handled by compact-slice minimality; points outside have value above
    -- the slice threshold `β₀`, which already dominates `f x`.
    intro y hyQ
    by_cases hyS : y ∈ S
    · exact hxMinS hyS
    · have hy_not_le : ¬ f y ≤ β₀ := by
        intro hyβ
        exact hyS (mem_constrainedSublevelSet_iff.2 ⟨hyQ, by exact_mod_cast hyβ⟩)
      exact le_trans hxβ (le_of_lt (lt_of_not_ge hy_not_le))
  exact ⟨x, hxQ, hxMinQ⟩

/-- Helper for Lemma 3.22: the pointwise maximum of the `u`- and `uStar`-slices inherits the
closed-convex owner structure on `P`. -/
-- Proof sketch: apply the chapter closure rule `ClosedConvexOn.max_inter` to the two primal
-- slices and simplify the resulting `sup` to the real-valued maximum.
lemma parametric_maximum_closed_convex_on
    {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {uStar u : U}
    (hΨ_primal_closedConvex :
      ∀ ⦃w : U⦄, w ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x w : WithTop ℝ)))
    (huStar_mem : uStar ∈ S) (hu : u ∈ S) :
    ClosedConvexOn P (fun x ↦ ((max (Ψ x u) (Ψ x uStar) : ℝ) : WithTop ℝ)) := by
  -- The pointwise maximum is the `WithTop` supremum of the two lifted slices on the common set `P`.
  change ClosedConvexOn P
    (((fun x ↦ (Ψ x u : WithTop ℝ)) ⊔ fun x ↦ (Ψ x uStar : WithTop ℝ)))
  simpa [Set.inter_self] using
    (ClosedConvexOn.max_inter
      (hΨ_primal_closedConvex hu)
      (hΨ_primal_closedConvex huStar_mem))

/-- Helper for Lemma 3.22: every constrained sublevel set of the two-slice maximum is bounded,
because it sits inside the corresponding `uStar`-slice constrained sublevel set. -/
-- Proof sketch: if `max (Ψ(x,u)) (Ψ(x,uStar)) ≤ α`, then in particular `Ψ(x,uStar) ≤ α`, so the
-- max-sublevel slice is contained in the bounded `uStar`-slice sublevel set.
lemma parametric_maximum_bounded_sublevel_sets
    {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {uStar u : U}
    (hlevel_bounded :
      ∀ ⦃w : U⦄, w ∈ S → ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet P (fun x ↦ (Ψ x w : WithTop ℝ)) α))
    (huStar_mem : uStar ∈ S) :
    ∀ α : ℝ,
      Bornology.IsBounded
        (constrainedSublevelSet P
          (fun x ↦ ((max (Ψ x u) (Ψ x uStar) : ℝ) : WithTop ℝ)) α) := by
  intro α
  refine (hlevel_bounded huStar_mem α).subset ?_
  intro x hx
  rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxP, hxα⟩
  have hxα' : max (Ψ x u) (Ψ x uStar) ≤ α := by
    exact_mod_cast hxα
  refine mem_constrainedSublevelSet_iff.2 ⟨hxP, ?_⟩
  exact_mod_cast (le_trans (le_max_right (Ψ x u) (Ψ x uStar)) hxα')

/-- Helper for Lemma 3.22: the dual closed-concavity owner on `v ↦ -Ψ(x,v)` yields ordinary
concavity of the real-valued dual slice `v ↦ Ψ(x,v)` on `S`. -/
-- Proof sketch: first pass from the lifted owner statement to ordinary convexity of the real part
-- of `v ↦ -Ψ(x,v)`, then use the standard `neg_convexOn_iff` equivalence to recover concavity.
lemma dual_slice_concave_on
    {P : Set X} {S : Set U} {Ψ : X → U → ℝ}
    (hΨ_dual_closedConcave :
      ∀ ⦃x : X⦄, x ∈ P →
        ClosedConvexOn S (fun v ↦ (-Ψ x v : WithTop ℝ)))
    {x : X} (hx : x ∈ P) :
    ConcaveOn ℝ S (fun v ↦ Ψ x v) := by
  have hconv : ConvexOn ℝ S (fun v ↦ -Ψ x v) := by
    simpa [withTopRealPart] using (hΨ_dual_closedConcave hx).convexOn_withTopRealPart
  exact neg_convexOn_iff.mp hconv

/-
Lemma 3.22 lies in the chapter's parametric minimax / convex-analysis domain on a proper real
normed space, with the textbook `ℝⁿ × ℝᵐ` statement recovered by specialization.

Sampled owner-style declarations:
- `IsMinOn`
- `ClosedConvexOn.convex`
- `ClosedConvexOn.max_inter`
- `IsMaxOn`

Best owner abstraction:
- source-facing: the attained minimum of the two-slice maximum
  `x ↦ max (Ψ x u) (Ψ x uStar)` and its identification with the lower value
  `sInf ((fun x ↦ Ψ x uStar) '' P)` at a maximizing parameter
- core/canonical: the slice-infimum expression justified by the primal-slice hypotheses,
  the closed-convex two-function max owner `ClosedConvexOn.max_inter`,
  and the two-function minimax owner
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view: the coercion of the real-valued kernel `Ψ` to `WithTop ℝ` inside the slice
  closed-convexity and bounded-sublevel hypotheses

Primitive data:
- the feasible set `P`
- the parameter set `S`
- the real-valued kernel `Ψ`
- nonemptiness of `P`, which lets one extract any dual slice and recover `Convex ℝ S` from the
  owner theorem `ClosedConvexOn.convex`
- the closed-convexity of each primal slice `x ↦ Ψ x u` on `P`
- the boundedness of the constrained sublevel sets of each primal slice
- the closed-concavity of each dual slice `u ↦ Ψ x u` on `S`, encoded through
  `u ↦ -Ψ x u`
- the canonical maximizing-parameter datum
  `uStar ∈ S ∧ IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar`

Derived API:
- the real-valued two-slice maximum `x ↦ max (Ψ x u) (Ψ x uStar)`
- the feasible attained minimizer supplied by the theorem below

Source/core/bridge triage:
- source-facing: Lemma 3.22 itself, expressed for a real-valued convex-concave kernel
- core/canonical: `IsMinOn` and the Chapter 3 closed-convex minimizer-existence
  owners above
- bridge/view: the internal `WithTop` lift used to apply those owners

The previous version kept duplicate public wrappers for the lower value and the two-slice maximum
and overstated the ambient space as an arbitrary real inner-product space. This refinement deletes
that wrapper layer and states the lemma directly in terms of the actual slice-infimum expression
and the source-facing real-valued maximum, while keeping the `WithTop` lift only in the
hypotheses that genuinely use the closed-convex owner API and matching the proper real normed-
space layer of the underlying minimax owner theorem. The textbook `ℝⁿ × ℝᵐ` statement is
recovered by specializing `X` and `U` to Euclidean spaces, using the canonical properness of
finite-dimensional real normed spaces on the primal side.
-/

/-- Lemma 3.22: if every primal slice `x ↦ Ψ(x, u)` is closed and convex on `P` with bounded real
sublevel sets, every dual slice `u ↦ Ψ(x, u)` is closed and concave on `S`, and `uStar` is a
dual-feasible maximizer of the lower value `u ↦ sInf ((fun x ↦ Ψ x u) '' P)` on `S`,
then for every `u ∈ S`
the two-slice maximum `x ↦ max (Ψ(x, u)) (Ψ(x, uStar))` has a feasible minimizer `xBar ∈ P`, and
that minimum value is `sInf ((fun x ↦ Ψ x uStar) '' P)`. The convexity of `S` is recovered from the
dual closed-concavity owner by `ClosedConvexOn.convex`. This owner-level statement lives on the
same proper real normed-space layer as the chapter's minimax-linearization existence theorem. -/
-- Proof sketch: apply `ClosedConvexOn.max_inter` to the two primal slices to keep the source
-- maximum as the public objective, then use
-- `exists_minimax_parameter_of_bounded_constrainedSublevelSets` to replace that maximum by one
-- convex combination of the two slices. Dual concavity and the convexity of `S` compare that
-- convex combination to the slice at `λ u + (1 - λ) uStar`; here `Convex ℝ S` is derived from
-- any witness of `hΨ_dual_closedConcave` using `hP_nonempty` and `ClosedConvexOn.convex`. The
-- proper-space hypotheses on `X` are exactly the owner-level hypotheses needed for that
-- minimax-linearization step. The maximizing property of `uStar` for
-- `u ↦ sInf ((fun x ↦ Ψ x u) '' P)` then gives the reverse inequality,
-- while the bounded sublevel-set
-- hypotheses supply attainment for the relevant slice minima.
-- The lower bound
-- `sInf ((fun x ↦ Ψ x uStar) '' P) ≤ max (Ψ x u) (Ψ x uStar)` is immediate from the `uStar` slice.
theorem exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer
    {P : Set X} (hP_nonempty : P.Nonempty)
    {S : Set U} {Ψ : X → U → ℝ}
    (hΨ_primal_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hlevel_bounded :
      ∀ ⦃u : U⦄, u ∈ S → ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet P (fun x ↦ (Ψ x u : WithTop ℝ)) α))
    (hΨ_dual_closedConcave :
      ∀ ⦃x : X⦄, x ∈ P →
        ClosedConvexOn S (fun v ↦ (-Ψ x v : WithTop ℝ)))
    {uStar u : U}
    (huStar_mem : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar)
    (hu : u ∈ S) :
    ∃ xBar ∈ P,
      IsMinOn (fun x ↦ max (Ψ x u) (Ψ x uStar)) P xBar ∧
        max (Ψ xBar u) (Ψ xBar uStar) = sInf ((fun x ↦ Ψ x uStar) '' P) := by
  let F : X → ℝ := fun x ↦ max (Ψ x u) (Ψ x uStar)
  -- First isolate the `uStar`-slice minimum so the easy lower bound uses an attained value.
  obtain ⟨xStar, hxStar_mem, hxStar_min⟩ :=
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      hP_nonempty
      (hΨ_primal_closedConvex huStar_mem)
      (hlevel_bounded huStar_mem)
  have hvalue_uStar_eq :
      sInf ((fun x ↦ Ψ x uStar) '' P) = Ψ xStar uStar := by
    -- The attained `uStar`-slice minimum identifies the value function with that slice value.
    exact (hxStar_min.isGLB hxStar_mem).csInf_eq ⟨Ψ xStar uStar, ⟨xStar, hxStar_mem, rfl⟩⟩
  have hF_closedConvex :
      ClosedConvexOn P (fun x ↦ (F x : WithTop ℝ)) :=
    parametric_maximum_closed_convex_on hΨ_primal_closedConvex huStar_mem hu
  have hF_bounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet P (fun x ↦ (F x : WithTop ℝ)) α) :=
    parametric_maximum_bounded_sublevel_sets hlevel_bounded huStar_mem
  -- Then attain the minimum of the two-slice maximum by the same compact-sublevel argument.
  obtain ⟨xBar, hxBar_mem, hxBar_min⟩ :=
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      hP_nonempty hF_closedConvex hF_bounded
  have hS_convex : Convex ℝ S :=
    (hΨ_dual_closedConcave hP_nonempty.some_mem).convex
  obtain ⟨lam, hlam⟩ :=
    exists_minimax_parameter_of_bounded_constrainedSublevelSets
      (hΨ_primal_closedConvex hu)
      (hΨ_primal_closedConvex huStar_mem)
      hF_bounded
  let uLam : U := (1 - (lam : ℝ)) • uStar + (lam : ℝ) • u
  let line : X → ℝ := fun x ↦ (1 - (lam : ℝ)) * Ψ x uStar + (lam : ℝ) * Ψ x u
  have huLam_mem : uLam ∈ S := by
    -- Convexity of `S` comes from any dual slice owner, so the affine combination stays feasible.
    simpa [uLam] using
      hS_convex huStar_mem hu (sub_nonneg.mpr lam.2.2) lam.2.1 (by nlinarith)
  obtain ⟨xLam, hxLam_mem, hxLam_min⟩ :=
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      hP_nonempty
      (hΨ_primal_closedConvex huLam_mem)
      (hlevel_bounded huLam_mem)
  have hvalue_uLam_eq :
      sInf ((fun x ↦ Ψ x uLam) '' P) = Ψ xLam uLam := by
    -- The `uLam` slice also attains its lower value on `P`.
    exact (hxLam_min.isGLB hxLam_mem).csInf_eq ⟨Ψ xLam uLam, ⟨xLam, hxLam_mem, rfl⟩⟩
  have hline_le_uLam : ∀ x ∈ P, line x ≤ Ψ x uLam := by
    -- Dual concavity turns the weighted average of the two slice values into the slice value at the
    -- weighted parameter `uLam`.
    intro x hx
    have hconcave : ConcaveOn ℝ S (fun v ↦ Ψ x v) :=
      dual_slice_concave_on hΨ_dual_closedConcave hx
    have hineq :=
      hconcave.2 huStar_mem hu (sub_nonneg.mpr lam.2.2) lam.2.1 (by nlinarith)
    simpa [line, uLam, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using hineq
  have hline_le_F : ∀ x : X, line x ≤ F x := by
    -- Any convex combination of two reals is bounded above by their maximum.
    intro x
    have hleft :
        (1 - (lam : ℝ)) * Ψ x uStar ≤ (1 - (lam : ℝ)) * F x := by
      exact mul_le_mul_of_nonneg_left (le_max_right (Ψ x u) (Ψ x uStar))
        (sub_nonneg.mpr lam.2.2)
    have hright : (lam : ℝ) * Ψ x u ≤ (lam : ℝ) * F x := by
      exact mul_le_mul_of_nonneg_left (le_max_left (Ψ x u) (Ψ x uStar)) lam.2.1
    change (1 - (lam : ℝ)) * Ψ x uStar + (lam : ℝ) * Ψ x u ≤ F x
    nlinarith
  have hminimax :
      sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) =
        sInf (Set.range fun x : P ↦ ((line x : ℝ) : EReal)) := by
    -- The chapter minimax-parameter theorem identifies the max-objective infimum with the
    -- weighted-line infimum on the feasible subtype.
    simpa [F, line, max_def, AffineMap.lineMap_apply_ring, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using
      (isMinimaxLinearizationParameter_iff
        (fun x : P ↦ Ψ x u) (fun x : P ↦ Ψ x uStar) lam).mp hlam
  have hsInf_line_le_value :
      sInf (Set.range fun x : P ↦ ((line x : ℝ) : EReal)) ≤
        (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) := by
    -- Evaluate the weighted line at a minimizing point of the `uLam` slice, then use that `uStar`
    -- maximizes the lower-value function on `S`.
    have hline_mem :
        (((line xLam : ℝ) : EReal)) ∈ Set.range fun x : P ↦ ((line x : ℝ) : EReal) :=
      ⟨⟨xLam, hxLam_mem⟩, rfl⟩
    calc
      sInf (Set.range fun x : P ↦ ((line x : ℝ) : EReal)) ≤ ((line xLam : ℝ) : EReal) :=
        sInf_le hline_mem
      _ ≤ ((Ψ xLam uLam : ℝ) : EReal) := by
        exact_mod_cast hline_le_uLam xLam hxLam_mem
      _ = (((sInf ((fun x ↦ Ψ x uLam) '' P) : ℝ)) : EReal) := by
        exact_mod_cast hvalue_uLam_eq.symm
      _ ≤ (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) := by
        exact_mod_cast huStar_max huLam_mem
  have hvalue_le_hsInf_F :
      (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) ≤
        sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) := by
    -- The `uStar` lower value is a lower bound for every value of the max-objective.
    refine le_sInf ?_
    intro b hb
    rcases hb with ⟨x, rfl⟩
    have hvalue_le_slice :
        sInf ((fun x ↦ Ψ x uStar) '' P) ≤ Ψ x uStar := by
      calc
        sInf ((fun x ↦ Ψ x uStar) '' P) = Ψ xStar uStar := hvalue_uStar_eq
        _ ≤ Ψ x uStar := hxStar_min x.property
    have hvalue_le_F_real :
        sInf ((fun x ↦ Ψ x uStar) '' P) ≤ F x := by
      exact hvalue_le_slice.trans (le_max_right (Ψ x u) (Ψ x uStar))
    have hvalue_le_F_ereal :
        (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) ≤ ((F x : ℝ) : EReal) := by
      exact_mod_cast hvalue_le_F_real
    exact hvalue_le_F_ereal
  have hsInf_F_eq :
      sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) =
        (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) := by
    refine le_antisymm ?_ hvalue_le_hsInf_F
    rw [hminimax]
    exact hsInf_line_le_value
  have hxBar_le_hsInf_F :
      ((F xBar : ℝ) : EReal) ≤ sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) := by
    -- The minimizing point `xBar` is itself a lower bound for the feasible subtype image.
    refine le_sInf ?_
    intro b hb
    rcases hb with ⟨x, rfl⟩
    have hxBar_le_real : F xBar ≤ F x := hxBar_min x.property
    change ((F xBar : ℝ) : EReal) ≤ ((F x : ℝ) : EReal)
    exact_mod_cast hxBar_le_real
  have hsInf_F_le_xBar :
      sInf (Set.range fun x : P ↦ ((F x : ℝ) : EReal)) ≤ ((F xBar : ℝ) : EReal) :=
    sInf_le ⟨⟨xBar, hxBar_mem⟩, rfl⟩
  have hxBar_value :
      ((F xBar : ℝ) : EReal) = (((sInf ((fun x ↦ Ψ x uStar) '' P) : ℝ)) : EReal) := by
    refine le_antisymm ?_ ?_
    · exact hxBar_le_hsInf_F.trans hsInf_F_eq.le
    · exact hsInf_F_eq.symm.le.trans hsInf_F_le_xBar
  refine ⟨xBar, hxBar_mem, ?_, ?_⟩
  · simpa [F] using hxBar_min
  · exact_mod_cast hxBar_value

end

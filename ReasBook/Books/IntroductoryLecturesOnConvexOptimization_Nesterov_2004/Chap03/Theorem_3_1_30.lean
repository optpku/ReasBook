/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_28
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Corollary_3_1_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators WithTopConvexAnalysis

variable {E : Type u} {U : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [ProperSpace U]

/-
Theorem 3 1 30 lies in the chapter's bounded-set minimax / saddle-value existence domain on
proper real normed spaces.

Mandatory domain-style sampling:
- `MaxRepresentationPrimalDualProblem` in `Chap03/Definition_3_28`, the chapter owner for the
  primal feasible set, objective, dual set, kernel, slice geometry, and max-representation data;
- `MaxRepresentationPrimalDualProblem.objective_eq_pointwiseSupremumOn` in
  `Chap03/Definition_3_28`, the canonical bridge from the source max-attainment hypothesis to the
  chapter upper-envelope owner;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project
  owner for the primal infimum value;
- `exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer` in
  `Chap03/Lemma_3_22`, the nearby attainment owner for a maximizing dual parameter.

Best owner abstraction:
- source-facing: the bounded-set minimax equality `(3.1.79)` and the resulting attained dual
  maximizer / primal minimum statement;
- core/canonical: `MaxRepresentationPrimalDualProblem E U` together with the inherited primal
  owner `SetConstrainedMinimizationProblem` and its `optimalValue`;
- bridge/view: `objective_eq_pointwiseSupremumOn`, relating the source objective to the canonical
  upper-envelope owner already stored by the max-representation problem.

Primitive data:
- the primal objective and feasible set, already owned by
  `problem.toSetConstrainedMinimizationProblem`;
- the dual set `problem.dualSet`;
- the kernel `problem.kernel`;
- the slice closed-convex / closed-concave data and the max-attainment representation, already
  primitive fields of `MaxRepresentationPrimalDualProblem`.

Derived API:
- the source minimax equality
  `sInf (problem '' problem.feasibleSet) = sSup ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) ''
    problem.feasibleSet)) '' problem.dualSet)`;
- the Chapter 1 owner equality for
  `problem.toSetConstrainedMinimizationProblem.optimalValue`;
- the attained dual maximizer and primal least-value witness.

Source/core/bridge triage:
- source-facing: the minimax equality and attainment theorem in this file;
- core/canonical: `MaxRepresentationPrimalDualProblem` and
  `SetConstrainedMinimizationProblem.optimalValue`;
- bridge/view: the owner theorem `objective_eq_pointwiseSupremumOn`.

The previous version duplicated the owner data as a raw tuple `{P, S, Ψ, f}` together with
separate slice hypotheses and an `hf_eq` bridge. This refinement deletes that duplicate wheel and
states Theorem 3 1 30 directly for `problem : MaxRepresentationPrimalDualProblem E U`. The primal
nonemptiness hypothesis remains explicit, while dual nonemptiness is now derived from the owner by
`problem.dualSet_nonempty`. The main theorem is the source minimax equality `(3.1.79)` on the
owner layer; the explicit `uStar` / `IsLeast` conclusion is kept only as a companion.
-/

omit [ProperSpace U] in
/-- Helper for Theorem 3 1 30: every feasible dual slice attains its minimum on the bounded primal
feasible set. -/
-- Proof sketch: every constrained sublevel set of the fixed slice sits inside the bounded feasible
-- set, so the compact-sublevel existence theorem from `Lemma_3_22` applies directly.
lemma exists_primal_slice_minimizer_of_bounded_feasibleSet
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    {u : U} (hu : u ∈ problem.dualSet) :
    ∃ x ∈ problem.feasibleSet, IsMinOn (fun z ↦ problem.kernel z u) problem.feasibleSet x := by
  have hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet
            problem.feasibleSet (fun x ↦ (problem.kernel x u : WithTop ℝ)) α) := by
    -- Each slice sublevel set is feasible by definition, hence inherits boundedness from `P`.
    intro α
    exact hfeasible_bounded.subset fun x hx ↦ (mem_constrainedSublevelSet_iff.mp hx).1
  exact
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      hfeasible_nonempty (problem.kernel_primal_closedConvex hu) hbounded

/-- Helper for Theorem 3 1 30: the lower-value function attains a maximizer on the bounded dual
set. -/
-- Proof sketch: write the negative lower-value function as the pointwise supremum of the dual
-- slices `u ↦ -Ψ(x,u)`. Slice minimizers from the previous helper show that this supremum is
-- finite everywhere on `S`, so `ClosedConvexOn.pointwise_sSup` gives closed convexity. Since every
-- constrained sublevel set is a subset of the bounded dual set, minimizing the negative lower
-- value yields a maximizing dual parameter.
lemma exists_dual_value_maximizer_of_bounded_dualSet
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    (hdual_bounded : Bornology.IsBounded problem.dualSet) :
    ∃ uStar ∈ problem.dualSet,
      IsMaxOn (fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet))
        problem.dualSet uStar := by
  let g : U → ℝ := fun u ↦ -sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)
  let Φ : U → E → WithTop ℝ := fun u x ↦ (-problem.kernel x u : WithTop ℝ)
  have hdual_nonempty : problem.dualSet.Nonempty :=
    problem.dualSet_nonempty hfeasible_nonempty.some_mem
  have hpointwise :
      ∀ {u : U}, u ∈ problem.dualSet →
        pointwiseSupremumOn problem.feasibleSet Φ u = (g u : WithTop ℝ) := by
    intro u hu
    obtain ⟨xMin, hxMin, hxMinOn⟩ :=
      exists_primal_slice_minimizer_of_bounded_feasibleSet
        problem hfeasible_nonempty hfeasible_bounded hu
    have hsInf_eq :
        sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet) = problem.kernel xMin u := by
      -- The minimizing primal point identifies the slice infimum with its attained value.
      exact (hxMinOn.isGLB hxMin).csInf_eq ⟨problem.kernel xMin u, ⟨xMin, hxMin, rfl⟩⟩
    have hgreatest :
        IsGreatest ((fun x ↦ Φ u x) '' problem.feasibleSet)
          (((-problem.kernel xMin u : ℝ) : WithTop ℝ)) := by
      -- Negating the minimizing inequality turns the attained minimum into an attained supremum.
      refine ⟨⟨xMin, hxMin, rfl⟩, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      change ((-problem.kernel x u : ℝ) : WithTop ℝ) ≤
        (((-problem.kernel xMin u : ℝ) : WithTop ℝ))
      exact_mod_cast (neg_le_neg (hxMinOn hx))
    calc
      pointwiseSupremumOn problem.feasibleSet Φ u
          = (((-problem.kernel xMin u : ℝ) : WithTop ℝ)) := by
              rw [pointwiseSupremumOn_apply]
              exact hgreatest.csSup_eq
      _ = (g u : WithTop ℝ) := by
        simp [g, hsInf_eq]
  have heffective :
      pointwiseSupremumOnEffectiveDomain problem.dualSet problem.feasibleSet Φ =
        problem.dualSet := by
    ext u
    rw [mem_pointwiseSupremumOnEffectiveDomain_iff]
    constructor
    · exact fun hu ↦ hu.1
    · intro hu
      refine ⟨hu, ?_⟩
      rw [mem_withTopEffectiveDomain_iff, hpointwise hu]
      exact WithTop.coe_lt_top (g u)
  have hsup :
      ClosedConvexOn
        (pointwiseSupremumOnEffectiveDomain problem.dualSet problem.feasibleSet Φ)
        (pointwiseSupremumOn problem.feasibleSet Φ) :=
    ClosedConvexOn.pointwise_sSup hfeasible_nonempty fun x hx ↦
      problem.kernel_dual_closedConcave hx
  have hepigraph :
      constrainedEpigraph problem.dualSet (fun u ↦ (g u : WithTop ℝ)) =
        constrainedEpigraph
          (pointwiseSupremumOnEffectiveDomain problem.dualSet problem.feasibleSet Φ)
          (pointwiseSupremumOn problem.feasibleSet Φ) := by
    ext p
    rw [mem_constrainedEpigraph_iff, mem_constrainedEpigraph_iff]
    constructor
    · rintro ⟨hp, hp₂⟩
      refine ⟨by simpa [heffective] using hp, ?_⟩
      rw [hpointwise hp]
      exact hp₂
    · rintro ⟨hp, hp₂⟩
      have hp' : p.1 ∈ problem.dualSet := by
        simpa [heffective] using hp
      refine ⟨hp', ?_⟩
      rw [hpointwise hp'] at hp₂
      exact hp₂
  have hg_closedConvex :
      ClosedConvexOn problem.dualSet (fun u ↦ (g u : WithTop ℝ)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      exact WithTop.coe_lt_top (g u)
    · simpa [hepigraph] using hsup.2.1
    · simpa [hepigraph] using hsup.2.2
  have hg_bounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet problem.dualSet (fun u ↦ (g u : WithTop ℝ)) α) := by
    -- Every dual sublevel set remains inside the bounded dual domain.
    intro α
    exact hdual_bounded.subset fun u hu ↦ (mem_constrainedSublevelSet_iff.mp hu).1
  obtain ⟨uStar, huStar, hgMin⟩ :=
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      hdual_nonempty hg_closedConvex hg_bounded
  refine ⟨uStar, huStar, ?_⟩
  intro u hu
  -- Negating the minimizing inequality converts it into the desired maximizing inequality.
  have hg_le : g uStar ≤ g u := hgMin hu
  simpa [g] using (neg_le_neg hg_le)

omit [ProperSpace U] in
/-- Helper for Theorem 3 1 30: the bounded primal objective attains a feasible minimizer. -/
-- Proof sketch: apply the same compact-sublevel existence theorem to the represented objective
-- itself; every constrained objective sublevel set is feasible by definition, so boundedness again
-- comes from the ambient bounded feasible set.
lemma exists_primal_objective_minimizer_of_bounded_feasibleSet
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet) :
    ∃ x ∈ problem.feasibleSet, IsMinOn problem problem.feasibleSet x := by
  have hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet
            problem.feasibleSet (fun x ↦ (problem x : WithTop ℝ)) α) := by
    -- Objective sublevel sets stay inside `P`, so the boundedness of `P` controls them as well.
    intro α
    exact hfeasible_bounded.subset fun x hx ↦ (mem_constrainedSublevelSet_iff.mp hx).1
  exact
    exists_isMinOn_of_closedConvexOn_bounded_sublevels
      hfeasible_nonempty problem.objective_closedConvex hbounded

omit [ProperSpace U] in
/-- Helper for Theorem 3 1 30: a maximizing dual parameter gives a pointwise lower bound on the
represented primal objective. -/
-- Proof sketch: at a feasible primal point `x`, choose an active dual parameter realizing
-- `problem x`. Lemma 3.22 then gives a minimizer of the two-slice maximum
-- `max (Ψ(·,u)) (Ψ(·,uStar))` whose value equals the lower value at `uStar`; evaluating the
-- minimizing inequality at `x` turns that value into a lower bound for `problem x`.
lemma lower_value_le_objective_of_dual_value_maximizer
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    {uStar : U} (huStar : uStar ∈ problem.dualSet)
    (huStar_max :
      IsMaxOn (fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet))
        problem.dualSet uStar)
    {x : E} (hx : x ∈ problem.feasibleSet) :
    sInf ((fun z ↦ problem.kernel z uStar) '' problem.feasibleSet) ≤ problem x := by
  rcases (problem.objective_isGreatest hx).1 with ⟨u, hu, hux_eq⟩
  have hlevel_bounded :
      ∀ ⦃w : U⦄, w ∈ problem.dualSet → ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet
            problem.feasibleSet (fun z ↦ (problem.kernel z w : WithTop ℝ)) α) := by
    -- Every slice sublevel set is feasible, hence bounded inside `P`.
    intro w hw α
    exact hfeasible_bounded.subset fun z hz ↦ (mem_constrainedSublevelSet_iff.mp hz).1
  obtain ⟨xBar, hxBar, hxBar_min, hxBar_value⟩ :=
    exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer
      hfeasible_nonempty
      (fun _ hw ↦ problem.kernel_primal_closedConvex hw)
      hlevel_bounded
      (fun _ hz ↦ problem.kernel_dual_closedConcave hz)
      huStar huStar_max hu
  have hvalue_le_max :
      sInf ((fun z ↦ problem.kernel z uStar) '' problem.feasibleSet) ≤
        max (problem.kernel x u) (problem.kernel x uStar) := by
    -- Compare the minimizing two-slice maximum at `xBar` with the same maximum evaluated at `x`.
    calc
      sInf ((fun z ↦ problem.kernel z uStar) '' problem.feasibleSet)
          = max (problem.kernel xBar u) (problem.kernel xBar uStar) := hxBar_value.symm
      _ ≤ max (problem.kernel x u) (problem.kernel x uStar) := hxBar_min hx
  have huStar_le : problem.kernel x uStar ≤ problem x :=
    (problem.objective_isGreatest hx).2 ⟨uStar, huStar, rfl⟩
  calc
    sInf ((fun z ↦ problem.kernel z uStar) '' problem.feasibleSet)
        ≤ max (problem.kernel x u) (problem.kernel x uStar) := hvalue_le_max
    _ = problem x := by
      rw [hux_eq, max_eq_left huStar_le]

omit [ProperSpace U] in
/-- Helper for Theorem 3 1 30: the `uStar`-slice argmin carrier is a nonempty compact set, and on
that carrier the `uStar`-slice value equals the slice infimum. -/
-- Proof sketch: the `uStar`-slice minimizer from the bounded primal set theorem belongs to the
-- constrained sublevel set at the slice infimum, giving nonemptiness. Closedness and boundedness
-- of that constrained sublevel set give compactness, and the infimum property upgrades the
-- defining inequality to equality on the carrier.
lemma uStar_slice_argmin_compact
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    {uStar : U} (huStar : uStar ∈ problem.dualSet) :
    let m := sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)
    let K :=
      constrainedSublevelSet
        problem.feasibleSet (fun x ↦ (problem.kernel x uStar : WithTop ℝ)) m
    IsCompact K ∧ K.Nonempty ∧ ∀ {x}, x ∈ K → problem.kernel x uStar = m := by
  let m := sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)
  let K :=
    constrainedSublevelSet
      problem.feasibleSet (fun x ↦ (problem.kernel x uStar : WithTop ℝ)) m
  obtain ⟨xMin, hxMin, hxMinOn⟩ :=
    exists_primal_slice_minimizer_of_bounded_feasibleSet
      problem hfeasible_nonempty hfeasible_bounded huStar
  have hm_eq : m = problem.kernel xMin uStar := by
    -- The attained slice minimum identifies the real infimum with the minimizing slice value.
    exact (hxMinOn.isGLB hxMin).csInf_eq ⟨problem.kernel xMin uStar, ⟨xMin, hxMin, rfl⟩⟩
  have hK_closed : IsClosed K := by
    -- The carrier is the closed constrained sublevel set of the `uStar` slice.
    simpa [K, m] using (problem.kernel_primal_closedConvex huStar).isClosed_constrainedSublevelSet m
  have hK_bounded : Bornology.IsBounded K := by
    -- Every point of the carrier is feasible, so boundedness comes from the primal feasible set.
    exact hfeasible_bounded.subset fun x hx ↦ (mem_constrainedSublevelSet_iff.mp hx).1
  have hK_compact : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hK_closed hK_bounded
  have hxMin_memK : xMin ∈ K := by
    -- The slice minimizer lies on the infimum level by the previous value identification.
    refine mem_constrainedSublevelSet_iff.2 ⟨hxMin, ?_⟩
    exact_mod_cast hm_eq.symm.le
  refine ⟨hK_compact, ⟨xMin, hxMin_memK⟩, ?_⟩
  intro x hxK
  rcases mem_constrainedSublevelSet_iff.mp hxK with ⟨hxFeasible, hxLe⟩
  have hm_le : m ≤ problem.kernel x uStar := by
    -- Any feasible slice value lies above the attained infimum.
    rw [hm_eq]
    exact hxMinOn hxFeasible
  exact le_antisymm (by exact_mod_cast hxLe) hm_le

omit [ProperSpace E] [ProperSpace U] in
/-- Helper for Theorem 3 1 30: a simplex-weighted average of feasible dual parameters stays in the
dual set, and dual concavity bounds the weighted kernel average by the kernel at that weighted
parameter. -/
-- Proof sketch: use convexity of the dual set to keep the weighted average feasible, then apply
-- Jensen's inequality to the concave dual slice `u ↦ Ψ(x, u)` at the fixed feasible primal point.
lemma weighted_dual_family_le_kernel_of_convex_combination
    {ι : Type*} [Fintype ι]
    (problem : MaxRepresentationPrimalDualProblem E U)
    {x : E} (hx : x ∈ problem.feasibleSet)
    {familyU : ι → U} (hfamilyU : ∀ i, familyU i ∈ problem.dualSet)
    (coeffs : StdSimplex ℝ ι) :
    let uCoeff : U := ∑ i, coeffs.weights i • familyU i
    uCoeff ∈ problem.dualSet ∧
      (∑ i, coeffs.weights i * problem.kernel x (familyU i)) ≤ problem.kernel x uCoeff := by
  let uCoeff : U := ∑ i, coeffs.weights i • familyU i
  have huCoeff_mem : uCoeff ∈ problem.dualSet := by
    -- Convexity of `S` keeps the simplex-weighted combination inside the dual set.
    refine problem.dualSet_convex.sum_mem ?_ ?_ ?_
    · intro i _
      exact coeffs.nonneg i
    · simpa [Finsupp.sum_fintype] using coeffs.total
    · intro i _
      exact hfamilyU i
  have hconv : ConvexOn ℝ problem.dualSet (fun u ↦ -problem.kernel x u) := by
    simpa [withTopRealPart] using (problem.kernel_dual_closedConcave hx).convexOn_withTopRealPart
  have hconcave : ConcaveOn ℝ problem.dualSet (fun u ↦ problem.kernel x u) :=
    neg_convexOn_iff.mp hconv
  have hweighted :
      ∑ i, coeffs.weights i • problem.kernel x (familyU i) ≤ problem.kernel x uCoeff := by
    -- Jensen's inequality for the concave dual slice gives the desired kernel comparison.
    simpa [uCoeff] using
      hconcave.le_map_sum
        (t := Finset.univ)
        (w := coeffs.weights)
        (p := familyU)
        (fun i _ ↦ coeffs.nonneg i)
        (by simpa [Finsupp.sum_fintype] using coeffs.total)
        (fun i _ ↦ hfamilyU i)
  exact ⟨huCoeff_mem, by simpa [smul_eq_mul] using hweighted⟩

omit [ProperSpace U] in
/-- Helper for Theorem 3 1 30: every finite family of dual inequalities is realized on the
compact `uStar`-slice argmin carrier. -/
-- Proof sketch: add `uStar` to the given finite family, minimize the resulting family maximum on
-- the feasible set, and linearize that finite maximum by a simplex-weighted dual combination. The
-- maximizing property of `uStar` forces the attained family-maximum value to be exactly the slice
-- infimum `m`, so the minimizer lies in the `uStar`-argmin carrier and satisfies all requested
-- dual inequalities.
lemma finite_family_sublevel_realization_on_uStar_argmin
    {ι : Type*} [Finite ι] [Nonempty ι]
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    {uStar : U} (huStar : uStar ∈ problem.dualSet)
    (huStar_max :
      IsMaxOn (fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet))
        problem.dualSet uStar)
    {us : ι → U} (hus : ∀ i, us i ∈ problem.dualSet) :
    let m := sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)
    let K :=
      constrainedSublevelSet
        problem.feasibleSet (fun x ↦ (problem.kernel x uStar : WithTop ℝ)) m
    ∃ x ∈ K, ∀ i, problem.kernel x (us i) ≤ m := by
  classical
  -- Local instance justification (typeclass bridge): the finite-family max-type API is stated
  -- for `Fintype`, while this helper only exposes the weaker `Finite` assumption in its type.
  let _ : Fintype ι := Fintype.ofFinite ι
  let m := sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)
  let K :=
    constrainedSublevelSet
      problem.feasibleSet (fun x ↦ (problem.kernel x uStar : WithTop ℝ)) m
  let familyU : Option ι → U := fun
    | none => uStar
    | some i => us i
  let fs : Option ι → E → ℝ := fun j x ↦ problem.kernel x (familyU j)
  have hfamilyU : ∀ j, familyU j ∈ problem.dualSet := by
    intro j
    cases j with
    | none =>
        exact huStar
    | some i =>
        exact hus i
  have hfs : ∀ j, ClosedConvexOn problem.feasibleSet (fun x ↦ (fs j x : WithTop ℝ)) := by
    -- Each family member is one of the primal slices of the kernel.
    intro j
    exact problem.kernel_primal_closedConvex (hfamilyU j)
  have hbounded :
      ∀ α : ℝ,
        Bornology.IsBounded
          (constrainedSublevelSet
            problem.feasibleSet (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α) := by
    -- A family-maximum sublevel point satisfies the `uStar` slice inequality, so it stays inside
    -- the bounded `uStar`-slice sublevel set.
    intro α
    have hsubset :
        constrainedSublevelSet
            problem.feasibleSet (fun x ↦ ((maxTypeObjective fs x : ℝ) : WithTop ℝ)) α ⊆
          constrainedSublevelSet
            problem.feasibleSet (fun x ↦ (problem.kernel x uStar : WithTop ℝ)) α := by
      intro x hx
      rcases mem_constrainedSublevelSet_iff.mp hx with ⟨hxFeasible, hxMax⟩
      refine mem_constrainedSublevelSet_iff.2 ⟨hxFeasible, ?_⟩
      have hxMax' : maxTypeObjective fs x ≤ α := by
        exact_mod_cast hxMax
      exact_mod_cast (maxTypeObjective_le_iff fs x α).mp hxMax' none
    refine
      (hfeasible_bounded.subset fun x hx ↦ (mem_constrainedSublevelSet_iff.mp hx).1).subset
        hsubset
  obtain ⟨xMin, hxMinMin⟩ :=
    exists_isMinOn_familyMaximum_of_bounded_sublevels hfs hbounded hfeasible_nonempty
  obtain ⟨coeffs, hweighted_lower, hweighted_eq⟩ :=
    supporting_coeffs_of_familyMaximum_minimizer xMin hfs hxMinMin
  let uCoeff : U := ∑ j, coeffs.weights j • familyU j
  have huCoeff_mem : uCoeff ∈ problem.dualSet := by
    -- The simplex-weighted family parameter is dual feasible.
    exact
      (weighted_dual_family_le_kernel_of_convex_combination
        problem xMin.property hfamilyU coeffs).1
  have hfamily_value_le_m :
      maxTypeObjective fs xMin ≤ m := by
    -- The linearized family maximum is a lower bound for every feasible point, hence for the
    -- lower value at `uCoeff`, which is bounded above by the maximizing property of `uStar`.
    have hfamily_le_uCoeff :
        ∀ x : problem.feasibleSet,
          maxTypeObjective fs xMin ≤ problem.kernel x uCoeff := by
      intro x
      calc
        maxTypeObjective fs xMin ≤ ∑ j, coeffs.weights j * problem.kernel x (familyU j) :=
          hweighted_lower x
        _ ≤ problem.kernel x uCoeff :=
          (weighted_dual_family_le_kernel_of_convex_combination
            problem x.property hfamilyU coeffs).2
    have hfamily_le_lower :
        maxTypeObjective fs xMin ≤
          sInf ((fun x ↦ problem.kernel x uCoeff) '' problem.feasibleSet) := by
      refine le_csInf (hfeasible_nonempty.image fun x ↦ problem.kernel x uCoeff) ?_
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hfamily_le_uCoeff ⟨x, hx⟩
    exact hfamily_le_lower.trans (huStar_max huCoeff_mem)
  obtain ⟨xStar, hxStar, hxStar_eq⟩ :=
    exists_primal_slice_minimizer_of_bounded_feasibleSet
      problem hfeasible_nonempty hfeasible_bounded huStar
  have hm_eq : m = problem.kernel xStar uStar := by
    -- An attained `uStar`-slice minimum identifies the slice infimum.
    exact (hxStar_eq.isGLB hxStar).csInf_eq ⟨problem.kernel xStar uStar, ⟨xStar, hxStar, rfl⟩⟩
  have hm_le_uStar : m ≤ problem.kernel xMin uStar := by
    -- Every feasible `uStar`-slice value lies above the attained infimum.
    rw [hm_eq]
    exact hxStar_eq xMin.property
  have huStar_le_family :
      problem.kernel xMin uStar ≤ maxTypeObjective fs xMin := by
    -- The family maximum dominates each component, in particular the distinguished `uStar` one.
    exact (maxTypeObjective_le_iff fs xMin (maxTypeObjective fs xMin)).mp le_rfl none
  have hfamily_eq_m : maxTypeObjective fs xMin = m := by
    exact le_antisymm hfamily_value_le_m (hm_le_uStar.trans huStar_le_family)
  have huStar_eq_m : problem.kernel xMin uStar = m := by
    refine le_antisymm ?_ ?_
    · exact huStar_le_family.trans hfamily_eq_m.le
    · exact hm_le_uStar
  have hxMin_memK : (xMin : E) ∈ K := by
    -- Equality on the distinguished `uStar` coordinate places the minimizer on the carrier `K`.
    refine mem_constrainedSublevelSet_iff.2 ⟨xMin.property, ?_⟩
    exact_mod_cast huStar_eq_m.le
  refine ⟨(xMin : E), hxMin_memK, ?_⟩
  intro i
  have hi_le_family : problem.kernel xMin (us i) ≤ maxTypeObjective fs xMin :=
    (maxTypeObjective_le_iff fs xMin (maxTypeObjective fs xMin)).mp le_rfl (some i)
  simpa [hfamily_eq_m] using hi_le_family

omit [ProperSpace U] in
/-- Helper for Theorem 3 1 30: bounded primal and dual sets admit a saddle attainer at a dual
maximizer `uStar`, with primal objective value equal to the attained lower value `m`. -/
-- Proof sketch: intersect the compact `uStar`-slice argmin carrier with the closed sublevel sets
-- `{x ∈ K | Ψ(x, u) ≤ m}` for every dual parameter `u`. The previous finite-family lemma gives
-- the finite intersection property, so compactness yields a common point `xStar`; that point
-- maximizes the dual slice at `uStar`, hence its primal objective equals `m`.
lemma exists_saddle_attainer_of_bounded_sets
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    {uStar : U} (huStar : uStar ∈ problem.dualSet)
    (huStar_max :
      IsMaxOn (fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet))
        problem.dualSet uStar) :
    let m := sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)
    ∃ xStar ∈ problem.feasibleSet,
      problem.kernel xStar uStar = m ∧
        (∀ u ∈ problem.dualSet, problem.kernel xStar u ≤ m) ∧
        problem xStar = m := by
  let m := sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)
  let K :=
    constrainedSublevelSet
      problem.feasibleSet (fun x ↦ (problem.kernel x uStar : WithTop ℝ)) m
  obtain ⟨hK_compact, hK_nonempty, hK_eq⟩ :=
    uStar_slice_argmin_compact problem hfeasible_nonempty hfeasible_bounded huStar
  have hK_closed : IsClosed K := by
    -- The carrier is a closed sublevel set of the `uStar` slice.
    simpa [K, m] using (problem.kernel_primal_closedConvex huStar).isClosed_constrainedSublevelSet m
  have hK_convex : Convex ℝ K := by
    -- The same source slice gives convexity of the carrier.
    simpa [K, m] using (problem.kernel_primal_closedConvex huStar).convex_constrainedSublevelSet m
  have hK_subset : K ⊆ problem.feasibleSet := by
    -- Membership in the constrained sublevel set records feasibility.
    intro x hx
    exact (mem_constrainedSublevelSet_iff.mp hx).1
  let t : problem.dualSet → Set E := fun u =>
    constrainedSublevelSet K (fun x ↦ (problem.kernel x (u : U) : WithTop ℝ)) m
  have htc : ∀ u : problem.dualSet, IsClosed (t u) := by
    -- Restrict each primal slice to the compact carrier `K`.
    intro u
    let hrestrict : ClosedConvexOn K (fun x ↦ (problem.kernel x (u : U) : WithTop ℝ)) :=
      (problem.kernel_primal_closedConvex u.property).restrict hK_closed hK_convex hK_subset
    simpa [t] using hrestrict.isClosed_constrainedSublevelSet m
  have hfinite :
      ∀ a : Finset problem.dualSet, (K ∩ ⋂ u ∈ a, t u).Nonempty := by
    intro a
    by_cases ha : a.Nonempty
    · rcases ha with ⟨a0, ha0⟩
      let us : a → U := fun i ↦ (i : problem.dualSet)
      let _ : Nonempty a := ⟨⟨a0, ha0⟩⟩
      have hus : ∀ i, us i ∈ problem.dualSet := by
        intro i
        exact (i : problem.dualSet).property
      have hrealize :=
        finite_family_sublevel_realization_on_uStar_argmin
          (ι := a) problem hfeasible_nonempty hfeasible_bounded huStar huStar_max hus
      rcases hrealize with ⟨x, hxK, hxineq⟩
      refine ⟨x, ?_⟩
      refine ⟨hxK, ?_⟩
      rw [Set.mem_iInter]
      intro u
      rw [Set.mem_iInter]
      intro hu
      refine mem_constrainedSublevelSet_iff.2 ⟨hxK, ?_⟩
      simpa [t, us] using hxineq ⟨u, hu⟩
    · rcases hK_nonempty with ⟨x, hxK⟩
      refine ⟨x, ?_⟩
      refine ⟨hxK, ?_⟩
      rw [Set.mem_iInter]
      intro u
      rw [Set.mem_iInter]
      intro hu
      exact False.elim (ha ⟨u, hu⟩)
  obtain ⟨xStar, hxStarK, hxStarAll⟩ :=
    hK_compact.inter_iInter_nonempty t htc hfinite
  have hxStar_feasible : xStar ∈ problem.feasibleSet := hK_subset hxStarK
  have hkernel_eq : problem.kernel xStar uStar = m := hK_eq hxStarK
  have hall : ∀ u ∈ problem.dualSet, problem.kernel xStar u ≤ m := by
    -- Membership in each restricted sublevel set gives the requested dual inequalities.
    intro u hu
    have hxStar_mem : xStar ∈ t ⟨u, hu⟩ := (Set.mem_iInter.mp hxStarAll) ⟨u, hu⟩
    exact_mod_cast (mem_constrainedSublevelSet_iff.mp hxStar_mem).2
  have huStar_isMax :
      IsMaxOn (problem.kernel xStar) problem.dualSet uStar := by
    -- The common point satisfies `Ψ(xStar, u) ≤ m = Ψ(xStar, uStar)` for every feasible `u`.
    intro u hu
    calc
      problem.kernel xStar u ≤ m := hall u hu
      _ = problem.kernel xStar uStar := hkernel_eq.symm
  have hobjective_eq :
      problem xStar = m := by
    -- At a dual-slice maximizer, the represented objective equals the active kernel value.
    rw [problem.objective_eq_kernel_of_isMaxOn hxStar_feasible ⟨uStar, huStar⟩ huStar_isMax]
    exact hkernel_eq
  exact ⟨xStar, hxStar_feasible, hkernel_eq, hall, hobjective_eq⟩

/-- Helper for Theorem 3 1 30: bounded feasible and dual sets admit a dual maximizer whose lower
value is the least feasible primal objective value. -/
-- Route correction: the dual maximizer is already available from
-- `exists_dual_value_maximizer_of_bounded_dualSet`. The remaining source-faithful step is the
-- finite-family/FIP argument producing a primal point on the `uStar`-slice argmin set that
-- satisfies all dual inequalities simultaneously.
lemma exists_primal_dual_value_witness_of_bounded_sets
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    (hdual_bounded : Bornology.IsBounded problem.dualSet) :
    ∃ uStar ∈ problem.dualSet,
      IsMaxOn (fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet))
        problem.dualSet uStar ∧
        IsLeast (problem '' problem.feasibleSet)
          (sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)) := by
  obtain ⟨uStar, huStar, huStar_max⟩ :=
    exists_dual_value_maximizer_of_bounded_dualSet
      problem hfeasible_nonempty hfeasible_bounded hdual_bounded
  obtain ⟨xStar, hxStar, _, _, hobjective_eq⟩ :=
    exists_saddle_attainer_of_bounded_sets
      problem hfeasible_nonempty hfeasible_bounded huStar huStar_max
  refine ⟨uStar, huStar, huStar_max, ?_⟩
  refine ⟨⟨xStar, hxStar, hobjective_eq⟩, ?_⟩
  intro y hy
  -- Weak duality at the maximizing parameter supplies the lower bound for every feasible value.
  rcases hy with ⟨z, hz, rfl⟩
  exact
    lower_value_le_objective_of_dual_value_maximizer
      problem hfeasible_nonempty hfeasible_bounded huStar huStar_max hz

/-- Theorem 3 1 30: for a bounded max-representation primal-dual problem on proper real normed
spaces, if the primal feasible set is nonempty and both the primal feasible set and dual set are
bounded, then the primal minimum equals the dual maximum:
`min_{x ∈ P} f(x) = max_{u ∈ S} inf_{x ∈ P} Ψ(x, u)`.

Here the data `P`, `S`, `Ψ`, and `f` are carried canonically by
`problem : MaxRepresentationPrimalDualProblem E U`, rather than repeated as separate tuple
arguments. -/
-- Proof sketch: use the owner fields of `problem` to recover the slice closed-convex and
-- closed-concave hypotheses needed in the bounded minimax existence argument. Boundedness and
-- properness give an attained maximizing parameter `uStar` for the lower-value function
-- `u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)`; the Chapter 3 bridge in
-- `Definition_3_28` identifies the primal objective with the canonical upper envelope. The
-- resulting saddle-value identity yields the displayed minimax equality.
theorem minimax_eq_of_bounded_maxRepresentationPrimalDualProblem
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    (hdual_bounded : Bornology.IsBounded problem.dualSet) :
    sInf (problem '' problem.feasibleSet) =
      sSup ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)) ''
        problem.dualSet) := by
  obtain ⟨uStar, huStar, huStar_max, hleast⟩ :=
    exists_primal_dual_value_witness_of_bounded_sets
      problem hfeasible_nonempty hfeasible_bounded hdual_bounded
  have hgreatest :
      IsGreatest
        ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)) ''
          problem.dualSet)
        (sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)) := by
    -- The maximizing dual parameter realizes the supremum of the lower-value image.
    refine ⟨⟨uStar, huStar, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    exact huStar_max hu
  calc
    sInf (problem '' problem.feasibleSet)
        = sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet) := hleast.csInf_eq
    _ = sSup ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)) ''
          problem.dualSet) := hgreatest.csSup_eq.symm

/-- Owner-value bridge for Theorem 3 1 30: the same minimax equality written with the canonical
Chapter 1 optimal-value owner on the primal side. -/
-- Proof sketch: combine
-- `exists_dual_maximizer_with_primal_minimum_of_bounded_sets` with
-- `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, or equivalently coerce the
-- real-valued equality above to `EReal` after identifying the attained primal minimum.
theorem optimalValue_eq_dualValue_of_bounded_maxRepresentationPrimalDualProblem
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    (hdual_bounded : Bornology.IsBounded problem.dualSet) :
    problem.toSetConstrainedMinimizationProblem.optimalValue =
      (sSup ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)) ''
        problem.dualSet) : EReal) := by
  obtain ⟨uStar, huStar, huStar_max, hleast⟩ :=
    exists_primal_dual_value_witness_of_bounded_sets
      problem hfeasible_nonempty hfeasible_bounded hdual_bounded
  rcases hleast with ⟨⟨xStar, hxStar, hxValue⟩, hleast_bound⟩
  have hxStar_min : IsMinOn problem problem.feasibleSet xStar := by
    -- The least-value witness exactly says that `xStar` minimizes the primal objective.
    intro y hy
    have hm_le : sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet) ≤ problem y :=
      hleast_bound ⟨y, hy, rfl⟩
    simpa [hxValue] using hm_le
  have hopt :
      problem.toSetConstrainedMinimizationProblem.optimalValue = (problem xStar : EReal) :=
    problem.optimalValue_eq_of_isMinOn hxStar hxStar_min
  have hgreatest :
      IsGreatest
        ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)) ''
          problem.dualSet)
        (sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)) := by
    -- The maximizing dual parameter realizes the dual supremum as an actual greatest element.
    refine ⟨⟨uStar, huStar, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    exact huStar_max hu
  have hdual_value_coe_eq :
      ∀ {u : U}, u ∈ problem.dualSet →
        (((sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet) : ℝ)) : EReal) =
          sInf ((fun x ↦ (problem.kernel x u : EReal)) '' problem.feasibleSet) := by
    intro u hu
    obtain ⟨xMin, hxMin, hxMinOn⟩ :=
      exists_primal_slice_minimizer_of_bounded_feasibleSet
        problem hfeasible_nonempty hfeasible_bounded hu
    have hsReal :
        sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet) = problem.kernel xMin u := by
      -- The bounded feasible set gives an attained real slice minimum.
      exact (hxMinOn.isGLB hxMin).csInf_eq ⟨problem.kernel xMin u, ⟨xMin, hxMin, rfl⟩⟩
    have hxMinOnEReal :
        IsMinOn (fun z ↦ (problem.kernel z u : EReal)) problem.feasibleSet xMin := by
      -- The same point minimizes the coerced `EReal` slice because coercion preserves order.
      rw [isMinOn_iff] at hxMinOn ⊢
      intro z hz
      exact_mod_cast hxMinOn z hz
    have hsEReal :
        sInf ((fun x ↦ (problem.kernel x u : EReal)) '' problem.feasibleSet) =
          (problem.kernel xMin u : EReal) := by
      -- Attainment identifies the `EReal` infimum with the same slice value.
      exact (hxMinOnEReal.isGLB hxMin).csInf_eq
        ⟨(problem.kernel xMin u : EReal), ⟨xMin, hxMin, rfl⟩⟩
    rw [hsReal, hsEReal]
  have hgreatestEReal :
      IsGreatest
        ((fun u ↦ sInf ((fun x ↦ (problem.kernel x u : EReal)) '' problem.feasibleSet)) ''
          problem.dualSet)
        (((sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet) : ℝ)) : EReal) := by
    refine ⟨⟨uStar, huStar, (hdual_value_coe_eq huStar).symm⟩, ?_⟩
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    calc
      sInf ((fun x ↦ (problem.kernel x u : EReal)) '' problem.feasibleSet)
          = (((sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet) : ℝ)) : EReal) := by
            symm
            exact hdual_value_coe_eq hu
      _ ≤ (((sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet) : ℝ)) : EReal) := by
            exact_mod_cast huStar_max hu
  calc
    problem.toSetConstrainedMinimizationProblem.optimalValue
        = (problem xStar : EReal) := hopt
    _ =
        (((sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet) : ℝ)) : EReal) := by
      exact congrArg (fun r : ℝ ↦ (r : EReal)) hxValue
    _ =
        (sSup ((fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)) ''
          problem.dualSet) : EReal) := by
      simpa using hgreatestEReal.csSup_eq.symm

/-- Companion attainment form of Theorem 3 1 30: the lower-value function attains a maximizer on
the dual set, and its attained value is the least feasible primal objective value. -/
-- Proof sketch: first obtain the bounded-set minimax equality on the owner layer. The properness
-- hypotheses and the slice geometry built into `problem` yield a maximizing parameter `uStar`.
-- Theorem 3.1.29-style saddle-value consequences then identify the attained dual value with the
-- least element of the primal value image `problem '' problem.feasibleSet`.
theorem exists_dual_maximizer_with_primal_minimum_of_bounded_sets
    (problem : MaxRepresentationPrimalDualProblem E U)
    (hfeasible_nonempty : problem.feasibleSet.Nonempty)
    (hfeasible_bounded : Bornology.IsBounded problem.feasibleSet)
    (hdual_bounded : Bornology.IsBounded problem.dualSet) :
    ∃ uStar,
      IsMaxOn (fun u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet))
        problem.dualSet uStar ∧
        IsLeast (problem '' problem.feasibleSet)
          (sInf ((fun x ↦ problem.kernel x uStar) '' problem.feasibleSet)) := by
  -- The public attainment statement is exactly the shared witness helper.
  obtain ⟨uStar, _, huStar_max, hleast⟩ :=
    exists_primal_dual_value_witness_of_bounded_sets
      problem hfeasible_nonempty hfeasible_bounded hdual_bounded
  exact ⟨uStar, huStar_max, hleast⟩

end

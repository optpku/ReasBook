/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_35
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Algorithm_14_3
import FirstOrderMethodsOptimization_Beck_2017.Chap14.CompositeObjectiveDomain
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Lemma_14_2
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Theorem_14_3_Helpers.PrefixState
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Theorem_14_3_Helpers.Recovery

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Filter
open scoped Topology Gradient

section

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, InnerProductSpace ℝ (Ei i)]
variable [FiniteDimensional ℝ ((i : Fin p) → Ei i)]

attribute [-instance] Pi.seminormedAddCommGroup Pi.normedAddCommGroup Pi.normedSpace

local instance theorem14_5_rawTupleNormedAddCommGroup :
    NormedAddCommGroup ((i : Fin p) → Ei i) :=
  rawTupleNormedAddCommGroup (ι := Fin p) (Ei := Ei)

local instance theorem14_5_rawTupleNormedSpace : NormedSpace ℝ ((i : Fin p) → Ei i) :=
  rawTupleNormedSpace (ι := Fin p) (Ei := Ei)

local instance theorem14_5_rawTupleInnerProductSpace :
    InnerProductSpace ℝ ((i : Fin p) → Ei i) :=
  rawTupleInnerProductSpace (ι := Fin p) (Ei := Ei)

local instance theorem14_5_rawTupleFiniteDimensional :
    FiniteDimensional ℝ ((i : Fin p) → Ei i) :=
  rawTupleFiniteDimensional (ι := Fin p) (Ei := Ei)

local instance theorem14_5_blockFiniteDimensional (i : Fin p) : FiniteDimensional ℝ (Ei i) :=
  blockFiniteDimensional (ι := Fin p) (Ei := Ei) i

local instance theorem14_5_blockCompleteSpace (i : Fin p) : CompleteSpace (Ei i) :=
  blockCompleteSpace (ι := Fin p) (Ei := Ei) i

variable (f : ((i : Fin p) → Ei i) → ℝ)
variable (g : (i : Fin p) → Ei i → EReal)

local notation "F" => composite_model_objective f.toEReal (separableSum g)

-- Semantic recall note: the Chapter 14.5 optimality bridge is routed through
-- `Chap14/Lemma_14_2.lean`, `Chap14/Theorem_14_4.lean`, and `Chap03/Theorem_3_35.lean`, so the
-- smoothness needed downstream is already supplied by `IsAlternatingMinimizationCompositeModel
-- f.toEReal g`; it should not survive as a second public `ContDiffOn` hypothesis here.

/- This item is `source-facing` for the Chapter 14.5 convergence conclusion. The bounded-trajectory
half is already owned canonically by `alternating_minimization_trajectory_range_bounded` from
Theorem 14.3, so the new reusable surface here is the bridge from a cluster point of the
alternating-minimization trajectory to a global minimizer of the convex composite objective. The
textbook bundled statement is then kept as a thin source-facing wrapper around that canonical
boundedness owner and the cluster-point optimality bridge below. -/

variable (x : ℕ → (i : Fin p) → Ei i)

/-- Under the Chapter 14.5 hypotheses, every coordinate-wise minimum of `F` is already a global
minimizer on the whole product space. This is the reusable bridge from the source-facing owner
`is_coordinatewise_minimum` to mathlib's `IsMinOn F Set.univ`, separated from the trajectory-
specific cluster-point wrapper below. The standing owner
`IsAlternatingMinimizationCompositeModel f.toEReal g` already carries the regularity needed by the
Chapter 14 to Chapter 3 bridge, so the only additional public optimality input here is convexity
of `f`. -/
theorem alternating_minimization_coordinatewise_minimum_is_global_minimizer
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    {xStar : (i : Fin p) → Ei i} (hcoord : is_coordinatewise_minimum F xStar) :
    IsMinOn F Set.univ xStar := by
  have hxSep :
      xStar ∈ effective_domain (separableSum g) :=
    composite_objective_effective_domain_iff_separableSum.mp hcoord.mem_effective_domain
  have hxStarInterior :
      xStar ∈ interior (effective_domain f.toEReal) := by
    simp [effective_domain, Function.toEReal]
  have hdiff : is_differentiable_at f.toEReal xStar := by
    -- The standing composite-model owner already makes the real-valued smooth term
    -- differentiable everywhere on the ambient product space.
    have hdiffReal : DifferentiableAt ℝ f xStar := by
      exact
        (hmodel.f_toReal_differentiableOn_interior_effective_domain xStar
          (by simpa [Function.toEReal] using hxStarInterior)).differentiableAt
          (isOpen_interior.mem_nhds (by simpa [Function.toEReal] using hxStarInterior))
    simpa [is_differentiable_at,
      finite_domain_eq_effective_domain (f := f.toEReal) (fun y ↦ by simp [Function.toEReal])]
      using ⟨hxStarInterior, hdiffReal⟩
  have hstationary :
      is_stationary_point f.toEReal (separableSum g) xStar :=
    is_stationary_point_of_coordinatewise_minimum hmodel hcoord
  -- Route correction: once coordinatewise minimality is translated to stationarity by
  -- `Lemma_14_2`, Theorem 3.35 closes the global minimizer claim directly.
  exact
    (isMinOn_univ_iff_is_stationary_point
      hmodel.f_proper
      (separableSum_proper g hmodel.g_proper)
      (separableSum_convex g hmodel.g_proper hmodel.g_convex)
      (by
        simpa [finite_domain_eq_effective_domain (f := f.toEReal) (fun y ↦ by
          simp [Function.toEReal])]
          using hmodel.g_effective_domain_subset_interior_f_effective_domain)
      hxSep
      hdiff
      (Function.toEReal_isConvexFunction hf_convex)).2
      hstationary

/-- Under the Chapter 14.5 hypotheses, every coordinate-wise minimum of `F` belongs to the
canonical unconstrained solution set. This is the companion owner-level bridge from
`is_coordinatewise_minimum F xStar` to `unconstrained_problem_solutions F`, obtained by composing
the global-minimizer bridge above with Definition 8.2's canonical solution-set owner. -/
theorem alternating_minimization_coordinatewise_minimum_mem_solution_set
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    {xStar : (i : Fin p) → Ei i} (hcoord : is_coordinatewise_minimum F xStar) :
    xStar ∈ unconstrained_problem_solutions F := by
  rw [mem_unconstrained_problem_solutions_iff]
  exact alternating_minimization_coordinatewise_minimum_is_global_minimizer
    f g hmodel hf_convex hcoord

/-- Helper for Theorem 14.5: the block-separable penalty `separableSum g` never takes the value
`⊥` under the standing composite-model assumptions. -/
private lemma alternatingMinimizationSeparableSumNeBot
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g) :
    ∀ z : (i : Fin p) → Ei i, separableSum g z ≠ ⊥ := by
  intro z
  -- Every block penalty avoids `⊥`, so the finite block sum avoids `⊥` as well.
  simpa [separableSum_apply] using
    ereal_sum_ne_bot
      Finset.univ
      (fun i ↦ g i (z i))
      (fun i _ ↦ (hmodel.g_proper i).ne_bot (z i))

/-- Helper for Theorem 14.5: the composite objective `F = f.toEReal + separableSum g` never
takes the value `⊥`. -/
private lemma alternatingMinimizationCompositeObjectiveNeBot
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g) :
    ∀ z : (i : Fin p) → Ei i, F z ≠ ⊥ := by
  intro z
  -- The smooth term and the separable penalty are both finite from below.
  rw [composite_model_objective_apply, EReal.add_ne_bot_iff]
  exact ⟨hmodel.f_ne_bot z, alternatingMinimizationSeparableSumNeBot (f := f) (g := g) hmodel z⟩

/-- Helper for Theorem 14.5: finiteness of `F` forces finiteness of the separable penalty. -/
private lemma compositeObjectiveEffectiveDomainSubsetSeparable
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) :
    z ∈ effective_domain (separableSum g) := by
  -- If the separable term were `⊤`, then the whole composite objective would also be `⊤`.
  refine mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr ?_
  intro hsep_top
  have hF_top : F z = ⊤ := by
    rw [composite_model_objective_apply, hsep_top]
    exact EReal.add_top_of_ne_bot (hmodel.f_ne_bot z)
  exact (lt_top_iff_ne_top.mp (mem_effective_domain.mp hz)) hF_top

/-- Helper for Theorem 14.5: every block value of a point in `effective_domain F` lies in the
effective domain of the corresponding block penalty. -/
private lemma alternatingMinimizationBlockMemEffectiveDomain
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) (i : Fin p) :
    z i ∈ effective_domain (g i) := by
  -- Move from the composite effective domain to the separable one, then read off the block.
  exact
    block_mem_effective_domain_of_mem_separableSum_effective_domain
      g
      hmodel.g_proper
      (compositeObjectiveEffectiveDomainSubsetSeparable (f := f) (g := g) hmodel hz)
      i

/-- Helper for Theorem 14.5: replacing one feasible block of a point in
`effective_domain (separableSum g)` preserves membership in that separable effective domain. -/
private lemma alternatingMinimizationUpdateMemEffectiveDomainSeparableSum
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {z : (i : Fin p) → Ei i}
    (hz : z ∈ effective_domain (separableSum g))
    (i : Fin p) {yi : Ei i} (hyi : yi ∈ effective_domain (g i)) :
    Function.update z i yi ∈ effective_domain (separableSum g) := by
  let y : (i : Fin p) → Ei i := Function.update z i yi
  have hyBlock : ∀ j : Fin p, y j ∈ effective_domain (g j) := by
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [y]
    · simpa [y, Function.update, hji] using
        block_mem_effective_domain_of_mem_separableSum_effective_domain
          g
          hmodel.g_proper
          hz
          j
  have hySum :
      separableSum g y = ((((∑ j : Fin p, (g j (y j)).toReal : ℝ)) : ℝ) : EReal) := by
    rw [separableSum_apply]
    calc
      ∑ j : Fin p, g j (y j) = ∑ j : Fin p, ((((g j (y j)).toReal : ℝ)) : EReal) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        exact
          (EReal.coe_toReal
            (mem_effective_domain.mp (hyBlock j)).ne
            ((hmodel.g_proper j).ne_bot (y j))).symm
      _ = ((((∑ j : Fin p, (g j (y j)).toReal : ℝ)) : ℝ) : EReal) := by
        classical
        induction (Finset.univ : Finset (Fin p)) using Finset.induction_on with
        | empty =>
            simp
        | @insert a s ha hs =>
            simp [Finset.sum_insert, ha, hs, EReal.coe_add]
  -- Once each block value is finite, the whole separable sum is finite as well.
  refine mem_effective_domain.mpr ?_
  rw [hySum]
  simp

/-- Helper for Theorem 14.5: replacing one block of a feasible composite point by another feasible
block value preserves membership in the composite effective domain. -/
private lemma alternatingMinimizationCompositeUpdateMemEffectiveDomain
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F)
    (i : Fin p) {yi : Ei i} (hyi : yi ∈ effective_domain (g i)) :
    Function.update z i yi ∈ effective_domain F := by
  -- Route correction: for the composite objective, the moving-base competitor updates stay
  -- feasible by the product-domain API, so later blockwise limit transport should use this lemma
  -- instead of the generic Theorem 14.3 recovery helper.
  exact
    composite_update_mem_effective_domain_of_block_mem
      (f := f)
      (g := g)
      hmodel
      i
      hz
      hyi

/-- Helper for Theorem 14.5: coercing a finite real sum into `EReal` agrees with summing the
coerced terms. -/
private lemma alternatingMinimizationERealCoeFinsetSumAux {α : Type*} (s : Finset α)
    (a : α → ℝ) :
    (((Finset.sum s a : ℝ)) : EReal) = Finset.sum s (fun i ↦ ((a i : ℝ) : EReal)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, ih, EReal.coe_add]

/-- Helper for Theorem 14.5: on `effective_domain F`, each block penalty value is a real coercion
in `EReal`. -/
private lemma alternatingMinimizationBlockValueEqCoeToReal
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) (i : Fin p) :
    g i (z i) = ((((g i (z i)).toReal : ℝ)) : EReal) := by
  -- Effective-domain membership gives both `≠ ⊤` and `≠ ⊥` for the active block value.
  exact
    (EReal.coe_toReal
      (mem_effective_domain.mp
        (alternatingMinimizationBlockMemEffectiveDomain
          (f := f)
          (g := g)
          hmodel
          hz
          i)).ne
      ((hmodel.g_proper i).ne_bot (z i))).symm

/-- Helper for Theorem 14.5: the composite objective `F = f.toEReal + separableSum g` is lower
semicontinuous and continuous on its effective domain. -/
private lemma alternatingMinimizationCompositeObjectiveRegular
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g) :
    LowerSemicontinuous F ∧ ContinuousOn F (effective_domain F) := by
  have hdom_subset :
      effective_domain F ⊆ interior (effective_domain f.toEReal) := by
    intro z hz
    exact
      hmodel.g_effective_domain_subset_interior_f_effective_domain
        (composite_objective_effective_domain_iff_separableSum.mp hz)
  have hclosed : LowerSemicontinuous F := by
    -- Lower semicontinuity is inherited from the two summands because both avoid the singular
    -- `⊥ + ⊤` addition case.
    refine hmodel.f_closed.add' (separableSum_closed g hmodel.g_closed) ?_
    intro z
    exact
      EReal.continuousAt_add
        (.inr (alternatingMinimizationSeparableSumNeBot (f := f) (g := g) hmodel z))
        (.inl (hmodel.f_ne_bot z))
  have hf_cont :
      ContinuousOn (fun z ↦ ((f z : ℝ) : EReal)) (effective_domain F) := by
    -- Differentiability of the real-valued smooth term gives continuity on the composite domain.
    refine
      (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
        ?_
        ?_
    · intro z hz
      exact
        ContinuousWithinAt.mono
          ((hmodel.f_toReal_differentiableOn_interior_effective_domain z (hdom_subset hz)).continuousWithinAt)
          hdom_subset
    · intro z hz
      simp
  have hsep_cont :
      ContinuousOn (separableSum g) (effective_domain F) := by
    classical
    rw [continuousOn_iff_continuous_restrict]
    have htermReal :
        ∀ i : Fin p, Continuous (fun z : effective_domain F ↦ (g i (z.1 i)).toReal) := by
      intro i
      have htermOn :
          ContinuousOn (fun z : effective_domain F ↦ g i (z.1 i)) Set.univ := by
        refine
          (hmodel.g_continuousOn_effective_domain i).comp
            (((continuous_apply i).comp continuous_subtype_val).continuousOn)
            ?_
        intro z hz
        simpa using
          alternatingMinimizationBlockMemEffectiveDomain
            (f := f)
            (g := g)
            hmodel
            z.property
            i
      have htoRealOn :
          ContinuousOn (fun z : effective_domain F ↦ (g i (z.1 i)).toReal) Set.univ := by
        refine EReal.continuousOn_toReal.comp htermOn ?_
        intro z hz
        have hblock :
            z.1 i ∈ effective_domain (g i) :=
          alternatingMinimizationBlockMemEffectiveDomain
            (f := f)
            (g := g)
            hmodel
            z.property
            i
        have htop : g i (z.1 i) ≠ ⊤ := (mem_effective_domain.mp hblock).ne
        have hbot : g i (z.1 i) ≠ ⊥ := (hmodel.g_proper i).ne_bot (z.1 i)
        simp [htop, hbot]
      exact continuousOn_univ.mp htoRealOn
    have hsumReal :
        Continuous (fun z : effective_domain F ↦ ∑ i : Fin p, (g i (z.1 i)).toReal) := by
      exact continuous_finset_sum Finset.univ (fun i _ ↦ htermReal i)
    have hsumCoe :
        Continuous
          (fun z : effective_domain F ↦
            (((∑ i : Fin p, (g i (z.1 i)).toReal : ℝ)) : EReal)) :=
      continuous_coe_real_ereal.comp hsumReal
    have hsumEq :
        (fun z : effective_domain F ↦ separableSum g z.1) =
          fun z : effective_domain F ↦
            (((∑ i : Fin p, (g i (z.1 i)).toReal : ℝ)) : EReal) := by
      funext z
      rw [separableSum_apply]
      calc
        ∑ i : Fin p, g i (z.1 i) = ∑ i : Fin p, ((((g i (z.1 i)).toReal : ℝ)) : EReal) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact
            alternatingMinimizationBlockValueEqCoeToReal
              (f := f)
              (g := g)
              hmodel
              z.property
              i
        _ = (((∑ i : Fin p, (g i (z.1 i)).toReal : ℝ)) : EReal) := by
          simpa using
            (alternatingMinimizationERealCoeFinsetSumAux
              (s := Finset.univ)
              (a := fun i : Fin p ↦ (g i (z.1 i)).toReal)).symm
    change Continuous (fun z : effective_domain F ↦ separableSum g z.1)
    rw [hsumEq]
    exact hsumCoe
  have hcont : ContinuousOn F (effective_domain F) := by
    intro z hz
    have hsum :
        ContinuousWithinAt
          (fun y ↦ ((f y : ℝ) : EReal) + separableSum g y)
          (effective_domain F)
          z := by
      -- On the effective domain both summands are finite, so `EReal` addition is continuous.
      exact
        ContinuousAt.comp₂_continuousWithinAt
          (f := fun p : EReal × EReal ↦ p.1 + p.2)
          (g := fun y ↦ ((f y : ℝ) : EReal))
          (h := separableSum g)
          (s := effective_domain F)
          (x := z)
          (EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _)))
          (hf_cont z hz)
          (hsep_cont z hz)
    -- On `effective_domain F`, the smooth term is literally its `toReal` coercion.
    refine hsum.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp [composite_model_objective_apply,
        EReal.coe_toReal
          (mem_effective_domain.mp (interior_subset (hdom_subset hy))).ne
          (hmodel.f_ne_bot y)]
    · simp [composite_model_objective_apply,
        EReal.coe_toReal
          (mem_effective_domain.mp (interior_subset (hdom_subset hz))).ne
          (hmodel.f_ne_bot z)]
  exact ⟨hclosed, hcont⟩

/-- Helper for Theorem 14.5: restricting the ambient derivative of `f` to one updated block
recovers the derivative of the fixed-base slice `yi ↦ f (Function.update z i yi)`. -/
private lemma alternatingMinimizationTupleToDualMapApplyEqSum
    (v w : (i : Fin p) → Ei i) :
    (InnerProductSpace.toDualMap ℝ ((i : Fin p) → Ei i) v) w =
      ∑ i, inner ℝ (v i) (w i) := by
  -- Route correction: use the canonical raw-tuple inner product rather than unfolding the
  -- instance by hand inside the transport proof.
  rw [InnerProductSpace.toDualMap_apply_apply]
  change
    inner ℝ
        ((ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)) v)
        ((ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)) w) =
      ∑ i, inner ℝ (v i) (w i)
  simpa using
    PiLp.inner_apply
      ((ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)) v)
      ((ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)) w)

/-- Helper for Theorem 14.5: evaluating the ambient dual functional on a singleton block
direction recovers the blockwise pairing on that coordinate. -/
private lemma alternatingMinimizationAmbientToDualApplySingleEqBlock
    (i : Fin p) (v : (j : Fin p) → Ei j) (d : Ei i) :
    (InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j) v) (Pi.single i d : (j : Fin p) → Ei j) =
      (InnerProductSpace.toDualMap ℝ (Ei i) (v i)) d := by
  -- Expand the ambient pairing and keep only the active coordinate of the singleton direction.
  rw [alternatingMinimizationTupleToDualMapApplyEqSum, InnerProductSpace.toDualMap_apply_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- Helper for Theorem 14.5: restricting the ambient derivative of `f` to one updated block
recovers the derivative of the fixed-base slice `yi ↦ f (Function.update z i yi)`. -/
private lemma alternatingMinimizationCoordinateUpdateHasFDerivAt
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {z : (i : Fin p) → Ei i}
    (hz : z ∈ interior (effective_domain f.toEReal))
    (i : Fin p) :
    HasFDerivAt
      (fun yi : Ei i ↦ f (Function.update z i yi))
      (InnerProductSpace.toDualMap ℝ (Ei i) ((∇ f z) i))
      (z i) := by
  classical
  have hdiffAt : DifferentiableAt ℝ f z := by
    exact
      (hmodel.f_toReal_differentiableOn_interior_effective_domain z hz).differentiableAt
        (isOpen_interior.mem_nhds hz)
  have hambient :
      HasFDerivAt
        f
        (InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j) (∇ f z))
        z := by
    simpa using hdiffAt.hasGradientAt.hasFDerivAt
  have hrewrite :
      (fun yi : Ei i ↦ Function.update z i yi) =
        fun yi : Ei i ↦ z + Pi.single i (yi - z i) := by
    funext yi
    ext j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]
  have hupdate :
      HasFDerivAt
        (fun yi : Ei i ↦ Function.update z i yi)
        (ContinuousLinearMap.single ℝ Ei i)
        (z i) := by
    rw [hrewrite]
    simpa using
      (hasFDerivAt_const (x := z i) (z : (j : Fin p) → Ei j)).add
        ((ContinuousLinearMap.single ℝ Ei i).hasFDerivAt.comp
          (x := z i)
          (hasFDerivAt_sub_const (z i)))
  have hambientAtUpdate :
      HasFDerivAt
        f
        (InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j) (∇ f z))
        (Function.update z i (z i)) := by
    -- Rebase the ambient derivative at the definitionally equal updated point.
    simpa using hambient
  have hcomp :
      HasFDerivAt
        (fun yi : Ei i ↦ f (Function.update z i yi))
        ((InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j) (∇ f z)).comp
          (ContinuousLinearMap.single ℝ Ei i))
        (z i) := by
    simpa [Function.comp] using hambientAtUpdate.comp (x := z i) hupdate
  have hdual :
      ((InnerProductSpace.toDualMap ℝ ((j : Fin p) → Ei j) (∇ f z)).comp
          (ContinuousLinearMap.single ℝ Ei i)) =
        InnerProductSpace.toDualMap ℝ (Ei i) ((∇ f z) i) := by
    ext d
    rw [ContinuousLinearMap.comp_apply]
    exact alternatingMinimizationAmbientToDualApplySingleEqBlock i (∇ f z) d
  simpa [hdual] using hcomp

/-- Helper for Theorem 14.5: Euclidean block-subgradient membership yields the corresponding
real-valued support inequality on every feasible comparison block. -/
private lemma alternatingMinimizationBlockSubgradientEvalLeToRealSub
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {z : (i : Fin p) → Ei i} {i : Fin p}
    (hsub : -((∇ f z) i) ∈ euclideanSubdifferential (g i) (z i))
    {yi : Ei i} (hyi : yi ∈ effective_domain (g i)) :
    inner ℝ (-((∇ f z) i)) (yi - z i) ≤
      (g i yi).toReal - (g i (z i)).toReal := by
  rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_iff_forall_mem_effective_domain] at hsub
  rcases hsub with ⟨hzi, hineq⟩
  have hzi_ne_bot : g i (z i) ≠ ⊥ := (hmodel.g_proper i).ne_bot (z i)
  have hyi_ne_bot : g i yi ≠ ⊥ := (hmodel.g_proper i).ne_bot yi
  have hzi_ne_top : g i (z i) ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hzi)
  have hyi_ne_top : g i yi ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hyi)
  have hreal_add :
      (g i (z i)).toReal +
          InnerProductSpace.toDualMap ℝ (Ei i) (-((∇ f z) i)) (yi - z i) ≤
        (g i yi).toReal := by
    have hineq' := hineq yi hyi
    rw [ge_iff_le, (EReal.coe_toReal hyi_ne_top hyi_ne_bot).symm,
      (EReal.coe_toReal hzi_ne_top hzi_ne_bot).symm] at hineq'
    have hineq'' :
        (((g i (z i)).toReal : ℝ) : EReal) +
            (((InnerProductSpace.toDualMap ℝ (Ei i) (-((∇ f z) i)) (yi - z i) : ℝ)) : EReal) ≤
          (((g i yi).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_add] using hineq'
    exact_mod_cast hineq''
  have hpair :
      (g i (z i)).toReal + inner ℝ (-((∇ f z) i)) (yi - z i) ≤
        (g i yi).toReal := by
    simpa [InnerProductSpace.toDualMap_apply_apply] using hreal_add
  linarith

/-- Helper for Theorem 14.5: one stage of the refined prefix-state chain packages the next stage
limit as an explicit block update of the current stage limit, together with the exact block
argmin relation and the preserved objective value. -/
private lemma alternatingMinimizationStageStepLimitPackage
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hclosed : LowerSemicontinuous F)
    (hcont : ContinuousOn F (effective_domain F))
    (hlevels : ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar z : (i : Fin p) → Ei i}
    {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ)
    (hxBar : xBar ∈ effective_domain F)
    (hiter : Tendsto (fun m ↦ x (ψ m)) atTop (𝓝 xBar))
    (hz : z ∈ effective_domain F)
    (hvalue : F z = F xBar)
    (l : Fin p)
    (hstage :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) l.1) atTop (𝓝 z)) :
    ∃ ψ' : ℕ → ℕ, ∃ zNext : (i : Fin p) → Ei i, StrictMono ψ' ∧
      Tendsto (fun m ↦ x (ψ' m)) atTop (𝓝 xBar) ∧
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) (l.1 + 1))
        atTop (𝓝 zNext) ∧
      zNext = Function.update z l (zNext l) ∧
      zNext l ∈ alternating_minimization_argmin F z l ∧
      F zNext = F z := by
  rcases AlternatingMinimization.PrefixState.stage_succ_has_convergent_refinement
      F x hclosed hlevels htraj (ψ := ψ) l.is_lt with
    ⟨φ, hφ, zNext, hnext⟩
  let ψ' : ℕ → ℕ := ψ ∘ φ
  have hψ' : StrictMono ψ' := by
    intro a b hab
    exact hψ (hφ hab)
  have hiter' :
      Tendsto (fun m ↦ x (ψ' m)) atTop (𝓝 xBar) := by
    simpa [ψ', Function.comp] using hiter.comp hφ.tendsto_atTop
  have hstage' :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) l.1) atTop (𝓝 z) := by
    simpa [ψ', Function.comp] using hstage.comp hφ.tendsto_atTop
  have hnext' :
      Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ' m) (l.1 + 1))
        atTop (𝓝 zNext) := by
    simpa [ψ', Function.comp] using hnext
  have hFiter :
      Tendsto (fun m ↦ F (x (ψ' m))) atTop (𝓝 (F xBar)) := by
    exact alternating_minimization_tendsto_objective_of_tendsto
      F hcont hxBar hiter' fun m ↦
        alternating_minimization_iterate_mem_effective_domain F x htraj (ψ' m)
  have hFshift :
      Tendsto (fun m ↦ F (x (ψ' m + 1))) atTop (𝓝 (F xBar)) := by
    exact alternating_minimization_shifted_objective_tendsto F x htraj hψ' hFiter
  have hFstage :
      Tendsto (fun m ↦ F (alternating_minimization_prefix_state x (ψ' m) l.1))
        atTop (𝓝 (F xBar)) := by
    simpa [hvalue] using
      (alternating_minimization_tendsto_objective_of_tendsto
        F hcont hz hstage' fun m ↦
          (alternating_minimization_prefix_state_mem_effective_domain_and_le
            F x htraj (ψ' m)
            (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ' m))
            l.1 (Nat.le_of_lt l.is_lt)).1)
  have hFnext :
      Tendsto (fun m ↦ F (alternating_minimization_prefix_state x (ψ' m) (l.1 + 1)))
        atTop (𝓝 (F z)) := by
    have hFnext_xBar :
        Tendsto (fun m ↦ F (alternating_minimization_prefix_state x (ψ' m) (l.1 + 1)))
          atTop
          (𝓝 (F xBar)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hFshift hFstage ?_ ?_
      · intro m
        exact alternating_minimization_next_iterate_objective_le_prefix_state
          F x htraj (ψ' m) (l.1 + 1)
      · intro m
        exact alternating_minimization_prefix_state_succ_objective_le
          F x htraj (ψ' m) l.1 l.is_lt
    simpa [hvalue] using hFnext_xBar
  have hupdate :
      zNext = Function.update z l (zNext l) := by
    exact alternating_minimization_prefix_state_limit_eq_update x ψ' l hstage' hnext'
  have hyUpdate : Inseparable zNext (Function.update z l (zNext l)) := by
    exact Inseparable.of_eq hupdate
  have hupdatedValue :
      F (Function.update z l (zNext l)) = F z :=
    (alternating_minimization_limit_block_updated_value_eq_cluster_value
      F x hclosed hcont htraj z zNext l hz hyUpdate hnext' hFnext).2
  have hargmin :
      zNext l ∈ alternating_minimization_argmin F z l := by
    refine (mem_alternating_minimization_argmin_update_iff).2 ?_
    rw [isMinOn_iff]
    intro zi _
    by_cases hzi : zi ∈ effective_domain (g l)
    · have hzUpdate : Function.update z l zi ∈ effective_domain F :=
        alternatingMinimizationCompositeUpdateMemEffectiveDomain
          (f := f) (g := g) hmodel hz l hzi
      have hmovingUpdate :
          ∀ m,
            Function.update
                (alternating_minimization_prefix_state x (ψ' m) l.1)
                l zi ∈ effective_domain F := by
        intro m
        have hmDom :
            alternating_minimization_prefix_state x (ψ' m) l.1 ∈ effective_domain F :=
          (alternating_minimization_prefix_state_mem_effective_domain_and_le
            F x htraj (ψ' m)
            (alternating_minimization_iterate_mem_effective_domain F x htraj (ψ' m))
            l.1 (Nat.le_of_lt l.is_lt)).1
        exact alternatingMinimizationCompositeUpdateMemEffectiveDomain
          (f := f) (g := g) hmodel hmDom l hzi
      exact
        alternating_minimization_limit_block_compare_with_recovered_competitor
          F x hcont htraj z zNext l hstage' hFnext hupdatedValue hzUpdate
          tendsto_const_nhds hmovingUpdate
    · have hziTop : g l zi = ⊤ := by
        exact top_unique <| not_lt.mp (by simpa [effective_domain] using hzi)
      have hrestNeBot :
          (∑ j ∈ Finset.univ.erase l,
              g j ((Function.update z l zi) j)) ≠ ⊥ := by
        exact
          ereal_sum_ne_bot
            (Finset.univ.erase l)
            (fun j ↦ g j ((Function.update z l zi) j))
            (fun j _ ↦ (hmodel.g_proper j).ne_bot _)
      have hsumTop : separableSum g (Function.update z l zi) = ⊤ := by
        rw [separableSum_apply]
        have hactiveTop : g l ((Function.update z l zi) l) = ⊤ := by
          simpa using hziTop
        calc
          ∑ j : Fin p, g j ((Function.update z l zi) j) =
              g l ((Function.update z l zi) l) +
                ∑ j ∈ Finset.univ.erase l,
                  g j ((Function.update z l zi) j) := by
            symm
            exact
              Finset.add_sum_erase Finset.univ
                (fun j : Fin p ↦ g j ((Function.update z l zi) j))
                (Finset.mem_univ l)
          _ = ⊤ := by
            rw [hactiveTop, EReal.top_add_of_ne_bot hrestNeBot]
      have hcompetitorTop : F (Function.update z l zi) = ⊤ := by
        rw [composite_model_objective_apply, hsumTop]
        exact EReal.add_top_of_ne_bot (hmodel.f_ne_bot _)
      rw [hcompetitorTop]
      exact le_top
  have hvalueNext :
      F zNext = F z := by
    -- Rewrite the updated-limit value identity through the packaged update equation.
    exact hupdate.symm ▸ hupdatedValue
  exact ⟨ψ', zNext, hψ', hiter', hnext', hupdate, hargmin, hvalueNext⟩

/-- Helper for Theorem 14.5: an exact one-block argmin relation yields the Euclidean block
subdifferential certificate at the same base point. -/
private lemma negativeGradientMemEuclideanSubdifferential_ofExactBlockArgmin
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {z : (i : Fin p) → Ei i} (i : Fin p)
    (hz : z ∈ effective_domain F)
    (hargmin : z i ∈ alternating_minimization_argmin F z i) :
    -((∇ f z) i) ∈ euclideanSubdifferential (g i) (z i) := by
  have hzSep :
      z ∈ effective_domain (separableSum g) :=
    compositeObjectiveEffectiveDomainSubsetSeparable (f := f) (g := g) hmodel hz
  have hzInterior :
      z ∈ interior (effective_domain f.toEReal) :=
    hmodel.g_effective_domain_subset_interior_f_effective_domain hzSep
  have hinactive_ne_bot :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then z j else z j)) ≠ ⊥ := by
    -- Every inactive block penalty avoids `⊥`, so the frozen inactive sum does too.
    simpa using
      ereal_sum_ne_bot
        (Finset.univ.erase i)
        (fun j ↦ g j (if j.1 < i.1 then z j else z j))
        (fun j _ ↦ (hmodel.g_proper j).ne_bot _)
  have hactive_ne_bot :
      alternating_minimization_composite_block_objective f.toEReal g z z i (z i) ≠ ⊥ := by
    -- At the current block value both the smooth slice and the active penalty are finite below.
    simpa [alternating_minimization_composite_block_objective_apply,
      alternating_minimization_block_objective_base_apply] using
      (EReal.add_ne_bot_iff.2
        ⟨hmodel.f_ne_bot z, (hmodel.g_proper i).ne_bot (z i)⟩)
  have hinactive :
      (∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then z j else z j)) =
        (((∑ j ∈ Finset.univ.erase i, g j (if j.1 < i.1 then z j else z j)).toReal : ℝ) :
          EReal) := by
    -- Proposition 14.2 needs the frozen inactive penalty to be a genuine finite constant.
    refine
      inactive_penalty_eq_coe_toReal_of_ne_bot_of_mem_effective_domain
        (f := f.toEReal)
        (g := g)
        (xk := z)
        (xNext := z)
        (i := i)
        hinactive_ne_bot
        hactive_ne_bot
        ?_
    simpa using hz
  have hminFull :
      IsMinOn
        (alternating_minimization_block_objective F z z i)
        Set.univ
        (z i) := by
    -- Rewrite the fixed-base argmin certificate into the full one-block objective spelling.
    exact (mem_alternating_minimization_argmin_iff).1 hargmin
  have hminBlock :
      IsMinOn
        (alternating_minimization_composite_block_objective f.toEReal g z z i)
        Set.univ
        (z i) := by
    -- Proposition 14.2 removes the inactive constant from the one-block objective.
    exact
      (isMinOn_alternating_minimization_full_objective_iff_isMinOn_composite_block_objective
        (f := f.toEReal)
        (g := g)
        (xk := z)
        (xNext := z)
        (i := i)
        hinactive
        (z i)).1
        hminFull
  have hxBlock :
      z i ∈ effective_domain (g i) :=
    alternatingMinimizationBlockMemEffectiveDomain
      (f := f)
      (g := g)
      hmodel
      hz
      i
  have hfBlockProper :
      IsProperExtendedRealFunction
        (alternating_minimization_block_objective f.toEReal z z i) := by
    refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro yi
      simpa [alternating_minimization_block_objective_base_apply] using
        hmodel.f_ne_bot (Function.update z i yi)
    · refine ⟨z i, ?_⟩
      simpa [alternating_minimization_block_objective_base_apply, effective_domain, Function.toEReal]
  have hdomBlock :
      effective_domain (g i) ⊆
        interior (finite_domain (alternating_minimization_block_objective f.toEReal z z i)) := by
    -- The real-valued smooth slice has full finite domain after coercion to `EReal`.
    intro yi hyi
    simp [alternating_minimization_block_objective_base_apply, finite_domain, effective_domain,
      Function.toEReal]
  have hdiffBlock :
      is_differentiable_at
        (alternating_minimization_block_objective f.toEReal z z i)
        (z i) := by
    refine ⟨hdomBlock hxBlock, ?_⟩
    -- Restrict the ambient derivative of `f` to the active coordinate slice.
    simpa [alternating_minimization_block_objective_base_apply] using
      (alternatingMinimizationCoordinateUpdateHasFDerivAt
        (f := f)
        (g := g)
        hmodel
        hzInterior
        i).differentiableAt
  have hlocal :
      IsLocalMin
        (alternating_minimization_composite_block_objective f.toEReal g z z i)
        (z i) :=
    hminBlock.isLocalMin (by simp)
  have hstationary :
      is_stationary_point
        (alternating_minimization_block_objective f.toEReal z z i)
        (g i)
        (z i) :=
    is_stationary_point_of_isLocalMin
      hfBlockProper
      (hmodel.g_proper i)
      (hmodel.g_convex i)
      hdomBlock
      hxBlock
      hdiffBlock
      hlocal
  rw [is_stationary_point_iff] at hstationary
  have hupdateGradient :
      ∇ (fun yi : Ei i ↦ f (Function.update z i yi)) (z i) =
        ((∇ f z) i) := by
    have hgradHasFDerivAt :
        HasFDerivAt
          (fun yi : Ei i ↦ f (Function.update z i yi))
          (InnerProductSpace.toDualMap ℝ (Ei i)
            (∇ (fun yi : Ei i ↦ f (Function.update z i yi)) (z i)))
          (z i) := by
      -- The one-block slice has a unique ambient gradient at the base point.
      simpa using
        (alternatingMinimizationCoordinateUpdateHasFDerivAt
          (f := f)
          (g := g)
          hmodel
          hzInterior
          i).differentiableAt.hasGradientAt.hasFDerivAt
    have hdual :
        InnerProductSpace.toDualMap ℝ (Ei i)
          (∇ (fun yi : Ei i ↦ f (Function.update z i yi)) (z i)) =
        InnerProductSpace.toDualMap ℝ (Ei i)
          ((∇ f z) i) := by
      exact hgradHasFDerivAt.unique
        (alternatingMinimizationCoordinateUpdateHasFDerivAt
          (f := f)
          (g := g)
          hmodel
          hzInterior
          i)
    exact (InnerProductSpace.toDualMap ℝ (Ei i)).injective hdual
  have hnegDual :
      (-InnerProductSpace.toDual ℝ (Ei i)
          (∇ (fun yi : Ei i ↦ f (Function.update z i yi)) (z i)) :
          Module.Dual ℝ (Ei i)) =
        InnerProductSpace.toDualMap ℝ (Ei i) (-((∇ f z) i)) := by
    -- Rewrite the stationary dual vector into the Euclidean block-gradient spelling.
    ext d
    simp [InnerProductSpace.toDual_apply_eq_toDualMap_apply, hupdateGradient]
  rw [mem_euclideanSubdifferential_iff]
  simpa [hnegDual] using hstationary.2

/-- Helper for Theorem 14.5: a convex differentiable real-valued function on the whole product
space satisfies the first-order support inequality at the chosen base point. -/
private lemma alternatingMinimizationConvexSupportAtBase
    {xBase yBase : (i : Fin p) → Ei i}
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hbase_diff : DifferentiableAt ℝ f xBase) :
    f yBase ≥ f xBase + inner ℝ (∇ f xBase) (yBase - xBase) := by
  have hbaseDiffEReal :
      is_differentiable_at f.toEReal xBase := by
    refine ⟨?_, ?_⟩
    · simp [finite_domain, effective_domain, Function.toEReal]
    · simpa [Function.toEReal] using hbase_diff
  have hsub :
      (InnerProductSpace.toDual ℝ ((i : Fin p) → Ei i) (∇ f xBase) :
          Module.Dual ℝ ((i : Fin p) → Ei i)) ∈
        subdifferential f.toEReal xBase := by
    -- Convex differentiability gives the canonical gradient subgradient for `f.toEReal`.
    simpa [Function.toEReal] using
      toDualGradient_mem_subdifferential_of_convex_differentiableAt
        (f := f.toEReal)
        (xStar := xBase)
        (Function.toEReal_isConvexFunction hf_convex)
        hbaseDiffEReal
  have hsupport :
      inner ℝ (∇ f xBase) (yBase - xBase) ≤ f yBase - f xBase := by
    -- Read the owner subgradient inequality back in `ℝ`.
    simpa [Function.toEReal, InnerProductSpace.toDual_apply_eq_toDualMap_apply,
      InnerProductSpace.toDualMap_apply_apply] using
      (subgradient_eval_le_toReal_sub
        (f := f.toEReal)
        (x := xBase)
        (y := yBase)
        (h_ne_bot := fun z _ ↦ by simp [Function.toEReal])
        (by simp [finite_domain, effective_domain, Function.toEReal])
        (by simp [finite_domain, effective_domain, Function.toEReal])
        hsub)
  linarith

/-- Helper for Theorem 14.5: on `effective_domain F`, the composite objective agrees with the
coercion of the real smooth term plus the real block-penalty sum. -/
private lemma alternatingMinimizationCompositeValueEqCoeRealSum
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    {z : (i : Fin p) → Ei i} (hz : z ∈ effective_domain F) :
    F z = (((f z + ∑ i : Fin p, (g i (z i)).toReal : ℝ)) : EReal) := by
  -- Normalize both the smooth term and the block penalties to their real-valued representatives.
  rw [composite_model_objective_apply, separableSum_apply]
  calc
    (((f z : ℝ)) : EReal) + ∑ i : Fin p, g i (z i) =
        (((f z : ℝ)) : EReal) +
          ∑ i : Fin p, ((((g i (z i)).toReal : ℝ)) : EReal) := by
      refine congrArg (fun t : EReal ↦ (((f z : ℝ)) : EReal) + t) ?_
      refine Finset.sum_congr rfl ?_
      intro i _
      exact
        alternatingMinimizationBlockValueEqCoeToReal
          (f := f)
          (g := g)
          hmodel
          hz
          i
    _ = (((f z : ℝ)) : EReal) +
          (((∑ i : Fin p, (g i (z i)).toReal : ℝ)) : EReal) := by
      rw [← alternatingMinimizationERealCoeFinsetSumAux
        (s := Finset.univ)
        (a := fun i : Fin p ↦ (g i (z i)).toReal)]
    _ = (((f z + ∑ i : Fin p, (g i (z i)).toReal : ℝ)) : EReal) := by
      rw [← EReal.coe_add]

/-- Helper for Theorem 14.5: if the next stage point is obtained by updating the current base at
the same block, then the fixed-base argmin statement is unchanged when the base is switched to the
updated point. -/
private lemma alternatingMinimizationArgminBaseInvariantOfSelfUpdate
    {z zNext : (i : Fin p) → Ei i} {l : Fin p}
    (hupdate : zNext = Function.update z l (zNext l)) :
    zNext l ∈ alternating_minimization_argmin F z l ↔
      zNext l ∈ alternating_minimization_argmin F zNext l := by
  rw [mem_alternating_minimization_argmin_update_iff,
    mem_alternating_minimization_argmin_update_iff]
  -- After a self-update on the same block, both fixed-base slices are literally the same.
  rw [hupdate]
  have hslice :
      (fun yi : Ei l ↦ F (Function.update (Function.update z l (zNext l)) l yi)) =
        fun yi : Ei l ↦ F (Function.update z l yi) := by
    funext yi
    simp
  simpa [hslice]

/-- Helper for Theorem 14.5: replacing block `m` in the earlier stage and subtracting the later
stage point produces exactly the sum of the changed `l`- and `m`-block singleton directions. -/
private lemma alternatingMinimizationBackwardTransportDisplacement
    {zPrev z : (i : Fin p) → Ei i} {l m : Fin p}
    (hlm : l.1 < m.1)
    (hupdate : z = Function.update zPrev l (z l))
    (yi : Ei m) :
    Function.update zPrev m yi - z =
      Pi.single l (zPrev l - z l) + Pi.single m (yi - z m) := by
  -- Compare coordinates: only the `l`- and `m`-blocks change between the two states.
  rw [hupdate]
  ext j
  by_cases hjl : j = l
  · subst j
    have hlm' : l ≠ m := ne_of_lt hlm
    have hml : m ≠ l := ne_of_gt hlm
    simp [Function.update, hlm', hml]
  · by_cases hjm : j = m
    · subst j
      have hlm' : l ≠ m := ne_of_lt hlm
      have hml : m ≠ l := ne_of_gt hlm
      simp [Function.update, hlm', hml]
    · simp [Function.update, hjl, hjm]

/-- Helper for Theorem 14.5: after undoing the earlier block-`l` update and changing block `m`,
the real-valued separable penalty sum differs from the later-stage penalty only in the `l`- and
`m`-coordinates. -/
private lemma alternatingMinimizationBackwardTransportPenaltyDifference
    {zPrev z : (i : Fin p) → Ei i} {l m : Fin p}
    (hlm : l.1 < m.1)
    (hupdate : z = Function.update zPrev l (z l))
    (yi : Ei m) :
    (∑ j : Fin p, (g j ((Function.update zPrev m yi) j)).toReal) =
      (∑ j : Fin p, (g j (z j)).toReal) +
        ((g l (zPrev l)).toReal - (g l (z l)).toReal) +
        ((g m yi).toReal - (g m (z m)).toReal) := by
  let y : (i : Fin p) → Ei i := Function.update zPrev m yi
  have hlm_ne : l ≠ m := ne_of_lt hlm
  have hml_ne : m ≠ l := ne_of_gt hlm
  have hm_mem : m ∈ Finset.univ.erase l := by
    simp [hml_ne]
  have hy_split :
      (∑ j : Fin p, (g j (y j)).toReal) =
        (g l (zPrev l)).toReal + (g m yi).toReal +
          Finset.sum ((Finset.univ.erase l).erase m) (fun j ↦ (g j (z j)).toReal) := by
    -- Split the updated penalty sum into the active `l`- and `m`-coordinates and the unchanged
    -- tail coordinates.
    calc
      (∑ j : Fin p, (g j (y j)).toReal) =
          (g l (y l)).toReal +
            Finset.sum (Finset.univ.erase l) (fun j ↦ (g j (y j)).toReal) := by
            symm
            exact Finset.add_sum_erase Finset.univ (fun j ↦ (g j (y j)).toReal) (Finset.mem_univ l)
      _ = (g l (zPrev l)).toReal +
            Finset.sum (Finset.univ.erase l) (fun j ↦ (g j (y j)).toReal) := by
            simp [y, Function.update, hlm_ne]
      _ = (g l (zPrev l)).toReal +
            ((g m (y m)).toReal +
              Finset.sum ((Finset.univ.erase l).erase m) (fun j ↦ (g j (y j)).toReal)) := by
            rw [← Finset.add_sum_erase (Finset.univ.erase l) (fun j ↦ (g j (y j)).toReal) hm_mem]
      _ = (g l (zPrev l)).toReal +
            ((g m yi).toReal +
              Finset.sum ((Finset.univ.erase l).erase m) (fun j ↦ (g j (z j)).toReal)) := by
            have hm_eq : (g m (y m)).toReal = (g m yi).toReal := by
              simp [y, Function.update]
            have htail_eq :
                Finset.sum ((Finset.univ.erase l).erase m) (fun j ↦ (g j (y j)).toReal) =
                  Finset.sum ((Finset.univ.erase l).erase m) (fun j ↦ (g j (z j)).toReal) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hj_ne_m : j ≠ m := (Finset.mem_erase.mp hj).1
              have hj_mem_l : j ∈ Finset.univ.erase l := Finset.mem_of_mem_erase hj
              have hj_ne_l : j ≠ l := (Finset.mem_erase.mp hj_mem_l).1
              have hyj : y j = zPrev j := by
                simp [y, Function.update, hj_ne_m]
              have hzj : z j = zPrev j := by
                simpa [Function.update, hj_ne_l] using
                  congrArg (fun w : (i : Fin p) → Ei i ↦ w j) hupdate
              rw [hyj, hzj]
            rw [hm_eq, htail_eq]
      _ = (g l (zPrev l)).toReal + (g m yi).toReal +
            Finset.sum ((Finset.univ.erase l).erase m) (fun j ↦ (g j (z j)).toReal) := by
            ring
  have hz_split :
      (∑ j : Fin p, (g j (z j)).toReal) =
        (g l (z l)).toReal + (g m (z m)).toReal +
          Finset.sum ((Finset.univ.erase l).erase m) (fun j ↦ (g j (z j)).toReal) := by
    -- Split the later-stage penalty sum in the same two-coordinate normal form.
    calc
      (∑ j : Fin p, (g j (z j)).toReal) =
          (g l (z l)).toReal +
            Finset.sum (Finset.univ.erase l) (fun j ↦ (g j (z j)).toReal) := by
            symm
            exact Finset.add_sum_erase Finset.univ (fun j ↦ (g j (z j)).toReal) (Finset.mem_univ l)
      _ = (g l (z l)).toReal +
            ((g m (z m)).toReal +
              Finset.sum ((Finset.univ.erase l).erase m) (fun j ↦ (g j (z j)).toReal)) := by
            rw [← Finset.add_sum_erase (Finset.univ.erase l) (fun j ↦ (g j (z j)).toReal) hm_mem]
      _ = (g l (z l)).toReal + (g m (z m)).toReal +
            Finset.sum ((Finset.univ.erase l).erase m) (fun j ↦ (g j (z j)).toReal) := by
            ring
  -- Compare the two split penalty sums and isolate the changed `l`- and `m`-blocks.
  linarith [hy_split, hz_split]

/-- Helper for Theorem 14.5: later exact block-minimizer data at stage `z` transports the target
block argmin statement backward across an earlier exact update on block `l < m`. -/
private lemma alternatingMinimizationTransportExactBlockArgminBackward
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    {zPrev z : (i : Fin p) → Ei i} {l m : Fin p}
    (hlm : l.1 < m.1)
    (hzPrev : zPrev ∈ effective_domain F)
    (hz : z ∈ effective_domain F)
    (hupdate : z = Function.update zPrev l (z l))
    (hvalue : F z = F zPrev)
    (harg_l : z l ∈ alternating_minimization_argmin F z l)
    (harg_m : z m ∈ alternating_minimization_argmin F z m) :
    zPrev m ∈ alternating_minimization_argmin F zPrev m := by
  rw [mem_alternating_minimization_argmin_update_iff, isMinOn_iff]
  intro yi _
  by_cases hyi : yi ∈ effective_domain (g m)
  · let y : (i : Fin p) → Ei i := Function.update zPrev m yi
    have hy : y ∈ effective_domain F :=
      alternatingMinimizationCompositeUpdateMemEffectiveDomain
        (f := f)
        (g := g)
        hmodel
        hzPrev
        m
        hyi
    have hzSep :
        z ∈ effective_domain (separableSum g) :=
      compositeObjectiveEffectiveDomainSubsetSeparable (f := f) (g := g) hmodel hz
    have hzInterior :
        z ∈ interior (effective_domain f.toEReal) :=
      hmodel.g_effective_domain_subset_interior_f_effective_domain hzSep
    have hdiff :
        DifferentiableAt ℝ f z := by
      -- The standing smoothness owner gives differentiability of `f` on the later-stage base.
      exact
        (hmodel.f_toReal_differentiableOn_interior_effective_domain z hzInterior).differentiableAt
          (isOpen_interior.mem_nhds hzInterior)
    have hlSub :
        inner ℝ (-((∇ f z) l)) (zPrev l - z l) ≤
          (g l (zPrev l)).toReal - (g l (z l)).toReal := by
      -- Convert the exact block-`l` argmin to the corresponding block subgradient inequality.
      exact
        alternatingMinimizationBlockSubgradientEvalLeToRealSub
          (f := f)
          (g := g)
          hmodel
          (negativeGradientMemEuclideanSubdifferential_ofExactBlockArgmin
            (f := f)
            (g := g)
            hmodel
            l
            hz
            harg_l)
          (alternatingMinimizationBlockMemEffectiveDomain
            (f := f)
            (g := g)
            hmodel
            hzPrev
            l)
    have hmSub :
        inner ℝ (-((∇ f z) m)) (yi - z m) ≤
          (g m yi).toReal - (g m (z m)).toReal := by
      -- The exact block-`m` argmin gives the comparison inequality for the competitor `yi`.
      exact
        alternatingMinimizationBlockSubgradientEvalLeToRealSub
          (f := f)
          (g := g)
          hmodel
          (negativeGradientMemEuclideanSubdifferential_ofExactBlockArgmin
            (f := f)
            (g := g)
            hmodel
            m
            hz
            harg_m)
          hyi
    have hdisp :
        y - z =
          Pi.single l (zPrev l - z l) + Pi.single m (yi - z m) := by
      -- Keep the transport geometry in the two-coordinate normal form.
      simpa [y] using
        alternatingMinimizationBackwardTransportDisplacement
          (zPrev := zPrev)
          (z := z)
          (l := l)
          (m := m)
          hlm
          hupdate
          yi
    have hinner_l :
        inner ℝ (∇ f z) (Pi.single l (zPrev l - z l) : (i : Fin p) → Ei i) =
          inner ℝ ((∇ f z) l) (zPrev l - z l) := by
      -- Evaluating the ambient pairing on the singleton `l`-direction recovers the block pairing.
      simpa [InnerProductSpace.toDualMap_apply_apply] using
        alternatingMinimizationAmbientToDualApplySingleEqBlock
          (Ei := Ei)
          (i := l)
          (v := ∇ f z)
          (d := zPrev l - z l)
    have hinner_m :
        inner ℝ (∇ f z) (Pi.single m (yi - z m) : (i : Fin p) → Ei i) =
          inner ℝ ((∇ f z) m) (yi - z m) := by
      -- Do the same normalization for the moving target block `m`.
      simpa [InnerProductSpace.toDualMap_apply_apply] using
        alternatingMinimizationAmbientToDualApplySingleEqBlock
          (Ei := Ei)
          (i := m)
          (v := ∇ f z)
          (d := yi - z m)
    have hinner_disp :
        inner ℝ (∇ f z) (y - z) =
          inner ℝ ((∇ f z) l) (zPrev l - z l) +
            inner ℝ ((∇ f z) m) (yi - z m) := by
      -- The displacement only uses the `l`- and `m`-coordinates, so the ambient pairing splits.
      rw [hdisp, inner_add_right, hinner_l, hinner_m]
    have hinner_lower :
        ((g l (z l)).toReal - (g l (zPrev l)).toReal) +
            ((g m (z m)).toReal - (g m yi).toReal) ≤
          inner ℝ (∇ f z) (y - z) := by
      have hlGrad :
          (g l (z l)).toReal - (g l (zPrev l)).toReal ≤
            inner ℝ ((∇ f z) l) (zPrev l - z l) := by
        have hlSub' :
            -inner ℝ ((∇ f z) l) (zPrev l - z l) ≤
              (g l (zPrev l)).toReal - (g l (z l)).toReal := by
          simpa using hlSub
        linarith
      have hmGrad :
          (g m (z m)).toReal - (g m yi).toReal ≤
            inner ℝ ((∇ f z) m) (yi - z m) := by
        have hmSub' :
            -inner ℝ ((∇ f z) m) (yi - z m) ≤
              (g m yi).toReal - (g m (z m)).toReal := by
          simpa using hmSub
        linarith
      rw [hinner_disp]
      linarith [hlGrad, hmGrad]
    have hsupport :
        f y ≥ f z + inner ℝ (∇ f z) (y - z) :=
      alternatingMinimizationConvexSupportAtBase
        (f := f)
        (xBase := z)
        (yBase := y)
        hf_convex
        hdiff
    let sz : ℝ := ∑ j : Fin p, (g j (z j)).toReal
    let sy : ℝ := ∑ j : Fin p, (g j (y j)).toReal
    have hpenalty :
        sy = sz + ((g l (zPrev l)).toReal - (g l (z l)).toReal) +
          ((g m yi).toReal - (g m (z m)).toReal) := by
      -- Normalize the penalty gap once so the final arithmetic stays on `ℝ`.
      simpa [sy, sz, y] using
        alternatingMinimizationBackwardTransportPenaltyDifference
          (g := g)
          (zPrev := zPrev)
          (z := z)
          (l := l)
          (m := m)
          hlm
          hupdate
          yi
    have hreal_le : f z + sz ≤ f y + sy := by
      -- Convex support plus the two block subgradient inequalities force the competitor value up.
      linarith
    have hzValue :
        F z = (((f z + sz : ℝ)) : EReal) := by
      simpa [sz] using
        alternatingMinimizationCompositeValueEqCoeRealSum
          (f := f)
          (g := g)
          hmodel
          hz
    have hyValue :
        F y = (((f y + sy : ℝ)) : EReal) := by
      simpa [sy, y] using
        alternatingMinimizationCompositeValueEqCoeRealSum
          (f := f)
          (g := g)
          hmodel
          hy
    have htransport : F z ≤ F y := by
      -- Once both objective values are normalized to `ℝ`, the transport inequality is scalar.
      rw [hzValue, hyValue]
      exact_mod_cast hreal_le
    calc
      F (Function.update zPrev m (zPrev m)) = F zPrev := by simp
      _ = F z := by simpa using hvalue.symm
      _ ≤ F y := htransport
      _ = F (Function.update zPrev m yi) := by simp [y]
  · have hyi_top : g m yi = ⊤ := by
      by_contra hyi_top
      exact hyi (mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hyi_top))
    have hrest_ne_bot :
        (∑ j ∈ Finset.univ.erase m, g j ((Function.update zPrev m yi) j)) ≠ ⊥ := by
      exact
        ereal_sum_ne_bot
          (Finset.univ.erase m)
          (fun j ↦ g j ((Function.update zPrev m yi) j))
          (fun j _ ↦ (hmodel.g_proper j).ne_bot _)
    have hsum_top : separableSum g (Function.update zPrev m yi) = ⊤ := by
      -- An infeasible block competitor forces the separable penalty sum to be `⊤`.
      rw [separableSum_apply]
      calc
        ∑ j : Fin p, g j ((Function.update zPrev m yi) j) =
            g m ((Function.update zPrev m yi) m) +
              ∑ j ∈ Finset.univ.erase m, g j ((Function.update zPrev m yi) j) := by
              symm
              exact
                Finset.add_sum_erase
                  Finset.univ
                  (fun j ↦ g j ((Function.update zPrev m yi) j))
                  (Finset.mem_univ m)
        _ = ⊤ := by
              rw [show g m ((Function.update zPrev m yi) m) = ⊤ by simpa [Function.update] using hyi_top,
                EReal.top_add_of_ne_bot hrest_ne_bot]
    have hy_top : F (Function.update zPrev m yi) = ⊤ := by
      rw [composite_model_objective_apply, hsum_top]
      exact EReal.add_top_of_ne_bot (hmodel.f_ne_bot _)
    -- In the infeasible branch the competitor value is `⊤`, so minimality is immediate.
    calc
      F (Function.update zPrev m (zPrev m)) = F zPrev := by simp
      _ ≤ F (Function.update zPrev m yi) := by simpa [hy_top] using (le_top : F zPrev ≤ ⊤)

/-- Helper for Theorem 14.5: for any finite stage depth `N`, one can refine the cluster-point
subsequence so that stage `N` converges to a point `z N`, while every earlier stage transition in
that refined chain is recorded as an exact one-block update preserving the objective value. -/
private lemma alternatingMinimizationStageChain
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hclosed : LowerSemicontinuous F)
    (hcont : ContinuousOn F (effective_domain F))
    (hlevels : ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar : (i : Fin p) → Ei i}
    (hxBar_dom : xBar ∈ effective_domain F)
    (hxBar : MapClusterPt xBar atTop x) :
    ∀ N, ∀ hN : N ≤ p,
      ∃ ψ : ℕ → ℕ, ∃ z : ℕ → ((i : Fin p) → Ei i),
        StrictMono ψ ∧
          Tendsto (fun m ↦ x (ψ m)) atTop (𝓝 xBar) ∧
          Tendsto (fun m ↦ alternating_minimization_prefix_state x (ψ m) N)
            atTop
            (𝓝 (z N)) ∧
          z 0 = xBar ∧
          F (z N) = F xBar ∧
          ∀ l, ∀ hl : l < N,
            let i : Fin p := ⟨l, lt_of_lt_of_le hl hN⟩
            z (l + 1) = Function.update (z l) i (z (l + 1) i) ∧
              z (l + 1) i ∈ alternating_minimization_argmin F (z l) i ∧
              F (z (l + 1)) = F (z l) := by
  intro N hN
  induction N with
  | zero =>
      rcases MapClusterPt.tendsto_subseq hxBar with ⟨ψ, hψ, hiter⟩
      -- At stage `0`, the prefix state is the iterate itself, so the chain is constant at `xBar`.
      refine ⟨ψ, fun _ ↦ xBar, hψ, hiter, ?_, rfl, rfl, ?_⟩
      · simpa using hiter
      · intro l hl
        exact (Nat.not_lt_zero _ hl).elim
  | succ N ih =>
      have hNle : N ≤ p := Nat.le_of_succ_le hN
      have hNlt : N < p := Nat.lt_of_succ_le hN
      rcases ih hNle with
        ⟨ψ, z, hψ, hiter, hstage, hz0, hvalue, hblocks⟩
      have hzN : z N ∈ effective_domain F := by
        -- Every recorded stage value stays on the initial cluster-point objective level.
        refine mem_effective_domain.mpr ?_
        simpa [hvalue] using mem_effective_domain.mp hxBar_dom
      let i : Fin p := ⟨N, hNlt⟩
      rcases alternatingMinimizationStageStepLimitPackage
          (f := f)
          (g := g)
          (x := x)
          hmodel
          hclosed
          hcont
          hlevels
          htraj
          (xBar := xBar)
          (z := z N)
          (ψ := ψ)
          hψ
          hxBar_dom
          hiter
          hzN
          hvalue
          i
          hstage with
        ⟨ψ', zNext, hψ', hiter', hnext, hupdate, hargmin, hvalueNext⟩
      let z' : ℕ → ((i : Fin p) → Ei i) := Function.update z (N + 1) zNext
      refine ⟨ψ', z', hψ', hiter', ?_, ?_, ?_, ?_⟩
      · -- The refined subsequence now records the new stage `N + 1` limit.
        simpa [z'] using hnext
      · -- Earlier stages are untouched by updating only the new index `N + 1`.
        simpa [z', Function.update] using hz0
      · -- The new endpoint still lies on the same objective level as `xBar`.
        calc
          F (z' (N + 1)) = F zNext := by simp [z']
          _ = F (z N) := hvalueNext
          _ = F xBar := hvalue
      · intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlN | rfl
        · -- Route correction: preserve the previously recorded stage history verbatim.
          have hl_neN : l ≠ N := Nat.ne_of_lt hlN
          have hl_ne : l ≠ N + 1 := Nat.ne_of_lt (Nat.lt_trans hlN (Nat.lt_succ_self N))
          simpa [z', Function.update, hl_neN, hl_ne] using hblocks l hlN
        · -- Append the new stage certificate returned by the one-step package.
          simpa [z', i, Function.update] using ⟨hupdate, hargmin, hvalueNext⟩

/-- Helper for Theorem 14.5: every target block of a cluster point belongs to the fixed-base
alternating-minimization argmin set at that cluster point. -/
private lemma alternatingMinimizationClusterPointBlockArgmin
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hclosed : LowerSemicontinuous F)
    (hcont : ContinuousOn F (effective_domain F))
    (hlevels : ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar : (i : Fin p) → Ei i}
    (hxBar_dom : xBar ∈ effective_domain F)
    (hxBar : MapClusterPt xBar atTop x)
    (m : Fin p) :
    xBar m ∈ alternating_minimization_argmin F xBar m := by
  rcases alternatingMinimizationStageChain
      (f := f)
      (g := g)
      (x := x)
      hmodel
      hclosed
      hcont
      hlevels
      htraj
      hxBar_dom
      hxBar
      (m.1 + 1)
      (Nat.succ_le_of_lt m.is_lt) with
    ⟨ψ, z, hψ, hiter, hstage, hz0, hvalue, hblocks⟩
  have hmStage :
      z (m.1 + 1) = Function.update (z m.1) m (z (m.1 + 1) m) ∧
        z (m.1 + 1) m ∈ alternating_minimization_argmin F (z m.1) m ∧
        F (z (m.1 + 1)) = F (z m.1) := by
    -- The stage-chain certificate at `l = m` is the starting point for the backward transport.
    simpa using hblocks m.1 (Nat.lt_succ_self m.1)
  rcases hmStage with ⟨hmUpdate, hmArg, hmValue⟩
  have hmSuccDom : z (m.1 + 1) ∈ effective_domain F := by
    -- The final stage of the chain stays on the cluster-point objective level.
    refine mem_effective_domain.mpr ?_
    simpa [hvalue] using mem_effective_domain.mp hxBar_dom
  have hmDom : z m.1 ∈ effective_domain F := by
    -- The stage-`m` point has the same objective value as the stage-`m+1` update.
    refine mem_effective_domain.mpr ?_
    simpa [hmValue] using mem_effective_domain.mp hmSuccDom
  have hmBase :
      z m.1 m ∈ alternating_minimization_argmin F (z m.1) m :=
    let hmValueUpdate :
        F (Function.update (z m.1) m (z (m.1 + 1) m)) = F (z m.1) := by
      exact hmUpdate ▸ hmValue
    alternating_minimization_base_coordinate_mem_argmin_of_limit
      F
      (z m.1)
      (z (m.1 + 1))
      m
      hmArg
      hmValueUpdate
  have hzero :
      z 0 ∈ effective_domain F ∧ z 0 m ∈ alternating_minimization_argmin F (z 0) m := by
    refine Nat.decreasingInduction' (m := 0) (n := m.1) ?_ (Nat.zero_le m.1) ?_
    · intro k hk _ hkNext
      let l : Fin p := ⟨k, Nat.lt_trans hk m.is_lt⟩
      have hkStage :
          z (k + 1) = Function.update (z k) l (z (k + 1) l) ∧
            z (k + 1) l ∈ alternating_minimization_argmin F (z k) l ∧
            F (z (k + 1)) = F (z k) := by
        -- Read the recorded step at stage `k` using the common refined subsequence.
        simpa [l] using hblocks k (Nat.lt_succ_of_lt hk)
      rcases hkStage with ⟨hkUpdate, hkArg, hkValue⟩
      have hkArgSelf :
          z (k + 1) l ∈ alternating_minimization_argmin F (z (k + 1)) l := by
        -- The stored block-`l` argmin can be switched to the self-updated base.
        exact
          (alternatingMinimizationArgminBaseInvariantOfSelfUpdate
            (f := f)
            (g := g)
            hkUpdate).1 hkArg
      have hkDom : z k ∈ effective_domain F := by
        -- Equal objective values transport effective-domain membership backward one stage.
        refine mem_effective_domain.mpr ?_
        simpa [hkValue] using mem_effective_domain.mp hkNext.1
      exact
        ⟨hkDom,
          alternatingMinimizationTransportExactBlockArgminBackward
            (f := f)
            (g := g)
            hmodel
            hf_convex
            hk
            hkDom
            hkNext.1
            hkUpdate
            hkValue
            hkArgSelf
            hkNext.2⟩
    · exact ⟨hmDom, hmBase⟩
  -- The stage chain starts at `z 0 = xBar`, so the transported block argmin lives at `xBar`.
  simpa [hz0] using hzero.2

/-- Theorem 14.5 optimality half: under the Chapter 14.5 hypotheses, every sequential cluster
point of the alternating-minimization trajectory globally minimizes the composite objective `F`. -/
theorem alternating_minimization_cluster_point_is_global_minimizer
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hlevels : ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar : (i : Fin p) → Ei i} (hxBar : MapClusterPt xBar atTop x) :
    IsMinOn F Set.univ xBar := by
  rcases alternatingMinimizationCompositeObjectiveRegular (f := f) (g := g) hmodel with
    ⟨hclosed, hcont⟩
  have hxBar_dom :
      xBar ∈ effective_domain F :=
    AlternatingMinimization.ClusterPoint.mem_effective_domain_of_initial_sublevel
      F x hclosed htraj hxBar
  have hcoord : is_coordinatewise_minimum F xBar := by
    refine ⟨hxBar_dom, ?_⟩
    intro m
    -- Each block of the cluster point solves its fixed-base one-block problem by the refined
    -- stage-chain construction and backward transport of exact later-stage optimality.
    exact (mem_alternating_minimization_argmin_iff).1 <|
        alternatingMinimizationClusterPointBlockArgmin
          (f := f)
          (g := g)
          (x := x)
          hmodel
          hf_convex
          hclosed
          hcont
          hlevels
          htraj
          hxBar_dom
          hxBar
          m
  -- Once the cluster point is coordinatewise minimal, the convex Chapter 3 bridge gives global
  -- optimality immediately.
  exact
    alternating_minimization_coordinatewise_minimum_is_global_minimizer
      f
      g
      hmodel
      hf_convex
      hcoord

/-- Under the Chapter 14.5 hypotheses, every sequential cluster point of the alternating-
minimization trajectory belongs to the unconstrained solution set of `F`. -/
theorem alternating_minimization_cluster_point_mem_solution_set
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hlevels : ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (htraj : is_alternating_minimization_trajectory F x)
    {xBar : (i : Fin p) → Ei i} (hxBar : MapClusterPt xBar atTop x) :
    xBar ∈ unconstrained_problem_solutions F := by
  rw [mem_unconstrained_problem_solutions_iff]
  exact alternating_minimization_cluster_point_is_global_minimizer
    f g x hmodel hf_convex hlevels htraj hxBar

/-- Source-facing wrapper for Theorem 14.5: under Assumption 14.6 for the composite objective
`F(x) = f(x) + ∑ i, g_i(x_i)`, if `f` is convex and every real sublevel set
`{y | F y ≤ α}` is bounded, then every alternating-minimization trajectory is bounded and each of
its cluster points is a global minimizer of `F`. The standing owner
`IsAlternatingMinimizationCompositeModel f.toEReal g` supplies the regularity used by the Chapter
14 to Chapter 3 optimality bridge, while the finite-dimensional inner-product ambient hypotheses
needed for that bridge stay explicit in this file. -/
theorem alternating_minimization_bounded_and_cluster_points_optimal
    (hmodel : IsAlternatingMinimizationCompositeModel f.toEReal g)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hlevels : ∀ α : ℝ, Bornology.IsBounded {y | F y ≤ (α : EReal)})
    (htraj : is_alternating_minimization_trajectory F x) :
    Bornology.IsBounded (Set.range x) ∧
      ∀ ⦃xBar : (i : Fin p) → Ei i⦄,
        MapClusterPt xBar atTop x →
          IsMinOn F Set.univ xBar := by
  constructor
  · -- The boundedness half is already the canonical owner from Theorem 14.3.
    exact alternating_minimization_trajectory_range_bounded F x hlevels htraj
  · intro xBar hxBar
    -- The remaining work is exactly the cluster-point optimality bridge proved above.
    exact alternating_minimization_cluster_point_is_global_minimizer
      f g x hmodel hf_convex hlevels htraj hxBar

end

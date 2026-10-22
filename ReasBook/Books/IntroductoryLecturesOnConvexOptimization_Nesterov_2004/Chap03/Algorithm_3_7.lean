/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_51
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_52
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_54
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory

universe u

section Ambient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance instMeasurableSpaceAlgorithm37 : MeasurableSpace E := borel E
local instance instBorelSpaceAlgorithm37 : BorelSpace E := ⟨rfl⟩

/- Primary domain: centroid-based cutting methods for bounded convex minimization on a finite-
dimensional real inner-product space.

Relevant owner-style declarations sampled before refinement:
- `ConvexMinimizationWithSeparationOracle` in `Definition_3_51` for the ambient bounded closed
  convex feasible set with nonempty interior and its feasible-point subgradient guarantee;
- `GeneralCuttingPlaneScheme` and `cuttingHalfspace` in `Algorithm_3_6` for the chapter's
  canonical cutting-plane owner and retained affine half-space cut;
- `localizationSets` in `Definition_3_52` for the chapter's canonical recursive localization-set
  owner;
- `setAverage` in `Definition_3_54` for the iterate `x_k = ⨍ x in S_k, x`.

Best owner abstraction:
- source-facing layer: the recursive centroid localizers `S_k`, their centroids `x_k`, and the
  chosen feasible-point subgradients `g_k`;
- core/canonical layer: the owner feasible set `Q`, `GeneralCuttingPlaneScheme`,
  `cuttingHalfspace`, `setAverage`, and `localizationSets`;
- bridge/view layer: the induced `GeneralCuttingPlaneScheme` and the identification
  `S_k = localizationSets Q x g k`.

Primitive data:
- the owner bounded convex minimization problem with feasible-set geometry and oracle.

Derived API:
- the recursive localization sets `S_k`;
- the centroids `x_k = cg(S_k)`;
- the feasible-point cut vectors `g_k`;
- the admissibility invariant that every `S_k` is again a bounded closed convex body with nonempty
  interior, `x_k ∈ S_k`, and `S_k ⊆ Q`;
- the bridge to the chapter's `GeneralCuttingPlaneScheme` owner;
- the bridge to the canonical localization-set recursion.

Accordingly, this file keeps Algorithm 3.7 source-facing: the recursion is on centroid cuts inside
the feasible set, but the retained cut itself is expressed through the owner half-space
`cuttingHalfspace`; the owner oracle is used only through its feasible-point subgradient branch at
the recursively certified centroid iterates. -/

namespace CenterOfGravityMethod

variable (problem : ConvexMinimizationWithSeparationOracle E)

private structure State
    (problem : ConvexMinimizationWithSeparationOracle E) where
  localizer : ConvexBody E
  localizer_interior_nonempty : (interior (localizer : Set E)).Nonempty
  localizer_subset_feasibleSet : (localizer : Set E) ⊆ problem.feasibleSet

namespace State

variable {problem : ConvexMinimizationWithSeparationOracle E}

omit [FiniteDimensional ℝ E] in
private theorem localizer_compact (state : State problem) :
    IsCompact (state.localizer : Set E) :=
  state.localizer.isCompact

omit [FiniteDimensional ℝ E] in
private theorem localizer_bounded (state : State problem) :
    Bornology.IsBounded (state.localizer : Set E) :=
  state.localizer.isBounded

omit [FiniteDimensional ℝ E] in
private theorem localizer_closed (state : State problem) :
    IsClosed (state.localizer : Set E) :=
  state.localizer.isClosed

omit [FiniteDimensional ℝ E] in
private theorem localizer_convex (state : State problem) :
    Convex ℝ (state.localizer : Set E) :=
  state.localizer.convex

private def iterate (state : State problem) : E :=
  ⨍ x in (state.localizer : Set E), x

private theorem integrable_localizer (state : State problem) :
    Integrable (fun x : E ↦ x) (volume.restrict (state.localizer : Set E)) := by
  simpa [IntegrableOn] using
    continuous_id.continuousOn.integrableOn_compact (localizer_compact state)

private theorem iterate_mem_localizer (state : State problem) :
    state.iterate ∈ (state.localizer : Set E) := by
  exact
    (localizer_convex state).set_average_mem
      (localizer_closed state)
      ((isOpen_interior.measure_pos volume state.localizer_interior_nonempty).trans_le
        (measure_mono interior_subset)).ne'
      (localizer_compact state).measure_ne_top
      (ae_restrict_mem (localizer_closed state).measurableSet)
      state.integrable_localizer

private theorem iterate_mem_interior (state : State problem) :
    state.iterate ∈ interior (state.localizer : Set E) := by
  rcases state.localizer_interior_nonempty with ⟨x, hx⟩
  rcases Metric.isOpen_iff.mp isOpen_interior x hx with ⟨r, hr, hrball⟩
  let t : Set E := Metric.closedBall x (r / 2)
  have ht_subset_ball : t ⊆ Metric.ball x r := by
    intro y hy
    refine Metric.mem_ball.mpr ?_
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by nlinarith)
  have ht_subset_interior : t ⊆ interior (state.localizer : Set E) := by
    intro y hy
    exact hrball (ht_subset_ball hy)
  have ht_subset_localizer : t ⊆ (state.localizer : Set E) :=
    ht_subset_interior.trans interior_subset
  have ht_measurable : MeasurableSet t := Metric.isClosed_closedBall.measurableSet
  have hcompact_t : IsCompact t := by
    simpa [t] using isCompact_closedBall x (r / 2)
  have hμt_eq : (volume.restrict (state.localizer : Set E)) t = volume t := by
    rw [Measure.restrict_apply ht_measurable, Set.inter_eq_left.mpr ht_subset_localizer]
  have hμt_ne_zero : (volume.restrict (state.localizer : Set E)) t ≠ 0 := by
    rw [hμt_eq]
    exact (Metric.measure_closedBall_pos volume x (half_pos hr)).ne'
  have hμt_ne_top : (volume.restrict (state.localizer : Set E)) t ≠ ⊤ := by
    rw [hμt_eq]
    exact measure_closedBall_lt_top.ne
  have hmem_t :
      ∀ᵐ y ∂(volume.restrict (state.localizer : Set E)).restrict t,
        y ∈ Metric.closedBall x (r / 2) := by
    simpa [t] using
      (ae_restrict_mem ht_measurable :
        ∀ᵐ y ∂(volume.restrict (state.localizer : Set E)).restrict t, y ∈ t)
  have hintegrable_t :
      IntegrableOn (fun y : E ↦ y) t (volume.restrict (state.localizer : Set E)) := by
    simpa [t] using
      continuous_id.continuousOn.integrableOn_compact' hcompact_t ht_measurable
  have ht_average_mem_interior :
      (⨍ y in t, y ∂(volume.restrict (state.localizer : Set E))) ∈
        interior (state.localizer : Set E) := by
    exact ht_subset_interior <|
      (convex_closedBall x (r / 2)).set_average_mem
        Metric.isClosed_closedBall
        hμt_ne_zero
        hμt_ne_top
        hmem_t
        hintegrable_t
  have hlocalizer_measure_lt_top : volume (state.localizer : Set E) < ⊤ :=
    (localizer_compact state).measure_lt_top
  have hmem_localizer :
      ∀ᵐ y ∂volume.restrict (state.localizer : Set E), y ∈ (state.localizer : Set E) :=
    ae_restrict_mem (localizer_closed state).measurableSet
  haveI : IsFiniteMeasure (volume.restrict (state.localizer : Set E)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hlocalizer_measure_lt_top⟩
  simpa using
    (localizer_convex state).average_mem_interior_of_set
      hμt_ne_zero
      hmem_localizer
      state.integrable_localizer
      ht_average_mem_interior

private def cuttingVector (state : State problem) : E :=
  problem.oracle.oracle state.iterate

private def next (state : State problem) : State problem :=
  let nextLocalizer : Set E :=
    (state.localizer : Set E) ∩ cuttingHalfspace state.iterate state.cuttingVector
  have hnext_interior_nonempty : (interior nextLocalizer).Nonempty := by
    by_cases hg : state.cuttingVector = 0
    · have hcut :
          nextLocalizer = (state.localizer : Set E) := by
        ext x
        simp [nextLocalizer, cuttingHalfspace, hg]
      simpa [hcut] using state.localizer_interior_nonempty
    · let c := state.iterate
      have hc : c ∈ interior (state.localizer : Set E) := state.iterate_mem_interior
      rcases Metric.isOpen_iff.mp isOpen_interior c hc with ⟨r, hr, hrball⟩
      let xBar : E := c - (r / 2) • ((‖state.cuttingVector‖⁻¹ : ℝ) • state.cuttingVector)
      have hxBar_mem_interior : xBar ∈ interior (state.localizer : Set E) := by
        apply hrball
        refine Metric.mem_ball.mpr <| by
          have hunit : ‖((‖state.cuttingVector‖⁻¹ : ℝ) • state.cuttingVector)‖ = 1 :=
            norm_smul_inv_norm hg
          calc
            dist xBar c = ‖(r / 2) • ((‖state.cuttingVector‖⁻¹ : ℝ) • state.cuttingVector)‖ := by
              simp [xBar, c]
            _ = r / 2 := by
              rw [norm_smul, hunit, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
            _ < r := by nlinarith
      have hxBar_pos :
          0 < inner ℝ state.cuttingVector (c - xBar) := by
        have hcx :
            c - xBar = (r / 2) • ((‖state.cuttingVector‖⁻¹ : ℝ) • state.cuttingVector) := by
          simp [xBar, c]
        rw [hcx, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
        have hnorm : 0 < ‖state.cuttingVector‖ := norm_pos_iff.mpr hg
        positivity
      have hxBar_mem_open :
          xBar ∈ {x : E | 0 < inner ℝ state.cuttingVector (c - x)} :=
        hxBar_pos
      have hopen : IsOpen {x : E | 0 < inner ℝ state.cuttingVector (c - x)} :=
        isOpen_lt continuous_const (continuous_const.inner (continuous_const.sub continuous_id))
      refine ⟨xBar, mem_interior_iff_mem_nhds.mpr ?_⟩
      refine Filter.mem_of_superset
        (Filter.inter_mem (mem_interior_iff_mem_nhds.mp hxBar_mem_interior)
          (hopen.mem_nhds hxBar_mem_open))
        ?_
      intro y hy
      refine ⟨hy.1, ?_⟩
      have hycut : 0 ≤ inner ℝ state.cuttingVector (c - y) := hy.2.le
      simpa [cuttingHalfspace, inner_sub_right, sub_nonneg] using hycut
  { localizer :=
      ⟨nextLocalizer,
        state.localizer_convex.inter
          (cuttingHalfspace_convex state.iterate state.cuttingVector),
        state.localizer_compact.inter_right
          (cuttingHalfspace_closed state.iterate state.cuttingVector),
        by
          rcases hnext_interior_nonempty with ⟨x, hx⟩
          exact ⟨x, interior_subset hx⟩⟩
    localizer_interior_nonempty := hnext_interior_nonempty
    localizer_subset_feasibleSet := by
      intro x hx
      exact state.localizer_subset_feasibleSet hx.1 }

end State

private def state : ℕ → State problem
  | 0 =>
      { localizer :=
          ⟨problem.feasibleSet,
            problem.feasibleSet_convex,
            Metric.isCompact_of_isClosed_isBounded
              problem.feasibleSet_closed
              problem.feasibleSet_bounded,
            problem.feasibleSet_nonempty⟩
        localizer_interior_nonempty := problem.feasibleSet_interior_nonempty
        localizer_subset_feasibleSet := by
          intro x hx
          exact hx }
  | k + 1 => (state k).next

/-- The iterate sequence `x_k = cg(S_k)` induced by the centroid localizers. -/
def iterate
    (problem : ConvexMinimizationWithSeparationOracle E)
    (k : ℕ) : E :=
  (state problem k).iterate

/-- The cut vector `g_k` of Algorithm 3.7 is the owner oracle value at the centroid iterate
`x_k`. -/
def cuttingVector
    (problem : ConvexMinimizationWithSeparationOracle E)
    (k : ℕ) : E :=
  problem.oracle.oracle (iterate problem k)

/-- The centroid localization sets `S₀, S₁, ...` of Algorithm 3.7. -/
def localizer
    (problem : ConvexMinimizationWithSeparationOracle E)
    (k : ℕ) : Set E :=
  localizationSets problem.feasibleSet (iterate problem) (cuttingVector problem) k

private theorem state_localizer_eq_localizer (k : ℕ) :
    ((state problem k).localizer : Set E) = localizer problem k := by
  induction k with
  | zero =>
      simp [localizer, state]
  | succ k hk =>
      simp [localizer, state, State.next, localizationSets_succ, hk, iterate, cuttingVector,
        State.iterate, State.cuttingVector]

/-- The centroid localizer recursion starts at the feasible set `Q`. -/
theorem localizer_zero :
    localizer problem 0 = problem.feasibleSet :=
  by simp [localizer]

/-- Every localization set `S_k` remains bounded. -/
theorem localizer_bounded (k : ℕ) :
    Bornology.IsBounded (localizer problem k) := by
  simpa [state_localizer_eq_localizer problem k] using
    State.localizer_bounded (state problem k)

/-- Every localization set `S_k` remains closed. -/
theorem localizer_closed (k : ℕ) :
    IsClosed (localizer problem k) := by
  simpa [state_localizer_eq_localizer problem k] using
    State.localizer_closed (state problem k)

/-- Every localization set `S_k` remains convex. -/
theorem localizer_convex (k : ℕ) :
    Convex ℝ (localizer problem k) := by
  simpa [state_localizer_eq_localizer problem k] using
    State.localizer_convex (state problem k)

/-- Every localization set `S_k` keeps nonempty interior, so its centroid is taken on an
admissible convex body. -/
theorem localizer_interior_nonempty (k : ℕ) :
    (interior (localizer problem k)).Nonempty := by
  simpa [state_localizer_eq_localizer problem k] using
    (state problem k).localizer_interior_nonempty

/-- Every localization set `S_k` stays inside the feasible set `Q`. -/
theorem localizer_subset_feasibleSet (k : ℕ) :
    localizer problem k ⊆ problem.feasibleSet := by
  simpa [state_localizer_eq_localizer problem k] using
    (state problem k).localizer_subset_feasibleSet

/-- The current iterate is the centroid of the current localization set. -/
theorem iterate_eq_centerOfGravity_localizer (k : ℕ) :
    iterate problem k = (⨍ x in localizer problem k, x) :=
  by
    simp [iterate, State.iterate, state_localizer_eq_localizer problem k]

/-- The cut vector `g_k` is the owner oracle value at the centroid iterate `x_k`. -/
theorem cuttingVector_eq_oracle (k : ℕ) :
    cuttingVector problem k = problem.oracle.oracle (iterate problem k) :=
  rfl

/-- The current centroid iterate belongs to the current localization set. -/
theorem iterate_mem_localizer (k : ℕ) :
    iterate problem k ∈ localizer problem k := by
  simpa [iterate, state_localizer_eq_localizer problem k] using
    (state problem k).iterate_mem_localizer

/-- Every centroid iterate remains feasible. -/
theorem iterate_mem_feasibleSet (k : ℕ) :
    iterate problem k ∈ problem.feasibleSet :=
  localizer_subset_feasibleSet problem k (iterate_mem_localizer problem k)

/-- The successor localization set is the retained centroid cut
`S_{k+1} = S_k ∩ {x | ⟪g_k, x_k - x⟫ ≥ 0}`. -/
theorem localizer_succ (k : ℕ) :
    localizer problem (k + 1) =
      localizer problem k ∩ cuttingHalfspace (iterate problem k) (cuttingVector problem k) :=
  by simp [localizer, localizationSets_succ]

/-- At every centroid iterate, the cut vector `g_k` is a genuine subgradient of the objective. -/
theorem cuttingVector_isSubgradientAt (k : ℕ) :
    IsSubgradientAt (fun x ↦ (problem.objective x : WithTop ℝ))
      (iterate problem k) (cuttingVector problem k) := by
  simpa [cuttingVector] using problem.oracle.subgradient_spec (iterate_mem_feasibleSet problem k)

/-- The centroid localizers are exactly the owner recursive localization sets specialized to the
iterate sequence `x_k = cg(S_k)` and the cut vectors `g_k`. -/
theorem localizer_eq_localizationSets :
    localizer problem =
      localizationSets problem.feasibleSet (iterate problem) (cuttingVector problem) :=
  rfl

/-- Algorithm 3.7 viewed as the chapter's general cutting-plane owner abstraction. -/
def toGeneralCuttingPlaneScheme : GeneralCuttingPlaneScheme problem where
  localizer := localizer problem
  queryPoint := iterate problem
  initial_bounded := by
    simpa [localizer_zero] using localizer_bounded problem 0
  feasibleSet_subset_initial := by
    simp [localizer_zero]
  query_mem := iterate_mem_localizer problem
  next_localizer_contains := by
    intro k x hx
    simpa [localizer_succ, cuttingVector] using hx

/-- The induced cutting-plane scheme uses the same cut vectors `g_k` as Algorithm 3.7. -/
@[simp] theorem toGeneralCuttingPlaneScheme_cuttingVector (k : ℕ) :
    (toGeneralCuttingPlaneScheme problem).cuttingVector k = cuttingVector problem k :=
  by
    simp [GeneralCuttingPlaneScheme.cuttingVector, toGeneralCuttingPlaneScheme,
      cuttingVector]

end CenterOfGravityMethod

end Ambient

end

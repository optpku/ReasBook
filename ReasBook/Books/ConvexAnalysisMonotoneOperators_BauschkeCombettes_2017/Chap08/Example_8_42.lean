/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology Pointwise

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: apply the general fact `LinearMap.convexOn` to `f` and to `-f`, both on the
-- convex set `Set.univ`.
/-- Example 8.42 (1): textbook clause (i), first part. A real linear functional and its negative
are convex on the whole space. -/
theorem convexOn_univ_linearFunctional_and_neg (f : H →ₗ[ℝ] ℝ) :
    ConvexOn ℝ (Set.univ : Set H) f ∧
      ConvexOn ℝ (Set.univ : Set H) (-f) := by
  constructor
  · -- A linear functional is convex on every convex set, in particular on `univ`.
    simpa using f.convexOn (convex_univ : Convex ℝ (Set.univ : Set H))
  · -- The same convexity statement applies to the negated linear functional.
    simpa using (-f).convexOn (convex_univ : Convex ℝ (Set.univ : Set H))

-- Proof sketch: a real-valued linear functional, and likewise its negative, is finite everywhere,
-- so its `EReal` domain is all of `H`; the interior of `univ` is `univ`.
/-- Example 8.42 (2): textbook clause (i), second part. The effective domains of a real linear
functional and of its negative have full interior. -/
theorem interior_dom_linearFunctional_and_neg_eq_univ (f : H →ₗ[ℝ] ℝ) :
    interior (ERealFunction.dom fun x : H ↦ (f x : EReal)) = (Set.univ : Set H) ∧
      interior (ERealFunction.dom fun x : H ↦ (((-f) x : ℝ) : EReal)) = (Set.univ : Set H) := by
  constructor
  · -- Real-valued linear functionals take only finite `EReal` values, so the domain is `univ`.
    have hdom : ERealFunction.dom (fun x : H ↦ (f x : EReal)) = (Set.univ : Set H) := by
      ext x
      simp [ERealFunction.dom]
    simp [hdom]
  · -- The same finiteness argument applies to the negated functional.
    have hdom : ERealFunction.dom (fun x : H ↦ (((-f) x : ℝ) : EReal)) = (Set.univ : Set H) := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        rw [ERealFunction.mem_dom_iff]
        simpa using (EReal.coe_lt_top (((-f) x : ℝ)))
    simpa [hdom]

-- Proof sketch: the first equality is exactly the assumption that `f` is discontinuous at every
-- point. For `-f`, use that negation is continuous, so `ContinuousAt (fun y ↦ -f y) x` is
-- equivalent to `ContinuousAt f x`.
/-- Example 8.42 (3): textbook clause (i), third part. A linear functional that is discontinuous at
every point, and likewise its negative, has no continuity points. -/
theorem continuityPoints_linearFunctional_and_neg_eq_empty_of_everywhereDiscontinuous
    (f : H →ₗ[ℝ] ℝ) (hdisc : ∀ x : H, ¬ ContinuousAt f x) :
    {x : H | ContinuousAt f x} = (∅ : Set H) ∧
      {x : H | ContinuousAt (fun y : H ↦ -f y) x} = (∅ : Set H) := by
  constructor
  · ext x
    -- The first continuity set is empty by the standing nowhere-continuity hypothesis.
    simp [hdisc x]
  · ext x
    -- Negation is continuous, so continuity of `-f` is equivalent to continuity of `f`.
    constructor
    · intro hx
      have hxNeg : ContinuousAt (-(f : H → ℝ)) x := by
        simpa only [Pi.neg_apply] using hx
      have hx' : ContinuousAt (f : H → ℝ) x := by
        simpa using (continuousAt_neg_iff.mp hxNeg)
      exact hdisc x hx'
    · intro hx
      exact False.elim hx

/-- Helper for Example 8.42: lower semicontinuity of a real linear functional yields an
upper-bound neighborhood at the origin by applying the lower bound to both `x` and `-x`. -/
theorem isBoundedUnder_nhds_zero_of_lowerSemicontinuous
    (f : H →ₗ[ℝ] ℝ) (hlsc : LowerSemicontinuous (f : H → ℝ)) :
    Filter.IsBoundedUnder (· ≤ ·) (𝓝 (0 : H)) f := by
  rw [lowerSemicontinuous_iff] at hlsc
  have hzero := hlsc 0
  rw [lowerSemicontinuousAt_iff] at hzero
  have hLower : {x : H | (-1 : ℝ) < f x} ∈ 𝓝 (0 : H) := by
    -- Apply lower semicontinuity at the threshold `-1 < f 0 = 0`.
    simpa using hzero (-1) (by simp)
  have hLowerNeg : {x : H | (-1 : ℝ) < f (-x)} ∈ 𝓝 (0 : H) := by
    -- Pull the same neighborhood back along the continuous negation map.
    have hnegCont : ContinuousAt (fun x : H ↦ -x) (0 : H) := continuous_neg.continuousAt
    have hLowerAtNeg0 : {x : H | (-1 : ℝ) < f x} ∈ 𝓝 ((fun x : H ↦ -x) (0 : H)) := by
      simpa using hLower
    simpa using hnegCont.preimage_mem_nhds hLowerAtNeg0
  have hUpperSet : {x : H | f x ≤ 1} ∈ 𝓝 (0 : H) := by
    -- Combining the lower bounds at `x` and `-x` gives an upper bound at `x`.
    filter_upwards [hLower, hLowerNeg] with x hx hxneg
    have hxneg' : (-1 : ℝ) < -f x := by
      simpa using hxneg
    linarith
  refine BddAbove.isBoundedUnder hUpperSet ?_
  -- On this neighborhood, every value is bounded above by `1`.
  refine ⟨1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hx

-- Proof sketch: lower semicontinuity together with convexity would force continuity on the
-- interior of the domain, which is all of `H` by the previous clause. Applying the same argument
-- to `-f` yields the failure of upper semicontinuity for `f`.
/-- Example 8.42 (4): textbook clause (ii). A real linear functional that is discontinuous at every
point is neither lower semicontinuous nor upper semicontinuous. -/
theorem not_lowerSemicontinuous_and_not_upperSemicontinuous_of_everywhereDiscontinuous
    (f : H →ₗ[ℝ] ℝ) (hdisc : ∀ x : H, ¬ ContinuousAt f x) :
    ¬ LowerSemicontinuous (f : H → ℝ) ∧
      ¬ UpperSemicontinuous (f : H → ℝ) := by
  rcases convexOn_univ_linearFunctional_and_neg f with ⟨hconv, hconvNeg⟩
  constructor
  · intro hlsc
    have hbounded : Filter.IsBoundedUnder (· ≤ ·) (𝓝 (0 : H)) f :=
      isBoundedUnder_nhds_zero_of_lowerSemicontinuous f hlsc
    have hcontOn : ContinuousOn (f : H → ℝ) Set.univ := by
      -- A local upper bound on an open convex domain forces continuity on the whole domain.
      have hlocal :
          ∃ x0 ∈ (Set.univ : Set H), Filter.IsBoundedUnder (· ≤ ·) (𝓝 x0) f :=
        ⟨0, by simp, hbounded⟩
      exact ((hconv.continuousOn_tfae isOpen_univ Set.univ_nonempty).out 3 1).mp hlocal
    exact hdisc 0 <| by
      simpa using hcontOn.continuousAt <|
        isOpen_univ.mem_nhds (by simp : (0 : H) ∈ (Set.univ : Set H))
  · intro husc
    have hneg_lsc : LowerSemicontinuous (fun x : H ↦ ((-f) x : ℝ)) := husc.neg
    have hboundedNeg : Filter.IsBoundedUnder (· ≤ ·) (𝓝 (0 : H)) (fun x : H ↦ ((-f) x : ℝ)) :=
      isBoundedUnder_nhds_zero_of_lowerSemicontinuous (-f) hneg_lsc
    have hcontOnNeg : ContinuousOn (fun x : H ↦ ((-f) x : ℝ)) Set.univ := by
      -- Apply the same convex continuity criterion to `-f`.
      have hlocal :
          ∃ x0 ∈ (Set.univ : Set H),
            Filter.IsBoundedUnder (· ≤ ·) (𝓝 x0) (fun x : H ↦ ((-f) x : ℝ)) :=
        ⟨0, by simp, hboundedNeg⟩
      exact ((hconvNeg.continuousOn_tfae isOpen_univ Set.univ_nonempty).out 3 1).mp hlocal
    have hcontNeg : ContinuousAt (fun x : H ↦ ((-f) x : ℝ)) 0 := by
      simpa using hcontOnNeg.continuousAt
        (isOpen_univ.mem_nhds (by simp : (0 : H) ∈ (Set.univ : Set H)))
    exact hdisc 0 <| by
      simpa using (continuousAt_neg_iff.mp hcontNeg)

-- Proof sketch: the set `{x | f x ≤ 1}` is a closed halfspace cut out by a linear functional, so
-- convexity follows directly from linearity.
/-- Example 8.42 (5): textbook clause (iii), first part. The sublevel set
`{x | f x ≤ 1}` of a real linear functional is convex. -/
theorem convex_oneSublevelSet_linearFunctional (f : H →ₗ[ℝ] ℝ) :
    Convex ℝ {x : H | f x ≤ 1} := by
  -- A lower level set of a convex function is convex.
  simpa using (convexOn_univ_linearFunctional_and_neg f).1.convex_le (1 : ℝ)

/-- Helper for Example 8.42: every vector is a positive multiple of a point in the one-sublevel set
of a linear functional. -/
theorem oneSublevelSet_pos_factorization (f : H →ₗ[ℝ] ℝ) (x : H) :
    ∃ y ∈ {z : H | f z ≤ 1}, ∃ a : ℝ, 0 < a ∧ x = a • y := by
  by_cases hx : f x ≤ 1
  · -- If `x` already lies in the sublevel set, use the trivial factorization with scalar `1`.
    exact ⟨x, hx, 1, by positivity, by simp⟩
  · have hfx_pos : 0 < f x := by
      have : ¬ f x ≤ 1 := hx
      linarith [show f (0 : H) = 0 by simp]
    refine ⟨(f x)⁻¹ • x, ?_, f x, hfx_pos, ?_⟩
    · -- Scaling by `1 / f x` lands exactly on the level set `f = 1`.
      have hlevel : f ((f x)⁻¹ • x) = 1 := by
        simpa [LinearMap.map_smul, smul_eq_mul] using inv_mul_cancel₀ hfx_pos.ne'
      exact le_of_eq hlevel
    · -- Multiplying back by `f x` recovers the original vector.
      calc
        x = (1 : ℝ) • x := by simp
        _ = (f x * (f x)⁻¹) • x := by
          simp [mul_inv_cancel₀ hfx_pos.ne']
        _ = f x • ((f x)⁻¹ • x) := by rw [smul_smul]

-- Proof sketch: if `x ∈ C`, then the segment `[0,x]` lies in `C`; if `x ∉ C`, scale `x` by the
-- positive factor `1 / f x` to land on the boundary of `C`. Hence the cone generated by
-- `C - {0}` is all of `H`, which is exactly the core condition at the origin.
/-- Example 8.42 (6): textbook clause (iii), second part. The origin belongs to the core of the
sublevel set `{x | f x ≤ 1}`. -/
theorem zero_mem_core_oneSublevelSet_linearFunctional (f : H →ₗ[ℝ] ℝ) :
    (0 : H) ∈ Set.core {x : H | f x ≤ 1} := by
  rw [Set.mem_core_iff]
  constructor
  · -- The origin belongs to the one-sublevel set because `f 0 = 0`.
    simp
  · ext x
    constructor
    · -- Any element of the conical hull is, by definition, a vector in the ambient space.
      intro _
      simp
    · intro _
      -- Use the positive-scalar factorization to place `x` in the conical hull of the translate.
      change x ∈
        (ConvexCone.hull ℝ ({z : H | f z ≤ 1} - ({(0 : H)} : Set H)) : Set H)
      rcases oneSublevelSet_pos_factorization f x with ⟨y, hy, a, ha, rfl⟩
      have hy' : y ∈ {z : H | f z ≤ 1} - ({(0 : H)} : Set H) := by
        exact Set.mem_sub.mpr ⟨y, hy, 0, by simp, by simp⟩
      exact (ConvexCone.hull ℝ ({z : H | f z ≤ 1} - ({(0 : H)} : Set H))).smul_mem ha
        (ConvexCone.subset_hull hy')

-- Proof sketch: if the sublevel set had nonempty interior, then `f` would be locally bounded above
-- on some neighborhood, and convex-function continuity would force `f` to be continuous there,
-- contradicting everywhere discontinuity.
/-- Example 8.42 (7): textbook clause (iii), third part. If a real linear functional is
discontinuous at every point, then the sublevel set `{x | f x ≤ 1}` has empty interior. -/
theorem interior_oneSublevelSet_linearFunctional_eq_empty_of_everywhereDiscontinuous
    (f : H →ₗ[ℝ] ℝ) (hdisc : ∀ x : H, ¬ ContinuousAt f x) :
    interior {x : H | f x ≤ 1} = (∅ : Set H) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx) with ⟨ρ, hρ, hball⟩
    have hbounded : Filter.IsBoundedUnder (· ≤ ·) (𝓝 x) f := by
      -- An interior ball in the sublevel set gives a neighborhood where `f ≤ 1`.
      refine BddAbove.isBoundedUnder (Metric.ball_mem_nhds x hρ) ?_
      refine ⟨1, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hball hy
    have hcontOn : ContinuousOn (f : H → ℝ) Set.univ := by
      -- Local boundedness contradicts the assumption that `f` is nowhere continuous.
      have hlocal :
          ∃ x0 ∈ (Set.univ : Set H), Filter.IsBoundedUnder (· ≤ ·) (𝓝 x0) f :=
        ⟨x, by simp, hbounded⟩
      exact (((convexOn_univ_linearFunctional_and_neg f).1.continuousOn_tfae
        isOpen_univ Set.univ_nonempty).out 3 1).mp hlocal
    exact False.elim <| hdisc x <| by
      simpa using hcontOn.continuousAt
        (isOpen_univ.mem_nhds (by simp : x ∈ (Set.univ : Set H)))
  · intro x hx
    exact False.elim hx

-- Proof sketch: if `f '' U` were bounded above or below on a nonempty open set, then `f` would be
-- locally bounded on some neighborhood and therefore continuous there, contradicting the
-- assumption that it is discontinuous everywhere.
/-- Example 8.42 (8): textbook clause (iv). On every nonempty open subset, a real linear
functional that is discontinuous at every point is unbounded above and unbounded below. -/
theorem image_not_bddAbove_and_not_bddBelow_of_isOpen_of_nonempty_of_everywhereDiscontinuous
    (f : H →ₗ[ℝ] ℝ) (hdisc : ∀ x : H, ¬ ContinuousAt f x) {U : Set H}
    (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) :
    ¬ BddAbove (f '' U) ∧ ¬ BddBelow (f '' U) := by
  rcases hU_nonempty with ⟨x, hxU⟩
  rcases convexOn_univ_linearFunctional_and_neg f with ⟨hconv, hconvNeg⟩
  constructor
  · intro hBA
    have hbounded : Filter.IsBoundedUnder (· ≤ ·) (𝓝 x) f :=
      BddAbove.isBoundedUnder (hU_open.mem_nhds hxU) hBA
    have hcontOn : ContinuousOn (f : H → ℝ) Set.univ := by
      -- An upper bound on `U` gives the local boundedness needed for convex continuity.
      have hlocal :
          ∃ x0 ∈ (Set.univ : Set H), Filter.IsBoundedUnder (· ≤ ·) (𝓝 x0) f :=
        ⟨x, by simp, hbounded⟩
      exact ((hconv.continuousOn_tfae isOpen_univ Set.univ_nonempty).out 3 1).mp hlocal
    exact hdisc x <| by
      simpa using hcontOn.continuousAt (isOpen_univ.mem_nhds (by simp : x ∈ (Set.univ : Set H)))
  · intro hBB
    have hnegBA : BddAbove ((fun y : H ↦ ((-f) y : ℝ)) '' U) := by
      -- A lower bound for `f` is an upper bound for `-f`.
      rcases hBB with ⟨m, hm⟩
      refine ⟨-m, ?_⟩
      rintro _ ⟨y, hyU, rfl⟩
      have hmy : m ≤ f y := hm ⟨y, hyU, rfl⟩
      simpa using (neg_le_neg hmy)
    have hboundedNeg : Filter.IsBoundedUnder (· ≤ ·) (𝓝 x) (fun y : H ↦ ((-f) y : ℝ)) :=
      BddAbove.isBoundedUnder (hU_open.mem_nhds hxU) hnegBA
    have hcontOnNeg : ContinuousOn (fun y : H ↦ ((-f) y : ℝ)) Set.univ := by
      -- Apply the same argument to `-f`.
      have hlocal :
          ∃ x0 ∈ (Set.univ : Set H),
            Filter.IsBoundedUnder (· ≤ ·) (𝓝 x0) (fun y : H ↦ ((-f) y : ℝ)) :=
        ⟨x, by simp, hboundedNeg⟩
      exact ((hconvNeg.continuousOn_tfae isOpen_univ Set.univ_nonempty).out 3 1).mp hlocal
    have hcontNeg : ContinuousAt (fun y : H ↦ ((-f) y : ℝ)) x := by
      simpa using hcontOnNeg.continuousAt
        (isOpen_univ.mem_nhds (by simp : x ∈ (Set.univ : Set H)))
    exact hdisc x <| by
      simpa using (continuousAt_neg_iff.mp hcontNeg)

/-- Helper for Example 8.42: opposite signs at two points produce an affine combination in the
kernel of the linear functional. -/
theorem exists_kernel_point_on_segment_of_opposite_sign
    (f : H →ₗ[ℝ] ℝ) {yNeg yPos : H} (hyNeg : f yNeg < 0) (hyPos : 0 < f yPos) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ f (t • yNeg + (1 - t) • yPos) = 0 := by
  let t : ℝ := f yPos / (f yPos - f yNeg)
  have hden_pos : 0 < f yPos - f yNeg := by
    linarith
  have ht_pos : 0 < t := by
    dsimp [t]
    exact div_pos hyPos hden_pos
  have ht_lt_one : t < 1 := by
    dsimp [t]
    refine (div_lt_one hden_pos).2 ?_
    linarith
  refine ⟨t, ht_pos, ht_lt_one, ?_⟩
  -- The chosen coefficient makes the linear interpolation cancel exactly.
  have hden_ne : f yPos - f yNeg ≠ 0 := by
    linarith
  have hscalar :
      t * f yNeg + (1 - t) * f yPos = 0 := by
    dsimp [t]
    field_simp [hden_ne]
    ring
  simpa [LinearMap.map_add, LinearMap.map_smul, mul_comm, mul_left_comm, mul_assoc] using hscalar

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: a discontinuous linear functional on a real topological vector space has dense
-- kernel by the closed-or-dense kernel dichotomy, since a closed kernel would make the functional
-- continuous. The same assumption rules out `f = 0`, so the kernel is also a hyperplane.
/-- Example 8.42 (9): textbook clause (v). The kernel `{x | f x = 0}` of a real linear functional
that is discontinuous at every point is a dense hyperplane. -/
theorem ker_dense_and_is_hyperplane_of_everywhereDiscontinuous
    (f : H →ₗ[ℝ] ℝ) (hdisc : ∀ x : H, ¬ ContinuousAt f x) :
    Dense (LinearMap.ker f : Set H) ∧ is_hyperplane (LinearMap.ker f : Set H) := by
  constructor
  · rw [dense_iff_closure_eq]
    ext x
    constructor
    · intro _
      simp
    · intro _
      rw [Metric.mem_closure_iff]
      intro ε hε
      let U : Set H := Metric.ball x ε
      have hU_open : IsOpen U := Metric.isOpen_ball
      have hU_nonempty : U.Nonempty := ⟨x, Metric.mem_ball_self hε⟩
      rcases
          image_not_bddAbove_and_not_bddBelow_of_isOpen_of_nonempty_of_everywhereDiscontinuous
            f hdisc hU_open hU_nonempty with
        ⟨hnotAbove, hnotBelow⟩
      rcases (not_bddBelow_iff.1 hnotBelow) 0 with ⟨_, hyNegIm, hyNeg⟩
      rcases hyNegIm with ⟨yNeg, hyNegU, rfl⟩
      rcases (not_bddAbove_iff.1 hnotAbove) 0 with ⟨_, hyPosIm, hyPos⟩
      rcases hyPosIm with ⟨yPos, hyPosU, rfl⟩
      rcases exists_kernel_point_on_segment_of_opposite_sign f hyNeg hyPos with
        ⟨t, ht0, ht1, hzker⟩
      let z : H := t • yNeg + (1 - t) • yPos
      have hzSeg : z ∈ segment ℝ yNeg yPos := by
        refine ⟨t, 1 - t, ht0.le, sub_nonneg.mpr ht1.le, by linarith, rfl⟩
      have hzU : z ∈ U := (convex_ball x ε).segment_subset hyNegU hyPosU hzSeg
      refine ⟨z, ?_, ?_⟩
      · simpa [LinearMap.mem_ker, z] using hzker
      · simpa [U, z, Metric.mem_ball, dist_comm] using hzU
  · have hf_ne : f ≠ 0 := by
      intro hf
      subst hf
      exact hdisc 0 <| by
        simpa using (continuousAt_const : ContinuousAt (fun _ : H ↦ (0 : ℝ)) (0 : H))
    -- A nonzero linear functional cuts out a hyperplane at level `0`.
    have hker :
        (LinearMap.ker f : Set H) = {x : H | f x = 0} := by
      ext x
      simp [LinearMap.mem_ker]
    rw [hker]
    exact is_hyperplane_setOf_eq f hf_ne 0

end

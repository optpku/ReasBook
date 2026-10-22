/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_22
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin
open scoped TangentCone
open scoped WithTopConvexAnalysis
open scoped NormalCone
open scoped Topology

universe u

/- Theorem 3.1.24 lies in the chapter's constrained convex minimization / normal-cone domain.

Mandatory domain-style sampling before refinement:
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the owner API
  for feasible minimizers on a set, with textbook notation `argmin[Q] f`;
- `subdifferential` and `mem_subdifferential_iff` in `Definition_3_1_5`, the owner API for
  pointwise subdifferentials;
- `normalCone` and `mem_normalCone_iff` in `Definition_3_22`, the chapter owner API for textbook
  normal cones;
- `subgradient_inner_sub_nonneg_of_isMinOn` in `Theorem_3_1_5_6`, the intrinsic subgradient
  inequality at a constrained minimizer.

Best owner abstraction:
- the minimizer set owner `argmin[Q] f`;
- the pointwise owners `gStar ∈ ∂ (fun x ↦ (f x : WithTop ℝ))(xStar)` and `gStar ∈ N[Q] xStar`.

Primitive data:
- a feasible set `Q`;
- a convex objective `f`;
- a feasible point `xStar`;
- a candidate certificate `gStar`.

Derived API:
- the source-facing constrained-optimality criterion in normal-cone form;
- its textbook pairing reformulation via `mem_normalCone_iff`.

Source/core/bridge triage:
- source-facing: Theorem 3.1.24's constrained minimizer criterion;
- core/canonical: `argmin[Q] f`, `subdifferential`, and `normalCone`;
- bridge/view: the pairing reformulation through `mem_normalCone_iff`.

The later common-normal-cone/common-subdifferential propagation layer belongs downstream in
`Theorem_3_29`. This file stays focused on the normal-cone optimality criterion itself, while
using the chapter owner notation `argmin[Q] f` directly on the public theorem surface. The
textbook item lives on `ℝⁿ`, so the ambient layer here is the corresponding finite-dimensional
real inner-product-space owner rather than an unnecessarily more general complete-space wrapper.
-/

section NormalConeOwner

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Helper for Theorem 3.1.24: the subdifferential of a real-valued convex function at a point is
closed in the subgradient variable. -/
lemma isClosed_subdifferential_coe_real_at
    {f : V → ℝ} (xStar : V) :
    IsClosed (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) : Set V) := by
  let H : V → Set V := fun y ↦ {g : V | f xStar + inner ℝ g (y - xStar) ≤ f y}
  have hclosedH : ∀ y : V, IsClosed (H y) := by
    intro y
    refine isClosed_le ?_ continuous_const
    -- Each support inequality cuts out a closed half-space in the subgradient variable.
    have hcont : Continuous fun g : V ↦ f xStar + inner ℝ g (y - xStar) := by
      continuity
    simpa [H] using hcont
  have hrepr :
      (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) : Set V) = ⋂ y : V, H y := by
    -- Rewrite subdifferential membership as the family of affine support inequalities.
    ext g
    rw [mem_subdifferential_coe_real_iff]
    simp [H, ge_iff_le]
  rw [hrepr]
  exact isClosed_iInter hclosedH

/-- Helper for Theorem 3.1.24: the real-valued subdifferential is convex in the subgradient
variable. -/
lemma convex_subdifferential_coe_real_at
    {f : V → ℝ} (xStar : V) :
    Convex ℝ (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)) := by
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  rw [mem_subdifferential_coe_real_iff] at hg₁ hg₂ ⊢
  intro y
  have h₁ := hg₁ y
  have h₂ := hg₂ y
  -- Convex combinations preserve the affine lower-support inequalities.
  have hcombo :
      a * (f xStar + inner ℝ g₁ (y - xStar)) + b * (f xStar + inner ℝ g₂ (y - xStar)) ≤ f y := by
    have ha' := mul_le_mul_of_nonneg_left h₁ ha
    have hb' := mul_le_mul_of_nonneg_left h₂ hb
    calc
      a * (f xStar + inner ℝ g₁ (y - xStar)) + b * (f xStar + inner ℝ g₂ (y - xStar))
          ≤ a * f y + b * f y := add_le_add ha' hb'
      _ = f y := by
            rw [← add_mul, hab, one_mul]
  calc
    f y ≥ a * (f xStar + inner ℝ g₁ (y - xStar)) + b * (f xStar + inner ℝ g₂ (y - xStar)) := by
      exact hcombo
    _ = f xStar + inner ℝ (a • g₁ + b • g₂) (y - xStar) := by
      calc
        a * (f xStar + inner ℝ g₁ (y - xStar)) + b * (f xStar + inner ℝ g₂ (y - xStar))
            = (a + b) * f xStar + (a * inner ℝ g₁ (y - xStar) + b * inner ℝ g₂ (y - xStar)) := by
                ring
        _ = f xStar + (a * inner ℝ g₁ (y - xStar) + b * inner ℝ g₂ (y - xStar)) := by
              rw [hab]
              ring
        _ = f xStar + inner ℝ (a • g₁ + b • g₂) (y - xStar) := by
              simp [inner_add_left, inner_smul_left]

/-- Helper for Theorem 3.1.24: at an interior point of the effective domain, the real-valued
subdifferential is compact and convex. -/
lemma subdifferential_compact_convex_at
    [FiniteDimensional ℝ V]
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f) (xStar : V) :
    IsCompact (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)) ∧
      Convex ℝ (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)) := by
  let lift : V → WithTop ℝ := fun x ↦ (f x : WithTop ℝ)
  have hf_withTop : ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
    simpa [lift, withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hxInt : xStar ∈ interior (dom lift) := by
    simp [lift, withTopEffectiveDomain]
  have hbounded : Bornology.IsBounded (∂ lift(xStar)) :=
    (subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
      hf_withTop hxInt).2
  have hclosed : IsClosed (∂ lift(xStar) : Set V) :=
    isClosed_subdifferential_coe_real_at (f := f) xStar
  have hconv : Convex ℝ (∂ lift(xStar)) := by
    -- Real-valued subgradients stay convex under affine interpolation.
    simpa [lift] using convex_subdifferential_coe_real_at (f := f) xStar
  exact ⟨Metric.isCompact_of_isClosed_isBounded hclosed hbounded, hconv⟩

/-- Helper for Theorem 3.1.24: a point of the pointed cone hull of `Q - xStar` is a nonnegative
multiple of one feasible displacement from `xStar`. -/
lemma exists_nonneg_smul_vsub_of_mem_pointedConeHull
    {Q : Set V} (hQ_convex : Convex ℝ Q) {xStar p : V} (hxStar : xStar ∈ Q)
    (hp : p ∈ PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V))) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ x ∈ Q, p = r • (x - xStar) := by
  let S : Set V := Q -ᵥ ({xStar} : Set V)
  have hS_convex : Convex ℝ S := by
    -- Translating a convex set by `-xStar` preserves convexity.
    simpa [S, Set.vsub_singleton, vsub_eq_sub] using
      hQ_convex.sub (convex_singleton xStar)
  have hxSingleton : xStar ∈ ({xStar} : Set V) := by
    simp
  have hz : xStar -ᵥ xStar = (0 : V) := by
    simp [vsub_eq_sub]
  have hS_zero : (0 : V) ∈ S := by
    -- The zero displacement belongs to the displacement set because `xStar ∈ Q`.
    exact ⟨xStar, hxStar, xStar, hxSingleton, hz⟩
  have hconvexHull_pointed : (ConvexCone.hull ℝ S).Pointed :=
    ConvexCone.subset_hull hS_zero
  have hpointedHull_eq_convexHull : (PointedCone.hull ℝ S : Set V) = ConvexCone.hull ℝ S := by
    -- For a convex set containing `0`, the pointed hull agrees with the convex cone hull.
    ext v
    constructor
    · intro hv
      let C : PointedCone ℝ V := (ConvexCone.hull ℝ S).toPointedCone hconvexHull_pointed
      have hspan : PointedCone.hull ℝ S ≤ C := by
        refine Submodule.span_le.2 ?_
        intro y hy
        exact ConvexCone.subset_hull hy
      exact hspan hv
    · intro hv
      have hconvexHull_le : ConvexCone.hull ℝ S ≤ (PointedCone.hull ℝ S : ConvexCone ℝ V) := by
        exact ConvexCone.hull_min fun y hy ↦ PointedCone.subset_hull hy
      exact hconvexHull_le hv
  have hpS : p ∈ (PointedCone.hull ℝ S : Set V) := by
    simpa [S] using hp
  have hp' : p ∈ ConvexCone.hull ℝ S := by
    rwa [hpointedHull_eq_convexHull] at hpS
  rcases (ConvexCone.mem_hull_of_convex hS_convex).mp hp' with ⟨r, hr, y, hy, rfl⟩
  have hy' : y ∈ (fun z ↦ z - xStar) '' Q := by
    simpa [S, Set.vsub_singleton] using hy
  rcases hy' with ⟨x, hx, rfl⟩
  exact ⟨r, hr.le, x, hx, rfl⟩

/-- Helper for Theorem 3.1.24: the compact subdifferential admits a closest point to the normal
cone, and together with the projection of that point onto the cone one gets the two standard
variational inequalities for the closest pair. -/
lemma exists_closest_subgradient_normalCone_pair
    [FiniteDimensional ℝ V] [CompleteSpace V]
    {Q : Set V} {f : V → ℝ} {xStar : V}
    (hf_conv : ConvexOn ℝ Set.univ f) :
    ∃ g1Star ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar),
      ∃ g2Star ∈ N[Q] xStar,
        (∀ g1 ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar),
            inner ℝ (g2Star - g1Star) (g1 - g1Star) ≤ 0) ∧
          (∀ g2 ∈ N[Q] xStar,
            inner ℝ (g1Star - g2Star) (g2 - g2Star) ≤ 0) := by
  let S : Set V := ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)
  let N : Set V := N[Q] xStar
  let lift : V → WithTop ℝ := fun x ↦ (f x : WithTop ℝ)
  have hf_withTop : ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
    simpa [lift, withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hxInt : xStar ∈ interior (dom lift) := by
    simp [lift, withTopEffectiveDomain]
  have hS_nonempty : S.Nonempty := by
    -- Interior points of a real-valued convex function admit at least one subgradient.
    simpa [S, lift] using
      (subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
        hf_withTop hxInt).1
  have hS_compact : IsCompact S := by
    -- The compactness package lets us minimize the distance to the normal cone on the
    -- subdifferential.
    simpa [S] using (subdifferential_compact_convex_at (V := V) hf_conv xStar).1
  have hS_convex : Convex ℝ S := by
    simpa [S] using (subdifferential_compact_convex_at (V := V) hf_conv xStar).2
  have hinf_cont : ContinuousOn (fun g : V ↦ Metric.infDist g N) S := by
    simpa [N] using (Metric.continuous_infDist_pt N).continuousOn
  rcases hS_compact.exists_isMinOn hS_nonempty hinf_cont with ⟨g1Star, hg1Star, hg1Min⟩
  have hzero_mem : (0 : V) ∈ N := by
    -- The normal cone is a cone, so it always contains the zero vector.
    change (0 : V) ∈ N[Q] xStar
    rw [mem_normalCone_iff]
    intro x hx
    simp
  have hN_nonempty : N.Nonempty := ⟨0, hzero_mem⟩
  have hN_closed : IsClosed N := by
    simpa [N] using (N[Q] xStar : ProperCone ℝ V).isClosed
  have hN_convex : Convex ℝ N := by
    simpa [N] using (N[Q] xStar : ProperCone ℝ V).convex
  rcases exists_unique_projection_point_of_nonempty_closed_convex
      N hN_nonempty hN_closed hN_convex g1Star with ⟨g2Star, hprojN, _⟩
  have hprojS : IsProjectionPointOn S g2Star g1Star := by
    -- Minimizing `infDist · N` on `S` turns `g1Star` into a projection of `g2Star` onto `S`.
    refine (IsProjectionPointOn.iff_isMinOn).2 ?_
    refine ⟨hg1Star, ?_⟩
    rw [isMinOn_iff]
    intro g1 hg1
    have hdist_le : dist g2Star g1Star ≤ dist g2Star g1 := by
      calc
        dist g2Star g1Star = Metric.infDist g1Star N := by
          simpa [dist_comm] using hprojN.2
        _ ≤ Metric.infDist g1 N := (isMinOn_iff.mp hg1Min) g1 hg1
        _ ≤ dist g1 g2Star := Metric.infDist_le_dist_of_mem hprojN.1
        _ = dist g2Star g1 := by rw [dist_comm]
    simpa [dist_eq_norm, norm_sub_rev] using hdist_le
  refine ⟨g1Star, hg1Star, g2Star, hprojN.1, ?_, ?_⟩
  · intro g1 hg1
    -- The projection inequality on the subdifferential gives the first closest-pair inequality.
    have hineq : 0 ≤ inner ℝ (g1Star - g2Star) (g1 - g1Star) :=
      hprojS.inner_sub_nonneg hS_convex hg1
    simpa [sub_eq_add_neg, inner_add_left, inner_neg_left] using neg_nonpos.mpr hineq
  · intro g2 hg2
    -- The projection inequality on the normal cone gives the second closest-pair inequality.
    have hineq : 0 ≤ inner ℝ (g2Star - g1Star) (g2 - g2Star) :=
      hprojN.inner_sub_nonneg hN_convex hg2
    simpa [sub_eq_add_neg, inner_add_left, inner_neg_left] using neg_nonpos.mpr hineq

/-- Helper for Theorem 3.1.24: the normal-cone projection inequalities force the projection point
to be orthogonal to the gap vector `g2Star - g1Star`. -/
lemma normal_projection_gap_pairing_eq_zero
    [CompleteSpace V]
    {Q : Set V} {xStar g1Star g2Star : V}
    (hg2Star : g2Star ∈ N[Q] xStar)
    (hproj :
      ∀ g2 ∈ N[Q] xStar, inner ℝ (g1Star - g2Star) (g2 - g2Star) ≤ 0) :
    inner ℝ g2Star (g2Star - g1Star) = 0 := by
  have hzero_mem : (0 : V) ∈ N[Q] xStar := by
    rw [mem_normalCone_iff]
    intro x hx
    simp
  have htwo_mem : (2 : ℝ) • g2Star ∈ N[Q] xStar := by
    rw [mem_normalCone_iff]
    intro x hx
    have hnormal := mem_normalCone_iff.mp hg2Star x hx
    simpa [inner_smul_left] using mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) hnormal
  have hzero := hproj 0 hzero_mem
  have htwo := hproj ((2 : ℝ) • g2Star) htwo_mem
  have hzero' : ‖g2Star‖ ^ (2 : ℕ) ≤ inner ℝ g1Star g2Star := by
    simpa [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      real_inner_comm, real_inner_self_eq_norm_sq] using hzero
  have htwo_simple : inner ℝ (g1Star - g2Star) g2Star ≤ 0 := by
    simpa [two_smul, sub_eq_add_neg] using htwo
  have htwo' : inner ℝ g1Star g2Star ≤ ‖g2Star‖ ^ (2 : ℕ) := by
    have htwo'':
        inner ℝ g1Star g2Star - ‖g2Star‖ ^ (2 : ℕ) ≤ 0 := by
      simpa [sub_eq_add_neg, inner_add_left, inner_neg_left, real_inner_comm,
        real_inner_self_eq_norm_sq] using htwo_simple
    linarith
  have hEq : inner ℝ g1Star g2Star = ‖g2Star‖ ^ (2 : ℕ) := le_antisymm htwo' hzero'
  calc
    inner ℝ g2Star (g2Star - g1Star) = ‖g2Star‖ ^ (2 : ℕ) - inner ℝ g1Star g2Star := by
      calc
        inner ℝ g2Star (g2Star - g1Star) = inner ℝ g2Star g2Star - inner ℝ g2Star g1Star := by
          rw [inner_sub_right]
        _ = ‖g2Star‖ ^ (2 : ℕ) - inner ℝ g1Star g2Star := by
          rw [real_inner_self_eq_norm_sq, real_inner_comm]
    _ = 0 := by linarith

/-- Helper for Theorem 3.1.24: the gap vector of the closest pair belongs to the tangent cone. -/
lemma closest_pair_direction_mem_tangentCone
    [CompleteSpace V]
    {Q : Set V} (hQ_convex : Convex ℝ Q) {xStar g1Star g2Star : V}
    (hxStar : xStar ∈ Q) (hg2Star : g2Star ∈ N[Q] xStar)
    (hproj :
      ∀ g2 ∈ N[Q] xStar, inner ℝ (g1Star - g2Star) (g2 - g2Star) ≤ 0) :
    g2Star - g1Star ∈ 𝒯[Q] xStar := by
  have hzeroPair :
      inner ℝ g2Star (g2Star - g1Star) = 0 :=
    normal_projection_gap_pairing_eq_zero hg2Star hproj
  rw [mem_tangentCone_iff hQ_convex hxStar]
  intro g hg
  have hineq := hproj g hg
  have hEq : inner ℝ g1Star g2Star = ‖g2Star‖ ^ (2 : ℕ) := by
    have hzeroPair' : inner ℝ g2Star g2Star - inner ℝ g2Star g1Star = 0 := by
      simpa [sub_eq_add_neg, inner_add_right] using hzeroPair
    have hzeroPair'' : ‖g2Star‖ ^ (2 : ℕ) - inner ℝ g1Star g2Star = 0 := by
      simpa [real_inner_self_eq_norm_sq, real_inner_comm] using hzeroPair'
    linarith
  have hbasic : inner ℝ g1Star g ≤ inner ℝ g2Star g := by
    have hineq' :
        inner ℝ g1Star g - inner ℝ g2Star g +
          (‖g2Star‖ ^ (2 : ℕ) - inner ℝ g1Star g2Star) ≤ 0 := by
      simpa [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
        real_inner_self_eq_norm_sq, real_inner_comm, add_assoc, add_left_comm, add_comm] using hineq
    linarith
  calc
    0 ≤ inner ℝ g2Star g - inner ℝ g1Star g := sub_nonneg.mpr hbasic
    _ = inner ℝ g (g2Star - g1Star) := by
          rw [inner_sub_right, real_inner_comm g g2Star, real_inner_comm g g1Star]

/-- Helper for Theorem 3.1.24: the convex directional derivative is nonnegative on every feasible
displacement from a constrained minimizer. -/
lemma directionalDerivativeReal_nonneg_on_feasible_displacement_of_mem_argmin
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) (hxArgmin : xStar ∈ argmin[Q] f)
    (hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ))))
    {x : V} (hx : x ∈ Q) :
    0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt (x - xStar) := by
  let lift : V → WithTop ℝ := fun z ↦ (f z : WithTop ℝ)
  have hf_withTop : ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
    simpa [lift, withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hxMin : IsMinOn f Q xStar := (mem_constrainedArgmin_iff.mp hxArgmin).2
  have hlt : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  have hquot_nonneg :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        0 ≤ (withTopRealPart lift (xStar + α • (x - xStar)) - withTopRealPart lift xStar) / α := by
    -- Along the feasible segment from `xStar` to `x`, every forward secant quotient is
    -- nonnegative because `xStar` minimizes `f` on `Q`.
    filter_upwards [self_mem_nhdsWithin, hlt] with α hαpos hαlt
    have hseg : xStar + α • (x - xStar) ∈ segment ℝ xStar x := by
      rw [segment_eq_image']
      exact ⟨α, ⟨le_of_lt hαpos, le_of_lt hαlt⟩, rfl⟩
    have hfeas : xStar + α • (x - xStar) ∈ Q := hQ_convex.segment_subset hxStar hx hseg
    have hmin_ineq : f xStar ≤ f (xStar + α • (x - xStar)) := (isMinOn_iff.mp hxMin) _ hfeas
    have hsub : 0 ≤ f (xStar + α • (x - xStar)) - f xStar := by
      linarith
    simpa [lift, withTopRealPart] using div_nonneg hsub hαpos.le
  have hzero : Filter.Tendsto (fun _ : ℝ ↦ 0) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds
  have hsecant :=
    tendsto_directionalSecantQuotient_of_mem_interior hf_withTop hxInt (x - xStar)
  -- Passing to the limit preserves the secant-quotient lower bound at `0`.
  exact le_of_tendsto_of_tendsto hzero hsecant hquot_nonneg

/-- Helper for Theorem 3.1.24: the convex directional derivative is nonnegative on the pointed
cone hull generated by feasible displacements. -/
lemma directionalDerivativeReal_nonneg_on_pointedConeHull_of_mem_argmin
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) (hxArgmin : xStar ∈ argmin[Q] f)
    (hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ))))
    {p : V} (hp : p ∈ PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V))) :
    0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt p := by
  rcases exists_nonneg_smul_vsub_of_mem_pointedConeHull hQ_convex hxStar hp with
    ⟨r, hr, x, hx, rfl⟩
  have hdisp :
      0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
        hxInt (x - xStar) :=
    directionalDerivativeReal_nonneg_on_feasible_displacement_of_mem_argmin
      hQ_convex hf_conv hxStar hxArgmin hxInt hx
  have hf_withTop :
      ConvexOn ℝ (dom (fun z : V ↦ (f z : WithTop ℝ)))
        (withTopRealPart (fun z : V ↦ (f z : WithTop ℝ))) := by
    simpa [withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hzero :
      convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt (0 : V) = 0 := by
    -- The zero direction has zero directional derivative by uniqueness against the constant slice.
    have howner :
        HasDirectionalDerivAt (withTopToEReal ∘ fun z : V ↦ (f z : WithTop ℝ))
          xStar (0 : V)
          (convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt (0 : V)) :=
      convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf_withTop hxInt 0
    have hconst :
        HasDirectionalDerivAt (withTopToEReal ∘ fun z : V ↦ (f z : WithTop ℝ))
          xStar (0 : V) 0 :=
      HasDirectionalDerivAt.zero
        (f := withTopToEReal ∘ fun z : V ↦ (f z : WithTop ℝ))
        (x := xStar)
        (mem_dom_withTopToEReal_comp_of_mem_dom (interior_subset hxInt))
    exact HasDirectionalDerivAt.unique howner hconst
  have hscale :
      convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
          hxInt (r • (x - xStar)) =
        r * convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
          hxInt (x - xStar) := by
    -- Positive homogeneity transports the feasible-displacement estimate to the whole cone hull.
    by_cases hr0 : r = 0
    · subst hr0
      simp [hzero]
    · have hr_pos : 0 < r := lt_of_le_of_ne hr (by simpa [eq_comm] using hr0)
      rw [convexDirectionalDerivativeReal_apply, convexDirectionalDerivativeReal_apply]
      rw [convexDirectionalDerivative_smul
        (f := fun z : V ↦ (f z : WithTop ℝ))
        (hx := interior_subset hxInt) hr_pos (x - xStar)]
      simp [EReal.toReal_mul]
  rw [hscale]
  exact mul_nonneg hr hdisp

/-- Helper for Theorem 3.1.24: the convex directional derivative is nonnegative on the whole
tangent cone at a constrained minimizer. -/
lemma directionalDerivativeReal_nonneg_on_tangentCone_of_mem_argmin
    [FiniteDimensional ℝ V] [CompleteSpace V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) (hxArgmin : xStar ∈ argmin[Q] f)
    (hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ))))
    {p : V} (hp : p ∈ 𝒯[Q] xStar) :
    0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt p := by
  let dderiv : V → ℝ :=
    convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt
  let C : Set V := {q : V | 0 ≤ dderiv q}
  have hf_withTop :
      ConvexOn ℝ (dom (fun z : V ↦ (f z : WithTop ℝ)))
        (withTopRealPart (fun z : V ↦ (f z : WithTop ℝ))) := by
    simpa [withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hcont : Continuous dderiv := by
    -- The whole-space convex directional derivative is continuous on all directions.
    rw [← continuousOn_univ]
    simpa [dderiv] using
      (convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior
        (f := fun z : V ↦ (f z : WithTop ℝ)) hf_withTop hxInt).continuousOn_interior
  have hclosed : IsClosed C := by
    simpa [C] using isClosed_Ici.preimage hcont
  have hsubset :
      (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V)) : Set V) ⊆ C := by
    -- The pointed-cone-hull lemma provides the dense generating cone of tangent directions.
    intro q hq
    exact directionalDerivativeReal_nonneg_on_pointedConeHull_of_mem_argmin
      hQ_convex hf_conv hxStar hxArgmin hxInt hq
  have hp' : p ∈ closure (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V)) : Set V) := by
    -- Lemma 3.1.18 identifies the tangent cone with the closure of the pointed feasible hull.
    rw [posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton Q hQ_convex xStar hxStar] at hp
    simpa using hp
  have hclosure :
      closure (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V)) : Set V) ⊆ C := by
    exact hclosed.closure_subset_iff.2 hsubset
  exact hclosure hp'

/-- Helper for Theorem 3.1.24: the subgradient-side variational inequality forces the directional
derivative along the closest-pair gap to be strictly negative. -/
lemma closest_pair_directionalDerivative_lt_zero
    [FiniteDimensional ℝ V]
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar g1Star g2Star : V}
    (hdisj :
      Disjoint (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)) ({g2Star} : Set V))
    (hg1Star : g1Star ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar))
    (hproj :
      ∀ g1 ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar),
        inner ℝ (g2Star - g1Star) (g1 - g1Star) ≤ 0)
    (hzeroPair : inner ℝ g2Star (g2Star - g1Star) = 0)
    (hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ)))) :
    convexDirectionalDerivativeReal
        (fun z : V ↦ (f z : WithTop ℝ)) hxInt (g2Star - g1Star) < 0 := by
  let pStar : V := g2Star - g1Star
  have hf_withTop :
      ConvexOn ℝ (dom (fun z : V ↦ (f z : WithTop ℝ)))
        (withTopRealPart (fun z : V ↦ (f z : WithTop ℝ))) := by
    simpa [withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hmax :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
      (f := fun z : V ↦ (f z : WithTop ℝ)) hf_withTop hxInt pStar
  have hupper :
      ∀ g ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar),
        inner ℝ g pStar ≤ inner ℝ g1Star pStar := by
    intro g hg
    have hineq : inner ℝ g pStar - inner ℝ g1Star pStar ≤ 0 := by
      calc
        inner ℝ g pStar - inner ℝ g1Star pStar
            = inner ℝ pStar g - inner ℝ pStar g1Star := by
                rw [real_inner_comm g pStar, real_inner_comm g1Star pStar]
        _ = inner ℝ pStar (g - g1Star) := by
              rw [inner_sub_right]
        _ ≤ 0 := hproj g hg
    exact sub_nonpos.mp hineq
  have hmemImage :
      inner ℝ g1Star pStar ∈
        (fun g : V ↦ inner ℝ g pStar) '' ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) := by
    exact ⟨g1Star, hg1Star, rfl⟩
  have hle_max :
      inner ℝ g1Star pStar ≤
        convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt pStar :=
    hmax.2 hmemImage
  have hge_max :
      convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt pStar ≤
        inner ℝ g1Star pStar := by
    rcases hmax.1 with ⟨g, hg, hgEq⟩
    rw [← hgEq]
    exact hupper g hg
  have hvalue :
      convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt pStar =
        inner ℝ g1Star pStar := by
    exact le_antisymm hge_max hle_max
  have hg2_not_mem :
      g2Star ∉ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) := by
    rw [Set.disjoint_singleton_right] at hdisj
    exact hdisj
  have hneq : g1Star ≠ g2Star := by
    intro hEq
    apply hg2_not_mem
    simpa [hEq] using hg1Star
  have hp_nonzero : pStar ≠ 0 := by
    exact sub_ne_zero.mpr hneq.symm
  have hp_norm_sq_pos : 0 < ‖pStar‖ ^ (2 : ℕ) := by
    positivity
  have hpair :
      inner ℝ g1Star pStar = -‖pStar‖ ^ (2 : ℕ) := by
    calc
      inner ℝ g1Star pStar = inner ℝ (g2Star - pStar) pStar := by
        simp [pStar, sub_eq_add_neg, add_left_comm]
      _ = inner ℝ g2Star pStar - inner ℝ pStar pStar := by
        rw [inner_sub_left]
      _ = -‖pStar‖ ^ (2 : ℕ) := by
        simp [pStar, hzeroPair]
  rw [hvalue, hpair]
  linarith

/-- Theorem 3 1 24: a feasible point `xStar ∈ Q` belongs to the
optimal set `X* = argmin_{x ∈ Q} f(x)` if and only if some subgradient at `xStar` lies in the
normal cone of `Q` at `xStar`. -/
theorem mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) :
    xStar ∈ argmin[Q] f ↔
      ∃ gStar : V,
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) ∧
          gStar ∈ N[Q] xStar := by
  constructor
  · intro hxArgmin
    by_contra hno
    let S : Set V := ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)
    have hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ))) := by
      simp [withTopEffectiveDomain]
    have hnone :
        ∀ g : V, g ∈ S → g ∉ N[Q] xStar := by
      intro g hgS hgN
      exact hno ⟨g, hgS, hgN⟩
    rcases exists_closest_subgradient_normalCone_pair (V := V) (Q := Q) (f := f) (xStar := xStar)
        hf_conv with ⟨g1Star, hg1Star, g2Star, hg2Star, hprojS, hprojN⟩
    have hg2_not_mem : g2Star ∉ S := by
      intro hg2S
      exact hno ⟨g2Star, hg2S, hg2Star⟩
    have hdisj_singleton : Disjoint S ({g2Star} : Set V) := by
      rw [Set.disjoint_singleton_right]
      exact hg2_not_mem
    have htan : g2Star - g1Star ∈ 𝒯[Q] xStar :=
      closest_pair_direction_mem_tangentCone hQ_convex hxStar hg2Star hprojN
    have hnonneg :
        0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
          hxInt (g2Star - g1Star) :=
      directionalDerivativeReal_nonneg_on_tangentCone_of_mem_argmin
        hQ_convex hf_conv hxStar hxArgmin hxInt htan
    have hzeroPair :
        inner ℝ g2Star (g2Star - g1Star) = 0 :=
      normal_projection_gap_pairing_eq_zero hg2Star hprojN
    have hlt :
        convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
          hxInt (g2Star - g1Star) < 0 :=
      closest_pair_directionalDerivative_lt_zero
        hf_conv hdisj_singleton hg1Star hprojS hzeroPair hxInt
    linarith
  · rintro ⟨gStar, hgStar_sub, hgStar_normal⟩
    rw [mem_constrainedArgmin_iff]
    refine ⟨hxStar, isMinOn_iff.mpr ?_⟩
    intro x hx
    have hsubgrad := mem_subdifferential_coe_real_iff.mp hgStar_sub x
    have hnormal := mem_normalCone_iff.mp hgStar_normal x hx
    linarith

end NormalConeOwner

section PairingBridge

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Pairing reformulation of Theorem 3 1 24: a feasible point `xStar ∈ Q` belongs to the optimal set
`X* = argmin_{x ∈ Q} f(x)` if and only if there exists a subgradient `gStar ∈ ∂f(xStar)` such
that `⟪gStar, x - xStar⟫ ≥ 0` for every `x ∈ Q`. -/
-- Proof sketch: rewrite the canonical normal-cone owner statement through
-- the normal-cone pairing condition.
theorem mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) :
    xStar ∈ argmin[Q] f ↔
      ∃ gStar : V,
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) ∧
          ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar) := by
  -- Rewrite the canonical owner statement through the normal-cone membership criterion.
  rw [mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone hQ_convex hf_conv hxStar]
  constructor
  · rintro ⟨gStar, hgStar, hgNormal⟩
    exact ⟨gStar, hgStar, mem_normalCone_iff.mp hgNormal⟩
  · rintro ⟨gStar, hgStar, hpair⟩
    exact ⟨gStar, hgStar, mem_normalCone_iff.mpr hpair⟩

end PairingBridge

end

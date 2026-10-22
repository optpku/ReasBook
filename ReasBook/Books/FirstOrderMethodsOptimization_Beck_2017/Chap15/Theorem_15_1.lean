/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Proposition_2_3
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_6
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_1
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_2
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped Pointwise

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {h₁ : X → EReal} {h₂ : Z → EReal}
variable {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
variable {ρ : PosReal} {G : X →ₗ[ℝ] X} {Q : Z →ₗ[ℝ] Z}

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled from the nearby
Chapter 4 and Chapter 15 duality files. This item is `source-facing`: its mathematical content is
the strong-duality equality for the ADMM primal/dual value pair together with dual attainment.
The `core/canonical` owners are already upstream:
- `admm_problem_value`, `admm_dual_problem_value`, and `admm_dual_objective` in Chapter 15;
- `fenchel_duality_value_eq` and
  `exists_isGreatest_fenchel_dual_objective_of_finite_value` in Chapter 4.

Accordingly, this file keeps only the ADMM-specialized statements. The main labeled theorems are
source-facing over the Chapter 15 assumption owner `IsADPMMProblem`; the private helper layer
below keeps the projected properness, convexity, and qualification inputs explicit because those
are the Chapter 4 duality hypotheses consumed internally by the proof skeleton. -/

variable (h₁_proper : IsProperExtendedRealFunction h₁)
variable (h₂_proper : IsProperExtendedRealFunction h₂)
variable (h₁_convex : is_convex_function h₁)
variable (h₂_convex : is_convex_function h₂)
variable (hqual :
  ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
    ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
      A xHat + B zHat = c)

/-- Helper for Theorem 15.1: negating an affine perturbation turns its infimum into the negative
Fenchel conjugate. -/
private theorem ereal_sInf_range_sub_pairing_eq_neg_conjugate
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → EReal) (η : Module.Dual ℝ E) :
    sInf (Set.range fun x : E ↦ f x - (η x : EReal)) = -conjugate_function f η := by
  -- Rewrite the affine-perturbation range as the negation of the conjugate-defining range.
  have hrange :
      Set.range (fun x : E ↦ f x - (η x : EReal)) =
        -Set.range (fun x : E ↦ (η x : EReal) - f x) := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      rw [Set.mem_neg]
      refine ⟨x, ?_⟩
      have hneg : -(f x - (η x : EReal)) = ((η x : EReal) - f x) := by
        have hraw : -(f x - (η x : EReal)) = -f x + (η x : EReal) := by
          exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
        simpa [sub_eq_add_neg, add_comm] using hraw
      simpa using hneg.symm
    · rw [Set.mem_neg]
      rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have hneg : -(f x - (η x : EReal)) = -r := by
        calc
          -(f x - (η x : EReal)) = ((η x : EReal) - f x) := by
            have hraw : -(f x - (η x : EReal)) = -f x + (η x : EReal) := by
              exact EReal.neg_sub (Or.inr (by simp)) (Or.inr (by simp))
            simpa [sub_eq_add_neg, add_comm] using hraw
          _ = -r := by simpa using hx
      have hr : -(-(f x - (η x : EReal))) = -(-r) := congrArg Neg.neg hneg
      simpa using hr
  -- Translate the infimum of the negated range into the negative supremum from the conjugate.
  rw [hrange]
  have hsInf_neg :
      sInf (-Set.range (fun x : E ↦ (η x : EReal) - f x)) =
        -sSup (Set.range fun x : E ↦ (η x : EReal) - f x) := by
    refine le_antisymm ?_ ?_
    · have hsSup :
          sSup (Set.range fun x : E ↦ (η x : EReal) - f x) ≤
            -sInf (-Set.range fun x : E ↦ (η x : EReal) - f x) := by
        refine sSup_le ?_
        intro x hx
        have hsInf :
            sInf (-Set.range fun x : E ↦ (η x : EReal) - f x) ≤ -x := by
          exact sInf_le
            (by
              simpa [Set.mem_neg] using hx :
                -x ∈ -Set.range fun x : E ↦ (η x : EReal) - f x)
        exact EReal.le_neg.mp hsInf
      exact EReal.le_neg.mpr hsSup
    · refine le_sInf ?_
      intro z hz
      exact EReal.neg_le.mpr
        (le_sSup
          (by
            simpa [Set.mem_neg] using hz :
              -z ∈ Set.range fun x : E ↦ (η x : EReal) - f x))
  rw [hsInf_neg, conjugate_function_apply]

/-- Helper for Theorem 15.1: every point of an affine subspace lies in the intrinsic interior of
its carrier set. -/
private theorem mem_intrinsicInterior_affineSubspace
    {V : Type*} {P : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (s : AffineSubspace ℝ P) {x : P} (hx : x ∈ (s : Set P)) :
    x ∈ intrinsicInterior ℝ (s : Set P) := by
  -- Unfold the intrinsic interior inside the affine span, which is the affine subspace itself.
  rw [intrinsicInterior]
  refine ⟨⟨x, ?_⟩, ?_, rfl⟩
  · simpa [AffineSubspace.affineSpan_coe] using hx
  · have hpre :
        ((↑) : affineSpan ℝ (s : Set P) → P) ⁻¹' (s : Set P) = Set.univ := by
      ext y
      change (↑y ∈ (s : Set P)) ↔ True
      constructor
      · intro _
        trivial
      · intro _
        simpa [AffineSubspace.affineSpan_coe] using y.property
    rw [hpre]
    simp

/-- Helper for Theorem 15.1: the relative interiors of the block domains combine to the product
relative interior. -/
private theorem mem_intrinsicInterior_prod
    {S : Set X} {T : Set Z} {x : X} {z : Z}
    (hx : x ∈ intrinsicInterior ℝ S)
    (hz : z ∈ intrinsicInterior ℝ T) :
    (x, z) ∈ intrinsicInterior ℝ (S ×ˢ T) := by
  -- Use the closed-ball characterization and project the product affine-span condition.
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_span, εS, hεS, hballS⟩
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hz with
    ⟨hz_span, εT, hεT, hballT⟩
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨
    subset_affineSpan ℝ (S ×ˢ T) ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hz⟩,
    min εS εT,
    lt_min hεS hεT,
    ?_⟩
  intro uv huv
  rcases uv with ⟨u, v⟩
  rcases huv with ⟨huv_ball, huv_span⟩
  have huv_dist : max (dist u x) (dist v z) ≤ min εS εT := by
    simpa [Prod.dist_eq, max_comm, max_left_comm, max_assoc] using huv_ball
  have hu_ball : u ∈ Metric.closedBall x εS := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).1) (min_le_left εS εT)
  have hv_ball : v ∈ Metric.closedBall z εT := by
    exact Metric.mem_closedBall.2 <|
      le_trans ((max_le_iff.1 huv_dist).2) (min_le_right εS εT)
  have hu_span_prod :
      u ∈ affineSpan ℝ (((LinearMap.fst ℝ X Z).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        u ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.fst ℝ X Z).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.fst ℝ X Z).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hv_span_prod :
      v ∈ affineSpan ℝ (((LinearMap.snd ℝ X Z).toAffineMap) '' (S ×ˢ T)) := by
    have hmem_map :
        v ∈ (affineSpan ℝ (S ×ˢ T)).map ((LinearMap.snd ℝ X Z).toAffineMap) := by
      simpa using
        (AffineSubspace.mem_map_of_mem (f := (LinearMap.snd ℝ X Z).toAffineMap) huv_span)
    rw [AffineSubspace.map_span] at hmem_map
    exact hmem_map
  have hu_span : u ∈ affineSpan ℝ S := by
    refine (affineSpan_mono ℝ ?_) hu_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  have hv_span : v ∈ affineSpan ℝ T := by
    refine (affineSpan_mono ℝ ?_) hv_span_prod
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  exact ⟨hballS ⟨hu_ball, hu_span⟩, hballT ⟨hv_ball, hv_span⟩⟩

/-- Helper for Theorem 15.1: the ADMM objective is finite exactly on the product of the two block
effective domains. -/
private theorem effective_domain_admm_objective
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂) :
    effective_domain (H[h₁, h₂]) = effective_domain h₁ ×ˢ effective_domain h₂ := by
  ext xz
  rcases xz with ⟨x, z⟩
  -- Turn finiteness of the block sum into coordinatewise finiteness using `≠ ⊥`.
  simp [effective_domain, lt_top_iff_ne_top, admm_objective_apply,
    EReal.add_ne_top_iff_ne_top₂, h₁_proper.ne_bot x, h₂_proper.ne_bot z]

/-- Helper for Theorem 15.1: the ADMM objective never takes the value `-∞`. -/
private theorem admm_objective_ne_bot
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (xz : X × Z) :
    H[h₁, h₂] xz ≠ ⊥ := by
  rcases xz with ⟨x, z⟩
  -- Each block objective avoids `⊥`, so their sum avoids `⊥` as well.
  simpa [admm_objective_apply, EReal.add_ne_bot_iff] using
    And.intro (h₁_proper.ne_bot x) (h₂_proper.ne_bot z)

/-- Helper for Theorem 15.1: the ADMM product objective is proper. -/
private theorem admm_objective_proper
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂) :
    IsProperExtendedRealFunction (H[h₁, h₂]) := by
  rcases h₁_proper.effective_domain_nonempty with ⟨x0, hx0⟩
  rcases h₂_proper.effective_domain_nonempty with ⟨z0, hz0⟩
  refine
    { ne_bot := admm_objective_ne_bot h₁_proper h₂_proper
      effective_domain_nonempty := ?_ }
  refine ⟨(x0, z0), ?_⟩
  simpa [effective_domain_admm_objective h₁_proper h₂_proper] using And.intro hx0 hz0

/-- Helper for Theorem 15.1: the ADMM product objective is convex on `X × Z`. -/
private theorem admm_objective_convex
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (h₁_convex : is_convex_function h₁)
    (h₂_convex : is_convex_function h₂) :
    is_convex_function (H[h₁, h₂]) := by
  have hh₁_fst : is_convex_function (fun xz : X × Z ↦ h₁ xz.1) := by
    -- Pull the convexity of `h₁` back along the first-coordinate projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := h₁) h₁_convex (LinearMap.fst ℝ X Z) (0 : X)
  have hh₂_snd : is_convex_function (fun xz : X × Z ↦ h₂ xz.2) := by
    -- Pull the convexity of `h₂` back along the second-coordinate projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := h₂) h₂_convex (LinearMap.snd ℝ X Z) (0 : Z)
  -- The ADMM objective is the pointwise sum of the two block pullbacks.
  simpa [composite_model_objective_eq_add] using
    is_convex_function_pointwise_add
      hh₁_fst hh₂_snd
      (fun xz ↦ h₁_proper.ne_bot xz.1)
      (fun xz ↦ h₂_proper.ne_bot xz.2)

/-- Helper for Theorem 15.1: a linear fiber is a translate of the kernel through any feasible
base point. -/
private theorem linear_fiber_eq_singleton_add_ker
    {E : Type*} {F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (x0 : E) (c : F) (hx0 : L x0 = c) :
    {x : E | L x = c} = ({x0} : Set E) + (LinearMap.ker L : Set E) := by
  ext x
  constructor
  · intro hx
    -- Rewrite a feasible point as the base point plus a kernel vector.
    refine Set.mem_add.2 ⟨x0, by simp, x - x0, ?_, ?_⟩
    · simpa [LinearMap.mem_ker] using
        show L (x - x0) = 0 by
          calc
            L (x - x0) = L x - L x0 := by rw [map_sub]
            _ = c - c := by rw [hx, hx0]
            _ = 0 := sub_self c
    · abel
  · intro hx
    rcases Set.mem_add.1 hx with ⟨u, hu, z, hz, rfl⟩
    rcases Set.mem_singleton_iff.1 hu with rfl
    have hz' : L z = 0 := by simpa [LinearMap.mem_ker] using hz
    -- Adding a kernel vector to a chosen solution preserves feasibility.
    simpa using
      show L (u + z) = c by
        rw [map_add, hx0, hz', add_zero]

/-- Helper for Theorem 15.1: the polar cone of a submodule carrier is its dual annihilator. -/
private theorem polar_cone_submodule_eq_dualAnnihilator
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (W : Submodule ℝ E) :
    polar_cone (W : Set E) = W.dualAnnihilator := by
  ext φ
  rw [mem_polar_cone]
  constructor
  · intro h
    change φ ∈ W.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    -- Test the polar inequality on `w` and `-w` to upgrade nonpositivity to equality.
    have hle : φ w ≤ 0 := h w hw
    have hneg : φ (-w) ≤ 0 := h (-w) (by simpa using W.neg_mem hw)
    have hge : 0 ≤ φ w := by
      have hneg' : -φ w ≤ 0 := by simpa using hneg
      exact neg_nonpos.mp hneg'
    exact le_antisymm hle hge
  · intro h
    change φ ∈ W.dualAnnihilator at h
    rw [Submodule.mem_dualAnnihilator] at h
    -- Vanishing on the submodule is stronger than the polar-cone inequality.
    intro w hw
    simp [h w hw]

/-- Helper for Theorem 15.1: the set-theoretic range of `dualMap` matches its linear-map range. -/
private theorem set_range_dualMap_eq_linearMap_range
    {E : Type*} {F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) :
    Set.range L.dualMap = (LinearMap.range L.dualMap : Set (Module.Dual ℝ E)) := by
  ext ξ
  constructor
  · rintro ⟨η, rfl⟩
    exact LinearMap.mem_range.2 ⟨η, rfl⟩
  · intro hξ
    rcases LinearMap.mem_range.1 hξ with ⟨η, rfl⟩
    exact ⟨η, rfl⟩

/-- Helper for Theorem 15.1: the support function of a singleton is evaluation at its unique
point. -/
private theorem support_function_singleton
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x0 : E) (ξ : Module.Dual ℝ E) :
    support_function ({x0} : Set E) ξ = (ξ x0 : EReal) := by
  -- The image set is a singleton, so its unique element is automatically greatest.
  have hmax :
      IsGreatest ((fun x : E ↦ (ξ x : EReal)) '' ({x0} : Set E)) (ξ x0 : EReal) := by
    constructor
    · exact ⟨x0, by simp, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rcases Set.mem_singleton_iff.1 hx with rfl
      simp
  exact support_function_eq_of_isGreatest_image ({x0} : Set E) ξ hmax

/-- Helper for Theorem 15.1: the support function of an affine linear fiber is evaluation at the
base point plus the indicator of the transpose range. -/
private theorem support_function_linear_fiber_eq_eval_add_indicator_dual_range
    {E : Type*} {F : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (x0 : E) (c : F) (hx0 : L x0 = c) (ξ : Module.Dual ℝ E) :
    support_function ({x : E | L x = c}) ξ =
      (ξ x0 : EReal) + extendedIndicator (Set.range L.dualMap) ξ := by
  have hcone : IsCone (LinearMap.ker L : Set E) := by
    rw [isCone_iff_smul_mem]
    intro a _ha x hx
    exact Submodule.smul_mem _ a hx
  have hzero : (0 : E) ∈ (LinearMap.ker L : Set E) := by
    simp
  -- Translate the affine fiber to a singleton plus the kernel, then rewrite the kernel support.
  calc
    support_function ({x : E | L x = c}) ξ
        = support_function (({x0} : Set E) + (LinearMap.ker L : Set E)) ξ := by
            rw [← linear_fiber_eq_singleton_add_ker L x0 c hx0]
    _ = support_function ({x0} : Set E) ξ +
          support_function (LinearMap.ker L : Set E) ξ := by
            simpa using
              congrFun
                (support_function_minkowski_sum_eq_add
                  ({x0} : Set E) (LinearMap.ker L : Set E))
                ξ
    _ = (ξ x0 : EReal) + support_function (LinearMap.ker L : Set E) ξ := by
            rw [support_function_singleton]
    _ = (ξ x0 : EReal) +
          extendedIndicator (polar_cone (LinearMap.ker L : Set E)) ξ := by
            congr 1
            rw [support_function_eq_indicatorFunction_polarCone
              (LinearMap.ker L : Set E) hcone hzero]
    _ = (ξ x0 : EReal) +
          extendedIndicator (Set.range L.dualMap) ξ := by
            have hrange :
                polar_cone (LinearMap.ker L : Set E) = Set.range L.dualMap := by
              have hpolar :
                  (polar_cone (LinearMap.ker L : Set E) : Set (Module.Dual ℝ E)) =
                    ((LinearMap.ker L).dualAnnihilator : Set (Module.Dual ℝ E)) := by
                simpa using
                  congrArg
                    (fun K : PointedCone ℝ (Module.Dual ℝ E) => (K : Set (Module.Dual ℝ E)))
                    (polar_cone_submodule_eq_dualAnnihilator (W := LinearMap.ker L))
              calc
                polar_cone (LinearMap.ker L : Set E)
                    = ((LinearMap.ker L).dualAnnihilator : Set (Module.Dual ℝ E)) := by
                      exact hpolar
                _ = (LinearMap.range L.dualMap : Set (Module.Dual ℝ E)) := by
                  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
                _ = Set.range L.dualMap := (set_range_dualMap_eq_linearMap_range L).symm
            rw [hrange]

/-- Helper for Theorem 15.1: once a feasible base point is fixed, the ADMM constraint set is the
affine subspace obtained by translating `ker (A.coprod B)` through that point. -/
private theorem admm_feasible_set_eq_affineSubspace_of_mem
    {xz0 : X × Z} (hxz0 : xz0 ∈ admm_feasible_set A B c) :
    admm_feasible_set A B c =
      ((AffineSubspace.mk' xz0 (A.coprod B).ker : AffineSubspace ℝ (X × Z)) : Set (X × Z)) := by
  have hxz0_eq : (A.coprod B) xz0 = c := by
    simpa [admm_feasible_set, LinearMap.coprod_apply] using hxz0
  have htranslate :
      ({xz0} : Set (X × Z)) + ((A.coprod B).ker : Set (X × Z)) =
        ((AffineSubspace.mk' xz0 (A.coprod B).ker : AffineSubspace ℝ (X × Z)) : Set (X × Z)) := by
    ext xz
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      rcases Set.mem_singleton_iff.1 hu with rfl
      simpa [AffineSubspace.mem_mk'] using hv
    · intro hxz
      have hxz' : xz - xz0 ∈ (A.coprod B).ker := by
        simpa [AffineSubspace.mem_mk'] using hxz
      refine Set.mem_add.2 ⟨xz0, by simp, xz - xz0, hxz', ?_⟩
      abel
  -- Identify the feasible set with the affine fiber of `A.coprod B`.
  calc
    admm_feasible_set A B c = {xz : X × Z | (A.coprod B) xz = c} := by
      ext xz
      simp [admm_feasible_set, LinearMap.coprod_apply]
    _ = ({xz0} : Set (X × Z)) + ((A.coprod B).ker : Set (X × Z)) := by
      rw [linear_fiber_eq_singleton_add_ker (A.coprod B) xz0 c hxz0_eq]
    _ = ((AffineSubspace.mk' xz0 (A.coprod B).ker : AffineSubspace ℝ (X × Z)) : Set (X × Z)) :=
      htranslate

/-- Helper for Theorem 15.1: the ADMM feasible set is convex. -/
private theorem admm_feasible_set_convex :
    Convex ℝ (admm_feasible_set A B c) := by
  intro x hx y hy a b ha hb hab
  rcases x with ⟨x₁, z₁⟩
  rcases y with ⟨x₂, z₂⟩
  have hx_eq : A x₁ + B z₁ = c := by
    simpa [admm_feasible_set] using hx
  have hy_eq : A x₂ + B z₂ = c := by
    simpa [admm_feasible_set] using hy
  -- Linear combinations preserve the affine equality constraint.
  have hcomb :
      A (a • x₁ + b • x₂) + B (a • z₁ + b • z₂) =
        a • (A x₁ + B z₁) + b • (A x₂ + B z₂) := by
    simp [map_add, smul_add, add_assoc, add_left_comm, add_comm]
  have hconstraint :
      A (a • x₁ + b • x₂) + B (a • z₁ + b • z₂) = c := by
    calc
      A (a • x₁ + b • x₂) + B (a • z₁ + b • z₂)
          = a • (A x₁ + B z₁) + b • (A x₂ + B z₂) := hcomb
      _ = a • c + b • c := by rw [hx_eq, hy_eq]
      _ = (a + b) • c := by rw [← add_smul]
      _ = c := by simpa [hab]
  simpa [admm_feasible_set] using hconstraint

/-- Helper for Theorem 15.1: every feasible ADMM point lies in the intrinsic interior of the
affine feasible set. -/
private theorem mem_intrinsicInterior_admm_feasible_set
    {xz : X × Z} (hxz : xz ∈ admm_feasible_set A B c) :
    xz ∈ intrinsicInterior ℝ (admm_feasible_set A B c) := by
  -- Rewrite the feasible set to the affine-subspace carrier determined by the chosen point.
  rw [admm_feasible_set_eq_affineSubspace_of_mem (A := A) (B := B) (c := c) hxz]
  exact mem_intrinsicInterior_affineSubspace
    (AffineSubspace.mk' xz (A.coprod B).ker) (by simp)

/-- Helper for Theorem 15.1: the ADMM primal value is the Fenchel primal infimum for the product
objective plus the feasible-set indicator. -/
private theorem admm_problem_value_eq_fenchel_primal_infimum
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂) :
    H_opt[h₁, h₂; A, B, c] =
      sInf (Set.range (composite_model_objective (H[h₁, h₂])
        (extendedIndicator (admm_feasible_set A B c)))) := by
  have hconstrained_eq :
      constrained_problem_objective (H[h₁, h₂]) (admm_feasible_set A B c) =
        composite_model_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) := by
    -- Rewrite the constrained objective as `H[h₁,h₂] + δ_feas`.
    simpa [composite_model_objective_eq_add] using
      constrained_problem_objective_eq_add_extendedIndicator
        (H[h₁, h₂]) (admm_feasible_set A B c)
        (fun xz _ ↦ admm_objective_ne_bot h₁_proper h₂_proper xz)
  -- Substitute the normalized owner into the Chapter 15 primal-value definition.
  simpa [admm_problem_value_eq_sInf, hconstrained_eq]

/-- Helper for Theorem 15.1: the ADMM qualification matches the Chapter 4 Fenchel qualification
on the product space. -/
private theorem admm_fenchel_qualification
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c) :
    (intrinsicInterior ℝ (effective_domain (H[h₁, h₂])) ∩
      intrinsicInterior ℝ (admm_feasible_set A B c)).Nonempty := by
  rcases hqual with ⟨xHat, hxHat, zHat, hzHat, hEq⟩
  refine ⟨(xHat, zHat), ?_⟩
  constructor
  · -- Put the qualification witness in the product relative interior of the effective domain.
    simpa [effective_domain_admm_objective h₁_proper h₂_proper] using
      mem_intrinsicInterior_prod (x := xHat) (z := zHat) hxHat hzHat
  · -- Then use the affine-fiber owner for the feasible-set intrinsic interior.
    exact mem_intrinsicInterior_admm_feasible_set
      (A := A) (B := B) (c := c) (by simpa [admm_feasible_set] using hEq)

/-- Helper for Theorem 15.1: the support function of the ADMM feasible affine fiber is constant on
the transpose range. -/
private theorem support_function_admm_feasible_set_on_range
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c)
    (y : Module.Dual ℝ Y) :
    support_function (admm_feasible_set A B c) ((A.coprod B).dualMap y) = (y c : EReal) := by
  rcases hqual with ⟨xHat, _hxHat, zHat, _hzHat, hEq⟩
  have hxz0 : (A.coprod B) (xHat, zHat) = c := by
    simpa [LinearMap.coprod_apply] using hEq
  have hmem : (A.coprod B).dualMap y ∈ Set.range (A.coprod B).dualMap := ⟨y, rfl⟩
  -- Evaluate the affine-fiber support formula at a feasible base point.
  calc
    support_function (admm_feasible_set A B c) ((A.coprod B).dualMap y)
        = ((((A.coprod B).dualMap y) (xHat, zHat) : ℝ) : EReal) +
            extendedIndicator (Set.range (A.coprod B).dualMap) ((A.coprod B).dualMap y) := by
              simpa [admm_feasible_set, LinearMap.coprod_apply] using
                support_function_linear_fiber_eq_eval_add_indicator_dual_range
                  (A.coprod B) (xHat, zHat) c hxz0 ((A.coprod B).dualMap y)
    _ = (y c : EReal) + 0 := by
          simp [extendedIndicator, hmem, LinearMap.dualMap_apply, LinearMap.coprod_apply, hEq]
    _ = (y c : EReal) := by simp

/-- Helper for Theorem 15.1: outside the transpose range, the support function of the ADMM
feasible affine fiber is infinite. -/
private theorem support_function_admm_feasible_set_eq_top_of_not_mem_dual_range
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c)
    (ξ : Module.Dual ℝ (X × Z))
    (hξ : ξ ∉ Set.range (A.coprod B).dualMap) :
    support_function (admm_feasible_set A B c) (-ξ) = ⊤ := by
  rcases hqual with ⟨xHat, _hxHat, zHat, _hzHat, hEq⟩
  have hxz0 : (A.coprod B) (xHat, zHat) = c := by
    simpa [LinearMap.coprod_apply] using hEq
  have hneg : -ξ ∉ Set.range (A.coprod B).dualMap := by
    intro hmem
    rcases hmem with ⟨y, hy⟩
    have hneg_map : (A.coprod B).dualMap (-y) = -((A.coprod B).dualMap y) := by
      apply LinearMap.ext
      intro xz
      rcases xz with ⟨x, z⟩
      simp [LinearMap.dualMap_apply, LinearMap.coprod_apply]
    apply hξ
    refine ⟨-y, ?_⟩
    calc
      (A.coprod B).dualMap (-y) = -((A.coprod B).dualMap y) := hneg_map
      _ = -(-ξ) := by simpa [hy]
      _ = ξ := by simp
  -- Off the transpose range, the indicator term in the affine-fiber support formula is `⊤`.
  calc
    support_function (admm_feasible_set A B c) (-ξ)
        = (((-ξ) (xHat, zHat) : ℝ) : EReal) +
            extendedIndicator (Set.range (A.coprod B).dualMap) (-ξ) := by
              simpa [admm_feasible_set, LinearMap.coprod_apply] using
                support_function_linear_fiber_eq_eval_add_indicator_dual_range
                  (A.coprod B) (xHat, zHat) c hxz0 (-ξ)
    _ = ⊤ := by
          simp [extendedIndicator, hneg]

/-- Helper for Theorem 15.1: subtracting the pulled-back dual pairing from the block objective
repackages the integrand as the ADMM Lagrangian plus the constant term `⟨y, c⟩`. -/
private theorem admm_objective_sub_coprodDual_neg_eq_lagrangian_add_eval
    (y : Module.Dual ℝ Y) (xz : X × Z) :
    H[h₁, h₂] xz - (((A.coprod B).dualMap (-y)) xz : EReal) =
      admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y + (y c : EReal) := by
  rcases xz with ⟨x, z⟩
  have hdual :
      (((A.coprod B).dualMap (-y)) (x, z) : EReal) = ((-(y (A x + B z)) : ℝ) : EReal) := by
    simp [LinearMap.dualMap_apply, LinearMap.coprod_apply]
  have hpair :
      (admm_lagrangian h₁ h₂ A B c x z y : EReal) + (y c : EReal) =
        h₁ x + h₂ z + (y (A x + B z) : EReal) := by
    have hpair_eval :
        (y (A x + B z - c) : EReal) + (y c : EReal) = (y (A x + B z) : EReal) := by
      change (((y (A x + B z - c) + y c : ℝ)) : EReal) = (((y (A x + B z) : ℝ)) : EReal)
      have hreal : y (A x + B z - c) + y c = y (A x + B z) := by
        rw [map_sub]
        abel
      simp [hreal]
    rw [admm_lagrangian_apply]
    calc
      h₁ x + h₂ z + (y (A x + B z - c) : EReal) + (y c : EReal)
          = h₁ x + h₂ z + ((y (A x + B z - c) : EReal) + (y c : EReal)) := by
              rw [add_assoc]
      _ = h₁ x + h₂ z + (y (A x + B z) : EReal) := by rw [hpair_eval]
  -- Normalize the pulled-back dual pairing into the ADMM Lagrangian residual.
  calc
    H[h₁, h₂] (x, z) - (((A.coprod B).dualMap (-y)) (x, z) : EReal)
        = h₁ x + h₂ z + (y (A x + B z) : EReal) := by
            rw [admm_objective_apply]
            change
              h₁ x + h₂ z + (((-((-y) (A x + B z)) : ℝ)) : EReal) =
                h₁ x + h₂ z + (y (A x + B z) : EReal)
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = admm_lagrangian h₁ h₂ A B c x z y + (y c : EReal) := hpair.symm

/-- Helper for Theorem 15.1: translating an `EReal` range by a finite scalar translates its
infimum by the same scalar. -/
private theorem ereal_sInf_range_add_finite
    {α : Type*} (φ : α → EReal) (r : ℝ) :
    sInf (Set.range fun a : α ↦ φ a + (r : EReal)) = sInf (Set.range φ) + (r : EReal) := by
  let f : EReal → EReal := fun t ↦ t + (r : EReal)
  have hmono : Monotone f := by
    intro a b hab
    simpa [f, add_comm, add_left_comm, add_assoc] using
      add_le_add_left hab (r : EReal)
  have hcontAdd :
      ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (sInf (Set.range φ), (r : EReal)) := by
    apply EReal.continuousAt_add <;> simp
  have hpair_cont : ContinuousAt (fun t : EReal ↦ (t, (r : EReal))) (sInf (Set.range φ)) :=
    continuousAt_id.prodMk continuousAt_const
  have hcont : ContinuousAt f (sInf (Set.range φ)) := by
    simpa [f] using hcontAdd.comp₂ continuousAt_id continuousAt_const
  have htop : f ⊤ = ⊤ := by
    simp [f]
  have hmap :
      f (sInf (Set.range φ)) = sInf (f '' Set.range φ) :=
    Monotone.map_sInf_of_continuousAt (s := Set.range φ) hcont hmono htop
  have himage :
      f '' Set.range φ = Set.range fun a : α ↦ φ a + (r : EReal) := by
    ext t
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨φ a, ⟨a, rfl⟩, rfl⟩
  simpa [f, himage] using hmap.symm

/-- Helper for Theorem 15.1: on the transpose range, the first Fenchel term is the ADMM dual
objective plus the constant evaluation `⟨y, c⟩`. -/
private theorem neg_conjugate_admm_objective_coprodDual_neg_eq_dual_objective_add_eval
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (y : Module.Dual ℝ Y) :
    -conjugate_function (H[h₁, h₂]) ((A.coprod B).dualMap (-y)) =
      admm_dual_objective h₁ h₂ A B c y + (y c : EReal) := by
  -- Rewrite the conjugate as an infimum of affine perturbations, then identify the ADMM integrand.
  calc
    -conjugate_function (H[h₁, h₂]) ((A.coprod B).dualMap (-y))
        = sInf (Set.range fun xz : X × Z ↦
            H[h₁, h₂] xz - ((((A.coprod B).dualMap (-y)) xz : ℝ) : EReal)) := by
              symm
              exact ereal_sInf_range_sub_pairing_eq_neg_conjugate
                (H[h₁, h₂]) ((A.coprod B).dualMap (-y))
    _ = sInf (Set.range fun xz : X × Z ↦
          admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y + (y c : EReal)) := by
          congr 1
          ext r
          constructor
          · rintro ⟨xz, rfl⟩
            exact ⟨xz, by
              exact
                (admm_objective_sub_coprodDual_neg_eq_lagrangian_add_eval
                  (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂) y xz).symm⟩
          · rintro ⟨xz, rfl⟩
            exact ⟨xz, by
              exact admm_objective_sub_coprodDual_neg_eq_lagrangian_add_eval
                (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂) y xz⟩
    _ = sInf (Set.range fun xz : X × Z ↦ admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y) +
          (y c : EReal) := by
            simpa using
              ereal_sInf_range_add_finite
                (fun xz : X × Z ↦ admm_lagrangian h₁ h₂ A B c xz.1 xz.2 y) (y c)
    _ = admm_dual_objective h₁ h₂ A B c y + (y c : EReal) := by
          rw [← admm_dual_objective_eq_sInf_lagrangian h₁ h₂ A B c h₁_proper h₂_proper y]

/-- Helper for Theorem 15.1: on the transpose range, the unrestricted Fenchel dual objective
agrees with the ADMM dual objective. -/
private theorem fenchel_dual_objective_on_admm_constraint_dual_range
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c)
    (y : Module.Dual ℝ Y) :
    fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
      ((A.coprod B).dualMap (-y)) =
        admm_dual_objective h₁ h₂ A B c y := by
  have hneg_dual : -((A.coprod B).dualMap (-y)) = (A.coprod B).dualMap y := by
    apply LinearMap.ext
    intro xz
    rcases xz with ⟨x, z⟩
    simp [LinearMap.dualMap_apply, LinearMap.coprod_apply]
  -- On the transpose range, the support-function term is exactly `⟨y, c⟩`.
  rw [fenchel_dual_objective_apply, conjugate_function_extendedIndicator_apply_eq_support_function]
  rw [hneg_dual, support_function_admm_feasible_set_on_range (A := A) (B := B) (c := c) hqual y]
  rw [neg_conjugate_admm_objective_coprodDual_neg_eq_dual_objective_add_eval
    (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂) h₁_proper h₂_proper y]
  rw [admm_dual_objective, sub_eq_add_neg]
  have hcancel :
      -conjugate_function h₁ (A.dualMap (-y)) -
          conjugate_function h₂ (B.dualMap (-y)) -
            (y c : EReal) + (y c : EReal) =
        -conjugate_function h₁ (A.dualMap (-y)) -
          conjugate_function h₂ (B.dualMap (-y)) := by
    calc
      -conjugate_function h₁ (A.dualMap (-y)) -
          conjugate_function h₂ (B.dualMap (-y)) -
            (y c : EReal) + (y c : EReal)
          =
          (-conjugate_function h₁ (A.dualMap (-y)) -
            conjugate_function h₂ (B.dualMap (-y))) +
              (-(y c : EReal) + (y c : EReal)) := by
                simp [sub_eq_add_neg, add_assoc]
      _ = -conjugate_function h₁ (A.dualMap (-y)) -
            conjugate_function h₂ (B.dualMap (-y)) := by
              have hyc : (-(y c : EReal) + (y c : EReal)) = 0 := by
                change (((-(y c) + y c : ℝ)) : EReal) = 0
                simp
              rw [hyc]
              rw [add_zero]
  calc
    (-conjugate_function h₁ (A.dualMap (-y)) -
        conjugate_function h₂ (B.dualMap (-y)) -
          (y c : EReal) + (y c : EReal)) +
        -(y c : EReal)
        =
        (-conjugate_function h₁ (A.dualMap (-y)) -
          conjugate_function h₂ (B.dualMap (-y))) + -(y c : EReal) := by
            rw [hcancel]
    _ = -conjugate_function h₁ (A.dualMap (-y)) -
          conjugate_function h₂ (B.dualMap (-y)) - (y c : EReal) := by
            rfl

/-- Helper for Theorem 15.1: outside the transpose range, the unrestricted Fenchel dual objective
collapses to `-∞`. -/
private theorem fenchel_dual_objective_eq_bot_of_not_mem_admm_constraint_dual_range
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c)
    (ξ : Module.Dual ℝ (X × Z))
    (hξ : ξ ∉ Set.range (A.coprod B).dualMap) :
    fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ξ = ⊥ := by
  -- Off the transpose range, the support-function term is `⊤`, so the dual objective collapses.
  rw [fenchel_dual_objective_apply, conjugate_function_extendedIndicator_apply_eq_support_function]
  rw [support_function_admm_feasible_set_eq_top_of_not_mem_dual_range
    (A := A) (B := B) (c := c) hqual ξ hξ]
  simp

/-- Helper for Theorem 15.1: the unrestricted Fenchel dual value of the ADMM product formulation
is exactly the ADMM dual problem value. -/
private theorem fenchel_dual_problem_value_eq_admm_dual_problem_value
    (h₁_proper : IsProperExtendedRealFunction h₁)
    (h₂_proper : IsProperExtendedRealFunction h₂)
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c) :
    fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) =
      admm_dual_problem_value h₁ h₂ A B c := by
  -- Compare the two suprema pointwise using the on-range rewrite and the off-range collapse.
  rw [fenchel_dual_problem_value_eq_sSup, admm_dual_problem_value_eq_sSup]
  apply le_antisymm
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨ξ, rfl⟩
    by_cases hξ : ξ ∈ Set.range (A.coprod B).dualMap
    · rcases hξ with ⟨y0, hy0⟩
      have hy : ξ = (A.coprod B).dualMap (-(-y0)) := by
        calc
          ξ = (A.coprod B).dualMap y0 := hy0.symm
          _ = (A.coprod B).dualMap (-(-y0)) := by simp
      rw [hy]
      rw [fenchel_dual_objective_on_admm_constraint_dual_range
        (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂)
        h₁_proper h₂_proper hqual (-y0)]
      exact le_sSup ⟨-y0, rfl⟩
    · rw [fenchel_dual_objective_eq_bot_of_not_mem_admm_constraint_dual_range
        (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂) hqual ξ hξ]
      exact bot_le
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨y, rfl⟩
    rw [← fenchel_dual_objective_on_admm_constraint_dual_range
      (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂)
      h₁_proper h₂_proper hqual y]
    exact le_sSup ⟨(A.coprod B).dualMap (-y), rfl⟩

/-- Helper for Theorem 15.1: the indicator of the nonempty ADMM feasible set is proper. -/
private theorem admm_feasible_set_indicator_proper
    (hqual :
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain h₁),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain h₂),
          A xHat + B zHat = c) :
    IsProperExtendedRealFunction (extendedIndicator (admm_feasible_set A B c)) := by
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro xz
    by_cases hxz : xz ∈ admm_feasible_set A B c <;> simp [extendedIndicator, hxz]
  · rcases hqual with ⟨xHat, _hxHat, zHat, _hzHat, hEq⟩
    refine ⟨(xHat, zHat), ?_⟩
    simpa [effective_domain_extendedIndicator, admm_feasible_set, hEq]

/-- Helper for Theorem 15.1: the indicator of the ADMM feasible affine set is convex. -/
private theorem admm_feasible_set_indicator_convex :
    is_convex_function (extendedIndicator (admm_feasible_set A B c)) := by
  have h_zero_convex : is_convex_function (0 : X × Z → EReal) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set (X × Z))))
  have h_constrained_convex :
      is_convex_function
        (constrained_problem_objective (0 : X × Z → EReal) (admm_feasible_set A B c)) :=
    is_convex_function_constrained_problem_objective h_zero_convex admm_feasible_set_convex
  -- Rewrite the constrained zero objective as `0 + δ_feas`.
  rw [constrained_problem_objective_eq_add_extendedIndicator
    (0 : X × Z → EReal) (admm_feasible_set A B c) (fun _ _ ↦ by simp)] at h_constrained_convex
  simpa [composite_model_objective] using h_constrained_convex

-- Proof sketch: the public theorem is stated under `hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c`,
-- while the private proof path rewrites the affine-constrained ADMM primal problem as a Fenchel
-- problem on `X × Z` and uses `hAssump.ri_qualification` as the Chapter 4 qualification input.
include h₁_proper h₂_proper h₁_convex h₂_convex hqual

omit h₁_proper h₂_proper h₁_convex h₂_convex in
/-- Helper for Theorem 15.1: a Fenchel dual maximizer for the ADMM product formulation must lie in
the transpose range, because off-range dual values collapse to `⊥` while the attained dual value
is finite. -/
private theorem fenchel_maximizer_mem_admm_constraint_dual_range
    (ξ : Module.Dual ℝ (X × Z))
    (hgreat :
      IsGreatest
        (Set.range
          (fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))))
        (fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ξ))
    (hfiniteF :
      ∃ r : ℝ,
        fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) =
          (r : EReal)) :
    ξ ∈ Set.range (A.coprod B).dualMap := by
  by_contra hξ_not_mem
  have hdual_ne_bot :
      fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ≠ ⊥ := by
    rcases hfiniteF with ⟨r, hr⟩
    rw [hr]
    exact EReal.coe_ne_bot r
  have hξ_value :
      fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) =
        fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) ξ := by
    rw [fenchel_dual_problem_value_eq_sSup]
    exact hgreat.csSup_eq
  rw [fenchel_dual_objective_eq_bot_of_not_mem_admm_constraint_dual_range
    (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂) hqual ξ hξ_not_mem] at hξ_value
  exact hdual_ne_bot hξ_value

omit h₁_proper h₂_proper h₁_convex h₂_convex hqual

/-- Theorem 15.1 (1): if Assumption 15.2 holds for the AD-PMM problem, then the optimal values of
the primal problem `(15.1)` and dual problem `(15.2)` coincide. -/
theorem admm_problem_value_eq_admm_dual_problem_value
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c) :
    H_opt[h₁, h₂; A, B, c] = admm_dual_problem_value h₁ h₂ A B c := by
  -- Specialize Chapter 4 Fenchel duality to the ADMM product objective and affine feasible set.
  calc
    H_opt[h₁, h₂; A, B, c]
        = sInf (Set.range
            (composite_model_objective (H[h₁, h₂])
              (extendedIndicator (admm_feasible_set A B c)))) :=
            admm_problem_value_eq_fenchel_primal_infimum
              (A := A) (B := B) (c := c)
              hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper
    _ = fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) :=
          fenchel_duality_value_eq
            (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
            (admm_objective_proper
              (h₁ := h₁) (h₂ := h₂)
              hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper)
            (admm_feasible_set_indicator_proper
              (A := A) (B := B) (c := c) hAssump.ri_qualification)
            (admm_objective_convex
              (h₁ := h₁) (h₂ := h₂)
              hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper
              hAssump.h₁_convex hAssump.h₂_convex)
            (admm_feasible_set_indicator_convex (A := A) (B := B) (c := c))
            (by
              simpa [effective_domain_extendedIndicator] using
                admm_fenchel_qualification
                  (A := A) (B := B) (c := c)
                  hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper
                  hAssump.ri_qualification)
    _ = admm_dual_problem_value h₁ h₂ A B c :=
          fenchel_dual_problem_value_eq_admm_dual_problem_value
            (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂)
            hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper
            hAssump.ri_qualification

-- Proof sketch: `hAssump.optimal_set_nonempty` supplies the source-side optimal-solution context,
-- so the dual attainment statement is exposed directly from the Assumption 15.2 owner rather than
-- through a separate finiteness hypothesis on `H_opt[h₁, h₂; A, B, c]`.
/-- Theorem 15.1 (2): if Assumption 15.2 holds for the AD-PMM problem, then the dual problem
`(15.2)` possesses an optimal solution. -/
theorem exists_isGreatest_admm_dual_objective
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c) :
    ∃ y : Module.Dual ℝ Y,
      IsGreatest (Set.range (admm_dual_objective h₁ h₂ A B c))
        (admm_dual_objective h₁ h₂ A B c y) := by
  obtain ⟨xzStar, hxzStar⟩ := hAssump.optimal_set_nonempty
  have hxzStar_data : xzStar ∈ admm_feasible_set A B c ∧
      IsMinOn (H[h₁, h₂]) (admm_feasible_set A B c) xzStar := by
    simpa using hxzStar
  have hprimal_value_eq :
      H_opt[h₁, h₂; A, B, c] = H[h₁, h₂] xzStar := by
    have hxzStar_min :
        IsMinOn (constrained_problem_objective (H[h₁, h₂]) (admm_feasible_set A B c))
          Set.univ xzStar := by
      rw [isMinOn_univ_iff]
      intro y
      by_cases hy : y ∈ admm_feasible_set A B c
      · simpa [constrained_problem_objective, hy, hxzStar_data.1] using hxzStar_data.2 hy
      · rw [constrained_problem_objective_of_not_mem (H[h₁, h₂]) hy]
        exact le_top
    have hglb_raw :=
      hxzStar_min.isGLB (by simp : xzStar ∈ (Set.univ : Set (X × Z)))
    rw [admm_problem_value_eq_sInf]
    have hcs_raw := hglb_raw.csInf_eq ⟨_, ⟨xzStar, ⟨by simp, rfl⟩⟩⟩
    calc
      sInf (Set.range (constrained_problem_objective (H[h₁, h₂]) (admm_feasible_set A B c)))
          = constrained_problem_objective (H[h₁, h₂]) (admm_feasible_set A B c) xzStar :=
            by simpa [Set.range] using hcs_raw
      _ = H[h₁, h₂] xzStar := by
            simp [constrained_problem_objective, hxzStar_data.1]
  rcases hAssump.ri_qualification with ⟨xHat, hxHat, zHat, hzHat, hEq⟩
  have hqual_feas : (xHat, zHat) ∈ admm_feasible_set A B c := by
    simpa [admm_feasible_set] using hEq
  have hqual_finite :
      H[h₁, h₂] (xHat, zHat) < ⊤ := by
    have hmem :
        (xHat, zHat) ∈ effective_domain (H[h₁, h₂]) := by
      simpa [effective_domain_admm_objective
        (h₁ := h₁) (h₂ := h₂)
        hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper] using
        And.intro (intrinsicInterior_subset hxHat) (intrinsicInterior_subset hzHat)
    exact mem_effective_domain.mp hmem
  have hxzStar_lt_top : H[h₁, h₂] xzStar < ⊤ := by
    exact lt_of_le_of_lt (hxzStar_data.2 hqual_feas) hqual_finite
  have hprimal_ne_bot : H_opt[h₁, h₂; A, B, c] ≠ ⊥ := by
    rw [hprimal_value_eq]
    exact admm_objective_ne_bot
      (h₁ := h₁) (h₂ := h₂)
      hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper xzStar
  have hprimal_ne_top : H_opt[h₁, h₂; A, B, c] ≠ ⊤ := by
    rw [hprimal_value_eq]
    exact ne_of_lt hxzStar_lt_top
  have hfiniteF :
      ∃ r : ℝ,
        fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c)) =
          (r : EReal) := by
    refine ⟨(H_opt[h₁, h₂; A, B, c]).toReal, ?_⟩
    calc
      fenchel_dual_problem_value (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
          = admm_dual_problem_value h₁ h₂ A B c :=
              fenchel_dual_problem_value_eq_admm_dual_problem_value
                (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂)
                hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper
                hAssump.ri_qualification
      _ = H_opt[h₁, h₂; A, B, c] := by
            rw [admm_problem_value_eq_admm_dual_problem_value (ρ := ρ) (G := G) (Q := Q) hAssump]
      _ = (((H_opt[h₁, h₂; A, B, c]).toReal : ℝ) : EReal) := by
            exact (EReal.coe_toReal hprimal_ne_top hprimal_ne_bot).symm
  rcases exists_isGreatest_fenchel_dual_objective_of_finite_value
      (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
      (admm_objective_proper
        (h₁ := h₁) (h₂ := h₂)
        hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper)
      (admm_feasible_set_indicator_proper
        (A := A) (B := B) (c := c) hAssump.ri_qualification)
      (admm_objective_convex
        (h₁ := h₁) (h₂ := h₂)
        hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper
        hAssump.h₁_convex hAssump.h₂_convex)
      (admm_feasible_set_indicator_convex (A := A) (B := B) (c := c))
      (by
        simpa [effective_domain_extendedIndicator] using
          admm_fenchel_qualification
            (A := A) (B := B) (c := c)
            hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper
            hAssump.ri_qualification)
      hfiniteF with
    ⟨ξ, hξ_greatest⟩
  have hξ_mem :
      ξ ∈ Set.range (A.coprod B).dualMap :=
    fenchel_maximizer_mem_admm_constraint_dual_range
      (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂)
      (hqual := hAssump.ri_qualification) ξ hξ_greatest hfiniteF
  rcases hξ_mem with ⟨y0, rfl⟩
  refine ⟨-y0, ?_⟩
  refine ⟨⟨-y0, rfl⟩, ?_⟩
  intro r hr
  rcases hr with ⟨y, rfl⟩
  have hle :
      fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
          ((A.coprod B).dualMap (-y)) ≤
        fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
          ((A.coprod B).dualMap y0) :=
    hξ_greatest.2
      (show
        fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))
            ((A.coprod B).dualMap (-y)) ∈
          Set.range
            (fenchel_dual_objective (H[h₁, h₂]) (extendedIndicator (admm_feasible_set A B c))) from
          ⟨(A.coprod B).dualMap (-y), rfl⟩)
  -- Restrict the Fenchel maximizer to the transpose range and rewrite both endpoints back.
  have hy0_dual : (A.coprod B).dualMap y0 = (A.coprod B).dualMap (-(-y0)) := by
    simp
  rw [fenchel_dual_objective_on_admm_constraint_dual_range
    (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂)
    (h₁_proper := hAssump.toIsProperExtendedRealFunction) (h₂_proper := hAssump.h₂_proper)
    hAssump.ri_qualification y,
    hy0_dual,
    fenchel_dual_objective_on_admm_constraint_dual_range
      (A := A) (B := B) (c := c) (h₁ := h₁) (h₂ := h₂)
      (h₁_proper := hAssump.toIsProperExtendedRealFunction) (h₂_proper := hAssump.h₂_proper)
      hAssump.ri_qualification (-y0)] at hle
  simpa using hle

omit h₁_proper h₂_proper h₁_convex h₂_convex hqual

end
